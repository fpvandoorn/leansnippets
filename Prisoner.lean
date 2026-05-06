import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Card

abbrev Prisoner : Type := Fin 100

def Strategy := Prisoner → Bool → List Bool → Option Bool

def Schedule := Prisoner → Nat

def Memory := Prisoner → List Bool

inductive Memory.Valid (s : Strategy) : Option Bool → Memory → Prop
  | start : Memory.Valid s (some false) (fun _ => [])
  | next (p : Prisoner) {light h} :
    Memory.Valid s (some light) h →
    Memory.Valid s (s p light (h p)) (Function.update h p (light :: h p))

def Memory.Fair (m : Memory) (n : Nat) := ∀ p, (m p).length ≥ n

def ofState' {α} (init : α) (f : α → Bool → Option (α × Bool)) (ls : List Bool) : Option α :=
  ls.foldrM (fun b a => (f a b).map (·.1)) init

@[simp] theorem ofState'_succ {α} (init : α) (f : α → Bool → Option (α × Bool))
    (l : Bool) (ls : List Bool) :
    ofState' init f (l :: ls) = (ofState' init f ls).bind fun a => (f a l).map (·.1) := by
  simp [ofState']

def ofState {α} (init : α) (f : α → Bool → Option (α × Bool))
    (l : Bool) (ls : List Bool) : Option Bool :=
  ofState' init f ls |>.bind fun a => (f a l).map (·.2)

def leader : Nat → Bool → Option (Nat × Bool)
  | n, false => some (n, false)
  | n, true => if 98 ≤ n then none else some (n+1, false)

def follower : Bool → Bool → Option (Bool × Bool)
  | false, false => some (true, true)
  | state, light => some (state, light)

def Invariant : Option Bool → Memory → Prop
  | none, m => ∀ p, (m p).length ≥ 1
  | some l, m =>
    let s := Finset.univ.filter fun p : Prisoner =>
      p ≠ 0 ∧ ofState' false follower (m p) = some true
    ∃ n, ofState' 0 leader (m 0) = some n ∧ s.card = if l then n + 1 else n

attribute [-simp] Bool.exists_bool Bool.forall_bool

theorem prisoner : ∃ s : Strategy, ∀ m, Memory.Valid s none m → ∀ p, (m p).length ≥ 1 := by
  let s (p : Prisoner) := if p = 0 then ofState 0 leader else ofState false follower
  use s
  suffices ∀ m l, Memory.Valid s l m → Invariant l m from fun m => this _ _
  intro m l v
  -- match v with
  induction v with
  | start => simp [Invariant, ofState']
  | @next p l m v ih =>
    let ⟨n, h1, h2⟩ := ih
    dsimp [s]; split <;> [subst p; skip] <;> simp [ofState, h1]
    · cases l <;> simp [leader] at h2 ⊢
      · exact ⟨n, by simp [h1, leader], h2⟩
      · split
        · have := Nat.succ_le_succ ‹_›
          rw [← Nat.succ_eq_add_one] at h2
          have eq1 : ((@Finset.univ Prisoner _).filter (·≠0)).card = (98).succ := rfl
          rw [← h2, ← eq1] at this
          have := Finset.eq_of_subset_of_card_le ?_ this
          · simp [Finset.ext_iff] at this
            intro p
            simp [Function.update]; split
            · simp
            · have := this p ‹_›; revert this
              cases m p <;> simp [ofState']
          · aesop (add simp Finset.subset_iff)
        · simp [Invariant, leader, *]; exact h2
    · have (b l) : ∃ c, follower b l = some c := by simp [follower]; split <;> simp
      have ⟨b, hb⟩ : ∃ b, ofState' false follower (m p) = some b := by
        induction m p with
        | nil => simp [ofState']
        | cons l ls ih => let ⟨b, hb⟩ := ih; simpa [hb] using this ..
      have ⟨(a, l), hc⟩ := this b l
      simp [hb, hc, Invariant]
      refine ⟨n, Eq.trans ?_ h1, ?_⟩
      · rw [Function.update_noteq (Ne.symm ‹_›)]
      · unfold follower at hc; split at hc <;> cases hc
        · simp at h2 ⊢
          rw [← h2, ← Finset.card_insert_of_not_mem (a := p)]
          congr 1; simp [Finset.ext_iff]
          intro q
          by_cases h : q = p <;> simp [h]
          · subst q; simp [*, follower]
          · simp [*]
        · refine Eq.trans ?_ h2; congr 1; simp [Finset.ext_iff]
          intro q hq
          simp [Function.update]; split
          · subst q
            simp [hb, follower]
          · simp
