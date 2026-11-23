import Formalism.LocalToGlobal.CharacterGerms.RowTiePPTFBSt
import Formalism.LocalToGlobal.CharacterGerms.RowTieGermI

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds

variable {C : Type} [Field C]

def VLim (V : VF C) {N : Type} (m : ℕ → ℕ → N → C) (m' : ℕ → N → C) : Prop :=
  ∀ (K : ℝ) (s : ℕ) (n : N), ∃ k0 : ℕ, ∀ k ≥ k0, V.Ge K (m' s n - m k s n)

def OActTySt : Prop :=
  ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ)
    (Y : FBChart C V O dd) (d : ℕ) [NeZero d] (I : Fin 2 → Type) [∀ g, Fintype (I g)] (p : PairData Y d I)
    (g : Fin 2) (α : O) (x : ℕ → I g ⊕ JJ I g → C), x ∈ (Y.raw p).TySet V g →
    (fun s n => p.em g ((Y.raw p).tyC g n) α * x s n) ∈ (Y.raw p).TySet V g

def LimTySt : Prop :=
  AllFB fun C _ V _ I _ _ X => ∀ (g : Fin 2) (x : ℕ → ℕ → I g ⊕ JJ I g → C) (x' : ℕ → I g ⊕ JJ I g → C),
    (∀ k, x k ∈ X.TySet V g) → VLim V x x' → x' ∈ X.TySet V g

def IndSt : Prop :=
  ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ)
    (Y : FBChart C V O dd) (d : ℕ) [NeZero d] (I : Fin 2 → Type) [∀ g, Fintype (I g)] (p : PairData Y d I)
    (g : Fin 2) (N : Type) (ty : N → ZMod d) (M : Set (ℕ → N → C)),
    1 ∈ M → (∀ m m', m ∈ M → m' ∈ M → m + m' ∈ M) → (∀ m, m ∈ M → -m ∈ M) →
    (∀ m m', m ∈ M → m' ∈ M → m * m' ∈ M) →
    (∀ c : C, V.Ge 0 c → (fun s (_ : N) => c ^ (V.l ^ s)) ∈ M) →
    (∀ α : O, (fun (_ : ℕ) n => p.em g (ty n) α) ∈ M) →
    (∀ (m : ℕ → ℕ → N → C) (m' : ℕ → N → C), (∀ k, m k ∈ M) → VLim V m m' → m' ∈ M) →
    ∀ a : ZMod d, (fun (s : ℕ) (n : N) => if ty n = a + (s : ZMod d) then (1 : C) else 0) ∈ M

theorem VLim.mul_right {V : VF C} {N : Type} {m : ℕ → ℕ → N → C} {m' : ℕ → N → C} (h : VLim V m m')
    (y : ℕ → N → C) : VLim V (fun k => m k * y) (m' * y) := by
  intro K s n
  by_cases hy : y s n = 0
  · exact ⟨0, fun k _ => by simp [hy, VF.Ge.zero]⟩
  · have hne : V.v (y s n) ≠ ⊤ := by
      rw [Ne, AddValuation.top_iff]; exact hy
    obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp hne
    obtain ⟨k0, hk0⟩ := h (K - r) s n
    refine ⟨k0, fun k hk => ?_⟩
    have e : (m' * y) s n - (m k * y) s n = (m' s n - m k s n) * y s n := by
      simp only [Pi.mul_apply]; ring
    rw [e]
    have hyr : V.Ge r (y s n) := by unfold VF.Ge; rw [← hr]
    have := (hk0 k hk).mul hyr
    simpa using this

theorem ptAvg_of (hAct : OActTySt) (hLim : LimTySt) (hInd : IndSt) : PTAvgFBSt := by
  intro C _ _ V O _ _ dd Y d _ I _ p g a x hx hx0
  set X := Y.raw p with hX
  let M : Set (ℕ → I g ⊕ JJ I g → C) := {m | ∀ y ∈ X.TySet V g, m * y ∈ X.TySet V g}
  have hAdd := addCvFB_of germIAll_holds C V O dd Y d I p
  have h1 : (1 : ℕ → I g ⊕ JJ I g → C) ∈ M := fun y hy => by rwa [one_mul]
  have hadd : ∀ m m', m ∈ M → m' ∈ M → m + m' ∈ M := fun m m' hm hm' y hy => by
    rw [add_mul]; exact X.add_mem V g hAdd p.u_int _ _ (hm y hy) (hm' y hy)
  have hneg : ∀ m, m ∈ M → -m ∈ M := fun m hm y hy => by
    rw [neg_mul]; exact X.neg_mem V g Y.l_odd _ (hm y hy)
  have hmul : ∀ m m', m ∈ M → m' ∈ M → m * m' ∈ M := fun m m' hm hm' y hy => by
    rw [mul_assoc]; exact hm _ (hm' y hy)
  have hteich : ∀ c : C, V.Ge 0 c → (fun s (_ : I g ⊕ JJ I g) => c ^ (V.l ^ s)) ∈ M := fun c hc y hy =>
    X.teich_mem V g c hc y hy
  have hact : ∀ α : O, (fun (_ : ℕ) n => p.em g (X.tyC g n) α) ∈ M := fun α y hy =>
    hAct C V O dd Y d I p g α y hy
  have hlim : ∀ (m : ℕ → ℕ → I g ⊕ JJ I g → C) (m' : ℕ → I g ⊕ JJ I g → C), (∀ k, m k ∈ M) → VLim V m m' → m' ∈ M :=
    fun m m' hm hmm' y hy => hLim C V O dd Y d I p g (fun k => m k * y) (m' * y) (fun k => hm k y hy) (hmm'.mul_right y)
  have hI := hInd C V O dd Y d I p g (I g ⊕ JJ I g) (X.tyC g) M h1 hadd hneg hmul hteich hact hlim a
  refine ⟨_, hI x hx, ?_, ?_⟩
  · funext n
    simp only [Pi.mul_apply, Nat.cast_zero, add_zero]
    by_cases hn : X.tyC g n = a
    · rw [if_pos hn, one_mul]
    · rw [if_neg hn, zero_mul, hx0 n hn]
  · intro i n hn
    simp only [Pi.mul_apply]
    rw [if_neg hn, zero_mul]

theorem ptFB_of_act (hEx : PTExFBSt) (hAct : OActTySt) (hLim : LimTySt) (hInd : IndSt) (hStab : HStabFBSt) : PTFBSt :=
  ptFB_of hEx (ptAvg_of hAct hLim hInd) germIAll_holds hStab

end Formalism.L2.FormalSeriesBounds
