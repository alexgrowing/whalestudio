import Formalism.LocalToGlobal.CharacterGerms.RowTiePTyp
import Formalism.LocalToGlobal.CharacterGerms.RowTiePAllOps
import Formalism.LocalToGlobal.CharacterGerms.RowTieGermI
import Formalism.LocalToGlobal.CharacterGerms.RowTiePIndAr
import Formalism.LocalToGlobal.CharacterGerms.RowTiePLimTy

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds

variable {C : Type} [Field C]

namespace RawChart

variable {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ] (X : RawChart C d I κ)

theorem typ_link (V : VF C) (g : Fin 2) {L : ℕ → I g ⊕ JJ I g → C} (hL : L ∈ X.AllSet V g)
    (h0 : ∀ n k, (¬ ∃ s, V.l ^ s = n) → L n k = 0) :
    (fun s k => L (V.l ^ s) k) ∈ X.TySet V g := by
  obtain ⟨γ, lam, hγ, hlam, h1, h2⟩ := hL
  have key : ∀ k, tyS V.l (fun s => L (V.l ^ s) k) = PowerSeries.mk (fun n => L n k) := by
    intro k
    apply tyS_eq V.l_prime.two_le
    · intro s; rw [PowerSeries.coeff_mk]
    · intro m hm
      rw [PowerSeries.coeff_mk]
      exact h0 m k (fun ⟨s, hs⟩ => hm s hs)
  refine ⟨γ, lam, hγ, hlam, ?_, ?_⟩
  · intro i; simp only [key]; exact h1 i
  · intro q; simp only [key]; exact h2 q

end RawChart

def AllStartFBSt : Prop :=
  AllFB fun C _ V _ I _ _ X => ∀ (g : Fin 2) (w : I g → C), (∀ c, V.Ge 0 (w c)) →
    ∃ L ∈ X.AllSet V g, ∀ c, L 1 (Sum.inl c) = w c

theorem ptEx_of_start (hS : AllStartFBSt) : PTExFBSt := by
  intro C _ _ V O _ _ dd Y d _ I _ p g a w hw _
  obtain ⟨L0, hL0, hL01⟩ := hS C V O dd Y d I p g w hw
  set X := Y.raw p with hX
  let M : Set (ℕ → I g ⊕ JJ I g → C) := {m | ∀ L ∈ X.AllSet V g, m * L ∈ X.AllSet V g}
  have hAdd := addCvFB_of germIAll_holds C V O dd Y d I p
  have h1 : (1 : ℕ → I g ⊕ JJ I g → C) ∈ M := fun L hL => by rwa [one_mul]
  have hadd : ∀ m m', m ∈ M → m' ∈ M → m + m' ∈ M := fun m m' hm hm' L hL => by
    rw [add_mul]; exact X.allSet_add V g hAdd p.u_int (hm L hL) (hm' L hL)
  have hmul : ∀ m m', m ∈ M → m' ∈ M → m * m' ∈ M := fun m m' hm hm' L hL => by
    rw [mul_assoc]; exact hm _ (hm' L hL)
  have hteich : ∀ c : C, V.Ge 0 c → (fun n (_ : I g ⊕ JJ I g) => c ^ n) ∈ M := fun c hc L hL =>
    X.allSet_teich V g c hc hL
  have hlim : ∀ (m : ℕ → ℕ → I g ⊕ JJ I g → C) (m' : ℕ → I g ⊕ JJ I g → C), (∀ k, m k ∈ M) → VLim V m m' → m' ∈ M :=
    fun m m' hm hmm' L hL => X.allSet_lim (Y.chart_log_constantCoeff p) (Y.chart_exp_constantCoeff p) (Y.raw_lgex p) (Y.raw_exlg p)
      (fun k => hm k L hL) (hmm'.mul_right L)
  have hroot : ∀ q : ℕ, q.Prime → q ≠ V.l → ∃ ζ : C, IsPrimitiveRoot ζ q := by
    intro q hq _
    have := Y.algClosed
    have : NeZero (q : C) := ⟨Nat.cast_ne_zero.mpr hq.ne_zero⟩
    exact HasEnoughRootsOfUnity.exists_primitiveRoot C q
  have hind := TypAr.typ_gen M hroot h1 hadd hmul hteich hlim
  have hL := hind L0 hL0
  refine ⟨_, X.typ_link V g hL ?_, ?_⟩
  · intro n k hn
    simp only [Pi.mul_apply]
    rw [if_neg hn, zero_mul]
  · intro c
    simp only [Pi.mul_apply, pow_zero]
    rw [if_pos ⟨0, pow_zero _⟩, one_mul, hL01 c]

theorem ptFB_of_start (hS : AllStartFBSt) (hAct : OActTySt) (hLim : LimTySt) (hStab : HStabFBSt) : PTFBSt :=
  ptFB_of_act (ptEx_of_start hS) hAct hLim indSt_holds hStab

theorem ptFB_of_start2 (hS : AllStartFBSt) (hAct : OActTySt) (hStab : HStabFBSt) : PTFBSt :=
  ptFB_of_start hS hAct limTy_holds hStab

end Formalism.L2.FormalSeriesBounds
