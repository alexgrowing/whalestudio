import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenImmersionCellFl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvMulApplyEqZeroOfMinor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchubertCellOpenImmersion
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.FlagZ GlobalTheory.FlagZ.Univ
open GlobalTheory.QCoh (freeModule)
open GlobalTheory.Twist (resM)

namespace GlobalTheory.FlagZ.Univ

theorem isFrame_sum_smul_of_isUnit {X : Scheme.{0}} {F : X.Modules} {U : X.Opens} {n : Type} [Fintype n]
    [DecidableEq n] {e : n → Γ(F, U)} (he : VB.IsFrame e) (M : Matrix n n Γ(X, U)) (hM : IsUnit M) :
    VB.IsFrame fun j => ∑ i, M i j • e i := by
  intro V h
  have hM' : IsUnit ((resG X h).mapMatrix M) := hM.map _
  have hb : Function.Bijective ((resG X h).mapMatrix M).mulVec :=
    ⟨Matrix.mulVec_injective_of_isUnit hM', Matrix.mulVec_surjective_iff_isUnit.2 hM'⟩
  have key : ⇑(Fintype.linearCombination Γ(X, V) fun j => resM F h (∑ i, M i j • e i)) =
      (Fintype.linearCombination Γ(X, V) fun i => resM F h (e i)) ∘
        ((resG X h).mapMatrix M).mulVec := by
    funext a
    simp only [Function.comp_apply, Fintype.linearCombination_apply, map_sum, GlobalTheory.Twist.resM_smul,
      Matrix.mulVec, dotProduct, Finset.sum_smul, Finset.smul_sum, smul_smul,
      RingHom.mapMatrix_apply, Matrix.map_apply]
    rw [Finset.sum_comm]
    simp only [mul_comm]
  rw [key]
  exact (he V h).comp hb

theorem isFrame_cellCol : ∀ (ι : Type) [Fintype ι] (N : ℕ) (w : ι → Equiv.Perm (Fin N)) (τ : ι),
    VB.IsFrame (cellCol ι N w τ) := by
  intro ι _ N w τ
  exact isFrame_sum_smul_of_isUnit ((VB.isFrame_freeFrame (Fl ι N) (Fin N)).res le_top)
    ((cellRing ι N w).mapMatrix (cellGL Prod.fst Prod.snd w τ).1)
    ((cellGL Prod.fst Prod.snd w τ).isUnit.map _)

end GlobalTheory.FlagZ.Univ
