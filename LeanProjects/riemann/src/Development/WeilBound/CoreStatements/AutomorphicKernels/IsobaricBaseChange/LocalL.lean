import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeIsobaric
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsIrreducibleSecondFactorOfIrreducibleProduct
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCovBySubmodule

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC

namespace GlobalTheory.PfBCI

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem nontrivial_of_irr {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ G V} (h : ρ.IsIrreducible) : Nontrivial V := by
  by_contra hV
  rw [not_nontrivial_iff_subsingleton] at hV
  exact bot_ne_top (α := Subrepresentation ρ)
    (Subrepresentation.toSubmodule_injective (Subsingleton.elim _ _))

theorem nontrivial_piTensor {ι : Type} [Fintype ι] {X : ι → Type} [∀ a, AddCommGroup (X a)]
    [∀ a, Module ℂ (X a)] [∀ a, Nontrivial (X a)] : Nontrivial (PiTensorProduct ℂ X) := by
  classical
  choose v hv using fun a => exists_ne (0 : X a)
  have hex : ∀ a, ∃ φ : Module.Dual ℂ (X a), φ (v a) ≠ 0 := fun a => by
    by_contra hc
    push Not at hc
    exact hv a ((Module.forall_dual_apply_eq_zero_iff ℂ (v a)).1 hc)
  choose φ hφ using hex
  let L := PiTensorProduct.lift ((MultilinearMap.mkPiAlgebra ℂ ι ℂ).compLinearMap φ)
  have h : L (PiTensorProduct.tprod ℂ v) ≠ 0 := by
    simp only [L, PiTensorProduct.lift.tprod, MultilinearMap.compLinearMap_apply,
      MultilinearMap.mkPiAlgebra_apply]
    exact Finset.prod_ne_zero_iff.2 fun a _ => hφ a
  exact ⟨PiTensorProduct.tprod ℂ v, 0, fun h0 => h (by rw [h0, map_zero])⟩

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField in

theorem nontrivial_locProd {c : ℕ} {N : Fin c → ℕ} (h : ∑ i, N i = n) (w : HeightOneSpectrum (𝓞 E))
    (σ : ∀ i, SmIrr (GL (Fin (N i)) (w.adicCompletion E))) :
    Nontrivial (GlobalTheory.SmGL.IndSp (GlobalTheory.SmGL.stdBlocks N h) (GlobalTheory.SmGL.piTensor fun i => (σ i).ρ)) := by
  have : ∀ i, Nontrivial (σ i).V := fun i => nontrivial_of_irr (σ i).irred
  have : Nontrivial (PiTensorProduct ℂ fun i => (σ i).V) := nontrivial_piTensor
  obtain ⟨u, hu⟩ := exists_ne (0 : PiTensorProduct ℂ fun i => (σ i).V)
  obtain ⟨f, hf, -⟩ := GlobalTheory.SmGL.ProdIrr.exists_indSp_apply_one (GlobalTheory.SmGL.stdBlocks N h)
    (GlobalTheory.SmGL.piTensor fun i => (σ i).ρ) (GlobalTheory.SmGL.isSmooth_piTensor fun i => (σ i).smooth) u
  exact ⟨f, 0, fun h0 => hu (by rw [← hf, h0]; rfl)⟩

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField in

theorem isSmooth_locProd {c : ℕ} {N : Fin c → ℕ} (h : ∑ i, N i = n) (w : HeightOneSpectrum (𝓞 E))
    (σ : ∀ i, SmIrr (GL (Fin (N i)) (w.adicCompletion E))) : IsSmooth (locProd h w σ) :=
  GlobalTheory.SmGL.isSmooth_parInd _ _

theorem local_subquotient {c : ℕ} {N : Fin c → ℕ} (h : ∑ i, N i = n) (w : HeightOneSpectrum (𝓞 E))
    (σ : ∀ i, SmIrr (GL (Fin (N i)) (w.adicCompletion E))) :
    ∃ P : SmIrr (GL (Fin n) (w.adicCompletion E)), GlobalTheory.SmGL.IsSubquotient P.ρ (locProd h w σ) := by
  obtain ⟨Y, _, _, τ, hτ, hτs⟩ :=
    GlobalTheory.IrrSubquot.exists_irreducible_subquotient _ _ (locProd h w σ) (nontrivial_locProd h w σ)
  exact ⟨⟨Y, τ, hτs.isSmooth (isSmooth_locProd h w σ), hτ⟩, hτs⟩

end GlobalTheory.PfBCI

end
