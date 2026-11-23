import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RangeSndRel
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AuxiliaryPrimeLtFirstTypePrimeOfSizes
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ComplexConjugationMapsMultiplicitySpace
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiscreteSeriesModelOfDualParameter
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.TypeConj

open Matrix Formalism.IndefR.Mult GlobalTheory.ConjDS GlobalTheory.ConjMult

variable {D : D7}

theorem isTypeAt_star (θ : InfFam D) (V : HSp D) (τ : D.what₂.Tau) (P : SPar) (φ : GA D V → ℂ)
    (h : IsTypeAt θ V τ P φ) : IsTypeAt θ V τ (dualPar P) fun g => star (φ g) := by
  obtain ⟨H, i1, i2, σ, lam, ε, Q, hE, hD, hQ, hG, hx⟩ := h
  letI := i1; letI := i2
  have hJ := GlobalTheory.SmoothAutCheck.gramAt_unit V τ
  have e : ∀ g, rv (Q.submatrix Fin.revPerm (Equiv.refl _) * g * (Q.submatrix Fin.revPerm (Equiv.refl _))⁻¹) =
      Q * g * Q⁻¹ := by
    intro g
    rw [inv_submatrix_equiv]
    have : Q.submatrix Fin.revPerm (Equiv.refl _) * g * Q⁻¹.submatrix (Equiv.refl _) Fin.revPerm =
        rv (Q * g * Q⁻¹) := by
      ext i j
      simp [rv, Matrix.mul_apply]
    rw [this, rv_rv]
  have hc : ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ w : Cj H,
      cj H ((fun g => cjOp (σ (rv g))) (Q.submatrix Fin.revPerm (Equiv.refl _) * g *
        (Q.submatrix Fin.revPerm (Equiv.refl _))⁻¹) w) = (fun g => σ (Q * g * Q⁻¹)) g (cj H w) := by
    intro g _ w
    show σ (rv _) (cj H w) = _
    rw [e]
  have hc' : ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ w : H,
      (cj H).symm ((fun g => σ (Q * g * Q⁻¹)) g w) = (fun g => cjOp (σ (rv g))) (Q.submatrix Fin.revPerm (Equiv.refl _) * g *
        (Q.submatrix Fin.revPerm (Equiv.refl _))⁻¹) ((cj H).symm w) := by
    intro g hg w
    apply (cj H).injective
    rw [hc g hg, LinearIsometryEquiv.apply_symm_apply, LinearIsometryEquiv.apply_symm_apply]
  have hfold : ∀ l : List (Matrix (Fin V.rank) (Fin V.rank) ℂ), (∀ X ∈ l, X ∈ lieAt V τ) → ∀ w : Cj H,
      l.foldr (dRep (fun g => σ (Q * g * Q⁻¹))) (cj H w) =
        cj H (l.foldr (dRep (fun g => (fun g => cjOp (σ (rv g))) (Q.submatrix Fin.revPerm (Equiv.refl _) * g *
          (Q.submatrix Fin.revPerm (Equiv.refl _))⁻¹))) w) := by
    intro l
    induction l with
    | nil => intro _ _; rfl
    | cons X l ih =>
      intro hl w
      rw [List.foldr_cons, ih (fun Y hY => hl Y (List.mem_cons_of_mem _ hY)), dRep_conj hJ (cj H) hc (hl X List.mem_cons_self),
        List.foldr_cons]
  have hn : ∀ l : List (Matrix (Fin V.rank) (Fin V.rank) ℂ), (∀ X ∈ l, X ∈ lieAt V τ) → ∀ w : Cj H,
      ‖l.foldr (dRep (fun g => (fun g => cjOp (σ (rv g))) (Q.submatrix Fin.revPerm (Equiv.refl _) * g *
          (Q.submatrix Fin.revPerm (Equiv.refl _))⁻¹))) w‖ =
        ‖l.foldr (dRep (fun g => σ (Q * g * Q⁻¹))) (cj H w)‖ := by
    intro l hl w
    rw [hfold l hl, LinearIsometryEquiv.norm_map]
  refine ⟨Cj H, inferInstance, inferInstance, fun g => cjOp (σ (rv g)), nr lam, fun a => ε a.rev,
    Q.submatrix Fin.revPerm (Equiv.refl _), isEnum_dual hE, isDS_transfer (fun _ => rfl) (cj H) (fun _ _ => rfl) hD,
    (Matrix.isUnit_submatrix_equiv _ _).2 hQ, ?_, fun x => ?_⟩
  · rw [← hG, ← rv_Jm (ε := fun a => ε a.rev) (ε' := ε) (fun a => by simp), rv,
      conjTranspose_submatrix, submatrix_mul_equiv, submatrix_mul_equiv]
    rfl
  obtain ⟨v, hv, ℓ, hℓ, ⟨S, C, hS, hb, hsum, B, hB, hBb⟩, hs⟩ := hx x
  let ℓ' : ℕ → (Cj H →ₗ[ℂ] ℂ) := fun i =>
    { toFun := fun w => star (ℓ i (cj H w))
      map_add' := fun x y => by simp
      map_smul' := fun a x => by rw [map_smulₛₗ, map_smul]; simp }
  refine ⟨fun i => (cj H).symm (v i), fun i => smoothVec_conj hJ (cj H).symm hc' (hv i), ℓ', fun i => ?_,
    ⟨S, C, hS, fun i w hw => ?_, fun S' hS' => ?_, B, hB, fun g hg w hw => ?_⟩, fun g hg => ?_⟩
  · obtain ⟨ℓ'', h1, h2⟩ := sobCont_conj hJ (cj H) hc (hℓ i)
    have : ℓ'' = ℓ' i := LinearMap.ext h2
    rw [← this]; exact h1
  · have h1 := hb i (cj H w) (smoothVec_conj hJ (cj H) hc hw)
    have h2 : (S.map fun l => ‖l.foldr (dRep (fun g => (fun g => cjOp (σ (rv g))) (Q.submatrix Fin.revPerm (Equiv.refl _) * g *
          (Q.submatrix Fin.revPerm (Equiv.refl _))⁻¹))) w‖) = S.map fun l => ‖l.foldr (dRep (fun g => σ (Q * g * Q⁻¹))) (cj H w)‖ :=
      List.map_congr_left fun l hl => hn l (hS l hl) w
    rw [h2]
    exact (norm_star _).trans_le h1
  · have h2 : ∀ i, (S'.map fun l => ‖l.foldr (dRep (fun g => (fun g => cjOp (σ (rv g))) (Q.submatrix Fin.revPerm (Equiv.refl _) * g *
          (Q.submatrix Fin.revPerm (Equiv.refl _))⁻¹))) ((cj H).symm (v i))‖) =
        S'.map fun l => ‖l.foldr (dRep (fun g => σ (Q * g * Q⁻¹))) (v i)‖ := fun i =>
      List.map_congr_left fun l hl => by rw [hn l (hS' l hl), LinearIsometryEquiv.apply_symm_apply]
    simp only [h2]
    exact hsum S' hS'
  · have h2 := hc g hg w
    have h3 : ∀ u : Cj H, (S.map fun l => ‖l.foldr (dRep (fun g => (fun g => cjOp (σ (rv g))) (Q.submatrix Fin.revPerm (Equiv.refl _) * g *
          (Q.submatrix Fin.revPerm (Equiv.refl _))⁻¹))) u‖) = S.map fun l => ‖l.foldr (dRep (fun g => σ (Q * g * Q⁻¹))) (cj H u)‖ :=
      fun u => List.map_congr_left fun l hl => hn l (hS l hl) u
    rw [h3, h3, h2]
    exact hBb g hg (cj H w) (smoothVec_conj hJ (cj H) hc hw)
  · have e2 : ∀ i, ℓ' i ((fun g => cjOp (σ (rv g))) (Q.submatrix Fin.revPerm (Equiv.refl _) * g *
          (Q.submatrix Fin.revPerm (Equiv.refl _))⁻¹) ((cj H).symm (v i))) = star (ℓ i (σ (Q * g * Q⁻¹) (v i))) := by
      intro i
      show star (ℓ i (cj H _)) = _
      rw [hc g hg, LinearIsometryEquiv.apply_symm_apply]
    simp only [e2]
    exact (hs g hg).star

theorem isTypeAt_dualPar_iff : ∀ {D : D7} (θ : InfFam D) (V : HSp D) (τ : D.what₂.Tau) (P : SPar) (φ : GA D V → ℂ),
    IsTypeAt θ V τ (Formalism.IndefR.Mult.dualPar P) φ ↔ IsTypeAt θ V τ P fun g => star (φ g) := by
  intro D θ V τ P φ
  constructor
  · intro h
    have := isTypeAt_star θ V τ _ _ h
    rwa [dualPar_dualPar] at this
  · intro h
    have := isTypeAt_star θ V τ _ _ h
    simpa only [star_star] using this

end GlobalTheory.TypeConj

end
