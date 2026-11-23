import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CosetVectorsNonzeroDepthFockVacuaStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjugateHalfCommutantActsOnCosetVectorByScalarStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CommutantDepthLatticePermutesCosetVectorsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergOffPartVacuumCommutantActsByScalarStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergOperatorEigenOfThetaVectorAtPlaceStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SymplecticFormOffIdempotentPartOrthogonalHalfStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaHeisenbergConjugationNegHermitianSpace
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ComplexEmbeddingHermitianQuadrupleSum
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaSquareIntegrable
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.CosPerm

variable {D : D7}

theorem heisO_smul_fun (ψ : AddChar (AF D.host.F) ℂ) {S T : HSp D} (w : WO S T) (c : ℂ) (f : WO S T → ℂ) :
    heisO ψ S T w (c • f) = c • heisO ψ S T w f := by
  funext x; simp only [heisO, Pi.smul_apply, smul_eq_mul]; ring

theorem heisO_star {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (S T : HSp D) (w : WO S T) (f : WO S T → ℂ) :
    heisO ψ S T w (star f) = star (heisO ψ (negSp S) T w f) := by
  have h := GlobalTheory.CjNeg.heis_negS hψ S T w (star f)
  have hc : GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id (star f) = f := by
    funext y; simp [GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj]
  rw [hc] at h
  rw [h]; funext y; simp [GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj]

theorem symplO_negSp (S T : HSp D) (x y : WO S T) : symplO (negSp S) T x y = -symplO S T x y := by
  rw [GlobalTheory.ThetaSquare.symplO_eq, GlobalTheory.ThetaSquare.symplO_eq, GlobalTheory.CjNeg.symplOH_negS]; ring

theorem mem_ann_negSp {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {Γ : AddSubgroup (WO S T)} {w : WO S T}
    (hw : w ∈ Ann ψ S T Γ) : w ∈ Ann ψ (negSp S) T Γ := by
  have key : ∀ a b : WO S T, ψ (symplO S T a b) = 1 → ψ (symplO (negSp S) T a b) = 1 := fun a b h => by
    rw [symplO_negSp, AddChar.map_neg_eq_inv, h, inv_one]
  exact ⟨fun u hu => key _ _ (hw.1 u hu), fun e he u hu hh => key _ _ (hw.2 e he u hu hh)⟩

end GlobalTheory.CosPerm

open GlobalTheory.CosPerm in

theorem GlobalTheory.CosPerm.cosVec_perm : All fun {D} _ _ _ {G} W _ => ∀ i, i < D.R.m → ∀ κ, W.cosVec i κ ≠ 0 ∧ (∀ τ, IsFockVacAt (heisO W.ψ (G.pS (.chi i 0)) (G.pT (.chi i 0))) W.θ τ (cplxO (G.cartS W.cart (.chi i 0) τ) (G.onT W.cart (.chi i 0) τ)) (W.cosVec i κ)) ∧ VacG W.ψ _ _ (latRow G i) (star (W.cosVec i κ)) ∧ ∀ w ∈ Ann W.ψ _ _ (latRow G i), w.map (infPart D) = 0 → heisO W.ψ (G.V (.grid (i + 1) 0)) (G.V (.grid i 0)) w (star (W.cosVec i κ)) ∈ Submodule.span ℂ (Set.range fun κ' => (star (W.cosVec i κ') : WO (G.V (.grid (i + 1) 0)) (G.V (.grid i 0)) → ℂ)) := by
  intro D hD T L μ0 hL sc G W M hM i hi κ
  obtain ⟨h1, hdep, hfock⟩ := GlobalTheory.T.coset_vectors_nonzero_depth_fock_vacua D hD T L μ0 hL sc G W M hM i hi κ
  have hψ : IsStdChar D W.ψ (-1) := W.ψ_std
  have hth := (GlobalTheory.CjNeg.theta_heis_neg D W.ψ hψ (G.V (.grid (i + 1) 0)) (G.V (.grid i 0))).1 (star (W.cosVec i κ))
  have hcj : GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id (star (W.cosVec i κ)) = W.cosVec i κ := by
    funext y; simp [GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj]
  rw [hcj] at hth
  refine ⟨h1, hfock, ⟨hth.2.1 hdep.1, fun u hu => ?_, fun e he u hu hh => ?_⟩, ?_⟩
  · rw [heisO_star hψ]; exact congrArg star (hdep.2.1 u hu)
  · rw [heisO_star hψ]; exact congrArg star (hdep.2.2 e he u hu hh)
  intro w hw hfin
  have hw' : w ∈ Ann W.ψ (G.pS (.chi i 0)) (G.pT (.chi i 0)) (depLat G (.chi i 0)) := mem_ann_negSp hw
  obtain ⟨e, he, hthe⟩ := W.cosVec_is
  have hthi := fun κ => hthe i hi κ
  obtain ⟨c₀, hc₀⟩ := GlobalTheory.T.heisenberg_offPart_vacuumCommutant_acts_by_scalar D hD T L μ0 hL sc G W M hM i hi e he w hw' hfin
  obtain ⟨c₃, h₃⟩ := GlobalTheory.T.heisenbergOperator_eigen_of_thetaVector_at_place D W.ψ (G.pS (.chi i 0)) (G.pT (.chi i 0)) e
    (latO (G.pS (.chi i 0)) (G.pT (.chi i 0)) (G.latS (.chi i 0) : Set _) (G.latT (.chi i 0) : Set _) fun _ => True)
    (W.vac i) (cosInd e κ) (W.cosVec i κ) ((1 - e - cA D e) • w) c₀ (hthi κ)
    (fun x hx => GlobalTheory.T.symplecticForm_offIdempotentPart_orthogonal_half D (G.pS (.chi i 0)) (G.pT (.chi i 0)) G.pl.W0 e he w x (Or.inl hx))
    (fun y hy => GlobalTheory.T.symplecticForm_offIdempotentPart_orthogonal_half D (G.pS (.chi i 0)) (G.pT (.chi i 0)) G.pl.W0 e he w y (Or.inr hy)) hc₀
  obtain ⟨c₂, h₂⟩ := GlobalTheory.T.conjugateHalfCommutant_acts_on_cosetVector_by_scalar D hD T L μ0 hL sc G W M hM i hi e he hthi w hw' hfin κ
  obtain ⟨κ', h₁⟩ := GlobalTheory.T.commutant_depth_lattice_permutes_coset_vectors D hD T L μ0 hL sc G W M hM i hi e he hthi w hw' hfin κ
  have hdec : w = e • w + (cA D e • w + (1 - e - cA D e) • w) := by
    rw [← add_smul, ← add_smul, show e + (cA D e + (1 - e - cA D e)) = 1 by ring, one_smul]
  have hne : ∀ a, W.ψ a ≠ 0 := fun a h => by
    have := AddChar.map_add_eq_mul W.ψ a (-a)
    rw [add_neg_cancel, AddChar.map_zero_eq_one, h, zero_mul] at this
    exact one_ne_zero this
  have e1 := GlobalTheory.OrientedHeis.heisO_heisO (ψ := W.ψ) (S := G.pS (.chi i 0)) (T := G.pT (.chi i 0))
    (cA D e • w) ((1 - e - cA D e) • w) (W.cosVec i κ)
  rw [h₃, heisO_smul_fun, h₂, smul_smul] at e1
  have e1' : heisO W.ψ (G.pS (.chi i 0)) (G.pT (.chi i 0)) (cA D e • w + (1 - e - cA D e) • w) (W.cosVec i κ) =
      (W.ψ (symplOH (G.pS (.chi i 0)) (G.pT (.chi i 0)) (cA D e • w) ((1 - e - cA D e) • w)))⁻¹ • ((c₃ * c₂) • W.cosVec i κ) := by
    rw [e1, inv_smul_smul₀ (hne _)]
  have e2 := GlobalTheory.OrientedHeis.heisO_heisO (ψ := W.ψ) (S := G.pS (.chi i 0)) (T := G.pT (.chi i 0))
    (e • w) (cA D e • w + (1 - e - cA D e) • w) (W.cosVec i κ)
  rw [← hdec, e1', heisO_smul_fun, heisO_smul_fun, h₁] at e2
  have hC : heisO W.ψ (G.pS (.chi i 0)) (G.pT (.chi i 0)) w (W.cosVec i κ) =
      ((W.ψ (symplOH (G.pS (.chi i 0)) (G.pT (.chi i 0)) (e • w) (cA D e • w + (1 - e - cA D e) • w)))⁻¹ *
        ((W.ψ (symplOH (G.pS (.chi i 0)) (G.pT (.chi i 0)) (cA D e • w) ((1 - e - cA D e) • w)))⁻¹ * (c₃ * c₂))) • W.cosVec i κ' := by
    rw [← smul_smul, ← smul_smul, e2, inv_smul_smul₀ (hne _)]
  rw [heisO_star hψ]
  change star (heisO W.ψ (G.pS (.chi i 0)) (G.pT (.chi i 0)) w (W.cosVec i κ)) ∈ _
  rw [hC, star_smul]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨κ', rfl⟩)
