import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RangeSndRel
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspidalListedTopForms
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FinCoefMultT
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRealCentralCharacterDefiniteVertexMultipliStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsThetaLiftRealCentreAverageEigenvectorStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CentreEigenThetaFunctionFiniteSumFockPolynomialsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.ColFockRed

open GlobalTheory.Grid

theorem isContAut_cusp {D : D7} {θ : InfFam D} {N : Node D} (F : N.Cusp θ) (x : SmT N.M) :
    GlobalTheory.Unf.IsContAut N.V (F.1 x) := by
  have sm : ∀ {f : GA D N.V → ℂ}, GlobalTheory.Unf.IsContAut N.V f → ∀ c : ℂ, GlobalTheory.Unf.IsContAut N.V (c • f) := fun hf c =>
    ⟨fun γ hγ x => by simp only [Pi.smul_apply, hf.1 γ hγ x], hf.2.const_smul c⟩
  have ad : ∀ {f g : GA D N.V → ℂ}, GlobalTheory.Unf.IsContAut N.V f → GlobalTheory.Unf.IsContAut N.V g → GlobalTheory.Unf.IsContAut N.V (f + g) :=
    fun hf hg => ⟨fun γ hγ x => by simp only [Pi.add_apply, hf.1 γ hγ x, hg.1 γ hγ x], hf.2.add hg.2⟩
  obtain ⟨G, hG⟩ := F
  show GlobalTheory.Unf.IsContAut N.V (G x)
  obtain ⟨T, hT, rfl⟩ := hG
  induction hT using Submodule.span_induction generalizing x with
  | mem T hT =>
    induction x using PiTensorProduct.induction_on with
    | smul_tprod r v =>
      rw [map_smul, LinearEquiv.coe_coe, PiTensorProduct.lift.tprod]
      exact sm ⟨(hT.aut v).left, (hT.aut v).cont⟩ r
    | add x y hx hy => rw [map_add]; exact ad hx hy
  | zero => rw [map_zero, LinearMap.zero_apply]; exact ⟨fun _ _ _ => rfl, continuous_const⟩
  | add T₁ T₂ _ _ h₁ h₂ => rw [map_add, LinearMap.add_apply]; exact ad (h₁ x) (h₂ x)
  | smul c T _ h => rw [map_smul, LinearMap.smul_apply]; exact sm (h x) c

theorem xp_is {D : D7} {G₀ : Type} [Group G₀] [Fintype G₀] {Pl0 T : Type} {A : FamIn D.what₂.LL G₀ Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {G : GlobalTheory.Grid.GridPre R}
    (hG : G.Is) (k : ℕ) (hk : k ≤ D.R.m) : ∃ ν P, (G.Xp k).Is ν 0 P := by
  cases k with
  | zero =>
    have h := hG.spaces.P D.R.m le_rfl
    rw [show (D.R.m - D.R.m + 1) / 2 = 0 by omega] at h
    exact ⟨_, _, h⟩
  | succ k => exact ⟨_, _, hG.spaces.X k hk⟩

theorem measDat_haar_fd {D : D7} {N : Node D} {m : N.MeasDat} {df : Prop} {K : Subgroup (GL (Fin N.V.rank) (Lev.EAf D))}
    (h : m.Is df K) : m.ν.IsHaarMeasure ∧ IsFundamentalDomain (GQ N.V) m.fd m.ν := by
  by_cases hd : df
  · exact ⟨(h.1 hd).1.1, (h.1 hd).2⟩
  · exact ⟨(h.2 hd).1.1, (h.2 hd).2⟩

theorem measX_haar_fd {D : D7} {G₀ : Type} [Group G₀] [Fintype G₀] {Pl0 T : Type} {A : FamIn D.what₂.LL G₀ Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {G : GridPre R}
    (hG : G.Is) (j : ℕ) (hj : j ≤ D.R.m) :
    (G.measX j).ν.IsHaarMeasure ∧ IsFundamentalDomain (GQ (G.Xp j).V) (G.measX j).fd (G.measX j).ν := by
  cases j with
  | zero => exact measDat_haar_fd (hG.meas.P D.R.m le_rfl)
  | succ j => exact measDat_haar_fd (hG.meas.X j hj)

theorem lift_finSum_smooth : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → GlobalTheory.FunPr.Hypotheses₂ → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ t j, j < D.R.m → ∀ Φ, IsThetaFunO R.ψ (G.Xp j).V (G.Xp (j + 1)).V Φ →
    ∀ (n : ℕ) (F : Fin n → (G.Xp j).Cusp R.θ) (w : Fin n → SmT (G.Xp j).M),
    (∀ h, IntegrableOn (fun g => thetaKO (G.col t j).ω g h Φ * (∑ i, (F i).1 (w i)) g) (G.measX j).fd (G.measX j).ν) →
    ∃ (k : ℕ) (F' : Fin k → (G.Xp (j + 1)).Cusp R.θ) (z : Fin k → SmT (G.Xp (j + 1)).M),
      (fun h => ∫ g in (G.measX j).fd, thetaKO (G.col t j).ω g h Φ * (∑ i, (F i).1 (w i)) g ∂(G.measX j).ν) = ∑ i, (F' i).1 (z i) := by
  intro hL _hPr D hSz G₀ _ _ Pl0 T A Ks _ _ _ R G hRB hG t j hj Φ hΦ n F w hint
  have hCA := hL D hSz G₀ Pl0 T A Ks R G hRB hG
  have hθ : IsInfFam R.θ := hRB.inf
  obtain ⟨νS, PS, hS⟩ := xp_is hG j hj.le
  obtain ⟨νT, PT, hT⟩ := xp_is hG (j + 1) hj
  obtain ⟨hsig, hdef⟩ := GlobalTheory.ColTypeLift.xp_definite hG j hj.le
  obtain ⟨χ, hχ⟩ := GlobalTheory.T.exists_realCentralCharacter_definiteVertexMultiplicity D R.θ hθ (G.Xp j) νS PS hS
  have hψc : GlobalTheory.SeeSaw.HasCen (G.Xp j).V χ (∑ i, (F i).1 (w i)) := fun z hz hc h => by
    simp only [Finset.sum_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => hχ (F i) (w i) z hz hc h
  have hψa : GlobalTheory.Unf.IsContAut (G.Xp j).V (∑ i, (F i).1 (w i)) := by
    refine ⟨fun γ hγ g => ?_, by rw [Finset.sum_fn]; exact continuous_finset_sum _ fun i _ => (isContAut_cusp (F i) (w i)).2⟩
    simp only [Finset.sum_apply]
    exact Finset.sum_congr rfl fun i _ => (isContAut_cusp (F i) (w i)).1 γ hγ g
  obtain ⟨hν, hfd⟩ := measX_haar_fd hG j hj.le
  have hA := hG.arrows.col t j hj
  obtain ⟨Φ', hΦ', heig, heq⟩ := GlobalTheory.T.exists_thetaLift_realCentre_average_eigenvector D R.ψ _ _ _ _ (G.col t j).ω hA.weil hsig hdef _ _ hν hfd χ _ hψc hψa Φ hΦ hint
  obtain ⟨k, f, p, hf, hsum⟩ := GlobalTheory.T.centreEigen_thetaFunction_finite_sum_fockPolynomials D R.ψ R.θ hθ (G.Xp j) (G.Xp (j + 1)) νS νT PS PT hS hT (G.col t j) _ _ hA
    (fun z => (χ z)⁻¹) Φ' hΦ' heig
  have hcol := hCA.col t j hj
  choose F' hF' hI using fun (l : Fin k) (i : Fin n) => hcol (f l) (hf l) (F i).1 (F i).2
  refine ⟨k * n, fun q => ⟨F' (finProdFinEquiv.symm q).1 (finProdFinEquiv.symm q).2, hF' _ _⟩,
    fun q => (G.col t j).It (p (finProdFinEquiv.symm q).1) (w (finProdFinEquiv.symm q).2), ?_⟩
  funext h
  rw [heq h, hsum]
  have key : ∀ g, thetaKO (G.col t j).ω g h (∑ l, fock R.ψ R.θ false (G.Xp j) (G.Xp (j + 1)) (f l) (p l)) *
      (∑ i, (F i).1 (w i)) g = ∑ l, ∑ i, thetaKO (G.col t j).ω g h (fock R.ψ R.θ false (G.Xp j) (G.Xp (j + 1)) (f l) (p l)) *
        (F i).1 (w i) g := fun g => by
    simp only [thetaKO, map_sum, Finset.sum_apply, Finset.sum_mul_sum]
  rw [integral_congr_ae (Filter.Eventually.of_forall key)]
  rw [integral_finset_sum _ fun l _ => integrable_finset_sum _ fun i _ => (hI l i (p l) (w i) h).1]
  simp_rw [integral_finset_sum _ fun i _ => (hI _ i _ (w i) h).1]
  have e2 : ∀ l i, ∫ g in (G.measX j).fd, thetaKO (G.col t j).ω g h (fock R.ψ R.θ false (G.Xp j) (G.Xp (j + 1)) (f l) (p l)) *
      (F i).1 (w i) g ∂(G.measX j).ν = F' l i ((G.col t j).It (p l) (w i)) h := fun l i => (hI l i (p l) (w i) h).2
  simp_rw [e2]
  rw [← Fintype.sum_prod_type']
  rw [Finset.sum_apply]
  exact (finProdFinEquiv.symm.sum_comp (fun x : Fin k × Fin n => F' x.1 x.2 ((G.col t j).It (p x.1) (w x.2)) h)).symm

end GlobalTheory.ColFockRed
