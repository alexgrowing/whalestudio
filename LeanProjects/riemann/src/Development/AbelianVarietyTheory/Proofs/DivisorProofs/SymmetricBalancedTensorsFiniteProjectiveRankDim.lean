import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigRank
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BalancedSymmetricLieTensorsFiniteProjectiveRankStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentBasisActionMatricesRingHomStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenEigenRankLevelSetIntegersActionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenRankInteriorEqSignatureStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DenseAffineChartPreimageInteriorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmTypeSignatureSumEqTwiceDimensionStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.BalProj

theorem balanced_finite_projective_rank : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)), 1 ≤ Dw.p + Dw.q → SmoothOfRelativeDimension Dw.dim (genStr Y) → ReciprocityTheory.AnForm.R.FinalTheorems.Snc (genBdIdeal Y) → ∀ (U : Y.X.affineOpens) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(Y.X, U.1)) ⟶ Y.t.G.left)) (A : 𝓞 E → Matrix (Fin n) (Fin n) Γ(Y.X, U.1)), (∀ i, IsTanAtG Y.t (chart U) (v i)) → (∀ w, IsTanAtG Y.t (chart U) w → ∃! cf : Fin n → Γ(Y.X, U.1), IsCombAtG Y.t (chart U) v cf w) → (∀ a i, IsCombAtG Y.t (chart U) v (A a i) (v i ≫ (Y.t.act.act a).left)) → Module.Finite Γ(Y.X, U.1) (balanced H.bar A) ∧ Module.Projective Γ(Y.X, U.1) (balanced H.bar A) ∧ ∀ m : Ideal Γ(Y.X, U.1), m.IsMaximal → Module.finrank (Γ(Y.X, U.1) ⧸ m) ((Γ(Y.X, U.1) ⧸ m) ⊗[Γ(Y.X, U.1)] (balanced H.bar A)) = Dw.dim := by
  intro E _ _ _ H Dw l Xo c Y h1 hsm hsnc U n v A hv hb hA
  obtain ⟨h1A, haddA, hmulA⟩ := GlobalTheory.T.tangentBasis_actionMatrices_ringHom H Y.t Γ(Y.X, U.1) (chart U) n v A hv hb hA
  obtain ⟨hfin, hproj, hrk⟩ := GlobalTheory.T.balancedSymmetricLieTensors_finite_projective_rank H c.F c.conj Γ(Y.X, U.1) (GlobalTheory.BalProj.fnHom Y.s U.1) n A h1A haddA hmulA
  refine ⟨hfin, hproj, fun m hm => ?_⟩
  have key : ∀ τ : E →+* ℂ, GlobalTheory.BalProj.eigRank (algebraMap Γ(Y.X, U.1) m.ResidueField) A
      (GlobalTheory.BalProj.embR c.F c.conj (GlobalTheory.BalProj.fnHom Y.s U.1) τ) = if τ (H.rt : E) = H.rt0 then Dw.p else Dw.q := by
    intro τ
    set e : ℕ := if τ (H.rt : E) = H.rt0 then Dw.p else Dw.q with he
    let f : PrimeSpectrum Γ(Y.X, U.1) → ℕ := fun 𝔭 => GlobalTheory.BalProj.eigRank (algebraMap Γ(Y.X, U.1) 𝔭.asIdeal.ResidueField) A
      (GlobalTheory.BalProj.embR c.F c.conj (GlobalTheory.BalProj.fnHom Y.s U.1) τ)
    have hop : ∀ N, IsOpen {𝔭 | f 𝔭 = N} := fun N =>
      GlobalTheory.T.isOpen_eigenRank_levelSet_integersAction c.F c.conj Γ(Y.X, U.1) (GlobalTheory.BalProj.fnHom Y.s U.1) n A h1A haddA hmulA τ N
    have hcl : IsClosed {𝔭 | f 𝔭 = e} := by
      rw [← isOpen_compl_iff]
      have : {𝔭 | f 𝔭 = e}ᶜ = ⋃ N ∈ {N : ℕ | N ≠ e}, {𝔭 | f 𝔭 = N} := by
        ext 𝔭; simp
      rw [this]
      exact isOpen_biUnion fun N _ => hop N
    have hsub : (chart U).base ⁻¹' (interior Y : Set Y.X) ⊆ {𝔭 | f 𝔭 = e} := fun 𝔭 h𝔭 =>
      GlobalTheory.T.eigenRank_interior_eq_signature E H Dw l Xo c Y h1 hsm hsnc U n v A hv hb hA 𝔭 h𝔭 τ
    have hall : {𝔭 | f 𝔭 = e} = Set.univ :=
      Set.eq_univ_of_univ_subset ((GlobalTheory.T.dense_affineChart_preimage_interior E H Dw l Xo c Y U).closure_eq ▸ (closure_mono hsub).trans hcl.closure_subset)
    have := hall ▸ Set.mem_univ (⟨m, hm.isPrime⟩ : PrimeSpectrum Γ(Y.X, U.1))
    exact this
  have h2 := hrk m
  simp_rw [key] at h2
  rw [GlobalTheory.T.cmType_signature_sum_eq_twice_dimension E H Dw.p Dw.q] at h2
  unfold Datum.dim
  omega

end GlobalTheory.BalProj
