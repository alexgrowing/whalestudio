import Mathlib
import Development.AutomorphicArithmetic.ThetaCorrespondence.RallisInnerProduct.ExistsCommonLevelSobolevBoundWeilCompact
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SobContId
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVectorsOverVacuaDenseThetaFunctions
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FockOfVac
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsONBasis
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelWeilSectionDegeneratePrincipalSeriesLaw
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ImportsBis

section
open scoped ComplexConjugate Matrix NNReal ENNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec delta ThetaClause)
open GlobalTheory.Core.Rk.SW (sch)
open GlobalTheory.Mem.AutSpace (SmFun)
open GlobalTheory.Size (sobO thetaLevel)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ThetaDens

namespace UpperTheory.Lit.Rallis
open GlobalTheory

theorem graph_finDim_mem_of_pointwise_tendsto : ∀ (X : Type) (R : Submodule ℂ ((X → ℂ) × (X → ℂ))), (∀ E, (0, E) ∈ R → E = 0) → ∀ X₀ : Submodule ℂ (X → ℂ), FiniteDimensional ℂ X₀ → ∀ (a b : ℕ → X → ℂ) (a' b' : X → ℂ), (∀ j, a j ∈ X₀ ∧ (a j, b j) ∈ R) → (∀ x, Filter.Tendsto (fun j => a j x) Filter.atTop (nhds (a' x))) → (∀ x, Filter.Tendsto (fun j => b j x) Filter.atTop (nhds (b' x))) → (a', b') ∈ R := by
  intro X R hR X₀ hX₀ a b a' b' hab ha hb
  set R0 : Submodule ℂ ((X → ℂ) × (X → ℂ)) := R ⊓ (X₀.prod ⊤) with hR0
  have hmem : ∀ p : R0, p.1.1 ∈ X₀ := fun p => (Submodule.mem_prod.mp (Submodule.mem_inf.mp p.2).2).1
  let f : R0 →ₗ[ℂ] X₀ := LinearMap.codRestrict X₀ ((LinearMap.fst ℂ _ _).comp R0.subtype) hmem
  have hinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro p hp
    rw [LinearMap.mem_ker] at hp
    have h1 : p.1.1 = 0 := by
      exact congrArg Subtype.val hp
    have hpR : p.1 ∈ R := (Submodule.mem_inf.mp p.2).1
    have h2 : p.1.2 = 0 := by
      apply hR
      have : ((p.1.1, p.1.2) : (X → ℂ) × (X → ℂ)) = p.1 := rfl
      rw [← h1]; simpa using hpR
    ext1
    exact Prod.ext h1 h2
  haveI : FiniteDimensional ℂ R0 := Module.Finite.of_injective f hinj
  have hclosed : IsClosed (R0 : Set ((X → ℂ) × (X → ℂ))) := Submodule.closed_of_finiteDimensional R0
  have ht : Filter.Tendsto (fun j => (a j, b j)) Filter.atTop (nhds (a', b')) :=
    (tendsto_pi_nhds.mpr ha).prodMk_nhds (tendsto_pi_nhds.mpr hb)
  have hin : ∀ j, (a j, b j) ∈ R0 := fun j =>
    Submodule.mem_inf.mpr ⟨(hab j).2, Submodule.mem_prod.mpr ⟨(hab j).1, Submodule.mem_top⟩⟩
  have := hclosed.mem_of_tendsto ht (Filter.Eventually.of_forall hin)
  exact (Submodule.mem_inf.mp this).1

end UpperTheory.Lit.Rallis
end

section
open scoped ComplexConjugate Matrix NNReal ENNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec delta ThetaClause)
open GlobalTheory.Core.Rk.SW (sch)
open GlobalTheory.Mem.AutSpace (SmFun)
open GlobalTheory.Size (sobO thetaLevel)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ThetaDens

theorem _root_.UpperTheory.Lit.Rallis.T.pointwise_limit_mem_graphRelation_of_finiteDimensional : ∀ (X : Type) (R : Submodule ℂ ((X → ℂ) × (X → ℂ))), (∀ E, (0, E) ∈ R → E = 0) → ∀ X₀ : Submodule ℂ (X → ℂ), FiniteDimensional ℂ X₀ → ∀ (a b : ℕ → X → ℂ) (a' b' : X → ℂ), (∀ j, a j ∈ X₀ ∧ (a j, b j) ∈ R) → (∀ x, Filter.Tendsto (fun j => a j x) Filter.atTop (nhds (a' x))) → (∀ x, Filter.Tendsto (fun j => b j x) Filter.atTop (nhds (b' x))) → (a', b') ∈ R := by
  first | exact @UpperTheory.Lit.Rallis.graph_finDim_mem_of_pointwise_tendsto | exact UpperTheory.Lit.Rallis.graph_finDim_mem_of_pointwise_tendsto | (intros; apply UpperTheory.Lit.Rallis.graph_finDim_mem_of_pointwise_tendsto <;> assumption)
end

section
open scoped ComplexConjugate Matrix NNReal ENNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec delta ThetaClause)
open GlobalTheory.Core.Rk.SW (sch)
open GlobalTheory.Mem.AutSpace (SmFun)
open GlobalTheory.Size (sobO thetaLevel)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ThetaDens

namespace UpperTheory.Lit.Rallis.FinVecKernel
open GlobalTheory

open Module

theorem exists_reproducing_kernel : ∀ (K : Type) [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K] (ν : Measure K) [ν.IsHaarMeasure] (Y : Type) (ρ : K →* Module.End ℂ (Y → ℂ)) (f : Y → ℂ), FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k => ρ k f)) → (∀ y, Continuous fun k => ρ k f y) → ∃ (e : K → ℂ) (n : ℕ) (a b : Fin n → K → ℂ), Continuous e ∧ (∀ i, Continuous (b i)) ∧ (∀ k₀ k, e (k₀⁻¹ * k) = ∑ i, a i k₀ * b i k) ∧ ∀ y, f y = ∫ k, e k * ρ k f y ∂ν := by
  intro K _ _ _ _ _ _ ν _ Y ρ f hW hcont
  set W := Submodule.span ℂ (Set.range fun k => ρ k f) with hWdef
  haveI : FiniteDimensional ℂ W := hW
  have hmem : ∀ k, ρ k f ∈ W := fun k => Submodule.subset_span ⟨k, rfl⟩
  let o : K → W := fun k => ⟨ρ k f, hmem k⟩
  have ho : Continuous o := (continuous_pi hcont).subtype_mk _
  have hlc : ∀ l : Dual ℂ W, Continuous fun k => l (o k) := fun l =>
    (LinearMap.continuous_of_finiteDimensional l).comp ho
  have hint : ∀ l m : Dual ℂ W, Integrable (fun k => conj (l (o k)) * m (o k)) ν := fun l m =>
    ((Complex.continuous_conj.comp (hlc l)).mul (hlc m)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  let Ψ : Dual ℂ W → Dual ℂ (Dual ℂ W) := fun l =>
    { toFun := fun m => ∫ k, conj (l (o k)) * m (o k) ∂ν
      map_add' := fun m m' => by
        simp only [LinearMap.add_apply, mul_add]
        exact integral_add (hint l m) (hint l m')
      map_smul' := fun c m => by
        simp only [LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply]
        rw [← integral_const_mul]; congr 1; funext k; ring }
  have hΨ : ∀ l m, Ψ l m = ∫ k, conj (l (o k)) * m (o k) ∂ν := fun _ _ => rfl
  let P : Submodule ℂ (Dual ℂ (Dual ℂ W)) :=
    { carrier := {φ | ∃ l, φ = Ψ l}
      add_mem' := by
        rintro _ _ ⟨l, rfl⟩ ⟨l', rfl⟩
        refine ⟨l + l', ?_⟩
        ext m
        simp only [LinearMap.add_apply, hΨ, map_add, add_mul]
        exact (integral_add (hint l m) (hint l' m)).symm
      zero_mem' := ⟨0, by ext m; simp [hΨ]⟩
      smul_mem' := by
        rintro c _ ⟨l, rfl⟩
        refine ⟨(starRingEnd ℂ c) • l, ?_⟩
        ext m
        simp only [LinearMap.smul_apply, smul_eq_mul, hΨ, map_mul, Complex.conj_conj]
        rw [← integral_const_mul]; congr 1; funext k; ring }
  have hev : Module.Dual.eval ℂ W (o 1) ∈ P := by
    by_contra hne
    obtain ⟨Λ, hΛ, hmap⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hne inferInstance
    set m₀ := (Module.evalEquiv ℂ (Dual ℂ W)).symm Λ
    have hΛm : ∀ φ, Λ φ = φ m₀ := fun φ =>
      (Module.apply_evalEquiv_symm_apply (R := ℂ) (M := Dual ℂ W) φ Λ).symm
    have h0 : Λ (Ψ m₀) = 0 := by
      have h1 : Λ (Ψ m₀) ∈ P.map Λ := Submodule.mem_map_of_mem ⟨m₀, rfl⟩
      exact (Submodule.mem_bot ℂ).1 (hmap ▸ h1)
    rw [hΛm, hΨ] at h0
    have hg := hlc m₀
    have hre : ∫ k, Complex.normSq (m₀ (o k)) ∂ν = 0 := by
      have : ((∫ k, Complex.normSq (m₀ (o k)) ∂ν : ℝ) : ℂ) = 0 := by
        rw [← integral_complex_ofReal]; rw [← h0]; congr 1; funext k
        rw [Complex.normSq_eq_conj_mul_self]
      exact_mod_cast this
    have hcn : Continuous fun k => Complex.normSq (m₀ (o k)) := Complex.continuous_normSq.comp hg
    have hae := (integral_eq_zero_iff_of_nonneg (fun k => Complex.normSq_nonneg _)
      (hcn.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))).1 hre
    have hz := (hcn.ae_eq_iff_eq ν continuous_const).1 hae
    have h1 : Complex.normSq (m₀ (o 1)) = 0 := congrFun hz 1
    rw [Complex.normSq_eq_zero] at h1
    apply hΛ; rw [hΛm]; simpa using h1
  obtain ⟨l, hl⟩ := hev
  have hl' : ∀ m : Dual ℂ W, m (o 1) = ∫ k, conj (l (o k)) * m (o k) ∂ν := fun m => by
    rw [← hΨ, ← hl]; rfl
  have hinv : ∀ a : K, ∀ x ∈ W, ρ a x ∈ W := fun a => by
    have : W ≤ W.comap (ρ a) := Submodule.span_le.2 (by
      rintro _ ⟨k, rfl⟩
      have := hmem (a * k)
      rwa [map_mul, Module.End.mul_apply] at this)
    exact fun x hx => this hx
  let R : K → W →ₗ[ℂ] W := fun a => (ρ a).restrict (hinv a)
  have hR : ∀ k₀ k, o (k₀⁻¹ * k) = R k₀⁻¹ (o k) := fun k₀ k => by
    apply Subtype.ext
    simp [o, R, LinearMap.restrict_apply, map_mul, Module.End.mul_apply]
  let B := Module.finBasis ℂ W
  have hexp : ∀ a (w : W), l (R a w) = ∑ i, B.repr w i * l (R a (B i)) := fun a w => by
    calc l (R a w) = l (R a (∑ i, B.repr w i • B i)) := by rw [B.sum_repr]
      _ = _ := by rw [map_sum, map_sum]; simp only [map_smul, smul_eq_mul]
  refine ⟨fun k => conj (l (o k)), Module.finrank ℂ W, fun i k₀ => conj (l (R k₀⁻¹ (B i))),
    fun i k => conj (B.repr (o k) i), Complex.continuous_conj.comp (hlc l), fun i => ?_, ?_, ?_⟩
  · have := Complex.continuous_conj.comp (hlc (B.coord i))
    simpa [Basis.coord_apply, Function.comp_def] using this
  · intro k₀ k
    simp only
    rw [hR, hexp, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, mul_comm]
  · intro y
    have := hl' ((LinearMap.proj y).comp W.subtype)
    simpa [o, map_one] using this

end UpperTheory.Lit.Rallis.FinVecKernel
end

section
open scoped ComplexConjugate Matrix NNReal ENNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec delta ThetaClause)
open GlobalTheory.Core.Rk.SW (sch)
open GlobalTheory.Mem.AutSpace (SmFun)
open GlobalTheory.Size (sobO thetaLevel)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ThetaDens

theorem _root_.UpperTheory.Lit.Rallis.T.exists_continuous_kernel_reproducing_finite_vector : ∀ (K : Type) [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K] (ν : Measure K) [ν.IsHaarMeasure] (Y : Type) (ρ : K →* Module.End ℂ (Y → ℂ)) (f : Y → ℂ), FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k => ρ k f)) → (∀ y, Continuous fun k => ρ k f y) → ∃ (e : K → ℂ) (n : ℕ) (a b : Fin n → K → ℂ), Continuous e ∧ (∀ i, Continuous (b i)) ∧ (∀ k₀ k, e (k₀⁻¹ * k) = ∑ i, a i k₀ * b i k) ∧ ∀ y, f y = ∫ k, e k * ρ k f y ∂ν := by
  first | exact @UpperTheory.Lit.Rallis.FinVecKernel.exists_reproducing_kernel | exact UpperTheory.Lit.Rallis.FinVecKernel.exists_reproducing_kernel | (intros; apply UpperTheory.Lit.Rallis.FinVecKernel.exists_reproducing_kernel <;> assumption)
end

section
open scoped ComplexConjugate Matrix NNReal ENNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec delta ThetaClause)
open GlobalTheory.Core.Rk.SW (sch)
open GlobalTheory.Mem.AutSpace (SmFun)
open GlobalTheory.Size (sobO thetaLevel)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ThetaDens

noncomputable section

namespace UpperTheory.Lit.Rallis.FockDensCart
open GlobalTheory

theorem exists_fr_of_cartanInv {D : D7} (V : HSp D) (s : RealMat V) (hs : ∀ τ, IsCartanInv (gramAt D V τ) (s τ)) :
    ∃ A : GlobalTheory.ChainFr.Fr V, A.cart = s := by
  have key : ∀ τ, ∃ (ε : Fin V.rank → Bool) (B : Matrix (Fin V.rank) (Fin V.rank) ℂ), IsUnit B.det ∧
      Bᴴ * gramAt D V τ * B = Formalism.REAL.Jm ε ∧ s τ * B = B * Formalism.REAL.Jm ε := by
    intro τ
    obtain ⟨p, B, ε, h1, h2, h3⟩ := GlobalTheory.FrameLawsTheta.exists_isONBasis (hs τ)
    have hJ : Matrix.diagonal (fun a => (ε a : ℂ)) = Formalism.REAL.Jm (fun a => decide (a.val < p)) := by
      unfold Formalism.REAL.Jm
      congr 1
      funext a
      rcases h1 a with ⟨e, ha⟩ | ⟨e, ha⟩
      · simp [e, ha]
      · simp [e, show ¬ a.val < p by omega]
    rw [hJ] at h2 h3
    refine ⟨_, B, ?_, h2, h3⟩
    have hd := congrArg Matrix.det h2
    rw [Matrix.det_mul, Matrix.det_mul] at hd
    refine isUnit_iff_ne_zero.2 fun h0 => ?_
    rw [h0, mul_zero] at hd
    have hJd : (Formalism.REAL.Jm (fun a : Fin V.rank => decide (a.val < p))).det ≠ 0 := by
      unfold Formalism.REAL.Jm
      rw [Matrix.det_diagonal]
      exact Finset.prod_ne_zero_iff.2 fun a _ => by split_ifs <;> norm_num
    exact hJd hd.symm
  choose ε B hu hg hc using key
  refine ⟨⟨ε, fun τ => (B τ)⁻¹, fun τ => ?_, fun τ => ?_⟩, funext fun τ => ?_⟩
  · exact (Matrix.isUnit_iff_isUnit_det _).2 (Matrix.isUnit_nonsing_inv_det _ (hu τ))
  · show ((B τ)⁻¹)ᴴ * Formalism.REAL.Jm (ε τ) * (B τ)⁻¹ = gramAt D V τ
    rw [← hg τ]
    have h1 : ((B τ)⁻¹)ᴴ * (B τ)ᴴ = 1 := by
      rw [← Matrix.conjTranspose_mul, Matrix.mul_nonsing_inv _ (hu τ), Matrix.conjTranspose_one]
    calc _ = (((B τ)⁻¹)ᴴ * (B τ)ᴴ) * gramAt D V τ * (B τ * (B τ)⁻¹) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [h1, Matrix.mul_nonsing_inv _ (hu τ), Matrix.one_mul, Matrix.mul_one]
  · show ((B τ)⁻¹)⁻¹ * Formalism.REAL.Jm (ε τ) * (B τ)⁻¹ = s τ
    rw [Matrix.nonsing_inv_nonsing_inv _ (hu τ), ← hc τ, Matrix.mul_nonsing_inv_cancel_right _ _ (hu τ)]

section Fock

open GlobalTheory.FockIndep GlobalTheory.OrientedHeis GlobalTheory.ChainFr

variable {D : D7} {S T : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D}

theorem ptF_fock (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (A : Fr S) (B : Fr T) {f : WO S T → ℂ}
    (hf : IsVacF ψ θ A B f) (P : MvPolynomial (FVar D T.rank S.rank) ℂ) :
    IsThetaFunO ψ S T (ptF ψ θ A B f P) ∧ ∀ l : List (D.what₂.Tau × Matrix (Fin T.rank) (Fin S.rank) ℂ),
      P.totalDegree < l.length →
        l.foldr (fun p g => annih (heisO ψ S T) θ p.1 (cplxO (A.cart p.1) (B.cart p.1)) p.2 g) (ptF ψ θ A B f P) = 0 := by
  have hS : ∀ τ, IsCartanInv (gramAt D S τ) (A.cart τ) := GlobalTheory.ChainFr.Model.isCartanInv_cart A
  have hT : ∀ τ, IsCartanInv (gramAt D T τ) (B.cart τ) := GlobalTheory.ChainFr.Model.isCartanInv_cart B
  set Ap := aPlusAll (heisO ψ S T) θ (fun τ => cplxO (A.cart τ) (B.cart τ)) A.onb B.onb with hAdef
  have hadd : ∀ g g', IsThetaFunO ψ S T g → IsThetaFunO ψ S T g' → IsThetaFunO ψ S T (g + g') :=
    fun _ _ => theta_add
  have hsm : ∀ (a : ℂ) g, IsThetaFunO ψ S T g → IsThetaFunO ψ S T (a • g) := fun a _ => theta_smul a
  have hA : ∀ k g, IsThetaFunO ψ S T g → IsThetaFunO ψ S T (Ap k g) := fun _ _ h => aPlus_theta hψ hθ _ _ _ h
  have hc : ∀ i j g, IsThetaFunO ψ S T g → Ap i (Ap j g) = Ap j (Ap i g) :=
    fun i j _ h => aPlus_comm' hψ hθ i.1 _ hS hT j.1 _ h
  have Aadd : ∀ i g g', IsThetaFunO ψ S T g → IsThetaFunO ψ S T g' → Ap i (g + g') = Ap i g + Ap i g' :=
    fun i _ _ h h' => aPlus_add hψ hθ i.1 _ _ h h'
  have Asm : ∀ i (a : ℂ) g, IsThetaFunO ψ S T g → Ap i (a • g) = a • Ap i g :=
    fun i a _ h => aPlus_smul hψ hθ i.1 _ _ a h
  have hpt : ∀ Q, ptF ψ θ A B f Q = pureTensorL Ap f Q := fun _ => rfl
  have hm : ∀ Q, IsThetaFunO ψ S T (pureTensorL Ap f Q) := pure_mem hadd hsm hA hf.1
  have hder : ∀ (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ), ∃ c : FVar D T.rank S.rank → ℂ, ∀ Q,
      annih (heisO ψ S T) θ τ (cplxO (A.cart τ) (B.cart τ)) z (pureTensorL Ap f Q) =
        pureTensorL Ap f (∑ i, c i • MvPolynomial.pderiv i Q) := by
    intro τ z
    refine ⟨fun k => (fockScale D k.1 : ℂ)⁻¹ * (-(4 * Real.pi * Complex.I) *
      ((omDir S T τ z k.1 (unitMap (A.onb k.1) (B.onb k.1) k.2.1 k.2.2) : ℝ) +
        Complex.I * (omDir S T τ (cplxO (A.cart τ) (B.cart τ) z) k.1
          (unitMap (A.onb k.1) (B.onb k.1) k.2.1 k.2.2) : ℝ))), fun Q => ?_⟩
    exact GlobalTheory.ArchRec.DerFock.pure_deriv hadd hsm hA hc Aadd Asm
      (fun _ _ h h' => annih_add hψ hθ _ _ _ h h') (fun a _ h => annih_smul hψ hθ _ _ _ a h)
      (fun j _ h => GlobalTheory.FockIndep.annih_aPlus hψ hθ τ z hS hT j.1 _ h) hf.1 (hf.2 τ z) Q
  refine ⟨by rw [hpt]; exact hm P, fun l hl => ?_⟩
  have key : ∀ l : List (D.what₂.Tau × Matrix (Fin T.rank) (Fin S.rank) ℂ), ∃ Q : MvPolynomial (FVar D T.rank S.rank) ℂ,
      l.foldr (fun p g => annih (heisO ψ S T) θ p.1 (cplxO (A.cart p.1) (B.cart p.1)) p.2 g) (pureTensorL Ap f P) =
        pureTensorL Ap f Q ∧ ∀ m : FVar D T.rank S.rank →₀ ℕ, P.totalDegree < m.degree + l.length → Q.coeff m = 0 := by
    intro l
    induction l with
    | nil =>
      refine ⟨P, rfl, fun m hm' => MvPolynomial.coeff_eq_zero_of_totalDegree_lt ?_⟩
      have h' : P.totalDegree < m.degree := by simpa using hm'
      exact h'
    | cons p l ih =>
      obtain ⟨Q, hQ, hQc⟩ := ih
      obtain ⟨c, hc'⟩ := hder p.1 p.2
      refine ⟨∑ i, c i • MvPolynomial.pderiv i Q, ?_, fun m hm' => ?_⟩
      · rw [List.foldr_cons, hQ, hc']
      · refine GlobalTheory.FockVecOfVac.coeff_sum_pderiv_eq_zero c Q (P.totalDegree - l.length)
          (fun m' hm'' => hQc m' (by omega)) m ?_
        simp only [List.length_cons] at hm'
        omega
  obtain ⟨Q, hQ, hQc⟩ := key l
  have hQ0 : Q = 0 := MvPolynomial.ext _ _ fun m => by
    rw [hQc m (by omega), MvPolynomial.coeff_zero]
  rw [hpt, hQ, hQ0, map_zero]

end Fock

section Span

open GlobalTheory.FockIndep GlobalTheory.OrientedHeis GlobalTheory.ChainFr

variable {D : D7} {S T : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D}

theorem fold_laws (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (sS : RealMat S) (sT : RealMat T)
    (l : List (D.what₂.Tau × Matrix (Fin T.rank) (Fin S.rank) ℂ)) :
    (∀ g, IsThetaFunO ψ S T g →
      IsThetaFunO ψ S T (l.foldr (fun p g => annih (heisO ψ S T) θ p.1 (cplxO (sS p.1) (sT p.1)) p.2 g) g)) ∧
    (∀ g g', IsThetaFunO ψ S T g → IsThetaFunO ψ S T g' →
      l.foldr (fun p g => annih (heisO ψ S T) θ p.1 (cplxO (sS p.1) (sT p.1)) p.2 g) (g + g') =
        l.foldr (fun p g => annih (heisO ψ S T) θ p.1 (cplxO (sS p.1) (sT p.1)) p.2 g) g +
          l.foldr (fun p g => annih (heisO ψ S T) θ p.1 (cplxO (sS p.1) (sT p.1)) p.2 g) g') ∧
    (∀ (a : ℂ) g, IsThetaFunO ψ S T g →
      l.foldr (fun p g => annih (heisO ψ S T) θ p.1 (cplxO (sS p.1) (sT p.1)) p.2 g) (a • g) =
        a • l.foldr (fun p g => annih (heisO ψ S T) θ p.1 (cplxO (sS p.1) (sT p.1)) p.2 g) g) := by
  induction l with
  | nil => exact ⟨fun g h => h, fun _ _ _ _ => rfl, fun _ _ _ => rfl⟩
  | cons p l ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    refine ⟨fun g h => annih_theta hψ hθ _ _ _ (h1 g h), fun g g' h h' => ?_, fun a g h => ?_⟩
    · simp only [List.foldr_cons]
      rw [h2 g g' h h', annih_add hψ hθ _ _ _ (h1 g h) (h1 g' h')]
    · simp only [List.foldr_cons]
      rw [h3 a g h, annih_smul hψ hθ _ _ _ a (h1 g h)]

theorem isFockVec_of_mem (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (A : Fr S) (B : Fr T) (U : AddSubgroup (WO S T))
    {g : WO S T → ℂ} (hg : g ∈ fockSpan ψ θ A B U) : IsFockVec ψ θ S T A.cart B.cart g := by
  have L := fun l => fold_laws hψ hθ A.cart B.cart (θ := θ) l
  suffices H : IsThetaFunO ψ S T g ∧ ∃ N : ℕ, ∀ l : List (D.what₂.Tau × Matrix (Fin T.rank) (Fin S.rank) ℂ),
      N ≤ l.length → l.foldr (fun p f => annih (heisO ψ S T) θ p.1 (cplxO (A.cart p.1) (B.cart p.1)) p.2 f) g = 0 by
    obtain ⟨h1, N, h2⟩ := H
    exact ⟨h1, N, fun l hl => h2 l hl.ge⟩
  induction hg using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f₀, P, hv, -, rfl⟩ := hx
    obtain ⟨h1, h2⟩ := ptF_fock hψ hθ A B hv P
    exact ⟨h1, P.totalDegree + 1, fun l hl => h2 l (by omega)⟩
  | zero =>
    refine ⟨theta_zero, 0, fun l _ => ?_⟩
    have := (L l).2.2 0 0 theta_zero
    rwa [zero_smul, zero_smul] at this
  | add x y _ _ hx hy =>
    obtain ⟨hx1, N, hx2⟩ := hx
    obtain ⟨hy1, M, hy2⟩ := hy
    refine ⟨theta_add hx1 hy1, max N M, fun l hl => ?_⟩
    rw [(L l).2.1 x y hx1 hy1, hx2 l (le_of_max_le_left hl), hy2 l (le_of_max_le_right hl), add_zero]
  | smul a x _ hx =>
    obtain ⟨hx1, N, hx2⟩ := hx
    refine ⟨theta_smul a hx1, N, fun l hl => ?_⟩
    rw [(L l).2.2 a x hx1, hx2 l hl, smul_zero]

end Span

theorem fockDense_cart : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ S T : HSp D, ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 → ∀ (sS : RealMat S) (sT : RealMat T), (∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) → (∀ τ, IsCartanInv (gramAt D T τ) (sT τ)) → ∀ f, IsThetaFunO ψ S T f → ∃ U : AddSubgroup (WO S T), IsOpen (U : Set (WO S T)) ∧ f ∈ GlobalTheory.Size.thetaLevel ψ S T U ∧ ∀ (d : ℕ) (δ : ℝ≥0∞), 0 < δ → ∃ g, IsFockVec ψ θ S T sS sT g ∧ g ∈ GlobalTheory.Size.thetaLevel ψ S T U ∧ sobO ψ θ μ 𝓕 d (f - g) < δ := by
  intro D ψ hψ θ hθ S T μ 𝓕 hm sS sT hsS hsT f hf
  obtain ⟨A, rfl⟩ := exists_fr_of_cartanInv S sS hsS
  obtain ⟨B, rfl⟩ := exists_fr_of_cartanInv T sT hsT
  obtain ⟨U, hU, hfU, hd⟩ := GlobalTheory.FockDensity.fockDense D S T A B θ ψ hψ hθ μ 𝓕 hm f hf
  refine ⟨U, hU, hfU, fun d δ hδ => ?_⟩
  obtain ⟨g, hg, hgU, hlt⟩ := hd d δ hδ
  exact ⟨g, isFockVec_of_mem hψ hθ A B U hg, hgU, hlt⟩

end UpperTheory.Lit.Rallis.FockDensCart
end
end

section
open scoped ComplexConjugate Matrix NNReal ENNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec delta ThetaClause)
open GlobalTheory.Core.Rk.SW (sch)
open GlobalTheory.Mem.AutSpace (SmFun)
open GlobalTheory.Size (sobO thetaLevel)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ThetaDens

theorem _root_.UpperTheory.Lit.Rallis.T.thetaFun_approx_by_fockVectors_of_cartanInvolutions : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ S T : HSp D, ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 → ∀ (sS : RealMat S) (sT : RealMat T), (∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) → (∀ τ, IsCartanInv (gramAt D T τ) (sT τ)) → ∀ f, IsThetaFunO ψ S T f → ∃ U : AddSubgroup (WO S T), IsOpen (U : Set (WO S T)) ∧ f ∈ thetaLevel ψ S T U ∧ ∀ (d : ℕ) (δ : ℝ≥0∞), 0 < δ → ∃ g, IsFockVec ψ θ S T sS sT g ∧ g ∈ thetaLevel ψ S T U ∧ sobO ψ θ μ 𝓕 d (f - g) < δ := by
  first | exact @UpperTheory.Lit.Rallis.FockDensCart.fockDense_cart | exact UpperTheory.Lit.Rallis.FockDensCart.fockDense_cart | (intros; apply UpperTheory.Lit.Rallis.FockDensCart.fockDense_cart <;> assumption)
end

section
open MeasureTheory

namespace UpperTheory.Lit.Rallis
open GlobalTheory

theorem exists_continuous_coords_of_finiteDimensional_span
    {K : Type} [TopologicalSpace K] {Y : Type} (ρ : K → Y → ℂ)
    (hfd : FiniteDimensional ℂ (Submodule.span ℂ (Set.range ρ)))
    (hρ : ∀ y, Continuous fun k => ρ k y) :
    ∃ (n : ℕ) (b : Fin n → Submodule.span ℂ (Set.range ρ)) (c : Fin n → K → ℂ),
      (∀ i, Continuous (c i)) ∧
      ∀ k, (⟨ρ k, Submodule.subset_span ⟨k, rfl⟩⟩ : Submodule.span ℂ (Set.range ρ))
        = ∑ i, c i k • b i := by
  let V := Submodule.span ℂ (Set.range ρ)
  let b := Module.finBasis ℂ V
  let r : K → V := fun k => ⟨ρ k, Submodule.subset_span ⟨k, rfl⟩⟩
  have hr : Continuous r := Continuous.subtype_mk (continuous_pi hρ) _
  refine ⟨_, b, fun i k => b.coord i (r k), fun i => ?_, fun k => ?_⟩
  · exact (LinearMap.continuous_of_finiteDimensional (b.coord i)).comp hr
  · exact (b.sum_repr (r k)).symm

theorem weightedIntegral_mem_span_and_map_integral :
    ∀ (K : Type) [TopologicalSpace K] [CompactSpace K] [T2Space K] [MeasurableSpace K] [OpensMeasurableSpace K] (ν : Measure K) [IsFiniteMeasure ν] (Y : Type) (ρ : K → Y → ℂ) (e : K → ℂ), Continuous e → FiniteDimensional ℂ (Submodule.span ℂ (Set.range ρ)) → (∀ y, Continuous fun k => ρ k y) → (fun y => ∫ k, e k * ρ k y ∂ν) ∈ Submodule.span ℂ (Set.range ρ) ∧ ∀ Λ : (Y → ℂ) → ℂ, (∀ f ∈ Submodule.span ℂ (Set.range ρ), ∀ f' ∈ Submodule.span ℂ (Set.range ρ), Λ (f + f') = Λ f + Λ f') → (∀ (c : ℂ), ∀ f ∈ Submodule.span ℂ (Set.range ρ), Λ (c • f) = c * Λ f) → Λ (fun y => ∫ k, e k * ρ k y ∂ν) = ∫ k, e k * Λ (ρ k) ∂ν := by
  intro K _ _ _ _ _ ν _ Y ρ e he hfd hρ
  obtain ⟨n, b, c, hc, hrep⟩ := exists_continuous_coords_of_finiteDimensional_span ρ hfd hρ
  have hint : ∀ i, Integrable (fun k => e k * c i k) ν := fun i => by
    have h : ContinuousOn (fun k => e k * c i k) Set.univ := (he.mul (hc i)).continuousOn
    exact integrableOn_univ.mp (h.integrableOn_compact' isCompact_univ MeasurableSet.univ)
  have key : ∀ (L : Submodule.span ℂ (Set.range ρ) →ₗ[ℂ] ℂ),
      ∫ k, e k * L ⟨ρ k, Submodule.subset_span ⟨k, rfl⟩⟩ ∂ν
        = L (∑ i, (∫ k, e k * c i k ∂ν) • b i) := by
    intro L
    have h1 : ∀ k, e k * L ⟨ρ k, Submodule.subset_span ⟨k, rfl⟩⟩
        = ∑ i, (e k * c i k) * L (b i) := by
      intro k
      rw [hrep k, map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, smul_eq_mul, mul_assoc]
    simp_rw [h1]
    rw [integral_finset_sum _ (fun i _ => (hint i).mul_const _), map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_mul_const, map_smul, smul_eq_mul]
  set w : Submodule.span ℂ (Set.range ρ) := ∑ i, (∫ k, e k * c i k ∂ν) • b i with hw
  have hfun : (fun y => ∫ k, e k * ρ k y ∂ν) = (w : Y → ℂ) := by
    funext y
    exact key ((LinearMap.proj y).comp (Submodule.span ℂ (Set.range ρ)).subtype)
  refine ⟨hfun ▸ w.2, fun Λ hadd hsmul => ?_⟩
  let L : Submodule.span ℂ (Set.range ρ) →ₗ[ℂ] ℂ :=
    { toFun := fun v => Λ v
      map_add' := fun u v => hadd _ u.2 _ v.2
      map_smul' := fun a v => hsmul a _ v.2 }
  rw [hfun]
  exact (key L).symm

end UpperTheory.Lit.Rallis
end

section
open MeasureTheory

theorem _root_.UpperTheory.Lit.Rallis.T.weighted_integral_mem_span_of_finiteDimensional_orbit : ∀ (K : Type) [TopologicalSpace K] [CompactSpace K] [T2Space K] [MeasurableSpace K] [OpensMeasurableSpace K] (ν : Measure K) [IsFiniteMeasure ν] (Y : Type) (ρ : K → Y → ℂ) (e : K → ℂ), Continuous e → FiniteDimensional ℂ (Submodule.span ℂ (Set.range ρ)) → (∀ y, Continuous fun k => ρ k y) → (fun y => ∫ k, e k * ρ k y ∂ν) ∈ Submodule.span ℂ (Set.range ρ) ∧ ∀ Λ : (Y → ℂ) → ℂ, (∀ f ∈ Submodule.span ℂ (Set.range ρ), ∀ f' ∈ Submodule.span ℂ (Set.range ρ), Λ (f + f') = Λ f + Λ f') → (∀ (c : ℂ), ∀ f ∈ Submodule.span ℂ (Set.range ρ), Λ (c • f) = c * Λ f) → Λ (fun y => ∫ k, e k * ρ k y ∂ν) = ∫ k, e k * Λ (ρ k) ∂ν := by
  first | exact @UpperTheory.Lit.Rallis.weightedIntegral_mem_span_and_map_integral | exact UpperTheory.Lit.Rallis.weightedIntegral_mem_span_and_map_integral | (intros; apply UpperTheory.Lit.Rallis.weightedIntegral_mem_span_and_map_integral <;> assumption)
end

section
open scoped ComplexConjugate Matrix NNReal ENNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec delta ThetaClause)
open GlobalTheory.Core.Rk.SW (sch)
open GlobalTheory.Mem.AutSpace (SmFun)
open GlobalTheory.Size (sobO thetaLevel)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ThetaDens

noncomputable section
namespace UpperTheory.Lit.Rallis.SWFinSpan
open GlobalTheory

theorem swSec_mem_finiteDimensional : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D) (χ : (AE D)ˣ →* Circle) (om : GA D (dblSp A) × GA D B →* Module.End ℂ (WO (dblSp A) B → ℂ)), IsWeilDatumO ψ (dblSp A) B 1 χ om → ∀ (ν : Measure (WO A B)) (𝓨 : Set (WO A B)), IsCovolOne (ratL B A) ν 𝓨 → ∀ a : GL (Fin A.rank) (AE D), HasIwasawa D.sp.cm.sig (dblSp A).gram (Khat A a) → ∀ (n : ℕ) (α : Fin n → Khat A a → ℂ), ∃ X₀ : Submodule ℂ (GA D (dblSp A) → ℂ), FiniteDimensional ℂ X₀ ∧ ∀ φ, IsThetaFunO ψ (dblSp A) B φ → ∀ β : Fin n → ℂ, (∀ k : Khat A a, swSec A B om ν 𝓨 φ k = ∑ i, β i * α i k) → swSec A B om ν 𝓨 φ ∈ X₀ := by
  intro D ψ A B χ om hom ν 𝓨 hν a hI n α
  have hI' : ∀ g : GA D (dblSp A), ∃ p : siegel A, ∃ k : Khat A a, g = (p : GA D (dblSp A)) * (k : GA D (dblSp A)) := by
    intro g
    obtain ⟨p, k, hk, h⟩ := hI g
    exact ⟨p, ⟨k, hk⟩, h⟩
  choose p k hpk using hI'
  let c : GA D (dblSp A) → ℂ := fun g => (χ⁻¹ (aP A (p g)) : Circle) *
    npow (absA D (aP A (p g))) (sZero A B + (A.rank : ℂ) / 2)
  let F : Fin n → GA D (dblSp A) → ℂ := fun i g => c g * α i (k g)
  refine ⟨Submodule.span ℂ (Set.range F), FiniteDimensional.span_of_finite ℂ (Set.finite_range F), ?_⟩
  intro φ hφ β hβ
  have h : swSec A B om ν 𝓨 φ = ∑ i, β i • F i := by
    funext g
    have h1 := GlobalTheory.Core.Rk.SWLaw.swSec_law GlobalTheory.weilRepresentationUnitaryPair D ψ A B χ om hom ν 𝓨 hν φ hφ (p g) (k g)
    rw [← hpk g, hβ (k g)] at h1
    rw [h1, Finset.sum_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [F, c, Pi.smul_apply, smul_eq_mul]
    ring
  rw [h]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

end UpperTheory.Lit.Rallis.SWFinSpan

end
end

section
open scoped ComplexConjugate Matrix NNReal ENNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec delta ThetaClause)
open GlobalTheory.Core.Rk.SW (sch)
open GlobalTheory.Mem.AutSpace (SmFun)
open GlobalTheory.Size (sobO thetaLevel)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ThetaDens

theorem _root_.UpperTheory.Lit.Rallis.T.exists_finiteDimensional_space_of_siegelWeilSections : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D) (χ : (AE D)ˣ →* Circle) (om : GA D (dblSp A) × GA D B →* Module.End ℂ (WO (dblSp A) B → ℂ)), IsWeilDatumO ψ (dblSp A) B 1 χ om → ∀ (ν : Measure (WO A B)) (𝓨 : Set (WO A B)), IsCovolOne (ratL B A) ν 𝓨 → ∀ a : GL (Fin A.rank) (AE D), HasIwasawa D.sp.cm.sig (dblSp A).gram (Khat A a) → ∀ (n : ℕ) (α : Fin n → Khat A a → ℂ), ∃ X₀ : Submodule ℂ (GA D (dblSp A) → ℂ), FiniteDimensional ℂ X₀ ∧ ∀ φ, IsThetaFunO ψ (dblSp A) B φ → ∀ β : Fin n → ℂ, (∀ k : Khat A a, swSec A B om ν 𝓨 φ k = ∑ i, β i * α i k) → swSec A B om ν 𝓨 φ ∈ X₀ := by
  first | exact @UpperTheory.Lit.Rallis.SWFinSpan.swSec_mem_finiteDimensional | exact UpperTheory.Lit.Rallis.SWFinSpan.swSec_mem_finiteDimensional | (intros; apply UpperTheory.Lit.Rallis.SWFinSpan.swSec_mem_finiteDimensional <;> assumption)
end

section
open scoped ComplexConjugate Matrix NNReal ENNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec delta ThetaClause)
open GlobalTheory.Core.Rk.SW (sch)
open GlobalTheory.Mem.AutSpace (SmFun)
open GlobalTheory.Size (sobO thetaLevel)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ThetaDens

namespace UpperTheory.Lit.Rallis.ThetaDens
open GlobalTheory

theorem swSec_sobBdd : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D) (χ : (AE D)ˣ →* Circle) (om : GA D (dblSp A) × GA D B →* Module.End ℂ (WO (dblSp A) B → ℂ)), IsWeilDatumO ψ (dblSp A) B 1 χ om → ∀ θ : InfFam D, IsInfFam θ → ∀ (ν : Measure (WO A B)) (𝓨 : Set (WO A B)), IsCovolOne (ratL B A) ν 𝓨 → ∀ (μ : Measure (WO (dblSp A) B)) (𝓕 : Set (WO (dblSp A) B)), IsCovolOne (ratL B (dblSp A)) μ 𝓕 → SobBdd ψ θ μ 𝓕 fun φ y => ‖swSec A B om ν 𝓨 φ y‖ₑ := by
  intro D ψ A B χ om hom θ hθ ν 𝓨 hν μ 𝓕 hμ U hU K hK
  obtain ⟨U', hU', hlev, hb⟩ := UpperTheory.Lit.Rallis.ThetaDens.om_compact_sobCont D ψ (dblSp A) B 1 χ om hom θ hθ μ 𝓕 hμ
    ((fun y => (y, (1 : GA D B))) '' K) (hK.image (continuous_id.prodMk continuous_const)) U hU
  obtain ⟨d₁, C₁, h₁⟩ := UpperTheory.Lit.Rallis.ThetaDensSup.sup_le_sobO D ψ hom.std θ hθ (dblSp A) B μ 𝓕 hμ U' hU'
  obtain ⟨d', C', h'⟩ := hb d₁
  refine ⟨d', C₁ * C', fun f hf y hy => ?_⟩
  have hm : (y, (1 : GA D B)) ∈ (fun y => (y, (1 : GA D B))) '' K := ⟨y, hy, rfl⟩
  have hsup := h₁ _ (hlev f hf _ hm)
  have hle := h' f hf _ hm
  have hone : ν 𝓨 = 1 := hν.2.2
  unfold swSec GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.evZero
  refine (enorm_integral_le_lintegral_enorm _).trans ?_
  refine (lintegral_mono fun w => hsup _).trans ?_
  rw [lintegral_const, Measure.restrict_apply_univ, hone, mul_one, ENNReal.coe_mul, mul_assoc]
  gcongr

end UpperTheory.Lit.Rallis.ThetaDens
end

section
open scoped ComplexConjugate Matrix NNReal ENNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec delta ThetaClause)
open GlobalTheory.Core.Rk.SW (sch)
open GlobalTheory.Mem.AutSpace (SmFun)
open GlobalTheory.Size (sobO thetaLevel)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ThetaDens

theorem _root_.UpperTheory.Lit.Rallis.T.siegelWeilSection_bounded_by_sobolevSeminorm : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D) (χ : (AE D)ˣ →* Circle) (om : GA D (dblSp A) × GA D B →* Module.End ℂ (WO (dblSp A) B → ℂ)), IsWeilDatumO ψ (dblSp A) B 1 χ om → ∀ θ : InfFam D, IsInfFam θ → ∀ (ν : Measure (WO A B)) (𝓨 : Set (WO A B)), IsCovolOne (ratL B A) ν 𝓨 → ∀ (μ : Measure (WO (dblSp A) B)) (𝓕 : Set (WO (dblSp A) B)), IsCovolOne (ratL B (dblSp A)) μ 𝓕 → SobBdd ψ θ μ 𝓕 fun φ y => ‖swSec A B om ν 𝓨 φ y‖ₑ := by
  first | exact @UpperTheory.Lit.Rallis.ThetaDens.swSec_sobBdd | exact UpperTheory.Lit.Rallis.ThetaDens.swSec_sobBdd | (intros; apply UpperTheory.Lit.Rallis.ThetaDens.swSec_sobBdd <;> assumption)
end
