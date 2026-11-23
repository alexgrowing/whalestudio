import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasInfExpDiv
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsPairReading
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LieActionFockOperatorsScalarsTrace
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffOfContinuousOneParameter
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasArchimedeanCharExponentsConjOfHasInfExp
import Development.AbelianVarietyTheory.Proofs.HeightProofs.AdelicUnitaryActionAtRealPlace
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SignedUnitaryGroupCompat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralNormSqEqToL2

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped ComplexConjugate
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun

open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.OmegaDer

section Mat
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

theorem exists_gen {n : ℕ} (G : Matrix (Fin n) (Fin n) ℂ) (m : ℝ → Matrix (Fin n) (Fin n) ℂ) (hc : Continuous m)
    (h0 : m 0 = 1) (hadd : ∀ s t, m (s + t) = m s * m t) (hG : ∀ t, (m t)ᴴ * G * m t = G) :
    ∃ Z : Matrix (Fin n) (Fin n) ℂ, Zᴴ * G + G * Z = 0 ∧ ∀ t : ℝ, m t = NormedSpace.exp (t • Z) := by
  haveI : CompleteSpace (Matrix (Fin n) (Fin n) ℂ) := FiniteDimensional.complete ℝ _
  have h := ((GlobalTheory.contDiff_of_continuous_oneParameter _ m hc h0 hadd).differentiable (by simp) 0).hasDerivAt
  set Z := deriv m 0
  refine ⟨Z, ?_, fun t => ?_⟩
  · let c : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ :=
      { toFun := fun A => Aᴴ
        map_add' := fun A B => conjTranspose_add A B
        map_smul' := fun r A => by rw [conjTranspose_smul, star_trivial]; rfl }
    have h1 : HasDerivAt (fun t => (m t)ᴴ) Zᴴ 0 :=
      (LinearMap.toContinuousLinearMap c).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h
    have h2 := (h1.mul_const G).fun_mul h
    simp only [hG, h0, conjTranspose_one, Matrix.mul_one, Matrix.one_mul] at h2
    exact h2.unique (hasDerivAt_const _ _)
  · have hd : ∀ s, HasDerivAt m (m s * Z) s := fun s => by
      have h1 : HasDerivAt (fun u => m s * m (u - s)) (m s * Z) s := by
        refine HasDerivAt.const_mul _ ?_
        have h2 : HasDerivAt m Z (s - s) := by rwa [sub_self]
        exact h2.comp_sub_const s s
      refine h1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun u => ?_)
      beta_reduce
      rw [← hadd, add_sub_cancel]
    have hk : ∀ s, HasDerivAt (fun u : ℝ => m u * NormedSpace.exp (u • (-Z))) 0 s := fun s => by
      refine ((hd s).fun_mul (hasDerivAt_exp_smul_const' (𝕂 := ℝ) (-Z) s)).congr_deriv ?_
      rw [Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_assoc, add_neg_cancel]
    have hcst := is_const_of_deriv_eq_zero (fun s => (hk s).differentiableAt) (fun s => (hk s).deriv) t 0
    simp only [zero_smul, NormedSpace.exp_zero, h0, Matrix.mul_one] at hcst
    have e : NormedSpace.exp (t • (-Z)) * NormedSpace.exp (t • Z) = 1 := by
      rw [smul_neg, ← Matrix.exp_add_of_commute _ _ (Commute.refl (t • Z)).neg_left, neg_add_cancel,
        NormedSpace.exp_zero]
    calc m t = m t * (NormedSpace.exp (t • (-Z)) * NormedSpace.exp (t • Z)) := by rw [e, Matrix.mul_one]
      _ = _ := by rw [← Matrix.mul_assoc, hcst, Matrix.one_mul]

end Mat

variable {D : D7}

theorem exists_expInf {θ : InfFam D} (hθ : IsInfFam θ) (V : HSp D) (g : ℝ → GA D V) (hc : Continuous g)
    (hadd : ∀ s t, g (s + t) = g s * g t) (hinf : ∀ t, g t ∈ GinfC V) :
    ∃ Z : GlobalTheory.SmoothForms.LieN V, ∀ t : ℝ, g t = GlobalTheory.SmoothForms.expInf θ V (t • Z) := by
  have R := (GlobalTheory.T.adelicUnitary_realPoints_structure_realPlaces D).2 θ hθ V
  have h0 : g 0 = 1 := by
    have := hadd 0 0
    rw [add_zero] at this
    exact mul_left_cancel (a := g 0) (by rw [← this, mul_one])
  have key : ∀ τ, ∃ Z : Matrix (Fin V.rank) (Fin V.rank) ℂ, Zᴴ * gramAt D V τ + gramAt D V τ * Z = 0 ∧
      ∀ t : ℝ, infMat D.sp.cm.sig V.gram (θ τ) (g t) = NormedSpace.exp (t • Z) := fun τ =>
    exists_gen _ _ ((GlobalTheory.RealWeil.continuous_compAt hθ τ _ _).comp
        ((Units.continuous_val.comp continuous_subtype_val).comp hc))
      (by rw [h0]; exact R.2.2.2.2.1 1 (one_mem _) τ) (fun s t => by rw [hadd, R.2.2.2.1])
      fun t => (GlobalTheory.T.adelicUnitary_action_at_real_place D θ hθ).1 V (g t) τ
  choose Z hZ hg using key
  refine ⟨fun τ => ⟨Z τ, hZ τ⟩, fun t => ?_⟩
  have h1 := GlobalTheory.SmoothForms.isExpFam_expInf R (t • fun τ => ⟨Z τ, hZ τ⟩)
  exact R.2.2.1 _ (hinf t) _ h1.1 fun τ => (hg τ t).trans (h1.2 τ).symm

theorem der_sum {θ : InfFam D} (hθ : IsInfFam θ) {U : HSp D} (𝒮 : Set (GA D U → ℂ)) (hc : ∀ φ ∈ 𝒮, Continuous φ)
    (hd : ∀ φ ∈ 𝒮, ∀ τ, ∀ X ∈ lieAt U τ, ∃ φ' ∈ 𝒮, ∀ g, HasDerivAt (fun t : ℝ => φ (g * oneP θ U τ X t)) (φ' g) 0)
    {φ : GA D U → ℂ} (hφ : φ ∈ 𝒮) (Z : GlobalTheory.SmoothForms.LieN U) (a : D.what₂.Tau → ℂ)
    (ha : ∀ τ, HasDerivAt (fun t : ℝ => φ (oneP θ U τ (Z τ).1 t)) (a τ) 0) :
    HasDerivAt (fun t : ℝ => φ (GlobalTheory.SmoothForms.expInf θ U (t • Z))) (∑ τ, a τ) 0 := by
  have R := (GlobalTheory.T.adelicUnitary_realPoints_structure_realPlaces D).2 θ hθ U
  have h1 := GlobalTheory.Mem.DerClosed.mem_smFun_of_closed D θ hθ U 𝒮 hc hd φ hφ
  have h2 : GlobalTheory.SmoothForms.Sm (GlobalTheory.SmoothForms.expInf θ U) φ :=
    (GlobalTheory.SmoothForms.isSmoothInf_iff φ).1 ((GlobalTheory.SmoothForms.smooth_iff R φ).1 h1)
  have h3 := ((h2 1).differentiable (by simp) 0).hasFDerivAt
  set L := fderiv ℝ (fun X : GlobalTheory.SmoothForms.LieN U => φ (1 * GlobalTheory.SmoothForms.expInf θ U X)) 0
  have key : ∀ v : GlobalTheory.SmoothForms.LieN U, HasDerivAt (fun t : ℝ => φ (GlobalTheory.SmoothForms.expInf θ U (t • v))) (L v) 0 := by
    intro v
    have h4 : HasDerivAt (fun t : ℝ => t • v) v 0 := by
      have h := (hasDerivAt_id (0 : ℝ)).smul_const v
      rwa [one_smul] at h
    have h3' : HasFDerivAt (fun X : GlobalTheory.SmoothForms.LieN U => φ (1 * GlobalTheory.SmoothForms.expInf θ U X)) L ((0 : ℝ) • v) := by
      rw [zero_smul]
      exact h3
    have h5 := HasFDerivAt.comp_hasDerivAt (0 : ℝ) h3' h4
    refine h5.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
    simp only [Function.comp, one_mul]
  have e1 : ∀ τ, a τ = L (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.atPlace U τ (Z τ)) := fun τ =>
    (ha τ).unique ((key (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.atPlace U τ (Z τ))).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun t => congrArg φ (GlobalTheory.SmoothForms.oneP_eq R τ (Z τ) t)))
  have e2 : Z = ∑ τ, (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.atPlace U τ (Z τ) : GlobalTheory.SmoothForms.LieN U) :=
    (GlobalTheory.SmoothForms.sum_atPlace Z).symm
  refine (key Z).congr_deriv ?_
  simp only [e1]
  exact (congrArg L e2).trans
    (map_sum L (fun τ => (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.atPlace U τ (Z τ) : GlobalTheory.SmoothForms.LieN U)) Finset.univ)

theorem exists_conjU (M : HSp D) {J : Matrix (Fin M.rank) (Fin M.rank) D.host.E} {c : D.host.E} (hc : c ≠ 0)
    (h : J = c • M.gram) (k : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.UB J) :
    ∃ g : GA D M, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU M c h g = k ∧
      Formalism.L2.Theta.matHom M g = GeneralLinearGroup.map (cA D) k.1 := by
  have e : ((GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k).map (cA D)).map (cA D) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k :=
    Matrix.ext fun _ _ => Formalism.L2.Theta.cA_cA _
  have hk : (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k)ᵀ * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM J * (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k).map (cA D) =
      GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM J := k.2
  have hu : IsUnit (incA D c) := (IsUnit.mk0 c hc).map _
  have hk2 : (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k)ᵀ * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM M.gram * (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k).map (cA D) =
      GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM M.gram := by
    generalize GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k = m at hk
    rw [h, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM_smul, Matrix.mul_smul, Matrix.smul_mul] at hk
    exact hu.smul_left_cancel.1 hk
  refine ⟨⟨GeneralLinearGroup.map (cA D) k.1, ?_⟩, Subtype.ext (Units.ext e), rfl⟩
  show (((GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k).map (cA D)).map (cA D))ᵀ * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM M.gram *
    (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k).map (cA D) = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM M.gram
  rw [e, hk2]

theorem map_finPart_conj {n : ℕ} (m : Matrix (Fin n) (Fin n) (AE D))
    (hm : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) (m - 1)) (i j : Fin n) :
    finPart D (cA D (m i j)) = finPart D ((1 : Matrix (Fin n) (Fin n) (AE D)) i j) := by
  have h1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) (1 + cA D ((m - 1) i j) - 1) := by
    intro u hu
    have h2 : u • (m - 1) i j = 0 := congrFun (congrFun (hm u hu) i) j
    rw [add_sub_cancel_left]
    have h3 : cA D (u • (m - 1) i j) = u • cA D ((m - 1) i j) :=
      map_smul (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) u _
    rw [← h3, h2, RingHom.map_zero]
  have h4 := GlobalTheory.ConjInfExp.finPart_eq_one _ h1
  have h5 : cA D ((1 : Matrix (Fin n) (Fin n) (AE D)) i j) = (1 : Matrix (Fin n) (Fin n) (AE D)) i j :=
    congrFun (congrFun (Matrix.map_one (cA D) (RingHom.map_zero _) (RingHom.map_one _)) i) j
  rw [RingHom.map_add, RingHom.map_one, add_eq_left, Matrix.sub_apply, RingHom.map_sub, h5, RingHom.map_sub,
    sub_eq_zero] at h4
  exact h4

theorem mem_GinfC_of_conj {M : HSp D} (g : GA D M) (m : Matrix (Fin M.rank) (Fin M.rank) (AE D))
    (hg : Formalism.L2.Theta.mt M g = m.map (cA D))
    (hm : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) (m - 1)) : g ∈ GinfC M := by
  show finHom M g = 1
  refine Units.ext (Matrix.ext fun i j => ?_)
  have h1 : (finHom M g).1 i j = finPart D (Formalism.L2.Theta.mt M g i j) := rfl
  have h2 : (finHom M 1).1 i j = finPart D ((1 : Matrix (Fin M.rank) (Fin M.rank) (AE D)) i j) := rfl
  rw [← map_one (finHom M), h1, h2, hg]
  exact map_finPart_conj _ hm i j

theorem exists_line (M : HSp D) {c : D.host.E} (hc : c ≠ 0) (Xs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E M.rank)
    (hJ : Xs.J = c • M.gram) (γ) (hγ : γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines D.sp.cm.sig Xs) :
    ∃ g : ℝ → GA D M, (∀ t : ℝ, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU M c hJ (g t) = γ (Multiplicative.ofAdd t)) ∧ Continuous g ∧
      (∀ s t, g (s + t) = g s * g t) ∧ ∀ t, g t ∈ GinfC M := by
  choose g h1 h2 using fun t : ℝ => exists_conjU M hc hJ (γ (Multiplicative.ofAdd t))
  refine ⟨g, h1, ?_, fun s t => ?_, fun t => ?_⟩
  · have h3 : Continuous fun t : ℝ => (γ (Multiplicative.ofAdd t)).1 :=
      continuous_subtype_val.comp (hγ.1.comp continuous_ofAdd)
    have h4 : Continuous fun t => Formalism.L2.Theta.matHom M (g t) := by
      simp only [h2]
      refine Units.continuous_iff.2 ⟨?_, ?_⟩
      · exact (Units.continuous_val.comp h3).matrix_map (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.continuous_conj D)
      · exact (Units.continuous_coe_inv.comp h3).matrix_map (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.continuous_conj D)
    exact continuous_induced_rng.2 h4
  · have h3 : Formalism.L2.Theta.matHom M (g (s + t)) = Formalism.L2.Theta.matHom M (g s * g t) := by
      rw [map_mul, h2, h2, h2, ← map_mul, ofAdd_add, map_mul γ]
      rfl
    exact Subtype.ext h3
  · exact mem_GinfC_of_conj _ _ (congrArg Units.val (h2 t)) (hγ.2 _)

theorem der_line {V W : HSp D} {θ : InfFam D} {ψ : AddChar (AF D.host.F) ℂ} {χS χT : (AE D)ˣ →* Circle}
    {ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)} (hθ : IsInfFam θ) (hω : IsWeilDatumO ψ V W χS χT ω)
    (A : Fr V) (B : Fr W) {eS eT : D.what₂.Tau → ℚ} (he : ∀ τ, HasInfExp D χS τ (eS τ) ∧ HasInfExp D χT τ (eT τ))
    {f : WO V W → ℂ} (hf : IsVacF ψ θ A B f) (g : ℝ → GA D V) (hc : Continuous g)
    (hadd : ∀ s t, g (s + t) = g s * g t) (hinf : ∀ t, g t ∈ GinfC V) :
    ∃ Z : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ, (∀ τ, Z τ ∈ lieAt V τ) ∧ ∀ P z,
      HasDerivAt (fun t : ℝ => ω (g t, 1) (ptF ψ θ A B f P) z)
        (ptF ψ θ A B f (∑ τ, (GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockS τ (A.ε τ) (B.ε τ)
          ((A.fr τ * Z τ * (A.fr τ)⁻¹).map (starRingEnd ℂ)) P + (-((eT τ : ℂ) * (Z τ).trace)) • P)) z) 0 := by
  obtain ⟨Z, hZ⟩ := exists_expInf hθ V g hc hadd hinf
  refine ⟨fun τ => (Z τ).1, fun τ => (Z τ).2, fun P z => ?_⟩
  have hs : ∀ Q : D.what₂.Tau → PolF D W.rank V.rank, ptF ψ θ A B f (∑ τ, Q τ) z = ∑ τ, ptF ψ θ A B f (Q τ) z :=
    fun Q => (congrFun (map_sum (pureTensorO ψ θ V W A.cart B.cart A.onb B.onb f) Q Finset.univ) z).trans
      (Finset.sum_apply _ _ _)
  rw [hs]
  simp only [hZ]
  rcases isEmpty_or_nonempty D.what₂.Tau with h0 | ⟨⟨τ₀⟩⟩
  · have e : ∀ t : ℝ, t • Z = Z := fun t => funext fun τ => isEmptyElim τ
    simp only [e, Finset.univ_eq_empty, Finset.sum_empty]
    exact hasDerivAt_const _ _
  let 𝒮 : Set (GA D V → ℂ) := {φ | ∃ f z, IsThetaFunO ψ V W f ∧ φ = fun g => ω (g, 1) f z}
  refine der_sum hθ 𝒮 ?_ ?_ (φ := fun g => ω (g, 1) (ptF ψ θ A B f P) z)
    ⟨_, z, (GlobalTheory.LieScalar.ptF_laws hθ hω.std A B hf).1 τ₀ P, rfl⟩ Z _ fun τ =>
    (GlobalTheory.LieScalar.lieFockAll D V W A B θ ψ χS χT ω f τ (eS τ) (eT τ) hθ hω (he τ).1 (he τ).2 hf).1 _ (Z τ).2 P z
  · rintro _ ⟨f, z, hf, rfl⟩
    exact (hω.om_cont f hf z).comp (continuous_id.prodMk continuous_const)
  · rintro _ ⟨f, z, hf, rfl⟩ τ' Y hY
    obtain ⟨G, hG', h⟩ := GlobalTheory.LieScalar.genS hθ hω τ' Y hY f hf
    refine ⟨_, ⟨G, z, hG', rfl⟩, fun g => ?_⟩
    have := h (g, 1) z
    simpa only [MonoidHom.inl_apply, Prod.mk_mul_mk, mul_one] using this

theorem line_deriv_mem_coinv : GlobalTheory.FunPr.Hypotheses₂ → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
  ∀ (ε : Bool) (M X : HSp D) (A : Fr M) (B : Fr X) (χS χT : (AE D)ˣ →* Circle) (ω : WRep M X) (eS eT : D.what₂.Tau → ℚ),
  IsWeil ψ ε M X χS χT ω → (∀ τ, HasInfExp D χS τ (eS τ) ∧ HasInfExp D χT τ (eT τ)) →
  ∀ (Xs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E M.rank) (hJ : Xs.J = GlobalTheory.RealDict.sgE (D := D) ε • M.gram),
  ∀ (f₀ : WO (sgn ε M) X → ℂ), IsVacF ψ θ (frSgn ε A) B f₀ →
  ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines D.sp.cm.sig Xs, ∃ g : ℝ → GA D M,
    (∀ t : ℝ, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU M (GlobalTheory.RealDict.sgE (D := D) ε) hJ (g t) = γ (Multiplicative.ofAdd t)) ∧
    ∀ P : PolF D X.rank M.rank, ∃ Q ∈ GlobalTheory.RealQuot.coinv ε A B eT, ∀ z,
      HasDerivAt (fun t : ℝ => ω (g t, 1) (ptF (V := sgn ε M) ψ θ (frSgn ε A) B f₀ P) z) (ptF ψ θ (frSgn ε A) B f₀ Q z) 0 := by
  intro _ D ψ θ _ hθ ε M X A B χS χT ω eS eT hω he Xs hJ f₀ hf γ hγ
  have hc : GlobalTheory.RealDict.sgE (D := D) ε ≠ 0 := by cases ε <;> simp [GlobalTheory.RealDict.sgE]
  obtain ⟨g, h1, h2, h3, h4⟩ := exists_line M hc Xs hJ γ hγ
  refine ⟨g, h1, fun P => ?_⟩
  obtain ⟨Z, hZ, hd⟩ := der_line (V := sgn ε M) (ω := ω.toSgn ε) hθ hω (frSgn ε A) B he hf
    (fun t => (ofSgn ε M).symm (g t)) ((continuous_ofSgn_symm ε M).comp h2)
    (fun s t => by rw [h3, map_mul]) h4
  refine ⟨_, ?_, hd P⟩
  refine Submodule.sum_mem _ fun τ _ => Submodule.subset_span ⟨τ, Z τ, ?_, P, ?_⟩
  · rw [← GlobalTheory.SgnIdent.lieAt_sgn ε M τ]
    exact hZ τ
  · rw [neg_smul, ← sub_eq_add_neg]
    rfl

end GlobalTheory.OmegaDer

end
