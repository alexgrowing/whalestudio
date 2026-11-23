import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisAtMinusRho
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocUnifSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RatStab
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RatFixLeRatStab
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigBLocalEigenTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigBLeviTorusEvaluationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemAutSub
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaBasicPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlaneAutomorphicFunctionTwist
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittFrameHypPlanesTorus
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianAdaptedPlaneRestriction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLeviElementAdaptedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftLeftInvariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviEmbeddingExistsDoublingConfiguration
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondConfigurationUnramifiedIdentity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open GlobalTheory.ConeSmallUnf

noncomputable section

open scoped ENNReal Pointwise

namespace UpperTheory.Dv.Fold

private theorem fund_union {G ι : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G] [Countable ι] (μ : Measure G)
    [μ.IsMulLeftInvariant] {P Q : Subgroup G} (hQP : Q ≤ P) (m : ι → G) (hm : ∀ i, m i ∈ P)
    (hcov : ∀ p ∈ P, ∃ i, m i * p ∈ Q) (huniq : ∀ i j, m i * (m j)⁻¹ ∈ Q → i = j) {D : Set G}
    (hD : IsFundamentalDomain P D μ) :
    IsFundamentalDomain Q (⋃ i, (fun g => (m i)⁻¹ * g) ⁻¹' D) μ ∧
      ∀ f : G → ℝ≥0∞, ∑' i, ∫⁻ g in D, f (m i * g) ∂μ = ∫⁻ g in ⋃ i, (fun g => (m i)⁻¹ * g) ⁻¹' D, f g ∂μ := by
  let T : G → Set G := fun h => (fun g => h⁻¹ * g) ⁻¹' D
  have hsmul : ∀ δ : P, δ • D = T δ.1 := fun δ => by
    ext g; rw [Set.mem_smul_set_iff_inv_smul_mem]; rfl
  have hdisj : ∀ δ δ' : G, δ ∈ P → δ' ∈ P → δ ≠ δ' → AEDisjoint μ (T δ) (T δ') := by
    intro δ δ' hδ hδ' hne
    have := hD.aedisjoint (show (⟨δ, hδ⟩ : P) ≠ ⟨δ', hδ'⟩ from fun h => hne (congrArg Subtype.val h))
    rwa [Function.onFun, hsmul, hsmul] at this
  have hnm : ∀ h, NullMeasurableSet (T h) μ := fun h =>
    hD.nullMeasurableSet.preimage (measurePreserving_mul_left μ h⁻¹).quasiMeasurePreserving
  have hq : ∀ q : Q, q • (⋃ x, T (m x)) = ⋃ x, T (q.1 * m x) := by
    intro q
    rw [Set.smul_set_iUnion]
    refine Set.iUnion_congr fun x => ?_
    ext g
    rw [Set.mem_smul_set_iff_inv_smul_mem]
    show (m x)⁻¹ * (q.1⁻¹ * g) ∈ D ↔ (q.1 * m x)⁻¹ * g ∈ D
    rw [mul_inv_rev, mul_assoc]
  refine ⟨{ nullMeasurableSet := NullMeasurableSet.iUnion fun x => hnm (m x), ae_covers := ?_, aedisjoint := ?_ }, ?_⟩
  · filter_upwards [hD.ae_covers] with g ⟨δ, hδg⟩
    obtain ⟨i, hi⟩ := hcov δ.1 δ.2
    refine ⟨⟨m i * δ.1, hi⟩, Set.mem_iUnion.2 ⟨i, ?_⟩⟩
    show (m i)⁻¹ * (m i * δ.1 * g) ∈ D
    rw [mul_assoc, inv_mul_cancel_left]
    exact hδg
  · intro q q' hqq'
    rw [Function.onFun, hq, hq, AEDisjoint.iUnion_left_iff]
    intro x
    rw [AEDisjoint.iUnion_right_iff]
    intro y
    apply hdisj _ _ (mul_mem (hQP q.2) (hm x)) (mul_mem (hQP q'.2) (hm y))
    intro heq
    have hxy : x = y := by
      apply huniq
      have e : m x * (m y)⁻¹ = q.1⁻¹ * q'.1 := by
        rw [mul_inv_eq_iff_eq_mul, mul_assoc, ← heq, inv_mul_cancel_left]
      rw [e]
      exact Q.mul_mem (Q.inv_mem q.2) q'.2
    subst hxy
    exact hqq' (Subtype.ext (mul_right_cancel heq))
  · intro f
    have hpw : Pairwise (Function.onFun (AEDisjoint μ) fun i => T (m i)) := fun i j hij =>
      hdisj _ _ (hm i) (hm j) fun heq => hij (huniq i j (by rw [heq, mul_inv_cancel]; exact Q.one_mem))
    rw [lintegral_iUnion₀ (fun i => hnm (m i)) hpw]
    refine tsum_congr fun i => ?_
    have := (measurePreserving_mul_left μ (m i)⁻¹).setLIntegral_comp_preimage_emb
      (measurableEmbedding_mulLeft (m i)⁻¹) (fun g => f (m i * g)) D
    simpa only [mul_inv_cancel_left] using this.symm

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

open GlobalTheory.StabCosetDomain GlobalTheory.ThKCtFin.LeftInvLevi

private abbrev prin (F : Type) [Field F] [NumberField F] [Algebra F E] (ξ : Eˣ) : (AE F E)ˣ :=
  Units.map (inclR (F := F) (AF F)).toMonoidHom ξ

private theorem exists_torus {B : Base F E} (hB : B.IsGood σ) {n n₁ r s i₀ i₁ : ℕ} {Y : Spc F E n} {Y₁ : Spc F E n₁}
    {H₀ : Plane E n n₁} (hH : Y.IsHerm σ B r s) (hA : H₀.IsAdapted σ B Y Y₁ i₀ i₁) (t : (AE F E)ˣ) :
    ∃ m₀ : UA σ Y.J, IsLevi (W₁ := Y₁) H₀ t 1 m₀ := by
  have hσ := GlobalTheory.LeviTorusH.sigma_invol hB.cm
  have hc : ∀ a : AE F E, (cA σ).toRingHom ((cA σ).toRingHom a) = a := GlobalTheory.LeviTorusH.cA_invol hσ
  have hJ : ∀ i j, (cA σ).toRingHom (incM F Y.J j i) = incM F Y.J i j := by
    intro i j
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, incM, Matrix.map_apply, GlobalTheory.LeviTorusH.cA_incl]
    exact congrArg _ (hH.herm i j)
  have hXX : incV F H₀.x ⬝ᵥ incM F Y.J *ᵥ (fun i => (cA σ).toRingHom (incV F H₀.x i)) = 0 := by
    rw [show (fun i => (cA σ).toRingHom (incV F H₀.x i)) = fun i => cA σ (incV F H₀.x i) from rfl,
      GlobalTheory.LeviTorusH.form_incl]
    exact (congrArg _ hA.xx).trans (map_zero _)
  have hYY : incV F H₀.y ⬝ᵥ incM F Y.J *ᵥ (fun i => (cA σ).toRingHom (incV F H₀.y i)) = 0 := by
    rw [show (fun i => (cA σ).toRingHom (incV F H₀.y i)) = fun i => cA σ (incV F H₀.y i) from rfl,
      GlobalTheory.LeviTorusH.form_incl]
    exact (congrArg _ hA.yy).trans (map_zero _)
  have hXY : incV F H₀.x ⬝ᵥ incM F Y.J *ᵥ (fun i => (cA σ).toRingHom (incV F H₀.y i)) = 1 := by
    rw [show (fun i => (cA σ).toRingHom (incV F H₀.y i)) = fun i => cA σ (incV F H₀.y i) from rfl,
      GlobalTheory.LeviTorusH.form_incl]
    exact (congrArg _ hA.xy).trans (map_one _)
  have h01 := GlobalTheory.LeviTorusH.torus_mul_inv hc hJ hXY t hXX hYY
  have h10 : GlobalTheory.LeviTorusH.torusMat (cA σ).toRingHom (incM F Y.J) (incV F H₀.x) (incV F H₀.y) t⁻¹ *
      GlobalTheory.LeviTorusH.torusMat (cA σ).toRingHom (incM F Y.J) (incV F H₀.x) (incV F H₀.y) t = 1 :=
    by simpa only [inv_inv] using GlobalTheory.LeviTorusH.torus_mul_inv hc hJ hXY t⁻¹ hXX hYY
  refine ⟨⟨⟨GlobalTheory.LeviTorusH.torusMat (cA σ).toRingHom (incM F Y.J) (incV F H₀.x) (incV F H₀.y) t, _, h01, h10⟩, ?_⟩, ?_, ?_, ?_⟩
  · exact GlobalTheory.LeviTorusH.torus_unitary hc hJ hXY t hXX hYY
  · exact GlobalTheory.LeviTorusH.torus_mulVec_x hXY t hXX
  · exact GlobalTheory.LeviTorusH.torus_mulVec_y hc hJ hXY t hYY
  · have hu : (incM F Y.J *ᵥ fun i => (cA σ).toRingHom (incV F H₀.y i)) ᵥ* incM F H₀.ι = 0 := by
      rw [show (fun i => (cA σ).toRingHom (incV F H₀.y i)) = fun i => cA σ (incV F H₀.y i) from rfl,
        GlobalTheory.LeviTorusH.vecMul_incM]
      funext j
      exact (congrArg _ (hA.orth (Pi.single j 1)).2).trans (map_zero _)
    have hw : (incM F Y.J *ᵥ fun i => (cA σ).toRingHom (incV F H₀.x i)) ᵥ* incM F H₀.ι = 0 := by
      rw [show (fun i => (cA σ).toRingHom (incV F H₀.x i)) = fun i => cA σ (incV F H₀.x i) from rfl,
        GlobalTheory.LeviTorusH.vecMul_incM]
      funext j
      exact (congrArg _ (hA.orth (Pi.single j 1)).1).trans (map_zero _)
    show GlobalTheory.LeviTorusH.torusMat (cA σ).toRingHom (incM F Y.J) (incV F H₀.x) (incV F H₀.y) t * incM F H₀.ι =
      incM F H₀.ι * 1
    rw [Matrix.mul_one]
    exact GlobalTheory.LeviTorusH.torus_mul_of t _ hu hw

private theorem inv_line {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {k : UA σ J} {a : (AE F E)ˣ} {x : Fin n → AE F E}
    (hx : mat k *ᵥ x = a.1 • x) : mat k⁻¹ *ᵥ x = (a⁻¹).1 • x := by
  calc mat k⁻¹ *ᵥ x = ((a⁻¹).1 * a.1) • (mat k⁻¹ *ᵥ x) := by rw [Units.inv_mul, one_smul]
    _ = (a⁻¹).1 • (mat k⁻¹ *ᵥ (a.1 • x)) := by rw [mul_smul, Matrix.mulVec_smul]
    _ = (a⁻¹).1 • x := by rw [← hx, Matrix.mulVec_mulVec, mat_inv_mul, Matrix.one_mulVec]

private theorem incM_mul {m k l : ℕ} (A : Matrix (Fin m) (Fin k) E) (C : Matrix (Fin k) (Fin l) E) :
    incM F (A * C) = incM F A * incM F C := Matrix.map_mul (f := (inclR (F := F) (AF F) : E →+* AE F E))

private theorem det_skew {B : Base F E} {d r s : ℕ} {W : Spc F E d} (hW : W.IsSkew σ B r s) : W.J.det ≠ 0 := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have h := GlobalTheory.LeviElem.det_ne_of_sig _ (hW.sig w)
  rw [Matrix.det_smul] at h
  have h' := right_ne_zero_of_mul h
  intro h0
  apply h'
  have := RingHom.map_det (B.emb w).1 W.J
  rw [h0, map_zero] at this
  exact this.symm

private theorem mem_ratU_of_mat {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {h : UA σ J} {A : Matrix (Fin n) (Fin n) E}
    (hA : mat h = incM F A) : h ∈ ratU σ J := by
  have hd : A.det ≠ 0 := by
    intro h0
    have h1 : (mat h).det = 0 := by
      rw [hA, show incM F A = (inclR (F := F) (AF F)).mapMatrix A from rfl, ← RingHom.map_det, h0, map_zero]
    have h2 := congrArg Matrix.det (mat_inv_mul h)
    rw [Matrix.det_mul, h1, mul_zero, Matrix.det_one] at h2
    have h3 : inclR (F := F) (AF F) (0 : E) = inclR (F := F) (AF F) (1 : E) := by rw [map_zero, map_one, h2]
    exact zero_ne_one (inclR_inj h3)
  exact Subgroup.mem_subgroupOf.2 ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero A hd, Units.ext hA.symm⟩

private theorem fix_decomp (hσ : ∀ x, σ (σ x) = x) {n n₁ : ℕ} {H : Plane E n n₁} {Y : Spc F E n} {Y₁ : Spc F E n₁}
    (hI : GlobalTheory.ThK.GLTwo.IsHypPlane σ H Y Y₁) (hsk : ∀ i j, σ (Y.J j i) = -Y.J i j) (hd : Y₁.J.det ≠ 0) (p : UA σ Y.J)
    (hpr : p ∈ ratU σ Y.J) (hp : mat p *ᵥ incV F H.x = incV F H.x) :
    ∃ h₁ ∈ ratU σ Y₁.J, ∃ m, IsLevi (W₁ := Y₁) H 1 h₁ m ∧ ∃ u ∈ unip σ Y H, p = u * m := by
  obtain ⟨h₁, hu⟩ := GlobalTheory.FlagRadDec.exists_proj hσ hI hsk hd p hp
  obtain ⟨M, -, hM, -⟩ := hI.exists_leviHom hσ hsk hd
  let π : Matrix (Fin n₁) (Fin n) E := (Y₁.J⁻¹)ᵀ * (Y.J * H.ι.map σ)ᵀ
  have hπι : π * H.ι = 1 := by
    calc π * H.ι = (Y₁.J⁻¹)ᵀ * (H.ιᵀ * Y.J * H.ι.map σ)ᵀ := by
          simp only [π, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
      _ = 1 := by
          rw [hI.2.2.2.2.2, ← Matrix.transpose_mul, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hd), Matrix.transpose_one]
  have hπx : π *ᵥ H.x = 0 := by
    simp only [π]
    rw [← Matrix.mulVec_mulVec, Matrix.mulVec_transpose (Y.J * _), GlobalTheory.FlagRadDec.x_vecMul hσ hI hsk, Matrix.mulVec_zero]
  clear_value π
  obtain ⟨g, hg, -⟩ := rat_desc p hpr
  have hmat : mat h₁ = incM F (π * g * H.ι) := by
    refine matrix_ext_mulVec fun z => ?_
    obtain ⟨a, ha⟩ := hu z
    have h0 : incM F π *ᵥ incV F H.x = 0 := by
      rw [← incV_mulVec, hπx]; funext i; simp [incV]
    have h1 : incM F π * incM F H.ι = 1 := by
      rw [← incM_mul, hπι]; exact Matrix.map_one _ (map_zero _) (map_one _)
    have := congrArg (incM F π *ᵥ ·) ha
    simp only [Matrix.mulVec_add, Matrix.mulVec_smul, h0, smul_zero, add_zero, Matrix.mulVec_mulVec] at this
    rw [← Matrix.mul_assoc (incM F π) (incM F H.ι), h1, Matrix.one_mul] at this
    rw [← this, incM_mul, incM_mul, hg, Matrix.mul_assoc]
    rfl
  refine ⟨h₁, mem_ratU_of_mat hmat, M h₁, hM h₁, p * M h₁⁻¹, Subgroup.subset_closure ?_, by rw [map_inv]; group⟩
  obtain ⟨mx, -, mι⟩ := hM h₁⁻¹
  simp only [Units.val_one, one_smul] at mx
  refine ⟨by rw [mat_mul, ← Matrix.mulVec_mulVec, mx, hp], fun z => ?_⟩
  obtain ⟨a, ha⟩ := hu (mat h₁⁻¹ *ᵥ z)
  refine ⟨a, ?_⟩
  have e : mat h₁ *ᵥ (mat h₁⁻¹ *ᵥ z) = z := by
    rw [Matrix.mulVec_mulVec, ← mat_mul, mul_inv_cancel]; simp [mat]
  rw [mat_mul, ← Matrix.mulVec_mulVec, Matrix.mulVec_mulVec z, mι, ← Matrix.mulVec_mulVec, ha, e]

private theorem norm_thetaSum_smul {κ : Type} (χ : Chr F E) (z : ℝ) (ξ : Eˣ) (Φ : (κ → AF F) → ℂ) :
    ‖thetaSum F (((χ (prin F ξ) : ℂ) * (((absE F E (prin F ξ) : ℝ) ^ z : ℝ) : ℂ)) • Φ)‖ = ‖thetaSum F Φ‖ := by
  rw [GlobalTheory.Doubling.absE_inclR]
  simp only [thetaSum, Pi.smul_apply, smul_eq_mul, tsum_mul_left]
  rw [norm_mul, norm_mul, Circle.norm_coe]
  simp

section Law

variable {B : Base F E} {a b : ℕ} {G : Geo σ a (b + 2)} {G₁ : Geo σ a b} {H : Plane E (b + 2) b}
  {H' : Plane E (a + (b + 2)) (a + b)} {e' : Fn F (b + 2) (a + (b + 2)) →ₗ[ℂ] Fn F b (a + b)} {X : Chars F E}
  {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W} {om₁ : Rep σ G₁.V G₁.W} {om₁' : Rep σ G₁.V' G₁.W}

private theorem norm_right (hK : KP) (hC : CfgB B G G₁ H H') (he : IsEv B G.M' G₁.M' H.ι H'.ι (isoB H H') e')
    (hT : IsTriple B G X om om') (hT₁ : IsTriple B G₁ X om₁ om₁') {q : UA σ G.W.J} (hq : q ∈ ratU σ G.W.J) (η : Eˣ)
    (hqx : mat q *ᵥ incV F H'.x = (prin F η).1 • incV F H'.x) {Ψ : Fn F (b + 2) (a + (b + 2))} (hΨ : Ψ ∈ schA F _) :
    ‖thetaSum F (e' (om' (1, q) Ψ))‖ = ‖thetaSum F (e' Ψ)‖ := by
  have hσ := GlobalTheory.LeviTorusH.sigma_invol hT.base.cm
  obtain ⟨m₀, hm₀⟩ := GlobalTheory.T.exists_levi_element_adapted F E σ B a (b + 2) G X om om' hT (a + b) G₁.W H' _ _ hC.hH' (prin F η)
  have hm₀r : m₀ ∈ ratU σ G.W.J := levi_mem_ratU (planeMap_bij hC.hH' hT.geo.hW.lat) η hm₀
  have hp : mat (q * m₀⁻¹) *ᵥ incV F H'.x = incV F H'.x := by
    rw [mat_mul, ← Matrix.mulVec_mulVec, inv_line hm₀.1, Matrix.mulVec_smul, hqx, smul_smul, Units.inv_mul, one_smul]
  obtain ⟨h₁, hh₁, m, hm, u, hu, hdec⟩ := fix_decomp hσ (GlobalTheory.ThK.GLTwo.IsAdapted.isHypPlane hC.hH') hT.geo.hW.skew
    (det_skew hT₁.geo.hW) (q * m₀⁻¹) (mul_mem hq (inv_mem hm₀r)) hp
  have hΨ₀ : om' (1, m₀) Ψ ∈ schA F _ := hT.weil'.isUSplitting.pres _ _ hΨ
  have e1 : om' (1, q) Ψ = om' (1, u * m) (om' (1, m₀) Ψ) := by
    rw [← Module.End.mul_apply, ← map_mul om', Prod.mk_mul_mk, one_mul, ← hdec, inv_mul_cancel_right]
  have e2 := GlobalTheory.T.config_b_levi_torus_evaluation hK.base F E σ B a b G G₁ H H' hC e' he X om om' om₁ om₁' hT hT₁ 1 h₁ m hm u hu _ hΨ₀
  have e3 := GlobalTheory.T.config_b_levi_torus_evaluation hK.base F E σ B a b G G₁ H H' hC e' he X om om' om₁ om₁' hT hT₁ _ 1 m₀ hm₀ 1 (one_mem _) _ hΨ
  rw [one_mul, Prod.mk_one_one, map_one om₁', Module.End.one_apply] at e3
  simp only [one_mul, map_one, Circle.coe_one, NNReal.coe_one, Real.one_rpow, Complex.ofReal_one, one_smul] at e2
  have e4 := ((GlobalTheory.T.theta_basic_properties hK.base F E σ B _ _ _ _ G₁.M' _ _ om₁' _ _ _ _ (GlobalTheory.ThK.Inhab.pairV' hT₁)).1 _
    (he.maps _ hΨ₀)).2.1 1 (one_mem _) h₁ hh₁ 1 1
  simp only [theta, mul_one] at e4
  rw [Prod.mk_one_one, map_one om₁', Module.End.one_apply] at e4
  rw [e1, e2, e4, e3, norm_thetaSum_smul]

private theorem norm_termW (hK : KP) (hC : CfgB B G G₁ H H') (he : IsEv B G.M' G₁.M' H.ι H'.ι (isoB H H') e')
    (hT : IsTriple B G X om om') (hT₁ : IsTriple B G₁ X om₁ om₁') {γ : IsoV σ G.W.J → UA σ G.W.J}
    (hγ : IsWitt (σ := σ) (J := G.W.J) H'.x γ) {Φ : Fn F (b + 2) (a + (b + 2))} (hΦ : Φ ∈ schA F _) (ξ : Eˣ)
    {m : UA σ G.V'.J} (hm : IsLevi (W₁ := G₁.V') H (prin F ξ) 1 m) (w w' : IsoV σ G.W.J) (hw : w'.1 = σ ξ • w.1)
    (g : UA σ G.V'.J) (h : UA σ G.W.J) :
    ‖termW B G.M' H H' e' om' Φ γ w (m * g) h‖ = ‖termW B G.M' H H' e' om' Φ γ w' g h‖ := by
  have hS := hT.weil'.isUSplitting
  have hΨ : om' (g, γ w * h) Φ ∈ schA F _ := hS.pres _ _ hΦ
  set Ψ := om' (g, γ w * h) Φ with hΨd
  set s := shiftB σ H H' (prin F ξ) with hs
  have hρ : G.M'.co.rho B.ψ s Ψ ∈ schA F _ := GlobalTheory.HeisSchA.rho_mem_schA G.M' B.ψ hT.base.std s Ψ hΨ
  set η : Eˣ := Units.map σ.toMonoidHom ξ⁻¹ with hη
  have hηξ : cA σ (prin F ξ).1 * (prin F η).1 = 1 := by
    show cA σ (inclR (F := F) (AF F) ξ) * inclR (F := F) (AF F) (σ (ξ⁻¹ : Eˣ)) = 1
    rw [GlobalTheory.StabCosetDomain.cA_inclR, ← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
  have hqx : mat (γ w' * (γ w)⁻¹) *ᵥ incV F H'.x = (prin F η).1 • incV F H'.x := by
    have h1 : mat (γ w)⁻¹ *ᵥ incV F H'.x = incV F w.1 := by
      rw [← (hγ w).2, Matrix.mulVec_mulVec, mat_inv_mul, Matrix.one_mulVec]
    have h2 : w.1 = (η : E) • w'.1 := by
      rw [hw, smul_smul]
      show _ = (σ (ξ⁻¹ : Eˣ) * σ ξ) • _
      rw [← map_mul, Units.inv_mul, map_one, one_smul]
    rw [mat_mul, ← Matrix.mulVec_mulVec, h1, h2, incV_smul, Matrix.mulVec_smul, (hγ w').2]
    rfl
  have a1 : actAB (cA σ) ((m, 1) : UA σ G.V'.J × UA σ G.W.J) s = shiftB σ H H' 1 := by
    change mat m * s * (mat (1 : UA σ G.W.J))ᵀ = _
    rw [show mat (1 : UA σ G.W.J) = 1 from rfl, Matrix.transpose_one, Matrix.mul_one, hs, shiftB, shiftB, Matrix.mul_smul,
      Matrix.mul_vecMulVec, hm.2.1, Matrix.smul_vecMulVec, smul_smul, ← map_mul, Units.mul_inv, Units.val_one]
  have a2 : actAB (cA σ) ((1, γ w' * (γ w)⁻¹) : UA σ G.V'.J × UA σ G.W.J) s = shiftB σ H H' 1 := by
    change mat (1 : UA σ G.V'.J) * s * (mat (γ w' * (γ w)⁻¹))ᵀ = _
    rw [show mat (1 : UA σ G.V'.J) = 1 from rfl, Matrix.one_mul, hs, shiftB, shiftB, Matrix.smul_mul,
      Matrix.vecMulVec_mul, Matrix.vecMul_transpose, hqx, Matrix.vecMulVec_smul, smul_smul, hηξ, Units.val_one, map_one]
  have b1 := hS.impl (m, 1) s Ψ hΨ
  have b2 := hS.impl (1, γ w' * (γ w)⁻¹) s Ψ hΨ
  rw [a1] at b1
  rw [a2] at b2
  have c1 : om' (m * g, γ w * h) Φ = om' (m, 1) Ψ := by
    rw [hΨd, ← Module.End.mul_apply, ← map_mul om', Prod.mk_mul_mk, one_mul]
  have c2 : om' (g, γ w' * h) Φ = om' (1, γ w' * (γ w)⁻¹) Ψ := by
    rw [hΨd, ← Module.End.mul_apply, ← map_mul om', Prod.mk_mul_mk, one_mul, mul_assoc, inv_mul_cancel_left]
  have d1 := (GlobalTheory.ThK.EvLawBLeft.globalLaw hK.base F E σ B a b G G₁ H H' hC e' he X om om' om₁ om₁' hT hT₁).2 _ 1 m hm _ hρ
  rw [Prod.mk_one_one, map_one om₁', Module.End.one_apply, GlobalTheory.ThK.LemF.fac] at d1
  rw [termW, termW, c1, c2, ← b1, ← b2, d1, norm_thetaSum_smul,
    norm_right hK hC he hT hT₁ (mul_mem (hγ w').1 (inv_mem (hγ w).1)) η hqx hρ]

end Law

private theorem rat_scalar {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {x : Fin n → E} (hx : x ≠ 0) {p : UA σ J}
    (hp : p ∈ ratStab σ J x) : ∃ ξ : Eˣ, mat p *ᵥ incV F x = (prin F ξ).1 • incV F x := by
  obtain ⟨hr, l, hl⟩ := hp
  obtain ⟨g, hg, -⟩ := rat_desc p hr
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hx
  have hi : x i ≠ 0 := hi
  have h1 : inclR (F := F) (AF F) ((g *ᵥ x) i) = l.1 * inclR (F := F) (AF F) (x i) := by
    have := congrFun hl i
    rw [hg] at this
    exact (congrFun (incV_mulVec (F := F) g x) i).trans this
  have h2 : l.1 = inclR (F := F) (AF F) ((g *ᵥ x) i * (x i)⁻¹) := by
    rw [map_mul, h1, mul_assoc, ← map_mul, mul_inv_cancel₀ hi, map_one, mul_one]
  have h3 : (g *ᵥ x) i * (x i)⁻¹ ≠ 0 := by
    intro h0
    rw [h0, map_zero] at h2
    have h4 : inclR (F := F) (AF F) (0 : E) = inclR (F := F) (AF F) (1 : E) := by
      rw [map_zero, map_one, ← l.mul_inv, h2, zero_mul]
    exact zero_ne_one (inclR_inj h4)
  exact ⟨Units.mk0 _ h3, by rw [hl, h2]; rfl⟩

private theorem exists_reps {n : ℕ} (J : Matrix (Fin n) (Fin n) E) :
    ∃ R : Set (IsoV σ J), GlobalTheory.ConeSmallClaim.NonProp R ∧ ∀ w : IsoV σ J, ∃ r ∈ R, ∃ ξ : Eˣ, w.1 = (ξ : E) • r.1 := by
  let S : Setoid (IsoV σ J) := ⟨fun w w' => ∃ ξ : Eˣ, w.1 = (ξ : E) • w'.1, fun w => ⟨1, by simp⟩,
    fun ⟨ξ, h⟩ => ⟨ξ⁻¹, by rw [h, smul_smul, Units.inv_mul, one_smul]⟩,
    fun ⟨ξ, h⟩ ⟨η, h'⟩ => ⟨ξ * η, by rw [h, h', smul_smul, Units.val_mul]⟩⟩
  refine ⟨Set.range (Quotient.out (s := S)), ?_, fun w => ⟨_, ⟨Quotient.mk S w, rfl⟩, S.symm (Quotient.mk_out w)⟩⟩
  rintro _ ⟨c, rfl⟩ _ ⟨c', rfl⟩ ξ h
  have : c = c' := by
    rw [← Quotient.out_eq c, ← Quotient.out_eq c']
    exact Quotient.sound ⟨ξ, h⟩
  rw [this]

private def scaleIso {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (ξ : Eˣ) (w : IsoV σ J) : IsoV σ J :=
  ⟨σ ξ • w.1, smul_ne_zero ((map_ne_zero σ).2 ξ.ne_zero) w.2.1, by
    have h := w.2.2
    have e : (fun i => σ ((σ ξ • w.1) i)) = σ (σ ξ) • fun i => σ (w.1 i) := by
      funext i; simp
    rw [form] at h
    rw [form, e, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, h, smul_zero, smul_zero]⟩

end UpperTheory.Dv.Fold

open UpperTheory.Dv.Fold GlobalTheory.StabCosetDomain GlobalTheory.ThKCtFin.LeftInvLevi in
theorem _root_.GlobalTheory.T.seesaw_evaluation_haar_volume : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a b : ℕ)
    (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
    ∀ e', IsEv B G.M' G₁.M' H.ι H'.ι (isoB H H') e' → ∀ (K : Subgroup (UA σ G.V'.J)) (μK : Measure K) (μ : Measure (AE F E)ˣ),
    IsStab B K → μK.IsHaarMeasure → μ.IsHaarMeasure → ∀ γ, IsWitt (σ := σ) (J := G.W.J) H'.x γ →
    ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' → ∀ Φ' ∈ PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁,
    ∀ hf : UA σ G.V'.J → ℝ, GlobalTheory.ConeSmall.IsIwaHt K H.x hf → (∀ g, ∃ (p k : UA σ G.V'.J) (l : (AE F E)ˣ), k ∈ K ∧ mat p *ᵥ incV F H.x = l.1 • incV F H.x ∧ g = p * k) →
    ∀ 𝓓 : Set (UA σ G.V'.J), IsFundamentalDomain (ratStab σ G.V'.J H.x) 𝓓 G.M'.μ →
    ∃ (𝓓₁ : Set (UA σ G.V'.J)) (R : Set (IsoV σ G.W.J)), IsFundamentalDomain (GlobalTheory.ConeSmallClaim.ratFix σ G.V'.J H.x) 𝓓₁ G.M'.μ ∧
      GlobalTheory.ConeSmallClaim.NonProp R ∧ ∀ (r : ℝ) (h : UA σ G.W.J),
        ∑' w, ∫⁻ g in 𝓓, ENNReal.ofReal (‖termW B G.M' H H' e' om' Φ' γ w g h‖ * hf g ^ r) ∂G.M'.μ ≤
          ∑' w : R, ∫⁻ g in 𝓓₁, ENNReal.ofReal (‖termW B G.M' H H' e' om' Φ' γ w.1 g h‖ * hf g ^ r) ∂G.M'.μ := by
  intro hK F E _ _ _ _ _ σ B a b G G₁ H H' hC e' he K μK μ _ _ _ γ hγ X om om' om₁ om₁' hT hT₁ Φ' hΦ hf hhf hIw 𝓓 h𝓓
  have hσ := GlobalTheory.LeviTorusH.sigma_invol hT.base.cm
  haveI : Countable E := (Module.finBasis ℚ E).equivFun.injective.countable
  haveI : Countable Eˣ := Units.val_injective.countable
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI : BorelSpace (UA σ G.V'.J) := ⟨rfl⟩
  haveI := hT.geo.hM'.haar
  have hΦS : Φ' ∈ schA F _ := GlobalTheory.ThKRatInv.polData_le_schA B G.M' hT.geo.hM' (Submodule.mem_inf.1 hΦ).1
  have hx0 : H.x ≠ 0 := by
    intro h
    have := hC.hH.xy
    rw [h] at this
    simp [form] at this
  choose m hm using fun ξ : Eˣ => exists_torus hT.base hT.geo.hV' hC.hH (prin F ξ)
  have hmr : ∀ ξ, m ξ ∈ ratU σ G.V'.J := fun ξ => levi_mem_ratU (planeMap_bij hC.hH hT.geo.hV'.lat) ξ (hm ξ)
  obtain ⟨hfd, hint⟩ := fund_union G.M'.μ (GlobalTheory.ConeSmallClaim.ratFix_le_ratStab G.V'.J H.x) m
    (fun ξ => ⟨hmr ξ, _, (hm ξ).1⟩) (fun p hp => by
      obtain ⟨ξ, hξ⟩ := rat_scalar hx0 hp
      refine ⟨ξ⁻¹, mul_mem (hmr _) hp.1, ?_⟩
      rw [mat_mul, ← Matrix.mulVec_mulVec, hξ, Matrix.mulVec_smul, (hm _).1, smul_smul, ← Units.val_mul, ← map_mul,
        mul_inv_cancel, map_one, Units.val_one, one_smul])
    (fun ξ η h => by
      have h2 := h.2
      rw [mat_mul, ← Matrix.mulVec_mulVec, inv_line (hm η).1, Matrix.mulVec_smul, (hm ξ).1, smul_smul, ← Units.val_mul,
        ← map_inv, ← map_mul] at h2
      have h3 : ((η⁻¹ * ξ : Eˣ) : E) • H.x = H.x := incV_inj (F := F) (by rw [incV_smul]; exact h2)
      have h4 : ((η⁻¹ * ξ : Eˣ) : E) = 1 := smul_left_injective E hx0 (h3.trans (one_smul E H.x).symm)
      exact (inv_mul_eq_one.1 (Units.ext h4)).symm) h𝓓
  obtain ⟨R, hR, hcov⟩ := exists_reps (σ := σ) G.W.J
  refine ⟨_, R, hfd, hR, fun r h => ?_⟩
  have hht : ∀ ξ g, hf (m ξ * g) = hf g := fun ξ g => by
    obtain ⟨p, k, l, hk, hp, rfl⟩ := hIw g
    rw [← mul_assoc, hhf p k l hk hp, hhf (m ξ * p) k (l * prin F ξ) hk (by
      rw [mat_mul, ← Matrix.mulVec_mulVec, hp, Matrix.mulVec_smul, (hm ξ).1, smul_smul, Units.val_mul]),
      map_mul, GlobalTheory.Doubling.absE_inclR, mul_one]
  have hsurj : Function.Surjective fun p : R × Eˣ => scaleIso p.2 p.1.1 := fun w => by
    obtain ⟨r, hr, ξ, hξ⟩ := hcov w
    refine ⟨(⟨r, hr⟩, Units.map σ.toMonoidHom ξ), Subtype.ext ?_⟩
    show σ (σ ξ) • r.1 = w.1
    rw [hσ, hξ]
  refine (ENNReal.tsum_le_tsum_comp_of_surjective hsurj _).trans (le_of_eq ?_)
  rw [ENNReal.tsum_prod']
  refine tsum_congr fun w => ?_
  rw [← hint]
  refine tsum_congr fun ξ => lintegral_congr fun g => ?_
  rw [hht, norm_termW hK hC he hT hT₁ hγ hΦS ξ (hm ξ) w.1 (scaleIso ξ w.1) rfl]

end
