import Mathlib
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentTransvectionUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeesawPairPlaneDescentFirstStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvalMapPairCompat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormSmulLeft
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAdelicCharExistsNeOneStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

section
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

private theorem form_swap_herm {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (hσ : ∀ x, σ (σ x) = x)
    (hJ : ∀ i j, σ (J j i) = J i j) (a b : Fin n → E) : form σ J a b = σ (form σ J b a) := by
  unfold form
  simp only [dotProduct, Matrix.mulVec, map_sum, map_mul, hσ, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hJ]; ring

open GlobalTheory.AnisRatInv in
private theorem split_vec {n d₂ : ℕ} (J : Matrix (Fin n) (Fin n) E) (hσ : ∀ x, σ (σ x) = x)
    (hJ : ∀ i j, σ (J j i) = J i j) (H : Plane E n d₂)
    (hH : d₂ + 2 = n ∧ form σ J H.x H.x = 0 ∧ form σ J H.y H.y = 0 ∧ form σ J H.x H.y = 1 ∧
        (∀ u, form σ J (H.ι *ᵥ u) H.x = 0 ∧ form σ J (H.ι *ᵥ u) H.y = 0) ∧ Function.Injective H.ι.mulVec)
    (r : Fin n → E) : ∃ (s t : E) (u : Fin d₂ → E), r = s • H.x + H.ι *ᵥ u + t • H.y := by
  obtain ⟨hn, hxx, hyy, hxy, horth, hinj⟩ := hH
  have hyx : form σ J H.y H.x = 1 := by rw [form_swap_herm J hσ hJ, hxy, map_one]
  let L : (E × E × (Fin d₂ → E)) →ₗ[E] (Fin n → E) :=
    { toFun := fun p => p.1 • H.x + H.ι *ᵥ p.2.2 + p.2.1 • H.y
      map_add' := fun p q => by
        simp only [Prod.fst_add, Prod.snd_add, Matrix.mulVec_add, add_smul]; abel
      map_smul' := fun c p => by
        simp only [Prod.smul_fst, Prod.smul_snd, Matrix.mulVec_smul, smul_eq_mul, mul_smul, RingHom.id_apply,
          smul_add] }
  have hL : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨s, t, u⟩ h
    change s • H.x + H.ι *ᵥ u + t • H.y = 0 at h
    have e1 := congrArg (fun z => form σ J z H.y) h
    have e2 := congrArg (fun z => form σ J z H.x) h
    simp only [form_add_left, form_smul_left, hxy, hyy, (horth u).2, (horth u).1, hxx, hyx] at e1 e2
    have hz : ∀ z : Fin n → E, form σ J 0 z = 0 := fun z => by unfold form; simp
    rw [hz] at e1 e2
    have hs : s = 0 := by simpa using e1
    have ht : t = 0 := by simpa using e2
    subst hs ht
    simp only [zero_smul, zero_add, add_zero] at h
    have hu : u = 0 := hinj (by rw [h, Matrix.mulVec_zero])
    subst hu; rfl
  have hdim : Module.finrank E (E × E × (Fin d₂ → E)) = Module.finrank E (Fin n → E) := by
    simp [Module.finrank_prod, ← hn]; ring
  have hS : Function.Surjective L := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hL
  obtain ⟨⟨s, t, u⟩, hp⟩ := hS r
  exact ⟨s, t, u, hp.symm⟩

private theorem rho_om {B : Base F E} {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {M : Model σ X W} {χX χW : Chr F E}
    {om : Rep σ X W} {r s r' s' : ℕ} (hP : IsPair B M χX χW om r s r' s') (u : UA σ X.J) (y : Fin n → AE F E)
    (w : Fin d → AE F E) (Ψ : Fn F n d) (hΨ : Ψ ∈ schA F (Fin n × Fin d)) :
    M.co.rho B.ψ (Matrix.vecMulVec y w) (om (u, 1) Ψ) =
      om (u, 1) (M.co.rho B.ψ (Matrix.vecMulVec (mat u⁻¹ *ᵥ y) w) Ψ) := by
  have himpl := (IsUWeilPair.isUSplitting hP.weil).impl (u, (1 : UA σ W.J)) (Matrix.vecMulVec (mat u⁻¹ *ᵥ y) w) Ψ hΨ
  have h1 : mat u * mat u⁻¹ = 1 := Units.mul_inv u.1
  have hact : actAB (cA σ) (u, (1 : UA σ W.J)) (Matrix.vecMulVec (mat u⁻¹ *ᵥ y) w) = Matrix.vecMulVec y w := by
    show mat u * _ * (1 : Matrix (Fin d) (Fin d) (AE F E))ᵀ = _
    rw [Matrix.transpose_one, Matrix.mul_one, Matrix.mul_vecMulVec, Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]
  rw [hact] at himpl
  exact himpl.symm

open GlobalTheory.AnisRatInv in

private theorem term_rat {B : Base F E} {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {M : Model σ X W} {χX χW : Chr F E}
    {om : Rep σ X W} {r s r' s' : ℕ} (hP : IsPair B M χX χW om r s r' s') {d₂ : ℕ} {H : Plane E n d₂}
    (hH : d₂ + 2 = n ∧ form σ X.J H.x H.x = 0 ∧ form σ X.J H.y H.y = 0 ∧ form σ X.J H.x H.y = 1 ∧
        (∀ u, form σ X.J (H.ι *ᵥ u) H.x = 0 ∧ form σ X.J (H.ι *ᵥ u) H.y = 0) ∧ Function.Injective H.ι.mulVec)
    {V₁ : Spc F E d₂} {M₁ : Model σ V₁ W} {e : Fn F n d →ₗ[ℂ] Fn F d₂ d} (hM₁ : M₁.IsGood B.ψ)
    (he : IsEv B M M₁ H.ι 1 {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z} e)
    (hN : ∀ u ∈ unip σ X H, ∀ Ψ ∈ schA F (Fin n × Fin d), e (om (u, 1) Ψ) = e Ψ)
    (w : Fin d → E) (γ : UA σ X.J) (hγr : γ ∈ ratU σ X.J) (hγu : γ ∈ unip σ X H) (Φ : Fn F n d)
    (hΦ : Φ ∈ schA F (Fin n × Fin d)) :
    thetaSum F (e (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.y) (incV F w)) (om (γ, 1) Φ))) =
      thetaSum F (e (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.y) (incV F w)) Φ)) := by
  have hψ : IsStd B.ψ := hP.base.std
  have hM : M.IsGood B.ψ := hP.good
  have hσ : ∀ x, σ (σ x) = x := GlobalTheory.AdelicU.cm_conj_conj hP.base.cm
  obtain ⟨G, hG⟩ := exists_rat (inv_mem hγr)
  have hGu : Gᵀ * X.J * G.map σ = X.J := unitary_rat _ G hG
  have hGx : G *ᵥ H.x = H.x := incV_injective (F := F) (by
    rw [← GlobalTheory.UnipMass.incM_mulVec_incV, ← hG]; exact unip_fix (inv_mem hγu))
  obtain ⟨a, t, b, hv⟩ := split_vec X.J hσ hP.herm.herm H hH (G *ᵥ H.y - H.y)
  have hyx : form σ X.J H.y H.x = 1 := by rw [form_swap_herm X.J hσ hP.herm.herm, hH.2.2.2.1, map_one]
  have ht : t = 0 := by
    have h0 : form σ X.J (G *ᵥ H.y - H.y) H.x = 0 := by
      rw [form_sub_left]
      conv_lhs => rw [← hGx]
      rw [form_mulVec σ X.J G hGu, hGx, sub_self]
    rw [hv, form_add_left, form_add_left, form_smul_left, form_smul_left, hH.2.1, (hH.2.2.2.2.1 b).1, hyx] at h0
    linear_combination h0
  subst ht
  have hGy : G *ᵥ H.y = H.y + a • H.x + H.ι *ᵥ b := by
    rw [zero_smul, add_zero, sub_eq_iff_eq_add'] at hv
    rw [hv, add_assoc]
  have hsum : Matrix.vecMulVec (G *ᵥ H.y) w =
      Matrix.vecMulVec H.x (a • w) + (H.ι * Matrix.vecMulVec b w + Matrix.vecMulVec H.y w) := by
    rw [hGy, Matrix.mul_vecMulVec]
    ext i j
    simp only [Matrix.add_apply, Matrix.vecMulVec_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hiso : incM F (Matrix.vecMulVec H.x (a • w)) ∈
      ({u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z} : Set (Matrix (Fin n) (Fin d) (AE F E))) :=
    ⟨incV F (a • w), GlobalTheory.ThetaExpandInv.incM_vecMulVec _ _⟩
  have hI : incM F (1 : Matrix (Fin d) (Fin d) E) = 1 := Matrix.map_one _ (map_zero _) (map_one _)
  have hmul : incM F (H.ι * Matrix.vecMulVec b w) =
      incM F H.ι * incM F (Matrix.vecMulVec b w) * (incM F (1 : Matrix (Fin d) (Fin d) E))ᵀ := by
    rw [hI, Matrix.transpose_one, Matrix.mul_one]
    unfold incM
    rw [Matrix.map_mul]
  rw [rho_om hP γ _ _ Φ hΦ, hN γ hγu _ (GlobalTheory.HeisSchA.rho_mem_schA M B.ψ hψ _ _ hΦ), hG,
    GlobalTheory.UnipMass.incM_mulVec_incV, ← GlobalTheory.ThetaExpandInv.incM_vecMulVec, hsum,
    ← GlobalTheory.ThetaExpandInv.rho_rat_rho_rat M hψ hM,
    he.inv _ hiso _ (GlobalTheory.HeisSchA.rho_mem_schA M B.ψ hψ _ _ hΦ), ← GlobalTheory.ThetaExpandInv.rho_rat_rho_rat M hψ hM,
    hmul, he.Heisenberg₂ _ _ (GlobalTheory.HeisSchA.rho_mem_schA M B.ψ hψ _ _ hΦ),
    GlobalTheory.ThetaExpandInv.thetaSum_rho_rat M₁ hψ hM₁, GlobalTheory.ThetaExpandInv.incM_vecMulVec]

private theorem term_center {B : Base F E} {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {M : Model σ X W} {χX χW : Chr F E}
    {om : Rep σ X W} {r s r' s' : ℕ} (hP : IsPair B M χX χW om r s r' s') {d₂ : ℕ} {H : Plane E n d₂}
    (hxy : form σ X.J H.x H.y = 1)
    {V₁ : Spc F E d₂} {M₁ : Model σ V₁ W} {e : Fn F n d →ₗ[ℂ] Fn F d₂ d}
    (he : IsEv B M M₁ H.ι 1 {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z} e)
    (hN : ∀ u ∈ unip σ X H, ∀ Ψ ∈ schA F (Fin n × Fin d), e (om (u, 1) Ψ) = e Ψ)
    (w : Fin d → AE F E) (c : AE F E) (z : UA σ X.J) (hz : z ∈ unip σ X H)
    (hzy : mat z⁻¹ *ᵥ incV F H.y = incV F H.y - c • incV F H.x) (Φ : Fn F n d) (hΦ : Φ ∈ schA F (Fin n × Fin d)) :
    thetaSum F (e (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.y) w) (om (z, 1) Φ))) =
      B.ψ (-(⅟(2 : AF F) * Algebra.trace (AF F) (AE F E) (c * GlobalTheory.UnipMass.hA σ W.J w w))) *
        thetaSum F (e (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.y) w) Φ)) := by
  have hψ : IsStd B.ψ := hP.base.std
  set yw := Matrix.vecMulVec (incV F H.y) w with hyw
  set a := Matrix.vecMulVec (-(c • incV F H.x)) w with ha
  have hsum : Matrix.vecMulVec (mat z⁻¹ *ᵥ incV F H.y) w = a + yw := by
    rw [hzy]
    ext i j
    simp only [hyw, ha, Matrix.add_apply, Matrix.vecMulVec_apply, Pi.neg_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    ring
  have hmem : a ∈ ({u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z} : Set (Matrix (Fin n) (Fin d) (AE F E))) := by
    refine ⟨-(c • w), ?_⟩
    ext i j
    simp only [ha, Matrix.vecMulVec_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hm2 := GlobalTheory.HeisSchA.rho_mem_schA M B.ψ hψ yw Φ hΦ
  set S := symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J) a yw with hS
  have hcomp : M.co.rho B.ψ a (M.co.rho B.ψ yw Φ) = B.ψ (⅟2 * S) • M.co.rho B.ψ (a + yw) Φ := by
    simp only [Darboux.rho]
    rw [schr_schr, hS, M.co.form a yw, map_add]
  have hρ : M.co.rho B.ψ (a + yw) Φ = B.ψ (-(⅟2 * S)) • M.co.rho B.ψ a (M.co.rho B.ψ yw Φ) := by
    rw [hcomp, smul_smul, ← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one, one_smul]
  have e2 : (incV F H.x ⬝ᵥ incM F X.J *ᵥ fun k => cA σ (incV F H.y k)) = 1 := by
    rw [show (incV F H.x ⬝ᵥ incM F X.J *ᵥ fun k => cA σ (incV F H.y k)) =
      GlobalTheory.UnipMass.hA σ X.J (incV F H.x) (incV F H.y) from rfl, GlobalTheory.UnipMass.hA_incV, hxy, map_one]
  have hS' : S = Algebra.trace (AF F) (AE F E) (c * GlobalTheory.UnipMass.hA σ W.J w w) := by
    rw [hS, symp, ha, hyw, GlobalTheory.ThK.AnisPhase.hTens_vecMulVec, neg_dotProduct, smul_dotProduct, smul_eq_mul, e2, mul_one,
      neg_one_mul, neg_mul, neg_neg]
    rfl
  rw [hyw, rho_om hP z _ _ Φ hΦ, hN z hz _ (GlobalTheory.HeisSchA.rho_mem_schA M B.ψ hψ _ _ hΦ), hsum, hρ, map_smul,
    he.inv a hmem _ hm2, hS']
  simp only [thetaSum, Pi.smul_apply, smul_eq_mul]
  exact tsum_mul_left

end

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.seesaw_pair_plane_descent_third : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' →
    ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ), H'.IsAdapted σ B W W₁ i₀ i₁ →
    ∀ (d₂ : ℕ) (H : Plane E n d₂), (d₂ + 2 = n ∧ form σ X.J H.x H.x = 0 ∧ form σ X.J H.y H.y = 0 ∧ form σ X.J H.x H.y = 1 ∧
        (∀ u, form σ X.J (H.ι *ᵥ u) H.x = 0 ∧ form σ X.J (H.ι *ᵥ u) H.y = 0) ∧ Function.Injective H.ι.mulVec) →
    ∀ (V₁ : Spc F E d₂) (M₁ : Model σ V₁ W) (e : Fn F n d →ₗ[ℂ] Fn F d₂ d),
      V₁.J = H.ιᵀ * X.J * H.ι.map σ → M₁.IsGood B.ψ → IsEv B M M₁ H.ι 1 {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z} e →
    ∀ (μ : Measure (unip σ X H)) (𝓕 : Set (unip σ X H)), μ.IsHaarMeasure →
      IsFundamentalDomain ((ratU σ X.J).subgroupOf (unip σ X H)) 𝓕 μ → μ 𝓕 = 1 →
    ∀ Ψ ∈ schA F (Fin n × Fin d), ∀ w : Fin d → E, form σ W.J w w ≠ 0 →
      ∫ u in 𝓕, thetaSum F (e (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.y) (incV F w)) (om (u.1, 1) Ψ))) ∂μ = 0 := by
  intro hKP F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ hH' d₂ H hH V₁ M₁ e hV₁ hM₁ he μ 𝓕 hμ h𝓕 h1 Ψ hΨ w hw
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI : IsTopologicalGroup (UA σ X.J) := inferInstance
  haveI : BorelSpace (UA σ X.J) := ⟨rfl⟩
  have hN := GlobalTheory.T.seesaw_pair_plane_descent_first hKP F E σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ hH' d₂ H hH V₁ M₁ e hV₁ hM₁ he
  have hσ : ∀ x, σ (σ x) = x := GlobalTheory.AdelicU.cm_conj_conj hP.base.cm
  obtain ⟨δ, hδ, hσδ⟩ := GlobalTheory.HermAnisConstTerm.exists_anti hP.base.cm
  set f : E := δ * form σ W.J w w with hf
  have hf0 : f ≠ 0 := mul_ne_zero hδ hw
  have hskew : σ (form σ W.J w w) = -form σ W.J w w := by
    rw [neg_eq_iff_eq_neg.2 (GlobalTheory.AnisRatInv.form_swap σ hσ hP.skew.skew w w)]
  have hσf : σ f = f := by rw [hf, map_mul, hσδ, hskew, neg_mul_neg]
  have htr : Algebra.trace F E f ≠ 0 := by
    intro h0
    have h1 := GlobalTheory.SplitAdeleTrace.add_conj_eq_trace hP.base.cm f
    rw [hσf, h0, map_zero, ← two_mul] at h1
    exact hf0 ((mul_eq_zero.1 h1).resolve_left two_ne_zero)
  obtain ⟨s₀, hs₀⟩ := GlobalTheory.T.standard_adelic_char_exists_ne_one F B.ψ hP.base.std
  set t : AF F := -s₀ * algebraMap F (AF F) (2 / Algebra.trace F E f) with ht
  set c : AE F E := t ⊗ₜ[F] δ with hc
  have hc' : c = algebraMap (AF F) (AE F E) t * inclR (F := F) (AF F) δ := by
    rw [hc, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
    show _ = (t ⊗ₜ[F] (1 : E)) * ((1 : AF F) ⊗ₜ[F] δ)
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  have hcc : cA σ c = -c := by
    rw [hc', map_mul (cA σ), AlgHom.commutes, GlobalTheory.UnipMass.cA_inclR, hσδ, map_neg, mul_neg]
  obtain ⟨z, hzU, hzc, hzy⟩ :=
    GlobalTheory.HermAnisConstTerm.exists_central_shift_herm hσ hP.herm.herm H hH.2.1 hH.2.2.2.1 c hcc
  have hph : -(⅟(2 : AF F) * Algebra.trace (AF F) (AE F E) (c * GlobalTheory.UnipMass.hA σ W.J (incV F w) (incV F w))) = s₀ := by
    have e3 : c * GlobalTheory.UnipMass.hA σ W.J (incV F w) (incV F w) = t ⊗ₜ[F] f := by
      rw [GlobalTheory.UnipMass.hA_incV, hc]
      show (t ⊗ₜ[F] δ) * ((1 : AF F) ⊗ₜ[F] form σ W.J w w) = _
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
    rw [e3, GlobalTheory.SplitAdeleTrace.trace_baseChange_tmul, GlobalTheory.ThK.AnisPhase.invOf_two_eq, ht, mul_assoc, ← map_mul,
      div_mul_cancel₀ _ htr, mul_left_comm, ← map_mul]
    norm_num
  have hpres' := (IsUWeilPair.isUSplitting hP.weil).pres
  set T : UA σ X.J → ℂ := fun u =>
    thetaSum F (e (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.y) (incV F w)) (om (u, 1) Ψ))) with hTdef
  have hmul : ∀ g u : UA σ X.J, om (g * u, 1) Ψ = om (g, 1) (om (u, 1) Ψ) := fun g u => by
    rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, one_mul]
  have hT : ∀ u, T (z * u) = B.ψ s₀ * T u := fun u => by
    simp only [hTdef]
    rw [hmul, term_center hP hH.2.2.2.1 he hN (incV F w) c z hzU hzy _ (hpres' (u, 1) Ψ hΨ), hph]
  have hR : ∀ γ ∈ ratU σ X.J, γ ∈ unip σ X H → ∀ u, T (γ * u) = T u := fun γ hγ hγU u => by
    simp only [hTdef]
    rw [hmul, term_rat hP hH hM₁ he hN w γ hγ hγU _ (hpres' (u, 1) Ψ hΨ)]

  set z' : unip σ X H := ⟨z, hzU⟩
  haveI : Countable ((ratU σ X.J).subgroupOf (unip σ X H)) := GlobalTheory.UnipMass.countable_ratU' σ X.J (unip σ X H)
  letI : MeasurableSpace ((ratU σ X.J).subgroupOf (unip σ X H)) := ⊤
  haveI : MeasurableSMul ((ratU σ X.J).subgroupOf (unip σ X H)) (unip σ X H) :=
    { measurable_const_smul := fun c => measurable_const_mul (c : unip σ X H)
      measurable_smul_const := fun _ => measurable_from_top }
  haveI : SMulInvariantMeasure ((ratU σ X.J).subgroupOf (unip σ X H)) (unip σ X H) μ :=
    ⟨fun c _ _ => measure_preimage_mul μ (c : unip σ X H) _⟩
  let φ : unip σ X H ≃ᵐ unip σ X H := MeasurableEquiv.mulLeft z'
  have hpres : MeasurePreserving φ μ μ := measurePreserving_mul_left μ z'
  have h𝓕' : IsFundamentalDomain ((ratU σ X.J).subgroupOf (unip σ X H)) (φ ⁻¹' 𝓕) μ := by
    refine h𝓕.preimage_of_equiv hpres.quasiMeasurePreserving (e := id) Function.bijective_id ?_
    intro g x
    apply Subtype.ext
    show z * ((g : unip σ X H) * x : unip σ X H).1 = ((g : unip σ X H) : UA σ X.J) * (z * x.1)
    rw [Subgroup.coe_mul, ← mul_assoc, hzc _ (g : unip σ X H).2, mul_assoc]
  have hinvz : ∀ (g : (ratU σ X.J).subgroupOf (unip σ X H)) (x : unip σ X H), T (z * (g • x).1) = T (z * x.1) := by
    intro g x
    show T (z * ((g : unip σ X H) * x : unip σ X H).1) = _
    rw [Subgroup.coe_mul, ← mul_assoc, hzc _ (g : unip σ X H).2, mul_assoc]
    exact hR _ (Subgroup.mem_subgroupOf.1 g.2) (g : unip σ X H).2 _
  have A : ∫ u in 𝓕, T (z * u.1) ∂μ = ∫ u in φ ⁻¹' 𝓕, T (z * u.1) ∂μ := h𝓕.setIntegral_eq h𝓕' hinvz
  have B' : ∫ u in φ ⁻¹' 𝓕, T (z * u.1) ∂μ = ∫ u in 𝓕, T u.1 ∂μ :=
    hpres.setIntegral_preimage_emb φ.measurableEmbedding (fun u : unip σ X H => T u.1) 𝓕
  have C : ∫ u in 𝓕, T (z * u.1) ∂μ = B.ψ s₀ * ∫ u in 𝓕, T u.1 ∂μ := by
    simp_rw [hT]; exact integral_const_mul _ _
  have D : (B.ψ s₀ - 1) * ∫ u in 𝓕, T u.1 ∂μ = 0 := by
    rw [sub_mul, ← C, A, B', one_mul, sub_self]
  exact (mul_eq_zero.1 D).resolve_left (sub_ne_zero.2 hs₀)
