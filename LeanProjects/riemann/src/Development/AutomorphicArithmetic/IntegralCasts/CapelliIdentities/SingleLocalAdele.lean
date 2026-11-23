import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.FourierTransformBijective
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SymmetricShiftIsUnit
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.StandardAdditiveCharacter
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SchwartzFunctionGeneration

noncomputable section

namespace UpperTheory.Reformulated.B.SingleLocalAdele

open GlobalTheory.WeilM Matrix

section Local

private theorem locConst {K : Type} [NormedField K] [IsUltrametricDist K] (ψ : AddChar K ℂ) (hψ : Continuous ψ) :
    IsLocallyConstant ψ := by
  obtain ⟨δ, hδ, h⟩ := Metric.continuousAt_iff.1 (hψ.continuousAt (x := 0)) (1 / 2) (by norm_num)
  simp only [AddChar.map_zero_eq_one, dist_eq_norm, sub_zero] at h
  have key : ∀ k : ℕ, ∀ x : K, ‖x‖ < δ → ‖ψ x - 1‖ ≤ (2 / 3) ^ k := by
    intro k
    induction k with
    | zero => intro x hx; have := h hx; simp only [pow_zero]; linarith
    | succ k ih =>
      intro x hx
      have h2 := ih (x + x) (lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max x x) (by simpa using hx))
      have e : ψ (x + x) - 1 = (ψ x - 1) * (2 + (ψ x - 1)) := by rw [AddChar.map_add_eq_mul]; ring
      have h3 : (3 / 2 : ℝ) ≤ ‖2 + (ψ x - 1)‖ := by
        have h4 := norm_sub_norm_le (2 : ℂ) (-(ψ x - 1))
        rw [sub_neg_eq_add, norm_neg] at h4
        have := h hx
        simp only [Complex.norm_ofNat] at h4
        linarith
      rw [e, norm_mul] at h2
      rw [pow_succ]
      nlinarith [norm_nonneg (ψ x - 1)]
  have h1 : ∀ x : K, ‖x‖ < δ → ψ x = 1 := fun x hx => by
    have := ge_of_tendsto' (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (2 / 3 : ℝ)) (by norm_num) (by norm_num))
      (fun k => key k x hx)
    exact sub_eq_zero.1 (norm_le_zero_iff.1 this)
  refine (IsLocallyConstant.iff_eventually_eq _).2 fun x => ?_
  filter_upwards [Metric.ball_mem_nhds x hδ] with y hy
  rw [← add_sub_cancel x y, AddChar.map_add_eq_mul, h1 (y - x) (by simpa [dist_eq_norm] using hy), mul_one]

private theorem sb_comp {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (h : X ≃ₜ Y) {f : Y → ℂ}
    (hf : f ∈ SB Y) : f ∘ h ∈ SB X :=
  ⟨hf.1.comp_continuous h.continuous, hf.2.comp_homeomorph h⟩

private theorem bij_comp {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (h : X ≃ₜ Y) :
    Set.BijOn (LinearMap.funLeft ℂ ℂ h) (SB Y : Set _) (SB X : Set _) :=
  Set.InvOn.bijOn (f' := LinearMap.funLeft ℂ ℂ h.symm)
    ⟨fun f _ => funext fun y => by simp [LinearMap.funLeft_apply], fun f _ => funext fun y => by
      simp [LinearMap.funLeft_apply]⟩ (fun _ hf => sb_comp h hf) (fun _ hf => sb_comp h.symm hf)

private theorem sb_mul {X : Type} [TopologicalSpace X] {c f : X → ℂ} (hc : IsLocallyConstant c)
    (hf : f ∈ SB X) : c * f ∈ SB X :=
  ⟨hc.mul hf.1, hf.2.mul_left⟩

variable {K : Type} [NontriviallyNormedField K] [IsUltrametricDist K] [ProperSpace K] [Invertible (2 : K)]
  {ψ : AddChar K ℂ} {κ : Type} [Fintype κ] [DecidableEq κ]

private theorem inter (hψ : IsLocallyConstant ψ) (h1 : ∃ t, ψ t ≠ 1)
    (g : (κ → K) × (κ → K) →ₗ[K] (κ → K) × (κ → K))
    (hg : ∀ w w', (g w).1 ⬝ᵥ (g w').2 - (g w').1 ⬝ᵥ (g w).2 = w.1 ⬝ᵥ w'.2 - w'.1 ⬝ᵥ w.2) :
    ∃ ι : ((κ → K) → ℂ) →ₗ[ℂ] ((κ → K) → ℂ), Set.BijOn ι (SB (κ → K) : Set _) (SB (κ → K) : Set _) ∧
      ∀ w, ∀ φ ∈ SB (κ → K), ι (schr ψ (g w) φ) = schr ψ w (ι φ) := by
  refine UpperTheory.symplectic_generation K κ (fun f => ∃ ι : ((κ → K) → ℂ) →ₗ[ℂ] ((κ → K) → ℂ),
    Set.BijOn ι (SB (κ → K) : Set _) (SB (κ → K) : Set _) ∧
      ∀ w, ∀ φ ∈ SB (κ → K), ι (schr ψ (f w) φ) = schr ψ w (ι φ)) ?_ ?_ ?_ ?_ g hg
  · rintro f g ⟨a, ha, ha'⟩ ⟨b, hb, hb'⟩
    exact ⟨b ∘ₗ a, hb.comp ha, fun w φ hφ => by
      simp only [LinearMap.comp_apply, Function.comp_apply]
      rw [ha' _ _ hφ, hb' _ _ (ha.mapsTo hφ)]⟩
  · obtain ⟨T, hT, ht, hm⟩ := UpperTheory.fourier_transform_bijective K ψ hψ h1 κ
    refine ⟨LinearMap.funLeft ℂ ℂ (Homeomorph.neg (κ → K)) ∘ₗ T, (bij_comp _).comp hT, fun w φ hφ => ?_⟩
    have e : schr ψ (w.2, -w.1) φ =
        ψ (⅟(2 : K) * (w.2 ⬝ᵥ (-w.1))) • fun x => ψ (x ⬝ᵥ (-w.1)) * (fun x => φ (x + w.2)) x := by
      funext x
      simp only [schr, AddChar.map_add_eq_mul, Pi.smul_apply, smul_eq_mul]; ring
    have hφ' := sb_comp (Homeomorph.addRight w.2) hφ
    funext y
    simp only [LinearMap.comp_apply, LinearMap.funLeft_apply, Homeomorph.coe_neg, Pi.neg_apply]
    rw [e, map_smul, Pi.smul_apply, hm (fun x => φ (x + w.2)) hφ'.1 hφ'.2, ht φ hφ.1 hφ.2]
    simp only [schr, LinearMap.funLeft_apply, Homeomorph.coe_neg, Pi.neg_apply, smul_eq_mul, ← mul_assoc, neg_add,
      ← AddChar.map_add_eq_mul]
    congr 2
    simp only [dotProduct_comm w.2, neg_dotProduct, add_dotProduct]
    linear_combination (-(w.1 ⬝ᵥ w.2)) * invOf_mul_self (2 : K)
  · intro S hS
    have hq : ∀ c : K, IsLocallyConstant fun x : κ → K => ψ (c * (x ⬝ᵥ S *ᵥ x)) := fun c =>
      hψ.comp_continuous (continuous_const.mul (continuous_id.dotProduct (continuous_const.matrix_mulVec continuous_id)))
    refine ⟨LinearMap.mulLeft ℂ (fun x : κ → K => ψ (⅟(2 : K) * (x ⬝ᵥ S *ᵥ x))),
      Set.InvOn.bijOn (f' := LinearMap.mulLeft ℂ (fun x : κ → K => ψ (-⅟(2 : K) * (x ⬝ᵥ S *ᵥ x))))
        ⟨fun f _ => funext fun y => ?_, fun f _ => funext fun y => ?_⟩
        (fun _ hf => sb_mul (hq _) hf) (fun _ hf => sb_mul (hq _) hf), fun w φ hφ => funext fun x => ?_⟩
    · simp only [LinearMap.mulLeft_apply, Pi.mul_apply, ← mul_assoc, ← AddChar.map_add_eq_mul]; simp
    · simp only [LinearMap.mulLeft_apply, Pi.mul_apply, ← mul_assoc, ← AddChar.map_add_eq_mul]; simp
    · simp only [schr, LinearMap.mulLeft_apply, Pi.mul_apply, ← mul_assoc, ← AddChar.map_add_eq_mul]
      congr 2
      have e : w.1 ⬝ᵥ S *ᵥ x = x ⬝ᵥ S *ᵥ w.1 := by
        rw [dotProduct_mulVec, ← mulVec_transpose, hS.eq, dotProduct_comm]
      simp only [dotProduct_add, add_dotProduct, mulVec_add, e]
      linear_combination (-(x ⬝ᵥ S *ᵥ w.1)) * invOf_mul_self (2 : K)
  · intro A A' hA
    have hA' : A * A' = 1 := mul_eq_one_comm.1 hA
    let h : (κ → K) ≃ₜ (κ → K) :=
      { toFun := fun x => A *ᵥ x
        invFun := fun x => A' *ᵥ x
        left_inv := fun x => by simp [hA]
        right_inv := fun x => by simp [hA']
        continuous_toFun := continuous_const.matrix_mulVec continuous_id
        continuous_invFun := continuous_const.matrix_mulVec continuous_id }
    refine ⟨LinearMap.funLeft ℂ ℂ h, bij_comp h, fun w φ hφ => funext fun x => ?_⟩
    have e : ∀ a b : κ → K, (A *ᵥ a) ⬝ᵥ (A'ᵀ *ᵥ b) = a ⬝ᵥ b := fun a b => by
      rw [dotProduct_mulVec, vecMul_transpose, mulVec_mulVec, hA, one_mulVec]
    change schr ψ _ φ (A *ᵥ x) = _ * φ (A *ᵥ (x + w.1))
    simp only [schr, e, mulVec_add]

private theorem inter2 (hψ : IsLocallyConstant ψ) (h1 : ∃ t, ψ t ≠ 1)
    (G : (κ → K) × (κ → K) →ₗ[K] (κ → K) × (κ → K)) (hG : Function.Injective G)
    (ha : ∀ y z, (G (y, 0)).1 ⬝ᵥ (G (z, 0)).2 - (G (z, 0)).1 ⬝ᵥ (G (y, 0)).2 = 0)
    (hb : ∀ y z, (G (0, y)).1 ⬝ᵥ (G (0, z)).2 - (G (0, z)).1 ⬝ᵥ (G (0, y)).2 = 0) :
    ∃ ι : ((κ → K) → ℂ) →ₗ[ℂ] ((κ → K) → ℂ), Set.BijOn ι (SB (κ → K) : Set _) (SB (κ → K) : Set _) ∧
      (∀ y, ∀ φ ∈ SB (κ → K), ∀ Y, ι (schr ψ (G (y, 0)) φ) Y = ι φ (Y + y)) ∧
      ∀ z, ∀ φ ∈ SB (κ → K), ∀ Y, ι (schr ψ (G (0, z)) φ) Y =
        ψ ((G (Y, 0)).1 ⬝ᵥ (G (0, z)).2 - (G (0, z)).1 ⬝ᵥ (G (Y, 0)).2) * ι φ Y := by
  let ω : ((κ → K) × (κ → K)) →ₗ[K] ((κ → K) × (κ → K)) →ₗ[K] K :=
    LinearMap.mk₂ K (fun w w' => w.1 ⬝ᵥ w'.2 - w'.1 ⬝ᵥ w.2)
      (fun _ _ _ => by simp; ring) (fun _ _ _ => by simp; ring) (fun _ _ _ => by simp; ring) (fun _ _ _ => by simp; ring)
  have hω : ∀ w w', ω w w' = w.1 ⬝ᵥ w'.2 - w'.1 ⬝ᵥ w.2 := fun _ _ => rfl
  have hanti : ∀ w w', ω w w' = -ω w' w := fun _ _ => by simp [hω]
  let β : (κ → K) →ₗ[K] (κ → K) →ₗ[K] K := ω.compl₁₂ (G ∘ₗ LinearMap.inl K _ _) (G ∘ₗ LinearMap.inr K _ _)
  have hβ : ∀ y z, β y z = ω (G (y, 0)) (G (0, z)) := fun _ _ => rfl
  let N : (κ → K) →ₗ[K] (κ → K) := LinearMap.pi fun i => β (Pi.single i 1)
  have hN : ∀ y z, y ⬝ᵥ N z = β y z := fun y z => by
    conv_rhs => rw [← Finset.univ_sum_single y]
    rw [map_sum, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show (Pi.single i (y i) : κ → K) = y i • Pi.single i 1 by rw [← Pi.single_smul]; simp, map_smul]
    rfl
  have hsp : ∀ w, G w = G (w.1, 0) + G (0, w.2) := fun w => by rw [← map_add]; simp
  have hNi : Function.Injective N := (injective_iff_map_eq_zero _).2 fun z hz => by
    have h0 : ∀ w, ω w (G (0, z)) = 0 := fun w => by
      obtain ⟨w, rfl⟩ := LinearMap.injective_iff_surjective.1 hG w
      rw [hsp, map_add, LinearMap.add_apply, ← hβ, ← hN, hz, hω, hb]; simp
    have : G (0, z) = G 0 := by
      rw [map_zero]
      refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
      · simpa [hω] using h0 (0, Pi.single i 1)
      · simpa [hω] using h0 (Pi.single i 1, 0)
    exact congrArg Prod.snd (hG this)
  let e := LinearEquiv.ofInjectiveEndo N hNi
  have he : ∀ z, N (e.symm z) = z := e.apply_symm_apply
  have he' : ∀ z, e.symm (N z) = z := e.symm_apply_apply
  obtain ⟨ι, hι, H⟩ := inter hψ h1 (G ∘ₗ LinearMap.prodMap LinearMap.id e.symm.toLinearMap) fun w w' => by
    change ω (G (w.1, e.symm w.2)) (G (w'.1, e.symm w'.2)) = _
    rw [hsp (w.1, _), hsp (w'.1, _)]
    simp only [map_add, LinearMap.add_apply]
    rw [hanti (G (0, _)) (G (_, 0)), ← hβ, ← hβ, ← hN, ← hN, he, he, hω, hω, ha, hb]
    ring
  refine ⟨ι, hι, fun y φ hφ Y => ?_, fun z φ hφ Y => ?_⟩
  · simpa [schr] using congrFun (H (y, 0) φ hφ) Y
  · have := congrFun (H (0, N z) φ hφ) Y
    rw [← hω, ← hβ, ← hN]
    simpa [schr, he'] using this

end Local

section Global

open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

private def sL (v : Pl F) : Fv F v →ₗ[F] AF F := (LinearMap.inr F (Ainf F) (Af F)).comp (singleFin v)

private theorem eval_single_local (v : Pl F) (a : Fv F v) : evFin F v (sL v a) = a := evalV_singleFin_self v a

private theorem mul_s (v : Pl F) (u : AF F) (a : Fv F v) : u * sL v a = sL v (evFin F v u * a) := by
  refine Prod.ext ((mul_zero _).trans rfl) (af_ext fun w => ?_)
  change evalV F w (u.2 * singleFin v a) = evalV F w (singleFin v (evFin F v u * a))
  rw [map_mul]
  by_cases h : w = v
  · subst h; rw [evalV_singleFin_self, evalV_singleFin_self]; rfl
  · rw [evalV_singleFin_ne h, evalV_singleFin_ne h, mul_zero]

private theorem sL_one_mul_eq_sL_evFin (v : Pl F) (u : AF F) : sL v 1 * u = sL v (evFin F v u) := by
  rw [mul_comm, mul_s, mul_one]

private theorem at_iff {M : Type} [AddCommGroup M] [Module (AF F) M] (v : Pl F) (z : M) :
    At (evFin F v) z ↔ sL v 1 • z = z := by
  refine ⟨fun h => ?_, fun h u hu => ?_⟩
  · have := h (1 - sL v 1) (by rw [map_sub, map_one, eval_single_local, sub_self])
    rw [sub_smul, one_smul, sub_eq_zero] at this
    exact this.symm
  · rw [← h, smul_smul, mul_s, hu, zero_mul, map_zero, zero_smul]

private theorem leviSection_continuous (v : Pl F) : Continuous (sL v) :=
  continuous_const.prodMk (continuous_singleFin v)

private def psiK (ψ : AddChar (AF F) ℂ) (v : Pl F) : AddChar (Fv F v) ℂ := ψ.compAddMonoidHom (sL v).toAddMonoidHom

private theorem psi_at (ψ : AddChar (AF F) ℂ) (v : Pl F) {a : AF F} (h : sL v 1 * a = a) :
    ψ a = psiK ψ v (evFin F v a) := by
  rw [sL_one_mul_eq_sL_evFin] at h
  exact (congrArg ψ h).symm

private theorem psiK_ne {ψ : AddChar (AF F) ℂ} (h : IsStd ψ) (v : Pl F) : ∃ t, psiK ψ v t ≠ 1 := by
  obtain ⟨a, h1, h2, h3⟩ := UpperTheory.standard_additive_character F ψ h.1 h.2.1 (fun a ha => h.2.2 a fun u hu => by
    have hu1 : u.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (hu.trans (map_zero _).symm)
    refine Prod.ext ?_ ?_
    · change u.1 * a.1 = 0
      rw [hu1, zero_mul]
    · change u.2 * a.2 = 0
      rw [ha, mul_zero]) v
  refine ⟨evFin F v a, fun e => h3 (Eq.trans (psi_at ψ v ?_) e)⟩
  rw [sL_one_mul_eq_sL_evFin]
  refine Prod.ext h1.symm (af_ext fun w => ?_)
  change evalV F w (singleFin v _) = _
  by_cases h : w = v
  · subst h; rw [evalV_singleFin_self]; rfl
  · rw [evalV_singleFin_ne h]; exact (h2 w h).symm

private theorem exists_schwartz (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] :
    ∃ f : SchwartzMap V ℂ, f 0 = 1 := by
  let b : ContDiffBump (0 : V) := ⟨1, 2, one_pos, one_lt_two⟩
  have h1 : HasCompactSupport fun x => (b x : ℂ) := b.hasCompactSupport.comp_left (g := fun t : ℝ => (t : ℂ)) rfl
  have h2 : ContDiff ℝ (⊤ : ℕ∞) fun x => (b x : ℂ) := Complex.ofRealCLM.contDiff.comp b.contDiff
  refine ⟨h1.toSchwartzMap h2, ?_⟩
  change ((b 0 : ℝ) : ℂ) = 1
  rw [b.one_of_mem_closedBall (Metric.mem_closedBall_self zero_le_one), Complex.ofReal_one]

private def evp {κ : Type} (v : Pl F) (w : (κ → AF F) × (κ → AF F)) : (κ → Fv F v) × (κ → Fv F v) :=
  (fun i => evFin F v (w.1 i), fun i => evFin F v (w.2 i))

private theorem ev_dot {κ : Type} [Fintype κ] (v : Pl F) (a b : κ → AF F) :
    evFin F v (a ⬝ᵥ b) = (fun i => evFin F v (a i)) ⬝ᵥ fun i => evFin F v (b i) := by
  simp only [dotProduct, map_sum, map_mul]

open Classical in
private theorem acts_eq {κ : Type} [Fintype κ] (ψ : AddChar (AF F) ℂ) (v : Pl F) [Invertible (2 : Fv F v)]
    {w : (κ → AF F) × (κ → AF F)} (hw : sL v 1 • w = w) {φ φ₁ : (κ → Fv F v) → ℂ} (hφ : φ ∈ SB _)
    (h : Acts (evFin F v) (schr ψ w) φ φ₁) : φ₁ = schr (psiK ψ v) (evp v w) φ := by
  obtain ⟨f, hf⟩ := exists_schwartz (κ → mixedEmbedding.mixedSpace F)
  let S : Set (κ → Af F) := {z | ∀ i u, u ≠ v → z i u ∈ u.adicCompletionIntegers F}
  let r : (κ → AF F) → ℂ := fun x => f (fun i => evI F (x i)) * S.indicator 1 fun i => (x i).2
  have hr : ∀ x z : κ → AF F, sL v 1 • z = z → r (x + z) = r x := fun x z hz => by
    have h0 : ∀ i, z i = sL v (evFin F v (z i)) := fun i => (congrFun hz i).symm.trans (sL_one_mul_eq_sL_evFin v _)
    have h1 : (fun i => evI F ((x + z) i)) = fun i => evI F (x i) := funext fun i => by
      have : (z i).1 = 0 := by rw [h0]; rfl
      change InfiniteAdeleRing.ringEquiv_mixedSpace F ((x i).1 + (z i).1) = _
      rw [this, add_zero]; rfl
    have h2 : (fun i => ((x + z) i).2) ∈ S ↔ (fun i => (x i).2) ∈ S := by
      refine forall_congr' fun i => forall_congr' fun u => forall_congr' fun hu => ?_
      have : evalV F u (z i).2 = 0 := by rw [h0]; exact evalV_singleFin_ne hu _
      change evalV F u ((x i).2 + (z i).2) ∈ _ ↔ evalV F u (x i).2 ∈ _
      rw [map_add, this, add_zero]
    simp only [r, h1, Set.indicator, h2, Pi.one_apply]
  have hg := UpperTheory.schwartz_function_generation F (fun u => (locField u).toLocallyCompactSpace) κ v φ hφ.1 hφ.2 _ fun _ => rfl
  have hR : Rest (evFin F v) φ r := ⟨fun x z hz => hr x z ((at_iff v z).1 hz),
    Submodule.subset_span ⟨f, _, hg, funext fun x => mul_left_comm _ _ _⟩⟩
  have hr0 : r 0 = 1 := by
    have h1 : (fun i => evI F ((0 : κ → AF F) i)) = 0 := funext fun i => map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F)
    have h2 : (fun i => ((0 : κ → AF F) i).2) ∈ S := fun i u _ => zero_mem _
    simp only [r, h1, hf, Set.indicator_of_mem h2, Pi.one_apply, mul_one]
  funext X
  let x : κ → AF F := fun i => sL v (X i)
  have hx : sL v 1 • x = x := funext fun i => by
    change sL v 1 * sL v (X i) = sL v (X i)
    rw [sL_one_mul_eq_sL_evFin, eval_single_local]
  have hw1 : sL v 1 • w.1 = w.1 := congrArg Prod.fst hw
  have hw2 : sL v 1 • w.2 = w.2 := congrArg Prod.snd hw
  have hx1 : r x = 1 := by rw [← zero_add x, hr _ _ hx, hr0]
  have hX : (fun i => evFin F v (x i)) = X := funext fun i => eval_single_local v _
  have h2 : evFin F v (⅟(2 : AF F)) = ⅟(2 : Fv F v) := by
    refine (invOf_eq_right_inv ?_).symm
    rw [← map_ofNat (evFin F v) 2, ← map_mul, mul_invOf_self, map_one]
  have := congrFun (h r hR) x
  simp only [tens, schr] at this
  rw [hr _ _ hw1, hx1, hX, mul_one, mul_one, psi_at ψ v (by
    rw [mul_add, mul_left_comm, ← smul_eq_mul (sL v 1), ← smul_eq_mul (sL v 1), ← dotProduct_smul, ← dotProduct_smul,
      hw2]), map_add, map_mul, ev_dot, ev_dot, hX, h2] at this
  rw [← this]
  simp only [schr, evp, Pi.add_apply, map_add]
  congr 2
  funext i
  exact congrArg (· + _) (eval_single_local v _)

private theorem comp_rT (v : Pl F) (y : Fv F v ⊗[F] E) : compFin F E v (LinearMap.rTensor E (sL v) y) = y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a e => exact congrArg (· ⊗ₜ[F] e) (eval_single_local v a)

private theorem rT_comp (v : Pl F) (z : AE F E) : LinearMap.rTensor E (sL v) (compFin F E v z) = sL v 1 • z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy, smul_add]
  | tmul a e => exact congrArg (· ⊗ₜ[F] e) (sL_one_mul_eq_sL_evFin v a).symm

private theorem rT_smul (v : Pl F) (a : Fv F v) (y : Fv F v ⊗[F] E) :
    LinearMap.rTensor E (sL v) (a • y) = sL v a • LinearMap.rTensor E (sL v) y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy, smul_add]
  | tmul b e =>
    refine congrArg (· ⊗ₜ[F] e) (?_ : sL v (a * b) = sL v a * sL v b)
    rw [mul_s, eval_single_local]

private theorem piW_cA {v : Pl F} (t : E →ₐ[F] Fv F v) (z : AE F E) : piW t (cA σ z) = piW (t.comp σ) z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul b e => rfl

variable {n d : ℕ}

private theorem iso_symp (h : IsCMExt F E σ) {v : Pl F} (t : E →ₐ[F] Fv F v) (JA : Matrix (Fin n) (Fin n) (AE F E))
    (JB : Matrix (Fin d) (Fin d) (AE F E)) {x u : Matrix (Fin n) (Fin d) (AE F E)} (hx : ∀ i j, piW t (x i j) = 0)
    (hu : ∀ i j, piW t (u i j) = 0) : evFin F v (symp (R := AF F) (cA σ) (-1) JA JB x u) = 0 := by
  have h0 : compFin F E v (hTens (cA σ) JA JB x u) = 0 := by
    refine split_ext h t ?_ ?_
    · change piW t _ = _
      simp only [hTens, map_sum, map_mul, hx, zero_mul, Finset.sum_const_zero, map_zero]
    · change piW (t.comp σ) _ = _
      simp only [hTens, map_sum, map_mul, piW_cA, comp_conj_conj h, hu, mul_zero, Finset.sum_const_zero, map_zero]
  have h1 := rT_comp v (hTens (cA σ) JA JB x u)
  rw [h0, map_zero] at h1
  have h2 : sL v 1 * symp (R := AF F) (cA σ) (-1) JA JB x u = 0 := by
    rw [symp, ← smul_eq_mul, ← map_smul, ← mul_smul_comm, ← h1, mul_zero, map_zero]
  have h3 := congrArg (evFin F v) h2
  rwa [map_mul, eval_single_local, one_mul, map_zero] at h3

private def liftM (h : IsCMExt F E σ) {v : Pl F} (t : E →ₐ[F] Fv F v)
    (p : (Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v)) : Matrix (Fin n) (Fin d) (AE F E) :=
  Matrix.of fun i j => LinearMap.rTensor E (sL v) ((splitAlgEquiv h t).symm (p.1 (i, j), p.2 (i, j)))

variable (h : IsCMExt F E σ) {v : Pl F} (t : E →ₐ[F] Fv F v)

private theorem liftM_add (p q : (Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v)) :
    liftM h t (p + q) = liftM h t p + liftM h t q := Matrix.ext fun i j => by
  simp only [liftM, Matrix.of_apply, Matrix.add_apply, ← map_add]; rfl

private theorem liftM_smul (a : Fv F v) (p : (Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v)) :
    liftM h t (a • p) = sL v a • liftM h t p := Matrix.ext fun i j => by
  simp only [liftM, Matrix.of_apply, Matrix.smul_apply, ← rT_smul, ← map_smul]; rfl

private theorem liftM_at (p : (Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v)) :
    sL v 1 • liftM h t p = liftM h t p := by rw [← liftM_smul, one_smul]

private theorem piW_liftM (p : (Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v)) (i j) :
    piW t (liftM h t p i j) = p.1 (i, j) := by
  change splitProj t (compFin F E v (LinearMap.rTensor E (sL v) _)) = _
  rw [comp_rT, splitProj_symm]

private theorem piW_liftM' (p : (Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v)) (i j) :
    piW (t.comp σ) (liftM h t p i j) = p.2 (i, j) := by
  change splitProj (t.comp σ) (compFin F E v (LinearMap.rTensor E (sL v) _)) = _
  rw [comp_rT, splitProj_comp_symm]

private theorem liftM_piW {u : Matrix (Fin n) (Fin d) (AE F E)} (hu : sL v 1 • u = u) :
    liftM h t (fun k => piW t (u k.1 k.2), fun k => piW (t.comp σ) (u k.1 k.2)) = u := Matrix.ext fun i j => by
  change LinearMap.rTensor E (sL v) ((splitAlgEquiv h t).symm (splitAlgEquiv h t (compFin F E v (u i j)))) = _
  rw [AlgEquiv.symm_apply_apply, rT_comp]
  exact congrFun₂ hu i j

end Global

section Main

open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}

private theorem main {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ)
    (h : IsCMExt F E σ) (v : Pl F) (t : E →ₐ[F] Fv F v) :
    ∃ ι : ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] Matrix (Fin n) (Fin d) (Fv F v) → ℂ, M.IsLinW ψ t 1 1 ι := by
  letI : NontriviallyNormedField (Fv F v) := Valued.toNontriviallyNormedField (Fv F v) (WithZero (Multiplicative ℤ))
  haveI : LocallyCompactSpace (Fv F v) := (locField v).toLocallyCompactSpace
  haveI : ProperSpace (Fv F v) := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace _
  haveI : IsUltrametricDist (Fv F v) := inferInstance
  letI : Invertible (2 : Fv F v) := invertibleOfNonzero (by
    rw [← map_ofNat (algebraMap F (Fv F v)) 2]; exact (map_ne_zero _).2 two_ne_zero)
  let G : ((Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v)) →ₗ[Fv F v]
      ((Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v)) :=
    { toFun := fun p => evp v (M.co.e (liftM h t p))
      map_add' := fun p q => by
        rw [liftM_add, map_add]
        exact Prod.ext (funext fun i => map_add (evFin F v) _ _) (funext fun i => map_add (evFin F v) _ _)
      map_smul' := fun a p => by
        rw [liftM_smul, map_smul]
        exact Prod.ext (funext fun i => (map_mul (evFin F v) _ _).trans (congrArg (· * _) (eval_single_local v a)))
          (funext fun i => (map_mul (evFin F v) _ _).trans (congrArg (· * _) (eval_single_local v a))) }
  have hG : ∀ p, G p = evp v (M.co.e (liftM h t p)) := fun _ => rfl
  have hf : ∀ x u, evFin F v (symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J) x u) =
      (evp v (M.co.e x)).1 ⬝ᵥ (evp v (M.co.e u)).2 - (evp v (M.co.e u)).1 ⬝ᵥ (evp v (M.co.e x)).2 := fun x u => by
    rw [M.co.form, map_sub, ev_dot, ev_dot]; rfl
  have hinj : Function.Injective G := (injective_iff_map_eq_zero _).2 fun p hp => by
    have h1 : M.co.e (liftM h t p) = 0 := by
      rw [← liftM_at, map_smul]
      refine Prod.ext (funext fun i => (sL_one_mul_eq_sL_evFin v _).trans ?_) (funext fun i => (sL_one_mul_eq_sL_evFin v _).trans ?_)
      · exact (congrArg (sL v) (congrFun (congrArg Prod.fst hp) i)).trans (map_zero _)
      · exact (congrArg (sL v) (congrFun (congrArg Prod.snd hp) i)).trans (map_zero _)
    have h2 : liftM h t p = 0 := M.co.e.map_eq_zero_iff.1 h1
    refine Prod.ext (funext fun k => ?_) (funext fun k => ?_)
    · rw [← piW_liftM h t p k.1 k.2, h2]; exact map_zero _
    · rw [← piW_liftM' h t p k.1 k.2, h2]; exact map_zero _
  have hcc : ∀ z : AE F E, piW t z = piW ((t.comp σ).comp σ) z := fun z => by rw [comp_conj_conj h]
  obtain ⟨ι, hι, ht, hm⟩ := inter2 (locConst (psiK ψ v) (hψ.1.comp (leviSection_continuous v))) (psiK_ne hψ v) G hinj
    (fun y z => (hf _ _).symm.trans
      (iso_symp h (t.comp σ) _ _ (fun i j => piW_liftM' h t _ i j) fun i j => piW_liftM' h t _ i j))
    (fun y z => (hf _ _).symm.trans
      (iso_symp h t _ _ (fun i j => piW_liftM h t _ i j) fun i j => piW_liftM h t _ i j))
  let c : Matrix (Fin n) (Fin d) (Fv F v) ≃ₜ (Fin n × Fin d → Fv F v) :=
    { toFun := fun Y k => Y k.1 k.2
      invFun := fun y => Matrix.of fun i j => y (i, j)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      continuous_toFun := continuous_pi fun k => continuous_id.matrix_elem k.1 k.2
      continuous_invFun := continuous_matrix fun i j => continuous_apply _ }
  have hco : ∀ u : Matrix (Fin n) (Fin d) (AE F E), ((1 : GL (Fin n) (Fv F v))⁻¹).1 * u.map (piW t) *
      ((1 : GL (Fin d) (Fv F v))⁻¹).1ᵀ = u.map (piW t) := fun u => by simp
  have h1 : ∀ u : Matrix (Fin n) (Fin d) (AE F E), At (evFin F v) u → u.map (piW (t.comp σ)) = 0 →
      G (c (u.map (piW t)), 0) = evp v (M.co.e u) := fun u hu h0 => by
    rw [hG]
    conv_rhs => rw [← liftM_piW h t ((at_iff v u).1 hu)]
    congr 4
    exact funext fun k => (congrFun₂ h0 k.1 k.2).symm
  have h0 : ∀ u : Matrix (Fin n) (Fin d) (AE F E), At (evFin F v) u → u.map (piW t) = 0 →
      G (0, c (u.map (piW (t.comp σ)))) = evp v (M.co.e u) := fun u hu h0 => by
    rw [hG]
    conv_rhs => rw [← liftM_piW h t ((at_iff v u).1 hu)]
    congr 4
    exact funext fun k => (congrFun₂ h0 k.1 k.2).symm
  have hat : ∀ u : Matrix (Fin n) (Fin d) (AE F E), At (evFin F v) u → sL v 1 • M.co.e u = M.co.e u := fun u hu => by
    rw [← map_smul, (at_iff v u).1 hu]
  refine ⟨LinearMap.funLeft ℂ ℂ c ∘ₗ ι, (bij_comp c).comp hι, fun u hu hu0 φ hφ φ₁ _ hA Y => ?_,
    fun u hu hu0 φ hφ φ₁ _ hA x hx hx0 => ?_⟩
  · rw [acts_eq ψ v (hat u hu) hφ hA, ← h1 u hu hu0, hco]
    exact ht _ φ hφ (c Y)
  · rw [acts_eq ψ v (hat u hu) hφ hA, hco, psi_at ψ v (a := symp (R := AF F) (cA σ) (-1) _ _ x u) (by
      have e1 : sL v 1 • (M.co.e u).1 = (M.co.e u).1 := congrArg Prod.fst (hat u hu)
      have e2 : sL v 1 • (M.co.e u).2 = (M.co.e u).2 := congrArg Prod.snd (hat u hu)
      rw [M.co.form, mul_sub, ← smul_eq_mul (sL v 1), ← smul_eq_mul (sL v 1), ← dotProduct_smul, ← smul_dotProduct,
        e1, e2]), hf, ← h0 u hu hu0, ← h1 x hx hx0]
    exact hm _ φ hφ _

end Main

end UpperTheory.Reformulated.B.SingleLocalAdele

end

theorem UpperTheory.Reformulated.B.SingleLocalAdele.exists_linW :
    ∀ {F E : Type} [inst : Field F] [inst_1 : NumberField F] [inst_2 : Field E] [inst_3 : NumberField E]
      [inst_4 : Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ} {X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d}
      (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ X W) (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr F E)
      (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ X W) {r s r' s' : ℕ},
      GlobalTheory.ThK.IsPair B M χX χW om r s r' s' →
        ∀ (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) (t : E →ₐ[F] Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v),
          ∃ (ι :
            ((Fin n × Fin d → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) → ℂ) →ₗ[ℂ] Matrix (Fin n) (Fin d) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) → ℂ),
            M.IsLinW B.ψ t (1 : GL (Fin n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v)) (1 : GL (Fin d) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v)) ι := by
  intro F E _ _ _ _ _ σ n d X W B M χX χW om r s r' s' H v t
  exact UpperTheory.Reformulated.B.SingleLocalAdele.main M H.base.std H.base.cm v t
