import Mathlib
import GroundTheory.AutomorphicForms.ReductionHeight
import GroundTheory.AutomorphicForms.Iwasawa
import GroundTheory.AutomorphicForms.RealGroupsIwasawa
import GroundTheory.GlobalFields.IdeleGroups.UnitBound

open NumberField IsDedekindDomain Topology Filter Set Matrix
open scoped NumberField.AdeleRing RestrictedProduct

namespace GroundTheory.Automorphic

noncomputable section

namespace Reduction

section Unitary

variable {𝕜 : Type*} [RCLike 𝕜] {n : ℕ}

theorem sum_norm_sq_vecMul_unitary {U : Matrix (Fin n) (Fin n) 𝕜} (hU : U ∈ unitaryGroup (Fin n) 𝕜)
    (z : Fin n → 𝕜) : ∑ j, ‖(z ᵥ* U) j‖ ^ 2 = ∑ i, ‖z i‖ ^ 2 := by
  have key : ∀ y : Fin n → 𝕜, ((∑ i, ‖y i‖ ^ 2 : ℝ) : 𝕜) = y ⬝ᵥ star y := by
    intro y
    simp only [dotProduct, Pi.star_apply, RCLike.star_def, RCLike.mul_conj]
    push_cast
    rfl
  apply (RCLike.ofReal_injective (K := 𝕜))
  rw [key, key, star_vecMul, dotProduct_mulVec, vecMul_vecMul]
  rw [mem_unitaryGroup_iff] at hU
  rw [show U * Uᴴ = 1 from hU, vecMul_one]

theorem euclidNorm_vecMul_unitary {U : Matrix (Fin n) (Fin n) 𝕜} (hU : U ∈ unitaryGroup (Fin n) 𝕜)
    (z : Fin n → 𝕜) : euclidNorm (z ᵥ* U) = euclidNorm z := by
  rw [euclidNorm, euclidNorm, sum_norm_sq_vecMul_unitary hU]

end Unitary

section Transport

variable {E 𝕜 : Type*} [NormedField E] [RCLike 𝕜] {n : ℕ}

theorem euclidNorm_map {F : Type*} [NormedField F] (φ : E →+* F) (hφ : ∀ x, ‖φ x‖ = ‖x‖)
    (y : Fin n → E) : euclidNorm (fun i => φ (y i)) = euclidNorm y := by
  simp [euclidNorm, hφ]

theorem exists_upper_mul_of_ringEquiv (φ : E ≃+* 𝕜) (hφ : ∀ x, ‖φ x‖ = ‖x‖) (h : GL (Fin n) E) :
    ∃ b : GL (Fin n) E, (b : Matrix (Fin n) (Fin n) E).IsUpperTriangular ∧
      ∃ k : GL (Fin n) E, (∀ y : Fin n → E,
        euclidNorm (y ᵥ* (k : Matrix (Fin n) (Fin n) E)) = euclidNorm y) ∧ h = b * k := by
  have hφ' : ∀ x, ‖φ.symm x‖ = ‖x‖ := fun x => by rw [← hφ, RingEquiv.apply_symm_apply]
  set h' := Matrix.GeneralLinearGroup.map φ.toRingHom h with hh'
  obtain ⟨k, a, ha, u, hu, hu1, hg⟩ := exists_KAN (h'⁻¹)
  set kU : GL (Fin n) 𝕜 := Unitary.toUnits k with hkU
  have hkU_val : (kU : Matrix (Fin n) (Fin n) 𝕜) = (k : Matrix (Fin n) (Fin n) 𝕜) := rfl
  set b'' : GL (Fin n) 𝕜 := h' * kU with hb''

  set Du : Matrix (Fin n) (Fin n) 𝕜 := (Matrix.diagonal fun i => ((a i : ℝ) : 𝕜)) * u with hDu
  have hleft : (b'' : Matrix (Fin n) (Fin n) 𝕜) * Du = 1 := by
    have h1 : (h' : Matrix (Fin n) (Fin n) 𝕜) * ((h'⁻¹ : GL (Fin n) 𝕜) : Matrix (Fin n) (Fin n) 𝕜) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    rw [hg] at h1
    rw [hb'', Units.val_mul, hkU_val, hDu]
    simpa only [Matrix.mul_assoc] using h1
  have hDu_upper : Du.IsUpperTriangular :=
    (Matrix.blockTriangular_diagonal _).mul hu
  have hinv : (b'' : Matrix (Fin n) (Fin n) 𝕜) = Du⁻¹ :=
    (Matrix.inv_eq_left_inv hleft).symm
  let _ : Invertible Du := ⟨(b'' : Matrix (Fin n) (Fin n) 𝕜), hleft, mul_eq_one_comm.1 hleft⟩
  have hb''_upper : (b'' : Matrix (Fin n) (Fin n) 𝕜).IsUpperTriangular := by
    rw [hinv]
    exact Matrix.blockTriangular_inv_of_blockTriangular hDu_upper
  refine ⟨Matrix.GeneralLinearGroup.map φ.symm.toRingHom b'', ?_,
    Matrix.GeneralLinearGroup.map φ.symm.toRingHom kU⁻¹, ?_, ?_⟩
  · intro i j hij
    change φ.symm ((b'' : Matrix (Fin n) (Fin n) 𝕜) i j) = 0
    rw [hb''_upper hij, map_zero]
  · intro y
    have hk' : ((kU⁻¹ : GL (Fin n) 𝕜) : Matrix (Fin n) (Fin n) 𝕜) ∈ unitaryGroup (Fin n) 𝕜 := by
      have : ((kU⁻¹ : GL (Fin n) 𝕜) : Matrix (Fin n) (Fin n) 𝕜) = ((k⁻¹ : unitaryGroup (Fin n) 𝕜) :
          Matrix (Fin n) (Fin n) 𝕜) := by
        rw [hkU, ← map_inv]
        rfl
      rw [this]
      exact (k⁻¹).2
    rw [← euclidNorm_map φ.toRingHom hφ, ← euclidNorm_map φ.toRingHom hφ y]
    have : (fun i => φ.toRingHom ((y ᵥ* ((Matrix.GeneralLinearGroup.map φ.symm.toRingHom kU⁻¹ :
        GL (Fin n) E) : Matrix (Fin n) (Fin n) E)) i)) =
        (fun i => φ.toRingHom (y i)) ᵥ* ((kU⁻¹ : GL (Fin n) 𝕜) : Matrix (Fin n) (Fin n) 𝕜) := by
      ext j
      simp [vecMul, dotProduct, map_sum, map_mul, Matrix.GeneralLinearGroup.map]
    rw [this, euclidNorm_vecMul_unitary hk']
  · rw [← map_mul, hb'', mul_assoc, mul_inv_cancel, mul_one, hh']
    ext i j
    simp [Matrix.GeneralLinearGroup.map]

end Transport

variable {K : Type*} [Field K] {n : ℕ}

def archCompact (w : InfinitePlace K) : Subgroup (GL (Fin n) w.Completion) where
  carrier := {k | ∀ y : Fin n → w.Completion,
    euclidNorm (y ᵥ* (k : Matrix (Fin n) (Fin n) w.Completion)) = euclidNorm y}
  one_mem' y := by simp
  mul_mem' {a b} ha hb y := by
    simp only [Set.mem_ofPred_eq] at ha hb ⊢
    rw [Units.val_mul, ← vecMul_vecMul, hb, ha]
  inv_mem' {k} hk y := by
    simp only [Set.mem_ofPred_eq] at hk ⊢
    have := hk (y ᵥ* ((k⁻¹ : GL (Fin n) w.Completion) : Matrix (Fin n) (Fin n) w.Completion))
    rw [vecMul_vecMul, ← Units.val_mul, inv_mul_cancel, Units.val_one, vecMul_one] at this
    exact this.symm

theorem mem_archCompact {w : InfinitePlace K} {k : GL (Fin n) w.Completion} :
    k ∈ archCompact w ↔ ∀ y : Fin n → w.Completion,
      euclidNorm (y ᵥ* (k : Matrix (Fin n) (Fin n) w.Completion)) = euclidNorm y :=
  Iff.rfl

theorem norm_apply_le_one_of_mem_archCompact {w : InfinitePlace K} {k : GL (Fin n) w.Completion}
    (hk : k ∈ archCompact w) (i j : Fin n) : ‖k i j‖ ≤ 1 := by
  classical
  have h := hk (Pi.single i 1)
  rw [single_one_vecMul] at h
  have h1 : euclidNorm (Pi.single i (1 : w.Completion)) = 1 := by
    rw [euclidNorm, Finset.sum_eq_single i (fun j _ hj => by simp [Pi.single_eq_of_ne hj])
      (by simp)]
    simp only [Pi.single_eq_same, norm_one, one_pow, Real.sqrt_one]
  calc ‖k i j‖ = ‖(k : Matrix (Fin n) (Fin n) w.Completion).row i j‖ := rfl
    _ ≤ euclidNorm ((k : Matrix (Fin n) (Fin n) w.Completion).row i) := norm_le_euclidNorm _ j
    _ = 1 := by rw [← h1, ← h]

theorem isCompact_archCompact (w : InfinitePlace K) :
    IsCompact (archCompact (n := n) w : Set (GL (Fin n) w.Completion)) := by
  set T : Set (Matrix (Fin n) (Fin n) w.Completion) := Set.pi univ fun _ => Set.pi univ fun _ =>
    Metric.closedBall (0 : w.Completion) 1 with hT
  have hTc : IsCompact T := isCompact_univ_pi fun _ => isCompact_univ_pi fun _ =>
    isCompact_closedBall _ _
  have hbig : IsCompact (Units.embedProduct (Matrix (Fin n) (Fin n) w.Completion) ⁻¹'
      (T ×ˢ (MulOpposite.opHomeomorph.symm ⁻¹' T))) :=
    Units.isClosedEmbedding_embedProduct.isCompact_preimage
      (hTc.prod (MulOpposite.opHomeomorph.symm.isCompact_preimage.2 hTc))
  refine hbig.of_isClosed_subset ?_ ?_
  · have : (archCompact (n := n) w : Set (GL (Fin n) w.Completion)) = ⋂ y : Fin n → w.Completion,
        {k : GL (Fin n) w.Completion |
          euclidNorm (y ᵥ* (k : Matrix (Fin n) (Fin n) w.Completion)) = euclidNorm y} := by
      ext k
      simp [mem_archCompact]
    rw [this]
    exact isClosed_iInter fun y => isClosed_eq
      (continuous_euclidNorm.comp ((continuous_const.matrix_vecMul Units.continuous_val)))
      continuous_const
  · intro k hk
    refine ⟨fun i _ j _ => ?_, fun i _ j _ => ?_⟩
    · simpa using norm_apply_le_one_of_mem_archCompact hk i j
    · simpa using norm_apply_le_one_of_mem_archCompact ((archCompact w).inv_mem hk) i j

theorem exists_upper_mul_archCompact (w : InfinitePlace K) (h : GL (Fin n) w.Completion) :
    ∃ b : GL (Fin n) w.Completion, (b : Matrix (Fin n) (Fin n) w.Completion).IsUpperTriangular ∧
      ∃ k ∈ archCompact w, h = b * k := by
  by_cases hw : w.IsReal
  · exact exists_upper_mul_of_ringEquiv (InfinitePlace.Completion.ringEquivRealOfIsReal hw)
      (fun x => (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hw).norm_map_of_map_zero
        (map_zero _) x) h
  · have hc := InfinitePlace.not_isReal_iff_isComplex.1 hw
    exact exists_upper_mul_of_ringEquiv (InfinitePlace.Completion.ringEquivComplexOfIsComplex hc)
      (fun x => (InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero
        (map_zero _) x) h

variable [NumberField K]

omit [NumberField K] in
theorem exists_upper_mul_archCompact' (w : InfinitePlace K) (h : GL (Fin n) w.Completion) :
    ∃ p : GL (Fin n) w.Completion × GL (Fin n) w.Completion,
      (p.1 : Matrix (Fin n) (Fin n) w.Completion).IsUpperTriangular ∧ p.2 ∈ archCompact w ∧
        h = p.1 * p.2 := by
  obtain ⟨b, hb, k, hk, rfl⟩ := exists_upper_mul_archCompact w h
  exact ⟨(b, k), hb, hk, rfl⟩

@[simp] theorem infAt_one (w : InfinitePlace K) : infAt w (1 : AdelicGLn.AdelicGL K n) = 1 := by
  simp [infAt]

@[simp] theorem finAt_one (v : HeightOneSpectrum (𝓞 K)) :
    finAt v (1 : AdelicGLn.AdelicGL K n) = 1 := by
  simp [finAt]

theorem infAt_inv (w : InfinitePlace K) (g : AdelicGLn.AdelicGL K n) :
    infAt w g⁻¹ = (infAt w g)⁻¹ := by
  simp [infAt, map_inv]

theorem finAt_inv (v : HeightOneSpectrum (𝓞 K)) (g : AdelicGLn.AdelicGL K n) :
    finAt v g⁻¹ = (finAt v g)⁻¹ := by
  simp [finAt, map_inv, RestrictedProduct.inv_apply]

def maxCompact : Subgroup (AdelicGLn.AdelicGL K n) where
  carrier := {k | (∀ w, infAt w k ∈ archCompact w) ∧
    ∀ v, finAt v k ∈ GLnLocal.integralGL (v.adicCompletion K) n}
  one_mem' := ⟨fun w => by rw [infAt_one]; exact one_mem _,
    fun v => by rw [finAt_one]; exact one_mem _⟩
  mul_mem' {a b} ha hb := ⟨fun w => by rw [infAt_mul]; exact mul_mem (ha.1 w) (hb.1 w),
    fun v => by rw [finAt_mul]; exact mul_mem (ha.2 v) (hb.2 v)⟩
  inv_mem' {k} hk := ⟨fun w => by rw [infAt_inv]; exact inv_mem (hk.1 w),
    fun v => by rw [finAt_inv]; exact inv_mem (hk.2 v)⟩

theorem mem_maxCompact {k : AdelicGLn.AdelicGL K n} :
    k ∈ maxCompact ↔ (∀ w, infAt w k ∈ archCompact w) ∧
      ∀ v, finAt v k ∈ GLnLocal.integralGL (v.adicCompletion K) n :=
  Iff.rfl

theorem isCompact_maxCompact :
    IsCompact (maxCompact (K := K) (n := n) : Set (AdelicGLn.AdelicGL K n)) := by
  have h : (maxCompact (K := K) (n := n) : Set (AdelicGLn.AdelicGL K n)) =
      (AdelicGLn.prodEquiv K n) ⁻¹' (((AdelicGLn.infiniteEquiv K n) ⁻¹'
        (Set.univ.pi fun w : InfinitePlace K =>
          (archCompact (n := n) w : Set (GL (Fin n) w.Completion)))) ×ˢ
        (AdelicGLn.integralFiniteGL K n : Set (AdelicGLn.FiniteAdelicGL K n))) := by
    ext k
    simp only [SetLike.mem_coe, mem_maxCompact, Set.mem_preimage, Set.mem_prod, Set.mem_pi,
      Set.mem_univ, true_implies, AdelicGLn.mem_integralFiniteGL_iff_forall]
    rfl
  rw [h]
  exact (AdelicGLn.prodEquiv K n).toHomeomorph.isCompact_preimage.2
    (((AdelicGLn.infiniteEquiv K n).toHomeomorph.isCompact_preimage.2
      (isCompact_univ_pi fun w => isCompact_archCompact w)).prod
      (AdelicGLn.isCompact_integralFiniteGL K n))

def adelicBorel : Subgroup (AdelicGLn.AdelicGL K n) where
  carrier := {b | (b : Matrix (Fin n) (Fin n) 𝔸[K]).IsUpperTriangular}
  one_mem' := Matrix.blockTriangular_one
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq, Units.val_mul] at ha hb ⊢
    exact ha.mul hb
  inv_mem' {b} hb := by
    simp only [Set.mem_ofPred_eq] at hb ⊢
    rw [Matrix.coe_units_inv]
    exact Matrix.blockTriangular_inv_of_blockTriangular hb

theorem mem_adelicBorel {b : AdelicGLn.AdelicGL K n} :
    b ∈ adelicBorel ↔ (b : Matrix (Fin n) (Fin n) 𝔸[K]).IsUpperTriangular :=
  Iff.rfl

theorem isUnit_apply_self_of_mem_adelicBorel {b : AdelicGLn.AdelicGL K n} (hb : b ∈ adelicBorel)
    (i : Fin n) : IsUnit ((b : Matrix (Fin n) (Fin n) 𝔸[K]) i i) := by
  have hdet : IsUnit (b : Matrix (Fin n) (Fin n) 𝔸[K]).det :=
    (Matrix.isUnit_iff_isUnit_det _).1 b.isUnit
  rw [Matrix.det_of_isUpperTriangular hb] at hdet
  exact isUnit_of_dvd_unit
    (Finset.dvd_prod_of_mem (fun j => (b : Matrix (Fin n) (Fin n) 𝔸[K]) j j) (Finset.mem_univ i)) hdet

theorem adele_ext {a b : 𝔸[K]} (h1 : ∀ w : InfinitePlace K, a.1 w = b.1 w)
    (h2 : ∀ v : HeightOneSpectrum (𝓞 K), a.2 v = b.2 v) : a = b :=
  Prod.ext (funext h1) (RestrictedProduct.ext _ _ h2)

theorem adelicGL_ext {g h : AdelicGLn.AdelicGL K n} (h1 : ∀ w, infAt w g = infAt w h)
    (h2 : ∀ v, finAt v g = finAt v h) : g = h := by
  refine (AdelicGLn.restrictedProductEquiv K n).injective (Prod.ext (funext h1) ?_)
  exact RestrictedProduct.ext _ _ h2

theorem exists_adelicBorel_mul_maxCompact (g : AdelicGLn.AdelicGL K n) :
    ∃ b ∈ adelicBorel, ∃ k ∈ maxCompact, g = b * k := by
  classical

  choose pw hpw using fun w : InfinitePlace K => exists_upper_mul_archCompact' w (infAt w g)
  have hloc : ∀ v : HeightOneSpectrum (𝓞 K), ∃ p : GL (Fin n) (v.adicCompletion K) ×
      GL (Fin n) (v.adicCompletion K), p.1 ∈ Iwasawa.borel (v.adicCompletion K) n ∧
      p.2 ∈ GLnLocal.integralGL (v.adicCompletion K) n ∧ finAt v g = p.1 * p.2 ∧
      (finAt v g ∈ GLnLocal.integralGL (v.adicCompletion K) n → p.1 = 1) := by
    intro v
    by_cases hv : finAt v g ∈ GLnLocal.integralGL (v.adicCompletion K) n
    · exact ⟨(1, finAt v g), one_mem _, hv, (one_mul _).symm, fun _ => rfl⟩
    · obtain ⟨b, hb, k, hk, he⟩ := Iwasawa.exists_borel_mul_integralGL _ n (finAt v g)
      exact ⟨(b, k), hb, hk, he, fun h => absurd h hv⟩
  choose pv hpv using hloc

  let bX : (Π w : InfinitePlace K, GL (Fin n) w.Completion) ×
      Πʳ v : HeightOneSpectrum (𝓞 K),
        [GL (Fin n) (v.adicCompletion K), GLnLocal.integralGL (v.adicCompletion K) n] :=
    (fun w => (pw w).1, ⟨fun v => (pv v).1, by
      filter_upwards [AdelicGLn.eventually_mem_integralGL K n g] with v hv
      rw [(hpv v).2.2.2 hv]
      exact one_mem _⟩)
  let kX : (Π w : InfinitePlace K, GL (Fin n) w.Completion) ×
      Πʳ v : HeightOneSpectrum (𝓞 K),
        [GL (Fin n) (v.adicCompletion K), GLnLocal.integralGL (v.adicCompletion K) n] :=
    (fun w => (pw w).2, ⟨fun v => (pv v).2, Filter.Eventually.of_forall fun v => (hpv v).2.1⟩)
  set b := (AdelicGLn.restrictedProductEquiv K n).symm bX with hb
  set k := (AdelicGLn.restrictedProductEquiv K n).symm kX with hk
  have hbw : ∀ w, infAt w b = (pw w).1 := fun w => by
    simp [infAt, hb, bX]
  have hbv : ∀ v, finAt v b = (pv v).1 := fun v => by
    simp only [finAt, hb, ContinuousMulEquiv.apply_symm_apply, bX]
    rfl
  have hkw : ∀ w, infAt w k = (pw w).2 := fun w => by
    simp [infAt, hk, kX]
  have hkv : ∀ v, finAt v k = (pv v).2 := fun v => by
    simp only [finAt, hk, ContinuousMulEquiv.apply_symm_apply, kX]
    rfl
  refine ⟨b, ?_, k, ⟨fun w => hkw w ▸ (hpw w).2.1, fun v => hkv v ▸ (hpv v).2.1⟩, ?_⟩
  · intro i j hij
    refine adele_ext (fun w => ?_) (fun v => ?_)
    · have h := (hpw w).1 hij
      rw [← hbw w] at h
      exact h
    · have h := (Iwasawa.mem_borel _ n).1 (hpv v).1 hij
      rw [← hbv v] at h
      exact h
  · refine adelicGL_ext (fun w => ?_) (fun v => ?_)
    · rw [infAt_mul, hbw, hkw]
      exact (hpw w).2.2
    · rw [finAt_mul, hbv, hkv]
      exact (hpv v).2.2.1

theorem adelicNorm_vecMul_maxCompact (y : Fin n → 𝔸[K]) {k : AdelicGLn.AdelicGL K n}
    (hk : k ∈ maxCompact) :
    adelicNorm (y ᵥ* (k : Matrix (Fin n) (Fin n) 𝔸[K])) = adelicNorm y := by
  rw [adelicNorm, adelicNorm]
  congr 1
  · refine Finset.prod_congr rfl fun w _ => ?_
    rw [infComp_vecMul_GL, hk.1 w]
  · refine finprod_congr fun v => ?_
    rw [finComp_vecMul_GL, norm_vecMul_integralGL v (hk.2 v)]

theorem height_mul_maxCompact (g : AdelicGLn.AdelicGL K n) {k : AdelicGLn.AdelicGL K n}
    (hk : k ∈ maxCompact) (x : Fin n → K) : height (g * k) x = height g x := by
  rw [height, height, Units.val_mul, ← vecMul_vecMul, adelicNorm_vecMul_maxCompact _ hk]

end Reduction

end

end GroundTheory.Automorphic
