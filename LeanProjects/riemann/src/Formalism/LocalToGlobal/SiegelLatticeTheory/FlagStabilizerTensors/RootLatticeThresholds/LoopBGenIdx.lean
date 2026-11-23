import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.LatticeGluingRadicals
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.InvertibleIdealIndex.SubmodulePiToAddSubgroup
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.GramDeterminantOfGenericIndex

noncomputable section

open scoped Classical nonZeroDivisors Pointwise
open NumberField Module Formalism.BasicNotions Formalism.MainNotions.S.Lat Formalism.MainNotions.LatticeGluingRadicals

namespace Formalism.L2.SG.Pf.LoopBGenIdx

section Pi

variable {E : Type} [Field E] [NumberField E] {e : ℕ}

def piF (J : Fin e → FractionalIdeal (𝓞 E)⁰ E) : Submodule (𝓞 E) (Fin e → E) :=
  Submodule.pi Set.univ (fun j => (J j : Submodule (𝓞 E) E))

theorem mem_piF {J : Fin e → FractionalIdeal (𝓞 E)⁰ E} {c : Fin e → E} : c ∈ piF J ↔ ∀ j, c j ∈ J j := by
  simp [piF, Submodule.mem_pi]

theorem piF_mono {J K : Fin e → FractionalIdeal (𝓞 E)⁰ E} (h : ∀ j, J j ≤ K j) : piF J ≤ piF K := fun c hc => mem_piF.2 (fun j => h j (mem_piF.1 hc j))

theorem jLat_piF_one : j_Lat (piF (fun _ : Fin e => (1 : FractionalIdeal (𝓞 E)⁰ E))) := by
  have hr : piF (fun _ : Fin e => (1 : FractionalIdeal (𝓞 E)⁰ E)) =
      LinearMap.range ((Algebra.linearMap (𝓞 E) E).compLeft (Fin e)) := by
    ext c
    rw [mem_piF, LinearMap.mem_range]
    constructor
    · intro h
      choose o ho using fun j => (FractionalIdeal.mem_one_iff _).1 (h j)
      exact ⟨o, funext fun j => ho j⟩
    · rintro ⟨o, rfl⟩ j
      exact (FractionalIdeal.mem_one_iff _).2 ⟨o j, rfl⟩
  refine ⟨?_, ?_⟩
  · rw [hr, LinearMap.range_eq_map]
    exact (Module.Finite.fg_top).map _
  · rw [eq_top_iff, ← (Pi.basisFun E (Fin e)).span_eq, Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    apply Submodule.subset_span
    rw [SetLike.mem_coe, mem_piF]
    intro i
    refine (FractionalIdeal.mem_one_iff _).2 ⟨if i = j then 1 else 0, ?_⟩
    rw [Pi.basisFun_apply, Pi.single_apply]
    split_ifs <;> simp

def diagC (a : Fin e → E) (ha : ∀ j, a j ≠ 0) : (Fin e → E) ≃ₗ[E] (Fin e → E) :=
  LinearEquiv.ofLinear (Matrix.toLin' (Matrix.diagonal a)) (Matrix.toLin' (Matrix.diagonal fun j => (a j)⁻¹))
    (by
      rw [← Matrix.toLin'_mul, Matrix.diagonal_mul_diagonal, ← Matrix.toLin'_one]
      congr 1
      ext i j
      simp [Matrix.diagonal_apply, Matrix.one_apply, mul_inv_cancel₀ (ha _)])
    (by
      rw [← Matrix.toLin'_mul, Matrix.diagonal_mul_diagonal, ← Matrix.toLin'_one]
      congr 1
      ext i j
      simp [Matrix.diagonal_apply, Matrix.one_apply, inv_mul_cancel₀ (ha _)])

theorem diagC_apply (a : Fin e → E) (ha : ∀ j, a j ≠ 0) (c : Fin e → E) (j : Fin e) :
    diagC a ha c j = a j * c j := by
  simp [diagC, Matrix.toLin'_apply, Matrix.mulVec_diagonal]

theorem det_diagC (a : Fin e → E) (ha : ∀ j, a j ≠ 0) :
    LinearMap.det ((diagC a ha : (Fin e → E) ≃ₗ[E] (Fin e → E)) : (Fin e → E) →ₗ[E] (Fin e → E)) = ∏ j, a j := by
  simp [diagC, LinearMap.det_toLin', Matrix.det_diagonal]

theorem den_ne (J : FractionalIdeal (𝓞 E)⁰ E) : algebraMap (𝓞 E) E (J.den : 𝓞 E) ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (J.den).2

theorem mem_num_iff (J : FractionalIdeal (𝓞 E)⁰ E) (y : E) :
    y ∈ ((J.num : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E) ↔
      ∃ c ∈ J, algebraMap (𝓞 E) E (J.den : 𝓞 E) * c = y := by
  rw [← FractionalIdeal.mem_coe, FractionalIdeal.coe_coeIdeal, IsLocalization.coeSubmodule,
    ← FractionalIdeal.den_mul_self_eq_num]
  change y ∈ (J.den : 𝓞 E) • (J : Submodule (𝓞 E) E) ↔ _
  rw [Submodule.mem_smul_pointwise_iff_exists]
  simp only [Algebra.smul_def, FractionalIdeal.mem_coe]

theorem map_diag_piF (J : Fin e → FractionalIdeal (𝓞 E)⁰ E) :
    (piF J).map (((diagC (fun j => algebraMap (𝓞 E) E ((J j).den : 𝓞 E)) fun j => den_ne (J j) :
        (Fin e → E) ≃ₗ[E] (Fin e → E)) : (Fin e → E) →ₗ[E] (Fin e → E)).restrictScalars (𝓞 E)) =
      piF (fun j => (((J j).num : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E)) := by
  ext y
  rw [Submodule.mem_map, mem_piF]
  constructor
  · rintro ⟨c, hc, rfl⟩ j
    exact (mem_num_iff _ _).2 ⟨c j, mem_piF.1 hc j, by
      rw [LinearMap.restrictScalars_apply, LinearEquiv.coe_coe, diagC_apply]⟩
  · intro hy
    choose c hc hcy using fun j => (mem_num_iff _ _).1 (hy j)
    refine ⟨c, mem_piF.2 hc, funext fun j => ?_⟩
    rw [LinearMap.restrictScalars_apply, LinearEquiv.coe_coe, diagC_apply, hcy]

theorem relIndex_piF (K : Fin e → Ideal (𝓞 E)) :
    (piF (fun j => (K j : FractionalIdeal (𝓞 E)⁰ E))).toAddSubgroup.relIndex
      (piF (fun _ : Fin e => (1 : FractionalIdeal (𝓞 E)⁰ E))).toAddSubgroup = ∏ j, Ideal.absNorm (K j) := by
  have h1 : (1 : FractionalIdeal (𝓞 E)⁰ E) = ((⊤ : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E) := by
    simp
  unfold piF
  rw [PI.InvIdealIdxPiWork.submodule_pi_toAddSubgroup, PI.InvIdealIdxPiWork.submodule_pi_toAddSubgroup, h1]
  exact PI.InvIdealIdxPiWork.relIndex_pi_idS K

theorem fg_piF (J : Fin e → FractionalIdeal (𝓞 E)⁰ E) : (piF J).FG := by
  set C := diagC (fun j => algebraMap (𝓞 E) E ((J j).den : 𝓞 E)) fun j => den_ne (J j)
  have hm := map_diag_piF J
  have hfg : (piF (fun j => (((J j).num : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E))).FG :=
    g_fg_le jLat_piF_one.1 (piF_mono fun _ => FractionalIdeal.coeIdeal_le_one)
  rw [← hm] at hfg
  have h2 := hfg.map (((C.symm : (Fin e → E) ≃ₗ[E] (Fin e → E)) : (Fin e → E) →ₗ[E] (Fin e → E)).restrictScalars (𝓞 E))
  rwa [← Submodule.map_comp, show ((((C.symm : (Fin e → E) ≃ₗ[E] (Fin e → E)) : (Fin e → E) →ₗ[E] (Fin e → E)).restrictScalars
      (𝓞 E)).comp (((C : (Fin e → E) ≃ₗ[E] (Fin e → E)) : (Fin e → E) →ₗ[E] (Fin e → E)).restrictScalars (𝓞 E))) =
      LinearMap.id by ext x; simp, Submodule.map_id] at h2

theorem jdel_piF {J : Fin e → FractionalIdeal (𝓞 E)⁰ E} (hJ : j_Lat (piF J)) :
    j_del (piF J) = (∏ j, FractionalIdeal.absNorm (J j)) *
      j_del (piF (fun _ : Fin e => (1 : FractionalIdeal (𝓞 E)⁰ E))) := by
  set a : Fin e → E := fun j => algebraMap (𝓞 E) E ((J j).den : 𝓞 E) with ha
  set C := diagC a fun j => den_ne (J j)
  have hm := map_diag_piF J
  have hK : j_Lat (piF (fun j => (((J j).num : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E))) := by
    rw [← hm]; exact j_Lat_map hJ C
  have e1 := j_del_map hJ C
  rw [hm, det_diagC] at e1
  have e2 := j_del_nested jLat_piF_one hK (piF_mono fun _ => FractionalIdeal.coeIdeal_le_one)
  rw [relIndex_piF, e1] at e2
  have hN : ∀ j, FractionalIdeal.absNorm (J j) = (Ideal.absNorm (J j).num : ℚ) / |Algebra.norm ℚ (a j)| := by
    intro j
    rw [FractionalIdeal.absNorm_eq, ha]
    congr 1
    rw [← Algebra.coe_norm_int]
    push_cast
    rfl
  have hpos : ∀ j, 0 < |Algebra.norm ℚ (a j)| := fun j =>
    abs_pos.2 (Algebra.norm_ne_zero_iff.2 (den_ne (J j)))
  rw [map_prod, Finset.abs_prod] at e2
  push_cast at e2
  simp_rw [hN]
  rw [Finset.prod_div_distrib]
  have hP : 0 < ∏ j, |Algebra.norm ℚ (a j)| := Finset.prod_pos fun j _ => hpos j
  rw [div_mul_eq_mul_div, eq_div_iff hP.ne']
  linear_combination e2

end Pi

section Dual

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {e : ℕ}

def psL (u : Fin e → S.V) (I : Fin e → FractionalIdeal (𝓞 E)⁰ E) : Submodule (𝓞 E) S.V :=
  Submodule.span (𝓞 E) {y | ∃ j, ∃ x ∈ I j, y = x • u j}

def gramU (u : Fin e → S.V) : Matrix (Fin e) (Fin e) E := Matrix.of fun i j => S.hT (u i) (u j)

theorem psL_eq_map (u : Fin e → S.V) (I : Fin e → FractionalIdeal (𝓞 E)⁰ E) :
    psL u I = (piF I).map (j_iotaO u) := by
  apply le_antisymm
  · rw [psL, Submodule.span_le]
    rintro _ ⟨j, x, hx, rfl⟩
    refine ⟨Pi.single j x, mem_piF.2 fun i => ?_, ?_⟩
    · rw [Pi.single_apply]
      split_ifs with h
      · subst h; exact hx
      · exact FractionalIdeal.mem_coe.1 ((I i : Submodule (𝓞 E) E).zero_mem)
    · show j_iota u (Pi.single j x) = x • u j
      rw [j_iota_apply]
      simp [Pi.single_apply]
  · rintro _ ⟨c, hc, rfl⟩
    show j_iota u c ∈ psL u I
    rw [j_iota_apply]
    exact Submodule.sum_mem _ fun i _ => Submodule.subset_span ⟨i, c i, mem_piF.1 hc i, rfl⟩

theorem coords_psL {u : Fin e → S.V} (hu : LinearIndependent E u) (I : Fin e → FractionalIdeal (𝓞 E)⁰ E) :
    (psL u I).comap (j_iotaO u) = piF I := by
  rw [psL_eq_map]
  exact Submodule.comap_map_eq_of_injective (f := j_iotaO u) (j_iota_inj hu) _

theorem exists_ne_mem {J : FractionalIdeal (𝓞 E)⁰ E} (hJ : J ≠ 0) : ∃ x ∈ J, x ≠ 0 := by
  by_contra h
  push_neg at h
  apply hJ
  ext x
  constructor
  · intro hx
    rw [h x hx]
    exact (FractionalIdeal.mem_zero_iff _).mpr rfl
  · intro hx
    rw [FractionalIdeal.mem_zero_iff] at hx
    rw [hx]
    exact (J : Submodule (𝓞 E) E).zero_mem

theorem spanE_psL (u : Fin e → S.V) {I : Fin e → FractionalIdeal (𝓞 E)⁰ E} (hI : ∀ j, I j ≠ 0) :
    spanE S (psL u I) = Submodule.span E (Set.range u) := by
  apply le_antisymm
  · have : psL u I ≤ (Submodule.span E (Set.range u)).restrictScalars (𝓞 E) := by
      rw [psL, Submodule.span_le]
      rintro _ ⟨j, x, -, rfl⟩
      exact Submodule.smul_mem _ x (Submodule.subset_span ⟨j, rfl⟩)
    rw [spanE, Submodule.span_le]
    exact fun y hy => this hy
  · rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    obtain ⟨x, hx, hx0⟩ := exists_ne_mem (hI j)
    have h1 : x • u j ∈ spanE S (psL u I) := Submodule.subset_span (Submodule.subset_span ⟨j, x, hx, rfl⟩)
    have h2 := Submodule.smul_mem _ x⁻¹ h1
    rwa [smul_smul, inv_mul_cancel₀ hx0, one_smul] at h2

theorem hT_iota (u : Fin e → S.V) (v : S.V) (c : Fin e → E) :
    S.hT v (j_iota u c) = ∑ j, c j * S.hT v (u j) := by
  simp [j_iota, Fintype.linearCombination_apply, map_sum, map_smul]

theorem hT_smul_left (x : E) (v w : S.V) : S.hT (x • v) w = star x * S.hT v w := by
  simp [LinearMap.map_smulₛₗ₂]
  left
  rfl

theorem hT_iota_gram (u : Fin e → S.V) (c : Fin e → E) (i : Fin e) :
    S.hT (u i) (j_iota u c) = (gramU u).mulVec c i := by
  rw [hT_iota]
  simp [gramU, Matrix.mulVec, dotProduct, mul_comm]

theorem one_mul_mem {a b : E} (ha : a ∈ (1 : Submodule (𝓞 E) E)) (hb : b ∈ (1 : Submodule (𝓞 E) E)) :
    a * b ∈ (1 : Submodule (𝓞 E) E) := by
  simpa using Submodule.mul_mem_mul ha hb

theorem mem_one_frac {a : E} : a ∈ (1 : FractionalIdeal (𝓞 E)⁰ E) ↔ a ∈ (1 : Submodule (𝓞 E) E) := by
  rw [FractionalIdeal.mem_one_iff, Submodule.mem_one]

theorem mem_dual_psL (u : Fin e → S.V) {I : Fin e → FractionalIdeal (𝓞 E)⁰ E} (hI : ∀ j, I j ≠ 0)
    (hs : ∀ j, ∀ x ∈ I j, star x ∈ I j) (c : Fin e → E) :
    j_iota u c ∈ Formalism.HermitianLatticesTheory.dual S.hT (psL u I) ↔ ∀ i, (gramU u).mulVec c i ∈ (I i)⁻¹ := by
  rw [i_mem_dual]
  constructor
  · intro h i
    rw [FractionalIdeal.mem_inv_iff (hI i)]
    intro y hy
    have h1 := h (star y • u i) (Submodule.subset_span ⟨i, star y, hs i y hy, rfl⟩)
    rw [hT_smul_left, star_star, hT_iota_gram] at h1
    rw [mem_one_frac, mul_comm]
    exact h1
  · intro h y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨j, x, hx, rfl⟩ := hy
      rw [hT_smul_left, hT_iota_gram, mul_comm]
      have := (FractionalIdeal.mem_inv_iff (hI j)).1 (h j) (star x) (hs j x hx)
      exact mem_one_frac.1 this
    | zero => simp
    | add y z _ _ hy hz =>
      rw [map_add, LinearMap.add_apply]
      exact Submodule.add_mem _ hy hz
    | smul o y _ hy =>
      rw [← IsScalarTower.algebraMap_smul E o y, hT_smul_left]
      obtain ⟨o', ho'⟩ := i_star_int o
      refine one_mul_mem ?_ hy
      rw [← ho']
      exact Submodule.mem_one.2 ⟨o', rfl⟩

def gramO (u : Fin e → S.V) : (Fin e → E) →ₗ[𝓞 E] (Fin e → E) := (Matrix.toLin' (gramU u)).restrictScalars (𝓞 E)

theorem coords_dual {u : Fin e → S.V} {I : Fin e → FractionalIdeal (𝓞 E)⁰ E}
    (hI : ∀ j, I j ≠ 0) (hs : ∀ j, ∀ x ∈ I j, star x ∈ I j) :
    (dualIn S (psL u I)).comap (j_iotaO u) = (piF fun j => (I j)⁻¹).comap (gramO u) := by
  ext c
  rw [Submodule.mem_comap, Submodule.mem_comap]
  show j_iota u c ∈ dualInH S.hT (psL u I) ↔ _
  rw [dualInH, Submodule.mem_inf, mem_piF]
  have hsp : j_iota u c ∈ (Submodule.span E (psL u I : Set S.V)).restrictScalars (𝓞 E) := by
    show j_iota u c ∈ spanE S (psL u I)
    rw [spanE_psL u hI, ← j_iota_range]
    exact ⟨c, rfl⟩
  simp only [hsp, and_true, gramO, LinearMap.restrictScalars_apply, Matrix.toLin'_apply]
  exact mem_dual_psL u hI hs c

theorem nondeg_span {u : Fin e → S.V} (hH : (gramU u).det ≠ 0) :
    Submodule.span E (Set.range u) ⊓ orth S (Submodule.span E (Set.range u)) = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hx, hxo⟩
  rw [← j_iota_range] at hx
  obtain ⟨c, rfl⟩ := hx
  have hc : (gramU u).mulVec c = 0 := funext fun i => by
    have h1 := Submodule.mem_iInf _ |>.1 hxo (u i)
    have h2 := Submodule.mem_iInf _ |>.1 h1 (Submodule.subset_span ⟨i, rfl⟩)
    rw [LinearMap.mem_ker, hT_iota_gram] at h2
    simpa using h2
  have : c = 0 := Matrix.eq_zero_of_mulVec_eq_zero hH hc
  subst this
  simp

def gramC (u : Fin e → S.V) (hH : (gramU u).det ≠ 0) : (Fin e → E) ≃ₗ[E] (Fin e → E) :=
  LinearEquiv.ofLinear (Matrix.toLin' (gramU u)) (Matrix.toLin' (gramU u)⁻¹)
    (by rw [← Matrix.toLin'_mul, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hH), Matrix.toLin'_one])
    (by rw [← Matrix.toLin'_mul, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hH), Matrix.toLin'_one])

theorem genIdx_psL {u : Fin e → S.V} (hu : LinearIndependent E u) {I : Fin e → FractionalIdeal (𝓞 E)⁰ E}
    (hI : ∀ j, I j ≠ 0) (hs : ∀ j, ∀ x ∈ I j, star x ∈ I j) (hH : (gramU u).det ≠ 0) :
    genIdx S (dualIn S (psL u I)) (psL u I) =
      |((Algebra.norm ℚ (gramU u).det : ℚ) : ℝ)| * ∏ j, ((FractionalIdeal.absNorm (I j) : ℚ) : ℝ) ^ 2 := by
  have hM : (psL u I).FG := by rw [psL_eq_map]; exact (fg_piF I).map _
  have hsp := spanE_psL u hI
  obtain ⟨l1, l2, hg⟩ := j_genIdx_dual hu hM hsp (by rw [hsp]; exact nondeg_span hH)
  rw [hg]
  rw [coords_psL hu] at l1 ⊢
  rw [coords_dual hI hs] at l2 ⊢
  set C := gramC u hH
  have hmap : ((piF fun j => (I j)⁻¹).comap (gramO u)).map
      (((C : (Fin e → E) ≃ₗ[E] (Fin e → E)) : (Fin e → E) →ₗ[E] (Fin e → E)).restrictScalars (𝓞 E)) =
      piF fun j => (I j)⁻¹ :=
    Submodule.map_comap_eq_of_surjective (f := gramO u) C.surjective _
  have e1 := j_del_map l2 C
  rw [hmap] at e1
  have hdet : LinearMap.det ((C : (Fin e → E) ≃ₗ[E] (Fin e → E)) : (Fin e → E) →ₗ[E] (Fin e → E)) = (gramU u).det := by
    show LinearMap.det (Matrix.toLin' (gramU u)) = _
    rw [LinearMap.det_toLin']
  rw [hdet] at e1
  have l3 : j_Lat (piF fun j => (I j)⁻¹) := by rw [← hmap]; exact j_Lat_map l2 C
  have e2 := jdel_piF l1
  have e3 := jdel_piF l3
  simp_rw [map_inv₀] at e3
  rw [Finset.prod_inv_distrib] at e3
  have hP := j_del_pos (jLat_piF_one (E := E) (e := e))
  have hn : 0 < ∏ j, FractionalIdeal.absNorm (I j) := Finset.prod_pos fun j _ =>
    lt_of_le_of_ne (FractionalIdeal.absNorm_nonneg _) (Ne.symm ((FractionalIdeal.absNorm_eq_zero_iff).not.2 (hI j)))
  have hd : 0 < |Algebra.norm ℚ (gramU u).det| := abs_pos.2 (Algebra.norm_ne_zero_iff.2 hH)
  have hB := j_del_pos l2
  have key : (j_del (piF I) : ℚ) / j_del ((piF fun j => (I j)⁻¹).comap (gramO u)) =
      |Algebra.norm ℚ (gramU u).det| * ∏ j, FractionalIdeal.absNorm (I j) ^ 2 := by
    rw [Finset.prod_pow, div_eq_iff hB.ne', e2]
    have : j_del ((piF fun j => (I j)⁻¹).comap (gramO u)) =
        (∏ j, FractionalIdeal.absNorm (I j))⁻¹ * j_del (piF (fun _ : Fin e => (1 : FractionalIdeal (𝓞 E)⁰ E))) /
          |Algebra.norm ℚ (gramU u).det| := by
      rw [eq_div_iff hd.ne', mul_comm, ← e1, e3]
    rw [this]
    field_simp
  have key' := congrArg (fun q : ℚ => (q : ℝ)) key
  push_cast at key'
  rw [← key']

end Dual

section Inst

open Formalism.MainNotions.S Formalism.L2.SG.DetUU

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem genIdxPseudo_holds : GenIdxPseudo := by
  intro D ι _ _ u I hu hI hs hH
  let σ := Fintype.equivFin ι
  have hpl : pseudoLat u I = psL (u ∘ σ.symm) (I ∘ σ.symm) := by
    unfold pseudoLat psL
    congr 1
    ext y
    constructor
    · rintro ⟨j, x, hx, rfl⟩
      exact ⟨σ j, x, by simpa using hx, by simp⟩
    · rintro ⟨j, x, hx, rfl⟩
      exact ⟨σ.symm j, x, hx, rfl⟩
  have hG : gramU (S := hS D) (u ∘ σ.symm) =
      (Matrix.of fun i j => (hS D).hT (u i) (u j)).submatrix σ.symm σ.symm := by
    ext i j
    rfl
  have hdet : (gramU (S := hS D) (u ∘ σ.symm)).det = (Matrix.of fun i j => (hS D).hT (u i) (u j)).det := by
    rw [hG, Matrix.det_submatrix_equiv_self]
  rw [hpl, genIdx_psL (I := I ∘ σ.symm) (hu.comp σ.symm σ.symm.injective) (fun j => hI _) (fun j => hs _) (by rwa [hdet]), hdet]
  congr 1
  exact Equiv.prod_comp σ.symm (fun j => ((FractionalIdeal.absNorm (I j) : ℚ) : ℝ) ^ 2)

theorem gram_determinant_relation : Formalism.L2.SG.LoopsFinal.GramDeterminantCount := gram_determinant_of_generic_index genIdxPseudo_holds

end Inst

end Formalism.L2.SG.Pf.LoopBGenIdx
