import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdeleModuleDetDiagUnitsPosIdele
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSiegelSetDiagNormOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspRapidDecaySiegelGLOfFinite
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AutomorphicFormsFiniteGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfMemWeakIn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealLieSmoothingMemSmoothAdelicFunctions
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieDerivativeRealLieSmoothingEqDensity
import Development.AbelianVarietyTheory.Definitions.Divisors.MemL2OfSmoothVector
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAddHaarMeasureVolumeLie
import GroundTheory.AutomorphicForms.ReductionFinite

noncomputable section

open NumberField Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC GroundTheory.Global GroundTheory.Global.IdeleGroup
  GroundTheory.Automorphic GroundTheory.Automorphic.Reduction
open scoped Pointwise

namespace GlobalTheory.ShortVecDecay

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

theorem continuous_pInf : Continuous (pInf E) :=
  continuous_pi fun w =>
    ((InfinitePlace.Completion.isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).continuous.comp
      (continuous_apply w)).comp continuous_fst

theorem exists_le_norm_pInf {T : Set (Af E)} (hT : IsCompact T) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x : E, x ≠ 0 → pFin E (algebraMap E (Ad E) x) ∈ T → ε ≤ ‖pInf E (algebraMap E (Ad E) x)‖ := by
  have hc : Continuous fun p : Cinf E × Af E => (((infEq E p.1, p.2) : InfiniteAdeleRing E × Af E) : Ad E) :=
    ((continuous_infEq E).comp continuous_fst).prodMk continuous_snd
  have hD := ((isCompact_closedBall (0 : Cinf E) 1).prod hT).image hc
  have hS := ((finite_setOf_algebraMap_mem (K := E) hD).inter_of_left {x | x ≠ 0}).image
    fun x => ‖pInf E (algebraMap E (Ad E) x)‖
  obtain ⟨m, M, hm, -, h⟩ := exists_pos_bounds hS.isCompact continuous_id (by
    rintro _ ⟨x, hx, rfl⟩
    exact norm_pos_iff.2 ((map_ne_zero ((pInf E).comp (algebraMap E (Ad E)))).2 hx.2))
  refine ⟨min m 1, lt_min hm one_pos, fun x hx hxT => ?_⟩
  rcases le_total ‖pInf E (algebraMap E (Ad E) x)‖ 1 with h1 | h1
  · refine (min_le_left _ _).trans (h _ ⟨x, ⟨⟨(pInf E (algebraMap E (Ad E) x), pFin E (algebraMap E (Ad E) x)),
      ⟨by simpa using h1, hxT⟩, ?_⟩, hx⟩, rfl⟩).1
    exact Prod.ext ((infEq E).apply_symm_apply _) rfl
  · exact (min_le_right _ _).trans h1

theorem exists_norm_vecMul_le {κ : Set (GA E a)} (hκ : IsCompact κ) :
    ∃ M : ℝ, 0 < M ∧ ∀ y ∈ κ, ∀ x : Fin a → Ad E,
      ‖fun i => pInf E ((x ᵥ* y.val) i)‖ ≤ M * ‖fun i => pInf E (x i)‖ := by
  have hc : Continuous fun y : GA E a => toL (y.val.map (pInf E)) :=
    (Units.continuous_val.matrix_map continuous_pInf : Continuous fun y : GA E a => y.val.map (pInf E))
  obtain ⟨B, hB⟩ := hκ.exists_bound_of_continuousOn hc.continuousOn
  refine ⟨a * |B| + 1, by positivity, fun y hy x => ?_⟩
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
  simp only [vecMul, dotProduct, map_sum, map_mul]
  refine (norm_sum_le _ _).trans ((Finset.sum_le_card_nsmul _ _ (‖fun i => pInf E (x i)‖ * |B|) fun j _ => ?_).trans ?_)
  · refine (norm_mul_le _ _).trans (mul_le_mul (norm_le_pi_norm (fun i => pInf E (x i)) j) ?_ (norm_nonneg _)
      (norm_nonneg _))
    exact (((norm_le_pi_norm (toL (y.val.map (pInf E)) j) i).trans
      (norm_le_pi_norm (toL (y.val.map (pInf E))) j)).trans (hB y hy)).trans (le_abs_self B)
  · simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    nlinarith [norm_nonneg fun i => pInf E (x i)]

omit [IsTotallyComplex E] in

theorem exists_isCompact_vecMul {κ : Set (GA E a)} (hκ : IsCompact κ) {L : Set (Fin a → Af E)} (hL : IsCompact L) :
    ∃ L' : Set (Fin a → Af E), IsCompact L' ∧ ∀ y ∈ κ, ∀ x : Fin a → Ad E,
      (fun i => pFin E (x i)) ∈ L → (fun i => pFin E ((x ᵥ* y.val) i)) ∈ L' := by
  have hc : Continuous fun p : (Fin a → Af E) × GA E a => p.1 ᵥ* p.2.val.map (pFin E) :=
    continuous_fst.matrix_vecMul ((Units.continuous_val.comp continuous_snd).matrix_map
      (continuous_snd : Continuous (pFin E)))
  refine ⟨_, (hL.prod hκ).image hc, fun y hy x hx => ⟨(_, y), ⟨hx, hy⟩, ?_⟩⟩
  funext i
  simp [vecMul, dotProduct]

theorem norm_pInf_posIdele {ρ : ℝ} (hρ : 0 < ρ) (w : InfinitePlace E) :
    ‖pInf E (posIdele (K := E) ρ hρ).val w‖ = ρ := by
  refine Eq.trans ?_ (norm_posIdele_infinite (K := E) ρ hρ w)
  exact ((InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _) _)

omit [IsTotallyComplex E] in

theorem pFin_vecMul_diag (r : Fin a → ℝ) (hr : ∀ i, 0 < r i) (x : Fin a → Ad E) :
    (fun i => pFin E ((x ᵥ* (diagUnits a fun i => posIdele (K := E) (r i) (hr i)).val) i)) = fun i => pFin E (x i) := by
  funext i
  have h : pFin E (posIdele (K := E) (r i) (hr i)).val = 1 :=
    IsDedekindDomain.FiniteAdeleRing.ext _ fun v => posIdele_finite _ _ v
  rw [coe_diagUnits, vecMul_diagonal, map_mul, h, mul_one]

theorem le_norm_vecMul_diag (r : Fin a → ℝ) (hr : ∀ i, 0 < r i) {ρ : ℝ} (hρ : 0 < ρ) (h : ∀ i, ρ ≤ r i)
    (x : Fin a → Ad E) : ρ * ‖fun i => pInf E (x i)‖ ≤
      ‖fun i => pInf E ((x ᵥ* (diagUnits a fun i => posIdele (K := E) (r i) (hr i)).val) i)‖ := by
  rw [← le_div_iff₀' hρ]
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => (pi_norm_le_iff_of_nonneg (by positivity)).2 fun w => ?_
  rw [le_div_iff₀ hρ]
  refine le_trans ?_ ((norm_le_pi_norm _ w).trans (norm_le_pi_norm
    (fun i => pInf E ((x ᵥ* (diagUnits a fun i => posIdele (K := E) (r i) (hr i)).val) i)) i))
  rw [coe_diagUnits, vecMul_diagonal, map_mul, Pi.mul_apply, norm_mul, norm_pInf_posIdele]
  exact mul_le_mul_of_nonneg_left (h i) (norm_nonneg _)

theorem exists_le_norm_vecMul {ω κ : Set (GA E a)} (hω : IsCompact ω) (hκ : IsCompact κ) {L : Set (Fin a → Af E)}
    (hL : IsCompact L) : ∃ δ : ℝ, 0 < δ ∧ ∀ b ∈ ω, ∀ k ∈ κ, ∀ (r : Fin a → ℝ) (hr : ∀ i, 0 < r i) (ρ : ℝ), 0 < ρ →
      (∀ i, ρ ≤ r i) → ∀ η : Fin a → E, η ≠ 0 → ∀ x : Fin a → Ad E,
        x = (fun j => algebraMap E (Ad E) (η j)) ᵥ* (b * (diagUnits a fun i => posIdele (K := E) (r i) (hr i)) * k).val →
        (fun i => pFin E (x i)) ∈ L → δ * ρ ≤ ‖fun i => pInf E (x i)‖ := by
  obtain ⟨M₁, hM₁, h₁⟩ := exists_norm_vecMul_le hκ.inv
  obtain ⟨M₂, hM₂, h₂⟩ := exists_norm_vecMul_le hω.inv
  obtain ⟨L₁, hL₁, g₁⟩ := exists_isCompact_vecMul hκ.inv hL
  obtain ⟨L₂, hL₂, g₂⟩ := exists_isCompact_vecMul hω.inv hL₁
  obtain ⟨ε, hε, hT⟩ := exists_le_norm_pInf (isCompact_iUnion fun i : Fin a => hL₂.image (continuous_apply i))
  refine ⟨ε / (M₁ * M₂), by positivity, fun b hb k hk r hr ρ hρ hρr η hη x hx hxL => ?_⟩
  set D := diagUnits a fun i => posIdele (K := E) (r i) (hr i) with hD
  set u₀ : Fin a → Ad E := fun j => algebraMap E (Ad E) (η j) with hu₀
  have e₂ : x ᵥ* (k⁻¹).val = (u₀ ᵥ* b.val) ᵥ* D.val := by
    rw [hx, vecMul_vecMul, vecMul_vecMul, ← Units.val_mul, ← Units.val_mul, mul_inv_cancel_right]
  have e₀ : (u₀ ᵥ* b.val) ᵥ* (b⁻¹).val = u₀ := by
    rw [vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one, vecMul_one]
  have f₂ := g₁ k⁻¹ (Set.inv_mem_inv.2 hk) x hxL
  rw [e₂, pFin_vecMul_diag] at f₂
  have f₀ := g₂ b⁻¹ (Set.inv_mem_inv.2 hb) _ f₂
  have n₂ := h₁ k⁻¹ (Set.inv_mem_inv.2 hk) x
  have n₀ := h₂ b⁻¹ (Set.inv_mem_inv.2 hb) (u₀ ᵥ* b.val)
  have n₁ := le_norm_vecMul_diag r hr hρ hρr (u₀ ᵥ* b.val)
  rw [e₀] at f₀ n₀
  rw [e₂] at n₂
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hη
  have n := (hT (η i) hi (Set.mem_iUnion.2 ⟨i, _, f₀, rfl⟩)).trans (norm_le_pi_norm (fun i => pInf E (u₀ i)) i)
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  calc ε * ρ ≤ M₂ * ‖fun i => pInf E ((u₀ ᵥ* b.val) i)‖ * ρ := mul_le_mul_of_nonneg_right (n.trans n₀) hρ.le
    _ = M₂ * (ρ * ‖fun i => pInf E ((u₀ ᵥ* b.val) i)‖) := by ring
    _ ≤ M₂ * (M₁ * ‖fun i => pInf E (x i)‖) := mul_le_mul_of_nonneg_left (n₁.trans n₂) hM₂.le
    _ = _ := by ring

def Decays (F : GA E a → ℂ) : Prop :=
  ∀ L : Set (Fin a → Af E), IsCompact L → ∀ C₀ : Set (GA E a), IsCompact C₀ → ∀ N : ℕ, ∃ C : ℝ,
    ∀ g : GA E a, ∀ c ∈ C₀, ∀ ξ : Fin a → E, ξ ≠ 0 →
      (fun i => pFin E (((fun j => algebraMap E (Ad E) (ξ j)) ᵥ* g.val) i)) ∈ L →
        ‖F (g * c)‖ ≤ C * (‖fun i => pInf E (((fun j => algebraMap E (Ad E) (ξ j)) ᵥ* g.val) i)‖ ^
          (a * Module.finrank ℚ E) / (ideleModule E (GeneralLinearGroup.det g) : ℝ)) ^ N

omit [IsTotallyComplex E] in

theorem ideleModule_det_eq_one {b : GA E a} (hb : b ∈ adelicBorel (K := E) (n := a))
    (h : ∀ i, ∃ u : IdeleGroup E, b.val i i = u ∧ (ideleModule E u : ℝ) = 1) :
    (ideleModule E (GeneralLinearGroup.det b) : ℝ) = 1 := by
  choose u hu hu1 using h
  have e : GeneralLinearGroup.det b = ∏ i, u i := by
    refine Units.ext ?_
    rw [GeneralLinearGroup.val_det_apply, det_of_isUpperTriangular (mem_adelicBorel.1 hb), Units.coe_prod]
    exact Finset.prod_congr rfl fun i _ => hu i
  rw [e, map_prod, coe_finset_prod_pos]
  exact Finset.prod_eq_one fun i _ => hu1 i

omit [IsTotallyComplex E] in

theorem ideleModule_det_rat (γ : GL (Fin a) E) : ideleModule E (GeneralLinearGroup.det (ratGL E a γ)) = 1 := by
  have h : GeneralLinearGroup.det (ratGL E a γ) = IdeleGroup.diagonal E (GeneralLinearGroup.det γ) := by
    refine Units.ext ?_
    rw [IdeleGroup.coe_diagonal, ratGL, ← det_map (algebraMap E (Ad E)) γ]
  rw [h]
  exact ideleModule_diagonal _

theorem decays_of_isCuspForm {φ : Sm E a} (hφ : IsCuspForm φ)
    (hA : ∀ (t : ℝ) (g : GA E a), ‖φ.1 (splitCentre E a t * g)‖ = ‖φ.1 g‖) : Decays φ.1 := by
  intro L hL C₀ hC₀ N
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · exact ⟨0, fun g c _ ξ hξ => (hξ (Subsingleton.elim _ _)).elim⟩
  obtain ⟨ω, hω, hωB, hω1, t, ht, hsieg⟩ := GlobalTheory.SiegelDiagNormOne.exists_siegelSet_diag_normOne E a
  set d : ℕ := Module.finrank ℚ E with hd
  have hdet : ∀ b ∈ ω, (ideleModule E (GeneralLinearGroup.det b) : ℝ) = 1 :=
    fun b hb => ideleModule_det_eq_one (hωB hb) (hω1 b hb)
  have hRD := fun i : Fin a => GlobalTheory.cuspRapidDecaySiegelGL_of_finite GlobalTheory.automorphicFormsFiniteGL E a φ hφ ω hω hωB hdet
    t ht (Pi.single i ((a * d * N : ℕ) : ℝ))
  choose C hC using hRD
  obtain ⟨δ, hδ, hgeo⟩ := exists_le_norm_vecMul hω ((isCompact_maxCompact (K := E) (n := a)).mul hC₀.inv) hL
  obtain ⟨m, M, hm, -, hmM⟩ := exists_pos_bounds hC₀ (f := fun c => (ideleModule E (GeneralLinearGroup.det c) : ℝ))
    (continuous_subtype_val.comp (continuous_ideleModule.comp (AdelicGLn.continuous_det E a)))
    (fun c _ => (ideleModule E _).2)
  refine ⟨(∑ i, |C i|) * ((δ ^ (a * d) * m)⁻¹) ^ N, fun g c hc ξ hξ hξL => ?_⟩
  obtain ⟨γ, b, hb, _, ⟨r, hr, hrat, rfl⟩, k, hk, e⟩ := hsieg (g * c)
  replace e : ratGL E a γ * (g * c) = b * diagUnits a (fun i => posIdele (K := E) (r i) (hr i)) * k := e
  have hprod : 0 < ∏ i, r i := Finset.prod_pos fun i _ => hr i
  set ρ := (∏ i, r i) ^ ((a : ℝ)⁻¹) with hρ
  have hρpos : 0 < ρ := Real.rpow_pos_of_pos hprod _
  have hρa : ρ ^ a = ∏ i, r i := Real.rpow_inv_natCast_pow hprod.le ha.ne'
  set r' : Fin a → ℝ := fun i => r i / ρ with hr'
  have hr'pos : ∀ i, 0 < r' i := fun i => div_pos (hr i) hρpos
  have hD : diagUnits a (fun i => posIdele (K := E) (r i) (hr i)) =
      diagUnits a (fun _ : Fin a => posIdele (K := E) ρ hρpos) *
        diagUnits a (fun i => posIdele (K := E) (r' i) (hr'pos i)) := by
    rw [← map_mul]
    congr 1
    funext i
    rw [Pi.mul_apply, ← GlobalTheory.CuspBoundSiegel.posIdele_mul]
    exact GlobalTheory.CuspBoundSiegel.posIdele_congr _ _ (by simp only [hr']; field_simp)
  have key : ratGL E a γ * (g * c) = splitCentre E a (Real.log ρ) *
      (b * diagUnits a (fun i => posIdele (K := E) (r' i) (hr'pos i)) * k) := by
    rw [e, hD, GlobalTheory.CuspBoundSiegel.diagUnits_posIdele a hρpos, ← mul_assoc b, ← splitCentre_comm]
    simp only [mul_assoc]
  haveI : Nonempty (Fin a) := ⟨⟨0, ha⟩⟩
  obtain ⟨i₀, hi₀⟩ := Finite.exists_min r

  have h1 : ‖φ.1 (g * c)‖ ≤ (∑ i, |C i|) * (r' i₀ ^ (a * d)) ^ N := by
    rw [← hφ.1.left γ, key, hA]
    refine (hC i₀ b hb r' hr'pos (fun i j hij => by
      simp only [hr']
      rw [← mul_div_assoc]
      exact div_le_div_of_nonneg_right (hrat i j hij) hρpos.le) (by
      simp only [hr']
      rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, hρa,
        div_self hprod.ne']) k hk).trans ?_
    rw [Finset.prod_eq_single i₀ (fun j _ hj => by rw [Pi.single_eq_of_ne hj, Real.rpow_zero]) (by simp),
      Pi.single_eq_same, Real.rpow_natCast, ← pow_mul]
    exact mul_le_mul_of_nonneg_right ((le_abs_self _).trans
      (Finset.single_le_sum (f := fun i => |C i|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i₀)))
      (pow_nonneg (hr'pos i₀).le _)

  have eg : g = ratGL E a γ⁻¹ * (b * diagUnits a (fun i => posIdele (K := E) (r i) (hr i)) * (k * c⁻¹)) := by
    rw [← mul_assoc _ k, ← e, map_inv]; group
  have hη : ξ ᵥ* (γ⁻¹).val ≠ 0 := fun h => hξ (by
    have := congrArg (· ᵥ* γ.val) h
    simpa only [vecMul_vecMul, ← Units.val_mul, inv_mul_cancel, Units.val_one, vecMul_one, zero_vecMul] using this)
  have h2 := hgeo b hb (k * c⁻¹) (Set.mul_mem_mul hk (Set.inv_mem_inv.2 hc)) r hr (r i₀) (hr i₀) hi₀ _ hη _ (by
    conv_lhs => rw [eg, Units.val_mul, ← vecMul_vecMul]
    congr 1
    funext j
    exact ((algebraMap E (Ad E)).map_vecMul (γ⁻¹).val ξ j).symm) hξL

  have h3 : (ideleModule E (GeneralLinearGroup.det g) : ℝ) * (ideleModule E (GeneralLinearGroup.det c) : ℝ) =
      ρ ^ (a * d) := by
    have h := det_mul_mul b (diagUnits a fun i => posIdele (K := E) (r i) (hr i)) k
    rw [ideleModule_det_diagUnits_posIdele r hr, mem_normOneGL.1 (maxCompact_le_normOneGL hk), mul_one, ← e] at h
    have hγ := ideleModule_det_rat γ
    replace h : (ideleModule E (GeneralLinearGroup.det (ratGL E a γ * (g * c))) : ℝ) =
      (ideleModule E (GeneralLinearGroup.det b) : ℝ) * (∏ i, r i) ^ d := h
    rw [map_mul, map_mul, hγ, one_mul, map_mul, map_mul, Positive.val_mul, hdet b hb, one_mul] at h
    rw [h, pow_mul, hρa]
  set X := ‖fun i => pInf E (((fun j => algebraMap E (Ad E) (ξ j)) ᵥ* g.val) i)‖ with hX
  set G : ℝ := (ideleModule E (GeneralLinearGroup.det g) : ℝ) with hG
  have hGpos : 0 < G := (ideleModule E _).2
  have h4 : r' i₀ ^ (a * d) ≤ (δ ^ (a * d) * m)⁻¹ * (X ^ (a * d) / G) := by
    have h5 : (δ * r i₀) ^ (a * d) ≤ X ^ (a * d) := pow_le_pow_left₀ (mul_pos hδ (hr i₀)).le h2 _
    have h6 : G * m ≤ ρ ^ (a * d) := h3 ▸ mul_le_mul_of_nonneg_left (hmM c hc).1 hGpos.le
    have hri := hr i₀
    calc r' i₀ ^ (a * d) = r i₀ ^ (a * d) / ρ ^ (a * d) := div_pow _ _ _
      _ ≤ r i₀ ^ (a * d) / (G * m) := div_le_div_of_nonneg_left (by positivity) (by positivity) h6
      _ = (δ ^ (a * d) * m)⁻¹ * ((δ * r i₀) ^ (a * d) / G) := by rw [mul_pow]; field_simp
      _ ≤ _ := by gcongr
  refine h1.trans ?_
  rw [mul_assoc, ← mul_pow]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (pow_nonneg (hr'pos i₀).le _) h4 N)
    (Finset.sum_nonneg fun _ _ => abs_nonneg _)

theorem decays_of_mem {π : CuspSub E a} (hπ : π.IsUnitary) {φ : Sm E a} (hφ : φ ∈ π.V) : Decays φ.1 := by
  obtain ⟨ω, hω, hc⟩ := hπ
  refine decays_of_isCuspForm (π.cusp φ hφ) fun t g => ?_
  rw [splitCentre_comm, splitCentre_eq_scalar]
  have h := congrFun (congrArg Subtype.val (hc (infId E (expU fun _ => (t : ℂ))) φ hφ)) g
  refine (congrArg norm h).trans ?_
  change ‖_ * φ.1 g‖ = _
  rw [norm_mul, hω, one_mul]

theorem word_mem {π : CuspSub E a} (l : List (Lie E a)) {φ : Sm E a} (hφ : φ ∈ π.V) : GlobalTheory.GLFin.word l φ ∈ π.V := by
  induction l with
  | nil => exact hφ
  | cons X l ih => exact π.stable (.lie X) _ ih

theorem Decays.zero : Decays (0 : GA E a → ℂ) := fun _ _ _ _ _ => ⟨0, fun _ _ _ _ _ _ => by simp⟩

theorem Decays.add {F G : GA E a → ℂ} (hF : Decays F) (hG : Decays G) : Decays (F + G) := fun L hL C₀ hC₀ N => by
  obtain ⟨C, h⟩ := hF L hL C₀ hC₀ N
  obtain ⟨C', h'⟩ := hG L hL C₀ hC₀ N
  refine ⟨C + C', fun g c hc ξ hξ hm => ?_⟩
  rw [add_mul]
  exact (norm_add_le _ _).trans (add_le_add (h g c hc ξ hξ hm) (h' g c hc ξ hξ hm))

theorem Decays.smul {F : GA E a → ℂ} (hF : Decays F) (z : ℂ) : Decays (z • F) := fun L hL C₀ hC₀ N => by
  obtain ⟨C, h⟩ := hF L hL C₀ hC₀ N
  refine ⟨‖z‖ * C, fun g c hc ξ hξ hm => ?_⟩
  rw [mul_assoc]
  exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left (h g c hc ξ hξ hm) (norm_nonneg _))

theorem Decays.smoothInf {F : GA E a → ℂ} (hF : Decays F) {f : Lie E a → ℂ} (hf : Continuous f)
    (hc : HasCompactSupport f) (hs : tsupport f ⊆ invSet E a) : Decays (GlobalTheory.JSW.smoothInf f F) := by
  intro L hL C₀ hC₀ N
  have hK : IsCompact ((fun y : GL (Fin a) (Cinf E) => toL y.val) ⁻¹' tsupport f) :=
    GlobalTheory.CuspQuot.isOpenEmbedding_val.isInducing.isCompact_preimage' hc fun x hx => hs hx
  obtain ⟨C, h⟩ := hF L hL _ (hC₀.mul (hK.image GlobalTheory.CuspQuot.continuous_infGL)) N
  haveI : IsFiniteMeasureOnCompacts (volume : Measure (Fin a → Cinf E)) := inferInstance
  haveI : SigmaFinite (volume : Measure (Fin a → Cinf E)) := inferInstance
  haveI : IsFiniteMeasureOnCompacts (volume : Measure (Lie E a)) :=
    MeasureTheory.Measure.pi.isFiniteMeasureOnCompacts _
  have hi : Integrable f := hf.integrable_of_hasCompactSupport hc
  refine ⟨(∫ x, ‖f x‖) * C, fun g c hcC ξ hξ hm => ?_⟩
  rw [mul_assoc, ← integral_mul_const]
  refine norm_integral_le_of_norm_le (hi.norm.mul_const _) (.of_forall fun x => ?_)
  by_cases hx : x ∈ tsupport f
  · obtain ⟨u, hu⟩ := hs hx
    obtain rfl : x = toL u.val := hu.symm
    rw [norm_mul, chart_val, mul_assoc]
    exact mul_le_mul_of_nonneg_left (h g _ (Set.mul_mem_mul hcC ⟨u, hx, rfl⟩) ξ hξ hm) (norm_nonneg _)
  · simp [image_eq_zero_of_notMem_tsupport hx]

theorem smoothSpan_le_Sm (π : CuspSub E a) : GlobalTheory.JSW.smoothSpan π ≤ Sm E a := Submodule.span_le.2 <| by
  rintro _ ⟨f, φ, hf, -, rfl⟩
  exact GlobalTheory.AutGrowth.smoothing_mem_Sm E a volume f hf φ.1 φ.2

end GlobalTheory.ShortVecDecay

end
