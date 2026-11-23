import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.FundamentalDomainCusps.ShortIsot
import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirVolumeRatios.VolumeClassRepresentatives.DensRat
import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.OneParameterDerivatives.TauReduction.BlockGramReduction.EmbeddingLinearIndependent
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.ConcreteLevelAdelicSubset

open Matrix MeasureTheory NumberField Topology

noncomputable section

namespace CompanionTheory.D.gk.RF

open Formalism.MainNotions.S Formalism.MainNotions.LeviCoordinates Formalism.L2.SG.Pf.Tau

variable (I : AutInst)

theorem phi_star (v : InfinitePlace I.F) (a : I.E) : I.φ v (star a) = star (I.φ v a) :=
  I.cm.cmUnram.2.1 (I.φ v) a

theorem star_atV_vecMul (v : InfinitePlace I.F) (u : Fin I.n → I.E) :
    star (atV I v u) ᵥ* Formalism.REAL.Jm (I.ε v) = (fun i => I.φ v ((star u ᵥ* I.J) i)) ᵥ* I.P v := by
  have hPP : ((I.P v)⁻¹)ᴴ * (I.P v)ᴴ = 1 := by
    rw [← conjTranspose_mul, rrg_P_mul_inv, conjTranspose_one]
  rw [atV, star_mulVec, ← I.P_spec v, vecMul_vecMul, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hPP, Matrix.one_mul,
    ← vecMul_vecMul]
  congr 1
  funext i
  simp [vecMul, dotProduct, map_sum, phi_star]

theorem hf_atV (v : InfinitePlace I.F) (u : Fin I.n → I.E) (z : Fin I.n → ℂ) :
    hf (Formalism.REAL.Jm (I.ε v)) (atV I v u) z = (fun i => I.φ v ((star u ᵥ* I.J) i)) ⬝ᵥ (I.P v *ᵥ z) := by
  rw [hf, dotProduct_mulVec, star_atV_vecMul, dotProduct_mulVec]

theorem P_atV (v : InfinitePlace I.F) (u : Fin I.n → I.E) : I.P v *ᵥ atV I v u = fun i => I.φ v (u i) := by
  rw [atV, mulVec_mulVec, rrg_P_mul_inv, one_mulVec]

theorem hf_atV_atV (v : InfinitePlace I.F) (u u' : Fin I.n → I.E) :
    hf (Formalism.REAL.Jm (I.ε v)) (atV I v u) (atV I v u') = I.φ v (hf I.J u u') := by
  rw [hf_atV, P_atV, hf, dotProduct_mulVec]
  simp [dotProduct, map_sum]

theorem hf_smul_leftD {K : Type} [Field K] [StarRing K] {n : ℕ} (J : Matrix (Fin n) (Fin n) K) (c : K)
    (x y : Fin n → K) : hf J (c • x) y = star c * hf J x y := by
  simp [hf, star_smul, smul_dotProduct]

theorem hf_add_leftD {K : Type} [Field K] [StarRing K] {n : ℕ} (J : Matrix (Fin n) (Fin n) K)
    (x x' y : Fin n → K) : hf J (x + x') y = hf J x y + hf J x' y := by
  simp [hf, star_add, add_dotProduct]

theorem mem_perp_spanD {K : Type} [Field K] [StarRing K] {n : ℕ} (J : Matrix (Fin n) (Fin n) K)
    {S : Set (Fin n → K)} {z : Fin n → K} (h : ∀ w ∈ S, hf J w z = 0) : z ∈ perp J (Submodule.span K S) := by
  intro w hw
  induction hw using Submodule.span_induction with
  | mem w hw => exact h w hw
  | zero => simp [hf]
  | add a b _ _ ha hb => rw [hf_add_leftD, ha, hb, add_zero]
  | smul c a _ ha => rw [hf_smul_leftD, ha, mul_zero]

theorem Wv_perp (v : InfinitePlace I.F) (W : Submodule I.E (Fin I.n → I.E)) :
    Wv I (perp I.J W) v = perp (Formalism.REAL.Jm (I.ε v)) (Wv I W v) := by
  refine le_antisymm (Submodule.span_le.2 ?_) fun z hz => ?_
  · rintro _ ⟨u, hu, rfl⟩
    refine mem_perp_spanD _ ?_
    rintro _ ⟨w, hw, rfl⟩
    rw [hf_atV_atV, hu w hw, map_zero]
  obtain ⟨d, w, hw⟩ := Submodule.fg_iff_exists_fin_generating_family.1 (IsNoetherian.noetherian W)
  let A : Matrix (Fin d) (Fin I.n) I.E := Matrix.of fun i => star (w i) ᵥ* I.J
  obtain ⟨s, hs⟩ := A.mulVecLin.rangeRestrict.exists_rightInverse_of_surjective A.mulVecLin.range_rangeRestrict
  obtain ⟨g, hg⟩ := s.exists_extend
  let Q : Matrix (Fin I.n) (Fin I.n) I.E := 1 - LinearMap.toMatrix' g * A
  have hAQ : ∀ u, A *ᵥ (Q *ᵥ u) = 0 := fun u => by
    have h1 := congrArg Subtype.val (LinearMap.congr_fun hs ⟨A *ᵥ u, u, rfl⟩)
    have h2 := LinearMap.congr_fun hg ⟨A *ᵥ u, u, rfl⟩
    simp only [Q, sub_mulVec, one_mulVec, mulVec_sub, ← mulVec_mulVec, LinearMap.toMatrix'_mulVec]
    rw [show g (A *ᵥ u) = s ⟨A *ᵥ u, u, rfl⟩ from h2]
    exact sub_eq_zero.2 h1.symm
  have hQ : ∀ u, Q *ᵥ u ∈ perp I.J W := fun u => by
    rw [← hw]
    refine mem_perp_spanD _ ?_
    rintro _ ⟨i, rfl⟩
    rw [hf, dotProduct_mulVec]
    exact congrFun (hAQ u) i
  have hz0 : A.map (I.φ v) *ᵥ (I.P v *ᵥ z) = 0 := funext fun i => by
    have := hz (atV I v (w i)) (Submodule.subset_span ⟨w i, hw ▸ Submodule.subset_span ⟨i, rfl⟩, rfl⟩)
    rw [hf_atV] at this
    exact this
  have hz1 : Q.map (I.φ v) *ᵥ (I.P v *ᵥ z) = I.P v *ᵥ z := by
    simp only [Q]
    rw [Matrix.map_sub _ (map_sub _), Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _), sub_mulVec,
      one_mulVec, ← mulVec_mulVec, hz0, mulVec_zero, sub_zero]
  have hz2 : z = ∑ j, (I.P v *ᵥ z) j • atV I v (Q *ᵥ Pi.single j 1) := by
    have : z = (I.P v)⁻¹ *ᵥ (Q.map (I.φ v) *ᵥ (I.P v *ᵥ z)) := by
      rw [hz1, mulVec_mulVec, rrg_P_inv_mul, one_mulVec]
    conv_lhs => rw [this]
    simp only [atV, ← mulVec_smul, ← mulVec_sum]
    congr 1
    funext i
    simp [mulVec, dotProduct, Finset.sum_apply, mul_comm, Pi.single_apply]
  rw [hz2]
  exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, hQ _, rfl⟩)

theorem atM_mulVec (v : InfinitePlace I.F) (A : Matrix (Fin I.n) (Fin I.n) I.E) (u : Fin I.n → I.E) :
    atM I v A *ᵥ atV I v u = atV I v (A *ᵥ u) := by
  rw [atM, ← mulVec_mulVec, P_atV, ← mulVec_mulVec, atV]
  congr 1
  funext i
  simp [mulVec, dotProduct, map_sum]

theorem transport_to_standard_form : Transp := by
  intro I
  refine ⟨I.J_herm, phi_star I, hf_atV_atV I, Wv_perp I, fun v W hW h => hW ?_, atM_mulVec I, fun v w b => ?_,
    fun γ hγ => ⟨fun v => Formalism.L2.S.S7.DensRat.ratReal I γ hγ v, fun _ => rfl⟩⟩
  · refine (Submodule.eq_bot_iff _).2 fun u hu => funext fun i => (I.φ v).injective ?_
    have h1 : atV I v u ∈ Wv I W v := Submodule.subset_span ⟨u, hu, rfl⟩
    rw [h, Submodule.mem_bot] at h1
    have h2 := P_atV I v u
    rw [h1, mulVec_zero] at h2
    simpa using (congrFun h2 i).symm
  · have e : ∀ a c : Fin I.n → I.E, (vecMulVec a c).map (I.φ v) =
        vecMulVec (fun i => I.φ v (a i)) fun i => I.φ v (c i) := fun a c => by
      ext i j; simp [vecMulVec_apply]
    simp only [atM, xw, star_atV_vecMul]
    rw [Matrix.map_sub _ (map_sub _), e, e, Matrix.mul_sub, Matrix.sub_mul, mul_vecMulVec, mul_vecMulVec,
      vecMulVec_mul, vecMulVec_mul]
    rfl

theorem atM_mul (v : InfinitePlace I.F) (A B : Matrix (Fin I.n) (Fin I.n) I.E) :
    atM I v (A * B) = atM I v A * atM I v B := by
  simp only [atM, Matrix.map_mul, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (I.P v), rrg_P_mul_inv, Matrix.one_mul]

theorem atM_one (v : InfinitePlace I.F) : atM I v 1 = 1 := by
  simp [atM, rrg_P_inv_mul]

variable {I}

theorem Cong.one (M : ℕ) : Cong I M 1 := fun _ _ => ⟨0, isIntegral_zero, by simp⟩

theorem Cong.mul {M : ℕ} {A B : Matrix (Fin I.n) (Fin I.n) I.E} (hA : Cong I M A) (hB : Cong I M B) :
    Cong I M (A * B) := by
  choose a ha ha' using hA
  choose b hb hb' using hB
  intro i j
  refine ⟨∑ k, a i k * ((M : I.E) * b k j) + a i j + b i j, ((IsIntegral.sum _ fun k _ => (ha i k).mul
    ((isIntegral_natCast M).mul (hb k j))).add (ha i j)).add (hb i j), ?_⟩
  have : A * B - 1 = (A - 1) * (B - 1) + (A - 1) + (B - 1) := by noncomm_ring
  rw [this, Matrix.add_apply, Matrix.add_apply, Matrix.mul_apply]
  simp only [ha', hb', mul_add, Finset.mul_sum]
  congr 2
  exact Finset.sum_congr rfl fun k _ => by ring

theorem Cong.integral {M : ℕ} {A : Matrix (Fin I.n) (Fin I.n) I.E} (hA : Cong I M A) (i j : Fin I.n) :
    IsIntegral ℤ (A i j) := by
  obtain ⟨a, ha, h⟩ := hA i j
  have : A i j = (M : I.E) * a + (1 : Matrix (Fin I.n) (Fin I.n) I.E) i j := by rw [← h, Matrix.sub_apply]; ring
  rw [this, Matrix.one_apply]
  refine ((isIntegral_natCast M).mul ha).add ?_
  split_ifs
  exacts [isIntegral_one, isIntegral_zero]

theorem norm_emb_le {a : I.E} {B : ℝ} (h : ∀ v, ‖I.φ v a‖ ≤ B) (σ : I.E →+* ℂ) : ‖σ a‖ ≤ B := by
  obtain ⟨v, rfl | rfl⟩ := complex_embedding_cases I σ
  · exact h v
  · simpa using h v

theorem arithmetic_subgroup_of_transport : Transp → GamSub := by
  intro _ I M
  refine ⟨{ carrier := GamSet I M
            one_mem' := ⟨1, ⟨one_mem _, Cong.one M, by simpa using Cong.one M⟩, fun v => by
              rw [Units.val_one, atM_one]; rfl⟩
            mul_mem' := ?_
            inv_mem' := ?_ }, rfl, fun C hC => ?_⟩
  · rintro g h ⟨γ, hγ, h1⟩ ⟨δ, hδ, h2⟩
    refine ⟨γ * δ, ⟨mul_mem hγ.1 hδ.1, hγ.2.1.mul hδ.2.1, by
      rw [_root_.mul_inv_rev]; exact hδ.2.2.mul hγ.2.2⟩, fun v => ?_⟩
    rw [Units.val_mul, atM_mul, ← h1, ← h2]
    rfl
  · rintro g ⟨γ, hγ, h1⟩
    refine ⟨γ⁻¹, ⟨inv_mem hγ.1, hγ.2.2, by simpa using hγ.2.1⟩, fun v => ?_⟩
    refine Units.inv_eq_of_mul_eq_one_right (u := ((g v : Formalism.REAL.UJ (I.ε v)) : (Matrix (Fin I.n) (Fin I.n) ℂ)ˣ)) ?_
    rw [show (((g v : Formalism.REAL.UJ (I.ε v)) : (Matrix (Fin I.n) (Fin I.n) ℂ)ˣ) : Matrix (Fin I.n) (Fin I.n) ℂ) = _
      from h1 v, ← atM_mul, Units.mul_inv, atM_one]
  · let f : I.Ginf → InfinitePlace I.F → Fin I.n → Fin I.n → ℂ := fun g v i j => (I.P v * uMat (g v) * (I.P v)⁻¹) i j
    have hf : Continuous f := continuous_pi fun v => continuous_pi fun i => continuous_pi fun j =>
      ((continuous_const.matrix_mul ((Units.continuous_val.comp continuous_subtype_val).comp
        (continuous_apply v))).matrix_mul continuous_const).matrix_elem i j
    obtain ⟨B, hB⟩ := hC.exists_bound_of_continuousOn hf.continuousOn
    have hfin := Set.Finite.pi' fun _ : Fin I.n => Set.Finite.pi' fun _ : Fin I.n =>
      Embeddings.finite_of_norm_le I.E ℂ B
    refine Set.Finite.of_finite_image (f := fun g v => uMat (g v))
      ((hfin.image fun A v => atM I v (Matrix.of A)).subset ?_)
      fun g _ h _ e => funext fun v => Subtype.ext (Units.ext (congrFun e v))
    rintro _ ⟨g, ⟨hgC, γ, hγ, h1⟩, rfl⟩
    refine ⟨fun i j => (γ : Matrix (Fin I.n) (Fin I.n) I.E) i j, fun i j => ⟨hγ.2.1.integral i j,
      norm_emb_le fun v => ?_⟩, funext fun v => (h1 v).symm⟩
    have e : f g v i j = I.φ v ((γ : Matrix (Fin I.n) (Fin I.n) I.E) i j) := by
      simp only [f, h1 v, atM, ← Matrix.mul_assoc, rrg_P_mul_inv, Matrix.one_mul]
      rw [Matrix.mul_assoc, rrg_P_mul_inv, Matrix.mul_one, Matrix.map_apply]
    rw [← e]
    exact (norm_le_pi_norm _ j).trans ((norm_le_pi_norm _ i).trans ((norm_le_pi_norm _ v).trans (hB g hgC)))

theorem fundamental_domain_discrete_of : GamSub → GFDisc := by
  intro _ I C hC
  have := Formalism.L2.SG.Pf.finite_adeles_group_t2 I
  have := Formalism.L2.SG.Pf.gf_discrete I
  have hcl : IsClosed ((rr_GF I : Subgroup I.GA) : Set I.GA) := Subgroup.isClosed_of_discrete
  exact (hC.inter_right hcl).finite
    (IsDiscrete.mono (isDiscrete_iff_discreteTopology.2 this) Set.inter_subset_right)

theorem exists_denD {ι : Type} [Finite ι] (a : ι → I.E) : ∃ c : ℕ, 1 ≤ c ∧ ∀ i, IsIntegral ℤ ((c : I.E) * a i) := by
  classical
  cases nonempty_fintype ι
  obtain ⟨y, hy, h⟩ := exists_integral_multiples ℤ ℚ (Finset.univ.image a)
  refine ⟨y.natAbs, Int.natAbs_pos.2 hy, fun i => ?_⟩
  have h1 := h (a i) (Finset.mem_image_of_mem _ (Finset.mem_univ i))
  rw [zsmul_eq_mul] at h1
  rcases Int.natAbs_eq y with e | e
  · rw [← Int.cast_natCast, ← e]; exact h1
  · have : ((y.natAbs : ℕ) : I.E) = -(y : I.E) := by rw [← Int.cast_natCast, ← Int.cast_neg]; congr 1; omega
    rw [this, neg_mul]; exact h1.neg

theorem isIntegral_starD {a : I.E} (h : IsIntegral ℤ a) : IsIntegral ℤ (star a) :=
  h.map (starRingEnd I.E).toIntAlgHom

theorem hf_unitary {n : ℕ} {ε : Fin n → Bool} (g : Formalism.REAL.UJ ε) (a b : Fin n → ℂ) :
    hf (Formalism.REAL.Jm ε) (uMat g *ᵥ a) (uMat g *ᵥ b) = hf (Formalism.REAL.Jm ε) a b := by
  have h : (uMat g)ᴴ * Formalism.REAL.Jm ε * uMat g = Formalism.REAL.Jm ε := g.2
  rw [hf, star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, h, hf]

theorem norm_hf_leD {n : ℕ} (ε : Fin n → Bool) (a b : Fin n → ℂ) : ‖hf (Formalism.REAL.Jm ε) a b‖ ≤ n * (‖a‖ * ‖b‖) := by
  rw [hf, dotProduct]
  refine (norm_sum_le _ _).trans ((Finset.sum_le_card_nsmul _ _ (‖a‖ * ‖b‖) fun i _ => ?_).trans (by simp))
  rw [norm_mul, Pi.star_apply, norm_star, Formalism.REAL.Jm, mulVec_diagonal, norm_mul]
  have : ‖(if ε i then (1 : ℂ) else -1)‖ = 1 := by split_ifs <;> simp
  rw [this, one_mul]
  exact mul_le_mul (norm_le_pi_norm a i) (norm_le_pi_norm b i) (norm_nonneg _) (norm_nonneg _)

theorem eq_zero_of_small {a : I.E} (ha : IsIntegral ℤ a) (h : ∀ v, ‖I.φ v a‖ ≤ 1 / 2) : a = 0 := by
  by_contra h0
  have h1 := InfinitePlace.one_le_of_lt_one (K := I.E) (a := ⟨a, ha⟩) (w := Classical.arbitrary _)
    (fun e => h0 (congrArg Subtype.val e)) fun z _ => by
      rw [← InfinitePlace.norm_embedding_eq]
      exact (norm_emb_le h _).trans_lt (by norm_num)
  rw [← InfinitePlace.norm_embedding_eq] at h1
  exact absurd (h1.trans (norm_emb_le h _)) (by norm_num)

theorem short_isotropic_vector_of : Transp → ShortIsot := by
  intro _ I
  obtain ⟨c, hc, hJ⟩ := exists_denD fun p : Fin I.n × Fin I.n => I.J p.1 p.2
  have hK : (1 : ℝ) ≤ 2 * c * (I.n + 1) := by
    have : (1 : ℝ) ≤ c := by exact_mod_cast hc
    nlinarith [(Nat.cast_nonneg I.n : (0 : ℝ) ≤ _)]
  refine ⟨1 / (2 * c * (I.n + 1)), by positivity, fun y u hu u' hu' h1 h2 => ?_⟩
  have hc0 : (c : I.E) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  refine (mul_eq_zero.1 (eq_zero_of_small (a := (c : I.E) * hf I.J u u') ?_ fun v => ?_)).resolve_left hc0
  · simp only [hf, dotProduct, mulVec, Finset.mul_sum]
    refine IsIntegral.sum _ fun i _ => IsIntegral.sum _ fun j _ => ?_
    rw [mul_left_comm, ← mul_assoc (c : I.E)]
    exact (isIntegral_starD (hu i)).mul ((hJ (i, j)).mul (hu' j))
  · rw [map_mul, norm_mul, map_natCast, Complex.norm_natCast, ← hf_atV_atV, ← hf_unitary (y v)⁻¹]
    set s : ℝ := 1 / (2 * c * (I.n + 1))
    have hs0 : 0 ≤ s := by positivity
    have hs1 : s ≤ 1 := by rw [div_le_one (by positivity)]; exact hK
    have a1 : ‖vecAt I y u v‖ * ‖vecAt I y u' v‖ ≤ s * 1 :=
      mul_le_mul ((norm_le_pi_norm _ v).trans h1) (((norm_le_pi_norm _ v).trans h2).trans hs1) (norm_nonneg _) hs0
    have a2 := (norm_hf_leD (I.ε v) (vecAt I y u v) (vecAt I y u' v)).trans
      (mul_le_mul_of_nonneg_left a1 (Nat.cast_nonneg _))
    refine (mul_le_mul_of_nonneg_left a2 (Nat.cast_nonneg c)).trans ?_
    have hcp : (0 : ℝ) < c := by exact_mod_cast hc
    have : (c : ℝ) * ((I.n + 1) * s) = 1 / 2 := by simp only [s]; field_simp
    rw [← this]
    gcongr
    · linarith
    · rw [mul_one]

end CompanionTheory.D.gk.RF
