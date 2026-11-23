import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.FundamentalDomainCusps.NilpotentSubgroupRepresentation
import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.FundamentalDomainCusps.ShortIsot
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.KoszulLowersPower

open Matrix MeasureTheory NumberField Topology

noncomputable section

namespace CompanionTheory.D.gk.RF

open Formalism.MainNotions.S Formalism.L2.SG.ProjRows

section Loc

variable {n : ℕ} {ε : Fin n → Bool}

theorem Jm_hermC (ε : Fin n → Bool) : (Formalism.REAL.Jm ε)ᴴ = Formalism.REAL.Jm ε := by
  unfold Formalism.REAL.Jm
  rw [diagonal_conjTranspose]
  congr 1
  funext a
  by_cases h : ε a <;> simp [h]

theorem Jm_det (ε : Fin n → Bool) : IsUnit (Formalism.REAL.Jm ε).det := by
  unfold Formalism.REAL.Jm
  rw [det_diagonal, isUnit_iff_ne_zero, Finset.prod_ne_zero_iff]
  intro a _
  by_cases h : ε a <;> simp [h]

theorem uMat_mul' (g h : Formalism.REAL.UJ ε) : uMat (g * h) = uMat g * uMat h := rfl

theorem uMat_inv_mulC (g : Formalism.REAL.UJ ε) : uMat g⁻¹ * uMat g = 1 := by
  rw [← uMat_mul', inv_mul_cancel]; rfl

theorem uMat_mul_invC (g : Formalism.REAL.UJ ε) : uMat g * uMat g⁻¹ = 1 := by
  rw [← uMat_mul', mul_inv_cancel]; rfl

theorem hf_uMatC (g : Formalism.REAL.UJ ε) (a z : Fin n → ℂ) :
    hf (Formalism.REAL.Jm ε) (uMat g *ᵥ a) (uMat g *ᵥ z) = hf (Formalism.REAL.Jm ε) a z := by
  have h : (uMat g)ᴴ * Formalism.REAL.Jm ε * uMat g = Formalism.REAL.Jm ε := g.2
  unfold hf
  rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, h]

theorem conj_xw (g : Formalism.REAL.UJ ε) (w b : Fin n → ℂ) :
    uMat g⁻¹ * xw (Formalism.REAL.Jm ε) w b * uMat g = xw (Formalism.REAL.Jm ε) (uMat g⁻¹ *ᵥ w) (uMat g⁻¹ *ᵥ b) := by
  have key : ∀ a z, hf (Formalism.REAL.Jm ε) (uMat g⁻¹ *ᵥ a) z = hf (Formalism.REAL.Jm ε) a (uMat g *ᵥ z) := fun a z => by
    rw [← hf_uMatC g, mulVec_mulVec, uMat_mul_invC, one_mulVec]
  refine mat_extC fun z => ?_
  rw [← mulVec_mulVec, ← mulVec_mulVec, xw_mulVec, xw_mulVec, key, key, mulVec_sub, mulVec_smul, mulVec_smul]

theorem second_order_exp_conj (g : Formalism.REAL.UJ ε) (X : Matrix (Fin n) (Fin n) ℂ) :
    uMat g⁻¹ * ex2 X * uMat g = ex2 (uMat g⁻¹ * X * uMat g) := by
  have : uMat g⁻¹ * X * uMat g * (uMat g⁻¹ * X * uMat g) = uMat g⁻¹ * (X * X) * uMat g := by
    calc _ = uMat g⁻¹ * X * (uMat g * uMat g⁻¹) * X * uMat g := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [uMat_mul_invC, Matrix.mul_one, Matrix.mul_assoc (uMat g⁻¹) X X]
  simp only [ex2, this, mul_add, add_mul, Matrix.mul_one, uMat_inv_mulC, mul_smul_comm, smul_mul_assoc]

theorem norm_xw_le (w b : Fin n → ℂ) (i j : Fin n) : ‖xw (Formalism.REAL.Jm ε) w b i j‖ ≤ 2 * (‖w‖ * ‖b‖) := by
  have h1 : ‖(if ε j then 1 else -1 : ℂ)‖ = 1 := by split_ifs <;> simp
  simp only [xw, Formalism.REAL.Jm, Matrix.sub_apply, vecMulVec_apply, vecMul_diagonal]
  refine (norm_sub_le _ _).trans ?_
  simp only [norm_mul, h1, mul_one, Pi.star_apply, norm_star]
  have a := norm_le_pi_norm w
  have c := norm_le_pi_norm b
  have e1 := mul_le_mul (a i) (c j) (norm_nonneg _) (norm_nonneg _)
  have e2 := mul_le_mul (c i) (a j) (norm_nonneg _) (norm_nonneg _)
  linarith

theorem norm_second_order_exp_sub_one_le {A : Matrix (Fin n) (Fin n) ℂ} {a : ℝ} (h : ∀ i j, ‖A i j‖ ≤ a) (i j : Fin n) :
    ‖(ex2 A - 1) i j‖ ≤ a + n * a ^ 2 := by
  have e : ex2 A - 1 = A + (2 : ℂ)⁻¹ • (A * A) := by unfold ex2; abel
  have h0 : 0 ≤ a := (norm_nonneg _).trans (h i j)
  have h2 : ‖(A * A) i j‖ ≤ n * a ^ 2 := by
    rw [Matrix.mul_apply]
    refine (norm_sum_le _ _).trans ((Finset.sum_le_card_nsmul _ _ (a ^ 2) fun k _ => ?_).trans (by simp))
    rw [norm_mul, _root_.sq]
    exact mul_le_mul (h _ _) (h _ _) (norm_nonneg _) h0
  rw [e, Matrix.add_apply, Matrix.smul_apply]
  refine (norm_add_le _ _).trans (add_le_add (h i j) ?_)
  rw [norm_smul, norm_inv, Complex.norm_two]
  nlinarith [norm_nonneg ((A * A) i j)]

end Loc

section XW

variable {K : Type} [Field K] [StarRing K] {n : ℕ} (J : Matrix (Fin n) (Fin n) K)

theorem xw_add (w b b' : Fin n → K) : xw J w (b + b') = xw J w b + xw J w b' :=
  mat_extC fun z => by
    rw [add_mulVec, xw_mulVec, xw_mulVec, xw_mulVec, hf_add_leftC, add_smul, smul_add]; abel

theorem xw_nat (w b : Fin n → K) (k : ℕ) : xw J w ((k : K) • b) = (k : K) • xw J w b :=
  mat_extC fun z => by
    rw [smul_mulVec, xw_mulVec, xw_mulVec, hf_smul_leftC, star_natCast, smul_sub, smul_smul, smul_smul, smul_smul,
      mul_comm (hf J w z)]

theorem smul_xw (c : K) (w b : Fin n → K) : c • xw J w b = xw (c • J) w b := by
  simp only [xw, vecMul_smul, vecMulVec_smul, smul_sub]

end XW

variable (I : AutInst)

theorem P_det (v : InfinitePlace I.F) : IsUnit (I.P v).det := (Matrix.isUnit_iff_isUnit_det _).1 (I.P_unit v)

theorem atM_add (v : InfinitePlace I.F) (A B : Matrix (Fin I.n) (Fin I.n) I.E) :
    atM I v (A + B) = atM I v A + atM I v B := by
  simp only [atM, Matrix.map_add _ (map_add (I.φ v)), mul_add, add_mul]

theorem atM_neg (v : InfinitePlace I.F) (A : Matrix (Fin I.n) (Fin I.n) I.E) : atM I v (-A) = -atM I v A := by
  simp only [atM, Matrix.map_neg _ (map_neg (I.φ v)), Matrix.mul_neg, Matrix.neg_mul]

theorem atM_sum (v : InfinitePlace I.F) {ι : Type} (s : Finset ι) (A : ι → Matrix (Fin I.n) (Fin I.n) I.E) :
    atM I v (∑ i ∈ s, A i) = ∑ i ∈ s, atM I v (A i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [atM]
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, atM_add, ih]

theorem second_order_exp_at_infinite_place (v : InfinitePlace I.F) (X : Matrix (Fin I.n) (Fin I.n) I.E) : atM I v (ex2 X) = ex2 (atM I v X) := by
  have h1 : atM I v 1 = 1 := by
    simp only [atM, Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one, nonsing_inv_mul _ (P_det I v)]
  have h2 : atM I v (X * X) = atM I v X * atM I v X := by
    simp only [atM, Matrix.map_mul, Matrix.mul_assoc, mul_nonsing_inv_cancel_left _ _ (P_det I v)]
  have h3 : ∀ A, atM I v ((2 : I.E)⁻¹ • A) = (2 : ℂ)⁻¹ • atM I v A := fun A => by
    have : ((2 : I.E)⁻¹ • A).map (I.φ v) = (2 : ℂ)⁻¹ • A.map (I.φ v) := by
      ext i j; simp [map_ofNat]
    simp only [atM, this, mul_smul_comm, smul_mul_assoc]
  rw [ex2, atM_add, atM_add, h1, h3, h2, ex2]

theorem atV_addC (v : InfinitePlace I.F) (a b : Fin I.n → I.E) : atV I v (a + b) = atV I v a + atV I v b := by
  simp only [atV, ← mulVec_add]; congr 1; funext i; simp

theorem atV_smulC (v : InfinitePlace I.F) (c : I.E) (a : Fin I.n → I.E) : atV I v (c • a) = I.φ v c • atV I v a := by
  simp only [atV, ← mulVec_smul]; congr 1; funext i; simp

theorem atV_zero (v : InfinitePlace I.F) : atV I v 0 = 0 := by
  simpa using atV_smulC I v 0 0

theorem Wv_span (v : InfinitePlace I.F) {ι : Type} (w : ι → Fin I.n → I.E) :
    Submodule.span ℂ (Set.range fun i => atV I v (w i)) = Wv I (Submodule.span I.E (Set.range w)) v := by
  refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)
  · rintro _ ⟨i, rfl⟩
    exact Submodule.subset_span ⟨w i, Submodule.subset_span ⟨i, rfl⟩, rfl⟩
  · rintro _ ⟨u, hu, rfl⟩
    induction hu using Submodule.span_induction with
    | mem x hx => obtain ⟨i, rfl⟩ := hx; exact Submodule.subset_span ⟨i, rfl⟩
    | zero => rw [atV_zero]; exact Submodule.zero_mem _
    | add a b _ _ ha hb => rw [atV_addC]; exact Submodule.add_mem _ ha hb
    | smul c a _ ha => rw [atV_smulC]; exact Submodule.smul_mem _ _ ha

theorem exists_denC : ∃ c : ℕ, 1 ≤ c ∧ ∀ i j, IsIntegral ℤ (((c : I.E) • I.J) i j) := by
  classical
  obtain ⟨y, hy, h⟩ := exists_integral_multiples ℤ ℚ (L := I.E)
    (Finset.univ.image fun p : Fin I.n × Fin I.n => I.J p.1 p.2)
  refine ⟨y.natAbs, Int.natAbs_pos.2 hy, fun i j => ?_⟩
  have h1 := h _ (Finset.mem_image_of_mem _ (Finset.mem_univ (i, j)))
  rw [Matrix.smul_apply, smul_eq_mul, Nat.cast_natAbs]
  rcases abs_choice y with e | e <;> rw [e]
  · simpa using h1
  · simpa using h1.neg

theorem int_xw {J : Matrix (Fin I.n) (Fin I.n) I.E} (hJ : ∀ i j, IsIntegral ℤ (J i j)) {w b : Fin I.n → I.E}
    (hw : w ∈ IntV I) (hb : b ∈ IntV I) (i j : Fin I.n) : IsIntegral ℤ (xw J w b i j) := by
  have hs : ∀ a : I.E, IsIntegral ℤ a → IsIntegral ℤ (star a) := fun a ha =>
    ha.map (starRingEnd I.E).toIntAlgHom
  simp only [xw, Matrix.sub_apply, vecMulVec_apply, vecMul, dotProduct, Pi.star_apply]
  exact ((hw i).mul (IsIntegral.sum _ fun k _ => (hs _ (hb k)).mul (hJ k j))).sub
    ((hb i).mul (IsIntegral.sum _ fun k _ => (hs _ (hw k)).mul (hJ k j)))

theorem second_order_exp_congruence (M : ℕ) {Y : Matrix (Fin I.n) (Fin I.n) I.E} (hY : ∀ i j, IsIntegral ℤ (Y i j)) :
    Cong I M (ex2 (((2 * M : ℕ) : I.E) • Y)) := by
  intro i j
  refine ⟨2 * Y i j + 2 * M * (Y * Y) i j, ?_, ?_⟩
  · have h2 : IsIntegral ℤ (2 : I.E) := by exact_mod_cast isIntegral_natCast (R := ℤ) (B := I.E) 2
    refine (h2.mul (hY i j)).add ((h2.mul (isIntegral_natCast M)).mul ?_)
    rw [Matrix.mul_apply]
    exact IsIntegral.sum _ fun k _ => (hY _ _).mul (hY _ _)
  · simp only [ex2, smul_mul_assoc, mul_smul_comm, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    push_cast
    ring

theorem exists_gam (hT : Transp) (M c : ℕ) (hc : ∀ i j, IsIntegral ℤ (((c : I.E) • I.J) i j)) {d : ℕ}
    {w β : Fin d → Fin I.n → I.E} (hw : ∀ i, w i ∈ IntV I) (hβ : ∀ i, β i ∈ IntV I)
    (hW : Isot I.J (Submodule.span I.E (Set.range w))) (hβW : ∀ i, β i ∈ perp I.J (Submodule.span I.E (Set.range w))) :
    ∃ γ ∈ GamSet I M, ∀ v, uMat (γ v) =
      ex2 (-∑ i, xw (Formalism.REAL.Jm (I.ε v)) (atV I v (w i)) (((2 * M * c : ℕ) : ℂ) • atV I v (β i))) := by
  obtain ⟨hJ, -, -, -, -, -, hxw, hU⟩ := hT I
  have hd : IsUnit I.J.det := isUnit_iff_ne_zero.2 I.J_det
  obtain ⟨a1, -, -, -⟩ := nilpotent_lie_algebra I.E I.n I.J _ hJ hd hW
  let X := ∑ i, xw I.J (w i) (((2 * M * c : ℕ) : I.E) • β i)
  have hX : InL I.J _ X := (nilpotent_subgroup_representation I.E I.n I.J _ hJ hd hW d w rfl).1 _ fun i => Submodule.smul_mem _ _ (hβW i)
  let Y := ∑ i, xw ((c : I.E) • I.J) (w i) (β i)
  have hY : ∀ i j, IsIntegral ℤ (Y i j) := fun i j => by
    simp only [Y, Matrix.sum_apply]
    exact IsIntegral.sum _ fun k _ => int_xw I hc (hw k) (hβ k) i j
  have hXY : X = ((2 * M : ℕ) : I.E) • Y := by
    simp only [X, Y, xw_nat]
    simp only [Finset.smul_sum, ← smul_xw, smul_smul, Nat.cast_mul]
  obtain ⟨-, -, i1, hN⟩ := a1 X hX
  obtain ⟨u2, -, i2, -⟩ := a1 _ hN
  rw [neg_neg] at i2
  let γ : GL (Fin I.n) I.E := ⟨ex2 (-X), ex2 X, i2, i1⟩
  have hγ : γ ∈ Formalism.UG.UJ (starRingEnd I.E) I.J := u2
  obtain ⟨g, hg⟩ := hU γ hγ
  refine ⟨g, ⟨γ, ⟨hγ, ?_, ?_⟩, hg⟩, fun v => ?_⟩
  · show Cong I M (ex2 (-X))
    rw [hXY, ← smul_neg]
    exact second_order_exp_congruence I M fun i j => (hY i j).neg
  · show Cong I M (ex2 X)
    rw [hXY]
    exact second_order_exp_congruence I M hY
  · rw [hg]
    show atM I v (ex2 (-X)) = _
    simp only [second_order_exp_at_infinite_place, atM_neg, X, atM_sum, hxw, atV_smulC, map_natCast]

theorem split_cov {y : I.Ginf} {S : Submodule I.E (Fin I.n → I.E)} {ρ : ℝ} (h : Covers I y S ρ) {k : ℕ} (hk : k ≠ 0)
    {d : ℕ} (b : InfinitePlace I.F → Fin d → Fin I.n → ℂ) (hb : ∀ v i, b v i ∈ Wv I S v) :
    ∃ β : Fin d → Fin I.n → I.E, (∀ i, β i ∈ IntV I ∧ β i ∈ S) ∧
      ∀ v i, ‖uMat (y v)⁻¹ *ᵥ (b v i - (k : ℂ) • atV I v (β i))‖ ≤ k * ρ := by
  choose β h1 h2 h3 using fun i => h (fun v => (k : ℂ)⁻¹ • b v i) fun v => Submodule.smul_mem _ _ (hb v i)
  refine ⟨β, fun i => ⟨h1 i, h2 i⟩, fun v i => ?_⟩
  have hk' : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hk
  have h4 := (norm_le_pi_norm _ v).trans (h3 i)
  simp only [Pi.sub_apply, vecAt, ← mulVec_sub] at h4
  have e : b v i - (k : ℂ) • atV I v (β i) = (k : ℂ) • ((k : ℂ)⁻¹ • b v i - atV I v (β i)) := by
    rw [smul_sub, smul_inv_smul₀ hk']
  rw [e, mulVec_smul, norm_smul, Complex.norm_natCast]
  exact mul_le_mul_of_nonneg_left h4 (Nat.cast_nonneg k)

theorem atV_mem {S : Submodule I.E (Fin I.n → I.E)} {u : Fin I.n → I.E} (hu : u ∈ S) (v : InfinitePlace I.F) :
    atV I v u ∈ Wv I S v := Submodule.subset_span ⟨u, hu, rfl⟩

theorem nilpotent_cover_of : Transp → GamSub → NilpAlg → NilpRep → NCover := by
  intro hT hG hA hR I M hM
  obtain ⟨c, hc1, hc⟩ := exists_denC I
  obtain ⟨Γ, hΓ, -⟩ := hG I M
  set k : ℕ := 2 * M * c with hk
  have hk0 : k ≠ 0 := by positivity
  set Kc : ℝ := 4 * I.n * k
  refine ⟨Kc + I.n * Kc ^ 2 + 1, by positivity, fun y d w s ρ hd hs hρ hsρ hw hW hc1 hc2 m hm => ?_⟩
  set W := Submodule.span I.E (Set.range w)
  have hperp := (hT I).2.2.2.1
  have hWv : ∀ v, Isot (Formalism.REAL.Jm (I.ε v)) (Wv I W v) := fun v => by
    rw [Isot, ← hperp]; exact Submodule.span_mono (Set.image_mono hW)
  have A := fun v => hA ℂ I.n _ _ (Jm_hermC (I.ε v)) (Jm_det _) (hWv v)
  have R := fun v => hR ℂ I.n _ _ (Jm_hermC (I.ε v)) (Jm_det _) (hWv v) d _ (Wv_span I v w)
  choose X hX hmX using fun v => (A v).2.1 (uMat (m v)) (m v).2 (hm v)
  choose b hb hXb using fun v => (R v).2.2.1 _ (hX v)
  obtain ⟨β, hβ, hβr⟩ := split_cov I hc2 hk0 b fun v i => by rw [hperp]; exact hb v i
  obtain ⟨γ₁, hγ₁, e₁⟩ := exists_gam I hT M c hc (fun i => (hw i).1) (fun i => (hβ i).1) hW fun i => (hβ i).2
  let X₁ := fun v => ∑ i, xw (Formalism.REAL.Jm (I.ε v)) (atV I v (w i)) ((k : ℂ) • atV I v (β i))
  have hX₁ : ∀ v, InL (Formalism.REAL.Jm (I.ε v)) (Wv I W v) (-X₁ v) := fun v =>
    ((A v).1 _ ((R v).1 _ fun i => Submodule.smul_mem _ _ (by rw [← hperp]; exact atV_mem I (hβ i).2 v))).2.2.2
  choose b' hb' hZ using fun v => (R v).2.2.2 _ ((A v).2.2.1 _ _ (hX₁ v) (hX v)).2.1
  obtain ⟨β', hβ', hβr'⟩ := split_cov I hc1 hk0 b' hb'
  obtain ⟨γ₂, hγ₂, e₂⟩ := exists_gam I hT M c hc (fun i => (hw i).1) (fun i => (hβ' i).1) hW fun i => hW (hβ' i).2
  let Z₁ := fun v => ∑ i, xw (Formalism.REAL.Jm (I.ε v)) (atV I v (w i)) ((k : ℂ) • atV I v (β' i))
  have hZ₁ : ∀ v, InZ (Formalism.REAL.Jm (I.ε v)) (Wv I W v) (-Z₁ v) := fun v =>
    ((A v).2.2.2 _ ((R v).2.1 _ fun i => Submodule.smul_mem _ _ (atV_mem I (hβ' i).2 v))).2.1
  have cen : ∀ v Y, InL (Formalism.REAL.Jm (I.ε v)) (Wv I W v) Y →
      InL (Formalism.REAL.Jm (I.ε v)) (Wv I W v) (-Z₁ v + Y) ∧ ex2 (-Z₁ v) * ex2 Y = ex2 (-Z₁ v + Y) := fun v Y hY => by
    obtain ⟨h1, -, h2⟩ := (A v).2.2.2 _ (hZ₁ v)
    obtain ⟨h3, -, h4⟩ := (A v).2.2.1 _ _ h1 hY
    rw [(h2 Y hY).1, (h2 Y hY).2, sub_zero, smul_zero, add_zero] at h4
    exact ⟨h3, h4⟩
  refine ⟨γ₂ * γ₁, by rw [← hΓ] at hγ₁ hγ₂ ⊢; exact Γ.mul_mem hγ₂ hγ₁, fun v => ?_, fun v i j => ?_⟩
  · show Lowers _ _ (uMat (γ₂ v) * uMat (γ₁ v) - 1)
    rw [e₁, e₂, (cen v _ (hX₁ v)).2]
    exact ((A v).1 _ (cen v _ (hX₁ v)).1).2.1
  · obtain ⟨h1, h2, h3⟩ := (A v).2.2.1 _ _ (hX₁ v) (hX v)
    have h4 := ((A v).2.2.1 _ _ h1 ((A v).2.2.2 _ h2).1).1
    let r : Fin d → Fin I.n → ℂ := fun i =>
      (b v i - (k : ℂ) • atV I v (β i)) + (b' v i - (k : ℂ) • atV I v (β' i))
    have e : -Z₁ v + (-X₁ v + X v + (2 : ℂ)⁻¹ • (-X₁ v * X v - X v * -X₁ v)) =
        ∑ i, xw (Formalism.REAL.Jm (I.ε v)) (atV I v (w i)) (r i) := by
      rw [hZ v]
      nth_rewrite 1 [hXb v]
      have : ∀ (u p q : Fin I.n → ℂ), xw (Formalism.REAL.Jm (I.ε v)) u (p - q) =
          xw (Formalism.REAL.Jm (I.ε v)) u p - xw (Formalism.REAL.Jm (I.ε v)) u q := fun u p q => by
        rw [eq_sub_iff_add_eq, ← xw_add, sub_add_cancel]
      simp only [r, xw_add, this, Finset.sum_add_distrib, Finset.sum_sub_distrib, X₁, Z₁]
      abel
    have e' : uMat ((y⁻¹ * (γ₂ * γ₁ * m) * y) v) =
        ex2 (∑ i, xw (Formalism.REAL.Jm (I.ε v)) (vecAt I y (w i) v) (uMat (y v)⁻¹ *ᵥ r i)) := by
      show uMat (y v)⁻¹ * (uMat (γ₂ v) * uMat (γ₁ v) * uMat (m v)) * uMat (y v) = _
      rw [e₁, e₂, hmX, Matrix.mul_assoc (ex2 _), h3, (cen v _ h4).2, e, second_order_exp_conj, Finset.mul_sum, Finset.sum_mul]
      simp only [conj_xw, vecAt]
    have hb1 : ∀ i j, ‖(∑ l, xw (Formalism.REAL.Jm (I.ε v)) (vecAt I y (w l) v) (uMat (y v)⁻¹ *ᵥ r l)) i j‖ ≤
        Kc * (s * ρ) := fun i j => by
      rw [Matrix.sum_apply]
      refine (norm_sum_le _ _).trans ((Finset.sum_le_card_nsmul _ _ (4 * k * (s * ρ)) fun l _ => ?_).trans ?_)
      · refine (norm_xw_le _ _ _ _).trans ?_
        have q1 := (norm_le_pi_norm _ v).trans (hw l).2
        have q2 : ‖uMat (y v)⁻¹ *ᵥ r l‖ ≤ 2 * (k * ρ) := by
          simp only [r]
          rw [mulVec_add]
          exact (norm_add_le _ _).trans (by linarith [hβr v l, hβr' v l])
        have := mul_le_mul q1 q2 (norm_nonneg _) hs
        linarith
      · rw [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        have hd' : (d : ℝ) ≤ I.n := by exact_mod_cast hd
        have : 0 ≤ 4 * (k : ℝ) * (s * ρ) := by positivity
        calc (d : ℝ) * (4 * k * (s * ρ)) ≤ I.n * (4 * k * (s * ρ)) := mul_le_mul_of_nonneg_right hd' this
          _ = _ := by ring
    rw [e']
    refine (norm_second_order_exp_sub_one_le hb1 i j).trans ?_
    have h0 : 0 ≤ s * ρ := mul_nonneg hs hρ
    have h5 : (s * ρ) ^ 2 ≤ s * ρ := by nlinarith
    have h6 : (I.n : ℝ) * Kc ^ 2 * (s * ρ) ^ 2 ≤ I.n * Kc ^ 2 * (s * ρ) :=
      mul_le_mul_of_nonneg_left h5 (by positivity)
    nlinarith

theorem exists_kappa {U : Set I.Ginf} (hU : U ∈ 𝓝 (1 : I.Ginf)) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ g : I.Ginf, (∀ v i j, ‖(uMat (g v) - 1) i j‖ ≤ κ) → g ∈ U := by
  let f : I.Ginf → (InfinitePlace I.F → Fin I.n → Fin I.n → ℂ) := fun g v => uMat (g v)
  have hf : IsInducing f := IsInducing.piMap fun v => (Formalism.REAL.isClosedEmbeddingMatrix I.n (I.ε v)).1.isInducing
  rw [hf.nhds_eq_comap, Filter.mem_comap] at hU
  obtain ⟨V, hV, hVU⟩ := hU
  obtain ⟨κ, hκ, hb⟩ := Metric.nhds_basis_closedBall.mem_iff.1 hV
  refine ⟨κ, hκ, fun g hg => hVU (hb ?_)⟩
  rw [mem_closedBall_iff_norm]
  exact (pi_norm_le_iff_of_nonneg hκ.le).2 fun v => (pi_norm_le_iff_of_nonneg hκ.le).2 fun i =>
    (pi_norm_le_iff_of_nonneg hκ.le).2 fun j => hg v i j

theorem Covers.mono {I : AutInst} {y : I.Ginf} {S : Submodule I.E (Fin I.n → I.E)} {ρ ρ' : ℝ} (h : Covers I y S ρ)
    (hρ : ρ ≤ ρ') : Covers I y S ρ' := fun b hb => by
  obtain ⟨u, h1, h2, h3⟩ := h b hb
  exact ⟨u, h1, h2, h3.trans hρ⟩

theorem reduction_geometry_at_infinity : Gap → ShortIsot → CovSpan → CovPerp → Mahler → NCover → GeoInf := by
  intro hGap hSI hCS hCP hMa hNC I M hM U hU
  obtain ⟨κ, hκ, hκU⟩ := exists_kappa I hU
  obtain ⟨s₁, hs₁, hSI⟩ := hSI I
  obtain ⟨C₁, hC₁, hCS⟩ := hCS I
  obtain ⟨C₂, hC₂, hCP⟩ := hCP I
  obtain ⟨C₃, hC₃, hNC⟩ := hNC I M hM
  set s₀ := min s₁ 1
  have hs₀ : 0 < s₀ := lt_min hs₁ one_pos
  obtain ⟨η, hη, hη1, hηa, hηb, hηc⟩ : ∃ η : ℝ, 0 < η ∧ η < 1 ∧ 2 * C₁ * η ≤ 1 ∧ (C₁ + C₂) * η ≤ 1 ∧
      C₃ * ((C₁ + C₂) * η) ≤ κ := by
    have t : ∀ a : ℝ, Filter.Tendsto (fun η : ℝ => a * η) (𝓝[>] 0) (𝓝 0) := fun a => by
      simpa using ((continuous_const_mul a).tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
    obtain ⟨η, h0, h1, h2, h3, h4⟩ := (Filter.Eventually.and (eventually_mem_nhdsWithin (a := (0 : ℝ)) (s := Set.Ioi 0))
      (((t 1).eventually (gt_mem_nhds one_pos)).and (((t (2 * C₁)).eventually (ge_mem_nhds one_pos)).and
      (((t (C₁ + C₂)).eventually (ge_mem_nhds one_pos)).and ((t (C₃ * (C₁ + C₂))).eventually (ge_mem_nhds hκ)))))).exists
    exact ⟨η, h0, by simpa using h1, h2, h3, by rwa [← mul_assoc]⟩
  have he : 0 < s₀ * η ^ (I.n + 1) := by positivity
  obtain ⟨C, hC, hMa⟩ := hMa I M hM (C₂ / (s₀ * η ^ (I.n + 1)))
  refine ⟨C, hC, fun y => ?_⟩
  by_cases hc : ∃ u ∈ IntV I, u ≠ 0 ∧ ‖vecAt I y u‖ ≤ s₀ * η ^ (I.n + 1)
  · right
    obtain ⟨t, ht, hts, d, w, hd, hw, hne, hall⟩ := hGap I.E I.n (IntV I) (fun u => ‖vecAt I y u‖) s₀ η hs₀ hη hη1 hc
    have ht1 : t ≤ 1 := hts.trans (min_le_right _ _)
    have hs : η * t ≤ s₁ := (mul_le_of_le_one_left ht.le hη1.le).trans (hts.trans (min_le_left _ _))
    have hI : Isot I.J (Submodule.span I.E (Set.range w)) := Submodule.span_le.2 (by
      rintro _ ⟨j, rfl⟩
      exact mem_perp_spanC fun i => hSI y _ (hw i).1 _ (hw j).1 ((hw i).2.trans hs) ((hw j).2.trans hs))
    have c1 := hCS y d w (η * t) hd (by positivity) hw
    have c2 := hCP y _ _ t ht (by nlinarith) c1 fun u hu hn => by
      by_contra h
      exact hn (hall u hu (not_le.1 h).le)
    have hρ : η * t * (C₁ * (η * t) + C₂ / t) ≤ (C₁ + C₂) * η := by
      have e : η * t * (C₁ * (η * t) + C₂ / t) = C₁ * η * (η * t * t) + C₂ * η := by field_simp
      have : η * t * t ≤ 1 := mul_le_one₀ (mul_le_one₀ hη1.le ht.le ht1) ht.le ht1
      have := mul_le_of_le_one_right (by positivity : 0 ≤ C₁ * η) this
      rw [e]; linarith
    refine ⟨_, hne, hI, fun m hm => ?_⟩
    obtain ⟨γ, h1, h2, h3⟩ := hNC y d w (η * t) (C₁ * (η * t) + C₂ / t) hd (by positivity) (by positivity)
      (hρ.trans hηb) hw hI (c1.mono (le_add_of_nonneg_right (by positivity)))
      (c2.mono (le_add_of_nonneg_left (by positivity))) m hm
    exact ⟨γ, h1, h2, hκU _ fun v i j =>
      (h3 v i j).trans ((mul_le_mul_of_nonneg_left hρ hC₃.le).trans hηc)⟩
  · left
    push Not at hc
    have c0 : Covers I y ⊥ 0 := fun b hb => ⟨0, fun _ => isIntegral_zero, Submodule.zero_mem _, by
      have h0 : ∀ v, atV I v 0 = 0 := atV_zero I
      have hb0 : ∀ v, b v = 0 := fun v => by
        have := hb v
        simpa [Wv, h0] using this
      have : (fun v => uMat (y v)⁻¹ *ᵥ b v) - vecAt I y 0 = 0 := by
        funext v; simp [vecAt, hb0, h0]
      rw [this, norm_zero]⟩
    have c2 := hCP y ⊥ 0 _ he (by linarith) c0 fun u hu hn => (hc u hu fun h => hn (by simp [h])).le
    have e : perp I.J (⊥ : Submodule I.E (Fin I.n → I.E)) = ⊤ := eq_top_iff.2 fun z _ w hw => by
      rw [(Submodule.mem_bot I.E).1 hw]; simp [hf]
    exact hMa y (e ▸ c2)

end CompanionTheory.D.gk.RF
