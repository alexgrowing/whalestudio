import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock

open MeasureTheory ValuativeRel Matrix
open scoped NNReal ENNReal Pointwise

noncomputable section
namespace GlobalTheory.SplitFlip.Model
open GlobalTheory.SplitWeil GlobalTheory.SplitWeil.Model GlobalTheory.SplitFlip

variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

section NonZero
variable {A A' D : Type*} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A'] [Fintype D] [DecidableEq D]

omit [DecidableEq A] in

theorem isPrimFrame_mul {Λ Λ' : Submodule 𝒪[k] (D → k)} {X : Matrix A D k} (hX : IsPrimFrame Λ X) (g : GL D k)
    (hg : ∀ x, x ᵥ* g.val ∈ Λ' ↔ x ∈ Λ) : IsPrimFrame Λ' (X * g.val) := by
  have hr : ∀ i, (X * g.val).row i = X.row i ᵥ* g.val := fun i => by
    funext j; simp [Matrix.row, Matrix.mul_apply, vecMul, dotProduct]
  refine ⟨?_, fun i => ?_, le_antisymm ?_ ?_⟩
  · rw [rank_mul_eq_left_of_isUnit_det _ _ ((Matrix.isUnit_iff_isUnit_det _).1 g.isUnit)]; exact hX.1
  · rw [hr, hg]; exact hX.2.1 i
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨i, rfl⟩
    exact ⟨Submodule.subset_span ⟨i, rfl⟩, by rw [SetLike.mem_coe, hr, hg]; exact hX.2.1 i⟩
  · rintro x ⟨hx, hx'⟩
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun k).1 hx
    have e1 : ∑ i, c i • (X * g.val).row i = (∑ i, c i • X.row i) ᵥ* g.val := by
      simp only [hr, sum_vecMul, smul_vecMul]
    rw [e1] at hx' ⊢
    have h2 : (∑ i, c i • X.row i) ∈ Submodule.span 𝒪[k] (Set.range X.row) := by
      rw [hX.2.2]
      exact ⟨Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i)), (hg _).1 hx'⟩
    obtain ⟨d, hd⟩ := (Submodule.mem_span_range_iff_exists_fun 𝒪[k]).1 h2
    rw [← hd, sum_vecMul]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [smul_vecMul, ← hr]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

theorem val_le_iff_mem {ϖ : kˣ} (hϖ : IsUnif ϖ) (e : ℕ) (r : 𝒪[k]) :
    r ∈ IsLocalRing.maximalIdeal 𝒪[k] ^ e ↔ valuation k (r : k) ≤ valuation k ((ϖ ^ e : kˣ) : k) := by
  rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton,
    ← (Valuation.integer.integers (valuation k)).le_iff_dvd]
  rfl

open Classical in

theorem sum_psi {ϖ : kˣ} (hϖ : IsUnif ϖ) {ψ : AddChar k Circle} (hψ : HasConductor ψ 1) (e : ℕ) (s s' : Res k e) :
    ∑ t : Res k e, (ψ (((Quotient.out t : 𝒪[k]) : k) *
      ((((ϖ ^ e)⁻¹ : kˣ) : k) * (((Quotient.out s : 𝒪[k]) : k) - ((Quotient.out s' : 𝒪[k]) : k)))) : ℂ) =
      if s = s' then (Fintype.card (Res k e) : ℂ) else 0 := by
  split_ifs with h
  · subst h; simp
  set x : k := (((ϖ ^ e)⁻¹ : kˣ) : k) * (((Quotient.out s : 𝒪[k]) : k) - ((Quotient.out s' : 𝒪[k]) : k)) with hx
  have h0 : 0 < valuation k ((ϖ ^ e : kˣ) : k) := zero_lt_iff.2 (by simp)
  have hvx : valuation k x = (valuation k ((ϖ ^ e : kˣ) : k))⁻¹ *
      valuation k ((Quotient.out s - Quotient.out s' : 𝒪[k]) : k) := by
    rw [hx, map_mul, Units.val_inv_eq_inv_val, map_inv₀]; rfl
  have triv : ∀ y : k, valuation k y ≤ 1 → ψ y = 1 := fun y hy => (hψ 1).2 le_rfl y (by simpa using hy)
  have hx1 : ¬ valuation k x ≤ valuation k ((1 : kˣ) : k) := by
    intro H
    rw [hvx, Units.val_one, map_one, inv_mul_le_iff₀ h0, mul_one, ← val_le_iff_mem hϖ, ← Ideal.Quotient.eq] at H
    exact h (by simpa using H)
  rw [← hψ x] at hx1
  push Not at hx1
  obtain ⟨y, hy, hy'⟩ := hx1
  have hx0 : x ≠ 0 := by
    rintro H
    rw [H, map_zero, le_zero_iff, map_eq_zero] at hy
    exact hy' (by simp [hy])
  have hr : y / x ∈ 𝒪[k] := by
    rw [Valuation.mem_integer_iff, map_div₀]; exact div_le_one_of_le₀ hy zero_le
  have key : ∀ a b : 𝒪[k], Ideal.Quotient.mk (IsLocalRing.maximalIdeal 𝒪[k] ^ e) a = Ideal.Quotient.mk _ b →
      ψ ((a : k) * x) = ψ ((b : k) * x) := fun a b hab => by
    rw [Ideal.Quotient.eq, val_le_iff_mem hϖ] at hab
    rw [show (a : k) * x = b * x + ((a - b : 𝒪[k]) : k) * x by push_cast; ring, AddChar.map_add_eq_mul,
      triv (((a - b : 𝒪[k]) : k) * x), mul_one]
    rw [map_mul, hvx, ← mul_assoc]
    exact mul_le_one' (by rw [mul_inv_le_iff₀ h0, one_mul]; exact hab) (Quotient.out s - Quotient.out s' : 𝒪[k]).2
  set S := ∑ t : Res k e, (ψ (((Quotient.out t : 𝒪[k]) : k) * x) : ℂ) with hS
  have hshift : S = ψ y * S := by
    rw [hS, Finset.mul_sum, ← Equiv.sum_comp (Equiv.addRight (Ideal.Quotient.mk _ (⟨_, hr⟩ : 𝒪[k]) : Res k e))]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [key _ (Quotient.out t + ⟨_, hr⟩) (by simp), ← Circle.coe_mul, ← AddChar.map_add_eq_mul]
    congr 2
    push_cast
    field_simp
    ring
  by_contra hne
  exact hy' (Circle.ext (by simpa using (mul_left_eq_self₀.1 hshift.symm).resolve_right hne))

theorem sum_invFourierSum {ϖ : kˣ} (hϖ : IsUnif ϖ) {ψ : AddChar k Circle} (hψ : HasConductor ψ 1) (e : ℕ)
    (P : Finset D) (Ψ : Matrix A D k → ℂ) (X : Matrix A D k) (S₀ : A → P → Res k e) :
    ∑ T : A → P → Res k e, invFourierSum ψ ϖ e P Ψ (setCols P X (liftRes T)) *
      (ψ (pairCols P (setCols P X ((ϖ ^ e)⁻¹ • liftRes S₀)) (liftRes T)) : ℂ) =
      (Fintype.card (Res k e) : ℂ) ^ (Fintype.card A * P.card) * Ψ (setCols P X ((ϖ ^ e)⁻¹ • liftRes S₀)) := by
  classical
  have h1 : ∀ T S, setCols P (setCols P X T) S = setCols P X S := fun T S => by
    ext i j; by_cases h : j ∈ P <;> simp [setCols, h]
  have h2 : ∀ T : A → P → Res k e, ∀ i, ∀ j ∈ P, setCols P X (liftRes T) i j ∈ 𝒪[k] := fun T i j h => by
    simpa [setCols, h] using liftRes_mem T i ⟨j, h⟩
  simp only [invFourierSum_apply, if_pos (h2 _), h1, Finset.sum_mul]
  rw [Finset.sum_comm]
  have h3 : ∀ S T : A → P → Res k e,
      (ψ (-pairCols P (setCols P X (liftRes T)) ((ϖ ^ e)⁻¹ • liftRes S)) : ℂ) *
        (ψ (pairCols P (setCols P X ((ϖ ^ e)⁻¹ • liftRes S₀)) (liftRes T)) : ℂ) =
      ∏ i, ∏ j, (ψ (((Quotient.out (T i j) : 𝒪[k]) : k) * ((((ϖ ^ e)⁻¹ : kˣ) : k) *
        (((Quotient.out (S₀ i j) : 𝒪[k]) : k) - ((Quotient.out (S i j) : 𝒪[k]) : k)))) : ℂ) := fun S T => by
    have hp : ∀ {ι : Type _} (s : Finset ι) (f : ι → k), (ψ (∑ i ∈ s, f i) : ℂ) = ∏ i ∈ s, (ψ (f i) : ℂ) :=
      fun s f => by
        induction s using Finset.induction_on with
        | empty => simp
        | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, AddChar.map_add_eq_mul,
            Circle.coe_mul, ih]
    rw [← Circle.coe_mul, ← AddChar.map_add_eq_mul, ← Finset.prod_product', ← hp, Finset.sum_product]
    congr 2
    simp only [pairCols, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp [setCols, liftRes, Units.smul_def]
    ring
  have h4 : ∀ S : A → P → Res k e, ∑ T : A → P → Res k e,
      ∏ i, ∏ j, (ψ (((Quotient.out (T i j) : 𝒪[k]) : k) * ((((ϖ ^ e)⁻¹ : kˣ) : k) *
        (((Quotient.out (S₀ i j) : 𝒪[k]) : k) - ((Quotient.out (S i j) : 𝒪[k]) : k)))) : ℂ) =
      if S₀ = S then (Fintype.card (Res k e) : ℂ) ^ (Fintype.card A * P.card) else 0 := fun S => by
    rw [← Fintype.prod_sum (fun i (t : P → Res k e) => ∏ j, (ψ (((Quotient.out (t j) : 𝒪[k]) : k) *
      ((((ϖ ^ e)⁻¹ : kˣ) : k) *
        (((Quotient.out (S₀ i j) : 𝒪[k]) : k) - ((Quotient.out (S i j) : 𝒪[k]) : k)))) : ℂ))]
    have h5 : ∀ i, ∑ t : P → Res k e, ∏ j, (ψ (((Quotient.out (t j) : 𝒪[k]) : k) * ((((ϖ ^ e)⁻¹ : kˣ) : k) *
        (((Quotient.out (S₀ i j) : 𝒪[k]) : k) - ((Quotient.out (S i j) : 𝒪[k]) : k)))) : ℂ) =
        ∏ j, if S₀ i j = S i j then (Fintype.card (Res k e) : ℂ) else 0 := fun i => by
      rw [← Fintype.prod_sum (fun (j : P) (t : Res k e) => (ψ (((Quotient.out t : 𝒪[k]) : k) *
        ((((ϖ ^ e)⁻¹ : kˣ) : k) *
        (((Quotient.out (S₀ i j) : 𝒪[k]) : k) - ((Quotient.out (S i j) : 𝒪[k]) : k)))) : ℂ))]
      exact Finset.prod_congr rfl fun j _ => by convert sum_psi hϖ hψ e (S₀ i j) (S i j)
    rw [Finset.prod_congr rfl fun i _ => h5 i]
    split_ifs with h
    · subst h; simp [← pow_mul, mul_comm]
    · obtain ⟨i, hi⟩ := Function.ne_iff.1 h
      obtain ⟨j, hj⟩ := Function.ne_iff.1 hi
      exact Finset.prod_eq_zero (Finset.mem_univ i) (Finset.prod_eq_zero (Finset.mem_univ j) (if_neg hj))
  simp only [mul_assoc, h3, ← Finset.mul_sum, h4]
  simp [mul_comm]

variable [MeasurableSpace k] [BorelSpace k]

theorem squareFlip_ne_zero [IsEmpty A'] {ϖ : kˣ} (hϖ : IsUnif ϖ) {ψ : AddChar k Circle} (hψ : HasConductor ψ 1)
    {e : ℕ} (he : 1 ≤ e) (σ : A ⊕ A' ≃ D) (ν : kˣ →* ℂˣ) (P : Finset D) (Φ : Matrix A' D k → ℂ) (hΦ : Φ 0 ≠ 0) :
    squareFlip (haarVol (KO k A')) σ ψ ν ϖ e P Φ ≠ 0 := by
  classical
  intro H
  have hψ' : HasConductor ψ⁻¹ 1 := fun x => by simpa only [AddChar.inv_apply', inv_eq_one] using hψ x
  let I := IsLocalRing.maximalIdeal 𝒪[k] ^ e
  let K : Matrix D D 𝒪[k] := Matrix.of fun r j =>
    if j ∈ Pᶜ then Quotient.out (Ideal.Quotient.mk I ((1 : Matrix D D 𝒪[k]) r j)) else (1 : Matrix D D 𝒪[k]) r j
  have hK : IsUnit K := by
    rw [Matrix.isUnit_iff_isUnit_det, ← IsLocalRing.residue_ne_zero_iff_isUnit, RingHom.map_det]
    have : (IsLocalRing.residue 𝒪[k]).mapMatrix K = (IsLocalRing.residue 𝒪[k]).mapMatrix 1 := by
      ext r j
      simp only [RingHom.mapMatrix_apply, map_apply, K, of_apply]
      split_ifs
      · exact Ideal.Quotient.eq.2 (Ideal.pow_le_self (by omega) (Ideal.Quotient.eq.1 (Ideal.Quotient.mk_out _)))
      · rfl
    rw [this]; simp
  obtain ⟨u, hu⟩ := hK
  let g : GL D k := Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) u * blockScale ϖ e Pᶜ
  have hg : ∀ x, x ᵥ* g.val ∈ blockLat ϖ e Pᶜ ↔ x ∈ stdLat k D := fun x => by
    rw [Units.val_mul, ← vecMul_vecMul, vecMul_blockScale_mem]
    exact (show _ ∈ glLat (stdLat k D) from glLat_stdLat (k := k) (D := D) ▸ ⟨u, rfl⟩) x
  have hprim := isPrimFrame_mul (isPrimitiveFrame_standardBasis σ) g hg
  let S₀ : A → ↥(Pᶜ) → Res k e := fun i j => Ideal.Quotient.mk I ((1 : Matrix D D 𝒪[k]) (σ (.inl i)) j)
  have hX : setCols Pᶜ (X0 k σ * g.val) ((ϖ ^ e)⁻¹ • liftRes S₀) = X0 k σ * g.val := by
    ext i j
    by_cases h : j ∈ Pᶜ
    · rw [frameMatrixFirstColumnBlock_mul_apply]
      simp only [setCols, of_apply, dif_pos h, g, Units.val_mul, blockScale, diagGL_val, mul_diagonal, blockUnits,
        if_pos h]
      show _ = ((u.val (σ (.inl i)) j : 𝒪[k]) : k) * _
      rw [hu]
      simp only [K, of_apply, if_pos h, Matrix.smul_apply, liftRes, S₀, Units.smul_def, smul_eq_mul]
      ring
    · simp only [setCols, of_apply, dif_neg h]
  have h5 := sum_invFourierSum hϖ hψ' e Pᶜ (phiA (haarVol (KO k A')) σ ν ϖ e (blockLat ϖ e P) (fourierSum ψ ϖ e P Φ))
    (X0 k σ * g.val) S₀
  rw [squareFlip] at H
  rw [H, hX, phiA, latA_blockLat, if_pos hprim, ← invT_invT g, splitTheta_fFun_frameFirstBlock_mul, smallF_of_isEmpty] at h5
  have h6 : fourierSum ψ ϖ e P Φ 0 = Φ 0 := by
    have h : ∀ T, setCols P (0 : Matrix A' D k) T = 0 := fun T => Subsingleton.elim _ _
    simp [fourierSum_apply, h, pairCols]
  rw [h6] at h5
  simp [hΦ, apow_ne_zero] at h5

theorem exists_flip_ne_zero (t s : ℕ) (ht : Odd t) (hs : Odd s) (a : Assignment) :
    ∃ (G : Grid k) (ϖ : kˣ) (ψ : AddChar k Circle) (S : G.PiLocalization₂), G.m = 1 ∧ G.t = t ∧ G.s = s ∧ G.IsGood ϖ ψ 2 ∧
      S.path = givenPath 1 ∧ S.IsAdmissible a ϖ 2 ∧ PassesThrough 0 0 S.path ∧
      (S.flip a ψ ϖ 2 (0, 0)).path = oppositePath 1 ∧ (S.flip a ψ ϖ 2 (0, 0)).tensor ≠ 0 := by
  obtain ⟨G, ϖ, ψ, hm, hr, ht', hs', hG⟩ := Grid.exists_isGood (k := k) 1 0 t s ht hs
  have hset := hG.square 0 (by omega) 0 (by omega)
  obtain ⟨S, hp, hS, h0⟩ := hG.exists_isAdmissible hset.unif a (γ := givenPath 1) (by unfold IsPath; decide)
    (by rw [hm]; intro b hb; simp [givenPath] at hb; rcases hb with rfl | rfl <;> simp [Edge.InGrid])
  refine ⟨G, ϖ, ψ, S, hm, ht', hs', hG, hp, hS, by rw [hp]; unfold PassesThrough; decide,
    by show flipPath 0 0 S.path = _; rw [hp]; decide, fun H => ?_⟩
  haveI : IsEmpty (Fin (G.rank (0, 0))) := by simp [Grid.rank, hr]; infer_instance
  have hJ : (S.level (0, 0)).map invT = KO k _ := Subsingleton.elim _ _
  have hB : ∀ x, G.sliceB 0 0 S.tensor x = fun _ => 1 := fun x => by
    funext Z
    rw [← h0]
    refine hS.tensor.1 fun b hb => ?_
    rw [hp] at hb
    simp [givenPath] at hb
    rcases hb with rfl | rfl
    · exact Subsingleton.elim _ _
    · ext i j; exact isEmptyElim j
  refine squareFlip_ne_zero hset.unif hset.cond one_le_two (stdSplit (G.rank_square 0 0)) (G.nu 0 0)
    (a.block _ _) (fun _ => 1) one_ne_zero ?_
  funext X
  have := congrFun H (Function.update (Function.update 0 (.ex 0 1) X.toCols₁) (.theta 1 0) X.toCols₂ᵀ)
  simp only [Grid.PiLocalization₂.flip, Grid.flipTensor, hJ, hB] at this
  convert this using 2
  · simp [Grid.joinA]
  · rfl

end NonZero

variable {A D₁ D₂ : Type*} [Fintype A] [DecidableEq A] [Fintype D₁] [DecidableEq D₁] [Fintype D₂] [DecidableEq D₂]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

def unip (b : Matrix D₁ D₂ k) : GL (D₁ ⊕ D₂) k :=
  ⟨fromBlocks 1 b 0 1, fromBlocks 1 (-b) 0 1, by simp [fromBlocks_multiply], by simp [fromBlocks_multiply]⟩

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

theorem gdet_unip (b : Matrix D₁ D₂ k) : gdet (unip b) = 1 :=
  Units.ext (by simp [gdet, unip, Matrix.GeneralLinearGroup.val_det_apply])

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [DecidableEq A] in

theorem pair_two (Y : Matrix A (D₁ ⊕ D₂) k) (T : Matrix A (Assignment.two.block D₁ D₂) k) :
    pairCols _ Y T = ∑ i, ∑ j : D₂, setCols _ (0 : Matrix A (D₁ ⊕ D₂) k) T i (.inr j) * Y i (.inr j) := by
  unfold pairCols
  refine Finset.sum_congr rfl fun i _ => ?_
  symm
  refine Finset.sum_bij (fun j _ => ⟨.inr j, by simp [Assignment.block]⟩) (by simp)
    (fun a _ a' _ h => by simpa using congrArg Subtype.val h) ?_ ?_
  · rintro ⟨j | j, hj⟩ _
    · simp [Assignment.block] at hj
    · exact ⟨j, by simp, rfl⟩
  · intro j _; simp [setCols, Assignment.block]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [DecidableEq A] in

theorem pair_one (Y : Matrix A (D₁ ⊕ D₂) k) (T : Matrix A (Assignment.one.block D₁ D₂) k) :
    pairCols _ Y T = ∑ i, ∑ j : D₁, setCols _ (0 : Matrix A (D₁ ⊕ D₂) k) T i (.inl j) * Y i (.inl j) := by
  unfold pairCols
  refine Finset.sum_congr rfl fun i _ => ?_
  symm
  refine Finset.sum_bij (fun j _ => ⟨.inl j, by simp [Assignment.block]⟩) (by simp)
    (fun a _ a' _ h => by simpa using congrArg Subtype.val h) ?_ ?_
  · rintro ⟨j | j, hj⟩ _
    · exact ⟨j, by simp, rfl⟩
    · simp [Assignment.block] at hj
  · intro j _; simp [setCols, Assignment.block]

variable [MeasurableSpace k] [BorelSpace k]

theorem omB_unip_fourier (ψ : AddChar k Circle) (m : Measure k) (ν α : kˣ →* ℂˣ) (b : Matrix D₁ D₂ k)
    (Φ : Matrix A (D₁ ⊕ D₂) k → ℂ) :
    omB ν α 1 (unip b) (fourierInt ψ m (Assignment.two.block D₁ D₂) Φ) =
      fourierInt ψ m (Assignment.two.block D₁ D₂)
        fun T => (ψ (trace (T.toCols₁ * b * T.toCols₂ᵀ)) : ℂ) * Φ T := by
  funext Y
  simp only [omB, gdet_unip, map_one, Units.val_one, apow_one, one_mul, transpose_one, Matrix.one_mul, fourierInt]
  congr 1
  funext T
  have h1 : setCols _ (Y * (unip b).val) T = setCols _ Y T := by
    ext i (j | j) <;> simp [setCols, Assignment.block, unip, Matrix.mul_apply, one_apply]
  have h2 : pairCols _ (Y * (unip b).val) T = trace ((setCols _ Y T).toCols₁ * b * (setCols _ Y T).toCols₂ᵀ)
      + pairCols _ Y T := by
    rw [pair_two, pair_two, trace, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [diag_apply, Matrix.mul_apply, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [setCols, Assignment.block, unip, Matrix.mul_apply, one_apply, toCols₁, toCols₂]
    ring
  rw [h1, h2, AddChar.map_add_eq_mul, Circle.coe_mul]
  ring

theorem omA_unip_fourier (ψ : AddChar k Circle) (m : Measure k) (ν β : kˣ →* ℂˣ) (b : Matrix D₁ D₂ k)
    (Φ : Matrix A (D₁ ⊕ D₂) k → ℂ) :
    omA ν β 1 (unip b) (fourierInt ψ m (Assignment.one.block D₁ D₂) Φ) =
      fourierInt ψ m (Assignment.one.block D₁ D₂)
        fun T => (ψ (-trace (T.toCols₁ * b * T.toCols₂ᵀ)) : ℂ) * Φ T := by
  funext Y
  simp only [omA, gdet_unip, map_one, inv_one, Units.val_one, apow_one, one_mul, Matrix.one_mul, fourierInt]
  congr 1
  funext T
  obtain ⟨M, hM⟩ : ∃ M : Matrix (D₁ ⊕ D₂) (D₁ ⊕ D₂) k, M = fromBlocks 1 0 (-bᵀ) 1 := ⟨_, rfl⟩
  have h0 : (invT (unip b)).val = M := by
    rw [hM]
    show (fromBlocks 1 (-b) 0 1)ᵀ = _
    simp [fromBlocks_transpose]
  rw [h0]
  have h1 : setCols _ (Y * M) T = setCols _ Y T := by
    ext i (j | j) <;> simp [hM, setCols, Assignment.block, Matrix.mul_apply, one_apply]
  have h2 : pairCols _ (Y * M) T =
      -trace ((setCols _ Y T).toCols₁ * b * (setCols _ Y T).toCols₂ᵀ) + pairCols _ Y T := by
    rw [pair_one, pair_one, trace, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [diag_apply, Matrix.mul_assoc, Matrix.mul_apply, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [hM, setCols, Assignment.block, Matrix.mul_apply, one_apply, toCols₁, toCols₂, mul_comm (b _ _)]
    ring
  rw [h1, h2, AddChar.map_add_eq_mul, Circle.coe_mul]
  ring

theorem omA_unip_fourier_inv (ψ : AddChar k Circle) (m : Measure k) (ν β : kˣ →* ℂˣ) (b : Matrix D₁ D₂ k)
    (Φ : Matrix A (D₁ ⊕ D₂) k → ℂ) :
    omA ν β 1 (unip b) (fourierInt ψ⁻¹ m (Assignment.one.block D₁ D₂) Φ) =
      fourierInt ψ⁻¹ m (Assignment.one.block D₁ D₂)
        fun T => (ψ (trace (T.toCols₁ * b * T.toCols₂ᵀ)) : ℂ) * Φ T := by
  rw [omA_unip_fourier]
  simp [AddChar.inv_apply]

end GlobalTheory.SplitFlip.Model
