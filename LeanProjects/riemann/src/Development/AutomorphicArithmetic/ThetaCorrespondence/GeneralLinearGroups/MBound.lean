import Mathlib
import Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.CasselmanSuffTemp
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.BernsteinUnitaryProductIrreducible
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivProdIrrTw
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsAverage
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactOpenSubgroupsBasis
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup

open Filter Topology GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult UpperTheory.Lit.Cas

private theorem abs_bound {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V]
    [Module ℂ V] (σ : Representation ℂ G V) (ha : IsAdmissible σ) (hu : IsUnitarisable σ) (K : Subgroup G)
    (ho : IsOpen (K : Set G)) (hc : IsCompact (K : Set G)) (μ : V →ₗ[ℂ] ℂ) (v : V) :
    ∃ C : ℝ, ∀ g, (∀ x ∈ K, μ (σ x (σ g v)) = μ (σ g v)) → ‖μ (σ g v)‖ ≤ C := by
  obtain ⟨B, h1, h2, h3⟩ := hu
  let c : InnerProductSpace.Core ℂ V :=
    { inner := fun x y => B y x
      conj_inner_symm := fun x y => (h1 x y).symm
      re_inner_nonneg := fun x => by
        by_cases hx : x = 0
        · simp [hx]
        · exact (h2 x hx).le
      add_left := fun x y z => map_add (B z) x y
      smul_left := fun x y r => by
        show B y (r • x) = _
        rw [LinearMap.map_smulₛₗ, smul_eq_mul]
      definite := fun x hx => by
        by_contra h
        have := h2 x h
        have hx' : B x x = 0 := hx
        simp [hx'] at this }
  letI : NormedAddCommGroup V := c.toNormedAddCommGroup
  letI : InnerProductSpace ℂ V := InnerProductSpace.ofCore c.toCore
  have hin : ∀ x y : V, inner ℂ x y = B y x := fun _ _ => rfl
  have := ha.2 K ho hc
  let ν := LinearMap.toContinuousLinearMap (μ ∘ₗ (fixed σ K).subtype)
  have hn : ∀ g w, ‖σ g w‖ = ‖w‖ := fun g w => by
    rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), norm_eq_sqrt_re_inner (𝕜 := ℂ), hin, hin, h3]
  refine ⟨‖ν‖ * ‖v‖, fun g hg => ?_⟩
  obtain ⟨w, hw, hw'⟩ := GlobalTheory.WordGrowth.exists_average ha.1 hc (σ g v)
  have e1 := hw' μ hg
  have e2 : B w w = B (σ g v) w := hw' (B.flip w) fun j hj => by
    have : σ j w = w := by simpa using hw ⟨j, hj⟩
    show B (σ j (σ g v)) w = B (σ g v) w
    conv_lhs => rw [← this]
    exact h3 _ _ _
  have e3 : ‖w‖ ≤ ‖v‖ := by
    have a1 : ‖w‖ * ‖w‖ ≤ ‖w‖ * ‖v‖ := by
      have := norm_inner_le_norm (𝕜 := ℂ) w (σ g v)
      rw [hin, ← e2, ← hin, hn, inner_self_eq_norm_sq_to_K] at this
      simpa [sq] using this
    by_contra hlt
    push Not at hlt
    nlinarith [norm_nonneg v]
  rw [← e1]
  exact (ν.le_opNorm ⟨w, hw⟩).trans (mul_le_mul_of_nonneg_left e3 (norm_nonneg _))

private theorem geo {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {a b n : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype n] [DecidableEq n]
    (e : a ⊕ b ≃ n) (t : kˣ) (ht : Tendsto (fun i : ℕ => (t : k) ^ i) atTop (𝓝 0))
    (U : Set (GL n k)) (hU : U ∈ 𝓝 (1 : GL n k)) :
    ∀ᶠ x in 𝓝 (1 : GL n k), ∀ i : ℕ, ∃ u ∈ unipRad k (two e), ∃ y ∈ U,
      x * emb₂ k e (Matrix.GeneralLinearGroup.scalar a t, 1) ^ i =
        u * emb₂ k e (Matrix.GeneralLinearGroup.scalar a t, 1) ^ i * y := by
  obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  rw [(GlobalTheory.SplitFlip.isEmbedding_val_GL (k := k) (n := n)).nhds_eq_comap, mem_comap] at hU
  obtain ⟨O, hO, hOU⟩ := hU
  let M : GL n k → Matrix (a ⊕ b) (a ⊕ b) k := fun x => x.val.submatrix e e
  have hM : Continuous M := Units.continuous_val.matrix_submatrix _ _
  have hM1 : M 1 = 1 := by simp [M]
  have c11 : Continuous fun x => (M x).toBlocks₁₁ := hM.matrix_submatrix Sum.inl Sum.inl
  have c12 : Continuous fun x => (M x).toBlocks₁₂ := hM.matrix_submatrix Sum.inl Sum.inr
  have c21 : Continuous fun x => (M x).toBlocks₂₁ := hM.matrix_submatrix Sum.inr Sum.inl
  have c22 : Continuous fun x => (M x).toBlocks₂₂ := hM.matrix_submatrix Sum.inr Sum.inr
  have v11 : (M 1).toBlocks₁₁ = 1 := by rw [hM1, ← Matrix.fromBlocks_one]; rfl
  have v12 : (M 1).toBlocks₁₂ = 0 := by rw [hM1, ← Matrix.fromBlocks_one]; rfl
  have v21 : (M 1).toBlocks₂₁ = 0 := by rw [hM1, ← Matrix.fromBlocks_one]; rfl
  have v22 : (M 1).toBlocks₂₂ = 1 := by rw [hM1, ← Matrix.fromBlocks_one]; rfl
  have cinv : ContinuousAt (fun x => (M x).toBlocks₂₂⁻¹) 1 := by
    refine ContinuousAt.comp (g := fun A : Matrix b b k => A⁻¹) (continuousAt_matrix_inv _ ?_) c22.continuousAt
    rw [Ring.inverse_eq_inv', v22, Matrix.det_one]
    exact continuousAt_inv₀ one_ne_zero
  let H : (GL n k × k) × Matrix b b k → Matrix n n k := fun p =>
    (Matrix.fromBlocks ((M p.1.1).toBlocks₁₁ - (M p.1.1).toBlocks₁₂ * p.2 * (M p.1.1).toBlocks₂₁) 0
      (p.1.2 • (M p.1.1).toBlocks₂₁) (M p.1.1).toBlocks₂₂).submatrix e.symm e.symm
  have hp : Continuous fun p : (GL n k × k) × Matrix b b k => p.1.1 := continuous_fst.fst
  have hH : Continuous H :=
    (Continuous.matrix_fromBlocks ((c11.comp hp).sub (((c12.comp hp).matrix_mul continuous_snd).matrix_mul
      (c21.comp hp))) continuous_const (continuous_fst.snd.smul (c21.comp hp)) (c22.comp hp)).matrix_submatrix _ _
  have h1 : ∀ᶠ x in 𝓝 (1 : GL n k), ∀ s ∈ insert (0 : k) (Set.range fun i : ℕ => (t : k) ^ i),
      H ((x, s), (M x).toBlocks₂₂⁻¹) ∈ O := by
    refine ht.isCompact_insert_range.eventually_forall_of_forall_eventually fun s _ => ?_
    have hc : ContinuousAt (fun z : GL n k × k => H (z, (M z.1).toBlocks₂₂⁻¹)) (1, s) :=
      hH.continuousAt.comp (continuousAt_id.prodMk (cinv.comp_of_eq continuousAt_fst rfl))
    refine hc.preimage_mem_nhds ?_
    simpa [H, v11, v12, v21, v22] using hO
  have h2 : ∀ᶠ x in 𝓝 (1 : GL n k), (M x).toBlocks₂₂.det ≠ 0 :=
    c22.matrix_det.continuousAt.eventually_ne (by simp [v22])
  filter_upwards [h1, h2] with x hx hd i
  set Z := (M x).toBlocks₁₂ * (M x).toBlocks₂₂⁻¹ with hZ
  let u : GL n k := ⟨(Matrix.fromBlocks 1 Z 0 1).submatrix e.symm e.symm,
    (Matrix.fromBlocks 1 (-Z) 0 1).submatrix e.symm e.symm,
    by simp [Matrix.fromBlocks_multiply], by simp [Matrix.fromBlocks_multiply]⟩
  have hu : u ∈ unipRad k (two e) := by
    refine mem_unipRad.2 ⟨(mem_parab_two k).2 fun j i => by simp [u], ?_⟩
    rintro (_ | _) i j <;> simp [u]
  set d := emb₂ k e (Matrix.GeneralLinearGroup.scalar a t, 1) ^ i with hd'
  have hdv : d.val = (Matrix.fromBlocks (((t : k) ^ i) • (1 : Matrix a a k)) 0 0 1).submatrix e.symm e.symm := by
    rw [hd', ← map_pow, val_emb₂, Prod.pow_mk, ← map_pow, one_pow]
    simp [Matrix.GeneralLinearGroup.scalar, Matrix.smul_one_eq_diagonal, Matrix.diagonal_pow, Pi.pow_def]
  have hx' : x.val = (Matrix.fromBlocks (M x).toBlocks₁₁ (M x).toBlocks₁₂ (M x).toBlocks₂₁
      (M x).toBlocks₂₂).submatrix e.symm e.symm := by
    rw [Matrix.fromBlocks_toBlocks]; simp [M]
  have key : (u * d).val * H ((x, (t : k) ^ i), (M x).toBlocks₂₂⁻¹) = (x * d).val := by
    rw [Units.val_mul, Units.val_mul, hdv]
    conv_rhs => rw [hx']
    have hZD : Z * (M x).toBlocks₂₂ = (M x).toBlocks₁₂ := by
      rw [hZ, Matrix.nonsing_inv_mul_cancel_right _ _ (Ne.isUnit hd)]
    simp only [u, H, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply, ← hZ]
    simp [hZD, smul_sub]
  refine ⟨u, hu, (u * d)⁻¹ * (x * d), hOU ?_, by group⟩
  have : ((u * d)⁻¹ * (x * d)).val = H ((x, (t : k) ^ i), (M x).toBlocks₂₂⁻¹) := by
    rw [Units.val_mul, ← key, Units.inv_mul_cancel_left]
  show ((u * d)⁻¹ * (x * d)).val ∈ O
  rw [this]
  exact hx _ (Or.inr ⟨i, rfl⟩)

theorem UpperTheory.Lit.Mix.bound :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (m n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (W₁ : Type) [AddCommGroup W₁] [Module ℂ W₁] (W₂ : Type) [AddCommGroup W₂] [Module ℂ W₂] (σ : Representation ℂ (GL (Fin (m + n)) k) V) (π₁ : Representation ℂ (GL (Fin m) k) W₁) (π₂ : Representation ℂ (GL (Fin n) k) W₂), IsAdmissible σ → Nontrivial V → IsUnitarisable σ → (∃ f : σ.IntertwiningMap (prod₂ π₁ π₂), Function.Injective f) → ∀ (t : kˣ), Tendsto (fun i : ℕ => (t : k) ^ i) atTop (𝓝 0) → ∀ c : ℂ, (∀ v, π₁ (Matrix.GeneralLinearGroup.scalar (Fin m) t) v = c • v) → ‖c * ((absPow k (((m * n : ℕ) : ℂ) / 2) t : ℂˣ) : ℂ)‖ ≤ 1 := by
  intro k _ _ _ _ m n V _ _ W₁ _ _ W₂ _ _ σ π₁ π₂ ha _ hu ⟨f, hf⟩ t ht c hc
  set γ : ℂ := c * ((absPow k (((m * n : ℕ) : ℂ) / 2) t : ℂˣ) : ℂ) with hγ
  let e := stdSum (rfl : m + n = m + n)
  let φ : V →ₗ[ℂ] TensorProduct ℂ W₁ W₂ :=
    { toFun := fun v => (f v).1.1 1
      map_add' := fun v w => by rw [map_add]; rfl
      map_smul' := fun r v => by rw [map_smul]; rfl }
  have hφ : ∀ g v, φ (σ g v) = (f v).1.1 g := fun g v => by
    show (f (σ g v)).1.1 1 = _
    rw [f.isIntertwining]
    show (f v).1.1 (1 * g) = _
    rw [one_mul]
  let ρ := (extTensor π₁ π₂).comp (leviTwo k (Fin m) (Fin n)).symm.toMonoidHom
  have hP : ∀ (p : parab k (two e)) v, φ (σ p v) =
      (deltaHalf k _ (leviProj k (two e) p) : ℂ) • ρ (leviProj k (two e) p) (φ v) := fun p v => by
    rw [hφ]
    have := parInd_law (two e) ρ (f v) p 1
    rwa [mul_one] at this
  have hN : ∀ u ∈ unipRad k (two e), ∀ v, φ (σ u v) = φ v := fun u hu v => by
    have h := hP ⟨u, unipRad_le_parab k _ hu⟩ v
    rw [(coe_mem_unipRad k ⟨u, unipRad_le_parab k _ hu⟩).1 hu] at h
    simpa using h
  let d := emb₂ k e (Matrix.GeneralLinearGroup.scalar (Fin m) t, 1)
  have hd : ∀ v, φ (σ d v) = γ • φ v := fun v => by
    have h := hP ⟨_, leviEmb_mem_parab k (two e)
      (leviTwo k (Fin m) (Fin n) (Matrix.GeneralLinearGroup.scalar (Fin m) t, 1))⟩ v
    rw [leviProj_leviEmb, deltaHalf_two] at h
    have h1 : ∀ w, extTensor π₁ π₂ (Matrix.GeneralLinearGroup.scalar (Fin m) t, 1) w = c • w := fun w => by
      induction w using TensorProduct.induction_on with
      | zero => simp
      | tmul x y => simp [hc, TensorProduct.smul_tmul']
      | add x y hx hy => rw [map_add, hx, hy, smul_add]
    have h2 : Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin m) t) = t ^ m := by
      ext; simp [Matrix.GeneralLinearGroup.scalar]
    refine h.trans ?_
    refine (congrArg _ (h1 (φ v))).trans ?_
    rw [smul_smul, hγ, mul_comm c]
    congr 2
    rw [map_one, map_one, mul_one, h2, map_pow, Units.val_pow_eq_pow_val, val_absPow, val_absPow,
      ← Complex.cpow_nat_mul]
    congr 1
    simp [mul_div_assoc]
  have hdi : ∀ (i : ℕ) v, φ (σ (d ^ i) v) = γ ^ i • φ v := fun i v => by
    induction i with
    | zero => simp
    | succ i ih => rw [pow_succ', map_mul, Module.End.mul_apply, hd, ih, smul_smul, pow_succ']
  obtain ⟨v, hv⟩ : ∃ v, φ v ≠ 0 := by
    by_contra h
    push Not at h
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    refine hv (hf ?_)
    rw [map_zero]
    exact Subtype.ext (Subtype.ext (funext fun g => (hφ g v).symm.trans (h _)))
  obtain ⟨l, hl⟩ : ∃ l : Module.Dual ℂ (TensorProduct ℂ W₁ W₂), l (φ v) ≠ 0 := by
    by_contra h
    push Not at h
    exact hv ((Module.forall_dual_apply_eq_zero_iff ℂ _).1 h)
  obtain ⟨K, ho, hK, hKU⟩ := GlobalTheory.CompanionTheory.SmGL.exists_compact_open_subgroup_subset k (m + n) _
    (geo e t ht _ ((ha.1 v).mem_nhds (by simp)))
  obtain ⟨C, hC⟩ := abs_bound σ ha hu K ho hK (l ∘ₗ φ) v
  have hb : ∀ i : ℕ, ‖γ‖ ^ i * ‖l (φ v)‖ ≤ C := fun i => by
    have h := hC (d ^ i) fun x hx => by
      obtain ⟨u, hu, y, hy, h⟩ := hKU hx i
      have hy' : σ y v = v := hy
      have h' : σ x (σ (d ^ i) v) = σ u (σ (d ^ i) v) := by
        rw [← Module.End.mul_apply, ← map_mul, h, map_mul, map_mul, Module.End.mul_apply, hy',
          Module.End.mul_apply]
      rw [h', LinearMap.comp_apply, hN u hu, LinearMap.comp_apply]
    rwa [LinearMap.comp_apply, hdi, map_smul, norm_smul, norm_pow] at h
  by_contra hlt
  push Not at hlt
  have := (tendsto_pow_atTop_atTop_of_one_lt hlt).atTop_mul_const (norm_pos_iff.2 hl)
  obtain ⟨i, hi⟩ := (this.eventually_gt_atTop C).exists
  exact absurd (hb i) hi.not_ge
