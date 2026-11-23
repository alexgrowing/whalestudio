import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlockTriangularOneAddMat
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwasawaBlockTriangular
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel MeasureTheory Matrix
open scoped TensorProduct ENNReal

namespace GlobalTheory.SmGL.UnitInd

section Tensor

@[reducible] def core {X : Type} [AddCommGroup X] [Module ℂ X] (B : X →ₗ[ℂ] X →ₗ⋆[ℂ] ℂ)
    (hs : ∀ v w, B w v = starRingEnd ℂ (B v w)) (hp : ∀ v, v ≠ 0 → 0 < (B v v).re) :
    InnerProductSpace.Core ℂ X where
  inner v w := B w v
  conj_inner_symm v w := (hs _ _).symm
  re_inner_nonneg v := by
    by_cases h : v = 0
    · simp [h]
    · exact (hp v h).le
  add_left x y z := map_add _ _ _
  smul_left x y r := by simp
  definite v h := by
    by_contra hv
    simpa [h] using hp v hv

variable {G H V W : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem isUnitarisable_comp {ρ : Representation ℂ G V} (h : IsUnitarisable ρ) (s : H →* G) :
    IsUnitarisable (ρ.comp s : Representation ℂ H V) := by
  obtain ⟨B, h1, h2, h3⟩ := h
  exact ⟨B, h1, h2, fun g => h3 (s g)⟩

theorem isUnitarisable_extTensor {ρ : Representation ℂ G V} {σ : Representation ℂ H W}
    (h₁ : IsUnitarisable ρ) (h₂ : IsUnitarisable σ) : IsUnitarisable (extTensor ρ σ) := by
  obtain ⟨B, b1, b2, b3⟩ := h₁
  obtain ⟨C, c1, c2, c3⟩ := h₂
  letI : InnerProductSpace.Core ℂ V := core B b1 b2
  letI : InnerProductSpace.Core ℂ W := core C c1 c2
  letI : NormedAddCommGroup V := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ)
  letI : NormedAddCommGroup W := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ)
  letI : InnerProductSpace ℂ V := InnerProductSpace.ofCore _
  letI : InnerProductSpace ℂ W := InnerProductSpace.ofCore _
  refine ⟨(innerₛₗ ℂ (E := V ⊗[ℂ] W)).flip, fun v w => (inner_conj_symm (𝕜 := ℂ) v w).symm, fun v hv => ?_, fun g v w => ?_⟩
  · exact (re_inner_self_pos (𝕜 := ℂ)).2 hv
  · show inner ℂ (extTensor ρ σ g w) (extTensor ρ σ g v) = inner ℂ w v
    induction v with
    | zero => simp
    | add x y hx hy => simp only [map_add, inner_add_right, hx, hy]
    | tmul v v' =>
      induction w with
      | zero => simp
      | add x y hx hy => simp only [map_add, inner_add_left, hx, hy]
      | tmul w w' =>
        rw [extTensor_tmul, extTensor_tmul, TensorProduct.inner_tmul, TensorProduct.inner_tmul]
        exact congrArg₂ _ (b3 _ _ _) (c3 _ _ _)

theorem exists_orthonormal (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ)
    (hs : ∀ v w, B w v = starRingEnd ℂ (B v w)) (hp : ∀ v, v ≠ 0 → 0 < (B v v).re) {S : Set V}
    (hS : S.Finite) : ∃ (d : ℕ) (b : Fin d → V), (∀ i j, B (b i) (b j) = if i = j then 1 else 0) ∧
      ∀ v ∈ S, ∃ c : Fin d → ℂ, v = ∑ i, c i • b i := by
  letI : InnerProductSpace.Core ℂ V := core B hs hp
  letI : NormedAddCommGroup V := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ)
  letI : InnerProductSpace ℂ V := InnerProductSpace.ofCore _
  haveI : FiniteDimensional ℂ (Submodule.span ℂ S) := FiniteDimensional.span_of_finite ℂ hS
  let b := stdOrthonormalBasis ℂ (Submodule.span ℂ S)
  refine ⟨_, fun i => b i, fun i j => ?_, fun v hv => ⟨b.repr ⟨v, Submodule.subset_span hv⟩, ?_⟩⟩
  · exact (orthonormal_iff_ite.1 b.orthonormal j i).trans (by simp only [eq_comm])
  · simpa using (congrArg Subtype.val (b.sum_repr ⟨v, Submodule.subset_span hv⟩)).symm

variable {α : Type} [Fintype α] {X : α → Type} [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)]

theorem exists_piForm (B : ∀ a, X a →ₗ[ℂ] X a →ₗ⋆[ℂ] ℂ) (hs : ∀ a v w, B a w v = starRingEnd ℂ (B a v w)) :
    ∃ C : (⨂[ℂ] a, X a) →ₗ[ℂ] (⨂[ℂ] a, X a) →ₗ⋆[ℂ] ℂ, ∀ x y,
      C (PiTensorProduct.tprod ℂ x) (PiTensorProduct.tprod ℂ y) = ∏ a, B a (x a) (y a) := by
  let F : (∀ a, X a) → (⨂[ℂ] a, X a) →ₗ⋆[ℂ] ℂ := fun x =>
    (starLinearEquiv ℂ (A := ℂ)).toLinearMap.comp (PiTensorProduct.lift
      ((MultilinearMap.mkPiAlgebra ℂ α ℂ).compLinearMap fun a => (B a).flip (x a)))
  have hF : ∀ x y, F x (PiTensorProduct.tprod ℂ y) =
      (MultilinearMap.mkPiAlgebra ℂ α ℂ).compLinearMap (fun a => (B a).flip (y a)) x := fun x y => by
    simp [F, ← hs]
  refine ⟨PiTensorProduct.lift ⟨F, fun x i u v => ?_, fun x i c u => ?_⟩, fun x y => ?_⟩
  · refine LinearMap.ext_on_range PiTensorProduct.span_tprod_eq_top fun y => ?_
    rw [LinearMap.add_apply, hF, hF, hF, MultilinearMap.map_update_add]
  · refine LinearMap.ext_on_range PiTensorProduct.span_tprod_eq_top fun y => ?_
    rw [LinearMap.smul_apply, hF, hF, MultilinearMap.map_update_smul]
  · rw [PiTensorProduct.lift.tprod]
    exact (hF x y).trans (by simp)

theorem isUnitarisable_piTensor {Γ : α → Type} [∀ a, Group (Γ a)] {ρ : ∀ a, Representation ℂ (Γ a) (X a)}
    (h : ∀ a, IsUnitarisable (ρ a)) : IsUnitarisable (piTensor ρ) := by
  classical
  choose B hs hp hi using h
  obtain ⟨C, hC⟩ := exists_piForm B hs
  have ind : ∀ (P : (⨂[ℂ] a, X a) → (⨂[ℂ] a, X a) → Prop),
      (∀ x y, P (PiTensorProduct.tprod ℂ x) (PiTensorProduct.tprod ℂ y)) →
      (∀ (c : ℂ) x y, P x y → P (c • x) y) → (∀ (c : ℂ) x y, P x y → P x (c • y)) →
      (∀ x x' y, P x y → P x' y → P (x + x') y) → (∀ x y y', P x y → P x y' → P x (y + y')) →
      ∀ x y, P x y := by
    intro P h0 h1 h2 h3 h4 x y
    induction x using PiTensorProduct.induction_on with
    | add x x' hx hx' => exact h3 _ _ _ hx hx'
    | smul_tprod c x =>
      induction y using PiTensorProduct.induction_on with
      | add y y' hy hy' => exact h4 _ _ _ hy hy'
      | smul_tprod d y => exact h1 _ _ _ (h2 _ _ _ (h0 _ _))
  refine ⟨C, ind _ ?_ ?_ ?_ ?_ ?_, fun v hv => ?_, fun g => ind _ ?_ ?_ ?_ ?_ ?_⟩
  · intro x y
    simp [hC, ← hs]
  · intro c x y h; simp [h]
  · intro c x y h; simp [h]
  · intro x x' y h h'; simp [h, h']
  · intro x x' y h h'; simp [h, h']
  · have hv' : v ∈ Submodule.span ℂ (Set.range (PiTensorProduct.tprod ℂ (s := X))) := by
      rw [PiTensorProduct.span_tprod_eq_top]; trivial
    obtain ⟨N, r, x, hx⟩ := Submodule.mem_span_set'.1 hv'
    choose y hy using fun i => (x i).2
    choose d b hb hc using fun a => exists_orthonormal (B a) (hs a) (hp a)
      (Set.finite_range fun i => y i a)
    choose c hc using fun i a => hc a (y i a) ⟨i, rfl⟩
    let E : (∀ a, Fin (d a)) → ⨂[ℂ] a, X a := fun I => PiTensorProduct.tprod ℂ fun a => b a (I a)
    have hmem : v ∈ Submodule.span ℂ (Set.range E) := by
      rw [← hx]
      refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
      rw [← hy, show y i = fun a => ∑ j, c i a j • b a j from funext (hc i), MultilinearMap.map_sum]
      refine Submodule.sum_mem _ fun I _ => ?_
      rw [MultilinearMap.map_smul_univ]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨I, rfl⟩)
    obtain ⟨t, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hmem
    have hE : ∀ I J, C (E I) (E J) = if I = J then 1 else 0 := fun I J => by
      simp only [E, hC, hb, Finset.prod_ite_zero, Finset.prod_const_one, Finset.mem_univ, true_imp_iff,
        funext_iff]
    have h1 : C (∑ I, t I • E I) (∑ I, t I • E I) = ((∑ I, Complex.normSq (t I) : ℝ) : ℂ) := by
      simp [hE, Complex.mul_conj, mul_comm]
    rw [h1, Complex.ofReal_re]
    obtain ⟨I, hI⟩ : ∃ I, t I ≠ 0 := by
      by_contra! h0
      simp [h0] at hv
    exact Finset.sum_pos' (fun _ _ => Complex.normSq_nonneg _) ⟨I, Finset.mem_univ _, Complex.normSq_pos.2 hI⟩
  · intro x y
    simp [hC, hi]
  · intro c x y h; simp [h]
  · intro c x y h; simp [h]
  · intro x x' y h h'; simp [h, h']
  · intro x x' y h h'; simp [h, h']

end Tensor

section Average

variable {G X : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G] [MeasurableSpace X]

theorem lintegral_average (μ : Measure G) [SFinite μ] [μ.IsMulLeftInvariant] (ρ : Measure X) [SFinite ρ]
    {K L : Set G} (hK : MeasurableSet K) (hL : MeasurableSet L) {j : X → G} (hj : Measurable j)
    {δ : X → ℝ≥0∞} (hδ : Measurable δ) {φ : G → ℝ≥0∞} (hφ : Measurable φ)
    (hlaw : ∀ y x, φ ((j y)⁻¹ * x) = δ y * φ x) {c : ℝ≥0∞}
    (ha : ∀ x, ∫⁻ y, L.indicator 1 (j y * x) ∂ρ = c)
    (hb : ∀ x, ∫⁻ y, K.indicator 1 ((j y)⁻¹ * x) * δ y ∂ρ = c) :
    c * ∫⁻ x in K, φ x ∂μ = c * ∫⁻ x in L, φ x ∂μ := by
  have mK : Measurable (K.indicator (1 : G → ℝ≥0∞)) := measurable_one.indicator hK
  have mL : Measurable (L.indicator (1 : G → ℝ≥0∞)) := measurable_one.indicator hL
  have e : ∀ {S : Set G}, MeasurableSet S →
      c * ∫⁻ x in S, φ x ∂μ = ∫⁻ x, (S.indicator 1 x * φ x) * c ∂μ := fun {S} hS => by
    rw [lintegral_mul_const (f := fun x => S.indicator 1 x * φ x) _ ((measurable_one.indicator hS).mul hφ), mul_comm,
      ← lintegral_indicator hS]
    congr 2
    funext x
    by_cases h : x ∈ S <;> simp [h]
  rw [e hK, e hL]
  calc ∫⁻ x, (K.indicator 1 x * φ x) * c ∂μ
      = ∫⁻ x, ∫⁻ y, (K.indicator 1 x * φ x) * L.indicator 1 (j y * x) ∂ρ ∂μ := by
        refine lintegral_congr fun x => ?_
        rw [lintegral_const_mul (f := fun y => L.indicator 1 (j y * x)) _ (mL.comp (hj.mul_const x)), ha]
    _ = ∫⁻ y, ∫⁻ x, (K.indicator 1 x * φ x) * L.indicator 1 (j y * x) ∂μ ∂ρ :=
        lintegral_lintegral_swap (((mK.mul hφ).comp measurable_fst).mul
          (mL.comp ((hj.comp measurable_snd).mul measurable_fst))).aemeasurable
    _ = ∫⁻ y, ∫⁻ x, (L.indicator 1 x * φ x) * (K.indicator 1 ((j y)⁻¹ * x) * δ y) ∂μ ∂ρ := by
        refine lintegral_congr fun y => ?_
        rw [← lintegral_mul_left_eq_self _ (j y)⁻¹]
        refine lintegral_congr fun x => ?_
        rw [hlaw, mul_inv_cancel_left]
        ring
    _ = ∫⁻ x, ∫⁻ y, (L.indicator 1 x * φ x) * (K.indicator 1 ((j y)⁻¹ * x) * δ y) ∂ρ ∂μ :=
        (lintegral_lintegral_swap (((mL.mul hφ).comp measurable_fst).mul
          ((mK.comp ((hj.comp measurable_snd).inv.mul measurable_fst)).mul
            (hδ.comp measurable_snd))).aemeasurable).symm
    _ = _ := by
        refine lintegral_congr fun x => ?_
        rw [lintegral_const_mul (f := fun y => K.indicator 1 ((j y)⁻¹ * x) * δ y) _
          ((mK.comp (hj.inv.mul_const x)).mul hδ), hb]

end Average

theorem indicator_congr_iff {A B : Type} {S : Set A} {T : Set B} {a : A} {b : B} {f : A → ℝ≥0∞} {g : B → ℝ≥0∞}
    (h : a ∈ S ↔ b ∈ T) (h' : f a = g b) : S.indicator f a = T.indicator g b := by
  by_cases hb : b ∈ T
  · rw [Set.indicator_of_mem hb, Set.indicator_of_mem (h.2 hb), h']
  · rw [Set.indicator_of_notMem hb, Set.indicator_of_notMem (mt h.1 hb)]

theorem isLocallyConstant_of_open {G Y : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {f : G → Y}
    {U : Set G} (hU : IsOpen U) (h1 : (1 : G) ∈ U) (h : ∀ x, ∀ u ∈ U, f (x * u) = f x) : IsLocallyConstant f := by
  refine (IsLocallyConstant.iff_eventually_eq f).2 fun x => ?_
  have ho : IsOpen ((fun y => x⁻¹ * y) ⁻¹' U) := hU.preimage (by fun_prop)
  filter_upwards [ho.mem_nhds (x := x) (by simpa using h1)] with y hy
  simpa using h x _ hy

section Local

open GlobalTheory.SplitFlip GlobalTheory.SmGL.UnipHaar

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] (e : (Σ a, m a) ≃ n)

theorem unip_mul_levi_mem_KO (u : unipRad k e) (g : Levi k m) :
    (u : GL n k) * leviEmb k e g ∈ KO k n ↔ (u : GL n k) ∈ KO k n ∧ ∀ a, g a ∈ KO k (m a) := by
  have key : (∀ a, g a ∈ KO k (m a)) → leviEmb k e g ∈ KO k n := fun h => by
    have aux : ∀ t : Levi k m, (∀ a i j, (t a).val i j ∈ 𝒪[k]) → ∀ i j, (leviEmb k e t).val i j ∈ 𝒪[k] := by
      intro t ht i j
      obtain ⟨⟨a, i⟩, rfl⟩ := e.surjective i
      obtain ⟨⟨b, j⟩, rfl⟩ := e.surjective j
      by_cases hab : a = b
      · subst hab
        rw [leviEmb_apply_same]; exact ht a i j
      · rw [leviEmb_apply_ne k e t hab]; exact zero_mem _
    refine (mem_KO_iff _).2 ⟨aux g fun a => ((mem_KO_iff _).1 (h a)).1, ?_⟩
    rw [← map_inv]
    exact aux g⁻¹ fun a => ((mem_KO_iff _).1 (h a)).2
  refine ⟨fun h => ?_, fun h => mul_mem h.1 (key h.2)⟩
  let p : parab k e := ⟨u, unipRad_le_parab k e u.2⟩ * ⟨_, leviEmb_mem_parab k e g⟩
  have hp : leviProj k e p = g := by
    rw [map_mul, (coe_mem_unipRad k _).1 u.2, leviProj_leviEmb, one_mul]
  have hg : ∀ a, g a ∈ KO k (m a) := fun a => by
    obtain ⟨h1, h2⟩ := (mem_KO_iff _).1 h
    refine (mem_KO_iff _).2 ⟨fun i j => ?_, fun i j => ?_⟩
    · rw [← hp]; exact h1 _ _
    · rw [← hp, ← Pi.inv_apply, ← map_inv]; exact h2 _ _
  exact ⟨(mul_mem_cancel_right (key hg)).1 h, hg⟩

theorem exists_iwasawa (x : GL n k) :
    ∃ (u : unipRad k e) (g : Levi k m), ∃ w ∈ KO k n, x = u * leviEmb k e g * w := by
  let r := (monoEquivOfFin α rfl).symm
  obtain ⟨b, hb, w, hw, rfl⟩ := iwasawa_blockTriangular k n (fun i => r (blk e i)) x
  have hp : b ∈ parab k e := fun i j h => hb (r.strictMono h)
  obtain ⟨u, hu, h⟩ := exists_levi_mul_unip k e ⟨b, hp⟩
  refine ⟨conj e (leviProj k e ⟨b, hp⟩) ⟨u, hu⟩, leviProj k e ⟨b, hp⟩, w, hw, ?_⟩
  simp only [conj, inv_mul_cancel_right]
  rw [← h]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

theorem det_rmat_unip (u : unipRad k e) : (rmat e ((u : GL n k) : Matrix n n k)).det = 1 := by
  rw [← det_transpose, det_of_blocks _ (fun p : Idx e => blk e p.1.2) ?_ (fun a => {j : n // blk e j < a})
    (fun _ => 1) (colEquiv e) ?_]
  · simp
  · intro p q h
    simp [rmat, (mem_unipRad.1 u.2).1 h]
  · intro a x y
    exact if_congr (eq_comm.trans Subtype.ext_iff.symm) ((mem_unipRad.1 u.2).2 a x.1 y.1) rfl

theorem isLocallyConstant_modulus : IsLocallyConstant (modulus k m) := by
  refine isLocallyConstant_of_open (isSmoothChar_deltaHalf k) (one_mem _) fun x u hu => ?_
  have h : deltaHalf k m (x * u) = deltaHalf k m x := by rw [map_mul, show deltaHalf k m u = 1 from hu, mul_one]
  have h2 := congrArg Units.val h
  rw [val_deltaHalf, val_deltaHalf, Complex.ofReal_inj] at h2
  exact (Real.sqrt_inj (modulus_pos k _).le (modulus_pos k _).le).1 h2

theorem modulus_mul_inv (g : Levi k m) : modulus k m g * modulus k m g⁻¹ = 1 := by
  have : ∀ a, ((distribHaarChar k (GeneralLinearGroup.det (g a)) : NNReal) : ℝ) ≠ 0 := fun a => (nabs_pos' k _).ne'
  simp only [modulus, nabs, ← Finset.prod_mul_distrib, Pi.inv_apply, map_inv, NNReal.coe_inv, ← mul_zpow,
    mul_inv_cancel₀ (this _), _root_.one_zpow, Finset.prod_const_one]

variable [MeasurableSpace k] [BorelSpace k]

theorem isMulRightInvariant_map (ν : Measure k) [ν.IsAddHaarMeasure] :
    (Measure.map (unipHomeo (R := k) e).symm (Measure.pi fun _ : Idx e => ν)).IsMulRightInvariant := by
  obtain ⟨_, _⟩ := Model.secondCountable_and_t2_local_field (k := k)
  have hΦ : Measurable (unipHomeo (R := k) e).symm := (unipHomeo e).symm.measurable
  refine ⟨fun u => ?_⟩
  have hm : Measurable (rmat e ((u : GL n k) : Matrix n n k)).mulVec :=
    (continuous_const.matrix_mulVec continuous_id).measurable
  have h1 := WeilM.smul_map_mulVec_pi ν _ 1 (det_rmat_unip e u).symm
  rw [map_one, ENNReal.coe_one, one_smul] at h1
  have h2 : (· * u) ∘ (unipHomeo e).symm = (unipHomeo e).symm ∘ ((unipEquiv e u + ·) ∘
      (rmat e ((u : GL n k) : Matrix n n k)).mulVec) :=
    funext fun x => (unipEquiv e).eq_symm_apply.2 (by
      show ent e ((1 + mat e x) * ((u : GL n k) : Matrix n n k)) = unipEquiv e u + (rmat e _).mulVec x
      rw [← ent_mat_mul, add_mul, one_mul]
      rfl)
  rw [Measure.map_map (measurable_mul_const u) hΦ, h2,
    ← Measure.map_map hΦ ((measurable_const_add _).comp hm),
    ← Measure.map_map (measurable_const_add _) hm, h1, map_add_left_eq_self]

theorem lintegral_KO_mul_right (μ : Measure (GL n k)) [μ.IsHaarMeasure] {φ : GL n k → ℝ≥0∞} (hφ : Measurable φ)
    (hlaw : ∀ (p : parab k e) x, φ (p * x) = ENNReal.ofReal (modulus k m (leviProj k e p)) * φ x) (g : GL n k) :
    ∫⁻ x in (KO k n : Set (GL n k)), φ (x * g) ∂μ = ∫⁻ x in (KO k n : Set (GL n k)), φ x ∂μ := by
  obtain ⟨_, _⟩ := Model.secondCountable_and_t2_local_field (k := k)
  haveI : SecondCountableTopology (unipRad k e) := (unipHomeo e).secondCountableTopology
  haveI : LocallyCompactSpace (unipRad k e) := (unipHomeo e).isClosedEmbedding.locallyCompactSpace
  obtain ⟨ν, _, _⟩ : ∃ ν : Measure (unipRad k e), ν.IsHaarMeasure ∧ ν.IsMulRightInvariant :=
    ⟨_, isHaarMeasure_map e Measure.addHaar, isMulRightInvariant_map e Measure.addHaar⟩
  let τ : Measure (Levi k m) := Measure.pi fun _ => Measure.haar
  let N₀ : Set (unipRad k e) := Subtype.val ⁻¹' (KO k n : Set (GL n k))
  let M₀ : Set (Levi k m) := Set.univ.pi fun a => (KO k (m a) : Set (GL (m a) k))
  have hK : MeasurableSet (KO k n : Set (GL n k)) := isOpen_KO.measurableSet
  have hN₀ : IsOpen N₀ := isOpen_KO.preimage continuous_subtype_val
  have hM₀ : IsOpen M₀ := isOpen_set_pi Set.finite_univ fun _ _ => isOpen_KO
  have hNc : IsCompact N₀ := by
    have : IsClosed (unipRad k e : Set (GL n k)) := by
      have h : (unipRad k e : Set (GL n k)) = (⋂ (i) (j) (_ : blk e j < blk e i), {g | g.val i j = 0}) ∩
          ⋂ (a) (i) (j), {g | g.val (e ⟨a, i⟩) (e ⟨a, j⟩) = (1 : Matrix (m a) (m a) k) i j} := by
        ext g
        simp only [SetLike.mem_coe, mem_unipRad, mem_parab, Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq]
      rw [h]
      refine IsClosed.inter ?_ ?_ <;>
        exact isClosed_iInter fun _ => isClosed_iInter fun _ => isClosed_iInter fun _ =>
          isClosed_eq (Units.continuous_val.matrix_elem _ _) continuous_const
    exact this.isClosedEmbedding_subtypeVal.isCompact_preimage isCompact_KO
  have hMc : IsCompact M₀ := isCompact_univ_pi fun _ => isCompact_KO
  have hc0 : ν N₀ * τ M₀ ≠ 0 := mul_ne_zero (hN₀.measure_pos ν ⟨1, one_mem (KO k n)⟩).ne'
    (hM₀.measure_pos τ ⟨1, fun a _ => one_mem (KO k (m a))⟩).ne'
  have hc1 : ν N₀ * τ M₀ ≠ ⊤ := ENNReal.mul_ne_top hNc.measure_lt_top.ne hMc.measure_lt_top.ne
  let j : Levi k m × unipRad k e → GL n k := fun y => y.2 * leviEmb k e y.1
  have hj : Measurable j := ((continuous_subtype_val.comp continuous_snd).mul
    ((continuous_leviEmb k e).comp continuous_fst)).measurable
  let δ : Levi k m × unipRad k e → ℝ≥0∞ := fun y => ENNReal.ofReal (modulus k m y.1⁻¹)
  have hδ : Measurable δ := ((isLocallyConstant_modulus (k := k) (m := m)).continuous.comp
    continuous_fst.inv).measurable.ennreal_ofReal
  have mK : Measurable ((KO k n : Set (GL n k)).indicator (1 : GL n k → ℝ≥0∞)) := measurable_one.indicator hK
  have ha : ∀ x, ∫⁻ y, (KO k n : Set (GL n k)).indicator 1 (j y * x) ∂(τ.prod ν) = ν N₀ * τ M₀ := by
    intro x
    obtain ⟨u, t, w, hw, rfl⟩ := exists_iwasawa e x
    rw [lintegral_prod (fun y => (KO k n : Set (GL n k)).indicator 1 (j y * (u * leviEmb k e t * w)))
      (mK.comp (hj.mul_const _)).aemeasurable, ← measure_preimage_mul_right τ t M₀,
      ← lintegral_indicator_const (measurable_mul_const t hM₀.measurableSet)]
    refine lintegral_congr fun s => ?_
    have h : ∀ v : unipRad k e, j (s, v) * (u * leviEmb k e t * w) ∈ (KO k n : Set (GL n k)) ↔
        v * conj e s u ∈ N₀ ∧ s * t ∈ M₀ := fun v => by
      have : j (s, v) * (u * leviEmb k e t * w) = (v * conj e s u : unipRad k e) * leviEmb k e (s * t) * w := by
        simp [j, conj, mul_assoc]
      rw [this, SetLike.mem_coe, mul_mem_cancel_right hw, unip_mul_levi_mem_KO]
      simp [N₀, M₀]
    by_cases hs : s * t ∈ M₀
    · rw [Set.indicator_of_mem (show s ∈ (· * t) ⁻¹' M₀ from hs), ← measure_preimage_mul_right ν (conj e s u) N₀,
        ← lintegral_indicator_one (measurable_mul_const _ hN₀.measurableSet)]
      refine lintegral_congr fun v => ?_
      exact indicator_congr_iff ((h v).trans (and_iff_left hs)) rfl
    · rw [Set.indicator_of_notMem (show s ∉ (· * t) ⁻¹' M₀ from hs)]
      simp [Set.indicator, h, hs]
  have hb : ∀ x, ∫⁻ y, (KO k n : Set (GL n k)).indicator 1 ((j y)⁻¹ * x) * δ y ∂(τ.prod ν) = ν N₀ * τ M₀ := by
    intro x
    obtain ⟨u, t, w, hw, rfl⟩ := exists_iwasawa e x
    rw [lintegral_prod (fun y => (KO k n : Set (GL n k)).indicator 1 ((j y)⁻¹ * (u * leviEmb k e t * w)) * δ y)
      ((mK.comp (hj.inv.mul_const _)).mul hδ).aemeasurable, ← measure_preimage_mul τ t⁻¹ M₀,
      ← lintegral_indicator_const (measurable_const_mul t⁻¹ hM₀.measurableSet)]
    refine lintegral_congr fun s => ?_
    let T : Set (unipRad k e) := {u | ∃ v ∈ N₀, (u : GL n k) = leviEmb k e s * (v : GL n k) * (leviEmb k e s)⁻¹}
    have hT : T = conj e s⁻¹ ⁻¹' N₀ := by
      ext v
      refine ⟨?_, fun h => ⟨_, h, by simp [conj, mul_assoc]⟩⟩
      rintro ⟨v', hv, h⟩
      simpa [N₀, conj, h, mul_assoc] using hv
    have hTm : MeasurableSet T := hT ▸ (continuous_conj e s⁻¹).measurable hN₀.measurableSet
    have h : ∀ v : unipRad k e, (j (s, v))⁻¹ * (u * leviEmb k e t * w) ∈ (KO k n : Set (GL n k)) ↔
        u⁻¹ * v ∈ T ∧ t⁻¹ * s ∈ M₀ := fun v => by
      have : (j (s, v))⁻¹ * (u * leviEmb k e t * w) =
          ((conj e s⁻¹ (u⁻¹ * v))⁻¹ : unipRad k e) * leviEmb k e (t⁻¹ * s)⁻¹ * w := by
        simp [j, conj, mul_assoc]
      rw [this, SetLike.mem_coe, mul_mem_cancel_right hw, unip_mul_levi_mem_KO, hT, Subgroup.coe_inv, inv_mem_iff]
      simp only [Pi.inv_apply, inv_mem_iff]
      simp [N₀, M₀]
    by_cases hs : t⁻¹ * s ∈ M₀
    · have h1 : ν N₀ = ν T * ENNReal.ofReal (modulus k m s⁻¹) := by
        rw [haar_conj_eq_modulus_mul k α n m e ν s N₀ hN₀.measurableSet, mul_right_comm,
          ← ENNReal.ofReal_mul (modulus_pos k _).le, modulus_mul_inv]
        simp
      rw [Set.indicator_of_mem (show s ∈ (t⁻¹ * ·) ⁻¹' M₀ from hs), h1, ← measure_preimage_mul ν u⁻¹ T,
        ← lintegral_indicator_one (measurable_const_mul _ hTm),
        ← lintegral_mul_const _ (measurable_one.indicator (measurable_const_mul _ hTm))]
      refine lintegral_congr fun v => ?_
      exact congrArg₂ _ (indicator_congr_iff ((h v).trans (and_iff_left hs)) rfl) rfl
    · rw [Set.indicator_of_notMem (show s ∉ (t⁻¹ * ·) ⁻¹' M₀ from hs)]
      simp [Set.indicator, h, hs, -_root_.mul_inv_rev]
  have hL : MeasurableSet ((· * g⁻¹) ⁻¹' (KO k n : Set (GL n k))) := measurable_mul_const _ hK
  have key := lintegral_average μ (τ.prod ν) hK hL hj hδ hφ (c := ν N₀ * τ M₀) (fun y x => by
    let p : parab k e := ⟨y.2, unipRad_le_parab k e y.2.2⟩ * ⟨_, leviEmb_mem_parab k e y.1⟩
    have hp : leviProj k e p = y.1 := by
      rw [map_mul, (coe_mem_unipRad k _).1 y.2.2, leviProj_leviEmb, one_mul]
    have := hlaw p⁻¹ x
    rwa [map_inv, hp] at this) (fun x => by
      rw [← ha (x * g⁻¹)]
      refine lintegral_congr fun y => ?_
      exact indicator_congr_iff (by rw [Set.mem_preimage, mul_assoc]) rfl) hb
  rw [(ENNReal.mul_right_inj hc0 hc1).1 key, ← lintegral_indicator hK, ← lintegral_indicator hL,
    ← lintegral_mul_right_eq_self _ g⁻¹]
  refine lintegral_congr fun x => indicator_congr_iff Iff.rfl ?_
  rw [inv_mul_cancel_right]

end Local

theorem form_eq_of_diag {V : Type} [AddCommGroup V] [Module ℂ V] (B C : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ)
    (h : ∀ v, B v v = C v v) (v w : V) : B v w = C v w := by
  have h1 := h (v + w)
  have h2 := h (v + Complex.I • w)
  simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, LinearMap.map_smulₛₗ, h v, h w,
    Complex.conj_I, smul_eq_mul, RingHom.id_apply] at h1 h2
  linear_combination (1 / 2 : ℂ) * h1 + (Complex.I / 2) * h2 +
    ((1 / 2 : ℂ) * (B v w - C v w - B w v + C w v)) * Complex.I_mul_I

section Induction

open GlobalTheory.SplitFlip

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n]
  {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem isLocallyConstant_indSp {e : (Σ a, m a) ≃ n} {ρ : Representation ℂ (Levi k m) W} (f : IndSp e ρ) :
    IsLocallyConstant f.1.1 :=
  isLocallyConstant_of_open f.2 (by simp) fun x _ hu => congrFun (congrArg Subtype.val hu) x

theorem isUnitarisable_parInd (e : (Σ a, m a) ≃ n) {ρ : Representation ℂ (Levi k m) W} (h : IsUnitarisable ρ) :
    IsUnitarisable (parInd e ρ) := by
  obtain ⟨B, hs, hp, hi⟩ := h
  borelize k
  let μ : Measure (GL n k) := (Measure.haar : Measure (GL n k)).restrict (KO k n)
  have hK : MeasurableSet (KO k n : Set (GL n k)) := isOpen_KO.measurableSet
  have hc : ∀ f f' : IndSp e ρ, Continuous fun x => B (f.1.1 x) (f'.1.1 x) := fun f f' =>
    ((isLocallyConstant_indSp f).comp₂ (isLocallyConstant_indSp f') fun v w => B v w).continuous
  have hI : ∀ f f' : IndSp e ρ, Integrable (fun x => B (f.1.1 x) (f'.1.1 x)) μ := fun f f' =>
    (hc f f').continuousOn.integrableOn_compact isCompact_KO
  let C : IndSp e ρ →ₗ[ℂ] IndSp e ρ →ₗ⋆[ℂ] ℂ := LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ)
    (fun f f' => ∫ x, B (f.1.1 x) (f'.1.1 x) ∂μ)
    (fun f g f' => by rw [← integral_add (hI _ _) (hI _ _)]; simp)
    (fun c f f' => by rw [← integral_smul]; simp)
    (fun f g f' => by rw [← integral_add (hI _ _) (hI _ _)]; simp)
    (fun c f f' => by rw [← integral_smul]; simp)
  have hC : ∀ f f', C f f' = ∫ x, B (f.1.1 x) (f'.1.1 x) ∂μ := fun _ _ => rfl
  have hn : ∀ v, 0 ≤ (B v v).re := fun v => by
    by_cases h : v = 0
    · simp [h]
    · exact (hp v h).le
  have hre : ∀ v, B v v = ((B v v).re : ℂ) := fun v => (Complex.conj_eq_iff_re.1 (hs v v).symm).symm
  have hcr : ∀ f : IndSp e ρ, Continuous fun x => (B (f.1.1 x) (f.1.1 x)).re := fun f =>
    Complex.continuous_re.comp (hc f f)
  have hdiag : ∀ f, C f f = ((∫ x, (B (f.1.1 x) (f.1.1 x)).re ∂μ : ℝ) : ℂ) := fun f => by
    rw [hC, ← integral_complex_ofReal]
    exact integral_congr_ae (.of_forall fun x => hre _)
  refine ⟨C, fun f f' => ?_, fun f hf => ?_, fun g => ?_⟩
  · rw [hC, hC, ← integral_conj]
    exact integral_congr_ae (.of_forall fun x => hs _ _)
  · rw [hdiag, Complex.ofReal_re, integral_pos_iff_support_of_nonneg (fun x => hn _) (hI f f).re,
      Measure.restrict_apply' hK]
    refine ((hcr f).isOpen_support.inter isOpen_KO).measure_pos _ ?_
    obtain ⟨x, hx⟩ : ∃ x, f.1.1 x ≠ 0 := by
      by_contra! h0
      exact hf (Subtype.ext (Subtype.ext (funext h0)))
    obtain ⟨u, t, w, hw, rfl⟩ := exists_iwasawa e x
    refine ⟨w, (hp _ fun h0 => hx ?_).ne', hw⟩
    have := parInd_law e ρ f (⟨u, unipRad_le_parab k e u.2⟩ * ⟨_, leviEmb_mem_parab k e t⟩) w
    rw [h0, map_zero, smul_zero] at this
    exact this
  · refine form_eq_of_diag ((C.comp (parInd e ρ g)).compl₂ (parInd e ρ g)) C fun f => ?_
    rw [LinearMap.compl₂_apply, LinearMap.comp_apply, hdiag, hdiag,
      integral_eq_lintegral_of_nonneg_ae (.of_forall fun x => hn _) (hcr _).aestronglyMeasurable,
      integral_eq_lintegral_of_nonneg_ae (.of_forall fun x => hn _) (hcr _).aestronglyMeasurable]
    congr 2
    refine lintegral_KO_mul_right e Measure.haar (φ := fun x => ENNReal.ofReal (B (f.1.1 x) (f.1.1 x)).re)
      (hcr f).measurable.ennreal_ofReal (fun p x => ?_) g
    have h0 := (modulus_pos k (leviProj k e p)).le
    rw [← ENNReal.ofReal_mul h0, parInd_law, val_deltaHalf]
    simp only [map_smul, LinearMap.smul_apply, LinearMap.map_smulₛₗ, hi, Complex.conj_ofReal, smul_eq_mul,
      Complex.re_ofReal_mul, RingHom.id_apply]
    rw [← mul_assoc, Real.mul_self_sqrt h0]

theorem isUnitarisable_prod₂ {r t : ℕ} {π₁ : Representation ℂ (GL (Fin r) k) V}
    {π₂ : Representation ℂ (GL (Fin t) k) W} (h₁ : IsUnitarisable π₁) (h₂ : IsUnitarisable π₂) :
    IsUnitarisable (prod₂ π₁ π₂) :=
  isUnitarisable_parInd _ (isUnitarisable_comp (isUnitarisable_extTensor h₁ h₂) _)

theorem isUnitarisable_multiProd (e : (Σ a, m a) ≃ n) {X : α → Type} [∀ a, AddCommGroup (X a)]
    [∀ a, Module ℂ (X a)] {π : ∀ a, Representation ℂ (GL (m a) k) (X a)} (h : ∀ a, IsUnitarisable (π a)) :
    IsUnitarisable (multiProd e π) :=
  isUnitarisable_parInd _ (isUnitarisable_piTensor h)

end Induction

end GlobalTheory.SmGL.UnitInd
