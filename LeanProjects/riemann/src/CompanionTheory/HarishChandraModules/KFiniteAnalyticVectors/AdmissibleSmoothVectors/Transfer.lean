import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.MapStdPoly

open MeasureTheory Matrix
open scoped Kronecker Pointwise

noncomputable section

namespace CompanionTheory.D.gk.admitted

namespace PrismTransfer

section Closure

variable {G : Type} [Group G] {ι ι' : Type} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']

def sumRep (ρ : G →* Matrix ι ι ℂ) (ρ' : G →* Matrix ι' ι' ℂ) : G →* Matrix (ι ⊕ ι') (ι ⊕ ι') ℂ where
  toFun x := fromBlocks (ρ x) 0 0 (ρ' x)
  map_one' := by simp
  map_mul' x y := by simp [fromBlocks_multiply]

def tensRep (ρ : G →* Matrix ι ι ℂ) (ρ' : G →* Matrix ι' ι' ℂ) : G →* Matrix (ι × ι') (ι × ι') ℂ where
  toFun x := ρ x ⊗ₖ ρ' x
  map_one' := by simp
  map_mul' x y := by simp [mul_kronecker_mul]

def conjRep (ρ : G →* Matrix ι ι ℂ) : G →* Matrix ι ι ℂ where
  toFun x := (ρ x).map (starRingEnd ℂ)
  map_one' := by simp
  map_mul' x y := by simp [Matrix.map_mul]

variable [TopologicalSpace G] {st : G → G} {S : Set G} {ρ : G →* Matrix ι ι ℂ} {ρ' : G →* Matrix ι' ι' ℂ}

theorem isGood_sum (h : IsGood st S ρ) (h' : IsGood st S ρ') : IsGood st S (sumRep ρ ρ') where
  cont := Continuous.matrix_fromBlocks h.cont continuous_const continuous_const h'.cont
  adj g := by
    change fromBlocks (ρ (st g)) 0 0 (ρ' (st g)) = (fromBlocks (ρ g) 0 0 (ρ' g))ᴴ
    simp [fromBlocks_conjTranspose, h.adj, h'.adj]
  tri := by
    obtain ⟨a, ha, ha'⟩ := h.tri
    obtain ⟨b, hb, hb'⟩ := h'.tri
    refine ⟨Sum.elim (fun i => 2 * a i) (fun j => 2 * b j + 1), ?_, ?_⟩
    · rintro (i | i) (j | j) hij <;> simp only [Sum.elim_inl, Sum.elim_inr] at hij
      · rw [ha (show a i = a j by omega)]
      · omega
      · omega
      · rw [hb (show b i = b j by omega)]
    · intro s hs
      change (fromBlocks (ρ s) 0 0 (ρ' s)).BlockTriangular _
      rintro (i | i) (j | j) hij <;> simp only [Sum.elim_inl, Sum.elim_inr] at hij
      · exact ha' s hs (show a j < a i by omega)
      · rfl
      · rfl
      · exact hb' s hs (show b j < b i by omega)

theorem pair_mono {a b c d : ℕ} (h : a ≤ c) (h' : b ≤ d) : Nat.pair a b ≤ Nat.pair c d := by
  have h1 : Nat.pair a b ≤ Nat.pair c b := by
    rcases h.eq_or_lt with rfl | h
    · exact le_rfl
    · exact (Nat.pair_lt_pair_left b h).le
  have h2 : Nat.pair c b ≤ Nat.pair c d := by
    rcases h'.eq_or_lt with rfl | h'
    · exact le_rfl
    · exact (Nat.pair_lt_pair_right c h').le
  exact h1.trans h2

theorem isGood_tens (h : IsGood st S ρ) (h' : IsGood st S ρ') : IsGood st S (tensRep ρ ρ') where
  cont := by
    refine continuous_matrix fun i j => ?_
    exact (h.cont.matrix_elem i.1 j.1).mul (h'.cont.matrix_elem i.2 j.2)
  adj g := by
    change ρ (st g) ⊗ₖ ρ' (st g) = (ρ g ⊗ₖ ρ' g)ᴴ
    rw [conjTranspose_kronecker, h.adj, h'.adj]
  tri := by
    obtain ⟨a, ha, ha'⟩ := h.tri
    obtain ⟨b, hb, hb'⟩ := h'.tri
    refine ⟨fun p => Nat.pair (a p.1) (b p.2), ?_, ?_⟩
    · intro p q hpq
      obtain ⟨h1, h2⟩ := Nat.pair_eq_pair.1 hpq
      exact Prod.ext (ha h1) (hb h2)
    · intro s hs p q hpq
      change ρ s p.1 q.1 * ρ' s p.2 q.2 = 0
      by_cases h1 : a q.1 < a p.1
      · rw [ha' s hs h1, zero_mul]
      by_cases h2 : b q.2 < b p.2
      · rw [hb' s hs h2, mul_zero]
      exact absurd (pair_mono (not_lt.1 h1) (not_lt.1 h2)) (not_le.2 hpq)

theorem isGood_conj (h : IsGood st S ρ) : IsGood st S (conjRep ρ) where
  cont := by
    refine continuous_matrix fun i j => ?_
    exact Complex.continuous_conj.comp (h.cont.matrix_elem i j)
  adj g := by
    change (ρ (st g)).map (starRingEnd ℂ) = ((ρ g).map (starRingEnd ℂ))ᴴ
    rw [h.adj]
    ext i j
    simp
  tri := by
    obtain ⟨a, ha, ha'⟩ := h.tri
    refine ⟨a, ha, fun s hs i j hij => ?_⟩
    change starRingEnd ℂ (ρ s i j) = 0
    rw [ha' s hs hij, map_zero]

theorem isGood_one : IsGood st S (1 : G →* Matrix Unit Unit ℂ) where
  cont := continuous_const
  adj g := by simp
  tri := ⟨fun _ => 0, fun _ _ _ => rfl, fun _ _ _ _ h => absurd h (lt_irrefl _)⟩

omit [DecidableEq ι] [DecidableEq ι'] in
theorem coef_kronecker (A : Matrix ι ι ℂ) (B : Matrix ι' ι' ℂ) (a b : ι → ℂ) (a' b' : ι' → ℂ) :
    (fun p : ι × ι' => a p.1 * a' p.2) ⬝ᵥ ((A ⊗ₖ B) *ᵥ fun p : ι × ι' => b p.1 * b' p.2) =
      (a ⬝ᵥ (A *ᵥ b)) * (a' ⬝ᵥ (B *ᵥ b')) := by
  have : ((A ⊗ₖ B) *ᵥ fun p : ι × ι' => b p.1 * b' p.2) = fun p => (A *ᵥ b) p.1 * (B *ᵥ b') p.2 := by
    funext p
    simp only [mulVec, dotProduct, Fintype.sum_prod_type, Finset.sum_mul_sum, kroneckerMap_apply]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  rw [this]
  simp only [dotProduct, Fintype.sum_prod_type, Finset.sum_mul_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

def coefAlg (st : G → G) (S : Set G) (C : Set G) : StarSubalgebra ℂ C(C, ℂ) where
  carrier := {f | ∃ (κ : Type) (_ : Fintype κ) (_ : DecidableEq κ) (τ : G →* Matrix κ κ ℂ) (a b : κ → ℂ),
    IsGood st S τ ∧ ∀ x : C, f x = a ⬝ᵥ (τ x *ᵥ b)}
  mul_mem' := by
    rintro f g ⟨κ, _, _, τ, a, b, h, hf⟩ ⟨κ', _, _, τ', a', b', h', hg⟩
    refine ⟨κ × κ', inferInstance, inferInstance, tensRep τ τ', fun p => a p.1 * a' p.2,
      fun p => b p.1 * b' p.2, isGood_tens h h', fun x => ?_⟩
    rw [ContinuousMap.mul_apply, hf, hg]
    exact (coef_kronecker _ _ _ _ _ _).symm
  add_mem' := by
    rintro f g ⟨κ, _, _, τ, a, b, h, hf⟩ ⟨κ', _, _, τ', a', b', h', hg⟩
    refine ⟨κ ⊕ κ', inferInstance, inferInstance, sumRep τ τ', Sum.elim a a', Sum.elim b b',
      isGood_sum h h', fun x => ?_⟩
    rw [ContinuousMap.add_apply, hf, hg]
    change _ = Sum.elim a a' ⬝ᵥ (fromBlocks (τ x) 0 0 (τ' x) *ᵥ Sum.elim b b')
    simp [fromBlocks_mulVec, sumElim_dotProduct_sumElim]
  algebraMap_mem' c := by
    refine ⟨Unit, inferInstance, inferInstance, 1, fun _ => c, fun _ => 1, isGood_one, fun x => ?_⟩
    simp [dotProduct]
  star_mem' := by
    rintro f ⟨κ, _, _, τ, a, b, h, hf⟩
    refine ⟨κ, inferInstance, inferInstance, conjRep τ, star a, star b, isGood_conj h, fun x => ?_⟩
    rw [ContinuousMap.star_apply, hf]
    change _ = star a ⬝ᵥ ((τ x).map (starRingEnd ℂ) *ᵥ star b)
    simp [dotProduct, mulVec, mul_comm]

theorem coefAlg_separates (h : IsGood st S ρ) (hi : Function.Injective ρ) (C : Set G) :
    (coefAlg st S C).SeparatesPoints := by
  intro x y hxy
  have : ρ x ≠ ρ y := fun e => hxy (Subtype.ext (hi e))
  obtain ⟨i, j, hij⟩ : ∃ i j, ρ x i j ≠ ρ y i j := by
    by_contra hc
    push Not at hc
    exact this (Matrix.ext hc)
  refine ⟨fun z : C => ρ z i j, ⟨⟨fun z : C => ρ z i j,
    (h.cont.matrix_elem i j).comp continuous_subtype_val⟩, ?_, rfl⟩, hij⟩
  refine ⟨ι, inferInstance, inferInstance, ρ, Pi.single i 1, Pi.single j 1, h, fun z => ?_⟩
  simp

theorem exists_approx (h : IsGood st S ρ) (hi : Function.Injective ρ) {C : Set G} (hC : IsCompact C)
    {Φ : G → ℂ} (hΦ : Continuous Φ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ (κ : Type) (_ : Fintype κ) (_ : DecidableEq κ) (τ : G →* Matrix κ κ ℂ) (a b : κ → ℂ),
      IsGood st S τ ∧ ∀ x ∈ C, ‖Φ x - a ⬝ᵥ (τ x *ᵥ b)‖ ≤ δ := by
  have : CompactSpace C := isCompact_iff_compactSpace.1 hC
  have htop := ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints _
    (coefAlg_separates h hi C)
  let F : C(C, ℂ) := ⟨fun x => Φ x, hΦ.comp continuous_subtype_val⟩
  have hF : F ∈ closure (coefAlg st S C : Set C(C, ℂ)) := by
    have : F ∈ (coefAlg st S C).topologicalClosure := by rw [htop]; trivial
    exact this
  obtain ⟨f, ⟨κ, _, _, τ, a, b, hτ, hf⟩, hd⟩ := Metric.mem_closure_iff.1 hF δ hδ
  refine ⟨κ, inferInstance, inferInstance, τ, a, b, hτ, fun x hx => ?_⟩
  have := (ContinuousMap.dist_apply_le_dist (f := F) (g := f) ⟨x, hx⟩).trans hd.le
  rw [dist_eq_norm, hf] at this
  exact this

end Closure

section Bound

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {K : Subgroup G} [CompactSpace K] [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [IsFiniteMeasure μ]
  (e : K → ℂ)

structure IsFam (Φ : G → ℂ) (F : List G → G → ℂ) : Prop where
  cont₀ : Continuous Φ
  cont : ∀ l, Continuous (F l)
  nil : ∀ x, F [] x = ∫ k : K, e k * Φ (x * k) ∂μ
  cons : ∀ a l x, F (a :: l) x = ∫ k : K, e k * F l (x * k * a) ∂μ

variable {μ e}

omit [IsTopologicalGroup G] in
theorem integrable_of_cont {V : Type} [NormedAddCommGroup V] [SecondCountableTopology K] {f : K → V}
    (hf : Continuous f) : Integrable f μ :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

theorem IsFam.sub [SecondCountableTopology K] (he : Continuous e) {Φ Φ' : G → ℂ} {F F' : List G → G → ℂ}
    (h : IsFam μ e Φ F) (h' : IsFam μ e Φ' F') :
    IsFam μ e (fun x => Φ x - Φ' x) (fun l x => F l x - F' l x) where
  cont₀ := h.cont₀.sub h'.cont₀
  cont l := (h.cont l).sub (h'.cont l)
  nil x := by
    have h1 := h.cont₀
    have h2 := h'.cont₀
    rw [h.nil, h'.nil, ← integral_sub (integrable_of_cont (by fun_prop)) (integrable_of_cont (by fun_prop))]
    simp only [mul_sub]
  cons a l x := by
    have h1 := h.cont l
    have h2 := h'.cont l
    rw [h.cons, h'.cons, ← integral_sub (integrable_of_cont (by fun_prop)) (integrable_of_cont (by fun_prop))]
    simp only [mul_sub]

omit [IsTopologicalGroup G] in
theorem norm_avg_le [SecondCountableTopology K] (he : Continuous e) {f : K → ℂ} {δ : ℝ} (hf : ∀ k, ‖f k‖ ≤ δ) :
    ‖∫ k, e k * f k ∂μ‖ ≤ (∫ k, ‖e k‖ ∂μ) * δ := by
  rw [← integral_mul_const]
  refine norm_integral_le_of_norm_le (integrable_of_cont (by fun_prop)) (ae_of_all _ fun k => ?_)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (hf k) (norm_nonneg _)

theorem exists_bound [SecondCountableTopology K] (he : Continuous e) (l : List G) :
    ∀ C : Set G, IsCompact C → ∃ C' : Set G, IsCompact C' ∧ ∀ Φ F, IsFam μ e Φ F → ∀ δ : ℝ,
      (∀ y ∈ C', ‖Φ y‖ ≤ δ) → ∀ x ∈ C, ‖F l x‖ ≤ (∫ k, ‖e k‖ ∂μ) ^ (l.length + 1) * δ := by
  have hK : IsCompact (K : Set G) := isCompact_iff_compactSpace.2 ‹_›
  induction l with
  | nil =>
    intro C hC
    refine ⟨C * (K : Set G), hC.mul hK, fun Φ F h δ hδ x hx => ?_⟩
    rw [h.nil]
    simpa using norm_avg_le (μ := μ) he fun k => hδ _ (Set.mul_mem_mul hx k.2)
  | cons a l ih =>
    intro C hC
    obtain ⟨C', hC', H⟩ := ih (C * (K : Set G) * {a}) ((hC.mul hK).mul isCompact_singleton)
    refine ⟨C', hC', fun Φ F h δ hδ x hx => ?_⟩
    rw [h.cons, List.length_cons, pow_succ', mul_assoc]
    exact norm_avg_le he fun k => H Φ F h δ hδ _ (Set.mul_mem_mul (Set.mul_mem_mul hx k.2) rfl)

omit [IsTopologicalGroup G] in
theorem isFam_rep [SecondCountableTopology K] (he : Continuous e) {V : Type} [NormedAddCommGroup V]
    [NormedSpace ℂ V] [CompleteSpace V] (τ : G →* Module.End ℂ V) (h1 : ∀ x, Continuous (τ x))
    (h2 : ∀ v, Continuous fun x => τ x v) (E : Module.End ℂ V) (hE : ∀ u, E u = ∫ k : K, e k • τ k u ∂μ)
    (ℓ : V →L[ℂ] ℂ) (u : V) :
    IsFam μ e (fun x => ℓ (τ x u)) (fun l x => ℓ (τ x (word E (l.map τ) u))) := by
  have key : ∀ x w, ℓ (τ x (E w)) = ∫ k : K, e k * ℓ (τ (x * k) w) ∂μ := by
    intro x w
    have hw := h2 w
    have := (ℓ.comp ⟨τ x, h1 x⟩).integral_comp_comm (μ := μ) (φ := fun k : K => e k • τ k w)
      (integrable_of_cont (he.smul (hw.comp continuous_subtype_val)))
    rw [hE]
    refine Eq.trans this.symm ?_
    simp
  refine ⟨ℓ.continuous.comp (h2 u), fun l => ℓ.continuous.comp (h2 _), fun x => key x u, fun a l x => ?_⟩
  simp only [List.map_cons, word_cons, Module.End.mul_apply]
  rw [key]
  simp

end Bound

theorem apply_stdPoly {G V : Type} [AddCommGroup V] [Module ℂ V] (τ : G → Module.End ℂ V) (E : Module.End ℂ V)
    {M : ℕ} (g : Fin M → G) (ℓ : V →ₗ[ℂ] ℂ) (u : V) :
    ℓ (stdPoly E (fun i => τ (g i)) u) = ∑ π : Equiv.Perm (Fin M),
      ((Equiv.Perm.sign π : ℤ) : ℂ) * ℓ (word E ((List.ofFn fun i => g (π i)).map τ) u) := by
  simp only [stdPoly, LinearMap.sum_apply, map_sum, List.map_ofFn, Function.comp_def, Module.End.mul_apply,
    Module.End.intCast_apply, map_zsmul, zsmul_eq_mul]

end PrismTransfer

open PrismTransfer

theorem transfer_holds : Transfer := by
  intro G _ _ _ _ _ K _ _ _ μ _ st S ι₀ _ _ ρ₀ hρ₀ hi e he M g hgood H _ _ _ σ hσ E hE
  have : SecondCountableTopology K := TopologicalSpace.Subtype.secondCountableTopology (K : Set G)
  set B : ℝ := ∫ k, ‖e k‖ ∂μ with hB
  choose C hC hbd using fun π : Equiv.Perm (Fin M) =>
    exists_bound (μ := μ) he (List.ofFn fun i => g (π i)) {1} isCompact_singleton
  have hCU : IsCompact (⋃ π, C π) := isCompact_iUnion hC
  let φ : (H →L[ℂ] H) →+* Module.End ℂ H := ContinuousLinearMap.toLinearMapRingHom
  let σ' : G →* Module.End ℂ H := φ.toMonoidHom.comp σ
  ext v
  refine SeparatingDual.eq_zero_of_forall_dual_eq_zero (R := ℂ) fun ℓ => ?_
  have hF := isFam_rep (μ := μ) he σ' (fun x => (σ x).continuous) hσ (φ E) hE ℓ v
  have hmap : stdPoly E (fun i => σ (g i)) v = stdPoly (φ E) (fun i => σ' (g i)) v := by
    change φ (stdPoly E fun i => σ (g i)) v = _
    rw [map_stdPoly]
    rfl
  rw [hmap]
  have main : ∀ δ : ℝ, 0 < δ → ‖ℓ (stdPoly (φ E) (fun i => σ' (g i)) v)‖ ≤
      (Fintype.card (Equiv.Perm (Fin M)) * B ^ (M + 1)) * δ := by
    intro δ hδ
    obtain ⟨κ, _, _, τ, a, b, hτ, hap⟩ := exists_approx hρ₀ hi hCU hF.cont₀ hδ
    let τ' : G →* Module.End ℂ (κ → ℂ) := (Matrix.toLinAlgEquiv' : Matrix κ κ ℂ ≃ₐ[ℂ] _).toMonoidHom.comp τ
    have hc : ∀ u : κ → ℂ, Continuous fun x => τ x *ᵥ u := fun u => hτ.cont.matrix_mulVec continuous_const
    have hint : ∀ u : κ → ℂ, Integrable (fun k : K => e k • (τ k *ᵥ u)) μ := fun u =>
      integrable_of_cont (he.smul ((hc u).comp continuous_subtype_val))
    let E' : Module.End ℂ (κ → ℂ) :=
      { toFun := fun u => ∫ k : K, e k • (τ k *ᵥ u) ∂μ
        map_add' := fun u w => by
          rw [← integral_add (hint u) (hint w)]
          simp only [mulVec_add, smul_add]
        map_smul' := fun c u => by
          rw [RingHom.id_apply, ← integral_smul]
          simp only [mulVec_smul, smul_comm c] }
    let ℓ' : (κ → ℂ) →L[ℂ] ℂ := LinearMap.toContinuousLinearMap (dotProductBilin ℂ ℂ a)
    have hF' := isFam_rep (μ := μ) he τ' (fun x => (τ' x).continuous_of_finiteDimensional) hc E'
      (fun _ => rfl) ℓ' b
    have hz : stdPoly E' (fun i => τ' (g i)) = 0 := hgood κ τ hτ E' fun _ => rfl
    have e1 := apply_stdPoly σ' (φ E) g (ℓ : H →ₗ[ℂ] ℂ) v
    have e2 := apply_stdPoly τ' E' g (ℓ' : (κ → ℂ) →ₗ[ℂ] ℂ) b
    rw [hz, LinearMap.zero_apply, map_zero] at e2
    have e3 : ℓ (stdPoly (φ E) (fun i => σ' (g i)) v) = ∑ π : Equiv.Perm (Fin M),
        ((Equiv.Perm.sign π : ℤ) : ℂ) * (ℓ (word (φ E) ((List.ofFn fun i => g (π i)).map σ') v) -
          ℓ' (word E' ((List.ofFn fun i => g (π i)).map τ') b)) := by
      simp only [mul_sub, Finset.sum_sub_distrib]
      exact e1.trans (by rw [← sub_zero (Finset.sum _ _), e2]; rfl)
    rw [e3]
    refine (norm_sum_le _ _).trans ?_
    rw [mul_assoc, ← nsmul_eq_mul, ← Finset.card_univ]
    refine Finset.sum_le_card_nsmul _ _ _ fun π _ => ?_
    have hs : ‖((Equiv.Perm.sign π : ℤ) : ℂ)‖ = 1 := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign π) with h | h <;> simp [h]
    rw [norm_mul, hs, one_mul]
    have := hbd π _ _ (hF.sub he hF') δ
      (fun y hy => hap y (Set.mem_iUnion.2 ⟨π, hy⟩)) 1 rfl
    simpa only [map_one, Module.End.one_apply, List.length_ofFn] using this
  rw [← norm_le_zero_iff]
  refine le_of_forall_pos_le_add fun ε hε => ?_
  set D : ℝ := Fintype.card (Equiv.Perm (Fin M)) * B ^ (M + 1)
  have hD : 0 ≤ D := mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (integral_nonneg fun _ => norm_nonneg _) _)
  refine (main (ε / (D + 1)) (by positivity)).trans ?_
  rw [zero_add, mul_div_assoc', div_le_iff₀ (by positivity)]
  nlinarith

end CompanionTheory.D.gk.admitted
