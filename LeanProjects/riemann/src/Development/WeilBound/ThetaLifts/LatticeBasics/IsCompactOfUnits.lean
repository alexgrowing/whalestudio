import Development.WeilBound.ThetaLifts.TowerModels.LeviAd

noncomputable section

namespace GlobalTheory.ThK.Dbl.St

open PositivityTheory.ThKG.Tow

open scoped TensorProduct Matrix Pointwise RestrictedProduct
open NumberField IsDedekindDomain Topology Filter GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

theorem isCompact_of_units {A : Type} [Monoid A] [TopologicalSpace A] [ContinuousMul A] [T2Space A]
    (H : Subgroup Aˣ) (hH : IsClosed (H : Set Aˣ)) (K : Set H) (hK : IsClosed K) (S : Set A) (hS : IsCompact S)
    (h : ∀ k ∈ K, (k.1 : A) ∈ S ∧ ((k⁻¹).1 : A) ∈ S) : IsCompact K := by
  have e : IsClosedEmbedding (fun k : H => Units.embedProduct A k.1) :=
    Units.isClosedEmbedding_embedProduct.comp hH.isClosedEmbedding_subtypeVal
  have hc : IsCompact (S ×ˢ (MulOpposite.op '' S)) := hS.prod (hS.image MulOpposite.continuous_op)
  exact (e.isCompact_preimage hc).of_isClosed_subset hK fun k hk => ⟨(h k hk).1, _, (h k hk).2, rfl⟩

theorem cartan_bound {n : ℕ} {M θ : Matrix (Fin n) (Fin n) ℂ} (h : IsCartan M θ) :
    ∃ R : ℝ, ∀ A : Matrix (Fin n) (Fin n) ℂ, Aᵀ * M * A.map star = M → Commute A θ → ∀ i j, ‖A i j‖ ≤ R := by
  let Q : (Fin n → ℂ) → ℝ := fun x => ((θ *ᵥ x) ⬝ᵥ M *ᵥ star x).re
  have hQ : Continuous Q := Complex.continuous_re.comp
    ((continuous_const.matrix_mulVec continuous_id).dotProduct (continuous_const.matrix_mulVec continuous_star))
  have hom : ∀ (t : ℝ) x, Q (t • x) = t ^ 2 * Q x := fun t x => by
    simp only [Q, star_smul, star_trivial, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, Complex.smul_re,
      smul_eq_mul]
    ring
  obtain ⟨c, hc, hle⟩ := (isCompact_sphere (0 : Fin n → ℂ) 1).exists_forall_le' hQ.continuousOn (a := 0)
    fun x hx => h.2.2 x (by rintro rfl; simp at hx)
  have low : ∀ x, c * ‖x‖ ^ 2 ≤ Q x := fun x => by
    by_cases hx : x = 0
    · subst hx; simp [Q]
    · have hn : 0 < ‖x‖ := norm_pos_iff.2 hx
      have h1 := hle (‖x‖⁻¹ • x) (by simp [norm_smul, hn.ne'])
      have h2 : Q x = ‖x‖ ^ 2 * Q (‖x‖⁻¹ • x) := by rw [← hom, smul_smul, mul_inv_cancel₀ hn.ne', one_smul]
      rw [h2, mul_comm]
      exact mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
  refine ⟨∑ j, √(Q (Pi.single j 1) / c), fun A hA hc' i j => ?_⟩
  have inv : ∀ x, Q (A *ᵥ x) = Q x := fun x => by
    have e1 : star (A *ᵥ x) = A.map star *ᵥ star x := by
      ext k; simp [Matrix.mulVec, dotProduct]
    have e2 : θ *ᵥ A *ᵥ x = A *ᵥ θ *ᵥ x := by rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hc'.eq]
    have e3 : (A *ᵥ θ *ᵥ x) ⬝ᵥ M *ᵥ A.map star *ᵥ star x = (θ *ᵥ x) ⬝ᵥ (Aᵀ * M * A.map star) *ᵥ star x := by
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec (θ *ᵥ x) Aᵀ,
        Matrix.vecMul_transpose]
    simp only [Q]
    rw [e1, e2, e3, hA]
  have h1 : ‖A i j‖ ≤ ‖A *ᵥ Pi.single j 1‖ := by
    have := norm_le_pi_norm (A *ᵥ Pi.single j 1) i
    rwa [Matrix.mulVec_single_one] at this ⊢
  have h2 : ‖A *ᵥ Pi.single j 1‖ ≤ √(Q (Pi.single j 1) / c) := by
    refine Real.le_sqrt_of_sq_le ?_
    rw [le_div_iff₀ hc, mul_comm, ← inv]
    exact low _
  exact h1.trans (h2.trans (Finset.single_le_sum (f := fun j => √(Q (Pi.single j 1) / c))
    (fun _ _ => Real.sqrt_nonneg _) (Finset.mem_univ j)))

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}

theorem ae_ring : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _

theorem ae_t2 : T2Space (AE F E) := by
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)
  exact e.isEmbedding.t2Space

theorem ae_smul : ContinuousSMul (AF F) (AE F E) := IsModuleTopology.toContinuousSMul (AF F) _

attribute [local instance] ae_ring ae_t2 ae_smul

theorem evI_eq_zero {a : AF F} : evI F a = 0 ↔ a.1 = 0 := map_eq_zero_iff _ (RingEquiv.injective _)

variable (F) in

def intF : AddSubgroup (AF F) where
  carrier := {a | evI F a = 0 ∧ ∀ v, evFin F v a ∈ v.adicCompletionIntegers F}
  zero_mem' := ⟨evI_eq_zero.2 rfl, fun v => by rw [map_zero]; exact zero_mem _⟩
  add_mem' := fun {a b} ha hb => ⟨evI_eq_zero.2 (by
      change a.1 + b.1 = 0
      rw [evI_eq_zero.1 ha.1, evI_eq_zero.1 hb.1, add_zero]),
    fun v => by rw [map_add]; exact add_mem (ha.2 v) (hb.2 v)⟩
  neg_mem' := fun {a} ha => ⟨evI_eq_zero.2 (by
      change -a.1 = 0
      rw [evI_eq_zero.1 ha.1, neg_zero]),
    fun v => by rw [map_neg]; exact neg_mem (ha.2 v)⟩

theorem isCompact_intF : IsCompact (intF F : Set (AF F)) := by
  haveI := GlobalTheory.AdelicUnitaryTop.compactSpace_adicCompletionIntegers F
  let s : (∀ v : Pl F, (v.adicCompletionIntegers F : Set (v.adicCompletion F))) → Af F :=
    RestrictedProduct.structureMap (fun v : Pl F => v.adicCompletion F)
      (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) cofinite
  haveI : ∀ v : Pl F, CompactSpace (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := this
  have hs : Continuous s := RestrictedProduct.isEmbedding_structureMap.continuous
  have hc : Continuous fun x => pairA F 0 (s x) := continuous_const.prodMk hs
  convert isCompact_range hc using 1
  ext a
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun v => ⟨_, h2 v⟩, Prod.ext (evI_eq_zero.1 h1).symm ?_⟩
    exact RestrictedProduct.ext _ _ fun v => rfl
  · rintro ⟨x, rfl⟩
    exact ⟨evI_eq_zero.2 rfl, fun v => (x v).2⟩

theorem mem_latHat (X : Spc F E n) {a : AF F} (ha : a ∈ intF F) {y : Fin n → E} (hy : y ∈ X.L) :
    a • incV F y ∈ latHat X :=
  AddSubgroup.subset_closure ⟨a, ha.1, ha.2, y, hy, rfl⟩

theorem isCompact_latHat (X : Spc F E n) (hX : X.L.FG) : IsCompact (latHat X : Set (Fin n → AE F E)) := by
  have hZ : (X.L.restrictScalars ℤ).FG := hX.restrictScalars
  obtain ⟨m, s, hs⟩ := Submodule.fg_iff_exists_fin_generating_family.1 hZ
  have hsL : ∀ j, s j ∈ X.L := fun j => by
    have : s j ∈ X.L.restrictScalars ℤ := hs ▸ Submodule.subset_span ⟨j, rfl⟩
    exact this
  haveI : CompactSpace (intF F) := isCompact_iff_compactSpace.1 isCompact_intF
  let f : (Fin m → intF F) →+ (Fin n → AE F E) :=
    AddMonoidHom.mk' (fun a => ∑ j, (a j : AF F) • incV F (s j)) fun a b => by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      have : ((a + b) j : AF F) = a j + b j := rfl
      rw [this, add_smul]
  have hf : Continuous f := by
    change Continuous fun a : Fin m → intF F => ∑ j, (a j : AF F) • incV F (s j)
    refine continuous_finsetSum _ fun j _ => ?_
    have h1 : Continuous fun a : Fin m → intF F => (a j : AF F) := Continuous.subtype_val (continuous_apply j)
    exact h1.fun_smul continuous_const
  have e : latHat X = f.range := by
    refine le_antisymm ((AddSubgroup.closure_le _).2 ?_) ?_
    · rintro _ ⟨a, ha, ha', y, hy, rfl⟩
      have hy' : y ∈ Submodule.span ℤ (Set.range s) := by rw [hs]; exact hy
      obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 hy'
      refine ⟨fun j => c j • ⟨a, ha, ha'⟩, funext fun i => ?_⟩
      change (∑ j, (c j • a) • incV F (s j)) i = a • inclR (F := F) (AF F) ((∑ j, c j • s j) i)
      rw [Finset.sum_apply, Finset.sum_apply, map_sum, Finset.smul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      change (c j • a) • inclR (F := F) (AF F) (s j i) = _
      rw [Pi.smul_apply, map_zsmul, smul_assoc, smul_comm]
    · rintro _ ⟨a, rfl⟩
      change (∑ j, (a j : AF F) • incV F (s j)) ∈ latHat X
      exact sum_mem fun j _ => mem_latHat X (a j).2 (hsL j)
  rw [e, AddMonoidHom.coe_range]
  exact isCompact_range hf

variable (F) in

def eF : AF F := pairA F 0 1

theorem eF_mem : eF F ∈ intF F := ⟨evI_eq_zero.2 rfl, fun v => by
  have : evFin F v (eF F) = 1 := map_one (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v)
  rw [this]; exact one_mem _⟩

theorem vec_bound (X : Spc F E n) (hX : X.L.IsLattice E) (x : Fin n → E) :
    ∃ C : Set (Fin n → AE F E), IsCompact C ∧ ∀ M : Matrix (Fin n) (Fin n) (AE F E),
      (∀ y ∈ latHat X, M *ᵥ y ∈ latHat X) → M *ᵥ (eF F • incV F x) ∈ C := by
  have hx : x ∈ Submodule.span E (X.L : Set (Fin n → E)) := by
    rw [Submodule.IsLattice.span_eq_top (A := E)]; trivial
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨_, isCompact_latHat X hX.fg, fun M hM => hM _ (mem_latHat X eF_mem hy)⟩
  | zero =>
    refine ⟨{0}, isCompact_singleton, fun M _ => ?_⟩
    have : incV F (0 : Fin n → E) = 0 := funext fun i => map_zero (inclR (F := F) (AF F))
    rw [this, smul_zero, Matrix.mulVec_zero]; rfl
  | add y z _ _ hy hz =>
    obtain ⟨C, hC, h⟩ := hy
    obtain ⟨C', hC', h'⟩ := hz
    refine ⟨C + C', hC.add hC', fun M hM => ?_⟩
    have : incV F (y + z) = incV F y + incV F z := funext fun i => map_add (inclR (F := F) (AF F)) _ _
    rw [this, smul_add, Matrix.mulVec_add]
    exact Set.add_mem_add (h M hM) (h' M hM)
  | smul c y _ hy =>
    obtain ⟨C, hC, h⟩ := hy
    refine ⟨(fun z => inclR (F := F) (AF F) c • z) '' C, hC.image (continuous_const_smul _), fun M hM => ⟨_, h M hM, ?_⟩⟩
    have : eF F • incV F (c • y) = inclR (F := F) (AF F) c • eF F • incV F y :=
      funext fun i => by
        change eF F • inclR (F := F) (AF F) (c * y i) = inclR (F := F) (AF F) c * (eF F • inclR (F := F) (AF F) (y i))
        rw [map_mul, mul_smul_comm]
    rw [this]
    exact (Matrix.mulVec_smul _ _ _).symm

theorem fin_bound (X : Spc F E n) (hX : X.L.IsLattice E) (i j : Fin n) :
    ∃ C : Set (AE F E), IsCompact C ∧ ∀ M : Matrix (Fin n) (Fin n) (AE F E),
      (∀ y ∈ latHat X, M *ᵥ y ∈ latHat X) → eF F • M i j ∈ C := by
  obtain ⟨C, hC, h⟩ := vec_bound X hX (Pi.single j 1)
  refine ⟨(fun z => z i) '' C, hC.image (continuous_apply i), fun M hM => ⟨_, h M hM, ?_⟩⟩
  have : incV F (Pi.single j 1 : Fin n → E) = Pi.single j 1 := funext fun k => by
    by_cases hk : k = j
    · subst hk; simp [incV]
    · simp [incV, hk]
  rw [this, Matrix.mulVec_smul, Matrix.mulVec_single_one]
  rfl

omit [NumberField E] in
theorem piInf_smul {w : InfinitePlace F} (τ : EmbOver E w) (a : AF F) (z : AE F E) :
    piInf τ (a • z) = InfinitePlace.Completion.extensionEmbedding w (a.1 w) * piInf τ z := by
  have : piInf τ (algebraMap (AF F) (AE F E) a) = InfinitePlace.Completion.extensionEmbedding w (a.1 w) := by
    change InfinitePlace.Completion.extensionEmbedding w (a.1 w) * τ.1 1 = _
    rw [map_one, mul_one]
  rw [Algebra.smul_def, map_mul, this]

omit [NumberField E] in
theorem compFin_smul (v : Pl F) {a : AF F} (ha : a.2 = 0) (z : AE F E) : compFin F E v (a • z) = 0 := by
  have : compFin F E v (algebraMap (AF F) (AE F E) a) = 0 := by
    change Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v a.2 ⊗ₜ[F] (1 : E) = 0
    rw [ha, map_zero, TensorProduct.zero_tmul]
  rw [Algebra.smul_def, map_mul, this, zero_mul]

theorem exists_section (h : IsCMExt F E σ) (τ : ∀ w : InfinitePlace F, EmbOver E w) :
    ∃ Φ : (InfinitePlace F → ℂ) → AE F E, Continuous Φ ∧ ∀ z, z = Φ (fun w => piInf (τ w) z) + eF F • z := by
  haveI := h.1
  have hr : ∀ w : InfinitePlace F, w.IsReal := fun w => IsTotallyReal.isReal w
  let ρ : (InfinitePlace F → ℝ) → AF F := fun t =>
    pairA F (fun w => (InfinitePlace.Completion.isometryEquivRealOfIsReal (hr w)).symm (t w)) 0
  have hρ : Continuous ρ := by
    have : Continuous fun (t : InfinitePlace F → ℝ) (w : InfinitePlace F) =>
        (InfinitePlace.Completion.isometryEquivRealOfIsReal (hr w)).symm (t w) :=
      continuous_pi fun w => (IsometryEquiv.continuous _).comp (continuous_apply w)
    exact this.prodMk continuous_const
  have eρ : ∀ t w, InfinitePlace.Completion.extensionEmbedding w ((ρ t).1 w) = t w := fun t w => by
    rw [← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply (hr w)]
    exact congrArg _ ((InfinitePlace.Completion.isometryEquivRealOfIsReal (hr w)).apply_symm_apply (t w))
  obtain ⟨a, ha, -⟩ := Levi.exists_inf h τ fun _ => Complex.I
  refine ⟨fun z => ρ (fun w => (z w).re) • 1 + ρ (fun w => (z w).im) • a, ?_, fun z => ?_⟩
  · have h1 : Continuous fun z : InfinitePlace F → ℂ => ρ fun w => (z w).re :=
      hρ.comp (continuous_pi fun w => Complex.continuous_re.comp (continuous_apply w))
    have h2 : Continuous fun z : InfinitePlace F → ℂ => ρ fun w => (z w).im :=
      hρ.comp (continuous_pi fun w => Complex.continuous_im.comp (continuous_apply w))
    have h3 : ∀ b : AE F E, Continuous fun x : AF F => x • b := fun b =>
      Continuous.fun_smul (f := fun x : AF F => x) (g := fun _ => b) continuous_id' continuous_const
    exact Continuous.fun_add (f := fun z : InfinitePlace F → ℂ => ρ (fun w => (z w).re) • (1 : AE F E))
      (g := fun z => ρ (fun w => (z w).im) • a) ((h3 1).comp' h1) ((h3 a).comp' h2)
  · refine Levi.ad_ext h τ (fun w => ?_) fun v => ?_
    · have e0 : (eF F).1 w = 0 := rfl
      rw [map_add, map_add, piInf_smul, piInf_smul, piInf_smul, eρ, eρ, ha, e0, map_zero, map_one, zero_mul, mul_one,
        add_zero, Complex.re_add_im]
    · have e0 : compFin F E v ((1 - eF F) • z) = 0 := compFin_smul v (sub_self (1 : Af F)) z
      rw [sub_smul, one_smul, map_sub, sub_eq_zero] at e0
      rw [map_add, map_add, compFin_smul v rfl, compFin_smul v rfl, zero_add, zero_add, e0]

end GlobalTheory.ThK.Dbl.St

end
