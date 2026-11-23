import Development.WeilBound.ThetaLifts.LocalTheory.UnramifiedCohomology.Lint
import Development.WeilBound.ThetaLifts.SmallCones.FcCols
import Development.WeilBound.ThetaLifts.SmallCones.ThetaUniq
import Development.WeilBound.ThetaLifts.LocalTheory.ConeShifts.EvFinIdemSelf
import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.Kcompact

noncomputable section

namespace PositivityTheory.ThKG.Loc.KInv

open scoped TensorProduct NNReal ENNReal Matrix Pointwise
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK PositivityTheory.ThKCT PositivityTheory.ThKCT.Unf PositivityTheory.ThKG.Loc.Cone
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

attribute [local instance] PositivityTheory.ThK.kc_ring PositivityTheory.ThK.adele_t2Space PositivityTheory.ThK.kc_smul

theorem push {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] {K K' : Subgroup G} (hK : IsCompact (K : Set G)) [CompactSpace K'] (π : K →* K')
    (hc : Continuous π) (hs : Function.Surjective π) (μ : Measure K') [μ.IsHaarMeasure] :
    ∃ (μK : Measure K) (_ : μK.IsHaarMeasure) (c : ℝ≥0), ∀ f : K' → ℂ, Continuous f → ∫ k, f k ∂μ = c • ∫ k, f (π k) ∂μK := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
  haveI : ((Measure.haar : Measure K).map π).IsHaarMeasure := Measure.isHaarMeasure_map_of_isFiniteMeasure _ π hc hs
  refine ⟨Measure.haar, inferInstance, Measure.haarScalarFactor μ ((Measure.haar : Measure K).map π), fun f hf => ?_⟩
  rw [← integral_map hc.measurable.aemeasurable hf.aestronglyMeasurable, ← integral_smul_nnreal_measure,
    ← Measure.isMulLeftInvariant_eq_smul]

namespace Tp

theorem ae_ring : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
theorem ae_smul : ContinuousSMul (AF F) (AE F E) := IsModuleTopology.toContinuousSMul (AF F) _
theorem ae_top : T2Space (AE F E) ∧ LocallyCompactSpace (AE F E) ∧ SecondCountableTopology (AE F E) := by
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)
  exact ⟨e.isEmbedding.t2Space, e.isClosedEmbedding.locallyCompactSpace, e.secondCountableTopology⟩
theorem ae_t2 : T2Space (AE F E) := ae_top.1
theorem ae_lc : LocallyCompactSpace (AE F E) := ae_top.2.1
theorem ae_sc : SecondCountableTopology (AE F E) := ae_top.2.2

attribute [local instance] ae_ring ae_smul ae_t2 ae_lc ae_sc

theorem units_top {A : Type} [Ring A] [TopologicalSpace A] [IsTopologicalRing A] [T2Space A] [LocallyCompactSpace A]
    [SecondCountableTopology A] : LocallyCompactSpace Aˣ ∧ SecondCountableTopology Aˣ := by
  haveI : SecondCountableTopology Aᵐᵒᵖ := MulOpposite.opHomeomorph.symm.secondCountableTopology
  haveI : LocallyCompactSpace Aᵐᵒᵖ := MulOpposite.opHomeomorph.symm.isClosedEmbedding.locallyCompactSpace
  exact ⟨Units.isClosedEmbedding_embedProduct.locallyCompactSpace, Units.isEmbedding_embedProduct.secondCountableTopology⟩

theorem ua_top {n : ℕ} (J : Matrix (Fin n) (Fin n) E) : LocallyCompactSpace (UA σ J) ∧ SecondCountableTopology (UA σ J) := by
  haveI : LocallyCompactSpace (Matrix (Fin n) (Fin n) (AE F E)) := inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → AE F E))
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) (AE F E)) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → AE F E))
  obtain ⟨h1, h2⟩ := units_top (A := Matrix (Fin n) (Fin n) (AE F E))
  have hc : Continuous (cA σ) := IsModuleTopology.continuous_of_linearMap (cA σ).toLinearMap
  have : IsClosed ((UG (cA σ) (incM F J) : Subgroup (GL (Fin n) (AE F E))) : Set (GL (Fin n) (AE F E))) :=
    isClosed_eq (((Units.continuous_val.matrix_transpose).matrix_mul continuous_const).matrix_mul
      (Units.continuous_val.matrix_map hc)) continuous_const
  exact ⟨this.locallyCompactSpace, TopologicalSpace.Subtype.secondCountableTopology _⟩

end Tp

namespace US

variable {n : ℕ} {X : Spc F E n}

variable (σ X) in

def uSub (v : Pl F) : Subgroup (UA σ X.J) where
  carrier := UAt σ X (evFin F v)
  one_mem' := fun u _ => by rw [show mat (1 : UA σ X.J) = 1 from rfl, sub_self, smul_zero]
  mul_mem' := fun {a b} ha hb u hu => by
    have e : mat (a * b) - 1 = (mat a - 1) * mat b + (mat b - 1) := by
      rw [show mat (a * b) = mat a * mat b from rfl, Matrix.sub_mul, Matrix.one_mul]; abel
    rw [e, smul_add, ← Matrix.smul_mul, ha u hu, hb u hu, Matrix.zero_mul, add_zero]
  inv_mem' := fun {a} ha u hu => by
    have h1 : mat a⁻¹ * mat a = 1 := a.1.inv_mul
    have e : mat a⁻¹ - 1 = -(mat a⁻¹ * (mat a - 1)) := by rw [Matrix.mul_sub, h1, Matrix.mul_one]; abel
    rw [e, smul_neg, ← Matrix.mul_smul, ha u hu, Matrix.mul_zero, neg_zero]

theorem kAt_eq (K : Subgroup (UA σ X.J)) (v : Pl F) : kAt K (evFin F v) = K ⊓ uSub σ X v :=
  congrArg (K ⊓ ·) (Subgroup.closure_eq (uSub σ X v))

theorem kAt_mem {K : Subgroup (UA σ X.J)} {v : Pl F} (k : kAt K (evFin F v)) : k.1 ∈ UAt σ X (evFin F v) :=
  ((kAt_eq K v).le k.2).2

theorem kAt_compact {K : Subgroup (UA σ X.J)} (hK : IsCompact (K : Set (UA σ X.J))) (v : Pl F) : CompactSpace (kAt K (evFin F v)) := by
  refine isCompact_iff_compactSpace.1 ?_
  rw [kAt_eq, Subgroup.coe_inf]
  refine hK.inter_right ?_
  have : (uSub σ X v : Set (UA σ X.J)) = ⋂ u : AF F, ⋂ _ : evFin F v u = 0, {g | u • (mat g - 1) = 0} := by
    ext g; simp only [Set.mem_iInter]; rfl
  rw [this]
  exact isClosed_iInter fun u => isClosed_iInter fun _ =>
    isClosed_eq (((PositivityTheory.ThK.kc_cont_mat X.J).sub continuous_const).const_smul u) continuous_const

end US

section Part

variable {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {a : AF F} (ha : a * a = a)

theorem part_mul (g h : UA σ J) : partU ha (g * h) = partU ha g * partU ha h :=
  Cone.mat_inj (mix_mul ha (mat g) (mat h)).symm

theorem cont_part : Continuous (partU (σ := σ) (J := J) ha) := by
  have c := PositivityTheory.ThK.kc_cont_mat (F := F) (σ := σ) J
  refine Continuous.subtype_mk (Units.continuous_iff.2 ⟨?_, ?_⟩) _
  · exact (c.const_smul a).add continuous_const
  · exact ((c.comp continuous_inv).const_smul a).add continuous_const

theorem part_vec (g : UA σ J) (z : Fin n → AE F E) : mat (partU ha g) *ᵥ z = a • (mat g *ᵥ z) + (1 - a) • z := by
  rw [mat_partU, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]

def partI (t : (AE F E)ˣ) : (AE F E)ˣ :=
  ⟨a • t.1 + (1 - a) • 1, a • (t⁻¹).1 + (1 - a) • 1,
    by rw [mix_mul ha, Units.mul_inv, ← add_smul, add_sub_cancel, one_smul],
    by rw [mix_mul ha, Units.inv_mul, ← add_smul, add_sub_cancel, one_smul]⟩

end Part

variable {B : Base F E} {n n₁ : ℕ} {Y : Spc F E n} {Y₁ : Spc F E n₁} {H : Plane E n n₁} {i₀ i₁ r s : ℕ}

theorem part_levi {a : AF F} (ha : a * a = a) {t : (AE F E)ˣ} {g : UA σ Y₁.J} {m : UA σ Y.J} (h : IsLevi H t g m) :
    IsLevi H (partI ha t) (partU ha g) (partU ha m) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [part_vec, h.1]
    simp only [partI, add_smul, smul_assoc, one_smul]
  · rw [part_vec, h.2.1]
    change _ = cA σ (a • (t⁻¹).1 + (1 - a) • 1) • _
    simp only [map_add, map_smul, map_one, add_smul, smul_assoc, one_smul]
  · simp only [mat_partU, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, h.2.2, Matrix.one_mul, Matrix.mul_one]

theorem part_unip {a : AF F} (ha : a * a = a) {u : UA σ Y.J} (h : u ∈ unip σ Y H) : partU ha u ∈ unip σ Y H := by
  obtain ⟨h1, h2⟩ := Fr.mem_unip.1 h
  refine Fr.mem_unip.2 ⟨by rw [part_vec, h1, ← add_smul, add_sub_cancel, one_smul], fun z => ?_⟩
  obtain ⟨c, hc⟩ := h2 z
  refine ⟨a • c, ?_⟩
  rw [part_vec, hc, smul_add, smul_assoc, sub_smul, one_smul]
  abel

theorem part_at {v : Pl F} {g : UA σ Y.J} (hg : g ∈ UAt σ Y (evFin F v)) : partU (idem_mul_self v) g = g := by
  have h := hg (1 - idem F v) (by rw [map_sub, map_one, Cone.evFin_idem_self, sub_self])
  refine Cone.mat_inj (sub_left_inj (a := 1) |>.1 ?_)
  rw [partU_sub_one]
  rw [sub_smul, one_smul, sub_eq_zero] at h
  exact h.symm

theorem htEx (hB : B.IsGood σ) (hY : Y.IsHerm σ B r s) (hH : H.IsAdapted σ B Y Y₁ i₀ i₁) {K : Subgroup (UA σ Y.J)}
    (hI : Iwa H K) {N : Type} [TopologicalSpace N] {nn : N → UA σ Y.J} {ι : UA σ Y₁.J →* UA σ Y.J} {mm : (AE F E)ˣ →* UA σ Y.J}
    (hemb : IsClosedEmbedding fun z : N × UA σ Y₁.J × (AE F E)ˣ => nn z.1 * ι z.2.1 * mm z.2.2)
    (hu : ∀ u, u ∈ unip σ Y H ↔ ∃ p, u = nn p) (hL : ∀ t g, IsLevi H t g (ι g * mm t)) :
    (∀ x, ∃ p u t, ∃ k ∈ K, x = nn p * ι u * mm t * k) ∧
    (∀ q g₁ t, mat (nn q * ι g₁ * mm t) *ᵥ incV F H.x = t.1 • incV F H.x) ∧
    ∃ ht : UA σ Y.J → ℝ≥0, Continuous ht ∧ (∀ x, ht x ≠ 0) ∧ (∀ x, ∀ k ∈ K, ht (x * k) = ht x) ∧
      ∀ (p : UA σ Y.J) (t : (AE F E)ˣ), mat p *ᵥ incV F H.x = t.1 • incV F H.x → ∀ x, ht (p * x) = absE F E t ^ (n₁ + 1) * ht x := by
  obtain ⟨ε', A', hfr⟩ := Fr.isFr hB (.inl hY) hH
  have hd := Fr.det_ne (.inl hY : Y.IsHerm σ B r s ∨ Y.IsSkew σ B r s)
  have dec : ∀ (p : UA σ Y.J) (t : (AE F E)ˣ), mat p *ᵥ incV F H.x = t.1 • incV F H.x → ∃ q g₁, p = nn q * ι g₁ * mm t :=
    fun p t hp => by
      obtain ⟨u, hu', g₁, m, hm, e, -⟩ := Fr.stab_dec hB.cm hfr hd p t hp
      obtain ⟨q, rfl⟩ := (hu u).1 hu'
      exact ⟨q, g₁, by rw [e, Fr.levi_uniq hfr hm (hL t g₁), mul_assoc]⟩
  have act : ∀ q g₁ t, mat (nn q * ι g₁ * mm t) *ᵥ incV F H.x = t.1 • incV F H.x := fun q g₁ t => by
    rw [mul_assoc, Fr.mat_mul, ← Matrix.mulVec_mulVec, (hL t g₁).1, Matrix.mulVec_smul, (Fr.mem_unip.1 ((hu _).2 ⟨q, rfl⟩)).1]
  have hG : ∀ x, ∃ p u t, ∃ k ∈ K, x = nn p * ι u * mm t * k := fun x => by
    obtain ⟨p, k, l, hk, hp, rfl⟩ := hI.2 x
    obtain ⟨q, g₁, rfl⟩ := dec p l hp
    exact ⟨q, g₁, l, k, hk, rfl⟩
  have inv : ∀ (p : UA σ Y.J) (t : (AE F E)ˣ), mat p *ᵥ incV F H.x = t.1 • incV F H.x →
      mat p⁻¹ *ᵥ incV F H.x = (t⁻¹).1 • incV F H.x := fun p t hp => by
    have := Fr.mat_cancel p (incV F H.x)
    rw [hp, Matrix.mulVec_smul] at this
    conv_rhs => rw [← this, smul_smul, Units.inv_mul, one_smul]
  have le1 : ∀ k ∈ K, ∀ t : (AE F E)ˣ, mat k *ᵥ incV F H.x = t.1 • incV F H.x → absE F E t ≤ 1 := fun k hk t ht => by
    obtain ⟨C, hC⟩ := ((hemb.isCompact_preimage hI.1).image
      (GlobalTheory.Doubling.continuous_absE.comp (continuous_snd.comp continuous_snd))).bddAbove
    have pw : ∀ j : ℕ, mat (k ^ j) *ᵥ incV F H.x = (t ^ j).1 • incV F H.x := fun j => by
      induction j with
      | zero => simp [Fr.mat_one]
      | succ j ih => rw [pow_succ, Fr.mat_mul, ← Matrix.mulVec_mulVec, ht, Matrix.mulVec_smul, ih, smul_smul, pow_succ',
          Units.val_mul]
    by_contra hlt
    obtain ⟨j, hj⟩ := pow_unbounded_of_one_lt C (not_le.1 hlt)
    obtain ⟨q, g₁, e⟩ := dec _ _ (pw j)
    have : absE F E (t ^ j) ≤ C := hC ⟨(q, g₁, t ^ j), by
      change nn q * ι g₁ * mm (t ^ j) ∈ K
      rw [← e]; exact pow_mem hk j, rfl⟩
    rw [map_pow] at this
    exact absurd hj (not_lt.2 this)
  have one : ∀ k ∈ K, ∀ t : (AE F E)ˣ, mat k *ᵥ incV F H.x = t.1 • incV F H.x → absE F E t = 1 := fun k hk t ht => by
    have a1 := le1 k hk t ht
    have a2 := le1 _ (inv_mem hk) _ (inv k t ht)
    have a3 : absE F E t * absE F E t⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
    exact le_antisymm a1 (a3 ▸ mul_le_of_le_one_right zero_le a2)
  refine ⟨hG, act, ?_⟩
  choose P U T k₀ hk₀ hx using hG
  let ht : UA σ Y.J → ℝ≥0 := fun x => absE F E (T x) ^ (n₁ + 1)
  have spec : ∀ q g₁ t, ∀ k ∈ K, ht (nn q * ι g₁ * mm t * k) = absE F E t ^ (n₁ + 1) := fun q g₁ t k hk => by
    have e := hx (nn q * ι g₁ * mm t * k)
    set x := nn q * ι g₁ * mm t * k with hxd
    have h1 : (nn q * ι g₁ * mm t)⁻¹ * (nn (P x) * ι (U x) * mm (T x)) = k * (k₀ x)⁻¹ := by
      rw [← mul_left_inj (k₀ x), mul_assoc, ← e, hxd]; group
    have := one _ (mul_mem hk (inv_mem (hk₀ x))) (T x * t⁻¹) (by
      rw [← h1, Fr.mat_mul, ← Matrix.mulVec_mulVec, act, Matrix.mulVec_smul, inv _ _ (act q g₁ t), smul_smul, Units.val_mul])
    have h2 : absE F E (T x) = absE F E t := by rw [← inv_mul_cancel_right (T x) t, map_mul, this, one_mul]
    simp only [ht, h2]
  have htK : ∀ x, ∀ k ∈ K, ht (x * k) = ht x := fun x k hk => by
    conv_lhs => rw [hx x, mul_assoc, spec _ _ _ _ (mul_mem (hk₀ x) hk)]
  have htP : ∀ (p : UA σ Y.J) (t : (AE F E)ˣ), mat p *ᵥ incV F H.x = t.1 • incV F H.x → ∀ x,
      ht (p * x) = absE F E t ^ (n₁ + 1) * ht x := fun p t hp x => by
    obtain ⟨q, g₁, e⟩ := dec (p * (nn (P x) * ι (U x) * mm (T x))) (t * T x) (by
      rw [Fr.mat_mul, ← Matrix.mulVec_mulVec, act, Matrix.mulVec_smul, hp, smul_smul, Units.val_mul, mul_comm])
    conv_lhs => rw [hx x, ← mul_assoc, e, spec _ _ _ _ (hk₀ x), map_mul, mul_pow]
  have ht0 : ∀ t : (AE F E)ˣ, absE F E t ≠ 0 := fun t => ((Group.isUnit t).map (absE F E)).ne_zero
  have htc : Continuous ht := continuous_iff_isClosed.2 fun C hC => by
    have : ht ⁻¹' C = ((fun z : N × UA σ Y₁.J × (AE F E)ˣ => nn z.1 * ι z.2.1 * mm z.2.2) ''
        {z | absE F E z.2.2 ^ (n₁ + 1) ∈ C}) * (K : Set (UA σ Y.J)) := by
      ext x
      constructor
      · exact fun h => ⟨_, ⟨(P x, U x, T x), h, rfl⟩, k₀ x, hk₀ x, (hx x).symm⟩
      · rintro ⟨_, ⟨z, hz, rfl⟩, k, hk, rfl⟩
        change ht _ ∈ C
        rw [spec _ _ _ _ hk]; exact hz
    rw [this]
    exact (hemb.isClosedMap _ (hC.preimage ((GlobalTheory.Doubling.continuous_absE.comp
      (continuous_snd.comp continuous_snd)).pow _))).mul_right_of_isCompact hI.1
  exact ⟨ht, htc, fun x => pow_ne_zero _ (ht0 _), htK, htP⟩

theorem part_comm {v : Pl F} {g : UA σ Y.J} (hg : g ∈ UAt σ Y (evFin F v)) (k : UA σ Y.J) :
    k * g = partU (idem_mul_self v) k * g * ((partU (idem_mul_self v) k)⁻¹ * k) := by
  have ha := idem_mul_self v
  obtain ⟨c, hc⟩ : ∃ c, c = (partU ha k)⁻¹ * k := ⟨_, rfl⟩
  have c1 : partU ha c = 1 := by
    rw [hc, part_mul, ← part_at (inv_mem (show partU ha k ∈ US.uSub σ Y v from partU_idem_mem v _) :
      _ ∈ US.uSub σ Y v)]
    nth_rewrite 1 [part_at (inv_mem (show partU ha k ∈ US.uSub σ Y v from partU_idem_mem v _) : _ ∈ US.uSub σ Y v)]
    rw [part_at (inv_mem (show partU ha k ∈ US.uSub σ Y v from partU_idem_mem v _) : _ ∈ US.uSub σ Y v),
      inv_mul_cancel]
  have c2 : idem F v • (mat c - 1) = 0 := by rw [← partU_sub_one ha, c1, Fr.mat_one, sub_self]
  have c3 : idem F v • (mat g - 1) = mat g - 1 := by rw [← partU_sub_one ha, part_at hg]
  have c4 : g * c = c * g := Cone.mat_inj (by
    have l : (mat g - 1) * (mat c - 1) = 0 := by rw [← c3, smul_mul_assoc, ← mul_smul_comm, c2, mul_zero]
    have r : (mat c - 1) * (mat g - 1) = 0 := by rw [← c3, mul_smul_comm, ← smul_mul_assoc, c2, zero_mul]
    rw [Fr.mat_mul, Fr.mat_mul, ← sub_eq_zero, ← sub_self (0 : Matrix _ _ _)]
    nth_rewrite 1 [← l]
    rw [← r]
    noncomm_ring)
  rw [← hc, mul_assoc, c4, hc]; group

set_option maxHeartbeats 800000 in
theorem kInv (hB : B.IsGood σ) (hY : Y.IsHerm σ B r s) (hH : H.IsAdapted σ B Y Y₁ i₀ i₁) {K : Subgroup (UA σ Y.J)}
    (hK : IsStab B K) (hI : Iwa H K) (v : Pl F) (μ : Measure (kAt K (evFin F v))) [μ.IsHaarMeasure] {f : UA σ Y.J → ℂ}
    (hf : ContinuousOn f (UAt σ Y (evFin F v)))
    (hP : ∀ u ∈ unip σ Y H, u ∈ UAt σ Y (evFin F v) → ∀ t g₁ m, IsLevi (W₁ := Y₁) H t g₁ m → m ∈ UAt σ Y (evFin F v) →
      g₁ ∈ UAt σ Y₁ (evFin F v) → At (evFin F v) (t.1 - 1) →
      ∀ x ∈ UAt σ Y (evFin F v), f (u * m * x) = ((absE F E t ^ (n₁ + 1) : ℝ≥0) : ℝ) * f x)
    {g : UA σ Y.J} (hg : g ∈ UAt σ Y (evFin F v)) : ∫ k, f (k.1 * g) ∂μ = ∫ k, f k.1 ∂μ := by
  obtain ⟨N, _, _, _, _, μN, _, _, nn, ι, mm, χ, hpar, hχ, hu, hL, hR, -⟩ := parEx hB (.inl hY) hH
  obtain ⟨ε', A', hfr⟩ := Fr.isFr hB (.inl hY) hH
  have hd := Fr.det_ne (.inl hY : Y.IsHerm σ B r s ∨ Y.IsSkew σ B r s)
  have hd₁ : IsUnit Y₁.J.det := hfr.isUnit_det hd.isUnit
  have h₁ : ∀ i j, σ (Y₁.J j i) = (((1 : ℤˣ) : ℤ) : E) * Y₁.J i j := fun i j => by
    rw [← hH.gram]
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, map_sum, map_mul, hY.herm,
      PositivityTheory.ThKG.Tow.Levi.sig_sig hB.cm, Finset.sum_mul, Units.val_one, Int.cast_one, one_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  obtain ⟨-, ⟨ν, -, hν, -⟩, hνr⟩ := PositivityTheory.ThKF.unimodularity_holds F E σ hB.cm n Y.J 1 (fun i j => by simp [hY.herm]) hd
  obtain ⟨-, ⟨μH, -, hμH, -⟩, hμr⟩ := PositivityTheory.ThKF.unimodularity_holds F E σ hB.cm n₁ Y₁.J 1 h₁ hd₁.ne_zero
  haveI := hνr ν hν
  haveI := hμr μH hμH
  haveI := (Tp.ua_top (F := F) (σ := σ) Y.J).1
  haveI := (Tp.ua_top (F := F) (σ := σ) Y.J).2
  haveI := (Tp.ua_top (F := F) (σ := σ) Y₁.J).1
  haveI := (Tp.ua_top (F := F) (σ := σ) Y₁.J).2
  haveI := Tp.ae_lc (F := F) (E := E)
  haveI := Tp.ae_sc (F := F) (E := E)
  haveI := (Tp.units_top (A := AE F E)).1
  haveI := (Tp.units_top (A := AE F E)).2
  haveI : BorelSpace (UA σ Y.J) := ⟨rfl⟩
  haveI : BorelSpace (UA σ Y₁.J) := ⟨rfl⟩
  haveI : BorelSpace (AE F E)ˣ := ⟨rfl⟩
  haveI := US.kAt_compact hI.1 v
  obtain ⟨hG, act, ht, htc, ht1, htK, htP⟩ := htEx hB hY hH hI hpar.emb hu hL
  have ht0 : ∀ t : (AE F E)ˣ, absE F E t ≠ 0 := fun t => ((Group.isUnit t).map (absE F E)).ne_zero
  have ha := idem_mul_self v
  have htne : ∀ x, ((ht x : ℝ) : ℂ) ≠ 0 := fun x => by exact_mod_cast ht1 x
  let f' : UA σ Y.J → ℂ := fun x => f (partU ha x) * ((ht x : ℝ) : ℂ) / ((ht (partU ha x) : ℝ) : ℂ)
  have hc1 : Continuous fun x => ((ht x : ℝ) : ℂ) := by fun_prop
  have hf' : Continuous f' := ((hf.comp_continuous (cont_part ha) (partU_idem_mem v)).mul hc1).div (hc1.comp (cont_part ha))
    fun x => htne _
  let π : K →* kAt K (evFin F v) := MonoidHom.mk' (fun k => ⟨partU ha k.1, partU_mem_kAt hK k.2 v⟩)
    fun a b => Subtype.ext (part_mul ha _ _)
  have πc : Continuous π := ((cont_part ha).comp continuous_subtype_val).subtype_mk _
  have πs : Function.Surjective π := fun k => ⟨⟨k.1, k.2.1⟩, Subtype.ext (part_at (US.kAt_mem k))⟩
  obtain ⟨μK, _, c, hc⟩ := push hI.1 π πc πs μ
  have main := KInv.int ν μH Measure.haar hpar hR hI.1 μK hG hf' (fun p u t x => by
    have hl := part_levi ha (hL t u)
    have hn := part_unip ha ((hu _).2 ⟨p, rfl⟩)
    have e1 : partU ha (nn p * ι u * mm t * x) = partU ha (nn p) * partU ha (ι u * mm t) * partU ha x := by
      rw [mul_assoc (nn p), part_mul, part_mul]
    have e2 := hP _ hn (partU_idem_mem v _) _ _ _ hl (partU_idem_mem v _) (partU_idem_mem v _) (by
      change At _ (idem F v • t.1 + (1 - idem F v) • 1 - 1)
      rw [show idem F v • t.1 + (1 - idem F v) • (1 : AE F E) - 1 = idem F v • (t.1 - 1) by
        rw [smul_sub, sub_smul, one_smul]; abel]
      exact Cone.at_idem v _) _ (partU_idem_mem v x)
    have e3 := htP (partU ha (nn p) * partU ha (ι u * mm t)) (partI ha t) (by
      rw [Fr.mat_mul, ← Matrix.mulVec_mulVec, hl.1, Matrix.mulVec_smul, (Fr.mem_unip.1 hn).1]) (partU ha x)
    have e4 : (((χ t : ℝ≥0) : ℝ) : ℂ) * (((absE F E t ^ (n₁ + 1) : ℝ≥0) : ℝ) : ℂ) = 1 := by exact_mod_cast hχ t
    have e5 : (((absE F E (partI ha t) ^ (n₁ + 1) : ℝ≥0) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast pow_ne_zero _ (ht0 _)
    have e6 := htne (partU ha x)
    simp only [f', e1, e2, e3, htP _ _ (act p u t), NNReal.coe_mul, Complex.ofReal_mul]
    field_simp
    linear_combination (f (partU ha x) * ((ht x : ℝ) : ℂ)) * e4)
  have val : ∀ g ∈ UAt σ Y (evFin F v), ∀ k : K, f' (k.1 * g) = f ((π k).1 * g) := fun g hg k => by
    have e1 : partU ha (k.1 * g) = partU ha k.1 * g := by rw [part_mul, part_at hg]
    have e2 := part_comm hg k.1
    have e3 : ht (k.1 * g) = ht (partU ha k.1 * g) := by
      conv_lhs => rw [e2, htK _ _ (mul_mem (inv_mem (partU_mem_kAt hK k.2 v).1) k.2)]
    simp only [f', e1, e3]
    exact mul_div_cancel_right₀ _ (htne _)
  have tr : ∀ g ∈ UAt σ Y (evFin F v), ∫ k, f (k.1 * g) ∂μ = c • ∫ k : K, f' (k.1 * g) ∂μK := fun g hg => by
    rw [hc (fun k => f (k.1 * g)) (hf.comp_continuous (continuous_subtype_val.mul continuous_const)
      fun k => (US.uSub σ Y v).mul_mem (US.kAt_mem k) hg)]
    simp only [val g hg]
  have t1 := tr 1 (US.uSub σ Y v).one_mem
  simp only [mul_one] at t1
  rw [tr g hg, main g, t1]

end PositivityTheory.ThKG.Loc.KInv

end
