import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.RightOnto

noncomputable section

namespace PositivityTheory.KCo

open GlobalTheory.WeilM GlobalTheory.SplitFlip Matrix ValuativeRel Topology

section Avg

variable {A : Type} [AddCommGroup A] (L₀ L : AddSubgroup A) [Fintype (L ⧸ L₀.addSubgroupOf L)] {f : A → ℂ}

theorem avg_inv (hf : ∀ a ∈ L₀, ∀ b, f (b + a) = f b) {a : A} (ha : a ∈ L) (b : A) :
    ∑ q : L ⧸ L₀.addSubgroupOf L, f (b + a + (q.out : L)) = ∑ q : L ⧸ L₀.addSubgroupOf L, f (b + (q.out : L)) := by
  rw [← Equiv.sum_comp (Equiv.addLeft (QuotientAddGroup.mk (⟨a, ha⟩ : L) : L ⧸ L₀.addSubgroupOf L))
    fun q => f (b + (q.out : L))]
  refine Finset.sum_congr rfl fun q _ => ?_
  have h : QuotientAddGroup.mk (s := L₀.addSubgroupOf L) (⟨a, ha⟩ + q.out) =
      QuotientAddGroup.mk (Equiv.addLeft (QuotientAddGroup.mk (⟨a, ha⟩ : L) : L ⧸ L₀.addSubgroupOf L) q).out := by simp
  have h1 := hf _ (AddSubgroup.mem_addSubgroupOf.1 (QuotientAddGroup.eq.1 h)) (b + a + (q.out : L))
  rw [← h1]
  congr 1
  push_cast
  abel

theorem avg_off (hf : ∀ b ∉ L, f b = 0) {b : A} (hb : b ∉ L) : ∑ q : L ⧸ L₀.addSubgroupOf L, f (b + (q.out : L)) = 0 :=
  Finset.sum_eq_zero fun q _ => hf _ fun h => hb (by simpa using sub_mem h q.out.2)

theorem avg_zero (hf : ∀ a ∈ L₀, ∀ b, f (b + a) = f b) (h0 : ∀ b ∉ L₀, f b = 0) :
    ∑ q : L ⧸ L₀.addSubgroupOf L, f (0 + (q.out : L)) = f 0 := by
  rw [Finset.sum_eq_single 0]
  · exact hf _ (AddSubgroup.mem_addSubgroupOf.1 ((QuotientAddGroup.eq_zero_iff _).1 (Quotient.out_eq _))) 0
  · intro q _ hq
    refine h0 _ fun h => hq ?_
    rw [← Quotient.out_eq q]
    exact (QuotientAddGroup.eq_zero_iff _).2 (AddSubgroup.mem_addSubgroupOf.2 (by simpa using h))
  · simp

end Avg

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

section Box

variable {S : Type} [Fintype S]

def bx (S : Type) (c : k) : AddSubgroup (S → k) where
  carrier := {b | ∀ s, valuation k (b s) ≤ valuation k c}
  add_mem' ha hb s := (valuation k).map_add_le (ha s) (hb s)
  zero_mem' s := by simp
  neg_mem' ha s := by simpa using ha s

theorem bx_compact (c : k) : IsCompact (bx S c : Set (S → k)) := by
  have := isCompact_univ_pi fun _ : S => IsNonarchimedeanLocalField.isCompact_closedBall k (valuation k c)
  convert this using 1
  ext b
  simp [bx]

theorem bx_open {c : k} (hc : c ≠ 0) : IsOpen (bx S c : Set (S → k)) := by
  refine AddSubgroup.isOpen_of_mem_nhds _ (g := 0) ?_
  have h : {x : k | valuation k x < valuation k c} ∈ 𝓝 (0 : k) :=
    (IsValuativeTopology.hasBasis_nhds_zero' k).mem_of_mem (by simpa using hc)
  refine Filter.mem_of_superset (set_pi_mem_nhds Set.finite_univ fun _ _ => h) fun b hb s => le_of_lt (hb s trivial)

theorem bx_finite {c : k} (c' : k) (hc : c ≠ 0) : Finite (bx S c' ⧸ (bx S c).addSubgroupOf (bx S c')) :=
  have : CompactSpace (bx S c') := isCompact_iff_compactSpace.1 (bx_compact c')
  AddSubgroup.quotient_finite_of_isOpen _ ((bx_open hc).preimage continuous_subtype_val)

theorem bx_small {W : Set (S → k)} (hW : W ∈ 𝓝 (0 : S → k)) : ∃ c : k, c ≠ 0 ∧ (bx S c : Set (S → k)) ⊆ W := by
  rw [nhds_pi, Filter.mem_pi] at hW
  obtain ⟨I, -, t, ht, hI⟩ := hW
  obtain ⟨γ, hγ, h⟩ := (IsValuativeTopology.hasBasis_nhds_zero' k).mem_iff.1 (Filter.iInter_mem.2 ht)
  obtain ⟨y, rfl⟩ := ValuativeRel.valuation_surjective γ
  obtain ⟨r, hr, hr1⟩ := Valuation.IsNontrivial.exists_lt_one (v := valuation k)
  have hy : y ≠ 0 := by simpa using hγ
  refine ⟨y * r, mul_ne_zero hy (by simpa using hr), fun b hb => hI fun s _ => Set.mem_iInter.1 (h ?_) s⟩
  refine lt_of_le_of_lt (hb s) ?_
  rw [map_mul]
  exact mul_lt_of_lt_one_right (zero_lt_iff.2 hγ) hr1

theorem bx_large {L : Set (S → k)} (hL : IsCompact L) : ∃ c : k, c ≠ 0 ∧ L ⊆ bx S c := by
  have hb : ∀ (T : Finset S) (b : S → k), ∃ c : k, c ≠ 0 ∧ ∀ s ∈ T, valuation k (b s) ≤ valuation k c := by
    classical
    intro T b
    induction T using Finset.induction_on with
    | empty => exact ⟨1, one_ne_zero, by simp⟩
    | insert s T _ ih =>
      obtain ⟨c, hc, h⟩ := ih
      rcases le_total (valuation k (b s)) (valuation k c) with h1 | h1
      · exact ⟨c, hc, by simpa using ⟨h1, h⟩⟩
      · refine ⟨b s, fun e => hc (by simpa [e] using h1), ?_⟩
        simpa using fun a ha => (h a ha).trans h1
  have : Nonempty {c : k // c ≠ 0} := ⟨⟨1, one_ne_zero⟩⟩
  obtain ⟨c, h⟩ := hL.elim_directed_cover (fun c : {c : k // c ≠ 0} => (bx S c.1 : Set (S → k))) (fun c => bx_open c.2)
    (fun b _ => by
      obtain ⟨c, hc, h⟩ := hb Finset.univ b
      exact Set.mem_iUnion.2 ⟨⟨c, hc⟩, fun s => h s (Finset.mem_univ s)⟩)
    (fun c c' => by
      rcases le_total (valuation k c.1) (valuation k c'.1) with h | h
      · exact ⟨c', fun b hb s => (hb s).trans h, subset_rfl⟩
      · exact ⟨c, subset_rfl, fun b hb s => (hb s).trans h⟩)
  exact ⟨c.1, c.2, h⟩

end Box

variable {n d : ℕ} (S : Finset (Fin n)) (i : Fin n)

def cmb (a : S → k) (Y : Matrix (Fin n) (Fin d) k) : Fin d → k := ∑ s : S, a s • Y s

def mv (x : k) (a : S → k) (Y : Matrix (Fin n) (Fin d) k) : Matrix (Fin n) (Fin d) k := Y.updateRow i (x • Y i + cmb S a Y)

variable {S i}

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem mv_row (hi : i ∉ S) (x : k) (a : S → k) (Y : Matrix (Fin n) (Fin d) k) (s : S) : mv S i x a Y s = Y s :=
  updateRow_ne fun e => hi (e ▸ s.2)

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem mv_mv (hi : i ∉ S) (x y : k) (a b : S → k) (Y : Matrix (Fin n) (Fin d) k) :
    mv S i x a (mv S i y b Y) = mv S i (x * y) (x • b + a) Y := by
  have h : cmb S a (mv S i y b Y) = cmb S a Y := Finset.sum_congr rfl fun s _ => by rw [mv_row hi]
  rw [mv, h]
  simp only [mv, updateRow_self, updateRow_idem, cmb, Pi.add_apply, Pi.smul_apply, add_smul, smul_add, Finset.sum_add_distrib,
    Finset.smul_sum, smul_smul, smul_eq_mul, add_assoc]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem mv_one (Y : Matrix (Fin n) (Fin d) k) : mv S i 1 0 Y = Y := by simp [mv, cmb]

theorem continuous_mv (x : k) : Continuous fun p : (S → k) × Matrix (Fin n) (Fin d) k => mv S i x p.1 p.2 := by
  refine continuous_pi fun r => ?_
  by_cases h : r = i
  · subst h
    simp only [mv, updateRow_self, cmb]
    fun_prop
  · simp only [mv, updateRow_ne h]
    fun_prop

theorem exists_gl (hi : i ∉ S) (ν α : kˣ →* ℂˣ) (x : kˣ) (a : S → k) : ∃ g : GL (Fin n) k, ∀ Φ : Matrix (Fin n) (Fin d) k → ℂ,
    omB ν α g 1 Φ = ((ν x : ℂ) * apow x ((d : ℂ) / 2)) • fun Y => Φ (mv S i x a Y) := by
  classical
  let c : Fin n → k := fun r => if h : r ∈ S then a ⟨r, h⟩ else if r = i then x else 0
  let M : Matrix (Fin n) (Fin n) k := (1 : Matrix (Fin n) (Fin n) k).updateRow i (∑ r, c r • (1 : Matrix (Fin n) (Fin n) k) r)
  have hd : Mᵀ.det = x := by
    rw [det_transpose, det_updateRow_sum]
    simp [c, hi]
  have hm : ∀ Y : Matrix (Fin n) (Fin d) k, M * Y = mv S i (x : k) a Y := fun Y => by
    rw [updateRow_mul, Matrix.one_mul, mv]
    congr 1
    have e : ∀ r, (c r • (1 : Matrix (Fin n) (Fin n) k) r) ᵥ* Y = c r • Y r := fun r => by
      rw [smul_vecMul]
      exact congrArg _ (congrFun (Matrix.one_mul Y) r)
    rw [sum_vecMul, Finset.sum_congr rfl fun r _ => e r, ← Finset.sum_add_sum_compl S, add_comm, Finset.sum_eq_single i,
      ← Finset.sum_coe_sort S]
    · simp [c, hi, cmb]
    · intro r hr h
      simp [c, Finset.mem_compl.1 hr, h]
    · simp [hi]
  refine ⟨GeneralLinearGroup.mkOfDetNeZero Mᵀ (hd ▸ x.ne_zero), fun Φ => funext fun Y => ?_⟩
  have e : gdet (GeneralLinearGroup.mkOfDetNeZero Mᵀ (hd ▸ x.ne_zero)) = x := Units.ext hd
  simp only [omB, e, gdet, map_one]
  simp [hm]

theorem mv_aug (hi : i ∉ S) (ν α : kˣ →* ℂˣ) (x : kˣ) (a : S → k) {Φ : Matrix (Fin n) (Fin d) k → ℂ}
    (hΦ : Φ ∈ SB (Matrix (Fin n) (Fin d) k)) :
    (((ν x : ℂ) * apow x ((d : ℂ) / 2)) • fun Y => Φ (mv S i x a Y)) ∈ SB (Matrix (Fin n) (Fin d) k) ∧
      (((ν x : ℂ) * apow x ((d : ℂ) / 2)) • fun Y => Φ (mv S i x a Y)) - Φ ∈ aug n d ν α := by
  obtain ⟨g, hg⟩ := exists_gl (d := d) hi ν α x a
  rw [← hg]
  exact ⟨omB_mem_SB ν α g 1 hΦ, Submodule.subset_span ⟨g, Φ, hΦ, rfl⟩⟩

theorem sum_aug (hi : i ∉ S) (ν α : kˣ →* ℂˣ) {Q : Type} [Fintype Q] (a : Q → S → k) {Φ : Matrix (Fin n) (Fin d) k → ℂ}
    (hΦ : Φ ∈ SB (Matrix (Fin n) (Fin d) k)) :
    (fun Y => ∑ q, Φ (mv S i 1 (a q) Y)) ∈ SB (Matrix (Fin n) (Fin d) k) ∧
      (fun Y => ∑ q, Φ (mv S i 1 (a q) Y)) - (Fintype.card Q : ℂ) • Φ ∈ aug n d ν α := by
  have h := fun q => mv_aug hi ν α 1 (a q) hΦ
  simp only [map_one, Units.val_one, apow_one, mul_one, one_smul] at h
  have e : (fun Y => ∑ q, Φ (mv S i 1 (a q) Y)) = ∑ q, fun Y => Φ (mv S i 1 (a q) Y) := by
    funext Y
    simp
  rw [e]
  refine ⟨Submodule.sum_mem _ fun q _ => (h q).1, ?_⟩
  convert Submodule.sum_mem _ fun q (_ : q ∈ Finset.univ) => (h q).2 using 1
  simp [Finset.sum_sub_distrib, Nat.cast_smul_eq_nsmul]

theorem exists_inv (hi : i ∉ S) {Φ : Matrix (Fin n) (Fin d) k → ℂ} (hΦ : Φ ∈ SB (Matrix (Fin n) (Fin d) k)) :
    ∃ c : k, c ≠ 0 ∧ ∀ a ∈ bx S c, ∀ Y, Φ (mv S i 1 a Y) = Φ Y := by
  have ho : IsOpen {p : (S → k) × Matrix (Fin n) (Fin d) k | Φ (mv S i 1 p.1 p.2) - Φ p.2 = 0} :=
    ((hΦ.1.comp_continuous (continuous_mv 1)).sub (hΦ.1.comp_continuous continuous_snd)).isOpen_fiber 0
  obtain ⟨u, v, hu, -, h0, hv, huv⟩ := generalized_tube_lemma (isCompact_singleton (x := (0 : S → k))) hΦ.2.isCompact ho
    (by rintro ⟨_, Y⟩ ⟨rfl, -⟩; simp [mv_one])
  obtain ⟨c, hc, h⟩ := bx_small (hu.mem_nhds (h0 rfl))
  have key : ∀ a ∈ bx S c, ∀ Y, Φ Y ≠ 0 → Φ (mv S i 1 a Y) = Φ Y := fun a ha Y hY =>
    sub_eq_zero.1 (huv (Set.mk_mem_prod (h ha) (hv (subset_tsupport _ hY))))
  refine ⟨c, hc, fun a ha Y => ?_⟩
  by_cases hY : Φ Y = 0
  · by_contra hne
    have := key _ (neg_mem ha) _ (hY ▸ hne)
    rw [mv_mv hi] at this
    simp only [mul_one, one_smul, add_neg_cancel, mv_one] at this
    exact hne this.symm
  · exact key a ha Y hY

theorem exists_bound {K : Set (Matrix (Fin n) (Fin d) k)} (hK : IsCompact K) (hU : ∀ Y ∈ K, LinearIndepOn k Y S) :
    ∃ L : Set (S → k), IsCompact L ∧ ∀ Y ∈ K, ∀ b, Y i = cmb S b Y → b ∈ L := by
  classical
  have : LocallyCompactSpace (Matrix (Fin n) (Fin d) k) := inferInstanceAs (LocallyCompactSpace (Fin n → Fin d → k))
  refine hK.induction_on (p := fun s => ∃ L : Set (S → k), IsCompact L ∧ ∀ Y ∈ s, ∀ b, Y i = cmb S b Y → b ∈ L)
    ⟨∅, isCompact_empty, by simp⟩ (fun s t hst ⟨L, h1, h2⟩ => ⟨L, h1, fun Y hY => h2 Y (hst hY)⟩)
    (fun s t ⟨L, h1, h2⟩ ⟨L', h3, h4⟩ => ⟨L ∪ L', h1.union h3, fun Y hY b hb =>
      hY.elim (fun h => Or.inl (h2 Y h b hb)) fun h => Or.inr (h4 Y h b hb)⟩) fun Y₀ hY₀ => ?_
  let R : Matrix (Fin n) (Fin d) k → Matrix S (Fin d) k := fun Y => Y.submatrix Subtype.val id
  have hR : Continuous R := continuous_id.matrix_submatrix _ _
  have hinj : Function.Injective (R Y₀).vecMulLinear := vecMul_injective_iff.2 (hU Y₀ hY₀)
  obtain ⟨l, hl⟩ := LinearMap.exists_leftInverse_of_injective _ (LinearMap.ker_eq_bot.2 hinj)
  let B : Matrix (Fin d) S k := (LinearMap.toMatrix' l)ᵀ
  have hB : R Y₀ * B = 1 := by
    ext s s'
    have := congrFun (LinearMap.congr_fun hl (Pi.single s 1)) s'
    rw [LinearMap.comp_apply, ← LinearMap.toMatrix'_mulVec, vecMulLinear_apply, single_one_vecMul] at this
    rw [Matrix.mul_apply, Matrix.one_apply]
    simpa [mulVec, dotProduct, B, mul_comm, Pi.single_apply, eq_comm] using this
  have hc : Continuous fun Y => (R Y * B).det := (hR.matrix_mul continuous_const).matrix_det
  have hW : {Y | (R Y * B).det ≠ 0} ∈ 𝓝 Y₀ := (isOpen_ne_fun hc continuous_const).mem_nhds (by simp [hB])
  obtain ⟨t, ht, htW, htc⟩ := local_compact_nhds hW
  refine ⟨t, mem_nhdsWithin_of_mem_nhds ht, (fun Y => ((R Y * B).det)⁻¹ • ((Y i ᵥ* B) ᵥ* (R Y * B).adjugate)) '' t,
    htc.image_of_continuousOn ((hc.continuousOn.inv₀ fun Y hY => htW hY).smul (Continuous.continuousOn ?_)), fun Y hY b hb => ⟨Y, hY, ?_⟩⟩
  · exact ((continuous_apply i).matrix_vecMul continuous_const).matrix_vecMul (hR.matrix_mul continuous_const).matrix_adjugate
  · have e : Y i = b ᵥ* R Y := by
      rw [hb]
      ext j
      simp [cmb, vecMul, dotProduct, R]
    have h0 : (R Y * B).det ≠ 0 := htW hY
    simp only
    rw [e, vecMul_vecMul b (R Y) B, vecMul_vecMul, mul_adjugate, vecMul_smul, vecMul_one, smul_smul, inv_mul_cancel₀ h0, one_smul]

theorem step (hi : i ∉ S) {ν α : kˣ →* ℂˣ} (hν : USm ν) (h1 : ν ≠ 1) {Φ : Matrix (Fin n) (Fin d) k → ℂ}
    (hΦ : Φ ∈ SB (Matrix (Fin n) (Fin d) k)) (h0 : ∀ Y : Matrix (Fin n) (Fin d) k, ¬ LinearIndepOn k Y S → Φ Y = 0) :
    ∃ Ψ ∈ SB (Matrix (Fin n) (Fin d) k), (∀ Y : Matrix (Fin n) (Fin d) k, ¬ LinearIndepOn k Y (insert i S : Finset _) → Ψ Y = 0) ∧ Φ - Ψ ∈ aug n d ν α := by
  obtain ⟨x, hx, hx1⟩ : ∃ x : kˣ, ν x ≠ 1 ∧ valuation k (x : k) ≤ 1 := by
    obtain ⟨x, hx⟩ := DFunLike.ne_iff.1 h1
    rcases le_total (valuation k (x : k)) 1 with h | h
    · exact ⟨x, hx, h⟩
    · exact ⟨x⁻¹, by simpa using hx, by simpa using inv_le_one_of_one_le₀ h⟩
  obtain ⟨c₀, hc₀, hinv⟩ := exists_inv hi hΦ
  have hK : IsCompact (Function.support Φ) := hΦ.2.isCompact.of_isClosed_subset
    (hΦ.1.isOpen_fiber 0).isClosed_compl (subset_tsupport _)
  obtain ⟨L, hL, hLb⟩ := exists_bound (i := i) hK fun Y hY => by_contra fun h => hY (h0 Y h)
  obtain ⟨c, hc, hLc⟩ := bx_large hL
  have := bx_finite (S := S) c hc₀
  have := bx_finite (S := S) ((x⁻¹ : kˣ) * c) hc
  have := Fintype.ofFinite (bx S c ⧸ (bx S c₀).addSubgroupOf (bx S c))
  have := Fintype.ofFinite (bx S ((x⁻¹ : kˣ) * c) ⧸ (bx S c).addSubgroupOf (bx S ((x⁻¹ : kˣ) * c)))
  obtain ⟨s1, a1⟩ := sum_aug hi ν α (fun q : bx S c ⧸ (bx S c₀).addSubgroupOf (bx S c) => (q.out : S → k)) hΦ
  set Φ₁ := fun Y => ∑ q : bx S c ⧸ (bx S c₀).addSubgroupOf (bx S c), Φ (mv S i 1 (q.out : S → k) Y) with hΦ₁
  obtain ⟨s2, a2⟩ := sum_aug hi ν α
    (fun q : bx S ((x⁻¹ : kˣ) * c) ⧸ (bx S c).addSubgroupOf (bx S ((x⁻¹ : kˣ) * c)) => (q.out : S → k)) s1
  obtain ⟨s3, a3⟩ := mv_aug hi ν α x 0 s1
  set N₁ : ℂ := ((Fintype.card (bx S c ⧸ (bx S c₀).addSubgroupOf (bx S c)) : ℕ) : ℂ) with hN₁
  set N₂ : ℕ := Fintype.card (bx S ((x⁻¹ : kˣ) * c) ⧸ (bx S c).addSubgroupOf (bx S ((x⁻¹ : kˣ) * c))) with hN₂
  set z : ℂ := (ν x : ℂ) * apow x ((d : ℂ) / 2) with hz
  have n1 : N₁ ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have n2 : z * N₂ - 1 ≠ 0 := fun e => hx (by
    have hp : 0 ≤ GlobalTheory.SplitWeil.nabs k x := NNReal.coe_nonneg _
    have e1 : apow x ((d : ℂ) / 2) = ((GlobalTheory.SplitWeil.nabs k x ^ ((d : ℝ) / 2) : ℝ) : ℂ) := by
      rw [Complex.ofReal_cpow hp]; simp [apow]
    set r : ℝ := GlobalTheory.SplitWeil.nabs k x ^ ((d : ℝ) / 2) * N₂ with hr
    have e2 : (ν x : ℂ) * r = 1 := by rw [← sub_eq_zero.1 e, hz, e1, hr]; push_cast; ring
    have e3 : r = 1 := by
      have := congrArg norm e2
      rwa [norm_mul, hν.1, one_mul, norm_one, Complex.norm_real, Real.norm_of_nonneg (by positivity)] at this
    exact Units.ext (by simpa [e3] using e2))
  refine ⟨((z * N₂ - 1) * N₁)⁻¹ • (z • _ - _), Submodule.smul_mem _ _ (sub_mem (Submodule.smul_mem _ z s2) s3), fun Y hY => ?_, ?_⟩
  · rw [Finset.coe_insert] at hY
    replace hY := fun h => hY ((linearIndepOn_insert (K := k) (f := (Y : Fin n → Fin d → k)) (mt Finset.mem_coe.1 hi)).2 h)
    rw [imp_false, not_and_or, not_not] at hY
    suffices h : ∑ q : bx S ((x⁻¹ : kˣ) * c) ⧸ (bx S c).addSubgroupOf (bx S ((x⁻¹ : kˣ) * c)), Φ₁ (mv S i 1 (q.out : S → k) Y) =
        Φ₁ (mv S i x 0 Y) by simp [h]
    rcases hY with hY | hY
    · have z0 : ∀ y a, Φ (mv S i y a Y) = 0 := fun y a => h0 _ fun h => hY (h.congr fun s hs => mv_row hi y a Y ⟨s, hs⟩)
      simp [hΦ₁, mv_mv hi, z0]
    · obtain ⟨b, hb⟩ := (Submodule.mem_span_range_iff_exists_fun k).1
        ((congrArg (Submodule.span k) (Set.image_eq_range (Y : Fin n → Fin d → k) S)).le hY)
      have eY : Y = mv S i 0 b Y := by
        rw [mv, zero_smul, zero_add, show cmb S b Y = Y i from hb, updateRow_eq_self]
      let f : (S → k) → ℂ := fun a => Φ (mv S i 0 a Y)
      let f₁ : (S → k) → ℂ := fun a => Φ₁ (mv S i 0 a Y)
      have e1 : ∀ a, f₁ a = ∑ q : bx S c ⧸ (bx S c₀).addSubgroupOf (bx S c), f (a + (q.out : bx S c)) := fun a => by
        simp [f₁, f, hΦ₁, mv_mv hi]
      have i0 : ∀ a ∈ bx S c₀, ∀ b, f (b + a) = f b := fun a ha b => by
        simpa [mv_mv hi] using hinv a ha (mv S i 0 b Y)
      have o0 : ∀ a ∉ bx S c, f a = 0 := fun a ha => by_contra fun h => ha (hLc (hLb _ h a (by
        rw [show cmb S a (mv S i 0 a Y) = cmb S a Y from Finset.sum_congr rfl fun s _ => by rw [mv_row hi]]
        simp [mv])))
      have i1 : ∀ a ∈ bx S c, ∀ b, f₁ (b + a) = f₁ b := fun a ha b => by rw [e1, e1, avg_inv _ _ i0 ha]
      have o1 : ∀ a ∉ bx S c, f₁ a = 0 := fun a ha => by rw [e1, avg_off _ _ o0 ha]
      have hm : ∀ a : S → k, a ∈ bx S ((x⁻¹ : kˣ) * c) ↔ (x : k) • a ∈ bx S c := fun a => forall_congr' fun s => by
        have : 0 < valuation k (x : k) := zero_lt_iff.2 (by simp)
        simp [le_inv_mul_iff₀ this]
      rw [eY]
      simp only [mv_mv hi, one_smul, mul_zero, add_zero]
      change ∑ q : bx S ((x⁻¹ : kˣ) * c) ⧸ (bx S c).addSubgroupOf (bx S ((x⁻¹ : kˣ) * c)), f₁ (b + (q.out : bx S _)) = f₁ ((x : k) • b)
      by_cases hbm : b ∈ bx S ((x⁻¹ : kˣ) * c)
      · have := avg_inv (bx S c) _ i1 hbm 0
        rw [zero_add] at this
        rw [this, avg_zero _ _ i1 o1, ← i1 _ ((hm b).1 hbm) 0, zero_add]
      · rw [o1 _ fun h => hbm ((hm b).2 h)]
        refine avg_off _ _ (fun a ha => o1 a fun h => ha ((hm a).2 fun s => ?_)) hbm
        simpa using (mul_le_of_le_one_left' hx1).trans (h s)
  · have := Submodule.smul_mem _ (-((z * N₂ - 1) * N₁)⁻¹)
      (add_mem (sub_mem (Submodule.smul_mem _ z a2) a3) (Submodule.smul_mem _ (z * N₂ - 1) a1))
    convert this using 1
    ext Y
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    field_simp
    ring

theorem surjectivity_statement : SurjSt := by
  intro k _ _ _ _ n d ν α hν h1 Φ hΦ
  have key : ∀ S : Finset (Fin n), ∃ Ψ ∈ SB (Matrix (Fin n) (Fin d) k), (∀ Y : Matrix (Fin n) (Fin d) k, ¬ LinearIndepOn k Y S → Ψ Y = 0) ∧
      Φ - Ψ ∈ aug n d ν α := fun S => by
    induction S using Finset.induction_on with
    | empty => exact ⟨Φ, hΦ, fun Y h => absurd (Finset.coe_empty ▸ linearIndepOn_empty k (Y : Fin n → Fin d → k)) h, by simp⟩
    | insert i S hi ih =>
      obtain ⟨Ψ, h2, h3, h4⟩ := ih
      obtain ⟨Ψ', h5, h6, h7⟩ := step (α := α) hi hν h1 h2 h3
      exact ⟨Ψ', h5, h6, by simpa using add_mem h4 h7⟩
  obtain ⟨Ψ, h2, h3, h4⟩ := key Finset.univ
  refine ⟨Ψ, ⟨h2, fun Y hY => h3 Y fun h => hY ?_⟩, h4⟩
  rw [Finset.coe_univ] at h
  simpa using LinearIndependent.rank_matrix (M := Y) (linearIndepOn_univ_iff.1 h)

end PositivityTheory.KCo
