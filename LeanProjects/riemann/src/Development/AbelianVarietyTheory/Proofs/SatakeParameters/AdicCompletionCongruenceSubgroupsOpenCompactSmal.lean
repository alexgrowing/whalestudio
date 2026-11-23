import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.PolyApproxZeroPadic
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
import ReciprocityTheory.GeneralLinearIntegers.AlgebraMapIntMemOint

open NumberField IsDedekindDomain Filter Topology

noncomputable section

namespace GlobalTheory.CongOpenSmall

variable {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (a : ℕ)

abbrev cong (t : w.adicCompletionIntegers E) : Subgroup (GL (Fin a) (w.adicCompletion E)) :=
  (Matrix.GeneralLinearGroup.map (n := Fin a) (Ideal.Quotient.mk (Ideal.span {t}))).ker.map
    (Matrix.GeneralLinearGroup.map (algebraMap (w.adicCompletionIntegers E) (w.adicCompletion E)))

theorem isCompact_integers : IsCompact (w.adicCompletionIntegers E : Set (w.adicCompletion E)) :=
  ReciprocityTheory.GeneralLinearIntegers.GeneralLinearIntegersOpenCompact.isCompact_integers w

variable {w a}

theorem le_one_of_sub_le {x y : w.adicCompletion E} {c : WithZero (Multiplicative ℤ)} (hc : c ≤ 1)
    (hy : Valued.v y ≤ 1) (h : Valued.v (x - y) ≤ c) : Valued.v x ≤ 1 := by
  have := Valuation.map_add_le Valued.v (h.trans hc) hy
  rwa [sub_add_cancel] at this

theorem v_one_apply_le (i j : Fin a) :
    Valued.v ((1 : Matrix (Fin a) (Fin a) (w.adicCompletion E)) i j) ≤ 1 := by
  rw [Matrix.one_apply]; split_ifs <;> simp

theorem coe_one_apply (i j : Fin a) :
    (((1 : Matrix (Fin a) (Fin a) (w.adicCompletionIntegers E)) i j : w.adicCompletionIntegers E) :
      w.adicCompletion E) = (1 : Matrix (Fin a) (Fin a) (w.adicCompletion E)) i j := by
  rw [Matrix.one_apply, Matrix.one_apply]; split_ifs <;> simp

theorem mk_eq_one_apply_iff (t x : w.adicCompletionIntegers E) (i j : Fin a) :
    Ideal.Quotient.mk (Ideal.span {t}) x =
        (1 : Matrix (Fin a) (Fin a) (w.adicCompletionIntegers E ⧸ Ideal.span {t})) i j ↔
      Valued.v ((x : w.adicCompletion E) - (1 : Matrix (Fin a) (Fin a) (w.adicCompletion E)) i j) ≤
        Valued.v (t : w.adicCompletion E) := by
  have e2 : (1 : Matrix (Fin a) (Fin a) (w.adicCompletionIntegers E ⧸ Ideal.span {t})) i j =
      Ideal.Quotient.mk (Ideal.span {t}) ((1 : Matrix (Fin a) (Fin a) (w.adicCompletionIntegers E)) i j) := by
    rw [Matrix.one_apply, Matrix.one_apply]; split_ifs <;> simp
  have hI := Valuation.integer.integers (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ)))
  rw [e2, Ideal.Quotient.eq, Ideal.mem_span_singleton, ← coe_one_apply]
  exact hI.dvd_iff_le

end GlobalTheory.CongOpenSmall

namespace GlobalTheory.CongOpenSmall

variable {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {a : ℕ}

theorem entry_le_of_mem_ker (t : w.adicCompletionIntegers E) (h : GL (Fin a) (w.adicCompletionIntegers E))
    (hh : h ∈ (Matrix.GeneralLinearGroup.map (n := Fin a) (Ideal.Quotient.mk (Ideal.span {t}))).ker)
    (i j : Fin a) :
    Valued.v (((Matrix.GeneralLinearGroup.map (algebraMap (w.adicCompletionIntegers E) (w.adicCompletion E)) h :
      GL (Fin a) (w.adicCompletion E)) : Matrix (Fin a) (Fin a) (w.adicCompletion E)) i j
      - (1 : Matrix (Fin a) (Fin a) (w.adicCompletion E)) i j) ≤ Valued.v (t : w.adicCompletion E) := by
  rw [MonoidHom.mem_ker] at hh
  have e := congrArg (fun g : GL (Fin a) (w.adicCompletionIntegers E ⧸ Ideal.span {t}) =>
    g.1 i j) hh
  change Ideal.Quotient.mk _ (h.1 i j) = (1 : Matrix (Fin a) (Fin a) _) i j at e
  exact (mk_eq_one_apply_iff t _ i j).1 e

theorem bounds_of_mem (t : w.adicCompletionIntegers E) (g : GL (Fin a) (w.adicCompletion E))
    (hg : g ∈ cong w a t) (i j : Fin a) :
    Valued.v ((g : Matrix (Fin a) (Fin a) (w.adicCompletion E)) i j
        - (1 : Matrix (Fin a) (Fin a) (w.adicCompletion E)) i j) ≤ Valued.v (t : w.adicCompletion E) ∧
      Valued.v ((↑g⁻¹ : Matrix (Fin a) (Fin a) (w.adicCompletion E)) i j
        - (1 : Matrix (Fin a) (Fin a) (w.adicCompletion E)) i j) ≤ Valued.v (t : w.adicCompletion E) := by
  obtain ⟨h, hh, rfl⟩ := Subgroup.mem_map.1 hg
  refine ⟨entry_le_of_mem_ker t h hh i j, ?_⟩
  rw [← map_inv]
  exact entry_le_of_mem_ker t h⁻¹ (inv_mem hh) i j

theorem mem_cong_of (t : w.adicCompletionIntegers E) (g : GL (Fin a) (w.adicCompletion E))
    (hb : ∀ i j, Valued.v ((g : Matrix (Fin a) (Fin a) (w.adicCompletion E)) i j
        - (1 : Matrix (Fin a) (Fin a) (w.adicCompletion E)) i j) ≤ Valued.v (t : w.adicCompletion E) ∧
      Valued.v ((↑g⁻¹ : Matrix (Fin a) (Fin a) (w.adicCompletion E)) i j
        - (1 : Matrix (Fin a) (Fin a) (w.adicCompletion E)) i j) ≤ Valued.v (t : w.adicCompletion E)) :
    g ∈ cong w a t := by
  have ht : Valued.v (t : w.adicCompletion E) ≤ 1 := t.2
  have h1 : ∀ i j, (g : Matrix (Fin a) (Fin a) (w.adicCompletion E)) i j ∈ w.adicCompletionIntegers E :=
    fun i j => (HeightOneSpectrum.mem_adicCompletionIntegers (R := 𝓞 E) E w).2
      (le_one_of_sub_le ht (v_one_apply_le i j) (hb i j).1)
  have h2 : ∀ i j, (↑g⁻¹ : Matrix (Fin a) (Fin a) (w.adicCompletion E)) i j ∈ w.adicCompletionIntegers E :=
    fun i j => (HeightOneSpectrum.mem_adicCompletionIntegers (R := 𝓞 E) E w).2
      (le_one_of_sub_le ht (v_one_apply_le i j) (hb i j).2)
  let M : Matrix (Fin a) (Fin a) (w.adicCompletionIntegers E) := Matrix.of fun i j => ⟨_, h1 i j⟩
  let M' : Matrix (Fin a) (Fin a) (w.adicCompletionIntegers E) := Matrix.of fun i j => ⟨_, h2 i j⟩
  have hM : M.map (algebraMap (w.adicCompletionIntegers E) (w.adicCompletion E)) = g := by ext i j; rfl
  have hM' : M'.map (algebraMap (w.adicCompletionIntegers E) (w.adicCompletion E)) = ↑g⁻¹ := by ext i j; rfl
  have inj : Function.Injective fun N : Matrix (Fin a) (Fin a) (w.adicCompletionIntegers E) =>
      N.map (algebraMap (w.adicCompletionIntegers E) (w.adicCompletion E)) :=
    Matrix.map_injective fun x y hxy => Subtype.ext hxy
  have hMM : M * M' = 1 := inj (by
    simp only [Matrix.map_mul, hM, hM', Matrix.map_one _ (map_zero _) (map_one _)]
    exact g.mul_inv)
  have hM'M : M' * M = 1 := inj (by
    simp only [Matrix.map_mul, hM, hM', Matrix.map_one _ (map_zero _) (map_one _)]
    exact g.inv_mul)
  refine Subgroup.mem_map.2 ⟨⟨M, M', hMM, hM'M⟩, ?_, Units.ext hM⟩
  rw [MonoidHom.mem_ker]
  refine Units.ext (Matrix.ext fun i j => ?_)
  change Ideal.Quotient.mk _ (M i j) = (1 : Matrix (Fin a) (Fin a) _) i j
  exact (mk_eq_one_apply_iff t _ i j).2 (hb i j).1

theorem cong_mem_nhds (t : w.adicCompletionIntegers E) (ht : (t : w.adicCompletion E) ≠ 0) :
    (cong w a t : Set (GL (Fin a) (w.adicCompletion E))) ∈ 𝓝 (1 : GL (Fin a) (w.adicCompletion E)) := by
  have hv : Valued.v (t : w.adicCompletion E) ≠ 0 := (Valuation.ne_zero_iff _).2 ht
  have hnb : ∀ x : w.adicCompletion E, {y | Valued.v (y - x) ≤ Valued.v (t : w.adicCompletion E)} ∈ 𝓝 x :=
    fun x => by
    have hc : Continuous fun y : w.adicCompletion E => (t : w.adicCompletion E)⁻¹ * (y - x) :=
      continuous_const.mul (continuous_id.sub continuous_const)
    have hO : (w.adicCompletionIntegers E : Set (w.adicCompletion E)) ∈ 𝓝 (0 : w.adicCompletion E) :=
      (ReciprocityTheory.GeneralLinearIntegers.GeneralLinearIntegersOpenCompact.isOpen_integers w).mem_nhds (zero_mem _)
    have h0 := hc.tendsto x
    rw [sub_self, mul_zero] at h0
    refine mem_of_superset (h0 hO) fun y hy => ?_
    have hy' := (HeightOneSpectrum.mem_adicCompletionIntegers (R := 𝓞 E) E w).1 hy
    rw [map_mul, map_inv₀, inv_mul_le_iff₀ (zero_lt_iff.2 hv), mul_one] at hy'
    exact hy'
  have hc1 : ∀ i j, Tendsto (fun g : GL (Fin a) (w.adicCompletion E) => (g : Matrix (Fin a) (Fin a) _) i j) (𝓝 1)
      (𝓝 ((1 : Matrix (Fin a) (Fin a) (w.adicCompletion E)) i j)) := fun i j => by
    have := (Units.continuous_val.matrix_elem i j).tendsto (1 : GL (Fin a) (w.adicCompletion E))
    simpa using this
  have hc2 : ∀ i j, Tendsto (fun g : GL (Fin a) (w.adicCompletion E) => (↑g⁻¹ : Matrix (Fin a) (Fin a) _) i j)
      (𝓝 1) (𝓝 ((1 : Matrix (Fin a) (Fin a) (w.adicCompletion E)) i j)) := fun i j => by
    have := (Units.continuous_coe_inv.matrix_elem i j).tendsto (1 : GL (Fin a) (w.adicCompletion E))
    simpa using this
  have hev : ∀ᶠ g : GL (Fin a) (w.adicCompletion E) in 𝓝 1, ∀ i j,
      Valued.v ((g : Matrix (Fin a) (Fin a) (w.adicCompletion E)) i j
        - (1 : Matrix (Fin a) (Fin a) (w.adicCompletion E)) i j) ≤ Valued.v (t : w.adicCompletion E) ∧
      Valued.v ((↑g⁻¹ : Matrix (Fin a) (Fin a) (w.adicCompletion E)) i j
        - (1 : Matrix (Fin a) (Fin a) (w.adicCompletion E)) i j) ≤ Valued.v (t : w.adicCompletion E) :=
    eventually_all.2 fun i => eventually_all.2 fun j =>
      ((hc1 i j).eventually (hnb _)).and ((hc2 i j).eventually (hnb _))
  exact mem_of_superset hev fun g hg => mem_cong_of t g hg

theorem isOpen_cong (t : w.adicCompletionIntegers E) (ht : (t : w.adicCompletion E) ≠ 0) :
    IsOpen (cong w a t : Set (GL (Fin a) (w.adicCompletion E))) :=
  Subgroup.isOpen_of_mem_nhds _ (cong_mem_nhds t ht)

theorem isCompact_cong (t : w.adicCompletionIntegers E) (ht : (t : w.adicCompletion E) ≠ 0) :
    IsCompact (cong w a t : Set (GL (Fin a) (w.adicCompletion E))) := by
  have hB : IsCompact (Set.univ.pi fun _ : Fin a => Set.univ.pi fun _ : Fin a =>
      (w.adicCompletionIntegers E : Set (w.adicCompletion E)) : Set (Matrix (Fin a) (Fin a) (w.adicCompletion E))) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_integers w
  have hS : IsCompact (Units.embedProduct (Matrix (Fin a) (Fin a) (w.adicCompletion E)) ⁻¹'
      ((Set.univ.pi fun _ : Fin a => Set.univ.pi fun _ : Fin a =>
        (w.adicCompletionIntegers E : Set (w.adicCompletion E)) : Set (Matrix (Fin a) (Fin a) (w.adicCompletion E))) ×ˢ
        (MulOpposite.op '' (Set.univ.pi fun _ : Fin a => Set.univ.pi fun _ : Fin a =>
        (w.adicCompletionIntegers E : Set (w.adicCompletion E)) : Set (Matrix (Fin a) (Fin a) (w.adicCompletion E)))))
        : Set (GL (Fin a) (w.adicCompletion E))) :=
    Units.isClosedEmbedding_embedProduct.isCompact_preimage (hB.prod (hB.image MulOpposite.continuous_op))
  refine hS.of_isClosed_subset (Subgroup.isClosed_of_isOpen (cong w a t) (isOpen_cong t ht)) ?_
  intro g hg
  have ht1 : Valued.v (t : w.adicCompletion E) ≤ 1 := t.2
  refine ⟨Set.mem_univ_pi.2 fun i => Set.mem_univ_pi.2 fun j => ?_,
    ⟨_, Set.mem_univ_pi.2 fun i => Set.mem_univ_pi.2 fun j => ?_, rfl⟩⟩
  · exact (HeightOneSpectrum.mem_adicCompletionIntegers (R := 𝓞 E) E w).2
      (le_one_of_sub_le ht1 (v_one_apply_le i j) (bounds_of_mem t g hg i j).1)
  · exact (HeightOneSpectrum.mem_adicCompletionIntegers (R := 𝓞 E) E w).2
      (le_one_of_sub_le ht1 (v_one_apply_le i j) (bounds_of_mem t g hg i j).2)

end GlobalTheory.CongOpenSmall

namespace GlobalTheory.CongOpenSmall

variable {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {a : ℕ}

theorem exists_small_ball {x : w.adicCompletion E} {s : Set (w.adicCompletion E)} (hs : s ∈ 𝓝 x)
    {k : w.adicCompletion E} (hk : Valued.v k < 1) :
    ∃ m : ℕ, ∀ y, Valued.v (y - x) ≤ Valued.v k ^ m → y ∈ s := by
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds.1 hs
  have hs0 : {y : w.adicCompletion E | Valued.v y < MonoidWithZeroHom.ValueGroup₀.embedding γ.1} ∈
      𝓝 (0 : w.adicCompletion E) :=
    Valued.mem_nhds.2 ⟨γ, fun y hy => by
      simpa using ((Valuation.restrict_lt_iff_lt_embedding _).1 hy)⟩
  obtain ⟨m, hm⟩ := ((Valued.tendsto_zero_pow_of_v_lt_one hk).eventually hs0).exists
  refine ⟨m, fun y hy => hγ ?_⟩
  refine (Valuation.restrict_lt_iff_lt_embedding _).2 (hy.trans_lt ?_)
  simpa [map_pow] using hm

theorem eventually_cong_subset (l : w.adicCompletionIntegers E) (hl : Valued.v (l : w.adicCompletion E) < 1)
    (N : Set (GL (Fin a) (w.adicCompletion E))) (hN : N ∈ 𝓝 (1 : GL (Fin a) (w.adicCompletion E))) :
    ∀ᶠ m : ℕ in atTop, (cong w a (l ^ m) : Set (GL (Fin a) (w.adicCompletion E))) ⊆ N := by
  have hpow : ∀ m : ℕ, Valued.v (((l ^ m : w.adicCompletionIntegers E)) : w.adicCompletion E) =
      Valued.v (l : w.adicCompletion E) ^ m := fun m => by
    rw [← map_pow]; rfl
  have hanti : ∀ m m' : ℕ, m ≤ m' → (cong w a (l ^ m') : Set (GL (Fin a) (w.adicCompletion E))) ⊆
      cong w a (l ^ m) := by
    intro m m' hmm g hg
    have hle : Valued.v (((l ^ m' : w.adicCompletionIntegers E)) : w.adicCompletion E) ≤
        Valued.v (((l ^ m : w.adicCompletionIntegers E)) : w.adicCompletion E) := by
      rw [hpow, hpow]; exact pow_le_pow_right_of_le_one' hl.le hmm
    exact mem_cong_of _ g fun i j =>
      ⟨(bounds_of_mem _ g hg i j).1.trans hle, (bounds_of_mem _ g hg i j).2.trans hle⟩
  let G : Filter (GL (Fin a) (w.adicCompletion E)) :=
    ⨅ m : ℕ, 𝓟 (cong w a (l ^ m) : Set (GL (Fin a) (w.adicCompletion E)))
  have hent : ∀ i j, Tendsto (fun g : GL (Fin a) (w.adicCompletion E) => (g : Matrix (Fin a) (Fin a) _) i j) G
        (𝓝 ((1 : Matrix (Fin a) (Fin a) (w.adicCompletion E)) i j)) ∧
      Tendsto (fun g : GL (Fin a) (w.adicCompletion E) => (↑g⁻¹ : Matrix (Fin a) (Fin a) _) i j) G
        (𝓝 ((1 : Matrix (Fin a) (Fin a) (w.adicCompletion E)) i j)) := by
    intro i j
    have key : ∀ s ∈ 𝓝 ((1 : Matrix (Fin a) (Fin a) (w.adicCompletion E)) i j), ∃ m : ℕ,
        ∀ g ∈ (cong w a (l ^ m) : Set (GL (Fin a) (w.adicCompletion E))),
          (g : Matrix (Fin a) (Fin a) _) i j ∈ s ∧ (↑g⁻¹ : Matrix (Fin a) (Fin a) _) i j ∈ s := by
      intro s hs
      obtain ⟨m, hm⟩ := exists_small_ball hs hl
      refine ⟨m, fun g hg => ?_⟩
      have hb := bounds_of_mem _ g hg i j
      rw [hpow] at hb
      exact ⟨hm _ hb.1, hm _ hb.2⟩
    constructor
    · intro s hs
      obtain ⟨m, hm⟩ := key s hs
      exact mem_iInf_of_mem m (mem_principal.2 fun g hg => (hm g hg).1)
    · intro s hs
      obtain ⟨m, hm⟩ := key s hs
      exact mem_iInf_of_mem m (mem_principal.2 fun g hg => (hm g hg).2)
  have hG : Tendsto id G (𝓝 (1 : GL (Fin a) (w.adicCompletion E))) := by
    rw [Units.isEmbedding_embedProduct.tendsto_nhds_iff]
    refine Tendsto.prodMk_nhds ?_ ?_
    · exact tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => (hent i j).1
    · exact (MulOpposite.continuous_op.tendsto _).comp
        (tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => (hent i j).2)
  have hdir : Directed (· ≥ ·) fun m : ℕ => 𝓟 (cong w a (l ^ m) : Set (GL (Fin a) (w.adicCompletion E))) :=
    fun m m' => ⟨max m m', principal_mono.2 (hanti _ _ (le_max_left _ _)),
      principal_mono.2 (hanti _ _ (le_max_right _ _))⟩
  obtain ⟨m₀, hm₀⟩ := (mem_iInf_of_directed hdir _).1 (hG hN)
  filter_upwards [eventually_ge_atTop m₀] with m hm
  exact (hanti _ _ hm).trans (mem_principal.1 hm₀)

end GlobalTheory.CongOpenSmall

namespace GlobalTheory.CongOpenSmall

theorem congruence_open_compact_small : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (a l : ℕ), l.Prime → (l : 𝓞 E) ∈ w.asIdeal → (∀ m : ℕ, IsOpen (((Matrix.GeneralLinearGroup.map (n := Fin a) (Ideal.Quotient.mk (Ideal.span {(l : w.adicCompletionIntegers E) ^ m}))).ker.map (Matrix.GeneralLinearGroup.map (algebraMap (w.adicCompletionIntegers E) (w.adicCompletion E))) : Subgroup (GL (Fin a) (w.adicCompletion E))) : Set (GL (Fin a) (w.adicCompletion E))) ∧ IsCompact (((Matrix.GeneralLinearGroup.map (n := Fin a) (Ideal.Quotient.mk (Ideal.span {(l : w.adicCompletionIntegers E) ^ m}))).ker.map (Matrix.GeneralLinearGroup.map (algebraMap (w.adicCompletionIntegers E) (w.adicCompletion E))) : Subgroup (GL (Fin a) (w.adicCompletion E))) : Set (GL (Fin a) (w.adicCompletion E)))) ∧ ∀ N ∈ nhds (1 : GL (Fin a) (w.adicCompletion E)), ∀ᶠ m : ℕ in Filter.atTop, (((Matrix.GeneralLinearGroup.map (n := Fin a) (Ideal.Quotient.mk (Ideal.span {(l : w.adicCompletionIntegers E) ^ m}))).ker.map (Matrix.GeneralLinearGroup.map (algebraMap (w.adicCompletionIntegers E) (w.adicCompletion E))) : Subgroup (GL (Fin a) (w.adicCompletion E))) : Set (GL (Fin a) (w.adicCompletion E))) ⊆ N := by
  intro E _ _ w a l hl hw
  have hchar : CharZero (w.adicCompletion E) :=
    charZero_of_injective_algebraMap (algebraMap E (w.adicCompletion E)).injective
  have hcoe : ((l : w.adicCompletionIntegers E) : w.adicCompletion E) = (l : w.adicCompletion E) := rfl
  have hl0 : ((l : w.adicCompletionIntegers E) : w.adicCompletion E) ≠ 0 := by
    rw [hcoe]; exact Nat.cast_ne_zero.2 hl.ne_zero
  have hv : Valued.v ((l : w.adicCompletionIntegers E) : w.adicCompletion E) < 1 := by
    have h : Valued.v (((algebraMap (𝓞 E) E (l : 𝓞 E) : E)) : w.adicCompletion E) =
        w.valuation E (algebraMap (𝓞 E) E (l : 𝓞 E)) :=
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w _
    have h2 : w.valuation E (algebraMap (𝓞 E) E (l : 𝓞 E)) < 1 :=
      (HeightOneSpectrum.valuation_lt_one_iff_mem w _).mpr hw
    rw [← h] at h2
    have e : (((algebraMap (𝓞 E) E (l : 𝓞 E) : E)) : w.adicCompletion E) = ((l : ℕ) : w.adicCompletion E) := by
      rw [map_natCast]
      exact map_natCast (algebraMap E (w.adicCompletion E)) l
    rwa [e, ← hcoe] at h2
  have hm0 : ∀ m : ℕ, (((l : w.adicCompletionIntegers E) ^ m : w.adicCompletionIntegers E) : w.adicCompletion E) ≠ 0 :=
    fun m => by
      have : (((l : w.adicCompletionIntegers E) ^ m : w.adicCompletionIntegers E) : w.adicCompletion E) =
        ((l : w.adicCompletionIntegers E) : w.adicCompletion E) ^ m := rfl
      rw [this]; exact pow_ne_zero _ hl0
  exact ⟨fun m => ⟨isOpen_cong _ (hm0 m), isCompact_cong _ (hm0 m)⟩,
    fun N hN => eventually_cong_subset _ hv N hN⟩

end GlobalTheory.CongOpenSmall
