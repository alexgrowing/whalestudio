import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.AlgOfCyc
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AfDesc
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LitAut
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutomorphicFormHyp
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TAlgCyc
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TAlgRes

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeckeGal GlobalTheory.GalOfCusp Filter Topology
section Lem
variable {E : Type} [Field E] [NumberField E] {l : ℕ} [Fact l.Prime]
private theorem norm_pow_sub_le {K : Type} [NormedField K] [IsUltrametricDist K] {y : K} (hy : ‖y - 1‖ ≤ 1) (m : ℕ) :
    ‖y ^ m - 1‖ ≤ ‖y - 1‖ := by
  have h1 : ‖y‖ ≤ 1 := by
    have := IsUltrametricDist.norm_add_le_max (y - 1) 1
    rw [sub_add_cancel, norm_one] at this
    exact this.trans (max_le hy le_rfl)
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show y ^ (m + 1) - 1 = y * (y ^ m - 1) + (y - 1) by ring]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ le_rfl)
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) h1).trans ih
private theorem norm_geom_sub_le {K : Type} [NormedField K] [IsUltrametricDist K] {y : K} (hy : ‖y - 1‖ ≤ 1) (m : ℕ) :
    ‖(∑ i ∈ Finset.range m, y ^ i) - m‖ ≤ ‖y - 1‖ := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, Nat.cast_succ, add_sub_add_comm]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ih (norm_pow_sub_le hy m))
private theorem norm_pow_sub_eq {K : Type} [NormedField K] [IsUltrametricDist K] {y : K} (hy : ‖y - 1‖ ≤ 1) {m : ℕ}
    (hm : ‖y - 1‖ < ‖(m : K)‖) : ‖y ^ m - 1‖ = ‖(m : K)‖ * ‖y - 1‖ := by
  rw [← geom_sum_mul, norm_mul]
  congr 1
  have h := (norm_geom_sub_le hy m).trans_lt hm
  have := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h.ne
  rwa [sub_add_cancel, max_eq_right h.le] at this
private theorem norm_nat (m : ℕ) : ‖((m : ℕ) : Qbar l)‖ = ‖((m : ℕ) : ℚ_[l])‖ := by
  rw [← map_natCast (algebraMap ℚ_[l] (PadicAlgCl l)), PadicAlgCl.norm_extends]
private theorem norm_l_le : ‖((l : ℕ) : Qbar l)‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one _ l
private theorem norm_coprime {m : ℕ} (hm : m.Coprime l) : ‖((m : ℕ) : Qbar l)‖ = 1 := by
  rw [norm_nat]
  exact Padic.norm_natCast_eq_one_iff.mpr hm.symm
private theorem eq_one_of_near {k : ℕ} (hk : 0 < k) : ∀ y : Qbar l, ‖y - 1‖ < ‖((l : ℕ) : Qbar l)‖ → y ^ k = 1 → y = 1 := by
  induction k using Nat.recOnMul with
  | zero => exact absurd hk (lt_irrefl 0)
  | one => intro y _ h; simpa using h
  | prime p hp =>
    intro y hy h
    have hl : ‖((l : ℕ) : Qbar l)‖ ≤ ‖((p : ℕ) : Qbar l)‖ := by
      by_cases e : p = l
      · rw [e]
      · rw [norm_coprime ((Nat.coprime_primes hp Fact.out).2 e)]
        exact norm_l_le
    have := norm_pow_sub_eq (hy.le.trans norm_l_le) (hy.trans_le hl)
    rw [h, sub_self, norm_zero, eq_comm, mul_eq_zero] at this
    exact sub_eq_zero.1 (norm_eq_zero.1 (this.resolve_left ((norm_nonneg _).trans_lt (hy.trans_le hl)).ne'))
  | mul a b iha ihb =>
    intro y hy h
    rw [pow_mul] at h
    exact iha (Nat.pos_of_mul_pos_right hk) y hy
      (ihb (Nat.pos_of_mul_pos_left hk) _ ((norm_pow_sub_le (hy.le.trans norm_l_le) a).trans_lt hy) h)
private theorem tendsto_pow_pow {K : Type} [NormedField K] [IsUltrametricDist K] {z : K} (hz : ‖z - 1‖ < 1) {p : ℕ}
    (hp : ‖(p : K)‖ < 1) : Tendsto (fun n : ℕ => z ^ p ^ n) atTop (𝓝 1) := by
  let c := max ‖z - 1‖ ‖(p : K)‖
  have hc0 : 0 ≤ c := (norm_nonneg _).trans (le_max_left _ _)
  have key : ∀ n : ℕ, ‖z ^ p ^ n - 1‖ ≤ c ^ n := fun n => by
    induction n with
    | zero => simpa using hz.le
    | succ n ih =>
      have h1 := norm_pow_sub_le hz.le (p ^ n)
      have h2 := norm_geom_sub_le (h1.trans hz.le) p
      have h3 := IsUltrametricDist.norm_add_le_max ((∑ i ∈ Finset.range p, (z ^ p ^ n) ^ i) - p) (p : K)
      rw [sub_add_cancel] at h3
      rw [pow_succ, pow_mul, ← geom_sum_mul, norm_mul, pow_succ']
      exact mul_le_mul (h3.trans (max_le_max (h2.trans h1) le_rfl)) ih (norm_nonneg _) hc0
  rw [tendsto_iff_norm_sub_tendsto_zero]
  exact squeeze_zero (fun _ => norm_nonneg _) key (tendsto_pow_atTop_nhds_zero_of_lt_one hc0 (max_lt hz hp))
private theorem unit_pow {v : HeightOneSpectrum (𝓞 E)} {p : ℕ} (hp : ((p : ℕ) : 𝓞 E) ∈ v.asIdeal)
    {x : (v.adicCompletion E)ˣ} (hx : IsUnitAt v x) :
    ∃ M : ℕ, 0 < M ∧ Tendsto (fun n : ℕ => (x ^ M) ^ p ^ n) atTop (𝓝 1) := by
  have hlt : Valued.v ((p : ℕ) : v.adicCompletion E) < 1 := by
    have h : Valued.v (((algebraMap (𝓞 E) E (p : 𝓞 E) : E)) : v.adicCompletion E) =
        v.valuation E (algebraMap (𝓞 E) E (p : 𝓞 E)) :=
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v _
    have h2 : v.valuation E (algebraMap (𝓞 E) E (p : 𝓞 E)) < 1 :=
      (HeightOneSpectrum.valuation_lt_one_iff_mem v _).mpr hp
    rw [← h] at h2
    have e : (((algebraMap (𝓞 E) E (p : 𝓞 E) : E)) : v.adicCompletion E) = ((p : ℕ) : v.adicCompletion E) := by
      rw [map_natCast]
      exact map_natCast (algebraMap E (v.adicCompletion E)) p
    rwa [e] at h2
  have hM : ∃ M : ℕ, 0 < M ∧ Valued.v ((x : v.adicCompletion E) ^ M - 1) < 1 := by
    let O := v.adicCompletionIntegers E
    let y : O := ⟨x, hx.le⟩
    haveI : Finite (IsLocalRing.ResidueField O) := inferInstance
    obtain ⟨a, b, hab, e⟩ := Finite.exists_ne_map_eq_of_infinite fun n : ℕ => IsLocalRing.residue O (y ^ n)
    wlog hlt : a < b generalizing a b
    · exact this b a hab.symm e.symm (lt_of_le_of_ne (not_lt.1 hlt) hab.symm)
    refine ⟨b - a, Nat.sub_pos_of_lt hlt, ?_⟩
    have h1 : y ^ b - y ^ a ∈ IsLocalRing.maximalIdeal O := Ideal.Quotient.eq.1 e.symm
    have h2 : Valued.v ((x : v.adicCompletion E) ^ b - (x : v.adicCompletion E) ^ a) < 1 :=
      (Valuation.mem_maximalIdeal_iff _ _).1 h1
    have hx' : Valued.v (x : v.adicCompletion E) = 1 := hx
    rwa [show (x : v.adicCompletion E) ^ b - (x : v.adicCompletion E) ^ a =
      (x : v.adicCompletion E) ^ a * ((x : v.adicCompletion E) ^ (b - a) - 1) by
        rw [mul_sub, ← pow_add, Nat.add_sub_cancel' hlt.le, mul_one], map_mul, map_pow, hx', one_pow, one_mul] at h2
  obtain ⟨M, hM0, hM⟩ := hM
  refine ⟨M, hM0, ?_⟩
  rw [Units.isEmbedding_val₀.tendsto_nhds_iff]
  exact tendsto_pow_pow (K := v.adicCompletion E) (Valued.toNormedField.norm_lt_one_iff.2 hM)
    (Valued.toNormedField.norm_lt_one_iff.2 hlt)
private theorem loc_away {v : HeightOneSpectrum (𝓞 E)} (hv : ((l : ℕ) : 𝓞 E) ∉ v.asIdeal)
    (φ : (v.adicCompletion E)ˣ →* (Qbar l)ˣ) (hφ : Continuous φ) {x : (v.adicCompletion E)ˣ} (hx : IsUnitAt v x)
    (h : ‖((φ x : (Qbar l)ˣ) : Qbar l) - 1‖ < ‖((l : ℕ) : Qbar l)‖) : φ x = 1 := by
  have hl : l.Prime := Fact.out
  have hN : Ideal.absNorm v.asIdeal ≠ 0 := fun h => v.ne_bot (Ideal.absNorm_eq_zero_iff.mp h)
  obtain ⟨a, p, hp, hNM⟩ := Nat.exists_eq_pow_mul_and_not_dvd hN l hl.ne_one
  have hmem : ((p : ℕ) : 𝓞 E) ∈ v.asIdeal := by
    have h := Ideal.absNorm_mem v.asIdeal
    rw [hNM, Nat.cast_mul, Nat.cast_pow] at h
    exact (v.isPrime.mem_or_mem h).resolve_left fun h' => hv (v.isPrime.mem_of_pow_mem a h')
  obtain ⟨M, hM, ht⟩ := unit_pow hmem hx
  have h1 := (norm_pow_sub_le (h.le.trans norm_l_le) M).trans_lt h
  have h2 : ∀ n : ℕ, ‖((φ ((x ^ M) ^ p ^ n) : (Qbar l)ˣ) : Qbar l) - 1‖ = ‖((φ x : (Qbar l)ˣ) : Qbar l) ^ M - 1‖ := fun n => by
    have hc := norm_coprime (l := l) (Nat.Coprime.pow_left n ((Nat.Prime.coprime_iff_not_dvd hl).mpr hp).symm)
    rw [map_pow, map_pow, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val,
      norm_pow_sub_eq (h1.le.trans norm_l_le) (by rw [hc]; exact h1.trans_le norm_l_le), hc, one_mul]
  have h3 := ((((Units.continuous_val.comp hφ).tendsto 1).comp ht).sub_const 1).norm
  simp only [Function.comp_def, h2, map_one, Units.val_one, sub_self, norm_zero] at h3
  exact Units.ext (eq_one_of_near hM _ h (sub_eq_zero.1 (norm_eq_zero.1 (tendsto_nhds_unique tendsto_const_nhds h3))))
private theorem nhd_loc (V : Set (Ideles E)) (hV : V ∈ 𝓝 (1 : Ideles E)) : ∃ H ∈ 𝓝 (1 : Ideles E), ∀ u ∈ H,
    ∀ (v : HeightOneSpectrum (𝓞 E)) (x : (v.adicCompletion E)ˣ), (x : v.adicCompletion E) = (u : AdeleRing (𝓞 E) E).2 v →
      IsUnitAt v x ∧ localIdele E v x ∈ V := by
  classical
  rw [Units.isInducing_embedProduct.nhds_eq_comap, Filter.mem_comap] at hV
  obtain ⟨T, hT, hTV⟩ := hV
  obtain ⟨T1, hT1, T2, hT2, hTT⟩ := mem_nhds_prod_iff.1 hT
  let f : FiniteAdeleRing (𝓞 E) E → AdeleRing (𝓞 E) E := fun b => (1, 1 + b)
  have hf : Continuous f := continuous_const.prodMk (continuous_const.add continuous_id)
  have hf0 : f 0 = 1 := Prod.ext rfl (add_zero _)
  have h1 : f ⁻¹' T1 ∈ 𝓝 0 := hf.continuousAt.preimage_mem_nhds (by rw [hf0]; exact hT1)
  have h2 : (fun b => MulOpposite.op (f b)) ⁻¹' T2 ∈ 𝓝 0 :=
    (MulOpposite.continuous_op.comp hf).continuousAt.preimage_mem_nhds (by rw [Function.comp_apply, hf0]; exact hT2)
  obtain ⟨N, hN, hNW⟩ := GlobalTheory.AdLat.OpenLat.exists_nsmul_adele E _ (Filter.inter_mem h1 h2)
  let P : Set (FiniteAdeleRing (𝓞 E) E) :=
    {c | ∃ a : FiniteAdeleRing (𝓞 E) E, (∀ v, a v ∈ v.adicCompletionIntegers E) ∧ c = N • a}
  have hP : P ∈ 𝓝 0 := GlobalTheory.AdLat.OpenLat.nsmul_integral_mem_nhds E N hN
  have key : ∀ (u : Ideles E), (u : AdeleRing (𝓞 E) E).2 - 1 ∈ P → ∀ (v : HeightOneSpectrum (𝓞 E)) (x : (v.adicCompletion E)ˣ),
      (x : v.adicCompletion E) = (u : AdeleRing (𝓞 E) E).2 v → Valued.v (x : v.adicCompletion E) ≤ 1 ∧
        ∃ b : FiniteAdeleRing (𝓞 E) E, (∀ v, b v ∈ v.adicCompletionIntegers E) ∧
          ((localIdele E v x : Ideles E) : AdeleRing (𝓞 E) E) = f (N • b) := by
    rintro u ⟨a, ha, e⟩ v x hx
    have e1 : (x : v.adicCompletion E) = 1 + N • a v := by
      rw [hx, eq_add_of_sub_eq' e]
      rfl
    refine ⟨?_, Neutral.B1.finiteSingle E v (1 + a v) - 1, fun w => ?_, Prod.ext rfl ?_⟩
    · rw [e1]
      exact (add_mem (one_mem _) (nsmul_mem (ha v) N) : _ ∈ v.adicCompletionIntegers E)
    · show Function.update (fun w : HeightOneSpectrum (𝓞 E) => (1 : w.adicCompletion E)) v (1 + a v) w - 1 ∈ _
      by_cases hw : w = v
      · subst hw
        rw [Function.update_self, add_sub_cancel_left]
        exact ha w
      · rw [Function.update_of_ne hw, sub_self]
        exact zero_mem _
    · refine Subtype.ext (funext fun w => ?_)
      show Function.update (fun w : HeightOneSpectrum (𝓞 E) => (1 : w.adicCompletion E)) v (x : v.adicCompletion E) w =
        1 + N • (Function.update (fun w : HeightOneSpectrum (𝓞 E) => (1 : w.adicCompletion E)) v (1 + a v) w - 1)
      by_cases hw : w = v
      · subst hw
        rw [Function.update_self, Function.update_self, add_sub_cancel_left, e1]
      · rw [Function.update_of_ne hw, Function.update_of_ne hw, sub_self, smul_zero, add_zero]
  refine ⟨{u | (u : AdeleRing (𝓞 E) E).2 - 1 ∈ P ∧ ((u⁻¹ : Ideles E) : AdeleRing (𝓞 E) E).2 - 1 ∈ P}, Filter.inter_mem ?_ ?_,
    fun u hu v x hx => ?_⟩
  · have hc : Continuous fun u : Ideles E => (u : AdeleRing (𝓞 E) E).2 - 1 :=
      (continuous_snd.comp (Units.continuous_val (M := AdeleRing (𝓞 E) E))).sub continuous_const
    exact hc.continuousAt.preimage_mem_nhds (t := P) (by convert hP; exact sub_self _)
  · have hc : Continuous fun u : Ideles E => ((u⁻¹ : Ideles E) : AdeleRing (𝓞 E) E).2 - 1 :=
      (continuous_snd.comp (Units.continuous_coe_inv (M := AdeleRing (𝓞 E) E))).sub continuous_const
    exact hc.continuousAt.preimage_mem_nhds (t := P) (by convert hP; exact sub_self _)
  · obtain ⟨k1, b, hb, e⟩ := key u hu.1 v x hx
    obtain ⟨k2, b', hb', e'⟩ := key u⁻¹ hu.2 v x⁻¹ (by
      rw [Units.val_inv_eq_inv_val, hx]
      exact (eq_inv_of_mul_eq_one_right (congrArg (fun y : AdeleRing (𝓞 E) E => y.2 v) u.mul_inv)).symm)
    refine ⟨le_antisymm k1 ?_, hTV (hTT ⟨?_, ?_⟩)⟩
    · rw [Units.val_inv_eq_inv_val, map_inv₀] at k2
      exact (inv_le_one₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 x.ne_zero))).1 k2
    · change ((localIdele E v x : Ideles E) : AdeleRing (𝓞 E) E) ∈ T1
      rw [e]; exact (hNW b hb).1
    · change MulOpposite.op (((localIdele E v x)⁻¹ : Ideles E) : AdeleRing (𝓞 E) E) ∈ T2
      rw [← map_inv, e']; exact (hNW b' hb').2
private theorem open_ker (θ : Ideles E →* (Qbar l)ˣ) (hθ : Continuous θ) (h : ∀ x ∈ infConn E, θ x = 1)
    (hl : ∀ v : HeightOneSpectrum (𝓞 E), ((l : ℕ) : 𝓞 E) ∈ v.asIdeal → ∀ x : (v.adicCompletion E)ˣ, IsUnitAt v x →
      ∃ k : ℕ, 0 < k ∧ θ (localIdele E v x) ^ k = 1) : IsOpen (θ.ker : Set (Ideles E)) := by
  have hV : {u | ‖((θ u : (Qbar l)ˣ) : Qbar l) - 1‖ < ‖((l : ℕ) : Qbar l)‖} ∈ 𝓝 (1 : Ideles E) := by
    refine (isOpen_lt (((Units.continuous_val.comp hθ).sub continuous_const).norm) continuous_const).mem_nhds ?_
    simpa using (Fact.out : l.Prime).ne_zero
  obtain ⟨H, hH, hHV⟩ := nhd_loc _ hV
  let p : Ideles E →* (InfiniteAdeleRing E)ˣ :=
    Units.map (MonoidHom.fst (InfiniteAdeleRing E) (FiniteAdeleRing (𝓞 E) E))
  let q : Ideles E →* (FiniteAdeleRing (𝓞 E) E)ˣ :=
    Units.map (MonoidHom.snd (InfiniteAdeleRing E) (FiniteAdeleRing (𝓞 E) E))
  have hp : Continuous p := Continuous.units_map _ continuous_fst
  have ho := (isOpen_connectedComponentOfOne_inf E).preimage hp
  refine θ.ker.isOpen_of_mem_nhds (g := 1) (Filter.mem_of_superset (Filter.inter_mem (ho.mem_nhds ?_) hH) ?_)
  · rw [Set.mem_preimage, map_one]
    exact Subgroup.one_mem _
  · rintro x ⟨h1, h2⟩
    have e : x = inlInf E (p x) * inrFin E (q x) :=
      Units.ext (Prod.ext (mul_one _).symm (one_mul _).symm)
    have h3 : θ (inrFin E (q x)) = 1 := by
      refine GlobalTheory.FrobDense.eq_one_of_local θ hθ _ rfl fun v => ?_
      obtain ⟨hu, hn⟩ := hHV x h2 v (Units.map (GlobalTheory.Mem.LocTriv.ev v) (inrFin E (q x))) rfl
      by_cases hv : ((l : ℕ) : 𝓞 E) ∈ v.asIdeal
      · obtain ⟨k, hk, e⟩ := hl v hv _ hu
        exact Units.ext (eq_one_of_near hk _ hn (congrArg Units.val e))
      · exact loc_away hv (θ.comp (localIdele E v)) (hθ.comp ((continuous_const.prodMk
          (GlobalTheory.Mem.UnrAe.continuous_finSingle v)).units_map _)) hu hn
    show θ x = 1
    rw [e, map_mul, h3, mul_one]
    exact h _ ⟨_, h1, rfl⟩
private theorem pos_conn (k : Eˣ) (hk : ∀ φ : E →+* ℝ, 0 < φ (k : E)) : infDiag k ∈ infConn E := by
  rw [infDiag, MonoidHom.finsetProd_apply]
  refine prod_mem fun w _ => ?_
  let s : (w.Completion)ˣ →* (InfiniteAdeleRing E)ˣ := by
    classical
    exact Units.map (MonoidHom.mulSingle (fun w : InfinitePlace E => w.Completion) w)
  have hs : Continuous s := by
    classical
    exact Continuous.units_map _ (continuous_mulSingle w)
  suffices H : atInf w k ∈ connectedComponent (1 : (w.Completion)ˣ) by
    have := hs.image_connectedComponent_subset 1 ⟨_, H, rfl⟩
    rw [map_one] at this
    exact ⟨_, this, rfl⟩
  have key : ∀ S : Set w.Completion, IsPreconnected S → 0 ∉ S → 1 ∈ S → algebraMap E w.Completion (k : E) ∈ S →
      atInf w k ∈ connectedComponent (1 : (w.Completion)ˣ) := fun S hS h0 h1 h2 => by
    refine IsPreconnected.subset_connectedComponent (s := Units.val ⁻¹' S) ?_ h1 h2
    rw [← Units.isEmbedding_val₀.isInducing.isPreconnected_image, Set.image_preimage_eq_of_subset]
    · exact hS
    · exact fun y hy => ⟨Units.mk0 y fun e => h0 (e ▸ hy), rfl⟩
  rcases w.isReal_or_isComplex with hw | hw
  · let e := InfinitePlace.Completion.ringEquivRealOfIsReal hw
    have he : e (algebraMap E w.Completion (k : E)) = InfinitePlace.embedding_of_isReal hw (k : E) :=
      InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe hw ((WithAbs.equiv w.1).symm (k : E))
    refine key (e ⁻¹' Set.Ioi 0) ((InfinitePlace.Completion.isometryEquivRealOfIsReal hw).toHomeomorph.isPreconnected_preimage.2
      isPreconnected_Ioi) (by simp) (by simp) ?_
    rw [Set.mem_preimage, he]
    exact hk _
  · let e := InfinitePlace.Completion.ringEquivComplexOfIsComplex hw
    refine key (e ⁻¹' {0}ᶜ) ((InfinitePlace.Completion.isometryEquivComplexOfIsComplex hw).toHomeomorph.isPreconnected_preimage.2
      (isConnected_compl_singleton_of_one_lt_rank (by simp) 0).isPreconnected) (by simp) (by simp) ?_
    exact (map_ne_zero e).2 ((map_ne_zero _).2 k.ne_zero)
end Lem
section
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] {l : ℕ} [Fact l.Prime]
private theorem cyc_loc [IsAlgClosure E Ω] {art : Ideles E →* Gab E Ω} (ha : IsGlobalArtin art) (ι : Qbar l ≃+* ℂ)
    {v : HeightOneSpectrum (𝓞 E)} {x : (v.adicCompletion E)ˣ} (hx : IsUnitAt v x) {σ : G E Ω}
    (e : art (localIdele E v x) = toAb E Ω σ) :
    ((cycBar E Ω l σ : (Qbar l)ˣ) : Qbar l) = locPow ι (fun _ => 1) v x := by
  have h := GlobalTheory.Published.CharAboveModel.absPow_isAlgPos E 1
  obtain ⟨μ, hμ, hL⟩ := ha.exists_isLAdicOf ι h
  have e' : μ = cycBar E Ω l ^ 1 := GlobalTheory.Published.CharAboveModel.eq_cyc_pow ha hμ hL
  rw [pow_one] at e'
  rw [← e', hL.loc x σ e, (GlobalTheory.HeckeGal.Model.absPow_isAbsPow E _).1 v x hx]
  simp
private theorem exists_type (ι : Qbar l ≃+* ℂ) (a : HeightOneSpectrum (𝓞 E) → ℤ) :
    ∃ n : (E →+* ℂ) → ℤ, ∀ v y, locPow ι n v y = locPow ι (fun _ => 1) v y ^ a v := by
  classical
  let P : (E →+* ℂ) → HeightOneSpectrum (𝓞 E) → Prop := fun φ v =>
    ∃ j : v.adicCompletion E →+* Qbar l, Continuous j ∧ φ = (ι.toRingHom.comp j).comp (algebraMap E (v.adicCompletion E))
  refine ⟨fun φ => if h : ∃ v, P φ v then a h.choose else 0, fun v y => ?_⟩
  haveI : Fintype {j : v.adicCompletion E →+* Qbar l // Continuous j} := @Fintype.ofFinite _ (finite_contEmb v)
  unfold locPow
  rw [finprod_eq_prod_of_fintype, finprod_eq_prod_of_fintype, ← Finset.prod_zpow]
  refine Finset.prod_congr rfl fun j _ => ?_
  have h : ∃ v', P ((ι.toRingHom.comp j.1).comp (algebraMap E (v.adicCompletion E))) v' := ⟨v, j.1, j.2, rfl⟩
  obtain ⟨j', hj', e⟩ := h.choose_spec
  have h1 : v = h.choose := place_eq_of_contEmb_comp_eq E l v _ j.1 j' j.2 hj'
    (RingHom.ext fun b => ι.injective (DFunLike.congr_fun e b))
  simp only [dif_pos h, zpow_one, ← h1]
private theorem alg_of_open {art : Ideles E →* Gab E Ω} [IsAlgClosure E Ω] (ha : IsGlobalArtin art) (ι : Qbar l ≃+* ℂ)
    (κ : G E Ω →* (Qbar l)ˣ) (hκ : Continuous κ) (n : (E →+* ℂ) → ℤ)
    (h : ∀ v : HeightOneSpectrum (𝓞 E), ((l : ℕ) : 𝓞 E) ∈ v.asIdeal → ∀ x : (v.adicCompletion E)ˣ, IsUnitAt v x →
      ∃ k : ℕ, 0 < k ∧ (((liftAb κ hκ (art (localIdele E v x)) : (Qbar l)ˣ) : Qbar l) * (locPow ι n v x)⁻¹) ^ k = 1) :
    UpperTheory.V.Af.IsAlgChar ι κ := by
  obtain ⟨f, hf, hfe⟩ := exists_infPow_hom E n
  obtain ⟨g, hg, hge⟩ := exists_lPow_hom E l ι n
  let θ : Ideles E →* (Qbar l)ˣ := (liftAb κ hκ).comp art * g⁻¹
  have hθ : Continuous θ := ((continuous_liftAb κ hκ).comp ha.quot.continuous).mul hg.inv
  have hθe : ∀ x, ((θ x : (Qbar l)ˣ) : Qbar l) = ((liftAb κ hκ (art x) : (Qbar l)ˣ) : Qbar l) * (lPow ι n x)⁻¹ := fun x => by
    rw [← hge, ← Units.val_inv_eq_inv_val]
    rfl
  have hk : ∀ x ∈ (diagUnits E).range ⊔ infConn E, art x = 1 := fun x hx => by
    rw [← MonoidHom.mem_ker, ha.ker]
    exact Subgroup.le_topologicalClosure _ hx
  have h1 : ∀ x ∈ infConn E, θ x = 1 := fun x hx => Units.ext (by
    rw [hθe, hk x (Subgroup.mem_sup_right hx), lPow_of_mem_infConn ι n hx]
    simp)
  have ho := open_ker θ hθ h1 fun v hv x hx => by
    obtain ⟨k, hk0, e⟩ := h v hv x hx
    exact ⟨k, hk0, Units.ext (by rw [Units.val_pow_eq_pow_val, hθe, lPow_localIdele, e]; rfl)⟩
  let θ' : Ideles E →* ℂˣ := (Units.map ι.toRingHom.toMonoidHom).comp θ
  have hθ' : Continuous θ' := continuous_of_isOpen_ker' θ' (Subgroup.isOpen_mono (fun x hx => by
      rw [MonoidHom.mem_ker] at hx ⊢
      rw [MonoidHom.comp_apply, hx, map_one]) ho)
  have hχ : ∀ x, (((θ' * f) x : ℂˣ) : ℂ) = ι ((θ x : (Qbar l)ˣ) : Qbar l) * infPow n x := fun x => by
    rw [← hfe]
    rfl
  refine ⟨⟨θ' * f, hθ'.mul hf, fun k => Units.ext ?_⟩, hκ, art, n, ha, fun k hk => ?_, fun x σ hx => ?_⟩
  · rw [hχ, hθe, hk _ (Subgroup.mem_sup_left ⟨k, rfl⟩), infPow_diagUnits, lPow_diagUnits, map_one, Units.val_one, one_mul,
      map_inv₀, map_prod]
    simp only [map_zpow₀, RingEquiv.apply_symm_apply]
    exact inv_mul_cancel₀ (Finset.prod_ne_zero_iff.mpr fun φ _ => zpow_ne_zero _ (by simp))
  · show (((θ' * f) (infDiag k) : ℂˣ) : ℂ) = _
    rw [hχ, h1 _ (pos_conn k hk), Units.val_one, map_one, one_mul, ← infPow_diagUnits E n k, infDiag_eq]
    rfl
  · show _ = ι.symm ((((θ' * f) x : ℂˣ) : ℂ) * _) * _
    have hf0 : infPow n x ≠ 0 := hfe x ▸ Units.ne_zero _
    have hg0 : lPow ι n x ≠ 0 := hge x ▸ Units.ne_zero _
    rw [hχ, mul_inv_cancel_right₀ hf0, ι.symm_apply_apply, hθe, inv_mul_cancel_right₀ hg0, hx, liftAb_toAb]
private theorem alg_iff [IsAlgClosure E Ω] (ι : Qbar l ≃+* ℂ) (κ : G E Ω →* (Qbar l)ˣ) :
    UpperTheory.V.Af.IsAlgChar ι κ ↔ UpperTheory.V.Sd.IsAlgChar ι κ :=
  ⟨fun ⟨χ, h, art, a, h'⟩ => ⟨h, art, χ, a, h'⟩, fun ⟨h, art, χ, a, h'⟩ => ⟨χ, h, art, a, h'⟩⟩
end
theorem UpperTheory.V.Af.algOfCyc_s :
    _root_.UpperTheory.V.Af.HypothesesH' → UpperTheory.V.Af.AlgOfCyc := by
  intro hP F Ω _ _ _ _ _ l _ ι
  refine ⟨fun κ hκ h => ?_, fun κ κ' h h' => ?_, fun M _ _ _ _ _ _ κ h => ?_⟩
  · obtain ⟨art, ha⟩ : ∃ art : Ideles F →* Gab F Ω, IsGlobalArtin art := hP.toClassicalTheorems.litN.aut.art _ Ω
    choose! A hA a k hk H using h
    obtain ⟨n, hn⟩ := exists_type ι a
    refine alg_of_open ha ι κ hκ n fun v hv x hx => ⟨k v, hk v hv, ?_⟩
    obtain ⟨σ, hσ, e⟩ := (ha.ine v (A v) (hA v hv) _).mp ⟨x, hx, rfl⟩
    rw [hn, ← cyc_loc ha ι hx e.symm, ← e, liftAb_toAb, ← zpow_neg, ← Units.val_zpow_eq_zpow_val, ← Units.val_mul,
      ← Units.val_pow_eq_pow_val, H v hv σ hσ, Units.val_one]
  · have H := _root_.UpperTheory.V.Sd.alg_cyclotomic_of_printed_results hP.toClassicalTheorems F Ω l ι
    simp only [alg_iff] at h h' ⊢
    exact ⟨H.2.1 κ κ' h h', H.2.2 κ h⟩
  · exact (alg_iff ι _).2 (_root_.UpperTheory.V.Sd.alg_restriction_of_printed_results hP.toClassicalTheorems F M Ω l ι κ ((alg_iff ι κ).1 h))
end
