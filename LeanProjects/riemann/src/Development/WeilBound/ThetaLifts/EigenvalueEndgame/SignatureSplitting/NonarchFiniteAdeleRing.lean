import Development.WeilBound.ThetaLifts.EigenvalueEndgame.SignatureSplitting.ClosedEmb
import Development.WeilBound.ThetaLifts.EigenvalueEndgame.SignatureSplitting.RightOfFd
import Development.AutomorphicSpectrum.Proofs.AdelicProofs.SiegelSetsSL2AdelicTie
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup
import GroundTheory.GlobalFields.Adele.Compact

noncomputable section

set_option linter.unusedSectionVars false

namespace PositivityTheory.ThKEnd.Two

open MeasureTheory Topology Filter Matrix NumberField IsDedekindDomain GroundTheory.Global
open scoped Pointwise MatrixGroups

theorem nonarch_of_isInducing {G S : Type} [AddGroup G] [TopologicalSpace G] [NonarchimedeanAddGroup G]
    [AddGroup S] [TopologicalSpace S] [IsTopologicalAddGroup S] (f : S →+ G) (hf : Topology.IsInducing f) :
    NonarchimedeanAddGroup S where
  is_nonarchimedean U hU := by
    rw [hf.nhds_eq_comap, map_zero, Filter.mem_comap] at hU
    obtain ⟨t, ht, hsub⟩ := hU
    obtain ⟨V, hV⟩ := NonarchimedeanAddGroup.is_nonarchimedean t ht
    exact ⟨V.comap f hf.continuous, fun x hx => hsub (hV hx)⟩

theorem nonarch_pi {ι : Type} {G : ι → Type} [∀ i, AddGroup (G i)] [∀ i, TopologicalSpace (G i)]
    [∀ i, NonarchimedeanAddGroup (G i)] : NonarchimedeanAddGroup (∀ i, G i) where
  is_nonarchimedean U hU := by
    rw [nhds_pi, Filter.mem_pi] at hU
    obtain ⟨I, hI, t, ht, hs⟩ := hU
    choose K hK using fun i => NonarchimedeanAddGroup.is_nonarchimedean (G := G i) (t i) (ht i)
    exact ⟨⟨AddSubgroup.pi I fun i => (K i : AddSubgroup (G i)), isOpen_set_pi hI fun i _ => (K i).isOpen⟩,
      fun x hx => hs fun i hi => hK i (hx i hi)⟩

theorem nonarch_finiteAdeleRing (F : Type) [Field F] [NumberField F] : NonarchimedeanAddGroup (FiniteAdeleRing (𝓞 F) F) := by
  haveI : ∀ v : HeightOneSpectrum (𝓞 F), NonarchimedeanAddGroup (v.adicCompletionIntegers F) := fun v =>
    nonarch_of_isInducing (v.adicCompletionIntegers F).subtype.toAddMonoidHom Topology.IsInducing.subtypeVal
  haveI := nonarch_pi (G := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletionIntegers F)
  let f : (∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletionIntegers F) →+ FiniteAdeleRing (𝓞 F) F :=
    { toFun := RestrictedProduct.structureMap (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
        (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) Filter.cofinite
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  exact NonarchimedeanAddGroup.nonarchimedean_of_emb f
    (RestrictedProduct.isOpenEmbedding_structureMap (fun v => Valued.isOpen_integer _))

variable (K : Type) [Field K] [NumberField K]

def pI : AdeleRing (𝓞 K) K →+* ((w : InfinitePlace K) → w.Completion) where
  toFun x w := x.1 w
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

def pF : AdeleRing (𝓞 K) K →+* FiniteAdeleRing (𝓞 K) K where
  toFun x := x.2
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

theorem pI_cont : Continuous (pI K) := continuous_fst

theorem pF_cont : Continuous (pF K) := continuous_snd

variable {K}

theorem norm_emb (w : InfinitePlace K) (x : w.Completion) : ‖InfinitePlace.Completion.extensionEmbedding w x‖ = ‖x‖ :=
  (InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _) _

theorem ball_cpt (r : ℝ) (C : Set (FiniteAdeleRing (𝓞 K) K)) (hC : IsCompact C) : IsCompact {x | ‖pI K x‖ ≤ r ∧ pF K x ∈ C} := by
  have : ∀ w : InfinitePlace K, ProperSpace w.Completion := fun w => ⟨fun x r => by
    rw [← (InfinitePlace.Completion.isometry_extensionEmbedding w).preimage_closedBall]
    exact (InfinitePlace.Completion.isometry_extensionEmbedding w).isClosedEmbedding.isCompact_preimage (isCompact_closedBall _ _)⟩
  have := (isCompact_closedBall (0 : (w : InfinitePlace K) → w.Completion) r).prod hC
  exact (Set.ext fun x => and_congr_left' mem_closedBall_zero_iff :
    (Metric.closedBall (0 : (w : InfinitePlace K) → w.Completion) r ×ˢ C) = {x | ‖pI K x‖ ≤ r ∧ pF K x ∈ C}) ▸ this

theorem nhds_ad (O : Set (AdeleRing (𝓞 K) K)) (hO : O ∈ 𝓝 0) :
    ∃ ε > 0, ∃ U ∈ 𝓝 (0 : FiniteAdeleRing (𝓞 K) K), ∀ x, ‖pI K x‖ ≤ ε → pF K x ∈ U → x ∈ O := by
  obtain ⟨A, hA, U, hU, h⟩ := (mem_nhds_prod_iff (X := (w : InfinitePlace K) → w.Completion) (x := 0) (y := 0)).1 hO
  obtain ⟨ε, h0, h1⟩ := Metric.nhds_basis_closedBall.mem_iff.1 hA
  exact ⟨ε, h0, U, hU, fun x a b => h ⟨h1 (mem_closedBall_zero_iff.2 a), b⟩⟩

theorem small_ad (U : Set (FiniteAdeleRing (𝓞 K) K)) (hU : U ∈ 𝓝 0) : ∃ L : AddSubgroup (FiniteAdeleRing (𝓞 K) K),
    IsOpen (L : Set (FiniteAdeleRing (𝓞 K) K)) ∧ IsCompact (L : Set (FiniteAdeleRing (𝓞 K) K)) ∧
      (L : Set (FiniteAdeleRing (𝓞 K) K)) ⊆ U ∧ ∃ D : ℝ, ∀ x : AdeleRing (𝓞 K) K, ∃ ξ : K,
        ‖pI K (algebraMap K _ ξ + x)‖ ≤ D ∧ pF K (algebraMap K _ ξ + x) ∈ L := by
  obtain ⟨V, hV⟩ := (nonarch_finiteAdeleRing K).is_nonarchimedean U hU
  let O := (integralFiniteAdeles (𝓞 K) K).toAddSubgroup
  have hO : IsCompact (O : Set (FiniteAdeleRing (𝓞 K) K)) := isCompact_integralFiniteAdeles K
  have : CompactSpace O := isCompact_iff_compactSpace.1 hO
  have ho : IsOpen ((V.toAddSubgroup ⊓ O : AddSubgroup _) : Set (FiniteAdeleRing (𝓞 K) K)) :=
    V.isOpen.inter isOpen_integralFiniteAdeles
  have := (V.toAddSubgroup.addSubgroupOf O).quotient_finite_of_isOpen (V.isOpen.preimage continuous_subtype_val)
  have hi : (V.toAddSubgroup.addSubgroupOf O).index ≠ 0 := AddSubgroup.index_ne_zero_of_finite
  obtain ⟨C, hC, hx⟩ := exists_isCompact_forall_exists_sub_mem K
  obtain ⟨D, hD⟩ := IsCompact.exists_bound_of_continuousOn (f := fun z : (w : InfinitePlace K) → w.Completion => z) hC continuousOn_id
  set M := (V.toAddSubgroup.addSubgroupOf O).index
  refine ⟨V.toAddSubgroup ⊓ O, ho, hO.of_isClosed_subset (AddSubgroup.isClosed_of_isOpen _ ho) inf_le_right,
    fun x hx => hV hx.1, M * D, fun x => ?_⟩
  obtain ⟨k, h1, h2⟩ := hx (algebraMap K _ (M : K)⁻¹ * x)
  have e : algebraMap K _ (-(M * k)) + x = M • (algebraMap K (AdeleRing (𝓞 K) K) (M : K)⁻¹ * x - algebraMap K _ k) := by
    rw [nsmul_eq_mul, ← map_natCast (algebraMap K (AdeleRing (𝓞 K) K)), mul_sub, ← mul_assoc, ← map_mul, ← map_mul,
      mul_inv_cancel₀ (Nat.cast_ne_zero.2 hi), map_one, one_mul, map_neg, neg_add_eq_sub]
  refine ⟨-(M * k), ?_, ?_⟩
  · rw [e, map_nsmul]
    exact (norm_nsmul_le).trans (mul_le_mul_of_nonneg_left (hD _ h1) M.cast_nonneg)
  · rw [e, map_nsmul]
    exact ⟨AddSubgroup.nsmul_index_mem (V.toAddSubgroup.addSubgroupOf O) ⟨_, h2⟩, O.nsmul_mem h2 _⟩

theorem norm_half {u : (AdeleRing (𝓞 K) K)ˣ} (hu : 2 * pI K (u⁻¹).1 = 1) (w : InfinitePlace K) : ‖pI K (u⁻¹).1 w‖ = 1 / 2 := by
  have := congrArg (fun z => ‖InfinitePlace.Completion.extensionEmbedding w (z w)‖) hu
  simp only [Pi.mul_apply, Pi.ofNat_apply, map_mul, map_ofNat, norm_mul, norm_emb, Pi.one_apply, norm_one, Complex.norm_ofNat] at this
  linarith

theorem siegel_ad {u : (AdeleRing (𝓞 K) K)ˣ} (hu : 2 * pI K (u⁻¹).1 = 1) (hu' : pF K (u⁻¹).1 = 1) :
    ∃ Ω : Set SL(2, AdeleRing (𝓞 K) K), IsCompact Ω ∧ ∀ g, ∃ γ ∈ (Matrix.SpecialLinearGroup.map (algebraMap K (AdeleRing (𝓞 K) K))).range,
      ∃ k : ℕ, ∃ κ ∈ Ω, γ * g = dia u ^ k * κ := by
  obtain ⟨Ω, K₀, t₀, h1, h2, h3, h4, h5⟩ := GlobalTheory.CompanionTheory.Classical.siegelSetsSL2Adelic_tie K
  have hC : IsCompact (⋃ i, ⋃ j, (fun z : SL(2, AdeleRing (𝓞 K) K) => z.1 i j) '' Ω) :=
    isCompact_iUnion fun i => isCompact_iUnion fun j => h1.image (continuous_subtype_val.matrix_elem i j)
  obtain ⟨r, hr⟩ := hC.exists_bound_of_continuousOn (pI_cont K).continuousOn
  refine ⟨_, ((box fun _ _ => ball_cpt r _ (hC.image (pF_cont K))).mul
    (box fun _ _ => ball_cpt (2 * t₀ + t₀⁻¹) {0, 1} (Set.toFinite _).isCompact)).mul h3, fun g => ?_⟩
  obtain ⟨γ, a1, p, a2, t, a3, a, a', a4, k, a5, a6⟩ := h5 g
  obtain ⟨j, b1, b2⟩ := exists_nat_pow_near ((one_le_div h4).2 a3) one_lt_two
  rw [le_div_iff₀ h4] at b1
  rw [div_lt_iff₀ h4, pow_succ] at b2
  have t0 : 0 < t := h4.trans_le a3
  let A : (AdeleRing (𝓞 K) K)ˣ := ⟨Formalism.D.adeleOfParts K a 1, Formalism.D.adeleOfParts K a' 1,
    Prod.ext (funext fun w => (a4 w).1) (mul_one _), Prod.ext (funext fun w => (mul_comm _ _).trans (a4 w).1) (mul_one _)⟩
  have e : γ * g = p * dia A * k := Subtype.ext a6
  have n1 : ∀ w, ‖pI K ((u ^ j)⁻¹).1 w‖ = (2 ^ j)⁻¹ := fun w => by
    rw [← inv_pow, Units.val_pow_eq_pow_val, map_pow, Pi.pow_apply, norm_pow, norm_half hu, one_div, inv_pow]
  have n2 : pF K ((u ^ j)⁻¹).1 = 1 := by rw [← inv_pow, Units.val_pow_eq_pow_val, map_pow, hu', one_pow]
  have n3 : ∀ w, ‖pI K A.1 w‖ = t := fun w => by
    rw [← norm_emb, show pI K A.1 w = a w from rfl, (a4 w).2, Complex.norm_real, Real.norm_of_nonneg t0.le]
  have n4 : ∀ (v : (AdeleRing (𝓞 K) K)ˣ) w, ‖pI K (v⁻¹).1 w‖ = ‖pI K v.1 w‖⁻¹ := fun v w => by
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← norm_mul, ← Pi.mul_apply, ← map_mul, Units.inv_mul, map_one, Pi.one_apply, norm_one]
  have n5 : ∀ w, ‖pI K ((u ^ j)⁻¹ * A).1 w‖ = t / 2 ^ j := fun w => by
    rw [Units.val_mul, map_mul, Pi.mul_apply, norm_mul, n1, n3, div_eq_inv_mul]
  have n6 : pF K ((u ^ j)⁻¹ * A).1 = 1 := by rw [Units.val_mul, map_mul, n2, one_mul]; rfl
  have n7 : pF K (((u ^ j)⁻¹ * A)⁻¹).1 = 1 := by
    rw [← one_mul (pF K _), ← n6, ← map_mul, Units.mul_inv, map_one, n6]
  have p2 : (0 : ℝ) < 2 ^ j := by positivity
  have m : ∀ i l, ‖pI K (p.1 i l)‖ ≤ r ∧ pF K (p.1 i l) ∈ pF K '' ⋃ i, ⋃ j, (fun z : SL(2, AdeleRing (𝓞 K) K) => z.1 i j) '' Ω :=
    fun i l => ⟨hr _ (Set.mem_iUnion₂.2 ⟨i, l, p, a2, rfl⟩), _, Set.mem_iUnion₂.2 ⟨i, l, p, a2, rfl⟩, rfl⟩
  refine ⟨γ, a1, j, dia (u ^ j)⁻¹ * p * dia (u ^ j) * dia ((u ^ j)⁻¹ * A) * k,
    Set.mul_mem_mul (Set.mul_mem_mul (fun i l => ?_) fun i l => ?_) a5, by simp only [e, map_mul, map_inv, map_pow]; group⟩
  · have c : (dia (u ^ j)⁻¹ * p * dia (u ^ j)).1 = !![p.1 0 0, ((u ^ j)⁻¹).1 * (((u ^ j)⁻¹).1 * p.1 0 1); p.1 1 0, p.1 1 1] := by
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, dia_val, dia_val, Matrix.eta_fin_two p.1,
        Matrix.mul_fin_two, Matrix.mul_fin_two, inv_inv]
      have z : p.1 1 0 = 0 := h2 p a2
      generalize u ^ j = v
      simp only [z, mul_zero, zero_mul, add_zero, zero_add, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one]
      rw [mul_right_comm, Units.inv_mul, one_mul, mul_right_comm v.1, Units.mul_inv, one_mul, mul_right_comm, mul_assoc]
    rw [c]
    fin_cases i <;> fin_cases l
    · exact m 0 0
    · refine ⟨le_trans ?_ (m 0 1).1, ?_⟩
      · refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun w => le_trans ?_ (norm_le_pi_norm _ w)
        change ‖pI K (_ * (_ * p.1 0 1)) w‖ ≤ _
        rw [map_mul, map_mul, Pi.mul_apply, Pi.mul_apply, norm_mul, norm_mul, n1]
        have : ((2 : ℝ) ^ j)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ one_le_two)
        exact (mul_le_of_le_one_left (by positivity) this).trans (mul_le_of_le_one_left (by positivity) this)
      · change pF K (_ * (_ * p.1 0 1)) ∈ _
        rw [map_mul, map_mul, n2, one_mul, one_mul]
        exact (m 0 1).2
    · exact m 1 0
    · exact m 1 1
  · have q0 : 0 ≤ 2 * t₀ + t₀⁻¹ := by positivity
    have q1 : 0 < t₀⁻¹ := by positivity
    rw [dia_val]
    fin_cases i <;> fin_cases l
    · refine ⟨(pi_norm_le_iff_of_nonneg q0).2 fun w => (n5 w).trans_le ?_, Or.inr n6⟩
      exact ((div_le_iff₀ p2).2 (by linarith)).trans (le_add_of_nonneg_right q1.le)
    · exact ⟨by simpa using q0, Or.inl (map_zero _)⟩
    · exact ⟨by simpa using q0, Or.inl (map_zero _)⟩
    · refine ⟨(pi_norm_le_iff_of_nonneg q0).2 fun w => ((n4 _ w).trans (congrArg _ (n5 w))).trans_le ?_, Or.inr n7⟩
      exact (inv_anti₀ h4 ((le_div_iff₀ p2).2 (by linarith))).trans (le_add_of_nonneg_left (by positivity))

variable {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] (Φ : R ≃+* AdeleRing (𝓞 K) K)
  (hΦ : Continuous Φ) (hΦ' : Continuous Φ.symm) {inc : K →+* R} (hi : ∀ x, Φ (inc x) = algebraMap K _ x)

include hΦ hΦ' hi

theorem cusp_of {u : Rˣ} (hu : 2 * pI K (Φ (u⁻¹).1) = 1) (hu' : pF K (Φ (u⁻¹).1) = 1) :
    Cusp (Matrix.SpecialLinearGroup.map (n := Fin 2) inc).range uni (dia u) := by
  let v : (AdeleRing (𝓞 K) K)ˣ := Units.map (Φ : R →* _) u
  refine ⟨?_, lip_of ((pI K).comp Φ) ((pF K).comp Φ) ((pI_cont K).comp hΦ) ((pF_cont K).comp hΦ) (fun r C hC => ?_)
    (fun O hO => ?_) (fun U hU => ?_) ((pi_norm_le_iff_of_nonneg one_half_pos.le).2 fun w => (norm_half (u := v) hu w).le) hu'⟩
  · obtain ⟨Ω, h1, h2⟩ := siegel_ad (u := v) hu hu'
    let s := Matrix.SpecialLinearGroup.map (n := Fin 2) Φ.symm.toRingHom
    refine ⟨s '' Ω, h1.image (Continuous.subtype_mk (continuous_subtype_val.matrix_map hΦ') _), fun g => ?_⟩
    obtain ⟨_, ⟨γ, rfl⟩, k, κ, a1, a2⟩ := h2 (Matrix.SpecialLinearGroup.map Φ.toRingHom g)
    refine ⟨_, ⟨γ, rfl⟩, k, _, ⟨κ, a1, rfl⟩, ?_⟩
    have := congrArg s a2
    rw [map_mul, map_mul, map_pow] at this
    convert this using 2
    · exact Subtype.ext (Matrix.ext fun i j => ((Φ.symm_apply_eq).2 (hi _).symm).symm)
    · exact Subtype.ext (Matrix.ext fun i j => (Φ.symm_apply_apply _).symm)
    · congr 1
      refine Subtype.ext (Matrix.ext fun i j => ?_)
      fin_cases i <;> fin_cases j
      exacts [(Φ.symm_apply_apply _).symm, (map_zero Φ.symm).symm, (map_zero Φ.symm).symm, (Φ.symm_apply_apply _).symm]
  · exact (Homeomorph.mk Φ.toEquiv hΦ hΦ').isCompact_preimage.2 (ball_cpt r C hC)
  · obtain ⟨ε, h0, U, hU, h⟩ := nhds_ad (Φ.symm ⁻¹' O) (hΦ'.continuousAt.preimage_mem_nhds (by rwa [map_zero]))
    exact ⟨ε, h0, U, hU, fun x a b => by simpa using h (Φ x) a b⟩
  · obtain ⟨L, a, b, c, D, hD⟩ := small_ad U hU
    refine ⟨L, a, b, c, D, fun x => ?_⟩
    obtain ⟨ξ, h⟩ := hD (Φ x)
    rw [← hi, ← map_add] at h
    refine ⟨inc ξ, ⟨uni (.ofAdd ξ), Subtype.ext (Matrix.ext fun i j => ?_)⟩, h⟩
    fin_cases i <;> fin_cases j
    exacts [map_one inc, rfl, map_zero inc, map_one inc]

theorem lat_of : Lat (inc.toAddMonoidHom.toMultiplicative).range := by
  refine ⟨?_, ?_, ?_⟩
  · have : Countable K := Finsupp.Countable.of_moduleFinite (R := ℚ)
    have : Countable (Multiplicative K) := this
    exact (Set.countable_range _).to_subtype
  · have := discreteTopology_principalSubgroup K
    have k : ∀ x : (inc.toAddMonoidHom.toMultiplicative).range, Φ x.1.toAdd ∈ AdeleRing.principalSubgroup (𝓞 K) K := by
      rintro ⟨_, y, rfl⟩
      exact ⟨y.toAdd, (hi _).symm⟩
    exact DiscreteTopology.of_continuous_injective (f := fun x => (⟨_, k x⟩ : AdeleRing.principalSubgroup (𝓞 K) K))
      (Continuous.subtype_mk (hΦ.comp (continuous_toAdd.comp continuous_subtype_val)) k) fun x y h =>
        Subtype.ext (Φ.injective (congrArg Subtype.val h))
  · obtain ⟨L, -, b, -, D, hD⟩ := small_ad (K := K) _ univ_mem
    refine ⟨_, ((ball_cpt D L b).image hΦ').image continuous_ofAdd, fun x => ?_⟩
    obtain ⟨ξ, h⟩ := hD (Φ x.toAdd)
    rw [← hi, ← map_add] at h
    exact ⟨_, ⟨.ofAdd ξ, rfl⟩, _, ⟨_, h, Φ.symm_apply_apply _⟩, rfl⟩

end PositivityTheory.ThKEnd.Two

end
