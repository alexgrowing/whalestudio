import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.CoreDet
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LitAut
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.UnitaryPointProperties
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TCoreSep
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.HeckeOperatorPreservesPart
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CdNormLt

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V UpperTheory.V.Hi
open UpperTheory.V.HV (Coef)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [local instance high] UpperTheory.V.W.coefLocal
private theorem cd_compact {R : Type} [CommRing R] [WithIdeal R] [IsAdicComplete (WithIdeal.i : Ideal R) R]
    (hf : ∀ N : ℕ, Finite (R ⧸ (WithIdeal.i : Ideal R) ^ N)) : CompactSpace R := by
  have hI : IsAdic (WithIdeal.i : Ideal R) := rfl
  have hc : CompleteSpace R := (hI.isAdicComplete_iff.1 inferInstance).1
  refine ⟨isCompact_iff_totallyBounded_isComplete.2 ⟨?_, complete_univ⟩⟩
  rw [totallyBounded_iff_subset_finite_iUnion_nhds_zero]
  intro U hU
  obtain ⟨N, hN⟩ := (isAdic_iff.1 hI).2 U hU
  choose s hs using fun q : R ⧸ (WithIdeal.i : Ideal R) ^ N => Ideal.Quotient.mk_surjective q
  refine ⟨Set.range s, Set.finite_range s, fun x _ => ?_⟩
  refine Set.mem_biUnion (Set.mem_range_self (Ideal.Quotient.mk _ x)) ⟨x - s (Ideal.Quotient.mk _ x), hN ?_, by simp⟩
  exact Ideal.Quotient.eq.1 (hs _).symm
private theorem cd_intIff {l : ℕ} [Fact l.Prime] (x : PadicAlgCl l) : IsIntegral ℤ_[l] x ↔ ‖x‖ ≤ 1 := by
  have hi : IsIntegral ℚ_[l] x := Algebra.IsIntegral.isIntegral x
  have h0 : ‖x‖ = spectralValue (minpoly ℚ_[l] x) := rfl
  rw [h0, spectralValue_le_one_iff (minpoly.monic hi)]
  constructor
  · intro h n
    rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[l] h, coeff_map]
    exact PadicInt.norm_le_one _
  · intro h
    have hl' : minpoly ℚ_[l] x ∈ lifts (algebraMap ℤ_[l] ℚ_[l]) :=
      (lifts_iff_coeff_lifts _).mpr fun n => ⟨⟨_, h n⟩, rfl⟩
    obtain ⟨q, hq, -, hqm⟩ := lifts_and_degree_eq_and_monic hl' (minpoly.monic hi)
    exact ⟨q, hqm, by rw [← aeval_def, ← aeval_map_algebraMap ℚ_[l], hq, minpoly.aeval]⟩
private theorem cd_norm_lt {l : ℕ} [Fact l.Prime] (c : Coef l) {R : Type} [CommRing R] [IsLocalRing R] [Algebra c.O R]
    (y : R →ₐ[c.O] PadicAlgCl l) (a : R) (ha : a ∈ maximalIdeal R) : ‖y a‖ < 1 :=
  _root_.UpperTheory.Reformulated.B.Gs5b.cd_norm_lt c y a ha
private theorem cd_pow {l : ℕ} [Fact l.Prime] (c : Coef l) {R : Type} [CommRing R] [Algebra c.O R] [Alg.IsCO c.O R]
    (y : R →ₐ[c.O] PadicAlgCl l) : ∃ b : ℝ, 0 ≤ b ∧ b < 1 ∧ ∀ N : ℕ, ∀ a ∈ maximalIdeal R ^ N, ‖y a‖ ≤ b ^ N := by
  have h1 : ∀ a, ‖y a‖ ≤ 1 := fun a => by
    obtain ⟨o, ho⟩ := Alg.IsCO.res_surj (O := c.O) a
    have e : y a = y (a - algebraMap c.O R o) + algebraMap c.O _ o := by simp
    rw [e]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (cd_norm_lt c y _ ho).le ((cd_intIff _).1 ?_))
    exact (Algebra.IsIntegral.isIntegral (R := ℤ_[l]) o).map (IsScalarTower.toAlgHom ℤ_[l] c.O (PadicAlgCl l))
  let J : ℝ → Ideal R := fun b =>
    { carrier := {a | ‖y a‖ ≤ max b 0}
      add_mem' := fun {p q} hp hq => by
        change ‖y (p + q)‖ ≤ _
        rw [map_add]
        exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hp hq)
      zero_mem' := by simp
      smul_mem' := fun r p hp => by
        change ‖y (r * p)‖ ≤ _
        rw [map_mul, norm_mul]
        exact (mul_le_of_le_one_left (norm_nonneg _) (h1 r)).trans hp }
  obtain ⟨s, hs⟩ := IsNoetherian.noetherian (maximalIdeal R)
  have hb : ∃ b : ℝ, 0 ≤ b ∧ b < 1 ∧ ∀ a ∈ s, ‖y a‖ ≤ b := by
    refine ⟨(s.sup fun a => ‖y a‖₊ : NNReal), NNReal.coe_nonneg _, ?_, fun a ha => ?_⟩
    · rw [← NNReal.coe_one, NNReal.coe_lt_coe, Finset.sup_lt_iff (by simp)]
      exact fun a ha => cd_norm_lt c y a (hs ▸ Submodule.subset_span ha)
    · exact NNReal.coe_le_coe.2 (Finset.le_sup (f := fun a => ‖y a‖₊) ha)
  obtain ⟨b, b0, b1, hb⟩ := hb
  have hm : ∀ a ∈ maximalIdeal R, ‖y a‖ ≤ b := fun a ha => by
    have : maximalIdeal R ≤ J b := by
      rw [← hs, Submodule.span_le]
      exact fun a ha => (hb a ha).trans (le_max_left _ _)
    exact (this ha).trans (max_le le_rfl b0)
  refine ⟨b, b0, b1, fun N => ?_⟩
  induction N with
  | zero => simpa using h1
  | succ N ih =>
    have : maximalIdeal R ^ (N + 1) ≤ J (b ^ (N + 1)) := by
      rw [pow_succ (maximalIdeal R), Ideal.mul_le]
      intro p hp q hq
      change ‖y (p * q)‖ ≤ max (b ^ (N + 1)) 0
      refine le_trans ?_ (le_max_left _ _)
      rw [map_mul, norm_mul, pow_succ]
      exact mul_le_mul (ih p hp) (hm q hq) (norm_nonneg _) (pow_nonneg b0 _)
    exact fun a ha => (this ha).trans (max_le le_rfl (pow_nonneg b0 _))
private theorem cd_cont {l : ℕ} [Fact l.Prime] (c : Coef l) {R : Type} [CommRing R] [Algebra c.O R] [Alg.IsCO c.O R]
    [TopologicalSpace R] [IsTopologicalRing R] (hI : IsAdic (maximalIdeal R))
    (y : R →ₐ[c.O] PadicAlgCl l) : Continuous y := by
  obtain ⟨b, b0, b1, hb⟩ := cd_pow c y
  refine continuous_of_continuousAt_zero y (Metric.tendsto_nhds.2 fun ε hε => ?_)
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hε b1
  filter_upwards [((isAdic_iff.1 hI).1 N).mem_nhds (zero_mem _)] with a ha
  rw [map_zero, dist_zero_right]
  exact (hb N a ha).trans_lt hN
private theorem cd_xi {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {R : Type} [CommRing R] (I : Ideal R) (φ : Uo k →* Rˣ) (u : Rˣ)
    (hφ : ∀ N : ℕ, ∃ c : ℕ, ∀ y : Uo k, valuation k (((y : kˣ) : k) - 1) ≤ uniformizer k ^ ((c + 1 : ℕ) : ℤ) →
      (φ y : R) - 1 ∈ I ^ N) :
    ∃ ξ : kˣ →* Rˣ, Alg.AdicCont I (fun x => (ξ x : R)) ∧ (∀ y : Uo k, ξ y = φ y) ∧ ξ (unif k) = u := by
  let ξ : kˣ →* Rˣ := MonoidHom.mk' (fun x => φ ⟨x / unif k ^ ord k x, GlAx.val_div_ord x⟩ * u ^ ord k x) fun x y => by
    rw [mul_mul_mul_comm, ← map_mul, ← _root_.zpow_add, ← ord_mul]
    congr 2
    refine Subtype.ext ?_
    change x * y / _ = x / _ * (y / _)
    rw [ord_mul, _root_.zpow_add, mul_div_mul_comm]
  have h1 : ∀ y : Uo k, ξ y = φ y := fun y => by
    change φ ⟨_, _⟩ * u ^ ord k y = φ y
    have : ord k y = 0 := ord_eq_zero y.2
    simp only [this, zpow_zero, div_one, mul_one]
  refine ⟨ξ, fun N => ?_, h1, ?_⟩
  · obtain ⟨c, hc⟩ := hφ N
    rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    have hp : uniformizer k ^ ((c + 1 : ℕ) : ℤ) ≠ 0 := (zpow_pos GlAx.unif_pos _).ne'
    have hlt : uniformizer k ^ ((c + 1 : ℕ) : ℤ) < 1 := zpow_lt_one₀ GlAx.unif_pos uniformizer_lt_one (by omega)
    have hn : {z : k | valuation k z < uniformizer k ^ ((c + 1 : ℕ) : ℤ)} ∈ nhds (0 : k) :=
      (IsValuativeTopology.mem_nhds_zero_iff _).2 ⟨Units.mk0 _ hp, subset_rfl⟩
    have hc' : Continuous fun y : kˣ => ((x⁻¹ * y : kˣ) : k) - 1 :=
      (Units.continuous_val.comp (continuous_const.mul continuous_id)).sub continuous_const
    filter_upwards [hc'.continuousAt.preimage_mem_nhds (x := x) (by simpa using hn)] with y hy
    have hy' : valuation k (((x⁻¹ * y : kˣ) : k) - 1) < uniformizer k ^ ((c + 1 : ℕ) : ℤ) := hy
    have hu : x⁻¹ * y ∈ Uo k := by
      have := (valuation k).map_one_add_of_lt (hy'.trans hlt)
      rwa [add_sub_cancel] at this
    have e : ξ y = ξ x * φ ⟨_, hu⟩ := by rw [← h1, ← map_mul]; simp
    rw [Ideal.Quotient.eq, e, Units.val_mul, ← mul_sub_one]
    exact Ideal.mul_mem_left _ _ (hc ⟨_, hu⟩ hy'.le)
  · change φ ⟨_, _⟩ * u ^ ord k (unif k) = u
    have : ord k (unif k) = 1 := ord_eq_one GlAx.unif_spec
    simp only [this, zpow_one, div_self']
    rw [show φ ⟨1, _⟩ = 1 from map_one φ, one_mul]
private theorem cd_alg {Γ R : Type} [TopologicalSpace Γ] [CommRing R] {l : ℕ} [Fact l.Prime] (π : ℤ_[l] →+* R)
    (I : Ideal R) (hI : (l : R) ∈ I) (f : Γ → ℤ_[l]) (hf : Continuous f) :
    Alg.AdicCont I fun g => π (f g) := by
  intro n
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have hpos : (0 : ℝ) < (l : ℝ) ^ (-(n : ℤ)) := zpow_pos (by exact_mod_cast (Fact.out : l.Prime).pos) _
  filter_upwards [hf.continuousAt.eventually (Metric.closedBall_mem_nhds (f x) hpos)] with y hy
  rw [dist_eq_norm, PadicInt.norm_le_pow_iff_mem_span_pow, Ideal.mem_span_singleton'] at hy
  obtain ⟨a, ha⟩ := hy
  rw [Ideal.Quotient.eq, ← map_sub, ← ha, map_mul, map_pow, map_natCast]
  exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_pow hI n)
private theorem cd_tel {M : Type} [CommGroup M] {n : ℕ} (U : Fin n → M) :
    ∃ u : Fin n → M, ∀ j, ∏ i with i ≤ j, u i = U j := by
  let V : ℕ → M := fun j => if h : 0 < j ∧ j - 1 < n then U ⟨j - 1, h.2⟩ else 1
  refine ⟨fun i => V (i + 1) / V i, fun j => ?_⟩
  have e : ∏ i with i ≤ j, V (i + 1) / V i = ∏ i ∈ Finset.range (j + 1), V (i + 1) / V i := by
    refine Finset.prod_bij (fun i _ => (i : ℕ)) ?_ ?_ ?_ ?_
    · intro i hi
      have : (i : ℕ) ≤ j := (Finset.mem_filter.1 hi).2
      simp; omega
    · exact fun a _ b _ h => Fin.ext h
    · intro b hb
      have := Finset.mem_range.1 hb
      have := j.2
      exact ⟨⟨b, by omega⟩, Finset.mem_filter.2 ⟨Finset.mem_univ _, by rw [Fin.le_def]; simp; omega⟩, rfl⟩
    · exact fun _ _ => rfl
  rw [e, Finset.prod_range_div]
  simp [V]
private theorem cd_fin {l : ℕ} [Fact l.Prime] (c : Coef l) : Finite (ResidueField c.O) := by
  have h : (maximalIdeal c.O).comap (algebraMap ℤ_[l] c.O) = maximalIdeal ℤ_[l] :=
    eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal _)
  have : IsLocalHom (algebraMap ℤ_[l] c.O) := ((IsLocalRing.local_hom_TFAE _).out 4 0).1 h
  exact ResidueField.finite_of_finite (R := ℤ_[l]) inferInstance
private theorem cd_eT {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}
    (i : Fin n) (c : ℕ) (y : Uo k) (hy : valuation k (((y : kˣ) : k) - 1) ≤ uniformizer k ^ ((c + 1 : ℕ) : ℤ)) :
    (eT k n i y : GL (Fin n) k) ∈ (glIwa k n).Tc c := by
  have key : ∀ y : Uo k, valuation k (((y : kˣ) : k) - 1) ≤ uniformizer k ^ ((c + 1 : ℕ) : ℤ) →
      GlAx.Bd ((c + 1 : ℕ) : ℤ) (eT k n i y : GL (Fin n) k) := fun y hy a b => by
    change valuation k (((diagT k (Fin n) (Pi.mulSingle i (y : kˣ))).val - 1) a b) ≤ _
    rw [val_diagT, ← Matrix.diagonal_one, Matrix.diagonal_sub, Matrix.diagonal_apply]
    split_ifs with h
    · by_cases h' : a = i
      · subst h'
        simpa using hy
      · simp [Pi.mulSingle_eq_of_ne h']
    · simp
  refine ⟨(eT k n i y).2, GlAx.mem_Kc.2 ⟨key y hy, ?_⟩⟩
  rw [← Subgroup.coe_inv, ← map_inv]
  refine key _ ?_
  have h1 : valuation k ((y : kˣ) : k) = 1 := y.2
  have e : (((y⁻¹ : Uo k) : kˣ) : k) - 1 = -(((y : kˣ) : k) - 1) * ((y : kˣ) : k)⁻¹ := by
    rw [Subgroup.coe_inv, Units.val_inv_eq_inv_val]
    field_simp
    ring
  rw [e, map_mul, map_inv₀, h1, Valuation.map_neg]
  simpa using hy
private theorem cd_psi (hN : _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis) {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
    {l : ℕ} [Fact l.Prime] {n : ℕ} {c : Coef l} (H : HSet L Ω l n c) (hH : H.Ax)
    {A : Type} [CommRing A] [Algebra c.O A] [Alg.IsCO c.O A] (θ : H.X.I.T →* Aˣ) (hθ : H.X.I.ContChar θ)
    {T : Type} [CommRing T] [Algebra c.O T] [Alg.IsCO c.O T] (f : A →ₐ[c.O] T) (v : H.V) (i : Fin n) (u : Tˣ) :
    ∃ ψ : Dec (F := L) (H.pl v) →* Tˣ, Alg.AdicCont (maximalIdeal T) (fun g => (ψ g : T)) ∧
      (∀ (s : Weil (H.ovr v)) (g : Dec (F := L) (H.pl v)) (y : Uo ((H.Sl v).adicCompletion L)),
        (g : G L Ω) = (s : G L Ω) → H.art v s = y →
        (ψ g * H.epsV T v g ^ (i : ℕ) : Tˣ) * f (θ (eV n H.Sl v i y)) = 1) ∧
      ∀ (s : Weil (H.ovr v)) (g : Dec (F := L) (H.pl v)), (g : G L Ω) = (s : G L Ω) → H.art v s = Hi.unif _ →
        ψ g * H.epsV T v g ^ (i : ℕ) = u := by
  classical
  let e : Uo ((H.Sl v).adicCompletion L) →* H.X.I.T := MonoidHom.mk' (eV n H.Sl v i) fun x y => Subtype.ext (by
    change (eV n H.Sl v i (x * y)).1 = (eV n H.Sl v i x).1 * (eV n H.Sl v i y).1
    unfold eV
    simp only [map_mul, Subgroup.coe_mul, Pi.mulSingle_mul])
  let φ : Uo ((H.Sl v).adicCompletion L) →* Tˣ := ((Units.map (f : A →* T)).comp (θ.comp e))⁻¹
  have hle : ∀ N, maximalIdeal A ^ N ≤ (maximalIdeal T ^ N).comap (f : A →+* T) := fun N => by
    refine le_trans (Ideal.pow_right_mono (fun y hy => ?_) N) (Ideal.le_comap_pow _ N)
    show f y ∈ maximalIdeal T
    rw [← Alg.res_eq_zero_iff c.O, Alg.res_map, Alg.res_eq_zero_iff]
    exact hy
  obtain ⟨ξ, hξ, hξu, hξp⟩ := cd_xi (maximalIdeal T) φ u fun N => by
    obtain ⟨b, hb⟩ := hθ N
    refine ⟨b, fun y hy => ?_⟩
    have h1 : ((e y : H.X.I.T) : GV n H.Sl) ∈ H.X.I.Tc b := fun v' _ => by
      change (eV n H.Sl v i y).1 v' ∈ _
      unfold eV
      by_cases h : v' = v
      · subst h
        simp only [Pi.mulSingle_eq_same]
        exact cd_eT i b y hy
      · simp only [Pi.mulSingle_eq_of_ne h]
        exact Subgroup.one_mem _
    have h2 := hle N (hb (e y)⁻¹ (inv_mem h1))
    rw [Ideal.mem_comap, map_sub, map_one, map_inv] at h2
    exact h2
  have := cd_fin c
  have hcnl := IsCNL.ofCO c.O T
  obtain ⟨ψ, ⟨hψ, hψa⟩, -⟩ := Loc.charExt hN.aut.art (H.ovr v) (H.art v) (hH.art_spec v) T ξ hξ
  have hl : ((l : ℕ) : T) ∈ maximalIdeal T := by
    have h : (maximalIdeal c.O).comap (algebraMap ℤ_[l] c.O) = maximalIdeal ℤ_[l] :=
      eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal _)
    have h1 : (l : ℤ_[l]) ∈ maximalIdeal ℤ_[l] := by
      rw [PadicInt.maximalIdeal_eq_span_p]; exact Ideal.mem_span_singleton_self _
    rw [← h, Ideal.mem_comap] at h1
    have h2 := map_nonunit (algebraMap c.O T) _ h1
    rwa [map_natCast, map_natCast] at h2
  have hc := cd_alg ((algebraMap c.O T).comp (algebraMap ℤ_[l] c.O)) _ hl
    (fun g : Dec (F := L) (H.pl v) => ((cycZ L Ω l g ^ (i : ℕ))⁻¹ : ℤ_[l]ˣ))
    (Units.continuous_coe_inv.comp (((continuous_cycZ L Ω l).comp continuous_subtype_val).pow _))
  have hv : ∀ g, (ψ * (H.epsV T v ^ (i : ℕ))⁻¹) g * H.epsV T v g ^ (i : ℕ) = ψ g := fun g => by simp
  refine ⟨ψ * (H.epsV T v ^ (i : ℕ))⁻¹, fun N => ?_, fun s g y hg hy => ?_, fun s g hg hy => ?_⟩
  · convert (hψ N).mul (hc N) using 1
    funext g
    rw [Pi.mul_apply, ← map_mul]
    congr 1
    simp [HSet.epsV]
  · rw [hv, hψa s g hg trivial, hy, hξu]
    exact Units.inv_mul (Units.map (f : A →* T) (θ (e y)))
  · rw [hv, hψa s g hg trivial, hy, hξp]
private theorem cd_glue {l : ℕ} [Fact l.Prime] (c : Coef l) {n : ℕ} {T Γ : Type} [CommRing T] [Algebra c.O T] [Alg.IsCO c.O T]
    [Group Γ] [TopologicalSpace Γ] (Q : (T →ₐ[c.O] Qbar l) → Prop) (hsep : ∀ t, (∀ x, Q x → x t = 0) → t = 0)
    {J : Type} (s : J → Γ) (p : J → T[X]) (hs : DenseRange s)
    (hr : ∀ x, Q x → ∃ r : Γ →* GL (Fin n) (Qbar l), Continuous r ∧
      ∀ j, (p j).map x.toRingHom = (r (s j) : Matrix (Fin n) (Fin n) (Qbar l)).charpoly) :
    ∃ D : W.GDet n T Γ, D.IsCont (maximalIdeal T) ∧ ∀ j, D.chi (MonoidAlgebra.single (s j) 1) = p j := by
  choose r hrc hrf using hr
  have := cd_fin c
  have hcnl := IsCNL.ofCO c.O T
  letI : WithIdeal T := ⟨maximalIdeal _⟩
  have hI : IsAdic (maximalIdeal T) := rfl
  haveI : CompactSpace T := @cd_compact _ _ _ hcnl.complete fun N => by
    haveI : Finite (T ⧸ maximalIdeal T) := hcnl.finite
    exact Ideal.finite_quotient_pow (I := maximalIdeal T) (IsNoetherian.noetherian _) N
  have hinj : ∀ t : T, (∀ x : {x // Q x}, x.1.toRingHom t = 0) → t = 0 :=
    fun t ht => hsep t fun x hx => ht ⟨x, hx⟩
  obtain ⟨D, hD, hDc⟩ := AlgebraTools.Det.glueRep (fun _ : {x // Q x} => Qbar l) (fun x => x.1.toRingHom)
    (fun x => W.mat (r x.1 x.2)) _ (fun x => cd_cont c hI x.1) hinj hs
    (fun x => Units.continuous_val.comp (hrc x.1 x.2)) (by
      rintro _ ⟨j, rfl⟩
      exact ⟨_, fun x => hrf x.1 x.2 j⟩)
  refine ⟨D, (AlgebraTools.Det.isContIff _ hI D).2 hDc, fun j => Polynomial.ext fun k => ?_⟩
  rw [← sub_eq_zero]
  refine hinj _ fun x => ?_
  have h1 := (AlgebraTools.Det.mapApi D x.1.toRingHom).1 (MonoidAlgebra.single (s j) 1)
  rw [hD x, MonoidAlgebra.mapRingHom_single, map_one, (AlgebraTools.Det.repApi (W.mat (r x.1 x.2))).2.1] at h1
  have h2 := congrArg (fun p => p.coeff k) (h1.symm.trans (hrf x.1 x.2 j).symm)
  simp only [Polynomial.coeff_map] at h2
  rw [map_sub, sub_eq_zero]
  exact h2
private theorem cd_pol {T : Type} [CommRing T] {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (x : T →+* Qbar l) (n q : ℕ)
    (a : ℕ → T) (b : ℕ → ℂ) (h : ∀ j ≤ n, ι (x (a j)) = b j) (p : (Qbar l)[X]) (hp : p.map ι.toRingHom = Hi.heckePol n q b) :
    (Hi.heckePol n q a).map x = p := by
  apply Polynomial.map_injective ι.toRingHom ι.injective
  rw [hp]
  simp only [Hi.heckePol, Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_pow, map_C, map_X]
  refine Finset.sum_congr rfl fun j hj => ?_
  simp [← h j (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj))]
set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 800000 in
theorem UpperTheory.V.Hi.coreDet_alt :
    _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → ∀ (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime] (n : ℕ) (c : Coef l) (H : HSet L Ω l n c), H.Ax →
    ∀ (A : Type) [CommRing A] [Algebra c.O A] [Alg.IsCO c.O A] (θ : H.X.I.T →* Aˣ), H.IsWt θ →
    ∀ (ι : Qbar l ≃+* ℂ) (P : Wt L l n → (H.Gq →* GL (Fin n) (Qbar l)) → Prop), H.AutomorphicHeckeSet ι P →
    ∀ lam0 ∈ H.admitted, H.DenseWt θ lam0 → ∀ (a : H.Op → c.O) (K : H.Lev) [Fact (CommOn (H.MK θ a K) (H.op A))] [Alg.IsCO c.O (H.TK θ a K)], ∃ (D : W.GDet n (H.TK θ a K) H.Gq) (ψ : ∀ v, Fin n → Dec (F := L) (H.pl v) →* (H.TK θ a K)ˣ), H.IsUniv θ a K (maximalIdeal _) D ψ := by
  intro hN L Ω _ _ _ _ _ l _ n c H hH A _ _ _ θ hθ ι P hP lam hlam hd a K _ _
  have hne : H.MK θ a K ≠ ⊥ := fun h => by
    have : Subsingleton (H.MK θ a K) := Submodule.subsingleton_iff_eq_bot.2 h
    exact zero_ne_one (α := H.TK θ a K) (Subtype.ext (Subsingleton.elim _ _))
  obtain ⟨_, -, -, -, hU, -⟩ := hiAlg L Ω l n c H hH A θ hθ a K hne
  choose u hu using fun v => cd_tel fun j => (hU v j).unit
  choose ψ hψ1 hψ2 hψ3 using fun v i =>
    cd_psi hN H hH θ hθ.cont (IsScalarTower.toAlgHom c.O A (H.TK θ a K)) v i (u v i)
  obtain ⟨D, hD, hDf⟩ := cd_glue (n := n) c (fun x => H.Good θ (x.toRingHom.comp (algebraMap A _)) lam)
    (_root_.UpperTheory.V.Hi.eq_zero_of_vanish_at_good_points_dense_weight hN L Ω l n c H hH A θ hθ ι P hP a K lam hlam hd)
    (J := {j : H.Wp × ValuationSubring Ω × G L Ω // IsPlaceOver j.2.1 j.1.1 ∧ IsFrob j.2.1 (normV j.1.1) j.2.2})
    (fun j => H.prj j.1.2.2⁻¹) (fun j => heckePol n (normV j.1.1.1) (H.genW θ a K j.1.1))
    (hH.dense.mono (by
      rintro _ ⟨w, hw, B, σ, hB, hσ, rfl⟩
      exact ⟨⟨(⟨w, hw⟩, B, σ), hB, hσ⟩, rfl⟩)) fun x hx => by
    obtain ⟨d, ξ, c0, sp, hsp⟩ := spec L Ω l n c H hH A θ hθ ι (x.comp (IsScalarTower.toAlgHom c.O A _)) lam hx.2.1
    obtain ⟨-, act, -, -, -, h4, -⟩ := _root_.UpperTheory.V.Hi.partAct0_alt hN L Ω l n c H hH A θ hθ ι P hP _ lam d ξ c0 sp hsp hlam a K _ rfl
    obtain ⟨Y, F, e, -, -, hF, hFY, hop⟩ := h4 x rfl
    refine ⟨Y.r, Y.cont, fun ⟨⟨w, B, σ⟩, hB, hσ⟩ => cd_pol ι _ n _ _ (Y.a w) (fun j hj => ?_) _ (Y.frob w B σ hB hσ)⟩
    change ι (x (H.genW θ a K w j)) = _
    rcases j with _ | j
    · rw [HSet.genW, dif_neg (by omega), map_one, map_one, Y.a_zero]
    · rw [HSet.genW, dif_pos ⟨j.succ_pos, hj⟩]
      exact smul_left_injective ℂ hF ((hop (.inl (w, ⟨j, hj⟩))).symm.trans (Y.sph w (j + 1) F hFY.1))
  refine ⟨D, ψ, hD, hψ1, fun w B σ hB hσ => hDf ⟨(w, B, σ), hB, hσ⟩, hψ2, fun v j s g hg hs => ?_⟩
  rw [Finset.prod_congr rfl fun i _ => hψ3 v i s g hg hs, hu]
  rfl
end
