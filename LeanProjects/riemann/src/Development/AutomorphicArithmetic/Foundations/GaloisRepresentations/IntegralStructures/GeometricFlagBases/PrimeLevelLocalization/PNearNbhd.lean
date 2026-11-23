import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PrimeLevelLocalization.InIdBasic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClopenKGLInvEntries
open NumberField IsDedekindDomain Matrix
open GlobalTheory.LFun (KGL)
open UpperTheory.Gal.CertificateRingHomMap (Plc GLw)
open UpperTheory.Gal.Int.Geo.Pl
open scoped Classical Topology

private lemma v_coe_algebraMap {E : Type} [Field E] [NumberField E] (w : Plc E) (c : 𝓞 E) :
    Valued.v ((algebraMap (𝓞 E) (w.adicCompletionIntegers E) c : w.adicCompletionIntegers E) : w.adicCompletion E)
      = w.intValuation c := by
  have h : ((algebraMap (𝓞 E) (w.adicCompletionIntegers E) c : w.adicCompletionIntegers E) : w.adicCompletion E)
      = algebraMap E (w.adicCompletion E) (algebraMap (𝓞 E) E c) := rfl
  rw [h]
  have := HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (K := E) w (algebraMap (𝓞 E) E c)
  rw [HeightOneSpectrum.valuation_of_algebraMap] at this
  exact this

private lemma v_le_of_inId {E : Type} [Field E] [NumberField E] (w : Plc E) (e : ℕ)
    (y : w.adicCompletion E) (h : InId w (w.asIdeal ^ e) y) : Valued.v y ≤ WithZero.exp (-(e : ℤ)) := by
  obtain ⟨z, hz, rfl⟩ := h
  refine Submodule.span_induction
    (p := fun (z : w.adicCompletionIntegers E) _ => Valued.v (z : w.adicCompletion E) ≤ WithZero.exp (-(e : ℤ)))
    ?_ ?_ ?_ ?_ (show z ∈ Submodule.span _ _ from hz)
  · rintro _ ⟨c, hc, rfl⟩
    rw [v_coe_algebraMap]
    exact (HeightOneSpectrum.intValuation_le_pow_iff_mem w c e).2 hc
  · simp
  · intro a b _ _ ha hb
    have := Valuation.map_add_le (Valued.v) ha hb
    simpa using this
  · intro a b _ hb
    have ha : Valued.v (a : w.adicCompletion E) ≤ 1 := a.2
    simp only [smul_eq_mul, MulMemClass.coe_mul, map_mul]
    exact mul_le_of_le_one_of_le ha hb

private lemma v_inv_sub_one_le {E : Type} [Field E] [NumberField E] {n : ℕ} (w : Plc E) (g : GLw n w)
    (hg : g ∈ KGL w n) (γ : WithZero (Multiplicative ℤ))
    (h : ∀ i k, Valued.v ((g.val - 1) i k) ≤ γ) (i k : Fin n) :
    Valued.v (((g⁻¹).val - 1) i k) ≤ γ := by
  have hI := ((GlobalTheory.HenQ.Basic.mem_KGL_iff w g).1 hg).2
  have e : (g⁻¹).val - 1 = -((g⁻¹).val * (g.val - 1)) := by
    rw [mul_sub, mul_one, Units.inv_mul]
    abel
  rw [e, Matrix.neg_apply, Valuation.map_neg, Matrix.mul_apply]
  refine Valuation.map_sum_le _ fun j _ => ?_
  rw [map_mul]
  exact mul_le_of_le_one_of_le (hI i j) (h j k)

private lemma tendsto_of_v_le {E : Type} [Field E] [NumberField E] (w : Plc E)
    (y : ℕ → w.adicCompletion E) (c : w.adicCompletion E)
    (h : ∀ e : ℕ, Valued.v (y e - c) ≤ WithZero.exp (-(e : ℤ))) : Filter.Tendsto y Filter.atTop (𝓝 c) := by
  rw [← tendsto_sub_nhds_zero_iff, (Valued.hasBasis_nhds_zero _ _).tendsto_right_iff]
  intro γ _
  have hne : MonoidWithZeroHom.ValueGroup₀.embedding γ.1 ≠ 0 := by simp
  have hlt : WithZero.exp (-1 : ℤ) < 1 := by
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
    norm_num
  obtain ⟨m, hm⟩ := exists_pow_lt₀ hlt (Units.mk0 _ hne)
  filter_upwards [Filter.eventually_ge_atTop m] with e he
  rw [Valuation.restrict_lt_iff_lt_embedding]
  refine lt_of_le_of_lt ((h e).trans ?_) hm
  rw [← WithZero.exp_nsmul, WithZero.exp_le_exp]
  simpa using he

private lemma tendsto_mat_of_v_le {E : Type} [Field E] [NumberField E] {n : ℕ} (w : Plc E)
    (M : ℕ → Matrix (Fin n) (Fin n) (w.adicCompletion E))
    (h : ∀ (e : ℕ) i k, Valued.v ((M e - 1) i k) ≤ WithZero.exp (-(e : ℤ))) :
    Filter.Tendsto M Filter.atTop (𝓝 1) := by
  refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun k => ?_
  exact tendsto_of_v_le w _ _ fun e => h e i k

theorem UpperTheory.Gal.Int.Geo.Pl.nearNbhd_holds :
    UpperTheory.Gal.Int.Geo.Pl.NearNbhd := by
  intro E _ _ n w O hO h1
  by_contra hcon
  push_neg at hcon
  choose e' he g hgK hN hgO using hcon
  have hv : ∀ (e : ℕ) i k, Valued.v (((g e).val - 1) i k) ≤ WithZero.exp (-(e : ℤ)) := by
    intro e i k
    refine (v_le_of_inId w (e' e) _ (hN e i k)).trans ?_
    rw [WithZero.exp_le_exp]
    have := he e
    omega
  have ha : Filter.Tendsto (fun e => (g e).val) Filter.atTop (𝓝 1) := tendsto_mat_of_v_le w _ hv
  have hb : Filter.Tendsto (fun e => ((g e)⁻¹).val) Filter.atTop (𝓝 1) :=
    tendsto_mat_of_v_le w _ fun e => v_inv_sub_one_le w (g e) (hgK e) _ (hv e)
  have ht : Filter.Tendsto g Filter.atTop (𝓝 1) := by
    rw [Units.isEmbedding_embedProduct.tendsto_nhds_iff]
    exact ha.prodMk_nhds ((MulOpposite.continuous_op.tendsto _).comp hb)
  obtain ⟨e, hE⟩ := (ht.eventually (hO.mem_nhds h1)).exists
  exact hgO e hE
