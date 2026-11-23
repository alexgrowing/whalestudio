import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsHalfPtIff
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LatticeInvariantsPeriodPairDictionary
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LatticeCovolumePosAndSelfDual

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric NumberField

namespace GlobalTheory.Mem.Per.Model

theorem eisG_map (Λ : AddSubgroup ℂ) (δ : ℂ) (hδ : δ ≠ 0) (k : ℕ) :
    eisG (Λ.map (AddMonoidHom.mulLeft δ)) k = (δ ^ (2 * k))⁻¹ * eisG Λ k := by
  unfold eisG
  rw [← tsum_mul_left]
  let f : {w : ℂ // w ∈ Λ ∧ w ≠ 0} → {w : ℂ // w ∈ Λ.map (AddMonoidHom.mulLeft δ) ∧ w ≠ 0} :=
    fun w => ⟨δ * w.1, ⟨w.1, w.2.1, rfl⟩, mul_ne_zero hδ w.2.2⟩
  have hf : Function.Bijective f := by
    constructor
    · intro a b h
      exact Subtype.ext (mul_left_cancel₀ hδ (congrArg Subtype.val h))
    · rintro ⟨w, ⟨v, hv, rfl⟩, h0⟩
      refine ⟨⟨v, hv, ?_⟩, rfl⟩
      rintro rfl
      simp at h0
  rw [← (Equiv.ofBijective f hf).tsum_eq]
  refine tsum_congr fun w => ?_
  simp [f, mul_pow, mul_comm]

theorem discr_map (Λ : AddSubgroup ℂ) (δ : ℂ) (hδ : δ ≠ 0) :
    TaylorLogMetric.discr (Λ.map (AddMonoidHom.mulLeft δ)) = (δ ^ 12)⁻¹ * TaylorLogMetric.discr Λ := by
  unfold TaylorLogMetric.discr g2 g3
  rw [eisG_map _ _ hδ, eisG_map _ _ hδ]
  field_simp
  ring

theorem jLat_map (Λ : AddSubgroup ℂ) (δ : ℂ) (hδ : δ ≠ 0) :
    jLat (Λ.map (AddMonoidHom.mulLeft δ)) = jLat Λ := by
  unfold jLat
  rw [discr_map _ _ hδ]
  unfold g2
  rw [eisG_map _ _ hδ]
  by_cases h : TaylorLogMetric.discr Λ = 0
  · simp [h]
  · field_simp
    ring

variable {LL : Type} [Field LL] [NumberField LL]

theorem exists_isConjLat_self (emb : LL →+* ℂ) (Λ : AddSubgroup ℂ) (h : TaylorLogMetric.discr Λ ≠ 0)
    (ha : ∃ a : LL, emb a = jLat Λ) : ∃ Λ', IsConjLat emb emb Λ Λ' := by
  obtain ⟨δ, hδ⟩ := IsAlgClosed.exists_pow_nat_eq (TaylorLogMetric.discr Λ) (n := 12) (by norm_num)
  have h0 : δ ≠ 0 := by rintro rfl; apply h; rw [← hδ]; simp
  obtain ⟨a, ha⟩ := ha
  refine ⟨Λ.map (AddMonoidHom.mulLeft δ), ?_, a, ha, ?_⟩
  · rw [discr_map _ _ h0, hδ, inv_mul_cancel₀ h]
  · rw [jLat_map _ _ h0, ha]

theorem eisG_eq_zero_of_infinite (Λ : AddSubgroup ℂ) (h : {w : ℂ | w ∈ Λ ∧ w ≠ 0 ∧ ‖w‖ ≤ 1}.Infinite) (k : ℕ) :
    eisG Λ k = 0 := by
  unfold eisG
  apply tsum_eq_zero_of_not_summable
  intro hs
  have ht := hs.tendsto_cofinite_zero
  have he := (Metric.tendsto_nhds.1 ht) 1 one_pos
  rw [Filter.eventually_cofinite] at he
  apply h
  refine (he.image Subtype.val).subset ?_
  rintro w ⟨h1, h2, h3⟩
  refine ⟨⟨w, h1, h2⟩, ?_, rfl⟩
  simp only [Set.mem_setOf_eq, dist_zero_right, not_lt, norm_div, norm_one, norm_pow]
  have hp : 0 < ‖w‖ ^ (2 * k) := pow_pos (norm_pos_iff.2 h2) _
  rw [le_div_iff₀ hp, one_mul]
  exact pow_le_one₀ (norm_nonneg _) h3

theorem finite_of_isConjLat {emb s : LL →+* ℂ} {Λ Λ' : AddSubgroup ℂ} (h : IsConjLat emb s Λ Λ') :
    {w : ℂ | w ∈ Λ' ∧ w ≠ 0 ∧ ‖w‖ ≤ 1}.Finite := by
  by_contra hi
  have := h.1
  unfold TaylorLogMetric.discr g2 g3 at this
  rw [eisG_eq_zero_of_infinite _ hi, eisG_eq_zero_of_infinite _ hi] at this
  norm_num at this

theorem ne_bot_of_isConjLat {emb s : LL →+* ℂ} {Λ Λ' : AddSubgroup ℂ} (h : IsConjLat emb s Λ Λ') : Λ' ≠ ⊥ := by
  rintro rfl
  have := h.1
  haveI : IsEmpty {w : ℂ // w ∈ (⊥ : AddSubgroup ℂ) ∧ w ≠ 0} := ⟨fun w => w.2.2 (AddSubgroup.mem_bot.1 w.2.1)⟩
  unfold TaylorLogMetric.discr g2 g3 eisG at *
  rw [tsum_empty, tsum_empty] at *
  norm_num at *

variable {R : Ranks} (H : Host R)

theorem ellLat_ne_bot (embE : H.E →+* LL) (g : R.GG) : ellLat H embE g ≠ ⊥ := by
  have hd : differentIdeal (𝓞 H.K) (𝓞 H.E) ≠ ⊥ := differentIdeal_ne_bot
  have hb : H.𝔟 ≠ ⊥ := by
    intro h0
    apply hd
    have := H.𝔟_spec.1
    rw [h0, Ideal.bot_mul] at this
    exact this
  have hA : H.AA0 ≠ 0 := by
    unfold Host.AA0
    exact inv_ne_zero (FractionalIdeal.coeIdeal_ne_zero.2 hb)
  obtain ⟨a, ha0, ha⟩ := FractionalIdeal.exists_ne_zero_mem_isInteger hA |>.imp fun a h => h
  obtain ⟨b, hb1, hb0⟩ := (Submodule.ne_bot_iff _).1 hd
  intro h
  have : embE (H.sigmaOf g ((a : H.E) * (b : H.E))) ∈ ellLat H embE g :=
    Submodule.subset_span ⟨_, ha, b, hb1, rfl⟩
  rw [h, Submodule.mem_bot] at this
  simp [ha0, hb0] at this

theorem ne_zero_of_isGen {embE : H.E →+* LL} {g : R.GG} {x : LL} (h : IsGen H embE g x) : x ≠ 0 := by
  rintro rfl
  apply ellLat_ne_bot H embE g
  rw [← h]; simp

theorem gen_spec {emb : LL →+* ℂ} {embE : H.E →+* LL} (h : FieldOK H emb embE) (g) :
    IsGen H embE g (gen H embE g) := Classical.epsilon_spec (h.2 g)

theorem prod_norm_eq_of_isGen {embE : H.E →+* LL} {g : R.GG} {x y : LL}
    (hx : IsGen H embE g x) (hy : IsGen H embE g y) :
    ∏ s : LL →+* ℂ, ‖s x‖ = ∏ s : LL →+* ℂ, ‖s y‖ := by
  have h : Submodule.span (𝓞 LL) {x} = Submodule.span (𝓞 LL) {y} := hx.trans hy.symm
  obtain ⟨u, hu⟩ := Submodule.span_singleton_eq_span_singleton.1 h
  have hu1 : ∏ s : LL →+* ℂ, ‖s ((u : 𝓞 LL) : LL)‖ = 1 := by
    rw [Fintype.prod_equiv (RingHom.equivRatAlgHom LL ℂ) (fun f => ‖f ((u : 𝓞 LL) : LL)‖)
      (fun φ => ‖φ ((u : 𝓞 LL) : LL)‖) (fun _ => rfl), ← norm_prod, ← Algebra.norm_eq_prod_embeddings ℚ ℂ]
    have := NumberField.Units.norm LL u
    simp only [eq_ratCast, Complex.norm_ratCast]
    exact_mod_cast this
  rw [← hu]
  simp only [Units.smul_def, Algebra.smul_def, map_mul, norm_mul, Finset.prod_mul_distrib]
  rw [show (∏ s : LL →+* ℂ, ‖s (algebraMap (𝓞 LL) LL u)‖) = 1 from hu1, one_mul]

theorem area_pos_of_isConjLat {emb s : LL →+* ℂ} {Λ Λ' : AddSubgroup ℂ} (h : IsConjLat emb s Λ Λ') :
    (∃ L : PeriodPair, ∀ z, z ∈ Λ' ↔ z ∈ L.lattice) ∧ 0 < area Λ' := by
  obtain ⟨L, hL⟩ := GlobalTheory.LatticeInvariants.exists_periodPair_of_discr_ne_zero (Λ := Λ') (by rw [h.1]; exact one_ne_zero)
  exact ⟨⟨L, hL⟩, (GlobalTheory.PlaneLattice.area_pos_and_selfDual L Λ' hL).1⟩

theorem exists_isConjLat (emb s : LL →+* ℂ) (Λ : AddSubgroup ℂ) (ha : ∃ a : LL, emb a = jLat Λ) :
    ∃ Λ', IsConjLat emb s Λ Λ' := by
  obtain ⟨a, ha⟩ := ha
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq (s a / 1728) (n := 3) (by norm_num)
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_pow_nat_eq ((s a / 1728 - 1) / 27) (n := 2) (by norm_num)
  have h1 : x ^ 3 - 27 * y ^ 2 = 1 := by rw [hx, hy]; ring
  obtain ⟨L, h2, h3⟩ := GlobalTheory.LatticeInvariants.exists_periodPair_of_invariants (a := x) (b := y)
    (by rw [h1]; exact one_ne_zero)
  have hd := GlobalTheory.LatticeInvariants.invariants_dictionary L L.lattice.toAddSubgroup (fun _ => Iff.rfl)
  have hD : TaylorLogMetric.discr L.lattice.toAddSubgroup = 1 := by
    unfold TaylorLogMetric.discr; rw [hd.1, hd.2.1, h2, h3, h1]
  refine ⟨L.lattice.toAddSubgroup, hD, a, ha, ?_⟩
  unfold jLat
  rw [hD, hd.1, h2, hx]; ring

theorem conjLat_spec {emb : LL →+* ℂ} {embE : H.E →+* LL} (h : FieldOK H emb embE) (s : LL →+* ℂ) :
    IsConjLat emb s (baseLat H) (conjLat H emb s) :=
  Classical.epsilon_spec (exists_isConjLat emb s _ h.1)

theorem om_eq {emb : LL →+* ℂ} {embE : H.E →+* LL} (h : FieldOK H emb embE) {I : Type}
    (e : I ≃ R.Psi) (τ : I) (s : LL →+* ℂ) :
    (trueGx H emb embE e).Om τ s = area (conjLat H emb s) / (Real.pi * ‖s (gen H embE (e τ).1)‖ ^ 2) := by
  have h1 := (area_pos_of_isConjLat (conjLat_spec H h s)).2
  have h2 : s (gen H embE (e τ).1) ≠ 0 := (map_ne_zero s).2 (ne_zero_of_isGen H (gen_spec H h _))
  have h3 : 0 < omAt H emb s (gen H embE (e τ).1) := by
    unfold omAt
    have := norm_pos_iff.2 h2
    have := Real.pi_pos
    positivity
  show posOr1 _ = _
  unfold posOr1
  rw [if_pos h3]; rfl

end GlobalTheory.Mem.Per.Model
