import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RedMFrMapAdjZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjugatePlacesProductIdealProperOddCoprime
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NeZeroOfIsIdemAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdempotentSumAuxiliaryPlaces
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

noncomputable section

namespace GlobalTheory.ConjCompl

def clos (D : D7) (I : Ideal (𝓞 D.host.E)) : AddSubgroup (Af D.host.F ⊗[D.host.F] D.host.E) :=
  AddSubgroup.closure {y | ∃ a ∈ intAf D.host.F, ∃ x : 𝓞 D.host.E, x ∈ I ∧ y = a ⊗ₜ[D.host.F] (x : D.host.E)}

theorem intAf_mul' {F : Type} [Field F] [NumberField F] {a b : Af F} (ha : a ∈ intAf F) (hb : b ∈ intAf F) :
    a * b ∈ intAf F := fun v => by
  rw [map_mul]; exact mul_mem (ha v) (hb v)

theorem one_mem_intAf' {F : Type} [Field F] [NumberField F] : (1 : Af F) ∈ intAf F := fun v => by
  rw [map_one]; exact one_mem _

variable {D : D7}

theorem tmul_mem_clos {I : Ideal (𝓞 D.host.E)} {a : Af D.host.F} (ha : a ∈ intAf D.host.F) {x : 𝓞 D.host.E}
    (hx : x ∈ I) : a ⊗ₜ[D.host.F] (x : D.host.E) ∈ clos D I :=
  AddSubgroup.subset_closure ⟨a, ha, x, hx, rfl⟩

theorem mul_mem_clos {I J : Ideal (𝓞 D.host.E)} {y z : Af D.host.F ⊗[D.host.F] D.host.E}
    (hy : y ∈ clos D I) (hz : z ∈ clos D J) : y * z ∈ clos D (I * J) := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨b, hb, x', hx', rfl⟩ := hz
    induction hy using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨a, ha, x, hx, rfl⟩ := hy
      rw [Algebra.TensorProduct.tmul_mul_tmul]
      have e : (x : D.host.E) * (x' : D.host.E) = ((x * x' : 𝓞 D.host.E) : D.host.E) := rfl
      rw [e]
      exact tmul_mem_clos (intAf_mul' ha hb) (Ideal.mul_mem_mul hx hx')
    | zero => rw [zero_mul]; exact zero_mem _
    | add _ _ _ _ h1 h2 => rw [add_mul]; exact add_mem h1 h2
    | neg _ _ h => rw [neg_mul]; exact neg_mem h
  | zero => rw [mul_zero]; exact zero_mem _
  | add _ _ _ _ h1 h2 => rw [mul_add]; exact add_mem h1 h2
  | neg _ _ h => rw [mul_neg]; exact neg_mem h

theorem intAE_eq_clos : intAE D = clos D ⊤ := by
  unfold intAE clos
  congr 1
  ext y
  simp only [Set.mem_setOf_eq, Submodule.mem_top, true_and]

theorem one_mem_clos : (1 : Af D.host.F ⊗[D.host.F] D.host.E) ∈ clos D ⊤ := by
  have h := tmul_mem_clos (D := D) (I := ⊤) one_mem_intAf' (Submodule.mem_top (x := (1 : 𝓞 D.host.E)))
  have e : ((1 : 𝓞 D.host.E) : D.host.E) = 1 := rfl
  rwa [e, ← Algebra.TensorProduct.one_def] at h

theorem prod_mem_clos {ι : Type} (s : Finset ι) (f : ι → Af D.host.F ⊗[D.host.F] D.host.E)
    (I : ι → Ideal (𝓞 D.host.E)) (h : ∀ i ∈ s, f i ∈ clos D (I i)) : ∏ i ∈ s, f i ∈ clos D (∏ i ∈ s, I i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.prod_empty, Finset.prod_empty, Ideal.one_eq_top]; exact one_mem_clos
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    exact mul_mem_clos (h a (Finset.mem_insert_self _ _)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem prod_one_sub {A ι : Type} [CommRing A] (c : ι → A) (s : Finset ι)
    (h : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → c i * c j = 0) : ∏ i ∈ s, (1 - c i) = 1 - ∑ i ∈ s, c i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      ih fun i hi j hj hij => h i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj) hij]
    have h0 : c a * ∑ i ∈ s, c i = 0 := by
      rw [Finset.mul_sum]
      exact Finset.sum_eq_zero fun j hj =>
        h a (Finset.mem_insert_self _ _) j (Finset.mem_insert_of_mem hj) (fun e => ha (e ▸ hj))
    linear_combination h0

theorem exists_pow_eq_span' {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    ∃ (n : ℕ) (s : 𝓞 F), 0 < n ∧ v.asIdeal ^ n = Ideal.span {s} := by
  classical
  have hv : v.asIdeal ∈ nonZeroDivisors (Ideal (𝓞 F)) := mem_nonZeroDivisors_of_ne_zero v.ne_bot
  set n := Fintype.card (ClassGroup (𝓞 F)) with hn
  have hvn : v.asIdeal ^ n ∈ nonZeroDivisors (Ideal (𝓞 F)) := pow_mem hv n
  have e : (⟨v.asIdeal ^ n, hvn⟩ : nonZeroDivisors (Ideal (𝓞 F))) = ⟨v.asIdeal, hv⟩ ^ n := Subtype.ext (by simp)
  have h1 : ClassGroup.mk0 ⟨v.asIdeal ^ n, hvn⟩ = 1 := by
    rw [e, map_pow]
    exact pow_card_eq_one
  obtain ⟨s, hs⟩ := ((ClassGroup.mk0_eq_one_iff hvn).1 h1).principal
  exact ⟨n, s, Fintype.card_pos, hs⟩

theorem finPart_es_mem {es : AE D} {PP : Formalism.L2.DIV.Pl D.host.E} (h : Formalism.L2.NTheta.IsIdemAt es PP)
    (hne : conjI PP.asIdeal ≠ PP.asIdeal) : finPart D es ∈ clos D (conjI PP.asIdeal) := by
  have hmax : (conjI PP.asIdeal).IsMaximal := by
    rw [GlobalTheory.LiftIdeal.conjI_eq_map D]; exact GlobalTheory.LiftIdeal.isMaximal_map D PP
  obtain ⟨s, hs, hsP⟩ : ∃ s ∈ conjI PP.asIdeal, s ∉ PP.asIdeal := by
    by_contra hc
    push_neg at hc
    exact hne (hmax.eq_of_le PP.isPrime.ne_top hc)
  have hs0 : s ≠ 0 := fun e => hsP (e ▸ PP.asIdeal.zero_mem)
  have hsE : (s : D.host.E) ≠ 0 := fun e => hs0 (RingOfIntegers.coe_eq_zero_iff.1 e)
  have hint : finPart D (es * incA D ((s : D.host.E))⁻¹) ∈ intAE D := by
    by_contra hc
    exact hsP ((h.2 s hs0).2 hc)
  rw [intAE_eq_clos] at hint
  have e1 : es = es * incA D ((s : D.host.E))⁻¹ * incA D (s : D.host.E) := by
    rw [mul_assoc, ← map_mul, inv_mul_cancel₀ hsE, map_one, mul_one]
  have hgen : finPart D (incA D (s : D.host.E)) ∈ clos D (conjI PP.asIdeal) := by
    have e2 : finPart D (incA D (s : D.host.E)) = (1 : Af D.host.F) ⊗ₜ[D.host.F] (s : D.host.E) := by
      show Algebra.TensorProduct.map _ _ ((1 : AF D.host.F) ⊗ₜ[D.host.F] (s : D.host.E)) = _
      rw [Algebra.TensorProduct.map_tmul, map_one]; rfl
    rw [e2]; exact tmul_mem_clos one_mem_intAf' hs
  rw [e1, map_mul]
  have h3 := mul_mem_clos hint hgen
  rwa [Ideal.top_mul] at h3

theorem one_sub_mem {PP : Formalism.L2.DIV.Pl D.host.E} {v : HeightOneSpectrum (𝓞 D.host.F)}
    (hv : PP.asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) = v.asIdeal) {α : Af D.host.F}
    (h1 : evalV D.host.F v α = 1) (h0 : ∀ w, w ≠ v → evalV D.host.F w α = 0) :
    (1 - α) ⊗ₜ[D.host.F] (1 : D.host.E) ∈ clos D (conjI PP.asIdeal) := by
  obtain ⟨n, t, hn, ht⟩ := exists_pow_eq_span' v
  have htv : t ∈ v.asIdeal := Ideal.pow_le_self hn.ne' (ht ▸ Ideal.mem_span_singleton_self t)
  have htw : ∀ w : HeightOneSpectrum (𝓞 D.host.F), w ≠ v → t ∉ w.asIdeal := fun w hw h => by
    have h2 : v.asIdeal ^ n ≤ w.asIdeal := by rw [ht, Ideal.span_le, Set.singleton_subset_iff]; exact h
    exact hw (HeightOneSpectrum.ext (v.isMaximal.eq_of_le w.isPrime.ne_top (w.isPrime.le_of_pow_le h2))).symm
  have ht0 : (t : D.host.F) ≠ 0 := by
    intro h0'
    have : t = 0 := by exact_mod_cast h0'
    subst this
    rw [Ideal.span_singleton_eq_bot.2 rfl] at ht
    exact v.ne_bot ((pow_eq_zero_iff hn.ne').1 ht)
  set a : Af D.host.F := algebraMap D.host.F (Af D.host.F) (t : D.host.F)⁻¹ * (1 - α) with ha_def
  have ha : a ∈ intAf D.host.F := by
    intro w
    rw [ha_def, map_mul, AlgHom.commutes, map_sub, map_one]
    by_cases hw : w = v
    · subst hw; rw [h1, sub_self, mul_zero]; exact zero_mem _
    · rw [h0 w hw, sub_zero, mul_one, HeightOneSpectrum.mem_adicCompletionIntegers]
      change Valued.v (((((t : D.host.F))⁻¹ : D.host.F) : HeightOneSpectrum.adicCompletion D.host.F w)) ≤ 1
      rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', map_inv₀,
        show ((t : D.host.F)) = algebraMap (𝓞 D.host.F) D.host.F t from rfl,
        (HeightOneSpectrum.valuation_eq_one_iff_notMem w).2 (htw w hw), inv_one]
  have ecoe : ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) t : 𝓞 D.host.E) : D.host.E) =
      algebraMap D.host.F D.host.E (t : D.host.F) := rfl
  have hx : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) t ∈ conjI PP.asIdeal := by
    apply Ideal.subset_span
    refine ⟨algebraMap (𝓞 D.host.F) (𝓞 D.host.E) t, ?_, ?_⟩
    · rw [← Ideal.mem_comap, hv]; exact htv
    · rw [ecoe]
      simp [ReciprocityTheory.ChartRestriction.G.FD.cc]
  have h3 := tmul_mem_clos ha hx
  have e : a ⊗ₜ[D.host.F] ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) t : 𝓞 D.host.E) : D.host.E) =
      (1 - α) ⊗ₜ[D.host.F] (1 : D.host.E) := by
    rw [ecoe, Algebra.algebraMap_eq_smul_one, ← TensorProduct.smul_tmul, Algebra.smul_def, ha_def, ← mul_assoc,
      ← map_mul, mul_inv_cancel₀ ht0, map_one, one_mul]
  rwa [e] at h3

theorem finPart_one_sub_cA_mem {es : AE D} {PP : Formalism.L2.DIV.Pl D.host.E} (h : Formalism.L2.NTheta.IsIdemAt es PP)
    (hne : conjI PP.asIdeal ≠ PP.asIdeal) : finPart D (1 - cA D es) ∈ clos D (conjI PP.asIdeal) := by
  obtain ⟨-, -, v, ε, hε, h3⟩ := h.1
  have hsplit := GlobalTheory.LevelPlaces.splitAt_of h.1 hε h3
  obtain ⟨Q, hQ, hQv⟩ := GlobalTheory.IdemPrime.exists_isIdemAt D v es hsplit
  have hQP : Q = PP := GlobalTheory.PlaceVec.isIdemAt_inj hQ h
  subst hQP
  obtain ⟨α, rfl, hα1, hα0⟩ := hε
  have e1 : 1 - cA D es = es + (1 - algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α)) := by
    rw [← h3]; ring
  have e2 : finPart D (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α)) = α ⊗ₜ[D.host.F] (1 : D.host.E) := rfl
  rw [e1, map_add, map_sub, map_one, e2, Algebra.TensorProduct.one_def, ← TensorProduct.sub_tmul]
  exact add_mem (finPart_es_mem h hne) (one_sub_mem hQv hα1 hα0)

theorem offConj : ∀ (D : D7) (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (e : AE D), IsIdemSum e (Pg ∪ Q) →
    finPart D (1 - cA D e) ∈ AddSubgroup.closure {y | ∃ a ∈ intAf D.host.F, ∃ x : 𝓞 D.host.E,
      x ∈ GlobalTheory.LiftLevel.liftI Pg Q ∧ y = a ⊗ₜ[D.host.F] (x : D.host.E)} := by
  intro D Pg Q e he
  have he' := he
  obtain ⟨⟨es, hes, rfl⟩, h0⟩ := he
  have hz : ∀ i ∈ Pg ∪ Q, ∀ j ∈ Pg ∪ Q, es i * cA D (es j) = 0 := by
    have hsum : ∑ x ∈ (Pg ∪ Q) ×ˢ (Pg ∪ Q), es x.1 * cA D (es x.2) = 0 := by
      rw [Finset.sum_product, ← h0, map_sum, Finset.sum_mul_sum]
    have hall := GlobalTheory.PlaceVec.idem_eq_zero_of_sum (A := AE D) GlobalTheory.PlaceVec.natCast_mul_eq_zero
      (fun x : Formalism.L2.DIV.Pl D.host.E × Formalism.L2.DIV.Pl D.host.E => es x.1 * cA D (es x.2)) ((Pg ∪ Q) ×ˢ (Pg ∪ Q))
      (fun x hx => by
        obtain ⟨h1, h2⟩ := Finset.mem_product.1 hx
        show es x.1 * cA D (es x.2) * (es x.1 * cA D (es x.2)) = es x.1 * cA D (es x.2)
        rw [mul_mul_mul_comm, ← map_mul, (hes _ h1).1.1, (hes _ h2).1.1]) hsum
    exact fun i hi j hj => hall (i, j) (Finset.mem_product.2 ⟨hi, hj⟩)
  have horth : ∀ i ∈ Pg ∪ Q, ∀ j ∈ Pg ∪ Q, i ≠ j → cA D (es i) * cA D (es j) = 0 := by
    intro i hi j hj hij
    rcases GlobalTheory.PlaceVec.splitIdem_eq_or (hes i hi).1 (hes j hj).1 (hz i hi j hj) (hz j hj i hi) with e | e
    · exact absurd (GlobalTheory.PlaceVec.isIdemAt_inj (hes i hi) (by rw [e]; exact hes j hj)) hij
    · rw [← map_mul, e, map_zero]
  show finPart D _ ∈ clos D (GlobalTheory.LiftLevel.liftI Pg Q)
  rw [map_sum, ← prod_one_sub _ _ horth, map_prod]
  exact prod_mem_clos (Pg ∪ Q) _ (fun PP => conjI PP.asIdeal) fun PP hP =>
    finPart_one_sub_cA_mem (hes PP hP) (by rw [GlobalTheory.LiftIdeal.conjI_eq_map D]; exact GlobalTheory.LiftIdeal.map_ne he' hP hP)

end GlobalTheory.ConjCompl

end
