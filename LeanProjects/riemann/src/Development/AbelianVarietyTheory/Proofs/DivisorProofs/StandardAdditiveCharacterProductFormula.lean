import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSelfDualFor
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.WeylFour
open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.AdeleCharProd

variable {F : Type} [Field F] [NumberField F]

lemma isOpen_intV (v : HeightOneSpectrum (𝓞 F)) :
    IsOpen (HeightOneSpectrum.adicCompletionIntegers F v : Set (HeightOneSpectrum.adicCompletion F v)) :=
  Valued.isOpen_valuationSubring _

def ofInt (q : ∀ v : HeightOneSpectrum (𝓞 F), HeightOneSpectrum.adicCompletionIntegers F v) : Af F :=
  RestrictedProduct.structureMap _ _ _ q

lemma continuous_ofInt : Continuous (ofInt (F := F)) :=
  (RestrictedProduct.isOpenEmbedding_structureMap (fun v => isOpen_intV (F := F) v)).continuous

lemma ofInt_add (p q : ∀ v : HeightOneSpectrum (𝓞 F), HeightOneSpectrum.adicCompletionIntegers F v) :
    ofInt (p + q) = ofInt p + ofInt q := by
  apply RestrictedProduct.ext; intro w; rfl

open Classical in
lemma ofInt_single (v : HeightOneSpectrum (𝓞 F)) (t : HeightOneSpectrum.adicCompletionIntegers F v) :
    ofInt (Pi.single v t) = singleFin v (t : Fv F v) := by
  apply RestrictedProduct.ext; intro w
  by_cases h : w = v
  · subst h
    show ((Pi.single w t : ∀ v : HeightOneSpectrum (𝓞 F), HeightOneSpectrum.adicCompletionIntegers F v) w : Fv F w) = _
    rw [Pi.single_eq_same]
    exact (RestrictedProduct.single_eq_same _ w (t : Fv F w)).symm
  · show ((Pi.single v t : ∀ v : HeightOneSpectrum (𝓞 F), HeightOneSpectrum.adicCompletionIntegers F v) w : Fv F w) = _
    rw [Pi.single_eq_of_ne h]
    exact (RestrictedProduct.single_eq_of_ne _ (t : Fv F v) h).symm

end GlobalTheory.AdeleCharProd

namespace GlobalTheory.AdeleCharProd

variable {F : Type} [Field F] [NumberField F]

lemma psiLoc_int {ψ : AddChar (AF F) ℂ} {v : Pl F} (hv : PsiUnr ψ v) {t : Fv F v}
    (ht : t ∈ HeightOneSpectrum.adicCompletionIntegers F v) : psiLoc ψ v t = 1 := by
  have := ((hv 1).2 (one_mem _)) t ht
  simpa using this

open Classical in
lemma psi_ofInt_single (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F))
    (t : HeightOneSpectrum.adicCompletionIntegers F v) (h : PsiUnr ψ v ∨ t = 0) :
    ψ (LinearMap.inr F (Ainf F) (Af F) (ofInt (Pi.single v t))) = 1 := by
  classical
  rw [ofInt_single]
  rcases h with h | h
  · exact psiLoc_int h t.2
  · subst h
    have h0 : (LinearMap.inr F (Ainf F) (Af F)) ((singleFin v) ((0 : HeightOneSpectrum.adicCompletionIntegers F v) : Fv F v)) = (0 : AF F) := by
      simp; rfl
    rw [h0]; exact AddChar.map_zero_eq_one ψ

open Classical in

lemma psi_ofInt (ψ : AddChar (AF F) ℂ) (hc : Continuous ψ)
    (q : ∀ v : HeightOneSpectrum (𝓞 F), HeightOneSpectrum.adicCompletionIntegers F v)
    (hq : ∀ v, PsiUnr ψ v ∨ q v = 0) :
    ψ (LinearMap.inr F (Ainf F) (Af F) (ofInt q)) = 1 := by
  set g : (∀ v : HeightOneSpectrum (𝓞 F), HeightOneSpectrum.adicCompletionIntegers F v) → ℂ :=
    fun p => ψ (LinearMap.inr F (Ainf F) (Af F) (ofInt p)) with hg
  have gc : Continuous g := by
    refine hc.comp ?_
    refine Continuous.comp ?_ continuous_ofInt
    exact (continuous_const.prodMk continuous_id)
  let tr : Finset (HeightOneSpectrum (𝓞 F)) → ∀ v : HeightOneSpectrum (𝓞 F), HeightOneSpectrum.adicCompletionIntegers F v :=
    fun T => ∑ v ∈ T, Pi.single v (q v)
  have htr : Tendsto tr atTop (𝓝 q) := by
    rw [tendsto_pi_nhds]; intro w
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop {w}] with T hT
    have hw : w ∈ T := hT (Finset.mem_singleton_self w)
    simp only [tr, Finset.sum_apply]
    rw [Finset.sum_eq_single w]
    · simp
    · intro b _ hb; simp [Pi.single_eq_of_ne' hb]
    · intro h; exact absurd hw h
  have h1 : ∀ T, g (tr T) = 1 := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
      have h0 : ofInt (F := F) 0 = 0 := by apply RestrictedProduct.ext; intro w; rfl
      simp only [g, tr, Finset.sum_empty, h0, map_zero]; exact AddChar.map_zero_eq_one ψ
    | insert a T ha ih =>
      have hmul : ∀ p p', g (p + p') = g p * g p' := by
        intro p p'; simp only [g, ofInt_add, map_add]; exact AddChar.map_add_eq_mul _ _ _
      have e : tr (insert a T) = Pi.single a (q a) + tr T := by simp only [tr, Finset.sum_insert ha]
      rw [e, hmul, ih, mul_one]; exact psi_ofInt_single ψ a (q a) (hq a)
  have := gc.continuousAt.tendsto.comp htr
  have h2 : Tendsto (g ∘ tr) atTop (𝓝 1) := by
    simp only [Function.comp_def, h1]; exact tendsto_const_nhds
  exact tendsto_nhds_unique this h2

end GlobalTheory.AdeleCharProd

namespace GlobalTheory.AdeleCharProd

variable {F : Type} [Field F] [NumberField F]

open Classical in

lemma finite_decomp (ψ : AddChar (AF F) ℂ) (hunr : ∀ᶠ v in cofinite, PsiUnr ψ v) (x : Af F) :
    ∃ (S : Finset (HeightOneSpectrum (𝓞 F)))
      (q : ∀ v : HeightOneSpectrum (𝓞 F), HeightOneSpectrum.adicCompletionIntegers F v),
      (∀ v, PsiUnr ψ v ∨ q v = 0) ∧ (∀ v ∉ S, PsiUnr ψ v ∧ x v ∈ HeightOneSpectrum.adicCompletionIntegers F v) ∧
      x = ofInt q + ∑ v ∈ S, singleFin v (x v) := by
  have hev : ∀ᶠ v in cofinite, PsiUnr ψ v ∧ x v ∈ HeightOneSpectrum.adicCompletionIntegers F v :=
    hunr.and x.2
  have hS := Filter.eventually_cofinite.1 hev
  refine ⟨hS.toFinset, fun v => if h : PsiUnr ψ v ∧ x v ∈ HeightOneSpectrum.adicCompletionIntegers F v
    then ⟨x v, h.2⟩ else 0, ?_, ?_, ?_⟩
  · intro v
    by_cases h : PsiUnr ψ v ∧ x v ∈ HeightOneSpectrum.adicCompletionIntegers F v
    · exact Or.inl h.1
    · exact Or.inr (dif_neg h)
  · intro v hv
    by_contra h
    exact hv (hS.mem_toFinset.2 h)
  · apply RestrictedProduct.ext; intro w
    show evalV F w x = evalV F w (_ + _)
    rw [map_add, map_sum]
    have hsame : ∀ (t : Fv F w), evalV F w (singleFin w t) = t := fun t =>
      RestrictedProduct.single_eq_same (fun v => HeightOneSpectrum.adicCompletionIntegers F v) w t
    have hne : ∀ v (t : Fv F v), v ≠ w → evalV F w (singleFin v t) = 0 := fun v t h =>
      RestrictedProduct.single_eq_of_ne (fun v => HeightOneSpectrum.adicCompletionIntegers F v) t (Ne.symm h)
    by_cases hw : PsiUnr ψ w ∧ x w ∈ HeightOneSpectrum.adicCompletionIntegers F w
    · have hwS : w ∉ hS.toFinset := fun h => (hS.mem_toFinset.1 h) hw
      rw [Finset.sum_eq_zero]
      · show x w = ((if h : PsiUnr ψ w ∧ x w ∈ HeightOneSpectrum.adicCompletionIntegers F w
          then (⟨x w, h.2⟩ : HeightOneSpectrum.adicCompletionIntegers F w) else 0 : _) : Fv F w) + 0
        rw [dif_pos hw, add_zero]
      · intro v hv
        apply hne
        rintro rfl; exact hwS hv
    · have hwS : w ∈ hS.toFinset := hS.mem_toFinset.2 hw
      rw [Finset.sum_eq_single w]
      · rw [hsame]
        show x w = ((if h : PsiUnr ψ w ∧ x w ∈ HeightOneSpectrum.adicCompletionIntegers F w
          then (⟨x w, h.2⟩ : HeightOneSpectrum.adicCompletionIntegers F w) else 0 : _) : Fv F w) + x w
        rw [dif_neg hw]; simp
      · intro v _ hv; exact hne v _ hv
      · intro h; exact absurd hwS h

end GlobalTheory.AdeleCharProd

namespace GlobalTheory.AdeleCharProd

variable {F : Type} [Field F] [NumberField F]

lemma addChar_sum {ι : Type} (ψ : AddChar (AF F) ℂ) (S : Finset ι) (f : ι → AF F) :
    ψ (∑ v ∈ S, f v) = ∏ v ∈ S, ψ (f v) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, Finset.prod_empty]; exact AddChar.map_zero_eq_one ψ
  | insert a S ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, AddChar.map_add_eq_mul, ih]

end GlobalTheory.AdeleCharProd

namespace GlobalTheory.AdeleCharProd

theorem psi_eq_inf_mul_finprod : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ →
    (∀ᶠ v in cofinite, PsiUnr ψ v) →
    ∀ a : AF F, ψ a = Complex.exp (-(2 * Real.pi * Complex.I) *
      (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F a) : ℝ)) * ∏ᶠ v, psiLoc ψ v (evFin F v a) := by
  intro F _ _ ψ hstd hunr a
  classical
  obtain ⟨S, q, hq, hout, hx⟩ := finite_decomp ψ hunr a.2
  let j : Af F →+ AF F :=
    { toFun := fun y => (LinearMap.inr F (Ainf F) (Af F) y : AF F)
      map_zero' := by simp; rfl
      map_add' := fun y z => by
        show ((0 : Ainf F), y + z) = ((0 : Ainf F) + 0, y + z)
        rw [add_zero] }
  let i1 : AF F := LinearMap.inl F (Ainf F) (Af F) a.1
  have ha : a = i1 + j a.2 := by
    show a = (a.1 + 0, 0 + a.2)
    rw [add_zero, zero_add]; rfl
  have hinf : ψ i1 = Complex.exp (-(2 * Real.pi * Complex.I) *
      (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F a) : ℝ)) := by
    refine hstd.2.2 _ ?_
    intro u hu
    have hu1 : u.1 = 0 := by
      have : (InfiniteAdeleRing.ringEquiv_mixedSpace F) u.1 = 0 := hu
      exact (map_eq_zero_iff _ (RingEquiv.injective _)).1 this
    show (u.1 * a.1, u.2 * 0) = ((0 : AF F))
    rw [hu1, zero_mul, mul_zero]; rfl
  have hfin : ψ (j a.2) = ∏ v ∈ S, psiLoc ψ v (evFin F v a) := by
    rw [hx, map_add, map_sum, AddChar.map_add_eq_mul, addChar_sum]
    rw [show ψ (j (ofInt q)) = 1 from psi_ofInt ψ hstd.1 q hq, one_mul]
    refine Finset.prod_congr rfl fun v _ => ?_
    rfl
  have hfp : ∏ᶠ v, psiLoc ψ v (evFin F v a) = ∏ v ∈ S, psiLoc ψ v (evFin F v a) := by
    apply finprod_eq_prod_of_mulSupport_subset
    intro v hv
    by_contra hvS
    obtain ⟨h1, h2⟩ := hout v hvS
    exact hv (psiLoc_int h1 h2)
  rw [hfp]
  conv_lhs => rw [ha]
  rw [AddChar.map_add_eq_mul, hinf, hfin]

end GlobalTheory.AdeleCharProd

end
