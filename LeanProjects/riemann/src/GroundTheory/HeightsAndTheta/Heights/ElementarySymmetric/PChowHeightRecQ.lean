import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PRecQOfRecursion
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PRecursion
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.ContinuousHermNormGroup
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PBaseChangeAvoid
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.Imports
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

noncomputable section

namespace ChowHeightRecQ

open MvPolynomial NumberField
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsArithVar IsHorizontal divSupp multAt geoNum charOf arInt)

variable {n : ℕ}

def chowHtAt (h : HermNorm n) (k δ : ℕ) (f : MvPolynomial (Fin k × Fin n) ℚ) : ℝ :=
  (∑ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ), Real.log (gaussNorm v f)) +
    (mahler h k (f.map (Rat.castHom ℂ)) + k * δ * (harmonic (n - 1) : ℝ) / 2)

theorem chowHtAt_C (h : HermNorm n) (k : ℕ) {c : ℚ} (hc : c ≠ 0) :
    chowHtAt h k 0 (C c : MvPolynomial (Fin k × Fin n) ℚ) = 0 := by
  have h1 := sum_log_norm_embeddings (K := ℚ) hc
  rw [Fintype.sum_subsingleton _ (Rat.castHom ℂ)] at h1
  unfold chowHtAt
  rw [map_C, mahler_C]
  simp only [gaussNorm_C, Nat.cast_zero, mul_zero, zero_mul, zero_div, add_zero,
    finsum_log_adicAbv hc, h1, neg_add_cancel]

theorem chowHtAt_zero_groups (h : HermNorm n) (δ : ℕ) {g : MvPolynomial (Fin 0 × Fin n) ℚ} (hg : g ≠ 0) :
    chowHtAt h 0 δ g = 0 := by
  have h0 : chowHtAt h 0 δ g = chowHtAt h 0 0 g := by simp [chowHtAt]
  rw [h0, eq_C_of_isEmpty g]
  rw [eq_C_of_isEmpty g] at hg
  exact chowHtAt_C h 0 fun hc => hg (by rw [hc, map_zero])

theorem chowHtAt_mul (h : HermNorm n) (k δ₁ δ₂ : ℕ) {f₁ f₂ : MvPolynomial (Fin k × Fin n) ℚ}
    (h₁ : f₁ ≠ 0) (h₂ : f₂ ≠ 0) :
    chowHtAt h k (δ₁ + δ₂) (f₁ * f₂) = chowHtAt h k δ₁ f₁ + chowHtAt h k δ₂ f₂ := by
  unfold chowHtAt
  rw [finsum_log_gaussNorm_mul h₁ h₂, map_mul,
    mahlerMul n k h _ _ (fun h0 => h₁ (map_injective _ (Rat.castHom ℂ).injective (by rw [h0, map_zero])))
      (fun h0 => h₂ (map_injective _ (Rat.castHom ℂ).injective (by rw [h0, map_zero])))]
  push_cast
  ring

theorem chowHtAt_pow (h : HermNorm n) {k : ℕ} (d : ℕ) {g : MvPolynomial (Fin k × Fin n) ℚ} (hg : g ≠ 0)
    (m : ℕ) : chowHtAt h k (m * d) (g ^ m) = m * chowHtAt h k d g := by
  induction m with
  | zero =>
    rw [zero_mul, pow_zero, Nat.cast_zero, zero_mul, ← C_1]
    exact chowHtAt_C h k one_ne_zero
  | succ m ih =>
    rw [pow_succ, Nat.succ_mul, chowHtAt_mul h k _ _ (pow_ne_zero _ hg) hg, ih]
    push_cast
    ring

theorem chowHtAt_C_mul_prod (h : HermNorm n) {k : ℕ} {ι : Type*} (s : Finset ι) (m d : ι → ℕ)
    (g : ι → MvPolynomial (Fin k × Fin n) ℚ) (hg : ∀ i ∈ s, g i ≠ 0) {c : ℚ} (hc : c ≠ 0) :
    chowHtAt h k (∑ i ∈ s, m i * d i) (C c * ∏ i ∈ s, g i ^ m i) =
      ∑ i ∈ s, (m i : ℝ) * chowHtAt h k (d i) (g i) := by
  classical
  have hP : ∀ t ⊆ s, ∏ i ∈ t, g i ^ m i ≠ 0 := fun t ht =>
    Finset.prod_ne_zero_iff.mpr fun i hi => pow_ne_zero _ (hg i (ht hi))
  have hprod : ∀ t ⊆ s, chowHtAt h k (∑ i ∈ t, m i * d i) (∏ i ∈ t, g i ^ m i) =
      ∑ i ∈ t, (m i : ℝ) * chowHtAt h k (d i) (g i) := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
      intro _
      rw [Finset.sum_empty, Finset.prod_empty, Finset.sum_empty, ← C_1]
      exact chowHtAt_C h k one_ne_zero
    | insert a t ha ih =>
      intro hts
      rw [Finset.sum_insert ha, Finset.prod_insert ha, Finset.sum_insert ha,
        chowHtAt_mul h k _ _ (pow_ne_zero _ (hg a (hts (Finset.mem_insert_self a t))))
          (hP t (fun x hx => hts (Finset.mem_insert_of_mem hx))),
        chowHtAt_pow h _ (hg a (hts (Finset.mem_insert_self a t))),
        ih (fun x hx => hts (Finset.mem_insert_of_mem hx))]
  have := chowHtAt_mul h k 0 (∑ i ∈ s, m i * d i) (C_ne_zero.mpr hc) (hP s le_rfl)
  rw [zero_add] at this
  rw [this, chowHtAt_C h k hc, zero_add, hprod s le_rfl]

theorem chowHtAt_eq_chowHeight (S : Matrix (Fin n) (Fin n) ℂ) (hS : IsUnit S) {e δ : ℕ}
    (f : MvPolynomial (Fin (e + 1) × Fin n) ℚ) :
    chowHtAt (ObjectsHeight.ofPointMatrix S hS) (e + 1) δ f = IndefiniteRowSideFullHecke.ArithBezout.chowHeight S f δ := by
  have hw : Height.totalWeight ℚ = 1 := by
    rw [NumberField.totalWeight_eq_finrank, Module.finrank_self]
  have hmult : (default : InfinitePlace ℚ).mult = 1 := by
    have := NumberField.totalWeight_eq_sum_mult (K := ℚ)
    rw [hw, Fintype.sum_unique] at this
    exact this.symm
  have hσ : (default : InfinitePlace ℚ).embedding = Rat.castHom ℂ := Subsingleton.elim _ _
  unfold chowHtAt IndefiniteRowSideFullHecke.ArithBezout.chowHeight ReciprocityTheory.ChartRestriction.G.Geo.chowHt ReciprocityTheory.ChartRestriction.G.Geo.chowHeightOfForm
  rw [ObjectsHeight.finsum_log_gaussNorm, Fintype.sum_unique, hmult, hw, hσ,
    ObjectsHeight.mahler_eq_chowMean S hS _ (ObjectsHeight.ofPointMatrix_norm S hS)]
  simp only [ReciprocityTheory.ChartRestriction.G.Geo.logMean, IndefiniteRowSideFullHecke.ArithBezout.chowMean]
  push_cast
  ring

theorem chowHtAt_rec (hV : ChowFormSectionVertical.Statement) (hA : MahlerSection.Statement)
    (hB : ChowFormBaseChange.Statement) (hAv : BaseChangeAvoid.Statement) (h : HermNorm n) {e δ : ℕ}
    {I : Ideal (MvPolynomial (Fin n) ℚ)} {f : MvPolynomial (Fin (e + 1) × Fin n) ℚ} {u : Fin n → 𝓞 ℚ}
    (hI : IsProjPrime I) (hf : IsChowForm I (e + 1) f) (hδ : IsMultiHomog δ f)
    (hu : linForm (fun j => (u j : ℚ)) ∉ I) :
    chowHtAt h (e + 1) δ f =
      chowHtAt h e δ (specFirst f fun j => (u j : ℚ)) +
        (vertTerm I (e + 1) u -
          cycleIntegral h (fundCycle (I.map (MvPolynomial.map (Rat.castHom ℂ)))) e
            (fsLog h fun j => Rat.castHom ℂ (u j))) := by
  set u' : Fin n → ℚ := fun j => (u j : ℚ) with hu'
  set g := specFirst f u' with hg
  have hfin_f := log_gaussNorm_support_finite (K := ℚ) hf.1
  have hfin_g : (Function.support fun v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ) =>
      Real.log (gaussNorm v g)).Finite := by
    by_cases hg0 : g = 0
    · have : (fun v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ) => Real.log (gaussNorm v g)) = 0 := by
        funext v
        rw [hg0]
        simp [gaussNorm]
        exact Or.inl rfl
      rw [this, Function.support_zero]
      exact Set.finite_empty
    · exact log_gaussNorm_support_finite hg0
  have hfinsum : ∑ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ), Real.log (gaussNorm v f) =
      (∑ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ), Real.log (gaussNorm v g)) + vertTerm I (e + 1) u := by
    unfold vertTerm
    rw [← finsum_add_distrib hfin_g]
    · refine finsum_congr fun v => ?_
      rw [← hV ℚ n e I f u hI hf hu v]
      ring
    · refine Set.Finite.subset (hfin_f.union hfin_g) fun v hv => ?_
      rw [Function.mem_support, ← hV ℚ n e I f u hI hf hu v] at hv
      by_contra hcon
      simp only [Set.mem_union, Function.mem_support, not_or, not_not] at hcon
      exact hv (by rw [hcon.1, hcon.2, sub_zero])
  have harch : mahler h (e + 1) (f.map (Rat.castHom ℂ)) =
      mahler h e (g.map (Rat.castHom ℂ)) - δ * (harmonic (n - 1) : ℝ) / 2 -
        cycleIntegral h (fundCycle (I.map (MvPolynomial.map (Rat.castHom ℂ)))) e
          (fsLog h fun j => Rat.castHom ℂ (u j)) := by
    obtain ⟨hprime, hcyc⟩ := hB ℚ n (e + 1) I f (Rat.castHom ℂ) hI hf
    have hδσ : IsMultiHomog δ (MvPolynomial.map (Rat.castHom ℂ) f) :=
      (isMultiHomog_iff _ _).mpr fun i =>
        IsWeightedHomogeneous.map' ((isMultiHomog_iff _ _).mp hδ i) (Rat.castHom ℂ)
    have h' := hA n e δ h _ _ (fun j => Rat.castHom ℂ (u j)) hprime hcyc hδσ
      (fun W hW => hAv ℚ n I u' (Rat.castHom ℂ) hI hu W hW)
    rw [hg, map_specFirst, h']
    ring
  unfold chowHtAt
  rw [hfinsum, harch]
  push_cast
  ring

theorem integralAt_eq (hC : ComplexFibreCycle.Statement) (hI : ConeIntegralPts.Statement)
    (S : Matrix (Fin n) (Fin n) ℂ) (hS : IsUnit S)
    {e δ : ℕ} {P : Ideal (MRing (PBlk n))} {f : MvPolynomial (Fin (e + 1) × Fin n) ℚ} {u : Fin n → ℤ}
    (hP : IsArithVar P (e + 1))
    (hf : ReciprocityTheory.ChartRestriction.G.Geo.IsChowForm (Int.castRingHom ℂ) (IndefiniteRowSideFullHecke.ArithBezout.finIdeal P) e δ
      (map (Rat.castHom ℂ) f))
    (hsf : specFirst f (fun j => (u j : ℚ)) ≠ 0) :
    cycleIntegral (ObjectsHeight.ofPointMatrix S hS)
        (fundCycle ((ObjectsChow.genericIdeal P).map (MvPolynomial.map (Rat.castHom ℂ)))) e
        (fsLog (ObjectsHeight.ofPointMatrix S hS) fun j => Rat.castHom ℂ (u j : ℚ)) =
      arInt P (IndefiniteRowSideFullHecke.ArithBezout.linForm u) (IndefiniteRowSideFullHecke.ArithBezout.hermLine S hS)
        (fun _ : Fin e => IndefiniteRowSideFullHecke.ArithBezout.hermLine S hS) := by
  have hu : (fun j => (Rat.castHom ℂ) (u j : ℚ)) = fun j => (u j : ℂ) := funext fun j => by simp
  rw [hu, RecQOfRecursion.map_genericIdeal]
  have hW : ∀ W ∈ (fundCycle (complexFibreIdeal P)).support, linForm (fun j => (u j : ℂ)) ∉ W := by
    refine ((hC n e δ P _ hP hf).2.2 _).mp ?_
    have h : IndefiniteRowSideFullHecke.ArithBezout.specFirst (fun j => (u j : ℂ)) (map (Rat.castHom ℂ) f) =
        map (Rat.castHom ℂ) (specFirst f fun j => (u j : ℚ)) := by
      rw [ObjectsChow.specFirst_eq, ObjectsChow.map_specFirst, ← hu]
      rfl
    rw [h]
    exact fun h0 => hsf (map_injective _ (Rat.castHom ℂ).injective (by rw [h0, map_zero]))
  exact (hI n e S hS P _ hP hW).trans (by rw [RecQOfRecursion.logFormNorm_eq]; rfl)

theorem stepAt (hSV : ChowFormSectionVertical.Statement) (hA : MahlerSection.Statement)
    (hB : ChowFormBaseChange.Statement) (hAv : BaseChangeAvoid.Statement) (hSec : ChowFormSection.Statement)
    (hV : ObjectsChow.VertPartEq.Statement) (hC : ComplexFibreCycle.Statement)
    (hI : ConeIntegralPts.Statement) (S : Matrix (Fin n) (Fin n) ℂ) (hS : IsUnit S)
    {e δ : ℕ} {P : Ideal (MRing (PBlk n))} {f : MvPolynomial (Fin (e + 1) × Fin n) ℚ} {u : Fin n → ℤ}
    (hP : IsArithVar P (e + 1))
    (hf : ReciprocityTheory.ChartRestriction.G.Geo.IsChowForm (Int.castRingHom ℂ) (IndefiniteRowSideFullHecke.ArithBezout.finIdeal P) e δ
      (map (Rat.castHom ℂ) f))
    (hu : IndefiniteRowSideFullHecke.ArithBezout.linForm u ∉ P) :
    IndefiniteRowSideFullHecke.ArithBezout.chowHeight S f δ =
                              chowHtAt (ObjectsHeight.ofPointMatrix S hS) e δ (specFirst f fun j => (u j : ℚ)) +
                                (IndefiniteRowSideFullHecke.ArithBezout.vertPart P e (IndefiniteRowSideFullHecke.ArithBezout.linForm u) -
                                  arInt P (IndefiniteRowSideFullHecke.ArithBezout.linForm u) (IndefiniteRowSideFullHecke.ArithBezout.hermLine S hS)
                                    (fun _ : Fin e => IndefiniteRowSideFullHecke.ArithBezout.hermLine S hS)) ∧
      IsChowFormCycle (divCycle (ObjectsChow.genericIdeal P) fun j => (u j : ℚ)) e
        (specFirst f fun j => (u j : ℚ)) := by
  have hprime := VerticalPartGauss.isProjPrime_genericIdeal hP
  have hfA := VerticalPartGauss.isChowForm_genericIdeal hP hf
  have huA := VerticalPartGauss.linForm_not_mem_genericIdeal hP hu
  have hcyc := hSec ℚ n e (ObjectsChow.genericIdeal P) f _ hprime hfA huA
  have hcast : ∀ j, (((u j : ℤ) : 𝓞 ℚ) : ℚ) = (u j : ℚ) := fun j => by simp
  have key := chowHtAt_rec hSV hA hB hAv (ObjectsHeight.ofPointMatrix S hS) (u := fun j => ((u j : ℤ) : 𝓞 ℚ))
    hprime hfA (ObjectsChow.isMultiHomog_of_isChowForm hf) (by simp only [hcast]; exact huA)
  simp only [hcast] at key
  refine ⟨?_, hcyc⟩
  rw [← chowHtAt_eq_chowHeight S hS f, key, hV n e P u hP hu,
    integralAt_eq hC hI S hS hP hf (RecQOfRecursion.ne_zero_of_isChowFormCycle hcyc)]

open Classical in

theorem horizontalAt (S : Matrix (Fin n) (Fin n) ℂ) (hS : IsUnit S)
    {e δ : ℕ} {P : Ideal (MRing (PBlk n))} {f : MvPolynomial (Fin (e + 1 + 1) × Fin n) ℚ} {u : Fin n → ℤ}
    {g : Ideal (MRing (PBlk n)) → MvPolynomial (Fin (e + 1) × Fin n) ℚ} {d : Ideal (MRing (PBlk n)) → ℕ}
    (hP : IsArithVar P (e + 1 + 1))
    (hf : ReciprocityTheory.ChartRestriction.G.Geo.IsChowForm (Int.castRingHom ℂ) (IndefiniteRowSideFullHecke.ArithBezout.finIdeal P) (e + 1) δ
      (map (Rat.castHom ℂ) f))
    (hu : IndefiniteRowSideFullHecke.ArithBezout.linForm u ∉ P)
    (hg : ∀ W ∈ divSupp P (IndefiniteRowSideFullHecke.ArithBezout.linForm u), IsHorizontal W →
      ReciprocityTheory.ChartRestriction.G.Geo.IsChowForm (Int.castRingHom ℂ) (IndefiniteRowSideFullHecke.ArithBezout.finIdeal W) e (d W)
        (map (Rat.castHom ℂ) (g W)))
    (hcyc : IsChowFormCycle (divCycle (ObjectsChow.genericIdeal P) fun j => (u j : ℚ)) (e + 1)
      (specFirst f fun j => (u j : ℚ))) :
    chowHtAt (ObjectsHeight.ofPointMatrix S hS) (e + 1) δ (specFirst f fun j => (u j : ℚ)) =
      ∑ᶠ W ∈ divSupp P (IndefiniteRowSideFullHecke.ArithBezout.linForm u),
        (multAt (P ⊔ Ideal.span {IndefiniteRowSideFullHecke.ArithBezout.linForm u}) W : ℝ) *
          (if IsHorizontal W then IndefiniteRowSideFullHecke.ArithBezout.chowHeight S (g W) (d W) else 0) := by
  set s := IndefiniteRowSideFullHecke.ArithBezout.linForm u
  set Zh := (ReciprocityTheory.ChartRestriction.G.Geo.divCycle P s).filter IsHorizontal with hZh
  have hmem : ∀ W ∈ Zh.support, W ∈ divSupp P s ∧ IsHorizontal W := by
    intro W hW
    rw [hZh, Finsupp.support_filter, Finset.mem_filter, Finsupp.mem_support_iff,
      RecQOfRecursion.divCycle_apply] at hW
    exact ⟨by_contra fun h => hW.1 (if_neg h), hW.2⟩
  have hgA : ∀ W ∈ Zh.support, IsChowForm (ObjectsChow.genericIdeal W) (e + 1) (g W) := fun W hW =>
    VerticalPartGauss.isChowForm_genericIdeal
      (ObjectsChow.DivSuppHorizontalArithVar.proof n (e + 1) P u W hP hu (hmem W hW).1 (hmem W hW).2)
      (hg W (hmem W hW).1 (hmem W hW).2)
  have hsfne := RecQOfRecursion.ne_zero_of_isChowFormCycle hcyc
  obtain ⟨c, hc, g', hg', hsf⟩ := hcyc
  have hD := ObjectsChow.DivCycleGeneric.proof n (e + 1) P u hP hu
  rw [hD] at hsf hg'
  have hpos : ∀ W ∈ Zh.support,
      ObjectsChow.genericIdeal W ∈ (Zh.mapDomain ObjectsChow.genericIdeal).support := by
    intro W hW
    rw [Finsupp.mem_support_iff, Finsupp.mapDomain, Finsupp.sum_apply]
    have h1 := Finset.single_le_sum (f := fun a => Finsupp.single (ObjectsChow.genericIdeal a) (Zh a)
      (ObjectsChow.genericIdeal W)) (fun _ _ => Nat.zero_le _) hW
    simp only [Finsupp.single_eq_same] at h1
    exact (lt_of_lt_of_le (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hW)) h1).ne'
  have hr : ∀ W ∈ Zh.support, ∃ r : ℚ, r ≠ 0 ∧ g' (ObjectsChow.genericIdeal W) = C r * g W :=
    fun W hW => RecQOfRecursion.exists_C_mul_of_isChowForm (hgA W hW) (hg' _ (hpos W hW))
  choose! r hr0 hr using hr
  have hsf' : specFirst f (fun j => (u j : ℚ)) =
      C (c * ∏ W ∈ Zh.support, r W ^ Zh W) * ∏ W ∈ Zh.support, g W ^ Zh W := by
    have hprod : ∏ W ∈ (Zh.mapDomain ObjectsChow.genericIdeal).support,
        g' W ^ (Zh.mapDomain ObjectsChow.genericIdeal) W =
          Zh.prod fun W m => g' (ObjectsChow.genericIdeal W) ^ m :=
      Finsupp.prod_mapDomain_index (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)
    rw [hsf, hprod, Finsupp.prod, Finset.prod_congr rfl (fun W hW =>
      show g' (ObjectsChow.genericIdeal W) ^ Zh W = C (r W ^ Zh W) * g W ^ Zh W by
        rw [hr W hW, mul_pow, map_pow]), Finset.prod_mul_distrib, ← map_prod, map_mul, mul_assoc]
  have hgne : ∀ W ∈ Zh.support, g W ≠ 0 := fun W hW => (hgA W hW).1
  have hgm : ∀ W ∈ Zh.support, IsMultiHomog (d W) (g W) := fun W hW =>
    ObjectsChow.isMultiHomog_of_isChowForm (hg W (hmem W hW).1 (hmem W hW).2)
  have hc' : c * ∏ W ∈ Zh.support, r W ^ Zh W ≠ 0 :=
    mul_ne_zero hc (Finset.prod_ne_zero_iff.mpr fun W hW => pow_ne_zero _ (hr0 W hW))
  have hδ : δ = ∑ W ∈ Zh.support, Zh W * d W := by
    have h1 : IsMultiHomog δ (specFirst f fun j => (u j : ℚ)) :=
      (ObjectsChow.isMultiHomog_of_isChowForm hf).specFirst _
    have h2 : IsMultiHomog (∑ W ∈ Zh.support, Zh W * d W) (specFirst f fun j => (u j : ℚ)) := by
      rw [hsf']
      unfold IsMultiHomog
      have := (isWeightedHomogeneous_C (groupWeight (e + 1) n) (c * ∏ W ∈ Zh.support, r W ^ Zh W)).mul
        (IsWeightedHomogeneous.prod Zh.support (fun W => g W ^ Zh W)
          (fun W => Zh W • fun _ : Fin (e + 1) => d W) fun W hW => (hgm W hW).pow (Zh W))
      convert this using 1
      funext i
      simp [Finset.sum_apply]
    exact congrFun (IsWeightedHomogeneous.inj_right hsfne h1 h2) 0
  rw [hsf', hδ, chowHtAt_C_mul_prod _ Zh.support (⇑Zh) d g hgne hc']
  simp_rw [chowHtAt_eq_chowHeight S hS]
  rw [finsum_mem_eq_finite_toFinset_sum _ (ReciprocityTheory.ChartRestriction.G.Geo.divSupp_finite P s)]
  refine (Finset.sum_subset (fun W hW => (ReciprocityTheory.ChartRestriction.G.Geo.divSupp_finite P s).mem_toFinset.mpr
    (hmem W hW).1) ?_).trans (Finset.sum_congr rfl fun W hW => ?_)
  · intro W _ hW
    rw [Finsupp.mem_support_iff, not_not] at hW
    rw [hW, Nat.cast_zero, zero_mul]
  · have hWd : W ∈ divSupp P s := (ReciprocityTheory.ChartRestriction.G.Geo.divSupp_finite P s).mem_toFinset.mp hW
    rw [hZh, Finsupp.filter_apply, RecQOfRecursion.divCycle_apply, if_pos hWd]
    split_ifs <;> simp

theorem of_local (hSV : ChowFormSectionVertical.Statement) (hA : MahlerSection.Statement)
    (hB : ChowFormBaseChange.Statement) (hAv : BaseChangeAvoid.Statement) (hSec : ChowFormSection.Statement)
    (hV : ObjectsChow.VertPartEq.Statement) (hC : ComplexFibreCycle.Statement)
    (hI : ConeIntegralPts.Statement) : ChowHeightRecQ.Statement := by
  intro n S hS
  refine ⟨fun δ P f u hP hf hu => ?_, fun e δ P f u g d hP hf hu hg => ?_⟩
  · obtain ⟨h, hcyc⟩ := stepAt hSV hA hB hAv hSec hV hC hI S hS hP hf hu
    rw [h, chowHtAt_zero_groups _ _ (RecQOfRecursion.ne_zero_of_isChowFormCycle hcyc), zero_add]
  · obtain ⟨h, hcyc⟩ := stepAt hSV hA hB hAv hSec hV hC hI S hS hP hf hu
    rw [h, horizontalAt S hS hP hf hu hg hcyc, IndefiniteRowSideFullHecke.ArithBezout.vertPart, ← add_sub_assoc,
      ← finsum_mem_add_distrib (ReciprocityTheory.ChartRestriction.G.Geo.divSupp_finite _ _)]
    congr 1
    refine finsum_mem_congr rfl fun W _ => ?_
    split_ifs <;> ring

end ChowHeightRecQ

theorem ChowHeightRecQ.proof (hA : MahlerSection.Statement) (hB : ChowFormBaseChange.Statement)
    (hSec : ChowFormSection.Statement) (hV : ObjectsChow.VertPartEq.Statement)
    (hC : ComplexFibreCycle.Statement) (hI : ConeIntegralPts.Statement) : ChowHeightRecQ.Statement :=
  ChowHeightRecQ.of_local Vertical.ChowFormSectionVertical.full hA hB BaseChangeAvoid.proof hSec hV hC hI

end

end GroundTheory.Heights₂.Heights
