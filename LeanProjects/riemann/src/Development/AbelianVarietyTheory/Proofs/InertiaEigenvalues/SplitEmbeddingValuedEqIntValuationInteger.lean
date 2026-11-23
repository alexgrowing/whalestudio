import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsRatConstMul
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsInertTop
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SplitLinearModelNorm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OscillatorModelValuesThird
import Formalism.LocalToGlobal.IndefiniteReal.TopMult
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsThetaFunOOfIsVacO
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsThetaFunOOfThetaAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PtYAndItYOfPair
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasInfExpMulOfIsOpenKer
import Development.AbelianVarietyTheory.Definitions.Foundations.AbsCharNotUnitary
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RelIndexMatrixLattice
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ModulusUnramifiedCharDetHeckeDoubleCosetSplit

noncomputable section

open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links
  Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.L2.Host

namespace GlobalTheory.SplitIdeleModulus

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F)) (φ : E →+* v.adicCompletion F) (P : HeightOneSpectrum (𝓞 E))
  (hφ : ∀ t : F, φ (algebraMap F E t) = algebraMap F (v.adicCompletion F) t)
  (hP : ∀ x : 𝓞 E, x ∈ P.asIdeal ↔ Valued.v (φ x) < 1)

include hφ hP in

theorem splitEmbedding_valued_eq_intValuation_integer (n : ℕ) : ∀ y : 𝓞 E, y ≠ 0 → P.intValuation y = WithZero.exp (-(n : ℤ)) →
    Valued.v (φ y) = WithZero.exp (-(n : ℤ)) := by
  induction n with
  | zero =>
    intro y hy hyv
    have hyP : y ∉ P.asIdeal := by
      rw [← HeightOneSpectrum.intValuation_lt_one_iff_mem, hyv]
      simp
    refine le_antisymm ?_ ?_
    · rw [Nat.cast_zero, neg_zero, WithZero.exp_zero]
      exact GlobalTheory.SplitUnif.map_mem v φ y
    · rw [Nat.cast_zero, neg_zero, WithZero.exp_zero]
      exact not_lt.1 (mt (hP y).2 hyP)
  | succ n ih =>
    intro y hy hyv
    obtain ⟨ϖ, hϖ⟩ := P.intValuation_exists_uniformizer
    have hϖ0 : ϖ ≠ 0 := by
      rintro rfl
      rw [map_zero] at hϖ
      exact WithZero.exp_ne_zero hϖ.symm
    have hϖ1 : ϖ ∈ P.asIdeal := by
      rw [← HeightOneSpectrum.intValuation_lt_one_iff_mem, hϖ]
      exact WithZero.exp_lt_exp.2 (by omega) |>.trans_eq WithZero.exp_zero
    have hϖ2 : ϖ ∉ P.asIdeal ^ 2 := by
      rw [← HeightOneSpectrum.intValuation_le_pow_iff_mem, hϖ, WithZero.exp_le_exp]
      norm_num
    have hE0 : ((ϖ : 𝓞 E) : E) ≠ 0 := by
      intro h; exact hϖ0 (Subtype.ext h)
    have hx : P.valuation E ((y : E) / ϖ) ≤ 1 := by
      rw [map_div₀, HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap, hyv, hϖ,
        ← WithZero.exp_sub]
      rw [← WithZero.exp_zero, WithZero.exp_le_exp]
      omega
    obtain ⟨m, d, h⟩ := P.exists_primeCompl_mul_eq_of_integer _ hx
    have h3 : (y : E) * ((d : 𝓞 E) : E) = (m : E) * ϖ := by
      have h' : (y : E) / ϖ * ((d : 𝓞 E) : E) = (m : E) := h
      rw [← h']
      field_simp
    have h3' : y * (d : 𝓞 E) = m * ϖ := by
      apply RingOfIntegers.coe_injective
      push_cast
      exact h3
    have hdv : P.intValuation (d : 𝓞 E) = 1 := by
      refine le_antisymm (P.intValuation_le_one _) ?_
      exact not_lt.1 (mt (HeightOneSpectrum.intValuation_lt_one_iff_mem P _).1 d.2)
    have hm0 : m ≠ 0 := by
      rintro rfl
      rw [zero_mul, mul_eq_zero] at h3'
      rcases h3' with h0 | h0
      · exact hy h0
      · exact d.2 (h0 ▸ zero_mem _)
    have hmv : P.intValuation m = WithZero.exp (-(n : ℤ)) := by
      have h4 := congrArg P.intValuation h3'
      rw [map_mul, map_mul, hdv, mul_one, hyv, hϖ] at h4
      have h5 : P.intValuation m ≠ 0 := P.intValuation_ne_zero m hm0
      rw [← WithZero.exp_log h5, ← WithZero.exp_add, WithZero.exp_inj] at h4
      rw [← WithZero.exp_log h5, WithZero.exp_inj]
      push_cast at h4
      omega
    have hd : Valued.v (φ ((d : 𝓞 E) : E)) = 1 :=
      le_antisymm (GlobalTheory.SplitUnif.map_mem v φ d) (not_lt.1 (mt (hP d).2 d.2))
    have h4 := congrArg (fun z => Valued.v (φ z)) h3
    simp only [map_mul] at h4
    rw [hd, mul_one, ih m hm0 hmv, GlobalTheory.SplitUnif.valued_unif v φ P hφ hP ϖ hϖ1 hϖ2, ← WithZero.exp_add] at h4
    rw [h4]
    congr 1
    push_cast
    ring

include hφ hP in
theorem valued_eq_intValuation (y : 𝓞 E) (hy : y ≠ 0) : Valued.v (φ y) = P.intValuation y := by
  have h0 : P.intValuation y ≠ 0 := P.intValuation_ne_zero y hy
  have hle : WithZero.log (P.intValuation y) ≤ 0 := by
    have := P.intValuation_le_one y
    rw [← WithZero.exp_log h0, ← WithZero.exp_zero, WithZero.exp_le_exp] at this
    exact this
  have key : P.intValuation y = WithZero.exp (-((WithZero.log (P.intValuation y)).natAbs : ℤ)) := by
    rw [← WithZero.exp_log h0]
    congr 1
    rw [WithZero.log_exp]
    omega
  rw [key]
  exact splitEmbedding_valued_eq_intValuation_integer v φ P hφ hP _ y hy key

end General

end GlobalTheory.SplitIdeleModulus

namespace GlobalTheory.SplitIdeleModulus

open GlobalTheory.SplitHecke
open Formalism.L2.NTheta (IsIdemAt)

variable {D : D7}

theorem chart_incA_algebraMap {e : AE D} {v : HeightOneSpectrum (𝓞 D.host.F)} {π : AE D →+* Fv D.host.F v}
    (hc : Chart e v π) (t : D.host.F) :
    (π.comp (incA D)) (algebraMap D.host.F D.host.E t) = algebraMap D.host.F (v.adicCompletion D.host.F) t := by
  have e1 : incA D (algebraMap D.host.F D.host.E t) =
      algebraMap (AF D.host.F) (AE D) (algebraMap D.host.F (AF D.host.F) t) := by
    rw [← IsScalarTower.algebraMap_apply]
    exact (Algebra.TensorProduct.includeRight (R := D.host.F) (A := AF D.host.F) (B := D.host.E)).commutes t
  show π (incA D _) = _
  rw [e1, hc.2.2.1, AlgHom.commutes, AlgHom.commutes]

theorem chart_incA_mem {e : AE D} {P : HeightOneSpectrum (𝓞 D.host.E)} {v : HeightOneSpectrum (𝓞 D.host.F)}
    {π : AE D →+* Fv D.host.F v} (he : IsIdemAt e P) (hc : Chart e v π) (x : 𝓞 D.host.E) :
    x ∈ P.asIdeal ↔ Valued.v ((π.comp (incA D)) x) < 1 := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · have hx0 : Valued.v ((π.comp (incA D)) x) ≠ 0 := by
      rw [Valuation.ne_zero_iff, map_ne_zero]
      exact fun h => hx (Subtype.ext h)
    rw [he.2 x hx, hc.2.2.2, isInt_Ov]
    show ¬ Valued.v ((π.comp (incA D)) (x : D.host.E)⁻¹) ≤ 1 ↔ _
    rw [map_inv₀, map_inv₀, not_le, one_lt_inv₀ (zero_lt_iff.2 hx0)]

theorem idemAt_mul_eq_zero {e f : AE D} {P Q : HeightOneSpectrum (𝓞 D.host.E)} (he : IsIdemAt e P)
    (hf : IsIdemAt f Q) (hPQ : P ≠ Q) : e * f = 0 := by
  obtain ⟨v, π, hπ⟩ := GlobalTheory.SplitChart.exists_chart e he.1
  obtain ⟨w, ρ, hρ⟩ := GlobalTheory.SplitChart.exists_chart f hf.1
  have hee : e * e = e := he.1.1
  have hff : f * f = f := hf.1.1
  have hg : (e * f) * (e * f) = e * f := by
    calc (e * f) * (e * f) = (e * e) * (f * f) := by ring
      _ = e * f := by rw [hee, hff]
  by_contra hne

  have h1 : e = e * f := by
    have hi : IsIdempotentElem (π (e * f)) := by
      unfold IsIdempotentElem; rw [← map_mul, hg]
    rcases IsIdempotentElem.iff_eq_zero_or_one.1 hi with h0 | h0
    · exfalso; apply hne
      have := (hπ.2.1 (e * f)).1 h0
      rwa [← mul_assoc, hee] at this
    · have h2 : π (e - e * f) = 0 := by
        rw [map_sub, h0, GlobalTheory.SplitLinear.chart_e hee hπ, sub_self]
      have := (hπ.2.1 _).1 h2
      rw [mul_sub, ← mul_assoc, hee, sub_eq_zero] at this
      exact this
  have h2 : f = e * f := by
    have hi : IsIdempotentElem (ρ (e * f)) := by
      unfold IsIdempotentElem; rw [← map_mul, hg]
    rcases IsIdempotentElem.iff_eq_zero_or_one.1 hi with h0 | h0
    · exfalso; apply hne
      have := (hρ.2.1 (e * f)).1 h0
      rw [mul_comm e f, ← mul_assoc, hff, mul_comm] at this
      exact this
    · have h2 : ρ (f - e * f) = 0 := by
        rw [map_sub, h0, GlobalTheory.SplitLinear.chart_e hff hρ, sub_self]
      have := (hρ.2.1 _).1 h2
      rw [mul_sub, mul_comm e f, ← mul_assoc, hff, sub_eq_zero] at this
      exact this.trans (mul_comm f e)
  have hef : e = f := h1.trans h2.symm
  apply hPQ
  ext x
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · rw [he.2 x hx, hf.2 x hx, hef]

theorem absFin_idemAt {e : AE D} {P : HeightOneSpectrum (𝓞 D.host.E)} (he : IsIdemAt e P) (m : ℕ)
    (hm : (m : D.host.E) ≠ 0) (u : (AE D)ˣ) (hu : (u : AE D) = e * (m : AE D) + (1 - e)) :
    GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absFin D u =
      ((Ideal.absNorm P.asIdeal : ℕ) : ℝ) ^ (-(Formalism.L2.Host.ordF P (Units.mk0 (m : D.host.E) hm))) := by
  obtain ⟨v, π, hπ⟩ := GlobalTheory.SplitChart.exists_chart e he.1
  have hee : e * e = e := he.1.1
  have hu1 : (1 - e) * (u : AE D) = 1 - e := by
    rw [hu]
    have : (1 - e) * e = 0 := by rw [sub_mul, one_mul, hee, sub_self]
    calc (1 - e) * (e * (m : AE D) + (1 - e)) = ((1 - e) * e) * (m : AE D) + (1 - e) - ((1 - e) * e) := by ring
      _ = 1 - e := by rw [this]; ring
  rw [GlobalTheory.SplitLinear.absFin_split D e v π he.1 hπ u hu1, GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absV]
  have hφ := chart_incA_algebraMap hπ
  have hP := chart_incA_mem he hπ
  have hN : Ideal.absNorm v.asIdeal = Ideal.absNorm P.asIdeal := by
    rw [← GlobalTheory.SplitDetValue.card_residue_eq]
    exact GlobalTheory.SplitUnif.card_residueField v _ P hφ hP
  have hm' : ((m : 𝓞 D.host.E)) ≠ 0 := by
    intro h; apply hm
    have := congrArg (fun z : 𝓞 D.host.E => (z : D.host.E)) h
    simpa using this
  have hval : Valued.v (π (u : AE D)) = P.valuation D.host.E (m : D.host.E) := by
    have e1 : π (u : AE D) = (π.comp (incA D)) (((m : 𝓞 D.host.E)) : D.host.E) := by
      rw [hu, map_add, map_mul, map_sub, map_one, GlobalTheory.SplitLinear.chart_e hee hπ, one_mul, sub_self, add_zero]
      simp
    rw [e1, valued_eq_intValuation v _ P hφ hP _ hm', ← P.valuation_of_algebraMap (K := D.host.E)]
    simp
  have e2 : ((Units.map π.toMonoidHom u : (Fv D.host.F v)ˣ) : Fv D.host.F v) = π (u : AE D) := rfl
  rw [e2, hval, hN, Formalism.L2.Host.ordF, Units.val_mk0, neg_neg]

end GlobalTheory.SplitIdeleModulus

namespace GlobalTheory.SplitIdeleModulus

open Formalism.L2.NTheta (IsIdemAt)

variable {D : D7}

theorem unit_aux {e c c' : AE D} (hee : e * e = e) (hcc : c * c' = 1) :
    (e * c + (1 - e)) * (e * c' + (1 - e)) = 1 := by
  linear_combination (c * c' - c - c' + 1) * hee + e * hcc

theorem prod_idem {P1 : Finset (Formalism.L2.DIV.Pl D.host.E)} {es : Formalism.L2.DIV.Pl D.host.E → AE D}
    (hes : ∀ PP ∈ P1, IsIdemAt (es PP) PP) (c : AE D) :
    ∀ s ⊆ P1, ∏ PP ∈ s, (es PP * c + (1 - es PP)) = (∑ PP ∈ s, es PP) * c + (1 - ∑ PP ∈ s, es PP) := by
  classical
  intro s
  induction s using Finset.induction_on with
  | empty => intro _; simp
  | insert Q s hQ ih =>
    intro hs
    have hs' : s ⊆ P1 := (Finset.subset_insert Q s).trans hs
    have hQS : es Q * ∑ PP ∈ s, es PP = 0 := by
      rw [Finset.mul_sum]
      refine Finset.sum_eq_zero fun PP hPP => ?_
      exact idemAt_mul_eq_zero (hes Q (hs (Finset.mem_insert_self Q s))) (hes PP (hs' hPP))
        (fun h => hQ (h ▸ hPP))
    rw [Finset.prod_insert hQ, Finset.sum_insert hQ, ih hs']
    linear_combination (c - 1) ^ 2 * hQS

theorem absFin_one' : GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absFin D 1 = 1 := by
  simp [GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absFin, GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absV]

theorem absFin_idemSum : ∀ (D : D7) (P1 : Finset (Formalism.L2.DIV.Pl D.host.E)) (a : AE D), IsIdemSum a P1 → ∀ (m : ℕ) (hm : (m : D.host.E) ≠ 0) (x : (AE D)ˣ), (x : AE D) = a * (m : AE D) + (1 - a) → GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absFin D x = ∏ PP ∈ P1, ((Ideal.absNorm PP.asIdeal : ℕ) : ℝ) ^ (-(Formalism.L2.Host.ordF PP (Units.mk0 (m : D.host.E) hm))) := by
  intro D P1 a ha m hm x hx
  obtain ⟨⟨es, hes, hae⟩, -⟩ := ha
  have hcc : (m : AE D) * incA D ((m : D.host.E)⁻¹) = 1 := by
    rw [← map_natCast (incA D) m, ← map_mul, mul_inv_cancel₀ hm, map_one]
  let u : {PP // PP ∈ P1} → (AE D)ˣ := fun PP =>
    { val := es PP.1 * (m : AE D) + (1 - es PP.1)
      inv := es PP.1 * incA D ((m : D.host.E)⁻¹) + (1 - es PP.1)
      val_inv := unit_aux (hes PP.1 PP.2).1.1 hcc
      inv_val := unit_aux (hes PP.1 PP.2).1.1 (by rw [mul_comm]; exact hcc) }
  have hx' : x = ∏ PP ∈ P1.attach, u PP := by
    apply Units.ext
    rw [hx, Units.coe_prod]
    change _ = ∏ PP ∈ P1.attach, (fun PP => es PP * (m : AE D) + (1 - es PP)) PP.1
    rw [Finset.prod_attach P1 (fun PP => es PP * (m : AE D) + (1 - es PP)), prod_idem hes _ P1 subset_rfl, hae]
  let A : (AE D)ˣ →* ℝ := ⟨⟨GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absFin D, absFin_one'⟩, GlobalTheory.SplitLinear.absFin_mul⟩
  have hA : GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absFin D x = A x := rfl
  rw [hA, hx', map_prod, ← Finset.prod_attach P1]
  exact Finset.prod_congr rfl fun PP _ => absFin_idemAt (hes PP.1 PP.2) m hm (u PP) rfl

end GlobalTheory.SplitIdeleModulus

end
