import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsFlipDet
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeCharEqProdLocalComponentsApproximating
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsBaseChangeFiniteAdeleRingEquiv
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinitePlaceIdempotentBaseChangeAdeles
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

namespace GlobalTheory.FlipCharFormula

variable {D : D7}

theorem fa_mul (a b : FiniteAdeleRing (𝓞 D.host.E) D.host.E) (Q : HeightOneSpectrum (𝓞 D.host.E)) :
    (a * b) Q = a Q * b Q := rfl
theorem fa_add (a b : FiniteAdeleRing (𝓞 D.host.E) D.host.E) (Q : HeightOneSpectrum (𝓞 D.host.E)) :
    (a + b) Q = a Q + b Q := rfl
theorem fa_sub (a b : FiniteAdeleRing (𝓞 D.host.E) D.host.E) (Q : HeightOneSpectrum (𝓞 D.host.E)) :
    (a - b) Q = a Q - b Q := rfl
theorem fa_one (Q : HeightOneSpectrum (𝓞 D.host.E)) :
    (1 : FiniteAdeleRing (𝓞 D.host.E) D.host.E) Q = 1 := rfl
theorem fa_natCast (n : ℕ) (Q : HeightOneSpectrum (𝓞 D.host.E)) :
    (n : FiniteAdeleRing (𝓞 D.host.E) D.host.E) Q = n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Nat.cast_succ, fa_add, ih, fa_one, Nat.cast_succ]
theorem fa_sum {α : Type*} (s : Finset α) (g : α → FiniteAdeleRing (𝓞 D.host.E) D.host.E)
    (Q : HeightOneSpectrum (𝓞 D.host.E)) : (∑ a ∈ s, g a) Q = ∑ a ∈ s, g a Q := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; rfl
  | insert a s ha ih => rw [Finset.sum_insert ha, fa_add, ih, Finset.sum_insert ha]

theorem finPart_incA (k : D.host.E) : finPart D (incA D k) = 1 ⊗ₜ k := rfl

theorem comp_of_isIdemAt (ι : Af ↥D.host.F ⊗[↥D.host.F] D.host.E ≃+* FiniteAdeleRing (𝓞 D.host.E) D.host.E)
    (h1 : ∀ (x : D.host.E), ι (1 ⊗ₜ[↥D.host.F] x) = (algebraMap D.host.E (FiniteAdeleRing (𝓞 D.host.E) D.host.E)) x)
    (h2 : ∀ (y : Af ↥D.host.F ⊗[↥D.host.F] D.host.E),
      y ∈ intAE D ↔ ∀ (P : HeightOneSpectrum (𝓞 D.host.E)), Valued.v ((ι y) P) ≤ 1)
    {e : AE D} {PP : HeightOneSpectrum (𝓞 D.host.E)} (he : Formalism.L2.NTheta.IsIdemAt e PP)
    (P : HeightOneSpectrum (𝓞 D.host.E)) :
    ι (finPart D e) P = if P = PP then 1 else 0 := by
  obtain ⟨⟨hee, -, -⟩, hP⟩ := he
  have hidem : ∀ Q, ι (finPart D e) Q = 0 ∨ ι (finPart D e) Q = 1 := by
    intro Q
    apply IsIdempotentElem.iff_eq_zero_or_one.mp
    show ι (finPart D e) Q * ι (finPart D e) Q = ι (finPart D e) Q
    rw [← fa_mul, ← map_mul, ← map_mul, hee]
  have key : ∀ x : 𝓞 D.host.E, x ≠ 0 →
      (x ∈ PP.asIdeal ↔ ∃ Q, ι (finPart D e) Q = 1 ∧ x ∈ Q.asIdeal) := by
    intro x hx
    rw [hP x hx, h2, map_mul, finPart_incA, map_mul, h1]
    have hQ : ∀ Q, (Valued.v ((ι (finPart D e) * algebraMap D.host.E (FiniteAdeleRing (𝓞 D.host.E) D.host.E)
        ((x : D.host.E))⁻¹) Q) ≤ 1 ↔ ¬ (ι (finPart D e) Q = 1 ∧ x ∈ Q.asIdeal)) := by
      intro Q
      rw [fa_mul]
      rcases hidem Q with h | h
      · rw [h, zero_mul]; simp
      · rw [h, one_mul]
        have hv : Valued.v ((algebraMap D.host.E (FiniteAdeleRing (𝓞 D.host.E) D.host.E) ((x : D.host.E))⁻¹) Q)
            = HeightOneSpectrum.valuation D.host.E Q ((x : D.host.E))⁻¹ :=
          HeightOneSpectrum.valuedAdicCompletion_eq_valuation' Q _
        have hx0 : HeightOneSpectrum.valuation D.host.E Q (x : D.host.E) ≠ 0 := by
          simpa using hx
        rw [hv, map_inv₀, inv_le_one₀ (zero_lt_iff.mpr hx0), ← not_lt,
          HeightOneSpectrum.valuation_lt_one_iff_mem]
        simp
    simp only [hQ, not_forall, not_not]
  have hne : ∀ Q, Q ≠ PP → ι (finPart D e) Q = 0 := by
    intro Q hQ
    rcases hidem Q with h | h
    · exact h
    · exfalso
      have hnle : ¬ Q.asIdeal ≤ PP.asIdeal := by
        intro hle
        apply hQ
        exact HeightOneSpectrum.ext (Q.isMaximal.eq_of_le PP.isPrime.ne_top hle)
      obtain ⟨x, hxQ, hxP⟩ := Set.not_subset.mp hnle
      have hx0 : x ≠ 0 := by rintro rfl; exact hxP PP.asIdeal.zero_mem
      exact hxP ((key x hx0).mpr ⟨Q, h, hxQ⟩)
  have hPP : ι (finPart D e) PP = 1 := by
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot PP.ne_bot
    obtain ⟨Q, hQ1, -⟩ := (key x hx0).mp hx
    by_cases hQ : Q = PP
    · rwa [hQ] at hQ1
    · rw [hne Q hQ] at hQ1; exact absurd hQ1 zero_ne_one
  split_ifs with h
  · rw [h, hPP]
  · exact hne P h

theorem infPart_of_isIdemAt {e : AE D} {PP : HeightOneSpectrum (𝓞 D.host.E)}
    (he : Formalism.L2.NTheta.IsIdemAt e PP) : infPart D e = 0 := by
  obtain ⟨⟨hee, hec, v, ε, ⟨α, rfl, -, -⟩, hsum⟩, -⟩ := he
  have h0 : infPart D (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α)) = 0 := by
    rw [Algebra.TensorProduct.algebraMap_apply]
    show (Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id (↥D.host.F) D.host.E)) ((pairA D.host.F 0 α : AF D.host.F) ⊗ₜ[↥D.host.F] (1 : D.host.E)) = 0
    rw [Algebra.TensorProduct.map_tmul]
    have : (fstA D.host.F) (pairA D.host.F 0 α) = 0 := rfl
    rw [this]
    exact TensorProduct.zero_tmul _ _
  have hs := congrArg (infPart D) hsum
  have hm := congrArg (infPart D) hec
  have hi := congrArg (infPart D) hee
  rw [map_add, h0] at hs
  rw [map_mul, map_zero] at hm
  rw [map_mul] at hi
  have hc : infPart D (cA D e) = - infPart D e :=
    eq_neg_iff_add_eq_zero.mpr (by rw [add_comm]; exact hs)
  rw [hc, mul_neg, hi, neg_eq_zero] at hm
  exact hm

set_option maxHeartbeats 800000 in

theorem char_inv_eq_prod_locK_of_flip : ∀ (D : D7) (V : HSp D) (χW : (AE D)ˣ →* Circle) (χ : Formalism.L2.Host.HChar D.host.E) (M₀ : ℕ) (u : D.host.Eˣ) (T : Finset (Formalism.L2.DIV.Pl D.host.E)) (eT : AE D) (x : (AE D)ˣ), ChrEq χW χ → (u : D.host.E) = ((M₀ : ℕ) : D.host.E) → IsIdemSum eT T → IsFlipDet V eT M₀ x → ((χW x : Circle) : ℂ)⁻¹ = ∏ PP ∈ T, ((χ.locK PP u : ℂˣ) : ℂ) ^ V.rank := by
  intro D V χW χ M₀ u T eT x hχ hu hT hx
  classical
  obtain ⟨ι, h1, h2, h3⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
  obtain ⟨N, hN, hprod⟩ := GlobalTheory.CharLocProd.char_eq_prod_locK D ι h1 h2
    (GlobalTheory.PlaceIdem.exists_isPlIdem D ι h1 h2 h3) χW χ hχ
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := hT
  unfold IsFlipDet at hx
  have heT : ∀ P, ι (finPart D (∑ PP ∈ T, es PP)) P = if P ∈ T then 1 else 0 := by
    intro P
    rw [map_sum, map_sum, fa_sum,
      Finset.sum_congr rfl (fun PP hPP => comp_of_isIdemAt ι h1 h2 (hes PP hPP) P)]
    exact Finset.sum_ite_eq T P (fun _ => (1 : HeightOneSpectrum.adicCompletion D.host.E P))
  have hinfT : infPart D (∑ PP ∈ T, es PP) = 0 := by
    rw [map_sum]
    exact Finset.sum_eq_zero (fun PP hPP => infPart_of_isIdemAt (hes PP hPP))
  have hinf : infPart D (x : AE D) = 1 := by
    have := congrArg (infPart D) hx
    rw [map_mul, map_add, map_mul, map_sub, hinfT, map_one, zero_mul, zero_add, sub_zero, mul_one] at this
    exact this
  have hcomp : ∀ P, ι (finPart D (x : AE D)) P *
      ((if P ∈ T then 1 else 0) * (((M₀ ^ V.rank : ℕ) : HeightOneSpectrum.adicCompletion D.host.E P))
        + (1 - if P ∈ T then 1 else 0)) = 1 := by
    intro P
    have h0 : ι (finPart D ((x : AE D) * ((∑ PP ∈ T, es PP) * ((M₀ ^ V.rank : ℕ) : AE D)
        + (1 - ∑ PP ∈ T, es PP)))) P = ι (finPart D 1) P := by
      rw [Nat.cast_pow, hx]
    simp only [map_mul, map_add, map_sub, map_one, map_natCast] at h0
    rw [fa_mul, fa_add, fa_mul, fa_sub, fa_one, fa_natCast, heT] at h0
    exact h0
  let k : HeightOneSpectrum (𝓞 D.host.E) → D.host.Eˣ := fun P => if P ∈ T then (u⁻¹) ^ V.rank else 1
  have hxk : ∀ P, ι (finPart D (x : AE D)) P =
      algebraMap D.host.E (HeightOneSpectrum.adicCompletion D.host.E P) (k P : D.host.E) := by
    intro P
    have hc := hcomp P
    by_cases hP : P ∈ T
    · rw [if_pos hP, one_mul, sub_self, add_zero] at hc
      rw [show k P = (u⁻¹) ^ V.rank from if_pos hP, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val, hu,
        map_pow, map_inv₀, map_natCast, eq_inv_of_mul_eq_one_left hc, Nat.cast_pow, inv_pow]
    · rw [if_neg hP, zero_mul, sub_zero, zero_add, mul_one] at hc
      rw [show k P = 1 from if_neg hP, Units.val_one, map_one]
      exact hc
  have hI : Ideal.span {((N : ℕ) : 𝓞 D.host.E)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hN.ne'
  have key := hprod x hinf (T ∪ (Ideal.finite_factors hI).toFinset) k
    (fun P _ => by
      rw [hxk P, sub_self, map_zero]
      exact ⟨HeightOneSpectrum.valuedAdicCompletion_eq_valuation' P _, zero_le'⟩)
    (fun P hP => by
      have hPT : P ∉ T := fun h => hP (Finset.mem_union_left _ h)
      refine ⟨?_, ?_⟩
      · rw [hxk P, show k P = 1 from if_neg hPT, Units.val_one, map_one, map_one]
      · intro hNP
        apply hP
        apply Finset.mem_union_right
        rw [Set.Finite.mem_toFinset]
        exact Ideal.dvd_span_singleton.mpr hNP)
  rw [key, ← Finset.prod_subset (Finset.subset_union_left)
    (fun P _ hPT => by rw [show k P = 1 from if_neg hPT, map_one, Units.val_one])]
  rw [Finset.prod_congr rfl (fun P hP => by
    rw [show k P = (u⁻¹) ^ V.rank from if_pos hP, map_pow, map_inv, Units.val_pow_eq_pow_val,
      Units.val_inv_eq_inv_val, inv_pow])]
  rw [Finset.prod_inv_distrib, inv_inv]

end GlobalTheory.FlipCharFormula
