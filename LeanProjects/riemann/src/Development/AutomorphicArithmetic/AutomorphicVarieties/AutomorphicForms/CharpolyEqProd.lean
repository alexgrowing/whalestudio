import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.GuDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.UniversalOrdinaryDeterminantRing
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RecProdRecSatakeLL
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RecOfRecLiteralStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChebotarevDegreeOne
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChebotarevDegreeOneIffCheb
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.FrobeniusEigenvaluesTwist
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.GaloisRepIrreducibilityCriterion
import Formalism.SharpRestriction.LevelLetterCocycles.LinearIndependentSmulOfNeZero
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CyclotomicCharacterFourth

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V.Af.Gu UpperTheory.V.Af.Bc

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Af.Es

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {l : ℕ} [Fact l.Prime]

theorem exists_rec (P : Hypotheses₂) {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} (h : IsPlaceOver A w) :
    ∃ rc : IrrGL (w.adicCompletion E) → WD h, IsRec h rc := by
  have L := P.litN.loc
  obtain ⟨rc, hrc⟩ := L.llc E Ω A w h
  exact ⟨rc, GlobalTheory.T.rec_of_rec_literal L.dzc L.dzi L.exh L.multi L.cos L.zel L.geo L.bz E Ω A w h rc hrc⟩

omit [IsAlgClosure E Ω] in
theorem cyc_cont : Continuous (cycBar E Ω l) :=
  _root_.UpperTheory.Reformulated.B.CyclotomicCharacterContinuity.cyc_cont

theorem charEig_cyc (ι : Qbar l ≃+* ℂ) {w : HeightOneSpectrum (𝓞 E)} (hw : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) (j : ℕ) :
    CharEig ι (cycBar E Ω l ^ (-(j : ℤ))) w ((normV w : ℂ) ^ j) := by
  intro A hA
  refine ⟨fun s hs => ?_, fun σ hσ => ?_⟩
  · have h1 : cycZ E Ω l s = 1 := Units.ext (PadicInt.ext_of_toZModPow.mp fun n => by
      rw [cycZ_toZModPow_eq hw hA (q := 1) (fun x hx => by simpa using hs.2 x hx) n]
      simp)
    rw [MonoidHom.zpow_apply, cycBar, MonoidHom.comp_apply, h1, map_one, one_zpow]
  · have h2 : ((cycBar E Ω l σ : (Qbar l)ˣ) : Qbar l) = (normV w : ℕ) := by
      change algebraMap ℚ_[l] (Qbar l) (PadicInt.Coe.ringHom ((cycZ E Ω l σ : ℤ_[l]ˣ) : ℤ_[l])) = _
      rw [cycZ_of_isFrob hw hA hσ, map_natCast, map_natCast]
    rw [MonoidHom.zpow_apply, map_inv, inv_zpow', neg_neg, zpow_natCast, Units.val_pow_eq_pow_val, h2, map_pow, map_natCast]

theorem map_sum_ms {I X Y : Type} [Fintype I] (B : I → Multiset X) (f : X → Y) :
    (∑ i, B i).map f = ∑ i, (B i).map f := map_sum (Multiset.mapAddMonoidHom f) B Finset.univ

theorem algSat_satTot (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) {c : ℕ} (d : Fin c → ℕ) (S : Fin c → Multiset ℂˣ) :
    algSat n (normV w) (satTot w d S) = ∑ x : Σ i, Fin (d i),
      ((S x.1).map fun α : ℂˣ => (α : ℂ) * ((normV w : ℕ) : ℂ) ^ (-((((ex n (d x.1) 0 : ℤ) : ℝ) / 2 : ℝ) : ℂ))).map
        (· * (normV w : ℂ) ^ (x.2 : ℕ)) := by
  have e : ∀ B : Multiset ℂˣ, algSat n (normV w) B =
      B.map fun α : ℂˣ => (((normV w : ℝ) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ) * (α : ℂ) := fun B => by
    simp [algSat, Multiset.bind_singleton, Multiset.map_map]
  have hq : ((normV w : ℕ) : ℂ) ≠ 0 := coe_qPow_one (w := w) ▸ (qPow w 1).ne_zero
  rw [e, satTot, Fintype.sum_sigma, map_sum_ms]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_sum_ms]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Multiset.map_map, Multiset.map_map]
  refine Multiset.map_congr rfl fun α _ => ?_
  simp only [Function.comp_apply, Units.val_mul, coe_qPow]
  rw [Complex.ofReal_cpow (Nat.cast_nonneg _), ← Complex.cpow_natCast, mul_assoc, ← Complex.cpow_add _ _ hq, mul_left_comm,
    Complex.ofReal_natCast, ← Complex.cpow_add _ _ hq]
  congr 2
  simp only [ex]
  push_cast
  ring

private theorem contCoeff {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] (n i : ℕ) :
    Continuous fun M : Matrix (Fin n) (Fin n) K => M.charpoly.coeff i := by
  have h : (fun M : Matrix (Fin n) (Fin n) K => M.charpoly.coeff i) =
      fun M => MvPolynomial.eval (fun ij : Fin n × Fin n => M ij.1 ij.2)
        ((Matrix.charpoly.univ K (Fin n)).coeff i) := by
    funext M
    exact (Matrix.charpoly.univ_coeff_eval₂Hom (Fin n) (RingHom.id K) (fun ij : Fin n × Fin n => M ij.1 ij.2) i).symm
  rw [h]
  exact (MvPolynomial.continuous_eval _).comp
    (continuous_pi fun ij => (continuous_apply ij.2).comp (continuous_apply ij.1))

private theorem contProd {K T I : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] [TopologicalSpace T]
    (s : Finset I) (f : I → T → K[X]) (hf : ∀ i m, Continuous fun x => (f i x).coeff m) (m : ℕ) :
    Continuous fun x => (∏ i ∈ s, f i x).coeff m := by
  classical
  induction s using Finset.induction_on generalizing m with
  | empty => simpa using continuous_const
  | insert i s hi ih =>
    simp only [Finset.prod_insert hi, Polynomial.coeff_mul]
    exact continuous_finset_sum _ fun p _ => (hf i p.1).mul (ih p.2)

theorem charpoly_eq_prod (ι : Qbar l ≃+* ℂ) {I : Type} [Fintype I] {n : ℕ} {a : I → ℕ} (ρ : G E Ω →* GL (Fin n) (Qbar l))
    (r : ∀ i, G E Ω →* GL (Fin (a i)) (Qbar l)) (hρ : Continuous ρ) (hr : ∀ i, Continuous (r i))
    (hw : ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, w.asIdeal.inertiaDeg ℤ = 1 →
      ∃ B : I → Multiset ℂ, FrobEig ι ρ w (∑ i, B i) ∧ ∀ i, FrobEig ι (r i) w (B i)) (g : G E Ω) :
    (ρ g : Matrix (Fin n) (Fin n) (Qbar l)).charpoly = ∏ i, (r i g : Matrix (Fin (a i)) (Fin (a i)) (Qbar l)).charpoly := by
  have hD := GlobalTheory.Published.ChebotarevDegreeOne.dense (F := E) (Ω := Ω) GlobalTheory.Published.chebotarevDegreeOne'
    (Filter.eventually_cofinite.1 hw)
  suffices hc : ∀ g : G E Ω, (ρ g⁻¹ : Matrix (Fin n) (Fin n) (Qbar l)).charpoly =
      ∏ i, (r i g⁻¹ : Matrix (Fin (a i)) (Fin (a i)) (Qbar l)).charpoly by simpa using hc g⁻¹
  intro g
  ext m
  have h1 : Continuous fun g : G E Ω => (ρ g⁻¹ : Matrix (Fin n) (Fin n) (Qbar l)).charpoly.coeff m :=
    (contCoeff n m).comp (Units.continuous_val.comp (hρ.comp continuous_inv))
  have h2 := contProd Finset.univ (fun i (g : G E Ω) => (r i g⁻¹ : Matrix (Fin (a i)) (Fin (a i)) (Qbar l)).charpoly)
    (fun i m => (contCoeff (a i) m).comp (Units.continuous_val.comp ((hr i).comp continuous_inv))) m
  refine congrFun (Continuous.ext_on hD h1 h2 ?_) g
  rintro σ ⟨v, hv, hd, A, hA, hσ⟩
  obtain ⟨B, hB, hB'⟩ := not_not.1 hv hd
  have h : (ρ σ⁻¹ : Matrix (Fin n) (Fin n) (Qbar l)).charpoly.map ι.toRingHom =
      (∏ i, (r i σ⁻¹ : Matrix (Fin (a i)) (Fin (a i)) (Qbar l)).charpoly).map ι.toRingHom := by
    rw [(hB A hA).2 σ hσ, Polynomial.map_prod, map_sum_ms, Multiset.prod_sum]
    exact Finset.prod_congr rfl fun i _ => ((hB' i A hA).2 σ hσ).symm
  have h' := Polynomial.map_injective ι.toRingHom ι.injective h
  simp only [h']

end UpperTheory.V.Af.Es
