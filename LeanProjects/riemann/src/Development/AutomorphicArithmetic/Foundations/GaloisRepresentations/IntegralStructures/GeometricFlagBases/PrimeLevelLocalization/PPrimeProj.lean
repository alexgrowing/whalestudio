import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PrimeLevelLocalization.PrimeProj
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.CyclotomicConjugation.ConjLoc

noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU Formalism.L2.Host GlobalTheory.HeckeGal
open GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKDef
open GlobalTheory.LFun (KGL satEig)
open UpperTheory.Gal.CertificateRingHomMap (GUf Gam0 Plc GLw AfQ sim mat comp rat loc lev SameK IsCen Shape IsForm IsKap mOf)
open UpperTheory.Gal.W2.Seed (Arith Setup)
open scoped TensorProduct Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.Gal.Int.Geo.Pl

open UpperTheory.Gal.CertificateRingHomMap (Sim mem_Sim cj)
open GroundTheory.Global.AdeleBaseChange (finiteAdeleMap below)

def cutU {R : Type} [Ring R] (e : R) (he : e * e = e) (hc : ∀ x, x * e = e * x) : Rˣ →* Rˣ :=
  Units.map
    { toFun := fun x => e * x + (1 - e)
      map_one' := by simp
      map_mul' := fun x y => by
        have h1 : e * x * (e * y) = e * (x * y) := by rw [mul_assoc, ← mul_assoc x, hc, mul_assoc, ← mul_assoc, he]
        have h2 : e * x * (1 - e) = 0 := by rw [← hc, mul_assoc, mul_sub, mul_one, he, sub_self, mul_zero]
        have h3 : (1 - e) * (e * y) = 0 := by rw [← mul_assoc, sub_mul, one_mul, he, sub_self, zero_mul]
        have h4 : (1 - e) * (1 - e) = 1 - e := by rw [mul_sub, mul_one, sub_mul, one_mul, he, sub_self, sub_zero]
        rw [add_mul, mul_add, mul_add, h1, h2, h3, h4, add_zero, zero_add] }

theorem sim_cut {A B : Type} [CommRing A] [CommRing B] (σ : A →+* A) (i : B →+* A) (n : ℕ) (e : B) (he : e * e = e)
    (hσ : σ (i e) = i e) : ∃ π : Sim σ i n →* Sim σ i n, ∀ g, (π g).1.1.val = i e • g.1.1.val + (1 - i e) • 1 := by
  have hie : i e * i e = i e := by rw [← map_mul, he]
  have h1 : (i e • (1 : Matrix (Fin n) (Fin n) A)) * (i e • 1) = i e • 1 := by simp [smul_smul, hie]
  have h2 : ∀ x : Matrix (Fin n) (Fin n) A, x * (i e • 1) = (i e • 1) * x := by simp
  have hv : ∀ g : GL (Fin n) A, (cutU _ h1 h2 g).val = i e • g.val + (1 - i e) • 1 := fun g => by
    show (i e • (1 : Matrix (Fin n) (Fin n) A)) * g.val + (1 - i e • 1) = _
    simp [sub_smul]
  refine ⟨(((cutU _ h1 h2).prodMap (cutU e he fun x => mul_comm _ _)).comp (Sim σ i n).subtype).codRestrict _ fun g => ?_, fun g => hv _⟩
  have hg := mem_Sim.1 g.2
  refine mem_Sim.2 ?_
  show ((cutU _ h1 h2 g.1.1).val.map σ)ᵀ * (cutU _ h1 h2 g.1.1).val = i (e * g.1.2.val + (1 - e)) • 1
  have h3 : ((i e • g.1.1.val + (1 - i e) • (1 : Matrix (Fin n) (Fin n) A)).map σ)ᵀ = i e • (g.1.1.val.map σ)ᵀ + (1 - i e) • 1 := by
    ext a b
    by_cases hab : a = b
    · subst hab; simp [hσ]
    · simp [hσ, Matrix.one_apply, hab, Ne.symm hab]
  have h4 : i e * (1 - i e) = 0 := by rw [mul_sub, mul_one, hie, sub_self]
  have h5 : (1 - i e) * (1 - i e) = 1 - i e := by rw [sub_mul, one_mul, h4, sub_zero]
  rw [hv, h3, add_mul, mul_add, mul_add]
  simp only [smul_mul_smul_comm, hg, hie, h4, h5, mul_comm (1 - i e) (i e), zero_smul, add_zero, zero_add, smul_smul, mul_one,
    map_add, map_mul, map_sub, map_one, add_smul]

theorem nat_mem_cj {E : Type} [Field E] [NumberField E] [IsCMField E] (q : ℕ) (u : Plc E) :
    (q : 𝓞 E) ∈ (cj u).asIdeal ↔ (q : 𝓞 E) ∈ u.asIdeal := by
  have h := (CertificateRingHomMap.ZetaNonvanishing₂.conjLoc E 0 u).2.2.1 q
  have key : ∀ w : Plc E, (q : 𝓞 E) ∈ w.asIdeal ↔ Valued.v ((q : ℕ) : w.adicCompletion E) < 1 := fun w => by
    rw [← HeightOneSpectrum.valuation_lt_one_iff_mem (K := E), ← HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    have : (((q : ℕ) : E) : w.adicCompletion E) = (q : w.adicCompletion E) := map_natCast (algebraMap E (w.adicCompletion E)) q
    have h2 : ((q : 𝓞 E) : E) = q := map_natCast (algebraMap (𝓞 E) E) q
    rw [← this, ← h2]
  rw [key, key, h]

theorem primeProj_holds : PrimeProj := by
  intro E _ _ _ n q _
  let e : AfQ := ⟨fun v => if (q : 𝓞 ℚ) ∈ v.asIdeal then 1 else 0, Filter.Eventually.of_forall fun v => by
    show (if (q : 𝓞 ℚ) ∈ v.asIdeal then 1 else 0) ∈ v.adicCompletionIntegers ℚ
    split_ifs
    exacts [one_mem _, zero_mem _]⟩
  have hev : ∀ v, e v = if (q : 𝓞 ℚ) ∈ v.asIdeal then 1 else 0 := fun _ => rfl
  have he : e * e = e := FiniteAdeleRing.ext (R := 𝓞 ℚ) ℚ fun v => by
    show e v * e v = e v
    rw [hev]; split_ifs <;> simp
  have hp : ∀ w : Plc E, pLoc E w (finiteAdeleMap ℚ E e) = if (q : 𝓞 E) ∈ w.asIdeal then 1 else 0 := fun w => by
    show GroundTheory.Global.SemiLocal.completionMap (below ℚ w) w (e (below ℚ w)) = _
    have : (q : 𝓞 ℚ) ∈ (below ℚ w).asIdeal ↔ (q : 𝓞 E) ∈ w.asIdeal := by
      show algebraMap (𝓞 ℚ) (𝓞 E) q ∈ w.asIdeal ↔ _
      rw [map_natCast]
    rw [hev]
    by_cases h : (q : 𝓞 E) ∈ w.asIdeal <;> simp [h, this]
  have hσ : conjFin (GlobalTheory.SplitPts.conjE E) (finiteAdeleMap ℚ E e) = finiteAdeleMap ℚ E e :=
    FiniteAdeleRing.ext (R := 𝓞 E) E fun w => by
      have hq : ∀ b : Af E, b w = pLoc E w b := fun _ => rfl
      rw [hq, hq, pLoc_conjFin, hp, hp]
      have := nat_mem_cj q w
      by_cases h : (q : 𝓞 E) ∈ w.asIdeal <;> simp [h, this]
  obtain ⟨π, hπ⟩ := sim_cut (conjFin (GlobalTheory.SplitPts.conjE E)) (finiteAdeleMap ℚ E) n e he hσ
  have hc : ∀ (g : GUf E n) (w : Plc E) a b, (comp w g).val a b = pLoc E w (g.1.1.val a b) := fun _ _ _ _ => rfl
  refine ⟨π, fun g w => ⟨fun h => ?_, fun h => ?_⟩⟩ <;> ext a b <;> rw [hc, hπ]
  · simp [hp, h, hc]
  · by_cases hab : a = b <;> simp [hp, h, hab, Matrix.one_apply]

end UpperTheory.Gal.Int.Geo.Pl
