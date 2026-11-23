import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.StConj
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.AdjoinForm
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ConjugateElement

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RoadWGeo
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso)
open UpperTheory.Gal.TP.Sub (Cl Above unrPol)
open UpperTheory.Gal.crystallineComparison (GenericMul rootPol)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep Formalism.UG GlobalTheory.DefU
open UpperTheory.Gal.Int.Div

private theorem conj_alt_bis {E : Type} [Field E] [NumberField E] [IsCMField E] {d : ℕ} (hd : 0 < d) {x : E}
    (hx : x ^ 2 = -(d : E)) : IsCMField.complexConj E x = -x :=
  _root_.UpperTheory.Reformulated.B.CMConjNegOfSqEqNegPos.conj_alt_bis hd hx

private theorem adjoin_form {E : Type} [Field E] [NumberField E] {d : ℕ} (hd : 0 < d) {x : E}
    (hx : x ^ 2 = -(d : E)) (y : E) (hy : y ∈ IntermediateField.adjoin ℚ {x}) :
    ∃ s t : ℚ, y = (s : E) + (t : E) * x :=
  _root_.UpperTheory.Reformulated.B.AdjoinForm.adjoin_form hd hx y hy

private theorem two_cases {R : Type} [CommRing R] (T : R → Prop) (hT : ∀ a b, T a → T b → T (a + b))
    (I J : Ideal R) (h : ∀ y, T y → y ∈ I ∨ y ∈ J) : (∀ y, T y → y ∈ I) ∨ (∀ y, T y → y ∈ J) := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨⟨a, ha, haI⟩, b, hb, hbJ⟩ := hcon
  have haJ : a ∈ J := (h a ha).resolve_left haI
  have hbI : b ∈ I := (h b hb).resolve_right hbJ
  rcases h (a + b) (hT a b ha hb) with h1 | h1
  · exact haI ((Submodule.add_mem_iff_left I hbI).mp h1)
  · exact hbJ ((Submodule.add_mem_iff_right J haJ).mp h1)

private theorem core {R : Type} [CommRing R] (c : R ≃+* R) (hcc : ∀ y, c (c y) = y) (K : R → Prop)
    (hKa : ∀ a b, K a → K b → K (a + b)) (hKc : ∀ y, K y → K (c y)) (W W' : Ideal R)
    (h1 : ∀ y, K y → y ∈ W → y ∈ W' ∨ c y ∈ W') (h2 : ∀ y, K y → y ∈ W' → y ∈ W ∨ c y ∈ W) :
    (∀ y, K y → (y ∈ W ↔ y ∈ W')) ∨ (∀ y, K y → (c y ∈ W ↔ y ∈ W')) := by
  have A := two_cases (fun y => K y ∧ y ∈ W') (fun a b ha hb => ⟨hKa a b ha.1 hb.1, W'.add_mem ha.2 hb.2⟩)
    W (W.comap (c : R →+* R)) (fun y hy => by simpa [Ideal.mem_comap] using h2 y hy.1 hy.2)
  have B := two_cases (fun y => K y ∧ y ∈ W) (fun a b ha hb => ⟨hKa a b ha.1 hb.1, W.add_mem ha.2 hb.2⟩)
    W' (W'.comap (c : R →+* R)) (fun y hy => by simpa [Ideal.mem_comap] using h1 y hy.1 hy.2)
  simp only [Ideal.mem_comap, RingHom.coe_coe] at A B
  rcases A with A | A <;> rcases B with B | B
  · exact Or.inl fun y hy => ⟨fun h => B y ⟨hy, h⟩, fun h => A y ⟨hy, h⟩⟩
  · refine Or.inl fun y hy => ⟨fun h => ?_, fun h => A y ⟨hy, h⟩⟩
    have h3 := A (c y) ⟨hKc y hy, B y ⟨hy, h⟩⟩
    have h4 := B (c y) ⟨hKc y hy, h3⟩
    rwa [hcc] at h4
  · refine Or.inr fun y hy => ⟨fun h => ?_, fun h => A y ⟨hy, h⟩⟩
    have h3 := B (c y) ⟨hKc y hy, h⟩
    have h4 := A (c y) ⟨hKc y hy, h3⟩
    rw [hcc] at h4
    exact B y ⟨hy, h4⟩
  · refine Or.inr fun y hy => ⟨fun h => ?_, fun h => A y ⟨hy, h⟩⟩
    have h3 := B (c y) ⟨hKc y hy, h⟩
    rwa [hcc] at h3

private theorem int_mem {R : Type} [CommRing R] {l : ℕ} (hl : l.Prime) {u u' : Ideal R} (hu : u ≠ ⊤)
    (hlu : (l : R) ∈ u) (hlu' : (l : R) ∈ u') {n : ℤ} (hn : (n : R) ∈ u) : (n : R) ∈ u' := by
  by_cases hd : (l : ℤ) ∣ n
  · obtain ⟨k, rfl⟩ := hd
    push_cast
    exact u'.mul_mem_right _ hlu'
  · have hp : Prime (l : ℤ) := Nat.prime_iff_prime_int.mp hl
    obtain ⟨a, b, hab⟩ : IsCoprime (l : ℤ) n := (Prime.coprime_iff_not_dvd hp).mpr hd
    exfalso
    apply hu
    rw [Ideal.eq_top_iff_one]
    have : ((a * l + b * n : ℤ) : R) = 1 := by rw [hab]; simp
    rw [← this]
    push_cast
    exact u.add_mem (u.mul_mem_left _ hlu) (u.mul_mem_left _ hn)

private theorem norm_int {E : Type} [Field E] [NumberField E] [IsCMField E] {d : ℕ} (hd : 0 < d) {x : E}
    (hx : x ^ 2 = -(d : E)) (y y' : 𝓞 E) (hy : (y : E) ∈ IntermediateField.adjoin ℚ {x})
    (hy' : (y' : E) = IsCMField.complexConj E (y : E)) : ∃ n : ℤ, y * y' = (n : 𝓞 E) := by
  obtain ⟨s, t, hst⟩ := adjoin_form hd hx _ hy
  have hc := conj_alt_bis hd hx
  have hq : ((y * y' : 𝓞 E) : E) = algebraMap ℚ E (s ^ 2 + d * t ^ 2) := by
    have h1 : (y' : E) = (s : E) - t * x := by
      rw [hy', hst, map_add, map_mul, hc]
      simp [sub_eq_add_neg]
    change (y : E) * (y' : E) = _
    rw [h1, hst, eq_ratCast]
    push_cast
    linear_combination (-(t : E) ^ 2) * hx
  have hI : IsIntegral ℤ (algebraMap ℚ E (s ^ 2 + d * t ^ 2)) := hq ▸ RingOfIntegers.isIntegral_coe _
  have hI' : IsIntegral ℤ (s ^ 2 + d * t ^ 2 : ℚ) := (isIntegral_algebraMap_iff (algebraMap ℚ E).injective).mp hI
  obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.mp hI'
  refine ⟨n, RingOfIntegers.ext ?_⟩
  rw [hq, ← hn]
  simp

private theorem two_places {E : Type} [Field E] [NumberField E] [IsCMField E] {l d : ℕ} (hl : l.Prime) (hd : 0 < d) {x : E}
    (hx : x ^ 2 = -(d : E)) (u u' : HeightOneSpectrum (𝓞 E)) (hu : ((l : ℕ) : 𝓞 E) ∈ u.asIdeal)
    (hu' : ((l : ℕ) : 𝓞 E) ∈ u'.asIdeal) (y y' : 𝓞 E) (hy : (y : E) ∈ IntermediateField.adjoin ℚ {x})
    (hy' : (y' : E) = IsCMField.complexConj E (y : E)) (hm : y ∈ u.asIdeal) : y ∈ u'.asIdeal ∨ y' ∈ u'.asIdeal := by
  obtain ⟨n, hn⟩ := norm_int hd hx y y' hy hy'
  have h1 : (n : 𝓞 E) ∈ u.asIdeal := hn ▸ u.asIdeal.mul_mem_right _ hm
  have h2 := int_mem hl u.isPrime.ne_top hu hu' h1
  rw [← hn] at h2
  exact u'.isPrime.mem_or_mem h2

theorem UpperTheory.Gal.Int.Div.sameOr_of :
    CplMem → SameOr := by
  intro hC E _ _ _ l d hl hd x hx w w' hw hw'
  let c : 𝓞 E ≃+* 𝓞 E := RingOfIntegers.mapRingEquiv (IsCMField.complexConj E).toRingEquiv
  have hcE : ∀ y : 𝓞 E, ((c y : 𝓞 E) : E) = IsCMField.complexConj E (y : E) := fun y => rfl
  have hcc : ∀ y, c (c y) = y := fun y => RingOfIntegers.ext (by
    rw [hcE, hcE, IsCMField.complexConj_apply_apply])
  have hKc : ∀ y : 𝓞 E, (y : E) ∈ IntermediateField.adjoin ℚ {x} → ((c y : 𝓞 E) : E) ∈ IntermediateField.adjoin ℚ {x} := by
    intro y hy
    obtain ⟨s, t, hst⟩ := adjoin_form hd hx _ hy
    have hxK : x ∈ IntermediateField.adjoin ℚ {x} := IntermediateField.mem_adjoin_simple_self ℚ x
    have h1 : ((c y : 𝓞 E) : E) = (s : E) + ((-t : ℚ) : E) * x := by
      rw [hcE, hst, map_add, map_mul, conj_alt_bis hd hx]
      simp
    rw [h1]
    exact add_mem (SubfieldClass.ratCast_mem _ s) (mul_mem (SubfieldClass.ratCast_mem _ _) hxK)
  have key := core c hcc (fun y : 𝓞 E => (y : E) ∈ IntermediateField.adjoin ℚ {x})
    (fun a b ha hb => by simpa using add_mem ha hb) hKc w.asIdeal w'.asIdeal
    (fun y hy hm => two_places hl hd hx w w' hw hw' y (c y) hy (hcE y) hm)
    (fun y hy hm => two_places hl hd hx w' w hw' hw y (c y) hy (hcE y) hm)
  rcases key with h | h
  · exact Or.inl fun y hy => h y hy
  · exact Or.inr fun y hy => (hC E w y (c y) (hcE y)).trans (h y hy)
