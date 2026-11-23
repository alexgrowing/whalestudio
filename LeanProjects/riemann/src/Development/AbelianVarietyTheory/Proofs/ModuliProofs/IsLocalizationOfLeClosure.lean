import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.TopAmpExists
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ArcFamSt
import Development.AbelianVarietyTheory.Definitions.Degenerations.HomExtSt
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CmModelCoefficientSubringDedekindCompatibleEmbed
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsCyclotomicBaseRingInvertingPrime
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsCoprimeTwoSubRtTwoAddRt

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM

namespace GlobalTheory.JoinRing

def coprimeNat (p : ℕ) (A : Type) [CommRing A] : Submonoid A where
  carrier := {x | ∃ m : ℕ, m.Coprime p ∧ x = m}
  one_mem' := ⟨1, by simp, by simp⟩
  mul_mem' := by
    rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    exact ⟨a * b, Nat.Coprime.mul_left ha hb, by simp⟩

theorem ne_zero_of_coprime {p m : ℕ} (hp : p.Prime) (hm : m.Coprime p) : m ≠ 0 := by
  rintro rfl
  exact hp.ne_one (by simpa using hm)

theorem coprimeNat_le {p : ℕ} (hp : p.Prime) (A : Type) [CommRing A] [IsDomain A] [CharZero A] :
    coprimeNat p A ≤ nonZeroDivisors A := by
  rintro _ ⟨m, hm, rfl⟩
  exact mem_nonZeroDivisors_of_ne_zero (Nat.cast_ne_zero.mpr (ne_zero_of_coprime hp hm))

theorem isLocalization_of_le_closure {p : ℕ} (hp : p.Prime) (A : Type) [CommRing A] (T : Subring ℂ) [Algebra A T]
    (hinj : Function.Injective (algebraMap A T)) (hinv : ∀ m : ℕ, m.Coprime p → (m : ℂ)⁻¹ ∈ T)
    (hT : T ≤ Subring.closure ({x | ∃ a, x = (algebraMap A T a : ℂ)} ∪ {x | ∃ n : ℕ, n.Coprime p ∧ x = (n : ℂ)⁻¹})) :
    IsLocalization (coprimeNat p A) T := by
  have h0 : ∀ m : ℕ, m.Coprime p → (m : ℂ) ≠ 0 := fun m hm => Nat.cast_ne_zero.mpr (ne_zero_of_coprime hp hm)
  have key : ∀ z ∈ Subring.closure ({x | ∃ a, x = (algebraMap A T a : ℂ)} ∪ {x | ∃ n : ℕ, n.Coprime p ∧ x = (n : ℂ)⁻¹}),
      ∃ m : ℕ, m.Coprime p ∧ ∃ a, z * m = (algebraMap A T a : ℂ) := by
    intro z hz
    induction hz using Subring.closure_induction with
    | mem x hx =>
      rcases hx with ⟨a, rfl⟩ | ⟨m, hm, rfl⟩
      · exact ⟨1, by simp, a, by simp⟩
      · exact ⟨m, hm, 1, by simp [h0 m hm]⟩
    | zero => exact ⟨1, by simp, 0, by simp⟩
    | one => exact ⟨1, by simp, 1, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨m, hm, a, ha⟩ := hx
      obtain ⟨k, hk, b, hb⟩ := hy
      refine ⟨m * k, Nat.Coprime.mul_left hm hk, a * k + b * m, ?_⟩
      simp only [map_add, map_mul, map_natCast]
      push_cast
      rw [← ha, ← hb]; ring
    | neg x _ hx =>
      obtain ⟨m, hm, a, ha⟩ := hx
      refine ⟨m, hm, -a, ?_⟩
      simp only [map_neg]
      push_cast
      rw [← ha]; ring
    | mul x y _ _ hx hy =>
      obtain ⟨m, hm, a, ha⟩ := hx
      obtain ⟨k, hk, b, hb⟩ := hy
      refine ⟨m * k, Nat.Coprime.mul_left hm hk, a * b, ?_⟩
      simp only [map_mul]
      push_cast
      rw [← ha, ← hb]; ring
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨_, m, hm, rfl⟩
    simp only [map_natCast]
    refine IsUnit.of_mul_eq_one ⟨_, hinv m hm⟩ (Subtype.ext ?_)
    simp [h0 m hm]
  · intro z
    obtain ⟨m, hm, a, ha⟩ := key z (hT z.2)
    refine ⟨(a, ⟨m, m, hm, rfl⟩), Subtype.ext ?_⟩
    simp only [map_natCast]
    push_cast
    exact ha
  · intro x y h
    exact ⟨1, by rw [hinj h]⟩

theorem inv_mem_ZP {p m : ℕ} (k : ℕ) (hm : m.Coprime p) : (m : ℂ)⁻¹ ∈ ZP p k :=
  Subring.subset_closure (Or.inr ⟨m, hm, rfl⟩)

open CycBase in

theorem isDedekindDomain_ZP {n p : ℕ} (e : ℕ) (hn : n.Prime) (hp : p.Prime) : IsDedekindDomain (ZP p (n ^ e)) := by
  haveI := Fact.mk hn
  have hk : n ^ e ≠ 0 := NeZero.ne _
  haveI : IsCyclotomicExtension {n ^ e} ℚ (CF (n ^ e)) := cyc
  haveI : NumberField (CF (n ^ e)) := IsCyclotomicExtension.numberField {n ^ e} ℚ _
  let io : 𝓞 (CF (n ^ e)) →+* ℂ := (CF (n ^ e)).val.toRingHom.comp (algebraMap _ (CF (n ^ e)))
  have hio : Function.Injective io := Subtype.val_injective.comp (RingOfIntegers.coe_injective)
  letI : Algebra (𝓞 (CF (n ^ e))) (ZP p (n ^ e)) := (io.codRestrict _ (mem_ZP p n e hn)).toAlgebra
  have : IsLocalization (coprimeNat p (𝓞 (CF (n ^ e)))) (ZP p (n ^ e)) := by
    refine isLocalization_of_le_closure hp _ _ (fun x y h => hio (congrArg (fun z : ZP p (n ^ e) => (z : ℂ)) h))
      (fun m hm => inv_mem_ZP _ hm) (Subring.closure_mono ?_)
    rintro x (rfl | h)
    · exact Or.inl ⟨(zF_prim hk).toInteger, rfl⟩
    · exact Or.inr h
  exact IsLocalization.isDedekindDomain _ (coprimeNat_le hp (𝓞 (CF (n ^ e)))) _

theorem isDedekindDomain_RZ_of_dvd {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) {S A e : ℕ}
    (hS : 0 < S) (hA : 0 < A) (h : A ∣ S ^ e) : IsDedekindDomain (RZ H S A) := by
  obtain ⟨l, rfl⟩ : ∃ l : Level H, l.A = A := ⟨GlobalTheory.HostModel.level H A hA, rfl⟩
  exact GlobalTheory.BaseRing.isDedekindDomain_RZ l hS h

theorem flat_inclusion {S T : Subring ℂ} (h : S ≤ T) [IsDedekindDomain S] : Flat (spMap (Subring.inclusion h)) := by
  letI : Algebra S T := (Subring.inclusion h).toAlgebra
  have htf : Module.IsTorsionFree S T := by
    rw [Module.isTorsionFree_iff_algebraMap_injective]
    exact fun x y h => Subtype.ext (congrArg (fun z : T => (z : ℂ)) h)
  exact Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr (inferInstance : Module.Flat S T))

theorem noetherian_preimmersion {p : ℕ} (hp : p.Prime) {S T : Subring ℂ} (h : S ≤ T) [IsNoetherianRing S]
    (hinv : ∀ m : ℕ, m.Coprime p → (m : ℂ)⁻¹ ∈ T)
    (hT : T ≤ Subring.closure ((S : Set ℂ) ∪ {x | ∃ n : ℕ, n.Coprime p ∧ x = (n : ℂ)⁻¹})) :
    IsNoetherianRing T ∧ IsPreimmersion (spMap (Subring.inclusion h)) := by
  letI : Algebra S T := (Subring.inclusion h).toAlgebra
  have hL : IsLocalization (coprimeNat p S) T := by
    refine isLocalization_of_le_closure hp _ _ (fun x y h => Subtype.ext (congrArg (fun z : T => (z : ℂ)) h))
      hinv (hT.trans (Subring.closure_mono ?_))
    rintro x (hx | hx)
    · exact Or.inl ⟨⟨x, hx⟩, rfl⟩
    · exact Or.inr hx
  exact ⟨IsLocalization.isNoetherianRing (coprimeNat p S) _ inferInstance,
    IsPreimmersion.of_isLocalization (R := S) (S := T) (coprimeNat p S)⟩

theorem join_rings : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (n N p : ℕ), n.Prime → (∃ j, 1 ≤ j ∧ N = n ^ j) → p.Prime → p ≠ n → IsDedekindDomain (RZ H n N) ∧ IsNoetherianRing ↥(RZ H n N ⊔ ZP p N) ∧ Flat (spMap (Subring.inclusion (le_sup_left : RZ H n N ≤ RZ H n N ⊔ ZP p N))) ∧ IsPreimmersion (spMap (Subring.inclusion (le_sup_left : RZ H n N ≤ RZ H n N ⊔ ZP p N))) ∧ Flat (spMap (Subring.inclusion (le_sup_right : ZP p N ≤ RZ H n N ⊔ ZP p N))) := by
  rintro E _ _ _ H n N p hn ⟨j, -, hN⟩ hp -
  have hD : IsDedekindDomain (RZ H n N) :=
    isDedekindDomain_RZ_of_dvd H (e := j) hn.pos (hN ▸ pow_pos hn.pos j) (hN ▸ dvd_rfl)
  have hZ : IsDedekindDomain (ZP p N) := hN ▸ isDedekindDomain_ZP j hn hp
  have h := noetherian_preimmersion hp (le_sup_left : RZ H n N ≤ RZ H n N ⊔ ZP p N)
    (fun m hm => (le_sup_right : ZP p N ≤ _) (inv_mem_ZP _ hm))
    (sup_le (fun x hx => Subring.subset_closure (Or.inl hx)) (Subring.closure_mono (by
      rintro x (rfl | h)
      · exact Or.inl (RZ.ze H n N).2
      · exact Or.inr h)))
  exact ⟨hD, h.1, flat_inclusion _, h.2, flat_inclusion _⟩

end GlobalTheory.JoinRing
