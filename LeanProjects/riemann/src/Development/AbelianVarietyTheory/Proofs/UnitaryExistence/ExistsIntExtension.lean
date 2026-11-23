import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.FlagBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.EigLatBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.InversionStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Signature
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIntMulMem
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped Matrix nonZeroDivisors
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G.Key ReciprocityTheory.ChartRestriction.G.Key.Chi

namespace GlobalTheory.SatDual

theorem exists_int_extension {L V : Type} [AddCommGroup L] [AddCommGroup V] [Module.Finite ℤ L]
    [Module.IsTorsionFree ℤ V] (q : L →ₗ[ℤ] V) (f : L →ₗ[ℤ] ℚ)
    (hf : ∀ x, q x = 0 → ∃ n : ℤ, f x = n) :
    ∃ g : L →ₗ[ℤ] ℤ, ∀ x, q x = 0 → (g x : ℚ) = f x := by
  haveI : Module.Finite ℤ (LinearMap.range q) := inferInstance
  haveI : Module.Free ℤ (LinearMap.range q) := Module.free_of_finite_type_torsion_free'
  obtain ⟨σ, hσ⟩ := Module.projective_lifting_property q.rangeRestrict LinearMap.id
    q.surjective_rangeRestrict
  let p : L →ₗ[ℤ] L := LinearMap.id - σ ∘ₗ q.rangeRestrict
  have hp : ∀ x, q (p x) = 0 := by
    intro x
    have h := congrArg Subtype.val (LinearMap.congr_fun hσ (q.rangeRestrict x))
    simp only [LinearMap.comp_apply, LinearMap.id_apply, LinearMap.codRestrict_apply] at h
    simp only [p, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, map_sub]
    exact sub_eq_zero.2 h.symm
  have hp' : ∀ x, q x = 0 → p x = x := by
    intro x hx
    have : q.rangeRestrict x = 0 := Subtype.ext hx
    simp [p, this]
  choose n hn using fun x => hf (p x) (hp x)
  refine ⟨AddMonoidHom.toIntLinearMap (AddMonoidHom.mk' n ?_), ?_⟩
  · intro a b
    have : ((n (a + b) : ℤ) : ℚ) = ((n a + n b : ℤ) : ℚ) := by
      push_cast
      rw [← hn, ← hn, ← hn, map_add, map_add]
    exact_mod_cast this
  · intro x hx
    change ((n x : ℤ) : ℚ) = f x
    rw [← hn, hp' x hx]

variable {E : Type} [Field E] [NumberField E]

theorem exists_int_smul_mem {V : Type} [AddCommGroup V] [Module E V] [Module (𝓞 E) V]
    [IsScalarTower (𝓞 E) E V] (Λ : Submodule (𝓞 E) V) (v : V)
    (hv : v ∈ Submodule.span E (Λ : Set V)) : ∃ N : ℤ, N ≠ 0 ∧ (N : E) • v ∈ Λ := by
  first
  | exact @_root_.GlobalTheory.IntMulMem.exists_int_mul_mem
  | exact _root_.GlobalTheory.IntMulMem.exists_int_mul_mem
  | (apply _root_.GlobalTheory.IntMulMem.exists_int_mul_mem <;> assumption)
  | (intros; apply _root_.GlobalTheory.IntMulMem.exists_int_mul_mem <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IntMulMem.exists_int_mul_mem <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IntMulMem.exists_int_mul_mem ..)

variable [IsCMField E]

theorem herm_smul_snd {r : ℕ} (G : Matrix (Fin r) (Fin r) E) (x y : Fin r → E) (a : E) :
    FD.herm G x (a • y) = FD.herm G x y * FD.cc a := by
  simp only [FD.herm, FD.cc, Pi.smul_apply, smul_eq_mul, map_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem pairing_pseudoBasis : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (r : ℕ) (ξ : E) (Gm : Matrix (Fin r) (Fin r) E) (φ : D.La →ₗ[𝓞 E] (Fin r → E)) (s : ℕ) (e : Fin s → (Fin r → E)) (c : Fin s → FractionalIdeal (𝓞 E)⁰ E), FD.cc ξ = -ξ → (Function.Injective φ ∧ Submodule.span E (Set.range φ) = ⊤ ∧ (∀ a b, FD.cc (Gm a b) = Gm b a) ∧ Gm.det ≠ 0 ∧ ∀ x y, ((D.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (ξ * FD.herm Gm (φ x) (φ y))) → LinearIndependent E e → (∀ a : Fin s → E, (∑ b, a b • e b) ∈ LinearMap.range φ ↔ ∀ b, a b ∈ c b) → ∀ y : Fin s → E, (∃ x, ∀ b, ξ * FD.herm Gm (φ x) (e b) = y b) ↔ ∀ b, ∀ a ∈ c b, ∃ n : ℤ, Algebra.trace ℚ E (y b * FD.cc a) = n := by
  intro E _ _ _ H D r ξ Gm φ s e c _ hφ he hc y
  obtain ⟨hinj, hspan, -, -, hEF⟩ := hφ
  have hsingle : ∀ (b : Fin s) (a : E), ∑ b', (Pi.single b a : Fin s → E) b' • e b' = a • e b := by
    intro b a
    rw [Finset.sum_eq_single b]
    · simp
    · intro b' _ hb'
      simp [Pi.single_eq_of_ne hb']
    · simp
  have hmem : ∀ (b : Fin s) (a : E), a • e b ∈ LinearMap.range φ ↔ a ∈ c b := by
    intro b a
    rw [← hsingle, hc]
    constructor
    · intro h
      simpa using h b
    · intro h b'
      by_cases hb : b' = b
      · subst hb
        simpa using h
      · rw [Pi.single_eq_of_ne hb]
        exact FractionalIdeal.zero_mem _
  constructor
  · rintro ⟨x, hx⟩ b a ha
    obtain ⟨z, hz⟩ := (hmem b a).2 ha
    refine ⟨D.EF x z, ?_⟩
    rw [hEF, hz, herm_smul_snd, ← _root_.mul_assoc, hx]
  · intro hy
    haveI := D.fin
    haveI : Module.Finite ℤ D.La := Module.Finite.trans (𝓞 E) D.La
    let j : (Fin s → E) →ₗ[E] (Fin r → E) := Fintype.linearCombination E e
    have hj : LinearMap.ker j = ⊥ :=
      LinearMap.ker_eq_bot.2 he.fintypeLinearCombination_injective
    obtain ⟨π, hπ⟩ := j.exists_leftInverse_of_injective hj
    have hπ' : ∀ a, π (j a) = a := fun a => LinearMap.congr_fun hπ a
    let q : D.La →ₗ[ℤ] (Fin r → E) := AddMonoidHom.toIntLinearMap
      (AddMonoidHom.mk' (fun x => φ x - j (π (φ x))) (by
        intro a b
        simp only [map_add]
        abel))
    let f : D.La →ₗ[ℤ] ℚ := AddMonoidHom.toIntLinearMap
      (AddMonoidHom.mk' (fun x => ∑ b, Algebra.trace ℚ E (y b * FD.cc (π (φ x) b))) (by
        intro a b
        simp only [map_add, Pi.add_apply, FD.cc, mul_add, Finset.sum_add_distrib]))
    have hq : ∀ x, q x = φ x - j (π (φ x)) := fun _ => rfl
    have hf : ∀ x, f x = ∑ b, Algebra.trace ℚ E (y b * FD.cc (π (φ x) b)) := fun _ => rfl
    obtain ⟨g, hg⟩ := exists_int_extension q f (by
      intro x hx
      rw [hq, sub_eq_zero] at hx
      have h1 : ∀ b, π (φ x) b ∈ c b := (hc _).1 ⟨x, hx⟩
      choose n hn using fun b => hy b _ (h1 b)
      refine ⟨∑ b, n b, ?_⟩
      rw [hf]
      push_cast
      exact Finset.sum_congr rfl fun b _ => hn b)
    obtain ⟨x, hx⟩ := D.unimod.2 g
    refine ⟨x, fun b => ?_⟩
    have key : ∀ a ∈ c b,
        Algebra.trace ℚ E ((ξ * FD.herm Gm (φ x) (e b) - y b) * FD.cc a) = 0 := by
      intro a ha
      obtain ⟨z, hz⟩ := (hmem b a).2 ha
      have hz' : φ z = j (Pi.single b a) := by
        rw [hz, ← hsingle]
        rfl
      have h1 := hg z (by rw [hq, hz', hπ', sub_self])
      rw [← hx, hEF, hz, herm_smul_snd, hf, hz', hπ', Finset.sum_eq_single b] at h1
      · rw [sub_mul, map_sub, _root_.mul_assoc, h1]
        simp
      · intro b' _ hb'
        simp [Pi.single_eq_of_ne hb', FD.cc]
      · simp
    rw [← sub_eq_zero]
    refine (traceForm_nondegenerate ℚ E).1 _ fun t => ?_
    obtain ⟨N, hN, hNt⟩ := exists_int_smul_mem (E := E) (LinearMap.range φ) (FD.cc t • e b)
      (by rw [LinearMap.coe_range, hspan]; trivial)
    rw [smul_smul, hmem] at hNt
    have h2 := key _ hNt
    have h3 : FD.cc ((N : E) * FD.cc t) = (N : ℚ) • t := by
      simp [FD.cc, Algebra.smul_def]
    rw [h3, mul_smul_comm, map_smul, smul_eq_zero] at h2
    rcases h2 with h2 | h2
    · exact absurd (by exact_mod_cast h2) hN
    · rw [Algebra.traceForm_apply]
      exact h2

end GlobalTheory.SatDual
