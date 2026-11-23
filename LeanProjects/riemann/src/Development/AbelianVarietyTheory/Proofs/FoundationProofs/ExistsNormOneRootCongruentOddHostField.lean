import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsRootNear
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsOpenCongruenceIdelesAndRealFiniteParts
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.ProjectiveLattices.FamilyUniformisationBasePointOrthogonalBis

section
open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.AdLat.RootNear
open scoped TensorProduct

namespace GlobalTheory.OddRoot

theorem finite_root_odd (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (c : E ≃ₐ[F] E) (h2 : Module.finrank F E = 2) (hc : c ≠ 1)
    (hP : ∀ P : Ideal (𝓞 E), P.IsMaximal → ∃ t s : 𝓞 E, (s : E) = c (t : E) ∧ t - s ∉ P) (n : ℕ)
    (hn : Odd n) (u z : RA F E) (hz : z ∈ intHat F E) (huz : u - 1 = n • z)
    (hu : u * sg (FiniteAdeleRing (𝓞 F) F) c u = 1) :
    ∃ x y : RA F E, x ∈ intHat F E ∧ y ∈ intHat F E ∧ x * y = 1 ∧
      x = u * sg (FiniteAdeleRing (𝓞 F) F) c x ∧ ∃ p ∈ intHat F E, x - 1 = n • p := by
  have hu1 : u = 1 + n * z := by
    rw [nsmul_eq_mul] at huz
    linear_combination huz
  have huO : u ∈ intHat F E := by
    rw [hu1]
    exact add_mem (one_mem _) (mul_mem (natCast_mem _ n) hz)
  obtain ⟨x₁, hx₁, ⟨y₁, hy₁, hxy₁⟩, hr₁⟩ := GlobalTheory.T.exists_integral_unit_root_norm_one_adele F E c h2 hc hP u huO hu
  obtain ⟨e, f, hee, hef, hun⟩ :=
    exists_idem (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletionIntegers F) n
  obtain ⟨h, hh⟩ : ∃ h, e = 2 * h := by
    obtain ⟨g, hg⟩ := (hun (-1)).exists_right_inv
    obtain ⟨k, hk⟩ := hn
    refine ⟨-(k * e * g), ?_⟩
    rw [hk] at hg
    push_cast at hg
    linear_combination (-e) * hg - (2 * k + 1) * g * hee
  obtain ⟨y₀, hy₀⟩ := (unit_of_integral (inclHat F E) (inclHat_integral F E) (e * n) hun
    (inclHat F E h * ⟨z, hz⟩)).exists_right_inv
  have hse : sg (FiniteAdeleRing (𝓞 F) F) c (inclHat F E e : RA F E) = (inclHat F E e : RA F E) := by
    change sg (FiniteAdeleRing (𝓞 F) F) c (incl F e ⊗ₜ[F] (1 : E)) = incl F e ⊗ₜ[F] (1 : E)
    simp [sg]
  have hee' : (inclHat F E e : RA F E) * inclHat F E e = inclHat F E e := by
    rw [← Subring.coe_mul, ← map_mul, hee]
  have hef' : 1 - (inclHat F E e : RA F E) = n * inclHat F E f := by
    have := congrArg (fun t => (inclHat F E t : RA F E)) hef
    simpa using this
  have hh' : (inclHat F E e : RA F E) = 2 * inclHat F E h := by
    have := congrArg (fun t => (inclHat F E t : RA F E)) hh
    simp only [map_mul, map_ofNat] at this
    exact this
  have hy₀' : (1 + (inclHat F E e : RA F E) * n * (inclHat F E h * z)) * y₀ = 1 := by
    have := congrArg (fun t : intHat F E => (t : RA F E)) hy₀
    simpa using this
  have heO := (inclHat F E e).2
  have hfO := (inclHat F E f).2
  have hhO := (inclHat F E h).2
  have hy₀O := y₀.2
  generalize (inclHat F E e : RA F E) = e' at *
  generalize (inclHat F E f : RA F E) = f' at *
  generalize (inclHat F E h : RA F E) = h' at *
  generalize (y₀ : RA F E) = y' at *
  have hx₁' : x₁ ∈ intHat F E := hx₁
  have hy₁' : y₁ ∈ intHat F E := hy₁
  obtain ⟨w, hw⟩ : ∃ w, w = 1 + e' * n * (h' * z) := ⟨_, rfl⟩
  rw [← hw] at hy₀'
  have hwO : w ∈ intHat F E := by
    rw [hw]
    exact add_mem (one_mem _) (mul_mem (mul_mem heO (natCast_mem _ n)) (mul_mem hhO hz))
  have h2w : 2 * (e' * w) = e' * (1 + u) := by
    rw [hw, hu1]
    linear_combination (-(e' * e' * n * z)) * hh' + (n * z * (e' + 1)) * hee'
  have hr₀ : e' * w = u * sg (FiniteAdeleRing (𝓞 F) F) c (e' * w) := by
    have htwo : IsUnit (2 : RA F E) := by
      have := (IsUnit.mk0 (2 : F) two_ne_zero).map (algebraMap F (RA F E))
      rwa [map_ofNat] at this
    apply htwo.mul_left_cancel
    have := congrArg (sg (FiniteAdeleRing (𝓞 F) F) c) h2w
    rw [map_mul _ 2, map_ofNat, map_mul _ e' (1 + u), map_add, map_one, hse] at this
    linear_combination h2w - u * this - e' * hu
  have he1 := sub_mem (one_mem (intHat F E)) heO
  refine ⟨e' * w + (1 - e') * x₁, e' * y' + (1 - e') * y₁, add_mem (mul_mem heO hwO) (mul_mem he1 hx₁'),
    add_mem (mul_mem heO hy₀O) (mul_mem he1 hy₁'), ?_, ?_, e' * e' * (h' * z) + f' * (x₁ - 1),
    add_mem (mul_mem (mul_mem heO heO) (mul_mem hhO hz)) (mul_mem hfO (sub_mem hx₁' (one_mem _))), ?_⟩
  · linear_combination e' * hy₀' + (1 - e') * hxy₁ + (w * y' - w * y₁ - x₁ * y' + x₁ * y₁) * hee'
  · rw [map_add, map_mul _ (1 - e'), map_sub, map_one, hse]
    linear_combination hr₀ + (1 - e') * hr₁
  · rw [nsmul_eq_mul, hw]
    linear_combination (x₁ - 1) * hef'

end GlobalTheory.OddRoot
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Links Formalism.L2.JoinChr Formalism.L2.Host
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.OddRoot
open GlobalTheory.Member

theorem exists_root_odd : ∀ (D : D7) (N : ℕ), Odd N → ∀ u z : (Af D.host.F ⊗[D.host.F] D.host.E), z ∈ intAE D → u - 1 = N • z → u * sigR (Af D.host.F) D.sp.cm.sig u = 1 → ∃ x y : (Af D.host.F ⊗[D.host.F] D.host.E), x ∈ intAE D ∧ y ∈ intAE D ∧ x * y = 1 ∧ x = u * sigR (Af D.host.F) D.sp.cm.sig x ∧ ∃ p ∈ intAE D, x - 1 = N • p := by
  intro D N hN u z hz huz hu
  have hP : ∀ P : Ideal (𝓞 D.host.E), P.IsMaximal →
      ∃ t s : 𝓞 D.host.E, (s : D.host.E) = cF D (t : D.host.E) ∧ t - s ∉ P := by
    intro P hP
    obtain ⟨θ, t, ht, hθ⟩ := D.sp.cm.cmUnram.2.2 P hP
    exact ⟨θ, t, ht, hθ⟩
  have hc : cF D ≠ 1 := by
    intro h
    obtain ⟨P, hM⟩ := Ideal.exists_maximal (𝓞 D.host.E)
    obtain ⟨t, s, hs, hts⟩ := hP P hM
    rw [h] at hs
    have : s = t := Subtype.ext hs
    rw [this, sub_self] at hts
    exact hts P.zero_mem
  rw [GlobalTheory.IdeleParts.integralFiniteAdeles_eq_adelicCompletion_integers] at hz ⊢
  exact finite_root_odd D.host.F D.host.E (cF D) D.sp.cm.deg2 hc hP N hN u z hz huz hu

end GlobalTheory.OddRoot
