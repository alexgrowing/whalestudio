import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.UnderTie

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.UG Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwU GlobalTheory.TwV
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeamTwist

theorem seamHom_smul {D : D7} {X : Fields} (s : Seam D X) {a b : ℕ} (r : X.E) (x : HomE D.host.E a b) :
    seamHom s (s.iE r • x) = r • seamHom s x := by
  refine LinearMap.ext fun w => funext fun l => s.iE.injective ?_
  rw [seamHom_apply]
  show s.iE r * x (fun k => s.iE (w k)) l = s.iE (r * seamHom s x w l)
  rw [map_mul, seamHom_apply]

theorem seamHom_smul_int {D : D7} {X : Fields} (s : Seam D X) {a b : ℕ} (r : 𝓞 X.E) (x : HomE D.host.E a b) :
    seamHom s (RingOfIntegers.mapRingEquiv s.iE r • x) = r • seamHom s x :=
  seamHom_smul s (r : X.E) x

theorem seamHom_mem_locP {D : D7} {X : Fields} (s : Seam D X) {a b : ℕ} (M : Submodule (𝓞 X.E) (HomE X.E a b))
    (M' : Submodule (𝓞 D.host.E) (HomE D.host.E a b)) (h : ∀ x, seamHom s x ∈ M ↔ x ∈ M') (P : HeightOneSpectrum (𝓞 X.E))
    (x : HomE D.host.E a b) :
    seamHom s x ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal M ↔ x ∈ Formalism.HermitianLatticesTheory.localization₂ (seamP s P).asIdeal M' := by
  show (∃ r ∈ P.asIdeal.primeCompl, r • seamHom s x ∈ M) ↔ ∃ r ∈ (seamP s P).asIdeal.primeCompl, r • x ∈ M'
  constructor
  · rintro ⟨r, hr, hm⟩
    refine ⟨RingOfIntegers.mapRingEquiv s.iE r, fun hh => hr ((mem_seamP s P r).1 hh), (h _).1 ?_⟩
    rwa [seamHom_smul_int]
  · rintro ⟨r, hr, hm⟩
    obtain ⟨r, rfl⟩ := (RingOfIntegers.mapRingEquiv s.iE).surjective r
    refine ⟨r, fun hh => hr ((mem_seamP s P r).2 hh), ?_⟩
    rw [← seamHom_smul_int]
    exact (h _).2 hm

theorem seamHom_mem_twO : ∀ {D : D7} {X : Fields} (s : Seam D X) {a b : ℕ} (M : Submodule (𝓞 X.E) (HomE X.E a b)) (M' : Submodule (𝓞 D.host.E) (HomE D.host.E a b)), (∀ x, seamHom s x ∈ M ↔ x ∈ M') → ∀ (cl : ℕ) (e : HeightOneSpectrum (𝓞 X.E) → ℤ) (e' : HeightOneSpectrum (𝓞 D.host.E) → ℤ), (∀ P, e' (seamP s P) = e P) → ∀ x, seamHom s x ∈ twist₂ M cl e ↔ x ∈ twist₂ M' cl e' := by
  intro D X s a b M M' h cl e e' he x
  have key : ∀ P : HeightOneSpectrum (𝓞 X.E),
      ((cl : X.E) ^ e P)⁻¹ • seamHom s x ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal M ↔
        ((cl : D.host.E) ^ e' (seamP s P))⁻¹ • x ∈ Formalism.HermitianLatticesTheory.localization₂ (seamP s P).asIdeal M' := by
    intro P
    rw [← seamHom_smul, seamHom_mem_locP s M M' h, he, map_inv₀, map_zpow₀, map_natCast]
  unfold twist₂
  rw [Submodule.mem_iInf, Submodule.mem_iInf]
  constructor
  · intro hx Q
    obtain ⟨P, rfl⟩ : ∃ P, seamP s P = Q :=
      (HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv s.iE)).surjective Q
    exact (key P).1 (hx P)
  · intro hx P
    exact (key P).2 (hx (seamP s P))

end GlobalTheory.SeamTwist
