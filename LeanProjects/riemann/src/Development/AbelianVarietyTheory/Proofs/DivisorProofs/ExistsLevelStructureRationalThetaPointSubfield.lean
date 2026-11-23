import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.ExistsIsSymplecticFamilySpan
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.ThetaDescentLevel

theorem isThetaPt_reindex {S : Scheme.{0}} {P : PolAV S} {k : ℕ} {T : Over S} {I I' : Type}
    {x : I → (T ⟶ P.A)} {v : I → Γ(T.left, ⊤)} (H : IsThetaPt P k x v) (f : I' → I) :
    IsThetaPt P k (fun i => x (f i)) fun i => v (f i) := by
  refine ⟨H.1, H.2.1, fun p => ?_⟩
  obtain ⟨V, hV, th, s1, α, τ, U, s2, w, u, a1, a2, a3, a4, a5, a6, a7, a8⟩ := H.2.2 p
  exact ⟨V, hV, th, s1, α, τ, fun i => U (f i), fun i => s2 (f i), fun i => w (f i), u, a1, a2, a3, a4,
    fun i => a5 _, fun i => a6 _, fun i => a7 _, fun i => a8 _⟩

theorem exists_level : ∀ (F Ω : Type) [Field F] [IsAlgClosed F] [CharZero F] [Field Ω] [IsAlgClosed Ω] (em : F →+* Ω) (A : PolAV (Sp Ω)) (n J : ℕ), n.Prime → 1 ≤ J → ∀ (Ix : Type) (x : Ix → (baseOver (Sp Ω) ⟶ A.A)) (v : Ix → F), (∀ z : baseOver (Sp Ω) ⟶ A.A, z ^ ((n ^ J) ^ 2) = 1 → ∃ i, x i = z) → IsThetaPt A (n ^ J) x (fun i => (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom (em (v i))) → ∃ (ζ : Fˣ) (lev : Level A ((n ^ J) ^ 2) (unitOn (Units.map em.toMonoidHom ζ))) (v' : (Fin (2 * A.g) → ZMod ((n ^ J) ^ 2)) → F), IsPrimitiveRoot ζ ((n ^ J) ^ 2) ∧ IsThetaPt A (n ^ J) (GlobalTheory.levelPoint lev rfl) (fun a => (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom (em (v' a))) := by
  intro F Ω _ _ _ _ _ em A n J hn _ Ix x v hx hv
  have hF : (n : F) ≠ 0 := Nat.cast_ne_zero.2 hn.ne_zero
  have hΩ : (n : Ω) ≠ 0 := by
    rw [← map_natCast em]
    exact (map_ne_zero _).2 hF
  have hlev := nonempty_level_prime_pow GlobalTheory.abelianSchemeLaws_all.1 Ω A n (J * 2) hn hΩ
  rw [pow_mul] at hlev
  have hM : (n ^ J) ^ 2 ≠ 0 := pow_ne_zero _ (pow_ne_zero _ hn.ne_zero)
  generalize n ^ J = m at *
  have : NeZero (m ^ 2) := ⟨hM⟩
  have : NeZero ((m ^ 2 : ℕ) : F) := ⟨Nat.cast_ne_zero.2 hM⟩
  obtain ⟨z, hz⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot F (m ^ 2)
  have hζ := hz.isUnit_unit (NeZero.ne _)
  generalize (hz.isUnit (NeZero.ne _)).unit = ζ at hζ
  have inj : Function.Injective (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom :=
    (Scheme.ΓSpecIso (CommRingCat.of Ω)).symm.commRingCatIsoToRingEquiv.injective
  have hζ' : IsPrimitiveRoot (Units.map em.toMonoidHom ζ) (m ^ 2) :=
    hζ.map_of_injective (Units.map_injective em.injective)
  obtain ⟨lev⟩ := hlev (unitOn (Units.map em.toMonoidHom ζ)) (hζ'.map_of_injective (Units.map_injective inj))
  choose i hi using fun a => hx _ (ThetaPtDet.levelPoint_pow lev rfl a)
  refine ⟨ζ, lev, fun a => v (i a), hζ, ?_⟩
  have h := isThetaPt_reindex hv i
  rwa [show (fun a => x (i a)) = GlobalTheory.levelPoint lev rfl from funext hi] at h

end GlobalTheory.ThetaDescentLevel
