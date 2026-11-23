import Mathlib
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
import Development.AbelianVarietyTheory.Definitions.Uniformization.WCompat
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat
import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CubWeilOneLeft
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PerfectPairingOrthogonalOfCard
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.GenericFibreCardTorsionCubicalPairingPerfectStatement

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UU

theorem mem_of_orthogonal_of_card {F : Type} [Field F] {M U : Type} [CommGroup M] [CommGroup U] (φ : U →* Fˣ)
    (hφ : Function.Injective φ) (N : ℕ) (w : M → M → U → Prop)
    (hex : ∀ x y, x ^ N = 1 → y ^ N = 1 → ∃! ζ, w x y ζ)
    (hmul : ∀ x x' y ζ ζ', w x y ζ → w x' y ζ' → w (x * x') y (ζ * ζ'))
    (hsymm : ∀ x y ζ, w x y ζ → w y x ζ⁻¹)
    (hfin : Nat.card {x : M // x ^ N = 1} ≠ 0)
    (hnd : ∀ x, x ^ N = 1 → (∀ y, y ^ N = 1 → w x y 1) → x = 1)
    (T H : Subgroup M) (hT : ∀ x ∈ T, x ^ N = 1) (hH : ∀ x ∈ H, x ^ N = 1)
    (hc : Nat.card T * Nat.card H = Nat.card {x : M // x ^ N = 1})
    (hTH : ∀ x ∈ T, ∀ y ∈ H, w x y 1) (x : M) (hx : x ^ N = 1) (hxH : ∀ y ∈ H, w x y 1) : x ∈ T := by
  let K : Subgroup M := (powMonoidHom N : M →* M).ker
  have hK : ∀ a, a ∈ K ↔ a ^ N = 1 := fun a => Iff.rfl
  have hcK : Nat.card K = Nat.card {x : M // x ^ N = 1} := rfl
  have : Finite K := Nat.finite_of_card_ne_zero (hcK ▸ hfin)
  have hex' : ∀ a b : K, ∃ ζ, w a b ζ := fun a b => (hex a b a.2 b.2).exists
  choose v hv using hex'
  have hu : ∀ (a b : K) ζ, w a b ζ → v a b = ζ := fun a b ζ h => (hex a b a.2 b.2).unique (hv a b) h
  have h1 : ∀ a a' b : K, v (a * a') b = v a b * v a' b :=
    fun a a' b => hu _ _ _ (hmul _ _ _ _ _ (hv a b) (hv a' b))
  have hs : ∀ a b : K, v b a = (v a b)⁻¹ := fun a b => hu _ _ _ (hsymm _ _ _ (hv a b))
  have hTK : T ≤ K := hT
  have hHK : H ≤ K := hH
  have key := (GlobalTheory.perfectPairing_orthogonal_of_card F K (fun a b => φ (v a b))
    (fun a a' b => by rw [h1, map_mul])
    (fun a b b' => by rw [hs (b * b') a, h1, mul_inv, ← hs, ← hs, map_mul])
    (fun a ha => Subtype.ext (hnd a a.2 fun y hy => by
      have h := hv a ⟨y, hy⟩
      rwa [hφ ((ha ⟨y, hy⟩).trans φ.map_one.symm)] at h))
    (T.subgroupOf K) (H.subgroupOf K)
    (fun t ht h hh => by rw [hu _ _ _ (hTH t ht h hh), map_one])
    (by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTK).toEquiv,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHK).toEquiv, hc, hcK])).1 ⟨x, hx⟩
  exact key.1 fun h hh => by rw [hu ⟨x, hx⟩ h _ (hxH h hh), map_one]

theorem mem_of_cubWeil_orthogonal : Laws → AllSet fun {V} _ _ _ {A} {G} _ _ s => ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing V) F] (N : ℕ), 1 ≤ N → ∀ T H : Subgroup (TF (R := V) F ⟶ G), (∀ x ∈ T, x ^ N = 1) → (∀ x ∈ H, x ^ N = 1) → Nat.card T * Nat.card H = N ^ (2 * A.g) → (∀ x ∈ T, ∀ y ∈ H, CubWeil s.P.c N x y 1) → ∀ x, x ^ N = 1 → (∀ y ∈ H, CubWeil s.P.c N x y 1) → x ∈ T := by
  intro hL V _ _ _ A G _ _ s F _ _ _ N hN T H hT hH hc hTH x hx hxH
  obtain ⟨hcard, hnd⟩ := GlobalTheory.T.generic_fibre_card_torsion_cubical_pairing_perfect hL V A G s F N hN
  let ε₀ : Γ(Spec (CommRingCat.of F), ⊤) ≃+* F := (Scheme.ΓSpecIso (CommRingCat.of F)).commRingCatIsoToRingEquiv
  refine mem_of_orthogonal_of_card (F := F) (M := TF (R := V) F ⟶ G) (U := Γ((TF (R := V) F).left, ⊤)ˣ)
    (Units.map ε₀.toMonoidHom) (Units.map_injective ε₀.injective) N (CubWeil s.P.c N)
    (fun _ _ hx hy => existsUnique_cubWeil _ hx hy) (fun _ _ _ _ _ h h' => h.mul_left h')
    (fun _ _ _ h => h.symm) ?_ hnd T H hT hH (hc.trans hcard.symm) hTH x hx hxH
  rw [hcard]
  exact pow_ne_zero _ (by omega)

end GlobalTheory.UU
end
