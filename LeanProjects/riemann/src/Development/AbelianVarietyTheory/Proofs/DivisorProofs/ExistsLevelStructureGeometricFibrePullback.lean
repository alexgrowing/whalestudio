import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsMulEquivOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsAbelianFibreIsoOfMatchedTorsionTheta
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.UniformizationLawsAndExpansionStatements
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.FibLevel

theorem comp_pow_pt {S : Scheme.{0}} {A T T' : Over S} [GrpObj A] (ρ : T' ⟶ T) (x : T ⟶ A) (n : ℕ) :
    ρ ≫ x ^ n = (ρ ≫ x) ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, MonObj.comp_one]
  | succ n ih => rw [pow_succ, pow_succ, MonObj.comp_mul, ih]

theorem exists_level_of_pullback : ∀ (T K : Type) [CommRing T] [IsNoetherianRing T] [Field K] [IsAlgClosed K] (χ : T →+* K) (P : PolAV (Sp T)) (Q : PolAV (Sp K)) (ψ : Q.A.left ⟶ P.A.left), IsGrpPullback Q.A P.A (spMap χ) ψ → LBIso Q.L (P.L.pull ψ) → ∀ (g M : ℕ) (hg : Q.g = g) (c : Tˣ) (ζK : Kˣ), (M : K) ≠ 0 → Units.map χ.toMonoidHom c = ζK → IsPrimitiveRoot ζK M → ∀ (y : Fin (2 * g) → (baseOver (Sp T) ⟶ P.A)), (∀ i, y i ^ M = 1) → (∀ i j, WeilIs P.A P.L M (y i) (y j) (unitOn c ^ stdSymp g i j)) → ∃ lev : Level Q M (unitOn ζK), ∀ i, (GlobalTheory.levelBasis lev hg i).left ≫ ψ = spMap χ ≫ (y i).left := by
  intro T K _ _ _ _ χ P Q ψ hpb hLB g M hg c ζK hM hcζ hζ y hy hw
  obtain ⟨⟨hL, -, -⟩, -⟩ := GlobalTheory.lawsAndExpansions
  obtain ⟨e, he⟩ := exists_mulEquiv_of_isGrpPullback hpb (𝟙 (Sp K)) (spMap χ) (Category.id_comp _).symm
  let h0 : Over.mk (spMap χ) ⟶ baseOver (Sp T) := Over.homMk (spMap χ) (Category.comp_id _)
  let x : Fin (2 * g) → (baseOver (Sp K) ⟶ Q.A) := fun i => e.symm (h0 ≫ y i)
  have hex : ∀ i, e (x i) = h0 ≫ y i := fun i => e.apply_symm_apply _
  have hxl : ∀ i, (h0 ≫ y i).left = (x i).left ≫ ψ := fun i => by rw [← hex, he]
  have hxM : ∀ i, x i ^ M = 1 := fun i => by
    show e.symm (h0 ≫ y i) ^ M = 1
    rw [← map_pow, ← comp_pow_pt, hy, MonObj.comp_one, map_one]
  have hv : ∀ n : ℤ, Units.map h0.left.appTop.hom.toMonoidHom (unitOn c ^ n) = unitOn ζK ^ n := by
    intro n
    rw [map_zpow]
    congr 1
    rw [← hcζ]
    apply Units.ext
    have := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom χ)
    exact (congrArg (fun f => f.hom c.val) this).symm
  have key : ∀ (s : Sp K ⟶ Sp T) (_ : s = 𝟙 _ ≫ spMap χ) (x y : baseOver (Sp K) ⟶ Q.A)
      (x₀ y₀ : Over.mk s ⟶ P.A) (u : Γ(Sp K, ⊤)ˣ), x₀.left = x.left ≫ ψ → y₀.left = y.left ≫ ψ →
      WeilIs P.A P.L M x₀ y₀ u → WeilIs Q.A Q.L M x y u := by
    rintro s rfl x y x₀ y₀ u hx hy h
    have := Q.isAb.comm
    exact (weilIs_grpPullback_of_comm' _ _ _ _ _ ψ _ _ P.isLB Q.isLB hpb hLB (baseOver _) M x y x₀ y₀ u
      hx hy).2 h
  have hxp : ∀ i j, WeilIs Q.A Q.L M (x i) (x j) (unitOn ζK ^ stdSymp g i j) := fun i j => by
    have w := CommPairing.weilIs_pull hL.globalFns P.isAb P.isLB h0 (hw i j)
    rw [hv] at w
    exact key _ (Category.id_comp _).symm _ _ _ _ _ (hxl i) (hxl j) w
  obtain ⟨lev, hlev⟩ := GlobalTheory.Ex.FibIso.exists_level hL Q hg hM hζ x hxM hxp
  exact ⟨lev, fun i => by rw [hlev]; exact (hxl i).symm⟩

end GlobalTheory.Mum.FibLevel
