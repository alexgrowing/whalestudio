import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.ThClassPins
import Formalism.LocalToGlobal.ProjectiveLattices.LiftLaSpec
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.LevelCarrying
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LevelActionOverlapLeSourceChart
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointBaseChangeUniqueReflIff
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabCancel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsReducedIsNormalSchemeIsLocallyNoetherianOfSmoo
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CompEqIdOfTwists

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LevelLawsCompare

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions Formalism.BasicNotions GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms

section General

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

instance finite_levelMod : Finite (LevelMod Dw l) := by
  haveI := Dw.fin
  haveI : Module.Finite ℤ (LevelMod Dw l) := Module.Finite.trans (𝓞 E) _
  have hM : (l.M : ℤ) ≠ 0 := by have := l.three_le; omega
  apply Module.finite_of_fg_torsion
  intro q
  refine ⟨⟨(l.M : ℤ), mem_nonZeroDivisors_of_ne_zero hM⟩, ?_⟩
  obtain ⟨a, rfl⟩ := Submodule.mkQ_surjective _ q
  change (l.M : ℤ) • (l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)).mkQ a = 0
  rw [natCast_zsmul, ← map_nsmul]
  exact (Submodule.Quotient.mk_eq_zero _).mpr (Moduli.LevelAction.mem_of_modN l ⟨a, rfl⟩)

instance finite_levelAut : Finite (LevelAut Dw l) :=
  Finite.of_injective (fun g : LevelAut Dw l => (g : LevelMod Dw l → LevelMod Dw l)) DFunLike.coe_injective

def Lifts (p : (Dw.La →ₗ[𝓞 E] Dw.La) × (Dw.La →ₗ[𝓞 E] Dw.La)) (g : LevelAut Dw l) : Prop :=
  (∀ a, (Submodule.Quotient.mk (p.1 a) : LevelMod Dw l) = g (Submodule.Quotient.mk a)) ∧
    ∀ a, Dw.ModN l.A (p.2 a - a)

theorem frMap_id_iff {S : Type} [CommRing S] [Algebra c.F S] (y y' : FrPt Xo c S) :
    FrMap (AlgHom.id c.F S) y y' ↔ y = y' := by
  obtain ⟨hu, hr, -⟩ := GlobalTheory.Frames.frMap_unique_refl_iff E H Dw l Xo c S S (AlgHom.id c.F S) y
  exact ⟨fun h => hu _ _ hr h, fun h => h ▸ hr⟩

section Laws

variable {G : Type} [Group G] (R : RelFam Xo c G)

abbrev reord {S : Type} [CommRing S] [Algebra c.F S] (g : G) (y y' : FrPt Xo c S) : Prop := R g S y y'

theorem mul_iff : ActMul (K := c.F) (fun S _ _ => FrPt Xo c S) (reord R) ↔ Multiplicative' R := Iff.rfl

variable {R}

end Laws

def redMod (f : Dw.La →ₗ[𝓞 E] Dw.La) : LevelMod Dw l →ₗ[𝓞 E] LevelMod Dw l :=
  Submodule.mapQ _ _ f fun x hx => by
    refine Submodule.smul_induction_on hx (fun r hr y _ => ?_) fun y z hy hz => Submodule.add_mem _ hy hz
    rw [Submodule.mem_comap, map_smul]
    exact Submodule.smul_mem_smul hr Submodule.mem_top

end General

section Record

variable {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} (Xo : Moduli Dw l) (c : Coeff l)

def ActLevAll : Prop :=
  ∀ (G : Type) [Group G] (lev : G → (Dw.La →ₗ[𝓞 D.host.E] Dw.La) × (Dw.La →ₗ[𝓞 D.host.E] Dw.La))
    (e : G →* LevelAut Dw l), (∀ g, Lifts (lev g) (e g)) → ActLev (Xo := Xo) c lev

def ActLevMul : Prop :=
  ∀ (G : Type) [Group G] (lev : G → Dw.La →ₗ[𝓞 D.host.E] Dw.La),
    (∀ a, lev 1 a - a ∈ l.Mb • (⊤ : Submodule (𝓞 D.host.E) Dw.La)) →
    (∀ g h a, lev (g * h) a - lev g (lev h a) ∈ l.Mb • (⊤ : Submodule (𝓞 D.host.E) Dw.La)) →
    ActLev (Xo := Xo) c (fun g => (lev g, LinearMap.id))

end Record

end GlobalTheory.LevelLawsCompare
