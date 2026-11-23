import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.ThClassPins
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ActLevFullLevelGroupFramedPoints

noncomputable section

namespace GlobalTheory.LevelActionOfLifts

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions

section General

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem levR_congr {f g k : Dw.La →ₗ[𝓞 E] Dw.La}
    (h : ∀ a, f a - g a ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)) {S : Type} [CommRing S] [Algebra c.F S]
    (y y' : FrPt Xo c S) : levR (f, k) y y' ↔ levR (g, k) y y' := by
  have e : ∀ a, Xo.univ.eta (f a) = Xo.univ.eta (g a) := fun a => GlobalTheory.LevelActionLaws.eta_congr Xo (h a)
  unfold levR IsLevMove
  simp only [e]

def modHalf (l : Level H) (f : Dw.La →ₗ[𝓞 E] Dw.La) : Module.End (𝓞 E) (LaMod Dw l) :=
  Submodule.mapQ _ _ f (by
    rw [← Submodule.map_le_iff_le_comap, Submodule.map_smul'']
    exact Submodule.smul_mono le_rfl le_top)

end General

variable {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H}

theorem actLev_of_lifts (Xo : Moduli Dw l) (c : Coeff l) {G : Type} [Group G]
    (lev : G → (Dw.La →ₗ[𝓞 D.host.E] Dw.La)) (hpq : 1 ≤ Dw.p + Dw.q) (hA : l.A.Coprime l.M)
    (h1 : ∀ a, lev 1 a - a ∈ l.Mb • (⊤ : Submodule (𝓞 D.host.E) Dw.La))
    (hm : ∀ g h a, lev (g * h) a - lev g (lev h a) ∈ l.Mb • (⊤ : Submodule (𝓞 D.host.E) Dw.La)) :
    ActLev (Xo := Xo) c (fun g => (lev g, (LinearMap.id : Dw.La →ₗ[𝓞 D.host.E] Dw.La))) := by
  let φ : G →* Module.End (𝓞 D.host.E) (LaMod Dw l) :=
    { toFun := fun g => modHalf l (lev g)
      map_one' := by
        refine LinearMap.ext fun q => ?_
        obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ q
        exact (Submodule.Quotient.eq _).2 (h1 a)
      map_mul' := fun g h => by
        refine LinearMap.ext fun q => ?_
        obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ q
        exact (Submodule.Quotient.eq _).2 (hm g h a) }
  let ψ : G →* (LaMod Dw l ≃ₗ[𝓞 D.host.E] LaMod Dw l) :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (𝓞 D.host.E) (LaMod Dw l)).toMonoidHom.comp φ.toHomUnits
  have key : ∀ (g : G) {S : Type} [CommRing S] [Algebra c.F S] (y y' : FrPt Xo c S),
      levActR (Xo := Xo) (c := c) (fun g => (lev g, (LinearMap.id : Dw.La →ₗ[𝓞 D.host.E] Dw.La))) g y y' ↔
        levActR (Xo := Xo) (c := c) (GlobalTheory.FormTies.levFull Dw l) (ψ g) y y' := by
    intro g S _ _ y y'
    refine levR_congr (fun a => (Submodule.Quotient.eq _).1 ?_) y y'
    exact (liftLa_spec (ψ g) a).symm
  have L := GlobalTheory.FullLevelAction.actLaws_levFull Xo c hpq hA
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro g S _ _ y
    obtain ⟨y', h⟩ := L.total (ψ g) S y
    exact ⟨y', (key g y y').2 h⟩
  · intro g S _ _ y y' y'' h h'
    exact L.func (ψ g) S y y' y'' ((key _ _ _).1 h) ((key _ _ _).1 h')
  · intro S _ _ y
    refine (key 1 y y).2 ?_
    rw [map_one]
    exact L.one S y
  · intro g h S _ _ y y' y'' a b
    refine (key _ _ _).2 ?_
    rw [map_mul]
    exact L.mul _ _ S y y' y'' ((key _ _ _).1 a) ((key _ _ _).1 b)
  · intro g S T _ _ _ _ φ y y' z z' m a b
    exact L.nat (ψ g) S T φ y y' z z' m ((key _ _ _).1 a) ((key _ _ _).1 b)
  · intro g S _ _ t y y' z z' m a b
    exact L.bor (ψ g) S t y y' z z' m ((key _ _ _).1 a) ((key _ _ _).1 b)

theorem actLev_of_lifts_of_eq_one : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (G : Type) [Group G] (lev : G → (Dw.La →ₗ[𝓞 D.host.E] Dw.La)), 1 ≤ Dw.p + Dw.q → l.A = 1 → (∀ a, lev 1 a - a ∈ l.Mb • (⊤ : Submodule (𝓞 D.host.E) Dw.La)) → (∀ g h a, lev (g * h) a - lev g (lev h a) ∈ l.Mb • (⊤ : Submodule (𝓞 D.host.E) Dw.La)) → ActLev (Xo := Xo) c (fun g => (lev g, (LinearMap.id : Dw.La →ₗ[𝓞 D.host.E] Dw.La))) := by
  intro D H Dw l Xo c G _ lev hpq hA h1 hm
  exact actLev_of_lifts Xo c lev hpq (by rw [hA]; exact Nat.coprime_one_left _) h1 hm

end GlobalTheory.LevelActionOfLifts
