import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.OrdReadOf
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

theorem UpperTheory.Gal.crystallineComparison.Mod.frobRing_of :
    FrobRing := by
  intro p f hp κ _ _ A _ B Λ _ _ _ _ i hi ε₀ hε ν g hg
  have hpΛ : (p : Λ) = 0 := by
    have h := map_natCast (algebraMap κ Λ) p
    rw [CharP.cast_eq_zero κ p, map_zero] at h
    exact h.symm
  let σ : Λ →+* Λ := GlobalTheory.SS.FrobField.powHom Λ p f hp hpΛ
  have hσ : ∀ c, σ c = c ^ p ^ f := fun _ => rfl
  have h0 : (p : Γ(Sp Λ, ⊤)) = 0 := GlobalTheory.SS.FrobField.cast_zero_sp Λ hpΛ
  have hfr : GlobalTheory.SS.FrobField.absFrob (Sp Λ) p f hp h0 = spMap σ :=
    GlobalTheory.SS.FrobField.absFrob_spec Λ p f hp h0 σ hσ
  have hmono : Mono i.left := (Over.forget _).map_mono i
  have h1 : (1 : algPt κ Λ ⟶ A).left = spMap (algebraMap κ Λ) ≫ spMap ε₀.toRingHom ≫ i.left := by
    have e : (1 : algPt κ Λ ⟶ A) = toUnit (algPt κ Λ) ≫ (1 : 𝟙_ (Over (Sp κ)) ⟶ A) := by
      simp
    have e2 : (toUnit (algPt κ Λ)).left = spMap (algebraMap κ Λ) := by
      have := Over.w (toUnit (algPt κ Λ))
      simpa using this
    rw [e, Over.comp_left, e2]
    exact congrArg (spMap (algebraMap κ Λ) ≫ ·) hε.symm
  have sc : ∀ {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (u : R →+* S) (v : S →+* T),
      spMap v ≫ spMap u = spMap (v.comp u) := by
    intro R S T _ _ _ u v
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have key : FrobKill p f hp g ↔ σ.comp ν.toRingHom = (σ.comp (algebraMap κ Λ)).comp ε₀.toRingHom := by
    constructor
    · intro h
      have h2 := h h0
      change GlobalTheory.SS.FrobField.absFrob (Sp Λ) p f hp h0 ≫ g.left =
        GlobalTheory.SS.FrobField.absFrob (Sp Λ) p f hp h0 ≫ (1 : algPt κ Λ ⟶ A).left at h2
      rw [hfr, hg, h1] at h2
      simp only [← Category.assoc] at h2
      have h3 := (cancel_mono i.left).1 h2
      rw [sc, sc, sc] at h3
      exact congrArg CommRingCat.Hom.hom (Spec.map_injective h3)
    · intro h hh
      change GlobalTheory.SS.FrobField.absFrob (Sp Λ) p f hp hh ≫ g.left =
        GlobalTheory.SS.FrobField.absFrob (Sp Λ) p f hp hh ≫ (1 : algPt κ Λ ⟶ A).left
      rw [show GlobalTheory.SS.FrobField.absFrob (Sp Λ) p f hp hh = spMap σ from hfr, hg, h1]
      simp only [← Category.assoc]
      rw [sc, sc, sc, h]
  rw [key]
  constructor
  · intro h x hx
    have := RingHom.congr_fun h x
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, hx, map_zero] at this
    rw [hσ] at this
    exact this
  · intro h
    ext x
    have hy : ε₀ (x - algebraMap κ B (ε₀ x)) = 0 := by
      simp
    have h2 := h _ hy
    have h3 : σ (ν (x - algebraMap κ B (ε₀ x))) = 0 := by rw [hσ]; exact h2
    rw [map_sub, map_sub, AlgHom.commutes, sub_eq_zero] at h3
    simpa using h3
