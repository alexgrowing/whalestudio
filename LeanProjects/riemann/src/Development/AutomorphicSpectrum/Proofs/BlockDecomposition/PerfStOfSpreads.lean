import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.HodgeWedgeFields.H1CommutesBaseChange
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.CubeTheorem.SchemeModels
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteAffineCoverInfClosed
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HasModelOfSpreading

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge

namespace GlobalTheory.CompanionTheory.PerfModels

theorem flat_sec {R : Type} [CommRing R] {X : Scheme.{0}} (s : X ⟶ Sp R) [Flat s] (U : X.affineOpens) :
    Module.Flat R (Sec s U.1) := by
  have hfl : RingHom.Flat (s.appLE ⊤ U.1 le_top).hom := s.flat_appLE (isAffineOpen_top _) U.2 le_top
  have hi : RingHom.Flat (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom :=
    RingHom.Flat.of_bijective (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).inv)
  have h : RingHom.Flat (secMap s U.1).hom := RingHom.Flat.comp hi hfl
  exact (RingHom.flat_algebraMap_iff (R := R) (S := Sec s U.1)).1 h

theorem exists_sys {R : Type} [CommRing R] {X : Scheme.{0}} (s : X ⟶ Sp R) [IsSeparated s] [QuasiCompact s] :
    ∃ (P : Type) (_ : SemilatticeInf P) (_ : Finite P), Nonempty (Sys X P) := by
  obtain ⟨J, hf, hl, U, -, hm, hc⟩ := GlobalTheory.exists_finite_affine_cover_infClosed R X s inferInstance inferInstance
  exact ⟨J, hl, hf, ⟨⟨U, hm, hc⟩⟩⟩

theorem perf_noeth (hF : FinCohSt) (hN : PerfNoethSt) (R : Type) [CommRing R] [IsNoetherianRing R]
    (X : Scheme.{0}) (s : X ⟶ Sp R) [Smooth s] [IsProper s] :
    ∃ (P : Type) (_ : SemilatticeInf P) (_ : Finite P) (S : Sys X P), Perf (OSys s S) := by
  obtain ⟨P, _, _, ⟨S⟩⟩ := exists_sys s
  obtain ⟨h₀, h₁⟩ := hF R X s inferInstance P S
  exact ⟨P, inferInstance, inferInstance, S,
    hN R P (OSys s S) inferInstance (fun T ↦ flat_sec s (S.u T.unop)) h₀ h₁⟩

theorem perf_base (hB : SysBCSt) (hP : PerfBaseSt) {R₀ R : Type} [CommRing R₀] [CommRing R] (φ : R₀ →+* R)
    {Y X : Scheme.{0}} (f : Y ⟶ Sp R₀) (s : X ⟶ Sp R) (π : X ⟶ Y) [IsSeparated f]
    (h : IsPullback π s f (spMap φ))
    (hY : ∃ (P : Type) (_ : SemilatticeInf P) (_ : Finite P) (S : Sys Y P), Perf (OSys f S)) :
    ∃ (P : Type) (_ : SemilatticeInf P) (_ : Finite P) (S : Sys X P), Perf (OSys s S) := by
  obtain ⟨P, _, _, S, hS⟩ := hY
  letI := φ.toAlgebra
  obtain ⟨S', m, -⟩ := hB R₀ R Y X f s π h inferInstance P S
  exact ⟨P, inferInstance, inferInstance, S', hP R₀ P (OSys f S) hS R (OSys s S') m⟩

theorem perfSt_of_spreads : GlobalTheory.SpreadingModels.SchemeModels → GlobalTheory.SpreadingModels.Spreads (fun _ _ f => Smooth f) →
    GlobalTheory.SpreadingModels.Spreads (fun _ _ f => IsProper f) → DescentSt → LowSt → SysBCSt → FinCohSt → PerfNoethSt →
    PerfBaseSt → PerfSt := by
  intro hS hSm hPr _ _ hBC hF hN hP R _ X s hsm hpr
  obtain ⟨R₀, _, φ, Y₀, f₀, π, hm⟩ := hS R X s inferInstance inferInstance inferInstance
  obtain ⟨R₁, _, ψ₁, φ₁, e₁, ft₁, sm₁⟩ := hSm R R₀ φ X Y₀ s f₀ π hm hsm
  have m₁ := GlobalTheory.CompanionTheory.CubeModels.model_refine' e₁ ft₁ hm
  obtain ⟨R₂, _, ψ₂, φ₂, e₂, ft₂, pr₂⟩ := hPr R R₁ φ₁ X _ s _ _ m₁ hpr
  have m₂ := GlobalTheory.CompanionTheory.CubeModels.model_refine' e₂ ft₂ m₁
  have sm₁' : Smooth (Limits.pullback.snd f₀ (Spec.map (CommRingCat.ofHom ψ₁))) := sm₁
  have pr₂' : IsProper (Limits.pullback.snd (Limits.pullback.snd f₀ (Spec.map (CommRingCat.ofHom ψ₁)))
      (Spec.map (CommRingCat.ofHom ψ₂))) := pr₂
  haveI : IsNoetherianRing R₂ := Algebra.FiniteType.isNoetherianRing ℤ R₂
  exact perf_base hBC hP φ₂ _ s _ m₂.2.2.2.2 (perf_noeth hF hN R₂ _ _)

end GlobalTheory.CompanionTheory.PerfModels
