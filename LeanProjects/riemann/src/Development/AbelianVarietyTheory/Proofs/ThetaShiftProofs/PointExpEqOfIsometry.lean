import Mathlib
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ModelsAt
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExpEqOfIsometryMatchingMarkings
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PointEqIffIsometryClosed

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries

namespace GlobalTheory.ArcCM

theorem isHolTo_comp_univ {V W : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W]
    [NormedSpace ℂ W] {X : Scheme.{0}} {B : Set W} {y : W → (Sp ℂ ⟶ X)} (hy : IsHolTo B y) {φ : V → W}
    (hφ : Differentiable ℂ φ) (hB : ∀ z, φ z ∈ B) : IsHolTo Set.univ (fun z => y (φ z)) := by
  unfold IsHolTo at hy ⊢
  intro U f
  obtain ⟨ho, hd⟩ := hy U f
  have hset : {b | b ∈ (Set.univ : Set V) ∧ ⊤ ≤ (fun z => y (φ z)) b ⁻¹ᵁ U} =
      φ ⁻¹' {b | b ∈ B ∧ ⊤ ≤ y b ⁻¹ᵁ U} := by
    ext b
    simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_univ, true_and, hB b]
  rw [hset]
  exact ⟨ho.preimage hφ.continuous, hd.comp hφ.differentiableOn (fun b hb => hb)⟩

theorem isHolTo_exp_of_isPeriod {E : Type} [Field E] [NumberField E] [IsCMField E]
    {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {D : Datum H} {l : Level H} {Xo : Moduli D l} {σ : KA l →+* ℂ} {g : ℕ}
    {ty : Fin g → (E →+* ℂ)} (Fu : FamilyUnif Xo σ ty) (i : Fin Fu.n) (P : (Fu.Di i).La →+ (Fin g → ℂ))
    (hP : IsPeriod (Fu.Di i) ty P) : IsHolTo Set.univ (fun z => (Fu.ex i P z).left) := by

  have hper : IsHolPeriods (Fu.Di i) ty (Set.univ : Set (Fin 0 → ℂ)) (fun _ => P) :=
    ⟨fun _ _ => hP, fun _ => differentiableOn_const _⟩
  have hjoint : IsHolTo ((Set.univ : Set (Fin 0 → ℂ)) ×ˢ (Set.univ : Set (Fin g → ℂ)))
      (fun bz : (Fin 0 → ℂ) × (Fin g → ℂ) => (Fu.ex i P bz.2).left) :=
    (Fu.21 i 0 Set.univ (fun _ => P) isOpen_univ hper).2
  have hφ : Differentiable ℂ (fun z : Fin g → ℂ => ((0 : Fin 0 → ℂ), z)) :=
    (differentiable_const _).prodMk differentiable_id
  have hmem : ∀ z : Fin g → ℂ, ((0 : Fin 0 → ℂ), z) ∈ (Set.univ : Set (Fin 0 → ℂ)) ×ˢ (Set.univ : Set (Fin g → ℂ)) :=
    fun z => Set.mk_mem_prod (Set.mem_univ _) (Set.mem_univ _)
  have hcomp := isHolTo_comp_univ hjoint hφ hmem
  exact hcomp

theorem point_exp_eq_of_isometry : Known → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo σ ty) (i i' : Fin Fu.n) (P : (Fu.Di i).La →+ (Fin g → ℂ)) (P' : (Fu.Di i').La →+ (Fin g → ℂ)) (gm : (Fu.Di i).La ≃ₗ[𝓞 E] (Fu.Di i').La) (L : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)), 1 ≤ D.p + D.q → σ (baseKA l).ρ = H.rt0 → IsTypeFn H D.p D.q ty → l.A = 1 → IsPeriod (Fu.Di i) ty P → IsPeriod (Fu.Di i') ty P' → (∀ u v, (Fu.Di i').EF (gm u) (gm v) = (Fu.Di i).EF u v) → (∀ v ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La), ∃ e, gm (Fu.t i v) = Fu.t i' v + l.M • e) → (∀ u, P' (gm u) = L (P u)) → Fu.u i P = Fu.u i' P' ∧ ∀ z, (Fu.ex i' P' (L z)).left = (Fu.ex i P z).left := by
  intro hK E _ _ _ H D l Xo σ g ty Fu i i' P P' gm L hpq hρ hty hA hP hP' hiso hmark hPL

  have hpt : Fu.u i P = Fu.u i' P' := by
    refine (GlobalTheory.UnifPoint.point_eq_iff_isometry_closed hK.theta hK.laws E H D l Xo σ g ty hpq hρ hty
      (Fu.Di i) (Fu.Di i') (Fu.t i) (Fu.t i') P P' (Fu.u i P) (Fu.u i' P') (Fu.ex i P) (Fu.ex i' P')
      ⟨Fu.over_σ i P hP, hP, ⟨Fu.ex_add i P hP, Fu.ex_onto i P hP, isHolTo_exp_of_isPeriod Fu i P hP,
        (Fu.22 i P hP).1, (Fu.22 i P hP).2⟩, Fu.ex_ker i P hP, Fu.ex_lin i P hP, Fu.ex_weil i P hP,
        Fu.ex_eta i P hP, Fu.ex_etaA i P hP⟩
      ⟨Fu.over_σ i' P' hP', hP', ⟨Fu.ex_add i' P' hP', Fu.ex_onto i' P' hP', isHolTo_exp_of_isPeriod Fu i' P' hP',
        (Fu.22 i' P' hP').1, (Fu.22 i' P' hP').2⟩, Fu.ex_ker i' P' hP', Fu.ex_lin i' P' hP', Fu.ex_weil i' P' hP',
        Fu.ex_eta i' P' hP', Fu.ex_etaA i' P' hP'⟩).2 ?_

    exact ⟨gm, L, hiso, hmark, fun a => ⟨gm (Fu.t i a) - Fu.t i' a, by rw [hA, one_smul]; abel⟩, hPL⟩

  have hii : i = i' := Fu.disj i i' P P' hP hP' hpt
  subst hii

  letI := H.starRing
  have hex := GlobalTheory.ArcPts.exp_eq_of_matching_markings E H D l Xo σ g ty Fu i P P' gm L rfl hP hP' hiso hmark
    (fun v => ⟨gm (Fu.t i v) - Fu.t i v, by rw [hA, one_smul]; abel⟩) hPL
  exact ⟨hpt, hex.2⟩

end GlobalTheory.ArcCM
