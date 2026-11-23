import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.DegreeHermitianFormula
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PullFieldDef
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PullFieldFlow
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PullLevGood
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PullLevD
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PullOmGood
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PullOmHom
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PullPbBd
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PullHomBd
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.ExistsCurve
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.CorrUniq
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.LocSec
open UpperTheory.V.Lit.Geo
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor

private theorem cone_open (E : Type) [Field E] [NumberField E] (a : ℕ) : IsOpen (cone E a) :=
  isOpen_iff_mem_nhds.2 fun p hp => by
    obtain ⟨τ, -, h⟩ := UpperTheory.V.Lit.Dr.locSec E a p hp
    exact h.mono fun x hx => ⟨τ x, hx⟩

private theorem homOm_zero {Γ V S : Type} [Group Γ] [NormedAddCommGroup V] [NormedSpace ℝ V] {d : ℕ}
    (G : UpperTheory.V.Lit.Dr.Geo Γ V S d) (W : S → V → V) (q : ℕ) : homOm G W (0 : G.Om (q + 1)) = 0 := by
  have e : (fun s => hom (W s) ((0 : G.Om (q + 1)).1 s)) = fun _ _ => 0 := by
    funext s p
    have : (fun t => hk (W s) t ((0 : G.Om (q + 1)).1 s) p) = fun _ => 0 := by
      funext t
      ext v
      simp [hk_apply]
    rw [hom, this, intervalIntegral.integral_zero]
  rw [homOm, e]
  refine Subtype.ext (funext fun s => funext fun p => ?_)
  by_cases hp : p ∈ G.Y
  · rw [toOm_apply G (fun _ => contDiffOn_const) s hp]
    rfl
  · rw [((toOm G _).2 s).2 p hp]
    rfl

private theorem d_step {Γ V S : Type} [Group Γ] [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] {d : ℕ}
    (G : UpperTheory.V.Lit.Dr.Geo Γ V S d) (W : S → V → V) (hF : IsFlow G W) (q : ℕ) (w : G.Om q) :
    G.dOm q (pbOm G W w - homOm G W (G.dOm q w)) = G.dOm q w := by
  have hH := omHom _ _ _ _ G W hF
  have e := hH.2.2.2 q (G.dOm q w)
  rw [hH.2.1, homOm_zero, add_zero, sub_eq_iff_eq_add] at e
  rw [map_sub, hH.1, e, add_sub_cancel_left]

private theorem corr_sub {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ} (ho : IsOpen (cone E a))
    (U : Subgroup (GL (Fin a) (Af E))) (Ξ : AlgRep E a) {q : ℕ} {α β : Co Ξ q} {w w' : (geo ho U Ξ).Om q}
    (h : Corr U Ξ α w.1) (h' : Corr U Ξ β w'.1) : Corr U Ξ (α - β) (w - w').1 := fun g x X => by
  rw [AlternatingMap.sub_apply, map_sub, Pi.sub_apply, Matrix.mulVec_sub, ← h g x X, ← h' g x X]
  rfl

theorem UpperTheory.V.Lit.Geo.oneStep :
    OneStep := by
  intro E _ _ _ a U Ξ Y C hY q
  have ho := cone_open E a
  obtain ⟨W, hW⟩ := fieldDef E a U Y C hY
  have hF := (fieldFlow E a ho U Ξ Y C hY W hW).1
  obtain ⟨B₁, hB₁, h₁⟩ := pbBd E a ho U Ξ Y C hY W hW q
  obtain ⟨B₂, hB₂, h₂⟩ := homBd E a ho U Ξ Y C hY W hW q
  refine ⟨B₁ + B₂, add_nonneg hB₁ hB₂, fun η hη => ?_⟩
  obtain ⟨w, hw, hg⟩ := (levGood E a ho U Ξ q).1 η hη
  have hO := omGood _ _ _ _ _ W hF q
  obtain ⟨gP, gD⟩ := hO.1 w hg
  have gH := hO.2.2 _ gD
  obtain ⟨α, cα, lα⟩ := (levGood E a ho U Ξ q).2 _ gP
  obtain ⟨β, cβ, lβ⟩ := (levGood E a ho U Ξ q).2 _ gH
  have cd := UpperTheory.V.Lit.Dr.corrD E a ho U Ξ q η w hw
  refine ⟨α - β, (levD E a U Ξ q α lα).2 β lβ, ?_, fun g M M' hM hM' H H' => ?_⟩
  · have c := UpperTheory.V.Lit.Dr.corrD E a ho U Ξ q _ _ (corr_sub ho U Ξ cα cβ)
    rw [d_step _ W hF] at c
    exact (UpperTheory.V.Lit.Dr.corrUniq E a ho U Ξ (q + 1)).1 _ _ _ c cd
  · refine ((h₁ η α w hη hw cα g M hM H).sub
      (h₂ _ β _ (levD E a U Ξ q η hη).1 cd cβ g M' hM' H')).mono ?_
    nlinarith [mul_nonneg hB₁ hM', mul_nonneg hB₂ hM]
