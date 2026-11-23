import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.ActsLinOfSplitLin
import Formalism.LocalToGlobal.IndefiniteReal.WeilFull
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.FinPartPhiE
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.PlaceSum

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum

namespace Formalism.IndefR.Fin.LevelGroupLemmas

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def SplitOrInert (D : D7) : Prop :=
  ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (ε : AF D.host.F), IsPlaceIdem D v ε →
    (∃ PP : HeightOneSpectrum (𝓞 D.host.E), PP.asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) = v.asIdeal ∧
      ¬ Lev.IsConjPl (D := D) PP PP) ∨
    ∀ e : AE D, IsSplitIdem D e → e * algebraMap (AF D.host.F) (AE D) ε = 0

open Classical in

theorem sbHalf_halfInd {S T : HSp D} (e : AE D) (Λ : AddSubgroup (WO S T)) : IsSBHalf e Λ (halfInd e Λ) := by
  unfold IsSBHalf halfInd
  refine ⟨?_, 1, one_pos, ?_⟩
  · intro t ht
    by_contra hn
    apply ht
    simp [hn]
  · refine ⟨?_, ?_⟩
    · intro u hu hh t
      have hΛ : t + 1 • u ∈ Λ ↔ t ∈ Λ := by
        rw [one_smul]
        exact ⟨fun h => by simpa using Λ.sub_mem h hu, fun h => Λ.add_mem h hu⟩
      have hH : IsHalf e (t + 1 • u) ↔ IsHalf e t := by
        unfold IsHalf at hh ⊢
        simp only [one_smul, Matrix.add_apply, Pi.add_apply, mul_add, hh, add_left_inj]
      simp only [hΛ, hH]
    · intro t ht
      rw [one_smul]
      by_contra hn
      apply ht
      simp [hn]

theorem fix_split (hSL : SplitLin D) (hPM : PlaceModelAt D) {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}
    {χS χT : (AE D)ˣ →* Circle} {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hW : IsWeilDatumO ψ S T χS χT om)
    {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
    (hsS : IsSelfDualC S ΛS) (hsT : IsSelfDualC T ΛT) {PP : Formalism.L2.DIV.Pl D.host.E} {e' : AE D}
    (he' : Formalism.L2.NTheta.IsIdemAt e' PP) {f₀ : WO S T → ℂ} (hf₀ : IsThetaFunO ψ S T f₀)
    (hlat : IsLatVac (heisO ψ S T) (latAll S T ΛS ΛT) f₀)
    (hn : ∃ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 ∧ nrm2 μ 𝓕 f₀ = 1)
    {g : GA D S} {h : GA D T} (hg : SuppAt e' S g) (hh : SuppAt e' T h) {x y : (AE D)ˣ}
    (hx : IsDetAt e' S g x) (hy : IsDetAt e' T h y) (hfac : splitFacO χS χT x y = 1)
    (hpres : ∀ t : WO S T, IsHalf e' t → (actO S T g h t ∈ latAll S T ΛS ΛT ↔ t ∈ latAll S T ΛS ΛT))
    (hpres' : ∀ t : WO S T, IsHalf e' t → (actO S T g⁻¹ h⁻¹ t ∈ latAll S T ΛS ΛT ↔ t ∈ latAll S T ΛS ΛT)) :
    om (g, h) f₀ = f₀ := by
  classical
  have hsp : IsSplitIdem D e' := he'.1
  have hsum : IsIdemSum e' {PP} := by
    refine ⟨⟨fun _ => e', fun Q hQ => ?_, by simp⟩, hsp.2.1⟩
    rw [Finset.mem_singleton] at hQ
    subst hQ
    exact he'
  have hvac : ∀ u ∈ latAll S T ΛS ΛT, (IsHalf e' u ∨ IsHalf (cA D e') u) →
      heisO ψ S T u f₀ = f₀ := by
    intro u hu hh
    rcases hh with hh | hh
    · exact hlat.2 e' hsp u hu hh
    · exact hlat.2 (cA D e') (isSplitIdem_cA hsp) u hu hh
  obtain ⟨Tm, hTm, -, -, -⟩ :=
    hPM ψ hW.std S T ΛS ΛT hsS hsT {PP} e' hsum f₀ hf₀ hvac e' (Or.inl rfl)
  obtain ⟨r, -, hrep, hr1⟩ := hSL ψ S T χS χT om hW ΛS ΛT hsS hsT {PP} e' hsum f₀ hf₀ hvac Tm hTm
    e' hsp hsp.1 g h hg hh x y hx hy
  have hr : r = 1 := hr1 hpres hn
  have hΦ : IsSBHalf e' (latAll S T ΛS ΛT) ((1 : ℂ) • halfInd e' (latAll S T ΛS ΛT)) := by
    rw [one_smul]
    exact sbHalf_halfInd e' _
  have hinv : (fun t => ((1 : ℂ) • halfInd e' (latAll S T ΛS ΛT)) (actO S T g⁻¹ h⁻¹ t)) =
      (1 : ℂ) • halfInd e' (latAll S T ΛS ΛT) := by
    funext t
    simp only [one_smul, halfInd]
    by_cases ht : IsHalf e' t
    · have h1 : IsHalf e' (actO S T g⁻¹ h⁻¹ t) := (isHalf_actO g⁻¹ h⁻¹ t).2 ht
      simp only [hpres' t ht, h1, ht, and_true]
    · have h1 : ¬ IsHalf e' (actO S T g⁻¹ h⁻¹ t) := fun h' => ht ((isHalf_actO g⁻¹ h⁻¹ t).1 h')
      simp only [h1, ht, and_false, if_false]
  calc om (g, h) f₀ = om (g, h) (Tm ((1 : ℂ) • halfInd e' (latAll S T ΛS ΛT))) := by rw [hTm.vac]
    _ = ((r : ℂ) * (splitFacO χS χT x y : ℂ)) •
          Tm (fun t => ((1 : ℂ) • halfInd e' (latAll S T ΛS ΛT)) (actO S T g⁻¹ h⁻¹ t)) := hrep _ hΦ
    _ = f₀ := by
      rw [hinv, hTm.vac, hr, hfac]
      simp

theorem latO_le_all {S T : HSp D} (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E))
    (P : HeightOneSpectrum (𝓞 D.host.F) → Prop) : latO S T ΛS ΛT P ≤ latO S T ΛS ΛT (fun _ => True) := by
  unfold latO
  apply AddSubgroup.closure_mono
  rintro w ⟨α, hα, h1, h2⟩
  refine ⟨α, hα, ?_, h2⟩
  intro v
  first
    | exact fun h => absurd trivial h
    | simp
    | simp_all
    | aesop

theorem fix_inert {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hI : WeilFull.SphInertAtO ψ S T χS χT om)
    (hrk : S.rank ≠ T.rank) (hev : Even S.rank ∨ Even T.rank)
    {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
    (hsS : IsSelfDualC S ΛS) (hsT : IsSelfDualC T ΛT) {βS : GL (Fin S.rank) (Lev.EAf D)} {βT : GL (Fin T.rank) (Lev.EAf D)}
    (hfS : Formalism.L2.DIV.IsFrame βS ΛS) (hfT : Formalism.L2.DIV.IsFrame βT ΛT) {v : HeightOneSpectrum (𝓞 D.host.F)}
    {ε : AF D.host.F} (hε : IsPlaceIdem D v ε) (h2 : (2 : 𝓞 D.host.F) ∉ v.asIdeal)
    (hin : ∀ e, IsSplitIdem D e → e * algebraMap (AF D.host.F) (AE D) ε = 0)
    (huS : WeilFull.UnrAtV ε χS) (huT : WeilFull.UnrAtV ε χT) {g : GA D S} {h : GA D T}
    (hg : WeilFull.SuppV ε S g) (hh : WeilFull.SuppV ε T h) (hgS : Lev.finE S g ∈ Formalism.L2.DIV.St βS)
    (hhT : Lev.finE T h ∈ Formalism.L2.DIV.St βT) {f₀ : WO S T → ℂ} (hf₀ : IsThetaFunO ψ S T f₀)
    (hlat : IsLatVac (heisO ψ S T) (latAll S T ΛS ΛT) f₀) : om (g, h) f₀ = f₀ := by
  have key : IsLatVac (heisO ψ S T) (latO S T ΛS ΛT fun w => w = v) f₀ := by
    clear * - hlat
    unfold IsLatVac at *
    exact ⟨fun u hu => hlat.1 u (latO_le_all (S := S) (T := T) ΛS ΛT _ hu),
      fun e he u hu hh => hlat.2 e he u (latO_le_all (S := S) (T := T) ΛS ΛT _ hu) hh⟩
  exact hI hrk hev ΛS ΛT hsS hsT βS βT hfS hfT v ε hε h2 hin huS huT g h hg hh hgS hhT f₀ hf₀ key

end Formalism.IndefR.Fin.LevelGroupLemmas

end
