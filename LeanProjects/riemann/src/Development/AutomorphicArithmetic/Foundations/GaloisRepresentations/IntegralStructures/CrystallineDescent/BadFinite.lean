import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.CrystallineDescent.PatchOneAlt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.InfinitelyManyRealQuadraticSteps
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsSplitAtOfDegOne
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RealGal
open UpperTheory.V.Af (FrobEig algSat RepIso)
open UpperTheory.V.Af.Bc (res)
open UpperTheory.Gal.Int.Core
open UpperTheory.Gal.UnramifiedFromSplittingCriterion

namespace UpperTheory.Gal.Int.Core

section

variable {E Ω : Type} [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {l : ℕ} [Fact l.Prime]

private def bad (l : ℕ) {a : ℕ} (π : CuspSub E a) (w₀ : HeightOneSpectrum (𝓞 E)) : Set (HeightOneSpectrum (𝓞 E)) :=
  {w | w = w₀ ∨ ((l : ℕ) : 𝓞 E) ∈ w.asIdeal ∨ ¬ ∃ B, (CG.mk π).HasSat w B}

private theorem bad_finite {a : ℕ} (π : CuspSub E a) (w₀ : HeightOneSpectrum (𝓞 E)) : (bad l π w₀).Finite := by
  have h1 := Filter.eventually_cofinite.1 (GlobalTheory.CongEx.eventually_not_mem_l E l)
  have h2 := Filter.eventually_cofinite.1 (GlobalTheory.CuspRep.UnrSat.eventually_hasSatGL_locRep GlobalTheory.automorphicFormsFiniteGL E a π)
  refine ((Set.finite_singleton w₀).union (h1.union h2)).subset ?_
  rintro w (h | h | h)
  · exact Or.inl h
  · exact Or.inr (Or.inl (not_not.2 h))
  · exact Or.inr (Or.inr h)

private theorem serves (hR : RamUnr) {a : ℕ} (π : CuspSub E a) (ι : Qbar l ≃+* ℂ) (w₀ : HeightOneSpectrum (𝓞 E)) (Q : QCM E Ω)
    (h1 : ∀ t ∈ bad l π w₀, ∀ A : ValuationSubring Ω, IsPlaceOver A t → ∀ g ∈ Dec (F := E) A, Fixes ↥Q.K g)
    (h2 : RamOff (bad l π w₀) Q)
    (h3 : ∀ P : CuspSub ↥Q.K a, IsLift π P → ∃ p : HeightOneSpectrum (𝓞 ↥Q.K) → Prop, RowP Ω p P ι ∧
      (∀ᶠ w : HeightOneSpectrum (𝓞 ↥Q.K) in Filter.cofinite, (normV w).Prime → p w) ∧ ∀ w, w.under (𝓞 E) = w₀ → p w) :
    Serves π ι w₀ Q := by
  refine ⟨fun A hA g hg => ?_, ?_, h3⟩
  · rw [GlobalTheory.ExSplitCM.mem_range_res_iff]
    exact fun x hx => h1 w₀ (Or.inl rfl) A hA g hg ⟨x, hx⟩
  · obtain ⟨w, hw, hT⟩ := hR E Ω _ Q h2
    exact ⟨w, hw, not_not.1 fun h => hT (Or.inr (Or.inr h))⟩

end

theorem joinUp_of' (hS : StepDown) (hC : CsdLift) (hR : RamUnr) (hO : OneUs) (hQ : Quad2Ex) : JoinUp := by
  intro hJ hG hL hcore
  have top : ∀ (E Y Ω : Type) [Field E] [NumberField E] [Field Y] [NumberField Y] [IsCMField Y] [Field Ω] [Algebra E Y]
      [Algebra Y Ω] [IsAlgClosure Y Ω] (δ : Y), RealStep E Ω δ → ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ),
      (∀ (M : Type) [Field M] [NumberField M] [IsCMField M] [Algebra Y M], ∃ w : Fin 3 → HeightOneSpectrum (𝓞 M),
        (∀ i, ((l : ℕ) : 𝓞 M) ∈ (w i).asIdeal) ∧ ∀ i j, i ≠ j → Apart (w i) (w j)) →
      ∀ a : ℕ, 1 ≤ a → ∀ π : CuspSub Y a, InScope .all l π (quadChar Y ^ a) → RowP Ω (fun _ => True) π ι := by
    intro E Y Ω _ _ _ _ _ _ _ _ _ δ hδ l _ ι h3 a ha π hπ
    refine hS hL Y Ω l ι a ha π fun w₀ => ?_
    have hinf : {Q : QCM Y Ω | Step2 (bad l π w₀) Q}.Infinite := by
      refine infOf Y Ω _ fun S hS => ?_
      obtain ⟨Q, ⟨a1, a2, a3, a4, u, hu, a5⟩, hI, d, hd, hU⟩ := hQ E Y Ω δ hδ (bad l π w₀ ∪ S) ((bad_finite π w₀).union hS)
      exact ⟨Q, ⟨⟨a1, a2, fun t ht => a3 t (Or.inl ht), fun w hw => ⟨fun h => (a4 w hw).1 (Or.inl h), (a4 w hw).2⟩, u,
        fun h => hu (Or.inl h), a5⟩, hI, d, hd, fun w hw => hU w (Or.inl hw)⟩, u, fun h => hu (Or.inr h), a5⟩
    refine hinf.mono ?_
    rintro Q ⟨h1, hI, d, hd, hU⟩
    refine serves hR π ι w₀ Q h1.2.2.1 h1.2.2.2.2 fun P hP => ?_
    have hl : ∀ w : HeightOneSpectrum (𝓞 ↥Q.K), ((l : ℕ) : 𝓞 ↥Q.K) ∈ w.asIdeal → w.under (𝓞 Y) ∈ bad l π w₀ :=
      fun w hw => Or.inr (Or.inl ((GlobalTheory.CMFam.natCast_mem_under w l).2 hw))
    obtain ⟨w, hw, hap⟩ := h3 ↥Q.K
    have hF : GlobalTheory.Row9.FieldOK l ↥Q.K := ⟨h1.1, h1.2.1, allUnr_holds Y Ω _ Q h1, fun u hu => (hU u (hl u hu)).1,
      w 0, w 1, w 2, hw 0, hw 1, hw 2, hap 0 1 (by decide), hap 0 2 (by decide), hap 1 2 (by decide)⟩
    have hsq : SqAt d l := (hU _ (hl _ (hw 0))).2 l Fact.out (hw 0)
    have hPs := hC hJ hG Y ↥Q.K l a ha π P hP hπ
    have hgood : Good l P := by
      refine ⟨h1.1, h1.2.1, fun u hu => ?_⟩
      obtain ⟨b1, b2, -⟩ := h1.2.2.2.1 u hu
      refine ⟨fun h => b1 (hl u h), b2, ?_⟩
      obtain ⟨B, hB⟩ : ∃ B, (CG.mk π).HasSat (u.under (𝓞 Y)) B := not_not.1 fun h => b1 (Or.inr (Or.inr h))
      exact ⟨_, hP.sat u _ B (GlobalTheory.RealGal.AttRes.normV_eq_pow u) hB⟩
    exact ⟨UsPl d, hcore ↥Q.K Ω l ι hF hI d hd hsq a ha P ⟨hPs.1, hPs.2.1, hgood, rfl⟩, hO ↥Q.K d hd,
      fun u hu => hU u (Or.inl hu)⟩
  intro E Ω _ _ _ _ _ _ l _ ι a ha π hπ
  obtain ⟨t, ht⟩ := GlobalTheory.CongEx.exists_place_over E l
  refine hS hL E Ω l ι a ha π fun w₀ => (infinitely_many_real_quadratic_steps E Ω _ (bad_finite (l := l) π w₀)).mono fun Q₁ s₁ => ?_
  refine serves hR π ι w₀ Q₁ s₁.2.1 s₁.2.2 fun P₁ hP₁ => ⟨fun _ => True, ?_, by simp, fun _ _ => trivial⟩
  have h₁ := hC hJ hG E ↥Q₁.K l a ha π P₁ hP₁ hπ
  refine hS hL ↥Q₁.K Ω l ι a ha P₁ fun w₁ => (infinitely_many_real_quadratic_steps ↥Q₁.K Ω _ (bad_finite (l := l) P₁ w₁)).mono fun Q₂ s₂ => ?_
  refine serves hR P₁ ι w₁ Q₂ s₂.2.1 s₂.2.2 fun P₂ hP₂ => ⟨fun _ => True, ?_, by simp, fun _ _ => trivial⟩
  have h₂ := hC hJ hG ↥Q₁.K ↥Q₂.K l a ha P₁ P₂ hP₂ h₁
  obtain ⟨δ, hδ, -⟩ := s₂.1
  refine top ↥Q₁.K ↥Q₂.K Ω δ hδ l ι (fun M _ _ _ _ => ?_) a ha P₂ h₂
  obtain ⟨w, hw, hap⟩ := threeApart_holds E Ω _ Q₁ s₁ _ Q₂ s₂ t (Or.inr (Or.inl ht))
    (fun u hu => Or.inr (Or.inl ((GlobalTheory.CMFam.natCast_mem_under (E := E) u l).1 (hu ▸ ht)))) M
  refine ⟨w, fun i => ?_, hap⟩
  rw [← GlobalTheory.CMFam.natCast_mem_under (E := ↥Q₂.K), ← GlobalTheory.CMFam.natCast_mem_under (E := ↥Q₁.K),
    ← GlobalTheory.CMFam.natCast_mem_under (E := E), hw i]
  exact ht

end UpperTheory.Gal.Int.Core
