import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.AdjointEta.EtaOK
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PrincipalSeriesMatching.EulerdShift
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PrincipalSeriesMatching.SuppTw
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PrincipalSeriesMatching.PolFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PrincipalSeriesMatching.NormVal

open NumberField IsDedekindDomain Polynomial Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.LocGL GlobalTheory.SplitWeil GlobalTheory.SmGL
open UpperTheory.V.Z.Gam UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter GlobalTheory.HenQ UpperTheory.V.Z.Inf UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.Ad
open GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.LocalField
open GroundTheory.Automorphic.GodementSection (localChar)
open Ad3P.DihedralUnramifiedPlaces (toH)
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

private theorem cnt_zero {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (s : Multiset (IrrGL k)) (χ : kˣ →* ℂˣ) (h : ∀ ζ ∈ chars s, ¬ IsUnram (ζ * χ)) : cnt s χ = 0 := by
  unfold cnt
  rw [Multiset.card_eq_zero, Multiset.filter_eq_nil]
  rintro y hy ⟨ζ, hζ, rfl, hu⟩
  exact h ζ ⟨hζ, hy⟩ hu

private theorem pol_one {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (s : Multiset (IrrGL k)) (χ : kˣ →* ℂˣ) (h : cnt s χ = 0) : pol s χ = 1 := by
  obtain ⟨h0, hd, -⟩ := (polFacts k).2.2.2 s χ
  have e := eq_C_of_natDegree_eq_zero (hd.trans h)
  rw [e, eval_C] at h0
  rw [e, h0, C_1]

private theorem prod_sub {α M : Type} [CommMonoid M] (p : α → Prop) [Fintype {a // p a}] (S : Finset α) (g : α → M)
    (h1 : ∀ w : {a // p a}, w.1 ∈ S) (h2 : ∀ a ∈ S, ¬ p a → g a = 1) : ∏ a ∈ S, g a = ∏ w : {a // p a}, g w.1 := by
  rw [← Finset.prod_subtype (S.filter p) (p := p) (fun a => ⟨fun h => (Finset.mem_filter.1 h).2,
    fun h => Finset.mem_filter.2 ⟨h1 ⟨a, h⟩, h⟩⟩) g]
  refine (Finset.prod_subset (Finset.filter_subset _ _) fun a ha hn => h2 a ha fun hp => hn ?_).symm
  exact Finset.mem_filter.2 ⟨ha, hp⟩

theorem UpperTheory.satake_parameters_twisted_automorphic :
    ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] (P : CuspSub K 3) (ξ : HChar K)
        (MainNotions : Finset (HeightOneSpectrum (𝓞 K))) (B : HeightOneSpectrum (𝓞 K) → Multiset ℂˣ) (v : Ad3.Pl)
        (s : ∀ w : HeightOneSpectrum (𝓞 K), Multiset (IrrGL (w.adicCompletion K))),
        GroundTheory.Automorphic.GJStandardL.ramifiedPlaces K ⊆ MainNotions →
        (∀ w ∉ MainNotions, (CG.mk (P.twist ξ)).HasSat w (B w)) → (∀ w, SuppAt P w (s w)) → (∀ w : PlacesOver K v, w.1 ∈ MainNotions) →
        (∀ w ∈ MainNotions, w.under (𝓞 ℚ) ≠ v → ∀ ζ ∈ chars (s w), ¬ IsUnram (ζ * ξ.loc w)) →
        ∃ β : ℂ[X], β ≠ 0 ∧ PairG (eulerL K (cx B) MainNotions) (eulerLd K (cx B) MainNotions) β (Ideal.absNorm v.asIdeal : ℝ)
          (∏ w : PlacesOver K v, (pol (s w.1) (ξ.loc w.1)).comp (X ^ fdeg w)) := by
  intro K _ _ _ P ξ MainNotions B v s hS hB hs hv hr
  have hex : ∀ w, ∃ s', SuppAt (P.twist ξ) w s' ∧ pol s' 1 = pol (s w) (ξ.loc w) ∧ cnt s' 1 = cnt (s w) (ξ.loc w) := fun w => by
    obtain ⟨s', h1, h2, -⟩ := suppTw K 3 (by omega) P w ξ (s w) (hs w)
    have hF := (polFacts (w.adicCompletion K)).2.2.2
    have e : pol s' 1 = pol (s w) (ξ.loc w) := by rw [h2, mul_one]
    exact ⟨s', h1, e, by rw [← (hF s' 1).2.1, e, (hF _ _).2.1]⟩
  choose s' h1 h2 h3 using hex
  have hz : ∀ w ∈ MainNotions, ¬ w.asIdeal.LiesOver v.asIdeal → cnt (s w) (ξ.loc w) = 0 := fun w hw hn =>
    cnt_zero _ _ (hr w hw fun e => hn (by subst e; exact ⟨rfl⟩))
  have hq : 1 < Ideal.absNorm v.asIdeal := NumberField.HeightOneSpectrum.one_lt_absNorm v
  obtain ⟨β, hβ, hP⟩ := sideX K 3 (by omega) (P.twist ξ) MainNotions hS B hB s' (Ideal.absNorm v.asIdeal)
    (fun w => v.asIdeal.inertiaDeg' w.asIdeal) hq (fun w hw => ⟨h1 w, fun hc => by
      have hl : w.asIdeal.LiesOver v.asIdeal := by
        by_contra hn
        exact hc ((h3 w).trans (hz w hw hn))
      exact (normVal ℚ K v ⟨w, hl⟩ 1).2.2.2⟩)
  refine ⟨β, hβ, ?_⟩
  have e : (∏ w ∈ MainNotions, (pol (s' w) 1).comp (X ^ v.asIdeal.inertiaDeg' w.asIdeal)) =
      ∏ w : PlacesOver K v, (pol (s w.1) (ξ.loc w.1)).comp (X ^ fdeg w) := by
    simp only [h2]
    exact prod_sub (fun w : HeightOneSpectrum (𝓞 K) => w.asIdeal.LiesOver v.asIdeal) MainNotions
      (fun w => (pol (s w) (ξ.loc w)).comp (X ^ v.asIdeal.inertiaDeg' w.asIdeal)) hv
      (fun w hw hn => by rw [pol_one _ _ (hz w hw hn), one_comp])
  rw [← e]
  exact hP
