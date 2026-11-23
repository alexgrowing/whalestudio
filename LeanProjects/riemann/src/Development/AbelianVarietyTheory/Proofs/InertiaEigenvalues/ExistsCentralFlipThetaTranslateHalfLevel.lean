import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsFlipDet
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaKernelFockVectorEqOfFinitePointMoveStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCentralFlipTranslateHalfPlacesThetaPairStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FlipScalarMemCoefficientRingAuxiliaryLevelStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FlipScalarPrimePowIntegralAtLevelPlacesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HalfTranslatesLeLevelHalfTranslatesOfDvdStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIdempotentSumSubsetAndConjugateFlipStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevelHalfLeConjPlaceOfNotLeStatement

open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

noncomputable section

namespace GlobalTheory.LevelSeries

variable {D : D7}

theorem not_mem_of_coprime {a b : ℕ} (h : Nat.Coprime a b) {PP : Formalism.L2.DIV.Pl D.host.E}
    (ha : ((a : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) : ((b : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal := fun hb => by
  have h1 : IsCoprime ((a : ℤ) : 𝓞 D.host.E) ((b : ℤ) : 𝓞 D.host.E) :=
    (Nat.isCoprime_iff_coprime.2 h).map (Int.castRingHom (𝓞 D.host.E))
  obtain ⟨u, v, huv⟩ := h1
  push_cast at huv
  apply PP.isPrime.ne_top
  rw [Ideal.eq_top_iff_one, ← huv]
  exact add_mem (Ideal.mul_mem_left _ _ ha) (Ideal.mul_mem_left _ _ hb)

theorem exists_flip_theta : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)) (sW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (f₀ : WO V W → ℂ), VacPair ψ θ V W χV χW om ΛV ΛW sW f₀ → Odd W.rank → ∀ (χ : Formalism.L2.Host.HChar D.host.E) (M₀ l : ℕ), ChiData χW χ M₀ → l.Prime → M₀ ≠ 0 → ∃ (Z : Finset (GA D V)) (c : ℕ), (∀ z ∈ Z, z ∈ GfC V) ∧ ∀ (H : Geo.Tor.Host D.host.E) (l₂ : Geo.Tor.Level H) (pd : ℕ), l₂.M = M₀ * pd → Nat.Coprime pd M₀ → Nat.Coprime pd l → Nat.Coprime l₂.M (GlobalTheory.Tow.badN D) → ∀ (k : Type) [Field k] [NumberField k] (σ : k →+* ℂ) (la : HeightOneSpectrum (𝓞 k)) (O : Subring ℂ), ((l : ℕ) : 𝓞 k) ∈ la.asIdeal → ValRing σ la O → ConjIn D σ → χ.ValuesIn (-1 / 2) σ → zeta l₂.M ∈ O → ∀ (e e₂ : AE D) (P : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e P → (∀ PP ∈ P, ((l₂.M : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) → IsHalfIdem l₂ e₂ → ∃ z₂ ∈ Z, ∃ z₁ ∈ GfC V, OneAt V l z₁ ∧ ∀ f ∈ trSp ψ V W ΛV ΛW f₀ e l₂.M O, ∃ f' ∈ trSp ψ V W ΛV ΛW f₀ e₂ l₂.M O, ∀ (BW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (Q : MvPolynomial (FVar D W.rank V.rank) ℂ) (s : GA D V) (g : GA D W), (l : ℂ) ^ c * thetaKO om s g (stdF ψ θ V W sW BW f Q) = thetaKO om (s * z₂ * z₁) g (stdF ψ θ V W sW BW f' Q) := by
  intro D ψ θ V W χV χW om ΛV ΛW sW f₀ hP hodd χ M₀ l hχ hl hM₀
  have hfin : {PP : Formalism.L2.DIV.Pl D.host.E | ((M₀ : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal}.Finite := by
    have h0 : Ideal.span {((M₀ : ℕ) : 𝓞 D.host.E)} ≠ ⊥ := by
      rw [Ne, Ideal.span_singleton_eq_bot]; exact_mod_cast hM₀
    refine (Ideal.finite_factors h0).subset fun PP hPP => ?_
    exact Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hPP)
  choose zOf hzG hzOne hzFlip using fun T : Finset (Formalism.L2.DIV.Pl D.host.E) =>
    GlobalTheory.T.exists_central_flip_translate_halfPlaces_thetaPair D ψ θ V W χV χW om ΛV ΛW sW f₀ hP T M₀
  choose cOf hcOf using fun T => GlobalTheory.T.flipScalar_primePow_integral_at_levelPlaces D ψ θ V W χV χW om ΛV ΛW sW f₀ hP hodd χ M₀ l hχ hl hM₀ T
  refine ⟨hfin.toFinset.powerset.image zOf, hfin.toFinset.powerset.sup cOf, ?_, ?_⟩
  · intro z hz
    obtain ⟨T, -, rfl⟩ := Finset.mem_image.1 hz
    exact hzG T
  intro H l₂ pd hM hc1 hc2 hbad k _ _ σ la O hla hO hconj hval hz e e₂ P he hPM he₂
  have hoddM : Odd (M₀ * pd) := hM ▸ l₂.odd
  have hoddM₀ : Odd M₀ := (Nat.odd_mul.1 hoddM).1
  have hoddpd : Odd pd := (Nat.odd_mul.1 hoddM).2
  set T₀ := P.filter fun PP => ((M₀ : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal ∧ ¬ l₂.Mb ≤ PP.asIdeal with hT₀
  set T₁ := P.filter fun PP => ((pd : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal ∧ ¬ l₂.Mb ≤ PP.asIdeal with hT₁
  set P₁ := (P \ T₀) ∪ T₀.image Formalism.L2.DIV.conjPl with hP₁
  have hT₁P₁ : T₁ ⊆ P₁ := fun PP hPP => by
    obtain ⟨h1, h2, -⟩ := Finset.mem_filter.1 hPP
    refine Finset.mem_union_left _ (Finset.mem_sdiff.2 ⟨h1, fun h3 => ?_⟩)
    exact not_mem_of_coprime hc1 h2 (Finset.mem_filter.1 h3).2.1
  obtain ⟨⟨eT₀, heT₀⟩, e₁, he₁⟩ := GlobalTheory.T.exists_idempotentSum_subset_and_conjugate_flip D e P T₀ he (Finset.filter_subset _ _)
  obtain ⟨⟨eT₁, heT₁⟩, e₃, he₃⟩ := GlobalTheory.T.exists_idempotentSum_subset_and_conjugate_flip D e₁ P₁ T₁ he₁ hT₁P₁
  have hT₀S : T₀ ∈ hfin.toFinset.powerset :=
    Finset.mem_powerset.2 fun PP hPP => hfin.mem_toFinset.2 (Finset.mem_filter.1 hPP).2.1
  obtain ⟨x₂, hx₂, hstep₂⟩ := hzFlip T₀ eT₀ heT₀ hoddM₀ (Nat.Coprime.coprime_mul_right (hM ▸ hbad)) fun PP hPP => (Finset.mem_filter.1 hPP).2.1
  obtain ⟨z₁, hz₁G, hz₁One, hz₁F⟩ := GlobalTheory.T.exists_central_flip_translate_halfPlaces_thetaPair D ψ θ V W χV χW om ΛV ΛW sW f₀ hP T₁ pd
  obtain ⟨x₁, hx₁, hstep₁⟩ := hz₁F eT₁ heT₁ hoddpd (Nat.Coprime.coprime_mul_left (hM ▸ hbad)) fun PP hPP => (Finset.mem_filter.1 hPP).2.1
  have hsub := GlobalTheory.T.halfTranslates_le_levelHalfTranslates_of_dvd D H l₂ e₂ e₃ _ he₂ he₃ (fun PP hPP => by
    rcases Finset.mem_union.1 hPP with h1 | h1
    · obtain ⟨h2, h3⟩ := Finset.mem_sdiff.1 h1
      rcases Finset.mem_union.1 h2 with h4 | h4
      · obtain ⟨h5, h6⟩ := Finset.mem_sdiff.1 h4
        by_contra h7
        have h8 := hPM PP h5
        rw [hM, Nat.cast_mul] at h8
        rcases PP.isPrime.mem_or_mem h8 with h9 | h9
        · exact h6 (Finset.mem_filter.2 ⟨h5, h9, h7⟩)
        · exact h3 (Finset.mem_filter.2 ⟨h5, h9, h7⟩)
      · obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.1 h4
        obtain ⟨hQ1, -, hQ2⟩ := Finset.mem_filter.1 hQ
        exact GlobalTheory.T.levelHalf_le_conj_place_of_not_le D H l₂ Q (hPM Q hQ1) hQ2
    · obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.1 h1
      obtain ⟨hQ1, -, hQ2⟩ := Finset.mem_filter.1 hQ
      exact GlobalTheory.T.levelHalf_le_conj_place_of_not_le D H l₂ Q (hPM Q hQ1) hQ2) ψ V W ΛV ΛW f₀ l₂.M O
  have hlO : ((l : ℕ) : ℂ) ∈ O := natCast_mem O l
  have ha : (l : ℂ) ^ (hfin.toFinset.powerset.sup cOf) * flipScal χW V W T₀ M₀ x₂ ∈ O := by
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le' (Finset.le_sup (f := cOf) hT₀S)
    rw [hd, pow_add, mul_assoc]
    exact mul_mem (pow_mem hlO _) (hcOf T₀ eT₀ x₂ heT₀ (fun PP hPP => (Finset.mem_filter.1 hPP).2.1) hx₂ k σ la O hla hO
      hconj hval hoddM₀ (Nat.Coprime.coprime_mul_right (hM ▸ hbad)))
  have hb : flipScal χW V W T₁ pd x₁ ∈ O :=
    GlobalTheory.T.flipScalar_mem_coefficientRing_auxiliaryLevel D ψ θ V W χV χW om ΛV ΛW sW f₀ hP hodd χ M₀ l pd hχ hl hc1 hc2 (Nat.Coprime.coprime_mul_left (hM ▸ hbad))
      k σ la O hla hO hconj hval T₁ eT₁ x₁ heT₁ (fun PP hPP => (Finset.mem_filter.1 hPP).2.1) hx₁
  refine ⟨zOf T₀, Finset.mem_image_of_mem _ hT₀S, z₁, hz₁G,
    hz₁One l (fun PP hPP => not_mem_of_coprime hc2 (Finset.mem_filter.1 hPP).2.1), fun f hf => ?_⟩
  obtain ⟨F₁, hF₁, hF₁eq⟩ := hstep₂ l₂.M pd e e₁ P O hM
    (fun PP hPP => not_mem_of_coprime (Nat.Coprime.symm hc1) (Finset.mem_filter.1 hPP).2.1) he (Finset.filter_subset _ _) he₁ hz f hf
  obtain ⟨F₂, hF₂, hF₂eq⟩ := hstep₁ l₂.M M₀ e₁ e₃ P₁ O (by rw [hM, mul_comm])
    (fun PP hPP => not_mem_of_coprime hc1 (Finset.mem_filter.1 hPP).2.1) he₁ hT₁P₁ he₃ hz F₁ hF₁
  set c := hfin.toFinset.powerset.sup cOf
  refine ⟨(⟨_, mul_mem ha hb⟩ : O) • F₂, Submodule.smul_mem _ _ (hsub hF₂), fun BW Q s g => ?_⟩
  have hom : om (zOf T₀ * z₁, 1) ((⟨_, mul_mem ha hb⟩ : O) • F₂) = ((l : ℂ) ^ c) • f := by
    have e1 : ((zOf T₀ * z₁, 1) : GA D V × GA D W) = (zOf T₀, 1) * (z₁, 1) := by simp
    rw [e1, map_mul, Module.End.mul_apply, Subring.smul_def]
    change om (zOf T₀, 1) (om (z₁, 1) (((l : ℂ) ^ c * flipScal χW V W T₀ M₀ x₂ * flipScal χW V W T₁ pd x₁) • F₂)) = _
    rw [← smul_smul, map_smul, hF₂eq, ← smul_smul, map_smul, hF₁eq]
  have := GlobalTheory.T.thetaKernel_fockVector_eq_of_finite_point_move D ψ θ V W χV χW om ΛV ΛW sW f₀ hP (zOf T₀ * z₁) (mul_mem (hzG T₀) hz₁G) e e₂ l₂.M O f _ _ hf
    (Submodule.smul_mem _ _ (hsub hF₂)) hom BW Q s g
  rw [← mul_assoc] at this
  exact this

end GlobalTheory.LevelSeries

end
