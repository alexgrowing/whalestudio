import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.Entire
import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Imports
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.RealStructures.Imports
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.ImportsBis
import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.HeckeCharacterEqOfCofinite

open NumberField IsDedekindDomain Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global
open UpperTheory.ConvolutionTheory.R2
open UpperTheory.ConvolutionTheory.RankTwoDescent

namespace UpperTheory.ConvolutionTheory.RankTwoDescent

private theorem bad_of_dvd {a b : ℕ} (h : a ∣ b) {v : H.P ℚ} (ha : Bad a v) : Bad b v := by
  obtain ⟨c, rfl⟩ := h
  unfold Bad at ha ⊢
  rw [Nat.cast_mul]
  exact Ideal.mul_mem_right _ _ ha

private theorem exists_bad {S : Set (H.P ℚ)} (hS : S.Finite) : ∃ m : ℕ, 0 < m ∧ ∀ v ∈ S, Bad m v := by
  classical
  refine ⟨∏ v ∈ hS.toFinset, Ideal.absNorm v.asIdeal, Finset.prod_pos fun v _ => ?_, fun v hv => ?_⟩
  · exact Nat.pos_of_ne_zero fun h => v.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  · refine bad_of_dvd (Finset.dvd_prod_of_mem _ (hS.mem_toFinset.2 hv)) ?_
    exact Ideal.absNorm_mem _

private theorem quad_sq {E : Type} [Field E] [NumberField E] {η : HChar ℚ} (hq : IsQuadCharOf E η) : η ^ 2 = 1 := by
  apply GlobalTheory.T.hecke_character_eq_of_cofinite ℚ (η ^ 2) 1
  have hc : ∀ᶠ v : H.P ℚ in cofinite, ∃ w : H.P E, w.under (𝓞 ℚ) = v ∧
      η.UnrAt v ∧ η.val v = if normV w = normV v then 1 else -1 := by
    unfold IsQuadCharOf at hq
    rw [Filter.eventually_cofinite] at hq ⊢
    refine (hq.image fun w => w.under (𝓞 ℚ)).subset fun v hv => ?_
    have := v.isMaximal
    obtain ⟨Q, hQ, hl⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 E) v.asIdeal
    have hne : Q ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q
    have e : (⟨Q, hQ.isPrime, hne⟩ : HeightOneSpectrum (𝓞 E)).under (𝓞 ℚ) = v :=
      HeightOneSpectrum.ext hl.over.symm
    refine ⟨⟨Q, hQ.isPrime, hne⟩, fun hP => hv ⟨_, e, hP v hl.over⟩, e⟩
  filter_upwards [hc] with v hv
  obtain ⟨w, -, hu, hval⟩ := hv
  refine ⟨fun x hx => ?_, fun x _ => rfl, ?_⟩
  · rw [pow_two, HChar.loc_mul, hu x hx, one_mul]
  · have e1 : (1 : HChar ℚ).val v = 1 := rfl
    rw [pow_two, HChar.val_mul, e1, hval]
    split_ifs <;> simp

end UpperTheory.ConvolutionTheory.RankTwoDescent

theorem UpperTheory.ConvolutionTheory.RankTwoDescent.asai_of :
    TrAdm → ExGd → ChEx → AsEx → Ext → Lan → AsaiNV := by
  intro hTr hEx hCh hAs hExt hLan E _ _ _ D M U P ω η hCI hCen hU hq ⟨h1, h2⟩
  have hη : η ^ 2 = 1 := quad_sq hq
  have c1 : ∀ a, ((ω⁻¹).1 a * ω.1 a) ^ 2 = 1 := by
    intro a
    show ((ω.1 a)⁻¹ * ω.1 a) ^ 2 = 1
    simp
  have c2 : ∀ a, (((ω * η)⁻¹).1 a * ω.1 a) ^ 2 = 1 := by
    intro a
    have e : (η.1 a) ^ 2 = 1 := by
      have := congrArg (fun c : HChar ℚ => c.1 a) hη
      exact this
    show ((ω.1 a * η.1 a)⁻¹ * ω.1 a) ^ 2 = 1
    rw [mul_inv, mul_comm (ω.1 a)⁻¹, mul_assoc, inv_mul_cancel, mul_one, inv_pow, e, inv_one]
  have hAdm := hTr E D P ω ω⁻¹ hCen hU c1
  obtain ⟨n₁, hn₁, hc₁⟩ := hCh ω⁻¹
  obtain ⟨n₂, hn₂, hc₂⟩ := hCh (ω * η)⁻¹
  obtain ⟨m, hm, hbad⟩ := exists_bad (((Filter.eventually_cofinite.1 hq).union (Filter.eventually_cofinite.1 hCI)).image fun w : H.P E => w.under (𝓞 ℚ))
  obtain ⟨L, N, φ, hL, hG, hW⟩ := hEx E D P ω ω⁻¹ hCen hU c1 hAdm (n₁ * n₂ * m) (by positivity)
  have hLN := hG.dvd
  have hgood : ∀ w : H.P E, ¬ Bad N (w.under (𝓞 ℚ)) → (∀ v : H.P ℚ, v.asIdeal = w.asIdeal.comap (algebraMap (𝓞 ℚ) (𝓞 E)) →
      η.UnrAt v ∧ η.val v = if normV w = normV v then 1 else -1) ∧
      ∀ w' : H.P E, w'.under (𝓞 ℚ) = w.under (𝓞 ℚ) → ∃ B, (CG.mk P).HasSat w B ∧ (CG.mk P).HasSat w' B := by
    intro w hw
    by_contra hcon
    refine hw (bad_of_dvd ((Dvd.intro_left _ rfl : m ∣ n₁ * n₂ * m).trans (hL.trans hLN)) (hbad _ ⟨w, ?_, rfl⟩))
    by_contra hn
    rw [Set.mem_union, not_or, Set.mem_setOf_eq, Set.mem_setOf_eq, not_not, not_not] at hn
    exact hcon hn
  have e₁ : ChOk ω⁻¹ L := hc₁ L ((Dvd.intro _ rfl : n₁ ∣ n₁ * n₂).trans ((Dvd.intro _ rfl : n₁ * n₂ ∣ n₁ * n₂ * m).trans hL))
  have e₂ : ChOk (ω * η)⁻¹ L := hc₂ L ((Dvd.intro_left _ rfl : n₂ ∣ n₁ * n₂).trans ((Dvd.intro _ rfl : n₁ * n₂ ∣ n₁ * n₂ * m).trans hL))
  obtain ⟨a, ha, hs⟩ := hAs E D P ω ω⁻¹ hCen hU c1 L N φ hG
  obtain ⟨a', ha', hs'⟩ := hAs E D P ω (ω * η)⁻¹ hCen hU c2 L N φ hG
  exact hLan E D P ω ω⁻¹ hCen hU c1 η rfl L N φ hG
    (fun w hw => ((hgood w hw).1 _ rfl).2)
    (fun w w' hw hww => (hgood w hw).2 w' hww)
    e₁ e₂ a a' ha ha' hs hs'
    (hExt E D P ω ω⁻¹ hCen hU c1 M U h1 L N φ e₁ hG hW a ha hs)
    (hExt E D P ω (ω * η)⁻¹ hCen hU c2 M U h2 L N φ e₂ hG hW a' ha' hs')
