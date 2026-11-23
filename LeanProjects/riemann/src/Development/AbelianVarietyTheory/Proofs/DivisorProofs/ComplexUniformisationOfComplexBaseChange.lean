import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHolPeriods
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationAtCorrespondOfCartesianStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHolToBaseChangeComplexIffStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.HolPairA

noncomputable section

namespace GlobalTheory.PELU

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped Matrix

theorem isHolTo_congr_on {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {X : Scheme.{0}} {B : Set V}
    {y y' : V → (Sp ℂ ⟶ X)} (h : ∀ b ∈ B, y b = y' b) : IsHolTo B y ↔ IsHolTo B y' := by
  have hs : ∀ U : X.Opens, {b ∈ B | ⊤ ≤ y b ⁻¹ᵁ U} = {b ∈ B | ⊤ ≤ y' b ⁻¹ᵁ U} := fun U =>
    Set.ext fun b => ⟨fun ⟨hb, h'⟩ => ⟨hb, by rw [← h b hb]; exact h'⟩, fun ⟨hb, h'⟩ => ⟨hb, by rw [h b hb]; exact h'⟩⟩
  constructor
  · intro H U s
    obtain ⟨h1, h2⟩ := H U s
    rw [← hs U]
    exact ⟨h1, h2.congr fun b hb => by rw [h b hb.1]⟩
  · intro H U s
    obtain ⟨h1, h2⟩ := H U s
    rw [hs U]
    exact ⟨h1, h2.congr fun b hb => by rw [h b hb.1]⟩

theorem unif_of_isBC : ∀ (O : Type) [Ring O] (bar : O → O) (g : ℕ) (ρ : O →+* Matrix (Fin g) (Fin g) ℂ) (R : Type) [CommRing R]
    (σ : R →+* ℂ) (Λ : Type) (F : Fam R O Λ g) (N : ℕ) (C : ∀ D' : PLat O bar, (Λ → D'.La) → Prop) (F' : Fam ℂ O Λ g),
    IsBC F' F σ → Nonempty (Unif F' (RingHom.id ℂ) ρ N C) → Nonempty (Unif F σ ρ N C) := by
  intro O _ bar g ρ R _ σ Λ F N C F' hbc hU
  obtain ⟨U'⟩ := hU
  obtain ⟨f, φ, hpb, hgp, hact, hL, heta⟩ := hbc
  have hw : φ ≫ F.A.hom = F'.A.hom ≫ f := hgp.1.w
  have hsq : f ≫ F.s = F'.s ≫ spMap σ := hpb.w
  have hid : spMap (RingHom.id ℂ) = 𝟙 _ := Spec.map_id _
  have hbase : ∀ y' : Sp ℂ ⟶ F'.X, y' ≫ F'.s = spMap (RingHom.id ℂ) → (y' ≫ f) ≫ F.s = spMap σ := by
    intro y' h
    rw [Category.assoc, hsq, ← Category.assoc, h, hid, Category.id_comp]
  have hinj : ∀ y₁ y₂ : Sp ℂ ⟶ F'.X, y₁ ≫ F'.s = spMap (RingHom.id ℂ) → y₂ ≫ F'.s = spMap (RingHom.id ℂ) →
      y₁ ≫ f = y₂ ≫ f → y₁ = y₂ := fun y₁ y₂ h₁ h₂ h => hpb.hom_ext h (by rw [h₁, h₂])
  let exF : ∀ i P, (Fin g → ℂ) → (Over.mk (U'.u i P ≫ f) ⟶ F.A) := fun i P z =>
    Over.homMk ((U'.ex i P z).left ≫ φ) (by rw [Category.assoc, hw, ← Category.assoc, Over.w]; rfl)
  refine ⟨{
      n := U'.n, Di := U'.Di, t := U'.t, mem := U'.mem, ne := U'.ne, all := U'.all, distinct := U'.distinct
      u := fun i P => U'.u i P ≫ f, ex := exF, unif := ?_, onto := ?_, disj := ?_, fibre := ?_, hol := ?_, lift := ?_ }⟩
  · intro i P hP
    have h := U'.unif i P hP
    obtain ⟨e, he, hee⟩ := (GlobalTheory.T.uniformisationAt_correspond_of_cartesian O bar g ρ R ℂ σ (RingHom.id ℂ) Λ F F' N f φ hgp hact hL heta (U'.Di i) (U'.t i) P
      (U'.u i P) h.1 (hbase _ h.1)).1 _ h
    have : e = exF i P := funext fun z => Over.OverMorphism.ext (by rw [hee z]; rfl)
    rw [← this]
    exact he
  · intro y hy
    obtain ⟨i, P, hP, hu⟩ := U'.onto (hpb.lift y (spMap (RingHom.id ℂ)) (by rw [hy, hid, Category.id_comp]))
      (IsPullback.lift_snd _ _ _ _)
    refine ⟨i, P, hP, ?_⟩
    show U'.u i P ≫ f = y
    rw [hu, IsPullback.lift_fst]
  · intro i j P P' hP hP' h
    exact U'.disj i j P P' hP hP' (hinj _ _ (U'.unif i P hP).1 (U'.unif j P' hP').1 h)
  · intro i P P' hP hP'
    refine Iff.trans ⟨fun h => hinj _ _ (U'.unif i P hP).1 (U'.unif i P' hP').1 h, fun h => ?_⟩ (U'.fibre i P P' hP hP')
    show U'.u i P ≫ f = U'.u i P' ≫ f
    rw [h]
  · intro i m B P hB hP
    obtain ⟨h1, h2⟩ := U'.hol i m B P hB hP
    refine ⟨(GlobalTheory.T.isHolTo_baseChange_complex_iff R σ F.X F'.X F.s F'.s f hpb (Fin m → ℂ) B (fun b => U'.u i (P b))
      (fun b hb => (U'.unif i (P b) (hP.1 b hb)).1)).1 h1, ?_⟩
    exact ReciprocityTheory.ChartRestriction.G.PullbackSections.isHolTo_comp h2 φ
  · intro m B y hB hy hhol b₀ hb₀
    classical
    let y' : (Fin m → ℂ) → (Sp ℂ ⟶ F'.X) := fun b =>
      if h : y b ≫ F.s = spMap σ then hpb.lift (y b) (spMap (RingHom.id ℂ)) (by rw [h, hid, Category.id_comp])
      else hpb.lift (y b₀) (spMap (RingHom.id ℂ)) (by rw [hy b₀ hb₀, hid, Category.id_comp])
    have hy'1 : ∀ b ∈ B, y' b ≫ F'.s = spMap (RingHom.id ℂ) := by
      intro b hb
      simp only [y', dif_pos (hy b hb)]
      exact IsPullback.lift_snd _ _ _ _
    have hy'2 : ∀ b ∈ B, y' b ≫ f = y b := by
      intro b hb
      simp only [y', dif_pos (hy b hb)]
      exact IsPullback.lift_fst _ _ _ _
    have hh : IsHolTo B y' := (GlobalTheory.T.isHolTo_baseChange_complex_iff R σ F.X F'.X F.s F'.s f hpb _ B y' hy'1).2
      ((isHolTo_congr_on fun b hb => (hy'2 b hb).symm).1 hhol)
    obtain ⟨B', i, P, hB', hb', hsub, hP, hu⟩ := U'.lift m B y' hB hy'1 hh b₀ hb₀
    refine ⟨B', i, P, hB', hb', hsub, hP, fun b hb => ?_⟩
    show U'.u i (P b) ≫ f = y b
    rw [hu b hb, hy'2 b (hsub hb)]

end GlobalTheory.PELU
