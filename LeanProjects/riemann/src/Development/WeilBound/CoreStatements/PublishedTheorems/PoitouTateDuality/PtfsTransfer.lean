import Mathlib
import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.PtfsDefs

noncomputable section

open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate
  PositivityTheory.PoitouTateConclusion

namespace PositivityTheory.Lit1.PTN

section Abstract

variable {R : Type} [CommRing R]

theorem exact_of_transfer {A B C A' B' C' : Type} [AddCommGroup A] [Module R A] [AddCommGroup B]
    [Module R B] [AddCommGroup C] [Module R C] [AddCommGroup A'] [Module R A'] [AddCommGroup B']
    [Module R B'] [AddCommGroup C'] [Module R C'] (f : A →ₗ[R] B) (g : B →ₗ[R] C)
    (f' : A' →ₗ[R] B') (g' : B' →ₗ[R] C') (eA : A ≃ₗ[R] A') (eB : B ≃ₗ[R] B') (eC : C ≃ₗ[R] C')
    (u v : Rˣ) (hf : ∀ a, f' (eA a) = u • eB (f a)) (hg : ∀ b, g' (eB b) = v • eC (g b))
    (h : Function.Exact f' g') : Function.Exact f g := by
  unfold Function.Exact at h ⊢
  intro b
  constructor
  · intro hb
    have h1 : g' (eB b) = 0 := by rw [hg, hb, map_zero, smul_zero]
    obtain ⟨a', ha'⟩ := (h (eB b)).1 h1
    refine ⟨(u : R) • eA.symm a', eB.injective ?_⟩
    have := hf (eA.symm a')
    rw [LinearEquiv.apply_symm_apply, ha'] at this
    rw [map_smul, map_smul, this, Units.smul_def]
  · rintro ⟨a, rfl⟩
    have h2 : g' (f' (eA a)) = 0 := (h _).2 ⟨_, rfl⟩
    rw [hf, Units.smul_def, map_smul, hg, ← Units.smul_def, smul_eq_zero_iff_eq,
      smul_eq_zero_iff_eq, LinearEquiv.map_eq_zero_iff] at h2
    exact h2

end Abstract

section Published

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
  {l : ℕ} [Fact l.Prime] {r : ℕ} (S : Finset (HeightOneSpectrum (𝓞 F)))
  (Av : S → ValuationSubring Ω)
  (μ : GS Ω (S : Set (HeightOneSpectrum (𝓞 F))) →* (ZMod (l ^ r))ˣ)
  (j : ∀ v : S, H2 ((charRep μ).comp (locFam S Av v)) →ₗ[ZMod (l ^ r)] ZMod (l ^ r))
  {M : Type} [AddCommGroup M] [Module (ZMod (l ^ r)) M] [TopologicalSpace M] [DiscreteTopology M]
  (ρ : Representation (ZMod (l ^ r)) (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M)
  (hρ : ContAction ρ)

theorem nineTermExact_of_nineCmp
    (h : NineCmp (loc0 S Av ρ) (tr0 S Av μ j ρ) (loc1 S Av ρ) (tr1 S Av μ j ρ hρ)
      (loc2 S Av ρ) (tr2 S Av μ j ρ)) : NineTermExact S Av μ j ρ hρ := by
  obtain ⟨B0, B1, B2, B3, B4, B5, B6, B7, BetaSesquilinearity, g0, g1, g2, g3, g4, g5, g6, g7,
    e0, e1, e2, e3, e4, e5, e6, e7, e8, u, h0, h1, h3, h4, h6, h7,
    i0, x01, x12, x23, x34, x45, x56, x67, s7⟩ := h
  have k2 : ∀ a, g2 (e2 a) = (1 : (ZMod (l ^ r))ˣ) • e3 ((e3.symm.toLinearMap ∘ₗ g2 ∘ₗ e2.toLinearMap) a) := by
    intro a; rw [one_smul]; exact (e3.apply_symm_apply _).symm
  have k5 : ∀ a, g5 (e5 a) = (1 : (ZMod (l ^ r))ˣ) • e6 ((e6.symm.toLinearMap ∘ₗ g5 ∘ₗ e5.toLinearMap) a) := by
    intro a; rw [one_smul]; exact (e6.apply_symm_apply _).symm
  refine ⟨e3.symm.toLinearMap ∘ₗ g2 ∘ₗ e2.toLinearMap, e6.symm.toLinearMap ∘ₗ g5 ∘ₗ e5.toLinearMap,
    ?_, exact_of_transfer _ _ _ _ e0 e1 e2 _ _ h0 h1 x01,
    exact_of_transfer _ _ _ _ e1 e2 e3 _ _ h1 k2 x12,
    exact_of_transfer _ _ _ _ e2 e3 e4 _ _ k2 h3 x23,
    exact_of_transfer _ _ _ _ e3 e4 e5 _ _ h3 h4 x34,
    exact_of_transfer _ _ _ _ e4 e5 e6 _ _ h4 k5 x45,
    exact_of_transfer _ _ _ _ e5 e6 e7 _ _ k5 h6 x56,
    exact_of_transfer _ _ _ _ e6 e7 e8 _ _ h6 h7 x67, ?_⟩
  · intro a b hab
    apply e0.injective
    apply i0
    rw [h0, h0, hab]
  · intro y
    obtain ⟨b, hb⟩ := s7 (e8 y)
    refine ⟨((u 5 : (ZMod (l ^ r))ˣ) : ZMod (l ^ r)) • e7.symm b, e8.injective ?_⟩
    have := h7 (e7.symm b)
    rw [LinearEquiv.apply_symm_apply, hb] at this
    rw [map_smul, map_smul, this, Units.smul_def]

end Published

end PositivityTheory.Lit1.PTN
