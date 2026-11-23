import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HilbertKodairaSpencer
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPullbackDegPreStrictLineBundleIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingActionOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsIsGenOfUniqueFactorizationMonoid

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.RealMult.Obj

attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.InvGlue

theorem bijective_localized {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M] (r : A) (m : M)
    (hsurj : ∀ x : M, ∃ (n : ℕ) (a : A), r ^ n • x = a • m)
    (hinj : ∀ a : A, a • m = 0 → ∃ n : ℕ, r ^ n * a = 0) :
    Function.Bijective (LinearMap.toSpanSingleton (Localization.Away r)
      (LocalizedModule (Submonoid.powers r) M) (LocalizedModule.mk m 1)) := by
  let pw : ℕ → Submonoid.powers r := fun n => ⟨r ^ n, Submonoid.pow_mem _ (Submonoid.mem_powers r) n⟩
  constructor
  · rw [injective_iff_map_eq_zero]
    intro y hy
    induction y using Localization.induction_on with
    | H p =>
      obtain ⟨a, s⟩ := p
      simp only [LinearMap.toSpanSingleton_apply] at hy
      rw [LocalizedModule.mk_smul_mk, _root_.mul_one] at hy
      rw [← LocalizedModule.zero_mk s, LocalizedModule.mk_eq] at hy
      obtain ⟨u, hu⟩ := hy
      simp only [smul_zero] at hu
      have : ((u : A) * (s : A) * a) • m = 0 := by
        rw [mul_smul, mul_smul]; simpa [Submonoid.smul_def] using hu
      obtain ⟨n, hn⟩ := hinj _ this
      rw [Localization.mk_eq_mk', IsLocalization.mk'_eq_zero_iff]
      exact ⟨pw n * u * s, by simpa [pw, _root_.mul_assoc] using hn⟩
  · intro z
    induction z using LocalizedModule.induction_on with
    | h x s =>
      obtain ⟨n, a, hn⟩ := hsurj x
      refine ⟨Localization.mk a (pw n * s), ?_⟩
      simp only [LinearMap.toSpanSingleton_apply]
      rw [LocalizedModule.mk_smul_mk, _root_.mul_one, ← hn,
        ← LocalizedModule.mk_cancel_common_left (pw n) s x]
      rfl

theorem invertible_of_locally_singly_generated : ∀ (R O : Type) [CommRing R] [CommRing O] (J : Type) [Fintype J] (b : Module.Basis J ℤ O)
    (M : Type) [AddCommGroup M] [Module R M] [Module O M] [SMulCommClass R O M],
    (∀ p : Ideal R, p.IsMaximal → ∃ g : R, g ∉ p ∧ ∃ m : M,
      (∀ x : M, ∃ (n : ℕ) (c : J →₀ R), g ^ n • x = Finsupp.linearCombination R (fun i => b i • m) c) ∧
      (∀ c : J →₀ R, Finsupp.linearCombination R (fun i => b i • m) c = 0 → ∃ n : ℕ, g ^ n • c = 0)) →
    letI : Module (R ⊗[ℤ] O) M := TensorProduct.Algebra.module
    Module.Invertible (R ⊗[ℤ] O) M := by
  intro R O _ _ J _ b M _ _ _ _ hyp
  letI : Module (R ⊗[ℤ] O) M := TensorProduct.Algebra.module
  let B := Algebra.TensorProduct.basis R b
  have hL : ∀ (m : M) (c : J →₀ R),
      (B.repr.symm c) • m = Finsupp.linearCombination R (fun i => b i • m) c := by
    intro m c
    induction c using Finsupp.induction_linear with
    | zero => simp
    | add c d hc hd => rw [map_add, add_smul, hc, hd, map_add]
    | single i x =>
      rw [Module.Basis.repr_symm_single, Finsupp.linearCombination_single]
      simp only [B, Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul,
        _root_.mul_one]
      exact TensorProduct.Algebra.smul_def x (b i) m
  have hr : ∀ (g : R) (x : M), (algebraMap R (R ⊗[ℤ] O) g) • x = g • x := by
    intro g x
    rw [Algebra.TensorProduct.algebraMap_apply, TensorProduct.Algebra.smul_def, one_smul]
    simp
  let G : Set R := {g | ∃ m : M,
      (∀ x : M, ∃ (n : ℕ) (c : J →₀ R), g ^ n • x = Finsupp.linearCombination R (fun i => b i • m) c) ∧
      (∀ c : J →₀ R, Finsupp.linearCombination R (fun i => b i • m) c = 0 → ∃ n : ℕ, g ^ n • c = 0)}
  have hG : Ideal.span G = ⊤ := by
    by_contra h
    obtain ⟨p, hp, hGp⟩ := Ideal.exists_le_maximal _ h
    obtain ⟨g, hg, hgG⟩ := hyp p hp
    exact hg (hGp (Ideal.subset_span hgG))
  let s : Set (R ⊗[ℤ] O) := algebraMap R (R ⊗[ℤ] O) '' G
  have hs : Ideal.span s = ⊤ := by
    rw [← Ideal.map_span, hG, Ideal.map_top]
  refine GlobalTheory.invertible_of_isLocalizedModule_span s hs (fun r => Localization.Away r.1)
    (fun r => LocalizedModule (Submonoid.powers r.1) M)
    (fun r => LocalizedModule.mkLinearMap (Submonoid.powers r.1) M) fun r => ?_
  obtain ⟨g, ⟨m, h1, h2⟩, hg⟩ := r.2
  refine GlobalTheory.invertible_of_bijective_toSpanSingleton (e := LocalizedModule.mk m 1)
    (bijective_localized r.1 m ?_ ?_)
  · intro x
    obtain ⟨n, c, hc⟩ := h1 x
    exact ⟨n, B.repr.symm c, by rw [← hg, ← map_pow, hr, hL, hc]⟩
  · intro a ha
    have ha' : a = B.repr.symm (B.repr a) := (B.repr.symm_apply_apply a).symm
    obtain ⟨n, hn⟩ := h2 (B.repr a) (by rw [← hL, ← ha', ha])
    refine ⟨n, ?_⟩
    rw [← hg, ← map_pow, ← Algebra.smul_def, ha', ← map_smul, hn, map_zero]

end GlobalTheory.InvGlue
