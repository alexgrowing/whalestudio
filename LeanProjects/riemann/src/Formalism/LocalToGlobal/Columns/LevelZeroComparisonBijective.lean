import Formalism.LocalToGlobal.Columns.DilYStab
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.PenultimateKernelDiamondInvariant

open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Ker

section Zero

variable {X : Fields} {Pr : Primes X} {R : Ranks} {W : Wts X Pr.Word R} {Λ : ∀ j, LevFam X.E X.K (R.N j) Pr.vGs}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}
  {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))} {u : Pr.Word} {m2 : ℕ}

attribute [local instance] ptYAct

variable (Λ L) in

structure Step0Hyp : Prop where
  uniq : ∀ b b' : L.β 0, b = b'
  levG : ∀ b, L.levG 0 b = Λ 0
  levQ : ∀ b, L.levQ 0 b = LevQFam.top X.E X.K (R.N 0) (QE sel (mu : Chr X.F X.E X.K))

theorem mem_grp_of_eq {E K : Type} [Field E] [NumberField E] [Field K] {n : ℕ} {SG : Finset (HeightOneSpectrum (𝓞 E))} {Λ₁ Λ₂ : LevFam E K n SG}
    (h : Λ₁ = Λ₂) {g : GLG E n SG} (hg : g ∈ Λ₁.grp) : g ∈ Λ₂.grp := h ▸ hg

theorem frame_move {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {P : HeightOneSpectrum (𝓞 E)} {N N' : Submodule (𝓞 E) (Sp E n)}
    {f f' γ : Sp E n ≃ₗ[E] Sp E n} (hf : ∀ x, f x ∈ localization₂ P.asIdeal N ↔ x ∈ stdAt E n P) (hf' : ∀ x, f' x ∈ localization₂ P.asIdeal N' ↔ x ∈ stdAt E n P)
    (hN : localization₂ P.asIdeal N = localization₂ P.asIdeal (gmap γ N')) : f⁻¹ * γ * f' ∈ GLint E n P := by
  intro x
  show f.symm (γ (f' x)) ∈ stdAt E n P ↔ x ∈ stdAt E n P
  rw [← hf, LinearEquiv.apply_symm_apply, hN, mem_localization_gmap, LinearEquiv.symm_apply_apply, hf']

def levelZeroClassMap (c : (chFY W sel mu cst L u m2 0).Cl) : StCl W Λ u 0 := (stepGSD W Λ u 0).cls (classRepresentativePair c).deco

def stabZeroY (H : Step0Hyp Λ L) {b : L.β 0} (x : PtY W cst L u m2 0 b) :
    MulAction.stabilizer ((chFY W sel mu cst L u m2 0).mem b).G x → MulAction.stabilizer (stepGSD W Λ u 0).G x.deco :=
  fun g => ⟨(g.1.1, ⟨g.1.2.1.1, mem_grp_of_eq (H.levG b) g.1.2.1.2⟩), congrArg PtY.deco g.2⟩

variable (σ₀ : X.K →+* ℂ) (hσ : ∀ x : X.K, σ₀ (star x) = starRingEnd ℂ (σ₀ x))

variable (W Λ cst L u m2) in

def e0LY : (StCl W Λ u 0 → FrS X σ₀ (R.N 0) → ℂ) →ₗ[ℂ] ((chFY W sel mu cst L u m2 0).Cl → FrS X σ₀ (R.N 0) → ℂ) where
  toFun F c := (stepEv W Λ σ₀ hσ u 0).atPt (classRepresentativePair c).deco F
  map_add' F G := by
    funext c
    exact map_add ((stepEv W Λ σ₀ hσ u 0).trPt (classRepresentativePair c).deco) _ _
  map_smul' t F := by
    funext c
    exact map_smul ((stepEv W Λ σ₀ hσ u 0).trPt (classRepresentativePair c).deco) t _

end Zero

end Formalism.L2.Col
