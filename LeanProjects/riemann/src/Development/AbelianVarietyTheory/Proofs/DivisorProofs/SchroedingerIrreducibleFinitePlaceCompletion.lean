import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenPtSubset
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchwartzBruhatMatrixTranslationModulationIrreduc

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.VacAny
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU GlobalTheory.WeilM
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram mulG colV adjV₁)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple Acts SInf At latAtV realAd evI)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.BigDat

noncomputable section

namespace GlobalTheory.SchrIrred

open ValuativeRel

theorem norm_addChar_eq_one {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (ψ : AddChar k ℂ) (hψ : Continuous ψ) (x : k) : ‖ψ x‖ = 1 := by
  have hle : ∀ y : k, ‖ψ y‖ ≤ 1 := by
    intro y
    have hK : IsCompact ((fun u : k => y * u) '' (𝒪[k] : Set k)) :=
      (IsNonarchimedeanLocalField.isCompact_closedBall k 1).image (by fun_prop)
    obtain ⟨C, hC⟩ := (hK.image (continuous_norm.comp hψ)).isBounded.exists_norm_le
    by_contra h
    push_neg at h
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt C h
    have hmem : ‖ψ (y * (n : k))‖ ∈ (fun z => ‖ψ z‖) '' ((fun u : k => y * u) '' (𝒪[k] : Set k)) :=
      ⟨y * n, ⟨n, natCast_mem _ n, rfl⟩, rfl⟩
    have h2 := hC _ hmem
    rw [Real.norm_of_nonneg (norm_nonneg _), mul_comm, ← nsmul_eq_mul, AddChar.map_nsmul_eq_pow, norm_pow] at h2
    linarith
  have h1 : ψ x * ψ (-x) = 1 := by rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
  have h2 : ‖ψ x‖ * ‖ψ (-x)‖ = 1 := by rw [← norm_mul, h1, norm_one]
  have a := hle x
  have b := hle (-x)
  nlinarith [norm_nonneg (ψ x), norm_nonneg (ψ (-x))]

def toCircle {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (ψ : AddChar k ℂ) (hψ : Continuous ψ) : AddChar k Circle where
  toFun x := ⟨ψ x, mem_sphere_zero_iff_norm.2 (norm_addChar_eq_one ψ hψ x)⟩
  map_zero_eq_one' := Circle.ext (by simp)
  map_add_eq_mul' a b := Circle.ext (by show ψ (a + b) = ψ a * ψ b; exact AddChar.map_add_eq_mul ψ a b)

theorem coe_toCircle {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (ψ : AddChar k ℂ) (hψ : Continuous ψ) (x : k) : (toCircle ψ hψ x : ℂ) = ψ x := rfl

def colH (k : Type) [TopologicalSpace k] (κ : Type) : (κ → k) ≃ₜ Matrix κ Unit k where
  toFun x := Matrix.of fun i _ => x i
  invFun M i := M i ()
  left_inv _ := rfl
  right_inv M := by ext i j; cases j; rfl
  continuous_toFun := by
    refine continuous_pi fun i => continuous_pi fun _ => continuous_apply i
  continuous_invFun := by
    refine continuous_pi fun i => ?_
    exact (continuous_apply () ).comp (continuous_apply i)

theorem sb_comp {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (h : X ≃ₜ Y) {f : Y → ℂ}
    (hf : f ∈ GlobalTheory.WeilM.SB Y) : f ∘ h ∈ GlobalTheory.WeilM.SB X :=
  ⟨hf.1.comp_continuous h.continuous, hf.2.comp_homeomorph h⟩

end GlobalTheory.SchrIrred

namespace GlobalTheory.SchrIrred

open ValuativeRel

theorem schr_irreducible_local (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [CharZero k] [Invertible (2 : k)] {κ : Type} [Fintype κ] (ψk : AddChar k ℂ) (hc : Continuous ψk) (h1 : ψk ≠ 1)
    (N : Submodule ℂ ((κ → k) → ℂ)) (hN : N ≤ GlobalTheory.WeilM.SB (κ → k))
    (hS : ∀ w, ∀ φ ∈ N, schr ψk w φ ∈ N) (φ₀ : (κ → k) → ℂ) (h0 : φ₀ ∈ N) (hne : φ₀ ≠ 0) :
    N = GlobalTheory.WeilM.SB (κ → k) := by
  classical
  let e := colH k κ
  let L : (Matrix κ Unit k → ℂ) →ₗ[ℂ] ((κ → k) → ℂ) := LinearMap.funLeft ℂ ℂ e
  have hL : ∀ Φ, L Φ = Φ ∘ e := fun _ => rfl
  have hcirc : Continuous (toCircle ψk hc) := by
    have : Continuous (fun x => ((toCircle ψk hc x : Circle) : ℂ)) := hc
    exact continuous_induced_rng.2 this
  have hne1 : toCircle ψk hc ≠ 1 := by
    intro h
    apply h1
    ext x
    have := congrArg (fun χ : AddChar k Circle => ((χ x : Circle) : ℂ)) h
    simpa [coe_toCircle] using this
  have hW : N.comap L ≤ GlobalTheory.SplitWeil.SB (Matrix κ Unit k) := by
    intro Φ hΦ
    have h := sb_comp e.symm (hN hΦ)
    have : (Φ ∘ e) ∘ e.symm = Φ := by funext M; simp
    rw [← this]
    exact h
  have hT : ∀ Φ ∈ N.comap L, ∀ x : Matrix κ Unit k, (fun t => Φ (t + x)) ∈ GlobalTheory.SplitWeil.SB (Matrix κ Unit k) →
      (fun t => Φ (t + x)) ∈ N.comap L := by
    intro Φ hΦ x _
    rw [Submodule.mem_comap, hL] at hΦ ⊢
    have h := hS (e.symm x, 0) _ hΦ
    convert h using 1
    funext y
    have he : e (y + e.symm x) = e y + x := by ext i j; cases j; rfl
    simp [schr, he]
  have hM : ∀ Φ ∈ N.comap L, ∀ b : Matrix κ Unit k,
      (fun t => ((toCircle ψk hc (∑ r, ∑ q, b r q * t r q) : Circle) : ℂ) * Φ t) ∈ GlobalTheory.SplitWeil.SB (Matrix κ Unit k) →
      (fun t => ((toCircle ψk hc (∑ r, ∑ q, b r q * t r q) : Circle) : ℂ) * Φ t) ∈ N.comap L := by
    intro Φ hΦ b _
    rw [Submodule.mem_comap, hL] at hΦ ⊢
    have h := hS (0, fun r => b r ()) _ hΦ
    convert h using 1
    funext y
    simp only [schr, Function.comp_apply, coe_toCircle, zero_dotProduct, mul_zero, add_zero]
    congr 2
    simp only [dotProduct, Finset.univ_unique, Finset.sum_singleton]
    exact Finset.sum_congr rfl fun r _ => mul_comm _ _
  have h0' : φ₀ ∘ e.symm ∈ N.comap L := by
    rw [Submodule.mem_comap, hL]
    have : (φ₀ ∘ e.symm) ∘ e = φ₀ := by funext y; simp
    rw [this]; exact h0
  have hne' : φ₀ ∘ e.symm ≠ 0 := by
    intro h
    apply hne
    funext y
    have := congrFun h (e y)
    simpa using this
  have hall := GlobalTheory.IrredSB.sb_irreducible k κ Unit (toCircle ψk hc) hcirc hne1 (N.comap L) hW hT hM _ h0' hne'
  refine le_antisymm hN fun φ hφ => ?_
  have hm : φ ∘ e.symm ∈ N.comap L := by
    rw [hall]
    exact sb_comp e.symm hφ
  rw [Submodule.mem_comap, hL] at hm
  have : (φ ∘ e.symm) ∘ e = φ := by funext y; simp
  rwa [this] at hm

end GlobalTheory.SchrIrred

namespace GlobalTheory.SchrIrred

theorem schr_irreducible : ∀ {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) {κ : Type} [Fintype κ] (ψk : AddChar (Fv F v) ℂ), Continuous ψk → ψk ≠ 1 →
    ∀ N : Submodule ℂ ((κ → Fv F v) → ℂ), N ≤ GlobalTheory.WeilM.SB (κ → Fv F v) → (∀ w, ∀ φ ∈ N, schr ψk w φ ∈ N) → ∀ φ₀ ∈ N, φ₀ ≠ 0 →
      N = GlobalTheory.WeilM.SB (κ → Fv F v) := by
  intro F _ _ v κ _ ψk hc h1 N hN hS φ₀ h0 hne
  haveI : CharZero (Fv F v) := charZero_of_injective_algebraMap (algebraMap F (Fv F v)).injective
  exact schr_irreducible_local (Fv F v) ψk hc h1 N hN hS φ₀ h0 hne

end GlobalTheory.SchrIrred
