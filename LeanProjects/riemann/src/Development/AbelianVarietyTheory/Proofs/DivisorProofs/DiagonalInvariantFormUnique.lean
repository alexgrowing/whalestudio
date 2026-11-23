import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsDblOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjLinApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicWeilRepSchrodingerModelUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductFunctionOnSumCoordsMemAdelicSchwartzSpace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerRestriction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StarMemAdelicSchwartzSpaceNumberField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagonalLagrangianInvariantForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterInvariantAdelicFormEqMulEvalZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanPartialFourierSurjectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFinitePartialFourierBijectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdelicProductOperatorStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.MixXChar GlobalTheory.DblEval
open GlobalTheory.Doubling (absE)

open scoped Classical
attribute [local instance] GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele
  GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField
  GlobalTheory.DiagForm.measAf GlobalTheory.DiagForm.borelAf

noncomputable section
namespace GlobalTheory.DiagUniq

variable {F : Type} [Field F] [NumberField F]

def piI : AF F →+* mixedEmbedding.mixedSpace F :=
  (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom.comp
    (RingHom.fst (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))

def piF : AF F →+* FiniteAdeleRing (𝓞 F) F := RingHom.snd (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)

def mk (a : mixedEmbedding.mixedSpace F) (b : FiniteAdeleRing (𝓞 F) F) : AF F :=
  (((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm a, b) : InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F)

theorem piI_mk (a : mixedEmbedding.mixedSpace F) (b : FiniteAdeleRing (𝓞 F) F) : piI (mk a b) = a :=
  (InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply a

theorem piF_mk (a : mixedEmbedding.mixedSpace F) (b : FiniteAdeleRing (𝓞 F) F) : piF (mk a b) = b := rfl

theorem pureA_apply {ι : Type} (f : (ι → mixedEmbedding.mixedSpace F) → ℂ) (g : (ι → FiniteAdeleRing (𝓞 F) F) → ℂ)
    (u : ι → AF F) : pureA F f g u = f (piI ∘ u) * g (piF ∘ u) := rfl

theorem psi_split {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (a : AF F) :
    ψ a = Complex.exp (-(2 * Real.pi * Complex.I) *
      ((Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (piI a) : ℝ) : ℂ)) *
      ψ (((0, piF a) : InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F) : AF F) := by
  set p : AF F := (((a.1, 0) : InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F) : AF F) with hp
  set q : AF F := (((0, a.2) : InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F) : AF F) with hq
  have e : p + q = a := by
    refine Prod.ext ?_ ?_
    · show a.1 + 0 = a.1; rw [add_zero]
    · show 0 + a.2 = a.2; rw [zero_add]
  conv_lhs => rw [← e, AddChar.map_add_eq_mul]
  congr 1
  refine (hψ.2.2 p fun u hu => ?_)
  have h1 : u.1 = 0 := (RingEquiv.map_eq_zero_iff _).1 hu
  refine Prod.ext ?_ ?_
  · show u.1 * a.1 = 0; rw [h1, zero_mul]
  · show u.2 * 0 = 0; rw [mul_zero]

theorem schr_add {ι : Type} [Fintype ι] (ψ : AddChar (AF F) ℂ) (w : (ι → AF F) × (ι → AF F))
    (φ φ' : (ι → AF F) → ℂ) : schr ψ w (φ + φ') = schr ψ w φ + schr ψ w φ' := by
  funext u; simp only [schr, Pi.add_apply, mul_add]

theorem schr_smul {ι : Type} [Fintype ι] (ψ : AddChar (AF F) ℂ) (w : (ι → AF F) × (ι → AF F)) (c : ℂ)
    (φ : (ι → AF F) → ℂ) : schr ψ w (c • φ) = c • schr ψ w φ := by
  funext u; simp only [schr, Pi.smul_apply, smul_eq_mul]; ring

end GlobalTheory.DiagUniq
end

open GlobalTheory.DiagUniq in

theorem GlobalTheory.DiagUniq.eq_smul_lDiag : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ →
    ∀ (κ : Type) [Fintype κ] (l : ((κ ⊕ κ → AF F) → ℂ) →ₗ[ℂ] ℂ), l ∈ (adeleClass F).adm (κ ⊕ κ) →
      (∀ x y : κ → AF F, ∀ Φ ∈ schA F (κ ⊕ κ), l (schr ψ (Sum.elim x x, Sum.elim y (-y)) Φ) = l Φ) →
      ∃ c : ℂ, ∀ Φ ∈ schA F (κ ⊕ κ), l Φ = c * GlobalTheory.DiagForm.lDiag F κ Φ := by
  intro F _ _ ψ hψ κ _ l hl hinv
  obtain ⟨A, hAs, hAi, C₁, hC₁, hAe⟩ := GlobalTheory.T.archimedean_partial_fourier_surjective F κ
  obtain ⟨B, hBs, hBo, hBi, C₂, hC₂, hBe⟩ := GlobalTheory.T.exists_finite_partial_fourier_bijective F ψ hψ κ
  obtain ⟨H, hH⟩ := GlobalTheory.T.exists_adelic_product_operator F (κ ⊕ κ) A.toLinearMap B
  have hH' : ∀ (f : SchwartzMap (κ ⊕ κ → mixedEmbedding.mixedSpace F) ℂ) (g : (κ ⊕ κ → FiniteAdeleRing (𝓞 F) F) → ℂ), H (pureA F f g) = pureA F (A f) (B g) := hH
  have hHs : ∀ Ψ ∈ schA F (κ ⊕ κ), H Ψ ∈ schA F (κ ⊕ κ) := by
    intro Ψ hΨ
    induction hΨ using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨f, g, hg, rfl⟩ := hx
      rw [hH']
      exact Submodule.subset_span ⟨A f, B g, hBs g hg, rfl⟩
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
    | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx
  have hHo : ∀ Φ ∈ schA F (κ ⊕ κ), ∃ Ψ ∈ schA F (κ ⊕ κ), H Ψ = Φ := by
    intro Φ hΦ
    induction hΦ using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨f, g, hg, rfl⟩ := hx
      obtain ⟨f', rfl⟩ := hAs f
      obtain ⟨g', hg', rfl⟩ := hBo g hg
      exact ⟨pureA F f' g', Submodule.subset_span ⟨f', g', hg', rfl⟩, hH' f' g'⟩
    | zero => exact ⟨0, Submodule.zero_mem _, map_zero H⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, ha, rfl⟩ := hx
      obtain ⟨b, hb, rfl⟩ := hy
      exact ⟨a + b, Submodule.add_mem _ ha hb, map_add H a b⟩
    | smul c x _ hx =>
      obtain ⟨a, ha, rfl⟩ := hx
      exact ⟨c • a, Submodule.smul_mem _ c ha, map_smul H c a⟩
  have hHe : ∀ Ψ ∈ schA F (κ ⊕ κ), GlobalTheory.DiagForm.lDiag F κ (H Ψ) = (C₂ * C₁) * Ψ 0 := by
    intro Ψ hΨ
    induction hΨ using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨f, g, hg, rfl⟩ := hx
      rw [hH', GlobalTheory.DiagForm.lDiag_pureA _ (hBs g hg), hBe g hg, hAe f, pureA_apply]
      have e1 : (piI ∘ (0 : κ ⊕ κ → AF F)) = 0 := funext fun _ => map_zero _
      have e2 : (piF ∘ (0 : κ ⊕ κ → AF F)) = 0 := funext fun _ => map_zero _
      rw [e1, e2]; ring
    | zero => rw [map_zero, map_zero]; simp
    | add x y _ _ hx hy => rw [map_add, map_add, hx, hy, Pi.add_apply]; ring
    | smul c x _ hx => rw [map_smul, map_smul, hx, Pi.smul_apply, smul_eq_mul, smul_eq_mul]; ring
  have hHi : ∀ z : κ ⊕ κ → AF F, ∃ x y : κ → AF F, ∀ Ψ ∈ schA F (κ ⊕ κ),
      H (fun u => ψ (u ⬝ᵥ z) * Ψ u) = schr ψ (Sum.elim x x, Sum.elim y (-y)) (H Ψ) := by
    intro z
    obtain ⟨x₀, y₀, hA⟩ := hAi (piI ∘ z)
    obtain ⟨x₁, y₁, hB⟩ := hBi (piF ∘ z)
    set x : κ → AF F := fun i => mk (x₀ i) (x₁ i) with hx
    set y : κ → AF F := fun i => mk (y₀ i) (y₁ i) with hy
    refine ⟨x, y, fun Ψ hΨ => ?_⟩
    induction hΨ using Submodule.span_induction with
    | mem Φ hΦ =>
      obtain ⟨f, g, hg, rfl⟩ := hΦ
      obtain ⟨f₁, hf₁, hAf₁⟩ := hA f
      have e1 : (fun u => ψ (u ⬝ᵥ z) * pureA F f g u) = pureA F f₁
          (fun u' => ψ (((0, u' ⬝ᵥ piF ∘ z) : InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F) : AF F) * g u') := by
        funext u
        rw [pureA_apply, pureA_apply, psi_split hψ, hf₁, piI.map_dotProduct, piF.map_dotProduct]
        ring
      rw [e1, hH', hH', hB g hg]
      funext u
      have hx1 : piI ∘ (u + Sum.elim x x) = piI ∘ u + Sum.elim x₀ x₀ := funext fun i => by
        cases i <;> simp [hx, map_add, piI_mk]
      have hx2 : piF ∘ (u + Sum.elim x x) = piF ∘ u + Sum.elim x₁ x₁ := funext fun i => by
        cases i <;> simp [hx, map_add, piF_mk]
      have hy1 : piI ∘ Sum.elim y (-y) = Sum.elim y₀ (-y₀) := funext fun i => by
        cases i <;> simp [hy, map_neg, piI_mk]
      have hy2 : piF ∘ Sum.elim y (-y) = Sum.elim y₁ (-y₁) := funext fun i => by
        cases i <;> simp [hy, map_neg, piF_mk]
      rw [show schr ψ (Sum.elim x x, Sum.elim y (-y)) (pureA F (A f) (B g)) u =
          ψ (u ⬝ᵥ Sum.elim y (-y) + ⅟(2 : AF F) * (Sum.elim x x ⬝ᵥ Sum.elim y (-y))) *
            pureA F (A f) (B g) (u + Sum.elim x x) from rfl]
      rw [GlobalTheory.DiagForm.dot_anti, mul_zero, add_zero, psi_split hψ, pureA_apply, pureA_apply, hAf₁,
        piI.map_dotProduct, piF.map_dotProduct, hx1, hx2, hy1, hy2]
      ring
    | zero =>
      have e0 : (fun u => ψ (u ⬝ᵥ z) * (0 : (κ ⊕ κ → AF F) → ℂ) u) = 0 := funext fun u => mul_zero _
      rw [e0, map_zero]
      funext u
      simp [schr]
    | add a b _ _ ha hb =>
      have e0 : (fun u => ψ (u ⬝ᵥ z) * (a + b) u) = (fun u => ψ (u ⬝ᵥ z) * a u) + (fun u => ψ (u ⬝ᵥ z) * b u) :=
        funext fun u => mul_add _ _ _
      rw [e0, map_add, map_add, ha, hb, schr_add]
    | smul c a _ ha =>
      have e0 : (fun u => ψ (u ⬝ᵥ z) * (c • a) u) = c • (fun u => ψ (u ⬝ᵥ z) * a u) := by
        funext u; simp only [Pi.smul_apply, smul_eq_mul]; ring
      rw [e0, map_smul, map_smul, ha, schr_smul]
  set l' : ((κ ⊕ κ → AF F) → ℂ) →ₗ[ℂ] ℂ := l ∘ₗ H with hl'def
  have hl' : l' ∈ (adeleClass F).adm (κ ⊕ κ) := by
    intro g hg
    obtain ⟨T, hT⟩ := hl (B g) (hBs g hg)
    refine ⟨T.comp A, fun f => ?_⟩
    rw [hl'def, LinearMap.comp_apply, hH', hT]
    rfl
  have hinv' : ∀ z : κ ⊕ κ → AF F, ∀ Ψ ∈ schA F (κ ⊕ κ), l' (fun u => ψ (u ⬝ᵥ z) * Ψ u) = l' Ψ := by
    intro z Ψ hΨ
    obtain ⟨x, y, h⟩ := hHi z
    rw [hl'def, LinearMap.comp_apply, LinearMap.comp_apply, h Ψ hΨ, hinv x y _ (hHs Ψ hΨ)]
  obtain ⟨c, hc⟩ := GlobalTheory.T.character_invariant_adelic_form_eq_mul_eval_zero F ψ hψ (κ ⊕ κ) l' hl' hinv'
  refine ⟨c / (C₂ * C₁), fun Φ hΦ => ?_⟩
  obtain ⟨Ψ, hΨ, rfl⟩ := hHo Φ hΦ
  rw [hHe Ψ hΨ]
  have := hc Ψ hΨ
  rw [hl'def, LinearMap.comp_apply] at this
  rw [this]
  field_simp
