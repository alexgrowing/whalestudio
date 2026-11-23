import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompReixMemAdm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpanFiniteDimensional
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaStabilizerExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealScalarArchimedeanAdeleSmulMatrixRealPlace
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling GlobalTheory.ThK.Bot GlobalTheory.DblBox

namespace GlobalTheory.KFinStab

open GlobalTheory.ThK.ConeEuler GlobalTheory.ThK.UnifLevel GlobalTheory.DefiniteLevel

theorem map_piInf_compArch {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (g : UA σ J) {w : InfinitePlace F} (τ : EmbOver E w) :
    (mat (compArch σ J g)).map (piInf τ) = (mat g).map (piInf τ) := by
  rw [mat_compArch]
  ext i j
  simp only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, map_add]
  rw [eInf, GlobalTheory.RealScalar.piInf_realAd_smul, sub_smul, one_smul, map_sub, GlobalTheory.RealScalar.piInf_realAd_smul]
  simp

theorem span_finiteDimensional : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E), B.IsGood σ → ∀ (n r s : ℕ) (X : Spc F E n), X.IsHerm σ B r s →
    ∀ K : Subgroup (UA σ X.J), IsStab B K →
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : UA σ X.J →* Module.End ℂ V) (x : V) (S : Submodule ℂ V), FiniteDimensional ℂ S →
    (∀ k ∈ KInf σ X B.emb, ρ k x ∈ S) → ∀ U : Subgroup (UA σ X.J), IsOpen (U : Set (UA σ X.J)) →
    (∀ k ∈ U, (mat k).map (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)) = 1 → ρ k x = x) →
    FiniteDimensional ℂ (Submodule.span ℂ {y | ∃ k ∈ K, y = ρ k x}) := by
  intro hKP F E _ _ _ _ _ σ B hB n r s X hX K hKst V _ _ ρ x S hS hK U hU hfix
  haveI : IsTopologicalGroup (UA σ X.J) := inferInstance
  obtain ⟨K', μK, μ, hK'st, hK'c, -, -⟩ := GlobalTheory.StabHaar.stabEx hKP.base F E σ B n X r s hB hX
  have hKK : K = K' := by
    ext g
    rw [hKst g, hK'st g]
  have hKc : IsCompact (K : Set (UA σ X.J)) := hKK ▸ hK'c
  have hU' : IsOpen ((U.comap (finPart (σ := σ) X.J) : Subgroup (UA σ X.J)) : Set (UA σ X.J)) :=
    hU.preimage (continuous_idemU _ _ _)
  obtain ⟨t, ht⟩ := hKc.elim_finite_subcover
    (fun k : K => (fun g => (k.1)⁻¹ * g) ⁻¹' ((U.comap (finPart (σ := σ) X.J) : Subgroup (UA σ X.J)) : Set (UA σ X.J)))
    (fun k => hU'.preimage (continuous_const.mul continuous_id))
    (fun g hg => Set.mem_iUnion.2 ⟨⟨g, hg⟩, by
      show (g⁻¹ * g) ∈ U.comap (finPart (σ := σ) X.J)
      rw [inv_mul_cancel]; exact Subgroup.one_mem _⟩)
  have key : ∀ u ∈ K, u ∈ U.comap (finPart (σ := σ) X.J) → ρ u x ∈ S := by
    intro u huK huU
    have h1 : ρ (finPart X.J u) x = x := hfix _ huU (finPart_inf _ _)
    have h2 : compArch σ X.J u ∈ KInf σ X B.emb := by
      refine ⟨compArch_mem u, fun w => ?_⟩
      rw [map_piInf_compArch]
      exact ((hKst u).1 huK).1 w
    have h3 : ρ u x = ρ (compArch σ X.J u) x := by
      conv_lhs => rw [← compArch_mul_finPart X.J u]
      rw [map_mul, Module.End.mul_apply, h1]
    rw [h3]
    exact hK _ h2
  have hle : Submodule.span ℂ {y | ∃ k ∈ K, y = ρ k x} ≤ t.sup (fun k : K => S.map (ρ k.1)) := by
    rw [Submodule.span_le]
    rintro _ ⟨g, hg, rfl⟩
    obtain ⟨k, hkt, hk⟩ := Set.mem_iUnion₂.1 (ht hg)
    have hu : (k.1)⁻¹ * g ∈ K := K.mul_mem (K.inv_mem k.2) hg
    have hm := key _ hu hk
    have e : ρ g x = ρ k.1 (ρ ((k.1)⁻¹ * g) x) := by
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]
    rw [SetLike.mem_coe, e]
    exact Finset.le_sup (f := fun k : K => S.map (ρ k.1)) hkt (Submodule.mem_map_of_mem hm)
  haveI : ∀ k : K, FiniteDimensional ℂ (S.map (ρ k.1)) := fun k => inferInstance
  haveI : FiniteDimensional ℂ ↥(t.sup (fun k : K => S.map (ρ k.1)) : Submodule ℂ V) := inferInstance
  exact Submodule.finiteDimensional_of_le hle

end GlobalTheory.KFinStab
