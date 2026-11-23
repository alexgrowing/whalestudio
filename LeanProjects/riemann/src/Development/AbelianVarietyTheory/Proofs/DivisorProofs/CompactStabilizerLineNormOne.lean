import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConeFinIntEq

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.ConeNZ

theorem absE_eq_one_of_eigen : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ)
    (X : Spc F E n) (x₀ : Fin n → E) (K : Subgroup (UA σ X.J)), IsCompact (K : Set (UA σ X.J)) → x₀ ≠ 0 →
    ∀ (v : Pl F) (k : UA σ X.J), k ∈ KAt K (evFin F v) → ∀ l : (AE F E)ˣ,
      mat k *ᵥ incV F x₀ = (l : AE F E) • incV F x₀ → absE F E l = 1 := by
  intro F E _ _ _ _ _ σ n X x₀ K hK hx v k hk l hkl
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  haveI : IsTopologicalRing (AE F E) := GlobalTheory.Doubling.isTopologicalRing_tens
  haveI : T2Space (AE F E) := GlobalTheory.Doubling.t2Space_tensorProduct_finiteExtension
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hx
  set x := incV F x₀ with hxdef
  let cu : (AE F E)ˣ := Units.map (inclR (F := F) (AF F)).toMonoidHom (Units.mk0 (x₀ i) hi)
  have hcu : (cu : AE F E) = x i := rfl
  let f : UA σ X.J → AE F E := fun g => (mat g *ᵥ x) i * ((cu⁻¹ : (AE F E)ˣ) : AE F E)
  have hm : Continuous fun g : UA σ X.J => mat g := Units.continuous_val.comp continuous_subtype_val
  have hf : Continuous f :=
    ((continuous_apply i).comp (hm.matrix_mulVec continuous_const)).mul continuous_const
  have hval : ∀ g (t : AE F E), mat g *ᵥ x = t • x → f g = t := fun g t h => by
    simp only [f, h, Pi.smul_apply, smul_eq_mul, ← hcu, Units.mul_inv_cancel_right]
  have hinv : ∀ (g : UA σ X.J) (t : (AE F E)ˣ), mat g *ᵥ x = (t : AE F E) • x →
      mat g⁻¹ *ᵥ x = ((t⁻¹ : (AE F E)ˣ) : AE F E) • x := fun g t h => by
    have e1 : mat g⁻¹ * mat g = 1 := by simpa using GlobalTheory.StabHaar.mat_mul_inv g⁻¹
    have e2 : (t : AE F E) • (mat g⁻¹ *ᵥ x) = x := by
      rw [← Matrix.mulVec_smul, ← h, Matrix.mulVec_mulVec, e1, Matrix.one_mulVec]
    calc mat g⁻¹ *ᵥ x = ((t⁻¹ : (AE F E)ˣ) : AE F E) • ((t : AE F E) • (mat g⁻¹ *ᵥ x)) := by
          rw [smul_smul, Units.inv_mul, one_smul]
      _ = _ := by rw [e2]
  have hpow : ∀ (g : UA σ X.J) (t : AE F E), mat g *ᵥ x = t • x → ∀ m : ℕ, mat (g ^ m) *ᵥ x = (t ^ m) • x := by
    intro g t h m
    induction m with
    | zero => simp [GlobalTheory.StabHaar.mat_one]
    | succ m ih =>
      rw [pow_succ, GlobalTheory.StabHaar.mat_mul, ← Matrix.mulVec_mulVec, h, Matrix.mulVec_smul, ih, smul_smul, pow_succ,
        mul_comm]
  let φ : UA σ X.J → AE F E × (AE F E)ᵐᵒᵖ := fun g => (f g, MulOpposite.op (f g⁻¹))
  have hφ : Continuous φ := hf.prodMk (MulOpposite.continuous_op.comp (hf.comp continuous_inv))
  have hC : IsCompact (Units.embedProduct (AE F E) ⁻¹' (φ '' (K : Set (UA σ X.J)))) :=
    Units.isClosedEmbedding_embedProduct.isCompact_preimage (hK.image hφ)
  obtain ⟨Cb, hCb⟩ := (hC.image GlobalTheory.Doubling.continuous_absE).bddAbove
  have key : ∀ g ∈ K, ∀ t : (AE F E)ˣ, mat g *ᵥ x = (t : AE F E) • x → absE F E t ≤ 1 := by
    intro g hg t h
    by_contra hlt
    obtain ⟨m, hmC⟩ := pow_unbounded_of_one_lt Cb (not_le.1 hlt)
    have h1 : mat (g ^ m) *ᵥ x = ((t ^ m : (AE F E)ˣ) : AE F E) • x := by rw [Units.val_pow_eq_pow_val]; exact hpow g _ h m
    have h2 := hinv _ _ h1
    have hmem : t ^ m ∈ Units.embedProduct (AE F E) ⁻¹' (φ '' (K : Set (UA σ X.J))) :=
      ⟨g ^ m, pow_mem hg m, Prod.ext (hval _ _ h1) (congrArg MulOpposite.op (hval _ _ h2))⟩
    exact not_le.2 hmC (by rw [← map_pow]; exact hCb ⟨_, hmem, rfl⟩)
  have hk' : k ∈ K := hk.1
  refine le_antisymm (key k hk' l hkl) ?_
  have h1 := key _ (inv_mem hk') _ (hinv k l hkl)
  calc (1 : ℝ≥0) = absE F E l * absE F E l⁻¹ := by rw [← map_mul, mul_inv_cancel, map_one]
    _ ≤ absE F E l * 1 := by gcongr
    _ = _ := mul_one _

end GlobalTheory.ConeNZ

end
