import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StabilizerEigenvectorIdeleAbsolute
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.LemF
open GlobalTheory.Doubling (absE)

noncomputable section
namespace GlobalTheory.ThK.LeviChar

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem at_eigen {d : ℕ} {W : Spc F E d} {k : UA σ W.J} (hk : k ∈ UAt σ W (evI F)) {x : Fin d → E} (hx : x ≠ 0)
    {t : AE F E} (hkt : mat k *ᵥ incV F x = t • incV F x) : At (evI F) (t - 1) := by
  intro u hu
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hx
  have h0 : u • (mat k - 1) = 0 := hk u hu
  have h1 : (u • (mat k - 1)) *ᵥ incV F x = u • ((t - 1) • incV F x) := by
    rw [Matrix.smul_mulVec, Matrix.sub_mulVec, hkt, Matrix.one_mulVec, sub_smul, one_smul]
  rw [h0, Matrix.zero_mulVec] at h1
  have h2 : (u • (t - 1)) * inclR (F := F) (AF F) (x i) = 0 := by
    have := congrFun h1 i
    simp only [Pi.zero_apply, Pi.smul_apply, incV, smul_eq_mul] at this
    rw [smul_mul_assoc]; exact this.symm
  have hi' : x i ≠ 0 := hi
  have h3 := congrArg (· * inclR (F := F) (AF F) (x i)⁻¹) h2
  simpa [mul_assoc, ← map_mul, mul_inv_cancel₀ hi', -map_inv₀] using h3

theorem norm_eigen (hcm : IsCMExt F E σ) {B : Base F E} {d r s : ℕ} {W : Spc F E d} (hW : W.IsSkew σ B r s)
    {k : UA σ W.J} (hk : k ∈ KInf σ W B.emb) {x : Fin d → E} (hx0 : x ≠ 0)
    {t : AE F E} (hkt : mat k *ᵥ incV F x = t • incV F x) (w : InfinitePlace F) : ‖piInf (B.emb w) t‖ = 1 := by
  have hinc : ∀ e : E, piInf (B.emb w) (inclR (F := F) (AF F) e) = (B.emb w).1 e := fun e => by
    simp [piInf, inclR, compInf, infEmb_tmul]
  have hu : ((mat k).map (piInf (B.emb w)))ᵀ * W.J.map (B.emb w).1 * ((mat k).map (piInf (B.emb w))).map star =
      W.J.map (B.emb w).1 := by
    have h0 : (mat k)ᵀ * incM F W.J * (mat k).map (cA σ) = incM F W.J := k.2
    have h1 := congrArg (fun A => A.map (piInf (B.emb w))) h0
    simp only [Matrix.map_mul, Matrix.transpose_map, Matrix.map_map] at h1
    have e1 : (incM F W.J).map (piInf (B.emb w)) = W.J.map (B.emb w).1 := by
      ext i j; exact hinc _
    have e2 : (piInf (B.emb w)) ∘ (cA σ) = star ∘ (piInf (B.emb w)) := funext fun z => GlobalTheory.StabBounded.cA_piInf hcm _ z
    rw [e1, e2] at h1
    simpa [Matrix.map_map] using h1
  have hu' : ((mat k).map (piInf (B.emb w)))ᵀ * (Complex.I • W.J.map (B.emb w).1) *
      ((mat k).map (piInf (B.emb w))).map star = Complex.I • W.J.map (B.emb w).1 := by
    rw [Matrix.mul_smul, Matrix.smul_mul, hu]
  have he : (mat k).map (piInf (B.emb w)) *ᵥ (fun i => (B.emb w).1 (x i)) =
      piInf (B.emb w) t • (fun i => (B.emb w).1 (x i)) := by
    funext i
    have h1 := congrArg (fun v => piInf (B.emb w) (v i)) hkt
    simp only [Pi.smul_apply, smul_eq_mul, map_mul, RingHom.map_mulVec] at h1
    have e3 : (piInf (B.emb w)) ∘ incV F x = fun i => (B.emb w).1 (x i) := funext fun j => hinc _
    rw [e3] at h1
    simpa [incV, hinc] using h1
  have hxw : (fun i => (B.emb w).1 (x i)) ≠ 0 := fun h =>
    hx0 (funext fun i => (B.emb w).1.injective (by simpa using congrFun h i))
  have hcs := CartanUnit.mul_star_eq_one_of_cartan (hW.cartan w) hu' (hk.2 w) hxw he
  have hn : ‖piInf (B.emb w) t‖ ^ 2 = 1 := by
    have := Complex.mul_conj' (piInf (B.emb w) t)
    rw [show (starRingEnd ℂ) (piInf (B.emb w) t) = star (piInf (B.emb w) t) from rfl, hcs] at this
    exact_mod_cast this.symm
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 hn

theorem char_levi_KInf : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (d d₁ r s i₀ i₁ : ℕ) (W : Spc F E d) (W₁ : Spc F E d₁) (H' : Plane E d d₁), IsCMExt F E σ →
    W.IsSkew σ B r s → H'.IsAdapted σ B W W₁ i₀ i₁ → ∀ (χ : Chr F E) (m : InfinitePlace F → ℤ), HasExp B.emb χ m →
    ∀ (z : ℝ) (t : (AE F E)ˣ) (h₁ : UA σ W₁.J) (k : UA σ W.J), k ∈ KInf σ W B.emb → IsLevi H' t h₁ k →
      (χ t : ℂ) * (((absE F E t : ℝ) ^ z : ℝ) : ℂ) = ∏ w, piInf (B.emb w) t.1 ^ m w := by
  intro F E _ _ _ _ _ σ B d d₁ r s i₀ i₁ W W₁ H' hcm hW hA χ m hχ z t h₁ k hk hL
  have hx0 : H'.x ≠ 0 := fun h => by
    have := hA.xy
    simp [form, h] at this
  have ht : At (evI F) (t.1 - 1) := at_eigen hk.1 hx0 hL.1
  have hw : ∀ w, ‖piInf (B.emb w) t.1‖ = 1 := norm_eigen hcm hW hk hx0 hL.1
  have habs : absE F E t = 1 := by
    rw [GlobalTheory.Doubling.absE_apply]
    have hf : ∀ v, GlobalTheory.Doubling.unitFin F E v t = 1 := fun v => Units.ext (by
      have := (at_evI_iff.1 ht) v
      rw [map_sub, map_one, sub_eq_zero] at this
      exact this)
    simp only [hf, map_one, finprod_one, mul_one]
    refine Finset.prod_eq_one fun w _ => ?_
    rw [GlobalTheory.Doubling.absEw_eq_sq hcm (B.emb w)]
    change ‖piInf (B.emb w) t.1‖₊ ^ 2 = 1
    rw [show ‖piInf (B.emb w) t.1‖₊ = 1 from NNReal.eq (by simpa using hw w), one_pow]
  rw [habs, hχ t ht]
  simp [hw]

end GlobalTheory.ThK.LeviChar
