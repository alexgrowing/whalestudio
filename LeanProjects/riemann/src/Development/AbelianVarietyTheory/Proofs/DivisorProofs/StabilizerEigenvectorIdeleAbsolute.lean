import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocPart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelativelyCompactStabilizer
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.LemF
open GlobalTheory.Doubling (absE)

noncomputable section
namespace GlobalTheory.ThK.CartanUnit

variable {n : ℕ}

theorem star_mulVec_map (A : Matrix (Fin n) (Fin n) ℂ) (x : Fin n → ℂ) : star (A *ᵥ x) = A.map star *ᵥ star x := by
  funext i
  simp [Matrix.mulVec, dotProduct, star_sum]

theorem mulVec_dot (A : Matrix (Fin n) (Fin n) ℂ) (u v : Fin n → ℂ) : (A *ᵥ u) ⬝ᵥ v = u ⬝ᵥ (Aᵀ *ᵥ v) := by
  rw [dotProduct_comm, Matrix.dotProduct_mulVec, Matrix.mulVec_transpose, dotProduct_comm]

theorem mul_star_eq_one_of_cartan {M θ k : Matrix (Fin n) (Fin n) ℂ} (hC : IsCartan M θ) (hk : kᵀ * M * k.map star = M)
    (hc : Commute k θ) {x : Fin n → ℂ} (hx : x ≠ 0) {c : ℂ} (hkx : k *ᵥ x = c • x) : c * star c = 1 := by
  have hpos := hC.2.2 x hx
  have hP : (θ *ᵥ x) ⬝ᵥ M *ᵥ star x ≠ 0 := fun h => by rw [h] at hpos; simp at hpos
  have h1 : (θ *ᵥ (k *ᵥ x)) ⬝ᵥ M *ᵥ star (k *ᵥ x) = (θ *ᵥ x) ⬝ᵥ M *ᵥ star x := by
    rw [Matrix.mulVec_mulVec, ← hc.eq, ← Matrix.mulVec_mulVec, star_mulVec_map, mulVec_dot, Matrix.mulVec_mulVec,
      Matrix.mulVec_mulVec, hk]
  have h2 : (θ *ᵥ (k *ᵥ x)) ⬝ᵥ M *ᵥ star (k *ᵥ x) = c * star c * ((θ *ᵥ x) ⬝ᵥ M *ᵥ star x) := by
    rw [hkx, Matrix.mulVec_smul, star_smul, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul,
      smul_eq_mul]
    ring
  have h3 : (c * star c - 1) * ((θ *ᵥ x) ⬝ᵥ M *ᵥ star x) = 0 := by rw [sub_mul, ← h2, h1, one_mul, sub_self]
  exact sub_eq_zero.1 ((mul_eq_zero.1 h3).resolve_right hP)

end GlobalTheory.ThK.CartanUnit

namespace GlobalTheory.ThK

theorem absE_eq_one_of_KInf_eigen : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ)
    (G : Geo σ (b + 2) a') (G₁ : Geo σ b a') (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' →
    B.IsGood σ → G.IsGood B → ∀ (K : Subgroup (UA σ G.V.J)), IsStab B K →
    ∀ k ∈ KAt K (evI F), ∀ t ∈ idelesAt E (evI F), mat k *ᵥ incV F H.x = t.1 • incV F H.x → absE F E t = 1 := by
  intro F E _ _ _ _ _ σ B b a' G G₁ H H' hC hB hG K hK k hk t ht hkt
  have hcm := hB.cm
  have hkI := (mem_KAt_inf hK).1 hk
  have hx0 : H.x ≠ 0 := fun h => by
    have := hC.hH.xy
    simp [form, h] at this
  have hw : ∀ w, ‖piInf (B.emb w) t.1‖₊ = 1 := by
    intro w
    have hinc : ∀ e : E, piInf (B.emb w) (inclR (F := F) (AF F) e) = (B.emb w).1 e := fun e => by
      simp [piInf, inclR, compInf, infEmb_tmul]
    have hu : ((mat k).map (piInf (B.emb w)))ᵀ * G.V.J.map (B.emb w).1 * ((mat k).map (piInf (B.emb w))).map star =
        G.V.J.map (B.emb w).1 := by
      have h0 : (mat k)ᵀ * incM F G.V.J * (mat k).map (cA σ) = incM F G.V.J := k.2
      have h1 := congrArg (fun A => A.map (piInf (B.emb w))) h0
      simp only [Matrix.map_mul, Matrix.transpose_map, Matrix.map_map] at h1
      have e1 : (incM F G.V.J).map (piInf (B.emb w)) = G.V.J.map (B.emb w).1 := by
        ext i j; exact hinc _
      have e2 : (piInf (B.emb w)) ∘ (cA σ) = star ∘ (piInf (B.emb w)) := funext fun z => GlobalTheory.StabBounded.cA_piInf hcm _ z
      rw [e1, e2] at h1
      simpa [Matrix.map_map] using h1
    have he : (mat k).map (piInf (B.emb w)) *ᵥ (fun i => (B.emb w).1 (H.x i)) =
        piInf (B.emb w) t.1 • (fun i => (B.emb w).1 (H.x i)) := by
      funext i
      have h1 := congrArg (fun v => piInf (B.emb w) (v i)) hkt
      simp only [Pi.smul_apply, smul_eq_mul, map_mul, RingHom.map_mulVec] at h1
      have e3 : (piInf (B.emb w)) ∘ incV F H.x = fun i => (B.emb w).1 (H.x i) := funext fun j => hinc _
      rw [e3] at h1
      simpa [incV, hinc] using h1
    have hxw : (fun i => (B.emb w).1 (H.x i)) ≠ 0 := fun h =>
      hx0 (funext fun i => (B.emb w).1.injective (by simpa using congrFun h i))
    have hcs := CartanUnit.mul_star_eq_one_of_cartan (hG.hV.cartan w) hu (hkI.2 w) hxw he
    have hn : ‖piInf (B.emb w) t.1‖ ^ 2 = 1 := by
      have := Complex.mul_conj' (piInf (B.emb w) t.1)
      rw [show (starRingEnd ℂ) (piInf (B.emb w) t.1) = star (piInf (B.emb w) t.1) from rfl, hcs] at this
      exact_mod_cast this.symm
    have hn' : ‖piInf (B.emb w) t.1‖ = 1 := (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 hn
    exact NNReal.eq (by simpa using hn')
  rw [GlobalTheory.Doubling.absE_apply]
  have hf : ∀ v, GlobalTheory.Doubling.unitFin F E v t = 1 := fun v => Units.ext (by
    have := (at_evI_iff.1 (mem_idelesAt.1 ht)) v
    rw [map_sub, map_one, sub_eq_zero] at this
    exact this)
  simp only [hf, map_one, finprod_one, mul_one]
  refine Finset.prod_eq_one fun w _ => ?_
  rw [GlobalTheory.Doubling.absEw_eq_sq hcm (B.emb w)]
  change ‖piInf (B.emb w) t.1‖₊ ^ 2 = 1
  rw [hw w, one_pow]

end GlobalTheory.ThK
