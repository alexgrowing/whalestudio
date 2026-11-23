import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigAStabilizerThetaGlobal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigATripleMatchedCompare

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open scoped Classical

noncomputable section

namespace GlobalTheory.ConeTateDecay

open GlobalTheory.XTermDecay

variable {F : Type} [Field F] [NumberField F]

theorem norm_evI_le {ι : Type} [Fintype ι] (x : ι → AF F) :
    ‖fun i => evI F (x i)‖ ≤ ∑ i, ∑ v : InfinitePlace F, ‖(x i).1 v‖ := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
  exact (norm_qA_le (x i)).trans (Finset.single_le_sum (f := fun i => ∑ v : InfinitePlace F, ‖(x i).1 v‖)
    (fun _ _ => by positivity) (Finset.mem_univ i))

theorem value_decay {κ κ₁ ι : Type} [Fintype κ] [Fintype κ₁] [Fintype ι] (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ)
    (S U : ι → (κ → AF F) × (κ → AF F)) (hSU : ∀ i j, (S j).1 ⬝ᵥ (U i).2 - (U i).1 ⬝ᵥ (S j).2 = if i = j then 1 else 0)
    (e : ((κ → AF F) → ℂ) →ₗ[ℂ] (κ₁ → mixedEmbedding.mixedSpace F) → ℂ)
    (hsl : ∀ g ∈ SB (κ → Af F), ∃ L : SInf F κ →L[ℂ] SInf F κ₁, ∀ f, ⇑(L f) = e (pureA F f g))
    (hinv : ∀ i (a : AF F), ∀ Φ ∈ schA F κ, e (schr ψ (a • U i) Φ) = e Φ)
    {Ω : Set (ι → Af F)} (hΩ : IsCompact Ω) (y : κ₁ → mixedEmbedding.mixedSpace F) (N : ℕ) :
    ∀ Φ ∈ schA F κ, ∃ C : ℝ, ∀ x : ι → AF F, (fun i => (x i).2) ∈ Ω →
      ‖e (schr ψ (∑ i, x i • S i) Φ) y‖ * (1 + ‖fun i => evI F (x i)‖) ^ N ≤ C := by
  intro Φ hΦ
  induction hΦ using Submodule.span_induction with
  | zero =>
    refine ⟨0, fun x _ => ?_⟩
    change ‖e (schrL ψ _ 0) y‖ * _ ≤ 0
    simp
  | add a b _ _ ha hb =>
    obtain ⟨C, hC⟩ := ha
    obtain ⟨D, hD⟩ := hb
    refine ⟨C + D, fun x hx => le_trans ?_ (add_le_add (hC x hx) (hD x hx))⟩
    change ‖e (schrL ψ _ (a + b)) y‖ * _ ≤ ‖e (schrL ψ _ a) y‖ * _ + ‖e (schrL ψ _ b) y‖ * _
    rw [map_add, map_add, ← add_mul]
    gcongr
    exact norm_add_le _ _
  | smul c a _ ha =>
    obtain ⟨C, hC⟩ := ha
    refine ⟨‖c‖ * C, fun x hx => le_trans ?_ (mul_le_mul_of_nonneg_left (hC x hx) (norm_nonneg c))⟩
    change ‖e (schrL ψ _ (c • a)) y‖ * _ ≤ ‖c‖ * (‖e (schrL ψ _ a) y‖ * _)
    rw [map_smul, map_smul, Pi.smul_apply, norm_smul, mul_assoc]
  | mem Φ h =>
    obtain ⟨f, g, hg, rfl⟩ := h
    obtain ⟨C, hC⟩ := slice_decay (T := Unit) ψ hψ S U hSU e hsl hinv hg (fun _ => f) (fun p _ => ⟨p f, fun _ => le_rfl⟩) hΩ
      (SchwartzMap.seminorm ℂ 0 0) ((schwartz_withSeminorms ℂ _ ℂ).continuous_seminorm (0, 0)) N
    refine ⟨C, fun x hx => ?_⟩
    obtain ⟨f₁, h1, h2⟩ := hC () x hx
    have h3 := norm_evI_le x
    set r := ∑ i, ∑ v : InfinitePlace F, ‖(x i).1 v‖
    have hr : 0 < 1 + r := by positivity
    have h4 : ‖f₁ y‖ ≤ C * (1 + r) ^ (-(N : ℝ)) := (SchwartzMap.norm_le_seminorm ℂ f₁ y).trans h2
    rw [Real.rpow_neg hr.le, Real.rpow_natCast, ← div_eq_mul_inv, le_div_iff₀ (by positivity)] at h4
    rw [← h1]
    refine le_trans ?_ h4
    gcongr

theorem decay : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a')
    (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' → ∀ e, IsEv B G.M G₁.M H.ι H'.ι (isoA H H') e → ∀ (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W), IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ Φ ∈ schA F (Fin (b + 2) × Fin (b + 2 + a')), ∀ y : Fin b × Fin (b + a') → AF F, ∀ (m : ℕ) (b₀ : Module.Basis (Fin m) F E) (N : ℕ), ∃ C : ℝ, ∀ a, ‖(fun a : AE F E => e (G.M.co.rho B.ψ (a • Matrix.vecMulVec (incV F H.x) (incV F H'.y)) Φ) y) a‖ * (1 + ‖fun i => evI F ((Algebra.TensorProduct.basis (AF F) b₀).equivFun a i)‖) ^ N ≤ C := by
  intro hKP F E _ _ _ _ _ σ B b a' G G₁ H H' hC e he X om om' om₁ om₁' hT hT₁ Φ hΦ y m b₀ N
  obtain ⟨K, hK, hK0⟩ := GlobalTheory.ConeTateSupp.finsupp hKP F E σ B b a' G G₁ H H' hC e he X om om' om₁ om₁' hT hT₁ Φ hΦ y m b₀
  choose c hc using GlobalTheory.ConeTateSupp.trace_mul_dual (F := F) (E := E) b₀
  let S := fun j => G.M.co.e (inclR (F := F) (AF F) (b₀ j) • Matrix.vecMulVec (incV F H.x) (incV F H'.y))
  let U := fun i => G.M.co.e (inclR (F := F) (AF F) (σ (c i)) • Matrix.vecMulVec (incV F H.y) (incV F H'.x))
  obtain ⟨C, hCb⟩ := value_decay B.ψ hT.base.std S U (fun i j => by
      have h := GlobalTheory.ConeTateSupp.symp_shift hT.base.cm hT.geo.hW.skew H H' hC.hH.xy hC.hH'.xy
        (inclR (F := F) (AF F) (b₀ j)) 1 (c i)
      rw [one_smul, one_mul, hc] at h
      rw [← G.M.co.form]
      refine h.trans ?_
      rw [show inclR (F := F) (AF F) (b₀ j) = Algebra.TensorProduct.basis (AF F) b₀ j from
        (Algebra.TensorProduct.basis_apply _ _).symm, Module.Basis.equivFun_self]
      rcases eq_or_ne i j with rfl | hij
      · rw [if_pos rfl, if_pos rfl]
      · rw [if_neg hij, if_neg hij.symm])
    (sliceL (fun q => (y q).2) ∘ₗ e) (exists_slice_clm hT.geo.hM he _) (fun i a Ψ hΨ => by
      have := he.inv (Matrix.vecMulVec (a • inclR (F := F) (AF F) (σ (c i)) • incV F H.y) (incV F H'.x))
        (Or.inl ⟨_, rfl⟩) Ψ hΨ
      rw [Matrix.smul_vecMulVec, Matrix.smul_vecMulVec, Darboux.rho, map_smul] at this
      exact congrArg (sliceL _) this) hK
    (fun q => InfiniteAdeleRing.ringEquiv_mixedSpace F (y q).1) N Φ hΦ
  refine ⟨max C 0, fun a => ?_⟩
  by_cases ha : (fun i => ((Algebra.TensorProduct.basis (AF F) b₀).equivFun a i).2) ∈ K
  swap
  · rw [hK0 a ha, norm_zero, zero_mul]
    exact le_max_right _ _
  refine le_trans (le_of_eq ?_) ((hCb _ ha).trans (le_max_left _ _))
  have hS : G.M.co.e (a • Matrix.vecMulVec (incV F H.x) (incV F H'.y)) =
      ∑ i, (Algebra.TensorProduct.basis (AF F) b₀).equivFun a i • S i := by
    simp only [S, ← map_smul, ← map_sum, ← smul_assoc, ← Finset.sum_smul]
    congr 2
    refine ((Algebra.TensorProduct.basis (AF F) b₀).sum_equivFun a).symm.trans ?_
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.TensorProduct.basis_apply]
    rfl
  rw [← hS]
  simp only [LinearMap.comp_apply, sliceL, LinearMap.coe_mk, AddHom.coe_mk, RingEquiv.symm_apply_apply]
  rfl

end GlobalTheory.ConeTateDecay

end
