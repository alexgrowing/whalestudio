import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InfPartFPlaceIdem
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RationalSymplecticPointsSelfAnnihilator
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardTraceAdelicAddCharLocalComponentNeOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardTraceAddCharIsStandardCharOfAdmissibleCM
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

noncomputable section

namespace GlobalTheory.RatAnnihF

section
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem cAF_incAF (σ : E →ₐ[F] E) (e : E) : cAF σ (incAF F E e) = incAF F E (σ e) := by
  show Algebra.TensorProduct.map (AlgHom.id F (AF F)) σ ((1 : AF F) ⊗ₜ[F] e) = (1 : AF F) ⊗ₜ[F] σ e
  rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply]

theorem psiV_exists_ne_one {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (v : HeightOneSpectrum (𝓞 F)) :
    ∃ y, psiV F ψ v y ≠ 1 := by
  by_contra h
  push_neg at h
  refine GlobalTheory.PsiNontriv.psiV_ne_one ψ hψ v (DFunLike.ext _ _ fun t => ?_)
  rw [AddChar.one_apply]
  exact h t

theorem adele_rat_of_isGood {σ : E →ₐ[F] E} {B : Base F E} (hB : B.IsGood σ) (a : AF F)
    (h : ∀ c : F, B.ψ (a * algebraMap F _ c) = 1) : ∃ d : F, a = algebraMap F _ d := by
  haveI : IsTotallyReal F := hB.cm.1
  obtain ⟨⟨θ, hθ⟩, -⟩ := (GlobalTheory.StdCharWeilDatum.isStdCharF_of_isGood F E σ B hB).2
  let L : Ainf F →+ ℂ := AddMonoidHom.mk' (fun x => ∑ w, θ w (x ⊗ₜ[F] (1 : E))) fun a b => by
    simp only [map_add, TensorProduct.add_tmul, Finset.sum_add_distrib]
  have hL : ∀ x, L x = ((Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (InfiniteAdeleRing.ringEquiv_mixedSpace F x) : ℝ) : ℂ) :=
    fun x => GlobalTheory.StdCharWeilDatum.sum_infFam B θ hθ x
  refine GlobalTheory.RatAnnih.adele_rat (GlobalTheory.StdCharWeilDatum.isCharAF hB.std) (psiV_exists_ne_one hB.std) L
    (continuous_finset_sum _ fun w _ => (hθ w).2) (fun x => ?_) (fun x => ?_) a h
  · rw [hL]
    have e : InfiniteAdeleRing.ringEquiv_mixedSpace F (algebraMap F (Ainf F) x) = mixedEmbedding F x := by
      rw [InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp]
    rw [e, GlobalTheory.LatVacArith.trace_mixedEmbedding]
    exact Complex.ofReal_ratCast _
  · show B.ψ (pairA F x 0) = _
    rw [GlobalTheory.StdCharWeilDatum.psi_pairA hB.std, hL]
    congr 1
    ring

theorem exists_symplOF_eq (σ : E →ₐ[F] E) (hσ : Function.Surjective σ) {nS nT : ℕ}
    {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E} (hS : IsHermND σ JS) (hT : IsHermND σ JT)
    {ξ₀ : E} (hξ : ξ₀ ≠ 0) (x : WOF F E nS nT) (i : Fin nT) (j : Fin nS) (e : E) :
    ∃ γ ∈ ratLF F E nS nT, symplOF σ JS JT ξ₀ x γ = Algebra.trace (AF F) (AEF F E) (incAF F E e * x i j) := by
  let g := Function.surjInv hσ
  let P := JS * Matrix.single j i (ξ₀⁻¹ * e) * JT⁻¹
  refine ⟨(incAF F E).toAddMonoidHom.mapMatrix (Matrix.of fun c b => g (P b c)), ⟨_, rfl⟩, ?_⟩
  have h := GlobalTheory.RatAnnih.sum_single (incAF F E) JS JT (isUnit_iff_ne_zero.2 hS.2) (isUnit_iff_ne_zero.2 hT.2) j i
    (ξ₀⁻¹ * e) x
  have h2 : hOF σ JS JT x ((incAF F E).toAddMonoidHom.mapMatrix (Matrix.of fun c b => g (P b c))) =
      incAF F E (ξ₀⁻¹ * e) * x i j := by
    rw [← h, hOF]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ =>
      Finset.sum_congr rfl fun d _ => ?_
    simp only [AddMonoidHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, RingHom.toAddMonoidHom_eq_coe,
      AddMonoidHom.coe_coe, cAF_incAF, g, Function.surjInv_eq hσ]
    rfl
  rw [symplOF, h2, ← mul_assoc, ← RingHom.map_mul, mul_inv_cancel_left₀ hξ]

theorem symplOF_rat (σ : E →ₐ[F] E) [Module.Finite F E] {nS nT : ℕ}
    (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E) (ξ₀ : E)
    (M N : Matrix (Fin nT) (Fin nS) E) :
    ∃ a : F, symplOF σ JS JT ξ₀ ((incAF F E).toAddMonoidHom.mapMatrix M) ((incAF F E).toAddMonoidHom.mapMatrix N) =
      algebraMap F (AF F) a := by
  refine ⟨Algebra.trace F E (ξ₀ * ∑ a, ∑ b, ∑ c, ∑ d, JS⁻¹ a b * σ (N c b) * JT c d * M d a), ?_⟩
  have h : hOF σ JS JT ((incAF F E).toAddMonoidHom.mapMatrix M) ((incAF F E).toAddMonoidHom.mapMatrix N) =
      incAF F E (∑ a, ∑ b, ∑ c, ∑ d, JS⁻¹ a b * σ (N c b) * JT c d * M d a) := by
    simp only [hOF, AddMonoidHom.mapMatrix_apply, Matrix.map_apply, RingHom.toAddMonoidHom_eq_coe,
      AddMonoidHom.coe_coe, cAF_incAF, map_sum, map_mul]
  rw [symplOF, h, ← map_mul]
  show Algebra.trace (AF F) (AEF F E) ((1 : AF F) ⊗ₜ[F] _) = _
  rw [GlobalTheory.LatVac.trace_tmul, one_mul]
end

theorem ratLF_annihilator : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E), B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
    IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → ∀ x : WOF F E nS nT,
      (∀ γ ∈ ratLF F E nS nT, B.ψ (symplOF σ JS JT ξ₀ x γ) = 1) ↔ x ∈ ratLF F E nS nT := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ hξ x
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by rw [hB.cm.2.2.1]; norm_num)
  have hσ : Function.Surjective σ := (Algebra.IsAlgebraic.algHom_bijective σ).2
  constructor
  · intro h
    have hent : ∀ i j, ∃ e : E, x i j = (1 : AF F) ⊗ₜ[F] e := fun i j =>
      GlobalTheory.RatAnnih.tensor_rat (x i j) fun e => adele_rat_of_isGood hB _ fun c => by
        obtain ⟨γ, hγ, hγe⟩ := exists_symplOF_eq σ hσ hS hT hξ x i j (c • e)
        exact (congrArg B.ψ ((GlobalTheory.RatAnnih.trace_mul_algebraMap (x i j) e c).trans hγe.symm)).trans (h γ hγ)
    choose M hM using hent
    refine ⟨Matrix.of M, Matrix.ext fun i j => ?_⟩
    rw [hM i j]
    rfl
  · rintro ⟨M, rfl⟩ _ ⟨N, rfl⟩
    obtain ⟨a, ha⟩ := symplOF_rat σ JS JT ξ₀ M N
    rw [ha]
    exact (GlobalTheory.StdCharWeilDatum.isCharAF hB.std).2.2.1 a

end GlobalTheory.RatAnnihF
