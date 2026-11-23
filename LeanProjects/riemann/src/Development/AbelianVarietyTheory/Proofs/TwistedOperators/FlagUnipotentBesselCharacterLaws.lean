import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.MixModel GlobalTheory.MixPer
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CharLaws

variable {D : D7}

section Conj

variable {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ)

theorem embedded_anisotropic_inv_fixes_isotropic (k : GA D S₀) : mt S (d.emb0 k)⁻¹ ⬝ d.jX = d.jX := by
  rw [← map_inv]; exact d.wittDecomp_anisotropicEmbedding_inclX k⁻¹

theorem witt_isotropic_projection_embedded_anisotropic_mul {m : ℕ} (k : GA D S₀) (x : Mx D S.rank m) : d.pX ⬝ (mt S (d.emb0 k) ⬝ x) = d.pX ⬝ x := by
  rw [← Matrix.mul_assoc, d.wittDecomp_projX_anisotropicEmbedding]

theorem blockX_conj (k : GA D S₀) (n : GA D S) :
    blockX d (d.emb0 k * n * (d.emb0 k)⁻¹) = blockX d n := by
  rw [blockX, blockX, mt_mul, mt_mul]
  simp only [Matrix.mul_assoc]
  rw [embedded_anisotropic_inv_fixes_isotropic, witt_isotropic_projection_embedded_anisotropic_mul]

theorem coefX_conj (k : GA D S₀) (n : GA D S) (z : Fin S₀.rank → D.host.E)
    (hz : mt S₀ k⁻¹ *ᵥ ratV z = ratV z) :
    coefX d z (d.emb0 k * n * (d.emb0 k)⁻¹) = coefX d z n := by
  rw [coefX, coefX, mt_mul, mt_mul, ← map_inv]
  simp only [Matrix.mul_assoc]
  rw [d.wittDecomp_anisotropicEmbedding_inclAnisotropic, witt_isotropic_projection_embedded_anisotropic_mul]
  have e : d.pX ⬝ (mt S n ⬝ (d.j0 ⬝ mt S₀ k⁻¹)) = d.pX ⬝ (mt S n ⬝ d.j0) ⬝ mt S₀ k⁻¹ := by
    simp only [Matrix.mul_assoc]
  rw [e, ← Matrix.mulVec_mulVec, hz]

theorem conj_mem_flagN (k : GA D S₀) {n : GA D S} (hn : n ∈ flagN d) :
    d.emb0 k * n * (d.emb0 k)⁻¹ ∈ flagN d := by
  have hi := (isIsoSub_e d).1
  change n ∈ NFlag S d.e at hn
  change _ ∈ NFlag S d.e
  rw [GlobalTheory.BesselChar.mem_NFlag_iff S d.e hi] at hn ⊢
  have he : mt S (d.emb0 k) ⬝ d.e.map (incA D) = d.e.map (incA D) := d.wittDecomp_anisotropicEmbedding_inclX k
  have he' : mt S (d.emb0 k)⁻¹ ⬝ d.e.map (incA D) = d.e.map (incA D) := embedded_anisotropic_inv_fixes_isotropic d k
  rw [mt_mul, mt_mul]
  exact hn.conj he he' (mt_mul_inv S _) (GlobalTheory.BesselChar.perp_fixed d.e _ he')

end Conj

section Cont

variable (ψ : AddChar (AF D.host.F) ℂ) {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ)

theorem continuous_psiBes (hψ : Continuous ψ) (θ : D.host.E) (z : Fin S₀.rank → D.host.E) :
    Continuous (psiBes ψ d θ z) := by
  have : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) (AE D)
  have ht : Continuous (Algebra.trace (AF D.host.F) (AE D)) := IsModuleTopology.continuous_of_linearMap _
  have hm : Continuous (mt S) := GlobalTheory.MixModel.continuous_mt S
  have hb : Continuous fun g => blockX d g := continuous_const.matrix_mul (hm.matrix_mul continuous_const)
  have hc : Continuous fun g => coefX d z g :=
    (continuous_const.matrix_mul (hm.matrix_mul continuous_const)).matrix_mulVec continuous_const
  have hu : Continuous fun g => upSum (blockX d g) := by
    unfold upSum
    refine continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ => ?_
    split_ifs
    · exact (continuous_apply j).comp ((continuous_apply i).comp hb)
    · exact continuous_const
  have hd : Continuous fun g => ell D ρ ⬝ᵥ coefX d z g := continuous_const.dotProduct hc
  exact hψ.comp (ht.comp (continuous_const.mul (hu.add hd)))

end Cont

end GlobalTheory.CharLaws

namespace GlobalTheory.CharLaws

variable {D : D7}

section Rat

variable (ψ : AddChar (AF D.host.F) ℂ) {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ)

theorem upSum_rat (N : Matrix (Fin ρ) (Fin ρ) D.host.E) :
    upSum (rat N) = incA D (∑ i : Fin ρ, ∑ j : Fin ρ, if j.1 = i.1 + 1 then N i j else 0) := by
  simp only [upSum, rat, Matrix.map_apply, map_sum, apply_ite (incA D), map_zero]

theorem ratV_dotProduct {m : ℕ} (a b : Fin m → D.host.E) : ratV a ⬝ᵥ ratV b = incA D (a ⬝ᵥ b) := by
  simp only [dotProduct, ratV, map_sum, map_mul]

theorem ell_eq : ell D ρ = ratV (fun i : Fin ρ => if i.1 + 1 = ρ then (1 : D.host.E) else 0) := by
  funext i
  simp only [ell, ratV]
  split_ifs <;> simp

theorem simpleSum_rat (z : Fin S₀.rank → D.host.E) {γ : GA D S} (hγ : γ ∈ GQ S) :
    ∃ x : D.host.E, simpleSum d z γ = incA D x := by
  obtain ⟨M, hM⟩ := (mem_GQ_iff S γ).1 hγ
  have hM' : rat M = mt S γ := hM
  have hb : blockX d γ = rat (d.qX * (M * d.e)) := by
    rw [blockX, ← hM', rat_mul, rat_mul]; rfl
  have hc : coefX d z γ = ratV ((d.qX * (M * d.i₀)) *ᵥ z) := by
    rw [coefX, ← hM', ratV_mulVec, rat_mul, rat_mul]; rfl
  rw [simpleSum, hb, hc, upSum_rat, ell_eq, ratV_dotProduct, ← map_add]
  exact ⟨_, rfl⟩

theorem psiBes_rat (hψ : ∀ a : D.host.F, ψ (algebraMap D.host.F (AF D.host.F) a) = 1) (θ : D.host.E)
    (z : Fin S₀.rank → D.host.E) {γ : GA D S} (hγ : γ ∈ GQ S) : psiBes ψ d θ z γ = 1 := by
  obtain ⟨x, hx⟩ := simpleSum_rat d z hγ
  rw [psiBes, hx, ← map_mul, psiE, GlobalTheory.BesselChar.trace_incA]
  exact hψ _

end Rat

end GlobalTheory.CharLaws

namespace GlobalTheory.CharLaws

variable {D : D7}

section Bes

variable (ψ : AddChar (AF D.host.F) ℂ) {S S₀ A L : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (o : OrthDec S₀ A L)

theorem emb_vecB (a : GA D A) (ζ : Fin L.rank → D.host.E) :
    mt S₀ (o.emb (a, 1)) *ᵥ ratV (vecB o ζ) = ratV (vecB o ζ) := by
  rw [vecB, ratV_mulVec, Matrix.mulVec_mulVec]
  change (mt S₀ (o.emb (a, 1)) ⬝ o.jB) *ᵥ _ = o.jB *ᵥ _
  rw [o.emb_jB, mt_one, Matrix.mul_one]

theorem psiBes_conj (θ : D.host.E) (ζ : Fin L.rank → D.host.E) (n : GA D S) (h : GA D A) :
    psiBes ψ d θ (vecB o ζ) (embA d o h * n * (embA d o h)⁻¹) = psiBes ψ d θ (vecB o ζ) n := by
  have hz : mt S₀ (o.emb (h, 1))⁻¹ *ᵥ ratV (vecB o ζ) = ratV (vecB o ζ) := by
    rw [← map_inv, Prod.inv_mk, inv_one]; exact emb_vecB o h⁻¹ ζ
  rw [embA_apply, psiBes, psiBes, simpleSum, simpleSum, blockX_conj, coefX_conj d _ n _ hz]

theorem psiFlag_conj (n : GA D S) (h : GA D S₀) :
    psiFlag ψ d (d.emb0 h * n * (d.emb0 h)⁻¹) = psiFlag ψ d n := by
  rw [psiFlag, psiFlag, blockX_conj]

theorem embA_conj_mem (h : GA D A) {n : GA D S} (hn : n ∈ flagN d) :
    embA d o h * n * (embA d o h)⁻¹ ∈ flagN d :=
  conj_mem_flagN d _ hn

theorem mem_besGrp (g : GA D S) : g ∈ besGrp d o ↔ ∃ n ∈ flagN d, ∃ h, g = n * embA d o h := by
  constructor
  · intro hg
    let K : Subgroup (GA D S) :=
      { carrier := {g | ∃ n ∈ flagN d, ∃ h, g = n * embA d o h}
        one_mem' := ⟨1, one_mem _, 1, by rw [map_one, mul_one]⟩
        mul_mem' := by
          rintro _ _ ⟨n₁, hn₁, h₁, rfl⟩ ⟨n₂, hn₂, h₂, rfl⟩
          refine ⟨n₁ * (embA d o h₁ * n₂ * (embA d o h₁)⁻¹), mul_mem hn₁ (embA_conj_mem d o h₁ hn₂), h₁ * h₂, ?_⟩
          rw [map_mul]; group
        inv_mem' := by
          rintro _ ⟨n, hn, h, rfl⟩
          refine ⟨embA d o h⁻¹ * n⁻¹ * (embA d o h⁻¹)⁻¹, embA_conj_mem d o h⁻¹ (inv_mem hn), h⁻¹, ?_⟩
          rw [map_inv]; group }
    have hle : besGrp d o ≤ K := sup_le (fun n hn => ⟨n, hn, 1, by rw [map_one, mul_one]⟩)
      (by rintro _ ⟨h, rfl⟩; exact ⟨1, one_mem _, h, (one_mul _).symm⟩)
    exact hle hg
  · rintro ⟨n, hn, h, rfl⟩
    exact mul_mem (Subgroup.mem_sup_left hn) (Subgroup.mem_sup_right ⟨h, rfl⟩)

theorem embRel_embA (ι : A.V →ₗ[D.host.E] S.V) (hι : frameMat S A ι = d.i₀ * o.iA) (h : GA D A) :
    EmbRel S A ι (embA d o h) h := by
  rw [EmbRel, hι]
  refine ⟨?_, fun x hx => ?_⟩
  · change mt S (d.emb0 (o.emb (h, 1))) ⬝ rat (d.i₀ * o.iA) = rat (d.i₀ * o.iA) ⬝ mt A h
    rw [rat_mul]
    change mt S (d.emb0 (o.emb (h, 1))) ⬝ (d.j0 ⬝ o.jA) = d.j0 ⬝ o.jA ⬝ mt A h
    rw [← Matrix.mul_assoc, d.wittDecomp_anisotropicEmbedding_inclAnisotropic, Matrix.mul_assoc, o.emb_jA, Matrix.mul_assoc]
  · have hι₂ : frameMat S₀ A (Matrix.toLin A.frame S₀.frame o.iA) = o.iA := LinearMap.toMatrix_toLin _ _ _
    have hA := (o.embRel_left _ hι₂ h).2
    rw [hι₂] at hA
    have hw : (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) o.iA * S₀.gram) *ᵥ (d.q0 *ᵥ x) = 0 := by
      rw [Matrix.mulVec_mulVec, cT_sig, HypDec.q0]
      have e : o.iAᴴ * S₀.gram * (S₀.gram⁻¹ * (d.i₀ᴴ * S.gram)) = (d.i₀ * o.iA)ᴴ * S.gram := by
        rw [conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc S₀.gram,
          Matrix.mul_nonsing_inv _ (gram_isUnit_det S₀), Matrix.one_mul, Matrix.mul_assoc]
      rw [e, ← cT_sig]; exact hx
    have h1 : mt S₀ (o.emb (h, 1)) *ᵥ ratV (d.q0 *ᵥ x) = ratV (d.q0 *ᵥ x) := hA _ hw
    have h2 : d.p0 *ᵥ ratV x = ratV (d.q0 *ᵥ x) := (ratV_mulVec _ _).symm
    have h3 := congrArg (· *ᵥ ratV x) d.sum_eq_one
    change mt S (d.emb0 (o.emb (h, 1))) *ᵥ ratV x = ratV x
    simp only [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, Matrix.one_mulVec] at h3
    rw [d.unitaryMatrix_wittCoreEmbedding]
    simp only [Matrix.add_mulVec, ← Matrix.mulVec_mulVec]
    rw [h2, h1, ← h2]
    exact h3

end Bes

end GlobalTheory.CharLaws

namespace GlobalTheory.MixPer

theorem charLaws : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ (S S₀ A L : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (o : OrthDec S₀ A L) (ζ : Fin L.rank → D.host.E) (θ : D.host.E), (∀ z, Continuous (psiBes ψ d θ z)) ∧ (∀ z, ∀ γ ∈ GQ S, psiBes ψ d θ z γ = 1) ∧ (∀ n h, psiBes ψ d θ (vecB o ζ) (embA d o h * n * (embA d o h)⁻¹) = psiBes ψ d θ (vecB o ζ) n) ∧ (∀ n h, psiFlag ψ d (d.emb0 h * n * (d.emb0 h)⁻¹) = psiFlag ψ d n) ∧ (∀ g, g ∈ besGrp d o ↔ ∃ n ∈ flagN d, ∃ h, g = n * embA d o h) ∧ ∀ ι : A.V →ₗ[D.host.E] S.V, frameMat S A ι = d.i₀ * o.iA → ∀ h, EmbRel S A ι (embA d o h) h := by
  intro D ψ hψ S S₀ A L ρ d o ζ θ
  exact ⟨fun z => GlobalTheory.CharLaws.continuous_psiBes ψ d hψ.1 θ z,
    fun z γ hγ => GlobalTheory.CharLaws.psiBes_rat ψ d hψ.2.2.1 θ z hγ,
    fun n h => GlobalTheory.CharLaws.psiBes_conj ψ d o θ ζ n h,
    fun n h => GlobalTheory.CharLaws.psiFlag_conj ψ d n h,
    fun g => GlobalTheory.CharLaws.mem_besGrp d o g,
    fun ι hι h => GlobalTheory.CharLaws.embRel_embA d o ι hι h⟩

end GlobalTheory.MixPer

end
