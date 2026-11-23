import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocPart
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilActionUnitaryCompact

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.LemF
open GlobalTheory.Doubling (absE)
open GlobalTheory.ArchLocality

noncomputable section
namespace GlobalTheory.ArchLocalityX

theorem comm_fin_left {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W)
    (hW : M.IsWeil ψ χX χW om) (g : UA σ X.J) (hg : g ∈ UAt σ X (evI F))
    (u : AF F) (hu : evI F u = 0) (p q : Fin n × Fin d → AF F)
    (Φ : (Fin n × Fin d → AF F) → ℂ) (hΦ : Φ ∈ schA F (Fin n × Fin d)) :
      om (g, 1) (schr ψ (u • p, u • q) Φ) = schr ψ (u • p, u • q) (om (g, 1) Φ) := by
  have hS := IsUWeilPair.isUSplitting hW
  set w := M.co.e.symm (p, q) with hw
  have he : M.co.e (u • w) = (u • p, u • q) := by
    rw [LinearEquiv.map_smul, hw, LinearEquiv.apply_symm_apply, Prod.smul_mk]
  have e1 : u • mat g = u • (1 : Matrix (Fin n) (Fin n) (AE F E)) := by
    have := hg u hu
    rwa [smul_sub, sub_eq_zero] at this
  have hact : actAB (cA σ) ((g, 1) : UA σ X.J × UA σ W.J) (u • w) = u • w := by
    change mat g * (u • w) * (mat (1 : UA σ W.J))ᵀ = u • w
    have h1 : mat (1 : UA σ W.J) = 1 := rfl
    rw [h1, Matrix.transpose_one, Matrix.mul_one, Matrix.mul_smul, ← Matrix.smul_mul, e1, Matrix.smul_mul,
      Matrix.one_mul]
  have h2 := hS.impl (g, 1) (u • w) Φ hΦ
  simp only [Darboux.rho, he, hact] at h2
  exact h2

theorem acts_arch_left : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W),
    IsCMExt F E σ → IsStd ψ → M.IsWeil ψ χX χW om →
    ∀ g ∈ UAt σ X (evI F), ∀ f : SInf F (Fin n × Fin d), ∃ f₁ : SInf F (Fin n × Fin d), Acts (evI F) (om (g, 1)) f f₁ := by
  intro _ F E _ _ _ _ _ σ n d X W M ψ χX χW om _ hψ hW g hg f
  have hS := IsUWeilPair.isUSplitting hW
  set T := om (g, 1) with hTdef
  have hpres : ∀ Φ ∈ schA F (Fin n × Fin d), T Φ ∈ schA F (Fin n × Fin d) := fun Φ hΦ => hS.pres (g, 1) Φ hΦ
  have hcomm := comm_fin_left M ψ χX χW om hW g hg
  obtain ⟨r₀, hr₀1, hr₀⟩ := ref_fun (F := F) (Fin n × Fin d)
  set Φ₀ := tens (evI F) (f : (Fin n × Fin d → mixedEmbedding.mixedSpace F) → ℂ) r₀ with hΦ₀
  have hm₀ : Φ₀ ∈ schA F _ := (hr₀ f).2
  obtain ⟨f₁, hf₁⟩ := res_arch (T Φ₀) (hpres Φ₀ hm₀)
  refine ⟨f₁, fun r hr => ?_⟩
  funext y
  set u : AF F := (0, 1) with hu
  have hu0 : evI F u = 0 := evI_fin
  have htr : ∀ Ψ ∈ schA F (Fin n × Fin d), T (fun w => Ψ (w + u • (-y))) = fun w => T Ψ (w + u • (-y)) := by
    intro Ψ hΨ
    have e := hcomm u hu0 (-y) 0 Ψ hΨ
    have hs0 : ∀ G : (Fin n × Fin d → AF F) → ℂ, schr ψ (u • (-y), u • (0 : Fin n × Fin d → AF F)) G =
        fun w => G (w + u • (-y)) := by
      intro G; funext w; simp [schr]
    rw [hs0, hs0] at e
    exact e
  set Φ₁ := tens (evI F) (f : (Fin n × Fin d → mixedEmbedding.mixedSpace F) → ℂ) r with hΦ₁
  set Φ₂ : (Fin n × Fin d → AF F) → ℂ := r y • (fun w => Φ₀ (w + u • (-y))) with hΦ₂
  have hm₂ : Φ₂ ∈ schA F _ := Submodule.smul_mem _ _ (GlobalTheory.SchwartzTranslation.schA_add_const _ _ hm₀)
  have hz2 : ∀ z : Fin n × Fin d → AF F, At (evI F) z → ∀ i, (z i).2 = 0 := by
    intro z hz i
    have := congrArg Prod.snd (congrFun (hz u hu0) i)
    change (u * z i).2 = (0 : AF F).2 at this
    have e : (u * z i).2 = (z i).2 := one_mul _
    rw [e] at this
    exact this
  have hvan : ∀ z, At (evI F) z → (Φ₁ - Φ₂) (y + z) = 0 := by
    intro z hz
    have e1 : r (y + z) = r y := hr.1 y z hz
    have e2 : (fun i => evI F ((y + z + u • (-y)) i)) = fun i => evI F ((y + z) i) := by
      funext i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, evI_add, evI_mul, hu0, zero_mul, add_zero]
    have e3 : r₀ (y + z + u • (-y)) = 1 := by
      refine hr₀1 _ fun i => ?_
      change ((y i + z i) + u * -(y i)).2 = 0
      change (y i).2 + (z i).2 + 1 * -(y i).2 = 0
      rw [hz2 z hz i]
      ring
    simp only [Pi.sub_apply, hΦ₂, hΦ₁, hΦ₀, Pi.smul_apply, smul_eq_mul, tens]
    rw [e2, e3, e1]
    ring
  have h0 := fibre ψ hψ T hcomm (Φ₁ - Φ₂) (sub_mem hr.2 hm₂) y hvan
  rw [map_sub, Pi.sub_apply, sub_eq_zero] at h0
  have hy0 : y + u • (-y) = fun i => (((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (evI F (y i)), 0) : AF F) := by
    funext i
    refine Prod.ext ?_ ?_
    · change (y i).1 + 0 * -(y i).1 = (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm
        (InfiniteAdeleRing.ringEquiv_mixedSpace F (y i).1)
      rw [RingEquiv.symm_apply_apply]
      ring
    · change (y i).2 + 1 * -(y i).2 = 0
      ring
  have h2 : T Φ₂ y = r y * f₁ (fun i => evI F (y i)) := by
    rw [hΦ₂, map_smul, htr Φ₀ hm₀, Pi.smul_apply, smul_eq_mul, hy0, hf₁]
  rw [h0, h2]
  simp only [tens]
  ring

end GlobalTheory.ArchLocalityX
