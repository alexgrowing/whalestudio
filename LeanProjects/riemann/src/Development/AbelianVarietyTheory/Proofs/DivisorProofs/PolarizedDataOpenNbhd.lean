import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.Divisors.PairsOfSquareTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMaxThOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemFinPt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TruncMatTranspose
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLatLevel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondConfigurationTripleCompatible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFactorPureTensorComponentAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExistsStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open Filter Topology GlobalTheory.TruncFix

noncomputable section

namespace GlobalTheory.TruncNear

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem continuous_truncMat {n : ℕ} (e : AF F) :
    Continuous fun A : Matrix (Fin n) (Fin n) (AE F E) => truncMat e A := by
  haveI : IsTopologicalRing (AE F E) := GlobalTheory.Doubling.isTopologicalRing_tens
  refine continuous_pi fun i => continuous_pi fun j => ?_
  have h : (fun A : Matrix (Fin n) (Fin n) (AE F E) => truncMat e A i j) =
      fun A => (1 : Matrix (Fin n) (Fin n) (AE F E)) i j +
        (e • (1 : AE F E)) * (A i j - (1 : Matrix (Fin n) (Fin n) (AE F E)) i j) := by
    funext A
    simp [truncMat]
  rw [h]
  exact continuous_const.add (continuous_const.mul ((continuous_apply_apply i j).sub continuous_const))

theorem continuous_truncU (T : Finset (Pl F)) {n : ℕ} {J : Matrix (Fin n) (Fin n) E} :
    Continuous fun k : UA σ J => truncU T k := by
  refine Continuous.subtype_mk ?_ _
  rw [Units.continuous_iff]
  exact ⟨(continuous_truncMat _).comp (Units.continuous_val.comp continuous_subtype_val),
    (continuous_truncMat _).comp (Units.continuous_coe_inv.comp continuous_subtype_val)⟩

theorem truncU_one (T : Finset (Pl F)) {n : ℕ} {J : Matrix (Fin n) (Fin n) E} : truncU T (1 : UA σ J) = 1 := by
  refine Subtype.ext (Units.ext ?_)
  show truncMat (idem T) 1 = 1
  simp [truncMat]

theorem truncU_empty {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (k : UA σ J) : truncU ∅ k = 1 := by
  refine Subtype.ext (Units.ext ?_)
  show truncMat (idem ∅) (mat k) = 1
  simp [truncMat, idem]

theorem near_pair (hA : ActsEx) {B : Base F E} {n d : ℕ} {Y : Spc F E n} {W : Spc F E d} {M : Model σ Y W}
    {χX χW : Chr F E} {om : Rep σ Y W} {r s r' s' : ℕ} (hP : IsPair B M χX χW om r s r' s')
    (Ψ : Fn F n d) (hΨ : Ψ ∈ PolData B M) (S : Finset (Pl F)) :
    ∀ᶠ h in 𝓝 (1 : UA σ W.J), om (1, truncU S h) Ψ = Ψ := by
  classical
  induction hΨ using Submodule.span_induction with
  | zero => exact Eventually.of_forall fun h => map_zero _
  | add x y _ _ hx hy => exact (hx.and hy).mono fun h hh => by rw [map_add, hh.1, hh.2]
  | smul c x _ hx => exact hx.mono fun h hh => by rw [map_smul, hh]
  | mem x hx =>
    obtain ⟨f, -, φ, hSB, hcof, rfl⟩ := hx
    have hstd : ∀ᶠ w in cofinite, φ w = Set.indicator {x | ∀ i, x i ∈ w.adicCompletionIntegers F} 1 :=
      (hcof.and hP.good.std).mono fun w hw => hw.1.trans hw.2
    have hpure : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ ∈ schA F _ := GlobalTheory.ConeMeasV.pure_mem_schA hP.good f φ hSB hcof
    have hfin := fun x => GlobalTheory.PureFactor.mulSupport_finite φ hstd x
    have hone : ∀ v : Pl F, ∀ᶠ h in 𝓝 (1 : UA σ W.J),
        om (1, truncU {v} h) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ := by
      intro v
      obtain ⟨U, hU, hfix⟩ := (hA F E σ B n d Y W M χX χW om r s r' s' hP v).2.2 (φ v) (hSB v)
      have hc : Continuous fun h : UA σ W.J => ((1 : UA σ Y.J), truncU {v} h) :=
        continuous_const.prodMk (continuous_truncU {v})
      have ht : Tendsto (fun h : UA σ W.J => ((1 : UA σ Y.J), truncU {v} h)) (𝓝 1) (𝓝 1) := by
        have := hc.tendsto 1
        rwa [truncU_one] at this
      refine (ht.eventually hU).mono fun h hh => ?_
      have h1 : (1 : UA σ Y.J) ∈ UAt σ Y (evFin F v) := by
        rw [← truncU_one {v}]; exact truncU_mem_UAt v 1
      have hA' := hfix _ hh h1 (truncU_mem_UAt v h)
      rw [GlobalTheory.ThK.LocalOps.acts_pure v (om (1, truncU {v} h)) f φ (φ v) hpure hfin hA', Function.update_eq_self]
    refine Finset.induction_on S ?_ ?_
    · refine Eventually.of_forall fun h => ?_
      rw [truncU_empty, show ((1 : UA σ Y.J), (1 : UA σ W.J)) = 1 from rfl, map_one, Module.End.one_apply]
    · intro v T hv ih
      refine (ih.and (hone v)).mono fun k hk => ?_
      rw [truncU_insert hv, show ((1 : UA σ Y.J), truncU {v} k * truncU T k) =
        ((1 : UA σ Y.J), truncU {v} k) * ((1 : UA σ Y.J), truncU T k) by simp, map_mul, Module.End.mul_apply, hk.1, hk.2]

theorem near : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple B G X om om' → ∀ Ψ ∈ GlobalTheory.ThK.PolData B G.M', ∀ S : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F), ∃ U ∈ nhds (1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ G.W.J), ∀ h ∈ U, om' (1, GlobalTheory.TruncFix.truncU S h) Ψ = Ψ := by
  intro hKP F E _ _ _ _ _ σ B a a' G X om om' hT Ψ hΨ S
  exact ⟨_, near_pair (GlobalTheory.T.theta_action_exists hKP.base) (GlobalTheory.ThK.Inhab.pairV' hT) Ψ hΨ S, fun h hh => hh⟩

end GlobalTheory.TruncNear

end
