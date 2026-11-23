import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.Definitions.Divisors.PairsOfSquareTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzFactorizableApproximationStatement

open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability

noncomputable section

namespace GlobalTheory.ThKLevelSmall

theorem level : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (hσ : ∀ x, σ (σ x) = x) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), GlobalTheory.ThK.KP → IsTriple B G X om om' →
    ∀ (c : E) (hc : c ≠ 0), σ c = -c → ∀ Φ ∈ GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁,
      ∃ U : Subgroup (GAd σ (c • G.W.J.map σ)), IsOpen (U : Set (GAd σ (c • G.W.J.map σ))) ∧ ∀ k ∈ U, k ∈ finPts σ (c • G.W.J.map σ) → ∀ g, (fun x => G.M'.I om' Φ ((toGAd hσ G.W.J hc).symm x)) (g * k) = (fun x => G.M'.I om' Φ ((toGAd hσ G.W.J hc).symm x)) g := by
  intro F E _ _ _ _ _ σ hσ B a a' G X om om' hK hT c hc _ Φ hΦ
  have hP := GlobalTheory.ThK.Inhab.pairV' hT
  have hΦ' : Φ ∈ GlobalTheory.ThK.PolData B G.M' := (Submodule.mem_inf.1 hΦ).1
  have key : ∃ U : Subgroup (UA σ G.W.J), IsOpen (U : Set (UA σ G.W.J)) ∧ ∀ k ∈ U,
      (mat k).map (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)) = 1 → om' (1, k) Φ = Φ := by
    clear hΦ
    induction hΦ' using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨f, -, φ, hSB, hev, rfl⟩ := hx
      exact GlobalTheory.T.exists_open_subgroup_fixing_pure_tensor F E σ B _ _ G.V' G.W G.M' _ _ om' _ _ _ _ hK hP f φ hSB hev
    | zero => exact ⟨⊤, isOpen_univ, fun k _ _ => map_zero _⟩
    | add x y _ _ hx hy =>
      obtain ⟨U, hU, h⟩ := hx
      obtain ⟨V, hV, h'⟩ := hy
      exact ⟨U ⊓ V, hU.inter hV, fun k hk hf => by rw [map_add, h k hk.1 hf, h' k hk.2 hf]⟩
    | smul t x _ hx =>
      obtain ⟨U, hU, h⟩ := hx
      exact ⟨U, hU, fun k hk hf => by rw [map_smul, h k hk hf]⟩
  obtain ⟨U, hU, hfix⟩ := key
  set e := toGAd hσ G.W.J hc
  have he : Continuous e.symm := continuous_subtype_val.subtype_mk _
  refine ⟨U.comap e.symm.toMonoidHom, hU.preimage he, fun k hk hfin g => ?_⟩
  have hf : (mat (e.symm k)).map (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)) = 1 :=
    congrArg Units.val (MonoidHom.mem_ker.1 hfin)
  have h1 : om' (1, e.symm k) Φ = Φ := hfix _ hk hf
  show G.M'.I om' Φ (e.symm (g * k)) = G.M'.I om' Φ (e.symm g)
  rw [map_mul]
  unfold Model.I theta
  congr 1
  funext g'
  rw [show ((g', e.symm g * e.symm k) : UA σ G.V'.J × UA σ G.W.J) = (g', e.symm g) * (1, e.symm k) by simp,
    map_mul, Module.End.mul_apply, h1]

end GlobalTheory.ThKLevelSmall
