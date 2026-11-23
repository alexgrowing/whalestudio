import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Definitions.Divisors.PairsOfSquareTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConeLawSecondOfPrintsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalOperatorMulOfPublished
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdCommOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripleLocalActionAtSpecialPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransportPositionTwo
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueLeviElement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical
namespace GlobalTheory.ConeStabLv

theorem span_cone_aug_stable : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a b : ℕ) (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b))
    (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W),
    CfgB B G G₁ H H' → IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ e', IsEv B G.M' G₁.M' H.ι H'.ι (isoB H H') e' →
    ∀ (ei : SInf F (Fin (b + 2) × Fin (a + (b + 2))) →L[ℂ] SInf F (Fin b × Fin (a + b)))
      (ev : ∀ v : Pl F, ((Fin (b + 2) × Fin (a + (b + 2)) → Fv F v) → ℂ) →ₗ[ℂ] (Fin b × Fin (a + b) → Fv F v) → ℂ),
    ei ≠ 0 → (∀ v, ev v (G.M'.vac v) = G₁.M'.vac v ∧ (SB _).map (ev v) = SB _) →
    (∀ f φ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = G.M'.vac v) → e' (pure f φ) = pure (ei f) fun v => ev v (φ v)) →
    ∀ K : Subgroup (UA σ G.V'.J), IsStab B K →
    ∀ (μKv : Measure (KAt K (evFin F B.v₁))) (μv : Measure (idelesAt E (evFin F B.v₁))),
    IsNormK K (evFin F B.v₁) μKv → IsNormE E B.v₁ μv →
    ∀ h ∈ UAt σ G₁.W (evFin F B.v₁), ∀ φ ∈ (Submodule.span ℂ (coneFin B G.M' om' B.v₁ (ev B.v₁) K μKv μv (shiftB σ H H') X.ν ((a - (b + 2)) / 2 + 1) '' G.M'.SoLoc B.ψ B.τ₁) ⊔ augAt om₁' B.v₁), ∀ φ₁ ∈ SB (Fin b × Fin (a + b) → Fv F B.v₁),
      Acts (evFin F B.v₁) (om₁' (1, h)) φ φ₁ → φ₁ ∈ (Submodule.span ℂ (coneFin B G.M' om' B.v₁ (ev B.v₁) K μKv μv (shiftB σ H H') X.ν ((a - (b + 2)) / 2 + 1) '' G.M'.SoLoc B.ψ B.τ₁) ⊔ augAt om₁' B.v₁) := by
  intro hKP F E _ _ _ _ _ σ B a b G G₁ H H' X om om' om₁ om₁' hc hT hT₁ e' he' ei ev hei hev hpure K hK μKv μv hμK hμ
    h hh φ hφ φ₁ hφ₁ hAct
  have hPr := hKP.base
  have hLP : GlobalTheory.ThK.LemF.IsLocPart G.M' G₁.M' e' ei ev := ⟨hei, hev, hpure⟩
  obtain ⟨hSBc, -, hLv⟩ := GlobalTheory.T.cone_law_second_of_hypotheses hPr F E σ B a b G G₁ H H' hc e' he' ei ev hLP K hK X om om' om₁ om₁' hT hT₁
    B.v₁ μKv μv hμK.1 hμ.1
  have hA : ActsEx := GlobalTheory.ThK.LocalOps.actsEx hPr
  have hP' := GlobalTheory.ThK.Inhab.pairV' hT
  have hP₁' := GlobalTheory.ThK.Inhab.pairV' hT₁
  have mul := GlobalTheory.ThK.LemF.locOpMul hPr F E σ B _ _ _ _ _ _ _ _ _ _ _ _ hP₁' B.v₁
  have h1V := GlobalTheory.ThK.LemF.one_mem_UAt (σ := σ) G.V' (evFin F B.v₁)
  have h1V₁ := GlobalTheory.ThK.LemF.one_mem_UAt (σ := σ) G₁.V' (evFin F B.v₁)
  have h1W₁ := GlobalTheory.ThK.LemF.one_mem_UAt (σ := σ) G₁.W (evFin F B.v₁)
  set N := Submodule.span ℂ (coneFin B G.M' om' B.v₁ (ev B.v₁) K μKv μv (shiftB σ H H') X.ν ((a - (b + 2)) / 2 + 1) ''
    G.M'.SoLoc B.ψ B.τ₁) ⊔ augAt om₁' B.v₁ with hN
  have hex : ∀ ψ ∈ SB (Fin b × Fin (a + b) → Fv F B.v₁),
      ∃ ψ₁, ψ₁ ∈ SB (Fin b × Fin (a + b) → Fv F B.v₁) ∧ Acts (evFin F B.v₁) (om₁' (1, h)) ψ ψ₁ := fun ψ hψ =>
    ⟨_, locOp_mem _ _ _, acts_locOp_om hA hP₁' h1V₁ hh hψ⟩
  have lin := fun c d {ψ ψ'} (hψ : ψ ∈ SB (Fin b × Fin (a + b) → Fv F B.v₁)) (hψ' : ψ' ∈ SB (Fin b × Fin (a + b) → Fv F B.v₁)) =>
    locOp_lin (om₁' (1, h)).isLinear hex c d hψ hψ'
  have hNSB : N ≤ SB (Fin b × Fin (a + b) → Fv F B.v₁) := by
    refine sup_le (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)
    · rintro _ ⟨ψ, hψ, rfl⟩
      exact hSBc ψ hψ.1
    · rintro _ ⟨g, -, ψ, hψ, ψ₁, hψ₁, -, rfl⟩
      exact sub_mem hψ₁ hψ
  let P : Submodule ℂ ((Fin b × Fin (a + b) → Fv F B.v₁) → ℂ) :=
    { carrier := {ψ | ψ ∈ SB (Fin b × Fin (a + b) → Fv F B.v₁) ∧ locOp B.v₁ (om₁' (1, h)) ψ ∈ N}
      add_mem' := by
        rintro ψ ψ' ⟨hψ, h1⟩ ⟨hψ', h2⟩
        refine ⟨add_mem hψ hψ', ?_⟩
        have e := lin 1 1 hψ hψ'
        simp only [one_smul] at e
        rw [e]
        exact add_mem h1 h2
      zero_mem' := by
        refine ⟨zero_mem _, ?_⟩
        have e := lin 0 0 (zero_mem _) (zero_mem _)
        simp only [zero_smul, add_zero] at e
        rw [e]
        exact zero_mem _
      smul_mem' := by
        rintro c ψ ⟨hψ, h1⟩
        refine ⟨(SB _).smul_mem c hψ, ?_⟩
        have e := lin c 0 hψ hψ
        simp only [zero_smul, add_zero] at e
        rw [e]
        exact N.smul_mem c h1 }
  have hNP : N ≤ P := by
    refine sup_le (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)
    · rintro _ ⟨ψ, hψ, rfl⟩
      refine ⟨hSBc ψ hψ.1, ?_⟩
      obtain ⟨m, hm, -⟩ := GlobalTheory.PlaneLeviExt.levi_existsUnique F E σ B _ _ G.W G₁.W H' a (a + b + 1) _ _ _ _
        (GlobalTheory.AdelicU.cm_conj_conj hT.base.cm) hT.geo.hW hT₁.geo.hW hc.hH' h
      have hmv : m ∈ UAt σ G.W (evFin F B.v₁) :=
        GlobalTheory.JacquetFlagLevi.levi_mem_UAt (GlobalTheory.JacquetFlagLevi.adapted_spans B hc.hH' hT.geo.hW.lat.span_eq_top) hm
          (fun c _ => by simp) (fun c _ => by simp) hh
      have e := hLv 1 h m hm hmv hh ψ hψ.1
      rw [GlobalTheory.ThK.LemF.fac_one, one_smul] at e
      change locOp B.v₁ (om₁' (1, h)) _ ∈ N
      rw [← e]
      refine Submodule.mem_sup_left (Submodule.subset_span ⟨_, ?_, rfl⟩)
      exact GlobalTheory.SoLocW.soLoc_stable hKP F E σ B a (b + 2) G X om om' hT m hmv ψ hψ _ (locOp_mem _ _ _)
        (acts_locOp_om hA hP' h1V hmv hψ.1)
    · rintro _ ⟨g, hg, ψ, hψ, ψ₁, hψ₁, hact, rfl⟩
      refine ⟨sub_mem hψ₁ hψ, ?_⟩
      have e := lin 1 (-1) hψ₁ hψ
      simp only [one_smul, neg_one_smul, ← sub_eq_add_neg] at e
      change locOp B.v₁ (om₁' (1, h)) (ψ₁ - ψ) ∈ N
      rw [e]
      have e1 : ψ₁ = locOp B.v₁ (om₁' (g, 1)) ψ := (locOp_eq hψ hψ₁ hact).symm
      have e2 : locOp B.v₁ (om₁' (1, h)) (locOp B.v₁ (om₁' (g, 1)) ψ) =
          locOp B.v₁ (om₁' (g, 1)) (locOp B.v₁ (om₁' (1, h)) ψ) := by
        rw [← mul (1, h) (g, 1) h1V₁ hh hg h1W₁ ψ hψ, ← mul (g, 1) (1, h) hg h1W₁ h1V₁ hh ψ hψ,
          GlobalTheory.ThK.LemF.prod_comm_one]
      rw [e1, e2]
      refine Submodule.mem_sup_right (Submodule.subset_span ⟨g, hg, _, locOp_mem _ _ _, _, locOp_mem _ _ _,
        acts_locOp_om hA hP₁' hg h1W₁ (locOp_mem _ _ _), rfl⟩)
  have hφP := hNP hφ
  have e := locOp_eq hφP.1 hφ₁ hAct
  rw [← e]
  exact hφP.2

end GlobalTheory.ConeStabLv
