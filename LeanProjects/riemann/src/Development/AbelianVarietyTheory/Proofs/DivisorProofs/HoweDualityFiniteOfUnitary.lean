import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HypothesesAbsDet
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocSubSB
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChainBoundedAndSupProper
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalHom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HoweDualityForClosure

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.Published
open scoped TensorProduct

open GlobalTheory.HoweAdelic in
theorem _root_.GlobalTheory.T.howe_duality_finite_of_unitary : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.Published.HoweDualityUnitary → GlobalTheory.Published.HoweDualityFinite := by
  intro hP hH F E _ _ _ _ _ σ hcm n d X W M ψ χX χW om hψ hX hXd hW hWd hrX hrW hhX hhW hwe v hv
  have memX : ∀ g, g ∈ Subgroup.closure (UAt σ X (evFin F v)) ↔ g ∈ UAt σ X (evFin F v) := fun g =>
    ⟨fun hg => (mem_UAtGrp σ X _ g).1 ((Subgroup.closure_le (K := UAtGrp σ X (evFin F v))).2
      (fun x hx => (mem_UAtGrp σ X _ x).2 hx) hg), fun hg => Subgroup.subset_closure hg⟩
  have memW : ∀ h, h ∈ Subgroup.closure (UAt σ W (evFin F v)) ↔ h ∈ UAt σ W (evFin F v) := fun h =>
    ⟨fun hh => (mem_UAtGrp σ W _ h).1 ((Subgroup.closure_le (K := UAtGrp σ W (evFin F v))).2
      (fun x hx => (mem_UAtGrp σ W _ x).2 hx) hh), fun hh => Subgroup.subset_closure hh⟩
  obtain ⟨om', hact⟩ := GlobalTheory.ThK.LocalHom.exists_localHom F E σ n d X W M ψ χX χW om hψ hwe v
  have hHD := GlobalTheory.HoweLocal.howeDualityFor_closure hP hH F E σ hcm n d X W M ψ χX χW om hψ hX hXd hW hWd hrX hrW hhX hhW
    hwe v hv om' hact
  have hpres : ∀ x, ∀ φ ∈ SB (Fin n × Fin d → Fv F v), om' x φ ∈ SB _ := fun x φ hφ => (hact x.1 x.2 φ hφ).1
  obtain ⟨⟨L, hL⟩, hsum⟩ := GlobalTheory.HoweTrivial.chain_bounded_and_sup_proper om' hHD hpres
  have uniq : ∀ (T : ((Fin n × Fin d → AF F) → ℂ) → (Fin n × Fin d → AF F) → ℂ) (φ φ₁ φ₂ : (Fin n × Fin d → Fv F v) → ℂ),
      φ ∈ SB _ → Acts (evFin F v) T φ φ₁ → Acts (evFin F v) T φ φ₂ → φ₁ = φ₂ := fun T φ φ₁ φ₂ hφ h1 h2 =>
    GlobalTheory.TensUniq.eq_of_tens_eq v φ φ₁ φ₂ hφ fun r hr => (h1 r hr).symm.trans (h2 r hr)
  have haug : augAt om v = locAug om' := by
    apply le_antisymm
    · refine Submodule.span_le.2 ?_
      rintro z ⟨g, hg, φ, hφ, φ₁, hφ₁, hA, rfl⟩
      have h2 := (hact ⟨g, (memX g).2 hg⟩ 1 φ hφ).2
      rw [show ((1 : Subgroup.closure (UAt σ W (evFin F v))) : UA σ W.J) = 1 from rfl] at h2
      rw [uniq _ φ φ₁ _ hφ hA h2]
      exact Submodule.subset_span ⟨⟨g, (memX g).2 hg⟩, φ, hφ, rfl⟩
    · refine Submodule.span_le.2 ?_
      rintro z ⟨g, φ, hφ, rfl⟩
      have h2 := hact g 1 φ hφ
      exact Submodule.subset_span ⟨g.1, (memX _).1 g.2, φ, hφ, _, h2.1, h2.2, rfl⟩
  have hsub : ∀ N, ThetaSub om v N ↔ IsLocSub om' N := by
    intro N
    refine ⟨fun ⟨h1, h2, h3⟩ => ⟨haug ▸ h1, h2, fun h φ hφ => ?_⟩, fun ⟨h1, h2, h3⟩ => ⟨haug ▸ h1, h2, ?_⟩⟩
    · have h4 := hact 1 h φ (h2 hφ)
      exact h3 h.1 ((memW _).1 h.2) φ hφ _ h4.1 h4.2
    · intro h hh φ hφ φ₁ hφ₁ hA
      have h4 := hact 1 ⟨h, (memW h).2 hh⟩ φ (h2 hφ)
      rw [uniq _ φ φ₁ _ (h2 hφ) hA h4.2]
      exact h3 ⟨h, (memW h).2 hh⟩ φ hφ
  refine ⟨⟨L, fun m N hN hT => hL m N hN fun i => (hsub _).1 (hT i)⟩, fun N N' h h' hN hN' => ?_⟩
  exact hsum N N' ((hsub N).1 h) ((hsub N').1 h') hN hN'
