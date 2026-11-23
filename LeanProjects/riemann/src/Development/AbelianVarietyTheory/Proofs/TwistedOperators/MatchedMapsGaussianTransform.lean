import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaSubSelf
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityReal
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HypothesesAbsDet
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AlgAtLeAlgD
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RelInf

import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RankSchwartzBruhatAdicCompletionPiLeAleph0
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRealmapsIsomorphism

open NumberField IsDedekindDomain
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.HoweGlobal.FinPlace

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem one_mem_UAt {n : ℕ} (X : Spc F E n) {R : Type} [Zero R] (ev : AF F → R) : (1 : UA σ X.J) ∈ UAt σ X ev := by
  intro u _
  have e : mat (1 : UA σ X.J) = 1 := rfl
  show u • (mat (1 : UA σ X.J) - 1) = 0
  rw [e, sub_self, smul_zero]

variable {Bs : Base F E} {a a' : ℕ} {G : Geo σ a a'} {Xc : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W}

theorem exists_image (hT : IsTriple Bs G Xc om om') (v : Pl F) {h : UA σ G.W.J} (hh : h ∈ UAt σ G.W (evFin F v))
    (φ : (Fin a × Fin (a + a') → Fv F v) → ℂ) (hφ : φ ∈ SB (Fin a × Fin (a + a') → Fv F v)) :
    ∃ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v), Acts (evFin F v) (om (1, h)) φ φ₁ :=
  GlobalTheory.ThK.LocalOps.acts_exists (GlobalTheory.ThK.RealUniq.isPair_V hT) v (1, h) (one_mem_UAt _ _) hh φ hφ

def locOp (hT : IsTriple Bs G Xc om om') (v : Pl F) {h : UA σ G.W.J} (hh : h ∈ UAt σ G.W (evFin F v)) :
    Module.End ℂ ↥(SB (Fin a × Fin (a + a') → Fv F v)) where
  toFun φ := ⟨Classical.choose (exists_image hT v hh φ φ.2), (Classical.choose_spec (exists_image hT v hh φ φ.2)).1⟩
  map_add' φ ψ := by
    apply Subtype.ext
    have hφ := (Classical.choose_spec (exists_image hT v hh φ φ.2)).2
    have hψ := (Classical.choose_spec (exists_image hT v hh ψ ψ.2)).2
    have hs := (Classical.choose_spec (exists_image hT v hh (φ + ψ : ↥(SB _)) (φ + ψ).2)).2
    have hl := GlobalTheory.ThK.LocalOps.acts_lin v (om (1, h)) (fun χ hχ => exists_image hT v hh χ hχ) φ.2 ψ.2 hφ hψ 1 1
    simp only [one_smul] at hl
    exact GlobalTheory.ThK.LocalOps.acts_unique v _ (φ + ψ).2 hs hl
  map_smul' c φ := by
    apply Subtype.ext
    have hφ := (Classical.choose_spec (exists_image hT v hh φ φ.2)).2
    have hs := (Classical.choose_spec (exists_image hT v hh (c • φ : ↥(SB _)) (c • φ).2)).2
    have hl := GlobalTheory.ThK.LocalOps.acts_lin v (om (1, h)) (fun χ hχ => exists_image hT v hh χ hχ) φ.2 φ.2 hφ hφ c 0
    simp only [zero_smul, add_zero] at hl
    exact GlobalTheory.ThK.LocalOps.acts_unique v _ (c • φ).2 hs hl

theorem locOp_acts (hT : IsTriple Bs G Xc om om') (v : Pl F) {h : UA σ G.W.J} (hh : h ∈ UAt σ G.W (evFin F v))
    (φ : ↥(SB (Fin a × Fin (a + a') → Fv F v))) :
    Acts (evFin F v) (om (1, h)) (φ : (Fin a × Fin (a + a') → Fv F v) → ℂ)
      ((locOp hT v hh φ : ↥(SB (Fin a × Fin (a + a') → Fv F v))) : (Fin a × Fin (a + a') → Fv F v) → ℂ) :=
  (Classical.choose_spec (exists_image hT v hh φ φ.2)).2

theorem locOp_mem (hT : IsTriple Bs G Xc om om') (v : Pl F) {h : UA σ G.W.J} (hh : h ∈ UAt σ G.W (evFin F v)) :
    locOp hT v hh ∈ GlobalTheory.HoweGlobal.opFin G om v :=
  ⟨h, hh, locOp_acts hT v hh⟩

theorem augAt_le_SB (v : Pl F) : augAt om v ≤ SB (Fin a × Fin (a + a') → Fv F v) := by
  refine Submodule.span_le.2 ?_
  rintro z ⟨g, -, φ, hφ, φ₁, hφ₁, -, rfl⟩
  exact sub_mem hφ₁ hφ

theorem thetaSub_map (hT : IsTriple Bs G Xc om om') (v : Pl F) (N : Submodule ℂ ↥(SB (Fin a × Fin (a + a') → Fv F v)))
    (hrel : GlobalTheory.HoweGlobal.relFin G om v ≤ N) (hst : ∀ g ∈ GlobalTheory.HoweGlobal.opFin G om v, ∀ x ∈ N, g x ∈ N) :
    GlobalTheory.Published.ThetaSub om v (N.map (SB (Fin a × Fin (a + a') → Fv F v)).subtype) := by
  refine ⟨?_, Submodule.map_subtype_le _ _, ?_⟩
  · intro z hz
    exact ⟨⟨z, augAt_le_SB v hz⟩, hrel hz, rfl⟩
  · rintro h hh φ ⟨x, hx, rfl⟩ φ₁ hφ₁ hA
    have e := GlobalTheory.ThK.LocalOps.acts_unique v _ x.2 hA (locOp_acts hT v hh x)
    exact ⟨locOp hT v hh x, hst _ (locOp_mem hT v hh) x hx, e.symm⟩

end GlobalTheory.HoweGlobal.FinPlace

open GlobalTheory.HoweGlobal.FinPlace in

theorem GlobalTheory.HoweGlobal.fin_place_howe : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W)
    (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs G Xc om om' R Rf →
    (∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (∃ L : ℕ, ∀ (m : ℕ) (N : Fin m → Submodule ℂ ((Fin a × Fin (a + a') → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) → ℂ)),
        StrictMono N → (∀ i, GlobalTheory.Published.ThetaSub om v (N i)) → m ≤ L) ∧
      ∀ N : Submodule ℂ ((Fin a × Fin (a + a') → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) → ℂ), GlobalTheory.Published.ThetaSub om v N →
        N ≠ GlobalTheory.WeilM.SB _ → ∀ φ ∈ N, Rf.p v φ = 0) →
    ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F,
    Module.rank ℂ ↥(GlobalTheory.WeilM.SB (Fin a × Fin (a + a') → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v)) ≤ Cardinal.aleph0 ∧
    (∃ L : ℕ, ∀ (m : ℕ) (N : Fin m → Submodule ℂ ↥(GlobalTheory.WeilM.SB (Fin a × Fin (a + a') → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v))), StrictMono N →
        (∀ j, GlobalTheory.HoweGlobal.relFin G om v ≤ N j ∧ ∀ g ∈ GlobalTheory.HoweGlobal.opFin G om v, ∀ x ∈ N j, g x ∈ N j) → m ≤ L) ∧
    (∀ N : Submodule ℂ ↥(GlobalTheory.WeilM.SB (Fin a × Fin (a + a') → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v)), GlobalTheory.HoweGlobal.relFin G om v ≤ N →
        (∀ g ∈ GlobalTheory.HoweGlobal.opFin G om v, ∀ x ∈ N, g x ∈ N) → N ≠ ⊤ → N ≤ LinearMap.ker (Rf.p v ∘ₗ (GlobalTheory.WeilM.SB (Fin a × Fin (a + a') → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v)).subtype)) ∧
    GlobalTheory.HoweGlobal.relFin G om v ≤ LinearMap.ker (Rf.p v ∘ₗ (GlobalTheory.WeilM.SB (Fin a × Fin (a + a') → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v)).subtype) ∧
    ∀ g ∈ GlobalTheory.HoweGlobal.opFin G om v, ∀ x ∈ LinearMap.ker (Rf.p v ∘ₗ (GlobalTheory.WeilM.SB (Fin a × Fin (a + a') → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v)).subtype), g x ∈ LinearMap.ker (Rf.p v ∘ₗ (GlobalTheory.WeilM.SB (Fin a × Fin (a + a') → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v)).subtype) := by
  intro F E _ _ _ _ _ σ Bs a a' G Xc om om' R Rf hM hfin v
  obtain ⟨⟨L, hL⟩, hker⟩ := hfin v
  have hT := hM.triple
  refine ⟨GlobalTheory.TripleAssembly.rank_SB_adicCompletion_le F _ v, ⟨L, fun m N hN hc => ?_⟩, ?_, ?_, ?_⟩
  · exact hL m (fun j => (N j).map (GlobalTheory.WeilM.SB _).subtype)
      ((Submodule.map_strictMono_of_injective (GlobalTheory.WeilM.SB _).injective_subtype).comp hN)
      (fun j => thetaSub_map hT v _ (hc j).1 (hc j).2)
  · intro N hrel hst hne x hx
    have hne' : N.map (GlobalTheory.WeilM.SB (Fin a × Fin (a + a') → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v)).subtype ≠ GlobalTheory.WeilM.SB _ := by
      intro heq
      apply hne
      apply Submodule.map_injective_of_injective (GlobalTheory.WeilM.SB _).injective_subtype
      rw [heq, Submodule.map_top, Submodule.range_subtype]
    exact hker _ (thetaSub_map hT v N hrel hst) hne' x ⟨x, hx, rfl⟩
  · intro x hx
    exact hM.fin.inv v hx
  · rintro g ⟨h, hh, hg⟩ x hx
    have hx' : Rf.p v (x : (Fin a × Fin (a + a') → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) → ℂ) = 0 := hx
    have h0 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.AdelicU.evFin F v) (om' (1, h))
        (0 : (Fin a' × Fin (a + a') → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) → ℂ) 0 := by
      intro r _
      have ht : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.AdelicU.evFin F v)
          (0 : (Fin a' × Fin (a + a') → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) → ℂ) r = 0 := by
        funext y; simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens]
      rw [ht, map_zero]
    have e := hM.fin.equiv v h hh x x.2 0 (zero_mem _) (g x) (g x).2 0 (zero_mem _) (hg x) h0
      (by rw [hx', map_zero])
    show Rf.p v ((g x : GlobalTheory.WeilM.SB _) : (Fin a × Fin (a + a') → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) → ℂ) = 0
    rw [e, map_zero]
