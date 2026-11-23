import Mathlib
import Development.AutomorphicArithmetic.ThetaCorrespondence.HoweDuality.FactorApply
import Development.WeilBound.ThetaLifts.SphericalLattices.ThetaSubSup
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RelInfAlt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatchedMapsGaussianTransform
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatchedMapsOrbitKernel
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatchedMapsGaussianIdentity

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open UpperTheory.Lit.HoweDuality GlobalTheory.HoweGlobalPair

theorem UpperTheory.Lit.HoweDuality.kerVp :
    ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {Bs : Base F E} {a a' : ℕ} {G : Geo σ a a'} {Xc : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W} {R : RealMaps F a a'} {Rf : FinMaps F a a'}, IsMatched Bs G Xc om om' R Rf → ∀ v : Pl F, relFin om' v ≤ LinearMap.ker (Rf.p' v ∘ₗ (SB (Fin a' × Fin (a + a') → Fv F v)).subtype) ∧ Stable (opFin om' v) (LinearMap.ker (Rf.p' v ∘ₗ (SB (Fin a' × Fin (a + a') → Fv F v)).subtype)) ∧ LinearMap.ker (Rf.p' v ∘ₗ (SB (Fin a' × Fin (a + a') → Fv F v)).subtype) ≠ ⊤ ∧ ∀ N : Submodule ℂ ↥(SB (Fin a' × Fin (a + a') → Fv F v)), LinearMap.ker (Rf.p' v ∘ₗ (SB (Fin a' × Fin (a + a') → Fv F v)).subtype) ≤ N → Stable (opFin om' v) N → N ≠ ⊤ → N ≤ LinearMap.ker (Rf.p' v ∘ₗ (SB (Fin a' × Fin (a + a') → Fv F v)).subtype) := by
  intro F E _ _ _ _ _ σ Bs a a' G Xc om om' R Rf hM v
  have hz : ∀ (h : UA σ G.W.J), Acts (evFin F v) (om (1, h))
      (0 : (Fin a × Fin (a + a') → Fv F v) → ℂ) 0 := by
    intro h r _
    have h0 : tens (evFin F v) (0 : (Fin a × Fin (a + a') → Fv F v) → ℂ) r = 0 := by
      funext x
      simp [tens]
    rw [h0, map_zero]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx
    rw [LinearMap.mem_ker, LinearMap.comp_apply]
    exact hM.fin.inv' v hx
  · rintro g ⟨h, hh, hg⟩ x hx
    rw [LinearMap.mem_ker, LinearMap.comp_apply] at hx ⊢
    have e := hM.fin.equiv v h hh 0 (Submodule.zero_mem _) x x.2 0 (Submodule.zero_mem _)
      (g x) (g x).2 (hz h) (hg x) (by rw [map_zero]; exact hx.symm)
    rw [map_zero] at e
    exact e.symm
  · intro hK
    haveI := hM.fin.nontriv v
    obtain ⟨y, hy⟩ := exists_ne (0 : Rf.Pi v)
    have hmem : y ∈ Submodule.map (Rf.p' v) (SB (Fin a' × Fin (a + a') → Fv F v)) := by
      rw [hM.fin.onto' v]
      exact Submodule.mem_top
    obtain ⟨φ, hφ, rfl⟩ := hmem
    have hk : (⟨φ, hφ⟩ : SB (Fin a' × Fin (a + a') → Fv F v)) ∈
        LinearMap.ker (Rf.p' v ∘ₗ (SB (Fin a' × Fin (a + a') → Fv F v)).subtype) := by
      rw [hK]
      exact Submodule.mem_top
    rw [LinearMap.mem_ker, LinearMap.comp_apply] at hk
    exact hy hk
  · intro N hKN hN hNtop
    have hst : ∀ h ∈ UAt σ G.W (evFin F v),
        ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v),
          ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v),
            Acts (evFin F v) (om (1, h)) φ φ₁ →
              Rf.p v φ ∈ Submodule.map (Rf.p' v) (Submodule.map (SB (Fin a' × Fin (a + a') → Fv F v)).subtype N) →
              Rf.p v φ₁ ∈ Submodule.map (Rf.p' v) (Submodule.map (SB (Fin a' × Fin (a + a') → Fv F v)).subtype N) := by
      intro h hh φ hφ φ₁ hφ₁ hact hp
      obtain ⟨y, ⟨n, hn, rfl⟩, hpn⟩ := hp
      have hgn := hN _ (GlobalTheory.HoweGlobalPair.FinPlaceSmall.locOp_mem hM.triple v hh) n hn
      have e := hM.fin.equiv v h hh φ hφ n n.2 φ₁ hφ₁ _ (GlobalTheory.HoweGlobalPair.FinPlaceSmall.locOp hM.triple v hh n).2
        hact (GlobalTheory.HoweGlobalPair.FinPlaceSmall.locOp_acts hM.triple v hh n) hpn.symm
      exact ⟨_, ⟨_, hgn, rfl⟩, e.symm⟩
    rcases hM.fin.irred v _ hst with hbot | htop
    · intro x hx
      have hm : Rf.p' v x ∈ Submodule.map (Rf.p' v) (Submodule.map (SB (Fin a' × Fin (a + a') → Fv F v)).subtype N) :=
        ⟨x, ⟨x, hx, rfl⟩, rfl⟩
      rw [hbot, Submodule.mem_bot] at hm
      rw [LinearMap.mem_ker, LinearMap.comp_apply]
      exact hm
    · exfalso
      apply hNtop
      rw [eq_top_iff]
      intro x _
      have hm : Rf.p' v x ∈ Submodule.map (Rf.p' v) (Submodule.map (SB (Fin a' × Fin (a + a') → Fv F v)).subtype N) := by
        rw [htop]
        exact Submodule.mem_top
      obtain ⟨y, ⟨n, hn, rfl⟩, hpn⟩ := hm
      have hk : x - n ∈ N := by
        apply hKN
        rw [LinearMap.mem_ker, LinearMap.comp_apply, map_sub, map_sub, sub_eq_zero]
        exact hpn.symm
      have := N.add_mem hk hn
      rwa [sub_add_cancel] at this
