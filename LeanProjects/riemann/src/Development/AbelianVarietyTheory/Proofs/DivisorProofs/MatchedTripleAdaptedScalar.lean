import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMaxThOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalPolynomialSubmoduleMatchingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaximalThetaFactorizationStatement

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct

namespace GlobalTheory.ThetaKillFin

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {B : Base F E} {a a' : ℕ} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W}
  {Rf : FinMaps F a a'}

theorem ker_maximal (hf : IsFinMaps B G X om om' Rf) (v : Pl F) :
    Maximal (fun Q => GlobalTheory.Published.ThetaSub om v Q ∧ Q ≠ SB _) (LinearMap.ker (Rf.p v) ⊓ SB _) := by
  have hsub : GlobalTheory.Published.ThetaSub om v (LinearMap.ker (Rf.p v) ⊓ SB _) := by
    refine ⟨le_inf (hf.inv v) ?_, inf_le_right, ?_⟩
    · rw [augAt, Submodule.span_le]
      rintro _ ⟨g, -, φ, hφ, φ₁, hφ₁, -, rfl⟩
      exact Submodule.sub_mem _ hφ₁ hφ
    · intro h hh φ hφ φ₁ hφ₁ hA
      obtain ⟨hφk, hφs⟩ := Submodule.mem_inf.1 hφ
      refine Submodule.mem_inf.2 ⟨?_, hφ₁⟩
      have h0 : Acts (evFin F v) (om' (1, h)) (0 : (Fin a' × Fin (a + a') → Fv F v) → ℂ) 0 := by
        intro r _
        have e : tens (evFin F v) (0 : (Fin a' × Fin (a + a') → Fv F v) → ℂ) r = 0 := by
          funext x; simp [tens]
        rw [e, map_zero]
      have := hf.equiv v h hh φ hφs 0 (Submodule.zero_mem _) φ₁ hφ₁ 0 (Submodule.zero_mem _) hA h0
        (by rw [map_zero]; exact LinearMap.mem_ker.1 hφk)
      rw [LinearMap.mem_ker, this, map_zero]
  refine ⟨⟨hsub, fun hK => ?_⟩, fun P hP hKP => ?_⟩
  · haveI := hf.nontriv v
    obtain ⟨y, hy⟩ := exists_ne (0 : Rf.Pi v)
    have hy' : y ∈ (SB _).map (Rf.p v) := by rw [hf.onto v]; trivial
    obtain ⟨φ, hφ, rfl⟩ := hy'
    have : φ ∈ LinearMap.ker (Rf.p v) ⊓ SB _ := by rw [hK]; exact hφ
    exact hy (LinearMap.mem_ker.1 (Submodule.mem_inf.1 this).1)
  · obtain ⟨hP, hPne⟩ := hP
    have key : ∀ φ ∈ SB _, Rf.p v φ ∈ P.map (Rf.p v) → φ ∈ P := by
      intro φ hφ hm
      obtain ⟨ψ, hψ, he⟩ := hm
      have hd : φ - ψ ∈ LinearMap.ker (Rf.p v) ⊓ SB _ :=
        Submodule.mem_inf.2 ⟨by rw [LinearMap.mem_ker, map_sub, he, sub_self],
          Submodule.sub_mem _ hφ (hP.2.1 hψ)⟩
      simpa using P.add_mem (hKP hd) hψ
    rcases hf.irred v (P.map (Rf.p v)) (fun h hh φ hφ φ₁ hφ₁ hA hm =>
        ⟨φ₁, hP.2.2 h hh φ (key φ hφ hm) φ₁ hφ₁ hA, rfl⟩) with h0 | h1
    · intro φ hφ
      refine Submodule.mem_inf.2 ⟨?_, hP.2.1 hφ⟩
      have : Rf.p v φ ∈ P.map (Rf.p v) := ⟨φ, hφ, rfl⟩
      rw [h0] at this
      exact LinearMap.mem_ker.2 ((Submodule.mem_bot ℂ).1 this)
    · exact absurd (le_antisymm hP.2.1 fun φ hφ => key φ hφ (by rw [h1]; trivial)) hPne

theorem killFin : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched B G X om om' R Rf → ∀ N, GlobalTheory.ThetaFac.IsMaxTh B om (GlobalTheory.ThK.PolData B G.M) N → (∀ Ψ ∈ GlobalTheory.ThK.PolData B G.M, G.M.I om Ψ = 0 → Ψ ∈ N) → ∀ (f : SInf F (Fin a × Fin (a + a'))) (φ : ∀ v : Pl F, (Fin a × Fin (a + a') → Fv F v) → ℂ), f ∈ G.M.Pol B.ψ B.emb → (∀ v, φ v ∈ SB _) → (∀ᶠ v in Filter.cofinite, φ v = G.M.vac v) → ∀ v, Rf.p v (φ v) = 0 → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ ∈ N := by
  intro hKP F E _ _ _ _ _ σ B a a' G X om om' R Rf hm N hN hI f φ hf hφ hφc v hv
  by_contra hn
  obtain ⟨P, hPm, hPv⟩ := GlobalTheory.T.maximal_theta_factorization hKP F E σ B a a' G X om om' hm.triple N hN hI f φ hf hφ hφc hn v
  have e := GlobalTheory.T.maximal_proper_thetaSub_unique hKP F E σ B a a' G X om om' hm.triple v P _ hPm (ker_maximal hm.fin v)
  rw [e] at hPv
  exact hPv (Submodule.mem_inf.2 ⟨LinearMap.mem_ker.2 hv, hφ v⟩)

end GlobalTheory.ThetaKillFin
