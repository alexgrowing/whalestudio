import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMaxThOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedTripleAdaptedScalarStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedTripleAdaptedFactorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMultilinearFactorizationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultilinearQuotientFactorizationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumMultilinearVacuumOutsideStatement

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct

namespace GlobalTheory.ThetaFacIrr

theorem thetaKer_le : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched B G X om om' R Rf → ∀ N, GlobalTheory.ThetaFac.IsMaxTh B om (GlobalTheory.ThK.PolData B G.M) N → (∀ Ψ ∈ GlobalTheory.ThK.PolData B G.M, G.M.I om Ψ = 0 → Ψ ∈ N) → ∀ Φ, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.PolMatch B G X R Rf Φ 0 → Φ ∈ N := by
  intro hKP F E _ _ _ _ _ σ B a a' G X om om' R Rf hm N hN hI Φ hPM
  classical
  obtain ⟨T, -, m, m', f, φ, f', φ', hi, hj, hΦ, h0, heq⟩ := hPM
  have hz := GlobalTheory.T.sum_multilinear_vacuum_outside F E σ a' (a + a') G.V' G.W G.M' B.ψ hm.triple.geo.hM' T m' f' φ'
    (fun j v hv => (hj j).2.2 v hv) h0.symm R.Pi Rf.Pi R.p' (fun v => Rf.p' v)
  rw [hz] at heq
  obtain ⟨Ψ, hΨ⟩ := GlobalTheory.T.exists_multilinear_factorization F E σ a (a + a') G.V G.W G.M B.ψ hm.triple.geo.hM T
  have hvac : ∀ v, G.M.vac v ∈ SB _ := fun v => (hm.triple.geo.hM.vac v).1
  have hext : ∀ s : ∀ v : T, (Fin a × Fin (a + a') → Fv F v) → ℂ, (∀ i, s i ∈ SB _) →
      (∀ v, (if h : v ∈ T then s ⟨v, h⟩ else G.M.vac v) ∈ SB _) ∧
      (∀ᶠ v in Filter.cofinite, (if h : v ∈ T then s ⟨v, h⟩ else G.M.vac v) = G.M.vac v) := by
    intro s hs
    refine ⟨fun v => ?_, Filter.eventually_cofinite.2 ((T.finite_toSet).subset fun v hv => ?_)⟩
    · split_ifs with h
      · exact hs _
      · exact hvac v
    · by_contra h
      exact hv (dif_neg (by simpa using h))
  have hk1 : ∀ x ∈ G.M.Pol B.ψ B.emb, ∀ s : ∀ v : T, (Fin a × Fin (a + a') → Fv F v) → ℂ,
      (∀ i, s i ∈ SB _) → R.p x = 0 → Ψ x s ∈ N := by
    intro x hx s hs hp
    rw [hΨ]
    exact GlobalTheory.T.matched_triple_adapted_factor hKP F E σ B a a' G X om om' R Rf hm N hN hI _ _ hx (hext s hs).1 (hext s hs).2 hp
  have hk2 : ∀ x ∈ G.M.Pol B.ψ B.emb, ∀ s : ∀ v : T, (Fin a × Fin (a + a') → Fv F v) → ℂ,
      (∀ i, s i ∈ SB _) → ∀ i : T, Rf.p i (s i) = 0 → Ψ x s ∈ N := by
    intro x hx s hs i hp
    rw [hΨ]
    refine GlobalTheory.T.matched_triple_adapted_scalar hKP F E σ B a a' G X om om' R Rf hm N hN hI _ _ hx (hext s hs).1 (hext s hs).2 i ?_
    simpa using hp
  have key := GlobalTheory.T.multilinear_quotient_factorization T (SInf F (Fin a × Fin (a + a'))) R.Pi ((Fin a × Fin (a + a') → AF F) → ℂ)
    (fun v : T => (Fin a × Fin (a + a') → Fv F v) → ℂ) (fun v : T => Rf.Pi v) (G.M.Pol B.ψ B.emb)
    (fun v => SB _) N R.p (fun v => Rf.p v) Ψ hm.real.quot.onto (fun v => hm.fin.onto v) hk1 hk2 m f
    (fun k v => φ k v) (fun k => ⟨(hi k).1, fun v => (hi k).2.1 v⟩) heq
  rw [hΦ]
  convert key using 2 with k
  rw [hΨ]
  congr 1
  funext v
  split_ifs with h
  · rfl
  · exact ((hi k).2.2 v h)

end GlobalTheory.ThetaFacIrr
