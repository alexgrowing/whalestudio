import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityReal

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

namespace GlobalTheory.SquareAgree

theorem polMatch_onto : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {a a' : ℕ} (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched B G X om om' R Rf → ∀ Φ ∈ algD G.M B.ψ B.emb, ∃ Φ' ∈ algD G.M' B.ψ B.emb, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.PolMatch B G X R Rf Φ Φ' := by
  intro F E _ _ _ _ _ σ a a' B G X om om' R Rf hM Φ hΦ
  classical
  obtain ⟨n, c, g, rfl⟩ := (Submodule.mem_span_set').1 hΦ
  choose f φ hf hφ hfin hg using fun i => (g i).2
  have hfin' : ∀ i, {v | ¬ φ i v = G.M.vac v}.Finite := fun i => Filter.eventually_cofinite.1 (hfin i)
  set T : Finset (Pl F) := X.T ∪ Finset.univ.biUnion (fun i => (hfin' i).toFinset) with hT
  have hout : ∀ i, ∀ v ∉ T, φ i v = G.M.vac v := by
    intro i v hv
    by_contra h
    exact hv (Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, (hfin' i).mem_toFinset.2 h⟩))
  have hreal : ∀ i, ∃ f' ∈ G.M'.Pol B.ψ B.emb, R.p' f' = R.p (c i • f i) := by
    intro i
    have : R.p (c i • f i) ∈ (G.M'.Pol B.ψ B.emb).map R.p' := by rw [hM.real.quot'.onto]; trivial
    obtain ⟨y, hy, e⟩ := Submodule.mem_map.1 this
    exact ⟨y, hy, e⟩
  choose f' hf' hf'eq using hreal
  have hloc : ∀ i v, ∃ y ∈ GlobalTheory.WeilM.SB _, Rf.p' v y = Rf.p v (φ i v) := by
    intro i v
    have : Rf.p v (φ i v) ∈ (GlobalTheory.WeilM.SB _).map (Rf.p' v) := by rw [hM.fin.onto' v]; trivial
    obtain ⟨y, hy, e⟩ := Submodule.mem_map.1 this
    exact ⟨y, hy, e⟩
  choose φ₀ hφ₀ hφ₀eq using hloc
  let φ' : Fin n → ∀ v : Pl F, (Fin a' × Fin (a + a') → Fv F v) → ℂ :=
    fun i v => if v ∈ T then φ₀ i v else G.M'.vac v
  have hvac' : ∀ v, G.M'.vac v ∈ GlobalTheory.WeilM.SB _ := fun v => (hM.triple.geo.hM'.vac v).1
  have hφ'SB : ∀ i v, φ' i v ∈ GlobalTheory.WeilM.SB _ := by
    intro i v
    by_cases hv : v ∈ T
    · simp only [φ', if_pos hv]; exact hφ₀ i v
    · simp only [φ', if_neg hv]; exact hvac' v
  have hφ'out : ∀ i, ∀ v ∉ T, φ' i v = G.M'.vac v := by
    intro i v hv; simp only [φ', if_neg hv]
  have hpure : ∀ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (c i • f i) (φ i) = c i • (g i : (Fin a × Fin (a + a') → AF F) → ℂ) := by
    intro i
    rw [hg i]
    funext x
    simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, mul_assoc]
  refine ⟨∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f' i) (φ' i), ?_, T, Finset.subset_union_left, n, n, fun i => c i • f i, φ, f', φ', ?_, ?_, ?_, rfl, ?_⟩
  · refine Submodule.sum_mem _ fun i _ => Submodule.subset_span ⟨f' i, φ' i, hf' i, hφ'SB i, ?_, rfl⟩
    exact Filter.eventually_cofinite.2 (T.finite_toSet.subset fun v hv => by
      by_contra h; exact hv (hφ'out i v h))
  · exact fun i => ⟨Submodule.smul_mem _ _ (hf i), hφ i, hout i⟩
  · exact fun i => ⟨hf' i, hφ'SB i, hφ'out i⟩
  · exact Finset.sum_congr rfl fun i _ => (hpure i).symm
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [hf'eq i]
    congr 2
    funext v
    simp only [φ', if_pos v.2]
    exact (hφ₀eq i v).symm

end GlobalTheory.SquareAgree
