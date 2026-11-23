import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaSubSelf
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityReal
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HypothesesAbsDet
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PolMatchLinear
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SumPureMemAlgD
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolActs
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRealmapsIsomorphism
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialDatumActionOfPairStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerSkewPlaneUniqueDual
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFinPartNeZero

open NumberField IsDedekindDomain
open scoped TensorProduct

namespace GlobalTheory.PolKerLieV

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

local notation "pureT" => GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure

theorem exists_decomp {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {n d : ℕ} {Y : Spc F E n} {Wd : Spc F E d} (M : Model σ Y Wd)
    (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) ℂ) (emb : (w : InfinitePlace F) → GlobalTheory.AdelicU.EmbOver E w)
    {Φ : (Fin n × Fin d → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) → ℂ} (hΦ : Φ ∈ GlobalTheory.SquareAgree.algD M ψ emb) :
    ∃ (T : Finset (Pl F)) (m : ℕ) (f : Fin m → SInf F (Fin n × Fin d))
      (φ : Fin m → (v : Pl F) → (Fin n × Fin d → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) → ℂ),
      (∀ i, f i ∈ M.Pol ψ emb ∧ (∀ v, φ i v ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v)) ∧
        ∀ v ∉ T, φ i v = M.vac v) ∧ Φ = ∑ i, pureT (f i) (φ i) := by
  classical
  unfold GlobalTheory.SquareAgree.algD at hΦ
  induction hΦ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, φ, hf, hφ, hv, rfl⟩ := hx
    have hfin := Filter.eventually_cofinite.1 hv
    refine ⟨hfin.toFinset, 1, fun _ => f, fun _ => φ, fun _ => ⟨hf, hφ, fun v hvT => ?_⟩, by simp⟩
    by_contra h
    exact hvT (hfin.mem_toFinset.2 h)
  | zero =>
    exact ⟨∅, 0, Fin.elim0, Fin.elim0, fun i => i.elim0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨T₁, m₁, f₁, φ₁, h₁, rfl⟩ := hx
    obtain ⟨T₂, m₂, f₂, φ₂, h₂, rfl⟩ := hy
    refine ⟨T₁ ∪ T₂, m₁ + m₂, Fin.append f₁ f₂, Fin.append φ₁ φ₂, fun i => ?_, ?_⟩
    · refine Fin.addCases (fun i => ?_) (fun i => ?_) i
      · simp only [Fin.append_left]
        exact ⟨(h₁ i).1, (h₁ i).2.1, fun v hv => (h₁ i).2.2 v (fun h => hv (Finset.mem_union_left _ h))⟩
      · simp only [Fin.append_right]
        exact ⟨(h₂ i).1, (h₂ i).2.1, fun v hv => (h₂ i).2.2 v (fun h => hv (Finset.mem_union_right _ h))⟩
    · rw [Fin.sum_univ_add]
      simp [Fin.append_left, Fin.append_right]
  | smul c x _ hx =>
    obtain ⟨T, m, f, φ, h, rfl⟩ := hx
    refine ⟨T, m, fun i => c • f i, φ, fun i => ⟨(M.Pol ψ emb).smul_mem c (h i).1, (h i).2⟩, ?_⟩
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    funext x
    simp only [Pi.smul_apply, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, SchwartzMap.smul_apply, smul_eq_mul, mul_assoc]

theorem polZero_deriv_V : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a')
    (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs G Xc om om' R Rf → ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ G.V, ∀ Φ ∈ GlobalTheory.SquareAgree.algD G.M Bs.ψ Bs.emb, ∀ Φ₁,
    (∀ x, HasDerivAt (fun t : ℝ => om (γ (Multiplicative.ofAdd t), 1) Φ x) (Φ₁ x) 0) → GlobalTheory.PolKer.PolZero Bs G Xc R Rf (Φ₁) := by
  intro hP F E _ _ _ _ _ σ Bs a a' G Xc om om' R Rf hM γ hγ Φ hΦ Φ₁ hd
  classical
  obtain ⟨T, m, f, φ, hfφ, rfl⟩ := exists_decomp G.M Bs.ψ Bs.emb hΦ
  obtain ⟨D, hDmem, hD⟩ := (GlobalTheory.T.polynomial_datum_action_of_pair hP F E σ Bs _ _ G.V G.W G.M _ _ om _ _ _ _
    (GlobalTheory.ThK.RealUniq.isPair_V hM.triple)).1 γ hγ
  have hstd := hM.triple.geo.hM.std
  have hacts : ∀ i, ActsD (evI F) (fun t => ⇑(om (γ (Multiplicative.ofAdd t), 1))) ⇑(f i) ⇑(D (f i)) :=
    fun i => (hD (f i) (hfφ i).1 (D (f i))).2 rfl
  have hrest : ∀ i, Rest (evI F) ⇑(f i) (GlobalTheory.EvZeroInf.finPart (φ i)) := by
    intro i
    refine GlobalTheory.ThK.EvUniqInf.rest_pure (f i) (φ i) (hfφ i).2.1 ?_
    filter_upwards [hstd, (Filter.eventually_cofinite.2 (by simpa using T.finite_toSet) : ∀ᶠ v in Filter.cofinite, v ∉ T)] with v hv hvT
    rw [(hfφ i).2.2 v hvT, hv]
  have hpure : ∀ i x, HasDerivAt (fun t : ℝ => om (γ (Multiplicative.ofAdd t), 1) (pureT (f i) (φ i)) x)
      (pureT (D (f i)) (φ i) x) 0 := by
    intro i x
    rw [GlobalTheory.EvZeroInf.pure_eq_tens, GlobalTheory.EvZeroInf.pure_eq_tens]
    exact hacts i _ (hrest i) x
  have hsum : ∀ x, HasDerivAt (fun t : ℝ => om (γ (Multiplicative.ofAdd t), 1) (∑ i, pureT (f i) (φ i)) x)
      (∑ i, pureT (D (f i)) (φ i) x) 0 := by
    intro x
    refine (HasDerivAt.sum (u := Finset.univ) (fun i _ => hpure i x)).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun t => ?_)
    simp [map_sum, Finset.sum_apply]
  have hΦ₁ : Φ₁ = ∑ i, pureT (D (f i)) (φ i) := by
    funext x
    rw [Finset.sum_apply]
    exact (hd x).unique (hsum x)
  have hp0 : ∀ i, R.p (D (f i)) = 0 := fun i =>
    hM.real.quot.lie γ hγ (f i) (hfφ i).1 (D (f i)) (hacts i)
  refine ⟨T ∪ Xc.T, Finset.subset_union_right, m, fun i => D (f i), φ, fun i =>
    ⟨hDmem _ (hfφ i).1, (hfφ i).2.1, fun v hv => (hfφ i).2.2 v (fun h => hv (Finset.mem_union_left _ h))⟩,
    hΦ₁, ?_⟩
  simp [hp0]

end GlobalTheory.PolKerLieV
