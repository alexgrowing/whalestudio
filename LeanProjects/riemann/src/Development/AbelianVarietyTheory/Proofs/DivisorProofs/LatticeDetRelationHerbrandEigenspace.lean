import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.QuotientEigenDifference
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.MultiplicationKernelIdentity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HerbrandQuotientEigenDetStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemAddValuationIntegerRingNormalizedIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemFiltrationPreimageIffEvalMemStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemPolynomialEvalFreeLatticeIffExistsEvalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvalQuotientRingVectorAtPointsInjectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenSublatticeFreeLatticeIffEvalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemFiltrationOfComponentsMemEigenSpanStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieEigenSublatticeIffEvalFlatStatement

open scoped NNReal
open GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity

namespace GlobalTheory.HerbrandBridge
open GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference (freeLattice unif IsFiltration filSpace eigenSub eigenQuot lie quotMap addVal)

theorem filPre_mem : ∀ (C : Type) [Field C] (w : Valuation C ℝ≥0) (v : AddValuation C (WithTop ℝ))
    (hv : ∀ x, x ∈ Int0 v ↔ x ∈ w.valuationSubring) (S : Type) [Fintype S] [DecidableEq S]
    (a : S → w.valuationSubring) (N : ℕ) (F : Submodule w.valuationSubring (S → Fin N → C)),
    (∀ x ∈ F, unif a x ∈ F) →
    ∀ x, x ∈ filPre (liftA hv a) F ↔ evalVec (liftA hv a) N x ∈ F :=
  GlobalTheory.T.mem_filtrationPreimage_iff_eval_mem

theorem evalVec_range : ∀ (C : Type) [Field C] (w : Valuation C ℝ≥0) (v : AddValuation C (WithTop ℝ))
    (hv : ∀ x, x ∈ Int0 v ↔ x ∈ w.valuationSubring) (S : Type) [Fintype S] [DecidableEq S]
    (a : S → w.valuationSubring) (N : ℕ) (y : S → Fin N → C),
    y ∈ freeLattice a N ↔ ∃ x, evalVec (liftA hv a) N x = y :=
  GlobalTheory.T.mem_polynomialEvalFreeLattice_iff_exists_eval

theorem evalVec_injective : ∀ (C : Type) [Field C] (w : Valuation C ℝ≥0) (v : AddValuation C (WithTop ℝ))
    (hv : ∀ x, x ∈ Int0 v ↔ x ∈ w.valuationSubring) (S : Type) [Fintype S] [DecidableEq S]
    (a : S → w.valuationSubring) (N : ℕ), Function.Injective a →
    Function.Injective (evalVec (liftA hv a) N) :=
  GlobalTheory.T.evalQuotientRingVectorAtPoints_injective

theorem eigenSub_iff : ∀ (C : Type) [Field C] (w : Valuation C ℝ≥0) (v : AddValuation C (WithTop ℝ))
    (hv : ∀ x, x ∈ Int0 v ↔ x ∈ w.valuationSubring) (S : Type) [Fintype S] [DecidableEq S]
    (a : S → w.valuationSubring) (N : ℕ) (τ : S), Function.Injective a →
    Function.Injective (evalVec (liftA hv a) N) →
    (∀ y, y ∈ freeLattice a N ↔ ∃ x, evalVec (liftA hv a) N x = y) →
    ∀ y : Fin N → C, y ∈ eigenSub (W := fun _ => Fin N → C) (freeLattice a N) τ ↔
      ∃ z ∈ eigSub (liftA hv a) τ (Fin N → RS (liftA hv a)),
        (fun i => ((comp (liftA hv a) N τ z i : Int0 v) : C)) = y :=
  GlobalTheory.T.eigenSublattice_freeLattice_iff_eval

theorem mem_of_components : ∀ (C : Type) [Field C] (w : Valuation C ℝ≥0) (S : Type) [Fintype S]
    [DecidableEq S] (a : S → w.valuationSubring) (N : ℕ)
    (F : Submodule w.valuationSubring (S → Fin N → C)), Function.Injective a → IsFiltration a F →
    ∀ x ∈ freeLattice a N, (∀ s, x s ∈ filSpace F s) → x ∈ F :=
  GlobalTheory.T.mem_filtration_of_components_mem_eigenSpan

theorem lie_iff : ∀ (C : Type) [Field C] (w : Valuation C ℝ≥0) (v : AddValuation C (WithTop ℝ))
    (hv : ∀ x, x ∈ Int0 v ↔ x ∈ w.valuationSubring) (S : Type) [Fintype S] [DecidableEq S]
    (a : S → w.valuationSubring) (N : ℕ) (F : Submodule w.valuationSubring (S → Fin N → C))
    (τ : S), Function.Injective a → IsFiltration a F →
    Function.Injective (evalVec (liftA hv a) N) →
    (∀ y, y ∈ freeLattice a N ↔ ∃ x, evalVec (liftA hv a) N x = y) →
    (∀ x, x ∈ filPre (liftA hv a) F ↔ evalVec (liftA hv a) N x ∈ F) →
    (∀ x ∈ freeLattice a N, (∀ s, x s ∈ filSpace F s) → x ∈ F) →
    ∀ z : (Fin N → C) ⧸ filSpace F τ, z ∈ eigenSub (lie (freeLattice a N) F) τ ↔
      ∃ x : Fin N → RS (liftA hv a),
        proj (liftA hv a) (filPre (liftA hv a) F) x ∈
          eigSub (liftA hv a) τ ((Fin N → RS (liftA hv a)) ⧸ filPre (liftA hv a) F) ∧
        quotMap (w := w) (filSpace F τ) (fun i => ((comp (liftA hv a) N τ x i : Int0 v) : C)) = z :=
  GlobalTheory.T.lieEigenSublattice_iff_eval_flat

end GlobalTheory.HerbrandBridge

namespace GlobalTheory.HerbrandBridge
open GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference (freeLattice unif IsFiltration filSpace eigenSub eigenQuot lie quotMap addVal
  DetRel IsLatticeBasis HasVal)

variable {C : Type} [Field C]

theorem span_eq_of_basis {w : Valuation C ℝ≥0} {v : AddValuation C (WithTop ℝ)}
    (hv : ∀ x, x ∈ Int0 v ↔ x ∈ w.valuationSubring) {E E' W : Type} [AddCommGroup E]
    [Module (Int0 v) E] [AddCommGroup E'] [Module (Int0 v) E'] [AddCommGroup W] [Module C W]
    [Module w.valuationSubring W] [IsScalarTower w.valuationSubring C W] {ι : Type} [Fintype ι]
    (M : Submodule (Int0 v) E) (b : Module.Basis ι (Int0 v) M) (π : E' →ₗ[Int0 v] E) (g : E' → W)
    (hadd : ∀ x y, g (x + y) = g x + g y) (hsmul : ∀ (c : Int0 v) x, g (c • x) = (c : C) • g x)
    (hwd : ∀ x x', π x = π x' → g x = g x') (xs : ι → E') (hxs : ∀ i, π (xs i) = b i)
    (X : Submodule w.valuationSubring W) (hX : ∀ y, y ∈ X ↔ ∃ x, π x ∈ M ∧ g x = y) :
    Submodule.span w.valuationSubring (Set.range fun i => g (xs i)) = X := by
  let gh : E' →+ W := AddMonoidHom.mk' g hadd
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨i, rfl⟩
    exact (hX _).2 ⟨xs i, by rw [hxs i]; exact (b i).2, rfl⟩
  · intro y hy
    obtain ⟨x, hxM, rfl⟩ := (hX y).1 hy
    have hrep := b.sum_repr ⟨π x, hxM⟩
    have hπ : π x = π (∑ i, b.repr ⟨π x, hxM⟩ i • xs i) := by
      have h2 : π x = ∑ i, b.repr ⟨π x, hxM⟩ i • (b i : E) := by
        have := congrArg Subtype.val hrep
        simp only [Submodule.coe_sum, Submodule.coe_smul] at this
        exact this.symm
      rw [map_sum]
      conv_lhs => rw [h2]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, hxs i]
    rw [hwd _ _ hπ]
    have : g (∑ i, b.repr ⟨π x, hxM⟩ i • xs i) = ∑ i, ((b.repr ⟨π x, hxM⟩ i : Int0 v) : C) • g (xs i) := by
      change gh _ = _
      rw [map_sum]
      exact Finset.sum_congr rfl fun i _ => hsmul _ _
    rw [this]
    refine Submodule.sum_mem _ fun i _ => ?_
    have hc : ((b.repr ⟨π x, hxM⟩ i : Int0 v) : C) ∈ w.valuationSubring := (hv _).1 (Subtype.prop _)
    have : ((b.repr ⟨π x, hxM⟩ i : Int0 v) : C) • g (xs i) =
        (⟨_, hc⟩ : w.valuationSubring) • g (xs i) := by
      rw [algebra_compatible_smul C (⟨_, hc⟩ : w.valuationSubring) (g (xs i))]; rfl
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

theorem linearIndependent_mkQ {p q : ℕ} (F : Submodule C (Fin (p + q) → C))
    (hF : Module.finrank C F = q) (u : Fin p → Fin (p + q) → C) (m : Fin q → Fin (p + q) → C)
    (hm : ∀ i, m i ∈ F) (hdet : (Matrix.of (Fin.append u m)).det ≠ 0) :
    LinearIndependent C (fun i => F.mkQ (u i)) := by
  have hli := Matrix.linearIndependent_rows_of_det_ne_zero hdet
  have hli' : LinearIndependent C (Fin.append u m) := hli
  have hmli : LinearIndependent C m := by
    have := hli'.comp (Fin.natAdd p) (Fin.natAdd_injective q p)
    convert this using 1
    funext i; simp
  have hspan : Submodule.span C (Set.range m) = F := by
    apply Submodule.eq_of_le_of_finrank_eq
    · exact Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact hm i)
    · rw [finrank_span_eq_card hmli, Fintype.card_fin, hF]
  rw [linearIndependent_iff']
  intro s c hs i hi
  have h1 : ∑ j ∈ s, c j • u j ∈ F := by
    have : F.mkQ (∑ j ∈ s, c j • u j) = 0 := by
      rw [map_sum]; simp only [map_smul]; exact hs
    exact (Submodule.Quotient.mk_eq_zero F).1 this
  rw [← hspan, Submodule.mem_span_range_iff_exists_fun] at h1
  obtain ⟨d, hd⟩ := h1
  let c' : Fin (p + q) → C := Fin.append (fun j => if j ∈ s then c j else 0) (fun k => - d k)
  have hsum : ∑ k, c' k • Fin.append u m k = 0 := by
    rw [Fin.sum_univ_add]
    simp only [c', Fin.append_left, Fin.append_right, neg_smul, Finset.sum_neg_distrib]
    rw [hd]
    simp only [ite_smul, zero_smul]
    rw [Finset.sum_ite_mem, Finset.univ_inter, add_neg_cancel]
  have := (Fintype.linearIndependent_iff.1 hli') c' hsum (Fin.castAdd q i)
  simpa [c', hi] using this

end GlobalTheory.HerbrandBridge

namespace GlobalTheory.HerbrandBridge
open GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference (freeLattice unif IsFiltration filSpace eigenSub eigenQuot lie quotMap addVal
  DetRel IsLatticeBasis HasVal)

variable {C : Type} [Field C] {S : Type} [Fintype S] [DecidableEq S]

theorem eigenQuot_iff {w : Valuation C ℝ≥0} {v : AddValuation C (WithTop ℝ)}
    (hv : ∀ x, x ∈ Int0 v ↔ x ∈ w.valuationSubring) (a : S → w.valuationSubring) (N : ℕ)
    (F : Submodule w.valuationSubring (S → Fin N → C)) (hle : F ≤ freeLattice a N)
    (hrange : ∀ y, y ∈ freeLattice a N ↔ ∃ x, evalVec (liftA hv a) N x = y)
    (hmem : ∀ x, x ∈ filPre (liftA hv a) F ↔ evalVec (liftA hv a) N x ∈ F) (s : S)
    (y : Fin N → C) :
    y ∈ eigenQuot (W := fun _ => Fin N → C) F s ↔
      ∃ z ∈ eigQuot (liftA hv a) (filPre (liftA hv a) F) s, (fun i => (z i : C)) = y := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨z, hz⟩ := (hrange x).1 (hle hx)
    refine ⟨comp (liftA hv a) N s z, ⟨z, (hmem z).2 (hz ▸ hx), rfl⟩, ?_⟩
    rw [comp_coe, hz]; rfl
  · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨_, (hmem z).1 hz, rfl⟩

theorem eigRank_eq {w : Valuation C ℝ≥0} {v : AddValuation C (WithTop ℝ)}
    (hv : ∀ x, x ∈ Int0 v ↔ x ∈ w.valuationSubring) (a : S → w.valuationSubring) (N : ℕ)
    (F : Submodule w.valuationSubring (S → Fin N → C)) (hle : F ≤ freeLattice a N)
    (hrange : ∀ y, y ∈ freeLattice a N ↔ ∃ x, evalVec (liftA hv a) N x = y)
    (hmem : ∀ x, x ∈ filPre (liftA hv a) F ↔ evalVec (liftA hv a) N x ∈ F) (s : S) :
    eigRank v (liftA hv a) (filPre (liftA hv a) F) s = Module.finrank C (filSpace F s) := by
  have : ((fun (x : Fin N → Int0 v) (i : Fin N) => (x i : C)) ''
      (eigQuot (liftA hv a) (filPre (liftA hv a) F) s : Set (Fin N → Int0 v))) =
      (eigenQuot (W := fun _ => Fin N → C) F s : Set (Fin N → C)) := by
    ext y
    simp only [Set.mem_image, SetLike.mem_coe]
    rw [eigenQuot_iff hv a N F hle hrange hmem s y]
  unfold eigRank filSpace
  rw [this]

end GlobalTheory.HerbrandBridge

namespace GlobalTheory.HerbrandBridge
open GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference (freeLattice unif IsFiltration filSpace eigenSub eigenQuot lie quotMap addVal
  DetRel IsLatticeBasis HasVal)

variable {C : Type} [Field C] {S : Type} [Fintype S] [DecidableEq S]

theorem yExp_eq (w : Valuation C ℝ≥0) (ℓ : C) (h0 : 0 < w ℓ) (h1 : w ℓ < 1)
    (hv : ∀ x, x ∈ Int0 (toAddVal w ℓ h0 h1) ↔ x ∈ w.valuationSubring)
    (a : S → w.valuationSubring) (ha : Function.Injective a) {N : ℕ}
    (F : Submodule (RS (liftA hv a)) (Fin N → RS (liftA hv a))) (G : S → Submodule C (Fin N → C))
    (hrk : ∀ s, eigRank (toAddVal w ℓ h0 h1) (liftA hv a) F s = Module.finrank C (G s)) (τ : S) :
    yExp (toAddVal w ℓ h0 h1) (liftA hv a) F τ =
      ((∑ s ∈ Finset.univ.erase τ, (Module.finrank C (G s) : ℝ) *
        addVal w ℓ ((a τ : C) - (a s : C)) : ℝ) : WithTop ℝ) := by
  unfold yExp
  rw [WithTop.coe_sum]
  refine Finset.sum_congr rfl fun s hs => ?_
  rw [hrk s]
  have hne : (a s : C) - (a τ : C) ≠ 0 := by
    intro h
    exact (Finset.ne_of_mem_erase hs) (ha (Subtype.ext (sub_eq_zero.1 h)))
  change _ • toAddVal w ℓ h0 h1 ((a s : C) - (a τ : C)) = _
  rw [toAddVal_of_ne _ _ _ _ hne, ← WithTop.coe_nsmul, nsmul_eq_mul]
  congr 2
  unfold addVal
  rw [w.map_sub_swap]

end GlobalTheory.HerbrandBridge

namespace GlobalTheory.HerbrandBridge
open GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference (freeLattice unif IsFiltration filSpace eigenSub eigenQuot lie quotMap addVal
  DetRel IsLatticeBasis HasVal)

theorem exForm : ∀ (C : Type) [Field C] (w : Valuation C ℝ≥0) (ℓ : C), 0 < w ℓ → w ℓ < 1 →
    ∀ (S : Type) [Fintype S] [DecidableEq S] (a : S → w.valuationSubring) (p q : ℕ)
    (Fil : Submodule w.valuationSubring (S → Fin (p + q) → C)) (τ : S), Function.Injective a →
    GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.IsFiltration a Fil →
    Module.finrank C (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.filSpace Fil τ) = q →
    GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.DetRel w ℓ (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.filSpace Fil τ)
      (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.eigenSub (W := fun _ => Fin (p + q) → C)
        (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.freeLattice a (p + q)) τ)
      (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.eigenSub
        (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.lie (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.freeLattice a (p + q)) Fil) τ)
      (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.eigenQuot (W := fun _ => Fin (p + q) → C) Fil τ)
      (∑ s ∈ Finset.univ.erase τ, (Module.finrank C (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.filSpace Fil s) : ℝ) *
        GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.addVal w ℓ ((a τ : C) - (a s : C))) := by
  intro C _ w ℓ h0 h1 S _ _ a p q Fil τ ha hF hq
  have hv := mem_addValuationIntegerRing_normalized_iff w ℓ h0 h1
  have ha' : Function.Injective (liftA hv a) := fun s t h =>
    ha (Subtype.ext (congrArg (fun z : Int0 (toAddVal w ℓ h0 h1) => (z : C)) h))
  have hmem := filPre_mem C w _ hv S a (p + q) Fil hF.stable
  have hrange := evalVec_range C w _ hv S a (p + q)
  have hinj := evalVec_injective C w _ hv S a (p + q) ha
  have hcomp := mem_of_components C w S a (p + q) Fil ha hF
  have hsat : ∀ (c : Int0 (toAddVal w ℓ h0 h1)) (x : Fin (p + q) → RS (liftA hv a)), c ≠ 0 →
      c • x ∈ filPre (liftA hv a) Fil → x ∈ filPre (liftA hv a) Fil := by
    intro c x hc hcx
    rw [hmem] at hcx ⊢
    have hc' : (c : C) ∈ w.valuationSubring := (hv _).1 c.2
    refine hF.saturated _ ((hrange _).2 ⟨x, rfl⟩) ⟨(c : C), hc'⟩ ?_ ?_
    · intro h
      apply hc
      exact Subtype.ext (congrArg (fun z : w.valuationSubring => (z : C)) h)
    · convert hcx using 1
      rw [evalVec_smul]
      rfl
  have hrk := eigRank_eq hv a (p + q) Fil hF.le hrange hmem
  obtain ⟨⟨p', hp', ⟨h⟩, ⟨l⟩, ⟨f⟩, hDet⟩, -, -⟩ :=
    GlobalTheory.T.herbrandQuotient_eigen_det C (toAddVal w ℓ h0 h1) S (liftA hv a) ha' (p + q) (filPre (liftA hv a) Fil) hsat τ
  have hq' : eigRank (toAddVal w ℓ h0 h1) (liftA hv a) (filPre (liftA hv a) Fil) τ = q :=
    (hrk τ).trans hq
  have hpp : p = p' := by omega
  subst hpp

  choose x hx using fun i => Submodule.Quotient.mk_surjective (filPre (liftA hv a) Fil)
    (l i : (Fin (p + q) → RS (liftA hv a)) ⧸ (filPre (liftA hv a) Fil))
  let e : Fin (p + q) ≃ Fin p ⊕ Fin (eigRank (toAddVal w ℓ h0 h1) (liftA hv a) (filPre (liftA hv a) Fil) τ) :=
    finSumFinEquiv.symm.trans (Equiv.sumCongr (Equiv.refl _) (finCongr hq'.symm))
  obtain ⟨c, hc, hne, hdet⟩ := hDet h l x hx f e
  let X : Fin (p + q) → Fin (p + q) → C := fun k i =>
    ((comp (liftA hv a) (p + q) τ (h k : Fin (p + q) → RS (liftA hv a)) i : Int0 (toAddVal w ℓ h0 h1)) : C)
  let U : Fin p → Fin (p + q) → C := fun k i => ((comp (liftA hv a) (p + q) τ (x k) i : Int0 (toAddVal w ℓ h0 h1)) : C)
  let fb := f.reindex (finCongr hq')
  let M : Fin q → Fin (p + q) → C := fun k i => ((fb k : Fin (p + q) → Int0 (toAddVal w ℓ h0 h1)) i : C)
  have hXmat : Matrix.of X = (Matrix.of fun k => comp (liftA hv a) (p + q) τ
      (h k : Fin (p + q) → RS (liftA hv a))).map (Int0 (toAddVal w ℓ h0 h1)).subtype := rfl
  have hAmat : Matrix.of (Fin.append U M) = (Matrix.of fun k => Sum.elim
      (fun i => comp (liftA hv a) (p + q) τ (x i)) (fun i => (f i : Fin (p + q) → Int0 (toAddVal w ℓ h0 h1))) (e k)).map
      (Int0 (toAddVal w ℓ h0 h1)).subtype := by
    ext k j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) k
    · simp [e, U]
    · simp [e, M, fb, Module.Basis.reindex_apply]
  have hdet' : (Matrix.of X).det = c * (Matrix.of (Fin.append U M)).det := by
    rw [hXmat, hAmat, ← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply, ← RingHom.map_det,
      ← RingHom.map_det]
    exact hdet
  have hy := yExp_eq w ℓ h0 h1 hv a ha (filPre (liftA hv a) Fil) (filSpace Fil) hrk τ
  have hc0 : c ≠ 0 := by
    intro h0'
    rw [h0', AddValuation.map_zero, hy] at hc
    exact WithTop.top_ne_coe hc
  have hAne : (Matrix.of (Fin.append U M)).det ≠ 0 := by
    rw [hAmat, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    intro h'
    exact hne (Subtype.ext h')
  have hXne : (Matrix.of X).det ≠ 0 := by
    rw [hdet']
    exact mul_ne_zero hc0 hAne
  have hli : LinearIndependent C (Fin.append U M) :=
    Matrix.linearIndependent_rows_of_det_ne_zero hAne
  have hMli : LinearIndependent C M := by
    have := hli.comp (Fin.natAdd p) (Fin.natAdd_injective q p)
    convert this using 1
    funext i; simp
  have hMq : ∀ k, M k ∈ eigenQuot (W := fun _ => Fin (p + q) → C) Fil τ := fun k =>
    (eigenQuot_iff hv a (p + q) Fil hF.le hrange hmem τ (M k)).2 ⟨_, (fb k).2, rfl⟩
  have hMF : ∀ k, M k ∈ filSpace Fil τ := fun k => Submodule.subset_span (hMq k)

  refine ⟨X, U, M, c, ⟨Matrix.linearIndependent_rows_of_det_ne_zero hXne, ?_⟩,
    ⟨linearIndependent_mkQ (filSpace Fil τ) hq U M hMF hAne, ?_⟩, ⟨hMli, ?_⟩, hMF,
    ⟨hc0, ?_⟩, hdet'⟩
  ·
    refine span_eq_of_basis hv (eigSub (liftA hv a) τ (Fin (p + q) → RS (liftA hv a))) h
      LinearMap.id (fun z i => ((comp (liftA hv a) (p + q) τ z i : Int0 (toAddVal w ℓ h0 h1)) : C))
      (fun z z' => by funext i; simp only [map_add, Pi.add_apply]; rfl)
      (fun c z => by funext i; simp only [map_smul, Pi.smul_apply, smul_eq_mul]; rfl)
      (fun z z' hz => by rw [show z = z' from hz])
      (fun k => (h k : Fin (p + q) → RS (liftA hv a))) (fun k => rfl) _ (fun y => ?_)
    rw [eigenSub_iff C w _ hv S a (p + q) τ ha hinj hrange y]
    simp only [LinearMap.id_apply]
  ·
    refine span_eq_of_basis hv (eigSub (liftA hv a) τ ((Fin (p + q) → RS (liftA hv a)) ⧸
        filPre (liftA hv a) Fil)) l (proj (liftA hv a) (filPre (liftA hv a) Fil))
      (fun z => quotMap (w := w) (filSpace Fil τ)
        (fun i => ((comp (liftA hv a) (p + q) τ z i : Int0 (toAddVal w ℓ h0 h1)) : C)))
      (fun z z' => by
        rw [← map_add]; congr 1; funext i; simp only [map_add, Pi.add_apply]; rfl)
      (fun c z => by
        show (filSpace Fil τ).mkQ _ = (c : C) • (filSpace Fil τ).mkQ _
        rw [← map_smul]; congr 1; funext i; simp only [map_smul, Pi.smul_apply, smul_eq_mul]; rfl)
      (fun z z' hz => ?_) x hx _ (fun y => ?_)
    · show (filSpace Fil τ).mkQ _ = (filSpace Fil τ).mkQ _
      rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
      have h2 : z - z' ∈ filPre (liftA hv a) Fil :=
        (Submodule.Quotient.eq (filPre (liftA hv a) Fil)).1 hz
      rw [hmem, evalVec_sub] at h2
      refine Submodule.subset_span ⟨_, h2, ?_⟩
      funext i
      rfl
    · exact lie_iff C w _ hv S a (p + q) Fil τ ha hF hinj hrange hmem hcomp y
  ·
    refine span_eq_of_basis hv (eigQuot (liftA hv a) (filPre (liftA hv a) Fil) τ) fb
      LinearMap.id (fun z i => ((z i : Int0 (toAddVal w ℓ h0 h1)) : C))
      (fun z z' => by funext i; rfl) (fun c z => by funext i; rfl)
      (fun z z' hz => by rw [show z = z' from hz])
      (fun k => (fb k : Fin (p + q) → Int0 (toAddVal w ℓ h0 h1))) (fun k => rfl) _ (fun y => ?_)
    rw [eigenQuot_iff hv a (p + q) Fil hF.le hrange hmem τ y]
    simp only [LinearMap.id_apply]
  · rw [hy, toAddVal_of_ne _ _ _ _ hc0] at hc
    exact WithTop.coe_injective hc

end GlobalTheory.HerbrandBridge
