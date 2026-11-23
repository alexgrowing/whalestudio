import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenLocOfCenReal
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CoreEq
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoFormsOff
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroWild
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalGlobalAboveL
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OverRowsAndMono
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AlgWeightContragredientExistsUnique
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AlgWeightHighestWeightExistsUniqueAntitoneStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolynomialRepGLComplexAlgebraicWeightEvalPointStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TotallyComplexHostE
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolyRep
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open ReciprocityTheory.Aut Formalism.AUTREP
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

noncomputable section

namespace GlobalTheory.LiftInfRef

open Matrix Formalism.L2.NG GlobalTheory.AlgWtHW NumberField

section Conj
variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

def w0 (n : ℕ) : GL (Fin n) ℂ :=
  ⟨(Fin.revPerm.toPEquiv).toMatrix, (Fin.revPerm.toPEquiv).toMatrix, by
    rw [PEquiv.toMatrix_toPEquiv_mul]; ext i j
    simp [PEquiv.toMatrix_apply, Matrix.one_apply], by
    rw [PEquiv.toMatrix_toPEquiv_mul]; ext i j
    simp [PEquiv.toMatrix_apply, Matrix.one_apply]⟩

theorem longestWeylElementGL_mul_self (n : ℕ) : w0 n * w0 n = 1 := by
  ext i j
  simp only [w0, Units.val_mul, Units.val_one]
  rw [PEquiv.toMatrix_toPEquiv_mul]
  simp [PEquiv.toMatrix_apply, Matrix.one_apply]

theorem longestWeylElementGL_conj_apply_rev (X : GL (Fin n) ℂ) (i j : Fin n) :
    (w0 n * X * w0 n).val i j = X.val (Fin.rev i) (Fin.rev j) := by
  simp only [w0, Units.val_mul]
  rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
  simp

def tinv (B : GL (Fin n) ℂ) : GL (Fin n) ℂ :=
  ⟨(B⁻¹ : GL (Fin n) ℂ).valᵀ, B.valᵀ, by rw [← transpose_mul, Units.mul_inv, transpose_one],
    by rw [← transpose_mul, Units.inv_mul, transpose_one]⟩

omit [NumberField L] [IsCMField L] in
theorem conj_conj (τ : L →+* ℂ) : ComplexEmbedding.conjugate (ComplexEmbedding.conjugate τ) = τ := by
  ext x; simp

theorem conj_ne (τ : L →+* ℂ) : ComplexEmbedding.conjugate τ ≠ τ := by
  intro h
  have h1 : ComplexEmbedding.IsReal τ := ComplexEmbedding.isReal_iff.2 h
  have h2 := IsTotallyComplex.isComplex (InfinitePlace.mk τ)
  rw [← InfinitePlace.not_isReal_iff_isComplex, InfinitePlace.isReal_mk_iff] at h2
  exact h2 h1

theorem evPt_eq_tinv (τ : L →+* ℂ) (B : GL (Fin n) ℂ) :
    evPt τ B = evPt (ComplexEmbedding.conjugate τ) (tinv B) := by
  have hne := conj_ne τ
  funext p
  rcases p with ⟨σ, i, j⟩
  by_cases h1 : σ = τ
  · subst h1
    simp [NG.evPt, tinv, Ne.symm hne]
  · by_cases h2 : σ = ComplexEmbedding.conjugate τ
    · subst h2
      simp [NG.evPt, tinv, hne]
    · have h3 : σ ≠ ComplexEmbedding.conjugate (ComplexEmbedding.conjugate τ) := by rwa [conj_conj]
      simp [NG.evPt, h1, h2, h3]

theorem inv_upper {B : GL (Fin n) ℂ} (hB : B.val.BlockTriangular id) : (B⁻¹).val.BlockTriangular id := by
  haveI : Invertible B.val := B.invertible
  rw [Matrix.coe_units_inv]
  exact Matrix.blockTriangular_inv_of_blockTriangular hB

theorem inv_diag {B : GL (Fin n) ℂ} (hB : B.val.BlockTriangular id) (k : Fin n) :
    (B⁻¹).val k k = (B.val k k)⁻¹ := by
  have hI := inv_upper hB
  have e : ((B⁻¹).val * B.val) k k = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one, one_apply_eq]
  rw [Matrix.mul_apply, Finset.sum_eq_single k] at e
  · exact eq_inv_of_mul_eq_one_left e
  · intro l _ hl
    rcases lt_or_gt_of_ne hl with h | h
    · rw [hI h, zero_mul]
    · rw [hB h, mul_zero]
  · simp

theorem hwAt_of_conj {a : AlgWt L n} {τ : L →+* ℂ} {lam' : Fin n → ℤ}
    (h : a.HWAt (ComplexEmbedding.conjugate τ) lam') : a.HWAt τ (fun i => -lam' (Fin.rev i)) := by
  obtain ⟨ι, hι1, hι2, b, P, hP, v, hv0, hv⟩ := h
  have hR := GlobalTheory.T.isPolynomialRepGLComplex_algebraicWeight_evalPoint L n a ι b P hP (ComplexEmbedding.conjugate τ)
  refine ⟨ι, hι1, hι2, b, P, hP, evM P (evPt (ComplexEmbedding.conjugate τ) (w0 n)) *ᵥ v, ?_, fun B hB => ?_⟩
  · intro h0
    apply hv0
    have := congrArg (fun x => evM P (evPt (ComplexEmbedding.conjugate τ) (w0 n)) *ᵥ x) h0
    simp only [mulVec_mulVec, mulVec_zero] at this
    rwa [← hR.mul, longestWeylElementGL_mul_self, hR.one, one_mulVec] at this
  · set C : GL (Fin n) ℂ := w0 n * tinv B * w0 n with hCdef
    have hBC : tinv B = w0 n * C * w0 n := by
      rw [hCdef, ← mul_assoc, ← mul_assoc, longestWeylElementGL_mul_self, one_mul, mul_assoc, longestWeylElementGL_mul_self, mul_one]
    have hCa : ∀ i j, C.val i j = (B⁻¹).val (Fin.rev j) (Fin.rev i) := by
      intro i j; rw [hCdef, longestWeylElementGL_conj_apply_rev]; rfl
    have hC : C.val.BlockTriangular id := by
      intro i j hij
      rw [hCa]
      exact inv_upper hB (show Fin.rev i < Fin.rev j from Fin.rev_lt_rev.2 hij)
    have hCd : ∀ i, C.val i i = (B.val (Fin.rev i) (Fin.rev i))⁻¹ := fun i => by rw [hCa, inv_diag hB]
    have e1 : (Matrix.of fun i j => MvPolynomial.eval (evPt τ B) (P i j)) =
        evM P (evPt (ComplexEmbedding.conjugate τ) (tinv B)) := by
      rw [evPt_eq_tinv τ B]; rfl
    have hww : evM P (NG.evPt (ComplexEmbedding.conjugate τ) (w0 n)) *ᵥ
        (evM P (NG.evPt (ComplexEmbedding.conjugate τ) (w0 n)) *ᵥ v) = v := by
      rw [mulVec_mulVec, ← hR.mul, longestWeylElementGL_mul_self, hR.one, one_mulVec]
    have hvC : evM P (NG.evPt (ComplexEmbedding.conjugate τ) C) *ᵥ v = (∏ i, (C.val i i) ^ (lam' i)) • v := hv C hC
    rw [e1, hBC, hR.mul, hR.mul, ← mulVec_mulVec, ← mulVec_mulVec, hww, hvC, mulVec_smul]
    congr 1
    rw [Finset.prod_congr rfl fun i _ => by rw [hCd i, _root_.inv_zpow']]
    exact Fintype.prod_equiv Fin.revPerm _ _ (fun i => by simp [Fin.rev_rev])

end Conj

end GlobalTheory.LiftInfRef

namespace GlobalTheory.LiftInfRef

open Matrix Formalism.L2.NG GlobalTheory.AlgWtHW NumberField

section Conj2
variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

theorem infOf_conj {a : AlgWt L n} {τ : L →+* ℂ} {lam lam' : Fin n → ℤ} (h : a.HWAt τ lam)
    (h' : a.HWAt (ComplexEmbedding.conjugate τ) lam') : infOf lam' = (infOf lam).map Neg.neg := by
  have e := (GlobalTheory.T.algWeight_highestWeight_exists_unique_antitone L n a τ).1.unique h (hwAt_of_conj h')
  have hl : lam' = fun i => -lam (Fin.rev i) := by funext i; rw [e]; simp
  subst hl
  unfold infOf
  rw [Multiset.map_map]
  conv_rhs => rw [← Multiset.map_univ_val_equiv Fin.revPerm, Multiset.map_map]
  refine Multiset.map_congr rfl fun i _ => ?_
  simp only [Function.comp_apply, Fin.revPerm_apply, Fin.val_rev]
  have hi := i.isLt
  rw [Nat.cast_sub (by omega)]
  push_cast
  ring

end Conj2

theorem sum_singletons {α : Type} (l : List α) (f : α → ℂ) : (l.map fun k => ({f k} : Multiset ℂ)).sum = ((l.map f : List ℂ) : Multiset ℂ) := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih, Multiset.singleton_add]

theorem bindCast (t : ℕ) : ((List.range t >>= fun a => pure (a : ℂ)) : List ℂ) = (List.range t).map (fun a : ℕ => (a : ℂ)) := by
  simp [List.map_eq_flatMap]

theorem range_rev (t : ℕ) (f : ℕ → ℂ) : (Multiset.range t).map (fun c => f (t - 1 - c)) = (Multiset.range t).map f := by
  have h := congrArg (fun l : List ℕ => ((l.map f : List ℂ) : Multiset ℂ)) (List.reverse_range' (s := 0) (n := t))
  simp only [List.map_reverse, Multiset.coe_reverse, List.map_map] at h
  rw [← List.range_eq_range'] at h
  simpa [Multiset.range, Function.comp_def] using h.symm

end GlobalTheory.LiftInfRef

namespace GlobalTheory.LiftInfRef

open GlobalTheory.LiftRef

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem lg_of_forall {K : Ctx} {p : ∀ B : Base, Fr B.toPre → TwDat B → Prop} (h : ∀ B f T, p B f T) : large₂ K p :=
  ⟨fun _ _ _ => ∅, fun _ _ _ _ => ∅, fun _ _ _ _ _ => ∅, fun _ _ _ _ _ => ∅, by simp, by simp, fun B f T _ _ _ _ => h B f T⟩

theorem evLgG_of_forall {p : Ctx → ∀ B : Base, Fr B.toPre → TwDat B → Prop} (h : ∀ K B f T, p K B f T) : EvLgG p :=
  evLgG_of_evLg ⟨1, one_pos, fun _ _ _ _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun _ _ _ _ => ⟨0, fun _ _ => ⟨0,
    fun _ _ => ⟨0, fun K _ _ _ _ _ => lg_of_forall (h K)⟩⟩⟩⟩⟩

theorem core (D : D7) (cf : CharFrame D) (A : AUSide D) (chr : CharSide D cf) (M : MtFam D)
    {tup : D.what₂.Tup → Fin D.R.m → HChar D.host.E} {Q : D.what₂.places.Pl → Finset (PlE D.host)}
    (hIn : MtInput D M tup Q) (k : ℕ) (h1 : 1 ≤ k + 1) (h2 : k + 1 ≤ D.R.m)
    (S : Submodule ℂ (Formalism.AUTREP.GAf D.host.E D.R.nV → (M D.what₂.mu0 (k + 1) h1 h2).wt.W))
    (hS : NG.IsIrrRep (M D.what₂.mu0 (k + 1) h1 h2).wt.ρ S) (μ : D.naut.CG 1)
    (hμ : (chr.e1 μ).1 = cf.mu0 ⟨k, by omega⟩) (τ : D.what₂.Tau) :
    D.nbc.infW (k + 1) (D.nbc.wtAU (k + 1) (A.cls (k + 1) h1 h2 (autOf (M D.what₂.mu0 (k + 1) h1 h2) S hS))) (GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.embTau D τ) =
        (GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.hcSigma (D.hc τ)).map (· - 1 / 2) + isoInf D.nd D.naut [⟨1, D.naut.tw μ D.naut.etaTinv, D.R.t⟩] (GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.embTau D τ) ∧
      D.nbc.infW (k + 1) (D.nbc.wtAU (k + 1) (A.cls (k + 1) h1 h2 (autOf (M D.what₂.mu0 (k + 1) h1 h2) S hS))) (GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.embTauBar D τ) =
        (GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.hcSigma (D.hc τ)).map (fun y => -y + 1 / 2) + isoInf D.nd D.naut [⟨1, D.naut.tw μ D.naut.etaTinv, D.R.t⟩] (GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.embTauBar D τ) := by
  set π := autOf (M D.what₂.mu0 (k + 1) h1 h2) S hS with hπ
  obtain ⟨b, hd, -, -⟩ := GlobalTheory.algWt_contragredient D.host.E D.R.nV π.toAlgWt
  have hw := A.wt (k + 1) h1 h2 π b hd
  obtain ⟨lam, hlam⟩ := (GlobalTheory.T.algWeight_highestWeight_exists_unique_antitone D.host.E D.R.nV b (GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.embTau D τ)).1.exists
  obtain ⟨lam', hlam'⟩ := (GlobalTheory.T.algWeight_highestWeight_exists_unique_antitone D.host.E D.R.nV b (ComplexEmbedding.conjugate (GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.embTau D τ))).1.exists
  have hbar : GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.embTauBar D τ = ComplexEmbedding.conjugate (GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.embTau D τ) := by
    ext x; simp [GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.embTauBar, ComplexEmbedding.conjugate_coe_eq]
  have hpar : NG.infOf lam = NG.paramV D.R (D.hc τ) ⟨k, by omega⟩ (1 / 2) := hIn.wt D.what₂.mu0 ⟨k, by omega⟩ τ b lam hd hlam
  have hinf1 := A.infW (k + 1) h1 h2 b _ lam hlam
  have hinf2 := A.infW (k + 1) h1 h2 b _ lam' hlam'
  have hconj := infOf_conj hlam hlam'
  have he : (chr.e1 (D.naut.tw μ D.naut.etaTinv)).1 = cf.mu0 ⟨k, by omega⟩ * cf.eta⁻¹ := by
    rw [chr.tw, hμ, chr.etaTinv]
  have hI : (chr.e1 (D.naut.tw μ D.naut.etaTinv)).1.HasInfQ (embPsi D.host)
      (fun g => -eExp D ⟨k, by omega⟩ g - 1 / 2) := by
    rw [he]
    have h1' := (cf.isMu0 ⟨k, by omega⟩).inf
    have h2' : (cf.eta⁻¹).HasInfQ (embPsi D.host) (-(fun _ => 1 / 2)) :=
      GlobalTheory.BlockCharInf.hasInfQ_inv' ⟨fun _ => 1, fun _ => by norm_num, cf.isEta.inf⟩
    convert GlobalTheory.BlockCharInf.hasInfQ_mul' h1' h2' using 1
    funext g
    simp only [Pi.add_apply, Pi.neg_apply]
    ring
  obtain ⟨hg1, hg2⟩ := chr.infG _ _ hI (D.eTau τ)
  have hval : eExp D ⟨k, by omega⟩ (D.eTau τ) = (D.hc τ).e ⟨k, by omega⟩ := by simp [eExp]
  have hG1 : D.naut.infG (D.naut.tw μ D.naut.etaTinv) (GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.embTau D τ) = {(-((D.hc τ).e ⟨k, by omega⟩ : ℂ) - 1 / 2)} := by
    rw [show GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.embTau D τ = embPsi D.host (D.eTau τ) from rfl, hg1, hval]; push_cast; ring_nf
  have hG2 : D.naut.infG (D.naut.tw μ D.naut.etaTinv) (ComplexEmbedding.conjugate (GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.embTau D τ)) =
      {(((D.hc τ).e ⟨k, by omega⟩ : ℂ) + 1 / 2)} := by
    rw [← hbar, show GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.embTauBar D τ = (starRingEnd ℂ).comp (embPsi D.host (D.eTau τ)) from rfl, hg2, hval]; push_cast; ring_nf
  rw [hw, hinf1, hbar, hinf2, hconj, hpar]
  constructor
  · unfold isoInf
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, hG1, Multiset.map_singleton, bindCast, List.map_map, Function.comp_def, sum_singletons]
    unfold NG.paramV GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.hcSigma
    rw [Multiset.map_add, Multiset.map_map, Multiset.map_map, ← Multiset.map_coe, Multiset.coe_range]
    refine congrArg₂ (· + ·) (congrArg₂ (· + ·) ?_ ?_) ?_
    · refine Multiset.map_congr rfl fun i _ => ?_
      simp only [Function.comp_apply]
    · refine Multiset.map_congr rfl fun i _ => ?_
      simp only [Function.comp_apply]
    · refine Multiset.map_congr rfl fun c _ => ?_
      push_cast; ring
  · unfold isoInf
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, hG2, Multiset.map_singleton, bindCast, List.map_map, Function.comp_def, sum_singletons]
    unfold NG.paramV GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.hcSigma
    rw [Multiset.map_add, Multiset.map_add, Multiset.map_add, Multiset.map_map, Multiset.map_map, Multiset.map_map,
      Multiset.map_map, Multiset.map_map, ← Multiset.map_coe, Multiset.coe_range]
    refine congrArg₂ (· + ·) (congrArg₂ (· + ·) ?_ ?_) ?_
    · refine Multiset.map_congr rfl fun i _ => ?_
      simp only [Function.comp_apply]; ring
    · refine Multiset.map_congr rfl fun i _ => ?_
      simp only [Function.comp_apply]; ring
    · have hf := range_rev D.R.t (fun c : ℕ => ((D.hc τ).e ⟨k, by omega⟩ : ℂ) + 1 / 2 - ((D.R.t : ℂ) - 1) / 2 + c)
      refine (Multiset.map_congr rfl fun c _ => ?_).trans (hf.symm.trans (Multiset.map_congr rfl fun c hc => ?_))
      · simp only [Function.comp_apply]; push_cast; ring
      · have hc' := Multiset.mem_range.1 hc
        rw [Nat.cast_sub (show c ≤ D.R.t - 1 by omega), Nat.cast_sub (show 1 ≤ D.R.t by omega)]
        push_cast; ring

end GlobalTheory.LiftInfRef

namespace GlobalTheory.LiftInfRef

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem lift_inf : PrN → ∀ hL : GlobalTheory.Published.LocalLanglandsGL, GlobalTheory.LiftRef.AtRows hL fun D cf _ _ a M => ∀ (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (S : Submodule ℂ (Formalism.AUTREP.GAf D.host.E D.R.nV → (M D.what₂.mu0 j h1 h2).wt.W)) (hS : NG.IsIrrRep (M D.what₂.mu0 j h1 h2).wt.ρ S) (μ : D.naut.CG 1), (a.chr.e1 μ).1 = cf.mu0 ⟨j - 1, by omega⟩ → ∀ τ, D.nbc.infW j (D.nbc.wtAU j (a.A.cls j h1 h2 (GlobalTheory.LiftRef.autOf (M D.what₂.mu0 j h1 h2) S hS))) (GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.embTau D τ) = (GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.hcSigma (D.hc τ)).map (· - 1 / 2) + isoInf D.nd D.naut [⟨1, D.naut.tw μ D.naut.etaTinv, D.R.t⟩] (GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.embTau D τ) ∧ D.nbc.infW j (D.nbc.wtAU j (a.A.cls j h1 h2 (GlobalTheory.LiftRef.autOf (M D.what₂.mu0 j h1 h2) S hS))) (GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.embTauBar D τ) = (GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.hcSigma (D.hc τ)).map (fun y => -y + 1 / 2) + isoInf D.nd D.naut [⟨1, D.naut.tw μ D.naut.etaTinv, D.R.t⟩] (GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.embTauBar D τ) := by
  intro _ hL
  unfold GlobalTheory.LiftRef.AtRows OverRows
  refine evLgG_of_forall fun K B f T _ w _ Z Wt hX z p0 Y _ _ _ _ _ => ?_
  intro Rw a M tup Q _ hIn j h1 h2 S hS μ hμ τ
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  exact core _ _ a.A a.chr M hIn k h1 h2 S hS μ (by simpa using hμ) τ

end GlobalTheory.LiftInfRef

end
