import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.DataParams₂
import Formalism.LocalRingCardinality.DataParamsS
import Formalism.LocalRingCardinality.DataDIVDefs
import Formalism.LocalRingCardinality.DataBu
import Formalism.LocalRingCardinality.PrincipalHermitianLattice
import Formalism.LocalRingCardinality.DataKap
import Formalism.LocalRingCardinality.KernelPlaceMeanBound
import Formalism.LocalRingCardinality.DataAmbForm
import Formalism.LocalRingCardinality.DataRRMetric
import Formalism.LocalRingCardinality.DataNChoice
import Formalism.SharpRestriction.ParConsts
import Formalism.SharpRestriction.ParamsHeightRankConstant
import Formalism.SharpRestriction.GlobalSchurBounds.ZetaZeroFreeRegion
import Formalism.SharpRestriction.Divisibility.PlaceRankTwoOne
import Formalism.SharpRestriction.LevelLetterCocycles.TwGood

noncomputable section

namespace Formalism.MainNotions.LocalQuadraticParts

open Formalism.BasicNotions Formalism.BasicNotions.DV NumberField IsDedekindDomain

structure Loc (D : D7) where

  Jx : ℕ → D.what₂.places.Pl → ℝ

abbrev qn {D : D7} (A : AmbForm D (RowSide.sharp D)) (v : InfinitePlace D.what₂.LL) (q : (A.MtH D.what₂.mu0).V) : ℝ :=
  DV.quotNorm A v q

def nTT (D : D7) : ℝ := (D.host.TT.card : ℝ)

def iotaQ (D : D7) (μ : D.what₂.Tup) : D.what₂.Qsp μ →ₗ[ℂ] D.what₂.EE :=
  (D.what₂.iota μ).domRestrict (D.what₂.Qsp μ)

def Z0 (D : D7) (μ : D.what₂.Tup) (j : ℕ) : Submodule ℂ (D.what₂.Mt μ j) :=
  (LinearMap.ker (D.what₂.thetaP μ j))ᗮ ⊓ LinearMap.range (D.what₂.eMt μ j)

def UsedT (D : D7) (μ : D.what₂.Tup) : Prop := μ = D.what₂.mu0 ∨ ∃ w, μ = D.what₂.muAt w

def adm1 (D : D7) (Z : DivX D) (P : BaseLevelRowSide D) : Prop :=
  (∀ μ, UsedT D μ → D.what₂.RRset μ ⊆ Set.range D.jEE) ∧
  (∀ μ, UsedT D μ → P.s.RRset μ ⊆ Set.range P.s.jEE) ∧
  D.RRFull ∧ P.BaseRowLatticeFull ∧ D.BuRational ∧
  Rows.BuDefQ D.what₂ ∧
  (∀ u μ, UsedT D μ → ∀ (φ : D.what₂.Mu u), ∀ F ∈ D.what₂.V0 μ,
    D.what₂.perCol u μ φ F = D.what₂.zeC u μ * D.what₂.Bu u φ (D.what₂.iota μ F)) ∧
  (∀ u, D.what₂.zeC u D.what₂.mu0 = 1) ∧
  Rows.ZeUnit D.what₂ ∧
  (∀ μ, Function.Bijective (iotaQ D μ)) ∧
  (0 < Z.kapR D.what₂.embLL ∧ ∃ ρ : D.what₂.Tup → ℝ, ρ D.what₂.mu0 = 1 ∧ (∀ μ, 0 < ρ μ) ∧ RhoUnit D ρ ∧
    ∀ μ (σ : Fin D.what₂.Drows),
      (iotaQ D μ ∘ₗ LinearMap.adjoint (iotaQ D μ)) (D.what₂.onb σ) =
        ((Z.kapR D.what₂.embLL * ρ μ * ∏ j ∈ SizeData₂.lifts D, D.what₂.lamP μ j (D.what₂.ft σ) : ℝ) : ℂ) • D.what₂.onb σ) ∧
  KapRBase Z ∧ P.BaseLevelSideLevelOneCondition ∧
  (∀ μ, ∀ j ∈ SizeData₂.lifts D, Function.Bijective ((D.what₂.thetaP μ j).domRestrict (Z0 D μ j))) ∧
  Rows.LamPDef D.what₂ ∧
  Rows.IsotRank D.what₂ ∧ Rows.IsotInternal D.what₂ ∧ (∀ σ : Fin D.what₂.Drows, 0 < D.what₂.nRows0 (D.what₂.ft σ))

def PeterssonBoundAtEmbedding (D : D7) (Z : DivX D) (A : AmbForm D (RowSide.sharp D)) (s : D.what₂.LL →+* ℂ) : Prop :=
  ∀ (x : D.div.RR.V) (q : (A.MtH D.what₂.mu0).V), A.jAmb D.what₂.mu0 q ∈ D.what₂.V0 D.what₂.mu0 →
    D.jEE x = D.what₂.iota D.what₂.mu0 (A.jAmb D.what₂.mu0 q) →
    Z.kapR s * Real.exp (⨅ σ : Fin D.what₂.Drows, ∑ j ∈ SizeData₂.lifts D, Z.logLam j (D.what₂.ft σ) s) *
        qn A (InfinitePlace.mk s) q ^ 2 ≤
      Formalism.HermitianLatticesTheory.normAt D.div.RR.b D.div.RR.X (InfinitePlace.mk s) x ^ 2 ∧
    Formalism.HermitianLatticesTheory.normAt D.div.RR.b D.div.RR.X (InfinitePlace.mk s) x ^ 2 ≤
      Z.kapR s * Real.exp (⨆ σ : Fin D.what₂.Drows, ∑ j ∈ SizeData₂.lifts D, Z.logLam j (D.what₂.ft σ) s) *
        qn A (InfinitePlace.mk s) q ^ 2

def PeterssonBoundAllEmbeddings (D : D7) (Z : DivX D) (A : AmbForm D (RowSide.sharp D)) : Prop := ∀ s, PeterssonBoundAtEmbedding D Z A s

def PeterssonBoundFixedEmbedding (D : D7) (Z : DivX D) (A : AmbForm D (RowSide.sharp D)) : Prop := PeterssonBoundAtEmbedding D Z A D.what₂.embLL

def DivisibilityLatticeMetricCondition (D : D7) (Z : DivX D) (A : AmbForm D (RowSide.sharp D)) (E : EigIdx D Z) : Prop := RRMetricDef D Z A E

def QPart {D : D7} {Z : DivX D} (A : AmbForm D (RowSide.sharp D)) (E : EigIdx D Z) (c : E.Pi) (q : (A.MtH D.what₂.mu0).V) : Prop :=
  A.jAmb D.what₂.mu0 q ∈ (RowSide.sharp D).V0 D.what₂.mu0 ∧
    (RowSide.sharp D).iota D.what₂.mu0 (A.jAmb D.what₂.mu0 q) ∈ EEcpart D E c

def EigensystemOrthogonality (D : D7) (Z : DivX D) (A : AmbForm D (RowSide.sharp D)) (E : EigIdx D Z) : Prop :=
  ∀ (v : InfinitePlace D.what₂.LL) (q : E.Pi → (A.MtH D.what₂.mu0).V), (∀ c, QPart A E c (q c)) →
    qn A v (∑ c, q c) ^ 2 = ∑ c, qn A v (q c) ^ 2

def DegreeNormalizationFormula (D : D7) (Z : DivX D) (A : AmbForm D (RowSide.sharp D)) (E : EigIdx D Z) : Prop :=
  ∀ (x : D.div.RR.V) (q : (A.MtH D.what₂.mu0).V), A.jAmb D.what₂.mu0 q ∈ D.what₂.V0 D.what₂.mu0 →
    D.jEE x = D.what₂.iota D.what₂.mu0 (A.jAmb D.what₂.mu0 q) →
    ∃ (xs : E.Pi → D.div.RR.V) (qs : E.Pi → (A.MtH D.what₂.mu0).V),
      (∀ c, QPart A E c (qs c) ∧ D.jEE (xs c) = (RowSide.sharp D).iota D.what₂.mu0 (A.jAmb D.what₂.mu0 (qs c))) ∧
      (∑ c, xs c) = x ∧ (∑ c, qs c) = q ∧
      ∀ c, (∀ σ, ftP E σ ≠ c) → ∀ v, qn A v (qs c) = 0

def PlancherelDifferenceBound (D : D7) (Z : DivX D) : Prop :=
  ∀ j ∈ SizeData₂.lifts D, ∀ π, D.what₂.isot j π ≠ ⊥ → ∀ s : D.what₂.LL →+* ℂ,
    Z.logLam j π (ComplexEmbedding.conjugate s) = Z.logLam j π s

def PeterssonMetricHypotheses (D : D7) (Z : DivX D) (A : AmbForm D (RowSide.sharp D)) : Prop :=
  PeterssonBoundFixedEmbedding D Z A ∧ (∃ E : EigIdx D Z, DivisibilityLatticeMetricCondition D Z A E ∧ EigensystemOrthogonality D Z A E ∧ DegreeNormalizationFormula D Z A E) ∧ 0 < D.what₂.Drows ∧ PlancherelDifferenceBound D Z

theorem sum_between {ι κ : Type} [Fintype ι] [Finite κ] [Nonempty κ] (f : κ → ι) (a : ι → ℝ) (n : ι → ℝ) (hn : ∀ i, 0 ≤ n i)
    (h0 : ∀ i, (∀ k, f k ≠ i) → n i = 0) (c : ℝ) (hc : 0 ≤ c) :
    c * Real.exp (⨅ k, a (f k)) * ∑ i, n i ≤ ∑ i, c * Real.exp (a i) * n i ∧
    ∑ i, c * Real.exp (a i) * n i ≤ c * Real.exp (⨆ k, a (f k)) * ∑ i, n i := by
  have hfin : (Set.range fun k => a (f k)).Finite := Set.finite_range _
  have key : ∀ i, c * Real.exp (⨅ k, a (f k)) * n i ≤ c * Real.exp (a i) * n i ∧
      c * Real.exp (a i) * n i ≤ c * Real.exp (⨆ k, a (f k)) * n i := by
    intro i
    by_cases hi : ∃ k, f k = i
    · obtain ⟨k, rfl⟩ := hi
      have h1 : (⨅ k', a (f k')) ≤ a (f k) := ciInf_le hfin.bddBelow k
      have h2 : a (f k) ≤ ⨆ k', a (f k') := le_ciSup hfin.bddAbove k
      constructor
      · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr h1) hc) (hn _)
      · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr h2) hc) (hn _)
    · push_neg at hi
      rw [h0 i hi]
      simp
  constructor
  · rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => (key i).1
  · rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => (key i).2

theorem isot_ne_bot {D : D7} (hR : Rows.IsotRank D.what₂) (hn : ∀ σ : Fin D.what₂.Drows, 0 < D.what₂.nRows0 (D.what₂.ft σ)) :
    ∀ σ : Fin D.what₂.Drows, ∀ j ∈ SizeData₂.lifts D, D.what₂.isot j (D.what₂.ft σ) ≠ ⊥ := by
  intro σ j hj hbot
  simp only [SizeData₂.lifts, Finset.mem_Icc] at hj
  have h1 := hR j hj.1 hj.2 (D.what₂.ft σ)
  rw [hbot, finrank_bot] at h1
  have h2 := hn σ
  omega

theorem logLamC_cOf {D : D7} {Z : DivX D} (E : EigIdx D Z) {j : ℕ} (hj : j ∈ SizeData₂.lifts D) (π : D.what₂.FT)
    (hπ : D.what₂.isot j π ≠ ⊥) (e : D.what₂.LL →+* ℂ) : logLamC E j (E.cOf π) e = Z.logLam j π e := by
  have hex : ∃ π', E.cOf π' = E.cOf π ∧ D.what₂.isot j π' ≠ ⊥ := ⟨π, rfl, hπ⟩
  unfold logLamC
  rw [dif_pos hex]
  exact E.lam_const j hj _ _ e hex.choose_spec.2 hπ hex.choose_spec.1

theorem all_embeddings_of_bounds {D : D7} {Z : DivX D} {A : AmbForm D (RowSide.sharp D)}
    (hI : ∀ σ : Fin D.what₂.Drows, ∀ j ∈ SizeData₂.lifts D, D.what₂.isot j (D.what₂.ft σ) ≠ ⊥)
    (h : PeterssonMetricHypotheses D Z A) : PeterssonBoundAllEmbeddings D Z A := by
  obtain ⟨h0, ⟨E, hm, ho, hd⟩, hD, hc⟩ := h

  have hLC : ∀ (c : E.Pi) (e : D.what₂.LL →+* ℂ), ∀ j ∈ SizeData₂.lifts D,
      logLamC E j c (ComplexEmbedding.conjugate e) = logLamC E j c e := by
    intro c e j hj
    unfold logLamC
    by_cases hh : ∃ π, E.cOf π = c ∧ D.what₂.isot j π ≠ ⊥
    · rw [dif_pos hh, dif_pos hh]
      exact hc j hj _ hh.choose_spec.2 e
    · rw [dif_neg hh, dif_neg hh]
  intro s
  by_cases hs : InfinitePlace.mk s = InfinitePlace.mk D.what₂.embLL
  · rcases InfinitePlace.mk_eq_iff.mp hs with h1 | h1
    · subst h1
      exact h0
    ·
      intro x q hq hx
      have h2 := h0 x q hq hx
      rw [← h1, InfinitePlace.mk_conjugate_eq, Z.kapR_conj] at h2
      have hinf : ∀ σ : Fin D.what₂.Drows,
          (∑ j ∈ SizeData₂.lifts D, Z.logLam j (D.what₂.ft σ) (ComplexEmbedding.conjugate s)) =
            ∑ j ∈ SizeData₂.lifts D, Z.logLam j (D.what₂.ft σ) s :=
        fun σ => Finset.sum_congr rfl fun j hj => hc j hj _ (hI σ j hj) s
      simp only [hinf] at h2
      exact h2
  · intro x q hq hx
    obtain ⟨xs, qs, hpart, hxs, hqs, hz⟩ := hd x q hq hx
    have hk : Z.kapR (InfinitePlace.mk s).embedding = Z.kapR s := by
      rcases InfinitePlace.embedding_mk_eq s with he | he
      · rw [he]
      · rw [he]
        exact Z.kapR_conj s
    have hl : ∀ c, ∀ j ∈ SizeData₂.lifts D,
        logLamC E j c (InfinitePlace.mk s).embedding = logLamC E j c s := by
      intro c j hj
      rcases InfinitePlace.embedding_mk_eq s with he | he
      · rw [he]
      · rw [he]
        exact hLC c s j hj
    have hmet : Formalism.HermitianLatticesTheory.normAt D.div.RR.b D.div.RR.X (InfinitePlace.mk s) x ^ 2 =
        ∑ c, Z.kapR s * Real.exp (∑ j ∈ SizeData₂.lifts D, logLamC E j c s) *
          qn A (InfinitePlace.mk s) (qs c) ^ 2 := by
      rw [← hxs, hm (InfinitePlace.mk s) hs xs qs (fun c => (hpart c).1.1) (fun c => (hpart c).2)
        (fun c => by rw [(hpart c).2]; exact (hpart c).1.2), hk]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [Finset.sum_congr rfl (hl c)]
      try rfl
    have hqn : qn A (InfinitePlace.mk s) q ^ 2 = ∑ c, qn A (InfinitePlace.mk s) (qs c) ^ 2 := by
      rw [← hqs]
      exact ho _ qs (fun c => (hpart c).1)
    haveI : Nonempty (Fin D.what₂.Drows) := ⟨⟨0, hD⟩⟩
    have hsb := sum_between (ftP E) (fun c => ∑ j ∈ SizeData₂.lifts D, logLamC E j c s)
      (fun c => qn A (InfinitePlace.mk s) (qs c) ^ 2) (fun c => sq_nonneg _)
      (fun c hc' => by simp [hz c hc' (InfinitePlace.mk s)]) (Z.kapR s) (Z.kapR_pos s).le
    have hI' : ∀ σ, (∑ j ∈ SizeData₂.lifts D, logLamC E j (ftP E σ) s) =
        ∑ j ∈ SizeData₂.lifts D, Z.logLam j (D.what₂.ft σ) s :=
      fun σ => Finset.sum_congr rfl fun j hj => logLamC_cOf E hj _ (hI σ j hj) s
    simp only [hI'] at hsb
    rw [hmet, hqn]
    exact hsb

theorem fixed_embedding_of_all {D : D7} {Z : DivX D} {A : AmbForm D (RowSide.sharp D)} (h : PeterssonBoundAllEmbeddings D Z A) : PeterssonBoundFixedEmbedding D Z A := h D.what₂.embLL

def adm2 (D : D7) (L : SizeData₂ D) : Prop :=
  ∀ u (w : D.what₂.places.Pl) (φ : (D.div.Nu u).V), φ ∈ L.NuLat u →
    ∀ F ∈ (D.what₂.Mtilde (D.what₂.muAt w)).carrier, F ∈ D.what₂.V0 (D.what₂.muAt w) →
      ∃ y : D.what₂.LL, D.what₂.embLL y = D.what₂.perCol u (D.what₂.muAt w) (D.jN u φ) F ∧
        (y = 0 ∨ ((⌊ur D w (L.sg u w)⌋ : ℤ) : ℝ) ≤ (vAdd (D.plEq w) y : ℝ))

def UnroundedValuationBound (D : D7) (L : SizeData₂ D) : Prop :=
  ∀ u (w : D.what₂.places.Pl) (φ : (D.div.Nu u).V), φ ∈ L.NuLat u →
    ∀ F ∈ (D.what₂.Mtilde (D.what₂.muAt w)).carrier, F ∈ D.what₂.V0 (D.what₂.muAt w) →
      ∃ y : D.what₂.LL, D.what₂.embLL y = D.what₂.perCol u (D.what₂.muAt w) (D.jN u φ) F ∧
        (y = 0 ∨ ur D w (L.sg u w) ≤ (vAdd (D.plEq w) y : ℝ))

theorem valuation_bound_of_unrounded (D : D7) (L : SizeData₂ D) (h : UnroundedValuationBound D L) : adm2 D L := by
  intro u w φ hφ F hF hV
  obtain ⟨y, hy, h'⟩ := h u w φ hφ F hF hV
  exact ⟨y, hy, h'.imp_right fun h'' => (Int.floor_le _).trans h''⟩

def adm3 (D : D7) (L : SizeData₂ D) (Z : DivX D) (C : ℝ) : Prop :=
  ∀ j ∈ SizeData₂.lifts D, (Z.MjH j).lcv / (D.what₂.D0 : ℝ) ≤
    (∑ ρ : D.what₂.Tau, (((D.R.sigW j).1 : ℝ) - ((D.R.sigW j).2 : ℝ)) * wSz D j ρ * L.logOm) +
      C * L.B0 * Real.log (Real.log L.sc.x)

def ArchimedeanSignatureMatching (D : D7) (L : SizeData₂ D) (X : Loc D) (C Cabs : ℝ) : Prop :=
  ∃ (err : ℕ → D.what₂.places.Pl → ℝ) (fl : ℕ → ℕ → ℝ) (r : ℕ → D.what₂.places.Pl → ℝ),
    (∀ j l, 0 ≤ fl j l) ∧ (∀ j w, 0 ≤ r j w) ∧ (∀ j w, 0 ≤ X.Jx j w) ∧
    (∀ j w, err j w = fl j (D.what₂.places.resChar w) +
      (r j w + r j (D.what₂.places.conj w)) / (D.what₂.D0 : ℝ)) ∧
    (∀ w, D.what₂.muAt w ≠ D.what₂.mu0 →
      ∑ j ∈ SizeData₂.lifts D,
        (((D.what₂.Ij (D.what₂.muAt w) j w : ℝ) +
          (D.what₂.Ij (D.what₂.muAt w) j (D.what₂.places.conj w) : ℝ)) /
          (D.what₂.D0 : ℝ) - 2 * ur D w (L.F j w)) ≤
        ur D w ((∑ j ∈ SizeData₂.lifts D, err j w) + 2 / ((D.what₂.places.resChar w : ℝ) ^ 2))) ∧
    (∀ j ∈ SizeData₂.lifts D,
      Summable (fun w => SizeData₂.lwP w * ur D w (err j w + X.Jx j w)) ∧
      ∑' w, SizeData₂.lwP w * ur D w (err j w + X.Jx j w) ≤
        C * L.sc.x ^ (Cabs * L.sc.eps) * (L.B0 + L.Nc))

open Classical in

def adm5 (D : D7) (L : SizeData₂ D) (C Cabs : ℝ) : Prop :=
  ∀ j ∈ SizeData₂.lifts D, (∀ w, 0 ≤ D.what₂.etaJ j w) ∧
    (∑ w ∈ L.supp.filter (fun w => D.what₂.muAt w ≠ D.what₂.mu0), SizeData₂.lwP w * ur D w (D.what₂.etaJ j w : ℝ)) /
      (D.what₂.D0 : ℝ) ≤
      C * L.sc.x ^ (Cabs * L.sc.eps) * (L.B0 + L.Nc)

def adm6 (D : D7) (L : SizeData₂ D) (C : ℝ) : Prop :=
  ∀ j ∈ SizeData₂.lifts D, ∀ π, D.what₂.isot j π ≠ ⊥ →
    (∑ ρ : D.what₂.Tau, placeRankTwoOne.logHk (D.R.sigW j).1 (aPlus D j ρ)) -
        C * (D.R.f : ℝ) * (D.R.N D.R.m : ℝ) ^ 2 * L.La ≤ Real.log (D.what₂.lamP D.what₂.mu0 j π)

def LogLambdaEstimatesOnComponents (D : D7) (L : SizeData₂ D) (Z : DivX D) (C : ℝ) : Prop :=
  ∀ j ∈ SizeData₂.lifts D, ∀ π, D.what₂.isot j π ≠ ⊥ → ∀ e : D.what₂.LL →+* ℂ,
    (∑ ρ : D.what₂.Tau, placeRankTwoOne.logHk (D.R.sigW j).1 (aPlus D j ρ)) -
        C * (D.R.f : ℝ) * (D.R.N D.R.m : ℝ) ^ 2 * L.La ≤ Z.logLam j π e ∧
    |Z.logLam j π e - placeRankTwoOne.sumHk D j| ≤ C * D.R.f * (D.R.nV : ℝ) ^ 2 *
      Real.log (L.sc.b * D.host.rdE * ((D.host.g 0 : ℝ) * D.host.g 1) * D.R.nV)

def ConjugateLowerBound (D : D7) (L : SizeData₂ D) (Z : DivX D) (C : ℝ) : Prop :=
  ∀ j ∈ SizeData₂.lifts D, ∀ π, D.what₂.isot j π ≠ ⊥ → ∀ e : D.what₂.LL →+* ℂ, L6lo D L C j ≤ Z.logLam j π e

def pSq (D : D7) (u : D.what₂.Word) (h : (D.fm u).PRat) (s : D.what₂.LL →+* ℂ) : ℝ :=
  Formalism.HN.opNormAt ((D.fm u).lat D.R.m).b ((D.fm u).lat D.R.m).X (D.fm u).ptLat.b (D.fm u).ptLat.X
    (InfinitePlace.mk s) ((D.fm u).PtL h) ^ 2

def adm7 (D : D7) (L : SizeData₂ D) (C : ℝ) : Prop :=
  (∀ u i (h : (D.fm u).KRat i), i + 1 ≤ D.R.m → placeRankTwoOne.kLe D u i h (kernelPlaceMeanBound D L C u (i + 1))) ∧
  (∀ u (h : (D.fm u).PRat) s, pSq D u h s ≤ Real.exp (SZbP D L C u)) ∧
  (∀ j ∈ SizeData₂.lifts D, ∀ ρ,
    (∀ i i', i ≤ i' → i' < (D.R.sigW j).1 → aPlus D j ρ i' ≤ aPlus D j ρ i) ∧
    ∀ i, D.R.k - 1 ≤ i → i < (D.R.sigW j).1 → aPlus D j ρ i ≤ L.etaSz)

def KernelRationality (D : D7) : Prop := (∀ u, ∀ i < D.R.m, (D.fm u).KRat i) ∧ ∀ u, (D.fm u).PRat

def LowKernelRationality (D : D7) : Prop := ∀ u, ∀ i, i + 3 ≤ D.R.m → (D.fm u).KRat i

def HighKernelRationality (D : D7) : Prop := ∀ u, ∀ i < D.R.m, D.R.m < i + 3 → (D.fm u).KRat i

theorem kernel_rationality_iff (D : D7) : KernelRationality D ↔ LowKernelRationality D ∧ HighKernelRationality D ∧ ∀ u, (D.fm u).PRat := by
  unfold KernelRationality LowKernelRationality HighKernelRationality
  constructor
  · rintro ⟨hK, hP⟩
    exact ⟨fun u i hi => hK u i (by omega), fun u i hi _ => hK u i hi, hP⟩
  · rintro ⟨hL, hT, hP⟩
    refine ⟨fun u i hi => ?_, hP⟩
    by_cases h3 : i + 3 ≤ D.R.m
    · exact hL u i h3
    · exact hT u i hi (by omega)

def adm8 (D : D7) (L : SizeData₂ D) (Z : DivX D) (P : BaseLevelRowSide D) (CF CT : ℝ) : Prop :=
  P.principalHermitianLattice.muMax + meanE D (fun e => Real.log (Z.kapR e)) ≤ L.sc.x ^ CF * L.sc.b + CT * D.R.m * lam0 D ∧
  D.div.RR.muMax + meanE D (fun e => Real.log (Z.kapR e)) ≤ L.sc.x ^ CF * L.sc.b

def KapConj {D : D7} (Z : DivX D) : Prop :=
  ∀ e : D.what₂.LL →+* ℂ, Z.kapR (ComplexEmbedding.conjugate e) = Z.kapR e

def adm9 (D : D7) (P : BaseLevelRowSide D) (C : ℝ) : Prop := Rows.AIntegral D.what₂ ∧ P.s.AIntegral ∧ FactDGam D C

def TwistedIndexValuationBound (D : D7) (X : Loc D) : Prop :=
  ∀ j ∈ SizeData₂.lifts D, ∀ w, D.what₂.muAt w ≠ D.what₂.mu0 →
    (D.what₂.jw (D.what₂.muAt w) j w : ℝ) ≤ ur D w ((D.what₂.etaJ j w : ℝ) + (D.what₂.D0 : ℝ) *
      (X.Jx j w + (padicValNat (D.what₂.places.resChar w) (D.mem D.u₀).C.DGam : ℝ) +
        (if ∃ i, D.what₂.places.resChar w = D.host.g i then 2 * (D.R.f : ℝ) * (D.R.N D.R.m : ℝ) ^ 2 else 0)))

def OrthonormalBoundsChoice (D : D7) (L : SizeData₂ D) (C Cabs : ℝ) : Prop := ∃ X : Loc D, ArchimedeanSignatureMatching D L X C Cabs ∧ TwistedIndexValuationBound D X

def adm10 (D : D7) (P : BaseLevelRowSide D) (C : ℝ) : Prop :=
  0 < C ∧ C * ((D.R.f : ℝ) * D.R.r / (min (D.host.g 0) (D.host.g 1) : ℕ)) ≤ 1 / 3 ∧ LemmaT D P C ∧
  |Real.log (kapSharp D) - Real.log P.kap0| ≤ C * D.R.m * lam0 D

def adm11 (D : D7) (L : SizeData₂ D) (C : ℝ) : Prop :=
  ∀ u, ∀ j ∈ SizeData₂.lifts D,
    |(∑ w ∈ L.supp, SizeData₂.sz w (L.E u j w)) -
        (∑ t : D.host.TT, (L.aT t : ℝ)) * Real.log (∏ g ∈ L.gTypes, (g : ℝ))| ≤ C * L.B0 ∧
    ∑ w ∈ L.supp.filter (fun w => D.what₂.places.resChar w ∉ L.gTypes), |SizeData₂.sz w (L.E u j w)| ≤
      C * L.B0

def adm12 (D : D7) (L : SizeData₂ D) : Prop :=
  ∀ u (w : D.what₂.places.Pl), D.what₂.places.resChar w ≠ (D.mem u).A.T →
    ∀ (φ : (D.div.Nu u).V), φ ∈ MramL D u →
    ∀ F ∈ (D.what₂.Mtilde (D.what₂.muAt w)).carrier, F ∈ D.what₂.V0 (D.what₂.muAt w) →
      ∃ y : D.what₂.LL, D.what₂.embLL y = D.what₂.perCol u (D.what₂.muAt w) (D.jN u φ) F ∧
        (y = 0 ∨ ur D w (∑ j ∈ SizeData₂.lifts D, (L.F j w - L.E u j w)) ≤ (vAdd (D.plEq w) y : ℝ))

def adm13 (D : D7) : Prop :=
  ∃ V : D.what₂.EE ≃ₗᵢ[ℂ] D.what₂.EE, ∀ u, ∃ a : ℂ, a ≠ 0 ∧
    ∃ U : D.what₂.Mu u ≃ₗᵢ[ℂ] D.what₂.Mu u, ∀ φ F, D.what₂.Bu u φ F = a * D.besS u (U φ) (V F)

def adm14 (D : D7) (L : SizeData₂ D) : Prop := NprimeDef D L

def adm15 (D : D7) : Prop := RRDef D

def ZeroGainAbove {D : D7} (L : SizeData₂ D) : Prop := L.ZeroAbove

def TWAt (D : D7) (N : NChoice D) (T : ThData D) : Prop :=
  Formalism.MainNotions.TwConjAt D N ∧
    ∃ (N0 : D.ntw.Tw → ℕ) (S : ∀ (i' : D.ntw.Tw) (j : ℕ) (b : Bool), Finset (D.nexp.Dat i' j b)),
      Formalism.MainNotions.TwGoodAt D N ⟨Formalism.MainNotions.twEOf T, N0, S⟩

theorem twAt_of_twGood {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (h : Formalism.MainNotions.TwGood Fm) :
    ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (hx : Fm.x1 < x) (i : Fm.Ix x), TWAt (Fm.D x i) (Fm.ex x hx i).nch (Fm.ex x hx i).xd := by
  obtain ⟨x0, hx0⟩ := h
  exact ⟨x0, fun x hx hx1 i => hx0 x hx hx1 i⟩

def sExpl (D : D7) (L : SizeData₂ D) (Z : DivX D) (C : ℝ) : ℝ := sFrame D.div.Nu (hExpl6 D L Z C)

def Conclusion1 (D : D7) (L : SizeData₂ D) (Z : DivX D) (N : NChoice D) (T : ThData D) (Csz C Cabs : ℝ) : Prop :=
    D.div.OneMapIntoCC ∧
    (∀ u, D.div.Bk u ≠ 0 →
      Formalism.HN.htMap (D.div.Nu u).b (D.div.Nu u).X D.div.RR.dualB D.div.RR.dualX (D.div.Bk u) ≤
      hExpl6 D L Z Csz u) ∧
    (TWAt D N T → ∀ u, D.div.RR.muDual + hExpl6 D L Z Csz u - L.Fo ≤ L.MAIN u + C * nTT D * L.sc.a * L.La +
      C * (D.R.m : ℝ) * (L.B0 + L.Nc) * L.sc.x ^ (Cabs * L.sc.eps)) ∧
    (∀ u u', |(hExpl6 D L Z Csz u + (∑ t : D.host.TT, (L.aT t : ℝ)) * Real.log ((D.mem u).A.T : ℝ)) -
      (hExpl6 D L Z Csz u' + (∑ t : D.host.TT, (L.aT t : ℝ)) * Real.log ((D.mem u').A.T : ℝ))| ≤
      C * (nTT D * L.sc.a * L.La + (D.R.m : ℝ) * L.B0))

def FrameNumberBound (D : D7) (L : SizeData₂ D) (Z : DivX D) (Csz CH : ℝ) : Prop :=
  sExpl D L Z Csz + D.div.RR.muMax ≤ L.sc.x ^ CH * L.sc.b

section ThmF

variable {K : Type} [Field K] [NumberField K] [StarRing K]

def frd (A : HLat K) : ℝ := (A.rank : ℝ)

def frh (c : InfinitePlace K → ℝ) : ℝ :=
  (1 / (Fintype.card (InfinitePlace K) : ℝ)) * ∑ σ, Real.log (c σ)

def frs {I : Type} [Fintype I] (N : I → HLat K) (c : I → InfinitePlace K → ℝ) : ℝ :=
  (∑ i, frd (N i) * ((N i).mu - frh (c i))) / (∑ i, frd (N i))

def fru {I : Type} [Fintype I] [Nonempty I] (N : I → HLat K) (c : I → InfinitePlace K → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun i => (N i).muMax - frh (c i)) - frs N c

def frB (cc : HLat K) {I : Type} (N : I → HLat K) (B : ∀ i, (N i).V →ₗ[K] cc.V) (v : InfinitePlace K)
    {κ : Type} [Fintype κ] (Y : ∀ i, Matrix (N i).ι (N i).ι ℂ) (Y' : Matrix cc.ι cc.ι ℂ)
    (G : ∀ i, Matrix κ (N i).ι ℂ) (i : I) :
    EuclideanSpace ℂ (N i).ι →ₗ[ℂ] EuclideanSpace ℂ (cc.ι ⊕ κ) :=
  Matrix.toEuclideanLin (Matrix.fromRows
    (Y'⁻¹ * (LinearMap.toMatrix (N i).b cc.b (B i)).map v.embedding * Y i) (G i))

end ThmF

def Conclusion2 : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
    (cc : HLat K) (I : Type) [Fintype I] [Nonempty I] (N : I → HLat K)
    (B : ∀ i, (N i).V →ₗ[K] cc.V) (c : I → InfinitePlace K → ℝ) (HH : ℝ)
    (v : InfinitePlace K) (κ : Type) [Fintype κ]
    (Y : ∀ i, Matrix (N i).ι (N i).ι ℂ) (Y' : Matrix cc.ι cc.ι ℂ) (G : ∀ i, Matrix κ (N i).ι ℂ)
    (ga : I → ℝ) (del η e : ℝ),
    cc.Good → (∀ i, (N i).Good) → 0 < cc.rank → (∀ i, 0 < (N i).rank) →
    (∀ i, (N i).L.map ((B i).restrictScalars (𝓞 K)) ≤ cc.L) →
    (∀ i σ, Formalism.HN.opNormAt (N i).b (N i).X cc.b cc.X σ (B i) ^ 2 ≤ c i σ) →
    0 ≤ fru N c → frs N c - cc.muMin ≤ HH → 0 < HH →
    ((Fintype.card (cc.ι ⊕ κ) : ℕ) : ℝ) ≤ (cc.rank : ℝ) / (1 - del) →
    (∀ i, IsUnit (Y i).det) → IsUnit Y'.det → (∀ i, 0 < ga i) →
    (LinearMap.trace ℂ _ (Formalism.CorankShareLayerCake.FR.frQ ga (frB cc N B v Y Y' G) ∘ₗ
        Formalism.CorankShareLayerCake.FR.frQ ga (frB cc N B v Y Y' G))).re ≤
      (1 + η) * (LinearMap.trace ℂ _ (Formalism.CorankShareLayerCake.FR.frQ ga (frB cc N B v Y Y' G))).re ^ 2 /
        ((Fintype.card (cc.ι ⊕ κ) : ℕ) : ℝ) →
    (∑ i, Formalism.CorankShareLayerCake.FR.hs2 (Formalism.CorankShareLayerCake.FR.frK (ga i) (frB cc N B v Y Y' G i) - LinearMap.id)) ≤
      e * ∑ i, frd (N i) →
    e ≤ 1 / 4 →
    frs N c - Real.log (Fintype.card I : ℝ) -
        (1 - del)⁻¹ * (4 * fru N c * Real.log (1 + HH / fru N c) + (η + 4 * Real.sqrt e) * HH) ≤
      cc.mu

def AdmA (D : D7) (L : SizeData₂ D) (Z : DivX D) (P : BaseLevelRowSide D) (A : AmbForm D (RowSide.sharp D)) (C Cabs CF CT Csz : ℝ) : Prop :=
  adm1 D Z P ∧ PeterssonMetricHypotheses D Z A ∧ adm2 D L ∧ adm3 D L Z C ∧ OrthonormalBoundsChoice D L C Cabs ∧ adm5 D L C Cabs ∧ adm6 D L C ∧ LogLambdaEstimatesOnComponents D L Z C ∧
  ConjugateLowerBound D L Z Csz ∧ adm7 D L Csz ∧ KernelRationality D ∧ adm8 D L Z P CF CT ∧ adm9 D P C ∧ adm10 D P CT ∧ adm11 D L C ∧ adm12 D L ∧
  adm13 D ∧ adm14 D L ∧ adm15 D ∧ ZeroGainAbove L

def AdmAF {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (Cabs CF Csz : ℝ) : Prop :=
  ∃ C CT x0 : ℝ, ∀ x, x0 ≤ x → ∀ hx : Fm.x1 < x, ∀ i : Fm.Ix x,
    AdmA (Fm.D x i) (Fm.L x i) (Fm.X x i) (Fm.ex x hx i).p0 (Fm.ex x hx i).amb C Cabs CF CT Csz

def familyUnitInput {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop :=
  ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ hx : Fm.x1 < x, ∀ i : Fm.Ix x, adm1 (Fm.D x i) (Fm.X x i) (Fm.ex x hx i).p0

def ComplementTwoFamily {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop :=
  ∃ C x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, adm11 (Fm.D x i) (Fm.L x i) C

def ComplementCountFamily {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop := ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, adm13 (Fm.D x i)

def vanishing_above_threshold {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop := ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, ZeroGainAbove (Fm.L x i)

def Conclusion1Family {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (Csz Cabs : ℝ) : Prop :=
  ∃ C x0 : ℝ, ∀ x, x0 ≤ x → ∀ hx : Fm.x1 < x, ∀ i : Fm.Ix x,
    Conclusion1 (Fm.D x i) (Fm.L x i) (Fm.X x i) (Fm.ex x hx i).nch (Fm.ex x hx i).xd Csz C Cabs

def FrameNumberBoundFamily {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (Csz CH : ℝ) : Prop :=
  ∃ x0 : ℝ, ∀ x, x0 ≤ x → Fm.x1 < x → ∀ i : Fm.Ix x, FrameNumberBound (Fm.D x i) (Fm.L x i) (Fm.X x i) Csz CH

def DivisionSideFamily {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (Cabs CF Cabs' : ℝ) : Prop :=
  AdmAF Fm Cabs CF Fm.Csz → Conclusion1Family Fm Fm.Csz Cabs'

open Formalism.FrobeniusOrbits

def MuH (D : D7) (u : D.what₂.Word) : HLat D.what₂.LL := { D.div.Nu u with L := MramL D u }

def hclP (e p : ℕ) : HGrp e :=
  if h : Nat.Coprime p (2 ^ (e + 2)) then hcl e (ZMod.unitOfCoprime p h) else 1

open Classical in

def wAt (D : D7) (j : ℕ) (g : D.R.GG) : ℝ :=
  if h : g ∈ D.R.Psi then wSz D j (D.eTau.symm ⟨g, h⟩) else 0

section Derived

variable {D : D7} (L : SizeData₂ D)

def IOsum : ℝ := ∑ w ∈ L.supp, SizeData₂.lwP w * (D.what₂.places.ramIdx w : ℝ) * (L.io w : ℝ)

def Ta : ℝ := ∑ w ∈ L.supp, SizeData₂.sz w (L.tau w)

def Exc (u : D.what₂.Word) (p : ℕ) : Prop :=
  p ∣ D.host.condN * (∏ g ∈ L.gTypes, g) * (D.mem u).A.T

def askPrimes (a : ℤ) : Finset ℕ := (Finset.range (a.toNat + 1)).filter Nat.Prime

open Classical in

def ASK : ℝ :=
  ∑ j ∈ SizeData₂.lifts D, ∑ t : D.host.TT,
    ((∑ p ∈ (askPrimes (L.aT t)).filter (fun p => InertK D p),
        2 * Real.log p * L.vonMangoldtClassSum j t p) +
      Real.log D.host.d * ZetaZeroFreeRegion.askD D (L.aT t : ℝ) (wAt D j) (D.R.tau1 (t : D.R.A)))

def MainC : ℝ :=
  ∑ j ∈ SizeData₂.lifts D, ∑ t : D.host.TT, (L.aT t : ℝ) *
    (Real.log (L.aT t) - 1 - Real.eulerMascheroniConstant + L.logDerivativeAtOne -
      (1 / (D.R.f : ℝ)) * ∑ ρ : D.what₂.Tau, Real.log (wSz D j ρ))

def LoU (C : ℝ) (u : D.what₂.Word) : ℝ :=
  C * IOsum L + C * nTT D * D.R.m * (L.sc.a / D.R.k + L.sc.b') * Real.log ((D.mem u).A.T : ℝ) +
    C * L.sc.X'' D.R.n + 1

def leastPowerExponent (p : ℕ) : ℕ := ⌈Real.logb p ((D.R.k : ℝ) ^ 2 * L.sc.x ^ (3 * Scale.A))⌉₊ + 1

def groupRank : ℕ := ⌈8 * ((2 + 8 * L.sc.eps) + 2) / L.sc.eps⌉₊ + 1

def floorTermOfPrime (C : ℝ) (p : ℕ) : ℝ :=
  C * (D.R.f : ℝ) * (D.R.N D.R.m : ℝ) ^ 2 * Real.logb p L.sc.a +
    C * (D.R.f : ℝ) * (Real.logb p L.sc.a) ^ 2

open Classical in

def lowerTermOfPrime (C bo : ℝ) (p : ℕ) : ℝ :=
  (C * (L.Sc + D.R.k + L.etaSz) * Real.logb p (2 * L.sc.a)) +
  (if D.host.cls p = PrimeClass.inertClass then
      (if (p : ℝ) < L.sc.p0 D.R.k then C * (groupRank L : ℝ) * L.sc.b' * Real.log L.sc.x
       else if (p : ℝ) < L.sc.X' then
         C * (L.sc.b' / L.sc.x + L.etaSz + L.Sc + (L.sc.w'' D.R.n + D.R.t) * Real.log L.sc.x /
           L.sc.delta1) + bo
       else 0) else 0) +
  (if D.host.cls p = PrimeClass.inertClass ∧ (p : ℝ) < L.sc.X' then
      C * Real.log L.sc.x * (L.LaG * L.sc.a / ((p : ℝ) * D.R.k) +
        (if (p : ℝ) < L.sc.p0 D.R.k then L.sc.a * (p : ℝ) ^ (-(leastPowerExponent L p : ℝ))
         else L.sc.a / (p : ℝ) ^ 2))
      else 0)

end Derived

section admitted

variable {D : D7} {L : SizeData₂ D}

def VVp (Gi : G.Inst D L) (K : G.Consts) (p : ℕ) : Finset (G.HH D) := G.VV Gi K (G.aL L) (G.bL L) p

def DropDef (Gi : G.Inst D L) (K : G.Consts) (Cr : ℝ) : Prop :=
  ∀ p : ℕ, p.Prime → (p ∈ L.drop ↔ NoGain Gi K Cr p ∧ ∀ u, p ≠ (D.mem u).A.T)

def Defs (Gi : G.Inst D L) (K : G.Consts) (Cr : ℝ) : Prop :=
  NprimeDef D L ∧ NuDef D L ∧ DropDef Gi K Cr ∧ ∀ w, G.ParametersFill Gi K w

def adm16 (Gi : G.Inst D L) (K : G.Consts) (Cr : ℝ) : Prop := Defs Gi K Cr ∧ D.NuFull

def adm18 (Gi : G.Inst D L) (K : G.Consts) : Prop :=
  (∀ u w, D.what₂.places.resChar w ≠ (D.mem u).A.T →
    LocLe (D.plEq w) ⌊ur D w (L.tau w)⌋₊ (L.NuLat u) (MramL D u) ∧
    (L.lenMN u w : ℝ) ≤ (D.duS u : ℝ) * (L.tau w + L.io w) ∧
    (VVp Gi K (D.what₂.places.resChar w) = ∅ → L.tau w = 0 ∧ L.io w = 0 ∧ L.lenMN u w = 0)) ∧
  (∀ p, ∀ t0 ∈ VVp Gi K p,
    G.Sv Gi K (G.aL L) (G.bL L) p t0 ≤ 2 * (D.R.m : ℝ) * (G.Nv Gi p t0 : ℝ) * L.sc.a / p)

end admitted

section Adm2

variable {D : D7} (L : SizeData₂ D)

def adm19 (C bo : ℝ) : Prop :=
  ∀ w, (D.what₂.places.resChar w : ℝ) ≤ L.sc.X'' D.R.n → InertK D (D.what₂.places.resChar w) →
    (∀ u, ¬ Exc L u (D.what₂.places.resChar w)) →
    (∀ j ∈ SizeData₂.lifts D, 0 ≤ L.gain j w ∧
      L.gain j w ≤ 4 * nTT D * L.sc.a / (D.what₂.places.resChar w : ℝ)) ∧
    (∑ j ∈ SizeData₂.lifts D, ∑ t ∈ L.TTw w,
        (L.vonMangoldtClassSum j t (D.what₂.places.resChar w) - lowerTermOfPrime L C bo (D.what₂.places.resChar w))) -
      (D.R.m : ℝ) * floorTermOfPrime L C (D.what₂.places.resChar w) ≤
      (∑ j ∈ SizeData₂.lifts D, L.gain j w) - L.tau w

end Adm2

section Adm3

variable {D : D7} {L : SizeData₂ D}

def posOn (D : D7) (h t0 : G.HH D) (T : Finset (G.HH D)) : Finset (Fin (addOrderOf h)) :=
  Finset.univ.filter (fun i => t0 + (i : ℕ) • h ∈ T)

def BadOrb (Gi : G.Inst D L) (h t : G.HH D) (T : Finset (G.HH D)) : Prop :=
  ¬ G.IsGoodOrbit (addOrderOf h) (posOn D h (Gi.bs h t) T) (G.L2 D L.sc) (G.KG L.sc) (G.rG L.sc) L.sc.delta1
    (G.hG L.sc) L.sc.x

open Classical in

def adm20 (Gi : G.Inst D L) (K : G.Consts) (C : ℝ) : Prop :=
  G.ServedOrbitsContained Gi K (G.aL L) (G.bL L) ∧
  G.rhoB D K L.sc ≤ L.sc.x ^ (-2 : ℝ) ∧
  (∀ h : G.HH D, L.sc.x ^ (L.sc.eps / 4) ≤ (addOrderOf h : ℝ) → ∀ t : G.HH D,
    (∑ T : Finset (G.HH D), if t ∈ T ∧ BadOrb Gi h t T then bern L.sc.delta1 T else 0) ≤
      (C * L.sc.x ^ (-2 : ℝ)) * L.sc.delta1)

end Adm3

section Adm4

variable {D : D7} (L : SizeData₂ D)

def adm21 (C0 : ℝ) : Prop :=
  (∀ u, C0⁻¹ ≤ (D.duS u : ℝ) * (D.mem u).A.GamP ^ 2 / D.what₂.Dstar ∧
    (D.duS u : ℝ) * (D.mem u).A.GamP ^ 2 / D.what₂.Dstar ≤ C0) →
  ∃ eta0 eta1 e0 : ℝ, 0 ≤ eta0 ∧ 0 ≤ eta1 ∧ 0 ≤ e0 ∧
    eta0 ≤ Real.exp (-(L.sc.x ^ (L.sc.eps / 8))) ∧ eta1 ≤ Real.exp (-(L.sc.x ^ (L.sc.eps / 8))) ∧
    Real.sqrt e0 ≤ Real.exp (-(L.sc.x ^ (L.sc.eps / 8))) ∧
    (∀ u u', u ≠ u' → SizeData₂.hsSq L u u' ≤ (1 + eta0) * (D.duS u : ℝ) * (D.duS u' : ℝ) / D.what₂.Dstar) ∧
    (∀ u, Formalism.MainNotions.S.hsNormSq (Formalism.MainNotions.S.KD D u u - ContinuousLinearMap.id ℂ (D.s.Cu u)) ≤ e0 * (D.duS u : ℝ)) ∧
    (D.what₂.Dall : ℝ) ≤ (1 + eta1) * D.what₂.Dstar

def adm22 : Prop := D.what₂.delp ≤ Real.exp (-(L.sc.x ^ (L.sc.ez / 7)))

def adm23 : Prop :=
  haveI : NeZero D.host.d := ⟨D.host.hyp.2.1.ne_zero⟩
  (∃ χ : DirichletCharacter ℂ D.host.d, (∀ n : ℕ, χ n = ((jacobiSym (n : ℤ) D.host.d : ℤ) : ℂ)) ∧
    ((L.logDerivativeAtOne : ℝ) : ℂ) = deriv (DirichletCharacter.LFunction χ) 1 / DirichletCharacter.LFunction χ 1) ∧
  |L.logOm| ≤ L.La

def FrobeniusExpansionCongruence (C : ℝ) : Prop :=
  ∀ u,
    (-(∑ t : D.host.TT, ((L.aT t : ℝ) / D.R.k) * Real.log ((D.mem u).A.T : ℝ)) -
        C * nTT D * L.sc.a * Real.log D.R.k -
        C * D.R.f * D.R.k * (L.sc.b' + L.Sc) * Real.log D.R.k -
        C * D.R.f * L.Sc * Real.log ((D.mem u).A.T : ℝ) -
        C * D.R.f * (D.R.k : ℝ) ^ 2 * L.sc.L ≤ ((D.fm u).lat 0).mu) ∧
    ((D.fm u).lat 0).muMax ≤ C * nTT D * L.sc.a * Real.log (D.R.k * D.host.v) +
      C * D.R.f * (L.sc.b' + L.Sc) * (D.R.k * Real.log (D.R.k * D.host.v) +
        Real.log ((D.mem u).A.T : ℝ)) + C * D.R.f * (D.R.k : ℝ) ^ 2 * L.sc.L

def HerrExtensionClause (C : ℝ) : Prop :=
  (∀ u,
    C⁻¹ ≤ (D.duS u : ℝ) * (D.mem u).A.GamP ^ 2 / (D.mem u).A.Dstar ∧
    (D.duS u : ℝ) * (D.mem u).A.GamP ^ 2 / (D.mem u).A.Dstar ≤ C ∧
    Real.log ((D.mem u).A.T : ℝ) ≤ C * D.R.m * L.sc.L ∧
    (∑ j ∈ SizeData₂.lifts D, (1 / (D.R.f : ℝ)) *
        ∑ ρ : D.what₂.Tau, Real.log (wSz D j ρ * D.host.v / Real.pi)) +
      (D.R.m : ℝ) * (∑ g ∈ L.gTypes, Real.log g) -
      C * (L.sc.L + (D.R.m : ℝ) ^ 2 * L.sc.L / D.R.k) -
      2 * Real.log (D.mem u).A.GamP / ((D.R.f : ℝ) * D.R.k) ≤ Real.log ((D.mem u).A.T : ℝ)) ∧
  (∀ u u', |Real.log (D.mem u).A.Xu - Real.log (D.mem u').A.Xu| ≤ C * Real.log D.R.k) ∧
  Fintype.card D.what₂.Word ≤ 2 ^ (D.R.k - 2)

open Classical in

def adm26 (C : ℝ) : Prop :=
  ∀ u,
    ((D.mem u).A.du : ℝ) = (1 - 1 / (((D.mem u).A.T : ℝ) - 1)) ^ D.R.f * (D.duS u : ℝ) ∧
    (MuH D u).mu = ((D.fm u).lat 0).mu -
      (D.R.f : ℝ) * Real.log (((D.mem u).A.T : ℝ) - 1) / (((D.mem u).A.T : ℝ) - 2) ∧
    (MuH D u).muMax ≤ ((D.fm u).lat 0).muMax ∧
    (∀ w, D.what₂.places.resChar w = (D.mem u).A.T → LocLe (D.plEq w) 0 (L.NuLat u) (MramL D u)) ∧
    ∀ S : Finset D.what₂.places.Pl, (∀ w ∈ S, D.what₂.places.resChar w = (D.mem u).A.T) →
      (∑ w ∈ S, SizeData₂.sz w (L.lenMN u w)) / ((D.mem u).A.du : ℝ) ≤
        C * nTT D * D.R.m * (L.sc.a / D.R.k + L.sc.b') * Real.log ((D.mem u).A.T : ℝ)

end Adm4

section Adm5

variable {D : D7} {L : SizeData₂ D}

def HerrCocycleExtensionClass (Gi : G.Inst D L) (K : G.Consts) (C bo : ℝ) : Prop :=
  (∀ p : ℕ, (p : ℝ) < L.sc.X' →
    (∀ t0 ∈ VVp Gi K p,
      ((⌈G.tv Gi K (G.aL L) (G.bL L) p t0⌉₊ : ℕ) : ℝ) ≤ C * (G.Nv Gi p t0 : ℝ) * L.sc.a / (p : ℝ) ∧
      (G.Dp K L p : ℝ) ≤ C * (G.Nv Gi p t0 : ℝ) * L.sc.a / (p : ℝ)) ∧
    (VVp Gi K p ≠ ∅ → (Gi.ep p : ℝ) ≤ C * D.R.f * (D.R.k : ℝ) ^ 2 * Real.logb p L.sc.a)) ∧
  Ta L ≤ C * D.R.m * nTT D * L.sc.a * Real.log L.sc.X' + bo ∧
  (∀ u p, p.Prime → Exc L u p → p = D.host.d ∨ ¬ InertK D p)

def TwistConductorsSplit (D : D7) (N : NChoice D) : Prop :=
  ∀ w, D.what₂.muAt w ≠ D.what₂.mu0 → ∀ v ∈ N.Q w,
    IsSplitPl D.host v ∧ v ∉ placesOver D.host.E (D.what₂.places.resChar w)

def FontaineFormalProperties (Gi : G.Inst D L) (K : G.Consts) : Prop := G.MeanKappaBound Gi K

end Adm5

def HostOrbitConditions : Prop := HostOrbits ∧ HostOrbitsPlaces ∧ HostOrbitCount ∧ HostOrders

def OrderConsequences (D : D7) (C : ℝ) : Prop :=
  (∀ J l : ℕ, 1 ≤ J → l.Prime → l ≠ 2 → orderOf (hclP D.R.e l) ≤ J →
    (4 * 2 ^ D.R.e : ℝ) / J - 1 ≤ l) ∧
  (∀ (J : ℕ) (S : Finset ℕ), 1 ≤ J →
    (∀ l ∈ S, l.Prime ∧ l ≠ 2 ∧ orderOf (hclP D.R.e l) ≤ J) →
    ∑ l ∈ S, Real.log l / (l : ℝ) ^ 2 ≤ C * J ^ 2 * Real.log (2 ^ D.R.e) / ((2 : ℝ) ^ D.R.e) ^ 2) ∧
  (∀ (J : ℕ) (Y : ℝ) (S : Finset ℕ), 1 ≤ J → 1 ≤ Y →
    (∀ l ∈ S, l.Prime ∧ l ≠ 2 ∧ (l : ℝ) ≤ Y ∧ orderOf (hclP D.R.e l) ≤ J) →
    ∑ l ∈ S, Real.log l / (l : ℝ) ≤ C * J * Real.log (2 ^ D.R.e * Y) ^ 2 / (2 : ℝ) ^ D.R.e)

def TopsChoiceLemma : Prop := HostTops

def ChosenTopsCount {D : D7} (L : SizeData₂ D) : Prop := ChTT_at L

def FewBadOrbits {D : D7} {L : SizeData₂ D} (Gi : G.Inst D L) (Cb : ℝ) : Prop := ChBad_at Gi Cb

def LevelPrimesProviso {D : D7} (L : SizeData₂ D) (C0 : ℝ) : Prop := ChProviso_at L C0

def WordCount' {D : D7} (L : SizeData₂ D) (C0 CH : ℝ) : Prop := ChCode_at L C0 CH

def Conclusion4 {D : D7} {L : SizeData₂ D} (Gi : G.Inst D L) (K : G.Consts) (C Cr : ℝ) : Prop :=
  Defs Gi K Cr →
  ∀ u, (D.div.Nu u).muMax ≤ ((D.fm u).lat 0).muMax + L.Ga + L.Fo - L.Ee u + C * D.R.m * L.B0 ∧
    ((D.fm u).lat 0).mu + L.Ga + L.Fo - L.Ee u - LoU L C u ≤ (D.div.Nu u).mu

section Fam

variable {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps)

theorem defs_fam {x : ℝ} (hx : Fm.x1 < x) (i : Fm.Ix x) : Defs (Fm.Gx x i) Fm.GK Fm.Cr :=
  ⟨Fm.nprimeDef x hx i, Fm.nuDef x hx i, fun p hp => Fm.drop_iff x hx i p hp, fun w => Fm.fills x hx i w⟩

def Realizes {x : ℝ} (i : Fm.Ix x) (u0 : ℕ) (a b : ℕ → ℤ) : Prop :=
  (Fm.D x i).host.u0.val = u0 ∧ ∀ t : (Fm.D x i).host.TT,
    (Fm.L x i).aT t = a (t : (Fm.D x i).R.A).val ∧
      (Fm.L x i).bT t = b (t : (Fm.D x i).R.A).val

def AdmW {x : ℝ} (i0 : Fm.Ix x) (a b : ℕ → ℤ) : Prop :=
  ∀ t ∈ Fm.TTn x, Formalism.MainNotions.aWin (Fm.L x i0) (a t) ∧ (Fm.L x i0).sc.b' ≤ (b t : ℝ) ∧ (b t : ℝ) ≤ Fm.bTop x

def AmbientMetricLowerBound (x : ℝ) : Prop :=
  ∀ (i i' : Fm.Ix x) (a b : ℕ → ℤ) (u0 u0' : ℕ), Realizes Fm i u0 a b → Realizes Fm i' u0' a b → ∀ p : ℕ,
    (VVp (Fm.Gx x i) Fm.GK p).image Formalism.HC.Frame.A.val = (VVp (Fm.Gx x i') Fm.GK p).image Formalism.HC.Frame.A.val ∧
    G.Sig (Fm.Gx x i) Fm.GK (G.aL (Fm.L x i)) (G.bL (Fm.L x i)) p =
      G.Sig (Fm.Gx x i') Fm.GK (G.aL (Fm.L x i')) (G.bL (Fm.L x i')) p ∧
    G.tauP (Fm.Gx x i) Fm.GK (G.aL (Fm.L x i)) (G.bL (Fm.L x i)) p =
      G.tauP (Fm.Gx x i') Fm.GK (G.aL (Fm.L x i')) (G.bL (Fm.L x i')) p ∧
    G.ioP (Fm.Gx x i) Fm.GK (G.aL (Fm.L x i)) (G.bL (Fm.L x i)) p =
      G.ioP (Fm.Gx x i') Fm.GK (G.aL (Fm.L x i')) (G.bL (Fm.L x i')) p ∧
    ∀ t0 ∈ VVp (Fm.Gx x i) Fm.GK p, ∀ t0' : G.HH (Fm.D x i'), t0.val = t0'.val →
      G.kapv (Fm.Gx x i) Fm.GK (G.aL (Fm.L x i)) (G.bL (Fm.L x i)) p t0 =
        G.kapv (Fm.Gx x i') Fm.GK (G.aL (Fm.L x i')) (G.bL (Fm.L x i')) p t0' ∧
      G.Sv (Fm.Gx x i) Fm.GK (G.aL (Fm.L x i)) (G.bL (Fm.L x i)) p t0 =
        G.Sv (Fm.Gx x i') Fm.GK (G.aL (Fm.L x i')) (G.bL (Fm.L x i')) p t0'

def Conclusion5 (x C C' : ℝ) : Prop :=
  ∃ (i0 : Fm.Ix x) (a b : ℕ → ℤ), AdmW Fm i0 a b ∧ ∀ (i : Fm.Ix x) (u0 : ℕ), Realizes Fm i u0 a b →
    ASK (Fm.L x i) - (Fm.L x i).Ga ≤
      C * nTT (Fm.D x i) * (Fm.D x i).R.m * (Fm.L x i).sc.b * (Fm.L x i).sc.x ^ (C' * eps) ∧
    IOsum (Fm.L x i) ≤
      C * nTT (Fm.D x i) * (Fm.D x i).R.m * (Fm.L x i).sc.b * (Fm.L x i).sc.x ^ (C' * eps)

def PointsLemma (x C' : ℝ) : Prop :=
  ∃ (i0 : Fm.Ix x) (a b : ℕ → ℤ) (pt : Fin (Fm.D x i0).R.n → Fm.Ix x), AdmW Fm i0 a b ∧
    (∀ u0, Realizes Fm (pt u0) u0.val a b) ∧
    (∑ u0, ASK (Fm.L x (pt u0))) / ((Fm.D x i0).R.n : ℝ) ≤
      (∑ u0, MainC (Fm.L x (pt u0))) / ((Fm.D x i0).R.n : ℝ) +
        (Fm.L x i0).sc.x ^ (C' * eps) *
          (nTT (Fm.D x i0) * (Fm.L x i0).sc.a *
              (1 + ((Fm.D x i0).R.m : ℝ) ^ 2 / (Fm.D x i0).R.k) +
            (Fm.D x i0).R.m * ((Fm.L x i0).B0 + (Fm.L x i0).Nc))

end Fam

section FamV

open Filter

variable {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps)

def FullRankFamily : Prop := ∃ x0 : ℝ, ∀ x ≥ x0, Fm.x1 < x → ∀ i, adm16 (Fm.Gx x i) Fm.GK Fm.Cr

def G1Family : Prop := ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i, adm18 (Fm.Gx x i) Fm.GK

def LogTermFamily : Prop := ∃ (C x0 : ℝ) (δ : ℝ → ℝ), Tendsto δ atTop (nhds 0) ∧
  ∀ x ≥ x0, ∀ i, adm19 (Fm.L x i) C ((Fm.L x i).sc.b ^ δ x)

def G3BoundFamily : Prop := ∃ C x0 : ℝ, ∀ x ≥ x0, ∀ i, adm20 (Fm.Gx x i) Fm.GK C

def SplitProvisoFamily (C0 : ℝ) : Prop := ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i, adm21 (Fm.L x i) C0

def IrreducibilityFamily : Prop := ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i, adm22 (Fm.L x i)

def PeriodFamily' : Prop := ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i, adm23 (Fm.L x i)

def SlopesFamily : Prop := ∃ C x0 : ℝ, ∀ x ≥ x0, ∀ i, FrobeniusExpansionCongruence (Fm.L x i) C

def CountFamily : Prop := ∃ C x0 : ℝ, ∀ x ≥ x0, ∀ i, HerrExtensionClause (Fm.L x i) C

def LevelTFamily : Prop := ∃ C x0 : ℝ, ∀ x ≥ x0, ∀ i, adm26 (Fm.L x i) C

def AddedTermFamily : Prop := ∃ (C x0 : ℝ) (δ : ℝ → ℝ), Tendsto δ atTop (nhds 0) ∧
  ∀ x ≥ x0, ∀ i, HerrCocycleExtensionClass (Fm.Gx x i) Fm.GK C ((Fm.L x i).sc.b ^ δ x)

def TwistConductorsFamily : Prop := ∃ x0 : ℝ, ∀ x ≥ x0, ∀ hx : Fm.x1 < x, ∀ i, TwistConductorsSplit (Fm.D x i) (Fm.ex x hx i).nch

def FontaineFormalPropertiesFamily : Prop := ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i, FontaineFormalProperties (Fm.Gx x i) Fm.GK

def BaseIndependenceFamily : Prop := ∀ x, Fm.x1 < x → AmbientMetricLowerBound Fm x

def SmallOrderPrimeBoundsFamily : Prop := ∃ C : ℝ, ∀ x (i : Fm.Ix x), OrderConsequences (Fm.D x i) C

def ChosenLeadingTermsCountFamily : Prop := ChosenTT Fm

def FewBadOrbitsFamily : Prop := ∃ Cb : ℝ, 0 < Cb ∧ ChosenBad Fm Cb

def ProvisoFamily (C0 : ℝ) : Prop := ChosenProviso Fm C0

def WordCountFamily (C0 CH : ℝ) : Prop := ChosenCode Fm C0 CH

def AdmCF : Prop :=
  FullRankFamily Fm ∧ G1Family Fm ∧ LogTermFamily Fm ∧ G3BoundFamily Fm ∧ IrreducibilityFamily Fm ∧ PeriodFamily' Fm ∧
  SlopesFamily Fm ∧ CountFamily Fm ∧ LevelTFamily Fm ∧ AddedTermFamily Fm ∧ TwistConductorsFamily Fm ∧ FontaineFormalPropertiesFamily Fm ∧ BaseIndependenceFamily Fm ∧
  HostOrbitConditions ∧ SmallOrderPrimeBoundsFamily Fm ∧ TopsChoiceLemma ∧ ChosenLeadingTermsCountFamily Fm ∧ FewBadOrbitsFamily Fm

def SlopeLemmaFamily : Prop := ∃ C x0 : ℝ, ∀ x ≥ x0, ∀ i, Conclusion4 (Fm.Gx x i) Fm.GK C Fm.Cr

def SlopeLossFamily (C' : ℝ) : Prop := ∃ C x0 : ℝ, ∀ x ≥ x0, x ∈ Fm.Win → Conclusion5 Fm x C C'

def Conclusion3Family (C' : ℝ) : Prop := ∃ x0 : ℝ, ∀ x ≥ x0, x ∈ Fm.Win → PointsLemma Fm x C'

end FamV

def KudlaFamilyStatement (Cabs CF Cabs' C' : ℝ) {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (CH : ℝ) : Prop :=
  AdmAF Fm Cabs CF Fm.Csz →
    Conclusion1Family Fm Fm.Csz Cabs' ∧
    (AdmCF Fm → FrameNumberBoundFamily Fm Fm.Csz CH ∧ SlopeLemmaFamily Fm ∧ SlopeLossFamily Fm C' ∧
      ∀ C0 : ℝ, 1 ≤ C0 → SplitProvisoFamily Fm C0 → ProvisoFamily Fm C0 → WordCountFamily Fm C0 CH → Conclusion3Family Fm C')

def ClosedAbsoluteShare (𝒞 : Formalism.MainNotions.FamClass) : Prop :=
  Conclusion2 ∧ ∀ (Cabs : ℝ) (CF : List ℝ → ℝ), ∃ Cabs' C' : ℝ,
    Formalism.MainNotions.Closed 𝒞 (fun Fm CH => KudlaFamilyStatement Cabs (CF Fm.cOut) Cabs' C' Fm CH)

theorem ClosedAbsoluteShare.const {𝒞 : Formalism.MainNotions.FamClass} (h : ClosedAbsoluteShare 𝒞) (Cabs CF : ℝ) :
    ∃ Cabs' C' : ℝ, Formalism.MainNotions.Closed 𝒞 (fun Fm CH => KudlaFamilyStatement Cabs CF Cabs' C' Fm CH) := by
  obtain ⟨Cabs', C', hC⟩ := h.2 Cabs (fun _ => CF)
  exact ⟨Cabs', C', hC⟩

end Formalism.MainNotions.LocalQuadraticParts

end
