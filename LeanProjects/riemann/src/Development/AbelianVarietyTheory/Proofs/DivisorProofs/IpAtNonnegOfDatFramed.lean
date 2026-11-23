import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FactorBounds
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeightedNormSquareRows
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OrthogonalNormSquareSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetRefinement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerChainMatricesWithNormBoundsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInvFrameOfPosDef
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FamFramedOfPos
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DatFramedOfGramPosDef
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColsInIsometry
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHtNumsOfKerSideLastSide
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimeWordLocalConstantsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LastMapNorm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrthNormLogBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodBoundLastLog
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightsInterlaceSameShift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LastSideLogBoundStatement

open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColRows
open scoped ComplexOrder

namespace GlobalTheory.ColRowsTop

open GlobalTheory.IndefiniteRowSideFullHecke.OrthogonalNormSquareSum GlobalTheory.ColNorms GlobalTheory.PeriodClassSum GlobalTheory.LastPeriod in

theorem periodFun_le (hL : LastMapNorm) {X : Fields} (hX : X.Ok) {Pr : Primes X} (hPr : Pr.Ok) {R : Ranks} (W : Wts X Pr.Word R)
    (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (Sg : Set ℕ)
    (P : LevFam X.E X.K R.r Pr.vGs) (u : Pr.Word) (hI : ∀ τ, Br.Interlace (N_m_succ R) (W.lamTrue u R.m τ) (W.sgTrue τ))
    (hS : ∀ τ, Br.SameShift (W.lamTrue u R.m τ) (W.sgTrue τ)) (s : X.K →+* ℂ)
    (ψ : RowPt Pr R sel (mu0 X.F X.E X.K Sg) → Formalism.L2.DIV.VV X.K (W.lamTrue u R.m))
    (F : RowPt Pr R sel (mu0 X.F X.E X.K Sg) → Formalism.L2.DIV.VV X.K W.sgTrue) :
    ‖s (PtilFF W Ch sel (mu0 X.F X.E X.K Sg) P (mtildeOk W Ch sel (mu0 X.F X.E X.K Sg) hX P) u ψ F)‖ ^ 2 ≤
      Real.exp (lastLog W u) *
        GlobalTheory.IndefiniteRowSideFullHecke.WeightedNormSquareDivisors.normSqAt (evGSD W Ch sel (mu0 X.F X.E X.K Sg) P u) (GlobalTheory.IndefiniteRowSideFullHecke.WeightedNormSquareDivisors.evOk W Ch sel Sg hX hPr P u) s ψ *
        GlobalTheory.IndefiniteRowSideFullHecke.WeightedNormSquareDivisors.normSqAt (mtildeGSD W Ch sel (mu0 X.F X.E X.K Sg) P) (mtildeOk W Ch sel (mu0 X.F X.E X.K Sg) hX P) s F := by
  have hT : (0 : ℝ) < (Pr.T u : ℝ) := Nat.cast_pos.2 (hPr.T_prime u).pos
  have ht : ∀ τ, star (s (X.emb τ (star ((Pr.piT u : 𝓞 X.E) : X.E)))) * s (X.emb τ (star ((Pr.piT u : 𝓞 X.E) : X.E))) =
      ((Pr.T u : ℝ) : ℂ) := fun τ => by
    have h1 := hX.conjE (s.comp (X.emb τ)) (star ((Pr.piT u : 𝓞 X.E) : X.E))
    rw [star_star, RingHom.comp_apply, RingHom.comp_apply, starRingEnd_apply] at h1
    have h2 : ((Pr.piT u : 𝓞 X.E) : X.E) * star ((Pr.piT u : 𝓞 X.E) : X.E) = (Pr.T u : X.E) := by
      have := congrArg (fun z : 𝓞 X.E => (z : X.E)) (hPr.piT_norm u)
      simp only [map_mul, map_natCast] at this
      exact this
    rw [← h1, ← map_mul, ← map_mul, h2]
    simp
  have hB := coefOpLe_brAt hL s (N_m_succ R) (W.lamTrue u R.m) W.sgTrue hI hS _ hT _ ht
  set hM := mtildeOk W Ch sel (mu0 X.F X.E X.K Sg) hX P
  set hE := GlobalTheory.IndefiniteRowSideFullHecke.WeightedNormSquareDivisors.evOk W Ch sel Sg hX hPr P u
  let _ := hM.fintypeCl
  have h := sum_pair_le s _ _ _ _ hB ((mtildeGSD W Ch sel (mu0 X.F X.E X.K Sg) P).toCSD hM).wt
    (fun c => ψ ((mtildeGSD W Ch sel (mu0 X.F X.E X.K Sg) P).outSec.rep c))
    (fun c => F ((mtildeGSD W Ch sel (mu0 X.F X.E X.K Sg) P).outSec.rep c))
  have e0 : PtilFF W Ch sel (mu0 X.F X.E X.K Sg) P hM u ψ F =
      ∑ c, ((((mtildeGSD W Ch sel (mu0 X.F X.E X.K Sg) P).toCSD hM).wt c : ℕ) : X.K)⁻¹ *
        pairBK W.sgTrue (brC W u (ψ ((mtildeGSD W Ch sel (mu0 X.F X.E X.K Sg) P).outSec.rep c)))
          (F ((mtildeGSD W Ch sel (mu0 X.F X.E X.K Sg) P).outSec.rep c)) := by
    unfold PtilFF GSD.csOf
    exact (LinearMap.congr_fun (LinearMap.sum_apply _ _ _) _).trans (LinearMap.sum_apply _ _ _)
  have e1 : GlobalTheory.IndefiniteRowSideFullHecke.WeightedNormSquareDivisors.normSqAt (evGSD W Ch sel (mu0 X.F X.E X.K Sg) P u) hE s ψ =
      ∑ c, ((((mtildeGSD W Ch sel (mu0 X.F X.E X.K Sg) P).toCSD hM).wt c : ℕ) : ℝ)⁻¹ *
        sqAt s (W.lamTrue u R.m) (ψ ((mtildeGSD W Ch sel (mu0 X.F X.E X.K Sg) P).outSec.rep c)) := by
    unfold GlobalTheory.IndefiniteRowSideFullHecke.WeightedNormSquareDivisors.normSqAt GSD.ipAt
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    exact (re_inv_mul _ _).trans
      (congrArg₂ (· * ·) rfl ((gram_posSemidef_and_sqAt X.E X.K X.Tau X.emb _ (W.lamTrue u R.m) s).2 _))
  have e2 : GlobalTheory.IndefiniteRowSideFullHecke.WeightedNormSquareDivisors.normSqAt (mtildeGSD W Ch sel (mu0 X.F X.E X.K Sg) P) hM s F =
      ∑ c, ((((mtildeGSD W Ch sel (mu0 X.F X.E X.K Sg) P).toCSD hM).wt c : ℕ) : ℝ)⁻¹ *
        sqAt s W.sgTrue (F ((mtildeGSD W Ch sel (mu0 X.F X.E X.K Sg) P).outSec.rep c)) := by
    unfold GlobalTheory.IndefiniteRowSideFullHecke.WeightedNormSquareDivisors.normSqAt GSD.ipAt
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    have hg := (gram_posSemidef_and_sqAt X.E X.K X.Tau X.emb _ W.sgTrue s).2
    simp only [pairVr_one_eq, pairK_one_basis] at hg
    refine (re_inv_mul _ _).trans (congrArg₂ (· * ·) rfl (Eq.trans ?_ (hg _)))
    unfold GSD.pairAt
    rw [row_gramV]
    rfl
  rw [e0, e1, e2]
  refine h.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ ?_) ?_)
  · rw [lastLog, Real.exp_add, mul_comm (-_ : ℝ), ← Real.rpow_def_of_pos hT, ← Int.cast_neg, Real.rpow_intCast]
    exact mul_le_mul_of_nonneg_left (Real.le_exp_log _) (by positivity)
  · exact Finset.sum_nonneg fun c _ => mul_nonneg (by positivity) (sqAt_nonneg _ _ _)
  · exact Finset.sum_nonneg fun c _ => mul_nonneg (by positivity) (sqAt_nonneg _ _ _)

theorem period_le (hL : GlobalTheory.IndefiniteRowSideFullHecke.OrthogonalNormSquareSum.LastMapNorm) {X : Fields} (hX : X.Ok) {Pr : Primes X} (hPr : Pr.Ok) {R : Ranks}
    (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
    (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {Sg : Set ℕ} (mu : Tup X.F X.E X.K Sg) (hmu : mu = 1)
    (P : LevFam X.E X.K R.r Pr.vGs) (u : Pr.Word) (hI : ∀ τ, Br.Interlace (N_m_succ R) (W.lamTrue u R.m τ) (W.sgTrue τ))
    (hS : ∀ τ, Br.SameShift (W.lamTrue u R.m τ) (W.sgTrue τ))
    (hP : (mtildeGSD W Ch sel mu P).Ok) (hE : (evGSD W Ch sel mu P u).Ok) (v : InfinitePlace X.K)
    (ψ : RowPt Pr R sel mu → Formalism.L2.DIV.VV X.K (W.lamTrue u R.m)) (F : RowPt Pr R sel mu → Formalism.L2.DIV.VV X.K W.sgTrue) :
    v (PtilFF W Ch sel mu P hP u ψ F) ^ 2 ≤
      Real.exp (lastLog W u) * ((evGSD W Ch sel mu P u).ipAt hE v ψ ψ).re * ((mtildeGSD W Ch sel mu P).ipAt hP v F F).re := by
  subst hmu
  have h := periodFun_le hL hX hPr W Ch sel Sg P u hI hS v.embedding ψ F
  rw [InfinitePlace.norm_embedding_eq] at h
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeightedNormSquareDivisors.normSqAt, InfinitePlace.mk_embedding] at h
  exact h

theorem ipAt_nonneg_of_datFramed {K : Type} [Field K] [NumberField K] [StarRing K] {S : GSD K} {h : S.Ok} (hS : DatFramed S h)
    (v : InfinitePlace K) (ψ : S.EqFun) : 0 ≤ (S.ipAt h v ψ ψ).re := by
  obtain ⟨n, e, X, -, hX⟩ := hS
  obtain ⟨y, rfl⟩ := e.surjective ψ
  rw [← hX v y, Complex.ofReal_re]
  positivity

theorem rowsBody_colFace : ColumnNorms → GlobalTheory.IndefiniteRowSideFullHecke.MeanPeriodLogarithms.MeanPeriod → GlobalTheory.ColNorms.FamilyVectors → GlobalTheory.ColNorms.FamilyNorms → ∃ C0 : ℝ, ∀ (D : D7) (N : NumDatum) (X : Fields) [IsTotallyComplex X.K] (s : Seam D X) (Pr : Primes X) (W : Wts X Pr.Word N.R) (Ch : Chars X Pr N.R.m) (G : ChGlob X N.R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (Sg : Set ℕ) (hX : X.Ok) (Bs : DefBase X.K) (Df : DefSide Bs) (Xg : Finset (Formalism.L2.Col.G0 X.E Pr.vGs N.R.r → X.K)) (mu : Bs.Tup → Tup X.F X.E X.K Sg) (cst : ∀ t, LocCst X (rowSG Pr sel (mu t))) (I : ∀ t, ChIdx X Pr N.R (QE sel (mu t : Chr X.F X.E X.K))) (hL : ∀ t, (I t).Ok Ch sel (mu t) (cst t) G (N.R.m - 2)) (hP : ∀ t, (mtildeGSD W Ch sel (mu t) (rPsymF Ch)).Ok) (Mem : Type) (wd : Mem → Pr.Word) (b : ∀ t, Mem → (I t).β (N.R.m - 2 + 1)) (hY : ∀ t x, YbHyp (R := N.R) sel (mu t) (cst t) (I t) (wd x) (N.R.m - 2) (b t x)) (dl : ℂ) (B : Base D D.host.ccK dl) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) (hK : ∀ t x, KerEquivC W Ch sel (mu t) (cst t) (I t) (ambOf s B χ cD) (wd x) (N.R.m - 2) (b t x) (hY t x) (rPsymF Ch)) (hF : ∀ t x j, (chF W sel (mu t) (I t) (wd x) j).Ok) (hE : ∀ x, (evGSD W Ch sel (mu Bs.μ0) (rPsymF Ch) (wd x)).Ok) (ev : ∀ t, (Fin (Df.nV t) → X.K) →ₗ[X.K] V0X W Ch sel (mu t) Xg (rPsymF Ch)) (pl : RPl N.R ≃ X.Tau) (x : Mem) (δ : Code N) (eJ : Bs.J ≃ Fin N.R.m) (R : RecNums Bs.J (RPl N.R)), HostTie N s Pr → WeightTie N W pl (wd x) δ → CharTie N s W Ch G sel → AnalyticTie D dl χ cD → mu Bs.μ0 = 1 → (cst Bs.μ0).sharp = true → FieldOfDefinition W sel (mu Bs.μ0) (cst Bs.μ0) (wd x) (ambOf s B χ cD) → Sizes Pr W N.sc.a → SizeRows N δ (Pr.T (wd x)) → Reads N eJ δ (Pr.T (wd x)) R → C0 ≤ R.Ch → (∀ v : InfinitePlace X.K, ((Df.HV Bs.μ0).map v.embedding).PosDef) → (∀ X0, IsFrames Df X0 → ∀ v F, ((mtildeGSD W Ch sel (mu Bs.μ0) (rPsymF Ch)).ipAt (hP Bs.μ0) v ((ev Bs.μ0 F).1).1 ((ev Bs.μ0 F).1).1).re ≤ Formalism.HermitianLatticesTheory.normAt (Pi.basisFun X.K (Fin (Df.nV Bs.μ0))) X0 v F ^ 2) → RowsBody (colFace hX Df Xg mu cst I hL hP Mem wd b hY (kerRec mu cst I wd b hY (ambOf s B χ cD) hK) hF ev) x (memQ (A := kerRec mu cst I wd b hY (ambOf s B χ cD) hK) (hF := hF) hE (x := x)) (colsIn W Ch hX sel (mu Bs.μ0) (cst Bs.μ0) (I Bs.μ0) (hL Bs.μ0) (wd x)) R ∧ ∀ v, IsUnit ((MramH W Ch hX (wd x)).X v).det := by
  intro h1 h2 h3 h4
  obtain ⟨C, hC, hker⟩ := GlobalTheory.T.prime_word_local_constants h1 h2 h3 h4
  refine ⟨max (2 * (16 + 25)) (max (6 * C + 1 + 2 * C * C) (4 * C * (25 + C))), ?_⟩
  intro D N X _ s Pr W Ch G sel Sg hX Bs Df Xg mu cst I hL hP Mem wd b hY dl B χ cD hK hF hE ev pl x δ eJ R
    hHost hWt hChar hAn hmu hsharp hFD hS hR hRd hC0 hpos hev
  have hPr : Pr.Ok := hHost.2.2.2.2.2.2.2.2.2.1
  have hT : 1 ≤ Pr.T (wd x) := (hPr.T_prime _).one_le
  have hk := hker D N X s Pr W Ch G sel Sg (mu Bs.μ0) (cst Bs.μ0) (I Bs.μ0) dl B χ cD pl (wd x) δ (b Bs.μ0 x) (hY Bs.μ0 x)
    (hK Bs.μ0 x) (hF Bs.μ0 x) (hE x) Bs.J eJ R hHost hWt hChar hAn hmu hsharp (hL Bs.μ0) hFD hS hR hRd
  have hl := GlobalTheory.T.last_side_log_bound GlobalTheory.BranchLogBound.orthNormLogBound N X Pr W pl (wd x) δ Bs.J eJ R hWt hS hR hT hRd
  obtain ⟨hn, hA, hsz⟩ := GlobalTheory.ColRows.exists_htNums_of_kerSide_lastSide Bs.J (RPl N.R) (InfinitePlace X.K) R C 25 _ _ hC (by norm_num)
    ((le_max_left _ _).trans hC0) (((le_max_left _ _).trans (le_max_right _ _)).trans hC0)
    (((le_max_right _ _).trans (le_max_right _ _)).trans hC0) hk hl
  obtain ⟨X0, hX0⟩ := GlobalTheory.ColRows.exists_isFrames X.K Bs Df hpos
  obtain ⟨hdet, hiso⟩ := GlobalTheory.ColFirstIso.colsIn_isometry X hX Pr N.R W Ch sel Sg (mu Bs.μ0) (cst Bs.μ0) (I Bs.μ0) G _ (hL Bs.μ0)
    (wd x) (hF Bs.μ0 x 0) hmu
  obtain ⟨hint, hsh⟩ := GlobalTheory.ColRows.weights_interlace_sameShift N X Pr W pl (wd x) δ hWt hR
  have hdat := GlobalTheory.ColRows.evGSD_datFramed X hX Pr N.R W Ch sel Sg (mu Bs.μ0) (rPsymF Ch) (wd x) (hE x)
  refine ⟨GlobalTheory.T.kerChain_matrices_with_norm_bounds X.K Bs Df (colFace hX Df Xg mu cst I hL hP Mem wd b hY (kerRec mu cst I wd b hY (ambOf s B χ cD) hK) hF ev) x
    (memQ (A := kerRec mu cst I wd b hY (ambOf s B χ cD) hK) (hF := hF) hE (x := x)) _
    (colPerL (hP Bs.μ0) Xg (wd x) (ev Bs.μ0)) (RPl N.R) R hn (fun l => (eJ l).1) X0 hdet hiso
    (fun i => GlobalTheory.FamilyFrames.famFramed_chF X hX Pr N.R W Ch sel Sg (mu Bs.μ0) (I Bs.μ0) (wd x) i (hF Bs.μ0 x i)) hdat
    (fun φ F => colPer_eq hX (hP Bs.μ0) Xg _ (hF Bs.μ0 x) (hE x) (hL Bs.μ0) (ev Bs.μ0) φ F) hX0 hsz ?_, hdet⟩
  intro v ψ F
  have hb := period_le GlobalTheory.BranchNorm.lastMapNorm hX hPr W Ch sel (mu Bs.μ0) hmu (rPsymF Ch) (wd x) hint hsh (hP Bs.μ0) (hE x) v
    ψ.1 (ev Bs.μ0 F).1.1
  rw [hA]
  exact hb.trans (mul_le_mul_of_nonneg_left (hev X0 hX0 v F)
    (mul_nonneg (Real.exp_pos _).le (ipAt_nonneg_of_datFramed hdat v ψ)))

end GlobalTheory.ColRowsTop
