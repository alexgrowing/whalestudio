import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundOfValue
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatDegreeFromPrismaticStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClosedOfIsAlgPt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeightAdditiveInSymbols
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InteriorPointSemiFibrationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiFibrationLieLatticeFullStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiltrationDegreeRecursionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegreeDeterminantLineTwoHermitianLatticesStatement
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NotMemPlaceholder
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.HadStA
import Development.AutomorphicArithmetic.LocalEmbeddings.HtSingleEqStepGrDeg
import Development.AutomorphicArithmetic.LocalEmbeddings.PointDiff
import Development.AutomorphicArithmetic.DivisorFrames.SemiFibrePointGivesModelObject
import Development.AutomorphicArithmetic.DivisorFrames.LieLatticeSuccessiveVectorsSpan
import Development.AutomorphicArithmetic.DivisorFrames.LieCombinationsIndependentUnderIso
import Development.AutomorphicArithmetic.DivisorFrames.EigenBasisOfIndependentEigenvectors
import Development.AutomorphicArithmetic.DivisorFrames.LieCombinationHasIntegralModel
import Development.AutomorphicArithmetic.DivisorFrames.HermitianLieCombinationIntegralModel

section SlopeTestRemainingChoices

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.FlatDegreeCompare
open ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.LieHt GlobalTheory.LieRead GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.Mean4 GlobalTheory.CovHt GlobalTheory.TrueGeo GlobalTheory.Toroidal

private theorem deg_sub_deg {D : D7} (O : Setup D) (y : Pt O.s) (hy : below y.y ∉ genBd O.s.T.Z) {K : Type} [Field K]
    [NumberField K] (F : SemiFib K) (ι : K →+* Qb) (hT : FibTie O y F ι) (h : HermFam K (Fin F.P₀.g → K))
    (hh : F.IsHerm h) (τ : Psi O.A.H) {δ : ℝ}
    (hδ : ∀ (j : O.κ.c.F →+* K)
      (o : Obj O.S.Dw O.κ.l (baseKA O.κ.l) (spMap j ≫ spMap (IntermediateField.inclusion O.κ.c.le).toRingHom)),
      GlobalTheory.PointDiff.Diff δ o.t (EigenvectorLieDegree.embIn O.κ.c j τ.1) (EigenvectorLieDegree.embIn O.κ.c j (conjEmb τ.1))
        (O.S.Dw.mult τ.1) (O.S.Dw.mult (conjEmb τ.1))) :
    deg h (stepLat O F τ.1 (O.S.Dw.mult τ.1)) - deg h (stepLat O F (conjEmb τ.1) (O.S.Dw.mult (conjEmb τ.1))) = δ := by
  obtain ⟨j, o, e, he, hL, hE⟩ := UpperTheory.semi_fibre_point_gives_model_object D O y hy K F ι hT
  have hg : F.P₀.g = (letters O.S.Dw).length := by
    obtain ⟨-, -, -, -, -, -, -, e, -⟩ := hT
    exact e
  have hfull := (GlobalTheory.T.semi_fibration_lie_lattice_full K F).1
  have c₁ := o.t.semi.comm
  have c₀ := F.semi.comm
  have c₂ : IsCommMonObj F.P₀.A := GlobalTheory.PolPull.isCommMonObj_of_isGrpPullback F.fib
  have hp : O.S.Dw.mult τ.1 = O.S.Dw.p := by unfold Datum.mult; rw [if_pos τ.2]
  have hq : O.S.Dw.mult (conjEmb τ.1) = O.S.Dw.q := by unfold Datum.mult; rw [if_neg (conj_not_mem τ)]
  have hx := GlobalTheory.T.eigenbasis_signature_exists _ O.A.H O.S.Dw O.κ.l O.κ.c K j o τ.1 τ.2
  rw [← hp, ← hq] at hx
  have key : ∀ ρ : D.host.E →+* ℂ, (∃ x : Fin (O.S.Dw.mult ρ) → (epsR K ⟶ o.t.G), EigenvectorLieDegree.IsEigBasis o.t.act
      ((EigenvectorLieDegree.embIn O.κ.c j ρ).comp (algebraMap (𝓞 D.host.E) D.host.E)) x) →
      ∃ r, IsEigData o.t (EigenvectorLieDegree.embIn O.κ.c j ρ) (O.S.Dw.mult ρ) r
          (fun σ => (h.gram σ fun i : Fin (O.S.Dw.mult ρ) => stepVec O F ρ i).det.re) ∧
        (∀ σ, 0 < (h.gram σ fun i : Fin (O.S.Dw.mult ρ) => stepVec O F ρ i).det.re) ∧
        ∀ (𝔓 : HeightOneSpectrum (𝓞 K)) (b : Fin (O.S.Dw.mult ρ) → Fin F.P₀.g → K)
          (M : Matrix (Fin (O.S.Dw.mult ρ)) (Fin (O.S.Dw.mult ρ)) K),
          GlobalTheory.PtDeg.LocBasis 𝔓 (stepLat O F ρ (O.S.Dw.mult ρ)) b → (∀ i, stepVec O F ρ i.1 = ∑ k, M i k • b k) →
            r 𝔓 = (vAdd 𝔓 M.det : ℝ) := by
    rintro ρ ⟨x, hx⟩
    obtain ⟨hi, hl, -, -⟩ := UpperTheory.lie_lattice_successive_vectors_span D O K F hg hfull ρ
    choose w hw using fun i : Fin (O.S.Dw.mult ρ) =>
      ((GlobalTheory.LieComb.lieComb_algebra K F.P₀.A _ F.v F.basis.1).1 (stepVec O F ρ i)).exists
    have hI := UpperTheory.lie_combinations_independent_under_iso K F.P₀.A o.t.G e he _ _ F.v _ w F.basis hi hw
    have hB := UpperTheory.eigen_basis_of_independent_eigenvectors K _ o.t.G o.t.act _ _ x _ hx (hE ρ w hw) hI
    have hF := UpperTheory.lie_combination_has_integral_model _ O.A.H K F o.t e he _ _ w hi hw
    have hA := UpperTheory.hermitian_lie_combination_integral_model _ O.A.H K F o.t e he hL h hh _ _ w hi hw
    choose a ha using fun 𝔓 => exists_gen hI (hF 𝔓).1
    refine ⟨ordOf a, ⟨_, hB, fun 𝔓 => locOrd_of_gen hI (ha 𝔓), hA⟩, fun σ => ?_, fun 𝔓 b M hb hM => ?_⟩
    · obtain ⟨_, _, _, _, _, _, _, _, _, -, -, -, h, -⟩ := hA σ
      exact h
    · exact (eq_of_locOrd hI (ha 𝔓) ((hF 𝔓).2 b M (hl ▸ hb) hM)).symm
  obtain ⟨r, d, p, m⟩ := key _ hx.1
  obtain ⟨r', d', p', m'⟩ := key _ hx.2
  obtain ⟨hi, -, fg, sp⟩ := UpperTheory.lie_lattice_successive_vectors_span D O K F hg hfull τ.1
  obtain ⟨hi', -, fg', sp'⟩ := UpperTheory.lie_lattice_successive_vectors_span D O K F hg hfull (conjEmb τ.1)
  have h1 := (GlobalTheory.T.degree_determinant_line_two_hermitianLattices K h _ _ fg fg' _ _ hi sp hi' sp' 1 one_ne_zero (r - r') (fun 𝔓 b M b' M' a₁ a₂ a₃ a₄ => by
    rw [Pi.sub_apply, m 𝔓 b M a₁ a₂, m' 𝔓 b' M' a₃ a₄]
    simp [vAdd])).2
  rw [← h1, ← GlobalTheory.FlatRow.adDeg_sq, ← (hδ j o _ _ _ _ d d').2]
  congr 1
  funext σ
  rw [map_one, norm_one, one_mul, div_pow, Real.sq_sqrt (p σ).le, Real.sq_sqrt (p' σ).le, Pi.div_apply]

private theorem ht_det {D : D7} (O : Setup D) (hO : O.Core) {A : SlopeTestRemainingChoices O.Y} {T : Real0 O.Y} {H : Ht O.Y} (hR : O.Reads A T H)
    (y : Pt O.s) (hy : below y.y ∉ genBd O.s.T.Z) {K : Type} [Field K]
    [NumberField K] (F : SemiFib K) (ι : K →+* Qb) (hT : FibTie O y F ι) (h : HermFam K (Fin F.P₀.g → K))
    (hh : F.IsHerm h) (τ : Psi O.A.H) :
    (adlOf (O.Φ.C _) (O.met.hm _) (detSym O.S.Dw (fun _ => false) none τ.1)).ht (basePt O.Φ y) =
      deg h (stepLat O F τ.1 (O.S.Dw.mult τ.1)) - deg h (stepLat O F (conjEmb τ.1) (O.S.Dw.mult (conjEmb τ.1))) := by
  have hg : F.P₀.g = (letters O.S.Dw).length := by
    obtain ⟨-, -, -, -, -, -, -, e, -⟩ := hT
    exact e
  have hfull := (GlobalTheory.T.semi_fibration_lie_lattice_full K F).1
  have hp : O.S.Dw.mult τ.1 = O.S.Dw.p := by unfold Datum.mult; rw [if_pos τ.2]
  have hq : O.S.Dw.mult (conjEmb τ.1) = O.S.Dw.q := by unfold Datum.mult; rw [if_neg (conj_not_mem τ)]
  have hdeg : ∀ ρ, ∀ k ≤ O.S.Dw.mult ρ, deg h (stepLat O F ρ k) = ∑ i ∈ Finset.range k, stepGrDeg O F h ρ i := by
    intro ρ k hk
    induction k with
    | zero => simp [stepLat_zero, HadamardFrameExtension.deg_bot]
    | succ k ih => rw [GlobalTheory.T.filtration_degree_recursion D O K F h hg hfull ρ k (by omega), ih (by omega), Finset.sum_range_succ]
  have hind : ArIn.ind ∅ = fun _ => false := by funext p; simp [ArIn.ind]
  have h1 : ∀ ρ i, i < O.S.Dw.mult ρ → (adlOf (O.Φ.C _) (O.met.hm _)
      (Finsupp.single ((fun _ => false), none, .inl (ρ, i)) 1)).ht (basePt O.Φ y) = stepGrDeg O F h ρ i := by
    intro ρ i hi
    obtain ⟨x, P, hc⟩ := hO
    rw [hc.hm_eq, ← hind]
    exact GlobalTheory.LieRead.ht_single_eq_stepGrDeg O x y hy F ι h hT hh ρ i hi
  have e : detSym O.S.Dw (fun _ => false) none τ.1 = ∑ i ∈ Finset.range (O.S.Dw.p + O.S.Dw.q), Finsupp.single
      (if i < O.S.Dw.p then (((fun _ => false), none, .inl (τ.1, i)) : Sym D.host.E)
        else ((fun _ => false), none, .inl (conjEmb τ.1, O.S.Dw.p + O.S.Dw.q - 1 - i)))
      (if i < O.S.Dw.p then (1 : ℤ) else -1) :=
    Finset.sum_congr rfl fun i _ => by unfold rootSym; split_ifs <;> rfl
  rw [e, GlobalTheory.HtAdd.ht_adlOf_sum D O hO A T H hR _ _ _ _ _ (fun i _ => by split_ifs <;> exact ⟨rfl, rfl⟩),
    hdeg _ _ le_rfl, hdeg _ _ le_rfl, hp, hq, Finset.sum_range_add, sub_eq_add_neg, ← Finset.sum_neg_distrib,
    ← Finset.sum_range_reflect (fun i => -stepGrDeg O F h (conjEmb τ.1) i)]
  refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun i hi => ?_) (Finset.sum_congr rfl fun i hi => ?_)
  · rw [Finset.mem_range] at hi
    rw [if_pos hi, if_pos hi, h1 _ _ (hp ▸ hi), Int.cast_one, one_mul]
  · rw [Finset.mem_range] at hi
    have e : O.S.Dw.p + O.S.Dw.q - 1 - (O.S.Dw.p + i) = O.S.Dw.q - 1 - i := by omega
    rw [if_neg (by omega), if_neg (by omega), e, h1 _ _ (by omega)]
    simp

private theorem exists_char (E : Type) [Field E] [NumberField E] {a b : ℕ} (h : a = b) [NeZero b]
    (χ : DirichletCharacter ℂ b) (hχ : GlobalTheory.IsKroneckerChar χ) :
    ∃ (_ : NeZero a) (χ' : DirichletCharacter ℂ a), GlobalTheory.IsKroneckerChar χ' ∧ GlobalTheory.CM.logOm E χ' = GlobalTheory.CM.logOm E χ := by
  subst h
  exact ⟨inferInstance, χ, hχ, rfl⟩

end SlopeTestRemainingChoices

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
theorem _root_.GlobalTheory.T.abs_degree_frame_le_log_discriminant : Hypotheses2 → HypothesesH → GlobalTheory.Published.ScholzeWeinsteinB → ∃ C₁ : ℝ, OnObj fun D O _ _ _ _ =>
    ∀ (c : O.Y.Comp) (τ : D.what₂.Tau), |GlobalTheory.ShFam.Pad.degFrame O.s O.Φ O.met.hm c τ| ≤
      C₁ * O.Y.N * (Real.log D.host.rdE + |dlogL D 1|) := by
  intro hP hH hSW
  refine ⟨7, GlobalTheory.FrameDegSize.bound_of_value fun D O hO hf A T H hR c τ => ?_⟩
  haveI : Fact D.host.d.Prime := ⟨D.host.hyp.2.1⟩
  haveI : NeZero D.host.d := ⟨D.host.hyp.2.1.ne_zero⟩
  have hd3 : D.host.d % 4 = 3 := by have := D.host.hyp.2.2.2.1; omega
  obtain ⟨_, χ, hχ, e⟩ := exists_char D.host.E O.A.d_eq (chiK D) (GlobalTheory.isKroneckerChar_quadraticChar hd3)
  obtain ⟨hb, hbd⟩ := GlobalTheory.ShFam.KitCheck.innerPt_spec O.Φ c
  obtain ⟨y, rfl, hy⟩ := GlobalTheory.Mean4O.OnModel.exists_baseOn (O := O) c hb
  have hint : GlobalTheory.TrueGeo.below y.y ∉ GlobalTheory.Toroidal.genBd O.s.T.Z := by
    rw [← π_basePt (Φ := O.Φ) y, basePt, hy]
    exact hbd
  obtain ⟨K, _, _, F, ι, -, hT⟩ := GlobalTheory.T.interior_point_semi_fibration hP hH D O hO hf A T H hR y ((hR.ht.int y).2 hint)
  obtain ⟨h, hh⟩ := (GlobalTheory.T.semi_fibration_lie_lattice_full K F).2.1
  have h1 := ht_det O hO hR y hint F ι hT h hh ⟨_, O.A.cm τ⟩
  rw [basePt, hy] at h1
  refine h1.trans (deg_sub_deg O y hint F ι hT h hh ⟨_, O.A.cm τ⟩ fun j o => ?_)
  rw [← e]
  exact GlobalTheory.PointDiff.diff_all (GlobalTheory.T.flat_degree_from_prismatic hSW hP hP.q2 hP.q3 hP.q4) (GlobalTheory.FlatRow.isHostField D _ O.A.d_eq) χ hχ
    (GlobalTheory.RankOneDatum.exists_datum_of_rt D O.A.H O.A.rt_eq O.A.cmHost_rootComplex_eq_pm_sqrt)
    ((one_le_two.trans O.S.two_le).trans O.S.rank_eq.ge) O.κ.c j o _
