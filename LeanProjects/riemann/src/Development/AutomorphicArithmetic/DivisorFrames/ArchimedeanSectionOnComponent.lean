import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HtValOnSubset
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatDegreeStatementOfDegreeTheorem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameCoord
import Development.AbelianVarietyTheory.Definitions.Divisors.VolMeasureOfAdd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NonemptyUnitAt
import Development.AbelianVarietyTheory.Definitions.Divisors.TorusExt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StepIdeal
import Development.AutomorphicArithmetic.DivisorFrames.TangentVectorsAtFramePointIndependent
import Development.AutomorphicArithmetic.DivisorFrames.ArchimedeanSquareConjInvariant
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ImDiagEqTrace
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.SupAtUnit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomogeneousNormFactorFlatLineOrthonormalFrameStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormDiagonalTorusCharacterFlatLineWeightStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetGramLowerTriangularCoordVecReStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TestValueEqConstMulReadingSecZ
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ChartCoverFOfSecBaseChange
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFramedPointBaseChangeAlgebraMap
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsOrthonormalFrameBorelChangeComplexFramedPo
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsAlgebraicOfNormConst
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LawsFieldsSeparately
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.FlatDegreeCompare

private theorem homFac_eq_archSq_ortho (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ) (hL : Laws U x) (τ : Psi H) (K : Type) [Field K] [NumberField K] [Algebra c.F K] (y : FrPt Xo c K) (t₀ : SAB H (Sp K)) (m1 : SABMap t₀ Xo.univ.t y.x) (v : Fin (Dw.mult τ.1) → (epsR K ⟶ t₀.G)) (v' : Fin (Dw.mult (conjEmb τ.1)) → (epsR K ⟶ t₀.G)) (hv : ∀ i, (v i).left ≫ m1.φ = y.u τ.1 i) (hv' : ∀ i, (v' i).left ≫ m1.φ = y.u (conjEmb τ.1) i) (σ : K →+* ℂ) (N N' : ℝ) (hN : EigenvectorLieDegree.IsArchSq t₀.G t₀.PP.L v σ N) (hN' : EigenvectorLieDegree.IsArchSq t₀.G t₀.PP.L v' σ N') (hσ : GoodEmb c (σ.comp (algebraMap c.F K))) (φ : K →ₐ[c.F] CAt (σ.comp (algebraMap c.F K))) (hφ : ∀ a, toC (φ a) = σ a) (z : FrPt Xo c (CAt (σ.comp (algebraMap c.F K)))) (hz : FrMap φ y z) (k : (U (σ.comp (algebraMap c.F K))).Comp) (w : ((U (σ.comp (algebraMap c.F K))).X k).dom) (t : Ix Dw → (CAt (σ.comp (algebraMap c.F K)))ˣ) (hort : ((U (σ.comp (algebraMap c.F K))).X k).IsOrtho w.1) (hbor : FrBor t ((U (σ.comp (algebraMap c.F K))).un k w) z) :
    GlobalTheory.CompHS.homFac (U (σ.comp (algebraMap c.F K))) x (flatWt Dw τ) k w = ‖GlobalTheory.CompHS.diagChar (exOf Dw (flatWt Dw τ) 0) t‖ * Real.sqrt N / Real.sqrt N' := by
  have hU := hL.unf _ hσ
  obtain ⟨W⟩ := ReciprocityTheory.ChartRestriction.G.PullbackSections.nonempty_unfAt hU k w
  obtain ⟨Wu⟩ := ReciprocityTheory.ChartRestriction.G.PullbackSections.nonempty_unitAt W (ReciprocityTheory.ChartRestriction.G.PullbackSections.PfSupAtUnit.dmin_ortho _ hort)
  have hHm := GlobalTheory.OrthoHerm.hm_eq_smul_one E H Dw l Xo c _ r (U _) x hσ hU k w W Wu (hL.xi _ hσ k) hort
  obtain ⟨hzx, hcomb, -⟩ := hbor
  choose C hCi hCup hCc using hcomb
  have hp : Dw.mult τ.1 = Dw.p := by unfold Datum.mult; rw [if_pos τ.2]
  have hq : Dw.mult (conjEmb τ.1) = Dw.q := by unfold Datum.mult; rw [if_neg (conj_not_mem τ)]

  have hx : 0 < x := by
    have hne : Nonempty (Σ ρ : E →+* ℂ, Fin (Dw.mult ρ)) := by
      rcases Nat.eq_zero_or_pos Dw.p with h0 | h0
      · have hq1 : 0 < Dw.q := by have := hL.pos; omega
        exact ⟨⟨conjEmb τ.1, ⟨0, hq ▸ hq1⟩⟩⟩
      · exact ⟨⟨τ.1, ⟨0, hp ▸ h0⟩⟩⟩
    obtain ⟨j0⟩ := hne
    have h1 := Wu.pos (Pi.single (W.e.symm j0) 1) (by simp)
    rw [hHm] at h1
    have h2 : hermForm (((2 * x : ℝ) : ℂ) • (1 : Matrix (Fin W.g) (Fin W.g) ℂ)) (Pi.single (W.e.symm j0) 1)
        (Pi.single (W.e.symm j0) 1) = ((2 * x : ℝ) : ℂ) := by
      simp [hermForm, Matrix.smul_mulVec, dotProduct, Pi.single_apply]
    rw [h2, Complex.ofReal_re] at h1
    linarith
  have key : ∀ (ρ : E →+* ℂ) (v : Fin (Dw.mult ρ) → (epsR K ⟶ t₀.G)), (∀ i, (v i).left ≫ m1.φ = y.u ρ i) →
      ∀ N : ℝ, EigenvectorLieDegree.IsArchSq t₀.G t₀.PP.L v σ N →
      N = (2 * Real.pi * x) ^ (Dw.mult ρ) *
        (∏ i : Fin (Dw.mult ρ), ‖toC ((t (some ⟨ρ, i⟩) : CAt (σ.comp (algebraMap c.F K))))‖) ^ 2 := by
    intro ρ v hv N hN
    rw [UpperTheory.tangent_vectors_at_frame_point_independent E H Dw l Xo c r U hL.pos K y t₀ m1 ρ v hv σ N hN φ hφ z hz k w W Wu hzx (C ρ) (hCc ρ), hHm,
      GlobalTheory.T.det_gram_lowerTriangular_re_eq_pi_mul_pow W.g (Dw.mult ρ) (fun l => W.e.symm ⟨ρ, l⟩) (fun a b e => by simpa using e) (2 * x)
        (fun i j => toC (C ρ i j)) (fun i j hij => by simp only [hCup ρ i j hij]; rfl), ← Finset.prod_pow]
    simp only [hCi]
    congr 1
    ring
  rw [GlobalTheory.T.homogeneousNormFactor_flatLine_orthonormalFrame E H Dw l Xo c _ r (U _) x τ k w hort, GlobalTheory.T.norm_diagonalTorusCharacter_flatLineWeight E H Dw l c _ τ t, key _ v hv N hN, key _ v' hv' N' hN']
  have e1 : (2 * Real.pi * x) ^ (Dw.mult τ.1) = (2 * Real.pi * x) ^ Dw.p := by rw [hp]
  have e2 : (2 * Real.pi * x) ^ (Dw.mult (conjEmb τ.1)) = (2 * Real.pi * x) ^ Dw.q := by rw [hq]
  rw [e1, e2]
  have hpos : ∀ ρ : E →+* ℂ, 0 < ∏ i : Fin (Dw.mult ρ), ‖toC ((t (some ⟨ρ, i⟩) : CAt (σ.comp (algebraMap c.F K))))‖ :=
    fun ρ => Finset.prod_pos fun i _ => norm_pos_iff.2 (Units.ne_zero (M₀ := ℂ) _)
  have hP := hpos τ.1
  have hP' := hpos (conjEmb τ.1)
  generalize ∏ i : Fin (Dw.mult τ.1), ‖toC ((t (some ⟨τ.1, i⟩) : CAt (σ.comp (algebraMap c.F K))))‖ = P at *
  generalize ∏ i : Fin (Dw.mult (conjEmb τ.1)), ‖toC ((t (some ⟨conjEmb τ.1, i⟩) : CAt (σ.comp (algebraMap c.F K))))‖ = P' at *
  have ha : 0 < 2 * Real.pi * x := by positivity
  have hs : ∀ n : ℕ, Real.sqrt ((2 * Real.pi * x) ^ n) = Real.exp ((n : ℝ) / 2 * Real.log (2 * Real.pi * x)) := by
    intro n
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul ha.le, Real.rpow_def_of_pos ha]
    congr 1
    ring
  rw [Real.sqrt_mul (pow_nonneg ha.le _), Real.sqrt_mul (pow_nonneg ha.le _), Real.sqrt_sq hP.le, Real.sqrt_sq hP'.le,
    hs, hs]
  have hq2 : Real.exp (((Dw.p : ℝ) - Dw.q) / 2 * Real.log (2 * Real.pi * x)) * Real.exp ((Dw.q : ℝ) / 2 * Real.log (2 * Real.pi * x)) =
      Real.exp ((Dw.p : ℝ) / 2 * Real.log (2 * Real.pi * x)) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [← hq2]
  field_simp

private theorem archSq_good_case (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ) (hL : Laws U x) (Z : Comp Xo c) (τ : Psi H) (s : ArchSec U x Z (flatWt Dw τ)) (K : Type) [Field K] [NumberField K] [Algebra c.F K] (y : FrPt Xo c K) (hy : LiesOn Z y) (t₀ : SAB H (Sp K)) (m1 : SABMap t₀ Xo.univ.t y.x) (v : Fin (Dw.mult τ.1) → (epsR K ⟶ t₀.G)) (v' : Fin (Dw.mult (conjEmb τ.1)) → (epsR K ⟶ t₀.G)) (hv : ∀ i, (v i).left ≫ m1.φ = y.u τ.1 i) (hv' : ∀ i, (v' i).left ≫ m1.φ = y.u (conjEmb τ.1) i) (σ : K →+* ℂ) (N N' : ℝ) (hN : EigenvectorLieDegree.IsArchSq t₀.G t₀.PP.L v σ N) (hN' : EigenvectorLieDegree.IsArchSq t₀.G t₀.PP.L v' σ N') (hσ : GoodEmb c (σ.comp (algebraMap c.F K))) :
    s.cInf (σ.comp (algebraMap c.F K)) = ‖σ (evR Xo c s.sig y)‖ * Real.sqrt N / Real.sqrt N' := by
  set σ₀ := σ.comp (algebraMap c.F K) with hσ₀
  let φ : K →ₐ[c.F] CAt σ₀ := { σ with commutes' := fun a => rfl }
  obtain ⟨z, hz⟩ := GlobalTheory.Frames.FramedBaseChange.exists_frMap GlobalTheory.lawsFieldsSeparately.2.1 E H Dw l Xo c K (CAt σ₀) φ y
  obtain ⟨k, w, t, ho, hb⟩ := GlobalTheory.LamT.exists_ortho_frBor E H Dw l Xo c σ₀ r (U σ₀) (hL.unf σ₀ hσ) z
  have hon : (⟨k, w.1⟩ : Σ k, Frame ((U σ₀).X k).Ψ r) ∈ framesOn (U σ₀) Z :=
    ⟨w.2, liesOn_frBor hb (liesOn_frMap hz hy)⟩
  have hgood : goodOf c σ₀ = σ₀ := if_pos hσ
  have hinf := s.norm_inf σ₀
  rw [hgood] at hinf
  have h1 : homN (U σ₀) x (wtOf Dw (flatWt Dw τ) 0) s.sig ⟨k, w.1⟩ = s.cInf σ₀ := by
    have : homN (U σ₀) x (wtOf Dw (flatWt Dw τ) 0) s.sig ⟨k, w.1⟩ ∈
        homN (U σ₀) x (wtOf Dw (flatWt Dw τ) 0) s.sig '' framesOn (U σ₀) Z := ⟨_, hon, rfl⟩
    rw [hinf] at this
    exact this
  rw [GlobalTheory.CompHS.homN_eq_homFac] at h1
  have h2 := GlobalTheory.evR_frBor_of_mem_secZ GlobalTheory.lawsFieldsSeparately.2.1 Xo c _ s.sig_mem (CAt σ₀) t _ _ hb
  have h3 := GlobalTheory.FrameEval.evR_frMap_of_isReduced E H Dw l Xo c s.sig s.sig_mem.1 φ y z hz
  have h4 := homFac_eq_archSq_ortho E H Dw l Xo c r U x hL τ K y t₀ m1 v v' hv hv' σ N N' hN hN' hσ φ (fun _ => rfl) z hz k w t ho hb
  rw [← h1, h4]
  have h5 : ‖σ (evR Xo c s.sig y)‖ = ‖GlobalTheory.CompHS.diagChar (exOf Dw (flatWt Dw τ) 0) t‖ * ‖toC (evR Xo c s.sig ((U σ₀).un k w))‖ := by
    rw [← norm_mul]
    show ‖toC (φ (evR Xo c s.sig y))‖ = _
    rw [← h3, h2]
    rfl
  rw [h5]
  ring

theorem UpperTheory.archimedean_section_on_component :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ), Laws U x → ∀ (Z : Comp Xo c) (τ : Psi H) (s : ArchSec U x Z (flatWt Dw τ)) (K : Type) [Field K] [NumberField K] [Algebra c.F K] (y : FrPt Xo c K), LiesOn Z y → ∀ (t₀ : SAB H (Sp K)) (m1 : SABMap t₀ Xo.univ.t y.x) (v : Fin (Dw.mult τ.1) → (epsR K ⟶ t₀.G)) (v' : Fin (Dw.mult (conjEmb τ.1)) → (epsR K ⟶ t₀.G)), (∀ i, (v i).left ≫ m1.φ = y.u τ.1 i) → (∀ i, (v' i).left ≫ m1.φ = y.u (conjEmb τ.1) i) → (∀ i, IsTangent (v i)) → (∀ i, IsTangent (v' i)) → ∀ (σ : K →+* ℂ) (N N' : ℝ), EigenvectorLieDegree.IsArchSq t₀.G t₀.PP.L v σ N → EigenvectorLieDegree.IsArchSq t₀.G t₀.PP.L v' σ N' → s.cInf (σ.comp (algebraMap c.F K)) ^ 2 = ‖σ (evR Xo c s.sig y)‖ ^ 2 * (N / N') := by
  intro E _ _ _ H Dw l Xo c r U x hL Z τ s K _ _ _ y hy t₀ m1 v v' hv hv' ht ht' σ N N' hN hN'
  have h0 : 0 < N := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, h, _⟩ := hN
    exact h
  have h0' : 0 < N' := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, h, _⟩ := hN'
    exact h
  have main : s.cInf (σ.comp (algebraMap c.F K)) = ‖σ (evR Xo c s.sig y)‖ * Real.sqrt N / Real.sqrt N' := by
    by_cases hσ : GoodEmb c (σ.comp (algebraMap c.F K))
    · exact archSq_good_case E H Dw l Xo c r U x hL Z τ s K y hy t₀ m1 v v' hv hv' σ N N' hN hN' hσ
    · set σ' := (starRingEnd ℂ).comp σ
      have e0 : σ'.comp (algebraMap c.F K) = (starRingEnd ℂ).comp (σ.comp (algebraMap c.F K)) := RingHom.comp_assoc _ _ _
      have hσ' : GoodEmb c (σ'.comp (algebraMap c.F K)) := by
        have := goodEmb_goodOf c (σ.comp (algebraMap c.F K))
        rw [goodOf, if_neg hσ] at this
        rw [e0]; exact this
      have hg := archSq_good_case E H Dw l Xo c r U x hL Z τ s K y hy t₀ m1 v v' hv hv' σ' N N'
        (UpperTheory.archimedean_square_conj_invariant K t₀.G t₀.PP.L _ v t₀.PP.isLB ht σ N hN)
        (UpperTheory.archimedean_square_conj_invariant K t₀.G t₀.PP.L _ v' t₀.PP.isLB ht' σ N' hN') hσ'
      have hc : s.cInf (σ'.comp (algebraMap c.F K)) = s.cInf (σ.comp (algebraMap c.F K)) := by
        have i1 := s.norm_inf (σ.comp (algebraMap c.F K))
        have i2 := s.norm_inf (σ'.comp (algebraMap c.F K))
        rw [e0, GlobalTheory.CompHt.goodOf_conj, i1] at i2
        exact (Set.singleton_eq_singleton_iff.1 i2).symm
      rw [← hc, hg]
      simp only [σ', RingHom.comp_apply, Complex.norm_conj]
  rw [main, div_pow, mul_pow, Real.sq_sqrt h0.le, Real.sq_sqrt h0'.le, mul_div_assoc]
