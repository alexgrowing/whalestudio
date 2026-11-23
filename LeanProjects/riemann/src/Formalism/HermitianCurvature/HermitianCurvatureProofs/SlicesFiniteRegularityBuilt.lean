import Mathlib
import Formalism.HermitianCurvature.StatementJCT
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentCoordinatesMeasurePreserving
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ComponentFamilySettingOfSetting
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TheoremPIntegralOfPlaces
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CorollaryU1Plain
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SeminormCompletion
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaSesquilinearity
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ComposeDifferentialOperators
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentComposition.Development
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentComposition.DegPderivMul
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentComposition.Expand
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CvRhoOfParts
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SymmetricScalarBlockMatrixMul
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelFormSesquilinearFiniteClass
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DerivativeBoundInBanachSpace
import Formalism.HermitianCurvature.HermitianCurvatureProofs.AdditiveCharacterPsi
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CompactlySupportedBanachModel
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PhiBoundPartsOfRadicalParametrisation
import Formalism.HermitianCurvature.HermitianCurvatureProofs.WirtingerIntegrationByParts

namespace Formalism.FourierDecayAlt.P.JCTx6

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants MeasureTheory

noncomputable section

def SliceLevel (Cc : ℝ) : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (T : D.LevTower k r Wp Wq) (f : B.Mat k r → (Wq →L[ℂ] Wp)) (χ : ℝ → ℝ) (A₀ : ℝ) (N : ℕ) (P0 : M.Par),
    P0.k = k → P0.r = r → 2 ≤ k → C6.IsCut0 χ → B.CkOn ⊤ (B.GV k r) f → (∀ m : ℕ, B.InCC A₀ m f) →
    Cc * ((r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (r : ℝ) + k + 1) ^ 2 + (2 * (r : ℝ) + k + 1) ^ 3) ≤ A₀ →
    ∀ ε : ℝ, 0 < ε → ∀ (i : ℕ) (hi : i ≤ r) (w : List C.Letter), w.length ≤ N →
      ∀ (p : C.LPt) (hp : D.IsLocPt p i) (a : Wd.Ix (Fin w.length)), ∃ ε' : ℝ, 0 < ε' ∧
        JC.CCCoefM (T.bs i) (P5.Auser P0 N + 1) (P5.mmUser P0 N) ε'
          (D.castF (by simp [hp.2]) (D.sliceAt k r T.base.z T.base.z'
            (D.uwG k r T.base.z T.base.z' (D.cutF T.base χ f ε) i hi w a) p))

theorem slicesCCBuilt_of (h : ∃ Cc, SliceLevel Cc) : JCT.SlicesCCBuilt := by
  obtain ⟨Cc, hC⟩ := h
  refine ⟨Cc, ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB _hbud v ε hε i hi w hw p hp a
  obtain ⟨_, _, _, hIB, _, _, _, _, _, hsm, hk2, hthr, _⟩ := hB
  have hlen : w.length ≤ S.Ntop := by
    obtain ⟨w', hw'⟩ := hw
    have h1 : (w'.1 v).length ≤ w'.1.cnt :=
      Finset.le_sup (f := fun v => (w'.1 v).length) (Finset.mem_univ v)
    rw [hw'] at h1
    exact h1.trans w'.2.2
  exact hC S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)) (T v) (f v) χ A₀ S.Ntop (D.parOf S v) rfl rfl hk2 hIB.1
    (hsm v) ((hIB.2 v).2.2.2.2.1) hthr ε hε i hi w hlen p hp a

end

end Formalism.FourierDecayAlt.P.JCTx6

namespace Formalism.FourierDecayAlt.P.JCTx6

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants MeasureTheory

noncomputable section

def LettersDD : Prop :=
  ∀ (k j ρ : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
    (z z' : Fin (2 * (j + ρ) + k + 1) → ℂ) (hj : j ≤ j + ρ) (w : List C.Letter) (a : Wd.Ix (Fin w.length)),
    1 ≤ j →
    ∃ Θ : B.DiffOp k (j + ρ) Wp Wq, U.InDD k j ρ (w.length * j) (w.length * j + w.length * j ^ 2) Θ ∧
      ∀ F : B.Mat k (j + ρ) → (Wq →L[ℂ] Wp), B.CkOn ⊤ (B.GV k (j + ρ)) F →
        ∀ g ∈ B.GV k (j + ρ), U.DjU k j ρ g ≠ 0 → D.uwG k (j + ρ) z z' F j hj w a g = B.opApply Θ F g

def gInt (k ph n ρ : ℕ) (σ : Equiv.Perm (Fin ph)) (d : Fin ph → ℂ) (t : ℂ)
    (z z' : Fin (2 * (ph + (n + 1) + ρ) + k + 1) → ℂ) {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (F : B.Mat k (ph + (n + 1) + ρ) → E) (γ : B.Mat k ρ)
    (y : (U.RC k (ph + (n + 1)) ρ × U.RC k (ph + (n + 1)) ρ) × (U.XiH ph (n + 1) σ × (G.UT (n + 1) → ℂ))) : E :=
  G.psi U.betaU (G.superSum (G.upper y.2.2)) •
    (U.psiStar (p := ph) (s := n + 1) k ρ σ z z' (y.1, y.2.1) •
      F (U.gaXi (p := ph) (s := n + 1) k ρ σ d (y.1, y.2.1)
        (Matrix.of.symm (t • G.wMat (n + 1) * G.upper y.2.2)) γ))

def muG (k ph n ρ : ℕ) (σ : Equiv.Perm (Fin ph)) :
    Measure ((U.RC k (ph + (n + 1)) ρ × U.RC k (ph + (n + 1)) ρ) × (U.XiH ph (n + 1) σ × (G.UT (n + 1) → ℂ))) :=
  ((U.muRC k (ph + (n + 1)) ρ).prod (U.muRC k (ph + (n + 1)) ρ)).prod (volume.prod volume)

def IntG : Prop :=
  ∀ (k ph n ρ : ℕ) (σ : Equiv.Perm (Fin ph)) (d : Fin ph → ℂ) (t : ℂ), (∀ i, d i ≠ 0) → t ≠ 0 →
    ∀ K : Set ℝ, IsCompact K → K ⊆ Set.Ioi 0 → ∀ (Q : ℕ) (A₁ : ℝ),
    2 * ((ph + (n + 1) + ρ : ℕ) : ℝ) * ((2 * (ph + (n + 1) + ρ) + k + 1 : ℕ) : ℝ) <
      A₁ / (8 * (2 * ((ph + (n + 1) + ρ : ℕ) : ℝ) + 1)) →
    ∀ (z z' : Fin (2 * (ph + (n + 1) + ρ) + k + 1) → ℂ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E]
      (F₁ : B.Mat k (ph + (n + 1) + ρ) → E) (B₁ : ℝ), U.Star k (ph + (n + 1)) ρ F₁ A₁ Q B₁ K →
      ∀ γ ∈ B.GV k ρ, Integrable (gInt k ph n ρ σ d t z z' F₁ γ) (muG k ph n ρ σ)

def OrbitSliceIntegrable : Prop :=
  ∀ (k ph n ρ : ℕ) (σ : Equiv.Perm (Fin ph)) (d : Fin ph → ℂ) (t : ℂ)
    (z z' : Fin (2 * (ph + (n + 1) + ρ) + k + 1) → ℂ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E]
    (F : B.Mat k (ph + (n + 1) + ρ) → E) (γ : B.Mat k ρ),
    Integrable (gInt k ph n ρ σ d t z z' F γ) (muG k ph n ρ σ) →
    Integrable (fun ξ : U.Xi k (ph + (n + 1)) 0 ρ (Dx2.SL.sigP σ) =>
        U.psiStar (p := ph + (n + 1)) (s := 0) k ρ (Dx2.SL.sigP σ) z z' ξ •
          F (U.gaXi (p := ph + (n + 1)) (s := 0) k ρ (Dx2.SL.sigP σ) (Dx2.SL.dP d t) ξ (fun a => a.elim0) γ))
      (U.muXi k (ph + (n + 1)) 0 ρ (Dx2.SL.sigP σ))

def PosCore : Prop :=
  IntG → OrbitSliceIntegrable → ∃ Cc : ℝ, 0 ≤ Cc ∧
  ∀ (k ph n ρ : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (z z' : Fin (2 * (ph + (n + 1) + ρ) + k + 1) → ℂ), inWb k (ph + (n + 1) + ρ) z → inWb k (ph + (n + 1) + ρ) z' →
    ∀ (Θ : B.DiffOp k (ph + (n + 1) + ρ) Wp Wq) (o κ : ℕ), U.InDD k (ph + (n + 1)) ρ o κ Θ →
    ∀ (f : B.Mat k (ph + (n + 1) + ρ) → (Wq →L[ℂ] Wp)) (χ : ℝ → ℝ) (A₀ ε : ℝ),
      B.CkOn ⊤ (B.GV k (ph + (n + 1) + ρ)) f → (∀ m : ℕ, B.InCC A₀ m f) → C6.IsCut0 χ → 0 < ε →
    ∀ F : B.Mat k (ph + (n + 1) + ρ) → (Wq →L[ℂ] Wp),
      (∀ g ∈ B.GV k (ph + (n + 1) + ρ), U.DjU k (ph + (n + 1)) ρ g ≠ 0 →
        F g = B.opApply Θ (fun x => ((χ (Gf k (ph + (n + 1) + ρ) z z' x / ε) : ℝ) : ℂ) • f x) g) →
    ∀ (σ : Equiv.Perm (Fin ph)) (d : Fin ph → ℂ) (t : ℂ), (∀ i, d i ≠ 0) → t ≠ 0 →
    ∀ (As mm : ℕ) (A : ℝ), o ≤ As → κ + (ph + (n + 1)) * o ≤ As → mm ≤ As →
      (2 * (ph + (n + 1) + ρ) + k + 1) ^ 3 ≤ As →
      A ≤ 128 * (((ph + (n + 1) + ρ : ℕ) : ℝ) + 1) ^ 3 * (As : ℝ) →
      Cc * (((ph + (n + 1) + ρ : ℕ) : ℝ) + 1) ^ 4 * (As : ℝ) ≤ A₀ →
      ∃ ε' : ℝ, 0 < ε' ∧
        B.CkOn (mm : ℕ∞) (B.GV k ρ) (fun γ => U.PhiFun (p := ph + (n + 1)) (s := 0) k ρ (Dx2.SL.sigP σ)
          (Dx2.SL.dP d t) z z' F (fun a => a.elim0) γ) ∧
        B.InCC A mm (fun γ => U.PhiFun (p := ph + (n + 1)) (s := 0) k ρ (Dx2.SL.sigP σ)
          (Dx2.SL.dP d t) z z' F (fun a => a.elim0) γ) ∧
        ∀ γ ∈ B.GV k ρ, U.PhiFun (p := ph + (n + 1)) (s := 0) k ρ (Dx2.SL.sigP σ)
          (Dx2.SL.dP d t) z z' F (fun a => a.elim0) γ ≠ 0 →
          ε' ≤ Gf k ρ (U.lowV k (ph + (n + 1)) ρ z) (U.lowV k (ph + (n + 1)) ρ z') γ

end

end Formalism.FourierDecayAlt.P.JCTx6

namespace Formalism.FourierDecayAlt.P.JCTx6.Lev0

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants MeasureTheory

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem cutoff_iteratedDeriv_bounded {χ : ℝ → ℝ} (hχ : C6.IsCut0 χ) (q : ℕ) : ∃ c : ℝ, ∀ x, ‖iteratedDeriv q χ x‖ ≤ c := by
  obtain ⟨hs, ⟨δ, hδ, h0⟩, h1⟩ := hχ
  have hc : Continuous (iteratedDeriv q χ) :=
    hs.continuous_iteratedDeriv q (by exact_mod_cast (le_top : ((q : ℕ∞)) ≤ ⊤))
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := δ) (b := 1)).exists_bound_of_continuousOn hc.continuousOn
  have hconst : ∀ (c x : ℝ), |c| ≤ 1 → ‖iteratedDeriv q (fun _ : ℝ => c) x‖ ≤ 1 := by
    intro c x hc1
    rcases Nat.eq_zero_or_pos q with hq | hq
    · subst hq
      simpa using hc1
    · rw [← norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedFDeriv_const_of_ne hq.ne']
      simp
  refine ⟨max M 1, fun x => ?_⟩
  by_cases hx : x ∈ Set.Icc δ 1
  · exact le_trans (hM x hx) (le_max_left _ _)
  · rcases not_and_or.mp hx with hx | hx
    · push_neg at hx
      have hev : χ =ᶠ[nhds x] fun _ => (0 : ℝ) := by
        filter_upwards [Iio_mem_nhds hx] with y hy using h0 y hy
      rw [hev.iteratedDeriv_eq]
      exact le_trans (hconst 0 x (by simp)) (le_max_right _ _)
    · push_neg at hx
      have hev : χ =ᶠ[nhds x] fun _ => (1 : ℝ) := by
        filter_upwards [Ioi_mem_nhds hx] with y hy using h1 y (le_of_lt hy)
      rw [hev.iteratedDeriv_eq]
      exact le_trans (hconst 1 x (by simp)) (le_max_right _ _)

theorem isCutG_div {χ : ℝ → ℝ} (hχ : C6.IsCut0 χ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ U.IsCutG (δ * ε) (fun x => χ (x / ε)) ∧ ∀ x, χ x ≠ 0 → δ ≤ x := by
  have hχ' := hχ
  obtain ⟨hs, ⟨δ, hδ, h0⟩, h1⟩ := hχ'
  have hfun : (fun x => χ (x / ε)) = fun x => χ (ε⁻¹ * x) := by
    funext x
    rw [div_eq_inv_mul]
  refine ⟨δ, hδ, ⟨?_, ?_, ?_⟩, ?_⟩
  · exact hs.comp (contDiff_id.div_const ε)
  · intro q
    obtain ⟨c, hc⟩ := cutoff_iteratedDeriv_bounded hχ q
    refine ⟨ε⁻¹ ^ q * c, fun x => ?_⟩
    have hq : ContDiff ℝ q χ := hs.of_le (by exact_mod_cast (le_top : ((q : ℕ∞)) ≤ ⊤))
    rw [hfun, iteratedDeriv_comp_const_smul hq ε⁻¹]
    have hcx := hc (ε⁻¹ * x)
    simp only [smul_eq_mul, norm_mul, norm_pow, norm_inv, Real.norm_of_nonneg hε.le]
    exact mul_le_mul_of_nonneg_left hcx (by positivity)
  · intro x hx
    apply h0
    rw [div_lt_iff₀ hε]
    exact hx
  · intro x hx
    by_contra h
    push_neg at h
    exact hx (h0 x h)

def idOp (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] : B.DiffOp k r Wp Wq :=
  [⟨fun _ => ContinuousLinearMap.id ℂ _, fun _ => ContinuousLinearMap.id ℂ _, [], by simp, fun _ _ _ => rfl⟩]

theorem opApply_idOp {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (F : B.Mat k r → (Wq →L[ℂ] Wp)) :
    B.opApply (idOp k r Wp Wq) F = F := by
  funext g
  simp [B.opApply, idOp, B.Rw]

theorem inDD_idOp (k ρ : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] :
    U.InDD k 0 ρ 0 0 (idOp k (0 + ρ) Wp Wq) := by
  intro T hT
  simp only [idOp, List.mem_singleton] at hT
  subst hT
  refine ⟨by simp, fun _ => 1, 0, 0, ⟨MvPolynomial.C 1, by simp, fun g => by simp⟩, fun g => by simp⟩

def bumpB : ContDiffBump (1 : ℂ) := ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩

def bumpOne : ℂ → ℂ := fun w => ((bumpB w : ℝ) : ℂ)

theorem bumpOne_eq : bumpOne = Complex.ofReal ∘ bumpB := rfl

theorem isCutC_bumpOne : U.IsCutC bumpOne := by
  rw [bumpOne_eq]
  refine ⟨?_, ?_, ?_⟩
  · exact Complex.ofRealCLM.contDiff.comp bumpB.contDiff
  · exact bumpB.hasCompactSupport.comp_left Complex.ofReal_zero
  · intro h
    have h2 := tsupport_comp_subset Complex.ofReal_zero (bumpB : ℂ → ℝ) h
    rw [bumpB.tsupport_eq] at h2
    simp [Metric.mem_closedBall, Complex.dist_eq, bumpB] at h2 <;> norm_num at h2

theorem bumpOne_one : bumpOne 1 = 1 := by
  have h : bumpB (1 : ℂ) = 1 := by
    apply ContDiffBump.one_of_mem_closedBall
    simp only [Metric.mem_closedBall, dist_self]
    exact bumpB.rIn_pos.le
  simp [bumpOne, h]

theorem level_zero_estimate {k ρ : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
    (z z' : Fin (2 * (0 + ρ) + k + 1) → ℂ) (f : B.Mat k (0 + ρ) → (Wq →L[ℂ] Wp)) (χ : ℝ → ℝ)
    (hχ : C6.IsCut0 χ) (A₀ : ℝ) (hfA : ∀ m : ℕ, B.InCC A₀ m f) (ε : ℝ) (hε : 0 < ε) (A : ℝ) (mm : ℕ)
    (hA : A + 2 * (((0 + ρ : ℕ) : ℝ) + 1) * (mm : ℝ) ≤ A₀) :
    ∃ ε' : ℝ, 0 < ε' ∧
      B.CkOn (mm : ℕ∞) (B.GV k (0 + ρ)) (fun g => ((χ (Gf k (0 + ρ) z z' g / ε) : ℝ) : ℂ) • f g) ∧
      B.InCC A mm (fun g => ((χ (Gf k (0 + ρ) z z' g / ε) : ℝ) : ℂ) • f g) ∧
      ∀ g ∈ B.GV k (0 + ρ), ((χ (Gf k (0 + ρ) z z' g / ε) : ℝ) : ℂ) • f g ≠ 0 → ε' ≤ Gf k (0 + ρ) z z' g := by
  obtain ⟨δ, hδ, hG, hsupp⟩ := isCutG_div hχ hε
  obtain ⟨C, hC⟩ := Formalism.FourierDecayAlt.P.corollary_u1_truncated_alt k 0 ρ Wp Wq z z' 0 0 (idOp k (0 + ρ) Wp Wq) bumpOne
    (fun x => χ (x / ε)) (δ * ε) (inDD_idOp k ρ Wp Wq) isCutC_bumpOne hG mm mm A₀ (by simp)
  obtain ⟨c, hc⟩ := hfA mm
  have hS := hC f c hc
  have hF : B.opApply (idOp k (0 + ρ) Wp Wq) (U.cutDG k 0 ρ z z' bumpOne (fun x => χ (x / ε)) f) =
      fun g => ((χ (Gf k (0 + ρ) z z' g / ε) : ℝ) : ℂ) • f g := by
    rw [opApply_idOp]
    funext g
    simp [U.cutDG, U.DjU, bumpOne_one]
  rw [hF] at hS
  obtain ⟨hck, -, hbd⟩ := hS
  refine ⟨δ * ε, by positivity, hck, ⟨C * c, ?_⟩, ?_⟩
  · refine Formalism.FourierDecayAlt.P.compactly_supported_monotone k (0 + ρ) _
      (A₀ - ((0 : ℕ) : ℝ) - ((0 : ℕ) : ℝ) * ((0 : ℕ) : ℝ) - 2 * (((0 + ρ : ℕ) : ℝ) + 1) * ((mm + 0 : ℕ) : ℝ))
      A (C * c) mm _ ?_ ⟨hck, ?_⟩
    · push_cast at hA ⊢; linarith
    · intro u v hu hv hl g hg
      refine hbd u v ?_ ?_ hl g hg
      · intro X hX; exact ⟨⟨(hu X hX).1, fun i b hb => absurd hb (Nat.not_lt_zero _)⟩, (hu X hX).2⟩
      · intro X hX; exact ⟨⟨(hv X hX).1, fun i b hb => absurd hb (Nat.not_lt_zero _)⟩, (hv X hX).2⟩
  · intro g hg hne
    have h1 : χ (Gf k (0 + ρ) z z' g / ε) ≠ 0 := by
      intro h0; apply hne; simp [h0]
    have h2 := hsupp _ h1
    rw [le_div_iff₀ hε] at h2
    linarith

end

end Formalism.FourierDecayAlt.P.JCTx6.Lev0

namespace Formalism.FourierDecayAlt.P.JCTx6.Link

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants MeasureTheory

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem budget0_abs (R n N r Cc A₀ : ℝ) (hR1 : 1 ≤ R) (hnR : R ≤ n) (hr : r ≤ n) (hr0 : 0 ≤ r) (hN : 0 ≤ N)
    (hCc : 150 ≤ Cc) (h : Cc * R ^ 4 * (N * n ^ 2 + n ^ 3) ≤ A₀) :
    (127 * R ^ 3 * (N * n ^ 2 + n ^ 3) + 1) + 2 * R * (5 + 3 * R * (N + 2) * n + N * r) ≤ A₀ := by
  have hn1 : 1 ≤ n := le_trans hR1 hnR
  have hR0 : 0 ≤ R := by linarith
  have hn0 : 0 ≤ n := by linarith
  have hR2 : 1 ≤ R ^ 2 := by nlinarith
  have hRR : R ≤ R ^ 2 := by nlinarith
  have hR24 : R ^ 2 ≤ R ^ 4 := by nlinarith
  have hR34 : R ^ 3 ≤ R ^ 4 := by nlinarith [pow_nonneg hR0 3]
  have hn13 : n ≤ n ^ 3 := by nlinarith
  have hn12 : n ≤ n ^ 2 := by nlinarith
  have hS0 : 0 ≤ N * n ^ 2 + n ^ 3 := by positivity
  have hR4 : 0 ≤ R ^ 4 := by positivity
  have e1 : 1 + 10 * R + 12 * (R ^ 2 * n) ≤ 23 * (R ^ 2 * n) := by nlinarith
  have e2 : R ^ 2 * n ≤ R ^ 4 * n ^ 3 := mul_le_mul hR24 hn13 hn0 hR4
  have e3 : R * (N * r) ≤ R ^ 2 * (N * n) :=
    mul_le_mul hRR (mul_le_mul_of_nonneg_left hr hN) (by positivity) (by positivity)
  have e4 : R ^ 2 * (N * n) ≤ R ^ 4 * (N * n ^ 2) :=
    mul_le_mul hR24 (mul_le_mul_of_nonneg_left hn12 hN) (by positivity) hR4
  have e5 : R ^ 3 * (N * n ^ 2 + n ^ 3) ≤ R ^ 4 * (N * n ^ 2 + n ^ 3) := mul_le_mul_of_nonneg_right hR34 hS0
  have e6 : 150 * (R ^ 4 * (N * n ^ 2 + n ^ 3)) ≤ Cc * (R ^ 4 * (N * n ^ 2 + n ^ 3)) :=
    mul_le_mul_of_nonneg_right hCc (mul_nonneg hR4 hS0)
  have e7 : 0 ≤ R ^ 4 * (N * n ^ 2) := by positivity
  nlinarith [e1, e2, e3, e4, e5, e6, e7, h]

theorem budget0 (r k N : ℕ) (hk : 2 ≤ k) (A₀ Cc : ℝ) (hCc : 150 ≤ Cc)
    (h : Cc * ((r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (r : ℝ) + k + 1) ^ 2 + (2 * (r : ℝ) + k + 1) ^ 3) ≤ A₀) :
    (127 * ((r : ℝ) + 1) ^ 3 * ((N : ℝ) * (2 * (r : ℝ) + k + 1) ^ 2 + (2 * (r : ℝ) + k + 1) ^ 3) + 1) +
      2 * ((r : ℝ) + 1) * (5 + 3 * ((r : ℝ) + 1) * ((N : ℝ) + 2) * (2 * (r : ℝ) + k + 1) + (N : ℝ) * r) ≤ A₀ := by
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  exact budget0_abs ((r : ℝ) + 1) (2 * (r : ℝ) + k + 1) (N : ℝ) (r : ℝ) Cc A₀ (by linarith) (by linarith)
    (by linarith) hr0 (Nat.cast_nonneg N) hCc h

theorem level_zero_case (Cc : ℝ) (hCc : 150 ≤ Cc) (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (T : D.LevTower k r Wp Wq) (f : B.Mat k r → (Wq →L[ℂ] Wp)) (χ : ℝ → ℝ) (A₀ : ℝ) (N : ℕ) (P0 : M.Par)
    (hPk : P0.k = k) (hPr : P0.r = r) (hk2 : 2 ≤ k) (hχ : C6.IsCut0 χ) (hfA : ∀ m : ℕ, B.InCC A₀ m f)
    (hA₀ : Cc * ((r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (r : ℝ) + k + 1) ^ 2 + (2 * (r : ℝ) + k + 1) ^ 3) ≤ A₀)
    (ε : ℝ) (hε : 0 < ε) (hi : 0 ≤ r) (w : List C.Letter) (p : C.LPt) (hp : D.IsLocPt p 0)
    (a : Wd.Ix (Fin w.length)) : ∃ ε' : ℝ, 0 < ε' ∧
        JC.CCCoefM (T.bs 0) (P5.Auser P0 N + 1) (P5.mmUser P0 N) ε'
          (D.castF (by simp [hp.2]) (D.sliceAt k r T.base.z T.base.z'
            (D.uwG k r T.base.z T.base.z' (D.cutF T.base χ f ε) 0 hi w a) p)) := by
  obtain rfl : p = [] := by
    cases p with
    | nil => rfl
    | cons b p =>
      exfalso
      have h1 := (hp.1 b (by simp)).1
      have h2 := hp.2
      simp [D.ptSize] at h2
      omega
  have hfun : (D.castF (by simp [hp.2]) (D.sliceAt k r T.base.z T.base.z'
      (D.uwG k r T.base.z T.base.z' (D.cutF T.base χ f ε) 0 hi w a) []) : B.Mat k (r - 0) → (Wq →L[ℂ] Wp)) =
      (if a = Wd.e1 then D.cutF T.base χ f ε else 0) := by
    funext γ
    have hc : D.castM (k := k) (a := r - 0) (b := r - D.ptSize []) (by simp [hp.2]) γ = γ := by
      ext i j; rfl
    simp only [D.castF]
    rw [hc, Formalism.FourierDecayAlt.P.Dx1.SN.sliceAt_nil k r _ _ T.base.z_mem T.base.z'_mem,
      Formalism.FourierDecayAlt.P.Dx1.LZ.uwG_zero]
  rw [hfun]
  by_cases ha : a = Wd.e1
  · rw [if_pos ha]
    obtain ⟨ρ, rfl⟩ : ∃ ρ, r = 0 + ρ := ⟨r, (zero_add r).symm⟩
    have hb := budget0 (0 + ρ) k N hk2 A₀ Cc hCc hA₀
    obtain ⟨ε', hε', h1, h2, h3⟩ := Formalism.FourierDecayAlt.P.JCTx6.Lev0.level_zero_estimate T.base.z T.base.z' f χ hχ A₀ hfA ε hε
      (P5.Auser P0 N + 1) (P5.mmUser P0 N) (by
        simp only [P5.Auser, P5.mmUser, P5.nV, hPk, hPr]
        push_cast
        push_cast at hb
        linarith)
    exact ⟨ε', hε', h1, h2, h3⟩
  · rw [if_neg ha]
    refine ⟨1, one_pos, ?_, ⟨0, ?_⟩, fun g _ h => (h rfl).elim⟩
    · exact (Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_zero (A := 0)).1
    · exact Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_zero

end

end Formalism.FourierDecayAlt.P.JCTx6.Link

namespace Formalism.FourierDecayAlt.P.JCTx6.Link2

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants MeasureTheory

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section casts

variable {k : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem castV_self {a : ℕ} (h : a = a) (v : Fin (2 * a + k + 1) → ℂ) : D.castV h v = v := by
  rfl

theorem castF_self {a : ℕ} (h : a = a) (F : B.Mat k a → E) : D.castF h F = F := by
  first
    | rfl
    | (funext g; simp [D.castF, D.castM])

theorem castF_uwG {a b : ℕ} (e : a = b) (z z' : Fin (2 * b + k + 1) → ℂ) (F : B.Mat k b → E) (j : ℕ)
    (hj : j ≤ b) (hj' : j ≤ a) (w : List C.Letter) (x : Wd.Ix (Fin w.length)) :
    D.castF e (D.uwG k b z z' F j hj w x) =
      D.uwG k a (D.castV e.symm z) (D.castV e.symm z') (D.castF e F) j hj' w x := by
  subst e
  simp only [castF_self, castV_self]

theorem uwG_level {r : ℕ} (z z' : Fin (2 * r + k + 1) → ℂ) (F : B.Mat k r → E) {i j : ℕ} (e : i = j)
    (hi : i ≤ r) (hj : j ≤ r) (w : List C.Letter) (x : Wd.Ix (Fin w.length)) :
    D.uwG k r z z' F i hi w x = D.uwG k r z z' F j hj w x := by
  subst e
  rfl

theorem castF_cutF {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] {a b : ℕ} (e : a = b) (Bs : B.RealPlaceData k b Wp Wq) (χ : ℝ → ℝ)
    (f : B.Mat k b → (Wq →L[ℂ] Wp)) (ε : ℝ) :
    D.castF e (D.cutF Bs χ f ε) =
      fun x => ((χ (Gf k a (D.castV e.symm Bs.z) (D.castV e.symm Bs.z') x / ε) : ℝ) : ℂ) • D.castF e f x := by
  subst e
  simp only [castF_self, castV_self]
  rfl

theorem ckOn_castF {a b : ℕ} (e : a = b) {m : ℕ∞} {F : B.Mat k b → E} (h : B.CkOn m (B.GV k b) F) :
    B.CkOn m (B.GV k a) (D.castF e F) := by
  subst e
  rw [castF_self]
  exact h

theorem inCC_castF {a b : ℕ} (e : a = b) {A : ℝ} {m : ℕ} {F : B.Mat k b → E} (h : B.InCC A m F) :
    B.InCC A m (D.castF e F) := by
  subst e
  rw [castF_self]
  exact h

end casts

theorem ckOn_cutF {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq) {χ : ℝ → ℝ}
    (hχ : C6.IsCut0 χ) {f : B.Mat k r → (Wq →L[ℂ] Wp)} (hf : B.CkOn ⊤ (B.GV k r) f) (ε : ℝ) :
    B.CkOn ⊤ (B.GV k r) (D.cutF Bs χ f ε) := by
  have hb : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun g : B.Mat k r => χ (Gf k r Bs.z Bs.z' g / ε)) :=
    hχ.1.comp ((Formalism.FourierDecayAlt.P.JCx1.contDiff_Gf Bs.z Bs.z').div_const ε)
  have := Formalism.FourierDecayAlt.P.MinorPolynomials.ckOn_rsmul hb hf
  convert this using 2 with g
  simp [D.cutF, Complex.coe_smul]

theorem ptScal_ne : ∀ (h : C.LPt), (∀ b ∈ h, 1 ≤ b.1 ∧ b.2 ≠ 0) → ∀ a, a < D.ptSize h → D.ptScal h a ≠ 0
  | [], _, a, ha => by simp [D.ptSize] at ha
  | (s, t) :: h, hb, a, ha => by
    simp only [D.ptScal]
    split_ifs with h1
    · exact (hb (s, t) (by simp)).2
    · refine ptScal_ne h (fun b' hb' => hb b' (List.mem_cons_of_mem _ hb')) _ ?_
      rw [Formalism.FourierDecayAlt.P.Dx2.SL.ptSize_cons] at ha
      simp only at ha
      omega

theorem lowV_liftVec {k i ρ j : ℕ} (hj : j = i) (e : i + ρ = j + ρ) (v : Fin (2 * ρ + k + 1) → ℂ) :
    U.lowV k j ρ (D.castV e (liftVec k i ρ v)) = v := by
  subst hj
  funext x
  have hx := x.isLt
  simp only [U.lowV, D.castV, liftVec, Fin.cast_mk, Fin.coe_cast, Fin.val_mk]
  split_ifs with hcond
  · congr 1
    apply Fin.ext
    simp
  · exact (hcond ⟨by omega, by omega⟩).elim

theorem budgetAs (r k N L j : ℕ) (hk : 2 ≤ k) (hL : L ≤ N) (hj : j ≤ r) :
    L * j ≤ 11 * (N * (2 * r + k + 1) ^ 2 + (2 * r + k + 1) ^ 3) + 5 ∧
    (L * j + L * j ^ 2) + j * (L * j) ≤ 11 * (N * (2 * r + k + 1) ^ 2 + (2 * r + k + 1) ^ 3) + 5 ∧
    5 + 3 * (r + 1) * (N + 2) * (2 * r + k + 1) + N * r ≤
      11 * (N * (2 * r + k + 1) ^ 2 + (2 * r + k + 1) ^ 3) + 5 ∧
    (2 * r + k + 1) ^ 3 ≤ 11 * (N * (2 * r + k + 1) ^ 2 + (2 * r + k + 1) ^ 3) + 5 ∧
    1 ≤ N * (2 * r + k + 1) ^ 2 + (2 * r + k + 1) ^ 3 := by
  have hrn : r + 1 ≤ 2 * r + k + 1 := by omega
  have hjn : j ≤ 2 * r + k + 1 := by omega
  have hrn' : r ≤ 2 * r + k + 1 := by omega
  set n := 2 * r + k + 1 with hn_def
  have hn : 1 ≤ n := by omega
  have hnn : n ≤ n ^ 2 := by nlinarith
  have hn23 : n ^ 2 ≤ n ^ 3 := by nlinarith
  have hLj : L * j ≤ N * n := Nat.mul_le_mul hL hjn
  have hLj2 : L * j ^ 2 ≤ N * n ^ 2 := Nat.mul_le_mul hL (Nat.pow_le_pow_left hjn 2)
  have hNn : N * n ≤ N * n ^ 2 := Nat.mul_le_mul_left N hnn
  have hNr : N * r ≤ N * n := Nat.mul_le_mul_left N hrn'
  have h3a : (r + 1) * ((N + 2) * n) ≤ n * ((N + 2) * n) := Nat.mul_le_mul_right ((N + 2) * n) hrn
  have hn3 : 1 ≤ n ^ 3 := by nlinarith
  refine ⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith, by nlinarith⟩

theorem pos_levels (hL : LettersDD) (hP : PosCore) (hI : IntG) (hT : OrbitSliceIntegrable) : ∃ Cp : ℝ, 0 ≤ Cp ∧
    ∀ Cc : ℝ, 16 * Cp ≤ Cc →
    ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (T : D.LevTower k r Wp Wq) (f : B.Mat k r → (Wq →L[ℂ] Wp)) (χ : ℝ → ℝ) (A₀ : ℝ) (N : ℕ) (P0 : M.Par),
    P0.k = k → P0.r = r → 2 ≤ k → C6.IsCut0 χ → B.CkOn ⊤ (B.GV k r) f → (∀ m : ℕ, B.InCC A₀ m f) →
    Cc * ((r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (r : ℝ) + k + 1) ^ 2 + (2 * (r : ℝ) + k + 1) ^ 3) ≤ A₀ →
    ∀ ε : ℝ, 0 < ε → ∀ (i : ℕ) (hi : i ≤ r), 1 ≤ i → ∀ (w : List C.Letter), w.length ≤ N →
      ∀ (p : C.LPt) (hc : r - i = r - D.ptSize p), D.IsLocPt p i → ∀ (a : Wd.Ix (Fin w.length)), ∃ ε' : ℝ, 0 < ε' ∧
        JC.CCCoefM (T.bs i) (P5.Auser P0 N + 1) (P5.mmUser P0 N) ε'
          (D.castF hc (D.sliceAt k r T.base.z T.base.z'
            (D.uwG k r T.base.z T.base.z' (D.cutF T.base χ f ε) i hi w a) p)) := by
  obtain ⟨Cp, hCp0, hCp⟩ := hP hI hT
  refine ⟨Cp, hCp0, ?_⟩
  intro Cc hCc k r Wp Wq _ _ _ _ _ _ T f χ A₀ N P0 hPk hPr hk2 hχ hf hfA hA₀ ε hε i hi hi1 w hw p hc hp a

  obtain ⟨h, n, t, rfl⟩ : ∃ (h : C.LPt) (n : ℕ) (t : ℂ), p = h ++ [(n + 1, t)] := by
    have hne : p ≠ [] := by
      rintro rfl
      have := hp.2
      simp [D.ptSize] at this
      omega
    refine ⟨p.dropLast, (p.getLast hne).1 - 1, (p.getLast hne).2, ?_⟩
    have h1 : 1 ≤ (p.getLast hne).1 := (hp.1 _ (List.getLast_mem hne)).1
    rw [Nat.sub_add_cancel h1]
    exact (List.dropLast_append_getLast hne).symm
  obtain ⟨hpb, hps⟩ := hp
  subst hps
  set ph := D.ptSize h with hph
  have hP : D.ptSize (h ++ [(n + 1, t)]) = ph + (n + 1) := Formalism.FourierDecayAlt.P.Dx2.SL.ptSize_append h (n + 1) t
  have ht : t ≠ 0 := (hpb (n + 1, t) (by simp)).2
  have hloc : D.IsLocPt (h ++ [(n + 1, t)]) (D.ptSize (h ++ [(n + 1, t)])) := ⟨hpb, rfl⟩
  have hlocH := Formalism.FourierDecayAlt.P.Dx2.SL.isLocPt_head hloc
  have hd0 : ∀ q, D.ptDiag h q ≠ 0 := fun q => ptScal_ne h hlocH.1 q q.2
  set ρ := r - D.ptSize (h ++ [(n + 1, t)]) with hρ
  have hsum : ph + (n + 1) + ρ = r := by omega

  have hspec := (Formalism.FourierDecayAlt.P.ptPerm_spec _ _ hloc).1
  have hspec' := (Formalism.FourierDecayAlt.P.ptPerm_spec _ _ hlocH).1
  have hσ : ∀ q : Fin (D.ptSize (h ++ [(n + 1, t)])),
      ((Formalism.FourierDecayAlt.P.Dx2.SL.sigP (n := n) (D.ptPerm h)) (Fin.cast hP q)).val = (D.ptPerm (h ++ [(n + 1, t)]) q).val := by
    intro q
    rw [hspec q, Formalism.FourierDecayAlt.P.Dx2.SL.partner_append (n + 1) t h q.val (by have := q.isLt; omega)]
    by_cases h1 : q.val < D.ptSize h
    · rw [if_pos h1]
      have e : Fin.cast hP q = Fin.castAdd (n + 1) ⟨q.val, h1⟩ := Fin.ext rfl
      rw [e, Formalism.FourierDecayAlt.P.Dx2.SL.blockPerm_castAdd]
      exact hspec' ⟨q.val, h1⟩
    · rw [if_neg h1]
      have e : Fin.cast hP q = Fin.natAdd (D.ptSize h) ⟨q.val - D.ptSize h, by have := q.isLt; omega⟩ :=
        Fin.ext (by simp; omega)
      rw [e, Formalism.FourierDecayAlt.P.Dx2.SL.blockPerm_natAdd]
      simp only [Fin.val_natAdd, Fin.val_rev]
      omega
  have hd : ∀ q : Fin (D.ptSize (h ++ [(n + 1, t)])),
      Formalism.FourierDecayAlt.P.Dx2.SL.dP (n := n) (D.ptDiag h) t (Fin.cast hP q) = D.ptDiag (h ++ [(n + 1, t)]) q := by
    intro q
    simp only [D.ptDiag]
    rw [Formalism.FourierDecayAlt.P.Dx2.SL.scal_append (n + 1) t h q.val (by have := q.isLt; omega)]
    by_cases h1 : q.val < D.ptSize h
    · rw [if_pos h1]
      have e : Fin.cast hP q = Fin.castAdd (n + 1) ⟨q.val, h1⟩ := Fin.ext rfl
      rw [e, Formalism.FourierDecayAlt.P.Dx2.SL.dP, Fin.addCases_left]; rfl
    · rw [if_neg h1]
      have e : Fin.cast hP q = Fin.natAdd (D.ptSize h) ⟨q.val - D.ptSize h, by have := q.isLt; omega⟩ :=
        Fin.ext (by simp; omega)
      rw [e, Formalism.FourierDecayAlt.P.Dx2.SL.dP, Fin.addCases_right]
  set G := D.uwG k r T.base.z T.base.z' (D.cutF T.base χ f ε) (D.ptSize (h ++ [(n + 1, t)])) hi w a with hG
  have hS : ∀ γ : B.Mat k ρ, D.sliceAt k r T.base.z T.base.z' G (h ++ [(n + 1, t)]) γ =
      U.PhiFun (p := ph + (n + 1)) (s := 0) k ρ (Formalism.FourierDecayAlt.P.Dx2.SL.sigP (D.ptPerm h))
        (Formalism.FourierDecayAlt.P.Dx2.SL.dP (D.ptDiag h) t) (D.castV (by omega) T.base.z) (D.castV (by omega) T.base.z')
        (D.castF (by omega) G) (fun a => a.elim0) γ := by
    intro γ
    obtain ⟨-, hT2⟩ := Formalism.FourierDecayAlt.P.Dx2.SL.phi_transport (k := k) (ρ := ρ) hP _ _ hσ _ _ hd
      (D.castV (by omega) T.base.z) (D.castV (by omega) T.base.z') (D.castF (by omega) G) γ
    unfold D.sliceAt
    rw [dif_pos (by omega), hT2]
    simp only [Formalism.FourierDecayAlt.P.Dx2.SL.castV_castV, Formalism.FourierDecayAlt.P.Dx2.SL.castF_castF]
  have e1 : r = ph + (n + 1) + ρ := hsum.symm
  have e2 : ph + (n + 1) + ρ = r := hsum
  have hj1 : 1 ≤ ph + (n + 1) := by omega
  obtain ⟨Θ, hΘ, hΘF⟩ := hL k (ph + (n + 1)) ρ Wp Wq (D.castV e1 T.base.z) (D.castV e1 T.base.z')
    (by omega) w a hj1
  have hFc : B.CkOn ⊤ (B.GV k r) (D.cutF T.base χ f ε) := ckOn_cutF T.base hχ hf ε
  have hFrel : ∀ g ∈ B.GV k (ph + (n + 1) + ρ), U.DjU k (ph + (n + 1)) ρ g ≠ 0 →
      D.castF e2 G g = B.opApply Θ (fun x => ((χ (Gf k (ph + (n + 1) + ρ) (D.castV e1 T.base.z)
        (D.castV e1 T.base.z') x / ε) : ℝ) : ℂ) • D.castF e2 f x) g := by
    intro g hg hD
    have h1 : D.castF e2 G = D.uwG k (ph + (n + 1) + ρ) (D.castV e1 T.base.z) (D.castV e1 T.base.z')
        (D.castF e2 (D.cutF T.base χ f ε)) (ph + (n + 1)) (by omega) w a := by
      rw [hG, castF_uwG e2 _ _ _ _ hi (by omega)]
      exact uwG_level _ _ _ hP _ _ w a
    rw [h1, hΘF _ (ckOn_castF e2 hFc) g hg hD, castF_cutF e2]
  set nd := 2 * r + k + 1 with hnd
  set As := 11 * (N * nd ^ 2 + nd ^ 3) + 5 with hAs
  obtain ⟨b1, b2, b3, b4, b5⟩ := budgetAs r k N w.length (ph + (n + 1)) hk2 hw (by omega)
  have hmmU : P5.mmUser P0 N = 5 + 3 * (r + 1) * (N + 2) * nd + N * r := by
    simp only [P5.mmUser, P5.nV, hPk, hPr, hnd]
  have hAU : P5.Auser P0 N = 127 * ((r : ℝ) + 1) ^ 3 * ((N : ℝ) * (nd : ℝ) ^ 2 + (nd : ℝ) ^ 3) := by
    simp only [P5.Auser, P5.nV, hPk, hPr, hnd]
    try (push_cast; try ring)
  have hX1 : (1 : ℝ) ≤ (N : ℝ) * (nd : ℝ) ^ 2 + (nd : ℝ) ^ 3 := by exact_mod_cast b5
  have hAsR : (As : ℝ) = 11 * ((N : ℝ) * (nd : ℝ) ^ 2 + (nd : ℝ) ^ 3) + 5 := by
    rw [hAs]; push_cast; ring
  have hR1 : (1 : ℝ) ≤ (r : ℝ) + 1 := by have : (0 : ℝ) ≤ r := Nat.cast_nonneg r; linarith
  have hsumR : (((ph + (n + 1) + ρ : ℕ) : ℝ)) = (r : ℝ) := by exact_mod_cast hsum
  obtain ⟨ε', hε', h1, h2, h3⟩ := hCp k ph n ρ Wp Wq (D.castV e1 T.base.z) (D.castV e1 T.base.z')
    (Formalism.FourierDecayAlt.P.Dx1.SN.castV_inWb e1 _ T.base.z_mem) (Formalism.FourierDecayAlt.P.Dx1.SN.castV_inWb e1 _ T.base.z'_mem)
    Θ _ _ hΘ (D.castF e2 f) χ A₀ ε (ckOn_castF e2 hf) (fun m => inCC_castF e2 (hfA m)) hχ hε
    (D.castF e2 G) hFrel (D.ptPerm h) (D.ptDiag h) t hd0 ht As (P5.mmUser P0 N) (P5.Auser P0 N + 1)
    b1 b2 (by rw [hmmU]; exact b3) (by rw [hsum]; exact b4)
    (by
      rw [hsumR, hAU, hAsR]
      have hR3 : (1 : ℝ) ≤ ((r : ℝ) + 1) ^ 3 := one_le_pow₀ hR1
      have : 0 ≤ ((r : ℝ) + 1) ^ 3 * ((N : ℝ) * (nd : ℝ) ^ 2 + (nd : ℝ) ^ 3) := by positivity
      nlinarith)
    (by
      rw [hsumR, hAsR]
      have hR4 : 0 ≤ ((r : ℝ) + 1) ^ 4 := by positivity
      have hX0 : 0 ≤ (N : ℝ) * (nd : ℝ) ^ 2 + (nd : ℝ) ^ 3 := by linarith
      have s1 : Cp * ((r : ℝ) + 1) ^ 4 * (11 * ((N : ℝ) * (nd : ℝ) ^ 2 + (nd : ℝ) ^ 3) + 5) ≤
          Cp * ((r : ℝ) + 1) ^ 4 * (16 * ((N : ℝ) * (nd : ℝ) ^ 2 + (nd : ℝ) ^ 3)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity); linarith
      have s2 : 16 * Cp * (((r : ℝ) + 1) ^ 4 * ((N : ℝ) * (nd : ℝ) ^ 2 + (nd : ℝ) ^ 3)) ≤
          Cc * (((r : ℝ) + 1) ^ 4 * ((N : ℝ) * (nd : ℝ) ^ 2 + (nd : ℝ) ^ 3)) :=
        mul_le_mul_of_nonneg_right hCc (by positivity)
      have s3 : Cc * ((r : ℝ) + 1) ^ 4 * ((N : ℝ) * (nd : ℝ) ^ 2 + (nd : ℝ) ^ 3) ≤ A₀ := by
        have hndR : (nd : ℝ) = 2 * (r : ℝ) + k + 1 := by rw [hnd]; push_cast; ring
        rw [hndR]; exact hA₀
      nlinarith)
  have hfun : D.castF hc (D.sliceAt k r T.base.z T.base.z' G (h ++ [(n + 1, t)])) =
      fun γ => U.PhiFun (p := ph + (n + 1)) (s := 0) k ρ (Formalism.FourierDecayAlt.P.Dx2.SL.sigP (D.ptPerm h))
        (Formalism.FourierDecayAlt.P.Dx2.SL.dP (D.ptDiag h) t) (D.castV e1 T.base.z) (D.castV e1 T.base.z')
        (D.castF e2 G) (fun a => a.elim0) γ := by
    rw [castF_self]
    funext γ
    exact hS γ
  rw [hfun]
  have hlz : ∀ v : Fin (2 * r + k + 1) → ℂ,
      v = D.castV (by omega) (liftVec k (D.ptSize (h ++ [(n + 1, t)])) ρ (T.bs (D.ptSize (h ++ [(n + 1, t)]))).z) →
      U.lowV k (ph + (n + 1)) ρ (D.castV e1 v) = (T.bs (D.ptSize (h ++ [(n + 1, t)]))).z := by
    intro v hv
    rw [hv, Formalism.FourierDecayAlt.P.Dx2.SL.castV_castV]
    exact lowV_liftVec hP.symm _ _
  have hzl : T.base.z = D.castV (by omega)
      (liftVec k (D.ptSize (h ++ [(n + 1, t)])) ρ (T.bs (D.ptSize (h ++ [(n + 1, t)]))).z) :=
    (T.z_lev _ hi).symm
  have hzl' : T.base.z' = D.castV (by omega)
      (liftVec k (D.ptSize (h ++ [(n + 1, t)])) ρ (T.bs (D.ptSize (h ++ [(n + 1, t)]))).z') :=
    (T.z'_lev _ hi).symm
  have hz1 := hlz _ hzl
  have hlz' : U.lowV k (ph + (n + 1)) ρ (D.castV e1 T.base.z') = (T.bs (D.ptSize (h ++ [(n + 1, t)]))).z' := by
    rw [hzl', Formalism.FourierDecayAlt.P.Dx2.SL.castV_castV]
    exact lowV_liftVec hP.symm _ _
  refine ⟨ε', hε', h1, h2, fun γ hγ hne => ?_⟩
  have := h3 γ hγ hne
  rwa [hz1, hlz'] at this

end

end Formalism.FourierDecayAlt.P.JCTx6.Link2

open Matrix MvPolynomial
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.JCTx6.Let

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.U Formalism.REAL Formalism.QuantumDeterminants PI.UnitaryGroupMassFormula.UsCompose

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k j ρ : ℕ}

def Sj (k j ρ : ℕ) : Set (Mat k (j + ρ)) := {g | g ∈ GV k (j + ρ) ∧ DjU k j ρ g ≠ 0}

theorem contDjU : Continuous (DjU k j ρ) := by
  unfold U.DjU U.Zh
  first
    | fun_prop
    | exact Continuous.matrix_det (by fun_prop)

section loc

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem rdV_loc {X : Mat k (j + ρ)} (hX : inLie k (j + ρ) X) {h₁ h₂ : Mat k (j + ρ) → E}
    (hh : ∀ g ∈ Sj k j ρ, h₁ g = h₂ g) : ∀ g ∈ Sj k j ρ, RdV X h₁ g = RdV X h₂ g := by
  intro g hg
  unfold RdV
  apply Filter.EventuallyEq.deriv_eq
  have hc : Continuous (fun t : ℝ => g * NormedSpace.exp ((t : ℂ) • X)) := (B5.curve_contDiff g X).continuous
  have hD : ContinuousAt (fun t : ℝ => DjU k j ρ (g * NormedSpace.exp ((t : ℂ) • X))) 0 :=
    (contDjU.comp hc).continuousAt
  have h0 : DjU k j ρ (g * NormedSpace.exp (((0 : ℝ) : ℂ) • X)) ≠ 0 := by rw [B5.curve_zero]; exact hg.2
  filter_upwards [hD.eventually_ne h0] with t ht
  exact hh _ ⟨B5.curve_mem hg.1 hX t, ht⟩

theorem shape_append (F : Mat k (j + ρ) → E) (L₁ L₂ : FS k (j + ρ)) (g : Mat k (j + ρ)) :
    shape k j ρ F (L₁ ++ L₂) g = shape k j ρ F L₁ g + shape k j ρ F L₂ g := by
  simp [shape, List.map_append, List.sum_append]

theorem shape_nil (F : Mat k (j + ρ) → E) (g : Mat k (j + ρ)) : shape k j ρ F [] g = 0 := by
  simp [shape]

theorem shape_flatMap' {α : Type*} (F : Mat k (j + ρ) → E) (l : List α) (f : α → FS k (j + ρ))
    (g : Mat k (j + ρ)) :
    shape k j ρ F (l.flatMap f) g = (l.map fun a => shape k j ρ F (f a) g).sum := by
  induction l with
  | nil => simp [shape]
  | cons a l ih => rw [List.flatMap_cons, shape_append, ih, List.map_cons, List.sum_cons]

theorem sv_const (u : ℂ) (g : Mat k (j + ρ)) : sv k j ρ (C u, 0, 0) g = u := by
  simp [sv]

end loc

def topFS (k j ρ : ℕ) (u : ℂ) (a b : Fin (2 * (j + ρ) + k + 1)) (L : FS k (j + ρ)) : FS k (j + ρ) :=
  (if a = b then L.map (fun e => (mulSC (C u, 0, 0) e.1, e.2)) else []) ++
    (step k j ρ (JFxB.Xa k (j + ρ) a b) L ++
      (step k j ρ (JFxB.Xb k (j + ρ) a b) L).map (fun e => (mulSC (C Complex.I, 0, 0) e.1, e.2)))

theorem bd_append {κ ℓ : ℕ} {L₁ L₂ : FS k (j + ρ)} (h₁ : Bd k j ρ κ ℓ L₁) (h₂ : Bd k j ρ κ ℓ L₂) :
    Bd k j ρ κ ℓ (L₁ ++ L₂) := by
  intro e he
  rcases List.mem_append.mp he with h | h
  exacts [h₁ e h, h₂ e h]

theorem bd_mulC {κ ℓ : ℕ} (u : ℂ) {L : FS k (j + ρ)} (h : Bd k j ρ κ ℓ L) :
    Bd k j ρ κ ℓ (L.map (fun e => (mulSC (C u, 0, 0) e.1, e.2))) := by
  intro e he
  obtain ⟨e0, he0, rfl⟩ := List.mem_map.mp he
  obtain ⟨h1, h2, h3⟩ := h e0 he0
  refine ⟨?_, h2, h3⟩
  simp only [mulSC]
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  simp [MvPolynomial.totalDegree_C, h1]

theorem bd_nil {κ ℓ : ℕ} : Bd k j ρ κ ℓ [] := by
  intro e he
  simp at he

private theorem bd_mono' {κ ℓ κ' ℓ' : ℕ} {L : FS k (j + ρ)} (h : Bd k j ρ κ ℓ L) (hκ : κ ≤ κ')
    (hℓ : ℓ ≤ ℓ') : Bd k j ρ κ' ℓ' L := by
  intro e he
  obtain ⟨h1, h2, h3⟩ := h e he
  exact ⟨h1.trans hκ, h2.trans hℓ, h3⟩

theorem bd_topFS {κ ℓ : ℕ} (u : ℂ) (a b : Fin (2 * (j + ρ) + k + 1)) {L : FS k (j + ρ)}
    (h : Bd k j ρ κ ℓ L) : Bd k j ρ (κ + j) (ℓ + 1) (topFS k j ρ u a b L) := by
  have hP : DegDP := fun N X q => degDP X q
  unfold topFS
  refine bd_append ?_ (bd_append ?_ ?_)
  · split_ifs
    · exact bd_mono' (bd_mulC u h) (Nat.le_add_right _ _) (Nat.le_succ _)
    · exact bd_nil
  · exact bd_step hP degD (JFxB.Xa_lie a b) h
  · exact bd_mulC Complex.I (bd_step hP degD (JFxB.Xb_lie a b) h)

section shapes

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem top_shape {F : Mat k (j + ρ) → E} (hF : CkOn ⊤ (GV k (j + ρ)) F) {κ ℓ : ℕ} {L : FS k (j + ρ)}
    (hL : Bd k j ρ κ ℓ L) {h : Mat k (j + ρ) → E} (hh : ∀ g ∈ Sj k j ρ, h g = shape k j ρ F L g)
    (u : ℂ) (a b : Fin (2 * (j + ρ) + k + 1)) :
    ∀ g ∈ Sj k j ρ, Top (EabH (Hpk k (j + ρ))) u a b h g = shape k j ρ F (topFS k j ρ u a b L) g := by
  intro g hg
  have hFm : CkOn ((ℓ + 1 : ℕ) : ℕ∞) (GV k (j + ρ)) F := B5.ckOn_mono le_top hF
  have hLie : ∀ e ∈ L, ∀ X ∈ e.2, inLie k (j + ρ) X := fun e he => (hL e he).2.2
  have hlen : ∀ e ∈ L, e.2.length + [JFxB.Xa k (j + ρ) a b].length ≤ ℓ + 1 := fun e he => by
    simp only [List.length_cons, List.length_nil]; have := (hL e he).2.1; omega
  have hlen' : ∀ e ∈ L, e.2.length + [JFxB.Xb k (j + ρ) a b].length ≤ ℓ + 1 := fun e he => by
    simp only [List.length_cons, List.length_nil]; have := (hL e he).2.1; omega
  have e1 : RdV (JFxB.Xa k (j + ρ) a b) h g = shape k j ρ F (step k j ρ (JFxB.Xa k (j + ρ) a b) L) g := by
    rw [rdV_loc (JFxB.Xa_lie a b) hh g hg]
    exact expand k j ρ E (ℓ + 1) F hFm [JFxB.Xa k (j + ρ) a b] L
      (by simpa using JFxB.Xa_lie a b) hLie hlen g hg.1 hg.2
  have e2 : RdV (JFxB.Xb k (j + ρ) a b) h g = shape k j ρ F (step k j ρ (JFxB.Xb k (j + ρ) a b) L) g := by
    rw [rdV_loc (JFxB.Xb_lie a b) hh g hg]
    exact expand k j ρ E (ℓ + 1) F hFm [JFxB.Xb k (j + ρ) a b] L
      (by simpa using JFxB.Xb_lie a b) hLie hlen' g hg.1 hg.2
  rw [JFxB.top_apply]
  have eE : EabH (Hpk k (j + ρ)) a b h g =
      RdV (JFxB.Xa k (j + ρ) a b) h g + Complex.I • RdV (JFxB.Xb k (j + ρ) a b) h g := rfl
  rw [eE, e1, e2, topFS, shape_append, shape_append, shape_mul, sv_const]
  split_ifs with hab
  · rw [shape_mul, sv_const, hh g hg]
  · rw [shape_nil]

def foldFS (k j ρ : ℕ) (ts : List (ℂ × Fin (2 * (j + ρ) + k + 1) × Fin (2 * (j + ρ) + k + 1))) (L : FS k (j + ρ)) :
    FS k (j + ρ) :=
  ts.foldr (fun t L => topFS k j ρ t.1 t.2.1 t.2.2 L) L

theorem bd_foldFS (ts : List (ℂ × Fin (2 * (j + ρ) + k + 1) × Fin (2 * (j + ρ) + k + 1))) {κ ℓ : ℕ}
    {L : FS k (j + ρ)} (h : Bd k j ρ κ ℓ L) : Bd k j ρ (κ + ts.length * j) (ℓ + ts.length) (foldFS k j ρ ts L) := by
  induction ts with
  | nil => simpa [foldFS] using h
  | cons t ts ih =>
    have h2 := bd_topFS t.1 t.2.1 t.2.2 ih
    have e1 : κ + (t :: ts).length * j = κ + ts.length * j + j := by simp only [List.length_cons]; ring
    have e2 : ℓ + (t :: ts).length = ℓ + ts.length + 1 := by simp only [List.length_cons]; ring
    rw [e1, e2]
    exact h2

theorem fold_shape {F : Mat k (j + ρ) → E} (hF : CkOn ⊤ (GV k (j + ρ)) F)
    (ts : List (ℂ × Fin (2 * (j + ρ) + k + 1) × Fin (2 * (j + ρ) + k + 1))) {κ ℓ : ℕ} {L : FS k (j + ρ)}
    (hL : Bd k j ρ κ ℓ L) {h : Mat k (j + ρ) → E} (hh : ∀ g ∈ Sj k j ρ, h g = shape k j ρ F L g) :
    ∀ g ∈ Sj k j ρ, (ts.map fun t => Top (EabH (Hpk k (j + ρ))) t.1 t.2.1 t.2.2).foldr (fun T h => T h) h g =
      shape k j ρ F (foldFS k j ρ ts L) g := by
  induction ts with
  | nil => intro g hg; exact hh g hg
  | cons t ts ih =>
    intro g hg
    exact top_shape hF (bd_foldFS ts hL) ih t.1 t.2.1 t.2.2 g hg

end shapes

end Formalism.FourierDecayAlt.P.JCTx6.Let

namespace Formalism.FourierDecayAlt.P.JCTx6.Let

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.U Formalism.REAL Formalism.QuantumDeterminants PI.UnitaryGroupMassFormula.UsCompose

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k j ρ : ℕ}

def linA (k r : ℕ) (e c : Fin (2 * r + k + 1)) : MvPolynomial (Vr (2 * r + k + 1)) ℂ :=
  ∑ x, C (Hpk k r e x) * X (Sum.inl (x, c))

def linV (k r : ℕ) (e i : Fin (2 * r + k + 1)) : MvPolynomial (Vr (2 * r + k + 1)) ℂ :=
  ∑ x, ∑ y, C (Hpk k r i x * Hpk k r y e) * X (Sum.inr (y, x))

theorem deg_linA (k r : ℕ) (e c : Fin (2 * r + k + 1)) : (linA k r e c).totalDegree ≤ 1 := by
  unfold linA
  refine (MvPolynomial.totalDegree_finset_sum _ _).trans (Finset.sup_le fun x _ => ?_)
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  simp only [MvPolynomial.totalDegree_C, MvPolynomial.totalDegree_X, zero_add, le_refl]

theorem deg_linV (k r : ℕ) (e i : Fin (2 * r + k + 1)) : (linV k r e i).totalDegree ≤ 1 := by
  unfold linV
  refine (MvPolynomial.totalDegree_finset_sum _ _).trans (Finset.sup_le fun x _ => ?_)
  refine (MvPolynomial.totalDegree_finset_sum _ _).trans (Finset.sup_le fun y _ => ?_)
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  simp only [MvPolynomial.totalDegree_C, MvPolynomial.totalDegree_X, zero_add, le_refl]

theorem vars_inl {N : ℕ} (g : Matrix (Fin N) (Fin N) ℂ) (x : Fin N × Fin N) : vars g (Sum.inl x) = g x.1 x.2 := rfl

theorem vars_inr {N : ℕ} (g : Matrix (Fin N) (Fin N) ℂ) (x : Fin N × Fin N) :
    vars g (Sum.inr x) = star (g x.1 x.2) := rfl

theorem eval_linA (k r : ℕ) (e c : Fin (2 * r + k + 1)) (g : Mat k r) :
    eval (vars g) (linA k r e c) = herm (Hpk k r) (g *ᵥ bvec c) (bvec e) := by
  simp only [linA, MvPolynomial.eval_sum, MvPolynomial.eval_mul, MvPolynomial.eval_C, MvPolynomial.eval_X,
    vars_inl]
  simp [herm, bvec, Matrix.mulVec, dotProduct, Pi.single_apply]

theorem eval_linV (k r : ℕ) (e i : Fin (2 * r + k + 1)) (g : Mat k r) (hg : g ∈ GV k r) :
    eval (vars g) (linV k r e i) = (g⁻¹ *ᵥ bvec e) i := by
  rw [Formalism.FourierDecayAlt.P.JCx2.mn_inv_gv hg]
  simp [linV, vars_inr, bvec, Matrix.mulVec, dotProduct, Pi.single_apply, Matrix.mul_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  ring

end Formalism.FourierDecayAlt.P.JCTx6.Let

namespace Formalism.FourierDecayAlt.P.JCTx6.Let

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.U Formalism.REAL Formalism.QuantumDeterminants PI.UnitaryGroupMassFormula.UsCompose

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k j ρ : ℕ}

theorem bd_flatMap {α : Type*} {κ ℓ : ℕ} (l : List α) (f : α → FS k (j + ρ)) (h : ∀ a ∈ l, Bd k j ρ κ ℓ (f a)) :
    Bd k j ρ κ ℓ (l.flatMap f) := by
  intro e he
  obtain ⟨a, ha, he⟩ := List.mem_flatMap.mp he
  exact h a ha e he

theorem bd_mulP {κ ℓ d : ℕ} (q : MvPolynomial (Vr (2 * (j + ρ) + k + 1)) ℂ) (hq : q.totalDegree ≤ d) (a b : ℕ)
    {L : FS k (j + ρ)} (h : Bd k j ρ κ ℓ L) :
    Bd k j ρ (d + κ) ℓ (L.map (fun e => (mulSC (q, a, b) e.1, e.2))) := by
  intro e he
  obtain ⟨e0, he0, rfl⟩ := List.mem_map.mp he
  obtain ⟨h1, h2, h3⟩ := h e0 he0
  exact ⟨(MvPolynomial.totalDegree_mul _ _).trans (add_le_add hq h1), h2, h3⟩

def tsQ (n m : ℕ) (u : ℂ) (a c : Fin m → Fin n) (σ : Equiv.Perm (Fin m)) : List (ℂ × Fin n × Fin n) :=
  List.ofFn fun i : Fin m => (u - ((i : ℕ) : ℂ), a (σ i), c i)

def qmFS (k j ρ m : ℕ) (u : ℂ) (a c : Fin m → Fin (2 * (j + ρ) + k + 1)) (L : FS k (j + ρ)) : FS k (j + ρ) :=
  (Finset.univ : Finset (Equiv.Perm (Fin m))).toList.flatMap fun σ =>
    (foldFS k j ρ (tsQ _ m u a c σ) L).map (fun e => (mulSC (C ((Equiv.Perm.sign σ : ℤ) : ℂ), 0, 0) e.1, e.2))

theorem bd_qmFS (m : ℕ) (u : ℂ) (a c : Fin m → Fin (2 * (j + ρ) + k + 1)) {κ ℓ : ℕ} {L : FS k (j + ρ)}
    (h : Bd k j ρ κ ℓ L) : Bd k j ρ (κ + m * j) (ℓ + m) (qmFS k j ρ m u a c L) := by
  unfold qmFS
  apply bd_flatMap
  intro σ _
  have h1 := bd_foldFS (tsQ _ m u a c σ) h
  have hl : (tsQ (2 * (j + ρ) + k + 1) m u a c σ).length = m := by simp [tsQ]
  rw [hl] at h1
  exact bd_mulC _ h1

section shapes

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem qm_shape {F : Mat k (j + ρ) → E} (hF : CkOn ⊤ (GV k (j + ρ)) F) {κ ℓ : ℕ} {L : FS k (j + ρ)}
    (hL : Bd k j ρ κ ℓ L) {h : Mat k (j + ρ) → E} (hh : ∀ g ∈ Sj k j ρ, h g = shape k j ρ F L g)
    (m : ℕ) (u : ℂ) (a c : Fin m → Fin (2 * (j + ρ) + k + 1)) :
    ∀ g ∈ Sj k j ρ, qminorOp (EabH (Hpk k (j + ρ))) a c u h g = shape k j ρ F (qmFS k j ρ m u a c L) g := by
  intro g hg
  unfold qminorOp qmFS
  rw [Finset.sum_apply, shape_flatMap', Finset.sum_map_toList]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Pi.smul_apply, shape_mul, sv_const]
  congr 1
  have e : (List.ofFn fun i : Fin m => Top (EabH (E := E) (Hpk k (j + ρ))) (u - ((i : ℕ) : ℂ)) (a (σ i)) (c i)) =
      (tsQ _ m u a c σ).map (fun t => Top (EabH (E := E) (Hpk k (j + ρ))) t.1 t.2.1 t.2.2) := by
    rw [tsQ, List.map_ofFn]; rfl
  rw [e]
  exact fold_shape hF _ hL hh g hg

end shapes

end Formalism.FourierDecayAlt.P.JCTx6.Let

namespace Formalism.FourierDecayAlt.P.JCTx6.Let

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.U Formalism.REAL Formalism.QuantumDeterminants PI.UnitaryGroupMassFormula.UsCompose

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k j ρ : ℕ}

def qAA (k r m : ℕ) (hm : m ≤ r) (c : Fin m → Fin (2 * r + k + 1)) : MvPolynomial (Vr (2 * r + k + 1)) ℂ :=
  (Matrix.of fun a l : Fin m => linA k r (eI k r (Fin.castLE hm a)) (c l)).det

def qAV (k r m : ℕ) (hm : m ≤ r) (B : Fin m → Fin (2 * r + k + 1)) : MvPolynomial (Vr (2 * r + k + 1)) ℂ :=
  (Matrix.of fun a l : Fin m => linV k r (eI k r (Fin.castLE hm a)) (B l)).det

private theorem det_totalDegree_le_of_entries_totalDegree_le_one {m N : ℕ} (M : Matrix (Fin m) (Fin m) (MvPolynomial (Vr N) ℂ))
    (h : ∀ a l, (M a l).totalDegree ≤ 1) : M.det.totalDegree ≤ m := by
  rw [Matrix.det_apply]
  refine (MvPolynomial.totalDegree_finset_sum _ _).trans (Finset.sup_le fun σ _ => ?_)
  have hb : (∏ i, M (σ i) i).totalDegree ≤ m := by
    refine (MvPolynomial.totalDegree_finset_prod _ _).trans ?_
    calc ∑ i, (M (σ i) i).totalDegree ≤ ∑ _i : Fin m, 1 := Finset.sum_le_sum fun i _ => h _ _
      _ = m := by simp
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs <;> rw [hs]
  · rw [one_smul]; exact hb
  · rw [Units.neg_smul, one_smul, MvPolynomial.totalDegree_neg]; exact hb

theorem deg_qAA (k r m : ℕ) (hm : m ≤ r) (c : Fin m → Fin (2 * r + k + 1)) : (qAA k r m hm c).totalDegree ≤ m := by
  exact det_totalDegree_le_of_entries_totalDegree_le_one _ fun a l => deg_linA _ _ _ _

theorem deg_qAV (k r m : ℕ) (hm : m ≤ r) (B : Fin m → Fin (2 * r + k + 1)) : (qAV k r m hm B).totalDegree ≤ m := by
  exact det_totalDegree_le_of_entries_totalDegree_le_one _ fun a l => deg_linV _ _ _ _

theorem eval_qAA (k r m : ℕ) (hm : m ≤ r) (c : Fin m → Fin (2 * r + k + 1)) (g : Mat k r) :
    eval (vars g) (qAA k r m hm c) =
      (Matrix.of fun a l : Fin m => herm (Hpk k r) (g *ᵥ bvec (c l)) (bvec (eI k r (Fin.castLE hm a)))).det := by
  unfold qAA
  rw [RingHom.map_det]
  congr 1
  ext a l
  simp [eval_linA]

theorem eval_qAV (k r m : ℕ) (hm : m ≤ r) (B : Fin m → Fin (2 * r + k + 1)) (g : Mat k r) (hg : g ∈ GV k r) :
    eval (vars g) (qAV k r m hm B) =
      (Matrix.of fun a l : Fin m => (g⁻¹ *ᵥ bvec (eI k r (Fin.castLE hm a))) (B l)).det := by
  unfold qAV
  rw [RingHom.map_det]
  congr 1
  ext a l
  simp [eval_linV k r _ _ g hg]

open Classical in

def aaFS (k j ρ m : ℕ) (hm : m ≤ j + ρ) (u : ℂ) (L : FS k (j + ρ)) : FS k (j + ρ) :=
  (Finset.univ : Finset (Fin m → Fin (2 * (j + ρ) + k + 1))).toList.flatMap fun c =>
    if StrictMono c then
      (qmFS k j ρ m u (C3.xR k (j + ρ) m hm) c L).map (fun e => (mulSC (qAA k (j + ρ) m hm c, 0, 0) e.1, e.2))
    else []

open Classical in

def avFS (k j ρ m : ℕ) (hm : m ≤ j + ρ) (ell : ℂ) (L : FS k (j + ρ)) : FS k (j + ρ) :=
  (Finset.univ : Finset (Fin m → Fin (2 * (j + ρ) + k + 1))).toList.flatMap fun B =>
    if StrictMono (fun l => C3.keyS k (j + ρ) (B l)) then
      (qmFS k j ρ m (ell + (m : ℂ) - 1) B (C3.sR k (j + ρ) m hm) L).map
        (fun e => (mulSC (qAV k (j + ρ) m hm B, 0, 0) e.1, e.2))
    else []

theorem bd_aaFS (m : ℕ) (hm : m ≤ j + ρ) (u : ℂ) {κ ℓ : ℕ} {L : FS k (j + ρ)} (h : Bd k j ρ κ ℓ L) :
    Bd k j ρ (m + (κ + m * j)) (ℓ + m) (aaFS k j ρ m hm u L) := by
  unfold aaFS
  apply bd_flatMap
  intro c _
  split_ifs
  · exact bd_mulP _ (deg_qAA k (j + ρ) m hm c) 0 0 (bd_qmFS m u _ c h)
  · exact bd_nil

theorem bd_avFS (m : ℕ) (hm : m ≤ j + ρ) (ell : ℂ) {κ ℓ : ℕ} {L : FS k (j + ρ)} (h : Bd k j ρ κ ℓ L) :
    Bd k j ρ (m + (κ + m * j)) (ℓ + m) (avFS k j ρ m hm ell L) := by
  unfold avFS
  apply bd_flatMap
  intro B _
  split_ifs
  · exact bd_mulP _ (deg_qAV k (j + ρ) m hm B) 0 0 (bd_qmFS m _ B _ h)
  · exact bd_nil

section shapes

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem sv_poly (q : MvPolynomial (Vr (2 * (j + ρ) + k + 1)) ℂ) (g : Mat k (j + ρ)) :
    sv k j ρ (q, 0, 0) g = eval (vars g) q := by
  simp [sv]

theorem aa_shape {F : Mat k (j + ρ) → E} (hF : CkOn ⊤ (GV k (j + ρ)) F) {κ ℓ : ℕ} {L : FS k (j + ρ)}
    (hL : Bd k j ρ κ ℓ L) {h : Mat k (j + ρ) → E} (hh : ∀ g ∈ Sj k j ρ, h g = shape k j ρ F L g)
    (m : ℕ) (hm : m ≤ j + ρ) (u : ℂ) :
    ∀ g ∈ Sj k j ρ, C3.AAop k (j + ρ) m hm u h g = shape k j ρ F (aaFS k j ρ m hm u L) g := by
  intro g hg
  unfold C3.AAop aaFS
  rw [shape_flatMap', Finset.sum_map_toList]
  refine Finset.sum_congr rfl fun c _ => ?_
  by_cases hc : StrictMono c
  · rw [if_pos hc, if_pos hc, shape_mul, sv_poly, eval_qAA, qm_shape hF hL hh m u _ c g hg]
  · rw [if_neg hc, if_neg hc, shape_nil]

theorem av_shape {F : Mat k (j + ρ) → E} (hF : CkOn ⊤ (GV k (j + ρ)) F) {κ ℓ : ℕ} {L : FS k (j + ρ)}
    (hL : Bd k j ρ κ ℓ L) {h : Mat k (j + ρ) → E} (hh : ∀ g ∈ Sj k j ρ, h g = shape k j ρ F L g)
    (m : ℕ) (hm : m ≤ j + ρ) (ell : ℂ) :
    ∀ g ∈ Sj k j ρ, C3.AAvop k (j + ρ) m hm ell h g = shape k j ρ F (avFS k j ρ m hm ell L) g := by
  intro g hg
  unfold C3.AAvop avFS
  rw [shape_flatMap', Finset.sum_map_toList]
  refine Finset.sum_congr rfl fun B _ => ?_
  by_cases hc : StrictMono (fun l => C3.keyS k (j + ρ) (B l))
  · rw [if_pos hc, if_pos hc, shape_mul, sv_poly, eval_qAV _ _ _ _ _ g hg.1, qm_shape hF hL hh m _ B _ g hg]
  · rw [if_neg hc, if_neg hc, shape_nil]

end shapes

end Formalism.FourierDecayAlt.P.JCTx6.Let

namespace Formalism.FourierDecayAlt.P.JCTx6.Let

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.U Formalism.REAL Formalism.QuantumDeterminants PI.UnitaryGroupMassFormula.UsCompose

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k j ρ : ℕ}

def letFS (k j ρ : ℕ) (l : C.Letter) (e : Fin 2) (L : FS k (j + ρ)) : FS k (j + ρ) :=
  if l.1 then
    (aaFS k j ρ (j - e) (by omega) ((l.2 : ℂ) + ((2 * (j + ρ) + k : ℕ) : ℂ) / 2) L).map
      (fun x => (mulSC (C 1, 1, 0) x.1, x.2))
  else
    (avFS k j ρ (j - e) (by omega) ((l.2 : ℂ) - ((2 * (j + ρ) + k : ℕ) : ℂ) / 2) L).map
      (fun x => (mulSC (C 1, 0, 1) x.1, x.2))

theorem bd_letFS (l : C.Letter) (e : Fin 2) {κ ℓ : ℕ} {L : FS k (j + ρ)} (h : Bd k j ρ κ ℓ L) :
    Bd k j ρ (κ + (j + j * j)) (ℓ + j) (letFS k j ρ l e L) := by
  unfold letFS
  have hd : j - (e : ℕ) ≤ j := Nat.sub_le _ _
  have hdj : (j - (e : ℕ)) * j ≤ j * j := Nat.mul_le_mul_right j hd
  split_ifs
  · refine bd_mono' (bd_mulP (d := 0) (MvPolynomial.C 1) (by simp) 1 0 (bd_aaFS _ _ _ h)) ?_ ?_
    · linarith
    · omega
  · refine bd_mono' (bd_mulP (d := 0) (MvPolynomial.C 1) (by simp) 0 1 (bd_avFS _ _ _ h)) ?_ ?_
    · linarith
    · omega

section shapes

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem vlet_shape (hj1 : 1 ≤ j) (z z' : Fin (2 * (j + ρ) + k + 1) → ℂ) (hj : j ≤ j + ρ)
    {F : Mat k (j + ρ) → E} (hF : CkOn ⊤ (GV k (j + ρ)) F) {κ ℓ : ℕ} {L : FS k (j + ρ)}
    (hL : Bd k j ρ κ ℓ L) {h : Mat k (j + ρ) → E} (hh : ∀ g ∈ Sj k j ρ, h g = shape k j ρ F L g)
    (l : C.Letter) (e : Fin 2) :
    ∀ g ∈ Sj k j ρ, D.vLet k (j + ρ) z z' j hj l e h g = shape k j ρ F (letFS k j ρ l e L) g := by
  intro g hg
  have hne : ¬ (e = 1 ∧ j = 0) := fun h' => by omega
  unfold D.vLet
  rw [if_neg hne]
  rcases l with ⟨b, y⟩
  cases b
  · simp only [letFS, Bool.false_eq_true, if_false]
    rw [shape_mul, av_shape hF hL hh _ _ _ g hg, Formalism.FourierDecayAlt.P.hat_z_minimum_degree]
    congr 1
    simp [sv]
  · simp only [letFS, if_true]
    rw [shape_mul, aa_shape hF hL hh _ _ _ g hg, Formalism.FourierDecayAlt.P.hat_z_minimum_degree]
    congr 1
    simp [sv]

def wordFS (k j ρ : ℕ) : (w : List C.Letter) → Wd.Ix (Fin w.length) → FS k (j + ρ)
  | [], _ => [((C 1, 0, 0), [])]
  | l :: w, e => letFS k j ρ l (e 0) (wordFS k j ρ w fun a => e a.succ)

theorem bd_wordFS : ∀ (w : List C.Letter) (e : Wd.Ix (Fin w.length)),
    Bd k j ρ (w.length * (j + j * j)) (w.length * j) (wordFS k j ρ w e)
  | [], _ => by
    intro x hx
    simp only [wordFS, List.mem_singleton] at hx
    subst hx
    simp
  | l :: w, e => by
    have := bd_letFS (k := k) (j := j) (ρ := ρ) l (e 0) (bd_wordFS w fun a => e a.succ)
    refine this.mono (le_of_eq ?_) (le_of_eq ?_)
    · simp only [List.length_cons]; ring
    · simp only [List.length_cons]; ring

theorem word_shape (hj1 : 1 ≤ j) (z z' : Fin (2 * (j + ρ) + k + 1) → ℂ) (hj : j ≤ j + ρ)
    {F : Mat k (j + ρ) → E} (hF : CkOn ⊤ (GV k (j + ρ)) F) :
    ∀ (w : List C.Letter) (e : Wd.Ix (Fin w.length)),
      ∀ g ∈ Sj k j ρ, D.uwG k (j + ρ) z z' F j hj w e g = shape k j ρ F (wordFS k j ρ w e) g
  | [], _ => by
    intro g _
    simp [D.uwG, wordFS, shape, sv, Rw]
  | l :: w, e => by
    intro g hg
    show D.vLet k (j + ρ) z z' j hj l (e 0) (D.uwG k (j + ρ) z z' F j hj w fun a => e a.succ) g = _
    exact vlet_shape hj1 z z' hj hF (bd_wordFS w fun a => e a.succ)
      (word_shape hj1 z z' hj hF w fun a => e a.succ) l (e 0) g hg

end shapes

theorem lettersDD : LettersDD := by
  intro k j ρ Wp Wq _ _ _ _ _ z z' hj w a hj1
  refine ⟨(wordFS k j ρ w a).map (mkTerm (Wp := Wp) (Wq := Wq) k j ρ), ?_, ?_⟩
  · apply inDD_mk
    exact (bd_wordFS w a).mono (le_of_eq (by ring)) le_rfl
  · intro F hF g hg hD
    rw [opApply_mk _ (fun e he => ((bd_wordFS w a) e he).2.2) F g]
    exact word_shape hj1 z z' hj hF w a g ⟨hg, hD⟩

end Formalism.FourierDecayAlt.P.JCTx6.Let

noncomputable section

open Matrix MeasureTheory Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.JCTx6.Int

open Formalism.FourierDecayAlt.P.Dx2.SL

theorem orbit_slice_integrable : OrbitSliceIntegrable := by
  intro k ph n ρ σ d t z z' E _ _ F γ hg
  set RR := U.RC k (ph + (n + 1)) ρ × U.RC k (ph + (n + 1)) ρ
  have sR := sigma_RC k (ph + (n + 1)) ρ
  set μR : Measure RR := (U.muRC k (ph + (n + 1)) ρ).prod (U.muRC k (ph + (n + 1)) ρ)
  have sX : SFinite (U.muXiH (ph + (n + 1)) 0 (sigP σ)) := by
    have hT := probT (ph + (n + 1))
    have b1 : SigmaFinite (volume : Measure (U.LW (sigP (n := n) σ) → ℂ)) := inferInstance
    have b2 : SigmaFinite (volume : Measure (G.UT (ph + (n + 1)) → ℂ)) := inferInstance
    have b3 : SigmaFinite (volume : Measure ((U.LW (sigP (n := n) σ) → ℂ) × (G.UT (ph + (n + 1)) → ℂ))) := by
      rw [Measure.volume_eq_prod]; infer_instance
    unfold U.muXiH
    rw [Measure.volume_eq_prod]; infer_instance
  let Φ : U.Xi k (ph + (n + 1)) 0 ρ (sigP σ) ≃ᵐ RR × (U.XiH ph (n + 1) σ × (G.UT (n + 1) → ℂ)) :=
    MeasurableEquiv.prodCongr (MeasurableEquiv.refl RR) (xiE σ)
  have hΦ : MeasurePreserving Φ (U.muXi k (ph + (n + 1)) 0 ρ (sigP σ)) (μR.prod (volume.prod volume)) :=
    (MeasurePreserving.id μR).prod (xiE_mp σ)
  have hfg : (fun ξ : U.Xi k (ph + (n + 1)) 0 ρ (sigP σ) =>
      U.psiStar (p := ph + (n + 1)) (s := 0) k ρ (sigP σ) z z' ξ •
        F (U.gaXi (p := ph + (n + 1)) (s := 0) k ρ (sigP σ) (dP d t) ξ (fun a => a.elim0) γ)) =
      gInt k ph n ρ σ d t z z' F γ ∘ Φ := by
    funext ξ
    obtain ⟨x, ⟨a0, b0⟩, v, u⟩ := ξ
    rw [Function.comp_apply]
    rw [show Φ (x, ((a0, b0), v, u)) = (x, xiE σ ((a0, b0), v, u)) from rfl, xiE_apply]
    simp only [gInt, U.psiStar, U.gaXi, U.ZjH, zj_zero, zj_split, Equiv.apply_symm_apply]
    rw [psiH_split, smul_smul]
    congr 1
    have e1 : Formalism.QuantumDeterminants.psi k (ph + (n + 1) + 0 + ρ) z cStd (U.Rn k (ph + (n + 1) + 0) ρ x.1) =
        Formalism.QuantumDeterminants.psi k (ph + (n + 1) + ρ) z cStd (U.Rn k (ph + (n + 1)) ρ x.1) := rfl
    have e2 : Formalism.QuantumDeterminants.psi k (ph + (n + 1) + 0 + ρ) z' cStd (U.Rn k (ph + (n + 1) + 0) ρ x.2) =
        Formalism.QuantumDeterminants.psi k (ph + (n + 1) + ρ) z' cStd (U.Rn k (ph + (n + 1)) ρ x.2) := rfl
    rw [e1, e2]
    ring
  rw [hfg]
  exact (hΦ.integrable_comp_emb Φ.measurableEmbedding).mpr hg

end Formalism.FourierDecayAlt.P.JCTx6.Int

noncomputable section

open Matrix MeasureTheory Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.JCTx6.Int

open Formalism.FourierDecayAlt.P.Dx2.SL

def Zu (n : ℕ) (t : ℂ) (u : G.UT (n + 1) → ℂ) : G.Mat (n + 1) :=
  Matrix.of.symm (t • G.wMat (n + 1) * G.upper u)

lemma Zu_apply (n : ℕ) (t : ℂ) (u : G.UT (n + 1) → ℂ) (a b : Fin (n + 1)) :
    Zu n t u a b = t * G.upper u a.rev b := by
  simp only [Zu, Matrix.smul_mul]
  simp [Matrix.mul_apply, G.wMat]

lemma Zu_entry (n : ℕ) (t : ℂ) (u : G.UT (n + 1) → ℂ) (q : G.UT (n + 1)) :
    Zu n t u q.1.1.rev q.1.2 = t * u q := by
  rw [Zu_apply, Fin.rev_rev]
  simp [G.upper, G.strictUpper, Matrix.one_apply, ne_of_lt q.2, q.2]

lemma norm_u_le (n : ℕ) {t : ℂ} (ht : t ≠ 0) (u : G.UT (n + 1) → ℂ) :
    ‖u‖ ≤ ‖t‖⁻¹ * ‖Zu n t u‖ := by
  have ht' : 0 < ‖t‖ := norm_pos_iff.mpr ht
  refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun q => ?_
  have h1 : ‖Zu n t u q.1.1.rev q.1.2‖ ≤ ‖Zu n t u‖ :=
    (norm_le_pi_norm (Zu n t u q.1.1.rev) q.1.2).trans (norm_le_pi_norm (Zu n t u) q.1.1.rev)
  rw [Zu_entry, norm_mul] at h1
  rw [le_inv_mul_iff₀ ht']
  exact h1

lemma one_add_u_le (n : ℕ) {t : ℂ} (ht : t ≠ 0) (u : G.UT (n + 1) → ℂ) :
    1 + ‖u‖ ≤ max 1 ‖t‖⁻¹ * (1 + ‖Zu n t u‖) := by
  have h := norm_u_le n ht u
  have hM2 : ‖t‖⁻¹ ≤ max 1 ‖t‖⁻¹ := le_max_right _ _
  have hM1 : 1 ≤ max 1 ‖t‖⁻¹ := le_max_left _ _
  have hZ : 0 ≤ ‖Zu n t u‖ := norm_nonneg _
  nlinarith [mul_le_mul_of_nonneg_right hM2 hZ]

lemma det_wMat_ne (m : ℕ) : (G.wMat m).det ≠ 0 := by
  intro h
  have hw : G.wMat m * G.wMat m = 1 := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp only [G.wMat, Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply_eq]
      rw [Finset.sum_eq_single i.rev]
      · simp
      · intro b _ hb
        simp [hb]
      · simp
    · simp only [G.wMat, Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply_ne hij]
      apply Finset.sum_eq_zero
      intro x _
      by_cases h1 : x = i.rev
      · have h2 : ¬ j = x.rev := by rw [h1, Fin.rev_rev]; exact Ne.symm hij
        rw [if_neg h2, mul_zero]
      · rw [if_neg h1, zero_mul]
  have := congrArg Matrix.det hw
  rw [Matrix.det_mul, h, Matrix.det_one] at this
  simp at this

private theorem det_upper_eq_one' {d : ℕ} (u : G.UT d → ℂ) : (G.upper u).det = 1 := by
  rw [Matrix.det_of_upperTriangular]
  · apply Finset.prod_eq_one
    intro i _
    simp [G.upper, G.strictUpper]
  · intro i j hij
    have hij' : j < i := hij
    have hne : i ≠ j := (ne_of_lt hij').symm
    simp [G.upper, G.strictUpper, Matrix.one_apply, hne, not_lt.mpr hij'.le]

lemma detM_Zu (n : ℕ) {t : ℂ} (ht : t ≠ 0) (u : G.UT (n + 1) → ℂ) : G.detM (Zu n t u) ≠ 0 := by
  show Matrix.det (t • G.wMat (n + 1) * G.upper u) ≠ 0
  rw [Matrix.det_mul, Matrix.det_smul, Fintype.card_fin, det_upper_eq_one', mul_one]
  exact mul_ne_zero (pow_ne_zero _ ht) (det_wMat_ne _)

end Formalism.FourierDecayAlt.P.JCTx6.Int

noncomputable section

open Matrix MeasureTheory Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.JCTx6.Int

open Formalism.FourierDecayAlt.P.Dx2.SL

lemma cont_Zu (n : ℕ) (t : ℂ) : Continuous (Zu n t) := by
  refine continuous_pi fun a => continuous_pi fun b => ?_
  simp only [Zu_apply, G.upper, G.strictUpper, Matrix.add_apply, Matrix.of_apply]
  split_ifs <;> fun_prop

lemma continuous_slice_integrand {ph n : ℕ} (σ : Equiv.Perm (Fin ph)) (d : Fin ph → ℂ) (t : ℂ) :
    Continuous fun y : U.XiH ph (n + 1) σ × (G.UT (n + 1) → ℂ) => U.ZjH σ d y.1 (Zu n t y.2) := by
  have e : (fun y : U.XiH ph (n + 1) σ × (G.UT (n + 1) → ℂ) => U.ZjH σ d y.1 (Zu n t y.2)) =
      fun y => U.Zj y.1.1.1 y.1.1.2 (U.headH σ d y.1.2.1 y.1.2.2) (t • G.wMat (n + 1) * G.upper y.2) := by
    funext y
    simp only [U.ZjH, Zu, Equiv.apply_symm_apply]
  rw [e]
  unfold U.Zj U.headH U.blk2 G.upper
  fun_prop

lemma cont_gaXi2 {k ph n ρ : ℕ} (σ : Equiv.Perm (Fin ph)) (d : Fin ph → ℂ) (hd : ∀ i, d i ≠ 0) {t : ℂ}
    (ht : t ≠ 0) (γ : B.Mat k ρ) :
    Continuous fun y : (U.RC k (ph + (n + 1)) ρ × U.RC k (ph + (n + 1)) ρ) × (U.XiH ph (n + 1) σ × (G.UT (n + 1) → ℂ)) =>
      U.gaXi k ρ σ d (y.1, y.2.1) (Zu n t y.2.2) γ := by
  have hR := Formalism.FourierDecayAlt.P.radical_parametrisation
  have h1 : Continuous fun y : (U.RC k (ph + (n + 1)) ρ × U.RC k (ph + (n + 1)) ρ) ×
      (U.XiH ph (n + 1) σ × (G.UT (n + 1) → ℂ)) => (U.Rn k (ph + (n + 1)) ρ y.1.1)⁻¹ :=
    Formalism.FourierDecayAlt.P.Ux10.cont_inv ((Formalism.FourierDecayAlt.P.Ux10.cont_Rn k (ph + (n + 1)) ρ).comp (continuous_fst.comp continuous_fst))
      fun y => (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_unit (Formalism.FourierDecayAlt.P.Ux10.Rn_mem hR k (ph + (n + 1)) ρ y.1.1)).ne_zero
  have h3 : Continuous fun y : (U.RC k (ph + (n + 1)) ρ × U.RC k (ph + (n + 1)) ρ) ×
      (U.XiH ph (n + 1) σ × (G.UT (n + 1) → ℂ)) => U.ZjH σ d y.2.1 (Zu n t y.2.2) :=
    (continuous_slice_integrand σ d t).comp continuous_snd
  have h2 : Continuous fun y : (U.RC k (ph + (n + 1)) ρ × U.RC k (ph + (n + 1)) ρ) ×
      (U.XiH ph (n + 1) σ × (G.UT (n + 1) → ℂ)) => (U.ZjH σ d y.2.1 (Zu n t y.2.2))ᴴ⁻¹ := by
    refine Formalism.FourierDecayAlt.P.Ux10.cont_inv h3.matrix_conjTranspose fun y => ?_
    rw [Matrix.det_conjTranspose, Formalism.FourierDecayAlt.P.Ux10.detZj]
    exact star_ne_zero.2 (mul_ne_zero (Formalism.FourierDecayAlt.P.Ux10.det_hMat_ne σ d hd) (detM_Zu n ht _))
  have h4 : Continuous fun y : (U.RC k (ph + (n + 1)) ρ × U.RC k (ph + (n + 1)) ρ) ×
      (U.XiH ph (n + 1) σ × (G.UT (n + 1) → ℂ)) => U.Rn k (ph + (n + 1)) ρ y.1.2 :=
    (Formalism.FourierDecayAlt.P.Ux10.cont_Rn k (ph + (n + 1)) ρ).comp (continuous_snd.comp continuous_fst)
  unfold U.gaXi U.mMap U.blk3
  fun_prop

lemma cont_psiU (n : ℕ) : Continuous fun u : G.UT (n + 1) → ℂ => G.psi U.betaU (G.superSum (G.upper u)) := by
  have hU : Continuous fun u : G.UT (n + 1) → ℂ => G.upper u := by
    refine continuous_pi fun a => continuous_pi fun b => ?_
    simp only [G.upper, G.strictUpper, Matrix.add_apply, Matrix.of_apply]
    split_ifs <;> fun_prop
  have hS : Continuous fun M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ => G.superSum M := by
    unfold G.superSum
    fun_prop
  have hSU : Continuous fun u : G.UT (n + 1) → ℂ => G.superSum (G.upper u) := hS.comp hU
  unfold G.psi
  first
    | fun_prop
    | exact Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp
        (Complex.continuous_re.comp (continuous_const.mul hSU))))

lemma norm_psiU (β w : ℂ) : ‖G.psi β w‖ = 1 := by
  first
    | simp [G.psi, Complex.norm_exp]
    | (rw [G.psi, mul_comm]; exact Complex.norm_exp_ofReal_mul_I _)

end Formalism.FourierDecayAlt.P.JCTx6.Int

noncomputable section

open Matrix MeasureTheory Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.JCTx6.Int

open Formalism.FourierDecayAlt.P.Dx2.SL

lemma rpow_Z_le {a c x y : ℝ} (ha : 0 ≤ a) (hc : 0 < c) (hx : 0 < x) (hy : 0 < y) (hxy : x ≤ c * y) :
    y ^ (-a) ≤ c ^ a * x ^ (-a) := by
  rw [Real.rpow_neg hy.le, Real.rpow_neg hx.le]
  have hxa : 0 < x ^ a := Real.rpow_pos_of_pos hx a
  have hya : 0 < y ^ a := Real.rpow_pos_of_pos hy a
  have h1 : x ^ a ≤ c ^ a * y ^ a := by
    rw [← Real.mul_rpow hc.le hy.le]
    exact Real.rpow_le_rpow hx.le hxy ha
  have key : (y ^ a)⁻¹ * x ^ a ≤ c ^ a := by
    rw [inv_mul_le_iff₀ hya]
    linarith [mul_comm (c ^ a) (y ^ a)]
  calc (y ^ a)⁻¹ = (y ^ a)⁻¹ * x ^ a * (x ^ a)⁻¹ := by rw [mul_assoc, mul_inv_cancel₀ hxa.ne', mul_one]
    _ ≤ c ^ a * (x ^ a)⁻¹ := by gcongr

lemma two_mul_card_UT_succ (n : ℕ) : 2 * Fintype.card (G.UT (n + 1)) = (n + 1) * n := by
  have := card_UT (n + 1)
  simpa using this

theorem intG : IntG := by
  intro k ph n ρ σ d t hd ht K hK hK0 Q A₁ hA z z' E _ _ F₁ B₁ hStar γ hγ
  set R : ℝ := ((ph + (n + 1) + ρ : ℕ) : ℝ) with hR
  set a : ℝ := A₁ / (8 * (2 * R + 1)) with ha_def
  have hden : 0 < 8 * (2 * R + 1) := by positivity
  have hR1 : (1 : ℝ) ≤ R := by rw [hR]; exact_mod_cast (by omega : 1 ≤ ph + (n + 1) + ρ)
  have hnd : R ≤ ((2 * (ph + (n + 1) + ρ) + k + 1 : ℕ) : ℝ) := by
    rw [hR]; exact_mod_cast (by omega : ph + (n + 1) + ρ ≤ 2 * (ph + (n + 1) + ρ) + k + 1)
  have ha : 2 * R * ((2 * (ph + (n + 1) + ρ) + k + 1 : ℕ) : ℝ) < a := hA
  have ha0 : 0 < a := lt_of_le_of_lt (by positivity) ha
  have hA0 : 0 ≤ A₁ := by
    have e : A₁ = a * (8 * (2 * R + 1)) := by rw [ha_def]; field_simp
    rw [e]; positivity
  obtain ⟨C₂, hC₂⟩ := Formalism.FourierDecayAlt.P.norm_decay_in_coordinates k ph (n + 1) ρ σ d hd (by omega) K hK hK0 A₁ hA0
  have hI1 : Integrable (fun ξ : U.Xi k ph (n + 1) ρ σ => U.wt ξ ^ (-a)) (U.muXi k ph (n + 1) ρ σ) :=
    Formalism.FourierDecayAlt.P.weight_integrability k ph (n + 1) ρ σ a (by omega) ha
  have hfr : ((Module.finrank ℝ (G.UT (n + 1) → ℂ) : ℕ) : ℝ) < a := by
    have e1 : Module.finrank ℝ (G.UT (n + 1) → ℂ) = Fintype.card (G.UT (n + 1)) * 2 := by
      rw [Module.finrank_pi_fintype]
      simp [Complex.finrank_real_complex]
    have e2 := two_mul_card_UT_succ n
    have hnR : ((n + 1 : ℕ) : ℝ) ≤ R := by rw [hR]; exact_mod_cast (by omega : n + 1 ≤ ph + (n + 1) + ρ)
    have e3 : ((Module.finrank ℝ (G.UT (n + 1) → ℂ) : ℕ) : ℝ) = ((n + 1 : ℕ) : ℝ) * (n : ℝ) := by
      rw [e1]; exact_mod_cast (by rw [mul_comm]; exact e2)
    rw [e3]
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    have hn1 : (n : ℝ) ≤ R := by
      have : (n : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by push_cast; linarith
      linarith
    nlinarith
  have hI2 : Integrable (fun u : G.UT (n + 1) → ℂ => (1 + ‖u‖) ^ (-a)) volume := integrable_one_add_norm hfr
  have sR := sigma_RC k (ph + (n + 1)) ρ
  have hxi : SFinite (volume : Measure (U.XiH ph (n + 1) σ)) := by
    have c1 : SigmaFinite (volume : Measure (Fin (n + 1) → Fin ph → ℂ)) := inferInstance
    have c2 : SigmaFinite (volume : Measure (Fin ph → Fin (n + 1) → ℂ)) := inferInstance
    have c3 : SigmaFinite (volume : Measure (U.LW σ → ℂ)) := inferInstance
    have c4 : SigmaFinite (volume : Measure (G.UT ph → ℂ)) := inferInstance
    have c5 : SigmaFinite (volume : Measure ((Fin (n + 1) → Fin ph → ℂ) × (Fin ph → Fin (n + 1) → ℂ))) := by
      rw [Measure.volume_eq_prod]; infer_instance
    have c6 : SigmaFinite (volume : Measure ((U.LW σ → ℂ) × (G.UT ph → ℂ))) := by
      rw [Measure.volume_eq_prod]; infer_instance
    rw [Measure.volume_eq_prod]; infer_instance
  set μR := (U.muRC k (ph + (n + 1)) ρ).prod (U.muRC k (ph + (n + 1)) ρ) with hμR
  have hP : Integrable (fun p : U.Xi k ph (n + 1) ρ σ × (G.UT (n + 1) → ℂ) => U.wt p.1 ^ (-a) * (1 + ‖p.2‖) ^ (-a))
      ((U.muXi k ph (n + 1) ρ σ).prod volume) := hI1.mul_prod hI2
  have hAs : MeasurePreserving (MeasurableEquiv.prodAssoc.symm :
      (U.RC k (ph + (n + 1)) ρ × U.RC k (ph + (n + 1)) ρ) × (U.XiH ph (n + 1) σ × (G.UT (n + 1) → ℂ)) ≃ᵐ _)
      (μR.prod (volume.prod volume)) ((μR.prod volume).prod volume) :=
    (assoc_mp μR volume volume).symm _
  have hD : Integrable (fun y : (U.RC k (ph + (n + 1)) ρ × U.RC k (ph + (n + 1)) ρ) ×
      (U.XiH ph (n + 1) σ × (G.UT (n + 1) → ℂ)) => U.wt (y.1, y.2.1) ^ (-a) * (1 + ‖y.2.2‖) ^ (-a))
      (muG k ph n ρ σ) :=
    (hAs.integrable_comp_emb MeasurableEquiv.prodAssoc.symm.measurableEmbedding).mpr hP
  have hB₁ : 0 ≤ B₁ := by
    have := hStar.2.2 [] [] (by simp [U.unitP]) (by simp [U.unitP]) (by simp) 1 Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_one
    exact le_trans (mul_nonneg (Real.rpow_nonneg (Real.sqrt_nonneg _) _) (norm_nonneg _)) this
  have hγ1 : 1 ≤ B.gN γ := Formalism.FourierDecayAlt.P.BetaSesquilinearity.gN_ge_one hγ
  set c : ℝ := max 1 ‖t‖⁻¹ with hc
  have hc0 : 0 < c := lt_of_lt_of_le one_pos (le_max_left _ _)
  set Cst : ℝ := B₁ * |C₂| * (c ^ a * B.gN γ ^ (-a)) with hCst
  have hbound : ∀ y : (U.RC k (ph + (n + 1)) ρ × U.RC k (ph + (n + 1)) ρ) × (U.XiH ph (n + 1) σ × (G.UT (n + 1) → ℂ)),
      ‖gInt k ph n ρ σ d t z z' F₁ γ y‖ ≤ Cst * (U.wt (y.1, y.2.1) ^ (-a) * (1 + ‖y.2.2‖) ^ (-a)) := by
    intro y
    have hZ : G.detM (Zu n t y.2.2) ≠ 0 := detM_Zu n ht _
    have hg := Formalism.FourierDecayAlt.P.Ux10.gaXi_mem Formalism.FourierDecayAlt.P.slice_membership Formalism.FourierDecayAlt.P.radical_parametrisation σ d hd
      (y.1, y.2.1) (Zu n t y.2.2) hZ hγ
    have e : ‖gInt k ph n ρ σ d t z z' F₁ γ y‖ = ‖F₁ (U.gaXi k ρ σ d (y.1, y.2.1) (Zu n t y.2.2) γ)‖ := by
      simp only [gInt, norm_smul, norm_psiU, Formalism.FourierDecayAlt.P.Ux10.norm_psiStar, one_mul]
      rfl
    rw [e]
    have hw1 : 1 ≤ U.wt ((y.1, y.2.1) : U.Xi k ph (n + 1) ρ σ) := Formalism.FourierDecayAlt.P.Ux10.one_le_wt _
    have hu1 : 1 ≤ 1 + ‖y.2.2‖ := by linarith [norm_nonneg y.2.2]
    have hRHS : 0 ≤ Cst * (U.wt (y.1, y.2.1) ^ (-a) * (1 + ‖y.2.2‖) ^ (-a)) := by
      rw [hCst]; positivity
    by_cases h0 : F₁ (U.gaXi k ρ σ d (y.1, y.2.1) (Zu n t y.2.2) γ) = 0
    · rw [h0, norm_zero]; exact hRHS
    · have hK' := hStar.2.1 _ hg h0
      have hs := hC₂ (y.1, y.2.1) (Zu n t y.2.2) γ hγ hK'
      have hst := hStar.2.2 [] [] (by simp [U.unitP]) (by simp [U.unitP]) (by simp) _ hg
      have hg1 : 1 ≤ B.gN (U.gaXi k ρ σ d (y.1, y.2.1) (Zu n t y.2.2) γ) := Formalism.FourierDecayAlt.P.BetaSesquilinearity.gN_ge_one hg
      set gg := B.gN (U.gaXi k ρ σ d (y.1, y.2.1) (Zu n t y.2.2) γ) with hgg
      set Fv := ‖F₁ (U.gaXi k ρ σ d (y.1, y.2.1) (Zu n t y.2.2) γ)‖ with hFv
      have hst' : gg ^ A₁ * Fv ≤ B₁ := hst
      have hF : Fv ≤ B₁ * gg ^ (-A₁) := by
        have hpos : 0 < gg ^ A₁ := Real.rpow_pos_of_pos (by linarith) _
        have e2 : gg ^ (-A₁) = (gg ^ A₁)⁻¹ := Real.rpow_neg (by linarith) _
        rw [e2, ← div_eq_mul_inv, le_div_iff₀ hpos]
        linarith [mul_comm (gg ^ A₁) Fv]
      have hZb := one_add_u_le n ht y.2.2
      have hZle : (1 + ‖Zu n t y.2.2‖) ^ (-a) ≤ c ^ a * (1 + ‖y.2.2‖) ^ (-a) :=
        rpow_Z_le ha0.le hc0 (by linarith) (by linarith [norm_nonneg (Zu n t y.2.2)]) hZb
      have hsplit : (U.wt ((y.1, y.2.1) : U.Xi k ph (n + 1) ρ σ) * (1 + ‖Zu n t y.2.2‖) * B.gN γ) ^ (-a) =
          U.wt ((y.1, y.2.1) : U.Xi k ph (n + 1) ρ σ) ^ (-a) * (1 + ‖Zu n t y.2.2‖) ^ (-a) * B.gN γ ^ (-a) := by
        rw [Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow (by positivity) (by positivity)]
      have hs' : gg ^ (-A₁) ≤ |C₂| * (U.wt ((y.1, y.2.1) : U.Xi k ph (n + 1) ρ σ) ^ (-a) *
          (1 + ‖Zu n t y.2.2‖) ^ (-a) * B.gN γ ^ (-a)) := by
        rw [← hsplit]
        exact hs.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (Real.rpow_nonneg (by positivity) _))
      have hw0 : 0 ≤ U.wt ((y.1, y.2.1) : U.Xi k ph (n + 1) ρ σ) ^ (-a) := Real.rpow_nonneg (by linarith) _
      have hγ0 : 0 ≤ B.gN γ ^ (-a) := Real.rpow_nonneg (by linarith) _
      calc Fv ≤ B₁ * gg ^ (-A₁) := hF
        _ ≤ B₁ * (|C₂| * (U.wt ((y.1, y.2.1) : U.Xi k ph (n + 1) ρ σ) ^ (-a) *
            (1 + ‖Zu n t y.2.2‖) ^ (-a) * B.gN γ ^ (-a))) := mul_le_mul_of_nonneg_left hs' hB₁
        _ ≤ B₁ * (|C₂| * (U.wt ((y.1, y.2.1) : U.Xi k ph (n + 1) ρ σ) ^ (-a) *
            (c ^ a * (1 + ‖y.2.2‖) ^ (-a)) * B.gN γ ^ (-a))) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)) hB₁
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hZle hw0) hγ0
        _ = Cst * (U.wt (y.1, y.2.1) ^ (-a) * (1 + ‖y.2.2‖) ^ (-a)) := by rw [hCst]; ring
  have : BorelSpace (U.XiH ph (n + 1) σ) := Prod.borelSpace
  have : BorelSpace (U.RC k (ph + (n + 1)) ρ) := Prod.borelSpace
  have : BorelSpace (U.RC k (ph + (n + 1)) ρ × U.RC k (ph + (n + 1)) ρ) := Prod.borelSpace
  have : BorelSpace (U.XiH ph (n + 1) σ × (G.UT (n + 1) → ℂ)) := Prod.borelSpace
  have : BorelSpace ((U.RC k (ph + (n + 1)) ρ × U.RC k (ph + (n + 1)) ρ) × (U.XiH ph (n + 1) σ × (G.UT (n + 1) → ℂ))) :=
    Prod.borelSpace
  have hcont1 : ContinuousOn F₁ (B.GV k (ph + (n + 1) + ρ)) :=
    Formalism.FourierDecayAlt.P.BetaSesquilinearity.CkOn_cont subset_rfl (Formalism.FourierDecayAlt.P.BetaSesquilinearity.sCkOn_mono (by simp) hStar.1)
  have hcF : Continuous fun y : (U.RC k (ph + (n + 1)) ρ × U.RC k (ph + (n + 1)) ρ) × (U.XiH ph (n + 1) σ × (G.UT (n + 1) → ℂ)) =>
      F₁ (U.gaXi k ρ σ d (y.1, y.2.1) (Zu n t y.2.2) γ) :=
    hcont1.comp_continuous (cont_gaXi2 σ d hd ht γ) fun y =>
      Formalism.FourierDecayAlt.P.Ux10.gaXi_mem Formalism.FourierDecayAlt.P.slice_membership Formalism.FourierDecayAlt.P.radical_parametrisation σ d hd
        (y.1, y.2.1) (Zu n t y.2.2) (detM_Zu n ht _) hγ
  have hcg : Continuous (gInt k ph n ρ σ d t z z' F₁ γ) := by
    have h1 := (cont_psiU n).comp (continuous_snd.comp continuous_snd :
      Continuous fun y : (U.RC k (ph + (n + 1)) ρ × U.RC k (ph + (n + 1)) ρ) × (U.XiH ph (n + 1) σ × (G.UT (n + 1) → ℂ)) => y.2.2)
    have h2 := (Formalism.FourierDecayAlt.P.Ux10.cont_psiStar k ρ σ z z').comp (continuous_fst.prodMk (continuous_fst.comp continuous_snd) :
      Continuous fun y : (U.RC k (ph + (n + 1)) ρ × U.RC k (ph + (n + 1)) ρ) × (U.XiH ph (n + 1) σ × (G.UT (n + 1) → ℂ)) =>
        ((y.1, y.2.1) : U.Xi k ph (n + 1) ρ σ))
    exact h1.smul (h2.smul hcF)
  exact (hD.const_mul Cst).mono' hcg.aestronglyMeasurable (Filter.Eventually.of_forall hbound)

end Formalism.FourierDecayAlt.P.JCTx6.Int

open Matrix MeasureTheory Filter Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P.JCTx6.Pos

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section loc

variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem rdV_congr_open {O : Set (Mat k r)} (hO : IsOpen O) {f₁ f₂ : Mat k r → E}
    (h : ∀ x ∈ O, f₁ x = f₂ x) (X : Mat k r) : ∀ g ∈ O, RdV X f₁ g = RdV X f₂ g := by
  intro g hg
  unfold RdV
  apply Filter.EventuallyEq.deriv_eq
  have hc : Continuous (fun t : ℝ => g * NormedSpace.exp ((t : ℂ) • X)) := (B5.curve_contDiff g X).continuous
  have h0 : (fun t : ℝ => g * NormedSpace.exp ((t : ℂ) • X)) 0 ∈ O := by
    simp only; rw [B5.curve_zero]; exact hg
  have hev : ∀ᶠ t : ℝ in 𝓝 (0 : ℝ), g * NormedSpace.exp ((t : ℂ) • X) ∈ O :=
    hc.continuousAt.preimage_mem_nhds (hO.mem_nhds h0)
  filter_upwards [hev] with t ht
  exact h _ ht

theorem rw_congr_open {O : Set (Mat k r)} (hO : IsOpen O) {f₁ f₂ : Mat k r → E}
    (h : ∀ x ∈ O, f₁ x = f₂ x) : ∀ (v : List (Mat k r)), ∀ g ∈ O, Rw v f₁ g = Rw v f₂ g
  | [] => h
  | X :: v => by
    intro g hg
    show RdV X (Rw v f₁) g = RdV X (Rw v f₂) g
    exact rdV_congr_open hO (rw_congr_open hO h v) X g hg

theorem opApply_congr_open {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
    (Θ : DiffOp k r Wp Wq) {O : Set (Mat k r)} (hO : IsOpen O) {f₁ f₂ : Mat k r → (Wq →L[ℂ] Wp)}
    (h : ∀ x ∈ O, f₁ x = f₂ x) : ∀ g ∈ O, opApply Θ f₁ g = opApply Θ f₂ g := by
  intro g hg
  simp only [opApply]
  congr 1
  apply List.map_congr_left
  intro T _
  rw [rw_congr_open hO h T.word g hg]

end loc

section cle

variable {F₀ G₀ : Type*} [NormedAddCommGroup F₀] [NormedSpace ℝ F₀] [NormedAddCommGroup G₀] [NormedSpace ℝ G₀]

theorem deriv_cle_comp (L : F₀ →L[ℝ] G₀) (L' : G₀ →L[ℝ] F₀) (hL : ∀ y, L' (L y) = y) (f : ℝ → F₀) (x : ℝ) :
    deriv (fun t => L (f t)) x = L (deriv f x) := by
  by_cases hf : DifferentiableAt ℝ f x
  · exact (L.hasFDerivAt.comp_hasDerivAt x hf.hasDerivAt).deriv
  · have hLf : ¬ DifferentiableAt ℝ (fun t => L (f t)) x := by
      intro hd
      apply hf
      have : (fun t => L' (L (f t))) = f := funext fun t => hL (f t)
      rw [← this]
      exact L'.differentiableAt.comp x hd
    rw [deriv_zero_of_not_differentiableAt hf, deriv_zero_of_not_differentiableAt hLf, map_zero]

variable {k r : ℕ} {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup E'] [NormedSpace ℂ E']

theorem rdV_cle (e : E ≃L[ℂ] E') (X : Mat k r) (f : Mat k r → E) :
    RdV X (fun g => e (f g)) = fun g => e (RdV X f g) := by
  funext g
  exact deriv_cle_comp ((e : E →L[ℂ] E').restrictScalars ℝ) ((e.symm : E' →L[ℂ] E).restrictScalars ℝ)
    (fun y => e.symm_apply_apply y) _ 0

theorem ldV_cle (e : E ≃L[ℂ] E') (X : Mat k r) (f : Mat k r → E) :
    LdV X (fun g => e (f g)) = fun g => e (LdV X f g) := by
  funext g
  first
    | exact deriv_cle_comp ((e : E →L[ℂ] E').restrictScalars ℝ) ((e.symm : E' →L[ℂ] E).restrictScalars ℝ)
        (fun y => e.symm_apply_apply y) (fun t : ℝ => f (NormedSpace.exp (-((t : ℂ) • X)) * g)) 0
    | exact deriv_cle_comp ((e : E →L[ℂ] E').restrictScalars ℝ) ((e.symm : E' →L[ℂ] E).restrictScalars ℝ)
        (fun y => e.symm_apply_apply y) _ 0

theorem rw_cle (e : E ≃L[ℂ] E') : ∀ (v : List (Mat k r)) (f : Mat k r → E),
    Rw v (fun g => e (f g)) = fun g => e (Rw v f g)
  | [], _ => rfl
  | X :: v, f => by
    show RdV X (Rw v fun g => e (f g)) = fun g => e (RdV X (Rw v f) g)
    rw [rw_cle e v f, rdV_cle e X]

theorem dLR_cle (e : E ≃L[ℂ] E') (v : List (Mat k r)) : ∀ (u : List (Mat k r)) (f : Mat k r → E),
    dLR u v (fun g => e (f g)) = fun g => e (dLR u v f g)
  | [], f => rw_cle e v f
  | X :: u, f => by
    show LdV X (dLR u v fun g => e (f g)) = fun g => e (LdV X (dLR u v f) g)
    rw [dLR_cle e v u f, ldV_cle e X]

theorem ckOn_cle (e : E ≃L[ℂ] E') {m : ℕ∞} {UU : Set (Mat k r)} {f : Mat k r → E} (hf : CkOn m UU f) :
    CkOn m UU (fun g => e (f g)) := by
  intro g₀ hg₀
  obtain ⟨U, f', hU, hgU, hcd, heq⟩ := hf g₀ hg₀
  refine ⟨U, fun g => e (f' g), hU, hgU, ?_, fun g hg hgv => congrArg (fun x => e x) (heq g hg hgv)⟩
  exact ((e : E →L[ℂ] E').restrictScalars ℝ).contDiff.comp_contDiffOn hcd

theorem ccle_unit {A c : ℝ} {m : ℕ} {F : Mat k r → (Unit → E)} (hF : CCle A m F c) :
    CCle A m (fun g => F g ()) c := by
  let e : (Unit → E) ≃L[ℂ] E := ContinuousLinearEquiv.funUnique Unit ℂ E
  have he : ∀ y : Unit → E, e y = y () := fun _ => rfl
  refine ⟨?_, fun u v hu hv hl g hg => ?_⟩
  · have := ckOn_cle e hF.1
    simpa [he] using this
  · have h1 := dLR_cle e v u F
    have h2 : dLR u v (fun g => F g ()) g = e (dLR u v F g) := by
      have := congrFun h1 g
      simpa [he] using this
    rw [h2, he]
    refine le_trans ?_ (hF.2 u v hu hv hl g hg)
    have hgN : 0 ≤ gN g ^ A := Real.rpow_nonneg (Real.sqrt_nonneg _) A
    exact mul_le_mul_of_nonneg_left (norm_le_pi_norm (dLR u v F g) ()) hgN

end cle

end Formalism.FourierDecayAlt.P.JCTx6.Pos

open Matrix MeasureTheory Filter Topology Metric

noncomputable section

namespace Formalism.FourierDecayAlt.P.JCTx6.Pos

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

theorem isCutG_scale {χ : ℝ → ℝ} (hχ : C6.IsCut0 χ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ U.IsCutG (δ * ε) (fun x => χ (ε⁻¹ * x)) := by
  obtain ⟨δ, hδ, hG, -⟩ := Lev0.isCutG_div hχ hε
  refine ⟨δ, hδ, ?_⟩
  have hfun : (fun x => χ (ε⁻¹ * x)) = fun x => χ (x / ε) := by
    funext x
    rw [div_eq_inv_mul]
  rw [hfun]
  exact hG

theorem bump_exists {c₀ : ℂ} (hc : c₀ ≠ 0) :
    ∃ χD : ℂ → ℂ, U.IsCutC χD ∧ (∀ w, dist w c₀ ≤ ‖c₀‖ / 4 → χD w = 1) ∧
      (∀ w ∈ tsupport χD, ‖c₀‖ / 2 ≤ ‖w‖ ∧ ‖w‖ ≤ 2 * ‖c₀‖) := by
  have hc0 : 0 < ‖c₀‖ := norm_pos_iff.mpr hc
  let b : ContDiffBump c₀ := ⟨‖c₀‖ / 4, ‖c₀‖ / 2, by positivity, by linarith⟩
  refine ⟨fun w => ((b w : ℝ) : ℂ), ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · exact Complex.ofRealCLM.contDiff.comp b.contDiff
  · exact b.hasCompactSupport.comp_left Complex.ofReal_zero
  · intro h0
    have h1 := tsupport_comp_subset (g := Complex.ofReal) Complex.ofReal_zero b h0
    rw [b.tsupport_eq, mem_closedBall, dist_comm, dist_zero_right] at h1
    have h2 : b.rOut = ‖c₀‖ / 2 := rfl
    linarith
  · intro w hw
    have := b.one_of_mem_closedBall (x := w) (mem_closedBall.mpr hw)
    simp [this]
  · intro w hw
    have h1 := tsupport_comp_subset (g := Complex.ofReal) Complex.ofReal_zero b hw
    rw [b.tsupport_eq, mem_closedBall] at h1
    have h1' : dist w c₀ ≤ ‖c₀‖ / 2 := h1
    rw [dist_eq_norm] at h1'
    constructor
    · have := norm_sub_norm_le c₀ w
      rw [norm_sub_rev] at this
      linarith
    · have := norm_le_insert' w c₀
      linarith

end Formalism.FourierDecayAlt.P.JCTx6.Pos

open Matrix MeasureTheory Filter Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P.JCTx6.Pos

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

theorem cont_DjU (k j ρ : ℕ) : Continuous (fun g : B.Mat k (j + ρ) => U.DjU k j ρ g) := by
  unfold U.DjU U.Zh
  first
    | fun_prop
    | exact Continuous.matrix_det (by fun_prop)

theorem detM_Zv (n : ℕ) (t : ℂ) (u : G.UT (n + 1) → ℂ) :
    G.detM (G.ptLong (n + 1) t * G.upper u) = t ^ (n + 1) * (G.wMat (n + 1)).det := by
  show Matrix.det (G.ptLong (n + 1) t * G.upper u) = _
  rw [Matrix.det_mul, Formalism.FourierDecayAlt.P.JCTx6.Int.det_upper_eq_one', mul_one, G.ptLong, Matrix.det_smul, Fintype.card_fin]

def Zv (n : ℕ) (t : ℂ) (u : G.UT (n + 1) → ℂ) : G.Mat (n + 1) := fun i j => (G.ptLong (n + 1) t * G.upper u) i j

theorem Zv_entry (n : ℕ) (t : ℂ) (u : G.UT (n + 1) → ℂ) (q : G.UT (n + 1)) :
    (G.ptLong (n + 1) t * G.upper u) q.1.1.rev q.1.2 = t * u q := by
  have h := Formalism.FourierDecayAlt.P.JCTx6.Int.Zu_entry n t u q
  simpa [Formalism.FourierDecayAlt.P.JCTx6.Int.Zu, G.ptLong] using h

theorem Zv_norm (n : ℕ) {t : ℂ} (ht : t ≠ 0) (u : G.UT (n + 1) → ℂ) :
    ‖t‖ * ‖u‖ ≤ ‖Zv n t u‖ := by
  have ht' : 0 < ‖t‖ := norm_pos_iff.mpr ht
  have hb : ‖u‖ ≤ ‖t‖⁻¹ * ‖Zv n t u‖ := by
    refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun q => ?_
    have h1 : ‖Zv n t u q.1.1.rev q.1.2‖ ≤ ‖Zv n t u‖ :=
      (norm_le_pi_norm (Zv n t u q.1.1.rev) q.1.2).trans (norm_le_pi_norm (Zv n t u) q.1.1.rev)
    have h2 : Zv n t u q.1.1.rev q.1.2 = t * u q := Zv_entry n t u q
    rw [h2, norm_mul] at h1
    rw [le_inv_mul_iff₀ ht']
    exact h1
  rw [le_inv_mul_iff₀ ht'] at hb
  exact hb

theorem Zv_decay (n : ℕ) {t : ℂ} (ht : t ≠ 0) (u : G.UT (n + 1) → ℂ) {a : ℝ} (ha : 0 ≤ a) :
    (1 + ‖Zv n t u‖) ^ (-a) ≤
      (min 1 ‖t‖) ^ (-a) * (1 + ‖u‖) ^ (-a) := by
  have ht' : 0 < ‖t‖ := norm_pos_iff.mpr ht
  have hm : 0 < min 1 ‖t‖ := lt_min one_pos ht'
  have hZ := Zv_norm n ht u
  have hxy : min 1 ‖t‖ * (1 + ‖u‖) ≤ 1 + ‖Zv n t u‖ := by
    have h1 : min 1 ‖t‖ ≤ 1 := min_le_left _ _
    have h2 : min 1 ‖t‖ ≤ ‖t‖ := min_le_right _ _
    nlinarith [norm_nonneg u, mul_le_mul_of_nonneg_right h2 (norm_nonneg u)]
  rw [← Real.mul_rpow hm.le (by positivity)]
  first
    | exact Real.rpow_le_rpow_of_nonpos (by positivity) hxy (by linarith)
    | (rw [Real.rpow_neg (by positivity), Real.rpow_neg (by positivity)]
       exact inv_anti₀ (Real.rpow_pos_of_pos (by positivity) _) (Real.rpow_le_rpow (by positivity) hxy ha))

end Formalism.FourierDecayAlt.P.JCTx6.Pos

open Matrix MeasureTheory Filter Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P.JCTx6.Pos

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

set_option maxHeartbeats 1000000 in
theorem posCore : PosCore := by
  intro hIntG hTrans
  obtain ⟨CcU, hCcU⟩ := Formalism.FourierDecayAlt.P.corollary_u2_germ_hypothesis 127 0
  refine ⟨max CcU 0, le_max_right _ _, ?_⟩
  intro k ph n ρ Wp Wq _ _ _ _ _ _ z z' hz hz' Θ o κ hΘ f χ A₀ ε hf hfA hχ hε F hF σ d t hd ht As mm A ho hκ
    hmm hAs hA hA₀

  have hw : (G.wMat (n + 1)).det ≠ 0 := Formalism.FourierDecayAlt.P.G2.det_wMat_ne_zero (n + 1)
  set c₀ : ℂ := (U.hMat σ d).det * (t ^ (n + 1) * (G.wMat (n + 1)).det) with hc₀def
  have hc₀ : c₀ ≠ 0 := mul_ne_zero (Formalism.FourierDecayAlt.P.Ux10.det_hMat_ne σ d hd) (mul_ne_zero (pow_ne_zero _ ht) hw)
  have hc₀n : 0 < ‖c₀‖ := norm_pos_iff.mpr hc₀
  obtain ⟨χD, hχD, hχD1, hχDs⟩ := bump_exists hc₀
  obtain ⟨δ, hδ, hχε⟩ := isCutG_scale hχ hε
  set ε' : ℝ := δ * ε / (2 * ‖c₀‖) ^ 2 with hε'def
  have hε' : 0 < ε' := by positivity
  let UD : U.UData k ph (n + 1) ρ Wp Wq Unit :=
    ⟨σ, d, z, z', fun _ => Θ, χD, fun x => χ (ε⁻¹ * x), δ * ε, ε', o, κ, 0, mm, As⟩
  have hAs1 : 1 ≤ As := le_trans (Nat.one_le_pow _ _ (by omega)) hAs
  have hOk : UD.Ok 0 := by
    refine ⟨hd, by omega, hz, hz', fun _ => hΘ, hχD, hχε, hε', ?_, ho, hκ, by simp [UD], hmm, hAs,
      by simpa using hAs1⟩
    intro w hw'
    have h2 := (hχDs w hw').2
    have h3 : ‖w‖ ^ 2 ≤ (2 * ‖c₀‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h2 2
    calc ε' * ‖w‖ ^ 2 ≤ ε' * (2 * ‖c₀‖) ^ 2 := mul_le_mul_of_nonneg_left h3 hε'.le
      _ = δ * ε := by rw [hε'def]; field_simp
  have hA₀U : CcU * (((ph + (n + 1) + ρ : ℕ) : ℝ) + 1) ^ 4 * (As : ℝ) ≤ A₀ := by
    refine le_trans ?_ hA₀
    gcongr
    exact le_max_left _ _
  obtain ⟨ha1, -, -, C, hC⟩ := hCcU k ph (n + 1) ρ Wp Wq Unit UD hOk A₀ hA₀U
  set a := UD.a 0 A₀ with ha_def
  obtain ⟨c, hc⟩ := hfA (3 * As)
  obtain ⟨V, indexVFirst, indexVSecond, hVc, ⟨MM⟩⟩ :=
    Formalism.FourierDecayAlt.P.compactly_supported_banach_model k ρ (Unit → (Wq →L[ℂ] Wp)) (UD.a 0 A₀) mm UD.S
  obtain ⟨Φ, hΦev, hΦreg⟩ := hC f c hc V MM

  obtain ⟨C1, hC1⟩ := Formalism.FourierDecayAlt.P.corollary_u1_truncated_alt k (ph + (n + 1)) ρ Wp Wq z z' o κ Θ χD
    (fun x => χ (ε⁻¹ * x)) (δ * ε) hΘ hχD hχε 0 (3 * As) A₀ (by omega)
  have hStar := hC1 f c hc
  set F₁ := B.opApply Θ (U.cutDG k (ph + (n + 1)) ρ z z' χD (fun x => χ (ε⁻¹ * x)) f) with hF₁def

  have hB : ∀ g ∈ B.GV k (ph + (n + 1) + ρ), U.DjU k (ph + (n + 1)) ρ g = c₀ → F g = F₁ g := by
    intro g hg hgc
    rw [hF g hg (by rw [hgc]; exact hc₀)]
    refine opApply_congr_open Θ (O := {x | dist (U.DjU k (ph + (n + 1)) ρ x) c₀ < ‖c₀‖ / 4}) ?_ ?_ g ?_
    · exact isOpen_lt ((cont_DjU k (ph + (n + 1)) ρ).dist continuous_const) continuous_const
    · intro x hx
      simp only [U.cutDG]
      rw [hχD1 _ (le_of_lt hx), one_mul, div_eq_inv_mul]
    · show dist _ c₀ < ‖c₀‖ / 4
      rw [hgc, dist_self]; positivity
  have hZne : ∀ v : G.UT (n + 1) → ℂ, G.detM (Zv n t v) ≠ 0 := by
    intro v
    have e : G.detM (Zv n t v) = t ^ (n + 1) * (G.wMat (n + 1)).det := detM_Zv n t v
    rw [e]; exact mul_ne_zero (pow_ne_zero _ ht) hw
  have hOrb : ∀ (ξ : U.Xi k ph (n + 1) ρ σ) (v : G.UT (n + 1) → ℂ) (γ : B.Mat k ρ), γ ∈ B.GV k ρ →
      F (U.gaXi k ρ σ d ξ (Zv n t v) γ) = F₁ (U.gaXi k ρ σ d ξ (Zv n t v) γ) := by
    intro ξ v γ hγ
    apply hB _ (Formalism.FourierDecayAlt.P.Ux10.gaXi_mem Formalism.FourierDecayAlt.P.slice_membership Formalism.FourierDecayAlt.P.radical_parametrisation σ d hd ξ _
      (hZne v) hγ)
    rw [Formalism.FourierDecayAlt.P.Ux10.DjU_gaXi Formalism.FourierDecayAlt.P.hat_z_on_slice]
    have e : G.detM (Zv n t v) = t ^ (n + 1) * (G.wMat (n + 1)).det := detM_Zv n t v
    rw [e]

  have hK : IsCompact ((fun w : ℂ => ‖w‖) '' tsupport χD) := hχD.2.1.isCompact.image continuous_norm
  have hK0 : (fun w : ℂ => ‖w‖) '' tsupport χD ⊆ Set.Ioi 0 := by
    rintro _ ⟨w, hw', rfl⟩
    exact lt_of_lt_of_le (by positivity) (hχDs w hw').1
  have hthr : 2 * ((ph + (n + 1) + ρ : ℕ) : ℝ) * ((2 * (ph + (n + 1) + ρ) + k + 1 : ℕ) : ℝ) <
      (A₀ - (κ : ℝ) - ((ph + (n + 1) : ℕ) : ℝ) * (o : ℝ) -
        2 * (((ph + (n + 1) + ρ : ℕ) : ℝ) + 1) * ((0 + o : ℕ) : ℝ)) /
        (8 * (2 * ((ph + (n + 1) + ρ : ℕ) : ℝ) + 1)) := by
    have hnd : ((2 * (ph + (n + 1) + ρ) + k + 1 : ℕ) : ℝ) ≤ (As : ℝ) := by
      have h1 : 2 * (ph + (n + 1) + ρ) + k + 1 ≤ (2 * (ph + (n + 1) + ρ) + k + 1) ^ 3 :=
        Nat.le_self_pow (by norm_num) _
      exact_mod_cast h1.trans hAs
    have ha1' := ha1
    simp only [ha_def, U.UData.a, U.a1] at ha1'
    set R : ℝ := ((ph + (n + 1) + ρ : ℕ) : ℝ) with hR
    have hR0 : 0 ≤ R := Nat.cast_nonneg _
    have hD : 0 < 8 * (2 * R + 1) := by positivity
    set Nd : ℝ := ((2 * (ph + (n + 1) + ρ) + k + 1 : ℕ) : ℝ) with hNd
    have hNd1 : 1 ≤ Nd := by rw [hNd]; exact_mod_cast Nat.succ_le_succ (Nat.zero_le _)
    have hle : (A₀ - (κ : ℝ) - ((ph + (n + 1) : ℕ) : ℝ) * (o : ℝ) -
          2 * (R + 1) * (((0 * (n + 1) ^ 2 + 1 + mm) + o : ℕ) : ℝ) - 5 * R * (((0 * (n + 1) ^ 2 : ℕ) : ℝ) + 1) -
          2 * R * (mm : ℝ)) / (8 * (2 * R + 1)) ≤
        (A₀ - (κ : ℝ) - ((ph + (n + 1) : ℕ) : ℝ) * (o : ℝ) - 2 * (R + 1) * ((0 + o : ℕ) : ℝ)) /
          (8 * (2 * R + 1)) := by
      apply div_le_div_of_nonneg_right _ hD.le
      push_cast
      have hm0 : (0 : ℝ) ≤ mm := Nat.cast_nonneg _
      nlinarith
    have hlt : 2 * R * Nd < (((127 : ℕ) : ℝ) + 1) * (R + 1) ^ 3 * (As : ℝ) := by
      have hAs' : (1 : ℝ) ≤ As := by exact_mod_cast hAs1
      have h1 : 2 * R * Nd < 128 * (R + 1) * Nd := by nlinarith
      have h2 : 128 * (R + 1) * Nd ≤ 128 * (R + 1) ^ 3 * (As : ℝ) := by
        have h3 : (R + 1) ≤ (R + 1) ^ 3 := le_self_pow₀ (by linarith) (by norm_num)
        have h4 : (R + 1) * Nd ≤ (R + 1) ^ 3 * (As : ℝ) :=
          mul_le_mul h3 hnd (by linarith) (by positivity)
        nlinarith
      norm_num
      linarith
    exact lt_of_lt_of_le hlt (le_trans ha1' hle)

  have hInt : ∀ γ ∈ B.GV k ρ, Integrable (gInt k ph n ρ σ d t z z' F γ) (muG k ph n ρ σ) := by
    intro γ hγ
    have h1 := hIntG k ph n ρ σ d t hd ht _ hK hK0 0 _ hthr z z' (Wq →L[ℂ] Wp) F₁ (C1 * c) hStar γ hγ
    have e : gInt k ph n ρ σ d t z z' F γ = gInt k ph n ρ σ d t z z' F₁ γ := by
      funext y
      unfold gInt
      have e1 : U.gaXi k ρ σ d (y.1, y.2.1) (Matrix.of.symm (t • G.wMat (n + 1) * G.upper y.2.2)) γ =
          U.gaXi k ρ σ d (y.1, y.2.1) (Zv n t y.2.2) γ := rfl
      rw [e1, hOrb _ _ γ hγ]
    rw [e]; exact h1
  have hcore : ∀ γ ∈ B.GV k ρ,
      U.PhiFun (p := ph + (n + 1)) (s := 0) k ρ (Dx2.SL.sigP σ) (Dx2.SL.dP d t) z z' F (fun a => a.elim0) γ =
        ((Real.pi ^ ((n + 1) * n / 2) : ℝ) : ℂ) •
          G.OmLong U.betaU n (fun Z => U.PhiFun (p := ph) (s := n + 1) k ρ σ d z z' F Z γ) t :=
    fun γ hγ => Dx2.SL.core σ d t z z' F γ (hTrans k ph n ρ σ d t z z' _ F γ (hInt γ hγ))

  have ha128 : 128 * (((ph + (n + 1) + ρ : ℕ) : ℝ) + 1) ^ 3 * (As : ℝ) ≤ a := by
    have h := ha1
    norm_num at h ⊢
    exact h
  have ha0 : 0 ≤ a := le_trans (by positivity) ha128
  have hZc : Continuous (fun v : G.UT (n + 1) → ℂ => Zv n t v) := by
    show Continuous (fun v : G.UT (n + 1) → ℂ =>
      (G.ptLong (n + 1) t * G.upper v : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ))
    exact continuous_const.matrix_mul Dx2.SL.cont_upper
  have hΦc : Continuous (fun v : G.UT (n + 1) → ℂ => Φ (Zv n t v)) :=
    continuous_iff_continuousAt.2 fun v => ((hΦreg _ (hZne v)).1.continuousAt).comp hZc.continuousAt
  have hψc : Continuous (fun v : G.UT (n + 1) → ℂ => G.psi U.betaU (G.superSum (G.upper v))) := by
    have h1 : Continuous fun v : G.UT (n + 1) → ℂ => G.superSum (G.upper v) := by
      unfold G.superSum
      exact continuous_finsetSum _ fun i _ =>
        (continuous_apply _).comp ((continuous_apply _).comp Dx2.SL.cont_upper)
    unfold G.psi
    exact Complex.continuous_exp.comp (continuous_const.mul
      (Complex.continuous_ofReal.comp (Complex.continuous_re.comp (continuous_const.mul h1))))
  have hCc : 0 ≤ C * c := by
    have h := (hΦreg _ (hZne 0)).2 0 (Nat.zero_le _)
    rw [norm_iteratedFDeriv_zero] at h
    have hp : 0 < (1 + ‖Zv n t 0‖) ^ (-a) := Real.rpow_pos_of_pos (by positivity) _
    by_contra hneg
    have := mul_neg_of_neg_of_pos (lt_of_not_ge hneg) hp
    linarith [norm_nonneg (Φ (Zv n t 0))]
  have hbound : ∀ v : G.UT (n + 1) → ℂ, ‖G.psi U.betaU (G.superSum (G.upper v)) • Φ (Zv n t v)‖ ≤
      C * c * (min 1 ‖t‖) ^ (-a) * (1 + ‖v‖) ^ (-a) := by
    intro v
    rw [norm_smul, Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts.norm_psi, one_mul]
    have h := (hΦreg _ (hZne v)).2 0 (Nat.zero_le _)
    rw [norm_iteratedFDeriv_zero] at h
    refine h.trans ?_
    have := mul_le_mul_of_nonneg_left (Zv_decay n ht v ha0) hCc
    rw [← mul_assoc] at this
    exact this
  have hfin : (Module.finrank ℝ (G.UT (n + 1) → ℂ) : ℝ) < a := by
    have e : Module.finrank ℝ (G.UT (n + 1) → ℂ) = Fintype.card (G.UT (n + 1)) * 2 := by
      rw [Module.finrank_pi_fintype]
      simp [Complex.finrank_real_complex]
    have hcard : Fintype.card (G.UT (n + 1)) ≤ (n + 1) * (n + 1) := by
      have := Fintype.card_subtype_le (fun p : Fin (n + 1) × Fin (n + 1) => p.1 < p.2)
      simpa [Fintype.card_prod, Fintype.card_fin] using this
    have hcardR : ((Fintype.card (G.UT (n + 1)) * 2 : ℕ) : ℝ) ≤ 2 * (((n : ℝ) + 1) * ((n : ℝ) + 1)) := by
      have : Fintype.card (G.UT (n + 1)) * 2 ≤ 2 * ((n + 1) * (n + 1)) := by omega
      exact_mod_cast this
    rw [e]
    refine lt_of_le_of_lt hcardR (lt_of_lt_of_le ?_ ha128)
    have hn : ((n : ℝ) + 1) ≤ ((ph + (n + 1) + ρ : ℕ) : ℝ) + 1 := by push_cast; linarith [(Nat.cast_nonneg ph : (0:ℝ) ≤ ph), (Nat.cast_nonneg ρ : (0:ℝ) ≤ ρ)]
    have hAs' : (1 : ℝ) ≤ As := by exact_mod_cast hAs1
    set R1 : ℝ := ((ph + (n + 1) + ρ : ℕ) : ℝ) + 1
    have hR1 : 1 ≤ R1 := by
      have : (0 : ℝ) ≤ ((ph + (n + 1) + ρ : ℕ) : ℝ) := Nat.cast_nonneg _
      linarith
    have hn0 : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]
    have h1 : 2 * (((n : ℝ) + 1) * ((n : ℝ) + 1)) ≤ 2 * (R1 * R1) := by gcongr
    have h2 : 2 * (R1 * R1) < 128 * R1 ^ 3 := by nlinarith
    have h3 : 128 * R1 ^ 3 ≤ 128 * R1 ^ 3 * (As : ℝ) := by nlinarith
    linarith
  have hφint : Integrable (fun v : G.UT (n + 1) → ℂ => G.psi U.betaU (G.superSum (G.upper v)) • Φ (Zv n t v))
      (G.muPi U.betaU (G.UT (n + 1))) := by
    rw [Dx2.SL.muPi_betaU]
    apply Integrable.smul_measure_nnreal
    exact ((integrable_one_add_norm hfin).const_mul (C * c * (min 1 ‖t‖) ^ (-a))).mono'
      (hψc.smul hΦc).aestronglyMeasurable (Eventually.of_forall hbound)

  set W₀ : V := ∫ v, G.psi U.betaU (G.superSum (G.upper v)) • Φ (Zv n t v) ∂(G.muPi U.betaU (G.UT (n + 1)))
    with hW₀
  set Wf : V := ((Real.pi ^ ((n + 1) * n / 2) : ℝ) : ℂ) • W₀ with hWf
  have key : ∀ γ ∈ B.GV k ρ,
      U.PhiFun (p := ph + (n + 1)) (s := 0) k ρ (Dx2.SL.sigP σ) (Dx2.SL.dP d t) z z' F (fun a => a.elim0) γ =
        MM.ev Wf γ () := by
    intro γ hγ
    have hgN : 0 < B.gN γ ^ a := Real.rpow_pos_of_pos (Formalism.FourierDecayAlt.P.Ux1.gN_pos hγ) a
    let L₀ : V →ₗ[ℂ] (Wq →L[ℂ] Wp) :=
      (LinearMap.proj (R := ℂ) (φ := fun _ : Unit => Wq →L[ℂ] Wp) ()) ∘ₗ
        (LinearMap.proj (R := ℂ) (φ := fun _ : B.Mat k ρ => Unit → (Wq →L[ℂ] Wp)) γ) ∘ₗ MM.ev
    have hL₀ : ∀ w, L₀ w = MM.ev w γ () := fun w => rfl
    have hbd : ∀ w, ‖L₀ w‖ ≤ (B.gN γ ^ a)⁻¹ * ‖w‖ := by
      intro w
      rw [hL₀]
      have h1 := (MM.mem w).2 [] [] (by simp) (by simp) (by simp) γ hγ
      rw [inv_mul_eq_div, le_div_iff₀' hgN]
      exact le_trans (mul_le_mul_of_nonneg_left (norm_le_pi_norm _ ()) hgN.le) h1
    let L : V →L[ℂ] (Wq →L[ℂ] Wp) := L₀.mkContinuous _ hbd
    have hL : ∀ w, L w = MM.ev w γ () := fun w => rfl
    have hΨ : ∀ v : G.UT (n + 1) → ℂ,
        U.PhiFun (p := ph) (s := n + 1) k ρ σ d z z' F (Zv n t v) γ = MM.ev (Φ (Zv n t v)) γ () := by
      intro v
      rw [hΦev _ (hZne v) γ hγ]
      show _ = (U.PhiFun (p := ph) (s := n + 1) k ρ σ d z z' (UD.F1 f) (Zv n t v) γ) ()
      unfold U.PhiFun
      have e := (ContinuousLinearEquiv.funUnique Unit ℂ (Wq →L[ℂ] Wp)).integral_comp_comm
        (μ := U.muXi k ph (n + 1) ρ σ)
        (fun ξ => U.psiStar k ρ σ z z' ξ • UD.F1 f (U.gaXi k ρ σ d ξ (Zv n t v) γ))
      refine Eq.trans ?_ e
      refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
      show U.psiStar k ρ σ z z' ξ • F (U.gaXi k ρ σ d ξ (Zv n t v) γ) =
        U.psiStar k ρ σ z z' ξ • F₁ (U.gaXi k ρ σ d ξ (Zv n t v) γ)
      rw [hOrb ξ v γ hγ]
    rw [hcore γ hγ]
    have hOm : G.OmLong U.betaU n (fun Z => U.PhiFun (p := ph) (s := n + 1) k ρ σ d z z' F Z γ) t = L W₀ := by
      rw [hW₀, ← L.integral_comp_comm hφint]
      unfold G.OmLong
      refine integral_congr_ae (Eventually.of_forall fun v => ?_)
      show G.psi U.betaU (G.superSum (G.upper v)) • U.PhiFun (p := ph) (s := n + 1) k ρ σ d z z' F (Zv n t v) γ =
        L (G.psi U.betaU (G.superSum (G.upper v)) • Φ (Zv n t v))
      rw [L.map_smul, hL, hΨ v]
    rw [hOm, hL, hWf, map_smul]
    rfl

  have hAa : A ≤ a := le_trans hA ha128
  have hCC : B.CCle A mm (fun γ => MM.ev Wf γ ()) ‖Wf‖ :=
    Formalism.FourierDecayAlt.P.compactly_supported_monotone k ρ (Wq →L[ℂ] Wp) a A ‖Wf‖ mm _ hAa (ccle_unit (MM.mem Wf))
  have hCC' : B.CCle A mm (fun γ => U.PhiFun (p := ph + (n + 1)) (s := 0) k ρ (Dx2.SL.sigP σ)
      (Dx2.SL.dP d t) z z' F (fun a => a.elim0) γ) ‖Wf‖ :=
    Formalism.FourierDecayAlt.P.Ux1.cc_congr (fun γ hγ => (key γ hγ).symm) hCC
  refine ⟨ε', hε', hCC'.1, ⟨_, hCC'⟩, ?_⟩
  intro γ hγ hne
  by_contra hlt
  have hnot : γ ∉ UD.S := fun h => hlt h
  apply hne
  rw [key γ hγ, MM.off Wf γ hγ hnot]
  rfl

end Formalism.FourierDecayAlt.P.JCTx6.Pos

namespace Formalism.FourierDecayAlt.P.JCTx6.Asm

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants MeasureTheory

theorem sliceLevel_of (hL : LettersDD) (hP : PosCore) (hI : IntG) (hT : OrbitSliceIntegrable) : ∃ Cc, SliceLevel Cc := by
  obtain ⟨Cp, hCp0, hCp⟩ := Link2.pos_levels hL hP hI hT
  refine ⟨max 150 (16 * Cp), ?_⟩
  intro k r Wp Wq _ _ _ _ _ _ T f χ A₀ N P0 hPk hPr hk2 hχ hf hfA hA₀ ε hε i hi w hw p hp a
  rcases Nat.eq_zero_or_pos i with h0 | hpos
  · subst h0
    exact Link.level_zero_case (max 150 (16 * Cp)) (le_max_left _ _) k r Wp Wq T f χ A₀ N P0 hPk hPr hk2 hχ hfA hA₀
      ε hε hi w p hp a
  · exact hCp (max 150 (16 * Cp)) (le_max_right _ _) k r Wp Wq T f χ A₀ N P0 hPk hPr hk2 hχ hf hfA hA₀ ε hε i hi
      hpos w hw p (by rw [hp.2]) hp a

theorem slicesCCBuilt_of_parts (hL : LettersDD) (hP : PosCore) (hI : IntG) (hT : OrbitSliceIntegrable) : JCT.SlicesCCBuilt := by
  exact slicesCCBuilt_of (sliceLevel_of hL hP hI hT)

end Formalism.FourierDecayAlt.P.JCTx6.Asm

namespace Formalism.FourierDecayAlt.P

theorem slices_finite_regularity_built : Formalism.FourierDecayAlt.JCT.SlicesCCBuilt := by
  exact JCTx6.Asm.slicesCCBuilt_of_parts JCTx6.Let.lettersDD JCTx6.Pos.posCore JCTx6.Int.intG
    JCTx6.Int.orbit_slice_integrable

end Formalism.FourierDecayAlt.P
