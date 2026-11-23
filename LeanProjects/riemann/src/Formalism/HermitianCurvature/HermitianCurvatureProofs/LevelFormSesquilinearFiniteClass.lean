import Formalism.HermitianCurvature.StatementJC
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TwoByOneBlock
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormDiagonalEntryDilationGeneratorLeOne
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OrbitalIntegralAeConvergenceContinuity
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaSesquilinearity
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ExistsAuxiliaryXi
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BXiAsm
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ZinvBound
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SplLen
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ComponentFamilySettingOfSetting
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BigCellOrbitSet
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CvRhoOfParts
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PsiNormalization
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CapelliUnderIntegral
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CapelliWordSumExpansion
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CompactSupportFiniteClass
import Formalism.HermitianCurvature.HermitianCurvatureProofs.WCellMemOmPlus
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RadJFExists
import Formalism.HermitianCurvature.HermitianCurvatureProofs.InvariantOperatorUnderJacquet
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SumDualVectorEqZeta
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ActualAdjointnessFromHermitian
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RestrictionIrrelevantDoubleLevelOperator
import Formalism.HermitianCurvature.HermitianCurvatureProofs.QxChain
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OperatorPreservesFusionForms

noncomputable section

section

open Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.JCx2

open scoped ComplexOrder

theorem exists_common_eps {ι : Type*} [Fintype ι] (Q : ι → ℝ → Prop)
    (hmono : ∀ a ε ε', 0 < ε' → ε' ≤ ε → Q a ε → Q a ε') (h : ∀ a, ∃ ε, 0 < ε ∧ Q a ε) :
    ∃ ε, 0 < ε ∧ ∀ a, Q a ε := by
  classical
  choose e he hQ using h
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact ⟨1, one_pos, fun a => (IsEmpty.false a).elim⟩
  · have hpos : 0 < Finset.univ.inf' Finset.univ_nonempty e := (Finset.lt_inf'_iff _).2 fun b _ => he b
    exact ⟨_, hpos, fun a => hmono a (e a) _ hpos (Finset.inf'_le _ (Finset.mem_univ a)) (hQ a)⟩

section classes

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem ckOn_zero' {m : ℕ∞} {UU : Set (B.Mat k r)} : B.CkOn m UU (0 : B.Mat k r → (Wq →L[ℂ] Wp)) :=
  fun _ _ => ⟨Set.univ, 0, isOpen_univ, trivial, contDiffOn_const, fun _ _ _ => rfl⟩

theorem ckOn_add' {m : ℕ∞} {UU : Set (B.Mat k r)} {F F' : B.Mat k r → (Wq →L[ℂ] Wp)} (hF : B.CkOn m UU F)
    (hF' : B.CkOn m UU F') : B.CkOn m UU (F + F') := by
  intro g₀ hg₀
  obtain ⟨U, f, hU, hgU, hf, hFf⟩ := hF g₀ hg₀
  obtain ⟨U', f', hU', hgU', hf', hFf'⟩ := hF' g₀ hg₀
  refine ⟨U ∩ U', f + f', hU.inter hU', ⟨hgU, hgU'⟩,
    (hf.mono Set.inter_subset_left).add (hf'.mono Set.inter_subset_right), fun g hg hG => ?_⟩
  simp only [Pi.add_apply, hFf g hg.1 hG, hFf' g hg.2 hG]

theorem ckOn_smul' {m : ℕ∞} {UU : Set (B.Mat k r)} {F : B.Mat k r → (Wq →L[ℂ] Wp)} (c : ℂ)
    (hF : B.CkOn m UU F) : B.CkOn m UU (c • F) := by
  intro g₀ hg₀
  obtain ⟨U, f, hU, hgU, hf, hFf⟩ := hF g₀ hg₀
  refine ⟨U, c • f, hU, hgU, hf.const_smul c, fun g hg hG => ?_⟩
  simp only [Pi.smul_apply, hFf g hg hG]

def KKc (Bs : B.RealPlaceData k r Wp Wq) (A : ℝ) (mm : ℕ) : Submodule ℂ (B.Mat k r → (Wq →L[ℂ] Wp)) where
  carrier := {F | ∃ ε, 0 < ε ∧ JC.CCCoef Bs A mm ε F}
  zero_mem' := ⟨1, one_pos, ckOn_zero', ⟨0, Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_zero⟩, fun _ _ h => (h rfl).elim⟩
  add_mem' := by
    rintro F F' ⟨ε, hε, hF1, ⟨c, hc⟩, hF3⟩ ⟨ε', hε', hF1', ⟨c', hc'⟩, hF3'⟩
    refine ⟨min ε ε', lt_min hε hε', ckOn_add' hF1 hF1', ⟨c + c', Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_add hc hc'⟩,
      fun g hg hne => ?_⟩
    by_cases h : F g = 0
    · have h' : F' g ≠ 0 := by simpa [h] using hne
      exact (min_le_right _ _).trans (hF3' g hg h')
    · exact (min_le_left _ _).trans (hF3 g hg h)
  smul_mem' := by
    rintro a F ⟨ε, hε, hF1, ⟨c, hc⟩, hF3⟩
    refine ⟨ε, hε, ckOn_smul' a hF1, ⟨‖a‖ * c, Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_smul a hc⟩, fun g hg hne => ?_⟩
    refine hF3 g hg fun h => hne ?_
    simp [h]

end classes

theorem auser_mono (P : M.Par) {N N' : ℕ} (h : N ≤ N') : P5.Auser P N ≤ P5.Auser P N' := by
  unfold P5.Auser
  have : (N : ℝ) ≤ N' := by exact_mod_cast h
  gcongr

theorem mmUser_mono (P : M.Par) {N N' : ℕ} (h : N ≤ N') : P5.mmUser P N ≤ P5.mmUser P N' := by
  unfold P5.mmUser
  gcongr

theorem auser_parLev (P0 : M.Par) (j : Fin (P0.r + 1)) (N : ℕ) : P5.Auser (JC.parLev P0 j) N ≤ P5.Auser P0 N := by
  unfold P5.Auser P5.nV JC.parLev
  have h1 : ((P0.r - (j : ℕ) : ℕ) : ℝ) ≤ P0.r := by exact_mod_cast Nat.sub_le _ _
  have h2 : ((2 * (P0.r - (j : ℕ)) + P0.k + 1 : ℕ) : ℝ) ≤ ((2 * P0.r + P0.k + 1 : ℕ) : ℝ) := by
    exact_mod_cast (by omega)
  gcongr

theorem mmUser_parLev (P0 : M.Par) (j : Fin (P0.r + 1)) (N : ℕ) :
    P5.mmUser (JC.parLev P0 j) N ≤ P5.mmUser P0 N := by
  unfold P5.mmUser P5.nV JC.parLev
  have h1 : P0.r - (j : ℕ) ≤ P0.r := Nat.sub_le _ _
  have h2 : 2 * (P0.r - (j : ℕ)) + P0.k + 1 ≤ 2 * P0.r + P0.k + 1 := by omega
  gcongr

end Formalism.FourierDecayAlt.P.JCx2

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt

theorem radial_module_form_of_parts : Formalism.FourierDecayAlt.JC.RadialModuleFormOfParts := by
  intro hBeta hAct hJF hBes hNice Wp Wq _ _ _ _ _ _ P0 T j X μ L st l0 hD
  obtain ⟨C, hC, hβ⟩ := hBeta Wp Wq P0 T j μ hD.2.1
  refine ⟨C, hC, fun w F F' Φ Φ' ε hε hF hF' hΦ hΦ' => ?_⟩
  have hN := hNice Wp Wq P0 T (M.sgn P0 l0) j w F ε hε hF
  refine hβ w.length (D.actOp (D.RRlev T (M.sgn P0 l0) j w) F) F' (P5.act (P5.RRi L st 0 (D.positionted w)) Φ) Φ'
    ε hε hN hF' ?_ hΦ'
  intro a y hy
  rw [hAct Wp Wq P0 T j X μ L st l0 hD w (fun b => B.JF (T.bs j) (F b)) Φ
    (fun b => hJF P0.k (P0.r - j) Wp Wq (T.bs j) (F b) ε hε (hF b)) hΦ a y hy]
  exact (hBes Wp Wq P0 T (M.sgn P0 l0) j w F ε hε hF a y hy).symm

end Formalism.FourierDecayAlt.P

namespace Formalism.FourierDecayAlt.P.JCx2

open Formalism.FourierDecayAlt

theorem form_zero_indep {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
    [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
    {π : Q.Mx k r → (Wp →L[ℂ] Wp)} {π' : Q.Mx k r → (Wq →L[ℂ] Wq)} {S : Type} [Fintype S] [DecidableEq S]
    (μ : MeasureTheory.Measure (Formalism.QuantumDeterminants.Mt k r)) (x y : Wd.Ix S → Q.RadSp k r z z' π π') (c c' : Fin r → ℂ) :
    P5.form μ 0 x y c = P5.form μ 0 x y c' := by
  unfold P5.form
  have : ∀ c'' : P5.Cf r 0, P5.glue 0 c c'' = P5.glue 0 c' c'' := fun c'' => by
    funext l
    simp [P5.glue]
  simp only [this]

end Formalism.FourierDecayAlt.P.JCx2

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt
open scoped ComplexOrder

end Formalism.FourierDecayAlt.P

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

theorem bessel_function_finite_class : Formalism.FourierDecayAlt.JC.JFInFF := by
  intro k r Wp Wq _ _ _ _ _ _ Bs F ε _hε hF
  have := P.B5.haar_sigmaFinite Bs.haarW
  have := P.B5.haar_sigmaFinite Bs.haarN
  have := P.B5.haar_sigmaFinite Bs.haarW'
  have hN := bessel_unipotent_equiv_holds Wp Wq k r Bs.z Bs.z' cStd Bs.π Bs.π' Bs.μW Bs.μN Bs.μW' F Bs.z_mem Bs.z'_mem
    Bs.haarN.conc (fun n₀ h => Bs.haarN.left n₀ h)
  refine ⟨P5.Rad.jf_smoothLev Bs F hF.2.1, ?_, ?_, ?_⟩
  · intro g _ n hn
    have e := hN g n hn.1 1 WeylGroupFacts.mem_n_one
    rw [Matrix.mul_one, BesselCapelliCommutation.psi_one Bs.z'_mem, mul_one] at e
    exact e
  · intro g _ n hn
    have e := hN g 1 WeylGroupFacts.mem_n_one n hn.1
    rw [Matrix.one_mul, BesselCapelliCommutation.psi_one Bs.z_mem, one_mul] at e
    exact e
  · intro g _ h hh h' hh'
    exact P5.jf_uEquiv Bs F g hh hh'

end Formalism.FourierDecayAlt.P

end

section

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B

namespace Formalism.FourierDecayAlt.P.JCx2

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section mnGen

variable {k r : ℕ}

theorem mn_norm_mul_le (A B : Mat k r) : ‖A * B‖ ≤ ((2 * r + k + 1 : ℕ) : ℝ) * ‖A‖ * ‖B‖ := by
  rw [Matrix.norm_le_iff (by positivity)]
  intro i j
  rw [Matrix.mul_apply]
  calc ‖∑ l, A i l * B l j‖ ≤ ∑ l, ‖A i l * B l j‖ := norm_sum_le _ _
    _ ≤ ∑ _l : Fin (2 * r + k + 1), ‖A‖ * ‖B‖ := Finset.sum_le_sum fun l _ => by
        rw [norm_mul]
        exact mul_le_mul (Matrix.norm_entry_le_entrywise_sup_norm A) (Matrix.norm_entry_le_entrywise_sup_norm B)
          (norm_nonneg _) (norm_nonneg _)
    _ = ((2 * r + k + 1 : ℕ) : ℝ) * ‖A‖ * ‖B‖ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

theorem mn_norm_le_gN (g : Mat k r) : ‖g‖ ≤ gN g := by
  have e : gN g = Real.sqrt (∑ i, ∑ j, Complex.normSq (g i j)) := rfl
  rw [e, Matrix.norm_le_iff (Real.sqrt_nonneg _)]
  intro i j
  rw [Complex.norm_def]
  apply Real.sqrt_le_sqrt
  calc Complex.normSq (g i j) ≤ ∑ j', Complex.normSq (g i j') :=
        Finset.single_le_sum (f := fun j' => Complex.normSq (g i j')) (fun _ _ => Complex.normSq_nonneg _)
          (Finset.mem_univ j)
    _ ≤ ∑ i', ∑ j', Complex.normSq (g i' j') :=
        Finset.single_le_sum (f := fun i' => ∑ j', Complex.normSq (g i' j'))
          (fun _ _ => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _) (Finset.mem_univ i)

def mnP : List (Bool × Mat k r) → Mat k r → Mat k r
  | [], P => P
  | x :: w, P => if x.1 then mnP w P * -x.2 else mnP w P

def mnQ : List (Bool × Mat k r) → Mat k r → Mat k r
  | [], Q => Q
  | x :: w, Q => if x.1 then mnQ w Q else x.2 * mnQ w Q

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem mn_Dx_lin (Λ : Mat k r →L[ℝ] V) (x : Bool × Mat k r) (P Q : Mat k r) :
    Formalism.FourierDecayAlt.P.BetaSesquilinearity.Dx x (fun g => Λ (P * g * Q)) = fun g => Λ (P * Formalism.FourierDecayAlt.P.BetaSesquilinearity.dirv x g * Q) := by
  funext g
  rw [Formalism.FourierDecayAlt.P.BetaSesquilinearity.Dx_eq]
  have h1 := (Λ.comp (Formalism.FourierDecayAlt.P.BetaSesquilinearity.abL P Q)).hasFDerivAt.comp_hasDerivAt (0 : ℝ)
    (Formalism.FourierDecayAlt.P.BetaSesquilinearity.crv_hasDerivAt x g)
  have e1 : (fun t : ℝ => Λ (P * Formalism.FourierDecayAlt.P.BetaSesquilinearity.crv x g t * Q)) =
      (⇑(Λ.comp (Formalism.FourierDecayAlt.P.BetaSesquilinearity.abL P Q))) ∘ Formalism.FourierDecayAlt.P.BetaSesquilinearity.crv x g := by
    funext t
    simp [Formalism.FourierDecayAlt.P.BetaSesquilinearity.abL_apply]
  have e2 : Λ (P * Formalism.FourierDecayAlt.P.BetaSesquilinearity.dirv x g * Q) = (Λ.comp (Formalism.FourierDecayAlt.P.BetaSesquilinearity.abL P Q)) (Formalism.FourierDecayAlt.P.BetaSesquilinearity.dirv x g) := by
    simp [Formalism.FourierDecayAlt.P.BetaSesquilinearity.abL_apply]
  show deriv (fun t : ℝ => Λ (P * Formalism.FourierDecayAlt.P.BetaSesquilinearity.crv x g t * Q)) 0 = _
  rw [e1, e2]
  exact h1.deriv

theorem mn_Dw_lin (Λ : Mat k r →L[ℝ] V) (w : List (Bool × Mat k r)) (P Q : Mat k r) :
    Formalism.FourierDecayAlt.P.BetaSesquilinearity.Dw w (fun g => Λ (P * g * Q)) = fun g => Λ (mnP w P * g * mnQ w Q) := by
  induction w with
  | nil => rfl
  | cons x w ih =>
    show Formalism.FourierDecayAlt.P.BetaSesquilinearity.Dx x (Formalism.FourierDecayAlt.P.BetaSesquilinearity.Dw w _) = _
    rw [ih, mn_Dx_lin]
    funext g
    obtain ⟨b, X⟩ := x
    cases b
    · show Λ (mnP w P * (g * X) * mnQ w Q) = Λ (mnP w P * g * (X * mnQ w Q))
      rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc]
    · show Λ (mnP w P * (-X * g) * mnQ w Q) = Λ (mnP w P * -X * g * mnQ w Q)
      rw [Matrix.mul_assoc (mnP w P) (-X) g]

theorem norm_mnP_le (w : List (Bool × Mat k r)) (hw : ∀ x ∈ w, ‖x.2‖ ≤ 1) (P : Mat k r) :
    ‖mnP w P‖ ≤ ((2 * r + k + 1 : ℕ) : ℝ) ^ w.length * ‖P‖ := by
  induction w with
  | nil => simp [mnP]
  | cons x w ih =>
    have ih' := ih fun y hy => hw y (List.mem_cons_of_mem _ hy)
    have hx := hw x List.mem_cons_self
    have hn : (1 : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega)
    obtain ⟨b, X⟩ := x
    cases b
    · simp only [mnP, Bool.false_eq_true, if_false, List.length_cons, pow_succ]
      have : 0 ≤ ((2 * r + k + 1 : ℕ) : ℝ) ^ w.length * ‖P‖ := by positivity
      nlinarith
    · simp only [mnP, if_true, List.length_cons, pow_succ]
      calc ‖mnP w P * -X‖ ≤ ((2 * r + k + 1 : ℕ) : ℝ) * ‖mnP w P‖ * ‖-X‖ := mn_norm_mul_le _ _
        _ ≤ ((2 * r + k + 1 : ℕ) : ℝ) * (((2 * r + k + 1 : ℕ) : ℝ) ^ w.length * ‖P‖) * 1 := by
          rw [norm_neg]
          gcongr
        _ = _ := by ring

theorem mn_mnQ_norm (w : List (Bool × Mat k r)) (hw : ∀ x ∈ w, ‖x.2‖ ≤ 1) (Q : Mat k r) :
    ‖mnQ w Q‖ ≤ ((2 * r + k + 1 : ℕ) : ℝ) ^ w.length * ‖Q‖ := by
  induction w with
  | nil => simp [mnQ]
  | cons x w ih =>
    have ih' := ih fun y hy => hw y (List.mem_cons_of_mem _ hy)
    have hx := hw x List.mem_cons_self
    have hn : (1 : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega)
    obtain ⟨b, X⟩ := x
    cases b
    · simp only [mnQ, Bool.false_eq_true, if_false, List.length_cons, pow_succ]
      calc ‖X * mnQ w Q‖ ≤ ((2 * r + k + 1 : ℕ) : ℝ) * ‖X‖ * ‖mnQ w Q‖ := mn_norm_mul_le _ _
        _ ≤ ((2 * r + k + 1 : ℕ) : ℝ) * 1 * (((2 * r + k + 1 : ℕ) : ℝ) ^ w.length * ‖Q‖) := by
          gcongr
        _ = _ := by ring
    · simp only [mnQ, if_true, List.length_cons, pow_succ]
      have : 0 ≤ ((2 * r + k + 1 : ℕ) : ℝ) ^ w.length * ‖Q‖ := by positivity
      nlinarith

theorem mn_dLR_lin_bound (Λ : Mat k r →L[ℝ] V) (K : ℝ) (hK : ∀ M, ‖Λ M‖ ≤ K * ‖M‖) (m : ℕ) :
    ∀ u v : List (Mat k r), (∀ X ∈ u, unitLie k r X) → (∀ X ∈ v, unitLie k r X) → u.length + v.length ≤ m →
      ∀ g : Mat k r, ‖dLR u v (fun g => Λ g) g‖ ≤
        K * ((2 * r + k + 1 : ℕ) : ℝ) ^ (2 * m + 2) * gN g := by
  intro u v hu hv hl g
  have hK0 : 0 ≤ K := by
    have h := hK 1
    by_contra hneg
    have h1 : (0 : ℝ) < ‖(1 : Mat k r)‖ := norm_pos_iff.2 one_ne_zero
    nlinarith [norm_nonneg (Λ 1)]
  set n : ℝ := ((2 * r + k + 1 : ℕ) : ℝ) with hn_def
  have hn : (1 : ℝ) ≤ n := by rw [hn_def]; exact_mod_cast (by omega)
  have e : (fun g => Λ g) = fun g => Λ (1 * g * 1) := by funext g; simp
  rw [Formalism.FourierDecayAlt.P.BetaSesquilinearity.dLR_eq, e, mn_Dw_lin]
  set w := Formalism.FourierDecayAlt.P.BetaSesquilinearity.wL u ++ Formalism.FourierDecayAlt.P.BetaSesquilinearity.wR v
  have hw : ∀ x ∈ w, ‖x.2‖ ≤ 1 := by
    intro x hx
    rcases List.mem_append.mp hx with h | h
    · obtain ⟨X, hX, rfl⟩ := List.mem_map.mp h
      exact (Matrix.norm_le_iff zero_le_one).2 (hu X hX).2
    · obtain ⟨X, hX, rfl⟩ := List.mem_map.mp h
      exact (Matrix.norm_le_iff zero_le_one).2 (hv X hX).2
  have hlen : w.length ≤ m := by rw [Formalism.FourierDecayAlt.P.BetaSesquilinearity.len_LR]; exact hl
  have h1 : ‖(1 : Mat k r)‖ ≤ 1 := by
    rw [Matrix.norm_le_iff zero_le_one]
    intro i j
    by_cases h : i = j <;> simp [Matrix.one_apply, h]
  have hP := (norm_mnP_le w hw 1).trans (mul_le_of_le_one_right (by positivity) h1)
  have hQ := (mn_mnQ_norm w hw 1).trans (mul_le_of_le_one_right (by positivity) h1)
  have hpow : n ^ w.length ≤ n ^ m := pow_le_pow_right₀ hn hlen
  have hg := mn_norm_le_gN g
  have hn0 : 0 ≤ n := by linarith
  have hPm : ‖mnP w 1‖ ≤ n ^ m := hP.trans hpow
  have hQm : ‖mnQ w 1‖ ≤ n ^ m := hQ.trans hpow
  have hm1 : ‖mnP w 1 * g * mnQ w 1‖ ≤ n * (n * ‖mnP w 1‖ * ‖g‖) * ‖mnQ w 1‖ :=
    (mn_norm_mul_le _ _).trans (by gcongr; exact mn_norm_mul_le _ _)
  have hgN : 0 ≤ gN g := Real.sqrt_nonneg _
  have hm2 : n * (n * ‖mnP w 1‖ * ‖g‖) * ‖mnQ w 1‖ ≤ n * (n * n ^ m * gN g) * n ^ m := by
    have a1 : n * ‖mnP w 1‖ * ‖g‖ ≤ n * n ^ m * gN g :=
      mul_le_mul (mul_le_mul_of_nonneg_left hPm hn0) hg (norm_nonneg _) (mul_nonneg hn0 (pow_nonneg hn0 _))
    have a2 : 0 ≤ n * (n * n ^ m * gN g) := mul_nonneg hn0 (mul_nonneg (mul_nonneg hn0 (pow_nonneg hn0 _)) hgN)
    exact mul_le_mul (mul_le_mul_of_nonneg_left a1 hn0) hQm (norm_nonneg _) a2
  calc ‖Λ (mnP w 1 * g * mnQ w 1)‖ ≤ K * ‖mnP w 1 * g * mnQ w 1‖ := hK _
    _ ≤ K * (n * (n * n ^ m * gN g) * n ^ m) := mul_le_mul_of_nonneg_left (hm1.trans hm2) hK0
    _ = K * n ^ (2 * m + 2) * gN g := by ring

end mnGen

end Formalism.FourierDecayAlt.P.JCx2

namespace Formalism.FourierDecayAlt.P.JCx2

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section mnNice

variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem mn_ckOn_congr {m : ℕ∞} {F F' : Mat k r → E} (hE : ∀ g ∈ GV k r, F g = F' g)
    (h : CkOn m (GV k r) F) : CkOn m (GV k r) F' := by
  intro g₀ hg₀
  obtain ⟨U, f, hU, hgU, hf, hff⟩ := h g₀ hg₀
  exact ⟨U, f, hU, hgU, hf, fun g hg hG => (hE g hG).symm.trans (hff g hg hG)⟩

theorem mn_ccle_congr {A : ℝ} {m : ℕ} {c : ℝ} {F F' : Mat k r → E} (hE : ∀ g ∈ GV k r, F g = F' g)
    (h : CCle A m F c) : CCle A m F' c := by
  refine ⟨mn_ckOn_congr hE h.1, fun u v hu hv hl g hg => ?_⟩
  have e := Formalism.FourierDecayAlt.P.BetaSesquilinearity.Dw_congr (Formalism.FourierDecayAlt.P.BetaSesquilinearity.lie_LR (Formalism.FourierDecayAlt.P.BetaSesquilinearity.unit_lie hu)
    (Formalism.FourierDecayAlt.P.BetaSesquilinearity.unit_lie hv)) hE g hg
  rw [Formalism.FourierDecayAlt.P.BetaSesquilinearity.dLR_eq, ← e, ← Formalism.FourierDecayAlt.P.BetaSesquilinearity.dLR_eq]
  exact h.2 u v hu hv hl g hg

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] {Bs : RealPlaceData k r Wp Wq} {ε : ℝ}

theorem mn_nice_zero : JC.NiceCoef Bs ε (fun _ : Mat k r => (0 : Wq →L[ℂ] Wp)) :=
  ⟨Formalism.FourierDecayAlt.P.BetaSesquilinearity.CkOn_zero, fun _ _ => ⟨0, Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_zero⟩, fun _ _ h => (h rfl).elim⟩

theorem mn_nice_add {F F' : Mat k r → (Wq →L[ℂ] Wp)} (h : JC.NiceCoef Bs ε F) (h' : JC.NiceCoef Bs ε F') :
    JC.NiceCoef Bs ε (fun g => F g + F' g) := by
  refine ⟨Formalism.FourierDecayAlt.P.BetaSesquilinearity.CkOn_add h.1 h'.1, fun A m => ?_, fun g hg hne => ?_⟩
  · obtain ⟨c, hc⟩ := h.2.1 A m
    obtain ⟨c', hc'⟩ := h'.2.1 A m
    exact ⟨c + c', Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_add hc hc'⟩
  · by_cases hF : F g = 0
    · exact h'.2.2 g hg (by simpa [hF] using hne)
    · exact h.2.2 g hg hF

theorem mn_nice_smul (a : ℂ) {F : Mat k r → (Wq →L[ℂ] Wp)} (h : JC.NiceCoef Bs ε F) :
    JC.NiceCoef Bs ε (fun g => a • F g) := by
  refine ⟨Formalism.FourierDecayAlt.P.BetaSesquilinearity.CkOn_smul a h.1, fun A m => ?_, fun g hg hne => h.2.2 g hg fun h0 => hne (by simp [h0])⟩
  obtain ⟨c, hc⟩ := h.2.1 A m
  exact ⟨_, Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_smul a hc⟩

theorem mn_nice_neg {F : Mat k r → (Wq →L[ℂ] Wp)} (h : JC.NiceCoef Bs ε F) :
    JC.NiceCoef Bs ε (fun g => -F g) := by
  have e : (fun g => -F g) = fun g => (-1 : ℂ) • F g := by funext g; simp
  rw [e]
  exact mn_nice_smul (-1) h

theorem mn_nice_sum {ι : Type*} (s : Finset ι) (F : ι → Mat k r → (Wq →L[ℂ] Wp))
    (h : ∀ i ∈ s, JC.NiceCoef Bs ε (F i)) : JC.NiceCoef Bs ε (fun g => ∑ i ∈ s, F i g) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (mn_nice_zero (Bs := Bs) (ε := ε))
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact mn_nice_add (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem mn_nice_sum' {ι : Type*} (s : Finset ι) (F : ι → Mat k r → (Wq →L[ℂ] Wp))
    (h : ∀ i ∈ s, JC.NiceCoef Bs ε (F i)) : JC.NiceCoef Bs ε (∑ i ∈ s, F i) := by
  have e : (∑ i ∈ s, F i) = fun g => ∑ i ∈ s, F i g := by funext g; simp [Finset.sum_apply]
  rw [e]
  exact mn_nice_sum s F h

theorem mn_nice_congr {F F' : Mat k r → (Wq →L[ℂ] Wp)} (hE : ∀ g ∈ GV k r, F g = F' g)
    (h : JC.NiceCoef Bs ε F) : JC.NiceCoef Bs ε F' := by
  refine ⟨mn_ckOn_congr hE h.1, fun A m => ?_, fun g hg hne => h.2.2 g hg (by rw [hE g hg]; exact hne)⟩
  obtain ⟨c, hc⟩ := h.2.1 A m
  exact ⟨c, mn_ccle_congr hE hc⟩

def mnGood (Bs : RealPlaceData k r Wp Wq) (ε : ℝ) (c : Mat k r → ℂ) : Prop :=
  ∀ F : Mat k r → (Wq →L[ℂ] Wp), JC.NiceCoef Bs ε F → JC.NiceCoef Bs ε (fun g => c g • F g)

theorem mn_good_const (a : ℂ) : mnGood Bs ε (fun _ => a) := fun _ h => mn_nice_smul a h

theorem mn_good_mul {c₁ c₂ : Mat k r → ℂ} (h₁ : mnGood Bs ε c₁) (h₂ : mnGood Bs ε c₂) :
    mnGood Bs ε (fun g => c₁ g * c₂ g) := by
  intro F hF
  have e : (fun g => (c₁ g * c₂ g) • F g) = fun g => c₁ g • (c₂ g • F g) := funext fun g => mul_smul _ _ _
  rw [e]
  exact h₁ _ (h₂ F hF)

theorem mn_good_add {c₁ c₂ : Mat k r → ℂ} (h₁ : mnGood Bs ε c₁) (h₂ : mnGood Bs ε c₂) :
    mnGood Bs ε (fun g => c₁ g + c₂ g) := by
  intro F hF
  have e : (fun g => (c₁ g + c₂ g) • F g) = fun g => c₁ g • F g + c₂ g • F g := funext fun g => add_smul _ _ _
  rw [e]
  exact mn_nice_add (h₁ F hF) (h₂ F hF)

theorem mn_good_sub {c₁ c₂ : Mat k r → ℂ} (h₁ : mnGood Bs ε c₁) (h₂ : mnGood Bs ε c₂) :
    mnGood Bs ε (fun g => c₁ g - c₂ g) := by
  have e : (fun g => c₁ g - c₂ g) = fun g => c₁ g + (fun _ => (-1 : ℂ)) g * c₂ g := by funext g; ring
  rw [e]
  exact mn_good_add h₁ (mn_good_mul (mn_good_const (-1)) h₂)

theorem mn_good_congr {c c' : Mat k r → ℂ} (hE : ∀ g ∈ GV k r, c g = c' g) (h : mnGood Bs ε c) :
    mnGood Bs ε c' :=
  fun F hF => mn_nice_congr (fun g hg => by simp only [hE g hg]) (h F hF)

theorem mn_good_lin (L : Mat k r →L[ℝ] ℂ) : mnGood Bs ε (fun g => L g) := by
  intro F hF
  refine ⟨?_, fun A m => ?_, fun g hg hne => hF.2.2 g hg fun h0 => hne (by simp [h0])⟩
  · intro g₀ hg₀
    obtain ⟨U, f, hU, hgU, hf, hff⟩ := hF.1 g₀ hg₀
    exact ⟨U, fun g => L g • f g, hU, hgU, L.contDiff.contDiffOn.smul hf, fun g hg hG => by simp only [hff g hg hG]⟩
  · obtain ⟨c, hc⟩ := hF.2.1 (A + 1) m
    set Λ : Mat k r →L[ℝ] ((Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp)) :=
      ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp))).restrictScalars ℝ).comp
        L with hΛdef
    have hΛ : ∀ g, Λ g = L g • ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp) := fun g => by simp [Λ]
    obtain ⟨K, hK⟩ : ∃ K : ℝ, ∀ M, ‖Λ M‖ ≤ K * ‖M‖ := ⟨_, Λ.le_opNorm⟩
    have ha : CkOn (m : ℕ∞) Set.univ (fun g => Λ g) := fun g₀ _ =>
      ⟨Set.univ, fun g => Λ g, isOpen_univ, trivial, Λ.contDiff.contDiffOn, fun _ _ _ => rfl⟩
    have hab : ∀ u v : List (Mat k r), (∀ X ∈ u, unitLie k r X) → (∀ X ∈ v, unitLie k r X) →
        u.length + v.length ≤ m → ∀ g ∈ GV k r, g ∉ (∅ : Set (Mat k r)) →
          ‖dLR u v (fun g => Λ g) g‖ ≤ (K * ((2 * r + k + 1 : ℕ) : ℝ) ^ (2 * m + 2)) * gN g ^ (1 : ℝ) := by
      intro u v hu hv hl g _ _
      rw [Real.rpow_one]
      exact mn_dLR_lin_bound Λ K hK m u v hu hv hl g
    have hb := Formalism.FourierDecayAlt.P.BetaSesquilinearity.prodBound (O := ∅) (UU := Set.univ) isOpen_empty (fun g _ => Or.inr trivial)
      (A := A) (d := 1) ha hab hc (fun g _ h => h.elim)
    have e : (fun g => L g • F g) = Formalism.FourierDecayAlt.P.BetaSesquilinearity.ap (fun g => Λ g) F := by
      funext g
      simp [Formalism.FourierDecayAlt.P.BetaSesquilinearity.ap, hΛ]
    rw [e]
    exact ⟨_, hb⟩

theorem mn_nice_RdV {X : Mat k r} (hX : inLie k r X) {F : Mat k r → (Wq →L[ℂ] Wp)} (hF : JC.NiceCoef Bs ε F) :
    JC.NiceCoef Bs ε (RdV X F) := by
  have hXl : ∀ Y ∈ [X], inLie k r Y := by simpa using hX
  refine ⟨?_, fun A m => ?_, fun g hg hne => ?_⟩
  · exact Formalism.FourierDecayAlt.P.B5.ckOn_RdV (m := ⊤) hX (by rw [top_add]; exact hF.1)
  · have := Formalism.FourierDecayAlt.P.BetaSesquilinearity.InCC_Rw (m := m) hXl (hF.2.1 A (m + [X].length))
    simpa [Rw] using this
  · by_contra hlt
    rw [not_le] at hlt
    have hO : IsOpen {g : Mat k r | Gf k r Bs.z Bs.z' g < ε} :=
      isOpen_lt (Formalism.FourierDecayAlt.P.BetaSesquilinearity.Gf_cont _ _) continuous_const
    have hz : ∀ g' ∈ GV k r, g' ∈ {g : Mat k r | Gf k r Bs.z Bs.z' g < ε} → F g' = 0 := by
      intro g' hg' hlt'
      by_contra hne'
      exact absurd (hF.2.2 g' hg' hne') (not_le.2 hlt')
    have := Formalism.FourierDecayAlt.P.BetaSesquilinearity.Rw_vanish hO hXl hz g hg hlt
    exact hne (by simpa [Rw] using this)

theorem mn_nice_EH (a b : Fin (2 * r + k + 1)) {F : Mat k r → (Wq →L[ℂ] Wp)} (hF : JC.NiceCoef Bs ε F) :
    JC.NiceCoef Bs ε (Q.EH k r a b F) :=
  mn_nice_add (mn_nice_RdV (Formalism.FourierDecayAlt.P.Qx2.hpart1_lie (k := k) (r := r) (Matrix.single a b 1)) hF)
    (mn_nice_smul Complex.I (mn_nice_RdV (Formalism.FourierDecayAlt.P.Qx2.hpart2_lie (k := k) (r := r) (Matrix.single a b 1)) hF))

end mnNice

end Formalism.FourierDecayAlt.P.JCx2

namespace Formalism.FourierDecayAlt.P.JCx2

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section mnOps

open Matrix

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] {Bs : RealPlaceData k r Wp Wq} {ε : ℝ}

def mnLinHerm (b v : Fin (2 * r + k + 1) → ℂ) : Mat k r →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun g => herm (Hpk k r) (g *ᵥ b) v
      map_add' := by intro g g'; simp [herm, Matrix.add_mulVec, Matrix.mulVec_add, dotProduct_add]
      map_smul' := by
        intro c g
        simp [herm, Matrix.smul_mulVec, Matrix.mulVec_smul, dotProduct_smul] }

def mnLinInv (v : Fin (2 * r + k + 1) → ℂ) (p : Fin (2 * r + k + 1)) : Mat k r →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun g => ((Hpk k r * gᴴ * Hpk k r) *ᵥ v) p
      map_add' := by
        intro g g'
        simp [Matrix.conjTranspose_add, Matrix.mul_add, Matrix.add_mul, Matrix.add_mulVec]
      map_smul' := by
        intro c g
        simp [Matrix.conjTranspose_smul, Matrix.smul_mulVec] }

theorem mn_inv_gv {g : Mat k r} (hg : g ∈ GV k r) : g⁻¹ = Hpk k r * gᴴ * Hpk k r := by
  apply Matrix.inv_eq_left_inv
  have e : gᴴ * Hpk k r * g = Hpk k r := hg
  calc Hpk k r * gᴴ * Hpk k r * g = Hpk k r * (gᴴ * Hpk k r * g) := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [e, Formalism.FourierDecayAlt.P.Qx2.hpk_sq']

theorem mn_good_herm (b v : Fin (2 * r + k + 1) → ℂ) :
    mnGood Bs ε (fun g => herm (Hpk k r) (g *ᵥ b) v) :=
  mn_good_lin (mnLinHerm b v)

theorem mn_good_inv (v : Fin (2 * r + k + 1) → ℂ) (p : Fin (2 * r + k + 1)) :
    mnGood Bs ε (fun g => (g⁻¹ *ᵥ v) p) :=
  mn_good_congr (fun g hg => by
    show ((Hpk k r * gᴴ * Hpk k r) *ᵥ v) p = (g⁻¹ *ᵥ v) p
    rw [mn_inv_gv hg]) (mn_good_lin (mnLinInv v p))

def mnNP (Bs : RealPlaceData k r Wp Wq) (ε : ℝ)
    (Θ : (Mat k r → (Wq →L[ℂ] Wp)) → Mat k r → (Wq →L[ℂ] Wp)) : Prop :=
  ∀ F, JC.NiceCoef Bs ε F → JC.NiceCoef Bs ε (Θ F)

theorem mn_np_Top {Eop : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → (Mat k r → (Wq →L[ℂ] Wp)) →
    (Mat k r → (Wq →L[ℂ] Wp))} (hE : ∀ a b, mnNP Bs ε (Eop a b)) (u : ℂ) (a b : Fin (2 * r + k + 1)) :
    mnNP Bs ε (Top Eop u a b) := by
  intro F hF
  show JC.NiceCoef Bs ε (fun g => (if a = b then u • F g else 0) + Eop a b F g)
  by_cases h : a = b
  · simp only [h, ↓reduceIte]
    exact mn_nice_add (mn_nice_smul u hF) (hE b b F hF)
  · simp only [h, ↓reduceIte, zero_add]
    exact hE a b F hF

theorem mn_np_foldr (l : List ((Mat k r → (Wq →L[ℂ] Wp)) → Mat k r → (Wq →L[ℂ] Wp)))
    (hl : ∀ T ∈ l, mnNP Bs ε T) : mnNP Bs ε (fun F => l.foldr (fun T h => T h) F) := by
  induction l with
  | nil => intro F hF; exact hF
  | cons T l ih =>
    intro F hF
    exact hl T List.mem_cons_self _ (ih (fun T' h' => hl T' (List.mem_cons_of_mem _ h')) F hF)

theorem mn_np_qminorOp {Eop : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → (Mat k r → (Wq →L[ℂ] Wp)) →
    (Mat k r → (Wq →L[ℂ] Wp))} (hE : ∀ a b, mnNP Bs ε (Eop a b)) {t : ℕ} (a b : Fin t → Fin (2 * r + k + 1))
    (u : ℂ) : mnNP Bs ε (qminorOp Eop a b u) := by
  intro F hF
  unfold qminorOp
  apply mn_nice_sum'
  intro σ _
  have h := mn_np_foldr (Bs := Bs) (ε := ε)
    (List.ofFn fun k : Fin t => Top Eop (u - ((k : ℕ) : ℂ)) (a (σ k)) (b k)) (fun T hT => by
      rw [List.mem_ofFn] at hT
      obtain ⟨i, rfl⟩ := hT
      exact mn_np_Top hE _ _ _) F hF
  exact mn_nice_smul _ h

theorem mn_np_chatL {Eop : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → (Mat k r → (Wq →L[ℂ] Wp)) →
    (Mat k r → (Wq →L[ℂ] Wp))} (hE : ∀ a b, mnNP Bs ε (Eop a b)) {t : ℕ} (pos : Fin t → Fin (2 * r + k + 1))
    (u : ℂ) (a β : Mat k r → Fin t → ℂ) (ha : ∀ j, mnGood Bs ε (fun g => a g j))
    (hβ : ∀ i, mnGood Bs ε (fun g => β g i)) : mnNP Bs ε (Q.chatL Eop pos u a β) := by
  intro F hF
  unfold Q.chatL
  apply mn_nice_sum
  intro i _
  apply mn_nice_sum
  intro j _
  exact mn_good_mul (mn_good_mul (mn_good_const _) (hβ i)) (ha j) _
    (mn_np_qminorOp hE _ _ u F hF)

theorem mn_np_chat2L {Eop : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → (Mat k r → (Wq →L[ℂ] Wp)) →
    (Mat k r → (Wq →L[ℂ] Wp))} (hE : ∀ a b, mnNP Bs ε (Eop a b)) {t : ℕ} (pos : Fin t → Fin (2 * r + k + 1))
    (u : ℂ) (a a' β β' : Mat k r → Fin t → ℂ) (ha : ∀ j, mnGood Bs ε (fun g => a g j))
    (ha' : ∀ j, mnGood Bs ε (fun g => a' g j)) (hβ : ∀ i, mnGood Bs ε (fun g => β g i))
    (hβ' : ∀ i, mnGood Bs ε (fun g => β' g i)) : mnNP Bs ε (Q.chat2L Eop pos u a a' β β') := by
  intro F hF
  unfold Q.chat2L
  apply mn_nice_sum; intro i _
  apply mn_nice_sum; intro i' _
  apply mn_nice_sum; intro j _
  apply mn_nice_sum; intro j' _
  by_cases hP : i < i' ∧ j < j'
  · simp only [if_pos hP]
    exact mn_good_mul (mn_good_mul (mn_good_const _)
      (mn_good_sub (mn_good_mul (hβ i) (hβ' i')) (mn_good_mul (hβ i') (hβ' i))))
      (mn_good_sub (mn_good_mul (ha j) (ha' j')) (mn_good_mul (ha j') (ha' j))) _
      (mn_np_qminorOp hE _ _ u F hF)
  · simp only [if_neg hP]
    exact mn_nice_zero

theorem mn_np_EH : ∀ a b, mnNP Bs ε (Q.EH k r a b) := fun a b _ hF => mn_nice_EH a b hF

theorem mn_np_tL (z z' : Fin (2 * r + k + 1) → ℂ) (Y : ℂ) (a b : Fin 2) :
    mnNP Bs ε (Q.tL k r z z' 0 Y a b) := by
  have hyv : ∀ j, mnGood Bs ε (fun g => Q.yv k r z 0 g j) := fun j => mn_good_inv _ _
  have hybv : ∀ j, mnGood Bs ε (fun g => Q.ybv k r z 0 g j) := fun j => mn_good_herm _ _
  have hc : ∀ (v : Fin (Q.mdim k r 0) → ℂ) j, mnGood Bs ε (fun _ : Mat k r => v j) := fun v j => mn_good_const _
  intro F hF
  fin_cases a <;> fin_cases b
  · show JC.NiceCoef Bs ε (Q.capL k r 0 (Q.uC k r 0 Y) F)
    exact mn_np_qminorOp mn_np_EH _ _ _ F hF
  · show JC.NiceCoef Bs ε (-(Q.chatL (Q.EH k r) (Q.posL k r 0) (Q.uC k r 0 Y - 1) (fun _ => Q.xv k r z' 0)
      (Q.ybv k r z 0) F))
    exact mn_nice_neg (mn_np_chatL mn_np_EH _ _ _ _ (fun j => hc _ j) hybv F hF)
  · show JC.NiceCoef Bs ε (-(Q.chatL (Q.EH k r) (Q.posL k r 0) (Q.uC k r 0 Y) (Q.yv k r z 0)
      (fun _ => Q.xbv k r z' 0) F))
    exact mn_nice_neg (mn_np_chatL mn_np_EH _ _ _ _ hyv (fun j => hc _ j) F hF)
  · show JC.NiceCoef Bs ε (-(Q.chat2L (Q.EH k r) (Q.posL k r 0) (Q.uC k r 0 Y - 1) (Q.yv k r z 0)
      (fun _ => Q.xv k r z' 0) (Q.ybv k r z 0) (fun _ => Q.xbv k r z' 0) F))
    exact mn_nice_neg (mn_np_chat2L mn_np_EH _ _ _ _ _ _ hyv (fun j => hc _ j) hybv (fun j => hc _ j) F hF)

theorem mn_tL_nice (Bs : RealPlaceData k r Wp Wq) (ε : ℝ) (F : Mat k r → (Wq →L[ℂ] Wp)) (Y : ℂ) (a b : Fin 2)
    (hF : JC.NiceCoef Bs ε F) : JC.NiceCoef Bs ε (Q.tL k r Bs.z Bs.z' 0 Y a b F) :=
  mn_np_tL Bs.z Bs.z' Y a b F hF

end mnOps

end Formalism.FourierDecayAlt.P.JCx2

namespace Formalism.FourierDecayAlt.P.JCx2

section mnRR

variable {X : Type} [AddCommGroup X] [Module ℂ X]

structure mnClosed (S : D.Op X → Prop) : Prop where
  zero : S 0
  one : S 1
  add : ∀ a b, S a → S b → S (a + b)
  mul : ∀ a b, S a → S b → S (a * b)
  cop : ∀ c, S (D.cOp c)

variable {S : D.Op X → Prop} {Sl : Type} [Fintype Sl] [DecidableEq Sl]

theorem mn_sum_closed (hS : mnClosed S) {ι : Type*} (s : Finset ι) (f : ι → D.Op X) (h : ∀ i ∈ s, S (f i)) :
    S (∑ i ∈ s, f i) :=
  Finset.sum_induction f S hS.add hS.zero h

def mnAll (S : D.Op X → Prop) (M : Wd.SlopeTestRemainingChoices Sl (D.Op X)) : Prop := ∀ a b, S (M a b)

theorem mn_all_mul (hS : mnClosed S) {M N : Wd.SlopeTestRemainingChoices Sl (D.Op X)} (hM : mnAll S M) (hN : mnAll S N) :
    mnAll S (M * N) := fun a b => by
  rw [Matrix.mul_apply]
  exact mn_sum_closed hS _ _ fun c _ => hS.mul _ _ (hM a c) (hN c b)

theorem mn_all_add (hS : mnClosed S) {M N : Wd.SlopeTestRemainingChoices Sl (D.Op X)} (hM : mnAll S M) (hN : mnAll S N) :
    mnAll S (M + N) := fun a b => by
  rw [Matrix.add_apply]
  exact hS.add _ _ (hM a b) (hN a b)

theorem mn_all_zero (hS : mnClosed S) : mnAll S (0 : Wd.SlopeTestRemainingChoices Sl (D.Op X)) := fun _ _ => hS.zero

theorem mn_all_one (hS : mnClosed S) : mnAll S (1 : Wd.SlopeTestRemainingChoices Sl (D.Op X)) := fun a b => by
  rw [Matrix.one_apply]
  split_ifs
  exacts [hS.one, hS.zero]

theorem mn_all_map (hS : mnClosed S) (A : Wd.SlopeTestRemainingChoices Sl ℂ) : mnAll S (A.map D.cOp) := fun _ _ => hS.cop _

theorem mn_all_diag (hS : mnClosed S) (x : D.Op X) (hx : S x) :
    mnAll S (Matrix.diagonal fun _ : Wd.Ix Sl => x) := fun a b => by
  rw [Matrix.diagonal_apply]
  split_ifs
  exacts [hx, hS.zero]

theorem mn_all_sum (hS : mnClosed S) {ι : Type*} (s : Finset ι) (f : ι → Wd.SlopeTestRemainingChoices Sl (D.Op X))
    (h : ∀ i ∈ s, mnAll S (f i)) : mnAll S (∑ i ∈ s, f i) :=
  Finset.sum_induction f (mnAll S) (fun _ _ => mn_all_add hS) (mn_all_zero hS) h

def mnAll2 (S : D.Op X → Prop) (M : Wd.M2 (Wd.SlopeTestRemainingChoices Sl (D.Op X))) : Prop := ∀ p q, mnAll S (M p q)

theorem monomial_entries_mul (hS : mnClosed S) {M N : Wd.M2 (Wd.SlopeTestRemainingChoices Sl (D.Op X))} (hM : mnAll2 S M) (hN : mnAll2 S N) :
    mnAll2 S (M * N) := fun p q => by
  rw [Matrix.mul_apply]
  exact mn_all_sum hS _ _ fun c _ => mn_all_mul hS (hM p c) (hN c q)

theorem monomial_entries_transpose {M : Wd.M2 (Wd.SlopeTestRemainingChoices Sl (D.Op X))} (hM : mnAll2 S M) : mnAll2 S M.transpose :=
  fun p q => hM q p

theorem monomial_entries_scalar_matrix (hS : mnClosed S) (M : Wd.M2 (Wd.SlopeTestRemainingChoices Sl ℂ)) : mnAll2 S (D.scal M : Wd.M2 (Wd.SlopeTestRemainingChoices Sl (D.Op X))) :=
  fun p q => by
    unfold D.scal
    rw [Matrix.map_apply]
    exact mn_all_map hS _

theorem mn_TTop (hS : mnClosed S) (QQ : ℂ → Wd.M2 (D.Op X)) (hQQ : ∀ Y p q, S (QQ Y p q))
    (w : List (Wd.Letter ℂ Sl)) (Y : ℂ) : mnAll2 S (D.TTop QQ w Y) := by
  induction w with
  | nil =>
    intro p q
    simp only [D.TTop, Matrix.map_apply]
    exact mn_all_diag hS _ (hQQ Y p q)
  | cons l w ih =>
    simp only [D.TTop]
    split_ifs
    · exact monomial_entries_mul hS ih (monomial_entries_scalar_matrix hS _)
    · exact monomial_entries_mul hS (monomial_entries_scalar_matrix hS _) ih

theorem mn_insOp (hS : mnClosed S) (a : Sl) (M : Wd.M2 (Wd.SlopeTestRemainingChoices Sl (D.Op X))) (hM : mnAll2 S M) :
    mnAll S (D.insOp a M) := by
  unfold D.insOp
  exact mn_all_sum hS _ _ fun i _ => mn_all_sum hS _ _ fun j _ => mn_all_mul hS (mn_all_map hS _) (hM i j)

theorem mn_rrop_closure (hS : mnClosed S) (QQ : ℂ → Wd.M2 (D.Op X)) (hQQ : ∀ Y p q, S (QQ Y p q))
    (w : List (Wd.Letter ℂ Sl)) : ∀ a b, S (D.RRop QQ w a b) := by
  induction w with
  | nil => exact mn_all_one hS
  | cons l w ih =>
    simp only [D.RRop]
    refine mn_all_mul hS ih (mn_insOp hS _ _ ?_)
    split_ifs
    · exact mn_TTop hS QQ hQQ w l.pt
    · exact monomial_entries_transpose (mn_TTop hS QQ hQQ w l.pt)

end mnRR

end Formalism.FourierDecayAlt.P.JCx2

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P.JCx2

theorem module_regularity : Formalism.FourierDecayAlt.JC.ModuleNice := by
  intro Wp Wq _ _ _ _ _ _ P0 T s j w F ε hε hF a
  have hcl : mnClosed (mnNP (T.bs j) ε) :=
    { zero := fun _ _ => mn_nice_zero
      one := fun _ hF => hF
      add := fun _ _ ha hb F hF => mn_nice_add (ha F hF) (hb F hF)
      mul := fun _ _ ha hb F hF => ha _ (hb F hF)
      cop := fun c _ hF => mn_nice_smul c hF }
  have hQQ : ∀ Y p q, mnNP (T.bs j) ε (D.QQlev T s j Y p q) := fun Y p q F hF =>
    mn_nice_smul s (mn_tL_nice (T.bs j) ε F Y p q hF)
  have hR := mn_rrop_closure hcl (D.QQlev T s j) hQQ (D.positionted w)
  show JC.NiceCoef (T.bs j) ε (∑ b, D.ap (D.RRlev T s j w a b) (F b))
  exact mn_nice_sum' _ _ fun b _ => hR a b (F b) (hF b)

end Formalism.FourierDecayAlt.P

end

section

open Matrix MeasureTheory Filter Topology
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.JCx2

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem bc_qminorWords (k r : ℕ) {t : ℕ} (p q : Fin t → Fin (2 * r + k + 1)) (u : ℂ) :
    ∃ L : List (ℂ × List (B.Mat k r)),
    (∀ cw ∈ L, (∀ X ∈ cw.2, B.unitLie k r X) ∧ cw.2.length ≤ t) ∧
    ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (UU : Set (B.Mat k r)) (f : B.Mat k r → E),
      B.CkOn (t : ℕ∞) UU f → ∀ g ∈ UU, g ∈ B.GV k r →
        qminorOp (Q.EH k r) p q u f g = (L.map fun cw => cw.1 • B.Rw cw.2 f g).sum := by
  let ts : Equiv.Perm (Fin t) → List (ℂ × Fin (2 * r + k + 1) × Fin (2 * r + k + 1)) :=
    fun σ => List.ofFn fun j : Fin t => (u - ((j : ℕ) : ℂ), p (σ j), q j)
  refine ⟨(Finset.univ : Finset (Equiv.Perm (Fin t))).toList.flatMap
      (fun σ => (CapelliWordSumExpansion.expand k r (ts σ)).map fun cw => (((Equiv.Perm.sign σ : ℤ) : ℂ) * cw.1, cw.2)), ?_, ?_⟩
  · intro cw hcw
    simp only [List.mem_flatMap, List.mem_map] at hcw
    obtain ⟨σ, _, cw', hm', rfl⟩ := hcw
    have := CapelliWordSumExpansion.expand_words (k := k) (r := r) (ts σ) cw' hm'
    refine ⟨this.1, this.2.trans ?_⟩
    simp [ts]
  · intro E _ _ UU f hf g hgU hg
    have hloc : ∀ σ, CapelliWordSumExpansion.Loc ((ts σ).length : ℕ∞) f g := by
      intro σ
      obtain ⟨U, f', a, b, c, d⟩ := hf g hgU
      refine ⟨U, f', a, b, ?_, d⟩
      simpa [ts] using c
    have e1 : qminorOp (Q.EH k r) p q u f g = ∑ σ, (((Equiv.Perm.sign σ : ℤ) : ℂ)) • CapelliWordSumExpansion.foldT (ts σ) f g := by
      simp only [qminorOp, Finset.sum_apply, Pi.smul_apply]
      refine Finset.sum_congr rfl (fun σ _ => ?_)
      congr 1
      simp only [CapelliWordSumExpansion.foldT, ts, List.map_ofFn]
      rfl
    rw [e1, CapelliWordSumExpansion.sum_flatMap, Finset.sum_map_toList]
    refine Finset.sum_congr rfl (fun σ _ => ?_)
    rw [CapelliWordSumExpansion.expand_eq (ts σ) f g hg (hloc σ), List.map_map, ← CapelliWordSumExpansion.sum_map_mul_smul]
    rfl

section under

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem bc_qminor_under (D : B.RealPlaceData k r Wp Wq) (A : ℝ) (m : ℕ) (F : B.Mat k r → (Wq →L[ℂ] Wp)) {t : ℕ}
    (p q : Fin t → Fin (2 * r + k + 1)) (u : ℂ) (htm : t ≤ m) (hThr : JF.TransportedAlt k r A m) (hF : B.InCC A m F)
    (g : B.Mat k r) (hg : g ∈ JF.Om k r D.z D.z') :
    Integrable (fun p' => JF.xiP D p' • qminorOp (Q.EH k r) p q u (B.rho D p' F) g) D.μSS ∧
    qminorOp (Q.EH k r) p q u (B.JF D F) g =
      ∫ p', JF.xiP D p' • qminorOp (Q.EH k r) p q u (B.rho D p' F) g ∂D.μSS := by
  obtain ⟨L, hLw, hL⟩ := bc_qminorWords k r p q u
  have hCk : CkOn (m : ℕ∞) (GV k r) F := hF.choose_spec.1
  have hCkt : CkOn (t : ℕ∞) (GV k r) F := P.B5.ckOn_mono (by exact_mod_cast htm) hCk
  have hJ := Formalism.FourierDecayAlt.P.jacquet_derivative_formula k r Wp Wq D A m F hThr hF
  have hJck : CkOn (t : ℕ∞) (Om k r D.z D.z') (B.JF D F) := by
    intro g₀ hg₀
    obtain ⟨U, F', hU, hgU, hc, he⟩ := hJ.1 g₀ ⟨(P.CapelliUnderIntegral.glev0 g₀).2 hg₀.1, hg₀.2⟩
    exact ⟨U, F', hU, hgU, hc.of_le (by exact_mod_cast htm),
      fun g' hg'U hg'G => he g' hg'U ((P.CapelliUnderIntegral.glev0 g').2 hg'G)⟩
  have hw : ∀ cw ∈ L, (∀ X ∈ cw.2, unitLie k r X) ∧ cw.2.length ≤ m :=
    fun cw h => ⟨(hLw cw h).1, (hLw cw h).2.trans htm⟩
  have hword : ∀ cw ∈ L, Integrable (fun p' => xiP D p' • Rw cw.2 (rho D p' F) g) D.μSS ∧
      Rw cw.2 (B.JF D F) g = ∫ p', xiP D p' • Rw cw.2 (rho D p' F) g ∂D.μSS := by
    intro cw hcw
    obtain ⟨hint, heq⟩ := hJ.2 [] cw.2 (by simp) (hw cw hcw).1 (by simpa using (hw cw hcw).2) g hg
    have hae : (fun p' => xiP D p' • rho D p' (dLR ([].map (AdL p')) (cw.2.map (AdR p')) F) g) =ᵐ[D.μSS]
        (fun p' => xiP D p' • Rw cw.2 (rho D p' F) g) := by
      filter_upwards [P.B5.ae_inSS D] with p' hp
      have e := Formalism.FourierDecayAlt.P.rewrite_rho_action k r Wp Wq D m F p' hp hCk [] cw.2 (by simp)
        (fun X hX => ((hw cw hcw).1 X hX).1) (by simpa using (hw cw hcw).2) g hg.1
      simp only [List.map_nil] at e ⊢
      rw [← e]
      rfl
    exact ⟨hint.congr hae, (show Rw cw.2 (B.JF D F) g = dLR [] cw.2 (B.JF D F) g from rfl).trans
      (heq.trans (integral_congr_ae hae))⟩
  have hae2 : (fun p' => xiP D p' • qminorOp (Q.EH k r) p q u (rho D p' F) g) =ᵐ[D.μSS]
      (fun p' => (L.map (fun cw => cw.1 • (xiP D p' • Rw cw.2 (rho D p' F) g))).sum) := by
    filter_upwards [P.B5.ae_inSS D] with p' hp
    rw [hL _ _ (rho D p' F) (P.B5.ckOn_rho D hp hCkt) g hg.1 hg.1, List.smul_sum, List.map_map]
    congr 1
    refine List.map_congr_left (fun cw _ => ?_)
    simp only [Function.comp_apply]
    exact smul_comm _ _ _
  refine ⟨(P.CapelliUnderIntegral.integrable_map_sum L (fun cw p' => cw.1 • (xiP D p' • Rw cw.2 (rho D p' F) g))
    (fun cw hcw => (hword cw hcw).1.smul cw.1)).congr hae2.symm, ?_⟩
  rw [hL _ _ (B.JF D F) hJck g hg hg.1, integral_congr_ae hae2, P.CapelliUnderIntegral.integral_map_sum L
    (fun cw p' => cw.1 • (xiP D p' • Rw cw.2 (rho D p' F) g))
    (fun cw hcw => (hword cw hcw).1.smul cw.1)]
  congr 1
  refine List.map_congr_left (fun cw hcw => ?_)
  rw [integral_smul, (hword cw hcw).2]

end under

end Formalism.FourierDecayAlt.P.JCx2

namespace Formalism.FourierDecayAlt.P.JCx2

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF Formalism.FourierDecayAlt.P.BetaSesquilinearity

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section tLunder

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

def BcUnder (D : B.RealPlaceData k r Wp Wq) (F : B.Mat k r → (Wq →L[ℂ] Wp)) (g : B.Mat k r)
    (Θ : (B.Mat k r → (Wq →L[ℂ] Wp)) → B.Mat k r → (Wq →L[ℂ] Wp)) : Prop :=
  Integrable (fun p' => JF.xiP D p' • Θ (B.rho D p' F) g) D.μSS ∧
    Θ (B.JF D F) g = ∫ p', JF.xiP D p' • Θ (B.rho D p' F) g ∂D.μSS

variable {D : B.RealPlaceData k r Wp Wq} {F : B.Mat k r → (Wq →L[ℂ] Wp)} {g : B.Mat k r}

theorem bcUnder_congr {Θ Θ' : (B.Mat k r → (Wq →L[ℂ] Wp)) → B.Mat k r → (Wq →L[ℂ] Wp)}
    (h : BcUnder D F g Θ) (e : ∀ f, Θ' f g = Θ f g) : BcUnder D F g Θ' := by
  unfold BcUnder at *
  simp only [e]
  exact h

theorem bcUnder_smul {Θ : (B.Mat k r → (Wq →L[ℂ] Wp)) → B.Mat k r → (Wq →L[ℂ] Wp)} (c : ℂ)
    (h : BcUnder D F g Θ) : BcUnder D F g (fun f x => c • Θ f x) := by
  refine ⟨?_, ?_⟩
  · have := h.1.smul c
    refine this.congr (Eventually.of_forall fun p' => ?_)
    simp only [Pi.smul_apply]
    exact smul_comm _ _ _
  · simp only
    rw [h.2, ← integral_smul]
    congr 1
    funext p'
    exact smul_comm _ _ _

theorem bcUnder_neg {Θ : (B.Mat k r → (Wq →L[ℂ] Wp)) → B.Mat k r → (Wq →L[ℂ] Wp)}
    (h : BcUnder D F g Θ) : BcUnder D F g (fun f x => -Θ f x) := by
  refine ⟨?_, ?_⟩
  · exact h.1.neg.congr (Eventually.of_forall fun p' => by simp)
  · simp only
    rw [h.2, ← integral_neg]
    congr 1
    funext p'
    simp

theorem bcUnder_sum {ι : Type*} (s : Finset ι) (Θ : ι → (B.Mat k r → (Wq →L[ℂ] Wp)) → B.Mat k r → (Wq →L[ℂ] Wp))
    (h : ∀ i ∈ s, BcUnder D F g (Θ i)) : BcUnder D F g (fun f x => ∑ i ∈ s, Θ i f x) := by
  classical
  refine ⟨?_, ?_⟩
  · have := integrable_finsetSum s (fun i hi => (h i hi).1)
    refine this.congr (Eventually.of_forall fun p' => ?_)
    simp [Finset.smul_sum]
  · simp only
    rw [Finset.sum_congr rfl (fun i hi => (h i hi).2), ← integral_finsetSum s (fun i hi => (h i hi).1)]
    congr 1
    funext p'
    simp [Finset.smul_sum]

theorem bcUnder_coef {Θ : (B.Mat k r → (Wq →L[ℂ] Wp)) → B.Mat k r → (Wq →L[ℂ] Wp)} (c : B.Mat k r → ℂ)
    (h : BcUnder D F g Θ) : BcUnder D F g (fun f x => c x • Θ f x) :=
  bcUnder_congr (bcUnder_smul (c g) h) (fun _ => rfl)

theorem bcUnder_ite {Θ : (B.Mat k r → (Wq →L[ℂ] Wp)) → B.Mat k r → (Wq →L[ℂ] Wp)} (P : Prop) [Decidable P]
    (h : P → BcUnder D F g Θ) : BcUnder D F g (fun f x => if P then Θ f x else 0) := by
  by_cases hP : P
  · simp only [if_pos hP]
    exact h hP
  · simp only [if_neg hP]
    exact ⟨by simp, by simp⟩

theorem bc_tL_under (A : ℝ) (m : ℕ) (hnm : 2 * r + k + 1 ≤ m) (hThr : JF.TransportedAlt k r A m) (hF : B.InCC A m F)
    (hg : g ∈ JF.Om k r D.z D.z') (Y : ℂ) (a b : Fin 2) :
    BcUnder D F g (Q.tL k r D.z D.z' 0 Y a b) := by
  have hm : Q.mdim k r 0 = 2 * r + k + 1 := by simp [Q.mdim]
  have base : ∀ {t : ℕ} (P Q' : Fin t → Fin (2 * r + k + 1)) (u : ℂ), t ≤ 2 * r + k + 1 →
      BcUnder D F g (qminorOp (Q.EH k r) P Q' u) :=
    fun P Q' u ht => bc_qminor_under D A m F P Q' u (ht.trans hnm) hThr hF g hg
  fin_cases a <;> fin_cases b
  · exact base _ _ _ (by rw [hm])
  · refine bcUnder_congr (bcUnder_neg (bcUnder_sum (Finset.univ : Finset (Fin (Q.mdim k r 0))) _ fun i _ =>
      bcUnder_sum (Finset.univ : Finset (Fin (Q.mdim k r 0))) _ fun j _ =>
      bcUnder_coef (fun x => (-1 : ℂ) ^ ((i : ℕ) + (j : ℕ)) * Q.ybv k r D.z 0 x i * Q.xv k r D.z' 0 j)
        (base (Q.posL k r 0 ∘ Q.skip1 i) (Q.posL k r 0 ∘ Q.skip1 j) (Q.uC k r 0 Y - 1)
          (by rw [hm]; omega)))) (fun f => rfl)
  · refine bcUnder_congr (bcUnder_neg (bcUnder_sum (Finset.univ : Finset (Fin (Q.mdim k r 0))) _ fun i _ =>
      bcUnder_sum (Finset.univ : Finset (Fin (Q.mdim k r 0))) _ fun j _ =>
      bcUnder_coef (fun x => (-1 : ℂ) ^ ((i : ℕ) + (j : ℕ)) * Q.xbv k r D.z' 0 i * Q.yv k r D.z 0 x j)
        (base (Q.posL k r 0 ∘ Q.skip1 i) (Q.posL k r 0 ∘ Q.skip1 j) (Q.uC k r 0 Y)
          (by rw [hm]; omega)))) (fun f => rfl)
  · refine bcUnder_congr (bcUnder_neg (bcUnder_sum (Finset.univ : Finset (Fin (Q.mdim k r 0))) _ fun i _ =>
      bcUnder_sum (Finset.univ : Finset (Fin (Q.mdim k r 0))) _ fun i' _ =>
      bcUnder_sum (Finset.univ : Finset (Fin (Q.mdim k r 0))) _ fun j _ =>
      bcUnder_sum (Finset.univ : Finset (Fin (Q.mdim k r 0))) _ fun j' _ =>
      bcUnder_ite (i < i' ∧ j < j') fun _ => bcUnder_coef (fun x =>
        ((-1 : ℂ) ^ ((i : ℕ) + (i' : ℕ) + (j : ℕ) + (j' : ℕ)) *
          (Q.ybv k r D.z 0 x i * Q.xbv k r D.z' 0 i' - Q.ybv k r D.z 0 x i' * Q.xbv k r D.z' 0 i) *
          (Q.yv k r D.z 0 x j * Q.xv k r D.z' 0 j' - Q.yv k r D.z 0 x j' * Q.xv k r D.z' 0 j)))
        (base (Q.posL k r 0 ∘ Q.skip2 i i') (Q.posL k r 0 ∘ Q.skip2 j j') (Q.uC k r 0 Y - 1)
          (by rw [hm]; omega)))) (fun f => rfl)

end tLunder

end Formalism.FourierDecayAlt.P.JCx2

namespace Formalism.FourierDecayAlt.P.JCx2

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF Formalism.FourierDecayAlt.P.BetaSesquilinearity

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section invariance

variable {k r : ℕ}

theorem bc_qminor_post {E E' : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup E']
    [NormedSpace ℂ E'] (L : E →L[ℂ] E') {f : B.Mat k r → E} (hf : CkOn (⊤ : ℕ∞) (GV k r) f) {g : B.Mat k r}
    (hg : g ∈ GV k r) {t : ℕ} (p q : Fin t → Fin (2 * r + k + 1)) (u : ℂ) :
    qminorOp (Q.EH k r) p q u (fun x => L (f x)) g = L (qminorOp (Q.EH k r) p q u f g) := by
  have h1 := P.JFxB.qminor_trn (k := k) (r := r) L gv_one gv_one (Q.EH k r) (Q.EH k r)
    (fun c d f hf => by
      intro g hg
      rw [P.JFxB.EH_trn L gv_one gv_one c d f hf g hg, P.JFxB.EHc_one])
    (fun c d f f₂ h => P.JFxB.EH_congr c d f f₂ h) (fun c d m f hf => P.JFxB.EH_ck c d m f hf)
    p q u f (P.B5.ckOn_mono le_top hf) g hg
  rw [P.JFxB.trn_one_one, P.JFxB.trn_one_one] at h1
  exact h1

theorem bc_tL_post {E E' : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup E']
    [NormedSpace ℂ E'] (z z' : Fin (2 * r + k + 1) → ℂ) (L : E →L[ℂ] E') {f : B.Mat k r → E}
    (hf : CkOn (⊤ : ℕ∞) (GV k r) f) {g : B.Mat k r} (hg : g ∈ GV k r) (Y : ℂ) (a b : Fin 2) :
    Q.tL k r z z' 0 Y a b (fun x => L (f x)) g = L (Q.tL k r z z' 0 Y a b f g) := by
  fin_cases a <;> fin_cases b
  · exact bc_qminor_post L hf hg _ _ _
  · show -(Q.chatL (Q.EH k r) (Q.posL k r 0) (Q.uC k r 0 Y - 1) (fun _ => Q.xv k r z' 0) (Q.ybv k r z 0)
      (fun x => L (f x))) g = L (-(Q.chatL (Q.EH k r) (Q.posL k r 0) (Q.uC k r 0 Y - 1) (fun _ => Q.xv k r z' 0)
        (Q.ybv k r z 0) f) g)
    simp only [Pi.neg_apply, Q.chatL, map_neg, map_sum, map_smul, bc_qminor_post L hf hg]
  · show -(Q.chatL (Q.EH k r) (Q.posL k r 0) (Q.uC k r 0 Y) (Q.yv k r z 0) (fun _ => Q.xbv k r z' 0)
      (fun x => L (f x))) g = L (-(Q.chatL (Q.EH k r) (Q.posL k r 0) (Q.uC k r 0 Y) (Q.yv k r z 0)
        (fun _ => Q.xbv k r z' 0) f) g)
    simp only [Pi.neg_apply, Q.chatL, map_neg, map_sum, map_smul, bc_qminor_post L hf hg]
  · show -(Q.chat2L (Q.EH k r) (Q.posL k r 0) (Q.uC k r 0 Y - 1) (Q.yv k r z 0) (fun _ => Q.xv k r z' 0)
      (Q.ybv k r z 0) (fun _ => Q.xbv k r z' 0) (fun x => L (f x))) g = L (-(Q.chat2L (Q.EH k r) (Q.posL k r 0)
        (Q.uC k r 0 Y - 1) (Q.yv k r z 0) (fun _ => Q.xv k r z' 0) (Q.ybv k r z 0) (fun _ => Q.xbv k r z' 0) f) g)
    simp only [Pi.neg_apply, Q.chat2L, map_neg, map_sum, apply_ite L, map_smul, map_zero, bc_qminor_post L hf hg]

theorem bc_smoothLev {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {f : B.Mat k r → E}
    (hf : CkOn (⊤ : ℕ∞) (GV k r) f) : Q.SmoothLev k r 0 Set.univ f := by
  intro g₀ hg₀
  obtain ⟨U, F', hU, hgU, hc, he⟩ := hf g₀ ((P.CapelliUnderIntegral.glev0 g₀).1 hg₀.1)
  exact ⟨U, F', hU, hgU, hc, fun g hg hgl => he g hg ((P.CapelliUnderIntegral.glev0 g).1 hgl)⟩

theorem bc_trn_id {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {f : B.Mat k r → E} {a b : B.Mat k r}
    (ha : a ∈ GV k r) (hb : b ∈ GV k r) (hf : CkOn (⊤ : ℕ∞) (GV k r) f) :
    CkOn (⊤ : ℕ∞) (GV k r) (fun x => f (a * x * b)) := by
  have := CkOn_trn (ContinuousLinearMap.id ℂ E) ha hb hf
  have e : trn (ContinuousLinearMap.id ℂ E) a b f = fun x => f (a * x * b) := by
    funext x; simp [trn]
  rwa [e] at this

theorem bc_tL_rho {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq) {p : B.SS k r} (hp : D.inSS p)
    {F : B.Mat k r → (Wq →L[ℂ] Wp)} (hF : CkOn (⊤ : ℕ∞) (GV k r) F) (Y : ℂ) (a b : Fin 2) {g : B.Mat k r}
    (hg : g ∈ GV k r) :
    Q.tL k r D.z D.z' 0 Y a b (B.rho D p F) g = B.rho D p (Q.tL k r D.z D.z' 0 Y a b F) g := by
  obtain ⟨h1, h2, h3, h4⟩ := hp
  have ha0 : (Matrix.of p.1.1)⁻¹ * (Matrix.of p.1.2)⁻¹ ∈ GV k r := gv_mul (gv_inv h1.1) (gv_inv h2.1)
  have hb0 : Matrix.of p.2.2 * Matrix.of p.2.1 ∈ GV k r := gv_mul h4.1 h3.1
  set a0 := (Matrix.of p.1.1)⁻¹ * (Matrix.of p.1.2)⁻¹ with ha0def
  set n2 := Matrix.of p.2.2
  set h2' := Matrix.of p.2.1
  rw [P.JFxB.rho_eq_trn' D p F, P.JFxB.rho_eq_trn' D p (Q.tL k r D.z D.z' 0 Y a b F)]
  have hf1 : CkOn (⊤ : ℕ∞) (GV k r) (fun x => F (a0 * x * (n2 * h2'))) := bc_trn_id ha0 hb0 hF
  show Q.tL k r D.z D.z' 0 Y a b (fun x => P.JFxB.Lq D p ((fun x => F (a0 * x * (n2 * h2'))) x)) g =
    P.JFxB.Lq D p (Q.tL k r D.z D.z' 0 Y a b F (a0 * g * (n2 * h2')))
  rw [bc_tL_post D.z D.z' (P.JFxB.Lq D p) hf1 hg Y a b]
  congr 1

  have hF1 : CkOn (⊤ : ℕ∞) (GV k r) (fun x => F (1 * x * h2')) := bc_trn_id gv_one h3.1 hF
  have hDom : ∀ z z' : Fin (2 * r + k + 1) → ℂ, Q.IsDom k r z z' 0 Set.univ :=
    fun _ _ => ⟨isOpen_univ, fun _ _ _ _ _ _ => trivial⟩
  have hn1 : (Matrix.of p.1.2)⁻¹ ∈ Q.Nlev k r 0 := P.Qx8.nlev_inv ⟨h2, (P.CapelliUnderIntegral.glev0 _).2 h2.1⟩
  have hs : a0 ∈ Q.Slev k r D.z 0 := ⟨_, P.BigCellInversePair.uw_inv h1, _, hn1, rfl⟩
  have hs' : n2 ∈ Q.Slev k r D.z' 0 := ⟨1, P.Qx8.uw_one _, n2, ⟨h4, (P.CapelliUnderIntegral.glev0 _).2 h4.1⟩, (one_mul _).symm⟩
  have hs1 : (1 : B.Mat k r) ∈ Q.Slev k r D.z 0 := ⟨1, P.Qx8.uw_one _, 1, P.Qx8.nlev_one _, (mul_one _).symm⟩
  have hs2 : h2' ∈ Q.Slev k r D.z' 0 := ⟨h2', h3, 1, P.Qx8.nlev_one _, (mul_one _).symm⟩
  have hgl : g ∈ Q.Glev k r 0 ∩ Set.univ := ⟨(P.CapelliUnderIntegral.glev0 g).2 hg, trivial⟩
  have e1 : (fun x => F (a0 * x * (n2 * h2'))) = fun x => (fun y => F (1 * y * h2')) (a0 * x * n2) := by
    funext x; simp [Matrix.mul_assoc]
  rw [e1, Formalism.FourierDecayAlt.P.operator_invariance _ k r D.z D.z' 0 Set.univ _ Y a b D.z_mem D.z'_mem (hDom _ _)
    (bc_smoothLev hF1) a0 hs n2 hs' g hgl]
  have hy : a0 * g * n2 ∈ Q.Glev k r 0 ∩ Set.univ :=
    ⟨(P.CapelliUnderIntegral.glev0 _).2 (gv_mul (gv_mul ha0 hg) h4.1), trivial⟩
  rw [Formalism.FourierDecayAlt.P.operator_invariance _ k r D.z D.z' 0 Set.univ F Y a b D.z_mem D.z'_mem (hDom _ _)
    (bc_smoothLev hF) 1 hs1 h2' hs2 _ hy]
  simp [Matrix.mul_assoc]

end invariance

end Formalism.FourierDecayAlt.P.JCx2

namespace Formalism.FourierDecayAlt.P.JCx2

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF Formalism.FourierDecayAlt.P.BetaSesquilinearity

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section tLbessel

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem bc_tL_bessel (D : B.RealPlaceData k r Wp Wq) {F : B.Mat k r → (Wq →L[ℂ] Wp)}
    (hF : CkOn (⊤ : ℕ∞) (GV k r) F) (A : ℝ) (m : ℕ) (hnm : 2 * r + k + 1 ≤ m) (hThr : JF.TransportedAlt k r A m)
    (hFi : B.InCC A m F) (Y : ℂ) (a b : Fin 2) {g : B.Mat k r} (hg : g ∈ JF.Om k r D.z D.z') :
    B.JF D (Q.tL k r D.z D.z' 0 Y a b F) g = Q.tL k r D.z D.z' 0 Y a b (B.JF D F) g := by
  rw [(bc_tL_under (D := D) (F := F) A m hnm hThr hFi hg Y a b).2]
  show ∫ p, JF.xiP D p • B.rho D p (Q.tL k r D.z D.z' 0 Y a b F) g ∂D.μSS = _
  refine integral_congr_ae ?_
  filter_upwards [P.B5.ae_inSS D] with p hp
  rw [bc_tL_rho D hp hF Y a b hg.1]

end tLbessel

section local_

variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

def BcLoc (U : Set (B.Mat k r)) (Θ : (B.Mat k r → E) → B.Mat k r → E) : Prop :=
  ∀ f f' : B.Mat k r → E, (∀ x ∈ U, x ∈ GV k r → f x = f' x) → ∀ x ∈ U, x ∈ GV k r → Θ f x = Θ f' x

variable {U : Set (B.Mat k r)}

theorem bcLoc_congr {Θ Θ' : (B.Mat k r → E) → B.Mat k r → E} (h : BcLoc U Θ) (e : ∀ f x, Θ' f x = Θ f x) :
    BcLoc U Θ' := fun f f' hff x hx hxG => by rw [e, e]; exact h f f' hff x hx hxG

theorem bcLoc_neg {Θ : (B.Mat k r → E) → B.Mat k r → E} (h : BcLoc U Θ) : BcLoc U (fun f x => -Θ f x) :=
  fun f f' hff x hx hxG => by simp only [h f f' hff x hx hxG]

theorem bcLoc_sum {ι : Type*} (s : Finset ι) (Θ : ι → (B.Mat k r → E) → B.Mat k r → E)
    (h : ∀ i ∈ s, BcLoc U (Θ i)) : BcLoc U (fun f x => ∑ i ∈ s, Θ i f x) :=
  fun f f' hff x hx hxG => Finset.sum_congr rfl fun i hi => h i hi f f' hff x hx hxG

theorem bcLoc_coef {Θ : (B.Mat k r → E) → B.Mat k r → E} (c : B.Mat k r → ℂ) (h : BcLoc U Θ) :
    BcLoc U (fun f x => c x • Θ f x) :=
  fun f f' hff x hx hxG => by simp only [h f f' hff x hx hxG]

theorem bcLoc_ite {Θ : (B.Mat k r → E) → B.Mat k r → E} (P : Prop) [Decidable P] (h : P → BcLoc U Θ) :
    BcLoc U (fun f x => if P then Θ f x else 0) := by
  intro f f' hff x hx hxG
  by_cases hP : P
  · simp only [if_pos hP]; exact h hP f f' hff x hx hxG
  · simp only [if_neg hP]

theorem bcLoc_fold (Ts : List ((B.Mat k r → E) → B.Mat k r → E))
    (hT : ∀ T ∈ Ts, BcLoc U T) : BcLoc U (fun f => Ts.foldr (fun T h => T h) f) := by
  induction Ts with
  | nil => intro f f' hff x hx hxG; exact hff x hx hxG
  | cons T Ts ih =>
    intro f f' hff x hx hxG
    simp only [List.foldr_cons]
    exact hT T (by simp) _ _ (fun y hy hyG => ih (fun T' hT' => hT T' (by simp [hT'])) f f' hff y hy hyG) x hx hxG

theorem bcLoc_top (hU : IsOpen U) (u : ℂ) (a b : Fin (2 * r + k + 1)) :
    BcLoc U (Top (E := E) (Q.EH k r) u a b) := by
  intro f f' hff x hx hxG
  rw [P.CapelliWordSumExpansion.top_apply', P.CapelliWordSumExpansion.top_apply', P.CapelliWordSumExpansion.EH_apply, P.CapelliWordSumExpansion.EH_apply, hff x hx hxG,
    P.CapelliWordSumExpansion.rdV_congr hU hx hxG (P.CapelliWordSumExpansion.Xa_unit a b).1 hff, P.CapelliWordSumExpansion.rdV_congr hU hx hxG (P.CapelliWordSumExpansion.Xb_unit a b).1 hff]

theorem bcLoc_qminor (hU : IsOpen U) {t : ℕ} (p q : Fin t → Fin (2 * r + k + 1)) (u : ℂ) :
    BcLoc U (qminorOp (E := E) (Q.EH k r) p q u) := by
  intro f f' hff x hx hxG
  simp only [qminorOp, Finset.sum_apply, Pi.smul_apply]
  refine Finset.sum_congr rfl fun σ _ => ?_
  congr 1
  refine bcLoc_fold _ (fun T hT => ?_) f f' hff x hx hxG
  simp only [List.mem_ofFn] at hT
  obtain ⟨j, rfl⟩ := hT
  exact bcLoc_top hU _ _ _

theorem bc_tL_local (hU : IsOpen U) (z z' : Fin (2 * r + k + 1) → ℂ) (Y : ℂ) (a b : Fin 2) :
    BcLoc U (Q.tL (E := E) k r z z' 0 Y a b) := by
  have hm : Q.mdim k r 0 = 2 * r + k + 1 := by simp [Q.mdim]
  fin_cases a <;> fin_cases b
  · exact bcLoc_qminor hU _ _ _
  · refine bcLoc_congr (bcLoc_neg (bcLoc_sum (Finset.univ : Finset (Fin (Q.mdim k r 0))) _ fun i _ =>
      bcLoc_sum (Finset.univ : Finset (Fin (Q.mdim k r 0))) _ fun j _ =>
      bcLoc_coef (fun x => (-1 : ℂ) ^ ((i : ℕ) + (j : ℕ)) * Q.ybv k r z 0 x i * Q.xv k r z' 0 j)
        (bcLoc_qminor hU (Q.posL k r 0 ∘ Q.skip1 i) (Q.posL k r 0 ∘ Q.skip1 j) (Q.uC k r 0 Y - 1))))
      (fun f x => rfl)
  · refine bcLoc_congr (bcLoc_neg (bcLoc_sum (Finset.univ : Finset (Fin (Q.mdim k r 0))) _ fun i _ =>
      bcLoc_sum (Finset.univ : Finset (Fin (Q.mdim k r 0))) _ fun j _ =>
      bcLoc_coef (fun x => (-1 : ℂ) ^ ((i : ℕ) + (j : ℕ)) * Q.xbv k r z' 0 i * Q.yv k r z 0 x j)
        (bcLoc_qminor hU (Q.posL k r 0 ∘ Q.skip1 i) (Q.posL k r 0 ∘ Q.skip1 j) (Q.uC k r 0 Y))))
      (fun f x => rfl)
  · refine bcLoc_congr (bcLoc_neg (bcLoc_sum (Finset.univ : Finset (Fin (Q.mdim k r 0))) _ fun i _ =>
      bcLoc_sum (Finset.univ : Finset (Fin (Q.mdim k r 0))) _ fun i' _ =>
      bcLoc_sum (Finset.univ : Finset (Fin (Q.mdim k r 0))) _ fun j _ =>
      bcLoc_sum (Finset.univ : Finset (Fin (Q.mdim k r 0))) _ fun j' _ =>
      bcLoc_ite (i < i' ∧ j < j') fun _ => bcLoc_coef (fun x =>
        ((-1 : ℂ) ^ ((i : ℕ) + (i' : ℕ) + (j : ℕ) + (j' : ℕ)) *
          (Q.ybv k r z 0 x i * Q.xbv k r z' 0 i' - Q.ybv k r z 0 x i' * Q.xbv k r z' 0 i) *
          (Q.yv k r z 0 x j * Q.xv k r z' 0 j' - Q.yv k r z 0 x j' * Q.xv k r z' 0 j)))
        (bcLoc_qminor hU (Q.posL k r 0 ∘ Q.skip2 i i') (Q.posL k r 0 ∘ Q.skip2 j j') (Q.uC k r 0 Y - 1))))
      (fun f x => rfl)

end local_

end Formalism.FourierDecayAlt.P.JCx2

namespace Formalism.FourierDecayAlt.P.JCx2

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF Formalism.FourierDecayAlt.P.BetaSesquilinearity

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section besselModule

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
  {Bs : B.RealPlaceData k r Wp Wq} {ε : ℝ}

theorem bc_integrable {F : B.Mat k r → (Wq →L[ℂ] Wp)} (hF : JC.NiceCoef Bs ε F) {h : B.Mat k r} (hh : h ∈ JF.Om k r Bs.z Bs.z') :
    Integrable (fun p => JF.xiP Bs p • B.rho Bs p F h) Bs.μSS :=
  (Formalism.FourierDecayAlt.P.bessel_integral_converges k r Wp Wq Bs _ F (P5.Rad.thr_big k r 0) (hF.2.1 _ 0)).1 h hh

theorem bc_JF_zero (h : B.Mat k r) : B.JF Bs (fun _ => (0 : Wq →L[ℂ] Wp)) h = 0 := by
  show ∫ p, JF.xiP Bs p • B.rho Bs p (fun _ => (0 : Wq →L[ℂ] Wp)) h ∂Bs.μSS = 0
  simp [B.rho]

theorem bc_JF_add {F G : B.Mat k r → (Wq →L[ℂ] Wp)} (hF : JC.NiceCoef Bs ε F) (hG : JC.NiceCoef Bs ε G)
    {h : B.Mat k r} (hh : h ∈ JF.Om k r Bs.z Bs.z') :
    B.JF Bs (fun g => F g + G g) h = B.JF Bs F h + B.JF Bs G h := by
  show ∫ p, JF.xiP Bs p • B.rho Bs p (fun g => F g + G g) h ∂Bs.μSS =
    ∫ p, JF.xiP Bs p • B.rho Bs p F h ∂Bs.μSS + ∫ p, JF.xiP Bs p • B.rho Bs p G h ∂Bs.μSS
  rw [← integral_add (bc_integrable hF hh) (bc_integrable hG hh)]
  congr 1
  funext p
  simp [B.rho, ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add, smul_add]

theorem bc_JF_smul (c : ℂ) (F : B.Mat k r → (Wq →L[ℂ] Wp)) (h : B.Mat k r) :
    B.JF Bs (fun g => c • F g) h = c • B.JF Bs F h := by
  show ∫ p, JF.xiP Bs p • B.rho Bs p (fun g => c • F g) h ∂Bs.μSS = c • ∫ p, JF.xiP Bs p • B.rho Bs p F h ∂Bs.μSS
  rw [← integral_smul]
  congr 1
  funext p
  simp only [B.rho, ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul]
  exact smul_comm _ _ _

theorem bc_JF_sum {ι : Type*} (s : Finset ι) (G : ι → B.Mat k r → (Wq →L[ℂ] Wp))
    (hG : ∀ i ∈ s, JC.NiceCoef Bs ε (G i)) {h : B.Mat k r} (hh : h ∈ JF.Om k r Bs.z Bs.z') :
    B.JF Bs (∑ i ∈ s, G i) h = ∑ i ∈ s, B.JF Bs (G i) h := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty]
    exact bc_JF_zero h
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    have e : (G a + ∑ i ∈ s, G i) = fun g => G a g + (∑ i ∈ s, G i) g := rfl
    rw [e, bc_JF_add (hG a (Finset.mem_insert_self a s))
      (mn_nice_sum' s G fun i hi => hG i (Finset.mem_insert_of_mem hi)) hh,
      ih fun i hi => hG i (Finset.mem_insert_of_mem hi)]

def BcGood (Bs : B.RealPlaceData k r Wp Wq) (ε : ℝ) (Θ : D.Op (B.Mat k r → (Wq →L[ℂ] Wp))) : Prop :=
  mnNP Bs ε Θ ∧ (∀ F, JC.NiceCoef Bs ε F → ∀ h ∈ JF.Om k r Bs.z Bs.z', B.JF Bs (Θ F) h = Θ (B.JF Bs F) h) ∧
    BcLoc (Q.OmPlus k r Bs.z Bs.z') Θ

theorem bcGood_closed : mnClosed (BcGood Bs ε) where
  zero := ⟨fun _ _ => mn_nice_zero, fun _ _ h _ => bc_JF_zero h, fun _ _ _ _ _ _ => rfl⟩
  one := ⟨fun _ hF => hF, fun _ _ _ _ => rfl, fun _ _ hff x hx hxG => hff x hx hxG⟩
  add := fun a b ha hb => ⟨fun F hF => mn_nice_add (ha.1 F hF) (hb.1 F hF),
    fun F hF h hh => by
      show B.JF Bs (fun g => a F g + b F g) h = a (B.JF Bs F) h + b (B.JF Bs F) h
      rw [bc_JF_add (ha.1 F hF) (hb.1 F hF) hh, ha.2.1 F hF h hh, hb.2.1 F hF h hh],
    fun f f' hff x hx hxG => by
      show a f x + b f x = a f' x + b f' x
      rw [ha.2.2 f f' hff x hx hxG, hb.2.2 f f' hff x hx hxG]⟩
  mul := fun a b ha hb => ⟨fun F hF => ha.1 _ (hb.1 F hF),
    fun F hF h hh => by
      show B.JF Bs (a (b F)) h = a (b (B.JF Bs F)) h
      rw [ha.2.1 _ (hb.1 F hF) h hh]
      exact ha.2.2 _ _ (fun x hx hxG => hb.2.1 F hF x ⟨hxG, hx⟩) h hh.2 hh.1,
    fun f f' hff x hx hxG => ha.2.2 _ _ (fun y hy hyG => hb.2.2 f f' hff y hy hyG) x hx hxG⟩
  cop := fun c => ⟨fun _ hF => mn_nice_smul c hF, fun F _ h _ => bc_JF_smul c F h,
    fun f f' hff x hx hxG => by
      show c • f x = c • f' x
      rw [hff x hx hxG]⟩

theorem bcGood_tL (s : ℂ) (Y : ℂ) (a b : Fin 2) :
    BcGood Bs ε (fun f => s • Q.tL k r Bs.z Bs.z' 0 Y a b f) := by
  refine ⟨fun F hF => mn_nice_smul s (mn_tL_nice Bs ε F Y a b hF), fun F hF h hh => ?_, ?_⟩
  · show B.JF Bs (fun g => s • Q.tL k r Bs.z Bs.z' 0 Y a b F g) h = s • Q.tL k r Bs.z Bs.z' 0 Y a b (B.JF Bs F) h
    rw [bc_JF_smul, bc_tL_bessel Bs hF.1 _ (2 * r + k + 1) le_rfl (P5.Rad.thr_big k r _) (hF.2.1 _ _) Y a b hh]
  · intro f f' hff x hx hxG
    show s • Q.tL k r Bs.z Bs.z' 0 Y a b f x = s • Q.tL k r Bs.z Bs.z' 0 Y a b f' x
    rw [bc_tL_local (P.SmoothnessOnGoodSet.isOpen_OmPlus _ _) Bs.z Bs.z' Y a b f f' hff x hx hxG]

theorem bc_core {Sl : Type} [Fintype Sl] [DecidableEq Sl] (RR : Wd.SlopeTestRemainingChoices Sl (D.Op (B.Mat k r → (Wq →L[ℂ] Wp))))
    (hR : ∀ a b, BcGood Bs ε (RR a b)) (F : Wd.Ix Sl → B.Mat k r → (Wq →L[ℂ] Wp))
    (hF : ∀ b, JC.NiceCoef Bs ε (F b)) (a : Wd.Ix Sl) {h : B.Mat k r} (hh : h ∈ JF.Om k r Bs.z Bs.z') :
    B.JF Bs (D.actOp RR F a) h = D.actOp RR (fun b => B.JF Bs (F b)) a h := by
  show B.JF Bs (∑ b, D.ap (RR a b) (F b)) h = (∑ b, D.ap (RR a b) (B.JF Bs (F b))) h
  rw [bc_JF_sum Finset.univ (fun b => D.ap (RR a b) (F b)) (fun b _ => (hR a b).1 (F b) (hF b)) hh,
    Finset.sum_apply]
  exact Finset.sum_congr rfl fun b _ => (hR a b).2.1 (F b) (hF b) _ hh

end besselModule

end Formalism.FourierDecayAlt.P.JCx2

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P.JCx2

theorem bessel_module : Formalism.FourierDecayAlt.JC.BesselModule := by
  intro Wp Wq _ _ _ _ _ _ P0 T s j w F ε _hε hF a y hy
  have hQQ : ∀ Y p q, BcGood (T.bs j) ε (D.QQlev T s j Y p q) := fun Y p q => bcGood_tL s Y p q
  have hR := mn_rrop_closure bcGood_closed (D.QQlev T s j) hQQ (D.positionted w)
  have hGV : Q.wCell (JC.parLev P0 j).k (JC.parLev P0 j).r (Fin.last _) y.1 * y.2 ∈
      B.GV (JC.parLev P0 j).k (JC.parLev P0 j).r := by
    rw [P5.Rad.wCell_last_eq]
    exact P.BetaSesquilinearity.gv_mul (big_cell_mem_holds _ _ _ 1 hy.1 (by simp)) hy.2.1.1
  have hh : Q.wCell (JC.parLev P0 j).k (JC.parLev P0 j).r (Fin.last _) y.1 * y.2 ∈
      JF.Om (JC.parLev P0 j).k (JC.parLev P0 j).r (T.bs j).z (T.bs j).z' :=
    ⟨hGV, P5.Rad.wCell_mem_omPlus (T.bs j).z_mem (T.bs j).z'_mem hy.1 hy.2.1 hy.2.2⟩
  simp only [Q.resG]
  congr 1
  exact bc_core (D.RRlev T s j w) hR F hF a hh

end Formalism.FourierDecayAlt.P

end

section

open Matrix Filter Topology
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.JCx2

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section rma

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
  {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}

theorem rma_isDom_omPlus (hz : inWb k r z) (hz' : inWb k r z') : IsDom k r z z' 0 (OmPlus k r z z') := by
  refine ⟨P.SmoothnessOnGoodSet.isOpen_OmPlus z z', ?_⟩
  rintro g ⟨-, hg⟩ s ⟨h, hh, m, hm, rfl⟩ s' ⟨h', hh', m', hm', rfl⟩
  have hs : h * m ∈ Sset k r z := ⟨h, hh, m, hm.1, rfl⟩
  have hs' : h' * m' ∈ Sset k r z' := ⟨h', hh', m', hm'.1, rfl⟩
  have hD : ∀ l, Dmin k r z z' (h * m * g * (h' * m')) l = Dmin k r z z' g l :=
    fun l => dInv k r z z' hz hz' _ hs _ hs' g l
  refine ⟨fun l hl => by rw [hD]; exact hg.1 l hl, ?_⟩
  have e : Gf k r z z' (h * m * g * (h' * m')) = Gf k r z z' g := by
    unfold Gf
    rw [hD, hD]
  rw [e]
  exact hg.2

variable (k r z z' π π') in

def rma_K : Submodule ℂ (Mx k r → (Wq →L[ℂ] Wp)) where
  carrier := FFl k r z z' π π' 0 (OmPlus k r z z')
  zero_mem' := P.Qx8.FFl_zero
  add_mem' := fun hJ hJ' => P.Qx8.FFl_add hJ hJ'
  smul_mem' := fun a _ hJ => P.Qx8.FFl_smul hJ a

theorem rma_resG_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (i : Fin (r + 1)) (s : ℂ)
    (J : Mx k r → E) (c : Fin r → ℂ) (g : Mx k r) :
    resG k r i (s • J) c g = s • resG k r i J c g := by
  simp only [resG, Pi.smul_apply]
  rw [smul_comm]

theorem rma_resG_add {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (i : Fin (r + 1))
    (J J' : Mx k r → E) (c : Fin r → ℂ) (g : Mx k r) :
    resG k r i (J + J') c g = resG k r i J c g + resG k r i J' c g := by
  simp only [resG, Pi.add_apply, smul_add]

variable (z z') in
open Classical in

def rma_resFn (J : Mx k r → (Wq →L[ℂ] Wp)) : Fn k r (Wq →L[ℂ] Wp) := fun c g =>
  if (c, g) ∈ DomR k r z z' then resG k r (Fin.last r) J c g else 0

theorem rma_resFn_of_mem (J : Mx k r → (Wq →L[ℂ] Wp)) {y : (Fin r → ℂ) × Mx k r} (hy : y ∈ DomR k r z z') :
    rma_resFn z z' J y.1 y.2 = resG k r (Fin.last r) J y.1 y.2 := by
  unfold rma_resFn
  rw [if_pos (by simpa using hy)]

theorem rma_resFn_mem (hz : inWb k r z) (hz' : inWb k r z') (J : Mx k r → (Wq →L[ℂ] Wp))
    (hJ : J ∈ FFl k r z z' π π' 0 (OmPlus k r z z')) : rma_resFn z z' J ∈ RadSp k r z z' π π' := by
  classical
  have hsm := Formalism.FourierDecayAlt.P5.Rad.sf_resG hJ.1
  refine ⟨fun x hx => ?_, fun x₀ hx₀ => ?_, fun x hx h hh h' hh' => ?_⟩
  · show (if (x.1, x.2) ∈ DomR k r z z' then resG k r (Fin.last r) J x.1 x.2 else 0) = 0
    rw [if_neg (by rw [Prod.mk.eta]; exact hx)]
  · obtain ⟨U, Fe, hU, hxU, hFe, hΦ⟩ := hsm x₀
      ⟨hx₀.1, Formalism.FourierDecayAlt.P5.Rad.wCell_mem_omPlus hz hz' hx₀.1 hx₀.2.1 hx₀.2.2⟩ hx₀.2.1
    have hV : IsOpen {x : (Fin r → ℂ) × Mx k r | x.1 ∈ OmX r ∧ 0 < GGl k r z z' x.2} :=
      ((P.Qx3.isOpen_OmX r).preimage continuous_fst).inter
        (isOpen_lt continuous_const ((P.Qx5.GGl_continuous k r z z').comp continuous_snd))
    refine ⟨U ∩ {x | x.1 ∈ OmX r ∧ 0 < GGl k r z z' x.2}, Fe, hU.inter hV,
      ⟨hxU, hx₀.1, hx₀.2.2⟩, hFe.mono Set.inter_subset_left, fun x hx hxG => ?_⟩
    have hxD : (x.1, x.2) ∈ DomR k r z z' := ⟨hx.2.1, hxG, hx.2.2⟩
    show (if (x.1, x.2) ∈ DomR k r z z' then resG k r (Fin.last r) J x.1 x.2 else 0) = _
    rw [if_pos hxD]
    exact hΦ x hx.1 hxG
  · have hx' : (x.1, x.2) ∈ DomR k r z z' := by simpa using hx
    show (if (x.1, h * x.2 * h') ∈ DomR k r z z' then resG k r (Fin.last r) J x.1 (h * x.2 * h') else 0) =
      (π h).comp ((if (x.1, x.2) ∈ DomR k r z z' then resG k r (Fin.last r) J x.1 x.2 else 0).comp (π' h'))
    rw [if_pos (Formalism.FourierDecayAlt.P5.Rad.domR_uw hx hh hh'), if_pos hx']
    unfold resG
    have e : wCell k r (Fin.last r) x.1 * (h * x.2 * h') =
        h * (wCell k r (Fin.last r) x.1 * x.2) * h' := by
      have hc := P.Qx3.wlist_comm (k := k) (Fin.last r) x.1
        ((List.finRange r).filter fun a => a.val < (Fin.last r).val)
        (fun a _ => a.isLt) (P.Qx3.uw_glev (Fin.last r) hh)
      change wCell k r (Fin.last r) x.1 * h = h * wCell k r (Fin.last r) x.1 at hc
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hc, Matrix.mul_assoc h]
    have hw : wCell k r (Fin.last r) x.1 * x.2 ∈ Glev k r 0 ∩ OmPlus k r z z' :=
      ⟨P.Qx3.glev_mul (P.Qx3.wlist_glev hx.1 _) (P.Qx3.glev_mono (Fin.zero_le _) hx.2.1),
        Formalism.FourierDecayAlt.P5.Rad.wCell_mem_omPlus hz hz' hx.1 hx.2.1 hx.2.2⟩
    rw [e, hJ.2.2.2 _ hw h hh h' hh']
    ext v
    simp

def rma_resK (hz : inWb k r z) (hz' : inWb k r z') :
    rma_K k r z z' π π' →ₗ[ℂ] RadSp k r z z' π π' where
  toFun J := ⟨rma_resFn z z' J.1, rma_resFn_mem hz hz' J.1 J.2⟩
  map_add' J J' := by
    apply Subtype.ext
    funext c g
    show rma_resFn z z' (J.1 + J'.1) c g = rma_resFn z z' J.1 c g + rma_resFn z z' J'.1 c g
    unfold rma_resFn
    split_ifs
    · exact rma_resG_add _ _ _ _ _
    · simp
  map_smul' a J := by
    apply Subtype.ext
    funext c g
    show rma_resFn z z' (a • J.1) c g = a • rma_resFn z z' J.1 c g
    unfold rma_resFn
    split_ifs
    · exact rma_resG_smul _ _ _ _ _
    · simp

def rma_res (hz : inWb k r z) (hz' : inWb k r z') :
    (Mx k r → (Wq →L[ℂ] Wp)) →ₗ[ℂ] RadSp k r z z' π π' :=
  (rma_resK hz hz').comp (Submodule.projectionOnto _ _
    (Submodule.exists_isCompl (rma_K k r z z' π π')).choose_spec)

theorem rma_res_apply (hz : inWb k r z) (hz' : inWb k r z') (J : Mx k r → (Wq →L[ℂ] Wp))
    (hJ : J ∈ rma_K k r z z' π π') {y : (Fin r → ℂ) × Mx k r} (hy : y ∈ DomR k r z z') :
    ((rma_res hz hz' J : RadSp k r z z' π π') : Fn k r (Wq →L[ℂ] Wp)) y.1 y.2 =
      resG k r (Fin.last r) J y.1 y.2 := by
  have e : rma_res (π := π) (π' := π') hz hz' J = rma_resK hz hz' ⟨J, hJ⟩ := by
    unfold rma_res
    rw [LinearMap.comp_apply]
    congr 1
    exact Submodule.projectionOnto_apply_left _ ⟨J, hJ⟩
  rw [e]
  exact rma_resFn_of_mem J hy

variable (V : Type) [AddCommGroup V] [Module ℂ V] in

def rma_fst : Pr V →ₐ[ℂ] Module.End ℂ V where
  toFun x := x.1
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

theorem rma_fst_mkP {V : Type} [AddCommGroup V] [Module ℂ V] (A B : Module.End ℂ V) : rma_fst V (mkP A B) = A := rfl

theorem rma_star_alg {V : Type} [AddCommGroup V] [Module ℂ V] (w : ℂ) :
    star (algebraMap ℂ (Pr V) w) = algebraMap ℂ (Pr V) (star w) := by
  rw [P.Qx8.algebraMap_Pr, P.Qx8.algebraMap_Pr, P.Qx8.star_mkPair, star_star]

variable (k r z z') in

def rma_Loc {E : Type*} (N : OM (Fn k r E)) : Prop :=
  ∀ a b (f₁ f₂ : Fn k r E), (∀ y ∈ DomR k r z z', f₁ y.1 y.2 = f₂ y.1 y.2) →
    ∀ y ∈ DomR k r z z', N a b f₁ y.1 y.2 = N a b f₂ y.1 y.2

def rma_Rel (M : Matrix (Fin 2) (Fin 2) (Pr (RadSp k r z z' π π'))) (N : OM (Fn k r (Wq →L[ℂ] Wp))) : Prop :=
  ∀ a b (Ψ : RadSp k r z z' π π'), ∀ y ∈ DomR k r z z',
    ((rma_fst _ (M a b) Ψ : RadSp k r z z' π π') : Fn k r (Wq →L[ℂ] Wp)) y.1 y.2 = N a b (Ψ : Fn k r _) y.1 y.2

theorem rma_crd_loc {E : Type*} (R : ((Fin r → ℂ) → E) → (Fin r → ℂ) → E)
    (hR : ∀ f₁ f₂ c, c ∈ OmX r → (∀ c' ∈ OmX r, f₁ c' = f₂ c') → R f₁ c = R f₂ c) (f₁ f₂ : Fn k r E)
    (h : ∀ y ∈ DomR k r z z', f₁ y.1 y.2 = f₂ y.1 y.2) :
    ∀ y ∈ DomR k r z z', crd R f₁ y.1 y.2 = crd R f₂ y.1 y.2 := by
  intro y hy
  exact hR _ _ y.1 hy.1 (fun c' hc' => h (c', y.2) ⟨hc', hy.2.1, hy.2.2⟩)

theorem rma_eq_nhds {E : Type*} {f₁ f₂ : (Fin r → ℂ) → E} {c : Fin r → ℂ} (hc : c ∈ OmX r)
    (h : ∀ c' ∈ OmX r, f₁ c' = f₂ c') : f₁ =ᶠ[𝓝 c] f₂ :=
  Filter.eventuallyEq_of_mem ((P.Qx3.isOpen_OmX r).mem_nhds hc) h

theorem rma_TL_loc {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (l : Fin r) (Y : ℂ) :
    rma_Loc k r z z' (TL (E := E) k l Y) := by
  intro a b f₁ f₂ h
  refine rma_crd_loc (Tmat l Y a b) ?_ f₁ f₂ h
  intro g₁ g₂ c hc hg
  have h0 : g₁ c = g₂ c := hg c hc
  have he := rma_eq_nhds hc hg
  fin_cases a <;> fin_cases b <;> simp [Tmat, pOp, wirt, cOp, ciOp, h0, he.fderiv_eq]

theorem rma_TLs_loc {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (l : Fin r) (Y : ℂ) :
    rma_Loc k r z z' (TLs (E := E) k l Y) := by
  intro a b f₁ f₂ h
  refine rma_crd_loc (TmatStar l Y a b) ?_ f₁ f₂ h
  intro g₁ g₂ c hc hg
  have h0 : g₁ c = g₂ c := hg c hc
  have he := rma_eq_nhds hc hg
  fin_cases a <;> fin_cases b <;> simp [TmatStar, pbOp, wirtBar, cbOp, cbiOp, h0, he.fderiv_eq]

end rma

end Formalism.FourierDecayAlt.P.JCx2

namespace Formalism.FourierDecayAlt.P.JCx2

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section rma2

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
  {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}

theorem rma_T_fst (X : ActualOps k r z z' π π') (L : R.LevelData (Pr (RadSp k r z z' π π')) r)
    (hL : IsActualLevel X L) (l : Fin r) (Y : ℂ) (a b : Fin 2) (Ψ : RadSp k r z z' π π') :
    ((rma_fst _ (Wd.Ts (P5.site L l) Y a b) Ψ : RadSp k r z z' π π') : Fn k r (Wq →L[ℂ] Wp)) =
      TL k l Y a b (Ψ : Fn k r (Wq →L[ℂ] Wp)) := by
  obtain ⟨hp, -, hc, hci, -⟩ := hL
  funext c g
  fin_cases a <;> fin_cases b <;>
    simp [Wd.Ts, YangianSpanCharacter.T.Tm, P5.site, hp l, hc l, hci l, rma_fst_mkP, TL, crd, Tmat, X.op_apply, opL]

theorem rma_Ts_fst (X : ActualOps k r z z' π π') (L : R.LevelData (Pr (RadSp k r z z' π π')) r)
    (hL : IsActualLevel X L) (l : Fin r) (Y : ℂ) (a b : Fin 2) (Ψ : RadSp k r z z' π π') :
    ((rma_fst _ ((Wd.Ts (P5.site L l) (star Y))ᴴ a b) Ψ : RadSp k r z z' π π') : Fn k r (Wq →L[ℂ] Wp)) =
      TLs k l Y a b (Ψ : Fn k r (Wq →L[ℂ] Wp)) := by
  obtain ⟨hp, -, hc, hci, -⟩ := hL
  funext c g
  fin_cases a <;> fin_cases b <;>
    simp [Matrix.conjTranspose_apply, Wd.Ts, YangianSpanCharacter.T.Tm, P5.site, hp l, hc l, hci l, rma_fst_mkP, rma_star_alg,
      P.Qx8.star_mkPair, TLs, crd, TmatStar, X.op_apply, opL, sub_eq_add_neg]

end rma2

end Formalism.FourierDecayAlt.P.JCx2

namespace Formalism.FourierDecayAlt.P.JCx2

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section rma3

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
  {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}

theorem rma_step (X : ActualOps k r z z' π π') (L : R.LevelData (Pr (RadSp k r z z' π π')) r)
    (hL : IsActualLevel X L) (l : Fin r) (Y : ℂ)
    {M : Matrix (Fin 2) (Fin 2) (Pr (RadSp k r z z' π π'))} {N : OM (Fn k r (Wq →L[ℂ] Wp))}
    (hR : rma_Rel M N) (hN : rma_Loc k r z z' N) :
    rma_Rel ((Wd.Ts (P5.site L l) (star Y))ᴴ * M * Wd.Ts (P5.site L l) Y)
        (oMul (TLs k l Y) (oMul N (TL k l Y))) ∧
      rma_Loc k r z z' (oMul (TLs k l Y) (oMul N (TL k l Y))) := by
  constructor
  · intro a b Ψ y hy
    have e1 : rma_fst _ (((Wd.Ts (P5.site L l) (star Y))ᴴ * M * Wd.Ts (P5.site L l) Y) a b) Ψ =
        ∑ c, rma_fst _ ((Wd.Ts (P5.site L l) (star Y))ᴴ a c)
          (∑ d, rma_fst _ (M c d) (rma_fst _ (Wd.Ts (P5.site L l) Y d b) Ψ)) := by
      simp only [Matrix.mul_apply, map_sum, map_mul, Finset.sum_mul, LinearMap.sum_apply, Module.End.mul_apply]
      first | rfl | exact Finset.sum_comm
    rw [e1]
    simp only [Submodule.coe_sum, Finset.sum_apply, oMul]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [rma_Ts_fst X L hL l Y a c]
    refine rma_TLs_loc l Y a c _ _ (fun y' hy' => ?_) y hy
    simp only [Submodule.coe_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [hR c d _ y' hy', rma_T_fst X L hL l Y d b]
  · intro a b f₁ f₂ h y hy
    simp only [oMul, Finset.sum_apply]
    refine Finset.sum_congr rfl fun c _ => ?_
    refine rma_TLs_loc l Y a c _ _ (fun y' hy' => ?_) y hy
    simp only [Finset.sum_apply]
    refine Finset.sum_congr rfl fun d _ => ?_
    exact hN c d _ _ (rma_TL_loc l Y d b f₁ f₂ h) y' hy'

def rma_pref (L : R.LevelData (Pr (RadSp k r z z' π π')) r) (Y : ℂ) :
    ℕ → Matrix (Fin 2) (Fin 2) (Pr (RadSp k r z z' π π'))
  | 0 => 1
  | n + 1 => if h : n < r then Wd.Ts (P5.site L ⟨n, h⟩) Y * rma_pref L Y n else rma_pref L Y n

theorem rma_tprod_pref (L : R.LevelData (Pr (RadSp k r z z' π π')) r) (Y : ℂ) :
    ∀ m i, i + m = r → P5.tprod L Y i * rma_pref L Y i = rma_pref L Y r
  | 0, i, h => by
    have hi : i = r := by omega
    rw [hi, P5.tprod, dif_neg (lt_irrefl r), Matrix.one_mul]
  | m + 1, i, h => by
    have hi : i < r := by omega
    have e : rma_pref L Y (i + 1) = Wd.Ts (P5.site L ⟨i, hi⟩) Y * rma_pref L Y i := by
      simp only [rma_pref, dif_pos hi]
    rw [P5.tprod, dif_pos hi, Matrix.mul_assoc, ← e]
    exact rma_tprod_pref L Y m (i + 1) (by omega)

theorem rma_sandw (X : ActualOps k r z z' π π') (L : R.LevelData (Pr (RadSp k r z z' π π')) r)
    (hL : IsActualLevel X L) (Y : ℂ) :
    ∀ n, n ≤ r → ∀ (M : Matrix (Fin 2) (Fin 2) (Pr (RadSp k r z z' π π'))) (N : OM (Fn k r (Wq →L[ℂ] Wp))),
      rma_Rel M N → rma_Loc k r z z' N →
      rma_Rel ((rma_pref L (star Y) n)ᴴ * M * rma_pref L Y n) (sandw k r Y n N) ∧
        rma_Loc k r z z' (sandw k r Y n N)
  | 0, _, M, N, hR, hN => by
    simp only [rma_pref, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one, sandw]
    exact ⟨hR, hN⟩
  | n + 1, hn, M, N, hR, hN => by
    have h : n < r := by omega
    obtain ⟨hR', hN'⟩ := rma_step X L hL ⟨n, h⟩ Y hR hN
    have ih := rma_sandw X L hL Y n (by omega) _ _ hR' hN'
    have e1 : sandw k r Y (n + 1) N =
        sandw k r Y n (oMul (TLs k ⟨n, h⟩ Y) (oMul N (TL k ⟨n, h⟩ Y))) := by
      simp only [sandw, dif_pos h]
    have e2 : (rma_pref L (star Y) (n + 1))ᴴ * M * rma_pref L Y (n + 1) =
        (rma_pref L (star Y) n)ᴴ * ((Wd.Ts (P5.site L ⟨n, h⟩) (star Y))ᴴ * M * Wd.Ts (P5.site L ⟨n, h⟩) Y) *
          rma_pref L Y n := by
      simp only [rma_pref, dif_pos h, Matrix.conjTranspose_mul, Matrix.mul_assoc]
    rw [e1, e2]
    exact ih

theorem rma_base (X : ActualOps k r z z' π π') (Y : ℂ) : rma_Rel (X.QQ Y) (QL k r z z' (Fin.last r) Y) := by
  intro a b Ψ y hy
  show ((X.t Y a b Ψ : RadSp k r z z' π π') : Fn k r (Wq →L[ℂ] Wp)) y.1 y.2 = _
  rw [X.t_apply Y a b Ψ y hy]
  rfl

theorem rma_QL_loc {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (Y : ℂ) :
    rma_Loc k r z z' (QL (E := E) k r z z' (Fin.last r) Y) := by
  intro a b f₁ f₂ h y hy
  exact (P.Qx2.ll_tL (E := E) (i := Fin.last r) (P.Qx8.Dp_open k r z z') z z' Y a b).loc (f₁ y.1) (f₂ y.1)
    (fun g hg => h (y.1, g) ⟨hy.1, hg.1, hg.2⟩) y.2 ⟨hy.2.1, hy.2.2⟩

theorem rma_QQi (X : ActualOps k r z z' π π') (L : R.LevelData (Pr (RadSp k r z z' π π')) r)
    (hL : IsActualLevel X L) (st : Fr.Start (Pr (RadSp k r z z' π π'))) (s : ℂ)
    (hst : ∀ Y, st.QQ Y = s • X.QQ Y) (Y : ℂ) (a b : Fin 2) (Ψ : RadSp k r z z' π π')
    {y : (Fin r → ℂ) × Mx k r} (hy : y ∈ DomR k r z z') :
    ((rma_fst _ (P5.QQi L st 0 Y a b) Ψ : RadSp k r z z' π π') : Fn k r (Wq →L[ℂ] Wp)) y.1 y.2 =
      s • sandw k r Y r (QL k r z z' (Fin.last r) Y) a b (Ψ : Fn k r (Wq →L[ℂ] Wp)) y.1 y.2 := by
  have hT0 : ∀ Y', P5.tprod L Y' 0 = rma_pref L Y' r := fun Y' => by
    have := rma_tprod_pref L Y' r 0 (by omega)
    simpa [rma_pref] using this
  have hQ : P5.QQi L st 0 Y = s • ((rma_pref L (star Y) r)ᴴ * X.QQ Y * rma_pref L Y r) := by
    simp only [P5.QQi, Fin.val_zero]
    rw [hT0, hT0, hst, Matrix.mul_smul, Matrix.smul_mul]
  rw [hQ, Matrix.smul_apply, map_smul, LinearMap.smul_apply, Submodule.coe_smul, Pi.smul_apply, Pi.smul_apply]
  congr 1
  exact (rma_sandw X L hL Y r le_rfl _ _ (rma_base X Y) (rma_QL_loc Y)).1 a b Ψ y hy

variable (k r z z') in

def rma_Qop (s : ℂ) : ℂ → Wd.M2 (D.Op (Mx k r → (Wq →L[ℂ] Wp))) := fun Y =>
  Matrix.of fun a b => (fun f => s • tL k r z z' 0 Y a b f : D.Op (Mx k r → (Wq →L[ℂ] Wp)))

theorem rma_main (hz : inWb k r z) (hz' : inWb k r z') (X : ActualOps k r z z' π π')
    (L : R.LevelData (Pr (RadSp k r z z' π π')) r) (st : Fr.Start (Pr (RadSp k r z z' π π'))) (s : ℂ)
    (hL : IsActualLevel X L) (hst : ∀ Y, st.QQ Y = s • X.QQ Y) {S : Type} [Fintype S] [DecidableEq S]
    (w : List (Wd.Letter ℂ S)) (x : Wd.Ix S → Mx k r → (Wq →L[ℂ] Wp)) (Φ : Wd.Ix S → RadSp k r z z' π π')
    (hx : ∀ a, x a ∈ FFl k r z z' π π' 0 (OmPlus k r z z'))
    (hΦ : ∀ a, ∀ y ∈ DomR k r z z',
      (Φ a : Fn k r (Wq →L[ℂ] Wp)) y.1 y.2 = resG k r (Fin.last r) (x a) y.1 y.2) :
    ∀ a, ∀ y ∈ DomR k r z z', (P5.act (P5.RRi L st 0 w) Φ a : Fn k r (Wq →L[ℂ] Wp)) y.1 y.2 =
      resG k r (Fin.last r) (D.actOp (D.RRop (rma_Qop k r z z' s) w) x a) y.1 y.2 := by
  intro a y hy
  have hDom := rma_isDom_omPlus hz hz'
  have hyp : ∀ (Y : ℂ) (a b : Fin 2), ∀ J ∈ rma_K k r z z' π π',
      D.ap (rma_Qop k r z z' s Y a b) J ∈ rma_K k r z z' π π' ∧
        rma_res hz hz' (D.ap (rma_Qop k r z z' s Y a b) J) =
          rma_fst _ (P5.QQi L st 0 Y a b) (rma_res hz hz' J) := by
    intro Y a b J hJ
    have hmem : D.ap (rma_Qop k r z z' s Y a b) J ∈ rma_K k r z z' π π' :=
      P.Qx8.FFl_smul (P.operator_preserves_fusion_forms Wp Wq k r z z' π π' 0 _ Y a b hz hz' hDom J hJ) s
    refine ⟨hmem, P.Qx8.rad_ext fun y hy => ?_⟩
    rw [rma_res_apply hz hz' _ hmem hy, rma_QQi X L hL st s hst Y a b _ hy]
    show resG k r (Fin.last r) (s • tL k r z z' 0 Y a b J) y.1 y.2 = _
    have hc := P.chain_recursion_all_levels Wp Wq k r z z' π π' (Fin.last r) _ Y a b hz hz' hDom J hJ y.1 hy.1 y.2
      hy.2.1 (Formalism.FourierDecayAlt.P5.Rad.wCell_mem_omPlus hz hz' hy.1 hy.2.1 hy.2.2)
    rw [Fin.val_last] at hc
    rw [rma_resG_smul, hc]
    congr 1
    exact (rma_sandw X L hL Y r le_rfl _ _ (rma_base X Y) (rma_QL_loc Y)).2 a b _ _
      (fun y' hy' => (rma_res_apply hz hz' J hJ hy').symm) y hy
  have key := P.module_of_words (Mx k r → (Wq →L[ℂ] Wp)) (rma_K k r z z' π π') (RadSp k r z z' π π')
    (rma_res hz hz') (Pr (RadSp k r z z' π π')) S (rma_fst _) (rma_Qop k r z z' s) (P5.QQi L st 0) hyp w x hx
  obtain ⟨hmem, heq⟩ := key a
  have hΦres : ∀ b, Φ b = rma_res hz hz' (x b) := fun b => P.Qx8.rad_ext fun y hy => by
    rw [rma_res_apply hz hz' _ (hx b) hy]
    exact hΦ b y hy
  have e : P5.act (P5.RRi L st 0 w) Φ a = rma_res hz hz' (D.actOp (D.RRop (rma_Qop k r z z' s) w) x a) := by
    rw [heq]
    simp only [P5.act, P5.RRi, hΦres]
    rfl
  rw [e, rma_res_apply hz hz' _ hmem hy]

end rma3

end Formalism.FourierDecayAlt.P.JCx2

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt

theorem radial_module_action : Formalism.FourierDecayAlt.JC.RadialModuleAct := by
  intro Wp Wq _ _ _ _ _ _ P0 T j X μ L st l0 hD w x Φ hx hΦ a y hy
  exact JCx2.rma_main (T.bs j).z_mem (T.bs j).z'_mem X L st (M.sgn P0 l0) hD.2.2.1 hD.2.2.2.1 (D.positionted w) x Φ
    hx hΦ a y hy

end Formalism.FourierDecayAlt.P

end

section

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Matrix

namespace Formalism.FourierDecayAlt.P.JCx2

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section sqQuant

variable {k r : ℕ} (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

def sqGood (d : ℕ) (c : Mat k r → ℂ) : Prop :=
  (∀ F : Mat k r → (Wq →L[ℂ] Wp), CkOn (⊤ : ℕ∞) (GV k r) F → CkOn (⊤ : ℕ∞) (GV k r) (fun g => c g • F g)) ∧
  ∀ (A : ℝ) (m : ℕ) (F : Mat k r → (Wq →L[ℂ] Wp)), InCC (A + d) m F → InCC A m (fun g => c g • F g)

def sqOp (d o : ℕ) (Θ : (Mat k r → (Wq →L[ℂ] Wp)) → Mat k r → (Wq →L[ℂ] Wp)) : Prop :=
  (∀ F, CkOn (⊤ : ℕ∞) (GV k r) F → CkOn (⊤ : ℕ∞) (GV k r) (Θ F)) ∧
  ∀ (A : ℝ) (m : ℕ) (F : Mat k r → (Wq →L[ℂ] Wp)), CkOn (⊤ : ℕ∞) (GV k r) F → InCC (A + d) (m + o) F →
    InCC A m (Θ F)

variable {Wp Wq}

theorem sq_inCC_mono {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {A A' : ℝ} {m m' : ℕ}
    (hA : A ≤ A') (hm : m ≤ m') {F : Mat k r → E} (h : InCC A' m' F) : InCC A m F :=
  Formalism.FourierDecayAlt.P.BetaSesquilinearity.sInCC_mono hA hm h

theorem sq_inCC_add {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {A : ℝ} {m : ℕ}
    {F F' : Mat k r → E} (h : InCC A m F) (h' : InCC A m F') : InCC A m (fun g => F g + F' g) := by
  obtain ⟨c, hc⟩ := h
  obtain ⟨c', hc'⟩ := h'
  exact ⟨c + c', Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_add hc hc'⟩

theorem sq_inCC_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {A : ℝ} {m : ℕ} (a : ℂ)
    {F : Mat k r → E} (h : InCC A m F) : InCC A m (fun g => a • F g) := by
  obtain ⟨c, hc⟩ := h
  exact ⟨_, Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_smul a hc⟩

theorem sq_inCC_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {A : ℝ} {m : ℕ} :
    InCC A m (fun _ : Mat k r => (0 : E)) := ⟨0, Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_zero⟩

theorem sq_inCC_sum {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {A : ℝ} {m : ℕ} {ι : Type*}
    (s : Finset ι) (F : ι → Mat k r → E) (h : ∀ i ∈ s, InCC A m (F i)) : InCC A m (fun g => ∑ i ∈ s, F i g) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (sq_inCC_zero (k := k) (r := r) (E := E) (A := A) (m := m))
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact sq_inCC_add (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem sq_ckOn_sum {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {ι : Type*} (s : Finset ι)
    (F : ι → Mat k r → E) (h : ∀ i ∈ s, CkOn (⊤ : ℕ∞) (GV k r) (F i)) :
    CkOn (⊤ : ℕ∞) (GV k r) (fun g => ∑ i ∈ s, F i g) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (Formalism.FourierDecayAlt.P.BetaSesquilinearity.CkOn_zero (k := k) (r := r) (E := E) (m := ⊤))
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact Formalism.FourierDecayAlt.P.BetaSesquilinearity.CkOn_add (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem sq_good_lin (L : Mat k r →L[ℝ] ℂ) : sqGood Wp Wq 1 (fun g => L g) := by
  refine ⟨fun F hF => ?_, fun A m F hF => ?_⟩
  · intro g₀ hg₀
    obtain ⟨U, f, hU, hgU, hf, hff⟩ := hF g₀ hg₀
    exact ⟨U, fun g => L g • f g, hU, hgU, L.contDiff.contDiffOn.smul hf, fun g hg hG => by simp only [hff g hg hG]⟩
  · obtain ⟨c, hc⟩ := hF
    push_cast at hc
    set Λ : Mat k r →L[ℝ] ((Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp)) :=
      ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp))).restrictScalars ℝ).comp
        L with hΛdef
    have hΛ : ∀ g, Λ g = L g • ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp) := fun g => by simp [Λ]
    obtain ⟨K, hK⟩ : ∃ K : ℝ, ∀ M, ‖Λ M‖ ≤ K * ‖M‖ := ⟨_, Λ.le_opNorm⟩
    have ha : CkOn (m : ℕ∞) Set.univ (fun g => Λ g) := fun g₀ _ =>
      ⟨Set.univ, fun g => Λ g, isOpen_univ, trivial, Λ.contDiff.contDiffOn, fun _ _ _ => rfl⟩
    have hab : ∀ u v : List (Mat k r), (∀ X ∈ u, unitLie k r X) → (∀ X ∈ v, unitLie k r X) →
        u.length + v.length ≤ m → ∀ g ∈ GV k r, g ∉ (∅ : Set (Mat k r)) →
          ‖dLR u v (fun g => Λ g) g‖ ≤ (K * ((2 * r + k + 1 : ℕ) : ℝ) ^ (2 * m + 2)) * gN g ^ (1 : ℝ) := by
      intro u v hu hv hl g _ _
      rw [Real.rpow_one]
      exact mn_dLR_lin_bound Λ K hK m u v hu hv hl g
    have hb := Formalism.FourierDecayAlt.P.BetaSesquilinearity.prodBound (O := ∅) (UU := Set.univ) isOpen_empty (fun g _ => Or.inr trivial)
      (A := A) (d := 1) ha hab hc (fun g _ h => h.elim)
    have e : (fun g => L g • F g) = Formalism.FourierDecayAlt.P.BetaSesquilinearity.ap (fun g => Λ g) F := by
      funext g
      simp [Formalism.FourierDecayAlt.P.BetaSesquilinearity.ap, hΛ]
    rw [e]
    exact ⟨_, hb⟩

end sqQuant

end Formalism.FourierDecayAlt.P.JCx2

namespace Formalism.FourierDecayAlt.P.JCx2

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Matrix MeasureTheory

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section sqGraded

variable {X : Type} [AddCommGroup X] [Module ℂ X]

structure sqGr (S : ℕ → D.Op X → Prop) : Prop where
  zero : ∀ N, S N 0
  one : S 0 1
  add : ∀ N a b, S N a → S N b → S N (a + b)
  mul : ∀ N M a b, S N a → S M b → S (N + M) (a * b)
  cop : ∀ c, S 0 (D.cOp c)
  mono : ∀ N a, S N a → S (N + 1) a

variable {S : ℕ → D.Op X → Prop} {Sl : Type} [Fintype Sl] [DecidableEq Sl]

theorem sq_gr_sum (hS : sqGr S) (N : ℕ) {ι : Type*} (s : Finset ι) (f : ι → D.Op X) (h : ∀ i ∈ s, S N (f i)) :
    S N (∑ i ∈ s, f i) :=
  Finset.sum_induction f (S N) (hS.add N) (hS.zero N) h

def sqAll (S : ℕ → D.Op X → Prop) (N : ℕ) (M : Wd.SlopeTestRemainingChoices Sl (D.Op X)) : Prop := ∀ a b, S N (M a b)

theorem sq_all_mul (hS : sqGr S) {N N' : ℕ} {M M' : Wd.SlopeTestRemainingChoices Sl (D.Op X)} (hM : sqAll S N M) (hM' : sqAll S N' M') :
    sqAll S (N + N') (M * M') := fun a b => by
  rw [Matrix.mul_apply]
  exact sq_gr_sum hS _ _ _ fun c _ => hS.mul _ _ _ _ (hM a c) (hM' c b)

theorem sq_all_add (hS : sqGr S) {N : ℕ} {M M' : Wd.SlopeTestRemainingChoices Sl (D.Op X)} (hM : sqAll S N M) (hM' : sqAll S N M') :
    sqAll S N (M + M') := fun a b => by
  rw [Matrix.add_apply]
  exact hS.add _ _ _ (hM a b) (hM' a b)

theorem sq_all_zero (hS : sqGr S) (N : ℕ) : sqAll S N (0 : Wd.SlopeTestRemainingChoices Sl (D.Op X)) := fun _ _ => hS.zero N

theorem sq_all_one (hS : sqGr S) : sqAll S 0 (1 : Wd.SlopeTestRemainingChoices Sl (D.Op X)) := fun a b => by
  rw [Matrix.one_apply]
  split_ifs
  exacts [hS.one, hS.zero 0]

theorem sq_all_map (hS : sqGr S) (A : Wd.SlopeTestRemainingChoices Sl ℂ) : sqAll S 0 (A.map D.cOp) := fun _ _ => hS.cop _

theorem sq_all_diag (hS : sqGr S) {N : ℕ} (x : D.Op X) (hx : S N x) :
    sqAll S N (Matrix.diagonal fun _ : Wd.Ix Sl => x) := fun a b => by
  rw [Matrix.diagonal_apply]
  split_ifs
  exacts [hx, hS.zero N]

theorem sq_all_sum (hS : sqGr S) (N : ℕ) {ι : Type*} (s : Finset ι) (f : ι → Wd.SlopeTestRemainingChoices Sl (D.Op X))
    (h : ∀ i ∈ s, sqAll S N (f i)) : sqAll S N (∑ i ∈ s, f i) :=
  Finset.sum_induction f (sqAll S N) (fun _ _ => sq_all_add hS) (sq_all_zero hS N) h

def sqAll2 (S : ℕ → D.Op X → Prop) (N : ℕ) (M : Wd.M2 (Wd.SlopeTestRemainingChoices Sl (D.Op X))) : Prop := ∀ p q, sqAll S N (M p q)

theorem degree_entries_mul (hS : sqGr S) {N N' N'' : ℕ} (h : N + N' = N'') {M M' : Wd.M2 (Wd.SlopeTestRemainingChoices Sl (D.Op X))}
    (hM : sqAll2 S N M) (hM' : sqAll2 S N' M') : sqAll2 S N'' (M * M') := fun p q => by
  rw [Matrix.mul_apply, ← h]
  exact sq_all_sum hS _ _ _ fun c _ => sq_all_mul hS (hM p c) (hM' c q)

theorem degree_entries_transpose {N : ℕ} {M : Wd.M2 (Wd.SlopeTestRemainingChoices Sl (D.Op X))} (hM : sqAll2 S N M) : sqAll2 S N M.transpose :=
  fun p q => hM q p

theorem degree_entries_scalar_matrix (hS : sqGr S) (M : Wd.M2 (Wd.SlopeTestRemainingChoices Sl ℂ)) :
    sqAll2 S 0 (D.scal M : Wd.M2 (Wd.SlopeTestRemainingChoices Sl (D.Op X))) :=
  fun p q => by
    unfold D.scal
    rw [Matrix.map_apply]
    exact sq_all_map hS _

theorem sq_TTop (hS : sqGr S) (QQ : ℂ → Wd.M2 (D.Op X)) (hQQ : ∀ Y p q, S 1 (QQ Y p q))
    (w : List (Wd.Letter ℂ Sl)) (Y : ℂ) : sqAll2 S 1 (D.TTop QQ w Y) := by
  induction w with
  | nil =>
    intro p q
    simp only [D.TTop, Matrix.map_apply]
    exact sq_all_diag hS _ (hQQ Y p q)
  | cons l w ih =>
    simp only [D.TTop]
    split_ifs
    · exact degree_entries_mul hS (by omega) ih (degree_entries_scalar_matrix hS _)
    · exact degree_entries_mul hS (by omega) (degree_entries_scalar_matrix hS _) ih

theorem sq_insOp (hS : sqGr S) (a : Sl) (M : Wd.M2 (Wd.SlopeTestRemainingChoices Sl (D.Op X))) (hM : sqAll2 S 1 M) :
    sqAll S 1 (D.insOp a M) := by
  unfold D.insOp
  refine sq_all_sum hS 1 _ _ fun i _ => sq_all_sum hS 1 _ _ fun j _ => ?_
  have := sq_all_mul hS (sq_all_map hS (Wd.eU a i j : Wd.SlopeTestRemainingChoices Sl ℂ)) (hM i j)
  simpa using this

theorem sq_rrop (hS : sqGr S) (QQ : ℂ → Wd.M2 (D.Op X)) (hQQ : ∀ Y p q, S 1 (QQ Y p q))
    (w : List (Wd.Letter ℂ Sl)) : sqAll S w.length (D.RRop QQ w) := by
  induction w with
  | nil => exact sq_all_one hS
  | cons l w ih =>
    simp only [D.RRop]
    refine sq_all_mul hS ih (sq_insOp hS _ _ ?_)
    split_ifs
    · exact sq_TTop hS QQ hQQ w l.pt
    · exact degree_entries_transpose (sq_TTop hS QQ hQQ w l.pt)

end sqGraded

section sqLin

variable {k r : ℕ} (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

def sqS (N : ℕ) (Θ : D.Op (Mat k r → (Wq →L[ℂ] Wp))) : Prop :=
  sqOp Wp Wq (2 * N) ((2 * r + k + 1) * N) Θ ∧
  (∀ (F F' : Mat k r → (Wq →L[ℂ] Wp)) (c : ℂ), CkOn (⊤ : ℕ∞) (GV k r) F → CkOn (⊤ : ℕ∞) (GV k r) F' →
    ∀ g ∈ GV k r, Θ (F + c • F') g = Θ F g + c • Θ F' g) ∧
  (∀ F F' : Mat k r → (Wq →L[ℂ] Wp), CkOn (⊤ : ℕ∞) (GV k r) F → CkOn (⊤ : ℕ∞) (GV k r) F' →
    (∀ g ∈ GV k r, F g = F' g) → ∀ g ∈ GV k r, Θ F g = Θ F' g)

variable {Wp Wq}

theorem sq_glev0 (g : Mat k r) : g ∈ Q.Glev k r 0 ↔ g ∈ GV k r := by
  simp [Q.Glev]

end sqLin

end Formalism.FourierDecayAlt.P.JCx2

end

section

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Matrix MeasureTheory Filter
open scoped ComplexConjugate

namespace Formalism.FourierDecayAlt.P.JCx2

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section sqBeta

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem sq_jf_congr (D : RealPlaceData k r Wp Wq) {F F₂ : Mat k r → (Wq →L[ℂ] Wp)} (h : ∀ g ∈ GV k r, F g = F₂ g)
    {g : Mat k r} (hg : g ∈ GV k r) : JF D F g = JF D F₂ g := by
  show ∫ p, JF.xiP D p • rho D p F g ∂D.μSS = ∫ p, JF.xiP D p • rho D p F₂ g ∂D.μSS
  refine integral_congr_ae ?_
  filter_upwards [Formalism.FourierDecayAlt.P.B5.ae_inSS D] with p hp
  obtain ⟨h1, h2, h3, h4⟩ := hp
  have hs : sgs p g ∈ GV k r := by
    unfold sgs
    exact Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul
      (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_inv h1.1) (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_inv h2.1)) hg) h4.1) h3.1
  simp only [rho, h _ hs]

theorem sq_bcWeight_nonneg (T T' : ℝ) (q : (Fin r → ℂ) × ℂ) : 0 ≤ bcWeight k r T T' q := by
  unfold bcWeight
  split_ifs with h
  · exact mul_nonneg (Finset.prod_nonneg fun a _ => by positivity) (pow_nonneg (sub_nonneg.2 h) _)
  · exact le_rfl

variable [FiniteDimensional ℂ Wq]

theorem sq_beta_congr (D : RealPlaceData k r Wp Wq) {F F₂ G : Mat k r → (Wq →L[ℂ] Wp)}
    (h : ∀ g ∈ GV k r, F g = F₂ g) : beta D F G = beta D F₂ G := by
  unfold B.beta betaBig
  refine integral_congr_ae ?_
  filter_upwards [ae_imp_of_ae_restrict (Formalism.FourierDecayAlt.P.big_cell_orbit_set k r Wp Wq D)] with q hq
  by_cases hQ : q ∈ B.Qset D
  · have hg : bigCell k r q.1 (D.μsec q.2) ∈ GV k r := (hq hQ).1
    show (bcWeight k r (Tz k r D.z) (Tz k r D.z') q : ℂ) * inner ℂ (hsVec (JF D G (bigCell k r q.1 (D.μsec q.2))))
        (hsVec (JF D F (bigCell k r q.1 (D.μsec q.2)))) =
      (bcWeight k r (Tz k r D.z) (Tz k r D.z') q : ℂ) * inner ℂ (hsVec (JF D G (bigCell k r q.1 (D.μsec q.2))))
        (hsVec (JF D F₂ (bigCell k r q.1 (D.μsec q.2))))
    rw [sq_jf_congr D h hg]
  · have hw : bcWeight k r (Tz k r D.z) (Tz k r D.z') q = 0 :=
      le_antisymm (not_lt.1 hQ) (sq_bcWeight_nonneg _ _ q)
    show (bcWeight k r (Tz k r D.z) (Tz k r D.z') q : ℂ) * _ = (bcWeight k r (Tz k r D.z) (Tz k r D.z') q : ℂ) * _
    rw [hw]
    simp

variable [FiniteDimensional ℂ Wp]

theorem sq_beta_sesq (D : RealPlaceData k r Wp Wq) {A : ℝ} (hA : AB k r ≤ A) {F F' G : Mat k r → (Wq →L[ℂ] Wp)}
    (hF : InCC A 5 F) (hF' : InCC A 5 F') (hG : InCC A 5 G) (c : ℂ) :
    beta D (F + c • F') G = beta D F G + c * beta D F' G ∧
      beta D G (F + c • F') = beta D G F + conj c * beta D G F' := by
  obtain ⟨c0, -, -, -, hβ, -⟩ := Formalism.FourierDecayAlt.P.b_any_of_xi k r Wp Wq D A hA
  obtain ⟨Ξ, hCB, hXi⟩ := Formalism.FourierDecayAlt.P.exists_auxiliary_xi k r Wp Wq D A hA
  have hS := (Formalism.FourierDecayAlt.P.regularized_beta_bound_continuity_sesquilinear k r Wp Wq D Ξ A hA hCB hXi).2.2 (1, 1)
    ⟨by norm_num, by norm_num⟩
  have h4 : ∀ {H : Mat k r → (Wq →L[ℂ] Wp)}, InCC A 5 H → InCC A 4 H :=
    fun h => sq_inCC_mono le_rfl (by norm_num) h
  have hcF' : InCC A 5 (c • F') := sq_inCC_smul c hF'
  have hsum : InCC A 5 (F + c • F') := sq_inCC_add hF hcF'
  rw [hβ _ _ hsum hG, hβ _ _ hF hG, hβ _ _ hF' hG, hβ _ _ hG hsum, hβ _ _ hG hF, hβ _ _ hG hF']
  unfold betaInf
  rw [hS.1 _ _ _ (h4 hF) (h4 hcF') (h4 hG), hS.2.2.1 c _ _ (h4 hF') (h4 hG),
    hS.2.1 _ _ _ (h4 hG) (h4 hF) (h4 hcF'), hS.2.2.2 c _ _ (h4 hG) (h4 hF')]
  constructor <;> ring

end sqBeta

end Formalism.FourierDecayAlt.P.JCx2

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.JCx2
open scoped ComplexConjugate

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

end Formalism.FourierDecayAlt.P

end

section

open MeasureTheory Matrix
open scoped ENNReal NNReal ContDiff

namespace Formalism.FourierDecayAlt.P.JCx2

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section rankOne

variable {k r : ℕ}

def rbO (T T' : ℝ) : Set ℂ := {ζ | T * T' < Complex.normSq ζ}

theorem rb_isOpen_O (T T' : ℝ) : IsOpen (rbO T T') :=
  isOpen_lt continuous_const Complex.continuous_normSq

def rbEf (k r : ℕ) (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (ζ : ℂ) : Mt k r := B2.embWb k r (μsec ζ)

def rbE (k r : ℕ) (T T' : ℝ) (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (ζ : ℂ) : Mt k r :=
  (rbO T T').indicator (rbEf k r μsec) ζ

theorem rb_contOn_E {T T' : ℝ} {μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ}
    (hsec : ∀ i j, ContinuousOn (fun ζ => μsec ζ i j) (rbO T T')) :
    ContinuousOn (rbEf k r μsec) (rbO T T') := by
  refine continuousOn_pi.2 fun i => continuousOn_pi.2 fun j => ?_
  simp only [rbEf, B2.embWb]
  split_ifs
  · exact hsec _ _
  · exact continuousOn_const
  · exact continuousOn_const

theorem rb_measurable_E {T T' : ℝ} {μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ}
    (hsec : ∀ i j, ContinuousOn (fun ζ => μsec ζ i j) (rbO T T')) : Measurable (rbE k r T T' μsec) :=
  B7.meas_ind (rb_isOpen_O T T').measurableSet (rb_contOn_E hsec)

def rbMul (p : Mt k r × Mt k r) : Mt k r := B7.mulM p.1 p.2

theorem rb_measurable_mul : Measurable (rbMul (k := k) (r := r)) :=
  (B7.continuous_mulM (k := k) (r := r)).measurable

def rbPsi (k r : ℕ) (T T' : ℝ) (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
    (a : ℂ × (Mt k r × Mt k r)) : Mt k r :=
  rbMul (rbMul (B7.invM a.2.1, rbE k r T T' μsec a.1), a.2.2)

theorem rb_measurable_Psi {T T' : ℝ} {μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ}
    (hsec : ∀ i j, ContinuousOn (fun ζ => μsec ζ i j) (rbO T T')) : Measurable (rbPsi k r T T' μsec) := by
  have hi : Measurable fun a : ℂ × (Mt k r × Mt k r) => B7.invM a.2.1 :=
    B7.measurable_invM.comp (measurable_fst.comp measurable_snd)
  have he : Measurable fun a : ℂ × (Mt k r × Mt k r) => rbE k r T T' μsec a.1 :=
    (rb_measurable_E hsec).comp measurable_fst
  have h1 : Measurable fun a : ℂ × (Mt k r × Mt k r) => rbMul (B7.invM a.2.1, rbE k r T T' μsec a.1) :=
    rb_measurable_mul.comp (hi.prodMk he)
  have h3 : Measurable fun a : ℂ × (Mt k r × Mt k r) => a.2.2 := measurable_snd.comp measurable_snd
  exact rb_measurable_mul.comp (h1.prodMk h3)

theorem rb_Psi_eq {T T' : ℝ} {μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} {ζ : ℂ} (hζ : ζ ∈ rbO T T')
    (x y : Mt k r) :
    rbPsi k r T T' μsec (ζ, (x, y)) = ((Matrix.of x)⁻¹ * B2.embWb k r (μsec ζ) * Matrix.of y : B.Mat k r) := by
  simp only [rbPsi, rbMul, B7.mulM, B7.invM, rbE, Set.indicator_of_mem hζ]
  rfl

def rbW (k : ℕ) (T T' : ℝ) (ζ : ℂ) : ℝ≥0∞ := ENNReal.ofReal (B2.zWeight k T T' ζ)

theorem measurable_radial_weight (k : ℕ) (T T' : ℝ) : Measurable (rbW k T T') := by
  unfold rbW B2.zWeight
  refine ENNReal.measurable_ofReal.comp (Measurable.ite ?_ ?_ measurable_const)
  · exact measurableSet_le measurable_const Complex.continuous_normSq.measurable
  · exact ((Complex.continuous_normSq.sub continuous_const).pow _).measurable

theorem rb_zWeight_nonneg (k : ℕ) (T T' : ℝ) (ζ : ℂ) : 0 ≤ B2.zWeight k T T' ζ := by
  unfold B2.zWeight
  split_ifs with h
  · exact pow_nonneg (by linarith) _
  · exact le_rfl

theorem rb_ae_ne_circle {T T' : ℝ} (hc : 0 < T * T') : ∀ᵐ ζ : ℂ, Complex.normSq ζ ≠ T * T' := by
  have hs : (volume : Measure ℂ) (Metric.sphere 0 (Real.sqrt (T * T'))) = 0 :=
    Measure.addHaar_sphere_of_ne_zero _ _ (Real.sqrt_pos.2 hc).ne'
  refine ae_iff.2 (measure_mono_null ?_ hs)
  intro ζ hζ
  simp only [ne_eq, not_not, Set.mem_ofPred_eq] at hζ
  rw [mem_sphere_zero_iff_norm, ← hζ, Complex.normSq_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]

theorem rb_zWeight_zero_of_not {k : ℕ} {T T' : ℝ} {ζ : ℂ} (h1 : ζ ∉ rbO T T') (h2 : Complex.normSq ζ ≠ T * T') :
    B2.zWeight k T T' ζ = 0 := by
  unfold B2.zWeight
  rw [if_neg]
  intro hle
  exact h1 (lt_of_le_of_ne hle (Ne.symm h2))

def rbP (k r : ℕ) (T T' : ℝ) (μW μW' : Measure (Mt k r)) : Measure (ℂ × (Mt k r × Mt k r)) :=
  ((volume : Measure ℂ).withDensity (rbW k T T')).prod (μW.prod μW')

theorem rb_map {z z' : Fin (2 * r + k + 1) → ℂ} {μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ}
    {μb μW μW' : Measure (Mt k r)} (hk : 1 ≤ k) (hz : inWb k r z) (hz' : inWb k r z') (hT : 0 < Tz k r z)
    (hT' : 0 < Tz k r z') (hsec : IsSection k r z z' μsec) (hb : B.IsHaarOn (B2.UWb k r) μb)
    (hW : B.IsHaarOn (UWset k r z) μW) (hW' : B.IsHaarOn (UWset k r z') μW') :
    ∃ C : ℝ≥0, 0 < C ∧
      μb = (C : ℝ≥0∞) • (rbP k r (Tz k r z) (Tz k r z') μW μW').map (rbPsi k r (Tz k r z) (Tz k r z') μsec) := by
  have := B7.sf hW
  have := B7.sf hW'
  have hcont : ∀ i j, ContinuousOn (fun ζ => μsec ζ i j) (rbO (Tz k r z) (Tz k r z')) :=
    fun i j => (hsec.1 i j).continuousOn
  obtain ⟨C, hC, hI⟩ := Formalism.FourierDecayAlt.P.rank_one_integration_formula k r z z' μsec μb μW μW' hk hz hz' hT hT' hsec hb hW hW'
  refine ⟨C, hC, Measure.ext_of_lintegral _ fun f hf => ?_⟩
  have hΨ := rb_measurable_Psi (k := k) (r := r) hcont
  have hfΨ : Measurable fun a : ℂ × (Mt k r × Mt k r) => f (rbPsi k r (Tz k r z) (Tz k r z') μsec a) := hf.comp hΨ
  rw [lintegral_smul_measure, lintegral_map hf hΨ]
  unfold rbP
  rw [lintegral_prod _ hfΨ.aemeasurable,
    lintegral_withDensity_eq_lintegral_mul _ (measurable_radial_weight k _ _) hfΨ.lintegral_prod_right', hI f hf]
  congr 1
  refine lintegral_congr_ae ?_
  filter_upwards [rb_ae_ne_circle (mul_pos hT hT')] with ζ hζ
  by_cases h : ζ ∈ rbO (Tz k r z) (Tz k r z')
  · simp only [Pi.mul_apply, rbW]
    congr 1
    refine lintegral_congr fun p => ?_
    rw [rb_Psi_eq h]
  · simp only [Pi.mul_apply, rbW, rb_zWeight_zero_of_not h hζ, ENNReal.ofReal_zero, zero_mul]

end rankOne

end Formalism.FourierDecayAlt.P.JCx2

namespace Formalism.FourierDecayAlt.P.JCx2

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section rankOneB

variable {k r : ℕ}

theorem rb_integral {z z' : Fin (2 * r + k + 1) → ℂ} {μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ}
    {μb μW μW' : Measure (Mt k r)} {C : ℝ≥0} (hT : 0 < Tz k r z) (hT' : 0 < Tz k r z')
    (hsec : IsSection k r z z' μsec) (hW : B.IsHaarOn (UWset k r z) μW) (hW' : B.IsHaarOn (UWset k r z') μW')
    (hmap : μb = (C : ℝ≥0∞) • (rbP k r (Tz k r z) (Tz k r z') μW μW').map (rbPsi k r (Tz k r z) (Tz k r z') μsec))
    (φ : Mt k r → ℂ) (hφ : StronglyMeasurable φ) (ψ : ℂ → ℂ)
    (hψ : ∀ ζ ∈ rbO (Tz k r z) (Tz k r z'), ∀ x y : Mt k r, Matrix.of x ∈ UWset k r z → Matrix.of y ∈ UWset k r z' →
      φ (rbPsi k r (Tz k r z) (Tz k r z') μsec (ζ, (x, y))) = ψ ζ) :
    ∫ g, φ g ∂μb = (((C : ℝ) * (μW.prod μW').real Set.univ : ℝ) : ℂ) *
      ∫ ζ, (B2.zWeight k (Tz k r z) (Tz k r z') ζ : ℂ) * ψ ζ := by
  have := B7.sf hW
  have := B7.sf hW'
  have hcont : ∀ i j, ContinuousOn (fun ζ => μsec ζ i j) (rbO (Tz k r z) (Tz k r z')) :=
    fun i j => (hsec.1 i j).continuousOn
  subst hmap
  rw [integral_smul_measure, integral_map (rb_measurable_Psi hcont).aemeasurable hφ.aestronglyMeasurable]
  have h1 : ∀ᵐ ζ ∂((volume : Measure ℂ).withDensity (rbW k (Tz k r z) (Tz k r z'))),
      ζ ∈ rbO (Tz k r z) (Tz k r z') := by
    rw [ae_withDensity_iff (measurable_radial_weight k _ _)]
    filter_upwards [rb_ae_ne_circle (mul_pos hT hT')] with ζ hζ hw
    by_contra h
    exact hw (by simp [rbW, rb_zWeight_zero_of_not h hζ])
  have h2 : ∀ᵐ p ∂(μW.prod μW'), Matrix.of p.1 ∈ UWset k r z ∧ Matrix.of p.2 ∈ UWset k r z' := by
    have a1 := (Measure.quasiMeasurePreserving_fst (μ := μW) (ν := μW')).ae (B7.ae_mem hW)
    have a2 := (Measure.quasiMeasurePreserving_snd (μ := μW) (ν := μW')).ae (B7.ae_mem hW')
    filter_upwards [a1, a2] with p hp1 hp2 using ⟨hp1, hp2⟩
  have hae : ∀ᵐ a ∂(rbP k r (Tz k r z) (Tz k r z') μW μW'),
      φ (rbPsi k r (Tz k r z) (Tz k r z') μsec a) = ψ a.1 := by
    have g1 := (Measure.quasiMeasurePreserving_fst
      (μ := (volume : Measure ℂ).withDensity (rbW k (Tz k r z) (Tz k r z'))) (ν := μW.prod μW')).ae h1
    have g2 := (Measure.quasiMeasurePreserving_snd
      (μ := (volume : Measure ℂ).withDensity (rbW k (Tz k r z) (Tz k r z'))) (ν := μW.prod μW')).ae h2
    unfold rbP
    filter_upwards [g1, g2] with a ha1 ha2
    exact hψ a.1 ha1 a.2.1 a.2.2 ha2.1 ha2.2
  rw [integral_congr_ae hae]
  unfold rbP
  rw [integral_fun_fst (fun ζ => ψ ζ),
    integral_withDensity_eq_integral_toReal_smul (measurable_radial_weight k _ _)
      (Filter.Eventually.of_forall fun ζ => ENNReal.ofReal_lt_top)]
  have e : ∀ ζ, (rbW k (Tz k r z) (Tz k r z') ζ).toReal • ψ ζ = (B2.zWeight k (Tz k r z) (Tz k r z') ζ : ℂ) * ψ ζ := by
    intro ζ
    rw [rbW, ENNReal.toReal_ofReal (rb_zWeight_nonneg k _ _ ζ), Complex.real_smul]
  simp only [e]
  rw [ENNReal.coe_toReal, smul_smul, Complex.real_smul]

end rankOneB

end Formalism.FourierDecayAlt.P.JCx2

namespace Formalism.FourierDecayAlt.P.JCx2

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section slices

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
  {z z' : Fin (2 * r + k + 1) → ℂ} {π : Q.Mx k r → (Wp →L[ℂ] Wp)} {π' : Q.Mx k r → (Wq →L[ℂ] Wq)}

theorem rb_slice_sm (Φ : Q.RadSp k r z z' π π') (c : Fin r → ℂ) :
    StronglyMeasurable fun x : Mt k r => (Φ : Q.Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of x) := by
  classical
  obtain ⟨h0, hs, -⟩ := Φ.2
  set S : Set (Mt k r) := {x | (c, Matrix.of x) ∈ Q.DomR k r z z'} with hSdef
  have hS : MeasurableSet S := by
    by_cases hc : c ∈ OmX r
    · have e : S = {x : Mt k r | Matrix.of x ∈ Q.Glev k r (Fin.last r)} ∩
          {x : Mt k r | 0 < Q.GGl k r z z' (Matrix.of x)} := by
        ext x
        simp only [hSdef, Q.DomR, Set.mem_ofPred_eq, Set.mem_inter_iff, hc, true_and]
      rw [e]
      refine MeasurableSet.inter ?_ ?_
      · have hcl : IsClosed {x : Mt k r | Matrix.of x ∈ Q.Glev k r (Fin.last r)} :=
          (Formalism.FourierDecayAlt.P.Qx5.Glev_closed (k := k) (r := r) (Fin.last r)).preimage
            (f := fun x : Mt k r => (Matrix.of x : Q.Mx k r)) continuous_id
        exact hcl.measurableSet
      · have hGc : Continuous fun x : Mt k r => Q.GGl k r z z' (Matrix.of x) :=
          (Formalism.FourierDecayAlt.P.Qx5.GGl_continuous k r z z').comp (f := fun x : Mt k r => (Matrix.of x : Q.Mx k r)) continuous_id
        exact measurableSet_lt measurable_const hGc.measurable
    · have e : S = ∅ := by
        ext x
        simp only [hSdef, Q.DomR, Set.mem_ofPred_eq, hc, false_and, Set.mem_empty_iff_false]
      rw [e]
      exact MeasurableSet.empty
  have hcont : ContinuousOn (fun x : Mt k r => (Φ : Q.Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of x)) S := by
    intro x hx
    obtain ⟨U, F, hU, hxU, hF, hΦF⟩ := hs (c, Matrix.of x) hx
    have hpc : Continuous fun y : Mt k r => ((c, Matrix.of y) : (Fin r → ℂ) × Q.Mx k r) :=
      continuous_const.prodMk continuous_id
    have hFc : ContinuousAt (fun y : Mt k r => F (c, Matrix.of y)) x :=
      (hF.continuousOn.continuousAt (hU.mem_nhds hxU)).comp hpc.continuousAt
    refine hFc.continuousWithinAt.congr_of_eventuallyEq ?_ (hΦF _ hxU hx.2.1)
    have hUx : (fun y : Mt k r => ((c, Matrix.of y) : (Fin r → ℂ) × Q.Mx k r)) ⁻¹' U ∈ nhds x :=
      hpc.continuousAt.preimage_mem_nhds (hU.mem_nhds hxU)
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds hUx] with y hyS hyU
    exact hΦF _ hyU hyS.2.1
  have heq : (fun x : Mt k r => (Φ : Q.Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of x)) =
      S.indicator (fun x : Mt k r => (Φ : Q.Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of x)) := by
    funext x
    by_cases hx : x ∈ S
    · rw [Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx]
      exact h0 (c, Matrix.of x) hx
  rw [heq]
  exact B7.sm_ind hS hcont

theorem rb_pair_sm (Φ Ψ : Q.RadSp k r z z' π π') (c : Fin r → ℂ) :
    StronglyMeasurable fun x : Mt k r =>
      B.hsInner ((Φ : Q.Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of x)) ((Ψ : Q.Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of x)) :=
  B6.hsInner_continuous.comp_stronglyMeasurable ((rb_slice_sm Φ c).prodMk (rb_slice_sm Ψ c))

end slices

end Formalism.FourierDecayAlt.P.JCx2

namespace Formalism.FourierDecayAlt.P.JCx2

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section point

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

def rbGauge (k r : ℕ) (c : Fin r → ℂ) : ℝ :=
  ∏ a : Fin r, (if a.val < (Fin.last r).val then ‖c a‖ ^ (Mdim k r a - 1) else 1)

theorem rb_uwb_glev {g : Q.Mx k r} (hg : g ∈ B2.UWb k r) : g ∈ Q.Glev k r (Fin.last r) :=
  ⟨hg.1, fun a _ => hg.2 a⟩

theorem rb_uwb_eq : (B2.UWb k r : Set (Q.Mx k r)) = Q.Glev k r (Fin.last r) := by
  ext g
  exact ⟨rb_uwb_glev, P5.Rad.glev_last_uwb⟩

theorem rb_point (D : B.RealPlaceData k r Wp Wq) (F F' : B.Mat k r → (Wq →L[ℂ] Wp))
    (Φ Φ' : Q.RadSp k r D.z D.z' D.π D.π')
    (hΦ : ∀ y ∈ Q.DomR k r D.z D.z',
      (Φ : Q.Fn k r (Wq →L[ℂ] Wp)) y.1 y.2 = Q.resG k r (Fin.last r) (B.JF D F) y.1 y.2)
    (hΦ' : ∀ y ∈ Q.DomR k r D.z D.z',
      (Φ' : Q.Fn k r (Wq →L[ℂ] Wp)) y.1 y.2 = Q.resG k r (Fin.last r) (B.JF D F') y.1 y.2)
    {c : Fin r → ℂ} (hc : c ∈ OmX r) {ζ : ℂ} (hζ : ζ ∈ rbO (Tz k r D.z) (Tz k r D.z')) {x y : Mt k r}
    (hx : Matrix.of x ∈ UWset k r D.z) (hy : Matrix.of y ∈ UWset k r D.z') :
    B.hsInner ((Φ : Q.Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of (rbPsi k r (Tz k r D.z) (Tz k r D.z') D.μsec (ζ, (x, y)))))
        ((Φ' : Q.Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of (rbPsi k r (Tz k r D.z) (Tz k r D.z') D.μsec (ζ, (x, y))))) =
      ((rbGauge k r c ^ 2 : ℝ) : ℂ) * B.hsInner (B.JF D F (B.gq D (c, ζ))) (B.JF D F' (B.gq D (c, ζ))) := by
  have hP : (Matrix.of (rbPsi k r (Tz k r D.z) (Tz k r D.z') D.μsec (ζ, (x, y))) : Q.Mx k r) =
      (Matrix.of x)⁻¹ * B2.embWb k r (D.μsec ζ) * Matrix.of y := by
    rw [rb_Psi_eq hζ]
    rfl
  rw [hP]
  obtain ⟨hmem, hherm⟩ := Formalism.FourierDecayAlt.P.b2_rank_one_mem k r D.z D.z' D.μsec D.z_mem D.z'_mem D.sec ζ hζ
    (Matrix.of x) hx (Matrix.of y) hy
  have hdom : (c, (Matrix.of x)⁻¹ * B2.embWb k r (D.μsec ζ) * Matrix.of y) ∈ Q.DomR k r D.z D.z' := by
    refine ⟨hc, rb_uwb_glev hmem, ?_⟩
    unfold Q.GGl
    rw [P5.Rad.zetaL_last, hherm]
    exact sub_pos.2 hζ
  have hinv : (Matrix.of x)⁻¹ ∈ UWset k r D.z := WeylGroupFacts.uw_inv hx
  have hfacts := Formalism.FourierDecayAlt.P.unipotent_weyl_properties k r
  have hcomm : (Matrix.of x)⁻¹ * bigCell k r c 1 = bigCell k r c 1 * (Matrix.of x)⁻¹ :=
    hfacts.2.2 c _ (hfacts.2.1 D.z hinv)
  have hcell : Q.wCell k r (Fin.last r) c * ((Matrix.of x)⁻¹ * B2.embWb k r (D.μsec ζ) * Matrix.of y) =
      (Matrix.of x)⁻¹ * B.gq D (c, ζ) * Matrix.of y := by
    rw [P5.Rad.wCell_last_eq, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← hcomm, Matrix.mul_assoc _ (bigCell k r c 1),
      ← (Formalism.FourierDecayAlt.P.bruhat_big_cell_factorization k r c (D.μsec ζ)).1]
    rfl
  rw [hΦ _ hdom, hΦ' _ hdom]
  simp only [Q.resG]
  rw [hcell, P5.jf_uEquiv D F _ hinv hy, P5.jf_uEquiv D F' _ hinv hy, B6.hsInner_smul_left, B6.hsInner_smul_right]
  have hinv2 : B.hsInner ((D.π (Matrix.of x)⁻¹).comp ((B.JF D F (B.gq D (c, ζ))).comp (D.π' (Matrix.of y))))
      ((D.π (Matrix.of x)⁻¹).comp ((B.JF D F' (B.gq D (c, ζ))).comp (D.π' (Matrix.of y)))) =
      B.hsInner (B.JF D F (B.gq D (c, ζ))) (B.JF D F' (B.gq D (c, ζ))) := by
    unfold B.hsInner
    exact B7.al_hs_inv _ (D.π_unitary _ hinv) _ (D.π'_unitary _ hy) _ _
  rw [hinv2, Complex.conj_ofReal]
  unfold rbGauge
  push_cast
  ring

end point

end Formalism.FourierDecayAlt.P.JCx2

namespace Formalism.FourierDecayAlt.P.JCx2

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section pairAt

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem rb_pairAt (D : B.RealPlaceData k r Wp Wq) (μ : Measure (Mt k r))
    (hμ : B.IsHaarOn (Q.Glev k r (Fin.last r)) μ) :
    ∃ C1 : ℝ, 0 < C1 ∧ ∀ (F F' : B.Mat k r → (Wq →L[ℂ] Wp)) (Φ Φ' : Q.RadSp k r D.z D.z' D.π D.π'),
      (∀ y ∈ Q.DomR k r D.z D.z',
        (Φ : Q.Fn k r (Wq →L[ℂ] Wp)) y.1 y.2 = Q.resG k r (Fin.last r) (B.JF D F) y.1 y.2) →
      (∀ y ∈ Q.DomR k r D.z D.z',
        (Φ' : Q.Fn k r (Wq →L[ℂ] Wp)) y.1 y.2 = Q.resG k r (Fin.last r) (B.JF D F') y.1 y.2) →
      ∀ c ∈ OmX r, P5.pairAt μ Φ Φ' c = (C1 : ℂ) * ∫ ζ, (B2.zWeight k (Tz k r D.z) (Tz k r D.z') ζ : ℂ) *
        (((rbGauge k r c ^ 2 : ℝ) : ℂ) * B.hsInner (B.JF D F (B.gq D (c, ζ))) (B.JF D F' (B.gq D (c, ζ)))) := by
  have hμb : B.IsHaarOn (B2.UWb k r) μ := by
    rw [rb_uwb_eq]
    exact hμ
  obtain ⟨C, hC, hmap⟩ := rb_map D.k_pos D.z_mem D.z'_mem D.T_pos D.T'_pos D.sec hμb D.haarW D.haarW'
  have hfW : IsFiniteMeasure D.μW := RankOneEmbeddings.R1.haar_finite B2x3.compactW D.z_mem D.T_pos D.haarW
  have hfW' : IsFiniteMeasure D.μW' := RankOneEmbeddings.R1.haar_finite B2x3.compactW D.z'_mem D.T'_pos D.haarW'
  have hm : 0 < (D.μW.prod D.μW').real Set.univ := by
    rw [Measure.real_def, ← Set.univ_prod_univ, Measure.prod_prod, ENNReal.toReal_mul]
    refine mul_pos (ENNReal.toReal_pos ?_ (measure_ne_top _ _)) (ENNReal.toReal_pos ?_ (measure_ne_top _ _))
    · exact Measure.measure_univ_ne_zero.2 D.haarW.ne_zero
    · exact Measure.measure_univ_ne_zero.2 D.haarW'.ne_zero
  refine ⟨(C : ℝ) * (D.μW.prod D.μW').real Set.univ, mul_pos (by exact_mod_cast hC) hm, ?_⟩
  intro F F' Φ Φ' hΦ hΦ' c hc
  unfold P5.pairAt
  exact rb_integral D.T_pos D.T'_pos D.sec D.haarW D.haarW' hmap _ (rb_pair_sm Φ Φ' c) _
    (fun ζ hζ x y hx hy => rb_point D F F' Φ Φ' hΦ hΦ' hc hζ hx hy)

end pairAt

end Formalism.FourierDecayAlt.P.JCx2

namespace Formalism.FourierDecayAlt.P.JCx2

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section weight

variable {k r : ℕ}

theorem rb_gauge_eq (c : Fin r → ℂ) : rbGauge k r c = ∏ a : Fin r, ‖c a‖ ^ (Mdim k r a - 1) := by
  unfold rbGauge
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [if_pos (by simp [a.isLt])]

theorem rb_cw_eq {c : Fin r → ℂ} (hc : c ∈ OmX r) :
    (∏ a : Fin r, ‖c a‖ ^ (-2 : ℤ)) * rbGauge k r c ^ 2 = B2.cWeight k r c := by
  rw [rb_gauge_eq, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
  unfold B2.cWeight
  refine Finset.prod_congr rfl fun a _ => ?_
  have ht : 0 < ‖c a‖ := norm_pos_iff.2 (hc a)
  have hM : Mdim k r a - 1 = (Mdim k r a - 2) + 1 := by
    have := a.isLt
    unfold Mdim
    omega
  rw [hM, ← pow_mul, show (Mdim k r a - 2 + 1) * 2 = 2 * (Mdim k r a - 2) + 2 by ring, pow_add, _root_.zpow_neg,
    zpow_two]
  field_simp

theorem rb_bcWeight_nonneg (T T' : ℝ) (q : (Fin r → ℂ) × ℂ) : 0 ≤ bcWeight k r T T' q := by
  unfold bcWeight
  split_ifs with h
  · exact mul_nonneg (Finset.prod_nonneg fun a _ => pow_nonneg (norm_nonneg _) _) (pow_nonneg (by linarith) _)
  · exact le_rfl

theorem rb_weight {c : Fin r → ℂ} (hc : c ∈ OmX r) (T T' : ℝ) (ζ : ℂ) (X : ℂ) :
    ((∏ a : Fin r, ‖c a‖ ^ (-2 : ℤ) : ℝ) : ℂ) * ((B2.zWeight k T T' ζ : ℂ) * (((rbGauge k r c ^ 2 : ℝ) : ℂ) * X)) =
      (bcWeight k r T T' (c, ζ) : ℂ) * X := by
  rw [Formalism.FourierDecayAlt.P.weight_factorization k r T T' (c, ζ), ← rb_cw_eq hc]
  push_cast
  ring

theorem rb_ae_OmX : ∀ᵐ c : Fin r → ℂ, c ∈ OmX r := by
  have h : ∀ a : Fin r, ∀ᵐ c : Fin r → ℂ, c a ≠ 0 := by
    intro a
    refine ae_iff.2 ?_
    have e : {c : Fin r → ℂ | ¬ c a ≠ 0} = Function.eval a ⁻¹' {0} := by
      ext c
      simp
    rw [e, volume_pi]
    exact Measure.pi_eval_preimage_null _ (measure_singleton 0)
  filter_upwards [ae_all_iff.2 h] with c hc
  exact hc

end weight

section integrable

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem rb_aesm {E : Type*} [NormedAddCommGroup E] [SecondCountableTopology E] (D : B.RealPlaceData k r Wp Wq)
    (f : (Fin r → ℂ) × ℂ → E) (hf : ContinuousOn f (B7.Q0 D))
    (h0 : ∀ q, bcWeight k r (Tz k r D.z) (Tz k r D.z') q = 0 → f q = 0) : AEStronglyMeasurable f volume := by
  have hsm := B7.sm_ind (B7.isOpen_good_set D).measurableSet hf
  refine hsm.aestronglyMeasurable.congr ?_
  filter_upwards [B7.ae_mem_good_set_or_weight_zero D] with q hq
  rcases hq with h | h
  · exact Set.indicator_of_mem h _
  · by_cases hq : q ∈ B7.Q0 D
    · exact Set.indicator_of_mem hq _
    · rw [Set.indicator_of_notMem hq, h0 q h]

theorem rb_contOn_bcW (D : B.RealPlaceData k r Wp Wq) :
    ContinuousOn (bcWeight k r (Tz k r D.z) (Tz k r D.z')) (B7.Q0 D) := by
  have hc : Continuous fun q : (Fin r → ℂ) × ℂ =>
      (∏ a : Fin r, ‖q.1 a‖ ^ (2 * (Mdim k r a - 2))) * (Complex.normSq q.2 - Tz k r D.z * Tz k r D.z') ^ (k - 1) :=
    (continuous_finsetProd _ fun a _ => (continuous_norm.comp ((continuous_apply a).comp continuous_fst)).pow _).mul
      (((Complex.continuous_normSq.comp continuous_snd).sub continuous_const).pow _)
  refine hc.continuousOn.congr fun q hq => ?_
  unfold bcWeight
  rw [if_pos hq.2.le]

theorem rb_contOn_J (D : B.RealPlaceData k r Wp Wq) (F : B.Mat k r → (Wq →L[ℂ] Wp)) (hF : ∀ (A : ℝ) (m : ℕ), B.InCC A m F) :
    ContinuousOn (fun q => B.hsVec (B.JF D F (B.gq D q))) (B7.Q0 D) := by
  have h := Formalism.FourierDecayAlt.P.jacquet_smooth_coordinates k r Wp Wq D _ 0 F (P5.Rad.thr_big k r 0) (hF _ 0)
  have h2 : ContinuousOn (fun q => B.JF D F (B.gq D q)) (B7.Q0 D) := h.continuousOn
  exact (LinearMap.continuous_of_finiteDimensional
    (⟨⟨B.hsVec, fun X Y => by ext; simp [B.hsVec]⟩, fun a X => by ext; simp [B.hsVec]⟩ :
      (Wq →L[ℂ] Wp) →ₗ[ℂ] PiLp 2 (fun _ : Fin (Module.finrank ℂ Wq) => Wp))).comp_continuousOn h2

theorem rb_int_sq (D : B.RealPlaceData k r Wp Wq) (F : B.Mat k r → (Wq →L[ℂ] Wp)) (hF : ∀ (A : ℝ) (m : ℕ), B.InCC A m F) :
    Integrable (fun q => bcWeight k r (Tz k r D.z) (Tz k r D.z') q * ‖B.hsVec (B.JF D F (B.gq D q))‖ ^ 2) := by
  obtain ⟨-, -, -, ⟨C, hB1⟩, -⟩ := Formalism.FourierDecayAlt.P.b_any_of_xi k r Wp Wq D (B.AB k r) le_rfl
  obtain ⟨c4, hc4⟩ := hF (B.AB k r) 4
  have hfin := (hB1 F F c4 c4 (hF _ 5) (hF _ 5) hc4 hc4).1
  have hmeas : AEStronglyMeasurable
      (fun q => bcWeight k r (Tz k r D.z) (Tz k r D.z') q * ‖B.hsVec (B.JF D F (B.gq D q))‖ ^ 2) volume :=
    rb_aesm D _ ((rb_contOn_bcW D).mul ((rb_contOn_J D F hF).norm.pow 2)) fun q h => by simp [h]
  refine ⟨hmeas, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun q =>
    mul_nonneg (rb_bcWeight_nonneg _ _ q) (sq_nonneg _))]
  exact lt_of_le_of_ne le_top hfin

theorem rb_int_pair (D : B.RealPlaceData k r Wp Wq) (F F' : B.Mat k r → (Wq →L[ℂ] Wp))
    (hF : ∀ (A : ℝ) (m : ℕ), B.InCC A m F) (hF' : ∀ (A : ℝ) (m : ℕ), B.InCC A m F') :
    Integrable (fun q => (bcWeight k r (Tz k r D.z) (Tz k r D.z') q : ℂ) *
      inner ℂ (B.hsVec (B.JF D F' (B.gq D q))) (B.hsVec (B.JF D F (B.gq D q)))) := by
  have hmeas : AEStronglyMeasurable (fun q => (bcWeight k r (Tz k r D.z) (Tz k r D.z') q : ℂ) *
      inner ℂ (B.hsVec (B.JF D F' (B.gq D q))) (B.hsVec (B.JF D F (B.gq D q)))) volume := by
    refine rb_aesm D _ ?_ fun q h => by simp [h]
    exact (Complex.continuous_ofReal.comp_continuousOn (rb_contOn_bcW D)).mul
      ((rb_contOn_J D F' hF').inner (rb_contOn_J D F hF))
  refine Integrable.mono' (((rb_int_sq D F hF).add (rb_int_sq D F' hF')).div_const 2) hmeas ?_
  refine Filter.Eventually.of_forall fun q => ?_
  set b := bcWeight k r (Tz k r D.z) (Tz k r D.z') q
  set u := ‖B.hsVec (B.JF D F (B.gq D q))‖
  set v := ‖B.hsVec (B.JF D F' (B.gq D q))‖
  have hb : 0 ≤ b := rb_bcWeight_nonneg _ _ q
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hb]
  have h1 : ‖inner ℂ (B.hsVec (B.JF D F' (B.gq D q))) (B.hsVec (B.JF D F (B.gq D q)))‖ ≤ v * u :=
    norm_inner_le_norm _ _
  have h2 : v * u ≤ (u ^ 2 + v ^ 2) / 2 := by nlinarith [sq_nonneg (u - v)]
  calc b * ‖inner ℂ (B.hsVec (B.JF D F' (B.gq D q))) (B.hsVec (B.JF D F (B.gq D q)))‖ ≤ b * ((u ^ 2 + v ^ 2) / 2) :=
        mul_le_mul_of_nonneg_left (h1.trans h2) hb
    _ = (b * u ^ 2 + b * v ^ 2) / 2 := by ring

end integrable

end Formalism.FourierDecayAlt.P.JCx2

namespace Formalism.FourierDecayAlt.P.JCx2

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section assembly

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem rb_form_eq {z z' : Fin (2 * r + k + 1) → ℂ} {π : Q.Mx k r → (Wp →L[ℂ] Wp)} {π' : Q.Mx k r → (Wq →L[ℂ] Wq)}
    {S : Type} [Fintype S] [DecidableEq S] (μ : Measure (Mt k r)) (x y : Wd.Ix S → Q.RadSp k r z z' π π') :
    P5.form μ 0 x y 0 =
      ∫ c : Fin r → ℂ, ((∏ a : Fin r, ‖c a‖ ^ (-2 : ℤ) : ℝ) : ℂ) * ∑ b, P5.pairAt μ (x b) (y b) c := by
  unfold P5.form
  let e : {l : Fin r // (0 : Fin (r + 1)).val ≤ l.val} ≃ Fin r := Equiv.subtypeUnivEquiv (fun l => Nat.zero_le _)
  have hmp := volume_measurePreserving_piCongrLeft (fun _ : Fin r => ℂ) e
  refine Eq.trans ?_ (hmp.integral_comp' (g := fun c : Fin r → ℂ =>
    ((∏ a : Fin r, ‖c a‖ ^ (-2 : ℤ) : ℝ) : ℂ) * ∑ b, P5.pairAt μ (x b) (y b) c))
  refine integral_congr_ae (Filter.Eventually.of_forall fun c' => ?_)
  have hv : ∀ l : {l : Fin r // (0 : Fin (r + 1)).val ≤ l.val},
      (MeasurableEquiv.piCongrLeft (fun _ : Fin r => ℂ) e c') (e l) = c' l := fun l =>
    Equiv.piCongrLeft_apply_apply _ _ _ _
  have hg : P5.glue 0 0 c' = MeasurableEquiv.piCongrLeft (fun _ : Fin r => ℂ) e c' := by
    funext l
    have h := hv ⟨l, Nat.zero_le _⟩
    simp only [P5.glue]
    exact h.symm
  simp only [hg]
  rw [Fintype.prod_equiv e (fun l => ‖c' l‖ ^ (-2 : ℤ))
    (fun a => ‖(MeasurableEquiv.piCongrLeft (fun _ : Fin r => ℂ) e c') a‖ ^ (-2 : ℤ)) (fun l => by rw [hv])]

theorem rb_main (D : B.RealPlaceData k r Wp Wq) (μ : Measure (Mt k r)) (C1 : ℝ)
    (hpair : ∀ (F F' : B.Mat k r → (Wq →L[ℂ] Wp)) (Φ Φ' : Q.RadSp k r D.z D.z' D.π D.π'),
      (∀ y ∈ Q.DomR k r D.z D.z',
        (Φ : Q.Fn k r (Wq →L[ℂ] Wp)) y.1 y.2 = Q.resG k r (Fin.last r) (B.JF D F) y.1 y.2) →
      (∀ y ∈ Q.DomR k r D.z D.z',
        (Φ' : Q.Fn k r (Wq →L[ℂ] Wp)) y.1 y.2 = Q.resG k r (Fin.last r) (B.JF D F') y.1 y.2) →
      ∀ c ∈ OmX r, P5.pairAt μ Φ Φ' c = (C1 : ℂ) * ∫ ζ, (B2.zWeight k (Tz k r D.z) (Tz k r D.z') ζ : ℂ) *
        (((rbGauge k r c ^ 2 : ℝ) : ℂ) * B.hsInner (B.JF D F (B.gq D (c, ζ))) (B.JF D F' (B.gq D (c, ζ)))))
    {n : ℕ} (x x' : Wd.Ix (Fin n) → B.Mat k r → (Wq →L[ℂ] Wp)) (Φ Φ' : Wd.Ix (Fin n) → Q.RadSp k r D.z D.z' D.π D.π')
    (hx : ∀ a, ∀ (A : ℝ) (m : ℕ), B.InCC A m (x a)) (hx' : ∀ a, ∀ (A : ℝ) (m : ℕ), B.InCC A m (x' a))
    (hΦ : ∀ a, ∀ y ∈ Q.DomR k r D.z D.z',
      (Φ a : Q.Fn k r (Wq →L[ℂ] Wp)) y.1 y.2 = Q.resG k r (Fin.last r) (B.JF D (x a)) y.1 y.2)
    (hΦ' : ∀ a, ∀ y ∈ Q.DomR k r D.z D.z',
      (Φ' a : Q.Fn k r (Wq →L[ℂ] Wp)) y.1 y.2 = Q.resG k r (Fin.last r) (B.JF D (x' a)) y.1 y.2) :
    P5.form μ 0 Φ Φ' 0 = (C1 : ℂ) * ∑ a, B.beta D (x a) (x' a) := by
  rw [rb_form_eq]
  let f : Wd.Ix (Fin n) → (Fin r → ℂ) × ℂ → ℂ := fun a q =>
    (bcWeight k r (Tz k r D.z) (Tz k r D.z') q : ℂ) *
      inner ℂ (B.hsVec (B.JF D (x' a) (B.gq D q))) (B.hsVec (B.JF D (x a) (B.gq D q)))
  have hint : ∀ a, Integrable (f a) := fun a => rb_int_pair D (x a) (x' a) (hx a) (hx' a)
  have hae : (fun c : Fin r → ℂ => ((∏ a : Fin r, ‖c a‖ ^ (-2 : ℤ) : ℝ) : ℂ) * ∑ b, P5.pairAt μ (Φ b) (Φ' b) c)
      =ᵐ[volume] fun c => ∑ b, (C1 : ℂ) * ∫ ζ, f b (c, ζ) := by
    filter_upwards [rb_ae_OmX] with c hc
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [hpair (x b) (x' b) (Φ b) (Φ' b) (hΦ b) (hΦ' b) c hc, mul_left_comm, ← integral_const_mul]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun ζ => ?_)
    dsimp only
    rw [rb_weight hc]
    rfl
  rw [integral_congr_ae hae, integral_finsetSum _ (fun b _ => ((hint b).integral_prod_left).const_mul _),
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [integral_const_mul, ← integral_prod _ (hint b)]
  rfl

end assembly

end Formalism.FourierDecayAlt.P.JCx2

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt

theorem radial_beta_pos : Formalism.FourierDecayAlt.JC.RadialBetaPos := by
  intro Wp Wq _ _ _ _ _ _ P0 T j μ hμ
  obtain ⟨C1, hC1, hpair⟩ := JCx2.rb_pairAt (T.bs j) μ hμ
  refine ⟨C1⁻¹, inv_pos.2 hC1, fun n x x' Φ Φ' ε _ hx hx' hΦ hΦ' => ?_⟩
  have h : P5.form μ 0 Φ Φ' 0 = (C1 : ℂ) * ∑ a, B.beta (T.bs j) (x a) (x' a) :=
    JCx2.rb_main (T.bs j) μ C1 hpair x x' Φ Φ' (fun a => (hx a).2.1) (fun a => (hx' a).2.1) hΦ hΦ'
  rw [h]
  have hC : (C1 : ℂ) ≠ 0 := by exact_mod_cast hC1.ne'
  push_cast
  field_simp

end Formalism.FourierDecayAlt.P

end

section

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Matrix

namespace Formalism.FourierDecayAlt.P.JCx2

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section pdQuant

variable {k r : ℕ} (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

def pdGood (d : ℕ) (c : Mat k r → ℂ) : Prop :=
  (∀ F : Mat k r → (Wq →L[ℂ] Wp), CkOn (⊤ : ℕ∞) (GV k r) F → CkOn (⊤ : ℕ∞) (GV k r) (fun g => c g • F g)) ∧
  ∀ (A : ℝ) (m : ℕ), ∃ K : ℝ, 0 ≤ K ∧ ∀ (F : Mat k r → (Wq →L[ℂ] Wp)) (b : ℝ), CCle (A + d) m F b →
    CCle A m (fun g => c g • F g) (K * b)

def pdOp (d o : ℕ) (Θ : (Mat k r → (Wq →L[ℂ] Wp)) → Mat k r → (Wq →L[ℂ] Wp)) : Prop :=
  (∀ F, CkOn (⊤ : ℕ∞) (GV k r) F → CkOn (⊤ : ℕ∞) (GV k r) (Θ F)) ∧
  ∀ (A : ℝ) (m : ℕ), ∃ K : ℝ, 0 ≤ K ∧ ∀ (F : Mat k r → (Wq →L[ℂ] Wp)) (b : ℝ), CkOn (⊤ : ℕ∞) (GV k r) F →
    CCle (A + d) (m + o) F b → CCle A m (Θ F) (K * b)

variable {Wp Wq}

theorem pd_ccle_nonneg {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {A : ℝ} {m : ℕ} {F : Mat k r → E}
    {b : ℝ} (h : CCle A m F b) : 0 ≤ b :=
  le_trans (mul_nonneg (Real.rpow_nonneg (Real.sqrt_nonneg _) _) (norm_nonneg _))
    (h.2 [] [] (by simp) (by simp) (by simp) 1 Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_one)

theorem pd_ccle_mono_c {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {A : ℝ} {m : ℕ} {F : Mat k r → E}
    {b b' : ℝ} (h : CCle A m F b) (hb : b ≤ b') : CCle A m F b' :=
  ⟨h.1, fun u v hu hv hl g hg => (h.2 u v hu hv hl g hg).trans hb⟩

theorem pd_ccle_mono {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {A A' : ℝ} {m m' : ℕ}
    (hA : A ≤ A') (hm : m ≤ m') {F : Mat k r → E} {b : ℝ} (h : CCle A' m' F b) : CCle A m F b :=
  Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_mono_A hA (Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_mono_m hm h)

theorem pd_ccle_sum {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {A : ℝ} {m : ℕ} {ι : Type*}
    (s : Finset ι) (F : ι → Mat k r → E) (c : ι → ℝ) (h : ∀ i ∈ s, CCle A m (F i) (c i)) :
    CCle A m (fun g => ∑ i ∈ s, F i g) (∑ i ∈ s, c i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_zero (A := A) (m := m) (k := k) (r := r) (E := E))
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_add (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem pd_good_const (d : ℕ) (a : ℂ) : pdGood Wp Wq d (fun _ : Mat k r => a) := by
  refine ⟨fun F hF => Formalism.FourierDecayAlt.P.BetaSesquilinearity.CkOn_smul a hF, fun A m => ⟨‖a‖, norm_nonneg _, fun F b hF => ?_⟩⟩
  have hd : A ≤ A + d := by have : (0 : ℝ) ≤ d := Nat.cast_nonneg d; linarith
  exact Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_smul a (pd_ccle_mono hd le_rfl hF)

theorem pd_good_mul {d₁ d₂ d : ℕ} (hd : d₁ + d₂ ≤ d) {c₁ c₂ : Mat k r → ℂ} (h₁ : pdGood Wp Wq d₁ c₁)
    (h₂ : pdGood Wp Wq d₂ c₂) : pdGood Wp Wq d (fun g => c₁ g * c₂ g) := by
  have e : ∀ F : Mat k r → (Wq →L[ℂ] Wp), (fun g => (c₁ g * c₂ g) • F g) = fun g => c₁ g • (fun g => c₂ g • F g) g :=
    fun F => funext fun g => mul_smul _ _ _
  refine ⟨fun F hF => by rw [e]; exact h₁.1 _ (h₂.1 F hF), fun A m => ?_⟩
  obtain ⟨K₁, hK₁, h1⟩ := h₁.2 A m
  obtain ⟨K₂, hK₂, h2⟩ := h₂.2 (A + d₁) m
  refine ⟨K₁ * K₂, mul_nonneg hK₁ hK₂, fun F b hF => ?_⟩
  have hd' : ((d₁ + d₂ : ℕ) : ℝ) ≤ d := by exact_mod_cast hd
  push_cast at hd'
  have hF' : CCle (A + d₁ + d₂) m F b := pd_ccle_mono (by linarith) le_rfl hF
  rw [e, mul_assoc]
  exact h1 _ _ (h2 F b hF')

theorem pd_good_add {d : ℕ} {c₁ c₂ : Mat k r → ℂ} (h₁ : pdGood Wp Wq d c₁) (h₂ : pdGood Wp Wq d c₂) :
    pdGood Wp Wq d (fun g => c₁ g + c₂ g) := by
  have e : ∀ F : Mat k r → (Wq →L[ℂ] Wp), (fun g => (c₁ g + c₂ g) • F g) = fun g => c₁ g • F g + c₂ g • F g :=
    fun F => funext fun g => add_smul _ _ _
  refine ⟨fun F hF => by rw [e]; exact Formalism.FourierDecayAlt.P.BetaSesquilinearity.CkOn_add (h₁.1 F hF) (h₂.1 F hF), fun A m => ?_⟩
  obtain ⟨K₁, hK₁, h1⟩ := h₁.2 A m
  obtain ⟨K₂, hK₂, h2⟩ := h₂.2 A m
  refine ⟨K₁ + K₂, add_nonneg hK₁ hK₂, fun F b hF => ?_⟩
  rw [e, add_mul]
  exact Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_add (h1 F b hF) (h2 F b hF)

theorem pd_good_sub {d : ℕ} {c₁ c₂ : Mat k r → ℂ} (h₁ : pdGood Wp Wq d c₁) (h₂ : pdGood Wp Wq d c₂) :
    pdGood Wp Wq d (fun g => c₁ g - c₂ g) := by
  have h := pd_good_add h₁ (pd_good_mul (d₁ := 0) (d₂ := d) (by omega) (pd_good_const 0 (-1)) h₂)
  have e : (fun g => c₁ g + (-1) * c₂ g) = fun g => c₁ g - c₂ g := funext fun g => by ring
  rw [e] at h
  exact h

theorem pd_good_congr {d : ℕ} {c c' : Mat k r → ℂ} (hE : ∀ g ∈ GV k r, c g = c' g) (h : pdGood Wp Wq d c) :
    pdGood Wp Wq d c' := by
  have hE' : ∀ F : Mat k r → (Wq →L[ℂ] Wp), ∀ g ∈ GV k r, c g • F g = c' g • F g :=
    fun F g hg => by rw [hE g hg]
  refine ⟨fun F hF => mn_ckOn_congr (hE' F) (h.1 F hF), fun A m => ?_⟩
  obtain ⟨K, hK, h2⟩ := h.2 A m
  exact ⟨K, hK, fun F b hF => mn_ccle_congr (hE' F) (h2 F b hF)⟩

theorem pd_good_lin (L : Mat k r →L[ℝ] ℂ) : pdGood Wp Wq 1 (fun g => L g) := by
  refine ⟨(sq_good_lin (Wp := Wp) (Wq := Wq) L).1, fun A m => ?_⟩
  set Λ : Mat k r →L[ℝ] ((Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp)) :=
    ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp))).restrictScalars ℝ).comp
      L with hΛdef
  have hΛ : ∀ g, Λ g = L g • ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp) := fun g => by simp [Λ]
  obtain ⟨K, hK⟩ : ∃ K : ℝ, ∀ M, ‖Λ M‖ ≤ K * ‖M‖ := ⟨_, Λ.le_opNorm⟩
  set C := K * ((2 * r + k + 1 : ℕ) : ℝ) ^ (2 * m + 2) with hC
  refine ⟨2 ^ m * |C|, by positivity, fun F b hF => ?_⟩
  have hF' : CCle (A + 1) m F b := by simpa using hF
  have ha : CkOn (m : ℕ∞) Set.univ (fun g => Λ g) := fun g₀ _ =>
    ⟨Set.univ, fun g => Λ g, isOpen_univ, trivial, Λ.contDiff.contDiffOn, fun _ _ _ => rfl⟩
  have hab : ∀ u v : List (Mat k r), (∀ X ∈ u, unitLie k r X) → (∀ X ∈ v, unitLie k r X) →
      u.length + v.length ≤ m → ∀ g ∈ GV k r, g ∉ (∅ : Set (Mat k r)) →
        ‖dLR u v (fun g => Λ g) g‖ ≤ C * gN g ^ (1 : ℝ) := by
    intro u v hu hv hl g _ _
    rw [Real.rpow_one]
    exact mn_dLR_lin_bound Λ K hK m u v hu hv hl g
  have hb := Formalism.FourierDecayAlt.P.BetaSesquilinearity.prodBound (O := ∅) (UU := Set.univ) isOpen_empty (fun g _ => Or.inr trivial)
    (A := A) (d := 1) ha hab hF' (fun g _ h => h.elim)
  have e : (fun g => L g • F g) = Formalism.FourierDecayAlt.P.BetaSesquilinearity.ap (fun g => Λ g) F := by
    funext g
    simp [Formalism.FourierDecayAlt.P.BetaSesquilinearity.ap, hΛ]
  rw [e]
  have hb0 := pd_ccle_nonneg hF
  refine pd_ccle_mono_c hb (le_of_eq ?_)
  rw [abs_of_nonneg hb0]
  ring

theorem pd_good_herm (b v : Fin (2 * r + k + 1) → ℂ) :
    pdGood Wp Wq 1 (fun g : Mat k r => herm (Hpk k r) (g *ᵥ b) v) :=
  pd_good_lin (mnLinHerm b v)

theorem pd_good_inv (v : Fin (2 * r + k + 1) → ℂ) (p : Fin (2 * r + k + 1)) :
    pdGood Wp Wq 1 (fun g : Mat k r => (g⁻¹ *ᵥ v) p) :=
  pd_good_congr (fun g hg => by
    show ((Hpk k r * gᴴ * Hpk k r) *ᵥ v) p = (g⁻¹ *ᵥ v) p
    rw [mn_inv_gv hg]) (pd_good_lin (mnLinInv v p))

end pdQuant

end Formalism.FourierDecayAlt.P.JCx2

namespace Formalism.FourierDecayAlt.P.JCx2

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section pdOps

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

def pdS (N : ℕ) (Θ : D.Op (Mat k r → (Wq →L[ℂ] Wp))) : Prop :=
  pdOp Wp Wq (2 * N) ((2 * r + k + 1) * N) Θ

end pdOps

end Formalism.FourierDecayAlt.P.JCx2

end

section

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Matrix

namespace Formalism.FourierDecayAlt.P.JCx2

open Formalism.FourierDecayAlt.P.BetaSesquilinearity PI.UnitaryCorollaryDerivatives.CRH Filter Topology
open scoped ContDiff

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section pdCut

variable {k r : ℕ}

def pdChi (t : ℝ) : ℝ := Real.smoothTransition ((4 - t) / 3)

def pdSq (M : Mat k r) : ℝ := ∑ i, ∑ j, Complex.normSq (M i j)

def pdPhi (M : Mat k r) : ℂ := ((pdChi (pdSq M) : ℝ) : ℂ)

def pdPsi (R : ℝ) (g : Mat k r) : ℂ := 1 - pdPhi (R⁻¹ • g)

theorem pd_sq_cd : ContDiff ℝ ∞ (pdSq (k := k) (r := r)) := by
  unfold pdSq
  refine ContDiff.sum fun i _ => ContDiff.sum fun j _ => ?_
  exact Formalism.FourierDecayAlt.P.AdmissibleLieWords.normSq_cd.comp (contDiff_apply_apply ℝ ℂ i j)

theorem pd_chi_cd : ContDiff ℝ ∞ pdChi := by
  unfold pdChi
  exact Real.smoothTransition.contDiff.comp ((contDiff_const.sub contDiff_id).div_const 3)

theorem pd_phi_cd : ContDiff ℝ ∞ (pdPhi (k := k) (r := r)) :=
  Complex.ofRealCLM.contDiff.comp (pd_chi_cd.comp pd_sq_cd)

theorem pd_chi_one {t : ℝ} (ht : t ≤ 1) : pdChi t = 1 :=
  Real.smoothTransition.one_of_one_le (by rw [le_div_iff₀ (by norm_num : (0:ℝ) < 3)]; linarith)

theorem pd_chi_zero {t : ℝ} (ht : 4 ≤ t) : pdChi t = 0 :=
  Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) (by norm_num))

theorem pd_sq_eq (M : Mat k r) : pdSq M = gN M ^ 2 :=
  (Real.sq_sqrt (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => Complex.normSq_nonneg (M i j))).symm

theorem pd_sq_smul (s : ℝ) (M : Mat k r) : pdSq (s • M) = s ^ 2 * pdSq M := by
  unfold pdSq
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Matrix.smul_apply]
  rw [show (s • M i j : ℂ) = (s : ℂ) * M i j from by simp [Complex.real_smul], Complex.normSq_mul,
    Complex.normSq_ofReal]
  ring

theorem pd_phi_support : HasCompactSupport (pdPhi (k := k) (r := r)) := by
  have hK : IsCompact {M : Mat k r | pdSq M ≤ 4} := by
    refine Metric.isCompact_of_isClosed_isBounded (isClosed_le pd_sq_cd.continuous continuous_const) ?_
    refine (Metric.isBounded_closedBall (x := (0 : Mat k r)) (r := 2)).subset fun M hM => ?_
    simp only [Set.mem_setOf_eq] at hM
    rw [Metric.mem_closedBall, dist_zero_right]
    have h1 := mn_norm_le_gN M
    have h2 : gN M ^ 2 ≤ 2 ^ 2 := by rw [← pd_sq_eq]; linarith
    have h0 : 0 ≤ gN M := Real.sqrt_nonneg _
    have h3 : gN M ≤ 2 := by nlinarith
    linarith
  refine HasCompactSupport.intro hK fun M hM => ?_
  simp only [Set.mem_setOf_eq, not_le] at hM
  simp [pdPhi, pd_chi_zero hM.le]

theorem pd_phi_bound (j : ℕ) : ∃ B : ℝ, ∀ y ∈ (Set.univ : Set (Mat k r)), ‖iteratedFDeriv ℝ j pdPhi y‖ ≤ B := by
  obtain ⟨B, hB⟩ := ((pd_phi_cd (k := k) (r := r)).continuous_iteratedFDeriv (m := j)
    (by exact_mod_cast le_top)).norm.bddAbove_range_of_hasCompactSupport
    ((pd_phi_support (k := k) (r := r)).iteratedFDeriv (𝕜 := ℝ) j).norm
  exact ⟨B, fun y _ => hB ⟨y, rfl⟩⟩

theorem pd_Dx_scale {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (s : ℝ) (x : Bool × Mat k r)
    (f : Mat k r → E) : Dx x (fun g => f (s • g)) = fun g => Dx x f (s • g) := by
  funext g
  rw [Dx_eq, Dx_eq]
  congr 1
  funext t
  congr 1
  unfold crv
  split_ifs
  · rw [Matrix.mul_smul]
  · rw [Matrix.smul_mul]

theorem pd_Dw_scale {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (s : ℝ) (f : Mat k r → E) :
    ∀ w : List (Bool × Mat k r), Dw w (fun g => f (s • g)) = fun g => Dw w f (s • g) := by
  intro w
  induction w with
  | nil => rfl
  | cons x w ih =>
    show Dx x (Dw w _) = fun g => Dx x (Dw w f) (s • g)
    rw [ih]
    exact pd_Dx_scale s x _

theorem pd_Dw_congr_open {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {U : Set (Mat k r)} (hU : IsOpen U)
    {f f' : Mat k r → E} (h : ∀ M ∈ U, f M = f' M) :
    ∀ w : List (Bool × Mat k r), ∀ M ∈ U, Dw w f M = Dw w f' M := by
  intro w
  induction w with
  | nil => exact h
  | cons x w ih =>
    intro M hM
    show Dx x (Dw w f) M = Dx x (Dw w f') M
    rw [Dx_eq, Dx_eq]
    apply Filter.EventuallyEq.deriv_eq
    have hc := (crv_hasDerivAt x M).continuousAt
    have hmem : ∀ᶠ t : ℝ in 𝓝 0, crv x M t ∈ U :=
      hc.preimage_mem_nhds (by rw [crv_zero]; exact hU.mem_nhds hM)
    filter_upwards [hmem] with t ht
    exact ih _ ht

theorem pd_Dx_const {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (c : E) (x : Bool × Mat k r) :
    Dx x (fun _ : Mat k r => c) = fun _ => 0 := by
  funext M; rw [Dx_eq]; simp

theorem pd_Dw_const0 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (c : E) :
    ∀ w : List (Bool × Mat k r), w ≠ [] → Dw w (fun _ : Mat k r => c) = fun _ => 0 := by
  intro w
  induction w with
  | nil => intro h; exact (h rfl).elim
  | cons x w ih =>
    intro _
    show Dx x (Dw w _) = _
    by_cases hw : w = []
    · subst hw; exact pd_Dx_const c x
    · rw [ih hw]; exact pd_Dx_const 0 x

theorem pd_Dw_const {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (c : E) (w : List (Bool × Mat k r))
    (M : Mat k r) : ‖Dw w (fun _ => c) M‖ ≤ ‖c‖ := by
  by_cases hw : w = []
  · subst hw; exact le_rfl
  · rw [pd_Dw_const0 c w hw]; simp

end pdCut

end Formalism.FourierDecayAlt.P.JCx2

namespace Formalism.FourierDecayAlt.P.JCx2

open Formalism.FourierDecayAlt.P.BetaSesquilinearity PI.UnitaryCorollaryDerivatives.CRH Filter Topology
open scoped ContDiff

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section pdCutBound

variable {k r : ℕ}

theorem pd_gN_le_of_sq {M : Mat k r} {a : ℝ} (ha : 0 ≤ a) (h : pdSq M ≤ a ^ 2) : gN M ≤ a := by
  have h0 : 0 ≤ gN M := Real.sqrt_nonneg _
  rw [pd_sq_eq] at h
  nlinarith

theorem pd_phi_deriv (m : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ w, admitted m w → ∀ M : Mat k r, ‖Dw w pdPhi M‖ ≤ C := by
  set n : ℝ := ((2 * r + k + 1 : ℕ) : ℝ)
  have H : ∀ w, admitted m w → w ≠ [] → ∀ M ∈ {M : Mat k r | pdSq M ≤ 3 ^ 2},
      ‖Dw w (fun M : Mat k r => M) M‖ ≤ (n ^ (2 * m + 2) * 3) * (fun _ => (1 : ℝ)) M ^ (0 * w.length + 0) := by
    intro w hw _ M hM
    obtain ⟨u, v, hu, hv, hl, rfl⟩ := hw
    have h1 := mn_dLR_lin_bound (ContinuousLinearMap.id ℝ (Mat k r)) 1 (fun M => by show ‖M‖ ≤ 1 * ‖M‖; rw [one_mul]) m u v hu hv hl M
    rw [dLR_eq] at h1
    have h2 : gN M ≤ 3 := pd_gN_le_of_sq (by norm_num) hM
    have hn : 0 ≤ n ^ (2 * m + 2) := by positivity
    simp only [one_pow, mul_one]
    calc ‖Dw (wL u ++ wR v) (fun M : Mat k r => M) M‖ ≤ 1 * n ^ (2 * m + 2) * gN M := h1
      _ ≤ n ^ (2 * m + 2) * 3 := by nlinarith
  obtain ⟨C, hC0, hC⟩ := Formalism.FourierDecayAlt.P.AdmissibleLieWords.fdb (fun M : Mat k r => M) contDiff_id {M : Mat k r | pdSq M ≤ 3 ^ 2}
    Set.univ (fun _ _ => trivial) (fun _ => (1 : ℝ)) (fun _ _ => le_rfl) 0 0 (n ^ (2 * m + 2) * 3) m H m ℂ
    pdPhi pd_phi_cd pd_phi_bound
  refine ⟨C, hC0, fun w hw M => ?_⟩
  by_cases hM : pdSq M ≤ 3 ^ 2
  · have := hC w hw (Formalism.FourierDecayAlt.P.AdmissibleLieWords.admissible_word_length_le hw) M hM
    simpa using this
  · have hU : IsOpen {M : Mat k r | 4 < pdSq M} := isOpen_lt continuous_const pd_sq_cd.continuous
    have hz : ∀ M' ∈ {M : Mat k r | 4 < pdSq M}, pdPhi M' = (fun _ => (0 : ℂ)) M' := by
      intro M' hM'
      simp [pdPhi, pd_chi_zero (le_of_lt hM')]
    rw [pd_Dw_congr_open hU hz w M (by simp only [Set.mem_setOf_eq]; simp only [Set.mem_setOf_eq, not_le] at hM; linarith), Dw_zero]
    simpa using hC0

theorem pd_psi_deriv (m : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R → ∀ w, admitted m w → ∀ g : Mat k r,
    ‖Dw w (pdPsi R) g‖ ≤ C ∧ (gN g < R → Dw w (pdPsi R) g = 0) := by
  obtain ⟨C, hC0, hC⟩ := pd_phi_deriv (k := k) (r := r) m
  refine ⟨1 + C, by linarith, fun R hR w hw g => ⟨?_, fun hg => ?_⟩⟩
  · have hcd : ContDiff ℝ ∞ (fun g : Mat k r => pdPhi (R⁻¹ • g)) :=
      pd_phi_cd.comp (contDiff_const_smul R⁻¹)
    have hsum : Dw w (pdPsi R) g =
        Dw w (fun _ : Mat k r => (1 : ℂ)) g + Dw w (fun g => (-1 : ℂ) • pdPhi (R⁻¹ • g)) g := by
      have := congrFun (Formalism.FourierDecayAlt.P.AdmissibleLieWords.dw_add w (a := fun _ : Mat k r => (1 : ℂ))
        (b := fun g => (-1 : ℂ) • pdPhi (R⁻¹ • g)) contDiff_const (hcd.const_smul (-1 : ℂ))) g
      rw [← this]
      congr 1
      funext g
      simp [pdPsi, sub_eq_add_neg]
    rw [hsum, Dw_smul, pd_Dw_scale]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul]
    have h1 := pd_Dw_const (1 : ℂ) w g
    have h2 := hC w hw (R⁻¹ • g)
    simp only [norm_neg, norm_one, one_mul] at h1 h2 ⊢
    linarith
  · have hU : IsOpen {g' : Mat k r | pdSq (R⁻¹ • g') < 1} :=
      isOpen_lt (pd_sq_cd.continuous.comp (continuous_const_smul R⁻¹)) continuous_const
    have hgU : g ∈ {g' : Mat k r | pdSq (R⁻¹ • g') < 1} := by
      simp only [Set.mem_setOf_eq]
      rw [pd_sq_smul, pd_sq_eq]
      have h0 : 0 ≤ gN g := Real.sqrt_nonneg _
      rw [inv_pow, inv_mul_lt_iff₀ (by positivity), mul_one]
      nlinarith
    have hz : ∀ g' ∈ {g' : Mat k r | pdSq (R⁻¹ • g') < 1}, pdPsi R g' = (fun _ => (0 : ℂ)) g' := by
      intro g' hg'
      simp [pdPsi, pdPhi, pd_chi_one (le_of_lt hg')]
    rw [pd_Dw_congr_open hU hz w g hgU, Dw_zero]

end pdCutBound

end Formalism.FourierDecayAlt.P.JCx2

namespace Formalism.FourierDecayAlt.P.JCx2

open Formalism.FourierDecayAlt.P.BetaSesquilinearity PI.UnitaryCorollaryDerivatives.CRH Filter Topology
open scoped ContDiff

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section pdCutCC

variable {k r : ℕ}

theorem pd_psi_cd (R : ℝ) : ContDiff ℝ ∞ (pdPsi (k := k) (r := r) R) :=
  contDiff_const.sub (pd_phi_cd.comp (contDiff_const_smul R⁻¹))

theorem pd_cut_ccle {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (m : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ R : ℝ, 0 < R → ∀ (A : ℝ) (F : Mat k r → E) (b : ℝ), CCle A m F b →
      CCle (A - 1) m (fun g => pdPsi R g • F g) (K * b / R) := by
  obtain ⟨C, hC0, hC⟩ := pd_psi_deriv (k := k) (r := r) m
  set L : ℂ →L[ℝ] (E →L[ℂ] E) :=
    (ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (ContinuousLinearMap.id ℂ E)).restrictScalars ℝ with hLdef
  have hL : ∀ z : ℂ, L z = z • ContinuousLinearMap.id ℂ E := fun z => by simp [L]
  refine ⟨2 ^ m * (‖L‖ * C), by positivity, fun R hR A F b hF => ?_⟩
  have hb0 := pd_ccle_nonneg hF
  have ha : CkOn (m : ℕ∞) (Set.univ : Set (Mat k r)) (fun g : Mat k r => L (pdPsi R g)) := fun g₀ _ =>
    ⟨Set.univ, fun g : Mat k r => L (pdPsi R g), isOpen_univ, trivial,
      (L.contDiff.comp (pd_psi_cd R)).contDiffOn.of_le (by exact_mod_cast le_top), fun _ _ _ => rfl⟩
  have hab : ∀ u v : List (Mat k r), (∀ X ∈ u, unitLie k r X) → (∀ X ∈ v, unitLie k r X) →
      u.length + v.length ≤ m → ∀ g ∈ GV k r, g ∉ (∅ : Set (Mat k r)) →
        ‖dLR u v (fun g => L (pdPsi R g)) g‖ ≤ (‖L‖ * C / R) * gN g ^ (1 : ℝ) := by
    intro u v hu hv hl g hg _
    rw [Real.rpow_one, dLR_eq, Formalism.FourierDecayAlt.P.AdmissibleLieWords.dw_clm L _ (pd_psi_cd R)]
    show ‖L (Dw (wL u ++ wR v) (pdPsi R) g)‖ ≤ _
    have hw : admitted m (wL u ++ wR v) := ⟨u, v, hu, hv, hl, rfl⟩
    obtain ⟨h1, h2⟩ := hC R hR _ hw g
    have hgN : 0 ≤ gN g := Real.sqrt_nonneg _
    by_cases hg' : gN g < R
    · rw [h2 hg', map_zero, norm_zero]
      positivity
    · push_neg at hg'
      calc ‖L (Dw (wL u ++ wR v) (pdPsi R) g)‖ ≤ ‖L‖ * ‖Dw (wL u ++ wR v) (pdPsi R) g‖ := L.le_opNorm _
        _ ≤ ‖L‖ * C := mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
        _ ≤ ‖L‖ * C / R * gN g := by
          have hLC : 0 ≤ ‖L‖ * C := mul_nonneg (norm_nonneg _) hC0
          rw [div_mul_eq_mul_div, le_div_iff₀ hR]
          exact mul_le_mul_of_nonneg_left hg' hLC
  have hF' : CCle (A - 1 + 1) m F b := by simpa using hF
  have hb := prodBound (O := ∅) (UU := Set.univ) isOpen_empty (fun g _ => Or.inr trivial)
    (A := A - 1) (d := 1) ha hab hF' (fun g _ h => h.elim)
  have e : (fun g => pdPsi R g • F g) = ap (fun g => L (pdPsi R g)) F := by
    funext g
    simp [ap, hL]
  rw [e]
  refine pd_ccle_mono_c hb (le_of_eq ?_)
  rw [abs_of_nonneg hb0, abs_of_nonneg (by positivity)]
  field_simp

theorem pd_cut_nice {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {R : ℝ} (hR : 0 < R)
    {F : Mat k r → E} (hF : CkOn (⊤ : ℕ∞) (GV k r) F) :
    CkOn (⊤ : ℕ∞) (GV k r) (fun g => pdPhi (R⁻¹ • g) • F g) ∧
      ∀ (A : ℝ) (m : ℕ), InCC A m (fun g => pdPhi (R⁻¹ • g) • F g) := by
  have hcd : ContDiff ℝ ∞ (fun g : Mat k r => pdPhi (R⁻¹ • g)) := pd_phi_cd.comp (contDiff_const_smul R⁻¹)
  have hck : CkOn (⊤ : ℕ∞) (GV k r) (fun g => pdPhi (R⁻¹ • g) • F g) := by
    intro g₀ hg₀
    obtain ⟨U, f, hU, hgU, hf, hff⟩ := hF g₀ hg₀
    exact ⟨U, fun g => pdPhi (R⁻¹ • g) • f g, hU, hgU, hcd.contDiffOn.smul hf,
      fun g hg hG => by simp only [hff g hg hG]⟩
  refine ⟨hck, ?_⟩
  have hK : IsCompact {g : Mat k r | pdSq g ≤ (2 * R) ^ 2} := by
    refine Metric.isCompact_of_isClosed_isBounded (isClosed_le pd_sq_cd.continuous continuous_const) ?_
    refine (Metric.isBounded_closedBall (x := (0 : Mat k r)) (r := 2 * R)).subset fun M hM => ?_
    rw [Metric.mem_closedBall, dist_zero_right]
    exact (mn_norm_le_gN M).trans (pd_gN_le_of_sq (by positivity) hM)
  refine Formalism.FourierDecayAlt.P.compact_support_finite_class k r E _ _ hck hK fun g hg => ?_
  simp only [Set.mem_setOf_eq, not_le] at hg
  have h4 : 4 ≤ pdSq (R⁻¹ • g) := by
    rw [pd_sq_smul, inv_pow, le_inv_mul_iff₀ (by positivity)]
    nlinarith
  simp [pdPhi, pd_chi_zero h4]

end pdCutCC

end Formalism.FourierDecayAlt.P.JCx2

end

section

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Matrix

namespace Formalism.FourierDecayAlt.P.JCx2

open Formalism.FourierDecayAlt.P.BetaSesquilinearity
open scoped ComplexOrder ComplexConjugate

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section pdMain

theorem pd_nonneg_of_approx (z : ℂ) (M : ℝ) (h : ∀ R : ℝ, 1 ≤ R → ∃ w : ℂ, 0 ≤ w ∧ ‖z - w‖ ≤ M / R) : 0 ≤ z := by
  have him : z.im = 0 := by
    by_contra hne
    have hpos : 0 < |z.im| := abs_pos.2 hne
    obtain ⟨w, hw, hzw⟩ := h (max 1 ((|M| + 1) / |z.im|)) (le_max_left _ _)
    have hwim : w.im = 0 := (Complex.nonneg_iff.1 hw).2.symm
    have h1 : |z.im| ≤ ‖z - w‖ := by
      have := Complex.abs_im_le_norm (z - w)
      simpa [hwim] using this
    have hRpos : 0 < max 1 ((|M| + 1) / |z.im|) := lt_of_lt_of_le one_pos (le_max_left _ _)
    have h2 : M / max 1 ((|M| + 1) / |z.im|) < |z.im| := by
      rw [div_lt_iff₀ hRpos]
      have h3 : (|M| + 1) / |z.im| ≤ max 1 ((|M| + 1) / |z.im|) := le_max_right _ _
      have h4 : |M| + 1 ≤ |z.im| * max 1 ((|M| + 1) / |z.im|) := by
        rw [div_le_iff₀ hpos] at h3; linarith
      linarith [le_abs_self M]
    linarith
  have hre : 0 ≤ z.re := by
    by_contra hneg
    push_neg at hneg
    have hpos : 0 < -z.re := by linarith
    obtain ⟨w, hw, hzw⟩ := h (max 1 ((|M| + 1) / (-z.re))) (le_max_left _ _)
    have hwre : 0 ≤ w.re := (Complex.nonneg_iff.1 hw).1
    have h1 : -z.re ≤ ‖z - w‖ := by
      have := Complex.abs_re_le_norm (z - w)
      simp only [Complex.sub_re] at this
      have : |z.re - w.re| ≥ w.re - z.re := by rw [abs_sub_comm]; exact le_abs_self _
      linarith
    have hRpos : 0 < max 1 ((|M| + 1) / (-z.re)) := lt_of_lt_of_le one_pos (le_max_left _ _)
    have h2 : M / max 1 ((|M| + 1) / (-z.re)) < -z.re := by
      rw [div_lt_iff₀ hRpos]
      have h3 : (|M| + 1) / (-z.re) ≤ max 1 ((|M| + 1) / (-z.re)) := le_max_right _ _
      have h4 : |M| + 1 ≤ (-z.re) * max 1 ((|M| + 1) / (-z.re)) := by
        rw [div_le_iff₀ hpos] at h3; linarith
      linarith [le_abs_self M]
    linarith
  exact Complex.nonneg_iff.2 ⟨hre, him.symm⟩

theorem pd_smooth_smul {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {c : Mat k r → ℂ}
    (hc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) c) {F : Mat k r → E} (hF : CkOn (⊤ : ℕ∞) (GV k r) F) :
    CkOn (⊤ : ℕ∞) (GV k r) (fun g => c g • F g) := by
  intro g₀ hg₀
  obtain ⟨U, f, hU, hgU, hf, hff⟩ := hF g₀ hg₀
  exact ⟨U, fun g => c g • f g, hU, hgU, hc.contDiffOn.smul hf,
    fun g hg hG => by simp only [hff g hg hG]⟩

end pdMain

end Formalism.FourierDecayAlt.P.JCx2

namespace Formalism.FourierDecayAlt.P.JCx2

open Formalism.FourierDecayAlt.P.BetaSesquilinearity
open scoped ComplexOrder ComplexConjugate

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section pdMain2

theorem pd_thr_AB (P0 : M.Par) (j : Fin (P0.r + 1)) (N : ℕ) (A : ℝ) (hA : P5.Auser P0 N + 1 ≤ A) :
    AB P0.k (P0.r - j) ≤ A - 1 - 2 * N := by
  unfold P5.Auser P5.nV at hA
  unfold AB
  have hr' : ((P0.r - (j : ℕ) : ℕ) : ℝ) ≤ P0.r := by exact_mod_cast Nat.sub_le _ _
  have hr0 : (0 : ℝ) ≤ ((P0.r - (j : ℕ) : ℕ) : ℝ) := Nat.cast_nonneg _
  set n : ℝ := ((2 * P0.r + P0.k + 1 : ℕ) : ℝ) with hn
  have hnc : n = 2 * (P0.r : ℝ) + P0.k + 1 := by rw [hn]; push_cast; ring
  have hk0 : (0 : ℝ) ≤ P0.k := Nat.cast_nonneg _
  have hrr0 : (0 : ℝ) ≤ P0.r := Nat.cast_nonneg _
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hn1 : 1 ≤ n := by rw [hnc]; linarith
  have h1 : 1 ≤ ((P0.r : ℝ) + 1) ^ 3 := one_le_pow₀ (by linarith)
  have hbr : 0 ≤ (N : ℝ) * n ^ 2 + n ^ 3 := by positivity
  have h2 : 127 * ((N : ℝ) * n ^ 2 + n ^ 3) ≤ 127 * ((P0.r : ℝ) + 1) ^ 3 * ((N : ℝ) * n ^ 2 + n ^ 3) := by
    nlinarith
  have h3 : 2 * ((P0.k : ℝ) + ((P0.r - (j : ℕ) : ℕ) : ℝ)) * (((P0.r - (j : ℕ) : ℕ) : ℝ) + 1) ≤ 2 * n * n := by
    have a1 : (P0.k : ℝ) + ((P0.r - (j : ℕ) : ℕ) : ℝ) ≤ n := by rw [hnc]; linarith
    have a2 : ((P0.r - (j : ℕ) : ℕ) : ℝ) + 1 ≤ n := by rw [hnc]; linarith
    nlinarith
  have h4 : 2 * n * n + 1 + 2 * N ≤ 127 * ((N : ℝ) * n ^ 2 + n ^ 3) := by
    have b1 : n * n ≤ n ^ 3 := by nlinarith
    have b2 : (N : ℝ) ≤ N * n ^ 2 := le_mul_of_one_le_right hN0 (one_le_pow₀ hn1)
    nlinarith
  linarith

theorem pd_thr_mm (P0 : M.Par) (j : Fin (P0.r + 1)) (N mm : ℕ) (hmm : P5.mmUser P0 N ≤ mm) :
    5 + (2 * (P0.r - (j : ℕ)) + P0.k + 1) * N ≤ mm := by
  unfold P5.mmUser P5.nV at hmm
  have h1 : (2 * (P0.r - (j : ℕ)) + P0.k + 1) * N ≤ (2 * P0.r + P0.k + 1) * N :=
    Nat.mul_le_mul_right _ (by omega)
  have h2 : (2 * P0.r + P0.k + 1) * N ≤ 3 * (P0.r + 1) * (N + 2) * (2 * P0.r + P0.k + 1) := by
    have : (2 * P0.r + P0.k + 1) * N ≤ (2 * P0.r + P0.k + 1) * (3 * (P0.r + 1) * (N + 2)) :=
      Nat.mul_le_mul_left _ (by nlinarith)
    linarith [Nat.mul_comm (2 * P0.r + P0.k + 1) (3 * (P0.r + 1) * (N + 2))]
  omega

end pdMain2

end Formalism.FourierDecayAlt.P.JCx2

namespace Formalism.FourierDecayAlt.P.JCx2

open Formalism.FourierDecayAlt.P.BetaSesquilinearity
open scoped ComplexOrder ComplexConjugate

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

end Formalism.FourierDecayAlt.P.JCx2

end

section

end

section

namespace Formalism.FourierDecayAlt.P

theorem radial_module_form : Formalism.FourierDecayAlt.JC.RadialModuleForm :=
  radial_module_form_of_parts radial_beta_pos radial_module_action bessel_function_finite_class
    bessel_module module_regularity

end Formalism.FourierDecayAlt.P

end

section

noncomputable section

namespace Formalism.FourierDecayAlt.P.JCx2

open Formalism.FourierDecayAlt

section classesM

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def KKcM (Bs : B.RealPlaceData k r Wp Wq) (A : ℝ) (mm : ℕ) : Submodule ℂ (B.Mat k r → (Wq →L[ℂ] Wp)) where
  carrier := {F | ∃ ε, 0 < ε ∧ JC.CCCoefM Bs A mm ε F}
  zero_mem' := ⟨1, one_pos, ckOn_zero', ⟨0, Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_zero⟩, fun _ _ h => (h rfl).elim⟩
  add_mem' := by
    rintro F F' ⟨ε, hε, hF1, ⟨c, hc⟩, hF3⟩ ⟨ε', hε', hF1', ⟨c', hc'⟩, hF3'⟩
    refine ⟨min ε ε', lt_min hε hε', ckOn_add' hF1 hF1', ⟨c + c', Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_add hc hc'⟩,
      fun g hg hne => ?_⟩
    by_cases h : F g = 0
    · have h' : F' g ≠ 0 := by simpa [h] using hne
      exact (min_le_right _ _).trans (hF3' g hg h')
    · exact (min_le_left _ _).trans (hF3 g hg h)
  smul_mem' := by
    rintro a F ⟨ε, hε, hF1, ⟨c, hc⟩, hF3⟩
    refine ⟨ε, hε, ckOn_smul' a hF1, ⟨‖a‖ * c, Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_smul a hc⟩, fun g hg hne => ?_⟩
    refine hF3 g hg fun h => hne ?_
    simp [h]

theorem cCCoefM_mono {Bs : B.RealPlaceData k r Wp Wq} {A : ℝ} {mm : ℕ} {ε ε' : ℝ} (h : ε' ≤ ε)
    {F : B.Mat k r → (Wq →L[ℂ] Wp)} (hF : JC.CCCoefM Bs A mm ε F) : JC.CCCoefM Bs A mm ε' F :=
  ⟨hF.1, hF.2.1, fun g hg hne => h.trans (hF.2.2 g hg hne)⟩

end classesM

end Formalism.FourierDecayAlt.P.JCx2

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt
open scoped ComplexOrder

theorem theorem_P_module_moderate_growth : Formalism.FourierDecayAlt.JC.ThmPModuleOfActualMM := by
  intro hP hRMF hPD hSesq Wp Wq _ _ _ _ _ _ P0 T l0 N admitted A mm hl0 hl0k hAdmN hA hmm hdata
  refine ⟨fun j => JCx2.KKcM (T.bs j) A mm, fun j w hw => ?_, fun j F ε hε hF hF1 hF3 => ⟨ε, hε, hF1, hF, hF3⟩⟩
  have hlen := hAdmN w hw
  have hA' : P5.Auser P0 w.length + 1 ≤ A := le_trans (by linarith [JCx2.auser_mono P0 hlen]) hA
  have hmm' : P5.mmUser P0 w.length ≤ mm := le_trans (JCx2.mmUser_mono P0 hlen) hmm
  have hmemK : ∀ x : Wd.Ix (Fin w.length) → B.Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp),
      x ∈ Submodule.pi Set.univ (fun _ => JCx2.KKcM (T.bs j) A mm) →
      ∃ ε, 0 < ε ∧ ∀ a, JC.CCCoefM (T.bs j) A mm ε (x a) := by
    intro x hx
    exact JCx2.exists_common_eps (fun a ε => JC.CCCoefM (T.bs j) A mm ε (x a))
      (fun a ε ε' _ h hF => JCx2.cCCoefM_mono h hF) (fun a => hx a (Set.mem_univ a))
  refine ⟨fun x hx x' hx' y hy c => ?_, fun x hx => ?_⟩
  · obtain ⟨e1, he1, h1⟩ := hmemK x hx
    obtain ⟨e2, he2, h2⟩ := hmemK x' hx'
    obtain ⟨e3, he3, h3⟩ := hmemK y hy
    have hε : 0 < min e1 (min e2 e3) := lt_min he1 (lt_min he2 he3)
    exact hSesq Wp Wq P0 T (M.sgn P0 l0) j w A mm _ hε hA' hmm' x x' y c
      (fun a => JCx2.cCCoefM_mono (min_le_left _ _) (h1 a))
      (fun a => JCx2.cCCoefM_mono ((min_le_right _ _).trans (min_le_left _ _)) (h2 a))
      (fun a => JCx2.cCCoefM_mono ((min_le_right _ _).trans (min_le_right _ _)) (h3 a))
  · obtain ⟨ε, hε, hxε⟩ := hmemK x hx
    refine hPD Wp Wq P0 T (M.sgn P0 l0) j w A mm ε hε hA' hmm' ?_ x hxε
    intro ε₁ hε₁ v hvn
    obtain ⟨X, μ, L, st, hD, hOK⟩ := hdata j
    obtain ⟨Cst, hC, hform⟩ := hRMF Wp Wq P0 T j X μ L st l0 hD
    have hAu : P5.Auser (JC.parLev P0 j) (Fintype.card (Fin w.length)) ≤ A := by
      rw [Fintype.card_fin]
      linarith [JCx2.auser_parLev P0 j w.length]
    have hmu : P5.mmUser (JC.parLev P0 j) (Fintype.card (Fin w.length)) ≤ mm := by
      rw [Fintype.card_fin]
      exact (JCx2.mmUser_parLev P0 j w.length).trans hmm'
    obtain ⟨K, hThm, -, -, hJ⟩ := hP Wp Wq (Fin w.length) (JC.parLev P0 j) (T.bs j).z (T.bs j).z' (T.bs j).π
      (T.bs j).π' X μ L st l0 (T.bs j) A mm hD hl0 hl0k rfl rfl rfl rfl hAu hmu
    choose Φ hΦK hΦ using fun a => hJ (v a) ε₁ hε₁ (hvn a).2.1 (hvn a).2.2
    rw [hform w v v Φ Φ ε₁ hε₁ hvn hvn hΦ hΦ]
    have hpos := ((hThm (D.positionted w) (hOK w hw)).2.2 0 (fun _ => 1) (fun _ => one_ne_zero)).2 Φ
      (fun a _ => hΦK a)
    have hpos' : 0 ≤ P5.form μ 0 (P5.act (P5.RRi L st 0 (D.positionted w)) Φ) Φ 0 :=
      hpos.trans_eq (JCx2.form_zero_indep μ _ _ _ _)
    exact mul_nonneg (by exact_mod_cast hC.le) hpos'

end Formalism.FourierDecayAlt.P

end

end
