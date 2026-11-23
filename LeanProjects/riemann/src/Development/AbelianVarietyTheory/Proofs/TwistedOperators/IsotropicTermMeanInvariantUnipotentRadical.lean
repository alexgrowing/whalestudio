import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilCompatibleOfSameSplittingCharacterStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WittTowerRestrictionUnipotentRadicalInvariantStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnipotentRadicalTargetPreservesIsotropicMeanStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaRestrictIsotropicQuotientWittTowerPropertieStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilDatumOfSplittingCharactersStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsEtaTildeUnramified
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfPartOneSubEInfSmul
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasChr
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.StarPurelyImaginaryEqNeg
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.EmbRelExistsUnique
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnipotentRadicalMeanEqVolumeMulRationalMeanStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.IsoTermMean
variable {D : D7}

theorem adj_eq {m n : ℕ} (A : Matrix (Fin m) (Fin n) D.host.E) : adj D A = (A.map star)ᵀ := rfl

theorem adj_ct {m n : ℕ} (A : Matrix (Fin m) (Fin n) D.host.E) : adj D A = Aᴴ := by
  ext i j; rfl

theorem adj_mul {m n p : ℕ} (A : Matrix (Fin m) (Fin n) D.host.E) (B : Matrix (Fin n) (Fin p) D.host.E) :
    adj D (A * B) = adj D B * adj D A := by
  simp only [adj_ct, Matrix.conjTranspose_mul]

theorem adj_adjS {m n : ℕ} (A : Matrix (Fin m) (Fin n) D.host.E) : adj D (adj D A) = A := by
  simp only [adj_ct, Matrix.conjTranspose_conjTranspose]

theorem adj_gram (V : HSp D) : adj D V.gram = V.gram := by
  ext i j; simp [adj_eq, GlobalTheory.DualPairCheck.gram_star]

theorem adj_one {m : ℕ} : adj D (1 : Matrix (Fin m) (Fin m) D.host.E) = 1 := by
  simp only [adj_ct, Matrix.conjTranspose_one]

theorem adj_zero {m n : ℕ} : adj D (0 : Matrix (Fin m) (Fin n) D.host.E) = 0 := by
  simp only [adj_ct, Matrix.conjTranspose_zero]

theorem frame_decomp (V V' : HSp D) {r : ℕ} (C C' : Matrix (Fin V.rank) (Fin r) D.host.E)
    (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E)
    (hCC : adj D C * V.gram * C = 0) (hBB : adj D B * V.gram * B = V'.gram) (hCB : adj D C * V.gram * B = 0)
    (hrk : V.rank = V'.rank + 2 * r)
    (h1 : adj D C * V.gram * C' = 1) (h2 : adj D C' * V.gram * C' = 0) (h3 : adj D C' * V.gram * B = 0) :
    C * (adj D C' * V.gram) + B * (V'.gram⁻¹ * adj D B * V.gram) + C' * (adj D C * V.gram) = 1 := by
  have hdet : IsUnit V'.gram.det := isUnit_iff_ne_zero.2 (GlobalTheory.AutFunCounterexample.gram_det_ne V')

  have h1' : adj D C' * V.gram * C = 1 := by
    have := congrArg (adj D) h1
    rwa [adj_mul, adj_mul, adj_adjS, adj_gram, adj_one, ← Matrix.mul_assoc] at this
  have hBC : adj D B * V.gram * C = 0 := by
    have := congrArg (adj D) hCB
    rwa [adj_mul, adj_mul, adj_adjS, adj_gram, adj_zero, ← Matrix.mul_assoc] at this
  have hBC' : adj D B * V.gram * C' = 0 := by
    have := congrArg (adj D) h3
    rwa [adj_mul, adj_mul, adj_adjS, adj_gram, adj_zero, ← Matrix.mul_assoc] at this
  let P : Matrix (Fin V.rank) (Fin r ⊕ (Fin V'.rank ⊕ Fin r)) D.host.E := Matrix.fromCols C (Matrix.fromCols B C')
  let Q : Matrix (Fin r ⊕ (Fin V'.rank ⊕ Fin r)) (Fin V.rank) D.host.E :=
    Matrix.fromRows (adj D C' * V.gram) (Matrix.fromRows (V'.gram⁻¹ * adj D B * V.gram) (adj D C * V.gram))
  have hPQ : P * Q = C * (adj D C' * V.gram) + B * (V'.gram⁻¹ * adj D B * V.gram) + C' * (adj D C * V.gram) := by
    simp only [P, Q, Matrix.fromCols_mul_fromRows, add_assoc]
  have hQP : Q * P = 1 := by
    simp only [P, Q, Matrix.fromRows_mul_fromCols, Matrix.fromRows_mul, Matrix.mul_fromCols]
    have e1 : V'.gram⁻¹ * adj D B * V.gram * B = 1 := by
      rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (adj D B), hBB, Matrix.nonsing_inv_mul _ hdet]
    have e2 : V'.gram⁻¹ * adj D B * V.gram * C = 0 := by
      rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (adj D B), hBC, Matrix.mul_zero]
    have e3 : V'.gram⁻¹ * adj D B * V.gram * C' = 0 := by
      rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (adj D B), hBC', Matrix.mul_zero]
    rw [h1', h3, h2, e1, e2, e3, hCC, hCB, h1]
    ext (i | i | i) (j | j | j) <;> simp [Matrix.one_apply]
  have hcard : Fintype.card (Fin r ⊕ (Fin V'.rank ⊕ Fin r)) = Fintype.card (Fin V.rank) := by
    simp [hrk]; ring
  rw [← hPQ]
  exact (Matrix.mul_eq_one_comm_of_equiv (Fintype.equivOfCardEq hcard.symm)).2 hQP

end GlobalTheory.IsoTermMean

namespace GlobalTheory.IsoTermMean
variable {D : D7}
local infixl:70 " ⬝ₘ " => HMul.hMul

theorem mt_mul_frame (V : HSp D) {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) D.host.E) {g : GA D V}
    (hg : g ∈ NI V C) : mt V g ⬝ₘ (C.map (incA D) : Matrix (Fin V.rank) (Fin r) (AE D)) = C.map (incA D) := by
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨h1, -, -⟩ := hx
    have h : (mt V x - 1) ⬝ₘ (C.map (incA D) : Matrix (Fin V.rank) (Fin r) (AE D)) = 0 := h1
    rwa [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at h
  | one => simp [Formalism.L2.Theta.mt]
  | mul x y _ _ hx hy =>
    have e : mt V (x * y) = mt V x * mt V y := by simp only [Formalism.L2.Theta.mt, map_mul, Units.val_mul]
    rw [e, Matrix.mul_assoc, hy, hx]
  | inv x _ hx =>
    have e : mt V x⁻¹ * mt V x = 1 := by
      simp only [Formalism.L2.Theta.mt, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]
    calc mt V x⁻¹ ⬝ₘ (C.map (incA D) : Matrix (Fin V.rank) (Fin r) (AE D))
          = mt V x⁻¹ ⬝ₘ (mt V x ⬝ₘ (C.map (incA D) : Matrix (Fin V.rank) (Fin r) (AE D))) := by rw [hx]
      _ = C.map (incA D) := by rw [← Matrix.mul_assoc, e, Matrix.one_mul]

theorem hO_iso (S T : HSp D) {s : ℕ} (L : Matrix (Fin T.rank) (Fin s) D.host.E) (hL : adj D L * T.gram * L = 0)
    (α β : Matrix (Fin s) (Fin S.rank) (AE D)) :
    hO S T ((L.map (incA D) : Matrix (Fin T.rank) (Fin s) (AE D)) ⬝ₘ α) ((L.map (incA D) : Matrix (Fin T.rank) (Fin s) (AE D)) ⬝ₘ β) = 0 := by
  have hM : (((L.map (incA D) : Matrix (Fin T.rank) (Fin s) (AE D)) ⬝ₘ β).map (cA D))ᵀ ⬝ₘ
      (T.gram.map (incA D) : Matrix (Fin T.rank) (Fin T.rank) (AE D)) ⬝ₘ ((L.map (incA D) : Matrix (Fin T.rank) (Fin s) (AE D)) ⬝ₘ α) = 0 := by
    have e1 : ((L.map (incA D) : Matrix (Fin T.rank) (Fin s) (AE D)) ⬝ₘ β).map (cA D) =
        ((L.map star).map (incA D) : Matrix (Fin T.rank) (Fin s) (AE D)) ⬝ₘ β.map (cA D) := by
      rw [Matrix.map_mul]; congr 1
    have e2 : (((L.map star).map (incA D) : Matrix (Fin T.rank) (Fin s) (AE D)))ᵀ ⬝ₘ
        (T.gram.map (incA D) : Matrix (Fin T.rank) (Fin T.rank) (AE D)) ⬝ₘ (L.map (incA D) : Matrix (Fin T.rank) (Fin s) (AE D)) =
        ((adj D L * T.gram * L).map (incA D) : Matrix (Fin s) (Fin s) (AE D)) := by
      rw [Matrix.map_mul, Matrix.map_mul, adj_eq, Matrix.transpose_map]
    rw [e1, Matrix.transpose_mul]
    calc _ = (β.map (cA D))ᵀ ⬝ₘ ((((L.map star).map (incA D) : Matrix (Fin T.rank) (Fin s) (AE D)))ᵀ ⬝ₘ
          (T.gram.map (incA D) : Matrix (Fin T.rank) (Fin T.rank) (AE D)) ⬝ₘ (L.map (incA D) : Matrix (Fin T.rank) (Fin s) (AE D))) ⬝ₘ α := by
          simp only [Matrix.mul_assoc]
      _ = 0 := by rw [e2, hL, Matrix.map_zero _ (map_zero _), Matrix.mul_zero, Matrix.zero_mul]
  have hent : ∀ b a, ∑ c, ∑ d, cA D (((L.map (incA D) : Matrix (Fin T.rank) (Fin s) (AE D)) ⬝ₘ β) c b) * incA D (T.gram c d) * ((L.map (incA D) : Matrix (Fin T.rank) (Fin s) (AE D)) ⬝ₘ α) d a = 0 := by
    intro b a
    have h := congrFun (congrFun hM b) a
    simp only [Matrix.mul_apply (M := _ * _), Matrix.mul_apply (M := Matrix.transpose _), Matrix.transpose_apply,
      Matrix.map_apply, Matrix.zero_apply, Finset.sum_mul] at h
    rw [Finset.sum_comm]
    exact h
  unfold hO
  refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ?_
  calc _ = incA D (S.gram⁻¹ a b) * ∑ c, ∑ d, cA D (((L.map (incA D) : Matrix (Fin T.rank) (Fin s) (AE D)) ⬝ₘ β) c b) * incA D (T.gram c d) *
        ((L.map (incA D) : Matrix (Fin T.rank) (Fin s) (AE D)) ⬝ₘ α) d a := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun c _ => ?_
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun d _ => ?_
        ring
    _ = 0 := by rw [hent b a, mul_zero]

theorem symplO_iso (S T : HSp D) {s : ℕ} (L : Matrix (Fin T.rank) (Fin s) D.host.E) (hL : adj D L * T.gram * L = 0)
    (α β : Matrix (Fin s) (Fin S.rank) (AE D)) :
    symplO S T ((L.map (incA D) : Matrix (Fin T.rank) (Fin s) (AE D)) ⬝ₘ α) ((L.map (incA D) : Matrix (Fin T.rank) (Fin s) (AE D)) ⬝ₘ β) = 0 := by
  rw [symplO, hO_iso S T L hL, mul_zero, map_zero]

end GlobalTheory.IsoTermMean

namespace GlobalTheory.IsoTermMean
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
variable {D : D7}
local infixl:70 " ⬝ₘ " => HMul.hMul

theorem mt_one (V : HSp D) : mt V 1 = 1 := by simp [Formalism.L2.Theta.mt]

theorem mt_mul_inv (V : HSp D) (g : GA D V) : mt V g * mt V g⁻¹ = 1 := by
  simp only [Formalism.L2.Theta.mt, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]

end GlobalTheory.IsoTermMean

namespace GlobalTheory.IsoTermMean
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
variable {D : D7}
local infixl:70 " ⬝ₘ " => HMul.hMul

theorem map_frame_decomp (V V' : HSp D) {r : ℕ} (C C' : Matrix (Fin V.rank) (Fin r) D.host.E)
    (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E) (hs : IsIsoSplit V V' C B) (h1 : adj D C * V.gram * C' = 1)
    (h2 : adj D C' * V.gram * C' = 0) (h3 : adj D C' * V.gram * B = 0) :
    (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) =
      (C.map (incA D) : Matrix (Fin V.rank) (Fin r) (AE D)) ⬝ₘ
        ((adj D C' * V.gram).map (incA D) : Matrix (Fin r) (Fin V.rank) (AE D)) +
      (B.map (incA D) : Matrix (Fin V.rank) (Fin V'.rank) (AE D)) ⬝ₘ
        ((V'.gram⁻¹ * adj D B * V.gram).map (incA D) : Matrix (Fin V'.rank) (Fin V.rank) (AE D)) +
      (C'.map (incA D) : Matrix (Fin V.rank) (Fin r) (AE D)) ⬝ₘ
        ((adj D C * V.gram).map (incA D) : Matrix (Fin r) (Fin V.rank) (AE D)) := by
  have e : C * (adj D C' * V.gram) + B * (V'.gram⁻¹ * adj D B * V.gram) + C' * (adj D C * V.gram) = 1 :=
    frame_decomp V V' C C' B hs.frame.2.2 hs.isom hs.orth hs.rank h1 h2 h3
  rw [← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_add _ (map_add (incA D)),
    ← Matrix.map_add _ (map_add (incA D)), e, Matrix.map_one _ (map_zero _) (map_one _)]

theorem decomp (V V' W : HSp D) {r s : ℕ} (C C' : Matrix (Fin V.rank) (Fin r) D.host.E)
    (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E)
    (hI : (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) =
      (C.map (incA D) : Matrix (Fin V.rank) (Fin r) (AE D)) ⬝ₘ
        ((adj D C' * V.gram).map (incA D) : Matrix (Fin r) (Fin V.rank) (AE D)) +
      (B.map (incA D) : Matrix (Fin V.rank) (Fin V'.rank) (AE D)) ⬝ₘ
        ((V'.gram⁻¹ * adj D B * V.gram).map (incA D) : Matrix (Fin V'.rank) (Fin V.rank) (AE D)) +
      (C'.map (incA D) : Matrix (Fin V.rank) (Fin r) (AE D)) ⬝ₘ
        ((adj D C * V.gram).map (incA D) : Matrix (Fin r) (Fin V.rank) (AE D)))
    (Lm : Matrix (Fin W.rank) (Fin s) (AE D)) (K : Matrix (Fin s) (Fin V.rank) (AE D))
    (M : Matrix (Fin V.rank) (Fin V.rank) (AE D))
    (hM : (M - 1) ⬝ₘ (C.map (incA D) : Matrix (Fin V.rank) (Fin r) (AE D)) = 0) :
    (Lm ⬝ₘ K ⬝ₘ M : WO V W) =
      isoPart V W C (Lm ⬝ₘ (K ⬝ₘ (M - 1) ⬝ₘ (C'.map (incA D) : Matrix (Fin V.rank) (Fin r) (AE D)))) +
        (midPart V V' W B (Lm ⬝ₘ (K ⬝ₘ (M - 1) ⬝ₘ (B.map (incA D) : Matrix (Fin V.rank) (Fin V'.rank) (AE D)))) +
          Lm ⬝ₘ K) := by
  have e : (Lm ⬝ₘ K ⬝ₘ M : WO V W) = Lm ⬝ₘ K + Lm ⬝ₘ K ⬝ₘ (M - 1) ⬝ₘ
      ((C.map (incA D) : Matrix (Fin V.rank) (Fin r) (AE D)) ⬝ₘ
        ((adj D C' * V.gram).map (incA D) : Matrix (Fin r) (Fin V.rank) (AE D)) +
      (B.map (incA D) : Matrix (Fin V.rank) (Fin V'.rank) (AE D)) ⬝ₘ
        ((V'.gram⁻¹ * adj D B * V.gram).map (incA D) : Matrix (Fin V'.rank) (Fin V.rank) (AE D)) +
      (C'.map (incA D) : Matrix (Fin V.rank) (Fin r) (AE D)) ⬝ₘ
        ((adj D C * V.gram).map (incA D) : Matrix (Fin r) (Fin V.rank) (AE D))) := by
    rw [← hI, Matrix.mul_one, Matrix.mul_sub, Matrix.mul_one]; abel
  rw [e]
  simp only [isoPart, midPart, Matrix.mul_add, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (M - 1) (C.map (incA D) : Matrix (Fin V.rank) (Fin r) (AE D)), hM]
  simp only [Matrix.zero_mul, Matrix.mul_zero, zero_add]
  abel

end GlobalTheory.IsoTermMean

namespace GlobalTheory.IsoTermMean
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
variable {D : D7}
local infixl:70 " ⬝ₘ " => HMul.hMul

theorem term_eq_aux (V V' W : HSp D) (r : ℕ) (C C' : Matrix (Fin V.rank) (Fin r) D.host.E)
    (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E) (hs : IsIsoSplit V V' C B) (h1 : adj D C * V.gram * C' = 1)
    (h2 : adj D C' * V.gram * C' = 0) (h3 : adj D C' * V.gram * B = 0)
    (ψ : AddChar (AF D.host.F) ℂ) (χS χT : (AE D)ˣ →* Circle) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ))
    (hω : IsWeilDatumO ψ V W χS χT ω) (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r))
    (hY : IsCovolOne (ratMx D W.rank r) μ 𝓨) (s : ℕ) (L : Matrix (Fin W.rank) (Fin s) D.host.E)
    (m : Matrix (Fin s) (Fin r) D.host.E) (hL : IsIsoFrame W L) (n : NI V C) (F : WO V W → ℂ)
    (hF : IsThetaFunO ψ V W F) (Lm : Matrix (Fin W.rank) (Fin s) (AE D)) (hLm : Lm = L.map (incA D))
    (K : Matrix (Fin s) (Fin V.rank) (AE D)) (hK : K = (m * adj D C' * V.gram).map (incA D)) :
    res V V' W C B μ 𝓨 (heisO ψ V W (Lm ⬝ₘ K) (ω ((n : GA D V), 1) F)) 0 =
      res V V' W C B μ 𝓨 (heisO ψ V W (Lm ⬝ₘ K) F)
        (Lm ⬝ₘ (K ⬝ₘ (mt V (n : GA D V) - 1) ⬝ₘ (B.map (incA D) : Matrix (Fin V.rank) (Fin V'.rank) (AE D)))) := by
  have hstd := hω.std
  have hLiso : adj D L * W.gram * L = 0 := hL.2.2
  have hres := (GlobalTheory.T.thetaRestrictIsotropicQuotient_wittTower_properties D V V' W r C B hs ψ hstd μ 𝓨 hY).1
  have hact : actO V W (n : GA D V) 1 (Lm ⬝ₘ K ⬝ₘ mt V (n : GA D V)) = Lm ⬝ₘ K := by
    simp only [actO, mt_one, Matrix.one_mul, Matrix.mul_assoc, mt_mul_inv, Matrix.mul_one]
  have hFu := GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hstd hF (Lm ⬝ₘ K ⬝ₘ mt V (n : GA D V))
  have step1 : heisO ψ V W (Lm ⬝ₘ K) (ω ((n : GA D V), 1) F) =
      ω ((n : GA D V), 1) (heisO ψ V W (Lm ⬝ₘ K ⬝ₘ mt V (n : GA D V)) F) := by
    rw [hω.om_heis (n : GA D V) 1 _ F hF, hact]
  have step2 := GlobalTheory.T.wittTower_restriction_unipotentRadical_invariant D V V' W r C B hs ψ χS χT ω hω μ 𝓨 hY n _ hFu
  have hM : (mt V (n : GA D V) - 1) ⬝ₘ (C.map (incA D) : Matrix (Fin V.rank) (Fin r) (AE D)) = 0 := by
    rw [Matrix.sub_mul, mt_mul_frame V C n.2, Matrix.one_mul, sub_self]
  have hdec := decomp V V' W C C' B (map_frame_decomp V V' C C' B hs h1 h2 h3) Lm K (mt V (n : GA D V)) hM
  have o1 : symplO V W (isoPart V W C (Lm ⬝ₘ (K ⬝ₘ (mt V (n : GA D V) - 1) ⬝ₘ
      (C'.map (incA D) : Matrix (Fin V.rank) (Fin r) (AE D)))))
      (midPart V V' W B (Lm ⬝ₘ (K ⬝ₘ (mt V (n : GA D V) - 1) ⬝ₘ
        (B.map (incA D) : Matrix (Fin V.rank) (Fin V'.rank) (AE D)))) + Lm ⬝ₘ K) = 0 := by
    simp only [isoPart, midPart, Matrix.mul_assoc, ← Matrix.mul_add]
    rw [hLm]; exact symplO_iso V W L hLiso _ _
  have o2 : symplO V W (midPart V V' W B (Lm ⬝ₘ (K ⬝ₘ (mt V (n : GA D V) - 1) ⬝ₘ
        (B.map (incA D) : Matrix (Fin V.rank) (Fin V'.rank) (AE D))))) (Lm ⬝ₘ K) = 0 := by
    simp only [midPart, Matrix.mul_assoc]
    rw [hLm]; exact symplO_iso V W L hLiso _ _
  have hF0 := GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hstd hF (Lm ⬝ₘ K)
  have hF1 := GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hstd hF0 (midPart V V' W B (Lm ⬝ₘ (K ⬝ₘ (mt V (n : GA D V) - 1) ⬝ₘ
        (B.map (incA D) : Matrix (Fin V.rank) (Fin V'.rank) (AE D)))))
  rw [step1, step2, hdec, GlobalTheory.SplitScalar.heisO_add_of_orth ψ V W o1, GlobalTheory.SplitScalar.heisO_add_of_orth ψ V W o2,
    (hres _ hF1).2.2.2, (hres _ hF0).2.2.1]
  simp only [heisO, symplOH, GlobalTheory.SplitScalar.symplO_zero_left, mul_zero, AddChar.map_zero_eq_one, one_mul, zero_add]

end GlobalTheory.IsoTermMean

namespace GlobalTheory.IsoTermMean
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
variable {D : D7}
local infixl:70 " ⬝ₘ " => HMul.hMul

theorem iso_read_periodic (V' W : HSp D) (ψ : AddChar (AF D.host.F) ℂ) {s : ℕ} (L : Matrix (Fin W.rank) (Fin s) D.host.E)
    (hL : IsIsoFrame W L) (G : WO V' W → ℂ) (hG : IsThetaFunO ψ V' W G) :
    Continuous (fun a : Mx D s V'.rank => G ((L.map (incA D) : Matrix (Fin W.rank) (Fin s) (AE D)) ⬝ₘ a)) ∧
    ∀ γ ∈ ratMx D s V'.rank, ∀ a : Mx D s V'.rank,
      G ((L.map (incA D) : Matrix (Fin W.rank) (Fin s) (AE D)) ⬝ₘ (γ + a)) =
        G ((L.map (incA D) : Matrix (Fin W.rank) (Fin s) (AE D)) ⬝ₘ a) := by
  refine ⟨hG.cont.comp (continuous_const.matrix_mul continuous_id), ?_⟩
  intro γ hγ a
  obtain ⟨γ₀, rfl⟩ := hγ
  have hLiso : adj D L * W.gram * L = 0 := hL.2.2
  have e : ((L.map (incA D) : Matrix (Fin W.rank) (Fin s) (AE D)) ⬝ₘ
      ((incA D).toAddMonoidHom.mapMatrix γ₀ : Mx D s V'.rank)) = ratW W V' (L * γ₀) := by
    simp only [ratW, Matrix.map_mul]; rfl
  rw [Matrix.mul_add, e, hG.quasi, symplOH]
  have h0 : symplO V' W (ratW W V' (L * γ₀)) ((L.map (incA D) : Matrix (Fin W.rank) (Fin s) (AE D)) ⬝ₘ a) = 0 := by
    rw [← e]; exact symplO_iso V' W L hLiso _ _
  rw [h0, mul_zero, neg_zero, AddChar.map_zero_eq_one, one_mul]

theorem heis_comm_radical (V W : HSp D) (ψ : AddChar (AF D.host.F) ℂ) (χS χT : (AE D)ˣ →* Circle)
    (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (hω : IsWeilDatumO ψ V W χS χT ω) {s : ℕ}
    (L : Matrix (Fin W.rank) (Fin s) D.host.E) (K : Matrix (Fin s) (Fin V.rank) (AE D)) (n' : NI W L)
    (f : WO V W → ℂ) (hf : IsThetaFunO ψ V W f) :
    heisO ψ V W ((L.map (incA D) : Matrix (Fin W.rank) (Fin s) (AE D)) ⬝ₘ K) (ω (1, (n' : GA D W)) f) =
      ω (1, (n' : GA D W)) (heisO ψ V W ((L.map (incA D) : Matrix (Fin W.rank) (Fin s) (AE D)) ⬝ₘ K) f) := by
  rw [hω.om_heis 1 (n' : GA D W) _ f hf]
  congr 1
  simp only [actO, inv_one, mt_one, Matrix.mul_one, ← Matrix.mul_assoc, mt_mul_frame W L n'.2]

theorem mean_isoTerm_invariant : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C C' : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → adj D C * V.gram * C' = 1 → adj D C' * V.gram * C' = 0 → adj D C' * V.gram * B = 0 → ∀ (ψ : AddChar (AF D.host.F) ℂ) (χS χT : (AE D)ˣ →* Circle) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)), IsWeilDatumO ψ V W χS χT ω → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (ratMx D W.rank r) μ 𝓨 → ∀ (κ : Measure (NI V C)) (𝓝 : Set (NI V C)), κ.IsHaarMeasure → IsFundamentalDomain (NIQ V C) 𝓝 κ → ∀ (s : ℕ) (L : Matrix (Fin W.rank) (Fin s) D.host.E) (m : Matrix (Fin s) (Fin r) D.host.E), IsIsoFrame W L → m.rank = s → ∀ (n' : NI W L) f, IsThetaFunO ψ V W f → ∫ n in 𝓝, res V V' W C B μ 𝓨 (heisO ψ V W (isoPart V W C' (Matrix.map (L * m) (incA D))) (ω ((n : GA D V), (n' : GA D W)) f)) 0 ∂κ = ∫ n in 𝓝, res V V' W C B μ 𝓨 (heisO ψ V W (isoPart V W C' (Matrix.map (L * m) (incA D))) (ω ((n : GA D V), 1) f)) 0 ∂κ := by
  intro D V V' W r C C' B hs h1 h2 h3 ψ χS χT ω hω μ 𝓨 hY κ 𝓝 hκ h𝓝 s L m hL hm n' f hf
  have hstd := hω.std
  obtain ⟨ω', hω'⟩ := GlobalTheory.T.exists_weilDatum_of_splittingCharacters D ψ hstd V' W χS χT (GlobalTheory.WeilParts.exists_isEtaTilde_unramified D) hω.hecS
    hω.hecT (Formalism.L2.Theta.resEta_parity hω.resS (by rw [hs.rank]; omega)) hω.resT
  have hcomp := GlobalTheory.T.weilCompatible_of_sameSplittingCharacter D V V' W r C B hs ψ χS χT χT ω ω' hω hω' μ 𝓨 hY
  obtain ⟨μ', 𝓐, hA, hmean⟩ := GlobalTheory.T.unipotentRadicalMean_eq_volume_mul_rationalMean D V V' r C C' B hs h1 h2 h3 κ 𝓝 hκ h𝓝 s m hm
  have hres := (GlobalTheory.T.thetaRestrictIsotropicQuotient_wittTower_properties D V V' W r C B hs ψ hstd μ 𝓨 hY).1
  have hw₀ : isoPart V W C' (Matrix.map (L * m) (incA D)) =
      (L.map (incA D) : Matrix (Fin W.rank) (Fin s) (AE D)) ⬝ₘ
        ((m * adj D C' * V.gram).map (incA D) : Matrix (Fin s) (Fin V.rank) (AE D)) := by
    simp only [isoPart, Matrix.map_mul, Matrix.mul_assoc]
  rw [hw₀]
  have hsplit : ∀ n : NI V C, ω ((n : GA D V), (n' : GA D W)) f = ω ((n : GA D V), 1) (ω (1, (n' : GA D W)) f) := by
    intro n
    rw [show (((n : GA D V), (n' : GA D W)) : GA D V × GA D W) = ((n : GA D V), 1) * (1, (n' : GA D W)) by simp,
      map_mul, Module.End.mul_apply]
  have hf1 : IsThetaFunO ψ V W (ω (1, (n' : GA D W)) f) := hω.om_pres _ f hf
  have hf0 := GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hstd hf ((L.map (incA D) : Matrix (Fin W.rank) (Fin s) (AE D)) ⬝ₘ
        ((m * adj D C' * V.gram).map (incA D) : Matrix (Fin s) (Fin V.rank) (AE D)))
  have hG0 := (hres _ hf0).2.1
  have hG1 : res V V' W C B μ 𝓨 (heisO ψ V W ((L.map (incA D) : Matrix (Fin W.rank) (Fin s) (AE D)) ⬝ₘ
        ((m * adj D C' * V.gram).map (incA D) : Matrix (Fin s) (Fin V.rank) (AE D))) (ω (1, (n' : GA D W)) f)) =
      ω' (1, (n' : GA D W)) (res V V' W C B μ 𝓨 (heisO ψ V W ((L.map (incA D) : Matrix (Fin W.rank) (Fin s) (AE D)) ⬝ₘ
        ((m * adj D C' * V.gram).map (incA D) : Matrix (Fin s) (Fin V.rank) (AE D))) f)) := by
    rw [heis_comm_radical V W ψ χS χT ω hω L _ n' f hf, hcomp _ _ hf0]
  have hG1' := hω'.om_pres (1, (n' : GA D W)) _ hG0
  have p0 := iso_read_periodic V' W ψ L hL _ hG0
  have p1 := iso_read_periodic V' W ψ L hL _ hG1'
  calc _ = ∫ n in 𝓝, ω' (1, (n' : GA D W)) (res V V' W C B μ 𝓨 (heisO ψ V W ((L.map (incA D) : Matrix (Fin W.rank) (Fin s) (AE D)) ⬝ₘ
          ((m * adj D C' * V.gram).map (incA D) : Matrix (Fin s) (Fin V.rank) (AE D))) f))
          ((L.map (incA D) : Matrix (Fin W.rank) (Fin s) (AE D)) ⬝ₘ
            (((m * adj D C' * V.gram).map (incA D) : Matrix (Fin s) (Fin V.rank) (AE D)) ⬝ₘ (mt V (n : GA D V) - 1) ⬝ₘ
              (B.map (incA D) : Matrix (Fin V.rank) (Fin V'.rank) (AE D)))) ∂κ := by
        congr 1; funext n
        rw [hsplit n, term_eq_aux V V' W r C C' B hs h1 h2 h3 ψ χS χT ω hω μ 𝓨 hY s L m hL n _ hf1 _ rfl _ rfl, hG1]
    _ = ((κ 𝓝).toReal : ℂ) * ∫ a in 𝓐, ω' (1, (n' : GA D W)) (res V V' W C B μ 𝓨 (heisO ψ V W
          ((L.map (incA D) : Matrix (Fin W.rank) (Fin s) (AE D)) ⬝ₘ
          ((m * adj D C' * V.gram).map (incA D) : Matrix (Fin s) (Fin V.rank) (AE D))) f))
          ((L.map (incA D) : Matrix (Fin W.rank) (Fin s) (AE D)) ⬝ₘ a) ∂μ' := hmean _ p1.1 p1.2
    _ = ((κ 𝓝).toReal : ℂ) * ∫ a in 𝓐, (res V V' W C B μ 𝓨 (heisO ψ V W
          ((L.map (incA D) : Matrix (Fin W.rank) (Fin s) (AE D)) ⬝ₘ
          ((m * adj D C' * V.gram).map (incA D) : Matrix (Fin s) (Fin V.rank) (AE D))) f))
          ((L.map (incA D) : Matrix (Fin W.rank) (Fin s) (AE D)) ⬝ₘ a) ∂μ' := by
        rw [GlobalTheory.T.unipotentRadical_target_preserves_isotropic_mean D V' W s L hL ψ χS χT ω' hω' μ' 𝓐 hA n' _ hG0]
    _ = ∫ n in 𝓝, (res V V' W C B μ 𝓨 (heisO ψ V W
          ((L.map (incA D) : Matrix (Fin W.rank) (Fin s) (AE D)) ⬝ₘ
          ((m * adj D C' * V.gram).map (incA D) : Matrix (Fin s) (Fin V.rank) (AE D))) f))
          ((L.map (incA D) : Matrix (Fin W.rank) (Fin s) (AE D)) ⬝ₘ
            (((m * adj D C' * V.gram).map (incA D) : Matrix (Fin s) (Fin V.rank) (AE D)) ⬝ₘ (mt V (n : GA D V) - 1) ⬝ₘ
              (B.map (incA D) : Matrix (Fin V.rank) (Fin V'.rank) (AE D)))) ∂κ := (hmean _ p0.1 p0.2).symm
    _ = _ := by
        refine (congrArg (fun φ : NI V C → ℂ => ∫ n in 𝓝, φ n ∂κ) (funext fun n => ?_)).symm
        exact term_eq_aux V V' W r C C' B hs h1 h2 h3 ψ χS χT ω hω μ 𝓨 hY s L m hL n f hf
          (L.map (incA D)) rfl ((m * adj D C' * V.gram).map (incA D)) rfl

end GlobalTheory.IsoTermMean
