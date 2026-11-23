import Mathlib
import Formalism.LocalToGlobal.KernelLattices.ColumnData.KerEntHyp
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.PeriodLatticeFinitelyGenerated
import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem

open NumberField Formalism.BasicNotions Classical

noncomputable section

namespace Formalism.L2.Ker

open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.G

theorem canInv_spec (D : D7) (w : D.what₂.places.Pl) (N : ℕ) (nu : Bool × HH D → YoungDiagram) (F : FrP D w N → Cw D w)
    (hF : F ∈ LinearMap.range (canM D w N nu)) : canM D w N nu (canInv D w N nu F) = F := by
  have hex : ∃ g : (FrP D w N → Cw D w) →ₗ[Cw D w] Module.Dual (Cw D w) (MvPolynomial ((Bool × HH D) × ℕ × Fin N) (Cw D w)),
      ∀ F ∈ LinearMap.range (canM D w N nu), canM D w N nu (g F) = F := by
    have : Module.Free (Cw D w) (LinearMap.range (canM D w N nu)) := Module.Free.of_divisionRing _ _
    have : Module.Projective (Cw D w) (LinearMap.range (canM D w N nu)) := Module.Projective.of_free
    obtain ⟨r, hr⟩ := (canM D w N nu).rangeRestrict.exists_rightInverse_of_surjective (LinearMap.range_rangeRestrict _)
    obtain ⟨g, hg⟩ := LinearMap.exists_extend r
    refine ⟨g, fun F hF => ?_⟩
    have h1 : g F = r ⟨F, hF⟩ := LinearMap.congr_fun hg ⟨F, hF⟩
    rw [h1]
    exact congrArg Subtype.val (LinearMap.congr_fun hr ⟨F, hF⟩)
  exact Classical.epsilon_spec hex F hF

section Obj

variable {D : D7} (P : Examples₂.EntPl D) (O : ∀ u μ, GL3Theta.LiftObj D (D.chTw u μ)) (B : PlaceMatrixFamily D)

theorem basC_spec (h : BasEx P O) (u : D.what₂.Word) (μ : D.what₂.Tup) (w : D.what₂.places.Pl) (i : ℕ) (hi : i ≤ D.R.m) (c : (D.chTw u μ).cls i)
    (τ : D.what₂.Tau) : IsBasC P O u μ w i c τ (basC P O u μ w i c τ) :=
  Classical.epsilon_spec (h u μ w i hi c τ)

theorem basC_ok (h : BasEx P O) : BasOk P O (basC P O) := fun u μ w i hi c τ => (basC_spec P O h u μ w i hi c τ).1

theorem secC_spec (u : D.what₂.Word) (μ : D.what₂.Tup) (i : ℕ) (v : ValQ O u μ i) : (LinearMap.ker (evP O u μ i)).mkQ (secC O u μ i v) = v :=
  LinearMap.congr_fun (Classical.choose_spec ((LinearMap.ker (evP O u μ i)).mkQ.exists_rightInverse_of_surjective (Submodule.range_mkQ _))) v

theorem evC_sec (u : D.what₂.Word) (μ : D.what₂.Tup) (i : ℕ) (v : ValQ O u μ i) : evC O u μ i v = evP O u μ i (secC O u μ i v) := by
  conv_lhs => rw [← secC_spec O u μ i v]
  rfl

theorem embLL_alg (w : D.what₂.places.Pl) (x : D.what₂.LL) : D.what₂.embLL x ∈ Qbar := by
  obtain ⟨_, _, h, _⟩ := Examples₂.exists_placeEmb D w
  exact (h x).choose

def jL (w : D.what₂.places.Pl) : D.what₂.LL →+* Qbar := D.what₂.embLL.codRestrict Qbar (embLL_alg w)

theorem alg_jL (w : D.what₂.places.Pl) : (algebraMap Qbar ℂ).comp (jL w) = D.what₂.embLL := RingHom.ext fun _ => rfl

theorem lam_jL (w : D.what₂.places.Pl) : (P.lam w).comp (jL w) = P.iL w :=
  RingHom.ext fun x => (P.iL_lam' w x (embLL_alg w x)).symm

theorem eval_detP {K S : Type} [Field K] [CommRing S] (f : K →+* S) {N : ℕ} (y : D.what₂.Tau → Matrix (Fin N) (Fin N) S) (τ : D.what₂.Tau) :
    MvPolynomial.eval (fun k : GL3Theta.FrV D N => y k.1 k.2.1 k.2.2) (MvPolynomial.map f (frDet K N τ)) = (y τ).det := by
  have h := RingHom.map_det ((MvPolynomial.eval (fun k : GL3Theta.FrV D N => y k.1 k.2.1 k.2.2)).comp (MvPolynomial.map f))
    (Matrix.of fun a k : Fin N => (MvPolynomial.X (τ, a, k) : MvPolynomial (GL3Theta.FrV D N) K))
  refine h.trans (congrArg Matrix.det ?_)
  ext a k
  simp

variable {Dx : DivX D} {Tw : TwForms D}

theorem src_sharp (hL : TwLe D) (u : D.what₂.Word) (μ : D.what₂.Tup) (w : D.what₂.places.Pl) (i : ℕ) (hi : i < D.R.m) (v : ValQ O u μ i) :
    (D.chTw u μ).sharp i (evC O u μ i v) = fun y => GL3Theta.evFr D (MvPolynomial.map (algebraMap Qbar ℂ)
      (MvPolynomial.map (jL w) (srcPol u μ i (secC O u μ i v : MvPolynomial (GL3Theta.FrV D (D.R.N i)) D.what₂.LL)))) ((O u μ).frm i y) := by
  funext y
  rw [evC_sec, MvPolynomial.map_map, alg_jL]
  show (∏ τ, ((D.chTw u μ).de i y τ) ^ ((D.chTw u μ).sSharp i τ)) * ((∏ τ, ((D.chTw u μ).de i y τ) ^ (-(twB D u μ i τ))) *
    GL3Theta.evFr D (MvPolynomial.map D.what₂.embLL (secC O u μ i v : MvPolynomial (GL3Theta.FrV D (D.R.N i)) D.what₂.LL)) ((O u μ).frm i y)) = _
  unfold srcPol GL3Theta.evFr
  rw [map_mul, map_mul, map_prod, map_prod, ← mul_assoc, ← Finset.prod_mul_distrib, mul_comm]
  congr 1
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [map_pow, map_pow, eval_detP, ← (O u μ).frm_de i hi.le y τ, ← zpow_add₀ ((D.chTw u μ).de_ne i y τ), ← zpow_natCast,
    Int.toNat_of_nonneg (sub_nonneg.2 (hL u μ i hi τ)), sub_eq_add_neg]

def kfTieC (hB : BasOk P O B) (hS : CanS P B) (hT : CanT P B) (hL : TwLe D) (h : KerEntHyp P O B Dx Tw) (u : D.what₂.Word) (μ : D.what₂.Tup)
    (w : D.what₂.places.Pl) : GL3Columns.KFTie (kerEntC P O B h) (O u μ) w where
  B := fun i c τ => B u μ w i c τ
  B_bas := fun i hi c τ => hB u μ w i hi c τ
  c0 := fun _ _ _ _ => 1
  unitAbs_eq_one := fun _ _ _ _ => norm_one
  th := fun _ _ _ _ => rfl
  prS_can := fun i hi c (v : ValQ O u μ i) => by
    refine ⟨MvPolynomial.map (jL w) (srcPol u μ i (secC O u μ i v : MvPolynomial (GL3Theta.FrV D (D.R.N i)) D.what₂.LL)),
      src_sharp O hL u μ w i hi v, fun y => ?_⟩
    have h1 := congrFun (canInv_spec D w (D.R.N i) (nuD D u i) _ (hS u μ w i hi c (secC O u μ i v))) y
    refine h1.trans ?_
    rw [MvPolynomial.map_map]
    show _ = _ * MvPolynomial.eval _ (MvPolynomial.map ((P.lam w).comp (jL w)) _)
    rw [lam_jL]
    rfl
  prT_can := fun i hi c' (v' : ValQ O u μ (i + 1)) => by
    refine ⟨MvPolynomial.map (jL w) (secC O u μ (i + 1) v' : MvPolynomial (GL3Theta.FrV D (D.R.N (i + 1))) D.what₂.LL),
      tgtPh P O B u μ w i c' v', fun y' => ?_, fun _ => rfl, fun y' => ?_⟩
    · rw [MvPolynomial.map_map, alg_jL]
      show _ * evC O u μ (i + 1) v' y' = _
      rw [evC_sec]
      show (∏ τ, ((D.chTw u μ).de (i + 1) y' τ) ^ ((D.chTw u μ).sDiv i τ)) * ((∏ τ, ((D.chTw u μ).de (i + 1) y' τ) ^ (-((D.chTw u μ).sDiv i τ))) * _) = _
      rw [← mul_assoc, ← Finset.prod_mul_distrib, Finset.prod_eq_one, one_mul]
      intro τ _
      rw [← zpow_add₀ ((D.chTw u μ).de_ne (i + 1) y' τ), add_neg_cancel, zpow_zero]
    · have h1 := congrFun (canInv_spec D w (D.R.N (i + 1)) (nuD D u i) _ (hT u μ w i hi c' (secC O u μ (i + 1) v'))) y'
      refine h1.trans ?_
      rw [MvPolynomial.map_map]
      show _ = _ * MvPolynomial.eval _ (MvPolynomial.map ((P.lam w).comp (jL w)) _)
      rw [lam_jL]
      rfl

theorem lamC_ne {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) {x : ℂ} (hx : x ∈ Qbar) (h0 : x ≠ 0) : lamC lam x ≠ 0 := by
  unfold lamC
  rw [dif_pos hx]
  exact (map_ne_zero lam).2 fun h => h0 (congrArg Subtype.val h)

theorem unF_ne (hB : BasOk P O B) (u : D.what₂.Word) (μ : D.what₂.Tup) (hR : GL3Columns.RhoAlg (O u μ)) (w : D.what₂.places.Pl) (i : ℕ) (hi : i < D.R.m)
    (c : (D.chTw u μ).cls i) (c' : (D.chTw u μ).cls (i + 1)) : unF P O B u μ w i c c' ≠ 0 := by
  unfold unF
  refine mul_ne_zero (mul_ne_zero (lamC_ne _ ((hR i hi).1 c) (Units.ne_zero _)) ?_) (mul_ne_zero (lamC_ne _ ((hR i hi).2 c') (Units.ne_zero _)) ?_)
  · exact Finset.prod_ne_zero_iff.2 fun τ _ => zpow_ne_zero _ (hB u μ w i hi.le c τ).1
  · exact Finset.prod_ne_zero_iff.2 fun τ _ => zpow_ne_zero _ (hB u μ w (i + 1) hi c' τ).1

theorem kfTieC_un (hB : BasOk P O B) (hS : CanS P B) (hT : CanT P B) (hL : TwLe D) (h : KerEntHyp P O B Dx Tw) (u : D.what₂.Word) (μ : D.what₂.Tup)
    (hR : GL3Columns.RhoAlg (O u μ)) (w : D.what₂.places.Pl) : (kfTieC P O B hB hS hT hL h u μ w).UnIs := by
  intro i hi c c'
  show unC P O B u μ w i c c' = _
  unfold unC
  rw [if_neg (unF_ne P O B hB u μ hR w i hi c c')]
  unfold GL3Columns.KFTie.un GL3Columns.KFTie.cK
  simp only [kfTieC, one_pow, Finset.prod_const_one, inv_one, one_mul]
  rfl

end Obj

theorem twLe (D : D7) : TwLe D := by
  intro u μ i hi τ
  cases i with
  | zero => exact le_rfl
  | succ j =>
    show (D.chTw u μ).sDiv j τ ≤ (D.chTw u μ).sSharp (j + 1) τ
    have h1 := (D.chTw u μ).sDiv_eq j (by omega) τ
    have h2 := (D.chTw u μ).sSharp_eq (j + 1) hi τ
    have g1 := (D.hcW u τ).gap_be ⟨j + 1, hi⟩
    have g2 := (D.hcW u τ).gap_eb ⟨j, by omega⟩ hi
    have h3 : (((D.chTw u μ).sDiv j τ : ℤ) : ℚ) ≤ (((D.chTw u μ).sSharp (j + 1) τ : ℤ) : ℚ) := by
      rw [h1, h2]
      unfold sExp sExp' Ranks.N
      have ht : (0 : ℚ) ≤ (D.R.t : ℚ) := Nat.cast_nonneg _
      simp only [Nat.add_sub_cancel]
      push_cast
      nlinarith
    exact_mod_cast h3

theorem wtPol_mul_det {K : Type} [Field K] {ι : Type} [Fintype ι] {n : ℕ} (ν : ι → Fin n → ℕ) (k : ι → ℕ) {Q : Formalism.L2.DIV.Pol K ι n} (hQ : Q ∈ WtPol K ν) :
    Q * ∏ τ, frDet K n τ ^ k τ ∈ WtPol K (fun τ r => ν τ r + k τ) := by
  intro β hβ
  rw [map_mul, hQ β hβ, map_prod]
  simp only [map_pow, colSub_frDet β hβ, smul_pow]
  rw [Finset.prod_smul, smul_mul_smul_comm]
  congr 1
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [← Finset.prod_pow, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun x _ => (pow_add _ _ _).symm

theorem srcPol_zero {D : D7} (u : D.what₂.Word) (μ : D.what₂.Tup) (v : polV D u 0) :
    srcPol u μ 0 (v : MvPolynomial (GL3Theta.FrV D (D.R.N 0)) D.what₂.LL) ∈ WtPol D.what₂.LL (nuT D u 0) := by
  have e0 : ∀ τ, ((D.chTw u μ).sSharp 0 τ - twB D u μ 0 τ).toNat = 0 := fun τ => by
    show ((D.chTw u μ).sSharp 0 τ - (D.chTw u μ).sSharp 0 τ).toNat = 0
    simp
  have h := wtPol_mul_det (nuT D u 0) (fun τ => ((D.chTw u μ).sSharp 0 τ - twB D u μ 0 τ).toNat) v.2
  simp only [e0, add_zero] at h
  unfold srcPol
  simp only [e0]
  exact h

theorem srcPol_succ {D : D7} (u : D.what₂.Word) (μ : D.what₂.Tup) (j : ℕ) (v : polV D u (j + 1)) :
    srcPol u μ (j + 1) (v : MvPolynomial (GL3Theta.FrV D (D.R.N (j + 1))) D.what₂.LL) ∈
      WtPol D.what₂.LL (fun τ r => extNu (D.R.N (j + 1)) (nuT D u j) τ r + ((D.chTw u μ).sSharp (j + 1) τ - (D.chTw u μ).sDiv j τ).toNat) :=
  wtPol_mul_det (extNu (D.R.N (j + 1)) (nuT D u j)) (fun τ => ((D.chTw u μ).sSharp (j + 1) τ - (D.chTw u μ).sDiv j τ).toNat) v.2

theorem nuStep (D : D7) (u : D.what₂.Word) (μ : D.what₂.Tup) (j : ℕ) (hj : j + 1 < D.R.m) (τ : D.what₂.Tau) (r : Fin (D.R.N (j + 1))) :
    extNu (D.R.N (j + 1)) (nuT D u j) τ r + ((D.chTw u μ).sSharp (j + 1) τ - (D.chTw u μ).sDiv j τ).toNat = nuT D u (j + 1) τ r := by
  have hle : (D.chTw u μ).sDiv j τ ≤ (D.chTw u μ).sSharp (j + 1) τ := twLe D u μ (j + 1) hj τ
  have h1 := (D.chTw u μ).sDiv_eq j (by omega) τ
  have h2 := (D.chTw u μ).sSharp_eq (j + 1) hj τ
  have hn : ((((D.chTw u μ).sSharp (j + 1) τ - (D.chTw u μ).sDiv j τ).toNat : ℕ) : ℝ) =
      (((D.hcW u τ).e ⟨j + 1, hj⟩ : ℚ) : ℝ) - (((D.hcW u τ).e ⟨j, by omega⟩ : ℚ) : ℝ) - ((D.R.t : ℝ) + 1) := by
    have a1 : ((((D.chTw u μ).sSharp (j + 1) τ - (D.chTw u μ).sDiv j τ).toNat : ℕ) : ℤ) =
        (D.chTw u μ).sSharp (j + 1) τ - (D.chTw u μ).sDiv j τ := Int.toNat_of_nonneg (sub_nonneg.2 hle)
    have a2 : ((((D.chTw u μ).sSharp (j + 1) τ - (D.chTw u μ).sDiv j τ).toNat : ℕ) : ℚ) =
        (D.hcW u τ).e ⟨j + 1, hj⟩ - (D.hcW u τ).e ⟨j, by omega⟩ - ((D.R.t : ℚ) + 1) := by
      have a3 : ((((D.chTw u μ).sSharp (j + 1) τ - (D.chTw u μ).sDiv j τ).toNat : ℕ) : ℚ) =
          (((D.chTw u μ).sSharp (j + 1) τ : ℤ) : ℚ) - (((D.chTw u μ).sDiv j τ : ℤ) : ℚ) := by exact_mod_cast a1
      rw [a3, h1, h2]
      unfold sExp sExp' Ranks.N
      simp only [Nat.add_sub_cancel]
      push_cast
      ring
    exact_mod_cast a2
  have hR := (nu_t_identity D u (j + 1) hj τ r).1
  have w2 : DV.wSz D (j + 1 + 1) τ = (((D.hcW u τ).e ⟨j + 1, hj⟩ : ℚ) : ℝ) := by
    unfold DV.wSz
    rw [dif_pos ⟨by omega, by omega⟩, D.hcW_e u τ]
    rfl
  have w1 : DV.wSz D (j + 1) τ = (((D.hcW u τ).e ⟨j, by omega⟩ : ℚ) : ℝ) := by
    unfold DV.wSz
    rw [dif_pos ⟨by omega, by omega⟩, D.hcW_e u τ]
    rfl
  have key : ((extNu (D.R.N (j + 1)) (nuT D u j) τ r : ℕ) : ℝ) +
      ((((D.chTw u μ).sSharp (j + 1) τ - (D.chTw u μ).sDiv j τ).toNat : ℕ) : ℝ) = ((nuT D u (j + 1) τ r : ℕ) : ℝ) := by
    rw [hR, hn]
    unfold DV.nuRow
    rw [w2]
    by_cases hr : r.1 < D.R.N j
    · have hL := (nu_t_identity D u j (by omega) τ ⟨r.1, hr⟩).1
      unfold extNu
      rw [dif_pos hr, hL]
      unfold DV.nuRow
      rw [w1]
      simp only [Nat.add_sub_cancel]
      unfold Ranks.N
      push_cast
      ring
    · unfold extNu
      rw [dif_neg hr]
      have hr2 := r.2
      unfold Ranks.N at hr hr2
      obtain ⟨a, ha⟩ : ∃ a, r.1 = D.R.k + j * (D.R.t + 1) + a := ⟨r.1 - (D.R.k + j * (D.R.t + 1)), by omega⟩
      have hat : a < D.R.t + 1 := by
        rw [ha, Nat.add_mul] at hr2
        omega
      have hsub : r.1 - D.R.k = a + j * (D.R.t + 1) := by omega
      have hdiv : (r.1 - D.R.k) / (D.R.t + 1) = j := by
        rw [hsub, Nat.add_mul_div_right _ _ (Nat.succ_pos _), Nat.div_eq_of_lt hat, Nat.zero_add]
      have hmod : (r.1 - D.R.k) % (D.R.t + 1) = a := by
        rw [hsub, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hat]
      have hb : (r.1 - D.R.k) / (D.R.t + 1) < D.R.m := by rw [hdiv]; omega
      have he : (D.hcW u τ).e ⟨(r.1 - D.R.k) / (D.R.t + 1), hb⟩ = (D.hcW u τ).e ⟨j, by omega⟩ := congrArg _ (Fin.ext hdiv)
      unfold DV.srcPar
      rw [dif_neg (by omega), dif_pos hb, he, hmod]
      simp only [Nat.add_sub_cancel]
      unfold Ranks.N
      rw [ha]
      push_cast
      ring
  exact_mod_cast key

theorem srcPol_mem {D : D7} (u : D.what₂.Word) (μ : D.what₂.Tup) (i : ℕ) (hi : i < D.R.m) (v : polV D u i) :
    srcPol u μ i (v : MvPolynomial (GL3Theta.FrV D (D.R.N i)) D.what₂.LL) ∈ WtPol D.what₂.LL (nuT D u i) := by
  cases i with
  | zero => exact srcPol_zero u μ v
  | succ j =>
    have h := srcPol_succ u μ j v
    have e : (fun τ r => extNu (D.R.N (j + 1)) (nuT D u j) τ r + ((D.chTw u μ).sSharp (j + 1) τ - (D.chTw u μ).sDiv j τ).toNat) = nuT D u (j + 1) :=
      funext fun τ => funext fun r => nuStep D u μ j hi τ r
    rw [e] at h
    exact h

theorem diagram_fits_source_rank (D : D7) (u : D.what₂.Word) (i : ℕ) (hi : i < D.R.m) : NuFits D (nuD D u i) (nuT D u i) := by
  refine ⟨fun z r => ?_, fun z r hr => ?_⟩
  · have h1 := nuRowOK D u i hi z r.1
    rw [if_pos r.2, ← (nu_t_identity D u i hi (tauPl D z) r).1] at h1
    exact_mod_cast h1
  · have h1 := nuRowOK D u i hi z r
    rw [if_neg (by omega)] at h1
    exact_mod_cast h1

theorem nuFits_tgt (D : D7) (u : D.what₂.Word) (i : ℕ) (hi : i < D.R.m) :
    NuFits D (nuD D u i) (extNu (D.R.N (i + 1)) (nuT D u i)) := by
  refine ⟨fun z r => ?_, fun z r hr => ?_⟩
  · unfold extNu
    by_cases h : r.1 < D.R.N i
    · rw [dif_pos h]
      exact (diagram_fits_source_rank D u i hi).1 z ⟨r.1, h⟩
    · rw [dif_neg h]
      exact (diagram_fits_source_rank D u i hi).2 z r.1 (by omega)
  · exact (diagram_fits_source_rank D u i hi).2 z r (le_trans (N_le_succ D.R i) hr)

theorem canS_of {D : D7} (P : Examples₂.EntPl D) (B : PlaceMatrixFamily D) (h : CanOnto P) : CanS P B := fun u μ w i hi c v =>
  Submodule.smul_mem _ _ (h w (D.R.N i) (nuD D u i) (nuT D u i) (diagram_fits_source_rank D u i hi) _ (srcPol_mem u μ i hi v) (B u μ w i c))

theorem canT_of {D : D7} (P : Examples₂.EntPl D) (B : PlaceMatrixFamily D) (h : CanOnto P) : CanT P B := fun u μ w i hi c' v =>
  Submodule.smul_mem _ _ (h w (D.R.N (i + 1)) (nuD D u i) (extNu (D.R.N (i + 1)) (nuT D u i)) (nuFits_tgt D u i hi) _ v.2 (B u μ w (i + 1) c'))

def kfTieOf {D : D7} (P : Examples₂.EntPl D) (O : ∀ u μ, GL3Theta.LiftObj D (D.chTw u μ)) (B : PlaceMatrixFamily D) {Dx : DivX D} {Tw : TwForms D} (hB : BasOk P O B)
    (hC : CanOnto P) (h : KerEntHyp P O B Dx Tw) (u : D.what₂.Word) (μ : D.what₂.Tup) (w : D.what₂.places.Pl) :
    GL3Columns.KFTie (kerEntC P O B h) (O u μ) w :=
  kfTieC P O B hB (canS_of P B hC) (canT_of P B hC) (twLe D) h u μ w

theorem kfTieOf_un {D : D7} (P : Examples₂.EntPl D) (O : ∀ u μ, GL3Theta.LiftObj D (D.chTw u μ)) (B : PlaceMatrixFamily D) {Dx : DivX D} {Tw : TwForms D} (hB : BasOk P O B)
    (hC : CanOnto P) (h : KerEntHyp P O B Dx Tw) (u : D.what₂.Word) (μ : D.what₂.Tup) (hR : GL3Columns.RhoAlg (O u μ)) (w : D.what₂.places.Pl) :
    (kfTieOf P O B hB hC h u μ w).UnIs :=
  kfTieC_un P O B hB (canS_of P B hC) (canT_of P B hC) (twLe D) h u μ hR w

theorem kfPair_of_field {D : D7} {Dx : DivX D} {Tw : TwForms D} (E : KerEnt D Dx Tw) {u : D.what₂.Word} {μ : D.what₂.Tup}
    {O : GL3Theta.LiftObj D (D.chTw u μ)} {w : D.what₂.places.Pl} (T : GL3Columns.KFTie E O w) (hw : LevFree Dx u μ w) (hU : T.UnIs) : T.kfPair :=
  fun i hi c c' v v' h I => by
    rw [← hU i hi c c']
    exact E.kform u μ w hw i hi c c' v v' h I

end Formalism.L2.Ker

end
