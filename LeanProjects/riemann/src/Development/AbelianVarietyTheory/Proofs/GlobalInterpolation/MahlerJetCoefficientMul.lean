import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LatIntZero

noncomputable section

namespace GlobalTheory.MomN.MahlerProd

open GlobalTheory.MomN
open scoped ContDiff

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

def dd (u : V) (f : V → ℂ) : V → ℂ := fun x => fderiv ℂ f x u

def ddl {κ : Type} (v : κ → V) (L : List κ) (f : V → ℂ) : V → ℂ := L.foldr (fun a h => dd (v a) h) f

theorem contDiff_dd (u : V) {f : V → ℂ} (hf : ContDiff ℂ ∞ f) : ContDiff ℂ ∞ (dd u f) :=
  (contDiff_infty_iff_fderiv.1 hf).2.clm_apply contDiff_const

theorem contDiff_ddl {κ : Type} (v : κ → V) {f : V → ℂ} (hf : ContDiff ℂ ∞ f) :
    ∀ L : List κ, ContDiff ℂ ∞ (ddl v L f)
  | [] => hf
  | a :: L => contDiff_dd (v a) (contDiff_ddl v hf L)

theorem jet_eq {κ : Type} (v : κ → V) {f : V → ℂ} (hf : ContDiff ℂ ∞ f) :
    ∀ (L : List κ) (x : V), iteratedFDeriv ℂ L.length f x (fun i => v (L.get i)) = ddl v L f x
  | [], x => by simp [ddl]
  | a :: L, x => by
    have hd : DifferentiableAt ℂ (iteratedFDeriv ℂ L.length f) x :=
      hf.differentiable_iteratedFDeriv (by exact_mod_cast ENat.natCast_lt_top _) x
    have h : (fun y => iteratedFDeriv ℂ L.length f y (fun i => v (L.get i))) = ddl v L f :=
      funext fun y => jet_eq v hf L y
    show iteratedFDeriv ℂ (L.length + 1) f x _ = _
    rw [iteratedFDeriv_succ_apply_left]
    rw [← fderiv_continuousMultilinear_apply_const_apply hd]
    show fderiv ℂ (fun y => iteratedFDeriv ℂ L.length f y (fun i => v (L.get i))) x (v a) = _
    rw [h]
    rfl

theorem dd_comm (u w : V) {f : V → ℂ} (hf : ContDiff ℂ ∞ f) : dd u (dd w f) = dd w (dd u f) := by
  funext x
  have hs := (hf.contDiffAt (x := x)).isSymmSndFDerivAt (by simp only [minSmoothness_of_isRCLikeNormedField]; exact WithTop.coe_le_coe.2 (le_top : (2:ℕ∞) ≤ ⊤))
  have hd : DifferentiableAt ℂ (fderiv ℂ f) x :=
    (contDiff_infty_iff_fderiv.1 hf).2.differentiable (by simp) x
  show fderiv ℂ (fun y => fderiv ℂ f y w) x u = fderiv ℂ (fun y => fderiv ℂ f y u) x w
  rw [fderiv_clm_apply hd (differentiableAt_const _), fderiv_clm_apply hd (differentiableAt_const _)]
  simp [hs u w]

theorem ddl_perm {κ : Type} (v : κ → V) {f : V → ℂ} (hf : ContDiff ℂ ∞ f) {L L' : List κ} (h : L.Perm L') :
    ddl v L f = ddl v L' f := by
  induction h with
  | nil => rfl
  | cons a _ ih => exact congrArg (dd (v a)) ih
  | swap a b L => exact dd_comm (v b) (v a) (contDiff_ddl v hf L)
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

theorem ddl_append {κ : Type} (v : κ → V) (f : V → ℂ) (L L' : List κ) :
    ddl v (L ++ L') f = ddl v L (ddl v L' f) := by
  simp [ddl, List.foldr_append]

theorem monoJet_eq {κ : Type} [Fintype κ] (v : κ → V) {f : V → ℂ} (hf : ContDiff ℂ ∞ f) (m : κ →₀ ℕ) :
    monoJet v f m = ddl v m.toMultiset.toList f 0 :=
  jet_eq v hf _ 0

theorem monoJet_add_single {κ : Type} [Fintype κ] (v : κ → V) {f : V → ℂ} (hf : ContDiff ℂ ∞ f)
    (m : κ →₀ ℕ) (i : κ) : monoJet v f (m + Finsupp.single i 1) = monoJet v (dd (v i) f) m := by
  rw [monoJet_eq v hf, monoJet_eq v (contDiff_dd _ hf)]
  have e : dd (v i) f = ddl v [i] f := rfl
  rw [e, ← ddl_append]
  refine congrFun (ddl_perm v hf ?_) 0
  rw [← Multiset.coe_eq_coe, ← Multiset.coe_add, Multiset.coe_toList, Multiset.coe_toList,
    Finsupp.toMultiset_add, Finsupp.toMultiset_single]
  simp

theorem dd_mul (u : V) {F G : V → ℂ} (hF : ContDiff ℂ ∞ F) (hG : ContDiff ℂ ∞ G) :
    dd u (fun z => F z * G z) = fun z => dd u F z * G z + F z * dd u G z := by
  funext x
  simp only [dd]
  rw [show (fun z => F z * G z) = F * G from rfl, fderiv_mul (hF.differentiable (by simp) x) (hG.differentiable (by simp) x)]
  simp; ring

theorem dd_add (u : V) {F G : V → ℂ} (hF : ContDiff ℂ ∞ F) (hG : ContDiff ℂ ∞ G) :
    dd u (fun z => F z + G z) = fun z => dd u F z + dd u G z := by
  funext x
  simp only [dd]
  rw [show (fun z => F z + G z) = F + G from rfl, fderiv_add (hF.differentiable (by simp) x) (hG.differentiable (by simp) x)]
  rfl

theorem ddl_add {κ : Type} (v : κ → V) {F G : V → ℂ} (hF : ContDiff ℂ ∞ F) (hG : ContDiff ℂ ∞ G) :
    ∀ L : List κ, ddl v L (fun z => F z + G z) = fun z => ddl v L F z + ddl v L G z
  | [] => rfl
  | a :: L => by
    show dd (v a) (ddl v L _) = _
    rw [ddl_add v hF hG L, dd_add _ (contDiff_ddl v hF L) (contDiff_ddl v hG L)]
    rfl

theorem monoJet_add {κ : Type} [Fintype κ] (v : κ → V) {F G : V → ℂ} (hF : ContDiff ℂ ∞ F)
    (hG : ContDiff ℂ ∞ G) (m : κ →₀ ℕ) :
    monoJet v (fun z => F z + G z) m = monoJet v F m + monoJet v G m := by
  rw [monoJet_eq v (hF.add hG), monoJet_eq v hF, monoJet_eq v hG, ddl_add v hF hG]

theorem monoJet_zero {κ : Type} [Fintype κ] (v : κ → V) {f : V → ℂ} (hf : ContDiff ℂ ∞ f) :
    monoJet v f 0 = f 0 := by
  rw [monoJet_eq v hf]; simp [ddl]

section Alg

variable {κ : Type} [Fintype κ]

open MvPolynomial

theorem sum_support_eq {σ : Type} (c : (σ →₀ ℕ) → ℂ) (r : MvPolynomial σ ℂ) (s : Finset (σ →₀ ℕ))
    (hs : r.support ⊆ s) : ∑ m ∈ r.support, r.coeff m * c m = ∑ m ∈ s, r.coeff m * c m :=
  Finset.sum_subset hs fun m _ hm => by rw [MvPolynomial.mem_support_iff, not_not] at hm; rw [hm, zero_mul]

def lin {σ : Type} (c : (σ →₀ ℕ) → ℂ) : MvPolynomial σ ℂ →+ ℂ where
  toFun p := ∑ m ∈ p.support, p.coeff m * c m
  map_zero' := by simp
  map_add' p q := by
    classical
    rw [sum_support_eq c (p + q) (p.support ∪ q.support) MvPolynomial.support_add,
      sum_support_eq c p _ Finset.subset_union_left, sum_support_eq c q _ Finset.subset_union_right,
      ← Finset.sum_add_distrib]
    simp only [MvPolynomial.coeff_add, add_mul]

theorem lin_monomial {σ : Type} (c : (σ →₀ ℕ) → ℂ) (m : σ →₀ ℕ) (a : ℂ) : lin c (monomial m a) = a * c m := by
  classical
  show ∑ k ∈ (monomial m a).support, (monomial m a).coeff k * c k = _
  rw [sum_support_eq c _ {m} MvPolynomial.support_monomial_subset, Finset.sum_singleton, coeff_monomial, if_pos rfl]

def LJ (v : κ → V) (f : V → ℂ) : MvPolynomial κ ℂ →+ ℂ := lin (monoJet v f)

def BJ (v : κ → V) (F G : V → ℂ) : MvPolynomial (κ ⊕ κ) ℂ →+ ℂ :=
  lin fun e =>
    monoJet v F (Finsupp.sumFinsuppAddEquivProdFinsupp e).1 * monoJet v G (Finsupp.sumFinsuppAddEquivProdFinsupp e).2

def cop : MvPolynomial κ ℂ →ₐ[ℂ] MvPolynomial (κ ⊕ κ) ℂ :=
  aeval fun i => X (Sum.inl i) + X (Sum.inr i)

def Pn {σ : Type} [Fintype σ] (n : σ → ℕ) : MvPolynomial σ ℂ :=
  ∏ i, C (((n i).factorial : ℂ)⁻¹) * Polynomial.aeval (X i : MvPolynomial σ ℂ) (descPochhammer ℂ (n i))

theorem LJ_monomial (v : κ → V) (f : V → ℂ) (m : κ →₀ ℕ) (c : ℂ) :
    LJ v f (monomial m c) = c * monoJet v f m := by
  exact lin_monomial _ _ _

theorem BJ_monomial (v : κ → V) (F G : V → ℂ) (e : κ ⊕ κ →₀ ℕ) (c : ℂ) :
    BJ v F G (monomial e c) = c * (monoJet v F (Finsupp.sumFinsuppAddEquivProdFinsupp e).1 *
      monoJet v G (Finsupp.sumFinsuppAddEquivProdFinsupp e).2) := by
  exact lin_monomial _ _ _

theorem mahler_eq (v : κ → V) (f : V → ℂ) (n : κ → ℕ) : mahler v f n = LJ v f (Pn n) := by
  rfl

theorem LJ_mul_X (v : κ → V) {f : V → ℂ} (hf : ContDiff ℂ ∞ f) (p : MvPolynomial κ ℂ) (i : κ) :
    LJ v f (p * X i) = LJ v (dd (v i) f) p := by
  induction p using MvPolynomial.induction_on' with
  | monomial m c => rw [X, monomial_mul, LJ_monomial, LJ_monomial, mul_one, monoJet_add_single v hf]
  | add p q hp hq => rw [add_mul, map_add, map_add, hp, hq]

theorem LJ_fun_add (v : κ → V) {F G : V → ℂ} (hF : ContDiff ℂ ∞ F) (hG : ContDiff ℂ ∞ G)
    (p : MvPolynomial κ ℂ) : LJ v (fun z => F z + G z) p = LJ v F p + LJ v G p := by
  induction p using MvPolynomial.induction_on' with
  | monomial m c => rw [LJ_monomial, LJ_monomial, LJ_monomial, monoJet_add v hF hG, mul_add]
  | add p q hp hq => rw [map_add, map_add, map_add, hp, hq]; ring

theorem split_single_inl (e : κ ⊕ κ →₀ ℕ) (i : κ) :
    Finsupp.sumFinsuppAddEquivProdFinsupp (e + Finsupp.single (Sum.inl i) 1) =
      ((Finsupp.sumFinsuppAddEquivProdFinsupp e).1 + Finsupp.single i 1, (Finsupp.sumFinsuppAddEquivProdFinsupp e).2) := by
  classical
  ext j <;> simp [Finsupp.fst_sumFinsuppAddEquivProdFinsupp, Finsupp.snd_sumFinsuppAddEquivProdFinsupp,
    Finsupp.single_apply]

theorem split_single_inr (e : κ ⊕ κ →₀ ℕ) (i : κ) :
    Finsupp.sumFinsuppAddEquivProdFinsupp (e + Finsupp.single (Sum.inr i) 1) =
      ((Finsupp.sumFinsuppAddEquivProdFinsupp e).1, (Finsupp.sumFinsuppAddEquivProdFinsupp e).2 + Finsupp.single i 1) := by
  classical
  ext j <;> simp [Finsupp.fst_sumFinsuppAddEquivProdFinsupp, Finsupp.snd_sumFinsuppAddEquivProdFinsupp,
    Finsupp.single_apply]

theorem BJ_mul_X_inl (v : κ → V) {F : V → ℂ} (G : V → ℂ) (hF : ContDiff ℂ ∞ F) (Q : MvPolynomial (κ ⊕ κ) ℂ) (i : κ) :
    BJ v F G (Q * X (Sum.inl i)) = BJ v (dd (v i) F) G Q := by
  induction Q using MvPolynomial.induction_on' with
  | monomial m c => rw [X, monomial_mul, BJ_monomial, BJ_monomial, mul_one, split_single_inl, monoJet_add_single v hF]
  | add p q hp hq => rw [add_mul, map_add, map_add, hp, hq]

theorem BJ_mul_X_inr (v : κ → V) (F : V → ℂ) {G : V → ℂ} (hG : ContDiff ℂ ∞ G) (Q : MvPolynomial (κ ⊕ κ) ℂ) (i : κ) :
    BJ v F G (Q * X (Sum.inr i)) = BJ v F (dd (v i) G) Q := by
  induction Q using MvPolynomial.induction_on' with
  | monomial m c => rw [X, monomial_mul, BJ_monomial, BJ_monomial, mul_one, split_single_inr, monoJet_add_single v hG]
  | add p q hp hq => rw [add_mul, map_add, map_add, hp, hq]

theorem LJ_mul (v : κ → V) (P : MvPolynomial κ ℂ) : ∀ (F G : V → ℂ), ContDiff ℂ ∞ F → ContDiff ℂ ∞ G →
    LJ v (fun z => F z * G z) P = BJ v F G (cop P) := by
  induction P using MvPolynomial.induction_on with
  | C a =>
    intro F G hF hG
    have h0 : Finsupp.sumFinsuppAddEquivProdFinsupp (0 : κ ⊕ κ →₀ ℕ) = (0, 0) := map_zero _
    rw [cop, aeval_C, algebraMap_eq, C_apply, C_apply, LJ_monomial, BJ_monomial, h0, monoJet_zero v (hF.mul hG),
      monoJet_zero v hF, monoJet_zero v hG]
  | add p q hp hq =>
    intro F G hF hG
    rw [map_add, map_add, map_add, hp F G hF hG, hq F G hF hG]
  | mul_X p i ih =>
    intro F G hF hG
    rw [LJ_mul_X v (hF.mul hG), dd_mul _ hF hG, LJ_fun_add v ((contDiff_dd _ hF).mul hG) (hF.mul (contDiff_dd _ hG)),
      ih _ _ (contDiff_dd _ hF) hG, ih _ _ hF (contDiff_dd _ hG), map_mul, cop, aeval_X, ← cop, mul_add, map_add,
      BJ_mul_X_inl v G hF, BJ_mul_X_inr v F hG]

end Alg

section Alg2

open MvPolynomial

theorem aeval_descPochhammer {R : Type} [CommRing R] [Algebra ℂ R] (z : R) (k : ℕ) :
    Polynomial.aeval z (descPochhammer ℂ k) = (descPochhammer ℤ k).smeval z := by
  rw [← descPochhammer_map (algebraMap ℤ ℂ), Polynomial.aeval_map_algebraMap, Polynomial.aeval_eq_smeval]

theorem vdm {σ : Type} (x y : MvPolynomial σ ℂ) (n : ℕ) :
    C ((n.factorial : ℂ)⁻¹) * Polynomial.aeval (x + y) (descPochhammer ℂ n) =
      ∑ a ∈ Finset.range (n + 1), (C ((a.factorial : ℂ)⁻¹) * Polynomial.aeval x (descPochhammer ℂ a)) *
        (C (((n - a).factorial : ℂ)⁻¹) * Polynomial.aeval y (descPochhammer ℂ (n - a))) := by
  simp only [aeval_descPochhammer]
  rw [Ring.descPochhammer_smeval_add n (Commute.all x y), Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a ha => ?_
  have ha' : a ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 ha)
  have hc : ((n.factorial : ℂ))⁻¹ * (n.choose a : ℂ) = (a.factorial : ℂ)⁻¹ * ((n - a).factorial : ℂ)⁻¹ := by
    rw [← Nat.choose_mul_factorial_mul_factorial ha']
    push_cast
    have h1 : (a.factorial : ℂ) ≠ 0 := by exact_mod_cast a.factorial_ne_zero
    have h2 : ((n - a).factorial : ℂ) ≠ 0 := by exact_mod_cast (n - a).factorial_ne_zero
    have h3 : (n.choose a : ℂ) ≠ 0 := by exact_mod_cast (Nat.choose_pos ha').ne'
    field_simp
  calc C ((n.factorial : ℂ)⁻¹) * (((n.choose a : ℕ) : MvPolynomial σ ℂ) *
        ((descPochhammer ℤ a).smeval x * (descPochhammer ℤ (n - a)).smeval y))
      = C ((n.factorial : ℂ)⁻¹ * (n.choose a : ℂ)) *
        ((descPochhammer ℤ a).smeval x * (descPochhammer ℤ (n - a)).smeval y) := by
        rw [C_mul, ← map_natCast (C : ℂ →+* MvPolynomial σ ℂ)]; ring
    _ = _ := by rw [hc, C_mul]; ring

variable {κ : Type} [Fintype κ] [DecidableEq κ]

theorem cop_Pn (n : κ → ℕ) :
    cop (Pn n) = ∑ k ∈ Fintype.piFinset (fun i => Finset.range (n i + 1)),
      rename Sum.inl (Pn k) * rename Sum.inr (Pn (fun i => n i - k i)) := by
  have e : ∀ i, cop (C (((n i).factorial : ℂ)⁻¹) * Polynomial.aeval (X i : MvPolynomial κ ℂ) (descPochhammer ℂ (n i))) =
      C (((n i).factorial : ℂ)⁻¹) * Polynomial.aeval (X (Sum.inl i) + X (Sum.inr i) : MvPolynomial (κ ⊕ κ) ℂ)
        (descPochhammer ℂ (n i)) := by
    intro i
    rw [map_mul, ← Polynomial.aeval_algHom_apply, cop, aeval_C, aeval_X, algebraMap_eq]
  rw [Pn, map_prod]
  simp only [e, vdm, Finset.prod_univ_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.prod_mul_distrib, Pn, Pn, map_prod, map_prod]
  congr 1 <;> refine Finset.prod_congr rfl fun i _ => ?_ <;>
    rw [map_mul, rename_C, ← Polynomial.aeval_algHom_apply, rename_X]

theorem split_rename (a b : κ →₀ ℕ) :
    Finsupp.sumFinsuppAddEquivProdFinsupp (Finsupp.mapDomain Sum.inl a + Finsupp.mapDomain Sum.inr b) = (a, b) := by
  ext j
  · simp [Finsupp.fst_sumFinsuppAddEquivProdFinsupp, Finsupp.mapDomain_apply Sum.inl_injective,
      Finsupp.mapDomain_notin_range]
  · simp [Finsupp.snd_sumFinsuppAddEquivProdFinsupp, Finsupp.mapDomain_apply Sum.inr_injective,
      Finsupp.mapDomain_notin_range]

theorem BJ_rename (v : κ → V) (F G : V → ℂ) (p q : MvPolynomial κ ℂ) :
    BJ v F G (rename Sum.inl p * rename Sum.inr q) = LJ v F p * LJ v G q := by
  induction p using MvPolynomial.induction_on' with
  | monomial a c =>
    induction q using MvPolynomial.induction_on' with
    | monomial b d =>
      rw [rename_monomial, rename_monomial, monomial_mul, BJ_monomial, LJ_monomial, LJ_monomial, split_rename]
      ring
    | add q q' hq hq' => rw [map_add, mul_add, map_add, hq, hq', map_add, mul_add]
  | add p p' hp hp' => rw [map_add, add_mul, map_add, hp, hp', map_add, add_mul]

end Alg2

end GlobalTheory.MomN.MahlerProd

namespace GlobalTheory.MomN

open GlobalTheory.MomN.MahlerProd
open scoped ContDiff

theorem mahler_mul (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (κ : Type) [Fintype κ] [DecidableEq κ]
    (v : κ → V) (F G : V → ℂ) (hF : ContDiff ℂ ⊤ F) (hG : ContDiff ℂ ⊤ G) (n : κ → ℕ) :
    mahler v (fun z => F z * G z) n = ∑ k ∈ Fintype.piFinset (fun i => Finset.range (n i + 1)),
      mahler v F k * mahler v G (fun i => n i - k i) := by
  have hF' : ContDiff ℂ ∞ F := hF.of_le le_top
  have hG' : ContDiff ℂ ∞ G := hG.of_le le_top
  rw [mahler_eq, LJ_mul v _ F G hF' hG', cop_Pn, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [BJ_rename, ← mahler_eq, ← mahler_eq]

end GlobalTheory.MomN
