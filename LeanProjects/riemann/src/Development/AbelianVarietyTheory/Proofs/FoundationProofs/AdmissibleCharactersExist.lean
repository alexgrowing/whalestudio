import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaussPowFourHom
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InducedTypeThetaGenusOnePermutesStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaTranslationIntertwinerUnitaryStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaSpaceSelfDualPairAtMostLineStatement

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

noncomputable section

namespace GlobalTheory.TripleIntertwiner

variable (D : D7) (T : Tor D) {N N' : ℕ}

theorem hf_add_left (x y z : VC D N N') : Hf D T (x + y) z = Hf D T x z + Hf D T y z := by
  unfold Hf
  rw [← add_div]
  congr 1
  simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem hf_add_right (x y z : VC D N N') : Hf D T x (y + z) = Hf D T x y + Hf D T x z := by
  unfold Hf
  rw [← add_div]
  congr 1
  simp only [Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib]

theorem hf_conj (x y : VC D N N') : Hf D T x y = (starRingEnd ℂ) (Hf D T y x) := by
  simp only [Hf, map_div₀, map_sum, map_mul, Complex.conj_conj, Complex.conj_ofReal, mul_comm]

def wLin (x : VC D N N') : (VC D N N' → ℂ) →ₗ[ℂ] (VC D N N' → ℂ) where
  toFun := Wd D T x
  map_add' F G := by funext z; simp only [Wd, U, Pi.add_apply]; ring
  map_smul' a F := by funext z; simp only [Wd, U, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

def cocExp (x y : VC D N N') : ℂ :=
  (Real.pi : ℂ) * (Hf D T y x - Hf D T x y) / 2 -
    (Real.pi : ℂ) * Complex.I * ((Real.sqrt D.host.d : ℝ) : ℂ) / 2 *
      (((Hf D T x y).re : ℂ) + ((Hf D T y x).re : ℂ))

theorem wLin_heis :
    (∀ (x y : VC D N N') f, wLin D T x (wLin D T y f) = Complex.exp (cocExp D T x y) • wLin D T (x + y) f) ∧
    (∀ x x' y : VC D N N', Complex.exp (cocExp D T (x + x') y) =
      Complex.exp (cocExp D T x y) * Complex.exp (cocExp D T x' y)) ∧
    (∀ x y y' : VC D N N', Complex.exp (cocExp D T x (y + y')) =
      Complex.exp (cocExp D T x y) * Complex.exp (cocExp D T x y')) ∧
    ∀ x y : VC D N N', Complex.exp (cocExp D T x y) ≠ 0 := by
  refine ⟨fun x y f => ?_, fun x x' y => ?_, fun x y y' => ?_, fun _ _ => Complex.exp_ne_zero _⟩
  · funext z
    show Wd D T x (Wd D T y f) z = Complex.exp (cocExp D T x y) * Wd D T (x + y) f z
    simp only [Wd, U, wdPh, ee, qH, add_assoc]
    have : ∀ a b c d e g h u : ℂ, a + b + c + d = e + g + h →
        Complex.exp a * (Complex.exp b * (u * Complex.exp c) * Complex.exp d) =
          Complex.exp e * (Complex.exp g * (u * Complex.exp h)) := by
      intro a b c d e g h u hh
      calc _ = u * Complex.exp (a + b + c + d) := by simp only [Complex.exp_add]; ring
        _ = _ := by rw [hh]; simp only [Complex.exp_add]; ring
    apply this
    simp only [cocExp, hf_add_left, hf_add_right, Complex.add_re]
    push_cast
    ring
  · rw [← Complex.exp_add]; congr 1
    simp only [cocExp, hf_add_left, hf_add_right, Complex.add_re]
    push_cast
    ring
  · rw [← Complex.exp_add]; congr 1
    simp only [cocExp, hf_add_left, hf_add_right, Complex.add_re]
    push_cast
    ring

theorem im_int_of_comm (x v : VC D N N')
    (h : Complex.exp (cocExp D T x v) = Complex.exp (cocExp D T v x)) : ∃ m : ℤ, (Hf D T v x).im = m := by
  obtain ⟨m, hm⟩ := Complex.exp_eq_exp_iff_exists_int.mp h
  refine ⟨m, ?_⟩
  have h1 : Hf D T v x - Hf D T x v = 2 * ((Hf D T v x).im : ℂ) * Complex.I := by
    rw [hf_conj D T x v, Complex.sub_conj]; push_cast; ring
  have h2 : (2 * (Real.pi : ℂ) * Complex.I) * ((Hf D T v x).im : ℂ) = (2 * (Real.pi : ℂ) * Complex.I) * m := by
    simp only [cocExp] at hm
    linear_combination hm - (Real.pi : ℂ) * h1
  have h3 := mul_left_cancel₀ Complex.two_pi_I_ne_zero h2
  exact_mod_cast h3

theorem iop_eq_itw (A B : AddSubgroup (VC D N N'))
    (hB : ∀ x ∈ B, ∀ F, Wd D T x F = fun z => al D T x * U D T x F z) (G : VC D N N' → ℂ) :
    Iop D T A B G = itw (wLin D T) A B G := by
  funext z
  simp only [Iop, itw, Pi.smul_apply, smul_eq_mul]
  by_cases h : (A.addSubgroupOf B).index = 0
  · simp [h]
  · haveI : Finite (B ⧸ A.addSubgroupOf B) := Nat.finite_of_card_ne_zero h
    letI : Fintype (B ⧸ A.addSubgroupOf B) := Fintype.ofFinite _
    rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, Finset.sum_apply]
    congr 1
    refine Finset.sum_congr rfl fun q _ => ?_
    exact (congrFun (hB _ (rep_mem q) G) z).symm

theorem itw_smul {V F : Type} [AddCommGroup V] [AddCommGroup F] [Module ℂ F] (W : V → F →ₗ[ℂ] F)
    (A B : AddSubgroup V) (a : ℂ) (f : F) : itw W A B (a • f) = a • itw W A B f := by
  by_cases h : (A.addSubgroupOf B).index = 0
  · simp [itw, h]
  · haveI : Finite (B ⧸ A.addSubgroupOf B) := Nat.finite_of_card_ne_zero h
    letI : Fintype (B ⧸ A.addSubgroupOf B) := Fintype.ofFinite _
    simp only [itw, finsum_eq_sum_of_fintype, map_smul, ← Finset.smul_sum]
    rw [smul_comm]

theorem triple_constant : ∀ D : D7, GaussSumTripleConstant D := by
  intro D cc δ hc N N' A B C kA kB kC th hth
  by_cases h0 : th = 0
  · refine ⟨1, one_pow _, ?_⟩
    subst h0
    have e : ∀ X Y : AddSubgroup (VC D N N'), Iop D (tor0 D cc δ) X Y 0 = 0 := by
      intro X Y; funext z; simp [Iop, U]
    rw [e, e, e]; funext z; simp
  set T := tor0 D cc δ with hT
  have line := fun X (k : KLat D T X) => GlobalTheory.T.theta_space_selfDual_pair_at_most_line D (GlobalTheory.T.inducedType_thetaGenusOne_permutes D).1 cc δ hc N N' X k
  have eqI : ∀ X Y : AddSubgroup (VC D N N'), KLat D T Y → ∀ G, Iop D T X Y G = itw (wLin D T) X Y G :=
    fun X Y k G => iop_eq_itw D T X Y (line Y k).2.1 G
  have fix : ∀ X : AddSubgroup (VC D N N'), KLat D T X → ∀ G ∈ ThSp D T X, ∀ x ∈ X, wLin D T x G = G := by
    intro X k G hG x hx
    show Wd D T x G = G
    rw [(line X k).2.1 x hx]
    funext z
    exact hG.2 x hx z
  have uni : ∀ X Y : AddSubgroup (VC D N N'), KLat D T X → KLat D T Y → ∀ G ∈ ThSp D T X,
      itw (wLin D T) X Y G ∈ ThSp D T Y ∧ itw (wLin D T) Y X (itw (wLin D T) X Y G) = G := by
    intro X Y kX kY G hG
    have := GlobalTheory.T.intertwinerUnitary_all D cc δ hc N N' X Y kX kY G hG
    rw [← eqI X Y kY, ← eqI Y X kX]
    exact ⟨this.2.1, this.2.2.2⟩
  have nz : ∀ X Y : AddSubgroup (VC D N N'), KLat D T X → KLat D T Y → ∀ G ∈ ThSp D T X, G ≠ 0 →
      itw (wLin D T) X Y G ≠ 0 := by
    intro X Y kX kY G hG hG0 h
    have := (uni X Y kX kY G hG).2
    rw [h, ← zero_smul ℂ (0 : VC D N N' → ℂ), itw_smul, zero_smul] at this
    exact hG0 this.symm
  have ex : ∀ X : AddSubgroup (VC D N N'), KLat D T X → ∃ G ∈ ThSp D T X, G ≠ 0 :=
    fun X k => ⟨_, (uni A X kA k th hth).1, nz A X kA k th hth h0⟩
  have fin : ∀ X Y : AddSubgroup (VC D N N'), KLat D T X → KLat D T Y → X.relIndex Y ≠ 0 := by
    intro X Y kX kY h
    obtain ⟨G, hG, hG0⟩ := ex X kX
    apply nz X Y kX kY G hG hG0
    have h' : (X.addSubgroupOf Y).index = 0 := h
    simp [itw, h']
  have fin3 : ∀ Y : AddSubgroup (VC D N N'), KLat D T Y → (A ⊓ B ⊓ C).relIndex Y ≠ 0 := fun Y k =>
    AddSubgroup.relIndex_inf_ne_zero (AddSubgroup.relIndex_inf_ne_zero (fin A Y kA k) (fin B Y kB k))
      (fin C Y kC k)
  have H := wLin_heis D T (N := N) (N' := N')
  have coc : ∀ X : AddSubgroup (VC D N N'), KLat D T X → ∀ x ∈ X, ∀ y ∈ X,
      Complex.exp (cocExp D T x y) = 1 := by
    intro X k x hx y hy
    obtain ⟨G, hG, hG0⟩ := ex X k
    have := H.1 x y G
    rw [fix X k G hG y hy, fix X k G hG x hx, fix X k G hG _ (X.add_mem hx hy)] at this
    exact smul_left_injective ℂ hG0 (this.symm.trans (one_smul ℂ G).symm)
  have m1 := (uni A B kA kB th hth).1
  have m2 := (uni B C kB kC _ m1).1
  have m3 := (uni A C kA kC th hth).1
  have m4 := (uni C B kC kB _ m3).1
  obtain ⟨μ, μ', h4, e1, e2⟩ := itw_triple (c := fun x y => Complex.exp (cocExp D T x y)) H
    (fin3 A kA) (fin3 B kB) (fin3 C kC) (coc A kA) (coc B kB) (coc C kC)
    (fun v hv => (line A kA).2.2.2.1 v fun y hy => im_int_of_comm D T y v (hv y hy))
    th (fix A kA th hth) (fix B kB _ m1) (fix C kC _ m2) (fix C kC _ m3) (fix B kB _ m4)
  have e3 := (uni C A kC kA _ m2).2
  rw [e1, itw_smul] at e3
  have e4 := (uni B C kB kC _ m1).2
  have e5 := (uni A B kA kB th hth).2
  rw [← e4, ← e3, itw_smul, itw_smul, e2, smul_smul] at e5
  have e6 : μ * μ' = 1 := smul_left_injective ℂ h0 (e5.trans (one_smul ℂ th).symm)
  refine ⟨μ, ?_, ?_⟩
  · calc μ ^ 8 = μ ^ 4 * μ ^ 4 := by ring
      _ = (μ * μ') ^ 4 := by rw [mul_pow, ← h4]
      _ = 1 := by rw [e6, one_pow]
  · rw [eqI B C kC, eqI A B kB, eqI A C kC, ← e3]
    rfl

end GlobalTheory.TripleIntertwiner
