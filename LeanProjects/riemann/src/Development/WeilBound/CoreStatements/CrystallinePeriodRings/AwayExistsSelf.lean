import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import GroundTheory.PAdicHodge.BCrisRegularFinal
import GroundTheory.PAdicHodge.FundamentalSeqBCris
import Development.WeilBound.CoreStatements.CrystallinePeriodRings.NonemptyThetaLOfTied
import Development.WeilBound.CoreStatements.CrystallinePeriodRings.FilQuot
import Development.WeilBound.CoreStatements.CrystallinePeriodRings.InvRestrictScalarsMem

noncomputable section

namespace PositivityTheory.LocInh

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct
open scoped Formalism.Per6

section Abstract

theorem onto_eigen {A C : Type} [CommRing A] [CommRing C] {k : A →+* C}
    (hk : Function.Injective k) {G : C →+* C} {g : A →+* A} (hG : ∀ x, G (k x) = k (g x))
    {p m n : ℕ} {a : A} {y : C} (ha : k a = k (p : A) ^ m * y) (hy : G y = (p : C) ^ n * y) :
    g a = (p : A) ^ n * a := by
  apply hk
  rw [← hG, map_mul, map_pow, ha, map_mul, map_pow, map_natCast, map_natCast, hy]
  ring

theorem onto_fixed {A B : Type} [CommRing A] [CommRing B] {f : A →+* B} {F : B →+* B}
    {g : A →+* A} (hF : ∀ x, F (f x) = f (g x)) {p t a : A} (hf : IsFrac f p t) (hp : g p = p)
    (ht : g t = p * t) (m : ℕ) {n : ℕ} (ha : g a = p ^ n * a) :
    ∃ x : B, F x = x ∧ f p ^ m * f t ^ n * x = f a := by
  obtain ⟨x, hx⟩ := ((hf.1.pow m).mul (hf.2.1.pow n)).exists_right_inv
  have e : f p ^ m * f t ^ n * (x * f a) = f a := by rw [← mul_assoc, hx, one_mul]
  refine ⟨x * f a, ?_, e⟩
  have h1 := congrArg F e
  rw [map_mul, map_mul, map_pow, map_pow, hF, hF, hF, hp, ht, ha, map_mul f, map_mul f,
    map_pow f] at h1
  refine ((hf.1.pow m).mul ((hf.1.mul hf.2.1).pow n)).mul_left_cancel (h1.trans ?_)
  conv_lhs => rw [← e]
  ring

theorem onto_cancel {A C E : Type} [CommRing A] [CommRing C] [Field E] {k : A →+* C}
    {I : C →+* E} {c : A →+* E} (hI : ∀ x, I (k x) = c x) {p a : A} (hp : c p ≠ 0) {m : ℕ}
    {y : C} (ha : k a = k p ^ m * y) {z : E} (h : c a = c p ^ m * z) : z = I y := by
  have h1 := congrArg I ha
  rw [map_mul, map_pow, hI, hI, h] at h1
  exact mul_left_cancel₀ (pow_ne_zero m hp) h1

theorem onto_injective {A C E : Type} [CommRing A] [CommRing C] [Field E] {k : A →+* C}
    {I : C →+* E} {c : A →+* E} (hI : ∀ x, I (k x) = c x) (hc : Function.Injective c) :
    Function.Injective k := fun x y e => hc (by rw [← hI, ← hI, e])

theorem away_exists_self {A : Type} [CommRing A] {a : A} (y : Localization.Away a) :
    ∃ (k : ℕ) (x : A), algebraMap A (Localization.Away a) x =
      algebraMap A (Localization.Away a) a ^ k * y :=
  away_exists (RingHom.id _) _ (fun _ => rfl) y

theorem reg_isUnit {B C E : Type} [CommRing B] [CommRing C] [Field E] {i : B →+* E} {j : C →+* E}
    (hi : Function.Injective i) (h : ∀ c, ∃ b, i b = j c) {b : B} {c : C} (e : j c = i b)
    (hc : IsUnit c) : IsUnit b := by
  obtain ⟨c', hc'⟩ := hc.exists_right_inv
  obtain ⟨b', hb'⟩ := h c'
  refine IsUnit.of_mul_eq_one b' (hi ?_)
  rw [map_mul, ← e, hb', ← map_mul, hc', map_one, map_one]

theorem reg_ne_zero {B C E : Type} [CommRing B] [CommRing C] [Field E] {i : B →+* E} {j : C →+* E}
    (hi : Function.Injective i) {b : B} {c : C} (e : j c = i b) (hb : b ≠ 0) : c ≠ 0 := by
  rintro rfl
  exact hb (hi (by rw [← e, map_zero, map_zero]))

theorem reg_eigen {B C E : Type} [CommRing B] [CommRing C] [Field E] {i : B →+* E} {j : C →+* E}
    (hj : Function.Injective j) {b b₁ q : B} {c c₁ r : C} (e : j c = i b) {τ : E → E}
    (h1 : j c₁ = τ (j c)) (h2 : i b₁ = τ (i b)) (hq : j r = i q) (hb : b₁ = q * b) :
    c₁ = r * c := by
  apply hj
  rw [h1, e, ← h2, hb, map_mul, map_mul, hq, e]

theorem reg_range {B C E : Type} [CommRing B] [CommRing C] [Field E] {i : B →+* E} {j : C →+* E}
    {u b : B} (hu : IsUnit u) {t y c : C} {n : ℕ} (h : y = t ^ n * c) (ht : j t = i u)
    (hy : i b = j y) : ∃ x, i x = j c :=
  exists_map_eq_of_pow_mul i hu (k := n) (by rw [hy, h, map_mul, map_pow, ht])

end Abstract

section Concrete

open GroundTheory.PAdicHodge

variable {l : ℕ} [Fact l.Prime]

theorem onto_plus {y : ACris.BCrisPlus ℂ_[l] l} {n : ℕ}
    (hy : ACris.phiPlus ℂ_[l] l y = (l : ACris.BCrisPlus ℂ_[l] l) ^ n * y) :
    ∃ x : Per6.Bcris l, Per6.φB l x = x ∧ cD l (Per6.tA l) ^ n * ιCD l x = invPlusD l y := by
  obtain ⟨m, a, ha⟩ := away_exists_self y
  have h1 := onto_eigen (onto_injective invPlusD_algebraMap (cD_injective l))
    ACris.phiPlus_algebraMap ha hy
  obtain ⟨x, hx, e⟩ := onto_fixed φB_cB (cB_isFrac l) (map_natCast _ l) frob_phi_tA m h1
  exact ⟨x, hx, onto_cancel invPlusD_algebraMap (cD_l_ne_zero l) ha (inv_map_frac (ιCD_fac l) e)⟩

theorem cD_tA_eq : cD l (Per6.tA l) =
    algebraMap (Per6.BdRp l) (Per6.BdR l) (fontaineT (epsilon l) untilt_epsilon) :=
  congrArg (algebraMap (Per6.BdRp l) (Per6.BdR l)) (ACris.iota_periodT (untilt_epsilon (p := l)))

theorem fund_onto (z : Per6.BdR l) : ∃ x : Per6.Bcris l, Per6.φB l x = x ∧
    ∃ c : Per6.BdRp l, ιCD l x - z = algebraMap (Per6.BdRp l) (Per6.BdR l) c := by
  obtain ⟨n, w, hs⟩ := ACris.exists_mul_pow_fontaineT_eq (untilt_epsilon (p := l))
    untilt_frobeniusEquiv_symm_epsilon_ne_one z
  obtain ⟨y, hy, hyw⟩ := ACris.exists_phiPlus_eq_pow_iotaPlus_sub_mem (untilt_epsilon (p := l))
    untilt_frobeniusEquiv_symm_epsilon_ne_one (m := n) (n := n) le_rfl w
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hyw
  obtain ⟨x, hx, e⟩ := onto_plus hy
  rw [cD_tA_eq] at e
  exact ⟨x, hx, c, ACris.sub_eq_map_of_pow_mul (algebraMap (Per6.BdRp l) (Per6.BdR l))
    (cD_tA_eq (l := l) ▸ cD_tA_ne_zero l) e hs hc⟩

section Eps

variable {ε : PreTilt (normInteger ℂ_[l]) l} (hε : PreTilt.untilt ε = 1)
  (hζ : PreTilt.untilt ((_root_.frobeniusEquiv (PreTilt (normInteger ℂ_[l]) l) l).symm ε) ≠ 1)

set_option maxHeartbeats 1600000 in
theorem reg_exists_ιCD {u : Per6.Bcris l} (hu : IsUnit u)
    (e : algebraMap (Per6.BdRp l) (Per6.BdR l) (ACris.iota ℂ_[l] l (ACris.periodT hε)) = ιCD l u)
    (c : ACris.BCris hε) : ∃ b, ιCD l b = ACris.iotaB hε hζ c :=
  (ACris.exists_algebraMap_eq_periodTCris_pow_mul hε c).elim fun _ h₀ => h₀.elim fun y h =>
    (exists_ιCD_eq_iotaPlus y).elim fun _ hb =>
      reg_range hu h ((ACris.iotaB_periodTCris hε hζ).trans e)
        (hb.trans (ACris.iotaB_algebraMap hε hζ y).symm)

theorem reg_ιCD_qB (q : ℚ_[l]) : ιCD l (qB l q) = algebraMap ℚ_[l] (Per6.BdR l) q := by
  refine (ιCD_qB q).trans ?_
  rw [frob_oD_apply, AlgHom.commutes, ← IsScalarTower.algebraMap_apply]

set_option maxHeartbeats 1600000 in
theorem reg_galB_eigen {K : IntermediateField ℚ_[l] (Om l)} (σ : Gal(PadicAlgCl l/K))
    {b : Per6.Bcris l} {c : ACris.BCris hε} (e : ACris.iotaB hε hζ c = ιCD l b) {q : ℚ_[l]}
    (hq : Per6.σB (σ.restrictScalars ℚ_[l]) b = qB l q * b) :
    ACris.galB hε σ c = algebraMap ℚ_[l] (ACris.BCris hε) q * c :=
  reg_eigen (ACris.iotaB_injective hε hζ) e (τ := Per6.σD (σ.restrictScalars ℚ_[l]))
    ((ACris.iotaB_galB hε hζ σ c).trans ((gal_smul_bDeRham_def σ _).trans
      (congrArg (fun f : Per6.BdR l ≃+* Per6.BdR l => f (ACris.iotaB hε hζ c))
        (inv_galBdRField_eq σ))))
    (ιCD_σB _ b) ((ACris.iotaB_algebraMap_padic hε hζ q).trans (reg_ιCD_qB q).symm) hq

include hζ in
set_option maxHeartbeats 1600000 in
theorem reg_core (K : FinExt l) {u : Per6.Bcris l} (hu : IsUnit u)
    (eu : algebraMap (Per6.BdRp l) (Per6.BdR l) (ACris.iota ℂ_[l] l (ACris.periodT hε)) = ιCD l u)
    {b : Per6.Bcris l} (hb0 : b ≠ 0) (hb : ∀ g ∈ GK K, ∃ q : ℚ_[l], Per6.σB g b = qB l q * b)
    {n : ℕ} {y : ACris.BCrisPlus ℂ_[l] l}
    (h : invPlusD l y = cD l (ACris.periodT hε) ^ n * ιCD l b) : IsUnit b := by
  have := K.2
  obtain ⟨c, e⟩ := inv_exists_iotaB hε hζ h
  refine reg_isUnit ιCD_injective (reg_exists_ιCD hε hζ hu eu) e
    (ACris.isUnit_of_galB_eigen hε hζ (K := K.1) (reg_ne_zero ιCD_injective e hb0) fun σ => ?_)
  exact (hb _ (inv_restrictScalars_mem K σ)).imp fun _ hq => reg_galB_eigen hε hζ σ e hq

end Eps

set_option maxHeartbeats 1600000 in

theorem bcris_regular (K : FinExt l) {b : Per6.Bcris l} (hb0 : b ≠ 0)
    (hb : ∀ g ∈ GK K, ∃ q : ℚ_[l], Per6.σB g b = qB l q * b) : IsUnit b := by
  obtain ⟨n, y, h⟩ := inv_exists_plus b
  exact reg_core untilt_epsilon untilt_frobeniusEquiv_symm_epsilon_ne_one K isUnit_tB
    ((cD_apply (Per6.tA l)).symm.trans (ιCD_cB (Per6.tA l)).symm) hb0 hb h

end Concrete

theorem tied_regular : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P),
    LocTied6 l P AI → ∀ (K : FinExt l) (b : P.R.B), b ≠ 0 →
      (∀ g ∈ GK K, ∃ x : ℚ_[l], P.actQ g b = x • b) → IsUnit b := by
  intro l _ P AI T K b hb0 hb
  have h : IsUnit (T.eB b) := bcris_regular K ((map_ne_zero_iff _ T.eB.injective).2 hb0)
    fun g hg => by
      obtain ⟨q, hq⟩ := hb g hg
      exact ⟨q, by rw [← T.actB, hq, Algebra.smul_def, map_mul, tie_q]⟩
  simpa using h.map T.eB.symm

theorem tied_fund_onto : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P),
    LocTied6 l P AI → ∀ (K : FinExt l) (w : P.R.BdR),
      ∃ x : P.R.B, P.φB x = x ∧ P.ιB x - w ∈ (P.PD K).Fil 0 := by
  intro l _ P AI T K w
  obtain ⟨x, hx, c, hc⟩ := fund_onto (T.eD w)
  obtain ⟨x, rfl⟩ := T.eB.surjective x
  refine ⟨x, T.eB.injective ((T.frob x).trans hx), (tie_fil_zero T K _).2 ⟨c, ?_⟩⟩
  rw [map_sub, tie_ι, hc]

end PositivityTheory.LocInh
