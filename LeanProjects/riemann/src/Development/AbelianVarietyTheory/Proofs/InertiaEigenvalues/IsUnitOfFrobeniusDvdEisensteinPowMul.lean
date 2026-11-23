import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaloisPrescribedUnramifiedKummer
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DvdSubOfDvdSubX
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeierstrassPreparationWittOfTiltFiniteFieldStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExpandMapDvdOfBreuilKisinFrobeniusDvdStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffZeroNeZeroOfWittFrobeniusExpandDvdStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAlgEquivExtendingWittTiltFrobeniusStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormLtOneOfIsRootDistinguishedWittPolynomialStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IrreducibleMapUnramifiedWittToFractionFieldOfEisStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormEqOfIsRootMinpolyUnramifiedRootsOfUnityFieldStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffEqZeroOfRootsContainLthRootsConjugatesStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

noncomputable section
namespace GlobalTheory.LemZ

theorem weier : ∀ (l : ℕ) [Fact l.Prime] (a : ℕ) [NeZero a] (g : (Wq l a)⟦X⟧), ¬ (l : (Wq l a)⟦X⟧) ∣ g →
    ∃ (P : Polynomial (Wq l a)) (U : (Wq l a)⟦X⟧), IsUnit U ∧ P.Monic ∧
      (∀ i < P.natDegree, (l : Wq l a) ∣ P.coeff i) ∧ g = U * (P : (Wq l a)⟦X⟧) := GlobalTheory.T.weierstrass_preparation_wittOfTiltFiniteField

theorem descend : ∀ (l : ℕ) [Fact l.Prime] (a : ℕ) [NeZero a] (P Q : Polynomial (Wq l a)), P.Monic →
    (∀ i < P.natDegree, (l : Wq l a) ∣ P.coeff i) → frobS l a (P : (Wq l a)⟦X⟧) ∣ (Q : (Wq l a)⟦X⟧) →
    Polynomial.expand (Wq l a) l (P.map (sigma l a : Wq l a →+* Wq l a)) ∣ Q := GlobalTheory.T.expand_map_dvd_of_breuilKisinFrobenius_dvd

theorem coeffZero : ∀ (l : ℕ) [Fact l.Prime] (a : ℕ) [NeZero a] (P E : Polynomial (Wq l a)) (M : ℕ), P.Monic → E.coeff 0 ≠ 0 →
    Polynomial.expand (Wq l a) l (P.map (sigma l a : Wq l a →+* Wq l a)) ∣ E ^ M * P → P.coeff 0 ≠ 0 := GlobalTheory.T.coeff_zero_ne_zero_of_wittFrobenius_expand_dvd

theorem frobAut : ∀ (l : ℕ) [Fact l.Prime] (a : ℕ) [NeZero a], ∃ Φ : Om l ≃ₐ[ℚ_[l]] Om l,
    ∀ w : Wq l a, Φ (GlobalTheory.TameFrob.iotaO l a w) = GlobalTheory.TameFrob.iotaO l a (sigma l a w) := GlobalTheory.T.exists_algEquiv_extending_wittTiltFrobenius

theorem rootLt : ∀ (l : ℕ) [Fact l.Prime] (a : ℕ) [NeZero a] (P : Polynomial (Wq l a)), P.Monic →
    (∀ i < P.natDegree, (l : Wq l a) ∣ P.coeff i) → ∀ x : Om l, (P.map (GlobalTheory.TameFrob.iotaO l a)).IsRoot x → ‖x‖ < 1 := GlobalTheory.T.norm_lt_one_of_isRoot_distinguished_witt_polynomial

theorem irr : ∀ (l : ℕ) [Fact l.Prime] (a : ℕ) [NeZero a] (E : Polynomial (Wq l a)), E.Monic → 0 < E.natDegree →
    (∀ i < E.natDegree, (l : Wq l a) ∣ E.coeff i) → (∃ w : (Wq l a)ˣ, E.coeff 0 = (l : Wq l a) * w) →
    Irreducible (E.map (GlobalTheory.TameFrob.iota l a)) := GlobalTheory.T.irreducible_map_unramifiedWittToFractionField_of_eisenstein

theorem conj : ∀ (l : ℕ) [Fact l.Prime] (a : ℕ) [NeZero a] (z z' : Om l),
    Polynomial.aeval z' (minpoly (↥(Kunr l a)) z) = 0 → ‖z'‖ = ‖z‖ := GlobalTheory.T.norm_eq_of_isRoot_minpoly_unramifiedRootsOfUnityField

theorem expandCoeff : ∀ (l : ℕ) [Fact l.Prime] (a : ℕ) [NeZero a] (E : Polynomial (Wq l a)), E.Monic →
    Irreducible (E.map (GlobalTheory.TameFrob.iota l a)) → ∀ z : Om l, z ≠ 0 →
    (∀ z' : Om l, Polynomial.aeval z' (minpoly (↥(Kunr l a)) z) = 0 → ∀ y : Om l, y ^ l = z' →
      (E.map (GlobalTheory.TameFrob.iotaO l a)).IsRoot y) →
    ∀ i, ¬ l ∣ i → E.coeff i = 0 := GlobalTheory.T.coeff_eq_zero_of_roots_contain_lth_roots_conjugates

theorem isUnit_of_frob_dvd : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K), ∀ g : bk.S, ¬ (l : bk.S) ∣ g →
    ∀ M : ℕ, frobS l bk.a g ∣ bk.E ^ M * g → IsUnit g := by
  intro l _ K bk g hg M hdvd
  classical
  obtain ⟨P, U, hU, hPm, hPd, rfl⟩ := weier l bk.a g hg
  have h1 : frobS l bk.a (P : (Wq l bk.a)⟦X⟧) ∣ ((bk.Ep ^ M * P : Polynomial (Wq l bk.a)) : (Wq l bk.a)⟦X⟧) := by
    rw [map_mul] at hdvd
    have h3 : frobS l bk.a (P : (Wq l bk.a)⟦X⟧) ∣ bk.E ^ M * (P : (Wq l bk.a)⟦X⟧) * U := by
      have := (dvd_mul_left _ _).trans hdvd
      rw [show bk.E ^ M * (U * (P : (Wq l bk.a)⟦X⟧)) = bk.E ^ M * (P : (Wq l bk.a)⟦X⟧) * U by ring] at this
      exact this
    rw [Polynomial.coe_mul, Polynomial.coe_pow]
    exact hU.dvd_mul_right.1 h3
  have h2 := descend l bk.a P _ hPm hPd h1
  by_cases hd : P.natDegree = 0
  · rw [Polynomial.eq_one_of_monic_natDegree_zero hPm hd, Polynomial.coe_one, mul_one]
    exact hU
  exfalso
  have hl0 : (l : Wq l bk.a) ≠ 0 := fun h => by
    have := congrArg (GlobalTheory.TameFrob.iotaO l bk.a) h
    rw [map_natCast, map_zero] at this
    exact (Fact.out : l.Prime).ne_zero (by exact_mod_cast this)
  have hE0 : bk.Ep.coeff 0 ≠ 0 := by
    obtain ⟨w, hw⟩ := bk.coeff_zero
    rw [hw]
    exact mul_ne_zero hl0 w.ne_zero
  have hP0 := coeffZero l bk.a P bk.Ep M hPm hE0 h2
  set ι := GlobalTheory.TameFrob.iotaO l bk.a with hι
  have hιinj : Function.Injective ι := GlobalTheory.TameFrob.iotaO_injective l bk.a
  set Pι := P.map ι with hPι
  have hPι0 : Pι ≠ 0 := (hPm.map ι).ne_zero
  have hdeg : Pι.degree ≠ 0 := by
    rw [hPι, Polynomial.degree_map_eq_of_injective hιinj, Polynomial.degree_eq_natDegree hPm.ne_zero]
    exact_mod_cast hd
  obtain ⟨x0, hx0⟩ := IsAlgClosed.exists_root Pι hdeg
  have hne : Pι.roots.toFinset.Nonempty := ⟨x0, Multiset.mem_toFinset.2 ((Polynomial.mem_roots hPι0).2 hx0)⟩
  obtain ⟨x, hxs, hxmax⟩ := Finset.exists_max_image _ (fun y : Om l => ‖y‖) hne
  have hx : Pι.IsRoot x := (Polynomial.mem_roots hPι0).1 (Multiset.mem_toFinset.1 hxs)
  have hmax : ∀ y : Om l, Pι.IsRoot y → ‖y‖ ≤ ‖x‖ := fun y hy =>
    hxmax y (Multiset.mem_toFinset.2 ((Polynomial.mem_roots hPι0).2 hy))
  set r := ‖x‖ with hr
  have hr1 : r < 1 := rootLt l bk.a P hPm hPd x hx
  have hxne : x ≠ 0 := by
    rintro rfl
    apply hP0
    apply hιinj
    rw [map_zero, Polynomial.coeff_zero_eq_eval_zero, ← Polynomial.eval_zero_map]
    exact hx
  have hr0 : 0 < r := norm_pos_iff.2 hxne
  obtain ⟨Φ, hΦ⟩ := frobAut l bk.a
  have hn : ∀ y, ‖Φ y‖ = ‖y‖ := fun y => (spectralNorm_eq_of_equiv Φ y).symm
  set z := Φ x with hzdef
  have hz : ‖z‖ = r := hn x
  have hz0 : z ≠ 0 := fun h => by rw [h, norm_zero] at hz; exact hr0.ne hz
  set Q := P.map (sigma l bk.a : Wq l bk.a →+* Wq l bk.a) with hQ
  have hQι : Q.map ι = Pι.map (Φ : Om l →+* Om l) := by
    rw [hQ, hPι, Polynomial.map_map, Polynomial.map_map]
    congr 1
    ext w
    exact (hΦ w).symm
  have hzQ : (Q.map ι).IsRoot z := by
    rw [hQι]
    exact hx.map
  have hcomp : (algebraMap (↥(Kunr l bk.a)) (Om l)).comp (GlobalTheory.TameFrob.iota l bk.a) = ι := RingHom.ext fun w => rfl
  have haev : ∀ y : Om l, Polynomial.aeval y (Q.map (GlobalTheory.TameFrob.iota l bk.a)) = (Q.map ι).eval y := fun y => by
    rw [Polynomial.aeval_def, Polynomial.eval₂_map, hcomp, Polynomial.eval_map]
  have hmdvd : minpoly (↥(Kunr l bk.a)) z ∣ Q.map (GlobalTheory.TameFrob.iota l bk.a) := by
    apply minpoly.dvd
    rw [haev]
    exact hzQ
  have key : ∀ z' : Om l, Polynomial.aeval z' (minpoly (↥(Kunr l bk.a)) z) = 0 → ∀ y : Om l, y ^ l = z' →
      (bk.Ep.map ι).IsRoot y := by
    intro z' hz' y hy
    have hnz' : ‖z'‖ = r := (conj l bk.a z z' hz').trans hz
    have hz'Q : (Q.map ι).IsRoot z' := by
      obtain ⟨c, hc⟩ := hmdvd
      rw [Polynomial.IsRoot, ← haev, hc, map_mul, hz', zero_mul]
    have hyE : ((bk.Ep ^ M * P).map ι).IsRoot y := by
      have h4 : ((Polynomial.expand (Wq l bk.a) l Q).map ι).IsRoot y := by
        rw [Polynomial.IsRoot, Polynomial.map_expand, Polynomial.expand_eval, hy]
        exact hz'Q
      obtain ⟨c, hc⟩ := h2
      rw [Polynomial.IsRoot, hc, Polynomial.map_mul, Polynomial.eval_mul, h4.eq_zero, zero_mul]
    have hyr : r < ‖y‖ := by
      by_contra hle
      push_neg at hle
      have h5 : ‖y‖ ^ l = r := by rw [← norm_pow, hy, hnz']
      have h6 : r ^ l < r := pow_lt_self_of_lt_one₀ hr0 hr1 (Fact.out : l.Prime).one_lt
      have h7 : ‖y‖ ^ l ≤ r ^ l := pow_le_pow_left₀ (norm_nonneg _) hle l
      linarith
    have hyP : ¬ Pι.IsRoot y := fun h => absurd (hmax y h) (not_le.2 hyr)
    rw [Polynomial.IsRoot, Polynomial.map_mul, Polynomial.map_pow, Polynomial.eval_mul, Polynomial.eval_pow] at hyE
    have h8 := (mul_eq_zero.1 hyE).resolve_right hyP
    rcases Nat.eq_zero_or_pos M with hM | hM
    · rw [hM, pow_zero] at h8; exact absurd h8 one_ne_zero
    · exact (pow_eq_zero_iff hM.ne').1 h8
  have hirr := irr l bk.a bk.Ep bk.monic bk.deg_pos bk.dvd_coeff bk.coeff_zero
  have hc := expandCoeff l bk.a bk.Ep bk.monic hirr z hz0 key
  obtain ⟨i, hi, hci⟩ := bk.not_expand
  exact hci (hc i hi)

end GlobalTheory.LemZ
