import Mathlib
import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.SandwichNormalForm
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.SourceLatticeInvariance
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.LatticeNormalFormUnipotent
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormalFormAtPrime
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnipotentCharacterArgumentMulStabilizer

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.QNormal

noncomputable section

namespace GlobalTheory.Proof.localUnfoldingIntegrand_boundedSchwartz

variable {E : Type} [Field E] {n' c' n c : ℕ}

open NumberField IsDedekindDomain in
variable {E : Type} [Field E] {n' c' n c : ℕ} in
theorem _root_.GlobalTheory.Proof.localUnfoldingIntegrand_boundedSchwartz.chArg_add (x y : (Fin (n' + c') → E) →ₗ[E] (Fin (n + c) → E)) :
    _root_.Formalism.L2.Col.Loc.chArg (x + y) = _root_.Formalism.L2.Col.Loc.chArg x + _root_.Formalism.L2.Col.Loc.chArg y := by
  unfold _root_.Formalism.L2.Col.Loc.chArg
  simp only [LinearMap.add_apply, _root_.GlobalTheory.QNormal.atN_add, Finset.sum_add_distrib]

open NumberField IsDedekindDomain in
variable {E : Type} [Field E] {n' c' n c : ℕ} in
theorem _root_.GlobalTheory.Proof.localUnfoldingIntegrand_boundedSchwartz.chArg_smul (a : E) (x : (Fin (n' + c') → E) →ₗ[E] (Fin (n + c) → E)) :
    _root_.Formalism.L2.Col.Loc.chArg (a • x) = a * _root_.Formalism.L2.Col.Loc.chArg x := by
  unfold _root_.Formalism.L2.Col.Loc.chArg
  simp only [LinearMap.smul_apply, _root_.GlobalTheory.QNormal.atN_smul, Finset.mul_sum]

def freeMap (u : Loc.FC n' c' n c → E) : (Fin (n' + c') → E) →ₗ[E] (Fin (n + c) → E) :=
  Matrix.toLin' (Matrix.of fun (l : Fin (n + c)) (s : Fin (n' + c')) =>
    if hf : Loc.IsFree n' n c l.1 s.1 then u ⟨(l, s), hf⟩ else 0)

open NumberField IsDedekindDomain in
variable {E : Type} [Field E] {n' c' n c : ℕ} in
theorem _root_.GlobalTheory.Proof.localUnfoldingIntegrand_boundedSchwartz.periodXX1_add_smul (xj : (Fin n' → E) →ₗ[E] (Fin n → E))
    (t u : _root_.Formalism.L2.Col.Loc.FC n' c' n c → E) (a : E) :
    _root_.Formalism.L2.Col.Loc.xx1 xj (t + a • u) = _root_.Formalism.L2.Col.Loc.xx1 xj t + a • _root_.GlobalTheory.Proof.localUnfoldingIntegrand_boundedSchwartz.freeMap u := by
  unfold _root_.Formalism.L2.Col.Loc.xx1 _root_.GlobalTheory.Proof.localUnfoldingIntegrand_boundedSchwartz.freeMap
  rw [← map_smul, ← map_add]
  congr 1
  ext l s
  simp only [Matrix.of_apply, Matrix.add_apply, Matrix.smul_apply, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul]
  split_ifs <;> simp

variable [NumberField E] {P : HeightOneSpectrum (𝓞 E)}

open NumberField IsDedekindDomain in
variable {E : Type} [Field E] {n' c' n c : ℕ} in
variable [NumberField E] {P : HeightOneSpectrum (𝓞 E)} in
private lemma intAt_atN_of_intV {N : ℕ} {v : Fin N → E}
    (hv : _root_.GlobalTheory.QNormal.IntV P v) (i : ℕ) : _root_.Formalism.L2.Col.IntAt P (_root_.Formalism.L2.Col.Loc.atN v i) := by
  unfold _root_.Formalism.L2.Col.Loc.atN
  split_ifs with h
  · exact hv ⟨i, h⟩
  · exact _root_.GlobalTheory.IndefiniteRowSideFullHecke.SourceLatticeInvariance.intAt_zero P

open NumberField IsDedekindDomain in
variable {E : Type} [Field E] {n' c' n c : ℕ} in
variable [NumberField E] {P : HeightOneSpectrum (𝓞 E)} in
private lemma intV_eN' (N s : ℕ) :
    _root_.GlobalTheory.QNormal.IntV P (_root_.Formalism.L2.Col.Loc.eN E N s) := by
  intro l
  dsimp only [_root_.Formalism.L2.Col.Loc.eN]
  split_ifs
  · exact _root_.GlobalTheory.QNormal.intAt_one P
  · exact _root_.GlobalTheory.IndefiniteRowSideFullHecke.SourceLatticeInvariance.intAt_zero P

open NumberField IsDedekindDomain in
variable {E : Type} [Field E] {n' c' n c : ℕ} in
variable [NumberField E] {P : HeightOneSpectrum (𝓞 E)} in
theorem _root_.GlobalTheory.Proof.localUnfoldingIntegrand_boundedSchwartz.intAt_chArg
    {y : (Fin (n' + c') → E) →ₗ[E] (Fin (n + c) → E)} (hy : _root_.GlobalTheory.QNormal.IntHom P y) :
    _root_.Formalism.L2.Col.IntAt P (_root_.Formalism.L2.Col.Loc.chArg y) := by
  unfold _root_.Formalism.L2.Col.Loc.chArg
  exact _root_.GlobalTheory.QNormal.intAt_sum _ _ fun i _ =>
    intAt_atN_of_intV (hy _ (intV_eN' _ _)) _

open NumberField IsDedekindDomain in
variable {E : Type} [Field E] {n' c' n c : ℕ} in
variable [NumberField E] {P : HeightOneSpectrum (𝓞 E)} in
theorem _root_.GlobalTheory.Proof.localUnfoldingIntegrand_boundedSchwartz.intHom_freeMap {u : _root_.Formalism.L2.Col.Loc.FC n' c' n c → E}
    (hu : ∀ i, _root_.Formalism.L2.Col.IntAt P (u i)) : _root_.GlobalTheory.QNormal.IntHom P (_root_.GlobalTheory.Proof.localUnfoldingIntegrand_boundedSchwartz.freeMap u) := by
  rw [_root_.GlobalTheory.QNormal.intHom_iff]
  intro s l
  simp only [_root_.GlobalTheory.Proof.localUnfoldingIntegrand_boundedSchwartz.freeMap, Matrix.toLin'_apply, Matrix.mulVec_single_one,
    Matrix.transpose_apply, Matrix.col_apply, Matrix.of_apply]
  split_ifs with hf
  · exact hu _
  · exact _root_.GlobalTheory.IndefiniteRowSideFullHecke.SourceLatticeInvariance.intAt_zero P

open NumberField IsDedekindDomain in
variable {E : Type} [Field E] {n' c' n c : ℕ} in
variable [NumberField E] {P : HeightOneSpectrum (𝓞 E)} in

theorem _root_.GlobalTheory.Proof.localUnfoldingIntegrand_boundedSchwartz.integrand_bdd : ∀ (E : Type) [Field E] [NumberField E] (K : Type)
    [Field K] (P : HeightOneSpectrum (𝓞 E))
    (n' c' n c : ℕ) (psi : E → K) (D N : ℕ) (Psi : _root_.Formalism.L2.Col.Loc.SF E K (n' + c') (n + c)), N ≤ D →
    _root_.GlobalTheory.QNormal.CharTo P D psi → _root_.GlobalTheory.QNormal.HomBdd P N Psi →
    ∀ xj : (Fin n' → E) →ₗ[E] (Fin n → E),
      _root_.GlobalTheory.QNormal.FunBdd P N (_root_.GlobalTheory.QNormal.integrand psi Psi xj) ∧
      ∀ t : _root_.Formalism.L2.Col.Loc.FC n' c' n c → E, Psi (_root_.Formalism.L2.Col.Loc.xx1 xj t) ≠ 0 →
        _root_.Formalism.L2.Col.IntAt P ((_root_.Formalism.L2.Col.qOf P : E) ^ N * _root_.Formalism.L2.Col.Loc.chArg (_root_.Formalism.L2.Col.Loc.xx1 xj t)) := by
  intro E _ _ K _ P n' c' n c psi D N Psi hND hpsi hPsi xj
  obtain ⟨hPsi1, hPsi2⟩ := hPsi
  obtain ⟨hpsi1, hpsi2⟩ := hpsi
  have hchar : ∀ t : _root_.Formalism.L2.Col.Loc.FC n' c' n c → E, Psi (_root_.Formalism.L2.Col.Loc.xx1 xj t) ≠ 0 →
      _root_.Formalism.L2.Col.IntAt P ((_root_.Formalism.L2.Col.qOf P : E) ^ N * _root_.Formalism.L2.Col.Loc.chArg (_root_.Formalism.L2.Col.Loc.xx1 xj t)) := fun t ht => by
    rw [← _root_.GlobalTheory.Proof.localUnfoldingIntegrand_boundedSchwartz.chArg_smul]
    exact _root_.GlobalTheory.Proof.localUnfoldingIntegrand_boundedSchwartz.intAt_chArg (hPsi1 _ ht)
  refine ⟨?_, hchar⟩
  unfold _root_.GlobalTheory.QNormal.FunBdd
  refine ⟨fun t ht i => ?_, fun t u hu => ?_⟩
  · have hne : Psi (_root_.Formalism.L2.Col.Loc.xx1 xj t) ≠ 0 := fun h => ht (by simp [_root_.GlobalTheory.QNormal.integrand, h])
    have hint := (_root_.GlobalTheory.QNormal.intHom_iff _).1 (hPsi1 _ hne)
    obtain ⟨⟨l, s⟩, hf⟩ := i
    have hentry := hint s l
    simpa only [LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul,
      _root_.GlobalTheory.QNormal.linearMap_unfolding_apply_single, dif_pos hf] using hentry
  · have hfree := _root_.GlobalTheory.Proof.localUnfoldingIntegrand_boundedSchwartz.intHom_freeMap (P := P) hu
    have hPsi_eq : Psi (_root_.Formalism.L2.Col.Loc.xx1 xj (t + (_root_.Formalism.L2.Col.qOf P : E) ^ N • u)) = Psi (_root_.Formalism.L2.Col.Loc.xx1 xj t) := by
      rw [_root_.GlobalTheory.Proof.localUnfoldingIntegrand_boundedSchwartz.periodXX1_add_smul]
      exact hPsi2 _ _ hfree
    simp only [_root_.GlobalTheory.QNormal.integrand, hPsi_eq]
    by_cases h0 : Psi (_root_.Formalism.L2.Col.Loc.xx1 xj t) = 0
    · simp [h0]
    · congr 1
      rw [_root_.GlobalTheory.Proof.localUnfoldingIntegrand_boundedSchwartz.periodXX1_add_smul, _root_.GlobalTheory.Proof.localUnfoldingIntegrand_boundedSchwartz.chArg_add,
        _root_.GlobalTheory.Proof.localUnfoldingIntegrand_boundedSchwartz.chArg_smul, neg_add]
      have hx : _root_.Formalism.L2.Col.IntAt P ((_root_.Formalism.L2.Col.qOf P : E) ^ D * -_root_.Formalism.L2.Col.Loc.chArg (_root_.Formalism.L2.Col.Loc.xx1 xj t)) := by
        rw [mul_neg]
        exact _root_.GlobalTheory.IndefiniteRowSideFullHecke.SourceLatticeInvariance.intAt_neg (_root_.GlobalTheory.Proof.NormalFormAtPrime.intAt_pow_mono hND (hchar t h0))
      have hy : _root_.Formalism.L2.Col.IntAt P (-((_root_.Formalism.L2.Col.qOf P : E) ^ N * _root_.Formalism.L2.Col.Loc.chArg (_root_.GlobalTheory.Proof.localUnfoldingIntegrand_boundedSchwartz.freeMap u))) :=
        _root_.GlobalTheory.IndefiniteRowSideFullHecke.SourceLatticeInvariance.intAt_neg (_root_.GlobalTheory.Proof.NormalFormAtPrime.intAt_pow_mul N
          (_root_.GlobalTheory.Proof.localUnfoldingIntegrand_boundedSchwartz.intAt_chArg hfree))
      rw [hpsi1 _ _ hx (_root_.GlobalTheory.Proof.NormalFormAtPrime.intAt_pow_mul D hy), hpsi2 _ hy, mul_one]

end GlobalTheory.Proof.localUnfoldingIntegrand_boundedSchwartz
