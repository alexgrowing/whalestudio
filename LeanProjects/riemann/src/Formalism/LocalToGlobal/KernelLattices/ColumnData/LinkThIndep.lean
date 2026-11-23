import Mathlib
import Formalism.LocalToGlobal.KernelLattices.ColumnData

noncomputable section

namespace Formalism.L2.Ker.Cd.IntegralLatticeDensity

open Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity hiding CMConjEmb CMTransitive DedekindFactor LinkChi LinkPer LinkThIndep LinkThU LinkThUFam ThetaNormIndependent theta_norm_independent_of_bounds th22U theta_norm_unitary_invariant_of_bounds

open NumberField Formalism.BasicNotions MeasureTheory
open Formalism.L2.Ker.Cd.TaylorLogMetric
open Formalism.MainNotions.TaylorLogMetric hiding admitted AdmittedStatements AllSplit CoefIn DataIn DualB EqAt EqAway FamE Hf IdE InProd Iop IsChi IsComb IsCurveIdeal IsDiscriminantTwelfthRootOfIdealLattice IsFrobC IsIdem JetsInt La LocBasis LocBasisW Mono N1 NNBasis OrthoBasisW Orthonormal Pos Qd QdB Stmt TVar TVarB Th ThSp Tor TorsPrime U VC Wop XiF YYl adm1 al atLog chK chg chgB coordV der detId logDerivativeAtOne ellT embT embV eq22 fF fnConj hYY hh homL int22 jet kap lamOf letterOf liftY logOmVal meanLogNormSq meanLogOm mmM mom22 LargerSupportMomentCondition mono normSq pSer pairN per22 posEmb posG aux₃ pull qH sE sgm str22 tauEmb tauSg taylor th22 tor0 torConj vec22 vecN wPh zB

variable {D : Car} {N N' : ℕ}

theorem normSq_const_mul (T : Tor D) (La' : AddSubgroup (VC D N N')) (c : ℂ) (F : VC D N N' → ℂ) :
    normSq D T La' (fun z => c * F z) = ‖c‖ ^ 2 * normSq D T La' F := by
  unfold normSq
  simp only [norm_mul, mul_pow, mul_assoc]
  rw [MeasureTheory.average_eq, MeasureTheory.average_eq, MeasureTheory.integral_const_mul, smul_eq_mul, smul_eq_mul]
  ring

def IopIso (D : Car) (T : Tor D) : Prop :=
  ∀ N N' L₁ L₁' L₂ L₂', admitted D N N' L₁ L₁' → admitted D N N' L₂ L₂' → ∀ G ∈ Th D T L₁ L₁',
    normSq D T (La D T L₂ L₂') (Iop D T (La D T L₁ L₁') (La D T L₂ L₂') G) =
      normSq D T (La D T L₁ L₁') G

def ChiUnitDet (D : Car) (χ : IdE D → ℂ) : Prop :=
  letI := D.host.cmStar
  ∀ N (L L' : Submodule (𝓞 D.host.E) (Fin N → D.host.E)), Even N →
    IsSDLat D.host.E N L → IsSDLat D.host.E N L' → ‖χ (detId D L L')‖ = 1

theorem LinkThIndep_of
    (hI : ∀ D : Car, ∀ cc : Ideal (𝓞 D.host.K), IsCurveIdeal D cc → ∀ δ : ℂ, IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
      IopIso D (tor0 D cc δ))
    (hC : ∀ D : Car, ∀ χ : IdE D → ℂ, IsChi D χ → ChiUnitDet D χ) :
    LinkThIndep := by
  intro D cc hcc δ hδ χ e hχ hvec heq N N' L₁ L₁' L₂ L₂' h1 h2
  obtain ⟨hN, hN', hs1, hs1'⟩ := h1
  obtain ⟨-, -, hs2, hs2'⟩ := h2
  have hU := hC D χ hχ
  have hIso := hI D cc hcc δ hδ
  have hA21 : admitted D N N' L₂ L₁' := ⟨hN, hN', hs2, hs1'⟩
  have hA11 : admitted D N N' L₁ L₁' := ⟨hN, hN', hs1, hs1'⟩
  have hA22 : admitted D N N' L₂ L₂' := ⟨hN, hN', hs2, hs2'⟩
  have e1 := heq.2.1 N N' ⟨L₂, hs2⟩ ⟨L₁', hs1'⟩ ⟨L₂', hs2'⟩ hN hN'
  have e2 := heq.2.2 N N' ⟨L₁, hs1⟩ ⟨L₂, hs2⟩ ⟨L₁', hs1'⟩ hN hN'
  dsimp only at e1 e2
  rw [e1, normSq_const_mul, hIso N N' L₂ L₁' L₂ L₂' hA21 hA22 _ (hvec N N' L₂ L₁' hA21).1, e2,
    normSq_const_mul, hIso N N' L₁ L₁' L₂ L₁' hA11 hA21 _ (hvec N N' L₁ L₁' hA11).1,
    norm_zpow, hU N' L₁' L₂' hN' hs1' hs2', norm_zpow, hU N L₁ L₂ hN hs1 hs2]
  simp

end Formalism.L2.Ker.Cd.IntegralLatticeDensity

namespace Formalism.L2.Ker.Cd.IntegralLatticeDensity.CU

open Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity hiding CMConjEmb CMTransitive DedekindFactor LinkChi LinkPer LinkThIndep LinkThU LinkThUFam ThetaNormIndependent theta_norm_independent_of_bounds th22U theta_norm_unitary_invariant_of_bounds

open NumberField Formalism.BasicNotions Formalism.FrobeniusOrbits
open Formalism.L2.Ker.Cd.TaylorLogMetric
open Formalism.MainNotions.TaylorLogMetric hiding admitted AdmittedStatements AllSplit CoefIn DataIn DualB EqAt EqAway FamE Hf IdE InProd Iop IsChi IsComb IsCurveIdeal IsDiscriminantTwelfthRootOfIdealLattice IsFrobC IsIdem JetsInt La LocBasis LocBasisW Mono N1 NNBasis OrthoBasisW Orthonormal Pos Qd QdB Stmt TVar TVarB Th ThSp Tor TorsPrime U VC Wop XiF YYl adm1 al atLog chK chg chgB coordV der detId logDerivativeAtOne ellT embT embV eq22 fF fnConj hYY hh homL int22 jet kap lamOf letterOf liftY logOmVal meanLogNormSq meanLogOm mmM mom22 LargerSupportMomentCondition mono normSq pSer pairN per22 posEmb posG aux₃ pull qH sE sgm str22 tauEmb tauSg taylor th22 tor0 torConj vec22 vecN wPh zB

variable (D : Car)

theorem star_conj (x : D.host.E) : (letI := D.host.cmStar; star x) = D.host.conj x := by
  letI := D.host.cmStar
  let ψ : D.host.E →+* ℂ := (IsAlgClosed.lift : D.host.E →ₐ[ℚ] ℂ).toRingHom
  apply ψ.injective
  have h2 : ψ (D.host.conj x) = starRingEnd ℂ (ψ x) :=
    (D.host.der.conj_iff ψ D.host.conj).mpr (by simp [Formalism.HC.HostRaw.conj]) x
  rw [h2]
  haveI : IsCMField D.host.E := by
    first
    | exact D.host.isCMField_hostE
    | exact D.host.der.cm
  first
  | exact NumberField.IsCMField.complexEmbedding_complexConj D.host.E ψ x
  | exact NumberField.IsCMField.complexEmbedding_complexConj (K := D.host.E) ψ x
  | exact NumberField.IsCMField.complexEmbedding_complexConj (K := D.host.E) (φ := ψ) (x := x)

theorem emb_conj (φ : D.host.E →+* ℂ) (x : D.host.E) :
    φ (D.host.conj x) = starRingEnd ℂ (φ x) :=
  (D.host.der.conj_iff φ D.host.conj).mpr (by simp [Formalism.HC.HostRaw.conj]) x

theorem conj_conj (x : D.host.E) : D.host.conj (D.host.conj x) = x := by
  let ψ : D.host.E →+* ℂ := (IsAlgClosed.lift : D.host.E →ₐ[ℚ] ℂ).toRingHom
  apply ψ.injective
  rw [emb_conj, emb_conj, Complex.conj_conj]

def conjO (r : 𝓞 D.host.E) : 𝓞 D.host.E :=
  ⟨D.host.conj r, r.isIntegral_coe.map (D.host.conj : D.host.E →+* D.host.E).toIntAlgHom⟩

theorem conj_smul (r : 𝓞 D.host.E) (x : D.host.E) :
    D.host.conj (r • x) = conjO D r • D.host.conj x := by
  rw [Algebra.smul_def, Algebra.smul_def, map_mul]
  rfl

def cS (𝔞 : IdE D) : IdE D where
  carrier := {x | D.host.conj x ∈ 𝔞}
  add_mem' := fun ha hb => by
    simp only [Set.mem_ofPred_eq, map_add]; exact 𝔞.add_mem ha hb
  zero_mem' := by simp
  smul_mem' := fun r x hx => by
    show D.host.conj (r • x) ∈ 𝔞
    rw [conj_smul]; exact 𝔞.smul_mem _ hx

theorem mem_cS (𝔞 : IdE D) (x : D.host.E) : x ∈ cS D 𝔞 ↔ D.host.conj x ∈ 𝔞 := Iff.rfl

theorem cS_mul (𝔞 𝔟 : IdE D) : cS D (𝔞 * 𝔟) = cS D 𝔞 * cS D 𝔟 := by
  apply le_antisymm
  · intro x hx
    rw [mem_cS] at hx
    have key : ∀ y ∈ 𝔞 * 𝔟, D.host.conj y ∈ cS D 𝔞 * cS D 𝔟 := by
      intro y hy
      refine Submodule.mul_induction_on (C := fun y => D.host.conj y ∈ cS D 𝔞 * cS D 𝔟) hy ?_ ?_
      · intro a ha b hb
        rw [map_mul]
        exact Submodule.mul_mem_mul (by rw [mem_cS, conj_conj]; exact ha)
          (by rw [mem_cS, conj_conj]; exact hb)
      · intro y y' hy hy'
        rw [map_add]
        exact add_mem hy hy'
    have := key _ hx
    rwa [conj_conj] at this
  · rw [Submodule.mul_le]
    intro a ha b hb
    rw [mem_cS, map_mul]
    exact Submodule.mul_mem_mul ha hb

theorem cS_one : cS D 1 = 1 := by
  ext x
  rw [mem_cS, Submodule.mem_one, Submodule.mem_one]
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨conjO D y, ?_⟩
    change D.host.conj (y : D.host.E) = x
    rw [show ((y : D.host.E)) = algebraMap (𝓞 D.host.E) D.host.E y from rfl, hy, conj_conj]
  · rintro ⟨y, rfl⟩
    exact ⟨conjO D y, rfl⟩

theorem cS_pow (𝔞 : IdE D) (k : ℕ) : cS D (𝔞 ^ k) = cS D 𝔞 ^ k := by
  induction k with
  | zero => rw [pow_zero, pow_zero, cS_one]
  | succ k ih => rw [pow_succ, pow_succ, cS_mul, ih]

theorem cS_span (β : D.host.E) :
    cS D (Submodule.span (𝓞 D.host.E) {β}) = Submodule.span (𝓞 D.host.E) {D.host.conj β} := by
  ext x
  rw [mem_cS, Submodule.mem_span_singleton, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨r, hr⟩
    refine ⟨conjO D r, ?_⟩
    rw [← conj_smul, hr, conj_conj]
  · rintro ⟨r, rfl⟩
    refine ⟨conjO D r, ?_⟩
    rw [conj_smul, conj_conj]

theorem span_singleton_mul_span_singleton_host (a b : D.host.E) :
    Submodule.span (𝓞 D.host.E) {a} * Submodule.span (𝓞 D.host.E) {b} =
      Submodule.span (𝓞 D.host.E) {a * b} := by
  rw [Submodule.span_mul_span, Set.singleton_mul_singleton]

theorem normOne_ideal_iff_mul_conj (𝔞 : IdE D) : N1 D 𝔞 ↔ 𝔞 * cS D 𝔞 = 1 := by
  constructor
  · rintro ⟨𝔟, h𝔟, hmul⟩
    have e : 𝔟 = cS D 𝔞 := by
      ext x
      rw [h𝔟, mem_cS]
    rwa [← e]
  · intro h
    exact ⟨cS D 𝔞, fun x => mem_cS D 𝔞 x, h⟩

theorem normOne_ideal_mul {𝔞 𝔟 : IdE D} (ha : N1 D 𝔞) (hb : N1 D 𝔟) : N1 D (𝔞 * 𝔟) := by
  rw [normOne_ideal_iff_mul_conj] at ha hb ⊢
  rw [cS_mul, mul_mul_mul_comm, ha, hb, one_mul]

theorem normOne_ideal_pow {𝔞 : IdE D} (ha : N1 D 𝔞) (k : ℕ) : N1 D (𝔞 ^ k) := by
  induction k with
  | zero =>
    rw [pow_zero, normOne_ideal_iff_mul_conj, cS_one, one_mul]
  | succ k ih =>
    rw [pow_succ]
    exact normOne_ideal_mul D ih ha

theorem chi_pow (χ : IdE D → ℂ) (hχ : IsChi D χ) {𝔞 : IdE D} (ha : N1 D 𝔞) (k : ℕ) (hk : 1 ≤ k) :
    χ (𝔞 ^ k) = χ 𝔞 ^ k := by
  induction k, hk using Nat.le_induction with
  | base => rw [pow_one, pow_one]
  | succ k hk ih =>
    rw [pow_succ, hχ.1 _ _ (normOne_ideal_pow D ha k) ha, ih, pow_succ]

theorem pow_unitary {𝔞 : IdE D} (ha : N1 D 𝔞) :
    ∃ k : ℕ, 1 ≤ k ∧ ∃ z : D.host.E, z * D.host.conj z = 1 ∧
      𝔞 ^ k = Submodule.span (𝓞 D.host.E) {z} := by
  have hm := (normOne_ideal_iff_mul_conj D 𝔞).mp ha
  have hm' : cS D 𝔞 * 𝔞 = 1 := by rw [mul_comm]; exact hm
  have hfa : IsFractional (nonZeroDivisors (𝓞 D.host.E)) 𝔞 :=
    FractionalIdeal.isFractional_of_fg (Submodule.fg_of_isUnit ⟨⟨𝔞, cS D 𝔞, hm, hm'⟩, rfl⟩)
  have hfb : IsFractional (nonZeroDivisors (𝓞 D.host.E)) (cS D 𝔞) :=
    FractionalIdeal.isFractional_of_fg (Submodule.fg_of_isUnit ⟨⟨cS D 𝔞, 𝔞, hm', hm⟩, rfl⟩)
  let I : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E := ⟨𝔞, hfa⟩
  let J : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E := ⟨cS D 𝔞, hfb⟩
  have hIJ : I * J = 1 := by
    apply FractionalIdeal.coeToSubmodule_injective
    show ((I * J : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) : Submodule (𝓞 D.host.E) D.host.E) =
      ((1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) : Submodule (𝓞 D.host.E) D.host.E)
    rw [FractionalIdeal.coe_mul, FractionalIdeal.coe_one]; exact hm
  have hJI : J * I = 1 := by rw [mul_comm]; exact hIJ
  let u : (FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)ˣ := ⟨I, J, hIJ, hJI⟩
  set h := Fintype.card (ClassGroup (𝓞 D.host.E))
  have hpos : 0 < h := Fintype.card_pos
  have hcl : ClassGroup.mk (K := D.host.E) (u ^ h) = 1 := by rw [map_pow, pow_card_eq_one]
  rw [ClassGroup.mk_eq_one_iff] at hcl
  obtain ⟨β, hβ⟩ := hcl.principal
  have hah : 𝔞 ^ h = Submodule.span (𝓞 D.host.E) {β} := by
    rw [← hβ, Units.val_pow_eq_pow_val, FractionalIdeal.coe_pow]
    rfl
  have hbh : cS D 𝔞 ^ h = Submodule.span (𝓞 D.host.E) {D.host.conj β} := by
    rw [← cS_pow, hah, cS_span]
  have hone : Submodule.span (𝓞 D.host.E) {β * D.host.conj β} = 1 := by
    rw [← span_singleton_mul_span_singleton_host D, ← hah, ← hbh, ← mul_pow, hm, one_pow]
  have hβ0 : β ≠ 0 := by
    intro h0
    rw [h0, zero_mul, Submodule.span_singleton_eq_bot.mpr rfl] at hone
    have : (1 : D.host.E) ∈ (1 : IdE D) := Submodule.one_le.mp le_rfl
    rw [← hone] at this
    exact one_ne_zero ((Submodule.mem_bot _).mp this)
  have hβc0 : D.host.conj β ≠ 0 := by
    intro h0; apply hβ0; rw [← conj_conj D β, h0, map_zero]
  have hinv : Submodule.span (𝓞 D.host.E) {(β * D.host.conj β)⁻¹} = 1 := by
    have h2 : Submodule.span (𝓞 D.host.E) {(β * D.host.conj β)⁻¹} *
        Submodule.span (𝓞 D.host.E) {β * D.host.conj β} = 1 := by
      rw [span_singleton_mul_span_singleton_host D, inv_mul_cancel₀ (mul_ne_zero hβ0 hβc0),
        ← Submodule.one_eq_span]
    rwa [hone, mul_one] at h2
  refine ⟨2 * h, by omega, β / D.host.conj β, ?_, ?_⟩
  · rw [map_div₀, conj_conj]
    field_simp
  · have e : β / D.host.conj β = (β * β) * (β * D.host.conj β)⁻¹ := by
      field_simp
    rw [e, ← span_singleton_mul_span_singleton_host D, hinv, mul_one,
      ← span_singleton_mul_span_singleton_host D, ← hah, two_mul, pow_add]

theorem norm_chi_eq_one_of_normOne (χ : IdE D → ℂ) (hχ : IsChi D χ) {𝔞 : IdE D} (ha : N1 D 𝔞) : ‖χ 𝔞‖ = 1 := by
  obtain ⟨k, hk, z, hz, hpow⟩ := pow_unitary D ha
  letI := D.host.cmStar
  have hzu : z ∈ unitary D.host.E := by
    have e1 : star z * z = 1 := by rw [star_conj, mul_comm]; exact hz
    have e2 : z * star z = 1 := by rw [star_conj]; exact hz
    first
    | exact Unitary.mem_iff.mpr ⟨e1, e2⟩
    | exact ⟨e1, e2⟩

  have hn : ∀ τ, ‖embT D τ z‖ = 1 := by
    intro τ
    have h1 : embT D τ z * starRingEnd ℂ (embT D τ z) = 1 := by
      rw [← emb_conj, ← map_mul, hz, map_one]
    have h2 : ((‖embT D τ z‖ ^ 2 : ℝ) : ℂ) = 1 := by
      rw [← h1]
      first
      | exact (Complex.mul_conj' _).symm
      | (rw [Complex.mul_conj, Complex.normSq_eq_norm_sq])
    have h3 : ‖embT D τ z‖ ^ 2 = 1 := by exact_mod_cast h2
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).mp h3
  have hχk : χ 𝔞 ^ k = ∏ τ, (embT D τ z)⁻¹ := by
    rw [← chi_pow D χ hχ ha k hk, hpow]
    exact hχ.2 ⟨z, hzu⟩
  have hnorm : ‖χ 𝔞‖ ^ k = 1 := by
    rw [← norm_pow, hχk, norm_prod]
    simp [hn]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by omega)).mp hnorm

end Formalism.L2.Ker.Cd.IntegralLatticeDensity.CU

namespace Formalism.L2.Ker.Cd.IntegralLatticeDensity

open Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity hiding CMConjEmb CMTransitive DedekindFactor LinkChi LinkPer LinkThIndep LinkThU LinkThUFam ThetaNormIndependent theta_norm_independent_of_bounds th22U theta_norm_unitary_invariant_of_bounds

open NumberField Formalism.BasicNotions
open Formalism.L2.Ker.Cd.TaylorLogMetric
open Formalism.MainNotions.TaylorLogMetric hiding admitted AdmittedStatements AllSplit CoefIn DataIn DualB EqAt EqAway FamE Hf IdE InProd Iop IsChi IsComb IsCurveIdeal IsDiscriminantTwelfthRootOfIdealLattice IsFrobC IsIdem JetsInt La LocBasis LocBasisW Mono N1 NNBasis OrthoBasisW Orthonormal Pos Qd QdB Stmt TVar TVarB Th ThSp Tor TorsPrime U VC Wop XiF YYl adm1 al atLog chK chg chgB coordV der detId logDerivativeAtOne ellT embT embV eq22 fF fnConj hYY hh homL int22 jet kap lamOf letterOf liftY logOmVal meanLogNormSq meanLogOm mmM mom22 LargerSupportMomentCondition mono normSq pSer pairN per22 posEmb posG aux₃ pull qH sE sgm str22 tauEmb tauSg taylor th22 tor0 torConj vec22 vecN wPh zB

def DetIdealsKernelNormOne (D : Car) : Prop :=
  letI := D.host.cmStar
  ∀ N (L L' : Submodule (𝓞 D.host.E) (Fin N → D.host.E)), Even N →
    IsSDLat D.host.E N L → IsSDLat D.host.E N L' → N1 D (detId D L L')

theorem chi_unit_of_det_norm_one (D : Car) (hd : DetIdealsKernelNormOne D) (χ : IdE D → ℂ) (hχ : IsChi D χ) :
    ChiUnitDet D χ := by
  intro N L L' hN hL hL'
  exact CU.norm_chi_eq_one_of_normOne D χ hχ (hd N L L' hN hL hL')

theorem theta_norm_indep_of_det_norm_one
    (hI : ∀ D : Car, ∀ cc : Ideal (𝓞 D.host.K), IsCurveIdeal D cc → ∀ δ : ℂ, IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
      IopIso D (tor0 D cc δ))
    (hd : ∀ D : Car, DetIdealsKernelNormOne D) :
    LinkThIndep :=
  LinkThIndep_of hI fun D χ hχ => chi_unit_of_det_norm_one D (hd D) χ hχ

end Formalism.L2.Ker.Cd.IntegralLatticeDensity

end
