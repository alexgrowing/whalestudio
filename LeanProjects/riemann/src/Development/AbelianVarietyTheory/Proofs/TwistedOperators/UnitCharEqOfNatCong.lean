import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryAdelicInfFinSplitPeriodsUnimodular
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompAtMtOfMemGfC
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLowestKTypeFockMapThetaVectors
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DualTypePlacesIsSplitNonconjugateOfAdmissible
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchrodingerIntertwinerSchwartzBruhatIsTheta
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHomLatticeIffFrameStabilizerActMem
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FrameMatrixMovedHomIntegralReduction
import Formalism.LocalToGlobal.Divisibility.DefGroupLemmas
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEqMulOfResSNeOne
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemRangeOfOneTmulMem
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

noncomputable section

namespace GlobalTheory.UnitCharCong

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped Pointwise TensorProduct InnerProductSpace ComplexOrder
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle

variable {D : D7}

local notation "OO" => Formalism.L2.Herm.intAf D.host.F D.host.E

theorem hom_sum {R R' ι : Type} [CommRing R] [CommRing R'] (f : R →+* R') (p : ι → R) (s : Finset ι) :
    f (∑ i ∈ s, p i) = ∑ i ∈ s, f (p i) := map_sum f p s

theorem hom_shift {R κ : Type} [CommRing R] [CommRing κ] (f : R →+* κ) {a b z u u' : R} (h0 : f a * f b = 0)
    (hu' : u' = u + a * (b * z)) : f u' = f u := by
  rw [hu', map_add, map_mul, map_mul, ← mul_assoc, h0, zero_mul, add_zero]

theorem hom_natCast {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') (n : ℕ) : f n = n := map_natCast f n

theorem toEAf_surj (z : EAf D) : ∃ w : AE D, infPart D w = 0 ∧ toEAf D w = z := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, RingHom.map_zero _, RingHom.map_zero _⟩
  | tmul b α =>
    refine ⟨pairA D.host.F 0 α ⊗ₜ[D.host.F] b, ?_, rfl⟩
    change (fstA D.host.F (pairA D.host.F 0 α)) ⊗ₜ[D.host.F] b = 0
    rw [show fstA D.host.F (pairA D.host.F 0 α) = 0 from rfl, TensorProduct.zero_tmul]
  | add x y hx hy =>
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨b, hb, rfl⟩ := hy
    exact ⟨a + b, by rw [RingHom.map_add, ha, hb, add_zero], RingHom.map_add _ _ _⟩

theorem finPart_eq_of_toEAf {a b : AE D} (h : toEAf D a = toEAf D b) : finPart D a = finPart D b :=
  (Algebra.TensorProduct.comm D.host.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.host.E).injective h

theorem eq_of_parts {a b : AE D} (h1 : infPart D a = infPart D b) (h2 : toEAf D a = toEAf D b) : a = b := by
  rw [← sub_eq_zero]
  refine GlobalTheory.LatVac.eq_zero_of_parts _ ?_ ?_
  · rw [RingHom.map_sub, h1, sub_self]
  · rw [RingHom.map_sub, finPart_eq_of_toEAf h2, sub_self]

theorem exists_unit {u v : EAf D} (huv : u * v = 1) :
    ∃ x : (AE D)ˣ, infPart D (x : AE D) = 1 ∧ toEAf D (x : AE D) = u ∧ toEAf D ((x⁻¹ : (AE D)ˣ) : AE D) = v := by
  obtain ⟨g₁, a₁, b₁⟩ := toEAf_surj (1 : EAf D)
  obtain ⟨g, a₂, b₂⟩ := toEAf_surj u
  obtain ⟨g', a₃, b₃⟩ := toEAf_surj v
  have w₁ : infPart D (1 - g₁) = 1 := by rw [RingHom.map_sub, a₁, RingHom.map_one, sub_zero]
  have w₀ : toEAf D (1 - g₁) = 0 := by rw [RingHom.map_sub, b₁, RingHom.map_one, sub_self]
  have h : (1 - g₁ + g) * (1 - g₁ + g') = 1 := eq_of_parts
    (by simp only [RingHom.map_mul, RingHom.map_add, w₁, a₂, a₃, RingHom.map_one, add_zero, mul_one])
    (by simp only [RingHom.map_mul, RingHom.map_add, w₀, b₂, b₃, RingHom.map_one, zero_add, huv])
  refine ⟨⟨_, _, h, by rw [mul_comm]; exact h⟩, ?_, ?_, ?_⟩
  · change infPart D (1 - g₁ + g) = 1
    rw [RingHom.map_add, w₁, a₂, add_zero]
  · change toEAf D (1 - g₁ + g) = u
    rw [RingHom.map_add, w₀, b₂, zero_add]
  · change toEAf D (1 - g₁ + g') = v
    rw [RingHom.map_add, w₀, b₃, zero_add]

theorem res_idem_off {a : AE D} {P Q : Pl D.host.E} (ha : Formalism.L2.NTheta.IsIdemAt a P) (hQ : Q ≠ P)
    (h : toEAf D a ∈ OO) : resS D.host.F Q ⟨toEAf D a, h⟩ = 0 := by
  obtain ⟨x, hxQ, hxP⟩ : ∃ x ∈ Q.asIdeal, x ∉ P.asIdeal := by
    by_contra hc
    push Not at hc
    exact hQ (HeightOneSpectrum.ext (Q.isMaximal.eq_of_le P.isMaximal.ne_top hc))
  have hx0 : x ≠ 0 := fun h0 => hxP (h0 ▸ P.asIdeal.zero_mem)
  have hx0' : (x : D.host.E) ≠ 0 := fun h => hx0 (RingOfIntegers.coe_eq_zero_iff.1 h)
  have hmem : finPart D (a * incA D ((x : D.host.E)⁻¹)) ∈ intAE D := by
    by_contra hn
    exact hxP ((ha.2 x hx0).2 hn)
  have hs := GlobalTheory.IdemRes.toEAf_mem_of_finPart hmem
  have e1 : (⟨toEAf D a, h⟩ : OO) = ⟨_, hs⟩ * oToS D.host.F D.host.E x := Subtype.ext (by
    change toEAf D a = toEAf D (a * incA D ((x : D.host.E)⁻¹)) * eToEAf D (x : D.host.E)
    have h2 : toEAf D (incA D ((x : D.host.E)⁻¹)) = eToEAf D ((x : D.host.E)⁻¹) := rfl
    rw [RingHom.map_mul, h2, mul_assoc, ← RingHom.map_mul, inv_mul_cancel₀ hx0', RingHom.map_one, mul_one])
  rw [e1, RingHom.map_mul, resS_oToS, Ideal.Quotient.eq_zero_iff_mem.2 hxQ, mul_zero]

theorem res_off {e : AE D} {S : Finset (Pl D.host.E)} (he : IsIdemSum e S) (h : toEAf D e ∈ OO) {Q : Pl D.host.E}
    (hQ : Q ∉ S) : resS D.host.F Q ⟨toEAf D e, h⟩ = 0 := by
  obtain ⟨⟨es, hes, hs⟩, -⟩ := he
  have hi : ∀ P ∈ S, toEAf D (es P) ∈ OO := fun P hP => (GlobalTheory.IdemRes.resS_idem_eq_one D _ _ (hes P hP)).1
  have e1 : (⟨toEAf D e, h⟩ : OO) = ∑ P ∈ S.attach, ⟨toEAf D (es P.1), hi P.1 P.2⟩ := Subtype.ext (by
    refine Eq.trans ?_ (hom_sum (OO).subtype _ _).symm
    change toEAf D e = ∑ P ∈ S.attach, toEAf D (es P.1)
    rw [hs, hom_sum, Finset.sum_attach S fun P => toEAf D (es P)])
  rw [e1, hom_sum]
  exact Finset.sum_eq_zero fun P _ => res_idem_off (hes P.1 P.2) (fun hh => hQ (by rw [hh]; exact P.2)) _

theorem isUnit_add {e : AE D} {S : Finset (Pl D.host.E)} (he : IsIdemSum e S) (h : toEAf D e ∈ OO) {c : ℕ}
    (hc : ∀ P ∈ S, ((c : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal) {u u' z : OO} (hu : IsUnit u)
    (hu' : u' = u + ⟨toEAf D e, h⟩ * ((c : OO) * z)) : IsUnit u' := by
  refine isUnit_of_resS_ne_zero D.sp.cm _ fun Q => ?_
  have := Q.isPrime
  have h0 : resS D.host.F Q ⟨toEAf D e, h⟩ * resS D.host.F Q (c : OO) = 0 := by
    by_cases hQ : Q ∈ S
    · have h1 : resS D.host.F Q (c : OO) = Ideal.Quotient.mk Q.asIdeal ((c : ℕ) : 𝓞 D.host.E) := by
        rw [hom_natCast (Ideal.Quotient.mk Q.asIdeal), ← hom_natCast (resS D.host.F Q)]
      rw [h1, Ideal.Quotient.eq_zero_iff_mem.2 (hc Q hQ), mul_zero]
    · rw [res_off he h hQ, zero_mul]
  exact (hom_shift (resS D.host.F Q) h0 hu').symm ▸ (hu.map (resS D.host.F Q)).ne_zero

theorem det_cong {R : Type} [CommRing R] {k : ℕ} {A B : Matrix (Fin k) (Fin k) R} {c : R}
    (h : ∀ i j, ∃ z, B i j = A i j + c * z) : ∃ z, B.det = A.det + c * z := by
  have e : (Ideal.Quotient.mk (Ideal.span {c})).mapMatrix B = (Ideal.Quotient.mk (Ideal.span {c})).mapMatrix A := by
    ext i j
    obtain ⟨z, hz⟩ := h i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, hz, RingHom.map_add, RingHom.map_mul]
    rw [Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self c), zero_mul, add_zero]
  have e2 : Ideal.Quotient.mk (Ideal.span {c}) B.det = Ideal.Quotient.mk (Ideal.span {c}) A.det := by
    rw [RingHom.map_det, RingHom.map_det, e]
  obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq.1 e2)
  exact ⟨z, by linear_combination -hz⟩

theorem det_cong_int {k : ℕ} {N N' Z : Matrix (Fin k) (Fin k) (EAf D)} (hN : IsIntM N) (hZ : IsIntM Z) {c : ℕ}
    (h : ∀ i j, N' i j = N i j + c * Z i j) : ∃ hd : N.det ∈ OO, ∃ hd' : N'.det ∈ OO, ∃ z : OO,
      (⟨N'.det, hd'⟩ : OO) = ⟨N.det, hd⟩ + c * z := by
  have hN' : IsIntM N' := fun i j => by
    rw [h]
    exact add_mem (hN i j) (mul_mem (natCast_mem _ _) (hZ i j))
  let A : Matrix (Fin k) (Fin k) OO := fun i j => ⟨N i j, hN i j⟩
  let B : Matrix (Fin k) (Fin k) OO := fun i j => ⟨N' i j, hN' i j⟩
  have eA : N.det = ((A.det : OO) : EAf D) := by
    have := RingHom.map_det (OO).subtype A
    rw [show N = (OO).subtype.mapMatrix A from rfl]
    exact this.symm
  have eB : N'.det = ((B.det : OO) : EAf D) := by
    have := RingHom.map_det (OO).subtype B
    rw [show N' = (OO).subtype.mapMatrix B from rfl]
    exact this.symm
  obtain ⟨z, hz⟩ := det_cong (A := A) (B := B) (c := (c : OO)) fun i j => ⟨⟨Z i j, hZ i j⟩, Subtype.ext (h i j)⟩
  refine ⟨eA ▸ A.det.2, eB ▸ B.det.2, z, Subtype.ext ?_⟩
  have := congrArg Subtype.val hz
  simpa [eA, eB] using this

theorem coe_nat {R : Type} [CommRing R] (A : Subring R) (n : ℕ) : (((n : A)) : R) = n := map_natCast A.subtype n

theorem hom_nsmul {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') (n : ℕ) (a : R) : f (n • a) = n • f a :=
  map_nsmul f n a

theorem ring_id {R : Type} [CommRing R] {t t' ti ε d d' n c z : R} (a : t = 1 - ε + ε * d) (b : t' = 1 - ε + ε * d')
    (hz : d' = d + n * c * z) (hm : t * ti = 1) : t' * ti - 1 = n * (ε * (c * z) * ti) := by
  subst a b hz
  linear_combination hm

theorem ring_id' {R : Type} [CommRing R] {ε d d' c z : R} (hz : d' = d + c * z) :
    1 - ε + ε * d' = (1 - ε + ε * d) + ε * (c * z) := by
  subst hz
  ring

theorem toEAf_mem {e : AE D} {S : Finset (Pl D.host.E)} (he : IsIdemSum e S) : toEAf D e ∈ OO :=
  GlobalTheory.IdemRes.toEAf_mem_of_finPart (GlobalTheory.AdIdem.idempotent_mem_intAE D _
    (by rw [← RingHom.map_mul, GlobalTheory.PlaceDatum.idemSum_mul_self he]))

theorem exists_isUnitDet {e : AE D} {S : Finset (Pl D.host.E)} (he : IsIdemSum e S) {c : ℕ}
    (hc : ∀ P ∈ S, ((c : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal) {k : ℕ} {N N' Z : Matrix (Fin k) (Fin k) (EAf D)}
    (hN : IsIntM N) (hZ : IsIntM Z) (h : ∀ i j, N' i j = N i j + c * Z i j)
    (hx : ∃ x, IsUnitDet e N x) : ∃ x, IsUnitDet e N' x := by
  obtain ⟨x, h1, h2, h3⟩ := hx
  have hE := toEAf_mem he
  obtain ⟨hd, hd', z, hz⟩ := det_cong_int hN hZ h
  have hzv : N'.det = N.det + (c : EAf D) * (z : EAf D) := by
    have := congrArg Subtype.val hz
    rw [← coe_nat (OO) c]
    exact this
  have hu : toEAf D (x : AE D) ∈ OO := by
    rw [h2]
    exact add_mem (sub_mem (one_mem _) hE) (mul_mem hE hd)
  have hu' : 1 - toEAf D e + toEAf D e * N'.det ∈ OO := add_mem (sub_mem (one_mem _) hE) (mul_mem hE hd')
  have hxx : (⟨_, hu⟩ : OO) * ⟨_, h3⟩ = 1 := Subtype.ext (by
    change toEAf D (x : AE D) * toEAf D ((x⁻¹ : (AE D)ˣ) : AE D) = 1
    rw [← RingHom.map_mul, Units.mul_inv, RingHom.map_one])
  have hU : IsUnit (⟨_, hu⟩ : OO) := IsUnit.of_mul_eq_one _ hxx
  have hU' : IsUnit (⟨_, hu'⟩ : OO) := isUnit_add he hE hc hU (z := z) (Subtype.ext (by
    change 1 - toEAf D e + toEAf D e * N'.det = toEAf D (x : AE D) + toEAf D e * (((c : OO) : EAf D) * (z : EAf D))
    rw [coe_nat, h2]
    exact ring_id' hzv))
  obtain ⟨w, hw⟩ := hU'.exists_right_inv
  obtain ⟨x', a, b, d⟩ := exists_unit (u := 1 - toEAf D e + toEAf D e * N'.det) (v := (w : EAf D)) (congrArg Subtype.val hw)
  exact ⟨x', a, b, by rw [d]; exact w.2⟩

set_option maxHeartbeats 2000000 in

theorem nu_eq {ν : (AE D)ˣ →* Circle} {e : AE D} {S : Finset (Pl D.host.E)} (he : IsIdemSum e S) {n c : ℕ}
    (hl : ∀ x, Formalism.L2.Pj.FinUnit x → (∃ y ∈ intAE D, finPart D (x : AE D) - 1 = n • y) → ν x = 1) {k : ℕ}
    {N N' Z : Matrix (Fin k) (Fin k) (EAf D)} (hN : IsIntM N) (hZ : IsIntM Z)
    (h : ∀ i j, N' i j = N i j + ((n * c : ℕ) : EAf D) * Z i j) {x x' : (AE D)ˣ} (hx : IsUnitDet e N x)
    (hx' : IsUnitDet e N' x') : ν x = ν x' := by
  obtain ⟨a1, a2, a3⟩ := hx
  obtain ⟨b1, b2, b3⟩ := hx'
  have hE := toEAf_mem he
  obtain ⟨hd, hd', z, hz⟩ := det_cong_int hN hZ h
  have hzv : N'.det = N.det + (n : EAf D) * (c : EAf D) * (z : EAf D) := by
    have := congrArg Subtype.val hz
    rw [← Nat.cast_mul, ← coe_nat (OO) (n * c)]
    exact this
  have hX : toEAf D (x : AE D) ∈ OO := by
    rw [a2]
    exact add_mem (sub_mem (one_mem _) hE) (mul_mem hE hd)
  have hX' : toEAf D (x' : AE D) ∈ OO := by
    rw [b2]
    exact add_mem (sub_mem (one_mem _) hE) (mul_mem hE hd')
  have hm : toEAf D (x : AE D) * toEAf D ((x⁻¹ : (AE D)ˣ) : AE D) = 1 := by
    rw [← RingHom.map_mul, Units.mul_inv, RingHom.map_one]
  have hinv : infPart D ((x⁻¹ : (AE D)ˣ) : AE D) = 1 := by
    have := congrArg (infPart D) (Units.mul_inv x)
    rwa [RingHom.map_mul, a1, one_mul, RingHom.map_one] at this
  have hinv' : ((x' * x⁻¹ : (AE D)ˣ) : AE D) = (x' : AE D) * ((x⁻¹ : (AE D)ˣ) : AE D) := rfl
  have hinv2 : (((x' * x⁻¹)⁻¹ : (AE D)ˣ) : AE D) = (x : AE D) * ((x'⁻¹ : (AE D)ˣ) : AE D) := by
    rw [_root_.mul_inv_rev, inv_inv]
    rfl
  have hr : Formalism.L2.Pj.FinUnit (x' * x⁻¹) := by
    refine ⟨?_, GlobalTheory.PlaceDatum.finPart_mem_of_toEAf ?_, GlobalTheory.PlaceDatum.finPart_mem_of_toEAf ?_⟩
    · rw [hinv', RingHom.map_mul, b1, hinv, one_mul]
    · rw [hinv', RingHom.map_mul]
      exact mul_mem hX' a3
    · rw [hinv2, RingHom.map_mul]
      exact mul_mem hX b3
  obtain ⟨w, -, hw⟩ := toEAf_surj (toEAf D e * ((c : EAf D) * (z : EAf D)) * toEAf D ((x⁻¹ : (AE D)ˣ) : AE D))
  have hwI : toEAf D w ∈ OO := by
    rw [hw]
    exact mul_mem (mul_mem hE (mul_mem (natCast_mem _ _) z.2)) a3
  have key : finPart D ((x' * x⁻¹ : (AE D)ˣ) : AE D) - 1 = n • finPart D w := by
    have e1 : finPart D (((x' * x⁻¹ : (AE D)ˣ) : AE D) - 1) = finPart D (n • w) :=
      finPart_eq_of_toEAf (by
        rw [RingHom.map_sub, RingHom.map_one, hinv', RingHom.map_mul, hom_nsmul, hw, nsmul_eq_mul]
        exact ring_id a2 b2 hzv hm)
    rw [RingHom.map_sub, RingHom.map_one, hom_nsmul] at e1
    exact e1
  have h1 := hl _ hr ⟨_, GlobalTheory.PlaceDatum.finPart_mem_of_toEAf hwI, key⟩
  rw [map_mul, map_inv] at h1
  exact (mul_inv_eq_one.1 h1).symm

end

set_option maxHeartbeats 2000000 in

theorem unitChar_eq_of_natCong : ∀ (D : D7) (ν : (AE D)ˣ →* Circle) (e : AE D) (Sf : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e Sf → ∀ N : ℕ, 0 < N → (∀ w ∈ Sf, ((N : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal) → (∀ u : (AE D)ˣ, infPart D (u : AE D) = 1 → (∃ w ∈ Formalism.L2.Herm.intAf D.host.F D.host.E, toEAf D (u : AE D) = 1 + (N : Lev.EAf D) * w) → (∃ w ∈ Formalism.L2.Herm.intAf D.host.F D.host.E, toEAf D ((u⁻¹ : (AE D)ˣ) : AE D) = 1 + (N : Lev.EAf D) * w) → ν u = 1) → ∀ {k : ℕ} (P Q : Matrix (Fin k) (Fin k) (Lev.EAf D)), IsIntM (D := D) P → (∀ a b, ∃ w ∈ Formalism.L2.Herm.intAf D.host.F D.host.E, Q a b - P a b = (N : Lev.EAf D) * w) → GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.unitChar ν e Q = GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.unitChar ν e P := by
  intro D ν e Sf he N _ hSf hν k P Q hP hQ
  choose Z hZ hZe using hQ
  have hZint : IsIntM (D := D) (fun a b => Z a b : Matrix (Fin k) (Fin k) (Lev.EAf D)) := fun a b => hZ a b
  have h : ∀ i j, Q i j = P i j + (N : Lev.EAf D) * Z i j := fun i j => eq_add_of_sub_eq' (hZe i j)
  have hQint : IsIntM (D := D) Q := fun i j => by
    rw [h]
    exact add_mem (hP i j) (mul_mem (natCast_mem _ _) (hZ i j))
  have hZn : IsIntM (D := D) (-(fun a b => Z a b : Matrix (Fin k) (Fin k) (Lev.EAf D))) := fun a b => neg_mem (hZ a b)
  have h' : ∀ i j, P i j = Q i j + (N : Lev.EAf D) * (-(fun a b => Z a b : Matrix (Fin k) (Fin k) (Lev.EAf D))) i j :=
    fun i j => by
      change P i j = Q i j + (N : Lev.EAf D) * (-(Z i j))
      rw [h, mul_neg, add_neg_cancel_right]
  have hl : ∀ x, Formalism.L2.Pj.FinUnit x → (∃ y ∈ intAE D, finPart D (x : AE D) - 1 = N • y) → ν x = 1 := by
    rintro x ⟨h1, -, h3⟩ ⟨y, hy, hxy⟩
    obtain ⟨a, -, ha⟩ := GlobalTheory.UnitCharCong.toEAf_surj (D := D) (Algebra.TensorProduct.comm D.host.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.host.E y)
    have hfa : finPart D a = y := (Algebra.TensorProduct.comm D.host.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.host.E).injective ha
    have haI : toEAf D a ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := GlobalTheory.IdemRes.toEAf_mem_of_finPart (hfa ▸ hy)
    have hvI : toEAf D ((x⁻¹ : (AE D)ˣ) : AE D) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := GlobalTheory.IdemRes.toEAf_mem_of_finPart h3
    have hu : toEAf D (x : AE D) = 1 + (N : Lev.EAf D) * toEAf D a := by
      have := congrArg (Algebra.TensorProduct.comm D.host.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.host.E) hxy
      rw [map_sub, map_one, map_nsmul, nsmul_eq_mul, ← ha] at this
      change toEAf D (x : AE D) - 1 = (N : Lev.EAf D) * toEAf D a at this
      linear_combination this
    have hm : toEAf D (x : AE D) * toEAf D ((x⁻¹ : (AE D)ˣ) : AE D) = 1 := by
      rw [← RingHom.map_mul, Units.mul_inv, RingHom.map_one]
    refine hν x h1 ⟨_, haI, hu⟩ ⟨-(toEAf D ((x⁻¹ : (AE D)ˣ) : AE D) * toEAf D a), neg_mem (mul_mem hvI haI), ?_⟩
    linear_combination hm - toEAf D ((x⁻¹ : (AE D)ˣ) : AE D) * hu
  have f := fun hx => GlobalTheory.UnitCharCong.exists_isUnitDet he (c := N) hSf hP hZint h hx
  have g := fun hx => GlobalTheory.UnitCharCong.exists_isUnitDet he (c := N) hSf hQint hZn h' hx
  have h1 : ∀ i j, Q i j = P i j + ((N * 1 : ℕ) : Lev.EAf D) * (fun a b => Z a b : Matrix (Fin k) (Fin k) (Lev.EAf D)) i j :=
    fun i j => by rw [Nat.mul_one]; exact h i j
  unfold GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.unitChar
  by_cases hx : ∃ x, GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.IsUnitDet e P x
  · rw [dif_pos (f hx), dif_pos hx, GlobalTheory.UnitCharCong.nu_eq he (n := N) (c := 1) hl hP hZint h1 hx.choose_spec (f hx).choose_spec]
  · rw [dif_neg (fun h => hx (g h)), dif_neg hx]

end GlobalTheory.UnitCharCong

end
