import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
import Formalism.LocalToGlobal.Divisibility.DefGroupLemmas
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOrEqOfPlaceIdem
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchrodingerIntertwinerSchwartzBruhatIsTheta
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEqMulOfResSNeOne
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ContinuousCharacterFiniteOrderIntegralUnits

namespace StandardFirstTheta
section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped Pointwise TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Grid GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle GlobalTheory.ConstRatio

namespace GlobalTheory.CompanionTheory.StdFstTheta

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

end GlobalTheory.CompanionTheory.StdFstTheta

end

end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped Pointwise TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Grid GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle GlobalTheory.ConstRatio

namespace GlobalTheory.CompanionTheory.StdFstTheta

variable {D : D7}

local notation "OO" => Formalism.L2.Herm.intAf D.host.F D.host.E

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

theorem unitChar_congr {ν : (AE D)ˣ →* Circle} {e : AE D} {S : Finset (Pl D.host.E)} (he : IsIdemSum e S) {n c : ℕ}
    (hl : ∀ x, Formalism.L2.Pj.FinUnit x → (∃ y ∈ intAE D, finPart D (x : AE D) - 1 = n • y) → ν x = 1)
    (hc : ∀ P ∈ S, ((c : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal) {k : ℕ} {N N' Z : Matrix (Fin k) (Fin k) (EAf D)}
    (hN : IsIntM N) (hZ : IsIntM Z) (h : ∀ i j, N' i j = N i j + ((n * c : ℕ) : EAf D) * Z i j) :
    unitChar ν e N = unitChar ν e N' := by
  have hC : ∀ P ∈ S, ((n * c : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal := fun P hP => by
    rw [Nat.cast_mul]
    exact Ideal.mul_mem_left _ _ (hc P hP)
  have hN' : IsIntM N' := fun i j => by
    rw [h]
    exact add_mem (hN i j) (mul_mem (natCast_mem _ _) (hZ i j))
  have hZ' : IsIntM (-Z) := fun i j => neg_mem (hZ i j)
  have h' : ∀ i j, N i j = N' i j + ((n * c : ℕ) : EAf D) * (-Z) i j := fun i j => by
    rw [h, Matrix.neg_apply, mul_neg, add_neg_cancel_right]
  have f := fun hx => exists_isUnitDet he hC hN hZ h hx
  have g := fun hx => exists_isUnitDet he hC hN' hZ' h' hx
  unfold unitChar
  by_cases hx : ∃ x, IsUnitDet e N x
  · rw [dif_pos hx, dif_pos (f hx), nu_eq he hl hN hZ h hx.choose_spec (f hx).choose_spec]
  · rw [dif_neg hx, dif_neg fun h => hx (g h)]

theorem isIntM_topL {b a k : ℕ} {Y : Matrix (Fin b) (Fin a) (EAf D)} (h : IsIntM Y) : IsIntM (topL k Y) := fun i j => by
  unfold topL
  split_ifs
  · exact h _ _
  · exact zero_mem _

theorem topL_shift {b a k : ℕ} {Y Y' W : Matrix (Fin b) (Fin a) (EAf D)} {c : EAf D}
    (h : ∀ i j, Y' i j = Y i j + c * W i j) (i j : Fin k) : topL k Y' i j = topL k Y i j + c * topL k W i j := by
  unfold topL
  split_ifs
  · exact h _ _
  · rw [mul_zero, add_zero]

theorem inId_shift {I : Ideal (𝓞 D.host.E)} {n : ℕ} (hn : ((n : ℕ) : 𝓞 D.host.E) ∈ I) {z z' w : EAf D} (hw : w ∈ OO)
    (h : z' = z + n * w) (hz : InId I z) : InId I z' := by
  obtain ⟨h1, h2⟩ := hz
  have h3 : z' ∈ OO := by
    rw [h]
    exact add_mem h1 (mul_mem (natCast_mem _ _) hw)
  refine ⟨h3, ?_⟩
  have e : (⟨z', h3⟩ : OO) = ⟨z, h1⟩ + oToS D.host.F D.host.E (n : 𝓞 D.host.E) * ⟨w, hw⟩ := Subtype.ext (by
    rw [hom_natCast]
    change z' = z + (((n : OO)) : EAf D) * w
    rw [coe_nat]
    exact h)
  rw [e]
  exact add_mem h2 (Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hn))

end GlobalTheory.CompanionTheory.StdFstTheta

end

end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped Pointwise TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Grid GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle GlobalTheory.ConstRatio

namespace GlobalTheory.CompanionTheory.StdFstTheta

variable {D : D7}

local notation "OO" => Formalism.L2.Herm.intAf D.host.F D.host.E

set_option maxHeartbeats 1000000 in

theorem stdFst_shift {ν : (AE D)ˣ →* Circle} {e : AE D} {S : Finset (Pl D.host.E)} (he : IsIdemSum e S)
    {I : Ideal (𝓞 D.host.E)} {n₀ n c : ℕ} (hn₀ : ((n₀ : ℕ) : 𝓞 D.host.E) ∈ I)
    (hl : ∀ x, Formalism.L2.Pj.FinUnit x → (∃ y ∈ intAE D, finPart D (x : AE D) - 1 = n • y) → ν x = 1)
    (hc : ∀ P ∈ S, ((c : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal) (A WW : HSp D) (βA : GL (Fin A.rank) (EAf D))
    (βW : GL (Fin WW.rank) (EAf D)) {t t' : WO A WW} (hh : IsHalf e t' ↔ IsHalf e t)
    {W : Matrix (Fin WW.rank) (Fin A.rank) (EAf D)} (hW : IsIntM W)
    (h : ∀ i j, frMapO A WW βA βW t' i j = frMapO A WW βA βW t i j + ((n₀ * (n * c) : ℕ) : EAf D) * W i j) :
    stdFst ν e I A WW βA βW t' = stdFst ν e I A WW βA βW t := by
  have hW1 : ∀ i j, ((n * c : ℕ) : EAf D) * W i j ∈ OO := fun i j => mul_mem (natCast_mem _ _) (hW i j)
  have hW2 : ∀ i j, (n₀ : EAf D) * (((n * c : ℕ) : EAf D) * W i j) ∈ OO := fun i j => mul_mem (natCast_mem _ _) (hW1 i j)
  have ha : ∀ i j, frMapO A WW βA βW t' i j =
      frMapO A WW βA βW t i j + (n₀ : EAf D) * (((n * c : ℕ) : EAf D) * W i j) := fun i j => by
    rw [h, Nat.cast_mul n₀, mul_assoc]
  have hb : ∀ i j, frMapO A WW βA βW t i j =
      frMapO A WW βA βW t' i j + (n₀ : EAf D) * (-(((n * c : ℕ) : EAf D) * W i j)) := fun i j => by
    rw [ha, mul_neg, add_neg_cancel_right]
  have hint : IsIntM (frMapO A WW βA βW t') ↔ IsIntM (frMapO A WW βA βW t) :=
    forall_congr' fun i => forall_congr' fun j => by
      rw [ha]
      exact add_mem_cancel_right (hW2 i j)
  have hid : (∀ i j, A.rank ≤ i.1 → InId I (frMapO A WW βA βW t' i j)) ↔
      ∀ i j, A.rank ≤ i.1 → InId I (frMapO A WW βA βW t i j) :=
    ⟨fun H i j hi => inId_shift hn₀ (neg_mem (hW1 i j)) (hb i j) (H i j hi),
      fun H i j hi => inId_shift hn₀ (hW1 i j) (ha i j) (H i j hi)⟩
  unfold stdFst
  by_cases hcnd : IsHalf e t ∧ IsIntM (frMapO A WW βA βW t) ∧ ∀ i j, A.rank ≤ i.1 → InId I (frMapO A WW βA βW t i j)
  · rw [if_pos hcnd, if_pos ⟨hh.2 hcnd.1, hint.2 hcnd.2.1, hid.2 hcnd.2.2⟩]
    refine (unitChar_congr he hl hc (isIntM_topL hcnd.2.1)
      (Z := topL A.rank fun i j => (n₀ : EAf D) * W i j) (isIntM_topL fun i j => mul_mem (natCast_mem _ _) (hW i j))
      (topL_shift (c := ((n * c : ℕ) : EAf D)) fun i j => ?_)).symm
    rw [h, Nat.cast_mul n₀]
    ring
  · rw [if_neg hcnd, if_neg fun h' => hcnd ⟨hh.1 h'.1, hint.1 h'.2.1, hid.1 h'.2.2⟩]

set_option maxHeartbeats 1000000 in

theorem stdFst_isSB {ν : (AE D)ˣ →* Circle} (hν : Continuous ν) {e : AE D} {S : Finset (Pl D.host.E)} (he : IsIdemSum e S)
    {I : Ideal (𝓞 D.host.E)} (hI : I ≠ ⊥) (A WW : HSp D) (βA : GL (Fin A.rank) (EAf D)) (βW : GL (Fin WW.rank) (EAf D))
    (Λ : AddSubgroup (WO A WW))
    (hB : ∃ M : ℕ, 0 < M ∧ ∀ u ∈ Λ, ∀ i j, (M : EAf D) * frMapO A WW βA βW u i j ∈ OO)
    (hC : ∃ K : ℕ, 0 < K ∧ ∀ t : WO A WW, IsHalf e t → IsIntM (frMapO A WW βA βW t) → K • t ∈ Λ) :
    IsSBHalf e Λ (stdFst ν e I A WW βA βW) := by
  obtain ⟨M, hM, hB⟩ := hB
  obtain ⟨K, hK, hC⟩ := hC
  obtain ⟨n, hn, hl, -⟩ := GlobalTheory.CharFin.char_finUnit_finite_order D ν hν
  obtain ⟨n₀, hn₀, hnI⟩ : ∃ n₀ : ℕ, 0 < n₀ ∧ ((n₀ : ℕ) : 𝓞 D.host.E) ∈ I :=
    ⟨_, Nat.pos_of_ne_zero fun h => hI (Ideal.absNorm_eq_zero_iff.1 h), Ideal.absNorm_mem I⟩
  obtain ⟨c, hc, hcS⟩ : ∃ c : ℕ, 0 < c ∧ ∀ P ∈ S, ((c : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal := by
    refine ⟨∏ P ∈ S, Ideal.absNorm P.asIdeal, Finset.prod_pos fun P _ =>
      Nat.pos_of_ne_zero fun h => P.ne_bot (Ideal.absNorm_eq_zero_iff.1 h), fun P hP => ?_⟩
    obtain ⟨m, hm⟩ := Finset.dvd_prod_of_mem (fun P : Pl D.host.E => Ideal.absNorm P.asIdeal) hP
    rw [hm, Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ (Ideal.absNorm_mem P.asIdeal)
  refine ⟨fun t ht => ?_, K * ((n₀ * (n * c)) * M), Nat.mul_pos hK (Nat.mul_pos (Nat.mul_pos hn₀ (Nat.mul_pos hn hc)) hM),
    fun u hu hh t => ?_, fun t ht => ?_⟩
  · unfold stdFst at ht
    by_contra h
    exact ht (if_neg fun h' => h h'.1)
  · refine stdFst_shift he hnI hl hcS A WW βA βW (W := fun i j => (K : EAf D) * ((M : EAf D) * frMapO A WW βA βW u i j))
      ?_ (fun i j => mul_mem (natCast_mem _ _) (hB u hu i j)) fun i j => ?_
    · rw [GlobalTheory.PlaceModel.isHalf_iff A WW, GlobalTheory.PlaceModel.isHalf_iff A WW]
      exact AddSubgroup.add_mem_cancel_right _ (nsmul_mem ((GlobalTheory.PlaceModel.isHalf_iff A WW).1 hh) _)
    · rw [GlobalTheory.PlaceDatum.frMapO_add]
      push_cast
      ring
  · have h : IsHalf e t ∧ IsIntM (frMapO A WW βA βW t) := by
      unfold stdFst at ht
      by_contra h
      exact ht (if_neg fun h' => h ⟨h'.1, h'.2.1⟩)
    rw [mul_nsmul]
    exact nsmul_mem (hC t h.1 h.2) _

theorem exists_theta : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (A WW : HSp D) (rA : Rig A) (rW : Rig WW) (ν : (AE D)ˣ →* Circle) (e : AE D) (S : Finset (Pl D.host.E)) (I : Ideal (𝓞 D.host.E)) (vac : WO A WW → ℂ), rA.Is → rW.Is → IsHeckeChar D ν → IsIdemSum e S → I ≠ ⊥ → IsVacO ψ θ (neg A) WW (fun τ => -rA.s τ) rW.s rA.Λ rW.Λ vac → ∃ f, IsThetaAt ψ (symplO (neg A) WW) (heisO ψ (neg A) WW) e (latO (neg A) WW rA.Λ rW.Λ fun _ => True) 1 vac (stdFst ν e I A WW rA.β rW.β) f ∧ IsThetaFunO ψ (neg A) WW f := by
  intro D ψ θ A WW rA rW ν e S I vac hA hW hν he hI hv
  have hinf := GlobalTheory.PlaceDatum.infPart_idemSum he
  have hee := GlobalTheory.PlaceDatum.idemSum_mul_self he
  have hSd : IsSelfDualC (neg A) rA.Λ := by
    refine ⟨hA.1.1, fun y => (hA.1.2 y).trans (forall₂_congr fun x _ => ⟨fun ⟨c, hc⟩ => ⟨-c, ?_⟩, fun ⟨c, hc⟩ => ⟨-c, ?_⟩⟩)⟩
    · simp [neg_gram, hc]
    · simp [neg_gram] at hc ⊢
      exact neg_eq_iff_eq_neg.2 hc
  obtain ⟨K, hK, hC⟩ := GlobalTheory.PlaceDatum.exists_nsmul_of_frMapO (S := neg A) hSd.1 hW.1.1 rA.β rW.β
  have hSB : IsSBHalf e (latO (neg A) WW rA.Λ rW.Λ fun _ => True) (stdFst ν e I A WW rA.β rW.β) :=
    stdFst_isSB hν.1 he hI A WW rA.β rW.β (latO (neg A) WW rA.Λ rW.Λ fun _ => True)
      (GlobalTheory.PlaceDatum.exists_den_frMapO (S := neg A) hSd.1.fg hW.1.1.fg rA.β rW.β)
      ⟨K, hK, fun t ht => hC t (GlobalTheory.PlaceDatum.infPart_of_half hinf ht)⟩
  obtain ⟨Tm, hTm⟩ := (GlobalTheory.PlaceModelSum.placeModelExistsSum D ψ hv.1 (neg A) WW rA.Λ rW.Λ hSd hW.1 _ e he vac hv.2.theta hv.2.lat).1
  obtain ⟨f, h⟩ := GlobalTheory.PlaceDatum.exists_isThetaAt hv.1 hSd hW.1 hee hinf ⟨Tm, hTm⟩ hSB
  refine ⟨f, h, ?_⟩
  rw [h.2 Tm hTm]
  exact GlobalTheory.SchrTheta.isTheta_placeModel D ψ hv.1 (neg A) WW rA.Λ rW.Λ hSd hW.1 e hee hinf vac hv.2.theta Tm hTm _ hSB

end GlobalTheory.CompanionTheory.StdFstTheta

end

end

end StandardFirstTheta
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped Pointwise TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Grid GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle GlobalTheory.ConstRatio
theorem _root_.GlobalTheory.Adopt.first_standard_pair_member_has_theta_function : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (A WW : HSp D) (rA : Rig A) (rW : Rig WW) (ν : (AE D)ˣ →* Circle) (e : AE D) (S : Finset (Pl D.host.E)) (I : Ideal (𝓞 D.host.E)) (vac : WO A WW → ℂ), rA.Is → rW.Is → IsHeckeChar D ν → IsIdemSum e S → I ≠ ⊥ → IsVacO ψ θ (neg A) WW (fun τ => -rA.s τ) rW.s rA.Λ rW.Λ vac → ∃ f, IsThetaAt ψ (symplO (neg A) WW) (heisO ψ (neg A) WW) e (latO (neg A) WW rA.Λ rW.Λ fun _ => True) 1 vac (stdFst ν e I A WW rA.β rW.β) f ∧ IsThetaFunO ψ (neg A) WW f := by
  first | exact @StandardFirstTheta.GlobalTheory.CompanionTheory.StdFstTheta.exists_theta | exact StandardFirstTheta.GlobalTheory.CompanionTheory.StdFstTheta.exists_theta | (intros; apply StandardFirstTheta.GlobalTheory.CompanionTheory.StdFstTheta.exists_theta <;> assumption)

end
