import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatSurjectiveGeomFibre
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsogenyCompIffAndDegreeMulStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsogenyFlatFinrank
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyFiniteHomKernelKilledByNat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyIntCastSmulIsogenyDegree
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowEqOneOfPoints
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar.DegPrime

theorem pow_comp_mon {S : Scheme.{0}} {G H Z : Over S} [GrpObj G] [GrpObj H] (φ : G ⟶ H) [IsMonHom φ]
    (x : Z ⟶ G) (n : ℕ) : (x ^ n) ≫ φ = (x ≫ φ) ^ n := by
  induction n with
  | zero => simp [pow_zero, MonObj.one_comp]
  | succ n ih => rw [pow_succ, pow_succ, MonObj.mul_comp, ih]

theorem pow_prime_pow {K : Type} [Field K] (l : ℕ) {A B : AbVar K} (f : A ⟶ B)
    (hf : ∀ x : A.Pt, x ^ l = 1 → x ≫ f.hom = 1 → x = 1) :
    ∀ (b : ℕ) (x : A.Pt), x ^ (l ^ b) = 1 → x ≫ f.hom = 1 → x = 1 := by
  intro b
  induction b with
  | zero => intro x hx _; simpa using hx
  | succ b ih =>
    intro x hx hxf
    apply ih x _ hxf
    apply hf (x ^ (l ^ b))
    · rw [← pow_mul, ← pow_succ]; exact hx
    · rw [pow_comp_mon, hxf, one_pow]

end GlobalTheory.AV.AbVar.DegPrime

theorem GlobalTheory.AV.AbVar.not_dvd_deg_of_no_torsion_in_kernel : ∀ (K : Type) [Field K] (l : ℕ) [Fact l.Prime], (l : K) ≠ 0 →
    ∀ (A B : AbVar K) (h : A ⟶ B), IsIsogeny h → (∀ x : A.Pt, x ^ l = 1 → x ≫ h.hom = 1 → x = 1) →
      ¬ l ∣ deg h := by
  intro K _ l hl hlK A B h hh hker
  have hp : l.Prime := hl.out
  obtain ⟨hdim, -, -, -⟩ := GlobalTheory.AV.AbVar.isogeny_flat_finrank K A B h hh
  obtain ⟨N, hN, hkill⟩ := GlobalTheory.AV.KerKill.kernel_killed K A B h hh.1
  obtain ⟨b, m, hlm, hNm⟩ := Nat.exists_eq_pow_mul_and_not_dvd hN.ne' l hp.ne_one
  have hm : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · rw [h0, mul_zero] at hNm; omega
    · exact h0
  have hlb : ((l ^ b : ℕ) : K) ≠ 0 := by rw [Nat.cast_pow]; exact pow_ne_zero _ hlK
  have hpts := GlobalTheory.AV.TorsKer.pow_eq_one_of_points K A B h (l ^ b) 1 hlb
    (fun x hx hxf => by rw [pow_one]; exact GlobalTheory.AV.AbVar.DegPrime.pow_prime_pow l h hker b x hx hxf)
  have hkm : ∀ (T : Over (Sp K)) (x : T ⟶ A.X), x ≫ h.hom = 1 → x ^ m = 1 := by
    intro T x hx
    have h1 : (x ^ m) ^ (l ^ b) = 1 := by
      rw [← pow_mul, mul_comm, ← hNm]; exact hkill T x hx
    have h2 : (x ^ m) ≫ h.hom = 1 := by
      rw [GlobalTheory.AV.AbVar.DegPrime.pow_comp_mon, hx, one_pow]
    simpa using hpts T (x ^ m) h1 h2
  have hB := B.smooth
  have hA := A.smooth
  rw [hdim] at hA
  obtain ⟨h', hh', hhh', -⟩ := GlobalTheory.IsogenyQuasiInverse.exists_quasiInverse K A.X B.X B.dim A.ab B.ab hA hB
    h.hom inferInstance m hm hkm
  let g : B ⟶ A := Hom.mk (A := B) (B := A) h' (h := hh')
  have e1 : h ≫ g = ((m : ℤ)) • 𝟙 A := hom_ext (by simp [g, hhh'])
  obtain ⟨-, hdeg⟩ := GlobalTheory.T.isIsogeny_comp_iff_and_degree_mul K A B A h g hdim hdim.symm
  obtain ⟨-, hdm⟩ := GlobalTheory.MulIsogeny.mul_isogeny K A (m : ℤ) (by exact_mod_cast hm.ne')
  rw [e1, hdm, Int.natAbs_natCast] at hdeg
  intro hdvd
  have : l ∣ m ^ (2 * A.dim) := by rw [hdeg]; exact Dvd.dvd.mul_right hdvd _
  exact hlm (hp.dvd_of_dvd_pow this)
