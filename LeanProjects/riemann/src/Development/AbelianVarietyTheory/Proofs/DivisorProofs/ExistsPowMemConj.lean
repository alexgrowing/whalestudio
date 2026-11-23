import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NatDegreeMinpolyLeBaseChange

noncomputable section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount Polynomial
open scoped TensorProduct Classical

namespace GlobalTheory.StabFin

variable {p : ℕ} [Fact p.Prime] {G : HTGroup p}

abbrev FM (P : Pair G) : Type := AdjoinRoot P.pol

def jM (P : Pair G) : FM P →ₐ[G.F] G.C :=
  Ideal.Quotient.liftₐ _ (aeval (P.γ : G.C)) fun f hf => by
    obtain ⟨g, rfl⟩ := Ideal.mem_span_singleton.1 hf
    rw [map_mul, Pair.pol, minpoly.aeval, zero_mul]

theorem jM_mk (P : Pair G) (f : G.F[X]) : jM P (AdjoinRoot.mk P.pol f) = aeval (P.γ : G.C) f := rfl

theorem jM_root (P : Pair G) : jM P (AdjoinRoot.root P.pol) = P.γ := by
  rw [← AdjoinRoot.mk_X, jM_mk, aeval_X]

theorem jM_injective (P : Pair G) : Function.Injective (jM P) := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  obtain ⟨f, rfl⟩ := AdjoinRoot.mk_surjective a
  rw [jM_mk] at ha
  exact AdjoinRoot.mk_eq_zero.2 (minpoly.dvd G.F _ ha)

theorem jM_algQ (P : Pair G) (q : ℚ) : jM P (algebraMap ℚ (FM P) q) = algebraMap ℚ G.C q := by
  rw [IsScalarTower.algebraMap_apply ℚ G.F (FM P), AlgHom.commutes, ← IsScalarTower.algebraMap_apply]

theorem jM_comm (P : Pair G) (a : FM P) : jM P a * P.γ = P.γ * jM P a := by
  rw [← jM_root, ← map_mul, ← map_mul, mul_comm]

theorem exists_jM (P : Pair G) (u : G.C) (hu : u * P.γ = P.γ * u) : ∃ a, jM P a = u := by
  have hc : u ∈ Subalgebra.centralizer G.F {(P.γ : G.C)} := by
    rw [Subalgebra.mem_centralizer_iff]
    rintro g rfl
    exact hu.symm
  rw [GlobalTheory.CentSep.centralizer_eq_adjoin G.F G.C G.n G.rankC _ P.reg.2 P.reg.1,
    Algebra.adjoin_singleton_eq_range_aeval] at hc
  obtain ⟨f, rfl⟩ := hc
  exact ⟨AdjoinRoot.mk _ f, rfl⟩

theorem sh_mul (x y : G.C) : sh G (x * y) = sh G y * sh G x := by
  simp [sh, map_mul]

theorem sh_one : sh G (1 : G.C) = 1 := by simp [sh]

theorem sh_add (x y : G.C) : sh G (x + y) = sh G x + sh G y := by simp [sh, map_add]

theorem sh_zero : sh G (0 : G.C) = 0 := by simp [sh]

theorem sh_sh (x : G.C) : sh G (sh G x) = x := G.star_star x

theorem sh_algF (a : G.F) : sh G (algebraMap G.F G.C a) = algebraMap G.F G.C (IsCMField.complexConj G.F a) :=
  G.star_F a

def iC (P : Pair G) (x : G.C) : G.C := (P.β : G.C) * sh G x * ((P.β⁻¹ : G.Cˣ) : G.C)

theorem iC_mul (P : Pair G) (x y : G.C) : iC P (x * y) = iC P y * iC P x := by
  simp only [iC, sh_mul, mul_assoc, Units.inv_mul_cancel_left]

theorem iC_one (P : Pair G) : iC P 1 = 1 := by simp [iC, sh_one]

theorem iC_add (P : Pair G) (x y : G.C) : iC P (x + y) = iC P x + iC P y := by
  simp [iC, sh_add, mul_add, add_mul]

theorem iC_zero (P : Pair G) : iC P 0 = 0 := by simp [iC, sh_zero]

theorem iC_algF (P : Pair G) (a : G.F) :
    iC P (algebraMap G.F G.C a) = algebraMap G.F G.C (IsCMField.complexConj G.F a) := by
  rw [iC, sh_algF, ← Algebra.commutes, mul_assoc, Units.mul_inv, mul_one]

theorem iC_algQ (P : Pair G) (q : ℚ) : iC P (algebraMap ℚ G.C q) = algebraMap ℚ G.C q := by
  rw [IsScalarTower.algebraMap_apply ℚ G.F G.C, iC_algF]
  congr 1
  simp

theorem iC_gamma_mul (P : Pair G) : iC P P.γ * P.γ = algebraMap ℚ G.C P.c := by
  have h := P.sim
  have h2 : (P.β : G.C) * sh G P.γ = ((P.γ⁻¹ : G.Cˣ) : G.C) * (algebraMap ℚ G.C P.c * P.β) := by
    rw [← h]; simp only [← mul_assoc, Units.inv_mul, one_mul]
  calc iC P P.γ * P.γ = ((P.β : G.C) * sh G P.γ) * ((P.β⁻¹ : G.Cˣ) : G.C) * P.γ := rfl
    _ = ((P.γ⁻¹ : G.Cˣ) : G.C) * algebraMap ℚ G.C P.c * P.γ := by
        rw [h2]; simp only [mul_assoc, Units.mul_inv, mul_one]
    _ = _ := by rw [mul_assoc, Algebra.commutes, ← mul_assoc, Units.inv_mul, one_mul]

theorem iC_comm (P : Pair G) (u : G.C) (hu : u * P.γ = P.γ * u) : iC P u * P.γ = P.γ * iC P u := by
  have h1 : iC P u * iC P P.γ = iC P P.γ * iC P u := by rw [← iC_mul, ← iC_mul, hu]
  have hg : iC P P.γ = algebraMap ℚ G.C P.c * ((P.γ⁻¹ : G.Cˣ) : G.C) := by
    rw [← iC_gamma_mul, mul_assoc, Units.mul_inv, mul_one]
  rw [hg, ← mul_assoc, ← Algebra.commutes, mul_assoc, mul_assoc] at h1
  have hc : IsUnit (algebraMap ℚ G.C P.c) := (P.c.isUnit).map _
  have h2 := hc.mul_left_cancel h1
  calc iC P u * P.γ = P.γ * (((P.γ⁻¹ : G.Cˣ) : G.C) * iC P u) * P.γ := by
        rw [← mul_assoc, Units.mul_inv, one_mul]
    _ = P.γ * (iC P u * ((P.γ⁻¹ : G.Cˣ) : G.C)) * P.γ := by rw [h2]
    _ = _ := by rw [mul_assoc, mul_assoc, Units.inv_mul, mul_one]

theorem iC_iC (P : Pair G) (x : G.C) : iC P (iC P x) = x := by
  have hb : sh G (P.β : G.C) = P.β := P.sym
  have hbi : sh G ((P.β⁻¹ : G.Cˣ) : G.C) = ((P.β⁻¹ : G.Cˣ) : G.C) := by
    have e : sh G ((P.β⁻¹ : G.Cˣ) : G.C) * P.β = 1 := by
      rw [← hb, ← sh_mul, Units.mul_inv, sh_one]
    calc sh G ((P.β⁻¹ : G.Cˣ) : G.C) = sh G ((P.β⁻¹ : G.Cˣ) : G.C) * P.β * ((P.β⁻¹ : G.Cˣ) : G.C) := by
          rw [mul_assoc, Units.mul_inv, mul_one]
      _ = _ := by rw [e, one_mul]
  simp only [iC, sh_mul, hb, hbi, sh_sh, mul_assoc, Units.mul_inv, mul_one, Units.mul_inv_cancel_left]

def iMf (P : Pair G) (a : FM P) : FM P := (exists_jM P (iC P (jM P a)) (iC_comm P _ (jM_comm P a))).choose

theorem jM_iMf (P : Pair G) (a : FM P) : jM P (iMf P a) = iC P (jM P a) :=
  (exists_jM P (iC P (jM P a)) (iC_comm P _ (jM_comm P a))).choose_spec

def iM (P : Pair G) : FM P →ₐ[ℚ] FM P where
  toFun := iMf P
  map_one' := jM_injective P (by rw [jM_iMf, map_one, iC_one])
  map_mul' a b := jM_injective P (by
    rw [mul_comm (iMf P a), jM_iMf, map_mul, map_mul, jM_iMf, jM_iMf, iC_mul])
  map_zero' := jM_injective P (by rw [jM_iMf, map_zero, iC_zero])
  map_add' a b := jM_injective P (by rw [jM_iMf, map_add, map_add, jM_iMf, jM_iMf, iC_add])
  commutes' q := jM_injective P (by rw [jM_iMf, jM_algQ, iC_algQ])

theorem jM_iM (P : Pair G) (a : FM P) : jM P (iM P a) = iC P (jM P a) := jM_iMf P a

theorem iM_algF (P : Pair G) (a : G.F) :
    iM P (algebraMap G.F (FM P) a) = algebraMap G.F (FM P) (IsCMField.complexConj G.F a) :=
  jM_injective P (by rw [jM_iM, AlgHom.commutes, AlgHom.commutes, iC_algF])

theorem iM_root_mul (P : Pair G) :
    iM P (AdjoinRoot.root P.pol) * AdjoinRoot.root P.pol = algebraMap ℚ (FM P) P.c :=
  jM_injective P (by rw [map_mul, jM_iM, jM_root, jM_algQ, iC_gamma_mul])

theorem iM_iM (P : Pair G) (a : FM P) : iM P (iM P a) = a :=
  jM_injective P (by rw [jM_iM, jM_iM, iC_iC])

theorem mul_iM_of_cent (P : Pair G) (w : P.cent) (a : FM P) (ha : jM P a = ((w : G.Cˣ × ℚˣ).1 : G.C)) :
    a * iM P a = algebraMap ℚ (FM P) ((w : G.Cˣ × ℚˣ).2 : ℚ) :=
  jM_injective P (by
    rw [map_mul, jM_iM, jM_algQ, ha, iC, ← mul_assoc, ← mul_assoc, w.2.2, mul_assoc, Units.mul_inv, mul_one])

theorem exists_pow_mem_conj {H : Type} [Group H] (K K₀ : Subgroup H) (g y : H) (hK : K.Commensurable K₀)
    (hy : y ∈ K.map (MulAut.conj g).toMonoidHom) :
    ∃ m : ℕ, 0 < m ∧ y ^ m ∈ K₀.map (MulAut.conj g).toMonoidHom := by
  obtain ⟨k, hk, rfl⟩ := hy
  obtain ⟨m, hm0, -, hm⟩ := Subgroup.exists_pow_mem_of_index_ne_zero hK.2 (⟨k, hk⟩ : K)
  refine ⟨m, hm0, k ^ m, ?_, by simp [map_pow]⟩
  simpa [Subgroup.mem_subgroupOf] using hm

instance numberField (P : Pair G) [Fact (Irreducible P.pol)] : NumberField (FM P) := by
  haveI : CharZero (FM P) := charZero_of_injective_algebraMap (algebraMap G.F (FM P)).injective
  haveI : Module.Finite G.F (FM P) :=
    (AdjoinRoot.powerBasis (minpoly.ne_zero (IsIntegral.of_finite G.F (P.γ : G.C)))).finite
  haveI : Module.Finite ℚ (FM P) := Module.Finite.trans G.F (FM P)
  exact ⟨⟩

end GlobalTheory.StabFin
