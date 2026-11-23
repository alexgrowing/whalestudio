import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ZsmulGeneratorEqZeroOfProjection

open NumberField IntermediateField Ideal
open scoped Pointwise

noncomputable section

namespace Formalism.HC

open Formalism.FrobeniusOrbits

structure HostRaw (φ : Frame) where
  q : ℕ
  d : ℕ

  QS : ℕ
  hyp : HostHyp q d
  two_le_e : 2 ≤ φ.e
  QS_pos : 0 < QS
  tower_dvd : 2 ^ (φ.e + 2) ∣ QS
  QS_coprime : Nat.Coprime QS (q * d)
  QS_split : ∀ l : ℕ, l.Prime → l ≠ 2 → l ∣ QS → jacobiSym (-(d : ℤ)) l = 1
  E : Type
  [instField : Field E]
  [instNF : NumberField E]
  galois : IsGalois ℚ E
  gal : (E ≃ₐ[ℚ] E) ≃* φ.GG

  sqd : E
  sqd_sq : sqd ^ 2 = -(d : E)
  gal_sqd : ∀ σ : E ≃ₐ[ℚ] E, σ sqd = ((((gal σ).1.2 : ℤˣ) : ℤ) : E) * sqd

  cycEmb : E →ₐ[ℚ] CyclotomicField (QS * q * d) ℚ
  cycZeta : CyclotomicField (QS * q * d) ℚ
  cycZeta_prim : IsPrimitiveRoot cycZeta (QS * q * d)

  art : (ZMod (QS * q * d))ˣ →* φ.GG
  art_spec : ∀ (u : (ZMod (QS * q * d))ˣ)
    (τ : CyclotomicField (QS * q * d) ℚ ≃ₐ[ℚ] CyclotomicField (QS * q * d) ℚ),
    τ cycZeta = cycZeta ^ (u : ZMod (QS * q * d)).val → ∀ x : E, cycEmb (gal.symm (art u) x) = τ (cycEmb x)
  art_neg_one : art (-1) = φ.cc
  art_h : ∀ (u : (ZMod (QS * q * d))ˣ) (v : (ZMod (2 ^ (φ.e + 2)))ˣ),
    (v : ZMod (2 ^ (φ.e + 2))) = (((u : ZMod (QS * q * d)).val : ℕ) : ZMod (2 ^ (φ.e + 2))) →
    φ.hH (art u).2 = hcl φ.e v
  art_d : ∀ u : (ZMod (QS * q * d))ˣ, (u : ZMod (QS * q * d)).val ≡ 1 [MOD QS * q] → art u = 1 ∨ art u = φ.iod
  art_q : ∀ u : (ZMod (QS * q * d))ˣ, (u : ZMod (QS * q * d)).val ≡ 1 [MOD QS * d] → art u ^ 2 = 1

attribute [instance] HostRaw.instField HostRaw.instNF

namespace HostRaw

variable {φ : Frame} (H : HostRaw φ)

abbrev condN : ℕ := H.QS * H.q * H.d

def small : Finset ℕ := H.QS.primeFactors

abbrev F : Subfield H.E := maximalRealSubfield H.E

def K : IntermediateField ℚ H.E := ℚ⟮H.sqd⟯

abbrev galE (σ : H.E ≃ₐ[ℚ] H.E) : φ.GG := H.gal σ

def conj : H.E ≃ₐ[ℚ] H.E := H.gal.symm φ.cc

def cmType : Set (H.E →+* ℂ) := {ψ | ψ H.sqd = Complex.I * (Real.sqrt H.d : ℂ)}

def psAt (p : ℕ) : ℤ :=
  if h : Nat.Coprime p H.condN then (((H.art (ZMod.unitOfCoprime p h)).1.1 : ℤˣ) : ℤ) else 0

def rd : ℝ := |(discr H.E : ℝ)| ^ ((1 : ℝ) / (Module.finrank ℚ H.E : ℝ))

def etaF (𝔭 : Ideal (𝓞 H.F)) : ℤ := if (primesOver 𝔭 (𝓞 H.E)).ncard = 2 then 1 else -1

def MuPM : Prop := ∀ x : H.E, (∃ m : ℕ, 0 < m ∧ x ^ m = 1) → x = 1 ∨ x = -1

def CoprimeFifteen : Prop := Nat.Coprime H.QS 15

def Exact : Prop := ∀ l : ℕ, l.Prime → l ∣ H.QS →
  ∃ u : (ZMod H.condN)ˣ, (u : ZMod H.condN).val ≡ 1 [MOD H.condN / l] ∧ H.art u ≠ 1

def PsQ : Prop := ∀ u : (ZMod H.condN)ˣ,
  (((H.art u).1.1 : ℤˣ) : ℤ) = jacobiSym (((u : ZMod H.condN).val : ℕ) : ℤ) H.q

end HostRaw

structure HostDer {φ : Frame} (H : HostRaw φ) : Prop where
  art_surj : Function.Surjective H.art
  cm : IsCMField H.E
  conj_iff : ∀ (ψ : H.E →+* ℂ) (σ : H.E ≃ₐ[ℚ] H.E), (∀ x, ψ (σ x) = starRingEnd ℂ (ψ x)) ↔ H.gal σ = φ.cc
  finrank_E : Module.finrank ℚ H.E = 4 * φ.ord
  finrank_F : Module.finrank ℚ H.F = 2 * φ.ord
  mem_F : ∀ x : H.E, x ∈ H.F ↔ H.conj x = x

  cmType : (∀ ψ : H.E →+* ℂ, ψ ∈ H.cmType ↔ (starRingEnd ℂ).comp ψ ∉ H.cmType) ∧ H.cmType.ncard = 2 * φ.ord ∧
    ∀ ψ ∈ H.cmType, ∀ σ : H.E ≃ₐ[ℚ] H.E, ψ.comp (σ : H.E →+* H.E) ∈ H.cmType ↔ H.gal σ ∈ φ.Psi

  ps_root : ∃ a : H.E, a ≠ 0 ∧ ∀ σ : H.E ≃ₐ[ℚ] H.E, σ a = ((((H.gal σ).1.1 : ℤˣ) : ℤ) : H.E) * a
  art_ch : ∀ u : (ZMod H.condN)ˣ, (((H.art u).1.2 : ℤˣ) : ℤ) = jacobiSym (((u : ZMod H.condN).val : ℕ) : ℤ) H.d

  ps_d : ∀ u : (ZMod H.condN)ˣ, (u : ZMod H.condN).val ≡ H.d [MOD H.QS * H.q] → (H.art u).1.1 = -1

  frob : ∀ (p : ℕ) [Fact p.Prime], ¬ p ∣ H.condN →
    ∀ (P : Ideal (𝓞 H.E)) [P.IsPrime] [P.LiesOver (span {(p : ℤ)})],
      (∃ σ : H.E ≃ₐ[ℚ] H.E, IsArithFrobAt ℤ σ P) ∧
      (∀ (σ : H.E ≃ₐ[ℚ] H.E) (u : (ZMod H.condN)ˣ), (u : ZMod H.condN) = (p : ZMod H.condN) →
        (IsArithFrobAt ℤ σ P ↔ H.gal σ = H.art u)) ∧
      (∀ σ : H.E ≃ₐ[ℚ] H.E, IsArithFrobAt ℤ σ P →
        (((H.gal σ).1.1 : ℤˣ) : ℤ) = H.psAt p ∧ (((H.gal σ).1.2 : ℤˣ) : ℤ) = jacobiSym (-(H.d : ℤ)) p ∧
        ∃ v : (ZMod (2 ^ (φ.e + 2)))ˣ, (v : ZMod (2 ^ (φ.e + 2))) = (p : ZMod _) ∧ φ.hH (H.gal σ).2 = hcl φ.e v) ∧
      ∀ σ : H.E ≃ₐ[ℚ] H.E, (∀ x : 𝓞 H.E, σ • x - x ∈ P) ↔ σ = 1

  frob_any : ∀ (l : ℕ) [Fact l.Prime] (P : Ideal (𝓞 H.E)) [P.IsPrime] [P.LiesOver (span {(l : ℤ)})] (σ : H.E ≃ₐ[ℚ] H.E),
    IsArithFrobAt ℤ σ P ↔
      ∃ u : (ZMod H.condN)ˣ, (u : ZMod H.condN).val ≡ l [MOD ordCompl[l] H.condN] ∧ H.gal σ = H.art u

  inertia : ∀ (l : ℕ) [Fact l.Prime] (P : Ideal (𝓞 H.E)) [P.IsPrime] [P.LiesOver (span {(l : ℤ)})] (σ : H.E ≃ₐ[ℚ] H.E),
    (∀ x : 𝓞 H.E, σ • x - x ∈ P) ↔
      ∃ u : (ZMod H.condN)ˣ, (u : ZMod H.condN).val ≡ 1 [MOD ordCompl[l] H.condN] ∧ H.gal σ = H.art u

  decomp : ∀ (l : ℕ) [Fact l.Prime] (P : Ideal (𝓞 H.E)) [P.IsPrime] [P.LiesOver (span {(l : ℤ)})] (σ : H.E ≃ₐ[ℚ] H.E),
    σ ∈ MulAction.stabilizer _ P ↔
      ∃ (u : (ZMod H.condN)ˣ) (k : ℕ), (u : ZMod H.condN).val ≡ l ^ k [MOD ordCompl[l] H.condN] ∧ H.gal σ = H.art u

  inertia_d : ∀ (P : Ideal (𝓞 H.E)) [P.IsPrime] [P.LiesOver (span {(H.d : ℤ)})] (σ : H.E ≃ₐ[ℚ] H.E),
    (∀ x : 𝓞 H.E, σ • x - x ∈ P) ↔ (H.gal σ = 1 ∨ H.gal σ = φ.iod)

  decomp_typeI : ∀ (l : ℕ), l.Prime → l ∣ H.QS * H.q →
    ∀ (P : Ideal (𝓞 H.E)) [P.IsPrime] [P.LiesOver (span {(l : ℤ)})] (σ : H.E ≃ₐ[ℚ] H.E),
      σ ∈ MulAction.stabilizer _ P → H.gal σ ∈ φ.Psi

  decompConj : ∀ (l : ℕ), l.Prime → l ∣ H.condN →
    ∀ (P : Ideal (𝓞 H.E)) [P.IsPrime] [P.LiesOver (span {(l : ℤ)})], H.conj ∉ MulAction.stabilizer _ P

  unramEF : ∀ (P : Ideal (𝓞 H.E)), P.IsPrime → P ≠ ⊥ → ¬ ∀ x : 𝓞 H.E, H.conj • x - x ∈ P

  splitK : ∀ p : ℕ, p.Prime →
    ((primesOver (span {(p : ℤ)}) (𝓞 H.K)).ncard = 2 ↔ (p = 2 ∨ (p ≠ 2 ∧ jacobiSym (-(H.d : ℤ)) p = 1)))

  ordinary : ∀ (p : ℕ) [Fact p.Prime] (P : Ideal (𝓞 H.E)) [P.IsPrime] [P.LiesOver (span {(p : ℤ)})],
    (∀ σ τ : H.E ≃ₐ[ℚ] H.E, τ ∈ MulAction.stabilizer _ P → (H.gal (σ * τ) ∈ φ.Psi ↔ H.gal σ ∈ φ.Psi)) ↔
      (primesOver (span {(p : ℤ)}) (𝓞 H.K)).ncard = 2

  eta : (∀ 𝔭 : Ideal (𝓞 H.F), 𝔭.IsPrime → 𝔭 ≠ ⊥ →
      (primesOver 𝔭 (𝓞 H.E)).ncard = 2 ∨ ((primesOver 𝔭 (𝓞 H.E)).ncard = 1 ∧ 𝔭.inertiaDegIn (𝓞 H.E) = 2)) ∧
    (∀ (p : ℕ) [Fact p.Prime], ¬ p ∣ H.condN →
      ∀ (P : Ideal (𝓞 H.E)) [P.IsPrime] [P.LiesOver (span {(p : ℤ)})] (σ : H.E ≃ₐ[ℚ] H.E), IsArithFrobAt ℤ σ P →
        (H.etaF (P.comap (algebraMap (𝓞 H.F) (𝓞 H.E))) = -1 ↔ φ.cc ∈ Subgroup.zpowers (H.gal σ))) ∧
    (∀ (p : ℕ) [Fact p.Prime], p ∣ H.condN →
      ∀ (P : Ideal (𝓞 H.E)) [P.IsPrime] [P.LiesOver (span {(p : ℤ)})],
        H.etaF (P.comap (algebraMap (𝓞 H.F) (𝓞 H.E))) = 1)

  diffSupport : ∀ P : Ideal (𝓞 H.E), P.IsPrime → P ∣ differentIdeal (𝓞 H.K) (𝓞 H.E) →
    ((H.QS * H.q : ℕ) : 𝓞 H.E) ∈ P

  principal : ∃ 𝔟 : Ideal (𝓞 H.E), differentIdeal (𝓞 H.K) (𝓞 H.E) = 𝔟 * (H.conj • 𝔟) ∧ 𝔟 ⊔ H.conj • 𝔟 = ⊤ ∧
    ∀ σ : H.E ≃ₐ[ℚ] H.E, H.gal σ ∈ φ.Psi → σ • 𝔟 = 𝔟

  unimodular : ∀ 𝔟 : Ideal (𝓞 H.E), differentIdeal (𝓞 H.K) (𝓞 H.E) = 𝔟 * (H.conj • 𝔟) → ∀ x : H.E,
    x ∈ ((𝔟 : FractionalIdeal (nonZeroDivisors (𝓞 H.E)) H.E)⁻¹) ↔
      ∀ y ∈ ((𝔟 : FractionalIdeal (nonZeroDivisors (𝓞 H.E)) H.E)⁻¹),
        Algebra.trace H.K H.E (x * H.conj y) ∈ (algebraMap (𝓞 H.K) H.K).range
  discr_sq : discr H.E = discr H.F ^ 2

  discr_primes : (∀ p : ℕ, p.Prime → (p : ℤ) ∣ discr H.E → p ∣ H.condN) ∧ (2 : ℤ) ∣ discr H.E ∧ (H.d : ℤ) ∣ discr H.E
  rd_ge : (2 : ℝ) ^ ((φ.e : ℝ) + 1 - (2 : ℝ) ^ (-(φ.e : ℝ))) * Real.sqrt H.d ≤ H.rd
  rd_le : H.rd ≤ (H.QS : ℝ) / 2 * Real.sqrt ((H.q : ℝ) * H.d)
  rd_sq_ge : (4 * φ.ord : ℝ) ≤ H.rd ^ 2

  norm_mu : ∀ x : H.E, (∃ m : ℕ, 0 < m ∧ x ^ m = 1) → Algebra.norm H.K x = 1

def DerOfRaw : Prop := ∀ (φ : Frame) (H : HostRaw φ), HostDer H

structure HostAx (φ : Frame) extends HostRaw φ where
  der : HostDer toHostRaw

namespace HostAx

variable {φ : Frame} (H : HostAx φ)

theorem hostE_isGalois : IsGalois ℚ H.E := H.galois
theorem isCMField_hostE : IsCMField H.E := H.der.cm
theorem finrank_cmField : Module.finrank ℚ H.E = 4 * φ.ord := H.der.finrank_E
theorem finrank_hostF : Module.finrank ℚ H.F = 2 * φ.ord := H.der.finrank_F
theorem galE_mul (σ τ : H.E ≃ₐ[ℚ] H.E) : H.galE (σ * τ) = H.galE σ * H.galE τ := map_mul H.gal σ τ
theorem galE_bijective : Function.Bijective H.galE := H.gal.bijective
theorem galE_injective : Function.Injective H.galE := H.gal.injective
theorem galE_one : H.galE 1 = 1 := map_one H.gal
theorem galE_inv (σ : H.E ≃ₐ[ℚ] H.E) : H.galE σ⁻¹ = (H.galE σ)⁻¹ := map_inv H.gal σ
theorem galE_pow (σ : H.E ≃ₐ[ℚ] H.E) (k : ℕ) : H.galE (σ ^ k) = H.galE σ ^ k := map_pow H.gal σ k
theorem exists_galE_eq (g : φ.GG) : ∃ σ : H.E ≃ₐ[ℚ] H.E, H.galE σ = g := ⟨H.gal.symm g, H.gal.apply_symm_apply g⟩
theorem galE_eq_one_iff (σ : H.E ≃ₐ[ℚ] H.E) : H.galE σ = 1 ↔ σ = 1 := MulEquiv.map_eq_one_iff H.gal
theorem galE_conjE : H.galE H.conj = φ.cc := H.gal.apply_symm_apply φ.cc
theorem eq_conjE_iff (σ : H.E ≃ₐ[ℚ] H.E) : σ = H.conj ↔ H.galE σ = φ.cc := by
  exact MulEquiv.eq_symm_apply H.gal
theorem isConj_iff_galE (ψ : H.E →+* ℂ) (σ : H.E ≃ₐ[ℚ] H.E) :
    (∀ x, ψ (σ x) = starRingEnd ℂ (ψ x)) ↔ H.galE σ = φ.cc := H.der.conj_iff ψ σ
theorem conjE_apply (ψ : H.E →+* ℂ) (x : H.E) : ψ (H.conj x) = starRingEnd ℂ (ψ x) := (H.der.conj_iff ψ H.conj).2 H.galE_conjE x
theorem conjE_mem_hostF_iff (x : H.E) : x ∈ H.F ↔ H.conj x = x := H.der.mem_F x
theorem galE_bE (σ : H.E ≃ₐ[ℚ] H.E) : σ H.sqd = ((((H.galE σ).1.2 : ℤˣ) : ℤ) : H.E) * H.sqd := H.gal_sqd σ

theorem sqd_ne_zero : H.sqd ≠ 0 := by
  intro h
  have h1 := H.sqd_sq
  rw [h] at h1
  have hd : H.d = 0 := by simpa using h1.symm
  exact H.hyp.2.1.ne_zero hd

theorem galE_mem_Psi_iff (σ : H.E ≃ₐ[ℚ] H.E) : H.galE σ ∈ φ.Psi ↔ σ H.sqd = H.sqd := by
  have hs := H.sqd_ne_zero
  rw [H.galE_bE σ]
  change (H.galE σ).1.2 = 1 ↔ _
  rcases Int.units_eq_one_or (H.galE σ).1.2 with h | h <;> rw [h]
  · simp
  · constructor
    · intro h2
      exact absurd h2 (by decide)
    · intro h2
      exfalso
      apply hs
      have h4 : ((((-1 : ℤˣ) : ℤ) : H.E)) = -1 := by simp
      rw [h4] at h2
      have h3 : (2 : H.E) * H.sqd = 0 := by linear_combination -h2
      exact (mul_eq_zero.1 h3).resolve_left two_ne_zero

end HostAx

end Formalism.HC

end
