import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.ShaFamMono
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.ExistsO

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V.Base UpperTheory.Top

namespace UpperTheory.V.HV

structure Coef (l : ℕ) [Fact l.Prime] where
  O : Subalgebra ℤ_[l] (PadicAlgCl l)
  dvr : IsDiscreteValuationRing O
  fin : Module.Finite ℤ_[l] O

attribute [instance] Coef.dvr Coef.fin

instance factPrimes (p : Nat.Primes) : Fact (p : ℕ).Prime := ⟨p.2⟩

section Parts

variable {Γ : Type} [Group Γ]

def lPart (l : ℕ) (x : Γ) : Γ := x ^ (ordCompl[l] (orderOf x)) ^ Nat.totient (ordProj[l] (orderOf x))

def lPrime (l : ℕ) (x : Γ) : Γ := x * (lPart l x)⁻¹

theorem lPrime_mul_lPart (l : ℕ) (x : Γ) : lPrime l x * lPart l x = x := inv_mul_cancel_right _ _

end Parts

theorem coprime_ordProj_ordCompl (r N : ℕ) : (ordProj[r] N).Coprime (ordCompl[r] N) := by
  by_cases hr : r.Prime
  · by_cases hN : N = 0
    · subst hN
      simp
    · exact Nat.Coprime.pow_left _ (Nat.coprime_ordCompl hr hN)
  · rw [Nat.factorization_eq_zero_of_not_prime N hr, pow_zero]
    exact Nat.coprime_one_left _

def idem (r N : ℕ) : ZMod N := ((ordCompl[r] N ^ Nat.totient (ordProj[r] N) : ℕ) : ZMod N)

theorem idem_mul_idem (r N : ℕ) : idem r N * idem r N = idem r N := by
  unfold idem
  rw [← Nat.cast_mul]
  have hcop : (ordCompl[r] N).Coprime (ordProj[r] N) := (coprime_ordProj_ordCompl r N).symm
  have hapos : 0 < ordProj[r] N := Nat.ordProj_pos N r
  have he1 : ordCompl[r] N ^ Nat.totient (ordProj[r] N) ≡ 1 [MOD ordProj[r] N] :=
    Nat.ModEq.pow_totient hcop
  have hdvd : ordCompl[r] N ∣ ordCompl[r] N ^ Nat.totient (ordProj[r] N) :=
    dvd_pow_self _ (Nat.totient_pos.mpr hapos).ne'
  have hA : ordCompl[r] N ^ Nat.totient (ordProj[r] N) * ordCompl[r] N ^ Nat.totient (ordProj[r] N) ≡
      ordCompl[r] N ^ Nat.totient (ordProj[r] N) [MOD ordProj[r] N] := by
    refine (he1.mul he1).trans ?_
    rw [one_mul]
    exact he1.symm
  have hC : ordCompl[r] N ^ Nat.totient (ordProj[r] N) * ordCompl[r] N ^ Nat.totient (ordProj[r] N) ≡
      ordCompl[r] N ^ Nat.totient (ordProj[r] N) [MOD ordCompl[r] N] :=
    (Nat.modEq_zero_iff_dvd.mpr (dvd_mul_of_dvd_left hdvd _)).trans
      (Nat.modEq_zero_iff_dvd.mpr hdvd).symm
  have key := (Nat.modEq_and_modEq_iff_modEq_mul hcop.symm).mp ⟨hA, hC⟩
  rw [Nat.ordProj_mul_ordCompl_eq_self N r] at key
  exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr key

def projZ (r N : ℕ) : ZMod N →* ZMod N where
  toFun u := idem r N * u + (1 - idem r N)
  map_one' := by ring
  map_mul' u v := by linear_combination (-(u * v) + u + v - 1) * idem_mul_idem r N

def proj (r N : ℕ) : (ZMod N)ˣ →* (ZMod N)ˣ := Units.map (projZ r N)

section Data

variable {O : Type} [CommRing O] {N : ℕ}

def comp (r : ℕ) (χ : DirichletCharacter O N) : DirichletCharacter O N :=
  MulChar.ofUnitHom (χ.toUnitHom.comp (proj r N))

def kap (l : ℕ) (ψ : DirichletCharacter O N) : DirichletCharacter O N := lPart l ψ

def th0 (l : ℕ) (ψ : DirichletCharacter O N) : DirichletCharacter O N := lPrime l ψ

def psi2 (ψ : DirichletCharacter O N) : DirichletCharacter O N := comp 2 ψ

def th1 (l : ℕ) (ψ : DirichletCharacter O N) : DirichletCharacter O N := th0 l ψ * (comp 2 (th0 l ψ))⁻¹

def chiP (l : ℕ) (ψ : DirichletCharacter O N) : DirichletCharacter O N := th0 l ψ * (comp l (th0 l ψ))⁻¹

def kapL (l : ℕ) (ψ : DirichletCharacter O N) : DirichletCharacter O N := comp l (kap l ψ)

def kapB (l : ℕ) (ψ : DirichletCharacter O N) : DirichletCharacter O N := kap l ψ * (kapL l ψ)⁻¹

def c2 (ψ : DirichletCharacter O N) : ℕ := (psi2 ψ).conductor.factorization 2

open Classical in

def Sb (l : ℕ) (ψ : DirichletCharacter O N) : Finset ℕ := N.primeFactors.filter fun p => p ≠ l ∧ comp p (kap l ψ) ≠ 1

def Tb (l : ℕ) (ψ : DirichletCharacter O N) : Finset ℕ := insert l (Sb l ψ)

def f0 (l : ℕ) (ψ : DirichletCharacter O N) : ℕ := orderOf (l : ZMod (Nat.lcm 4 (orderOf (th1 l ψ))))

def n0 (l : ℕ) (ψ : DirichletCharacter O N) : ℕ := (l ^ f0 l ψ - 1).factorization 2

def PsiEven (e : ℕ) (ψ : DirichletCharacter O N) : Prop := ψ (-1) = (-1) ^ e

def EV (l : ℕ) (ψ : DirichletCharacter O N) : Prop := Even (orderOf (chiP l ψ))

theorem dirichletPrimeToLPart_mul_lPowerPart (l : ℕ) (ψ : DirichletCharacter O N) : th0 l ψ * kap l ψ = ψ := lPrime_mul_lPart l ψ

end Data

section Len

variable (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] (c : Coef l) {N : ℕ} [NeZero N]

def Vlen (e : ℕ) (ψ : DirichletCharacter c.O N) : ℕ∞ := Chr.V' l N e (Chr.dirG ℚ Ω ψ)

def Vn (e : ℕ) (ψ : DirichletCharacter c.O N) : ℝ := Chr.nrm l c.O (Vlen Ω c e ψ)

def VLe (e : ℕ) (ψ : DirichletCharacter c.O N) (B : ℝ) : Prop := Vlen Ω c e ψ ≠ ⊤ ∧ Vn Ω c e ψ * Real.log l ≤ B

def kerFam {O : Type} [CommRing O] (l : ℕ) (θ : G ℚ Ω →* Oˣ) : Set (Subgroup (G ℚ Ω)) :=
  {D | (∃ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 ∧ D = Dec (F := ℚ) A) ∨
    ∃ A : ValuationSubring Ω, ¬ A.valuation (l : Ω) < 1 ∧ D = Ine (F := ℚ) A ⊓ θ.ker}

def VkerLen (e : ℕ) (ψ : DirichletCharacter c.O N) : ℕ∞ :=
  Module.length c.O (LocSel (Chr.rho l e (Chr.dirG ℚ Ω ψ)) ⊤ (kerFam Ω l (Chr.dirG ℚ Ω ψ)))

def hLen (e : ℕ) (ψ : DirichletCharacter c.O N) : ℕ∞ :=
  ∑ᶠ (v : HeightOneSpectrum (𝓞 ℚ)) (_ : ((l * N : ℕ) : 𝓞 ℚ) ∈ v.asIdeal),
    Chr.h0 l e (Chr.dirG ℚ Ω ψ) (Dec (F := ℚ) (placeOf Ω v))

def hn (e : ℕ) (ψ : DirichletCharacter c.O N) : ℝ := Chr.nrm l c.O (hLen Ω c e ψ)

theorem Vn_nonneg (e : ℕ) (ψ : DirichletCharacter c.O N) : 0 ≤ Vn Ω c e ψ := Chr.nrm_nonneg _ _

theorem VLe.mono {e : ℕ} {ψ : DirichletCharacter c.O N} {B B' : ℝ} (h : VLe Ω c e ψ B) (hB : B ≤ B') : VLe Ω c e ψ B' :=
  ⟨h.1, h.2.trans hB⟩

def orb (H : Subgroup (ZMod N)ˣ) : Finset (DirichletCharacter c.O N) :=
  (Set.toFinite {ψ : DirichletCharacter c.O N | ψ.toUnitHom.ker = H}).toFinset

theorem mem_orb {H : Subgroup (ZMod N)ˣ} {ψ : DirichletCharacter c.O N} : ψ ∈ orb c H ↔ ψ.toUnitHom.ker = H :=
  Set.Finite.mem_toFinset _

end Len

structure Host where
  chi : PChar
  ex : ℕ
  q1 : ℕ
  d : ℕ
  two_le : 2 ≤ ex
  pair : PrimePair chi.N q1 d

namespace Host

variable (h : Host)

abbrev q : ℕ := h.chi.N

abbrev o : ℕ := ordC h.chi

def N : ℕ := Nat.lcm (2 ^ (h.ex + 2)) h.q * (h.q1 * h.d)

theorem N_pos : 0 < h.N := by
  unfold N
  obtain ⟨hq1, -, hd, -, -⟩ := h.pair
  have hq : 0 < h.q := Nat.pos_of_ne_zero h.chi.ne.out
  exact Nat.mul_pos (Nat.lcm_pos (by positivity) hq) (Nat.mul_pos hq1.pos hd.pos)

instance : NeZero h.N := ⟨h.N_pos.ne'⟩

theorem two_pow_dvd : 2 ^ (h.ex + 2) ∣ h.N := (Nat.dvd_lcm_left _ _).mul_right _
theorem q_dvd : h.q ∣ h.N := (Nat.dvd_lcm_right _ _).mul_right _
theorem host_q1_dvd_N : h.q1 ∣ h.N := (dvd_mul_right _ _).mul_left _
theorem d_dvd : h.d ∣ h.N := (dvd_mul_left _ _).mul_left _

def H : Subgroup (ZMod h.N)ˣ :=
  (Subgroup.zpowers (-1)).comap (ZMod.unitsMap h.two_pow_dvd) ⊓ h.chi.χ.toUnitHom.ker.comap (ZMod.unitsMap h.q_dvd) ⊓
    (powMonoidHom 2).range.comap (ZMod.unitsMap h.host_q1_dvd_N) ⊓ (powMonoidHom 2).range.comap (ZMod.unitsMap h.d_dvd)

def IsChar {O : Type} [CommRing O] (ψ : DirichletCharacter O h.N) : Prop := h.H ≤ ψ.toUnitHom.ker

def Big (t : ℕ) : Prop :=
  2 * t + 1 < h.q1 ∧ 2 * t + 1 < h.d ∧ ∀ y ∈ [h.q, h.o, pK h.chi, hStar h.chi, pOne h.chi], y < h.q1 ∧ y < h.d

def X {l : ℕ} [Fact l.Prime] (c : Coef l) (e : ℕ) : Finset (DirichletCharacter c.O h.N) :=
  (Set.toFinite (Chr.evenSet c.O h.H e)).toFinset

theorem mem_X {l : ℕ} [Fact l.Prime] {c : Coef l} {e : ℕ} {ψ : DirichletCharacter c.O h.N} :
    ψ ∈ h.X c e ↔ h.IsChar ψ ∧ PsiEven e ψ := Set.Finite.mem_toFinset _

theorem host_q1_mod_four_eq_three : h.q1 % 4 = 3 := by
  obtain ⟨-, h8, -⟩ := h.pair
  omega
theorem d_mod : h.d % 4 = 3 := by
  obtain ⟨-, -, -, h16, -⟩ := h.pair
  omega
theorem firstPrime_ne_secondPrime : h.q1 ≠ h.d := by
  obtain ⟨-, h8, -, h16, -⟩ := h.pair
  omega

variable {O : Type} [CommRing O]

def R1 (l : ℕ) (ψ : DirichletCharacter O h.N) : ℕ := 16 * h.o * (l * h.q) ^ 2 * 4 ^ n0 l ψ

def CaseI (l e : ℕ) : Prop := l ∉ Bchi h.chi ∧ ¬ l - 1 ∣ 2 * e

def CaseZ (l e : ℕ) (ψ : DirichletCharacter O h.N) : Prop := l ∉ Bchi h.chi ∧ l - 1 ∣ 2 * e ∧ ψ = 1

def CaseII (l e : ℕ) (ψ : DirichletCharacter O h.N) : Prop := 2 ≤ e ∧ EV l ψ ∧ (l ∈ Bchi h.chi ∨ l - 1 ∣ 2 * e)

def CaseIII (l e : ℕ) (ψ : DirichletCharacter O h.N) : Prop :=
  l ∉ Bchi h.chi ∧ l - 1 ∣ 2 * e ∧ Odd (orderOf ψ) ∧ ψ ≠ 1

def CaseIV (l e : ℕ) (ψ : DirichletCharacter O h.N) : Prop := l ∈ Bchi h.chi ∧ 2 ≤ e ∧ Odd (orderOf (chiP l ψ))

def CaseV (l e : ℕ) : Prop := l ∈ Bchi h.chi ∧ e = 1

def nII (l : ℕ) (ψ : DirichletCharacter O h.N) : ℕ :=
  Nat.clog 2 (max (l * h.N * 4 ^ n0 l ψ) (2 ^ (c2 ψ + 6) * h.o * l ^ 3 * h.q ^ 2))

def nIII (l : ℕ) (ψ : DirichletCharacter O h.N) : ℕ :=
  Nat.clog 2 (max (l * h.q * pOne h.chi * 4 ^ n0 l ψ) (8 * l ^ 2))

end Host

theorem exists_coef (l : ℕ) [Fact l.Prime] (n : ℕ) [NeZero n] : ∃ c : Coef l, HasEnoughRootsOfUnity c.O n := by
  obtain ⟨O, a, b, c⟩ := existsO l n
  exact ⟨⟨O, a, b⟩, c⟩

example (χ : PChar) (h : (3 * 7).Coprime χ.N) : Host := ⟨χ, 2, 3, 7, le_rfl, by norm_num, by norm_num, by norm_num, by norm_num, h⟩

end UpperTheory.V.HV

end
