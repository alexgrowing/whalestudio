import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.HcDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.EtaKer
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.HostNumber
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.CongrFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.HcOmDir
import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.HcDirData
import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.HcDirVal
import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.Th1Facts

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.X

private theorem res_of_sub {O : Type} [CommRing O] [IsLocalRing O] {x y : O} (h : x - y ∈ maximalIdeal O) :
    residue O x = residue O y := by
  exact Ideal.Quotient.eq.2 h

private theorem dirG_pow_one {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {O : Type} [CommRing O] {N : ℕ} [NeZero N]
    (χ : DirichletCharacter O N) (m : ℕ) (h : χ ^ m = 1) : Chr.dirG ℚ Ω χ ^ m = 1 := by
  ext g
  simp only [MonoidHom.pow_apply, MonoidHom.one_apply, Units.val_pow_eq_pow_val, Units.val_one]
  show (χ (Chr.cls ℚ Ω N g : ZMod N)) ^ m = 1
  rw [← MulChar.pow_apply_coe, h, MulChar.one_apply_coe]

theorem UpperTheory.V.X.dir :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (c : Coef l) (N : ℕ) [NeZero N] (e : ℕ) (ψ : DirichletCharacter c.O N) (o₁ : ℕ), UnitaryThreeInertia.HostData l e ψ o₁ → ∀ q : ℕ, UnitaryThreeInertia.XData l ψ q → ∃ (d f n : ℕ) (_ : NeZero (f * 2 ^ n)) (φ : DirichletCharacter c.O f) (ξ : DirichletCharacter c.O (2 ^ n)), XData l d φ ξ ∧ ∀ g : G ℚ Ω, (redChar Ω (residue c.O) (prodX φ ξ) g : ResidueField c.O) = residue c.O (Chr.Psi l e (Chr.dirG ℚ Ω ψ) g : c.O) ^ 2 * ((UnitaryThreeInertia.eta4 Ω g : ℤ) : ResidueField c.O) := by
  intro Ω _ _ _ l _ c N _ e ψ o₁ hHD q hX
  obtain ⟨ω, hω1, hωT⟩ := omDir Ω l c
  obtain ⟨d, f, n, φ, ξ, hXD, hdvd, hv⟩ := dirData l c N e ψ o₁ hHD q hX ω hω1
  have hl : l.Prime := Fact.out
  haveI : NeZero l := ⟨hl.ne_zero⟩
  have hf0 : f ≠ 0 := by
    rintro rfl
    obtain ⟨k, hk⟩ := hXD.f_odd
    omega
  haveI hNZ : NeZero (f * 2 ^ n) := ⟨Nat.mul_ne_zero hf0 (pow_ne_zero _ two_ne_zero)⟩
  haveI : NeZero (l * N * N) := ⟨Nat.mul_ne_zero (Nat.mul_ne_zero hl.ne_zero (NeZero.ne N)) (NeZero.ne N)⟩
  refine ⟨d, f, n, hNZ, φ, ξ, hXD, ?_⟩
  intro g
  obtain ⟨a, ha, hA⟩ := dirVal Ω (l * N * N) g
  obtain ⟨hψdec, ⟨s, hks⟩, -⟩ := th1Facts c.O N ψ l hl hHD.l_odd
  have hprod := hA (f * 2 ^ n) hdvd c.O (prodX φ ξ)
  have hψa := hA N ⟨l * N, by ring⟩ c.O ψ
  have hωa := hA l ⟨N * N, by ring⟩ c.O ω
  have h4 : 4 ∣ l * N * N := by
    obtain ⟨k, hk⟩ := hHD.N_even
    exact ⟨l * k * k, by rw [hk]; ring⟩
  have hη := hA 4 h4 ℤ ZMod.χ₄
  have hkap := hA N ⟨l * N, by ring⟩ c.O (kap l ψ)
  have hkC := (congrFacts Ω l c).2.2.1 (Chr.dirG ℚ Ω (kap l ψ)) s (dirG_pow_one _ _ hks)
  have hk1 : residue c.O (kap l ψ (a : ZMod N)) = 1 := by
    rw [← hkap, res_of_sub (hkC g)]
    simp
  have hωC := res_of_sub (hωT.2 g)
  rw [hωa] at hωC
  have hψa' : ψ (a : ZMod N) = psi2 ψ (a : ZMod N) * th1 l ψ (a : ZMod N) * kap l ψ (a : ZMod N) := by
    conv_lhs => rw [hψdec]
    rfl
  have hLHS : (redChar Ω (residue c.O) (prodX φ ξ) g : ResidueField c.O) =
      residue c.O ((prodX φ ξ) (a : ZMod (f * 2 ^ n))) := by
    show residue c.O (Chr.dirG ℚ Ω (prodX φ ξ) g : c.O) = _
    rw [hprod]
  have hP : (Chr.Psi l e (Chr.dirG ℚ Ω ψ) g : c.O) = (chiO ℚ Ω l c.O g : c.O) ^ e * ψ (a : ZMod N) := by
    simp only [Chr.Psi, zpow_natCast, MonoidHom.mul_apply, MonoidHom.pow_apply, Units.val_mul,
      Units.val_pow_eq_pow_val, hψa]
  have hE : ((UnitaryThreeInertia.eta4 Ω g : ℤ)) = ZMod.χ₄ (a : ZMod 4) := hη
  rw [hLHS, hv a ha, hP, hE, hψa']
  simp only [map_mul, map_pow, map_intCast]
  rw [← hωC, hk1]
  ring
