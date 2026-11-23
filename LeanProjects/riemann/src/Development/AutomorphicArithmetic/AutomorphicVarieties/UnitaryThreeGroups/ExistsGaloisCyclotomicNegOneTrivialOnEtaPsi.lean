import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.KatoUse
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.BoxDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.DatFacts

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Matrix IsLocalRing
open UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.Alg UpperTheory.V.U3

private theorem cycMod_cc {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] {σ : G ℚ Ω}
    (h : IsConjOm σ.toRingEquiv) : cycMod ℚ Ω l 1 σ = -1 := by
  obtain ⟨j, hj⟩ := h
  have hlp : l.Prime := Fact.out
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : NeZero (l : Ω) := ⟨Nat.cast_ne_zero.mpr hlp.ne_zero⟩
  haveI : ∀ i, HasEnoughRootsOfUnity Ω (l ^ i) := fun i => inferInstance
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω l
  have hζl : ζ ^ l = 1 := hζ.pow_eq_one
  have hσζ : σ.toRingEquiv ζ = ζ⁻¹ := by
    apply j.injective
    rw [hj, map_inv₀]
    have hn : ‖j ζ‖ = 1 := Complex.norm_eq_one_of_pow_eq_one (n := l)
      (by rw [← map_pow, hζl, map_one]) hlp.ne_zero
    rw [Complex.inv_def, Complex.normSq_eq_norm_sq, hn]
    simp
  have hspec := cyclotomicCharacter.spec (L := Ω) l σ.toRingEquiv ζ (n := 1) (by rw [pow_one]; exact hζl)
  have hval : ((cycMod ℚ Ω l 1 σ : (ZMod (l ^ 1))ˣ) : ZMod (l ^ 1)) =
      PadicInt.toZModPow 1 (cyclotomicCharacter Ω l σ.toRingEquiv).val := rfl
  set a : ZMod (l ^ 1) := PadicInt.toZModPow 1 (cyclotomicCharacter Ω l σ.toRingEquiv).val with ha
  haveI : NeZero (l ^ 1) := ⟨by simp [hlp.ne_zero]⟩
  have hlt : a.val < l := by simpa using ZMod.val_lt a
  have hinv : ζ⁻¹ = ζ ^ (l - 1) := by
    rw [eq_comm, inv_eq_of_mul_eq_one_right]
    rw [← pow_succ', Nat.sub_add_cancel hlp.one_le, hζl]
  have hav : a.val = l - 1 := by
    apply hζ.pow_inj hlt (Nat.sub_lt hlp.pos one_pos)
    rw [← hspec, hσζ, hinv]
  apply Units.ext
  rw [hval, ← ZMod.natCast_zmod_val a, hav, Units.val_neg, Units.val_one, eq_neg_iff_add_eq_zero]
  have h0 : ((l : ℕ) : ZMod (l ^ 1)) = 0 := by
    rw [ZMod.natCast_eq_zero_iff]
    simp
  rw [← h0, ← Nat.cast_succ, Nat.succ_eq_add_one, Nat.sub_add_cancel hlp.one_le]

theorem UpperTheory.exists_galois_cyclotomic_neg_one_trivial_on_eta_psi :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {K : Type} [Field K] [NumberField K] [Algebra K Ω]
          {l : ℕ} [Fact l.Prime] {c : Coef l} {N : ℕ} [NeZero N] {e : ℕ} {ψ : DirichletCharacter c.O N} (D : Dat Ω K c e ψ),
          ∃ g : G ℚ Ω, D.η g = 1 ∧ barChar c.O D.Ψ g = 1 ∧ cycMod ℚ Ω l 1 g = -1 := by
  intro Ω _ _ _ K _ _ _ l _ c N _ e ψ D
  obtain ⟨-, hηcc, hΨcc, -⟩ := dat_facts D
  have hcyc_cc : cycMod ℚ Ω l 1 D.cc = -1 := by
    apply cycMod_cc l
    obtain ⟨φ, hφ⟩ := D.conj
    exact ⟨φ, hφ⟩
  have hgd := D.gd.eta
  rw [← D.η_ker] at hgd
  obtain ⟨h, hmem, hnot⟩ := SetLike.not_le_iff_exists.mp hgd
  obtain ⟨hh1, hh2⟩ := Subgroup.mem_inf.mp hmem
  rw [MonoidHom.mem_ker] at hh1 hh2 hnot
  have hηh : D.η h = -1 := (Int.units_eq_one_or _).resolve_left hnot
  obtain ⟨⟨w, hw, -⟩, hall⟩ := omT Ω l c
  have hwk : w.ker = (cycMod ℚ Ω l 1).ker := (hall w hw).1
  have hwh : w h = 1 := by
    rw [← MonoidHom.mem_ker, hwk, MonoidHom.mem_ker]
    exact hh1
  obtain ⟨b, -, -, hcong⟩ := (psiBar Ω l c w hw N ψ).1
  have hΨh : barChar c.O D.Ψ h = 1 := by
    have hm := hcong e h
    rw [MonoidHom.mul_apply, MonoidHom.pow_apply, hwh, hh2, one_pow, mul_one, Units.val_one] at hm
    apply Units.ext
    show (residue c.O) ((D.Ψ h : (c.O)ˣ) : c.O) = ((1 : (ResidueField c.O)ˣ) : ResidueField c.O)
    rw [Units.val_one, ← map_one (residue c.O), ← sub_eq_zero, ← map_sub, residue_eq_zero_iff]
    exact hm
  refine ⟨D.cc * h, ?_, ?_, ?_⟩
  · rw [map_mul, hηcc, hηh]
    rfl
  · rw [map_mul, hΨh, mul_one]
    simp only [barChar, MonoidHom.coe_comp, Function.comp_apply, hΨcc, map_one]
  · rw [map_mul, hcyc_cc, hh1, mul_one]
