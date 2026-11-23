import Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.ZeroMemUnrHom
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.ResInfInj
import Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.LiftEx

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Bern UpperTheory.V.B4 UpperTheory.V.B5 UpperTheory.V.Odd

private theorem pow_tot_mem (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (N : ℕ) [NeZero N] (g : G E Ω) : g ^ N.totient ∈ fixMu E Ω N := by
  obtain ⟨b, hb⟩ := (liftEx E Ω N).2 g.toRingEquiv
  intro x hx
  have h : ∀ k : ℕ, (g ^ k) x = x ^ ((b : ZMod N).val ^ k) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', AlgEquiv.mul_apply, ih, map_pow, pow_succ', pow_mul]
      congr 1
      exact hb x hx
  rw [h, pow_eq_pow_mod _ hx, (Nat.ModEq.pow_totient (ZMod.val_coe_unit_coprime b) : _ % N = 1 % N),
    ← pow_eq_pow_mod _ hx, pow_one]

theorem UpperTheory.V.Odd.totKill :
    ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (D : LData E Ω l) (e : ℤ) (N : ℕ) [NeZero N], e ≠ 0 → Procyc E Ω l → ∀ x : H1 (qzTw D e), (∀ u : Uinf E Ω l, u.1 ∈ fixMu E Ω N → resInf D e x u = 0) → N.totient • x = 0 := by
  intro E Ω _ _ _ _ _ l _ D e N _ he hP x hx
  have hadd : ∀ a b : Uinf E Ω l, resInf D e x (a * b) = resInf D e x a + resInf D e x b := by
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have hchi : ∀ g : G E Ω, D.chi (toGS Ω _ g) = cycZ E Ω l g := fun g => DFunLike.congr_fun D.hchi g
    have htriv : ∀ g : G E Ω, cycZ E Ω l g = 1 → ∀ m, qzTw D e (toGS Ω _ g) m = m := fun g hg m => by
      rw [qzTw_apply, hchi, hg, one_zpow, Units.val_one, one_smul]
    have hz : ∀ a b, z.1 (a * b) = z.1 a + qzTw D e a (z.1 b) := z.2.2
    intro a b
    rw [resInf_mk, resInf_mk, resInf_mk, Subgroup.coe_mul, map_mul, hz, htriv _ a.2.2]
  have hpow : ∀ (u : Uinf E Ω l) (k : ℕ), resInf D e x (u ^ k) = k • resInf D e x u := by
    intro u k
    induction k with
    | zero =>
      have := hadd 1 1
      rw [one_mul] at this
      rw [pow_zero, zero_smul]
      exact left_eq_add.1 this
    | succ k ih => rw [pow_succ, hadd, ih, succ_nsmul]
  apply resInfInj E Ω l D e he hP
  rw [map_nsmul, map_zero]
  funext u
  rw [Pi.smul_apply, ← hpow]
  exact hx _ (by rw [Subgroup.coe_pow]; exact pow_tot_mem E Ω N u.1)
