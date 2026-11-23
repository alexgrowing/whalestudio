import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.FixedIntegersIsUnitOfNotMemPrimeSpan
import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.PresTr
import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.RepSmul
import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.WdVal
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.Col UpperTheory.Kd.C7

namespace UpperTheory.Kd.C7

section
variable {R : Type} [CommRing R]

private theorem sb_one_add (b : ℕ) : sb (R := R) b (1 + PowerSeries.X) = (1 + PowerSeries.X) ^ b := by
  rw [map_add, map_one, sb, PowerSeries.substAlgHom_X]; ring

private theorem sb_C (b : ℕ) (a : R) : sb b (PowerSeries.C a : PowerSeries R) = PowerSeries.C a :=
  (sb (R := R) b).commutes a

private theorem sb_eval₂ (b : ℕ) (P : Polynomial R) :
    sb b (P.eval₂ PowerSeries.C (1 + PowerSeries.X)) =
      (Polynomial.expand R b P).eval₂ PowerSeries.C (1 + PowerSeries.X) := by
  induction P using Polynomial.induction_on' with
  | add f g hf hg => simp only [Polynomial.eval₂_add, map_add, hf, hg]
  | monomial n a =>
    rw [Polynomial.expand_monomial, Polynomial.eval₂_monomial, Polynomial.eval₂_monomial, map_mul, map_pow,
      sb_one_add, sb_C, ← pow_mul, mul_comm b n]

private theorem map_sb' {S : Type} [CommRing S] (τ : R →+* S) (b : ℕ) (h : PowerSeries R) :
    PowerSeries.map τ (sb b h) = sb b (PowerSeries.map τ h) := by
  unfold sb
  rw [PowerSeries.coe_substAlgHom, PowerSeries.coe_substAlgHom]
  refine Eq.trans (PowerSeries.map_subst (hasSubst_pow (R := R) b) (h := τ) h) ?_
  congr 1
  change PowerSeries.map τ _ = _
  simp

private theorem dd_sb (b : ℕ) (hb : b ≠ 0) (f : PowerSeries R) :
    dd (sb b f) = (b : PowerSeries R) * sb b (dd f) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hb
  unfold dd
  rw [map_mul, sb_one_add]
  unfold sb
  rw [PowerSeries.coe_substAlgHom, PowerSeries.derivative_subst (hasSubst_pow (R := R) _)]
  simp only [map_sub, Derivation.leibniz_pow, map_add, Derivation.map_one_eq_zero, PowerSeries.derivative_X,
    smul_eq_mul, nsmul_eq_mul, Nat.succ_sub_one, Nat.succ_eq_add_one]
  ring

private theorem dl_sb (b : ℕ) (hb : b ≠ 0) (f : PowerSeries R) (hf : IsUnit f) :
    dl (sb b f) = (b : PowerSeries R) * sb b (dl f) := by
  obtain ⟨u, rfl⟩ := hf
  unfold dl
  have h1 : Ring.inverse (sb b (u : PowerSeries R)) = sb b ((u⁻¹ : (PowerSeries R)ˣ) : PowerSeries R) := by
    have := Ring.inverse_unit (Units.map (sb (R := R) b : PowerSeries R →* PowerSeries R) u)
    simpa using this
  rw [dd_sb b hb, h1, Ring.inverse_unit, map_mul, mul_assoc]

private theorem isUnit_nat {l : ℕ} [Fact l.Prime] (b : ℕ) (hb : ¬ l ∣ b) : IsUnit (b : ℤ_[l]) := by
  rw [PadicInt.isUnit_iff]
  refine le_antisymm (PadicInt.norm_le_one _) (not_lt.1 fun h => hb ?_)
  have : ‖((b : ℤ) : ℤ_[l])‖ < 1 := by simpa using h
  exact_mod_cast (PadicInt.norm_int_lt_one_iff_dvd (b : ℤ)).1 this

private theorem lc_sb {l : ℕ} [Fact l.Prime] [Algebra ℤ_[l] R] (b : ℕ) (hb : ¬ l ∣ b) (m n : ℕ) (f g : PowerSeries R)
    (h : LC l m n f g) : LC l m n ((b : PowerSeries R) * sb b f) ((b : PowerSeries R) * sb b g) := by
  obtain ⟨u, hu⟩ := isUnit_nat b hb
  unfold LC at h ⊢
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 h
  have h2 := congrArg (levAct (R := R) l m u) hy
  rw [map_sub, levAct_ev, levAct_ev, hu, sbp_nat, map_mul, map_pow, map_natCast] at h2
  rw [map_mul, map_mul, ← mul_sub, ← h2]
  exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _ (Ideal.subset_span rfl))

end

end UpperTheory.Kd.C7

theorem UpperTheory.Kd.C7.pRepTr :
    UpperTheory.Kd.C7.SRepTr := by
  intro l _ hl Ω _ _ _ A hA j Φ c β ζ hζ Z hZ b hb D hD
  have hb0 : b ≠ 0 := by rintro rfl; exact hb (dvd_zero l)
  have h1 : Rep Φ β ζ (fun r s x => (b : Qbar l) * tr b hb Z r s x)
      (fun i => (b : PowerSeries Φ.R) * sb b (D i)) := by
    obtain ⟨c₁, m₁, H⟩ := hD
    refine ⟨c₁, max m₁ 1, fun m hm => ?_⟩
    obtain ⟨P, hP, hL⟩ := H m (le_of_max_le_left hm)
    refine ⟨_, pPresTr l hl Ω A hA c β ζ hζ Z hZ b hb m _ P hP, fun i => ?_⟩
    have hu : IsUnit (Φ.ser (P i)) :=
      (pWD l hl Ω A hA j Φ ζ hζ m (le_of_max_le_right hm) (P i)).2 (hP.2.2.1 i)
    have e1 : Φ.ser (Polynomial.expand (R0 A) b (P i)) = sb b (Φ.ser (P i)) := by
      unfold Fr.ser
      rw [sb_eval₂, Polynomial.map_expand]
    have e2 : Φ.tw m ((b : PowerSeries Φ.R) * sb b (D i)) = (b : PowerSeries Φ.R) * sb b (Φ.tw m (D i)) := by
      unfold Fr.tw
      rw [map_mul, map_natCast, map_sb']
    rw [e1, e2, dl_sb b hb0 _ hu]
    exact lc_sb b hb _ _ _ _ (hL i)
  obtain ⟨u, hu⟩ := isUnit_nat (l := l) b hb
  have hw : ((u⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) * (b : ℤ_[l]) = 1 := by rw [← hu, Units.inv_mul]
  generalize ((u⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) = w at hw
  have h2 := pRepSmul l hl Ω A hA j Φ c β ζ hζ _ _ (algebraMap ℤ_[l] c.O w) h1
  convert h2 using 1
  · funext r s x
    have : ((algebraMap ℤ_[l] c.O w : c.O) : PadicAlgCl l) * (b : Qbar l) = 1 := by
      have := congrArg (algebraMap ℤ_[l] (PadicAlgCl l)) hw
      rw [map_mul, map_natCast, map_one] at this
      exact this
    rw [← mul_assoc, this, one_mul]
  · funext i
    have hm : β.mat (algebraMap ℤ_[l] c.O w) = Matrix.diagonal fun _ => w := by
      unfold Bas.mat
      rw [AlgHom.commutes, Matrix.algebraMap_eq_diagonal]
      rfl
    have h3 : PowerSeries.C (algebraMap ℤ_[l] Φ.R w) * (b : PowerSeries Φ.R) = 1 := by
      have := congrArg (fun z => PowerSeries.C (algebraMap ℤ_[l] Φ.R z)) hw
      simpa using this
    unfold Fr.act
    rw [hm, Finset.sum_eq_single i]
    · rw [Matrix.diagonal_apply_eq, ← mul_assoc, h3, one_mul]
    · intro k _ hk
      rw [Matrix.diagonal_apply_ne _ hk.symm]; simp
    · intro h; exact absurd (Finset.mem_univ i) h
