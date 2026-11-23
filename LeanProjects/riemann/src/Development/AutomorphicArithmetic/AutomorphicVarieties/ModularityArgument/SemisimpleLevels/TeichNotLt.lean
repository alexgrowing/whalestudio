import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.LevBasis
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.ClsFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RamifiedLineCharacters.CoefFacts

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

private theorem teich_not_lt {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {l N : ℕ} (h : l.Coprime N)
    (hl : A.valuation (l : Ω) < 1) : ¬ A.valuation (N : Ω) < 1 := by
  intro hN
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.mpr h
  have ha : A.valuation (a : Ω) ≤ 1 := by simpa using A.valuation_le_one (a : A)
  have hb : A.valuation (b : Ω) ≤ 1 := by simpa using A.valuation_le_one (b : A)
  have hv : A.valuation ((a : Ω) * l + (b : Ω) * N) < 1 := by
    refine lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt ?_ ?_)
    · rw [Valuation.map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_left' ha) hl
    · rw [Valuation.map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_left' hb) hN
  have h1 : ((a : Ω) * l + (b : Ω) * N) = 1 := by
    have e := congrArg (Int.cast : ℤ → Ω) hab
    push_cast at e
    exact e
  rw [h1, map_one] at hv
  exact lt_irrefl _ hv

theorem UpperTheory.V.Lev.teichDvd :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ N : ℕ, 1 ≤ N → Af.KillsMu N D.om → l ∣ N := by
  intro Ω _ _ _ l _ c D hD N hN hK
  by_contra hnd
  have hp : l.Prime := Fact.out
  have hcop : l.Coprime N := (Nat.Prime.coprime_iff_not_dvd hp).mpr hnd
  have hl := hD.pl_over l hp
  have hNA := teich_not_lt (D.pl l) hcop hl
  have hNz : NeZero N := ⟨by omega⟩
  have hIne := (Chr.clsFacts ℚ Ω N).2.2.2.2 (D.pl l) hNA
  obtain ⟨σ, hσ, hcyc⟩ := GlobalTheory.CycInertia.cycZ_Ine_surjective Ω l (D.pl l) hl (-1)
  have hom : D.om σ = 1 := by
    apply hK σ
    intro ζ hζ
    rw [Chr.cls_spec N σ ζ hζ, MonoidHom.mem_ker.mp (hIne hσ), Units.val_one, ZMod.val_one_eq_one_mod]
    rcases Nat.lt_or_ge N 2 with h2 | h2
    · have h1 : N = 1 := by omega
      subst h1
      simp at hζ ⊢
      exact hζ.symm
    · rw [Nat.one_mod_eq_one.mpr (by omega), pow_one]
  have hbar := hD.om_bar σ
  simp only [Raw.bar, hom, chiO, MonoidHom.comp_apply, hcyc] at hbar
  simp [Units.coe_map] at hbar
  have hch := (Ws.Gys.coefFacts c (ResidueField c.O) (residue c.O)
    (fun x hx => (IsLocalRing.residue_eq_zero_iff x).mpr hx)).1
  have h2 : ((2 : ℕ) : ResidueField c.O) = 0 := by
    have e : (1 : ResidueField c.O) + 1 = 0 := by
      nth_rewrite 1 [hbar]
      exact neg_add_cancel 1
    rw [Nat.cast_ofNat, ← e]
    norm_num
  have hdvd := (CharP.cast_eq_zero_iff (ResidueField c.O) l 2).mp h2
  have hle := Nat.le_of_dvd (by norm_num) hdvd
  have hge := hp.two_le
  exact hD.l_odd (by omega)
