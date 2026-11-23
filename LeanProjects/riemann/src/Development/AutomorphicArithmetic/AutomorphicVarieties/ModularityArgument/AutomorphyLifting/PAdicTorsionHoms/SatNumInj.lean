import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PlainAtR
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.FrobeniusPowerCompatibility

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GalOfCusp UpperTheory.Zero.LLC UpperTheory.V UpperTheory.V.Af UpperTheory.V.Z.Gam UpperTheory.V.Z.Win
open GroundTheory.Global.SemiLocal UpperTheory.V.Published

private theorem satNum_eq (n q : ℕ) (B : Multiset ℂˣ) :
    algSat n q B = B.map fun α : ℂˣ => (((q : ℝ) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ) * (α : ℂ) := by
  have e : (do let a ← B; pure (a : ℂ)) = B.map fun a : ℂˣ => (a : ℂ) := Multiset.bind_singleton _ _
  unfold algSat
  erw [e]
  rw [Multiset.map_map]
  rfl

private theorem satNum_pow (n q f : ℕ) (B : Multiset ℂˣ) :
    algSat n (q ^ f) (B.map (· ^ f)) = (algSat n q B).map (· ^ f) := by
  have hq : ((q : ℝ) ^ f) ^ (((n : ℝ) - 1) / 2) = ((q : ℝ) ^ (((n : ℝ) - 1) / 2)) ^ f := by
    rw [← Real.rpow_natCast (q : ℝ) f, ← Real.rpow_mul (Nat.cast_nonneg q), mul_comm,
      Real.rpow_mul_natCast (Nat.cast_nonneg q)]
  rw [satNum_eq, satNum_eq, Multiset.map_map, Multiset.map_map]
  refine Multiset.map_congr rfl fun b _ => ?_
  simp only [Function.comp_apply, Units.val_pow_eq_pow_val, mul_pow, Nat.cast_pow, hq, Complex.ofReal_pow]

private theorem satNum_inj (n q : ℕ) (hq : q ≠ 0) {B B' : Multiset ℂˣ} (h : algSat n q B = algSat n q B') : B = B' := by
  have hc : (((q : ℝ) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (Real.rpow_pos_of_pos (Nat.cast_pos.2 (Nat.pos_of_ne_zero hq)) _).ne'
  rw [satNum_eq, satNum_eq] at h
  exact Multiset.map_injective (fun a b e => Units.ext (mul_left_cancel₀ hc e)) h

private theorem frobEig_eq {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime]
    {n : ℕ} {ι : Qbar l ≃+* ℂ} {r : G F Ω →* GL (Fin n) (Qbar l)} {w : HeightOneSpectrum (𝓞 F)} {B B' : Multiset ℂ}
    (h : FrobEig ι r w B) (h' : FrobEig ι r w B') : B = B' := by
  obtain ⟨A, hA⟩ := exists_isPlaceOver Ω w
  obtain ⟨σ, hσ⟩ := exists_isFrob hA
  have e := congrArg Polynomial.roots (((h A hA).2 σ hσ).symm.trans ((h' A hA).2 σ hσ))
  rwa [roots_multiset_prod_X_sub_C, roots_multiset_prod_X_sub_C] at e

theorem UpperTheory.V.Z.Win.attBC :
    AttBC := by
  intro K L Ω _ _ _ _ _ _ _ _ _ _ _ _ l _ ι n r π P hπ hP
  haveI : Algebra.IsAlgebraic K Ω := IsAlgClosure.isAlgebraic
  haveI : IsAlgClosure L Ω := ⟨IsAlgClosure.isAlgClosed K, Algebra.IsAlgebraic.tower_top (K := K) (L := L) (A := Ω)⟩
  obtain ⟨-, hπ⟩ := hπ
  obtain ⟨-, hP⟩ := hP
  unfold WeakBC
  filter_upwards [(GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.tendsto_under K L).eventually hπ, hP] with w hw hw' f hf
  obtain ⟨B, hB, hF⟩ := hw
  obtain ⟨B', hB', hF'⟩ := hw'
  have h1 : FrobEig ι (r.comp (resG K L Ω)) w (algSat n (normV w) (B.map (· ^ f))) := by
    rw [hf, satNum_pow]
    exact (UpperTheory.frobenius_power_compatibility K L Ω l ι w f hf).1 n r _ hF
  have hq : normV w ≠ 0 := by
    rw [normV]
    exact (Ideal.absNorm_eq_zero_iff.not.2 w.ne_bot)
  have e := satNum_inj n _ hq (frobEig_eq hF' h1)
  exact ⟨B, hB, e ▸ hB'⟩
