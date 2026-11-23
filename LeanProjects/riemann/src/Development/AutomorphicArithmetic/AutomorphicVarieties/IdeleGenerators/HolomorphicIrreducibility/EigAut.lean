import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ShapeFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.ToNewform
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.DenseRangeUnitsR
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.AlgCyc
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.NewformAut
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.GaloisRepIrreducibilityCriterion
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.ClsFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.PlaceBasic

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial GlobalTheory.GalOfCusp
open UpperTheory.V UpperTheory.V.Af
open scoped Matrix

private theorem ev_not_mem (N : ℕ) (hN : N ≠ 0) :
    ∀ᶠ w : HeightOneSpectrum (𝓞 ℚ) in Filter.cofinite, ((N : ℕ) : 𝓞 ℚ) ∉ w.asIdeal := by
  have h0 : Ideal.span {((N : ℕ) : 𝓞 ℚ)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hN
  refine Filter.eventually_cofinite.2 ((Ideal.finite_factors h0).subset fun w hw => ?_)
  simp only [Set.mem_setOf_eq, not_not] at hw
  exact Ideal.dvd_span_singleton.2 hw

private theorem cls_frob {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (N : ℕ) [NeZero N]
    {A : ValuationSubring Ω} (hN : ¬ A.valuation (N : Ω) < 1) {q : ℕ} {σ : G ℚ Ω} (hσ : IsFrob A q σ) :
    ((Chr.cls ℚ Ω N σ : (ZMod N)ˣ) : ZMod N) = q := by
  obtain ⟨-, -, -, -, -, -, hpow, -⟩ := ML.placeBasic Ω
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : NeZero ((N : ℕ) : Ω) := ⟨Nat.cast_ne_zero.mpr (NeZero.ne N)⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω N
  have h2 : σ ζ = ζ ^ q := hpow A _ N _ hσ hN ζ hζ.pow_eq_one
  rw [Chr.cls_spec N σ ζ hζ.pow_eq_one, pow_eq_pow_mod q hζ.pow_eq_one] at h2
  have h3 := hζ.pow_inj (ZMod.val_lt _) (Nat.mod_lt _ (NeZero.pos N)) h2
  rw [← ZMod.natCast_zmod_val ((Chr.cls ℚ Ω N σ : (ZMod N)ˣ) : ZMod N), h3, ZMod.natCast_mod]

private theorem charpoly_adj {k : Type} [Field k] (g : GL (Fin 2) k) :
    ((g : Matrix (Fin 2) (Fin 2) k).det • ((g⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k)).charpoly =
      (g : Matrix (Fin 2) (Fin 2) k).charpoly := by
  have hd : (g : Matrix (Fin 2) (Fin 2) k).det ≠ 0 := (Matrix.isUnits_det_units g).ne_zero
  rw [Matrix.coe_units_inv, Matrix.inv_def, smul_smul, Ring.inverse_eq_inv, mul_inv_cancel₀ hd, one_smul,
    Matrix.charpoly_fin_two, Matrix.charpoly_fin_two, Matrix.adjugate_fin_two]
  simp only [Matrix.trace_fin_two, Matrix.det_fin_two, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one]
  congr 2
  · congr 2; ring
  · ring

theorem UpperTheory.V.Sd.eigAut :
    UpperTheory.V.Sd.Hypotheses₂ → UpperTheory.V.Sd.EigAut := by
  intro P k N _ hk χ hχ g l hl Ω _ _ _ ι ρ _ hirr hw
  obtain ⟨f, -, hfa, hfχ⟩ := Sd.toNewform P k N hk χ hχ g
  obtain ⟨hopen, -, -, -, hine⟩ := Chr.clsFacts ℚ Ω N
  set d : G ℚ Ω →* (Qbar l)ˣ := Chr.dirG ℚ Ω (χ.ringHomComp ι.symm.toRingHom) with hd
  have hker : (Chr.cls ℚ Ω N).ker ≤ d.ker := fun s hs => by
    rw [MonoidHom.mem_ker, hd, Chr.dirG, MonoidHom.comp_apply, MonoidHom.mem_ker.1 hs, map_one]
  have halg : Sd.IsAlgChar ι d := by
    have := (Sd.algCyc P.af ℚ Ω l ι).1 0 d (Subgroup.isOpen_mono hker hopen)
    rwa [zpow_zero, one_mul] at this
  have hbas := UpperTheory.galoisRep_irreducibility_criterion.1 (G ℚ Ω) (G ℚ Ω) (Qbar l) 2
  have haut : IsAutR ι (tw ρ d⁻¹) := by
    refine Af.newformAutR P.af k hk f l Ω ι _ (-((k - 1 : ℕ) : ℤ))
      ⟨(hbas _).2.2 _ ((hbas _).2.2 _ ((hbas _).2.1 hirr)), ?_⟩
    filter_upwards [hw, ev_not_mem l hl.out.ne_zero, ev_not_mem N (NeZero.ne N)] with w hw hwl hwN A hA
    have hN : ¬ A.valuation (N : Ω) < 1 := fun h => hwN ((hA N).1 (by simpa using h))
    refine ⟨fun s hs => ?_, fun σ hσ => ?_⟩
    · have h2 : cycZ ℚ Ω l s = 1 := by
        refine Units.ext (PadicInt.ext_of_toZModPow.mp fun n => ?_)
        rw [cycZ_toZModPow_eq (v := w) hwl hA (q := 1) (fun x hx => by simpa using hs.2 x hx) n]
        simp
      have h3 : (cycBar ℚ Ω l ^ (-((k - 1 : ℕ) : ℤ))) s = 1 := by
        rw [MonoidHom.zpow_apply, cycBar, MonoidHom.comp_apply, h2, map_one, one_zpow]
      have h4 : d s = 1 := hker (hine A hN hs)
      apply Units.ext
      rw [tw_val, tw_val, h3, MonoidHom.inv_apply, h4, (hw A hA).1 s hs]
      simp
    · have h1 := (hw A hA).2 σ hσ
      have h2 : ((cycBar ℚ Ω l σ : (Qbar l)ˣ) : Qbar l) = (normV w : ℕ) := by
        change algebraMap ℚ_[l] (Qbar l) (PadicInt.Coe.ringHom ((cycZ ℚ Ω l σ : ℤ_[l]ˣ) : ℤ_[l])) = _
        rw [cycZ_of_isFrob hwl hA hσ, map_natCast, map_natCast]
      have h3 : ι (d σ : Qbar l) = χ (normV w : ZMod N) := by
        rw [hd, Chr.dirG, MonoidHom.comp_apply, MulChar.coe_toUnitHom, cls_frob N hN hσ, MulChar.ringHomComp_apply]
        simp
      have h4 : ι (ρ σ : Matrix (Fin 2) (Fin 2) (Qbar l)).det = χ (normV w : ZMod N) * (normV w : ℂ) ^ (k - 1) := by
        have := congrArg (eval 0) h1
        rw [Matrix.charpoly_fin_two] at this
        simpa using this
      have h5 : (((cycBar ℚ Ω l ^ (-((k - 1 : ℕ) : ℤ))) σ⁻¹ : (Qbar l)ˣ) : Qbar l) * ((d⁻¹ σ⁻¹ : (Qbar l)ˣ) : Qbar l) =
          (ρ σ : Matrix (Fin 2) (Fin 2) (Qbar l)).det := by
        apply ι.injective
        rw [h4, MonoidHom.zpow_apply, MonoidHom.inv_apply, map_inv, map_inv, inv_inv, inv_zpow', neg_neg, zpow_natCast,
          Units.val_pow_eq_pow_val, h2, map_mul, h3, map_pow, map_natCast, mul_comm]
      rw [tw_val, tw_val, smul_smul, h5, map_inv, charpoly_adj, h1, Newform.heckePoly, hfa, hfχ]
  have h := Sd.twR P.af ℚ Ω l ι 2 _ d halg haut
  have e : tw (tw ρ d⁻¹) d = ρ := by
    ext1 s
    apply Units.ext
    rw [tw_val, tw_val, smul_smul, MonoidHom.inv_apply, Units.mul_inv, one_smul]
  rwa [e] at h
