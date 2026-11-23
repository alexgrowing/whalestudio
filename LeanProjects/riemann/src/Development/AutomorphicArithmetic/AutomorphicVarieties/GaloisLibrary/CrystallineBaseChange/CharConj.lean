import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.CqStmt

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.HeckeGal UpperTheory.V UpperTheory.V.Af
open GlobalTheory.CuspRep (Af finId pFin)
open ReciprocityTheory.Neutral.Bridge.HCFR (infIdele)

section

variable {F : Type} [Field F] [NumberField F]

private theorem cc_finId_local (w : HeightOneSpectrum (𝓞 F)) (x : (w.adicCompletion F)ˣ) :
    finId F (Units.map (pFin F).toMonoidHom (localIdele F w x)) = localIdele F w x := by
  refine Units.ext (Prod.ext ?_ ?_)
  · change (1 : InfiniteAdeleRing F) - 0 + 0 = 1
    simp
  · change (1 : Af F) - 1 + _ = _
    rw [sub_self, zero_add]
    rfl

private theorem cc_pFin_inf (v : InfinitePlace F) (x : (v.Completion)ˣ) :
    Units.map (pFin F).toMonoidHom (infIdele F v x) = 1 := Units.ext rfl

private theorem cc_split (k : Fˣ) :
    infDiag k * finId F (Units.map (algebraMap F (Af F)).toMonoidHom k) = diagUnits F k := by
  classical
  have h : ((infDiag k : Ideles F) : AdeleRing (𝓞 F) F) = (algebraMap F (InfiniteAdeleRing F) k, 1) := by
    unfold infDiag
    rw [MonoidHom.finsetProd_apply, Units.coe_prod]
    let ι : (∀ w : InfinitePlace F, w.Completion) →* AdeleRing (𝓞 F) F :=
      MonoidHom.inl (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)
    change ∏ w : InfinitePlace F, ι (Pi.mulSingle w (algebraMap F w.Completion k)) =
      ι (fun w => algebraMap F w.Completion k)
    rw [← map_prod, Finset.univ_prod_mulSingle]
  apply Units.ext
  rw [Units.val_mul, h]
  refine Prod.ext ?_ ?_
  · change algebraMap F (InfiniteAdeleRing F) k * (1 - 0 + 0) = algebraMap F (InfiniteAdeleRing F) k
    simp
  · change (1 : Af F) * (1 - 1 + algebraMap F (Af F) k) = algebraMap F (Af F) k
    simp

private theorem cc_inf_fixed (hF : Module.finrank ℚ F = 1) (χ : HChar F) (a : (F →+* ℂ) → ℤ) (h : IsAlgPos χ a)
    (σ : ℂ ≃+* ℂ) (k : Fˣ) : σ ((χ.inf k : ℂˣ) : ℂ) = ((χ.inf k : ℂˣ) : ℂ) := by
  have hs : Function.Surjective (algebraMap ℚ F) := (Algebra.finrank_eq_one_iff_bijective_algebraMap.1 hF).2
  obtain ⟨q, hq⟩ := hs (k : F)
  have h1 := h (k ^ 2) fun φ => by
    rw [Units.val_pow_eq_pow_val, map_pow]
    exact pow_two_pos_of_ne_zero ((map_ne_zero φ).2 k.ne_zero)
  have h2 : ((χ.inf k : ℂˣ) : ℂ) ^ 2 = (∏ φ : F →+* ℂ, (q : ℂ) ^ a φ) ^ 2 := by
    rw [← Units.val_pow_eq_pow_val, ← map_pow, h1, ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun φ _ => ?_
    rw [Units.val_pow_eq_pow_val, map_pow, ← hq, eq_ratCast, map_ratCast, ← zpow_natCast, ← zpow_natCast,
      ← zpow_mul, ← zpow_mul, mul_comm]
  have h3 : σ (∏ φ : F →+* ℂ, (q : ℂ) ^ a φ) = ∏ φ : F →+* ℂ, (q : ℂ) ^ a φ := by
    simp only [map_prod, map_zpow₀, map_ratCast]
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 h2 with e | e
  · rw [e, h3]
  · rw [e, map_neg, h3]

end

theorem UpperTheory.V.Br.charConj :
    UpperTheory.V.Br.CharConj := by
  intro F _ _ hF χ a ha σ
  have hσ : ∀ k : Fˣ, σ ((χ.1 (finId F (Units.map (algebraMap F (Af F)).toMonoidHom k)) : ℂˣ) : ℂ) =
      ((χ.1 (finId F (Units.map (algebraMap F (Af F)).toMonoidHom k)) : ℂˣ) : ℂ) := fun k => by
    have h1 := χ.2.2 k
    rw [← cc_split k, map_mul] at h1
    have h2 : χ.1 (finId F (Units.map (algebraMap F (Af F)).toMonoidHom k)) = (χ.inf k)⁻¹ :=
      eq_inv_of_mul_eq_one_right h1
    rw [h2, Units.val_inv_eq_inv_val, map_inv₀, cc_inf_fixed hF χ a ha σ k]
  let ψ : (Af F)ˣ →* ℂˣ := χ.1.comp (finId F)
  have hψ : Continuous ψ := χ.2.1.comp (GlobalTheory.CuspRep.continuous_finId F)
  let ψ' : (Af F)ˣ →* ℂˣ := (Units.map (σ : ℂ →+* ℂ).toMonoidHom).comp ψ
  have hψ' : Continuous ψ' := by
    refine continuous_of_continuousAt_one ψ' ?_
    have h1 : {u | ψ u = 1} ∈ nhds (1 : (Af F)ˣ) :=
      (GlobalTheory.CuspRep.isOpen_ker_finIdele F ψ hψ).mem_nhds (map_one ψ)
    refine (continuousAt_const (y := (1 : ℂˣ))).congr ?_
    filter_upwards [h1] with u hu
    change 1 = Units.map _ (ψ u)
    rw [hu, map_one]
  let p := Units.map (pFin F).toMonoidHom
  have hp : Continuous p := Continuous.units_map _ continuous_snd
  let χ' : HChar F := ⟨χ.1 * (ψ.comp p)⁻¹ * ψ'.comp p, (χ.2.1.mul (hψ.comp hp).inv).mul (hψ'.comp hp), fun k => by
    have e : ψ' (Units.map (algebraMap F (Af F)).toMonoidHom k) = ψ (Units.map (algebraMap F (Af F)).toMonoidHom k) :=
      Units.ext (hσ k)
    change χ.1 _ * (ψ (Units.map (algebraMap F (Af F)).toMonoidHom k))⁻¹ *
      ψ' (Units.map (algebraMap F (Af F)).toMonoidHom k) = 1
    rw [χ.2.2 k, e, one_mul, inv_mul_cancel]⟩
  have hloc : ∀ w x, χ'.loc w x = Units.map (σ : ℂ →+* ℂ).toMonoidHom (χ.loc w x) := fun w x => by
    have e := cc_finId_local w x
    change χ.1 (localIdele F w x) * (χ.1 (finId F (Units.map (pFin F).toMonoidHom (localIdele F w x))))⁻¹ *
      Units.map (σ : ℂ →+* ℂ).toMonoidHom (χ.1 (finId F (Units.map (pFin F).toMonoidHom (localIdele F w x)))) = _
    rw [e, mul_inv_cancel, one_mul]
    rfl
  refine ⟨χ', fun v => ?_, fun w hw => ⟨fun x hx => ?_, ?_⟩⟩
  · change χ.1 (infIdele F v (-1)) * (ψ (Units.map (pFin F).toMonoidHom (infIdele F v (-1))))⁻¹ *
      ψ' (Units.map (pFin F).toMonoidHom (infIdele F v (-1))) = χ.1 (infIdele F v (-1))
    rw [cc_pFin_inf, map_one, map_one, inv_one, mul_one, mul_one]
  · rw [hloc, hw x hx, map_one]
  · exact congrArg Units.val (hloc w (atFin w (unif w)))
