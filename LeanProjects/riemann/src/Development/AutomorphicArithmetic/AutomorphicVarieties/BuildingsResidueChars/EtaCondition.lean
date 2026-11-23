import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.GuDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.ExtReal
open UpperTheory.V.Af UpperTheory.V.Af.Gu
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host GlobalTheory.GalOfCusp

private theorem eta_val (L : Type) [Field L] [NumberField L] (k : Lˣ) :
    ((infDiag k : Ideles L) : AdeleRing (𝓞 L) L) = (algebraMap L (InfiniteAdeleRing L) k, 1) := by
  classical
  unfold infDiag
  rw [MonoidHom.finsetProd_apply, Units.coe_prod]
  let ι : (∀ w : InfinitePlace L, w.Completion) →* AdeleRing (𝓞 L) L :=
    MonoidHom.inl (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L)
  change ∏ w : InfinitePlace L, ι (Pi.mulSingle w (algebraMap L w.Completion k)) =
    ι (fun w => algebraMap L w.Completion k)
  rw [← map_prod, Finset.univ_prod_mulSingle]

private theorem eta_map (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] (x : Kˣ) :
    GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap K L (infDiag x) = infDiag (Units.map (algebraMap K L).toMonoidHom x) := by
  apply Units.ext
  change GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.adeleMap K L ((infDiag x : Ideles K) : AdeleRing (𝓞 K) K) = _
  rw [eta_val, eta_val]
  refine Prod.ext ?_ ?_
  · have h := congrArg Prod.fst (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.adeleMap_algebraMap K L (x : K))
    exact h
  · exact map_one (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.finiteAdeleMap K L)

private theorem eta_loc {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (χ : HChar F) (h2 : ∀ x, χ.1 x ^ 2 = 1)
    (v : InfinitePlace F) (hs : χ.locInf v (-1) = -1) (k : Fˣ) :
    ((χ.locInf v (atInf v k) : ℂˣ) : ℂ) * ((‖v.embedding (k : F)‖ : ℝ) : ℂ) = v.embedding (k : F) := by
  have hv : v.IsReal := IsTotallyReal.isReal v
  let e := InfinitePlace.Completion.ringEquivRealOfIsReal hv
  have he : e (algebraMap _ v.Completion (k : F)) = InfinitePlace.embedding_of_isReal hv k :=
    InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe hv ((WithAbs.equiv v.1).symm (k : F))
  have hsq : ∀ x : (v.Completion)ˣ, 0 < e x → χ.locInf v x = 1 := fun x hx => by
    have h0 : e.symm (Real.sqrt (e x)) ≠ 0 := by
      rw [map_ne_zero]
      exact (Real.sqrt_pos.2 hx).ne'
    have e1 : x = Units.mk0 _ h0 ^ 2 := Units.ext (e.injective (by
      rw [Units.val_pow_eq_pow_val, map_pow, Units.val_mk0, e.apply_symm_apply, Real.sq_sqrt hx.le]))
    rw [e1, map_pow]
    exact h2 _
  have h0 : InfinitePlace.embedding_of_isReal hv k ≠ 0 := (map_ne_zero _).2 k.ne_zero
  rw [← InfinitePlace.embedding_of_isReal_apply hv, Complex.norm_real, Real.norm_eq_abs]
  rcases lt_or_gt_of_ne h0 with h | h
  · have e1 : atInf v k = -1 * -atInf v k := by simp
    rw [e1, map_mul, hs, hsq _ (by
      rw [Units.val_neg, map_neg]
      exact neg_pos.2 (he ▸ h)), abs_of_neg h]
    simp
  · rw [hsq _ (he ▸ h), abs_of_pos h]
    simp

private theorem eta_inf {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (χ : HChar F) (h2 : ∀ x, χ.1 x ^ 2 = 1)
    (hs : ∀ v, χ.locInf v (-1) = -1) (k : Fˣ) :
    ((χ.inf k : ℂˣ) : ℂ) * ((‖∏ φ : F →+* ℂ, φ (k : F)‖ : ℝ) : ℂ) = ∏ φ : F →+* ℂ, φ (k : F) := by
  have hb : Function.Bijective fun v : InfinitePlace F => v.embedding :=
    ⟨InfinitePlace.embedding_injective F, fun φ =>
      ⟨InfinitePlace.mk φ, InfinitePlace.embedding_mk_eq_of_isReal (IsTotallyReal.complexEmbedding_isReal φ)⟩⟩
  have e1 : χ.inf k = ∏ v : InfinitePlace F, χ.locInf v (atInf v k) := by
    unfold HChar.inf HChar.locInf infDiag
    rw [MonoidHom.comp_apply, MonoidHom.finsetProd_apply, map_prod]
    rfl
  rw [← hb.prod_comp fun φ => φ (k : F), e1, Units.coe_prod, norm_prod, Complex.ofReal_prod, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun v _ => eta_loc χ h2 v (hs v) k

private theorem eta_norm (E : Type) [Field E] [NumberField E] (k : E) :
    ∏ φ : E →+* ℂ, φ k = ((Algebra.norm ℚ k : ℚ) : ℂ) := by
  have h := Algebra.norm_eq_prod_embeddings ℚ ℂ k
  rw [← Fintype.prod_equiv (RingHom.equivRatAlgHom E ℂ) (fun φ : E →+* ℂ => φ k)
    (fun σ : E →ₐ[ℚ] ℂ => σ k) (fun _ => rfl)] at h
  rw [← h]; simp

private theorem eta_abs (E : Type) [Field E] [NumberField E] [IsCMField E] (f : ℤ) (k : (maximalRealSubfield E)ˣ) :
    (((GlobalTheory.HeightCounting.Blocks.resReal (GlobalTheory.HeckeGal.Model.absPow E ((f : ℝ) / 2))).inf k : ℂˣ) : ℂ) =
      ((‖∏ φ : maximalRealSubfield E →+* ℂ, φ (k : maximalRealSubfield E)‖ : ℝ) : ℂ) ^ f := by
  have e1 : (GlobalTheory.HeightCounting.Blocks.resReal (GlobalTheory.HeckeGal.Model.absPow E ((f : ℝ) / 2))).inf k =
      (GlobalTheory.HeckeGal.Model.absPow E ((f : ℝ) / 2)).inf (Units.map (algebraMap (maximalRealSubfield E) E).toMonoidHom k) :=
    congrArg (GlobalTheory.HeckeGal.Model.absPow E ((f : ℝ) / 2)).1 (eta_map _ E k)
  rw [e1, (GlobalTheory.HeckeGal.Model.absPow_isAbsPow E _).2.2]
  simp only [← Complex.ofReal_cpow (norm_nonneg _)]
  rw [← Complex.ofReal_prod, Real.finsetProd_rpow _ _ fun _ _ => norm_nonneg _, ← norm_prod, eta_norm, eta_norm]
  have e2 : Algebra.norm ℚ ((Units.map (algebraMap (maximalRealSubfield E) E).toMonoidHom k : Eˣ) : E) =
      Algebra.norm ℚ (k : maximalRealSubfield E) ^ 2 := by
    change Algebra.norm ℚ (algebraMap (maximalRealSubfield E) E k) = _
    rw [← Algebra.norm_norm (S := maximalRealSubfield E), Algebra.norm_algebraMap, Algebra.IsQuadraticExtension.finrank_eq_two,
      map_pow]
  rw [e2, Rat.cast_pow, norm_pow, ← Complex.ofReal_zpow, ← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _),
    ← Real.rpow_intCast]
  congr 2
  push_cast
  ring

theorem UpperTheory.eta_condition :
    Eta := by
  intro E _ _ _ f
  have hq : ∀ x, (quadChar E).1 x ^ 2 = 1 := fun x => by
    change (Units.map (Int.castRingHom ℂ).toMonoidHom (GlobalTheory.IdeleNormChar.normSign E x)) ^ 2 = 1
    rw [← map_pow, Int.units_sq, map_one]
  obtain ⟨ξ, m, hm, hξ⟩ := Cq.extReal E
    (GlobalTheory.HeightCounting.Blocks.resReal (GlobalTheory.HeckeGal.Model.absPow E ((f : ℝ) / 2)) * quadChar E ^ f)⁻¹ (-f) fun k => by
      have e : (quadChar E ^ f).inf k = (quadChar E).inf k ^ f := rfl
      rw [HChar.inf_inv, HChar.inf_mul, Units.val_inv_eq_inv_val, Units.val_mul, eta_abs, e, Units.val_zpow_eq_zpow_val,
        ← mul_zpow, mul_comm, eta_inf _ hq (quadChar_locInf E), Finset.prod_zpow, zpow_neg]
  refine ⟨ξ, m, hm, ?_⟩
  have e : GlobalTheory.HeightCounting.Blocks.resReal (GlobalTheory.HeckeGal.Model.absPow E ((f : ℝ) / 2) * ξ) =
      GlobalTheory.HeightCounting.Blocks.resReal (GlobalTheory.HeckeGal.Model.absPow E ((f : ℝ) / 2)) * GlobalTheory.HeightCounting.Blocks.resReal ξ := rfl
  rw [e, hξ, mul_inv, mul_inv_cancel_left, map_inv, map_zpow, compNorm_quadChar, one_zpow, inv_one]
