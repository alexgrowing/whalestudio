import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.IsTanZero
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.FinDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.LemmaL

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial Matrix UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Eb GlobalTheory.GalOfCusp

private theorem UpperTheory.V.Ws.Eb.residue_dual {K : Type} [Field K] (x : DualNumber K) :
    residue (DualNumber K) x = ((residue (DualNumber K)).comp (algebraMap K (DualNumber K))) (dF K x) := by
  rw [RingHom.comp_apply, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
  have e : x - algebraMap K (DualNumber K) (dF K x) = TrivSqZeroExt.inr x.snd := by
    ext <;> simp [dF, TrivSqZeroExt.algebraMap_eq_inl]
  rw [e, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, TrivSqZeroExt.isUnit_iff_isUnit_fst]
  simp

private theorem UpperTheory.V.Ws.Eb.charpoly_lift {A K H : Type} [CommRing A] [CommRing K] [Group H] {n : ℕ} (f : A →+* K)
    (r : H →* GL (Fin n) A) (κ : Fin n → H →* Aˣ) (h : W.HasFlag (W.pushRep f r) fun i => W.pushCh f (κ i))
    (z : MonoidAlgebra A H) :
    (MonoidAlgebra.lift A (Matrix (Fin n) (Fin n) A) H ((Units.coeHom _).comp r) z).charpoly.map f =
      ∏ i, (X - C (f (MonoidAlgebra.lift A A H ((Units.coeHom _).comp (κ i)) z))) := by
  unfold W.HasFlag W.pushRep W.pushCh at h
  obtain ⟨g, hg⟩ := h
  have key : ∀ y : MonoidAlgebra A H,
      (∀ i j : Fin n, j < i → ((g : Matrix (Fin n) (Fin n) K) * f.mapMatrix (MonoidAlgebra.lift A (Matrix (Fin n) (Fin n) A) H ((Units.coeHom _).comp r) y) * ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) i j = 0) ∧
      ∀ i, ((g : Matrix (Fin n) (Fin n) K) * f.mapMatrix (MonoidAlgebra.lift A (Matrix (Fin n) (Fin n) A) H ((Units.coeHom _).comp r) y) * ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) i i = f (MonoidAlgebra.lift A A H ((Units.coeHom _).comp (κ i)) y) := by
    intro y
    induction y using MonoidAlgebra.induction_linear with
    | zero => simp
    | add x y hx hy =>
      simp only [map_add, mul_add, add_mul, Matrix.add_apply]
      exact ⟨fun i j hij => by rw [hx.1 i j hij, hy.1 i j hij, add_zero], fun i => by rw [hx.2, hy.2]⟩
    | single s a =>
      have e : (g : Matrix (Fin n) (Fin n) K) * f.mapMatrix (MonoidAlgebra.lift A (Matrix (Fin n) (Fin n) A) H ((Units.coeHom _).comp r) (MonoidAlgebra.single s a)) * ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = f a • ((g * ((GeneralLinearGroup.map f).comp r) s * g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
        rw [MonoidAlgebra.lift_single]
        have e' : f.mapMatrix (a • ((r s : GL (Fin n) A) : Matrix (Fin n) (Fin n) A)) = f a • ((GeneralLinearGroup.map f (r s) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
          ext i j
          simp [GeneralLinearGroup.map]
        simp only [MonoidHom.comp_apply, Units.coeHom_apply, e', Units.val_mul, Matrix.mul_smul, Matrix.smul_mul]
      rw [e]
      refine ⟨fun i j hij => ?_, fun i => ?_⟩
      · rw [Matrix.smul_apply, (hg s).1 i j hij, smul_zero]
      · rw [Matrix.smul_apply, (hg s).2 i]
        simp [MonoidAlgebra.lift_single]
  rw [← Matrix.charpoly_map, ← Matrix.charpoly_units_conj g, ← Matrix.coe_units_inv]
  simp only [← RingHom.mapMatrix_apply]
  rw [Matrix.charpoly_of_isUpperTriangular _ (fun i j hij => (key z).1 i j hij)]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [(key z).2 i]

theorem UpperTheory.V.Ws.Eb.flagDual :
    ∀ {K H : Type} [Field K] [Infinite K] [Group H] {n : ℕ} (ρ' : H →* GL (Fin n) (DualNumber K)) (κ : Fin n → H →* (DualNumber K)ˣ), (Function.Injective fun i => W.pushCh (dF K) (κ i)) →
        W.HasFlag (W.pushRep (dF K) ρ') (fun i => W.pushCh (dF K) (κ i)) → (∀ g : Fin n → H, (List.ofFn fun i => W.mat ρ' (g i) - algebraMap (DualNumber K) _ (κ i (g i) : DualNumber K)).prod = 0) → W.HasFlag ρ' κ := by
  intro K H _ _ _ n ρ' κ hinj hflag hprod
  set φ : K →+* ResidueField (DualNumber K) := (residue (DualNumber K)).comp (algebraMap K (DualNumber K)) with hφ
  have hres : residue (DualNumber K) = φ.comp (dF K) := RingHom.ext fun x => UpperTheory.V.Ws.Eb.residue_dual x
  have hcard : (n : Cardinal) ≤ Cardinal.mk (ResidueField (DualNumber K)) := by
    haveI : Infinite (ResidueField (DualNumber K)) := Infinite.of_injective φ φ.injective
    exact (Cardinal.nat_lt_aleph0 n).le.trans (Cardinal.infinite_iff.mp inferInstance)
  have hinj' : Function.Injective fun i => ((residue (DualNumber K) : DualNumber K →* ResidueField (DualNumber K))).comp ((Units.coeHom (DualNumber K)).comp (κ i)) := by
    intro i j hij
    apply hinj
    ext s
    have hs := DFunLike.congr_fun hij s
    simp only [MonoidHom.comp_apply, Units.coeHom_apply, MonoidHom.coe_coe] at hs
    rw [hres, RingHom.comp_apply, RingHom.comp_apply] at hs
    have := φ.injective hs
    simpa [W.pushCh] using this
  have hchar : ∀ z : MonoidAlgebra (DualNumber K) H,
      Polynomial.map (residue (DualNumber K))
          ((MonoidAlgebra.lift (DualNumber K) (Matrix (Fin n) (Fin n) (DualNumber K)) H ((Units.coeHom _).comp ρ')) z).charpoly =
        ∏ i, (X - C ((residue (DualNumber K)) ((MonoidAlgebra.lift (DualNumber K) (DualNumber K) H ((Units.coeHom _).comp (κ i))) z))) := by
    intro z
    rw [hres, ← Polynomial.map_map, UpperTheory.V.Ws.Eb.charpoly_lift (dF K) ρ' κ hflag z, Polynomial.map_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, RingHom.comp_apply]
    rfl
  obtain ⟨z, g, -, -, hg⟩ := AlgebraTools.lemma_L ρ' κ hcard hprod hinj' hchar
  unfold W.HasFlag
  exact ⟨g, hg⟩
