import Development.AutomorphicArithmetic.CommutativeAlgebra.PicData
open CategoryTheory TensorProduct UpperTheory.PicD

private theorem UpperTheory.PicD.Data.Triv.mapAlg (P : Data) {A : Type} [CommRing A]
    {z : P.S1.obj (CommRingCat.of A)} {M : Type} [AddCommGroup M] [Module A M]
    {C E : Type} [CommRing C] [Algebra A C] [CommRing E] [Algebra A E]
    {w : P.S0.obj (CommRingCat.of C)} {g : (C ⊗[A] C)ˣ} {t : M →ₗ[A] C}
    (h : P.Triv z M C w g t) (f : C →ₐ[A] E) :
    P.Triv z M E (P.r0 f.toRingHom w)
      (Units.map (Algebra.TensorProduct.map f f).toRingHom.toMonoidHom g) (f.toLinearMap ∘ₗ t) := by
  have e0 : f.toRingHom.comp (algebraMap A C) = algebraMap A E := f.comp_algebraMap
  have e1 : (Algebra.TensorProduct.map f f).toRingHom.comp (i1 A C).toRingHom
      = (i1 A E).toRingHom.comp f.toRingHom := by
    ext x <;> simp
  have e2 : (Algebra.TensorProduct.map f f).toRingHom.comp (i2 A C).toRingHom
      = (i2 A E).toRingHom.comp f.toRingHom := by
    ext x <;> simp
  have key : ∀ (c : C) (x : C ⊗[A] C), Algebra.TensorProduct.map f f (c • x)
      = f c • Algebra.TensorProduct.map f f x := by
    intro c x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [TensorProduct.smul_tmul']
    | add a b ha hb => simp [smul_add, ha, hb]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [P.diff_mapDegZero, h.dw, P.mapDegOne_comp, e0]
  · rw [← P.mapDegZero_ofUnit, h.hg, map_sub, P.mapDegZero_comp, P.mapDegZero_comp, P.mapDegZero_comp, P.mapDegZero_comp, e1, e2]
  · intro m
    have := congrArg (Algebra.TensorProduct.map f f) (h.ht m)
    rw [key] at this
    simpa using this
  · letI : Algebra C E := f.toRingHom.toAlgebra
    haveI : IsScalarTower A C E := IsScalarTower.of_algebraMap_eq' e0.symm
    have hb1 : IsBaseChange C t :=
      IsBaseChange.of_equiv (LinearEquiv.ofBijective _ h.bij) (fun x => by simp)
    have hb2 := hb1.comp (IsBaseChange.linearMap C E)
    have : LinearMap.liftBaseChange E (f.toLinearMap ∘ₗ t) = hb2.equiv.toLinearMap := by
      ext m
      simp [IsBaseChange.equiv_tmul]
      rfl
    rw [this]
    exact hb2.equiv.bijective

theorem UpperTheory.exists_etale_trivialization_of_two_invertibleModuleTorsors :
    ∀ (P : Data) (A : Type) [CommRing A] (z z' : P.S1.obj (CommRingCat.of A)) (M M' : Type) [AddCommGroup M] [Module A M]
        [AddCommGroup M'] [Module A M'], P.Rel z M → P.Rel z' M' →
        ∃ (C : Type) (_ : CommRing C) (_ : Algebra A C), Module.FaithfullyFlat A C ∧ Algebra.Etale A C ∧
          ∃ (w : P.S0.obj (CommRingCat.of C)) (g : (C ⊗[A] C)ˣ) (t : M →ₗ[A] C)
            (w' : P.S0.obj (CommRingCat.of C)) (g' : (C ⊗[A] C)ˣ) (t' : M' →ₗ[A] C),
            P.Triv z M C w g t ∧ P.Triv z' M' C w' g' t' := by
  intro P A _ z z' M M' _ _ _ _ hM hM'
  obtain ⟨C, _, _, hf, he, w, g, t, h⟩ := hM
  obtain ⟨C', _, _, hf', he', w', g', t', h'⟩ := hM'
  exact ⟨C ⊗[A] C', inferInstance, inferInstance, Module.FaithfullyFlat.trans A C _,
    Algebra.Etale.comp A C _, _, _, _, _, _, _,
    UpperTheory.PicD.Data.Triv.mapAlg P h Algebra.TensorProduct.includeLeft,
    UpperTheory.PicD.Data.Triv.mapAlg P h' Algebra.TensorProduct.includeRight⟩
