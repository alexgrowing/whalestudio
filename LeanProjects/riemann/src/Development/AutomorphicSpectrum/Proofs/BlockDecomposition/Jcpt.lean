import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.SiegelOneDescent.Descend2

open PositivityTheory.RgEis PositivityTheory.RgEis.So

namespace GlobalTheory.CompanionTheory.RgEisSo

theorem jcpt : StdGood → GrpTop → JTop → JCpt := by
  intro hS hG hT F E R _ _ _ _ _ _ _ _ _ _ A ε ν r δ α ω ι _ _ i j hGood hB hi hJ
  show IsCompact (cK α j : Set (cover A ν ι))
  have hj : Continuous j := (hT F E R A ε ν r δ α ω ι i j hGood hB hi hJ).1
  obtain ⟨-, -, -, hUT2, -, -, hUK⟩ := hG E R A hGood ι ε
  have hν : Continuous ν := hB.cont

  have hmapν : Continuous (Matrix.GeneralLinearGroup.map (n := ι ⊕ ι) ν) := by
    refine Continuous.units_map _ ?_
    exact Continuous.matrix_map continuous_id hν
  let D : GL (ι ⊕ ι) R := dg ι (Units.map A.i.toMonoidHom δ)
  let M : GL (ι ⊕ ι) (NumberField.AdeleRing (NumberField.RingOfIntegers F) F) → GL (ι ⊕ ι) R :=
    fun h => D⁻¹ * Matrix.GeneralLinearGroup.map ν h * D
  have hM : Continuous M := (continuous_const.mul hmapν).mul continuous_const
  let φ : A.U ε ι × GL (ι ⊕ ι) (NumberField.AdeleRing (NumberField.RingOfIntegers F) F) → R :=
    fun p => ((p.1.1 * (M p.2)⁻¹ : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R) (Sum.inl i) (Sum.inl i)
  let ψ : A.U ε ι × GL (ι ⊕ ι) (NumberField.AdeleRing (NumberField.RingOfIntegers F) F) → R :=
    fun p => ((M p.2 * (p.1.1)⁻¹ : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R) (Sum.inl i) (Sum.inl i)
  have hval : Continuous (Subtype.val : A.U ε ι → GL (ι ⊕ ι) R) := continuous_subtype_val
  have hφ : Continuous φ := by
    have : Continuous fun p : A.U ε ι × GL (ι ⊕ ι) (NumberField.AdeleRing (NumberField.RingOfIntegers F) F) =>
        (p.1.1 * (M p.2)⁻¹ : GL (ι ⊕ ι) R) :=
      (hval.comp continuous_fst).mul (hM.comp continuous_snd).inv
    exact (Units.continuous_val.comp this).matrix_elem _ _
  have hψ : Continuous ψ := by
    have : Continuous fun p : A.U ε ι × GL (ι ⊕ ι) (NumberField.AdeleRing (NumberField.RingOfIntegers F) F) =>
        (M p.2 * (p.1.1)⁻¹ : GL (ι ⊕ ι) R) :=
      (hM.comp continuous_snd).mul (hval.comp continuous_fst).inv
    exact (Units.continuous_val.comp this).matrix_elem _ _

  have hrel : ∀ x : cover A ν ι, ((j x).1 : Matrix (ι ⊕ ι) (ι ⊕ ι) R) = (x.1.1 : R) • (M x.1.2 : Matrix (ι ⊕ ι) (ι ⊕ ι) R) :=
    fun x => hJ x
  have hφv : ∀ x : cover A ν ι, φ (j x, x.1.2) = (x.1.1 : R) := by
    intro x
    have e : (((j x).1 * (M x.1.2)⁻¹ : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R) = (x.1.1 : R) • 1 := by
      rw [Units.val_mul, hrel x, Matrix.smul_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one]
    show (((j x).1 * (M x.1.2)⁻¹ : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R) (Sum.inl i) (Sum.inl i) = _
    rw [e]; simp
  have hψv : ∀ x : cover A ν ι, ψ (j x, x.1.2) = ((x.1.1⁻¹ : Rˣ) : R) := by
    intro x
    have e0 : (x.1.1 : R) • ((M x.1.2 * ((j x).1)⁻¹ : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R) = 1 := by
      rw [Units.val_mul, ← Matrix.smul_mul, ← hrel x, ← Units.val_mul, mul_inv_cancel, Units.val_one]
    have e : ((M x.1.2 * ((j x).1)⁻¹ : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R) = ((x.1.1⁻¹ : Rˣ) : R) • 1 := by
      rw [← e0, smul_smul, Units.inv_mul, one_smul]
    show ((M x.1.2 * ((j x).1)⁻¹ : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R) (Sum.inl i) (Sum.inl i) = _
    rw [e]; simp

  let C₂ : Set (GL (ι ⊕ ι) (NumberField.AdeleRing (NumberField.RingOfIntegers F) F)) :=
    ((((adStd F).kGL (ι ⊕ ι)).map (MulAut.conj (dg ι α)).toMonoidHom : Subgroup _) : Set _)
  have hC₂ : IsCompact C₂ := by
    have h0 := ((hS F).kcpt (ι ⊕ ι)).image
      (f := fun k => (MulAut.conj (dg ι α)).toMonoidHom k)
      (by
        show Continuous fun k => dg ι α * k * (dg ι α)⁻¹
        exact (continuous_const.mul continuous_id).mul continuous_const)
    exact h0
  let C₁ : Set (A.U ε ι) := (A.uK ε ι : Set (A.U ε ι))
  have hC : IsCompact (C₁ ×ˢ C₂) := hUK.prod hC₂
  have hS₁ := hC.image hφ
  have hS₂ : IsCompact (MulOpposite.op '' (ψ '' (C₁ ×ˢ C₂))) := (hC.image hψ).image MulOpposite.continuous_op
  let B : Set Rˣ := Units.embedProduct R ⁻¹' ((φ '' (C₁ ×ˢ C₂)) ×ˢ (MulOpposite.op '' (ψ '' (C₁ ×ˢ C₂))))
  have hBc : IsCompact B := Units.isClosedEmbedding_embedProduct.isCompact_preimage (hS₁.prod hS₂)

  have hdet : Continuous (Matrix.GeneralLinearGroup.det (n := ι ⊕ ι) (R := NumberField.AdeleRing (NumberField.RingOfIntegers F) F)) := by
    refine Units.continuous_iff.2 ⟨?_, ?_⟩
    · show Continuous fun g : GL (ι ⊕ ι) (NumberField.AdeleRing (NumberField.RingOfIntegers F) F) =>
        (g : Matrix (ι ⊕ ι) (ι ⊕ ι) (NumberField.AdeleRing (NumberField.RingOfIntegers F) F)).det
      exact Continuous.matrix_det Units.continuous_val
    · show Continuous fun g : GL (ι ⊕ ι) (NumberField.AdeleRing (NumberField.RingOfIntegers F) F) =>
        ((g⁻¹ : GL (ι ⊕ ι) (NumberField.AdeleRing (NumberField.RingOfIntegers F) F)) :
          Matrix (ι ⊕ ι) (ι ⊕ ι) (NumberField.AdeleRing (NumberField.RingOfIntegers F) F)).det
      exact Continuous.matrix_det (Units.continuous_val.comp continuous_inv)
  have hσ : Continuous A.σ := hGood.σcont
  have hUσ : Continuous (Units.map A.σ.toMonoidHom) := Continuous.units_map _ hσ
  have hUν : Continuous (Units.map ν.toMonoidHom) := Continuous.units_map _ hν
  have hcl : IsClosed ((cover A ν ι : Subgroup _) : Set (Rˣ × GL (ι ⊕ ι) (NumberField.AdeleRing (NumberField.RingOfIntegers F) F))) := by
    have hf : Continuous fun p : Rˣ × GL (ι ⊕ ι) (NumberField.AdeleRing (NumberField.RingOfIntegers F) F) =>
        p.1 * Units.map A.σ.toMonoidHom p.1 * Units.map ν.toMonoidHom (Matrix.GeneralLinearGroup.det p.2) :=
      (continuous_fst.mul (hUσ.comp continuous_fst)).mul (hUν.comp (hdet.comp continuous_snd))
    exact isClosed_singleton.preimage hf
  have hemb := hcl.isClosedEmbedding_subtypeVal
  have hP : IsCompact ((Subtype.val : cover A ν ι → _) ⁻¹' (B ×ˢ C₂)) :=
    hemb.isCompact_preimage (hBc.prod hC₂)
  have hprj : Continuous (prj A ν ι) := continuous_snd.comp continuous_subtype_val
  have hclK : IsClosed (cK α j : Set (cover A ν ι)) :=
    (hUK.isClosed.preimage hj).inter (hC₂.isClosed.preimage hprj)
  refine hP.of_isClosed_subset hclK ?_
  intro x hx
  have h1 : j x ∈ C₁ := hx.1
  have h2 : x.1.2 ∈ C₂ := hx.2
  refine ⟨?_, h2⟩
  refine ⟨⟨(j x, x.1.2), ⟨h1, h2⟩, hφv x⟩, ⟨ψ (j x, x.1.2), ⟨(j x, x.1.2), ⟨h1, h2⟩, rfl⟩, ?_⟩⟩
  rw [hψv x]
  rfl

end GlobalTheory.CompanionTheory.RgEisSo
