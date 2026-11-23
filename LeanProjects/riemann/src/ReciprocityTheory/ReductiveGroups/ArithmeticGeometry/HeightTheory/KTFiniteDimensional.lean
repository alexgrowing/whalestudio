import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HtDefs
import ReciprocityTheory.SemistableReduction.AlgAll

namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

theorem KTtoS_fieldRange (h : d.S1) (c : ι) :
    (d.KTtoS h c).fieldRange = (d.KT c).toSubfield := by
  have hval : ∀ p : (KTp K d.D d.N), d.KTtoS h c (algebraMap (KTp K d.D d.N) (KTf K d.D d.N) p) =
      MvPolynomial.aeval (sImg (d.jc c) (d.x c)) p := by
    intro p
    simp only [KTtoS]
    rw [IsFractionRing.lift_algebraMap]
    rfl
  apply le_antisymm
  · rintro _ ⟨z, rfl⟩
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := (KTp K d.D d.N)) z
    have hmem : ∀ p : (KTp K d.D d.N), d.KTtoS h c (algebraMap (KTp K d.D d.N) (KTf K d.D d.N) p) ∈ (d.KT c).toSubfield := by
      intro p
      rw [hval]
      show _ ∈ IntermediateField.adjoin K (Set.range (sImg (d.jc c) (d.x c)))
      apply IntermediateField.algebra_adjoin_le_adjoin
      rw [Algebra.adjoin_range_eq_range_aeval]
      exact ⟨p, rfl⟩
    rw [map_div₀]
    exact (d.KT c).toSubfield.div_mem (hmem a) (hmem b)
  · intro y hy
    have hE : IntermediateField.adjoin K (Set.range (sImg (d.jc c) (d.x c))) ≤
        { (d.KTtoS h c).fieldRange with
          algebraMap_mem' := fun k => (d.KTtoS h c).mem_fieldRange.2
            ⟨algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (MvPolynomial.C k), by rw [hval, MvPolynomial.aeval_C]⟩ } := by
      rw [IntermediateField.adjoin_le_iff]
      rintro _ ⟨v, rfl⟩
      exact (d.KTtoS h c).mem_fieldRange.2
        ⟨algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (MvPolynomial.X v), by rw [hval, MvPolynomial.aeval_X]⟩
    exact hE hy

theorem KT_finiteDimensional (hd : d.AxH 𝒜) (c : ι) :
    FiniteDimensional (d.KT c) (OmS (Ω c) d.D d.N) := by
  have hfs := ReciprocityTheory.MultiplicativeHeights.Closed.fieldOfS K (Ω c) d.D d.N (d.x c) (hd.fg c) (hd.trdeg c) (hd.a1 c)
  let e : TVar d.D d.N ≃ TVar d.D d.N :=
    Equiv.prodCongr (Equiv.refl _) (Fin.cycleRange (d.jc c)).symm
  have key : (ReciprocityTheory.MultiplicativeHeights.sImage (D := d.D) (d.x c)) = (sImg (D := d.D) (d.jc c) (d.x c)) ∘ e := by
    funext p
    obtain ⟨i, j⟩ := p
    refine Fin.cases ?_ (fun k => ?_) j
    · simp [e, ReciprocityTheory.MultiplicativeHeights.sImage, sImg, Fin.cycleRange_symm_zero]
    · simp [e, ReciprocityTheory.MultiplicativeHeights.sImage, sImg, Fin.cycleRange_symm_succ]
  have hrange : Set.range (ReciprocityTheory.MultiplicativeHeights.sImage (D := d.D) (d.x c)) =
      Set.range (sImg (D := d.D) (d.jc c) (d.x c)) := by
    rw [key, EquivLike.range_comp]
  have h2 := hfs.2
  rw [hrange] at h2
  exact h2

theorem omS_finite (hd : d.AxH 𝒜) (h : d.S1) (c : ι) :
    letI : Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := (d.KTtoS h c).toAlgebra
    FiniteDimensional (KTf K d.D d.N) (OmS (Ω c) d.D d.N) ∧
      Module.finrank (KTf K d.D d.N) (OmS (Ω c) d.D d.N) = d.delc c := by
  letI : Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := (d.KTtoS h c).toAlgebra
  haveI := d.KT_finiteDimensional hd c
  have hfr := d.KTtoS_fieldRange h c
  let e : (KTf K d.D d.N) ≃+* (d.KT c) :=
    ((d.KTtoS h c).rangeRestrictFieldEquiv).trans (RingEquiv.subfieldCongr hfr)
  have he : ∀ z, ((e z : d.KT c) : (OmS (Ω c) d.D d.N)) = d.KTtoS h c z := fun z => rfl
  have hc : (algebraMap (KTf K d.D d.N) (OmS (Ω c) d.D d.N)).comp e.symm.toRingHom =
      (RingEquiv.refl (OmS (Ω c) d.D d.N)).toRingHom.comp (algebraMap (d.KT c) (OmS (Ω c) d.D d.N)) := by
    refine RingHom.ext fun y => ?_
    show d.KTtoS h c (e.symm y) = (y : (OmS (Ω c) d.D d.N))
    rw [← he, RingEquiv.apply_symm_apply]
  refine ⟨Module.Finite.of_equiv_equiv e.symm (RingEquiv.refl _) hc, ?_⟩
  rw [show d.delc c = Module.finrank (d.KT c) (OmS (Ω c) d.D d.N) from rfl]
  exact (Algebra.finrank_eq_of_equiv_equiv e.symm (RingEquiv.refl _) hc).symm

end Data

end ReciprocityTheory.ChartRestriction.G.T0
