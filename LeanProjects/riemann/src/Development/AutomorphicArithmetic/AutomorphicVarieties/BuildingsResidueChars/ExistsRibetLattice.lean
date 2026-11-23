import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.QuadraticSplitting.QuadSplit
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.RibetLat
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.GalEmbTop

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Ws UpperTheory.V.Sd UpperTheory.V.Sd.S2

theorem UpperTheory.exists_ribet_lattice :
    UpperTheory.V.Sd.S2.RibOf := by
  intro Ω _ _ _ l _ c D T k₀ _ _ φ ι k t r hyp hch hd u hu
  haveI : IsAlgClosure k₀ Ω := ⟨IsAlgClosure.isAlgClosed ℚ, inferInstance⟩
  haveI : IsGalois k₀ Ω := {}
  have hc : Continuous (resQ k₀ : G k₀ Ω →* G ℚ Ω) := by
    have h := (galEmbTop ℚ k₀ Ω).1.continuous
    have e : (resQ k₀ : G k₀ Ω →* G ℚ Ω) = galEmb ℚ k₀ Ω := by
      ext σ x
      rw [galEmb_apply]; rfl
    rw [e]; exact h
  let H : Subgroup (G k₀ Ω) := T.F.fixingSubgroup.comap (resQ k₀)
  have hHo : IsOpen (H : Set (G k₀ Ω)) := T.F.fixingSubgroup_isOpen.preimage hc
  haveI : CompactSpace H := isCompact_iff_compactSpace.1 (H.isClosed_of_isOpen hHo).isCompact
  have hg : resQ T.F T.g0 ∈ T.F.fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    exact T.g0.commutes ⟨x, hx⟩
  have huH : u ∈ H := by
    show resQ k₀ u ∈ T.F.fixingSubgroup
    rw [hu]; exact mul_mem hg hg
  obtain ⟨ρ', ⟨g, hρ⟩, q1, q2, q3, s, q4⟩ := ribetLat l H (r.comp H.subtype) 1 (((up D.ξ).comp (resQ k₀)).comp H.subtype)
    (hd.cont.comp continuous_subtype_val) (hd.irr H hHo) (fun s => ⟨by simp, hch.unit _ _⟩)
    (fun s i => by
      have := hd.res s i
      simpa only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, MonoidHom.comp_apply, MonoidHom.one_apply,
        Subgroup.coe_subtype] using this) ⟨u, huH⟩ (by
      have := hch.sq
      rw [← hu] at this
      exact this)
  have e : ∀ s : H, ((MulAut.conj g).toMonoidHom.comp r) s = ρ' s := fun s => (hρ s).symm
  refine ⟨(MulAut.conj g).toMonoidHom.comp r, ⟨g, fun _ => rfl⟩, ?_, ?_, fun h hh => ?_, s, s.2, ?_⟩
  · rw [e ⟨u, huH⟩]; exact q1
  · rw [e ⟨u, huH⟩]; exact q2
  · rw [e ⟨h, hh⟩]; exact q3 ⟨h, hh⟩
  · rw [e s]; exact q4
