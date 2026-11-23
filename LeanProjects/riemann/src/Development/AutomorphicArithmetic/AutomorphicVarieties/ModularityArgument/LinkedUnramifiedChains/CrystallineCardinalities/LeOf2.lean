import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.CrystallineCardinalities.LcOrbit
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.CrystallineCardinalities.LeTrans

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr UpperTheory.V.Z.J Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V

private noncomputable def isoOf {D D' : Type} [Group D] [TopologicalSpace D] [CompactSpace D] [Group D'] [TopologicalSpace D']
    [T2Space D'] (f : D →* D') (hc : Continuous f) (hb : Function.Bijective f) : D ≃ₜ* D' :=
  { MulEquiv.ofBijective f hb with
    continuous_toFun := hc
    continuous_invFun :=
      (Continuous.homeoOfEquivCompactToT2 (f := (MulEquiv.ofBijective f hb).toEquiv) hc).symm.continuous }

theorem UpperTheory.V.Z.J.leOf2 :
    GC.Hypotheses₂ → ∀ (l : ℕ) [Fact l.Prime] (κ : Type) [Field κ] (Φ : Frame l κ) (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] S K π ι A pl e c, GC.FLink (F := F) (Ω := Ω) l Φ S K π ι A pl e c → LocE Φ := by
  intro hP l _ κ _ Φ F Ω _ _ _ _ _ S K π ι A pl e c hL v
  have hrange := hL.loc.range v
  let f : Φ.Gv v →* Dec (A v) :=
    (ι v).codRestrict (Dec (A v)) (fun s => hrange ▸ (MonoidHom.mem_range.2 ⟨s, rfl⟩))
  have hfc : Continuous f := (hL.loc.cont v).subtype_mk _
  have hfb : Function.Bijective f := by
    constructor
    · intro a b hab
      exact hL.loc.ι_inj v (congrArg Subtype.val hab)
    · rintro ⟨g, hg⟩
      rw [← hrange] at hg
      obtain ⟨s, rfl⟩ := hg
      exact ⟨s, rfl⟩
  have hl := (hL.loc.mem (pl v)).1 ⟨v, rfl⟩
  have h0 := leOf hP.lf hP.lt hP.le l F Ω (A v) (pl v) (hL.loc.isOver v) hl
  have h1 := leTrans l (Φ.Gv v) (Dec (A v)) (isoOf f hfc hfb) _ _ h0
  rw [hL.dv v]
  convert h1 using 2
  ext s
  simp [hL.loc_eq, hL.eps]
  rfl
