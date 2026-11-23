import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ResidueFlagPoints.ResLeCont
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AutomorphicCharacters.IrrOfStab

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.CuspRep GlobalTheory.GalOfCusp

private theorem exists_resLe {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l}
    {D : Raw Ω c} (T : Tower D) (g : G T.F Ω) (hg : g ∈ T.GalL) : ∃ s : G T.L Ω, resLe T.F_le s = g := by
  have h1 : resQ T.F g ∈ T.K.fixingSubgroup := hg
  have h2 : resQ T.F g ∈ T.F.fixingSubgroup :=
    (IntermediateField.mem_fixingSubgroup_iff _ _).2 fun x hx => g.commutes ⟨x, hx⟩
  have h3 : resQ T.F g ∈ T.L.fixingSubgroup := by
    have e : T.L.fixingSubgroup = T.F.fixingSubgroup ⊓ T.K.fixingSubgroup := by
      rw [T.hL]; exact IntermediateField.fixingSubgroup_sup
    rw [e]
    exact ⟨h2, h1⟩
  have h4 := (IntermediateField.mem_fixingSubgroup_iff _ _).1 h3
  exact ⟨{ g.toRingEquiv with commutes' := fun x => h4 x.1 x.2 }, AlgEquiv.ext fun _ => rfl⟩

theorem UpperTheory.V.Ws.Pt.ptIrr :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {D : Raw Ω c} {T : Tower D} {c' : Coef l} {h : c.O ≤ c'.O} (K : Link T c' h) (n : ℕ) (r : G T.F Ω →* M4 (PadicAlgCl l)), Irr (r.comp T.G'.subtype) → Irr r ∧ Af.IsIrr ((K.rhoQ n r).comp (cycBar T.L Ω l).ker.subtype) := by
  intro Ω _ _ _ l _ c D T c' h K n r hr
  constructor
  · have h1 : Submodule.span (PadicAlgCl l) (Set.range (r.comp T.G'.subtype)) = ⊤ := hr
    change Submodule.span (PadicAlgCl l) (Set.range r) = ⊤
    refine eq_top_iff.2 (h1.ge.trans (Submodule.span_mono ?_))
    rintro _ ⟨g, rfl⟩
    exact ⟨g.1, rfl⟩
  · have h2 := (auIrr (r.comp T.G'.subtype) ((r.comp (resLe T.F_le)).comp (cycBar T.L Ω l).ker.subtype) hr ?_).2
      ((K.twc n).comp (cycBar T.L Ω l).ker.subtype)
    · have e : (K.rhoQ n r).comp (cycBar T.L Ω l).ker.subtype =
          Af.tw ((r.comp (resLe T.F_le)).comp (cycBar T.L Ω l).ker.subtype).toHomUnits
            ((K.twc n).comp (cycBar T.L Ω l).ker.subtype) := by
        refine MonoidHom.ext fun g => Units.ext ?_
        rw [Af.tw_val]
        exact K.rho_val n r g
      rw [e]
      exact h2
    · intro g
      obtain ⟨s, hs⟩ := exists_resLe T g.1 g.2.1
      have hz : cycZ T.F Ω l g.1 = 1 := g.2.2
      have hk : s ∈ (cycBar T.L Ω l).ker := by
        rw [MonoidHom.mem_ker, ← cycBar_resLe T.F_le, hs, cycBar, MonoidHom.comp_apply, hz, map_one]
      refine ⟨⟨s, hk⟩, ?_⟩
      change r (resLe T.F_le s) = r g.1
      rw [hs]
