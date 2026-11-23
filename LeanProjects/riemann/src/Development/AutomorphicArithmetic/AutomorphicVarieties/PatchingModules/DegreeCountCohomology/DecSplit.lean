import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.EpsilonEtaMatrices.EpsilonEtaTensorDual

open Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

theorem UpperTheory.V.Pa.decSplit :
    ∀ (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (A : ValuationSubring Ω), Dec (F := Lp L) A ≤ (resP L Ω).range → ∃ α : Dec (F := L) A ≃ₜ* Dec (F := Lp L) A, ∀ g, (α g : G (Lp L) Ω) = resP L Ω (g : G L Ω) := by
  intro L Ω _ _ _ _ _ _ A hA
  have hinj : Function.Injective (resP L Ω) := by
    intro a b h
    ext x
    exact congrArg (fun f : G (Lp L) Ω => f x) h
  have hmap : ∀ g : Dec (F := L) A, resP L Ω (g : G L Ω) ∈ Dec (F := Lp L) A := by
    intro g
    have hg := mem_Dec.mp g.2
    exact mem_Dec.mpr hg
  let f : Dec (F := L) A →* Dec (F := Lp L) A :=
    { toFun := fun g => ⟨resP L Ω g, hmap g⟩
      map_one' := by ext1; exact map_one (resP L Ω)
      map_mul' := fun a b => by ext1; exact map_mul (resP L Ω) a.1 b.1 }
  have hbij : Function.Bijective f := by
    refine ⟨fun a b h => Subtype.ext (hinj (congrArg Subtype.val h)), fun t => ?_⟩
    obtain ⟨s, hs⟩ := hA t.2
    have hsA : s ∈ Dec (F := L) A := by
      apply mem_Dec.mpr
      have := mem_Dec.mp (hs ▸ t.2)
      exact this
    exact ⟨⟨s, hsA⟩, Subtype.ext hs⟩
  let e : Dec (F := L) A ≃* Dec (F := Lp L) A := MulEquiv.ofBijective f hbij
  have hcont : Continuous e := by
    apply Continuous.subtype_mk
    exact continuous_resP.comp continuous_subtype_val
  haveI : CompactSpace (Dec (F := L) A) :=
    isCompact_iff_compactSpace.mp (isClosed_Dec (F := L) A).isCompact
  let h := hcont.homeoOfEquivCompactToT2 (f := e.toEquiv)
  refine ⟨{ e with continuous_toFun := h.continuous, continuous_invFun := h.symm.continuous }, fun g => rfl⟩
