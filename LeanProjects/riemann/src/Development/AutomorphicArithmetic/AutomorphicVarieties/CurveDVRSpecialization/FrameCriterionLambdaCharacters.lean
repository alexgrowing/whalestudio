import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.CrDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.GalEmbTop

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Alg UpperTheory.V.Pr UpperTheory.V

theorem UpperTheory.frame_criterion_lambda_characters :
    UpperTheory.V.Pr.CrLam := by
  intro Ω _ _ _ l _ O _ _ η Ψ σ g₁ B M L _ _ _ _ _ Φ k v A hA hM
  haveI := Φ.cv v
  haveI := Φ.t2v v
  obtain ⟨hemb, -, -⟩ := galEmbTop ℚ L Ω
  let e1 : Dec (F := L) A →* G ℚ Ω := (galEmb ℚ L Ω).comp (Dec (F := L) A).subtype
  let e2 : Φ.Gv v →* G ℚ Ω := (upl Ω L).subtype.comp (k.j v)
  have he1 : Function.Injective e1 := hemb.injective.comp Subtype.val_injective
  have he2 : Function.Injective e2 := Subtype.val_injective.comp (k.j_inj v)
  have hrange : e1.range = e2.range := by
    ext τ
    constructor
    · rintro ⟨g, rfl⟩
      have hup : e1 g ∈ upl Ω L := by
        have := galEmb_mem ℚ L Ω (g : G L Ω)
        rw [k.gal] at this
        exact this.1
      have hdec : e1 g ∈ Dec (F := ℚ) (k.pl v) := by
        show galEmb ℚ L Ω g ∈ _
        rw [← hA, galEmb_mem_Dec]
        exact g.2
      obtain ⟨x, hx⟩ := (k.j_range v ⟨_, hup⟩).2 hdec
      exact ⟨x, congrArg Subtype.val hx⟩
    · rintro ⟨x, rfl⟩
      have hdec : e2 x ∈ Dec (F := ℚ) A := by
        rw [hA]
        exact (k.j_range v (k.j v x)).1 ⟨x, rfl⟩
      have hup : e2 x ∈ upl Ω L := (k.j v x).2
      have hker : e2 x ∈ η.ker := k.split A hM ⟨hdec, hup⟩
      have hfix : e2 x ∈ galOf ℚ L Ω := by
        rw [k.gal]
        exact ⟨hup, hker⟩
      let g : G L Ω := AlgEquiv.ofRingEquiv (f := (e2 x).toRingEquiv) (fun y => hfix y)
      have hg : galEmb ℚ L Ω g = e2 x := by
        ext y
        rfl
      have hgd : g ∈ Dec (F := L) A := by
        rw [← galEmb_mem_Dec (k := ℚ), hg]
        exact hdec
      exact ⟨⟨g, hgd⟩, hg⟩
  let m : Dec (F := L) A ≃* Φ.Gv v :=
    (MonoidHom.ofInjective he1).trans ((MulEquiv.subgroupCongr hrange).trans (MonoidHom.ofInjective he2).symm)
  have hm : ∀ g, e2 (m g) = e1 g := by
    intro g
    have := MonoidHom.ofInjective_apply he2 (x := m g)
    rw [← this, ← MonoidHom.ofInjective_apply he1 (x := g)]
    simp [m]
  have hinv : Continuous m.symm := by
    have hcomp : e1 ∘ m.symm = e2 := by
      funext x
      rw [Function.comp_apply, ← hm, MulEquiv.apply_symm_apply]
    have he1emb : Topology.IsEmbedding e1 := hemb.comp Topology.IsEmbedding.subtypeVal
    rw [he1emb.continuous_iff, hcomp]
    exact continuous_subtype_val.comp (k.j_cont v)
  have hfwd : Continuous m := by
    have := hinv.continuous_symm_of_equiv_compact_to_t2 (f := m.symm.toEquiv)
    simpa using this
  refine ⟨{ m with continuous_toFun := hfwd, continuous_invFun := hinv }, fun g => ?_⟩
  exact hm g
