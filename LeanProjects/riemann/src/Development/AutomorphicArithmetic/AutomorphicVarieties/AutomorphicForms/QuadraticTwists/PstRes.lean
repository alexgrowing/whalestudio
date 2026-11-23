import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Hypotheses2
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.LocIsotypic
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.V.Af.Cq.pstRes :
    ∀ (F K Ω : Type) [Field F] [NumberField F] [Field K] [NumberField K] [Field Ω] [Algebra F K] [Algebra F Ω] [Algebra K Ω] [IsScalarTower F K Ω] [IsAlgClosure F Ω] [IsAlgClosure K Ω] (l : ℕ) [Fact l.Prime] (A : ValuationSubring Ω) (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l F Ω (Dec (F := F) A) O) (Bw' : LocBridge l K Ω (Dec (F := K) A) O),
        Bw'.Kw = Bw.Kw → Bw'.j = Bw.j → Bw'.LL = Bw.LL → ∀ (n : ℕ) (r : G F Ω →* GL (Fin n) (Qbar l)), IsPstAt (Loc.PP l) Bw (r.comp (Dec (F := F) A).subtype) →
        IsPstAt (Loc.PP l) Bw' ((r.comp (AlgEquiv.restrictScalarsHom F : G K Ω →* G F Ω)).comp (Dec (F := K) A).subtype) := by
  intro F K Ω _ _ _ _ _ _ _ _ _ _ _ l _ A O _ _ _ Bw Bw' hK hj hL n r hr
  obtain ⟨Kw', j', jE', jd', e', ec', esc', ecomm', LL0', hs', eO', h1', h2', h3'⟩ := Bw'
  dsimp only at hK hj hL
  subst hK hj hL
  obtain ⟨LL', r', ⟨hle, hmap⟩, hpst⟩ := hr
  refine ⟨LL', r'.comp (e'.trans Bw.e.symm).toMonoidHom, ⟨hle, ?_⟩, ?_⟩
  · refine MonoidHom.ext fun g => ?_
    have h1 := DFunLike.congr_fun hmap (Bw.e.symm (e' g))
    have h2 : ((Bw.e.symm (e' g) : ↥(Dec (F := F) A)) : Ω ≃ₐ[F] Ω) =
        AlgEquiv.restrictScalarsHom F (g : Ω ≃ₐ[K] Ω) := by
      refine AlgEquiv.ext fun x => Bw.j.injective ?_
      rw [← Bw.e_comm, MulEquiv.apply_symm_apply, ecomm']
      rfl
    refine h1.trans ?_
    exact congrArg r h2
  · convert hpst using 1
    refine MonoidHom.ext fun g => ?_
    simp [LocBridge.repE]
