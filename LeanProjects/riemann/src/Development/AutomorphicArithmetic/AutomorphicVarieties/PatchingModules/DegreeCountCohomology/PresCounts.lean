import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.EpsilonEtaMatrices.EpsilonEtaTensorDual
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.GwBare
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.LocBare
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.LocCongr
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.ArPresAlt

open Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

theorem UpperTheory.V.Pa.presCounts :
    CohP → ∀ (l : ℕ) [Fact l.Prime] (Lc : Loc) (G : Glob l Lc) (q d : ℕ) (a : ArData G q d) (F Ω : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (_ : ArPres a F Ω), l ≠ 2 → (∀ u, UnrCount l (Lc.Gu u) (Lc.Ju u)) → a.Counts := by
  intro hC l _ Lc G q d a F Ω _ _ _ _ _ _ P hl hU
  obtain ⟨hLF, hLTD, hLEC, hGF, _, hGW, _, _⟩ := hC
  have key : ∀ (w : ArData.W Lc q) (n : ℕ),
      LocCount (↥(Dec (P.A w))) ((cycZ F Ω l).comp (Dec (P.A w)).subtype) n →
        LocCount (a.D w) (G.ε.comp (a.ι w)) n := by
    intro w n hn
    refine locCongr l (a.D w) (↥(Dec (P.A w))) (P.α w) (G.ε.comp (a.ι w))
      ((cycZ F Ω l).comp (Dec (P.A w)).subtype) n ?_ hn
    intro g
    simp only [MonoidHom.comp_apply, Subgroup.coe_subtype]
    rw [P.ι_eq w g, P.e_ε]
  have notl : ∀ (w : ArData.W Lc q), (∀ v, w ≠ Sum.inl v) →
      LocCount (a.D w) (G.ε.comp (a.ι w)) 0 := by
    intro w hw
    apply key
    refine (locBare hLF hLTD hLEC l F Ω (P.A w) (↑(P.pl w)) (P.isOver w)).2 ?_
    rw [P.pl_l]
    rintro ⟨v, hv⟩
    exact hw v hv
  have hcw : a.cw = fun i => P.e ((toGS Ω P.S) (P.c i)) := funext P.cw_eq
  refine ⟨?_, ?_, ?_, ?_, hU⟩
  · rw [hcw]
    exact gwBare hGW hLTD hGF hLF l F Ω P.S G.Γ P.e G.ε (ArData.W Lc q) P.pl P.A a.D a.ι P.α d P.ip P.c
      hl P.above P.e_ε P.isOver P.ι_eq P.cc
  · intro v
    have h1 := (locBare hLF hLTD hLEC l F Ω (P.A (Sum.inl v)) (↑(P.pl (Sum.inl v))) (P.isOver _)).1
      ((P.pl_l _).2 ⟨v, rfl⟩)
    rw [← P.dv_eq v] at h1
    exact key (Sum.inl v) _ h1
  · intro u
    exact notl (Sum.inr (Sum.inl u)) (fun v h => by cases h)
  · intro j
    exact notl (Sum.inr (Sum.inr j)) (fun v h => by cases h)
