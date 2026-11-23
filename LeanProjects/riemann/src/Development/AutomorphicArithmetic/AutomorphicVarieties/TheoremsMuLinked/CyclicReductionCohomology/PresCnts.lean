import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CyclicReductionCohomology.DualPair
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CyclicReductionCohomology.LocCntBare
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CyclicReductionCohomology.GwCntBare
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CyclicReductionCohomology.LocCntCongr
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CyclicReductionCohomology.UnrDev

open IsLocalRing Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.HV UpperTheory.V.Th GlobalTheory.GalOfCusp

theorem UpperTheory.V.Th.presCnts :
    CohP → ∀ (l : ℕ) [Fact l.Prime] (Lc : Loc) (G : Glob l Lc) (q d : ℕ) (a : ArData G q d) (F Ω : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (_ : ArPres a F Ω), l ≠ 2 → (∀ u, UnrCount l (Lc.Gu u) (Lc.Ju u)) → Cnts a := by
  intro hC l _ Lc G q d a F Ω _ _ _ _ _ _ P hl hU
  have hmatch : ∀ (w : ArData.W Lc q) (g : a.D w),
      G.ε (a.ι w g) = cycZ F Ω l ((Dec (P.A w)).subtype (P.α w g)) := by
    intro w g
    exact (congrArg G.ε (P.ι_eq w g)).trans (P.e_ε _)
  refine Cnts.mk ?_ ?_ ?_ ?_
  · have key := gwCntBare hC.gw hC.lt hC.gf hC.lf l F Ω P.S G.Γ P.e G.ε (ArData.W Lc q) P.pl P.A
      a.D a.ι P.α d P.ip P.c hl P.above P.e_ε P.isOver P.ι_eq P.cc
    have hcw : a.cw = fun i => P.e ((toGS Ω P.S) (P.c i)) := funext P.cw_eq
    rw [hcw]
    exact key
  · intro v
    have hv : (l : 𝓞 F) ∈ (P.pl (Sum.inl v) : HeightOneSpectrum (𝓞 F)).asIdeal := (P.pl_l _).2 ⟨v, rfl⟩
    have h1 := (locCntBare hC.lf hC.lt hC.le l F Ω (P.A (Sum.inl v)) _ (P.isOver (Sum.inl v))).1 hv
    rw [P.dv_eq v]
    exact locCntCongr l (a.D (Sum.inl v)) _ (P.α (Sum.inl v)) _ _ _ (hmatch (Sum.inl v)) h1
  · intro j
    have hn : (l : 𝓞 F) ∉ (P.pl (Sum.inr (Sum.inr j)) : HeightOneSpectrum (𝓞 F)).asIdeal := by
      intro hm
      obtain ⟨v, hv⟩ := (P.pl_l _).1 hm
      cases hv
    have h0 := (locCntBare hC.lf hC.lt hC.le l F Ω (P.A (Sum.inr (Sum.inr j))) _
      (P.isOver (Sum.inr (Sum.inr j)))).2 hn
    exact locCntCongr l (a.D (Sum.inr (Sum.inr j))) _ (P.α (Sum.inr (Sum.inr j))) _ _ _
      (hmatch (Sum.inr (Sum.inr j))) h0
  · intro u
    exact unrDev l _ _ (hU u)
