import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.TransCancel

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

theorem UpperTheory.Gal.G3.pKSNice :
    KNBasic → PowSm → TwFEt → SigmaFEt → KSNice := by
  intro hKN hP hT hS p _ D G L hsc R _ _ gb k T N J g
  have hq := T.e_q N
  obtain ⟨hsm, -, hpr⟩ := hP p D R gb N (T.M N) k
  refine ⟨?_, ?_, ?_⟩
  · show Smooth (T.X.q (T.lev N))
    rw [← hq]
    infer_instance
  · show IsProjOver (T.X.q (T.lev N))
    rw [← hq]
    exact GlobalTheory.ProjSpace.isProjOver_comp_of_isClosedImmersion _ (hpr hsc.cpt)
  · intro j
    dsimp only [UpperTheory.Gal.Int.Geo.KS.tower]
    have hne : ((L.KN ↑N).subgroupOf (g j).K).index ≠ 0 := by
      have h0 := (hKN p D G L 1).2.2 N (by norm_num) (by have := N.2.1; omega)
      rw [← Subgroup.relIndex_mul_relIndex _ _ _ (g j).le (g j).le_one] at h0
      exact left_ne_zero_of_mul h0
    haveI : ((L.KN ↑N).subgroupOf (g j).K).FiniteIndex := ⟨hne⟩
    refine ⟨_, hS _ _ _ (hT T.X _ _ ⟨?_, ?_⟩)⟩
    · exact one_mem _
    · intro u hu
      rw [T.K_eq] at hu ⊢
      simpa using UpperTheory.Gal.Int.Geo.KN_anti (g j).dvd hu
