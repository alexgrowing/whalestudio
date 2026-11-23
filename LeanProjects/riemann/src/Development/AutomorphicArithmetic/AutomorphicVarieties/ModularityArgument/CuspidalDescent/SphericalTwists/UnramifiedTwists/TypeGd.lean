import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.SphericalTwists.HodgeTateFromSandwich
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.AbConv
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PolarizedLinkage.ExtraV
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PlainTorExistsChars

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil
open GlobalTheory.PRep UpperTheory.V.Af UpperTheory.V.Z.Win UpperTheory.Zero.LLC

open scoped commutatorElement

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.V.Z.Desc.W.typeGd :
    UpperTheory.V.Z.Desc.W.TypeGd := by
  intro E Ω _ _ _ _ _ n w A h σ rc hrc χ ⟨b, hb, hN, hχ⟩
  have hm : (rc (algNorm σ)).mono0 := hb ▸ (WD.monodromyZero_ofWeilDeligneRepClass_iff b).2 hN
  have hT : UpperTheory.Zero.LLC.Toral (algNorm σ) := by
    refine UpperTheory.Zero.LLC.abConv E Ω A w h rc hrc (algNorm σ) (fun j : Fin n => (χ j).comp (Weil h).subtype) fun t => ?_
    rw [← hb, WD.charPol_mk, hχ t, Matrix.charpoly_toLin', Matrix.charpoly_diagonal]
    rfl
  obtain ⟨a, ha, ε, L⟩ := toV' hrc
  obtain ⟨s, hs, hch⟩ := hT
  refine ⟨?_, ?_, hm⟩
  · have hs' := GlobalTheory.LocGL.SupportRing.hasSupport_nu hs (-(((1 - (n : ℝ)) / 2 : ℝ) : ℂ))
    have e : (algNorm σ).nu (-(((1 - (n : ℝ)) / 2 : ℝ) : ℂ)) = IrrGL.of σ.ρ σ.smooth σ.irred := by
      unfold algNorm
      rw [IrrGL.nu_nu, add_neg_cancel, IrrGL.nu_zero]
    rw [← e]
    refine ⟨_, hs', fun y hy => ?_⟩
    obtain ⟨z, hz, rfl⟩ := Multiset.mem_map.1 hy
    exact Or.inl (hch z hz)
  · intro p q
    have h1 : ∀ y ∈ s, (rc y).charPol ⁅p, q⁆ = X - 1 := fun y hy => by
      obtain ⟨θ, hθ, rfl⟩ := GlobalTheory.RoadU.PlainChars.exists_eq_ofChar y (hch y hy)
      rw [L.one, WD.lpOfChar, WD.charPol_mk, WDRep.ofChars_ρ, charpoly_diagEnd]
      have hc1 : ⁅θ (a p), θ (a q)⁆ = 1 := by
        rw [commutatorElement_eq_one_iff_mul_comm]
        exact mul_comm _ _
      simp [hc1]
    have hc : Multiset.card s = (algNorm σ).1 := by
      have h2 := hs.sum_fst
      rw [Multiset.map_congr rfl hch, Multiset.map_const', Multiset.sum_replicate, Fintype.card_fin] at h2
      simpa using h2
    show WD.charPol _ _ = _
    rw [L.supp _ s hs, L.dim, Multiset.map_congr rfl h1, Multiset.map_const', Multiset.prod_replicate, hc]
