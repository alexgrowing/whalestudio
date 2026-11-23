import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.SameNormBasic
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PairCalc
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ConnectedSpaceSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFactorThroughIsogenyOfKillsKernel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsogenyFlatFinrankStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeTorsionPointTrivialOfGeometricStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinBundleKernelSecondCoordEquations

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
attribute [local instance] Over.cartesianMonoidalCategory
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

theorem UpperTheory.Gal.crystallineComparison.Mod.quasiInv_of :
    PairCalc → DivC → QuasiInv := by
  intro hPair hDiv p _ D R _ b N κ _ _ _ s c hc o o' ψ hψ hfin hsur hpol hker
  obtain ⟨hAdd, -, -, ⟨e, he, hE⟩, hcalc⟩ := hPair p D R b N (Sp κ) s o
  obtain ⟨hAdd', -⟩ := hPair p D R b N (Sp κ) s o'
  have hmul := (hcalc o' ψ c).1 hpol
  have hunit : ∀ T : Over (Sp κ), IsUnit ((e : ℕ) : Γ(T.left, ⊤)) := by
    intro T
    have h0 : IsUnit ((e : ℕ) : κ) := by
      rw [isUnit_iff_ne_zero, Ne, CharP.cast_eq_zero_iff κ p]
      intro hd
      have h3 := Nat.Coprime.coprime_dvd_left hd he
      rw [Nat.coprime_self] at h3
      exact (Fact.out : p.Prime).one_lt.ne' h3
    have h1 := h0.map (Scheme.ΓSpecIso (CommRingCat.of κ)).inv.hom
    have h2 := h1.map T.hom.appTop.hom
    simpa using h2
  have hkc : ∀ (T : Over (Sp κ)) (x : T ⟶ o.A), x ≫ ψ = 1 → x ^ c = 1 := by
    intro T x hx
    have h1 : (x ^ c) ^ e = 1 := by
      apply hE T (x ^ c)
      rw [MonObj.comp_pow, GlobalTheory.ZarhinKerB.evc_pow_left _ hAdd, ← hmul, Category.assoc, hx,
        MonObj.comp_one]
      exact IsAdditive.evc_one _ hAdd' _
    refine GlobalTheory.T.abelianScheme_torsionPoint_trivial_of_geometric (Sp κ) o.A o.ab T (x ^ c) e (hunit T) h1 ?_
    intro k _ _ _ z g
    rw [MonObj.comp_pow]
    have hg : g ≫ x = 1 := hker k z (g ≫ x) (by rw [Category.assoc, hx, MonObj.comp_one])
    rw [hg, one_pow]
  obtain ⟨d, hd⟩ := GlobalTheory.AbelianDim.exists_relDim κ o.A o.ab
  obtain ⟨d', hd'⟩ := GlobalTheory.AbelianDim.exists_relDim κ o'.A o'.ab
  let Av : GlobalTheory.AV.AbVar κ := ⟨o.A, o.ab, d, hd⟩
  let Av' : GlobalTheory.AV.AbVar κ := ⟨o'.A, o'.ab, d', hd'⟩
  let q : Av ⟶ Av' := GlobalTheory.AV.AbVar.Hom.mk (A := Av) (B := Av') ψ
  have hpm : IsMonHom (𝟙 o.A ^ c) :=
    (GlobalTheory.AV.AbVar.homSub Av Av).pow_mem (show (𝟙 Av.X) ∈ GlobalTheory.AV.AbVar.homSub Av Av from
      (inferInstance : IsMonHom (𝟙 o.A))) c
  let f : Av ⟶ Av := GlobalTheory.AV.AbVar.Hom.mk (A := Av) (B := Av) (𝟙 o.A ^ c)
  have hfhom : f.hom = 𝟙 o.A ^ c := rfl
  have hq : GlobalTheory.AV.AbVar.IsIsogeny q := ⟨hfin, hsur⟩
  obtain ⟨g, hg⟩ := GlobalTheory.AV.AbVar.exists_factor_of_isogeny κ Av Av' Av q f hq (by
    intro T x hx
    rw [hfhom, MonObj.comp_pow, Category.comp_id]
    exact hkc T x hx)
  have hgm : IsMonHom g.hom := (Additive.toMul g).2
  have hgψ : ψ ≫ g.hom = 𝟙 o.A ^ c := by
    rw [← hfhom, ← hg]
    rfl
  haveI : Flat (Over.Hom.left ψ) := (GlobalTheory.T.dim_eq_flat_finrank_eq_deg_of_isIsogeny κ Av Av' q hq).2.1
  haveI : Surjective (Over.Hom.left ψ) := hsur
  haveI : Epi (Over.Hom.left ψ) := Flat.epi_of_flat_of_surjective _
  refine ⟨g.hom, hgm, hgψ, ?_⟩
  ext1
  rw [← cancel_epi (Over.Hom.left ψ), ← Over.comp_left, ← Over.comp_left, ← Category.assoc, hgψ,
    MonObj.pow_comp, MonObj.comp_pow]
  simp
