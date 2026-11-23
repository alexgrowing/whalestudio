import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFlagBundleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleProjectiveOverBaseStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPairBundle
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGrassmannianPairBundle
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairBundleFlagCompat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleSuccessiveGrassmannian
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical

open GlobalTheory.VB

theorem GlobalTheory.OmitFlag.main : ∀ (k : Type) [CommRing k] [IsNoetherianRing k] (B : Scheme.{0}) (q : B ⟶ Sp k), IsProjOver q →
    ∀ (Y : Scheme.{0}) (π : Y ⟶ B) (ι : Type) [Fintype ι]
    (E : ι → B.Modules) (r : ι → ℕ), (∀ a, GlobalTheory.VB.IsVB (E a) (r a)) →
    ∀ (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (r a)), IsFlagBundle π E r fl →
    ∀ (a : ι) (i i' : Fin (r a)), (i' : ℕ) = i + 1 →
    ∃ (Y₁ : Scheme.{0}) (σ : Y₁ ⟶ B) (ρ : Y ⟶ Y₁) (wσ : ρ ≫ σ = π) (S P E₁ : Y₁.Modules) (s : S ⟶ P)
      (j : P ⟶ (Scheme.Modules.pullback σ).obj (E a)) (t : P ⟶ E₁) (wst : s ≫ t = 0)
      (fl₁ : Vert.Flag ((Scheme.Modules.pullback ρ).obj E₁) 2) (A₀ A₁ : (Σ b, Fin (r b)) → Y₁.Modules)
      (u : ∀ z, A₀ z ⟶ A₁ z) (v : ∀ z, A₁ z ⟶ (Scheme.Modules.pullback σ).obj (E z.1)),
      IsProjOver (σ ≫ q) ∧
      IsFlagBundle ρ (fun _ : Unit => E₁) (fun _ => 2) (fun _ => fl₁) ∧
      (ShortComplex.mk s t wst).ShortExact ∧ GlobalTheory.VB.IsSubbundle s ∧ GlobalTheory.VB.IsSubbundle j ∧ GlobalTheory.VB.IsVB S i ∧
      GlobalTheory.VB.IsVB P ((i : ℕ) + 2) ∧ GlobalTheory.VB.IsVB E₁ 2 ∧
      (∃ e : (Scheme.Modules.pullback ρ).obj P ≅ (fl a).F i'.succ, e.hom ≫ (fl a).ι i'.succ =
        (Scheme.Modules.pullback ρ).map j ≫ (Scheme.Modules.pullbackComp ρ σ).hom.app (E a) ≫
          (Scheme.Modules.pullbackCongr wσ).hom.app (E a)) ∧
      (∃ e : (Scheme.Modules.pullback ρ).obj S ≅ (fl a).F i.castSucc, e.hom ≫ (fl a).ι i.castSucc =
        (Scheme.Modules.pullback ρ).map (s ≫ j) ≫ (Scheme.Modules.pullbackComp ρ σ).hom.app (E a) ≫
          (Scheme.Modules.pullbackCongr wσ).hom.app (E a)) ∧
      (∃ (x : (fl a).F i.succ ⟶ (Scheme.Modules.pullback ρ).obj P) (g : (fl a).F i.succ ⟶ fl₁.F 1),
        x ≫ (Scheme.Modules.pullback ρ).map j ≫ (Scheme.Modules.pullbackComp ρ σ).hom.app (E a) ≫
          (Scheme.Modules.pullbackCongr wσ).hom.app (E a) = (fl a).ι i.succ ∧
        g ≫ fl₁.ι 1 = x ≫ (Scheme.Modules.pullback ρ).map t ∧ Epi g) ∧
      ∀ z : Σ b, Fin (r b), z ≠ ⟨a, i⟩ → z ≠ ⟨a, i'⟩ →
        GlobalTheory.VB.IsSubbundle (u z) ∧ GlobalTheory.VB.IsSubbundle (v z) ∧ GlobalTheory.VB.IsVB (A₀ z) z.2 ∧
        GlobalTheory.VB.IsVB (A₁ z) ((z.2 : ℕ) + 1) ∧
        (∃ e : (Scheme.Modules.pullback ρ).obj (A₁ z) ≅ (fl z.1).F z.2.succ, e.hom ≫ (fl z.1).ι z.2.succ =
          (Scheme.Modules.pullback ρ).map (v z) ≫ (Scheme.Modules.pullbackComp ρ σ).hom.app (E z.1) ≫
            (Scheme.Modules.pullbackCongr wσ).hom.app (E z.1)) ∧
        (∃ e : (Scheme.Modules.pullback ρ).obj (A₀ z) ≅ (fl z.1).F z.2.castSucc, e.hom ≫ (fl z.1).ι z.2.castSucc =
          (Scheme.Modules.pullback ρ).map (u z ≫ v z) ≫ (Scheme.Modules.pullbackComp ρ σ).hom.app (E z.1) ≫
            (Scheme.Modules.pullbackCongr wσ).hom.app (E z.1)) := by
  intro k _ _ B q hq Y π ι _ E r hE fl hfl a i i' hi'
  have hle : (i : ℕ) + 2 ≤ r a := by have := i'.isLt; omega
  obtain ⟨G, γ, SG, PG, sG, jG, hS, hP, hs, hj, hQ, hG⟩ := GlobalTheory.T.exists_grassmannian_pair_bundle B (E a) (r a) i ((i : ℕ) + 2) (hE a) (by omega) hle
  have hGp : IsProjOver (γ ≫ q) := GlobalTheory.T.pair_bundle_flag_compat k B q hq (E a) (r a) i ((i : ℕ) + 2) (hE a) (by omega) hle G γ SG PG sG jG hS hP hs hj hG
  have hF : ∀ c, GlobalTheory.VB.IsVB (GlobalTheory.OmitFlag.fam γ E a sG jG c) (GlobalTheory.OmitFlag.rk r a i ((i : ℕ) + 2) c) := by
    rintro (b | _ | _)
    · exact (hE b.1).pullback γ
    · exact hQ
    · exact hS
  obtain ⟨Y₁, τ, fl', hY₁⟩ := GlobalTheory.T.exists_flag_bundle G _ (GlobalTheory.OmitFlag.fam γ E a sG jG) (GlobalTheory.OmitFlag.rk r a i ((i : ℕ) + 2)) hF
  have hY₁p : IsProjOver (τ ≫ γ ≫ q) := GlobalTheory.T.flag_bundle_projective_over_base k G Y₁ (γ ≫ q) τ _ _ _ fl' hGp hF hY₁
  obtain ⟨ρ, wσ, S, P, E₁, s, j, t, wst, fl₁, A₀, A₁, u, v, h⟩ :=
    GlobalTheory.T.flag_bundle_successive_grassmannian B Y π ι E r hE fl hfl a i i' hi' G γ SG PG sG jG hS hP hs hj hQ hG Y₁ τ fl' hY₁
  exact ⟨Y₁, τ ≫ γ, ρ, wσ, S, P, E₁, s, j, t, wst, fl₁, A₀, A₁, u, v, by simpa using hY₁p, h⟩
