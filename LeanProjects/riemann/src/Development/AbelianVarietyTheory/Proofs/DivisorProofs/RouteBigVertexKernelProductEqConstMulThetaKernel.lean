import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareTriple
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaTensorRuleTargetOrthogonalSum
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjWeilDatumViaAdjointExchangedPair
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsWeilDatumConjNegHermitianSpaces
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDataDifferBySplittingFactorQuotient
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilDatumOfSplittingCharacters
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsOrthDec
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnramifiedHeckeCharHalfExponentRestrictQua
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PtYAndItYOfPair
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLowestKTypeFockMapThetaVectors

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.Grid
noncomputable section

namespace GlobalTheory.RouteSeesaw

open GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger GlobalTheory.MixModel

theorem data_theta {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (B : Frames G)
    (ρ : RealMatch W) (t : T) (i j : Fin D.R.m) {Θ : TotT G (routeBig t i j)} {Θ' : TotT G (routeSmall t i j)}
    (hΘ : IsMatched B t ρ i j Θ Θ') : ∀ d ∈ Θ.support,
      IsThetaFunO W.ψ (G.pS (.chi i (j + 1))) (G.pT (.chi i (j + 1))) d.1.2 ∧
      IsThetaFunO W.ψ (G.pS (.mu t (i + 1) j)) (G.pT (.mu t (i + 1) j)) d.2 := by
  classical
  obtain ⟨a, b, τ, τ', n, Φ, -, -, ⟨e, -, -, φ₁, φ₂, hloc, -⟩, rfl, -⟩ := hΘ
  intro d hd
  have hsupp := Finsupp.support_sum hd
  simp only [Finset.mem_biUnion] at hsupp
  obtain ⟨P, -, hP⟩ := hsupp
  have hsupp2 := Finsupp.support_sum hP
  simp only [Finset.mem_biUnion] at hsupp2
  obtain ⟨d', hd', hd'2⟩ := hsupp2
  have hdd := Finset.mem_singleton.1 (Finsupp.support_single_subset hd'2)
  subst hdd
  obtain ⟨h1, h2⟩ := hloc d' hd'
  have v1 := (ρ.vX_is (i : ℕ) ((j : ℕ) + 1) i.2 j.2).2.theta
  have v2 := (ρ.vT_is t ((i : ℕ) + 1) (j : ℕ) i.2 j.2).2.theta
  have t1 := GlobalTheory.JointHarm.isThetaFunO_of_isThetaAt W.ψ_std W.θ_is h1.2 v1
  have t2 := GlobalTheory.JointHarm.isThetaFunO_of_isThetaAt W.ψ_std W.θ_is h2.2 v2
  exact ⟨GlobalTheory.Chain.InnerSteps.theta_pureTensorO W.ψ_std W.θ_is _ _ _ _ t1 _,
    GlobalTheory.Chain.InnerSteps.theta_pureTensorO W.ψ_std W.θ_is _ _ _ _ t2 _⟩

theorem dagger_zero {D : D7} (S T : HSp D) : dagger S T 0 = 0 := by
  simp [dagger]

theorem hecke_mul' {D : D7} {χ ν : (AE D)ˣ →* Circle} (hχ : IsHeckeChar D χ) (hν : IsHeckeChar D ν) :
    IsHeckeChar D (χ * ν) :=
  ⟨hχ.1.mul hν.1, fun x => by rw [MonoidHom.mul_apply, hχ.2, hν.2, mul_one]⟩

theorem splitFac_ratio {D : D7} (a b c : (AE D)ˣ →* Circle) (x y : (AE D)ˣ) :
    (splitFacO a c⁻¹ x y : ℂ) * (splitFacO b⁻¹ c⁻¹ x y : ℂ)⁻¹ = ((a y * b y : Circle) : ℂ) := by
  simp only [splitFacO, MonoidHom.inv_apply, inv_inv, Circle.coe_mul, Circle.coe_inv]
  have h1 : ((c x : Circle) : ℂ) ≠ 0 := Circle.coe_ne_zero _
  have h2 : ((b y : Circle) : ℂ) ≠ 0 := Circle.coe_ne_zero _
  field_simp

theorem seesaw_product {D : D7} {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {Wo V V₁ : HSp D}
    {c1S c1T c2S c2T : (AE D)ˣ →* Circle}
    {ω₁ : GA D (negSp Wo) × GA D V →* Module.End ℂ (WO (negSp Wo) V → ℂ)}
    {ω₂ : GA D V₁ × GA D Wo →* Module.End ℂ (WO V₁ Wo → ℂ)}
    (H1 : IsWeilDatumO ψ (negSp Wo) V c1S c1T ω₁) (H2 : IsWeilDatumO ψ V₁ Wo c2S c2T ω₂)
    {f₁ : WO (negSp Wo) V → ℂ} {f₂ : WO V₁ Wo → ℂ} (hf₁ : IsThetaFunO ψ (negSp Wo) V f₁)
    (hf₂ : IsThetaFunO ψ V₁ Wo f₂) (g : GA D V) (g₁ : GA D V₁) :
    ∃ (X : HSp D) (χ χ' : (AE D)ˣ →* Circle) (ω : WRep Wo X), IsWeil ψ true Wo X χ χ' ω ∧
      X.rank = V.rank + V₁.rank ∧ ∃ Φ : WO (sgn true Wo) X → ℂ, IsThetaFunO ψ (sgn true Wo) X Φ ∧
        ∃ (h : GA D X) (c : ℂ), ∀ u, ω₁ (negGA Wo u, g) f₁ 0 * ω₂ (g₁, u) f₂ 0 = c * thetaKO ω u h Φ := by
  have hη : ∃ η, GlobalTheory.WeilParts.IsEtaTilde D η :=
    (GlobalTheory.Mem.EtaTilde.exists_etaTilde D).imp fun _ h => ⟨h.1, h.2.2.2, h.2.2.1, h.2.1⟩

  have H2b : IsWeilDatumO ψ (negSp Wo) V₁ c2T⁻¹ c2S⁻¹ (conjSource (conjAdjoint ω₂)) :=
    GlobalTheory.ConjWeil.weil_conjSource D ψ Wo V₁ _ _ _ (GlobalTheory.ConjAdjWeil.isWeilDatumO_conjAdjoint D ψ V₁ Wo _ _ ω₂ H2)

  obtain ⟨ω₂c, H2c⟩ := GlobalTheory.WeilExist.exists_isWeilDatumO D ψ hψ (negSp Wo) V₁ c1S c2S⁻¹ hη H1.hecS
    (GlobalTheory.ConjWeil.hecke_inv H2.hecS) H1.resS (resEta_inv H2.resS)

  obtain ⟨ω', H'⟩ := GlobalTheory.WeilExist.exists_isWeilDatumO D ψ hψ (negSp Wo) (GlobalTheory.Doubling.hsum V V₁) c1S (c1T * c2S⁻¹) hη
    H1.hecS (hecke_mul' H1.hecT (GlobalTheory.ConjWeil.hecke_inv H2.hecS)) H1.resS (resEta_mul H1.resT (resEta_inv H2.resS))
  set o := GlobalTheory.OrthSumExists.orthDecHsum D V V₁ with ho
  have TT := GlobalTheory.TensorTargetRule.tensorTarget D ψ hψ (GlobalTheory.Doubling.hsum V V₁) V V₁ o (negSp Wo)

  have hF₂ : IsThetaFunO ψ (negSp Wo) V₁ (cj id (cj (dagger Wo V₁) f₂)) := by
    have h1 : IsThetaFunO ψ Wo V₁ (cj (dagger Wo V₁) f₂) := ((GlobalTheory.T.hermitianAdjoint_symplectic_action_theta_heisenberg D ψ hψ V₁ Wo).2.2.1 f₂).2 hf₂
    have I := GlobalTheory.CjNeg.theta_heis_neg D ψ hψ Wo V₁
    exact ((I.1 _).2).2 h1
  obtain ⟨y, hy⟩ := GlobalTheory.RecDict.exists_isDetRoot D V₁ g₁
  let ω : WRep Wo (GlobalTheory.Doubling.hsum V V₁) := ω'.comp ((negGA Wo).toMonoidHom.prodMap (MonoidHom.id _))
  have hω : ω.toSgn true = ω' := MonoidHom.ext fun p => rfl
  refine ⟨GlobalTheory.Doubling.hsum V V₁, c1S, c1T * c2S⁻¹, ω, ?_, rfl, o.boxT (negSp Wo) f₁ (cj id (cj (dagger Wo V₁) f₂)),
    TT.box_theta _ _ hf₁ hF₂, o.emb (g, g₁), ((c1S y * c2T y : Circle) : ℂ)⁻¹, fun u => ?_⟩
  · show IsWeilDatumO ψ (sgn true Wo) _ _ _ (ω.toSgn true)
    rw [hω]; exact H'
  · obtain ⟨x, hx⟩ := GlobalTheory.RecDict.exists_isDetRoot D (negSp Wo) (negGA Wo u)
    have k1 := TT.om_box c1S c1T c2S⁻¹ ω' ω₁ ω₂c H' H1 H2c (negGA Wo u) g g₁ f₁ _ hf₁ hF₂
    have k2 := GlobalTheory.WeilChange.weilData_differ_by_splitFac D ψ (negSp Wo) V₁ c2T⁻¹ c2S⁻¹ c1S c2S⁻¹ _ ω₂c H2b H2c
      (negGA Wo u) g₁ x y hx hy _ hF₂
    have k3 : conjSource (conjAdjoint ω₂) (negGA Wo u, g₁) (cj id (cj (dagger Wo V₁) f₂)) 0 = ω₂ (g₁, u) f₂ 0 := by
      rw [GlobalTheory.ConjWeil.conjSource_apply]
      simp only [MulEquiv.symm_apply_apply, GlobalTheory.ConjWeil.cj_id_cj_id]
      rw [GlobalTheory.TensorTargetRule.conjAdjoint_cj]
      simp [GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj, dagger_zero]
    show _ = _ * ω' (negGA Wo u, o.emb (g, g₁)) (o.boxT (negSp Wo) f₁ (cj id (cj (dagger Wo V₁) f₂))) 0
    rw [k1, OrthDec.boxT_zero, k2, Pi.smul_apply, smul_eq_mul, k3, splitFac_ratio]
    have h0 : ((c1S y * c2T y : Circle) : ℂ) ≠ 0 := Circle.coe_ne_zero _
    field_simp

end GlobalTheory.RouteSeesaw

open GlobalTheory.RouteSeesaw in

theorem GlobalTheory.FunObj.routeBig_kernel_product_eq_theta : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (hL : L.Is μ₀)
    (W : G.Weil) (B : Frames G) (ρ : RealMatch W) (t : T) (i j : Fin D.R.m) (hT : SquareTriple W t i j)
    (M : Vol G) (hM : M.Is t) (Θ : TotT G (routeBig t i j)) (Θ' : TotT G (routeSmall t i j)) (hΘ : IsMatched B t ρ i j Θ Θ'),
    ∀ d ∈ Θ.support, ∀ (g : GA D (G.V (.grid i (j + 1)))) (g₁ : GA D (G.V (.grid (i + 1) j))),
      ∃ (ε : Bool) (X : HSp D) (χ χ' : (AE D)ˣ →* Circle) (ω : WRep (G.V (.grid (i + 1) (j + 1))) X),
        IsWeil W.ψ ε _ X χ χ' ω ∧ X.rank = (G.V (.grid i (j + 1))).rank + (G.V (.grid (i + 1) j)).rank ∧
        ∃ Φ : WO (sgn ε (G.V (.grid (i + 1) (j + 1)))) X → ℂ, IsThetaFunO W.ψ (sgn ε _) X Φ ∧
          ∃ (h : GA D X) (c : ℂ), ∀ u, W.kerA (.right i (j + 1)) d.1.2 g u * W.kerA (.down t (i + 1) j) d.2 u g₁ =
            c * thetaKO ω u h Φ := by
  intro D T L sc G μ₀ hL W B ρ t i j hT M hM Θ Θ' hΘ d hd g g₁
  obtain ⟨hf₁, hf₂⟩ := data_theta W B ρ t i j hΘ d hd
  have hp1 : (Pair.chi (i : ℕ) ((j : ℕ) + 1) : Pair T).InRange D.R.m := ⟨by omega, by omega⟩
  have hp2 : (Pair.mu t ((i : ℕ) + 1) (j : ℕ)).InRange D.R.m := ⟨by omega, by omega⟩
  obtain ⟨X, χ, χ', ω, hω, hX, Φ, hΦ, h, c, hc⟩ :=
    seesaw_product W.ψ_std (W.om_is _ hp1) (W.om_is _ hp2) hf₁ hf₂ g g₁
  exact ⟨true, X, χ, χ', ω, hω, hX, Φ, hΦ, h, c, hc⟩

end
