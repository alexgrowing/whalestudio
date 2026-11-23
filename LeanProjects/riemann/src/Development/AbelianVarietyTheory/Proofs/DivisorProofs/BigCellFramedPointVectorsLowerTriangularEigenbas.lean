import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBaseFrame
import Development.AbelianVarietyTheory.Definitions.Divisors.P22
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBlockMetricDiagForm
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyValExtOfOverLa
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsCombAtGMulVec
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical

set_option autoImplicit false

noncomputable section

theorem GlobalTheory.LogPole.frVec_cell_comb : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c) (U : TF.Y.X.affineOpens) (n : ℕ) (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (v : Fin n → (Sp (DualNumber Γ(TF.Y.X, U.1)) ⟶ TF.Y.t.G.left)), IsEigBasis TF U e v → ∀ (W : (Y₀ TF.X Z).Opens) (k : TF.X.F.J) (L N : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) Γ(Y₀ TF.X Z, W)), IsCell TF Z U e v W k L N → ∀ (S : Type) [CommRing S] [Algebra c.F S] (w : FrPt Xo c S) (zw : Sp S ⟶ Y₀ TF.X Z) (hzw : ⊤ ≤ zw ⁻¹ᵁ W) (x : Sp S ⟶ TF.Y.X) (hx : frX w ≫ TF.Y.j = x) (hUx : ⊤ ≤ x ⁻¹ᵁ U.1), zw ≫ inc₀ TF.X Z = TF.X.ptY w → ∃ B : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) S, (∀ σ i j, i < j → B σ i j = 0) ∧ (∀ σ i, IsUnit (B σ i i)) ∧ ∀ σ i, IsCombAtG TF.Y.t x (fun j => spMap (dualMap (ev x U.1 hUx)) ≫ v (e ⟨σ, j⟩)) (fun j => (B σ * (L σ * N σ).map (ev zw W hzw)) i j) (tv (frVec TF.Y w hx σ i)).left := by
  intro E _ _ _ H Dw l Xo c TF Z U n e v hv W k L N h S _ _ w zw hzw x hx hUx hpt
  have hl : TF.X.F.Lies (zw ≫ inc₀ TF.X Z) w := hpt ▸ TF.X.lies_ptY w
  have hk : ⊤ ≤ (zw ≫ inc₀ TF.X Z) ⁻¹ᵁ TF.X.F.U k := GlobalTheory.FlagMod.le_preimage_map _ h.2.2.1 hzw
  have hxz' : (zw ≫ inc₀ TF.X Z) ≫ TF.X.π = zw ≫ toBase TF Z := Category.assoc _ _ _
  have hxz : zw ≫ toBase TF Z = x := hxz'.symm.trans (hl.1.trans hx)
  subst hxz
  obtain ⟨Q, hQ⟩ := TF.X.top.exists_chartFr (GlobalTheory.FlagMod.frX_snd w) hl.1 k hk
  obtain ⟨t, ht⟩ := hQ.exists_frBor hl
  choose b hb hdiag hsum using fun σ =>
    GlobalTheory.FlagMod.frVec_of_frBor (M := (TF.X.F.M k).toMChart) (TF.X.F.inM hk hxz') (hQ.over.trans hxz') hx ht σ
  refine ⟨fun σ i j => b σ j i, fun σ i j hij => hb σ hij, fun σ i => by show IsUnit (b σ i i); rw [hdiag]; exact Units.isUnit _,
    fun σ i => ?_⟩
  have hv' : ∀ j, IsTanAtG TF.Y.t (zw ≫ toBase TF Z)
      (spMap (dualMap (ev (zw ≫ toBase TF Z) U.1 hUx)) ≫ v j) := by
    intro j
    have h0 := GlobalTheory.FactorDepth.isTanAtG_map TF.Y.t (ev (zw ≫ toBase TF Z) U.1 hUx) (hv.1 j)
    rwa [LogKS.chart, GlobalTheory.FlagMod.spMap_ev _ U.2 hUx] at h0
  have hcell := h.2.2.2.2.2.2.2 S zw hzw hUx hk hxz' σ
  have h2 : IsCombAtG TF.Y.t (zw ≫ toBase TF Z)
      (fun j => (tv (TF.X.F.vecAt k (zw ≫ inc₀ TF.X Z) hk hxz' σ j)).left) (fun j => b σ j i)
      (tv (frVec TF.Y w hx σ i)).left := by
    rw [GlobalTheory.LieMet.isComb_iff, hsum σ i, hQ.frVec_eq hxz' (hQ.over.trans hxz') σ]
  have h3 := GlobalTheory.TangentLinear.isCombAtG_mulVec _ (fun j => hv' (e ⟨σ, j⟩)) _
    (Matrix.of fun m j => ev zw W hzw ((L σ * N σ) j m)) (fun j => b σ j i) _ (fun j => hcell j) h2
  convert h3 using 1
  funext m
  show ∑ j, b σ j i * ev zw W hzw ((L σ * N σ) j m) = ∑ j, ev zw W hzw ((L σ * N σ) j m) * b σ j i
  exact Finset.sum_congr rfl fun j _ => _root_.mul_comm _ _
