import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.WellChosen
import Development.AbelianVarietyTheory.Definitions.Divisors.P22
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArcZeroZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFramePointEigenframe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLieEigenspaceFrameFlagCoverChartDomain
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open Filter Topology
open GlobalTheory.ShFam GlobalTheory.ShFam.BdArc GlobalTheory.Toroidal

open MonoidalCategory CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompHS.BridgeValue

theorem exists_gen_unit {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {S : Type} [CommRing S] [Algebra c.F S]
    (P P' : FrPt Xo c S) (e : P'.x = P.x) : ∃ u : Sˣ, ∀ i, (e ▸ P'.s).f i = scal P.x (u : S) i * P.s.f i := by
  obtain ⟨x', xo', v', t1', t2', t3', s', t4'⟩ := P'
  dsimp only at e
  subst e
  exact gen_unit P.s s' P.gen t4'

end GlobalTheory.CompHS.BridgeValue

namespace GlobalTheory.CompHS.BridgeValue

theorem val_sec₀_eq_evR : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} (TF : TorFlag Xo c) (Z : Comp Xo c) (la : AllWt.Weight Dw) (σ : c.F →+* ℂ) (W : (Y₀ TF.X Z).Opens) (hW : IsAffineOpen W) (i : (L₀ TF.X Z la).ι) (φ : c.F →+* Γ(Y₀ TF.X Z, W)) (x : Sp Γ(Y₀ TF.X Z, W) ⟶ gen TF.Y) (hx : ((show Sp Γ(Y₀ TF.X Z, W) ⟶ Y₀ TF.X Z from hW.fromSpec) ≫ inc₀ TF.X Z) ≫ TF.X.π = x ≫ genι TF.Y) (hz : ⊤ ≤ ((show Sp Γ(Y₀ TF.X Z, W) ⟶ Y₀ TF.X Z from hW.fromSpec) ≫ inc₀ TF.X Z) ⁻¹ᵁ TF.X.F.U (i PUnit.unit)) (fr : GlobalTheory.ShFam.EigFrame TF.Y φ (x ≫ genι TF.Y)), (∀ (τ : E →+* ℂ) (j : Fin (Dw.mult τ)), fr.v τ j = (ReciprocityTheory.ChartRestriction.G.PullbackSections.tv (TF.X.F.vecAt (i PUnit.unit) _ hz hx τ j)).left) → ∀ (ψ : Γ(Y₀ TF.X Z, W) →+* ℂ) (y : FrPt Xo c (CAt σ)), ψ.comp φ = σ → GlobalTheory.ShFam.BdArc.Matches fr ψ y → ∀ (g : AllWt.secZ Xo c (AllWt.exOf Dw la 0)) (hO : ⊤ ≤ (spMap ψ ≫ (show Sp Γ(Y₀ TF.X Z, W) ⟶ Y₀ TF.X Z from hW.fromSpec)) ⁻¹ᵁ U₀ TF.X Z) (hi : ⊤ ≤ (spMap ψ ≫ (show Sp Γ(Y₀ TF.X Z, W) ⟶ Y₀ TF.X Z from hW.fromSpec)) ⁻¹ᵁ (L₀ TF.X Z la).U i), H0.val (spMap ψ ≫ (show Sp Γ(Y₀ TF.X Z, W) ⟶ Y₀ TF.X Z from hW.fromSpec)) i hO hi (sec₀ TF.X Z _ g) = toC (evR Xo c g.1 y) := by
  intro E _ _ _ H Dw l Xo c TF Z la σ W hW i φ x hx hz fr hfr ψ y hψ hm g hO hi
  let k := i PUnit.unit
  let ψ' : Γ(Y₀ TF.X Z, W) →+* CAt σ := ψ
  let q : Sp Γ(Y₀ TF.X Z, W) ⟶ TF.X.YY := (show Sp Γ(Y₀ TF.X Z, W) ⟶ Y₀ TF.X Z from hW.fromSpec) ≫ inc₀ TF.X Z
  let z' : Sp (CAt σ) ⟶ TF.X.YY := spMap ψ' ≫ q
  have hz' : ⊤ ≤ z' ⁻¹ᵁ TF.X.F.U k := GlobalTheory.FlagMod.le_preimage_comp _ hz
  have hO' : ⊤ ≤ z' ⁻¹ᵁ flagOpen TF.X := fun s hs => hO hs
  have hpt : AllWt.ptF y = GlobalTheory.FlagMod.frX y := rfl
  have ex : spMap ψ' ≫ (x ≫ genι TF.Y) = z' ≫ TF.X.π := by
    rw [← hx]; exact (Category.assoc _ _ _).symm
  have hxy : GlobalTheory.FlagMod.frX y ≫ TF.Y.j = z' ≫ TF.X.π := by
    calc GlobalTheory.FlagMod.frX y ≫ TF.Y.j = (AllWt.ptF y ≫ TF.Y.jQ) ≫ genι TF.Y := by rw [Category.assoc]; rfl
    _ = spMap ψ' ≫ (x ≫ genι TF.Y) := by rw [hm.1, Category.assoc]
    _ = z' ≫ TF.X.π := ex
  obtain ⟨Q, hQ⟩ := TF.X.top.exists_chartFr (GlobalTheory.FlagMod.frX_snd y) hxy.symm k hz'
  have hv : ∀ τ j, GlobalTheory.FlagMod.frVec TF.Y y hxy τ j = GlobalTheory.FlagMod.frVec TF.Y Q hQ.over τ j := fun τ j => by
    rw [hQ.frVec_eq rfl hQ.over τ]
    refine (GlobalTheory.FlagMod.toModel_eq_iff _ _ _ _ _).2 ?_
    obtain ⟨w, h1, h2, h3⟩ := hm.2 τ j
    refine ⟨w, h1, h2, h3.trans ?_⟩
    rw [hfr τ j, ← TF.X.F.tanPull_vecAt k ψ' q hz hz' hx rfl ex]
    rfl
  have eQ : y.x = Q.x := by
    rw [← GlobalTheory.FlagMod.frX_fst, ← GlobalTheory.FlagMod.frX_fst,
      GlobalTheory.FlagMod.xF_ext (Y := TF.Y) (GlobalTheory.FlagMod.frX_snd y) (GlobalTheory.FlagMod.frX_snd Q) (hxy.trans hQ.over.symm)]
  obtain ⟨u0, hu0⟩ := exists_gen_unit Q y eQ
  let t : Ix Dw → (CAt σ)ˣ := fun ix => ix.elim u0 fun _ => 1
  have ht : FrBor t Q y := GlobalTheory.FlagMod.frBor_of_frVec (TF.X.F.inM hz' rfl) hQ.over hxy t (fun _ => 1)
    (fun _ => Matrix.blockTriangular_one) (fun _ i => Matrix.one_apply_eq i)
    (fun τ j => by
      rw [hv τ j]
      refine ((Fintype.sum_eq_single j fun j' hj' => ?_).trans ?_).symm
      · show (1 : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) (CAt σ)) j' j • _ = 0
        rw [Matrix.one_apply_ne hj', zero_smul]
      · show (1 : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) (CAt σ)) j j • _ = _
        rw [Matrix.one_apply_eq, one_smul]) (fun _ => hu0)
  have he := evR_eq_val_secOf (X := TF.X) g hO' hQ ht
  have hprod : (∏ ix, t ix ^ AllWt.exOf Dw la 0 ix) = 1 := by
    rw [Fintype.prod_option, GlobalTheory.FlagMod.exOf_none, zpow_zero, _root_.one_mul]
    exact Finset.prod_eq_one fun _ _ => one_zpow _
  rw [hprod, Units.val_one, _root_.one_mul] at he
  have key : ∀ (a b : Sp (CAt σ) ⟶ TF.X.YY), a = b → ∀ hOa hia hOb hib,
      H0.val (B := TF.X.LL (AllWt.exOf Dw la 0)) a k hOa hia (secOf TF.X _ g) =
        H0.val (B := TF.X.LL (AllWt.exOf Dw la 0)) b k hOb hib (secOf TF.X _ g) := by
    intro a b hab; subst hab; intros; rfl
  refine (H0.val_pull (inc₀ TF.X Z) le_rfl _ i hO hi (fun s hs => hO' hs) (fun s hs => hz' hs) _).trans ?_
  refine (key _ _ (Category.assoc _ _ _) _ _ hO' hz').trans ?_
  exact he.symm

end GlobalTheory.CompHS.BridgeValue
