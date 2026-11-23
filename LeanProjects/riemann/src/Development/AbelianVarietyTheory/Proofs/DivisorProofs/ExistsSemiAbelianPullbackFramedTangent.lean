import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTransl
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.FramedTransport

theorem exists_model_pullback : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (U : TF.Y.X.affineOpens) (n : ℕ) (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (v : Fin n → (Sp (DualNumber Γ(TF.Y.X, U.1)) ⟶ TF.Y.t.G.left)) (K : Type) [Field K] [Algebra c.F K] (P : FrPt Xo c K) (hU : ⊤ ≤ (frX P ≫ TF.Y.j) ⁻¹ᵁ U.1), IsBaseFrame TF U e v P hU → ∀ (y' : Sp (DualNumber K) ⟶ Xo.XF c), y' ≫ pullback.snd _ _ = spMap (algebraMap c.F (DualNumber K)) → GlobalTheory.DeRham.epsRed K ≫ y' = frX P → ∀ (A : Over (Sp K)) [GrpObj A] (A' : Over (Sp (DualNumber K))) [GrpObj A'] (π : A.left ⟶ Xo.univ.t.G.left) (π' : A'.left ⟶ Xo.univ.t.G.left) (i : A.left ⟶ A'.left) (ub : ∀ σ : E →+* ℂ, Fin (Dw.mult σ) → (epsR K ⟶ A)), IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i → IsGrpPullback A Xo.univ.t.G P.x π → IsGrpPullback A' Xo.univ.t.G (y' ≫ pullback.fst _ _) π' → i ≫ π' = π → (∀ σ k, (ub σ k).left ≫ π = P.u σ k) → ∃ (ι : A.left ⟶ TF.Y.t.G.left) (ι' : A'.left ⟶ TF.Y.t.G.left), IsGrpPullback A TF.Y.t.G (frX P ≫ TF.Y.j) ι ∧ IsGrpPullback A' TF.Y.t.G (y' ≫ TF.Y.j) ι' ∧ i ≫ ι' = ι ∧ (∀ σ k, (ub σ k).left ≫ ι = spMap (dualMap (ev (frX P ≫ TF.Y.j) U.1 hU)) ≫ v (e ⟨σ, k⟩)) ∧ LBIso (TF.Y.t.PP.L.pull ι) (Xo.univ.t.PP.L.pull π) ∧ ⨆ k, (Xo.univ.t.PP.L.pull π).U k = ⊤ := by
  intro E _ _ _ H Dw l Xo c TF U n e v K _ _ P hU hB y' hy' hred A _ A' _ π π' i ub hi hπ hπ' hiπ hub
  have hx : frX P ≫ pullback.fst _ _ = P.x := pullback.lift_fst _ _ _
  have hπ0 : IsGrpPullback A Xo.univ.t.G (frX P ≫ pullback.fst _ _) π := hπ.congr hx.symm rfl
  have w0 : π ≫ Xo.univ.t.G.hom = (A.hom ≫ frX P) ≫ pullback.fst _ _ := by
    rw [hπ0.1.w, Category.assoc]
  have w1 : π' ≫ Xo.univ.t.G.hom = (A'.hom ≫ y') ≫ pullback.fst _ _ := by
    rw [hπ'.1.w, Category.assoc]
  let lam := TF.Y.m0.cart.1.lift π (A.hom ≫ frX P) w0
  let lam' := TF.Y.m0.cart.1.lift π' (A'.hom ≫ y') w1
  have hl0 : lam ≫ TF.Y.m0.φ = π := TF.Y.m0.cart.1.lift_fst _ _ _
  have hl0' : lam' ≫ TF.Y.m0.φ = π' := TF.Y.m0.cart.1.lift_fst _ _ _
  have hs : lam ≫ TF.Y.oF.t.G.hom = A.hom ≫ frX P := TF.Y.m0.cart.1.lift_snd _ _ _
  have hs' : lam' ≫ TF.Y.oF.t.G.hom = A'.hom ≫ y' := TF.Y.m0.cart.1.lift_snd _ _ _
  have g1 : IsGrpPullback A TF.Y.oF.t.G (frX P) lam :=
    IsGrpPullback.cancel TF.Y.m0.cart (hπ0.congr rfl hl0.symm) hs
  have g1' : IsGrpPullback A' TF.Y.oF.t.G y' lam' :=
    IsGrpPullback.cancel TF.Y.m0.cart (hπ'.congr rfl hl0'.symm) hs'
  have hil : i ≫ lam' = lam := by
    apply TF.Y.m0.cart.1.hom_ext
    · rw [Category.assoc, hl0', hiπ, hl0]
    · rw [Category.assoc, hs', hs, ← Category.assoc, hi.1.w, Category.assoc, hred]
  obtain ⟨w, hw, -⟩ := TF.Y.m.lin
  obtain ⟨w0', hw0, -⟩ := TF.Y.m0.lin
  have i1 : LBIso (TF.Y.oF.t.PP.L.pull lam) (TF.Y.t.PP.L.pull (lam ≫ TF.Y.m.φ)) :=
    LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull _ lam lam rfl)
      (chartPullSame _ (fun _ => lam ≫ TF.Y.m.φ) (fun _ => TF.Y.m.φ) (fun _ => 1) lam (fun _ => rfl)) ⟨w, hw⟩
  have i2 : LBIso (TF.Y.oF.t.PP.L.pull lam) (Xo.univ.t.PP.L.pull (lam ≫ TF.Y.m0.φ)) :=
    LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull _ lam lam rfl)
      (chartPullSame _ (fun _ => lam ≫ TF.Y.m0.φ) (fun _ => TF.Y.m0.φ) (fun _ => 1) lam (fun _ => rfl)) ⟨w0', hw0⟩
  rw [hl0] at i2
  refine ⟨lam ≫ TF.Y.m.φ, lam' ≫ TF.Y.m.φ, g1.comp TF.Y.m.cart, g1'.comp TF.Y.m.cart, ?_, ?_, ?_, ?_⟩
  · rw [← Category.assoc, hil]
  · intro σ k
    rw [← hB σ k]
    unfold frVec
    rw [FlagMod.toModel_left, ← Category.assoc]
    congr 1
    apply TF.Y.m0.cart.1.hom_ext
    · rw [Category.assoc, hl0, hub, FlagMod.liftTan_univ]
    · rw [Category.assoc, hs, ← Category.assoc, Over.w (ub σ k), FlagMod.liftTan_over]
      rfl
  · exact LBIso.trans (pull_isLB TF.Y.t.PP.isLB _) (pull_isLB TF.Y.oF.t.PP.isLB _)
      (pull_isLB Xo.univ.t.PP.isLB _) i1.symm i2
  · exact (pull_isLB Xo.univ.t.PP.isLB π).cover

end GlobalTheory.FramedTransport
