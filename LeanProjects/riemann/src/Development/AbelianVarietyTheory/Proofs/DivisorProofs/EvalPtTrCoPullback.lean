import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairBaseIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndepOfIsEigBasis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieFramesPullbackGeneric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagMatrixGradedQuotient
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLieEigenpartsFrameFamilyOverVariety
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ArLieBase
open GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TwoLat GlobalTheory.FlagCov
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PairCov

open GlobalTheory.ShFam.Pad.Guard GlobalTheory.TangentOrigin GlobalTheory.FlagSec GlobalTheory.FlagCls

theorem evalPt_trCo_pullback {K : Type} [CommRing K] {Bs Y : Scheme.{0}} {M : Bs.Modules} [M.IsQuasicoherent] {m : ℕ}
    (π : Y ⟶ Bs) {V V' : Bs.Opens} {f : Fin m → Γ(M, V)} {f' : Fin m → Γ(M, V')} (hf : IsFrame f)
    (y : Sp K ⟶ Y) (z : Sp K ⟶ Bs) (hz : z = y ≫ π) (hy : ⊤ ≤ y ⁻¹ᵁ (π ⁻¹ᵁ V ⊓ π ⁻¹ᵁ V'))
    (hzz : ⊤ ≤ z ⁻¹ᵁ (V ⊓ V')) (b a : Fin m) :
    evalPt y _ hy (trCo (hf.pullback π) (fun i => QCoh.pullbackSections π M le_rfl (f' i)) b a) =
      evalPt z _ hzz (trCo hf f' b a) := by
  subst hz
  have h'' : π ⁻¹ᵁ V ⊓ π ⁻¹ᵁ V' ≤ π ⁻¹ᵁ (V ⊓ V') := fun p hp => hp
  rw [← evalPt_appLE π y _ _ h'' hy hzz]
  congr 1
  have e : Twist.resM _ (inf_le_right : π ⁻¹ᵁ V ⊓ π ⁻¹ᵁ V' ≤ _) (QCoh.pullbackSections π M le_rfl (f' a)) =
      QCoh.pullbackSections π M h'' (Twist.resM M inf_le_right (f' a)) :=
    ((QCoh.pullbackSections_res π M h'' inf_le_right _).trans (QCoh.res_pullbackSections π M _ _ _).symm).symm
  unfold trCo
  rw [e]
  exact hf.pullback_basis_repr π inf_le_left h'' _ b

set_option maxHeartbeats 1000000 in

theorem exists_isFrameSecX : ∀ (D : D7) (O : Setup D) (c : O.s.Comp) (Bs Bg : Scheme.{0}) (jB : Bg ⟶ Bs) (πB : Bg ⟶ gen O.s.T.Z)
    (Y X Gs : Scheme.{0}) [IsIntegral X] [IsIntegral Gs] (π : Y ⟶ Bs) (ρ : X ⟶ Y) (j : Gs ⟶ X)
    (πG : Gs ⟶ (O.var c).X) (φ : (O.var c).Fn →+* Gs.functionField) (jG : Gs ⟶ Bg),
    Gs.fromSpecStalk (genericPoint Gs) ≫ πG = spMap φ ≫ (O.var c).X.fromSpecStalk (genericPoint (O.var c).X) →
    jG ≫ jB = j ≫ ρ ≫ π → jG ≫ πB = πG ≫ (O.Φ.C c).π → ∀ (σ : D.host.E →+* ℂ) (M : Bs.Modules) (hM : IsVB M (O.S.Dw.mult σ)) (t : FrAssign O.s.T.Z M (O.S.Dw.mult σ) jB)
    (_ : IsLieFrames O.s.T.Z O.κ.e jB πB M _ σ false t)
    (F : Vert.Flag ((Scheme.Modules.pullback ρ).obj ((Scheme.Modules.pullback π).obj M)) (O.S.Dw.mult σ)),
    (∀ (V : Bs.Opens) (f : Fin (O.S.Dw.mult σ) → Γ(M, V)) (hf : IsFrame f)
      (hxV : ⊤ ≤ ((genPt Gs ≫ jG) ≫ jB) ⁻¹ᵁ V) (d : Matrix (Fin (O.S.Dw.mult σ)) (Fin (O.S.Dw.mult σ)) Gs.functionField),
      (∀ i, IsCombAtG O.s.T.Z.t (genPt Gs ≫ jG ≫ πB ≫ genι O.s.T.Z) (t V f hf Gs.functionField (genPt Gs ≫ jG) hxV) (d i)
        (spMap (dualMap φ) ≫ (O.Φ.C c).f0.v σ i)) →
      haveI := hM.isQuasicoherent
      GlobalTheory.FlagCls.FlagMat (hM.pullback π) ρ F (hf.pullback π) (genPt Gs ≫ j) d) →
    ∀ i, ∃ r : ((F.root i).pull j).ι → Gs.functionFieldˣ, GlobalTheory.PairCov.IsFrameSecX (O := O) (c := c) σ hM jB πB t π ρ F j φ jG i r := by
  intro D O c Bs Bg jB πB Y X Gs _ _ π ρ j πG φ jG hgen h1 h2 σ M hM t ht F hA i
  have := hM.isQuasicoherent
  have := (hM.pullback π).isQuasicoherent
  obtain ⟨hu1, hu2, -⟩ := ht
  have hφ' : genPt Gs ≫ πG = spMap φ ≫ genericPt (O.var c) := hgen
  have hx0 : genPt Gs ≫ jG ≫ πB ≫ genι O.s.T.Z =
      spMap φ ≫ genericPt (O.Φ.C c).Y ≫ (O.Φ.C c).π ≫ genι O.s.T.Z := by
    rw [reassoc_of% h2]
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) hgen).trans (Category.assoc _ _ _))
  have hz : (genPt Gs ≫ jG) ≫ jB = ((genPt Gs ≫ j) ≫ ρ) ≫ π := by simp only [Category.assoc, h1]
  have hχ : (genPt Gs ≫ jG) ≫ πB ≫ genStr O.s.T.Z = spMap (φ.comp (constF O.κ.e (O.var c))) := by
    have e1 : (genPt Gs ≫ jG) ≫ πB ≫ genStr O.s.T.Z =
        spMap φ ≫ (genericPt (O.var c) ≫ (O.Φ.C c).π) ≫ genStr O.s.T.Z := by
      rw [Category.assoc, reassoc_of% h2]
      simp only [← Category.assoc]
      rw [hφ']
    rw [e1, GlobalTheory.ShFam.TieBase.genericPt_str O.κ.e (O.var c) (O.Φ.C c).π (O.Φ.C c).π_str]
    exact (Spec.map_comp _ _).symm
  obtain ⟨g, hg⟩ := GlobalTheory.ShFam.EigFrame.exists_isMap (O.Φ.C c).f0 φ (φ' := φ.comp (constF O.κ.e (O.var c)))
    (x' := genPt Gs ≫ jG ≫ πB ≫ genι O.s.T.Z) rfl (by rw [hx0])
  have hvg : (fun l => spMap (dualMap φ) ≫ (O.Φ.C c).f0.v σ l) = g.v σ := funext fun l => (hg _ l).symm
  have hvb : IsEigBasis O.s.T.Z _ _ σ (g.v σ) :=
    ⟨fun k => ⟨g.tan _ k, g.eig _ k⟩, fun w hw => g.basis _ w hw.1 hw.2⟩
  rw [← hvg] at hvb
  have hv := fun k => (hvb.1 k).1
  have hvi := indep_of_isEigBasis hvb
  have hb := fun V f hf hxV => hu1 V f hf Gs.functionField (genPt Gs ≫ jG) hxV
    ((φ.comp (constF O.κ.e (O.var c))).comp O.κ.e.toRingHom) (by
      rw [← Category.assoc πB, ← Category.assoc, hχ, ← Spec.map_comp]; rfl)
  have h3 : ((φ.comp (constF O.κ.e (O.var c))).comp O.κ.e.toRingHom).comp O.κ.e.symm.toRingHom =
      φ.comp (constF O.κ.e (O.var c)) :=
    RingHom.ext fun z => congrArg (φ.comp (constF O.κ.e (O.var c))) (O.κ.e.apply_symm_apply z)
  have hT := fun V V' f f' hf hf' hx hx' hxx => hu2 V V' f f' hf hf' Gs.functionField (genPt Gs ≫ jG) hx hx' hxx
  rw [h3] at hb
  rw [Category.assoc _ jG (πB ≫ genι _)] at hb hT
  have hut := fun V f hf hxV k => ((hb V f hf hxV).1 k).1
  have key (V : Bs.Opens) (f : Fin (O.S.Dw.mult σ) → Γ(M, V)) (hf : IsFrame f)
      (hxV : ⊤ ≤ ((genPt Gs ≫ jG) ≫ jB) ⁻¹ᵁ V) :
      ∃ d : Matrix (Fin (O.S.Dw.mult σ)) (Fin (O.S.Dw.mult σ)) Gs.functionField,
        (∀ i, IsCombAtG O.s.T.Z.t (genPt Gs ≫ jG ≫ πB ≫ genι O.s.T.Z)
          (t V f hf Gs.functionField (genPt Gs ≫ jG) hxV) (d i) (spMap (dualMap φ) ≫ (O.Φ.C c).f0.v σ i)) ∧
        FlagMat (hM.pullback π) ρ F (hf.pullback π) (genPt Gs ≫ j) d := by
    choose d hd _ using fun l => (hb V f hf hxV).2 _ (hvb.1 l)
    exact ⟨Matrix.of d, hd, hA V f hf hxV _ hd⟩
  have hA1 (k : Fin (O.S.Dw.mult σ + 1)) (V : Bs.Opens) (f : Fin (O.S.Dw.mult σ) → Γ(M, V)) (hf : IsFrame f)
      (W : X.Opens) (hWV : W ≤ ρ ⁻¹ᵁ (π ⁻¹ᵁ V)) (s : Γ(F.F k, W)) (hx : ⊤ ≤ (genPt Gs ≫ j) ⁻¹ᵁ W)
      (hxV : ⊤ ≤ ((genPt Gs ≫ jG) ≫ jB) ⁻¹ᵁ V) :
      ∃ (w : Sp (DualNumber Gs.functionField) ⟶ O.s.T.Z.t.G.left) (cf : Fin (O.S.Dw.mult σ) → Gs.functionField),
        IsCombAtG O.s.T.Z.t (genPt Gs ≫ jG ≫ πB ≫ genι O.s.T.Z) (t V f hf Gs.functionField (genPt Gs ≫ jG) hxV)
          (coordAt (hM.pullback π) ρ (hf.pullback π) (genPt Gs ≫ j) hWV hx ((F.ι k).app W s)) w ∧
        IsCombAtG O.s.T.Z.t (genPt Gs ≫ jG ≫ πB ≫ genι O.s.T.Z)
          (fun l => spMap (dualMap φ) ≫ (O.Φ.C c).f0.v σ l) cf w ∧ (∀ l : Fin (O.S.Dw.mult σ), (k : ℕ) ≤ l → cf l = 0) ∧
        ∃ d, FlagMat (hM.pullback π) ρ F (hf.pullback π) (genPt Gs ≫ j) d ∧
          coordAt (hM.pullback π) ρ (hf.pullback π) (genPt Gs ≫ j) hWV hx ((F.ι k).app W s) = Matrix.vecMul cf d := by
    obtain ⟨d, hd, hF⟩ := key V f hf hxV
    obtain ⟨cf, hc1, hc2⟩ := hF.2 k W hWV s hx
    obtain ⟨w, hw1, hw2⟩ := exists_comb_comb _ _ rfl (hut V f hf hxV) hv hd cf
    exact ⟨w, cf, hc2 ▸ hw1, hw2, hc1, d, hF, hc2⟩
  have key' := fun ch : ((F.root i).pull j).ι => exists_unit
    (fun val : Gs.functionField => ∃ (V : Bs.Opens) (f : _ → Γ(M, V)) (hf : IsFrame f) (W : X.Opens)
      (hW : W ≤ (ch PUnit.unit).U) (hWV : W ≤ ρ ⁻¹ᵁ (π ⁻¹ᵁ V)) (s : Γ(F.F i.succ, W))
      (_ : (F.π i).app W s = Twist.resM _ hW ((ch PUnit.unit).e 0))
      (hx : ⊤ ≤ (genPt Gs ≫ j) ⁻¹ᵁ W) (hxV : ⊤ ≤ ((genPt Gs ≫ jG) ≫ jB) ⁻¹ᵁ V)
      (w : Sp (DualNumber Gs.functionField) ⟶ O.s.T.Z.t.G.left) (cf : Fin (O.S.Dw.mult σ) → Gs.functionField),
      IsCombAtG O.s.T.Z.t (genPt Gs ≫ jG ≫ πB ≫ genι O.s.T.Z) (t V f hf Gs.functionField (genPt Gs ≫ jG) hxV)
        (coordAt (hM.pullback π) ρ (hf.pullback π) (genPt Gs ≫ j) hWV hx ((F.ι i.succ).app W s)) w ∧
      IsCombAtG O.s.T.Z.t (genPt Gs ≫ jG ≫ πB ≫ genι O.s.T.Z)
        (fun k => spMap (dualMap φ) ≫ (O.Φ.C c).f0.v σ k) cf w ∧ cf i = val)
    (by
      rintro _ ⟨V, f, hf, W, hW, hWV, s, hs, hx, hxV, w, cf, hw, hc, rfl⟩
      obtain ⟨w', cf', hw', hc', -, d, hF, hd⟩ := hA1 i.succ V f hf W hWV s hx hxV
      obtain rfl := comb_unique (hut V f hf hxV) hw hw'
      rw [hvi _ _ _ hc hc']
      exact FlagMat.coeff_ne_zero _ _ _ _ _ ρ F _ _ _ _ _ _ hF i (ch PUnit.unit) W hW hWV s hs hx cf' hd)
    (by
      rintro _ _ ⟨V, f, hf, W, hW, hWV, s, hs, hx, hxV, w, cf, hw, hc, rfl⟩
        ⟨V', f', hf', W', hW', hWV', s', hs', hx', hxV', w', cf', hw', hc', rfl⟩
      have hx'' : ⊤ ≤ (genPt Gs ≫ j) ⁻¹ᵁ (W ⊓ W') := fun p hp => ⟨hx hp, hx' hp⟩
      have hxx : ⊤ ≤ ((genPt Gs ≫ jG) ≫ jB) ⁻¹ᵁ (V ⊓ V') := fun p hp => ⟨hxV hp, hxV' hp⟩
      have hyy : ⊤ ≤ ((genPt Gs ≫ j) ≫ ρ) ⁻¹ᵁ (π ⁻¹ᵁ V ⊓ π ⁻¹ᵁ V') := fun p hp => ⟨hWV (hx hp), hWV' (hx' hp)⟩
      obtain ⟨s₀, hs₀⟩ := coord_rel ρ F _ _ rfl i _ (hf.pullback π) (hf'.pullback π) hW hW' hWV hWV' s s' hs hs'
        hx hx' hx'' hyy
      simp only [evalPt_trCo_pullback π hf _ _ hz hyy hxx] at hs₀
      obtain ⟨w₀, d, hw₀, hd, h0, -⟩ := hA1 i.castSucc V f hf _ (inf_le_left.trans hWV) s₀ hx'' hxV
      rw [coeff_eq (hut V f hf hxV) hv hvi (hT V V' f f' hf hf' hxV hxV' hxx) hs₀ hw hc hw' hc' hw₀ hd, Pi.add_apply,
        h0 i le_rfl, add_zero])
  choose r hr' using key'
  refine ⟨r, fun ch V f hf W hW hWV s hs hx hxV => ?_⟩
  obtain ⟨w, cf, hw, hc, h0, -⟩ := hA1 i.succ V f hf W hWV s hx hxV
  exact ⟨w, cf, hw, hc, hr' ch _ ⟨V, f, hf, W, hW, hWV, s, hs, hx, hxV, w, cf, hw, hc, rfl⟩, fun k hk => h0 k hk⟩

end GlobalTheory.PairCov

end
