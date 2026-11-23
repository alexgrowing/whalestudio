import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairBaseIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalAdaptedSections
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagMatrixUniqueUpToTriangular
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagMatrixOfAdaptedCoordinates
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagMatrixChangeOfFrame
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ArLieBase
open GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TwoLat GlobalTheory.FlagCov
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagMove

open GlobalTheory.FlagCls GlobalTheory.TangentOrigin GlobalTheory.ShFam.Pad.Guard

section Bundle

variable {B Y : Scheme.{0}} {M M' : B.Modules} {r : ℕ}

theorem repr_map [M.IsQuasicoherent] [M'.IsQuasicoherent] (π : Y ⟶ B) (g : M ⟶ M') {V : B.Opens}
    {f : Fin r → Γ(M, V)} {f' : Fin r → Γ(M', V)} (hf : IsFrame f) (hf' : IsFrame f') {W : Y.Opens}
    (h : W ≤ π ⁻¹ᵁ V) (s : Γ((Scheme.Modules.pullback π).obj M, W)) (b : Fin r) :
    ((hf'.pullback π).basis h).repr (((Scheme.Modules.pullback π).map g).app W s) b =
      ∑ a, ((hf.pullback π).basis h).repr s a *
        π.appLE _ W h ((hf'.basis le_rfl).repr (Twist.resM M' le_rfl (g.app V (f a))) b) := by
  have e (a : Fin r) : (hf.pullback π).basis h a = QCoh.pullbackSections π M h (f a) := by
    rw [IsFrame.basis_apply]
    exact QCoh.res_pullbackSections π M _ _ _
  conv_lhs => rw [← ((hf.pullback π).basis h).sum_repr s]
  rw [← QCoh.appLinear_apply, map_sum, map_sum, Finsupp.finsetSum_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_smul, map_smul, Finsupp.smul_apply, smul_eq_mul, e, QCoh.appLinear_apply,
    QCoh.pullback_map_app_pullbackSections, Twist.resM_self]
  exact congrArg (_ * ·) (hf'.pullback_basis_repr π le_rfl h _ b)

theorem flagMat_map (hM : IsVB M r) (hM' : IsVB M' r) (π : Y ⟶ B) (g : M ⟶ M')
    {F : Vert.Flag ((Scheme.Modules.pullback π).obj M) r} {F' : Vert.Flag ((Scheme.Modules.pullback π).obj M') r}
    (hc : Compat ((Scheme.Modules.pullback π).map g) F F') {V : B.Opens}
    {f : Fin r → Γ(M, V)} {f' : Fin r → Γ(M', V)} (hf : IsFrame f) (hf' : IsFrame f')
    {K : Type} [CommRing K] [IsLocalRing K] (y : Sp K ⟶ Y) (hV : ⊤ ≤ (y ≫ π) ⁻¹ᵁ V)
    {d U : Matrix (Fin r) (Fin r) K} (hd : FlagMat hM π F hf y d) (hU : IsUnit U.det)
    (hU' : ∀ a b, U a b =
      evalPt (y ≫ π) V hV ((hf'.basis le_rfl).repr (Twist.resM M' le_rfl (g.app V (f a))) b)) :
    FlagMat hM' π F' hf' y (d * U) := by
  have := hM.isQuasicoherent
  have := hM'.isQuasicoherent
  obtain ⟨W, s, hWV, hp, hs⟩ := exists_adapted Y _ r F (y (IsLocalRing.closedPoint K)) (π ⁻¹ᵁ V)
    (hV (Set.mem_univ (IsLocalRing.closedPoint K)))
  have hy : ⊤ ≤ y ⁻¹ᵁ W := (Scheme.preimage_eq_top_of_closedPoint_mem y hp).ge
  obtain ⟨T, hT, eT⟩ := hd.adapted_eq hWV hy hs
  have uS : IsUnit (T * d).det := eT ▸ AdaptMat.isUnit_det (hf.pullback π) hWV hs.1 (evalPt y W hy)
  obtain ⟨A, hA⟩ := (flagMat_local B Y M' r hM' π F' V f' hf' K y hV).1
  have h : ∀ i : Fin r, ∃ cf : Fin r → K, (∀ l : Fin r, i < l → cf l = 0) ∧
      Matrix.vecMul (coordAt hM π hf y hWV hy (s i)) U = Matrix.vecMul cf A := by
    intro i
    obtain ⟨t, -, ht⟩ := hs.2 i.succ
    obtain ⟨τ, hτ⟩ := hc i.succ
    obtain ⟨cf, h1, h2⟩ := hA.2 i.succ W hWV (τ.app W (t (Fin.last i))) hy
    refine ⟨cf, fun l hl => h1 l hl, ?_⟩
    have e : (F'.ι i.succ).app W (τ.app W (t (Fin.last i))) = ((Scheme.Modules.pullback π).map g).app W (s i) := by
      refine (QCoh.app_app _ _ _ _).trans ?_
      rw [hτ]
      exact (QCoh.app_app _ _ _ _).symm.trans (congrArg _ (ht (Fin.last i)))
    rw [← h2, e]
    funext b
    simp only [coordAt, Matrix.vecMul, dotProduct]
    rw [repr_map π g hf hf', map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [map_mul, FlagSec.evalPt_appLE π y _ _ hWV hy hV, hU']
  choose T' h1 h2 using h
  have e : T * d * U = Matrix.of T' * A := by
    rw [← eT]
    ext i j
    exact congrFun (h2 i) j
  have uT : IsUnit T.det := by
    rw [Matrix.det_mul] at uS
    exact isUnit_of_mul_isUnit_left uS
  have uT' : IsUnit (Matrix.of T').det := by
    have := uS.mul hU
    rw [← Matrix.det_mul, e, Matrix.det_mul] at this
    exact isUnit_of_mul_isUnit_left this
  have := (hA.mul uT' h1).mul (Matrix.isUnit_nonsing_inv_det _ uT) (lower_inv uT hT)
  rwa [← e, Matrix.mul_assoc T, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ uT, Matrix.one_mul] at this

end Bundle

section Eig

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
  {Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H}
  {Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l} {c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l} {Oz : Type} [CommRing Oz]
  {β : Oz →+* c.F} {Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β}
  {K : Type} [CommRing K] {φ : c.F →+* K} {x : Sp K ⟶ Z.X} {τ : E →+* ℂ} {m : ℕ}
  {u u' : Fin m → (Sp (DualNumber K) ⟶ Z.t.G.left)}

attribute [local instance] Over.cartesianMonoidalCategory in

theorem isEigTan_comb (hu : ∀ j, IsEigTan Z φ x τ (u j)) {cf : Fin m → K} {w : Sp (DualNumber K) ⟶ Z.t.G.left}
    (h : IsCombAtG Z.t x u cf w) : IsEigTan Z φ x τ w := by
  refine ⟨comb_tan (fun j => (hu j).1) h, fun a => ?_⟩
  rw [← (isCombAtG_iff Z.t _ (fun j => ovT (hu j).1) _ _).1 h]
  have := Z.t.act.hom a
  exact congrArg (fun f => f.left) (combT_eig _ (fun j => ovT (hu j).1) (Z.t.act.act a) _
    (fun j => Over.OverMorphism.ext ((hu j).2 a)) cf)

theorem exists_coord (hu : IsEigBasis Z φ x τ u) (hu' : IsEigBasis Z φ x τ u') {U : Matrix (Fin m) (Fin m) K}
    (hU : ∀ a, IsCombAtG Z.t x u' (U a) (u a)) {cf : Fin m → K} {w : Sp (DualNumber K) ⟶ Z.t.G.left}
    (h : IsCombAtG Z.t x u' cf w) : ∃ d, IsCombAtG Z.t x u d w ∧ cf = Matrix.vecMul d U := by
  obtain ⟨d, hd, -⟩ := hu.2 w (isEigTan_comb hu'.1 h)
  refine ⟨d, hd, ?_⟩
  have := tanLinG u' (fun j => (hu'.1 j).1) u U.transpose d w hU hd
  rw [Matrix.mulVec_transpose] at this
  exact FlagSec.indep_of_isEigBasis hu' _ _ _ h this

theorem isUnit_det_trans (hu : IsEigBasis Z φ x τ u) (hu' : IsEigBasis Z φ x τ u') {U : Matrix (Fin m) (Fin m) K}
    (hU : ∀ a, IsCombAtG Z.t x u' (U a) (u a)) : IsUnit U.det := by
  rw [← Matrix.isUnit_iff_isUnit_det, ← Matrix.vecMul_surjective_iff_isUnit]
  intro cf
  obtain ⟨w, -, hw⟩ := exists_comb (fun j => (hu'.1 j).1) cf
  obtain ⟨d, -, hd⟩ := exists_coord hu hu' hU hw
  exact ⟨d, hd.symm⟩

theorem exists_mat (hu : IsEigBasis Z φ x τ u) (hu' : IsEigBasis Z φ x τ u') {U : Matrix (Fin m) (Fin m) K}
    (hU : ∀ a, IsCombAtG Z.t x u' (U a) (u a)) {d' : Matrix (Fin m) (Fin m) K}
    {v : Fin m → (Sp (DualNumber K) ⟶ Z.t.G.left)} (h : ∀ i, IsCombAtG Z.t x u' (d' i) (v i)) :
    ∃ d : Matrix (Fin m) (Fin m) K, (∀ i, IsCombAtG Z.t x u (d i) (v i)) ∧ d' = d * U := by
  choose d h1 h2 using fun i => exists_coord hu hu' hU (h i)
  refine ⟨Matrix.of d, h1, ?_⟩
  ext i j
  exact congrFun (h2 i) j

end Eig

theorem flagMat_move : ∀ (D : D7) (O : Setup D) (c : O.s.Comp) (Bs Bg : Scheme.{0}) (jB : Bg ⟶ Bs) (πB : Bg ⟶ gen O.s.T.Z)
    (Y X Gs : Scheme.{0}) [IsIntegral X] [IsIntegral Gs] (π : Y ⟶ Bs) (ρ : X ⟶ Y) (j : Gs ⟶ X)
    (πG : Gs ⟶ (O.var c).X) (φ : (O.var c).Fn →+* Gs.functionField) (jG : Gs ⟶ Bg),
    Gs.fromSpecStalk (genericPoint Gs) ≫ πG = spMap φ ≫ (O.var c).X.fromSpecStalk (genericPoint (O.var c).X) →
    jG ≫ jB = j ≫ ρ ≫ π → jG ≫ πB = πG ≫ (O.Φ.C c).π → ∀ (σ : D.host.E →+* ℂ) (M : Bs.Modules) (hM : IsVB M (O.S.Dw.mult σ)) (t : FrAssign O.s.T.Z M (O.S.Dw.mult σ) jB)
    (_ : IsLieFrames O.s.T.Z O.κ.e jB πB M _ σ false t)
    (F : Vert.Flag ((Scheme.Modules.pullback ρ).obj ((Scheme.Modules.pullback π).obj M)) (O.S.Dw.mult σ)) (M' : Bs.Modules) (hM' : IsVB M' (O.S.Dw.mult σ)) (t' : FrAssign O.s.T.Z M' (O.S.Dw.mult σ) jB)
    (_ : IsLieFrames O.s.T.Z O.κ.e jB πB M' _ σ false t')
    (F' : Vert.Flag ((Scheme.Modules.pullback ρ).obj ((Scheme.Modules.pullback π).obj M')) (O.S.Dw.mult σ)) (u : M ⟶ M'), Matches O.s.T.Z jB πB u t t' →
    Compat ((Scheme.Modules.pullback ρ).map ((Scheme.Modules.pullback π).map u)) F F' →
    (∀ (V : Bs.Opens) (f : Fin (O.S.Dw.mult σ) → Γ(M, V)) (hf : IsFrame f)
      (hxV : ⊤ ≤ ((genPt Gs ≫ jG) ≫ jB) ⁻¹ᵁ V) (d : Matrix (Fin (O.S.Dw.mult σ)) (Fin (O.S.Dw.mult σ)) Gs.functionField),
      (∀ i, IsCombAtG O.s.T.Z.t (genPt Gs ≫ jG ≫ πB ≫ genι O.s.T.Z) (t V f hf Gs.functionField (genPt Gs ≫ jG) hxV) (d i)
        (spMap (dualMap φ) ≫ (O.Φ.C c).f0.v σ i)) →
      haveI := hM.isQuasicoherent
      GlobalTheory.FlagCls.FlagMat (hM.pullback π) ρ F (hf.pullback π) (genPt Gs ≫ j) d) →
    (∀ (V : Bs.Opens) (f : Fin (O.S.Dw.mult σ) → Γ(M', V)) (hf : IsFrame f)
      (hxV : ⊤ ≤ ((genPt Gs ≫ jG) ≫ jB) ⁻¹ᵁ V) (d : Matrix (Fin (O.S.Dw.mult σ)) (Fin (O.S.Dw.mult σ)) Gs.functionField),
      (∀ i, IsCombAtG O.s.T.Z.t (genPt Gs ≫ jG ≫ πB ≫ genι O.s.T.Z) (t' V f hf Gs.functionField (genPt Gs ≫ jG) hxV) (d i)
        (spMap (dualMap φ) ≫ (O.Φ.C c).f0.v σ i)) →
      haveI := hM'.isQuasicoherent
      GlobalTheory.FlagCls.FlagMat (hM'.pullback π) ρ F' (hf.pullback π) (genPt Gs ≫ j) d) := by
  intro D O c Bs Bg jB πB Y X Gs _ _ π ρ j πG φ jG _ h1 _ σ M hM t ht F M' hM' t' ht' F' u hm hc H V f' hf' hxV d' hd'
  have := hM.isQuasicoherent
  have := hM'.isQuasicoherent
  have hz : ((genPt Gs ≫ j) ≫ ρ) ≫ π = (genPt Gs ≫ jG) ≫ jB := by simp only [Category.assoc, h1]
  obtain ⟨V₁, f, -, hp, hV, hf⟩ := hM.exists_affine (hxV (Set.mem_univ (IsLocalRing.closedPoint Gs.functionField)))
  have hx₁ : ⊤ ≤ ((genPt Gs ≫ jG) ≫ jB) ⁻¹ᵁ V₁ := (Scheme.preimage_eq_top_of_closedPoint_mem _ hp).ge
  have hxx : ⊤ ≤ ((genPt Gs ≫ jG) ≫ jB) ⁻¹ᵁ (V ⊓ V₁) := fun p hp => ⟨hxV hp, hx₁ hp⟩
  have hg := hf'.res hV
  have hψ : (genPt Gs ≫ jG) ≫ πB ≫ genStr O.s.T.Z ≫ spMap O.κ.e.toRingHom = spMap
    (Spec.preimage ((genPt Gs ≫ jG) ≫ πB ≫ genStr O.s.T.Z ≫ spMap O.κ.e.toRingHom)).hom := (Spec.map_preimage _).symm
  have b₁ := ht.1 V₁ f hf _ _ hx₁ _ hψ
  have b₂ := ht'.1 V₁ _ hg _ _ hx₁ _ hψ
  have b₃ := ht'.1 V f' hf' _ _ hxV _ hψ
  have m₁ := hm V₁ f _ hf hg _ _ hx₁
  have m₂ := ht'.2.1 V V₁ f' _ hf' hg _ _ hxV hx₁ hxx
  rw [Category.assoc _ jG (πB ≫ genι _)] at b₁ b₂ b₃ m₁ m₂
  obtain ⟨d₁, hd₁, rfl⟩ := exists_mat b₂ b₃ (U := Matrix.of fun a b => evalPt _ (V ⊓ V₁) hxx (trCo hf' _ b a)) m₂ hd'
  obtain ⟨d, hd, rfl⟩ := exists_mat b₁ b₂ (U := Matrix.of _) m₁ hd₁
  have hy₁ : ⊤ ≤ ((genPt Gs ≫ j) ≫ ρ) ⁻¹ᵁ (π ⁻¹ᵁ V₁) := by rw [← Scheme.Hom.comp_preimage, hz]; exact hx₁
  have hy : ⊤ ≤ ((genPt Gs ≫ j) ≫ ρ) ⁻¹ᵁ (π ⁻¹ᵁ V) := by rw [← Scheme.Hom.comp_preimage, hz]; exact hxV
  have hyy : ⊤ ≤ ((genPt Gs ≫ j) ≫ ρ) ⁻¹ᵁ (π ⁻¹ᵁ V ⊓ π ⁻¹ᵁ V₁) := fun p hp => ⟨hy hp, hy₁ hp⟩
  have key (U : Bs.Opens) (W : Y.Opens) (e : W ≤ π ⁻¹ᵁ U) (hW : ⊤ ≤ ((genPt Gs ≫ j) ≫ ρ) ⁻¹ᵁ W)
      (hU : ⊤ ≤ ((genPt Gs ≫ jG) ≫ jB) ⁻¹ᵁ U) (a : Γ(Bs, U)) :
      evalPt _ W hW (π.appLE U W e a) = evalPt _ U hU a := by
    revert hU
    rw [← hz]
    exact fun hU => FlagSec.evalPt_appLE π _ U W e hW hU a
  have k₁ := flagMat_map (hM.pullback π) (hM'.pullback π) ρ _ hc (hf.pullback π) (hg.pullback π) _ hy₁
    (H V₁ f hf hx₁ d hd) (isUnit_det_trans b₁ b₂ (U := Matrix.of _) m₁) (fun a b => by
      rw [Matrix.of_apply, QCoh.pullback_map_app_pullbackSections, Twist.resM_self, Twist.resM_self,
        hg.pullback_basis_repr π le_rfl le_rfl, key _ _ _ _ hx₁]
      rfl)
  have k₂ := (flagMat_change_frame Y X _ _ (hM'.pullback π) ρ F' _ _ (hf'.pullback π) _ _ (hg.pullback π) _ _ _ hyy _
    rfl k₁).2
  convert k₂ using 3
  funext a b
  have h'' : π ⁻¹ᵁ V ⊓ π ⁻¹ᵁ V₁ ≤ π ⁻¹ᵁ (V ⊓ V₁) := fun p hp => hp
  rw [← key _ _ h'' hyy]
  congr 1
  unfold trCo
  rw [← hf'.pullback_basis_repr π inf_le_left h'']
  congr 2
  exact (QCoh.pullbackSections_res π M' h'' inf_le_right _).trans (QCoh.res_pullbackSections π M' _ _ _).symm

end GlobalTheory.FlagMove

end
