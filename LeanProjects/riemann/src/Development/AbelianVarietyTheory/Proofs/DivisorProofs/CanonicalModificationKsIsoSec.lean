import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GrothendieckDeformation
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.WellChosen
import Development.AbelianVarietyTheory.Definitions.Divisors.P22
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimeSpectrumDualNumberEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvalPtAppLEOfComp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsJacobianSectionIsUnitGermOfLocalIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralSmoothProjectiveModificationOfNonempty
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBijectiveStalkMapOverDvrPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GermMemRangeStalkOfPullbackMulLocalIso

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CanonBirat

open GlobalTheory.Vanishing.H0 GlobalTheory.TangentOrigin GlobalTheory.TopForm GlobalTheory.MorJac GlobalTheory.Cartier

section General

variable {X Y : Scheme.{0}}

theorem ext_val {k : Type} [CommRing k] [IsReduced X] {q : X ⟶ Sp k} {B : LB X} {O : X.Opens} {f f' : H0 q B O}
    (h : ∀ (L : Type) [Field L] (z : Sp L ⟶ X) (hz : ⊤ ≤ z ⁻¹ᵁ O), ∃ i hi, H0.val z i hz hi f = H0.val z i hz hi f') :
    f = f' := by
  refine LB.sec_ext fun i => GlobalTheory.FlagMod.ext_ev_field fun L _ z hz => ?_
  have hO := GlobalTheory.FlagMod.le_preimage_mono inf_le_left hz
  have hi := GlobalTheory.FlagMod.le_preimage_mono inf_le_right hz
  obtain ⟨j, hj, e⟩ := h L z hO
  change H0.val z i hO hi f = H0.val z i hO hi f'
  rw [val_change z i j hO hi hj f, val_change z i j hO hi hj f', e]

theorem val_restr {k R : Type} [CommRing k] [CommRing R] {p : Y ⟶ Sp k} {B : LB Y} {O O' : Y.Opens} (x : Sp R ⟶ Y)
    (i : B.ι) (h : O' ≤ O) (hO' : ⊤ ≤ x ⁻¹ᵁ O') (hO : ⊤ ≤ x ⁻¹ᵁ O) (hi : ⊤ ≤ x ⁻¹ᵁ B.U i) (f : H0 p B O) :
    H0.val x i hO' hi (H0.restr h f) = H0.val x i hO hi f :=
  evalPt_res x (inf_le_inf_right _ h) _ _ (f.loc i)

theorem val_congr {k R : Type} [CommRing k] [CommRing R] {p : Y ⟶ Sp k} {B : LB Y} {O : Y.Opens} {x x' : Sp R ⟶ Y}
    (e : x = x') (i : B.ι) (hO : ⊤ ≤ x ⁻¹ᵁ O) (hi : ⊤ ≤ x ⁻¹ᵁ B.U i) (hO' : ⊤ ≤ x' ⁻¹ᵁ O) (hi' : ⊤ ≤ x' ⁻¹ᵁ B.U i)
    (f : H0 p B O) : H0.val x i hO hi f = H0.val x' i hO' hi' f := by
  subst e; rfl

theorem exists_jacobian {k : Type} [CommRing k] (p : Y ⟶ Sp k) (σ : X ⟶ Y) (q : X ⟶ Sp k) (hq : σ ≫ p = q) (D : ℕ)
    [SmoothOfRelativeDimension D p] [SmoothOfRelativeDimension D q] (K : CanonLB p D) (K' : CanonLB q D) :
    ∃ J : H0 q (LB.div K'.bundle (K.bundle.pull σ)) ⊤,
      (∀ x : X, Function.Bijective (σ.stalkMap x).hom → ∀ a ha, IsUnit (H0.germ a x (memTop x) ha J)) ∧
      ∀ (R : Type) [CommRing R] (z : Sp R ⟶ X) (i : K.bundle.ι) (j : K'.bundle.ι) (V : Y.Opens) (hV : V ≤ K.bundle.U i)
        (W : X.Opens) (hW : W ≤ K'.bundle.U j) (h : W ≤ σ ⁻¹ᵁ V) (g : Fin D → Γ(Y, V)) (hz : ⊤ ≤ z ⁻¹ᵁ W)
        (hzV : ⊤ ≤ (z ≫ σ) ⁻¹ᵁ V) (ha : ⊤ ≤ z ⁻¹ᵁ (LB.div K'.bundle (K.bundle.pull σ)).U (j, pIdx K.bundle σ i)),
        evalPt z W hz (K'.jacobian j hW fun a => σ.appLE V W h (g a)) =
          evalPt (z ≫ σ) V hzV (K.jacobian i hV g) *
            H0.val (B := LB.div K'.bundle (K.bundle.pull σ)) z (j, pIdx K.bundle σ i) le_top ha J := by
  subst hq
  have hB : (LB.div K'.bundle (K.bundle.pull σ)).IsLB := LB.isLB_div K'.isLB (LB.isLB_pull K.isLB σ)
  obtain ⟨J, hJ⟩ := H0.exists_of_germs (p := σ ≫ p) (O := ⊤) hB
    (fun t => (LB.div K'.bundle (K.bundle.pull σ)).U t) (fun t => t) (fun _ => le_top)
    (fun _ => le_rfl) (fun y _ => Opens.mem_iSup.1 (hB.cover.ge (Opens.mem_top y)))
    (jacLoc K K') (fun y t t' h h' => ger_jacLoc K K' y t t' h h')
  refine ⟨J, fun x hx a ha => (congrArg IsUnit (hJ a x ha)).mpr (isUnit_ger_jacLoc K K' x hx a ha), ?_⟩
  intro R _ z i j V hV W hW h g hz hzV ha
  have hWa : W ≤ (LB.div K'.bundle (K.bundle.pull σ)).U (j, pIdx K.bundle σ i) :=
    fun x hx => ⟨hW hx, mem_pIdx.2 (hV (h hx))⟩
  have e₁ : J.loc (j, pIdx K.bundle σ i) = resG X inf_le_right (jacLoc K K' (j, pIdx K.bundle σ i)) :=
    fun_ext_ger fun y hy => (hJ _ y hy.2).trans
      (ger_resG (Y := X) (inf_le_right : ⊤ ⊓ _ ≤ _) y hy (jacLoc K K' (j, pIdx K.bundle σ i))).symm
  have e₂ := coeff_pullForm_eq_mul K K' i j hV hW h (dOn p g)
  rw [pullForm_dOn] at e₂
  have e₃ : H0.val (B := LB.div K'.bundle (K.bundle.pull σ)) z (j, pIdx K.bundle σ i) le_top ha J =
      evalPt z W hz (resG X hWa (jacLoc K K' (j, pIdx K.bundle σ i))) :=
    (congrArg (evalPt z _ (le_preimage_inf le_top ha)) e₁).trans
      ((evalPt_res z inf_le_right ha _ _).trans (evalPt_res z hWa ha hz _).symm)
  rw [e₃, ← evalPt_appLE_of_comp z σ V W h _ hz hzV, ← map_mul]
  exact congrArg _ (e₂.trans (congrArg (_ * ·) (resG_jacLoc K K' (j, pIdx K.bundle σ i) hWa).symm))

abbrev jacChart {T : Scheme.{0}} {K' : LB X} {K : LB Y} {B : LB T} (σ : X ⟶ Y) (r : Y ⟶ T) (r' : X ⟶ T)
    (hr : σ ≫ r = r') (hK' : K'.IsLB) (hK : K.IsLB) (hB : B.IsLB) :
    ProdChart (LB.div K' (K.pull σ)) ((tens K (B.pull r)).pull σ) (tens K' (B.pull r')) where
  isLB₁ := LB.isLB_div hK' (LB.isLB_pull hK σ)
  isLB₂ := LB.isLB_pull (isLB_tens hK (LB.isLB_pull hB r)) σ
  isLB₃ := isLB_tens hK' (LB.isLB_pull hB r')
  τ := K'.ι × K.ι × B.ι
  a t := (t.1, pIdx K σ t.2.1)
  b t := pIdx (tens K (B.pull r)) σ (t.2.1, pIdx B r t.2.2)
  c t := (t.1, pIdx B r' t.2.2)
  cover x := by
    subst hr
    obtain ⟨i, hi⟩ := exists_chart hK' x
    obtain ⟨j, hj⟩ := exists_chart hK (σ x)
    obtain ⟨l, hl⟩ := exists_chart hB (r (σ x))
    exact ⟨(i, j, l), ⟨hi, mem_pIdx.2 hj⟩, mem_pIdx.2 ⟨hj, mem_pIdx.2 hl⟩, hi, mem_pIdx.2 hl⟩
  rule x t t' e e' := by
    subst hr
    have h₁ := mem_pull.1 e.2.1
    have h₂ := mem_pull.1 e'.2.1
    rw [tr_tens _ _ x e.2.2 e'.2.2, tr_div _ _ x e.1 e'.1, tr_pull _ σ x e.2.1 e'.2.1,
      tr_pull _ (σ ≫ r) x e.2.2.2 e'.2.2.2, tr_pull _ σ x e.1.2 e'.1.2,
      tr_tens _ _ (σ x) h₁ h₂, map_mul, mul_assoc, tr_pull _ r (σ x) h₁.2 h₂.2]
    refine congrArg (tr K' x t.1 t'.1 * ·) (Eq.trans ?_ (inv_mul_cancel_left _ _).symm)
    refine Units.ext ?_
    rw [Scheme.Hom.stalkMap_comp]
    rfl

theorem extends_iff {F : Type} [Field F] [IsIntegral Y] {p : Y ⟶ Sp F} {d : ℕ} [SmoothOfRelativeDimension d p]
    (hp : IsProjOver p) {U : Y.Opens} (hU : (U : Set Y).Nonempty) (σ : X ⟶ Y) (q : X ⟶ Sp F) (hq : σ ≫ p = q)
    (hs : SmoothOfRelativeDimension d q) (hpr : IsProjOver q) (hiso : IsIso (σ ∣_ U)) {O : X.Opens} (hO : O = σ ⁻¹ᵁ U)
    (hd : Dense (O : Set X)) {L : LB Y} (hL : L.IsLB) {P N : LB X} (C : ProdChart P (L.pull σ) N) (J : H0 q P ⊤)
    (hJ : ∀ x : X, Function.Bijective (σ.stalkMap x).hom → ∀ a ha, IsUnit (H0.germ a x (memTop x) ha J))
    (s : H0 p L U) (t : H0 q N O)
    (rel : ∀ (R : Type) [Field R] (z : Sp R ⟶ X) (hz : ⊤ ≤ z ⁻¹ᵁ O) (hz' : ⊤ ≤ (z ≫ σ) ⁻¹ᵁ U), ∃ (a : C.τ)
      (ha : ⊤ ≤ z ⁻¹ᵁ P.U (C.a a)) (_ : ⊤ ≤ z ⁻¹ᵁ (L.pull σ).U (C.b a)) (hc : ⊤ ≤ z ⁻¹ᵁ N.U (C.c a))
      (hb : ⊤ ≤ (z ≫ σ) ⁻¹ᵁ L.U (C.b a PUnit.unit)),
      H0.val z (C.c a) hz hc t = H0.val z (C.a a) le_top ha J * H0.val (z ≫ σ) (C.b a PUnit.unit) hz' hb s) :
    (∃ g : H0 p L ⊤, H0.restr le_top g = s) ↔ ∃ g : H0 q N ⊤, H0.restr le_top g = t := by
  subst hq hO
  let M : Modif p U d := ⟨X, σ, hs, hpr, hiso, hd⟩
  have : Smooth p := SmoothOfRelativeDimension.smooth d p
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian p
  have : GlobalTheory.IsNormalScheme Y := isNormalScheme_of_smooth p
  have : Nonempty U := hU.to_subtype
  have hXi : IsIntegral X := isIntegral_of_nonempty_modif F Y p U d M hU
  have hrel : C.mul (H0.restr le_top J) (H0.pull σ le_rfl s) = t := ext_val fun R _ z hz => by
    obtain ⟨a, ha, hb', hc, hb, e⟩ := rel R z hz hz
    refine ⟨C.c a, hc, ?_⟩
    rw [e, C.val_mul _ _ a z hz ha hb' hc, val_restr z _ le_top hz le_top, val_pull σ le_rfl z _ hz hb' hz hb]
  have hT : (⊤ : X.Opens) ≤ σ ⁻¹ᵁ (⊤ : Y.Opens) := le_top
  constructor
  · rintro ⟨g, rfl⟩
    refine ⟨C.mul J (H0.pull σ hT g), ?_⟩
    rw [← hrel, C.restr_mul, pull_restr]
    refine congrArg _ (ext_germ fun z hz => (exists_chart (LB.isLB_pull hL σ) z).imp fun i hi => ⟨hi, ?_⟩)
    rw [germ_restr, germ_pull, germ_pull]
  · rintro ⟨g, rfl⟩
    obtain ⟨t, ht⟩ := (exists_sec_res_eq_iff hL (W := U) (LB.coord_mem s)).2 (fun x hx1 _ => by
      have := IsNormalScheme.isDiscreteValuationRing_stalk hx1
      obtain ⟨x', rfl, hb⟩ := Modif.exists_bijective_stalkMap_of_dvr F Y p U d M hp hU x this
      obtain ⟨i, hi⟩ := exists_chart hL (σ x')
      have : Nonempty (L.U i) := ⟨⟨_, hi⟩⟩
      have hne := nonempty_inf_of_isIntegral U (L.U i)
      exact ⟨i, hne, hi, germToFunctionField_mem_range_stalk_of_mul_pull F Y X p σ U _ _ _ C J g s hrel x' hb
        (hJ x' hb) i hi⟩)
    refine ⟨H0.ofSec p ⊤ t, ?_⟩
    rw [restr_ofSec]; exact LB.sec_ext fun i => ht i

end General

section Flag

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} {X : FlagCover Y} {Z : Comp Xo c}

theorem val_canId_eq
    (hKS : ∀ (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K), GlobalTheory.FlagTan.KSIso (GlobalTheory.FlagTan.psiSet H) y)
    (M₀ M : Modif (str₀ X Z) (U₀ X Z) (dimFlag Dw)) (τ : M.X ⟶ M₀.X) (hτ : τ ≫ M₀.σ = M.σ) (ω₀ : CanId M₀) (ω : CanId M)
    {L : Type} [Field L] (z : Sp L ⟶ M.X) (i : M₀.K.bundle.ι) (j : M.K.bundle.ι) (k : X.F.J) (ho : ⊤ ≤ z ⁻¹ᵁ M.off)
    (ho₀ : ⊤ ≤ (z ≫ τ) ⁻¹ᵁ M₀.off)
    (hj : ⊤ ≤ z ⁻¹ᵁ (LB.div M.K.bundle ((L₀ X Z (GlobalTheory.FlagTan.kap Dw)).pull M.σ)).U (j, flagIdx M _ k))
    (hi : ⊤ ≤ (z ≫ τ) ⁻¹ᵁ (LB.div M₀.K.bundle ((L₀ X Z (GlobalTheory.FlagTan.kap Dw)).pull M₀.σ)).U (i, flagIdx M₀ _ k)) (u : L)
    (hu : ∀ (V : M₀.X.Opens) (hV : V ≤ M₀.K.bundle.U i) (W : M.X.Opens) (hW : W ≤ M.K.bundle.U j) (h : W ≤ τ ⁻¹ᵁ V)
      (g : Fin (dimFlag Dw) → Γ(M₀.X, V)) (hz : ⊤ ≤ z ⁻¹ᵁ W) (hzV : ⊤ ≤ (z ≫ τ) ⁻¹ᵁ V),
      evalPt z W hz (M.K.jacobian j hW fun a => τ.appLE V W h (g a)) =
        evalPt (z ≫ τ) V hzV (M₀.K.jacobian i hV g) * u) :
    H0.val (B := LB.div M.K.bundle ((L₀ X Z (GlobalTheory.FlagTan.kap Dw)).pull M.σ)) z (j, flagIdx M _ k) ho hj ω.ω =
      H0.val (B := LB.div M₀.K.bundle ((L₀ X Z (GlobalTheory.FlagTan.kap Dw)).pull M₀.σ)) (z ≫ τ) (i, flagIdx M₀ _ k) ho₀ hi ω₀.ω *
        u := by
  have eF : τ ≫ toFlag M₀ = toFlag M := by rw [toFlag, ← Category.assoc, hτ]
  have e₀ : (z ≫ τ) ≫ toFlag M₀ = z ≫ toFlag M := by rw [Category.assoc, eF]
  have hU : ⊤ ≤ (z ≫ M.σ) ⁻¹ᵁ U₀ X Z := fun s _ => by
    have := ho (Set.mem_univ s)
    rw [M.off_eq] at this
    exact this
  have hF : ⊤ ≤ (z ≫ toFlag M) ⁻¹ᵁ flagOpen X := hU
  have hk : ⊤ ≤ (z ≫ toFlag M) ⁻¹ᵁ X.F.U k := fun s _ =>
    (((common₀ X Z).pull M.σ).mem _ _ _).1 (hj (Set.mem_univ s)).2
  have hk₀ : ⊤ ≤ ((z ≫ τ) ≫ toFlag M₀) ⁻¹ᵁ X.F.U k := e₀ ▸ hk
  obtain ⟨inst, hch⟩ := exists_chartFr _ hF
  obtain ⟨Q, hQ⟩ := hch k hk
  have hQ₀ : X.F.ChartFr k ((z ≫ τ) ≫ toFlag M₀) hk₀ Q := by
    have key : ∀ (p q : Sp L ⟶ X.YY) (_ : p = q) (hp : ⊤ ≤ p ⁻¹ᵁ X.F.U k) (hq : ⊤ ≤ q ⁻¹ᵁ X.F.U k),
        X.F.ChartFr k p hp Q → X.F.ChartFr k q hq Q := by
      rintro p _ rfl _ _ hh; exact hh
    exact key _ _ e₀.symm hk hk₀ hQ
  obtain ⟨v, hv⟩ := (hKS L Q).exists_isTanFrame
  have e : z ≫ toFlag M = X.ptY Q := GlobalTheory.FlagMod.FlagCover.eq_ptY hQ.lies
  choose zv hzv hzO using fun b => exists_tanLift M (hv.isDef b) e ho
  have hzv₀ : ∀ b, (zv b ≫ τ) ≫ toFlag M₀ = X.ptY (v b) := fun b => by rw [Category.assoc, eF, hzv]
  have hpi : ptOf (z ≫ τ) ∈ M₀.K.bundle.U i := ((le_iff_ptOf_mem _ _).1 hi).1
  obtain ⟨V, f, hx, hf⟩ := exists_isFrame_dOn M₀.str (dimFlag Dw) (ptOf (z ≫ τ))
  obtain ⟨O, hO, hxO, hOV⟩ := Opens.isBasis_iff_nbhd.1 M₀.X.isBasis_affineOpens
    (show ptOf (z ≫ τ) ∈ V ⊓ M₀.K.bundle.U i from ⟨hx, hpi⟩)
  have hOV' : O ≤ V := hOV.trans inf_le_left
  have hOi : O ≤ M₀.K.bundle.U i := hOV.trans inf_le_right
  let g : Fin (dimFlag Dw) → Γ(M₀.X, O) := fun a => resG M₀.X hOV' (f a)
  have hun : IsUnit (M₀.K.jacobian i hOi g) := (M₀.K.isUnit_jacobian_iff i hO hOi g).2 (by
    have := hf.res hO hOV'
    rwa [resForm_dOn] at this)
  have hzO₀ : ⊤ ≤ (z ≫ τ) ⁻¹ᵁ O := (le_iff_ptOf_mem _ _).2 hxO
  have hzW : ⊤ ≤ z ⁻¹ᵁ (M.K.bundle.U j ⊓ τ ⁻¹ᵁ O) := fun s hs => ⟨(hj hs).1, hzO₀ hs⟩
  have hvO : ∀ b, ⊤ ≤ (zv b ≫ τ) ⁻¹ᵁ O := fun b s hs => (hzO b _ hzW hs).2
  have a₀ := canId_val_mul_det M₀ ω₀ Q v hv (z ≫ τ) (fun b => zv b ≫ τ) i k O hOi g hzO₀ hvO hk₀ ho₀ hi hQ₀ hzv₀
  have a := canId_val_mul_det M ω Q v hv z zv j k _ inf_le_left (fun a => τ.appLE O _ inf_le_right (g a)) hzW
    (fun b => hzO b _ hzW) hk ho hj hQ hzv
  have hm : (Matrix.of fun a b => (evalPt (zv (tanOrd Dw b)) _ (hzO _ _ hzW) (τ.appLE O _ inf_le_right (g a))).snd) =
      Matrix.of fun a b => (evalPt (zv (tanOrd Dw b) ≫ τ) O (hvO _) (g a)).snd :=
    Matrix.ext fun a b => congrArg TrivSqZeroExt.snd (evalPt_appLE_of_comp _ _ _ _ _ _ _ _)
  rw [hm, hu O hOi _ inf_le_left inf_le_right g hzW hzO₀, ← a₀] at a
  have hd : (Matrix.of fun a b => (evalPt (zv (tanOrd Dw b) ≫ τ) O (hvO _) (g a)).snd).det ≠ 0 := fun h0 => by
    rw [h0, mul_zero] at a₀
    exact (hun.map (evalPt (z ≫ τ) O hzO₀)).ne_zero a₀.symm
  exact mul_right_cancel₀ hd (a.trans (mul_right_comm _ _ _))

theorem extends_iff_of_hom
    (hKS : ∀ (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K), GlobalTheory.FlagTan.KSIso (GlobalTheory.FlagTan.psiSet H) y)
    (M₀ M : Modif (str₀ X Z) (U₀ X Z) (dimFlag Dw)) [IsIntegral M₀.X] (τ : M.X ⟶ M₀.X) (hτ : τ ≫ M₀.σ = M.σ)
    (hiso : IsIso (τ ∣_ M₀.off)) (ω₀ : CanId M₀) (ω : CanId M) {b s : AllWt.Weight Dw} (hs : FlagTan.kap Dw + b = s)
    (m : H0 (str₀ X Z) (L₀ X Z s) (U₀ X Z)) :
    (∃ g : H0 M₀.str (tens M₀.K.bundle ((L₀ X Z b).pull M₀.σ)) ⊤, H0.restr le_top g =
      (((common₀ X Z).pull M₀.σ).canChart M₀.K.isLB hs).mul ω₀.ω (M₀.pullOff m)) ↔
    ∃ g : H0 M.str (tens M.K.bundle ((L₀ X Z b).pull M.σ)) ⊤, H0.restr le_top g =
      (((common₀ X Z).pull M.σ).canChart M.K.isLB hs).mul ω.ω (M.pullOff m) := by
  have hq : τ ≫ M₀.str = M.str := by rw [Modif.str, ← Category.assoc, hτ]
  have hO : M.off = τ ⁻¹ᵁ M₀.off := by rw [M.off_eq, M₀.off_eq, ← Scheme.Hom.comp_preimage, hτ]
  obtain ⟨J, hJ, hJ'⟩ := exists_jacobian M₀.str τ M.str hq (dimFlag Dw) M₀.K M.K
  refine extends_iff M₀.proj (by rw [M₀.off_eq]; exact M₀.dense.nonempty) τ M.str hq M.smooth M.proj hiso hO
    (by rw [M.off_eq]; exact M.dense) (isLB_tens M₀.K.isLB (LB.isLB_pull (isLB_L₀ X Z b) _))
    (jacChart τ M₀.σ M.σ hτ M.K.isLB M₀.K.isLB (isLB_L₀ X Z b)) J hJ _ _ fun R _ z hz hz₀ => ?_
  have e : (z ≫ τ) ≫ M₀.σ = z ≫ M.σ := by rw [Category.assoc, hτ]
  obtain ⟨i, hi⟩ := exists_chart M₀.K.isLB (ptOf (z ≫ τ))
  obtain ⟨j, hj⟩ := exists_chart M.K.isLB (ptOf z)
  obtain ⟨k, hk⟩ := (common₀ X Z).cover (ptOf (z ≫ M.σ))
  replace hi := (le_iff_ptOf_mem _ _).2 hi
  replace hj := (le_iff_ptOf_mem _ _).2 hj
  replace hk := (le_iff_ptOf_mem _ _).2 hk
  have hL : ∀ la, ⊤ ≤ (z ≫ M.σ) ⁻¹ᵁ (L₀ X Z la).U ((common₀ X Z).idx la k) := fun la s hs =>
    ((common₀ X Z).mem _ _ _).2 (hk hs)
  have hL₀ : ∀ la, ⊤ ≤ ((z ≫ τ) ≫ M₀.σ) ⁻¹ᵁ (L₀ X Z la).U ((common₀ X Z).idx la k) := fun la => e ▸ hL la
  have hM : ∀ la, ⊤ ≤ z ⁻¹ᵁ ((L₀ X Z la).pull M.σ).U (flagIdx M la k) := fun la s hs => mem_pIdx.2 (hL la hs)
  have hM₀ : ∀ la, ⊤ ≤ (z ≫ τ) ⁻¹ᵁ ((L₀ X Z la).pull M₀.σ).U (flagIdx M₀ la k) := fun la s hs =>
    mem_pIdx.2 (hL₀ la hs)
  have hU : ⊤ ≤ (z ≫ M.σ) ⁻¹ᵁ U₀ X Z := fun s h => M.off_eq.le (hz h)
  have hU₀ : ⊤ ≤ ((z ≫ τ) ≫ M₀.σ) ⁻¹ᵁ U₀ X Z := e ▸ hU
  have ha : ⊤ ≤ z ⁻¹ᵁ (LB.div M.K.bundle (M₀.K.bundle.pull τ)).U (j, pIdx M₀.K.bundle τ i) :=
    fun s h => ⟨hj h, mem_pIdx.2 (hi h)⟩
  have hκ : ⊤ ≤ z ⁻¹ᵁ (LB.div M.K.bundle ((L₀ X Z (GlobalTheory.FlagTan.kap Dw)).pull M.σ)).U (j, flagIdx M _ k) :=
    fun s h => ⟨hj h, hM _ h⟩
  have hκ₀ : ⊤ ≤ (z ≫ τ) ⁻¹ᵁ (LB.div M₀.K.bundle ((L₀ X Z (GlobalTheory.FlagTan.kap Dw)).pull M₀.σ)).U (i, flagIdx M₀ _ k) :=
    fun s h => ⟨hi h, hM₀ _ h⟩
  have hc : ⊤ ≤ z ⁻¹ᵁ (tens M.K.bundle ((L₀ X Z b).pull M.σ)).U (j, flagIdx M b k) := fun s h => ⟨hj h, hM _ h⟩
  have hb : ⊤ ≤ (z ≫ τ) ⁻¹ᵁ (tens M₀.K.bundle ((L₀ X Z b).pull M₀.σ)).U (i, flagIdx M₀ b k) :=
    fun s h => ⟨hi h, hM₀ _ h⟩
  refine ⟨(j, i, (common₀ X Z).idx b k), ha, fun s h => mem_pIdx.2 (hb h), hc, hb, ?_⟩
  have v₁ := (((common₀ X Z).pull M.σ).canChart M.K.isLB hs).val_mul ω.ω (M.pullOff m) (j, k) z hz hκ (hM s) hc
  have v₀ := (((common₀ X Z).pull M₀.σ).canChart M₀.K.isLB hs).val_mul ω₀.ω (M₀.pullOff m) (i, k) (z ≫ τ) hz₀ hκ₀
    (hM₀ s) hb
  have w₁ := val_pull M.σ M.off_eq.le z (flagIdx M s k) hz (hM s) hU (hL s) m
  have w₀ := (val_pull M₀.σ M₀.off_eq.le (z ≫ τ) (flagIdx M₀ s k) hz₀ (hM₀ s) hU₀ (hL₀ s) m).trans
    (val_congr e _ hU₀ (hL₀ s) hU (hL s) m)
  have x := val_canId_eq hKS M₀ M τ hτ ω₀ ω z i j k hz hz₀ hκ hκ₀ _
    fun V hV W hW h g h₁ h₂ => hJ' R z i j V hV W hW h g h₁ h₂ ha
  refine v₁.trans (Eq.trans ?_ (congrArg (_ * ·) v₀).symm)
  refine (congrArg₂ (· * ·) x (w₁.trans w₀.symm)).trans ?_
  exact (congrArg (· * _) (mul_comm _ _)).trans (mul_assoc _ _ _)

end Flag

theorem extends_iff_modif : GlobalTheory.CovTop.Hypotheses₂ → GlobalTheory.Published.GrothendieckDeformation → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), FnAlgClosed Xo c → (∀ (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K), GlobalTheory.FlagTan.KSIso (GlobalTheory.FlagTan.psiSet H) y) → ∀ (hV : IsVariety₀ TF.X Z) (ω₀ : CanId (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z))) (M : Modif (str₀ TF.X Z) (U₀ TF.X Z) (dimFlag Dw)) (ω : CanId M) (b s : AllWt.Weight Dw) (hs : FlagTan.kap Dw + b = s) (m : H0 (str₀ TF.X Z) (L₀ TF.X Z s) (U₀ TF.X Z)), (∃ g : H0 (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).str (tens (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).K.bundle ((L₀ TF.X Z b).pull (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).σ)) ⊤, H0.restr le_top g = (((common₀ TF.X Z).pull (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).σ).canChart (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).K.isLB hs).mul ω₀.ω ((Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).pullOff m)) ↔ ∃ g : H0 M.str (tens M.K.bundle ((L₀ TF.X Z b).pull M.σ)) ⊤, H0.restr le_top g = (((common₀ TF.X Z).pull M.σ).canChart M.K.isLB hs).mul ω.ω (M.pullOff m) := by
  intro _ _ E _ _ _ H Dw l Xo c TF Z _ hKS hV ω₀ M ω b s hs m
  haveI := hV.1
  haveI := hV.2.2
  haveI : Smooth (str₀ TF.X Z) := SmoothOfRelativeDimension.smooth (dimFlag Dw) _
  have hI : IsIntegral (Y₀ TF.X Z) := GlobalTheory.isIntegral_of_smooth_of_geometricallyConnected (str₀ TF.X Z)
  haveI : IsIntegral (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).X := hI
  refine extends_iff_of_hom hKS (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)) M M.σ (Category.comp_id _) ?_ ω₀ ω hs m
  rw [Modif.off_eq]
  exact M.iso

end GlobalTheory.CanonBirat
