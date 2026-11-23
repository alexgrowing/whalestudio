import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.WellChosen
import Development.AbelianVarietyTheory.Definitions.Divisors.P22
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FgIntOfForallIsIntegral
import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LieLetterIntegralInIntegralEigenbasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LieBridgeE
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpPullbackBasisLiftCompatible
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameChangeCommBaseChange
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IntegralFramesDifferByUnit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFrameTangentVectorsOfIsGrpPullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.BcField
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LamT (CMPt)
open IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM fullB tv)
open scoped nonZeroDivisors
attribute [local instance] Over.cartesianMonoidalCategory
open MonObj

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LamT.TanRel

open MonoidalCategory CartesianMonoidalCategory GlobalTheory.Frames GlobalTheory.LamT GlobalTheory.IntLie GlobalTheory.LamT.LetterInt

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l}

theorem tvOf_congr {S : Type} [CommRing S] {x : Sp S ⟶ Xo.X} {v v' : Sp (DualNumber S) ⟶ Xo.univ.t.G.left}
    (h : v = v') (hv : IsTanAt x v) (hv' : IsTanAt x v') :
    ReciprocityTheory.ChartRestriction.G.PullbackSections.tvOf hv = ReciprocityTheory.ChartRestriction.G.PullbackSections.tvOf hv' := by
  subst h; rfl

theorem bc_tan {S T : Type} [CommRing S] [CommRing T] (ψ : S →+* T) {x : Sp S ⟶ Xo.X} {x' : Sp T ⟶ Xo.X}
    (hx : x' = spMap ψ ≫ x) {A : Over (Sp S)} [GrpObj A] {π : A.left ⟶ Xo.univ.t.G.left}
    (hπ : IsGrpPullback A Xo.univ.t.G x π) (w : epsR S ⟶ A) (ht : IsTangent w) :
    IsTanAt x' (spMap (dualMap ψ) ≫ w.left ≫ π) := by
  subst hx
  exact ReciprocityTheory.ChartRestriction.G.PullbackSections.tan_bc ψ ((GlobalTheory.KSExist.FrameLift.tan_iff hπ w).2 ht)

theorem bc_comb {S T : Type} [CommRing S] [CommRing T] (ψ : S →+* T) {x : Sp S ⟶ Xo.X} {x' : Sp T ⟶ Xo.X}
    (hx : x' = spMap ψ ≫ x) {A : Over (Sp S)} [GrpObj A] {π : A.left ⟶ Xo.univ.t.G.left}
    (hπ : IsGrpPullback A Xo.univ.t.G x π) {n : ℕ} (v : Fin n → (epsR S ⟶ A))
    (hvt : ∀ k, IsTanAt x' (spMap (dualMap ψ) ≫ (v k).left ≫ π)) (cf : Fin n → S) (w : epsR S ⟶ A)
    (h : IsLieComb cf v w) (hw : IsTanAt x' (spMap (dualMap ψ) ≫ w.left ≫ π)) :
    ReciprocityTheory.ChartRestriction.G.PullbackSections.tvOf hw = ∑ k, ψ (cf k) • ReciprocityTheory.ChartRestriction.G.PullbackSections.tvOf (hvt k) :=
  (ReciprocityTheory.ChartRestriction.G.PullbackSections.combAt_iff _ hvt _ hw).1
    (GlobalTheory.Frames.ChgBC.isCombAt_pull ψ hx (fun _ => rfl) rfl (GlobalTheory.LieBasisRing.isCombAt_of_isLieComb hπ v cf w h))

end GlobalTheory.LamT.TanRel

namespace GlobalTheory.LamT.TanRel

open MonoidalCategory CartesianMonoidalCategory GlobalTheory.Frames GlobalTheory.LamT GlobalTheory.IntLie GlobalTheory.LamT.LetterInt

set_option maxHeartbeats 1000000 in

theorem tangent_letter_model_relation : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H)
    (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (z : CMPt Xo c) (f : ℕ) (La : ℝ), z.Good f La →
    ∀ (p : HeightOneSpectrum (𝓞 z.K)) (T : CDVR) (iK : z.K →+* T.Fr) (M : GlobalTheory.LamT.LocMod z T iK),
    (∀ y : z.K, iK y ∈ Set.range (algebraMap T.V T.Fr) ↔ p.valuation z.K y ≤ 1) →
    ∀ A : Matrix (Fin z.Φ.T.g) (Fin z.Φ.T.g) z.K, GlobalTheory.LamF.IsModelAt z.B.pol z.Φ.key z.m'.φ p A →
    letI := (iK.comp (algebraMap c.F z.K)).toAlgebra
    ∀ (φ : z.K →ₐ[c.F] T.Fr) (yT y' : FrPt Xo c T.Fr)
      (g : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) T.Fr) (a : T.Fr),
      φ.toRingHom = iK → FrMap φ z.y yT → GlobalTheory.Frames.FrChg g a yT y' → (∀ b, IsUnit (g b).det) →
      GlobalTheory.LamT.LieInt T (iK.comp (algebraMap c.F z.K)) M.m1 M.m2 y'.u →
      ∃ (nu mu : Fin z.Φ.T.g → TanM yT.x Xo.univ.t.G) (C : (Σ b : E →+* ℂ, Fin (Dw.mult b)) → Fin z.Φ.T.g → T.Fr),
        (∀ σ k, C σ k ∈ Set.range (algebraMap T.V T.Fr)) ∧
        (∀ σ, fullB yT σ = ∑ k, iK (z.U (z.e σ) k) • nu k) ∧
        (∀ k, mu k = ∑ l, iK (A k l) • nu l) ∧
        ∀ b i, ∑ j, g b i j • fullB yT ⟨b, j⟩ = ∑ k, C ⟨b, i⟩ k • mu k := by
  intro E _ _ _ H Dw l Xo c _ z f La hz p T iK M hval A hA
  letI := (iK.comp (algebraMap c.F z.K)).toAlgebra
  intro φ yT y' g a hφ hmap hchg hg hint
  obtain ⟨-, hlet, -, hx, -, hu⟩ := hz
  obtain ⟨vV, hvV, hvw⟩ := GlobalTheory.T.exists_lieBasis_local_model E H Dw l Xo c z p T iK M hval A hA
  choose wK hwK hwV using hvw
  have hxT : yT.x = spMap iK ≫ z.x := by rw [hmap.1, hφ, hx]
  have hK := LieComb.lieComb_algebra z.K z.Φ.T.t.G _ z.Φ.v z.Φ.basis.1
  have tv0 : ∀ w : epsR z.K ⟶ z.Φ.T.t.G, IsTangent w →
      IsTanAt yT.x (spMap (dualMap iK) ≫ w.left ≫ z.Φ.m.φ) := fun w ht =>
    bc_tan iK hxT z.Φ.m.cart w ht
  have hvt : ∀ k, IsTanAt yT.x (spMap (dualMap iK) ≫ (z.Φ.v k).left ≫ z.Φ.m.φ) := fun k =>
    tv0 (z.Φ.v k) (z.Φ.basis.1 k)
  have key : ∀ (cf : Fin z.Φ.T.g → z.K) (w : epsR z.K ⟶ z.Φ.T.t.G), IsLieComb cf z.Φ.v w →
      ∀ hw : IsTanAt yT.x (spMap (dualMap iK) ≫ w.left ≫ z.Φ.m.φ),
      ReciprocityTheory.ChartRestriction.G.PullbackSections.tvOf hw = ∑ k, iK (cf k) • ReciprocityTheory.ChartRestriction.G.PullbackSections.tvOf (hvt k) :=
    fun cf w h hw => bc_comb iK hxT z.Φ.m.cart z.Φ.v hvt cf w h hw
  have hmt : ∀ k, IsTanAt yT.x (spMap (dualMap iK) ≫ (wK k).left ≫ z.Φ.m.φ) := fun k =>
    tv0 (wK k) (hK.2.1 _ _ (hwK k))

  obtain ⟨ub, hubt, -, -, hl⟩ := hint
  choose u' hu1 hu2 using hl
  let ubR : ∀ b i, epsR T.V ⟶ M.G.t.G := fun b i => Over.homMk (ub b i).left (Over.w (ub b i))
  have hubR : ∀ b i, IsTangent (ubR b i) := fun b i => by
    have h := hubt b i
    unfold IsTan at h
    unfold IsTangent
    refine h.trans ?_
    have e : (1 : ptOver T.V T.V ⟶ M.G.t.G) = toUnit _ ≫ η[M.G.t.G] := rfl
    rw [e, Over.comp_left]
    have e2 : (toUnit (ptOver T.V T.V)).left = 𝟙 (Sp T.V) := by
      have := Over.w (toUnit (ptOver T.V T.V))
      exact ((Category.comp_id _).symm.trans this).trans (Spec.map_id _)
    rw [e2]
    exact Category.id_comp _
  choose C' hC' using fun b i => (hvV.2 (ubR b i) (hubR b i)).exists

  have hsq : ∀ k, (spMap (dualMap iK) ≫ (wK k).left) ≫ z.Φ.T.t.G.hom =
      spMap (algebraMap T.Fr (DualNumber T.Fr)) ≫ spMap iK := fun k => by
    rw [Category.assoc, Over.w (wK k)]
    exact (spMap_comp₂ _ _).trans ((congrArg spMap (IntLie.dualMap_alg iK)).trans (spMap_comp₂ _ _).symm)
  let s' : Fin z.Φ.T.g → (Sp (DualNumber T.Fr) ⟶ M.t'.t.G.left) := fun k => M.n'.cart.1.lift _ _ (hsq k)
  have hs1 : ∀ k, s' k ≫ M.n'.φ = spMap (dualMap iK) ≫ (wK k).left := fun k => M.n'.cart.1.lift_fst _ _ _
  have hs2 : ∀ k, s' k ≫ M.t'.t.G.hom = spMap (algebraMap T.Fr (DualNumber T.Fr)) := fun k =>
    M.n'.cart.1.lift_snd _ _ _
  let vV' : Fin z.Φ.T.g → (epsOver T.V T.V ⟶ M.G.t.G) := fun k => Over.homMk (vV k).left (Over.w (vV k))
  have hm2 : ∀ k, s' k ≫ M.m2.φ = spMap (dualMap (algebraMap T.V T.Fr)) ≫ (vV' k).left := fun k => by
    apply M.n.cart.1.hom_ext
    · rw [Category.assoc, Category.assoc]
      refine Eq.trans ?_ (hwV k).symm
      exact (congrArg (s' k ≫ ·) M.h2).trans (by rw [reassoc_of% (hs1 k)])
    · rw [Category.assoc, M.m2.cart.1.w, reassoc_of% (hs2 k), Category.assoc, Over.w (vV' k)]
      exact (spMap_comp₂ _ _).trans ((congrArg spMap (IntLie.dualMap_alg _).symm).trans (spMap_comp₂ _ _).symm)
  have hm1 : ∀ k, s' k ≫ M.m1.φ = spMap (dualMap iK) ≫ (wK k).left ≫ z.Φ.m.φ := fun k => by
    rw [M.h1, reassoc_of% (hs1 k)]
  have hcomb : ∀ b i, IsComb vV' (C' b i) (ub b i) := fun b i => by
    obtain ⟨u, hu, he⟩ := hC' b i
    refine ⟨fun k => Over.homMk (u k).left (Over.w (u k)), fun k => hu k, ?_⟩
    exact he
  have hy't : ∀ b i, IsTanAt yT.x (y'.u b i) := fun b i => by
    rw [← hchg.1]; exact y'.tan b i
  have hgen : ∀ b i, IsCombAt yT.x (fun k => spMap (dualMap iK) ≫ (wK k).left ≫ z.Φ.m.φ)
      (fun k => algebraMap T.V T.Fr (C' b i k)) (y'.u b i) := fun b i => by
    have h := comb_generic M.m1 M.m2 vV' s' hm2 (ub b i) (u' b i) (hu2 b i) (C' b i) (hcomb b i)
    rw [hu1 b i] at h
    simp only [hm1] at h
    rw [hxT]
    exact h
  refine ⟨fun k => ReciprocityTheory.ChartRestriction.G.PullbackSections.tvOf (hvt k), fun k => ReciprocityTheory.ChartRestriction.G.PullbackSections.tvOf (hmt k),
    fun σ k => algebraMap T.V T.Fr (C' σ.1 σ.2 k), fun σ k => ⟨_, rfl⟩, ?_, fun k => key _ _ (hwK k) _, ?_⟩
  · rintro ⟨b, j⟩
    obtain ⟨w, hw, hwu⟩ := hu b j
    obtain ⟨w₀, hw₀, hU⟩ := hlet.2.2.1 (z.e ⟨b, j⟩)
    obtain rfl : w₀ = w := by
      refine Over.OverMorphism.ext (z.m'.cart.1.hom_ext ?_ ((Over.w _).trans (Over.w _).symm))
      unfold LamF.LamLetters.IsLetter at hw hw₀
      generalize z.letters.src (z.e ⟨b, j⟩) = s at hw hw₀
      rcases s with q | q
      · exact hw₀.trans hw.symm
      · exact hw₀.trans hw.symm
    have hyu : yT.u b j = spMap (dualMap iK) ≫ w₀.left ≫ z.Φ.m.φ := by
      rw [hmap.2.1 b j, hφ, hwu]
    show ReciprocityTheory.ChartRestriction.G.PullbackSections.tvOf (yT.tan b j) = _
    rw [tvOf_congr hyu (yT.tan b j) (tv0 w₀ (hK.2.1 _ _ hU))]
    exact key _ _ hU _
  · intro b i
    have h5 := (ReciprocityTheory.ChartRestriction.G.PullbackSections.combAt_iff (yT.u b) (yT.tan b) (g b i) (hy't b i)).1 (hchg.2.1 b i)
    have h4 := (ReciprocityTheory.ChartRestriction.G.PullbackSections.combAt_iff _ hmt _ (hy't b i)).1 (hgen b i)
    exact h5.symm.trans h4

end GlobalTheory.LamT.TanRel
