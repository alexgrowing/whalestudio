import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.ExistsPrincipalLattice
import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
import Formalism.LocalToGlobal.ProjectiveLattices.L2DefiniteCuspForms
import Formalism.LocalToGlobal.ProjectiveLattices.NonnegIffOfLiesTotal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NonemptyUnitAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.NonvanishingNearMaximum
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.IsotropicCoefficientSplitting
import Formalism.LocalToGlobal.CMDeterminantIdeals.LambdaLowerBound
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LawsFieldsSeparately
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaUniformisationComplexAbelianVariety
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FibreSectionNowhereZeroOfGenerates
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.LieBasisCoordinatesBijectiveTangent
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsFibreOfIffIsPolFibre
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.GramStdBasisPosDefAndHq
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.FormEqPiMulHermForm
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsIsPolFibreOfKeyPB
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LamLenOfIsHerm
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LinearIndependentOfIsLieBasis
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.UniversalTripleFibreKeyDataNonemptyField
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.UniversalTripleFibreKeyDataBaseChangeKeyPullback
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.KeyPBIdOfKeyPB
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsAppellHumbertUniformisationOfKeyDatumIso
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.RigidifiedSectionCorrespondenceExistsUniqueNonva

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

namespace GlobalTheory.LamT.CMMetric

theorem dualMap_eq_dualMapR {S T : Type} [CommRing S] [CommRing T] (φ : S →+* T) :
    Formalism.L2.Pj.dualMap φ = Chart.dualMapR φ := rfl

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l}

theorem exists_fibre {K : Type} [Field K] (σ : K →+* ℂ) {x x₀ : Sp K ⟶ Xo.X} (hx : x₀ = x) (Φ : FibKey Xo K x)
    (s : LB.Sec (PPx x₀)) (hs : SecTie Φ.m Φ.th s) (x' : Sp ℂ ⟶ Xo.X) (s' : LB.Sec (PPx x')) (hg : SecGen x' s')
    (hx' : x' = spMap σ ≫ x₀) (hb : SecBC σ 1 x₀ x' s s') (hpq : 1 ≤ Dw.p + Dw.q) :
    ∃ Φ' : FibKey Xo ℂ x', SecTie Φ'.m Φ'.th s' ∧ KeyPB Φ'.key Φ.key σ ∧
      ∀ (e : Φ'.T.g = Φ.T.g) (cf : Fin Φ.T.g → K) (w : epsR K ⟶ Φ.T.t.G), IsLieComb cf Φ.v w →
        ∃ w' : epsR ℂ ⟶ Φ'.T.t.G, IsLieComb (fun i => σ (cf i)) (fun i => Φ'.v (i.cast e.symm)) w' ∧
          w'.left ≫ Φ'.m.φ = spMap (Formalism.L2.Pj.dualMap σ) ≫ w.left ≫ Φ.m.φ := by
  subst hx
  obtain ⟨Φ₀⟩ := nonempty_fibKey E H Dw l Xo ℂ x' hpq
  obtain ⟨-, t2, t3⟩ := GlobalTheory.SecTieEx.secTie_exists_unique E H Dw l Xo ℂ x' Φ₀.T.t Φ₀.m
  obtain ⟨th, hth⟩ := t2 s'
  have hne := (t3 th s' hth).2.1 (secNZ_of_secGen GlobalTheory.lawsFieldsSeparately.2.1 E H Dw l Xo ℂ x' s' hg)
  obtain ⟨e, v', hv', hK, hv⟩ := GlobalTheory.LamT.fibKey_keyPB E H Dw l Xo K ℂ σ x₀ x' Φ { Φ₀ with th := th, th_ne := hne } s s' hx' hs hth hb
  refine ⟨{ Φ₀ with th := th, th_ne := hne, v := v', basis := hv' }, hth, hK, fun _ cf w hw => ?_⟩
  have hp := Φ.m.cart.1
  have hc : IsGrpPullback Φ₀.T.t.G Xo.univ.t.G (spMap σ ≫ x₀) Φ₀.m.φ := hx' ▸ Φ₀.m.cart
  have w₁ : Φ₀.m.φ ≫ Xo.univ.t.G.hom = (Φ₀.T.t.G.hom ≫ spMap σ) ≫ x₀ := by rw [hc.1.w, Category.assoc]
  have hF : hp.lift _ _ w₁ ≫ Φ.m.φ = Φ₀.m.φ := hp.lift_fst _ _ _
  have hψ : IsGrpPullback Φ₀.T.t.G Φ.T.t.G (spMap σ) (hp.lift _ _ w₁) :=
    Φ.m.cart.cancel (by rw [hF]; exact hc) (hp.lift_snd _ _ _)
  generalize hp.lift _ _ w₁ = ψ at hF hψ
  have hov : ∀ j : Fin Φ.T.g, IsVecOver σ ψ (Φ.v j) (v' (j.cast e.symm)) := fun j => by
    obtain ⟨a, ha, -⟩ := existsUnique_isVecOver hψ.1 (Φ.v j)
    have : v' (j.cast e.symm) = a := by
      refine Over.OverMorphism.ext (hc.1.hom_ext ?_ ((Over.w _).trans (Over.w a).symm))
      refine (hv _).trans ?_
      rw [← hF, ← Category.assoc a.left, ha, Category.assoc]
      rfl
    rw [this]; exact ha
  obtain ⟨w', hw', -⟩ := existsUnique_isVecOver hψ.1 w
  refine ⟨w', (lieComb_baseChange K ℂ σ _ _ ψ hψ _ Φ.v w cf _ w' hov hw).1 hw', ?_⟩
  show w'.left ≫ Φ₀.m.φ = _
  rw [← hF, ← Category.assoc, hw', Category.assoc]
  rfl

theorem exists_unif_of_eq (x : KeyIn ℂ) {g : ℕ} (hg : g = x.P.g) (u : HolUnif x.P.A x.P.L g)
    (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ) (θ : (Fin g → ℂ) → ℂ) (Fd : Set (Fin g → ℂ)) (N : ℝ)
    (h : u.IsAH Hm χ ∧ u.IsRig x.rig ∧ u.IsFn x.th θ ∧ IsAddFundamentalDomain u.Λ Fd volume ∧
      N = (∫ z in Fd, ‖θ z‖ ^ 2 * Real.exp (-Real.pi * (hermForm Hm z z).re)) / (volume Fd).toReal) :
    ∃ (u : HolUnif x.P.A x.P.L x.P.g) (Hm : Matrix (Fin x.P.g) (Fin x.P.g) ℂ) (χ : u.Λ → ℂ) (θ : (Fin x.P.g → ℂ) → ℂ)
      (Fd : Set (Fin x.P.g → ℂ)), u.IsAH Hm χ ∧ u.IsRig x.rig ∧ u.IsFn x.th θ ∧ IsAddFundamentalDomain u.Λ Fd volume ∧
      N = (∫ z in Fd, ‖θ z‖ ^ 2 * Real.exp (-Real.pi * (hermForm Hm z z).re)) / (volume Fd).toReal := by
  subst hg
  exact ⟨u, Hm, χ, θ, Fd, h⟩

theorem exists_unif {K : Type} [Field K] [NumberField K] {x : KeyIn K} {T abelian₂ : MLine K} {σ : K →+* ℂ}
    (h : KeyArchAt x T abelian₂ σ) (x' : KeyIn ℂ) (hx : KeyPB x' x σ) :
    ∃ (u : HolUnif x'.P.A x'.P.L x'.P.g) (Hm : Matrix (Fin x'.P.g) (Fin x'.P.g) ℂ) (χ : u.Λ → ℂ)
      (θ : (Fin x'.P.g → ℂ) → ℂ) (Fd : Set (Fin x'.P.g → ℂ)), u.IsAH Hm χ ∧ u.IsRig x'.rig ∧ u.IsFn x'.th θ ∧
      IsAddFundamentalDomain u.Λ Fd volume ∧
      T.n σ ^ 2 = (∫ z in Fd, ‖θ z‖ ^ 2 * Real.exp (-Real.pi * (hermForm Hm z z).re)) / (volume Fd).toReal := by
  obtain ⟨xσ, u, Hm, W, χ, θ, Fd, hK, hA, hR, hF, -, hD, hN, -⟩ := h
  have hI := GlobalTheory.KeyCancel.keyPB_id_of_keyPB K ℂ σ x x' xσ hx hK
  have hg : x'.P.g = xσ.P.g := by
    obtain ⟨_, _, _, hg, _⟩ := hI
    exact hg
  obtain ⟨u', χ', θ', Fd', a, b, c, d, e, -⟩ := GlobalTheory.KeyTransport.uniformisation_transport xσ x' hI hg _ u Hm χ θ Fd ⟨hA, hR, hF, hD⟩
  exact exists_unif_of_eq x' hg.symm u' _ χ' θ' Fd' _ ⟨a, b, c, d, hN.trans e.symm⟩

theorem form_eq_gram {K : Type} [Field K] [NumberField K] {n : ℕ} (h : ReciprocityTheory.GeometryOfNumbersTheory.HermFam K (Fin n → K)) (s : K →+* ℂ)
    (a b : Fin n → K) :
    star (ReciprocityTheory.MultiplicativeHeights.embVec s a) ⬝ᵥ (h.gram s (fun i => Pi.single i 1)).mulVec (ReciprocityTheory.MultiplicativeHeights.embVec s b) =
      h.form s a b := by
  rw [LieMetric.form_eq_sum_sum, Finset.sum_comm]
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, ReciprocityTheory.MultiplicativeHeights.embVec, Pi.star_apply,
    ReciprocityTheory.GeometryOfNumbersTheory.HermFam.gram, Matrix.of_apply]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem exists_isMetric : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (z : CMPt Xo c) (f : ℕ) (La : ℝ), z.Good f La → ∀ (σ : z.K →+* ℂ) (yσ : FrPt Xo c (CAt (σ.comp (algebraMap c.F z.K)))), FrMap (embAlg σ) z.y yσ → ∃ Hm : Matrix (Fin z.Φ.T.g) (Fin z.Φ.T.g) ℂ, Hm.PosDef ∧ z.LamL.n σ = Real.sqrt Hm.det.re ∧ (∀ j, ReciprocityTheory.MultiplicativeHeights.hq Hm (ReciprocityTheory.MultiplicativeHeights.embVec σ (z.U j)) ≤ (La * (z.ℓ j).n σ) ^ 2) ∧ IsMetric yσ (z.Tl.n σ ^ 2) (gramBlock z.e z.U Hm σ) := by
  intro E _ _ _ H Dw l Xo c _ z f La hz σ yσ hy
  obtain ⟨hG, hL, -, hx, hs, hu⟩ := hz
  have hU := GlobalTheory.thetaUnifAV_all
  have hLaw : Out.Laws := GlobalTheory.firstFiveLaws.1
  have hfib : LamF.IsFibreOf z.B.pol z.Φ.key (LamF.gmap z.K) z.m'.φ := hG.2.2.2.1
  have hp : IsPolFibre (algebraMap (𝓞 z.K) z.K) z.B.pol z.Φ.key.P z.m'.φ :=
    (LamF.isFibreOf_iff_isPolFibre _ _ _ _ _ _).1 hfib
  obtain ⟨h, Hh⟩ := (LieMetric.exists_unique_isHerm hU hLaw z.K z.B.pol
    (GenFib.mk z.Φ.key.P z.m'.φ hp z.Φ.key.v z.Φ.key.basis)).1
  obtain ⟨a₁, a₂⟩ := LamF.gram_stdBasis_posDef_and_hq z.K z.Φ.T.g h σ
  obtain ⟨b₁, b₂⟩ := LamF.lamLen_of_isHerm hU hLaw E H l c _ _ f z.obj La hG z.letters hL hp h Hh σ
  refine ⟨h.gram σ (fun i => Pi.single i 1), a₁, b₁, fun j => (a₂ _).trans_le (b₂ j), ?_⟩
  have hpq : 1 ≤ Dw.p + Dw.q := by
    have e : z.Φ.T.g = f * (Dw.p + Dw.q) := hG.2.2.2.2.2.2.2.2.1
    have := z.Φ.g_pos
    rcases Nat.eq_zero_or_pos (Dw.p + Dw.q) with h0 | h0
    · rw [h0] at e; omega
    · exact h0
  have harch : KeyArchAt z.Φ.key z.Tl z.LamL σ := hG.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 σ
  obtain ⟨y₁, y₂, pm, y₃, y₄, y₅⟩ := hy
  have hb : GlobalTheory.Frames.SecBC σ 1 z.y.x yσ.x z.y.s yσ.s := ⟨pm, y₃, y₄, fun i hi => by
    have e₁ : scal z.y.x 1 i = 1 := by simp only [scal, Out.liftFun, map_one]
    rw [e₁, _root_.one_mul]
    exact y₅ i hi⟩
  obtain ⟨Φ', ht, hK, hc⟩ := exists_fibre σ hx z.Φ z.y.s hs yσ.x yσ.s yσ.gen y₁ hb hpq
  obtain ⟨u, Hm, χ, θ, Fd, hA, hR, hF, hD, hN⟩ := exists_unif harch Φ'.key hK
  obtain ⟨ψ, e, hψ, hv⟩ := KeyFibre.exists_isPolFibre_of_keyPB _ _ σ _ _ hK
  obtain ⟨-, -, -, -, t1, -, -⟩ := AHWeil.tangent_and_weil_of_isAH hU Φ'.key.P _ u Hm χ hA
  have key : ∀ (b : E →+* ℂ) (i : Fin (Dw.mult b)), ∃ (w₀ : epsR z.K ⟶ z.Φ.T.t.G) (w : epsR ℂ ⟶ Φ'.key.P.A)
      (W : Fin Φ'.key.P.g → ℂ), IsLieComb (z.U (z.e ⟨b, i⟩)) z.Φ.v w₀ ∧ IsVecOver σ ψ w₀ w ∧
      w.left ≫ Φ'.m.φ = yσ.u b i ∧ u.IsDiff W w := fun b i => by
    obtain ⟨w₀, l₀, c₀⟩ := hL.2.2.1 (z.e ⟨b, i⟩)
    obtain ⟨w₁, l₁, c₁⟩ := hu b i
    have e₀ : w₀ = w₁ := by
      refine Over.OverMorphism.ext (z.m'.cart.1.hom_ext ?_ ((Over.w _).trans (Over.w w₁).symm))
      unfold LamF.LamLetters.IsLetter at l₀ l₁
      cases hs : z.src (z.e ⟨b, i⟩) with
      | inl q =>
        simp only [hs] at l₀ l₁
        exact l₀.trans l₁.symm
      | inr q =>
        simp only [hs] at l₀ l₁
        exact l₀.trans l₁.symm
    subst e₀
    obtain ⟨w, hw, hw'⟩ := hc e _ w₀ c₀
    have ho : IsVecOver σ ψ w₀ w :=
      (lieComb_baseChange z.K ℂ σ _ _ ψ hψ.2.1 _ z.Φ.v w₀ _ _ w (fun j => hv (j.cast e.symm)) c₀).2 hw
    obtain ⟨W, hW, -⟩ := t1 w (ho.isTangent hψ.2.1 (Reg.isTangent_of_isLieComb z.Φ.basis.1 c₀))
    refine ⟨w₀, w, W, c₀, ho, hw'.trans ?_, hW⟩
    rw [y₂, c₁]
    rfl
  choose w₀ w W k₁ k₂ k₃ k₄ using key
  refine ⟨Φ', u, Hm, χ, θ, Fd, w, W, ht, hA, hR, hF, hD, hN, fun b i => ⟨k₃ b i, k₄ b i⟩, fun b i k => ?_⟩
  refine (form_eq_gram h σ _ _).trans ?_
  exact LieMetric.form_eq_pi_mul_hermForm hU hLaw z.K z.B.pol _ h Hh σ Φ'.key.P ψ u Hm χ hψ hA _ _ _ _ _ _ _ _
    (k₁ b i) (k₁ b k) (k₂ b i) (k₂ b k) (k₄ b i) (k₄ b k)

end GlobalTheory.LamT.CMMetric
