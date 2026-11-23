import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DualGramInterpGram
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFrPtOfEigFrame
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PtEqOfPtOfFrameEq
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.CabsDiagEqOne
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.NonemptyUnifWitnessDataOfIsUnf
import Formalism.LocalToGlobal.ProjectiveLattices.RecConj
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OrthoStatementPf

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TopologicalSpace Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.GradedNorm
open GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.ProjVar.Var GlobalTheory.ShFam.Pad
open scoped ComplexOrder

namespace GlobalTheory.ShFam

attribute [local instance] Over.cartesianMonoidalCategory

open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.ArcQ GlobalTheory.FrameNormLie

section Free

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}

variable {σ : c.F →+* ℂ} {r : ℕ}

section Riemann

variable {U : Formalism.L2.PjFree.Unf Xo c σ r} (hσ : Formalism.L2.PjFree.GoodEmb c σ) (hU : Formalism.L2.PjFree.IsUnf U) (W : UnfWit U)
  {a : ℝ} (ha : ∀ k (τ : (U.X k).Ψ), (τ.1 (-(U.X k).ξ0)).im = a) {k : U.Comp} {x : (U.X k).dom} (hx : IsOrth (U.X k) x.1)
include hσ hU ha hx

theorem im_hermForm_orth (v w : (W.F.Di (W.ik k)).La) :
    (hermForm (((2 * a : ℝ) : ℂ) • 1) (W.Pm k x v) (W.Pm k x w)).im = (W.F.Di (W.ik k)).EF v w := by
  classical
  obtain ⟨hp0, hty⟩ := hU.2.1 k
  obtain ⟨hbij, hrt, -, -⟩ := GlobalTheory.Relab.relab_good E H l c σ hσ
  obtain ⟨f, hf⟩ := FrameUnif.exists_letter_equiv (U.X k).Ψ (U.X k).cmType Dw.p Dw.q r hU.1
    (Formalism.L2.PjFree.relab c σ) hbij Dw.mult
    (fun τ h => by unfold Datum.mult; rw [if_pos ((hrt τ).1 ((hty _).1 h))])
    (fun τ h => by unfold Datum.mult; rw [if_neg (fun h' => h ((hty _).2 ((hrt τ).2 h')))])
  rw [← hp0] at hf
  have hper (v) : W.Pm k x v = perVec (U.X k) (W.e.trans f) x.1 (W.φ k v : Fin r → E) := funext fun j => by
    rw [W.Pm_eq, perVec, Equiv.trans_apply]
    have h := hf (W.e j)
    generalize f (W.e j) = t at h ⊢
    obtain ⟨⟨τ, hτ⟩, ⟨n, hn⟩⟩ := t
    dsimp only at h ⊢
    rcases h with ⟨a, rfl, rfl⟩ | ⟨a, rfl, rfl, d⟩
    · rw [if_neg (by omega), Formalism.L2.PjFree.perFr, dif_pos a, dif_pos hn]
    · rw [if_pos (by omega), Formalism.L2.PjFree.perFr, dif_neg a,
        dif_pos (show conjEmb (Formalism.L2.PjFree.relab c σ (W.e j).1) ∈ (U.X k).Ψ from hτ), dif_pos hn]
      rfl
  have hd : (((2 * a : ℝ) : ℂ) • 1 : Matrix _ _ ℂ) = diagonal (diagXi (U.X k) (W.e.trans f)) := by
    rw [smul_one_eq_diagonal]
    exact congrArg _ (funext fun j => by rw [diagXi, ha])
  rw [hd, hper, hper, im_diag_ortho _ _ _ hx, ← W.iso]
  simp

theorem hermForm_eq_of_orth {i : Fin W.F.n} {P : (W.F.Di i).La →+ (Fin W.g → ℂ)}
    (hP : IsPeriod (W.F.Di i) (fun j => Formalism.L2.PjFree.relab c σ (W.e j).1) P) {Hm : Matrix (Fin W.g) (Fin W.g) ℂ}
    (hH : ∀ v w, (hermForm Hm (P v) (P w)).im = (W.F.Di i).EF v w) {y : FrPt Xo c (CAt σ)}
    {z : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Fin W.g → ℂ)} (hy : AnLie W.F i P y z) (e : y.x = (U.un k x).x)
    {τ : E →+* ℂ} {T : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ}
    (hT : ∀ b, IsCombAt (U.un k x).x ((U.un k x).u τ) (show Fin (Dw.mult τ) → CAt σ from fun b' => T b' b) (y.u τ b)) :
    (of fun b b' => hermForm Hm (z τ b') (z τ b)) = ((2 * a : ℝ) : ℂ) • (Tᴴ * T) := by
  classical
  have p := W.period k x
  obtain ⟨hPx, hv⟩ := W.lie k x
  obtain ⟨h, gam, hex, hh, hiso, -⟩ := familyUnif_exp_unique E H Dw l Xo _ _ _ W.F i (W.ik k) P _ hP p
    (by rw [← hPx, ← hy.1, e])
  set A := LinearMap.toMatrix' h.toLinearMap with hA
  have hAv : ∀ z, A *ᵥ z = h z := fun z => by rw [hA, LinearMap.toMatrix'_mulVec]; rfl
  have hcol (b) : A *ᵥ z τ b = ∑ j, T j b • (Pi.single (W.e.symm ⟨τ, j⟩) 1 : Fin W.g → ℂ) := by
    have d1 := (DerLin.isCombAt_iff_isDerivAt0 E H Dw l Xo _ _ _ W.F _ _ p _ ((U.un k x).u τ) _ (hv τ) _
      (y.u τ b)).1 (hPx ▸ hT b)
    have d2 := (ExpChain.isDerivAt0_ex_iff E H Dw l Xo _ _ _ W.F _ P hP _ _ h.toLinearMap p hex _ _).1 (hy.2 τ b)
    have tn := isDerivAt0_ex_isTanAt E H Dw l Xo _ _ _ W.F _ _ p
    rw [hAv]
    exact (tn.2.2 _ (tn.1 _ _ d2)).unique d2 d1
  have key := UnitDet.eq_of_im_hermForm_eq _ hP.2.2.2.1
    (Aᵀ * ((((2 * a : ℝ) : ℂ) • 1) * A.map (starRingEnd ℂ))) Hm (by
      rintro _ ⟨v, rfl⟩ _ ⟨w, rfl⟩
      rw [← UnitDet.hermForm_mulVec, hAv, hAv, ← hh, ← hh, im_hermForm_orth hσ hU W ha hx, hiso, hH])
  ext b b'
  rw [of_apply, ← key, ← UnitDet.hermForm_mulVec, hcol, hcol]
  have hi : ∀ j j' : Fin (Dw.mult τ), W.e.symm ⟨τ, j⟩ = W.e.symm ⟨τ, j'⟩ ↔ j = j' := fun j j' => by simp
  simp [hermForm, smul_mulVec, sum_dotProduct, dotProduct_sum, star_sum, Pi.single_apply, hi, mul_apply, mul_comm]

end Riemann

theorem isCombAt_co {y y' : FrPt Xo c (CAt σ)} (e : y'.x = y.x) {g : EigFrame Z σ ((cxPt Z y).1 ≫ genι Z)}
    (hg : ∀ τ i, g.v τ i = (cxFrame Z y').v τ i) (τ : E →+* ℂ) (b : Fin (Dw.mult τ)) :
    IsCombAt y.x (y.u τ) (show Fin (Dw.mult τ) → CAt σ from fun b' => (cxFrame Z y).co g τ b' b) (y'.u τ b) := by
  obtain ⟨x, xo, u, ut, ue, ub, s, sg⟩ := y'
  dsimp only at e
  subst e
  let L := lieEquiv (S := CAt σ) Z y (x := (cxPt Z y).1 ≫ genι Z) (Category.assoc _ _ _).symm
  refine (isComb_iff (t := Xo.univ.t) (S := CAt σ) (fun i => tanOf (y.tan τ i)) _ (tanOf (ut τ b))).2 (L.injective ?_)
  exact (tan_ext (w := g.vec τ b) (hg τ b).symm).trans (((cxFrame Z y).vec_eq g τ b).trans
    ((map_sum L _ _).trans (Finset.sum_congr rfl fun _ _ => map_smul L _ _)).symm)

theorem x_eq_of_cxPt {y y' : FrPt Xo c (CAt σ)} (h : (cxPt Z y).1 = (cxPt Z y').1) : y.x = y'.x := by
  have := Z.jQ_open
  rw [← ptF_fst (S := CAt σ) y, ← ptF_fst (S := CAt σ) y']
  exact congrArg (· ≫ _) ((cancel_mono Z.jQ).1 h)

variable (U : ∀ σ : c.F →+* ℂ, Formalism.L2.PjFree.Unf Xo c σ r)

def IsHodgeFrame (y : CxPts (genStr Z) σ) (g : EigFrame Z σ (y.1 ≫ genι Z)) : Prop :=
  ∃ (ψ : ℂ →+* ℂ) (σ' : c.F →+* ℂ) (k : (U σ').Comp) (x : ((U σ').X k).dom),
    (ψ = RingHom.id ℂ ∨ ψ = starRingEnd ℂ) ∧ σ' = ψ.comp σ ∧ Formalism.L2.PjFree.GoodEmb c σ' ∧ IsOrth ((U σ').X k) x.1 ∧
      (cxPt Z ((U σ').un k x)).1 = spMap ψ ≫ y.1 ∧ g.IsMap ψ (cxFrame Z ((U σ').un k x))

open Classical in

def EigMet.hodge (b : ℝ) (hb : 0 < b) (G₀ : EigMet Z σ) : EigMet Z σ where
  gram y g τ := if h : ∃ f, IsHodgeFrame U y f then (b : ℂ) • ((h.choose.co g τ)ᴴ * h.choose.co g τ) else G₀.gram y g τ
  pos y g τ := by
    split_ifs with h
    · exact (PosDef.conjTranspose_mul_self _ (mulVec_injective_of_isUnit
        ((isUnit_iff_isUnit_det _).2 (h.choose.isUnit_det_co g τ)))).smul (Complex.zero_lt_real.2 hb)
    · exact G₀.pos y g τ
  change y f g τ := by
    split_ifs with h
    · rw [← h.choose.co_mul f g]
      simp only [conjTranspose_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
    · exact G₀.change y f g τ

variable {U} {y : CxPts (genStr Z) σ} {f g : EigFrame Z σ (y.1 ≫ genι Z)}

theorem spMap_dualMap_id (R : Type) [CommRing R] : spMap (dualMap (RingHom.id R)) = 𝟙 _ := by
  rw [← Spec.map_id]
  congr 1
  ext r <;> simp [dualMap]

theorem isHodgeFrame_cxFrame (hσ : Formalism.L2.PjFree.GoodEmb c σ) {k : (U σ).Comp} {x : ((U σ).X k).dom}
    (hx : IsOrth ((U σ).X k) x.1) : IsHodgeFrame U (cxPt Z ((U σ).un k x)) (cxFrame Z ((U σ).un k x)) :=
  ⟨_, σ, k, x, .inl rfl, rfl, hσ, hx, by rw [show spMap (RingHom.id ℂ) = 𝟙 _ from Spec.map_id _, Category.id_comp],
    fun _ _ => by rw [spMap_dualMap_id, Category.id_comp]⟩

theorem liesIn_iff_of_comp {σ' : c.F →+* ℂ} {y' : CxPts (genStr Z) σ'} {ψ : ℂ →+* ℂ} (e : y'.1 = spMap ψ ≫ y.1)
    (C : Closeds (gen Z)) : LiesIn y' C ↔ LiesIn y C := by
  have : y'.1 (IsLocalRing.closedPoint ℂ) = y.1 (IsLocalRing.closedPoint ℂ) := by
    rw [e]
    exact (Scheme.Hom.comp_apply _ _ _).trans (congrArg _ (Subsingleton.elim (α := PrimeSpectrum ℂ) _ _))
  rw [LiesIn, LiesIn, this]

theorem IsHodgeFrame.not_liesIn (h : IsHodgeFrame U y g) : ¬ LiesIn y (genBd Z) := fun hy => by
  obtain ⟨ψ, σ', k, x, -, -, -, -, e, -⟩ := h
  exact not_liesIn_cxPt _ ((liesIn_iff_of_comp e _).2 hy)

theorem IsHodgeFrame.conj (h : IsHodgeFrame U y g) {σ₁ : c.F →+* ℂ} {y₁ : CxPts (genStr Z) σ₁}
    {g₁ : EigFrame Z σ₁ (y₁.1 ≫ genι Z)} (hσ : σ = (starRingEnd ℂ).comp σ₁) (e : y.1 = spMap (starRingEnd ℂ) ≫ y₁.1)
    (hg : g₁.IsMap (starRingEnd ℂ) g) : IsHodgeFrame U y₁ g₁ := by
  obtain ⟨ψ, σ', k, x, h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨ψ.comp (starRingEnd ℂ), σ', k, x, ?_, by rw [h2, hσ]; rfl, h3, h4, ?_, fun τ i => ?_⟩
  · rcases h1 with rfl | rfl
    exacts [.inr rfl, .inl (RingHom.ext Complex.conj_conj)]
  · rw [h5, e, ← Category.assoc, ← Spec.map_comp]; rfl
  · rw [h6, hg, GlobalTheory.GradedPieces.dual_comp]

variable (hU : ∀ σ, Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf (U σ))
include hU

theorem exists_isHodgeFrame (hy : ¬ LiesIn y (genBd Z)) : ∃ g, IsHodgeFrame U y g := by
  have good : ∀ {σ : c.F →+* ℂ} {y : CxPts (genStr Z) σ}, Formalism.L2.PjFree.GoodEmb c σ → ¬ LiesIn y (genBd Z) →
      ∃ g, IsHodgeFrame U y g := fun {σ y} hσ hy => by
    have hr : Set.range y.1 ⊆ Set.range Z.jQ := by
      rintro _ ⟨p, rfl⟩
      obtain rfl : p = IsLocalRing.closedPoint ℂ := Subsingleton.elim _ _
      exact not_not.1 hy
    have := Z.jQ_open
    let xF := IsOpenImmersion.lift Z.jQ y.1 hr
    have hxF : xF ≫ Z.jQ = y.1 := IsOpenImmersion.lift_fac _ _ _
    have hs : xF ≫ pullback.snd _ _ = spMap (algebraMap c.F (CAt σ)) := by
      have h2 := y.2
      rw [← hxF, Category.assoc, Z.jQ_over] at h2
      exact h2
    have ho : (xF ≫ pullback.fst _ _) ≫ Xo.s = sOf c (CAt σ) := by
      rw [Category.assoc, pullback.condition, ← Category.assoc, hs]
      exact OpenReg.spMap_comp _ _
    have : IsLocalRing (CAt σ) := inferInstanceAs (IsLocalRing ℂ)
    obtain ⟨z, hz⟩ : ∃ z : FrPt Xo c (CAt σ), z.x = xF ≫ pullback.fst _ _ := GlobalTheory.FlagTan.exists_frPt _ ho
    obtain ⟨k, f, t, hb⟩ := (hU σ hσ).2.2.1 z
    obtain ⟨x, hx, b, hb', e⟩ := ortho_holds r _ f.1 f.2
    obtain ⟨t', ht⟩ := ((hU σ hσ).2.2.2.1 k k ⟨x, KU.orth_dom _ hx⟩ f).2 ⟨1, one_mem _, b, hb', by rw [KU.lact_one, ← e]⟩
    obtain rfl : cxPt Z ((U σ).un k ⟨x, KU.orth_dom _ hx⟩) = y := by
      rw [cxPt_congr (ht.1.symm.trans hb.1.symm)]
      exact Subtype.ext (Eq.trans (congrArg (· ≫ Z.jQ)
        (pullback.hom_ext ((ptF_fst z).trans hz) ((ptF_snd z).trans hs.symm))) hxF)
    exact ⟨_, isHodgeFrame_cxFrame hσ hx⟩
  by_cases hσ : GoodEmb c σ
  · exact good hσ hy
  have h1 : GoodEmb c ((starRingEnd ℂ).comp σ) := by simpa only [goodOf, if_neg hσ] using goodEmb_goodOf c σ
  have hc : spMap (starRingEnd ℂ) ≫ spMap (starRingEnd ℂ) = 𝟙 _ := by
    rw [← Spec.map_comp, ← Spec.map_id]
    exact congrArg Spec.map (CommRingCat.hom_ext (RingHom.ext Complex.conj_conj))
  let y' : CxPts (genStr Z) ((starRingEnd ℂ).comp σ) :=
    ⟨spMap (starRingEnd ℂ) ≫ y.1, by rw [Category.assoc, y.2, ← Spec.map_comp]; rfl⟩
  obtain ⟨g', hg'⟩ := good (y := y') h1 fun h => hy ((liesIn_iff_of_comp rfl _).1 h)
  obtain ⟨g, hg⟩ := g'.exists_isMap (starRingEnd ℂ) (φ' := σ) (x' := y.1 ≫ genι Z)
    (RingHom.ext fun _ => (Complex.conj_conj _).symm) (by simp only [y', ← Category.assoc, hc, Category.id_comp])
  refine ⟨g, hg'.conj rfl rfl fun τ i => ?_⟩
  rw [hg, GlobalTheory.GradedPieces.dual_comp, show (starRingEnd ℂ).comp (starRingEnd ℂ) = RingHom.id ℂ from
    RingHom.ext Complex.conj_conj, spMap_dualMap_id, Category.id_comp]

variable {a : ℝ} (ha0 : 0 < a) (ha : ∀ σ k (τ : ((U σ).X k).Ψ), (τ.1 (-((U σ).X k).ξ0)).im = a)
include ha0 ha

theorem IsHodgeFrame.unitary (hf : IsHodgeFrame U y f) (hg : IsHodgeFrame U y g) (τ : E →+* ℂ) :
    (f.co g τ)ᴴ * f.co g τ = 1 := by
  classical
  obtain ⟨ψ, σ', k, x, h1, h2, h3, h4, h5, h6⟩ := hf
  obtain ⟨ψ₁, σ₁, k₁, x₁, g1, g2, g3, g4, g5, g6⟩ := hg
  obtain rfl : ψ = ψ₁ := by
    rw [h2] at h3
    rw [g2] at g3
    rcases h1 with rfl | rfl <;> rcases g1 with rfl | rfl
    exacts [rfl, (not_good_conj c (σ := σ) h3 g3).elim, (not_good_conj c (σ := σ) g3 h3).elim, rfl]
  obtain rfl : σ' = σ₁ := h2.trans g2.symm
  have hx : (cxPt Z ((U σ').un k x)).1 ≫ genι Z = spMap ψ ≫ y.1 ≫ genι Z := by rw [h5, Category.assoc]
  obtain ⟨g', hg'⟩ := g.exists_isMap ψ h2 hx
  obtain ⟨W⟩ := nonempty_unfWit_of_isUnf E H Dw l Xo c σ' r _ (hU _ h3)
  have e := x_eq_of_cxPt (g5.trans h5.symm)
  have key := hermForm_eq_of_orth h3 (hU _ h3) W (ha σ') h4 (W.period k₁ x₁)
    (im_hermForm_orth h3 (hU _ h3) W (ha σ') g4) (W.lie k₁ x₁) e
    (isCombAt_co e (fun τ i => (hg' τ i).trans (g6 τ i).symm) τ)
  have h7 : (((2 * a : ℝ) : ℂ)) ≠ 0 := Complex.ofReal_ne_zero.2 (by positivity)
  rw [h6.co τ hg' hx] at key
  have k2 : ((f.co g τ).map ψ)ᴴ * (f.co g τ).map ψ = 1 := smul_right_injective _ h7 (key.symm.trans (by
    ext b b'
    simp [hermForm, smul_mulVec, Pi.single_apply, one_apply, eq_comm]))
  rcases h1 with rfl | rfl
  · exact k2
  · have := congrArg (fun M => M.map (starRingEnd ℂ)) k2
    simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)] at this
    convert this using 2 <;> ext <;> simp

variable {b : ℝ} {hb : 0 < b} {G₀ : EigMet Z σ}

theorem IsHodgeFrame.gram_eq (hf : IsHodgeFrame U y f) (g : EigFrame Z σ (y.1 ≫ genι Z)) (τ : E →+* ℂ) :
    (EigMet.hodge U b hb G₀).gram y g τ = (b : ℂ) • ((f.co g τ)ᴴ * f.co g τ) := by
  have h : ∃ f, IsHodgeFrame U y f := ⟨f, hf⟩
  refine (dif_pos h).trans (congrArg _ ?_)
  rw [← h.choose.co_mul f g, conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc _ _ (f.co g τ),
    h.choose_spec.unitary hU ha0 ha hf, Matrix.one_mul]

theorem hodge_gram_eq_riemann (hσ : Formalism.L2.PjFree.GoodEmb c σ) (W : UnfWit (U σ)) {i : Fin W.F.n}
    {P : (W.F.Di i).La →+ (Fin W.g → ℂ)} (hP : IsPeriod (W.F.Di i) (fun j => Formalism.L2.PjFree.relab c σ (W.e j).1) P)
    {Hm : Matrix (Fin W.g) (Fin W.g) ℂ} (hH : IsRiem W.F i P Hm) {q : FrPt Xo c (CAt σ)}
    {z : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Fin W.g → ℂ)} (hq : AnLie W.F i P q z) (τ : E →+* ℂ)
    (hb : 0 < 2 * Real.pi * a) : (EigMet.hodge U _ hb G₀).gram (cxPt Z q) (cxFrame Z q) τ =
      (Real.pi : ℂ) • of fun b b' => hermForm Hm (z τ b') (z τ b) := by
  have key : ∀ (y : CxPts (genStr Z) σ) (g : EigFrame Z σ (y.1 ≫ genι Z)), y = cxPt Z q →
      (∀ τ i, g.v τ i = (cxFrame Z q).v τ i) → (EigMet.hodge U _ hb G₀).gram y g τ =
        (Real.pi : ℂ) • of fun b b' => hermForm Hm (z τ b') (z τ b) := fun y g e hg => by
    obtain ⟨f, ψ, σ', k, x, rfl | rfl, h2, h3, h4, h5, -⟩ := exists_isHodgeFrame hU (y := y) (e ▸ not_liesIn_cxPt q)
    · obtain rfl : σ' = σ := h2
      obtain rfl : cxPt Z ((U σ').un k x) = y :=
        Subtype.ext (h5.trans ((congrArg (· ≫ y.1) (Spec.map_id _)).trans (Category.id_comp _)))
      have e' := (x_eq_of_cxPt (congrArg Subtype.val e)).symm
      rw [(isHodgeFrame_cxFrame hσ h4).gram_eq hU ha0 ha,
        hermForm_eq_of_orth hσ (hU _ hσ) W (ha σ') h4 hP hH.2.2 hq e' (isCombAt_co e' hg τ), smul_smul]
      congr 1
      push_cast
      ring
    · exact (not_good_conj c (σ := σ) hσ (h2 ▸ h3)).elim
  exact key _ _ rfl fun _ _ => rfl

end Free

end GlobalTheory.ShFam
