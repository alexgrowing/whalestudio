import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StepIdeal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HodgeMetricFrameEqRiemannFormAtInteriorPoint
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IoOfLeOneIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiFibrationLieLatticeFullStatement
import Development.AutomorphicArithmetic.DivisorFrames.HodgeGramEqPiMulHermFormOfExponential

section SlopeTestRemainingChoices
open AlgebraicGeometry CategoryTheory Limits MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts GlobalTheory
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.ShFam.Hor.LogCh
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.ArcQ GlobalTheory.FrameNormLie GlobalTheory.HodgeSmooth ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.BasicNotions
attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}
  {σ : c.F →+* ℂ} {r : ℕ}

private theorem herm_orth_ne {U : Formalism.L2.PjFree.Unf Xo c σ r} (hσ : Formalism.L2.PjFree.GoodEmb c σ)
    (hU : Formalism.L2.PjFree.IsUnf U) (W : UnfWit U)
    {a : ℝ} (ha : ∀ k (τ : (U.X k).Ψ), (τ.1 (-(U.X k).ξ0)).im = a) {k : U.Comp} {x : (U.X k).dom}
    (hx : IsOrth (U.X k) x.1) {Hm : Matrix (Fin W.g) (Fin W.g) ℂ}
    (hH : ∀ v w, (hermForm Hm (W.Pm k x v) (W.Pm k x w)).im = (W.F.Di (W.ik k)).EF v w)
    (z : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Fin W.g → ℂ))
    (uu : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber ℂ) ⟶ Xo.univ.t.G.left))
    {T : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ}
    (hder : ∀ τ b, IsDerivAt0 (fun w => (W.F.ex (W.ik k) (W.Pm k x) w).left) (z τ b) (uu τ b))
    (hT : ∀ τ b, IsCombAt (U.un k x).x ((U.un k x).u τ) (show Fin (Dw.mult τ) → CAt σ from fun b' => T τ b' b)
      (uu τ b)) {τ τ' : E →+* ℂ} (b : Fin (Dw.mult τ)) (b' : Fin (Dw.mult τ')) (hne : τ ≠ τ') :
    hermForm Hm (z τ b) (z τ' b') = 0 := by
  classical
  have p := W.period k x
  obtain ⟨hPx, hv⟩ := W.lie k x
  have hcol (τ b) : z τ b = ∑ j, T τ j b • (Pi.single (W.e.symm ⟨τ, j⟩) 1 : Fin W.g → ℂ) := by
    have d1 := (DerLin.isCombAt_iff_isDerivAt0 E H Dw l Xo _ _ _ W.F _ _ p _ ((U.un k x).u τ) _ (hv τ) _
      (uu τ b)).1 (hPx ▸ hT τ b)
    have d2 := hder τ b
    have tn := isDerivAt0_ex_isTanAt E H Dw l Xo _ _ _ W.F _ _ p
    exact (tn.2.2 _ (tn.1 _ _ d2)).unique d2 d1
  have key := UnitDet.eq_of_im_hermForm_eq _ p.2.2.2.1
    ((((2 * a : ℝ) : ℂ) • 1)) Hm (by
      rintro _ ⟨v, rfl⟩ _ ⟨w, rfl⟩
      rw [im_hermForm_orth hσ hU W ha hx, hH])
  rw [← key, hcol, hcol]
  have hi : ∀ (j : Fin (Dw.mult τ)) (j' : Fin (Dw.mult τ')), W.e.symm ⟨τ, j⟩ ≠ W.e.symm ⟨τ', j'⟩ :=
    fun j j' h => hne (congrArg Sigma.fst (W.e.symm.injective h))
  have hi' : ∀ (j : Fin (Dw.mult τ)) (j' : Fin (Dw.mult τ')), W.e.symm ⟨τ', j'⟩ ≠ W.e.symm ⟨τ, j⟩ :=
    fun j j' => (hi j j').symm
  simp [hermForm, smul_mulVec, sum_dotProduct, dotProduct_sum, star_sum, Pi.single_apply, hi, hi', hne, hne.symm]

private theorem herm_exp_ne {U : Formalism.L2.PjFree.Unf Xo c σ r} (hσ : Formalism.L2.PjFree.GoodEmb c σ)
    (hU : Formalism.L2.PjFree.IsUnf U)
    {a : ℝ} (ha : ∀ k (τ : (U.X k).Ψ), (τ.1 (-(U.X k).ξ0)).im = a) {k : U.Comp} {x' : (U.X k).dom}
    (hx : IsOrth (U.X k) x'.1) {g : ℕ}
    (exx : (Fin g → ℂ) → (Over.mk ((cxPt Z (U.un k x')).1 ≫ genι Z) ⟶ Z.t.G))
    (hex : IsExpAt Z.t ((cxPt Z (U.un k x')).1 ≫ genι Z) exx) (hhol : IsHolTo Set.univ (fun w => (exx w).left))
    (Hm : Matrix (Fin g) (Fin g) ℂ)
    (hint : ∀ v w : Fin g → ℂ, exx v = 1 → exx w = 1 → ∃ m : ℤ, (hermForm Hm v w).im = m)
    (hweil : ∀ (k : ℕ) (v w : Fin g → ℂ) (ζ : ℂˣ), 0 < k → exx v = 1 → exx w = 1 → (ζ : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * ((hermForm Hm v w).im : ℂ) / k) → GlobalTheory.UU.CubWeil Z.t.cub k (exx ((k : ℂ)⁻¹ • v)) (exx ((k : ℂ)⁻¹ • w)) (unitOn ζ))
    (f : EigFrame Z σ ((cxPt Z (U.un k x')).1 ≫ genι Z)) (Wd : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Fin g → ℂ)
    (hdirs : ∀ τ b, IsDerivAt0 (fun w => (exx w).left) (Wd τ b) (f.v τ b))
    {τ τ' : E →+* ℂ} (b : Fin (Dw.mult τ)) (b' : Fin (Dw.mult τ')) (hne : τ ≠ τ') :
    hermForm Hm (Wd τ b) (Wd τ' b') = 0 := by
  classical
  obtain ⟨W⟩ := nonempty_unfWit_of_isUnf E H Dw l Xo c σ r _ hU
  have hu : W.F.u (W.ik k) (W.Pm k x') =
      (GlobalTheory.AllWt.ptF (S := CAt σ) (U.un k x') : Sp ℂ ⟶ Xo.XF c) ≫
        pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom) :=
    (W.lie k x').1.symm.trans (ptF_fst _).symm
  have hp : (GlobalTheory.AllWt.ptF (S := CAt σ) (U.un k x') : Sp ℂ ⟶ Xo.XF c) ≫ Z.jQ ≫
      pullback.fst Z.s (spMap β) = (cxPt Z (U.un k x')).1 ≫ genι Z := (Category.assoc _ _ _).symm
  have hper := W.period k x'
  have he' := isExpAt_pushEx E H Dw l Xo c O β Z W.g _ _ W.F _ _ _ _ hu hp hper
  have hhol' := pushEx_hol E H Dw l Xo c O β Z W.g _ _ W.F _ _ _ _ hu hp hper
  have hker := pushEx_eq_one_iff E H Dw l Xo c O β Z W.g _ _ W.F _ _ _ _ hu hp hper
  have hcw := pushEx_cubWeil E H Dw l Xo c O β Z W.g _ _ W.F _ _ _ _ hu hp hper
  obtain ⟨L, hL⟩ := exp_eq_comp_linearEquiv E H Z.X Z.t _ g W.g exx _ hex hhol he' hhol'
  set A : Matrix (Fin g) (Fin W.g) ℂ := LinearMap.toMatrix' L.toLinearMap with hA
  have hAv : ∀ z, A *ᵥ z = L z := fun z => LinearMap.toMatrix'_mulVec _ z
  set Hm' : Matrix (Fin W.g) (Fin W.g) ℂ := Aᵀ * Hm * Aᵀᴴ with hHm'
  have hpull : ∀ z w, hermForm Hm' z w = hermForm Hm (L z) (L w) := fun z w => by
    rw [hHm', GlobalTheory.HodgeInteriorGram.hermForm_pull', hAv, hAv]
  have hIm : ∀ a b, (hermForm Hm' (W.Pm k x' a) (W.Pm k x' b)).im = (W.F.Di (W.ik k)).EF a b := by
    intro a b
    rw [hpull]
    have h1 : exx (L (W.Pm k x' a)) = 1 := by rw [← hL]; exact (hker _).2 ⟨a, rfl⟩
    have h2 : exx (L (W.Pm k x' b)) = 1 := by rw [← hL]; exact (hker _).2 ⟨b, rfl⟩
    obtain ⟨m, hm⟩ := hint _ _ h1 h2
    rw [hm]
    congr 1
    refine GlobalTheory.HodgeInteriorGram.int_eq_of_exp_eq _ _ fun K hK => ?_
    have w1 := hweil K _ _ (Units.mk0 _ (Complex.exp_ne_zero (-(2 * Real.pi * Complex.I) * (m : ℂ) / K))) hK h1 h2
      (by rw [hm, Complex.ofReal_intCast]; rfl)
    have w2 := hcw K a b (Units.mk0 _ (Complex.exp_ne_zero
      (-(2 * Real.pi * Complex.I) * ((W.F.Di (W.ik k)).EF a b : ℂ) / K))) hK rfl
    rw [hL, hL, L.map_smul, L.map_smul] at w2
    exact congrArg Units.val (ReciprocityTheory.ChartRestriction.G.H1.unitOn_injective (w1.unique w2))
  set Lc := L.toContinuousLinearEquiv with hLc
  have hLc' : ∀ z, Lc z = L z := fun z => rfl
  choose w hwt hwm hwc using fun (τ : E →+* ℂ) (b : Fin (Dw.mult τ)) =>
    GlobalTheory.HodgeSmooth.exists_lift_comb (Z := Z) (U.un k x') rfl (cxFrame Z (U.un k x')) f (fun _ _ => rfl) τ b
  have hder : ∀ τ (b : Fin (Dw.mult τ)), IsDerivAt0 (fun z => (W.F.ex (W.ik k) (W.Pm k x') z).left)
      (Lc.symm (Wd τ b)) (w τ b ≫ Z.m0.toSABMap.φ) := by
    intro τ b
    refine isDerivAt0_ex_of_push Z W.F _ _ _ hper hu (hwt τ b).1 ?_
    rw [hwm τ b]
    have e1 : (fun z => liftEx Z W.F _ (W.ik k) (W.Pm k x') hu z ≫ Z.m.φ) =
        fun z => (exx (Lc z)).left := funext fun z => by
      rw [hLc', ← hL]
      rfl
    rw [e1]
    refine (GlobalTheory.HodgeInteriorGram.isDerivAt0_comp_equiv Lc (fun v => (exx v).left) _ _).2 ?_
    rw [Lc.apply_symm_apply]
    exact hdirs τ b
  have h2 := herm_orth_ne hσ hU W ha hx hIm (fun τ b => Lc.symm (Wd τ b)) (fun τ b => w τ b ≫ Z.m0.toSABMap.φ)
    (T := fun τ => (cxFrame Z (U.un k x')).co f τ) hder hwc b b' hne
  rw [hpull, ← hLc', ← hLc', Lc.apply_symm_apply, Lc.apply_symm_apply] at h2
  exact h2

end SlopeTestRemainingChoices

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain
open ReciprocityTheory.GeometryOfNumbersTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.Cartier
open GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LieHt GlobalTheory.LieRead GlobalTheory.GradedNorm GlobalTheory.Mean4O
open scoped ComplexOrder
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory

theorem UpperTheory.exponential_hermitian_holomorphic :
    ∀ (D : D7) (O : Setup D) (σ : O.κ.c.F →+* ℂ), Formalism.L2.PjFree.GoodEmb O.κ.c σ → ∀ (yc : GlobalTheory.CxPts (genStr O.s.T.Z) σ), yc.1 (IsLocalRing.closedPoint ℂ) ∉ genBd O.s.T.Z → ∀ (g : ℕ) (exx : (Fin g → ℂ) → (Over.mk (yc.1 ≫ genι O.s.T.Z) ⟶ O.s.T.Z.t.G)) (Hm : Matrix (Fin g) (Fin g) ℂ), GlobalTheory.ShFam.Hor.LogCh.IsExpAt O.s.T.Z.t (yc.1 ≫ genι O.s.T.Z) exx → IsHolTo Set.univ (fun w => (exx w).left) → ((∀ v w : Fin g → ℂ, exx v = 1 → exx w = 1 → ∃ m : ℤ, (hermForm Hm v w).im = m) ∧ (∀ (k : ℕ) (v w : Fin g → ℂ) (ζ : ℂˣ), 0 < k → exx v = 1 → exx w = 1 → (ζ : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * ((hermForm Hm v w).im : ℂ) / k) → GlobalTheory.UU.CubWeil O.s.T.Z.t.cub k (exx ((k : ℂ)⁻¹ • v)) (exx ((k : ℂ)⁻¹ • w)) (unitOn ζ))) → ∀ (f : EigFrame O.s.T.Z σ (yc.1 ≫ genι O.s.T.Z)) (Wd : ∀ τ : D.host.E →+* ℂ, Fin (O.S.Dw.mult τ) → Fin g → ℂ), (∀ τ b, IsDerivAt0 (fun w => (exx w).left) (Wd τ b) (f.v τ b)) → ∀ τ τ' a b, τ ≠ τ' → hermForm Hm (Wd τ a) (Wd τ' b) = 0 := by
  intro D O σ hσ yc hy g exx Hm hex hhol hH f Wd hd τ τ' a b hne
  obtain ⟨k, x', hx', rfl⟩ := GlobalTheory.HodgeSmooth.exists_orth (Z := O.s.T.Z) hσ (O.s.unf σ hσ).1 (y := yc) hy
  exact herm_exp_ne hσ (O.s.unf σ hσ).1 (O.s.im_neg_xi σ) hx' exx hex hhol Hm hH.1 hH.2 f Wd hd a b hne
