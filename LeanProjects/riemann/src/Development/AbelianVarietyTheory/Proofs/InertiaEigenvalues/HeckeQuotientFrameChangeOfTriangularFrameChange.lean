import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HeckeValueIntegrality
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckePointLawsOfTransport
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LowerTriIsUnitDet
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUniqueFrameChangeByMatrices
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsCombAtGMulVec
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FibreSectionGeneratesOfNowhereZero
import Formalism.LocalToGlobal.ProjectiveLattices.IntAllProofFree

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori GlobalTheory.HeckeFrCompare GlobalTheory.HeckePointLaw

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HeckeBorelChange

section SlopeTestRemainingChoices

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l}

theorem isLieImg_comb {Ω : Type} [Field Ω] {x x' : Sp Ω ⟶ Xo.X} {ψ : Gx x ⟶ Gx x'} (hψ : IsLinHom ψ) {p m : ℕ}
    {v v' : Fin m → (Sp (DualNumber Ω) ⟶ Xo.univ.t.G.left)} (hv : ∀ j, IsLieImg p ψ (v j) (v' j))
    (cf : Fin m → Ω) {w w' : Sp (DualNumber Ω) ⟶ Xo.univ.t.G.left} (htw : IsTanAt x w) (htw' : IsTanAt x' w')
    (hw : IsCombAt x v cf w) (hw' : IsCombAt x' v' cf w') : IsLieImg p ψ w w' := by
  let A : Fin m → (tEps x ⟶ Xo.univ.t.G) := fun j => Over.homMk (v j) (hv j).1.1
  let B : Fin m → (tEps x' ⟶ Xo.univ.t.G) := fun j => Over.homMk (v' j) (hv j).2.1.1
  let W : tEps x ⟶ Xo.univ.t.G := Over.homMk w htw.1
  let W' : tEps x' ⟶ Xo.univ.t.G := Over.homMk w' htw'.1
  have hAB : ∀ j, scaleAt x' (p : Ω) ≫ B j = tanMap hψ (A j) := fun j => by
    obtain ⟨-, -, a, ha, e⟩ := hv j
    have : a = A j := Over.OverMorphism.ext ha
    subst this
    exact Over.OverMorphism.ext e
  have hW : (List.ofFn fun i => scaleAt x (cf i) ≫ A i).prod = W := (isCombAt_iff A cf W).1 hw
  have hW' : (List.ofFn fun i => scaleAt x' (cf i) ≫ B i).prod = W' := (isCombAt_iff B cf W').1 hw'
  let Lc : (tEps x' ⟶ Xo.univ.t.G) →* (tEps x' ⟶ Xo.univ.t.G) :=
    MonoidHom.mk' (fun b => scaleAt x' (p : Ω) ≫ b) fun b b' => MonObj.comp_mul _ _ _
  have key : scaleAt x' (p : Ω) ≫ W' = tanMap hψ W := by
    have e1 : scaleAt x' (p : Ω) ≫ W' = Lc W' := rfl
    rw [e1, ← hW, ← hW', map_list_prod, map_list_prod, List.map_ofFn, List.map_ofFn]
    refine congrArg (fun f => (List.ofFn f).prod) (funext fun i => ?_)
    simp only [Function.comp_apply, Lc, MonoidHom.mk'_apply]
    rw [tanMap_scale, ← hAB, ← Category.assoc, ← Category.assoc, scaleAt_comm]
  exact ⟨htw, htw', W, rfl, congrArg (·.left) key⟩

theorem scal_mul'' {S : Type} [CommRing S] (x : Sp S ⟶ Xo.X) (a b : S) (i : (PPx x).ι) :
    scal x (a * b) i = scal x a i * scal x b i := by
  simp only [scal, ReciprocityTheory.ChartRestriction.G.Out.liftFun, map_mul]

theorem scal_one'' {S : Type} [CommRing S] (x : Sp S ⟶ Xo.X) (i : (PPx x).ι) : scal x (1 : S) i = 1 := by
  simp only [scal, ReciprocityTheory.ChartRestriction.G.Out.liftFun, map_one]

theorem secBC_self {Ω : Type} [CommRing Ω] {x : Sp Ω ⟶ Xo.X} {a : Ω} {s s' : LB.Sec (PPx x)}
    (h : GlobalTheory.Frames.SecBC (RingHom.id Ω) a x x s s') : ∀ i, s'.f i = scal x a i * s.f i := by
  obtain ⟨pm, h₁, h₂, h₃⟩ := h
  have e0 : spMap (RingHom.id Ω) = 𝟙 (Sp Ω) := by simp [spMap]
  obtain rfl : pm = 𝟙 _ := gx_ext (h₂.trans (by rw [e0]; simp))
    (h₁.trans (Category.id_comp _).symm)
  intro i
  have e : Scheme.Hom.appLE (𝟙 (Gx x)) ((PPx x).U i) ((PPx x).U i) le_rfl = 𝟙 _ := by
    simp only [Scheme.Hom.appLE, Scheme.Hom.id_app]
    exact (Category.id_comp _).trans (CategoryTheory.Functor.map_id _ _)
  have := h₃ i le_rfl
  rw [e] at this
  exact this.symm

end SlopeTestRemainingChoices

theorem hkRelFr_frBor : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (P : Ideal (𝓞 E)) (p i : ℕ), GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot39.IsHeckePrime H l P p → ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra c.F Ω] (t : Ix Dw → Ωˣ) (w z : FrPt Xo c Ω), FrBor t w z → ∀ (C : hkKer (Xo := Xo) P p i Ω z) (z' : FrPt Xo c Ω), hkRelFr P p i (GlobalTheory.ThetaTrace.hkTr Xo c p) Ω z C z' → ∃ (C₀ : hkKer (Xo := Xo) P p i Ω w) (w' : FrPt Xo c Ω), hkRelFr P p i (GlobalTheory.ThetaTrace.hkTr Xo c p) Ω w C₀ w' ∧ FrBor t w' z' := by
  intro E _ _ _ H Dw l Xo c P p i hP Ω _ _ _ t w z hb C z' hz
  have hsp : IsSplitOff l P p := hP
  obtain ⟨g, hg0, hgd, hgc⟩ := (GlobalTheory.Frames.frBor_iff_frChg w z t).1 hb
  have hdet : ∀ τ, IsUnit (g τ).det := fun τ =>
    GlobalTheory.Frames.lowerTri_isUnit_det _ (hg0 τ) fun j => by rw [hgd]; exact Units.isUnit _
  have hdet' : ∀ τ, IsUnit ((g τ)⁻¹).det := fun τ => by
    rw [Matrix.det_nonsing_inv]; exact (hdet τ).ringInverse
  obtain ⟨w', hw', -⟩ := GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c Ω z' (fun τ => (g τ)⁻¹) (t none)⁻¹ hdet'
  have hdiag : ∀ τ j, (g τ)⁻¹ j j = ((t⁻¹ (some ⟨τ, j⟩) : Ωˣ) : Ω) := fun τ j => by
    have e := GlobalTheory.Frames.lowerTri_mul_diag ((g τ)⁻¹) (g τ) (GlobalTheory.Frames.lowerTri_inv _ (hg0 τ) (hdet τ)) (hg0 τ) j
    rw [Matrix.nonsing_inv_mul _ (hdet τ), Matrix.one_apply_eq, hgd] at e
    rw [Pi.inv_apply, Units.val_inv_eq_inv_val]
    exact eq_inv_of_mul_eq_one_left e.symm
  have hb' : FrBor t⁻¹ z' w' := (GlobalTheory.Frames.frBor_iff_frChg z' w' t⁻¹).2
    ⟨fun τ => (g τ)⁻¹, fun τ => GlobalTheory.Frames.lowerTri_inv _ (hg0 τ) (hdet τ), hdiag, hw'⟩
  have hbw : FrBor t w' z' := by
    simpa using (GlobalTheory.Frames.frBor_calculus E H Dw l Xo c Ω z' w' w').2.2.2 t⁻¹ hb'
  obtain ⟨ψ, hiso, hlie, hth⟩ := (hkPt_iff hsp _ z C.1 z').1 hz
  obtain ⟨hx, hc, hs⟩ := hgc
  obtain ⟨hx', hc', hs'⟩ := hw'
  obtain ⟨zx, zo, zu, ztan, zeig, zbas, zs, zgen⟩ := z
  dsimp only at hx
  subst hx
  obtain ⟨zx', zo', zu', ztan', zeig', zbas', zs', zgen'⟩ := z'
  dsimp only at hx'
  subst hx'
  refine ⟨C, w', (hkPt_iff hsp _ w C.1 w').2 ⟨ψ, hiso, fun τ j => ?_, ?_⟩, hbw⟩
  · have hcomb : IsCombAt w.x (zu τ) ((g τ)⁻¹ j) (w.u τ j) := by
      obtain ⟨a, ha, -⟩ := zbas τ (w.u τ j) (w.tan τ j) (w.eig τ j)
      have h1 := GlobalTheory.TangentLinear.isCombAt_mulVec E H Dw l Xo Ω w.x (w.u τ) (w.tan τ) (zu τ) (g τ).transpose a
        (w.u τ j) (fun k => hc τ k) ha
      have h2 := Formalism.L2.PjFree.isCombAt_single (w.tan τ) j
      have e : (g τ).transpose.mulVec a = Pi.single j 1 :=
        (w.basis τ (w.u τ j) (w.tan τ j) (w.eig τ j)).unique h1 h2
      have ea : a = (g τ)⁻¹ j := by
        have e2 := congrArg ((g τ).transpose⁻¹.mulVec) e
        rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (by rw [Matrix.det_transpose]; exact hdet τ),
          Matrix.one_mulVec, Matrix.mulVec_single_one] at e2
        rw [e2, ← Matrix.transpose_nonsing_inv]
        ext k
        rfl
      exact ea ▸ ha
    exact isLieImg_comb hiso.2.1 (fun k => hlie τ k) ((g τ)⁻¹ j) (w.tan τ j) (w'.tan τ j) hcomb (hc' τ j)
  · have hth' : GlobalTheory.ThetaTrace.IsThetaTrace Xo.univ.t.G Xo.univ.t.PP ψ p zs zs' := by
      have := hth
      simp only [GlobalTheory.ThetaTrace.hkTr, Equiv.apply_symm_apply] at this
      exact this
    show GlobalTheory.ThetaTrace.IsThetaTrace Xo.univ.t.G Xo.univ.t.PP (conj w.x w'.x ((conj w.x w'.x).symm ψ)) p w.s w'.s
    rw [Equiv.apply_symm_apply]
    have hs₁ := secBC_self hs
    have hs₂ := secBC_self hs'
    refine GlobalTheory.ThetaTrace.IsThetaTrace.smul hth' (toΓ Ω (((t none)⁻¹ : Ωˣ) : Ω)) (fun k => ?_) (fun k => hs₂ k)
    show w.s.f k = scal w.x (((t none)⁻¹ : Ωˣ) : Ω) k * zs.f k
    rw [hs₁ k, ← _root_.mul_assoc, ← scal_mul'', Units.inv_mul, scal_one'', _root_.one_mul]

end GlobalTheory.HeckeBorelChange
