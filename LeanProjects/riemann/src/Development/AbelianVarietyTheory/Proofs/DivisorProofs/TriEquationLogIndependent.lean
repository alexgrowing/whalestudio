import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecializationMapCompUniversalSection
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GrNormPosOfBasis
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ScaleZeroComp
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IoOfLeOneIff
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LinearIndependentOfCutSec

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar
open GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.GalCarry GlobalTheory.TrueGeo

namespace GlobalTheory.ShFam.GalCarry.AnyFrame

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem indep_v {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β} {R : Type} [CommRing R]
    {φ : c.F →+* R} {x : Sp R ⟶ Z.X} (g : EigFrame Z φ x) (τ : E →+* ℂ) : Guard.Indep Z.t x (g.v τ) := by
  intro cf cf' w h1 h2
  refine (g.basis τ w (Guard.comb_tan (g.tan τ) h1) fun a => ?_).unique h1 h2
  rw [← (isCombAtG_iff Z.t _ (fun j => ovT (g.tan τ j)) _ _).1 h1]
  have := Z.t.act.hom a
  exact congrArg (fun f => f.left) (combT_eig _ (fun j => ovT (g.tan τ j)) (Z.t.act.act a) _
    (fun j => Over.OverMorphism.ext (g.eig τ j a)) cf)

theorem grNorm_pos {Z : Model Xo c (algebraMap (𝓞 c.F) c.F)} (p : ℕ) [Fact p.Prime] (x : Sp ℂ_[p] ⟶ Z.X) {m : ℕ}
    {u : Fin m → (Sp (DualNumber ℂ_[p]) ⟶ Z.t.G.left)} (hu : ∀ k, IsTanAtG Z.t x (u k)) (hi : Guard.Indep Z.t x u)
    (b : Bool) (i : Fin m) : 0 < grNorm Z.t x (lat Z.t p x b) u i := by
  cases b
  · exact (Guard.grNorm_latDR_pos Z x hu hi i).2
  · exact (Guard.grNorm_latHT_pos Z HTBound.htBound p x hu hi i).2

theorem lnStep_change {Z : Model Xo c (algebraMap (𝓞 c.F) c.F)} {R : Type} [CommRing R] {φ φ' : c.F →+* R}
    {x : Sp R ⟶ Z.X} (f₁ : EigFrame Z φ x) (f : EigFrame Z φ' x) (u : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Rˣ)
    (hc : ∀ τ i, ∃ cf : Fin (Dw.mult τ) → R, cf i = u τ i ∧ (∀ k, i < k → cf k = 0) ∧
      IsCombAtG Z.t x (f₁.v τ) cf (f.v τ i))
    (p : ℕ) [Fact p.Prime] (ψ : R →+* ℂ_[p]) (b : Bool) (τ : E →+* ℂ) (k : ℕ) (hk : k < Dw.mult τ) :
    lnStep Z.t (spMap ψ ≫ x) (fun τ i => spMap (dualMap ψ) ≫ f.v τ i) p b (.inl (τ, k)) =
      Real.log ‖ψ (u τ ⟨k, hk⟩)‖ +
        lnStep Z.t (spMap ψ ≫ x) (fun τ i => spMap (dualMap ψ) ≫ f₁.v τ i) p b (.inl (τ, k)) := by
  obtain ⟨g₁, hg₁⟩ := f₁.exists_isMap ψ rfl rfl
  have hv : (fun i => spMap (dualMap ψ) ≫ f₁.v τ i) = g₁.v τ := funext fun i => (hg₁ τ i).symm
  have hd : ∀ i, ψ (u τ i) ≠ 0 := fun i => ((u τ i).isUnit.map ψ).ne_zero
  have e := Guard.grNorm_tri (Λ := lat Z.t p (spMap ψ ≫ x) b) (u := fun i => spMap (dualMap ψ) ≫ f₁.v τ i)
    (u' := fun i => spMap (dualMap ψ) ≫ f.v τ i) (fun i => GlobalTheory.FactorDepth.isTanAtG_map Z.t ψ (f₁.tan τ i)) hd
    (fun i => by
      obtain ⟨cf, h1, h2, h3⟩ := hc τ i
      exact ⟨fun a => ψ (cf a), congrArg ψ h1, fun a ha => (congrArg ψ (h2 a ha)).trans (map_zero ψ),
        GlobalTheory.LatDRFree.comb_map Z.t ψ h3⟩)
    ⟨k, hk⟩
  have pos := grNorm_pos p (spMap ψ ≫ x) (u := fun i => spMap (dualMap ψ) ≫ f₁.v τ i)
    (fun i => GlobalTheory.FactorDepth.isTanAtG_map Z.t ψ (f₁.tan τ i)) (by rw [hv]; exact indep_v g₁ τ) b ⟨k, hk⟩
  simp only [lnStep, dif_pos hk]
  rw [e, Real.log_mul (norm_ne_zero_iff.2 (hd _)) pos.ne']
  ring

section Flag

variable {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β} {F : Type} [Field F] {e : F ≃+* c.F}
  (Y : FlagCpt Z e)

theorem compare {y₀ : Y.Y.X} {χ χ₁ : c.F →+* Y.Y.X.presheaf.stalk y₀}
    {f : EigFrame Z χ (stalkPt Y.Y y₀ ≫ Y.π ≫ genι Z)} {f₁ : EigFrame Z χ₁ (stalkPt Y.Y y₀ ≫ Y.π ≫ genι Z)}
    {t t₁ : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Y.Y.Fnˣ}
    (a : f.Tri (algebraMap (Y.Y.X.presheaf.stalk y₀) Y.Y.X.functionField) Y.f0 t)
    (a₁ : f₁.Tri (algebraMap (Y.Y.X.presheaf.stalk y₀) Y.Y.X.functionField) Y.f0 t₁) :
    ∃ u : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Y.Y.X.presheaf.stalk y₀)ˣ,
      (∀ τ i, t₁ τ i = t τ i * Units.map (algebraMap _ Y.Y.X.functionField).toMonoidHom (u τ i)) ∧
      ∀ τ i, ∃ cf : Fin (Dw.mult τ) → Y.Y.X.presheaf.stalk y₀, cf i = u τ i ∧ (∀ k, i < k → cf k = 0) ∧
        IsCombAtG Z.t (stalkPt Y.Y y₀ ≫ Y.π ≫ genι Z) (f₁.v τ) cf (f.v τ i) := by
  have hι := IsFractionRing.injective (Y.Y.X.presheaf.stalk y₀) Y.Y.X.functionField
  obtain rfl : χ₁ = χ := RingHom.ext fun x => hι ((RingHom.congr_fun a₁.2.1 x).symm.trans (RingHom.congr_fun a.2.1 x))
  obtain ⟨k₁, hk₁⟩ := f₁.exists_isMap _ a.2.1 a.1
  obtain ⟨k, hk⟩ := f.exists_isMap _ a.2.1 a.1
  have e1 (τ i d) : k₁.co Y.f0 τ d i = ∑ j, k.co Y.f0 τ j i * algebraMap _ Y.Y.X.functionField (f₁.co f τ d j) := by
    rw [← k₁.co_mul k, hk₁.co τ hk a.1, Matrix.mul_apply]
    exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
  have hM (τ d i) (h : i < d) : f₁.co f τ d i = 0 := hι ((CoordUniq.tri_of_mul
    (M := fun i a => algebraMap _ Y.Y.X.functionField (f₁.co f τ a i)) (fun i a => (a₁.co τ hk₁).1 a i)
    (fun i a' => (a.co τ hk).1 a' i) (fun i => (a.co τ hk).2 i ▸ (t τ i).ne_zero) (e1 τ) i d h).trans
      (map_zero _).symm)
  have hu (τ i) : IsUnit (f₁.co f τ i i) := by
    have := f₁.isUnit_det_co f τ
    rw [Matrix.det_of_upperTriangular (M := f₁.co f τ) fun _ _ h => hM τ _ _ h] at this
    exact isUnit_of_dvd_unit (Finset.dvd_prod_of_mem (fun i => f₁.co f τ i i) (Finset.mem_univ i)) this
  refine ⟨fun τ i => (hu τ i).unit, fun τ i => Units.ext ?_, fun τ i => ⟨fun d => f₁.co f τ d i,
    (hu τ i).unit_spec.symm, fun d hd => hM τ d i hd, f₁.co_spec f τ i⟩⟩
  rw [← (a₁.co τ hk₁).2, e1, Units.val_mul, ← (a.co τ hk).2]
  exact CoordUniq.diag_of_mul (M := fun i a => algebraMap _ Y.Y.X.functionField (f₁.co f τ a i))
    (fun i a' => (a.co τ hk).1 a' i) (fun i a h => by simp only [hM τ a i h, map_zero]) i

end Flag

section Main

variable {Z : Model Xo c (algebraMap (𝓞 c.F) c.F)} {F : Type} [Field F] [NumberField F] {e : F ≃+* c.F}
  (Y : FlagCpt Z e)

theorem sum_letter (w : Sym E →₀ ℤ) (g : Letter Dw → ℝ) :
    ∑ a ∈ w.support, (w a : ℝ) * (letterOf Dw a.2.2).elim 0 g = ∑ x, (expo Dw w x : ℝ) * g x := by
  classical
  simp only [expo, Finsupp.sum, Int.cast_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  cases h : letterOf Dw a.2.2 with
  | none => simp
  | some z => simp [Finset.sum_ite_eq]

theorem lgFr_eq (w : Sym E →₀ ℤ) (v : HeightOneSpectrum (𝓞 F)) (ε : Ext v) (y : AlgPt Y.Y) [Fact (resP v).Prime]
    {χ χ₁ : c.F →+* Y.Y.X.presheaf.stalk (below y.1)}
    (f : EigFrame Z χ (stalkPt Y.Y (below y.1) ≫ Y.π ≫ genι Z))
    (f₁ : EigFrame Z χ₁ (stalkPt Y.Y (below y.1) ≫ Y.π ≫ genι Z))
    (t t₁ : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Y.Y.Fnˣ) (hw : ∀ a ∈ w.support, a.2.2.isLeft = true)
    (a : f.Tri (algebraMap (Y.Y.X.presheaf.stalk (below y.1)) Y.Y.X.functionField) Y.f0 t)
    (a₁ : f₁.Tri (algebraMap (Y.Y.X.presheaf.stalk (below y.1)) Y.Y.X.functionField) Y.f0 t₁)
    (ht : ∀ τ i, (Y.gr τ i).IsEqn (below y.1) (t τ i)) :
    lgFr Y w v ε y f₁ t₁ = lgFr Y w v ε y f t := by
  obtain ⟨u, hut, hc⟩ := compare Y a a₁
  let s : Y.Y.X.presheaf.stalk (below y.1) →+* AlgebraicClosure F := (Scheme.stalkClosedPointTo y.1).hom
  let ψ : Y.Y.X.presheaf.stalk (below y.1) →+* ℂ_[resP v] := (ioOf (resP v) ε).comp s
  let L : Letter Dw → ℝ := fun x => Real.log ‖ψ (u x.1 x.2)‖
  let Δ := divOf Y (expo Dw w)
  let U : (Y.Y.X.presheaf.stalk (below y.1))ˣ := ∏ x : Letter Dw, u x.1 x.2 ^ expo Dw w x

  have hE : ∀ S : Finset (Letter Dw),
      (∑ x ∈ S, expo Dw w x • Y.gr x.1 x.2).IsEqn (below y.1) (∏ x ∈ S, t x.1 x.2 ^ expo Dw w x) := fun S => by
    classical
    induction S using Finset.induction_on with
    | empty => simpa using CartierDiv.isEqn_zero (below y.1)
    | insert z S hz ih => rw [Finset.sum_insert hz, Finset.prod_insert hz]; exact ((ht _ _).zsmul _).add ih
  have hU : UnitAt (below y.1) (((∏ x : Letter Dw, t x.1 x.2 ^ expo Dw w x) * (eqn Δ (below y.1))⁻¹ : Y.Y.Fnˣ) :
      Y.Y.Fn) := by
    have := (isEqn_eqn Δ (below y.1)).iff_unitAt.1 (hE Finset.univ)
    simpa [div_eq_mul_inv] using this
  have hprod : ((∏ x : Letter Dw, t₁ x.1 x.2 ^ expo Dw w x) * (eqn Δ (below y.1))⁻¹ : Y.Y.Fnˣ) =
      ((∏ x : Letter Dw, t x.1 x.2 ^ expo Dw w x) * (eqn Δ (below y.1))⁻¹) *
        Units.map (algebraMap _ Y.Y.X.functionField).toMonoidHom U := by
    simp only [hut, mul_zpow, Finset.prod_mul_distrib, U, map_prod, map_zpow]
    rw [mul_right_comm]
  have hv2 : valAt y.1 ((Units.map (algebraMap _ Y.Y.X.functionField).toMonoidHom U : Y.Y.Fnˣ) : Y.Y.Fn) = s U :=
    Res.valAt_algebraMap y.1 _
  have hN : Real.log ‖ψ U‖ = ∑ x, (expo Dw w x : ℝ) * L x := by
    have h1 : ψ U = ∏ x : Letter Dw, ψ (u x.1 x.2) ^ expo Dw w x := by
      refine (congrArg Units.val (map_prod (Units.map ψ.toMonoidHom) _ _)).trans ?_
      simp only [map_zpow, Units.coe_prod, Units.val_zpow_eq_zpow_val]
      rfl
    rw [h1, norm_prod, Real.log_prod (fun x _ => norm_ne_zero_iff.2 (zpow_ne_zero _ ((u x.1 x.2).isUnit.map ψ).ne_zero))]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [norm_zpow, Real.log_zpow]
  have hA : Real.log (ε.w (valAt y.1 (((∏ x : Letter Dw, t₁ x.1 x.2 ^ expo Dw w x) * (eqn Δ (below y.1))⁻¹ :
      Y.Y.Fnˣ) : Y.Y.Fn))) = Real.log (ε.w (valAt y.1 (((∏ x : Letter Dw, t x.1 x.2 ^ expo Dw w x) *
      (eqn Δ (below y.1))⁻¹ : Y.Y.Fnˣ) : Y.Y.Fn))) +
      (-Real.log (ε.w (resP v)) / Real.log (resP v)) * ∑ x, (expo Dw w x : ℝ) * L x := by
    rw [hprod, Units.val_mul, Res.valAt_mul (g := ((Units.map (algebraMap _ Y.Y.X.functionField).toMonoidHom U : Y.Y.Fnˣ) :
      Y.Y.Fn)) hU.regAt ⟨(U : Y.Y.X.presheaf.stalk (below y.1)), rfl⟩, hv2, map_mul,
      Real.log_mul (ε.w.ne_zero (Res.valAt_ne_zero hU)) (ε.w.ne_zero ((U.isUnit.map s).ne_zero)),
      log_w_eq (resP v) ε (ioOf (resP v) ε) (ioOf_le_one_iff _ (residueCharacteristic_mem v) ε) (s U), ← hN]
    rfl

  have hS : ∀ a ∈ w.support, lnStep Z.t (spMap ψ ≫ stalkPt Y.Y (below y.1) ≫ Y.π ≫ genι Z)
      (fun τ i => spMap (dualMap ψ) ≫ f.v τ i) (resP v) (a.1 (resP v)) a.2.2 =
      lnStep Z.t (spMap ψ ≫ stalkPt Y.Y (below y.1) ≫ Y.π ≫ genι Z)
        (fun τ i => spMap (dualMap ψ) ≫ f₁.v τ i) (resP v) (a.1 (resP v)) a.2.2 + (letterOf Dw a.2.2).elim 0 L := by
    intro a ha
    obtain ⟨b, R, ⟨τ, k⟩ | k⟩ := a
    · by_cases hk : k < Dw.mult τ
      · rw [lnStep_change f₁ f u hc (resP v) ψ _ τ k hk, add_comm]
        simp only [letterOf, dif_pos hk, Option.elim, L]
      · simp [lnStep, letterOf, hk]
    · exact absurd (hw _ ha) (by simp)
  have hsum : (w.sum fun a n => (n : ℝ) * lnStep Z.t (spMap ψ ≫ stalkPt Y.Y (below y.1) ≫ Y.π ≫ genι Z)
      (fun τ i => spMap (dualMap ψ) ≫ f.v τ i) (resP v) (a.1 (resP v)) a.2.2) =
      (w.sum fun a n => (n : ℝ) * lnStep Z.t (spMap ψ ≫ stalkPt Y.Y (below y.1) ≫ Y.π ≫ genι Z)
        (fun τ i => spMap (dualMap ψ) ≫ f₁.v τ i) (resP v) (a.1 (resP v)) a.2.2) + ∑ x, (expo Dw w x : ℝ) * L x := by
    simp only [Finsupp.sum]
    rw [Finset.sum_congr rfl fun a ha => by rw [hS a ha, mul_add], Finset.sum_add_distrib, sum_letter]
  show _ + _ * _ = _ + _ * _
  rw [hA]
  erw [hsum]
  ring

theorem lgOf_eq_lgFr (w : Sym E →₀ ℤ) (v : HeightOneSpectrum (𝓞 F)) (ε : Ext v) (y : AlgPt Y.Y) (hp : (resP v).Prime) :
    lgOf Y w v ε y = @lgFr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Y w v ε y (GlobalTheory.ShFam.Pad.lgOf._proof_5 v hp) _
      (GlobalTheory.ShFam.Pad.lgOf._proof_3 Y y).choose (GlobalTheory.ShFam.Pad.lgOf._proof_4 Y y).choose := by
  unfold lgOf lgFr
  rewrite [dif_pos hp]
  refine congrArg₂ HAdd.hAdd rfl (congrArg₂ HMul.hMul rfl (congrArg (Finsupp.sum w)
    (funext fun a => funext fun n => congrArg₂ HMul.hMul rfl ?_)))
  rfl

end Main

end GlobalTheory.ShFam.GalCarry.AnyFrame

open GlobalTheory.ShFam.GalCarry.AnyFrame in

theorem _root_.GlobalTheory.T.tri_equation_log_independent : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E]
    (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l)
    (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c (algebraMap (𝓞 c.F) c.F)) (F : Type) [Field F] [NumberField F]
    (e : F ≃+* c.F) (Y : FlagCpt Z e), TriEqn Y → LgIndep Y := by
  intro E _ _ _ H Dw l Xo c Z F _ _ e Y hT w v ε y hp χ f t hw ha
  obtain rfl : hp = GlobalTheory.ShFam.Pad.lgOf._proof_5 v (residueCharacteristic_prime v) := Subsingleton.elim _ _
  refine (lgOf_eq_lgFr Y w v ε y (residueCharacteristic_prime v)).trans ?_
  exact @lgFr_eq _ _ _ _ _ _ _ _ _ _ _ _ _ _ Y w v ε y (GlobalTheory.ShFam.Pad.lgOf._proof_5 v (residueCharacteristic_prime v)) _ _ f _ t _ hw ha
    (GlobalTheory.ShFam.Pad.lgOf._proof_4 Y y).choose_spec.1 (hT _ χ f t ha)
