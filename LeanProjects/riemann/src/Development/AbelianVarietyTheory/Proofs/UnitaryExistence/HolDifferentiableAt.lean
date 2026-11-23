import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.FlagBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.EigLatBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.CubicalExtendsSt
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsTestFunctionsSubsetOfMemNhds
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsEtaleCoordsVanishing
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TangentBijectionOfValues

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Filter Topology GlobalTheory.TangentOrigin

noncomputable section

namespace GlobalTheory.LocalLift

variable {Y : Scheme.{0}}

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField in
open scoped CategoryTheory.Obj in
open Filter Topology in
variable {Y : Scheme.{0}} in
theorem _root_.GlobalTheory.LocalLift.hol_eventually_mem {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    {B : Set V} {y : V → (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℂ ⟶ Y)}
    (hy : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsHolTo B y) {b : V} (hb : b ∈ B) {U : Y.Opens} (hU : ⊤ ≤ y b ⁻¹ᵁ U) :
    ∀ᶠ z in 𝓝 b, z ∈ B ∧ ⊤ ≤ y z ⁻¹ᵁ U :=
  (hy U 0).1.mem_nhds ⟨hb, hU⟩

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField in
open scoped CategoryTheory.Obj in
open Filter Topology in
variable {Y : Scheme.{0}} in
theorem _root_.GlobalTheory.LocalLift.hol_differentiableAt {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    {B : Set V} {y : V → (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℂ ⟶ Y)}
    (hy : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsHolTo B y) {b : V} (hb : b ∈ B) {U : Y.Opens} (hU : ⊤ ≤ y b ⁻¹ᵁ U) (f : Γ(Y, U)) :
    DifferentiableAt ℂ (fun z => _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt' (y z) U f) b :=
  ((hy U f).2 b ⟨hb, hU⟩).differentiableAt ((hy U f).1.mem_nhds ⟨hb, hU⟩)

theorem exists_chart (s : Y ⟶ Sp ℂ) [Smooth s] (x : Sp ℂ ⟶ Y) (hx : x ≫ s = 𝟙 _) :
    ∃ (n : ℕ) (U : Y.Opens) (t : Fin n → Γ(Y, U)) (W : Set (Fin n → ℂ)) (p : (Fin n → ℂ) → (Sp ℂ ⟶ Y)),
      IsAffineOpen U ∧ ⊤ ≤ x ⁻¹ᵁ U ∧ 0 ∈ W ∧ p 0 = x ∧ IsHolTo W p ∧ (∀ w, p w ≫ s = 𝟙 _) ∧
      (∀ w ∈ W, ∀ i, valAt' (p w) U (t i) = w i) ∧
      ∀ (g : ℕ) (e : (Fin g → ℂ) → (Sp ℂ ⟶ Y)), (∀ z, e z ≫ s = 𝟙 _) → IsHolTo Set.univ e → e 0 = x →
        ∀ᶠ z in 𝓝 (0 : Fin g → ℂ), e z = p (fun i => valAt' (e z) U (t i)) := by
  obtain ⟨U₀, -, U, hU, hp, hle, hsm⟩ := Smooth.exists_isStandardSmooth s (x (default : PrimeSpectrum ℂ))
  have hU₀ : U₀ = ⊤ := by
    refine eq_top_iff.2 fun y _ => ?_
    have h1 : s (x (default : PrimeSpectrum ℂ)) ∈ U₀ := hle hp
    have h2 : y = s (x (default : PrimeSpectrum ℂ)) :=
      Subsingleton.elim (α := PrimeSpectrum ℂ) _ _
    rw [h2]; exact h1
  subst hU₀
  obtain ⟨n, hn⟩ : ∃ n, RingHom.IsStandardSmoothOfRelativeDimension n (s.appLE ⊤ U hle).hom := by
    let _ := (s.appLE ⊤ U hle).hom.toAlgebra
    have : Algebra.IsStandardSmooth Γ(Sp ℂ, ⊤) Γ(Y, U) := hsm
    obtain ⟨_, _, _, _, ⟨P⟩⟩ := this
    exact ⟨P.dimension, _, _, _, ‹_›, P, rfl⟩
  let c : ℂ →+* Γ(Y, U) :=
    (s.appLE ⊤ U hle).hom.comp (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom
  have hcc : ∀ a, constFn s U a = c a := fun a => rfl
  have hc : c.IsStandardSmoothOfRelativeDimension n :=
    RingHom.isStandardSmoothOfRelativeDimension_respectsIso.2 (s.appLE ⊤ U hle).hom
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).symm.commRingCatIsoToRingEquiv hn
  have hpts : ∀ (y : Sp ℂ ⟶ Y) (hy : ⊤ ≤ y ⁻¹ᵁ U), y ≫ s = 𝟙 _ → ∀ a, evalPt y U hy (c a) = a := by
    intro y hy hys a
    rw [← valAt'_eq_evalPt, ← hcc]
    exact valAt'_constFn y s hys U a hy
  have hxU : ⊤ ≤ x ⁻¹ᵁ U := (top_le_preimage_iff_mem x U).2 hp
  obtain ⟨φ, hφc, hφ, hφ0⟩ := HolChart.exists_etale_coords_vanishing c hc (evalPt x U hxU) (hpts x hxU hx)
  let _ : Algebra ℂ Γ(Y, U) := c.toAlgebra
  let _ : Algebra (MvPolynomial (Fin n) ℂ) Γ(Y, U) := φ.toAlgebra
  have _ : IsScalarTower ℂ (MvPolynomial (Fin n) ℂ) Γ(Y, U) :=
    IsScalarTower.of_algebraMap_eq' hφc.symm
  have _ : Algebra.Etale (MvPolynomial (Fin n) ℂ) Γ(Y, U) := hφ
  let eA : Γ(Y, U) →ₐ[ℂ] ℂ := { evalPt x U hxU with commutes' := hpts x hxU hx }
  obtain ⟨W, σ, m, f, ε, hW, hW0, hσ0, hε, hσd, hσt, hσs⟩ :=
    exists_holomorphic_section_of_etale n Γ(Y, U) eA hφ0
  choose p hpU hpσ using fun w => exists_evalPt_eq hU (σ w).toRingHom
  have hval : ∀ w a, valAt' (p w) U a = σ w a := fun w a => by
    rw [valAt'_eq_evalPt _ _ (hpU w), hpσ]; rfl
  refine ⟨n, U, fun i => φ (MvPolynomial.X i), W, p, hU, hxU, hW0, ?_, ?_, ?_, ?_, ?_⟩
  · refine ext_evalPt hU (hpU 0) hxU ?_
    rw [hpσ, hσ0]
  · intro V a
    refine HolChart.hol_of_affine valAt'_rules hU hW p (fun w _ => hpU w) (fun b => ?_) V a
    simpa only [hval] using hσd b
  · intro w
    refine (eq_spMap_of_evalPt _ (RingHom.id ℂ) fun a => ?_).trans (Spec.map_id _)
    rw [← evalPt_constFn s (p w) U (hpU w), hpσ, hcc]
    exact (σ w).commutes a
  · intro w hw i
    rw [hval]; exact hσt w hw i
  · intro g e hes he he0
    have h0 : ⊤ ≤ e 0 ⁻¹ᵁ U := he0 ▸ hxU
    have hk : ∀ᶠ z in 𝓝 (0 : Fin g → ℂ), ∀ k, ‖valAt' (e z) U (f k) - eA (f k)‖ < ε := by
      refine eventually_all.2 fun k => ?_
      have h1 := (hol_differentiableAt he (Set.mem_univ _) h0 (f k)).continuousAt
      have h2 : valAt' (e 0) U (f k) = eA (f k) := by
        rw [he0, valAt'_eq_evalPt _ _ hxU]; rfl
      have := h1.eventually (Metric.ball_mem_nhds _ hε)
      simpa only [Metric.mem_ball, dist_eq_norm, h2] using this
    filter_upwards [hk, hol_eventually_mem he (Set.mem_univ _) h0] with z hz hzU
    let xA : Γ(Y, U) →ₐ[ℂ] ℂ := { evalPt (e z) U hzU.2 with commutes' := hpts _ hzU.2 (hes z) }
    have hxA : ∀ a, xA a = valAt' (e z) U a := fun a => (valAt'_eq_evalPt _ _ hzU.2 a).symm
    obtain ⟨w, hw, hxw⟩ := hσs xA (fun k => by rw [hxA]; exact hz k)
    have hwe : (fun i => valAt' (e z) U (φ (MvPolynomial.X i))) = w := by
      funext i
      rw [← hxA, hxw]; exact hσt w hw i
    rw [hwe]
    refine ext_evalPt hU hzU.2 (hpU w) ?_
    rw [hpσ, ← hxw]

theorem exists_tangent {n : ℕ} (s : Y ⟶ Sp ℂ) {W : Set (Fin n → ℂ)} (hW : 0 ∈ W) {p : (Fin n → ℂ) → (Sp ℂ ⟶ Y)}
    (hp : IsHolTo W p) (hps : ∀ w, p w ≫ s = 𝟙 _) {U : Y.Opens} (hU : IsAffineOpen U) (h0 : ⊤ ≤ p 0 ⁻¹ᵁ U)
    (u : Fin n → ℂ) :
    ∃ (v : Sp (DualNumber ℂ) ⟶ Y) (h : ⊤ ≤ v ⁻¹ᵁ U), v ≫ s = spMap (algebraMap ℂ (DualNumber ℂ)) ∧
      spMap fstC ≫ v = p 0 ∧ ∀ f, (evalPt v U h f).snd = fderiv ℂ (fun z => valAt' (p z) U f) 0 u := by
  have hd := hol_differentiableAt hp hW h0
  have hconst : ∀ a, fderiv ℂ (fun z => valAt' (p z) U (constFn s U a)) 0 = 0 := by
    intro a
    have : (fun z => valAt' (p z) U (constFn s U a)) =ᶠ[𝓝 0] fun _ => a := by
      filter_upwards [hol_eventually_mem hp hW h0] with z hz
      exact valAt'_constFn _ s (hps z) U a hz.2
    rw [this.fderiv_eq]; simp
  let J : Γ(Y, U) →+* DualNumber ℂ :=
    { toFun := fun f => TrivSqZeroExt.inl (valAt' (p 0) U f) +
        TrivSqZeroExt.inr (fderiv ℂ (fun z => valAt' (p z) U f) 0 u)
      map_one' := by
        have := hconst 1
        rw [show constFn s U 1 = 1 by simp [constFn]] at this
        ext <;> simp [this, valAt'_one _ h0]
      map_zero' := by
        ext <;> simp [valAt'_zero]
      map_add' := fun f f' => by
        ext <;> simp [valAt'_add, fderiv_fun_add (hd f) (hd f')]
      map_mul' := fun f f' => by
        ext <;> simp [valAt'_mul, fderiv_fun_mul (hd f) (hd f'), mul_comm] }
  obtain ⟨v, hv, hve⟩ := exists_evalPt_eq hU J
  refine ⟨v, hv, ?_, ?_, fun f => ?_⟩
  · refine eq_spMap_of_evalPt _ _ fun a => ?_
    rw [← evalPt_constFn s v U hv, hve]
    ext <;> simp [J, hconst, valAt'_constFn _ s (hps 0) U a h0, TrivSqZeroExt.algebraMap_eq_inl]
  · refine ext_evalPt hU ((top_le_preimage_iff v U).1 hv) h0 (RingHom.ext fun f => ?_)
    refine (evalPt_spMap_comp fstC v U hv _ f).trans ?_
    rw [hve, ← valAt'_eq_evalPt]
    simp [J]
  · rw [hve]; simp [J]

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField in
open scoped CategoryTheory.Obj in
open Filter Topology in
variable {Y : Scheme.{0}} in

theorem _root_.GlobalTheory.LocalLift.isDerivAt0_const {g : ℕ} (e : (Fin g → ℂ) → (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℂ ⟶ Y))
    (w : Fin g → ℂ)
    (h : ∀ (U : Y.Opens) (f : Γ(Y, U)), ⊤ ≤ e 0 ⁻¹ᵁ U →
      fderiv ℂ (fun z => _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt' (e z) U f) 0 w = 0) :
    _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsDerivAt0 e w (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap ℂ (DualNumber ℂ)) ≫ e 0) := by
  have hcomp : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫
      _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap ℂ (DualNumber ℂ)) ≫ e 0 = e 0 := by
    change Spec.map _ ≫ Spec.map _ ≫ _ = _
    rw [← Spec.map_comp_assoc]
    have hid : CommRingCat.ofHom (algebraMap ℂ (DualNumber ℂ)) ≫
        CommRingCat.ofHom (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom = 𝟙 _ := by
      ext a
      simp
    rw [hid, Spec.map_id, Category.id_comp]
  refine ⟨hcomp, fun U hv f => ?_⟩
  have h0 : ⊤ ≤ e 0 ⁻¹ᵁ U := by
    have hfst := (_root_.GlobalTheory.TangentOrigin.top_le_preimage_iff _ U).1 hv
    rwa [show _root_.GlobalTheory.TangentOrigin.fstC = (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom from rfl,
      hcomp] at hfst
  rw [h U f h0]
  have hval := _root_.GlobalTheory.TangentOrigin.evalPt_spMap_comp (algebraMap ℂ (DualNumber ℂ)) (e 0) U h0 hv f
  change TrivSqZeroExt.snd (_root_.GlobalTheory.TangentOrigin.evalPt _ U hv f) = 0
  rw [hval]
  exact TrivSqZeroExt.snd_inl _ _

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField in
open scoped CategoryTheory.Obj in
open Filter Topology in
variable {Y : Scheme.{0}} in

theorem _root_.GlobalTheory.LocalLift.exists_local_lift : ∀ (Y : Scheme.{0}) (s : Y ⟶ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℂ)
    (g g' : ℕ) (e : (Fin g → ℂ) → (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℂ ⟶ Y)) (e' : (Fin g' → ℂ) → (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℂ ⟶ Y)),
    Smooth s → (∀ z, e z ≫ s = 𝟙 _) → (∀ z, e' z ≫ s = 𝟙 _) → _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsHolTo Set.univ e →
    _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsHolTo Set.univ e' →
    ((∀ w, ∃! v : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp (DualNumber ℂ) ⟶ Y, v ≫ s = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap ℂ (DualNumber ℂ)) ∧
      _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsDerivAt0 e' w v) ∧
      ∀ v : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp (DualNumber ℂ) ⟶ Y, v ≫ s = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap ℂ (DualNumber ℂ)) →
        _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v = e' 0 → ∃! w, _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsDerivAt0 e' w v) →
    e 0 = e' 0 → ∃ k₀ : (Fin g → ℂ) → (Fin g' → ℂ), k₀ 0 = 0 ∧ AnalyticAt ℂ k₀ 0 ∧
      ∀ᶠ z in nhds (0 : Fin g → ℂ), e' (k₀ z) = e z := by
  intro Y s g g' e e' hs he he' hhe hhe' H h00
  obtain ⟨H1, H2⟩ := H
  set y := e' 0 with hy_def
  have hys : y ≫ s = 𝟙 _ := he' 0
  have hsub : Subsingleton (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℂ) := inferInstanceAs (Subsingleton (PrimeSpectrum ℂ))
  obtain ⟨U, hU, V, hV, hyV, hVU, hsm⟩ := Smooth.exists_isStandardSmooth s (y.base default)
  have hUtop : U = ⊤ := eq_top_iff.2 fun x _ => Subsingleton.elim (s.base (y.base default)) x ▸ hVU hyV
  subst hUtop
  have : ∃ n, (Scheme.Hom.appLE s ⊤ V hVU).hom.IsStandardSmoothOfRelativeDimension n := by
    algebraize [(Scheme.Hom.appLE s ⊤ V hVU).hom]
    obtain ⟨P, σ, hσ, hP, ⟨Q⟩⟩ := hsm
    exact ⟨Q.dimension, ⟨P, σ, hσ, hP, Q, rfl⟩⟩
  obtain ⟨n, hn⟩ := this
  let c : ℂ →+* Γ(Y, V) := (Scheme.Hom.appLE s ⊤ V hVU).hom.comp (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom
  have hc : c.IsStandardSmoothOfRelativeDimension n :=
    (RingHom.isStandardSmoothOfRelativeDimension_respectsIso (n := n)).2 _
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).symm.commRingCatIsoToRingEquiv hn
  have hyV' : ⊤ ≤ y ⁻¹ᵁ V := fun q _ => Subsingleton.elim default q ▸ hyV
  let ev : Γ(Y, V) →+* ℂ := _root_.GlobalTheory.TangentOrigin.evalPt y V hyV'
  have hconst : ∀ (x : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℂ ⟶ Y), x ≫ s = 𝟙 _ → ∀ (hx : ⊤ ≤ x ⁻¹ᵁ V) (a : ℂ),
      _root_.GlobalTheory.TangentOrigin.evalPt x V hx (c a) = a := by
    intro x hxs hx a
    have h1 := _root_.GlobalTheory.TangentOrigin.evalPt_constFn s x V hx a
    have hid : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (RingHom.id ℂ) = 𝟙 (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℂ) := by
      change Spec.map (𝟙 _) = _
      exact Spec.map_id _
    have key : ∀ (z : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℂ ⟶ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℂ) (hz : z = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (RingHom.id ℂ)) (h : ⊤ ≤ z ⁻¹ᵁ ⊤),
        _root_.GlobalTheory.TangentOrigin.evalPt z ⊤ h ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom a) = a := by
      rintro _ rfl h
      exact _root_.GlobalTheory.TangentOrigin.evalPt_spMap _ a
    exact h1.trans (key _ (hxs.trans hid.symm) _)
  have hev : ∀ a, ev (c a) = a := hconst y hys hyV'
  obtain ⟨φ, hφC, hφet, hφ0⟩ := _root_.GlobalTheory.HolChart.exists_etale_coords_vanishing c hc ev hev
  letI : Algebra ℂ Γ(Y, V) := c.toAlgebra
  letI : Algebra (MvPolynomial (Fin n) ℂ) Γ(Y, V) := φ.toAlgebra
  haveI : IsScalarTower ℂ (MvPolynomial (Fin n) ℂ) Γ(Y, V) := IsScalarTower.of_algebraMap_eq fun a => by
    change c a = φ (MvPolynomial.C a)
    rw [← hφC]; rfl
  haveI : Algebra.Etale (MvPolynomial (Fin n) ℂ) Γ(Y, V) := hφet
  let evA : Γ(Y, V) →ₐ[ℂ] ℂ := { ev with commutes' := fun a => hev a }
  obtain ⟨W, σ, m, fs, ε, hWo, hW0, hσ0, hε, hσhol, hσX, hσuniq⟩ :=
    _root_.GlobalTheory.exists_holomorphic_section_of_etale n Γ(Y, V) evA hφ0
  have hpt : ∀ w, ∃ x : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℂ ⟶ Y, ∃ h : ⊤ ≤ x ⁻¹ᵁ V, _root_.GlobalTheory.TangentOrigin.evalPt x V h = (σ w : Γ(Y, V) →+* ℂ) :=
    fun w => _root_.GlobalTheory.TangentOrigin.exists_evalPt_eq hV _
  choose pt hptV hpt using hpt
  let F : (Fin g' → ℂ) → (Fin n → ℂ) := fun z i => _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt' (e' z) V (φ (MvPolynomial.X i))
  let G : (Fin g → ℂ) → (Fin n → ℂ) := fun z i => _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt' (e z) V (φ (MvPolynomial.X i))
  have hyVe : ⊤ ≤ e 0 ⁻¹ᵁ V := by rw [h00]; exact hyV'
  have hlocal : ∀ (x : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℂ ⟶ Y), x ≫ s = 𝟙 _ → ∀ (hx : ⊤ ≤ x ⁻¹ᵁ V),
      (∀ k, ‖_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt' x V (fs k) - ev (fs k)‖ < ε) →
      (fun i => _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt' x V (φ (MvPolynomial.X i))) ∈ W ∧
        x = pt (fun i => _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt' x V (φ (MvPolynomial.X i))) := by
    intro x hxs hx hclose
    let ψ : Γ(Y, V) →ₐ[ℂ] ℂ :=
      { _root_.GlobalTheory.TangentOrigin.evalPt x V hx with commutes' := fun a => hconst x hxs hx a }
    obtain ⟨w, hw, hψw⟩ := hσuniq ψ (fun k => by
      have hk := hclose k
      rwa [_root_.GlobalTheory.TangentOrigin.valAt'_eq_evalPt x V hx] at hk)
    have hcoord : (fun i => _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt' x V (φ (MvPolynomial.X i))) = w := funext fun i => by
      rw [_root_.GlobalTheory.TangentOrigin.valAt'_eq_evalPt x V hx]
      change ψ (φ (MvPolynomial.X i)) = w i
      rw [hψw]
      exact hσX w hw i
    rw [hcoord]
    refine ⟨hw, _root_.GlobalTheory.TangentOrigin.ext_evalPt hV hx (hptV w) ?_⟩
    rw [hpt w]
    exact RingHom.ext fun a => DFunLike.congr_fun hψw a
  have hF_diff : ∀ᶠ z in 𝓝 (0 : Fin g' → ℂ), DifferentiableAt ℂ F z := by
    filter_upwards [_root_.GlobalTheory.LocalLift.hol_eventually_mem hhe' (Set.mem_univ 0) hyV'] with z hz
    exact differentiableAt_pi.2 fun i => _root_.GlobalTheory.LocalLift.hol_differentiableAt hhe' hz.1 hz.2 _
  have hG_diff : ∀ᶠ z in 𝓝 (0 : Fin g → ℂ), DifferentiableAt ℂ G z := by
    filter_upwards [_root_.GlobalTheory.LocalLift.hol_eventually_mem hhe (Set.mem_univ 0) hyVe] with z hz
    exact differentiableAt_pi.2 fun i => _root_.GlobalTheory.LocalLift.hol_differentiableAt hhe hz.1 hz.2 _
  have hF0 : F 0 = 0 := funext fun i => by
    change _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt' y V _ = 0
    rw [_root_.GlobalTheory.TangentOrigin.valAt'_eq_evalPt y V hyV']
    exact hφ0 i
  have hG0 : G 0 = 0 := funext fun i => by
    change _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt' (e 0) V _ = 0
    rw [h00, _root_.GlobalTheory.TangentOrigin.valAt'_eq_evalPt y V hyV']
    exact hφ0 i
  have hFe : ∀ᶠ z in 𝓝 (0 : Fin g' → ℂ), F z ∈ W ∧ e' z = pt (F z) := by
    have hcl : ∀ k, ∀ᶠ z in 𝓝 (0 : Fin g' → ℂ), ‖_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt' (e' z) V (fs k) - ev (fs k)‖ < ε := by
      intro k
      have hc := (_root_.GlobalTheory.LocalLift.hol_differentiableAt hhe' (Set.mem_univ 0) hyV' (fs k)).continuousAt
      have h0v : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt' (e' 0) V (fs k) = ev (fs k) :=
        _root_.GlobalTheory.TangentOrigin.valAt'_eq_evalPt _ V hyV' _
      filter_upwards [hc.eventually (Metric.ball_mem_nhds _ hε)] with z hz
      rwa [dist_eq_norm, h0v] at hz
    filter_upwards [Filter.eventually_all.2 hcl,
      _root_.GlobalTheory.LocalLift.hol_eventually_mem hhe' (Set.mem_univ 0) hyV'] with z hz hzV
    exact hlocal (e' z) (he' z) hzV.2 hz
  have hGe : ∀ᶠ z in 𝓝 (0 : Fin g → ℂ), G z ∈ W ∧ e z = pt (G z) := by
    have hcl : ∀ k, ∀ᶠ z in 𝓝 (0 : Fin g → ℂ), ‖_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt' (e z) V (fs k) - ev (fs k)‖ < ε := by
      intro k
      have hc := (_root_.GlobalTheory.LocalLift.hol_differentiableAt hhe (Set.mem_univ 0) hyVe (fs k)).continuousAt
      have h0v : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt' (e 0) V (fs k) = ev (fs k) := by
        rw [h00]
        exact _root_.GlobalTheory.TangentOrigin.valAt'_eq_evalPt _ V hyV' _
      filter_upwards [hc.eventually (Metric.ball_mem_nhds _ hε)] with z hz
      rwa [dist_eq_norm, h0v] at hz
    filter_upwards [Filter.eventually_all.2 hcl,
      _root_.GlobalTheory.LocalLift.hol_eventually_mem hhe (Set.mem_univ 0) hyVe] with z hz hzV
    exact hlocal (e z) (he z) hzV.2 hz
  have hbij : Function.Bijective (fderiv ℂ F 0) := by
    have hevcongr : ∀ (x x' : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp (DualNumber ℂ) ⟶ Y) (hxx : x = x') (hx : ⊤ ≤ x ⁻¹ᵁ V)
        (hx' : ⊤ ≤ x' ⁻¹ᵁ V), _root_.GlobalTheory.TangentOrigin.evalPt x V hx = _root_.GlobalTheory.TangentOrigin.evalPt x' V hx' := by
      rintro x _ rfl _ _; rfl
    have hevcongrC : ∀ (x x' : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℂ ⟶ Y) (hxx : x = x') (hx : ⊤ ≤ x ⁻¹ᵁ V)
        (hx' : ⊤ ≤ x' ⁻¹ᵁ V), _root_.GlobalTheory.TangentOrigin.evalPt x V hx = _root_.GlobalTheory.TangentOrigin.evalPt x' V hx' := by
      rintro x _ rfl _ _; rfl
    have hFi : ∀ w i, fderiv ℂ F 0 w i = fderiv ℂ (fun z => _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt' (e' z) V (φ (MvPolynomial.X i))) 0 w := by
      intro w i
      rw [fderiv_pi (fun i => _root_.GlobalTheory.LocalLift.hol_differentiableAt hhe' (Set.mem_univ 0) hyV' _)]
      rfl
    have hvV : ∀ v : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp (DualNumber ℂ) ⟶ Y,
        _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v = y → ⊤ ≤ v ⁻¹ᵁ V := by
      intro v hvy
      refine (_root_.GlobalTheory.TangentOrigin.top_le_preimage_iff v V).2 ?_
      rw [show _root_.GlobalTheory.TangentOrigin.fstC = (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom from rfl, hvy]
      exact hyV'
    have hfst : ∀ (v : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp (DualNumber ℂ) ⟶ Y) (hvy : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v = y)
        (hv : ⊤ ≤ v ⁻¹ᵁ V) (a : Γ(Y, V)), TrivSqZeroExt.fst (_root_.GlobalTheory.TangentOrigin.evalPt v V hv a) = ev a := by
      intro v hvy hv a
      have h' : ⊤ ≤ (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v) ⁻¹ᵁ V := by rw [hvy]; exact hyV'
      have h1 := _root_.GlobalTheory.TangentOrigin.evalPt_spMap_comp (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom v V hv h' a
      rw [hevcongrC _ _ hvy h' hyV'] at h1
      exact h1.symm
    have hcst : ∀ (v : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp (DualNumber ℂ) ⟶ Y), v ≫ s = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap ℂ (DualNumber ℂ)) →
        ∀ (hv : ⊤ ≤ v ⁻¹ᵁ V) (a : ℂ), _root_.GlobalTheory.TangentOrigin.evalPt v V hv (c a) = algebraMap ℂ (DualNumber ℂ) a := by
      intro v hvs hv a
      have h1 := _root_.GlobalTheory.TangentOrigin.evalPt_constFn s v V hv a
      have key : ∀ (z : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp (DualNumber ℂ) ⟶ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℂ) (hz : z = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap ℂ (DualNumber ℂ)))
          (h : ⊤ ≤ z ⁻¹ᵁ ⊤), _root_.GlobalTheory.TangentOrigin.evalPt z ⊤ h ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom a) =
            algebraMap ℂ (DualNumber ℂ) a := by
        rintro _ rfl h
        exact _root_.GlobalTheory.TangentOrigin.evalPt_spMap _ a
      exact h1.trans (key _ hvs _)
    let v0 : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp (DualNumber ℂ) ⟶ Y := _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap ℂ (DualNumber ℂ)) ≫ y
    have hv0y : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v0 = y := by
      change Spec.map _ ≫ Spec.map _ ≫ _ = _
      rw [← Spec.map_comp_assoc]
      have hid : CommRingCat.ofHom (algebraMap ℂ (DualNumber ℂ)) ≫
          CommRingCat.ofHom (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom = 𝟙 _ := by
        ext a
        simp
      rw [hid, Spec.map_id, Category.id_comp]
    have hv0s : v0 ≫ s = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap ℂ (DualNumber ℂ)) := by
      change _ ≫ y ≫ s = _
      rw [hys, Category.comp_id]
    constructor
    · refine (injective_iff_map_eq_zero (fderiv ℂ F 0)).2 fun w hw => ?_
      obtain ⟨v, ⟨hvs, hvd⟩, -⟩ := H1 w
      have hvy : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v = y := hvd.1
      have hv := hvV v hvy
      let D : Γ(Y, V) →+ ℂ :=
        { toFun := fun a => TrivSqZeroExt.snd (_root_.GlobalTheory.TangentOrigin.evalPt v V hv a)
          map_zero' := by simp
          map_add' := fun a b => by simp }
      have hD : D = 0 := by
        refine _root_.GlobalTheory.HolChart.derivation_eq_zero φ hφet ev D (fun a => ?_) (fun a b => ?_) (fun i => ?_)
        · change TrivSqZeroExt.snd (_root_.GlobalTheory.TangentOrigin.evalPt v V hv (φ (MvPolynomial.C a))) = 0
          rw [← RingHom.comp_apply φ, hφC, hcst v hvs hv a]
          exact TrivSqZeroExt.snd_inl _ _
        · change TrivSqZeroExt.snd (_root_.GlobalTheory.TangentOrigin.evalPt v V hv (a * b)) =
            ev a * TrivSqZeroExt.snd (_root_.GlobalTheory.TangentOrigin.evalPt v V hv b) +
              ev b * TrivSqZeroExt.snd (_root_.GlobalTheory.TangentOrigin.evalPt v V hv a)
          rw [map_mul, TrivSqZeroExt.snd_mul, hfst v hvy hv a, hfst v hvy hv b]
          simp [smul_eq_mul, mul_comm]
        · change TrivSqZeroExt.snd (_root_.GlobalTheory.TangentOrigin.evalPt v V hv (φ (MvPolynomial.X i))) = 0
          have h2 := hvd.2 V hv (φ (MvPolynomial.X i))
          refine h2.trans ?_
          rw [← hFi, hw]
          rfl
      have hv0V : ⊤ ≤ v0 ⁻¹ᵁ V := hvV v0 hv0y
      have hvv0 : v = v0 := by
        refine _root_.GlobalTheory.TangentOrigin.ext_evalPt hV hv hv0V (RingHom.ext fun a => ?_)
        have h0 := _root_.GlobalTheory.TangentOrigin.evalPt_spMap_comp (algebraMap ℂ (DualNumber ℂ)) y V hyV' hv0V a
        rw [h0]
        refine TrivSqZeroExt.ext ?_ ?_
        · rw [hfst v hvy hv a]; rfl
        · exact (DFunLike.congr_fun hD a).trans (TrivSqZeroExt.snd_inl _ _).symm
      have h0d : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsDerivAt0 e' 0 v0 :=
        _root_.GlobalTheory.LocalLift.isDerivAt0_const e' 0 (fun U f _ => map_zero _)
      exact (H2 v0 hv0s hv0y).unique (hvv0 ▸ hvd) h0d
    · intro u
      let S : Γ(Y, V) → (Fin n → ℂ) → ℂ := fun a w => σ w a
      have hSd : ∀ a, DifferentiableAt ℂ (S a) 0 := fun a =>
        (hσhol a 0 hW0).differentiableAt (hWo.mem_nhds hW0)
      have hS0 : ∀ a, S a 0 = ev a := fun a => by
        change σ 0 a = ev a
        rw [hσ0]
        rfl
      let χ : Γ(Y, V) →+* DualNumber ℂ :=
        { toFun := fun a => TrivSqZeroExt.inl (ev a) + TrivSqZeroExt.inr (fderiv ℂ (S a) 0 u)
          map_one' := by
            have h1 : S 1 = fun _ => 1 := funext fun w => map_one (σ w)
            rw [h1]
            ext <;> simp
          map_mul' := fun a b => by
            have hm : S (a * b) = S a * S b := funext fun w => map_mul (σ w) a b
            have hd : fderiv ℂ (S (a * b)) 0 u = S a 0 * fderiv ℂ (S b) 0 u + S b 0 * fderiv ℂ (S a) 0 u := by
              rw [hm, ((hSd a).hasFDerivAt.mul (hSd b).hasFDerivAt).fderiv]
              simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
            rw [hd, hS0, hS0]
            ext
            · simp
            · simp [smul_eq_mul]
              ring
          map_zero' := by
            have h0 : S 0 = fun _ => 0 := funext fun w => map_zero (σ w)
            rw [h0]
            ext <;> simp
          map_add' := fun a b => by
            have ha : S (a + b) = S a + S b := funext fun w => map_add (σ w) a b
            rw [ha, fderiv_add (hSd a) (hSd b)]
            ext <;> simp }
      have hχapp : ∀ a, χ a = TrivSqZeroExt.inl (ev a) + TrivSqZeroExt.inr (fderiv ℂ (S a) 0 u) := fun a => rfl
      obtain ⟨v, hv, hχ⟩ := _root_.GlobalTheory.TangentOrigin.exists_evalPt_eq hV χ
      have hvy : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v = y := by
        have h' : ⊤ ≤ (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v) ⁻¹ᵁ V :=
          (_root_.GlobalTheory.TangentOrigin.top_le_preimage_iff v V).1 hv
        refine _root_.GlobalTheory.TangentOrigin.ext_evalPt hV h' hyV' (RingHom.ext fun a => ?_)
        rw [_root_.GlobalTheory.TangentOrigin.evalPt_spMap_comp _ v V hv h' a, hχ]
        change TrivSqZeroExt.fst (χ a) = ev a
        rw [hχapp]
        simp
      have hvs : v ≫ s = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap ℂ (DualNumber ℂ)) := by
        refine _root_.GlobalTheory.TangentOrigin.eq_spMap_of_evalPt (v ≫ s) _ fun a => ?_
        rw [← _root_.GlobalTheory.TangentOrigin.evalPt_constFn s v V hv a, hχ]
        have hc' : S (c a) = fun _ => a := funext fun w => (σ w).commutes a
        change χ (c a) = _
        rw [hχapp]
        rw [hc', hev]
        refine TrivSqZeroExt.ext ?_ ?_
        · simp [TrivSqZeroExt.algebraMap_eq_inl]
        · simp [TrivSqZeroExt.algebraMap_eq_inl]
      obtain ⟨w, hw, -⟩ := H2 v hvs hvy
      refine ⟨w, funext fun i => ?_⟩
      rw [hFi, ← hw.2 V hv (φ (MvPolynomial.X i))]
      change TrivSqZeroExt.snd (_root_.GlobalTheory.TangentOrigin.evalPt v V hv _) = u i
      rw [hχ]
      have hXi : S (φ (MvPolynomial.X i)) =ᶠ[𝓝 0] fun w => w i := by
        filter_upwards [hWo.mem_nhds hW0] with w hw
        exact hσX w hw i
      rw [hχapp]
      rw [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add, hXi.fderiv_eq]
      rw [(hasFDerivAt_apply i (0 : Fin n → ℂ)).fderiv]
      rfl
  have hFan : AnalyticAt ℂ F 0 := _root_.GlobalTheory.SCV.analyticAt_iff_eventually_differentiableAt.2 hF_diff
  have hGan : AnalyticAt ℂ G 0 := _root_.GlobalTheory.SCV.analyticAt_iff_eventually_differentiableAt.2 hG_diff
  let L : (Fin g' → ℂ) ≃L[ℂ] (Fin n → ℂ) := ContinuousLinearEquiv.ofBijective (fderiv ℂ F 0)
    (LinearMap.ker_eq_bot.2 hbij.1) (LinearMap.range_eq_top.2 hbij.2)
  have hL : HasFDerivAt F (L : (Fin g' → ℂ) →L[ℂ] (Fin n → ℂ)) 0 := by
    rw [ContinuousLinearEquiv.coe_ofBijective]
    exact hFan.differentiableAt.hasFDerivAt
  have hFc : ContDiffAt ℂ 1 F 0 := hFan.contDiffAt
  have hS : HasStrictFDerivAt F (L : (Fin g' → ℂ) →L[ℂ] (Fin n → ℂ)) 0 :=
    hFc.hasStrictFDerivAt' hL one_ne_zero
  let Finv := HasStrictFDerivAt.localInverse F L 0 hS
  have hinvc : ContDiffAt ℂ 1 Finv (F 0) := hFc.to_localInverse hL one_ne_zero
  have hinvan : AnalyticAt ℂ Finv (F 0) := _root_.GlobalTheory.SCV.analyticAt_iff_eventually_differentiableAt.2
    ((hinvc.eventually (by simp)).mono fun p hp => hp.differentiableAt one_ne_zero)
  have hinv0 : Finv (F 0) = 0 := hS.localInverse_apply_image
  refine ⟨Finv ∘ G, ?_, ?_, ?_⟩
  · change Finv (G 0) = 0
    rw [hG0, ← hF0, hinv0]
  · have hA : AnalyticAt ℂ Finv (G 0) := by rw [hG0, ← hF0]; exact hinvan
    exact hA.comp hGan
  · have hGt : Tendsto G (𝓝 0) (𝓝 (F 0)) := by
      rw [hF0, ← hG0]; exact hGan.continuousAt.tendsto
    have hFt : Tendsto Finv (𝓝 (F 0)) (𝓝 0) := by
      have ht := hinvan.continuousAt.tendsto
      rwa [hinv0] at ht
    filter_upwards [hGt.eventually hS.eventually_right_inverse, (hFt.comp hGt).eventually hFe, hGe]
      with z h1 h2 h3
    simp only [Function.comp_apply] at h2 ⊢
    rw [h2.2, h1, ← h3.2]

end GlobalTheory.LocalLift
