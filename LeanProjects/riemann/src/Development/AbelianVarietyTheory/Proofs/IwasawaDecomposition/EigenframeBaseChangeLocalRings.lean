import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OrbitThickSt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFrPtOfEigFrame
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsLocalHomOfAlgebraic
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonoSpMapRingOfIntegers
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueRuleOfRegular

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory GlobalTheory.ArcQ GlobalTheory.ArcCM GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.CuspFrom
open scoped LaurentSeries

namespace GlobalTheory.CuspFrom.Vanish

open GlobalTheory.ShFam.Descent GlobalTheory.FlagTan GlobalTheory.AllWt GlobalTheory.Cartier

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}
  {F : Type} [Field F] {e : F ≃+* c.F}

def FrameBC (Z : Model Xo c β) : Prop :=
  ∀ (R R' : Type) [CommRing R] [IsLocalRing R] [CommRing R'] [IsLocalRing R'] (φ : c.F →+* R) (x : Sp R ⟶ Z.X)
    (f : EigFrame Z φ x) (ψ : R →+* R'), ∃ g : EigFrame Z (ψ.comp φ) (spMap ψ ≫ x),
      ∀ τ i, g.v τ i = spMap (dualMap ψ) ≫ f.v τ i

theorem FrameBC.at (hbc : FrameBC Z) {R R' : Type} [CommRing R] [IsLocalRing R] [CommRing R'] [IsLocalRing R']
    {φ : c.F →+* R} {x : Sp R ⟶ Z.X} (f : EigFrame Z φ x) (ψ : R →+* R') {x' : Sp R' ⟶ Z.X}
    (hx : x' = spMap ψ ≫ x) : ∃ g : EigFrame Z (ψ.comp φ) x', ∀ τ i, g.v τ i = spMap (dualMap ψ) ≫ f.v τ i := by
  subst hx
  exact hbc R R' φ x f ψ

section Cpt

variable {C : FlagCpt Z e}

theorem exists_extension {A k : Type} [CommRing A] [IsDomain A] [ValuationRing A] [Field k] [Algebra A k]
    [IsFractionRing A k] (p : Sp k ⟶ C.Y.X) (xA : Sp A ⟶ gen Z) (h : p ≫ C.π = spMap (algebraMap A k) ≫ xA) :
    ∃ q : Sp A ⟶ C.Y.X, spMap (algebraMap A k) ≫ q = p ∧ q ≫ C.π = xA := by
  have : IsProper Z.s := by
    obtain ⟨N, i, _, hi⟩ := Z.proj
    have := isProper_str O N
    rw [← hi]; infer_instance
  have : IsIso (spMap e.toRingHom) := by
    have : IsIso (CommRingCat.ofHom e.toRingHom) := e.toCommRingCatIso.isIso_hom
    infer_instance
  have : IsProper (C.π ≫ genStr Z ≫ spMap e.toRingHom) := by rw [C.π_str]; infer_instance
  have : IsProper C.π := IsProper.of_comp C.π (genStr Z ≫ spMap e.toRingHom)
  have hv : ValuativeCriterion.Existence C.π := by
    have h : UniversallyClosed C.π := inferInstance
    rw [UniversallyClosed.eq_valuativeCriterion] at h
    exact h.1
  obtain ⟨⟨q, q1, q2⟩⟩ := (hv ⟨A, k, p, xA, ⟨h⟩⟩).exists_lift
  exact ⟨q, q1, q2⟩

theorem exists_local_factor {T : Type} [CommRing T] [IsLocalRing T] [Algebra c.F T] (q : Sp T ⟶ C.Y.X)
    (hq : q ≫ C.π ≫ genStr Z = spMap (algebraMap c.F T)) :
    ∃ (y : C.Y.X) (ψ : St C y →ₐ[c.F] T), IsLocalHom ψ.toRingHom ∧ spMap ψ.toRingHom ≫ pt C y = q ∧
      q (IsLocalRing.closedPoint T) = y :=
  have h : spMap (R := St C _) (Scheme.stalkClosedPointTo q).hom ≫ pt C _ = q :=
    Scheme.Spec_stalkClosedPointTo_fromSpecStalk q
  ⟨_, algOf _ h hq, inferInstanceAs (IsLocalHom (Scheme.stalkClosedPointTo q).hom), h, rfl⟩

theorem exists_zero_coeff {y : C.Y.X} {t : Ix Dw → (Fk C)ˣ} (ht : ∀ τ i, (C.gr τ i).IsEqn y (t (some ⟨τ, i⟩)))
    {ex : Ix Dw → ℤ} (hex : ex none = 0) {s : Fk C} (hs : (C.LEx ex).VanishesAt y s) :
    ∃ a ∈ IsLocalRing.maximalIdeal (St C y), toFk C y a * Descent.chi ex t = s := by
  obtain ⟨a, ha, h⟩ := (isEqn_LEx ht hex).vanishesAt_iff.1 hs
  refine ⟨a, ha, ?_⟩
  have h' : toFk C y a = s * ((Descent.chi ex t)⁻¹ : (Fk C)ˣ) := h
  rw [h', mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, mul_one]

end Cpt

theorem chi_congr {A : Type} [CommRing A] {ex : Ix Dw → ℤ} (hex : ex none = 0) {t u : Ix Dw → Aˣ}
    (h : ∀ x, t (some x) = u (some x)) : Descent.chi ex t = Descent.chi ex u := by
  simp only [Descent.chi, Fintype.prod_option, hex, zpow_zero, one_mul, h]

section Core

theorem exists_mem_of_wit (hbc : FrameBC Z) {C : FlagCpt Z e} {A k : Type} [CommRing A] [IsDomain A] [ValuationRing A]
    [Field k] [Algebra A k] [IsFractionRing A k] [Algebra c.F A] [Algebra c.F k] [IsScalarTower c.F A k]
    (xA : Sp A ⟶ gen Z) (hxA : xA ≫ genStr Z = spMap (algebraMap c.F A))
    (gA : EigFrame Z (algebraMap c.F A) (xA ≫ genι Z)) (z : FrPt Xo c k) {φk : c.F →+* k} {xk : Sp k ⟶ Z.X}
    (gk : EigFrame Z φk xk) (hxk : xk = spMap (algebraMap A k) ≫ xA ≫ genι Z) (hφk : φk = algebraMap c.F k)
    (hgk : ∀ τ i, gk.v τ i = spMap (dualMap (algebraMap A k)) ≫ gA.v τ i) (hTz : Comparison₂ z gk) (p : Sp k ⟶ C.Y.X)
    (hp : p ≫ C.π = spMap (algebraMap A k) ≫ xA) (w : Descent.Wit C p z)
    (hbd : xA (IsLocalRing.closedPoint A) ∈ genBd Z) {ex : Ix Dw → ℤ} (hex : ex none = 0) {f : Rul Xo c}
    (hf : f ∈ GlobalTheory.AllWt.secZ Xo c ex) (hv : C.Y.vanishOn (C.LEx ex) (C.val f) C.Ybd) :
    ∃ b ∈ IsLocalRing.maximalIdeal A, evR Xo c f z = algebraMap A k b := by
  obtain ⟨q, q1, q2⟩ := exists_extension p xA hp
  obtain ⟨y₀, ψ₀, hloc, hψ₀, hy₀⟩ := exists_local_factor q (by rw [← Category.assoc, q2, hxA])
  have hmem : y₀ ∈ C.Ybd := by
    have h1 : C.π y₀ ∈ genBd Z := by
      have e0 : C.π (q (IsLocalRing.closedPoint A)) = xA (IsLocalRing.closedPoint A) :=
        congrArg (fun g => g (IsLocalRing.closedPoint A)) q2
      rw [← hy₀, e0]; exact hbd
    exact (C.bd_supp y₀).2 h1
  obtain ⟨φ₀, f₀, t₀, hT, ht⟩ := C.gr_spec y₀
  obtain rfl : φ₀ = algebraMap c.F (St C y₀) := RingHom.ext fun a => toFk_injective C y₀
    ((DFunLike.congr_fun hT.2.1 a).symm.trans ((toFk C y₀).commutes a).symm)
  let T₀ : Ix Dw → (Fk C)ˣ := fun j => j.elim 1 fun x => t₀ x.1 x.2
  obtain ⟨a, ha, ha'⟩ := exists_zero_coeff (t := T₀) ht hex (hv y₀ hmem)
  have hpstr : p ≫ C.π ≫ genStr Z = spMap (algebraMap c.F k) := by
    rw [← Category.assoc]; exact str_of_over w.ov
  obtain ⟨y₂, χ₂, hχ₂, hy₂⟩ := exists_factor p hpstr
  have hspec : y₂ ⤳ y₀ := hy₂ ▸ specializes_of (ψ := (algebraMap A k).comp ψ₀.toRingHom) (p := p)
    (by rw [← sp_comp, Category.assoc, hψ₀, q1]) (IsLocalRing.closedPoint k)
  obtain ⟨sp, s1, s2⟩ := exists_spec hspec
  have e1 : χ₂.toRingHom.comp sp.toRingHom = (algebraMap A k).comp ψ₀.toRingHom := hom_eq (by
    rw [← sp_comp, ← sp_comp, Category.assoc, Category.assoc, s1, hχ₂, hψ₀, q1])
  obtain ⟨f₂, hf₂⟩ := hbc.at (x := pt C y₀ ≫ C.π ≫ genι Z) f₀ sp.toRingHom (x' := pt C y₂ ≫ C.π ≫ genι Z)
    (by rw [← s1, Category.assoc])
  have hy₂b : C.π y₂ ∉ genBd Z := fun hb => hb ⟨GlobalTheory.AllWt.ptF z (IsLocalRing.closedPoint k),
    (congrArg (fun g => g (IsLocalRing.closedPoint k)) w.ov).trans (congrArg C.π hy₂)⟩
  obtain ⟨xF, hxF⟩ := exists_lift_open (pt C y₂ ≫ C.π) fun h => hy₂b ((congrArg C.π (pt_closedPoint y₂)) ▸ h)
  have hφ₂ : sp.toRingHom.comp (algebraMap c.F (St C y₀)) = algebraMap c.F (St C y₂) := sp.comp_algebraMap
  obtain ⟨P, hP, hTP⟩ := exists_tie_point (S := St C y₂) (xF := xF) (x := pt C y₂ ≫ C.π ≫ genι Z)
    (by rw [← Z.jQ_over, ← Category.assoc, hxF, Category.assoc, pt_str])
    (by rw [Model.j, ← Category.assoc, hxF, Category.assoc]) hφ₂ f₂
  have := Z.jQ_open
  have hx0 : (fr0 C).x = spMap (toFk C y₂).toRingHom ≫ P.x := by
    rw [← ptF_fst, ← ptF_fst, ← Category.assoc]
    congr 1
    rw [← cancel_mono Z.jQ, frame_point_over, Category.assoc, hP, hxF, ← Category.assoc, toFk_pt]
  have e2 : (toFk C y₂).toRingHom.comp sp.toRingHom = (toFk C y₀).toRingHom := RingHom.ext s2
  have hTf : f₂.Tri (toFk C y₂).toRingHom (rationalEigenFrame C) t₀ := by
    refine ⟨?_, ?_, fun τ i => ?_⟩
    · show gpt C ≫ C.π ≫ genι Z = _
      rw [← toFk_pt C y₂, Category.assoc]
    · rw [← RingHom.comp_assoc, e2]; exact hT.2.1
    · obtain ⟨cf, c1, c2, c3⟩ := hT.2.2 τ i
      refine ⟨cf, c1, c2, ?_⟩
      have e : ∀ j, spMap (dualMap (toFk C y₂).toRingHom) ≫ f₂.v τ j = spMap (dualMap (toFk C y₀).toRingHom) ≫ f₀.v τ j :=
        fun j => by rw [hf₂, ← Category.assoc, dual_comp, e2]
      simp only [e]
      exact c3
  obtain ⟨u, hu1, hu2⟩ := hTP.bm_of_tri tie0 hx0 hTf
  have hC : Chart C y₂ P u := ⟨by rw [hP, hxF], hu1⟩
  obtain ⟨t', hb, -⟩ := w.transfer hC hχ₂
  have v1 := hb.evR hf
  have v2 := hu1.evR hf
  have hchi : Descent.chi ex u = Descent.chi ex T₀ := chi_congr hex fun x => hu2 x.1 x.2
  have hval : sp a = evR Xo c f P := toFk_injective C y₂ (by
    refine (Descent.chi ex T₀).isUnit.mul_left_cancel ?_
    rw [s2, mul_comm, ha', ← hchi]
    exact v2)
  obtain ⟨fA, hfA⟩ := hbc.at (x := pt C y₀ ≫ C.π ≫ genι Z) f₀ ψ₀.toRingHom (x' := xA ≫ genι Z)
    (by rw [← q2, ← hψ₀]; simp only [Category.assoc])
  have hT1 := hTP.tri_of_bm hTz hb
  have hF : fA.Tri (algebraMap A k) gk (fun τ i => t' (some ⟨τ, i⟩)) := by
    refine ⟨hxk, ?_, fun τ i => ?_⟩
    · have h3 : ψ₀.toRingHom.comp (algebraMap c.F (St C y₀)) = algebraMap c.F A := ψ₀.comp_algebraMap
      show φk = (algebraMap A k).comp (ψ₀.toRingHom.comp (algebraMap c.F (St C y₀)))
      rw [hφk, h3]; exact IsScalarTower.algebraMap_eq _ _ _
    · obtain ⟨cf, c1, c2, c3⟩ := hT1.2.2 τ i
      refine ⟨cf, c1, c2, ?_⟩
      have e : ∀ j, spMap (dualMap (algebraMap A k)) ≫ fA.v τ j = spMap (dualMap χ₂.toRingHom) ≫ f₂.v τ j :=
        fun j => by
          rw [hfA, hf₂, ← Category.assoc (spMap (dualMap (algebraMap A k))),
            ← Category.assoc (spMap (dualMap χ₂.toRingHom)), dual_comp, dual_comp, e1]
      simp only [e]
      exact c3
  have hG : gA.Tri (algebraMap A k) gk 1 := by
    refine ⟨hxk, ?_, fun τ i => ⟨Pi.single i 1, by simp, fun j hj => Pi.single_eq_of_ne hj.ne' _, ?_⟩⟩
    · rw [hφk]; exact IsScalarTower.algebraMap_eq _ _ _
    · have e : (fun j => spMap (dualMap (algebraMap A k)) ≫ gA.v τ j) = gk.v τ := funext fun j => (hgk τ j).symm
      rw [e]
      exact isCombAtG_single Z.t _ (gk.tan τ) i
  obtain ⟨uu, huu⟩ := CoordUniq.exists_unit_ratio fA gA (IsFractionRing.injective A k) hF hG
  have hu' := huu (algebraMap A k) gk _ _ hF hG
  let W : Aˣ := ∏ x : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)), uu x.1 x.2 ^ ex (some x)
  have hW : (Descent.chi ex t' : k) = algebraMap A k (W : A) := by
    have : Descent.chi ex t' = Units.map (algebraMap A k : A →* k) W := by
      simp only [Descent.chi, Fintype.prod_option, hex, zpow_zero, one_mul, W, map_prod, map_zpow]
      refine Finset.prod_congr rfl fun x _ => ?_
      rw [show t' (some x) = _ from hu' x.1 x.2]
      simp
    rw [this]; rfl
  have hψa : ψ₀ a ∈ IsLocalRing.maximalIdeal A := fun h => ha (isUnit_of_map_unit ψ₀.toRingHom a h)
  refine ⟨W * ψ₀ a, Ideal.mul_mem_left _ _ hψa, ?_⟩
  rw [v1, hW, ← hval, map_mul]
  congr 1
  exact DFunLike.congr_fun e1 a

theorem exists_mem_maximalIdeal_evR (hbc : FrameBC Z) {σ : c.F →+* ℂ} {N : ℕ} {U : Formalism.L2.PjFree.Unf Xo c σ N}
    (Φ : FlagTor Z e U) {A k : Type} [CommRing A] [IsDomain A] [ValuationRing A] [Field k] [IsAlgClosed k] [Algebra A k]
    [IsFractionRing A k] [Algebra c.F A] [Algebra c.F k] [IsScalarTower c.F A k]
    (xA : Sp A ⟶ gen Z) (hxA : xA ≫ genStr Z = spMap (algebraMap c.F A))
    (gA : EigFrame Z (algebraMap c.F A) (xA ≫ genι Z)) (z : FrPt Xo c k)
    (hz : GlobalTheory.AllWt.ptF z ≫ Z.jQ = spMap (algebraMap A k) ≫ xA)
    (hu : ∀ τ i, TanRel Z (GlobalTheory.AllWt.ptF z) (z.u τ i) (spMap (dualMap (algebraMap A k)) ≫ gA.v τ i))
    (hbd : xA (IsLocalRing.closedPoint A) ∈ genBd Z) {ex : Ix Dw → ℤ} (hex : ex none = 0) {f : Rul Xo c}
    (hf : f ∈ GlobalTheory.AllWt.secZ Xo c ex)
    (hv : ∀ i, (Φ.C i).Y.vanishOn ((Φ.C i).LEx ex) ((Φ.C i).val f) (Φ.C i).Ybd) :
    ∃ b ∈ IsLocalRing.maximalIdeal A, evR Xo c f z = algebraMap A k b := by
  have hφ : (algebraMap A k).comp (algebraMap c.F A) = algebraMap c.F k := (IsScalarTower.algebraMap_eq _ _ _).symm
  obtain ⟨gk, hgk⟩ := hbc.at gA (algebraMap A k) (x' := (spMap (algebraMap A k) ≫ xA) ≫ genι Z) (Category.assoc _ _ _)
  have hTz : Comparison₂ z gk := ⟨hφ, by rw [Model.j, ← Category.assoc, hz], fun τ i => by rw [hgk]; exact hu τ i⟩
  have hstr : (spMap (algebraMap A k) ≫ xA) ≫ genStr Z = spMap ((algebraMap A k).comp (algebraMap c.F A)) := by
    rw [Category.assoc, hxA, sp_comp]
  obtain ⟨⟨i, p⟩, ⟨hp, hc⟩, -⟩ := Φ.lifts k _ _ hstr gk
  obtain ⟨w⟩ := wit_of_carries (hz.trans hp.symm) hTz hc
  exact exists_mem_of_wit hbc xA hxA gA z gk (Category.assoc _ _ _) hφ hgk hTz p hp w hbd hex hf (hv i)

theorem mem_of_dominates {V K A k : Type} [CommRing V] [IsDomain V] [ValuationRing V] [Field K] [Algebra V K]
    [IsFractionRing V K] [CommRing A] [IsLocalRing A] [Field k] [Algebra A k]
    (hinj : Function.Injective (algebraMap A k)) (j : K →+* k) (i : V →+* A) [IsLocalHom i]
    (h : (algebraMap A k).comp i = j.comp (algebraMap V K)) {w : K} {b : A} (hb : b ∈ IsLocalRing.maximalIdeal A)
    (hw : j w = algebraMap A k b) : ∃ v ∈ IsLocalRing.maximalIdeal V, w = algebraMap V K v := by
  have hc : ∀ a, algebraMap A k (i a) = j (algebraMap V K a) := fun a => DFunLike.congr_fun h a
  rcases ValuationRing.isInteger_or_isInteger V w with ⟨a, ha⟩ | ⟨a, ha⟩
  · have e : i a = b := hinj (by rw [hc, ha, hw])
    exact ⟨a, fun hu => hb (e ▸ hu.map i), ha.symm⟩
  · by_cases h0 : w = 0
    · exact ⟨0, Ideal.zero_mem _, by simp [h0]⟩
    · exfalso
      have e : i a * b = 1 := hinj (by
        rw [map_mul, hc, ha, ← hw, ← map_mul, inv_mul_cancel₀ h0, map_one, map_one])
      exact hb (IsUnit.of_mul_eq_one _ (by rwa [mul_comm] at e))

theorem mem_of_boundary_extension_valuation (hbc : FrameBC Z) {σ : c.F →+* ℂ} {N : ℕ} {U : Formalism.L2.PjFree.Unf Xo c σ N} (Φ : FlagTor Z e U)
    {V K A k : Type} [CommRing V] [IsDomain V] [ValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K]
    [Algebra c.F K] [CommRing A] [IsDomain A] [ValuationRing A] [Field k] [IsAlgClosed k] [Algebra A k]
    [IsFractionRing A k] [Algebra K k] [Algebra c.F A] [Algebra c.F k] [IsScalarTower c.F A k] [IsScalarTower c.F K k]
    (i : V →+* A) [IsLocalHom i] (hi : (algebraMap A k).comp i = (algebraMap K k).comp (algebraMap V K))
    (φ : c.F →+* V) (hiφ : i.comp φ = algebraMap c.F A) (y : FrPt Xo c K) {ex : Ix Dw → ℤ} {f : Rul Xo c}
    (hB : BdExt Z φ y) (hex : ex none = 0) (hf : f ∈ GlobalTheory.AllWt.secZ Xo c ex)
    (hv : ∀ i, (Φ.C i).Y.vanishOn ((Φ.C i).LEx ex) ((Φ.C i).val f) (Φ.C i).Ybd) :
    ∃ v ∈ IsLocalRing.maximalIdeal V, evR Xo c f y = algebraMap V K v := by
  obtain ⟨χ, g, hχ, hpt, hw, hbd⟩ := hB
  obtain ⟨z, hzm⟩ := exists_frMap (IsScalarTower.toAlgHom c.F K k) y
  obtain ⟨gA, hgA⟩ : ∃ gA : EigFrame Z (algebraMap c.F A) ((spMap i ≫ χ) ≫ genι Z), ∀ τ j,
      gA.v τ j = spMap (dualMap i) ≫ g.v τ j := hiφ ▸ hbc.at g i (x' := (spMap i ≫ χ) ≫ genι Z) (Category.assoc _ _ _)
  have hspm : spMap (algebraMap A k) ≫ spMap i = spMap (algebraMap K k) ≫ spMap (algebraMap V K) := by
    rw [sp_comp, sp_comp, hi]
  have hcoe : (IsScalarTower.toAlgHom c.F K k).toRingHom = algebraMap K k := RingHom.ext fun _ => rfl
  have hptz : GlobalTheory.AllWt.ptF z = spMap (algebraMap K k) ≫ GlobalTheory.AllWt.ptF y := by
    have h0 := ptF_map (φ := IsScalarTower.toAlgHom c.F K k) hzm.1
    rwa [hcoe] at h0
  obtain ⟨b, hb, hbv⟩ := exists_mem_maximalIdeal_evR (A := A) (k := k) hbc Φ (spMap i ≫ χ)
    (by rw [Category.assoc, hχ, sp_comp, hiφ]) gA z
    (by rw [hptz, Category.assoc, hpt, ← Category.assoc, ← hspm, Category.assoc])
    (fun τ j => by
      obtain ⟨w, w1, w2, w3⟩ := hw τ j
      have h1 : TanRel Z (GlobalTheory.AllWt.ptF y) (y.u τ j) (spMap (dualMap (algebraMap V K)) ≫ g.v τ j) := ⟨w, w1, w2, w3⟩
      have h2 := h1.map (algebraMap K k)
      have h3 : spMap (dualMap (algebraMap K k)) ≫ spMap (dualMap (algebraMap V K)) ≫ g.v τ j =
          spMap (dualMap (algebraMap A k)) ≫ gA.v τ j := by
        rw [hgA, ← Category.assoc (spMap (dualMap (algebraMap K k))), ← Category.assoc (spMap (dualMap (algebraMap A k))),
          dual_comp, dual_comp, hi]
      rw [hptz, show z.u τ j = _ from hzm.2.1 τ j, ← h3]
      exact h2)
    (by
      have h1 : (spMap i) (IsLocalRing.closedPoint A) = IsLocalRing.closedPoint V :=
        IsLocalRing.comap_closedPoint i
      have h2 : (spMap i ≫ χ) (IsLocalRing.closedPoint A) = χ ((spMap i) (IsLocalRing.closedPoint A)) := rfl
      rw [h2, h1]; exact hbd)
    hex hf hv
  have hj := evR_frMap hf.1 hzm
  exact mem_of_dominates (IsFractionRing.injective A k) (algebraMap K k) i hi hb (hj.symm.trans hbv)

theorem mem_of_bdExt (hbc : FrameBC Z) {σ : c.F →+* ℂ} {N : ℕ} {U : Formalism.L2.PjFree.Unf Xo c σ N} (Φ : FlagTor Z e U)
    {V K : Type} [CommRing V] [IsDomain V] [ValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K]
    [Algebra c.F K] (φ : c.F →+* V) (y : FrPt Xo c K) {ex : Ix Dw → ℤ} {f : Rul Xo c}
    (hφ : (algebraMap V K).comp φ = algebraMap c.F K) (hB : BdExt Z φ y) (hex : ex none = 0)
    (hf : f ∈ GlobalTheory.AllWt.secZ Xo c ex)
    (hv : ∀ i, (Φ.C i).Y.vanishOn ((Φ.C i).LEx ex) ((Φ.C i).val f) (Φ.C i).Ybd) :
    ∃ v ∈ IsLocalRing.maximalIdeal V, evR Xo c f y = algebraMap V K v := by
  let ι₁ : V →+* AlgebraicClosure K := (algebraMap K (AlgebraicClosure K)).comp (algebraMap V K)
  obtain ⟨A, hA, hloc⟩ := IsLocalRing.exists_factor_valuationRing ι₁
  let i : V →+* A := ι₁.codRestrict A.toSubring hA
  haveI : IsLocalHom i := hloc
  have hi : (algebraMap A (AlgebraicClosure K)).comp i = ι₁ := rfl
  letI : Algebra c.F A := (i.comp φ).toAlgebra
  haveI : IsScalarTower c.F A (AlgebraicClosure K) := IsScalarTower.of_algebraMap_eq' (by
    change algebraMap c.F (AlgebraicClosure K) = (algebraMap A (AlgebraicClosure K)).comp (i.comp φ)
    rw [← RingHom.comp_assoc, hi, RingHom.comp_assoc, hφ]
    exact IsScalarTower.algebraMap_eq _ _ _)
  exact mem_of_boundary_extension_valuation hbc Φ i hi φ rfl y hB hex hf hv

end Core

end GlobalTheory.CuspFrom.Vanish

namespace GlobalTheory.CuspFrom

theorem evR_mem_maximalIdeal_of_vanishOn : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β), (∀ (R R' : Type) [CommRing R] [IsLocalRing R] [CommRing R'] [IsLocalRing R'] (φ : c.F →+* R) (x : Sp R ⟶ Z.X) (f : EigFrame Z φ x) (ψ : R →+* R'), ∃ g : EigFrame Z (ψ.comp φ) (spMap ψ ≫ x), ∀ τ i, g.v τ i = spMap (dualMap ψ) ≫ f.v τ i) → ∀ (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r) (Φ : FlagTor Z e U) (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] [Algebra c.F K] (φ : c.F →+* V) (y : FrPt Xo c K) (ex : Ix Dw → ℤ) (f : Rul Xo c), (algebraMap V K).comp φ = algebraMap c.F K → BdExt Z φ y → ex none = 0 → f ∈ GlobalTheory.AllWt.secZ Xo c ex → (∀ k, (Φ.C k).Y.vanishOn ((Φ.C k).LEx ex) ((Φ.C k).val f) (Φ.C k).Ybd) → ∃ v ∈ IsLocalRing.maximalIdeal V, evR Xo c f y = algebraMap V K v :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ Z hbc _ _ _ _ _ _ Φ _ _ _ _ _ _ _ _ _ φ y ex f hφ hB hex hf hv =>
    Vanish.mem_of_bdExt (Z := Z) hbc Φ φ y hφ hB hex hf hv

end GlobalTheory.CuspFrom
