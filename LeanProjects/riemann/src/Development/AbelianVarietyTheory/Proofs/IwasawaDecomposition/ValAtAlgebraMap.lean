import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions

namespace GlobalTheory.TrueGeo.OfModel

section Values

variable {K : Type} [Field K] {Z : Scheme.{0}} [IsIntegral Z] (y : Sp K ⟶ Z)

theorem valAt_algebraMap (a : Z.presheaf.stalk (below y)) :
    valAt y (algebraMap _ Z.functionField a) = (Scheme.stalkClosedPointTo y).hom a := by
  have h : RegAt (below y) (algebraMap _ Z.functionField a) := ⟨a, rfl⟩
  rw [valAt, dif_pos h]
  exact congrArg _ (IsFractionRing.injective (Z.presheaf.stalk (below y)) Z.functionField h.choose_spec)

theorem valAt_mul {f g : Z.functionField} (hf : RegAt (below y) f) (hg : RegAt (below y) g) :
    valAt y (f * g) = valAt y f * valAt y g := by
  obtain ⟨a, rfl⟩ := hf
  obtain ⟨b, rfl⟩ := hg
  rw [← map_mul, valAt_algebraMap, valAt_algebraMap, valAt_algebraMap, map_mul]

theorem valAt_fnOf {U : Z.Opens} (hU : below y ∈ U) (h : ⊤ ≤ y ⁻¹ᵁ U) (a : Γ(Z, U)) :
    valAt y (fnOf U (gen_mem hU) a) =
      (y.appLE U ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of K)).hom).hom a := by
  have e : Z.presheaf.germ U _ hU ≫ Scheme.stalkClosedPointTo (R := CommRingCat.of K) y =
      y.appLE U ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of K)).hom := by
    rw [Scheme.germ_stalkClosedPointTo]
    simp [Iso.trans_hom, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_map_assoc]
  rw [← algebraMap_germ hU, valAt_algebraMap, ← e]
  rfl

end Values

theorem ext_unique {K R : Type} [Field K] [CommRing R] (O : ValuationSubring K) {X : Scheme.{0}} (p : X ⟶ Sp R)
    [IsSeparated p] {b b' : Sp O ⟶ X} (h : spMap O.subtype ≫ b = spMap O.subtype ≫ b') : b = b' := by
  have : IsDominant (spMap O.subtype) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2
    (((RingHom.injective_iff_ker_eq_bot _).1 Subtype.val_injective).le.trans bot_le)⟩
  refine ext_of_isDominant_of_isSeparated p (ext_of_isDominant (spMap O.subtype) ?_) _ h
  rw [← Category.assoc, h, Category.assoc]

theorem eval_pull {K O : Type} [CommRing K] [CommRing O] (φ : O →+* K) {X Z : Scheme.{0}} (j : Z ⟶ X)
    (y : Sp K ⟶ Z) (yt : Sp O ⟶ X) (e : spMap φ ≫ yt = y ≫ j) {U : X.Opens} {W : Z.Opens}
    (hW : W ≤ j ⁻¹ᵁ U) (h : ⊤ ≤ y ⁻¹ᵁ W) (ht : ⊤ ≤ yt ⁻¹ᵁ U) (a : Γ(X, U)) :
    (y.appLE W ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of K)).hom).hom ((j.appLE U W hW).hom a) =
      φ ((yt.appLE U ⊤ ht ≫ (Scheme.ΓSpecIso (CommRingCat.of O)).hom).hom a) := by
  have e1 : j.appLE U W hW ≫ y.appLE W ⊤ h = yt.appLE U ⊤ ht ≫ (spMap φ).appTop := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE]
    refine Eq.trans ?_ (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).symm
    simp only [e]
  have e2 := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ)
  have e3 : j.appLE U W hW ≫ y.appLE W ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of K)).hom =
      (yt.appLE U ⊤ ht ≫ (Scheme.ΓSpecIso (CommRingCat.of O)).hom) ≫ CommRingCat.ofHom φ := by
    rw [← Category.assoc, e1, Category.assoc, e2, Category.assoc]
  exact congrArg (fun ψ => ψ.hom a) e3

variable {F : Type} [Field F] [NumberField F]

theorem w_unit {v : HeightOneSpectrum (𝓞 F)} (e : Ext v) {x : e.O} (hx : IsUnit x) : e.w x = 1 := by
  obtain ⟨u, rfl⟩ := hx
  have h₁ := (e.mem_O _).1 (u : e.O).2
  have h₂ := (e.mem_O _).1 ((u⁻¹ : e.Oˣ) : e.O).2
  have h₃ : e.w ((u : e.O) : AlgebraicClosure F) * e.w (((u⁻¹ : e.Oˣ) : e.O) : AlgebraicClosure F) = 1 := by
    rw [← map_mul, ← MulMemClass.coe_mul, Units.mul_inv]
    simp
  have h₄ := e.w.nonneg ((u : e.O) : AlgebraicClosure F)
  nlinarith

variable {Y : Var F} (M : TrueGeo.Model Y) (B : LB M.X)

theorem le_chart {v : HeightOneSpectrum (𝓞 F)} (e : Ext v) (y : AlgPt Y) (yt : Sp e.O ⟶ M.X)
    (h : spMap e.O.subtype ≫ yt = y.1 ≫ M.j) {i : (B.pull M.j).ι} (hi : ⊤ ≤ yt ⁻¹ᵁ B.U (i PUnit.unit)) :
    ⊤ ≤ y.1 ⁻¹ᵁ (B.pull M.j).U i := fun x _ => Set.mem_iInter.2 fun _ => by
  change (y.1 ≫ M.j) x ∈ B.U (i PUnit.unit)
  rw [← h]
  exact hi (x := spMap e.O.subtype x) trivial

theorem w_indep {Δ : Y.Dv} {r : (B.pull M.j).ι → Y.Fnˣ} (hr : Presents Δ (B.pull M.j) r)
    {v : HeightOneSpectrum (𝓞 F)} (e : Ext v) (y : AlgPt Y) (yt : Sp e.O ⟶ M.X)
    (h : spMap e.O.subtype ≫ yt = y.1 ≫ M.j) {i i' : (B.pull M.j).ι} (hi : ⊤ ≤ yt ⁻¹ᵁ B.U (i PUnit.unit))
    (hi' : ⊤ ≤ yt ⁻¹ᵁ B.U (i' PUnit.unit)) :
    e.w (valAt y.1 (((eqn Δ (below y.1))⁻¹ * r i : Y.Fnˣ) : Y.Fn)) =
      e.w (valAt y.1 (((eqn Δ (below y.1))⁻¹ * r i' : Y.Fnˣ) : Y.Fn)) := by
  have h₁ : ⊤ ≤ y.1 ⁻¹ᵁ ((B.pull M.j).U i ⊓ (B.pull M.j).U i') :=
    fun x hx => ⟨le_chart M B e y yt h hi hx, le_chart M B e y yt h hi' hx⟩
  have h₂ : below y.1 ∈ (B.pull M.j).U i ⊓ (B.pull M.j).U i' := h₁ trivial
  have h₃ : ⊤ ≤ yt ⁻¹ᵁ (B.U (i PUnit.unit) ⊓ B.U (i' PUnit.unit)) := fun x hx => ⟨hi hx, hi' hx⟩
  have l : (B.pull M.j).U i ⊓ (B.pull M.j).U i' ≤ M.j ⁻¹ᵁ (B.U (i PUnit.unit) ⊓ B.U (i' PUnit.unit)) :=
    fun x hx => ⟨Set.mem_iInter.1 hx.1 PUnit.unit, Set.mem_iInter.1 hx.2 PUnit.unit⟩
  have hg : ((B.pull M.j).g i i').val =
      (M.j.appLE _ _ l).hom (B.g (i PUnit.unit) (i' PUnit.unit)).val := by
    have : (B.pull M.j).g i i' = res l (pullU M.j _ (B.g (i PUnit.unit) (i' PUnit.unit))) := by
      change ∏ _k : PUnit, _ = _
      exact (Fintype.prod_unique _).trans (zpow_one _)
    rw [this]
    rfl
  have hu : RegAt (below y.1) (((eqn Δ (below y.1))⁻¹ * r i' : Y.Fnˣ) : Y.Fn) := by
    have := ((Δ.exists_isEqn (below y.1)).choose_spec.iff_unitAt.1 (hr.isEqn i' _ h₂.2)).regAt
    rwa [div_eq_inv_mul, ← Units.val_inv_eq_inv_val, ← Units.val_mul] at this
  have e₁ : (((eqn Δ (below y.1))⁻¹ * r i : Y.Fnˣ) : Y.Fn) =
      fnOf _ (gen_mem h₂) ((B.pull M.j).g i i').val * (((eqn Δ (below y.1))⁻¹ * r i' : Y.Fnˣ) : Y.Fn) := by
    rw [Units.val_mul, Units.val_mul, hr.isRatSec i i' (gen_mem h₂), mul_left_comm]
  rw [e₁, valAt_mul _ (regAt_fnOf h₂ _ _) hu, valAt_fnOf _ h₂ h₁, hg, eval_pull _ _ _ yt h l h₁ h₃, map_mul]
  exact (congrArg (· * _) (w_unit e ((Units.isUnit _).map _))).trans (one_mul _)

theorem pn_mPow_one (C : CxSt F) (σ : F →+* ℂ) {Δ : Y.Dv} {L : LB Y.X} {r : L.ι → Y.Fnˣ} (hr : Presents Δ L r)
    (φ : Weight Y.str σ L) (y : Pts Y σ) {i : L.ι} (hi : under y ∈ L.U i) {f : Y.Fn}
    (hf : (1 • Δ).RegularAt (under y) f) :
    C.pn Y σ _ (C.mPow Y σ Δ 1 (C.ofWeight Y σ Δ L r hr φ)) (C.cx Y σ f) y =
      ‖ratVal (f * (r i : Y.Fn)) y‖ ^ 2 * Real.exp (-φ.φ i y) := by
  have h₁ := hr.isEqn i _ hi
  have h₂ := CartierDiv.isEqn_iff_generatesAt_inv.1 h₁
  have h₃ : (1 • Δ).RegularAt (under y) (r i : Y.Fn)⁻¹ := by rw [one_nsmul]; exact h₂.regularAt
  have h₄ : RegAt (under y) (f * (r i : Y.Fn)) := h₁.regularAt_iff.1 (by rwa [one_nsmul] at hf)
  have h₅ := C.pn_mul Y σ _ (C.mPow Y σ Δ 1 (C.ofWeight Y σ Δ L r hr φ)) _ _ y h₄ h₃
  have h₆ := C.pn_mPow Y σ Δ 1 (C.ofWeight Y σ Δ L r hr φ) _ y h₂
  have h₇ := C.pn_ofWeight Y σ Δ L r hr φ _ y i hi h₂.regularAt
  have h₈ : ratVal (1 : Y.Fn) y = 1 := by
    have e := ratVal_fnOf (y := y) CxPts.mem_ptsIn_top trivial 1
    rwa [map_one, CxPts.ev_one CxPts.mem_ptsIn_top] at e
  rw [mul_inv_cancel_right₀ (r i).ne_zero] at h₅
  rw [pow_one, pow_one] at h₆
  rw [inv_mul_cancel₀ (r i).ne_zero, h₈] at h₇
  rw [h₅, h₆, h₇]
  simp

def ptMap (σ : F →+* ℂ) (y : Pts Y σ) : CxPts M.p (σ.comp (algebraMap (𝓞 F) F)) :=
  ⟨y.1 ≫ M.j, by rw [Category.assoc, M.pb.w, ← Category.assoc, y.2, ← Spec.map_comp]; rfl⟩

theorem exists_induced : ∀ (F : Type) [Field F] [NumberField F] (C : CxSt F) (Y : Var F) (M : TrueGeo.Model Y)
    (L : HermLB M.p) (Δ : Y.Dv) (r : (L.B.pull M.j).ι → Y.Fnˣ), Presents Δ (L.B.pull M.j) r →
    ∃ A : Adl C Y, A.D = Δ ∧ A.n = 1 ∧ A.ci = 0 ∧ A.Induced M L 1 0 := by
  intro F _ _ C Y M L Δ r hr
  classical
  have : IsSeparated M.p := by
    obtain ⟨N, c, hc, h⟩ := M.ar.isProjOver
    have := isProper_str (𝓞 F) N
    rw [← h]
    infer_instance
  let φ (σ : F →+* ℂ) : Weight Y.str σ (L.B.pull M.j) :=
    (L.φ (σ.comp (algebraMap (𝓞 F) F))).linComb _ _ (fun _ => ptMap M σ) fun _ _ => rfl
  let P (v : HeightOneSpectrum (𝓞 F)) (e : Ext v) (y : AlgPt Y) (i : (L.B.pull M.j).ι) : Prop :=
    ∃ yt : Sp e.O ⟶ M.X, spMap e.O.subtype ≫ yt = y.1 ≫ M.j ∧ ⊤ ≤ yt ⁻¹ᵁ L.B.U (i PUnit.unit)
  refine ⟨⟨Δ, 1, fun σ => C.ofWeight Y σ Δ _ r hr (φ σ), 0, fun v e y => if h : ∃ i, P v e y i then
    Real.log (e.w (valAt y.1 (((eqn Δ (below y.1))⁻¹ * r h.choose : Y.Fnˣ) : Y.Fn))) else 0⟩,
    rfl, rfl, rfl, by simp, r, ?_, ?_, ?_⟩
  · change Presents (1 • Δ) _ _
    rwa [one_nsmul]
  · intro σ y y' i f hy hi hf
    obtain rfl : y' = ptMap M σ y := Subtype.ext hy
    have e : (φ σ).φ i y = (L.φ _).φ (i PUnit.unit) (ptMap M σ y) :=
      (Fintype.sum_unique fun a : PUnit.{1} =>
        ((1 : ℤ) : ℝ) * (L.φ _).φ (i a) (ptMap M σ y)).trans (by simp)
    rw [← e, ← pn_mPow_one C σ hr (φ σ) y hi hf]
    simp only [Pi.zero_apply, mul_zero, neg_zero, Real.exp_zero, one_mul]
    rfl
  · intro v e y yt i h hi
    have hP : ∃ i, P v e y i := ⟨i, yt, h, hi⟩
    obtain ⟨yt', h', hi'⟩ := hP.choose_spec
    obtain rfl : yt = yt' := ext_unique e.O M.p (h.trans h'.symm)
    simp only [dif_pos hP, PNat.val_ofNat, Nat.cast_one, one_mul, pow_one, Pi.zero_apply, sub_zero]
    rw [w_indep M L.B hr e y yt h hi' hi]

end GlobalTheory.TrueGeo.OfModel
