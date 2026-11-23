import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValAtAlgebraMap

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions

namespace GlobalTheory.TrueGeo.InducedPow

section Charts

variable {X Z : Scheme.{0}} (B : LB X) (j : Z ⟶ X) (m : ℕ)

theorem mem_chart {i : ((lbPow B m).pull j).ι} {x : Z} (hx : x ∈ ((lbPow B m).pull j).U i) :
    x ∈ (B.pull j).U fun _ => i PUnit.unit PUnit.unit :=
  Set.mem_iInter.2 fun _ => Set.mem_iInter.1 (Set.mem_iInter.1 hx PUnit.unit) PUnit.unit

theorem pull_g (i i' : (B.pull j).ι)
    (l : (B.pull j).U i ⊓ (B.pull j).U i' ≤ j ⁻¹ᵁ (B.U (i PUnit.unit) ⊓ B.U (i' PUnit.unit))) :
    ((B.pull j).g i i').val = (j.appLE _ _ l).hom (B.g (i PUnit.unit) (i' PUnit.unit)).val := by
  have : (B.pull j).g i i' = res l (pullU j _ (B.g (i PUnit.unit) (i' PUnit.unit))) := by
    change ∏ _k : PUnit, _ = _
    exact (Fintype.prod_unique _).trans (zpow_one _)
  rw [this]
  rfl

theorem pow_g (i i' : (lbPow B m).ι)
    (l : (lbPow B m).U i ⊓ (lbPow B m).U i' ≤ B.U (i PUnit.unit) ⊓ B.U (i' PUnit.unit)) :
    ((lbPow B m).g i i').val =
      (X.presheaf.map (homOfLE l).op).hom (B.g (i PUnit.unit) (i' PUnit.unit)).val ^ m := by
  have : (lbPow B m).g i i' = res l (B.g (i PUnit.unit) (i' PUnit.unit)) ^ m := by
    change ∏ _k : PUnit, _ = _
    refine (Fintype.prod_unique _).trans ((zpow_natCast _ _).trans ?_)
    rfl
  rw [this, Units.val_pow_eq_pow_val]
  rfl

variable [IsIntegral Z]

theorem presents_pow (hB : B.IsLB) {Δ : CartierDiv Z} {r : (B.pull j).ι → Z.functionFieldˣ}
    (hr : Presents Δ (B.pull j) r) :
    Presents (m • Δ) ((lbPow B m).pull j) fun i => r (fun _ => i PUnit.unit PUnit.unit) ^ m := by
  refine ⟨LB.isLB_pull (isLB_lbPow hB m) j, fun i i' h => ?_,
    fun i x hx => (hr.isEqn _ x (mem_chart B j m hx)).nsmul m⟩
  have l₀ : ((lbPow B m).pull j).U i ⊓ ((lbPow B m).pull j).U i' ≤
      (B.pull j).U (fun _ => i PUnit.unit PUnit.unit) ⊓ (B.pull j).U fun _ => i' PUnit.unit PUnit.unit :=
    fun _ hx => ⟨mem_chart B j m hx.1, mem_chart B j m hx.2⟩
  have l₁ : ((lbPow B m).pull j).U i ⊓ ((lbPow B m).pull j).U i' ≤
      j ⁻¹ᵁ ((lbPow B m).U (i PUnit.unit) ⊓ (lbPow B m).U (i' PUnit.unit)) :=
    fun x hx => ⟨Set.mem_iInter.1 hx.1 PUnit.unit, Set.mem_iInter.1 hx.2 PUnit.unit⟩
  have l₂ : (lbPow B m).U (i PUnit.unit) ⊓ (lbPow B m).U (i' PUnit.unit) ≤
      B.U (i PUnit.unit PUnit.unit) ⊓ B.U (i' PUnit.unit PUnit.unit) :=
    fun x hx => ⟨Set.mem_iInter.1 hx.1 PUnit.unit, Set.mem_iInter.1 hx.2 PUnit.unit⟩
  have l₃ : (B.pull j).U (fun _ => i PUnit.unit PUnit.unit) ⊓ (B.pull j).U (fun _ => i' PUnit.unit PUnit.unit) ≤
      j ⁻¹ᵁ (B.U (i PUnit.unit PUnit.unit) ⊓ B.U (i' PUnit.unit PUnit.unit)) :=
    fun x hx => ⟨Set.mem_iInter.1 hx.1 PUnit.unit, Set.mem_iInter.1 hx.2 PUnit.unit⟩
  rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, hr.isRatSec _ _ (l₀ h), mul_pow,
    pull_g _ j i i' l₁, pow_g B m _ _ l₂, map_pow, map_pow, pull_g B j _ _ l₃, ← fnOf_resG l₀ h]
  congr 3
  have e : j.appLE _ _ l₃ ≫ Z.presheaf.map (homOfLE l₀).op =
      X.presheaf.map (homOfLE l₂).op ≫ j.appLE _ _ l₁ := by
    rw [Scheme.Hom.appLE_map, Scheme.Hom.map_appLE]
  exact congrArg (fun ψ => ψ.hom (B.g (i PUnit.unit PUnit.unit) (i' PUnit.unit PUnit.unit)).val) e

end Charts

theorem unitAt_pow {Z : Scheme.{0}} [IsIntegral Z] {x : Z} {f : Z.functionField} (h : UnitAt x f) (n : ℕ) :
    UnitAt x (f ^ n) := by
  obtain ⟨a, ha, rfl⟩ := h
  exact ⟨a ^ n, ha.pow n, map_pow _ _ _⟩

theorem valAt_pow {K : Type} [Field K] {Z : Scheme.{0}} [IsIntegral Z] (y : Sp K ⟶ Z) {f : Z.functionField}
    (h : RegAt (below y) f) (n : ℕ) : valAt y (f ^ n) = valAt y f ^ n := by
  obtain ⟨a, rfl⟩ := h
  rw [← map_pow, OfModel.valAt_algebraMap, OfModel.valAt_algebraMap, map_pow]

theorem ratVal_pow {k : Type} [CommRing k] {σ : k →+* ℂ} {Z : Scheme.{0}} [IsIntegral Z] {q : Z ⟶ Sp k}
    (y : CxPts q σ) {f : Z.functionField} (h : UnitAt (under y) f) (n : ℕ) :
    ratVal (f ^ n) y = ratVal f y ^ n := by
  induction n with
  | zero =>
    have e := ratVal_fnOf (y := y) CxPts.mem_ptsIn_top trivial 1
    rwa [map_one, CxPts.ev_one CxPts.mem_ptsIn_top, ← pow_zero f, ← pow_zero (ratVal f y)] at e
  | succ n ih => rw [pow_succ, pow_succ, ratVal_mul (unitAt_pow h n).regAt h.regAt, ih]

theorem induced_pow : ∀ (F : Type) [Field F] [NumberField F] (C : CxSt F) (Y : Var F) (A : Adl C Y)
    (M : TrueGeo.Model Y) (L : HermLB M.p) (k m : ℕ+) (cf : HeightOneSpectrum (𝓞 F) → ℝ),
    A.Induced M L k cf → A.Induced M (L.pow m) (k * m) cf := by
  rintro F _ _ C Y A M L k m cf ⟨hfin, r, hr, hinf, hv⟩
  have hD : ((k * m : ℕ+) : ℕ) • A.D = (m : ℕ) • (k : ℕ) • A.D := by rw [PNat.mul_coe, mul_nsmul]
  have hr' := presents_pow L.B M.j m L.isLB hr
  refine ⟨hfin, fun i => r (fun _ => i PUnit.unit PUnit.unit) ^ (m : ℕ), ?_, ?_, ?_⟩
  · rw [hD]; exact hr'
  · intro σ y y' i f hy hi hf
    have hi' := mem_chart L.B M.j m hi
    obtain ⟨g, hg⟩ := A.D.exists_isEqn (under y)
    have hgen := CartierDiv.isEqn_iff_generatesAt_inv.1 hg
    have hgenk (n : ℕ) : (n • A.D).GeneratesAt (under y) ((g : Y.Fn)⁻¹ ^ n) := by
      have := CartierDiv.isEqn_iff_generatesAt_inv.1 (hg.nsmul n)
      rwa [Units.val_pow_eq_pow_val, ← inv_pow] at this
    have h₁ := hinf σ y y' (fun _ => i PUnit.unit PUnit.unit) _ hy hi' (hgenk k).regularAt
    rw [C.pn_mPow Y σ A.D k (A.m σ) _ y hgen] at h₁
    have hu := (hr.isEqn _ _ hi').generatesAt_iff.1 (hgenk k)
    have ha : RegAt (under y) (f * (g : Y.Fn) ^ ((k * m : ℕ+) : ℕ)) := by
      have := (hg.nsmul _).regularAt_iff.1 hf
      rwa [Units.val_pow_eq_pow_val] at this
    have h₂ := C.pn_mul Y σ _ (C.mPow Y σ A.D ((k * m : ℕ+) : ℕ) (A.m σ)) _ _ y ha (hgenk _).regularAt
    rw [C.pn_mPow Y σ A.D _ (A.m σ) _ y hgen, mul_assoc, ← mul_pow, mul_inv_cancel₀ g.ne_zero, one_pow,
      mul_one] at h₂
    have h₃ : f * ((r (fun _ => i PUnit.unit PUnit.unit) ^ (m : ℕ) : Y.Fnˣ) : Y.Fn) =
        f * (g : Y.Fn) ^ ((k * m : ℕ+) : ℕ) *
          ((g : Y.Fn)⁻¹ ^ (k : ℕ) * (r (fun _ => i PUnit.unit PUnit.unit) : Y.Fn)) ^ (m : ℕ) := by
      rw [Units.val_pow_eq_pow_val, mul_pow, ← pow_mul, PNat.mul_coe, mul_assoc, ← mul_assoc (_ ^ (_ * _)),
        ← mul_pow, mul_inv_cancel₀ g.ne_zero, one_pow, one_mul]
    have h₄ : ((L.pow m).φ _).φ (i PUnit.unit) y' =
        ((m : ℕ) : ℝ) * (L.φ _).φ (i PUnit.unit PUnit.unit) y' :=
      ((L.φ _).zpow_φ _ _ y').trans (by simp)
    rw [h₂, h₃, ratVal_mul ha (unitAt_pow hu _).regAt, ratVal_pow y hu, h₄, norm_mul, norm_pow, mul_pow,
      ← pow_mul, mul_comm (m : ℕ) 2, pow_mul, ← mul_neg ((m : ℕ) : ℝ), Real.exp_nat_mul, mul_assoc (_ ^ 2), ← mul_pow, ← h₁,
      mul_pow, ← Real.exp_nat_mul, ← pow_mul, PNat.mul_coe, mul_left_comm]
    congr 3
    push_cast
    ring
  · intro v e y yt i h hi
    have hi' : ⊤ ≤ yt ⁻¹ᵁ L.B.U (i PUnit.unit PUnit.unit) := fun x hx => Set.mem_iInter.1 (hi hx) PUnit.unit
    have h₁ := hv v e y yt (fun _ => i PUnit.unit PUnit.unit) h hi'
    have h₂ : below y.1 ∈ (L.B.pull M.j).U fun _ => i PUnit.unit PUnit.unit :=
      OfModel.le_chart M L.B e y yt h (i := fun _ => i PUnit.unit PUnit.unit) hi' trivial
    have hu : RegAt (below y.1) (((eqn A.D (below y.1))⁻¹ ^ (k : ℕ) *
        r (fun _ => i PUnit.unit PUnit.unit) : Y.Fnˣ) : Y.Fn) := by
      have := (((A.D.exists_isEqn (below y.1)).choose_spec.nsmul k).iff_unitAt.1 (hr.isEqn _ _ h₂)).regAt
      rwa [div_eq_inv_mul, ← Units.val_inv_eq_inv_val, ← Units.val_mul, ← inv_pow] at this
    rw [PNat.mul_coe, pow_mul, ← mul_pow, Units.val_pow_eq_pow_val, valAt_pow _ hu, map_pow, Real.log_pow]
    push_cast at h₁ ⊢
    linear_combination ((m : ℕ) : ℝ) * h₁

end GlobalTheory.TrueGeo.InducedPow
