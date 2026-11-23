import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsSymm
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueUniformisingVectorVerticalTangentStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFibreCoordsStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.InvariantVectorFieldAbelianVarietyAlgebraicStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueSectionOfLocallyRegularStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

noncomputable section
namespace GlobalTheory.KS.VertReg

private theorem rmul_rmul' {X : Scheme.{0}} {U V W : X.Opens} (h : V ≤ U) (h' : W ≤ V) (f : Γ(X, U)) :
    resG X h' (resG X h f) = resG X (h'.trans h) f := by
  show (X.presheaf.map (homOfLE h).op ≫ X.presheaf.map (homOfLE h').op).hom f = _
  rw [← Functor.map_comp]
  rfl

private theorem exists_ringHom_eq_valAt'' {Y : Scheme.{0}} (x : Sp ℂ ⟶ Y) (U : Y.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) :
    ∃ φ : Γ(Y, U) →+* ℂ, ∀ f, valAt' x U f = φ f := by
  refine ⟨(Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom.comp (x.appLE U ⊤ h).hom, fun f => ?_⟩
  unfold valAt'
  rw [dif_pos h]
  rfl

private theorem valAt'_resG_of_le {Y : Scheme.{0}} (x : Sp ℂ ⟶ Y) {U V : Y.Opens} (hVU : V ≤ U) (h : ⊤ ≤ x ⁻¹ᵁ V)
    (f : Γ(Y, U)) : valAt' x V (resG Y hVU f) = valAt' x U f := by
  have h' : ⊤ ≤ x ⁻¹ᵁ U := fun _ ha => hVU (h ha)
  unfold valAt'
  rw [dif_pos h, dif_pos h']
  unfold valAt
  exact congrArg (fun s => (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom s)
    (congrArg (fun φ => CommRingCat.Hom.hom φ f) (Scheme.Hom.map_appLE x h (homOfLE hVU).op))

private theorem valAt'_app_eq_valAt'_comp_moduli {Y Z : Scheme.{0}} (x : Sp ℂ ⟶ Y) (φ : Y ⟶ Z) (U : Z.Opens) (f : Γ(Z, U)) :
    valAt' x (φ ⁻¹ᵁ U) ((φ.app U).hom f) = valAt' (x ≫ φ) U f := by
  unfold valAt'
  by_cases hh : ⊤ ≤ x ⁻¹ᵁ φ ⁻¹ᵁ U
  · have hh' : ⊤ ≤ (x ≫ φ) ⁻¹ᵁ U := hh
    rw [dif_pos hh, dif_pos hh']
    unfold valAt
    rw [Scheme.Hom.comp_appLE]
    rfl
  · have hh' : ¬ ⊤ ≤ (x ≫ φ) ⁻¹ᵁ U := hh
    rw [dif_neg hh, dif_neg hh']

private theorem valAt'_constFn' {Y : Scheme.{0}} (y : Sp ℂ ⟶ Y) (q : Y ⟶ Sp ℂ) (hq : y ≫ q = 𝟙 _) (U : Y.Opens)
    (h : ⊤ ≤ y ⁻¹ᵁ U) (c : ℂ) : valAt' y U (constFn q U c) = c := by
  unfold valAt' constFn
  rw [dif_pos h]
  unfold valAt
  have e2 := congrArg (fun φ => CommRingCat.Hom.hom φ ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom c))
    (Scheme.Hom.appLE_comp_appLE y q ⊤ U ⊤ (fun x _ => trivial) h)
  have key : ∀ (φ : Sp ℂ ⟶ Sp ℂ) (_ : φ = 𝟙 _) (e : ⊤ ≤ φ ⁻¹ᵁ ⊤),
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom ((φ.appLE ⊤ ⊤ e).hom
        ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom c)) = c := by
    rintro φ rfl e
    simp [Scheme.Hom.appLE]
    change (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom (((Sp ℂ).presheaf.map (𝟙 (Opposite.op ⊤))).hom
      ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom c)) = c
    rw [CategoryTheory.Functor.map_id]
    simp
  exact (congrArg (fun s => (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom s) e2).trans (key _ hq _)

private theorem top_le_preimage_basicOpen_of_valAt'_ne_zero {Y : Scheme.{0}} (y : Sp ℂ ⟶ Y) (U : Y.Opens) (h : ⊤ ≤ y ⁻¹ᵁ U) (g : Γ(Y, U))
    (hg : valAt' y U g ≠ 0) : ⊤ ≤ y ⁻¹ᵁ Y.basicOpen g := by
  unfold valAt' at hg
  rw [dif_pos h] at hg
  unfold valAt at hg
  have hu : IsUnit ((y.appLE U ⊤ h).hom g) := by
    have h1 := (isUnit_iff_ne_zero.2 hg).map (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom
    simpa using h1
  have h1 : (Sp ℂ).basicOpen ((y.appLE U ⊤ h).hom g) = ⊤ := Scheme.basicOpen_of_isUnit _ hu
  have h2 : (Sp ℂ).basicOpen ((y.appLE U ⊤ h).hom g) ≤ y ⁻¹ᵁ Y.basicOpen g := by
    rw [Scheme.preimage_basicOpen]
    exact (Scheme.basicOpen_res (Sp ℂ) ((y.app U).hom g) (homOfLE h).op).le.trans inf_le_right
  exact h1.ge.trans h2

private theorem top_le_preimage_preimage_inf {Y X : Scheme.{0}} (y : Sp ℂ ⟶ Y) (m : Y ⟶ X) {U V : X.Opens}
    (h1 : ⊤ ≤ y ⁻¹ᵁ m ⁻¹ᵁ U) (h2 : ⊤ ≤ y ⁻¹ᵁ m ⁻¹ᵁ V) : ⊤ ≤ y ⁻¹ᵁ m ⁻¹ᵁ (U ⊓ V) :=
  fun _ ha => ⟨h1 ha, h2 ha⟩

theorem exists_cramer {Y : Scheme.{0}} {n : ℕ} (O₁ O₂ : Y.Opens) (J : Matrix (Fin n) (Fin n) Γ(Y, O₁))
    (e : Fin n → Γ(Y, O₂)) (a : Fin n) :
    ∃ c : Γ(Y, Y.basicOpen J.det ⊓ O₂), ∀ y : Sp ℂ ⟶ Y, ⊤ ≤ y ⁻¹ᵁ (Y.basicOpen J.det ⊓ O₂) → ∀ w : Fin n → ℂ,
      (∀ b, valAt' y O₂ (e b) = ∑ i, w i * valAt' y O₁ (J i b)) → valAt' y _ c = w a := by
  classical
  have hb : Y.basicOpen J.det ⊓ O₂ ≤ O₁ := inf_le_left.trans (Y.basicOpen_le _)
  have hu : IsUnit (resG Y hb J.det) := by
    have h0 : IsUnit (resG Y (Y.basicOpen_le J.det) J.det) := Y.toRingedSpace.isUnit_res_basicOpen J.det
    have h1 := h0.map
      (resG Y (inf_le_left : Y.basicOpen J.det ⊓ O₂ ≤ Y.basicOpen J.det))
    rwa [rmul_rmul'] at h1
  let A : Matrix (Fin n) (Fin n) Γ(Y, Y.basicOpen J.det ⊓ O₂) := Matrix.transpose (J.map (resG Y hb))
  let v : Fin n → Γ(Y, Y.basicOpen J.det ⊓ O₂) := fun b => resG Y inf_le_right (e b)
  have hA : A.det = resG Y hb J.det := by
    rw [Matrix.det_transpose, RingHom.map_det]
    rfl
  refine ⟨↑hu.unit⁻¹ * (Matrix.mulVec A.adjugate v) a, ?_⟩
  intro y hy w hw
  obtain ⟨φ, hφ⟩ := exists_ringHom_eq_valAt'' y _ hy
  have hJ : ∀ i b, valAt' y O₁ (J i b) = φ (A b i) := fun i b => by
    rw [← hφ]
    exact (valAt'_resG_of_le y hb hy (J i b)).symm
  have he : ∀ b, valAt' y O₂ (e b) = φ (v b) := fun b => by
    rw [← hφ]
    exact (valAt'_resG_of_le y inf_le_right hy (e b)).symm
  let M := A.map φ
  have hM : Matrix.mulVec M w = fun b => φ (v b) := by
    funext b
    rw [← he, hw b]
    simp only [M, Matrix.mulVec, dotProduct, Matrix.map_apply, hJ]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hdet : φ ↑hu.unit = M.det := by
    rw [IsUnit.unit_spec, ← hA, RingHom.map_det]
    rfl
  have hne : M.det ≠ 0 := by
    rw [← hdet]
    exact (hu.unit.isUnit.map φ).ne_zero
  have hadj : φ ((Matrix.mulVec A.adjugate v) a) = (Matrix.mulVec M.adjugate (Matrix.mulVec M w)) a := by
    rw [RingHom.map_mulVec]
    have hm : A.adjugate.map φ = M.adjugate := RingHom.map_adjugate φ A
    rw [hm, hM]
    rfl
  rw [hφ, map_mul, map_units_inv, hadj, hdet, Matrix.mulVec_mulVec, Matrix.adjugate_mul,
    Matrix.smul_mulVec, Matrix.one_mulVec, Pi.smul_apply, smul_eq_mul,
    inv_mul_cancel_left₀ hne]

variable {R : Type} [CommRing R] {Y X : Scheme.{0}} {q : Y ⟶ Sp ℂ} {p : X ⟶ Sp R} {m : Y ⟶ X}
  {W₀ : X.Opens} {d : ∀ W : X.Opens, Γ(X, W) → Γ(Y, m ⁻¹ᵁ W)}

theorem resG_resG {U V W : X.Opens} (h : V ≤ U) (h' : W ≤ V) (f : Γ(X, U)) :
    resG X h' (resG X h f) = resG X (h'.trans h) f := by
  show (X.presheaf.map (homOfLE h).op ≫ X.presheaf.map (homOfLE h').op).hom f = _
  rw [← Functor.map_comp]
  rfl

theorem resG_constFn {U V : X.Opens} (h : V ≤ U) (r : R) : resG X h (constFn p U r) = constFn p V r := by
  unfold constFn
  exact congrArg (fun φ => CommRingCat.Hom.hom φ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r))
    (Scheme.Hom.appLE_map p _ (homOfLE h).op)

def ptOf (W₀ : X.Opens) (d : ∀ W : X.Opens, Γ(X, W) → Γ(Y, m ⁻¹ᵁ W)) (y : Sp ℂ ⟶ Y) (W : X.Opens) (f : Γ(X, W)) : ℂ :=
  valAt' y (m ⁻¹ᵁ (W ⊓ W₀)) (d (W ⊓ W₀) (resG X inf_le_left f))

theorem val_res {D : R → ℂ} (h : LocDer q p m D W₀ d) (y : Sp ℂ ⟶ Y) {W W' : X.Opens} (hW : W' ≤ W) (h0 : W ≤ W₀)
    (hy : ⊤ ≤ (y ≫ m) ⁻¹ᵁ W') (f : Γ(X, W)) :
    valAt' y (m ⁻¹ᵁ W') (d W' (resG X hW f)) = valAt' y (m ⁻¹ᵁ W) (d W f) := by
  have hy1 : ⊤ ≤ y ⁻¹ᵁ m ⁻¹ᵁ W' := hy
  rw [h.res W W' hW h0 f]
  exact valAt'_resG_of_le y (fun _ hx => hW hx) hy1 (d W f)

theorem ptDer_ptOf {D : R → ℂ} (h : LocDer q p m D W₀ d) (y : Sp ℂ ⟶ Y) (hy : ⊤ ≤ (y ≫ m) ⁻¹ᵁ W₀) :
    PtDer (y ≫ m) (ptOf W₀ d y) where
  add W _ f f' := by
    rename_i hW
    obtain ⟨φ, hφ⟩ := exists_ringHom_eq_valAt'' y (m ⁻¹ᵁ (W ⊓ W₀)) (top_le_preimage_preimage_inf y m hW hy)
    unfold ptOf
    rw [map_add, h.add _ inf_le_right]
    simp only [hφ, map_add]
  mul W hW f f' := by
    have hh : ⊤ ≤ y ⁻¹ᵁ m ⁻¹ᵁ (W ⊓ W₀) := top_le_preimage_preimage_inf y m hW hy
    obtain ⟨φ, hφ⟩ := exists_ringHom_eq_valAt'' y (m ⁻¹ᵁ (W ⊓ W₀)) hh
    have e1 : ∀ g : Γ(X, W), valAt' (y ≫ m) W g = φ ((m.app (W ⊓ W₀)).hom (resG X inf_le_left g)) := fun g => by
      rw [← hφ, valAt'_app_eq_valAt'_comp_moduli, valAt'_resG_of_le (y ≫ m) inf_le_left hh]
    unfold ptOf
    rw [e1 f, e1 f', map_mul, h.mul _ inf_le_right]
    simp only [hφ, map_add, map_mul]
  res W W' hle hW' f := by
    unfold ptOf
    rw [resG_resG, ← val_res h y (inf_le_inf_right W₀ hle) inf_le_right (top_le_preimage_preimage_inf y m hW' hy)
      (resG X inf_le_left f), resG_resG]

theorem ptOf_const {D : R → ℂ} (h : LocDer q p m D W₀ d) (y : Sp ℂ ⟶ Y) (hq : y ≫ q = 𝟙 _)
    (hy : ⊤ ≤ (y ≫ m) ⁻¹ᵁ W₀) (r : R) : ptOf W₀ d y ⊤ (constFn p ⊤ r) = D r := by
  unfold ptOf
  rw [resG_constFn, h.base _ inf_le_right r]
  exact valAt'_constFn' y q hq (m ⁻¹ᵁ (⊤ ⊓ W₀)) (fun a ha => ⟨trivial, hy ha⟩) (D r)

end GlobalTheory.KS.VertReg

namespace GlobalTheory.KS
open VertReg

theorem locDer_regular_coeff : ∀ (P₀ : Out.PolAV (Sp ℂ)) (u : HolUnif P₀.A P₀.L P₀.g) (Hm : Matrix (Fin P₀.g) (Fin P₀.g) ℂ) (χ : u.Λ → ℂ), GoodU u Hm χ → ∀ (R : Type) [CommRing R] (x₀ : R →+* ℂ) (X : Scheme.{0}) (p : X ⟶ Sp R) (m : P₀.A.left ⟶ X), Smooth p → IsPullback m P₀.A.hom p (spMap x₀) → ∀ (W₀ : X.Opens) (d : ∀ W : X.Opens, Γ(X, W) → Γ(P₀.A.left, m ⁻¹ᵁ W)), LocDer P₀.A.hom p m (fun _ => 0) W₀ d → ∃ c : Fin P₀.g → Γ(P₀.A.left, m ⁻¹ᵁ W₀), ∀ W, W ≤ W₀ → ∀ f, ∀ z ∈ dom u m W, valAt' (u.ex z).left (m ⁻¹ᵁ W) (d W f) = fderiv ℂ (fn u m W f) z (fun a => valAt' (u.ex z).left (m ⁻¹ᵁ W₀) (c a)) := by
  classical
  intro P₀ u Hm χ hG R _ x₀ X p m hsm hpb W₀ d hd
  have hq : ∀ z, (u.ex z).left ≫ P₀.A.hom = 𝟙 _ := fun z => by simp [Over.w (u.ex z)]
  have hw : ∀ z, ⊤ ≤ ((u.ex z).left ≫ m) ⁻¹ᵁ W₀ → ∃ w : Fin P₀.g → ℂ, ∀ W f, z ∈ dom u m W →
      ptOf W₀ d (u.ex z).left W f = fderiv ℂ (fn u m W f) z w := fun z hz =>
    (GlobalTheory.T.existsUnique_uniformising_vector_vertical_tangent P₀ u Hm χ hG R x₀ X p m hsm hpb z _ (ptDer_ptOf hd _ hz)
      (fun r => ptOf_const hd _ (hq z) hz r)).exists
  let wf : (Fin P₀.g → ℂ) → Fin P₀.g → ℂ := fun z =>
    if hz : ⊤ ≤ ((u.ex z).left ≫ m) ⁻¹ᵁ W₀ then (hw z hz).choose else 0
  have hwf : ∀ z (hz : ⊤ ≤ ((u.ex z).left ≫ m) ⁻¹ᵁ W₀) W f, z ∈ dom u m W →
      ptOf W₀ d (u.ex z).left W f = fderiv ℂ (fn u m W f) z (wf z) := by
    intro z hz W f hzW
    simp only [wf, dif_pos hz]
    exact (hw z hz).choose_spec W f hzW
  have lin : ∀ (L : (Fin P₀.g → ℂ) →L[ℂ] ℂ) (v : Fin P₀.g → ℂ), L v = ∑ i, v i * L (Pi.single i 1) := by
    intro L v
    conv_lhs => rw [← Finset.univ_sum_single v]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hs : (Pi.single i (v i) : Fin P₀.g → ℂ) = v i • (Pi.single i (1 : ℂ) : Fin P₀.g → ℂ) := by
      ext j
      by_cases hj : j = i <;> simp [hj]
    rw [hs, map_smul, smul_eq_mul]
  choose D _ hDv using fun i : Fin P₀.g => GlobalTheory.T.invariant_vectorField_abelianVariety_algebraic P₀ u Hm χ hG (Pi.single i 1)
  have hfn : ∀ (W : X.Opens) (f : Γ(X, W)),
      (fun z' => valAt' (u.ex z').left (m ⁻¹ᵁ W) ((m.app W).hom f)) = fn u m W f := fun W f => by
    funext z'
    exact valAt'_app_eq_valAt'_comp_moduli _ m W f
  have hc : ∀ a, ∃ c : Γ(P₀.A.left, m ⁻¹ᵁ W₀), ∀ z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ (m ⁻¹ᵁ W₀) →
      valAt' (u.ex z).left (m ⁻¹ᵁ W₀) c = wf z a := by
    intro a
    refine (GlobalTheory.T.existsUnique_section_of_locally_given_values P₀ u Hm χ hG (m ⁻¹ᵁ W₀) (fun z => wf z a) ?_).exists
    intro z hz
    obtain ⟨W, t, hzW, hdet⟩ := GlobalTheory.T.exists_fibre_coords_det_fderiv_ne_zero_of_smooth P₀ u Hm χ hG R x₀ X p m hsm hpb z
    have hzW' : ⊤ ≤ (u.ex z).left ⁻¹ᵁ ((𝟙 P₀.A.left) ⁻¹ᵁ (m ⁻¹ᵁ W)) := hzW
    let J : Matrix (Fin P₀.g) (Fin P₀.g) Γ(P₀.A.left, (𝟙 P₀.A.left) ⁻¹ᵁ (m ⁻¹ᵁ W)) :=
      fun i b => D i (m ⁻¹ᵁ W) ((m.app W).hom (t b))
    let e : Fin P₀.g → Γ(P₀.A.left, m ⁻¹ᵁ (W ⊓ W₀)) := fun b => d (W ⊓ W₀) (resG X inf_le_left (t b))
    have hJv : ∀ z', ⊤ ≤ (u.ex z').left ⁻¹ᵁ (m ⁻¹ᵁ W) → ∀ i b,
        valAt' (u.ex z').left _ (J i b) = fderiv ℂ (fn u m W (t b)) z' (Pi.single i 1) := by
      intro z' hz' i b
      rw [← hfn]
      exact hDv i (m ⁻¹ᵁ W) _ z' hz'
    obtain ⟨c, hcr⟩ := exists_cramer _ _ J e a
    refine ⟨_, c, inf_le_right.trans (fun _ hx => (inf_le_right : W ⊓ W₀ ≤ W₀) hx), ?_, ?_⟩
    · have hb : ⊤ ≤ (u.ex z).left ⁻¹ᵁ P₀.A.left.basicOpen J.det := by
        refine top_le_preimage_basicOpen_of_valAt'_ne_zero _ _ hzW' _ ?_
        obtain ⟨φ, hφ⟩ := exists_ringHom_eq_valAt'' _ _ hzW'
        rw [hφ, RingHom.map_det]
        convert hdet using 2
        ext i b
        rw [RingHom.mapMatrix_apply, Matrix.map_apply, ← hφ, hJv z hzW i b]
        rfl
      exact fun x hx => ⟨hb hx, ⟨hzW hx, hz hx⟩⟩
    · intro z' hz'
      have h2 : ⊤ ≤ (u.ex z').left ⁻¹ᵁ m ⁻¹ᵁ (W ⊓ W₀) := fun x hx => (hz' hx).2
      have hW' : ⊤ ≤ ((u.ex z').left ≫ m) ⁻¹ᵁ W := fun x hx => (h2 hx).1
      have hW0 : ⊤ ≤ ((u.ex z').left ≫ m) ⁻¹ᵁ W₀ := fun x hx => (h2 hx).2
      refine hcr (u.ex z').left hz' (wf z') fun b => ?_
      have e1 : valAt' (u.ex z').left (m ⁻¹ᵁ (W ⊓ W₀)) (e b) = ptOf W₀ d (u.ex z').left W (t b) := rfl
      rw [e1, hwf z' hW0 W (t b) hW', lin]
      exact Finset.sum_congr rfl fun i _ => by rw [hJv z' hW' i b]
  choose c hcv using hc
  refine ⟨c, ?_⟩
  intro W hW f z hz
  have hz' : ⊤ ≤ ((u.ex z).left ≫ m) ⁻¹ᵁ W := hz
  have hz0 : ⊤ ≤ ((u.ex z).left ≫ m) ⁻¹ᵁ W₀ := fun x hx => hW (hz' hx)
  have e1 : valAt' (u.ex z).left (m ⁻¹ᵁ W) (d W f) = ptOf W₀ d (u.ex z).left W f :=
    (val_res hd _ inf_le_left hW (top_le_preimage_preimage_inf _ m hz' hz0) f).symm
  rw [e1, hwf z hz0 W f hz]
  congr 1
  funext a
  exact (hcv a z hz0).symm

end GlobalTheory.KS
end
