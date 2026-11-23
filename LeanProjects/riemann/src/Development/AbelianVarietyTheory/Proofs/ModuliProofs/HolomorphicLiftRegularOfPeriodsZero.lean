import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsSymm
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueUniformisingVectorVerticalTangentStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFibreCoords
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsDifferentiableOnVerticalVectorFieldStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLocalDerivationAlongFibreOfSmooth
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.InvariantVectorFieldAbelianVarietyAlgebraic
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LocDerRegularCoeff
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.AlgebraicCoboundaryOfHolomorphicCoboundary

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

noncomputable section
namespace GlobalTheory.KS.ZeroClass
open VertReg

section
variable {R : Type} [CommRing R] {Y X : Scheme.{0}} {q : Y ⟶ Sp ℂ} {p : X ⟶ Sp R} {m : Y ⟶ X} {D : R → ℂ}

theorem locDer_sub {V V' : X.Opens} {d d' : ∀ W : X.Opens, Γ(X, W) → Γ(Y, m ⁻¹ᵁ W)} (h : LocDer q p m D V d)
    (h' : LocDer q p m D V' d') : LocDer q p m (fun _ => 0) (V ⊓ V') (fun W f => d W f - d' W f) where
  add W hW f f' := by
    rw [h.add W (hW.trans inf_le_left), h'.add W (hW.trans inf_le_right)]
    abel
  mul W hW f f' := by
    rw [h.mul W (hW.trans inf_le_left), h'.mul W (hW.trans inf_le_right)]
    ring
  res W W' hle hW f := by
    rw [h.res W W' hle (hW.trans inf_le_left), h'.res W W' hle (hW.trans inf_le_right), map_sub]
  base W hW r := by
    rw [h.base W (hW.trans inf_le_left), h'.base W (hW.trans inf_le_right), sub_self,
      ← liftConstHom_apply, map_zero]

theorem ptOf_of_le {V : X.Opens} {d : ∀ W : X.Opens, Γ(X, W) → Γ(Y, m ⁻¹ᵁ W)} (h : LocDer q p m D V d)
    (y : Sp ℂ ⟶ Y) {W : X.Opens} (hW : W ≤ V) (hy : ⊤ ≤ (y ≫ m) ⁻¹ᵁ W) (f : Γ(X, W)) :
    ptOf V d y W f = valAt' y (m ⁻¹ᵁ W) (d W f) := by
  have hy' : ⊤ ≤ (y ≫ m) ⁻¹ᵁ (W ⊓ V) := (inf_eq_left.mpr hW).symm ▸ hy
  exact val_res h y inf_le_left hW hy' f

theorem ptDer_sub {y : Sp ℂ ⟶ X} {δ δ' : ∀ W : X.Opens, Γ(X, W) → ℂ} (h : PtDer y δ) (h' : PtDer y δ') :
    PtDer y (fun W f => δ W f - δ' W f) := by
  constructor
  · intro W hW f f'
    simp only [h.add W hW, h'.add W hW]
    ring
  · intro W hW f f'
    simp only [h.mul W hW, h'.mul W hW]
    ring
  · intro W W' hle hW f
    simp only [h.res W W' hle hW, h'.res W W' hle hW]

end

theorem ex_add_lattice {g : ℕ} {A₀ : Over (Sp ℂ)} [GrpObj A₀] {L₀ : LB A₀.left} (u : HolUnif A₀ L₀ g)
    (z : Fin g → ℂ) (l : u.Λ) : u.ex (z + l) = u.ex z := by
  rw [u.ex_add, (u.ker l).mpr l.2, ← (u.ker 0).mpr (zero_mem _), ← u.ex_add, add_zero]

variable {P₀ : Out.PolAV (Sp ℂ)} {u : HolUnif P₀.A P₀.L P₀.g} {Hm : Matrix (Fin P₀.g) (Fin P₀.g) ℂ} {χ : u.Λ → ℂ}
  {R : Type} [CommRing R] {x₀ : R →+* ℂ} {X : Scheme.{0}} {p : X ⟶ Sp R} {m : P₀.A.left ⟶ X}

theorem vector_ext (hu : GoodU u Hm χ) (hp : Smooth p) (hm : IsPullback m P₀.A.hom p (spMap x₀)) {V : X.Opens}
    {z : Fin P₀.g → ℂ} (hz : z ∈ dom u m V) {v v' : Fin P₀.g → ℂ}
    (h : ∀ W, W ≤ V → z ∈ dom u m W → ∀ f, fderiv ℂ (fn u m W f) z v = fderiv ℂ (fn u m W f) z v') : v = v' := by
  obtain ⟨W, t, hzW, hdet⟩ := exists_fibre_coords P₀ u Hm χ hu R x₀ X p m hp hm z
  have hzWV : z ∈ dom u m (W ⊓ V) := fun a ha => ⟨hzW ha, hz ha⟩
  have hlin : ∀ (w : Fin P₀.g → ℂ) b, fderiv ℂ (fn u m W (t b)) z w =
      Matrix.vecMul w (Matrix.of fun a b => fderiv ℂ (fn u m W (t b)) z (Pi.single a 1)) b := by
    intro w b
    conv_lhs => rw [← Finset.univ_sum_single w]
    rw [map_sum]
    simp only [Matrix.vecMul, dotProduct, Matrix.of_apply]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [show Pi.single a (w a) = w a • (Pi.single a 1 : Fin P₀.g → ℂ) by
      ext j; by_cases hj : j = a <;> simp [hj], map_smul, smul_eq_mul]
  have hk : Matrix.vecMul (v - v') (Matrix.of fun a b => fderiv ℂ (fn u m W (t b)) z (Pi.single a 1)) = 0 := by
    ext b
    rw [← hlin, map_sub, Pi.zero_apply, sub_eq_zero]
    have e := h (W ⊓ V) inf_le_right hzWV (resG X inf_le_left (t b))
    rwa [fderiv_fn_resG u m inf_le_left (t b) hzWV] at e
  exact sub_eq_zero.mp (Matrix.eq_zero_of_vecMul_eq_zero hdet hk)

theorem exists_periodic_vector (hu : GoodU u Hm χ) (hp : Smooth p) (hm : IsPullback m P₀.A.hom p (spMap x₀))
    {D : R → ℂ} {s} (hs : KSRel u p m D 0 s) {V : X.Opens} {d} (hd : LocDer P₀.A.hom p m D V d) :
    ∃ w : (Fin P₀.g → ℂ) → (Fin P₀.g → ℂ), DifferentiableOn ℂ w (dom u m V) ∧
      (∀ (l : u.Λ), ∀ z ∈ dom u m V, w (z + l) = w z) ∧
      ∀ W, W ≤ V → ∀ f, ∀ z ∈ dom u m W,
        s z W f = valAt' (u.ex z).left (m ⁻¹ᵁ W) (d W f) + fderiv ℂ (fn u m W f) z (w z) := by
  have hq : ∀ z, (u.ex z).left ≫ P₀.A.hom = 𝟙 _ := fun z => by simp
  have hex : ∀ (l : u.Λ) z, u.ex (z + l) = u.ex z := fun l z => ex_add_lattice u z l
  have hdomV : IsOpen (dom u m V) := (u.hol (m ⁻¹ᵁ V) 0).1
  have hpt : ∀ z ∈ dom u m V, PtDer ((u.ex z).left ≫ m)
      (fun W f => s z W f - ptOf V d (u.ex z).left W f) ∧
      ∀ r, s z ⊤ (constFn p ⊤ r) - ptOf V d (u.ex z).left ⊤ (constFn p ⊤ r) = 0 := fun z hz =>
    ⟨ptDer_sub (hs.der z) (ptDer_ptOf hd (u.ex z).left hz), fun r => by
      rw [hs.base z r, ptOf_const hd (u.ex z).left (hq z) hz r, sub_self]⟩
  obtain ⟨w, hw, hrep⟩ := GlobalTheory.T.exists_differentiableOn_verticalVectorField P₀ u Hm χ hu R x₀ X p m hp hm P₀.g (dom u m V) id
    (fun z W f => s z W f - ptOf V d (u.ex z).left W f) hdomV differentiable_id hpt
    (fun W f => ((hs.hol W f).mono fun z hz => hz.2).sub
      (((u.hol (m ⁻¹ᵁ (W ⊓ V)) (d (W ⊓ V) (resG X inf_le_left f))).2).mono fun z hz a ha => ⟨hz.2 ha, hz.1 ha⟩))
  refine ⟨w, hw, fun l z hz => ?_, fun W hWV f z hz => ?_⟩
  · have hzl : z + l ∈ dom u m V := by
      show ⊤ ≤ ((u.ex (z + l)).left ≫ m) ⁻¹ᵁ V
      rw [hex]; exact hz
    have hfn : ∀ W (f : Γ(X, W)), fderiv ℂ (fn u m W f) (z + l) = fderiv ℂ (fn u m W f) z := by
      intro W f
      have e : (fun x => fn u m W f (x + l)) = fn u m W f := by
        funext x; simp only [fn, hex]
      rw [← fderiv_comp_add_right, e]
    refine ((GlobalTheory.T.existsUnique_uniformising_vector_vertical_tangent P₀ u Hm χ hu R x₀ X p m hp hm z _ (hpt z hz).1 (hpt z hz).2).unique
      (fun W f hzW => ?_) (fun W f hzW => ?_))
    · have hzlW : z + l ∈ dom u m W := by
        show ⊤ ≤ ((u.ex (z + l)).left ≫ m) ⁻¹ᵁ W
        rw [hex]; exact hzW
      have e := hrep (z + l) hzl W f hzlW
      simp only [id, hex, hfn] at e
      rw [← e, hs.per l W f z hzW, Matrix.zero_mulVec, map_zero, add_zero]
    · exact hrep z hz W f hzW
  · have e := hrep z (fun a ha => hWV (hz ha)) W f hz
    rw [ptOf_of_le hd (u.ex z).left hWV hz f] at e
    simp only [id] at e
    rw [← e]; ring

private theorem valAt'_sub' {X : Scheme.{0}} (x : Sp ℂ ⟶ X) (U : X.Opens) (hx : ⊤ ≤ x ⁻¹ᵁ U)
    (a b : Γ(X, U)) : valAt' x U (a - b) = valAt' x U a - valAt' x U b := by
  simp only [valAt', dif_pos hx, valAt, map_sub]

private theorem valAt'_add_of_top_le {X : Scheme.{0}} (x : Sp ℂ ⟶ X) (U : X.Opens) (hx : ⊤ ≤ x ⁻¹ᵁ U)
    (a b : Γ(X, U)) : valAt' x U (a + b) = valAt' x U a + valAt' x U b := by
  simp only [valAt', dif_pos hx, valAt, map_add]

private theorem valAt'_mul_of_top_le {X : Scheme.{0}} (x : Sp ℂ ⟶ X) (U : X.Opens) (hx : ⊤ ≤ x ⁻¹ᵁ U)
    (a b : Γ(X, U)) : valAt' x U (a * b) = valAt' x U a * valAt' x U b := by
  simp only [valAt', dif_pos hx, valAt, map_mul]

private theorem valAt'_finset_sum {X : Scheme.{0}} (x : Sp ℂ ⟶ X) (U : X.Opens) (hx : ⊤ ≤ x ⁻¹ᵁ U)
    {κ : Type} (s : Finset κ) (F : κ → Γ(X, U)) : valAt' x U (∑ i ∈ s, F i) = ∑ i ∈ s, valAt' x U (F i) := by
  simp only [valAt', dif_pos hx, valAt, map_sum]

private theorem valAt'_comp' {Y X : Scheme.{0}} (y : Sp ℂ ⟶ Y) (m : Y ⟶ X) (W : X.Opens) (f : Γ(X, W)) :
    valAt' (y ≫ m) W f = valAt' y (m ⁻¹ᵁ W) ((m.app W).hom f) := by
  by_cases hy : ⊤ ≤ (y ≫ m) ⁻¹ᵁ W
  · have hy' : ⊤ ≤ y ⁻¹ᵁ (m ⁻¹ᵁ W) := hy
    rw [valAt', dif_pos hy, valAt', dif_pos hy', valAt, valAt]
    first
      | (rw [Scheme.comp_appLE]; rfl)
      | simp [Scheme.comp_appLE]
      | simp [Scheme.Hom.comp_appLE]
  · have hy' : ¬ ⊤ ≤ y ⁻¹ᵁ (m ⁻¹ᵁ W) := hy
    rw [valAt', dif_neg hy, valAt', dif_neg hy']

private theorem valAt'_resG_of_top_le {X : Scheme.{0}} (x : Sp ℂ ⟶ X) {U V : X.Opens} (h : V ≤ U) (hx : ⊤ ≤ x ⁻¹ᵁ V)
    (a : Γ(X, U)) : valAt' x V (resG X h a) = valAt' x U a := by
  have hx' : ⊤ ≤ x ⁻¹ᵁ U := fun p hp => h (hx hp)
  rw [valAt', dif_pos hx, valAt', dif_pos hx', valAt, valAt, resG]
  congr 1
  exact congrArg (fun φ => φ.hom a) (x.map_appLE hx (homOfLE h).op)

private theorem continuousLinearMap_apply_eq_sum_single {n : ℕ} (φ : (Fin n → ℂ) →L[ℂ] ℂ) (w : Fin n → ℂ) :
    φ w = ∑ b, w b * φ (Pi.single b 1) := by
  conv_lhs => rw [← Finset.univ_sum_single w]
  rw [map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [show Pi.single a (w a) = w a • (Pi.single a 1 : Fin n → ℂ) by
    ext j; by_cases hj : j = a <;> simp [hj], map_smul, smul_eq_mul]

end GlobalTheory.KS.ZeroClass

namespace GlobalTheory.KS
open ZeroClass

theorem regular_of_periods_zero : Out.Laws → ∀ (P₀ : Out.PolAV (Sp ℂ)) (u : HolUnif P₀.A P₀.L P₀.g) (Hm : Matrix (Fin P₀.g) (Fin P₀.g) ℂ) (χ : u.Λ → ℂ), GoodU u Hm χ → ∀ (R : Type) [CommRing R] (x₀ : R →+* ℂ) (X : Scheme.{0}) (p : X ⟶ Sp R) (m : P₀.A.left ⟶ X), Smooth p → IsPullback m P₀.A.hom p (spMap x₀) → ∀ D s, IsDer x₀ D → KSRel u p m D 0 s → ∀ W₀, IsAffineOpen W₀ → ∀ W, W ≤ W₀ → ∀ f : Γ(X, W), ∃ a : Γ(P₀.A.left, m ⁻¹ᵁ W), ∀ z ∈ dom u m W, valAt' (u.ex z).left (m ⁻¹ᵁ W) a = s z W f := by
  intro hL P₀ u Hm χ hu R _ x₀ X p m hp hm D s hD hs W₀ hW₀ W hWW₀ f
  choose dd hdd using fun i : X.affineOpens =>
    exists_locDer_of_smooth R x₀ P₀.A.left X P₀.A.hom p m D i.1 hp hm.w hD i.2
  choose ww hww hper hrep using fun i : X.affineOpens => exists_periodic_vector hu hp hm hs (hdd i)
  choose cc hcc using fun i j : X.affineOpens =>
    locDer_regular_coeff P₀ u Hm χ hu R x₀ X p m hp hm _ _ (locDer_sub (hdd i) (hdd j))
  have hrel : ∀ (i j : X.affineOpens) z, z ∈ dom u m (i.1 ⊓ j.1) →
      ww j z - ww i z = fun a => valAt' (u.ex z).left (m ⁻¹ᵁ (i.1 ⊓ j.1)) (cc i j a) := by
    intro i j z hz
    refine vector_ext hu hp hm hz fun W' hW' hzW' f' => ?_
    have e1 := hrep i W' (hW'.trans inf_le_left) f' z hzW'
    have e2 := hrep j W' (hW'.trans inf_le_right) f' z hzW'
    have e3 := hcc i j W' hW' f' z hzW'
    rw [valAt'_sub' (u.ex z).left (m ⁻¹ᵁ W') hzW'] at e3
    rw [map_sub, ← e3]
    linear_combination e1 - e2
  have hcov : ⨆ i : X.affineOpens, m ⁻¹ᵁ i.1 = ⊤ := by
    refine eq_top_iff.mpr fun y _ => ?_
    have hy : m.base y ∈ (⨆ i : X.affineOpens, (i.1 : X.Opens)) := by
      rw [iSup_affineOpens_eq_top X]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hy
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, hi⟩
  let i₀ : X.affineOpens := ⟨W₀, hW₀⟩
  have hcob : ∀ a : Fin P₀.g, ∃ e : Γ(P₀.A.left, m ⁻¹ᵁ W₀), ∀ z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ (m ⁻¹ᵁ W₀) →
      valAt' (u.ex z).left (m ⁻¹ᵁ W₀) e = ww i₀ z a := fun a =>
    algebraic_coboundary_of_holomorphic_coboundary hL P₀ u Hm χ hu X.affineOpens (fun i => m ⁻¹ᵁ i.1)
      (fun i j => cc i j a) (fun i z => ww i z a) hcov
      (fun i => ⟨(differentiableOn_pi.mp (hww i)) a, fun l z hz => congrFun (hper i l z hz) a⟩)
      (fun i j z hz => (congrFun (hrel i j z hz) a).symm) i₀
  choose ee hee using hcob
  choose δ hδ hδv using fun b : Fin P₀.g => invariant_field_algebraic P₀ u Hm χ hu (Pi.single b 1)
  have hW' : m ⁻¹ᵁ W ≤ m ⁻¹ᵁ W₀ := fun y hy => hWW₀ hy
  refine ⟨dd i₀ W f + ∑ b, resG P₀.A.left hW' (ee b) *
    (show Γ(P₀.A.left, m ⁻¹ᵁ W) from δ b (m ⁻¹ᵁ W) ((m.app W).hom f)), fun z hz => ?_⟩
  have hz0 : ⊤ ≤ (u.ex z).left ⁻¹ᵁ (m ⁻¹ᵁ W₀) := fun y hy => hWW₀ (hz hy)
  have hzW : ⊤ ≤ (u.ex z).left ⁻¹ᵁ (m ⁻¹ᵁ W) := hz
  rw [hrep i₀ W hWW₀ f z hz, valAt'_add_of_top_le _ _ hzW, valAt'_finset_sum _ _ hzW]
  congr 1
  rw [continuousLinearMap_apply_eq_sum_single (fderiv ℂ (fn u m W f) z) (ww i₀ z)]
  refine Finset.sum_congr rfl fun b _ => ?_
  have hv : valAt' (u.ex z).left (m ⁻¹ᵁ W) (show Γ(P₀.A.left, m ⁻¹ᵁ W) from δ b (m ⁻¹ᵁ W) ((m.app W).hom f)) =
      fderiv ℂ (fun z' => valAt' (u.ex z').left (m ⁻¹ᵁ W) ((m.app W).hom f)) z (Pi.single b 1) :=
    hδv b (m ⁻¹ᵁ W) ((m.app W).hom f) z hzW
  have efn : (fun z' => valAt' (u.ex z').left (m ⁻¹ᵁ W) ((m.app W).hom f)) = fn u m W f :=
    funext fun z' => (valAt'_comp' _ _ _ _).symm
  rw [valAt'_mul_of_top_le _ _ hzW, valAt'_resG_of_top_le _ hW' hzW, hee b z hz0, hv, efn]

end GlobalTheory.KS
end
