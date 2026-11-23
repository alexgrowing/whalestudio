import Mathlib
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.BlockTheory.CMModuli.FirstOrderRigidityLevel
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.ThetaPtSupportMeetsEveryCoset
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.LevelBasisEqOfSameThetaPt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaConstantsUniqueUpToUnit
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHeckeQuotientTriple
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.ExistsIsSymplecticFamilySpan
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.RosatiAdjOfPoints
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TracePowerSumModEq
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.PowObjGeometricallyConnected

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Published

def EndCharPolySt : Prop :=
  ∀ (K : Type) [Field K] [IsAlgClosed K] (P : PolAV (Sp K)) (ψ : P.A ⟶ P.A), IsMonHom ψ →
    ∃ χ : Polynomial ℤ, χ.Monic ∧ χ.natDegree = 2 * P.g ∧ ∀ l r : ℕ, l.Prime → (l : K) ≠ 0 →
      ∀ y : Fin (2 * P.g) → (baseOver (Sp K) ⟶ P.A), (∀ i, y i ^ l ^ r = 1) →
        (∀ z : baseOver (Sp K) ⟶ P.A, z ^ l ^ r = 1 → ∃ c : Fin (2 * P.g) → ℕ, linComb y c = z) →
        ∀ B : Matrix (Fin (2 * P.g)) (Fin (2 * P.g)) (ZMod (l ^ r)),
          (∀ i, y i ≫ ψ = linComb y fun k => (B k i).val) → B.charpoly = χ.map (Int.castRingHom (ZMod (l ^ r)))

def RosatiPositiveSt : Prop :=
  ∀ (K : Type) [Field K] [IsAlgClosed K] (P : PolAV (Sp K)) (φ φ' : P.A ⟶ P.A), IsMonHom φ → IsMonHom φ' →
    RosatiAdj P.A P.L φ φ' → φ ≠ 1 → ∀ t : ℤ, IndefiniteRowSideFullHecke.FirstOrderRigidityLevel.HasTrace P (φ' ≫ φ) t → 0 < t

end GlobalTheory.Published

namespace GlobalTheory.ThetaDetCompare

open GlobalTheory.IndefiniteRowSideFullHecke

section AdjRing

open CechPic MulOpposite

variable {K : Type} [Field K] {P : PolAV (Sp K)}

theorem rosatiAdj_iff_lam {f g : P.A ⟶ P.A} : RosatiAdj P.A P.L f g ↔ ∀ (T : Over (Sp K)) (x y : T ⟶ P.A),
    lam (cls P.L P.isLB) (x ≫ f) y = lam (cls P.L P.isLB) x (y ≫ g) := by
  have e : ∀ u v : P.A ⊗ P.A ⟶ P.A, padd P.A u v = u * v := fun _ _ => rfl
  have key : ∑ i, rosatiε i • pull (rosatiφ P.A f g i) (cls P.L P.isLB) =
      lam (cls P.L P.isLB) (fst _ _ ≫ f) (snd _ _) - lam (cls P.L P.isLB) (fst _ _) (snd P.A P.A ≫ g) := by
    simp only [Fin.sum_univ_succ, rosatiφ, rosatiε, Matrix.cons_val_zero, Matrix.cons_val_succ, e, Fin.sum_univ_zero,
      lam]
    module
  have key' : ∀ {Y : Scheme.{0}} (q : Y ⟶ (P.A ⊗ P.A).left),
      cls (LB.LinComb P.L (fun i => q ≫ rosatiφ P.A f g i) rosatiε) (LB.isLB_linComb P.isLB _ _) =
        pull q (∑ i, rosatiε i • pull (rosatiφ P.A f g i) (cls P.L P.isLB)) := fun q => by
    rw [cls_linComb P.isLB]
    simp only [map_sum, map_zsmul, pull_comp]
  refine ⟨fun h T x y => ?_, fun h s => ⟨⊤, trivial, (cls_eq_zero_iff (LB.isLB_linComb P.isLB _ _)).1 ?_⟩⟩
  · obtain ⟨U, hU, ht⟩ := h (default : PrimeSpectrum K)
    obtain rfl : U = ⊤ := top_unique fun y _ => by
      obtain rfl : y = (default : PrimeSpectrum K) := Subsingleton.elim (α := PrimeSpectrum K) _ _
      exact hU
    have : IsIso ((P.A ⊗ P.A).hom ⁻¹ᵁ ⊤).ι := inferInstanceAs (IsIso ((P.A ⊗ P.A).left.topIso).hom)
    have h₁ := congrArg (pull ((lift x y).left ≫ inv ((P.A ⊗ P.A).hom ⁻¹ᵁ ⊤).ι))
      ((key' _).symm.trans ((cls_eq_zero_iff (LB.isLB_linComb P.isLB _ _)).2 ht))
    rw [← pull_comp, Category.assoc, IsIso.inv_hom_id, Category.comp_id, key, map_sub, pull_lam, pull_lam,
      map_zero, lift_fst_assoc, lift_snd_assoc, lift_fst, lift_snd] at h₁
    exact sub_eq_zero.1 h₁
  · rw [key', key, h, sub_self, map_zero]

theorem rosatiAdj_symm {f g : P.A ⟶ P.A} (h : RosatiAdj P.A P.L f g) : RosatiAdj P.A P.L g f := by
  have := P.isAb.comm
  refine rosatiAdj_iff_lam.2 fun T x y => ?_
  rw [lam_comm, ← rosatiAdj_iff_lam.1 h, lam_comm]

theorem rosatiAdj_comp {f g f' g' : P.A ⟶ P.A} (h : RosatiAdj P.A P.L f g) (h' : RosatiAdj P.A P.L f' g') :
    RosatiAdj P.A P.L (f ≫ f') (g' ≫ g) := by
  refine rosatiAdj_iff_lam.2 fun T x y => ?_
  rw [← Category.assoc, rosatiAdj_iff_lam.1 h', rosatiAdj_iff_lam.1 h, Category.assoc]

def evId (e : AddMonoid.End (Additive (P.A ⟶ P.A))) : P.A ⟶ P.A := (e (Additive.ofMul (𝟙 _))).toMul

structure IsEnd (e : AddMonoid.End (Additive (P.A ⟶ P.A))) : Prop where
  hom : IsMonHom (evId e)
  eq : ∀ x, (e x).toMul = x.toMul ≫ evId e

variable (P) in

def endRing : Subring (AddMonoid.End (Additive (P.A ⟶ P.A))) where
  carrier := {e | IsEnd e}
  mul_mem' {a b} ha hb := by
    have := ha.hom; have := hb.hom
    have e : evId (a * b) = evId b ≫ evId a := ha.eq _
    refine ⟨by rw [e]; infer_instance, fun x => ?_⟩
    rw [e, ← Category.assoc, ← hb.eq]
    exact ha.eq _
  one_mem' := ⟨inferInstanceAs (IsMonHom (𝟙 _)), fun x => (Category.comp_id x.toMul).symm⟩
  add_mem' {a b} ha hb := by
    have := ha.hom; have := hb.hom
    have e : evId (a + b) = evId a * evId b := rfl
    refine ⟨by rw [e]; exact Serre.isMonHom_mul _ _, fun x => ?_⟩
    rw [e, MonObj.comp_mul, ← ha.eq, ← hb.eq]
    rfl
  zero_mem' := ⟨Serre.isMonHom_one, fun x => (MonObj.comp_one x.toMul).symm⟩
  neg_mem' {a} ha := by
    have := ha.hom
    have e : evId (-a) = (evId a)⁻¹ := rfl
    refine ⟨by rw [e]; infer_instance, fun x => ?_⟩
    rw [e, GrpObj.comp_inv, ← ha.eq]
    rfl

variable (P) in

def endAct : RingAct P.A (endRing P) where
  act e := evId e.1
  hom e := IsEnd.hom e.2
  map_one := rfl
  map_mul a _ := IsEnd.eq a.2 _
  map_add _ _ := rfl

variable (P) in

def adjRing (hc : CubeSt) : Subring (endRing P × (endRing P)ᵐᵒᵖ) where
  carrier := {a | RosatiAdj P.A P.L ((endAct P).act a.1) ((endAct P).act a.2.unop)}
  mul_mem' {a b} ha hb := by
    change RosatiAdj P.A P.L ((endAct P).act (a.1 * b.1)) ((endAct P).act (b.2.unop * a.2.unop))
    rw [RingAct.map_mul, RingAct.map_mul]
    exact rosatiAdj_comp hb ha
  one_mem' := IntAct.rosatiAdj_id P.isLB
  add_mem' {a b} ha hb := by
    obtain ⟨r, hr⟩ := P.rigid
    obtain ⟨c⟩ := (hc _ P ⟨P.L, r, P.isLB, hr⟩ rfl).1
    exact rosatiAdj_mul _ P.A ⟨P.L, r, P.isLB, hr⟩ c _ _ _ _ ha hb
  zero_mem' := IntAct.rosatiAdj_one P.isLB
  neg_mem' {a} ha := by
    have h := rosatiAdj_comp ha (IntAct.rosatiAdj_inv P.isLB P.sym)
    have := (endAct P).hom a.2.unop
    rwa [GrpObj.comp_inv, GrpObj.inv_comp, Category.comp_id, Category.id_comp] at h

instance (hc : CubeSt) : StarRing (adjRing P hc) where
  star a := ⟨(a.1.2.unop, op a.1.1), rosatiAdj_symm a.2⟩
  star_involutive _ := rfl
  star_mul _ _ := rfl
  star_add _ _ := rfl

variable (P) in

def adjAct (hc : CubeSt) : P.OAct (adjRing P hc) where
  act a := (endAct P).act a.1.1
  hom _ := (endAct P).hom _
  map_one := rfl
  map_mul _ _ := (endAct P).map_mul _ _
  map_add _ _ := rfl
  rosati a := a.2

def comapOAct {O O' : Type} [Ring O] [StarRing O] [Ring O'] [StarRing O'] (ρ : P.OAct O) (φ : O' →+* O)
    (h : ∀ a, φ (star a) = star (φ a)) : P.OAct O' where
  act a := ρ.act (φ a)
  hom _ := ρ.hom _
  map_one := by rw [map_one, ρ.map_one]
  map_mul a b := by rw [map_mul, ρ.map_mul]
  map_add a b := by rw [map_add, ρ.map_add]
  rosati a := by rw [h]; exact ρ.rosati _

end AdjRing

section Trace

open ThetaCoord

variable {K : Type} [Field K] {P : PolAV (Sp K)} {M : ℕ} {y : Fin (2 * P.g) → (baseOver (Sp K) ⟶ P.A)}
  {O : Type} [Ring O]

def Frame (P : PolAV (Sp K)) (M : ℕ) (y : Fin (2 * P.g) → (baseOver (Sp K) ⟶ P.A)) : Prop :=
  (∀ i, y i ^ M = 1) ∧ ∀ z : baseOver (Sp K) ⟶ P.A, z ^ M = 1 → ∃ c : Fin (2 * P.g) → ℕ, linComb y c = z

def Rep (y : Fin (2 * P.g) → (baseOver (Sp K) ⟶ P.A)) (ψ : P.A ⟶ P.A)
    (B : Matrix (Fin (2 * P.g)) (Fin (2 * P.g)) (ZMod M)) : Prop :=
  ∀ i, y i ≫ ψ = lab y fun k => B k i

theorem lab_natCast (h : ∀ i, y i ^ M = 1) (c : Fin (2 * P.g) → ℕ) :
    lab y (fun i => (c i : ZMod M)) = linComb y c := by
  simp only [lab, linComb, ZMod.val_natCast]
  exact congrArg (fun f => (List.ofFn f).prod) (funext fun i => (pow_eq_pow_mod _ (h i)).symm)

theorem Frame.exists_rep (h : Frame P M y) (ψ : P.A ⟶ P.A) [IsMonHom ψ] :
    ∃ B : Matrix _ _ (ZMod M), Rep y ψ B := by
  choose c hc using fun i => h.2 (y i ≫ ψ) (by rw [← MonObj.pow_comp, h.1, MonObj.one_comp])
  exact ⟨fun k i => (c i k : ZMod M), fun i => ((lab_natCast h.1 _).trans (hc i)).symm⟩

def repRing [NeZero M] (ρ : RingAct P.A O) (h : ∀ i, y i ^ M = 1) :
    Subring (O × Matrix (Fin (2 * P.g)) (Fin (2 * P.g)) (ZMod M)) :=
  have := P.isAb.comm
  let F (x : baseOver (Sp K) ⟶ P.A) : O →+ Additive (baseOver (Sp K) ⟶ P.A) :=
    AddMonoidHom.mk' (fun a => Additive.ofMul (x ≫ ρ.act a)) fun a b =>
      (congrArg (x ≫ ·) (ρ.map_add a b)).trans (MonObj.comp_mul x _ _)
  let G : (Fin (2 * P.g) → ZMod M) →+ Additive (baseOver (Sp K) ⟶ P.A) :=
    AddMonoidHom.mk' (fun c => Additive.ofMul (lab y c)) (lab_add h)
  { carrier := {x | Rep y (ρ.act x.1) x.2}
    mul_mem' := fun {a b} ha hb i => by
      have := ρ.hom a.1
      rw [Prod.fst_mul, ρ.map_mul, ← Category.assoc, hb i]
      exact char_ext (fun c => lab y c ≫ ρ.act a.1) (fun c => lab y (a.2.mulVec c))
        (fun c d => by rw [lab_add h, MonObj.mul_comp]) (fun c d => by rw [Matrix.mulVec_add, lab_add h])
        (fun j => by rw [lab_single h, Matrix.mulVec_single_one]; exact ha j) _
    one_mem' := fun i => by
      rw [Prod.fst_one, ρ.map_one, Category.comp_id, ← lab_single h i]
      exact congrArg _ (funext fun k => by simp [Matrix.one_apply, Pi.single_apply])
    add_mem' := fun {a b} ha hb i => (map_add (F (y i)) a.1 b.1).trans
      ((congrArg₂ (· * ·) (ha i) (hb i)).trans (map_add G _ _).symm)
    zero_mem' := fun i => (map_zero (F (y i))).trans (map_zero G).symm
    neg_mem' := fun {a} ha i => (map_neg (F (y i)) a.1).trans ((congrArg (·⁻¹) (ha i)).trans (map_neg G _).symm) }

variable [IsAlgClosed K]

theorem exists_frame (hL : Laws) (P : PolAV (Sp K)) {l : ℕ} (hl : l.Prime) (hK : (l : K) ≠ 0) (r : ℕ) :
    ∃ y, Frame P (l ^ r) y := by
  have : NeZero (l ^ r) := ⟨pow_ne_zero _ hl.ne_zero⟩
  have : NeZero ((l ^ r : ℕ) : K) := ⟨by rw [Nat.cast_pow]; exact pow_ne_zero _ hK⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot K (l ^ r)
  have h := hζ.map_of_injective (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.symm.injective
  obtain ⟨lev⟩ := nonempty_level_prime_pow hL K P l r hl hK _ (h.isUnit_unit (NeZero.ne _))
  refine ⟨lev.pt, lev.torsion, fun z hz => ?_⟩
  obtain ⟨a, ha⟩ := (pow_eq_one_iff (Nat.mul_one _).symm lev rfl z).1 hz
  exact ⟨_, (pow_one _).symm.trans ha⟩

theorem int_eq_of_frames (hL : Laws) (P : PolAV (Sp K)) {s t : ℤ} (H : ∀ l r : ℕ, l.Prime → (l : K) ≠ 0 →
    ∀ y, Frame P (l ^ r) y → (s : ZMod (l ^ r)) = t) : s = t := by
  obtain ⟨l, hl, hK⟩ : ∃ l : ℕ, l.Prime ∧ (l : K) ≠ 0 := by
    by_contra! h
    have h₂ := h 2 Nat.prime_two
    have h₃ := h 3 Nat.prime_three
    push_cast at h₂ h₃
    exact one_ne_zero (α := K) (by linear_combination h₃ - h₂)
  obtain ⟨y, hy⟩ := exists_frame hL P hl hK (t - s).natAbs
  have h := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1 (H l _ hl hK y hy)
  have := Nat.eq_zero_of_dvd_of_lt (Int.natCast_dvd.1 h) (Nat.lt_pow_self hl.one_lt)
  omega

end Trace

section Positive

variable {K : Type} [Field K] [IsAlgClosed K] {P : PolAV (Sp K)} {O : Type} [Ring O] [StarRing O]

end Positive

end GlobalTheory.ThetaDetCompare
