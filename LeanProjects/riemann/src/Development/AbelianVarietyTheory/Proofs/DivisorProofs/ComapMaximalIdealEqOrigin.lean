import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsorsTrivial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OriginIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosureFiniteEtale
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointAtZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodIffEtaleAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsZModTorsorFiniteProjectiveBaseChange

open IsLocalRing Polynomial
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.KeyOriginBC

section Poly

variable {A A₁ : Type} [CommRing A] [CommRing A₁] (f : A →+* A₁)

def PolyOver (_f : A →+* A₁) : Type := A₁[X]

instance : CommRing (PolyOver f) := inferInstanceAs (CommRing A₁[X])

instance : Algebra A[X] (PolyOver f) := (Polynomial.mapRingHom f).toAlgebra

instance : Algebra A₁[X] (PolyOver f) := inferInstanceAs (Algebra A₁[X] A₁[X])

instance : Algebra A₁ (PolyOver f) := inferInstanceAs (Algebra A₁ A₁[X])

instance : IsScalarTower A₁ A₁[X] (PolyOver f) := inferInstanceAs (IsScalarTower A₁ A₁[X] A₁[X])

instance : SMulCommClass A[X] A₁[X] (PolyOver f) where
  smul_comm a b c := mul_left_comm (G := A₁[X]) (Polynomial.map f a) b c

instance : SMulCommClass A[X] A₁ (PolyOver f) where
  smul_comm a b c := mul_smul_comm (β := A₁[X]) b (Polynomial.map f a) c

theorem algebraMap_polyOver (p : A[X]) : algebraMap A[X] (PolyOver f) p = Polynomial.map f p := rfl

variable (EA : Type) [CommRing EA] [Algebra A[X] EA]

abbrev Ext : Type := PolyOver f ⊗[A[X]] EA

example : Algebra A₁[X] (Ext f EA) := inferInstance
example : Algebra A₁ (Ext f EA) := inferInstance
example : IsScalarTower A₁ A₁[X] (Ext f EA) := inferInstance
instance [Algebra.Etale A[X] EA] : Algebra.Etale A₁[X] (Ext f EA) :=
  inferInstanceAs (Algebra.Etale (PolyOver f) (PolyOver f ⊗[A[X]] EA))

def inclE : EA →+* Ext f EA := (Algebra.TensorProduct.includeRight : EA →ₐ[A[X]] Ext f EA).toRingHom

theorem inclE_apply (x : EA) : inclE f EA x = (1 : PolyOver f) ⊗ₜ[A[X]] x := rfl

def lift {S : Type} [CommRing S] (u : A₁[X] →+* S) (v : EA →+* S)
    (huv : u.comp (Polynomial.mapRingHom f) = v.comp (algebraMap A[X] EA)) : Ext f EA →+* S :=
  letI : Algebra A[X] S := (v.comp (algebraMap A[X] EA)).toAlgebra
  (Algebra.TensorProduct.productMap
    (⟨(u : PolyOver f →+* S), fun r => by
        show u (Polynomial.map f r) = v (algebraMap A[X] EA r)
        exact congrArg (fun w : A[X] →+* S => w r) huv⟩ : PolyOver f →ₐ[A[X]] S)
    (⟨v, fun _ => rfl⟩ : EA →ₐ[A[X]] S)).toRingHom

theorem lift_tmul {S : Type} [CommRing S] (u : A₁[X] →+* S) (v : EA →+* S)
    (huv : u.comp (Polynomial.mapRingHom f) = v.comp (algebraMap A[X] EA)) (p : PolyOver f) (x : EA) :
    lift f EA u v huv (p ⊗ₜ[A[X]] x) = u p * v x := by
  simp [lift, Algebra.TensorProduct.productMap_apply_tmul]
  rfl

theorem algebraMap_ext (a : A₁) :
    algebraMap A₁ (Ext f EA) a = ((show PolyOver f from Polynomial.C a) ⊗ₜ[A[X]] (1 : EA) : Ext f EA) := rfl

end Poly

section Over

variable {B B₁ : Type} [CommRing B] [CommRing B₁] (β : B →+* B₁)

def Over (_β : B →+* B₁) : Type := B₁

instance : CommRing (Over β) := inferInstanceAs (CommRing B₁)

instance : Algebra B (Over β) := β.toAlgebra

variable (D : Type) [CommRing D] [Algebra B D]

abbrev BC : Type := Over β ⊗[B] D

def bcAct' (q : ℕ) (act : Multiplicative (ZMod q) →* (D ≃ₐ[B] D)) :
    Multiplicative (ZMod q) →* (BC β D ≃ₐ[Over β] BC β D) where
  toFun g := Algebra.TensorProduct.congr (AlgEquiv.refl : Over β ≃ₐ[Over β] Over β) (act g)
  map_one' := by
    apply AlgEquiv.ext; intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul b x => simp [Algebra.TensorProduct.congr_apply]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  map_mul' g h := by
    apply AlgEquiv.ext; intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul b x => simp [Algebra.TensorProduct.congr_apply, AlgEquiv.mul_apply]
    | add x y hx hy => rw [map_add, map_add, hx, hy]

instance : Algebra B₁ (BC β D) := inferInstanceAs (Algebra (Over β) (Over β ⊗[B] D))

def bcAct (q : ℕ) (act : Multiplicative (ZMod q) →* (D ≃ₐ[B] D)) :
    Multiplicative (ZMod q) →* (BC β D ≃ₐ[B₁] BC β D) := bcAct' β D q act

def inclD : D →+* BC β D := (Algebra.TensorProduct.includeRight : D →ₐ[B] BC β D).toRingHom

theorem inclD_algebraMap :
    (inclD β D).comp (algebraMap B D) = (algebraMap B₁ (BC β D)).comp β := by
  ext b
  simp [inclD, Algebra.TensorProduct.algebraMap_apply]
  rfl

end Over

end GlobalTheory.KeyOriginBC

namespace GlobalTheory.KeyOriginBC

section Datum

variable {T O : Type} [CommRing T] [CommRing O] [IsLocalRing O] [Algebra T O] [Algebra T[X] O]
  [IsScalarTower T T[X] O]
variable {A A₁ : Type} [CommRing A] [CommRing A₁] (f : A →+* A₁) (i : A →+* T) (i₁ : A₁ →+* T)
variable (EA : Type) [CommRing EA] [Algebra A[X] EA] (QA : Ideal EA) [QA.IsPrime]
  (jA : Localization.AtPrime QA →+* O)

def glue (hcomp : i₁.comp f = i)
    (hj : jA.comp (algebraMap A[X] (Localization.AtPrime QA)) =
      (algebraMap T[X] O).comp (Polynomial.mapRingHom i)) : Ext f EA →+* O :=
  lift f EA ((algebraMap T[X] O).comp (Polynomial.mapRingHom i₁))
    (jA.comp (algebraMap EA (Localization.AtPrime QA))) (by
      rw [RingHom.comp_assoc, Polynomial.mapRingHom_comp, hcomp, RingHom.comp_assoc,
        ← IsScalarTower.algebraMap_eq, hj])

variable (hcomp : i₁.comp f = i)
  (hj : jA.comp (algebraMap A[X] (Localization.AtPrime QA)) =
      (algebraMap T[X] O).comp (Polynomial.mapRingHom i))

theorem glue_tmul (p : PolyOver f) (x : EA) :
    glue f i i₁ EA QA jA hcomp hj (p ⊗ₜ[A[X]] x) =
      algebraMap T[X] O (Polynomial.map i₁ p) * jA (algebraMap EA (Localization.AtPrime QA) x) := by
  simp [glue, lift_tmul]
  rfl

theorem glue_algebraMap (a : A₁) :
    glue f i i₁ EA QA jA hcomp hj (algebraMap A₁ (Ext f EA) a) = algebraMap T O (i₁ a) := by
  rw [algebraMap_ext, glue_tmul]
  simp [IsScalarTower.algebraMap_apply T T[X] O]

theorem glue_inclE (x : EA) :
    glue f i i₁ EA QA jA hcomp hj (inclE f EA x) = jA (algebraMap EA (Localization.AtPrime QA) x) := by
  rw [inclE_apply, glue_tmul]
  change algebraMap T[X] O (Polynomial.map i₁ (1 : A₁[X])) * _ = _
  simp

def ideal₁ : Ideal (Ext f EA) := (maximalIdeal O).comap (glue f i i₁ EA QA jA hcomp hj)

instance : (ideal₁ f i i₁ EA QA jA hcomp hj).IsPrime := Ideal.comap_isPrime _ _

abbrev Loc₁ : Type := Localization.AtPrime (ideal₁ f i i₁ EA QA jA hcomp hj)

def locMap : Loc₁ f i i₁ EA QA jA hcomp hj →+* O :=
  IsLocalization.lift (M := (ideal₁ f i i₁ EA QA jA hcomp hj).primeCompl)
    (g := glue f i i₁ EA QA jA hcomp hj) (fun y => by
      by_contra h
      exact y.2 (IsLocalRing.mem_maximalIdeal _ |>.2 h))

theorem locMap_algebraMap (x : Ext f EA) :
    locMap f i i₁ EA QA jA hcomp hj (algebraMap (Ext f EA) (Loc₁ f i i₁ EA QA jA hcomp hj) x) =
      glue f i i₁ EA QA jA hcomp hj x := by
  simp [locMap, IsLocalization.lift_eq]

theorem locMap_algebraMap_base (a : A₁) :
    locMap f i i₁ EA QA jA hcomp hj (algebraMap A₁ (Loc₁ f i i₁ EA QA jA hcomp hj) a) =
      algebraMap T O (i₁ a) := by
  rw [IsScalarTower.algebraMap_apply A₁ (Ext f EA), locMap_algebraMap, glue_algebraMap]

def fibMap [IsDomain T] [Nontrivial A₁] (hi₁ : Function.Injective i₁) :
    GlobalTheory.LocAcyc.GenFib A₁ (Loc₁ f i i₁ EA QA jA hcomp hj) →+* GlobalTheory.LocAcyc.GenFib T O :=
  IsLocalization.lift
    (M := Algebra.algebraMapSubmonoid (Loc₁ f i i₁ EA QA jA hcomp hj) (nonZeroDivisors A₁))
    (g := (algebraMap O (GlobalTheory.LocAcyc.GenFib T O)).comp (locMap f i i₁ EA QA jA hcomp hj)) (by
      rintro ⟨_, a, ha, rfl⟩
      simp only [RingHom.coe_comp, Function.comp_apply, locMap_algebraMap_base]
      have h0 : i₁ a ≠ 0 := by
        rw [← map_zero i₁]; exact fun h => nonZeroDivisors.ne_zero ha (hi₁ h)
      exact IsLocalization.map_units (GlobalTheory.LocAcyc.GenFib T O)
        (⟨algebraMap T O (i₁ a), i₁ a, mem_nonZeroDivisors_of_ne_zero h0, rfl⟩ :
          Algebra.algebraMapSubmonoid O (nonZeroDivisors T)))

end Datum

end GlobalTheory.KeyOriginBC

namespace GlobalTheory.KeyOriginBC

section Datum2

variable {T O : Type} [CommRing T] [CommRing O] [IsLocalRing O] [Algebra T O] [Algebra T[X] O]
  [IsScalarTower T T[X] O]
variable {A A₁ : Type} [CommRing A] [CommRing A₁] (f : A →+* A₁) (i : A →+* T) (i₁ : A₁ →+* T)
variable (EA : Type) [CommRing EA] [Algebra A[X] EA] [Algebra A EA] [IsScalarTower A A[X] EA]
  (QA : Ideal EA) [QA.IsPrime] (jA : Localization.AtPrime QA →+* O)
variable (hcomp : i₁.comp f = i)
  (hj : jA.comp (algebraMap A[X] (Localization.AtPrime QA)) =
      (algebraMap T[X] O).comp (Polynomial.mapRingHom i))

def locBC : Localization.AtPrime QA →+* Loc₁ f i i₁ EA QA jA hcomp hj :=
  IsLocalization.lift (M := QA.primeCompl)
    (g := (algebraMap (Ext f EA) (Loc₁ f i i₁ EA QA jA hcomp hj)).comp (inclE f EA)) (fun y => by
      have hu : IsUnit (glue f i i₁ EA QA jA hcomp hj (inclE f EA y)) := by
        rw [glue_inclE]
        exact (IsLocalization.map_units (Localization.AtPrime QA) y).map jA
      have hz : inclE f EA y ∈ (ideal₁ f i i₁ EA QA jA hcomp hj).primeCompl :=
        fun hy => (IsLocalRing.mem_maximalIdeal _ |>.1 hy) hu
      exact IsLocalization.map_units (Loc₁ f i i₁ EA QA jA hcomp hj) ⟨_, hz⟩)

theorem locBC_algebraMap (x : EA) :
    locBC f i i₁ EA QA jA hcomp hj (algebraMap EA (Localization.AtPrime QA) x) =
      algebraMap (Ext f EA) (Loc₁ f i i₁ EA QA jA hcomp hj) (inclE f EA x) := by
  simp [locBC, IsLocalization.lift_eq]

theorem inclE_algebraMap_base (a : A) :
    inclE f EA (algebraMap A EA a) = algebraMap A₁ (Ext f EA) (f a) := by
  rw [IsScalarTower.algebraMap_apply A A[X] EA]
  have h1 : inclE f EA (algebraMap A[X] EA (algebraMap A A[X] a)) =
      algebraMap A[X] (Ext f EA) (algebraMap A A[X] a) :=
    (Algebra.TensorProduct.includeRight : EA →ₐ[A[X]] Ext f EA).commutes _
  rw [h1, Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.algebraMap_apply]
  congr 1
  show Polynomial.map f (Polynomial.C a) = Polynomial.C (f a)
  simp

theorem locBC_algebraMap_base (a : A) :
    locBC f i i₁ EA QA jA hcomp hj (algebraMap A (Localization.AtPrime QA) a) =
      algebraMap A₁ (Loc₁ f i i₁ EA QA jA hcomp hj) (f a) := by
  rw [IsScalarTower.algebraMap_apply A EA (Localization.AtPrime QA), locBC_algebraMap,
    inclE_algebraMap_base, ← IsScalarTower.algebraMap_apply]

end Datum2

end GlobalTheory.KeyOriginBC

namespace GlobalTheory.KeyOriginBC

section Datum3

variable {T O : Type} [CommRing T] [CommRing O] [IsLocalRing O] [Algebra T O] [Algebra T[X] O]
  [IsScalarTower T T[X] O]
variable {A A₁ : Type} [CommRing A] [CommRing A₁] (f : A →+* A₁) (i : A →+* T) (i₁ : A₁ →+* T)
variable (EA : Type) [CommRing EA] [Algebra A[X] EA] [Algebra A EA] [IsScalarTower A A[X] EA]
  (QA : Ideal EA) [QA.IsPrime] (jA : Localization.AtPrime QA →+* O)
variable (hcomp : i₁.comp f = i)
  (hj : jA.comp (algebraMap A[X] (Localization.AtPrime QA)) =
      (algebraMap T[X] O).comp (Polynomial.mapRingHom i))

def fibBC [Nontrivial A] [IsDomain A₁] (hf : Function.Injective f) :
    GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA) →+*
      GlobalTheory.LocAcyc.GenFib A₁ (Loc₁ f i i₁ EA QA jA hcomp hj) :=
  IsLocalization.lift
    (M := Algebra.algebraMapSubmonoid (Localization.AtPrime QA) (nonZeroDivisors A))
    (g := (algebraMap (Loc₁ f i i₁ EA QA jA hcomp hj)
      (GlobalTheory.LocAcyc.GenFib A₁ (Loc₁ f i i₁ EA QA jA hcomp hj))).comp
        (locBC f i i₁ EA QA jA hcomp hj)) (by
      rintro ⟨_, a, ha, rfl⟩
      simp only [RingHom.coe_comp, Function.comp_apply, locBC_algebraMap_base]
      have h0 : f a ≠ 0 := by
        rw [← map_zero f]; exact fun h => nonZeroDivisors.ne_zero ha (hf h)
      exact IsLocalization.map_units (GlobalTheory.LocAcyc.GenFib A₁ (Loc₁ f i i₁ EA QA jA hcomp hj))
        (⟨algebraMap A₁ _ (f a), f a, mem_nonZeroDivisors_of_ne_zero h0, rfl⟩ :
          Algebra.algebraMapSubmonoid (Loc₁ f i i₁ EA QA jA hcomp hj) (nonZeroDivisors A₁)))

theorem fibBC_algebraMap [Nontrivial A] [IsDomain A₁] (hf : Function.Injective f)
    (r : Localization.AtPrime QA) :
    fibBC f i i₁ EA QA jA hcomp hj hf (algebraMap _ (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) r) =
      algebraMap _ (GlobalTheory.LocAcyc.GenFib A₁ (Loc₁ f i i₁ EA QA jA hcomp hj))
        (locBC f i i₁ EA QA jA hcomp hj r) := by
  simp [fibBC, IsLocalization.lift_eq]

def reduce (ρ : Localization.AtPrime QA →+* A)
    (hρA : ρ.comp (algebraMap A (Localization.AtPrime QA)) = RingHom.id A)
    (hρX : ρ (algebraMap A[X] (Localization.AtPrime QA) Polynomial.X) = 0) : Ext f EA →+* A₁ :=
  lift f EA (Polynomial.evalRingHom 0) (f.comp (ρ.comp (algebraMap EA (Localization.AtPrime QA)))) (by
    apply Polynomial.ringHom_ext
    · intro a
      have h1 : algebraMap EA (Localization.AtPrime QA) (algebraMap A[X] EA (Polynomial.C a)) =
          algebraMap A (Localization.AtPrime QA) a := by
        rw [show (Polynomial.C a : A[X]) = algebraMap A A[X] a from rfl,
          ← IsScalarTower.algebraMap_apply A A[X] EA, ← IsScalarTower.algebraMap_apply]
      have h2 := congrArg (fun w => w a) hρA
      simp only [RingHom.coe_comp, Function.comp_apply, RingHom.id_apply] at h2
      simp [h1, h2]
    · have h1 : algebraMap EA (Localization.AtPrime QA) (algebraMap A[X] EA Polynomial.X) =
          algebraMap A[X] (Localization.AtPrime QA) Polynomial.X := by
        rw [← IsScalarTower.algebraMap_apply]
      simp [h1, hρX])

theorem reduce_tmul (ρ : Localization.AtPrime QA →+* A)
    (hρA : ρ.comp (algebraMap A (Localization.AtPrime QA)) = RingHom.id A)
    (hρX : ρ (algebraMap A[X] (Localization.AtPrime QA) Polynomial.X) = 0) (p : PolyOver f) (x : EA) :
    reduce f EA QA ρ hρA hρX (p ⊗ₜ[A[X]] x) =
      Polynomial.eval 0 (show A₁[X] from p) * f (ρ (algebraMap EA (Localization.AtPrime QA) x)) := by
  simp [reduce, lift_tmul]

def reduceLoc (ρ : Localization.AtPrime QA →+* A)
    (hρA : ρ.comp (algebraMap A (Localization.AtPrime QA)) = RingHom.id A)
    (hρX : ρ (algebraMap A[X] (Localization.AtPrime QA) Polynomial.X) = 0)
    (hunit : ∀ y : (ideal₁ f i i₁ EA QA jA hcomp hj).primeCompl,
      IsUnit (reduce f EA QA ρ hρA hρX y)) : Loc₁ f i i₁ EA QA jA hcomp hj →+* A₁ :=
  IsLocalization.lift hunit

end Datum3

end GlobalTheory.KeyOriginBC

namespace GlobalTheory.KeyOriginBC

theorem comap_maximalIdeal_eq_origin {T O : Type} [CommRing T] [IsLocalRing T] [CommRing O]
    [IsLocalRing O] [Algebra T[X] O] (P : Ideal T[X]) [P.IsPrime] (φ : Localization.AtPrime P →+* O)
    (hφ : φ.comp (algebraMap T[X] _) = algebraMap T[X] O)
    (hsh : GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsStrictHenselisation φ) (hP : P = GlobalTheory.KeyOriginCut.originIdeal T) :
    (maximalIdeal O).comap (algebraMap T[X] O) = GlobalTheory.KeyOriginCut.originIdeal T := by
  haveI : IsLocalHom φ := hsh.2.2.1
  have h1 : (maximalIdeal O).comap φ = maximalIdeal (Localization.AtPrime P) :=
    ((IsLocalRing.local_hom_TFAE φ).out 0 4).mp this
  rw [← hφ, ← Ideal.comap_comap, h1, ← hP]
  exact Localization.AtPrime.comap_maximalIdeal (I := P)

end GlobalTheory.KeyOriginBC

namespace GlobalTheory.KeyOriginBC

theorem reduce_sub_glue_mem {T O : Type} [CommRing T] [CommRing O] [IsLocalRing O] [Algebra T O] [Algebra T[X] O]
  [IsScalarTower T T[X] O]
  {A A₁ : Type} [CommRing A] [CommRing A₁] (f : A →+* A₁) (i : A →+* T) (i₁ : A₁ →+* T)
  (EA : Type) [CommRing EA] [Algebra A[X] EA] [Algebra A EA] [IsScalarTower A A[X] EA]
  (QA : Ideal EA) [QA.IsPrime] (jA : Localization.AtPrime QA →+* O)
  (hcomp : i₁.comp f = i)
  (hj : jA.comp (algebraMap A[X] (Localization.AtPrime QA)) =
      (algebraMap T[X] O).comp (Polynomial.mapRingHom i))
  (ρ : Localization.AtPrime QA →+* A)
  (hρA : ρ.comp (algebraMap A (Localization.AtPrime QA)) = RingHom.id A)
  (hρX : ρ (algebraMap A[X] (Localization.AtPrime QA) Polynomial.X) = 0)
  (hρmod : ∀ x : Localization.AtPrime QA,
      algebraMap T O (i (ρ x)) - jA x ∈ Ideal.span {algebraMap T[X] O Polynomial.X}) :
    ∀ z : Ext f EA, algebraMap T O (i₁ (reduce f EA QA ρ hρA hρX z)) -
      glue f i i₁ EA QA jA hcomp hj z ∈ Ideal.span {algebraMap T[X] O Polynomial.X} := by
  intro z
  set I := Ideal.span {algebraMap T[X] O Polynomial.X}
  rw [← Ideal.Quotient.eq]
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul p x =>
    rw [reduce_tmul, glue_tmul]
    simp only [map_mul]
    have h2 : Ideal.Quotient.mk I (algebraMap T O (i₁ (f (ρ (algebraMap EA (Localization.AtPrime QA) x))))) =
        Ideal.Quotient.mk I (jA (algebraMap EA (Localization.AtPrime QA) x)) := by
      rw [Ideal.Quotient.eq, ← RingHom.comp_apply i₁ f, hcomp]; exact hρmod _
    have h1 : Ideal.Quotient.mk I (algebraMap T O (i₁ (Polynomial.eval 0 (show A₁[X] from p)))) =
        Ideal.Quotient.mk I (algebraMap T[X] O (Polynomial.map i₁ p)) := by
      rw [Ideal.Quotient.eq]
      obtain ⟨r, hr⟩ := Polynomial.X_dvd_sub_C (p := Polynomial.map i₁ (show A₁[X] from p))
      have he : i₁ (Polynomial.eval 0 (show A₁[X] from p)) = Polynomial.eval 0 (Polynomial.map i₁ (show A₁[X] from p)) := by
        rw [Polynomial.eval_map, ← Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval₂_at_zero]
      rw [he, IsScalarTower.algebraMap_apply T T[X] O, Polynomial.algebraMap_apply, Algebra.algebraMap_self,
        RingHom.id_apply, ← map_sub, ← neg_sub, ← Polynomial.coeff_zero_eq_eval_zero, hr, map_neg, map_mul]
      exact I.neg_mem_iff.2 (I.mul_mem_right _ (Ideal.subset_span rfl))
    rw [h1, h2]
  | add x y hx hy => simp only [map_add, hx, hy]
end GlobalTheory.KeyOriginBC

namespace GlobalTheory.KeyOriginBC

theorem isUnit_reduce {T O : Type} [CommRing T] [IsLocalRing T] [CommRing O] [IsLocalRing O] [Algebra T O] [Algebra T[X] O]
  [IsScalarTower T T[X] O]
  {A A₁ : Type} [CommRing A] [CommRing A₁] (f : A →+* A₁) (i : A →+* T) (i₁ : A₁ →+* T)
  (EA : Type) [CommRing EA] [Algebra A[X] EA] [Algebra A EA] [IsScalarTower A A[X] EA]
  (QA : Ideal EA) [QA.IsPrime] (jA : Localization.AtPrime QA →+* O)
  (hcomp : i₁.comp f = i)
  (hj : jA.comp (algebraMap A[X] (Localization.AtPrime QA)) =
      (algebraMap T[X] O).comp (Polynomial.mapRingHom i))
  (ρ : Localization.AtPrime QA →+* A)
  (hρA : ρ.comp (algebraMap A (Localization.AtPrime QA)) = RingHom.id A)
  (hρX : ρ (algebraMap A[X] (Localization.AtPrime QA) Polynomial.X) = 0)
  (hmax : (maximalIdeal O).comap (algebraMap T[X] O) = GlobalTheory.KeyOriginCut.originIdeal T)
  (hloc₁ : IsLocalHom i₁)
  (hcong : ∀ z : Ext f EA, algebraMap T O (i₁ (reduce f EA QA ρ hρA hρX z)) -
      glue f i i₁ EA QA jA hcomp hj z ∈ Ideal.span {algebraMap T[X] O Polynomial.X}) :
    ∀ y : (ideal₁ f i i₁ EA QA jA hcomp hj).primeCompl, IsUnit (reduce f EA QA ρ hρA hρX y) := by
  rintro ⟨y, hy⟩
  have hX : Ideal.span {algebraMap T[X] O Polynomial.X} ≤ maximalIdeal O := by
    rw [Ideal.span_le, Set.singleton_subset_iff]
    show Polynomial.X ∈ (maximalIdeal O).comap (algebraMap T[X] O)
    rw [hmax]; exact Ideal.mem_sup_right (Ideal.subset_span rfl)
  have hg : glue f i i₁ EA QA jA hcomp hj y ∉ maximalIdeal O := hy
  have hr : algebraMap T O (i₁ (reduce f EA QA ρ hρA hρX y)) ∉ maximalIdeal O := by
    intro h
    apply hg
    have := hX (hcong y)
    have h2 := (maximalIdeal O).sub_mem h this
    simpa using h2
  have hT : i₁ (reduce f EA QA ρ hρA hρX y) ∉ maximalIdeal T := by
    intro h; apply hr
    rw [IsScalarTower.algebraMap_apply T T[X] O]
    show Polynomial.C _ ∈ (maximalIdeal O).comap (algebraMap T[X] O)
    rw [hmax]; exact Ideal.mem_sup_left (Ideal.mem_map_of_mem _ h)
  have hu : IsUnit (i₁ (reduce f EA QA ρ hρA hρX y)) := by
    by_contra h'; exact hT ((IsLocalRing.mem_maximalIdeal _).2 h')
  exact isUnit_of_map_unit i₁ _ hu
end GlobalTheory.KeyOriginBC

namespace GlobalTheory.KeyOriginBC

theorem mem_originIdeal_iff {R : Type} [CommRing R] [IsLocalRing R] (p : R[X]) :
    p ∈ GlobalTheory.KeyOriginCut.originIdeal R ↔ p.coeff 0 ∈ maximalIdeal R := by
  unfold GlobalTheory.KeyOriginCut.originIdeal
  constructor
  · intro h
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 h
    rw [Polynomial.coeff_add]
    have hb0 : b.coeff 0 = 0 := by
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hb
      simp
    rw [hb0, add_zero]
    exact (Ideal.mem_map_C_iff.1 ha) 0
  · intro h
    have hp : p = Polynomial.C (p.coeff 0) + (p - Polynomial.C (p.coeff 0)) := by ring
    rw [hp]
    refine Ideal.add_mem _ (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ h)) (Ideal.mem_sup_right ?_)
    obtain ⟨r, hr⟩ := Polynomial.X_dvd_sub_C (p := p)
    rw [hr]; exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)

theorem comap_ideal₁_eq_origin {T O : Type} [CommRing T] [IsLocalRing T] [CommRing O] [IsLocalRing O] [Algebra T O] [Algebra T[X] O]
  [IsScalarTower T T[X] O]
  {A A₁ : Type} [CommRing A] [CommRing A₁] [IsLocalRing A₁] (f : A →+* A₁) (i : A →+* T) (i₁ : A₁ →+* T)
  (EA : Type) [CommRing EA] [Algebra A[X] EA]
  (QA : Ideal EA) [QA.IsPrime] (jA : Localization.AtPrime QA →+* O)
  (hcomp : i₁.comp f = i)
  (hj : jA.comp (algebraMap A[X] (Localization.AtPrime QA)) =
      (algebraMap T[X] O).comp (Polynomial.mapRingHom i))
  (hmax : (maximalIdeal O).comap (algebraMap T[X] O) = GlobalTheory.KeyOriginCut.originIdeal T)
  (hloc₁ : IsLocalHom i₁) :
    (ideal₁ f i i₁ EA QA jA hcomp hj).comap (algebraMap A₁[X] (Ext f EA)) =
      GlobalTheory.KeyOriginCut.originIdeal A₁ := by
  have hg : (glue f i i₁ EA QA jA hcomp hj).comp (algebraMap A₁[X] (Ext f EA)) =
      (algebraMap T[X] O).comp (Polynomial.mapRingHom i₁) := by
    apply RingHom.ext; intro p
    rw [RingHom.comp_apply, Algebra.TensorProduct.algebraMap_apply, glue_tmul]
    change algebraMap T[X] O (Polynomial.map i₁ p) * _ = _
    simp
  unfold ideal₁
  rw [Ideal.comap_comap, hg, ← Ideal.comap_comap, hmax]
  ext p
  rw [Ideal.mem_comap, mem_originIdeal_iff, mem_originIdeal_iff, Polynomial.coe_mapRingHom,
    Polynomial.coeff_map]
  constructor
  · intro h h'
    exact h (h'.map i₁)
  · intro h h'
    exact h (isUnit_of_map_unit i₁ _ h')
end GlobalTheory.KeyOriginBC

namespace GlobalTheory.KeyOriginBC

theorem reduceLoc_sub_locMap_mem {T O : Type} [CommRing T] [CommRing O] [IsLocalRing O] [Algebra T O] [Algebra T[X] O]
  [IsScalarTower T T[X] O]
  {A A₁ : Type} [CommRing A] [CommRing A₁] (f : A →+* A₁) (i : A →+* T) (i₁ : A₁ →+* T)
  (EA : Type) [CommRing EA] [Algebra A[X] EA] [Algebra A EA] [IsScalarTower A A[X] EA]
  (QA : Ideal EA) [QA.IsPrime] (jA : Localization.AtPrime QA →+* O)
  (hcomp : i₁.comp f = i)
  (hj : jA.comp (algebraMap A[X] (Localization.AtPrime QA)) =
      (algebraMap T[X] O).comp (Polynomial.mapRingHom i))
  (ρ : Localization.AtPrime QA →+* A)
  (hρA : ρ.comp (algebraMap A (Localization.AtPrime QA)) = RingHom.id A)
  (hρX : ρ (algebraMap A[X] (Localization.AtPrime QA) Polynomial.X) = 0)
  (hunit : ∀ y : (ideal₁ f i i₁ EA QA jA hcomp hj).primeCompl, IsUnit (reduce f EA QA ρ hρA hρX y))
  (hcong : ∀ z : Ext f EA, algebraMap T O (i₁ (reduce f EA QA ρ hρA hρX z)) -
      glue f i i₁ EA QA jA hcomp hj z ∈ Ideal.span {algebraMap T[X] O Polynomial.X}) :
    ∀ x : Loc₁ f i i₁ EA QA jA hcomp hj,
      algebraMap T O (i₁ (reduceLoc f i i₁ EA QA jA hcomp hj ρ hρA hρX hunit x)) -
        locMap f i i₁ EA QA jA hcomp hj x ∈ Ideal.span {algebraMap T[X] O Polynomial.X} := by
  intro x
  rw [← Ideal.Quotient.eq]
  have key : ((Ideal.Quotient.mk _).comp ((algebraMap T O).comp
      (i₁.comp (reduceLoc f i i₁ EA QA jA hcomp hj ρ hρA hρX hunit))) :
        Loc₁ f i i₁ EA QA jA hcomp hj →+* O ⧸ Ideal.span {algebraMap T[X] O Polynomial.X}) =
      (Ideal.Quotient.mk _).comp (locMap f i i₁ EA QA jA hcomp hj) := by
    apply IsLocalization.ringHom_ext (ideal₁ f i i₁ EA QA jA hcomp hj).primeCompl
    apply RingHom.ext; intro z
    simp only [RingHom.comp_apply, reduceLoc, IsLocalization.lift_eq, locMap_algebraMap]
    exact Ideal.Quotient.eq.2 (hcong z)
  exact congrArg (fun w => w x) key
end GlobalTheory.KeyOriginBC

namespace GlobalTheory.KeyOriginBC

theorem isZTorsor_bc {B B₁ : Type} [CommRing B] [CommRing B₁] (β : B →+* B₁) (D : Type) [CommRing D] [Algebra B D]
    (q : ℕ) (hq : 0 < q) (act : Multiplicative (ZMod q) →* (D ≃ₐ[B] D))
    (h : GlobalTheory.KeyOriginCut.IsZTorsor B D q act) :
    GlobalTheory.KeyOriginCut.IsZTorsor B₁ (BC β D) q (bcAct β D q act) := by
  obtain ⟨act', hact', htor'⟩ := GlobalTheory.LocAcyc.isZModTorsor_baseChange B (Over β) D q hq act h
  have he : act' = bcAct' β D q act := by
    apply MonoidHom.ext; intro g
    apply AlgEquiv.ext; intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul b x => rw [hact']; simp [bcAct', Algebra.TensorProduct.congr_apply]
    | add x y hx hy => simp only [map_add, hx, hy]
  subst he
  exact htor'
end GlobalTheory.KeyOriginBC

namespace GlobalTheory.KeyOriginBC
theorem reduceLoc_locBC {T O : Type} [CommRing T] [CommRing O] [IsLocalRing O] [Algebra T O] [Algebra T[X] O]
  [IsScalarTower T T[X] O]
  {A A₁ : Type} [CommRing A] [CommRing A₁] (f : A →+* A₁) (i : A →+* T) (i₁ : A₁ →+* T)
  (EA : Type) [CommRing EA] [Algebra A[X] EA] [Algebra A EA] [IsScalarTower A A[X] EA]
  (QA : Ideal EA) [QA.IsPrime] (jA : Localization.AtPrime QA →+* O)
  (hcomp : i₁.comp f = i)
  (hj : jA.comp (algebraMap A[X] (Localization.AtPrime QA)) =
      (algebraMap T[X] O).comp (Polynomial.mapRingHom i))
  (ρ : Localization.AtPrime QA →+* A)
  (hρA : ρ.comp (algebraMap A (Localization.AtPrime QA)) = RingHom.id A)
  (hρX : ρ (algebraMap A[X] (Localization.AtPrime QA) Polynomial.X) = 0)
  (hunit : ∀ y : (ideal₁ f i i₁ EA QA jA hcomp hj).primeCompl, IsUnit (reduce f EA QA ρ hρA hρX y)) :
    (reduceLoc f i i₁ EA QA jA hcomp hj ρ hρA hρX hunit).comp (locBC f i i₁ EA QA jA hcomp hj) =
      f.comp ρ := by
  apply IsLocalization.ringHom_ext QA.primeCompl
  apply RingHom.ext; intro x
  simp only [RingHom.comp_apply, locBC_algebraMap, reduceLoc, IsLocalization.lift_eq, inclE_apply,
    reduce_tmul]
  change Polynomial.eval 0 (1 : A₁[X]) * _ = _
  simp

theorem reduceLoc_algebraMap {T O : Type} [CommRing T] [CommRing O] [IsLocalRing O] [Algebra T O] [Algebra T[X] O]
  [IsScalarTower T T[X] O]
  {A A₁ : Type} [CommRing A] [CommRing A₁] (f : A →+* A₁) (i : A →+* T) (i₁ : A₁ →+* T)
  (EA : Type) [CommRing EA] [Algebra A[X] EA] [Algebra A EA] [IsScalarTower A A[X] EA]
  (QA : Ideal EA) [QA.IsPrime] (jA : Localization.AtPrime QA →+* O)
  (hcomp : i₁.comp f = i)
  (hj : jA.comp (algebraMap A[X] (Localization.AtPrime QA)) =
      (algebraMap T[X] O).comp (Polynomial.mapRingHom i))
  (ρ : Localization.AtPrime QA →+* A)
  (hρA : ρ.comp (algebraMap A (Localization.AtPrime QA)) = RingHom.id A)
  (hρX : ρ (algebraMap A[X] (Localization.AtPrime QA) Polynomial.X) = 0)
  (hunit : ∀ y : (ideal₁ f i i₁ EA QA jA hcomp hj).primeCompl, IsUnit (reduce f EA QA ρ hρA hρX y)) :
    (reduceLoc f i i₁ EA QA jA hcomp hj ρ hρA hρX hunit).comp
      (algebraMap A₁ (Loc₁ f i i₁ EA QA jA hcomp hj)) = RingHom.id A₁ := by
  apply RingHom.ext; intro x
  rw [RingHom.comp_apply, IsScalarTower.algebraMap_apply A₁ (Ext f EA) (Loc₁ f i i₁ EA QA jA hcomp hj)]
  simp only [reduceLoc, IsLocalization.lift_eq, algebraMap_ext, reduce_tmul]
  change Polynomial.eval 0 (Polynomial.C x) * _ = _
  simp
end GlobalTheory.KeyOriginBC
