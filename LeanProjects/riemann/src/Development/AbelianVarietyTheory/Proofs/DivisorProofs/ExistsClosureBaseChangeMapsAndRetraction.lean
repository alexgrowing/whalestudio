import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComapMaximalIdealEqOrigin
open IsLocalRing Polynomial
open scoped TensorProduct
open GlobalTheory.LocAcyc GlobalTheory.KeyOriginNoeth GlobalTheory.KeyOriginBC

noncomputable section

namespace GlobalTheory.KeyOriginBCMaps

attribute [local instance] closureAlg

def tlift {B P Q Z : Type} [CommRing B] [CommRing P] [CommRing Q] [CommRing Z] [Algebra B P]
    [Algebra B Q] (u : P →+* Z) (v : Q →+* Z) (h : u.comp (algebraMap B P) = v.comp (algebraMap B Q)) :
    P ⊗[B] Q →+* Z :=
  letI : Algebra B Z := (v.comp (algebraMap B Q)).toAlgebra
  (Algebra.TensorProduct.productMap
    (⟨u, fun r => congrArg (fun w : B →+* Z => w r) h⟩ : P →ₐ[B] Z)
    (⟨v, fun _ => rfl⟩ : Q →ₐ[B] Z)).toRingHom

theorem tlift_tmul {B P Q Z : Type} [CommRing B] [CommRing P] [CommRing Q] [CommRing Z] [Algebra B P]
    [Algebra B Q] (u : P →+* Z) (v : Q →+* Z) (h : u.comp (algebraMap B P) = v.comp (algebraMap B Q))
    (p : P) (q : Q) : tlift u v h (p ⊗ₜ[B] q) = u p * v q := by
  simp [tlift, Algebra.TensorProduct.productMap_apply_tmul]

theorem exists_mul_mem_closure (A R DA : Type) [CommRing A] [CommRing R] [Algebra A R] [CommRing DA]
    [Algebra (GenFib A R) DA] [Algebra.IsIntegral (GenFib A R) DA] (d : DA) :
    ∃ a ∈ nonZeroDivisors A, baseHom A R DA (algebraMap A R a) * d ∈ closure A R DA := by
  letI := (baseHom A R DA).toAlgebra
  haveI : IsScalarTower R (GenFib A R) DA := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  obtain ⟨⟨m, hm⟩, hmi⟩ := IsIntegral.exists_multiple_integral_of_isLocalization
    (Algebra.algebraMapSubmonoid R (nonZeroDivisors A)) (Rₘ := GenFib A R) d
    (Algebra.IsIntegral.isIntegral d)
  obtain ⟨a, ha, rfl⟩ := hm
  refine ⟨a, ha, ?_⟩
  rw [Submonoid.smul_def, Algebra.smul_def] at hmi
  exact hmi

def denC (A R DA : Type) [CommRing A] [CommRing R] [Algebra A R] [CommRing DA]
    [Algebra (GenFib A R) DA] : Submonoid (closure A R DA) :=
  (nonZeroDivisors A).map ((algebraMap R (closure A R DA)).comp (algebraMap A R))

theorem isLocalization_closure (A R DA : Type) [CommRing A] [CommRing R] [Algebra A R] [CommRing DA]
    [Algebra (GenFib A R) DA] [Algebra.IsIntegral (GenFib A R) DA] :
    IsLocalization (denC A R DA) DA := by
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨_, a, ha, rfl⟩
    show IsUnit (algebraMap (GenFib A R) DA (algebraMap R (GenFib A R) (algebraMap A R a)))
    exact (IsLocalization.map_units (GenFib A R)
      (⟨algebraMap A R a, a, ha, rfl⟩ : Algebra.algebraMapSubmonoid R (nonZeroDivisors A))).map _
  · intro d
    obtain ⟨a, ha, hd⟩ := exists_mul_mem_closure A R DA d
    refine ⟨(⟨_, hd⟩, ⟨_, a, ha, rfl⟩), ?_⟩
    show d * baseHom A R DA (algebraMap A R a) = baseHom A R DA (algebraMap A R a) * d
    ring
  · intro x y h
    exact ⟨1, by simp only [OneMemClass.coe_one, one_mul]; exact Subtype.ext h⟩

end GlobalTheory.KeyOriginBCMaps

namespace GlobalTheory.KeyOriginBCMaps

attribute [local instance] closureAlg

section Maps

variable {A R A₁ R₁ : Type} [CommRing A] [IsDomain A] [CommRing R] [Algebra A R]
  [CommRing A₁] [IsDomain A₁] [CommRing R₁] [Algebra A₁ R₁]
  {κ : R →+* R₁} {β : GenFib A R →+* GenFib A₁ R₁}
  {DA : Type} [CommRing DA] [Algebra (GenFib A R) DA]
  {S : Type} [CommRing S] [Algebra R₁ S] [Algebra R S] [Algebra R₁ (BC β DA)]

def den (A₁ R₁ S : Type) [CommRing A₁] [CommRing R₁] [Algebra A₁ R₁] [CommRing S] [Algebra R₁ S] :
    Submonoid S :=
  (nonZeroDivisors A₁).map ((algebraMap R₁ S).comp (algebraMap A₁ R₁))

variable (A R A₁ R₁ DA S) in

abbrev EM : Type :=
  Localization (Algebra.algebraMapSubmonoid (S ⊗[R] closure A R DA) (den A₁ R₁ S))

theorem isUnit_EM {m : S} (hm : m ∈ den A₁ R₁ S) : IsUnit (algebraMap S (EM A R A₁ R₁ DA S) m) := by
  rw [IsScalarTower.algebraMap_apply S (S ⊗[R] closure A R DA)]
  exact IsLocalization.map_units (EM A R A₁ R₁ DA S)
    (⟨algebraMap S (S ⊗[R] closure A R DA) m, m, hm, rfl⟩ :
      Algebra.algebraMapSubmonoid (S ⊗[R] closure A R DA) (den A₁ R₁ S))

theorem incl_base (hRS : algebraMap R S = (algebraMap R₁ S).comp κ)
    (hβ : β.comp (algebraMap R (GenFib A R)) = (algebraMap R₁ (GenFib A₁ R₁)).comp κ)
    (hD : algebraMap R₁ (BC β DA) = baseHom A₁ R₁ (BC β DA)) (r : R) :
    (Algebra.TensorProduct.includeRight : BC β DA →ₐ[R₁] S ⊗[R₁] BC β DA)
        (inclD β DA (baseHom A R DA r)) = algebraMap S (S ⊗[R₁] BC β DA) (algebraMap R S r) := by
  have h1 : inclD β DA (baseHom A R DA r) = algebraMap R₁ (BC β DA) (κ r) := by
    rw [hD]
    show ((inclD β DA).comp (algebraMap (GenFib A R) DA)) (algebraMap R (GenFib A R) r) = _
    rw [inclD_algebraMap, RingHom.comp_apply, ← RingHom.comp_apply β, hβ]
    rfl
  rw [h1, AlgHom.commutes, hRS, RingHom.comp_apply, ← IsScalarTower.algebraMap_apply]

theorem inclC_base (hRS : algebraMap R S = (algebraMap R₁ S).comp κ) (r : R) :
    algebraMap (S ⊗[R] closure A R DA) (EM A R A₁ R₁ DA S)
        ((Algebra.TensorProduct.includeRight : closure A R DA →ₐ[R] S ⊗[R] closure A R DA)
          (algebraMap R (closure A R DA) r)) =
      algebraMap S (EM A R A₁ R₁ DA S) (algebraMap R₁ S (κ r)) := by
  rw [AlgHom.commutes, IsScalarTower.algebraMap_apply R S (S ⊗[R] closure A R DA),
    ← IsScalarTower.algebraMap_apply, hRS, RingHom.comp_apply]

end Maps

end GlobalTheory.KeyOriginBCMaps

namespace GlobalTheory.KeyOriginBCMaps

attribute [local instance] closureAlg

section Maps2

variable {A R A₁ R₁ : Type} [CommRing A] [IsDomain A] [CommRing R] [Algebra A R]
  [CommRing A₁] [IsDomain A₁] [CommRing R₁] [Algebra A₁ R₁]
  {κ : R →+* R₁} {β : GenFib A R →+* GenFib A₁ R₁}
  {DA : Type} [CommRing DA] [Algebra (GenFib A R) DA]
  {S : Type} [CommRing S] [Algebra R₁ S] [Algebra R S] [Algebra R₁ (BC β DA)]

theorem phi_compat (hRS : algebraMap R S = (algebraMap R₁ S).comp κ)
    (hβ : β.comp (algebraMap R (GenFib A R)) = (algebraMap R₁ (GenFib A₁ R₁)).comp κ)
    (hD : algebraMap R₁ (BC β DA) = baseHom A₁ R₁ (BC β DA)) :
    (algebraMap S (S ⊗[R₁] BC β DA)).comp (algebraMap R S) =
      (((Algebra.TensorProduct.includeRight : BC β DA →ₐ[R₁] S ⊗[R₁] BC β DA).toRingHom.comp
      (inclD β DA)).comp (closure A R DA).subtype).comp (algebraMap R (closure A R DA)) := by
  apply RingHom.ext; intro r
  simp only [RingHom.comp_apply]
  exact (incl_base hRS hβ hD r).symm

def phi (hRS : algebraMap R S = (algebraMap R₁ S).comp κ)
    (hβ : β.comp (algebraMap R (GenFib A R)) = (algebraMap R₁ (GenFib A₁ R₁)).comp κ)
    (hD : algebraMap R₁ (BC β DA) = baseHom A₁ R₁ (BC β DA)) :
    S ⊗[R] closure A R DA →ₐ[S] S ⊗[R₁] BC β DA where
  toRingHom := tlift (algebraMap S (S ⊗[R₁] BC β DA))
    (((Algebra.TensorProduct.includeRight : BC β DA →ₐ[R₁] S ⊗[R₁] BC β DA).toRingHom.comp
      (inclD β DA)).comp (closure A R DA).subtype) (phi_compat hRS hβ hD)
  commutes' s := by
    simp only [RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe,
      MonoidHom.coe_coe]
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, tlift_tmul]
    simp

theorem phi_tmul (hRS : algebraMap R S = (algebraMap R₁ S).comp κ)
    (hβ : β.comp (algebraMap R (GenFib A R)) = (algebraMap R₁ (GenFib A₁ R₁)).comp κ)
    (hD : algebraMap R₁ (BC β DA) = baseHom A₁ R₁ (BC β DA)) (s : S) (c : closure A R DA) :
    phi hRS hβ hD (s ⊗ₜ[R] c) = s ⊗ₜ[R₁] inclD β DA (c : DA) := by
  change tlift _ _ (phi_compat hRS hβ hD) (s ⊗ₜ[R] c) = _
  rw [tlift_tmul]
  simp [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul]

variable (A R DA S) in

def uOne : GenFib A₁ R₁ →+* EM A R A₁ R₁ DA S :=
  IsLocalization.lift (M := Algebra.algebraMapSubmonoid R₁ (nonZeroDivisors A₁))
    (g := (algebraMap S (EM A R A₁ R₁ DA S)).comp (algebraMap R₁ S)) (by
      rintro ⟨_, a, ha, rfl⟩
      exact isUnit_EM ⟨a, ha, rfl⟩)

end Maps2

end GlobalTheory.KeyOriginBCMaps

namespace GlobalTheory.KeyOriginBCMaps

attribute [local instance] closureAlg

section Maps3

variable {A R A₁ R₁ : Type} [CommRing A] [IsDomain A] [CommRing R] [Algebra A R]
  [CommRing A₁] [IsDomain A₁] [CommRing R₁] [Algebra A₁ R₁] {f : A →+* A₁}
  {κ : R →+* R₁} {β : GenFib A R →+* GenFib A₁ R₁}
  {DA : Type} [CommRing DA] [Algebra (GenFib A R) DA] [Algebra.IsIntegral (GenFib A R) DA]
  {S : Type} [CommRing S] [Algebra R₁ S] [Algebra R S] [Algebra R₁ (BC β DA)]

theorem fa_mem (hf : Function.Injective f) {a : A} (ha : a ∈ nonZeroDivisors A) :
    f a ∈ nonZeroDivisors A₁ :=
  mem_nonZeroDivisors_of_ne_zero (fun h => nonZeroDivisors.ne_zero ha (hf (by rw [h, map_zero])))

variable (S) in

def vOne (hf : Function.Injective f) (hκ : κ.comp (algebraMap A R) = (algebraMap A₁ R₁).comp f)
    (hRS : algebraMap R S = (algebraMap R₁ S).comp κ) : DA →+* EM A R A₁ R₁ DA S :=
  haveI := isLocalization_closure A R DA
  IsLocalization.lift (M := denC A R DA)
    (g := (algebraMap (S ⊗[R] closure A R DA) (EM A R A₁ R₁ DA S)).comp
      (Algebra.TensorProduct.includeRight : closure A R DA →ₐ[R] S ⊗[R] closure A R DA).toRingHom) (by
    rintro ⟨_, a, ha, rfl⟩
    show IsUnit (algebraMap (S ⊗[R] closure A R DA) (EM A R A₁ R₁ DA S)
      ((Algebra.TensorProduct.includeRight : closure A R DA →ₐ[R] S ⊗[R] closure A R DA)
        (algebraMap R _ (algebraMap A R a))))
    rw [inclC_base hRS, ← RingHom.comp_apply κ, hκ, RingHom.comp_apply]
    exact isUnit_EM ⟨f a, fa_mem hf ha, rfl⟩)

theorem vOne_coe (hf : Function.Injective f) (hκ : κ.comp (algebraMap A R) = (algebraMap A₁ R₁).comp f)
    (hRS : algebraMap R S = (algebraMap R₁ S).comp κ) (c : closure A R DA) :
    vOne S hf hκ hRS (c : DA) =
      algebraMap (S ⊗[R] closure A R DA) (EM A R A₁ R₁ DA S) ((1 : S) ⊗ₜ[R] c) := by
  haveI := isLocalization_closure A R DA
  exact IsLocalization.lift_eq (M := denC A R DA) (S := DA) _ c

theorem vD_compat (hf : Function.Injective f) (hκ : κ.comp (algebraMap A R) = (algebraMap A₁ R₁).comp f)
    (hRS : algebraMap R S = (algebraMap R₁ S).comp κ)
    (hβ : β.comp (algebraMap R (GenFib A R)) = (algebraMap R₁ (GenFib A₁ R₁)).comp κ) :
    ((uOne A R DA S : GenFib A₁ R₁ →+* EM A R A₁ R₁ DA S) : Over β →+* EM A R A₁ R₁ DA S).comp
        (algebraMap (GenFib A R) (Over β)) =
      (vOne S hf hκ hRS).comp (algebraMap (GenFib A R) DA) := by
  apply IsLocalization.ringHom_ext (Algebra.algebraMapSubmonoid R (nonZeroDivisors A))
  apply RingHom.ext; intro r
  show uOne A R DA S (β (algebraMap R (GenFib A R) r)) =
    vOne S hf hκ hRS (((algebraMap R (closure A R DA) r : closure A R DA) : DA))
  rw [← RingHom.comp_apply β, hβ, RingHom.comp_apply, vOne_coe]
  have h3 := inclC_base (A := A) (A₁ := A₁) (DA := DA) hRS r
  simp only [Algebra.TensorProduct.includeRight_apply] at h3
  rw [h3]
  exact IsLocalization.lift_eq _ _

end Maps3

end GlobalTheory.KeyOriginBCMaps

namespace GlobalTheory.KeyOriginBCMaps

attribute [local instance] closureAlg

section Maps4

variable {A R A₁ R₁ : Type} [CommRing A] [IsDomain A] [CommRing R] [Algebra A R]
  [CommRing A₁] [IsDomain A₁] [CommRing R₁] [Algebra A₁ R₁] {f : A →+* A₁}
  {κ : R →+* R₁} {β : GenFib A R →+* GenFib A₁ R₁}
  {DA : Type} [CommRing DA] [Algebra (GenFib A R) DA] [Algebra.IsIntegral (GenFib A R) DA]
  {S : Type} [CommRing S] [Algebra R₁ S] [Algebra R S] [Algebra R₁ (BC β DA)]

variable (S) in

def vD (hf : Function.Injective f) (hκ : κ.comp (algebraMap A R) = (algebraMap A₁ R₁).comp f)
    (hRS : algebraMap R S = (algebraMap R₁ S).comp κ)
    (hβ : β.comp (algebraMap R (GenFib A R)) = (algebraMap R₁ (GenFib A₁ R₁)).comp κ) :
    BC β DA →+* EM A R A₁ R₁ DA S :=
  tlift ((uOne A R DA S : GenFib A₁ R₁ →+* EM A R A₁ R₁ DA S) : Over β →+* EM A R A₁ R₁ DA S)
    (vOne S hf hκ hRS) (vD_compat hf hκ hRS hβ)

theorem vD_tmul (hf : Function.Injective f) (hκ : κ.comp (algebraMap A R) = (algebraMap A₁ R₁).comp f)
    (hRS : algebraMap R S = (algebraMap R₁ S).comp κ)
    (hβ : β.comp (algebraMap R (GenFib A R)) = (algebraMap R₁ (GenFib A₁ R₁)).comp κ)
    (g : Over β) (d : DA) :
    vD S hf hκ hRS hβ (g ⊗ₜ[GenFib A R] d) =
      (uOne A R DA S : GenFib A₁ R₁ →+* EM A R A₁ R₁ DA S) g * vOne S hf hκ hRS d :=
  tlift_tmul _ _ _ g d

theorem psi_compat (hf : Function.Injective f) (hκ : κ.comp (algebraMap A R) = (algebraMap A₁ R₁).comp f)
    (hRS : algebraMap R S = (algebraMap R₁ S).comp κ)
    (hβ : β.comp (algebraMap R (GenFib A R)) = (algebraMap R₁ (GenFib A₁ R₁)).comp κ)
    (hD : algebraMap R₁ (BC β DA) = baseHom A₁ R₁ (BC β DA)) :
    (algebraMap S (EM A R A₁ R₁ DA S)).comp (algebraMap R₁ S) =
      (vD S hf hκ hRS hβ).comp (algebraMap R₁ (BC β DA)) := by
  apply RingHom.ext; intro r
  rw [RingHom.comp_apply, RingHom.comp_apply, hD]
  show _ = vD S hf hκ hRS hβ ((show Over β from algebraMap R₁ (GenFib A₁ R₁) r) ⊗ₜ[GenFib A R] (1 : DA))
  rw [vD_tmul, map_one, mul_one]
  show _ = uOne A R DA S (algebraMap R₁ (GenFib A₁ R₁) r)
  unfold uOne
  rw [IsLocalization.lift_eq]
  rfl

variable (S) in

def psi (hf : Function.Injective f) (hκ : κ.comp (algebraMap A R) = (algebraMap A₁ R₁).comp f)
    (hRS : algebraMap R S = (algebraMap R₁ S).comp κ)
    (hβ : β.comp (algebraMap R (GenFib A R)) = (algebraMap R₁ (GenFib A₁ R₁)).comp κ)
    (hD : algebraMap R₁ (BC β DA) = baseHom A₁ R₁ (BC β DA)) :
    S ⊗[R₁] BC β DA →ₐ[S] EM A R A₁ R₁ DA S where
  toRingHom := tlift (algebraMap S (EM A R A₁ R₁ DA S)) (vD S hf hκ hRS hβ) (psi_compat hf hκ hRS hβ hD)
  commutes' s := by
    simp only [RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe,
      MonoidHom.coe_coe]
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, tlift_tmul]
    simp

theorem psi_tmul (hf : Function.Injective f) (hκ : κ.comp (algebraMap A R) = (algebraMap A₁ R₁).comp f)
    (hRS : algebraMap R S = (algebraMap R₁ S).comp κ)
    (hβ : β.comp (algebraMap R (GenFib A R)) = (algebraMap R₁ (GenFib A₁ R₁)).comp κ)
    (hD : algebraMap R₁ (BC β DA) = baseHom A₁ R₁ (BC β DA)) (s : S) (x : BC β DA) :
    psi S hf hκ hRS hβ hD (s ⊗ₜ[R₁] x) = algebraMap S (EM A R A₁ R₁ DA S) s * vD S hf hκ hRS hβ x := by
  change tlift _ _ (psi_compat hf hκ hRS hβ hD) (s ⊗ₜ[R₁] x) = _
  rw [tlift_tmul]

theorem uOne_one :
    ((uOne A R DA S : GenFib A₁ R₁ →+* EM A R A₁ R₁ DA S) : Over β →+* EM A R A₁ R₁ DA S) (1 : Over β) = 1 :=
  map_one _

theorem psi_comp_phi (hf : Function.Injective f) (hκ : κ.comp (algebraMap A R) = (algebraMap A₁ R₁).comp f)
    (hRS : algebraMap R S = (algebraMap R₁ S).comp κ)
    (hβ : β.comp (algebraMap R (GenFib A R)) = (algebraMap R₁ (GenFib A₁ R₁)).comp κ)
    (hD : algebraMap R₁ (BC β DA) = baseHom A₁ R₁ (BC β DA)) :
    (psi S hf hκ hRS hβ hD).comp (phi hRS hβ hD) = IsScalarTower.toAlgHom S _ _ := by
  apply Algebra.TensorProduct.ext'
  intro s c
  rw [AlgHom.comp_apply, phi_tmul, psi_tmul, IsScalarTower.coe_toAlgHom', inclD]
  show _ * vD S hf hκ hRS hβ ((1 : Over β) ⊗ₜ[GenFib A R] (c : DA)) = _
  rw [vD_tmul, uOne_one, one_mul, vOne_coe, IsScalarTower.algebraMap_apply S (S ⊗[R] closure A R DA) (EM A R A₁ R₁ DA S), ← map_mul, Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul]
  simp

end Maps4

end GlobalTheory.KeyOriginBCMaps

namespace GlobalTheory.KeyOriginBCMaps

attribute [local instance] closureAlg

section Maps5

variable {A R A₁ R₁ : Type} [CommRing A] [IsDomain A] [CommRing R] [Algebra A R]
  [CommRing A₁] [IsDomain A₁] [CommRing R₁] [Algebra A₁ R₁] {f : A →+* A₁}
  {κ : R →+* R₁} {β : GenFib A R →+* GenFib A₁ R₁}
  {DA : Type} [CommRing DA] [Algebra (GenFib A R) DA] [Algebra.IsIntegral (GenFib A R) DA]
  {S : Type} [CommRing S] [Algebra R₁ S] [Algebra R S] [Algebra R₁ (BC β DA)]

theorem isUnit_L (hD : algebraMap R₁ (BC β DA) = baseHom A₁ R₁ (BC β DA)) {m : S}
    (hm : m ∈ den A₁ R₁ S) : IsUnit (algebraMap S (S ⊗[R₁] BC β DA) m) := by
  obtain ⟨a, ha, rfl⟩ := hm
  rw [RingHom.comp_apply, ← IsScalarTower.algebraMap_apply R₁ S (S ⊗[R₁] BC β DA),
    ← (Algebra.TensorProduct.includeRight : BC β DA →ₐ[R₁] S ⊗[R₁] BC β DA).commutes, hD]
  exact ((IsLocalization.map_units (GenFib A₁ R₁) (⟨algebraMap A₁ R₁ a, a, ha, rfl⟩ :
    Algebra.algebraMapSubmonoid R₁ (nonZeroDivisors A₁))).map
      (algebraMap (GenFib A₁ R₁) (BC β DA))).map _

theorem algebraMap_L (hD : algebraMap R₁ (BC β DA) = baseHom A₁ R₁ (BC β DA)) (y : R₁) :
    algebraMap S (S ⊗[R₁] BC β DA) (algebraMap R₁ S y) =
      (1 : S) ⊗ₜ[R₁] ((show Over β from algebraMap R₁ (GenFib A₁ R₁) y) ⊗ₜ[GenFib A R] (1 : DA)) := by
  rw [← IsScalarTower.algebraMap_apply,
    ← (Algebra.TensorProduct.includeRight : BC β DA →ₐ[R₁] S ⊗[R₁] BC β DA).commutes, hD]
  rfl

theorem bc_key (hκ : κ.comp (algebraMap A R) = (algebraMap A₁ R₁).comp f)
    (hβ : β.comp (algebraMap R (GenFib A R)) = (algebraMap R₁ (GenFib A₁ R₁)).comp κ)
    (g : Over β) (d : DA) (r₁ : R₁) (a₁ : A₁) (a : A)
    (hg : (show GenFib A₁ R₁ from g) * algebraMap R₁ (GenFib A₁ R₁) (algebraMap A₁ R₁ a₁) =
      algebraMap R₁ (GenFib A₁ R₁) r₁) :
    (g ⊗ₜ[GenFib A R] d) *
        ((show Over β from algebraMap R₁ (GenFib A₁ R₁) (algebraMap A₁ R₁ (a₁ * f a))) ⊗ₜ[GenFib A R] (1 : DA)) =
      ((show Over β from algebraMap R₁ (GenFib A₁ R₁) r₁) ⊗ₜ[GenFib A R] (1 : DA)) *
        ((1 : Over β) ⊗ₜ[GenFib A R] (baseHom A R DA (algebraMap A R a) * d)) := by
  rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  have h1 : (show GenFib A₁ R₁ from g) * algebraMap R₁ (GenFib A₁ R₁) (algebraMap A₁ R₁ (a₁ * f a)) =
      algebraMap R₁ (GenFib A₁ R₁) r₁ * β (algebraMap R (GenFib A R) (algebraMap A R a)) := by
    rw [map_mul, map_mul, ← mul_assoc, hg, ← RingHom.comp_apply β, hβ, RingHom.comp_apply,
      ← RingHom.comp_apply κ, hκ, RingHom.comp_apply]
  have h2 : (show GenFib A₁ R₁ from g) * algebraMap R₁ (GenFib A₁ R₁) (algebraMap A₁ R₁ (a₁ * f a)) =
      (algebraMap R (GenFib A R) (algebraMap A R a)) • (show Over β from algebraMap R₁ (GenFib A₁ R₁) r₁) := by
    rw [h1, Algebra.smul_def, mul_comm]
    rfl
  change (show Over β from (show GenFib A₁ R₁ from g) * algebraMap R₁ (GenFib A₁ R₁) (algebraMap A₁ R₁ (a₁ * f a))) ⊗ₜ[GenFib A R] d = _
  rw [h2, TensorProduct.smul_tmul, Algebra.smul_def]
  congr 1
  exact (mul_one (M := GenFib A₁ R₁) _).symm

end Maps5

end GlobalTheory.KeyOriginBCMaps

namespace GlobalTheory.KeyOriginBCMaps

attribute [local instance] closureAlg

section Maps6

variable {A R A₁ R₁ : Type} [CommRing A] [IsDomain A] [CommRing R] [Algebra A R]
  [CommRing A₁] [IsDomain A₁] [CommRing R₁] [Algebra A₁ R₁] {f : A →+* A₁}
  {κ : R →+* R₁} {β : GenFib A R →+* GenFib A₁ R₁}
  {DA : Type} [CommRing DA] [Algebra (GenFib A R) DA] [Algebra.IsIntegral (GenFib A R) DA]
  {S : Type} [CommRing S] [Algebra R₁ S] [Algebra R S] [Algebra R₁ (BC β DA)]

theorem exists_mul_mem_range (hf : Function.Injective f)
    (hκ : κ.comp (algebraMap A R) = (algebraMap A₁ R₁).comp f)
    (hRS : algebraMap R S = (algebraMap R₁ S).comp κ)
    (hβ : β.comp (algebraMap R (GenFib A R)) = (algebraMap R₁ (GenFib A₁ R₁)).comp κ)
    (hD : algebraMap R₁ (BC β DA) = baseHom A₁ R₁ (BC β DA)) (x : S ⊗[R₁] BC β DA) :
    ∃ m ∈ den A₁ R₁ S, x * algebraMap S (S ⊗[R₁] BC β DA) m ∈ (phi hRS hβ hD).range := by
  have hrange : ∀ s : S, algebraMap S (S ⊗[R₁] BC β DA) s ∈ (phi hRS hβ hD).range :=
    fun s => (phi hRS hβ hD).range.algebraMap_mem s
  have hadd : ∀ x y : S ⊗[R₁] BC β DA,
      (∃ m ∈ den A₁ R₁ S, x * algebraMap S (S ⊗[R₁] BC β DA) m ∈ (phi hRS hβ hD).range) →
      (∃ m ∈ den A₁ R₁ S, y * algebraMap S (S ⊗[R₁] BC β DA) m ∈ (phi hRS hβ hD).range) →
      (∃ m ∈ den A₁ R₁ S, (x + y) * algebraMap S (S ⊗[R₁] BC β DA) m ∈ (phi hRS hβ hD).range) := by
    rintro x y ⟨m, hm, hx⟩ ⟨n, hn, hy⟩
    refine ⟨m * n, mul_mem hm hn, ?_⟩
    have e : (x + y) * algebraMap S (S ⊗[R₁] BC β DA) (m * n) =
        (x * algebraMap S _ m) * algebraMap S _ n + (y * algebraMap S _ n) * algebraMap S _ m := by
      rw [map_mul]; ring
    rw [e]
    exact add_mem (mul_mem hx (hrange n)) (mul_mem hy (hrange m))
  have hzero : ∃ m ∈ den A₁ R₁ S, (0 : S ⊗[R₁] BC β DA) * algebraMap S _ m ∈ (phi hRS hβ hD).range :=
    ⟨1, one_mem _, by rw [zero_mul]; exact zero_mem _⟩
  have hkey : ∀ (g : Over β) (d : DA), ∃ m ∈ den A₁ R₁ S,
      (1 : S) ⊗ₜ[R₁] (g ⊗ₜ[GenFib A R] d) * algebraMap S (S ⊗[R₁] BC β DA) m ∈
        (phi hRS hβ hD).range := by
    intro g d
    obtain ⟨⟨r₁, _, a₁, ha₁, rfl⟩, hg⟩ := IsLocalization.surj
      (Algebra.algebraMapSubmonoid R₁ (nonZeroDivisors A₁)) (show GenFib A₁ R₁ from g)
    obtain ⟨a, ha, hd⟩ := exists_mul_mem_closure A R DA d
    refine ⟨algebraMap R₁ S (algebraMap A₁ R₁ (a₁ * f a)),
      ⟨a₁ * f a, mul_mem ha₁ (fa_mem hf ha), rfl⟩,
      ⟨algebraMap R₁ S r₁ ⊗ₜ[R] (⟨_, hd⟩ : closure A R DA), ?_⟩⟩
    show phi hRS hβ hD _ = _
    rw [phi_tmul]
    have hl : algebraMap R₁ S r₁ ⊗ₜ[R₁] inclD β DA (baseHom A R DA (algebraMap A R a) * d) =
        algebraMap S (S ⊗[R₁] BC β DA) (algebraMap R₁ S r₁) *
          ((1 : S) ⊗ₜ[R₁] ((1 : Over β) ⊗ₜ[GenFib A R] (baseHom A R DA (algebraMap A R a) * d))) := by
      rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
        Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      rfl
    have e2 : (1 : S) ⊗ₜ[R₁] (g ⊗ₜ[GenFib A R] d) *
        algebraMap S (S ⊗[R₁] BC β DA) (algebraMap R₁ S (algebraMap A₁ R₁ (a₁ * f a))) =
        (1 : S) ⊗ₜ[R₁] ((g ⊗ₜ[GenFib A R] d) *
          ((show Over β from algebraMap R₁ (GenFib A₁ R₁) (algebraMap A₁ R₁ (a₁ * f a))) ⊗ₜ[GenFib A R]
            (1 : DA))) := by
      rw [algebraMap_L hD, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    have e3 : algebraMap S (S ⊗[R₁] BC β DA) (algebraMap R₁ S r₁) *
          ((1 : S) ⊗ₜ[R₁] ((1 : Over β) ⊗ₜ[GenFib A R] (baseHom A R DA (algebraMap A R a) * d))) =
        (1 : S) ⊗ₜ[R₁] (((show Over β from algebraMap R₁ (GenFib A₁ R₁) r₁) ⊗ₜ[GenFib A R] (1 : DA)) *
          ((1 : Over β) ⊗ₜ[GenFib A R] (baseHom A R DA (algebraMap A R a) * d))) := by
      rw [algebraMap_L hD, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    rw [hl, e3, e2, bc_key hκ hβ g d r₁ a₁ a hg]
  have hD1 : ∀ y : BC β DA, ∃ m ∈ den A₁ R₁ S,
      (1 : S) ⊗ₜ[R₁] y * algebraMap S (S ⊗[R₁] BC β DA) m ∈ (phi hRS hβ hD).range := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simpa only [TensorProduct.tmul_zero] using hzero
    | tmul g d => exact hkey g d
    | add y z hy hz => rw [TensorProduct.tmul_add]; exact hadd _ _ hy hz
  induction x using TensorProduct.induction_on with
  | zero => exact hzero
  | tmul s y =>
    obtain ⟨m, hm, h⟩ := hD1 y
    refine ⟨m, hm, ?_⟩
    have e : s ⊗ₜ[R₁] y * algebraMap S (S ⊗[R₁] BC β DA) m =
        algebraMap S _ s * ((1 : S) ⊗ₜ[R₁] y * algebraMap S _ m) := by
      simp only [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
        Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [e]
    exact mul_mem (hrange s) h
  | add x y hx hy => exact hadd _ _ hx hy

end Maps6

theorem exists_bc_closure_maps : ∀ (A R A₁ R₁ : Type) [CommRing A] [IsDomain A] [CommRing R] [Algebra A R]
    [CommRing A₁] [IsDomain A₁] [CommRing R₁] [Algebra A₁ R₁] (f : A →+* A₁), Function.Injective f →
    ∀ (κ : R →+* R₁), κ.comp (algebraMap A R) = (algebraMap A₁ R₁).comp f →
    ∀ (β : GenFib A R →+* GenFib A₁ R₁),
    β.comp (algebraMap R (GenFib A R)) = (algebraMap R₁ (GenFib A₁ R₁)).comp κ →
    ∀ (DA : Type) [CommRing DA] [Algebra (GenFib A R) DA] [Algebra.IsIntegral (GenFib A R) DA]
    (S : Type) [CommRing S] [Algebra R₁ S],
    letI := closureAlg A R DA
    letI : Algebra R S := ((algebraMap R₁ S).comp κ).toAlgebra
    letI : Algebra R₁ (BC β DA) := (baseHom A₁ R₁ (BC β DA)).toAlgebra
    ∃ (φ : S ⊗[R] closure A R DA →ₐ[S] S ⊗[R₁] BC β DA)
      (ψ : S ⊗[R₁] BC β DA →ₐ[S] Localization (Algebra.algebraMapSubmonoid (S ⊗[R] closure A R DA)
          ((nonZeroDivisors A₁).map ((algebraMap R₁ S).comp (algebraMap A₁ R₁))))),
      ψ.comp φ = IsScalarTower.toAlgHom S _ _ ∧
      (∀ m ∈ (nonZeroDivisors A₁).map ((algebraMap R₁ S).comp (algebraMap A₁ R₁)),
        IsUnit (algebraMap S (S ⊗[R₁] BC β DA) m)) ∧
      ∀ x : S ⊗[R₁] BC β DA, ∃ m ∈ (nonZeroDivisors A₁).map ((algebraMap R₁ S).comp (algebraMap A₁ R₁)),
        x * algebraMap S _ m ∈ φ.range := by
  intro A R A₁ R₁ _ _ _ _ _ _ _ _ f hf κ hκ β hβ DA _ _ _ S _ _
  letI : Algebra R S := ((algebraMap R₁ S).comp κ).toAlgebra
  letI : Algebra R₁ (BC β DA) := (baseHom A₁ R₁ (BC β DA)).toAlgebra
  exact ⟨phi rfl hβ rfl, psi S hf hκ rfl hβ rfl, psi_comp_phi hf hκ rfl hβ rfl,
    fun m hm => isUnit_L rfl hm, exists_mul_mem_range hf hκ rfl hβ rfl⟩

end GlobalTheory.KeyOriginBCMaps
