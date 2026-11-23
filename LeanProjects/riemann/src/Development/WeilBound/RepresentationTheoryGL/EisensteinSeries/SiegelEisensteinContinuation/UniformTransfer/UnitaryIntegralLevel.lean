import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.DictInf
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.UniformTransfer.TransferD

noncomputable section

open Matrix

namespace PositivityTheory.RgEis

variable {E R : Type} [Field E] [CommRing R]

namespace Ad

variable (A : Ad E R)

structure IsIdem (e : R) : Prop where
  sq : e * e = e
  σ : A.σ e = e
  O : e ∈ A.O
  φ : ∀ w, A.φ w e = 1

def k0GL (e : R) (ι : Type) [Fintype ι] [DecidableEq ι] : Subgroup (GL ι R) where
  carrier := {k | k ∈ A.kGL ι ∧ e • (k : Matrix ι ι R) = e • 1 ∧ e • ((k⁻¹ : GL ι R) : Matrix ι ι R) = e • 1}
  one_mem' := ⟨one_mem _, by simp, by simp⟩
  mul_mem' := fun {a b} ha hb => ⟨mul_mem ha.1 hb.1, by rw [Units.val_mul, ← smul_mul_assoc, ha.2.1, smul_mul_assoc,
      Matrix.one_mul, hb.2.1], by rw [_root_.mul_inv_rev, Units.val_mul, ← smul_mul_assoc, hb.2.2, smul_mul_assoc,
      Matrix.one_mul, ha.2.2]⟩
  inv_mem' := fun {a} ha => ⟨inv_mem ha.1, ha.2.2, by rw [inv_inv]; exact ha.2.1⟩

def unitaryIntegralLevel (e : R) (ε : ℤˣ) (ι : Type) [Fintype ι] [DecidableEq ι] : Subgroup (A.U ε ι) := (A.k0GL e (ι ⊕ ι)).subgroupOf _

def ChiT (e : R) : Prop := ∀ u : Rˣ, (u : R) ∈ A.O → ((u⁻¹ : Rˣ) : R) ∈ A.O → e * u = e → A.χ u = 1

variable [TopologicalSpace R]

def MirGLU (e : R) : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (i₀ i₁ : ι), 2 ≤ Fintype.card ι → ∃ D : ℂ → ℂ,
    AllRepT (A.kGL ι) (A.k0GL e ι) fun ρ => HasWallU (A.ratGL ι) (A.kGL ι) (stab R {i₁}ᶜ) (stab R {i₀}) 1
      (fun g => A.htGL {i₁}ᶜ g - A.htGL Set.univ g) (A.htGL {i₀})
      (fun g => (Fintype.card ι : ℝ) * A.htGL {i₀} g - A.htGL Set.univ g) ρ D

def SgU (ε : ℤˣ) (ι : Type) [Fintype ι] [DecidableEq ι] (e : R) : Prop :=
  Iwa (A.uQ ε (Set.univ : Set ι)) (A.uK ε ι) → ∃ D : ℂ → ℂ,
    AllRepT (A.uK ε ι) (A.unitaryIntegralLevel e ε ι) fun ρ =>
      HasWallU (A.uΓ ε ι) (A.uK ε ι) (A.uQ ε Set.univ) (A.uQ ε Set.univ) (A.uC ε ι) (A.uH ε Set.univ) (A.uH ε Set.univ)
        (fun g => (Fintype.card ι : ℝ) * A.uH ε Set.univ g) ρ D

end Ad

def LeviSU : Prop := ForAd fun {_} {R} _ _ _ _ A => ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (ε : ℤˣ) (e : R), A.IsIdem e →
  Iwa (A.uQ ε (Set.univ : Set ι)) (A.uK ε ι) →
  ∃ (π : A.uQ ε (Set.univ : Set ι) →* GL ι R) (j : GL ι R →* A.uQ ε (Set.univ : Set ι)),
    IsLevi (A.uΓ ε ι) (A.uK ε ι) (A.uQ ε Set.univ) (A.ratGL ι) (A.kGL ι) π j 1 ∧
    (∀ s : Set ι, IsPull (A.uQ ε Set.univ) (A.uQ ε s ⊓ A.uQ ε Set.univ) (stab R s) π 1 (A.uC ε ι) (A.cGL ι)) ∧
    (∀ s : Set ι, Iwa (A.uQ ε s ⊓ A.uQ ε Set.univ) (A.uK ε ι)) ∧
    (∀ s : Set ι, PullHt (A.uK ε ι) (A.uQ ε Set.univ) π (A.uH ε s) (A.htGL s)) ∧
    ∀ m ∈ A.k0GL e ι, ((j m : A.uQ ε Set.univ) : A.U ε ι) ∈ A.unitaryIntegralLevel e ε ι

open Classical in

def LeviQU : Prop := ForAd fun {_} {R} _ _ _ _ A => ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (ε : ℤˣ) (s : Set ι) (e : R), A.IsIdem e →
  Iwa (A.uQ ε s ⊓ A.uQ ε Set.univ) (A.uK ε ι) →
  ∃ (π : A.uQ ε s →* A.U ε (sᶜ : Set ι)) (j : A.U ε (sᶜ : Set ι) →* A.uQ ε s) (c₀ : A.U ε ι → ℂ),
    IsLevi (A.uΓ ε ι) (A.uK ε ι) (A.uQ ε s) (A.uΓ ε _) (A.uK ε _) π j c₀ ∧
    IsPull (A.uQ ε s) (A.uQ ε s ⊓ A.uQ ε Set.univ) (A.uQ ε Set.univ) π c₀ (A.uC ε ι) (A.uC ε _) ∧
    Iwa (A.uQ ε (Set.univ : Set (sᶜ : Set ι))) (A.uK ε _) ∧
    PullHt (A.uK ε ι) (A.uQ ε s) π (fun g => A.uH ε Set.univ g - A.uH ε s g) (A.uH ε Set.univ) ∧
    ∀ m ∈ A.unitaryIntegralLevel e ε (sᶜ : Set ι), ((j m : A.uQ ε s) : A.U ε ι) ∈ A.unitaryIntegralLevel e ε ι

def SgStepU : Prop := ForAd fun {_} {R} _ _ _ _ A => A.MirGL → ∀ e : R, A.IsIdem e → A.ChiT e → A.MirGLU e →
  ∀ (ε : ℤˣ) (ι : Type) [Fintype ι] [DecidableEq ι], 2 ≤ Fintype.card ι →
    (∀ (κ : Type) [Fintype κ] [DecidableEq κ], 1 ≤ Fintype.card κ → Fintype.card κ < Fintype.card ι → A.SgU ε κ e) →
    A.SgU ε ι e

open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU

def eSF {F : Type} [Field F] [NumberField F] (S : Finset (Pl F)) : AF F :=
  LinearMap.inl F (Ainf F) (Af F) 1 + LinearMap.inr F (Ainf F) (Af F) (∑ v ∈ S, singleFin v 1)

def eCM {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (S : Finset (Pl F)) : AE F E :=
  algebraMap (AF F) (AE F E) (eSF S)

def CMMirU : Prop := ForCM fun {F} {_} _ _ _ _ _ σ χ => ∀ S : Finset (Pl F), (adCM σ χ).MirGLU (eCM S)

def SgOneU : Prop := ForCM fun {F} {_} _ _ _ _ _ σ χ => ∀ S : Finset (Pl F), (adCM σ χ).ChiT (eCM S) →
  ∀ (ε : ℤˣ) (ι : Type) [Fintype ι] [DecidableEq ι], Fintype.card ι = 1 → (adCM σ χ).SgU ε ι (eCM S)

def SgAllU : Prop := ForCM fun {F} {_} _ _ _ _ _ σ χ => ∀ S : Finset (Pl F), (adCM σ χ).ChiT (eCM S) →
  ∀ (ε : ℤˣ) (ι : Type) [Fintype ι] [DecidableEq ι], 1 ≤ Fintype.card ι → (adCM σ χ).SgU ε ι (eCM S)

def EIdem : Prop := ForCM fun {F} {_} _ _ _ _ _ σ χ => ∀ S : Finset (Pl F), (adCM σ χ).IsIdem (eCM S)

def ChiS : Prop := ForCM fun {F} {_} _ _ _ _ _ σ χ => ∀ S₀ : Finset (Pl F), ∃ S, S₀ ⊆ S ∧ (adCM σ χ).ChiT (eCM S)

end PositivityTheory.RgEis
