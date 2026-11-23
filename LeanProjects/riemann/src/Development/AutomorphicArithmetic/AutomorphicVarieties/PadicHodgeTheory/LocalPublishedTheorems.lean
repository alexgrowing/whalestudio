import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.FiniteCohomology
import ReciprocityTheory.Hypotheses.GalCoh
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients

noncomputable section

namespace UpperTheory.V.Loc

open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module

structure LocalPublishedTheorems : Prop where
  lfK : Formalism.GaloisCohomology.LocalFinitenessK
  ltK : Formalism.GaloisCohomology.LocalTateDualityK
  leK : Formalism.GaloisCohomology.LocalEulerCharK
  lf : ReciprocityTheory.Gal.LocalFiniteness
  lt : ReciprocityTheory.Gal.LocalTateDuality
  le : ReciprocityTheory.Gal.LocalEulerChar
  bk : GlobalTheory.Published.BlochKatoLocal

section Rep

variable {G A V : Type} [Group G] [CommRing A] [AddCommGroup V] [Module A V]

def twist (κ : G →* Aˣ) (ρ : Representation A G V) : Representation A G V where
  toFun g := ((κ g : Aˣ) : A) • ρ g
  map_one' := by simp
  map_mul' g h := by
    ext x
    simp only [map_mul, Units.val_mul, LinearMap.smul_apply, Module.End.mul_apply, map_smul, mul_smul]
    rw [smul_comm]

def H0dual (χ : G →* Aˣ) (ρ : Representation A G V) : Submodule A (Module.Dual A V) where
  carrier := {f | ∀ g x, f (ρ g x) = ((χ g : Aˣ) : A) * f x}
  zero_mem' := fun g x => by simp
  add_mem' := fun {f f'} hf hf' g x => by simp only [LinearMap.add_apply, hf g x, hf' g x, mul_add]
  smul_mem' := fun c f hf g x => by simp only [LinearMap.smul_apply, hf g x, smul_eq_mul, mul_left_comm]

def FiltBy (ρ : Representation A G V) (S : Set (G →* Aˣ)) : Prop :=
  ∃ (n : ℕ) (F : ℕ → Submodule A V), F 0 = ⊥ ∧ F n = ⊤ ∧ ∀ i < n, F i ≤ F (i + 1) ∧
    ∃ κ ∈ S, ∃ x, F (i + 1) = F i ⊔ Submodule.span A {x} ∧ ∀ g, ρ g x - ((κ g : Aˣ) : A) • x ∈ F i

def UpperTri {n : ℕ} (r : G →* GL (Fin n) A) (κ : Fin n → G →* Aˣ) : Prop :=
  ∀ g, (∀ i j, j < i → (r g : Matrix (Fin n) (Fin n) A) i j = 0) ∧
    ∀ i, (r g : Matrix (Fin n) (Fin n) A) i i = ((κ i g : Aˣ) : A)

def conjGL {n : Type} [Fintype n] [DecidableEq n] (h : GL n A) (r : G →* GL n A) : G →* GL n A :=
  (MulAut.conj h).toMonoidHom.comp r

end Rep

section admitted

variable {l : ℕ} [Fact l.Prime] {G A V : Type} [Group G] [CommRing A] [Algebra ℚ_[l] A] [AddCommGroup V] [Module A V]
  [Module ℚ_[l] V] [IsScalarTower ℚ_[l] A V] (φ : G →* GQ l) (ρ : Representation A G V)

def IsCr : Prop :=
  finrank ℚ_[l] ↥(Dcr φ (resCoef ℚ_[l] ρ)) = (φ.range ⊔ Iq l).index * finrank ℚ_[l] V

def IsDr : Prop :=
  finrank ℚ_[l] ↥(Ddr φ (resCoef ℚ_[l] ρ)) = φ.range.index * finrank ℚ_[l] V

def CrOn (H : Subgroup G) : Prop := IsCr (φ.comp H.subtype) (ρ.comp H.subtype : Representation A H V)

end admitted

def Positive {l : ℕ} [Fact l.Prime] {G E V : Type} [Group G] [TopologicalSpace G] [Field E] [Algebra ℚ_[l] E]
    [Algebra ℤ_[l] E] [AddCommGroup V] [Module E V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] E V]
    (φ : G →* GQ l) (ρ : Representation E G V) : Prop :=
  IsDr φ ρ ∧ FiltBy ρ {κ | ∃ w : ℤ, 1 ≤ w ∧ HasWeight φ κ w}

def QCont (l : ℕ) [Fact l.Prime] {X V : Type} [TopologicalSpace X] [AddCommGroup V] [Module ℚ_[l] V] (f : X → V) :
    Prop := @Continuous X V _ (moduleTopology ℚ_[l] V) f

end UpperTheory.V.Loc
