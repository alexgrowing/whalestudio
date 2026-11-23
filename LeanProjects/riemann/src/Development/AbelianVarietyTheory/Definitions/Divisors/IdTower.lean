import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCorrOpOfAvg

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace GlobalTheory.GalV

structure HTower (k : Type) [Field k] where
  Γ : Type
  Z : Scheme.{0}
  q : Z ⟶ Spec (CommRingCat.of k)
  Y : Γ → Scheme.{0}
  s : ∀ g, Y g ⟶ Z
  t : ∀ g, Y g ⟶ Z
  comm : ∀ g, t g ≫ q = s g ≫ q

variable {k : Type} [Field k] (l : ℕ) [Fact l.Prime] (H : HTower k) (Ω : Type) [Field Ω] [Algebra k Ω]

abbrev HTower.geomZ : Scheme.{0} := GlobalTheory.Et.geom Ω H.q

def HTower.sΩ (g : H.Γ) : GlobalTheory.Et.geom Ω (H.s g ≫ H.q) ⟶ H.geomZ Ω := GlobalTheory.Et.geomMap Ω (H.s g ≫ H.q) (H.s g) rfl

def HTower.tΩ (g : H.Γ) : GlobalTheory.Et.geom Ω (H.s g ≫ H.q) ⟶ H.geomZ Ω := GlobalTheory.Et.geomMap Ω (H.s g ≫ H.q) (H.t g) (H.comm g)

open Classical in

def hop (g : H.Γ) : Htot l (sch.obj (H.geomZ Ω)) →ₗ[ℚ_[l]] Htot l (sch.obj (H.geomZ Ω)) :=
  if h : ∃ T, IsCorrOp l (H.sΩ Ω g) (H.tΩ Ω g) T then h.choose else 0

def V (L : Type) [Field L] [Algebra ℚ_[l] L] {J : Type} (ι : J → H.Γ) (θ : J → L) :
    Submodule L (TensorProduct ℚ_[l] L (Htot l (sch.obj (H.geomZ Ω)))) :=
  genEig L (fun j => hop l H Ω (ι j)) θ

def galV (L : Type) [Field L] [Algebra ℚ_[l] L] (σ : Ω ≃ₐ[k] Ω) :
    TensorProduct ℚ_[l] L (Htot l (sch.obj (H.geomZ Ω))) →ₗ[L] TensorProduct ℚ_[l] L (Htot l (sch.obj (H.geomZ Ω))) :=
  (galTot l Ω H.q σ).baseChange L

def HTower.triv (k : Type) [Field k] : HTower k where
  Γ := Empty
  Z := Spec (CommRingCat.of k)
  q := 𝟙 _
  Y := fun g => g.elim
  s := fun g => g.elim
  t := fun g => g.elim
  comm := fun g => g.elim

def HTower.idTower (k : Type) [Field k] : HTower k where
  Γ := Unit
  Z := Spec (CommRingCat.of k)
  q := 𝟙 _
  Y := fun _ => Spec (CommRingCat.of k)
  s := fun _ => 𝟙 _
  t := fun _ => 𝟙 _
  comm := fun _ => rfl

end GlobalTheory.GalV

end
