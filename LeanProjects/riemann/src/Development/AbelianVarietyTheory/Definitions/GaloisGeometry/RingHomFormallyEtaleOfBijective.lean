import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Subsingleton
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ReductionUniformizerPoint

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (RingAct)
open TopologicalSpace
open scoped CategoryTheory.Obj NumberField
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.IwLevel

section Etale

variable {X Y : Scheme.{0}}

def EtaleAtPt (f : X ⟶ Y) (x : X) : Prop := (f.stalkMap x).hom.FormallyEtale

theorem ringHom_formallyEtale_of_bijective {A B : Type} [CommRing A] [CommRing B] (g : A →+* B)
    (hg : Function.Bijective g) : g.FormallyEtale := by
  letI := g.toAlgebra
  show Algebra.FormallyEtale A B
  exact Algebra.FormallyEtale.of_equiv (AlgEquiv.ofBijective (Algebra.ofId A B) hg)

theorem etaleAtPt_of_isIso (f : X ⟶ Y) [IsIso f] (x : X) : EtaleAtPt f x := by
  unfold EtaleAtPt
  exact ringHom_formallyEtale_of_bijective _ (ConcreteCategory.bijective_of_isIso (f.stalkMap x))

end Etale

section Strata

variable {S : Scheme.{0}} {O : Type} [Ring O] {A : Over S} [GrpObj A] [IsCommMonObj A] {ρ : RingAct A O}
  {𝔴 : Ideal O} {d n : ℕ} (C : Chain ρ 𝔴 d n)

def nonEtaleLocus (j : Fin n) : Set (C.B j.castSucc).left :=
  {x | ¬ EtaleAtPt (C.φ j).left x}

def stratSet (j : Fin n) : Set S :=
  closure ((C.B j.castSucc).hom.base '' nonEtaleLocus C j)

theorem isClosed_stratSet (j : Fin n) : IsClosed (stratSet C j) := isClosed_closure

def stratClosed (j : Fin n) : Closeds S := ⟨stratSet C j, isClosed_stratSet C j⟩

def stratIdeal (j : Fin n) : S.IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal (stratClosed C j)

@[simp] theorem coe_support_stratIdeal (j : Fin n) : ((stratIdeal C j).support : Set S) = stratSet C j :=
  Scheme.IdealSheafData.coe_support_vanishingIdeal _

theorem stratSet_eq_empty_of_isIso (j : Fin n) [IsIso (C.φ j)] : stratSet C j = ∅ := by
  have : IsIso (C.φ j).left := inferInstanceAs (IsIso ((Over.forget S).map (C.φ j)))
  have h : nonEtaleLocus C j = ∅ := Set.eq_empty_iff_forall_notMem.2 fun x hx => hx (etaleAtPt_of_isIso _ x)
  rw [stratSet, h, Set.image_empty, closure_empty]

theorem stratIdeal_eq_top_of_isIso (j : Fin n) [IsIso (C.φ j)] : stratIdeal C j = ⊤ := by
  have : stratClosed C j = ⊥ := Closeds.ext (stratSet_eq_empty_of_isIso C j)
  rw [stratIdeal, this, Scheme.IdealSheafData.vanishingIdeal_bot]

def openStratum (T : Finset (Fin n)) : Set S := {s | ∀ j, s ∈ stratSet C j ↔ j ∈ T}

def openStratumOpens (T : Finset (Fin n)) : (GlobalTheory.Strata.Y (stratIdeal C) T).Opens :=
  ⟨(GlobalTheory.Strata.Yι (stratIdeal C) T).base ⁻¹' (⋂ j ∈ Tᶜ, (stratSet C j)ᶜ),
    (isOpen_biInter_finset fun j _ => (isClosed_stratSet C j).isOpen_compl).preimage
      (GlobalTheory.Strata.Yι (stratIdeal C) T).base.hom.continuous⟩

end Strata

section Rep

open GlobalTheory.UPel.HT

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ} {w : Ideal (𝓞 D.F)}

abbrev HTIwRep.strat (M : HTIwRep b N w) : Fin D.n → M.X.IdealSheafData := stratIdeal M.univC

abbrev HTIwRep.openStratum (M : HTIwRep b N w) (T : Finset (Fin D.n)) : Set M.X := IwLevel.openStratum M.univC T

end Rep

section Basic₂

variable {S : Scheme.{0}} {O : Type} [Ring O] {A : Over S} [GrpObj A] [IsCommMonObj A]

example (hA : IsAbelianScheme A) (ρ : RingAct A O) (h : IsIsogDeg (ρ.act 1) 1) (n : ℕ) (j : Fin n) :
    stratSet (powChain hA ρ 1 (fun _ => by simp) h n) j = ∅ := by
  haveI : IsIso ((powChain hA ρ 1 (fun _ => by simp) h n).φ j) := by
    show IsIso (ρ.act 1); rw [ρ.map_one]; infer_instance
  exact stratSet_eq_empty_of_isIso _ j

example (hA : IsAbelianScheme A) (ρ : RingAct A O) (h : IsIsogDeg (ρ.act 1) 1) (n : ℕ) (T : Finset (Fin n)) :
    openStratum (powChain hA ρ 1 (fun _ => by simp) h n) T = if T = ∅ then Set.univ else ∅ := by
  have e : ∀ j, stratSet (powChain hA ρ 1 (fun _ => by simp) h n) j = ∅ := fun j => by
    haveI : IsIso ((powChain hA ρ 1 (fun _ => by simp) h n).φ j) := by
      show IsIso (ρ.act 1); rw [ρ.map_one]; infer_instance
    exact stratSet_eq_empty_of_isIso _ j
  ext s
  simp only [openStratum, e, Set.mem_empty_iff_false, false_iff, Set.mem_setOf_eq]
  split_ifs with hT
  · simp [hT]
  · obtain ⟨j, hj⟩ := Finset.nonempty_iff_ne_empty.2 hT
    simp only [Set.mem_empty_iff_false, iff_false, not_forall, not_not]
    exact ⟨j, hj⟩

example (hA : IsAbelianScheme A) (ρ : RingAct A O) (h : IsIsogDeg (ρ.act 1) 1) :
    stratIdeal (powChain hA ρ 1 (fun _ => by simp) h 1) 0 = ⊤ := by
  haveI : IsIso ((powChain hA ρ 1 (fun _ => by simp) h 1).φ 0) := by
    show IsIso (ρ.act 1); rw [ρ.map_one]; infer_instance
  exact stratIdeal_eq_top_of_isIso _ 0

end Basic₂

end GlobalTheory.IwLevel
