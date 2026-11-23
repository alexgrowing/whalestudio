import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Formalism.LocalToGlobal.GaloisLevelStructure.Checks

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting
  NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.AutQuot

variable (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ)

structure AlgWtM where
  d : ℕ
  ρ : Representation ℂ (GQ L n) (Fin d → ℂ)
  alg : IsAlgWeight L n ρ
  irr : ρ.IsIrreducible

structure AutRepM extends AlgWtM L n where
  S : Submodule ℂ (GAf L n → (Fin d → ℂ))
  irrS : NG.IsIrrRep ρ S

variable {L n}

def AlgWtM.toAlgWt (m : AlgWtM L n) : NG.AlgWt L n := ⟨Fin m.d → ℂ, m.ρ, m.alg, m.irr⟩

def AutRepM.toAutRep (m : AutRepM L n) : NG.AutRep L n := ⟨m.toAlgWtM.toAlgWt, m.S, m.irrS⟩

variable (L n)

def AUq : Type := {X : Set (AutRepM L n) // ∃ π : NG.AutRep L n, X = {m | π.Iso m.toAutRep}}

def WtQ : Type := {X : Set (AlgWtM L n) // ∃ a : NG.AlgWt L n, X = {m | a.Iso m.toAlgWt}}

variable {L n}

def clsA (π : NG.AutRep L n) : AUq L n := ⟨{m | π.Iso m.toAutRep}, π, rfl⟩

def clsW (a : NG.AlgWt L n) : WtQ L n := ⟨{m | a.Iso m.toAlgWt}, a, rfl⟩

def AUq.rep (X : AUq L n) : NG.AutRep L n := X.2.choose

def WtQ.rep (X : WtQ L n) : NG.AlgWt L n := X.2.choose

theorem AUq.cls_rep (X : AUq L n) : clsA X.rep = X := Subtype.ext X.2.choose_spec.symm

theorem WtQ.cls_rep (X : WtQ L n) : clsW X.rep = X := Subtype.ext X.2.choose_spec.symm

section
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

def LocAt (π : NG.AutRep L n) (w : HeightOneSpectrum (𝓞 L)) (x : GlobalTheory.LocGL.IrrGL (w.adicCompletion L)) : Prop :=
  ∃ (s : SplitPlace L) (σ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (s.w.adicCompletion L))) (h : s.w = w),
    IsLocS π.S s σ ∧ HEq (GlobalTheory.LocLanglands.cls σ) x

end

open Classical in

def hwOf (a : NG.AlgWt L n) (τ : L →+* ℂ) : Fin n → ℤ :=
  if h : ∃ lam, a.HWAt τ lam ∧ Antitone lam then h.choose else 0

theorem hwOf_antitone (a : NG.AlgWt L n) (τ : L →+* ℂ) : Antitone (hwOf a τ) := by
  unfold hwOf
  split_ifs with h
  · exact h.choose_spec.2
  · exact fun _ _ _ => le_rfl

open Classical in

def satOf (π : NG.AutRep L n) (w : HeightOneSpectrum (𝓞 L)) : Multiset ℂ :=
  if h : ∃ (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (Dv : InertDatum L n v w) (α : Fin (n / 2) → ℂ),
      NG.OverPl w v ∧ NG.SatAt π Dv α
  then Finset.univ.val.map h.choose_spec.choose_spec.choose else Multiset.replicate (n / 2) 1

theorem satOf_card (π : NG.AutRep L n) (w : HeightOneSpectrum (𝓞 L)) : Multiset.card (satOf π w) = n / 2 := by
  unfold satOf
  split_ifs <;> simp

theorem infOf_card (lam : Fin n → ℤ) : Multiset.card (NG.infOf lam) = n := by
  simp [NG.infOf]

theorem infOf_nodup_alg {lam : Fin n → ℤ} (hl : Antitone lam) : (NG.infOf lam).Nodup ∧
    ∀ x ∈ NG.infOf lam, ∃ k : ℤ, x = (k : ℂ) + ((n : ℂ) - 1) / 2 := by
  refine ⟨?_, ?_⟩
  · unfold NG.infOf
    refine Multiset.Nodup.map_on (fun i _ j _ hij => ?_) Finset.univ.nodup
    have h1 : ((lam i - (i : ℕ) : ℤ) : ℂ) = ((lam j - (j : ℕ) : ℤ) : ℂ) := by
      push_cast; linear_combination hij
    have h2 : lam i - (i : ℕ) = lam j - (j : ℕ) := by exact_mod_cast h1
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · have := hl (le_of_lt h); have : (i : ℕ) < (j : ℕ) := h; omega
    · have := hl (le_of_lt h); have : (j : ℕ) < (i : ℕ) := h; omega
  · intro x hx
    unfold NG.infOf at hx
    obtain ⟨i, -, rfl⟩ := Multiset.mem_map.1 hx
    exact ⟨lam i - (i : ℕ), by push_cast; ring⟩

end GlobalTheory.AutQuot

end

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting
  NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.AutQuot

variable (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut)

open Classical in

def locOf (π : NG.AutRep D.host.E D.R.nV) (w : PlE D.host) : D.naut.LP w :=
  if h : ∃ x, LocAt π w x then (T.e w).symm (GlobalTheory.CuspRep.ParLaws.locRec hL (D.nd.plOm.2 w) h.choose)
  else D.naut.lpZero w

open Classical in

def wtOf (π : NG.AutRep D.host.E D.R.nV) : WtQ D.host.E D.R.nV :=
  if h : ∃ b, π.toAlgWt.IsDual b then clsW h.choose else clsW π.toAlgWt

set_option synthInstance.maxHeartbeats 400000 in

def nbcOf (hE : IsEmpty D.nd.Loc) : NBC D.naut where
  AU := fun _ => AUq D.host.E D.R.nV
  multAU := fun _ X => X.rep.mult
  sphAU := fun _ X w => ∃ v, NG.OverPl w v ∧ X.rep.SphAt v
  locAU := fun _ X w => locOf hL D T X.rep w
  satAU := fun _ X w => satOf X.rep w
  satAU_card := fun _ X w => satOf_card X.rep w
  Wt := fun _ => WtQ D.host.E D.R.nV
  infW := fun _ Y τ => NG.infOf (hwOf Y.rep τ)
  infW_card := fun _ Y τ => infOf_card _
  wtAU := fun _ X => wtOf D X.rep
  infW_alg := fun _ Y τ => infOf_nodup_alg (hwOf_antitone Y.rep τ)
  embAV := fun i => isEmptyElim i
  embAV_inj := fun i => isEmptyElim i
  embAV_loc := fun i => isEmptyElim i
  embAV_sat := fun i => isEmptyElim i
  embAV_sph := fun i => isEmptyElim i
  embAV_inf := fun i => isEmptyElim i

end GlobalTheory.AutQuot

end
