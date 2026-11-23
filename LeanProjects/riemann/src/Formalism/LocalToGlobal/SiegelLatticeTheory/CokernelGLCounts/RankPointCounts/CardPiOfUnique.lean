import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FrameGlobalPatching

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut Formalism.L2.SG.LsDatumB
  Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount

namespace Formalism.L2.SG.Pf.FrameGlobalPatching

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem card_pi_of_unique {ι : Type*} {α : ι → Type*} (T : Finset ι) (h : ∀ i ∉ T, Nonempty (Unique (α i))) :
    Nat.card (∀ i, α i) = ∏ᶠ i, Nat.card (α i) := by
  haveI : ∀ i : {i // i ∉ T}, Unique (α i) := fun i => (h i.1 i.2).some
  rw [Nat.card_congr (Equiv.piEquivPiSubtypeProd (fun i => i ∈ T) α), Nat.card_prod,
    Nat.card_unique (α := ∀ i : {i // i ∉ T}, α i), mul_one, Nat.card_pi]
  rw [finprod_eq_prod_of_mulSupport_subset (s := T)]
  · exact (Finset.prod_coe_sort T (fun i => Nat.card (α i)))
  · intro i hi
    by_contra hT
    haveI := (h i hT).some
    exact hi Nat.card_unique

def LatPatch : Prop :=
  ∀ (D : D7) (Zd : LocDat D) (Λ₀ : Submodule (𝓞 D.host.E) (VS D).V), Submodule.IsLattice D.host.E Λ₀ →
    ∀ Mf : ∀ p : PlF D, Submodule (Zd.M p).L.O (Vp D p),
      (∀ p, ∃ Λ' : Submodule (𝓞 D.host.E) (VS D).V, Submodule.IsLattice D.host.E Λ' ∧ Mf p = lattice₂ D Zd.M p Λ') →
      {p | Mf p ≠ lattice₂ D Zd.M p Λ₀}.Finite →
      ∃! Λ : Submodule (𝓞 D.host.E) (VS D).V, Submodule.IsLattice D.host.E Λ ∧ ∀ p, lattice₂ D Zd.M p Λ = Mf p

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u))
  (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))

def LocFullC : Prop :=
  ∀ (γ : TermDef.Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1)), EligAt γ w →
  ∀ w' : Point D.host.E (D.R.rS + 1), Gpt (D.mem u).A.T (D.mem u').A.T w' ≠ 0 → kind w' = kind w →
  ∀ Z : PairVal.MatR D, AtMat w' Z →
  ∀ (F'₂ : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E))
    (φ : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (tLoc Zd p γ).f)
    (φ' : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f' ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (locF' Zd p F'₂)),
    ZhatL (lf D F0) F'₂ = Z →
    (∀ p, LsDatumA.LocalCountHypotheses (locH Zd p) (tLoc Zd p γ) (tLoc Zd p γ).f (locF' Zd p F'₂) (φ p) (φ' p)) →
    ∀ p, ∀ M ∈ locSet Zd p (tLoc Zd p γ) (locF' Zd p F'₂) (φ p) (φ' p),
      ∃ Λ' : Submodule (𝓞 D.host.E) (VS D).V, Submodule.IsLattice D.host.E Λ' ∧ M = lattice₂ D Zd.M p Λ'

variable {Zd u u' F0 what₂}

theorem patchC_of (hP : LatPatch) (hL : LocFullC Zd u u' F0 what₂) : PatchC Zd u u' F0 what₂ := by
  intro γ w hγ w' hG' hk Z hZ F'₂ φ φ' hF hT hC
  obtain ⟨Λ₀, hΛ₀, hfin⟩ := hC
  have hfull := hL γ w hγ w' hG' hk Z hZ F'₂ φ φ' hF hT
  set S : ∀ p : PlF D, Set (Submodule (Zd.M p).L.O (Vp D p)) :=
    fun p => locSet Zd p (tLoc Zd p γ) (locF' Zd p F'₂) (φ p) (φ' p) with hS
  have hex : ∀ f : ∀ p, S p, ∃! Λ : Submodule (𝓞 D.host.E) (VS D).V,
      Submodule.IsLattice D.host.E Λ ∧ ∀ p, lattice₂ D Zd.M p Λ = (f p).1 := fun f =>
    hP D Zd Λ₀ hΛ₀ (fun p => (f p).1) (fun p => hfull p _ (f p).2)
      (hfin.subset fun p hp hS' => hp (Set.mem_singleton_iff.1 ((Set.ext_iff.1 hS' (f p).1).1 (f p).2)))
  let e : GlobSet Zd γ F'₂ φ φ' ≃ ∀ p, S p :=
    { toFun := fun Λ p => ⟨lattice₂ D Zd.M p Λ.1, Λ.2.2 p⟩
      invFun := fun f => ⟨(hex f).choose, (hex f).choose_spec.1.1, fun p => by
        rw [(hex f).choose_spec.1.2 p]; exact (f p).2⟩
      left_inv := fun Λ => by
        apply Subtype.ext
        exact (hex _).unique (hex _).choose_spec.1 ⟨Λ.2.1, fun p => rfl⟩
      right_inv := fun f => by
        funext p
        exact Subtype.ext ((hex f).choose_spec.1.2 p) }
  rw [Nat.card_congr e]
  obtain ⟨T, hTs⟩ := hfin.exists_finset
  refine card_pi_of_unique (α := fun p => S p) T (fun p hp => ?_)
  have hsing : S p = {lattice₂ D Zd.M p Λ₀} := by
    by_contra hne
    exact hp ((hTs p).2 hne)
  rw [hsing]
  exact ⟨Set.uniqueSingleton _⟩

end Formalism.L2.SG.Pf.FrameGlobalPatching
