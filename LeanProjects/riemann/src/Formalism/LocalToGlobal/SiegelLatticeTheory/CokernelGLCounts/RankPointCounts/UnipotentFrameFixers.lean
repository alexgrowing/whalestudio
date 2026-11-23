import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FrameGlobalPatching

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut Formalism.L2.SG.LsDatumB
  Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem equiv_of_corr {X L S : Type*} (P : X → Prop) (cl : X → S) (G : Set L) (R : X → L → Prop)
    (ha : ∀ x, P x → ∃ y ∈ G, R x y) (hb : ∀ y ∈ G, ∃ x, P x ∧ R x y)
    (hc : ∀ x x' y y', P x → P x' → R x y → R x' y' → (y = y' ↔ cl x = cl x')) :
    Nonempty ({O | ∃ x, P x ∧ O = cl x} ≃ G) := by
  refine ⟨{ toFun := fun O => ⟨(ha _ O.2.choose_spec.1).choose, (ha _ O.2.choose_spec.1).choose_spec.1⟩
            invFun := fun y => ⟨cl (hb y.1 y.2).choose, _, (hb y.1 y.2).choose_spec.1, rfl⟩
            left_inv := ?_
            right_inv := ?_ }⟩
  · rintro ⟨O, hO⟩
    apply Subtype.ext
    have h1 := (ha _ hO.choose_spec.1).choose_spec
    have h2 := (hb _ h1.1).choose_spec
    have h3 := (hc _ _ _ _ hO.choose_spec.1 h2.1 h1.2 h2.2).1 rfl
    show cl (hb _ h1.1).choose = O
    exact (hO.choose_spec.2.trans h3).symm
  · rintro ⟨y, hy⟩
    apply Subtype.ext
    have h2 := (hb y hy).choose_spec
    have hm : ∃ x, P x ∧ cl (hb y hy).choose = cl x := ⟨_, h2.1, rfl⟩
    have h4 := (ha _ hm.choose_spec.1).choose_spec
    show (ha _ hm.choose_spec.1).choose = y
    exact (hc _ _ _ _ hm.choose_spec.1 h2.1 h4.2 h2.2).2 hm.choose_spec.2.symm

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

def unipotentFrameFixers {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) : Set ((VS D).V ≃ₗ[D.host.E] (VS D).V) :=
  {n | n ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT ∧ (∀ j, ∀ x ∈ Xflag (lf D F0) (j + 1), n x - x ∈ Xflag (lf D F0) j) ∧
    (∀ x ∈ orth (VS D) (Xsp (lf D F0)), n x - x ∈ Xsp (lf D F0)) ∧ (∀ a, n (F0.e a) = F0.e a) ∧ n F0.z = F0.z}

def Moves {T' : D.host.E} (n : (VS D).V ≃ₗ[D.host.E] (VS D).V) (F' F'' : LFlag (VS D) D.R.rS T') : Prop :=
  (∀ a, n (F'.fl.e a) = F''.fl.e a) ∧ n F'.fl.z = F''.fl.z

def IsPartner (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D)
    (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) : Prop :=
  F' ∈ CntLocal.EZ (D := D) ((Tu D u' : ℕ) : D.host.E) F0 γ.lam Z ∧
    ∃ γ' : TermDef.Term D u u' F0 what₂, Corank.TermScal D γ γ' ∧
      Rep γ'.lam (lf D F0) (PD D γ'.lam (lf D F0) u') γ'.cls F'

def cls (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D)
    (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) : Set (LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) :=
  {F'' | F'' ∈ CntLocal.EZ (D := D) ((Tu D u' : ℕ) : D.host.E) F0 γ.lam Z ∧ CntLocal.NilradicalFlagMoved F0 γ.lam F' F''}

theorem frPart_eq (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D) :
    frPart γ Z = {O | ∃ F', IsPartner γ Z F' ∧ O = cls γ Z F'} := by
  ext O
  constructor
  · rintro ⟨F', h1, h2, h3⟩
    exact ⟨F', ⟨h1, h2⟩, h3⟩
  · rintro ⟨F', ⟨h1, h2⟩, h3⟩
    exact ⟨F', h1, h2, h3⟩

def RelN (γ : TermDef.Term D u u' F0 what₂) (F'₂ F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E))
    (Λ₂ : Submodule (𝓞 D.host.E) (VS D).V) : Prop :=
  ∃ n ∈ unipotentFrameFixers F0, Moves n F'₂ F' ∧ (n : (VS D).V → (VS D).V) '' (Λ₂ : Set (VS D).V) = (γ.lam : Set (VS D).V)

def Ctx (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D) : Prop :=
  ∃ w : Point D.host.E (D.R.rS + 1), EligAt γ w ∧ ∃ w' : Point D.host.E (D.R.rS + 1),
    Gpt (D.mem u).A.T (D.mem u').A.T w' ≠ 0 ∧ kind w' = kind w ∧ AtMat w' Z

def StarHyp (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D)
    (F'₂ : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E))
    (φ : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (tLoc Zd p γ).f)
    (φ' : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f' ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (locF' Zd p F'₂)) : Prop :=
  ZhatL (lf D F0) F'₂ = Z ∧
    (∀ p, LsDatumA.LocalCountHypotheses (locH Zd p) (tLoc Zd p γ) (tLoc Zd p γ).f (locF' Zd p F'₂) (φ p) (φ' p)) ∧
    ∀ p, φ p = LinearEquiv.refl _ _

def Coherent (γ : TermDef.Term D u u' F0 what₂) (F'₂ : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E))
    (φ : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (tLoc Zd p γ).f)
    (φ' : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f' ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (locF' Zd p F'₂)) : Prop :=
  ∃ Λ₀ : Submodule (𝓞 D.host.E) (VS D).V, Submodule.IsLattice D.host.E Λ₀ ∧
    {p | locSet Zd p (tLoc Zd p γ) (locF' Zd p F'₂) (φ p) (φ' p) ≠ {lattice₂ D Zd.M p Λ₀}}.Finite

variable (u u' F0 what₂)

def StarExists2 : Prop :=
  ∀ (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D), Ctx γ Z →
    ∃ (F'₂ : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E))
      (φ : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (tLoc Zd p γ).f)
      (φ' : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f' ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (locF' Zd p F'₂)),
      StarHyp Zd γ Z F'₂ φ φ' ∧ Coherent Zd γ F'₂ φ φ'

def FwdC : Prop :=
  ∀ (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D), Ctx γ Z →
    ∀ (F'₂ : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E))
      (φ : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (tLoc Zd p γ).f)
      (φ' : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f' ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (locF' Zd p F'₂)),
      StarHyp Zd γ Z F'₂ φ φ' →
      ∀ F', IsPartner γ Z F' → ∃ Λ₂ ∈ GlobSet Zd γ F'₂ φ φ', RelN γ F'₂ F' Λ₂

def BwdC : Prop :=
  ∀ (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D), Ctx γ Z →
    ∀ (F'₂ : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E))
      (φ : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (tLoc Zd p γ).f)
      (φ' : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f' ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (locF' Zd p F'₂)),
      StarHyp Zd γ Z F'₂ φ φ' →
      ∀ Λ₂ ∈ GlobSet Zd γ F'₂ φ φ', ∃ F', IsPartner γ Z F' ∧ RelN γ F'₂ F' Λ₂

def UniqC : Prop :=
  ∀ (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D), Ctx γ Z →
    ∀ (F'₂ : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E))
      (φ : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (tLoc Zd p γ).f)
      (φ' : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f' ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (locF' Zd p F'₂)),
      StarHyp Zd γ Z F'₂ φ φ' →
      ∀ F' F'' Λ₂ Λ₃, IsPartner γ Z F' → IsPartner γ Z F'' → RelN γ F'₂ F' Λ₂ → RelN γ F'₂ F'' Λ₃ →
        (Λ₂ = Λ₃ ↔ cls γ Z F' = cls γ Z F'')

variable {u u' F0 what₂}

theorem fStarC_of_route2 (h1 : StarExists2 Zd u u' F0 what₂) (h2 : FwdC Zd u u' F0 what₂) (h3 : BwdC Zd u u' F0 what₂)
    (h4 : UniqC Zd u u' F0 what₂) : FStarC Zd u u' F0 what₂ := by
  intro γ w hγ w' hG' hk Z hZ
  have hC : Ctx γ Z := ⟨w, hγ, w', hG', hk, hZ⟩
  obtain ⟨F'₂, φ, φ', hS, hCoh⟩ := h1 γ Z hC
  refine ⟨F'₂, φ, φ', hS.1, hS.2.2, hS.2.1, hCoh, ?_⟩
  rw [frPart_eq]
  exact equiv_of_corr (IsPartner γ Z) (cls γ Z) (GlobSet Zd γ F'₂ φ φ') (RelN γ F'₂)
    (h2 γ Z hC F'₂ φ φ' hS) (h3 γ Z hC F'₂ φ φ' hS) (h4 γ Z hC F'₂ φ φ' hS)

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
