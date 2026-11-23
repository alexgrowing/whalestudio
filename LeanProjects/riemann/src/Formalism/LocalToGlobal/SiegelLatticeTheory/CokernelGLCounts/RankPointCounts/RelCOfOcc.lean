import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NormalInvariants
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.PairingOmegaPrimeZ
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CorankRelation

noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.FourierDecayAlt
  Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.TermOp

set_option linter.dupNamespace false

namespace Formalism.L2.SG.NGCut.NormalVectorPairings

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Defs

variable {D : D7} {X : HidaSetting D} (Y : Full X) (u u' : D.what₂.Word)

def OccT (c : Set (TauC Y u u')) (γ : PN.Pts D.host.E D.R.rS) (t : TauC Y u u') : Prop :=
  t ∈ (Y.tO u u').ngSet ∧ (Y.tO u u').vec t ≠ 0 ∧ clsOf Y u u' t = c ∧ ptPN t = γ

def yT (t : TauC Y u u') : (VS D).V := yv (X.Fu u) t.frame.fl

def yT' (t : TauC Y u u') : (VS D).V := t.lin.symm (yv t.frame.fl (X.Fu u))

def coefA (t0 t : TauC Y u u') : D.host.E :=
  brS (VS D) (yT Y u u' t) (yT Y u u' t0) / brS (VS D) (yT Y u u' t0) (yT Y u u' t0)

def coefA' (t0 t : TauC Y u u') : D.host.E :=
  brS (VS D) (yT' Y u u' t) (yT' Y u u' t0) / brS (VS D) (yT' Y u u' t0) (yT' Y u u' t0)

theorem occ_iff (νL νB : X.B.I.Ginf → Measure X.B.I.Ginf) (ng : PN.Pts D.host.E D.R.rS → ℝ)
    (c : Set (TauC Y u u')) (γ : PN.Pts D.host.E D.R.rS) (ν : NuC D) :
    PN.Occ (Y.tO u u') (NOf2 Y u u' νL νB ng) c γ ν ↔ ∃ t, OccT Y u u' c γ t ∧ nmlOf Y u u' t = ν := by
  constructor
  · rintro ⟨t, h1, h2, h3, h4, h5⟩
    exact ⟨t, ⟨h1, h2, h3, h4⟩, h5⟩
  · rintro ⟨t, ⟨h1, h2, h3, h4⟩, h5⟩
    exact ⟨t, h1, h2, h3, h4, h5⟩

end Defs

section Rel

variable {D : D7} {X : HidaSetting D} (Y : Full X) (u u' : D.what₂.Word)

def RelC (t0 t : TauC Y u u') : Prop :=
  (Y.tO u u').rowOf t = (Y.tO u u').rowOf t0 ∧ (Y.tO u u').s0 t0 t = 1

end Rel

def NmlLine : Prop :=
  ∀ Cg cb Cw cT CT C0 : ℝ, ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
      Ctx Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u' →
      ∀ γ : PN.Pts D.host.E D.R.rS, 1 ≤ NGPt D.host.rdE ((Tu D u : ℕ) * (Tu D u' : ℕ)) γ →
        ∀ t0 t : TauC Y u u', Gt t0 ≠ 0 → Gt t ≠ 0 → ptPN t0 = γ → ptPN t = γ → RelC Y u u' t0 t →
          coefA Y u u' t0 t * star (coefA Y u u' t0 t) = 1 ∧ coefA' Y u u' t0 t * star (coefA' Y u u' t0 t) = 1

def NmlInt : Prop :=
  ∀ Cg cb Cw cT CT C0 : ℝ, ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
      Ctx Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u' →
      ∀ γ : PN.Pts D.host.E D.R.rS, 1 ≤ NGPt D.host.rdE ((Tu D u : ℕ) * (Tu D u' : ℕ)) γ →
        ∀ t0 : TauC Y u u', Gt t0 ≠ 0 → ptPN t0 = γ →
        ∃ J J' : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E, J ≠ 0 ∧ J' ≠ 0 ∧
          (∀ t : TauC Y u u', Gt t ≠ 0 → ptPN t = γ → RelC Y u u' t0 t →
            coefA Y u u' t0 t ∈ J ∧ coefA' Y u u' t0 t ∈ J') ∧
          (1 : ℝ) ≤ ((FractionalIdeal.absNorm J : ℚ) : ℝ) ^ 2 *
            ((Tu D u : ℕ) : ℝ) ^ (2 * D.R.f) * NormalInvariants.PG ((Tu D u : ℕ) * (Tu D u' : ℕ)) γ ^ 2 ∧
          (1 : ℝ) ≤ ((FractionalIdeal.absNorm J' : ℚ) : ℝ) ^ 2 *
            ((Tu D u' : ℕ) : ℝ) ^ (2 * D.R.f) * NormalInvariants.PG ((Tu D u : ℕ) * (Tu D u' : ℕ)) γ ^ 2

def NmlSep : Prop :=
  ∀ Cg cb Cw cT CT C0 : ℝ, ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
      Ctx Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u' →
      ∀ γ : PN.Pts D.host.E D.R.rS, 1 ≤ NGPt D.host.rdE ((Tu D u : ℕ) * (Tu D u' : ℕ)) γ →
        ∀ t0 t1 t2 : TauC Y u u', Gt t0 ≠ 0 → Gt t1 ≠ 0 → Gt t2 ≠ 0 →
          ptPN t0 = γ → ptPN t1 = γ → ptPN t2 = γ → RelC Y u u' t0 t1 → RelC Y u u' t0 t2 →
          coefA Y u u' t0 t1 = coefA Y u u' t0 t2 → coefA' Y u u' t0 t1 = coefA' Y u u' t0 t2 →
          nmlOf Y u u' t1 = nmlOf Y u u' t2

theorem relC_of_occ {D : D7} {X : HidaSetting D} {Y : Full X} {u u' : D.what₂.Word} (hTie : ConcTie X Y)
    {c : Set (TauC Y u u')} {γ : PN.Pts D.host.E D.R.rS} {t0 t : TauC Y u u'}
    (h0 : OccT Y u u' c γ t0) (h : OccT Y u u' c γ t) : RelC Y u u' t0 t := by
  have hrefl := (CorankRelation.corankOne_equivalence_holds D X Y u u' hTie).1 t h.1
  have ht : t ∈ clsOf Y u u' t := ⟨h.1, rfl, hrefl⟩
  rw [h.2.2.1, ← h0.2.2.1] at ht
  exact ⟨ht.2.1, ht.2.2⟩

theorem nmlInv_of (hL : NmlLine) (hI : NmlInt) (hS : NmlSep) : NormalInvariants.NmlInv := by
  intro Cg cb Cw cT CT C0
  obtain ⟨a1, b1, H1⟩ := hL Cg cb Cw cT CT C0
  obtain ⟨a2, b2, H2⟩ := hI Cg cb Cw cT CT C0
  obtain ⟨a3, b3, H3⟩ := hS Cg cb Cw cT CT C0
  refine ⟨max a1 (max a2 a3), max b1 (max b2 b3), fun C' Cl hC hCl D large₂ X Y u u' hctx νL νB ng c γ hocc hNG => ?_⟩
  have hC1 : a1 ≤ C' := le_trans (le_max_left _ _) hC
  have hC2 : a2 ≤ C' := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hC
  have hC3 : a3 ≤ C' := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hC
  have hl1 : b1 ≤ Cl := le_trans (le_max_left _ _) hCl
  have hl2 : b2 ≤ Cl := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hCl
  have hl3 : b3 ≤ Cl := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hCl
  obtain ⟨ν0, hν0⟩ := hocc
  obtain ⟨t0, ht0, -⟩ := (occ_iff Y u u' νL νB ng c γ ν0).1 hν0
  have hTie : ConcTie X Y := hctx.2.2
  have hG0 : Gt t0 ≠ 0 := ht0.1.1
  obtain ⟨J, J', hJ, hJ', hmem, hb, hb'⟩ := H2 C' Cl hC2 hl2 D large₂ X Y u u' hctx γ hNG t0 hG0 ht0.2.2.2
  set pick : NuC D → TauC Y u u' := fun ν =>
    if h : ∃ t, OccT Y u u' c γ t ∧ nmlOf Y u u' t = ν then h.choose else t0 with hpick
  have hpick_spec : ∀ ν, PN.Occ (Y.tO u u') (NOf2 Y u u' νL νB ng) c γ ν →
      OccT Y u u' c γ (pick ν) ∧ nmlOf Y u u' (pick ν) = ν := by
    intro ν hν
    have h := (occ_iff Y u u' νL νB ng c γ ν).1 hν
    simp only [hpick, dif_pos h]
    exact h.choose_spec
  refine ⟨J, J', 1, 1, fun ν => (coefA Y u u' t0 (pick ν), coefA' Y u u' t0 (pick ν)), hJ, hJ', one_ne_zero,
    one_ne_zero, fun ν hν => ?_, fun ν₁ ν₂ h₁ h₂ hκ => ?_, ?_, ?_⟩
  · obtain ⟨hp, -⟩ := hpick_spec ν hν
    obtain ⟨m1, m2⟩ := hmem _ hp.1.1 hp.2.2.2 (relC_of_occ hTie ht0 hp)
    obtain ⟨n1, n2⟩ := H1 C' Cl hC1 hl1 D large₂ X Y u u' hctx γ hNG t0 _ hG0 hp.1.1 ht0.2.2.2 hp.2.2.2
      (relC_of_occ hTie ht0 hp)
    exact ⟨m1, n1, m2, n2⟩
  · obtain ⟨hp1, he1⟩ := hpick_spec ν₁ h₁
    obtain ⟨hp2, he2⟩ := hpick_spec ν₂ h₂
    have hk1 := congrArg Prod.fst hκ
    have hk2 := congrArg Prod.snd hκ
    simp only at hk1 hk2
    rw [← he1, ← he2]
    exact H3 C' Cl hC3 hl3 D large₂ X Y u u' hctx γ hNG t0 _ _ hG0 hp1.1.1 hp2.1.1 ht0.2.2.2 hp1.2.2.2 hp2.2.2.2
      (relC_of_occ hTie ht0 hp1) (relC_of_occ hTie ht0 hp2) hk1 hk2
  · rw [map_one]
    simpa using hb
  · rw [map_one]
    simpa using hb'

end Formalism.L2.SG.NGCut.NormalVectorPairings
