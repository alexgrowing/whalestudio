import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermOpStmt

noncomputable section

open scoped Classical ComplexConjugate
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Matrix Formalism.L2.SG.TermOp Formalism.L2.SG.HidaSetting

namespace Formalism.L2.SG.NormCut

section ChiN

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

def CongG (x y : VA X.B.I) : Prop := InAt X.B.I X.B.g X.B.g (x - y)

def ChiNBi : Prop :=
  ∀ κ k₁ k₂ : X.B.I.Gf, κ ∈ X.B.I.Kset → k₁ ∈ X.B.I.Kset → k₂ ∈ X.B.I.Kset →
    (∀ a, CongG X (X.B.I.fmat k₁⁻¹ *ᵥ X.f0 a) (X.f0 a)) →
    (∀ a, CongG X (X.B.I.fmat k₂ *ᵥ nxt X.e0 X.z0 a) (nxt X.e0 X.z0 a)) →
    chiN X (k₁ * κ * k₂) = chiN X κ

variable {u : D.what₂.Word} {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

def ColLatK {X : Formalism.L2.SG.HidaSetting.HidaSetting D} (cs : ColSys X u what₂) : Prop :=
  ∀ ρ σ : cs.Cl, cs.lamOf ρ = cs.lamOf σ →
    ((cs.h ρ : X.B.I.Gf) * X.xu u)⁻¹ * ((cs.h σ : X.B.I.Gf) * X.xu u) ∈ X.B.I.Kset

def ColFix (u : D.what₂.Word) : Prop :=
  ∀ h h' : Formalism.L2.SG.PoincareInHH.PoincareSetting.Hfin X u,
    ((h : X.B.I.Gf) * X.xu u)⁻¹ * ((h' : X.B.I.Gf) * X.xu u) ∈ X.B.I.Kset →
      (∀ a, CongG X (X.B.I.fmat (((h : X.B.I.Gf) * X.xu u)⁻¹ * ((h' : X.B.I.Gf) * X.xu u)) *ᵥ X.f0 a) (X.f0 a)) ∧
      (∀ a, CongG X (X.B.I.fmat (((h : X.B.I.Gf) * X.xu u)⁻¹ * ((h' : X.B.I.Gf) * X.xu u)) *ᵥ nxt X.e0 X.z0 a)
        (nxt X.e0 X.z0 a))

theorem mem_Kset_mul {x y : X.B.I.Gf} (hx : x ∈ X.B.I.Kset) (hy : y ∈ X.B.I.Kset) : x * y ∈ X.B.I.Kset := by
  simp only [Formalism.MainNotions.S.AutInst.Kset, Set.mem_setOf_eq] at hx hy ⊢
  exact Subgroup.mul_mem _ hx hy

theorem mem_Kset_inv {x : X.B.I.Gf} (hx : x ∈ X.B.I.Kset) : x⁻¹ ∈ X.B.I.Kset := by
  simp only [Formalism.MainNotions.S.AutInst.Kset, Set.mem_setOf_eq] at hx ⊢
  exact Subgroup.inv_mem _ hx

variable {X}

theorem chiNIndep_of {u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)}
    {F0' : FlagG (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)} {rows' : Finset (Submodule (𝓞 D.host.E) (VS D).V)}
    (cs : ColSys X u what₂) (cs' : ColSys X u' rows') (hB : ChiNBi X) (hL : ColLatK cs) (hL' : ColLatK cs')
    (hF : ColFix X u) (hF' : ColFix X u') : ChiNIndep F0 F0' cs cs' := by
  intro t ρ ρ' hρ hρ' hk
  have hk' : _ ∧ _ := hk
  have hκ : kOf X u u' (cs.h ρ : X.B.I.Gf) (cs'.h ρ' : X.B.I.Gf) t.pt ∈ X.B.I.Kset := hk'.1
  have hbase : cs.lamOf (cs.base t.lam) = cs.lamOf ρ := by rw [cs.base_lam _ t.mem, hρ]
  have hbase' : cs'.lamOf (cs'.base t.lam') = cs'.lamOf ρ' := by rw [cs'.base_lam _ t.mem', hρ']
  have h1 := hL _ _ hbase
  have h1i := hL _ _ hbase.symm
  have h2 := hL' _ _ hbase'.symm
  obtain ⟨hf1, -⟩ := hF _ _ h1i
  obtain ⟨-, hf2⟩ := hF' _ _ h2
  have hf1' : ∀ a, CongG X (X.B.I.fmat (((cs.h (cs.base t.lam) : X.B.I.Gf) * X.xu u)⁻¹ *
      ((cs.h ρ : X.B.I.Gf) * X.xu u))⁻¹ *ᵥ X.f0 a) (X.f0 a) := by
    rw [_root_.mul_inv_rev, inv_inv]
    exact hf1
  have key := hB _ _ _ hκ h1 h2 hf1' hf2
  have heq : kOf X u u' (cs.h (cs.base t.lam) : X.B.I.Gf) (cs'.h (cs'.base t.lam') : X.B.I.Gf) t.pt =
      ((cs.h (cs.base t.lam) : X.B.I.Gf) * X.xu u)⁻¹ * ((cs.h ρ : X.B.I.Gf) * X.xu u) *
        kOf X u u' (cs.h ρ : X.B.I.Gf) (cs'.h ρ' : X.B.I.Gf) t.pt *
        (((cs'.h ρ' : X.B.I.Gf) * X.xu u')⁻¹ * ((cs'.h (cs'.base t.lam') : X.B.I.Gf) * X.xu u')) := by
    simp only [kOf]
    group
  rw [heq, key]

end ChiN

section ColFixPf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

theorem fmat_mul (x y : X.B.I.Gf) : X.B.I.fmat (x * y) = X.B.I.fmat x * X.B.I.fmat y := by
  rfl

theorem fmat_inv_mul (x : X.B.I.Gf) : X.B.I.fmat x⁻¹ * X.B.I.fmat x = 1 := by
  rw [← fmat_mul X, inv_mul_cancel]
  rfl

theorem fixes_mul {x y : X.B.I.Gf} {v : VA X.B.I} (hx : X.B.I.fmat x *ᵥ v = v) (hy : X.B.I.fmat y *ᵥ v = v) :
    X.B.I.fmat (x * y) *ᵥ v = v := by
  rw [fmat_mul X, ← Matrix.mulVec_mulVec, hy, hx]

theorem fixes_inv {x : X.B.I.Gf} {v : VA X.B.I} (hx : X.B.I.fmat x *ᵥ v = v) : X.B.I.fmat x⁻¹ *ᵥ v = v := by
  calc X.B.I.fmat x⁻¹ *ᵥ v = X.B.I.fmat x⁻¹ *ᵥ (X.B.I.fmat x *ᵥ v) := by rw [hx]
    _ = v := by rw [Matrix.mulVec_mulVec, fmat_inv_mul X, Matrix.one_mulVec]

theorem mem_mL_of_Kset {x : X.B.I.Gf} (hx : x ∈ X.B.I.Kset) (m : ℕ) {y : VA X.B.I} (hy : y ∈ mL X.B.I m) :
    X.B.I.fmat x *ᵥ y ∈ mL X.B.I m := by
  have hx' : ∀ z, z ∈ X.B.I.Lf ↔ X.B.I.fmat x *ᵥ z ∈ X.B.I.Lf := hx
  induction hy using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨w, hw, rfl⟩ := hz
    apply Submodule.subset_span
    exact ⟨X.B.I.fmat x *ᵥ w, (hx' w).1 hw, Matrix.mulVec_smul _ _ _⟩
  | zero =>
    rw [Matrix.mulVec_zero]
    exact zero_mem _
  | add a b _ _ ha hb =>
    rw [Matrix.mulVec_add]
    exact add_mem ha hb
  | smul c a _ ha =>
    rw [Matrix.mulVec_smul]
    exact Submodule.smul_mem _ c ha

theorem congG_of_Kset {x : X.B.I.Gf} (hx : x ∈ X.B.I.Kset) {δ : VA X.B.I} (hδ : InAt X.B.I X.B.g X.B.g δ) :
    InAt X.B.I X.B.g X.B.g (X.B.I.fmat x *ᵥ δ - δ) := by
  obtain ⟨c, hc, hcδ⟩ := hδ
  refine ⟨c, hc, ?_⟩
  rw [smul_sub, ← Matrix.mulVec_smul]
  exact sub_mem (mem_mL_of_Kset X hx _ hcδ) hcδ

private theorem congG_fmat_mulVec_of_fixed_of_inAt_sub {k : X.B.I.Gf} (hk : k ∈ X.B.I.Kset) {F v : VA X.B.I}
    (hF : X.B.I.fmat k *ᵥ F = F) (hv : InAt X.B.I X.B.g X.B.g (v - F)) :
    CongG X (X.B.I.fmat k *ᵥ v) v := by
  have h1 := congG_of_Kset X hk hv
  have e : X.B.I.fmat k *ᵥ v - v = X.B.I.fmat k *ᵥ (v - F) - (v - F) := by
    rw [Matrix.mulVec_sub, hF]
    abel
  show InAt X.B.I X.B.g X.B.g (X.B.I.fmat k *ᵥ v - v)
  rw [e]
  exact h1

private theorem inAt_neg' {x : VA X.B.I} (h : InAt X.B.I X.B.g X.B.g x) :
    InAt X.B.I X.B.g X.B.g (-x) := by
  obtain ⟨c, hc, hx⟩ := h
  refine ⟨c, hc, ?_⟩
  rw [smul_neg]
  exact neg_mem hx

theorem column_fixed_holds (u : D.what₂.Word) : ColFix X u := by
  intro h h' hk
  have hm : ((h : X.B.I.Gf)⁻¹ * (h' : X.B.I.Gf)) ∈ Formalism.L2.SG.PoincareInHH.PoincareSetting.Hfin X u :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ h.2) h'.2
  have hfix : ∀ y ∈ Formalism.L2.SG.PoincareInHH.PoincareSetting.fixSet X u,
      X.B.I.fmat ((h : X.B.I.Gf)⁻¹ * (h' : X.B.I.Gf)) *ᵥ incl X.B.I y = incl X.B.I y := hm
  have hk_eq : ((h : X.B.I.Gf) * X.xu u)⁻¹ * ((h' : X.B.I.Gf) * X.xu u) =
      (X.xu u)⁻¹ * ((h : X.B.I.Gf)⁻¹ * (h' : X.B.I.Gf)) * X.xu u := by group
  have hfixes : ∀ y ∈ Formalism.L2.SG.PoincareInHH.PoincareSetting.fixSet X u,
      X.B.I.fmat (X.xu u) *ᵥ incl X.B.I y = incl X.B.I y →
      X.B.I.fmat (((h : X.B.I.Gf) * X.xu u)⁻¹ * ((h' : X.B.I.Gf) * X.xu u)) *ᵥ incl X.B.I y =
        incl X.B.I y := by
    intro y hy hxu
    rw [hk_eq]
    exact fixes_mul X (fixes_mul X (fixes_inv X hxu) (hfix y hy)) hxu
  refine ⟨fun a => ?_, fun a => ?_⟩
  · exact congG_fmat_mulVec_of_fixed_of_inAt_sub X hk
      (hfixes (crdOf X.B.I X.ιE X.bas (X.fY a)) (Or.inl (Or.inr ⟨a, rfl⟩)) (X.xu_fix u a).2)
      (X.basisApprox a).2
  · unfold Formalism.L2.SG.HidaSetting.nxt
    split_ifs with hlt
    · exact congG_fmat_mulVec_of_fixed_of_inAt_sub X hk
        (hfixes (crdOf X.B.I X.ιE X.bas (X.eX ⟨a.1 + 1, hlt⟩)) (Or.inl (Or.inl ⟨_, rfl⟩))
          (X.xu_fix u _).1)
        (X.basisApprox _).1
    · have hz := inAt_neg' X (X.xu_z u)
      rw [neg_sub] at hz
      refine congG_fmat_mulVec_of_fixed_of_inAt_sub X hk ?_ hz
      have e1 : ((h : X.B.I.Gf) * X.xu u)⁻¹ * ((h' : X.B.I.Gf) * X.xu u) * (X.xu u)⁻¹ =
          (X.xu u)⁻¹ * ((h : X.B.I.Gf)⁻¹ * (h' : X.B.I.Gf)) := by group
      rw [Matrix.mulVec_mulVec, ← fmat_mul X, e1, fmat_mul X, ← Matrix.mulVec_mulVec,
        hfix (crdOf X.B.I X.ιE X.bas (X.zu u)) (Or.inr rfl)]

end ColFixPf

section ChiNFinal

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {u u' : D.what₂.Word}
  {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)} {F0' : FlagG (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)}
  {what₂ rows' : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

theorem chiNIndep_of_lat (cs : ColSys X u what₂) (cs' : ColSys X u' rows') (hB : ChiNBi X) (hL : ColLatK cs)
    (hL' : ColLatK cs') : ChiNIndep F0 F0' cs cs' :=
  chiNIndep_of cs cs' hB hL hL' (column_fixed_holds X u) (column_fixed_holds X u')

end ChiNFinal

end Formalism.L2.SG.NormCut
