import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermOp

noncomputable section

open scoped Classical ComplexConjugate TensorProduct
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Matrix

namespace Formalism.L2.SG.TermOp

section Stmt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.L2.SG.PoincareInHH.PoincareSetting

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {u u' : D.what₂.Word}
  {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)} {F0' : FlagG (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)}
  {what₂ rows' : Finset (Submodule (𝓞 D.host.E) (VS D).V)}
  (TR : TypedRed X) (cs : ColSys X u what₂) (cs' : ColSys X u' rows') (FdN FdN' : Set X.B.I.Ginf)

variable (F0 F0') in

def KExpansion (hK : X.LevelSubgroupCharacter) (Dt Dt' : Set X.B.I.GA) : Prop :=
  ∃ K : CM cs' →L[ℂ] CM cs,
    HasSum (fun t : GTerm X u u' F0 F0' what₂ rows' => aTerm cs cs' FdN FdN' t) K ∧
    ∀ (T : Cu X u hK) (T' : Cu X u' hK),
      Kform X u u' hK Dt Dt' FdN FdN' T T' = inner ℂ (K (sharp hK cs' T')) (sharp hK cs T)

variable (F0 F0') in

def AbsConvT : Prop := (tOf F0 F0' TR cs cs' FdN FdN').AbsConv

variable (F0 F0') in

def LemmaV : Prop :=
  ∀ t : GTerm X u u' F0 F0' what₂ rows', ¬ t.relevant → aTerm cs cs' FdN FdN' t = 0

variable (F0 F0') in

def NormExpSat : Prop :=
  (tOf F0 F0' TR cs cs' FdN FdN').NormExpansionOn
      (tOf F0 F0' TR cs cs' FdN FdN').genSet ∧
    (tOf F0 F0' TR cs cs' FdN FdN').NormExpansionOn
      (tOf F0 F0' TR cs cs' FdN FdN').ngSet

variable (F0 F0') in

def ChiNIndep : Prop :=
  ∀ (t : GTerm X u u' F0 F0' what₂ rows') (ρ : cs.Cl) (ρ' : cs'.Cl), cs.lamOf ρ = t.lam → cs'.lamOf ρ' = t.lam' →
    kOf X u u' (cs.h ρ : X.B.I.Gf) (cs'.h ρ' : X.B.I.Gf) t.pt ∈ X.K2 →
      chiN X (kOf X u u' (cs.h ρ : X.B.I.Gf) (cs'.h ρ' : X.B.I.Gf) t.pt) =
        chiN X (kOf X u u' (cs.h (cs.base t.lam) : X.B.I.Gf) (cs'.h (cs'.base t.lam') : X.B.I.Gf) t.pt)

variable (F0 F0') in

def AmpWellDef : Prop :=
  ∀ (ρ : cs.Cl) (ρ' : cs'.Cl) (p q : GCar X u u' F0 F0' (cs.lamOf ρ) (cs'.lamOf ρ')),
    GRel X u u' F0 F0' (cs.lamOf ρ) (cs'.lamOf ρ') p q →
    ∀ Ωp Ωq : Set X.B.I.Ginf,
      Formalism.L2.SG.HidaSetting.IsSFund X.B.I (ROset X F0 F0' (cs.lamOf ρ) (cs'.lamOf ρ') p.1.2) Ωp →
      Formalism.L2.SG.HidaSetting.IsSFund X.B.I (ROset X F0 F0' (cs.lamOf ρ) (cs'.lamOf ρ') q.1.2) Ωq →
      OOInt (Formalism.L2.SG.ProjRows.muInf X.B.I) Ωp (X.Wu u) (X.Wu u') p.1.1.1 →
      (kOf X u u' (cs.h ρ : X.B.I.Gf) (cs'.h ρ' : X.B.I.Gf) p.1.1 ∈ X.K2 ↔
        kOf X u u' (cs.h ρ : X.B.I.Gf) (cs'.h ρ' : X.B.I.Gf) q.1.1 ∈ X.K2) ∧
      (kOf X u u' (cs.h ρ : X.B.I.Gf) (cs'.h ρ' : X.B.I.Gf) p.1.1 ∈ X.K2 →
        (haveI := FiniteDimensional.complete ℂ (X.Vpi u)
         X.chi2 (kOf X u u' (cs.h ρ : X.B.I.Gf) (cs'.h ρ' : X.B.I.Gf) p.1.1) •
            OO (Formalism.L2.SG.ProjRows.muInf X.B.I) Ωp (X.Wu u) (X.Wu u') p.1.1.1 =
          X.chi2 (kOf X u u' (cs.h ρ : X.B.I.Gf) (cs'.h ρ' : X.B.I.Gf) q.1.1) •
            OO (Formalism.L2.SG.ProjRows.muInf X.B.I) Ωq (X.Wu u) (X.Wu u') q.1.1.1) ∧
        (haveI := FiniteDimensional.complete ℂ (X.Vpi u)
         chiN X (kOf X u u' (cs.h ρ : X.B.I.Gf) (cs'.h ρ' : X.B.I.Gf) p.1.1) •
            OO (Formalism.L2.SG.ProjRows.muInf X.B.I) Ωp (X.Wu u) (X.Wu u') p.1.1.1 =
          chiN X (kOf X u u' (cs.h ρ : X.B.I.Gf) (cs'.h ρ' : X.B.I.Gf) q.1.1) •
            OO (Formalism.L2.SG.ProjRows.muInf X.B.I) Ωq (X.Wu u) (X.Wu u') q.1.1.1))

variable (F0 F0') in

def IdCellOff : Prop :=
  u ≠ u' → HasSum (fun t : {t : GTerm X u u' F0 F0' what₂ rows' // t.isId} =>
    aTerm cs cs' FdN FdN' t.1) 0

theorem rowOrth : (tOf F0 F0' TR cs cs' FdN FdN').RowOrth := by
  intro t t' hio hne
  simp only [tOf, rowOf] at hio hne
  have hpair : ((⟨t.lam, t.mem⟩, ⟨t.lam', t.mem'⟩) : {Λ // Λ ∈ what₂} × {Λ' // Λ' ∈ rows'}) ≠
      (⟨t'.lam, t'.mem⟩, ⟨t'.lam', t'.mem'⟩) := by
    intro h
    apply hne
    simp only [Prod.mk.injEq] at h ⊢
    exact ⟨h.1, h.2, hio⟩
  rw [PiLp.inner_apply]
  refine Finset.sum_eq_zero fun q _ => ?_
  simp only [tOf, vec]
  split_ifs with h1 h2
  · exact absurd (h1.symm.trans h2) hpair
  · simp
  · simp
  · simp

theorem GG_diag (i : Iof TR) :
    (tOf F0 F0' TR cs cs' FdN FdN').GG i i =
      ((tOf F0 F0' TR cs cs' FdN FdN').Gam1 : ℂ) := by
  classical
  have hg : ∀ v, Formalism.L2.SG.GGMirabolic.gam (TR.psi0 v) (1 : GL (Fin D.R.k) (TR.Fq v)) =
      (((Nat.card (GL (Fin D.R.k) (TR.Fq v)) : ℝ) /
        (Formalism.L2.SG.GGMirabolic.cardU (TR.Fq v) D.R.k : ℝ) : ℝ) : ℂ) := by
    intro v
    have h1 : Formalism.L2.SG.GGMirabolic.psiNat (TR.psi0 v) (1 : GL (Fin D.R.k) (TR.Fq v)) = 1 := by
      unfold Formalism.L2.SG.GGMirabolic.psiNat Formalism.L2.SG.GGMirabolic.psiU
      rw [if_pos]
      · have hs : Formalism.L2.SG.GGMirabolic.superdiag D.R.k (1 : Matrix (Fin D.R.k) (Fin D.R.k) (TR.Fq v)) = 0 :=
          Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => by
            split_ifs with h
            · exact Matrix.one_apply_ne (fun e => by rw [e] at h; omega)
            · rfl
        rw [Units.val_one, hs, AddChar.map_zero_eq_one]
      · exact ⟨fun i => by simp, fun i j hij => by simp [Matrix.one_apply_ne (ne_of_gt hij)]⟩
    unfold Formalism.L2.SG.GGMirabolic.gam
    simp only [mul_one, mul_inv_cancel, h1, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [Nat.card_eq_fintype_card]
    push_cast
    ring
  have hp : Formalism.L2.SG.GGMirabolic.gamProd TR.psi0 (1 : Iof TR) =
      ((∏ v, ((Nat.card (GL (Fin D.R.k) (TR.Fq v)) : ℝ) /
        (Formalism.L2.SG.GGMirabolic.cardU (TR.Fq v) D.R.k : ℝ)) : ℝ) : ℂ) := by
    unfold Formalism.L2.SG.GGMirabolic.gamProd
    simp only [Pi.one_apply, hg]
    push_cast
    rfl
  show conj (Formalism.L2.SG.GGMirabolic.gamProd TR.psi0 (i⁻¹ * i)) =
    (((Formalism.L2.SG.GGMirabolic.gamProd TR.psi0 (1 : Iof TR)).re : ℝ) : ℂ)
  rw [inv_mul_cancel, hp, Complex.conj_ofReal, Complex.ofReal_re]

theorem ggBound (h : Formalism.L2.SG.GGMirabolic.TermsGGBound) (hψ : ∀ v, TR.psi0 v ≠ 1)
    (hq : ∀ v, 3 ≤ Fintype.card (TR.Fq v)) :
    (tOf F0 F0' TR cs cs' FdN FdN').GGBound
      (∏ v, (1 + 3 / (Fintype.card (TR.Fq v) : ℝ))) := by
  classical
  refine h TR.Pl TR.Fq D.R.k TR.psi0 hψ hq (Iof TR) (fun x j hx => ?_) (fun i j => j⁻¹ * i)
    (fun i j _ => ?_) _ _ _ _ (tOf F0 F0' TR cs cs' FdN FdN') (fun i j => ?_) rfl
  · rw [MulOpposite.smul_eq_mul_unop] at hx
    exact MulOpposite.unop_injective (mul_left_cancel (hx.trans (mul_one j).symm))
  · rw [MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, mul_inv_cancel_left]
  · rw [if_pos ⟨MulOpposite.op (j⁻¹ * i), by
      rw [MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, mul_inv_cancel_left]⟩]
    rfl

end Stmt

section IdCell

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.L2.SG.PoincareInHH.PoincareSetting

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {u : D.what₂.Word}
  {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)} {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}
  (cs : ColSys X u what₂) (FdN : Set X.B.I.Ginf)

variable (F0) in

def IdCellDiag : Prop :=
  Formalism.L2.SG.HidaSetting.IsSFund X.B.I (NOinf X u) FdN →
  HasSum (fun t : {t : GTerm X u u F0 F0 what₂ what₂ // t.isId} => aTerm cs cs FdN FdN t.1)
    (ContinuousLinearMap.id ℂ (CM cs))

end IdCell

end Formalism.L2.SG.TermOp
