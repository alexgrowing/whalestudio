import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.InBlock
import Formalism.LocalToGlobal.IndefiniteReal.CxPassMet
import Formalism.LocalToGlobal.Divisibility.TrivialExtensionSideWellFormed

open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder InnerProductSpace

noncomputable section

namespace Formalism.IndefR.CxPass

open Formalism.DivisionValues Formalism.L2.Indef Formalism.L2.DIV Formalism.IndefR.Cx Formalism.L2.GlobalTheoryTheory.DivPassage

section Part3

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 I0 Ty : Type}

theorem mem_part3_iff (B : BlockDat K G Pl0) (D : InertDat3 B I0 Ty) (ℓ : Lvl K G) (Z : Submodule K B.S.Forms)
    (p : Typ3 K Pl0 I0 Ty) (y : Fin (B.dZ ℓ Z) → K) : y ∈ D.part3 ℓ Z p ↔ B.toF ℓ Z y ∈ D.inertTypeEigenspaceSum p := by
  rw [InertDat3.inert_part_eq_comap]; rfl

end Part3

open Formalism.IndefR.CxPass.In

namespace In3

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 I0 Ty T : Type} {m : ℕ}
  (I : In3 K G Pl0 I0 Ty T m)

theorem side_lv (b : Bool) :
    lv (faceOf3 I.A3 I.P0 I.ψ0 I.P1 I.ψ1 I.Dc I.Sp I.Zsc I.X.zs) b = I.A3.side3 (I.lvP b) (I.lvψ b) I.X.zs := by
  cases b <;> rfl

theorem Jm_eq (b : Bool) : I.Jm b = I.Jt b I.A3.fam3.base3.μ0 := rfl

theorem pFrames : I.PFrames := by
  intro s h v
  have hW := I.A3.side_well_formed h.ok ⊥ 1 I.X.zs h.stable h.inBlock h.sep
  have hu : IsUnit (frameOf ((prin I.X).gramE I.cg false)).det :=
    gramE_unit' (prin I.X) I.cg false h.h2g.1 (by show (0 : ℝ) < 1; norm_num)
  exact (rowXE_spec (Df := I.A3.side3 ⊥ 1 I.X.zs) hW _ hu I.X.κ h.h4pos.1 (fun j p v => I.X.lam j I.A3.fam3.base3.μ0 p v)
    (fun j p v => h.h4pos.2.1 j _ p v)).1 v

variable {I} in
theorem Z_stable_g {s : ℕ} (h : I.Hyp s) (g : G) :
    I.X.zs.Z I.A.fam.μ0 ≤ (I.X.zs.Z I.A.fam.μ0).comap ((I.A.fam.R I.A.fam.μ0).r g) := fun _ hz =>
  h.stable.1 I.A.fam.μ0 (Sum.inr g) (Submodule.mem_map_of_mem hz)

variable {I} in
theorem toF_rho (hρ : I.PRho) {s : ℕ} (h : I.Hyp s) (g : G) (x : Fin I.Sg.D → K) :
    (I.A.fam.R I.A.fam.μ0).toF (I.A.fam.lvl ⊥ 1) (I.X.zs.Z I.A.fam.μ0) (I.ρf g *ᵥ x) =
      (I.A.fam.R I.A.fam.μ0).r g ((I.A.fam.R I.A.fam.μ0).toF (I.A.fam.lvl ⊥ 1) (I.X.zs.Z I.A.fam.μ0) x) := by
  obtain ⟨y, hty⟩ := exists_toF_act (I.A.fam.R I.A.fam.μ0) h.ok.ok2.conj (h.ok.ok2.what₂ _) I.A.fam.X h.ok.ok2.irr
    (I.X.zs.Z I.A.fam.μ0) (fun g => Z_stable_g h g) g x
  have key : I.iCg (cpt I.A3.fam3.base3.v0.embedding (I.ρf g *ᵥ x)) = I.iCg (cpt I.A3.fam3.base3.v0.embedding y) := by
    rw [(hρ s h).2.2 g x]
    have e1 : I.iCg (cpt I.A3.fam3.base3.v0.embedding x) =
        I.X.Θ I.A.fam.μ0 (I.X.jR I.A.fam.μ0 ((I.A.fam.R I.A.fam.μ0).toF (I.A.fam.lvl ⊥ 1) (I.X.zs.Z I.A.fam.μ0) x)) :=
      iC_cpt I.X I.cg false I.A.fam.μ0 x
    have e2 : I.iCg (cpt I.A3.fam3.base3.v0.embedding y) =
        I.X.Θ I.A.fam.μ0 (I.X.jR I.A.fam.μ0 ((I.A.fam.R I.A.fam.μ0).toF (I.A.fam.lvl ⊥ 1) (I.X.zs.Z I.A.fam.μ0) y)) :=
      iC_cpt I.X I.cg false I.A.fam.μ0 y
    rw [e1, e2]
    erw [hty]
    exact (h.gequiv I.A.fam.μ0 g _).symm
  have hxy := cpt_injective _ (h.h2g.1 key)
  exact (congrArg (fun z => (I.A.fam.R I.A.fam.μ0).toF (I.A.fam.lvl ⊥ 1) (I.X.zs.Z I.A.fam.μ0) z) hxy).trans hty

variable {I} in
theorem wf_lv {s : ℕ} (h : I.Hyp s) (b : Bool) : (lv (faceOf3 I.A3 I.P0 I.ψ0 I.P1 I.ψ1 I.Dc I.Sp I.Zsc I.X.zs) b).WF := by
  rw [side_lv]; exact I.A3.side_well_formed h.ok _ _ _ h.stable h.inBlock h.sep

variable {I} in
theorem wf_g {s : ℕ} (h : I.Hyp s) : (lv (faceOf3 I.A3 ⊥ 1 I.P1 I.ψ1 I.Dc I.Sp I.Zsc I.X.zs) false).WF :=
  I.A3.side_well_formed h.ok ⊥ 1 _ h.stable h.inBlock h.sep

variable {I} in

theorem opAll_comm {s : ℕ} (h : I.Hyp s) (g : G) (k : (I.A3.rowI I.A.fam.μ0).OpIx) :
    Commute ((I.A3.rowI I.A.fam.μ0).opAll k) ((I.A.fam.R I.A.fam.μ0).r g) := by
  rcases k with i | k
  · exact (h.ok.ok2.what₂ _).opG i g
  · exact (h.ok.what₂ _).opG k g

variable {I} in
theorem Jm_parts (hJt : I.PJt) {s : ℕ} (h : I.Hyp s) (b : Bool) (p : I.A3.fam3.base3.Ix)
    (x : Fin ((lv (faceOf3 I.A3 I.P0 I.ψ0 I.P1 I.ψ1 I.Dc I.Sp I.Zsc I.X.zs) b).dQ I.A3.fam3.base3.μ0) → K)
    (hx : x ∈ (lv (faceOf3 I.A3 I.P0 I.ψ0 I.P1 I.ψ1 I.Dc I.Sp I.Zsc I.X.zs) b).Qp I.A3.fam3.base3.μ0 p) :
    I.Jm b *ᵥ x ∈ (lv (faceOf3 I.A3 ⊥ 1 I.P1 I.ψ1 I.Dc I.Sp I.Zsc I.X.zs) false).Qp I.A3.fam3.base3.μ0 p := by
  cases b
  · refine (mem_part3_iff (I.A.fam.R I.A.fam.μ0) (I.A3.rowI I.A.fam.μ0) (I.A.fam.lvl ⊥ 1) (I.X.zs.Z I.A.fam.μ0) p.1 (I.Jm false *ᵥ x)).2 ?_
    have e : (I.A.fam.R I.A.fam.μ0).toF (I.A.fam.lvl ⊥ 1) (I.X.zs.Z I.A.fam.μ0) (I.Jm false *ᵥ x) =
        (I.A.fam.R I.A.fam.μ0).toF (I.A.fam.lvl I.P0 I.ψ0) (I.X.zs.Z I.A.fam.μ0) x := (hJt s h false I.A.fam.μ0).2.1 x
    rw [e]
    exact (mem_part3_iff (I.A.fam.R I.A.fam.μ0) (I.A3.rowI I.A.fam.μ0) (I.A.fam.lvl I.P0 I.ψ0) (I.X.zs.Z I.A.fam.μ0) p.1 x).1 hx
  · refine (mem_part3_iff (I.A.fam.R I.A.fam.μ0) (I.A3.rowI I.A.fam.μ0) (I.A.fam.lvl ⊥ 1) (I.X.zs.Z I.A.fam.μ0) p.1 (I.Jm true *ᵥ x)).2 ?_
    have e : (I.A.fam.R I.A.fam.μ0).toF (I.A.fam.lvl ⊥ 1) (I.X.zs.Z I.A.fam.μ0) (I.Jm true *ᵥ x) =
        (I.A.fam.R I.A.fam.μ0).toF (I.A.fam.lvl I.P1 I.ψ1) (I.X.zs.Z I.A.fam.μ0) x := (hJt s h true I.A.fam.μ0).2.1 x
    rw [e]
    exact (mem_part3_iff (I.A.fam.R I.A.fam.μ0) (I.A3.rowI I.A.fam.μ0) (I.A.fam.lvl I.P1 I.ψ1) (I.X.zs.Z I.A.fam.μ0) p.1 x).1 hx

variable {I} in
theorem quot_lv (hT : TransferS (K := K) (G := G) (Pl0 := Pl0)) (hJt : I.PJt) {s : ℕ} (h : I.Hyp s) (b : Bool)
    (v : InfinitePlace K)
    (x y : Fin ((lv (faceOf3 I.A3 I.P0 I.ψ0 I.P1 I.ψ1 I.Dc I.Sp I.Zsc I.X.zs) b).dQ I.A3.fam3.base3.μ0) → K) :
    Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K _) ((lv (faceOf3 I.A3 I.P0 I.ψ0 I.P1 I.ψ1 I.Dc I.Sp I.Zsc I.X.zs) b).XQ I.A3.fam3.base3.μ0) v x y =
      (((Nat.card (I.lvP b) : ℝ)⁻¹ : ℝ) : ℂ) *
        Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K _) ((lv (faceOf3 I.A3 ⊥ 1 I.P1 I.ψ1 I.Dc I.Sp I.Zsc I.X.zs) false).XQ I.A3.fam3.base3.μ0) v
          (I.Jm b *ᵥ x) (I.Jm b *ᵥ y) := by
  cases b
  · exact hT (I.A.fam.R I.A.fam.μ0) h.ok.ok2.conj (h.ok.ok2.what₂ _) I.A.fam.X h.ok.ok2.irr I.P0 I.ψ0 (I.X.zs.Z I.A.fam.μ0)
      (fun g => Z_stable_g h g) (I.Jm false) (hJt s h false I.A.fam.μ0).2.1 v x y
  · exact hT (I.A.fam.R I.A.fam.μ0) h.ok.ok2.conj (h.ok.ok2.what₂ _) I.A.fam.X h.ok.ok2.irr I.P1 I.ψ1 (I.X.zs.Z I.A.fam.μ0)
      (fun g => Z_stable_g h g) (I.Jm true) (hJt s h true I.A.fam.μ0).2.1 v x y

variable {I} in
theorem majorant_at_base_eq_inner {s : ℕ} (h : I.Hyp s) (x y : Fin I.Sg.D → K) :
    Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin I.Sg.D)) I.Sg.XE I.A3.fam3.base3.v0 x y =
      ⟪I.iCg (cpt I.A3.fam3.base3.v0.embedding x), I.iCg (cpt I.A3.fam3.base3.v0.embedding y)⟫_ℂ := by
  have e := majorant_at_base_eq_scaled_inner (prin I.X) I.cg false (wf_g h) h.h2g.1 (show (0 : ℝ) < 1 by norm_num) h.h4pos.1
    (fun j p v => h.h4pos.2.1 j _ p v) x y
  have e1 : (prin I.X).nP false = 1 := rfl
  rw [e1, inv_one, Complex.ofReal_one, one_mul] at e
  exact e

variable {I} in
theorem majorant_at_base_eq_inner_of_package {s : ℕ} (h : I.Hyp s) (b : Bool) (x y : Fin (I.Sb b).D → K) :
    Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin (I.Sb b).D)) (I.Sb b).XE I.A3.fam3.base3.v0 x y =
      (((I.X.nP b)⁻¹ : ℝ) : ℂ) *
        ⟪I.X.iC I.cr b I.A3.fam3.base3.μ0 (cpt I.A3.fam3.base3.v0.embedding x),
          I.X.iC I.cr b I.A3.fam3.base3.μ0 (cpt I.A3.fam3.base3.v0.embedding y)⟫_ℂ :=
  majorant_at_base_eq_scaled_inner I.X I.cr b (wf_lv h b) (h.h2 b).1 (h.h4pos.2.2 b) h.h4pos.1 (fun j p v => h.h4pos.2.1 j _ p v) x y

variable {I} in
theorem nP_eq_card_lvP {s : ℕ} (h : I.Hyp s) (b : Bool) : I.X.nP b = (Nat.card (I.lvP b) : ℝ) := by
  cases b
  · exact h.np0
  · exact h.np1

theorem pMet_core (hT : TransferS (K := K) (G := G) (Pl0 := Pl0)) (hsc : ∀ {n : ℕ}
    (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) (c : ℝ), 0 < c → ∀ (v : InfinitePlace K) (x y : Fin n → K),
      Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin n)) (Formalism.BranchingDeterminantCap.scaleFrame c X) v x y =
        (((c ^ 2)⁻¹ : ℝ) : ℂ) * Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin n)) X v x y)
    (hJt : I.PJt) (hJ : I.PJ) : I.PMet := by
  intro s h b v x y
  have hcard : (0 : ℝ) < (Nat.card (I.lvP b) : ℝ) := by exact_mod_cast Nat.card_pos
  rw [hsc _ _ (Real.sqrt_pos.2 hcard), Real.sq_sqrt hcard.le]
  by_cases hv : v = I.A3.fam3.base3.v0
  · subst hv
    rw [majorant_at_base_eq_inner_of_package h b, majorant_at_base_eq_inner h, nP_eq_card_lvP h b]
    congr 1
    exact (congrArg₂ (fun a c => ⟪a, c⟫_ℂ) ((hJ s h b).1 x) ((hJ s h b).1 y)).symm
  · exact rowXE_map (lv (faceOf3 I.A3 I.P0 I.ψ0 I.P1 I.ψ1 I.Dc I.Sp I.Zsc I.X.zs) b)
      (lv (faceOf3 I.A3 ⊥ 1 I.P1 I.ψ1 I.Dc I.Sp I.Zsc I.X.zs) false) (wf_lv h b) (wf_g h) _
      (gramE_unit' I.X I.cr b (h.h2 b).1 (h.h4pos.2.2 b)) _
      (gramE_unit' (prin I.X) I.cg false h.h2g.1 (by show (0 : ℝ) < 1; norm_num)) I.X.κ h.h4pos.1
      (fun j p v => I.X.lam j I.A3.fam3.base3.μ0 p v) (fun j p v => h.h4pos.2.1 j _ p v) (I.Jm b)
      (fun p x hx => Jm_parts hJt h b p x hx) _ v hv (quot_lv hT hJt h b v) x y

variable {I} in
theorem rho_parts (hρ : I.PRho) {s : ℕ} (h : I.Hyp s) (g : G) (p : I.A3.fam3.base3.Ix)
    (x : Fin ((lv (faceOf3 I.A3 ⊥ 1 I.P1 I.ψ1 I.Dc I.Sp I.Zsc I.X.zs) false).dQ I.A3.fam3.base3.μ0) → K)
    (hx : x ∈ (lv (faceOf3 I.A3 ⊥ 1 I.P1 I.ψ1 I.Dc I.Sp I.Zsc I.X.zs) false).Qp I.A3.fam3.base3.μ0 p) :
    I.ρf g *ᵥ x ∈ (lv (faceOf3 I.A3 ⊥ 1 I.P1 I.ψ1 I.Dc I.Sp I.Zsc I.X.zs) false).Qp I.A3.fam3.base3.μ0 p := by
  have hx' := (mem_part3_iff (I.A.fam.R I.A.fam.μ0) (I.A3.rowI I.A.fam.μ0) (I.A.fam.lvl ⊥ 1) (I.X.zs.Z I.A.fam.μ0) p.1 x).1 hx
  refine (mem_part3_iff (I.A.fam.R I.A.fam.μ0) (I.A3.rowI I.A.fam.μ0) (I.A.fam.lvl ⊥ 1) (I.X.zs.Z I.A.fam.μ0) p.1 (I.ρf g *ᵥ x)).2 ?_
  rw [toF_rho hρ h g x]
  exact Formalism.L2.Col.eigSum_le_comap (fun k => opAll_comm h g k) _ hx'

theorem pUni_core (hI : InvS (K := K) (G := G) (Pl0 := Pl0)) (hρ : I.PRho) : I.PUni := by
  intro s h v g x y
  by_cases hv : v = I.A3.fam3.base3.v0
  · subst hv
    rw [majorant_at_base_eq_inner h, majorant_at_base_eq_inner h]
    exact (congrArg₂ (fun a c => ⟪a, c⟫_ℂ) ((hρ s h).2.2 g x) ((hρ s h).2.2 g y)).trans (h.gunit g _ _)
  · have e := rowXE_map (lv (faceOf3 I.A3 ⊥ 1 I.P1 I.ψ1 I.Dc I.Sp I.Zsc I.X.zs) false)
      (lv (faceOf3 I.A3 ⊥ 1 I.P1 I.ψ1 I.Dc I.Sp I.Zsc I.X.zs) false) (wf_g h) (wf_g h) _
      (gramE_unit' (prin I.X) I.cg false h.h2g.1 (by show (0 : ℝ) < 1; norm_num)) _
      (gramE_unit' (prin I.X) I.cg false h.h2g.1 (by show (0 : ℝ) < 1; norm_num)) I.X.κ h.h4pos.1
      (fun j p v => I.X.lam j I.A3.fam3.base3.μ0 p v) (fun j p v => h.h4pos.2.1 j _ p v) (I.ρf g)
      (fun p x hx => rho_parts hρ h g p x hx) 1 v hv
      (fun x y => by
        rw [one_mul]
        exact (hI (I.A.fam.R I.A.fam.μ0) h.ok.ok2.conj (h.ok.ok2.what₂ _) I.A.fam.X h.ok.ok2.irr (I.X.zs.Z I.A.fam.μ0)
          (fun g => Z_stable_g h g) g (I.ρf g) (toF_rho hρ h g) v x y).symm) x y
    rw [one_mul] at e
    exact e.symm

theorem pMet_of (hJt : I.PJt) (hJ : I.PJ) : I.PMet :=
  I.pMet_core transferS_holds (fun X c hc v x y => BlockMetrics.majAt_scaleFrame X c hc v x y) hJt hJ

theorem pUni_of (_hJt : I.PJt) (hρ : I.PRho) : I.PUni :=
  I.pUni_core invS_holds hρ

end In3

end Formalism.IndefR.CxPass
