import Formalism.LocalToGlobal.Columns.TiedXp
import Formalism.LocalToGlobal.Columns.TiedVal
import Formalism.LocalToGlobal.Columns.TiedValRat
import Formalism.LocalToGlobal.Columns.TiedValFi
import Formalism.LocalToGlobal.Columns.TiedValLat
import Formalism.LocalToGlobal.Columns.TiedValNorm
import Formalism.LocalToGlobal.Columns.BaseLemmas

open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.UG Formalism.L2.Forms

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem xp_sgHC_eq {R : Ranks} (P : HCParam R) (i : Fin (R.N R.m - 1)) :
    (RowPar.of P).sgHC i.1 = Formalism.L2.Forms.sgHC R P i.1 := by
  unfold RowPar.sgHC Formalism.L2.Forms.sgHC
  by_cases h1 : i.1 < R.k - 1
  · simp only [dif_pos h1, RowPar.of]
  · have h2 : (i.1 - (R.k - 1)) / (R.t + 1) < R.m := by
      apply Nat.div_lt_of_lt_mul
      have := R.m_add_three_le_k
      have hi := i.2
      unfold Ranks.N at hi
      rw [Nat.mul_comm]; omega
    simp only [dif_neg h1, dif_pos h2, RowPar.bAt, RowPar.eAt, RowPar.of]

theorem xp_sg_tie {R : Ranks} (P : HCParam R) (i : Fin (R.N R.m - 1)) :
    (((RowPar.of P).sg).w i : ℚ) = Formalism.L2.Forms.sgHC R P i - rhoVec (R.N R.m - 1) i := by
  rw [RowPar.sg_eq, xp_sgHC_eq]

theorem xp_half (R : Ranks) : R.m * (R.t + 1) / 2 = R.m * ((R.t + 1) / 2) := by
  obtain ⟨b, hb⟩ := R.t_odd
  have h : R.t + 1 = 2 * (b + 1) := by omega
  rw [h, Nat.mul_div_cancel_left _ (by norm_num : 0 < 2), Nat.mul_left_comm, Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]

theorem xp_sgTrue_eq {R : Ranks} (S : RowPar R) : S.sgTrue = shW S.sg ((R.m * (R.t + 1) / 2 : ℕ) : ℤ) := by
  unfold RowPar.sgTrue shiftW shW
  congr 1
  funext i
  rw [xp_half]
  push_cast
  ring

section Gen

variable {X : Fields} {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 X.E))} (σ₀ : X.K →+* ℂ)
  (hσ : ∀ x : X.K, σ₀ (star x) = starRingEnd ℂ (σ₀ x)) (lam : X.Tau → DomWeight n)
  (Lf : DecoSet X.E n ST SG → Submodule (𝓞 X.E) (Sp X.E n)) (Λ : LevFam X.E X.K n SG)

theorem xp_ipCl_tie (hOk : (formGSD (roundPk X lam Lf) Λ).Ok) (lam' : X.Tau → DomWeight n)
    (hnf : ∀ p q, nfAll lam p q = nfAll lam' p q) {J : Matrix (Fin n) (Fin n) X.E} (hJ : J = 1)
    {emb : X.Tau → X.E →+* ℂ} (hemb : emb = X.embC σ₀) {lamT : X.Tau → DomWeight n} (hT : lamT = lam)
    (o : Frames (gramC J emb)) (ho : o.IsON)
    (z z' : (formGSD (roundPk X lam Lf) Λ).Cl → Frames (gramC J emb) → ℂ)
    (P Q : (formGSD (roundPk X lam Lf) Λ).Cl → MvPolynomial (X.Tau × Fin n × Fin n) ℂ)
    (hz : ∀ c, z c = fnOf (gramC J emb) (shiftOf lamT) (fun τ => (o.1 τ)⁻¹) (P c))
    (hz' : ∀ c, z' c = fnOf (gramC J emb) (shiftOf lamT) (fun τ => (o.1 τ)⁻¹) (Q c)) :
    (roundEv σ₀ hσ lam Lf Λ).ipCl hOk z z' = (letI := hOk.fintypeCl
      ∑ c, ((Nat.card (MulAction.stabilizer (formGSD (roundPk X lam Lf) Λ).G
        ((formGSD (roundPk X lam Lf) Λ).outSec.rep c)) : ℕ) : ℂ)⁻¹ * nfAll lam' (Q c) (P c)) := by
  subst hJ hemb hT
  refine (GSD.Ev.ipCl_apply (roundEv σ₀ hσ lamT Lf Λ) hOk z z').trans ?_
  refine Finset.sum_congr rfl fun c _ => ?_
  congr 1
  rw [hz c, hz' c, ← hnf]
  exact ipFr_fnOf _ lamT (stdFrC _) o (frame_std _ _ (stdFrC_isON _)) (frame_std _ o ho) (P c) (Q c)

end Gen

section GenP

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (ΛM : LevFam X.E X.K (R.N R.m - 1) Pr.vGs)

structure PCrd (σ₀ : X.K →+* ℂ) extends
    StepCrd Pr σ₀ (R.N R.m - 1) (fun c : (ptGSD W ΛM).Cl => ((ptGSD W ΛM).outSec.rep c).1.N) where
  lt : X.Tau → DomWeight (R.N R.m - 1)
  hlt : lt = W.sgTrue

variable (hc : CMData X.F X.E) (hX : X.Ok) (σ₀ : X.K →+* ℂ) (hσ : ∀ x : X.K, σ₀ (star x) = starRingEnd ℂ (σ₀ x))
  (hS : DecoPtSurj hc (R.N R.m - 1) (∅ : Finset (Pl X.E)) Pr.vGs)

@[reducible] def xpK (Q : PCrd W ΛM σ₀) :=
  clsPG hc σ₀ ΛM.inv (fun c : (ptGSD W ΛM).Cl => (ptGSD W ΛM).outSec.rep c) hS
    (fun c => (ptGSD W ΛM).outSec.spec c) Q.toStepCrd

def xpEW (Q : PCrd W ΛM σ₀) : ((ptGSD W ΛM).Cl → FrS X σ₀ (R.N R.m - 1) → ℂ) ≃ₗ[ℂ]
    ((ptGSD W ΛM).Cl → Frames (gramC Q.J Q.emb) → ℂ) := LinearEquiv.refl _ _

namespace XpV

def PtC (Q : PCrd W ΛM σ₀) : Prop :=
  ∀ z : (ptGSD W ΛM).Cl → FrS X σ₀ (R.N R.m - 1) → ℂ, z ∈ (ptEv W ΛM σ₀ hσ).Fi ↔
    xpEW W ΛM σ₀ Q z ∈ FiC (xpK W ΛM hc σ₀ hS Q).lev Q.emb Q.lt (xpK W ΛM hc σ₀ hS Q).y

def IpP (Q : PCrd W ΛM σ₀) : Prop :=
  letI := (ptOk W ΛM hX).fintypeCl
  ∀ (o : Frames (gramC Q.J Q.emb)), o.IsON → ∀ (z z' : (ptGSD W ΛM).Cl → FrS X σ₀ (R.N R.m - 1) → ℂ)
    (P P' : (ptGSD W ΛM).Cl → MvPolynomial (X.Tau × Fin (R.N R.m - 1) × Fin (R.N R.m - 1)) ℂ),
    (∀ c, P c ∈ CSpan W.sgW) → (∀ c, P' c ∈ CSpan W.sgW) →
    (∀ c, xpEW W ΛM σ₀ Q z c = fnOf _ (shiftOf Q.lt) (fun τ => (o.1 τ)⁻¹) (P c)) →
    (∀ c, xpEW W ΛM σ₀ Q z' c = fnOf _ (shiftOf Q.lt) (fun τ => (o.1 τ)⁻¹) (P' c)) →
    (ptEv W ΛM σ₀ hσ).ipCl (ptOk W ΛM hX) z z' =
      ∑ c, ((Nat.card (MulAction.stabilizer (ptGSD W ΛM).G ((ptGSD W ΛM).outSec.rep c)) : ℕ) : ℂ)⁻¹ *
        nfAll W.sgW (P' c) (P c)

def Rat (Q : PCrd W ΛM σ₀) : Prop :=
  ∀ z : (ptGSD W ΛM).Cl → FrS X σ₀ (R.N R.m - 1) → ℂ, (∃ x, (ptEv W ΛM σ₀ hσ).emb x = z) ↔
    z ∈ (ptEv W ΛM σ₀ hσ).Fi ∧ ∀ c, ∃ P ∈ RatSpanG σ₀ W.sgW, xpEW W ΛM σ₀ Q z c = fnOf _ (shiftOf Q.lt) 1 P

def Lat (Pl : Rows.Places X.K) (Q : PCrd W ΛM σ₀) : Prop :=
  ∀ x : (ptGSD W ΛM).EqFun, x ∈ (ptGSD W ΛM).intDel ↔
    ∀ (w : Pl.Pl) (c : (ptGSD W ΛM).Cl) (B : GL (Fin (R.N R.m - 1)) X.E),
      IsLocBasis (Pl.resChar w) (Q.lat c : Set _) B →
      ∃ P ∈ IntSpanG σ₀ Pl w W.sgW, xpEW W ΛM σ₀ Q ((ptEv W ΛM σ₀ hσ).emb x) c =
        fnOf _ (shiftOf Q.lt) (atInf Q.emb (B⁻¹ : GL (Fin (R.N R.m - 1)) X.E).1) P

def Norm (Q : PCrd W ΛM σ₀) : Prop :=
  letI := (ptOk W ΛM hX).fintypeCl
  ∀ (s : X.K →+* ℂ) (x : (ptGSD W ΛM).EqFun)
    (Pc : (ptGSD W ΛM).Cl → MvPolynomial (X.Tau × Fin (R.N R.m - 1) × Fin (R.N R.m - 1)) X.K),
    (∀ c, xpEW W ΛM σ₀ Q ((ptEv W ΛM σ₀ hσ).emb x) c = fnOf _ (shiftOf Q.lt) 1 (MvPolynomial.map σ₀ (Pc c))) →
    ∀ o : Frames (gramC Q.J (embAt s X.emb)), o.IsON →
      (Formalism.HermitianLatticesTheory.majAt (ptH W ΛM hX).b (ptH W ΛM hX).X (InfinitePlace.mk s) x x).re =
        ∑ c, ((Nat.card (MulAction.stabilizer (ptGSD W ΛM).G ((ptGSD W ΛM).outSec.rep c)) : ℕ) : ℝ)⁻¹ *
          (∏ τ, ‖(o.1 τ).det‖ ^ (2 * shiftOf Q.lt τ)) *
          (nfAll W.sgW (subP o.1 (MvPolynomial.map s (Pc c))) (subP o.1 (MvPolynomial.map s (Pc c)))).re

end XpV

theorem XpV.ipP (Q : PCrd W ΛM σ₀) : XpV.IpP W ΛM hX σ₀ hσ Q := by
  intro o ho z z' P P' _ _ hz hz'
  refine xp_ipCl_tie σ₀ hσ W.sgTrue _ ΛM.inv (ptOk W ΛM hX) W.sgW ?_ Q.hJ Q.hemb Q.hlt o ho z z' P P' hz hz'
  intro p q
  have h : W.sgTrue = fun τ => shW (W.sgW τ) ((R.m * (R.t + 1) / 2 : ℕ) : ℤ) := funext fun τ => xp_sgTrue_eq (W.row τ)
  rw [h]
  exact nfAll_shW _ _ _ _

include hX in
theorem XpV.rat (Q : PCrd W ΛM σ₀) : XpV.Rat W ΛM σ₀ hσ Q := by
  obtain ⟨⟨J, f, bad, emb, lat, l0, rfl, rfl, rfl, rfl, rfl, rfl⟩, lt, rfl⟩ := Q
  intro z
  have h := roundEv_exists_emb_iff σ₀ hσ W.sgTrue (fun d : DecoSet X.E (R.N R.m - 1) ∅ Pr.vGs => d.1.N) ΛM.inv (ptOk W ΛM hX) z
  have e : RatSpanG σ₀ W.sgTrue = RatSpanG σ₀ W.sgW := by
    have h2 : W.sgTrue = fun τ => shW (W.sgW τ) ((R.m * (R.t + 1) / 2 : ℕ) : ℤ) := funext fun τ => xp_sgTrue_eq (W.row τ)
    rw [h2]
    exact RatSpanG_shW σ₀ _ _
  rw [e] at h
  exact h

include hX in
theorem XpV.ptC (Q : PCrd W ΛM σ₀) : XpV.PtC W ΛM hc σ₀ hσ hS Q := by
  obtain ⟨⟨J, f, bad, emb, lat, l0, rfl, rfl, rfl, rfl, rfl, rfl⟩, lt, rfl⟩ := Q
  intro z
  exact fi_iff_FiC hc σ₀ hσ W.sgTrue (fun d : DecoSet X.E (R.N R.m - 1) ∅ Pr.vGs => d.1.N) ΛM.inv 1 (ptOk W ΛM hX) hS
    (L := tieLevP hc σ₀ ΛM.inv) ⟨rfl, fun _ _ => rfl⟩ z

theorem xp_natW_sgTrue (τ : X.Tau) : (W.sgTrue τ).natW = (W.sgW τ).natW := by
  show (W.row τ).sgTrue.natW = _
  rw [xp_sgTrue_eq, natW_shW]
  rfl

include hX in

theorem XpV.lat (Pl : Rows.Places X.K) (pw : Pl.Pl → HeightOneSpectrum (𝓞 X.K)) (hpw : Function.Surjective pw)
    (hval : ∀ w (x : X.K), x ≠ 0 → Pl.val w x = ((vAdd (pw w) x : ℤ) : WithTop ℤ)) (Q : PCrd W ΛM σ₀) :
    XpV.Lat W ΛM σ₀ hσ Pl Q := by
  obtain ⟨⟨J, f, bad, emb, lat, l0, rfl, rfl, rfl, rfl, rfl, rfl⟩, lt, rfl⟩ := Q
  intro x
  rw [(ptGSD W ΛM).mem_intDel_iff (ptOk W ΛM hX) (ptGSD W ΛM).outSec x]
  have key := fun c : (ptGSD W ΛM).Cl => vl_mem_delAtr_iff Pl pw hval X.emb σ₀ hpw
    (1 : Matrix (Fin (R.N R.m - 1)) (Fin (R.N R.m - 1)) X.E) W.sgTrue W.sgW (xp_natW_sgTrue W) ((ptGSD W ΛM).outSec.rep c).1.N
    ((ptGSD W ΛM).outSec.rep c).2.lat ((x : (ptGSD W ΛM).D → (ptGSD W ΛM).V) ((ptGSD W ΛM).outSec.rep c))
  constructor
  · intro h w c B hB
    exact (key c).1 (h c) w B hB
  · intro h c
    exact (key c).2 fun w B hB => h w c B hB

theorem XpV.norm (Q : PCrd W ΛM σ₀) : XpV.Norm W ΛM hX σ₀ hσ Q := by
  obtain ⟨⟨J, f, bad, emb, lat, l0, rfl, rfl, rfl, rfl, rfl, rfl⟩, lt, rfl⟩ := Q
  intro s x Pc hPc o ho
  have hval : ∀ c, (x.1 ((ptGSD W ΛM).outSec.rep c) : VV X.K W.sgTrue).1 = Pc c := by
    intro c
    apply evFr_injective (gramC (1 : Matrix (Fin (R.N R.m - 1)) (Fin (R.N R.m - 1)) X.E) (embAt σ₀ X.emb)) (shiftOf W.sgTrue) σ₀
      (stdFrC _)
    rw [evFr_eq_fnOf, evFr_eq_fnOf]
    exact hPc c
  have h := vn_norm_round W.sgTrue (fun d : DecoSet X.E (R.N R.m - 1) ∅ Pr.vGs => d.1.N) ΛM.inv (ptOk W ΛM hX)
    (ptRat W ΛM hX) s o ho x
  refine h.trans ?_
  let _ := (ptOk W ΛM hX).fintypeCl
  refine Finset.sum_congr rfl fun c _ => ?_
  have hv : (x.1 ((formGSD (roundPk X W.sgTrue fun d : DecoSet X.E (R.N R.m - 1) ∅ Pr.vGs => d.1.N) ΛM.inv).outSec.rep c) :
      VV X.K W.sgTrue).1 = Pc c := hval c
  have h2 : ∀ p q, nfAll W.sgTrue p q = nfAll W.sgW p q := by
    intro p q
    have h3 : W.sgTrue = fun τ => shW (W.sgW τ) ((R.m * (R.t + 1) / 2 : ℕ) : ℤ) := funext fun τ => xp_sgTrue_eq (W.row τ)
    rw [h3]
    exact nfAll_shW _ _ _ _
  rw [hv, h2, vn_inv_natCast_re]

end GenP

section Rec

variable {d : ColDat} (a : ColArgs d)

def RowSame (d : ColDat) : Prop := ∀ u τ, RowPar.of (d.hcW u τ) = RowPar.of (d.hcW d.u₀ τ)

theorem sgT_eq (u : d.what₂.Word) : CF.sgT (D := d.colRec a) u = d.W.sgTrue :=
  funext fun τ => (xp_sgTrue_eq (d.W.row τ)).symm

def pCrd (hS : SpStd d.toColBase) (hH : HostHyp d) (u : d.what₂.Word) : PCrd (Pr := d.Pr) d.W d.levP d.σ₀ where
  toStepCrd := crdPr a hS hH
  lt := CF.sgT (D := d.colRec a) u
  hlt := sgT_eq a u

variable (hS : SpStd d.toColBase) (hH : HostHyp d) (hP : PtSurjP d) (u : d.what₂.Word)

def parabolicValuationAgreement (hR : RowSame d) :
    CF.ValPTied (D := d.colRec a) u (parabolicClassAgreement a hS hH hP u) where
  sg := fun τ i => by
    have h := xp_sg_tie (d.hcW u τ) i
    rw [hR u τ] at h
    exact h
  eW := xpEW (Pr := d.Pr) d.W d.levP d.σ₀ (pCrd a hS hH u)
  ptC := XpV.ptC (Pr := d.Pr) d.W d.levP d.sp.cm d.hX d.σ₀ d.star_cx hP (pCrd a hS hH u)
  ipP := XpV.ipP (Pr := d.Pr) d.W d.levP d.hX d.σ₀ d.star_cx (pCrd a hS hH u)
  rat := XpV.rat (Pr := d.Pr) d.W d.levP d.hX d.σ₀ d.star_cx (pCrd a hS hH u)
  lat := XpV.lat (Pr := d.Pr) d.W d.levP d.hX d.σ₀ d.star_cx d.what₂.places d.plEq d.plEq.surjective hH.val_eq (pCrd a hS hH u)

theorem normPTied (hR : RowSame d) :
    CF.NormPTie (parabolicValuationAgreement a hS hH hP u hR) :=
  XpV.norm (Pr := d.Pr) d.W d.levP d.hX d.σ₀ d.star_cx (pCrd a hS hH u)

end Rec

end Formalism.L2.Col
