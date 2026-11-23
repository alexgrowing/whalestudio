import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.IotaDictAll

noncomputable section

open scoped Classical ComplexConjugate TensorProduct
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Matrix Formalism.L2.SG.TermOp Formalism.L2.SG.HidaSetting
  Formalism.L2.SG.Pf.unitaryCongruence Formalism.L2.SG.NormCut Formalism.L2.SG.Pf.BridgeRat

namespace Formalism.L2.SG.Pf.BridgeRA

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

theorem bezoutMo {v : VA X.B.I} (hv : v ∈ X.B.I.Lf) {N : ℕ} (hN : Nat.Coprime N X.B.g)
    (h : (N : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • v ∈ Mo X.B.I X.B.g (Set.range X.e0)) :
    v ∈ Mo X.B.I X.B.g (Set.range X.e0) := by
  have hb : ((N : ℤ) * Nat.gcdA N X.B.g + (X.B.g : ℤ) * Nat.gcdB N X.B.g) = 1 := by
    rw [← Nat.gcd_eq_gcd_ab, hN.gcd_eq_one]; rfl
  have e : v = ((Nat.gcdA N X.B.g : ℤ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • ((N : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • v) +
      ((Nat.gcdB N X.B.g : ℤ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • ((X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • v) := by
    rw [smul_smul, smul_smul, ← add_smul]
    have := congrArg (fun z : ℤ => (z : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F)) hb
    push_cast at this
    rw [show ((Nat.gcdA N X.B.g : ℤ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * (N : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) +
      ((Nat.gcdB N X.B.g : ℤ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * (X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) = 1 by
      linear_combination this, one_smul]
  rw [e]
  have sm : ∀ (z : ℤ) (w : VA X.B.I), w ∈ Mo X.B.I X.B.g (Set.range X.e0) →
      ((z : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F)) • w ∈ Mo X.B.I X.B.g (Set.range X.e0) := fun z w hw => by
    have : ((z : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F)) • w = (⟨_, intCast_mem _ z⟩ : IntAf X.B.I.F X.B.I.E) • w := rfl
    rw [this]; exact Submodule.smul_mem _ _ hw
  exact add_mem (sm _ _ h) (sm _ _ (mL_Mo X.B.I (smul_mem_mL X.B.I hv)))

theorem cE_mem (a : Fin D.R.rS) : ∃ c : ℕ, Nat.Coprime c X.B.g ∧
    (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • incl X.B.I (X.crd (X.eX a)) ∈ X.B.I.Lf := by
  obtain ⟨c, hc, hcm⟩ := (X.basisApprox a).1
  refine ⟨c, hc, ?_⟩
  have hmL : mL X.B.I X.B.g ≤ X.B.I.Lf := (Mo_le_Lf X).trans' (mL_Mo X.B.I)
  have e : (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • incl X.B.I (X.crd (X.eX a)) =
      (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • X.e0 a - (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (X.e0 a - incl X.B.I (X.crd (X.eX a))) := by
    rw [smul_sub]; abel
  rw [e]
  refine sub_mem ?_ (hmL hcm)
  have : (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • X.e0 a = (⟨_, natCast_mem _ c⟩ : IntAf X.B.I.F X.B.I.E) • X.e0 a := rfl
  rw [this]; exact Submodule.smul_mem _ _ (X.vectorsInLattice.1 a).1

theorem cF_mem (a : Fin D.R.rS) : ∃ c : ℕ, Nat.Coprime c X.B.g ∧
    (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • incl X.B.I (X.crd (X.fY a)) ∈ X.B.I.Lf := by
  obtain ⟨c, hc, hcm⟩ := (X.basisApprox a).2
  refine ⟨c, hc, ?_⟩
  have hmL : mL X.B.I X.B.g ≤ X.B.I.Lf := (Mo_le_Lf X).trans' (mL_Mo X.B.I)
  have e : (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • incl X.B.I (X.crd (X.fY a)) =
      (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • X.f0 a - (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (X.f0 a - incl X.B.I (X.crd (X.fY a))) := by
    rw [smul_sub]; abel
  rw [e]
  refine sub_mem ?_ (hmL hcm)
  have : (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • X.f0 a = (⟨_, natCast_mem _ c⟩ : IntAf X.B.I.F X.B.I.E) • X.f0 a := rfl
  rw [this]; exact Submodule.smul_mem _ _ (X.vectorsInLattice.1 a).2

theorem dense_hat (A : X.B.I.Gf) {Λ : Submodule (𝓞 D.host.E) (VS D).V}
    (hlat : ∀ y, y ∈ Λ ↔ hat X A y ∈ X.B.I.Lf) {w : VA X.B.I} (hw : w ∈ X.B.I.Lf) :
    ∃ y ∈ Λ, ∃ ℓ ∈ X.B.I.Lf, w = hat X A y + (X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • ℓ := by
  have hM := PIW.AdelClassFin.lattice_m_generation X.B.I A w hw
  set S : Set (VA X.B.I) := Set.range fun v : PIW.AdelClassFin.abelian₂ X.B.I A =>
    PIW.AdelClassFin.iv X.B.I (v : Fin X.B.I.n → X.B.I.E) with hS
  have hiv_smul : ∀ (a : 𝓞 X.B.I.E) (v : Fin X.B.I.n → X.B.I.E),
      PIW.AdelClassFin.iv X.B.I (a • v) = Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) (a : X.B.I.E) •
        PIW.AdelClassFin.iv X.B.I v := by
    intro a v; funext i
    simp [PIW.AdelClassFin.iv, Algebra.smul_def, map_mul]
  have claim : ∀ z ∈ Submodule.span (IntAf X.B.I.F X.B.I.E) S, ∃ v ∈ PIW.AdelClassFin.abelian₂ X.B.I A,
      ∃ z' ∈ Submodule.span (IntAf X.B.I.F X.B.I.E) S,
        z = PIW.AdelClassFin.iv X.B.I v + (X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • z' := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨v, rfl⟩ := hz
      exact ⟨v, v.2, 0, zero_mem _, by simp⟩
    | zero => exact ⟨0, zero_mem _, 0, zero_mem _, by funext i; simp [PIW.AdelClassFin.iv]⟩
    | add a b _ _ ha hb =>
      obtain ⟨v, hv, z', hz', rfl⟩ := ha
      obtain ⟨v', hv', z'', hz'', rfl⟩ := hb
      refine ⟨v + v', add_mem hv hv', z' + z'', add_mem hz' hz'', ?_⟩
      have : PIW.AdelClassFin.iv X.B.I (v + v') = PIW.AdelClassFin.iv X.B.I v + PIW.AdelClassFin.iv X.B.I v' := by
        funext i; simp [PIW.AdelClassFin.iv]
      rw [this, smul_add]; abel
    | smul o z _ hz =>
      obtain ⟨v, hv, z', hz', rfl⟩ := hz
      obtain ⟨a, r, hr, ho⟩ := PIW.AdelClassFin.dual_dense X.B.I.F X.B.I.E X.B.g
        (Nat.pos_of_ne_zero (Formalism.L2.SG.Pf.ChiNMul.gB_ne_zero X)) (o : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) o.2
      refine ⟨a • v, Submodule.smul_mem _ a hv,
        (⟨r, hr⟩ : IntAf X.B.I.F X.B.I.E) • PIW.AdelClassFin.iv X.B.I v + o • z',
        add_mem (Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨v, hv⟩, rfl⟩)) (Submodule.smul_mem _ _ hz'), ?_⟩
      rw [hiv_smul, Subring.smul_def, Subring.smul_def, Subring.smul_def, ho]
      simp only [mul_add, add_mul, add_smul, smul_add, smul_smul, mul_comm, mul_assoc, mul_left_comm]
      abel
  obtain ⟨v, hv, z', hz', he⟩ := claim _ hM
  have hz'L : X.B.I.fmat A⁻¹ *ᵥ z' ∈ X.B.I.Lf := by
    have hle : Submodule.span (IntAf X.B.I.F X.B.I.E) S ≤ X.B.I.Lf.comap (mvO X.B.I (X.B.I.fmat A⁻¹)) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨v, rfl⟩
      exact v.2
    exact hle hz'
  refine ⟨Formalism.L2.SG.Pf.LatDictK.vOf X v, ?_, X.B.I.fmat A⁻¹ *ᵥ z', hz'L, ?_⟩
  · rw [hlat]
    unfold hat
    rw [Formalism.L2.SG.Pf.LatDictK.crd_vOf]
    exact hv
  · have e1 : w = X.B.I.fmat A⁻¹ *ᵥ (X.B.I.fmat A *ᵥ w) := by
      rw [Matrix.mulVec_mulVec, NormCut.fmat_inv_mul, Matrix.one_mulVec]
    rw [e1, he, Matrix.mulVec_add, Matrix.mulVec_smul]
    unfold hat
    rw [Formalism.L2.SG.Pf.LatDictK.crd_vOf]
    rfl

theorem hat_NgX (A : X.B.I.Gf) {u : D.what₂.Word} {Λ : Submodule (𝓞 D.host.E) (VS D).V}
    (hlat : ∀ y, y ∈ Λ ↔ hat X A y ∈ X.B.I.Lf)
    (hfixE : ∀ a, hat X A (X.eX a) = incl X.B.I (X.crd (X.eX a)))
    (hfixF : ∀ a, hat X A (X.fY a) = incl X.B.I (X.crd (X.fY a))) (hTF : ∀ a, (X.Fu u).e a = X.eX a)
    {z : (VS D).V} (hz : z ∈ NgX Λ (gS D) (lf D (X.Fu u)) (lf D (X.Fu u))) :
    hat X A z ∈ Mo X.B.I X.B.g (Set.range X.e0) := by
  have hgS : ((gS D : ℕ) : D.host.E) = ((X.B.g : ℕ) : D.host.E) := by rw [X.g_eq]; rfl

  have hP : ∀ p ∈ Ideal.span {((gS D : ℕ) : 𝓞 D.host.E)} • Λ, hat X A p ∈ Mo X.B.I X.B.g (Set.range X.e0) := by
    intro p hp
    refine Submodule.smul_induction_on hp (fun r hr m hm => ?_) (fun x y hx hy => ?_)
    · obtain ⟨o, rfl⟩ := Ideal.mem_span_singleton'.1 hr
      have e : hat X A ((o * ((gS D : ℕ) : 𝓞 D.host.E)) • m) =
          (⟨_, inclE_int X o⟩ : IntAf X.B.I.F X.B.I.E) • ((X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • hat X A m) := by
        rw [← algebraMap_smul D.host.E, hat_smul, Subring.smul_def, smul_smul]
        congr 1
        simp only [map_mul, map_natCast, hgS]
      rw [e]
      exact mL_Mo X.B.I (Submodule.smul_mem _ _ (smul_mem_mL X.B.I ((hlat m).1 hm)))
    · rw [hat_add]; exact add_mem hx hy

  have hQ : ∀ q ∈ XLam Λ (lf D (X.Fu u)), hat X A q ∈ Mo X.B.I X.B.g (Set.range X.e0) := by
    intro q hq
    have hqΛ : q ∈ Λ := hq.1
    have hqL : hat X A q ∈ X.B.I.Lf := (hlat q).1 hqΛ
    have hqX : q ∈ Xsp (lf D (X.Fu u)) := hq.2
    have hspan : q ∈ Submodule.span D.host.E (Set.range X.eX) := by
      have e : Xsp (lf D (X.Fu u)) = Submodule.span D.host.E (Set.range X.eX) := by
        show Submodule.span D.host.E (Set.range (X.Fu u).e) = _
        rw [X.Fu_e u]
      rw [← e]; exact hqX
    obtain ⟨s, hs⟩ := (Submodule.mem_span_range_iff_exists_fun D.host.E).1 hspan
    have hcoef : ∀ b, (VS D).hT (X.fY b) q = s b := by
      intro b
      rw [← hs, map_sum]
      simp only [map_smul, smul_eq_mul, Formalism.L2.SG.Pf.hT_f_e X, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
        Finset.mem_univ, if_true]
    choose c hc hcF using fun b => cF_mem X b
    set N1 : ℕ := ∏ b, c b with hN1
    have hN1c : Nat.Coprime N1 X.B.g := Nat.Coprime.prod_left fun b _ => hc b
    set t : Fin D.R.rS → X.B.I.E ⊗[X.B.I.F] Af X.B.I.F :=
      fun a => Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) (X.ιE.symm (s a)) with ht
    have hct : ∀ a, (c a : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * t a ∈ IntAf X.B.I.F X.B.I.E := by
      intro a
      have h1 := hA_int X.B.I (hcF a) hqL
      rw [hA_smul_left, map_natCast, ← hfixF a, hA_hat, hcoef a] at h1
      exact h1
    have hot : ∀ a, (N1 : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * t a ∈ IntAf X.B.I.F X.B.I.E := by
      intro a
      have e : (N1 : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) =
          ((∏ b ∈ Finset.univ.erase a, c b : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * (c a : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) := by
        rw [hN1, ← Nat.cast_mul, Finset.prod_erase_mul _ _ (Finset.mem_univ a)]
      rw [e, mul_assoc]
      exact mul_mem (natCast_mem _ _) (hct a)
    have hhq : hat X A q = ∑ a, t a • incl X.B.I (X.crd (X.eX a)) := by
      rw [← hs, hat_sum]
      simp only [hat_smul, hfixE, ht]

    have hsmall : InAt X.B.I X.B.g X.B.g (∑ a, ((N1 : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * t a) •
        (X.e0 a - incl X.B.I (X.crd (X.eX a)))) :=
      InAt_sum X _ _ fun a _ => InAt_smul X (hot a) (X.basisApprox a).1
    obtain ⟨c2, hc2, hc2m⟩ := hsmall
    refine bezoutMo X hqL (N := c2 * N1) (Nat.Coprime.mul_left hc2 hN1c) ?_
    have e2 : ((c2 * N1 : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • hat X A q =
        (∑ a, ((c2 : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * ((N1 : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * t a)) • X.e0 a) -
        (c2 : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (∑ a, ((N1 : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * t a) •
          (X.e0 a - incl X.B.I (X.crd (X.eX a)))) := by
      rw [hhq, Finset.smul_sum, Finset.smul_sum]
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Nat.cast_mul]
      simp only [smul_sub, smul_smul, mul_assoc]
      abel
    rw [e2]
    refine sub_mem (sum_mem fun a _ => ?_) (mL_Mo X.B.I hc2m)
    have : ((c2 : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * ((N1 : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * t a)) • X.e0 a =
        (⟨_, mul_mem (natCast_mem _ c2) (hot a)⟩ : IntAf X.B.I.F X.B.I.E) • X.e0 a := rfl
    rw [this]; exact Submodule.smul_mem _ _ (sub_Mo X.B.I ⟨a, rfl⟩)
  obtain ⟨pq, hpq, q2, hq2, rfl⟩ := Submodule.mem_sup.1 hz
  obtain ⟨p, hp, q1, hq1, rfl⟩ := Submodule.mem_sup.1 hpq
  rw [hat_add, hat_add]
  exact add_mem (add_mem (hP p hp) (hQ q1 hq1)) (hQ q2 hq2)

theorem orth_of_eX {x : (VS D).V} {u : D.what₂.Word} (h : ∀ a, (VS D).hT (X.eX a) x = 0) :
    x ∈ orth (VS D) (Xsp (lf D (X.Fu u))) := by
  have e : Xsp (lf D (X.Fu u)) = Submodule.span D.host.E (Set.range X.eX) := by
    show Submodule.span D.host.E (Set.range (X.Fu u).e) = _
    rw [X.Fu_e u]
  rw [e]
  refine (Submodule.mem_iInf _).2 fun v => (Submodule.mem_iInf _).2 fun hv => ?_
  show (VS D).hT v x = 0
  induction hv using Submodule.span_induction with
  | mem v hv => obtain ⟨a, rfl⟩ := hv; exact h a
  | zero => simp
  | add v w _ _ hv hw => simp [hv, hw]
  | smul c v _ hv => simp [hv]

end Formalism.L2.SG.Pf.BridgeRA

namespace Formalism.L2.SG.Pf

open Formalism.L2.SG.Pf.BridgeRA

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem iotaBridgeRAC_holds : IotaBridgeRAC := by
  intro D X Y u Λ hΛ β b hb hK hN hRT j
  set A : X.B.I.Gf := ((Y.cs u).h ((Y.cs u).base Λ) : X.B.I.Gf) * X.xu u with hAdef
  set δ : X.B.I.Gf := A⁻¹ * b.2 * A with hδ
  have hbl : (Y.cs u).lamOf ((Y.cs u).base Λ) = Λ := (Y.cs u).base_lam Λ hΛ
  have hlat : ∀ y, y ∈ Λ ↔ hat X A y ∈ X.B.I.Lf := fun y => by
    have := (Y.cs u).lat_eq ((Y.cs u).base Λ) y
    rw [hbl] at this
    exact this
  have hfixE : ∀ a, hat X A (X.eX a) = incl X.B.I (X.crd (X.eX a)) := fun a => by
    unfold hat
    exact fixes_inv X (fixes_mul X (((Y.cs u).h ((Y.cs u).base Λ)).2 _ (Or.inl (Or.inl ⟨a, rfl⟩)))
      ((X.xu_fix u a).1))
  have hfixF : ∀ a, hat X A (X.fY a) = incl X.B.I (X.crd (X.fY a)) := fun a => by
    unfold hat
    exact fixes_inv X (fixes_mul X (((Y.cs u).h ((Y.cs u).base Λ)).2 _ (Or.inl (Or.inr ⟨a, rfl⟩)))
      ((X.xu_fix u a).2))
  have hTF : ∀ a, (X.Fu u).e a = X.eX a := (Formalism.L2.SG.Full.Full.frameTie (X := X) u u).1
  have hbwL : X.bw j ∈ X.B.I.Lf := (X.vectorsInLattice.2.2 j).1
  obtain ⟨y, hyΛ, ℓ, hℓ, hw⟩ := dense_hat X A hlat hbwL
  have hyL : hat X A y ∈ X.B.I.Lf := (hlat y).1 hyΛ
  set s : Fin D.R.rS → D.host.E := fun a => (VS D).hT (X.eX a) y with hs
  set t : Fin D.R.rS → X.B.I.E ⊗[X.B.I.F] Af X.B.I.F :=
    fun a => Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) (X.ιE.symm (s a)) with ht

  have hsmall : ∀ a, ∃ c : ℕ, Nat.Coprime c X.B.g ∧ ZMod' X.B.I X.B.g ((c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * t a) := by
    intro a
    obtain ⟨c, hc, hcm⟩ := (X.basisApprox a).1
    refine ⟨c, hc, ?_⟩
    have ht' : t a = hA X.B.I (incl X.B.I (X.crd (X.eX a))) (hat X A y) := by
      rw [← hfixE a, hA_hat]
    have e : (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * t a =
        (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * hA X.B.I (X.e0 a) (X.bw j) -
          (X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * ((c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * hA X.B.I (X.e0 a) ℓ) -
          hA X.B.I ((c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (X.e0 a - incl X.B.I (X.crd (X.eX a)))) (hat X A y) := by
      rw [ht', hA_smul_left, map_natCast, hA_sub_left]
      have hy' : hat X A y = X.bw j - (X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • ℓ := by rw [hw]; abel
      rw [hy']
      simp only [hA_sub_right, hA_smul_right]
      ring
    rw [e]
    refine Z_sub X.B.I X.B.g (Z_sub X.B.I X.B.g (Z_smul X.B.I X.B.g (natCast_mem _ c) ((X.weightVectorsIntegral j).2.2 a).1)
      ⟨_, mul_mem (natCast_mem _ c) (hA_int X.B.I (X.vectorsInLattice.1 a).1 hℓ), rfl⟩) ?_
    exact Z_hA_mL X hcm hyL
  choose c hc hcZ using hsmall
  choose c' hc' hcF using fun a => cF_mem X a
  set N : ℕ := ∏ a, (c a * c' a) with hNdef
  have hNc : Nat.Coprime N X.B.g := Nat.Coprime.prod_left fun a _ => Nat.Coprime.mul_left (hc a) (hc' a)

  set x : (VS D).V := (N : D.host.E) • y - ∑ a, ((N : D.host.E) * s a) • X.fY a with hx
  have hcorr : ∀ a, ((N : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * t a) • incl X.B.I (X.crd (X.fY a)) ∈ mL X.B.I X.B.g := by
    intro a
    obtain ⟨τ, hτ, hτe⟩ := hcZ a
    have e : (N : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) =
        ((∏ b ∈ Finset.univ.erase a, (c b * c' b) : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) *
          ((c a : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * (c' a : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F)) := by
      rw [hNdef, ← Nat.cast_mul, ← Nat.cast_mul, Finset.prod_erase_mul _ _ (Finset.mem_univ a)]
    have e2 : ((N : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * t a) • incl X.B.I (X.crd (X.fY a)) =
        (⟨_, mul_mem (natCast_mem _ (∏ b ∈ Finset.univ.erase a, (c b * c' b))) hτ⟩ : IntAf X.B.I.F X.B.I.E) •
          ((X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • ((c' a : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • incl X.B.I (X.crd (X.fY a)))) := by
      rw [Subring.smul_def, smul_smul, smul_smul, e]
      congr 1
      linear_combination ((∏ b ∈ Finset.univ.erase a, (c b * c' b) : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) *
        (c' a : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * hτe
    rw [e2]
    exact Submodule.smul_mem _ _ (smul_mem_mL X.B.I (hcF a))
  have hhatx : hat X A x = (N : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • hat X A y -
      ∑ a, ((N : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * t a) • incl X.B.I (X.crd (X.fY a)) := by
    rw [hx, hat_sub, hat_smul, hat_sum]
    simp only [hat_smul, hfixF, map_mul, map_natCast, ht]
  have hmx : (N : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • hat X A y - hat X A x ∈ mL X.B.I X.B.g := by
    rw [hhatx, sub_sub_cancel]
    exact sum_mem fun a _ => hcorr a
  have hxΛ : x ∈ Λ := by
    rw [hlat]
    have hmL : mL X.B.I X.B.g ≤ X.B.I.Lf := (Mo_le_Lf X).trans' (mL_Mo X.B.I)
    have : hat X A x = (N : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • hat X A y -
        ((N : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • hat X A y - hat X A x) := by abel
    rw [this]
    refine sub_mem ?_ (hmL hmx)
    have : (N : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • hat X A y = (⟨_, natCast_mem _ N⟩ : IntAf X.B.I.F X.B.I.E) • hat X A y := rfl
    rw [this]; exact Submodule.smul_mem _ _ hyL
  have hxo : ∀ a, (VS D).hT (X.eX a) x = 0 := by
    intro a
    rw [hx, map_sub, map_smul, map_sum]
    simp only [map_smul, smul_eq_mul, X.ef, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true, hs]
    ring
  have hxL : x ∈ Lrep Λ (lf D (X.Fu u)) := ⟨hxΛ, orth_of_eX X hxo⟩
  have hβx := hat_NgX X A hlat hfixE hfixF hTF (hRT x hxL)
  rw [hat_sub, hat_ratLink X A hb] at hβx

  have hδbw : (X.B.I.fmat δ - 1) *ᵥ X.bw j ∈ X.B.I.Lf := K_sub_mv X.B.I hK hbwL
  refine bezoutMo X hδbw hNc ?_
  have e3 : (N : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • ((X.B.I.fmat δ - 1) *ᵥ X.bw j) =
      (X.B.I.fmat δ *ᵥ hat X A x - hat X A x) +
        (X.B.I.fmat δ - 1) *ᵥ (((N : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • hat X A y - hat X A x) +
          (N : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • ((X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • ℓ)) := by
    rw [hw, ← Matrix.mulVec_smul, smul_add]
    simp only [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_add, Matrix.mulVec_sub]
    abel
  rw [e3]
  refine add_mem hβx (mL_Mo X.B.I ?_)
  rw [Matrix.sub_mulVec, Matrix.one_mulVec]
  have hm2 : ((N : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • hat X A y - hat X A x) +
      (N : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • ((X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • ℓ) ∈ mL X.B.I X.B.g := by
    refine add_mem hmx ?_
    have : (N : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • ((X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • ℓ) =
        (⟨_, natCast_mem _ N⟩ : IntAf X.B.I.F X.B.I.E) • ((X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • ℓ) := rfl
    rw [this]; exact Submodule.smul_mem _ _ (smul_mem_mL X.B.I hℓ)
  exact sub_mem (mem_mL_of_Kset X hK _ hm2) hm2

end Formalism.L2.SG.Pf
