import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SmulMtCutPartCompl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLatticeStabilizerOfLocalIntegralInBasis
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemLatOIffExistsActO
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatSelfDualOfUnimod
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

noncomputable section

namespace GlobalTheory.OffPartLattice

open GlobalTheory.StdFrames

variable {D : D7}

open Classical in

theorem cpt_idemSum {e : AE D} {P : Finset (Pl D.host.E)} (he : IsIdemSum e P) (Q : Pl D.host.E) :
    cpt Q (toEAf D e) = if Q ∈ P then 1 else 0 := by
  classical
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := he
  rw [map_sum, map_sum]
  have h : ∀ PP ∈ P, cpt Q (toEAf D (es PP)) = if Q = PP then 1 else 0 := fun PP hP => by
    by_cases hq : Q = PP
    · subst hq; rw [if_pos rfl]; exact (cpt_of_isIdemAt (hes _ hP)).1
    · rw [if_neg hq]; exact (cpt_of_isIdemAt (hes PP hP)).2 Q hq
  rw [Finset.sum_congr rfl h, Finset.sum_ite_eq]

open Classical in

theorem cpt_cA_idemSum (V : HSp D) {e : AE D} {P : Finset (Pl D.host.E)} (he : IsIdemSum e P) (Q : Pl D.host.E) :
    cpt Q (toEAf D (cA D e)) = if GlobalTheory.IdemSupport.cP Q ∈ P then 1 else 0 := by
  classical
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := he
  rw [map_sum, map_sum, map_sum]
  have hc := (GlobalTheory.IdemSupport.supported_group_and_prime_idempotents V).2.2.2
  have h : ∀ PP ∈ P, cpt Q (toEAf D (cA D (es PP))) = if GlobalTheory.IdemSupport.cP Q = PP then 1 else 0 := fun PP hP => by
    have hi := hc PP (GlobalTheory.IdemSupport.cP PP) (es PP) (hes PP hP) ((GlobalTheory.IdemSupport.isConjPl_iff PP _).2 rfl)
    by_cases hq : GlobalTheory.IdemSupport.cP Q = PP
    · subst hq
      rw [if_pos rfl, cP_cP] at *
      exact (cpt_of_isIdemAt hi).1
    · rw [if_neg hq]
      exact (cpt_of_isIdemAt hi).2 Q fun h' => hq (by rw [h', cP_cP])
  rw [Finset.sum_congr rfl h, Finset.sum_ite_eq]

theorem cpt_pair_zero (V : HSp D) {e : AE D} {P : Finset (Pl D.host.E)} (he : IsIdemSum e P) (Q : Pl D.host.E)
    (hQ : ∀ w ∈ P, Q.under (𝓞 D.host.F) ≠ w.under (𝓞 D.host.F)) : cpt Q (toEAf D (e + cA D e)) = 0 := by
  rw [map_add, map_add, cpt_idemSum he, cpt_cA_idemSum V he, if_neg, if_neg, add_zero]
  · exact fun h => hQ _ h (GlobalTheory.IdemSupport.under_cP Q).symm
  · exact fun h => hQ Q h rfl

theorem cpt_pair_one (V : HSp D) {e : AE D} {P : Finset (Pl D.host.E)} (he : IsIdemSum e P) (Q : Pl D.host.E)
    (hQ : ∃ w ∈ P, Q.under (𝓞 D.host.F) = w.under (𝓞 D.host.F)) : cpt Q (toEAf D (e + cA D e)) = 1 := by
  have h0 : cpt Q (toEAf D e) * cpt Q (toEAf D (cA D e)) = 0 := by
    rw [← map_mul, ← map_mul, he.2, map_zero, map_zero]
  rw [cpt_idemSum he, cpt_cA_idemSum V he] at h0
  rw [map_add, map_add, cpt_idemSum he, cpt_cA_idemSum V he]
  obtain ⟨w, hw, hu⟩ := hQ
  rcases GlobalTheory.IdemSupport.eq_or_eq_cP hu with rfl | rfl
  · rw [if_pos hw, one_mul] at h0
    rw [if_pos hw, h0, add_zero]
  · rw [cP_cP, if_pos hw, mul_one] at h0
    rw [cP_cP, if_pos hw, h0, zero_add]

end GlobalTheory.OffPartLattice

namespace GlobalTheory.OffPartLattice

open GlobalTheory.StdFrames Matrix

variable {D : D7}

theorem mix_map' {A B : Type} [CommRing A] [CommRing B] {n : Type} [DecidableEq n] (ψ : A →+* B) (f : A)
    (a : Matrix n n A) :
    (f • a + (1 - f) • (1 : Matrix n n A)).map ψ = ψ f • a.map ψ + (1 - ψ f) • (1 : Matrix n n B) := by
  ext i j
  by_cases h : i = j <;> simp [Matrix.one_apply, h]

theorem mix_conj' {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] (f : A) (β : GL n A)
    (y : Matrix n n A) :
    β.val * (f • y + (1 - f) • (1 : Matrix n n A)) * (β⁻¹).val =
      f • (β.val * y * (β⁻¹).val) + (1 - f) • (1 : Matrix n n A) := by
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_one, Units.mul_inv]

theorem finE_cutPart {a : AE D} (h : a * a = a) (hc : cA D a = a) (V : HSp D) (g : GA D V) :
    (Lev.finE V (cutPart a V g)).val = toEAf D a • (Lev.finE V g).val + (1 - toEAf D a) • (1 : Matrix _ _ (Lev.EAf D)) := by
  change (mt V (cutPart a V g)).map (toEAf D) = _
  rw [mt_cutPart h hc, mix_map']
  rfl

theorem inBasis_mix {n : ℕ} (β X Y : GL (Fin n) (Lev.EAf D)) (c : Lev.EAf D)
    (hX : X.val = c • Y.val + (1 - c) • (1 : Matrix (Fin n) (Fin n) (Lev.EAf D))) (Q : Pl D.host.E) :
    (cpt Q c = 0 → inBasis rfl β Q X = 1) ∧ (cpt Q c = 1 → inBasis rfl β Q X = inBasis rfl β Q Y) := by
  have hM : (β⁻¹ * X * β).val = c • (β⁻¹ * Y * β).val + (1 - c) • (1 : Matrix (Fin n) (Fin n) (Lev.EAf D)) := by
    have := mix_conj' c β⁻¹ Y.val
    rw [inv_inv] at this
    rw [Units.val_mul, Units.val_mul, hX, this, Units.val_mul, Units.val_mul]
  have h1 : (β⁻¹ * 1 * β : GL (Fin n) (Lev.EAf D)) = 1 := by group
  constructor
  · intro h0
    rw [← map_one (inBasis rfl β Q)]
    refine Units.ext (Matrix.ext fun i j => ?_)
    rw [inBasis_apply, inBasis_apply, hM, h1]
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add, map_mul, map_sub, map_one, h0, zero_mul,
      zero_add, sub_zero, one_mul, Units.val_one]
  · intro h0
    refine Units.ext (Matrix.ext fun i j => ?_)
    rw [inBasis_apply, inBasis_apply, hM]
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add, map_mul, map_sub, map_one, h0, one_mul,
      sub_self, zero_mul, add_zero]

theorem mulVec_mem_hatL_of_St {n : ℕ} {β : GL (Fin n) (Lev.EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)}
    (hβ : IsFrame β Λ) {x : GL (Fin n) (Lev.EAf D)} (hx : x ∈ St β) (v : Fin n → Lev.EAf D)
    (hv : v ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ) : x.val *ᵥ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ := by
  obtain ⟨y, rfl⟩ := hx
  rw [hβ] at hv ⊢
  intro i
  have e0 : β⁻¹ * frGL β y = intGL D.host.F D.host.E n y * β⁻¹ := by
    simp only [frGL, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply, MulAut.conj_apply]
    group
  have e : ((β⁻¹ : GL (Fin n) (Lev.EAf D)) : Matrix (Fin n) (Fin n) (Lev.EAf D)) * (frGL β y).val =
      (intGL D.host.F D.host.E n y).val * (β⁻¹ : GL (Fin n) (Lev.EAf D)).val := by
    rw [← Units.val_mul, e0, Units.val_mul]
  rw [Matrix.mulVec_mulVec, e, ← Matrix.mulVec_mulVec]
  simp only [Matrix.mulVec, dotProduct]
  exact Subring.sum_mem _ fun k _ => Subring.mul_mem _ (y.val i k).2 (hv k)

theorem actO_mem_latO_of (S T : HSp D) (g : GA D S) (h : GA D T)
    (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E))
    (hg : ∀ x ∈ Formalism.L2.Herm.hatL (F := D.host.F) ΛS, (mt S g).map (toEAf D) *ᵥ x ∈ Formalism.L2.Herm.hatL (F := D.host.F) ΛS)
    (hh : ∀ x ∈ Formalism.L2.Herm.hatL (F := D.host.F) ΛT, (mt T h).map (toEAf D) *ᵥ x ∈ Formalism.L2.Herm.hatL (F := D.host.F) ΛT)
    (u : WO S T)
    (hu : u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) :
    actO S T g h u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True := by
  induction hu using AddSubgroup.closure_induction with
  | mem u hu =>
    obtain ⟨α, hα, -, a, ha, s, hs, t, ht, rfl⟩ := hu
    have e := GlobalTheory.AdelicLatMove.rankOne_pure S T a s t 1 α
    rw [mul_one] at e
    rw [← e, GlobalTheory.AdelicLatMove.actO_rankOne]
    exact GlobalTheory.AdelicLatMove.rankOne_mem_latO S T ΛS ΛT a ha _
      (hg _ (GlobalTheory.AdelicLatMove.pure_mem_hatL ΛS 1 (one_mem _) s hs)) _
      (hh _ (GlobalTheory.AdelicLatMove.pure_mem_hatL ΛT α hα t ht))
  | zero => simp only [actO, Matrix.mul_zero, Matrix.zero_mul]; exact zero_mem _
  | add y z _ _ hy hz => simp only [actO, Matrix.mul_add, Matrix.add_mul] at hy hz ⊢; exact add_mem hy hz
  | neg y _ hy => simp only [actO, Matrix.mul_neg, Matrix.neg_mul] at hy ⊢; exact neg_mem hy

end GlobalTheory.OffPartLattice

namespace GlobalTheory.OffPartLattice

open GlobalTheory.StdFrames Matrix

variable {D : D7}

theorem isFrame_moved {n : ℕ} (Λ₀ Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) (β Uf : GL (Fin n) (Lev.EAf D))
    (hβ : IsFrame β Λ) (hU : ∀ v, v ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ₀ ↔ Uf.val *ᵥ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ) :
    IsFrame (Uf⁻¹ * β) Λ₀ := by
  intro x
  rw [hU, hβ]
  have e : ((Uf⁻¹ * β)⁻¹ : GL (Fin n) (Lev.EAf D)).val = (β⁻¹ : GL (Fin n) (Lev.EAf D)).val * Uf.val := by
    rw [_root_.mul_inv_rev, inv_inv, Units.val_mul]
  rw [e, ← Matrix.mulVec_mulVec]

theorem finE_cut_mem_St (V : HSp D) (β Uf K : GL (Fin V.rank) (Lev.EAf D)) (g : GA D V) (hg : Lev.finE V g = Uf⁻¹ * K * Uf)
    {P : Finset (Pl D.host.E)} {e : AE D} (he : IsIdemSum e P)
    (hK : ∀ Q : Pl D.host.E, (∀ w ∈ P, Q.under (𝓞 D.host.F) ≠ w.under (𝓞 D.host.F)) →
      inBasis rfl β Q K ∈ GlobalTheory.SplitWeil.KO (Kw Q) (Fin V.rank)) :
    Lev.finE V (cutPart (1 - (e + cA D e)) V g) ∈ St (Uf⁻¹ * β) := by
  have hf := idem_conj_sum (GlobalTheory.PlaceVec.idemSum_mul_self he) he.2
  have h2 := idem_compl hf
  have hX := finE_cutPart h2.1 h2.2 V g
  refine StabilizerBasis.GlobalTheory.CompanionTheory.StabBasis.mem_St_of_inBasis_mem_KO _ _ fun Q => ?_
  have hm := inBasis_mix (Uf⁻¹ * β) _ _ _ hX Q
  by_cases hQ : ∃ w ∈ P, Q.under (𝓞 D.host.F) = w.under (𝓞 D.host.F)
  · rw [hm.1 (by simp only [map_sub, map_one, cpt_pair_one V he Q hQ, sub_self])]
    exact one_mem _
  · push_neg at hQ
    rw [hm.2 (by simp only [map_sub, map_one, cpt_pair_zero V he Q hQ, sub_zero])]
    have e1 : (Uf⁻¹ * β)⁻¹ * (Uf⁻¹ * K * Uf) * (Uf⁻¹ * β) = β⁻¹ * K * β := by group
    have e2 : inBasis rfl (Uf⁻¹ * β) Q (Lev.finE V g) = inBasis rfl β Q K := by
      refine Units.ext (Matrix.ext fun a b => ?_)
      rw [inBasis_apply, inBasis_apply, hg, e1]
    rw [e2]
    exact hK Q hQ

end GlobalTheory.OffPartLattice

open GlobalTheory.OffPartLattice Matrix in

theorem GlobalTheory.OffPartLattice.offPart_keeps_stdLatO : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T},
    t ∈ U → ∀ {Φ : G.Datum} {β : CosFam G t} (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.top (j + 1))),
    finG (G.V (.top (j + 1))) k ∈ S.levTop t Φ β (j + 1) hj → ∀ e : AE D, IsIdemSum e (locPl G t) →
    ∀ u : WO (G.pS (.top t (j + 1) : Pair T)) (G.pT (.top t (j + 1) : Pair T)),
      u ∈ stdLatO S (.top t (j + 1)) ↔ ∃ u₀ ∈ stdLatO S (.top t (j + 1)),
        u = actO _ _ (cutPart (1 - (e + cA D e)) (G.V (.top (j + 1)))
          ((((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1)) : FinPt G (.top (j + 1))) : GA D (G.V (.top (j + 1)))))) 1 u₀ := by
  intro D T L sc G W U S t _ Φ β j hj k hk e he u
  have hdef : DefNode D.R.m (.top (j + 1)) := by show j + 1 ≤ D.R.m; omega
  have hfr := isFrame_moved (colLat (S.N.fr (.top (j + 1)))) (G.Λ (.top (j + 1))) (S.βp (j + 1))
    (Lev.finE (G.V (.top (j + 1))) (S.N.u (.top (j + 1))).1) (S.βp_is (j + 1) hdef) (S.N.u_lat _ hdef)
  have hk2 : finG (G.V (.top (j + 1))) k ∈ prodLev (S.βp (j + 1)) (locPl G t) (fun w => topRank_eq G t w hj.le)
      (fun w => (S.term t Φ β w).pr _ j.succ_pos hj) := hk
  have hSt := finE_cut_mem_St (G.V (.top (j + 1))) (S.βp (j + 1)) (Lev.finE (G.V (.top (j + 1))) (S.N.u (.top (j + 1))).1)
    (finG (G.V (.top (j + 1))) k) (((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1)) : FinPt G (.top (j + 1))) : GA D _)
    (by simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv]; rfl) he (fun Q hQ => by
      have h3 := (Subgroup.mem_inf.1 hk2).2
      rw [Subgroup.mem_iInf] at h3
      have h4 := h3 Q
      rw [Subgroup.mem_iInf] at h4
      exact Subgroup.mem_comap.1 (h4 hQ))
  have hpres : ∀ y : GA D (G.V (.top (j + 1))),
      Lev.finE (G.V (.top (j + 1))) y ∈ St ((Lev.finE (G.V (.top (j + 1))) (S.N.u (.top (j + 1))).1)⁻¹ * S.βp (j + 1)) →
      ∀ x ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat (S.N.fr (.top (j + 1)))),
        (mt (G.V (.top (j + 1))) y).map (toEAf D) *ᵥ x ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat (S.N.fr (.top (j + 1)))) :=
    fun y hy x hx => mulVec_mem_hatL_of_St hfr hy x hx
  have h1 : ∀ x ∈ Formalism.L2.Herm.hatL (F := D.host.F) (S.N.latT (.top t (j + 1))),
      (mt (G.pT (.top t (j + 1) : Pair T)) 1).map (toEAf D) *ᵥ x ∈ Formalism.L2.Herm.hatL (F := D.host.F) (S.N.latT (.top t (j + 1))) := by
    intro x hx
    rw [GlobalTheory.AdelicLatMove.mt_one, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mulVec]
    exact hx
  have key : ∀ g₂ : GA D (G.V (.top (j + 1))),
      Lev.finE (G.V (.top (j + 1))) g₂ ∈ St ((Lev.finE (G.V (.top (j + 1))) (S.N.u (.top (j + 1))).1)⁻¹ * S.βp (j + 1)) →
      (u ∈ stdLatO S (.top t (j + 1)) ↔ ∃ u₀ ∈ stdLatO S (.top t (j + 1)),
        u = actO (G.pS (.top t (j + 1) : Pair T)) (G.pT (.top t (j + 1) : Pair T)) g₂ 1 u₀) := by
    intro g₂ hg₂
    constructor
    · intro hu
      refine ⟨actO (G.pS (.top t (j + 1) : Pair T)) (G.pT (.top t (j + 1) : Pair T)) g₂⁻¹ 1⁻¹ u, ?_,
        (GlobalTheory.AdelicLatMove.actO_actO_inv (G.pS (.top t (j + 1) : Pair T)) (G.pT (.top t (j + 1) : Pair T)) g₂ 1 u).symm⟩
      exact actO_mem_latO_of (G.pS (.top t (j + 1) : Pair T)) (G.pT (.top t (j + 1) : Pair T)) g₂⁻¹ 1⁻¹
        (colLat (S.N.fr (.top (j + 1)))) (S.N.latT (.top t (j + 1)))
        (hpres _ (by rw [map_inv]; exact inv_mem hg₂)) (by rw [inv_one]; exact h1) u hu
    · rintro ⟨u₀, hu₀, rfl⟩
      exact actO_mem_latO_of (G.pS (.top t (j + 1) : Pair T)) (G.pT (.top t (j + 1) : Pair T)) g₂ 1
        (colLat (S.N.fr (.top (j + 1)))) (S.N.latT (.top t (j + 1))) (hpres _ hg₂) h1 u₀ hu₀
  exact key _ hSt
