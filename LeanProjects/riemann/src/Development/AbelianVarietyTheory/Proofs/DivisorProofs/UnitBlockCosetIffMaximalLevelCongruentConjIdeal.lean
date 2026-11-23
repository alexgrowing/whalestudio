import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodIdemEmpty
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardLatticeDoubleCosetClassesStabilisers
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsThetaFunctionStandardPairSecond
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentSumInfPartIntegralOneSubMem
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.BotSmallDict GlobalTheory.NormExact
open scoped Pointwise

noncomputable section

namespace GlobalTheory.BotSmallDict.CosetCong

open GlobalTheory.BotClassDict GlobalTheory.BotFormula

variable {D : D7}

theorem hatId_mul {I : Ideal (𝓞 D.host.E)} {x y : Formalism.MainNotions.StandardLatticesGL3.AE D} (hx : x ∈ hatId D I) (hy : y ∈ OhE D) :
    x * y ∈ hatId D I := by
  induction hx using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨b, hb, s, hs, rfl⟩ := hz
    exact AddSubgroup.subset_closure ⟨b, hb, s * y, mul_mem hs hy, by ring⟩
  | zero => rw [zero_mul]; exact zero_mem _
  | add u v _ _ hu hv => rw [add_mul]; exact add_mem hu hv
  | neg u _ hu => rw [neg_mul]; exact neg_mem hu

def rho (D : D7) : Formalism.MainNotions.StandardLatticesGL3.AE D →+* Lev.EAf D := (Lev.swapAE D).comp (toAfE D).toRingHom

theorem rho_finQ (z : Formalism.L2.Theta.AE D) : rho D (finQ D z) = toEAf D z := by
  change Lev.swapAE D (toAfE D (finQ D z)) = _
  rw [toAfE_finQ]
  rfl

theorem rho_int (y : Formalism.MainNotions.StandardLatticesGL3.AE D) : rho D y ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ↔ y ∈ OhE D := toAfE_int_iff y

theorem rho_bij : Function.Bijective (rho D) :=
  (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).bijective.comp (toAfE D).bijective

theorem rho_inc (b : 𝓞 D.host.E) :
    rho D (inc D (b : D.host.E)) = (Formalism.L2.DIV.oToS D.host.F D.host.E b : Lev.EAf D) := by
  rw [← finQ_inclR, rho_finQ]
  rfl

theorem mem_map_iff {A R S : Type} [CommRing A] [CommRing R] [CommRing S] (ρ : R →+* S) (hρ : Function.Bijective ρ)
    (O : Subring R) (O' : Subring S) (hO : ∀ y, ρ y ∈ O' ↔ y ∈ O) (ι : A → R) (ι' : A →+* O') (hι : ∀ b, ρ (ι b) = ι' b)
    (I : Ideal A) (y : R) :
    (∃ h : ρ y ∈ O', (⟨ρ y, h⟩ : O') ∈ I.map ι') ↔ y ∈ AddSubgroup.closure {y | ∃ b ∈ I, ∃ s ∈ O, y = ι b * s} := by
  constructor
  · rintro ⟨h, hI⟩
    have key : ∀ s ∈ I.map ι', ∀ u ∈ O, ∀ y, ρ y = s.1 →
        y * u ∈ AddSubgroup.closure {y | ∃ b ∈ I, ∃ s ∈ O, y = ι b * s} := by
      intro s hs
      induction hs using Submodule.span_induction with
      | mem s hs =>
        obtain ⟨b, hb, rfl⟩ := hs
        intro u hu y hy
        rw [← hι] at hy
        rw [hρ.1 hy]
        exact AddSubgroup.subset_closure ⟨b, hb, u, hu, rfl⟩
      | zero =>
        intro u _ y hy
        rw [hρ.1 (hy.trans (map_zero ρ).symm), zero_mul]
        exact zero_mem _
      | add s t _ _ hs ht =>
        intro w hw y hy
        obtain ⟨u, hu⟩ := hρ.2 s.1
        obtain ⟨v, hv⟩ := hρ.2 t.1
        have : y = u + v := hρ.1 (by rw [hy, map_add, hu, hv]; rfl)
        rw [this, add_mul]
        exact add_mem (hs w hw u hu) (ht w hw v hv)
      | smul a t _ ht =>
        intro w hw y hy
        obtain ⟨u, hu⟩ := hρ.2 a.1
        obtain ⟨v, hv⟩ := hρ.2 t.1
        have : y = v * u := hρ.1 (by rw [hy, map_mul, hu, hv, mul_comm]; rfl)
        rw [this, mul_assoc]
        exact ht _ (mul_mem ((hO u).1 (hu ▸ a.2)) hw) v hv
    have := key _ hI 1 (one_mem _) y rfl
    rwa [mul_one] at this
  · intro hy
    induction hy using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨b, hb, s, hs, rfl⟩ := hz
      have h1 : ι' b * ⟨ρ s, (hO s).2 hs⟩ ∈ I.map ι' := Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hb)
      rw [map_mul, hι]
      exact ⟨(ι' b * ⟨ρ s, (hO s).2 hs⟩).2, h1⟩
    | zero => rw [map_zero]; exact ⟨zero_mem _, zero_mem _⟩
    | add u v _ _ hu hv =>
      obtain ⟨h1, h2⟩ := hu
      obtain ⟨h3, h4⟩ := hv
      rw [map_add]
      exact ⟨add_mem h1 h3, add_mem h2 h4⟩
    | neg u _ hu =>
      obtain ⟨h1, h2⟩ := hu
      rw [map_neg]
      exact ⟨neg_mem h1, neg_mem h2⟩

theorem inId_rho (I : Ideal (𝓞 D.host.E)) (y : Formalism.MainNotions.StandardLatticesGL3.AE D) :
    GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.InId I (rho D y) ↔ y ∈ hatId D I :=
  mem_map_iff (rho D) rho_bij (OhE D) (Formalism.L2.Herm.intAf D.host.F D.host.E) rho_int (fun b : 𝓞 D.host.E => inc D (b : D.host.E))
    (Formalism.L2.DIV.oToS D.host.F D.host.E) rho_inc I y

theorem inId_iff (I : Ideal (𝓞 D.host.E)) (z : Formalism.L2.Theta.AE D) :
    GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.InId I (toEAf D z) ↔ finQ D z ∈ hatId D I := by
  rw [← rho_finQ, inId_rho]

theorem sgA_hatId {I : Ideal (𝓞 D.host.E)} {x : Formalism.MainNotions.StandardLatticesGL3.AE D} (hx : x ∈ hatId D I) :
    sgA D x ∈ hatId D (D.host.conj • I) := by
  induction hx using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨b, hb, s, hs, rfl⟩ := hz
    refine AddSubgroup.subset_closure ⟨D.host.conj • b, Ideal.smul_mem_pointwise_smul _ _ _ hb, sgA D s, Formalism.UG.P.csDual_sig_mem _ hs, ?_⟩
    rw [map_mul]
    rfl
  | zero => rw [map_zero]; exact zero_mem _
  | add u v _ _ hu hv => rw [map_add]; exact add_mem hu hv
  | neg u _ hu => rw [map_neg]; exact neg_mem hu

theorem conj_idem {e : Formalism.L2.Theta.AE D} {P : Finset (Formalism.L2.DIV.Pl D.host.E)} (c : Formalism.L2.DIV.Pl D.host.E → ℕ)
    (he : IsIdemSum e P) : finQ D (cA D e) ∈ OhE D ∧ 1 - finQ D (cA D e) ∈ hatId D (D.host.conj • modul P c) := by
  obtain ⟨-, h1, t, ht, h2⟩ := GlobalTheory.IdemSumIdeal.isIdemSum_props e P c he
  have hc : finQ D (cA D e) = sgA D (finQ D e) := finQ_sigR e
  have h3 : finQ D e ∈ OhE D := by
    rw [← rho_int, rho_finQ]
    exact h1
  have h4 : finQ D (1 - e) ∈ hatId D (modul P c) := by
    rw [← inId_iff, RingHom.map_sub, RingHom.map_one, ← h2]
    exact ⟨t.2, ht⟩
  rw [hc]
  refine ⟨Formalism.UG.P.csDual_sig_mem _ h3, ?_⟩
  have h5 := sgA_hatId h4
  rwa [map_sub, map_one, map_sub, map_one] at h5

theorem core {R : Type} [CommRing R] (O : Subring R) (J : AddSubgroup R) (hJ : ∀ x ∈ J, ∀ y ∈ O, x * y ∈ J)
    {n d o : ℕ} (ho : o + n = d) {a : R} (haO : a ∈ O) (ha : 1 - a ∈ J) (Y : Matrix (Fin d) (Fin n) R)
    (H : Matrix (Fin n) (Fin n) R) (hH : ∀ i j, H i j ∈ O)
    (hY : ∀ i j, Y i j - (if i.1 = o + j.1 then a else 0) ∈ J) :
    (∀ i j, (Y * H) i j - (if i.1 = o + j.1 then a else 0) ∈ J) ↔ ∀ i j, (H - 1) i j ∈ J := by
  let X : Matrix (Fin d) (Fin n) R := Matrix.of fun i j => if i.1 = o + j.1 then a else 0
  have hX : ∀ i j, X i j ∈ O := fun i j => by
    change (if i.1 = o + j.1 then a else 0) ∈ O
    split_ifs
    exacts [haO, zero_mem _]
  have hH1 : ∀ i j, (H - 1) i j ∈ O := fun i j => by
    rw [Matrix.sub_apply, Matrix.one_apply]
    refine sub_mem (hH i j) ?_
    split_ifs
    exacts [one_mem _, zero_mem _]
  have e : Y * H - X = (Y - X) * H + X * (H - 1) := by
    rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_one]
    abel
  have h1 : ∀ i j, ((Y - X) * H) i j ∈ J := fun i j => by
    rw [Matrix.mul_apply]
    exact sum_mem fun l _ => hJ _ (hY i l) _ (hH l j)
  have h2 : ∀ i j, ((Y * H) i j - (if i.1 = o + j.1 then a else 0) ∈ J) ↔ (X * (H - 1) : Matrix (Fin d) (Fin n) R) i j ∈ J := fun i j => by
    change (Y * H - X) i j ∈ J ↔ _
    rw [e, Matrix.add_apply]
    exact AddSubgroup.add_mem_cancel_left _ (h1 i j)
  simp only [h2]
  constructor
  · intro h i j
    have h3 := h ⟨o + i.1, by omega⟩ j
    rw [Matrix.mul_apply, Finset.sum_eq_single i] at h3
    · have h4 : X ⟨o + i.1, by omega⟩ i = a := if_pos rfl
      rw [h4] at h3
      have h5 : (H - 1) i j = (1 - a) * (H - 1) i j + a * (H - 1) i j := by ring
      rw [h5]
      exact add_mem (hJ _ ha _ (hH1 i j)) h3
    · intro l _ hl
      have h4 : X ⟨o + i.1, by omega⟩ l = 0 := if_neg fun h' => hl (Fin.ext (by simp only at h'; omega))
      rw [h4, zero_mul]
    · intro h'
      exact absurd (Finset.mem_univ i) h'
  · intro h i j
    rw [Matrix.mul_apply]
    exact sum_mem fun l _ => by rw [mul_comm]; exact hJ _ (h l j) _ (hX i l)

theorem congOne_inv {I : Ideal (𝓞 D.host.E)} {N : ℕ} {k : Formalism.MainNotions.StandardLatticesGL3.GA D N} (hk : k ∈ GlobalTheory.NormSum.intG D N)
    (h : CongOne D I k) : CongOne D I k⁻¹ := by
  intro i j
  have e : (k⁻¹).1.1 - 1 = -((k.1.1 - 1) * (k⁻¹).1.1) := by
    rw [Matrix.sub_mul, Matrix.one_mul, neg_sub, ← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel]
    rfl
  change ((k⁻¹).1.1 - 1) i j ∈ _
  rw [e, Matrix.neg_apply, Matrix.mul_apply]
  exact neg_mem (sum_mem fun l _ => hatId_mul (h i l) ((GlobalTheory.NormSum.mem_intG _).1 (inv_mem hk) l j).1)

theorem cosetFn_ne_zero {S T : HSp D} (a : Formalism.L2.Theta.AE D) (I : Ideal (𝓞 D.host.E)) (o : ℕ) (y : WO S T) :
    cosetFn a I (unitPt S T a o) y ≠ 0 ↔ IsHalf a y ∧
      ∀ i j, (y.map (finQ D)) i j - (if i.1 = o + j.1 then finQ D a else 0) ∈ hatId D I := by
  have : ∀ i j, GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.InId I (toEAf D (y i j - unitPt S T a o i j)) ↔
      (y.map (finQ D)) i j - (if i.1 = o + j.1 then finQ D a else 0) ∈ hatId D I := fun i j => by
    rw [inId_iff, map_sub, unitPt, apply_ite (finQ D), map_zero]
    rfl
  unfold cosetFn
  simp only [this]
  split_ifs with h
  · exact iff_of_true one_ne_zero h
  · exact iff_of_false (fun h' => h' rfl) h

theorem actO_inv_one (S T : HSp D) (g g' : Formalism.L2.Theta.GA D S) (y : WO S T) :
    actO S T g'⁻¹ 1 y = HMul.hMul (actO S T g⁻¹ 1 y : Matrix (Fin T.rank) (Fin S.rank) (Formalism.L2.Theta.AE D)) (Formalism.L2.Theta.mt S (g⁻¹ * g')) := by
  unfold actO Formalism.L2.Theta.mt
  rw [inv_inv, inv_inv, Matrix.mul_assoc _ (matHom S g).1, ← Units.val_mul, ← map_mul, mul_inv_cancel_left]

theorem coset_iff_congOne : ∀ {D : D7} (S T : HSp D), S.gram = 1 →
    ∀ (e : Formalism.L2.Theta.AE D) (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (c : Formalism.L2.DIV.Pl D.host.E → ℕ), IsIdemSum e P →
    ∀ o : ℕ, o + S.rank = T.rank → ∀ k ∈ GlobalTheory.NormSum.intG D S.rank, ∀ k' ∈ GlobalTheory.NormSum.intG D S.rank, ∀ g g' : Formalism.L2.Theta.GA D S,
    GlobalTheory.BotFormula.IsFinPt S g k → GlobalTheory.BotFormula.IsFinPt S g' k' → ∀ y : WO S T,
    cosetFn (cA D e) (D.host.conj • modul P c) (unitPt S T (cA D e) o) (actO S T g⁻¹ 1 y) ≠ 0 →
    (cosetFn (cA D e) (D.host.conj • modul P c) (unitPt S T (cA D e) o) (actO S T g'⁻¹ 1 y) ≠ 0 ↔
      CongOne D (D.host.conj • modul P c) (k'⁻¹ * k)) := by
  intro D S T hG e P c he o ho k hk k' hk' g g' hg hg' y hy
  obtain ⟨h1, h2⟩ := conj_idem c he
  have hkk := mul_mem (inv_mem hk) hk'
  have hfin : finStd S hG (g⁻¹ * g') = k⁻¹ * k' := by
    rw [map_mul, map_inv, finStd_of_isFinPt S hG hg, finStd_of_isFinPt S hG hg']
  have hM : (Formalism.L2.Theta.mt S (g⁻¹ * g')).map (finQ D) = (k⁻¹ * k').1.1 := by
    rw [← hfin]
    rfl
  have hc : CongOne D (D.host.conj • modul P c) (k'⁻¹ * k) ↔ CongOne D (D.host.conj • modul P c) (k⁻¹ * k') := by
    constructor
    · intro h
      have := congOne_inv (mul_mem (inv_mem hk') hk) h
      rwa [mul_inv_rev, inv_inv] at this
    · intro h
      have := congOne_inv hkk h
      rwa [mul_inv_rev, inv_inv] at this
  rw [cosetFn_ne_zero] at hy
  rw [hc, cosetFn_ne_zero, actO_inv_one S T g g' y, Matrix.map_mul, hM,
    core (OhE D) (hatId D (D.host.conj • modul P c)) (fun x hx y hy => hatId_mul hx hy) ho h1 h2 _ _
      (fun i j => ((GlobalTheory.NormSum.mem_intG _).1 hkk i j).1) hy.2]
  refine and_iff_right fun i j => ?_
  rw [Matrix.mul_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun l _ => by rw [← mul_assoc, hy.1 i l]

end GlobalTheory.BotSmallDict.CosetCong

end
