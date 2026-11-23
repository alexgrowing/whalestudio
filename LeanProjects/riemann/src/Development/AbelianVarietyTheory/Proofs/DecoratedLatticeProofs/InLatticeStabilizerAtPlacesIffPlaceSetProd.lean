import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OneSubIdemQMulSelf
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinPl.KSplit

open GlobalTheory.FinPl.SetCut

variable {D : D7}

theorem idAt_mono {P P' : Pl D → Prop} (h : ∀ w, P w → P' w) {a : AE D} (ha : a ∈ idAt D P) : a ∈ idAt D P' := by
  rw [mem_supportedOnPlacesIdeal_iff_components_zero_elsewhere] at ha ⊢
  exact ⟨ha.1, fun w hw => ha.2 w fun h' => hw (h w h')⟩

theorem latV_mono (V : HSp D) (L : Lat V) {P P' : Pl D → Prop} (h : ∀ w, P w → P' w) : latV V L P ≤ latV V L P' := by
  apply AddSubgroup.closure_mono
  rintro y ⟨α, hα, h0, r⟩
  exact ⟨α, hα, fun v hv => h0 v fun h' => hv (h v h'), r⟩

theorem mul_mem_idAt {P R : Pl D → Prop} {c : AE D} (hc : ∀ w, ¬ R w → compAt D w c = 0) {a : AE D}
    (ha : a ∈ idAt D P) : c * a ∈ idAt D (fun p => P p ∧ R p) := by
  rw [mem_supportedOnPlacesIdeal_iff_components_zero_elsewhere] at ha ⊢
  refine ⟨by rw [RingHom.map_mul, ha.1, mul_zero], fun w hw => ?_⟩
  rw [RingHom.map_mul]
  by_cases h : R w
  · rw [ha.2 w fun h' => hw ⟨h', h⟩, mul_zero]
  · rw [hc w h, zero_mul]

theorem smul_mem_latV (V : HSp D) (L : Lat V) {P R : Pl D → Prop} (β : Af D.host.F) (hβ : β ∈ intAf D.host.F)
    (h0 : ∀ v, ¬ R v → evalV D.host.F v β = 0) {y : Fin V.rank → AE D} (hy : y ∈ latV V L P) :
    algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 β) • y ∈ latV V L (fun p => P p ∧ R p) := by
  have main : latV V L P ≤ (latV V L (fun p => P p ∧ R p)).comap
      (DistribSMul.toAddMonoidHom (Fin V.rank → AE D) (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 β))) := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨α, hα, hα0, a, ha, x, hx, rfl⟩
    refine AddSubgroup.subset_closure ⟨β * α, fun v => by rw [map_mul]; exact mul_mem (hβ v) (hα v), fun v hv => ?_,
      a, ha, x, hx, ?_⟩
    · rw [map_mul]
      by_cases h : R v
      · rw [hα0 v fun h' => hv ⟨h', h⟩, mul_zero]
      · rw [h0 v h, zero_mul]
    · funext i
      change (pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 : D.host.E)) * (pairA D.host.F 0 α ⊗ₜ[D.host.F] (a * x i)) = _
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
      congr 1
      exact Prod.ext (mul_zero _) rfl
  exact main hy

theorem indQ_int (Q : Finset (Pl D)) : indQ D Q ∈ intAf D.host.F := by
  intro v
  rw [evalV_indQ]
  split_ifs
  · exact one_mem _
  · exact zero_mem _

theorem indQc_int (Q : Finset (Pl D)) : 1 - indQ D Q ∈ intAf D.host.F := by
  intro v
  rw [map_sub, map_one]
  exact sub_mem (one_mem _) (indQ_int Q v)

abbrev eQ (Q : Finset (Pl D)) : AE D := algebraMap (AF D.host.F) (AE D) (idemQ D Q)

theorem eQ_off (Q : Finset (Pl D)) (w : Pl D) (hw : ¬ w ∈ Q) : compAt D w (eQ Q) = 0 := by
  rw [(parts_idemQ Q).2 w, if_neg hw]

theorem one_sub_eQ_off (Q : Finset (Pl D)) (w : Pl D) (hw : ¬ w ∉ Q) : compAt D w (1 - eQ Q) = 0 := by
  rw [RingHom.map_sub, RingHom.map_one, (parts_idemQ Q).2 w, if_pos (not_not.1 hw), sub_self]

theorem eQ_mul_of_in {P : Pl D → Prop} (Q : Finset (Pl D)) {a : AE D} (ha : a ∈ idAt D (fun p => P p ∧ p ∈ Q)) :
    eQ Q * a = a :=
  (mem_idAt_Q_iff Q a).1 (idAt_mono (fun _ h => h.2) ha)

theorem eQ_mul_of_out {P : Pl D → Prop} (Q : Finset (Pl D)) {a : AE D} (ha : a ∈ idAt D (fun p => P p ∧ p ∉ Q)) :
    eQ Q * a = 0 := by
  classical
  refine (mem_idOff_iff_mul (· ∈ Q) _ (parts_idemQ Q).1 (fun w => by convert (parts_idemQ Q).2 w) a).1 ?_
  simp only [idOff, Submodule.mem_iInf, RingHom.mem_ker, Subtype.forall]
  intro w hw
  exact ((mem_supportedOnPlacesIdeal_iff_components_zero_elsewhere _ _ _).1 ha).2 w fun h => h.2 hw

theorem one_sub_mul_eq {P : Pl D → Prop} (Q : Finset (Pl D)) {a : AE D} (ha : a ∈ idAt D P) :
    (1 - eQ Q) * a = algebraMap (AF D.host.F) (AE D) (idemQc D Q) * a := by
  rw [← sub_eq_zero]
  rw [mem_supportedOnPlacesIdeal_iff_components_zero_elsewhere] at ha
  apply CMAdele_eq_zero_of_infinite_and_finite_components_zero
  · rw [RingHom.map_sub, RingHom.map_mul, RingHom.map_mul, ha.1, mul_zero, mul_zero, sub_zero]
  · intro w
    rw [RingHom.map_sub, RingHom.map_mul, RingHom.map_mul, RingHom.map_sub, RingHom.map_one, (parts_idemQ Q).2 w,
      (parts_idemQc Q).2 w]
    split_ifs
    · rw [sub_self, sub_self]
    · rw [sub_zero, sub_self]

theorem mem_latV_iff_parts (V : HSp D) (L : Lat V) (P : Pl D → Prop) (Q : Finset (Pl D)) {y : Fin V.rank → AE D}
    (hy : ∀ i, y i ∈ idAt D P) :
    y ∈ latV V L P ↔ eQ Q • y ∈ latV V L (fun p => P p ∧ p ∈ Q) ∧
      (1 - eQ Q) • y ∈ latV V L (fun p => P p ∧ p ∉ Q) := by
  constructor
  · intro h
    refine ⟨smul_mem_latV V L (indQ D Q) (indQ_int Q) (fun v hv => by rw [evalV_indQ, if_neg hv]) h, ?_⟩
    have e : (1 - eQ Q) • y = algebraMap (AF D.host.F) (AE D) (idemQc D Q) • y :=
      funext fun i => one_sub_mul_eq Q (hy i)
    rw [e]
    exact smul_mem_latV V L (1 - indQ D Q) (indQc_int Q)
      (fun v hv => by rw [map_sub, map_one, evalV_indQ, if_pos (not_not.1 hv), sub_self]) h
  · rintro ⟨h1, h2⟩
    have e : y = eQ Q • y + (1 - eQ Q) • y := by rw [← add_smul, add_sub_cancel, one_smul]
    rw [e]
    exact add_mem (latV_mono V L (fun _ h => h.1) h1) (latV_mono V L (fun _ h => h.1) h2)

theorem mt_mul (V : HSp D) (a b : GA D V) : mt V (a * b) = mt V a * mt V b := rfl

theorem mt_inj (V : HSp D) {a b : GA D V} (h : mt V a = mt V b) : a = b :=
  Subtype.ext (Units.ext h)

theorem mulVec_mem (V : HSp D) {I : Ideal (AE D)} (M : Matrix (Fin V.rank) (Fin V.rank) (AE D))
    {y : Fin V.rank → AE D} (hy : ∀ i, y i ∈ I) (i : Fin V.rank) : (M *ᵥ y) i ∈ I := by
  simp only [Matrix.mulVec, dotProduct]
  exact I.sum_mem fun j _ => I.mul_mem_left _ (hy j)

section Ring

variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]

theorem cut_sub_one (c : A) (M : Matrix n n A) : c • M + (1 - c) • (1 : Matrix n n A) - 1 = c • (M - 1) := by
  module

theorem cut_mulVec (c : A) (M : Matrix n n A) (y : n → A) (hy : c • y = y) :
    (c • M + (1 - c) • (1 : Matrix n n A)) *ᵥ y = M *ᵥ y := by
  rw [add_mulVec, smul_mulVec, smul_mulVec, one_mulVec, ← mulVec_smul, hy, sub_smul, hy, one_smul, sub_self, add_zero]

theorem cut_mul_cut (c : A) (hc : c * c = c) (M : Matrix n n A) :
    (c • M + (1 - c) • (1 : Matrix n n A)) * ((1 - c) • M + (1 - (1 - c)) • (1 : Matrix n n A)) = M := by
  have h1 : c * (1 - c) = 0 := by linear_combination -hc
  have h2 : (1 - c) * c = 0 := by linear_combination -hc
  have h3 : (1 - c) * (1 - c) = 1 - c := by linear_combination hc
  simp only [sub_sub_cancel, add_mul, mul_add, smul_mul_smul_comm, h1, h2, h3, hc, zero_smul, mul_one, one_mul,
    zero_add, add_zero]
  module

theorem prod_parts (c : A) (a b : Matrix n n A) (ha : c • (a - 1) = a - 1) (hb : c • (b - 1) = 0) (y : n → A) :
    c • ((a * b) *ᵥ y) = a *ᵥ (c • y) ∧ (1 - c) • ((a * b) *ᵥ y) = b *ᵥ ((1 - c) • y) := by
  have h1 : c • b = c • (1 : Matrix n n A) := by rw [← sub_eq_zero, ← smul_sub, hb]
  have h2 : (1 - c) • a = (1 - c) • (1 : Matrix n n A) := by
    rw [← sub_eq_zero, ← smul_sub, sub_smul, ha, one_smul, sub_self]
  constructor
  · rw [← smul_mulVec, ← mul_smul_comm, h1, mul_smul_comm, mul_one, smul_mulVec, mulVec_smul]
  · rw [← smul_mulVec, ← smul_mul_assoc, h2, smul_mul_assoc, one_mul, smul_mulVec, mulVec_smul]

end Ring

theorem inK_cut (V : HSp D) (L : Lat V) {P R : Pl D → Prop} (ε : AF D.host.F) (hε : ε * ε = ε)
    (hoff : ∀ w, ¬ R w → compAt D w (algebraMap (AF D.host.F) (AE D) ε) = 0)
    (hone : ∀ a ∈ idAt D (fun p => P p ∧ R p), algebraMap (AF D.host.F) (AE D) ε * a = a)
    (hlat : ∀ y : Fin V.rank → AE D, (∀ i, y i ∈ idAt D P) → y ∈ latV V L P →
      algebraMap (AF D.host.F) (AE D) ε • y ∈ latV V L (fun p => P p ∧ R p))
    {κ : GA D V} (hκ : InK V L P κ) : InK V L (fun p => P p ∧ R p) (cutG V ε hε κ) := by
  have key : ∀ y : Fin V.rank → AE D, (∀ i, y i ∈ idAt D (fun p => P p ∧ R p)) →
      (y ∈ latV V L (fun p => P p ∧ R p) ↔ y ∈ latV V L P) := by
    intro y hy
    refine ⟨fun h => latV_mono V L (fun _ h => h.1) h, fun h => ?_⟩
    have e : algebraMap (AF D.host.F) (AE D) ε • y = y := funext fun i => hone _ (hy i)
    have := hlat y (fun i => idAt_mono (fun _ h => h.1) (hy i)) h
    rwa [e] at this
  refine ⟨(mem_congGrp_iff V _ _).2 fun i j => ?_, fun y hy => ?_⟩
  · rw [mt_cutG, cut_sub_one]
    exact mul_mem_idAt hoff ((mem_congGrp_iff V _ _).1 hκ.1 i j)
  · have e : algebraMap (AF D.host.F) (AE D) ε • y = y := funext fun i => hone _ (hy i)
    rw [mt_cutG, cut_mulVec _ _ _ e, key y hy, key _ (mulVec_mem V _ hy)]
    exact hκ.2 y fun i => idAt_mono (fun _ h => h.1) (hy i)

theorem inK_iff_prod : ∀ (D : D7) (V : HSp D) (L : Lat V) (P : Pl D → Prop) (Q : Finset (Pl D)) (κ : GA D V),
    InK V L P κ ↔ ∃ a b, InK V L (fun p => P p ∧ p ∈ Q) a ∧ InK V L (fun p => P p ∧ p ∉ Q) b ∧ κ = a * b := by
  intro D V L P Q κ
  have e1 : algebraMap (AF D.host.F) (AE D) (1 - idemQ D Q) = 1 - eQ Q := by rw [map_sub, map_one]
  constructor
  · intro hκ
    refine ⟨cutG V _ (idemQ_mul_self Q) κ, cutG V _ (one_sub_idemQ_mul_self Q) κ,
      inK_cut V L _ _ (eQ_off Q) (fun a ha => eQ_mul_of_in Q ha)
        (fun y hy h => ((mem_latV_iff_parts V L P Q hy).1 h).1) hκ,
      inK_cut V L _ _ (by rw [e1]; exact one_sub_eQ_off Q)
        (fun a ha => by rw [e1, sub_mul, eQ_mul_of_out Q ha, one_mul, sub_zero])
        (fun y hy h => by rw [e1]; exact ((mem_latV_iff_parts V L P Q hy).1 h).2) hκ, mt_inj V ?_⟩
    rw [mt_mul, mt_cutG, mt_cutG, e1]
    exact (cut_mul_cut _ (by rw [← map_mul, idemQ_mul_self]) _).symm
  · rintro ⟨a, b, ha, hb, rfl⟩
    have hA := (mem_congGrp_iff V _ _).1 ha.1
    have hB := (mem_congGrp_iff V _ _).1 hb.1
    refine ⟨mul_mem ((mem_congGrp_iff V _ _).2 fun i j => idAt_mono (fun _ h => h.1) (hA i j))
      ((mem_congGrp_iff V _ _).2 fun i j => idAt_mono (fun _ h => h.1) (hB i j)), fun y hy => ?_⟩
    have hp := prod_parts (eQ Q) (mt V a) (mt V b) (Matrix.ext fun i j => eQ_mul_of_in Q (hA i j))
      (Matrix.ext fun i j => eQ_mul_of_out Q (hB i j)) y
    rw [mem_latV_iff_parts V L P Q hy, mem_latV_iff_parts V L P Q (mulVec_mem V _ hy), mt_mul, hp.1, hp.2]
    exact and_congr (ha.2 _ fun i => mul_mem_idAt (eQ_off Q) (hy i))
      (hb.2 _ fun i => mul_mem_idAt (one_sub_eQ_off Q) (hy i))

end GlobalTheory.FinPl.KSplit

end
