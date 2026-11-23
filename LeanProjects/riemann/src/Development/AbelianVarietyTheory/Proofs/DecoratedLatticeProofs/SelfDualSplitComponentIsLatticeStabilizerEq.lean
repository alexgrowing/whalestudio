import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LatticeLocalEqIntegralAlmostAll
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PlaceIdempotentActsOnSupportedAndOff

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel ValuativeRel Matrix NumberField
open scoped Pointwise TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.FinPl.FrameLat

section General

variable {D : D7}

theorem mul_mem_intAE {x y : Af D.host.F ⊗[D.host.F] D.host.E} (hx : x ∈ intAE D) (hy : y ∈ intAE D) :
    x * y ∈ intAE D := by
  refine AddSubgroup.closure_induction₂ (p := fun x y _ _ => x * y ∈ intAE D) ?_ ?_ ?_ ?_ ?_ ?_ ?_ hx hy
  · rintro _ _ ⟨a, ha, u, rfl⟩ ⟨b, hb, v, rfl⟩
    refine AddSubgroup.subset_closure ⟨a * b, fun w => ?_, u * v, ?_⟩
    · rw [map_mul]; exact mul_mem (ha w) (hb w)
    · rw [Algebra.TensorProduct.tmul_mul_tmul]; rfl
  · intro x _; rw [zero_mul]; exact zero_mem _
  · intro x _; rw [mul_zero]; exact zero_mem _
  · intro x y z _ _ _ h1 h2; rw [add_mul]; exact add_mem h1 h2
  · intro x y z _ _ _ h1 h2; rw [mul_add]; exact add_mem h1 h2
  · intro x y _ _ h; rw [neg_mul]; exact neg_mem h
  · intro x y _ _ h; rw [mul_neg]; exact neg_mem h

theorem finPart_cA (x : AE D) : finPart D (cA D x) = sigR (Af D.host.F) D.sp.cm.sig (finPart D x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [RingHom.map_zero]
  | add x y hx hy => simp only [RingHom.map_add, hx, hy]
  | tmul a x => rfl

theorem sigR_mem_intAE {z : Af D.host.F ⊗[D.host.F] D.host.E} (hz : z ∈ intAE D) :
    sigR (Af D.host.F) D.sp.cm.sig z ∈ intAE D := by
  induction hz using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨a, ha, o, rfl⟩ := hw
    exact AddSubgroup.subset_closure ⟨a, ha, ⟨D.sp.cm.sig (o : D.host.E),
      (show IsIntegral ℤ (o : D.host.E) from o.2).map (D.sp.cm.sig : D.host.E →+* D.host.E).toIntAlgHom⟩, rfl⟩
  | zero => rw [RingHom.map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [RingHom.map_add]; exact add_mem hx hy
  | neg x _ hx => rw [RingHom.map_neg]; exact neg_mem hx

theorem cA_int_iff (a : AE D) : finPart D (cA D a) ∈ intAE D ↔ finPart D a ∈ intAE D := by
  refine ⟨fun h => ?_, fun h => by rw [finPart_cA]; exact sigR_mem_intAE h⟩
  rw [← cA_cA a, finPart_cA]; exact sigR_mem_intAE h

theorem cA_incA (x : D.host.E) : cA D (incA D x) = incA D (star x) := rfl

def row (S : HSp D) (s : Fin S.rank → D.host.E) (b : Fin S.rank) : D.host.E := ∑ k, star (s k) * S.gram k b

def pairing (S : HSp D) (s : Fin S.rank → D.host.E) (y : Fin S.rank → AE D) : AE D := ∑ b, incA D (row S s b) * y b

variable {S : HSp D} {L : Lat S}

theorem pairing_int (hL : IsSelfDualC S L) {P : Pl D → Prop} {s : Fin S.rank → D.host.E} (hs : s ∈ L)
    {y : Fin S.rank → AE D} (hy : y ∈ latV S L P) : finPart D (pairing S s y) ∈ intAE D := by
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨α, hα, -, c, hc, x, hx, rfl⟩ := hy
    rw [Set.mem_singleton_iff] at hc
    subst hc
    obtain ⟨o, ho⟩ := (hL.2 x).1 hx s hs
    have h : pairing S s (fun i => pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 * x i)) =
        pairA D.host.F 0 α ⊗ₜ[D.host.F] (o : D.host.E) := by
      have h1 : ∀ b, incA D (row S s b) * (pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 * x b)) =
          pairA D.host.F 0 α ⊗ₜ[D.host.F] (row S s b * x b) := fun b => by
        change ((1 : AF D.host.F) ⊗ₜ[D.host.F] row S s b) * _ = _
        rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, one_mul]
      simp only [pairing, h1, ← TensorProduct.tmul_sum]
      rw [ho, Finset.sum_comm]
      simp only [row, Finset.sum_mul]
    rw [h]
    exact AddSubgroup.subset_closure ⟨α, hα, o, rfl⟩
  | zero => simp only [pairing, Pi.zero_apply, mul_zero, Finset.sum_const_zero, RingHom.map_zero]; exact zero_mem _
  | add x y _ _ hx hy =>
    have h : pairing S s (x + y) = pairing S s x + pairing S s y := by
      simp only [pairing, Pi.add_apply, mul_add, Finset.sum_add_distrib]
    rw [h, RingHom.map_add]; exact add_mem hx hy
  | neg x _ hx =>
    have h : pairing S s (-x) = -pairing S s x := by
      simp only [pairing, Pi.neg_apply, mul_neg, Finset.sum_neg_distrib]
    rw [h, RingHom.map_neg]; exact neg_mem hx

theorem latV_supp {P : Pl D → Prop} {y : Fin S.rank → AE D} (hy : y ∈ latV S L P) (i : Fin S.rank) : y i ∈ idAt D P := by
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨α, -, hα, c, -, x, -, rfl⟩ := hy
    exact GlobalTheory.FinPl.LatMem.tmul_mem_idAt hα _
  | zero => exact zero_mem _
  | add x y _ _ hx hy => exact add_mem hx hy
  | neg x _ hx => exact neg_mem hx

theorem int_mul_mem {v : Pl D} {a : AE D} (ha : a ∈ intAt D (· = v)) {x : Fin S.rank → D.host.E} (hx : x ∈ L) :
    (fun i => a * incA D (x i)) ∈ latV S L (· = v) := by
  have key : ∀ w ∈ intAE D, (fun i => GlobalTheory.LatAlmostStd.plc v w * incA D (x i)) ∈ latV S L (· = v) := by
    intro w hw
    induction hw using AddSubgroup.closure_induction with
    | mem w hw =>
      obtain ⟨α, hα, o, rfl⟩ := hw
      have h := GlobalTheory.LatAlmostStd.intSupp_single_mul v hα
      refine AddSubgroup.subset_closure ⟨_, h.1, h.2, 1, rfl, o • x, L.smul_mem o hx, ?_⟩
      funext i
      rw [GlobalTheory.LatAlmostStd.plc_tmul]
      change _ * ((1 : AF D.host.F) ⊗ₜ[D.host.F] x i) = _
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      rfl
    | zero => simp only [AddMonoidHom.map_zero, zero_mul]; exact zero_mem _
    | add a b _ _ ha hb => simp only [AddMonoidHom.map_add, add_mul]; exact add_mem ha hb
    | neg a _ ha => simp only [AddMonoidHom.map_neg, neg_mul]; exact neg_mem ha
  have h := key _ ha.2
  rwa [GlobalTheory.LatAlmostStd.plc_finPart, GlobalTheory.LatAlmostStd.smul_eq_of_mem_idAt ha.1] at h

theorem exists_expansion (hL : IsSelfDualC S L) :
    ∃ (m : ℕ) (s s' : Fin m → Fin S.rank → D.host.E), (∀ l, s l ∈ L) ∧ (∀ l, s' l ∈ L) ∧
      ∀ (y : Fin S.rank → AE D) (a : Fin S.rank), y a = ∑ l, pairing S (s' l) y * incA D (s l a) := by
  obtain ⟨m, s, s', hs, hs', hd⟩ := GlobalTheory.FinPl.LatMem.exists_dualBasis S hL
  refine ⟨m, s, s', hs, hs', fun y a => ?_⟩
  have h1 : ∀ b, ∑ l, incA D (row S (s' l) b) * y b * incA D (s l a) = if a = b then y b else 0 := fun b => by
    have h2 : ∑ l, incA D (row S (s' l) b) * y b * incA D (s l a) = incA D (∑ l, s l a * row S (s' l) b) * y b := by
      rw [map_sum, Finset.sum_mul]
      exact Finset.sum_congr rfl fun l _ => by rw [RingHom.map_mul]; ring
    rw [h2]
    unfold row
    rw [hd]
    split_ifs
    · rw [RingHom.map_one, one_mul]
    · rw [RingHom.map_zero, zero_mul]
  simp only [pairing, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp only [h1, Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem mem_of_pairing (hL : IsSelfDualC S L) {v : Pl D} {y : Fin S.rank → AE D} (hy : ∀ i, y i ∈ idAt D (· = v))
    (h : ∀ s ∈ L, finPart D (pairing S s y) ∈ intAE D) : y ∈ latV S L (· = v) := by
  obtain ⟨m, s, s', hs, hs', hd⟩ := exists_expansion hL
  have h1 : y = ∑ l, fun a => pairing S (s' l) y * incA D (s l a) := by
    funext a; rw [Finset.sum_apply]; exact hd y a
  rw [h1]
  refine sum_mem fun l _ => int_mul_mem ⟨?_, h _ (hs' l)⟩ (hs l)
  exact Ideal.sum_mem _ fun b _ => Ideal.mul_mem_left _ _ (hy b)

theorem smul_mem (hL : IsSelfDualC S L) {v : Pl D} {y : Fin S.rank → AE D}
    (hy : y ∈ latV S L (· = v)) {a : AE D} (ha : a ∈ intAt D (· = v)) : a • y ∈ latV S L (· = v) := by
  refine mem_of_pairing hL (fun i => Ideal.mul_mem_right _ _ ha.1) fun s hs => ?_
  have h : pairing S s (a • y) = a * pairing S s y := by
    simp only [pairing, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun b _ => by ring
  rw [h, RingHom.map_mul]
  exact mul_mem_intAE ha.2 (pairing_int hL hs hy)

end General

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k)

theorem e_mul_sec (a : k) : p.e * p.sec a = p.sec a := by rw [← p.sec_pr, p.pr_sec]

theorem sec_mul (a b : k) : p.sec (a * b) = p.sec a * p.sec b := by
  calc p.sec (a * b) = p.sec (p.pr (p.sec a * p.sec b)) := by rw [map_mul p.pr, p.pr_sec, p.pr_sec]
    _ = p.e * (p.sec a * p.sec b) := p.sec_pr _
    _ = p.sec a * p.sec b := by rw [← mul_assoc, e_mul_sec]

theorem sec_mul_right (c : k) (a : AE D) : p.sec c * a = p.sec (c * p.pr a) := by
  rw [sec_mul, p.sec_pr, ← mul_assoc, mul_comm (p.sec c) p.e, e_mul_sec]

theorem cAe_mul_e : cA D p.e * p.e = 0 := by rw [mul_comm]; exact p.split.2.1

theorem idem_iff (a : AE D) : a ∈ idAt D (· = p.v) ↔ (p.e + cA D p.e) * a = a := by
  obtain ⟨ε, hε, hsum⟩ := p.above
  rw [hsum]; exact (GlobalTheory.FinPl.placeIdem_acts D p.v ε hε).1 a

theorem e_mem_idAt : p.e ∈ idAt D (· = p.v) := by
  rw [idem_iff, add_mul, p.split.1, cAe_mul_e, add_zero]

theorem sum_mem_idAt : p.e + cA D p.e ∈ idAt D (· = p.v) := by
  rw [idem_iff, add_mul, mul_add, mul_add, p.split.1, p.split.2.1, cAe_mul_e, ← map_mul, p.split.1]; abel

theorem sec_mem_idAt (c : k) : p.sec c ∈ idAt D (· = p.v) := by
  rw [← e_mul_sec]; exact Ideal.mul_mem_right _ _ (e_mem_idAt p)

theorem sec_one : p.sec 1 = p.e := by rw [← map_one p.pr, p.sec_pr, mul_one]

theorem e_mem_intAt : p.e ∈ intAt D (· = p.v) :=
  ⟨e_mem_idAt p, by rw [← sec_one]; exact (p.int_iff 1).1 (one_mem _)⟩

theorem sec_mem_intAt (c : k) (hc : c ∈ 𝒪[k]) : p.sec c ∈ intAt D (· = p.v) :=
  ⟨sec_mem_idAt p c, (p.int_iff c).1 hc⟩

variable {p} {S : HSp D} {n : Type} [Fintype n] [DecidableEq n]

def latW (β : Frame p S n) {L : Lat S} (hL : IsSelfDualC S L) : Submodule 𝒪[k] (n → k) where
  carrier := {x | (fun i => p.sec ((β.b *ᵥ x) i)) ∈ latV S L (· = p.v)}
  add_mem' := by
    intro x y hx hy
    have : (fun i => p.sec ((β.b *ᵥ (x + y)) i)) =
        (fun i => p.sec ((β.b *ᵥ x) i)) + (fun i => p.sec ((β.b *ᵥ y) i)) := by
      funext i; simp [Matrix.mulVec_add]
    simp only [Set.mem_setOf_eq] at *
    rw [this]; exact add_mem hx hy
  zero_mem' := by
    simp only [Set.mem_setOf_eq, Matrix.mulVec_zero, Pi.zero_apply, map_zero]
    exact zero_mem _
  smul_mem' := by
    intro c x hx
    have : (fun i => p.sec ((β.b *ᵥ (c • x)) i)) = p.sec (c : k) • (fun i => p.sec ((β.b *ᵥ x) i)) := by
      funext i
      rw [show (c • x : n → k) = (c : k) • x from rfl, Matrix.mulVec_smul]
      simp [sec_mul]
    simp only [Set.mem_setOf_eq] at *
    rw [this]; exact smul_mem hL hx (sec_mem_intAt p _ c.2)

theorem mt_sec (β : Frame p S n) (g : GL n k) (y : Fin S.rank → k) :
    mt S (β.gl g) *ᵥ (fun i => p.sec (y i)) = fun i => p.sec (((β.b * g.val * β.b') *ᵥ y) i) := by
  funext i
  rw [← β.gl_mat g]
  simp only [Matrix.mulVec, dotProduct, map_sum, Matrix.map_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [sec_mul, p.sec_pr, mul_comm p.e, mul_assoc, e_mul_sec]

theorem mt_csec (h : GA D S) (z : Fin S.rank → k) :
    mt S h *ᵥ (fun i => cA D (p.sec (z i))) =
      fun i => cA D (p.sec ((((mt S h).map (fun a => p.pr (cA D a))) *ᵥ z) i)) := by
  funext i
  simp only [Matrix.mulVec, dotProduct, map_sum, Matrix.map_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [sec_mul, p.sec_pr, mul_comm p.e, mul_assoc, e_mul_sec, map_mul, cA_cA]

theorem csec_mem_idAt (c : k) : cA D (p.sec c) ∈ idAt D (· = p.v) := by
  rw [idem_iff]
  have h : (p.e + cA D p.e) = cA D (p.e + cA D p.e) := by rw [RingHom.map_add, cA_cA, add_comm]
  rw [h, ← RingHom.map_mul, (idem_iff p _).1 (sec_mem_idAt p c)]

theorem pairing_sec (s : Fin S.rank → D.host.E) (u : Fin S.rank → k) :
    pairing S s (fun i => p.sec (u i)) = p.sec (∑ b, p.pr (incA D (row S s b)) * u b) := by
  rw [map_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [mul_comm, sec_mul_right, mul_comm]

theorem pairing_csec (s : Fin S.rank → D.host.E) (z : Fin S.rank → k) :
    pairing S s (fun i => cA D (p.sec (z i))) =
      cA D (p.sec (∑ i, ∑ j, p.pr (incA D (s i)) * p.pr (cA D (incA D (S.gram i j))) * z j)) := by
  rw [Finset.sum_comm, map_sum, map_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  have h : ∑ i, p.pr (incA D (s i)) * p.pr (cA D (incA D (S.gram i b))) = p.pr (cA D (incA D (row S s b))) := by
    simp only [row, map_sum, RingHom.map_mul, cA_incA (star _), star_star]
  rw [← Finset.sum_mul, h, mul_comm (p.pr _), ← sec_mul_right, RingHom.map_mul, cA_cA, mul_comm]

theorem sec_inc_mem {L : Lat S} {s : Fin S.rank → D.host.E} (hs : s ∈ L) :
    (fun i => p.sec (p.pr (incA D (s i)))) ∈ latV S L (· = p.v) := by
  simp only [p.sec_pr]
  exact int_mul_mem (e_mem_intAt p) hs

theorem exists_gen {L : Lat S} (hL : IsSelfDualC S L) :
    ∃ (m : ℕ) (s : Fin m → Fin S.rank → D.host.E) (c : Fin m → (Fin S.rank → k) → k), (∀ l, s l ∈ L) ∧
      (∀ u, u = ∑ l, c l u • fun a => p.pr (incA D (s l a))) ∧
      ∀ u : Fin S.rank → k, (fun i => p.sec (u i)) ∈ latV S L (· = p.v) → ∀ l, c l u ∈ 𝒪[k] := by
  obtain ⟨m, s, s', hs, hs', hd⟩ := exists_expansion hL
  refine ⟨m, s, fun l u => ∑ b, p.pr (incA D (row S (s' l) b)) * u b, hs, fun u => ?_, fun u hu l => ?_⟩
  · funext a
    have h := congrArg p.pr (hd (fun i => p.sec (u i)) a)
    simp only [pairing_sec, map_sum p.pr, RingHom.map_mul, p.pr_sec] at h
    rw [Finset.sum_apply]
    exact h
  · rw [p.int_iff, ← pairing_sec]
    exact pairing_int hL (hs' l) hu

theorem csec_mem_iff {L : Lat S} (hL : IsSelfDualC S L) (z : Fin S.rank → k) :
    (fun i => cA D (p.sec (z i))) ∈ latV S L (· = p.v) ↔ ∀ x : Fin S.rank → k,
      (fun i => p.sec (x i)) ∈ latV S L (· = p.v) →
        ∑ i, ∑ j, x i * p.pr (cA D (incA D (S.gram i j))) * z j ∈ 𝒪[k] := by
  constructor
  · intro hz x hx
    obtain ⟨m, s, c, hs, hc, hint⟩ := exists_gen (p := p) hL
    have h : ∑ i, ∑ j, x i * p.pr (cA D (incA D (S.gram i j))) * z j =
        ∑ l, c l x * ∑ i, ∑ j, p.pr (incA D (s l i)) * p.pr (cA D (incA D (S.gram i j))) * z j := by
      have hx' : ∀ i, x i = ∑ l, c l x * p.pr (incA D (s l i)) := fun i => by
        have := congrFun (hc x) i
        rwa [Finset.sum_apply] at this
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm (s := Finset.univ (α := Fin m))]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_comm (s := Finset.univ (α := Fin m))]
      refine Finset.sum_congr rfl fun j _ => ?_
      conv_lhs => rw [hx' i]
      simp only [Finset.sum_mul, mul_assoc]
    rw [h]
    refine sum_mem fun l _ => mul_mem (hint x hx l) ?_
    rw [p.int_iff, ← cA_int_iff, ← pairing_csec]
    exact pairing_int hL (hs l) hz
  · intro h
    refine mem_of_pairing hL (fun i => csec_mem_idAt _) fun s hs => ?_
    rw [pairing_csec, cA_int_iff, ← p.int_iff]
    exact h _ (sec_inc_mem hs)

theorem pairing_inv (h : GA D S) (x z : Fin S.rank → k) :
    ∑ i, ∑ j, (((mt S h).map p.pr) *ᵥ x) i * p.pr (cA D (incA D (S.gram i j))) *
        (((mt S h).map (fun a => p.pr (cA D a))) *ᵥ z) j =
      ∑ i, ∑ j, x i * p.pr (cA D (incA D (S.gram i j))) * z j := by
  have hu : ((mt S h).map (cA D))ᵀ * S.gram.map (incA D) * mt S h = S.gram.map (incA D) := h.2
  have hu2 := congrArg (fun M : Matrix (Fin S.rank) (Fin S.rank) (AE D) => M.map (p.pr.comp (cA D))) hu
  simp only [Matrix.map_mul] at hu2
  have hA : (((mt S h).map (cA D))ᵀ).map (p.pr.comp (cA D)) = ((mt S h).map p.pr)ᵀ := by
    ext i j; simp only [Matrix.map_apply, Matrix.transpose_apply, RingHom.comp_apply, cA_cA]
  rw [hA] at hu2
  have hform : ∀ a b : Fin S.rank → k, ∑ i, ∑ j, a i * p.pr (cA D (incA D (S.gram i j))) * b j =
      a ⬝ᵥ ((S.gram.map (incA D)).map (p.pr.comp (cA D))) *ᵥ b := fun a b => by
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, Matrix.map_apply, RingHom.comp_apply, mul_assoc]
  rw [hform, hform]
  conv_rhs => rw [← hu2]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec x, Matrix.vecMul_transpose]
  rfl

theorem gl_mem_grpAt (β : Frame p S n) (g : GL n k) : β.gl g ∈ grpAt S (· = p.v) := by
  have hmem : ∀ i j, (mt S (β.gl g) - 1) i j ∈ idAt D (· = p.v) := fun i j => by
    rw [← β.gl_supp g i j]; exact Ideal.mul_mem_right _ _ (sum_mem_idAt p)
  unfold grpAt congGrp
  rw [MonoidHom.mem_ker]
  apply Units.ext
  ext i j
  have h := Ideal.Quotient.eq.2 (hmem i j)
  change Ideal.Quotient.mk _ (mt S (β.gl g) i j) = (1 : Matrix (Fin S.rank) (Fin S.rank) _) i j
  rw [h, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

theorem decomp {L : Lat S} (hL : IsSelfDualC S L) (u z : Fin S.rank → k) :
    (fun i => p.sec (u i)) + (fun i => cA D (p.sec (z i))) ∈ latV S L (· = p.v) ↔
      (fun i => p.sec (u i)) ∈ latV S L (· = p.v) ∧ (fun i => cA D (p.sec (z i))) ∈ latV S L (· = p.v) := by
  constructor
  · intro h
    have h1 : p.e • ((fun i => p.sec (u i)) + (fun i => cA D (p.sec (z i)))) = fun i => p.sec (u i) := by
      funext i
      have h0 : p.e * cA D (p.sec (z i)) = 0 := by
        rw [← cA_cA p.e, ← map_mul, ← e_mul_sec p (z i), ← mul_assoc, cAe_mul_e, zero_mul, map_zero]
      simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, mul_add, e_mul_sec, h0, add_zero]
    have h2 := smul_mem hL h (e_mem_intAt p)
    rw [h1] at h2
    refine ⟨h2, ?_⟩
    have h3 := sub_mem h h2
    rwa [add_sub_cancel_left] at h3
  · rintro ⟨h1, h2⟩; exact add_mem h1 h2

theorem exists_lat : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : SplitPt D k) (S : HSp D) (n : Type) [Fintype n] [DecidableEq n] (β : Frame p S n) (L : Lat S), IsSelfDualC S L →
    ∃ Λ : Submodule 𝒪[k] (n → k), Λ.IsLattice k ∧ β.IsLat L Λ ∧ ∀ g, InK S L (· = p.v) (β.gl g) ↔ g • Λ = Λ := by
  intro D k _ _ _ _ p S n _ _ β L hL
  refine ⟨latW β hL, ?_, fun x => Iff.rfl, ?_⟩
  · obtain ⟨m, s, c, hs, hc, hint⟩ := exists_gen (p := p) hL
    have hexp : ∀ x : n → k, x = ∑ l, c l (β.b *ᵥ x) • (β.b' *ᵥ fun a => p.pr (incA D (s l a))) := fun x => by
      have h := congrArg (β.b' *ᵥ ·) (hc (β.b *ᵥ x))
      simp only [Matrix.mulVec_sum, Matrix.mulVec_smul] at h
      rwa [Matrix.mulVec_mulVec, β.b'b, Matrix.one_mulVec] at h
    refine ⟨?_, ?_⟩
    · refine Submodule.FG.of_le (Submodule.fg_span (Set.finite_range
        fun l : Fin m => β.b' *ᵥ fun a => p.pr (incA D (s l a)))) ?_
      intro x hx
      rw [hexp x]
      exact Submodule.sum_mem _ fun l _ =>
        Submodule.smul_mem _ (⟨_, hint _ hx l⟩ : 𝒪[k]) (Submodule.subset_span ⟨l, rfl⟩)
    · rw [eq_top_iff]
      intro x _
      rw [hexp x]
      refine Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
      change (fun i => p.sec ((β.b *ᵥ (β.b' *ᵥ fun a => p.pr (incA D (s l a)))) i)) ∈ latV S L _
      rw [Matrix.mulVec_mulVec, β.bb', Matrix.one_mulVec]
      exact sec_inc_mem (hs l)
  · intro g
    have key : ∀ x : n → k, mt S (β.gl g) *ᵥ (fun i => p.sec ((β.b *ᵥ x) i)) =
        fun i => p.sec ((β.b *ᵥ (g.val *ᵥ x)) i) := by
      intro x
      rw [mt_sec, Matrix.mulVec_mulVec, Matrix.mul_assoc, β.b'b, Matrix.mul_one, ← Matrix.mulVec_mulVec]
    constructor
    · rintro ⟨_, hmv⟩
      have hiff : ∀ x, x ∈ latW β hL ↔ g • x ∈ latW β hL := by
        intro x
        change _ ∈ latV S L _ ↔ (fun i => p.sec ((β.b *ᵥ (g.val *ᵥ x)) i)) ∈ latV S L _
        rw [hmv _ (fun i => sec_mem_idAt p _), key]
      ext x
      rw [GlobalTheory.LatPair.mem_smul_iff, hiff, smul_inv_smul]
    · intro hg
      have hinv : ∀ x, g • x ∈ latW β hL ↔ x ∈ latW β hL := by
        intro x
        conv_lhs => rw [← hg]
        rw [GlobalTheory.LatPair.mem_smul_iff, inv_smul_smul]
      refine ⟨gl_mem_grpAt β g, ?_⟩
      have hE : ∀ u : Fin S.rank → k, (fun i => p.sec (u i)) ∈ latV S L (· = p.v) ↔
          (fun i => p.sec (((β.b * g.val * β.b') *ᵥ u) i)) ∈ latV S L (· = p.v) := by
        intro u
        have hu : u = β.b *ᵥ (β.b' *ᵥ u) := by rw [Matrix.mulVec_mulVec, β.bb', Matrix.one_mulVec]
        have hAu : (β.b * g.val * β.b') *ᵥ u = β.b *ᵥ (g.val *ᵥ (β.b' *ᵥ u)) := by
          simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
        have h := hinv (β.b' *ᵥ u)
        change (fun i => p.sec ((β.b *ᵥ (g.val *ᵥ (β.b' *ᵥ u))) i)) ∈ latV S L _ ↔
          (fun i => p.sec ((β.b *ᵥ (β.b' *ᵥ u)) i)) ∈ latV S L _ at h
        rw [← hu, ← hAu] at h
        exact h.symm
      have hAA : ∀ x : Fin S.rank → k, (β.b * g.val * β.b') *ᵥ ((β.b * (g⁻¹).val * β.b') *ᵥ x) = x := by
        intro x
        rw [Matrix.mulVec_mulVec]
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc β.b' β.b, β.b'b, Matrix.one_mul, ← Matrix.mul_assoc g.val, Units.mul_inv,
          Matrix.one_mul, β.bb', Matrix.one_mulVec]
      have hunit : ∀ x z : Fin S.rank → k,
          ∑ i, ∑ j, ((β.b * g.val * β.b') *ᵥ x) i * p.pr (cA D (incA D (S.gram i j))) *
            (((mt S (β.gl g)).map (fun a => p.pr (cA D a))) *ᵥ z) j =
          ∑ i, ∑ j, x i * p.pr (cA D (incA D (S.gram i j))) * z j := by
        intro x z
        have h := pairing_inv (p := p) (β.gl g) x z
        rwa [β.gl_mat g] at h
      have hC : ∀ z : Fin S.rank → k, (fun i => cA D (p.sec (z i))) ∈ latV S L (· = p.v) ↔
          (fun i => cA D (p.sec ((((mt S (β.gl g)).map (fun a => p.pr (cA D a))) *ᵥ z) i))) ∈ latV S L (· = p.v) := by
        intro z
        rw [csec_mem_iff hL, csec_mem_iff hL]
        constructor
        · intro h x hx
          have hx' : (fun i => p.sec (((β.b * (g⁻¹).val * β.b') *ᵥ x) i)) ∈ latV S L (· = p.v) := by
            rw [hE, hAA]; exact hx
          have h2 := hunit ((β.b * (g⁻¹).val * β.b') *ᵥ x) z
          rw [hAA] at h2
          rw [h2]; exact h _ hx'
        · intro h x hx
          rw [← hunit x z]; exact h _ ((hE x).1 hx)
      intro y hy
      have hyd : y = (fun i => p.sec (p.pr (y i))) + (fun i => cA D (p.sec (p.pr (cA D (y i))))) := by
        funext i
        simp only [Pi.add_apply, p.sec_pr]
        rw [map_mul, cA_cA, ← add_mul]
        exact ((idem_iff p _).1 (hy i)).symm
      obtain ⟨u, z, rfl⟩ : ∃ u z : Fin S.rank → k, y = (fun i => p.sec (u i)) + (fun i => cA D (p.sec (z i))) :=
        ⟨_, _, hyd⟩
      rw [Matrix.mulVec_add, mt_sec β g u, mt_csec (β.gl g) z, decomp hL, decomp hL, hE u, hC z]

end GlobalTheory.FinPl.FrameLat
