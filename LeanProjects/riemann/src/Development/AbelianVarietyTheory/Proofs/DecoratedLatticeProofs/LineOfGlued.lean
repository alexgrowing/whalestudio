import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LineLatAt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.NotLineLatAtZero
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsSumFrame
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemSmulOfMemFlagSubOne
import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.MiTop.GluedLine

open GlobalTheory.FinPl.FrameLat GlobalTheory.SeeSaw.LiftModel

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem pr_mem_of_intAt (p : SplitPt D k) {a : AE D} (ha : finPart D a ∈ intAE D) : p.pr a ∈ 𝒪[k] := by
  rw [p.int_iff, p.sec_pr, RingHom.map_mul]
  exact mul_mem_intAE (e_mem_intAt p).2 ha

theorem eq_sec_add (p : SplitPt D k) {a : AE D} (ha : a ∈ idAt D (· = p.v)) :
    a = p.sec (p.pr a) + cA D (p.sec (p.pr (cA D a))) := by
  rw [p.sec_pr, p.sec_pr, RingHom.map_mul, cA_cA, ← add_mul, (idem_iff p a).1 ha]

theorem mem_intAt_iff (p : SplitPt D k) {a : AE D} (ha : a ∈ idAt D (· = p.v)) :
    a ∈ intAt D (· = p.v) ↔ p.pr a ∈ 𝒪[k] ∧ p.pr (cA D a) ∈ 𝒪[k] := by
  refine ⟨fun h => ⟨pr_mem_of_intAt p h.2, pr_mem_of_intAt p ((cA_int_iff a).2 h.2)⟩, fun h => ⟨ha, ?_⟩⟩
  rw [eq_sec_add p ha, RingHom.map_add]
  exact add_mem ((p.int_iff _).1 h.1) ((cA_int_iff _).2 ((p.int_iff _).1 h.2))

theorem valuation_xi_zero_eq_one (p : SplitPt D k) (hp : p.UnitAA) : valuation k (p.pr (incA D D.host.xi0)) = 1 := by
  obtain ⟨h1, h2⟩ := hp.1 _ (e_mem_intAt p)
  have he : p.pr p.e = 1 := by rw [← sec_one, p.pr_sec]
  have h3 := pr_mem_of_intAt p h1.2
  have h4 := pr_mem_of_intAt p h2.2
  rw [RingHom.map_mul, he, mul_one, Valuation.mem_integer_iff] at h3 h4
  have h5 : valuation k (p.pr (incA D D.host.xi0)) * valuation k (p.pr (incA D D.host.xi0⁻¹)) = 1 := by
    rw [← map_mul, ← RingHom.map_mul, ← RingHom.map_mul, mul_inv_cancel₀ (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D), RingHom.map_one,
      RingHom.map_one, map_one]
  refine le_antisymm h3 ?_
  rw [← h5]
  exact mul_le_of_le_one_right' h4

theorem single_mem_glued_iff {n : Type} [DecidableEq n] (q : Unif k) (P : Pair k n) (t : k) :
    (Pi.single (Sum.inr 0) t : n ⊕ Fin 1 → k) ∈ gluedS q 1 P.ker P.vec ↔ t ∈ 𝒪[k] := by
  have h0 : (Pi.single (Sum.inr 0) t : n ⊕ Fin 1 → k) ∘ Sum.inl = 0 := by
    funext j
    simp
  rw [GlobalTheory.LevelUnfold.mem_gluedS, h0]
  constructor
  · rintro ⟨s, h1, h2⟩
    have h3 := (h2 0).1 rfl
    rw [Pi.single_eq_same] at h3
    rw [zero_sub, neg_mem_iff, Pair.mem_ker] at h1
    have h4 := (P.hasVal_vec.smul s).unique h1
    rw [mul_one, IsLocalRing.residue_eq_zero_iff, q.mem_max_iff] at h4
    obtain ⟨c, rfl⟩ := h4
    rw [h3, Unif.inv, Subring.coe_mul, ← mul_assoc, inv_mul_cancel₀ q.ne_zero, one_mul]
    exact c.2
  · intro ht
    refine ⟨q.1 * ⟨t, ht⟩, ?_, fun i => ⟨fun _ => ?_, fun hi => absurd hi (by omega)⟩⟩
    · rw [zero_sub]
      exact neg_mem (Pair.smul_mem_ker (Ideal.mul_mem_right _ _ q.mem_max) P.hasVal_vec.mem)
    · obtain rfl : i = 0 := Subsingleton.elim _ _
      rw [Pi.single_eq_same, Unif.inv, Subring.coe_mul, ← mul_assoc, inv_mul_cancel₀ q.ne_zero, one_mul]

theorem pair_sumFrame {p : SplitPt D k} {S A L : HSp D} (o : OrthDec S A L) (ζ : Fin L.rank → D.host.E) {n : Type} [Fintype n]
    [DecidableEq n] {β : Frame p A n} {β₀ : Frame p S (n ⊕ Fin 1)} (hs : IsSumFrame o ζ β β₀) (x : n ⊕ Fin 1 → k) (t : k) :
    ∑ i, ∑ j, (β₀.b *ᵥ x) i * p.pr (cA D (incA D (S.gram i j))) * (t * p.pr (incA D (star (vecB o ζ j)))) =
      t * (p.pr (incA D (star ζ ⬝ᵥ L.gram *ᵥ ζ)) * x (Sum.inr 0)) := by
  let f : D.host.E →+* k := p.pr.comp (incA D)
  let r : Fin S.rank → D.host.E := star (vecB o ζ) ᵥ* S.gram
  have hr : ∀ i, r i = ∑ j, star (S.gram i j) * star (vecB o ζ j) := fun i => by
    simp only [r, vecMul, dotProduct, Pi.star_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_comm, ← conjTranspose_apply, gram_conjTranspose]
  have h1 : ∑ i, ∑ j, (β₀.b *ᵥ x) i * p.pr (cA D (incA D (S.gram i j))) * (t * p.pr (incA D (star (vecB o ζ j)))) =
      t * ((f ∘ r) ⬝ᵥ β₀.b *ᵥ x) := by
    simp only [dotProduct, Function.comp_apply, hr, map_sum, map_mul, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    change _ * f (star (S.gram i j)) * (t * f (star (vecB o ζ j))) = _
    ring
  have hA : r ᵥ* o.iA = 0 := by
    simp only [r, vecB, star_mulVec, vecMul_vecMul, o.orth, vecMul_zero]
  have hB : r ⬝ᵥ vecB o ζ = star ζ ⬝ᵥ L.gram *ᵥ ζ := by
    rw [← o.isoB]
    simp only [r, vecB, star_mulVec, vecMul_vecMul, dotProduct_mulVec]
  have hA' : (f ∘ r) ᵥ* o.jA.map p.pr = 0 := by
    funext i
    have := RingHom.map_vecMul f o.iA r i
    rw [hA, Pi.zero_apply, map_zero] at this
    exact this.symm
  have hB' : (f ∘ r) ⬝ᵥ (fun i => p.pr (ratV (vecB o ζ) i)) = p.pr (incA D (star ζ ⬝ᵥ L.gram *ᵥ ζ)) := by
    rw [← hB]
    exact (RingHom.map_dotProduct f r (vecB o ζ)).symm
  rw [h1, hs, dotProduct_mulVec, vecMul_fromCols, ← vecMul_vecMul, hA', zero_vecMul, ← hB']
  congr 1
  simp [dotProduct, vecMul, Fintype.sum_sum_type]

theorem line_of_glued {p : SplitPt D k} {ρ : ℕ} {B : BesLev D ρ} {M : Lat B.V₀} {q : Unif k} {n : Type} [Fintype n] [DecidableEq n]
    {β : Frame p B.A n} {β₀ : Frame p B.V₀ (n ⊕ Fin 1)} {P : Pair k n} (hM : IsSelfDualC B.V₀ M) (hg : GluedCore B M q β β₀ P)
    {a : AE D} (ha : a ∈ idAt D (· = p.v)) :
    a • ratV (vecB B.o B.ζ) ∈ latV B.V₀ M (· = p.v) ↔ a ∈ intAt D (· = p.v) := by
  have hdec : a • ratV (vecB B.o B.ζ) = (fun i => p.sec ((β₀.b *ᵥ (Pi.single (Sum.inr 0) (p.pr a) : n ⊕ Fin 1 → k)) i)) +
      fun i => cA D (p.sec (p.pr (cA D a) * p.pr (incA D (star (vecB B.o B.ζ i))))) := by
    funext i
    have e := eq_sec_add p (Ideal.mul_mem_right (incA D (vecB B.o B.ζ i)) _ ha)
    rw [RingHom.map_mul, RingHom.map_mul (cA D), RingHom.map_mul, cA_incA] at e
    refine e.trans ?_
    rw [Pi.add_apply, mulVec_single, hg.sum]
    congr 2
    exact mul_comm _ _
  have hq : valuation k ((q.1 : 𝒪[k]) : k) ≠ 0 := by simpa using q.ne_zero
  have hu : valuation k (p.pr (incA D (star B.ζ ⬝ᵥ B.L.gram *ᵥ B.ζ)) * q.inv) = 1 := by
    rw [map_mul, hg.norm, Unif.inv, map_inv₀, mul_inv_cancel₀ hq]
  rw [hdec, decomp hM, ← hg.lat, single_mem_glued_iff, mem_intAt_iff p ha, csec_mem_iff hM]
  refine and_congr_right fun _ => ⟨fun h => ?_, fun h x hx => ?_⟩
  · have h1 := h _ ((hg.lat _).1 (GlobalTheory.LevelUnfold.mem_gluedS.2 ⟨1, (by simp : Sum.elim P.vec (fun _ => q.inv) ∘ Sum.inl - (1 : 𝒪[k]) • P.vec ∈ P.ker),
      fun i => ⟨fun _ => by simp, fun hi => absurd hi (by omega)⟩⟩))
    rw [pair_sumFrame B.o B.ζ hg.sum, Sum.elim_inr, Valuation.mem_integer_iff, map_mul, hu, mul_one] at h1
    exact h1
  · have hx' : x = β₀.b *ᵥ (β₀.b' *ᵥ x) := by rw [mulVec_mulVec, β₀.bb', one_mulVec]
    rw [hx'] at hx
    obtain ⟨s, -, hs⟩ := GlobalTheory.LevelUnfold.mem_gluedS.1 ((hg.lat _).2 hx)
    rw [hx', pair_sumFrame B.o B.ζ hg.sum, (hs 0).1 rfl, ← mul_assoc _ q.inv]
    exact mul_mem h (mul_mem ((Valuation.mem_integer_iff _ _).2 hu.le) s.2)

end GlobalTheory.MiTop.GluedLine

end
