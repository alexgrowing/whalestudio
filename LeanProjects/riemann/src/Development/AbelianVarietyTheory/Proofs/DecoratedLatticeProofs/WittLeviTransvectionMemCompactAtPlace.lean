import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacesToAdeles
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SpecialLinearGeneratedByTransvections
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsSelfDualLatticeAtPlaceLatticeCompletion

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.RootKeep

open GlobalTheory.IwaPlace

variable {D : D7} {S S₀ : HSp D} {ρ : ℕ}

theorem conj_mem_idAt {v : Pl D} {r : AE D} (hr : r ∈ idAt D (· = v)) : cA D r ∈ idAt D (· = v) := by
  obtain ⟨ε, hc, hε, hact⟩ := LocSD.exists_idem v
  rw [← hact r hr, RingHom.map_mul, hc]
  exact Ideal.mul_mem_right _ _ hε.1

theorem colMul_add {m n : ℕ} (x : Mx D m n) (l : Fin n) (a b : AE D) :
    colMul x l (a + b) = colMul x l a + colMul x l b := by
  funext k; exact add_mul _ _ _

theorem colMul_neg {m n : ℕ} (x : Mx D m n) (l : Fin n) (a : AE D) : colMul x l (-a) = -colMul x l a := by
  funext k; exact neg_mul _ _

theorem hermAt_colMul_jY (d : HypDec S S₀ ρ) (l : Fin ρ) (b : AE D) (x : Fin S.rank → AE D) :
    hermAt S (colMul d.jY l b) x = b * cA D ((d.pX *ᵥ x) l) := by
  have hg : ∀ k m, cA D (gA S k m) = gA S m k := fun k m => congrFun (congrFun (adj_gA S) m) k
  have hp : ∀ m, cA D (d.pX l m) = ∑ k, gA S m k * d.jY k l := fun m => by
    rw [d.pX_eq, Matrix.mul_apply, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [RingHom.map_mul, hg, mul_comm]
    exact congrArg _ (congrFun (congrFun (adj_adj d.jY) k) l)
  unfold hermAt colMul
  rw [Matrix.mulVec, dotProduct, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [RingHom.map_mul, hp, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

theorem pX_colMul_jX (d : HypDec S S₀ ρ) (l : Fin ρ) (a : AE D) : (d.pX *ᵥ colMul d.jX l a) l = a := by
  have h : (d.pX ⬝ d.jX) l l = 1 := by rw [d.pX_jX, Matrix.one_apply_eq]
  rw [Matrix.mul_apply] at h
  refine Eq.trans ?_ (mul_one a)
  rw [Matrix.mulVec, dotProduct, ← h, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  unfold colMul
  ring

theorem transv_mulVec (i j : Fin ρ) (r : AE D) (u : Fin ρ → AE D) (l : Fin ρ) :
    (transvection i j r *ᵥ u) l = u l + if l = i then r * u j else 0 := by
  rw [transvection, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.single_mulVec, Pi.add_apply, Function.update_apply]
  rfl

theorem adj_transv (i j : Fin ρ) (r : AE D) : adj (transvection i j r : Mx D ρ ρ) = transvection j i (cA D r) := by
  rw [transvection, transvection, adj_add, adj_one]
  congr 1
  funext a b
  change cA D (Matrix.single i j r b a) = _
  simp only [Matrix.single_apply]
  by_cases h : i = b ∧ j = a
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg (fun h' => h h'.symm), RingHom.map_zero]

theorem levi_maps (d : HypDec S S₀ ρ) {L : Lat S} {L₀ : Lat S₀} {v : Pl D} (hL : IsSelfDualC S L)
    (hM : MonoAt d L L₀ v) {i j : Fin ρ} (hij : i ≠ j) {r : AE D}
    (h : ∀ a ∈ idAt D (· = v), colMul d.jX j a ∈ latV S L (· = v) → colMul d.jX i (r * a) ∈ latV S L (· = v))
    {y : Fin S.rank → AE D} (hy : y ∈ latV S L (· = v)) :
    mt S (d.levi (GlobalTheory.GLGen.transvGL hij r)) *ᵥ y ∈ latV S L (· = v) := by
  obtain ⟨hs, -, hd⟩ := LocSD.isSDAt_latV D S L v hL
  have hX : ∀ x ∈ latV S L (· = v), colMul d.jX i (r * (d.pX *ᵥ x) j) ∈ latV S L (· = v) := fun x hx =>
    h _ (mulVec_mem_idAt _ (hs x hx) j) (((hM x).1 hx).1 j)
  obtain ⟨h1, h2, h3⟩ := (hM y).1 hy
  refine (hM _).2 ⟨fun l => ?_, fun l => ?_, ?_⟩
  · rw [Matrix.mulVec_mulVec, d.pX_levi, ← Matrix.mulVec_mulVec]
    change colMul d.jX l ((transvection i j r *ᵥ _) l) ∈ _
    rw [transv_mulVec, colMul_add]
    refine add_mem (h1 l) ?_
    split_ifs with hl
    · rw [hl]; exact hX y hy
    · have : colMul d.jX l 0 = 0 := funext fun k => zero_mul _
      rw [this]; exact zero_mem _
  · rw [Matrix.mulVec_mulVec, d.pY_levi, ← Matrix.mulVec_mulVec]
    change colMul d.jY l ((adj (transvection i j (-r) : Mx D ρ ρ) *ᵥ _) l) ∈ _
    rw [adj_transv, transv_mulVec, colMul_add]
    refine add_mem (h2 l) ?_
    split_ifs with hl
    · rw [hl, RingHom.map_neg, neg_mul, colMul_neg]
      refine neg_mem ((hd _ fun k => ?_).2 fun x hx => ?_)
      · exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ (mulVec_mem_idAt _ (hs y hy) i))
      · have h4 := (hd _ (hs _ (h2 i))).1 (h2 i) _ (hX x hx)
        rw [hermAt_colMul_jY, pX_colMul_jX, RingHom.map_mul] at h4
        rw [hermAt_colMul_jY]
        convert h4 using 1
        ring
    · have : colMul d.jY l 0 = 0 := funext fun k => zero_mul _
      rw [this]; exact zero_mem _
  · rwa [Matrix.mulVec_mulVec, d.wittDecomp_projAnisotropic_levi]

theorem levi_mem_grpAt (d : HypDec S S₀ ρ) {v : Pl D} {i j : Fin ρ} (hij : i ≠ j) {r : AE D}
    (hr : r ∈ idAt D (· = v)) : d.levi (GlobalTheory.GLGen.transvGL hij r) ∈ grpAt S (· = v) := by
  refine (mem_congGrp_iff S _ _).2 fun a b => ?_
  have e : mt S (d.levi (GlobalTheory.GLGen.transvGL hij r)) - 1 =
      d.jX ⬝ (Matrix.single i j r : Mx D ρ ρ) ⬝ d.pX + d.jY ⬝ (Matrix.single j i (cA D (-r)) : Mx D ρ ρ) ⬝ d.pY := by
    rw [d.mt_levi, ← d.sum_eq_one]
    change d.jX ⬝ (transvection i j r : Mx D ρ ρ) ⬝ d.pX + _ + d.jY ⬝ adj (transvection i j (-r) : Mx D ρ ρ) ⬝ d.pY - _ = _
    rw [adj_transv, transvection, transvection]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one]
    abel
  have k : ∀ (A : Mx D S.rank ρ) (B : Mx D ρ S.rank) (p q : Fin ρ) (s : AE D), s ∈ idAt D (· = v) →
      (A ⬝ (Matrix.single p q s : Mx D ρ ρ) ⬝ B) a b ∈ idAt D (· = v) := fun A B p q s hs => by
    rw [Matrix.mul_apply]
    refine Ideal.sum_mem _ fun k _ => Ideal.mul_mem_right _ _ ?_
    rw [Matrix.mul_apply]
    refine Ideal.sum_mem _ fun l _ => Ideal.mul_mem_left _ _ ?_
    rw [Matrix.single_apply]
    split_ifs
    · exact hs
    · exact zero_mem _
  rw [← Matrix.sub_apply, e, Matrix.add_apply]
  exact add_mem (k _ _ _ _ _ hr) (k _ _ _ _ _ (conj_mem_idAt (neg_mem hr)))

theorem inK_levi_transv : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (L : Lat S) (L₀ : Lat S₀) (v : Pl D), IsSelfDualC S L → MonoAt d L L₀ v → ∀ (i j : Fin ρ) (hij : i ≠ j) (r : AE D), r ∈ idAt D (· = v) → (∀ a ∈ idAt D (· = v), colMul d.jX j a ∈ latV S L (· = v) → colMul d.jX i (r * a) ∈ latV S L (· = v)) → InK S L (· = v) (d.levi (GlobalTheory.GLGen.transvGL hij r)) := by
  intro D S S₀ ρ d L L₀ v hL hM i j hij r hr h
  refine ⟨levi_mem_grpAt d hij hr, fun y _ => ⟨fun hy => levi_maps d hL hM hij h hy, fun hy => ?_⟩⟩
  have h' := levi_maps d hL hM hij (r := -r) (fun a ha hb => by
    rw [neg_mul, colMul_neg]; exact neg_mem (h a ha hb)) hy
  have e : GlobalTheory.GLGen.transvGL hij (-r) = (GlobalTheory.GLGen.transvGL hij r)⁻¹ := Units.ext rfl
  rwa [Matrix.mulVec_mulVec, ← mt_mul, ← map_mul, e, inv_mul_cancel, map_one, mt_one, Matrix.one_mulVec] at h'

end GlobalTheory.FinPl.RootKeep

end
