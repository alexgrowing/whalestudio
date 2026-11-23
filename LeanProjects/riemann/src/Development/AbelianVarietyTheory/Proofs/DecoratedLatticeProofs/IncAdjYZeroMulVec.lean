import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SmallPair
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsSelfDualLatticeAtPlaceLatticeCompletion
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FractionalIdealCompletionLocallyPrincipal
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.EventuallyIncAMulMemIntAt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LatticeLocalEqIntegralAlmostAll
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilDatumAtPlaceEqLatticeIntertwinerMulDetChar
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SmulColMul

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Matrix ValuativeRel IsLocalRing
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.FinPl GlobalTheory.FinPlLoc GlobalTheory.IwaPlace NumberField Filter
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000

namespace GlobalTheory.GoodPos

variable {D : D7}

theorem incAdj_yZero_mulVec {V₀ W W₀ : HSp D} {ρ : ℕ} (d : HypDec W W₀ ρ) (r : Fin ρ) (hr : r.1 + 1 = ρ)
    (z : Fin V₀.rank → D.host.E) (a : AE D) (y : Fin V₀.rank → AE D) :
    (show Matrix (Fin W.rank) (Fin V₀.rank) (AE D) from d.incAdj V₀ (a • yZero V₀ ρ z)) *ᵥ y =
      colMul d.jY r (incA D D.host.xi0⁻¹ * hermAt V₀ y (a • ratV z)) := by
  have h1 : (incA D (-D.host.xi0⁻¹) • (adj (a • yZero V₀ ρ z) ⬝ gA V₀)) *ᵥ y =
      Pi.single r (incA D D.host.xi0⁻¹ * hermAt V₀ y (a • ratV z)) := by
    rw [smul_mulVec, ← mulVec_mulVec, herm_eq]
    generalize gA V₀ *ᵥ y = t
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, mulVec, dotProduct, adj, yZero, zEll, ell, Matrix.transpose_apply,
      Matrix.map_apply, Matrix.smul_apply, Matrix.neg_apply, vecMulVec_apply, RingHom.map_neg]
    by_cases hi : i = r
    · subst hi
      simp only [hr, if_true, mul_one, Pi.single_eq_same, mul_neg, RingHom.map_neg, neg_mul, Finset.sum_neg_distrib, neg_neg]
    · have : ¬ (i.1 + 1 = ρ) := fun h => hi (Fin.ext (by omega))
      simp only [this, if_false, mul_zero, neg_zero, RingHom.map_zero, zero_mul, Finset.sum_const_zero, Pi.single_eq_of_ne hi]
  change (d.jY ⬝ (incA D (-D.host.xi0⁻¹) • (adj (a • yZero V₀ ρ z) ⬝ gA V₀))) *ᵥ y = _
  rw [← mulVec_mulVec, h1, mulVec_single]
  funext k
  exact mul_comm _ _

theorem mxAt_mul {P : Pl D → Prop} {l m n : ℕ} (M : Mx D l m) {N : Mx D m n} (h : MxAt P N) : MxAt P (M ⬝ N) := fun i j => by
  rw [Matrix.mul_apply]; exact Ideal.sum_mem _ fun k _ => Ideal.mul_mem_left _ _ (h k j)

theorem mxAt_mul' {P : Pl D → Prop} {l m n : ℕ} {M : Mx D l m} (N : Mx D m n) (h : MxAt P M) : MxAt P (M ⬝ N) := fun i j => by
  rw [Matrix.mul_apply]; exact Ideal.sum_mem _ fun k _ => Ideal.mul_mem_right _ _ (h i k)

theorem mxAt_smul {P : Pl D → Prop} {m n : ℕ} (a : AE D) {N : Mx D m n} (h : MxAt P N) : MxAt P (a • N) := fun i j =>
  Ideal.mul_mem_left _ _ (h i j)

theorem mxAt_adj {x : Pl D} {m n : ℕ} {N : Mx D m n} (h : MxAt (· = x) N) : MxAt (· = x) (adj N) := fun i j =>
  id_conj (h j i)

def xiU (D : D7) : (AE D)ˣ := inU D.host.xi0 (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D)

theorem cA_xi : cA D (incA D D.host.xi0) = -incA D D.host.xi0 := by
  rw [FrameLat.cA_incA, GlobalTheory.DualPairCheck.star_purely_imaginary_eq_neg, RingHom.map_neg]

theorem cA_xi_inv : cA D (incA D D.host.xi0⁻¹) = -incA D D.host.xi0⁻¹ := by
  rw [FrameLat.cA_incA, star_inv₀, GlobalTheory.DualPairCheck.star_purely_imaginary_eq_neg, inv_neg, RingHom.map_neg]

theorem last_of {V₀ W W₀ : HSp D} {ρ : ℕ} (d : HypDec W W₀ ρ) (z : Fin V₀.rank → D.host.E) {M : Lat V₀} {LW : Lat W}
    (hM : IsSelfDualC V₀ M) (hLW : IsSelfDualC W LW) {x : Pl D} {α m : (AE D)ˣ} {b : Fin ρ → (AE D)ˣ}
    (hb : ∀ r : Fin ρ, r.1 + 1 = ρ → b r = xiU D * cU α * m)
    (hα : ∀ y, y ∈ latA W LW (· = x) ↔ ((α⁻¹ : (AE D)ˣ) : AE D) • y ∈ latV W LW (· = x))
    (hW : ∀ i, ∀ a ∈ idAt D (· = x), colMul d.jY i a ∈ latV W LW (· = x) ↔ cA D (b i : AE D) * a ∈ intAt D (· = x))
    (hz : ∀ a ∈ idAt D (· = x), a • ratV z ∈ latV V₀ M (· = x) ↔ ((m⁻¹ : (AE D)ˣ) : AE D) * a ∈ intAt D (· = x))
    (hρ : 0 < ρ) : ∀ a ∈ idAt D (· = x),
      d.incAdj V₀ (a • yZero V₀ ρ z) ∈ latO V₀ W (M : Set _) (LW : Set _) (· = x) ↔ a ∈ intAt D (· = x) := fun a ha => by
  have hsd := LocSD.isSDAt_latV D V₀ M x hM
  have hr : (⟨ρ - 1, by omega⟩ : Fin ρ).1 + 1 = ρ := by simp only; omega
  have hmx : MxAt (· = x) (d.incAdj V₀ (a • yZero V₀ ρ z)) :=
    mxAt_mul _ (mxAt_smul _ (mxAt_mul' _ (mxAt_adj fun i j => Ideal.mul_mem_right _ _ ha)))
  rw [LatMem.mem_latO_iff D V₀ W M LW hM hLW, and_iff_right hmx]
  have h1 := hz _ (Ideal.mul_mem_left _ (m : AE D) ha)
  rw [Units.inv_mul_cancel_left,
    hsd.2.2 (((m : AE D) * a) • ratV z) fun i => Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ ha)] at h1
  rw [← h1]
  refine forall₂_congr fun y hy => ?_
  rw [incAdj_yZero_mulVec d _ hr, hα, smul_colMul, hW _ _
    (Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _ (LocSD.hermAt_mem_idAt (hsd.1 y hy) _))), hb _ hr, ← int_neg,
    ← herm_conj V₀ y, int_conj, mul_smul]
  have e1 := herm_smul V₀ 1 m y (a • ratV z)
  rw [one_smul] at e1
  rw [e1, Units.val_mul, Units.val_mul, RingHom.map_mul, RingHom.map_mul, cU_val, cA_cA, xiU, inU_val, cA_xi]
  have e2 := α.mul_inv
  have e3 : incA D D.host.xi0 * incA D D.host.xi0⁻¹ = 1 := (xiU D).mul_inv
  refine iff_of_eq (congrArg (· ∈ _) ?_)
  linear_combination (incA D D.host.xi0 * incA D D.host.xi0⁻¹ * cA D m * hermAt V₀ y (a • ratV z)) * e2 +
    (cA D m * hermAt V₀ y (a • ratV z)) * e3

theorem herm_kap {L L'' S : HSp D} (τ : Matrix (Fin L.rank) (Fin L''.rank) D.host.E) (w : WO S L'') (l : Fin L.rank → AE D)
    (s : Fin S.rank → AE D) :
    hermAt S ((show Matrix (Fin S.rank) (Fin L.rank) (AE D) from kap τ S w) *ᵥ l) s =
      incA D (-D.host.xi0⁻¹) * hermAt L l ((rat τ : Mx D _ _) *ᵥ ((show Matrix (Fin L''.rank) (Fin S.rank) (AE D) from w) *ᵥ s)) := by
  rw [mulVec_mulVec]
  change hermAt S ((incA D (-D.host.xi0⁻¹) • (giA S ⬝ (adj (rat τ ⬝ w) ⬝ gA L))) *ᵥ l) s = _
  generalize ((rat τ : Mx D _ _) ⬝ w : Mx D L.rank S.rank) = u
  rw [herm_eq, herm_eq, mulVec_mulVec, Matrix.mul_smul, gA_giA_cancel, smul_mulVec, dotProduct_smul, smul_eq_mul,
    ← mulVec_mulVec, dotProduct_mulVec]
  congr 2
  funext i
  simp only [vecMul, mulVec, dotProduct, adj, map_sum, RingHom.map_mul, Matrix.transpose_apply, Matrix.map_apply]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

theorem kap_of {L L'' S : HSp D} (τ : Matrix (Fin L.rank) (Fin L''.rank) D.host.E) {ζ : Fin L.rank → D.host.E}
    {ζ₀ : Fin L''.rank → D.host.E} (hζ : IsLineVec L ζ) (hζ₀ : IsLineVec L'' ζ₀) {lam : D.host.E} (hlam : lam ≠ 0)
    (hτ : τ *ᵥ ζ₀ = lam • ζ) {LL : Lat L} {LZ : Lat L''} {LS : Lat S} (hLL : IsSelfDualC L LL) (hLZ : IsSelfDualC L'' LZ)
    (hLS : IsSelfDualC S LS) {x : Pl D} {α μ : (AE D)ˣ}
    (hα : ∀ (S : HSp D) (L : Lat S) y, y ∈ latA S L (· = x) ↔ ((α⁻¹ : (AE D)ˣ) : AE D) • y ∈ latV S L (· = x))
    (hμ : ∀ a ∈ idAt D (· = x), a • ratV ζ₀ ∈ latV L'' LZ (· = x) ↔ ((μ⁻¹ : (AE D)ˣ) : AE D) * a ∈ intAt D (· = x))
    (hm : ∀ a ∈ idAt D (· = x), a • ratV ζ ∈ latV L LL (· = x) ↔
      (((α * μ * inU lam hlam * (xiU D * cU α)⁻¹)⁻¹ : (AE D)ˣ) : AE D) * a ∈ intAt D (· = x)) :
    ∀ w ∈ latO S L'' (LS : Set _) (LZ : Set _) (· = x), kap τ S w ∈ latO L S (LL : Set _) (LS : Set _) (· = x) := by
  intro w hw
  rw [LatMem.mem_latO_iff D S L'' LS LZ hLS hLZ] at hw
  have hsd := LocSD.isSDAt_latV D S LS x hLS
  have hmx : MxAt (· = x) (kap τ S w) := mxAt_smul _ (mxAt_mul _ (mxAt_mul' _ (mxAt_adj (mxAt_mul _ hw.1))))
  rw [LatMem.mem_latO_iff D L S LL LS hLL hLS]
  refine ⟨hmx, fun l hl => ?_⟩
  have hn := line_norm hζ hLL hm
  obtain ⟨a, ha, rfl⟩ := line_vec hζ (latV_idAt hl)
  rw [hα]
  refine (hsd.2.2 _ ?_).2 ?_
  · exact fun i => Ideal.mul_mem_left _ _ (mulVec_mem_idAt _ (latV_idAt hl) i)
  intro s hs
  have h1 := (hα _ _ _).1 (hw.2 s hs)
  obtain ⟨a', ha', e'⟩ := line_vec hζ₀ (latV_idAt h1)
  rw [e'] at h1
  have e2 : (show Matrix (Fin L''.rank) (Fin S.rank) (AE D) from w) *ᵥ s = ((α : AE D) * a') • ratV ζ₀ := by
    rw [mul_smul, ← e', smul_smul, Units.mul_inv, one_smul]
  have e1 := herm_smul S ((α⁻¹ : (AE D)ˣ) : AE D) 1 ((show Matrix (Fin S.rank) (Fin L.rank) (AE D) from kap τ S w) *ᵥ a • ratV ζ) s
  rw [one_smul] at e1
  rw [e1, herm_kap, e2, mulVec_smul, rat_mulVec, hτ, ratV_smul, smul_smul, herm_smul, herm_rat]
  have h2 := int_mul ((hm a ha).1 hl) (int_conj.2 ((hμ a' ha').1 h1))
  rw [hn _ h2.1] at h2
  convert h2 using 1
  generalize hm' : α * μ * inU lam hlam * (xiU D * cU α)⁻¹ = m
  have f1 := m.mul_inv
  have f2 : cA D (μ : AE D) * cA D ((μ⁻¹ : (AE D)ˣ) : AE D) = 1 := (cU μ).mul_inv
  have f3 : cA D (m : AE D) = cA D α * cA D μ * cA D (incA D lam) * (-incA D D.host.xi0⁻¹ * (α⁻¹ : (AE D)ˣ)) := by
    rw [← hm', mul_inv]
    simp only [Units.val_mul, RingHom.map_mul, inU_val, cU_inv, cA_cA, xiU, inU_inv, cA_xi_inv]
  rw [f3]
  simp only [RingHom.map_mul, RingHom.map_neg, RingHom.map_one]
  generalize incA D (star ζ ⬝ᵥ L.gram *ᵥ ζ) = h
  linear_combination (cA D α * cA D (incA D lam) * incA D D.host.xi0⁻¹ * (α⁻¹ : (AE D)ˣ) * h * a * cA D a') * f2 +
    (cA D α * cA D (incA D lam) * incA D D.host.xi0⁻¹ * (α⁻¹ : (AE D)ˣ) * h * a * cA D a' * (cA D μ * cA D (μ⁻¹ : (AE D)ˣ))) * f1

section Split

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {p : SplitPt D k}

theorem isU_xi (h : p.UnitAA) : IsU p.v (xiU D : AE D) :=
  IsU.of_pres (xiU D).mul_inv (fun a ha => (h.1 a ha).1) fun a ha => (h.1 a ha).2

theorem isU_alpha (h : p.UnitAA) {L : HSp D} {ζ : Fin L.rank → D.host.E} (hζ : IsLineVec L ζ) {α : (AE D)ˣ}
    (hα : ∀ (S : HSp D) (L : Lat S) y, y ∈ latA S L (· = p.v) ↔ ((α⁻¹ : (AE D)ˣ) : AE D) • y ∈ latV S L (· = p.v)) :
    IsU p.v (α : AE D) := by
  obtain ⟨e, he, hg⟩ := line_gen hζ (GlobalTheory.WeilAtPlace.isSelfDualC_frameLat L).1 p.v
  refine IsU.inv (fun a ha => ?_) α.inv_mul
  have h1 := hα L (GlobalTheory.AdelicU.frameLat L) ((incA D e * a) • ratV ζ)
  have e1 : incA D e⁻¹ * incA D e = 1 := (inU e he).inv_mul
  rw [h.2, smul_smul, hg _ (Ideal.mul_mem_left _ _ ha), hg _ (Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _ ha)),
    mul_left_comm (incA D e⁻¹) ((α⁻¹ : (AE D)ˣ) : AE D), ← mul_assoc (incA D e⁻¹), e1, one_mul] at h1
  exact h1

theorem val_le_one {u : AE D} (h : IsU p.v u) : valuation k (p.pr u) ≤ 1 := by
  refine (p.int_iff _).2 ?_
  rw [p.sec_pr, mul_comm]
  exact ((h _ (FrameLat.e_mem_idAt p)).1 (FrameLat.e_mem_intAt p)).2

theorem val_eq_one {u : (AE D)ˣ} (h : IsU p.v (u : AE D)) : valuation k (p.pr u) = 1 := by
  have h1 := val_le_one h
  have h2 := val_le_one (h.inv u.mul_inv)
  have h3 : valuation k (p.pr u) * valuation k (p.pr (u⁻¹ : (AE D)ˣ)) = 1 := by
    rw [← map_mul, ← map_mul, u.mul_inv, map_one, map_one]
  exact le_antisymm h1 (by rw [← h3]; exact mul_le_of_le_one_right' h2)

end Split

end GlobalTheory.GoodPos

end
