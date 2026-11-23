import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MemLineIff
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IncAdjYZeroMulVec
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FinitePartTraceCharacterIdempotentInverseDiffere
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualLatticeRationalLineTraceFractionalIdeal
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSuppVecLocEq
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RangeBesselAnisotropicEmbeddingEqSecondModelSubg
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ThmSOwn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FinitePartMemFrameStabilizerIffLocalStabilizer

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Matrix ValuativeRel IsLocalRing
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.FinPl GlobalTheory.FinPlLoc GlobalTheory.IwaPlace NumberField Filter
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000

namespace GlobalTheory.LineIdeal

open GlobalTheory.GoodPos

variable {D : D7}

theorem herm_colY {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (i : Fin ρ) (a : AE D) (y : Fin S.rank → AE D) :
    hermAt S (colMul d.jY i a) y = a * cA D ((d.pX *ᵥ y) i) := by
  have e0 : colMul d.jY i a = a • fun k => d.jY k i := rfl
  have e1 := herm_smul S a 1 (fun k => d.jY k i) y
  rw [one_smul, RingHom.map_one, mul_one] at e1
  rw [e0, e1, ← herm_conj, herm_eq]
  congr 2
  have e2 : d.pX = adj d.jY ⬝ gA S := by
    change rat (d.e'ᴴ * S.gram) = _
    rw [rat_mul, rat_conjTranspose]; rfl
  rw [e2, ← mulVec_mulVec]
  rfl

theorem dual_line {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) {L : Lat S} {L₀ : Lat S₀} {x : Pl D} (hL : IsSelfDualC S L)
    (hm : MonoAt d L L₀ x) (i : Fin ρ) {b : (AE D)ˣ}
    (hX : ∀ a ∈ idAt D (· = x), colMul d.jX i a ∈ latV S L (· = x) ↔ ((b⁻¹ : (AE D)ˣ) : AE D) * a ∈ intAt D (· = x)) :
    ∀ a ∈ idAt D (· = x), colMul d.jY i a ∈ latV S L (· = x) ↔ cA D (b : AE D) * a ∈ intAt D (· = x) := fun a ha => by
  have hsd := LocSD.isSDAt_latV D S L x hL
  have he := idem_mem_intAt (D := D) (· = x)
  rw [hsd.2.2 (colMul d.jY i a) fun k => Ideal.mul_mem_right _ _ ha]
  constructor
  · intro H
    have h1 := H _ ((hX _ (Ideal.mul_mem_left _ (b : AE D) he.1)).2 (by rwa [Units.inv_mul_cancel_left]))
    have h2 : ∀ t : AE D, (d.pX *ᵥ colMul d.jX i t) i = t := fun t => by
      have : (d.pX *ᵥ colMul d.jX i t) i = t * (d.pX ⬝ d.jX) i i := by
        simp only [mulVec, dotProduct, colMul, Matrix.mul_apply, Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => by ring
      rw [this, d.pX_jX, Matrix.one_apply_eq, mul_one]
    rw [herm_colY, h2, RingHom.map_mul, cA_idem] at h1
    convert h1 using 1
    linear_combination (-cA D (b : AE D)) * (mem_idAt_iff _ a).1 ha
  · intro H y hy
    have h1 := (hX _ (mulVec_mem_idAt d.pX (hsd.1 y hy) i)).1 (((hm y).1 hy).1 i)
    have h2 := int_mul H (int_conj.2 h1)
    rw [herm_colY]
    convert h2 using 1
    have e : cA D (b : AE D) * cA D ((b⁻¹ : (AE D)ˣ) : AE D) = 1 := (cU b).mul_inv
    rw [RingHom.map_mul]
    linear_combination (-a * cA D ((d.pX *ᵥ y) i)) * e

theorem last_iff {V₀ W W₀ : HSp D} {ρ : ℕ} (d : HypDec W W₀ ρ) (z : Fin V₀.rank → D.host.E) {M : Lat V₀} {LW : Lat W}
    (hM : IsSelfDualC V₀ M) (hLW : IsSelfDualC W LW) {x : Pl D} {α m b : (AE D)ˣ} (r : Fin ρ) (hr : r.1 + 1 = ρ)
    (hb : b = xiU D * cU α * m)
    (hα : ∀ y, y ∈ latA W LW (· = x) ↔ ((α⁻¹ : (AE D)ˣ) : AE D) • y ∈ latV W LW (· = x))
    (hW : ∀ a ∈ idAt D (· = x), colMul d.jY r a ∈ latV W LW (· = x) ↔ cA D (b : AE D) * a ∈ intAt D (· = x)) :
    ∀ a ∈ idAt D (· = x), d.incAdj V₀ (a • yZero V₀ ρ z) ∈ latO V₀ W (M : Set _) (LW : Set _) (· = x) ↔
      ((m : AE D) * a) • ratV z ∈ latV V₀ M (· = x) := fun a ha => by
  have hsd := LocSD.isSDAt_latV D V₀ M x hM
  have hmx : MxAt (· = x) (d.incAdj V₀ (a • yZero V₀ ρ z)) :=
    mxAt_mul _ (mxAt_smul _ (mxAt_mul' _ (mxAt_adj fun i j => Ideal.mul_mem_right _ _ ha)))
  rw [LatMem.mem_latO_iff D V₀ W M LW hM hLW, and_iff_right hmx,
    hsd.2.2 (((m : AE D) * a) • ratV z) fun i => Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ ha)]
  refine forall₂_congr fun y hy => ?_
  rw [incAdj_yZero_mulVec d _ hr, hα, smul_colMul, hW _
    (Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _ (LocSD.hermAt_mem_idAt (hsd.1 y hy) _))), hb, ← int_neg,
    ← herm_conj V₀ y, int_conj, mul_smul]
  have e1 := herm_smul V₀ 1 m y (a • ratV z)
  rw [one_smul] at e1
  rw [e1, Units.val_mul, Units.val_mul, RingHom.map_mul, RingHom.map_mul, cU_val, cA_cA, xiU, inU_val, cA_xi]
  have e2 := α.mul_inv
  have e3 : incA D D.host.xi0 * incA D D.host.xi0⁻¹ = 1 := (xiU D).mul_inv
  refine iff_of_eq (congrArg (· ∈ _) ?_)
  linear_combination (incA D D.host.xi0 * incA D D.host.xi0⁻¹ * cA D m * hermAt V₀ y (a • ratV z)) * e2 +
    (cA D m * hermAt V₀ y (a • ratV z)) * e3

theorem int_of_smul {S : HSp D} (hS : 0 < S.rank) {L : Lat S} (hL : IsSelfDualC S L) {x : Pl D} {u : AE D}
    (h : ∀ s ∈ latV S L (· = x), u • s ∈ latV S L (· = x)) : ∀ t ∈ intAt D (· = x), u * t ∈ intAt D (· = x) := fun t ht => by
  obtain ⟨𝔞, h0, -, h1⟩ := GlobalTheory.Core.Mi.LatLine.line_trace D S L (fun _ => 1) hL
    (fun e => one_ne_zero (congrFun e ⟨0, hS⟩))
  obtain ⟨g, hg, hgen⟩ := GlobalTheory.IdVGen.idV_gen D x 𝔞 h0
  have e1 : incA D g⁻¹ * incA D g = 1 := (inU g hg).inv_mul
  have ha : incA D g * t ∈ idAt D (· = x) := Ideal.mul_mem_left _ _ ht.1
  have h2 := h _ ((h1 x _ ha).2 ((hgen _).2 ⟨by rwa [← mul_assoc, e1, one_mul], ha⟩))
  rw [smul_smul, h1 x _ (Ideal.mul_mem_left _ _ ha), hgen] at h2
  convert h2.1 using 1
  linear_combination (-u * t) * e1

theorem isU_of_norm {x : Pl D} {u : AE D} (h : ∀ t ∈ intAt D (· = x), u * t ∈ intAt D (· = x)) (hn : IsU x (u * cA D u)) :
    IsU x u := fun a ha => ⟨h a, fun H => by
  have h1 := int_conj.2 (h _ (int_conj.2 H))
  rw [RingHom.map_mul, cA_cA, ← mul_assoc, mul_comm (cA D u)] at h1
  exact (hn a ha).2 h1⟩

theorem kap_test {L L'' S : HSp D} (τ : Matrix (Fin L.rank) (Fin L''.rank) D.host.E) {ζ : Fin L.rank → D.host.E}
    {ζ₀ : Fin L''.rank → D.host.E} {lam : D.host.E}
    (hτ : τ *ᵥ ζ₀ = lam • ζ) {LL : Lat L} {LZ : Lat L''} {LS : Lat S} (hLL : IsSelfDualC L LL) (hLZ : IsSelfDualC L'' LZ)
    (hLS : IsSelfDualC S LS) {x : Pl D} {α : (AE D)ˣ}
    (hα : ∀ (S : HSp D) (L : Lat S) y, y ∈ latA S L (· = x) ↔ ((α⁻¹ : (AE D)ˣ) : AE D) • y ∈ latV S L (· = x))
    (hμ : ∀ a ∈ idAt D (· = x), a • ratV ζ₀ ∈ latV L'' LZ (· = x) ↔ a ∈ intAt D (· = x))
    (hk : ∀ w ∈ latO S L'' (LS : Set _) (LZ : Set _) (· = x), kap τ S w ∈ latO L S (LL : Set _) (LS : Set _) (· = x))
    {a : AE D} (ha : a • ratV ζ ∈ latV L LL (· = x)) {s₀ s : Fin S.rank → AE D} (hs₀ : s₀ ∈ latV S LS (· = x))
    (hs : s ∈ latV S LS (· = x)) :
    cA D α * (-incA D D.host.xi0⁻¹ * (α⁻¹ : (AE D)ˣ)) * incA D (star lam) * incA D (star ζ ⬝ᵥ L.gram *ᵥ ζ) * a *
      hermAt S s₀ s ∈ intAt D (· = x) := by
  have hsd := LocSD.isSDAt_latV D S LS x hLS
  obtain ⟨w, hw0, hw⟩ : ∃ w : Matrix (Fin L''.rank) (Fin S.rank) (AE D), MxAt (· = x) w ∧
      ∀ y, w *ᵥ y = ((α : AE D) * hermAt S y s₀) • ratV ζ₀ := by
    refine ⟨vecMulVec ((α : AE D) • ratV ζ₀) ((fun i => cA D (s₀ i)) ᵥ* gA S), fun i j => ?_, fun y => ?_⟩
    · rw [vecMulVec_apply]
      refine Ideal.mul_mem_left _ _ ?_
      simp only [vecMul, dotProduct]
      exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_right _ _ (id_conj (hsd.1 _ hs₀ l))
    · rw [herm_eq, dotProduct_mulVec]
      generalize (fun i => cA D (s₀ i)) ᵥ* gA S = t
      funext i
      simp only [mulVec, dotProduct, vecMulVec_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, Finset.sum_mul]
      exact Finset.sum_congr rfl fun j _ => by ring
  have hwO : (show WO S L'' from w) ∈ latO S L'' (LS : Set _) (LZ : Set _) (· = x) := by
    rw [LatMem.mem_latO_iff D S L'' LS LZ hLS hLZ]
    refine ⟨hw0, fun y hy => ?_⟩
    have hy' := (hsd.2.2 y (hsd.1 y hy)).1 hy _ hs₀
    change w *ᵥ y ∈ _
    rw [hα, hw, smul_smul, Units.inv_mul_cancel_left]
    exact (hμ _ hy'.1).2 hy'
  have h1 := ((LatMem.mem_latO_iff D L S LL LS hLL hLS _ _).1 (hk _ hwO)).2 _ ha
  rw [hα] at h1
  have h2 := (hsd.2.2 _ (hsd.1 _ h1)).1 h1 s hs
  have e1 := herm_smul S ((α⁻¹ : (AE D)ˣ) : AE D) 1 ((show Matrix (Fin S.rank) (Fin L.rank) (AE D) from kap τ S w) *ᵥ
    a • ratV ζ) s
  rw [one_smul] at e1
  rw [e1, herm_kap] at h2
  change _ * (_ * hermAt L _ (_ *ᵥ (w *ᵥ s))) ∈ _ at h2
  rw [hw, mulVec_smul, rat_mulVec, hτ, ratV_smul, smul_smul, herm_smul, herm_rat] at h2
  convert h2 using 1
  simp only [RingHom.map_mul, RingHom.map_neg, RingHom.map_one, herm_conj, FrameLat.cA_incA lam]
  ring

theorem top_norm {lam t t₀ : D.host.E} (hlam : lam ≠ 0) (hn : lam * star lam * t = -(D.host.xi0 * star D.host.xi0) * t₀)
    (α : (AE D)ˣ) {m : (AE D)ˣ} (hm' : α * (xiU D * cU α)⁻¹ * inU lam hlam = m) :
    cA D (m : AE D) = cA D α * (-incA D D.host.xi0⁻¹ * (α⁻¹ : (AE D)ˣ)) * incA D (star lam) ∧
      (m : AE D) * cA D m * incA D t = -incA D t₀ := by
  have hn' := congrArg (incA D) hn
  simp only [RingHom.map_mul, RingHom.map_neg, GlobalTheory.DualPairCheck.star_purely_imaginary_eq_neg] at hn'
  have f2 : (m : AE D) = α * (incA D D.host.xi0⁻¹ * cA D (α⁻¹ : (AE D)ˣ)) * incA D lam := by
    rw [← hm', mul_inv]
    simp only [Units.val_mul, inU_val, cU_inv, xiU, inU_inv]
  have f3 : cA D (m : AE D) = cA D α * (-incA D D.host.xi0⁻¹ * (α⁻¹ : (AE D)ˣ)) * incA D (star lam) := by
    rw [f2]
    simp only [RingHom.map_mul, cA_cA, cA_xi_inv, FrameLat.cA_incA lam]
  have g1 := α.mul_inv
  have g2 : cA D (α : AE D) * cA D ((α⁻¹ : (AE D)ˣ) : AE D) = 1 := (cU α).mul_inv
  have g3 : incA D D.host.xi0 * incA D D.host.xi0⁻¹ = 1 := (xiU D).mul_inv
  refine ⟨f3, ?_⟩
  rw [f3, f2]
  linear_combination (-(α * (α⁻¹ : (AE D)ˣ) * cA D α * cA D (α⁻¹ : (AE D)ˣ) * incA D D.host.xi0⁻¹ * incA D D.host.xi0⁻¹)) * hn' +
    (-incA D t₀ * cA D α * cA D (α⁻¹ : (AE D)ˣ) * incA D D.host.xi0 * incA D D.host.xi0 * incA D D.host.xi0⁻¹ *
      incA D D.host.xi0⁻¹) * g1 +
    (-incA D t₀ * incA D D.host.xi0 * incA D D.host.xi0 * incA D D.host.xi0⁻¹ * incA D D.host.xi0⁻¹) * g2 +
    (-incA D t₀ * (incA D D.host.xi0 * incA D D.host.xi0⁻¹ + 1)) * g3

theorem top_line {L L'' S : HSp D} (hS : 0 < S.rank) (τ : Matrix (Fin L.rank) (Fin L''.rank) D.host.E) {ζ : Fin L.rank → D.host.E}
    {ζ₀ : Fin L''.rank → D.host.E} (hζ : IsLineVec L ζ) (hζ₀ : IsLineVec L'' ζ₀) {lam : D.host.E} (hlam : lam ≠ 0)
    (hn : lam * star lam * (star ζ ⬝ᵥ L.gram *ᵥ ζ) = -(D.host.xi0 * star D.host.xi0) * (star ζ₀ ⬝ᵥ L''.gram *ᵥ ζ₀))
    (hτ : τ *ᵥ ζ₀ = lam • ζ) {LL : Lat L} {LZ : Lat L''} {LS : Lat S} (hLL : IsSelfDualC L LL) (hLZ : IsSelfDualC L'' LZ)
    (hLS : IsSelfDualC S LS) {x : Pl D} {α : (AE D)ˣ}
    (hα : ∀ (S : HSp D) (L : Lat S) y, y ∈ latA S L (· = x) ↔ ((α⁻¹ : (AE D)ˣ) : AE D) • y ∈ latV S L (· = x))
    (hμ : ∀ a ∈ idAt D (· = x), a • ratV ζ₀ ∈ latV L'' LZ (· = x) ↔ a ∈ intAt D (· = x))
    (hk : ∀ w ∈ latO S L'' (LS : Set _) (LZ : Set _) (· = x), kap τ S w ∈ latO L S (LL : Set _) (LS : Set _) (· = x)) :
    ∀ a ∈ idAt D (· = x), a • ratV ζ ∈ latV L LL (· = x) ↔
      (((α * (xiU D * cU α)⁻¹ * inU lam hlam)⁻¹ : (AE D)ˣ) : AE D) * a ∈ intAt D (· = x) := by
  obtain ⟨e, he0, hg⟩ := line_gen hζ hLL.1 x
  have hne := line_norm (μ := inU e he0) hζ hLL hg
  have hn0 := (line_norm (μ := 1) hζ₀ hLZ (x := x) fun a ha => by rw [inv_one, Units.val_one, one_mul]; exact hμ a ha).neg
  rw [Units.val_one, RingHom.map_one, one_mul, one_mul] at hn0
  have hsd := LocSD.isSDAt_latV D S LS x hLS
  have hi := idem_mem_intAt (D := D) (· = x)
  generalize hm' : α * (xiU D * cU α)⁻¹ * inU lam hlam = m
  obtain ⟨f3, hmn⟩ := top_norm hlam hn α hm'
  have f1 := m.mul_inv
  have g4 : cA D (m : AE D) * cA D ((m⁻¹ : (AE D)ˣ) : AE D) = 1 := (cU m).mul_inv
  have g5 : incA D e * incA D e⁻¹ = 1 := (inU e he0).mul_inv
  rw [← hmn] at hn0
  rw [inU_val] at hne
  have hU : IsU x (incA D e * (m⁻¹ : (AE D)ˣ)) := by
    refine isU_of_norm (int_of_smul hS hLS fun s₀ hs₀ => ?_) fun a ha => ?_
    · refine (hsd.2.2 ((incA D e * (m⁻¹ : (AE D)ˣ)) • s₀) fun i => Ideal.mul_mem_left _ _ (hsd.1 _ hs₀ i)).2 fun s hs => ?_
      have h2 := kap_test τ hτ hLL hLZ hLS hα hμ hk
        ((hg _ (Ideal.mul_mem_left _ (incA D e) hi.1)).2 (by rwa [← mul_assoc, mul_comm _ (incA D e), g5, one_mul])) hs₀ hs
      have e2 := herm_smul S (incA D e * (m⁻¹ : (AE D)ˣ)) 1 s₀ s
      rw [one_smul, RingHom.map_one, mul_one] at e2
      have hid := LocSD.hermAt_mem_idAt (hsd.1 _ hs₀) s
      rw [e2, hn0 _ (Ideal.mul_mem_left _ _ hid)]
      rw [← f3] at h2
      have e3 := (mem_idAt_iff _ _).1 hid
      convert h2 using 1
      generalize incA D (star ζ ⬝ᵥ L.gram *ᵥ ζ) = t
      linear_combination (cA D m * t * incA D e * hermAt S s₀ s) * f1 - (cA D m * t * incA D e) * e3
    · rw [hne a ha, hn0 ((incA D e * (m⁻¹ : (AE D)ˣ) * cA D (incA D e * (m⁻¹ : (AE D)ˣ))) * a) (Ideal.mul_mem_left _ _ ha),
        RingHom.map_mul (cA D)]
      refine iff_of_eq (congrArg (· ∈ _) ?_)
      generalize incA D (star ζ ⬝ᵥ L.gram *ᵥ ζ) = t
      linear_combination (-incA D e * cA D (incA D e) * t * a * (cA D m * cA D (m⁻¹ : (AE D)ˣ))) * f1 -
        (incA D e * cA D (incA D e) * t * a) * g4
  intro a ha
  rw [hg a ha, hU _ (Ideal.mul_mem_left _ _ ha)]
  refine iff_of_eq (congrArg (· ∈ _) ?_)
  linear_combination (((m⁻¹ : (AE D)ˣ) : AE D) * a) * g5

variable {c : Comm D} {v : VCom c} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {ι : Type} {o : TDat c k ι}

theorem step_down {x : Pl D} (hg : GoodAt v o x) {α m : (AE D)ˣ}
    (hα : ∀ (S : HSp D) (L : Lat S) y, y ∈ latA S L (· = x) ↔ ((α⁻¹ : (AE D)ˣ) : AE D) • y ∈ latV S L (· = x))
    (j σ : ℕ) (h : j + 2 * (σ + 1) + 2 = D.R.m)
    (hz : ∀ a ∈ idAt D (· = x), a • ratV (vecB (c.bes (j + 1 + 1) σ (idx_step h)).o (c.bes (j + 1 + 1) σ (idx_step h)).ζ) ∈
      latV _ (o.M (j + 1 + 1) σ (idx_step h)) (· = x) ↔ ((m⁻¹ : (AE D)ˣ) : AE D) * a ∈ intAt D (· = x)) :
    (∀ a ∈ idAt D (· = x), a • ratV (vecB (c.bes j (σ + 1) h).o (c.bes j (σ + 1) h).ζ) ∈
      latV _ (o.M j (σ + 1) h) (· = x) ↔ (((α * (xiU D * cU α)⁻¹ * m)⁻¹ : (AE D)ˣ) : AE D) * a ∈ intAt D (· = x)) ∧
    ∀ a ∈ idAt D (· = x), colMul (c.bes j (σ + 1) h).d.jX (Fin.last σ) a ∈ latV _ (v.N j) (· = x) ↔
      (((α * α * m)⁻¹ : (AE D)ˣ) : AE D) * a ∈ intAt D (· = x) := by
  have bf := hg.bf j (σ + 1) h
  have fb := hg.fb j σ h
  have hJ : ∀ a ∈ idAt D (· = x), colMul (c.jac j (σ + 1) h).d.jX (Fin.last σ) a ∈ latV _ (v.N (j + 1)) (· = x) ↔
      (((α * m)⁻¹ : (AE D)ˣ) : AE D) * a ∈ intAt D (· = x) := fun a ha => by
    refine (fb.cols (Fin.last σ) a ha).trans ?_
    have hmono := fb.monoW
    revert hz hmono
    change ∀ (hz : ∀ a ∈ idAt D (· = x), a • ratV (vecB (c.bes (j + 1 + 1) σ (idx_step h)).o (c.bes (j + 1 + 1) σ (idx_step h)).ζ) ∈
      latV _ (o.M (j + 1 + 1) σ (idx_step h)) (· = x) ↔ _), MonoAt (c.bes (j + 1 + 1) σ (idx_step h)).d _ _ x →
      (colMul (xLast (c.bes (j + 1 + 1) σ (idx_step h)).d
        (vecB (c.bes (j + 1 + 1) σ (idx_step h)).o (c.bes (j + 1 + 1) σ (idx_step h)).ζ)) _ _ ∈ _ ↔ _)
    generalize vecB (c.bes (j + 1 + 1) σ (idx_step h)).o (c.bes (j + 1 + 1) σ (idx_step h)).ζ = z
    generalize (c.bes (j + 1 + 1) σ (idx_step h)).d = d'
    intro hz hmono
    have e : ∀ t : AE D, colMul (xLast d' z) (Fin.last σ) t = d'.j0 *ᵥ (t • ratV z) := fun t => by
      funext k
      simp only [colMul, xLast, Matrix.of_apply, Fin.snoc_last, mulVec_smul, Pi.smul_apply, smul_eq_mul]
    have e0 : ∀ (M : Mx D (c.V (j + 1 + 1)).rank σ) i, colMul M i 0 = 0 := fun M i => funext fun k => zero_mul _
    rw [hα, smul_colMul, e, hmono, mulVec_mulVec, mulVec_mulVec, mulVec_mulVec, d'.pX_j0, d'.pY_j0, d'.p0_j0, zero_mulVec,
      one_mulVec, hz _ (Ideal.mul_mem_left _ _ ha), mul_inv, Units.val_mul, mul_assoc, mul_left_comm]
    simp only [Pi.zero_apply, e0, zero_mem, implies_true, true_and]
  refine ⟨fun a ha => ?_, fun a ha => ?_⟩
  · have hY := dual_line _ bf.sdW bf.monoW (Fin.last σ) hJ
    have h1 := last_iff (c.jac j (σ + 1) h).d (vecB (c.bes j (σ + 1) h).o (c.bes j (σ + 1) h).ζ) bf.sdV₀ bf.sdW
      (m := α * (xiU D * cU α)⁻¹ * m) (Fin.last σ) rfl
      (by rw [← mul_assoc, mul_comm α (xiU D * cU α)⁻¹, mul_inv_cancel_left]) (hα _ _) hY _
      (Ideal.mul_mem_left _ (((α * (xiU D * cU α)⁻¹ * m)⁻¹ : (AE D)ˣ) : AE D) ha)
    rw [Units.mul_inv_cancel_left] at h1
    exact h1.symm.trans (bf.last (Nat.succ_pos σ) _ (Ideal.mul_mem_left _ _ ha))
  · refine (bf.cols (Fin.last σ) a ha).trans ?_
    rw [hα, smul_colMul]
    refine (hJ _ (Ideal.mul_mem_left _ _ ha)).trans ?_
    rw [← mul_assoc, ← Units.val_mul, ← mul_inv, mul_comm (α * m), mul_assoc]

theorem last_ideal (hc : c.Is) (sh : ShapeOff v o) (hp : GlobalTheory.MiTop.TopPrim v o) (hr : ∀ j, j < D.R.m → 0 < (c.X (j + 1)).rank)
    {lam : D.host.E} (hlam : lam ≠ 0) (hτ : ∀ j hj, v.τ j hj *ᵥ o.ζ₀ = lam • (c.bes j 0 hj).ζ) {x : Pl D} (hx : x ∉ v.tP)
    {α : (AE D)ˣ}
    (hα : ∀ (S : HSp D) (L : Lat S) y, y ∈ latA S L (· = x) ↔ ((α⁻¹ : (AE D)ˣ) : AE D) • y ∈ latV S L (· = x))
    (j ρ : ℕ) (h : j + 2 * ρ + 2 = D.R.m) (r : Fin ρ) (hρ : r.1 + 1 = ρ) :
    ∀ a ∈ idAt D (· = x), colMul (c.bes j ρ h).d.jX r a ∈ latV _ (v.N j) (· = x) ↔
      (((α * α * ((α * (xiU D * cU α)⁻¹) ^ ρ * inU lam hlam))⁻¹ : (AE D)ˣ) : AE D) * a ∈ intAt D (· = x) := by
  have key : ∀ σ j (h : j + 2 * σ + 2 = D.R.m), ∀ a ∈ idAt D (· = x), a • ratV (vecB (c.bes j σ h).o (c.bes j σ h).ζ) ∈
      latV _ (o.M j σ h) (· = x) ↔
        ((((α * (xiU D * cU α)⁻¹) ^ (σ + 1) * inU lam hlam)⁻¹ : (AE D)ˣ) : AE D) * a ∈ intAt D (· = x) := by
    intro σ
    induction σ with
    | zero =>
      intro j h a ha
      obtain ⟨LL, LZ, h1, h2, h3, h4, h5⟩ := (sh.split x hx).top j h
      have hn : lam * star lam * (star (c.bes j 0 h).ζ ⬝ᵥ (c.bes j 0 h).L.gram *ᵥ (c.bes j 0 h).ζ) =
          -(D.host.xi0 * star D.host.xi0) * (star o.ζ₀ ⬝ᵥ c.Lz.gram *ᵥ o.ζ₀) := by
        have := congrArg (fun M => star o.ζ₀ ⬝ᵥ M *ᵥ o.ζ₀) (sh.pre.tau j h)
        rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, ← star_mulVec, hτ, smul_mulVec, dotProduct_smul, smul_eq_mul,
          mulVec_smul, star_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul] at this
        rw [← this, mul_assoc]
      rw [← orth_line _ h3, zero_add, pow_one]
      exact top_line (hr j (by omega)) (v.τ j h) (c.bes j 0 h).line sh.pre.line hlam hn (hτ j h) h1 h2
        (hc.x (j + 1) (by omega)).sd hα (fun a ha => hp.line h hx h4 ha) h5 a ha
    | succ σ ih =>
      intro j h a ha
      rw [pow_succ', mul_assoc]
      exact (step_down (sh.good x) hα j σ h (ih _ _)).1 a ha
  obtain _ | σ := ρ
  · exact r.elim0
  · obtain rfl : r = Fin.last σ := Fin.ext (by simpa using hρ)
    exact (step_down (sh.good x) hα j σ h (key _ _ _)).2

theorem prim_down {ψ : AddChar (AF D.host.F) ℂ} {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) {L : Lat S} {x : Pl D}
    (hp : PrimAt ψ d L x) {cc b : (AE D)ˣ}
    (hψ : ∀ s ∈ idAt D (· = x), (∀ o ∈ intAt D (· = x), psiE ψ (s * o) = 1) ↔
      ((cc⁻¹ : (AE D)ˣ) : AE D) * s ∈ intAt D (· = x)) (i j : Fin ρ) (hij : j.1 = i.1 + 1)
    (hL : ∀ a ∈ idAt D (· = x), colMul d.jX j a ∈ latV S L (· = x) ↔ ((b⁻¹ : (AE D)ˣ) : AE D) * a ∈ intAt D (· = x)) :
    ∀ a ∈ idAt D (· = x), colMul d.jX i a ∈ latV S L (· = x) ↔
      (((cc * b)⁻¹ : (AE D)ˣ) : AE D) * a ∈ intAt D (· = x) := fun a ha => by
  have he := idem_mem_intAt (D := D) (· = x)
  have hs : ((b⁻¹ : (AE D)ˣ) : AE D) * a ∈ idAt D (· = x) := Ideal.mul_mem_left _ _ ha
  rw [mul_inv, Units.val_mul, mul_assoc, ← hψ _ hs, ← hp i j hij _ hs]
  constructor
  · intro H t ht
    have := smul_latV x ((hL t (colMul_id d j (latV_idAt ht))).1 ht) H
    rw [smul_colMul] at this
    convert this using 2
    ring
  · intro H
    have := H _ ((hL _ (Ideal.mul_mem_left _ (b : AE D) he.1)).2 (by rwa [Units.inv_mul_cancel_left]))
    convert this using 2
    linear_combination (-a * idem D (· = x)) * b.inv_mul - (mem_idAt_iff _ a).1 ha

theorem all_ideal (hc : c.Is) (sh : ShapeOff v o) (hp : GlobalTheory.MiTop.TopPrim v o) (hr : ∀ j, j < D.R.m → 0 < (c.X (j + 1)).rank)
    {lam : D.host.E} (hlam : lam ≠ 0) (hτ : ∀ j hj, v.τ j hj *ᵥ o.ζ₀ = lam • (c.bes j 0 hj).ζ) {x : Pl D} (hx : x ∉ v.tP)
    {α cc : (AE D)ˣ}
    (hα : ∀ (S : HSp D) (L : Lat S) y, y ∈ latA S L (· = x) ↔ ((α⁻¹ : (AE D)ˣ) : AE D) • y ∈ latV S L (· = x))
    (hψ : ∀ s ∈ idAt D (· = x), (∀ o ∈ intAt D (· = x), psiE c.ψ (s * o) = 1) ↔
      ((cc⁻¹ : (AE D)ˣ) : AE D) * s ∈ intAt D (· = x))
    (j ρ : ℕ) (h : j + 2 * ρ + 2 = D.R.m) (n : ℕ) : ∀ r : Fin ρ, r.1 + n + 1 = ρ →
    ∀ a ∈ idAt D (· = x), colMul (c.bes j ρ h).d.jX r a ∈ latV _ (v.N j) (· = x) ↔
      (((cc ^ n * (α * α * ((α * (xiU D * cU α)⁻¹) ^ ρ * inU lam hlam)))⁻¹ : (AE D)ˣ) : AE D) * a ∈ intAt D (· = x) := by
  induction n with
  | zero =>
    intro r hρ
    rw [pow_zero, one_mul]
    exact last_ideal hc sh hp hr hlam hτ hx hα j ρ h r hρ
  | succ n ih =>
    intro r hρ
    rw [pow_succ', mul_assoc cc]
    exact prim_down _ ((sh.good x).bf j ρ h).prim hψ r ⟨r.1 + 1, by omega⟩ rfl (ih _ (by simp only; omega))

end GlobalTheory.LineIdeal

end
