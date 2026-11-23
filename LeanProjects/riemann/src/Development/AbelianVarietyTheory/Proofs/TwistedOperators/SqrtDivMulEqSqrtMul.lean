import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RealPoints
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentMulAddOneSubInverse
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TameAtOfUnrAt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilLatticeVacuumStabilizerSplittingCharacters
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSelfDualCoordLatticeOfSelfDualFrame
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsUnramifiedEtaTildeOfOddExponentSum
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DetTwoDiagBlocksProperties
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinPartMulIncAMem
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ModulusUnramifiedCharDetHeckeDoubleCosetSplit
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InvolutionSphericalHeckeAnti
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLocalHomLatticeOfKeepsCompletedLattices

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links
  Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj IsDedekindDomain NumberField Matrix
open Formalism.L2.NTheta (IsIdemAt IsHeckeElt)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.HeckeVacuum

open GlobalTheory.AdelicLatMove GlobalTheory.LocalLatStab

variable {D : D7} {S T : HSp D}

def IsHalfReps (Λ : AddSubgroup (WO S T)) (b : AE D) (a : GA D T) (Δ : Finset (WO S T)) : Prop :=
  (∀ x ∈ Δ, actO S T 1 a⁻¹ x ∈ Λ ∧ IsHalf b x) ∧ ∀ w, actO S T 1 a⁻¹ w ∈ Λ → ∃! x, x ∈ Δ ∧ w - x ∈ Λ

theorem card_reps {G : Type} [AddCommGroup G] (A B : AddSubgroup G) {R : Finset G} (h1 : ∀ u ∈ R, u ∈ B)
    (h2 : ∀ w ∈ B, ∃! v, v ∈ R ∧ w - v ∈ A) : R.card = A.relIndex B := by
  have key : ∀ u w : B, (QuotientAddGroup.mk u : B ⧸ A.addSubgroupOf B) = QuotientAddGroup.mk w ↔ (w : G) - u ∈ A :=
    fun u w => by
      rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf, AddSubgroup.coe_add, AddSubgroup.coe_neg, neg_add_eq_sub]
  rw [← Nat.card_eq_finsetCard]
  refine Nat.card_congr (Equiv.ofBijective
    (fun u : R => (QuotientAddGroup.mk ⟨u, h1 u u.2⟩ : B ⧸ A.addSubgroupOf B)) ⟨fun u v h => ?_, fun q => ?_⟩)
  · exact Subtype.ext ((h2 v (h1 v v.2)).unique ⟨u.2, (key _ _).1 h⟩ ⟨v.2, by rw [sub_self]; exact zero_mem _⟩)
  · obtain ⟨w, rfl⟩ := QuotientAddGroup.mk_surjective q
    obtain ⟨v, ⟨hv, h⟩, -⟩ := h2 w w.2
    exact ⟨⟨v, hv⟩, (key _ _).2 h⟩

theorem smul_rankOne (b : AE D) (a : D.host.E) (s : Fin S.rank → Formalism.IndefR.Datum.EAf D) (α : Af D.host.F)
    (y : Fin T.rank → Af D.host.F ⊗[D.host.F] D.host.E) :
    b • rankOne S T a s (swpVec D _ α y) = rankOne S T a s (swpVec D _ α (finPart D b • y)) := by
  ext i j
  simp only [rankOne, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
  rw [← finEmb_mul]
  congr 1
  have : swpVec D _ α (finPart D b • y) i = toEAf D b * swpVec D _ α y i := by
    change _ * swp D (finPart D b * y i) = swp D (finPart D b) * (_ * swp D (y i))
    rw [map_mul, mul_left_comm]
  rw [this]
  ring

theorem smul_actO_mem (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (b : AE D) (h : GA D T)
    (hh : ∀ y ∈ latHat D.host.F D.host.E LT,
      finPart D b • finMat D.sp.cm.sig T.gram h *ᵥ y ∈ latHat D.host.F D.host.E LT)
    (u : WO S T) (hu : u ∈ latO S T LS LT fun _ => True) : b • actO S T 1 h u ∈ latO S T LS LT fun _ => True := by
  induction hu using AddSubgroup.closure_induction with
  | mem u hu =>
    obtain ⟨α, hα, hP, a, ha, s, hs, t, ht, rfl⟩ := hu
    have h1 : (1 : Af D.host.F) ∈ intAf D.host.F := (one_mem _ : (1 : Af D.host.F) ∈ Formalism.UG.intAd D.host.F)
    have e := rankOne_pure S T a s t (1 * 1) (α * 1)
    rw [← swpVec_pure, ← swpVec_pure, mul_one, mul_one, mul_one] at e
    rw [← e, actO_rankOne, mulVec_swpVec T, mt_one, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mulVec,
      smul_rankOne]
    exact rankOne_mem S T LS LT _ a ha α hα hP _ (AddSubgroup.subset_closure ⟨1, h1, s, hs, rfl⟩) _
      (hh _ (AddSubgroup.subset_closure ⟨1, h1, t, ht, rfl⟩))
  | zero => simp only [actO, Matrix.mul_zero, Matrix.zero_mul, smul_zero]; exact zero_mem _
  | add y z _ _ hy hz => simp only [actO, Matrix.mul_add, Matrix.add_mul, smul_add] at hy hz ⊢; exact add_mem hy hz
  | neg y _ hy => simp only [actO, Matrix.mul_neg, Matrix.neg_mul, smul_neg] at hy ⊢; exact neg_mem hy

theorem act_mul (h h' : GA D T) (u : WO S T) : actO S T 1 (h * h') u = actO S T 1 h (actO S T 1 h' u) := by
  rw [← GlobalTheory.SplitLinear.actO_mul, one_mul]

theorem act_one (u : WO S T) : actO S T 1 1 u = u := by
  simp only [actO, inv_one, mt_one, Matrix.mul_one, Matrix.one_mul]

theorem act_sub (h : GA D T) (u u' : WO S T) : actO S T 1 h (u - u') = actO S T 1 h u - actO S T 1 h u' :=
  map_sub (GlobalTheory.SplitHecke.actAdd S T 1 h) u u'

theorem act_smul (h : GA D T) (b : AE D) (u : WO S T) : actO S T 1 h (b • u) = b • actO S T 1 h u := by
  unfold actO
  rw [Matrix.mul_smul, Matrix.smul_mul]

section Elt

variable {LS : Set (Fin S.rank → D.host.E)} {e : AE D} {ϖ : D.host.E} {k : ℕ} {α : GA D T}

theorem inv_act_mem (he : IsSplitIdem D e) (hα : IsHeckeElt T e ϖ k α) (w : WO S T)
    (hw : w ∈ latO S T LS (L0c D T) fun _ => True) (hh : IsHalf (cA D e) w) :
    actO S T 1 α⁻¹ w ∈ latO S T LS (L0c D T) fun _ => True := by
  have h := smul_actO_mem LS (L0c D T) (cA D e) α⁻¹ (GlobalTheory.SplitPlace.hecke_conj he.1 hα).2.2.1 w hw
  rwa [← act_smul, (GlobalTheory.SplitScalar.isHalf_iff _ _).1 hh] at h

theorem off_conj_mem (he : IsSplitIdem D e) (hα : IsHeckeElt T e ϖ k α) (w : WO S T)
    (hw : actO S T 1 α⁻¹ w ∈ latO S T LS (L0c D T) fun _ => True) :
    w - cA D e • w ∈ latO S T LS (L0c D T) fun _ => True := by
  have he' := GlobalTheory.SplitScalar.isSplitIdem_conj he
  obtain ⟨u, hu, rfl⟩ : ∃ u ∈ latO S T LS (L0c D T) fun _ => True, w = actO S T 1 α u :=
    ⟨_, hw, by rw [← act_mul, mul_inv_cancel, act_one]⟩
  have h1 := smul_actO_mem LS (L0c D T) e α hα.2.2.1 u hu
  have h2 := GlobalTheory.SplitScalar.off_smul_actO (GlobalTheory.SplitLinear.suppAt_one e S) hα.2.1 u
  have h3 : actO S T 1 α u - cA D e • actO S T 1 α u =
      (1 - (e + cA D e)) • actO S T 1 α u + e • actO S T 1 α u := by
    rw [← add_smul, show 1 - (e + cA D e) + e = 1 - cA D e by ring, sub_smul, one_smul]
  rw [h3, h2, sub_smul, add_smul, one_smul]
  exact add_mem (sub_mem hu (add_mem (GlobalTheory.SplitScalar.idem_smul_mem he.1 u hu)
    (GlobalTheory.SplitScalar.idem_smul_mem he'.1 u hu))) h1

end Elt

section Weil

variable {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
  {e : AE D} {P : Pl D.host.E} {ϖ : 𝓞 D.host.E} {k : ℕ} {α : GA D T}

theorem exists_halfReps (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT) (hL : (ΛT : Set _) = L0c D T)
    (he : IsSplitIdem D e) (hα : IsHeckeElt T e (ϖ : D.host.E) k α) :
    ∃ Δ, IsHalfReps (latO S T ΛS ΛT fun _ => True) (cA D e) α Δ := by
  have he' := GlobalTheory.SplitScalar.isSplitIdem_conj he
  have hle : ∀ w ∈ latO S T ΛS ΛT (fun _ => True), IsHalf (cA D e) w →
      actO S T 1⁻¹ α⁻¹ w ∈ latO S T ΛS ΛT (fun _ => True) := by
    rw [hL, inv_one]; exact inv_act_mem he hα
  have hoff : ∀ w, actO S T 1 α⁻¹ w ∈ latO S T ΛS ΛT (fun _ => True) →
      w - cA D e • w ∈ latO S T ΛS ΛT (fun _ => True) := by
    rw [hL]; exact off_conj_mem he hα
  have hst := @GlobalTheory.SplitScalar.idem_smul_mem D S T (ΛS : Set _) (ΛT : Set _) _ he'.1
  haveI := GlobalTheory.SplitLinear.finite_enlarge hS.1 hT.1 he'.1 hle
  obtain ⟨R, -, r2, r3⟩ := GlobalTheory.SplitLinear.exists_reps
    ((latO S T ΛS ΛT fun _ => True) ⊓ GlobalTheory.PlaceModel.half S T (cA D e))
    ((latO S T ΛS ΛT fun _ => True).comap (GlobalTheory.SplitHecke.actAdd S T 1⁻¹ α⁻¹) ⊓ GlobalTheory.PlaceModel.half S T (cA D e))
  rw [inv_one] at r2 r3
  generalize latO S T ΛS ΛT (fun _ => True) = Λ at *
  have hR : ∀ u ∈ R, actO S T 1 α⁻¹ u ∈ Λ ∧ IsHalf (cA D e) u := fun u hu =>
    ⟨(r2 u hu).1, (GlobalTheory.PlaceModel.isHalf_iff S T).2 (r2 u hu).2⟩
  refine ⟨R, hR, fun w hw => ?_⟩
  have hh := GlobalTheory.SplitLinear.isHalf_smul' he'.1 w
  refine (existsUnique_congr fun v => and_congr_right fun hv => ⟨fun h => ?_, fun h => ?_⟩).1
    (r3 (cA D e • w) ⟨?_, (GlobalTheory.PlaceModel.isHalf_iff S T).1 hh⟩)
  · have := add_mem (hoff w hw) h.1
    rwa [sub_add_sub_cancel] at this
  · have := sub_mem h (hoff w hw)
    rw [sub_sub_sub_cancel_left] at this
    exact ⟨this, (GlobalTheory.PlaceModel.isHalf_iff S T).1 (GlobalTheory.SplitScalar.isHalf_sub hh (hR v hv).2)⟩
  · change actO S T 1 α⁻¹ (cA D e • w) ∈ Λ
    rw [act_smul]
    exact hst _ hw

theorem card_parity_sign_length_of_eq {N q k n : ℕ} (hq : 0 < q) (h : (Real.sqrt (N : ℝ))⁻¹ = ((q : ℝ) ^ k) ^ (-(n : ℝ) / 2)) :
    N = q ^ (k * n) := by
  have h0 : (0 : ℝ) < (q : ℝ) ^ k := by positivity
  have h1 : (N : ℝ)⁻¹ = (((q : ℝ) ^ k) ^ n)⁻¹ := by
    rw [← Real.sq_sqrt (Nat.cast_nonneg N), ← inv_pow, h, ← Real.rpow_natCast, ← Real.rpow_mul h0.le,
      ← Real.rpow_natCast _ n, ← Real.rpow_neg h0.le]
    congr 1
    push_cast
    ring
  rw [_root_.inv_inj, ← pow_mul] at h1
  exact_mod_cast h1

theorem card_halfReps (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT) (hL : (ΛT : Set _) = L0c D T)
    (hP : IsIdemAt e P) (hϖ : ϖ ∈ P.asIdeal) (hϖ2 : ϖ ∉ P.asIdeal ^ 2) (hα : IsHeckeElt T e (ϖ : D.host.E) k α)
    {Δ : Finset (WO S T)} (hΔ : IsHalfReps (latO S T ΛS ΛT fun _ => True) (cA D e) α Δ) :
    Δ.card = Ideal.absNorm P.asIdeal ^ (k * S.rank) := by
  have he := hP.1
  have he' := GlobalTheory.SplitScalar.isSplitIdem_conj he
  have hle : ∀ w ∈ latO S T ΛS ΛT (fun _ => True), IsHalf (cA D e) w →
      actO S T 1⁻¹ α⁻¹ w ∈ latO S T ΛS ΛT (fun _ => True) := by
    rw [hL, inv_one]; exact inv_act_mem he hα
  have h1 := GlobalTheory.SplitLinear.sqrt_index hS.1 hT.1 he' (GlobalTheory.VecInv.isDetAt_detAt _ he'.1 S 1)
    (GlobalTheory.VecInv.isDetAt_detAt _ he'.1 T α) hle
  rw [inv_one, ← card_reps ((latO S T ΛS ΛT fun _ => True) ⊓ GlobalTheory.PlaceModel.half S T (cA D e))
    ((latO S T ΛS ΛT fun _ => True).comap (GlobalTheory.SplitHecke.actAdd S T 1 α⁻¹) ⊓ GlobalTheory.PlaceModel.half S T (cA D e))
    (R := Δ) (fun u hu => ⟨(hΔ.1 u hu).1, (GlobalTheory.PlaceModel.isHalf_iff S T).1 (hΔ.1 u hu).2⟩)
    fun w hw => (existsUnique_congr fun v => and_congr_right fun hv => ⟨fun h => ⟨h, (GlobalTheory.PlaceModel.half S T (cA D e)).sub_mem hw.2
      ((GlobalTheory.PlaceModel.isHalf_iff S T).1 (hΔ.1 v hv).2)⟩, fun h => h.1⟩).1 (hΔ.2 w hw.1)] at h1
  have hϖ0 : (ϖ : D.host.E) ≠ 0 := fun h => hϖ2 (by rw [show ϖ = 0 from RingOfIntegers.ext h]; exact zero_mem _)
  have hone : (1 : GA D T) ∈ Formalism.IndefR.Mult.locPart T (KsphC T ∅) e := by
    refine ⟨⟨one_mem _, fun y => ?_, by simp⟩, GlobalTheory.SplitLinear.suppAt_one e T⟩
    have h3 : finMat D.sp.cm.sig T.gram (1 : GA D T) = 1 := by
      change (mt T 1).map (finPart D) = 1
      rw [mt_one, Matrix.map_one _ (map_zero _) (map_one _)]
    rw [h3, Matrix.one_mulVec]
  have h2 := (GlobalTheory.SplitDetValue.det_modulus_chi D T P e hP ϖ hϖ hϖ2 (Formalism.L2.JoinChr.locU he.1 (Units.mk0 _ hϖ0))
    (by rw [Formalism.L2.JoinChr.locU_val, Formalism.L2.JoinChr.locE, Units.val_mk0]; ring) k α hα 1
    hone 1 hone
    (GlobalTheory.VecInv.detAt e he.1 T α) (by rw [one_mul, mul_one]; exact GlobalTheory.VecInv.isDetAt_detAt _ he.1 T α)).1
  rw [map_one, GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.modFac,
    GlobalTheory.SplitLinear.absFin_of_mul_conj (GlobalTheory.SplitLinear.det_conj he'.1 (GlobalTheory.VecInv.isDetAt_detAt _ he.1 T α)), h2,
    inv_inv, show GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absFin D 1 = 1 by simp [GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absFin, GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absV],
    Real.one_rpow, one_mul] at h1
  exact card_parity_sign_length_of_eq (Nat.pos_of_ne_zero fun h => P.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)) h1

variable {ψ : AddChar (AF D.host.F) ℂ} {χS χT : (AE D)ˣ →* Circle}
  {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} {f : WO S T → ℂ}

theorem om_elt (hW : IsWeilDatumO ψ S T χS χT om) (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT)
    (hL : (ΛT : Set _) = L0c D T) (he : IsSplitIdem D e) (hα : IsHeckeElt T e (ϖ : D.host.E) k α)
    (hf : IsThetaFunO ψ S T f) (hv : IsLatVac (heisO ψ S T) (latO S T ΛS ΛT fun _ => True) f)
    {Δ : Finset (WO S T)} (hΔ : IsHalfReps (latO S T ΛS ΛT fun _ => True) (cA D e) α Δ) :
    om (1, α) f = ((χS (GlobalTheory.VecInv.detAt e he.1 T α) : ℂ) * ((Real.sqrt (Δ.card : ℝ) : ℝ) : ℂ)⁻¹) •
      ∑ u ∈ Δ, heisO ψ S T u f := by
  have he' := GlobalTheory.SplitScalar.isSplitIdem_conj he
  have hle : ∀ w ∈ latO S T ΛS ΛT (fun _ => True), IsHalf (cA D e) w →
      actO S T 1⁻¹ α⁻¹ w ∈ latO S T ΛS ΛT (fun _ => True) := by
    rw [hL, inv_one]; exact inv_act_mem he hα
  rw [GlobalTheory.SplitLinear.om_eq_sum_lattice hW hS hT he' hf
    (fun u hu hh => hh.elim (hv.2 _ he' u hu) (hv.2 _ (GlobalTheory.SplitScalar.isSplitIdem_conj he') u hu))
    (GlobalTheory.SplitLinear.suppAt_one _ S) (GlobalTheory.SplitPlace.suppAt_conj hα.2.1) (GlobalTheory.VecInv.isDetAt_detAt _ he'.1 S 1)
    (GlobalTheory.VecInv.isDetAt_detAt _ he'.1 T α) (R := Δ) (by rw [inv_one]; exact hΔ.1)
    (by rw [inv_one]; exact fun w hw _ => hΔ.2 w hw) hle, splitFacO, map_one, map_one, inv_one, one_mul,
    GlobalTheory.SplitDetCharacter.char_eq_of_mul_conj hW.resS _ _
      (GlobalTheory.SplitLinear.det_conj he'.1 (GlobalTheory.VecInv.isDetAt_detAt _ he.1 T α))]

end Weil

section Move

variable {Λ : AddSubgroup (WO S T)} {b : AE D} {α k₁ k₂ : GA D T} {Δ : Finset (WO S T)}

theorem act_inj (h : GA D T) : Function.Injective (actO S T 1 h) :=
  Function.LeftInverse.injective (g := actO S T 1 h⁻¹) fun u => by rw [← act_mul, inv_mul_cancel, act_one]

open Classical in

theorem IsHalfReps.move (h₁ : ∀ u, u ∈ Λ ↔ actO S T 1 k₁ u ∈ Λ) (h₂ : ∀ u, u ∈ Λ ↔ actO S T 1 k₂ u ∈ Λ)
    (h : IsHalfReps Λ b α Δ) : IsHalfReps Λ b (k₁ * α * k₂) (Δ.image (actO S T 1 k₁)) := by
  have key : ∀ u, actO S T 1 (k₁ * α * k₂)⁻¹ (actO S T 1 k₁ u) ∈ Λ ↔ actO S T 1 α⁻¹ u ∈ Λ := fun u => by
    rw [h₂, ← act_mul, ← act_mul, show k₂ * (k₁ * α * k₂)⁻¹ * k₁ = α⁻¹ by group]
  refine ⟨fun x hx => ?_, fun w hw => ?_⟩
  · obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 hx
    exact ⟨(key u).2 (h.1 u hu).1, GlobalTheory.SplitHecke.isHalf_actO _ _ (h.1 u hu).2⟩
  · obtain ⟨w, rfl⟩ : ∃ w', actO S T 1 k₁ w' = w := ⟨actO S T 1 k₁⁻¹ w, by rw [← act_mul, mul_inv_cancel, act_one]⟩
    obtain ⟨x, ⟨hx, hx'⟩, hu⟩ := h.2 w ((key w).1 hw)
    refine ⟨_, ⟨Finset.mem_image_of_mem _ hx, by rwa [← act_sub, ← h₁]⟩, ?_⟩
    rintro _ ⟨hy, hy'⟩
    obtain ⟨y, hy₀, rfl⟩ := Finset.mem_image.1 hy
    rw [← act_sub, ← h₁] at hy'
    rw [hu y ⟨hy₀, hy'⟩]

theorem keeps_inv {k : GA D T} (h : ∀ u, u ∈ Λ ↔ actO S T 1 k u ∈ Λ) (u : WO S T) : u ∈ Λ ↔ actO S T 1 k⁻¹ u ∈ Λ := by
  rw [h (actO S T 1 k⁻¹ u), ← act_mul, mul_inv_cancel, act_one]

end Move

theorem om_coset {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
    {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} {e : AE D} {P : Pl D.host.E} {ϖ : 𝓞 D.host.E} {k : ℕ}
    {α k₁ k₂ : GA D T} {ψ : AddChar (AF D.host.F) ℂ} {χS χT : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} {f : WO S T → ℂ}
    (hW : IsWeilDatumO ψ S T χS χT om) (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT) (hL : (ΛT : Set _) = L0c D T)
    (hP : IsIdemAt e P) (hϖ : ϖ ∈ P.asIdeal) (hϖ2 : ϖ ∉ P.asIdeal ^ 2) (hα : IsHeckeElt T e (ϖ : D.host.E) k α)
    (hf : IsThetaFunO ψ S T f) (hv : IsLatVac (heisO ψ S T) (latO S T ΛS ΛT fun _ => True) f)
    (h₁ : ∀ u, u ∈ (latO S T ΛS ΛT fun _ => True) ↔ actO S T 1 k₁ u ∈ latO S T ΛS ΛT fun _ => True)
    (h₂ : ∀ u, u ∈ (latO S T ΛS ΛT fun _ => True) ↔ actO S T 1 k₂ u ∈ latO S T ΛS ΛT fun _ => True)
    (f₁ : om (1, k₁) f = f) (f₂ : om (1, k₂) f = f) :
    (∃ Δ, IsHalfReps (latO S T ΛS ΛT fun _ => True) (cA D e) (k₁ * α * k₂) Δ) ∧
      ∀ Δ, IsHalfReps (latO S T ΛS ΛT fun _ => True) (cA D e) (k₁ * α * k₂) Δ →
        Δ.card = Ideal.absNorm P.asIdeal ^ (k * S.rank) ∧
          om (1, k₁ * α * k₂) f = ((χS (GlobalTheory.VecInv.detAt e hP.1.1 T α) : ℂ) * ((Real.sqrt (Δ.card : ℝ) : ℝ) : ℂ)⁻¹) •
            ∑ u ∈ Δ, heisO ψ S T u f := by
  classical
  refine ⟨(exists_halfReps hS hT hL hP.1 hα).elim fun Δ h => ⟨_, h.move h₁ h₂⟩, fun Δ hΔ => ?_⟩
  have h := hΔ.move (keeps_inv h₁) (keeps_inv h₂)
  rw [show k₁⁻¹ * (k₁ * α * k₂) * k₂⁻¹ = α by group] at h
  have hc := Finset.card_image_of_injective Δ (act_inj (S := S) k₁⁻¹)
  refine ⟨by rw [← hc]; convert card_halfReps hS hT hL hP hϖ hϖ2 hα h, ?_⟩
  have h3 := om_elt hW hS hT hL hP.1 hα hf hv h
  rw [Finset.card_image_of_injective Δ (act_inj k₁⁻¹), Finset.sum_image fun _ _ _ _ h => act_inj k₁⁻¹ h] at h3
  rw [show ((1 : GA D S), k₁ * α * k₂) = (1, k₁) * (1, α) * (1, k₂) by simp, map_mul, map_mul, Module.End.mul_apply,
    Module.End.mul_apply, f₂, h3, map_smul, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [hW.om_heis _ _ _ _ hf, f₁, ← act_mul, mul_inv_cancel, act_one]

section Level

open GlobalTheory.VecInv

variable {T0 : Type} {L : LevCh D T0} {μ0 : T0}

theorem twist_places_base (hL : L.Is μ0) : L.Q μ0 = ∅ :=
  Finset.eq_empty_of_forall_notMem fun PP h =>
    (hL.Q_ram μ0 PP).2 (Or.inl h) (by rw [hL.xi_base]; exact fun _ _ => rfl)

variable (hL : L.Is μ0) (i : Fin D.R.m) {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D}
  {sS : D.what₂.Tau → Matrix (Fin (Vc D i).rank) (Fin (Vc D i).rank) ℂ}
  {sT : D.what₂.Tau → Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ} {f₀ f : WO (Vc D i) (Wc D i) → ℂ}
  {om : GA D (Vc D i) × GA D (Wc D i) →* Module.End ℂ (WO (Vc D i) (Wc D i) → ℂ)}
  (hv : IsThPVecOf ψ θ (Vc D i) (Wc D i) sS sT (L.ΛV i) (L.ΛW i) (L.βV i) (L.βW i) L.Pg (L.Q μ0) (L.xiR μ0) f₀ f)

include hL hv

theorem level_fixes_vacuum
    (hW : IsWeilDatumO ψ (Vc D i) (Wc D i) (L.mu μ0 ((i : ℕ) + 1)) (L.mu μ0 ((i : ℕ) + 1) * L.eta⁻¹) om)
    {κ : GA D (Wc D i)} (hκ : κ ∈ levG (Wc D i) (L.βW i) (L.datWp i L.triv)) : om (1, κ) f₀ = f₀ := by
  have rV : (Vc D i).rank = D.R.r + D.R.t := D.sp.V_rank _ (Nat.le_add_left _ _) i.2
  have rW : (Wc D i).rank = D.R.r := D.sp.W_rank _ (Nat.le_add_left _ _) i.2
  have hη : GlobalTheory.WeilParts.IsEtaTilde D L.eta :=
    GlobalTheory.EtaTildeOddParity.isEtaTilde_of_odd D _ _ hL.eta L.C.isEta _ _ _ hW.resS hW.resT (by
      rw [rV, rW]
      obtain ⟨c, hc⟩ := D.R.t_odd
      exact ⟨D.R.r + c, by omega⟩)
  obtain ⟨hvac, e, he, -⟩ := hv
  have hee := GlobalTheory.PlaceVec.idemSum_mul_self he
  have hP := fun PP => @Finset.mem_union _ (Classical.decEq _) L.Pg (L.Q μ0) PP
  obtain ⟨u1, u2⟩ := unrOff_mu hL μ0 i hP (by convert he)
  have sW : finE (Wc D i) κ ∈ St (L.βW i) := parLev_St hκ.2.1
  have h0 := GlobalTheory.VecInv.Vac.stab_vacuum D ψ _ _ _ _ _ _ om hW
    (GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hL.βV i))
    (GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hL.βW i)) ⟨_, hη⟩ _ _ (hL.βV i).choose_spec.1
    (hL.βW i).choose_spec.1 _ e hee he u1 (u1.mul u2.inv) 1 κ (Stab.one _ _) ⟨hκ.1, sW⟩ f₀ hvac.2.theta hvac.2.lat
  obtain ⟨aW, haW, hrW⟩ := exists_det_int sW
  obtain ⟨mW, -⟩ := mu_val hL μ0 i hP (by convert he) (detAt e hee _ κ) _ aW _ (isDetAt_detAt e hee _ κ) haW
    fun PP _ => hrW PP
  have hr : rTup (L.βW i) (L.datWp i L.triv) (finE (Wc D i) κ) = 1 := Subgroup.mem_bot.1 hκ.2.2
  rw [h0, splitFacO, map_one, map_one, inv_one, one_mul, mW, twist_places_base hL, Finset.prod_empty, mul_one,
    Finset.prod_eq_one, Units.val_one, one_smul]
  intro PP h
  have h1 : upperLeftBlock (r_le_rank_Wc i) (redFn (L.βW i) PP (finE (Wc D i) κ)) = 1 := congrFun hr ⟨PP, h⟩
  rw [← (GlobalTheory.VecInv.TwoBlockDet.det_blocks _ _ _ 0 (r_le_rank_Wc i) _).2.2 rW, h1, map_one, map_one, inv_one]

theorem mu_detAt {P : Pl D.host.E} (hoff : Bridge.SplitOff P (L.Pg : Set (Pl D.host.E))) {V : HSp D} {k : ℕ} {α : GA D V}
    (hα : IsHeckeAt V P k α) {e : AE D} (hP : IsIdemAt e P) :
    ((L.mu μ0 ((i : ℕ) + 1) (detAt e hP.1.1 V α) : Circle) : ℂ) = (((L.C.mu0 i).val P : ℂˣ) : ℂ) ^ k := by
  obtain ⟨-, e₀, he, -⟩ := hv
  rw [twist_places_base hL, @Finset.union_empty _ (_)] at he
  have hz : IsDetAt (GlobalTheory.ExportSeries.idemAt P) V α (detAt e hP.1.1 V α) := by
    rw [GlobalTheory.ExportSeries.idemAt_eq hP]; exact isDetAt_detAt _ _ _ _
  have u1 : GlobalTheory.ExportSeries.UnramOutside (L.mu0 ((i : ℕ) + 1)) L.Pg := by
    unfold GlobalTheory.ExportSeries.UnramOutside
    rw [GlobalTheory.ExportSeries.idem_eq he]
    exact GlobalTheory.T.heckeChar_trivial_on_idempotentIntegralUnits D _ _ _ e₀ (hL.mu0 i) he (GlobalTheory.T.levelCharacters_ramification_levelPlaces D T0 L μ0 hL μ0 i).2.2.2
  have u2 : GlobalTheory.ExportSeries.UnramOutside (L.xi μ0) L.Pg := by
    unfold GlobalTheory.ExportSeries.UnramOutside
    rw [GlobalTheory.ExportSeries.idem_eq he]
    exact GlobalTheory.T.heckeChar_trivial_on_idempotentIntegralUnits D _ _ _ e₀ (hL.xi μ0) he fun _ _ _ => by rw [hL.xi_base]; exact fun _ _ => rfl
  have e0 : ((L.mu μ0 ((i : ℕ) + 1) (detAt e hP.1.1 V α) : Circle) : ℂ) =
      (L.mu0 ((i : ℕ) + 1) (detAt e hP.1.1 V α) : Circle) * (L.xi μ0 (detAt e hP.1.1 V α) : Circle) := rfl
  rw [e0, GlobalTheory.HeckeDetChar.chi_detAt (hL.mu0 i) u1 ⟨e₀, he⟩ hoff hα hz,
    GlobalTheory.HeckeDetChar.chi_detAt (hL.xi μ0) u2 ⟨e₀, he⟩ hoff hα hz, hL.xi_base,
    show Formalism.L2.Host.HChar.val (1 : Formalism.L2.Host.HChar D.host.E) P = 1 from rfl, Units.val_one, one_pow, mul_one]

end Level

theorem sqrt_div_mul_eq_sqrt_mul (q k : ℕ) {n : ℕ} (hn : Even n) :
    ((Real.sqrt ((q ^ (k * n) : ℕ) : ℝ) : ℝ) : ℂ)⁻¹ = (q : ℂ)⁻¹ ^ (k * n / 2) := by
  obtain ⟨a, rfl⟩ := hn
  rw [show k * (a + a) / 2 = k * a by rw [mul_add, ← two_mul, Nat.mul_div_cancel_left _ two_pos], mul_add, pow_add,
    Nat.cast_mul, Real.sqrt_mul_self (Nat.cast_nonneg _), inv_pow]
  push_cast
  rfl

theorem omega_vacuum_hecke : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type)
    (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F),
    R.toLevCh.Is A.μ0 → R.IsFam → R.IsThP → ∀ (i : Fin D.R.m) (P : Formalism.L2.DIV.Pl D.host.E) (p k : ℕ)
      (α : GA D (Wc D i)) (Rc : Finset (GA D (Wc D i))), GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.IsUnitaryHeckeOperatorSplitPrimeData T R i P p k α Rc →
    ∀ a ∈ Rc, (Vc D i).rank = D.R.nV ∧ ∃ e : AE D, IsIdemAt e P ∧
      (∃ Δ, IsHalfReps (latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) fun _ => True) (cA D e) a Δ) ∧
      ∀ Δ, IsHalfReps (latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) fun _ => True) (cA D e) a Δ →
        (∀ x ∈ Δ, x.map (infPart D) = 0) ∧ Δ.card = Ideal.absNorm P.asIdeal ^ (k * D.R.nV) ∧
        R.ωP i A.μ0 (1, a) (R.vacP i) =
          (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.muAt T R i P ^ k * ((Ideal.absNorm P.asIdeal : ℕ) : ℂ)⁻¹ ^ (k * D.R.nV / 2)) •
            ∑ x ∈ Δ, heisO R.ψ (Vc D i) (Wc D i) x (R.vacP i) := by
  intro D G _ _ Pl0 T0 A T _ R hL hF hT i P p k α Rc hs a ha
  obtain ⟨hoff, -, -, -, -, hα, hdc⟩ := hs
  obtain ⟨k₁, k₂, rfl⟩ := hdc.1 a ha
  have rV : (Vc D i).rank = D.R.nV := D.sp.V_rank _ (Nat.le_add_left _ _) i.2
  have hev : Even D.R.nV := by
    obtain ⟨a, ha⟩ := D.R.k_even
    obtain ⟨b, hb⟩ := D.R.m_even
    obtain ⟨c, hc⟩ := D.R.t_odd
    have := D.R.two_le_m
    exact ⟨a + b + c, by unfold Ranks.nV Ranks.r; omega⟩
  have hW := hT.ωP i A.μ0
  have hv := hT.vP i A.μ0
  have hoff' : Bridge.SplitOff P (R.Pg : Set (Pl D.host.E)) :=
    ⟨hoff.1, fun h => hoff.2.1 (hF.Sb h), fun Q hQ => hoff.2.2 Q (hF.Sb hQ)⟩
  have hmu := fun e (hP : IsIdemAt e P) => mu_detAt hL i hv hoff' hα hP
  obtain ⟨e, ϖ, hP, hϖ, hϖ2, hα⟩ := hα
  have hlat : (R.ΛW i : Set (Fin (Wc D i).rank → D.host.E)) = L0c D (Wc D i) := by
    obtain ⟨c, -, -, -, h1, h2⟩ := hL.βW i
    simp only [one_pow, Nat.cast_one, one_smul] at h1 h2
    exact Set.ext fun x => ⟨h2 x, h1 x⟩
  have keep := fun κ : levG (Wc D i) (R.βW i) (R.datWp i R.triv) =>
    GlobalTheory.VecInv.mem_latO_iff (g := 1) (h := κ) (hL.βV i).choose_spec.1 (hL.βW i).choose_spec.1
      (by rw [map_one]; exact one_mem _) (parLev_St κ.2.2.1)
  obtain ⟨r1, r2⟩ := om_coset hW (GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hL.βV i))
    (GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hL.βW i)) hlat hP hϖ hϖ2 hα hv.1.2.theta hv.1.2.lat
    (keep k₁) (keep k₂) (level_fixes_vacuum hL i hv hW k₁.2) (level_fixes_vacuum hL i hv hW k₂.2)
  refine ⟨rV, e, hP, r1, fun Δ hΔ => ?_⟩
  obtain ⟨c1, c2⟩ := r2 Δ hΔ
  have c3 : Δ.card = Ideal.absNorm P.asIdeal ^ (k * D.R.nV) := by rw [c1, rV]
  refine ⟨fun x hx => GlobalTheory.SplitScalar.half_fin (GlobalTheory.SplitScalar.isSplitIdem_conj hP.1) (hΔ.1 x hx).2, c3, ?_⟩
  rw [c2, c3, sqrt_div_mul_eq_sqrt_mul _ _ hev]
  exact congrArg (fun z : ℂ => (z * _) • _) (hmu e hP)

end GlobalTheory.HeckeVacuum

end
