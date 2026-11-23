import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OneSubIdemQMulSelf
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousIdempotentCutIsClosedScaledKernelStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryIdempotentCutMemFourierJacobiBesselGroupStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCompactOpenLatticeStabilizerAtPlacesStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InLatticeStabilizerAtPlacesIffPlaceSetProdStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinPl.SetCut

section Alg

variable {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n]

theorem mul_eq_add_sub_one (c : R) (a b : Matrix n n R) (ha : c • (a - 1) = a - 1) (hb : c • (b - 1) = 0) :
    a * b = a + b - 1 ∧ b * a = a + b - 1 := by
  have h1 : (a - 1) * (b - 1) = 0 := by rw [← ha, Matrix.smul_mul, ← Matrix.mul_smul, hb, Matrix.mul_zero]
  have h2 : (b - 1) * (a - 1) = 0 := by rw [← ha, Matrix.mul_smul, ← Matrix.smul_mul, hb, Matrix.zero_mul]
  have e1 : a * b = (a - 1) * (b - 1) + (a + b - 1) := by noncomm_ring
  have e2 : b * a = (b - 1) * (a - 1) + (a + b - 1) := by noncomm_ring
  exact ⟨by rw [e1, h1, zero_add], by rw [e2, h2, zero_add]⟩

theorem cut_sub_one (c : R) (g : Matrix n n R) : c • g + (1 - c) • (1 : Matrix n n R) - 1 = c • (g - 1) := by
  rw [smul_sub, sub_smul, one_smul]; abel

theorem cut_left (c : R) (a b : Matrix n n R) (ha : c • (a - 1) = a - 1) (hb : c • (b - 1) = 0) :
    c • (a * b) + (1 - c) • (1 : Matrix n n R) = a := by
  rw [← sub_left_inj (a := 1), cut_sub_one, (mul_eq_add_sub_one c a b ha hb).1,
    show a + b - 1 - 1 = (a - 1) + (b - 1) by abel, smul_add, ha, hb, add_zero]

theorem cut_right (c : R) (a b : Matrix n n R) (ha : c • (a - 1) = a - 1) (hb : c • (b - 1) = 0) :
    (1 - c) • (a * b) + (1 - (1 - c)) • (1 : Matrix n n R) = b := by
  rw [← sub_left_inj (a := 1), cut_sub_one, (mul_eq_add_sub_one c a b ha hb).1,
    show a + b - 1 - 1 = (a - 1) + (b - 1) by abel, sub_smul, one_smul, smul_add, ha, hb]
  abel

theorem cut_mul_cut (c : R) (hc : c * c = c) (g : Matrix n n R) :
    (c • g + (1 - c) • (1 : Matrix n n R)) * ((1 - c) • g + (1 - (1 - c)) • (1 : Matrix n n R)) = g := by
  have h0 : c * (1 - c) = 0 := by rw [mul_sub, mul_one, hc, sub_self]
  rw [(mul_eq_add_sub_one c _ _ (by rw [cut_sub_one, smul_smul, hc]) (by rw [cut_sub_one, smul_smul, h0, zero_smul])).1,
    sub_sub_cancel, sub_smul, sub_smul, one_smul, one_smul]
  abel

end Alg

variable {D : D7}

theorem mem_idOff_iff (P : Pl D → Prop) (a : AE D) : a ∈ idOff D P ↔ ∀ w, P w → GlobalTheory.FinPl.compAt D w a = 0 := by
  simp only [idOff, Submodule.mem_iInf, RingHom.mem_ker, Subtype.forall]

theorem mem_GfC_iff_entries (V : HSp D) (g : GA D V) :
    g ∈ GfC V ↔ ∀ i j, infPart D ((Formalism.L2.Theta.mt V g - 1) i j) = 0 := by
  rw [GlobalTheory.UnitaryIdemCut.mem_GfC_iff, Units.ext_iff]
  change (Formalism.L2.Theta.mt V g).map (infPart D) = 1 ↔ _
  rw [← Matrix.ext_iff]
  refine forall_congr' fun i => forall_congr' fun j => ?_
  rw [Matrix.sub_apply, RingHom.map_sub, sub_eq_zero, Matrix.map_apply]
  by_cases hij : i = j
  · subst hij
    rw [Matrix.one_apply_eq, Matrix.one_apply_eq, RingHom.map_one]
  · rw [Matrix.one_apply_ne hij, Matrix.one_apply_ne hij, RingHom.map_zero]

theorem mem_grpAt_iff_parts (V : HSp D) (P : Pl D → Prop) (g : GA D V) :
    g ∈ grpAt V P ↔ ∀ i j, infPart D ((Formalism.L2.Theta.mt V g - 1) i j) = 0 ∧
      ∀ w, ¬ P w → GlobalTheory.FinPl.compAt D w ((Formalism.L2.Theta.mt V g - 1) i j) = 0 := by
  rw [grpAt, mem_congGrp_iff]
  exact forall_congr' fun i => forall_congr' fun j => mem_supportedOnPlacesIdeal_iff_components_zero_elsewhere D P _

theorem mem_grpOff_iff_parts (V : HSp D) (P : Pl D → Prop) (g : GA D V) :
    g ∈ grpOff V P ↔ ∀ i j w, P w → GlobalTheory.FinPl.compAt D w ((Formalism.L2.Theta.mt V g - 1) i j) = 0 := by
  rw [grpOff, mem_congGrp_iff]
  exact forall_congr' fun i => forall_congr' fun j => mem_idOff_iff P _

theorem grpAt_le_GfC (V : HSp D) (P : Pl D → Prop) : grpAt V P ≤ GfC V := fun g hg =>
  (mem_GfC_iff_entries V g).2 fun i j => ((mem_grpAt_iff_parts V P g).1 hg i j).1

theorem grpAt_le_grpOff (V : HSp D) (P P' : Pl D → Prop) (h : ∀ p, P p → ¬ P' p) : grpAt V P ≤ grpOff V P' := fun g hg =>
  (mem_grpOff_iff_parts V P' g).2 fun i j w hw => ((mem_grpAt_iff_parts V P g).1 hg i j).2 w fun h' => h w h' hw

theorem GfC_inf_grpOff (V : HSp D) (P : Pl D → Prop) : GfC V ⊓ grpOff V P = grpAt V fun p => ¬ P p := by
  ext g
  rw [Subgroup.mem_inf, mem_GfC_iff_entries, mem_grpOff_iff_parts, mem_grpAt_iff_parts]
  exact ⟨fun h i j => ⟨h.1 i j, fun w hw => h.2 i j w (not_not.1 hw)⟩,
    fun h => ⟨fun i j => (h i j).1, fun i j w hw => (h i j).2 w (not_not.2 hw)⟩⟩

abbrev eQ (D : D7) (Q : Finset (Pl D)) : AE D := algebraMap (AF D.host.F) (AE D) (idemQ D Q)

theorem eQ_mul_self (Q : Finset (Pl D)) : eQ D Q * eQ D Q = eQ D Q := by
  rw [← RingHom.map_mul, idemQ_mul_self]

theorem algebraMap_one_sub (c : AF D.host.F) :
    algebraMap (AF D.host.F) (AE D) (1 - c) = 1 - algebraMap (AF D.host.F) (AE D) c := by
  rw [RingHom.map_sub, RingHom.map_one]

theorem smul_of_mem_Q (V : HSp D) (Q : Finset (Pl D)) {a : GA D V} (ha : a ∈ grpAt V (· ∈ Q)) :
    eQ D Q • (Formalism.L2.Theta.mt V a - 1) = Formalism.L2.Theta.mt V a - 1 := by
  rw [grpAt, mem_congGrp_iff] at ha
  exact Matrix.ext fun i j => (mem_idAt_Q_iff Q _).1 (ha i j)

open Classical in
theorem smul_of_mem_Qc (V : HSp D) (Q : Finset (Pl D)) {b : GA D V} (hb : b ∈ grpAt V (· ∉ Q)) :
    eQ D Q • (Formalism.L2.Theta.mt V b - 1) = 0 := by
  rw [mem_grpAt_iff_parts] at hb
  exact Matrix.ext fun i j => (mem_idOff_iff_mul (· ∈ Q) _ (parts_idemQ Q).1 (parts_idemQ Q).2 _).1
    ((mem_idOff_iff _ _).2 fun w hw => (hb i j).2 w (not_not.2 hw))

theorem comm_Q (V : HSp D) (Q : Finset (Pl D)) {a b : GA D V} (ha : a ∈ grpAt V (· ∈ Q)) (hb : b ∈ grpAt V (· ∉ Q)) :
    a * b = b * a := by
  have h := mul_eq_add_sub_one _ _ _ (smul_of_mem_Q V Q ha) (smul_of_mem_Qc V Q hb)
  apply mt_injective V
  rw [mt_mul, mt_mul]
  exact h.1.trans h.2.symm

theorem cutG_left (V : HSp D) (Q : Finset (Pl D)) {a b : GA D V} (ha : a ∈ grpAt V (· ∈ Q)) (hb : b ∈ grpAt V (· ∉ Q)) :
    cutG V _ (idemQ_mul_self Q) (a * b) = a := by
  apply mt_injective V
  rw [mt_cutG, mt_mul]
  exact cut_left _ _ _ (smul_of_mem_Q V Q ha) (smul_of_mem_Qc V Q hb)

theorem cutG_right (V : HSp D) (Q : Finset (Pl D)) {a b : GA D V} (ha : a ∈ grpAt V (· ∈ Q)) (hb : b ∈ grpAt V (· ∉ Q)) :
    cutG V _ (one_sub_idemQ_mul_self Q) (a * b) = b := by
  apply mt_injective V
  rw [mt_cutG, mt_mul, algebraMap_one_sub]
  exact cut_right _ _ _ (smul_of_mem_Q V Q ha) (smul_of_mem_Qc V Q hb)

theorem cutG_mul_cutG (V : HSp D) (Q : Finset (Pl D)) (g : GA D V) :
    cutG V _ (idemQ_mul_self Q) g * cutG V _ (one_sub_idemQ_mul_self Q) g = g := by
  apply mt_injective V
  rw [mt_mul, mt_cutG, mt_cutG, algebraMap_one_sub]
  exact cut_mul_cut _ (eQ_mul_self Q) _

theorem cutG_mem_Q (V : HSp D) (Q : Finset (Pl D)) (g : GA D V) :
    cutG V _ (idemQ_mul_self Q) g ∈ grpAt V (· ∈ Q) := by
  rw [grpAt, mem_congGrp_iff]
  intro i j
  rw [mt_cutG, cut_sub_one, mem_idAt_Q_iff, Matrix.smul_apply, smul_eq_mul, ← mul_assoc]
  exact congrArg (· * _) (eQ_mul_self Q)

open Classical in
theorem cutG_mem_Qc (V : HSp D) (Q : Finset (Pl D)) {g : GA D V} (hg : g ∈ GfC V) :
    cutG V _ (one_sub_idemQ_mul_self Q) g ∈ grpAt V (· ∉ Q) := by
  rw [mem_grpAt_iff_parts]
  intro i j
  rw [mt_cutG, cut_sub_one, Matrix.smul_apply, smul_eq_mul, algebraMap_one_sub]
  refine ⟨?_, fun w hw => ?_⟩
  · rw [RingHom.map_mul, (mem_GfC_iff_entries V g).1 hg i j, mul_zero]
  · rw [RingHom.map_mul, RingHom.map_sub, RingHom.map_one, (parts_idemQ Q).2 w, if_pos (not_not.1 hw), sub_self, zero_mul]

theorem isClosed_of_idem (V : HSp D) (P : Pl D → Prop) (c : AF D.host.F)
    (hc : ∀ a, a ∈ idAt D P ↔ algebraMap (AF D.host.F) (AE D) c * a = a) : IsClosed (grpAt V P : Set (GA D V)) := by
  have h := (GlobalTheory.T.continuous_idempotentCut_and_isClosed_scaledKernel D V).2 (1 - c)
  convert h using 1
  ext g
  rw [SetLike.mem_coe, grpAt, mem_congGrp_iff, Set.mem_setOf_eq]
  refine forall_congr' fun i => forall_congr' fun j => ?_
  rw [hc, algebraMap_one_sub, sub_mul, one_mul, sub_eq_zero, eq_comm]

def splitHomeo (V : HSp D) (Q : Finset (Pl D)) : (grpAt V (· ∈ Q) × grpAt V (· ∉ Q)) ≃ₜ GfC V where
  toFun p := ⟨p.1.1 * p.2.1, mul_mem (grpAt_le_GfC V _ p.1.2) (grpAt_le_GfC V _ p.2.2)⟩
  invFun g := (⟨cutG V _ (idemQ_mul_self Q) g.1, cutG_mem_Q V Q g.1⟩,
    ⟨cutG V _ (one_sub_idemQ_mul_self Q) g.1, cutG_mem_Qc V Q g.2⟩)
  left_inv p := Prod.ext (Subtype.ext (cutG_left V Q p.1.2 p.2.2)) (Subtype.ext (cutG_right V Q p.1.2 p.2.2))
  right_inv g := Subtype.ext (cutG_mul_cutG V Q g.1)
  continuous_toFun := by
    haveI := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V.gram
    exact Continuous.subtype_mk
      ((continuous_subtype_val.comp continuous_fst).mul (continuous_subtype_val.comp continuous_snd)) _
  continuous_invFun :=
    (Continuous.subtype_mk (((GlobalTheory.T.continuous_idempotentCut_and_isClosed_scaledKernel D V).1 _ _).comp continuous_subtype_val) _).prodMk
      (Continuous.subtype_mk (((GlobalTheory.T.continuous_idempotentCut_and_isClosed_scaledKernel D V).1 _ _).comp continuous_subtype_val) _)

theorem grp_split : ∀ (D : D7) (V : HSp D) (Q : Finset (Pl D)), IsClosed (grpAt V (· ∈ Q) : Set (GA D V)) ∧ IsClosed (grpAt V (· ∉ Q) : Set (GA D V)) ∧ grpAt V (· ∈ Q) ≤ GfC V ∧ grpAt V (· ∉ Q) ≤ GfC V ∧ (∀ a ∈ grpAt V (· ∈ Q), ∀ b ∈ grpAt V (· ∉ Q), a * b = b * a) ∧ (∃ e : (grpAt V (· ∈ Q) × grpAt V (· ∉ Q)) ≃ₜ GfC V, ∀ p, (e p : GA D V) = p.1 * p.2) ∧ (∀ P P' : Pl D → Prop, (∀ p, P p → ¬ P' p) → grpAt V P ≤ grpOff V P') ∧ (∀ P : Pl D → Prop, GfC V ⊓ grpOff V P = grpAt V fun p => ¬ P p) ∧ (∀ (L : Lat V), IsSelfDualC V L → ∀ P : Pl D → Prop, (∃ K : Subgroup (GA D V), (∀ g, g ∈ K ↔ InK V L P g) ∧ IsCompact (K : Set (GA D V)) ∧ IsOpen ((K.subgroupOf (grpAt V P) : Subgroup _) : Set (grpAt V P))) ∧ ∀ κ, InK V L P κ ↔ ∃ a b, InK V L (fun p => P p ∧ p ∈ Q) a ∧ InK V L (fun p => P p ∧ p ∉ Q) b ∧ κ = a * b) ∧ ∀ (V₀ : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ), (∀ a ∈ grpAt V (· ∈ Q), ∀ b ∈ grpAt V (· ∉ Q), a * b ∈ jacGrp d → a ∈ jacGrp d ∧ b ∈ jacGrp d) ∧ ∀ (A L : HSp D) (o : OrthDec V₀ A L), ∀ a ∈ grpAt V (· ∈ Q), ∀ b ∈ grpAt V (· ∉ Q), a * b ∈ besGrp d o → a ∈ besGrp d o ∧ b ∈ besGrp d o := by
  intro D V Q
  refine ⟨isClosed_of_idem V _ _ (mem_idAt_Q_iff Q), isClosed_of_idem V _ _ (mem_idAt_Qc_iff Q), grpAt_le_GfC V _,
    grpAt_le_GfC V _, fun a ha b hb => comm_Q V Q ha hb, ⟨splitHomeo V Q, fun _ => rfl⟩, grpAt_le_grpOff V,
    GfC_inf_grpOff V, fun L hL P => ⟨GlobalTheory.T.exists_compactOpen_latticeStabilizerAtPlaces D V L hL P, GlobalTheory.T.inLatticeStabilizerAtPlaces_iff_placeSet_prod D V L P Q⟩, fun V₀ ρ d => ⟨?_, ?_⟩⟩
  · intro a ha b hb h
    exact ⟨cutG_left V Q ha hb ▸ (GlobalTheory.T.unitaryIdempotentCut_mem_fourierJacobi_besselGroup D V V₀ ρ d _ (idemQ_mul_self Q)).1 _ h,
      cutG_right V Q ha hb ▸ (GlobalTheory.T.unitaryIdempotentCut_mem_fourierJacobi_besselGroup D V V₀ ρ d _ (one_sub_idemQ_mul_self Q)).1 _ h⟩
  · intro A L o a ha b hb h
    exact ⟨cutG_left V Q ha hb ▸ (GlobalTheory.T.unitaryIdempotentCut_mem_fourierJacobi_besselGroup D V V₀ ρ d _ (idemQ_mul_self Q)).2 A L o _ h,
      cutG_right V Q ha hb ▸ (GlobalTheory.T.unitaryIdempotentCut_mem_fourierJacobi_besselGroup D V V₀ ρ d _ (one_sub_idemQ_mul_self Q)).2 A L o _ h⟩

end GlobalTheory.FinPl.SetCut

end
