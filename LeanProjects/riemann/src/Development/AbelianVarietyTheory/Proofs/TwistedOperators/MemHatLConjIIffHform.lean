import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RedMFrMapAdjZero
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CompletedTensorLatticeStrongApproxOpenCompact
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CompletedTensorLatticeLatticeVacuumTransport
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HformZeroRight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelCharacterEmbeddingCompat
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.TensorLatticeSelfDualSemicharacterIndex
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemLatOIffExistsActO
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LiftLevel

noncomputable section

namespace GlobalTheory.FrameIdeal

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def InId (I : Ideal (𝓞 E)) (x : E ⊗[F] Formalism.L2.Herm.Af F) : Prop :=
  ∃ s ∈ Formalism.L2.DIV.idS F I, (s : E ⊗[F] Formalism.L2.Herm.Af F) = x

theorem inId_zero (I : Ideal (𝓞 E)) : InId (F := F) I 0 := ⟨0, zero_mem _, rfl⟩

theorem inId_add {I : Ideal (𝓞 E)} {x y : E ⊗[F] Formalism.L2.Herm.Af F} (hx : InId I x) (hy : InId I y) :
    InId I (x + y) := by
  obtain ⟨s, hs, rfl⟩ := hx
  obtain ⟨t, ht, rfl⟩ := hy
  exact ⟨s + t, add_mem hs ht, rfl⟩

theorem inId_mul {I : Ideal (𝓞 E)} {t x : E ⊗[F] Formalism.L2.Herm.Af F} (ht : t ∈ Formalism.L2.Herm.intAf F E)
    (hx : InId I x) : InId I (t * x) := by
  obtain ⟨s, hs, rfl⟩ := hx
  exact ⟨⟨t, ht⟩ * s, Ideal.mul_mem_left _ _ hs, rfl⟩

theorem inId_sum {I : Ideal (𝓞 E)} {n : ℕ} (f : Fin n → E ⊗[F] Formalism.L2.Herm.Af F) (h : ∀ i, InId I (f i)) :
    InId I (∑ i, f i) := by
  classical
  induction (Finset.univ : Finset (Fin n)) using Finset.induction_on with
  | empty => simpa using inId_zero (F := F) I
  | insert a s ha ih => rw [Finset.sum_insert ha]; exact inId_add (h a) ih

theorem inId_int {I : Ideal (𝓞 E)} {x : E ⊗[F] Formalism.L2.Herm.Af F} (hx : InId I x) :
    x ∈ Formalism.L2.Herm.intAf F E := by
  obtain ⟨s, -, rfl⟩ := hx
  exact s.2

theorem mulVec_eq_sum {A : Type} [CommRing A] {n : ℕ} (B : Matrix (Fin n) (Fin n) A) (u : Fin n → A) :
    B *ᵥ u = ∑ i, u i • (B *ᵥ Pi.single i 1) := by
  funext c
  rw [Finset.sum_apply]
  simp only [Pi.smul_apply, Matrix.mulVec_single_one, smul_eq_mul, Matrix.transpose_apply]
  simp only [Matrix.mulVec, dotProduct]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem smul_mem_hatL_ideal {n : ℕ} (Λ : Submodule (𝓞 E) (Fin n → E)) {𝔪 : Ideal (𝓞 E)}
    {a : 𝓞 E} (ha : a ∈ 𝔪) {z : Fin n → E ⊗[F] Formalism.L2.Herm.Af F} (hz : z ∈ Formalism.L2.Herm.hatL (F := F) Λ) :
    Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) (algebraMap (𝓞 E) E a) • z ∈
      Formalism.L2.Herm.hatL (F := F) (𝔪 • Λ) := by
  unfold Formalism.L2.Herm.hatL Formalism.UG.latS at hz ⊢
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨l, hl, rfl⟩ := hx
    refine Submodule.subset_span ⟨a • l, Submodule.smul_mem_smul ha hl, ?_⟩
    funext i
    simp [Algebra.smul_def]
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ a hx

theorem idS_smul_mem_hatL {n : ℕ} (Λ : Submodule (𝓞 E) (Fin n → E)) {I : Ideal (𝓞 E)}
    {s : Formalism.L2.Herm.intAf F E} (hs : s ∈ Formalism.L2.DIV.idS F I) {z : Fin n → E ⊗[F] Formalism.L2.Herm.Af F}
    (hz : z ∈ Formalism.L2.Herm.hatL (F := F) Λ) :
    (s : E ⊗[F] Formalism.L2.Herm.Af F) • z ∈ Formalism.L2.Herm.hatL (F := F) (I • Λ) := by
  unfold Formalism.L2.DIV.idS Ideal.map at hs
  induction hs using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, ha, rfl⟩ := hx
    exact smul_mem_hatL_ideal Λ ha hz
  | zero => simp
  | add x y _ _ hx hy => rw [Subring.coe_add, add_smul]; exact Submodule.add_mem _ hx hy
  | smul t x _ hx =>
    rw [smul_eq_mul, Subring.coe_mul, mul_smul]
    exact Submodule.smul_mem _ t hx

theorem mem_hatL_smul_iff {n : ℕ} (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (Λ : Submodule (𝓞 E) (Fin n → E))
    (hfr : Formalism.L2.DIV.IsFrame β Λ) (I : Ideal (𝓞 E)) (v : Fin n → E ⊗[F] Formalism.L2.Herm.Af F) :
    v ∈ Formalism.L2.Herm.hatL (F := F) (I • Λ) ↔ ∀ i, InId I (((β⁻¹).1 *ᵥ v) i) := by
  constructor
  · intro hv
    unfold Formalism.L2.Herm.hatL Formalism.UG.latS at hv
    induction hv using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨x, hx, rfl⟩ := hw
      refine Submodule.smul_induction_on hx ?_ ?_
      · intro r hr l hl i
        have e : (fun i => Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) ((r • l) i)) =
            Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) (algebraMap (𝓞 E) E r) •
              (fun i => Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) (l i)) := by
          funext i
          simp [Algebra.smul_def]
        beta_reduce
        rw [e, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]
        have hl' := (hfr _).1 (Submodule.subset_span ⟨l, hl, rfl⟩) i
        exact ⟨Formalism.L2.DIV.oToS F E r * ⟨_, hl'⟩, Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hr), rfl⟩
      · intro x y hx hy i
        have e : (fun i => Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) ((x + y) i)) =
            (fun i => Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) (x i)) +
              (fun i => Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) (y i)) := by
          funext i
          simp
        beta_reduce at hx hy ⊢
        rw [e, Matrix.mulVec_add, Pi.add_apply]
        exact inId_add (hx i) (hy i)
    | zero => intro i; rw [Matrix.mulVec_zero]; exact inId_zero I
    | add x y _ _ hx hy => intro i; rw [Matrix.mulVec_add, Pi.add_apply]; exact inId_add (hx i) (hy i)
    | smul t x _ hx =>
      intro i
      rw [Subring.smul_def, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]
      exact inId_mul t.2 (hx i)
  · intro hu
    have e1 : v = β.1 *ᵥ ((β⁻¹).1 *ᵥ v) := by
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
    rw [e1, mulVec_eq_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    obtain ⟨s, hs, hsv⟩ := hu i
    rw [← hsv]
    refine idS_smul_mem_hatL Λ hs ((hfr _).2 fun k => ?_)
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec, Pi.single_apply]
    split_ifs
    · exact Subring.one_mem _
    · exact Subring.zero_mem _

end General

variable {D : D7}

theorem sigR_invol (x : Lev.EAf D) :
    Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F) (Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F) x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    simp only [Formalism.UG.sigR, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul,
      AlgHom.id_apply]
    congr 1
    exact star_star a
  | add x y hx hy => simp only [map_add, hx, hy]

def cO (D : D7) : 𝓞 D.host.E →+* 𝓞 D.host.E :=
  NumberField.RingOfIntegers.mapRingHom (D.sp.cm.sig : D.host.E →+* D.host.E)

theorem cO_coe (b : 𝓞 D.host.E) : ((cO D b : 𝓞 D.host.E) : D.host.E) = star (b : D.host.E) := rfl

def sO (D : D7) : Formalism.L2.Herm.intAf D.host.F D.host.E →+* Formalism.L2.Herm.intAf D.host.F D.host.E :=
  (Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F)).restrict _ _ (fun _ hs => GlobalTheory.LevSplit.sigR_int hs)

theorem sO_comp_oToS : (sO D).comp (Formalism.L2.DIV.oToS D.host.F D.host.E) = (Formalism.L2.DIV.oToS D.host.F D.host.E).comp (cO D) := by
  ext b
  exact GlobalTheory.GramFrame.sigR_inclE (D := D) (b : D.host.E)

theorem map_cO_le_conjI (J : Ideal (𝓞 D.host.E)) : J.map (cO D) ≤ conjI J := by
  rw [Ideal.map_le_iff_le_comap]
  intro b hb
  exact Ideal.subset_span ⟨b, hb, rfl⟩

theorem map_cO_conjI_le (J : Ideal (𝓞 D.host.E)) : (conjI J).map (cO D) ≤ J := by
  unfold conjI
  rw [Ideal.map_span, Ideal.span_le]
  rintro _ ⟨a, ⟨b, hb, hab⟩, rfl⟩
  have e : cO D a = b := by
    apply RingOfIntegers.ext
    rw [cO_coe, hab]
    exact star_star _
  rw [e]
  exact hb

theorem inId_sigR {I K : Ideal (𝓞 D.host.E)} (hIK : I.map (cO D) ≤ K) {x : Lev.EAf D} (hx : InId (F := D.host.F) I x) :
    InId (F := D.host.F) K (Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F) x) := by
  obtain ⟨s, hs, rfl⟩ := hx
  refine ⟨sO D s, ?_, ?_⟩
  · have h1 : sO D s ∈ (Formalism.L2.DIV.idS D.host.F I).map (sO D) := Ideal.mem_map_of_mem _ hs
    have h2 : (Formalism.L2.DIV.idS D.host.F I).map (sO D) ≤ Formalism.L2.DIV.idS D.host.F K := by
      unfold Formalism.L2.DIV.idS
      rw [Ideal.map_map, sO_comp_oToS, ← Ideal.map_map]
      exact Ideal.map_mono hIK
    exact h2 h1
  · first
      | exact RingHom.coe_restrict_apply _ _ _ _ s
      | exact congrArg Subtype.val (RingHom.restrict_apply _ _ s)
      | (unfold sO; rw [RingHom.restrict_apply])
      | (with_reducible_and_instances rfl)

end GlobalTheory.FrameIdeal

namespace GlobalTheory.FrameIdeal

variable {D : D7}

local notation "σA" => Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F)
local notation "ιA" => Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F)

def frameGram (T : HSp D) (β : GL (Fin T.rank) (Lev.EAf D)) : Matrix (Fin T.rank) (Fin T.rank) (Lev.EAf D) :=
  Formalism.UG.cT σA β.1 * T.gram.map ιA * β.1

theorem selfDual_pair {T : HSp D} {Λ : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} (hsd : IsSelfDualC T Λ) :
    ∀ x ∈ Λ, ∀ y ∈ Λ, Formalism.UG.hform (D.sp.cm.sig : D.host.E →+* D.host.E) T.gram x y ∈
      (algebraMap (𝓞 D.host.E) D.host.E).range := by
  intro x hx y hy
  obtain ⟨b, hb⟩ := (hsd.2 y).1 hy x hx
  exact ⟨b, hb⟩

theorem selfDual_dualL_le {T : HSp D} {Λ : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} (hsd : IsSelfDualC T Λ) :
    Formalism.L2.Forms.dualL (D.sp.cm.sig : D.host.E →+* D.host.E) T.gram Λ ≤ Λ := by
  unfold Formalism.L2.Forms.dualL
  rw [Submodule.span_le]
  intro y hy
  refine (hsd.2 y).2 fun x hx => ?_
  obtain ⟨b, hb⟩ := hy x hx
  exact ⟨b, hb⟩

theorem col_mem_hatL {n : ℕ} {β : GL (Fin n) (Lev.EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)}
    (hfr : Formalism.L2.DIV.IsFrame β Λ) (j : Fin n) : β.1 *ᵥ Pi.single j 1 ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ := by
  refine (hfr _).2 fun k => ?_
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec, Pi.single_apply]
  split_ifs
  · exact Subring.one_mem _
  · exact Subring.zero_mem _

theorem frameGram_int {T : HSp D} {Λ : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} (hsd : IsSelfDualC T Λ)
    {β : GL (Fin T.rank) (Lev.EAf D)} (hfr : Formalism.L2.DIV.IsFrame β Λ) (i j : Fin T.rank) :
    frameGram T β i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  unfold frameGram
  rw [GlobalTheory.GramFrame.gram_entry]
  exact GlobalTheory.GramFrame.pair_hatL T.gram Λ (selfDual_pair hsd) _ _ (col_mem_hatL hfr i) (col_mem_hatL hfr j)

theorem frameGram_det (T : HSp D) (β : GL (Fin T.rank) (Lev.EAf D)) : IsUnit (frameGram T β).det := by
  have hb : IsUnit β.1.det := (Matrix.isUnit_iff_isUnit_det _).1 β.isUnit
  unfold frameGram
  rw [Matrix.det_mul, Matrix.det_mul, Formalism.UG.cT, Matrix.det_transpose]
  refine IsUnit.mul (IsUnit.mul ?_ ?_) hb
  · have h3 := hb.map σA
    rw [RingHom.map_det] at h3
    exact h3
  · have h3 := (GlobalTheory.LatVac.gram_det_isUnit T).map ιA
    rw [RingHom.map_det] at h3
    exact h3

theorem frameGram_inv_int {T : HSp D} {Λ : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} (hsd : IsSelfDualC T Λ)
    {β : GL (Fin T.rank) (Lev.EAf D)} (hfr : Formalism.L2.DIV.IsFrame β Λ) (i j : Fin T.rank) :
    (frameGram T β)⁻¹ i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E :=
  GlobalTheory.GramFrame.inv_int D.sp.cm.sig (fun _ hs => GlobalTheory.LevSplit.sigR_int hs) T.gram (GlobalTheory.LatVac.gram_det_isUnit T)
    β Λ hsd.1 hfr (selfDual_dualL_le hsd) _ (Matrix.mul_nonsing_inv _ (frameGram_det T β)) i j

theorem hform_col (T : HSp D) (β : GL (Fin T.rank) (Lev.EAf D)) (v : Fin T.rank → Lev.EAf D) (j : Fin T.rank) :
    Formalism.UG.hform σA (T.gram.map ιA) v (fun c => β.1 c j) =
      Matrix.vecMul (fun a => σA (((β⁻¹).1 *ᵥ v) a)) (frameGram T β) j := by
  have e1 : v = β.1 *ᵥ ((β⁻¹).1 *ᵥ v) := by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
  conv_lhs => rw [e1]
  rw [GlobalTheory.DualCompletion.hform_mulVec_left]
  simp only [Matrix.vecMul, dotProduct, frameGram]
  rfl

theorem inId_vecMul {I : Ideal (𝓞 D.host.E)} {n : ℕ} {x : Fin n → Lev.EAf D} {M : Matrix (Fin n) (Fin n) (Lev.EAf D)}
    (hM : ∀ i j, M i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) (hx : ∀ i, InId (F := D.host.F) I (x i)) (j : Fin n) :
    InId (F := D.host.F) I (Matrix.vecMul x M j) := by
  simp only [Matrix.vecMul, dotProduct]
  refine inId_sum _ fun a => ?_
  rw [mul_comm]
  exact inId_mul (hM a j) (hx a)

theorem key_iff {T : HSp D} {Λ : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} (hsd : IsSelfDualC T Λ)
    {β : GL (Fin T.rank) (Lev.EAf D)} (hfr : Formalism.L2.DIV.IsFrame β Λ) (J : Ideal (𝓞 D.host.E))
    (v : Fin T.rank → Lev.EAf D) :
    (∀ i, InId (F := D.host.F) (conjI J) (((β⁻¹).1 *ᵥ v) i)) ↔
      ∀ j, InId (F := D.host.F) J (Formalism.UG.hform σA (T.gram.map ιA) v (fun c => β.1 c j)) := by
  simp only [hform_col]
  constructor
  · intro h j
    exact inId_vecMul (frameGram_int hsd hfr) (fun a => inId_sigR (map_cO_conjI_le J) (h a)) j
  · intro h a
    have e : (fun a => σA (((β⁻¹).1 *ᵥ v) a)) =
        Matrix.vecMul (Matrix.vecMul (fun a => σA (((β⁻¹).1 *ᵥ v) a)) (frameGram T β)) (frameGram T β)⁻¹ := by
      rw [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ (frameGram_det T β), Matrix.vecMul_one]
    have h2 : InId (F := D.host.F) J (σA (((β⁻¹).1 *ᵥ v) a)) := by
      rw [congrFun e a]
      exact inId_vecMul (frameGram_inv_int hsd hfr) h a
    have h3 := inId_sigR (map_cO_le_conjI J) h2
    rwa [sigR_invol] at h3

end GlobalTheory.FrameIdeal

theorem GlobalTheory.FrameIdeal.mem_hatL_conjI_iff_hform : ∀ (D : D7) (T : HSp D) (ΛT : Lt D.host.E T.rank), IsSelfDualC T ΛT → ∀ βT : GL (Fin T.rank) (Lev.EAf D), Formalism.L2.DIV.IsFrame βT ΛT → ∀ J : Ideal (𝓞 D.host.E), J ≠ ⊥ → ∀ v : Fin T.rank → Lev.EAf D, (v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (conjI J • ΛT) ↔ ∀ j : Fin T.rank, ∃ s ∈ Formalism.L2.DIV.idS D.host.F J, (s : Lev.EAf D) = Formalism.UG.hform (Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F)) (T.gram.map (Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F))) v (fun c => βT.1 c j)) := by
  intro D T ΛT hsd βT hfr J _hJ v
  have key := GlobalTheory.FrameIdeal.key_iff hsd hfr J v
  rw [← GlobalTheory.FrameIdeal.mem_hatL_smul_iff βT ΛT hfr] at key
  unfold GlobalTheory.FrameIdeal.InId at key
  exact key
