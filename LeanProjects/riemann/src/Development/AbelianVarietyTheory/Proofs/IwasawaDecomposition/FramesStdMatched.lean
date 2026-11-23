import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralChangeBaseFrameOrthonormal
import Formalism.LocalToGlobal.IndefiniteReal.FrameExistence.SelfDualFramesExistOfDiagonal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCompatFiniteIsometry
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsometryMatchesParahoricLevels
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicUnitaryEqRealMulFiniteSplit

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

noncomputable section

set_option synthInstance.maxHeartbeats 200000

namespace GlobalTheory.StdFrameExist

variable {D : D7}

abbrev SI (D : D7) : Subring (Lev.EAf D) := Formalism.L2.Herm.intAf D.host.F D.host.E

theorem intAf_eq (D : D7) : (SI D : Subring (Lev.EAf D)) = ReciprocityTheory.Aut.ALint D.host.E := by
  apply le_antisymm
  · refine Subring.closure_le.2 ?_
    rintro _ (⟨⟨x, hx⟩, rfl⟩ | ⟨⟨y, hy⟩, rfl⟩)
    · obtain ⟨o, rfl⟩ := hx
      exact Subring.subset_closure (Or.inl ⟨o, rfl⟩)
    · exact Subring.subset_closure (Or.inr ⟨y, hy, rfl⟩)
  · rw [ReciprocityTheory.Aut.ALint, Subring.closure_le]
    rintro _ (⟨o, rfl⟩ | ⟨a, ha, rfl⟩)
    · exact Subring.subset_closure (Or.inl ⟨⟨_, o, rfl⟩, rfl⟩)
    · exact Subring.subset_closure (Or.inr ⟨⟨a, ha⟩, rfl⟩)

theorem mem_ALint_iff (x : Lev.EAf D) : x ∈ ReciprocityTheory.Aut.ALint D.host.E ↔ x ∈ SI D := by
  rw [intAf_eq]

section Int

variable {R : Type} [CommRing R] (S : Subring R) {n : ℕ}

def IntM (A : Matrix (Fin n) (Fin n) R) : Prop := ∀ i j, A i j ∈ S

variable {S}

theorem intM_mul {A B : Matrix (Fin n) (Fin n) R} (hA : IntM S A) (hB : IntM S B) : IntM S (A * B) := fun i j => by
  rw [Matrix.mul_apply]
  exact S.sum_mem fun k _ => S.mul_mem (hA i k) (hB k j)

theorem intV {A : Matrix (Fin n) (Fin n) R} (hA : IntM S A) {z : Fin n → R} (hz : ∀ i, z i ∈ S) (i : Fin n) :
    (A *ᵥ z) i ∈ S := by
  rw [Matrix.mulVec, dotProduct]
  exact S.sum_mem fun k _ => S.mul_mem (hA i k) (hz k)

theorem intM_of {A : Matrix (Fin n) (Fin n) R} (h : ∀ z : Fin n → R, (∀ i, z i ∈ S) → ∀ i, (A *ᵥ z) i ∈ S) : IntM S A := by
  intro i j
  have := h (Pi.single j 1) (fun k => by
    rw [Pi.single_apply]
    split_ifs
    · exact S.one_mem
    · exact S.zero_mem) i
  rw [Matrix.mulVec_single_one] at this
  exact this

end Int

def kmat {n : ℕ} (κ : Formalism.AUTREP.GAf D.host.E n) : GL (Fin n) (Lev.EAf D) := κ.1

theorem kmat_mul {n : ℕ} (a b : Formalism.AUTREP.GAf D.host.E n) : kmat (a * b) = kmat a * kmat b := rfl

theorem kmat_inv {n : ℕ} (a : Formalism.AUTREP.GAf D.host.E n) : kmat a⁻¹ = (kmat a)⁻¹ := rfl

theorem mem_Umax_iff {n : ℕ} (κ : Formalism.AUTREP.GAf D.host.E n) :
    κ ∈ ReciprocityTheory.Aut.Umax D.host.E n ↔ IntM (SI D) (kmat κ).1 := by
  show (∀ i j, (κ.1 : Matrix (Fin n) (Fin n) (ReciprocityTheory.Aut.AL D.host.E)) i j ∈ ReciprocityTheory.Aut.ALint D.host.E) ↔ _
  exact forall_congr' fun i => forall_congr' fun j => mem_ALint_iff _

theorem umax_iff {n : ℕ} (γ : GL (Fin n) (Lev.EAf D)) (hγ : IntM (SI D) γ.1) (hγ' : IntM (SI D) (γ⁻¹).1)
    (κ : Formalism.AUTREP.GAf D.host.E n) : κ ∈ ReciprocityTheory.Aut.Umax D.host.E n ↔
      ∀ z : Fin n → Lev.EAf D, (∀ i, z i ∈ SI D) ↔ ∀ i, ((γ * kmat κ * γ⁻¹).1 *ᵥ z) i ∈ SI D := by
  constructor
  · intro hκ
    have h1 : IntM (SI D) (γ * kmat κ * γ⁻¹).1 := by
      rw [Units.val_mul, Units.val_mul]
      exact intM_mul (intM_mul hγ ((mem_Umax_iff κ).1 hκ)) hγ'
    have h2 : IntM (SI D) (γ * kmat κ * γ⁻¹)⁻¹.1 := by
      have e : (γ * kmat κ * γ⁻¹)⁻¹ = γ * kmat κ⁻¹ * γ⁻¹ := by rw [kmat_inv]; group
      rw [e, Units.val_mul, Units.val_mul]
      exact intM_mul (intM_mul hγ ((mem_Umax_iff _).1 (inv_mem hκ))) hγ'
    intro z
    refine ⟨fun hz => intV h1 hz, fun hz => ?_⟩
    have := intV h2 hz
    rwa [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec] at this
  · intro h
    have h1 : IntM (SI D) (γ * kmat κ * γ⁻¹).1 := intM_of fun z hz => (h z).1 hz
    have e : kmat κ = γ⁻¹ * (γ * kmat κ * γ⁻¹) * γ := by group
    refine (mem_Umax_iff κ).2 ?_
    rw [e, Units.val_mul, Units.val_mul]
    exact intM_mul (intM_mul hγ' h1) hγ

section Lat

variable {V : HSp D}

theorem tmul_one_mem (o : 𝓞 D.host.E) :
    ((algebraMap (𝓞 D.host.E) D.host.E o) ⊗ₜ[D.host.F] (1 : Formalism.L2.Herm.Af D.host.F) : Lev.EAf D) ∈ SI D :=
  Subring.subset_closure (Or.inl ⟨⟨_, o, rfl⟩, rfl⟩)

theorem one_tmul_mem {a : Formalism.L2.Herm.Af D.host.F} (ha : a ∈ Formalism.MainNotions.StandardLattice.intAf D.host.F) :
    ((1 : D.host.E) ⊗ₜ[D.host.F] a : Lev.EAf D) ∈ SI D :=
  Subring.subset_closure (Or.inr ⟨⟨a, ha⟩, rfl⟩)

theorem one_mem_intAf : (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ∈ Formalism.MainNotions.StandardLattice.intAf D.host.F := fun v => by
  show evalV D.host.F v 1 ∈ _
  rw [map_one]
  exact one_mem _

theorem smul_gen {M : ℕ} (L : Set (Fin M → D.host.E)) (c : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)
    (hc : ∀ a ∈ Formalism.MainNotions.StandardLattice.intAf D.host.F, ∀ x ∈ L, c • (fun i => a ⊗ₜ[D.host.F] x i) ∈ latHat D.host.F D.host.E L)
    {w : Fin M → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E} (hw : w ∈ latHat D.host.F D.host.E L) :
    c • w ∈ latHat D.host.F D.host.E L := by
  induction hw using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨a, ha, x, hx, rfl⟩ := hy
    exact hc a ha x hx
  | zero => rw [smul_zero]; exact zero_mem _
  | add y z _ _ hy hz => rw [smul_add]; exact add_mem hy hz
  | neg y _ hy => rw [smul_neg]; exact neg_mem hy

theorem smul_closure {A B : Type} [CommRing A] [CommRing B] {M : ℕ} (e : B →+* A) (S : AddSubgroup (Fin M → A)) (T : Set B)
    (h : ∀ t ∈ T, ∀ w ∈ S, e t • w ∈ S) {r : B} (hr : r ∈ Subring.closure T) : ∀ w ∈ S, e r • w ∈ S := by
  induction hr using Subring.closure_induction with
  | mem r hr => exact h r hr
  | zero => intro w _; rw [map_zero, zero_smul]; exact zero_mem _
  | one => intro w hw; rwa [map_one, one_smul]
  | add x y _ _ hx hy => intro w hw; rw [map_add, add_smul]; exact add_mem (hx w hw) (hy w hw)
  | neg x _ hx => intro w hw; rw [map_neg, neg_smul]; exact neg_mem (hx w hw)
  | mul x y _ _ hx hy => intro w hw; rw [map_mul, mul_smul]; exact hx _ (hy w hw)

theorem smul_mem (hV : Seed.FrmC.StdLat V) {r : Lev.EAf D} (hr : r ∈ SI D) :
    ∀ w ∈ latHat D.host.F D.host.E (L0c D V), GlobalTheory.HeckeTrans.unswap D r • w ∈ latHat D.host.F D.host.E (L0c D V) := by
  refine smul_closure (GlobalTheory.HeckeTrans.unswap D) _ _ (fun r hr w hw => ?_) hr
  rcases hr with ⟨⟨_, o, rfl⟩, rfl⟩ | ⟨⟨b, hb⟩, rfl⟩
  · refine smul_gen _ _ (fun a ha x hx => AddSubgroup.subset_closure ⟨a, ha, (algebraMap (𝓞 D.host.E) D.host.E o) • x, ?_, ?_⟩) hw
    · refine (hV _).2 fun i => ?_
      rw [Pi.smul_apply, smul_eq_mul]
      exact (RingOfIntegers.isIntegral_coe o).mul ((hV x).1 hx i)
    · funext i
      change ((1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] (algebraMap (𝓞 D.host.E) D.host.E o)) * (a ⊗ₜ[D.host.F] x i) = _
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
      rfl
  · refine smul_gen _ _ (fun a ha x hx => AddSubgroup.subset_closure ⟨b * a, fun v => ?_, x, hx, ?_⟩) hw
    · rw [map_mul]
      exact mul_mem (hb v) (ha v)
    · funext i
      change ((b : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] (1 : D.host.E)) * (a ⊗ₜ[D.host.F] x i) = _
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]

theorem single_mem (hV : Seed.FrmC.StdLat V) (j : Fin V.rank) :
    (Pi.single j 1 : Fin V.rank → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) ∈ latHat D.host.F D.host.E (L0c D V) := by
  refine AddSubgroup.subset_closure ⟨1, one_mem_intAf, Pi.single j 1, (hV _).2 fun a => ?_, ?_⟩
  · rw [Pi.single_apply]
    split_ifs
    · exact isIntegral_one
    · exact isIntegral_zero
  · funext i
    rw [Pi.single_apply, Pi.single_apply]
    split_ifs
    · rfl
    · rw [TensorProduct.tmul_zero]

theorem latHat_iff (hV : Seed.FrmC.StdLat V) (y : Fin V.rank → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) :
    y ∈ latHat D.host.F D.host.E (L0c D V) ↔ ∀ i, swapAE D (y i) ∈ SI D := by
  constructor
  · intro hy i
    induction hy using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨a, ha, x, hx, rfl⟩ := hy
      obtain ⟨o, ho⟩ := (IsIntegralClosure.isIntegral_iff (A := 𝓞 D.host.E)).1 ((hV x).1 hx i)
      change (x i ⊗ₜ[D.host.F] a : Lev.EAf D) ∈ SI D
      rw [← ho, show ((algebraMap (𝓞 D.host.E) D.host.E o) ⊗ₜ[D.host.F] a : Lev.EAf D) =
        ((algebraMap (𝓞 D.host.E) D.host.E o) ⊗ₜ[D.host.F] (1 : Formalism.L2.Herm.Af D.host.F)) * ((1 : D.host.E) ⊗ₜ[D.host.F] a) by
          rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]]
      exact (SI D).mul_mem (tmul_one_mem o) (one_tmul_mem ha)
    | zero => rw [Pi.zero_apply, map_zero]; exact zero_mem _
    | add y z _ _ hy hz => rw [Pi.add_apply, map_add]; exact add_mem hy hz
    | neg y _ hy => rw [Pi.neg_apply, map_neg]; exact neg_mem hy
  · intro hy
    rw [pi_eq_sum_univ' y]
    refine sum_mem fun i _ => ?_
    have := smul_mem hV (hy i) _ (single_mem hV i)
    rwa [GlobalTheory.HeckeTrans.unswap_swap] at this

theorem swap_mulVec (Y : Matrix (Fin V.rank) (Fin V.rank) (Lev.EAf D))
    (y : Fin V.rank → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) (i : Fin V.rank) :
    swapAE D ((Y.map (GlobalTheory.HeckeTrans.unswap D) *ᵥ y) i) = (Y *ᵥ fun j => swapAE D (y j)) i := by
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, map_mul, GlobalTheory.HeckeTrans.swap_unswap]

theorem ksph_iff (hV : Seed.FrmC.StdLat V) {g : GA D V} (hg : g ∈ GfC V) :
    g ∈ KsphC V ∅ ↔ ∀ z : Fin V.rank → Lev.EAf D, (∀ i, z i ∈ SI D) ↔ ∀ i, ((finE V g).1 *ᵥ z) i ∈ SI D := by
  constructor
  · rintro ⟨-, h, -⟩ z
    have := h (fun j => GlobalTheory.HeckeTrans.unswap D (z j))
    rw [← GlobalTheory.HeckeTrans.finE_unswap] at this
    simp only [latHat_iff hV, swap_mulVec, GlobalTheory.HeckeTrans.swap_unswap] at this
    exact this
  · intro h
    refine ⟨hg, fun y => ?_, fun v hv => absurd hv (Finset.notMem_empty v)⟩
    rw [← GlobalTheory.HeckeTrans.finE_unswap]
    simp only [latHat_iff hV, swap_mulVec]
    exact h _

end Lat

end GlobalTheory.StdFrameExist

namespace GlobalTheory.StdFrameExist

variable {D : D7}

theorem unswap_sg (y : Lev.EAf D) : GlobalTheory.HeckeTrans.unswap D (Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F) y) =
    sigR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig (GlobalTheory.HeckeTrans.unswap D y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul x a => rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

variable (V : HSp D)

theorem unswap_mem (x : GL (Fin V.rank) (Lev.EAf D)) (hx : x ∈ Formalism.L2.DIV.UA D.sp.cm V.gram) :
    Formalism.UG.bc (GlobalTheory.HeckeTrans.unswap D) x ∈ HR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram := by
  have h : Formalism.UG.cT (Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F)) x.1 *
      V.gram.map (Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F)) * x.1 =
      V.gram.map (Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F)) := hx
  have h2 := congrArg (fun M => Matrix.map M (GlobalTheory.HeckeTrans.unswap D)) h
  simp only [Matrix.map_mul] at h2
  have e1 : (Formalism.UG.cT (Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F)) x.1).map (GlobalTheory.HeckeTrans.unswap D) =
      Formalism.UG.cT (sigR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig) (x.1.map (GlobalTheory.HeckeTrans.unswap D)) := by
    ext i j
    exact unswap_sg _
  have e2 : (V.gram.map (Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F))).map (GlobalTheory.HeckeTrans.unswap D) =
      JR (F := D.host.F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) V.gram := by
    ext i j
    rfl
  rw [e1, e2] at h2
  exact h2

def liftF (x : GL (Fin V.rank) (Lev.EAf D)) (hx : x ∈ Formalism.L2.DIV.UA D.sp.cm V.gram) : GA D V :=
  (GlobalTheory.UnitarySplit.ga_glue V 1 (Formalism.UG.bc (GlobalTheory.HeckeTrans.unswap D) x) (one_mem _) (unswap_mem V x hx)).choose

theorem liftF_mem (x : GL (Fin V.rank) (Lev.EAf D)) (hx : x ∈ Formalism.L2.DIV.UA D.sp.cm V.gram) : liftF V x hx ∈ GfC V :=
  MonoidHom.mem_ker.2 (GlobalTheory.UnitarySplit.ga_glue V 1 (Formalism.UG.bc (GlobalTheory.HeckeTrans.unswap D) x) (one_mem _) (unswap_mem V x hx)).choose_spec.1

theorem finE_liftF (x : GL (Fin V.rank) (Lev.EAf D)) (hx : x ∈ Formalism.L2.DIV.UA D.sp.cm V.gram) : finE V (liftF V x hx) = x := by
  have h := (GlobalTheory.UnitarySplit.ga_glue V 1 (Formalism.UG.bc (GlobalTheory.HeckeTrans.unswap D) x) (one_mem _) (unswap_mem V x hx)).choose_spec.2
  apply Units.ext
  ext i j
  show swapAE D ((finHom V (liftF V x hx)).1 i j) = x.1 i j
  rw [show liftF V x hx = (GlobalTheory.UnitarySplit.ga_glue V 1 (Formalism.UG.bc (GlobalTheory.HeckeTrans.unswap D) x) (one_mem _) (unswap_mem V x hx)).choose from rfl, h]
  exact GlobalTheory.HeckeTrans.swap_unswap _

end GlobalTheory.StdFrameExist

namespace GlobalTheory.StdFrameExist

variable {D : D7}

abbrev sgA (D : D7) : Lev.EAf D →+* Lev.EAf D := Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F)

abbrev gA (V : HSp D) : Matrix (Fin V.rank) (Fin V.rank) (Lev.EAf D) :=
  V.gram.map (Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F))

theorem conjAL_eq (y : ReciprocityTheory.Aut.AL D.host.E) : ReciprocityTheory.Aut.conjAL D.host.E y = sgA D y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul x a => rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem conjT_eq {n : ℕ} (M : Matrix (Fin n) (Fin n) (Lev.EAf D)) :
    ReciprocityTheory.Aut.conjT (ReciprocityTheory.Aut.conjAL D.host.E) M = Formalism.UG.cT (sgA D) M := by
  ext i j
  exact conjAL_eq _

theorem cT_kmat {n : ℕ} (κ : Formalism.AUTREP.GAf D.host.E n) : Formalism.UG.cT (sgA D) (kmat κ).1 * (kmat κ).1 = 1 := by
  have h : (kmat κ).1 * ReciprocityTheory.Aut.conjT (ReciprocityTheory.Aut.conjAL D.host.E) (kmat κ).1 = 1 := κ.2
  rw [conjT_eq] at h
  exact mul_eq_one_comm.1 h

theorem mem_GA {n : ℕ} (x : GL (Fin n) (Lev.EAf D)) (h : Formalism.UG.cT (sgA D) x.1 * x.1 = 1) :
    (x : GL (Fin n) (ReciprocityTheory.Aut.AL D.host.E)) ∈ ReciprocityTheory.Aut.GA D.host.E n := by
  show x.1 * ReciprocityTheory.Aut.conjT (ReciprocityTheory.Aut.conjAL D.host.E) x.1 = 1
  rw [conjT_eq]
  exact mul_eq_one_comm.1 h

variable (V : HSp D) (γ : GL (Fin V.rank) (Lev.EAf D))

def IsOrthF : Prop := Formalism.UG.cT (sgA D) γ.1 * gA V * γ.1 = 1

variable {V γ}

theorem cT_inv_mul (h : IsOrthF V γ) : Formalism.UG.cT (sgA D) (γ⁻¹).1 * (γ⁻¹).1 = gA V := by
  have h1 : Formalism.UG.cT (sgA D) (γ⁻¹).1 * Formalism.UG.cT (sgA D) γ.1 = 1 := by
    rw [← Formalism.UG.cT_mul, Units.mul_inv, Formalism.UG.cT_one]
  calc Formalism.UG.cT (sgA D) (γ⁻¹).1 * (γ⁻¹).1
      = Formalism.UG.cT (sgA D) (γ⁻¹).1 * (Formalism.UG.cT (sgA D) γ.1 * gA V * γ.1) * (γ⁻¹).1 := by
        rw [h, Matrix.mul_one]
    _ = (Formalism.UG.cT (sgA D) (γ⁻¹).1 * Formalism.UG.cT (sgA D) γ.1) * gA V * (γ.1 * (γ⁻¹).1) := by
        simp only [Matrix.mul_assoc]
    _ = gA V := by rw [h1, Units.mul_inv, Matrix.one_mul, Matrix.mul_one]

theorem conj_mem (h : IsOrthF V γ) (κ : Formalism.AUTREP.GAf D.host.E V.rank) :
    γ * kmat κ * γ⁻¹ ∈ Formalism.L2.DIV.UA D.sp.cm V.gram := by
  show Formalism.UG.cT (sgA D) (γ * kmat κ * γ⁻¹).1 * gA V * (γ * kmat κ * γ⁻¹).1 = gA V
  rw [Units.val_mul, Units.val_mul, Formalism.UG.cT_mul, Formalism.UG.cT_mul]
  calc _ = Formalism.UG.cT (sgA D) (γ⁻¹).1 * (Formalism.UG.cT (sgA D) (kmat κ).1 * (Formalism.UG.cT (sgA D) γ.1 * gA V * γ.1) * (kmat κ).1) *
        (γ⁻¹).1 := by simp only [Matrix.mul_assoc]
    _ = gA V := by rw [h, Matrix.mul_one, cT_kmat, Matrix.mul_one, cT_inv_mul h]

variable (V γ)

def psiF (h : IsOrthF V γ) (κ : Formalism.AUTREP.GAf D.host.E V.rank) : GA D V :=
  liftF V (γ * kmat κ * γ⁻¹) (conj_mem h κ)

variable {V γ}

theorem finE_psiF (h : IsOrthF V γ) (κ : Formalism.AUTREP.GAf D.host.E V.rank) : finE V (psiF V γ h κ) = γ * kmat κ * γ⁻¹ :=
  finE_liftF V _ _

theorem psiF_mem (h : IsOrthF V γ) (κ : Formalism.AUTREP.GAf D.host.E V.rank) : psiF V γ h κ ∈ GfC V :=
  liftF_mem V _ _

theorem ext_GfC {g g' : GA D V} (hg : g ∈ GfC V) (hg' : g' ∈ GfC V) (e : finE V g = finE V g') : g = g' := by
  refine GlobalTheory.UnitarySplit.ga_ext V ((MonoidHom.mem_ker.1 hg).trans (MonoidHom.mem_ker.1 hg').symm) ?_
  apply Units.ext
  ext i j
  have := congrArg (fun x : GL (Fin V.rank) (Lev.EAf D) => GlobalTheory.HeckeTrans.unswap D (x.1 i j)) e
  exact (GlobalTheory.HeckeTrans.unswap_swap _).symm.trans (this.trans (GlobalTheory.HeckeTrans.unswap_swap _))

variable (V γ)

def rowPsi (h : IsOrthF V γ) : principalLevelFrame.RowPsi V V.rank where
  ψ := MonoidHom.mk' (psiF V γ h) fun a b => by
    refine ext_GfC (psiF_mem h _) (mul_mem (psiF_mem h _) (psiF_mem h _)) ?_
    rw [map_mul, finE_psiF, finE_psiF, finE_psiF, kmat_mul]
    group
  inj := fun a b hab => by
    have e := congrArg (finE V) hab
    simp only [MonoidHom.mk'_apply, finE_psiF] at e
    have e2 : kmat a = kmat b := mul_left_cancel (mul_right_cancel e)
    exact Subtype.ext e2
  into := fun κ => psiF_mem h κ
  onto := fun g hg => by
    have hx := GlobalTheory.LevTrans.finE_unitary V g
    have hM : Formalism.UG.cT (sgA D) (finE V g).1 * gA V * (finE V g).1 = gA V := hx
    let κ0 : GL (Fin V.rank) (Lev.EAf D) := γ⁻¹ * finE V g * γ
    have hk : Formalism.UG.cT (sgA D) κ0.1 * κ0.1 = 1 := by
      show Formalism.UG.cT (sgA D) (γ⁻¹ * finE V g * γ).1 * (γ⁻¹ * finE V g * γ).1 = 1
      rw [Units.val_mul, Units.val_mul, Formalism.UG.cT_mul, Formalism.UG.cT_mul]
      calc _ = Formalism.UG.cT (sgA D) γ.1 * (Formalism.UG.cT (sgA D) (finE V g).1 *
            (Formalism.UG.cT (sgA D) (γ⁻¹).1 * (γ⁻¹).1) * (finE V g).1) * γ.1 := by simp only [Matrix.mul_assoc]
        _ = 1 := by rw [cT_inv_mul h, hM]; exact h
    refine ⟨⟨κ0, mem_GA κ0 hk⟩, ext_GfC (psiF_mem h _) hg ?_⟩
    show finE V (psiF V γ h _) = _
    rw [finE_psiF]
    show γ * (γ⁻¹ * finE V g * γ) * γ⁻¹ = _
    group

end GlobalTheory.StdFrameExist

namespace GlobalTheory.StdFrameExist

variable {D : D7}

section Std

variable {V : HSp D} {γ : GL (Fin V.rank) (Lev.EAf D)}

theorem stdFrame_rowPsi (hF : D.host.F = maximalRealSubfield D.host.E) (hV : Seed.FrmC.StdLat V) (h : IsOrthF V γ)
    (hγ : IntM (SI D) γ.1) (hγ' : IntM (SI D) (γ⁻¹).1) : StdFrame hF (rowPsi V γ h) := by
  refine ⟨⟨γ.1.map (GlobalTheory.HeckeTrans.unswap D), (γ⁻¹).1.map (GlobalTheory.HeckeTrans.unswap D), ?_, ?_, fun κ => ?_⟩, fun κ => ?_⟩
  · rw [← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]
  · rw [← Matrix.map_mul, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]
  · rw [← GlobalTheory.HeckeTrans.finE_unswap]
    show (finE V (psiF V γ h κ)).1.map _ = _
    rw [finE_psiF, Units.val_mul, Units.val_mul, Matrix.map_mul, Matrix.map_mul]
    rfl
  · have e : (rowPsi V γ h).ψ κ = psiF V γ h κ := rfl
    rw [e, umax_iff γ hγ hγ' κ, ksph_iff hV (psiF_mem h κ), finE_psiF]

theorem exists_std (hF : D.host.F = maximalRealSubfield D.host.E) (V : HSp D) (hV : Seed.FrmC.StdLat V) (n : ℕ)
    (hn : V.rank = n) : ∃ P : principalLevelFrame.RowPsi V n, StdFrame hF P := by
  subst hn
  obtain ⟨c, hB⟩ := Seed.FrmP.isSDFrame_std V hV 1
  obtain ⟨u, hu⟩ := GlobalTheory.AdelicOrthFrame.exists_orthonormal_baseFrame V 1 _ _ hB
  rw [one_mul] at hu
  refine ⟨rowPsi V (intGL D.host.F D.host.E V.rank u) hu, stdFrame_rowPsi hF hV hu (fun i j => (u.1 i j).2) ?_⟩
  rw [← map_inv]
  exact fun i j => ((u⁻¹).1 i j).2

end Std

section Match

theorem block_frame_conjugation_identity {R : Type} [CommRing R] {a b c : ℕ} (βW : Matrix (Fin a) (Fin b) R) (βY' : Matrix (Fin b) (Fin c) R)
    (βY : Matrix (Fin c) (Fin b) R) (βW' : Matrix (Fin b) (Fin a) R) (K : Matrix (Fin b) (Fin b) R) (h : βY' * βY = 1) :
    βW * K * βW' = βW * βY' * (βY * K * βY') * (βY * βW') := by
  rw [show βW * βY' * (βY * K * βY') * (βY * βW') = βW * (βY' * βY) * K * (βY' * βY) * βW' by simp only [Matrix.mul_assoc], h]
  simp only [Matrix.mul_one]

variable {Y W : HSp D} {n : ℕ}

def eqvF (P : principalLevelFrame.RowPsi Y n) : Formalism.AUTREP.GAf D.host.E n ≃* GfC Y :=
  MulEquiv.ofBijective (P.ψ.codRestrict (GfC Y) P.into)
    ⟨fun a b hab => P.inj (congrArg Subtype.val hab), fun g => by
      obtain ⟨h, hh⟩ := P.onto g.1 g.2
      exact ⟨h, Subtype.ext hh⟩⟩

theorem eqvF_apply (P : principalLevelFrame.RowPsi Y n) (h : Formalism.AUTREP.GAf D.host.E n) : ((eqvF P h : GfC Y) : GA D Y) = P.ψ h := rfl

variable (PY : principalLevelFrame.RowPsi Y n) (PW : principalLevelFrame.RowPsi W n)

def transF : GfC Y →* GfC W := (eqvF PW).toMonoidHom.comp (eqvF PY).symm.toMonoidHom

theorem transF_eqvF (κ : Formalism.AUTREP.GAf D.host.E n) : transF PY PW (eqvF PY κ) = eqvF PW κ := by
  show eqvF PW ((eqvF PY).symm (eqvF PY κ)) = _
  rw [MulEquiv.symm_apply_apply]

theorem isIsomFin_transF (hF : D.host.F = maximalRealSubfield D.host.E) (hY : StdFrame hF PY) (hW : StdFrame hF PW) :
    principalLevelFrame.IsIsomFin (transF PY PW) := by
  obtain ⟨⟨βY, βY', hY1, hY2, hYf⟩, hYk⟩ := hY
  obtain ⟨⟨βW, βW', hW1, hW2, hWf⟩, hWk⟩ := hW
  refine ⟨(eqvF PW).bijective.comp (eqvF PY).symm.bijective, ⟨βW * βY', βY * βW', ?_, ?_, fun g => ?_⟩, fun g => ?_⟩
  · rw [show βW * βY' * (βY * βW') = βW * (βY' * βY) * βW' by simp only [Matrix.mul_assoc], hY2, Matrix.mul_one, hW1]
  · rw [show βY * βW' * (βW * βY') = βY * (βW' * βW) * βY' by simp only [Matrix.mul_assoc], hW2, Matrix.mul_one, hY1]
  · obtain ⟨κ, rfl⟩ := (eqvF PY).surjective g
    rw [transF_eqvF, eqvF_apply, eqvF_apply, hWf κ, hYf κ]
    exact block_frame_conjugation_identity _ _ _ _ _ hY2
  · obtain ⟨κ, rfl⟩ := (eqvF PY).surjective g
    rw [transF_eqvF, eqvF_apply, eqvF_apply, ← hYk κ, hWk κ]

theorem frameMatch_transF : principalLevelFrame.FrameMatch PY PW (transF PY PW) := by
  refine ⟨1, fun h => ?_⟩
  rw [inv_one, one_mul, mul_one]
  show _ = ((transF PY PW (eqvF PY h) : GfC W) : GA D W)
  rw [transF_eqvF]
  rfl

end Match

theorem frames_std_matched : ∀ (D : D7) (hF : D.host.F = maximalRealSubfield D.host.E), Seed.FrmC.StdLat (Yc D 0) → (∀ i, Seed.FrmC.StdLat (Wc D i)) → ∃ (PY : principalLevelFrame.RowPsi (Yc D 0) D.R.r) (PW : ∀ i, principalLevelFrame.RowPsi (Wc D i) D.R.r) (ιW : ∀ i, ↥(GfC (Yc D 0)) →* ↥(GfC (Wc D i))), StdFrame hF PY ∧ (∀ i, StdFrame hF (PW i)) ∧ (∀ i, principalLevelFrame.IsIsomFin (ιW i)) ∧ ∀ i, principalLevelFrame.FrameMatch PY (PW i) (ιW i) := by
  intro D hF hY hW
  have rY : (Yc D 0).rank = D.R.r := by
    show (D.sp.Y (min 0 D.R.m)).rank = _
    rw [Nat.zero_min, D.sp.Y_rank 0 (Nat.zero_le _)]
    simp [Formalism.BasicNotions.Ranks.rankY]
  obtain ⟨PY, hPY⟩ := exists_std hF (Yc D 0) hY D.R.r rY
  choose PW hPW using fun i : Fin D.R.m => exists_std hF (Wc D i) (hW i) D.R.r (D.sp.W_rank _ (by omega) (by omega))
  exact ⟨PY, PW, fun i => transF PY (PW i), hPY, hPW, fun i => isIsomFin_transF PY (PW i) hF hPY (hPW i),
    fun i => frameMatch_transF PY (PW i)⟩

end GlobalTheory.StdFrameExist

end
