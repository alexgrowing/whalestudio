import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelSplitting.UnipotentRadicalActionFormula
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelSplitting.NCDefs
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelSplitting.ToMatrixLin

noncomputable section

namespace PI.LevelKSplit.W.NCH

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub PI.VolSemiDirect.W PI.VolSemiDirect.W.PG
  PI.VolSemiDirect.W.PG.Dat
open scoped TensorProduct Matrix

section Gen

variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] {r : ℕ} {D : Dat A n r}

theorem fix_span {Φ : (n → A) →ₗ[A] (n → A)} (he : ∀ a, Φ (D.e a) = D.e a) {x : n → A}
    (hx : x ∈ Submodule.span A (Set.range D.e)) : Φ x = x := by
  first
  | exact LinearMap.eqOn_span' (f := Φ) (g := LinearMap.id) (by rintro _ ⟨a, rfl⟩; exact he a) hx
  | (induction hx using Submodule.span_induction with
      | mem y hy => obtain ⟨a, rfl⟩ := hy; exact he a
      | zero => exact map_zero Φ
      | add y z _ _ hy hz => rw [map_add, hy, hz]
      | smul c y _ hy => rw [map_smul, hy])

def sMat (D : Dat A n r) (half : A) (y : Fin r → n → A) : Matrix n n A :=
  LinearMap.toMatrix' (sL D half y)

end Gen

section R

variable {F E : Type} [Field F] [Field E] [Algebra F E] {R : Type} [CommRing R] [Algebra F R]
  {σ : E →ₐ[F] E} {M : ℕ} {J : Matrix (Fin M) (Fin M) E} {r : ℕ} {P : Frame E M r} {T : F}

theorem spanR_eq :
    spanR (F := F) R P.e Set.univ =
      Submodule.span (R ⊗[F] E) (Set.range (datR R σ J P T).e) := by
  unfold spanR
  rw [Set.image_univ]
  rfl

theorem pWp_eq (x : Fin M → R ⊗[F] E) :
    PI.LevelKSplit.W.NC.pWp R σ J P x = pWp (datR R σ J P T) x := by
  rw [pWp_apply, pX_apply, pXv_apply]
  rfl

theorem yH_eq (g : HA R σ J) (a : Fin r) :
    PI.LevelKSplit.W.NC.yH R σ J P g a =
      pWp (datR R σ J P T) (lin R σ J g ((datR R σ J P T).f a)) :=
  pWp_eq _

theorem uni_lin (g : HA R σ J) : (datR R σ J P T).Uni (lin R σ J g) := fun x y => hR_lin g x y

theorem unipotent_radical_fixes_frame {g : HA R σ J} (hg : g ∈ PI.LevelKSplit.W.NC.LevelUnipotentSubgroup R σ J P) (a : Fin r) :
    lin R σ J g ((datR R σ J P T).e a) = (datR R σ J P T).e a :=
  (mem_stabT R σ J P.e g).1 hg.2 a

theorem N_perp {g : HA R σ J} (hg : g ∈ Nsub R σ J P) (v : Fin M → R ⊗[F] E)
    (hv : Xp (datR R σ J P T) v) :
    lin R σ J g v - v ∈ Submodule.span (R ⊗[F] E) (Set.range (datR R σ J P T).e) := by
  have hg' : UniC R σ J P.e g ∧ ∀ v, InXperp R σ J P v →
      lin R σ J g v - v ∈ spanR (F := F) R P.e Set.univ := hg
  rw [← spanR_eq]
  exact hg'.2 v hv

theorem mem_unipotent_radical_of {g : HA R σ J}
    (he : ∀ a, lin R σ J g ((datR R σ J P T).e a) = (datR R σ J P T).e a)
    (hp : ∀ v, Xp (datR R σ J P T) v →
      lin R σ J g v - v ∈ Submodule.span (R ⊗[F] E) (Set.range (datR R σ J P T).e)) :
    g ∈ PI.LevelKSplit.W.NC.LevelUnipotentSubgroup R σ J P := by
  refine ⟨⟨fun b => ?_, fun v hv => ?_⟩, (mem_stabT R σ J P.e g).2 he⟩
  · have hb : lin R σ J g (ratV (F := F) R (P.e b)) = ratV (F := F) R (P.e b) := he b
    rw [hb, sub_self]
    exact Submodule.zero_mem _
  · rw [spanR_eq (σ := σ) (J := J) (T := T)]
    exact hp v hv

theorem hJi (hJ : IsHermND σ J) : (J⁻¹).map (inclR (F := F) R) * JR R J = 1 := by
  rw [JR, ← Matrix.map_mul, Matrix.nonsing_inv_mul J (isUnit_iff_ne_zero.2 hJ.2)]
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem nd_datR (hJ : IsHermND σ J) : ND (datR R σ J P T) := by
  intro x hx
  have hJx : JR R J *ᵥ x = 0 := by
    funext i
    have h1 := hx (Pi.single i (1 : R ⊗[F] E))
    have hs : ∀ k, sigR R σ ((Pi.single i (1 : R ⊗[F] E) : Fin M → R ⊗[F] E) k) =
        (Pi.single i (1 : R ⊗[F] E) : Fin M → R ⊗[F] E) k := fun k => by
      rcases eq_or_ne k i with rfl | hk
      · rw [Pi.single_eq_same, map_one]
      · rw [Pi.single_eq_of_ne hk, map_zero]
    change ∑ k, ∑ j, sigR R σ ((Pi.single i (1 : R ⊗[F] E) : Fin M → R ⊗[F] E) k) * JR R J k j *
      x j = 0 at h1
    simp only [Pi.single_apply, zero_mul] at h1
    simpa [Matrix.mulVec, dotProduct] using h1
  rw [← Matrix.one_mulVec x, ← hJi (R := R) hJ, ← Matrix.mulVec_mulVec, hJx, Matrix.mulVec_zero]

section Sec

variable (hJ : IsHermND σ J) (H : (datR R σ J P T).Hyp) {half : R ⊗[F] E}
  (hh : Half (datR R σ J P T) half)
include hJ H hh

theorem sMat_uj {y : Fin r → Fin M → R ⊗[F] E} (hy : ∀ a, IsWp (datR R σ J P T) (y a)) :
    Formalism.UG.cT (sigR R σ) (sMat (datR R σ J P T) half y) * JR R J * sMat (datR R σ J P T) half y =
      JR R J :=
  PI.LevelKSplit.W.SemiA.uj_of_uni _ _ _ fun x x' => by
    rw [sMat, LinearMap.toMatrix'_mulVec, LinearMap.toMatrix'_mulVec]
    exact sL_uni H hy hh x x'

theorem sMat_linv {y : Fin r → Fin M → R ⊗[F] E} (hy : ∀ a, IsWp (datR R σ J P T) (y a)) :
    (J⁻¹).map (inclR (F := F) R) * Formalism.UG.cT (sigR R σ) (sMat (datR R σ J P T) half y) * JR R J *
      sMat (datR R σ J P T) half y = 1 := by
  have e : (J⁻¹).map (inclR (F := F) R) * Formalism.UG.cT (sigR R σ) (sMat (datR R σ J P T) half y) *
      JR R J * sMat (datR R σ J P T) half y = (J⁻¹).map (inclR (F := F) R) *
      (Formalism.UG.cT (sigR R σ) (sMat (datR R σ J P T) half y) * JR R J *
        sMat (datR R σ J P T) half y) := by
    simp only [Matrix.mul_assoc]
  rw [e, sMat_uj hJ H hh hy, hJi hJ]

def sU {y : Fin r → Fin M → R ⊗[F] E} (hy : ∀ a, IsWp (datR R σ J P T) (y a)) :
    GL (Fin M) (R ⊗[F] E) where
  val := sMat (datR R σ J P T) half y
  inv := (J⁻¹).map (inclR (F := F) R) * Formalism.UG.cT (sigR R σ) (sMat (datR R σ J P T) half y) *
    JR R J
  val_inv := mul_eq_one_comm.2 (sMat_linv hJ H hh hy)
  inv_val := sMat_linv hJ H hh hy

theorem sU_mem {y : Fin r → Fin M → R ⊗[F] E} (hy : ∀ a, IsWp (datR R σ J P T) (y a)) :
    sU hJ H hh hy ∈ HR R σ J := by
  first
  | exact sMat_uj hJ H hh hy
  | (simp only [HR]; exact sMat_uj hJ H hh hy)
  | (simp [HR, sU]; exact sMat_uj hJ H hh hy)

def sHG {y : Fin r → Fin M → R ⊗[F] E} (hy : ∀ a, IsWp (datR R σ J P T) (y a)) : HA R σ J :=
  ⟨sU hJ H hh hy, sU_mem hJ H hh hy⟩

theorem lin_sHG {y : Fin r → Fin M → R ⊗[F] E} (hy : ∀ a, IsWp (datR R σ J P T) (y a)) :
    lin R σ J (sHG hJ H hh hy) = sL (datR R σ J P T) half y := by
  unfold lin
  simp [sHG, sU, HA.mat, sMat]
  first
  | exact Matrix.toLin'_toMatrix' _
  | exact LinearMap.ext fun x => LinearMap.toMatrix'_mulVec _ x

theorem sHG_mem {y : Fin r → Fin M → R ⊗[F] E} (hy : ∀ a, IsWp (datR R σ J P T) (y a)) :
    sHG hJ H hh hy ∈ PI.LevelKSplit.W.NC.LevelUnipotentSubgroup R σ J P := by
  refine mem_unipotent_radical_of (T := T) (fun a => ?_) (fun v hv => ?_)
  · rw [lin_sHG]
    exact sL_e H hy a
  · rw [lin_sHG, sL_Xp H hy hv, sub_sub_cancel_left]
    exact Submodule.neg_mem _ (Submodule.sum_mem _ fun b _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, rfl⟩))

theorem yH_sHG {y : Fin r → Fin M → R ⊗[F] E} (hy : ∀ a, IsWp (datR R σ J P T) (y a)) (a : Fin r) :
    PI.LevelKSplit.W.NC.yH R σ J P (sHG hJ H hh hy) a = y a := by
  rw [yH_eq (T := T), lin_sHG]
  exact pWp_sL_f H hy a

theorem isWp_yH (g : HA R σ J) (a : Fin r) :
    IsWp (datR R σ J P T) (PI.LevelKSplit.W.NC.yH R σ J P g a) := by
  rw [yH_eq (T := T)]
  exact pWp_isWp H _

theorem N_xp {g : HA R σ J} (hg : g ∈ Nsub R σ J P) {v : Fin M → R ⊗[F] E}
    (hv : Xp (datR R σ J P T) v) : Xp (datR R σ J P T) (lin R σ J g v) := by
  have e : lin R σ J g v = v + (lin R σ J g v - v) := by abel
  rw [e]
  exact xp_add hv (xp_of_span H (N_perp hg v hv))

theorem unipotent_radical_action {g : HA R σ J} (hg : g ∈ PI.LevelKSplit.W.NC.LevelUnipotentSubgroup R σ J P)
    {v : Fin M → R ⊗[F] E} (hv : Xp (datR R σ J P T) v) :
    lin R σ J g v = v - ∑ a, (datR R σ J P T).h (PI.LevelKSplit.W.NC.yH R σ J P g a) v •
      (datR R σ J P T).e a := by
  simp only [yH_eq (T := T)]
  exact unipotent_radical_action_formula H (uni_lin g) (unipotent_radical_fixes_frame hg) (N_perp hg.1) hv

theorem inv_mul_mem_Z {g : HA R σ J} (hg : g ∈ PI.LevelKSplit.W.NC.LevelUnipotentSubgroup R σ J P) :
    (sHG hJ H hh (isWp_yH hJ H hh g))⁻¹ * g ∈ PI.LevelKSplit.W.NC.Zsub R σ J P := by
  refine ⟨(Nsub R σ J P).mul_mem ((Nsub R σ J P).inv_mem (sHG_mem hJ H hh _).1) hg.1,
    fun v hv => ?_⟩
  have e : lin R σ J g v = lin R σ J (sHG hJ H hh (isWp_yH hJ H hh g)) v := by
    rw [unipotent_radical_action hJ H hh hg hv, unipotent_radical_action hJ H hh (sHG_mem hJ H hh _) hv]
    simp only [yH_sHG]
  rw [lin_mul, e, lin_inv_lin]

theorem centre_le_unipotent_radical : PI.LevelKSplit.W.NC.Zsub R σ J P ≤ PI.LevelKSplit.W.NC.LevelUnipotentSubgroup R σ J P :=
  fun z hz => ⟨hz.1, (mem_stabT R σ J P.e z).2 fun a => hz.2 _ (xp_e H a)⟩

theorem Z_fix {z : HA R σ J} (hz : z ∈ PI.LevelKSplit.W.NC.Zsub R σ J P) {v : Fin M → R ⊗[F] E}
    (hv : Xp (datR R σ J P T) v) : lin R σ J z v = v :=
  hz.2 v hv

theorem Z_f {z : HA R σ J} (hz : z ∈ PI.LevelKSplit.W.NC.Zsub R σ J P) (a : Fin r) :
    lin R σ J z ((datR R σ J P T).f a) - (datR R σ J P T).f a ∈
      Submodule.span (R ⊗[F] E) (Set.range (datR R σ J P T).e) :=
  fix_f_mem H (nd_datR hJ) (uni_lin z) (fun v hv => Z_fix hJ H hh hz hv) a

theorem yH_mul_Z {g : HA R σ J} (hg : g ∈ PI.LevelKSplit.W.NC.LevelUnipotentSubgroup R σ J P) {z : HA R σ J}
    (hz : z ∈ PI.LevelKSplit.W.NC.Zsub R σ J P) (a : Fin r) :
    PI.LevelKSplit.W.NC.yH R σ J P (g * z) a = PI.LevelKSplit.W.NC.yH R σ J P g a := by
  rw [yH_eq (T := T), yH_eq (T := T), lin_mul]
  have e : lin R σ J z ((datR R σ J P T).f a) = (datR R σ J P T).f a +
      (lin R σ J z ((datR R σ J P T).f a) - (datR R σ J P T).f a) := by abel
  rw [e, map_add, fix_span (unipotent_radical_fixes_frame hg) (Z_f hJ H hh hz a), map_add, pWp_span H (Z_f hJ H hh hz a),
    add_zero]

theorem Z_comm {z : HA R σ J} (hz : z ∈ PI.LevelKSplit.W.NC.Zsub R σ J P) {g : HA R σ J}
    (hg : g ∈ PI.LevelKSplit.W.NC.LevelUnipotentSubgroup R σ J P) : z * g = g * z := by
  apply PI.LevelKSplit.W.SemiA.ext_lin
  intro v
  rw [lin_mul, lin_mul]
  refine ext_Xp_f H (Φ := (lin R σ J z).comp (lin R σ J g)) (Ψ := (lin R σ J g).comp (lin R σ J z))
    (fun v hv => ?_) (fun a => ?_) v
  · simp only [LinearMap.comp_apply]
    rw [Z_fix hJ H hh hz (N_xp hJ H hh hg.1 hv), Z_fix hJ H hh hz hv]
  · simp only [LinearMap.comp_apply]
    have hnf : Xp (datR R σ J P T) (lin R σ J g ((datR R σ J P T).f a) - (datR R σ J P T).f a) := by
      intro b
      have hb : (datR R σ J P T).h ((datR R σ J P T).e b) (lin R σ J g ((datR R σ J P T).f a)) =
          (datR R σ J P T).h ((datR R σ J P T).e b) ((datR R σ J P T).f a) := by
        rw [← uni_lin g ((datR R σ J P T).e b) ((datR R σ J P T).f a), unipotent_radical_fixes_frame hg b]
      rw [h_sub_right, hb, sub_self]
    calc lin R σ J z (lin R σ J g ((datR R σ J P T).f a))
        = lin R σ J z ((datR R σ J P T).f a +
            (lin R σ J g ((datR R σ J P T).f a) - (datR R σ J P T).f a)) := by
          congr 1; abel
      _ = lin R σ J z ((datR R σ J P T).f a) +
            (lin R σ J g ((datR R σ J P T).f a) - (datR R σ J P T).f a) := by
          rw [map_add, Z_fix hJ H hh hz hnf]
      _ = lin R σ J g ((datR R σ J P T).f a) +
            (lin R σ J z ((datR R σ J P T).f a) - (datR R σ J P T).f a) := by abel
      _ = lin R σ J g ((datR R σ J P T).f a +
            (lin R σ J z ((datR R σ J P T).f a) - (datR R σ J P T).f a)) := by
          rw [map_add, fix_span (unipotent_radical_fixes_frame hg) (Z_f hJ H hh hz a)]
      _ = lin R σ J g (lin R σ J z ((datR R σ J P T).f a)) := by
          congr 1; abel

theorem heisenberg_cocycle_mem_centre {y y' : Fin r → Fin M → R ⊗[F] E} (hy : ∀ a, IsWp (datR R σ J P T) (y a))
    (hy' : ∀ a, IsWp (datR R σ J P T) (y' a)) (hyy : ∀ a, IsWp (datR R σ J P T) ((y + y') a)) :
    sHG hJ H hh hy * sHG hJ H hh hy' * (sHG hJ H hh hyy)⁻¹ ∈ PI.LevelKSplit.W.NC.Zsub R σ J P := by
  refine ⟨(Nsub R σ J P).mul_mem ((Nsub R σ J P).mul_mem (sHG_mem hJ H hh hy).1
    (sHG_mem hJ H hh hy').1) ((Nsub R σ J P).inv_mem (sHG_mem hJ H hh hyy).1), fun v hv => ?_⟩
  obtain ⟨u, hu, rfl⟩ : ∃ u, Xp (datR R σ J P T) u ∧ lin R σ J (sHG hJ H hh hyy) u = v :=
    ⟨lin R σ J (sHG hJ H hh hyy)⁻¹ v,
      N_xp hJ H hh ((Nsub R σ J P).inv_mem (sHG_mem hJ H hh hyy).1) hv, lin_lin_inv R σ J _ _⟩
  rw [lin_mul, lin_inv_lin, lin_mul]
  simp only [lin_sHG]
  have hs : ∑ b, (datR R σ J P T).h (y' b) u • (datR R σ J P T).e b ∈
      Submodule.span (R ⊗[F] E) (Set.range (datR R σ J P T).e) :=
    Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, rfl⟩)
  rw [sL_Xp H hy' hu, map_sub, sL_Xp H hy hu, sL_span H hy hs, sL_Xp H hyy hu]
  simp only [Pi.add_apply, h_add_left, add_smul, Finset.sum_add_distrib]
  abel

theorem N_norm_Z {g : HA R σ J} (hg : g ∈ Nsub R σ J P) {z : HA R σ J}
    (hz : z ∈ PI.LevelKSplit.W.NC.Zsub R σ J P) : g * z * g⁻¹ ∈ PI.LevelKSplit.W.NC.Zsub R σ J P :=
  ⟨(Nsub R σ J P).mul_mem ((Nsub R σ J P).mul_mem hg hz.1) ((Nsub R σ J P).inv_mem hg),
    fun v hv => by
      rw [lin_mul, lin_mul, Z_fix hJ H hh hz (N_xp hJ H hh ((Nsub R σ J P).inv_mem hg) hv), lin_lin_inv]⟩

theorem H_e {h : HA R σ J} (hh' : h ∈ Hsub R σ J P) (a : Fin r) :
    lin R σ J h ((datR R σ J P T).e a) = (datR R σ J P T).e a :=
  PI.LevelKSplit.W.SemiA.H_fix_e hh' a

theorem H_f {h : HA R σ J} (hh' : h ∈ Hsub R σ J P) (a : Fin r) :
    lin R σ J h ((datR R σ J P T).f a) = (datR R σ J P T).f a :=
  PI.LevelKSplit.W.SemiA.H_fix_f hh' a

theorem H_he {h : HA R σ J} (hh' : h ∈ Hsub R σ J P) (a : Fin r) (v : Fin M → R ⊗[F] E) :
    (datR R σ J P T).h ((datR R σ J P T).e a) (lin R σ J h v) =
      (datR R σ J P T).h ((datR R σ J P T).e a) v := by
  rw [← uni_lin h ((datR R σ J P T).e a) v, H_e hJ H hh hh' a]

theorem H_hf {h : HA R σ J} (hh' : h ∈ Hsub R σ J P) (a : Fin r) (v : Fin M → R ⊗[F] E) :
    (datR R σ J P T).h ((datR R σ J P T).f a) (lin R σ J h v) =
      (datR R σ J P T).h ((datR R σ J P T).f a) v := by
  rw [← uni_lin h ((datR R σ J P T).f a) v, H_f hJ H hh hh' a]

theorem H_isWp {h : HA R σ J} (hh' : h ∈ Hsub R σ J P) {w : Fin M → R ⊗[F] E}
    (hw : IsWp (datR R σ J P T) w) : IsWp (datR R σ J P T) (lin R σ J h w) :=
  ⟨fun a => by rw [H_he hJ H hh hh', hw.1 a], fun a => by rw [H_hf hJ H hh hh', hw.2 a]⟩

theorem H_conj_sHG {g : HA R σ J} (hg : g ∈ Hsub R σ J P) {y : Fin r → Fin M → R ⊗[F] E}
    (hy : ∀ a, IsWp (datR R σ J P T) (y a))
    (hyh : ∀ a, IsWp (datR R σ J P T) ((fun b => lin R σ J g (y b)) a)) :
    g * sHG hJ H hh hy * g⁻¹ = sHG hJ H hh hyh := by
  apply PI.LevelKSplit.W.SemiA.ext_lin
  intro v
  rw [lin_mul, lin_mul, lin_sHG, lin_sHG, sL_apply, sL_apply]
  have hu : ∀ x x', (datR R σ J P T).h (lin R σ J g x) (lin R σ J g x') =
      (datR R σ J P T).h x x' := uni_lin g
  have e1 : ∀ a, (datR R σ J P T).h ((datR R σ J P T).e a) (lin R σ J g⁻¹ v) =
      (datR R σ J P T).h ((datR R σ J P T).e a) v := fun a => by
    rw [← hu, H_e hJ H hh hg a, lin_lin_inv]
  have e2 : ∀ b, (datR R σ J P T).h (y b) (lin R σ J g⁻¹ v) =
      (datR R σ J P T).h (lin R σ J g (y b)) v := fun b => by
    rw [← hu, lin_lin_inv]
  have luv : ∀ a, lin R σ J g (uv (datR R σ J P T) half y a) =
      uv (datR R σ J P T) half (fun b => lin R σ J g (y b)) a := fun a => by
    simp only [uv, cf, map_add, map_sum, map_smul, H_e hJ H hh hg, hu]
  simp only [map_add, map_sub, map_sum, map_smul, e1, e2, luv, H_e hJ H hh hg, lin_lin_inv]

theorem H_xp {h : HA R σ J} (hh' : h ∈ Hsub R σ J P) {v : Fin M → R ⊗[F] E}
    (hv : Xp (datR R σ J P T) v) : Xp (datR R σ J P T) (lin R σ J h v) :=
  fun a => by rw [H_he hJ H hh hh', hv a]

theorem H_comm_Z {g : HA R σ J} (hg : g ∈ Hsub R σ J P) {z : HA R σ J}
    (hz : z ∈ PI.LevelKSplit.W.NC.Zsub R σ J P) : g * z * g⁻¹ = z := by
  have hgi : g⁻¹ ∈ Hsub R σ J P := (Hsub R σ J P).inv_mem hg
  apply PI.LevelKSplit.W.SemiA.ext_lin
  intro v
  refine ext_Xp_f H (Φ := lin R σ J (g * z * g⁻¹)) (Ψ := lin R σ J z) (fun v hv => ?_)
    (fun a => ?_) v
  · rw [lin_mul, lin_mul, Z_fix hJ H hh hz (H_xp hJ H hh hgi hv), lin_lin_inv, Z_fix hJ H hh hz hv]
  · rw [lin_mul, lin_mul, H_f hJ H hh hgi a]
    have e : lin R σ J z ((datR R σ J P T).f a) = (datR R σ J P T).f a +
        (lin R σ J z ((datR R σ J P T).f a) - (datR R σ J P T).f a) := by abel
    rw [e, map_add, H_f hJ H hh hg a, fix_span (H_e hJ H hh hg) (Z_f hJ H hh hz a)]

end Sec

end R

end PI.LevelKSplit.W.NCH
