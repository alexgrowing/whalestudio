import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelSplitting.LevLSubPerp
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelSplitting.NCDefs
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelSplitting.ToMatrixLin

noncomputable section

namespace PI.LevelKSplit.W.NCL

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub PI.LevelKSplit.W.NC PI.VolSemiDirect.W
open scoped TensorProduct

section R

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
  (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) {r : ℕ} (P : Frame E M r) (T : F)

def uT (g : HA R σ J) : Matrix (Fin r) (Fin r) (R ⊗[F] E) :=
  Matrix.of fun a b => if a < b then
    hR R σ J (ratV (F := F) R (P.f a)) (lin R σ J g (ratV (F := F) R (P.e b)))
    else if a = b then 1 else 0

theorem uT_apply (g : HA R σ J) (a b : Fin r) : uT R σ J P g a b = if a < b then
    hR R σ J (ratV (F := F) R (P.f a)) (lin R σ J g (ratV (F := F) R (P.e b)))
    else if a = b then 1 else 0 := rfl

theorem det_uT (g : HA R σ J) : (uT R σ J P g).det = 1 := by
  rw [Matrix.det_of_upperTriangular]
  · exact Finset.prod_eq_one fun a _ => by simp [uT]
  · intro i j hji
    have h : j < i := hji
    simp only [uT, Matrix.of_apply]
    rw [if_neg (lt_asymm h), if_neg (ne_of_gt h)]

def uI (g : HA R σ J) : Matrix (Fin r) (Fin r) (R ⊗[F] E) := (uT R σ J P g).adjugate

theorem uT_mul_uI (g : HA R σ J) : uT R σ J P g * uI R σ J P g = 1 := by
  rw [uI, Matrix.mul_adjugate, det_uT, one_smul]

theorem uI_mul_uT (g : HA R σ J) : uI R σ J P g * uT R σ J P g = 1 := by
  rw [uI, Matrix.adjugate_mul, det_uT, one_smul]

def cj (U : Matrix (Fin r) (Fin r) (R ⊗[F] E)) : Matrix (Fin r) (Fin r) (R ⊗[F] E) :=
  Matrix.of fun a b => sigR R σ (U b a)

theorem cj_apply (U : Matrix (Fin r) (Fin r) (R ⊗[F] E)) (a b : Fin r) :
    cj R σ U a b = sigR R σ (U b a) := rfl

theorem cj_mul (U V : Matrix (Fin r) (Fin r) (R ⊗[F] E)) : cj R σ U * cj R σ V = cj R σ (V * U) := by
  ext a b
  simp only [cj, Matrix.mul_apply, Matrix.of_apply, map_sum, map_mul]
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _

theorem cj_one : cj R σ (1 : Matrix (Fin r) (Fin r) (R ⊗[F] E)) = 1 := by
  ext a b
  simp only [cj, Matrix.of_apply, Matrix.one_apply]
  by_cases h : a = b
  · subst h
    simp
  · simp [h, Ne.symm h]

variable {R σ J P T}

section Hyp

variable (hσσ : ∀ x, σ (σ x) = x) (hJ : IsHermND σ J) (hP : P.IsStd σ J T)
include hσσ hJ hP

theorem levTI (g : HA R σ J) (x : Fin M → R ⊗[F] E) :
    levL (datR R σ J P T) (uT R σ J P g) (cj R σ (uI R σ J P g))
      (levL (datR R σ J P T) (uI R σ J P g) (cj R σ (uT R σ J P g)) x) = x := by
  rw [levL_comp (datR_hyp hσσ hJ hP), uT_mul_uI, cj_mul, uT_mul_uI, cj_one,
    levL_one (datR_hyp hσσ hJ hP)]

theorem levIT (g : HA R σ J) (x : Fin M → R ⊗[F] E) :
    levL (datR R σ J P T) (uI R σ J P g) (cj R σ (uT R σ J P g))
      (levL (datR R σ J P T) (uT R σ J P g) (cj R σ (uI R σ J P g)) x) = x := by
  rw [levL_comp (datR_hyp hσσ hJ hP), uI_mul_uT, cj_mul, uI_mul_uT, cj_one,
    levL_one (datR_hyp hσσ hJ hP)]

end Hyp

def levU (hσσ : ∀ x, σ (σ x) = x) (hJ : IsHermND σ J) (hP : P.IsStd σ J T) (g : HA R σ J) :
    GL (Fin M) (R ⊗[F] E) where
  val := LinearMap.toMatrix' (levL (datR R σ J P T) (uT R σ J P g) (cj R σ (uI R σ J P g)))
  inv := LinearMap.toMatrix' (levL (datR R σ J P T) (uI R σ J P g) (cj R σ (uT R σ J P g)))
  val_inv := by
    rw [← LinearMap.toMatrix'_comp]
    have : (levL (datR R σ J P T) (uT R σ J P g) (cj R σ (uI R σ J P g))).comp
        (levL (datR R σ J P T) (uI R σ J P g) (cj R σ (uT R σ J P g))) = LinearMap.id :=
      LinearMap.ext fun x => levTI hσσ hJ hP g x
    rw [this, LinearMap.toMatrix'_id]
  inv_val := by
    rw [← LinearMap.toMatrix'_comp]
    have : (levL (datR R σ J P T) (uI R σ J P g) (cj R σ (uT R σ J P g))).comp
        (levL (datR R σ J P T) (uT R σ J P g) (cj R σ (uI R σ J P g))) = LinearMap.id :=
      LinearMap.ext fun x => levIT hσσ hJ hP g x
    rw [this, LinearMap.toMatrix'_id]

section Hyp2

variable (hσσ : ∀ x, σ (σ x) = x) (hJ : IsHermND σ J) (hP : P.IsStd σ J T)
include hσσ hJ hP

theorem levU_mem (g : HA R σ J) : levU hσσ hJ hP g ∈ HR R σ J := by
  have H : (datR R σ J P T).Hyp := datR_hyp hσσ hJ hP
  show Formalism.UG.cT (sigR R σ) (LinearMap.toMatrix' (levL (datR R σ J P T) (uT R σ J P g)
      (cj R σ (uI R σ J P g)))) * JR R J * LinearMap.toMatrix' (levL (datR R σ J P T)
      (uT R σ J P g) (cj R σ (uI R σ J P g))) = JR R J
  apply PI.LevelKSplit.W.SemiA.uj_of_uni
  intro x y
  rw [LinearMap.toMatrix'_mulVec, LinearMap.toMatrix'_mulVec]
  refine levL_uni H _ _ (fun b c => ?_) (fun b c => ?_) x y
  · calc ∑ a, sigR R σ (uT R σ J P g a b) * cj R σ (uI R σ J P g) a c
        = sigR R σ ((uI R σ J P g * uT R σ J P g) c b) := by
          rw [Matrix.mul_apply, map_sum]
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [cj_apply, map_mul, mul_comm]
      _ = if b = c then 1 else 0 := by
          rw [uI_mul_uT, Matrix.one_apply]
          by_cases h : b = c
          · subst h; simp
          · simp [h, Ne.symm h]
  · calc ∑ a, sigR R σ (cj R σ (uI R σ J P g) a b) * uT R σ J P g a c
        = (uI R σ J P g * uT R σ J P g) b c := by
          rw [Matrix.mul_apply]
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [cj_apply]
          exact congrArg (· * uT R σ J P g a c) (H.σσ _)
      _ = if b = c then 1 else 0 := by rw [uI_mul_uT, Matrix.one_apply]

end Hyp2

def levG (hσσ : ∀ x, σ (σ x) = x) (hJ : IsHermND σ J) (hP : P.IsStd σ J T) (g : HA R σ J) :
    HA R σ J :=
  ⟨levU hσσ hJ hP g, levU_mem hσσ hJ hP g⟩

variable (R σ J P)

def Asub : Subgroup (HA R σ J) where
  carrier := {g | g ∈ Nsub R σ J P ∧ (∀ w ∈ Wp R σ J P, lin R σ J g w = w) ∧
    (∀ b, lin R σ J g (ratV (F := F) R (P.f b)) ∈ spanR (F := F) R P.f Set.univ) ∧
    (∀ b, lin R σ J g⁻¹ (ratV (F := F) R (P.f b)) ∈ spanR (F := F) R P.f Set.univ)}
  one_mem' := by
    refine ⟨(Nsub R σ J P).one_mem, fun w _ => lin_one R σ J w, fun b => ?_, fun b => ?_⟩
    · rw [lin_one]; exact Submodule.subset_span ⟨b, Set.mem_univ _, rfl⟩
    · rw [inv_one, lin_one]; exact Submodule.subset_span ⟨b, Set.mem_univ _, rfl⟩
  mul_mem' := by
    intro g h hg hh
    obtain ⟨hg1, hg2, hg3, hg4⟩ := hg
    obtain ⟨hh1, hh2, hh3, hh4⟩ := hh
    have key : ∀ (k : HA R σ J), (∀ b, lin R σ J k (ratV (F := F) R (P.f b)) ∈
        spanR (F := F) R P.f Set.univ) → ∀ y ∈ spanR (F := F) R P.f Set.univ,
        lin R σ J k y ∈ spanR (F := F) R P.f Set.univ := by
      intro k hk y hy
      have hle : spanR (F := F) R P.f Set.univ ≤ (spanR (F := F) R P.f Set.univ).comap (lin R σ J k) := by
        rw [spanR, Submodule.span_le]
        rintro _ ⟨b, _, rfl⟩
        exact hk b
      exact hle hy
    refine ⟨(Nsub R σ J P).mul_mem hg1 hh1, fun w hw => ?_, fun b => ?_, fun b => ?_⟩
    · rw [lin_mul, hh2 w hw, hg2 w hw]
    · rw [lin_mul]; exact key g hg3 _ (hh3 b)
    · rw [mul_inv_rev, lin_mul]; exact key h⁻¹ hh4 _ (hg4 b)
  inv_mem' := by
    intro g hg
    obtain ⟨hg1, hg2, hg3, hg4⟩ := hg
    refine ⟨(Nsub R σ J P).inv_mem hg1, fun w hw => ?_, hg4, fun b => ?_⟩
    · conv_lhs => rw [← hg2 w hw]
      exact lin_inv_lin R σ J g w
    · rw [inv_inv]; exact hg3 b

variable {R σ J P}

theorem spanE_f_zero (H : (datR R σ J P T).Hyp) {s : Set (Fin r)} {x : Fin M → R ⊗[F] E}
    (hx : x ∈ spanR (F := F) R P.e s) {a : Fin r} (ha : a ∉ s) :
    (datR R σ J P T).h ((datR R σ J P T).f a) x = 0 := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨c, hc, rfl⟩ := hy
    show (datR R σ J P T).h ((datR R σ J P T).f a) ((datR R σ J P T).e c) = 0
    rw [PG.Dat.fe H, if_neg]
    rintro rfl
    exact ha hc
  | zero => exact PG.Dat.h_zero_right _ _
  | add x y _ _ hx hy => rw [PG.Dat.h_add_right, hx, hy, add_zero]
  | smul c x _ hx => rw [PG.Dat.h_smul_right, hx, mul_zero]

theorem pXv_mem_span (x : Fin M → R ⊗[F] E) :
    (datR R σ J P T).pXv x ∈ Submodule.span (R ⊗[F] E) (Set.range (datR R σ J P T).f) := by
  rw [PG.Dat.pXv_apply]
  exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)

theorem pXv_of_span (H : (datR R σ J P T).Hyp) {x : Fin M → R ⊗[F] E}
    (hx : x ∈ Submodule.span (R ⊗[F] E) (Set.range (datR R σ J P T).f)) :
    (datR R σ J P T).pXv x = x := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨b, rfl⟩ := hy
    rw [PG.Dat.pXv_apply]
    simp [H.ef]
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, hx, hy]
  | smul c x _ hx => rw [map_smul, hx]

theorem pX_mem (x : Fin M → R ⊗[F] E) :
    (datR R σ J P T).pX x ∈ Submodule.span (R ⊗[F] E) (Set.range fun a => ratV (F := F) R (P.e a)) :=
  PG.Dat.pX_mem_span (D := datR R σ J P T) x

theorem pXv_mem (x : Fin M → R ⊗[F] E) :
    (datR R σ J P T).pXv x ∈ Submodule.span (R ⊗[F] E) (Set.range fun a => ratV (F := F) R (P.f a)) :=
  pXv_mem_span (T := T) x

theorem pV_mem_Wp (H : (datR R σ J P T).Hyp) (x : Fin M → R ⊗[F] E) :
    pV (datR R σ J P T) x ∈ Wp R σ J P :=
  ⟨fun a => h_e_pV H a x, fun a => h_f_pV H a x⟩

section Hyp3

variable (hσσ : ∀ x, σ (σ x) = x) (hJ : IsHermND σ J) (hP : P.IsStd σ J T)
include hσσ hJ hP

theorem lin_levG (g : HA R σ J) :
    lin R σ J (levG hσσ hJ hP g) = levL (datR R σ J P T) (uT R σ J P g) (cj R σ (uI R σ J P g)) := by
  first
  | rfl
  | (unfold lin; simp [levG, levU, HA.mat]; exact Matrix.toLin'_toMatrix' _)
  | (unfold lin; simp [levG, levU, HA.mat]; exact LinearMap.ext fun x => LinearMap.toMatrix'_mulVec _ x)

theorem lin_levG_inv (g : HA R σ J) (x : Fin M → R ⊗[F] E) :
    lin R σ J (levG hσσ hJ hP g)⁻¹ x =
      levL (datR R σ J P T) (uI R σ J P g) (cj R σ (uT R σ J P g)) x := by
  unfold lin
  simp [levG, levU, HA.mat]
  first
  | exact LinearMap.toMatrix'_mulVec _ x
  | (show (LinearMap.toMatrix' (levL (datR R σ J P T) (uI R σ J P g) (cj R σ (uT R σ J P g)))).mulVec x = _
     exact LinearMap.toMatrix'_mulVec _ x)

theorem levG_mem (g : HA R σ J) : levG hσσ hJ hP g ∈ Asub R σ J P := by
  have H : (datR R σ J P T).Hyp := datR_hyp hσσ hJ hP
  have hfs : ∀ (U W : Matrix (Fin r) (Fin r) (R ⊗[F] E)) (b : Fin r),
      levL (datR R σ J P T) U W (ratV (F := F) R (P.f b)) ∈ spanR (F := F) R P.f Set.univ :=
    fun U W b => by
      show levL (datR R σ J P T) U W ((datR R σ J P T).f b) ∈ _
      rw [levL_f H]
      exact Submodule.sum_mem _ fun d _ => Submodule.smul_mem _ _
        (Submodule.subset_span ⟨d, Set.mem_univ _, rfl⟩)
  refine ⟨⟨fun b => ?_, fun v hv => ?_⟩, fun w hw => ?_, fun b => ?_, fun b => ?_⟩
  · rw [lin_levG]
    show levL (datR R σ J P T) _ _ ((datR R σ J P T).e b) - (datR R σ J P T).e b ∈ _
    rw [levL_e H]
    have e1 : ∑ a, uT R σ J P g a b • (datR R σ J P T).e a - (datR R σ J P T).e b =
        ∑ a, (if a < b then uT R σ J P g a b else 0) • (datR R σ J P T).e a := by
      have eb : (datR R σ J P T).e b =
          ∑ a, (if a = b then (1 : R ⊗[F] E) else 0) • (datR R σ J P T).e a := by simp
      rw [eb, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [← sub_smul]
      congr 1
      rw [uT_apply]
      rcases lt_trichotomy a b with h | h | h
      · simp [h, h.ne]
      · subst h; simp
      · simp [not_lt.2 h.le, h.ne']
    rw [e1]
    refine Submodule.sum_mem _ fun a _ => ?_
    split_ifs with h
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, h, rfl⟩)
    · rw [zero_smul]; exact Submodule.zero_mem _
  · rw [lin_levG, PI.LevelKSplit.W.Glob.spanR_univ]
    exact levL_sub_perp H _ _ hv
  · rw [lin_levG]
    exact levL_alt H _ _ hw.2 hw.1
  · rw [lin_levG]; exact hfs _ _ b
  · rw [lin_levG_inv]; exact hfs _ _ b

theorem levG_e (n : HA R σ J) (hn : n ∈ Nsub R σ J P) (b : Fin r) :
    lin R σ J (levG hσσ hJ hP n) (ratV (F := F) R (P.e b)) = lin R σ J n (ratV (F := F) R (P.e b)) := by
  have H : (datR R σ J P T).Hyp := datR_hyp hσσ hJ hP
  have hn1 : UniC R σ J P.e n := hn.1
  have hmem : lin R σ J n (ratV (F := F) R (P.e b)) ∈
      Submodule.span (R ⊗[F] E) (Set.range (datR R σ J P T).e) := by
    have := uni_map_le hn1 Set.univ (fun _ _ _ _ => Set.mem_univ _)
      (Submodule.mem_map_of_mem (Submodule.subset_span ⟨b, Set.mem_univ _, rfl⟩))
    rw [PI.LevelKSplit.W.Glob.spanR_univ] at this
    exact this
  have e1 : lin R σ J n (ratV (F := F) R (P.e b)) = ∑ a, (datR R σ J P T).h ((datR R σ J P T).f a)
      (lin R σ J n (ratV (F := F) R (P.e b))) • (datR R σ J P T).e a := by
    conv_lhs => rw [← PG.Dat.pX_of_span H hmem]
    exact PG.Dat.pX_apply _ _
  rw [lin_levG]
  show levL (datR R σ J P T) _ _ ((datR R σ J P T).e b) = _
  rw [levL_e H, e1]
  refine Finset.sum_congr rfl fun a _ => ?_
  congr 1
  rw [uT_apply]
  by_cases h1 : a < b
  · rw [if_pos h1]; rfl
  · rw [if_neg h1]
    have h0 := spanE_f_zero (T := T) H (hn1 b) (a := a) (fun h => h1 h)
    have hfe : (datR R σ J P T).h ((datR R σ J P T).f a) (ratV (F := F) R (P.e b)) =
        if a = b then 1 else 0 := PG.Dat.fe H a b
    rw [PG.Dat.h_sub_right, hfe, sub_eq_zero] at h0
    exact h0.symm

theorem levG_inv_mul (n : HA R σ J) (hn : n ∈ Nsub R σ J P) :
    (levG hσσ hJ hP n)⁻¹ * n ∈ LevelUnipotentSubgroup R σ J P := by
  refine Subgroup.mem_inf.2 ⟨(Nsub R σ J P).mul_mem ((Nsub R σ J P).inv_mem
    (levG_mem hσσ hJ hP n).1) hn, (mem_stabT R σ J P.e _).2 fun b => ?_⟩
  rw [lin_mul, ← levG_e hσσ hJ hP n hn b, lin_inv_lin]

theorem levi_inf_unipotent_eq_one (u : HA R σ J) (hu : u ∈ Asub R σ J P) (hu1 : u ∈ LevelUnipotentSubgroup R σ J P) : u = 1 := by
  have H : (datR R σ J P T).Hyp := datR_hyp hσσ hJ hP
  obtain ⟨_, hW, hF, _⟩ := hu
  have hS := (mem_stabT R σ J P.e u).1 (Subgroup.mem_inf.1 hu1).2
  have hf : ∀ b, lin R σ J u (ratV (F := F) R (P.f b)) = ratV (F := F) R (P.f b) := by
    intro b
    have hm : lin R σ J u (ratV (F := F) R (P.f b)) ∈
        Submodule.span (R ⊗[F] E) (Set.range (datR R σ J P T).f) := by
      have := hF b
      rw [PI.LevelKSplit.W.Glob.spanR_univ] at this
      exact this
    rw [← pXv_of_span H hm, PG.Dat.pXv_apply]
    have hc : ∀ d, (datR R σ J P T).h ((datR R σ J P T).e d) (lin R σ J u (ratV (F := F) R (P.f b))) =
        if d = b then 1 else 0 := fun d => by
      show hR R σ J (ratV (F := F) R (P.e d)) (lin R σ J u (ratV (F := F) R (P.f b))) = _
      rw [← hS d, hR_lin]
      exact H.ef d b
    simp only [hc, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rfl
  apply PI.LevelKSplit.W.SemiA.ext_lin
  intro x
  rw [lin_one]
  conv_lhs => rw [decomp (datR R σ J P T) x]
  rw [map_add, map_add, hW _ (pV_mem_Wp H x),
    PI.LevelKSplit.W.Glob.lin_fix_span u P.e hS _ (pX_mem x),
    PI.LevelKSplit.W.Glob.lin_fix_span u P.f hf _ (pXv_mem x)]
  exact (decomp (datR R σ J P T) x).symm

end Hyp3

theorem unipotent_radical_normal (n m : HA R σ J) (hn : n ∈ Nsub R σ J P) (hm : m ∈ LevelUnipotentSubgroup R σ J P) :
    n * m * n⁻¹ ∈ LevelUnipotentSubgroup R σ J P := by
  have hm' := Subgroup.mem_inf.1 hm
  refine Subgroup.mem_inf.2 ⟨(Nsub R σ J P).mul_mem ((Nsub R σ J P).mul_mem hn hm'.1)
    ((Nsub R σ J P).inv_mem hn), (mem_stabT R σ J P.e _).2 fun b => ?_⟩
  have hmS := (mem_stabT R σ J P.e m).1 hm'.2
  have h1 : lin R σ J n⁻¹ (ratV (F := F) R (P.e b)) ∈
      Submodule.span (R ⊗[F] E) (Set.range fun a => ratV (F := F) R (P.e a)) := by
    have := uni_map_le ((Nsub R σ J P).inv_mem hn).1 Set.univ (fun _ _ _ _ => Set.mem_univ _)
      (Submodule.mem_map_of_mem (Submodule.subset_span ⟨b, Set.mem_univ _, rfl⟩))
    rw [PI.LevelKSplit.W.Glob.spanR_univ] at this
    exact this
  rw [lin_mul, lin_mul, PI.LevelKSplit.W.Glob.lin_fix_span m P.e hmS _ h1, lin_lin_inv]

theorem H_comm_A (H : (datR R σ J P T).Hyp) (h u : HA R σ J) (hh : h ∈ Hsub R σ J P)
    (hu : u ∈ Asub R σ J P) : h * u = u * h := by
  obtain ⟨hu1, hW, hF, _⟩ := hu
  have hu1' : UniC R σ J P.e u := hu1.1
  have hhe := PI.LevelKSplit.W.Glob.lin_fix_span h P.e (PI.LevelKSplit.W.Glob.H_fix_e P h hh)
  have hhf := PI.LevelKSplit.W.Glob.lin_fix_span h P.f (PI.LevelKSplit.W.Glob.H_fix_f P h hh)
  apply PI.LevelKSplit.W.SemiA.ext_lin
  intro x
  have hWx : lin R σ J h (pV (datR R σ J P T) x) ∈ Wp R σ J P := by
    refine ⟨fun a => ?_, fun a => ?_⟩
    · rw [← PI.LevelKSplit.W.Glob.H_fix_e P h hh a, hR_lin]; exact h_e_pV H a x
    · rw [← PI.LevelKSplit.W.Glob.H_fix_f P h hh a, hR_lin]; exact h_f_pV H a x
  have uE : lin R σ J u ((datR R σ J P T).pX x) ∈
      Submodule.span (R ⊗[F] E) (Set.range fun a => ratV (F := F) R (P.e a)) := by
    have hx : (datR R σ J P T).pX x ∈ spanR (F := F) R P.e Set.univ := by
      rw [PI.LevelKSplit.W.Glob.spanR_univ]; exact pX_mem x
    have := uni_map_le hu1' Set.univ (fun _ _ _ _ => Set.mem_univ _) (Submodule.mem_map_of_mem hx)
    rw [PI.LevelKSplit.W.Glob.spanR_univ] at this
    exact this
  have uF : lin R σ J u ((datR R σ J P T).pXv x) ∈
      Submodule.span (R ⊗[F] E) (Set.range fun a => ratV (F := F) R (P.f a)) := by
    have hle : spanR (F := F) R P.f Set.univ ≤ (spanR (F := F) R P.f Set.univ).comap (lin R σ J u) := by
      rw [spanR, Submodule.span_le]
      rintro _ ⟨b, _, rfl⟩
      exact hF b
    have hx : (datR R σ J P T).pXv x ∈ spanR (F := F) R P.f Set.univ := by
      rw [PI.LevelKSplit.W.Glob.spanR_univ]; exact pXv_mem x
    have := hle hx
    rw [PI.LevelKSplit.W.Glob.spanR_univ] at this
    exact this
  rw [lin_mul, lin_mul]
  conv_lhs => rw [decomp (datR R σ J P T) x]
  conv_rhs => rw [decomp (datR R σ J P T) x]
  simp only [map_add]
  rw [hW _ (pV_mem_Wp H x), hW _ hWx, hhe _ (pX_mem x), hhf _ (pXv_mem x),
    hhe _ uE, hhf _ uF]

end R

end PI.LevelKSplit.W.NCL
