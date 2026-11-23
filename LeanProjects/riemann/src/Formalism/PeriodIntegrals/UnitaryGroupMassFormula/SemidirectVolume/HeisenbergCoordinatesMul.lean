import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.ModDefs
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.ReflectionFixesNormal
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.ModUni
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.ModComp

noncomputable section

namespace PI.VolSemiDirect.W.PG.Dat

variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] {r : ℕ} {D : Dat A n r}

theorem S_L (H : D.Hyp) {S : (n → A) →ₗ[A] (n → A)} (hS : D.FixEZ S) (hf : ∀ a, S (D.f a) = D.f a)
    (hU : D.Uni S) (w : Fin r → n → A) (s : Fin r → Fin r → A) (u : n → A) :
    S (D.L w s u) = D.L (fun a => S (w a)) s (S u) := by
  rw [L_apply, L_apply, pW_comm H hS hf hU]
  have hw : ∀ a, D.h (S (w a)) (S (D.pW u)) = D.h (w a) (D.pW u) := fun a => hU _ _
  simp only [map_sub, map_add, map_sum, map_smul, hS.1, h_e_S hS hU, hw]

theorem h_neg_left' (x y : n → A) : D.h (-x) y = -D.h x y := by
  have := D.h_add_left (-x) x y
  rw [neg_add_cancel, h_zero_left] at this
  linear_combination -this

theorem h_neg_right' (x y : n → A) : D.h x (-y) = -D.h x y := by
  have := D.h_add_right x (-y) y
  rw [neg_add_cancel, h_zero_right] at this
  linear_combination -this

end PI.VolSemiDirect.W.PG.Dat

namespace PI.VolSemiDirect.W.Md

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField
open scoped TensorProduct

def half (F E R : Type) [Field F] [Field E] [Algebra F E] [CommRing R] [Algebra F R] : R ⊗[F] E :=
  inclR (F := F) R (1 / 2 : E)

section R

variable {F E : Type} [Field F] [Field E] [Algebra F E] {R : Type} [CommRing R] [Algebra F R]
  {σ : E →ₐ[F] E} {M : ℕ} {J : Matrix (Fin M) (Fin M) E} {r : ℕ} {P : Frame E M r} {T : F}

theorem half_add_half (h2 : (2 : E) ≠ 0) : half F E R + half F E R = 1 := by
  have : (1 / 2 : E) + 1 / 2 = 1 := by rw [← two_mul, mul_one_div_cancel h2]
  rw [half, ← map_add, this, map_one]

theorem sigR_half : sigR R σ (half F E R) = half F E R := by
  rw [half, sigR_inclR, map_div₀, map_one, map_ofNat]

variable (σ J) in

def Lr (P : Frame E M r) (T : F) (w : Fin r → Fin M → R ⊗[F] E) (c : Fin r → Fin r → R ⊗[F] E) :
    (Fin M → R ⊗[F] E) →ₗ[R ⊗[F] E] (Fin M → R ⊗[F] E) :=
  (datR R σ J P T).L w (fun a b => c a b - half F E R * hR R σ J (w a) (w b))

variable (R σ J) in

def dat0 : PG.Dat (R ⊗[F] E) (Fin M) 0 where
  σA := sigR R σ
  JA := JR R J
  e := fun _ => 0
  f := fun _ => 0
  z := 0
  tz := 0

theorem hR_add_left' (x x' y : Fin M → R ⊗[F] E) :
    hR R σ J (x + x') y = hR R σ J x y + hR R σ J x' y :=
  PG.Dat.h_add_left (D := dat0 R σ J) x x' y

theorem hR_add_right' (x y y' : Fin M → R ⊗[F] E) :
    hR R σ J x (y + y') = hR R σ J x y + hR R σ J x y' :=
  PG.Dat.h_add_right (dat0 R σ J) x y y'

theorem hR_neg_left' (x y : Fin M → R ⊗[F] E) : hR R σ J (-x) y = -hR R σ J x y :=
  PG.Dat.h_neg_left' (D := dat0 R σ J) x y

theorem hR_neg_right' (x y : Fin M → R ⊗[F] E) : hR R σ J x (-y) = -hR R σ J x y :=
  PG.Dat.h_neg_right' (D := dat0 R σ J) x y

theorem Lr_zero : Lr σ J P T (0 : Fin r → Fin M → R ⊗[F] E) 0 = LinearMap.id := by
  have e : (fun a b => (0 : Fin r → Fin r → R ⊗[F] E) a b -
      half F E R * hR R σ J ((0 : Fin r → Fin M → R ⊗[F] E) a) ((0 : Fin r → Fin M → R ⊗[F] E) b)) =
      (0 : Fin r → Fin r → R ⊗[F] E) := by
    funext a b
    simp [hR_zero_left]
  rw [Lr, e]
  exact PG.Dat.L_zero

variable (hσσ : ∀ x, σ (σ x) = x) (hJ : IsHermND σ J) (hP : P.IsStd σ J T) (h2 : (2 : E) ≠ 0)
include hσσ hJ hP h2

theorem Lr_comp {w w' : Fin r → Fin M → R ⊗[F] E} (hw : ∀ a, w a ∈ Wsub R σ J P)
    (hw' : ∀ a, w' a ∈ Wsub R σ J P) (c c' : Fin r → Fin r → R ⊗[F] E) (v : Fin M → R ⊗[F] E) :
    Lr σ J P T w c (Lr σ J P T w' c' v) = Lr σ J P T (w + w') (c + c' + betaM R σ J w w') v := by
  have H := datR_hyp (R := R) hσσ hJ hP
  rw [Lr, Lr, PG.Dat.L_comp H _ _ (fun a => hw a) (fun a => hw' a), Lr]
  congr 2
  funext a b
  simp only [datR_h, Pi.add_apply, betaM]
  rw [hR_add_left', hR_add_right', hR_add_right']
  have hh := half_add_half (F := F) (R := R) h2
  rw [show inclR (F := F) R (1 / 2 : E) = half F E R from rfl]
  linear_combination (hR R σ J (w a) (w' b)) * hh

theorem Lr_inv {w : Fin r → Fin M → R ⊗[F] E} (hw : ∀ a, w a ∈ Wsub R σ J P)
    (c : Fin r → Fin r → R ⊗[F] E) :
    Lr σ J P T w c ∘ₗ Lr σ J P T (-w) (-c) = LinearMap.id ∧
      Lr σ J P T (-w) (-c) ∘ₗ Lr σ J P T w c = LinearMap.id := by
  have hwn : ∀ a, (-w) a ∈ Wsub R σ J P := fun a => (Wsub R σ J P).neg_mem (hw a)
  have b1 : c + -c + betaM R σ J w (-w) = 0 := by
    funext a b
    simp only [betaM, Pi.add_apply, Pi.neg_apply, Pi.zero_apply, hR_neg_left' ,
      hR_neg_right' ]
    ring
  have b2 : -c + c + betaM R σ J (-w) w = 0 := by
    funext a b
    simp only [betaM, Pi.add_apply, Pi.neg_apply, Pi.zero_apply, hR_neg_left' ,
      hR_neg_right' ]
    ring
  constructor
  · refine LinearMap.ext fun v => ?_
    rw [LinearMap.comp_apply, Lr_comp hσσ hJ hP h2 hw hwn, b1, add_neg_cancel, Lr_zero]
  · refine LinearMap.ext fun v => ?_
    rw [LinearMap.comp_apply, Lr_comp hσσ hJ hP h2 hwn hw, b2, neg_add_cancel, Lr_zero]

theorem Lr_uni {w : Fin r → Fin M → R ⊗[F] E} (hw : ∀ a, w a ∈ Wsub R σ J P)
    {c : Fin r → Fin r → R ⊗[F] E} (hc : ∀ a b, c a b + sigR R σ (c b a) = 0) :
    (datR R σ J P T).Uni (Lr σ J P T w c) := by
  have H := datR_hyp (R := R) hσσ hJ hP
  refine PG.Dat.L_uni H (fun a => hw a) fun a b => ?_
  have hsym : hR R σ J (w a) (w b) = sigR R σ (hR R σ J (w b) (w a)) :=
    PG.Dat.h_symm H (w b) (w a)
  have hh := half_add_half (F := F) (R := R) h2
  show c a b - half F E R * hR R σ J (w a) (w b) +
      sigR R σ (c b a - half F E R * hR R σ J (w b) (w a)) + hR R σ J (w a) (w b) = 0
  rw [map_sub, map_mul, sigR_half, ← hsym]
  linear_combination hc a b - hR R σ J (w a) (w b) * hh

def wv (w : Fin r → Wsub R σ J P) : Fin r → Fin M → R ⊗[F] E := fun a => (w a : Fin M → R ⊗[F] E)

def nU (w : Fin r → Wsub R σ J P) (c : Sk R σ r) : GL (Fin M) (R ⊗[F] E) where
  val := LinearMap.toMatrix' (Lr σ J P T (wv w) c)
  inv := LinearMap.toMatrix' (Lr σ J P T (-wv w) (-(c : Fin r → Fin r → R ⊗[F] E)))
  val_inv := by
    rw [← LinearMap.toMatrix'_comp, (Lr_inv hσσ hJ hP h2 (w := wv w) (fun a => (w a).2) _).1,
      LinearMap.toMatrix'_id]
  inv_val := by
    rw [← LinearMap.toMatrix'_comp, (Lr_inv hσσ hJ hP h2 (w := wv w) (fun a => (w a).2) _).2,
      LinearMap.toMatrix'_id]

theorem nU_mem (w : Fin r → Wsub R σ J P) (c : Sk R σ r) : nU hσσ hJ hP h2 w c ∈ HR R σ J := by
  show Formalism.UG.cT (sigR R σ) (LinearMap.toMatrix' (Lr σ J P T (wv w) c)) * JR R J *
    LinearMap.toMatrix' (Lr σ J P T (wv w) c) = JR R J
  apply uj_of_uni
  intro x y
  rw [LinearMap.toMatrix'_mulVec, LinearMap.toMatrix'_mulVec]
  exact Lr_uni hσσ hJ hP h2 (fun a => (w a).2) (fun a b => c.2 a b) x y

def nG (w : Fin r → Wsub R σ J P) (c : Sk R σ r) : HA R σ J :=
  ⟨nU hσσ hJ hP h2 w c, nU_mem hσσ hJ hP h2 w c⟩

theorem lin_nG (w : Fin r → Wsub R σ J P) (c : Sk R σ r) :
    lin R σ J (nG hσσ hJ hP h2 w c) = Lr σ J P T (wv w) c :=
  LinearMap.ext fun v => LinearMap.toMatrix'_mulVec _ v

theorem nG_mem (w : Fin r → Wsub R σ J P) (c : Sk R σ r) :
    nG hσσ hJ hP h2 w c ∈ FrameUnipotentSubgroup R σ J P := by
  have H := datR_hyp (R := R) hσσ hJ hP
  have he : ∀ b, lin R σ J (nG hσσ hJ hP h2 w c) (ratV (F := F) R (P.e b)) =
      ratV (F := F) R (P.e b) := fun b => by
    rw [lin_nG]; exact PG.Dat.L_e H _ _ b
  have hz : lin R σ J (nG hσσ hJ hP h2 w c) (ratV (F := F) R P.z) = ratV (F := F) R P.z := by
    rw [lin_nG]; exact PG.Dat.reflection_fixes_normal H _ _
  rw [FrameUnipotentSubgroup, Subgroup.mem_inf]
  refine ⟨?_, ?_⟩
  · show UniC R σ J P.e _ ∧ ∀ v, InXperp R σ J P v → _
    refine ⟨fun b => ?_, fun v hv => ?_⟩
    · rw [he b, sub_self]
      exact Submodule.zero_mem _
    · rw [spanR_eq hσσ hJ hP, lin_nG]
      exact PG.Dat.L_perp H _ _ v hv
  · rw [S0, mem_stabT]
    intro b
    refine Fin.lastCases ?_ (fun a => ?_) b
    · simp only [F0, Fin.snoc_last]; exact hz
    · simp only [F0, Fin.snoc_castSucc]; exact he a

omit h2 in
theorem phiW_mem (n : FrameUnipotentSubgroup R σ J P) (b : Fin r) :
    (datR R σ J P T).pW (lin R σ J n ((datR R σ J P T).f b)) ∈ Wsub R σ J P :=
  PG.Dat.isW_pW (datR_hyp hσσ hJ hP) _

omit h2 in

def phiW (n : FrameUnipotentSubgroup R σ J P) : Fin r → Wsub R σ J P := fun b =>
  ⟨(datR R σ J P T).pW (lin R σ J n ((datR R σ J P T).f b)), phiW_mem hσσ hJ hP n b⟩

omit h2 in

def phiSv (n : FrameUnipotentSubgroup R σ J P) : Fin r → Fin r → R ⊗[F] E := fun a b =>
  hR R σ J ((datR R σ J P T).f a) (lin R σ J n ((datR R σ J P T).f b)) +
    half F E R * hR R σ J (wv (phiW hσσ hJ hP n) a) (wv (phiW hσσ hJ hP n) b)

theorem phiSv_mem (n : FrameUnipotentSubgroup R σ J P) : phiSv hσσ hJ hP n ∈ Sk R σ r := by
  have H := datR_hyp (R := R) hσσ hJ hP
  have hS0 : (n : HA R σ J) ∈ S0 R σ J P := (Subgroup.mem_inf.1 n.2).2
  have hN := PG.Dat.N_skew H (stabilizer_fixes_frame_and_normal (T := T) hS0) (uni_lin (T := T) (n : HA R σ J))
  have hh := half_add_half (F := F) (R := R) h2
  intro a b
  have hsym : hR R σ J (wv (phiW hσσ hJ hP n) a) (wv (phiW hσσ hJ hP n) b) =
      sigR R σ (hR R σ J (wv (phiW hσσ hJ hP n) b) (wv (phiW hσσ hJ hP n) a)) :=
    PG.Dat.h_symm H _ _
  show phiSv hσσ hJ hP n a b + sigR R σ (phiSv hσσ hJ hP n b a) = 0
  simp only [phiSv]
  rw [map_add, map_mul, sigR_half, ← hsym]
  have k := hN a b
  simp only [datR_h] at k
  change hR R σ J ((datR R σ J P T).f a) (lin R σ J n ((datR R σ J P T).f b)) +
    sigR R σ (hR R σ J ((datR R σ J P T).f b) (lin R σ J n ((datR R σ J P T).f a))) +
    hR R σ J (wv (phiW hσσ hJ hP n) a) (wv (phiW hσσ hJ hP n) b) = 0 at k
  linear_combination k + hR R σ J (wv (phiW hσσ hJ hP n) a) (wv (phiW hσσ hJ hP n) b) * hh

def phiS (n : FrameUnipotentSubgroup R σ J P) : Sk R σ r := ⟨phiSv hσσ hJ hP n, phiSv_mem hσσ hJ hP h2 n⟩

omit h2 in

theorem phi_of_lin (n : FrameUnipotentSubgroup R σ J P) {w : Fin r → Fin M → R ⊗[F] E} (hw : ∀ a, w a ∈ Wsub R σ J P)
    (c : Fin r → Fin r → R ⊗[F] E) (hn : lin R σ J n = Lr σ J P T w c) :
    wv (phiW hσσ hJ hP n) = w ∧ phiSv hσσ hJ hP n = c := by
  have H := datR_hyp (R := R) hσσ hJ hP
  have h1 : wv (phiW hσσ hJ hP n) = w := by
    funext b
    show (datR R σ J P T).pW (lin R σ J n ((datR R σ J P T).f b)) = w b
    rw [hn, Lr]
    exact PG.Dat.coordW_L H (fun a => hw a) _ b
  refine ⟨h1, ?_⟩
  funext a b
  simp only [phiSv]
  rw [h1, hn, Lr]
  have := PG.Dat.coordS_L H (fun a => hw a)
    (fun a b => c a b - half F E R * hR R σ J (w a) (w b)) a b
  rw [datR_h] at this
  rw [this]
  ring

omit h2 in
theorem lin_eq_Lr (n : FrameUnipotentSubgroup R σ J P) :
    lin R σ J n = Lr σ J P T (wv (phiW hσσ hJ hP n)) (phiSv hσσ hJ hP n) := by
  have H := datR_hyp (R := R) hσσ hJ hP
  have hS0 : (n : HA R σ J) ∈ S0 R σ J P := (Subgroup.mem_inf.1 n.2).2
  have hNs := (Subgroup.mem_inf.1 n.2).1
  have hperp : (datR R σ J P T).PerpX (lin R σ J n) := fun v hv => by
    have := hNs.2 v hv
    rwa [spanR_eq hσσ hJ hP] at this
  have hs : (fun a b => phiSv hσσ hJ hP n a b - half F E R *
      hR R σ J (wv (phiW hσσ hJ hP n) a) (wv (phiW hσσ hJ hP n) b)) =
      fun a b => (datR R σ J P T).h ((datR R σ J P T).f a) (lin R σ J n ((datR R σ J P T).f b)) := by
    funext a b
    simp only [phiSv]
    rw [add_sub_cancel_right]
    rfl
  refine LinearMap.ext fun v => ?_
  rw [Lr, hs]
  exact PG.Dat.N_eq_L H (stabilizer_fixes_frame_and_normal hS0) (uni_lin _) hperp v

theorem nG_phi (n : FrameUnipotentSubgroup R σ J P) :
    nG hσσ hJ hP h2 (phiW hσσ hJ hP n) (phiS hσσ hJ hP h2 n) = n := by
  have e : lin R σ J (nG hσσ hJ hP h2 (phiW hσσ hJ hP n) (phiS hσσ hJ hP h2 n)) = lin R σ J n :=
    (lin_nG hσσ hJ hP h2 _ _).trans (lin_eq_Lr hσσ hJ hP n).symm
  apply HA_ext
  rw [← lin_eq_toLin', ← lin_eq_toLin', e]

theorem phi_nG (w : Fin r → Wsub R σ J P) (c : Sk R σ r) :
    phiW hσσ hJ hP ⟨nG hσσ hJ hP h2 w c, nG_mem hσσ hJ hP h2 w c⟩ = w ∧
      phiS hσσ hJ hP h2 ⟨nG hσσ hJ hP h2 w c, nG_mem hσσ hJ hP h2 w c⟩ = c := by
  obtain ⟨h1, h2'⟩ := phi_of_lin hσσ hJ hP ⟨nG hσσ hJ hP h2 w c, nG_mem hσσ hJ hP h2 w c⟩
    (fun a => (w a).2) c (lin_nG hσσ hJ hP h2 w c)
  exact ⟨funext fun b => Subtype.ext (congrFun h1 b), Subtype.ext h2'⟩

def coordEquiv : FrameUnipotentSubgroup R σ J P ≃ ((Fin r → Wsub R σ J P) × Sk R σ r) where
  toFun n := (phiW hσσ hJ hP n, phiS hσσ hJ hP h2 n)
  invFun p := ⟨nG hσσ hJ hP h2 p.1 p.2, nG_mem hσσ hJ hP h2 p.1 p.2⟩
  left_inv n := Subtype.ext (nG_phi hσσ hJ hP h2 n)
  right_inv p := Prod.ext (phi_nG hσσ hJ hP h2 p.1 p.2).1 (phi_nG hσσ hJ hP h2 p.1 p.2).2

theorem phi_mul (n₀ n : FrameUnipotentSubgroup R σ J P) :
    wv (phiW hσσ hJ hP (n₀ * n)) = wv (phiW hσσ hJ hP n₀) + wv (phiW hσσ hJ hP n) ∧
      phiSv hσσ hJ hP (n₀ * n) = phiSv hσσ hJ hP n₀ + phiSv hσσ hJ hP n +
        betaM R σ J (wv (phiW hσσ hJ hP n₀)) (wv (phiW hσσ hJ hP n)) := by
  have hl : lin R σ J ((n₀ * n : FrameUnipotentSubgroup R σ J P) : HA R σ J) =
      Lr σ J P T (wv (phiW hσσ hJ hP n₀) + wv (phiW hσσ hJ hP n))
        (phiSv hσσ hJ hP n₀ + phiSv hσσ hJ hP n +
          betaM R σ J (wv (phiW hσσ hJ hP n₀)) (wv (phiW hσσ hJ hP n))) := by
    refine LinearMap.ext fun v => ?_
    rw [Subgroup.coe_mul, lin_mul, lin_eq_Lr hσσ hJ hP n₀, lin_eq_Lr hσσ hJ hP n,
      Lr_comp hσσ hJ hP h2 (w := wv (phiW hσσ hJ hP n₀)) (w' := wv (phiW hσσ hJ hP n))
      (fun a => (phiW hσσ hJ hP n₀ a).2) (fun a => (phiW hσσ hJ hP n a).2)]
  exact phi_of_lin hσσ hJ hP (n₀ * n)
    (fun a => (Wsub R σ J P).add_mem (phiW hσσ hJ hP n₀ a).2 (phiW hσσ hJ hP n a).2) _ hl

theorem phi_conj {h : HA R σ J} (hh : h ∈ Hsub R σ J P) (n n' : FrameUnipotentSubgroup R σ J P)
    (hn : (n' : HA R σ J) = h * n * h⁻¹) :
    wv (phiW hσσ hJ hP n') = (fun a => lin R σ J h (wv (phiW hσσ hJ hP n) a)) ∧
      phiSv hσσ hJ hP n' = phiSv hσσ hJ hP n := by
  have H := datR_hyp (R := R) hσσ hJ hP
  have hS := stabilizer_fixes_frame_and_normal (T := T) (heisenberg_le_stabilizer R σ J P hh)
  have hf : ∀ b, lin R σ J h ((datR R σ J P T).f b) = (datR R σ J P T).f b :=
    fun b => fix_f_of_H hσσ hJ hP hh b
  have hU := uni_lin (T := T) (P := P) h
  have hw : ∀ a, lin R σ J h (wv (phiW hσσ hJ hP n) a) ∈ Wsub R σ J P :=
    fun a => lin_mem_Wsub hh (phiW hσσ hJ hP n a).2
  have hl : lin R σ J (n' : HA R σ J) =
      Lr σ J P T (fun a => lin R σ J h (wv (phiW hσσ hJ hP n) a)) (phiSv hσσ hJ hP n) := by
    refine LinearMap.ext fun v => ?_
    rw [hn, lin_mul, lin_mul, lin_eq_Lr hσσ hJ hP n, Lr, PG.Dat.S_L H hS hf hU, lin_lin_inv, Lr]
    congr 2
    funext a b
    rw [hR_lin]
  exact phi_of_lin hσσ hJ hP n' hw _ hl

end R

end PI.VolSemiDirect.W.Md
