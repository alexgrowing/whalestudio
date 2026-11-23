import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsAdaptedEmpty
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.LeviEqISupParts
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ExistsUnitOfComm
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
open GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet

noncomputable section

namespace GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.USplit

open GlobalTheory.CompanionTheory.LeviGen (prj prX prY onPart ind)
open Formalism.UG (cT)

section Abstract

variable {A : Type} [CommRing A] {n r : ℕ}

theorem mul_ind_cT (s : A →+* A) (X Y : Matrix (Fin n) (Fin r) A) (k : Fin r) :
    X * diagonal (ind {i | i ≤ k} : Fin r → A) * cT s Y =
      (X.submatrix id (Fin.castLE k.2) : Matrix (Fin n) (Fin (k.val + 1)) A) *
        cT s (Y.submatrix id (Fin.castLE k.2) : Matrix (Fin n) (Fin (k.val + 1)) A) := by
  classical
  ext a b
  rw [Matrix.mul_apply, Matrix.mul_apply]
  symm
  refine Finset.sum_of_injOn (Fin.castLE k.2) (Fin.castLE_injective _).injOn
    (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _)) ?_ ?_
  · intro i _ hi
    have h : ¬ i ≤ k := fun h => hi ⟨⟨i.1, Nat.lt_succ_of_le h⟩, by simp, by ext; simp⟩
    simp [Matrix.mul_diagonal, GlobalTheory.CompanionTheory.LeviGen.ind_apply, h]
  · intro j _
    have h : Fin.castLE k.2 j ≤ k := Nat.le_of_lt_succ j.2
    simp [Matrix.mul_diagonal, GlobalTheory.CompanionTheory.LeviGen.ind_apply, h, cT]

theorem onPart_mul_fix {m : ℕ} {Q G : Matrix (Fin n) (Fin n) A} {Z : Matrix (Fin n) (Fin m) A} (h : Q * Z = Z) :
    onPart Q G * Z = G * Z := by
  simp only [onPart, Matrix.add_mul, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, h, sub_self, zero_add]

theorem comm_onPart {Q G t : Matrix (Fin n) (Fin n) A} (htQ : t * Q = Q) (hQt : Q * t = Q) (hc : G * Q = Q * G) :
    t * onPart Q G = onPart Q G * t := by
  have e1 : t * (G * Q) = Q * G := by rw [hc, ← Matrix.mul_assoc, htQ]
  have e2 : G * Q * t = Q * G := by rw [Matrix.mul_assoc, hQt, hc]
  simp only [onPart, Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul,
    htQ, hQt, e1, e2]

theorem mul_onPart_inv {Q G H : Matrix (Fin n) (Fin n) A} (hQ : Q * Q = Q) (hGH : G * H = 1) :
    G * onPart Q H * Q = Q := by
  simp only [onPart, Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul,
    Matrix.mul_assoc, hQ, sub_self, zero_add]
  rw [← Matrix.mul_assoc, hGH, Matrix.one_mul]

end Abstract

section Field

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {X Y : Matrix (Fin n) (Fin r) E}

variable (σ J X Y) in

def P (I : Set (Fin r)) : Matrix (Fin n) (Fin n) E := prj (σ : E →+* E) J X Y (ind I)

theorem proj_eq_frameProj (I : Set (Fin r)) : P σ J X Y I = GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.Comm.frameProj σ J X Y I := by
  simp only [P, prj, prX, prY, GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.Comm.frameProj, GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.Comm.blockDiag,
    Matrix.mul_assoc]
  rfl

theorem P_sq (hCM : IsCMExt F E σ) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y) (I : Set (Fin r)) :
    P σ J X Y I * P σ J X Y I = P σ J X Y I := by
  rw [P, GlobalTheory.CompanionTheory.LeviGen.prj_mul_prj hW.xx hW.yy hW.xy (GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.Comm.yJx hCM hJ hW),
    GlobalTheory.CompanionTheory.LeviGen.ind_mul_self]

theorem proj_mul_X (hCM : IsCMExt F E σ) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y) (I : Set (Fin r)) :
    P σ J X Y I * X = X * diagonal (ind I : Fin r → E) := by
  rw [P, prj, Matrix.add_mul, GlobalTheory.CompanionTheory.LeviGen.prX_mul_X (GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.Comm.yJx hCM hJ hW),
    GlobalTheory.CompanionTheory.LeviGen.prY_mul_X hW.xx, add_zero]

theorem proj_mul_Y (hW : IsWittFrame σ J X Y) (I : Set (Fin r)) :
    P σ J X Y I * Y = Y * diagonal (ind I : Fin r → E) := by
  rw [P, prj, Matrix.add_mul, GlobalTheory.CompanionTheory.LeviGen.prX_mul_Y hW.yy, GlobalTheory.CompanionTheory.LeviGen.prY_mul_Y hW.xy, zero_add]

theorem P_selfAdjoint (hCM : IsCMExt F E σ) (hJ : IsHermND σ J) (I : Set (Fin r)) :
    cT (σ : E →+* E) (P σ J X Y I) * J = J * P σ J X Y I := by
  rw [proj_eq_frameProj]
  exact GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.Comm.frameProj_selfAdj hCM hJ I

theorem proj_Iic_eq (k : Fin r) :
    P σ J X Y {i | i ≤ k} = initCols X k * cT (σ : E →+* E) (initCols Y k) * J +
      initCols Y k * cT (σ : E →+* E) (initCols X k) * J := by
  simp only [P, prj, prX, prY, mul_ind_cT]
  rfl

theorem cT_init_mul (C C' : Matrix (Fin n) (Fin r) E) (k : Fin r) {M : Matrix (Fin r) (Fin r) E}
    (h : cT (σ : E →+* E) C * J * C' = M) :
    cT (σ : E →+* E) (initCols C k) * J * initCols C' k = M.submatrix (Fin.castLE k.2) (Fin.castLE k.2) := by
  subst h
  rfl

theorem mul_diag_init (C : Matrix (Fin n) (Fin r) E) {T : Finset (Fin r)} {k : Fin r} (hk : k ∈ T) :
    ((C * diagonal (ind (upTo T) : Fin r → E)).submatrix id (Fin.castLE k.2) :
      Matrix (Fin n) (Fin (k.val + 1)) E) = initCols C k := by
  classical
  ext a j
  have h : Fin.castLE k.2 j ∈ upTo T := ⟨k, hk, Nat.le_of_lt_succ j.2⟩
  simp [Matrix.mul_diagonal, GlobalTheory.CompanionTheory.LeviGen.ind_apply, h, initCols]

end Field

section Main

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {X Y : Matrix (Fin n) (Fin r) E}

theorem upTo_eq_max {T : Finset (Fin r)} (hT : T.Nonempty) : upTo T = {i | i ≤ T.max' hT} := by
  ext i
  constructor
  · rintro ⟨k, hk, hik⟩
    exact le_trans hik (T.le_max' k hk)
  · intro h
    exact ⟨_, T.max'_mem hT, h⟩

theorem proj_upTo_empty : P σ J X Y (upTo (∅ : Finset (Fin r))) = 0 := by
  have e : upTo (∅ : Finset (Fin r)) = ∅ := by ext i; simp [upTo]
  rw [P, e, GlobalTheory.CompanionTheory.LeviGen.ind_empty]
  simp [prj, prX, prY]

theorem adMat_P_idempotent (hCM : IsCMExt F E σ) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y) (I : Set (Fin r)) :
    adMat F (P σ J X Y I) * adMat F (P σ J X Y I) = adMat F (P σ J X Y I) := by
  rw [← Matrix.map_mul, P_sq hCM hJ hW]

theorem adMat_P_selfAdjoint (hCM : IsCMExt F E σ) (hJ : IsHermND σ J) (I : Set (Fin r)) :
    Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ) (adMat F (P σ J X Y I)) * JR (F := F) (AF F) J =
      JR (F := F) (AF F) J * adMat F (P σ J X Y I) := by
  rw [GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.Comm.cT_map]
  show (cT (σ : E →+* E) (P σ J X Y I)).map (inclR (F := F) (AF F)) * J.map (inclR (F := F) (AF F)) =
    J.map (inclR (F := F) (AF F)) * (P σ J X Y I).map (inclR (F := F) (AF F))
  rw [← Matrix.map_mul, ← Matrix.map_mul, P_selfAdjoint hCM hJ]

theorem frame_one {C C' : Matrix (Fin n) (Fin r) E} (h : cT (σ : E →+* E) C * J * C' = 1) (k : Fin r) :
    cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ) (adMat F (initCols C k)) * JR (F := F) (AF F) J * adMat F (initCols C' k) = 1 := by
  rw [GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.Comm.cT_map]
  show (cT (σ : E →+* E) (initCols C k)).map (inclR (F := F) (AF F)) * J.map (inclR (F := F) (AF F)) *
    (initCols C' k).map (inclR (F := F) (AF F)) = 1
  rw [← Matrix.map_mul, ← Matrix.map_mul, cT_init_mul C C' k h, Matrix.submatrix_one _ (Fin.castLE_injective _)]
  exact Matrix.map_one _ (map_zero _) (map_one _)

end Main

section Main2

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {X Y : Matrix (Fin n) (Fin r) E}

theorem matHom_mul_inv (g : GAd σ J) :
    (matHom (AF F) σ J g).1 * (matHom (AF F) σ J g⁻¹).1 = 1 := by
  rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]

theorem matHom_inv_mul (g : GAd σ J) :
    (matHom (AF F) σ J g⁻¹).1 * (matHom (AF F) σ J g).1 = 1 := by
  rw [← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]

theorem matHom_unitary (g : GAd σ J) :
    Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ) (matHom (AF F) σ J g).1 * JR (F := F) (AF F) J *
      (matHom (AF F) σ J g).1 = JR (F := F) (AF F) J :=
  (show HR (AF F) σ J from g).2

theorem comm_Q (hCM : IsCMExt F E σ) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y) {T : Finset (Fin r)}
    {g : GAd σ J} (hg : g ∈ levi σ J X Y T) :
    (matHom (AF F) σ J g).1 * adMat F (P σ J X Y (upTo T)) = adMat F (P σ J X Y (upTo T)) * (matHom (AF F) σ J g).1 := by
  rcases T.eq_empty_or_nonempty with rfl | hT
  · rw [proj_upTo_empty]
    simp
  set k := T.max' hT
  have hk : k ∈ T := T.max'_mem hT
  simp only [levi, Subgroup.mem_iInf, Subgroup.mem_inf] at hg
  obtain ⟨B, -, hB⟩ := (hg k hk).1
  obtain ⟨C, -, hC⟩ := (hg k hk).2
  have eQ : adMat F (P σ J X Y (upTo T)) =
      adMat F (initCols X k) * cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ) (adMat F (initCols Y k)) * JR (F := F) (AF F) J +
      adMat F (initCols Y k) * cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ) (adMat F (initCols X k)) * JR (F := F) (AF F) J := by
    rw [upTo_eq_max hT, proj_Iic_eq, GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.Comm.cT_map, GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.Comm.cT_map]
    simp only [adMat, JR]
    rw [Matrix.map_add _ (map_add (inclR (F := F) (E := E) (AF F)))]
    simp only [Matrix.map_mul]
    try rfl
  have h1 := GlobalTheory.CompanionTheory.LeviGen.comm_of_frame (frame_one (GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.Comm.yJx hCM hJ hW) k)
    (matHom_unitary g) (matHom_mul_inv g) (matHom_inv_mul g) hB hC
  have h2 := GlobalTheory.CompanionTheory.LeviGen.comm_of_frame (frame_one hW.xy k)
    (matHom_unitary g) (matHom_mul_inv g) (matHom_inv_mul g) hC hB
  rw [eQ, Matrix.mul_add, Matrix.add_mul, h1, h2]

end Main2

section Main3

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {X Y : Matrix (Fin n) (Fin r) E}

theorem Q_mulVec_col (hCM : IsCMExt F E σ) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y) (I : Set (Fin r))
    {C : Matrix (Fin n) (Fin r) E} (hC : P σ J X Y I * C = C * diagonal (ind I : Fin r → E)) {i : Fin r} (hi : i ∈ I) :
    adMat F (P σ J X Y I) *ᵥ (adMat F C)ᵀ i = (adMat F C)ᵀ i := by
  classical
  funext a
  show (adMat F (P σ J X Y I) * adMat F C) a i = adMat F C a i
  rw [← Matrix.map_mul, hC]
  simp [Matrix.mul_diagonal, GlobalTheory.CompanionTheory.LeviGen.ind_apply, hi]

theorem Q_fix_span (hCM : IsCMExt F E σ) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y) (I : Set (Fin r))
    {y : Fin n → AF F ⊗[F] E} (hy : y ∈ colSpan F X I ⊔ colSpan F Y I) :
    adMat F (P σ J X Y I) *ᵥ y = y := by
  let S : Submodule (AF F ⊗[F] E) (Fin n → AF F ⊗[F] E) :=
    LinearMap.eqLocus (adMat F (P σ J X Y I)).mulVecLin LinearMap.id
  have hle : colSpan F X I ⊔ colSpan F Y I ≤ S := by
    refine sup_le (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)
    · rintro _ ⟨i, hi, rfl⟩
      exact Q_mulVec_col hCM hJ hW I (proj_mul_X hCM hJ hW I) hi
    · rintro _ ⟨i, hi, rfl⟩
      exact Q_mulVec_col hCM hJ hW I (proj_mul_Y hW I) hi
  exact hle hy

theorem Q_mul_init (hCM : IsCMExt F E σ) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y) {T : Finset (Fin r)}
    {C : Matrix (Fin n) (Fin r) E} (hC : P σ J X Y (upTo T) * C = C * diagonal (ind (upTo T) : Fin r → E))
    {k : Fin r} (hk : k ∈ T) :
    adMat F (P σ J X Y (upTo T)) * adMat F (initCols C k) = adMat F (initCols C k) := by
  rw [← Matrix.map_mul]
  congr 1
  have e : P σ J X Y (upTo T) * initCols C k =
      ((P σ J X Y (upTo T) * C).submatrix id (Fin.castLE k.2) : Matrix (Fin n) (Fin (k.val + 1)) E) := rfl
  rw [e, hC, mul_diag_init C hk]

def onFrame (hCM : IsCMExt F E σ) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y) (T : Finset (Fin r)) (g : GAd σ J)
    (hg : g ∈ levi σ J X Y T) : GAd σ J :=
  show HR (AF F) σ J from
  ⟨⟨onPart (adMat F (P σ J X Y (upTo T))) (matHom (AF F) σ J g).1,
      onPart (adMat F (P σ J X Y (upTo T))) (matHom (AF F) σ J g⁻¹).1,
      GlobalTheory.CompanionTheory.LeviGen.onPart_inv (adMat_P_idempotent hCM hJ hW _) (comm_Q hCM hJ hW hg) (matHom_mul_inv g) (matHom_inv_mul g),
      GlobalTheory.CompanionTheory.LeviGen.onPart_inv (adMat_P_idempotent hCM hJ hW _)
        (GlobalTheory.CompanionTheory.LeviGen.comm_inv (comm_Q hCM hJ hW hg) (matHom_mul_inv g) (matHom_inv_mul g))
        (matHom_inv_mul g) (matHom_mul_inv g)⟩,
    GlobalTheory.CompanionTheory.LeviGen.onPart_unitary (adMat_P_idempotent hCM hJ hW _) (adMat_P_selfAdjoint hCM hJ _) (comm_Q hCM hJ hW hg)
      (matHom_unitary g) (matHom_mul_inv g) (matHom_inv_mul g)⟩

theorem matHom_onFrame (hCM : IsCMExt F E σ) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y) (T : Finset (Fin r))
    (g : GAd σ J) (hg : g ∈ levi σ J X Y T) :
    (matHom (AF F) σ J (onFrame hCM hJ hW T g hg)).1 = onPart (adMat F (P σ J X Y (upTo T))) (matHom (AF F) σ J g).1 :=
  rfl

theorem matHom_onFrame_inv (hCM : IsCMExt F E σ) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y) (T : Finset (Fin r))
    (g : GAd σ J) (hg : g ∈ levi σ J X Y T) :
    (matHom (AF F) σ J (onFrame hCM hJ hW T g hg)⁻¹).1 = onPart (adMat F (P σ J X Y (upTo T))) (matHom (AF F) σ J g⁻¹).1 :=
  rfl

end Main3

section AutomorphyRankFourMain

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {X Y : Matrix (Fin n) (Fin r) E}

theorem onFrame_mem_levi (hCM : IsCMExt F E σ) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y) (T : Finset (Fin r))
    (g : GAd σ J) (hg : g ∈ levi σ J X Y T) : onFrame hCM hJ hW T g hg ∈ levi σ J X Y T := by
  have hg' := hg
  simp only [levi, Subgroup.mem_iInf, Subgroup.mem_inf] at hg' ⊢
  intro k hk
  obtain ⟨B, -, hB⟩ := (hg' k hk).1
  obtain ⟨C, -, hC⟩ := (hg' k hk).2
  refine ⟨⟨B, Subgroup.mem_top _, ?_⟩, ⟨C, Subgroup.mem_top _, ?_⟩⟩
  · rw [matHom_onFrame, onPart_mul_fix (Q_mul_init hCM hJ hW (proj_mul_X hCM hJ hW _) hk), hB]
  · rw [matHom_onFrame, onPart_mul_fix (Q_mul_init hCM hJ hW (proj_mul_Y hW _) hk), hC]

theorem mul_inv_onFrame_mem_uPart (hCM : IsCMExt F E σ) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y)
    (T : Finset (Fin r)) (g : GAd σ J) (hg : g ∈ levi σ J X Y T) :
    g * (onFrame hCM hJ hW T g hg)⁻¹ ∈ uPart σ J X Y T := by
  intro y hy
  have hQy := Q_fix_span hCM hJ hW (upTo T) hy
  rw [map_mul, Units.val_mul, matHom_onFrame_inv]
  rw [← hQy, mulVec_mulVec,
    mul_onPart_inv (adMat_P_idempotent hCM hJ hW _) (matHom_mul_inv g)]

theorem Q_fix_of_uPart (hCM : IsCMExt F E σ) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y) {T : Finset (Fin r)}
    {t : GAd σ J} (ht : t ∈ uPart σ J X Y T) :
    (matHom (AF F) σ J t).1 * adMat F (P σ J X Y (upTo T)) = adMat F (P σ J X Y (upTo T)) := by
  have key : ∀ v, (matHom (AF F) σ J t).1 *ᵥ (adMat F (P σ J X Y (upTo T)) *ᵥ v) =
      adMat F (P σ J X Y (upTo T)) *ᵥ v := fun v => by
    refine ht _ ?_
    rw [proj_eq_frameProj]
    show (GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.Comm.frameProj σ J X Y (upTo T)).map (inclR (F := F) (AF F)) *ᵥ v ∈ _
    rw [GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.Comm.frameProj_map, add_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, ← mulVec_mulVec,
      ← mulVec_mulVec]
    exact Submodule.add_mem_sup (GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.Comm.mem_colSpan X subset_rfl _)
      (GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.Comm.mem_colSpan Y subset_rfl _)
  ext i j
  have := congrFun (key (Pi.single j 1)) i
  rw [mulVec_mulVec, mulVec_single_one, mulVec_single_one] at this
  exact this

theorem comm_onFrame (hCM : IsCMExt F E σ) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y) (T : Finset (Fin r))
    (g : GAd σ J) (hg : g ∈ levi σ J X Y T) {t : GAd σ J} (ht : t ∈ uPart σ J X Y T) :
    t * onFrame hCM hJ hW T g hg = onFrame hCM hJ hW T g hg * t := by
  have hJu : IsUnit (JR (F := F) (AF F) J).det := by
    rw [show JR (F := F) (AF F) J = J.map (inclR (F := F) (AF F)) from rfl,
      show (J.map (inclR (F := F) (E := E) (AF F))).det = inclR (F := F) (E := E) (AF F) J.det from
      (RingHom.map_det (inclR (F := F) (E := E) (AF F)) J).symm]
    exact (isUnit_iff_ne_zero.2 hJ.2).map (inclR (F := F) (E := E) (AF F))
  have htQ := Q_fix_of_uPart hCM hJ hW ht
  have hQt := GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.Comm.mul_eq_of_unitary hJu (matHom_unitary t) (adMat_P_selfAdjoint hCM hJ _) htQ
  have hc := comm_onPart htQ hQt (comm_Q hCM hJ hW hg)
  refine GlobalTheory.AdelicU.matHom_injective (AF F) σ J ?_
  rw [map_mul, map_mul]
  exact Units.ext (by rw [Units.val_mul, Units.val_mul, matHom_onFrame]; exact hc)

theorem exists_split_general (hCM : IsCMExt F E σ) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y) (T : Finset (Fin r))
    (g : GAd σ J) (hg : g ∈ levi σ J X Y T) :
    ∃ mH ∈ uPart σ J X Y T, ∃ mo ∈ levi σ J X Y T, (∀ t ∈ uPart σ J X Y T, t * mo = mo * t) ∧ g = mH * mo :=
  ⟨_, mul_inv_onFrame_mem_uPart hCM hJ hW T g hg, _, onFrame_mem_levi hCM hJ hW T g hg,
    fun _ ht => comm_onFrame hCM hJ hW T g hg ht, (inv_mul_cancel_right g _).symm⟩

end AutomorphyRankFourMain

theorem exists_split : ∀ (D : D7) (V : HSp D) (m : ℕ) (X Y : Matrix (Fin V.rank) (Fin m) D.host.E),
    GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram X Y → ∀ (T : Finset (Fin m)), ∀ mm ∈ levi D.sp.cm.sig V.gram X Y T,
    ∃ mH ∈ uPart D.sp.cm.sig V.gram X Y T, ∃ mo ∈ levi D.sp.cm.sig V.gram X Y T,
      (∀ t ∈ uPart D.sp.cm.sig V.gram X Y T, t * mo = mo * t) ∧ mm = mH * mo := by
  intro D V m X Y hW T mm hmm
  obtain ⟨hCM, hJ⟩ := GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND D.host.F D.host.E D.sp.cm
  exact exists_split_general hCM (hJ V) hW T mm hmm

end GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.USplit
end
