import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsotropicUnipotentRadicalsRationalCocompact

noncomputable section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.Mem.UnipCocompact
open Formalism.UG (cT cT_mul cT_one)
open scoped TensorProduct

namespace GlobalTheory.UAut

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) {r : ℕ}

def IsIsoCols (C : Matrix (Fin n) (Fin r) E) : Prop :=
  LinearIndependent E Cᵀ ∧ cT (σ : E →+* E) C * J * C = 0

def unipSet (C : Matrix (Fin n) (Fin r) E) (d : Fin r → ℕ) : Set (GAd σ J) :=
  {g | (∀ i, ∃ a : Fin r → AF F ⊗[F] E, (∀ j, d i ≤ d j → a j = 0) ∧
      ((matHom _ σ J g).1 - 1) *ᵥ (fun k => inclR (F := F) (AF F) (C k i)) = adMat F C *ᵥ a) ∧
    ∀ x : Fin n → E, (cT (σ : E →+* E) C * J) *ᵥ x = 0 →
      ∃ a, ((matHom _ σ J g).1 - 1) *ᵥ (fun i => inclR (F := F) (AF F) (x i)) = adMat F C *ᵥ a}

def unipFlag (C : Matrix (Fin n) (Fin r) E) (d : Fin r → ℕ) : Subgroup (GAd σ J) := Subgroup.closure (unipSet σ J C d)

def parFlag (C : Matrix (Fin n) (Fin r) E) (d : Fin r → ℕ) : Subgroup (GAd σ J) where
  carrier := {p | (∃ B : Matrix (Fin r) (Fin r) (AF F ⊗[F] E), B.BlockTriangular d ∧
      (matHom _ σ J p).1 * adMat F C = adMat F C * B) ∧
    ∃ B : Matrix (Fin r) (Fin r) (AF F ⊗[F] E), B.BlockTriangular d ∧ (matHom _ σ J p⁻¹).1 * adMat F C = adMat F C * B}
  one_mem' := ⟨⟨1, blockTriangular_one, by simp⟩, 1, blockTriangular_one, by simp⟩
  mul_mem' := fun {p q} ⟨⟨A, hA, eA⟩, A', hA', eA'⟩ ⟨⟨B, hB, eB⟩, B', hB', eB'⟩ =>
    ⟨⟨A * B, hA.mul hB, by
      rw [map_mul, Units.val_mul, Matrix.mul_assoc, eB, ← Matrix.mul_assoc, eA, Matrix.mul_assoc]⟩,
      B' * A', hB'.mul hA', by
        rw [_root_.mul_inv_rev, map_mul, Units.val_mul, Matrix.mul_assoc, eA', ← Matrix.mul_assoc, eB', Matrix.mul_assoc]⟩
  inv_mem' := fun {p} h => ⟨h.2, by rw [inv_inv]; exact h.1⟩

def leviFlag (X Y : Matrix (Fin n) (Fin r) E) (d : Fin r → ℕ) : Subgroup (GAd σ J) := parFlag σ J X d ⊓ parFlag σ J Y d

def leftGrp (C : Matrix (Fin n) (Fin r) E) (d : Fin r → ℕ) : Subgroup (GAd σ J) :=
  unipFlag σ J C d ⊔ (ratPts σ J ⊓ parFlag σ J C d)

def adjA : Matrix (Fin n) (Fin n) (AF F ⊗[F] E) →+ Matrix (Fin n) (Fin n) (AF F ⊗[F] E) where
  toFun X := J⁻¹.map (inclR (F := F) (AF F)) * cT (sigR (AF F) σ) X * J.map (inclR (F := F) (AF F))
  map_zero' := by simp [cT]
  map_add' X Y := by simp [cT, Matrix.map_add _ (map_add _), Matrix.mul_add, Matrix.add_mul]

def idemA (C : Matrix (Fin n) (Fin r) E) (L : Matrix (Fin r) (Fin n) E) (j : Fin r) :
    Matrix (Fin n) (Fin n) (AF F ⊗[F] E) := (C * single j j (1 : E) * L).map (inclR (F := F) (AF F))

variable {σ J}

omit [NumberField E] in
theorem adjA_apply (X : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) : adjA σ J X =
    J⁻¹.map (inclR (F := F) (AF F)) * cT (sigR (AF F) σ) X * J.map (inclR (F := F) (AF F)) := rfl

omit [NumberField E] in
theorem adjA_map (X : Matrix (Fin n) (Fin n) E) : adjA σ J (X.map (inclR (F := F) (AF F))) =
    (J⁻¹ * cT (σ : E →+* E) X * J).map (inclR (F := F) (AF F)) := by
  rw [adjA_apply, GlobalTheory.AutFunCounterexample.cT_map_gen, Matrix.map_mul, Matrix.map_mul]

omit [NumberField E] in
theorem idemA_eq (C : Matrix (Fin n) (Fin r) E) (L : Matrix (Fin r) (Fin n) E) (j : Fin r) :
    idemA (F := F) C L j = C.map (inclR (F := F) (AF F)) * single j j (1 : AF F ⊗[F] E) * L.map (inclR (F := F) (AF F)) := by
  rw [idemA, Matrix.map_mul, Matrix.map_mul, Matrix.map_single, map_one]

omit [NumberField E] in
theorem sum_idemA (C : Matrix (Fin n) (Fin r) E) (L : Matrix (Fin r) (Fin n) E) :
    ∑ j, idemA (F := F) C L j = (C * L).map (inclR (F := F) (AF F)) := by
  simp only [idemA_eq]
  rw [← Matrix.sum_mul, ← Matrix.mul_sum, Matrix.sum_single_one, Matrix.mul_one, Matrix.map_mul]

theorem lower_iff {C : Matrix (Fin n) (Fin r) E} {d : Fin r → ℕ} {m : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)} :
    (∀ i, ∃ a : Fin r → AF F ⊗[F] E, (∀ j, d i ≤ d j → a j = 0) ∧
      m *ᵥ (fun k => inclR (F := F) (AF F) (C k i)) = adMat F C *ᵥ a) ↔
    ∃ A : Matrix (Fin r) (Fin r) (AF F ⊗[F] E), (∀ j i, d i ≤ d j → A j i = 0) ∧ m * adMat F C = adMat F C * A := by
  constructor
  · intro h
    choose a ha e using h
    exact ⟨of fun j i => a i j, fun j i => ha i j, Matrix.ext fun k i => congrFun (e i) k⟩
  · rintro ⟨A, hA, e⟩ i
    exact ⟨fun j => A j i, fun j => hA j i, funext fun k => congrFun (congrFun e k) i⟩

theorem form_mul_of_mul_cols {C : Matrix (Fin n) (Fin r) E} {g : GAd σ J} {B : Matrix (Fin r) (Fin r) (AF F ⊗[F] E)}
    (h : (matHom _ σ J g).1 * adMat F C = adMat F C * B) :
    adMat F (cT (σ : E →+* E) C * J) * (matHom _ σ J g⁻¹).1 = cT (sigR (AF F) σ) B * adMat F (cT (σ : E →+* E) C * J) := by
  have hg : cT (sigR (AF F) σ) (matHom _ σ J g).1 * adMat F J * (matHom _ σ J g).1 = adMat F J := g.2
  have hi : (matHom _ σ J g).1 * (matHom _ σ J g⁻¹).1 = 1 := Units.mul_inv g.1
  have e : adMat F J * (matHom _ σ J g⁻¹).1 = cT (sigR (AF F) σ) (matHom _ σ J g).1 * adMat F J := by
    conv_lhs => rw [← hg, Matrix.mul_assoc, hi, Matrix.mul_one]
  rw [adMat, Matrix.map_mul, ← GlobalTheory.AutFunCounterexample.cT_map_gen, Matrix.mul_assoc, e, ← Matrix.mul_assoc, ← cT_mul, h, cT_mul,
    Matrix.mul_assoc]

theorem unipFlag_const (C : Matrix (Fin n) (Fin r) E) (c : ℕ) : unipFlag σ J C (fun _ => c) = unipRad σ J C := by
  rw [unipFlag, unipRad]
  congr 1
  ext g
  have h1 : ∀ m : Matrix (Fin n) (Fin n) (AF F ⊗[F] E), (∃ A : Matrix (Fin r) (Fin r) (AF F ⊗[F] E),
      (∀ j i, c ≤ c → A j i = 0) ∧ m * adMat F C = adMat F C * A) ↔ m * adMat F C = 0 := fun m =>
    ⟨fun ⟨A, hA, e⟩ => by rw [e, show A = 0 from Matrix.ext fun j i => hA j i le_rfl, Matrix.mul_zero],
      fun e => ⟨0, fun _ _ _ => rfl, by rw [e, Matrix.mul_zero]⟩⟩
  refine (and_congr (lower_iff.trans (h1 _)) Iff.rfl).trans ⟨fun h => ⟨h.1, ?_, h.2⟩, fun h => ⟨h.1, h.2.2⟩⟩
  have e : (matHom _ σ J g).1 * adMat F C = adMat F C * (1 : Matrix (Fin r) (Fin r) (AF F ⊗[F] E)) := by
    have := h.1
    rw [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at this
    rw [this, Matrix.mul_one]
  have e2 := form_mul_of_mul_cols e
  have hi : (matHom _ σ J g⁻¹).1 * (matHom _ σ J g).1 = 1 := Units.inv_mul g.1
  rw [cT_one, Matrix.one_mul] at e2
  rw [Matrix.mul_sub, Matrix.mul_one, sub_eq_zero]
  conv_lhs => rw [← e2, Matrix.mul_assoc, hi, Matrix.mul_one]

section Form

variable (hJ : IsHermND σ J)
include hJ

omit [NumberField F] [NumberField E] in
theorem det_isUnit : IsUnit J.det := IsUnit.mk0 _ hJ.2

omit [NumberField F] [NumberField E] in
theorem cT_form : cT (σ : E →+* E) J = J := Matrix.ext fun i j => hJ.1 i j

omit [NumberField F] [NumberField E] in
theorem cT_form_inv : cT (σ : E →+* E) J⁻¹ = J⁻¹ := by
  refine (Matrix.inv_eq_left_inv ?_).symm
  nth_rewrite 2 [← cT_form hJ]
  rw [← cT_mul, Matrix.mul_nonsing_inv _ (det_isUnit hJ), cT_one]

omit [NumberField E] in
theorem form_mul_inv : J.map (inclR (F := F) (AF F)) * J⁻¹.map (inclR (F := F) (AF F)) = 1 := by
  rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ (det_isUnit hJ), Matrix.map_one _ (map_zero _) (map_one _)]

omit [NumberField E] in
theorem inv_mul_form : J⁻¹.map (inclR (F := F) (AF F)) * J.map (inclR (F := F) (AF F)) = 1 :=
  mul_eq_one_comm.1 (form_mul_inv hJ)

omit [NumberField E] in
theorem adjA_mul (X Y : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) : adjA σ J (X * Y) = adjA σ J Y * adjA σ J X := by
  simp only [adjA_apply, cT_mul, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (J.map _), form_mul_inv hJ, Matrix.one_mul]

omit [NumberField E] in
theorem adjA_mul_self_iff (g : GL (Fin n) (AF F ⊗[F] E)) : adjA σ J g.1 * g.1 = 1 ↔ g ∈ HR (AF F) σ J := by
  change _ ↔ cT _ g.1 * J.map _ * g.1 = J.map _
  rw [adjA_apply, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (cT _ _)]
  constructor
  · intro h
    have := congrArg (J.map (inclR (F := F) (AF F)) * ·) h
    simpa only [← Matrix.mul_assoc, form_mul_inv hJ, Matrix.one_mul, Matrix.mul_one] using this
  · intro h
    rw [h, inv_mul_form hJ]

theorem adjA_mat (g : GAd σ J) : adjA σ J (matHom _ σ J g).1 = (matHom _ σ J g⁻¹).1 :=
  (Units.inv_eq_of_mul_eq_one_left ((adjA_mul_self_iff hJ g.1).2 g.2)).symm

omit [NumberField E] in
theorem perp_iff_idemA (C : Matrix (Fin n) (Fin r) E) (L : Matrix (Fin r) (Fin n) E)
    (hL : L * C = 1) (m : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) :
    (∀ x : Fin n → E, (cT (σ : E →+* E) C * J) *ᵥ x = 0 →
        ∃ a, m *ᵥ (fun i => inclR (F := F) (AF F) (x i)) = C.map (inclR (F := F) (AF F)) *ᵥ a) ↔
      (1 - (C * L).map (inclR (F := F) (AF F))) * m * (1 - adjA σ J ((C * L).map (inclR (F := F) (AF F)))) = 0 := by
  rw [adjA_map]
  set φ := inclR (F := F) (E := E) (AF F)
  have hL' : L.map φ * C.map φ = 1 := by rw [← Matrix.map_mul, hL, Matrix.map_one _ (map_zero _) (map_one _)]
  have e : J⁻¹ * cT (σ : E →+* E) (C * L) * J = J⁻¹ * cT (σ : E →+* E) L * (cT (σ : E →+* E) C * J) := by
    rw [cT_mul]; simp only [Matrix.mul_assoc]
  have hT : cT (σ : E →+* E) C * J * (J⁻¹ * cT (σ : E →+* E) L) = 1 := by
    rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_right _ _ (det_isUnit hJ), ← cT_mul, hL, cT_one]
  rw [e]
  generalize cT (σ : E →+* E) C * J = T at hT ⊢
  generalize J⁻¹ * cT (σ : E →+* E) L = P at hT ⊢
  have e1 : 1 - (P * T).map φ = (1 - P * T).map φ := by
    rw [Matrix.map_sub _ (map_sub _), Matrix.map_one _ (map_zero _) (map_one _)]
  constructor
  · intro h
    ext i k
    obtain ⟨a, ha⟩ := h (fun j => (1 - P * T : Matrix (Fin n) (Fin n) E) j k) (by
      have : T * (1 - P * T) = 0 := by
        rw [Matrix.mul_sub, ← Matrix.mul_assoc, hT, Matrix.mul_one, Matrix.one_mul, sub_self]
      funext j; exact congrFun (congrFun this j) k)
    have h2 : (1 - (C * L).map φ) * C.map φ = 0 := by
      rw [Matrix.sub_mul, Matrix.map_mul, Matrix.mul_assoc, hL', Matrix.mul_one, Matrix.one_mul, sub_self]
    have h3 := congrArg ((1 - (C * L).map φ) *ᵥ ·) ha
    simp only [Matrix.mulVec_mulVec, h2, Matrix.zero_mulVec] at h3
    rw [e1]
    exact congrFun h3 i
  · intro h x hx
    refine ⟨(L.map φ * m) *ᵥ fun i => φ (x i), ?_⟩
    have h1 : (T.map φ) *ᵥ (fun i => φ (x i)) = 0 := by
      funext i
      have := RingHom.map_mulVec φ T x i
      rw [hx] at this
      simpa [Function.comp_def] using this.symm
    have h2 := congrArg (· *ᵥ fun i => φ (x i)) h
    simp only [Matrix.zero_mulVec] at h2
    rw [← Matrix.mulVec_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.map_mul (L := P),
      ← Matrix.mulVec_mulVec _ (P.map φ), h1, Matrix.mulVec_zero, sub_zero, Matrix.sub_mul, Matrix.one_mul,
      Matrix.sub_mulVec, sub_eq_zero, Matrix.map_mul, Matrix.mul_assoc] at h2
    rw [h2, Matrix.mulVec_mulVec]

omit [NumberField E] in
theorem idemA_complete (C : Matrix (Fin n) (Fin r) E) (L : Matrix (Fin r) (Fin n) E) (hL : L * C = 1)
    (h0 : cT (σ : E →+* E) C * J * C = 0) (hLL : L * J⁻¹ * cT (σ : E →+* E) L = 0) :
    CompleteOrthogonalIdempotents (fam (adjA σ J) (idemA C L)) := by
  have e : ∀ j : Fin r, J⁻¹ * cT (σ : E →+* E) (C * single j j (1 : E) * L) * J =
      J⁻¹ * cT (σ : E →+* E) L * cT (σ : E →+* E) (single j j (1 : E)) * (cT (σ : E →+* E) C * J) := fun j => by
    rw [cT_mul, cT_mul]; simp only [Matrix.mul_assoc]
  have e2 : ∀ i j : Fin r, C * single i i (1 : E) * L * (C * single j j (1 : E) * L) =
      C * (single i i (1 : E) * single j j (1 : E)) * L := fun i j => by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc L C, hL, Matrix.one_mul]
  refine fam_complete (adjA_mul hJ) ⟨fun j => ?_, fun i j hij => ?_⟩ (fun i j => ?_) (fun i j => ?_)
  · show _ * _ = _
    rw [idemA, ← Matrix.map_mul, e2, Matrix.single_mul_single_same, one_mul]
  · show _ * _ = _
    rw [idemA, idemA, ← Matrix.map_mul, e2, Matrix.single_mul_single_of_ne (h := hij)]
    simp
  · rw [idemA, idemA, adjA_map, e, ← Matrix.map_mul]
    simp only [Matrix.mul_assoc] at hLL ⊢
    rw [← Matrix.mul_assoc J⁻¹, ← Matrix.mul_assoc L, hLL]
    simp
  · rw [idemA, idemA, adjA_map, e, ← Matrix.map_mul]
    simp only [Matrix.mul_assoc] at h0 ⊢
    rw [← Matrix.mul_assoc J C, ← Matrix.mul_assoc (cT _ C), h0]
    simp

variable (hσ : ∀ x, σ (σ x) = x)
include hσ

omit [NumberField E] in
theorem adjA_adjA (X : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) : adjA σ J (adjA σ J X) = X := by
  have h : cT (sigR (AF F) σ) (cT (sigR (AF F) σ) X) = X := by
    ext i j
    show sigR (AF F) σ (sigR (AF F) σ (X i j)) = X i j
    induction X i j using TensorProduct.induction_on with
    | zero => simp
    | tmul a x => exact congrArg (a ⊗ₜ[F] ·) (hσ x)
    | add x y hx hy => simp only [map_add, hx, hy]
  simp only [adjA_apply, cT_mul, GlobalTheory.AutFunCounterexample.cT_map_gen, cT_form hJ, cT_form_inv hJ, h, Matrix.mul_assoc]
  rw [inv_mul_form hJ, Matrix.mul_one, ← Matrix.mul_assoc, inv_mul_form hJ, Matrix.one_mul]

omit [NumberField F] in

theorem exists_dualCols {C : Matrix (Fin n) (Fin r) E} (hC : IsIsoCols σ J C) :
    ∃ L : Matrix (Fin r) (Fin n) E, L * C = 1 ∧ L * J⁻¹ * cT (σ : E →+* E) L = 0 := by
  obtain ⟨hC, h0⟩ := hC
  have cc : ∀ {m p : Type} (A : Matrix m p E), cT (σ : E →+* E) (cT (σ : E →+* E) A) = A := fun A =>
    Matrix.ext fun i j => hσ _
  obtain ⟨l, hl⟩ := LinearMap.exists_leftInverse_of_injective C.mulVecLin
    (LinearMap.ker_eq_bot.2 (Matrix.mulVec_injective_iff.2 hC))
  obtain ⟨L, hL⟩ : ∃ L : Matrix (Fin r) (Fin n) E, L * C = 1 :=
    ⟨LinearMap.toMatrix' l, by
      apply Matrix.toLin'.injective
      rw [Matrix.toLin'_mul, Matrix.toLin'_toMatrix', Matrix.toLin'_one]; exact hl⟩
  set c := cT (m := Fin n) (p := Fin r) (σ : E →+* E) C with hcd
  set d := cT (σ : E →+* E) L with hd
  set s := L * J⁻¹ * d with hs
  have hu := det_isUnit hJ
  have hcd1 : c * d = 1 := by rw [hcd, hd, ← cT_mul, hL, cT_one]
  have hss : cT (σ : E →+* E) s = s := by
    rw [hs, cT_mul, cT_mul, hd, cc, cT_form_inv hJ, Matrix.mul_assoc]
  refine ⟨L - (1 / 2 : E) • (s * (c * J)), ?_, ?_⟩
  · rw [Matrix.sub_mul, Matrix.smul_mul, Matrix.mul_assoc, h0, hL]; simp
  · have e : cT (σ : E →+* E) (L - (1 / 2 : E) • (s * (c * J))) = d - (1 / 2 : E) • (J * C * s) := by
      have : J * C * s = cT (σ : E →+* E) (s * (c * J)) := by
        rw [cT_mul, cT_mul, hss, cT_form hJ, hcd, cc]
      rw [this, hd]
      generalize s * (c * J) = X
      ext i j
      simp [cT, map_ofNat]
    have e1 : L * J⁻¹ * (J * C * s) = s := by
      rw [← Matrix.mul_assoc _ (J * C), ← Matrix.mul_assoc _ J,
        Matrix.nonsing_inv_mul_cancel_right _ _ hu, hL, Matrix.one_mul]
    have e2 : s * (c * J) * J⁻¹ = s * c := by
      rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_right _ _ hu]
    have e3 : s * c * (J * C * s) = 0 := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc c, ← Matrix.mul_assoc c, h0]; simp
    rw [e, Matrix.sub_mul, Matrix.smul_mul, e2, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.mul_smul, e1,
      Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, e3, Matrix.mul_assoc s, hcd1, ← hs, Matrix.mul_one]
    module

theorem mem_unipSet_iff (C : Matrix (Fin n) (Fin r) E) (L : Matrix (Fin r) (Fin n) E) (hL : L * C = 1)
    (h0 : cT (σ : E →+* E) C * J * C = 0) (hLL : L * J⁻¹ * cT (σ : E →+* E) L = 0)
    {d : Fin r → ℕ} {M : ℕ} (hd : ∀ j, d j < M) (g : GAd σ J) :
    g ∈ unipSet σ J C d ↔ (matHom _ σ J g).1 - 1 ∈ raise (fam (adjA σ J) (idemA C L)) (wt d M) 0 := by
  rw [mem_raise_fam (adjA_mul hJ) (adjA_adjA hJ hσ) (idemA_complete hJ C L hL h0 hLL) hd, sum_idemA,
    ← perp_iff_idemA hJ C L hL, map_sub, adjA_mat hJ, GlobalTheory.TwoStepUnipotent.st_one (adjA_mul hJ) (adjA_adjA hJ hσ)]
  have hinv : (matHom _ σ J g⁻¹).1 * (matHom _ σ J g).1 = 1 := Units.inv_mul g.1
  unfold unipSet adMat
  rw [Set.mem_ofPred_eq]
  generalize (matHom _ σ J g⁻¹).1 = y at hinv ⊢
  generalize (matHom _ σ J g).1 = x at hinv ⊢
  set φ := inclR (F := F) (E := E) (AF F)
  have hL' : L.map φ * C.map φ = 1 := by rw [← Matrix.map_mul, hL, Matrix.map_one _ (map_zero _) (map_one _)]
  have sw : ∀ (m : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) (i j : Fin r),
      idemA C L j * m * idemA C L i = 0 ↔ (L.map φ * m * C.map φ : Matrix (Fin r) (Fin r) (AF F ⊗[F] E)) j i = 0 :=
    fun m i j => by rw [idemA_eq, idemA_eq]; exact sandwich_eq_zero hL' m i j
  simp only [sw]
  have co : ∀ (i : Fin r) (a : Fin r → AF F ⊗[F] E), (x - 1) *ᵥ (fun k => φ (C k i)) = C.map φ *ᵥ a →
      ∀ j, (L.map φ * (x - 1) * C.map φ : Matrix (Fin r) (Fin r) (AF F ⊗[F] E)) j i = a j := fun i a ha j => by
    have := congrArg (L.map φ *ᵥ ·) ha
    simp only [Matrix.mulVec_mulVec, hL', Matrix.one_mulVec] at this
    exact congrFun this j
  constructor
  · rintro ⟨h1, h2⟩
    have k : ∀ i j : Fin r, d i ≤ d j →
        (L.map φ * (x - 1) * C.map φ : Matrix (Fin r) (Fin r) (AF F ⊗[F] E)) j i = 0 := fun i j hij => by
      obtain ⟨a, ha, ha'⟩ := h1 i
      rw [co i a ha', ha j hij]
    refine ⟨h2, k, triangular_inv d _ _ ?_ k⟩
    have e : (x - 1) * C.map φ = C.map φ * (L.map φ * (x - 1) * C.map φ) := by
      ext k i
      obtain ⟨a, -, ha'⟩ := h1 i
      rw [Matrix.mul_apply (M := C.map φ)]
      simp only [co i a ha']
      exact congrFun ha' k
    have e' : y - 1 = -(x - 1) - (y - 1) * (x - 1) := by
      rw [sub_mul, mul_sub, hinv]; noncomm_ring
    rw [Matrix.mul_assoc (L.map φ * (y - 1)), ← e]
    conv_lhs => rw [e']
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]
  · rintro ⟨h2, h1, -⟩
    refine ⟨fun i => ?_, h2⟩
    obtain ⟨a, ha⟩ := h2 (fun k => C k i) (funext fun j => congrFun (congrFun h0 j) i)
    exact ⟨a, fun j hij => by rw [← co i a ha, h1 i j hij], ha⟩

theorem mem_unipFlag_iff_raise (C : Matrix (Fin n) (Fin r) E) (L : Matrix (Fin r) (Fin n) E) (hL : L * C = 1)
    (h0 : cT (σ : E →+* E) C * J * C = 0) (hLL : L * J⁻¹ * cT (σ : E →+* E) L = 0)
    {d : Fin r → ℕ} {M : ℕ} (hd : ∀ j, d j < M) (g : GAd σ J) :
    g ∈ unipFlag σ J C d ↔ (matHom _ σ J g).1 - 1 ∈ raise (fam (adjA σ J) (idemA C L)) (wt d M) 0 := by
  have he := idemA_complete hJ C L hL h0 hLL
  refine ⟨fun hg => ?_, fun hg => Subgroup.subset_closure ((mem_unipSet_iff hJ hσ C L hL h0 hLL hd g).2 hg)⟩
  induction hg using Subgroup.closure_induction with
  | mem x hx => exact (mem_unipSet_iff hJ hσ C L hL h0 hLL hd x).1 hx
  | one => exact (sub_self (1 : Matrix (Fin n) (Fin n) (AF F ⊗[F] E))).symm ▸ zero_mem _
  | mul x y _ _ hx hy =>
    rw [map_mul, Units.val_mul]
    generalize (matHom _ σ J x).1 = a at hx ⊢
    generalize (matHom _ σ J y).1 = b at hy ⊢
    have : a * b - 1 = (a - 1) * (b - 1) + (a - 1) + (b - 1) := by noncomm_ring
    rw [this]
    exact add_mem (add_mem (raise_le 0 (raise_mul he 0 hx hy)) hx) hy
  | inv x _ hx =>
    have := raise_st (adjA_mul hJ) (adjA_adjA hJ hσ)
      (fam_st (adjA_mul hJ) (adjA_adjA hJ hσ) (idemA (F := F) C L) d M) 0 hx
    rwa [map_sub, adjA_mat hJ, GlobalTheory.TwoStepUnipotent.st_one (adjA_mul hJ) (adjA_adjA hJ hσ)] at this

variable {C : Matrix (Fin n) (Fin r) E} (hC : IsIsoCols σ J C) (d : Fin r → ℕ)
include hC

theorem mem_unipFlag {g : GAd σ J} : g ∈ unipFlag σ J C d ↔ g ∈ unipSet σ J C d := by
  obtain ⟨L, hL, hLL⟩ := exists_dualCols hJ hσ hC
  obtain ⟨M, hM⟩ := (Set.finite_range d).bddAbove
  have hd : ∀ j, d j < M + 1 := fun j => Nat.lt_succ_of_le (hM ⟨j, rfl⟩)
  rw [mem_unipFlag_iff_raise hJ hσ C L hL hC.2 hLL hd, mem_unipSet_iff hJ hσ C L hL hC.2 hLL hd]

theorem unipFlag_le_parFlag : unipFlag σ J C d ≤ parFlag σ J C d := by
  have key : ∀ g ∈ unipFlag σ J C d, ∃ B : Matrix (Fin r) (Fin r) (AF F ⊗[F] E), B.BlockTriangular d ∧
      (matHom _ σ J g).1 * adMat F C = adMat F C * B := fun g hg => by
    obtain ⟨A, hA, e⟩ := lower_iff.1 ((mem_unipFlag hJ hσ hC d).1 hg).1
    refine ⟨A + 1, BlockTriangular.add (fun i j h => hA i j h.le) blockTriangular_one, ?_⟩
    rw [Matrix.mul_add, ← e, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_one, sub_add_cancel]
  exact fun g hg => ⟨key g hg, key _ (inv_mem hg)⟩

theorem conj_mem_unipFlag {p u : GAd σ J} (hp : p ∈ parFlag σ J C d) (hu : u ∈ unipFlag σ J C d) :
    p * u * p⁻¹ ∈ unipFlag σ J C d := by
  obtain ⟨L, hL, -⟩ := exists_dualCols hJ hσ hC
  obtain ⟨h1, h2⟩ := (mem_unipFlag hJ hσ hC d).1 hu
  obtain ⟨A, hA, eA⟩ := lower_iff.1 h1
  obtain ⟨⟨B, hB, eB⟩, B', hB', eB'⟩ := hp
  have hi : (matHom _ σ J p).1 * (matHom _ σ J p⁻¹).1 = 1 := Units.mul_inv p.1
  have e : (matHom _ σ J (p * u * p⁻¹)).1 - 1 =
      (matHom _ σ J p).1 * ((matHom _ σ J u).1 - 1) * (matHom _ σ J p⁻¹).1 := by
    rw [map_mul, map_mul, Units.val_mul, Units.val_mul, mul_sub, sub_mul, mul_one, hi]
  refine Subgroup.subset_closure ⟨lower_iff.2 ⟨B * A * B', fun j i hij => ?_, ?_⟩, fun x hx => ?_⟩
  · simp only [Matrix.mul_apply, Finset.sum_mul]
    refine Finset.sum_eq_zero fun l _ => Finset.sum_eq_zero fun k _ => ?_
    by_cases a : d k < d j
    · rw [hB a, zero_mul, zero_mul]
    by_cases b : d i < d l
    · rw [hB' b, mul_zero]
    rw [hA k l (by omega), mul_zero, zero_mul]
  · rw [e, Matrix.mul_assoc, eB', ← Matrix.mul_assoc, Matrix.mul_assoc _ _ (adMat F C), eA, ← Matrix.mul_assoc, eB]
    simp only [Matrix.mul_assoc]
  · have h3 := (perp_iff_idemA hJ C L hL _).1 h2
    set φ := inclR (F := F) (E := E) (AF F)
    set y := (matHom _ σ J p⁻¹).1 *ᵥ fun i => φ (x i) with hy
    have h4 : adMat F (cT (σ : E →+* E) C * J) *ᵥ y = 0 := by
      have : adMat F (cT (σ : E →+* E) C * J) *ᵥ (fun i => φ (x i)) = 0 := funext fun i => by
        have := RingHom.map_mulVec φ (cT (σ : E →+* E) C * J) x i
        rw [hx] at this
        simpa [Function.comp_def] using this.symm
      rw [hy, Matrix.mulVec_mulVec, form_mul_of_mul_cols eB, ← Matrix.mulVec_mulVec, this, Matrix.mulVec_zero]
    have h5 : adjA σ J ((C * L).map φ) *ᵥ y = 0 := by
      rw [adjA_map, cT_mul, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.map_mul, ← Matrix.mulVec_mulVec,
        h4, Matrix.mulVec_zero]
    have h6 := congrArg (· *ᵥ y) h3
    simp only [Matrix.zero_mulVec] at h6
    rw [← Matrix.mulVec_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, h5, sub_zero, Matrix.sub_mul, Matrix.one_mul,
      Matrix.sub_mulVec, sub_eq_zero, Matrix.map_mul, Matrix.mul_assoc, ← Matrix.mulVec_mulVec] at h6
    refine ⟨B *ᵥ ((L.map φ * ((matHom _ σ J u).1 - 1)) *ᵥ y), ?_⟩
    rw [e, ← Matrix.mulVec_mulVec, ← hy, ← Matrix.mulVec_mulVec, h6, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec _ (adMat F C),
      ← eB]

theorem isClosed_unipFlag : IsClosed (unipFlag σ J C d : Set (GAd σ J)) := by
  obtain ⟨L, hL, hLL⟩ := exists_dualCols hJ hσ hC
  obtain ⟨M, hM⟩ := (Set.finite_range d).bddAbove
  have hd : ∀ j, d j < M + 1 := fun j => Nat.lt_succ_of_le (hM ⟨j, rfl⟩)
  have : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  have : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _
  have : T2Space (AF F) := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  have : T2Space (AF F ⊗[F] E) := GlobalTheory.Doubling.t2Space_tensorProduct_finiteExtension
  have hm : Continuous fun g : GAd σ J => (matHom _ σ J g).1 := Units.continuous_val.comp continuous_subtype_val
  have e : (unipFlag σ J C d : Set (GAd σ J)) = ⋂ a, ⋂ b, ⋂ _ : wt d (M + 1) a ≤ wt d (M + 1) b + (0 : ℕ),
      {g | fam (adjA σ J) (idemA C L) a * ((matHom _ σ J g).1 - 1) * fam (adjA σ J) (idemA C L) b = 0} := by
    ext g
    simp only [Set.mem_iInter]
    exact mem_unipFlag_iff_raise hJ hσ C L hL hC.2 hLL hd g
  rw [e]
  exact isClosed_iInter fun a => isClosed_iInter fun b => isClosed_iInter fun _ =>
    isClosed_eq ((continuous_const.mul (hm.sub continuous_const)).mul continuous_const) continuous_const

theorem locallyCompact_unipFlag : LocallyCompactSpace (unipFlag σ J C d) :=
  (isClosed_unipFlag hJ hσ hC d).isClosedEmbedding_subtypeVal.locallyCompactSpace

theorem cocompact_unipFlag : GlobalTheory.Cusp.Cocompact (ratPts σ J) (unipFlag σ J C d) := by
  obtain ⟨L, hL, hLL⟩ := exists_dualCols hJ hσ hC
  obtain ⟨M, hd⟩ : ∃ M, ∀ j, d j < M := by
    obtain ⟨M, hM⟩ := (Set.finite_range d).bddAbove
    exact ⟨M + 1, fun j => Nat.lt_succ_of_le (hM ⟨j, rfl⟩)⟩
  obtain ⟨K, hK, hKs⟩ := GlobalTheory.AutFunCompare.tens_cocompact (F := F) (E := E)
  have : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  have : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _
  set φ := inclR (F := F) (E := E) (AF F) with hφ
  have he := idemA_complete hJ C L hL hC.2 hLL
  have hs := fam_st (adjA_mul hJ) (adjA_adjA hJ hσ) (idemA (F := F) C L) d M
  have hcont : Continuous (adjA σ J) := (continuous_const.matrix_mul (continuous_id.matrix_map
      (GlobalTheory.AdelicUnitaryTop.continuous_sigR (AF F) σ)).matrix_transpose).matrix_mul continuous_const
  have hst0 : ∀ x ∈ (φ.mapMatrix (m := Fin n)).range, adjA σ J x ∈ (φ.mapMatrix (m := Fin n)).range := by
    rintro _ ⟨X, rfl⟩; exact ⟨_, (adjA_map X).symm⟩
  have hmem := mem_unipFlag_iff_raise hJ hσ C L hL hC.2 hLL hd
  obtain ⟨K', hK', k1, k2⟩ := compact_mod_of_weights (st := adjA σ J) (w := wt d M)
    (φ.mapMatrix (m := Fin n)).range
    (Matrix.scalar _ (φ (1 / 2))) (Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => K) hcont
    (adjA_mul hJ) (adjA_adjA hJ hσ) hst0
    ⟨Matrix.scalar _ (1 / 2), by ext i j; by_cases h : i = j <;> simp [h]⟩
    (by rw [← map_add, ← map_add, add_halves, map_one, map_one])
    (fun x => (Matrix.scalar_commute _ (fun _ => Commute.all _ _) x).eq)
    (isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hK)
    (fun X => by
      choose y hy using fun i j => hKs (X i j)
      exact ⟨_, ⟨Matrix.of y, rfl⟩, fun i _ j _ => hy i j⟩) he
    (by
      have hu : ∀ j, idemA (F := F) C L j ∈ (φ.mapMatrix (m := Fin n)).range := fun j => ⟨_, rfl⟩
      have hv : ∀ j : Fin r ⊕ Fin r, Sum.elim (idemA (F := F) C L) (fun j => adjA σ J (idemA C L j)) j ∈
          (φ.mapMatrix (m := Fin n)).range := by
        rintro (j | j)
        exacts [hu j, hst0 _ (hu j)]
      rintro (_ | j)
      exacts [sub_mem (one_mem _) (sum_mem fun j _ => hv j), hv j]) hs
  let lift : ∀ x : Matrix (Fin n) (Fin n) (AF F ⊗[F] E), (adjA σ J x * x = 1 ∧ x * adjA σ J x = 1) ∧
      x - 1 ∈ raise (fam (adjA σ J) (idemA C L)) (wt d M) 0 → unipFlag σ J C d := fun x hx =>
    ⟨⟨⟨x, adjA σ J x, hx.1.2, hx.1.1⟩, (adjA_mul_self_iff hJ _).1 hx.1.1⟩, (hmem _).2 hx.2⟩
  let f : unipFlag σ J C d → _ := fun n => Units.embedProduct _ (matHom _ σ J n.1)
  have hf : Topology.IsInducing f :=
    Units.isInducing_embedProduct.comp (Topology.IsInducing.subtypeVal.comp Topology.IsInducing.subtypeVal)
  refine ⟨f ⁻¹' ((fun x => (x, MulOpposite.op (adjA σ J x))) '' K'),
    hf.isCompact_preimage' (hK'.image (continuous_id.prodMk (MulOpposite.continuous_op.comp hcont))) ?_, fun u => ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact ⟨lift x (k1 x hx), rfl⟩
  · have hu := (adjA_mul_self_iff hJ _).2 u.1.2
    obtain ⟨γ, ⟨a, ha⟩, p1, k, hk, p2⟩ := k2 (matHom _ σ J u.1).1 ⟨⟨hu, mul_eq_one_comm.1 hu⟩, (hmem _).1 u.2⟩
    obtain ⟨b, hb⟩ := hst0 γ ⟨a, ha⟩
    have e : u = lift γ p1 * lift k (k1 k hk) := Subtype.ext (Subtype.ext (Units.ext p2))
    refine ⟨(lift γ p1)⁻¹, inv_mem ?_, by rw [e, inv_mul_cancel_left]; exact ⟨k, hk, rfl⟩⟩
    have inj : Function.Injective (φ.mapMatrix (m := Fin n)) := Matrix.map_injective GlobalTheory.AutFunCompare.inclA_injective
    have hab : a * b = 1 := inj (by rw [map_mul, ha, hb, map_one, p1.1.2])
    refine ⟨⟨a, b, hab, mul_eq_one_comm.1 hab⟩, inj ?_, Units.ext ha⟩
    have hγ' : cT (sigR (AF F) σ) γ * J.map φ * γ = J.map φ := (lift γ p1).1.2
    rw [← ha] at hγ'
    rw [map_mul, map_mul]
    exact (congrArg (· * J.map φ * a.map φ) (GlobalTheory.AutFunCounterexample.cT_map_gen σ a).symm).trans hγ'

end Form

end GlobalTheory.UAut

end
