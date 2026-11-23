import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmoothVecLowKSub
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOnAtTau

noncomputable section

open Formalism.MainNotions.S Formalism.L2.Theta Formalism.QuantumDeterminants Matrix
open scoped ContDiff InnerProductSpace Topology

namespace GlobalTheory.SmVec

variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def lieG (G : Matrix (Fin n) (Fin n) ℂ) : Set (Matrix (Fin n) (Fin n) ℂ) := {X | Xᴴ * G + G * X = 0}

def trRep (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (P : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H) := fun g => σ (P * g * P⁻¹)

def word (π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (l : List (Matrix (Fin n) (Fin n) ℂ)) (w : H) : H :=
  l.foldr (dRep π) w

def smSub (G : Matrix (Fin n) (Fin n) ℂ) (π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) : Submodule ℂ H where
  carrier := {w | SmoothVec (lieG G) π w}
  add_mem' := fun h h' k Xs hX => by simpa only [map_add] using (h k Xs hX).add (h' k Xs hX)
  zero_mem' := fun k Xs _ => by simpa only [map_zero] using contDiff_const
  smul_mem' := fun c _ h k Xs hX => by simpa only [map_smul] using (h k Xs hX).const_smul c

def conjG (G Z : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ := -(G⁻¹ * Zᴴ * G)

def dRepC (G : Matrix (Fin n) (Fin n) ℂ) (π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (Z : Matrix (Fin n) (Fin n) ℂ)
    (w : H) : H :=
  dRep π ((1 / 2 : ℂ) • (Z + conjG G Z)) w + Complex.I • dRep π ((1 / (2 * Complex.I)) • (Z - conjG G Z)) w

def gelfH (G : Matrix (Fin n) (Fin n) ℂ) (π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (k : ℕ) (w : H) : H :=
  ∑ idx : Fin (k + 1) → Fin n,
    (List.ofFn fun a : Fin (k + 1) => dRepC G π (Matrix.single (idx a) (idx (a + 1)) 1)).foldr (fun f acc => f acc) w

variable {G : Matrix (Fin n) (Fin n) ℂ} {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem mem_smSub {w : H} : w ∈ smSub G π ↔ SmoothVec (lieG G) π w := Iff.rfl

@[simp] theorem word_nil (w : H) : word π [] w = w := rfl

@[simp] theorem word_cons (X : Matrix (Fin n) (Fin n) ℂ) (l : List (Matrix (Fin n) (Fin n) ℂ)) (w : H) :
    word π (X :: l) w = dRep π X (word π l w) := rfl

theorem word_append (l l' : List (Matrix (Fin n) (Fin n) ℂ)) (w : H) :
    word π (l ++ l') w = word π l (word π l' w) := List.foldr_append

theorem exp_mem_UH (hG : IsUnit G) {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ lieG G) (t : ℝ) :
    NormedSpace.exp (t • X) ∈ UH G := GlobalTheory.GardingVec.exp_mem hG hX t

theorem expProd_mem_UH (hG : IsUnit G) {k : ℕ} {Xs : Fin k → Matrix (Fin n) (Fin n) ℂ} (hX : ∀ i, Xs i ∈ lieG G)
    (t : Fin k → ℝ) : (List.ofFn fun i => NormedSpace.exp (t i • Xs i)).prod ∈ UH G :=
  GlobalTheory.GardingVec.list_prod_mem _ fun g hg => by
    obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hg
    exact exp_mem_UH hG (hX i) _

theorem isUnit_of_mem_UH (hG : IsUnit G) {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UH G) : IsUnit g := by
  have h : gᴴ * G * g = G := hg
  exact isUnit_of_mul_isUnit_right (h.symm ▸ hG : IsUnit (gᴴ * G * g))

theorem inv_mem_UH (hG : IsUnit G) {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UH G) : g⁻¹ ∈ UH G := by
  have h : gᴴ * G * g = G := hg
  have hd := (Matrix.isUnit_iff_isUnit_det g).1 (isUnit_of_mem_UH hG hg)
  show (g⁻¹)ᴴ * G * g⁻¹ = G
  calc (g⁻¹)ᴴ * G * g⁻¹ = (g⁻¹)ᴴ * (gᴴ * G * g) * g⁻¹ := by rw [h]
    _ = (g * g⁻¹)ᴴ * G * (g * g⁻¹) := by simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = G := by rw [mul_nonsing_inv _ hd]; simp

theorem conj_mem_lieG (hG : IsUnit G) {g X : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UH G) (hX : X ∈ lieG G) :
    g⁻¹ * X * g ∈ lieG G := by
  have h : gᴴ * G * g = G := hg
  have hX' : Xᴴ * G + G * X = 0 := hX
  have hd := (Matrix.isUnit_iff_isUnit_det g).1 (isUnit_of_mem_UH hG hg)
  have h1 : G * g⁻¹ = gᴴ * G := by
    conv_lhs => rw [← h]
    rw [Matrix.mul_assoc, mul_nonsing_inv _ hd, Matrix.mul_one]
  have h2 : (g⁻¹)ᴴ * G = G * g := by
    conv_lhs => rw [← h]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← conjTranspose_mul, mul_nonsing_inv _ hd]; simp
  show (g⁻¹ * X * g)ᴴ * G + G * (g⁻¹ * X * g) = 0
  calc (g⁻¹ * X * g)ᴴ * G + G * (g⁻¹ * X * g) = gᴴ * Xᴴ * ((g⁻¹)ᴴ * G) + (G * g⁻¹) * X * g := by
        simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = gᴴ * (Xᴴ * G + G * X) * g := by rw [h1, h2]; simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
    _ = 0 := by rw [hX']; simp

theorem rep_mul (hπ : IsURepOn (UH G) π) {g g' : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UH G) (hg' : g' ∈ UH G) (w : H) :
    π (g * g') w = π g (π g' w) := by rw [hπ.1.2 g hg g' hg']; rfl

theorem rep_one (hπ : IsURepOn (UH G) π) (w : H) : π 1 w = w := by rw [hπ.1.1]; rfl

theorem rep_inner (hπ : IsURepOn (UH G) π) {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UH G) (v w : H) :
    ⟪π g v, π g w⟫_ℂ = ⟪v, w⟫_ℂ :=
  LinearIsometry.inner_map_map (⟨(π g : H →ₗ[ℂ] H), hπ.2.1 g hg⟩ : H →ₗᵢ[ℂ] H) v w

theorem exp_conj_inv {g : Matrix (Fin n) (Fin n) ℂ} (hg : IsUnit g) (X : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) :
    NormedSpace.exp (t • (g⁻¹ * X * g)) = g⁻¹ * NormedSpace.exp (t • X) * g := by
  rw [← Matrix.exp_conj' _ _ hg, Matrix.mul_smul, Matrix.smul_mul]

theorem hasDerivAt_dRep {w : H} (hw : w ∈ smSub G π) {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ lieG G) :
    HasDerivAt (fun t : ℝ => π (NormedSpace.exp (t • X)) w) (dRep π X w) 0 := by
  have h1 := hw 1 (fun _ => X) (fun _ => hX)
  have h2 : ContDiff ℝ ∞ fun t : ℝ => fun _ : Fin 1 => t := contDiff_pi.2 fun _ => contDiff_id
  have h3 : ContDiff ℝ ∞ fun t : ℝ => π (NormedSpace.exp (t • X)) w := by
    simpa [Function.comp_def] using h1.comp h2
  exact (h3.differentiable (by simp) 0).hasDerivAt

theorem contDiff_deriv_snoc {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {k : ℕ} {F : (Fin (k + 1) → ℝ) → E}
    (hF : ContDiff ℝ ∞ F) : ContDiff ℝ ∞ fun t : Fin k → ℝ => deriv (fun s : ℝ => F (Fin.snoc t s)) 0 := by
  have hs : ContDiff ℝ ∞ fun p : (Fin k → ℝ) × ℝ => (Fin.snoc p.1 p.2 : Fin (k + 1) → ℝ) := by
    refine contDiff_pi.2 fun i => ?_
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa using contDiff_snd
    · simp only [Fin.snoc_castSucc]
      fun_prop
  have h1 : ContDiff ℝ ∞ (Function.uncurry fun (t : Fin k → ℝ) (s : ℝ) => F (Fin.snoc t s)) := hF.comp hs
  have h2 := ContDiff.fderiv (𝕜 := ℝ) (m := ∞) (n := ∞) (g := fun _ : Fin k → ℝ => (0 : ℝ)) h1 contDiff_const
    (le_of_eq rfl)
  exact h2.clm_apply (contDiff_const (c := (1 : ℝ)))

theorem dRep_mem (hG : IsUnit G) (hπ : IsURepOn (UH G) π) {w : H} (hw : w ∈ smSub G π)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ lieG G) : dRep π X w ∈ smSub G π := by
  intro k Xs hXs
  have h1 := hw (k + 1) (Fin.snoc Xs X) (fun i => by
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa using hX
    · simpa using hXs j)
  convert contDiff_deriv_snoc h1 using 2 with t
  have h2 := (((π _).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hasDerivAt_dRep hw hX) :
    HasDerivAt (fun s : ℝ => π (List.ofFn fun i => NormedSpace.exp (t i • Xs i)).prod
      (π (NormedSpace.exp (s • X)) w)) _ 0)
  refine h2.deriv.symm.trans ?_
  congr 1
  funext s
  show π _ (π _ w) = _
  rw [← rep_mul hπ (expProd_mem_UH hG hXs t) (exp_mem_UH hG hX s)]
  simp [List.ofFn_succ', -List.ofFn_succ]

theorem prod_conj {g : Matrix (Fin n) (Fin n) ℂ} (hg : IsUnit g) (l : List (Matrix (Fin n) (Fin n) ℂ)) :
    g * (l.map fun x => g⁻¹ * x * g).prod = l.prod * g := by
  have hd := (Matrix.isUnit_iff_isUnit_det g).1 hg
  induction l with
  | nil => simp
  | cons x l ih =>
    rw [List.map_cons, List.prod_cons, List.prod_cons, Matrix.mul_assoc x, ← ih]
    simp only [← Matrix.mul_assoc, mul_nonsing_inv _ hd, Matrix.one_mul]

theorem rep_mem (hG : IsUnit G) (hπ : IsURepOn (UH G) π) {w : H} (hw : w ∈ smSub G π)
    {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UH G) : π g w ∈ smSub G π := by
  intro k Xs hXs
  have hu := isUnit_of_mem_UH hG hg
  have hY : ∀ i, g⁻¹ * Xs i * g ∈ lieG G := fun i => conj_mem_lieG hG hg (hXs i)
  have h1 := ((π g).restrictScalars ℝ).contDiff.comp (hw k _ hY)
  convert h1 using 2 with t
  show _ = π g _
  rw [← rep_mul hπ (expProd_mem_UH hG hXs t) hg, ← rep_mul hπ hg (expProd_mem_UH hG hY t), ← prod_conj hu,
    List.map_ofFn]
  simp only [exp_conj_inv hu, Function.comp_def]

theorem dRep_add {v w : H} (hv : v ∈ smSub G π) (hw : w ∈ smSub G π) {X : Matrix (Fin n) (Fin n) ℂ}
    (hX : X ∈ lieG G) : dRep π X (v + w) = dRep π X v + dRep π X w := by
  have := (hasDerivAt_dRep hv hX).add (hasDerivAt_dRep hw hX)
  refine Eq.trans ?_ this.deriv
  unfold dRep
  congr 1
  funext t
  exact map_add _ _ _

theorem dRep_smul (c : ℂ) {w : H} (hw : w ∈ smSub G π) {X : Matrix (Fin n) (Fin n) ℂ}
    (hX : X ∈ lieG G) : dRep π X (c • w) = c • dRep π X w := by
  have := (hasDerivAt_dRep hw hX).const_smul c
  refine Eq.trans ?_ this.deriv
  unfold dRep
  congr 1
  funext t
  exact map_smul _ _ _

theorem dRep_rep (hG : IsUnit G) (hπ : IsURepOn (UH G) π) {w : H} (hw : w ∈ smSub G π)
    {g X : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UH G) (hX : X ∈ lieG G) :
    dRep π X (π g w) = π g (dRep π (g⁻¹ * X * g) w) := by
  have hu := isUnit_of_mem_UH hG hg
  have hd := (Matrix.isUnit_iff_isUnit_det g).1 hu
  have hY := conj_mem_lieG hG hg hX
  have h2 := (((π g).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hasDerivAt_dRep hw hY) :
    HasDerivAt (fun s : ℝ => π g (π (NormedSpace.exp (s • (g⁻¹ * X * g))) w)) _ 0)
  refine Eq.trans ?_ h2.deriv
  unfold dRep
  congr 1
  funext s
  show _ = π g (π _ w)
  rw [← rep_mul hπ hg (exp_mem_UH hG hY s), ← rep_mul hπ (exp_mem_UH hG hX s) hg, exp_conj_inv hu]
  simp only [← Matrix.mul_assoc, mul_nonsing_inv _ hd, Matrix.one_mul]

theorem inner_dRep (hG : IsUnit G) (hπ : IsURepOn (UH G) π) {v w : H} (hv : v ∈ smSub G π) (hw : w ∈ smSub G π)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ lieG G) : ⟪v, dRep π X w⟫_ℂ = -⟪dRep π X v, w⟫_ℂ := by
  have h := (hasDerivAt_dRep hv hX).inner ℂ (hasDerivAt_dRep hw hX)
  simp only [rep_inner hπ (exp_mem_UH hG hX _), zero_smul, NormedSpace.exp_zero, rep_one hπ] at h
  exact eq_neg_of_add_eq_zero_left (h.unique (hasDerivAt_const _ _))

theorem word_mem (hG : IsUnit G) (hπ : IsURepOn (UH G) π) {l : List (Matrix (Fin n) (Fin n) ℂ)}
    (hl : ∀ X ∈ l, X ∈ lieG G) {w : H} (hw : w ∈ smSub G π) : word π l w ∈ smSub G π := by
  induction l with
  | nil => exact hw
  | cons X l ih => exact dRep_mem hG hπ (ih fun Y hY => hl Y (by simp [hY])) (hl X (by simp))

theorem word_add (hG : IsUnit G) (hπ : IsURepOn (UH G) π) {l : List (Matrix (Fin n) (Fin n) ℂ)}
    (hl : ∀ X ∈ l, X ∈ lieG G) {v w : H} (hv : v ∈ smSub G π) (hw : w ∈ smSub G π) :
    word π l (v + w) = word π l v + word π l w := by
  induction l with
  | nil => rfl
  | cons X l ih =>
    have hl' : ∀ Y ∈ l, Y ∈ lieG G := fun Y hY => hl Y (by simp [hY])
    rw [word_cons, ih hl', dRep_add (word_mem hG hπ hl' hv) (word_mem hG hπ hl' hw) (hl X (by simp))]
    rfl

theorem word_smul (hG : IsUnit G) (hπ : IsURepOn (UH G) π) {l : List (Matrix (Fin n) (Fin n) ℂ)}
    (hl : ∀ X ∈ l, X ∈ lieG G) (c : ℂ) {w : H} (hw : w ∈ smSub G π) : word π l (c • w) = c • word π l w := by
  induction l with
  | nil => rfl
  | cons X l ih =>
    have hl' : ∀ Y ∈ l, Y ∈ lieG G := fun Y hY => hl Y (by simp [hY])
    rw [word_cons, ih hl', dRep_smul c (word_mem hG hπ hl' hw) (hl X (by simp))]
    rfl

theorem word_adjoint (hG : IsUnit G) (hπ : IsURepOn (UH G) π) {l : List (Matrix (Fin n) (Fin n) ℂ)}
    (hl : ∀ X ∈ l, X ∈ lieG G) {u : H} (hu : u ∈ smSub G π) :
    ∃ u' ∈ smSub G π, ∀ w ∈ smSub G π, ⟪u, word π l w⟫_ℂ = ⟪u', w⟫_ℂ := by
  induction l generalizing u with
  | nil => exact ⟨u, hu, fun _ _ => rfl⟩
  | cons X l ih =>
    have hl' : ∀ Y ∈ l, Y ∈ lieG G := fun Y hY => hl Y (by simp [hY])
    have hX := hl X (by simp)
    obtain ⟨u', h1, h2⟩ := ih hl' (dRep_mem hG hπ hu hX)
    refine ⟨-u', neg_mem h1, fun w hw => ?_⟩
    rw [word_cons, inner_dRep hG hπ hu (word_mem hG hπ hl' hw) hX, h2 w hw, inner_neg_left]

theorem parts_mem (hG : IsUnit G) (hh : Gᴴ = G) (Z : Matrix (Fin n) (Fin n) ℂ) :
    (1 / 2 : ℂ) • (Z + conjG G Z) ∈ lieG G ∧ (1 / (2 * Complex.I)) • (Z - conjG G Z) ∈ lieG G := by
  have hd := (Matrix.isUnit_iff_isUnit_det G).1 hG
  have h1 : G * conjG G Z = -(Zᴴ * G) := by
    simp only [conjG, Matrix.mul_neg, ← Matrix.mul_assoc, mul_nonsing_inv _ hd, Matrix.one_mul]
  have h2 : (conjG G Z)ᴴ * G = -(G * Z) := by
    have := congrArg conjTranspose h1
    rwa [conjTranspose_mul, conjTranspose_neg, conjTranspose_mul, conjTranspose_conjTranspose, hh] at this
  constructor
  · show _ + _ = 0
    rw [conjTranspose_smul, conjTranspose_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul, Matrix.mul_add, h1, h2]
    have : star (1 / 2 : ℂ) = 1 / 2 := by simp
    rw [this, ← smul_add]; simp
  · show _ + _ = 0
    rw [conjTranspose_smul, conjTranspose_sub, Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_mul, Matrix.mul_sub, h1, h2]
    have : star (1 / (2 * Complex.I) : ℂ) = -(1 / (2 * Complex.I)) := by simp [div_neg]
    rw [this]; module

theorem dRepC_mem (hG : IsUnit G) (hh : Gᴴ = G) (hπ : IsURepOn (UH G) π) (Z : Matrix (Fin n) (Fin n) ℂ) {w : H}
    (hw : w ∈ smSub G π) : dRepC G π Z w ∈ smSub G π :=
  add_mem (dRep_mem hG hπ hw (parts_mem hG hh Z).1) ((smSub G π).smul_mem _ (dRep_mem hG hπ hw (parts_mem hG hh Z).2))

section Frame

variable {ε : Fin n → Bool} {P : Matrix (Fin n) (Fin n) ℂ} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem gram_unit (hP : IsUnit P) (h : Pᴴ * Formalism.REAL.Jm ε * P = G) : IsUnit G := by
  rw [← h]
  exact (((Matrix.isUnit_conjTranspose _).2 hP).mul (IsUnit.of_mul_eq_one _ (Formalism.REAL.Jm_mul_self ε))).mul hP

theorem gram_herm (h : Pᴴ * Formalism.REAL.Jm ε * P = G) : Gᴴ = G := by
  rw [← h]
  simp only [conjTranspose_mul, conjTranspose_conjTranspose, Formalism.REAL.Jm_conjTranspose, Matrix.mul_assoc]

theorem conj_mem_UJ (hP : IsUnit P) (h : Pᴴ * Formalism.REAL.Jm ε * P = G) {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UH G) :
    P * g * P⁻¹ ∈ UJset ε := GlobalTheory.GardingVec.conj_mem hP h hg

theorem conj_mem_UH (hP : IsUnit P) (h : Pᴴ * Formalism.REAL.Jm ε * P = G) {g : Matrix (Fin n) (Fin n) ℂ}
    (hg : g ∈ UJset ε) : P⁻¹ * g * P ∈ UH G := by
  have hd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).1 hP
  have hk : gᴴ * Formalism.REAL.Jm ε * g = Formalism.REAL.Jm ε := hg
  have h1 : (P⁻¹)ᴴ * Pᴴ = 1 := by rw [← conjTranspose_mul, mul_nonsing_inv _ hd, conjTranspose_one]
  change (P⁻¹ * g * P)ᴴ * G * (P⁻¹ * g * P) = G
  calc (P⁻¹ * g * P)ᴴ * G * (P⁻¹ * g * P)
      = Pᴴ * (gᴴ * ((P⁻¹)ᴴ * Pᴴ) * Formalism.REAL.Jm ε * (P * P⁻¹) * g) * P := by
        rw [← h]; simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = G := by rw [h1, mul_nonsing_inv _ hd, Matrix.mul_one, Matrix.mul_one, hk, h]

theorem trRep_conj (hP : IsUnit P) (g : Matrix (Fin n) (Fin n) ℂ) : trRep σ P (P⁻¹ * g * P) = σ g := by
  have hd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).1 hP
  unfold trRep
  congr 1
  simp only [← Matrix.mul_assoc, mul_nonsing_inv _ hd, Matrix.one_mul]
  rw [Matrix.mul_assoc, mul_nonsing_inv _ hd, Matrix.mul_one]

theorem isURepOn_trRep (hP : IsUnit P) (h : Pᴴ * Formalism.REAL.Jm ε * P = G) (hσ : IsURepOn (UJset ε) σ) :
    IsURepOn (UH G) (trRep σ P) := by
  have hd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).1 hP
  refine ⟨⟨?_, fun a ha b hb => ?_⟩, fun g hg v => hσ.2.1 _ (conj_mem_UJ hP h hg) v, fun v => ?_⟩
  · unfold trRep
    rw [Matrix.mul_one, mul_nonsing_inv _ hd, hσ.1.1]
  · unfold trRep
    rw [← hσ.1.2 _ (conj_mem_UJ hP h ha) _ (conj_mem_UJ hP h hb)]
    congr 1
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc P⁻¹, nonsing_inv_mul _ hd, Matrix.one_mul]
  · exact (hσ.2.2 v).comp ((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const).continuousOn
      fun g hg => conj_mem_UJ hP h hg

theorem isIrredOn_trRep (hP : IsUnit P) (h : Pᴴ * Formalism.REAL.Jm ε * P = G) (hσ : IsIrredOn (UJset ε) σ) :
    IsIrredOn (UH G) (trRep σ P) := fun S hS hst => hσ S hS fun g hg v hv => by
  rw [← trRep_conj (σ := σ) hP g]
  exact hst _ (conj_mem_UH hP h hg) v hv

theorem sigma_mem (hP : IsUnit P) (h : Pᴴ * Formalism.REAL.Jm ε * P = G) (hσ : IsURepOn (UJset ε) σ) {w : H}
    (hw : w ∈ smSub G (trRep σ P)) {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UJset ε) :
    σ g w ∈ smSub G (trRep σ P) := by
  rw [← trRep_conj (σ := σ) hP g]
  exact rep_mem (gram_unit hP h) (isURepOn_trRep hP h hσ) hw (conj_mem_UH hP h hg)

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra in

theorem garding_mem [CompleteSpace H] (hP : IsUnit P) (h : Pᴴ * Formalism.REAL.Jm ε * P = G) (hσ : IsURepOn (UJset ε) σ)
    {φ : Matrix (Fin n) (Fin n) ℂ → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) (w : H) :
    GlobalTheory.LowTypeRestriction.garding hσ hφ.continuous hφc w ∈ smSub G (trRep σ P) := fun k Xs hX =>
  GlobalTheory.LowTypeRestriction.contDiff_garding hσ hφ hφc w k _
    ((contDiff_const.mul (GlobalTheory.GardingVec.contDiff_expProd Xs)).mul contDiff_const) fun t =>
    conj_mem_UJ hP h (expProd_mem_UH (gram_unit hP h) hX t)

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra in

def IsTest (φ : Matrix (Fin n) (Fin n) ℂ → ℝ) : Prop := ContDiff ℝ ∞ φ ∧ HasCompactSupport φ

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra in
theorem IsTest.continuous {φ : Matrix (Fin n) (Fin n) ℂ → ℝ} (h : IsTest φ) : Continuous φ := h.1.continuous

def gard (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (φ : Matrix (Fin n) (Fin n) ℂ → ℝ) (w : H) :
    H :=
  ∫ g : Formalism.REAL.UJ ε, φ (umat g) • σ (umat g) w ∂(Formalism.REAL.muG ε)

theorem gard_eq (hσ : IsURepOn (UJset ε) σ) {φ : Matrix (Fin n) (Fin n) ℂ → ℝ} (hφ : IsTest φ) (w : H) :
    gard ε σ φ w = GlobalTheory.LowTypeRestriction.garding hσ hφ.continuous hφ.2 w := rfl

theorem gard_mem [CompleteSpace H] (hP : IsUnit P) (h : Pᴴ * Formalism.REAL.Jm ε * P = G) (hσ : IsURepOn (UJset ε) σ)
    {φ : Matrix (Fin n) (Fin n) ℂ → ℝ} (hφ : IsTest φ) (w : H) : gard ε σ φ w ∈ smSub G (trRep σ P) :=
  garding_mem hP h hσ hφ.1 hφ.2 w

theorem continuous_umat : Continuous fun g : Formalism.REAL.UJ ε => umat g := (Formalism.REAL.isClosedEmbeddingMatrix n ε).1.continuous

theorem IsTest.integrable {φ : Matrix (Fin n) (Fin n) ℂ → ℝ} (hφ : IsTest φ) {E : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {F : Formalism.REAL.UJ ε → E} (hF : Continuous F) :
    MeasureTheory.Integrable (fun g : Formalism.REAL.UJ ε => φ (umat g) • F g) (Formalism.REAL.muG ε) :=
  ((hφ.continuous.comp continuous_umat).smul hF).integrable_of_hasCompactSupport
    (hφ.2.comp_isClosedEmbedding (Formalism.REAL.isClosedEmbeddingMatrix n ε).1).smul_right

theorem continuous_orbit (hσ : IsURepOn (UJset ε) σ) (w : H) : Continuous fun g : Formalism.REAL.UJ ε => σ (umat g) w :=
  (hσ.2.2 w).comp_continuous continuous_umat fun g => g.2

theorem norm_gard_le (hσ : IsURepOn (UJset ε) σ) (φ : Matrix (Fin n) (Fin n) ℂ → ℝ) (w : H) :
    ‖gard ε σ φ w‖ ≤ (∫ g : Formalism.REAL.UJ ε, |φ (umat g)| ∂(Formalism.REAL.muG ε)) * ‖w‖ := by
  refine (MeasureTheory.norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  rw [← MeasureTheory.integral_mul_const]
  congr 1
  funext g
  rw [norm_smul, hσ.2.1 _ g.2, Real.norm_eq_abs]

open MeasureTheory in

theorem eq_zero_of_forall_test {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {F : Formalism.REAL.UJ ε → E} (hF : Continuous F)
    (h : ∀ φ, IsTest φ → ∫ g : Formalism.REAL.UJ ε, φ (umat g) • F g ∂(Formalism.REAL.muG ε) = 0) : F 1 = 0 := by
  by_contra hw
  have hwpos : 0 < ‖F 1‖ := norm_pos_iff.2 hw
  obtain ⟨hemb, -⟩ := Formalism.REAL.isClosedEmbeddingMatrix n ε
  have hnb : {g | ‖F g - F 1‖ < ‖F 1‖ / 2} ∈ 𝓝 (1 : Formalism.REAL.UJ ε) := by
    have := hF.continuousAt (x := 1) (Metric.ball_mem_nhds _ (half_pos hwpos))
    simpa [Set.preimage, dist_eq_norm] using this
  rw [hemb.isInducing.nhds_eq_comap] at hnb
  obtain ⟨U, hU, hUs⟩ := hnb
  obtain ⟨φ, hφ, hφc, hφU, hφ0, hφ1, -⟩ := GlobalTheory.LowTypeRestriction.exists_bump hU
  have hT : IsTest φ := ⟨hφ, hφc⟩
  have hint := hT.integrable hF
  have h0 := h φ hT
  set μ := Formalism.REAL.muG ε
  have hψ : Continuous fun g : Formalism.REAL.UJ ε => φ (umat g) := hT.continuous.comp continuous_umat
  have hψc : HasCompactSupport fun g : Formalism.REAL.UJ ε => φ (umat g) := hφc.comp_isClosedEmbedding hemb
  have hψi : Integrable (fun g : Formalism.REAL.UJ ε => φ (umat g)) μ := hψ.integrable_of_hasCompactSupport hψc
  have hpos : 0 < ∫ g : Formalism.REAL.UJ ε, φ (umat g) ∂μ :=
    hψ.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := 1) hψc (fun g => hφ0 _)
      (by show φ 1 ≠ 0; rw [hφ1]; exact one_ne_zero)
  have e1 : ∫ g : Formalism.REAL.UJ ε, (φ (umat g) • F g - φ (umat g) • F 1) ∂μ
      = -((∫ g : Formalism.REAL.UJ ε, φ (umat g) ∂μ) • F 1) := by
    rw [integral_sub hint (hψi.smul_const _), h0, integral_smul_const, zero_sub]
  have e2 : ‖∫ g : Formalism.REAL.UJ ε, (φ (umat g) • F g - φ (umat g) • F 1) ∂μ‖
      ≤ ∫ g : Formalism.REAL.UJ ε, φ (umat g) * (‖F 1‖ / 2) ∂μ := by
    refine norm_integral_le_of_norm_le (hψi.mul_const _) (Filter.Eventually.of_forall fun g => ?_)
    rw [← smul_sub, norm_smul, Real.norm_of_nonneg (hφ0 _)]
    by_cases hg : φ (umat g) = 0
    · simp [hg]
    · exact mul_le_mul_of_nonneg_left (le_of_lt (hUs (hφU _ hg))) (hφ0 _)
  rw [e1, norm_neg, norm_smul, Real.norm_of_nonneg hpos.le, integral_mul_const] at e2
  nlinarith [mul_pos hpos hwpos]

theorem inner_gard [CompleteSpace H] (hσ : IsURepOn (UJset ε) σ) {φ : Matrix (Fin n) (Fin n) ℂ → ℝ} (hφ : IsTest φ)
    (y w : H) :
    ⟪y, gard ε σ φ w⟫_ℂ = ∫ g : Formalism.REAL.UJ ε, φ (umat g) • ⟪y, σ (umat g) w⟫_ℂ ∂(Formalism.REAL.muG ε) := by
  unfold gard
  rw [← integral_inner (hφ.integrable (continuous_orbit hσ w))]
  congr 1
  funext g
  rw [← Complex.coe_smul, inner_smul_right, Complex.real_smul]

theorem eq_zero_of_inner_gard [CompleteSpace H] (hσ : IsURepOn (UJset ε) σ) {y : H}
    (h : ∀ φ, IsTest φ → ∀ w, ⟪gard ε σ φ w, y⟫_ℂ = 0) : y = 0 := by
  have := eq_zero_of_forall_test (F := fun g : Formalism.REAL.UJ ε => ⟪y, σ (umat g) y⟫_ℂ)
    (continuous_const.inner (continuous_orbit hσ y)) fun φ hφ => by
      rw [← inner_gard hσ hφ, ← inner_conj_symm, h φ hφ, map_zero]
  have e : σ (umat (1 : Formalism.REAL.UJ ε)) y = y := by
    show σ 1 y = y
    rw [hσ.1.1]; rfl
  simp only [e] at this
  exact inner_self_eq_zero.1 this

theorem eq_zero_of_inner_smooth [CompleteSpace H] (hP : IsUnit P) (h : Pᴴ * Formalism.REAL.Jm ε * P = G)
    (hσ : IsURepOn (UJset ε) σ) {y : H} (hy : ∀ u ∈ smSub G (trRep σ P), ⟪u, y⟫_ℂ = 0) : y = 0 :=
  eq_zero_of_inner_gard hσ fun _ hφ w => hy _ (gard_mem hP h hσ hφ w)

theorem ext_inner_smooth [CompleteSpace H] (hP : IsUnit P) (h : Pᴴ * Formalism.REAL.Jm ε * P = G)
    (hσ : IsURepOn (UJset ε) σ) {y z : H} (hy : ∀ u ∈ smSub G (trRep σ P), ⟪u, y⟫_ℂ = ⟪u, z⟫_ℂ) : y = z :=
  sub_eq_zero.1 (eq_zero_of_inner_smooth hP h hσ fun u hu => by rw [inner_sub_right, hy u hu, sub_self])

end Frame

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.IndefR.Mult in

theorem sm_eq {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau) :
    M.sm τ = smSub (gramAt D V τ) (trRep (M.σ τ) (M.fr τ)) :=
  Submodule.span_eq (smSub (gramAt D V τ) (trRep (M.σ τ) (M.fr τ)))

end GlobalTheory.SmVec

end
