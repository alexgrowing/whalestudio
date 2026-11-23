import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmoothVecLowKSub
import Development.AbelianVarietyTheory.Counterexamples.RotationExamples.SobolevContinuityLowGeneration

noncomputable section

open MeasureTheory Matrix
open scoped ContDiff Topology InnerProductSpace

namespace GlobalTheory.LowTypeDetermined

open Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.GardingVec GlobalTheory.LowTypeRestriction

section
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {G : Matrix (Fin n) (Fin n) ℂ} {ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

def lie (G : Matrix (Fin n) (Fin n) ℂ) : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ) where
  carrier := {X | Xᴴ * G + G * X = 0}
  add_mem' := fun {X Y} hX hY => by
    have h1 : Xᴴ * G + G * X = 0 := hX
    have h2 : Yᴴ * G + G * Y = 0 := hY
    show (X + Y)ᴴ * G + G * (X + Y) = 0
    rw [conjTranspose_add, add_mul, mul_add, add_add_add_comm, h1, h2, add_zero]
  zero_mem' := by simp
  smul_mem' := fun c X hX => by
    have h1 : Xᴴ * G + G * X = 0 := hX
    show (c • X)ᴴ * G + G * (c • X) = 0
    rw [conjTranspose_smul, star_trivial, smul_mul_assoc, mul_smul_comm, ← smul_add, h1, smul_zero]

def smooth (G : Matrix (Fin n) (Fin n) ℂ) (ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) : Submodule ℂ H where
  carrier := {w | SmoothVec (lie G) ρ w}
  add_mem' := fun h h' k Xs hX => by simpa only [map_add] using (h k Xs hX).add (h' k Xs hX)
  zero_mem' := fun k Xs hX => by simpa only [map_zero] using contDiff_const
  smul_mem' := fun c _ h k Xs hX => by simpa only [map_smul] using (h k Xs hX).const_smul c

def smoothAll (G : Matrix (Fin n) (Fin n) ℂ) (ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) : Submodule ℂ H where
  carrier := {w | ∀ (k : ℕ) (x : (Fin k → ℝ) → Matrix (Fin n) (Fin n) ℂ), ContDiff ℝ ∞ x →
    (∀ t, x t ∈ Formalism.QuantumDeterminants.UH G) → ContDiff ℝ ∞ fun t => ρ (x t) w}
  add_mem' := fun h h' k x hx hG => by simpa only [map_add] using (h k x hx hG).add (h' k x hx hG)
  zero_mem' := fun k x hx hG => by simpa only [map_zero] using contDiff_const
  smul_mem' := fun c _ h k x hx hG => by simpa only [map_smul] using (h k x hx hG).const_smul c

theorem expProd_mem (hG : IsUnit G) {k : ℕ} {Xs : Fin k → Matrix (Fin n) (Fin n) ℂ} (hX : ∀ i, Xs i ∈ lie G)
    (t : Fin k → ℝ) : (List.ofFn fun i => NormedSpace.exp (t i • Xs i)).prod ∈ Formalism.QuantumDeterminants.UH G := by
  refine list_prod_mem _ fun g hg => ?_
  obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hg
  exact exp_mem hG (hX i) _

theorem smoothAll_le (hG : IsUnit G) : smoothAll G ρ ≤ smooth G ρ :=
  fun _ h k Xs hX => h k _ (contDiff_expProd Xs) (expProd_mem hG hX)

theorem hasDerivAt_dRep {w : H} (hw : w ∈ smooth G ρ) {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ lie G) :
    HasDerivAt (fun t : ℝ => ρ (NormedSpace.exp (t • X)) w) (dRep ρ X w) 0 := by
  have h1 := (hw 1 (fun _ => X) (fun _ => hX)).differentiable (by simp)
  have h2 : Differentiable ℝ fun t : ℝ => (fun _ : Fin 1 => t) := by fun_prop
  have h3 : Differentiable ℝ fun t : ℝ => ρ (NormedSpace.exp (t • X)) w := by
    simpa [Function.comp_def] using h1.comp h2
  exact (h3 0).hasDerivAt

theorem contDiff_deriv_snoc {k : ℕ} {F : (Fin (k + 1) → ℝ) → H} (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ fun t : Fin k → ℝ => deriv (fun s : ℝ => F (Fin.snoc t s)) 0 := by
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

theorem deriv_map (A : H →L[ℂ] H) {f : ℝ → H} {f' : H} (h : HasDerivAt f f' 0) :
    deriv (fun t => A (f t)) 0 = A f' :=
  ((A.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 h).deriv

theorem dRep_mem (hG : IsUnit G) (hρ : IsURepOn (Formalism.QuantumDeterminants.UH G) ρ) {w : H} (hw : w ∈ smooth G ρ)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ lie G) : dRep ρ X w ∈ smooth G ρ := by
  intro k Xs hXs
  have h1 := hw (k + 1) (Fin.snoc Xs X) (fun i => by
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa using hX
    · simpa using hXs j)
  convert contDiff_deriv_snoc h1 using 2 with t
  rw [← deriv_map _ (hasDerivAt_dRep hw hX)]
  congr 1
  funext s
  have e := hρ.1.2 _ (expProd_mem hG hXs t) _ (exp_mem hG hX s)
  simp only [List.ofFn_succ', Fin.snoc_castSucc, Fin.snoc_last, List.concat_eq_append, List.prod_append,
    List.prod_cons, List.prod_nil, mul_one]
  rw [e]; rfl

def dOp (hG : IsUnit G) (hρ : IsURepOn (Formalism.QuantumDeterminants.UH G) ρ) {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ lie G) :
    smooth G ρ →ₗ[ℂ] smooth G ρ where
  toFun w := ⟨dRep ρ X w, dRep_mem hG hρ w.2 hX⟩
  map_add' v w := Subtype.ext <| by
    have := ((hasDerivAt_dRep v.2 hX).add (hasDerivAt_dRep w.2 hX)).deriv
    show dRep ρ X ((v : H) + w) = dRep ρ X v + dRep ρ X w
    rw [← this]; unfold dRep; simp only [map_add]; rfl
  map_smul' c w := Subtype.ext <| by
    have := ((hasDerivAt_dRep w.2 hX).const_smul c).deriv
    show dRep ρ X (c • (w : H)) = c • dRep ρ X w
    rw [← this]; unfold dRep; simp only [map_smul]; rfl

theorem exists_word (hG : IsUnit G) (hρ : IsURepOn (Formalism.QuantumDeterminants.UH G) ρ) (l : List (Matrix (Fin n) (Fin n) ℂ))
    (hl : ∀ X ∈ l, X ∈ lie G) :
    ∃ L : smooth G ρ →ₗ[ℂ] smooth G ρ, ∀ w : smooth G ρ, (L w : H) = l.foldr (dRep ρ) w := by
  induction l with
  | nil => exact ⟨LinearMap.id, fun _ => rfl⟩
  | cons X l ih =>
    obtain ⟨L, hL⟩ := ih fun Y hY => hl Y (List.mem_cons_of_mem _ hY)
    exact ⟨dOp hG hρ (hl X List.mem_cons_self) ∘ₗ L, fun w => by rw [List.foldr_cons, ← hL]; rfl⟩

theorem word_mem (hG : IsUnit G) (hρ : IsURepOn (Formalism.QuantumDeterminants.UH G) ρ) (l : List (Matrix (Fin n) (Fin n) ℂ))
    (hl : ∀ X ∈ l, X ∈ lie G) {w : H} (hw : w ∈ smooth G ρ) : l.foldr (dRep ρ) w ∈ smooth G ρ := by
  obtain ⟨L, hL⟩ := exists_word hG hρ l hl
  rw [← hL ⟨w, hw⟩]; exact (L _).2

theorem inner_dRep (hG : IsUnit G) (hρ : IsURepOn (Formalism.QuantumDeterminants.UH G) ρ) {y w : H} (hy : y ∈ smooth G ρ)
    (hw : w ∈ smooth G ρ) {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ lie G) :
    ⟪y, dRep ρ X w⟫_ℂ = -⟪dRep ρ X y, w⟫_ℂ := by
  have h := (hasDerivAt_dRep hy hX).inner ℂ (hasDerivAt_dRep hw hX)
  have e : (fun t : ℝ => ⟪ρ (NormedSpace.exp (t • X)) y, ρ (NormedSpace.exp (t • X)) w⟫_ℂ) = fun _ => ⟪y, w⟫_ℂ := by
    funext t
    exact LinearIsometry.inner_map_map
      ⟨(ρ (NormedSpace.exp (t • X)) : H →ₗ[ℂ] H), hρ.2.1 _ (exp_mem hG hX t)⟩ y w
  rw [e] at h
  have h0 := h.unique (hasDerivAt_const _ _)
  simp only [zero_smul, NormedSpace.exp_zero, hρ.1.1, ContinuousLinearMap.one_apply] at h0
  exact eq_neg_of_add_eq_zero_left h0

theorem exists_adjoint (hG : IsUnit G) (hρ : IsURepOn (Formalism.QuantumDeterminants.UH G) ρ) (l : List (Matrix (Fin n) (Fin n) ℂ))
    (hl : ∀ X ∈ l, X ∈ lie G) : ∀ y ∈ smooth G ρ, ∃ y' : H, ∀ v ∈ smooth G ρ,
      ⟪y, l.foldr (dRep ρ) v⟫_ℂ = ⟪y', v⟫_ℂ := by
  induction l with
  | nil => exact fun y _ => ⟨y, fun _ _ => rfl⟩
  | cons X l ih =>
    intro y hy
    have hX := hl X List.mem_cons_self
    have hl' := fun Y hY => hl Y (List.mem_cons_of_mem _ hY)
    obtain ⟨y', h⟩ := ih hl' _ (dRep_mem hG hρ hy hX)
    refine ⟨-y', fun v hv => ?_⟩
    rw [List.foldr_cons, inner_dRep hG hρ hy (word_mem hG hρ l hl' hv) hX, h v hv, inner_neg_left]

theorem isUnit_of_mem (hG : IsUnit G) {h : Matrix (Fin n) (Fin n) ℂ} (hh : h ∈ Formalism.QuantumDeterminants.UH G) : IsUnit h := by
  have e : hᴴ * G * h = G := hh
  rw [← e] at hG
  exact isUnit_of_mul_isUnit_right hG

theorem inv_eq_of_mem (hG : IsUnit G) {h : Matrix (Fin n) (Fin n) ℂ} (hh : h ∈ Formalism.QuantumDeterminants.UH G) :
    h⁻¹ = G⁻¹ * hᴴ * G := by
  have e : hᴴ * G * h = G := hh
  refine Matrix.inv_eq_left_inv ?_
  rw [mul_assoc, mul_assoc, ← mul_assoc hᴴ, e, Matrix.nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).1 hG)]

theorem conj_mem_lie (hG : IsUnit G) {h X : Matrix (Fin n) (Fin n) ℂ} (hh : h ∈ Formalism.QuantumDeterminants.UH G) (hX : X ∈ lie G) :
    h⁻¹ * X * h ∈ lie G := by
  have e : hᴴ * G * h = G := hh
  have hd := (isUnit_iff_isUnit_det _).1 (isUnit_of_mem hG hh)
  have h1 : Xᴴ * G + G * X = 0 := hX
  have e1 : G * h⁻¹ = hᴴ * G := by
    conv_lhs => rw [← e]
    rw [mul_assoc, Matrix.mul_nonsing_inv _ hd, mul_one]
  have e2 : (h⁻¹)ᴴ * G = G * h := by
    conv_lhs => rw [← e]
    rw [← mul_assoc, ← mul_assoc, ← conjTranspose_mul, Matrix.mul_nonsing_inv _ hd, conjTranspose_one, one_mul]
  show (h⁻¹ * X * h)ᴴ * G + G * (h⁻¹ * X * h) = 0
  calc (h⁻¹ * X * h)ᴴ * G + G * (h⁻¹ * X * h) = hᴴ * Xᴴ * ((h⁻¹)ᴴ * G) + (G * h⁻¹) * X * h := by
        simp only [conjTranspose_mul, mul_assoc]
    _ = hᴴ * (Xᴴ * G + G * X) * h := by rw [e1, e2]; simp only [mul_add, add_mul, mul_assoc]
    _ = 0 := by rw [h1, mul_zero, zero_mul]

theorem exp_mul_eq {h : Matrix (Fin n) (Fin n) ℂ} (hu : IsUnit h) (X : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) :
    NormedSpace.exp (t • X) * h = h * NormedSpace.exp (t • (h⁻¹ * X * h)) := by
  have hd := (isUnit_iff_isUnit_det _).1 hu
  rw [← smul_mul_assoc, ← mul_smul_comm, Matrix.exp_conj' _ _ hu, ← mul_assoc, ← mul_assoc,
    Matrix.mul_nonsing_inv _ hd, one_mul]

theorem prod_mul_eq {k : ℕ} (h : Matrix (Fin n) (Fin n) ℂ) (a b : Fin k → Matrix (Fin n) (Fin n) ℂ)
    (e : ∀ i, a i * h = h * b i) : (List.ofFn a).prod * h = h * (List.ofFn b).prod := by
  induction k with
  | zero => simp
  | succ k ih =>
    simp only [List.ofFn_succ, List.prod_cons]
    rw [mul_assoc, ih _ _ fun i => e i.succ, ← mul_assoc, e 0, mul_assoc]

theorem translate_mem (hG : IsUnit G) (hρ : IsURepOn (Formalism.QuantumDeterminants.UH G) ρ) {h : Matrix (Fin n) (Fin n) ℂ}
    (hh : h ∈ Formalism.QuantumDeterminants.UH G) {w : H} (hw : w ∈ smooth G ρ) : ρ h w ∈ smooth G ρ := by
  intro k Xs hX
  have hX' := fun i => conj_mem_lie hG hh (hX i)
  have h1 := ((ρ h).restrictScalars ℝ).contDiff.comp (hw k _ hX')
  convert h1 using 2 with t
  have e1 := hρ.1.2 _ (expProd_mem hG hX t) _ hh
  have e2 := hρ.1.2 _ hh _ (expProd_mem hG hX' t)
  rw [prod_mul_eq h _ _ fun i => exp_mul_eq (isUnit_of_mem hG hh) (Xs i) (t i), e2] at e1
  exact (congrArg (fun A : H →L[ℂ] H => A w) e1).symm

theorem word_translate (hG : IsUnit G) (hρ : IsURepOn (Formalism.QuantumDeterminants.UH G) ρ) {h : Matrix (Fin n) (Fin n) ℂ}
    (hh : h ∈ Formalism.QuantumDeterminants.UH G) {w : H} (hw : w ∈ smooth G ρ) (l : List (Matrix (Fin n) (Fin n) ℂ))
    (hl : ∀ X ∈ l, X ∈ lie G) :
    l.foldr (dRep ρ) (ρ h w) = ρ h (l.foldr (fun X => dRep ρ (h⁻¹ * X * h)) w) := by
  induction l with
  | nil => rfl
  | cons X l ih =>
    have hX := hl X List.mem_cons_self
    have hl' := fun Y hY => hl Y (List.mem_cons_of_mem _ hY)
    have hX' := conj_mem_lie hG hh hX
    have hm : l.foldr (fun X => dRep ρ (h⁻¹ * X * h)) w ∈ smooth G ρ := by
      rw [← List.foldr_map (f := fun X => h⁻¹ * X * h) (g := dRep ρ)]
      refine word_mem hG hρ _ (fun Y hY => ?_) hw
      obtain ⟨Z, hZ, rfl⟩ := List.mem_map.1 hY
      exact conj_mem_lie hG hh (hl' Z hZ)
    rw [List.foldr_cons, List.foldr_cons, ih hl', ← deriv_map _ (hasDerivAt_dRep hm hX')]
    unfold dRep
    congr 1
    funext t
    have e1 := hρ.1.2 _ (exp_mem hG hX t) _ hh
    have e2 := hρ.1.2 _ hh _ (exp_mem hG hX' t)
    rw [exp_mul_eq (isUnit_of_mem hG hh), e2] at e1
    exact (congrArg (fun A : H →L[ℂ] H => A _) e1).symm

theorem dRep_eq_fderiv (hG : IsUnit G) {k : ℕ} {B : Fin k → Matrix (Fin n) (Fin n) ℂ} (hB : ∀ i, B i ∈ lie G)
    {y : H} (hy : y ∈ smoothAll G ρ) :
    ∃ A : (Fin k → ℝ) →L[ℝ] H, ∀ c : Fin k → ℝ, dRep ρ (∑ i, c i • B i) y = A c := by
  have h1 : ContDiff ℝ ∞ (NormedSpace.exp : Matrix (Fin n) (Fin n) ℂ → _) :=
    contDiff_iff_contDiffAt.2 fun x => (NormedSpace.exp_analytic (𝕂 := ℝ) x).contDiffAt
  have h2 : ContDiff ℝ ∞ fun t : Fin k → ℝ => ∑ i, t i • B i :=
    ContDiff.sum fun i _ => (contDiff_apply ℝ ℝ i).smul contDiff_const
  have h3 := hy k _ (h1.comp h2) fun t => by
    have := exp_mem hG ((lie G).sum_mem (t := Finset.univ) fun i _ => (lie G).smul_mem (t i) (hB i)) 1
    rwa [one_smul] at this
  have h4 := (h3.differentiable (by simp) 0).hasFDerivAt
  have h5 : ∀ c : Fin k → ℝ, HasDerivAt (fun s : ℝ => s • c) c 0 := fun c => by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const c
  refine ⟨_, fun c => Eq.trans ?_ (h4.comp_hasDerivAt_of_eq 0 (h5 c) (by simp)).deriv⟩
  unfold dRep
  congr 1
  funext s
  simp only [Function.comp, Finset.smul_sum, Pi.smul_apply, smul_eq_mul, mul_smul]

theorem dRep_sum_all (hG : IsUnit G) {k : ℕ} {B : Fin k → Matrix (Fin n) (Fin n) ℂ} (hB : ∀ i, B i ∈ lie G)
    {y : H} (hy : y ∈ smoothAll G ρ) (c : Fin k → ℝ) :
    dRep ρ (∑ i, c i • B i) y = ∑ i, c i • dRep ρ (B i) y := by
  obtain ⟨A, hA⟩ := dRep_eq_fderiv hG hB hy
  have e : ∀ i, dRep ρ (B i) y = A (Pi.single i 1) := fun i => by
    rw [← hA]
    congr 1
    simp [Pi.single_apply]
  simp only [hA, e, ← map_smul, ← map_sum]
  congr 1
  funext j
  simp [Pi.single_apply]

theorem dRep_sum (hG : IsUnit G) (hρ : IsURepOn (Formalism.QuantumDeterminants.UH G) ρ) (hd : Dense (smoothAll G ρ : Set H)) {k : ℕ}
    {B : Fin k → Matrix (Fin n) (Fin n) ℂ} (hB : ∀ i, B i ∈ lie G) {w : H} (hw : w ∈ smooth G ρ) (c : Fin k → ℝ) :
    dRep ρ (∑ i, c i • B i) w = ∑ i, (c i : ℂ) • dRep ρ (B i) w := by
  refine hd.eq_of_inner_right (𝕜 := ℂ) fun y hy => ?_
  have hy' := smoothAll_le hG hy
  rw [inner_dRep hG hρ hy' hw ((lie G).sum_mem fun i _ => (lie G).smul_mem (c i) (hB i)), dRep_sum_all hG hB hy,
    inner_sum, sum_inner, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_smul_right, inner_dRep hG hρ hy' hw (hB i), ← Complex.coe_smul, inner_smul_left, Complex.conj_ofReal,
    mul_neg]

theorem continuous_word (hG : IsUnit G) (hρ : IsURepOn (Formalism.QuantumDeterminants.UH G) ρ) (hd : Dense (smoothAll G ρ : Set H))
    {T α : Type} [TopologicalSpace T] (Y : α → T → Matrix (Fin n) (Fin n) ℂ) (l : List α)
    (hY : ∀ a ∈ l, Continuous (Y a) ∧ ∀ t, Y a t ∈ lie G) {w : H} (hw : w ∈ smooth G ρ) :
    ∃ v : T → smooth G ρ, (∀ t, (v t : H) = l.foldr (fun a => dRep ρ (Y a t)) w) ∧
      ∀ f : smooth G ρ →ₗ[ℂ] H, Continuous fun t => f (v t) := by
  induction l with
  | nil => exact ⟨fun _ => ⟨w, hw⟩, fun _ => rfl, fun _ => continuous_const⟩
  | cons a l ih =>
    obtain ⟨v, hv, hc⟩ := ih fun b hb => hY b (List.mem_cons_of_mem _ hb)
    obtain ⟨h1, h2⟩ := hY a List.mem_cons_self
    refine ⟨fun t => dOp hG hρ (h2 t) (v t), fun t => by rw [List.foldr_cons, ← hv]; rfl, fun f => ?_⟩
    let b := Module.finBasis ℝ (lie G)
    have e : ∀ t, dOp hG hρ (h2 t) (v t) = ∑ i, (b.coord i ⟨Y a t, h2 t⟩ : ℂ) • dOp hG hρ (b i).2 (v t) := by
      intro t
      apply Subtype.ext
      have e1 : Y a t = ∑ i, b.coord i ⟨Y a t, h2 t⟩ • (b i : Matrix (Fin n) (Fin n) ℂ) := by
        have := congrArg Subtype.val (b.sum_repr ⟨Y a t, h2 t⟩)
        rw [Submodule.coe_sum] at this
        exact this.symm
      have e2 := dRep_sum hG hρ hd (fun i => (b i).2) (v t).2 fun i => b.coord i ⟨Y a t, h2 t⟩
      rw [← e1] at e2
      rw [Submodule.coe_sum]
      exact e2
    simp only [e, map_sum, map_smul]
    refine continuous_finset_sum _ fun i _ => Continuous.smul ?_ (hc (f ∘ₗ dOp hG hρ (b i).2))
    exact Complex.continuous_ofReal.comp ((b.coord i).continuous_of_finiteDimensional.comp (h1.subtype_mk h2))

theorem continuous_word_orbit (hG : IsUnit G) (hρ : IsURepOn (Formalism.QuantumDeterminants.UH G) ρ)
    (hd : Dense (smoothAll G ρ : Set H)) {T : Type} [TopologicalSpace T] {a : T → Matrix (Fin n) (Fin n) ℂ}
    (ha : Continuous a) (haG : ∀ t, a t ∈ Formalism.QuantumDeterminants.UH G) (l : List (Matrix (Fin n) (Fin n) ℂ))
    (hl : ∀ X ∈ l, X ∈ lie G) {w : H} (hw : w ∈ smooth G ρ) :
    Continuous fun t => l.foldr (dRep ρ) (ρ (a t) w) := by
  have hi : Continuous fun t => (a t)⁻¹ := by
    simp only [fun t => inv_eq_of_mem hG (haG t)]
    exact (continuous_const.mul ha.matrix_conjTranspose).mul continuous_const
  obtain ⟨v, hv, hc⟩ := continuous_word hG hρ hd (fun X t => (a t)⁻¹ * X * a t) l
    (fun X hX => ⟨(hi.mul continuous_const).mul ha, fun t => conj_mem_lie hG (haG t) (hl X hX)⟩) hw
  have hv' : Continuous fun t => (v t : H) := hc (smooth G ρ).subtype
  simp only [fun t => word_translate hG hρ (haG t) hw l hl, ← hv]
  refine continuous_iff_continuousAt.2 fun t₀ => ?_
  have h1 : Continuous fun t => ρ (a t) (v t₀) := (hρ.2.2 _).comp_continuous ha haG
  have h2 : Filter.Tendsto (fun t => ρ (a t) (v t - v t₀)) (𝓝 t₀) (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simp only [fun t => hρ.2.1 _ (haG t)]
    exact tendsto_iff_norm_sub_tendsto_zero.1 (hv'.tendsto t₀)
  have h3 := h2.add (h1.tendsto t₀)
  simpa [ContinuousAt] using h3

theorem exists_factor (hG : IsUnit G) (hρ : IsURepOn (Formalism.QuantumDeterminants.UH G) ρ) {ℓ : H →ₗ[ℂ] ℂ}
    (hℓ : Sobolev₂ (lie G) ρ ℓ) :
    ∃ (m : ℕ) (S : Fin m → List (Matrix (Fin n) (Fin n) ℂ)) (Λ : Fin m → H →L[ℂ] ℂ),
      (∀ i, ∀ X ∈ S i, X ∈ lie G) ∧ ∀ w ∈ smooth G ρ, ℓ w = ∑ i, Λ i ((S i).foldr (dRep ρ) w) := by
  obtain ⟨S, C, hS, hC⟩ := hℓ
  let S' : Fin (S.length + 1) → List (Matrix (Fin n) (Fin n) ℂ) := Fin.cons [] S.get
  have hS' : ∀ i, ∀ X ∈ S' i, X ∈ lie G := fun i => by
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [S']
    · exact hS _ (List.get_mem _ _)
  choose L hL using fun i => exists_word hG hρ (S' i) (hS' i)
  let Φ : smooth G ρ →ₗ[ℂ] (Fin (S.length + 1) → H) := LinearMap.pi fun i => (smooth G ρ).subtype ∘ₗ L i
  have hΦ : ∀ w i, Φ w i = (S' i).foldr (dRep ρ) w := fun w i => hL i w
  let f : LinearMap.range Φ →ₗ[ℂ] ℂ := ℓ ∘ₗ LinearMap.proj 0 ∘ₗ (LinearMap.range Φ).subtype
  have hf : ∀ w, f ⟨Φ w, ⟨w, rfl⟩⟩ = ℓ w := fun w => congrArg ℓ (hΦ w 0)
  have hb : ∀ z, ‖f z‖ ≤ (|C| * S.length) * ‖z‖ := by
    rintro ⟨_, w, rfl⟩
    rw [hf]
    have h1 : (S.map fun l => ‖l.foldr (dRep ρ) (w : H)‖).sum ≤ S.length * ‖Φ w‖ := by
      have := List.sum_le_card_nsmul (S.map fun l => ‖l.foldr (dRep ρ) (w : H)‖) ‖Φ w‖ fun x hx => by
        obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hx
        obtain ⟨j, rfl⟩ := List.get_of_mem hl
        have := norm_le_pi_norm (Φ w) j.succ
        rwa [hΦ] at this
      simpa using this
    have h0 : 0 ≤ (S.map fun l => ‖l.foldr (dRep ρ) (w : H)‖).sum := List.sum_nonneg fun x hx => by
      obtain ⟨l, -, rfl⟩ := List.mem_map.1 hx
      exact norm_nonneg _
    calc ‖ℓ w‖ ≤ _ := hC w w.2
      _ ≤ |C| * (S.length * ‖Φ w‖) := mul_le_mul (le_abs_self C) h1 h0 (abs_nonneg C)
      _ = _ := (mul_assoc _ _ _).symm
  obtain ⟨g, hg, -⟩ := exists_extension_norm_eq (LinearMap.range Φ) (f.mkContinuous _ hb)
  refine ⟨_, S', fun i => g ∘L ContinuousLinearMap.single ℂ (fun _ => H) i, hS', fun w hw => ?_⟩
  have h1 := hg ⟨Φ ⟨w, hw⟩, ⟨_, rfl⟩⟩
  rw [LinearMap.mkContinuous_apply, hf] at h1
  simp only [ContinuousLinearMap.comp_apply, ← map_sum, ContinuousLinearMap.single_apply]
  refine h1.symm.trans (congrArg g ?_)
  funext j
  simp [hΦ, Pi.single_apply]

theorem dense_of_irred {U : Set (Matrix (Fin n) (Fin n) ℂ)} (hi : IsIrredOn U ρ) {S : Submodule ℂ H}
    (hS : ∀ g ∈ U, ∀ v ∈ S, ρ g v ∈ S) (h0 : S ≠ ⊥) : Dense (S : Set H) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top]
  refine (hi S.topologicalClosure S.isClosed_topologicalClosure fun g hg v hv =>
    map_mem_closure (ρ g).continuous hv (hS g hg)).resolve_left fun h => h0 ?_
  exact le_bot_iff.1 (h ▸ S.le_topologicalClosure)

variable {ε : Fin n → Bool} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {P : Matrix (Fin n) (Fin n) ℂ}

theorem continuous_garding (hσ : IsURepOn (UJset ε) σ) {φ : Matrix (Fin n) (Fin n) ℂ → ℝ} (hφ : Continuous φ)
    (hφc : HasCompactSupport φ) : Continuous (garding hσ hφ hφc) := by
  obtain ⟨hemb, -⟩ := Formalism.REAL.isClosedEmbeddingMatrix n ε
  have hψi : Integrable (fun g : Formalism.REAL.UJ ε => φ (umat g)) (Formalism.REAL.muG ε) :=
    (hφ.comp hemb.continuous).integrable_of_hasCompactSupport (hφc.comp_isClosedEmbedding hemb)
  refine AddMonoidHomClass.continuous_of_bound _ (∫ g : Formalism.REAL.UJ ε, ‖φ (umat g)‖ ∂(Formalism.REAL.muG ε)) fun w => ?_
  rw [garding_apply, ← integral_mul_const]
  refine norm_integral_le_of_norm_le (hψi.norm.mul_const _) (Filter.Eventually.of_forall fun g => ?_)
  rw [norm_smul, hσ.2.1 _ g.2]

theorem eq_zero_of_bumps {F : Formalism.REAL.UJ ε → ℂ} (hF : Continuous F)
    (h : ∀ φ : Matrix (Fin n) (Fin n) ℂ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      ∫ g, φ (umat g) • F g ∂(Formalism.REAL.muG ε) = 0) : F 1 = 0 := by
  obtain ⟨hemb, -⟩ := Formalism.REAL.isClosedEmbeddingMatrix n ε
  by_contra hw
  have hwpos : 0 < ‖F 1‖ := norm_pos_iff.2 hw
  have hnb := (hF.tendsto 1) (Metric.ball_mem_nhds _ (half_pos hwpos))
  rw [Filter.mem_map, hemb.isInducing.nhds_eq_comap, Filter.mem_comap] at hnb
  obtain ⟨U, hU, hUs⟩ := hnb
  obtain ⟨φ, hφ, hφc, hφU, hφ0, hφ1, -⟩ := exists_bump hU
  have h0 := h φ hφ hφc
  set μ := Formalism.REAL.muG ε
  have hψ : Continuous fun g : Formalism.REAL.UJ ε => φ (umat g) := hφ.continuous.comp hemb.continuous
  have hψc : HasCompactSupport fun g : Formalism.REAL.UJ ε => φ (umat g) := hφc.comp_isClosedEmbedding hemb
  have hψi : Integrable (fun g : Formalism.REAL.UJ ε => φ (umat g)) μ := hψ.integrable_of_hasCompactSupport hψc
  have hint : Integrable (fun g : Formalism.REAL.UJ ε => φ (umat g) • F g) μ :=
    (hψ.smul hF).integrable_of_hasCompactSupport hψc.smul_right
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
    · exact mul_le_mul_of_nonneg_left (le_of_lt (mem_ball_iff_norm.1 (hUs (hφU _ hg)))) (hφ0 _)
  rw [e1, norm_neg, norm_smul, Real.norm_of_nonneg hpos.le, integral_mul_const] at e2
  nlinarith [mul_pos hpos hwpos]

theorem isUnit_gram (hP : IsUnit P) (h : Pᴴ * Formalism.REAL.Jm ε * P = G) : IsUnit G := by
  rw [← h]
  exact (((Matrix.isUnit_conjTranspose _).2 hP).mul (IsUnit.of_mul_eq_one _ (Formalism.REAL.Jm_mul_self ε))).mul hP

theorem conj_inv_mem (hP : IsUnit P) (h : Pᴴ * Formalism.REAL.Jm ε * P = G) {g : Matrix (Fin n) (Fin n) ℂ}
    (hg : g ∈ UJset ε) : P⁻¹ * g * P ∈ Formalism.QuantumDeterminants.UH G := by
  have hd := (isUnit_iff_isUnit_det _).1 hP
  have e : gᴴ * Formalism.REAL.Jm ε * g = Formalism.REAL.Jm ε := hg
  show (P⁻¹ * g * P)ᴴ * G * (P⁻¹ * g * P) = G
  calc (P⁻¹ * g * P)ᴴ * G * (P⁻¹ * g * P)
      = Pᴴ * (gᴴ * ((P * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * P⁻¹)) * g) * P := by
        rw [← h]; simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = G := by rw [Matrix.mul_nonsing_inv _ hd, conjTranspose_one, one_mul, mul_one, e, h]

theorem conj_conj (hP : IsUnit P) (g : Matrix (Fin n) (Fin n) ℂ) : P * (P⁻¹ * g * P) * P⁻¹ = g := by
  have hd := (isUnit_iff_isUnit_det _).1 hP
  calc P * (P⁻¹ * g * P) * P⁻¹ = (P * P⁻¹) * g * (P * P⁻¹) := by simp only [Matrix.mul_assoc]
    _ = g := by rw [Matrix.mul_nonsing_inv _ hd, one_mul, mul_one]

theorem isURepOn_conj (hσ : IsURepOn (UJset ε) σ) (hP : IsUnit P) (h : Pᴴ * Formalism.REAL.Jm ε * P = G) :
    IsURepOn (Formalism.QuantumDeterminants.UH G) fun g => σ (P * g * P⁻¹) := by
  have hd := (isUnit_iff_isUnit_det _).1 hP
  refine ⟨⟨?_, fun a ha b hb => ?_⟩, fun g hg => hσ.2.1 _ (conj_mem hP h hg), fun v => ?_⟩
  · show σ (P * 1 * P⁻¹) = 1
    rw [mul_one, Matrix.mul_nonsing_inv _ hd, hσ.1.1]
  · have e : P * (a * b) * P⁻¹ = P * a * P⁻¹ * (P * b * P⁻¹) := by
      calc P * (a * b) * P⁻¹ = P * a * (P⁻¹ * P) * b * P⁻¹ := by
            rw [Matrix.nonsing_inv_mul _ hd, mul_one]; simp only [Matrix.mul_assoc]
        _ = _ := by simp only [Matrix.mul_assoc]
    show σ (P * (a * b) * P⁻¹) = _
    rw [e]
    exact hσ.1.2 _ (conj_mem hP h ha) _ (conj_mem hP h hb)
  · exact (hσ.2.2 v).comp ((continuous_const.mul continuous_id).mul continuous_const).continuousOn
      fun g hg => conj_mem hP h hg

theorem eq_zero_of_translates [CompleteSpace H] (hσ : IsURepOn (UJset ε) σ) (hi : IsIrredOn (UJset ε) σ)
    (hP : IsUnit P) (h : Pᴴ * Formalism.REAL.Jm ε * P = G) {ℓ : H →ₗ[ℂ] ℂ}
    (hℓ : Sobolev₂ (lie G) (fun g => σ (P * g * P⁻¹)) ℓ) {u : H} (hu : u ∈ smooth G fun g => σ (P * g * P⁻¹))
    (hu0 : u ≠ 0) (h0 : ∀ g ∈ UJset ε, ℓ (σ g u) = 0) {w : H} (hw : w ∈ smooth G fun g => σ (P * g * P⁻¹)) :
    ℓ w = 0 := by
  obtain ⟨hemb, -⟩ := Formalism.REAL.isClosedEmbeddingMatrix n ε
  have hG := isUnit_gram hP h
  have hρ := isURepOn_conj hσ hP h
  set ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H) := fun g => σ (P * g * P⁻¹) with hρdef
  have hσρ : ∀ g, ρ (P⁻¹ * g * P) = σ g := fun g => congrArg σ (conj_conj hP g)
  haveI : Nontrivial H := ⟨u, 0, hu0⟩
  have hd : Dense (smoothAll G ρ : Set H) := by
    refine dense_of_irred hi (fun g hg v hv k x hx hxG => ?_) ?_
    · have hg' := conj_inv_mem hP h hg
      have h1 := hv k (fun t => x t * (P⁻¹ * g * P)) (hx.mul contDiff_const) fun t => by
        have := list_prod_mem (G := G) [x t, P⁻¹ * g * P] (by
          intro y hy
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
          rcases hy with rfl | rfl
          exacts [hxG t, hg'])
        rwa [List.prod_cons, List.prod_singleton] at this
      convert h1 using 2 with t
      rw [hρ.1.2 _ (hxG t) _ hg', hσρ]; rfl
    · obtain ⟨v, hv, hs⟩ := exists_garding hσ
      exact (Submodule.ne_bot_iff _).2 ⟨v, fun k x hx hxG => hs k _
        ((contDiff_const.mul hx).mul contDiff_const) fun t => conj_mem hP h (hxG t), hv⟩
  have hd' : Dense (smooth G ρ : Set H) := hd.mono (smoothAll_le hG)
  have htr : ∀ v ∈ smooth G ρ, ∀ g ∈ UJset ε, σ g v ∈ smooth G ρ := fun v hv g hg => by
    rw [← hσρ]; exact translate_mem hG hρ (conj_inv_mem hP h hg) hv
  have hcont : ∀ l : List (Matrix (Fin n) (Fin n) ℂ), (∀ X ∈ l, X ∈ lie G) → ∀ v ∈ smooth G ρ,
      Continuous fun g : Formalism.REAL.UJ ε => l.foldr (dRep ρ) (σ (umat g) v) := fun l hl v hv => by
    simp only [← hσρ]
    exact continuous_word_orbit hG hρ hd ((continuous_const.mul hemb.continuous).mul continuous_const)
      (fun g => conj_inv_mem hP h g.2) l hl hv
  obtain ⟨m, S, Λ, hS, hΛ⟩ := exists_factor hG hρ hℓ
  have hF : Continuous fun g : Formalism.REAL.UJ ε => ℓ (σ (umat g) w) := by
    simp only [fun g : Formalism.REAL.UJ ε => hΛ _ (htr w hw (umat g) g.2)]
    exact continuous_finset_sum _ fun i _ => (Λ i).continuous.comp (hcont _ (hS i) w hw)
  have key := eq_zero_of_bumps hF fun φ hφ hφc => ?_
  · have e : σ (umat (1 : Formalism.REAL.UJ ε)) = 1 := hσ.1.1
    rwa [e] at key
  have hψ : Continuous fun g : Formalism.REAL.UJ ε => φ (umat g) := hφ.continuous.comp hemb.continuous
  have hψc : HasCompactSupport fun g : Formalism.REAL.UJ ε => φ (umat g) := hφc.comp_isClosedEmbedding hemb
  set γ := garding hσ hφ.continuous hφc with hγ
  have hγs : ∀ x, γ x ∈ smooth G ρ := fun x => smoothAll_le hG fun k y hy hyG =>
    contDiff_garding hσ hφ hφc x k _ ((contDiff_const.mul hy).mul contDiff_const) fun t => conj_mem hP h (hyG t)
  have hint : ∀ l : List (Matrix (Fin n) (Fin n) ℂ), (∀ X ∈ l, X ∈ lie G) → ∀ v ∈ smooth G ρ,
      Integrable (fun g : Formalism.REAL.UJ ε => φ (umat g) • l.foldr (dRep ρ) (σ (umat g) v)) (Formalism.REAL.muG ε) :=
    fun l hl v hv => (hψ.smul (hcont l hl v hv)).integrable_of_hasCompactSupport hψc.smul_right

  have hex : ∀ l : List (Matrix (Fin n) (Fin n) ℂ), (∀ X ∈ l, X ∈ lie G) → ∀ v ∈ smooth G ρ,
      l.foldr (dRep ρ) (γ v) =
        ∫ g : Formalism.REAL.UJ ε, φ (umat g) • l.foldr (dRep ρ) (σ (umat g) v) ∂(Formalism.REAL.muG ε) := by
    intro l hl v hv
    refine hd'.eq_of_inner_right ℂ fun y hy => ?_
    obtain ⟨y', hy'⟩ := exists_adjoint hG hρ l hl y hy
    rw [hy' _ (hγs v), show γ v = _ from garding_apply hσ hφ.continuous hφc v,
      ← integral_inner (integrable_garding hσ hφ.continuous hφc v),
      ← integral_inner (hint l hl v hv)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    simp only [← Complex.coe_smul, inner_smul_right]
    rw [hy' _ (htr v hv _ g.2)]
  have hform : ∀ v ∈ smooth G ρ,
      ℓ (γ v) = ∫ g : Formalism.REAL.UJ ε, φ (umat g) • ℓ (σ (umat g) v) ∂(Formalism.REAL.muG ε) := by
    intro v hv
    rw [hΛ _ (hγs v)]
    simp only [fun i => hex _ (hS i) v hv, fun i => ((Λ i).integral_comp_comm (hint _ (hS i) v hv)).symm]
    rw [← integral_finset_sum _ fun i _ => (Λ i).integrable_comp (hint _ (hS i) v hv)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    simp only [hΛ _ (htr v hv (umat g) g.2), Finset.smul_sum, ContinuousLinearMap.map_smul_of_tower]

  have hbd : Continuous fun x => ℓ (γ x) := by
    simp only [fun x => hΛ _ (hγs x)]
    refine continuous_finset_sum _ fun i _ => (Λ i).continuous.comp ?_
    obtain ⟨L, hL⟩ := exists_word hG hρ (S i) (hS i)
    let A : H →ₗ[ℂ] H := (smooth G ρ).subtype ∘ₗ L ∘ₗ γ.codRestrict _ hγs
    have hA : ∀ x, A x = (S i).foldr (dRep ρ) (γ x) := fun x => hL _
    simp only [← hA]
    refine A.continuous_of_seq_closed_graph fun s x z hs hz => hd'.eq_of_inner_right ℂ fun y hy => ?_
    obtain ⟨y', hy'⟩ := exists_adjoint hG hρ _ (hS i) y hy
    have h1 : Filter.Tendsto (fun j => ⟪y, A (s j)⟫_ℂ) Filter.atTop (𝓝 ⟪y, z⟫_ℂ) := tendsto_const_nhds.inner hz
    simp only [hA, fun x => hy' _ (hγs x)] at h1 ⊢
    exact tendsto_nhds_unique h1
      (tendsto_const_nhds.inner (((continuous_garding hσ hφ.continuous hφc).tendsto x).comp hs))

  have hmul : ∀ a ∈ UJset ε, ∀ b ∈ UJset ε, a * b ∈ UJset ε := fun a ha b hb => by
    have e1 : aᴴ * Formalism.REAL.Jm ε * a = Formalism.REAL.Jm ε := ha
    have e2 : bᴴ * Formalism.REAL.Jm ε * b = Formalism.REAL.Jm ε := hb
    show (a * b)ᴴ * Formalism.REAL.Jm ε * (a * b) = Formalism.REAL.Jm ε
    calc (a * b)ᴴ * Formalism.REAL.Jm ε * (a * b) = bᴴ * (aᴴ * Formalism.REAL.Jm ε * a) * b := by
          simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := by rw [e1, e2]
  have hact : ∀ a ∈ UJset ε, ∀ b ∈ UJset ε, σ a (σ b u) = σ (a * b) u := fun a ha b hb => by
    rw [hσ.1.2 a ha b hb]; rfl
  have hdu : Dense (Submodule.span ℂ ((fun g => σ g u) '' UJset ε) : Set H) := by
    refine dense_of_irred hi (fun g hg v hv => ?_) ?_
    · refine (Submodule.map_span_le (σ g : H →ₗ[ℂ] H) _ _).2 ?_ ⟨v, hv, rfl⟩
      rintro _ ⟨b, hb, rfl⟩
      exact Submodule.subset_span ⟨g * b, hmul g hg b hb, (hact g hg b hb).symm⟩
    · refine (Submodule.ne_bot_iff _).2 ⟨u, Submodule.subset_span ⟨1, (1 : Formalism.REAL.UJ ε).2, ?_⟩, hu0⟩
      show σ 1 u = u
      rw [hσ.1.1]; rfl
  have hz : (fun x => ℓ (γ x)) = fun _ => 0 := by
    refine Continuous.ext_on hdu hbd continuous_const fun v hv => ?_
    have : Submodule.span ℂ ((fun g => σ g u) '' UJset ε) ≤ LinearMap.ker (ℓ ∘ₗ γ) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨b, hb, rfl⟩
      show ℓ (γ (σ b u)) = 0
      rw [hform _ (htr u hu b hb)]
      simp only [fun g : Formalism.REAL.UJ ε => (congrArg ℓ (hact (umat g) g.2 b hb)).trans (h0 _ (hmul _ g.2 b hb)),
        smul_zero, integral_zero]
    exact this hv
  rw [← hform w hw]
  exact congrFun hz w

end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Links

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem lowGenerates {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau) :
    GlobalTheory.Survey.SobolevContinuityLowGeneration.LowGenerates M τ := by
  intro ℓ hℓ h0 w
  obtain ⟨u, hu, hu0⟩ := (Submodule.ne_bot_iff _).1 (lowT_ne_bot M τ)
  obtain ⟨_, -, hσ, hi, -⟩ := M.ds τ
  have hs : M.sm τ = smooth (gramAt D V τ) (M.rep τ) := Submodule.span_eq (smooth (gramAt D V τ) (M.rep τ))
  have hP := M.fr_unit τ
  have h := M.fr_gram τ
  have hu' : (u : M.H τ) ∈ smooth (gramAt D V τ) (M.rep τ) := hs ▸ u.2
  have hw' : (w : M.H τ) ∈ smooth (gramAt D V τ) (M.rep τ) := hs ▸ w.2
  refine eq_zero_of_translates hσ hi hP h hℓ hu' (fun e => hu0 (Subtype.ext e)) (fun g hg => ?_) hw'
  have hg' := conj_inv_mem hP h hg
  have e : M.rep τ ((M.fr τ)⁻¹ * g * M.fr τ) = M.σ τ g := congrArg (M.σ τ) (conj_conj hP g)
  have hm : M.rep τ ((M.fr τ)⁻¹ * g * M.fr τ) u ∈ M.sm τ :=
    hs.ge (translate_mem (isUnit_gram hP h) (isURepOn_conj hσ hP h) hg' hu')
  rw [← e]
  exact h0 u hu _ hg' ⟨_, hm⟩ rfl

theorem eq_zero_of_lowT : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (θ : InfFam D),
    IsInfFam θ → (∀ τ, lowT M τ ≠ ⊥) → ∀ (J : Set (GA D V)) (χ : GA D V → ℂ), ∀ T ∈ Mult θ M J χ,
      (∀ v : ∀ ρ, lowT M ρ, T (fun ρ => v ρ) = 0) → T = 0 :=
  fun _ _ _ M _ _ _ _ _ _ hT h0 => GlobalTheory.Survey.SobolevContinuityLowGeneration.eq_zero_of_lowGenerates (lowGenerates M) hT h0

end GlobalTheory.LowTypeDetermined

end
