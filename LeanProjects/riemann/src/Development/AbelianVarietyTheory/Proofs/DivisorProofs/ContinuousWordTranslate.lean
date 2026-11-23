import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmoothVecLowKSub

noncomputable section

open MeasureTheory Matrix
open scoped ContDiff Topology InnerProductSpace

namespace GlobalTheory.SmoothCyclic

open Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.GardingVec GlobalTheory.LowTypeRestriction

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

section Conj
variable {n : ℕ}

theorem conj_lie {J G A B X : Matrix (Fin n) (Fin n) ℂ} (hAB : A * B = 1) (h : Bᴴ * J * B = G)
    (hX : Xᴴ * J + J * X = 0) : (A * X * B)ᴴ * G + G * (A * X * B) = 0 := by
  have hBA : B * A = 1 := mul_eq_one_comm.1 hAB
  have hBA' : Aᴴ * Bᴴ = 1 := by rw [← conjTranspose_mul, hBA, conjTranspose_one]
  calc (A * X * B)ᴴ * G + G * (A * X * B)
      = Bᴴ * (Xᴴ * (Aᴴ * Bᴴ) * J + J * (B * A) * X) * B := by
        rw [← h]; simp only [conjTranspose_mul, Matrix.mul_assoc, Matrix.mul_add, Matrix.add_mul]
    _ = 0 := by rw [hBA, hBA', Matrix.mul_one, Matrix.mul_one, hX, Matrix.mul_zero, Matrix.zero_mul]

theorem exp_conj_of_mul {A B : Matrix (Fin n) (Fin n) ℂ} (hAB : A * B = 1) (X : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) :
    NormedSpace.exp (t • (A * X * B)) = A * NormedSpace.exp (t • X) * B := by
  have hB : B = A⁻¹ := (Matrix.inv_eq_right_inv hAB).symm
  rw [hB, ← Matrix.exp_conj _ _ (IsUnit.of_mul_eq_one _ hAB)]
  simp

theorem list_prod_conj {A B : Matrix (Fin n) (Fin n) ℂ} (hAB : A * B = 1) (l : List (Matrix (Fin n) (Fin n) ℂ)) :
    (l.map fun a => A * a * B).prod = A * l.prod * B := by
  have hBA : B * A = 1 := mul_eq_one_comm.1 hAB
  induction l with
  | nil => simp [hAB]
  | cons a l ih =>
    rw [List.map_cons, List.prod_cons, List.prod_cons, ih]
    calc A * a * B * (A * l.prod * B) = A * a * (B * A) * l.prod * B := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hBA]; simp only [Matrix.mul_assoc, Matrix.one_mul]

theorem expProd_conj {A B : Matrix (Fin n) (Fin n) ℂ} (hAB : A * B = 1) {k : ℕ}
    (Xs : Fin k → Matrix (Fin n) (Fin n) ℂ) (t : Fin k → ℝ) :
    (List.ofFn fun i => NormedSpace.exp (t i • (A * Xs i * B))).prod
      = A * (List.ofFn fun i => NormedSpace.exp (t i • Xs i)).prod * B := by
  rw [← list_prod_conj hAB, List.map_ofFn]
  simp only [exp_conj_of_mul hAB, Function.comp_def]

end Conj

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

def lieJ (ε : Fin n → Bool) : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ) where
  carrier := {X | Xᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * X = 0}
  add_mem' := fun {X Y} hX hY => by
    simp only [Set.mem_setOf_eq] at *
    rw [conjTranspose_add, Matrix.add_mul, Matrix.mul_add, add_add_add_comm, hX, hY, add_zero]
  zero_mem' := by simp
  smul_mem' := fun c X hX => by
    simp only [Set.mem_setOf_eq] at *
    rw [conjTranspose_smul, star_trivial, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, hX, smul_zero]

theorem exp_memJ {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ lieJ ε) (t : ℝ) : NormedSpace.exp (t • X) ∈ UJset ε :=
  exp_mem (IsUnit.of_mul_eq_one _ (Formalism.REAL.Jm_mul_self ε)) hX t

theorem expProd_memJ {k : ℕ} {Xs : Fin k → Matrix (Fin n) (Fin n) ℂ} (hX : ∀ i, Xs i ∈ lieJ ε) (t : Fin k → ℝ) :
    (List.ofFn fun i => NormedSpace.exp (t i • Xs i)).prod ∈ UJset ε :=
  list_prod_mem (G := Formalism.REAL.Jm ε) _ fun g hg => by
    obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hg
    exact exp_memJ (hX i) _

theorem mul_memJ {a b : Matrix (Fin n) (Fin n) ℂ} (ha : a ∈ UJset ε) (hb : b ∈ UJset ε) : a * b ∈ UJset ε := by
  have := list_prod_mem (G := Formalism.REAL.Jm ε) [a, b] (by
    intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl
    exacts [ha, hb])
  rw [List.prod_cons, List.prod_singleton] at this
  exact this

theorem rep_mul (hσ : IsURepOn (UJset ε) σ) {a b : Matrix (Fin n) (Fin n) ℂ} (ha : a ∈ UJset ε) (hb : b ∈ UJset ε)
    (v : H) : σ a (σ b v) = σ (a * b) v := by
  rw [hσ.1.2 _ ha _ hb]; rfl

theorem exists_invJ {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UJset ε) : ∃ A, A * g = 1 :=
  ⟨Formalism.REAL.Jm ε * gᴴ * Formalism.REAL.Jm ε, by
    have h : gᴴ * Formalism.REAL.Jm ε * g = Formalism.REAL.Jm ε := hg
    calc Formalism.REAL.Jm ε * gᴴ * Formalism.REAL.Jm ε * g = Formalism.REAL.Jm ε * (gᴴ * Formalism.REAL.Jm ε * g) := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [h, Formalism.REAL.Jm_mul_self]⟩

def smSub (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) : Submodule ℂ H where
  carrier := {w | SmoothVec (lieJ ε : Set _) σ w}
  add_mem' := fun ha hb k Xs hX => by simpa only [map_add] using (ha k Xs hX).add (hb k Xs hX)
  zero_mem' := fun k Xs _ => by simpa only [map_zero] using contDiff_const
  smul_mem' := fun c w hw k Xs hX => by simpa only [map_smul] using (hw k Xs hX).const_smul c

theorem hasDerivAt_dRep {w : H} (hw : w ∈ smSub ε σ) {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ lieJ ε) :
    HasDerivAt (fun t : ℝ => σ (NormedSpace.exp (t • X)) w) (dRep σ X w) 0 := by
  have h := (hw 1 (fun _ => X) fun _ => hX).comp (contDiff_pi.2 fun _ : Fin 1 => (contDiff_id : ContDiff ℝ ∞ (id : ℝ → ℝ)))
  have h2 : ContDiff ℝ ∞ fun t : ℝ => σ (NormedSpace.exp (t • X)) w := by
    simpa [Function.comp_def] using h
  exact (h2.differentiable (by simp) 0).hasDerivAt

theorem dRep_mem (hσ : IsURepOn (UJset ε) σ) {w : H} (hw : w ∈ smSub ε σ) {X : Matrix (Fin n) (Fin n) ℂ}
    (hX : X ∈ lieJ ε) : dRep σ X w ∈ smSub ε σ := by
  intro k Xs hXs
  have h := hw (k + 1) (Fin.snoc Xs X) (by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa using hX
    · simpa using hXs j)
  have hs : ContDiff ℝ ∞ fun z : (Fin k → ℝ) × ℝ => (Fin.snoc z.1 z.2 : Fin (k + 1) → ℝ) := by
    refine contDiff_pi.2 fun i => Fin.lastCases ?_ (fun j => ?_) i
    · simpa using contDiff_snd
    · simpa [Function.comp_def] using (contDiff_apply ℝ ℝ j).comp (contDiff_fst (F := ℝ))
  have h2 : ContDiff ℝ ∞ fun z : (Fin k → ℝ) × ℝ =>
      σ ((List.ofFn fun i => NormedSpace.exp (z.1 i • Xs i)).prod) (σ (NormedSpace.exp (z.2 • X)) w) := by
    convert h.comp hs using 2 with z
    rw [rep_mul hσ (expProd_memJ hXs _) (exp_memJ hX _)]
    simp only [Function.comp_def, List.ofFn_succ_last, Fin.snoc_castSucc, Fin.snoc_last, List.prod_append,
      List.prod_singleton]
  have h3 := ContDiff.fderiv (𝕜 := ℝ) (m := ∞) (n := ∞) (f := fun (t : Fin k → ℝ) (s : ℝ) =>
      σ ((List.ofFn fun i => NormedSpace.exp (t i • Xs i)).prod) (σ (NormedSpace.exp (s • X)) w))
      (g := fun _ => 0) h2 contDiff_const (by simp)
  convert h3.clm_apply (contDiff_const (c := (1 : ℝ))) using 2 with t
  exact (((σ _).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 (hasDerivAt_dRep hw hX)).deriv.symm

theorem translate_mem (hσ : IsURepOn (UJset ε) σ) {w : H} (hw : w ∈ smSub ε σ) {g : Matrix (Fin n) (Fin n) ℂ}
    (hg : g ∈ UJset ε) : σ g w ∈ smSub ε σ := by
  intro k Xs hXs
  obtain ⟨A, hA⟩ := exists_invJ hg
  have hm : ∀ i, A * Xs i * g ∈ lieJ ε := fun i => conj_lie hA hg (hXs i)
  have h := ((σ g).restrictScalars ℝ).contDiff.comp (hw k (fun i => A * Xs i * g) hm)
  convert h using 2 with t
  show σ _ (σ g w) = σ g (σ _ w)
  rw [rep_mul hσ (expProd_memJ hXs t) hg, rep_mul hσ hg (expProd_memJ hm t), expProd_conj hA,
    ← Matrix.mul_assoc, ← Matrix.mul_assoc, mul_eq_one_comm.1 hA, Matrix.one_mul]

theorem dRep_translate (hσ : IsURepOn (UJset ε) σ) {w : H} (hw : w ∈ smSub ε σ) {g A X : Matrix (Fin n) (Fin n) ℂ}
    (hg : g ∈ UJset ε) (hA : A * g = 1) (hX : X ∈ lieJ ε) : dRep σ X (σ g w) = σ g (dRep σ (A * X * g) w) := by
  have hm : A * X * g ∈ lieJ ε := conj_lie hA hg hX
  have h := ((σ g).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 (hasDerivAt_dRep hw hm)
  refine HasDerivAt.deriv (h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_))
  show σ _ (σ g w) = σ g (σ _ w)
  rw [rep_mul hσ (exp_memJ hX t) hg, rep_mul hσ hg (exp_memJ hm t), exp_conj_of_mul hA,
    ← Matrix.mul_assoc, ← Matrix.mul_assoc, mul_eq_one_comm.1 hA, Matrix.one_mul]

theorem exists_word (hσ : IsURepOn (UJset ε) σ) (l : List (Matrix (Fin n) (Fin n) ℂ)) (hl : ∀ X ∈ l, X ∈ lieJ ε) :
    ∃ L : smSub ε σ →ₗ[ℂ] smSub ε σ, ∀ w : smSub ε σ, (L w : H) = l.foldr (dRep σ) w := by
  induction l with
  | nil => exact ⟨LinearMap.id, fun _ => rfl⟩
  | cons X l ih =>
    obtain ⟨L, hL⟩ := ih fun Y hY => hl Y (by simp [hY])
    have hX := hl X (by simp)
    let d : smSub ε σ →ₗ[ℂ] smSub ε σ :=
      { toFun := fun w => ⟨dRep σ X w, dRep_mem hσ w.2 hX⟩
        map_add' := fun a b => Subtype.ext (HasDerivAt.deriv (by
          simpa only [Submodule.coe_add, map_add] using (hasDerivAt_dRep a.2 hX).fun_add (hasDerivAt_dRep b.2 hX)))
        map_smul' := fun c a => Subtype.ext (HasDerivAt.deriv (by
          simpa only [Submodule.coe_smul, map_smul, RingHom.id_apply] using
            (hasDerivAt_dRep a.2 hX).fun_const_smul c)) }
    refine ⟨d.comp L, fun w => ?_⟩
    rw [List.foldr_cons, ← hL]; rfl

theorem word_mem (hσ : IsURepOn (UJset ε) σ) {l : List (Matrix (Fin n) (Fin n) ℂ)} (hl : ∀ X ∈ l, X ∈ lieJ ε)
    {w : H} (hw : w ∈ smSub ε σ) : l.foldr (dRep σ) w ∈ smSub ε σ := by
  obtain ⟨L, hL⟩ := exists_word hσ l hl
  rw [← hL ⟨w, hw⟩]; exact (L _).2

theorem word_translate (hσ : IsURepOn (UJset ε) σ) {w : H} (hw : w ∈ smSub ε σ) {g A : Matrix (Fin n) (Fin n) ℂ}
    (hg : g ∈ UJset ε) (hA : A * g = 1) (l : List (Matrix (Fin n) (Fin n) ℂ)) (hl : ∀ X ∈ l, X ∈ lieJ ε) :
    l.foldr (dRep σ) (σ g w) = σ g ((l.map fun X => A * X * g).foldr (dRep σ) w) := by
  induction l with
  | nil => rfl
  | cons X l ih =>
    rw [List.foldr_cons, ih fun Y hY => hl Y (by simp [hY]), List.map_cons, List.foldr_cons]
    refine dRep_translate hσ (word_mem hσ (fun Y hY => ?_) hw) hg hA (hl X (by simp))
    obtain ⟨Z, hZ, rfl⟩ := List.mem_map.1 hY
    exact conj_lie hA hg (hl Z (by simp [hZ]))

theorem inner_dRep (hσ : IsURepOn (UJset ε) σ) {h w : H} (hh : h ∈ smSub ε σ) (hw : w ∈ smSub ε σ)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ lieJ ε) : ⟪h, dRep σ X w⟫_ℂ = ⟪-dRep σ X h, w⟫_ℂ := by
  have h1 := HasDerivAt.inner ℂ (hasDerivAt_dRep hh hX) (hasDerivAt_dRep hw hX)
  have h2 : (fun t : ℝ => ⟪σ (NormedSpace.exp (t • X)) h, σ (NormedSpace.exp (t • X)) w⟫_ℂ) = fun _ => ⟪h, w⟫_ℂ :=
    funext fun t => LinearIsometry.inner_map_map
      ⟨(σ (NormedSpace.exp (t • X))).toLinearMap, hσ.2.1 _ (exp_memJ hX t)⟩ h w
  rw [h2] at h1
  have h3 := h1.unique (hasDerivAt_const _ _)
  simp only [zero_smul, NormedSpace.exp_zero, hσ.1.1, ContinuousLinearMap.one_apply] at h3
  rw [inner_neg_left]
  exact eq_neg_of_add_eq_zero_left h3

theorem exists_adjoint_word (hσ : IsURepOn (UJset ε) σ) (l : List (Matrix (Fin n) (Fin n) ℂ))
    (hl : ∀ X ∈ l, X ∈ lieJ ε) : ∀ h ∈ smSub ε σ, ∃ h' : H, ∀ w ∈ smSub ε σ, ⟪h, l.foldr (dRep σ) w⟫_ℂ = ⟪h', w⟫_ℂ := by
  induction l with
  | nil => exact fun h _ => ⟨h, fun _ _ => rfl⟩
  | cons X l ih =>
    intro h hh
    have hl' : ∀ Y ∈ l, Y ∈ lieJ ε := fun Y hY => hl Y (by simp [hY])
    have hX := hl X (by simp)
    obtain ⟨h', hh'⟩ := ih hl' _ ((smSub ε σ).neg_mem (dRep_mem hσ hh hX))
    exact ⟨h', fun w hw => by rw [List.foldr_cons, inner_dRep hσ hh (word_mem hσ hl' hw) hX, hh' w hw]⟩

theorem dense_of_stable (hirr : IsIrredOn (UJset ε) σ) {S : Submodule ℂ H} (hS : ∀ g ∈ UJset ε, ∀ v ∈ S, σ g v ∈ S)
    (h0 : S ≠ ⊥) : Dense (S : Set H) := by
  rcases hirr S.topologicalClosure S.isClosed_topologicalClosure
    (fun g hg v hv => map_mem_closure (σ g).continuous hv (hS g hg)) with h | h
  · exact absurd (eq_bot_iff.2 (h ▸ S.le_topologicalClosure)) h0
  · exact Submodule.dense_iff_topologicalClosure_eq_top.2 h

def famSub (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) : Submodule ℂ H where
  carrier := {w | ∀ (k : ℕ) (x : (Fin k → ℝ) → Matrix (Fin n) (Fin n) ℂ), ContDiff ℝ ∞ x →
      (∀ t, x t ∈ UJset ε) → ContDiff ℝ ∞ fun t => σ (x t) w}
  add_mem' := fun ha hb k x hx hG => by simpa only [map_add] using (ha k x hx hG).add (hb k x hx hG)
  zero_mem' := fun k x _ _ => by simpa only [map_zero] using contDiff_const
  smul_mem' := fun c w hw k x hx hG => by simpa only [map_smul] using (hw k x hx hG).const_smul c

theorem famSub_le : famSub ε σ ≤ smSub ε σ := fun _ hw k Xs hX =>
  hw k _ (contDiff_expProd Xs) (expProd_memJ hX)

theorem dense_famSub [CompleteSpace H] [Nontrivial H] (hσ : IsURepOn (UJset ε) σ) (hirr : IsIrredOn (UJset ε) σ) :
    Dense (famSub ε σ : Set H) := by
  refine dense_of_stable hirr (fun g hg v hv k x hx hG => ?_) ?_
  · simpa only [rep_mul hσ (hG _) hg] using hv k (fun t => x t * g) (hx.mul contDiff_const) fun t => mul_memJ (hG t) hg
  · obtain ⟨v, hv, hs⟩ := exists_garding hσ
    exact (Submodule.ne_bot_iff _).2 ⟨v, hs, hv⟩

theorem dRep_lin_fam {h : H} (hh : h ∈ famSub ε σ) {X Y : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ lieJ ε)
    (hY : Y ∈ lieJ ε) (a b : ℝ) : dRep σ (a • X + b • Y) h = a • dRep σ X h + b • dRep σ Y h := by
  have h1 : ContDiff ℝ ∞ (NormedSpace.exp : Matrix (Fin n) (Fin n) ℂ → _) :=
    contDiff_iff_contDiffAt.2 fun x => (NormedSpace.exp_analytic (𝕂 := ℝ) x).contDiffAt
  have hF := hh 2 (fun t => NormedSpace.exp (t 0 • X + t 1 • Y))
    (h1.comp (((contDiff_apply ℝ ℝ 0).smul contDiff_const).add ((contDiff_apply ℝ ℝ 1).smul contDiff_const)))
    (fun t => by
      simpa using exp_memJ ((lieJ ε).add_mem ((lieJ ε).smul_mem (t 0) hX) ((lieJ ε).smul_mem (t 1) hY)) 1)
  have hd := (hF.differentiable (by simp) 0).hasFDerivAt
  set L := fderiv ℝ (fun t : Fin 2 → ℝ => σ (NormedSpace.exp (t 0 • X + t 1 • Y)) h) 0
  have key : ∀ a b : ℝ, dRep σ (a • X + b • Y) h = L ![a, b] := fun a b => by
    have h2 : HasDerivAt (fun s : ℝ => s • (![a, b] : Fin 2 → ℝ)) ![a, b] 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).smul_const (![a, b] : Fin 2 → ℝ)
    have h3 := HasFDerivAt.comp_hasDerivAt_of_eq 0 hd h2 (by simp)
    refine HasDerivAt.deriv ?_
    convert h3 using 2 with s
    simp [mul_smul]
  have e1 := key 1 0
  have e2 := key 0 1
  simp only [one_smul, zero_smul, add_zero, zero_add] at e1 e2
  rw [key, e1, e2, ← map_smul, ← map_smul, ← map_add]
  congr 1
  ext i; fin_cases i <;> simp

theorem dRep_lin [CompleteSpace H] [Nontrivial H] (hσ : IsURepOn (UJset ε) σ) (hirr : IsIrredOn (UJset ε) σ)
    {w : H} (hw : w ∈ smSub ε σ) {X Y : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ lieJ ε)
    (hY : Y ∈ lieJ ε) (a b : ℝ) : dRep σ (a • X + b • Y) w = a • dRep σ X w + b • dRep σ Y w := by
  refine Dense.eq_of_inner_right ℂ (dense_famSub hσ hirr) fun h hh => ?_
  have hh' := famSub_le hh
  rw [inner_dRep hσ hh' hw ((lieJ ε).add_mem ((lieJ ε).smul_mem a hX) ((lieJ ε).smul_mem b hY)),
    dRep_lin_fam hh hX hY, inner_add_right, ← Complex.coe_smul a (dRep σ X w), ← Complex.coe_smul b (dRep σ Y w),
    inner_smul_right, inner_smul_right, inner_dRep hσ hh' hw hX, inner_dRep hσ hh' hw hY,
    ← Complex.coe_smul a, ← Complex.coe_smul b]
  simp only [inner_neg_left, inner_add_left, inner_smul_left, Complex.conj_ofReal]
  ring

theorem continuous_word [CompleteSpace H] [Nontrivial H] (hσ : IsURepOn (UJset ε) σ) (hirr : IsIrredOn (UJset ε) σ)
    {T : Type} [TopologicalSpace T] (fs : List (T → Matrix (Fin n) (Fin n) ℂ)) (hc : ∀ f ∈ fs, Continuous f)
    (hm : ∀ f ∈ fs, ∀ x, f x ∈ lieJ ε) :
    ∀ w ∈ smSub ε σ, Continuous fun x => (fs.map fun f => f x).foldr (dRep σ) w := by
  induction fs using List.reverseRecOn with
  | nil => exact fun w _ => continuous_const
  | append_singleton fs f ih =>
    intro w hw
    have hm' : ∀ f ∈ fs, ∀ x, f x ∈ lieJ ε := fun f hf => hm f (by simp [hf])
    replace ih := ih (fun f hf => hc f (by simp [hf])) hm'
    have hf := hm f (by simp)
    let dX : lieJ ε →ₗ[ℝ] H :=
      { toFun := fun X => dRep σ X w
        map_add' := fun X Y => by simpa using dRep_lin hσ hirr hw X.2 Y.2 1 1
        map_smul' := fun c X => by simpa using dRep_lin hσ hirr hw X.2 X.2 c 0 }
    let b := Module.finBasis ℝ (lieJ ε)
    have hco : ∀ j, Continuous fun x => b.repr ⟨f x, hf x⟩ j := fun j =>
      (b.coord j).continuous_of_finiteDimensional.comp ((hc f (by simp)).subtype_mk hf)
    have hs : Continuous fun x => ∑ j, ((b.repr ⟨f x, hf x⟩ j : ℝ) : ℂ) •
        (fs.map fun f => f x).foldr (dRep σ) (dRep σ (b j) w) :=
      continuous_finset_sum _ fun j _ =>
        (Complex.continuous_ofReal.comp (hco j)).smul (ih _ (dRep_mem hσ hw (b j).2))
    convert hs using 2 with x
    obtain ⟨L, hL⟩ := exists_word hσ (fs.map fun f => f x) (by
      intro X hX
      obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hX
      exact hm' g hg x)
    have e : (⟨dRep σ (f x) w, dRep_mem hσ hw (hf x)⟩ : smSub ε σ) =
        ∑ j, ((b.repr ⟨f x, hf x⟩ j : ℝ) : ℂ) • ⟨dRep σ (b j) w, dRep_mem hσ hw (b j).2⟩ := by
      apply Subtype.ext
      have := congrArg dX (b.sum_repr ⟨f x, hf x⟩).symm
      rw [map_sum] at this
      simpa [dX, -Module.Basis.sum_repr] using this
    have e2 := hL ⟨dRep σ (f x) w, dRep_mem hσ hw (hf x)⟩
    rw [List.map_append, List.foldr_append]
    refine e2.symm.trans ?_
    rw [e, map_sum, Submodule.coe_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, Submodule.coe_smul, hL]

theorem continuous_word_translate [CompleteSpace H] [Nontrivial H] (hσ : IsURepOn (UJset ε) σ)
    (hirr : IsIrredOn (UJset ε) σ) {l : List (Matrix (Fin n) (Fin n) ℂ)} (hl : ∀ X ∈ l, X ∈ lieJ ε) {w : H}
    (hw : w ∈ smSub ε σ) : Continuous fun g : Formalism.REAL.UJ ε => l.foldr (dRep σ) (σ (umat g) w) := by
  obtain ⟨hemb, -⟩ := Formalism.REAL.isClosedEmbeddingMatrix n ε
  have hu : Continuous fun g : Formalism.REAL.UJ ε => umat g := hemb.continuous
  have hinv : ∀ g : Formalism.REAL.UJ ε, umat g⁻¹ * umat g = 1 := fun g => congrArg umat (inv_mul_cancel g)
  have hv := continuous_word hσ hirr (l.map fun X => fun g : Formalism.REAL.UJ ε => umat g⁻¹ * X * umat g)
    (by
      intro f hf
      obtain ⟨X, -, rfl⟩ := List.mem_map.1 hf
      exact ((hu.comp continuous_inv).mul continuous_const).mul hu)
    (by
      intro f hf g
      obtain ⟨X, hX, rfl⟩ := List.mem_map.1 hf
      exact conj_lie (hinv g) g.2 (hl X hX)) w hw
  simp only [List.map_map, Function.comp_def] at hv
  simp only [fun g : Formalism.REAL.UJ ε => word_translate hσ hw g.2 (hinv g) l hl]
  set v := fun g : Formalism.REAL.UJ ε => (l.map fun X => umat g⁻¹ * X * umat g).foldr (dRep σ) w
  show Continuous fun g : Formalism.REAL.UJ ε => σ (umat g) (v g)
  refine continuous_iff_continuousAt.2 fun g₀ => ?_
  have h1 : Filter.Tendsto (fun g : Formalism.REAL.UJ ε => σ (umat g) (v g - v g₀)) (𝓝 g₀) (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simp only [fun g : Formalism.REAL.UJ ε => hσ.2.1 (umat g) g.2]
    exact tendsto_iff_norm_sub_tendsto_zero.1 (hv.tendsto g₀)
  have h2 := ((hσ.2.2 (v g₀)).comp_continuous hu fun g => g.2).tendsto g₀
  simpa [ContinuousAt] using h1.add h2

theorem exists_factor {V E : Type} [AddCommGroup V] [Module ℂ V] [NormedAddCommGroup E] [NormedSpace ℂ E]
    (J : V →ₗ[ℂ] E) (ℓ : V →ₗ[ℂ] ℂ) (C : ℝ) (h : ∀ v, ‖ℓ v‖ ≤ C * ‖J v‖) : ∃ f : E →L[ℂ] ℂ, ∀ v, f (J v) = ℓ v := by
  have h0 : ℓ ∈ (LinearMap.ker J).dualAnnihilator := (Submodule.mem_dualAnnihilator _).2 fun v hv => by
    have := h v
    rw [LinearMap.mem_ker.1 hv, norm_zero, mul_zero] at this
    exact norm_le_zero_iff.1 this
  rw [← LinearMap.range_dualMap_eq_dualAnnihilator_ker] at h0
  obtain ⟨f₀, hf₀⟩ := h0
  have h1 : ∀ v, f₀ (J v) = ℓ v := fun v => by rw [← hf₀]; rfl
  obtain ⟨f, hf, -⟩ := exists_extension_norm_eq (LinearMap.range J)
    ((f₀.domRestrict (LinearMap.range J)).mkContinuous C (by
      rintro ⟨_, v, rfl⟩
      simpa [h1] using h v))
  exact ⟨f, fun v => (hf ⟨J v, v, rfl⟩).trans (h1 v)⟩

theorem exists_sum_of_sobCont (hσ : IsURepOn (UJset ε) σ) {ℓ : H →ₗ[ℂ] ℂ} (hℓ : Sobolev₂ (lieJ ε : Set _) σ ℓ) :
    ∃ (m : ℕ) (l : Fin m → List (Matrix (Fin n) (Fin n) ℂ)) (f : Fin m → (H →L[ℂ] ℂ)),
      (∀ i, ∀ X ∈ l i, X ∈ lieJ ε) ∧ ∀ w ∈ smSub ε σ, ℓ w = ∑ i, f i ((l i).foldr (dRep σ) w) := by
  obtain ⟨S, C, hS, hb⟩ := hℓ
  have hl : ∀ i : Fin S.length, ∀ X ∈ S.get i, X ∈ lieJ ε := fun i => hS _ (List.get_mem S i)
  choose L hL using fun i => exists_word hσ (S.get i) (hl i)
  let J : smSub ε σ →ₗ[ℂ] (Fin S.length → H) := LinearMap.pi fun i => (smSub ε σ).subtype.comp (L i)
  have hJ : ∀ w i, J w i = (S.get i).foldr (dRep σ) w := fun w i => hL i w
  obtain ⟨f, hf⟩ := exists_factor J (ℓ.comp (smSub ε σ).subtype) (|C| * S.length) fun w => by
    have h1 : (S.map fun l => ‖l.foldr (dRep σ) (w : H)‖).sum ≤ S.length * ‖J w‖ := by
      have := List.sum_le_card_nsmul (S.map fun l => ‖l.foldr (dRep σ) (w : H)‖) ‖J w‖ (by
        intro x hx
        obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hx
        obtain ⟨i, rfl⟩ := List.get_of_mem hl
        rw [← hJ]; exact norm_le_pi_norm _ i)
      simpa using this
    have h2 : 0 ≤ (S.map fun l => ‖l.foldr (dRep σ) (w : H)‖).sum := List.sum_nonneg (by
      intro x hx
      obtain ⟨l, -, rfl⟩ := List.mem_map.1 hx
      exact norm_nonneg _)
    refine (hb w w.2).trans ((mul_le_mul_of_nonneg_right (le_abs_self C) h2).trans ?_)
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left h1 (abs_nonneg C)
  refine ⟨S.length, S.get, fun i => f.comp (ContinuousLinearMap.single ℂ (fun _ => H) i), hl, fun w hw => ?_⟩
  refine (hf ⟨w, hw⟩).symm.trans ?_
  conv_lhs => rw [← Finset.univ_sum_single (J ⟨w, hw⟩), map_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [hJ]; rfl

variable {φ : Matrix (Fin n) (Fin n) ℂ → ℝ}

theorem integrable_smul {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (hφ : Continuous φ)
    (hφc : HasCompactSupport φ) {v : Formalism.REAL.UJ ε → E} (hv : Continuous v) :
    Integrable (fun g : Formalism.REAL.UJ ε => φ (umat g) • v g) (Formalism.REAL.muG ε) := by
  obtain ⟨hemb, -⟩ := Formalism.REAL.isClosedEmbeddingMatrix n ε
  have hψc : HasCompactSupport fun g : Formalism.REAL.UJ ε => φ (umat g) := hφc.comp_isClosedEmbedding hemb
  exact ((hφ.comp hemb.continuous).smul hv).integrable_of_hasCompactSupport hψc.smul_right

theorem garding_mem [CompleteSpace H] (hσ : IsURepOn (UJset ε) σ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (w : H) : garding hσ hφ.continuous hφc w ∈ smSub ε σ :=
  famSub_le (contDiff_garding hσ hφ hφc w)

theorem continuous_garding (hσ : IsURepOn (UJset ε) σ) (hφ : Continuous φ) (hφc : HasCompactSupport φ) :
    Continuous (garding hσ hφ hφc) := by
  refine AddMonoidHomClass.continuous_of_bound _ (∫ g : Formalism.REAL.UJ ε, ‖φ (umat g)‖ ∂(Formalism.REAL.muG ε)) fun w => ?_
  rw [garding_apply, ← integral_mul_const]
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  simp only [norm_smul, fun g : Formalism.REAL.UJ ε => hσ.2.1 (umat g) g.2]

theorem continuous_word_garding [CompleteSpace H] [Nontrivial H] (hσ : IsURepOn (UJset ε) σ)
    (hirr : IsIrredOn (UJset ε) σ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    {l : List (Matrix (Fin n) (Fin n) ℂ)} (hl : ∀ X ∈ l, X ∈ lieJ ε) :
    Continuous fun w => l.foldr (dRep σ) (garding hσ hφ.continuous hφc w) := by
  obtain ⟨L, hL⟩ := exists_word hσ l hl
  let B : H →ₗ[ℂ] H := (smSub ε σ).subtype.comp
    (L.comp ((garding hσ hφ.continuous hφc).codRestrict _ (garding_mem hσ hφ hφc)))
  have hB : ∀ w, B w = l.foldr (dRep σ) (garding hσ hφ.continuous hφc w) := fun w => hL _
  simp only [← hB]
  refine B.continuous_of_seq_closed_graph fun u x y hu hy => ?_
  refine Dense.eq_of_inner_right ℂ (dense_famSub hσ hirr) fun h hh => ?_
  obtain ⟨h', hh'⟩ := exists_adjoint_word hσ l hl h (famSub_le hh)
  have e : ∀ w, ⟪h, B w⟫_ℂ = ⟪h', garding hσ hφ.continuous hφc w⟫_ℂ := fun w => by
    rw [hB, hh' _ (garding_mem hσ hφ hφc w)]
  refine tendsto_nhds_unique (tendsto_const_nhds.inner (𝕜 := ℂ) (x := h) hy) ?_
  simp only [Function.comp_def, e]
  exact tendsto_const_nhds.inner (((continuous_garding hσ hφ.continuous hφc).tendsto x).comp hu)

theorem word_garding [CompleteSpace H] [Nontrivial H] (hσ : IsURepOn (UJset ε) σ)
    (hirr : IsIrredOn (UJset ε) σ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    {l : List (Matrix (Fin n) (Fin n) ℂ)} (hl : ∀ X ∈ l, X ∈ lieJ ε) {w : H} (hw : w ∈ smSub ε σ) :
    l.foldr (dRep σ) (garding hσ hφ.continuous hφc w)
      = ∫ g : Formalism.REAL.UJ ε, φ (umat g) • l.foldr (dRep σ) (σ (umat g) w) ∂(Formalism.REAL.muG ε) := by
  refine Dense.eq_of_inner_right ℂ (dense_famSub hσ hirr) fun h hh => ?_
  obtain ⟨h', hh'⟩ := exists_adjoint_word hσ l hl h (famSub_le hh)
  rw [hh' _ (garding_mem hσ hφ hφc w), garding_apply hσ hφ.continuous hφc w, ← integral_inner (integrable_garding hσ hφ.continuous hφc w),
    ← integral_inner (integrable_smul hφ.continuous hφc (continuous_word_translate hσ hirr hl hw))]
  refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
  simp only [← Complex.coe_smul, inner_smul_right]
  rw [hh' _ (translate_mem hσ hw g.2)]

theorem eq_zero_of_integral {F : Formalism.REAL.UJ ε → ℂ} (hF : Continuous F)
    (h : ∀ φ : Matrix (Fin n) (Fin n) ℂ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      ∫ g : Formalism.REAL.UJ ε, φ (umat g) • F g ∂(Formalism.REAL.muG ε) = 0) : F 1 = 0 := by
  by_contra hw
  obtain ⟨hemb, -⟩ := Formalism.REAL.isClosedEmbeddingMatrix n ε
  have hwpos : 0 < ‖F 1‖ := norm_pos_iff.2 hw
  have hnb : {g | ‖F g - F 1‖ < ‖F 1‖ / 2} ∈ 𝓝 (1 : Formalism.REAL.UJ ε) := by
    have h := hF.continuousAt (x := 1) (Metric.ball_mem_nhds _ (half_pos hwpos))
    simpa [Set.preimage, dist_eq_norm] using h
  rw [hemb.isInducing.nhds_eq_comap] at hnb
  obtain ⟨U, hU, hUs⟩ := Filter.mem_comap.1 hnb
  obtain ⟨φ, hφ, hφc, hφU, hφ0, hφ1, -⟩ := exists_bump (n := n) hU
  have h0 := h φ hφ hφc
  have hint := integrable_smul hφ.continuous hφc hF
  set μ := Formalism.REAL.muG ε
  have hψ : Continuous fun g : Formalism.REAL.UJ ε => φ (umat g) := hφ.continuous.comp hemb.continuous
  have hψc : HasCompactSupport fun g : Formalism.REAL.UJ ε => φ (umat g) := hφc.comp_isClosedEmbedding hemb
  have hψi : Integrable (fun g : Formalism.REAL.UJ ε => φ (umat g)) μ := hψ.integrable_of_hasCompactSupport hψc
  have hpos : 0 < ∫ g : Formalism.REAL.UJ ε, φ (umat g) ∂μ :=
    hψ.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := 1) hψc (fun g => hφ0 _)
      (by show φ 1 ≠ 0; rw [hφ1]; exact one_ne_zero)
  have e1 : ∫ g : Formalism.REAL.UJ ε, (φ (umat g) • F g - φ (umat g) • F 1) ∂μ
      = -((∫ g : Formalism.REAL.UJ ε, φ (umat g) ∂μ) • F 1) := by
    rw [integral_sub hint (hψi.smul_const (F 1)), h0, integral_smul_const, zero_sub]
  have e2 : ‖∫ g : Formalism.REAL.UJ ε, (φ (umat g) • F g - φ (umat g) • F 1) ∂μ‖
      ≤ ∫ g : Formalism.REAL.UJ ε, φ (umat g) * (‖F 1‖ / 2) ∂μ := by
    refine norm_integral_le_of_norm_le (hψi.mul_const _) (Filter.Eventually.of_forall fun g => ?_)
    rw [← smul_sub, norm_smul, Real.norm_of_nonneg (hφ0 _)]
    by_cases hg : φ (umat g) = 0
    · simp [hg]
    · exact mul_le_mul_of_nonneg_left (le_of_lt (hUs (hφU _ hg))) (hφ0 _)
  rw [e1, norm_neg, norm_smul, Real.norm_of_nonneg hpos.le, integral_mul_const] at e2
  nlinarith [mul_pos hpos hwpos]

theorem cyclic_UJ [CompleteSpace H] (hσ : IsURepOn (UJset ε) σ) (hirr : IsIrredOn (UJset ε) σ) {u : H}
    (hu : u ∈ smSub ε σ) (hu0 : u ≠ 0) {ℓ : H →ₗ[ℂ] ℂ} (hℓ : Sobolev₂ (lieJ ε : Set _) σ ℓ)
    (hz : ∀ g ∈ UJset ε, ℓ (σ g u) = 0) {w : H} (hw : w ∈ smSub ε σ) : ℓ w = 0 := by
  haveI : Nontrivial H := nontrivial_of_ne u 0 hu0
  obtain ⟨m, l, f, hl, hsum⟩ := exists_sum_of_sobCont hσ hℓ
  have hc : ∀ v ∈ smSub ε σ, Continuous fun g : Formalism.REAL.UJ ε => ℓ (σ (umat g) v) := fun v hv => by
    simp only [fun g : Formalism.REAL.UJ ε => hsum _ (translate_mem hσ hv g.2)]
    exact continuous_finset_sum _ fun i _ => (f i).continuous.comp (continuous_word_translate hσ hirr (hl i) hv)
  have key := eq_zero_of_integral (hc w hw) fun φ hφ hφc => by
    have hint : ∀ v ∈ smSub ε σ, ℓ (garding hσ hφ.continuous hφc v)
        = ∫ g : Formalism.REAL.UJ ε, φ (umat g) • ℓ (σ (umat g) v) ∂(Formalism.REAL.muG ε) := fun v hv => by
      rw [hsum _ (garding_mem hσ hφ hφc v)]
      simp only [fun g : Formalism.REAL.UJ ε => hsum _ (translate_mem hσ hv g.2), Finset.smul_sum]
      refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) (integral_finset_sum _ fun i _ =>
        integrable_smul hφ.continuous hφc ((f i).continuous.comp (continuous_word_translate hσ hirr (hl i) hv))).symm
      rw [word_garding hσ hirr hφ hφc (hl i) hv, ← ContinuousLinearMap.integral_comp_comm _
        (integrable_smul hφ.continuous hφc (continuous_word_translate hσ hirr (hl i) hv))]
      simp only [ContinuousLinearMap.map_smul_of_tower, Function.comp_def]
    have hcont : Continuous fun v => ℓ (garding hσ hφ.continuous hφc v) := by
      simp only [fun v => hsum _ (garding_mem hσ hφ hφc v)]
      exact continuous_finset_sum _ fun i _ => (f i).continuous.comp (continuous_word_garding hσ hirr hφ hφc (hl i))
    let S : Submodule ℂ H :=
      { carrier := {v | ∀ g ∈ UJset ε, ℓ (garding hσ hφ.continuous hφc (σ g v)) = 0}
        add_mem' := fun ha hb g hg => by simp only [map_add, ha g hg, hb g hg, add_zero]
        zero_mem' := fun g _ => by simp only [map_zero]
        smul_mem' := fun c v hv g hg => by simp only [map_smul, hv g hg, smul_zero] }
    have hone : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ UJset ε := (1 : Formalism.REAL.UJ ε).2
    have huS : u ∈ S := fun g hg => by
      rw [hint _ (translate_mem hσ hu hg)]
      simp only [fun x : Formalism.REAL.UJ ε => rep_mul hσ x.2 hg u, fun x : Formalism.REAL.UJ ε => hz _ (mul_memJ x.2 hg),
        smul_zero, integral_zero]
    have hd : Dense (S : Set H) := dense_of_stable hirr
      (fun g hg v hv x hx => by rw [rep_mul hσ hx hg]; exact hv _ (mul_memJ hx hg))
      ((Submodule.ne_bot_iff _).2 ⟨u, huS, hu0⟩)
    rw [← hint w hw]
    refine congrFun (hcont.ext_on hd continuous_const (g := fun _ => 0) fun v hv => ?_) w
    simpa [hσ.1.1] using hv 1 hone
  have e : umat (1 : Formalism.REAL.UJ ε) = 1 := rfl
  simpa [e, hσ.1.1] using key

section Transport
variable {P G : Matrix (Fin n) (Fin n) ℂ}

theorem smoothVec_transport (hP : IsUnit P) (h : Pᴴ * Formalism.REAL.Jm ε * P = G) (w : H) :
    SmoothVec {X | Xᴴ * G + G * X = 0} (fun g => σ (P * g * P⁻¹)) w ↔ w ∈ smSub ε σ := by
  have hd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).1 hP
  have h1 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv _ hd
  have h2 : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul _ hd
  have h' : (P⁻¹)ᴴ * G * P⁻¹ = Formalism.REAL.Jm ε := by
    calc (P⁻¹)ᴴ * G * P⁻¹ = (P * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * P⁻¹) := by
          rw [← h]; simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := by rw [h1]; simp
  constructor
  · intro hw k Xs hX
    have := hw k (fun i => P⁻¹ * Xs i * P) fun i => conj_lie h2 h (hX i)
    convert this using 2 with t
    rw [expProd_conj h2]
    simp only [← Matrix.mul_assoc, h1, Matrix.one_mul]
    rw [Matrix.mul_assoc, h1, Matrix.mul_one]
  · intro hw k Xs hX
    simpa only [expProd_conj h1] using hw k (fun i => P * Xs i * P⁻¹) fun i => conj_lie h1 h' (hX i)

theorem sobCont_transport (hP : IsUnit P) (h : Pᴴ * Formalism.REAL.Jm ε * P = G) {ℓ : H →ₗ[ℂ] ℂ}
    (hℓ : Sobolev₂ {X | Xᴴ * G + G * X = 0} (fun g => σ (P * g * P⁻¹)) ℓ) : Sobolev₂ (lieJ ε : Set _) σ ℓ := by
  have hd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).1 hP
  have h1 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv _ hd
  have h' : (P⁻¹)ᴴ * G * P⁻¹ = Formalism.REAL.Jm ε := by
    calc (P⁻¹)ᴴ * G * P⁻¹ = (P * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * P⁻¹) := by
          rw [← h]; simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := by rw [h1]; simp
  obtain ⟨S, C, hS, hb⟩ := hℓ
  have e : dRep (fun g => σ (P * g * P⁻¹)) = fun X w => dRep σ (P * X * P⁻¹) w := by
    funext X w
    simp only [dRep, exp_conj_of_mul h1]
  refine ⟨S.map fun l => l.map fun X => P * X * P⁻¹, C, fun l hl X hX => ?_, fun w hw => ?_⟩
  · obtain ⟨l', hl', rfl⟩ := List.mem_map.1 hl
    obtain ⟨Y, hY, rfl⟩ := List.mem_map.1 hX
    exact conj_lie h1 h' (hS l' hl' Y hY)
  · simpa only [e, List.map_map, Function.comp_def, List.foldr_map] using
      hb w ((smoothVec_transport hP h w).2 hw)

end Transport

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Mult

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem sm_eq {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau) :
    M.sm τ = smSub (M.ε τ) (M.σ τ) := by
  rw [← Submodule.span_eq (smSub (M.ε τ) (M.σ τ))]
  exact congrArg (Submodule.span ℂ) (Set.ext fun w => smoothVec_transport (M.fr_unit τ) (M.fr_gram τ) w)

theorem smooth_cyclic (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (τ : D.what₂.Tau) (u : M.sm τ)
    (hu : u ≠ 0) (ℓ : M.H τ →ₗ[ℂ] ℂ) (hℓ : Sobolev₂ (lieAt V τ) (M.rep τ) ℓ)
    (hz : ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ w : M.sm τ, (w : M.H τ) = M.rep τ g u → ℓ w = 0)
    (w : M.sm τ) : ℓ w = 0 := by
  obtain ⟨_, -, hσ, hirr, -⟩ := M.ds τ
  have hus : (u : M.H τ) ∈ smSub (M.ε τ) (M.σ τ) := (sm_eq M τ).le u.2
  refine cyclic_UJ hσ hirr hus (fun h => hu (Subtype.ext h)) (sobCont_transport (M.fr_unit τ) (M.fr_gram τ) hℓ)
    (fun g hg => ?_) ((sm_eq M τ).le w.2)
  have hd : IsUnit (M.fr τ).det := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
  have h1 : M.fr τ * (M.fr τ)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hd
  have hg' : gᴴ * Formalism.REAL.Jm (M.ε τ) * g = Formalism.REAL.Jm (M.ε τ) := hg
  refine hz ((M.fr τ)⁻¹ * g * M.fr τ) ?_ ⟨M.σ τ g u, (sm_eq M τ).ge (translate_mem hσ hus hg)⟩ ?_
  · show ((M.fr τ)⁻¹ * g * M.fr τ)ᴴ * gramAt D V τ * ((M.fr τ)⁻¹ * g * M.fr τ) = gramAt D V τ
    rw [← M.fr_gram τ]
    calc _ = (M.fr τ)ᴴ * (gᴴ * ((M.fr τ * (M.fr τ)⁻¹)ᴴ * Formalism.REAL.Jm (M.ε τ) * (M.fr τ * (M.fr τ)⁻¹)) * g)
          * M.fr τ := by simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := by rw [h1, conjTranspose_one, Matrix.one_mul, Matrix.mul_one, hg']
  · show M.σ τ g u = M.σ τ (M.fr τ * ((M.fr τ)⁻¹ * g * M.fr τ) * (M.fr τ)⁻¹) u
    simp only [← Matrix.mul_assoc, h1, Matrix.one_mul]
    rw [Matrix.mul_assoc, h1, Matrix.mul_one]

end GlobalTheory.SmoothCyclic
