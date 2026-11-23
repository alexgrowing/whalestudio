import Formalism.LocalToGlobal.PairingIndexBounds.RowActionCoefficients.AdmissibleInterpolation.InterpolationHolds

open MvPolynomial

noncomputable section

namespace Formalism.L2.PairingIndexBounds.Ent

open Formalism.GradedWeylDivisibility Formalism.L2.G.Model.TS Formalism.MainNotions.G

def cN (K : Type) [CommRing K] {n : ℕ} (ν : Fin n → ℕ) : K := fockR (hw K le_rfl ν) (hw K le_rfl ν)

theorem cN_ne (K : Type) [Field K] [CharZero K] {n : ℕ} (ν : Fin n → ℕ) : cN K ν ≠ 0 := by
  obtain ⟨N, hN, h⟩ := Top.hWNorm n n le_rfl ν
  unfold cN
  rw [h K]
  exact_mod_cast hN.ne'

theorem map_cN (K Kc : Type) [CommRing K] [CommRing Kc] (φ : K →+* Kc) {n : ℕ} (ν : Fin n → ℕ) : φ (cN K ν) = cN Kc ν := by
  obtain ⟨N, _, h⟩ := Top.hWNorm n n le_rfl ν
  unfold cN
  rw [h K, h Kc, map_natCast]

theorem fockR_add_left {σ R : Type} [CommRing R] (f f' g : MvPolynomial σ R) : fockR (f + f') g = fockR f g + fockR f' g :=
  (Top.fockRBilin σ R f f' g 0).1

theorem fockR_smul_left {σ R : Type} [CommRing R] (a : R) (f g : MvPolynomial σ R) : fockR (a • f) g = a * fockR f g :=
  (Top.fockRBilin σ R f 0 g a).2.1

theorem fockR_comm {σ R : Type} [CommRing R] (f g : MvPolynomial σ R) : fockR f g = fockR g f :=
  (Top.fockRBilin σ R f 0 g 0).2.2

theorem fockR_zero_left {σ R : Type} [CommRing R] (g : MvPolynomial σ R) : fockR 0 g = 0 := by
  have := fockR_smul_left (0 : R) (0 : MvPolynomial σ R) g
  rwa [zero_smul, zero_mul] at this

theorem fockR_sum_left {σ R ι : Type} [CommRing R] (s : Finset ι) (f : ι → MvPolynomial σ R) (g : MvPolynomial σ R) :
    fockR (∑ i ∈ s, f i) g = ∑ i ∈ s, fockR (f i) g := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [fockR_zero_left]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, fockR_add_left, ih]

def fockL {σ R : Type} [CommRing R] (g : MvPolynomial σ R) : MvPolynomial σ R →ₗ[R] R where
  toFun f := fockR f g
  map_add' f f' := fockR_add_left f f' g
  map_smul' a f := by rw [fockR_smul_left]; rfl

theorem rowAct_rowAct {R : Type} [CommRing R] {k n : ℕ} (g h : Matrix (Fin k) (Fin k) R) (F : MvPolynomial (Fin k × Fin n) R) :
    rowAct R g (rowAct R h F) = rowAct R (h * g) F :=
  congrArg (fun φ : MvPolynomial (Fin k × Fin n) R →ₐ[R] MvPolynomial (Fin k × Fin n) R => φ F) (rowActMul R k n g h)

theorem rowAct_one {R : Type} [CommRing R] {k n : ℕ} (F : MvPolynomial (Fin k × Fin n) R) : rowAct R (1 : Matrix (Fin k) (Fin k) R) F = F := by
  have : rowAct R (n := n) (1 : Matrix (Fin k) (Fin k) R) = AlgHom.id R _ := by
    apply MvPolynomial.algHom_ext
    intro v
    unfold rowAct
    rw [aeval_X]
    simp [Matrix.one_apply, ite_mul]
  rw [this]; rfl

theorem mem_deltaL' {O K : Type} [CommRing O] [Field K] [Algebra O K] {n : ℕ} {ν : Fin n → ℕ} {g : Matrix (Fin n) (Fin n) K}
    {F : MvPolynomial (Fin n × Fin n) K} :
    F ∈ deltaL O K n ν g ↔ rowAct K g F ∈ (weyl O n n le_rfl ν).map (toK O K) := Iff.rfl

section Tgt

variable {O K Kc : Type} [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] [Field K] [Algebra O K] [IsFractionRing O K]
  [CharZero K] [Field Kc] [Algebra K Kc]
  {B τ : Type} [Fintype B] [DecidableEq B] {n : ℕ} (em : B → Fin n × Fin n → τ)
  (hem : Function.Injective fun x : B × (Fin n × Fin n) => em x.1 x.2)
  (ν : B → Fin n → ℕ) (hν : ∀ b, Antitone (ν b))
  (h hi : B → Matrix (Fin n) (Fin n) K) (hh : ∀ b, hi b * h b = 1)
  (M : AddSubgroup Kc)
  (ι : B → Type) [∀ b, Fintype (ι b)] [∀ b, DecidableEq (ι b)]
  (e e' : ∀ b, ι b → MvPolynomial (Fin n × Fin n) K)

def Ei (i : ∀ b, ι b) : MvPolynomial τ K := ∏ b, rename (em b) (rowAct K (hi b) (e b (i b)))

def Ei' (i : ∀ b, ι b) : MvPolynomial τ K := ∏ b, rename (em b) (rowAct K (h b).transpose (e' b (i b)))

include hh in
theorem tgt1 (hsp : ∀ b, dualWeyl K n n (ν b) ≤ Submodule.span K (Set.range (e b)))
    (F : B → MvPolynomial (Fin n × Fin n) K) (hF : ∀ b, F b ∈ dualWeyl K n n (ν b)) :
    ∏ b, rename (em b) (F b) ∈ Submodule.span K (Set.range (Ei em hi ι e)) := by
  have hh' : ∀ b, h b * hi b = 1 := fun b => mul_eq_one_comm.1 (hh b)
  refine prod_span (R := K) (fun b => Set.range fun i : ι b => rename (em b) (rowAct K (hi b) (e b i))) _ ?_ _ ?_
  · intro f hf
    choose i hi' using hf
    refine Submodule.subset_span ⟨i, ?_⟩
    exact Finset.prod_congr rfl fun b _ => hi' b
  · intro b
    have h2 : rowAct K (h b) (F b) ∈ Submodule.span K (Set.range (e b)) :=
      hsp b (dualWeylRowStable K n n (ν b) (h b) (F b) (hF b))
    have h3 : F b = rowAct K (hi b) (rowAct K (h b) (F b)) := by rw [rowAct_rowAct, hh' b, rowAct_one]
    rw [h3]
    have h4 := Submodule.mem_map_of_mem (f := ((rename (em b) : MvPolynomial (Fin n × Fin n) K →ₐ[K] MvPolynomial τ K).comp
      (rowAct K (hi b))).toLinearMap) h2
    rw [Submodule.map_span, ← Set.range_comp] at h4
    exact h4

theorem tgt2 {ι' : Type} (E : ι' → MvPolynomial τ K) (t : MvPolynomial τ K) (ht : t ∈ Submodule.span K (Set.range E)) :
    map (algebraMap K Kc) t ∈ Submodule.span Kc (Set.range fun i => map (algebraMap K Kc) (E i)) := by
  induction ht using Submodule.span_induction with
  | mem x hx => obtain ⟨i, rfl⟩ := hx; exact Submodule.subset_span ⟨i, rfl⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx =>
    rw [smul_eq_C_mul, map_mul, map_C, ← smul_eq_C_mul]
    exact Submodule.smul_mem _ _ hx

include hem hh in
theorem tgt3 (hFP : FockProd)
    (hee : ∀ b i k, fockR (e b i) (e' b k) = if i = k then fockR (hw K le_rfl (ν b)) (hw K le_rfl (ν b)) else 0)
    (i k : ∀ b, ι b) : fockR (Ei em hi ι e i) (Ei' em h ι e' k) = if i = k then ∏ b, cN K (ν b) else 0 := by
  unfold Ei Ei'
  rw [hFP K B (Fin n × Fin n) τ em hem]
  have h4 : ∀ b, fockR (rowAct K (hi b) (e b (i b))) (rowAct K (h b).transpose (e' b (k b))) =
      if i b = k b then cN K (ν b) else 0 := by
    intro b
    rw [Top.fockRRowAct, rowAct_rowAct, ← Matrix.transpose_mul, hh b, Matrix.transpose_one, rowAct_one]
    exact hee b (i b) (k b)
  rw [Finset.prod_congr rfl fun b _ => h4 b]
  by_cases hik : i = k
  · subst hik; simp
  · rw [if_neg hik]
    obtain ⟨b, hb⟩ := Function.ne_iff.1 hik
    exact Finset.prod_eq_zero (Finset.mem_univ b) (if_neg hb)

include hem hh in
theorem tgt5 (hFP : FockProd)
    (hee : ∀ b i k, fockR (e b i) (e' b k) = if i = k then fockR (hw K le_rfl (ν b)) (hw K le_rfl (ν b)) else 0)
    (a : (∀ b, ι b) → Kc) (k : ∀ b, ι b) :
    fockR (∑ i, a i • map (algebraMap K Kc) (Ei em hi ι e i)) (map (algebraMap K Kc) (Ei' em h ι e' k)) =
      a k * ∏ b, cN Kc (ν b) := by
  rw [fockR_sum_left, Finset.sum_eq_single k]
  · rw [fockR_smul_left, Top.fockRMap, tgt3 em hem ν h hi hh ι e e' hFP hee, if_pos rfl, map_prod]
    congr 1
    exact Finset.prod_congr rfl fun b _ => map_cN K Kc _ _
  · intro i _ hik
    rw [fockR_smul_left, Top.fockRMap, tgt3 em hem ν h hi hh ι e e' hFP hee, if_neg hik, map_zero, mul_zero]
  · intro hk; exact absurd (Finset.mem_univ k) hk

include hem hh in

theorem tgt_core (hFP : FockProd)
    (he : ∀ b i, e b i ∈ (weyl O n n le_rfl (ν b)).map (toK O K)) (he' : ∀ b i, e' b i ∈ (dualWeyl O n n (ν b)).map (toK O K))
    (hee : ∀ b i k, fockR (e b i) (e' b k) = if i = k then fockR (hw K le_rfl (ν b)) (hw K le_rfl (ν b)) else 0)
    (hsp : ∀ b, dualWeyl K n n (ν b) ≤ Submodule.span K (Set.range (e b))) (y : MvPolynomial τ Kc)
    (hy : y ∈ Submodule.span Kc {z | ∃ F : B → MvPolynomial (Fin n × Fin n) K, (∀ b, F b ∈ dualWeyl K n n (ν b)) ∧
      z = map (algebraMap K Kc) (∏ b, rename (em b) (F b))})
    (hp : ∀ Q : B → MvPolynomial (Fin n × Fin n) K, (∀ b, Q b ∈ (dualWeyl O n n (ν b)).map (toK O K)) →
      ∃ a ∈ M, fockR y (map (algebraMap K Kc) (∏ b, rename (em b) (rowAct K (h b).transpose (Q b)))) =
        a * ∏ b, cN Kc (ν b)) :
    y ∈ AddSubgroup.closure {z | ∃ a ∈ M, ∃ F : B → MvPolynomial (Fin n × Fin n) K,
      (∀ b, F b ∈ deltaL O K n (ν b) (h b)) ∧ z = a • map (algebraMap K Kc) (∏ b, rename (em b) (F b))} := by
  have : CharZero Kc := charZero_of_injective_algebraMap (algebraMap K Kc).injective
  have h2 : y ∈ Submodule.span Kc (Set.range fun i => map (algebraMap K Kc) (Ei em hi ι e i)) := by
    refine (Submodule.span_le.2 ?_) hy
    rintro _ ⟨F, hF, rfl⟩
    exact tgt2 _ _ (tgt1 em ν h hi hh ι e hsp F hF)
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun Kc).1 h2
  have hc : (∏ b, cN Kc (ν b)) ≠ 0 := Finset.prod_ne_zero_iff.2 fun b _ => cN_ne Kc (ν b)
  have h6 : ∀ k, a k ∈ M := by
    intro k
    obtain ⟨a', ha', h7⟩ := hp (fun b => e' b (k b)) fun b => he' b (k b)
    have h5 := tgt5 (Kc := Kc) em hem ν h hi hh ι e e' hFP hee a k
    rw [ha] at h5
    have : a k = a' := mul_right_cancel₀ hc (h5.symm.trans h7)
    rw [this]; exact ha'
  rw [← ha]
  refine AddSubgroup.sum_mem _ fun i _ => AddSubgroup.subset_closure ?_
  refine ⟨a i, h6 i, fun b => rowAct K (hi b) (e b (i b)), fun b => ?_, ?_⟩
  · rw [mem_deltaL', rowAct_rowAct, hh b, rowAct_one]
    exact he b (i b)
  · unfold Ei
    rfl

end Tgt

section Tgt'

variable {O K Kc : Type} [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] [Field K] [Algebra O K] [IsFractionRing O K]
  [CharZero K] [Field Kc] [Algebra K Kc]
  {B τ : Type} [Fintype B] [DecidableEq B] {n : ℕ} (em : B → Fin n × Fin n → τ)
  (hem : Function.Injective fun x : B × (Fin n × Fin n) => em x.1 x.2)
  (ν : B → Fin n → ℕ) (hν : ∀ b, Antitone (ν b))
  (h hi : B → Matrix (Fin n) (Fin n) K) (hh : ∀ b, hi b * h b = 1)
  (M : AddSubgroup Kc)

include hem hν hh in
theorem tgt_abs (hDB : DualBases) (hFP : FockProd) (y : MvPolynomial τ Kc)
    (hy : y ∈ Submodule.span Kc {z | ∃ F : B → MvPolynomial (Fin n × Fin n) K, (∀ b, F b ∈ dualWeyl K n n (ν b)) ∧
      z = map (algebraMap K Kc) (∏ b, rename (em b) (F b))})
    (hp : ∀ Q : B → MvPolynomial (Fin n × Fin n) K, (∀ b, Q b ∈ (dualWeyl O n n (ν b)).map (toK O K)) →
      ∃ a ∈ M, fockR y (map (algebraMap K Kc) (∏ b, rename (em b) (rowAct K (h b).transpose (Q b)))) =
        a * ∏ b, cN Kc (ν b)) :
    y ∈ AddSubgroup.closure {z | ∃ a ∈ M, ∃ F : B → MvPolynomial (Fin n × Fin n) K,
      (∀ b, F b ∈ deltaL O K n (ν b) (h b)) ∧ z = a • map (algebraMap K Kc) (∏ b, rename (em b) (F b))} := by
  choose ι fι dι e e' he he' hee hsp using fun b => hDB O K n (ν b) (hν b)
  exact @tgt_core O K Kc _ _ _ _ _ _ _ _ _ B τ _ _ n em hem ν h hi hh M ι fι dι e e' hFP he he' hee hsp y hy hp

end Tgt'

end Formalism.L2.PairingIndexBounds.Ent
