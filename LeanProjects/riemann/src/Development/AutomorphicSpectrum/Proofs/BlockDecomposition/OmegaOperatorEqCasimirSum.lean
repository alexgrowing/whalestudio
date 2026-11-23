import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.CuspFormsHeight
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.DecayUniform
import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.GKStable
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmMemArchSmooth
import Development.AutomorphicSpectrum.Proofs.HermitianForms.CasOfCapelliVec
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OmegaOpCommLiB
set_option maxSynthPendingDepth 1
open NumberField GlobalTheory.CuspRep GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction
open scoped NumberField.AdeleRing

noncomputable section

namespace GlobalTheory.CompanionTheory.HCRep.TraceCas

open AutomorphicForm GlobalTheory.CompanionTheory.ArchSmooth GlobalTheory.CompanionTheory.HCRep

theorem sum_sq_eq {L A ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [LieRing L] [LieAlgebra ℝ L]
    [Ring A] [Module ℝ A] [IsScalarTower ℝ A A] [SMulCommClass ℝ A A]
    (B : LinearMap.BilinForm ℝ L) (hs : ∀ X Y, B X Y = B Y X) (l : L →ₗ[ℝ] A)
    (b : Module.Basis ι ℝ L) (ε : ι → ℝ) (hε : ∀ i, ε i * ε i = 1)
    (horth : ∀ i j, B (b i) (b j) = if i = j then ε i else 0)
    (c c' : κ → L) (hc : ∀ Y, Y = ∑ k, B (c' k) Y • c k) :
    ∑ i, ε i • (l (b i) * l (b i)) = ∑ k, l (c k) * l (c' k) := by
  have h1 : ∀ i, l (b i) = ∑ k, B (c' k) (b i) • l (c k) := fun i => by
    conv_lhs => rw [hc (b i)]
    simp only [map_sum, map_smul]
  have h2 : ∀ k, l (c' k) = ∑ i, (ε i * B (b i) (c' k)) • l (b i) := fun k => by
    conv_lhs => rw [eq_sum_of_orthogonal hε horth (c' k)]
    simp only [map_sum, map_smul]
  calc ∑ i, ε i • (l (b i) * l (b i))
      = ∑ i, ε i • ((∑ k, B (c' k) (b i) • l (c k)) * l (b i)) :=
        Finset.sum_congr rfl fun i _ => by rw [← h1 i]
    _ = ∑ k, l (c k) * ∑ i, (ε i * B (b i) (c' k)) • l (b i) := by
        simp only [Finset.sum_mul, Finset.mul_sum, Finset.smul_sum, smul_mul_assoc, mul_smul_comm, smul_smul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
        rw [hs (c' k) (b i)]
    _ = ∑ k, l (c k) * l (c' k) := Finset.sum_congr rfl fun k _ => by rw [← h2 k]

theorem half_sum {A : Type*} [Ring A] [Algebra ℂ A] (e₁ f₁ e₂ f₂ : A) :
    (2 : ℂ) • (((1 / 2 : ℂ) • (e₁ - Complex.I • f₁)) * ((1 / 2 : ℂ) • (e₂ - Complex.I • f₂)) +
      ((1 / 2 : ℂ) • (e₁ + Complex.I • f₁)) * ((1 / 2 : ℂ) • (e₂ + Complex.I • f₂))) =
      e₁ * e₂ - f₁ * f₂ := by
  simp only [smul_mul_assoc, mul_smul_comm, sub_mul, mul_sub, add_mul, mul_add, smul_sub, smul_add, smul_smul]
  match_scalars <;> ring_nf <;> simp

theorem mul_neg_add {A : Type*} [Ring A] (x y z t : A) : x * -y + z * t = z * t - x * y := by
  rw [mul_neg]
  abel

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

open Classical in
theorem atEmb_embedding_apply (w v : InfinitePlace E) (z : ℂ) :
    atEmb w.embedding z v = if v = w then z else 0 := by
  classical
  unfold atEmb
  rw [InfinitePlace.mk_embedding, if_pos rfl, Pi.single_apply]

theorem atEmb_neg (τ : E →+* ℂ) (z : ℂ) : atEmb τ (-z) = -atEmb τ z := by
  rw [atEmb_eq τ (-z), atEmb_eq τ z]
  simp only [Complex.neg_re, Complex.neg_im, neg_smul]
  abel

theorem place_formula (τ : E →+* ℂ) :
    (2 : ℂ) • (Formalism.REAL.Cas (Eop (a := a) τ) + Formalism.REAL.Cas (Eop (a := a) (ComplexEmbedding.conjugate τ))) =
      ∑ i, ∑ j, (lieS E a i j (atEmb τ 1) * lieS E a j i (atEmb τ 1) -
        lieS E a i j (atEmb τ Complex.I) * lieS E a j i (atEmb τ Complex.I)) := by
  have hc : ∀ i j : Fin a, Eop (a := a) (ComplexEmbedding.conjugate τ) i j =
      (1 / 2 : ℂ) • (lieS E a i j (atEmb τ 1) + Complex.I • lieS E a i j (atEmb τ Complex.I)) := by
    intro i j
    simp only [Eop, atEmb_conj, map_one, Complex.conj_I, atEmb_neg, map_neg, smul_neg, sub_neg_eq_add]
  simp only [Formalism.REAL.Cas, hc, ← Finset.sum_add_distrib, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  exact half_sum (A := Module.End ℂ (Sm E a)) (lieS E a i j (atEmb τ 1)) (lieS E a i j (atEmb τ Complex.I))
    (lieS E a j i (atEmb τ 1)) (lieS E a j i (atEmb τ Complex.I))

def cInv (z : Cinf E) : mixedEmbedding.mixedSpace E := (0, fun v => z v.1)

theorem cMap_cInv (z : Cinf E) : cMap E (cInv z) = z := rfl

theorem cInv_cMap (x : mixedEmbedding.mixedSpace E) : cInv (cMap E x) = x := by
  refine Prod.ext (funext fun v => ?_) rfl
  exact absurd (IsTotallyComplex.isComplex v.1) (InfinitePlace.not_isComplex_iff_isReal.2 v.2)

theorem mMap_injective : Function.Injective (mMap E a) := by
  intro X Y h
  funext p q
  have h' : cMap E ((X : Matrix (Fin a) (Fin a) (mixedEmbedding.mixedSpace E)) p q) =
      cMap E ((Y : Matrix (Fin a) (Fin a) (mixedEmbedding.mixedSpace E)) p q) := congrFun (congrFun h p) q
  have := congrArg cInv h'
  rwa [cInv_cMap, cInv_cMap] at this

def Mt (i j : Fin a) (x : Cinf E) : (isExpLieAlgebra E a).lieSubalgebra :=
  ⟨(Matrix.single i j (cInv x) : Matrix (Fin a) (Fin a) (mixedEmbedding.mixedSpace E)), mem_lie _⟩

def coordL : (isExpLieAlgebra E a).lieSubalgebra →ₗ[ℝ] Lie E a where
  toFun X := mMap E a (X : ArchMatrix E a)
  map_add' X Y := map_add (mMap E a) (X : ArchMatrix E a) (Y : ArchMatrix E a)
  map_smul' r X := map_smul (mMap E a) r (X : ArchMatrix E a)

theorem coordL_Mt (i j : Fin a) (x : Cinf E) : coordL (Mt i j x) = toL (Matrix.single i j x) := by
  funext p q
  change cMap E (Matrix.single i j (cInv x) p q) = Matrix.single i j x p q
  simp only [Matrix.single_apply]
  split_ifs
  · exact cMap_cInv x
  · exact map_zero _

def liBL : (isExpLieAlgebra E a).lieSubalgebra →ₗ[ℝ] Module.End ℂ (Sm E a) := (lie E a).comp coordL

theorem liBL_apply (X : (isExpLieAlgebra E a).lieSubalgebra) : liBL X = liB X := rfl

theorem liBL_Mt (i j : Fin a) (x : Cinf E) : liBL (Mt i j x) = lieS E a i j x := by
  rw [lieS_apply]
  change lie E a (coordL (Mt i j x)) = _
  rw [coordL_Mt]

theorem trace_Mt (i j : Fin a) (x : Cinf E) (Y : (isExpLieAlgebra E a).lieSubalgebra) :
    archTraceForm E a (Mt j i x) Y = ∑ w, (x w * coordL Y i j w).re := by
  have h : Matrix.trace (mat ((Mt j i x : (isExpLieAlgebra E a).lieSubalgebra) : ArchMatrix E a) *
      mat (Y : ArchMatrix E a)) = cInv x * mat (Y : ArchMatrix E a) i j := by
    change Matrix.trace (Matrix.single j i (cInv x) * mat (Y : ArchMatrix E a)) = _
    rw [Matrix.trace, Finset.sum_eq_single j]
    · simp [Matrix.diag, Matrix.single_mul_apply_same]
    · intro c _ hc
      exact Matrix.single_mul_apply_of_ne _ _ _ _ _ hc _
    · simp
  rw [archTraceForm_apply, h, mixedTraceL_apply]
  simp only [Prod.fst_mul, Pi.mul_apply, cInv, Pi.zero_apply, zero_mul, Finset.sum_const_zero, zero_add, Prod.snd_mul]
  refine Finset.sum_bij (fun v _ => v.1) ?_ ?_ ?_ ?_
  · intro _ _
    exact Finset.mem_univ _
  · intro _ _ _ _ h
    exact Subtype.ext h
  · intro w _
    exact ⟨⟨w, IsTotallyComplex.isComplex w⟩, by simp, rfl⟩
  · intro v _
    rfl

open Classical in
theorem toL_single_atEmb (i j p q : Fin a) (w v : InfinitePlace E) (z : ℂ) :
    toL (Matrix.single i j (atEmb w.embedding z)) p q v = if (w, i, j) = (v, p, q) then z else 0 := by
  change Matrix.single i j (atEmb w.embedding z) p q v = _
  simp only [Matrix.single_apply, Prod.mk.injEq]
  by_cases h1 : i = p <;> by_cases h2 : j = q <;> by_cases h3 : w = v <;>
    simp [h1, h2, h3, atEmb_embedding_apply, eq_comm]

def cc : (InfinitePlace E × Fin a × Fin a) × Bool → (isExpLieAlgebra E a).lieSubalgebra
  | ((w, i, j), false) => Mt i j (atEmb w.embedding 1)
  | ((w, i, j), true) => Mt i j (atEmb w.embedding Complex.I)

def cc' : (InfinitePlace E × Fin a × Fin a) × Bool → (isExpLieAlgebra E a).lieSubalgebra
  | ((w, i, j), false) => Mt j i (atEmb w.embedding 1)
  | ((w, i, j), true) => -Mt j i (atEmb w.embedding Complex.I)

theorem trace_cc'_false (w : InfinitePlace E) (i j : Fin a) (Y : (isExpLieAlgebra E a).lieSubalgebra) :
    archTraceForm E a (cc' ((w, i, j), false)) Y = (coordL Y i j w).re := by
  classical
  change archTraceForm E a (Mt j i (atEmb w.embedding 1)) Y = _
  rw [trace_Mt]
  simp [atEmb_embedding_apply, apply_ite Complex.re]

theorem trace_cc'_true (w : InfinitePlace E) (i j : Fin a) (Y : (isExpLieAlgebra E a).lieSubalgebra) :
    archTraceForm E a (cc' ((w, i, j), true)) Y = (coordL Y i j w).im := by
  classical
  change archTraceForm E a (-Mt j i (atEmb w.embedding Complex.I)) Y = _
  rw [map_neg, LinearMap.neg_apply, trace_Mt]
  simp [atEmb_embedding_apply, apply_ite Complex.re]

theorem expansion (Y : (isExpLieAlgebra E a).lieSubalgebra) :
    Y = ∑ k, archTraceForm E a (cc' k) Y • cc k := by
  classical
  apply Subtype.ext
  apply mMap_injective
  change coordL Y = coordL (∑ k, archTraceForm E a (cc' k) Y • cc k)
  have term : ∀ (p q : Fin a) (v : InfinitePlace E) (t : InfinitePlace E × Fin a × Fin a),
      (∑ b, coordL (archTraceForm E a (cc' (t, b)) Y • cc (t, b))) p q v =
        if t = (v, p, q) then coordL Y p q v else 0 := by
    rintro p q v ⟨w, i, j⟩
    rw [Fintype.sum_bool, map_smul, map_smul, trace_cc'_true, trace_cc'_false]
    change (((coordL Y i j w).im • coordL (Mt i j (atEmb w.embedding Complex.I)) +
      (coordL Y i j w).re • coordL (Mt i j (atEmb w.embedding 1))) p q v) = _
    rw [coordL_Mt, coordL_Mt]
    simp only [Pi.add_apply, Pi.smul_apply, toL_single_atEmb]
    split_ifs with h
    · obtain ⟨rfl, rfl, rfl⟩ : w = v ∧ i = p ∧ j = q := by simpa using h
      apply Complex.ext <;> simp
    · simp
  rw [map_sum, Fintype.sum_prod_type]
  funext p q v
  let ev : Lie E a →+ ℂ := ⟨⟨fun X => X p q v, rfl⟩, fun _ _ => rfl⟩
  change ev (coordL Y) = ev (∑ t, ∑ b, coordL (archTraceForm E a (cc' (t, b)) Y • cc (t, b)))
  rw [map_sum]
  change _ = ∑ t, (∑ b, coordL (archTraceForm E a (cc' (t, b)) Y • cc (t, b))) p q v
  simp only [term]
  simp [ev]

theorem omegaOp_eq_two_cas (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a d : ℕ)
    (b : Module.Basis (Fin d) ℝ (AutomorphicForm.isExpLieAlgebra E a).lieSubalgebra) (ε : Fin d → ℝ)
    (hε : ∀ i, ε i = 1 ∨ ε i = -1)
    (horth : ∀ i j, AutomorphicForm.archTraceForm E a (b i) (b j) = if i = j then ε i else 0) :
    GlobalTheory.CompanionTheory.HCRep.omegaOp (⇑b) ε = (2 : ℂ) • ∑ w : InfinitePlace E,
      (Formalism.REAL.Cas (Eop (a := a) w.embedding) +
        Formalism.REAL.Cas (Eop (a := a) (ComplexEmbedding.conjugate w.embedding))) := by
  have hε2 : ∀ i, ε i * ε i = 1 := fun i => by rcases hε i with e | e <;> rw [e] <;> norm_num
  have key := sum_sq_eq (A := Module.End ℂ (Sm E a)) (archTraceForm E a) archTraceForm_symm (liBL (E := E) (a := a)) b ε hε2 horth cc cc' expansion
  have hL : omegaOp (⇑b) ε = ∑ i, ε i • (liBL (b i) * liBL (b i)) := by
    unfold omegaOp
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [liBL_apply]
    ext φ
    simp
  rw [hL, key, Fintype.sum_prod_type, Fintype.sum_prod_type, Finset.smul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [place_formula, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Fintype.sum_bool]
  change liBL (Mt i j (atEmb w.embedding Complex.I)) * liBL (-Mt j i (atEmb w.embedding Complex.I)) +
    liBL (Mt i j (atEmb w.embedding 1)) * liBL (Mt j i (atEmb w.embedding 1)) = _
  rw [map_neg, liBL_Mt, liBL_Mt, liBL_Mt, liBL_Mt]
  exact mul_neg_add (A := Module.End ℂ (Sm E a)) _ _ _ _

end GlobalTheory.CompanionTheory.HCRep.TraceCas

end
