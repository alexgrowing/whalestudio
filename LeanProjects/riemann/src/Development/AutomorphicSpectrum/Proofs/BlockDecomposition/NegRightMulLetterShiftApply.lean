import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InjectiveWedgeHighestCoefficient
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CenterEnvelopingAlgebraDirectSum
import Development.AbelianVarietyTheory.Proofs.HeightProofs.PolarConjTranspose
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ConstantTermParabolicFiniteType
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.StandardBlocksLevelSumStatement
open GlobalTheory.CompanionTheory.PairMult

noncomputable section

open Finset
open Formalism.REAL (GlRel qdet qminor Tm)

namespace GlobalTheory.CompanionTheory.PairMult.CenScal

variable {n : ℕ}

section Regular

variable {U : Type} [Ring U] [Algebra ℂ U]

def leftMulLetter (x : Fin n → Fin n → U) (p q : Fin n) : Module.End ℂ U := LinearMap.mulLeft ℂ (x p q)

def negRightMulLetterShift (x : Fin n → Fin n → U) (τ : Fin n → ℂ) (p q : Fin n) : Module.End ℂ U :=
  -LinearMap.mulRight ℂ (x p q) + if p = q then τ p • (1 : Module.End ℂ U) else 0

theorem leftMulLetter_apply (x : Fin n → Fin n → U) (p q : Fin n) (u : U) : leftMulLetter x p q u = x p q * u := rfl

theorem negRightMulLetterShift_apply (x : Fin n → Fin n → U) (τ : Fin n → ℂ) (p q : Fin n) (u : U) :
    negRightMulLetterShift x τ p q u = -(u * x p q) + if p = q then τ p • u else 0 := by
  unfold negRightMulLetterShift
  split_ifs <;> simp

def LevRel (lev : Fin n → ℕ) (x : Fin n → Fin n → U) : Prop :=
  ∀ p q r v, lev p = lev q → lev r = lev v →
    x p q * x r v - x r v * x p q = (if q = r then x p v else 0) - (if v = p then x r q else 0)

theorem lRel_regular {lev : Fin n → ℕ} {x : Fin n → Fin n → U} (hx : LevRel lev x) {τ : Fin n → ℂ}
    (hτ : ∀ a c, lev a = lev c → τ a = τ c) : LRel lev (leftMulLetter x) (negRightMulLetterShift x τ) := by
  refine ⟨fun p q r v h1 h2 => LinearMap.ext fun u => ?_, fun p q r v h1 h2 => LinearMap.ext fun u => ?_,
    fun p q r v _ _ => LinearMap.ext fun u => ?_⟩
  · have e := congrArg (· * u) (hx p q r v h1 h2)
    simp only [sub_mul, mul_assoc] at e
    simp only [LinearMap.sub_apply, Module.End.mul_apply, leftMulLetter_apply]
    rw [e]
    split_ifs <;> simp [leftMulLetter_apply]
  · have e := congrArg (u * ·) (hx p q r v h1 h2)
    simp only [mul_sub, ← mul_assoc] at e
    simp only [LinearMap.sub_apply, Module.End.mul_apply, negRightMulLetterShift_apply]
    have key : ∀ c c' : ℂ, (-((-(u * x r v) + c' • u) * x p q) + c • (-(u * x r v) + c' • u)) -
        (-((-(u * x p q) + c • u) * x r v) + c' • (-(u * x p q) + c • u)) = -(u * x p q * x r v - u * x r v * x p q) := by
      intro c c'
      simp only [add_mul, neg_mul, smul_mul_assoc, smul_add, smul_neg, smul_smul, neg_add, neg_neg]
      rw [mul_comm c c']
      abel
    have ea : ∀ (a b : Fin n) (w : U), (if a = b then τ a • w else 0) = (if a = b then τ a else 0) • w := by
      intro a b w
      split_ifs <;> simp
    simp only [ea]
    rw [key, e]
    by_cases h3 : q = r <;> by_cases h4 : v = p
    · subst h3 h4
      simp [negRightMulLetterShift_apply, hτ _ _ h1]
      abel
    · simp [h3, h4, negRightMulLetterShift_apply, Ne.symm h4]
    · simp [h3, h4, negRightMulLetterShift_apply, Ne.symm h3]
    · simp [h3, h4]
  · simp only [Module.End.mul_apply, leftMulLetter_apply, negRightMulLetterShift_apply]
    split_ifs <;> simp [mul_add, mul_assoc]

theorem central_letters {lev : Fin n → ℕ} {x : Fin n → Fin n → U} (hx : LevRel lev x) {τ : Fin n → ℂ}
    (hτ : ∀ a c, lev a = lev c → τ a = τ c) {b : FreeAlgebra ℂ (Bool × Fin n × Fin n)} (hb : InvLev lev b)
    (p q : Fin n) (hpq : lev p = lev q) :
    x p q * evB lev (leftMulLetter x) (negRightMulLetterShift x τ) b 1 = evB lev (leftMulLetter x) (negRightMulLetterShift x τ) b 1 * x p q := by
  have e := LinearMap.congr_fun (hb U (leftMulLetter x) (negRightMulLetterShift x τ) (lRel_regular hx hτ) p q hpq).eq 1
  simp only [Module.End.mul_apply, LinearMap.add_apply, leftMulLetter_apply, negRightMulLetterShift_apply] at e
  have e1 : x p q * (1 : U) + (-((1 : U) * x p q) + (if p = q then τ p • (1 : U) else 0)) = if p = q then τ p • (1 : U) else 0 := by
    simp
  rw [e1] at e
  split_ifs at e with h
  · rw [← add_assoc, map_smul] at e
    exact add_neg_eq_zero.1 (add_eq_right.1 e)
  · rw [add_zero, map_zero] at e
    exact add_neg_eq_zero.1 e

theorem evB_intertwine {W : Type} [AddCommGroup W] [Module ℂ W] {lev : Fin n → ℕ} {x : Fin n → Fin n → U}
    {τ : Fin n → ℂ} (ρ : U →ₐ[ℂ] Module.End ℂ W) (X1 X2 : Fin n → Fin n → Module.End ℂ W) (t : W)
    (hρ : ∀ p q, lev p = lev q → ρ (x p q) = X1 p q)
    (hc : ∀ p q, lev p = lev q → ∀ u, Commute (ρ u) (X2 p q))
    (ht : ∀ p q, lev p = lev q → (X1 p q + X2 p q) t = if p = q then τ p • t else 0)
    (b : FreeAlgebra ℂ (Bool × Fin n × Fin n)) (u : U) :
    evB lev X1 X2 b (ρ u t) = ρ (evB lev (leftMulLetter x) (negRightMulLetterShift x τ) b u) t := by
  induction b using FreeAlgebra.induction generalizing u with
  | grade0 r => simp [Module.algebraMap_end_apply]
  | grade1 l =>
    obtain ⟨s, p, q⟩ := l
    simp only [evB, FreeAlgebra.lift_ι_apply]
    by_cases hpq : lev p = lev q
    · cases s
      · simp only [if_true, hpq, Bool.false_eq_true, if_false, negRightMulLetterShift_apply]
        have e1 : X2 p q (ρ u t) = ρ u (X2 p q t) := (LinearMap.congr_fun (hc p q hpq u).eq t).symm
        have e2 : X2 p q t = -(X1 p q t) + if p = q then τ p • t else 0 := by
          rw [← ht p q hpq, LinearMap.add_apply]; abel
        rw [e1, e2]
        split_ifs <;> simp [map_add, map_neg, map_mul, hρ p q hpq, Module.End.mul_apply, LinearMap.add_apply]
      · simp only [if_true, hpq, leftMulLetter_apply, map_mul, Module.End.mul_apply, hρ p q hpq]
    · simp [hpq]
  | mul a c ha hc' =>
    simp only [map_mul, Module.End.mul_apply]
    rw [hc', ha]
  | add a c ha hc' =>
    simp only [map_add, LinearMap.add_apply, ha, hc']

end Regular

section Blocks

attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

open UniversalEnvelopingAlgebra

abbrev Gl (m : ℕ) : Type := Matrix (Fin m) (Fin m) ℂ

def eu (m : ℕ) (p q : Fin m) : UniversalEnvelopingAlgebra ℂ (Gl m) := ι ℂ (Matrix.single p q (1 : ℂ) : Gl m)

theorem single_lie {m : ℕ} (a b c d : Fin m) :
    (⁅(Matrix.single a b (1 : ℂ) : Gl m), (Matrix.single c d (1 : ℂ) : Gl m)⁆ : Gl m) =
      (if b = c then Matrix.single a d (1 : ℂ) else 0) - (if d = a then Matrix.single c b (1 : ℂ) else 0) := by
  rw [LieRing.of_associative_ring_bracket]
  congr 1
  · split_ifs with h
    · subst h; simp
    · exact Matrix.single_mul_single_of_ne _ _ _ _ h _
  · split_ifs with h
    · subst h; simp
    · exact Matrix.single_mul_single_of_ne _ _ _ _ h _

theorem glRel_eu (m : ℕ) : GlRel (eu m) := by
  intro a b c d
  have e := (ι ℂ : Gl m →ₗ⁅ℂ⁆ _).map_lie (Matrix.single a b (1 : ℂ) : Gl m) (Matrix.single c d (1 : ℂ) : Gl m)
  rw [single_lie, LieRing.of_associative_ring_bracket] at e
  simp only [eu]
  rw [← e, map_sub]
  split_ifs <;> simp

theorem gl_eq_sum {m : ℕ} (Z : Gl m) : Z = ∑ a, ∑ b, Z a b • (Matrix.single a b (1 : ℂ) : Gl m) := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single Z]
  simp

theorem mem_of_eu {m : ℕ} (S : Subalgebra ℂ (UniversalEnvelopingAlgebra ℂ (Gl m))) (h : ∀ p q, eu m p q ∈ S)
    (a : UniversalEnvelopingAlgebra ℂ (Gl m)) : a ∈ S := by
  refine GlobalTheory.EnvCentre.mem_of_ι_mem (AlgHom.id ℂ _) S (fun Z => ?_) a
  rw [gl_eq_sum Z, map_sum]
  simp only [map_sum, map_smul, AlgHom.id_apply]
  exact sum_mem fun p _ => sum_mem fun q _ => Subalgebra.smul_mem _ (h p q) _

theorem center_gl_le (m : ℕ) :
    Subalgebra.center ℂ (UniversalEnvelopingAlgebra ℂ (Gl m)) ≤ Algebra.adjoin ℂ (Set.range (qdet (eu m))) := by
  have hgen : Algebra.adjoin ℂ (Set.range fun p : Fin m × Fin m => eu m p.1 p.2) = ⊤ :=
    eq_top_iff.2 fun a _ => mem_of_eu (Algebra.adjoin ℂ (Set.range fun p : Fin m × Fin m => eu m p.1 p.2))
      (fun p q => Algebra.subset_adjoin ⟨(p, q), rfl⟩) a
  rw [GlobalTheory.SmoothForms.center_eq_adjoin (glRel_eu m) hgen, Algebra.adjoin_le_iff]
  rintro _ ⟨k, rfl⟩
  rw [← GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCentre.etr_succ_eq_gelfA']
  exact GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCentre.etr_mem_adjoin_qdet' _ _ _ (glRel_eu m) _

def glLin {A : Type} [Ring A] [Algebra ℂ A] {m : ℕ} (E : Fin m → Fin m → A) : Gl m →ₗ[ℂ] A where
  toFun Z := ∑ a, ∑ b, Z a b • E a b
  map_add' Z Z' := by simp [add_smul, sum_add_distrib]
  map_smul' c Z := by simp [smul_sum, mul_smul]

theorem glLin_single {A : Type} [Ring A] [Algebra ℂ A] {m : ℕ} (E : Fin m → Fin m → A) (p q : Fin m) :
    glLin E (Matrix.single p q (1 : ℂ) : Gl m) = E p q := by
  simp [glLin, Matrix.single_apply, ite_and]

theorem glLin_lie {A : Type} [Ring A] [Algebra ℂ A] {m : ℕ} {E : Fin m → Fin m → A} (hE : GlRel E) (Z Z' : Gl m) :
    glLin E ⁅Z, Z'⁆ = ⁅glLin E Z, glLin E Z'⁆ := by
  have key : ∀ a b c d : Fin m, glLin E ⁅(Matrix.single a b (1 : ℂ) : Gl m), (Matrix.single c d (1 : ℂ) : Gl m)⁆ =
      ⁅glLin E (Matrix.single a b (1 : ℂ) : Gl m), glLin E (Matrix.single c d (1 : ℂ) : Gl m)⁆ := by
    intro a b c d
    rw [single_lie, map_sub, glLin_single, glLin_single, LieRing.of_associative_ring_bracket, hE a b c d]
    split_ifs <;> simp [glLin_single]
  rw [gl_eq_sum Z, gl_eq_sum Z']
  simp only [sum_lie, lie_sum, smul_lie, lie_smul, map_sum, map_smul, key]

def glHom {A : Type} [Ring A] [Algebra ℂ A] {m : ℕ} (E : Fin m → Fin m → A) (hE : GlRel E) : Gl m →ₗ⁅ℂ⁆ A :=
  { glLin E with map_lie' := fun {Z Z'} => glLin_lie hE Z Z' }

theorem glHom_single {A : Type} [Ring A] [Algebra ℂ A] {m : ℕ} (E : Fin m → Fin m → A) (hE : GlRel E) (p q : Fin m) :
    glHom E hE (Matrix.single p q (1 : ℂ) : Gl m) = E p q := glLin_single E p q

variable {M : ℕ} (d : Fin M → ℕ)

abbrev Ds : Type := DirectSum (Fin M) fun i => Gl (d i)

abbrev UD : Type := UniversalEnvelopingAlgebra ℂ (Ds d)

def mi (i : Fin M) : UniversalEnvelopingAlgebra ℂ (Gl (d i)) →ₐ[ℂ] UD d :=
  lift ℂ ((ι ℂ).comp (DirectSum.lieAlgebraOf ℂ (Fin M) (fun i => Gl (d i)) i))

theorem mi_ι (i : Fin M) (Z : Gl (d i)) : mi d i (ι ℂ Z) = ι ℂ (DirectSum.of (fun i => Gl (d i)) i Z) := by
  simp only [mi, lift_ι_apply]
  rfl

def eb (i : Fin M) (p q : Fin (d i)) : UD d := mi d i (eu (d i) p q)

theorem mem_of_eb (S : Subalgebra ℂ (UD d)) (h : ∀ i p q, eb d i p q ∈ S) (a : UD d) : a ∈ S := by
  refine GlobalTheory.EnvCentre.mem_of_ι_mem (AlgHom.id ℂ _) S (fun z => ?_) a
  induction z using DirectSum.induction_on with
  | zero => simp
  | of i Z =>
    have : ∀ b, mi d i b ∈ S := fun b => mem_of_eu (S.comap (mi d i)) (fun p q => h i p q) b
    rw [AlgHom.id_apply, ← mi_ι]
    exact this _
  | add y z hy hz =>
    simp only [map_add]
    exact add_mem hy hz

theorem center_UD_le : Subalgebra.center ℂ (UD d) ≤
    Algebra.adjoin ℂ (⋃ i, Set.range fun u : ℂ => mi d i (qdet (eu (d i)) u)) := by
  rw [GlobalTheory.EnvCentre.center_directSum (Fin M) (fun i => Gl (d i)) (mi d) (mi_ι d), Algebra.adjoin_le_iff]
  intro z hz
  obtain ⟨i, c, hc, rfl⟩ := Set.mem_iUnion.1 hz
  have hle : Algebra.adjoin ℂ (Set.range (qdet (eu (d i)))) ≤
      (Algebra.adjoin ℂ (⋃ i, Set.range fun u : ℂ => mi d i (qdet (eu (d i)) u))).comap (mi d i) := by
    refine Algebra.adjoin_le ?_
    rintro _ ⟨u, rfl⟩
    exact Algebra.subset_adjoin (Set.mem_iUnion.2 ⟨i, u, rfl⟩)
  exact hle (center_gl_le _ hc)

theorem eb_comm {i k : Fin M} (hik : i ≠ k) (p q : Fin (d i)) (r v : Fin (d k)) : Commute (eb d i p q) (eb d k r v) := by
  have e := (ι ℂ : Ds d →ₗ⁅ℂ⁆ _).map_lie (DirectSum.of (fun i => Gl (d i)) i (Matrix.single p q (1 : ℂ)))
    (DirectSum.of (fun i => Gl (d i)) k (Matrix.single r v (1 : ℂ)))
  rw [DirectSum.lie_of_of_ne _ hik, map_zero, LieRing.of_associative_ring_bracket] at e
  simp only [eb, eu, mi_ι]
  exact sub_eq_zero.1 e.symm

theorem eb_rel (i : Fin M) : GlRel (eb d i) := by
  intro a b c e
  have h := congrArg (mi d i) (glRel_eu (d i) a b c e)
  simp only [map_sub, map_mul] at h
  simp only [eb]
  rw [h]
  split_ifs <;> simp

end Blocks

section Final

attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

open UniversalEnvelopingAlgebra

theorem qdet_map {A A' : Type} [Ring A] [Algebra ℂ A] [Ring A'] [Algebra ℂ A'] (φ : A →ₐ[ℂ] A') {m : ℕ}
    (E : Fin m → Fin m → A) (u : ℂ) : φ (qdet E u) = qdet (fun a b => φ (E a b)) u := by
  unfold Formalism.REAL.qdet Formalism.REAL.qminor Formalism.REAL.Tm
  simp only [map_sum, map_mul, map_intCast, map_list_prod, List.map_ofFn]
  refine Finset.sum_congr rfl fun σ _ => ?_
  congr 3
  funext k
  simp only [Function.comp_apply, map_add]
  split_ifs <;> simp

variable {M : ℕ} {d : Fin M → ℕ}

def xs (a b : Σ i, Fin (d i)) : UD d := if h : a.1 = b.1 then eb d a.1 a.2 (h ▸ b.2) else 0

theorem xs_same (i : Fin M) (p q : Fin (d i)) : xs (d := d) ⟨i, p⟩ ⟨i, q⟩ = eb d i p q := by
  simp [xs]

def xl {n : ℕ} (e : (Σ i, Fin (d i)) ≃ Fin n) (p q : Fin n) : UD d := xs (e.symm p) (e.symm q)

theorem xl_apply {n : ℕ} (e : (Σ i, Fin (d i)) ≃ Fin n) (a b : Σ i, Fin (d i)) : xl e (e a) (e b) = xs a b := by
  simp [xl]

theorem levRel_xl {n : ℕ} (e : (Σ i, Fin (d i)) ≃ Fin n) {lev : Fin n → ℕ} (he : ∀ i p, lev (e ⟨i, p⟩) = (i : ℕ)) :
    LevRel lev (xl e) := by
  intro p q r v h1 h2
  obtain ⟨⟨i, p⟩, rfl⟩ := e.surjective p
  obtain ⟨⟨i', q⟩, rfl⟩ := e.surjective q
  obtain ⟨⟨k, r⟩, rfl⟩ := e.surjective r
  obtain ⟨⟨k', v⟩, rfl⟩ := e.surjective v
  rw [he, he] at h1 h2
  obtain rfl : i = i' := Fin.ext h1
  obtain rfl : k = k' := Fin.ext h2
  by_cases hik : i = k
  · subst hik
    simp only [xl_apply, xs_same, EmbeddingLike.apply_eq_iff_eq, Sigma.mk.injEq, heq_eq_eq, true_and]
    exact eb_rel d i p q r v
  · have n1 : (⟨i, q⟩ : Σ i, Fin (d i)) ≠ ⟨k, r⟩ := fun h => hik (congrArg Sigma.fst h)
    have n2 : (⟨k, v⟩ : Σ i, Fin (d i)) ≠ ⟨i, p⟩ := fun h => hik (congrArg Sigma.fst h).symm
    simp only [xl_apply, xs_same, EmbeddingLike.apply_eq_iff_eq, n1, n2, if_false, sub_zero]
    exact sub_eq_zero.2 (eb_comm d hik p q r v).eq

theorem glHom_comm {A : Type} [Ring A] [Algebra ℂ A] {m m' : ℕ} {E : Fin m → Fin m → A} {E' : Fin m' → Fin m' → A}
    (hE : GlRel E) (hE' : GlRel E') (hc : ∀ p q r v, Commute (E p q) (E' r v)) (Z : Gl m) (Z' : Gl m') :
    ⁅glHom E hE Z, glHom E' hE' Z'⁆ = 0 := by
  change ⁅glLin E Z, glLin E' Z'⁆ = 0
  rw [gl_eq_sum Z, gl_eq_sum Z']
  have h0 : ∀ p q r v, ⁅E p q, E' r v⁆ = 0 := fun p q r v => by
    rw [LieRing.of_associative_ring_bracket, (hc p q r v).eq, sub_self]
  simp only [sum_lie, lie_sum, smul_lie, lie_smul, map_sum, map_smul, glLin_single, h0, smul_zero, sum_const_zero]

end Final

end GlobalTheory.CompanionTheory.PairMult.CenScal

namespace GlobalTheory.CompanionTheory.PairMult

end GlobalTheory.CompanionTheory.PairMult
end
