import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IntMIffInt
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsBaseClassLevelAdapted
import Development.AbelianVarietyTheory.BlockTheory.JetGauges.ThetaSpanAdjoint
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HMatMulVecPerCrd
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.TensorLatticeSelfDualSemicharacterIndex
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.DualHalfLevelMarkingExistsAndMatch

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict GlobalTheory.Phase GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointCongruence

namespace GlobalTheory.Dict.RootsMove

section Abstract

variable {R Q : Type} [CommRing R] [AddCommGroup Q] [Module R Q] {n : ℕ}

private theorem inv_lemma' {R Q : Type} [CommRing R] [AddCommGroup Q] [Module R Q] {M k : ℕ}
    (hM : ∀ x : Q, (M : R) • x = 0) (hk : k.Coprime M) :
    ∃ c : R, ∀ x : Q, (c * k) • x = x := by
  refine ⟨(Nat.gcdA k M : R), fun x => ?_⟩
  have h := Nat.gcd_eq_gcd_ab k M
  rw [hk.gcd_eq_one] at h
  have h2 : ((1 : ℤ) : R) = ((k * Nat.gcdA k M + M * Nat.gcdB k M : ℤ) : R) := by
    exact_mod_cast congrArg (fun z : ℤ => (z : R)) h
  push_cast at h2
  have h3 : (Nat.gcdA k M : R) * k = 1 - (M : R) * Nat.gcdB k M := by linear_combination -h2
  rw [h3, sub_smul, one_smul, mul_smul, hM, sub_zero]

private theorem sum_smul_sum_smul_eq_mul_apply {R Q : Type} [CommRing R] [AddCommGroup Q] [Module R Q] {n : ℕ}
    (c d : Matrix (Fin n) (Fin n) R) (q : Fin n → Q) (i : Fin n) :
    ∑ j, c i j • ∑ l, d j l • q l = ∑ l, (c * d) i l • q l := by
  simp only [Matrix.mul_apply, Finset.smul_sum, Finset.sum_smul, mul_smul]
  exact Finset.sum_comm

private theorem sum_smul_one_apply_smul {R Q : Type} [CommRing R] [AddCommGroup Q] [Module R Q] {n : ℕ}
    (m : R) (q : Fin n → Q) (i : Fin n) :
    ∑ l, (m • (1 : Matrix (Fin n) (Fin n) R)) i l • q l = m • q i := by
  simp [Matrix.one_apply]

theorem exists_perm {M k m : ℕ} (hM : ∀ x : Q, (M : R) • x = 0) (hk : k.Coprime M) (hm : m.Coprime M)
    (a b : Matrix (Fin n) (Fin n) R) (hab : a * b = (m : R) • 1) (hba : b * a = (m : R) • 1) :
    ∃ e : (Fin n → Q) ≃ (Fin n → Q), ∀ q i, (k : R) • e q i = ∑ j, a i j • q j := by
  obtain ⟨ck, hck⟩ := inv_lemma' hM hk
  obtain ⟨cm, hcm⟩ := inv_lemma' hM hm
  have hfix : ∀ x : Q, ck • (cm * k) • (m : R) • x = x := fun x => by
    rw [smul_smul, smul_smul, show ck * (cm * k) * m = (ck * k) * (cm * m) by ring, mul_smul, hcm, hck]
  refine ⟨{ toFun := fun q i => ck • ∑ j, a i j • q j
            invFun := fun q i => (cm * k) • ∑ j, b i j • q j
            left_inv := ?_
            right_inv := ?_ }, fun q i => ?_⟩
  · intro q
    funext i
    show (cm * k) • ∑ j, b i j • (ck • ∑ l, a j l • q l) = q i
    have e1 : ∑ j, b i j • (ck • ∑ l, a j l • q l) = ck • ∑ j, b i j • ∑ l, a j l • q l := by
      rw [Finset.smul_sum]
      exact Finset.sum_congr rfl fun j _ => smul_comm _ _ _
    rw [e1, sum_smul_sum_smul_eq_mul_apply, hba, sum_smul_one_apply_smul, smul_comm, hfix]
  · intro q
    funext i
    show ck • ∑ j, a i j • ((cm * k) • ∑ l, b j l • q l) = q i
    have e1 : ∑ j, a i j • ((cm * k) • ∑ l, b j l • q l) = (cm * k) • ∑ j, a i j • ∑ l, b j l • q l := by
      rw [Finset.smul_sum]
      exact Finset.sum_congr rfl fun j _ => smul_comm _ _ _
    rw [e1, sum_smul_sum_smul_eq_mul_apply, hab, sum_smul_one_apply_smul, hfix]
  · show (k : R) • ck • ∑ j, a i j • q j = _
    rw [smul_smul, mul_comm, hck]

theorem int_of_coprime {x : ℚ} {s t : ℕ} (h : s.Coprime t) {a b : ℤ} (ha : (s : ℚ) * x = a)
    (hb : (t : ℚ) * x = b) : ∃ c : ℤ, x = c := by
  refine ⟨Nat.gcdA s t * a + Nat.gcdB s t * b, ?_⟩
  have h' := Nat.gcd_eq_gcd_ab s t
  rw [h.gcd_eq_one] at h'
  have h'' : ((1 : ℤ) : ℚ) = ((s * Nat.gcdA s t + t * Nat.gcdB s t : ℤ) : ℚ) := by
    exact_mod_cast congrArg (fun z : ℤ => (z : ℚ)) h'
  push_cast at h'' ⊢
  rw [← ha, ← hb]
  linear_combination x * h''

private theorem heisS_heisS {K1 K2 : Type} [Fintype K1] [Fintype K2] (a b a' b' : Matrix K1 K2 ℚ)
    (φ : Matrix K1 K2 ℚ → ℂ) :
    heisS a b (heisS a' b' φ) =
      cexp (Real.pi * I * ((∑ k, (a k ⬝ᵥ b' k - a' k ⬝ᵥ b k) : ℚ) : ℂ)) •
        heisS (a + a') (b + b') φ := by
  funext x
  have hq : (∑ k, (2 * ((x - b) k ⬝ᵥ a' k) - a' k ⬝ᵥ b' k)) +
      (∑ k, (2 * (x k ⬝ᵥ a k) - a k ⬝ᵥ b k)) =
      (∑ k, (a k ⬝ᵥ b' k - a' k ⬝ᵥ b k)) +
        ∑ k, (2 * (x k ⬝ᵥ (a + a') k) - (a + a') k ⬝ᵥ (b + b') k) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    have e1 : (x - b) k = x k - b k := rfl
    have e2 : (a + a') k = a k + a' k := rfl
    have e3 : (b + b') k = b k + b' k := rfl
    rw [e1, e2, e3]
    simp only [sub_dotProduct, add_dotProduct, dotProduct_add, dotProduct_comm (b k) (a' k)]
    ring
  simp only [heisS, Pi.smul_apply, smul_eq_mul]
  rw [sub_sub, _root_.mul_assoc, ← Complex.exp_add, _root_.mul_left_comm, ← Complex.exp_add, ← _root_.mul_add,
    ← _root_.mul_add]
  congr 3
  exact_mod_cast hq

end Abstract

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r n g : ℕ} {H : Host E} {Dw : Datum H}
  {l : Geo.Tor.Level H} {X : Data E r} {L : Lt E r}

theorem heisG_comp {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} (hs : IsSympl X bas)
    (y y' : Matrix (Fin n) (Fin r) E) {φ : TF n g} (hφ : IsSB φ) : heisG X bas y (heisG X bas y' φ) =
      cexp (-(Real.pi * I * ((∑ k, EF X (y k) (y' k) : ℚ) : ℂ))) • heisG X bas (y + y') φ := by
  have hA : (Matrix.of fun k i => crd X bas ((y + y') k) (Sum.inl i) : Matrix (Fin n) (Fin g) ℚ) =
      Matrix.of (fun k i => crd X bas (y k) (Sum.inl i)) +
        Matrix.of (fun k i => crd X bas (y' k) (Sum.inl i)) := by
    ext k i
    show crd X bas (y k + y' k) _ = _
    rw [crd_add hs]
    rfl
  have hB : (Matrix.of fun k i => crd X bas ((y + y') k) (Sum.inr i) : Matrix (Fin n) (Fin g) ℚ) =
      Matrix.of (fun k i => crd X bas (y k) (Sum.inr i)) +
        Matrix.of (fun k i => crd X bas (y' k) (Sum.inr i)) := by
    ext k i
    show crd X bas (y k + y' k) _ = _
    rw [crd_add hs]
    rfl
  have hE : (∑ k, ((Matrix.of fun k i => crd X bas (y k) (Sum.inl i) : Matrix (Fin n) (Fin g) ℚ) k ⬝ᵥ
        (Matrix.of fun k i => crd X bas (y' k) (Sum.inr i) : Matrix (Fin n) (Fin g) ℚ) k -
        (Matrix.of fun k i => crd X bas (y' k) (Sum.inl i) : Matrix (Fin n) (Fin g) ℚ) k ⬝ᵥ
        (Matrix.of fun k i => crd X bas (y k) (Sum.inr i) : Matrix (Fin n) (Fin g) ℚ) k)) =
      -∑ k, EF X (y k) (y' k) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [EF_crd hs]
    simp only [dotProduct, Matrix.of_apply, neg_neg, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  simp only [heisG]
  rw [heisS_heisS, hA, hB, hE]
  push_cast
  ring_nf

theorem sumEF_smul (s t : ℕ) (y y' : Matrix (Fin n) (Fin r) E) :
    ∑ k, EF X (((s : E) • y) k) (((t : E) • y') k) = s * t * ∑ k, EF X (y k) (y' k) := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  show EF X ((s : E) • y k) ((t : E) • y' k) = _
  have hs' : ((s : E) • y k) = ((s : ℚ) • y k) := by
    rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
  have ht' : ((t : E) • y' k) = ((t : ℚ) • y' k) := by
    rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
  rw [hs', ht']
  change EFBil X ((s : ℚ) • y k) ((t : ℚ) • y' k) = _
  rw [LinearMap.map_smul₂, LinearMap.map_smul]
  change (s : ℚ) • (t : ℚ) • EF X (y k) (y' k) = _
  simp only [smul_eq_mul]
  ring

theorem heisG_add_two {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} (hs : IsSympl X bas) (hL : SelfD X L) {M : ℕ}
    {Λ : Lt E n} (hΛ : Λ ∈ Vset E n M) {w : E} (hw : IsIntegral ℤ w) {u : TF n g}
    (hu : IsVac X bas w (tens Λ L) u) (y : Matrix (Fin n) (Fin r) E) {d : Matrix (Fin n) (Fin r) E}
    (hd : d ∈ tens Λ L) {c : ℤ} (hc : ∑ k, EF X (y k) (d k) = c) :
    heisG X bas (y + ((2 : ℕ) : E) • d) u = heisG X bas y u := by
  obtain ⟨hsb, -, hfix⟩ := hu
  have h2d : ((2 : ℕ) : E) • d ∈ tens Λ L := by
    rw [Nat.cast_smul_eq_nsmul]
    exact AddSubgroup.nsmul_mem _ hd 2
  obtain ⟨m, hm⟩ := (TensLat.tens_selfDual hΛ hL d).mp hd (w • d) (TensLat.smul_mem_tens hΛ hw hd)
  have heps : epsW X w (((2 : ℕ) : E) • d) = 1 := by
    unfold epsW
    have hsum : ∑ k, EF X ((((2 : ℕ) : E) • d) k) (w • (((2 : ℕ) : E) • d) k) =
        ∑ k, EF X ((((2 : ℕ) : E) • d) k) ((((2 : ℕ) : E) • (w • d)) k) := by
      refine Finset.sum_congr rfl fun k _ => ?_
      congr 1
      show w • ((2 : ℕ) : E) • d k = ((2 : ℕ) : E) • w • d k
      exact smul_comm _ _ _
    have hq : ∑ k, EF X ((((2 : ℕ) : E) • d) k) ((((2 : ℕ) : E) • (w • d)) k) = ((4 * m : ℤ) : ℚ) := by
      rw [sumEF_smul, hm]
      push_cast
      ring
    rw [hsum, hq]
    have e : (Real.pi : ℂ) * I * (((4 * m : ℤ) : ℚ) : ℂ) = ((2 * m : ℤ) : ℂ) * (2 * Real.pi * I) := by
      push_cast
      ring
    rw [e]
    exact Complex.exp_int_mul_two_pi_mul_I _
  have h2fix : heisG X bas (((2 : ℕ) : E) • d) u = u := by
    have := hfix _ h2d
    rwa [heps, one_smul] at this
  have h1 := sumEF_smul (X := X) 1 2 y d
  simp only [Nat.cast_one, one_smul] at h1
  have hexp : cexp (-(Real.pi * I * ((∑ k, EF X (y k) ((((2 : ℕ) : E) • d) k) : ℚ) : ℂ))) = 1 := by
    have hq : ∑ k, EF X (y k) ((((2 : ℕ) : E) • d) k) = ((2 * c : ℤ) : ℚ) := by
      rw [h1, hc]
      push_cast
      ring
    rw [hq]
    have e : -((Real.pi : ℂ) * I * (((2 * c : ℤ) : ℚ) : ℂ)) = ((-c : ℤ) : ℂ) * (2 * Real.pi * I) := by
      push_cast
      ring
    rw [e]
    exact Complex.exp_int_mul_two_pi_mul_I _
  have hcomp := heisG_comp hs y (((2 : ℕ) : E) • d) hsb
  rw [h2fix, hexp, one_smul] at hcomp
  exact hcomp.symm

omit [IsCMField E] in

theorem mul_mem_tens {Λ Λ' : Lt E n} {h : Matrix (Fin n) (Fin n) E} (hh : ∀ v ∈ Λ, h *ᵥ v ∈ Λ')
    {y : Matrix (Fin n) (Fin r) E} (hy : y ∈ tens Λ L) : h * y ∈ tens Λ' L := by
  let f : Matrix (Fin n) (Fin r) E →+ Matrix (Fin n) (Fin r) E :=
    { toFun := fun z => h * z
      map_zero' := Matrix.mul_zero h
      map_add' := fun z z' => Matrix.mul_add h z z' }
  have key : tens Λ L ≤ (tens Λ' L).comap f := by
    refine TensLat.tens_le fun v hv u hu => ?_
    show h * vecMulVec v u ∈ tens Λ' L
    have e : h * vecMulVec v u = vecMulVec (h *ᵥ v) u := by
      ext i j
      simp [Matrix.mul_apply, vecMulVec_apply, mulVec, dotProduct, Finset.sum_mul]
      exact Finset.sum_congr rfl fun _ _ => by ring
    rw [e]
    exact TensLat.pure_mem (hh v hv) hu
  exact key hy

omit [IsCMField E] in

theorem smul_mem_tens' {Λ Λ' : Lt E n} {s : E} (hh : ∀ v ∈ Λ, s • v ∈ Λ')
    {y : Matrix (Fin n) (Fin r) E} (hy : y ∈ tens Λ L) : s • y ∈ tens Λ' L := by
  have key : tens Λ L ≤ (tens Λ' L).comap
      (DistribSMul.toAddMonoidHom (Matrix (Fin n) (Fin r) E) s) := by
    refine TensLat.tens_le fun v hv u hu => ?_
    show s • vecMulVec v u ∈ tens Λ' L
    have e : s • vecMulVec v u = vecMulVec (s • v) u := by
      ext i j
      simp [vecMulVec_apply]
      ring
    rw [e]
    exact TensLat.pure_mem (hh v hv) hu
  exact key hy

theorem exists_int {M : ℕ} {Λ Λ' : Lt E n} (hΛ : Λ ∈ Vset E n M) (hΛ' : Λ' ∈ Vset E n M)
    {h : Matrix (Fin n) (Fin n) E} (hh : Moves h Λ Λ') :
    ∃ (k : ℕ) (a : Matrix (Fin n) (Fin n) (𝓞 E)), k.Coprime M ∧ ∀ i j, (a i j : E) = (k : E) * h i j := by
  obtain ⟨-, -, s, -, hsc, -, hs2⟩ := hΛ
  obtain ⟨-, -, s', -, hsc', hs1', -⟩ := hΛ'
  have hcol : ∀ j, ∃ c : Fin n → 𝓞 E, ∀ i, (c i : E) = ((s * s' : ℕ) : E) * h i j := by
    intro j
    have he : (Pi.single j (1 : E) : Fin n → E) ∈ stdL E n := Submodule.subset_span ⟨j, rfl⟩
    have h3 : (s' : E) • h *ᵥ ((s : E) • (Pi.single j (1 : E) : Fin n → E)) ∈ stdL E n :=
      hs1' _ ((hh _).mp (hs2 _ he))
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 E)).mp h3
    refine ⟨c, fun i => ?_⟩
    have hci := congrFun hc i
    simp only [Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_ite, smul_zero,
      Finset.sum_ite_eq, Finset.mem_univ, if_true, mulVec_smul, mulVec_single_one] at hci
    rw [Algebra.smul_def, _root_.mul_one] at hci
    rw [show (c i : E) = algebraMap (𝓞 E) E (c i) from rfl, hci]
    simp only [smul_eq_mul, Matrix.col_apply]
    push_cast
    ring
  choose c hc using hcol
  exact ⟨s * s', Matrix.of fun i j => c j i, Nat.Coprime.mul_left hsc hsc', fun i j => hc j i⟩

theorem exists_levPerm {Λ Λ' : Lt E n} (hΛ : Λ ∈ Vset E n l.M) (hΛ' : Λ' ∈ Vset E n l.M)
    {h : Matrix (Fin n) (Fin n) E} (hu : ccT h * h = 1) (hh : Moves h Λ Λ') :
    ∃ e : (Fin n → LevQ Dw l) ≃ (Fin n → LevQ Dw l), ∀ q, LevMoves h q (e q) := by
  obtain ⟨k, a, hk, ha⟩ := exists_int hΛ hΛ' hh
  have hinv : h * ccT h = 1 := _root_.mul_eq_one_comm.mp hu
  have hh' : Moves (ccT h) Λ' Λ := by
    intro v
    rw [hh (ccT h *ᵥ v), mulVec_mulVec, hinv, one_mulVec]
  obtain ⟨k', b, hk', hb⟩ := exists_int hΛ' hΛ hh'
  have key : ∀ (A B : Matrix (Fin n) (Fin n) E), A * B = 1 → ∀ (c d : Matrix (Fin n) (Fin n) (𝓞 E))
      (kc kd : ℕ), (∀ i j, (c i j : E) = (kc : E) * A i j) → (∀ i j, (d i j : E) = (kd : E) * B i j) →
      c * d = ((kc * kd : ℕ) : 𝓞 E) • 1 := by
    intro A B hAB c d kc kd hc hd
    ext i j
    have e1 : ((c * d) i j : E) = ((kc * kd : ℕ) : E) * (A * B) i j := by
      simp only [Matrix.mul_apply, map_sum, map_mul]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [show (algebraMap (𝓞 E) E (c i l)) = (c i l : E) from rfl,
        show (algebraMap (𝓞 E) E (d l j)) = (d l j : E) from rfl, hc, hd]
      push_cast
      ring
    rw [show (((c * d) i j : 𝓞 E) : E) = ((c * d) i j : E) from rfl, e1, hAB]
    simp only [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    split_ifs <;> simp
  have hab := key h (ccT h) hinv a b k k' ha hb
  have hba := key (ccT h) h hu b a k' k hb ha
  rw [Nat.mul_comm k' k] at hba
  have hMb : (l.M : 𝓞 E) ∈ l.Mb := by
    have : (l.M : 𝓞 E) ∈ l.Mb * l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := by
      rw [l.prod]
      exact Ideal.mem_span_singleton_self _
    exact (Ideal.mul_le_inf (I := l.Mb) (J := l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)) this).1
  have hM : ∀ x : LevQ Dw l, ((l.M : ℕ) : 𝓞 E) • x = 0 := by
    intro x
    refine Submodule.Quotient.induction_on _ x fun z => ?_
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    exact Submodule.smul_mem_smul hMb trivial
  obtain ⟨e, he⟩ := exists_perm hM hk (Nat.Coprime.mul_left hk hk') a b hab hba
  exact ⟨e, fun q => ⟨k, a, hk, ha, fun i => he q i⟩⟩

theorem exists_pow {mk : Dw.La →ₗ[𝓞 E] (Fin r → E)} {N : ℕ}
    {Y : (Fin n → LevQ Dw l) → Matrix (Fin n) (Fin r) E} (hY : IsRoots l L mk N Y) (q : Fin n → LevQ Dw l) :
    ∃ j₀ : ℕ, ∀ j, j₀ ≤ j → ∀ s ∈ l.Mb, ∃ U : Matrix (Fin n) (Fin r) E, (∀ b, U b ∈ L) ∧
      ((s : E) ^ j) • Y q = ((2 * N : ℕ) : E) • U := by
  have hb : ∀ b, ∃ j : ℕ, ∀ s ∈ l.Mb ^ j, ∃ u ∈ L, s • Y q b = (2 * N) • u := fun b => (hY q b).2
  choose j hj using hb
  refine ⟨Finset.univ.sup j, fun i hi s hs => ?_⟩
  have hu : ∀ b, ∃ u ∈ L, (s ^ i) • Y q b = (2 * N) • u := fun b =>
    hj b _ (Ideal.pow_le_pow_right (le_trans (Finset.le_sup (Finset.mem_univ b)) hi)
      (Ideal.pow_mem_pow hs i))
  choose U hUL hU using hu
  refine ⟨fun b => U b, hUL, ?_⟩
  funext b
  show ((s : E) ^ i) • Y q b = ((2 * N : ℕ) : E) • U b
  rw [Nat.cast_smul_eq_nsmul, ← hU b, ← algebraMap_smul E (s ^ i) (Y q b), map_pow]

theorem ef_int (hL : SelfD X L) {mk : Dw.La →ₗ[𝓞 E] (Fin r → E)} (hmk : ∀ a, mk a ∈ L) {y d u : Fin r → E}
    {a : Dw.La} (ha : a ∈ Mfr l • (⊤ : Submodule (𝓞 E) Dw.La)) (hy : y - (l.M : E)⁻¹ • mk a ∈ L) (hd : d ∈ L)
    (hu : u ∈ L) {s : 𝓞 E} (hs : 1 - s ∈ Mfr l) (hsd : (s : E) • d = (l.M : E) • u) : ∃ c : ℤ, EF X y d = c := by
  obtain ⟨-, hself⟩ := hL
  have hint : ∀ x ∈ L, ∀ z ∈ L, ∃ k : ℤ, EF X x z = k := fun x hx z hz => (hself x).mp hx z hz
  have hM0 : (l.M : E) ≠ 0 := by
    have h3 := l.three_le
    exact_mod_cast (show l.M ≠ 0 by omega)
  have addL : ∀ v v' z, EF X (v + v') z = EF X v z + EF X v' z := fun v v' z => by
    change EFBil X (v + v') z = EFBil X v z + EFBil X v' z
    rw [LinearMap.map_add₂]
  have addR : ∀ v z z', EF X v (z + z') = EF X v z + EF X v z' := fun v z z' => by
    change EFBil X v (z + z') = EFBil X v z + EFBil X v z'
    rw [LinearMap.map_add]
  have hs' : 1 - s ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := hs
  obtain ⟨p, hp, hpt⟩ := (Ideal.mem_map_iff_of_surjective (H.bar : 𝓞 E →+* 𝓞 E) H.bar.surjective).mp hs'
  have hpt' : H.bar p = 1 - s := hpt
  have hccp : cc (p : E) = 1 - (s : E) := by
    have hb := H.bar_eq p
    rw [hpt'] at hb
    change IsCMField.complexConj E (p : E) = _
    rw [← hb]
    push_cast
    rfl
  have hpa : p • a ∈ (Ideal.span {(l.M : 𝓞 E)}) • (⊤ : Submodule (𝓞 E) Dw.La) := by
    rw [← l.prod, Submodule.mul_smul]
    exact Submodule.smul_mem_smul hp ha
  rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at hpa
  obtain ⟨a', -, ha'⟩ := hpa
  have e3 : (p : E) • ((l.M : E)⁻¹ • mk a) = mk a' := by
    have h1 : (p : E) • mk a = mk (p • a) := by
      rw [LinearMap.map_smul]
      exact algebraMap_smul E p (mk a)
    have h2 : mk ((l.M : 𝓞 E) • a') = (l.M : E) • mk a' := by
      rw [LinearMap.map_smul, ← algebraMap_smul E (l.M : 𝓞 E) (mk a'), map_natCast]
    rw [smul_comm, h1, ← ha', h2, smul_smul, inv_mul_cancel₀ hM0, one_smul]
  have hccM : cc ((l.M : E)⁻¹) = (l.M : E)⁻¹ := by
    change IsCMField.complexConj E ((l.M : E)⁻¹) = _
    rw [map_inv₀, map_natCast]
  have split1 : EF X y d = EF X (y - (l.M : E)⁻¹ • mk a) d + EF X ((l.M : E)⁻¹ • mk a) d := by
    rw [← addL, sub_add_cancel]
  have split2 : EF X ((l.M : E)⁻¹ • mk a) d =
      EF X ((l.M : E)⁻¹ • mk a) ((s : E) • d) + EF X ((l.M : E)⁻¹ • mk a) ((1 - (s : E)) • d) := by
    rw [← addR, ← add_smul, add_sub_cancel, one_smul]
  have t2 : EF X ((l.M : E)⁻¹ • mk a) ((s : E) • d) = EF X (mk a) u := by
    rw [hsd, TensLat.EF_smul X, hccM, smul_smul, inv_mul_cancel₀ hM0, one_smul]
  have t3 : EF X ((l.M : E)⁻¹ • mk a) ((1 - (s : E)) • d) = EF X (mk a') d := by
    rw [← hccp, ← TensLat.EF_smul X, e3]
  obtain ⟨k1, hk1⟩ := hint _ hy d hd
  obtain ⟨k2, hk2⟩ := hint _ (hmk a) u hu
  obtain ⟨k3, hk3⟩ := hint _ (hmk a') d hd
  refine ⟨k1 + k2 + k3, ?_⟩
  rw [split1, split2, t2, t3, hk1, hk2, hk3]
  push_cast
  ring

private theorem mem_of_natCast_smul_mem_of_coprime {F V : Type} [Field F] [AddCommGroup V] [Module F V] (G : AddSubgroup V) {p q : ℕ}
    (hpq : p.Coprime q) {v : V} (hp : (p : F) • v ∈ G) (hq : (q : F) • v ∈ G) : v ∈ G := by
  have h := Nat.gcd_eq_gcd_ab p q
  rw [hpq.gcd_eq_one] at h
  have h2 : ((Nat.gcdA p q : ℤ) : F) * p + ((Nat.gcdB p q : ℤ) : F) * q = 1 := by
    have := congrArg (fun z : ℤ => (z : F)) h
    push_cast at this
    linear_combination -this
  have hv : v = Nat.gcdA p q • ((p : F) • v) + Nat.gcdB p q • ((q : F) • v) := by
    rw [← Int.cast_smul_eq_zsmul F, ← Int.cast_smul_eq_zsmul F, smul_smul, smul_smul, ← add_smul, h2,
      one_smul]
  rw [hv]
  exact add_mem (AddSubgroup.zsmul_mem _ hp _) (AddSubgroup.zsmul_mem _ hq _)

private theorem mem_mul_smul_of_mem_smul_of_sup_eq_top {R V : Type} [CommRing R] [AddCommGroup V] [Module R V] {I J : Ideal R}
    {P : Submodule R V} (hIJ : I ⊔ J = ⊤) {x : V} (hI : x ∈ I • P) (hJ : x ∈ J • P) :
    x ∈ (I * J) • P := by
  have h1 : (1 : R) ∈ I ⊔ J := by
    rw [hIJ]
    exact Submodule.mem_top
  obtain ⟨i, hi, j, hj, hij⟩ := Submodule.mem_sup.mp h1
  have hx : x = i • x + j • x := by rw [← add_smul, hij, one_smul]
  rw [hx]
  refine add_mem ?_ ?_
  · rw [Submodule.mul_smul]
    exact Submodule.smul_mem_smul hi hJ
  · rw [_root_.mul_comm, Submodule.mul_smul]
    exact Submodule.smul_mem_smul hj hI

private theorem map_mul_row_mem_of_rows_mem {F : Type} [Field F] [NumberField F] {m s : ℕ} {L : Submodule (𝓞 F) (Fin s → F)}
    (B : Matrix (Fin m) (Fin m) (𝓞 F)) (W : Matrix (Fin m) (Fin s) F) (hW : ∀ i, W i ∈ L) (i : Fin m) :
    (B.map (algebraMap (𝓞 F) F) * W) i ∈ L := by
  have e : (B.map (algebraMap (𝓞 F) F) * W) i = ∑ j, B i j • W j := by
    funext c
    simp only [Matrix.mul_apply, Matrix.map_apply, Finset.sum_apply, Pi.smul_apply, Algebra.smul_def]
  rw [e]
  exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hW j)

private theorem natCast_smul_mem_of_span_smul_stdLat_le {F : Type} [Field F] [NumberField F] {m N : ℕ} {Λ : Lt F m}
    (hle : Ideal.span {(N : 𝓞 F)} • stdLat F m ≤ (⟨Λ⟩ : GenLat F m).Ln) :
    ∀ v ∈ stdL F m, (N : F) • v ∈ Λ := by
  intro v hv
  have hv' : v ∈ stdLat F m := by
    refine Submodule.span_le.mpr ?_ hv
    rintro _ ⟨j, rfl⟩
    refine Submodule.mem_pi.mpr fun i _ => ?_
    rw [Submodule.mem_one]
    by_cases hij : i = j
    · subst hij
      exact ⟨1, by simp⟩
    · exact ⟨0, by simp [hij]⟩
  have h1 := hle (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self (N : 𝓞 F)) hv')
  have h2 : (N : 𝓞 F) • v = (N : F) • v := by
    rw [← algebraMap_smul F (N : 𝓞 F) v, map_natCast]
  rw [← h2]
  exact h1.1

private theorem matrix_mul_row_eq_sum_smul {F : Type} [Field F] {m s : ℕ} (A : Matrix (Fin m) (Fin m) F)
    (Z : Matrix (Fin m) (Fin s) F) (i : Fin m) :
    (A * Z) i = ∑ j, A i j • Z j := by
  funext c
  simp [Matrix.mul_apply, Finset.sum_apply]

theorem roots_move : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (n : ℕ), IsSympl X bas → Even n → ∀ L : Lt E r, SelfD X L → ∀ mk : Dw.La →ₗ[𝓞 E] (Fin r → E), IsMark l L mk → ∀ h : Matrix (Fin n) (Fin n) E, ccT h * h = 1 → ∀ Λ ∈ Vset E n l.M, ∀ Λ' ∈ Vset E n l.M, Moves h Λ Λ' → ∀ N N' : ℕ, (⟨Λ⟩ : GenLat E n).LevOK N l.M → (⟨Λ'⟩ : GenLat E n).LevOK N' l.M → ∀ Y Y' : (Fin n → LevQ Dw l) → Matrix (Fin n) (Fin r) E, IsRoots l L mk N Y → IsRoots l L mk N' Y' → (∃ e : (Fin n → LevQ Dw l) ≃ (Fin n → LevQ Dw l), ∀ q, LevMoves h q (e q)) ∧ ∀ q q', LevMoves h q q' → ∀ u : TF n g, IsVac X bas (H.w0 : E) (tens Λ' L) u → heisG X bas (Y' q') u = heisG X bas (h * Y q) u := by
  intro E _ _ _ H Dw l r X g bas n hs _ L hL mk hmk h hu Λ hΛ Λ' hΛ' hh N N' hN hN' Y Y' hY hY'
  refine ⟨exists_levPerm (Dw := Dw) hΛ hΛ' hu hh, ?_⟩
  intro q q' hmv u hvac
  obtain ⟨k1, g1, hk1, hg1, hq⟩ := hmv
  have cs : ∀ (x : 𝓞 E) (v : Fin r → E), x • v = (x : E) • v := fun x v => (algebraMap_smul E x v).symm
  have hM0 : (l.M : E) ≠ 0 := by
    have h3 := l.three_le
    exact_mod_cast (show l.M ≠ 0 by omega)
  have hMc : ((l.M : 𝓞 E) : E) = (l.M : E) := map_natCast (algebraMap (𝓞 E) E) l.M
  have hk1c : ((k1 : 𝓞 E) : E) = (k1 : E) := map_natCast (algebraMap (𝓞 E) E) k1
  have hMb : (l.M : 𝓞 E) ∈ l.Mb := by
    have : (l.M : 𝓞 E) ∈ l.Mb * l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := by
      rw [l.prod]
      exact Ideal.mem_span_singleton_self _
    exact (Ideal.mul_le_inf (I := l.Mb) (J := l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)) this).1
  have h1top : (1 : 𝓞 E) ∈ l.Mb ⊔ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := by
    rw [l.coprime]
    exact Submodule.mem_top
  obtain ⟨s0, hs0, t0, ht0, hst⟩ := Submodule.mem_sup.mp h1top
  obtain ⟨j1, hj1⟩ := exists_pow hY q
  obtain ⟨j2, hj2⟩ := exists_pow hY' q'
  obtain ⟨U1, hU1L, hU1⟩ := hj1 (max j1 j2) (le_max_left _ _) s0 hs0
  obtain ⟨U2, hU2L, hU2⟩ := hj2 (max j1 j2) (le_max_right _ _) s0 hs0
  obtain ⟨V1, hV1L, hV1⟩ := hj1 (max j1 j2) (le_max_left _ _) _ hMb
  obtain ⟨V2, hV2L, hV2⟩ := hj2 (max j1 j2) (le_max_right _ _) _ hMb
  rw [hMc] at hV1 hV2
  obtain ⟨J, hJ⟩ : ∃ J, J = max j1 j2 := ⟨_, rfl⟩
  rw [← hJ] at hU1 hU2 hV1 hV2
  have h1s : 1 - s0 ^ J ∈ Mfr l := by
    have hd := sub_dvd_pow_sub_pow (1 : 𝓞 E) s0 J
    rw [one_pow] at hd
    obtain ⟨c, hc⟩ := hd
    rw [hc]
    have : 1 - s0 = t0 := by rw [← hst]; ring
    rw [this]
    exact Ideal.mul_mem_right c _ ht0
  obtain ⟨-, ⟨n1, hn1⟩, hNle⟩ := hN
  obtain ⟨-, ⟨n2, hn2⟩, hN'le⟩ := hN'
  have hM2 : Nat.Coprime l.M 2 := by
    have ho := l.odd
    rw [Nat.odd_iff] at ho
    exact Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 (by omega))
  obtain ⟨t, -, htc, -, ht2⟩ := hΛ'.2.2

  have hrep : ∀ j, ∃ a ∈ Mfr l • (⊤ : Submodule (𝓞 E) Dw.La), Submodule.Quotient.mk a = q j ∧
      Y q j - ((l.M : E)⁻¹) • mk a ∈ L := fun j => (hY q j).1
  choose A hAm hAq hAL using hrep
  have hrep' : ∀ j, ∃ a ∈ Mfr l • (⊤ : Submodule (𝓞 E) Dw.La), Submodule.Quotient.mk a = q' j ∧
      Y' q' j - ((l.M : E)⁻¹) • mk a ∈ L := fun j => (hY' q' j).1
  choose A' hA'm hA'q hA'L using hrep'
  have hC : ∀ i, ∃ Ci : Dw.La, (l.M : 𝓞 E) • Ci = (k1 : 𝓞 E) • A' i - ∑ j, g1 i j • A j := by
    intro i
    have hxb : (k1 : 𝓞 E) • A' i - ∑ j, g1 i j • A j ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La) := by
      have h0 : (l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)).mkQ ((k1 : 𝓞 E) • A' i - ∑ j, g1 i j • A j) = 0 := by
        simp only [map_sub, map_smul, map_sum, Submodule.mkQ_apply, hAq, hA'q]
        rw [hq i, sub_self]
      exact (Submodule.Quotient.mk_eq_zero _).mp h0
    have hxf : (k1 : 𝓞 E) • A' i - ∑ j, g1 i j • A j ∈
        l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) Dw.La) :=
      sub_mem (Submodule.smul_mem _ _ (hA'm i)) (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hAm j))
    have hx := mem_mul_smul_of_mem_smul_of_sup_eq_top l.coprime hxb hxf
    rw [l.prod, Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at hx
    obtain ⟨Ci, -, hCi⟩ := hx
    exact ⟨Ci, hCi⟩
  choose C hC using hC
  obtain ⟨D, hD⟩ : ∃ D : Matrix (Fin n) (Fin r) E, D = Y' q' - h * Y q := ⟨_, rfl⟩
  obtain ⟨W, hW⟩ : ∃ W : Matrix (Fin n) (Fin r) E, W = (k1 : E) • D := ⟨_, rfl⟩
  obtain ⟨d, hd⟩ : ∃ d : Matrix (Fin n) (Fin r) E, d = (2 : E)⁻¹ • D := ⟨_, rfl⟩
  have hWi : ∀ i, W i = (k1 : E) • Y' q' i - ∑ j, (g1 i j : E) • Y q j := by
    intro i
    rw [hW, hD]
    show (k1 : E) • (Y' q' i - (h * Y q) i) = _
    rw [matrix_mul_row_eq_sum_smul, smul_sub, Finset.smul_sum]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_smul, hg1]
  have hWL : ∀ i, W i ∈ L := by
    intro i
    have hCE : (l.M : E) • mk (C i) = (k1 : E) • mk (A' i) - ∑ j, (g1 i j : E) • mk (A j) := by
      have := congrArg mk (hC i)
      simp only [map_sub, map_sum, LinearMap.map_smul, cs, hMc, hk1c] at this
      exact this
    have hmkC : mk (C i) = (l.M : E)⁻¹ • ((k1 : E) • mk (A' i) - ∑ j, (g1 i j : E) • mk (A j)) := by
      rw [← hCE, smul_smul, inv_mul_cancel₀ hM0, one_smul]
    have hsplit : W i = mk (C i) + ((k1 : E) • (Y' q' i - (l.M : E)⁻¹ • mk (A' i)) -
        ∑ j, (g1 i j : E) • (Y q j - (l.M : E)⁻¹ • mk (A j))) := by
      rw [hWi, hmkC]
      simp only [smul_sub, Finset.smul_sum, Finset.sum_sub_distrib, smul_comm ((l.M : E)⁻¹)]
      abel
    rw [hsplit]
    refine add_mem (hmk.mem _) (sub_mem ?_ (Submodule.sum_mem _ fun j _ => ?_))
    · rw [Nat.cast_smul_eq_nsmul]
      exact Submodule.smul_of_tower_mem _ k1 (hA'L i)
    · rw [← cs]
      exact Submodule.smul_mem _ _ (hAL j)
  have hg : g1.map (algebraMap (𝓞 E) E) = (k1 : E) • h := by
    ext i j
    rw [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, ← hg1]
  obtain ⟨Um, hUm⟩ : ∃ Um : Matrix (Fin n) (Fin r) E, Um = ((2 * n2 * k1 : ℕ) : E) • U2 -
      ((2 * n1 : ℕ) : E) • (g1.map (algebraMap (𝓞 E) E) * U1) := ⟨_, rfl⟩
  have hUmL : ∀ i, Um i ∈ L := by
    intro i
    rw [hUm]
    show ((2 * n2 * k1 : ℕ) : E) • U2 i - ((2 * n1 : ℕ) : E) • (g1.map (algebraMap (𝓞 E) E) * U1) i ∈ L
    refine sub_mem ?_ ?_
    · rw [Nat.cast_smul_eq_nsmul]
      exact Submodule.smul_of_tower_mem _ _ (hU2L i)
    · rw [Nat.cast_smul_eq_nsmul]
      exact Submodule.smul_of_tower_mem _ _ (map_mul_row_mem_of_rows_mem g1 U1 hU1L i)
  have hsW : ((s0 : E) ^ J) • W = (l.M : E) • Um := by
    rw [hUm, hg, Matrix.smul_mul, hW, hD, smul_comm, smul_sub, ← Matrix.mul_smul, hU1, hU2, Matrix.mul_smul,
      hn1, hn2]
    push_cast
    module
  have hsd : ∀ i, (((s0 ^ J : 𝓞 E)) : E) • W i = (l.M : E) • Um i := by
    intro i
    have := congrFun hsW i
    have e : ((s0 ^ J : 𝓞 E) : E) = (s0 : E) ^ J := map_pow (algebraMap (𝓞 E) E) s0 J
    rw [e]
    exact this

  have addL : ∀ v v' z, EF X (v + v') z = EF X v z + EF X v' z := fun v v' z => by
    change EFBil X (v + v') z = EFBil X v z + EFBil X v' z
    rw [LinearMap.map_add₂]
  have hEF0 : ∀ v : Fin r → E, EF X v v = 0 := fun v => by
    have := TensLat.EF_swap X v v
    linarith
  have hYd : Y' q' = h * Y q + ((2 : ℕ) : E) • d := by
    rw [hd, smul_smul, Nat.cast_two, mul_inv_cancel₀ two_ne_zero, one_smul, hD, add_sub_cancel]

  have hN'V2 : (N' : E) • V2 ∈ tens Λ' L :=
    smul_mem_tens' (natCast_smul_mem_of_span_smul_stdLat_le hN'le) ((TensLat.mem_tens_stdL L V2).mpr hV2L)
  have hNV1 : (N : E) • (h * V1) ∈ tens Λ' L := by
    rw [← Matrix.mul_smul]
    exact mul_mem_tens (fun v hv => (hh v).mp hv)
      (smul_mem_tens' (natCast_smul_mem_of_span_smul_stdLat_le hNle) ((TensLat.mem_tens_stdL L V1).mpr hV1L))
  have hdmem : d ∈ tens Λ' L := by
    refine mem_of_natCast_smul_mem_of_coprime (F := E) (tens Λ' L) (p := l.M ^ J) (q := 2 * k1 * t)
      (Nat.Coprime.pow_left J (Nat.Coprime.mul_right (Nat.Coprime.mul_right hM2 hk1.symm) htc.symm)) ?_ ?_
    · have e : ((l.M ^ J : ℕ) : E) • d = (N' : E) • V2 - (N : E) • (h * V1) := by
        rw [hd, hD, smul_comm, smul_sub, ← Matrix.mul_smul, Nat.cast_pow, hV1, hV2, Matrix.mul_smul]
        push_cast
        module
      rw [e]
      exact sub_mem hN'V2 hNV1
    · have e : ((2 * k1 * t : ℕ) : E) • d = (t : E) • W := by
        rw [hd, hW, smul_smul, smul_smul]
        congr 1
        push_cast
        field_simp
      rw [e]
      exact smul_mem_tens' ht2 ((TensLat.mem_tens_stdL L W).mpr hWL)

  have hXeq : ∑ k, EF X ((h * Y q) k) (d k) = ∑ k, EF X (Y' q' k) (d k) := by
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hYd]
    show EF X ((h * Y q) k) (d k) = EF X ((h * Y q) k + ((2 : ℕ) : E) • d k) (d k)
    rw [addL, Nat.cast_two, two_smul, addL, hEF0]
    ring
  have hXa : ∃ z : ℤ, ((l.M ^ J : ℕ) : ℚ) * ∑ k, EF X (Y' q' k) (d k) = z := by
    obtain ⟨m, hm⟩ := (TensLat.tens_selfDual hΛ' hL _).mp hN'V2 d hdmem
    refine ⟨2 * m, ?_⟩
    have e1 := sumEF_smul (X := X) (l.M ^ J) 1 (Y' q') d
    have e2 := sumEF_smul (X := X) 2 1 ((N' : E) • V2) d
    have hMV : ((l.M ^ J : ℕ) : E) • Y' q' = ((2 : ℕ) : E) • ((N' : E) • V2) := by
      rw [Nat.cast_pow, hV2, smul_smul]
      congr 1
      push_cast
      ring
    rw [hMV] at e1
    simp only [Nat.cast_one, one_smul, _root_.mul_one] at e1 e2
    rw [hm] at e2
    rw [← e1, e2]
    push_cast
    ring
  have hXb : ∃ z : ℤ, ((2 * k1 : ℕ) : ℚ) * ∑ k, EF X (Y' q' k) (d k) = z := by
    have e3 := sumEF_smul (X := X) 1 (2 * k1) (Y' q') d
    have e4 : ((2 * k1 : ℕ) : E) • d = W := by
      rw [hd, hW, smul_smul]
      congr 1
      push_cast
      field_simp
    rw [e4] at e3
    simp only [Nat.cast_one, one_smul, _root_.one_mul] at e3
    have hz : ∀ i, ∃ z : ℤ, EF X (Y' q' i) (W i) = z := fun i =>
      ef_int hL hmk.mem (hA'm i) (hA'L i) (hWL i) (hUmL i) h1s (hsd i)
    choose z hz using hz
    refine ⟨∑ i, z i, ?_⟩
    rw [← e3]
    push_cast
    exact Finset.sum_congr rfl fun i _ => hz i
  obtain ⟨za, hza⟩ := hXa
  obtain ⟨zb, hzb⟩ := hXb
  obtain ⟨c, hc⟩ := int_of_coprime
    (Nat.Coprime.pow_left J (Nat.Coprime.mul_right hM2 hk1.symm)) hza hzb
  have hcX : ∑ k, EF X ((h * Y q) k) (d k) = c := by rw [hXeq, hc]
  have hmain := heisG_add_two hs hL hΛ' (NumberField.RingOfIntegers.isIntegral_coe H.w0) hvac (h * Y q) hdmem hcX
  rw [hYd]
  exact hmain

end GlobalTheory.Dict.RootsMove
