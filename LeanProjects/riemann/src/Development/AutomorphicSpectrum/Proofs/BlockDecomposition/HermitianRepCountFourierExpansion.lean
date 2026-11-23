import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.LocalDefs
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ResAlgSplitTwo
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FixedNondeg
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens GlobalTheory.CompanionTheory.SiegLoc Filter Topology

namespace GlobalTheory.CompanionTheory.SiegLoc.LevelId

variable {R : Type} [CommRing R]

theorem cT_mul (σ : R →+* R) {a b c : ℕ} (x : Matrix (Fin a) (Fin b) R) (y : Matrix (Fin b) (Fin c) R) :
    cT σ (x * y) = cT σ y * cT σ x := by
  unfold cT
  rw [Matrix.map_mul, Matrix.transpose_mul]

theorem cT_cT (σ : R →+* R) (h : ∀ a, σ (σ a) = a) {a b : ℕ} (x : Matrix (Fin a) (Fin b) R) :
    cT σ (cT σ x) = x := by
  ext i j
  exact h (x i j)

theorem cT_sub (σ : R →+* R) {a b : ℕ} (x y : Matrix (Fin a) (Fin b) R) :
    cT σ (x - y) = cT σ x - cT σ y := by
  ext i j
  exact map_sub σ (x j i) (y j i)

theorem red_mul (ϖ : R) (k : ℕ) {a b c : ℕ} (x : Matrix (Fin a) (Fin b) R) (y : Matrix (Fin b) (Fin c) R) :
    red ϖ k (x * y) = red ϖ k x * red ϖ k y := by
  unfold red
  exact Matrix.map_mul

theorem red_sub (ϖ : R) (k : ℕ) {a b : ℕ} (x y : Matrix (Fin a) (Fin b) R) :
    red ϖ k (x - y) = red ϖ k x - red ϖ k y := by
  ext i j
  exact map_sub (Ideal.Quotient.mk (lev ϖ k)) (x i j) (y i j)

theorem red_neg (ϖ : R) (k : ℕ) {a b : ℕ} (x : Matrix (Fin a) (Fin b) R) :
    red ϖ k (-x) = - red ϖ k x := by
  ext i j
  exact map_neg (Ideal.Quotient.mk (lev ϖ k)) (x i j)

theorem red_cT (σ : R →+* R) (ϖ : R) (h : σ ϖ = ϖ) (k : ℕ) {a b : ℕ} (x : Matrix (Fin a) (Fin b) R) :
    red ϖ k (cT σ x) = cT (barσ σ ϖ h k) (red ϖ k x) := by
  ext i j
  exact (barσ_mk σ ϖ h k (x j i)).symm

theorem red_surj (ϖ : R) (k : ℕ) {a b : ℕ} :
    Function.Surjective (red ϖ k : Matrix (Fin a) (Fin b) R → _) := by
  intro y
  refine ⟨Matrix.of fun i j => (Ideal.Quotient.mk_surjective (y i j)).choose, ?_⟩
  ext i j
  exact (Ideal.Quotient.mk_surjective (y i j)).choose_spec

theorem red_gram (σ : R →+* R) (ϖ : R) (h : σ ϖ = ϖ) (k : ℕ) {m n : ℕ}
    (S : Matrix (Fin m) (Fin m) R) (x : Matrix (Fin m) (Fin n) R) :
    red ϖ k (cT σ x * S * x) = cT (barσ σ ϖ h k) (red ϖ k x) * red ϖ k S * red ϖ k x := by
  rw [red_mul, red_mul, red_cT σ ϖ h]

theorem image_sol (σ : R →+* R) (ϖ : R) (h : σ ϖ = ϖ) (k : ℕ) {m n : ℕ}
    (S : Matrix (Fin m) (Fin m) R) (T : Matrix (Fin n) (Fin n) R) :
    red ϖ k '' {x : Matrix (Fin m) (Fin n) R | red ϖ k (cT σ x * S * x) = red ϖ k T} =
      {y | cT (barσ σ ϖ h k) y * red ϖ k S * y = red ϖ k T} := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    show cT (barσ σ ϖ h k) (red ϖ k x) * red ϖ k S * red ϖ k x = red ϖ k T
    rw [← red_gram σ ϖ h]
    exact hx
  · intro hy
    obtain ⟨x, rfl⟩ := red_surj ϖ k y
    refine ⟨x, ?_, rfl⟩
    show red ϖ k (cT σ x * S * x) = red ϖ k T
    rw [red_gram σ ϖ h]
    exact hy

theorem gram_sub_mem (σ : R →+* R) (ϖ : R) (hinv : ∀ a, σ (σ a) = a) (h : σ ϖ = ϖ) (k : ℕ) {m n : ℕ}
    (S : Matrix (Fin m) (Fin m) R) (T : Matrix (Fin n) (Fin n) R) (hS : cT σ S = S) (hT : cT σ T = T)
    (y : Matrix (Fin m) (Fin n) (R ⧸ lev ϖ k)) :
    cT (barσ σ ϖ h k) y * red ϖ k S * y - red ϖ k T ∈ hermMod σ ϖ n k := by
  obtain ⟨x, rfl⟩ := red_surj ϖ k y
  unfold hermMod
  refine ⟨cT σ x * S * x - T, ?_, ?_⟩
  · show cT σ (cT σ x * S * x - T) = cT σ x * S * x - T
    rw [cT_sub, cT_mul, cT_mul, cT_cT σ hinv, hS, hT, Matrix.mul_assoc]
  · show red ϖ k (cT σ x * S * x - T) = _
    rw [red_sub, red_gram σ ϖ h]

theorem neg_mem_herm (σ : R →+* R) (ϖ : R) (n k : ℕ) {B : Matrix (Fin n) (Fin n) (R ⧸ lev ϖ k)}
    (hB : B ∈ hermMod σ ϖ n k) : -B ∈ hermMod σ ϖ n k := by
  unfold hermMod at hB ⊢
  obtain ⟨h0, hh, rfl⟩ := hB
  refine ⟨-h0, ?_, red_neg ϖ k h0⟩
  show cT σ (-h0) = -h0
  have hh' : cT σ h0 = h0 := hh
  ext i j
  have e : σ (h0 j i) = h0 i j := congrFun (congrFun hh' i) j
  show σ (-(h0 j i)) = -(h0 i j)
  rw [map_neg, e]

theorem nuAt_neg (ϖ : R) {n k : ℕ} (B : Matrix (Fin n) (Fin n) (R ⧸ lev ϖ k)) :
    nuAt ϖ (-B) = nuAt ϖ B := by
  unfold nuAt
  have hset : (Set.range fun x : Fin n → R ⧸ lev ϖ k => Matrix.vecMul x (-B)) =
      Set.range fun x : Fin n → R ⧸ lev ϖ k => Matrix.vecMul x B := by
    ext v
    constructor
    · rintro ⟨x, rfl⟩
      refine ⟨-x, ?_⟩
      show Matrix.vecMul (-x) B = Matrix.vecMul x (-B)
      rw [Matrix.neg_vecMul, Matrix.vecMul_neg]
    · rintro ⟨x, rfl⟩
      refine ⟨-x, ?_⟩
      show Matrix.vecMul (-x) (-B) = Matrix.vecMul x B
      rw [Matrix.neg_vecMul, Matrix.vecMul_neg, neg_neg]
  rw [hset]

end GlobalTheory.CompanionTheory.SiegLoc.LevelId

open GlobalTheory.CompanionTheory.SiegLoc.LevelId in

theorem GlobalTheory.CompanionTheory.SiegLoc.level_identity : ∀ (R : Type) [CommRing R] (σ : R →+* R) (ϖ : R) (q : ℕ) (ε : ℤ) (hR : IsUnrQuad R σ ϖ q ε) [∀ k, Fintype (R ⧸ lev ϖ k)] (ψ : ∀ k, AddChar (R ⧸ lev ϖ k) ℂ), IsLevelChars σ ϖ ψ → ∀ (m n k : ℕ) (S : Matrix (Fin m) (Fin m) R) (T : Matrix (Fin n) (Fin n) R), cT σ S = S → cT σ T = T → (∀ Y : Matrix (Fin n) (Fin n) (R ⧸ lev ϖ k), Y ∈ hermMod σ ϖ n k → (Y = 0 → (∑' B : hermMod σ ϖ n k, ψ k (Matrix.trace (B.1 * Y))) = (Nat.card (hermMod σ ϖ n k) : ℂ)) ∧ (Y ≠ 0 → (∑' B : hermMod σ ϖ n k, ψ k (Matrix.trace (B.1 * Y))) = 0)) → (∀ B ∈ hermMod σ ϖ n k, (∑ x : Matrix (Fin m) (Fin n) (R ⧸ lev ϖ k), ψ k (Matrix.trace (B * (cT (barσ σ ϖ hR.fix_ϖ k) x * red ϖ k S * x)))) = (Nat.card (Matrix (Fin m) (Fin n) (R ⧸ lev ϖ k)) : ℂ) * (((ε : ℂ) ^ m * (q : ℂ) ^ (-(m : ℤ))) ^ Nat.log (q ^ 2) (nuAt ϖ B))) → siegAt ϖ σ ψ q ε m T k = ((densAt σ ϖ S T k : ℝ) : ℂ) := by
  intro R _ σ ϖ q ε hR _ ψ hψ m n k S T hS hT horth hgauss
  classical
  have : Fintype ↥(hermMod σ ϖ n k) := Fintype.ofFinite _
  have hx : ∀ x : Matrix (Fin m) (Fin n) (R ⧸ lev ϖ k),
      (∑' B : hermMod σ ϖ n k,
        ψ k (Matrix.trace (B.1 * (cT (barσ σ ϖ hR.fix_ϖ k) x * red ϖ k S * x - red ϖ k T)))) =
        if cT (barσ σ ϖ hR.fix_ϖ k) x * red ϖ k S * x = red ϖ k T then
          (Nat.card (hermMod σ ϖ n k) : ℂ) else 0 := by
    intro x
    have hmem := gram_sub_mem σ ϖ hR.inv hR.fix_ϖ k S T hS hT x
    by_cases hxe : cT (barσ σ ϖ hR.fix_ϖ k) x * red ϖ k S * x = red ϖ k T
    · rw [if_pos hxe]
      exact (horth _ hmem).1 (sub_eq_zero.mpr hxe)
    · rw [if_neg hxe]
      exact (horth _ hmem).2 (sub_ne_zero.mpr hxe)
  have hsplit : ∀ (B : hermMod σ ϖ n k) (x : Matrix (Fin m) (Fin n) (R ⧸ lev ϖ k)),
      ψ k (Matrix.trace (B.1 * (cT (barσ σ ϖ hR.fix_ϖ k) x * red ϖ k S * x - red ϖ k T))) =
        ψ k (Matrix.trace (B.1 * (cT (barσ σ ϖ hR.fix_ϖ k) x * red ϖ k S * x))) *
          ψ k (-Matrix.trace (B.1 * red ϖ k T)) := by
    intro B x
    rw [Matrix.mul_sub, Matrix.trace_sub, sub_eq_add_neg, AddChar.map_add_eq_mul]
  have hsol : (solCount σ ϖ S T k : ℂ) = ∑ x : Matrix (Fin m) (Fin n) (R ⧸ lev ϖ k),
      if cT (barσ σ ϖ hR.fix_ϖ k) x * red ϖ k S * x = red ϖ k T then (1 : ℂ) else 0 := by
    unfold solCount
    rw [image_sol σ ϖ hR.fix_ϖ k S T, Nat.card_eq_fintype_card, Fintype.card_subtype,
      Finset.natCast_card_filter]
    exact Finset.sum_congr rfl fun x _ => if_congr Iff.rfl rfl rfl
  have h1 : ∀ x : Matrix (Fin m) (Fin n) (R ⧸ lev ϖ k), (Nat.card (hermMod σ ϖ n k) : ℂ) *
      (if cT (barσ σ ϖ hR.fix_ϖ k) x * red ϖ k S * x = red ϖ k T then (1 : ℂ) else 0) =
      ∑ B : hermMod σ ϖ n k, ψ k (Matrix.trace (B.1 * (cT (barσ σ ϖ hR.fix_ϖ k) x * red ϖ k S * x))) *
        ψ k (-Matrix.trace (B.1 * red ϖ k T)) := by
    intro x
    rw [mul_ite, mul_one, mul_zero, ← hx x, tsum_fintype]
    exact Finset.sum_congr rfl fun B _ => hsplit B x
  have hcount : (Nat.card (hermMod σ ϖ n k) : ℂ) * (solCount σ ϖ S T k : ℂ) =
      (Nat.card (Matrix (Fin m) (Fin n) (R ⧸ lev ϖ k)) : ℂ) *
        ∑ B : hermMod σ ϖ n k, ψ k (-Matrix.trace (B.1 * red ϖ k T)) *
          ((ε : ℂ) ^ m * (q : ℂ) ^ (-(m : ℤ))) ^ Nat.log (q ^ 2) (nuAt ϖ B.1) := by
    calc (Nat.card (hermMod σ ϖ n k) : ℂ) * (solCount σ ϖ S T k : ℂ)
        = ∑ x : Matrix (Fin m) (Fin n) (R ⧸ lev ϖ k), (Nat.card (hermMod σ ϖ n k) : ℂ) *
            (if cT (barσ σ ϖ hR.fix_ϖ k) x * red ϖ k S * x = red ϖ k T then (1 : ℂ) else 0) := by
          rw [hsol, Finset.mul_sum]
      _ = ∑ x : Matrix (Fin m) (Fin n) (R ⧸ lev ϖ k), ∑ B : hermMod σ ϖ n k,
            ψ k (Matrix.trace (B.1 * (cT (barσ σ ϖ hR.fix_ϖ k) x * red ϖ k S * x))) *
              ψ k (-Matrix.trace (B.1 * red ϖ k T)) := Finset.sum_congr rfl fun x _ => h1 x
      _ = ∑ B : hermMod σ ϖ n k, ∑ x : Matrix (Fin m) (Fin n) (R ⧸ lev ϖ k),
            ψ k (Matrix.trace (B.1 * (cT (barσ σ ϖ hR.fix_ϖ k) x * red ϖ k S * x))) *
              ψ k (-Matrix.trace (B.1 * red ϖ k T)) := Finset.sum_comm
      _ = ∑ B : hermMod σ ϖ n k, (Nat.card (Matrix (Fin m) (Fin n) (R ⧸ lev ϖ k)) : ℂ) *
            (ψ k (-Matrix.trace (B.1 * red ϖ k T)) *
              ((ε : ℂ) ^ m * (q : ℂ) ^ (-(m : ℤ))) ^ Nat.log (q ^ 2) (nuAt ϖ B.1)) := by
          refine Finset.sum_congr rfl fun B _ => ?_
          rw [← Finset.sum_mul, hgauss B.1 B.2]
          ring
      _ = _ := by rw [Finset.mul_sum]
  have hneg : ∑ B : hermMod σ ϖ n k, ψ k (-Matrix.trace (B.1 * red ϖ k T)) *
        ((ε : ℂ) ^ m * (q : ℂ) ^ (-(m : ℤ))) ^ Nat.log (q ^ 2) (nuAt ϖ B.1) =
      ∑ B : hermMod σ ϖ n k, ψ k (Matrix.trace (red ϖ k T * B.1)) *
        ((ε : ℂ) ^ m * (q : ℂ) ^ (-(m : ℤ))) ^ Nat.log (q ^ 2) (nuAt ϖ B.1) := by
    let e : hermMod σ ϖ n k ≃ hermMod σ ϖ n k :=
      { toFun := fun B => ⟨-B.1, neg_mem_herm σ ϖ n k B.2⟩
        invFun := fun B => ⟨-B.1, neg_mem_herm σ ϖ n k B.2⟩
        left_inv := fun B => Subtype.ext (neg_neg _)
        right_inv := fun B => Subtype.ext (neg_neg _) }
    refine Fintype.sum_equiv e _ _ fun B => ?_
    show _ = ψ k (Matrix.trace (red ϖ k T * -B.1)) *
      ((ε : ℂ) ^ m * (q : ℂ) ^ (-(m : ℤ))) ^ Nat.log (q ^ 2) (nuAt ϖ (-B.1))
    rw [nuAt_neg, Matrix.mul_neg, Matrix.trace_neg, Matrix.trace_mul_comm]
  have hfin : siegAt ϖ σ ψ q ε m T k = ∑ B : hermMod σ ϖ n k, ψ k (-Matrix.trace (B.1 * red ϖ k T)) *
        ((ε : ℂ) ^ m * (q : ℂ) ^ (-(m : ℤ))) ^ Nat.log (q ^ 2) (nuAt ϖ B.1) := by
    unfold siegAt
    rw [tsum_fintype, hneg]
  have hM : (Nat.card (Matrix (Fin m) (Fin n) (R ⧸ lev ϖ k)) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hcast : ((densAt σ ϖ S T k : ℝ) : ℂ) = (solCount σ ϖ S T k : ℂ) * (Nat.card (hermMod σ ϖ n k) : ℂ) /
      (Nat.card (Matrix (Fin m) (Fin n) (R ⧸ lev ϖ k)) : ℂ) := by
    unfold densAt
    rw [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_natCast, Complex.ofReal_natCast,
      Complex.ofReal_natCast]
  rw [hfin, hcast, eq_div_iff hM]
  linear_combination (-1 : ℂ) * hcount
