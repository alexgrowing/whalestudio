import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjWeilDatumViaAdjointExchangedPair

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.SplitLeviDet

theorem smul_iff {R : Type*} [CommRing R] {m n : Type*} (ε : R) (N : Matrix m n R) :
    ε • N = N ↔ ∀ i j, ε * N i j = N i j :=
  ⟨fun h i j => congrFun (congrFun h i) j, fun h => by ext i j; exact h i j⟩

theorem smul_sandwich {R : Type*} [CommRing R] {k l m n : Type*} [Fintype l] [Fintype m] (ε : R)
    (P : Matrix k l R) (N : Matrix l m R) (Q : Matrix m n R) (hN : ε • N = N) : ε • (P * N * Q) = P * N * Q := by
  rw [← Matrix.smul_mul, ← Matrix.mul_smul, hN]

theorem det_supp {R : Type*} [CommRing R] {n : ℕ} (ε : R) (hε : ε * ε = ε) (M : Matrix (Fin n) (Fin n) R)
    (hM : ε • (M - 1) = M - 1) : (1 - ε) * M.det = 1 - ε := by
  have hid : IsIdempotentElem (1 - ε) := by unfold IsIdempotentElem; linear_combination hε
  have hf : (1 - ε) • M = (1 - ε) • (1 : Matrix (Fin n) (Fin n) R) := by
    have h0 : (1 - ε) • (M - 1) = 0 := by rw [sub_smul, one_smul, hM, sub_self]
    rw [smul_sub, sub_eq_zero] at h0
    exact h0
  have key := congrArg Matrix.det hf
  rw [Matrix.det_smul, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin] at key
  cases n with
  | zero => rw [Matrix.det_isEmpty, mul_one]
  | succ k => rw [hid.pow_succ_eq] at key; exact key

variable {D : D7}

def locU (e : AE D) (h : e * e = e) (t : (AE D)ˣ) : (AE D)ˣ where
  val := e * t + (1 - e)
  inv := e * ↑t⁻¹ + (1 - e)
  val_inv := by
    have htu : (t : AE D) * ↑t⁻¹ = 1 := t.mul_inv
    linear_combination e * htu + ((t : AE D) * ↑t⁻¹ - t - ↑t⁻¹ + 1) * h
  inv_val := by
    have htu : (↑t⁻¹ : AE D) * t = 1 := t.inv_mul
    linear_combination e * htu + ((↑t⁻¹ : AE D) * t - ↑t⁻¹ - t + 1) * h

theorem locU_val (e : AE D) (h : e * e = e) (t : (AE D)ˣ) : (locU e h t : AE D) = e * t + (1 - e) := rfl

def detU (V : HSp D) (g : GA D V) : (AE D)ˣ where
  val := (mt V g).det
  inv := (mt V g⁻¹).det
  val_inv := by rw [← Matrix.det_mul, GlobalTheory.MixModel.mt_mul_inv, Matrix.det_one]
  inv_val := by rw [← Matrix.det_mul, GlobalTheory.MixModel.mt_inv_mul, Matrix.det_one]

theorem detU_val (V : HSp D) (g : GA D V) : (detU V g : AE D) = (mt V g).det := rfl

theorem det_adj {n : ℕ} (y : Mx D n n) : (adj y).det = cA D y.det := by
  rw [adj, Matrix.det_transpose]; exact (RingHom.map_det (cA D) y).symm

theorem one_add_sub {n : ℕ} (M : Mx D n n) : 1 + (M - 1) = M := by abel

end GlobalTheory.SplitLeviDet

open GlobalTheory.SplitLeviDet

theorem GlobalTheory.SplitLeviDet.emb0Part : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (e : AE D), IsSplitIdem D e → (∀ g, SuppAt e S₀ g → SuppAt e S (d.emb0 g) ∧ ∃ x, IsDetAt e S₀ g x ∧ IsDetAt e S (d.emb0 g) x) := by
  intro D S S₀ ρ d e he
  obtain ⟨h1, h2, -⟩ := he
  have hce : cA D e * cA D e = cA D e := by rw [← map_mul, h1]
  have hcc : cA D (cA D e) = e := Formalism.L2.Theta.cA_cA e
  have hεε : (e + cA D e) * (e + cA D e) = e + cA D e := by linear_combination h1 + 2 * h2 + hce
  have hcε : cA D (e + cA D e) = e + cA D e := by rw [map_add, hcc, add_comm]
  intro g hg
  have hN : (e + cA D e) • (mt S₀ g - 1) = mt S₀ g - 1 := (smul_iff _ _).2 hg
  have hm : mt S (d.emb0 g) = (1 : Mx D S.rank S.rank) + d.j0 ⬝ (mt S₀ g - 1) ⬝ d.p0 := by
    rw [d.unitaryMatrix_wittCoreEmbedding]; conv_rhs => rw [← d.sum_eq_one]
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc]; abel
  have hdet : (mt S (d.emb0 g)).det = (mt S₀ g).det := by
    rw [hm, Matrix.mul_assoc, Matrix.det_one_add_mul_comm, Matrix.mul_assoc, d.p0_j0, Matrix.mul_one, one_add_sub]
  refine ⟨?_, locU e h1 (detU S₀ g), ?_, ?_⟩
  · intro i j
    rw [hm, add_sub_cancel_left]
    exact (smul_iff _ _).1 (smul_sandwich _ _ _ _ hN) i j
  · rw [IsDetAt, locU_val, detU_val]
  · rw [IsDetAt, locU_val, detU_val, hdet]

set_option maxHeartbeats 1000000 in
theorem GlobalTheory.SplitLeviDet.leviPart : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (e : AE D), IsSplitIdem D e → ∀ (χ : (AE D)ˣ →* Circle) (n : ℕ), IsHeckeChar D χ → ResEta D χ n → ∀ a : GL (Fin ρ) (AE D), (∀ i j, (e + cA D e) * (a.1 - 1) i j = (a.1 - 1) i j) → SuppAt e S (d.levi a) ∧ ∃ x, IsDetAt e S (d.levi a) x ∧ χ x = χ (Matrix.GeneralLinearGroup.det a) := by
  intro D S S₀ ρ d e he
  obtain ⟨h1, h2, -⟩ := he
  have hce : cA D e * cA D e = cA D e := by rw [← map_mul, h1]
  have hcc : cA D (cA D e) = e := Formalism.L2.Theta.cA_cA e
  have hεε : (e + cA D e) * (e + cA D e) = e + cA D e := by linear_combination h1 + 2 * h2 + hce
  have hcε : cA D (e + cA D e) = e + cA D e := by rw [map_add, hcc, add_comm]
  intro χ n hχ hR a ha
  have hA : (e + cA D e) • (a.1 - 1 : Mx D ρ ρ) = (a.1 - 1 : Mx D ρ ρ) := by
    ext i j
    exact ha i j
  have hI : (e + cA D e) • ((a⁻¹).1 - 1 : Mx D ρ ρ) = ((a⁻¹).1 - 1 : Mx D ρ ρ) := by
    have hinv : ((a⁻¹).1 - 1 : Mx D ρ ρ) = -((a⁻¹).1 ⬝ (a.1 - 1 : Mx D ρ ρ)) := by
      rw [Matrix.mul_sub, Matrix.mul_one, Units.inv_mul, neg_sub]
    rw [hinv, smul_neg, ← Matrix.mul_smul, hA]
  have hB : (e + cA D e) • (adj (a⁻¹).1 - 1 : Mx D ρ ρ) = (adj (a⁻¹).1 - 1 : Mx D ρ ρ) := by
    have h' : (adj (a⁻¹).1 - 1 : Mx D ρ ρ) = adj ((a⁻¹).1 - 1 : Mx D ρ ρ) := by rw [adj_sub, adj_one]
    rw [h']
    calc (e + cA D e) • adj ((a⁻¹).1 - 1 : Mx D ρ ρ) = cA D (e + cA D e) • adj ((a⁻¹).1 - 1 : Mx D ρ ρ) := by rw [hcε]
      _ = adj ((e + cA D e) • ((a⁻¹).1 - 1 : Mx D ρ ρ)) := (adj_smul _ _).symm
      _ = adj ((a⁻¹).1 - 1 : Mx D ρ ρ) := by rw [hI]
  have hm : mt S (d.levi a) = (1 : Mx D S.rank S.rank) + (d.jX ⬝ (a.1 - 1 : Mx D ρ ρ) ⬝ d.pX + d.jY ⬝ (adj (a⁻¹).1 - 1 : Mx D ρ ρ) ⬝ d.pY) := by
    rw [d.mt_levi a]; conv_rhs => rw [← d.sum_eq_one]
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc]; abel
  have hdet : (mt S (d.levi a)).det = a.1.det * cA D (a⁻¹).1.det := by
    have h' : d.jX ⬝ (a.1 - 1 : Mx D ρ ρ) ⬝ d.pX + d.jY ⬝ (adj (a⁻¹).1 - 1 : Mx D ρ ρ) ⬝ d.pY =
        Matrix.fromCols d.jX d.jY ⬝ Matrix.fromRows ((a.1 - 1 : Mx D ρ ρ) ⬝ d.pX) ((adj (a⁻¹).1 - 1 : Mx D ρ ρ) ⬝ d.pY) := by
      rw [Matrix.fromCols_mul_fromRows, Matrix.mul_assoc, Matrix.mul_assoc]
    rw [hm, h', Matrix.det_one_add_mul_comm, Matrix.fromRows_mul_fromCols]
    simp only [Matrix.mul_assoc, d.pX_jX, d.pX_jY, d.pY_jX, d.pY_jY, Matrix.mul_one, Matrix.mul_zero]
    rw [← Matrix.fromBlocks_one, Matrix.fromBlocks_add]
    simp only [add_zero, one_add_sub]
    rw [Matrix.det_fromBlocks_zero₂₁, det_adj]
  have hs : (1 - (e + cA D e)) * a.1.det = 1 - (e + cA D e) := det_supp _ hεε _ hA
  set t := Matrix.GeneralLinearGroup.det a with ht
  have ht1 : (t : AE D) = a.1.det := rfl
  have ht2 : ((t⁻¹ : (AE D)ˣ) : AE D) = (a⁻¹).1.det := by rw [ht, ← map_inv]; rfl
  refine ⟨?_, locU e h1 (t * Units.map (cA D).toMonoidHom t⁻¹), ?_, ?_⟩
  · have X : (e + cA D e) • (mt S (d.levi a) - 1) = mt S (d.levi a) - 1 := by
      rw [hm, add_sub_cancel_left, smul_add, smul_sandwich _ _ _ _ hA, smul_sandwich _ _ _ _ hB]
    intro i j
    exact congrFun (congrFun X i) j
  · rw [IsDetAt, locU_val, hdet, Units.val_mul, Units.coe_map, ht1, ht2]; rfl
  · set w := locU (cA D e) hce t with hw
    have hdc : cA D ((t⁻¹ : (AE D)ˣ) : AE D) * cA D (t : AE D) = 1 := by
      rw [← map_mul, Units.inv_mul, map_one]
    have hs' : (1 - (e + cA D e)) * (t : AE D) = 1 - (e + cA D e) := by rw [ht1]; exact hs
    have key : t = locU e h1 (t * Units.map (cA D).toMonoidHom t⁻¹) * (w * Units.map (cA D).toMonoidHom w) := by
      apply Units.ext
      rw [Units.val_mul, Units.val_mul, Units.coe_map, locU_val, Units.val_mul, Units.coe_map, hw, locU_val]
      simp only [RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, map_add, map_mul, map_sub, map_one, hcc]
      linear_combination (-((e * t * cA D ((t⁻¹ : (AE D)ˣ) : AE D) + 1 - e) * (t * cA D (t : AE D) - t - cA D (t : AE D) + 1) +
          ((t : AE D) ^ 2 * cA D ((t⁻¹ : (AE D)ˣ) : AE D) - t * cA D ((t⁻¹ : (AE D)ˣ) : AE D) - t + 1))) * h2 -
        ((t : AE D) * cA D ((t⁻¹ : (AE D)ˣ) : AE D) * cA D (t : AE D) - t * cA D ((t⁻¹ : (AE D)ˣ) : AE D) - cA D (t : AE D) + 1) * h1 -
        e * t * hdc + hs'
    conv_rhs => rw [key]
    rw [map_mul, map_mul, GlobalTheory.ConjAdjWeil.chi_conj hR w, mul_inv_cancel, mul_one]

theorem GlobalTheory.splitLeviDet : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (e : AE D), IsSplitIdem D e → (∀ g, SuppAt e S₀ g → SuppAt e S (d.emb0 g) ∧ ∃ x, IsDetAt e S₀ g x ∧ IsDetAt e S (d.emb0 g) x) ∧ ∀ (χ : (AE D)ˣ →* Circle) (n : ℕ), IsHeckeChar D χ → ResEta D χ n → ∀ a : GL (Fin ρ) (AE D), (∀ i j, (e + cA D e) * (a.1 - 1) i j = (a.1 - 1) i j) → SuppAt e S (d.levi a) ∧ ∃ x, IsDetAt e S (d.levi a) x ∧ χ x = χ (Matrix.GeneralLinearGroup.det a) := fun D S S₀ ρ d e he =>
  ⟨GlobalTheory.SplitLeviDet.emb0Part D S S₀ ρ d e he, GlobalTheory.SplitLeviDet.leviPart D S S₀ ρ d e he⟩
