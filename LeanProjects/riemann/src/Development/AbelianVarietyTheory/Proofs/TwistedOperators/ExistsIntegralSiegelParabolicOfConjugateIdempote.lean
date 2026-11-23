import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinMapsOfForall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FromBlocksMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplementaryAdelicSchwartzRestFunction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StarMemAdelicSchwartzSpaceNumberField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitEqNormCompletionTensorOfIsInertAt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LiftVAlgebraMapMul
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.SplitConjPar

section FinTwoTypeFamily
variable {R : Type} [CommRing R] {d : ℕ}

def blk2 (d : ℕ) (a b : R) : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) R :=
  Matrix.fromBlocks (a • 1) (b • 1) (b • 1) (a • 1)

theorem symmetricScalarBlockMatrix_mul (a b a' b' : R) : blk2 d a b * blk2 d a' b' = blk2 d (a * a' + b * b') (a * b' + b * a') := by
  simp only [blk2, Matrix.fromBlocks_multiply, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul, ← add_smul]
  congr 2 <;> ring

theorem symmetricScalarBlockMatrix_one_zero : blk2 d (1 : R) 0 = 1 := by
  simp [blk2, Matrix.fromBlocks_one]

theorem symmetricScalarBlockMatrix_transpose (a b : R) : (blk2 d a b)ᵀ = blk2 d a b := by
  simp [blk2, Matrix.fromBlocks_transpose, Matrix.transpose_smul]

theorem symmetricScalarBlockMatrix_map (c : R → R) (h0 : c 0 = 0) (a b : R) : (blk2 d a b).map c = blk2 d (c a) (c b) := by
  ext (i | i) (j | j) <;> by_cases h : i = j <;> simp [blk2, Matrix.one_apply, h, h0]

theorem symmetricScalarBlockMatrix_mul_gram_mul (J : Matrix (Fin d) (Fin d) R) (a b a' b' : R) :
    blk2 d a b * Matrix.fromBlocks J 0 0 (-J) * blk2 d a' b' =
      Matrix.fromBlocks ((a * a' - b * b') • J) ((a * b' - b * a') • J) ((b * a' - a * b') • J) ((b * b' - a * a') • J) := by
  simp only [blk2, Matrix.fromBlocks_multiply, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one,
    Matrix.zero_mul, Matrix.mul_zero, smul_zero, zero_add, add_zero, smul_neg, Matrix.neg_mul, Matrix.mul_neg, smul_smul]
  congr 1 <;> module

theorem symmetricScalarBlockMatrix_mul_diagonalColumns (a b : R) :
    blk2 d a b * (Matrix.fromRows (1 : Matrix (Fin d) (Fin d) R) (1 : Matrix (Fin d) (Fin d) R) : Matrix (Fin d ⊕ Fin d) (Fin d) R) =
      (Matrix.fromRows (1 : Matrix (Fin d) (Fin d) R) (1 : Matrix (Fin d) (Fin d) R) : Matrix (Fin d ⊕ Fin d) (Fin d) R) * ((a + b) • (1 : Matrix (Fin d) (Fin d) R)) := by
  simp only [blk2, Matrix.fromBlocks_mul_fromRows, Matrix.fromRows_mul, Matrix.mul_one, Matrix.one_mul, add_comm b a, ← add_smul]

theorem symmetricScalarBlockMatrix_mul_antidiagonalColumns (a b : R) :
    blk2 d a b * (Matrix.fromRows (1 : Matrix (Fin d) (Fin d) R) (-(1 : Matrix (Fin d) (Fin d) R)) : Matrix (Fin d ⊕ Fin d) (Fin d) R) =
      (Matrix.fromRows (1 : Matrix (Fin d) (Fin d) R) (-(1 : Matrix (Fin d) (Fin d) R)) : Matrix (Fin d ⊕ Fin d) (Fin d) R) * ((a - b) • (1 : Matrix (Fin d) (Fin d) R)) := by
  simp only [blk2, Matrix.fromBlocks_mul_fromRows, Matrix.fromRows_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_neg,
    Matrix.neg_mul]
  congr 1 <;> module

theorem symmetricScalarBlockMatrix_sub_one (a b : R) : blk2 d a b - 1 = blk2 d (a - 1) b := by
  ext (i | i) (j | j) <;> by_cases h : i = j <;> simp [blk2, Matrix.one_apply, h]

theorem symmetricScalarBlockMatrix_mulVec_inl (a b : R) (z : Fin d ⊕ Fin d → R) (i : Fin d) :
    (blk2 d a b *ᵥ z) (Sum.inl i) = a * z (Sum.inl i) + b * z (Sum.inr i) := by
  simp [blk2, Matrix.fromBlocks_mulVec, Matrix.smul_mulVec]

theorem symmetricScalarBlockMatrix_mulVec_inr (a b : R) (z : Fin d ⊕ Fin d → R) (i : Fin d) :
    (blk2 d a b *ᵥ z) (Sum.inr i) = b * z (Sum.inl i) + a * z (Sum.inr i) := by
  simp [blk2, Matrix.fromBlocks_mulVec, Matrix.smul_mulVec]

end FinTwoTypeFamily

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem evFin_half_mem (v : Pl F) (h2 : (2 : 𝓞 F) ∉ v.asIdeal) :
    evFin F v (⅟2 : AF F) ∈ v.adicCompletionIntegers F := by
  have hv2 : Valued.v (2 : Fv F v) = 1 := by
    have e : ((algebraMap (𝓞 F) (v.adicCompletionIntegers F) 2 : v.adicCompletionIntegers F) : Fv F v) = 2 := by
      rw [map_ofNat]; rfl
    have hn := (GlobalTheory.InertUnitNorm.algebraMap_mem_maximalIdeal_iff v 2).not.2 h2
    rw [GlobalTheory.InertUnitNorm.mem_maximalIdeal_iff_valued_lt_one, e] at hn
    have hle : Valued.v (2 : Fv F v) ≤ 1 := by
      rw [← e]; exact (algebraMap (𝓞 F) (v.adicCompletionIntegers F) 2).2
    exact le_antisymm hle (not_lt.1 hn)
  have hx : (2 : Fv F v) * evFin F v (⅟2 : AF F) = 1 := by
    rw [← map_ofNat (evFin F v) 2, ← map_mul, mul_invOf_self, map_one]
  rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]
  have := congrArg Valued.v hx
  rw [map_mul, hv2, one_mul, map_one] at this
  exact this.le

theorem symmetricScalarBlockMatrix_mulVec_mem_doubledLattice {d : ℕ} {W : Spc F E d} {v : Pl F} {a b : AE F E} (ha : GlobalTheory.SplitConj.Mult W v a)
    (hb : GlobalTheory.SplitConj.Mult W v b) (z : Fin d ⊕ Fin d → AE F E) (hz : z ∈ GlobalTheory.InertDbl.latAtD W v) :
    blk2 d a b *ᵥ z ∈ GlobalTheory.InertDbl.latAtD W v := by
  constructor
  · simp only [symmetricScalarBlockMatrix_mulVec_inl]
    exact add_mem (ha _ hz.1) (hb _ hz.2)
  · simp only [symmetricScalarBlockMatrix_mulVec_inr]
    exact add_mem (hb _ hz.1) (ha _ hz.2)

theorem mult_neg {d : ℕ} {W : Spc F E d} {v : Pl F} {a : AE F E} (ha : GlobalTheory.SplitConj.Mult W v a) :
    GlobalTheory.SplitConj.Mult W v (-a) := fun z hz => by
  have : (fun i => -a * z i) = -(fun i => a * z i) := by ext i; simp
  rw [this]; exact neg_mem (ha z hz)

theorem mult_sub {d : ℕ} {W : Spc F E d} {v : Pl F} {a b : AE F E} (ha : GlobalTheory.SplitConj.Mult W v a)
    (hb : GlobalTheory.SplitConj.Mult W v b) : GlobalTheory.SplitConj.Mult W v (a - b) := by
  rw [sub_eq_add_neg]; exact GlobalTheory.SplitConj.mult_add ha (mult_neg hb)

theorem mult_one {d : ℕ} (W : Spc F E d) (v : Pl F) : GlobalTheory.SplitConj.Mult W v 1 := fun z hz => by
  simpa using hz

theorem exists_par : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (d : ℕ) (W : Spc F E d) (v : Pl F), (2 : 𝓞 F) ∉ v.asIdeal →
    ∀ Eid : AE F E, Eid * Eid = Eid → Eid + cA σ Eid = algebraMap (AF F) (AE F E) (GlobalTheory.LatVac.liftV v 1) →
    Eid * cA σ Eid = 0 →
    (∀ z ∈ GlobalTheory.InertSph.latAt W v, (fun i => Eid * z i) ∈ GlobalTheory.InertSph.latAt W v) →
    ∃ s ∈ GlobalTheory.InertDbl.ParD σ W v,
      GlobalTheory.InertDbl.matD s * diagCols (Fin d) =
        diagCols (Fin d) * ((1 - (⅟2 : AF F) • Eid) • (1 : Matrix (Fin d) (Fin d) (AE F E))) ∧
      GlobalTheory.InertDbl.matD s * GlobalTheory.InertDbl.antiCols d =
        GlobalTheory.InertDbl.antiCols d * ((1 + cA σ Eid) • (1 : Matrix (Fin d) (Fin d) (AE F E))) := by
  intro F E _ _ _ _ _ σ B _ d W v h2 A hA hAe hAB hL
  set h : AE F E := algebraMap (AF F) (AE F E) (⅟2) with hh
  set e : AE F E := algebraMap (AF F) (AE F E) (GlobalTheory.LatVac.liftV v 1) with he
  set A' : AE F E := cA σ A with hA'
  have h2h : 2 * h = 1 := by
    rw [hh, ← map_ofNat (algebraMap (AF F) (AE F E)) 2, ← map_mul, mul_invOf_self, map_one]
  have hee : e * e = e := by rw [he, ← map_mul, ← GlobalTheory.SplitConj.liftV_mul, one_mul]
  have hAe' : A * e = A := by rw [← hAe, mul_add, hA, hAB, add_zero]
  have hA'e : A' = e - A := by rw [← hAe]; ring
  have hA'A' : A' * A' = A' := by rw [hA'e]; linear_combination hee - 2 * hAe' + hA
  have ch : cA σ h = h := (cA σ).commutes _
  have ce : cA σ e = e := (cA σ).commutes _
  have cA' : cA σ A' = A := by rw [hA'e, map_sub, ce, ← hA', hA'e]; ring
  have hx : (1 - h * A) * (1 + A) = 1 := by linear_combination (-h) * hA - A * h2h
  have hy : (1 + A') * (1 - h * A') = 1 := by linear_combination (-h) * hA'A' - A' * h2h
  have cx : cA σ (1 - h * A) = 1 - h * A' := by rw [map_sub, map_one, map_mul, ch]
  have cy : cA σ (1 + A') = 1 + A := by rw [map_add, map_one, cA']
  have Mh : GlobalTheory.SplitConj.Mult W v h := GlobalTheory.SplitConj.mult_algebraMap W v _ (evFin_half_mem v h2)
  have Me : GlobalTheory.SplitConj.Mult W v e := GlobalTheory.SplitConj.mult_algebraMap W v _ (by
    rw [GlobalTheory.LatVac.evFin_liftV]; exact one_mem _)
  have MA : GlobalTheory.SplitConj.Mult W v A := hL
  have MA' : GlobalTheory.SplitConj.Mult W v A' := hA'e ▸ mult_sub Me MA
  have Mx := mult_sub (mult_one W v) (GlobalTheory.SplitConj.mult_mul Mh MA)
  have Mx' := GlobalTheory.SplitConj.mult_add (mult_one W v) MA
  have My := GlobalTheory.SplitConj.mult_add (mult_one W v) MA'
  have My' := mult_sub (mult_one W v) (GlobalTheory.SplitConj.mult_mul Mh MA')
  have hu : ∀ u : AF F, evFin F v u = 0 →
      algebraMap (AF F) (AE F E) u * A = 0 ∧ algebraMap (AF F) (AE F E) u * A' = 0 := by
    intro u hu
    have h1 : algebraMap (AF F) (AE F E) u * e = 0 := by
      have := GlobalTheory.LatVac.at_liftV v 1 u hu
      rw [he, ← map_mul, ← smul_eq_mul, this, map_zero]
    have h3 : algebraMap (AF F) (AE F E) u * A = 0 := by
      rw [← hAe']; linear_combination A * h1
    exact ⟨h3, by rw [hA'e, mul_sub, h1, h3, sub_zero]⟩
  have hsm : (⅟2 : AF F) • A = h * A := Algebra.smul_def _ _
  rw [hsm]
  generalize hxe : 1 - h * A = x at *
  generalize hxe' : 1 + A = x' at *
  generalize hye : 1 + A' = y at *
  generalize hye' : 1 - h * A' = y' at *
  have i1 : h * (x + y) * (h * (x' + y')) + h * (x - y) * (h * (x' - y')) = 1 := by
    linear_combination 2 * h * h * hx + 2 * h * h * hy + (2 * h + 1) * h2h
  have i2 : h * (x + y) * (h * (x' - y')) + h * (x - y) * (h * (x' + y')) = 0 := by
    linear_combination 2 * h * h * hx - 2 * h * h * hy
  have i3 : h * (x' + y') * (h * (x + y)) + h * (x' - y') * (h * (x - y)) = 1 := by
    linear_combination i1
  have i4 : h * (x' + y') * (h * (x - y)) + h * (x' - y') * (h * (x + y)) = 0 := by
    linear_combination i2
  have ca : cA σ (h * (x + y)) = h * (x' + y') := by rw [map_mul, map_add, ch, cx, cy, add_comm]
  have cb : cA σ (h * (x - y)) = -(h * (x' - y')) := by rw [map_mul, map_sub, ch, cx, cy]; ring
  have hmem : (blk2 d (h * (x + y)) (h * (x - y)))ᵀ * dbl (incM F W.J) *
      (blk2 d (h * (x + y)) (h * (x - y))).map (cA σ) = dbl (incM F W.J) := by
    rw [symmetricScalarBlockMatrix_transpose, symmetricScalarBlockMatrix_map _ (map_zero _), ca, cb, dbl, symmetricScalarBlockMatrix_mul_gram_mul]
    have j1 : h * (x + y) * (h * (x' + y')) - h * (x - y) * -(h * (x' - y')) = 1 := by linear_combination i1
    have j2 : h * (x + y) * -(h * (x' - y')) - h * (x - y) * (h * (x' + y')) = 0 := by linear_combination -i2
    have j3 : h * (x - y) * (h * (x' + y')) - h * (x + y) * -(h * (x' - y')) = 0 := by linear_combination i2
    have j4 : h * (x - y) * -(h * (x' - y')) - h * (x + y) * (h * (x' + y')) = -1 := by linear_combination -i1
    rw [j1, j2, j3, j4, one_smul, zero_smul, neg_smul, one_smul]
  let s : GlobalTheory.InertDbl.UD σ W :=
    ⟨⟨blk2 d (h * (x + y)) (h * (x - y)), blk2 d (h * (x' + y')) (h * (x' - y')),
      by rw [symmetricScalarBlockMatrix_mul, i1, i2, symmetricScalarBlockMatrix_one_zero], by rw [symmetricScalarBlockMatrix_mul, i3, i4, symmetricScalarBlockMatrix_one_zero]⟩, hmem⟩
  have hs : GlobalTheory.InertDbl.matD s = blk2 d (h * (x + y)) (h * (x - y)) := rfl
  have hs' : GlobalTheory.InertDbl.matD s⁻¹ = blk2 d (h * (x' + y')) (h * (x' - y')) := rfl
  have hd : GlobalTheory.InertDbl.matD s * diagCols (Fin d) = diagCols (Fin d) * (x • (1 : Matrix (Fin d) (Fin d) (AE F E))) := by
    have : h * (x + y) + h * (x - y) = x := by linear_combination x * h2h
    have k := symmetricScalarBlockMatrix_mul_diagonalColumns (d := d) (h * (x + y)) (h * (x - y))
    rw [this] at k
    exact k
  refine ⟨s, ⟨⟨?_, ?_⟩, ⟨x • 1, x' • 1, ?_, ?_⟩, hd⟩, hd, ?_⟩
  · intro u hu0
    obtain ⟨u1, u2⟩ := hu u hu0
    have k1 : u • (h * (x + y) - 1) = 0 := by
      rw [Algebra.smul_def, ← hxe, ← hye]
      linear_combination (-h * h) * u1 + h * u2 + algebraMap (AF F) (AE F E) u * h2h
    have k2 : u • (h * (x - y)) = 0 := by
      rw [Algebra.smul_def, ← hxe, ← hye]
      linear_combination (-h * h) * u1 - h * u2
    rw [hs, symmetricScalarBlockMatrix_sub_one, blk2, Matrix.fromBlocks_smul, ← smul_assoc, ← smul_assoc, k1, k2, zero_smul,
      Matrix.fromBlocks_zero]
  · intro z hz
    rw [hs, hs']
    exact ⟨symmetricScalarBlockMatrix_mulVec_mem_doubledLattice (GlobalTheory.SplitConj.mult_mul Mh (GlobalTheory.SplitConj.mult_add Mx My))
        (GlobalTheory.SplitConj.mult_mul Mh (mult_sub Mx My)) z hz,
      symmetricScalarBlockMatrix_mulVec_mem_doubledLattice (GlobalTheory.SplitConj.mult_mul Mh (GlobalTheory.SplitConj.mult_add Mx' My'))
        (GlobalTheory.SplitConj.mult_mul Mh (mult_sub Mx' My')) z hz⟩
  · rw [Matrix.smul_mul, Matrix.one_mul, smul_smul, hx, one_smul]
  · rw [Matrix.smul_mul, Matrix.one_mul, smul_smul, mul_comm, hx, one_smul]
  · have : h * (x + y) - h * (x - y) = y := by linear_combination y * h2h
    have k := symmetricScalarBlockMatrix_mul_antidiagonalColumns (d := d) (h * (x + y)) (h * (x - y))
    rw [this] at k
    exact k

end GlobalTheory.SplitConjPar

end
