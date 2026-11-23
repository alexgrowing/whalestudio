import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.VacuumUnderAdelicPairModulusOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaSpanRationalTranslatesVacuum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ApplyAt0Smul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaFunctionRationalTranslateMemStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMovesOfSelfDual
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField Polynomial
open scoped Pointwise nonZeroDivisors
open Formalism.L2.Host (HChar embTau)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.FunObj GlobalTheory.FunObj.SqNum

namespace GlobalTheory.CongSplitFactor

variable {D : D7} {N : ℕ}

noncomputable def phi (e : AE D) (A : Matrix (Fin N) (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D) :=
  e • A + (1 - e) • (1 : Matrix (Fin N) (Fin N) (AE D))

theorem phi_apply (e : AE D) (A : Matrix (Fin N) (Fin N) (AE D)) (i j : Fin N) :
    phi e A i j = e * A i j + (1 - e) * (1 : Matrix (Fin N) (Fin N) (AE D)) i j := by
  simp [phi, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]

theorem phi_sub_one (e : AE D) (A : Matrix (Fin N) (Fin N) (AE D)) :
    phi e A - 1 = e • (A - 1) := by
  rw [phi, sub_smul, one_smul, smul_sub]; abel

theorem phi_one (e : AE D) : phi e (1 : Matrix (Fin N) (Fin N) (AE D)) = 1 := by
  rw [phi, ← add_smul, add_sub_cancel, one_smul]

theorem phi_mul {e : AE D} (he : e * e = e) (A B : Matrix (Fin N) (Fin N) (AE D)) :
    phi e A * phi e B = phi e (A * B) := by
  have h1 : (1 - e) * e = 0 := by rw [sub_mul, one_mul, he, sub_self]
  have h2 : e * (1 - e) = 0 := by rw [mul_sub, mul_one, he, sub_self]
  have h3 : (1 - e) * (1 - e) = 1 - e := by
    rw [sub_mul, one_mul, mul_sub, mul_one, he, sub_self, sub_zero]
  simp only [phi, add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.one_mul,
    Matrix.mul_one, he, h1, h2, h3, zero_smul, add_zero, zero_add]

theorem phi_mul_compl {e : AE D} (he : e * e = e) (A : Matrix (Fin N) (Fin N) (AE D)) :
    phi e A * phi (1 - e) A = A := by
  have h1 : (1 - e) * e = 0 := by rw [sub_mul, one_mul, he, sub_self]
  have h2 : e * (1 - e) = 0 := by rw [mul_sub, mul_one, he, sub_self]
  have h3 : (1 - e) * (1 - e) = 1 - e := by
    rw [sub_mul, one_mul, mul_sub, mul_one, he, sub_self, sub_zero]
  simp only [phi, sub_sub_cancel, add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    Matrix.one_mul, Matrix.mul_one, he, h1, h2, h3, zero_smul, add_zero, zero_add]
  rw [← add_smul, sub_add_cancel, one_smul]

noncomputable def phiHom {e : AE D} (he : e * e = e) :
    Matrix (Fin N) (Fin N) (AE D) →* Matrix (Fin N) (Fin N) (AE D) where
  toFun := phi e
  map_one' := phi_one e
  map_mul' A B := (phi_mul he A B).symm

theorem phi_map (e : AE D) (A : Matrix (Fin N) (Fin N) (AE D)) :
    (phi e A).map (sgA D) = phi (sgA D e) (A.map (sgA D)) := by
  ext i j
  simp only [Matrix.map_apply, phi_apply, map_add, map_mul, map_sub, map_one]
  by_cases h : i = j <;> simp [Matrix.one_apply, h]

theorem phi_transpose (e : AE D) (A : Matrix (Fin N) (Fin N) (AE D)) :
    (phi e A).transpose = phi e A.transpose := by
  simp [phi, Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_one]

theorem phi_mem_OhE {e : AE D} (he : e ∈ OhE D) {A : Matrix (Fin N) (Fin N) (AE D)}
    (hA : ∀ i j, A i j ∈ OhE D) (i j : Fin N) : phi e A i j ∈ OhE D := by
  rw [phi_apply]
  refine add_mem (mul_mem he (hA i j)) (mul_mem (sub_mem (one_mem _) he) ?_)
  by_cases h : i = j
  · simp [Matrix.one_apply, h, one_mem]
  · simp [Matrix.one_apply, h, zero_mem]

theorem hatId_mul {𝔪 : Ideal (𝓞 D.host.E)} {x : AE D} (hx : x ∈ hatId D 𝔪) {s : AE D}
    (hs : s ∈ OhE D) : s * x ∈ hatId D 𝔪 := by
  unfold hatId at hx ⊢
  induction hx using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨b, hb, t, ht, rfl⟩ := hy
    exact AddSubgroup.subset_closure ⟨b, hb, s * t, mul_mem hs ht, by ring⟩
  | zero => simp
  | add a b _ _ ha hb => rw [mul_add]; exact add_mem ha hb
  | neg a _ ha => rw [mul_neg]; exact neg_mem ha

noncomputable def part {e : AE D} (he : e * e = e) (hse : sgA D e = e) (k : GA D N) : GA D N :=
  ⟨Units.map (phiHom he) (k : GL (Fin N) (AE D)), by
    rw [PtsMem.mem_GA]
    have hk := (PtsMem.mem_GA D (k : GL (Fin N) (AE D))).1 k.2
    show ((phi e (↑(k : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D))).map (sgA D)).transpose *
      phi e (↑(k : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) = 1
    rw [phi_map, hse, phi_transpose, phi_mul he, hk, phi_one]⟩

theorem part_val {e : AE D} (he : e * e = e) (hse : sgA D e = e) (k : GA D N) :
    (((part he hse k : GA D N) : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) =
      phi e ((k : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) := rfl

theorem part_inv_val {e : AE D} (he : e * e = e) (hse : sgA D e = e) (k : GA D N) :
    ((((part he hse k : GA D N) : GL (Fin N) (AE D))⁻¹ : GL (Fin N) (AE D)) :
      Matrix (Fin N) (Fin N) (AE D)) =
      phi e (((k : GL (Fin N) (AE D))⁻¹ : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) := rfl

theorem part_intG {e : AE D} (he : e * e = e) (hse : sgA D e = e) (heO : e ∈ OhE D) {k : GA D N}
    (hk : k ∈ intG D N) : part he hse k ∈ intG D N := by
  rw [mem_intG] at hk ⊢
  intro i j
  refine ⟨?_, ?_⟩
  · rw [part_val]; exact phi_mem_OhE heO (fun a b => (hk a b).1) i j
  · rw [part_inv_val]; exact phi_mem_OhE heO (fun a b => (hk a b).2) i j

theorem part_sub_one_apply {e : AE D} (he : e * e = e) (hse : sgA D e = e) (k : GA D N) (i j : Fin N) :
    (((part he hse k : GA D N) : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) i j -
        (1 : Matrix (Fin N) (Fin N) (AE D)) i j =
      e * ((((k : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) - 1) i j) := by
  rw [← Matrix.sub_apply, part_val, phi_sub_one, Matrix.smul_apply, smul_eq_mul]

theorem exists_split_inert_factor : ∀ {D : D7} {N : ℕ} {𝔪 : Ideal (𝓞 D.host.E)} {k : GA D N},
    k ∈ intG D N → CongOne D 𝔪 k →
    ∃ ks ki : GA D N, k = ks * ki ∧ ks ∈ intG D N ∧ ki ∈ intG D N ∧ CongOne D 𝔪 ks ∧
      SuppSplit D (ks : GL (Fin N) (AE D)) ∧ SuppInert D (ki : GL (Fin N) (AE D)) := by
  intro D N 𝔪 k hk hc
  obtain ⟨ε, hεO, hεε, hεs, hq⟩ := VacMove.exists_half_idem D
  set e := ε + sgA D ε with he_def
  have heO : e ∈ OhE D := add_mem hεO (VacMove.sgA_mem D hεO)
  have hse : sgA D e = e := by rw [he_def, map_add, VacMove.sgA_sgA, add_comm]
  have hee : e * e = e := by
    have h2 : sgA D ε * sgA D ε = sgA D ε := by rw [← map_mul, hεε]
    have h3 : sgA D ε * ε = 0 := by rw [mul_comm, hεs]
    rw [he_def, add_mul, mul_add, mul_add, hεε, hεs, h3, h2, zero_add, add_zero]
  have hfO : 1 - e ∈ OhE D := sub_mem (one_mem _) heO
  have hsf : sgA D (1 - e) = 1 - e := by rw [map_sub, map_one, hse]
  have hff : (1 - e) * (1 - e) = 1 - e := by
    rw [sub_mul, one_mul, mul_sub, mul_one, hee, sub_self, sub_zero]
  refine ⟨part hee hse k, part hff hsf k, ?_, part_intG hee hse heO hk, part_intG hff hsf hfO hk,
    ?_, ?_, ?_⟩
  · apply Subtype.ext; apply Units.ext
    show ((k : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) =
      phi e ((k : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) *
        phi (1 - e) ((k : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D))
    rw [phi_mul_compl hee]
  · intro i j
    show ((((part hee hse k : GA D N) : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) - 1) i j ∈ hatId D 𝔪
    rw [Matrix.sub_apply, part_sub_one_apply]
    exact hatId_mul (hc i j) heO
  · intro q hqp hin i j
    rw [part_sub_one_apply]
    exact VacMove.zeroAt_mul D hqp ((hq q hqp).1 hin) _
  · intro q hqp hin i j
    rw [part_sub_one_apply]
    exact VacMove.zeroAt_mul D hqp ((hq q hqp).2 hin) _

end GlobalTheory.CongSplitFactor
