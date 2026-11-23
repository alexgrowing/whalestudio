import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinMapsOfForall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiCols
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalBlockOfMatrix
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.OneEqSumPlaceIdempotentsOverTwoAddTwoMul
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.DblVacGauss

open GlobalTheory.DblVac

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem evFin_invOf_two_mem (v : Pl F) (h : (2 : 𝓞 F) ∉ v.asIdeal) :
    evFin F v (⅟(2 : AF F)) ∈ v.adicCompletionIntegers F := by
  have e : evFin F v (⅟(2 : AF F)) = algebraMap F (Fv F v) (2 : F)⁻¹ := by
    have h1 : evFin F v (⅟(2 : AF F)) * 2 = 1 := by
      have := congrArg (evFin F v) (invOf_mul_self (2 : AF F))
      rwa [map_mul, map_ofNat, map_one] at this
    have h2 : algebraMap F (Fv F v) (2 : F)⁻¹ * 2 = 1 := by
      rw [← map_ofNat (algebraMap F (Fv F v)) 2, ← map_mul, inv_mul_cancel₀ two_ne_zero, map_one]
    have h20 : (2 : Fv F v) ≠ 0 := by
      intro h0; rw [h0, mul_zero] at h1; exact zero_ne_one h1
    exact mul_right_cancel₀ h20 (h1.trans h2.symm)
  rw [e]
  exact GlobalTheory.LatVac.half_mem_adicCompletionIntegers F v h

theorem invOf_two_smul_mem_latAt {d : ℕ} (W : Spc F E d) (v : Pl F) (h : (2 : 𝓞 F) ∉ v.asIdeal)
    {z : Fin d → AE F E} (hz : z ∈ GlobalTheory.InertSph.latAt W v) : (⅟(2 : AF F)) • z ∈ GlobalTheory.InertSph.latAt W v := by
  induction hz using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨a, ha, hai, y, hy, rfl⟩ := hx
    refine AddSubgroup.subset_closure ⟨⅟(2 : AF F) * a, fun u hu => ?_, ?_, y, hy, by rw [mul_smul]⟩
    · have := ha u hu
      simp only [smul_eq_mul] at this ⊢
      rw [mul_left_comm, this, mul_zero]
    · rw [map_mul]; exact mul_mem (evFin_invOf_two_mem v h) hai
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

section Grp

variable {σ : E →ₐ[F] E} {d : ℕ} {W : Spc F E d} {v : Pl F}

theorem matD_mul (g h : UD σ W) : matD (g * h) = matD g * matD h := rfl

theorem matD_inv_mul (g : UD σ W) : matD g⁻¹ * matD g = 1 := by
  rw [← matD_mul, inv_mul_cancel]; rfl

theorem mul_mem_KD {g h : UD σ W} (hg : g ∈ KD σ W v) (hh : h ∈ KD σ W v) : g * h ∈ KD σ W v := by
  refine ⟨fun u hu => ?_, fun z hz => ⟨?_, ?_⟩⟩
  · have e : matD (g * h) - 1 = (matD g - 1) * matD h + (matD h - 1) := by
      rw [matD_mul, Matrix.sub_mul, Matrix.one_mul]; abel
    rw [e, smul_add, ← Matrix.smul_mul, hg.1 u hu, hh.1 u hu, Matrix.zero_mul, add_zero]
  · rw [matD_mul, ← Matrix.mulVec_mulVec]; exact (hg.2 _ (hh.2 z hz).1).1
  · rw [mul_inv_rev, matD_mul, ← Matrix.mulVec_mulVec]; exact (hh.2 _ (hg.2 z hz).2).2

theorem inv_mem_KD {g : UD σ W} (hg : g ∈ KD σ W v) : g⁻¹ ∈ KD σ W v := by
  refine ⟨fun u hu => ?_, fun z hz => ⟨(hg.2 z hz).2, ?_⟩⟩
  · have e : matD g⁻¹ - 1 = -(matD g⁻¹ * (matD g - 1)) := by
      rw [Matrix.mul_sub, matD_inv_mul, Matrix.mul_one]; abel
    rw [e, smul_neg, ← Matrix.mul_smul, hg.1 u hu, Matrix.mul_zero, neg_zero]
  · rw [inv_inv]; exact (hg.2 z hz).1

end Grp

section Blocks

variable {σ : E →ₐ[F] E} {d : ℕ} {W : Spc F E d} {v : Pl F}

def nb (Z : Matrix (Fin d) (Fin d) (AE F E)) : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E) :=
  Matrix.fromBlocks (1 + Z) Z (-Z) (1 - Z)

theorem nb_mul_nb_neg (Z : Matrix (Fin d) (Fin d) (AE F E)) : nb Z * nb (-Z) = 1 := by
  rw [nb, nb, Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one]
  refine Matrix.fromBlocks_inj.mpr ⟨?_, ?_, ?_, ?_⟩ <;> noncomm_ring

theorem mapc_eq (σ : E →ₐ[F] E) {ι : Type} [Fintype ι] [DecidableEq ι] (X : Matrix ι ι (AE F E)) :
    X.map (cA σ) = (cA σ).mapMatrix X := rfl

theorem nb_unitary {J : Matrix (Fin d) (Fin d) (AE F E)} {Z : Matrix (Fin d) (Fin d) (AE F E)}
    (hZ : Zᵀ * J + J * Z.map (cA σ) = 0) : (nb Z)ᵀ * dbl J * (nb Z).map (cA σ) = dbl J := by
  rw [nb, dbl, Matrix.fromBlocks_transpose, Matrix.fromBlocks_map, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_multiply]
  simp only [mapc_eq, map_add, map_sub, map_neg, map_one, Matrix.transpose_add, Matrix.transpose_sub,
    Matrix.transpose_neg, Matrix.transpose_one] at hZ ⊢
  refine Matrix.fromBlocks_inj.mpr ⟨?_, ?_, ?_, ?_⟩ <;> rw [← sub_eq_zero] <;> refine Eq.trans ?_ hZ <;> noncomm_ring

end Blocks

section Elt

attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid

theorem fromBlocks_mul_fromRows' {d : ℕ} (A B C D X Y : Matrix (Fin d) (Fin d) (AE F E)) :
    Matrix.fromBlocks A B C D * Matrix.fromRows X Y = Matrix.fromRows (A * X + B * Y) (C * X + D * Y) := by
  ext (i | i) j <;> simp [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr, Matrix.add_apply]

variable {σ : E →ₐ[F] E} {d : ℕ} {W : Spc F E d} {v : Pl F}

def nbU (σ : E →ₐ[F] E) (W : Spc F E d) (Z : Matrix (Fin d) (Fin d) (AE F E))
    (hZ : Zᵀ * incM F W.J + incM F W.J * Z.map (cA σ) = 0) : UD σ W :=
  ⟨⟨nb Z, nb (-Z), nb_mul_nb_neg Z, by simpa using nb_mul_nb_neg (-Z)⟩, nb_unitary hZ⟩

theorem matD_nbU (Z : Matrix (Fin d) (Fin d) (AE F E))
    (hZ : Zᵀ * incM F W.J + incM F W.J * Z.map (cA σ) = 0) : matD (nbU σ W Z hZ) = nb Z := rfl

theorem matD_nbU_inv (Z : Matrix (Fin d) (Fin d) (AE F E))
    (hZ : Zᵀ * incM F W.J + incM F W.J * Z.map (cA σ) = 0) : matD (nbU σ W Z hZ)⁻¹ = nb (-Z) := rfl

theorem nb_mulVec_mem {Z : Matrix (Fin d) (Fin d) (AE F E)}
    (hZ : ∀ w ∈ GlobalTheory.InertSph.latAt W v, Z *ᵥ w ∈ GlobalTheory.InertSph.latAt W v) :
    ∀ z ∈ latD W v, nb Z *ᵥ z ∈ latD W v := by
  intro z hz
  obtain ⟨h1, h2⟩ := hz
  rw [nb, Matrix.fromBlocks_mulVec]
  refine ⟨?_, ?_⟩
  · rw [Sum.elim_comp_inl]
    have e : (1 + Z) *ᵥ (z ∘ Sum.inl) + Z *ᵥ (z ∘ Sum.inr) = z ∘ Sum.inl + Z *ᵥ (z ∘ Sum.inl + z ∘ Sum.inr) := by
      rw [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.mulVec_add, add_assoc]
    rw [e]; exact add_mem h1 (hZ _ (add_mem h1 h2))
  · rw [Sum.elim_comp_inr]
    have e : (-Z) *ᵥ (z ∘ Sum.inl) + (1 - Z) *ᵥ (z ∘ Sum.inr) = z ∘ Sum.inr - Z *ᵥ (z ∘ Sum.inl + z ∘ Sum.inr) := by
      rw [Matrix.neg_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_add]; abel
    rw [e]; exact sub_mem h2 (hZ _ (add_mem h1 h2))

theorem nb_sub_one (Z : Matrix (Fin d) (Fin d) (AE F E)) : nb Z - 1 = Matrix.fromBlocks Z Z (-Z) (-Z) := by
  rw [nb, ← Matrix.fromBlocks_one, sub_eq_add_neg, Matrix.fromBlocks_neg, Matrix.fromBlocks_add]
  congr 1 <;> abel

theorem nbU_mem_KD (Z : Matrix (Fin d) (Fin d) (AE F E))
    (hZ : Zᵀ * incM F W.J + incM F W.J * Z.map (cA σ) = 0)
    (hs : ∀ u, evFin F v u = 0 → u • Z = 0)
    (hl : ∀ w ∈ GlobalTheory.InertSph.latAt W v, Z *ᵥ w ∈ GlobalTheory.InertSph.latAt W v) : nbU σ W Z hZ ∈ KD σ W v := by
  refine ⟨fun u hu => ?_, fun z hz => ⟨?_, ?_⟩⟩
  · rw [matD_nbU, nb_sub_one, Matrix.fromBlocks_smul, smul_neg, hs u hu, neg_zero, Matrix.fromBlocks_zero]
  · rw [matD_nbU]; exact nb_mulVec_mem hl z hz
  · rw [matD_nbU_inv]
    refine nb_mulVec_mem (fun w hw => ?_) z hz
    rw [Matrix.neg_mulVec]; exact neg_mem (hl w hw)

theorem nbU_mem_PAnti (Z : Matrix (Fin d) (Fin d) (AE F E))
    (hZ : Zᵀ * incM F W.J + incM F W.J * Z.map (cA σ) = 0) : nbU σ W Z hZ ∈ PAnti σ W := by
  refine ⟨1, ?_⟩
  have e : nb Z * (Matrix.fromRows 1 (-1) : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E)) =
      (Matrix.fromRows 1 (-1) : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E)) * (1 : Matrix (Fin d) (Fin d) (AE F E)) := by
    rw [Matrix.mul_one, nb, fromBlocks_mul_fromRows']
    congr 1 <;> noncomm_ring
  exact e

end Elt

section Main

attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid

theorem invOf_two_smul_add_self {M : Type} [AddCommGroup M] [Module (AF F) M] (x : M) :
    ⅟(2 : AF F) • x + ⅟(2 : AF F) • x = x := by
  rw [← add_smul, invOf_two_add_invOf_two, one_smul]

theorem fromRows_mul' {d : ℕ} (X Y B : Matrix (Fin d) (Fin d) (AE F E)) :
    Matrix.fromRows X Y * B = Matrix.fromRows (X * B) (Y * B) := by
  ext (i | i) j <;> simp [Matrix.mul_apply, Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr]

theorem gauss_decomp : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    {d : ℕ} (W : Spc F E d) (v : Pl F), (2 : 𝓞 F) ∉ v.asIdeal → ∀ g ∈ GlobalTheory.DblVac.KD σ W v, GlobalTheory.DblVac.BigCell W v g →
      ∃ q ∈ GlobalTheory.DblVac.KD σ W v, q ∈ GlobalTheory.DblVac.PAnti σ W ∧ ∃ p ∈ GlobalTheory.DblVac.KD σ W v, p ∈ GlobalTheory.DblVac.PDiag σ W ∧
        g = q * p := by
  intro F E _ _ _ _ _ σ d W v h2 g hg hbig
  obtain ⟨M, hMA, hM⟩ := hbig
  set G := matD g with hG
  set J := incM F W.J with hJ
  set a := G.toBlocks₁₁ with ha
  set b := G.toBlocks₁₂ with hb
  set c := G.toBlocks₂₁ with hc
  set e := G.toBlocks₂₂ with he
  set A := diagonalBlockOfMatrix g with hA
  have hAdef : A = ⅟(2 : AF F) • (a + b + c + e) := rfl
  obtain ⟨C, hC⟩ : ∃ C : Matrix (Fin d) (Fin d) (AE F E), C = ⅟(2 : AF F) • (a + b - (c + e)) := ⟨_, rfl⟩
  have hAM : A * M = 1 := mul_eq_one_comm.mp hMA
  have hP : a + b = A + C := by
    rw [hAdef, hC, ← smul_add]
    have : a + b + c + e + (a + b - (c + e)) = (a + b) + (a + b) := by abel
    rw [this, smul_add, invOf_two_smul_add_self]
  have hQ : c + e = A - C := by
    rw [hAdef, hC, ← smul_sub]
    have : a + b + c + e - (a + b - (c + e)) = (c + e) + (c + e) := by abel
    rw [this, smul_add, invOf_two_smul_add_self]

  have hU : (Matrix.fromBlocks a b c e)ᵀ * dbl J * (Matrix.fromBlocks a b c e).map (cA σ) = dbl J := by
    rw [ha, hb, hc, he, Matrix.fromBlocks_toBlocks]; exact g.2
  rw [dbl, Matrix.fromBlocks_transpose, Matrix.fromBlocks_map, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_multiply] at hU
  obtain ⟨h11, h12, h21, h22⟩ := Matrix.fromBlocks_inj.mp hU
  simp only [mapc_eq] at h11 h12 h21 h22
  have hsum : (a + b)ᵀ * J * (cA σ).mapMatrix (a + b) - (c + e)ᵀ * J * (cA σ).mapMatrix (c + e) = 0 := by
    have := congrArg₂ HAdd.hAdd (congrArg₂ HAdd.hAdd h11 h12) (congrArg₂ HAdd.hAdd h21 h22)
    rw [show (0 : Matrix (Fin d) (Fin d) (AE F E)) = J + 0 + (0 + -J) by abel, ← this]
    simp only [map_add, Matrix.transpose_add]
    noncomm_ring
  have h2x : (Aᵀ * J * (cA σ).mapMatrix C + Cᵀ * J * (cA σ).mapMatrix A) +
      (Aᵀ * J * (cA σ).mapMatrix C + Cᵀ * J * (cA σ).mapMatrix A) = 0 := by
    rw [← hsum, hP, hQ]
    simp only [map_add, map_sub, Matrix.transpose_add, Matrix.transpose_sub]
    noncomm_ring
  have hkey : Aᵀ * J * (cA σ).mapMatrix C + Cᵀ * J * (cA σ).mapMatrix A = 0 := by
    rw [← invOf_two_smul_add_self (F := F) (Aᵀ * J * (cA σ).mapMatrix C + Cᵀ * J * (cA σ).mapMatrix A), ← smul_add, h2x,
      smul_zero]
  have hAMc : (cA σ).mapMatrix A * (cA σ).mapMatrix M = 1 := by rw [← map_mul, hAM, map_one]
  have hAMt : Mᵀ * Aᵀ = 1 := by rw [← Matrix.transpose_mul, hAM, Matrix.transpose_one]
  have hY : (C * M)ᵀ * J + J * (cA σ).mapMatrix (C * M) = 0 := by
    rw [Matrix.transpose_mul, map_mul]
    calc Mᵀ * Cᵀ * J + J * ((cA σ).mapMatrix C * (cA σ).mapMatrix M)
        = Mᵀ * Cᵀ * J * ((cA σ).mapMatrix A * (cA σ).mapMatrix M) +
          Mᵀ * Aᵀ * J * ((cA σ).mapMatrix C * (cA σ).mapMatrix M) := by
          rw [hAMc, hAMt, Matrix.mul_one, Matrix.one_mul]
      _ = Mᵀ * (Aᵀ * J * (cA σ).mapMatrix C + Cᵀ * J * (cA σ).mapMatrix A) * (cA σ).mapMatrix M := by noncomm_ring
      _ = 0 := by rw [hkey, Matrix.mul_zero, Matrix.zero_mul]
  obtain ⟨Z, hZdef⟩ : ∃ Z : Matrix (Fin d) (Fin d) (AE F E), Z = ⅟(2 : AF F) • (C * M) := ⟨_, rfl⟩
  have hZ : Zᵀ * incM F W.J + incM F W.J * Z.map (cA σ) = 0 := by
    rw [← hJ, hZdef, mapc_eq, map_smul, Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, hY,
      smul_zero]

  have hs : ∀ u, evFin F v u = 0 → u • Z = 0 := by
    intro u hu
    have hG1 : u • G = u • (1 : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)) := by
      have := hg.1 u hu
      rwa [smul_sub, sub_eq_zero] at this
    have e1 : u • a = u • (1 : Matrix (Fin d) (Fin d) (AE F E)) := by
      have : u • a = (u • G).toBlocks₁₁ := rfl
      rw [this, hG1]; ext i j; simp [Matrix.toBlocks₁₁, Matrix.one_apply]
    have e2 : u • b = 0 := by
      have : u • b = (u • G).toBlocks₁₂ := rfl
      rw [this, hG1]; ext i j; simp [Matrix.toBlocks₁₂, Matrix.one_apply]
    have e3 : u • c = 0 := by
      have : u • c = (u • G).toBlocks₂₁ := rfl
      rw [this, hG1]; ext i j; simp [Matrix.toBlocks₂₁, Matrix.one_apply]
    have e4 : u • e = u • (1 : Matrix (Fin d) (Fin d) (AE F E)) := by
      have : u • e = (u • G).toBlocks₂₂ := rfl
      rw [this, hG1]; ext i j; simp [Matrix.toBlocks₂₂, Matrix.one_apply]
    have hCu : u • C = 0 := by
      rw [hC, smul_comm, smul_sub, smul_add, smul_add, e1, e2, e3, e4, add_zero, zero_add, sub_self, smul_zero]
    rw [hZdef, smul_comm, ← Matrix.smul_mul, hCu, Matrix.zero_mul, smul_zero]

  have hl : ∀ w ∈ GlobalTheory.InertSph.latAt W v, Z *ᵥ w ∈ GlobalTheory.InertSph.latAt W v := by
    intro w hw
    have hMw := hM w hw
    have hy : Sum.elim (M *ᵥ w) (M *ᵥ w) ∈ latD W v :=
      ⟨by rw [Sum.elim_comp_inl]; exact hMw, by rw [Sum.elim_comp_inr]; exact hMw⟩
    obtain ⟨g1, g2⟩ := (hg.2 _ hy).1
    rw [← hG, ← Matrix.fromBlocks_toBlocks G, Matrix.fromBlocks_mulVec] at g1 g2
    simp only [Sum.elim_comp_inl, Sum.elim_comp_inr] at g1 g2
    have eZ : Z *ᵥ w = ⅟(2 : AF F) • ⅟(2 : AF F) • ((a *ᵥ (M *ᵥ w) + b *ᵥ (M *ᵥ w)) - (c *ᵥ (M *ᵥ w) + e *ᵥ (M *ᵥ w))) := by
      rw [hZdef, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec, hC, Matrix.smul_mulVec, Matrix.sub_mulVec,
        Matrix.add_mulVec, Matrix.add_mulVec]
    rw [eZ]
    exact invOf_two_smul_mem_latAt W v h2 (invOf_two_smul_mem_latAt W v h2 (sub_mem g1 g2))

  set q := nbU σ W Z hZ with hq
  have hqK : q ∈ KD σ W v := nbU_mem_KD Z hZ hs hl
  refine ⟨q, hqK, nbU_mem_PAnti Z hZ, q⁻¹ * g, mul_mem_KD (inv_mem_KD hqK) hg, ⟨⟨A, M, hAM, hMA⟩, ?_⟩,
    (mul_inv_cancel_left q g).symm⟩
  have hZA : Z * A + Z * A = C := by
    rw [hZdef, Matrix.smul_mul, Matrix.mul_assoc, hMA, Matrix.mul_one, invOf_two_smul_add_self]
  have eG : G * (diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E)) = Matrix.fromRows (A + C) (A - C) := by
    rw [← Matrix.fromBlocks_toBlocks G, diagCols, fromBlocks_mul_fromRows', Matrix.mul_one, Matrix.mul_one,
      Matrix.mul_one, Matrix.mul_one, ← ha, ← hb, ← hc, ← he, hP, hQ]
  have ep : nb (-Z) * G * (diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E)) =
      (diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E)) * A := by
    rw [Matrix.mul_assoc, eG, nb, fromBlocks_mul_fromRows', diagCols, fromRows_mul', Matrix.one_mul]
    congr 1
    · rw [← sub_eq_zero]
      calc _ = C - (Z * A + Z * A) := by noncomm_ring
        _ = 0 := by rw [hZA, sub_self]
    · rw [← sub_eq_zero]
      calc _ = (Z * A + Z * A) - C := by noncomm_ring
        _ = 0 := by rw [hZA, sub_self]
  exact ep

end Main

end GlobalTheory.DblVacGauss
