import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedBasisGramEqStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitDetAdaptedBasisStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.QhtUnip

noncomputable section

namespace GlobalTheory.LiftHeisW

variable {F E : Type} [Field F] [Field E] [Algebra F E]

theorem heis_unitary [CharZero E] (σ : E →ₐ[F] E) (hσ : ∀ e, σ (σ e) = e) {m : ℕ} (J₁ : Matrix (Fin m) (Fin m) E)
    (hJ : ∀ i j, σ (J₁ j i) = -J₁ i j) (w : Fin m → E) :
    (Heisenberg₂ (fun k => -∑ j, J₁ k j * σ (w j)) w (-(2 : E)⁻¹ * ∑ j, ∑ k, w j * J₁ j k * σ (w k)))ᵀ * gI J₁ *
      (Heisenberg₂ (fun k => -∑ j, J₁ k j * σ (w j)) w (-(2 : E)⁻¹ * ∑ j, ∑ k, w j * J₁ j k * σ (w k))).map σ = gI J₁ := by
  have h1 : ∑ x, ∑ y, σ (w x) * σ (J₁ x y) * σ (σ (w y)) = -∑ j, ∑ k, w j * J₁ j k * σ (w k) := by
    simp only [hσ, hJ]
    rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  have h2 : ∑ a, (∑ b, w b * J₁ b a) * σ (w a) = ∑ j, ∑ k, w j * J₁ j k * σ (w k) := by
    simp only [Finset.sum_mul]
    exact Finset.sum_comm
  have h3 : ∀ j, ∑ x, σ (J₁ j x) * σ (σ (w x)) = -∑ a, w a * J₁ a j := by
    intro j
    simp only [hσ, hJ, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  have hs2 : σ 2 = 2 := map_ofNat σ 2
  ext ((i|i)|i) ((j|j)|j) <;> (try obtain rfl := Subsingleton.elim i 0) <;> (try obtain rfl := Subsingleton.elim j 0) <;>
    simp [Heisenberg₂, gI, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.fromBlocks, Matrix.one_apply, Matrix.transpose_apply]
  all_goals first
    | (rw [h3]; ring)
    | (rw [h1, h2, hs2]; field_simp; ring)
    | done

theorem form_skew (σ : E →ₐ[F] E) (hσ : ∀ e, σ (σ e) = e) {n : ℕ} {J : Matrix (Fin n) (Fin n) E}
    (hJ : ∀ i j, σ (J j i) = -J i j) (x y : Fin n → E) : σ (form σ J x y) = -form σ J y x := by
  simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, hσ, hJ, Finset.mul_sum, ← Finset.sum_neg_distrib]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem mul_apply_form (σ : E →ₐ[F] E) {n : ℕ} {ι : Type} [Fintype ι] (J : Matrix (Fin n) (Fin n) E)
    (A B : Matrix (Fin n) ι E) (i j : ι) :
    (Aᵀ * J * B.map σ) i j = form σ J (fun r => A r i) (fun r => B r j) := by
  simp only [form, dotProduct, Matrix.mulVec, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
    Finset.sum_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

theorem heis_map {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {m : ℕ} (a w : Fin m → R) (α : R) :
    (Heisenberg₂ a w α).map f = Heisenberg₂ (fun k => f (a k)) (fun k => f (w k)) (f α) := by
  ext ((i|i)|i) ((j|j)|j) <;> (try obtain rfl := Subsingleton.elim i 0) <;> (try obtain rfl := Subsingleton.elim j 0) <;>
    simp [Heisenberg₂, Matrix.fromBlocks, Matrix.one_apply, apply_ite f]

end GlobalTheory.LiftHeisW

open GlobalTheory.LiftHeisW in

theorem GlobalTheory.LiftHeisW.exists_ratU_heis : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), (∀ e, σ (σ e) = e) → ∀ (B : Base F E) {m : ℕ} (W : Spc F E (m + 2)) (r s : ℕ), W.IsSkew σ B r s →
    ∀ (W₁ : Spc F E m) (H : Plane E (m + 2) m) (i₀ i₁ : ℕ), H.IsAdapted σ B W W₁ i₀ i₁ → ∀ w₀ : Fin m → E, ∃ γ ∈ ratU σ W.J, ∃ (a : Fin m → AE F E) (α : AE F E),
      crd H γ = Heisenberg₂ a (fun k => inclR (F := F) (AF F) (w₀ k)) α := by
  intro F E _ _ _ _ _ σ hσ B m W r s hW W₁ H i₀ i₁ hH w₀
  have hgram := GlobalTheory.T.adapted_basis_gram_eq F E σ hσ B W r s hW W₁ H i₀ i₁ hH
  have hP : IsUnit (basQ H).det := GlobalTheory.T.isUnit_det_adapted_basis F E σ B W r s hW W₁ H i₀ i₁ hH
  have hJ₁ : ∀ i j, σ (W₁.J j i) = -W₁.J i j := by
    intro i j
    have a := hgram (Sum.inl (Sum.inr j)) (Sum.inl (Sum.inr i))
    have b := hgram (Sum.inl (Sum.inr i)) (Sum.inl (Sum.inr j))
    simp only [gI, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₂₂] at a b
    rw [← a, ← b]
    exact form_skew σ hσ hW.skew _ _
  have mσ : ∀ A C : Matrix (Fin (m + 2)) (Fin (m + 2)) E, (A * C).map σ = A.map σ * C.map σ :=
    fun A C => Matrix.map_mul (f := σ.toRingHom)
  set a₀ : Fin m → E := fun k => -∑ j, W₁.J k j * σ (w₀ j) with ha₀
  set α₀ : E := -(2 : E)⁻¹ * ∑ j, ∑ k, w₀ j * W₁.J j k * σ (w₀ k) with hα₀
  set N := Heisenberg₂ a₀ w₀ α₀ with hNdef
  have hN : Nᵀ * gI W₁.J * N.map σ = gI W₁.J := heis_unitary σ hσ W₁.J hJ₁ w₀
  set P := basQ H with hPdef
  set N' := N.submatrix (ixE m) (ixE m) with hN'def
  set G' := (gI W₁.J).submatrix (ixE m) (ixE m) with hG'def
  have hPJ : Pᵀ * W.J * P.map σ = G' := by
    ext i j
    rw [mul_apply_form]
    exact hgram _ _
  have hN' : N'ᵀ * G' * N'.map σ = G' := by
    rw [hN'def, hG'def, Matrix.transpose_submatrix, ← Matrix.submatrix_map, Matrix.submatrix_mul_equiv,
      Matrix.submatrix_mul_equiv, hN]
  have hdetN : IsUnit N'.det := by
    rw [hN'def, Matrix.det_submatrix_equiv_self, hNdef, Heisenberg₂, Matrix.det_fromBlocks_zero₂₁,
      Matrix.det_fromBlocks_zero₂₁]
    simp
  have e1 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hP
  have e2 : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hP
  set M := P * N' * P⁻¹ with hMdef
  have hM : Mᵀ * W.J * M.map σ = W.J := by
    calc Mᵀ * W.J * M.map σ = (P⁻¹)ᵀ * (N'ᵀ * (Pᵀ * W.J * P.map σ) * N'.map σ) * P⁻¹.map σ := by
          simp only [hMdef, Matrix.transpose_mul, mσ, Matrix.mul_assoc]
      _ = (P⁻¹)ᵀ * (Pᵀ * W.J * P.map σ) * P⁻¹.map σ := by rw [hPJ, hN']
      _ = (P * P⁻¹)ᵀ * W.J * (P * P⁻¹).map σ := by
          simp only [Matrix.transpose_mul, mσ, Matrix.mul_assoc]
      _ = W.J := by
          rw [e1, Matrix.transpose_one, Matrix.map_one σ (map_zero σ) (map_one σ), Matrix.one_mul, Matrix.mul_one]
  have hdetM : IsUnit M.det := by
    rw [hMdef, Matrix.det_mul, Matrix.det_mul]
    exact (hP.mul hdetN).mul ((Matrix.isUnit_nonsing_inv_det_iff).mpr hP)
  let γE : GL (Fin (m + 2)) E := Matrix.nonsingInvUnit M hdetM
  let γA := Matrix.GeneralLinearGroup.map (inclR (F := F) (E := E) (AF F)) γE
  have hcoe : (γA : Matrix (Fin (m + 2)) (Fin (m + 2)) (AE F E)) = M.map (inclR (F := F) (AF F)) := rfl
  have hcA : ∀ e : E, cA σ (inclR (F := F) (AF F) e) = inclR (F := F) (AF F) (σ e) := by
    intro e
    simp [cA, inclR]
  have hmem : γA ∈ UG (cA σ) (incM F W.J) := by
    show (γA : Matrix (Fin (m + 2)) (Fin (m + 2)) (AE F E))ᵀ * incM F W.J *
      (γA : Matrix (Fin (m + 2)) (Fin (m + 2)) (AE F E)).map (cA σ) = incM F W.J
    rw [hcoe, incM, Matrix.map_map]
    have : (cA σ ∘ inclR (F := F) (AF F)) = (inclR (F := F) (AF F)) ∘ σ := funext hcA
    rw [this, ← Matrix.map_map, ← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, hM]
  refine ⟨⟨γA, hmem⟩, ?_, fun k => inclR (F := F) (AF F) (a₀ k), inclR (F := F) (AF F) α₀, ?_⟩
  · rw [ratU, Subgroup.mem_subgroupOf]
    exact ⟨γE, rfl⟩
  · have hinv : (incM F P)⁻¹ = incM F P⁻¹ := by
      apply Matrix.inv_eq_left_inv
      rw [incM, incM, ← Matrix.map_mul, e2, Matrix.map_one _ (map_zero _) (map_one _)]
    have hmat : mat (⟨γA, hmem⟩ : UA σ W.J) = M.map (inclR (F := F) (AF F)) := rfl
    have hPMP : P⁻¹ * M * P = N' := by
      rw [hMdef, Matrix.mul_assoc, Matrix.mul_assoc, e2, Matrix.mul_one, ← Matrix.mul_assoc, e2, Matrix.one_mul]
    rw [crd, hinv, hmat, ← hPdef, incM, incM, ← Matrix.map_mul, ← Matrix.map_mul, hPMP, hN'def, ← Matrix.submatrix_map,
      Matrix.submatrix_submatrix, Equiv.self_comp_symm, Matrix.submatrix_id_id, hNdef, heis_map]

end
