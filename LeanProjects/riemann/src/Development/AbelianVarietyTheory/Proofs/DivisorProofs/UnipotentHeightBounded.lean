import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCuspW
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRegFamConst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundedAdelesSubringStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstMemBoundedAdelesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjMemBoundedAdelesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundedAdelesModGlobalElementsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeightBoundedOfBoundedEntriesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitDetAdaptedBasisStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedBasisGramEqStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoordsPreserveGramMatrixStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentCoordsHeisenbergStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergCoordsFormulaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalHeisenbergTranslateExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalHeisenbergCenterExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisMulHeisStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoordsMultiplicativeConjugationStatement

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.QhtUnip

namespace GlobalTheory.QhtUnip

theorem qht_bdd_unip : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), (∀ e, σ (σ e) = e) → ∀ (B : Base F E) {d d₁ : ℕ}
    (W : Spc F E d) (r s : ℕ), W.IsSkew σ B r s → ∀ (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ), H'.IsAdapted σ B W W₁ i₀ i₁ →
    ∀ h : UA σ W.J, ∃ C : ℝ, ∀ u ∈ unip σ W H', (qht (u * h) : ℝ) ≤ C := by
  intro F E _ _ _ _ _ σ hσ B d d₁ W r s hW W₁ H' i₀ i₁ hA h
  obtain rfl := hA.rank
  suffices key : ∃ K : ℝ≥0, ∀ u ∈ unip σ W H', ∃ γ ∈ ratU σ W.J, heightGL F (γ * u).1 ≤ K by
    obtain ⟨K, hK⟩ := key
    refine ⟨K * ht h, fun u hu => ?_⟩
    obtain ⟨γ, hγ, hγK⟩ := hK u hu
    have h1 : qht (u * h) ≤ ht ((⟨γ, hγ⟩ : ratU σ W.J).1 * (u * h)) :=
      ciInf_le (OrderBot.bddBelow _) (⟨γ, hγ⟩ : ratU σ W.J)
    have h2 : ht ((⟨γ, hγ⟩ : ratU σ W.J).1 * (u * h)) ≤ K * ht h := by
      show heightGL F (γ * (u * h)).1 ≤ K * heightGL F h.1
      rw [← mul_assoc]
      calc heightGL F ((γ * u) * h).1 = heightGL F ((γ * u).1 * h.1) := rfl
        _ ≤ heightGL F (γ * u).1 * heightGL F h.1 := heightGL_mul_le F _ _
        _ ≤ K * heightGL F h.1 := mul_le_mul_of_nonneg_right hγK zero_le
    exact_mod_cast h1.trans h2
  have hP := GlobalTheory.T.isUnit_det_adapted_basis F E σ B W r s hW W₁ H' i₀ i₁ hA
  obtain ⟨hmul, hone, hmat⟩ := GlobalTheory.T.coords_multiplicative_conjugation F E σ W.J H' hP
  let ι := unip σ W H'
  obtain ⟨R, hR⟩ := GlobalTheory.T.bounded_adeles_subring F E ι
  have mem : ∀ f : ι → AE F E, f ∈ Bdd F E ι → f ∈ R := fun f hf => by rw [← SetLike.mem_coe, hR]; exact hf
  have cst : ∀ x : E, (fun _ : ι => inclR (F := F) (AF F) x) ∈ R := fun x => mem _ (GlobalTheory.T.const_mem_bounded_adeles F E ι x)
  have cnj : ∀ f : ι → AE F E, f ∈ R → (fun t => cA σ (f t)) ∈ R := fun f hf =>
    mem _ (GlobalTheory.T.conj_mem_bounded_adeles F E σ ι f (by rw [← hR]; exact hf))
  have sumB : ∀ {κ : Type} (s : Finset κ) (f : κ → ι → AE F E), (∀ i ∈ s, f i ∈ R) → (fun t => ∑ i ∈ s, f i t) ∈ R :=
    fun s f hf => by
      convert R.sum_mem hf using 1
      funext t; simp [Finset.sum_apply]
  have heisB : ∀ (a' w' : ι → Fin d₁ → AE F E) (α' : ι → AE F E), (∀ k, (fun t => a' t k) ∈ R) →
      (∀ k, (fun t => w' t k) ∈ R) → α' ∈ R → ∀ i j, (fun t => Heisenberg₂ (a' t) (w' t) (α' t) i j) ∈ R := by
    intro a' w' α' ha hw hα i j
    rcases i with ((i | i) | i) <;> rcases j with ((j | j) | j) <;>
      simp only [Heisenberg₂, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
        Matrix.fromBlocks_apply₂₂, Matrix.one_apply, Matrix.zero_apply, Matrix.of_apply, Sum.elim_inl, Sum.elim_inr]
    all_goals first
      | exact R.zero_mem | exact R.one_mem | exact ha _ | exact hw _ | exact hα
      | (by_cases hij : i = j <;> simp only [hij, if_true, if_false] <;> first | exact R.one_mem | exact R.zero_mem)

  have hsh := fun u : ι => GlobalTheory.T.unipotent_coords_heisenberg F E σ hσ B W r s hW W₁ H' i₀ i₁ hA u.1 u.2
  choose a w α hu using hsh
  have hap := fun k : Fin d₁ => GlobalTheory.T.bounded_adeles_mod_global_elements F E ι (fun t => w t k)
  choose e he using hap
  have hl := fun t : ι => GlobalTheory.T.rational_heisenberg_translate_exists F E σ hσ B W r s hW W₁ H' i₀ i₁ hA (fun k => -e k t)
  choose γ hγ aγ αγ hγc using hl
  let a₂ : ι → Fin d₁ → AE F E := fun t => aγ t + a t
  let w₂ : ι → Fin d₁ → AE F E := fun t => (fun k => inclR (F := F) (AF F) (-e k t)) + w t
  let α₂ : ι → AE F E := fun t => αγ t + α t + ∑ k, aγ t k * w t k
  have hv : ∀ t : ι, crd H' (γ t * t.1) = Heisenberg₂ (a₂ t) (w₂ t) (α₂ t) := fun t => by
    rw [hmul, hγc t, hu t, GlobalTheory.T.heis_mul_heis]
  have hrel := fun t : ι => GlobalTheory.T.heisenberg_coords_formula F E σ hσ B W r s hW W₁ H' i₀ i₁ hA (γ t * t.1) (a₂ t) (w₂ t) (α₂ t) (hv t)
  let Q : ι → AE F E := fun t => ∑ j, ∑ k, w₂ t j * inclR (F := F) (AF F) (W₁.J j k) * cA σ (w₂ t k)
  obtain ⟨f₀, hf₀⟩ := GlobalTheory.T.bounded_adeles_mod_global_elements F E ι (fun t => 2 * α₂ t + Q t)
  let f : ι → E := fun t => -((2 : E)⁻¹ * (2 : E)⁻¹) * (f₀ t + σ (f₀ t))
  have hff : ∀ t, σ (f t) = f t := fun t => by
    simp only [f, map_mul, map_neg, map_add, hσ, map_inv₀, map_ofNat]; ring
  have hz := fun t : ι => GlobalTheory.T.rational_heisenberg_center_exists F E σ hσ B W r s hW W₁ H' i₀ i₁ hA (f t) (hff t)
  choose γ₂ hγ₂ hγ₂c using hz
  let α₃ : ι → AE F E := fun t => inclR (F := F) (AF F) (f t) + α₂ t
  let g : ι → UA σ W.J := fun t => γ₂ t * (γ t * t.1)
  have hg : ∀ t, crd H' (g t) = Heisenberg₂ (a₂ t) (w₂ t) (α₃ t) := fun t => by
    simp only [g]; rw [hmul, hγ₂c t, hv t, GlobalTheory.T.heis_mul_heis]; simp [α₃]

  have bw : ∀ k, (fun t => w₂ t k) ∈ R := fun k => by
    convert mem _ (he k) using 1
    funext t; simp [w₂, map_neg]; ring
  have ba : ∀ k, (fun t => a₂ t k) ∈ R := fun k => by
    have e1 : (fun t => a₂ t k) = fun t => -∑ j, inclR (F := F) (AF F) (W₁.J k j) * cA σ (w₂ t j) :=
      funext fun t => (hrel t).1 k
    rw [e1]
    exact R.neg_mem (sumB _ _ fun j _ => R.mul_mem (cst _) (cnj _ (bw j)))
  have bQ : Q ∈ R := sumB _ _ fun j _ => sumB _ _ fun k _ => R.mul_mem (R.mul_mem (bw j) (cst _)) (cnj _ (bw k))

  have alg : ∀ (c x q F0 Fs : AE F E), c * 2 = 1 →
      -(c * c) * (F0 + Fs) + x = c * c * ((2 * x + q - F0) + ((2 * x + q) - Fs)) - c * q := by
    intro c x q F0 Fs hc
    linear_combination (-(1 + 2 * c) * x - c * q) * hc
  have hc2 : inclR (F := F) (AF F) (2⁻¹ : E) * 2 = 1 := by
    rw [← map_ofNat (inclR (F := F) (AF F)) 2, ← map_mul, inv_mul_cancel₀ two_ne_zero, map_one]
  have hcA : ∀ x : E, cA σ (inclR (F := F) (AF F) x) = inclR (F := F) (AF F) (σ x) := fun x => rfl
  have bα : α₃ ∈ R := by
    have hb := mem _ hf₀
    have e1 : α₃ = fun t => inclR (F := F) (AF F) (2⁻¹ : E) * inclR (F := F) (AF F) (2⁻¹ : E) *
        ((2 * α₂ t + Q t - inclR (F := F) (AF F) (f₀ t)) + cA σ (2 * α₂ t + Q t - inclR (F := F) (AF F) (f₀ t))) -
        inclR (F := F) (AF F) (2⁻¹ : E) * Q t := funext fun t => by
      have hz : cA σ (2 * α₂ t + Q t) = 2 * α₂ t + Q t := (hrel t).2
      rw [map_sub, hz, hcA]
      simp only [α₃, f, map_mul, map_neg, map_add]
      exact alg _ _ _ _ _ hc2
    rw [e1]
    exact R.sub_mem (R.mul_mem (R.mul_mem (cst _) (cst _)) (R.add_mem hb (cnj _ hb))) (R.mul_mem (cst _) bQ)
  let ginvH : ι → Matrix (Ix d₁) (Ix d₁) (AE F E) := fun t => Heisenberg₂ (-a₂ t) (-w₂ t) (-α₃ t + ∑ k, a₂ t k * w₂ t k)
  have hgi : ∀ t, crd H' (g t)⁻¹ = ginvH t := by
    intro t
    have h1 : crd H' (g t) * crd H' (g t)⁻¹ = 1 := by rw [← hmul, mul_inv_cancel, hone]
    have h3 : (-α₃ t + ∑ k, a₂ t k * w₂ t k) + α₃ t + ∑ k, (-a₂ t) k * w₂ t k = 0 := by
      simp only [Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]; ring
    have h2 : ginvH t * crd H' (g t) = 1 := by
      rw [hg t, GlobalTheory.T.heis_mul_heis, neg_add_cancel, neg_add_cancel, h3, heis_zero]
    calc crd H' (g t)⁻¹ = (ginvH t * crd H' (g t)) * crd H' (g t)⁻¹ := by rw [h2, one_mul]
      _ = ginvH t := by rw [mul_assoc, h1, mul_one]
  have hPinv : (incM F (basQ H'))⁻¹ = incM F (basQ H')⁻¹ := by
    refine Matrix.inv_eq_left_inv ?_
    simp only [incM]
    rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ hP, Matrix.map_one _ (map_zero _) (map_one _)]
  have matB : ∀ (x : ι → UA σ W.J) (aa ww : ι → Fin d₁ → AE F E) (αα : ι → AE F E),
      (∀ t, crd H' (x t) = Heisenberg₂ (aa t) (ww t) (αα t)) → (∀ k, (fun t => aa t k) ∈ R) →
      (∀ k, (fun t => ww t k) ∈ R) → αα ∈ R → ∀ i j, (fun t => mat (x t) i j) ∈ R := by
    intro x aa ww αα hx ha hw hα i j
    have e1 : (fun t => mat (x t) i j) = fun t => ∑ k, ∑ l, inclR (F := F) (AF F) (basQ H' i l) *
        Heisenberg₂ (aa t) (ww t) (αα t) (ixE d₁ l) (ixE d₁ k) * inclR (F := F) (AF F) ((basQ H')⁻¹ k j) := funext fun t => by
      rw [hmat, hx t, hPinv]
      simp only [Matrix.mul_apply, Matrix.submatrix_apply, Finset.sum_mul, incM, Matrix.map_apply]
    rw [e1]
    exact sumB _ _ fun k _ => sumB _ _ fun l _ =>
      R.mul_mem (R.mul_mem (cst _) (heisB aa ww αα ha hw hα _ _)) (cst _)
  have bαi : (fun t => -α₃ t + ∑ k, a₂ t k * w₂ t k) ∈ R :=
    R.add_mem (R.neg_mem bα) (sumB _ _ fun k _ => R.mul_mem (ba k) (bw k))
  have toB : ∀ f, f ∈ R → f ∈ Bdd F E ι := fun f hf => by rw [← hR]; exact hf
  obtain ⟨K, hK⟩ := GlobalTheory.T.height_bounded_of_bounded_entries F E (d₁ + 2) ι (fun t => (g t).1)
    (fun i j => toB _ (matB g a₂ w₂ α₃ hg ba bw bα i j))
    (fun i j => toB _ (matB (fun t => (g t)⁻¹) (fun t => -a₂ t) (fun t => -w₂ t)
      (fun t => -α₃ t + ∑ k, a₂ t k * w₂ t k) hgi (fun k => R.neg_mem (ba k)) (fun k => R.neg_mem (bw k)) bαi i j))
  refine ⟨K, fun u hu => ⟨γ₂ ⟨u, hu⟩ * γ ⟨u, hu⟩, mul_mem (hγ₂ _) (hγ _), ?_⟩⟩
  have := hK ⟨u, hu⟩
  simpa [g, mul_assoc] using this

end GlobalTheory.QhtUnip

end
