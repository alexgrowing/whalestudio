import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DefsRep
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IsClosedEmbeddingToM

noncomputable section

open Matrix Topology MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS.S7

open ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

def hs (g : Matrix (Fin n) (Fin n) ℂ) : ℝ := ∑ i, ∑ j, ‖g i j‖ ^ 2

lemma Jm_mul_self (ε : Fin n → Bool) : Jm ε * Jm ε = 1 := by
  unfold Jm
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext a
  split_ifs <;> norm_num

lemma Jm_conjTranspose (ε : Fin n → Bool) : (Jm ε)ᴴ = Jm ε := by
  unfold Jm
  rw [Matrix.diagonal_conjTranspose]
  congr 1
  funext a
  by_cases h : ε a = true <;> simp [h]

def UJ (ε : Fin n → Bool) : Subgroup (Matrix (Fin n) (Fin n) ℂ)ˣ where
  carrier := {g | inUJ ε (g : Matrix (Fin n) (Fin n) ℂ)}
  mul_mem' := by
    intro g h hg hh
    simp only [Set.mem_ofPred_eq, inUJ, Units.val_mul, Matrix.conjTranspose_mul] at *
    calc (h : Matrix (Fin n) (Fin n) ℂ)ᴴ * (g : Matrix (Fin n) (Fin n) ℂ)ᴴ * Jm ε *
          ((g : Matrix (Fin n) (Fin n) ℂ) * h)
        = (h : Matrix (Fin n) (Fin n) ℂ)ᴴ * ((g : Matrix (Fin n) (Fin n) ℂ)ᴴ * Jm ε * g) * h := by
          simp only [Matrix.mul_assoc]
      _ = Jm ε := by rw [hg, hh]
  one_mem' := by
    simp only [Set.mem_ofPred_eq, inUJ, Units.val_one, Matrix.conjTranspose_one, Matrix.one_mul,
      Matrix.mul_one]
  inv_mem' := by
    intro g hg
    simp only [Set.mem_ofPred_eq, inUJ] at *
    have h1 : ((g⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)ᴴ *
        (g : Matrix (Fin n) (Fin n) ℂ)ᴴ = 1 := by
      rw [← Matrix.conjTranspose_mul, Units.mul_inv, Matrix.conjTranspose_one]
    have h2 : (g : Matrix (Fin n) (Fin n) ℂ) * ((g⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) :
        Matrix (Fin n) (Fin n) ℂ) = 1 := Units.mul_inv g
    calc ((g⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)ᴴ * Jm ε *
          ((g⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)
        = ((g⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)ᴴ *
          ((g : Matrix (Fin n) (Fin n) ℂ)ᴴ * Jm ε * g) *
          ((g⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) := by rw [hg]
      _ = Jm ε := by
          rw [show ∀ A B C D E : Matrix (Fin n) (Fin n) ℂ, A * (B * C * D) * E = (A * B) * C * (D * E)
            from fun A B C D E => by simp only [Matrix.mul_assoc], h1, h2, Matrix.one_mul, Matrix.mul_one]

abbrev toM {ε : Fin n → Bool} (g : UJ ε) : Matrix (Fin n) (Fin n) ℂ :=
  ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)

lemma left_inv_of_inUJ (ε : Fin n → Bool) (g : Matrix (Fin n) (Fin n) ℂ) (hg : inUJ ε g) :
    (Jm ε * gᴴ * Jm ε) * g = 1 := by
  unfold inUJ at hg
  calc (Jm ε * gᴴ * Jm ε) * g = Jm ε * (gᴴ * Jm ε * g) := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hg, Jm_mul_self]

lemma toM_inv (ε : Fin n → Bool) (g : UJ ε) : toM g⁻¹ = Jm ε * (toM g)ᴴ * Jm ε :=
  Units.inv_eq_of_mul_eq_one_left (left_inv_of_inUJ ε _ g.2)

lemma continuous_toM (ε : Fin n → Bool) : Continuous (fun g : UJ ε => toM g) :=
  Units.continuous_val.comp continuous_subtype_val

lemma isClosed_inUJ (ε : Fin n → Bool) : IsClosed {g : Matrix (Fin n) (Fin n) ℂ | inUJ ε g} := by
  unfold inUJ
  exact isClosed_eq ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul
    continuous_id) continuous_const

lemma range_toM (ε : Fin n → Bool) : Set.range (fun g : UJ ε => toM g) = {g | inUJ ε g} := by
  ext g
  constructor
  · rintro ⟨u, rfl⟩
    exact u.2
  · intro hg
    have h2 := left_inv_of_inUJ ε g hg
    have h1 : g * (Jm ε * gᴴ * Jm ε) = 1 := mul_eq_one_comm.mp h2
    exact ⟨⟨⟨g, Jm ε * gᴴ * Jm ε, h1, h2⟩, hg⟩, rfl⟩

lemma isClosedEmbedding_toM (ε : Fin n → Bool) : IsClosedEmbedding (fun g : UJ ε => toM g) := by
  first | exact UpperTheory.Reformulated.B.Qk16.isClosedEmbedding_toM .. | (apply UpperTheory.Reformulated.B.Qk16.isClosedEmbedding_toM <;> assumption) | (intros; apply UpperTheory.Reformulated.B.Qk16.isClosedEmbedding_toM <;> assumption) | (apply @UpperTheory.Reformulated.B.Qk16.isClosedEmbedding_toM <;> assumption) | (intros; apply @UpperTheory.Reformulated.B.Qk16.isClosedEmbedding_toM <;> assumption) | (apply @UpperTheory.Reformulated.B.Qk16.isClosedEmbedding_toM <;> first | assumption | infer_instance)

instance (ε : Fin n → Bool) : LocallyCompactSpace (UJ ε) := by
  have : LocallyCompactSpace (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → ℂ))
  exact (isClosedEmbedding_toM ε).locallyCompactSpace

instance (ε : Fin n → Bool) : SecondCountableTopology (UJ ε) := by
  have : SecondCountableTopology (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → ℂ))
  exact (isClosedEmbedding_toM ε).isInducing.secondCountableTopology

instance (ε : Fin n → Bool) : MeasurableSpace (UJ ε) := borel _

instance (ε : Fin n → Bool) : BorelSpace (UJ ε) := ⟨rfl⟩

lemma haar_isHaar (ε : Fin n → Bool) : (Measure.haar : Measure (UJ ε)).IsHaarMeasure := inferInstance

lemma Kset_mul (ε : Fin n → Bool) {g h : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Kset ε)
    (hh : h ∈ Kset ε) : g * h ∈ Kset ε := by
  refine ⟨Submonoid.mul_mem _ hg.1 hh.1, ?_⟩
  rw [Matrix.mul_assoc, hh.2, ← Matrix.mul_assoc, hg.2, Matrix.mul_assoc]

lemma Kset_star (ε : Fin n → Bool) {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Kset ε) :
    star g ∈ Kset ε := by
  refine ⟨Unitary.star_mem hg.1, ?_⟩
  have h := congrArg star hg.2
  simp only [star_mul, Matrix.star_eq_conjTranspose, Jm_conjTranspose] at h
  simpa [Matrix.star_eq_conjTranspose] using h.symm

def KG (ε : Fin n → Bool) : Subgroup (UJ ε) where
  carrier := {g | toM g ∈ Kset ε}
  mul_mem' := by
    intro g h hg hh
    show toM g * toM h ∈ Kset ε
    exact Kset_mul ε hg hh
  one_mem' := by
    show (1 : Matrix (Fin n) (Fin n) ℂ) ∈ Kset ε
    refine ⟨Submonoid.one_mem _, ?_⟩
    rw [Matrix.one_mul, Matrix.mul_one]
  inv_mem' := by
    intro g hg
    have h2 : toM g⁻¹ = star (toM g) :=
      Units.inv_eq_of_mul_eq_one_right (Unitary.mul_star_self_of_mem hg.1)
    show toM g⁻¹ ∈ Kset ε
    rw [h2]
    exact Kset_star ε hg

abbrev toMK {ε : Fin n → Bool} (k : KG ε) : Matrix (Fin n) (Fin n) ℂ := toM (k : UJ ε)

end ReciprocityTheory.ChartRestriction.DS.S7
