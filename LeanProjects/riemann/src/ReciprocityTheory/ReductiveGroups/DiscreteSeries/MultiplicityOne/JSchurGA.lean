import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.StDefs
import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeCSchur

noncomputable section

open MeasureTheory Matrix Topology
open scoped ENNReal NNReal InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Mult1

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B

section

def epsG (k r : ℕ) : Fin (2 * r + k + 1) → Bool := fun i => decide (i.val < r + k)

def sq2 : ℂ := ((Real.sqrt 2 : ℝ) : ℂ)⁻¹

theorem sq2_mul_sq2_eq_half : sq2 * sq2 = 1 / 2 := by
  first
    | (unfold sq2
       rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2)]
       norm_num)
    | (unfold sq2; rw [← mul_inv]; norm_cast; rw [Real.mul_self_sqrt (by norm_num)]; norm_num)

theorem star_sq2_eq_self : star sq2 = sq2 := by
  first
    | simp [sq2]
    | (unfold sq2; rw [star_inv₀, Complex.star_def, Complex.conj_ofReal])

def dG (k r : ℕ) (i : Fin (2 * r + k + 1)) : ℂ :=
  if i.val < r then sq2 else if i.val ≤ r + k then 1 else -sq2

def cG (k r : ℕ) (i : Fin (2 * r + k + 1)) : ℂ :=
  if i.val < r ∨ r + k < i.val then sq2 else 0

def PG (k r : ℕ) : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ := fun i j =>
  (if i = j then dG k r i else 0) + (if j = Fin.rev i then cG k r i else 0)

theorem PG_mul_apply (k r : ℕ) (M : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (i j) :
    (PG k r * M) i j = dG k r i * M i j + cG k r i * M (Fin.rev i) j := by
  first
    | simp only [Matrix.mul_apply, PG, add_mul, Finset.sum_add_distrib, ite_mul, zero_mul,
        Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    | simp [Matrix.mul_apply, PG, add_mul, Finset.sum_add_distrib]

theorem val_rev_eq_sub (k r : ℕ) (i : Fin (2 * r + k + 1)) : (Fin.rev i).val = 2 * r + k - i.val := by
  have := i.isLt
  rw [Fin.val_rev]
  omega

theorem PG_mul_PG (k r : ℕ) : PG k r * PG k r = 1 := by
  ext i j
  rw [PG_mul_apply]
  have h2 := sq2_mul_sq2_eq_half
  have hi := i.isLt
  have hj := j.isLt
  simp only [PG, dG, cG, Matrix.one_apply, Fin.rev_rev, Fin.ext_iff, val_rev_eq_sub]
  split_ifs <;> first | omega | ring1 | linear_combination (2:ℂ) * h2 | linear_combination (-2:ℂ) * h2 | linear_combination h2 | linear_combination (-1:ℂ) * h2

theorem PG_conjTranspose (k r : ℕ) : (PG k r)ᴴ = PG k r := by
  ext i j
  have hi := i.isLt
  have hj := j.isLt
  simp only [Matrix.conjTranspose_apply, PG, dG, cG, Fin.ext_iff, val_rev_eq_sub]
  split_ifs <;> first | omega | simp [star_sq2_eq_self]

def eG (k r : ℕ) (i : Fin (2 * r + k + 1)) : ℂ := if i.val < r + k then 1 else -1

theorem Jm_epsG (k r : ℕ) : Formalism.REAL.Jm (epsG k r) = Matrix.diagonal (eG k r) := by
  unfold Formalism.REAL.Jm
  congr 1
  funext a
  simp [epsG, eG]

theorem cG_rev (k r : ℕ) (i : Fin (2 * r + k + 1)) : cG k r (Fin.rev i) = cG k r i := by
  have := i.isLt
  simp only [cG, val_rev_eq_sub]
  split_ifs <;> first | rfl | omega

theorem PJP_apply (k r : ℕ) (i j : Fin (2 * r + k + 1)) :
    (PG k r * Matrix.diagonal (eG k r) * PG k r) i j =
      (if i = j then dG k r i * dG k r i * eG k r i + cG k r i * cG k r i * eG k r (Fin.rev i) else 0) +
      (if j = Fin.rev i then cG k r i * (dG k r i * eG k r i + eG k r (Fin.rev i) * dG k r (Fin.rev i)) else 0) := by
  rw [Matrix.mul_assoc, PG_mul_apply]
  have hi := i.isLt
  have hj := j.isLt
  simp only [Matrix.diagonal_mul, PG, Fin.rev_rev, cG_rev, Fin.ext_iff, val_rev_eq_sub]
  split_ifs <;> first | omega | ring1

theorem PG_J_PG (k r : ℕ) : PG k r * Formalism.REAL.Jm (epsG k r) * PG k r = Formalism.QuantumDeterminants.Hpk k r := by
  rw [Jm_epsG]
  ext i j
  rw [PJP_apply]
  have h2 := sq2_mul_sq2_eq_half
  have hi := i.isLt
  have hj := j.isLt
  have hr := val_rev_eq_sub k r i
  simp only [Formalism.QuantumDeterminants.Hpk, Fin.ext_iff, hr]
  rcases lt_or_ge i.val r with h1 | h1
  · have : dG k r i = sq2 := by
      simp only [dG, cG, eG]
      split_ifs <;> first | rfl | omega
    rw [this]
    have : cG k r i = sq2 := by
      simp only [dG, cG, eG]
      split_ifs <;> first | rfl | omega
    rw [this]
    have : eG k r i = 1 := by
      simp only [dG, cG, eG]
      split_ifs <;> first | rfl | omega
    rw [this]
    have : dG k r (Fin.rev i) = -sq2 := by
      simp only [dG, cG, eG, hr]
      split_ifs <;> first | rfl | omega
    rw [this]
    have : eG k r (Fin.rev i) = -1 := by
      simp only [dG, cG, eG, hr]
      split_ifs <;> first | rfl | omega
    rw [this]
    split_ifs <;> first | omega | ring1 | linear_combination (2:ℂ) * h2 | linear_combination (-2:ℂ) * h2 | linear_combination h2 | linear_combination (-1:ℂ) * h2
  rcases lt_or_ge i.val (r + k) with h3 | h3
  · have : dG k r i = 1 := by
      simp only [dG, cG, eG]
      split_ifs <;> first | rfl | omega
    rw [this]
    have : cG k r i = 0 := by
      simp only [dG, cG, eG]
      split_ifs <;> first | rfl | omega
    rw [this]
    have : eG k r i = 1 := by
      simp only [dG, cG, eG]
      split_ifs <;> first | rfl | omega
    rw [this]
    split_ifs <;> first | omega | ring1 | linear_combination (2:ℂ) * h2 | linear_combination (-2:ℂ) * h2 | linear_combination h2 | linear_combination (-1:ℂ) * h2
  rcases eq_or_lt_of_le h3 with h4 | h4
  · have : dG k r i = 1 := by
      simp only [dG, cG, eG]
      split_ifs <;> first | rfl | omega
    rw [this]
    have : cG k r i = 0 := by
      simp only [dG, cG, eG]
      split_ifs <;> first | rfl | omega
    rw [this]
    have : eG k r i = -1 := by
      simp only [dG, cG, eG]
      split_ifs <;> first | rfl | omega
    rw [this]
    split_ifs <;> first | omega | ring1 | linear_combination (2:ℂ) * h2 | linear_combination (-2:ℂ) * h2 | linear_combination h2 | linear_combination (-1:ℂ) * h2
  · have : dG k r i = -sq2 := by
      simp only [dG, cG, eG]
      split_ifs <;> first | rfl | omega
    rw [this]
    have : cG k r i = sq2 := by
      simp only [dG, cG, eG]
      split_ifs <;> first | rfl | omega
    rw [this]
    have : eG k r i = -1 := by
      simp only [dG, cG, eG]
      split_ifs <;> first | rfl | omega
    rw [this]
    have : dG k r (Fin.rev i) = sq2 := by
      simp only [dG, cG, eG, hr]
      split_ifs <;> first | rfl | omega
    rw [this]
    have : eG k r (Fin.rev i) = 1 := by
      simp only [dG, cG, eG, hr]
      split_ifs <;> first | rfl | omega
    rw [this]
    split_ifs <;> first | omega | ring1 | linear_combination (2:ℂ) * h2 | linear_combination (-2:ℂ) * h2 | linear_combination h2 | linear_combination (-1:ℂ) * h2

end

section
variable {k r : ℕ}

private theorem PG_mul_PG_conj_mul_PG_eq (k r : ℕ) (X : Mat k r) :
    PG k r * (PG k r * X * PG k r) * PG k r = X := by
  simp only [← Matrix.mul_assoc, PG_mul_PG, Matrix.one_mul]
  rw [Matrix.mul_assoc, PG_mul_PG, Matrix.mul_one]

theorem mem_GV_iff_PG (g : Mat k r) :
    g ∈ GV k r ↔ Formalism.REAL.inUJ (epsG k r) (PG k r * g * PG k r) := by
  have hH := PG_conjTranspose k r
  have hJ := PG_J_PG k r
  have hJ' : PG k r * Formalism.QuantumDeterminants.Hpk k r * PG k r = Formalism.REAL.Jm (epsG k r) := by
    rw [← hJ]
    simp only [← Matrix.mul_assoc, PG_mul_PG, Matrix.one_mul]
    rw [Matrix.mul_assoc, PG_mul_PG, Matrix.mul_one]
  have key : (PG k r * g * PG k r)ᴴ * Formalism.REAL.Jm (epsG k r) * (PG k r * g * PG k r)
      = PG k r * (gᴴ * Formalism.QuantumDeterminants.Hpk k r * g) * PG k r := by
    rw [← hJ]
    simp only [Matrix.conjTranspose_mul, hH, Matrix.mul_assoc]
  show gᴴ * Formalism.QuantumDeterminants.Hpk k r * g = Formalism.QuantumDeterminants.Hpk k r ↔
    (PG k r * g * PG k r)ᴴ * Formalism.REAL.Jm (epsG k r) * (PG k r * g * PG k r) = Formalism.REAL.Jm (epsG k r)
  rw [key]
  constructor
  · intro h
    rw [h, hJ']
  · intro h
    rw [← PG_mul_PG_conj_mul_PG_eq k r (gᴴ * Formalism.QuantumDeterminants.Hpk k r * g), h, hJ]

def conjPG (k r : ℕ) : Mat k r ≃ₜ Mat k r where
  toFun M := PG k r * M * PG k r
  invFun M := PG k r * M * PG k r
  left_inv M := by
    simp only [← Matrix.mul_assoc, PG_mul_PG, Matrix.one_mul]; rw [Matrix.mul_assoc, PG_mul_PG, Matrix.mul_one]
  right_inv M := by
    simp only [← Matrix.mul_assoc, PG_mul_PG, Matrix.one_mul]; rw [Matrix.mul_assoc, PG_mul_PG, Matrix.mul_one]
  continuous_toFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  continuous_invFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const

def psiM (k r : ℕ) (u : Formalism.REAL.UJ (epsG k r)) : Mat k r :=
  conjPG k r (Formalism.MainNotions.S.umat u)

def psiG (k r : ℕ) (u : Formalism.REAL.UJ (epsG k r)) : Mt k r := Matrix.of.symm (psiM k r u)

theorem of_psiG (u : Formalism.REAL.UJ (epsG k r)) : Matrix.of (psiG k r u) = psiM k r u := by
  first | exact Matrix.of.apply_symm_apply _ | rfl

theorem psiM_eq (u : Formalism.REAL.UJ (epsG k r)) : psiM k r u = PG k r * Formalism.MainNotions.S.umat u * PG k r := rfl

private theorem real_Jm_mul_self_eq_one {n : ℕ} (ε : Fin n → Bool) : Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1 := by
  simp only [Formalism.REAL.Jm, Matrix.diagonal_mul_diagonal]
  rw [← Matrix.diagonal_one]
  congr 1
  funext a
  split_ifs <;> norm_num

private theorem Jm_mul_conjTranspose_mul_Jm_mul_eq_one_of_mem_UJset {n : ℕ} {ε : Fin n → Bool} {h : Matrix (Fin n) (Fin n) ℂ}
    (hu : Formalism.REAL.inUJ ε h) : Formalism.REAL.Jm ε * hᴴ * Formalism.REAL.Jm ε * h = 1 := by
  have hu' : hᴴ * Formalism.REAL.Jm ε * h = Formalism.REAL.Jm ε := hu
  calc Formalism.REAL.Jm ε * hᴴ * Formalism.REAL.Jm ε * h = Formalism.REAL.Jm ε * (hᴴ * Formalism.REAL.Jm ε * h) := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hu', real_Jm_mul_self_eq_one]

private theorem exists_UJ_umat_eq_of_inUJ {n : ℕ} {ε : Fin n → Bool} (h : Matrix (Fin n) (Fin n) ℂ)
    (hu : Formalism.REAL.inUJ ε h) : ∃ v : Formalism.REAL.UJ ε, Formalism.MainNotions.S.umat v = h := by
  have hl := Jm_mul_conjTranspose_mul_Jm_mul_eq_one_of_mem_UJset hu
  have hr : h * (Formalism.REAL.Jm ε * hᴴ * Formalism.REAL.Jm ε) = 1 := by
    first
      | exact mul_eq_one_comm.mp hl
      | exact Matrix.mul_eq_one_comm.mp hl
      | exact (mul_eq_one_comm_of_equiv (Equiv.refl _)).mp hl
      | exact mul_eq_one_symm hl
      | exact Matrix.mul_eq_one_symm hl
  exact ⟨⟨⟨h, _, hr, hl⟩, hu⟩, rfl⟩

private theorem isClosedEmbedding_umat (k r : ℕ) :
    IsClosedEmbedding (fun u : Formalism.REAL.UJ (epsG k r) => Formalism.MainNotions.S.umat u) := by
  have hG : Continuous (fun m : Mat k r =>
      (m, MulOpposite.op (Formalism.REAL.Jm (epsG k r) * mᴴ * Formalism.REAL.Jm (epsG k r)))) := by
    have h0 : Continuous (fun m : Mat k r =>
        Formalism.REAL.Jm (epsG k r) * mᴴ * Formalism.REAL.Jm (epsG k r)) :=
      (continuous_const.matrix_mul continuous_id.matrix_conjTranspose).matrix_mul continuous_const
    first
      | exact continuous_id.prodMk (MulOpposite.continuous_op.comp h0)
      | exact continuous_id.prod_mk (MulOpposite.continuous_op.comp h0)
  have hc : Continuous (fun u : Formalism.REAL.UJ (epsG k r) => Formalism.MainNotions.S.umat u) :=
    Units.continuous_val.comp continuous_subtype_val
  have he : IsInducing (fun u : Formalism.REAL.UJ (epsG k r) => Units.embedProduct _ (u : (Mat k r)ˣ)) := by
    first
      | exact Units.isInducing_embedProduct.comp IsInducing.subtypeVal
      | exact Units.isInducing_embedProduct.comp Topology.IsInducing.subtypeVal
  have hcomp : (fun u : Formalism.REAL.UJ (epsG k r) => Units.embedProduct _ (u : (Mat k r)ˣ)) =
      (fun m : Mat k r => (m, MulOpposite.op (Formalism.REAL.Jm (epsG k r) * mᴴ * Formalism.REAL.Jm (epsG k r)))) ∘
        (fun u : Formalism.REAL.UJ (epsG k r) => Formalism.MainNotions.S.umat u) := by
    funext u
    refine Prod.ext rfl ?_
    show MulOpposite.op (((u : (Mat k r)ˣ)⁻¹ : (Mat k r)ˣ) : Mat k r) =
      MulOpposite.op (Formalism.REAL.Jm (epsG k r) * (Formalism.MainNotions.S.umat u)ᴴ * Formalism.REAL.Jm (epsG k r))
    rw [Units.inv_eq_of_mul_eq_one_left (Jm_mul_conjTranspose_mul_Jm_mul_eq_one_of_mem_UJset (h := Formalism.MainNotions.S.umat u) u.2)]
  have hind : IsInducing (fun u : Formalism.REAL.UJ (epsG k r) => Formalism.MainNotions.S.umat u) :=
    IsInducing.of_comp hc hG (by rw [← hcomp]; exact he)
  refine ⟨⟨hind, ?_⟩, ?_⟩
  · intro a b hab
    exact Subtype.ext (Units.ext hab)
  · have hr : Set.range (fun u : Formalism.REAL.UJ (epsG k r) => Formalism.MainNotions.S.umat u) =
        {g : Mat k r | gᴴ * Formalism.REAL.Jm (epsG k r) * g = Formalism.REAL.Jm (epsG k r)} := by
      ext g
      constructor
      · rintro ⟨u, rfl⟩
        exact u.2
      · intro hg
        exact exists_UJ_umat_eq_of_inUJ g hg
    rw [hr]
    exact isClosed_eq
      ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul continuous_id)
      continuous_const

theorem isClosedEmbedding_psiM (k r : ℕ) : IsClosedEmbedding (psiM k r) := (conjPG k r).isClosedEmbedding.comp (isClosedEmbedding_umat k r)

theorem isClosedEmbedding_psiG (k r : ℕ) : IsClosedEmbedding (psiG k r) := isClosedEmbedding_psiM k r

theorem range_psiM (k r : ℕ) : Set.range (psiM k r) = GV k r := by
  apply Set.Subset.antisymm
  · rintro _ ⟨u, rfl⟩
    rw [mem_GV_iff_PG, psiM_eq, PG_mul_PG_conj_mul_PG_eq]
    exact u.2
  · intro g hg
    obtain ⟨v, hv⟩ := exists_UJ_umat_eq_of_inUJ (PG k r * g * PG k r) ((mem_GV_iff_PG g).1 hg)
    refine ⟨v, ?_⟩
    rw [psiM_eq, hv, PG_mul_PG_conj_mul_PG_eq]

theorem range_psiG (k r : ℕ) : Set.range (psiG k r) = GV k r := range_psiM k r

theorem psiM_mem (u : Formalism.REAL.UJ (epsG k r)) : psiM k r u ∈ GV k r := by
  rw [← range_psiM k r]
  exact ⟨u, rfl⟩

theorem psiM_one : psiM k r 1 = 1 := by
  rw [psiM_eq]
  first
    | simp [PG_mul_PG]
    | (show PG k r * 1 * PG k r = 1; rw [Matrix.mul_one, PG_mul_PG])

theorem psiM_mul (u v : Formalism.REAL.UJ (epsG k r)) : psiM k r (u * v) = psiM k r u * psiM k r v := by
  have hPP : ∀ X : Mat k r, PG k r * (PG k r * X) = X := fun X => by
    rw [← Matrix.mul_assoc, PG_mul_PG, Matrix.one_mul]
  have hm : Formalism.MainNotions.S.umat (u * v) = Formalism.MainNotions.S.umat u * Formalism.MainNotions.S.umat v := rfl
  rw [psiM_eq, psiM_eq, psiM_eq, hm]
  simp only [Matrix.mul_assoc, hPP]

theorem continuous_psiM (k r : ℕ) : Continuous (psiM k r) := (conjPG k r).continuous.comp (Units.continuous_val.comp continuous_subtype_val)

theorem measurableEmbedding_psiG (k r : ℕ) : MeasurableEmbedding (psiG k r) := (isClosedEmbedding_psiG k r).measurableEmbedding

end

section
variable {k r : ℕ}

def nuG (μ : Measure (Mt k r)) : Measure (Formalism.REAL.UJ (epsG k r)) := μ.comap (psiG k r)

theorem map_nuG {μ : Measure (Mt k r)} (hμ : IsHaarOn (GV k r) μ) : (nuG μ).map (psiG k r) = μ := by
  have he := measurableEmbedding_psiG k r
  unfold nuG
  rw [he.map_comap, range_psiG]
  exact Measure.restrict_eq_self_of_ae_mem (ae_iff.2 hμ.conc)

theorem psiG_mul' (u x : Formalism.REAL.UJ (epsG k r)) : psiG k r (u * x) = lmulM (psiM k r u) (psiG k r x) := by
  rw [lmulM, of_psiG, psiG, psiM_mul]
  try rfl

theorem measurable_lmulM (a : Mat k r) : Measurable (lmulM (k := k) (r := r) a) := by
  apply Continuous.measurable
  unfold lmulM
  exact continuous_const.matrix_mul continuous_id

private theorem nuG_map_eq_of_psiG_comm {μ : Measure (Mt k r)} (hμ : IsHaarOn (GV k r) μ)
    (f : Formalism.REAL.UJ (epsG k r) → Formalism.REAL.UJ (epsG k r)) (hf : Measurable f)
    (F : Mt k r → Mt k r) (hF : Measurable F) (hcomm : ∀ x, psiG k r (f x) = F (psiG k r x))
    (hFμ : μ.map F = μ) : (nuG μ).map f = nuG μ := by
  have he := measurableEmbedding_psiG k r
  have key : ((nuG μ).map f).map (psiG k r) = μ := by
    rw [Measure.map_map he.measurable hf]
    have hc : psiG k r ∘ f = F ∘ psiG k r := funext hcomm
    rw [hc, ← Measure.map_map hF he.measurable, map_nuG hμ, hFμ]
  calc (nuG μ).map f = (((nuG μ).map f).map (psiG k r)).comap (psiG k r) := (he.comap_map _).symm
    _ = nuG μ := by
      rw [key]
      try rfl

theorem nuG_left {μ : Measure (Mt k r)} (hμ : IsHaarOn (GV k r) μ) : (nuG μ).IsMulLeftInvariant := by
  constructor
  intro u
  exact nuG_map_eq_of_psiG_comm hμ _ (continuous_mul_left u).measurable (lmulM (psiM k r u)) (measurable_lmulM _)
    (fun x => psiG_mul' u x) (hμ.left _ (psiM_mem u))

theorem nuG_finite {μ : Measure (Mt k r)} (hμ : IsHaarOn (GV k r) μ) : IsFiniteMeasureOnCompacts (nuG μ) := by
  constructor
  intro K hK
  have he := measurableEmbedding_psiG k r
  unfold nuG
  rw [he.comap_apply]
  exact hμ.finite_compact _ (hK.image (isClosedEmbedding_psiG k r).continuous)

theorem nuG_eq_smul {μ : Measure (Mt k r)} (hμ : IsHaarOn (GV k r) μ) :
    ∃ c : ℝ≥0, c ≠ 0 ∧ nuG μ = c • Formalism.REAL.muG (epsG k r) := by
  haveI := nuG_left hμ
  haveI := nuG_finite hμ
  haveI hHaar : (Formalism.REAL.muG (epsG k r)).IsHaarMeasure := by
    first
      | infer_instance
      | (unfold Formalism.REAL.muG; infer_instance)
  have hE := Measure.isMulLeftInvariant_eq_smul (nuG μ) (Formalism.REAL.muG (epsG k r))
  refine ⟨Measure.haarScalarFactor (nuG μ) (Formalism.REAL.muG (epsG k r)), ?_, hE⟩
  intro h0
  rw [h0, zero_smul] at hE
  apply hμ.ne_zero
  rw [← map_nuG hμ, hE, Measure.map_zero]

private theorem nuG_isOpenPosMeasure {μ : Measure (Mt k r)} (hμ : IsHaarOn (GV k r) μ) :
    (nuG μ).IsOpenPosMeasure := by
  obtain ⟨c, hc, he⟩ := nuG_eq_smul hμ
  haveI hHaar : (Formalism.REAL.muG (epsG k r)).IsHaarMeasure := by
    first
      | infer_instance
      | (unfold Formalism.REAL.muG; infer_instance)
  constructor
  intro U hU hne
  rw [he, Measure.smul_apply]
  have h0 := hU.measure_ne_zero (Formalism.REAL.muG (epsG k r)) hne
  first
    | exact smul_ne_zero hc h0
    | exact mul_ne_zero (ENNReal.coe_ne_zero.2 hc) h0

theorem nuG_inv {μ : Measure (Mt k r)} (hμ : IsHaarOn (GV k r) μ) : (nuG μ).IsInvInvariant := by
  haveI := nuG_left hμ
  haveI := nuG_finite hμ
  haveI := nuG_isOpenPosMeasure hμ
  haveI hH : (nuG μ).IsHaarMeasure :=
    { toIsFiniteMeasureOnCompacts := inferInstance, toIsMulLeftInvariant := inferInstance,
      toIsOpenPosMeasure := inferInstance }
  haveI hR : (nuG μ).IsMulRightInvariant := by
    constructor
    intro u
    refine nuG_map_eq_of_psiG_comm hμ _ (continuous_mul_right u).measurable (Formalism.FourierDecayAlt.B.rmulF (psiM k r u)) ?_
      (fun x => ?_) (hμ.right _ (psiM_mem u))
    · apply Continuous.measurable
      unfold Formalism.FourierDecayAlt.B.rmulF
      exact continuous_id.matrix_mul continuous_const
    · rw [Formalism.FourierDecayAlt.B.rmulF, of_psiG, psiG, psiM_mul]
      try rfl
  haveI hFi : IsFiniteMeasureOnCompacts (nuG μ).inv := by
    first
      | infer_instance
      | exact ⟨fun K hK => by rw [Measure.inv_apply]; exact hK.inv.measure_lt_top⟩
  haveI hLi : (nuG μ).inv.IsMulLeftInvariant := by infer_instance
  obtain ⟨c, hc⟩ : ∃ c : ℝ≥0, (nuG μ).inv = c • nuG μ :=
    ⟨_, Measure.isMulLeftInvariant_eq_smul _ _⟩
  obtain ⟨K, hK, hK1⟩ := exists_compact_mem_nhds (1 : Formalism.REAL.UJ (epsG k r))
  have hSc : IsCompact (K ∪ K⁻¹) := hK.union hK.inv
  have hpos : 0 < nuG μ (K ∪ K⁻¹) := by
    obtain ⟨t, htK, hto, h1t⟩ := mem_nhds_iff.1 hK1
    exact lt_of_lt_of_le (pos_iff_ne_zero.2 (hto.measure_ne_zero (nuG μ) ⟨_, h1t⟩))
      (measure_mono (htK.trans Set.subset_union_left))
  have hfin : nuG μ (K ∪ K⁻¹) ≠ ∞ := hSc.measure_lt_top.ne
  have hSinv : (K ∪ K⁻¹)⁻¹ = K ∪ K⁻¹ := by
    rw [Set.union_inv, inv_inv, Set.union_comm]
  have h2 : nuG μ (K ∪ K⁻¹) = (c : ℝ≥0∞) * nuG μ (K ∪ K⁻¹) := by
    have h1 : (nuG μ).inv (K ∪ K⁻¹) = nuG μ (K ∪ K⁻¹) := by rw [Measure.inv_apply, hSinv]
    rw [hc, Measure.smul_apply] at h1
    first
      | exact h1.symm
      | (rw [ENNReal.smul_def] at h1; exact h1.symm)
      | (simp only [ENNReal.smul_def, smul_eq_mul] at h1; exact h1.symm)
  have hc1 : (c : ℝ≥0∞) = 1 := by
    have h3 : (c : ℝ≥0∞) * nuG μ (K ∪ K⁻¹) = 1 * nuG μ (K ∪ K⁻¹) := by
      rw [one_mul]
      exact h2.symm
    first
      | exact (ENNReal.mul_left_inj hpos.ne' hfin).1 h3
      | exact (ENNReal.mul_right_inj hpos.ne' hfin).1 h3
      | exact ENNReal.mul_right_cancel hpos.ne' hfin h3
      | exact (ENNReal.mul_eq_mul_left hpos.ne' hfin).1 (by rw [mul_comm, h3, mul_comm])
      | exact (ENNReal.mul_left_inj hpos.ne' hfin).1 (by rw [mul_comm, h3, mul_comm])
      | exact (ENNReal.mul_right_inj hpos.ne' hfin).1 (by rw [mul_comm, h3, mul_comm])
  constructor
  rw [hc, ENNReal.coe_eq_one.1 hc1, one_smul]

theorem nuG_openPos {μ : Measure (Mt k r)} (hμ : IsHaarOn (GV k r) μ) : (nuG μ).IsOpenPosMeasure := nuG_isOpenPosMeasure hμ

end

section
variable {k r : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem sqRep_psiG {μ : Measure (Mt k r)} (hμ : IsHaarOn (GV k r) μ) {σ : Mat k r → (H →L[ℂ] H)}
    (hU : Formalism.MainNotions.S.IsURepOn (GV k r) σ)
    (hS : ∀ v w : H, MemLp (fun g : Mt k r => ⟪w, σ (Matrix.of g) v⟫_ℂ) 2 μ) :
    Formalism.MainNotions.BridgeCSchur.SqRep (nuG μ) (fun u => σ (psiM k r u)) where
  one := by rw [psiM_one]; exact hU.1.1
  mul a b := by rw [psiM_mul]; exact hU.1.2 _ (psiM_mem a) _ (psiM_mem b)
  iso g v := hU.2.1 _ (psiM_mem g) v
  cont v := (hU.2.2 v).comp_continuous (continuous_psiM k r) psiM_mem
  sq v w := by
    have h := hS v w
    rw [← map_nuG hμ] at h
    have h' := ((measurableEmbedding_psiG k r).memLp_map_measure_iff).mp h
    convert h' using 1
    funext u
    simp only [Function.comp_apply, of_psiG]

theorem irr_psiG {σ : Mat k r → (H →L[ℂ] H)} (hI : Formalism.MainNotions.S.IsIrredOn (GV k r) σ) :
    ∀ S : Submodule ℂ H, IsClosed (S : Set H) →
      (∀ u : Formalism.REAL.UJ (epsG k r), ∀ v ∈ S, σ (psiM k r u) v ∈ S) → S = ⊥ ∨ S = ⊤ := by
  intro S hS hinv
  apply hI S hS
  intro g hg v hv
  have hg' : g ∈ Set.range (psiM k r) := by
    rw [range_psiM]
    exact hg
  obtain ⟨u, rfl⟩ := hg'
  exact hinv u v hv

theorem schur_GV [CompleteSpace H] [Nontrivial H] {μ : Measure (Mt k r)} (hμ : IsHaarOn (GV k r) μ)
    {σ : Mat k r → (H →L[ℂ] H)} (hU : Formalism.MainNotions.S.IsURepOn (GV k r) σ) (hI : Formalism.MainNotions.S.IsIrredOn (GV k r) σ)
    (hS : ∀ v w : H, MemLp (fun g : Mt k r => ⟪w, σ (Matrix.of g) v⟫_ℂ) 2 μ) :
    ∃ d : ℝ, 0 < d ∧ ∀ v w v' w' : H,
      Integrable (fun g : Mt k r => ⟪w, σ (Matrix.of g) v⟫_ℂ * star ⟪w', σ (Matrix.of g) v'⟫_ℂ) μ ∧
      ∫ g : Mt k r, ⟪w, σ (Matrix.of g) v⟫_ℂ * star ⟪w', σ (Matrix.of g) v'⟫_ℂ ∂μ =
        ⟪v', v⟫_ℂ * ⟪w, w'⟫_ℂ / (d : ℂ) := by
  haveI := nuG_left hμ
  haveI := nuG_inv hμ
  haveI := nuG_openPos hμ
  obtain ⟨d, hd, h⟩ := Formalism.MainNotions.BridgeCSchur.schur_orth (sqRep_psiG hμ hU hS) (irr_psiG hI)
  refine ⟨d, hd, fun v w v' w' => ?_⟩
  obtain ⟨hi, he⟩ := h v w v' w'
  have hE := measurableEmbedding_psiG k r
  rw [← map_nuG hμ]
  constructor
  · first
      | exact hE.integrable_map_iff.2 hi
      | simpa [Function.comp_def, of_psiG] using hE.integrable_map_iff.2 hi
  · rw [hE.integral_map]
    first
      | exact he
      | simpa [of_psiG] using he

end

end ReciprocityTheory.ChartRestriction.DS.Mult1
