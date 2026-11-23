import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.ContinuousRepresentations.DerivExistsAllPosStatement
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.OneParam

noncomputable section

open Matrix Topology

namespace ReciprocityTheory.ChartRestriction.DS.HW

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

def blkP (ε : Fin n → Bool) (s : Bool) : ℕ := Fintype.card {a // ε a = s}

def blkE (ε : Fin n → Bool) (s : Bool) : Fin (blkP ε s) ≃ {a // ε a = s} :=
  (Fintype.equivFin _).symm

def blkSig (ε : Fin n → Bool) : (Σ s : Bool, Fin (blkP ε s)) ≃ Fin n :=
  (Equiv.sigmaCongrRight (blkE ε)).trans (Equiv.sigmaFiberEquiv ε)

lemma blkSig_apply (ε : Fin n → Bool) (s : Bool) (i : Fin (blkP ε s)) :
    blkSig ε ⟨s, i⟩ = (blkE ε s i : Fin n) := rfl

lemma ε_blkSig (ε : Fin n → Bool) (s : Bool) (i : Fin (blkP ε s)) : ε (blkSig ε ⟨s, i⟩) = s :=
  (blkE ε s i).2

def blkRes (ε : Fin n → Bool) (s : Bool) :
    Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin (blkP ε s)) (Fin (blkP ε s)) ℂ where
  toFun X := Matrix.of fun i j => X (blkSig ε ⟨s, i⟩) (blkSig ε ⟨s, j⟩)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma blkRes_apply (ε : Fin n → Bool) (s : Bool) (X : Matrix (Fin n) (Fin n) ℂ)
    (i j : Fin (blkP ε s)) : blkRes ε s X i j = X (blkSig ε ⟨s, i⟩) (blkSig ε ⟨s, j⟩) := rfl

def blkDiag (ε : Fin n → Bool) :
    (∀ s : Bool, Matrix (Fin (blkP ε s)) (Fin (blkP ε s)) ℂ) →+* Matrix (Fin n) (Fin n) ℂ :=
  (Matrix.reindexAlgEquiv ℂ ℂ (blkSig ε)).toRingEquiv.toRingHom.comp
    (Matrix.blockDiagonal'RingHom (fun s => Fin (blkP ε s)) ℂ)

lemma blkDiag_apply (ε : Fin n → Bool) (v : ∀ s : Bool, Matrix (Fin (blkP ε s)) (Fin (blkP ε s)) ℂ)
    (x y : Σ s : Bool, Fin (blkP ε s)) :
    blkDiag ε v (blkSig ε x) (blkSig ε y) = blockDiagonal' v x y := by
  simp [blkDiag, Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply]

lemma continuous_blkDiag (ε : Fin n → Bool) : Continuous (blkDiag ε) := by
  let L : (∀ s : Bool, Matrix (Fin (blkP ε s)) (Fin (blkP ε s)) ℂ) →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ :=
    { toFun := blkDiag ε
      map_add' := map_add _
      map_smul' := fun c v => by
        ext i j
        obtain ⟨x, rfl⟩ := (blkSig ε).surjective i
        obtain ⟨y, rfl⟩ := (blkSig ε).surjective j
        rcases x with ⟨s, a⟩
        rcases y with ⟨t, b⟩
        simp only [RingHom.id_apply, Matrix.smul_apply, blkDiag_apply]
        by_cases hst : s = t
        · subst hst
          simp [Matrix.blockDiagonal'_apply_eq]
        · simp [Matrix.blockDiagonal'_apply_ne _ _ _ hst] }
  exact L.continuous_of_finiteDimensional

lemma commJ_iff (ε : Fin n → Bool) (M : Matrix (Fin n) (Fin n) ℂ) :
    M * Jm ε = Jm ε * M ↔ ∀ a b, ε a ≠ ε b → M a b = 0 := by
  constructor
  · intro h a b hab
    have h1 := congrFun (congrFun h a) b
    rw [Jm, Matrix.mul_diagonal, Matrix.diagonal_mul] at h1
    cases ha : ε a <;> cases hb : ε b <;> simp [ha, hb] at hab h1 ⊢ <;>
      first | exact h1 | linear_combination h1 / 2 | linear_combination -h1 / 2
  · intro h
    ext a b
    rw [Jm, Matrix.mul_diagonal, Matrix.diagonal_mul]
    by_cases hab : ε a = ε b
    · rw [hab, mul_comm]
    · rw [h a b hab, zero_mul, mul_zero]

lemma blkDiag_commJ (ε : Fin n → Bool)
    (v : ∀ s : Bool, Matrix (Fin (blkP ε s)) (Fin (blkP ε s)) ℂ) :
    blkDiag ε v * Jm ε = Jm ε * blkDiag ε v := by
  refine (commJ_iff ε _).mpr fun a b hab => ?_
  obtain ⟨⟨s, i⟩, rfl⟩ := (blkSig ε).surjective a
  obtain ⟨⟨t, j⟩, rfl⟩ := (blkSig ε).surjective b
  rw [ε_blkSig ε s i, ε_blkSig ε t j] at hab
  rw [blkDiag_apply, Matrix.blockDiagonal'_apply_ne _ _ _ hab]

lemma eq_blkDiag {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ} (hX : X * Jm ε = Jm ε * X) :
    X = blkDiag ε (fun s => blkRes ε s X) := by
  ext a b
  obtain ⟨⟨s, i⟩, rfl⟩ := (blkSig ε).surjective a
  obtain ⟨⟨t, j⟩, rfl⟩ := (blkSig ε).surjective b
  rw [blkDiag_apply]
  by_cases hst : s = t
  · subst hst
    rw [Matrix.blockDiagonal'_apply_eq, blkRes_apply]
  · rw [Matrix.blockDiagonal'_apply_ne _ _ _ hst]
    refine (commJ_iff ε X).mp hX _ _ ?_
    rw [ε_blkSig ε s i, ε_blkSig ε t j]
    exact hst

lemma blkDiag_conjTranspose (ε : Fin n → Bool)
    (v : ∀ s : Bool, Matrix (Fin (blkP ε s)) (Fin (blkP ε s)) ℂ) :
    (blkDiag ε v)ᴴ = blkDiag ε (fun s => (v s)ᴴ) := by
  simp [blkDiag, Matrix.reindexAlgEquiv_apply, Matrix.conjTranspose_reindex,
    Matrix.blockDiagonal'_conjTranspose]

lemma blkDiag_Kset (ε : Fin n → Bool) (v : ∀ s : Bool, Matrix (Fin (blkP ε s)) (Fin (blkP ε s)) ℂ)
    (hv : ∀ s, v s * (v s)ᴴ = 1) : blkDiag ε v ∈ Kset ε := by
  refine ⟨?_, blkDiag_commJ ε v⟩
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, blkDiag_conjTranspose, ← map_mul]
  have : (v * fun s => (v s)ᴴ) = 1 := by
    funext s
    exact hv s
  rw [this, map_one]

def embM (ε : Fin n → Bool) (s : Bool) (A : Matrix (Fin (blkP ε s)) (Fin (blkP ε s)) ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  blkDiag ε (Pi.mulSingle (M := fun s => Matrix (Fin (blkP ε s)) (Fin (blkP ε s)) ℂ) s A)

lemma Jm_allPos (k : ℕ) : Jm (fun _ : Fin k => true) = 1 := by
  simp [Jm]

lemma embM_Kset (ε : Fin n → Bool) (s : Bool) {A : Matrix (Fin (blkP ε s)) (Fin (blkP ε s)) ℂ}
    (hA : A ∈ Kset (fun _ : Fin (blkP ε s) => true)) : embM ε s A ∈ Kset ε := by
  refine blkDiag_Kset ε _ fun t => ?_
  by_cases hts : t = s
  · subst hts
    rw [Pi.mulSingle_eq_same]
    have := hA.1
    rwa [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose] at this
  · rw [Pi.mulSingle_eq_of_ne hts]
    simp

def blkK (ε : Fin n → Bool) {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Kset ε) : KG ε :=
  ⟨⟨⟨g, star g, Unitary.mul_star_self_of_mem hg.1, Unitary.star_mul_self_of_mem hg.1⟩, by
      show gᴴ * Jm ε * g = Jm ε
      have h1 : gᴴ * g = 1 := by
        rw [← Matrix.star_eq_conjTranspose]; exact Unitary.star_mul_self_of_mem hg.1
      rw [Matrix.mul_assoc, ← hg.2, ← Matrix.mul_assoc, h1, Matrix.one_mul]⟩, hg⟩

lemma toMK_blkK (ε : Fin n → Bool) {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Kset ε) :
    toMK (blkK ε hg) = g := rfl

def blkEmbed (ε : Fin n → Bool) (s : Bool) : KG (fun _ : Fin (blkP ε s) => true) →* KG ε where
  toFun h := blkK ε (embM_Kset ε s h.2)
  map_one' := by
    apply onep_KG_ext
    show embM ε s 1 = 1
    rw [embM, Pi.mulSingle_one, map_one]
  map_mul' h h' := by
    apply onep_KG_ext
    show embM ε s (toMK h * toMK h') = embM ε s (toMK h) * embM ε s (toMK h')
    rw [embM, embM, embM, ← map_mul, Pi.mulSingle_mul]

lemma toMK_blkEmbed (ε : Fin n → Bool) (s : Bool) (h : KG (fun _ : Fin (blkP ε s) => true)) :
    toMK (blkEmbed ε s h) = embM ε s (toMK h) := rfl

lemma continuous_blkEmbed (ε : Fin n → Bool) (s : Bool) : Continuous (blkEmbed ε s) := by
  have hmk : Continuous (fun h : KG (fun _ : Fin (blkP ε s) => true) => toMK h) :=
    Units.continuous_val.comp (continuous_subtype_val.comp continuous_subtype_val)
  have hemb : Continuous fun h : KG (fun _ : Fin (blkP ε s) => true) => embM ε s (toMK h) :=
    (continuous_blkDiag ε).comp ((continuous_mulSingle s).comp hmk)
  refine Continuous.subtype_mk (Continuous.subtype_mk ?_ _) _
  exact Units.continuous_iff.mpr ⟨hemb, hemb.matrix_conjTranspose⟩

lemma inK_blkRes {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ} (hX : inK ε X) (s : Bool) :
    inK (fun _ : Fin (blkP ε s) => true) (blkRes ε s X) := by
  refine ⟨?_, by rw [Jm_allPos, Matrix.mul_one, Matrix.one_mul]⟩
  show (blkRes ε s X)ᴴ * Jm (fun _ : Fin (blkP ε s) => true) +
    Jm (fun _ : Fin (blkP ε s) => true) * blkRes ε s X = 0
  rw [Jm_allPos, Matrix.mul_one, Matrix.one_mul]
  ext i j
  have h := congrFun (congrFun hX.1 (blkSig ε ⟨s, i⟩)) (blkSig ε ⟨s, j⟩)
  rw [Jm, Matrix.add_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, ε_blkSig ε s i,
    ε_blkSig ε s j] at h
  simp only [Matrix.add_apply, Matrix.conjTranspose_apply, blkRes_apply, Matrix.zero_apply] at h ⊢
  cases s <;> simp at h ⊢ <;> first | linear_combination h | linear_combination -h

lemma exp_blkDiag (ε : Fin n → Bool) (v : ∀ s : Bool, Matrix (Fin (blkP ε s)) (Fin (blkP ε s)) ℂ) :
    NormedSpace.exp (blkDiag ε v) = blkDiag ε (fun s => NormedSpace.exp (v s)) := by
  letI : ∀ s : Bool, NormedRing (Matrix (Fin (blkP ε s)) (Fin (blkP ε s)) ℂ) :=
    fun _ => Matrix.linftyOpNormedRing
  letI : ∀ s : Bool, NormedAlgebra ℚ (Matrix (Fin (blkP ε s)) (Fin (blkP ε s)) ℂ) :=
    fun _ => Matrix.linftyOpNormedAlgebra
  letI : ∀ s : Bool, NormedAlgebra ℂ (Matrix (Fin (blkP ε s)) (Fin (blkP ε s)) ℂ) :=
    fun _ => Matrix.linftyOpNormedAlgebra
  haveI : ∀ s : Bool, CompleteSpace (Matrix (Fin (blkP ε s)) (Fin (blkP ε s)) ℂ) :=
    fun _ => FiniteDimensional.complete ℂ _
  letI : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℚ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra
  have h := NormedSpace.map_exp (blkDiag ε) (continuous_blkDiag ε) v
  exact h.symm.trans (congrArg _ (Pi.exp_def v))

theorem exp_blk {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ} (hX : X * Jm ε = Jm ε * X) :
    NormedSpace.exp X = embM ε true (NormedSpace.exp (blkRes ε true X)) *
      embM ε false (NormedSpace.exp (blkRes ε false X)) := by
  conv_lhs => rw [eq_blkDiag hX, exp_blkDiag]
  rw [embM, embM, ← map_mul]
  congr 1
  funext t
  cases t <;> simp [Pi.mulSingle_apply]

theorem blk_curve {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ} (hX : inK ε X)
    (γ : ℝ → KG ε) (hγ : ∀ t : ℝ, toMK (γ t) = NormedSpace.exp ((t : ℂ) • X))
    (γp : ℝ → KG (fun _ : Fin (blkP ε true) => true))
    (hp : ∀ t : ℝ, toMK (γp t) = NormedSpace.exp ((t : ℂ) • blkRes ε true X))
    (γm : ℝ → KG (fun _ : Fin (blkP ε false) => true))
    (hm : ∀ t : ℝ, toMK (γm t) = NormedSpace.exp ((t : ℂ) • blkRes ε false X)) (t : ℝ) :
    γ t = blkEmbed ε true (γp t) * blkEmbed ε false (γm t) := by
  apply onep_KG_ext
  have hX' : ((t : ℂ) • X) * Jm ε = Jm ε * ((t : ℂ) • X) := by
    rw [Matrix.smul_mul, hX.2, Matrix.mul_smul]
  show toMK (γ t) = toMK (blkEmbed ε true (γp t)) * toMK (blkEmbed ε false (γm t))
  rw [toMK_blkEmbed, toMK_blkEmbed, hγ, hp, hm, exp_blk hX', map_smul, map_smul]

def BlockExpCurve : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (X : Matrix (Fin n) (Fin n) ℂ), inK ε X →
    ∀ (γ : ℝ → KG ε), (∀ t : ℝ, toMK (γ t) = NormedSpace.exp ((t : ℂ) • X)) →
    ∀ (γp : ℝ → KG (fun _ : Fin (blkP ε true) => true)),
      (∀ t : ℝ, toMK (γp t) = NormedSpace.exp ((t : ℂ) • blkRes ε true X)) →
    ∀ (γm : ℝ → KG (fun _ : Fin (blkP ε false) => true)),
      (∀ t : ℝ, toMK (γm t) = NormedSpace.exp ((t : ℂ) • blkRes ε false X)) →
    ∀ t : ℝ, γ t = blkEmbed ε true (γp t) * blkEmbed ε false (γm t)

theorem blkCurve : BlockExpCurve :=
  fun _ _ _ hX γ hγ γp hp γm hm t => blk_curve hX γ hγ γp hp γm hm t

end ReciprocityTheory.ChartRestriction.DS.HW
