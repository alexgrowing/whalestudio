import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.InstBorelGL

open MeasureTheory Matrix GlobalTheory.CompanionTheory.QL
open scoped ComplexConjugate ValuativeRel

namespace GlobalTheory.CompanionTheory.QL.Par

section Alg

variable {F : Type} [Field F]

def piIdeal (O : Subring F) (ϖ : F) : Ideal O where
  carrier := {x | ∃ o ∈ O, (x : F) = ϖ * o}
  add_mem' := by
    rintro a b ⟨x, hx, hax⟩ ⟨y, hy, hby⟩
    exact ⟨x + y, O.add_mem hx hy, by simp [hax, hby, mul_add]⟩
  zero_mem' := ⟨0, O.zero_mem, by simp⟩
  smul_mem' := by
    rintro c a ⟨x, hx, hax⟩
    refine ⟨c * x, O.mul_mem c.2 hx, ?_⟩
    simp only [smul_eq_mul, Subring.coe_mul, hax]
    ring

def liftO {n : ℕ} (O : Subring F) (Z : Matrix (Fin n) (Fin n) F) (h : IsInt O Z) :
    Matrix (Fin n) (Fin n) O := fun i j => ⟨Z i j, h i j⟩

theorem liftO_mul {n : ℕ} (O : Subring F) {x y : Matrix (Fin n) (Fin n) F} (hx : IsInt O x)
    (hy : IsInt O y) (hxy : IsInt O (x * y)) :
    liftO O (x * y) hxy = liftO O x hx * liftO O y hy := by
  ext i j
  simp [liftO, Matrix.mul_apply]

theorem liftO_one {n : ℕ} (O : Subring F) (h : IsInt O (1 : Matrix (Fin n) (Fin n) F)) :
    liftO O 1 h = 1 := by
  ext i j
  by_cases hij : i = j <;> simp [liftO, hij, Matrix.one_apply]

def red {n : ℕ} (O : Subring F) (ϖ : F) (Z : Matrix (Fin n) (Fin n) F) (h : IsInt O Z) :
    Matrix (Fin n) (Fin n) (O ⧸ piIdeal O ϖ) :=
  (liftO O Z h).map (Ideal.Quotient.mk (piIdeal O ϖ))

theorem red_mul {n : ℕ} (O : Subring F) (ϖ : F) {x y : Matrix (Fin n) (Fin n) F} (hx : IsInt O x)
    (hy : IsInt O y) (hxy : IsInt O (x * y)) :
    red O ϖ (x * y) hxy = red O ϖ x hx * red O ϖ y hy := by
  rw [red, liftO_mul O hx hy hxy, Matrix.map_mul]
  rfl

theorem red_one {n : ℕ} (O : Subring F) (ϖ : F) (h : IsInt O (1 : Matrix (Fin n) (Fin n) F)) :
    red O ϖ 1 h = 1 := by
  rw [red, liftO_one]
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem red_congr {n : ℕ} (O : Subring F) (ϖ : F) {x y : Matrix (Fin n) (Fin n) F} (e : x = y)
    (hx : IsInt O x) (hy : IsInt O y) : red O ϖ x hx = red O ϖ y hy := by
  subst e
  rfl

def blk (r c : ℕ) (i : Fin (r + c)) : ℕ := if (i : ℕ) < r then 0 else 1

theorem bDA_iff {r c : ℕ} (O : Subring F) (ϖ : F) {Z : Matrix (Fin (r + c)) (Fin (r + c)) F}
    (h : IsInt O Z) : bDA Z ∈ IIset O ϖ ↔ (red O ϖ Z h).BlockTriangular (blk r c) := by
  constructor
  · intro hZ i j hij
    have hji : (j : ℕ) < r ∧ r ≤ (i : ℕ) := by
      unfold blk at hij
      split_ifs at hij <;> omega
    obtain ⟨hj, hi'⟩ := hji
    obtain ⟨i', rfl⟩ : ∃ i' : Fin c, i = Fin.natAdd r i' :=
      ⟨⟨(i : ℕ) - r, by omega⟩, by ext; simp; omega⟩
    obtain ⟨j', rfl⟩ : ∃ j' : Fin r, j = Fin.castAdd c j' := ⟨⟨j, hj⟩, by ext; simp⟩
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (hZ i' j')
  · intro hZ i j
    have hlt : blk r c (Fin.castAdd c j) < blk r c (Fin.natAdd r i) := by
      simp [blk]
    exact Ideal.Quotient.eq_zero_iff_mem.mp (hZ hlt)

theorem parJ_mul {O : Subring F} {ϖ : F} {r c : ℕ} {k k' : GL (Fin (r + c)) F}
    (hk : k ∈ parJ O ϖ r c) (hk' : k' ∈ parJ O ϖ r c) : k * k' ∈ parJ O ϖ r c := by
  have hm : k * k' ∈ GLint O (r + c) := mul_mem hk.1 hk'.1
  refine ⟨hm, ?_⟩
  rw [bDA_iff O ϖ hm.1]
  rw [red_congr O ϖ (Units.val_mul k k') hm.1 (isInt_mul' O hk.1.1 hk'.1.1),
    red_mul O ϖ hk.1.1 hk'.1.1]
  exact ((bDA_iff O ϖ hk.1.1).mp hk.2).mul ((bDA_iff O ϖ hk'.1.1).mp hk'.2)

theorem parJ_inv {O : Subring F} {ϖ : F} {r c : ℕ} {k : GL (Fin (r + c)) F}
    (hk : k ∈ parJ O ϖ r c) : k⁻¹ ∈ parJ O ϖ r c := by
  have hm : k⁻¹ ∈ GLint O (r + c) := inv_mem hk.1
  refine ⟨hm, ?_⟩
  rw [bDA_iff O ϖ hm.1]
  have h1 : IsInt O ((k : Matrix (Fin (r + c)) (Fin (r + c)) F) *
      ((k⁻¹ : GL (Fin (r + c)) F) : Matrix (Fin (r + c)) (Fin (r + c)) F)) :=
    isInt_mul' O hk.1.1 hm.1
  have e1 : (k : Matrix (Fin (r + c)) (Fin (r + c)) F) *
      ((k⁻¹ : GL (Fin (r + c)) F) : Matrix (Fin (r + c)) (Fin (r + c)) F) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hN : red O ϖ (k : Matrix (Fin (r + c)) (Fin (r + c)) F) hk.1.1 * red O ϖ _ hm.1 = 1 := by
    rw [← red_mul O ϖ hk.1.1 hm.1 h1, red_congr O ϖ e1 h1 (e1 ▸ h1)]
    exact red_one O ϖ _
  have hinv : (red O ϖ (k : Matrix (Fin (r + c)) (Fin (r + c)) F) hk.1.1)⁻¹ = red O ϖ _ hm.1 :=
    Matrix.inv_eq_right_inv hN
  letI : Invertible (red O ϖ (k : Matrix (Fin (r + c)) (Fin (r + c)) F) hk.1.1) :=
    ⟨_, mul_eq_one_comm.mp hN, hN⟩
  rw [← hinv]
  exact Matrix.blockTriangular_inv_of_blockTriangular ((bDA_iff O ϖ hk.1.1).mp hk.2)

theorem one_mem_parJ {O : Subring F} {ϖ : F} {r c : ℕ} : (1 : GL (Fin (r + c)) F) ∈ parJ O ϖ r c := by
  refine ⟨one_mem _, fun i j => ⟨0, O.zero_mem, ?_⟩⟩
  have : Fin.natAdd r i ≠ Fin.castAdd c j := by
    intro h
    have := congrArg Fin.val h
    simp at this
    omega
  simp [bDA, Matrix.one_apply, this]

def parSub (O : Subring F) (ϖ : F) (r c : ℕ) : Subgroup (GL (Fin (r + c)) F) where
  carrier := parJ O ϖ r c
  mul_mem' := parJ_mul
  one_mem' := one_mem_parJ
  inv_mem' := parJ_inv

end Alg

section Top

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {O : Subring F} {ϖ : F} {nrm : AbsoluteValue F ℝ} {q : ℕ}

theorem isOpen_O (h : LF O ϖ nrm q) : IsOpen (O : Set F) := by
  rw [h.O_eq]
  exact Valuation.isOpen_integer

theorem isCompact_O (h : LF O ϖ nrm q) : IsCompact (O : Set F) := by
  rw [h.O_eq]
  exact isCompact_iff_compactSpace.mpr (inferInstanceAs (CompactSpace 𝒪[F]))

theorem isOpen_GLint (h : LF O ϖ nrm q) (n : ℕ) : IsOpen (GLint O n : Set (GL (Fin n) F)) := by
  have hv : ∀ a b : Fin n, Continuous fun g : GL (Fin n) F => (g : Matrix (Fin n) (Fin n) F) a b :=
    fun a b => Units.continuous_val.matrix_elem a b
  have hw : ∀ a b : Fin n, Continuous fun g : GL (Fin n) F =>
      ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) a b :=
    fun a b => (hv a b).comp continuous_inv
  have e : (GLint O n : Set (GL (Fin n) F)) =
      (⋂ a, ⋂ b, (fun g : GL (Fin n) F => (g : Matrix (Fin n) (Fin n) F) a b) ⁻¹' (O : Set F)) ∩
      (⋂ a, ⋂ b, (fun g : GL (Fin n) F =>
        ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) a b) ⁻¹' (O : Set F)) := by
    ext g
    simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage]
    rfl
  rw [e]
  exact (isOpen_iInter_of_finite fun a => isOpen_iInter_of_finite fun b =>
      (isOpen_O h).preimage (hv a b)).inter
    (isOpen_iInter_of_finite fun a => isOpen_iInter_of_finite fun b =>
      (isOpen_O h).preimage (hw a b))

theorem isCompact_int (h : LF O ϖ nrm q) (n : ℕ) :
    IsCompact {m : Matrix (Fin n) (Fin n) F | IsInt O m} := by
  have e : {m : Matrix (Fin n) (Fin n) F | IsInt O m} =
      Set.pi Set.univ (fun _ : Fin n => Set.pi Set.univ (fun _ : Fin n => (O : Set F))) := by
    ext m
    exact ⟨fun hm a _ b _ => hm a b, fun hm a b => hm a trivial b trivial⟩
  rw [e]
  exact isCompact_univ_pi (fun _ : Fin n => isCompact_univ_pi (fun _ : Fin n => isCompact_O h))

theorem isCompact_GLint (h : LF O ϖ nrm q) (n : ℕ) : IsCompact (GLint O n : Set (GL (Fin n) F)) := by
  haveI : T2Space F := by
    letI := IsTopologicalAddGroup.rightUniformSpace F
    haveI := isUniformAddGroup_of_addCommGroup (G := F)
    infer_instance
  have hc := isCompact_int h n
  have h2 := (Units.isClosedEmbedding_embedProduct (α := Matrix (Fin n) (Fin n) F)).isCompact_preimage
    (hc.prod (hc.image MulOpposite.continuous_op))
  refine h2.of_isClosed_subset ((GLint O n).isClosed_of_isOpen (isOpen_GLint h n)) ?_
  intro x hx
  exact ⟨hx.1, _, hx.2, rfl⟩

theorem isOpen_parJ (h : LF O ϖ nrm q) (r c : ℕ) : IsOpen (parJ O ϖ r c) := by
  have hP : IsOpen {x : F | ∃ o ∈ O, x = ϖ * o} := by
    have e : {x : F | ∃ o ∈ O, x = ϖ * o} = (fun x => ϖ⁻¹ * x) ⁻¹' (O : Set F) := by
      ext x
      constructor
      · rintro ⟨o, ho, rfl⟩
        simpa [h.ne] using ho
      · intro hx
        exact ⟨_, hx, by simp [h.ne]⟩
    rw [e]
    exact (isOpen_O h).preimage (continuous_const.mul continuous_id)
  have e : parJ O ϖ r c = (GLint O (r + c) : Set (GL (Fin (r + c)) F)) ∩
      ⋂ i : Fin c, ⋂ j : Fin r, (fun g : GL (Fin (r + c)) F =>
        (g : Matrix (Fin (r + c)) (Fin (r + c)) F) (Fin.natAdd r i) (Fin.castAdd c j)) ⁻¹'
          {x : F | ∃ o ∈ O, x = ϖ * o} := by
    ext g
    simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage]
    rfl
  rw [e]
  exact (isOpen_GLint h _).inter (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
    hP.preimage (Units.continuous_val.matrix_elem _ _))

theorem parJ_compact_open : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] {O : Subring F} {ϖ : F} {nrm : AbsoluteValue F ℝ} {q : ℕ},
    LF O ϖ nrm q → ∀ r c : ℕ, ∃ J : Subgroup (GL (Fin (r + c)) F),
      (J : Set (GL (Fin (r + c)) F)) = parJ O ϖ r c ∧ IsOpen (parJ O ϖ r c) ∧
      IsCompact (parJ O ϖ r c) ∧ ∃ μ : Measure (GL (Fin (r + c)) F), μ.IsMulLeftInvariant ∧
        μ (parJ O ϖ r c) = 1 := by
  intro F _ _ _ _ O ϖ nrm q h r c
  have ho : IsOpen (parJ O ϖ r c) := isOpen_parJ h r c
  have hc : IsCompact (parJ O ϖ r c) :=
    (isCompact_GLint h (r + c)).of_isClosed_subset
      ((parSub O ϖ r c).isClosed_of_isOpen ho) fun k hk => hk.1
  refine ⟨parSub O ϖ r c, rfl, ho, hc, ?_⟩
  let K₀ : TopologicalSpace.PositiveCompacts (GL (Fin (r + c)) F) :=
    ⟨⟨parJ O ϖ r c, hc⟩, ⟨1, by
      rw [ho.interior_eq]
      exact one_mem_parJ⟩⟩
  exact ⟨Measure.haarMeasure K₀, inferInstance, Measure.haarMeasure_self (K₀ := K₀)⟩

end Top

end GlobalTheory.CompanionTheory.QL.Par
