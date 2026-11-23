import Formalism.DoubleCosetMeasures.StatementV

open MeasureTheory Matrix Set Pointwise

namespace Formalism.DoubleCosetMeasures.P.GLRed

variable {F : Type} [Field F] (O : Subring F) {a : ℕ}

def intM (M : Matrix (Fin a) (Fin a) F) (h : IsInt O M) : Matrix (Fin a) (Fin a) O :=
  fun i j => ⟨M i j, h i j⟩

theorem map_intM (M : Matrix (Fin a) (Fin a) F) (h : IsInt O M) : (intM O M h).map O.subtype = M :=
  rfl

theorem map_sub_inj : Function.Injective
    (fun M : Matrix (Fin a) (Fin a) O => M.map O.subtype) :=
  Matrix.map_injective Subtype.val_injective

theorem intM_mul (M N : Matrix (Fin a) (Fin a) F) (hM : IsInt O M) (hN : IsInt O N)
    (hMN : IsInt O (M * N)) : intM O (M * N) hMN = intM O M hM * intM O N hN := by
  apply map_sub_inj O
  simp only [Matrix.map_mul, map_intM]

theorem intM_one (h : IsInt O (1 : Matrix (Fin a) (Fin a) F)) :
    intM O (1 : Matrix (Fin a) (Fin a) F) h = 1 := by
  apply map_sub_inj O
  simp only [map_intM, Matrix.map_one _ (map_zero O.subtype) (map_one O.subtype)]

variable (a)

def toO : GLint O a →* GL (Fin a) O where
  toFun g :=
    { val := intM O _ g.2.1
      inv := intM O _ g.2.2
      val_inv := by
        apply map_sub_inj O
        simp only [Matrix.map_mul, map_intM, Matrix.map_one _ (map_zero O.subtype) (map_one O.subtype)]
        rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
      inv_val := by
        apply map_sub_inj O
        simp only [Matrix.map_mul, map_intM, Matrix.map_one _ (map_zero O.subtype) (map_one O.subtype)]
        rw [← Units.val_mul, inv_mul_cancel, Units.val_one] }
  map_one' := by
    ext1
    exact intM_one O _
  map_mul' g h := by
    ext1
    exact intM_mul O _ _ _ _ _

variable (ϖ : F) (hϖ : ϖ ∈ O)

def red : GLint O a →* GL (Fin a) (kF O ϖ hϖ) :=
  (Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk (Ideal.span {(⟨ϖ, hϖ⟩ : O)}))).comp (toO O a)

theorem red_val (g : GLint O a) (i j : Fin a) :
    ((red O a ϖ hϖ g : GL (Fin a) (kF O ϖ hϖ)) : Matrix (Fin a) (Fin a) (kF O ϖ hϖ)) i j =
      Ideal.Quotient.mk _ ⟨((g : GL (Fin a) F) : Matrix (Fin a) (Fin a) F) i j, g.2.1 i j⟩ :=
  rfl

variable {a}

theorem mem_span_iff (hϖ0 : ϖ ≠ 0) (x : O) :
    x ∈ Ideal.span {(⟨ϖ, hϖ⟩ : O)} ↔ ϖ⁻¹ * (x : F) ∈ O := by
  rw [Ideal.mem_span_singleton']
  constructor
  · rintro ⟨c, hc⟩
    have : (x : F) = c * ϖ := by rw [← hc]; rfl
    rw [this, mul_comm (c : F), ← mul_assoc, inv_mul_cancel₀ hϖ0, one_mul]; exact c.2
  · intro h
    refine ⟨⟨_, h⟩, Subtype.ext ?_⟩
    change ϖ⁻¹ * (x : F) * ϖ = x
    field_simp

theorem one_kF (i j : Fin a) : (1 : Matrix (Fin a) (Fin a) (kF O ϖ hϖ)) i j =
    Ideal.Quotient.mk _ ((1 : Matrix (Fin a) (Fin a) O) i j) := by
  rw [Matrix.one_apply, Matrix.one_apply]; split_ifs <;> simp

theorem one_coe (i j : Fin a) :
    (((1 : Matrix (Fin a) (Fin a) O) i j : O) : F) = (1 : Matrix (Fin a) (Fin a) F) i j := by
  rw [Matrix.one_apply, Matrix.one_apply]; split_ifs <;> simp

theorem ker_red (hϖ0 : ϖ ≠ 0) :
    (red O a ϖ hϖ).ker = (congSub O ϖ a).subgroupOf (GLint O a) := by
  ext g
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  change _ ↔ (g : GL (Fin a) F) ∈ GLint O a ∧ _
  have key : ∀ i j, ((red O a ϖ hϖ g : GL (Fin a) (kF O ϖ hϖ)) : Matrix (Fin a) (Fin a) _) i j =
      (1 : Matrix (Fin a) (Fin a) (kF O ϖ hϖ)) i j ↔
      (ϖ⁻¹ • (((g : GL (Fin a) F) : Matrix (Fin a) (Fin a) F) - 1)) i j ∈ O := by
    intro i j
    rw [red_val, one_kF, Ideal.Quotient.eq, mem_span_iff O ϖ hϖ hϖ0]
    simp [Matrix.smul_apply, Matrix.sub_apply, one_coe]
  constructor
  · intro h
    refine ⟨g.2, fun i j => (key i j).1 ?_⟩
    rw [h]; rfl
  · rintro ⟨-, h⟩
    apply Units.ext; ext i j
    exact (key i j).2 (h i j)

theorem nontriv (hloc : IsLocalAt O ϖ) : Nontrivial (kF O ϖ hϖ) := by
  apply Ideal.Quotient.nontrivial_iff.mpr
  rw [Ne, Ideal.eq_top_iff_one, Ideal.mem_span_singleton']
  rintro ⟨c, hc⟩
  have h1 : (c : F) * ϖ = 1 := congrArg Subtype.val hc
  apply hloc.1
  rw [← eq_inv_of_mul_eq_one_left h1]; exact c.2

variable (a)

theorem red_surj (hloc : IsLocalAt O ϖ) : Function.Surjective (red O a ϖ hϖ) := by
  intro gb
  have := nontriv O ϖ hϖ hloc
  let G0 : Matrix (Fin a) (Fin a) O := fun i j => (Ideal.Quotient.mk_surjective (gb.val i j)).choose
  have hG0 : ∀ i j, Ideal.Quotient.mk _ (G0 i j) = gb.val i j := fun i j =>
    (Ideal.Quotient.mk_surjective (gb.val i j)).choose_spec
  have hG0' : G0.map (Ideal.Quotient.mk (Ideal.span {(⟨ϖ, hϖ⟩ : O)})) = gb.val := by
    ext i j; exact hG0 i j
  have hdet : Ideal.Quotient.mk (Ideal.span {(⟨ϖ, hϖ⟩ : O)}) G0.det = gb.val.det := by
    rw [RingHom.map_det, RingHom.mapMatrix_apply, hG0']
  have hdetu : IsUnit (Ideal.Quotient.mk (Ideal.span {(⟨ϖ, hϖ⟩ : O)}) G0.det) := by
    rw [hdet]; exact (Matrix.isUnit_iff_isUnit_det _).mp gb.isUnit
  have hnot : G0.det ∉ Ideal.span {(⟨ϖ, hϖ⟩ : O)} := fun h => by
    rw [← Ideal.Quotient.eq_zero_iff_mem] at h; rw [h] at hdetu; exact not_isUnit_zero hdetu
  have hnot' : ∀ o ∈ O, (G0.det : F) ≠ ϖ * o := by
    intro o ho he; apply hnot; rw [Ideal.mem_span_singleton']
    exact ⟨⟨o, ho⟩, Subtype.ext (by simp [he, mul_comm])⟩
  have hinv : (G0.det : F)⁻¹ ∈ O := hloc.2 _ G0.det.2 hnot'
  have hne : (G0.det : F) ≠ 0 := by simpa using hnot' 0 O.zero_mem
  have hu : IsUnit G0.det :=
    ⟨⟨G0.det, ⟨_, hinv⟩, Subtype.ext (by simp [hne]), Subtype.ext (by simp [hne])⟩, rfl⟩
  let U : GL (Fin a) O := ((Matrix.isUnit_iff_isUnit_det G0).mpr hu).unit
  let g : GL (Fin a) F := Matrix.GeneralLinearGroup.map O.subtype U
  have hg : g ∈ GLint O a := by
    refine ⟨fun i j => ?_, fun i j => ?_⟩
    · exact ((U : Matrix (Fin a) (Fin a) O) i j).2
    · rw [← map_inv]; exact (((U⁻¹ : GL (Fin a) O) : Matrix (Fin a) (Fin a) O) i j).2
  refine ⟨⟨g, hg⟩, ?_⟩
  apply Units.ext; ext i j
  rw [red_val]
  exact hG0 i j

theorem card_eq (hϖ0 : ϖ ≠ 0) (hloc : IsLocalAt O ϖ) :
    Nat.card ((GLint O a) ⧸ (congSub O ϖ a).subgroupOf (GLint O a)) =
      Nat.card (GL (Fin a) (kF O ϖ hϖ)) := by
  rw [← ker_red O ϖ hϖ hϖ0]
  exact Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective _ (red_surj O a ϖ hϖ hloc)).toEquiv

end Formalism.DoubleCosetMeasures.P.GLRed

namespace Formalism.DoubleCosetMeasures.P

theorem glRed : Formalism.DoubleCosetMeasures.GLRed := by
  intro F _ O ϖ hϖ hϖ0 hloc _ a
  exact GLRed.card_eq O a ϖ hϖ hϖ0 hloc

end Formalism.DoubleCosetMeasures.P

namespace Formalism.DoubleCosetMeasures.P.GLRed

theorem relIndex_mul_measure {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G]
    (H L : Subgroup G) (hHL : H ≤ L) [(H.subgroupOf L).FiniteIndex]
    (hH : MeasurableSet (H : Set G)) (μ : Measure G) [μ.IsMulLeftInvariant] :
    (H.relIndex L : ENNReal) * μ H = μ L := by
  obtain ⟨s, hs, -⟩ := (H.subgroupOf L).exists_isComplement_left 1
  have hs' : Finite s := hs.finite_left_iff.mpr inferInstance
  have hU : (⋃ a : s, (a.val : L) • (H : Set G)) = (L : Set G) := by
    ext x
    simp only [mem_iUnion, Set.mem_smul_set, SetLike.mem_coe]
    constructor
    · rintro ⟨a, h, hh, rfl⟩
      exact L.mul_mem a.val.2 (hHL hh)
    · intro hx
      obtain ⟨⟨b, h⟩, hbh, -⟩ := hs.existsUnique ⟨x, hx⟩
      refine ⟨b, (h.val : G), Subgroup.mem_subgroupOf.mp h.2, ?_⟩
      have := congrArg Subtype.val hbh
      exact this
  have hdisj : Pairwise (Function.onFun Disjoint fun a : s => (a.val : L) • (H : Set G)) := by
    intro a b hab
    rw [Function.onFun, Set.disjoint_left]
    rintro x ⟨h1, hh1, rfl⟩ ⟨h2, hh2, he⟩
    apply hab
    have hh1' : (⟨h1, hHL hh1⟩ : L) ∈ H.subgroupOf L := Subgroup.mem_subgroupOf.mpr hh1
    have hh2' : (⟨h2, hHL hh2⟩ : L) ∈ H.subgroupOf L := Subgroup.mem_subgroupOf.mpr hh2
    have e : (a.val : L) * ⟨h1, hHL hh1⟩ = (b.val : L) * ⟨h2, hHL hh2⟩ := Subtype.ext he.symm
    have := (hs.existsUnique ((a.val : L) * ⟨h1, hHL hh1⟩)).unique
      (y₁ := (a, ⟨_, hh1'⟩)) (y₂ := (b, ⟨_, hh2'⟩)) rfl e.symm
    exact congrArg Prod.fst this
  calc (H.relIndex L : ENNReal) * μ H = ∑' a : s, μ ((a.val : L) • (H : Set G)) := by
        simp [measure_smul, hs.encard_left, Subgroup.relIndex]
    _ = μ (⋃ a : s, (a.val : L) • (H : Set G)) :=
        (measure_iUnion hdisj fun a => hH.const_smul _).symm
    _ = μ L := by rw [hU]

section Top

variable {F : Type} [Field F] [TopologicalSpace F] [IsTopologicalRing F]

theorem congSub_open (O : Subring F) (hO : IsOpen (O : Set F)) (ϖ : F) (a : ℕ) :
    IsOpen (congSub O ϖ a : Set (GL (Fin a) F)) := by
  have e : (congSub O ϖ a : Set (GL (Fin a) F)) =
      ((⋂ i, ⋂ j, (fun g : GL (Fin a) F => (g : Matrix (Fin a) (Fin a) F) i j) ⁻¹' (O : Set F)) ∩
      (⋂ i, ⋂ j, (fun g : GL (Fin a) F =>
        ((g⁻¹ : GL (Fin a) F) : Matrix (Fin a) (Fin a) F) i j) ⁻¹' (O : Set F))) ∩
      (⋂ i, ⋂ j, (fun g : GL (Fin a) F =>
        ϖ⁻¹ * ((g : Matrix (Fin a) (Fin a) F) i j - (1 : Matrix (Fin a) (Fin a) F) i j)) ⁻¹'
          (O : Set F)) := by
    ext g; simp [congSub, GLint, IsInt]
  rw [e]
  refine IsOpen.inter (IsOpen.inter (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite
    fun j => hO.preimage ?_) (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite
    fun j => hO.preimage ?_)) (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite
    fun j => hO.preimage ?_)
  · exact Units.continuous_val.matrix_elem i j
  · exact Units.continuous_coe_inv.matrix_elem i j
  · exact continuous_const.mul ((Units.continuous_val.matrix_elem i j).sub continuous_const)

end Top

end Formalism.DoubleCosetMeasures.P.GLRed

namespace Formalism.DoubleCosetMeasures.P

theorem volJ : Formalism.DoubleCosetMeasures.VolJ := by
  intro F _ _ _ O hO ϖ hϖ hϖ0 hloc hfin a μ _ J' hKJ hJL
  have hKL : congSub O ϖ a ≤ GLint O a := fun g hg => hg.1
  have hcard := GLRed.card_eq O a ϖ hϖ hϖ0 hloc
  have hfinGL : Finite (GL (Fin a) (kF O ϖ hϖ)) := by
    have : Finite (Matrix (Fin a) (Fin a) (kF O ϖ hϖ)) :=
      inferInstanceAs (Finite (Fin a → Fin a → kF O ϖ hϖ))
    exact Finite.of_injective _ Units.val_injective
  have hpos : Nat.card (GL (Fin a) (kF O ϖ hϖ)) ≠ 0 := Nat.card_pos.ne'
  have hrel : (congSub O ϖ a).relIndex (GLint O a) = Nat.card (GL (Fin a) (kF O ϖ hϖ)) := by
    rw [← hcard]; rfl
  have hmul := Subgroup.relIndex_mul_relIndex (congSub O ϖ a) J' (GLint O a) hKJ hJL
  have hJfin : J'.relIndex (GLint O a) ≠ 0 := by
    intro h0; rw [h0, mul_zero, hrel] at hmul; exact hpos hmul.symm
  have : (J'.subgroupOf (GLint O a)).FiniteIndex := ⟨hJfin⟩
  have hJopen : IsOpen (J' : Set (GL (Fin a) F)) :=
    Subgroup.isOpen_mono hKJ (GLRed.congSub_open O hO ϖ a)
  have hmeas := GLRed.relIndex_mul_measure J' (GLint O a) hJL hJopen.measurableSet μ
  have hq : Nat.card (J' ⧸ (congSub O ϖ a).subgroupOf J') = (congSub O ϖ a).relIndex J' := rfl
  rw [hq, ← hmeas, ← hrel, ← hmul]
  push_cast
  ring

end Formalism.DoubleCosetMeasures.P
