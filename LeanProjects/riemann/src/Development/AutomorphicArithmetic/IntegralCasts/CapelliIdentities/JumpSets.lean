import Mathlib

open scoped IntermediateField TensorProduct Matrix Pointwise NumberField Topology ContDiff NNReal ENNReal Polynomial DirectSum BigOperators InnerProductSpace Manifold
open scoped Classical

noncomputable def UpperTheory.Reformulated.B.JumpSetsAlt.HypOdd :
    ℕ → ℕ → Prop :=
    fun (q d : ℕ) ↦ Nat.Prime q ∧ Nat.Prime d ∧ q ≠ d ∧ q ≠ (2 : ℕ) ∧ d ≠ (2 : ℕ)

noncomputable def UpperTheory.Reformulated.B.JumpSetsAlt.IsLayer.{u_1} :
    ℕ → ℕ → ℕ → {L : Type u_1} → [inst : Field L] → [Algebra ℚ L] → L → L → L → Prop :=
    fun (n q d : ℕ) {L : Type u_1} [Field L] [Algebra ℚ L] (ζ a b : L) ↦
      IsPrimitiveRoot ζ ((2 : ℕ) ^ n) ∧ a ^ (2 : ℕ) = -(↑q : L) ∧ b ^ (2 : ℕ) = -(↑d : L) ∧ ℚ⟮ζ, a, b⟯ = ⊤

noncomputable def UpperTheory.Reformulated.B.JumpSetsAlt.E0.{u_1} :
    {L : Type u_1} → [inst : Field L] → [inst_1 : Algebra ℚ L] → L → L → IntermediateField ℚ L :=
    fun {L : Type u_1} [Field L] [Algebra ℚ L] (a b : L) ↦ ℚ⟮a, b⟯

noncomputable def UpperTheory.Reformulated.B.JumpSetsAlt.F1.{u_1} :
    {L : Type u_1} → [inst : Field L] → [inst_1 : Algebra ℚ L] → L → IntermediateField ℚ L :=
    fun {L : Type u_1} [Field L] [Algebra ℚ L] (ζ : L) ↦ ℚ⟮ζ + ζ⁻¹⟯

noncomputable def UpperTheory.Reformulated.B.JumpSetsAlt.hostE.{u_1} :
    {L : Type u_1} → [inst : Field L] → [inst_1 : Algebra ℚ L] → L → L → L → IntermediateField ℚ L :=
    fun {L : Type u_1} [Field L] [Algebra ℚ L] (ζ a b : L) ↦ UpperTheory.Reformulated.B.JumpSetsAlt.E0 a b ⊔ UpperTheory.Reformulated.B.JumpSetsAlt.F1 ζ

theorem UpperTheory.Reformulated.B.JumpSetsAlt.aux6 :
    ∀ (L : Type) [inst : Field L] [inst_1 : NumberField L] (ζ a b : L), CharZero ↥(UpperTheory.Reformulated.B.JumpSetsAlt.hostE ζ a b) := by
  intro L _ _ ζ a b
  infer_instance

theorem UpperTheory.Reformulated.B.JumpSetsAlt.aux7 :
    ∀ (L : Type) [inst : Field L] [inst_1 : NumberField L], IsScalarTower ℚ ℚ L := by
  intro L _ _
  infer_instance

@[reducible] noncomputable def UpperTheory.Reformulated.B.JumpSetsAlt.G0 :
    Type :=
    ℤˣ × ℤˣ

@[reducible] noncomputable def UpperTheory.Reformulated.B.JumpSetsAlt.HGrp :
    ℕ → Type :=
    fun (e : ℕ) ↦ (ZMod ((2 : ℕ) ^ (e + (2 : ℕ))))ˣ ⧸ Subgroup.zpowers (-1 : (ZMod ((2 : ℕ) ^ (e + (2 : ℕ))))ˣ)

@[reducible] noncomputable def UpperTheory.Reformulated.B.JumpSetsAlt.GG :
    ℕ → Type :=
    fun (e : ℕ) ↦ UpperTheory.Reformulated.B.JumpSetsAlt.G0 × UpperTheory.Reformulated.B.JumpSetsAlt.HGrp e

noncomputable def UpperTheory.Reformulated.B.JumpSetsAlt.sgn.{u_1} :
    {L : Type u_1} → [inst : Field L] → [inst_1 : Algebra ℚ L] → Gal(L/ℚ) → L → ℤˣ :=
    fun {L : Type u_1} [Field L] [Algebra ℚ L] (σ : Gal(L/ℚ)) (x : L) ↦ if (σ : L → L) x = x then (1 : ℤˣ) else (-1 : ℤˣ)

theorem UpperTheory.Reformulated.B.JumpSetsAlt.algebra_smulCommClass_complex.{u_1} :
    ∀ {L : Type u_1} [inst : Field L] [inst_1 : Algebra ℚ L] (ζ a b : L), a ∈ UpperTheory.Reformulated.B.JumpSetsAlt.hostE ζ a b := by
  intro L _ _ ζ a b
  exact (le_sup_left : UpperTheory.Reformulated.B.JumpSetsAlt.E0 a b ≤ _) (IntermediateField.subset_adjoin ℚ _ (by simp))

noncomputable def UpperTheory.Reformulated.B.JumpSetsAlt.aE.{u_1} :
    {L : Type u_1} → [inst : Field L] → [inst_1 : Algebra ℚ L] → (ζ a b : L) → ↥(UpperTheory.Reformulated.B.JumpSetsAlt.hostE ζ a b) :=
    fun {L : Type u_1} [Field L] [Algebra ℚ L] (ζ a b : L) ↦
      (⟨a, UpperTheory.Reformulated.B.JumpSetsAlt.algebra_smulCommClass_complex ζ a b⟩ : ↥(UpperTheory.Reformulated.B.JumpSetsAlt.hostE ζ a b))

theorem UpperTheory.Reformulated.B.JumpSetsAlt.sign_action_map_comm.{u_1} :
    ∀ {L : Type u_1} [inst : Field L] [inst_1 : Algebra ℚ L] (ζ a b : L), b ∈ UpperTheory.Reformulated.B.JumpSetsAlt.hostE ζ a b := by
  intro L _ _ ζ a b
  exact (le_sup_left : UpperTheory.Reformulated.B.JumpSetsAlt.E0 a b ≤ _) (IntermediateField.subset_adjoin ℚ _ (by simp))

noncomputable def UpperTheory.Reformulated.B.JumpSetsAlt.bE.{u_1} :
    {L : Type u_1} → [inst : Field L] → [inst_1 : Algebra ℚ L] → (ζ a b : L) → ↥(UpperTheory.Reformulated.B.JumpSetsAlt.hostE ζ a b) :=
    fun {L : Type u_1} [Field L] [Algebra ℚ L] (ζ a b : L) ↦
      (⟨b, UpperTheory.Reformulated.B.JumpSetsAlt.sign_action_map_comm ζ a b⟩ : ↥(UpperTheory.Reformulated.B.JumpSetsAlt.hostE ζ a b))

theorem UpperTheory.Reformulated.B.JumpSetsAlt.complex_normed_instance_compat.{u_1} :
    ∀ {L : Type u_1} [inst : Field L] [inst_1 : Algebra ℚ L] (ζ a b : L), ζ + ζ⁻¹ ∈ UpperTheory.Reformulated.B.JumpSetsAlt.hostE ζ a b := by
  intro L _ _ ζ a b
  exact (le_sup_right : UpperTheory.Reformulated.B.JumpSetsAlt.F1 ζ ≤ _) (IntermediateField.subset_adjoin ℚ _ (by simp))

noncomputable def UpperTheory.Reformulated.B.JumpSetsAlt.thE.{u_1} :
    {L : Type u_1} → [inst : Field L] → [inst_1 : Algebra ℚ L] → (ζ a b : L) → ↥(UpperTheory.Reformulated.B.JumpSetsAlt.hostE ζ a b) :=
    fun {L : Type u_1} [Field L] [Algebra ℚ L] (ζ a b : L) ↦
      (⟨ζ + ζ⁻¹, UpperTheory.Reformulated.B.JumpSetsAlt.complex_normed_instance_compat ζ a b⟩ : ↥(UpperTheory.Reformulated.B.JumpSetsAlt.hostE ζ a b))

noncomputable def UpperTheory.Reformulated.B.JumpSetsAlt.hcl :
    (e : ℕ) → (ZMod ((2 : ℕ) ^ (e + (2 : ℕ))))ˣ → UpperTheory.Reformulated.B.JumpSetsAlt.HGrp e :=
    fun (e : ℕ) (u : (ZMod ((2 : ℕ) ^ (e + (2 : ℕ))))ˣ) ↦
      (↑u : (ZMod ((2 : ℕ) ^ (e + (2 : ℕ))))ˣ ⧸ Subgroup.zpowers (-1 : (ZMod ((2 : ℕ) ^ (e + (2 : ℕ))))ˣ))

noncomputable def UpperTheory.Reformulated.B.JumpSetsAlt.hPart.{u_1} :
    {L : Type u_1} →
      [inst : Field L] →
        [inst_1 : Algebra ℚ L] → (e : ℕ) → (ζ a b : L) → Gal(↥(UpperTheory.Reformulated.B.JumpSetsAlt.hostE ζ a b)/ℚ) → UpperTheory.Reformulated.B.JumpSetsAlt.HGrp e :=
    fun {L : Type u_1} [Field L] [Algebra ℚ L] (e : ℕ) (ζ a b : L) (σ : Gal(↥(UpperTheory.Reformulated.B.JumpSetsAlt.hostE ζ a b)/ℚ)) ↦
      if h :
          ∃ (u : (ZMod ((2 : ℕ) ^ (e + (2 : ℕ))))ˣ),
            (↑((σ : ↥(UpperTheory.Reformulated.B.JumpSetsAlt.hostE ζ a b) → ↥(UpperTheory.Reformulated.B.JumpSetsAlt.hostE ζ a b)) (UpperTheory.Reformulated.B.JumpSetsAlt.thE ζ a b)) : L) =
              ζ ^ (↑u : ZMod ((2 : ℕ) ^ (e + (2 : ℕ)))).val + ζ⁻¹ ^ (↑u : ZMod ((2 : ℕ) ^ (e + (2 : ℕ)))).val then
        UpperTheory.Reformulated.B.JumpSetsAlt.hcl e (Classical.choose h)
      else (1 : UpperTheory.Reformulated.B.JumpSetsAlt.HGrp e)

noncomputable def UpperTheory.Reformulated.B.JumpSetsAlt.galE.{u_1} :
    {L : Type u_1} →
      [inst : Field L] →
        [inst_1 : Algebra ℚ L] → (e : ℕ) → (ζ a b : L) → Gal(↥(UpperTheory.Reformulated.B.JumpSetsAlt.hostE ζ a b)/ℚ) → UpperTheory.Reformulated.B.JumpSetsAlt.GG e :=
    fun {L : Type u_1} [Field L] [Algebra ℚ L] (e : ℕ) (ζ a b : L) (σ : Gal(↥(UpperTheory.Reformulated.B.JumpSetsAlt.hostE ζ a b)/ℚ)) ↦
      ((UpperTheory.Reformulated.B.JumpSetsAlt.sgn σ (UpperTheory.Reformulated.B.JumpSetsAlt.aE ζ a b), UpperTheory.Reformulated.B.JumpSetsAlt.sgn σ (UpperTheory.Reformulated.B.JumpSetsAlt.bE ζ a b)),
        UpperTheory.Reformulated.B.JumpSetsAlt.hPart e ζ a b σ)

noncomputable def UpperTheory.Reformulated.B.JumpSetsAlt.HostGalois :
    Prop :=
    ∀ (e q d : ℕ),
      UpperTheory.Reformulated.B.JumpSetsAlt.HypOdd q d →
        ∀ (L : Type) [inst : Field L] [inst_1 : NumberField L] (ζ a b : L),
          UpperTheory.Reformulated.B.JumpSetsAlt.IsLayer (e + (2 : ℕ)) q d ζ a b →
            IsGalois ℚ ↥(UpperTheory.Reformulated.B.JumpSetsAlt.hostE ζ a b) ∧
              Module.finrank ℚ ↥(UpperTheory.Reformulated.B.JumpSetsAlt.hostE ζ a b) = (2 : ℕ) ^ (e + (2 : ℕ)) ∧
                (∀ (σ τ : Gal(↥(UpperTheory.Reformulated.B.JumpSetsAlt.hostE ζ a b)/ℚ)),
                    UpperTheory.Reformulated.B.JumpSetsAlt.galE e ζ a b (σ * τ) =
                      UpperTheory.Reformulated.B.JumpSetsAlt.galE e ζ a b σ * UpperTheory.Reformulated.B.JumpSetsAlt.galE e ζ a b τ) ∧
                  Function.Bijective (UpperTheory.Reformulated.B.JumpSetsAlt.galE e ζ a b)

@[reducible] noncomputable def UpperTheory.Reformulated.B.JumpSetsAlt.GalL :
    ℕ → Type :=
    fun (n : ℕ) ↦ (ZMod ((2 : ℕ) ^ n))ˣ × ℤˣ × ℤˣ

noncomputable def UpperTheory.Reformulated.B.JumpSetsAlt.galMap.{u_1} :
    {n : ℕ} →
      {L : Type u_1} →
        [inst : Field L] →
          [inst_1 : Algebra ℚ L] → {ζ : L} → IsPrimitiveRoot ζ ((2 : ℕ) ^ n) → L → L → Gal(L/ℚ) → UpperTheory.Reformulated.B.JumpSetsAlt.GalL n :=
    fun {n : ℕ} {L : Type u_1} [Field L] [Algebra ℚ L] {ζ : L} (hζ : IsPrimitiveRoot ζ ((2 : ℕ) ^ n)) (a b : L)
        (σ : Gal(L/ℚ)) ↦
      ((IsPrimitiveRoot.autToPow ℚ hζ : Gal(L/ℚ) → (ZMod ((2 : ℕ) ^ n))ˣ) σ, UpperTheory.Reformulated.B.JumpSetsAlt.sgn σ a,
        UpperTheory.Reformulated.B.JumpSetsAlt.sgn σ b)

theorem UpperTheory.Reformulated.B.JumpSetsAlt.glEmbMat_one_eq_one :
    ∀ (e q d : ℕ) (L : Type) [inst : Field L] [inst_1 : NumberField L] (ζ a b : L),
      UpperTheory.Reformulated.B.JumpSetsAlt.IsLayer (e + (2 : ℕ)) q d ζ a b → IsPrimitiveRoot ζ ((2 : ℕ) ^ (e + (2 : ℕ))) := by
  intro e q d L _ _ ζ a b h
  exact h.1

noncomputable def UpperTheory.Reformulated.B.JumpSetsAlt.HostGalSpec :
    Prop :=
    ∀ (e q d : ℕ),
      UpperTheory.Reformulated.B.JumpSetsAlt.HypOdd q d →
        ∀ (L : Type) [inst : Field L] [inst_1 : NumberField L] (ζ a b : L)
          (h : UpperTheory.Reformulated.B.JumpSetsAlt.IsLayer (e + (2 : ℕ)) q d ζ a b) (σ : Gal(↥(UpperTheory.Reformulated.B.JumpSetsAlt.hostE ζ a b)/ℚ)),
          (↑((σ : ↥(UpperTheory.Reformulated.B.JumpSetsAlt.hostE ζ a b) → ↥(UpperTheory.Reformulated.B.JumpSetsAlt.hostE ζ a b)) (UpperTheory.Reformulated.B.JumpSetsAlt.aE ζ a b)) : L) =
              (↑(↑(UpperTheory.Reformulated.B.JumpSetsAlt.galE e ζ a b σ).1.1 : ℤ) : L) * a ∧
            (↑((σ : ↥(UpperTheory.Reformulated.B.JumpSetsAlt.hostE ζ a b) → ↥(UpperTheory.Reformulated.B.JumpSetsAlt.hostE ζ a b)) (UpperTheory.Reformulated.B.JumpSetsAlt.bE ζ a b)) : L) =
                (↑(↑(UpperTheory.Reformulated.B.JumpSetsAlt.galE e ζ a b σ).1.2 : ℤ) : L) * b ∧
              (∀ (u : (ZMod ((2 : ℕ) ^ (e + (2 : ℕ))))ˣ),
                  (UpperTheory.Reformulated.B.JumpSetsAlt.galE e ζ a b σ).2 = UpperTheory.Reformulated.B.JumpSetsAlt.hcl e u ↔
                    (↑((σ : ↥(UpperTheory.Reformulated.B.JumpSetsAlt.hostE ζ a b) → ↥(UpperTheory.Reformulated.B.JumpSetsAlt.hostE ζ a b)) (UpperTheory.Reformulated.B.JumpSetsAlt.thE ζ a b)) :
                        L) =
                      ζ ^ (↑u : ZMod ((2 : ℕ) ^ (e + (2 : ℕ)))).val + ζ⁻¹ ^ (↑u : ZMod ((2 : ℕ) ^ (e + (2 : ℕ)))).val) ∧
                ∀ (τ : Gal(L/ℚ)),
                  (∀ (x : ↥(UpperTheory.Reformulated.B.JumpSetsAlt.hostE ζ a b)),
                      (↑((σ : ↥(UpperTheory.Reformulated.B.JumpSetsAlt.hostE ζ a b) → ↥(UpperTheory.Reformulated.B.JumpSetsAlt.hostE ζ a b)) x) : L) =
                        (τ : L → L) (↑x : L)) →
                    UpperTheory.Reformulated.B.JumpSetsAlt.galE e ζ a b σ =
                      (((UpperTheory.Reformulated.B.JumpSetsAlt.galMap (UpperTheory.Reformulated.B.JumpSetsAlt.glEmbMat_one_eq_one e q d L ζ a b h) a b τ).2.1,
                          (UpperTheory.Reformulated.B.JumpSetsAlt.galMap (UpperTheory.Reformulated.B.JumpSetsAlt.glEmbMat_one_eq_one e q d L ζ a b h) a b τ).2.2),
                        UpperTheory.Reformulated.B.JumpSetsAlt.hcl e (UpperTheory.Reformulated.B.JumpSetsAlt.galMap (UpperTheory.Reformulated.B.JumpSetsAlt.glEmbMat_one_eq_one e q d L ζ a b h) a b τ).1)

noncomputable def UpperTheory.Reformulated.B.JumpSetsAlt.c0 :
    UpperTheory.Reformulated.B.JumpSetsAlt.G0 :=
    ((-1 : ℤˣ), (-1 : ℤˣ))

noncomputable def UpperTheory.Reformulated.B.JumpSetsAlt.cc :
    (e : ℕ) → UpperTheory.Reformulated.B.JumpSetsAlt.GG e :=
    fun (e : ℕ) ↦ (UpperTheory.Reformulated.B.JumpSetsAlt.c0, (1 : UpperTheory.Reformulated.B.JumpSetsAlt.HGrp e))

noncomputable def UpperTheory.Reformulated.B.JumpSetsAlt.HostConj :
    Prop :=
    ∀ (e q d : ℕ),
      UpperTheory.Reformulated.B.JumpSetsAlt.HypOdd q d →
        ∀ (L : Type) [inst : Field L] [inst_1 : NumberField L] (ζ a b : L),
          UpperTheory.Reformulated.B.JumpSetsAlt.IsLayer (e + (2 : ℕ)) q d ζ a b →
            NumberField.IsCMField ↥(UpperTheory.Reformulated.B.JumpSetsAlt.hostE ζ a b) ∧
              ∀ (φ : ↥(UpperTheory.Reformulated.B.JumpSetsAlt.hostE ζ a b) →+* ℂ) (σ : Gal(↥(UpperTheory.Reformulated.B.JumpSetsAlt.hostE ζ a b)/ℚ)),
                (∀ (x : ↥(UpperTheory.Reformulated.B.JumpSetsAlt.hostE ζ a b)),
                    (φ : ↥(UpperTheory.Reformulated.B.JumpSetsAlt.hostE ζ a b) → ℂ)
                        ((σ : ↥(UpperTheory.Reformulated.B.JumpSetsAlt.hostE ζ a b) → ↥(UpperTheory.Reformulated.B.JumpSetsAlt.hostE ζ a b)) x) =
                      (starRingEnd ℂ : ℂ → ℂ) ((φ : ↥(UpperTheory.Reformulated.B.JumpSetsAlt.hostE ζ a b) → ℂ) x)) ↔
                  UpperTheory.Reformulated.B.JumpSetsAlt.galE e ζ a b σ = UpperTheory.Reformulated.B.JumpSetsAlt.cc e

@[reducible] noncomputable def UpperTheory.Reformulated.B.JumpSetsAlt.hostF.{u_1} :
    {L : Type u_1} → [inst : Field L] → [inst_1 : Algebra ℚ L] → (ζ a b : L) → Subfield ↥(UpperTheory.Reformulated.B.JumpSetsAlt.hostE ζ a b) :=
    fun {L : Type u_1} [Field L] [Algebra ℚ L] (ζ a b : L) ↦ NumberField.maximalRealSubfield ↥(UpperTheory.Reformulated.B.JumpSetsAlt.hostE ζ a b)

noncomputable def UpperTheory.Reformulated.B.JumpSetsAlt.HostReal :
    Prop :=
    ∀ (e q d : ℕ),
      UpperTheory.Reformulated.B.JumpSetsAlt.HypOdd q d →
        ∀ (L : Type) [inst : Field L] [inst_1 : NumberField L] (ζ a b : L),
          UpperTheory.Reformulated.B.JumpSetsAlt.IsLayer (e + (2 : ℕ)) q d ζ a b →
            Module.finrank ℚ ↥(UpperTheory.Reformulated.B.JumpSetsAlt.hostF ζ a b) = (2 : ℕ) ^ (e + (1 : ℕ)) ∧
              ∀ (x : ↥(UpperTheory.Reformulated.B.JumpSetsAlt.hostE ζ a b)),
                (x ∈ UpperTheory.Reformulated.B.JumpSetsAlt.hostF ζ a b ↔
                    ∀ (σ : Gal(↥(UpperTheory.Reformulated.B.JumpSetsAlt.hostE ζ a b)/ℚ)),
                      UpperTheory.Reformulated.B.JumpSetsAlt.galE e ζ a b σ = UpperTheory.Reformulated.B.JumpSetsAlt.cc e →
                        (σ : ↥(UpperTheory.Reformulated.B.JumpSetsAlt.hostE ζ a b) → ↥(UpperTheory.Reformulated.B.JumpSetsAlt.hostE ζ a b)) x = x) ∧
                  (x ∈ UpperTheory.Reformulated.B.JumpSetsAlt.hostF ζ a b ↔ (↑x : L) ∈ ℚ⟮a * b, ζ + ζ⁻¹⟯)

theorem UpperTheory.Reformulated.B.JumpSetsAlt.hostReal_of :
    UpperTheory.Reformulated.B.JumpSetsAlt.HostGalois → UpperTheory.Reformulated.B.JumpSetsAlt.HostGalSpec → UpperTheory.Reformulated.B.JumpSetsAlt.HostConj → UpperTheory.Reformulated.B.JumpSetsAlt.HostReal := by
  intro hG hS hC e q d hqd L _ _ ζ a b hL
  obtain ⟨hgal, hfin, hmul, hbij⟩ := hG e q d hqd L ζ a b hL
  obtain ⟨hCM, hconj⟩ := hC e q d hqd L ζ a b hL
  have hspec := hS e q d hqd L ζ a b hL
  obtain ⟨σ₀, hσ₀⟩ := hbij.2 (UpperTheory.Reformulated.B.JumpSetsAlt.cc e)
  have hone : UpperTheory.Reformulated.B.JumpSetsAlt.galE e ζ a b 1 = 1 := by
    have h := hmul 1 1
    rw [mul_one] at h
    exact left_eq_mul.mp h
  have hfix : ∀ x : ↥(UpperTheory.Reformulated.B.JumpSetsAlt.hostE ζ a b), x ∈ UpperTheory.Reformulated.B.JumpSetsAlt.hostF ζ a b ↔ σ₀ x = x := by
    intro x
    rw [NumberField.mem_maximalRealSubfield_iff]
    constructor
    · intro hx
      obtain ⟨φ⟩ : Nonempty (↥(UpperTheory.Reformulated.B.JumpSetsAlt.hostE ζ a b) →+* ℂ) := inferInstance
      apply φ.injective
      rw [(hconj φ σ₀).mpr hσ₀ x]
      exact hx φ
    · intro hx φ
      have h := (hconj φ σ₀).mpr hσ₀ x
      rw [hx] at h
      exact h.symm
  have hval : ((1 : (ZMod (2 ^ (e + 2)))ˣ) : ZMod (2 ^ (e + 2))).val = 1 := by
    haveI : Fact (1 < 2 ^ (e + 2)) := ⟨Nat.one_lt_two_pow (by omega)⟩
    rw [Units.val_one, ZMod.val_one]
  have hth : ∀ σ : Gal(↥(UpperTheory.Reformulated.B.JumpSetsAlt.hostE ζ a b)/ℚ), (UpperTheory.Reformulated.B.JumpSetsAlt.galE e ζ a b σ).2 = 1 ↔
      σ (UpperTheory.Reformulated.B.JumpSetsAlt.thE ζ a b) = UpperTheory.Reformulated.B.JumpSetsAlt.thE ζ a b := by
    intro σ
    have h := (hspec σ).2.2.1 1
    rw [hval, pow_one, pow_one] at h
    exact h.trans ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
  have hab : ∀ σ : Gal(↥(UpperTheory.Reformulated.B.JumpSetsAlt.hostE ζ a b)/ℚ),
      ((σ (UpperTheory.Reformulated.B.JumpSetsAlt.aE ζ a b * UpperTheory.Reformulated.B.JumpSetsAlt.bE ζ a b) : ↥(UpperTheory.Reformulated.B.JumpSetsAlt.hostE ζ a b)) : L) =
        ((((UpperTheory.Reformulated.B.JumpSetsAlt.galE e ζ a b σ).1.1 * (UpperTheory.Reformulated.B.JumpSetsAlt.galE e ζ a b σ).1.2 : ℤˣ) : ℤ) : L) * (a * b) := by
    intro σ
    rw [map_mul, IntermediateField.coe_mul, (hspec σ).1, (hspec σ).2.1]
    push_cast
    ring
  have ha : a ≠ 0 := by
    rintro rfl
    have h := hL.2.1
    have hq : (q : L) ≠ 0 := Nat.cast_ne_zero.mpr hqd.1.ne_zero
    exact hq (by simpa using h)
  have hb : b ≠ 0 := by
    rintro rfl
    have h := hL.2.2.1
    have hd : (d : L) ≠ 0 := Nat.cast_ne_zero.mpr hqd.2.1.ne_zero
    exact hd (by simpa using h)
  refine ⟨?_, fun x => ⟨?_, ?_⟩⟩
  · have h := Module.finrank_mul_finrank ℚ ↥(UpperTheory.Reformulated.B.JumpSetsAlt.hostF ζ a b) ↥(UpperTheory.Reformulated.B.JumpSetsAlt.hostE ζ a b)
    rw [Algebra.IsQuadraticExtension.finrank_eq_two ↥(UpperTheory.Reformulated.B.JumpSetsAlt.hostF ζ a b) ↥(UpperTheory.Reformulated.B.JumpSetsAlt.hostE ζ a b),
      hfin, show 2 ^ (e + 2) = 2 ^ (e + 1) * 2 from pow_succ 2 (e + 1)] at h
    exact Nat.eq_of_mul_eq_mul_right two_pos h
  · rw [hfix]
    exact ⟨fun hx σ hσ => by rw [hbij.1 (hσ.trans hσ₀.symm)]; exact hx, fun hx => hx σ₀ hσ₀⟩
  · set K : IntermediateField ℚ ↥(UpperTheory.Reformulated.B.JumpSetsAlt.hostE ζ a b) :=
      ℚ⟮UpperTheory.Reformulated.B.JumpSetsAlt.aE ζ a b * UpperTheory.Reformulated.B.JumpSetsAlt.bE ζ a b, UpperTheory.Reformulated.B.JumpSetsAlt.thE ζ a b⟯ with hK
    have hlift : (x : L) ∈ ℚ⟮a * b, ζ + ζ⁻¹⟯ ↔ x ∈ K := by
      have h1 := IntermediateField.lift_adjoin ℚ (UpperTheory.Reformulated.B.JumpSetsAlt.hostE ζ a b)
        {UpperTheory.Reformulated.B.JumpSetsAlt.aE ζ a b * UpperTheory.Reformulated.B.JumpSetsAlt.bE ζ a b, UpperTheory.Reformulated.B.JumpSetsAlt.thE ζ a b}
      rw [Set.image_pair] at h1
      have h2 := IntermediateField.mem_lift (F := UpperTheory.Reformulated.B.JumpSetsAlt.hostE ζ a b)
        (E := ℚ⟮UpperTheory.Reformulated.B.JumpSetsAlt.aE ζ a b * UpperTheory.Reformulated.B.JumpSetsAlt.bE ζ a b, UpperTheory.Reformulated.B.JumpSetsAlt.thE ζ a b⟯) x
      exact (SetLike.ext_iff.mp h1 (x : L)).symm.trans h2
    rw [hlift, hfix]
    constructor
    · intro hx
      rw [← IsGalois.fixedField_fixingSubgroup K, IntermediateField.mem_fixedField_iff]
      intro σ hσ
      rw [IntermediateField.mem_fixingSubgroup_iff] at hσ
      have h1 := hab σ
      rw [hσ _ (IntermediateField.subset_adjoin ℚ _ (by simp))] at h1
      have h2 := (hth σ).mpr (hσ _ (IntermediateField.subset_adjoin ℚ _ (by simp)))
      have h3 : (UpperTheory.Reformulated.B.JumpSetsAlt.galE e ζ a b σ).1.1 * (UpperTheory.Reformulated.B.JumpSetsAlt.galE e ζ a b σ).1.2 = 1 := by
        have h4 : a * b = ((((UpperTheory.Reformulated.B.JumpSetsAlt.galE e ζ a b σ).1.1 *
          (UpperTheory.Reformulated.B.JumpSetsAlt.galE e ζ a b σ).1.2 : ℤˣ) : ℤ) : L) * (a * b) := h1
        have h5 := (right_eq_mul₀ (mul_ne_zero ha hb)).mp h4
        exact Units.ext (Int.cast_injective (α := L) (by simpa using h5))
      have h6 : UpperTheory.Reformulated.B.JumpSetsAlt.galE e ζ a b σ = 1 ∨ UpperTheory.Reformulated.B.JumpSetsAlt.galE e ζ a b σ = UpperTheory.Reformulated.B.JumpSetsAlt.cc e := by
        generalize UpperTheory.Reformulated.B.JumpSetsAlt.galE e ζ a b σ = g at h2 h3
        obtain ⟨⟨s, t⟩, u⟩ := g
        dsimp only at h2 h3
        subst h2
        rcases Int.units_eq_one_or s with rfl | rfl
        · left
          rw [one_mul] at h3
          rw [h3]
          rfl
        · right
          have : t = -1 := by
            rw [neg_mul, one_mul, neg_eq_iff_eq_neg] at h3
            exact h3
          rw [this]
          rfl
      rcases h6 with h6 | h6
      · rw [hbij.1 (h6.trans hone.symm)]
        rfl
      · rw [hbij.1 (h6.trans hσ₀.symm)]
        exact hx
    · intro hx
      have hle : K ≤ IntermediateField.fixedField (Subgroup.zpowers σ₀) := by
        rw [hK, IntermediateField.adjoin_le_iff]
        have hgen : ∀ y, σ₀ y = y → y ∈ IntermediateField.fixedField (Subgroup.zpowers σ₀) := by
          intro y hy
          rw [IntermediateField.mem_fixedField_iff, Subgroup.forall_mem_zpowers]
          exact (MulAction.mem_fixedBy_zpowers_iff_mem_fixedBy (g := σ₀)).mpr hy
        rintro y (rfl | rfl)
        · refine hgen _ (Subtype.ext ?_)
          rw [hab σ₀, hσ₀]
          simp [UpperTheory.Reformulated.B.JumpSetsAlt.cc, UpperTheory.Reformulated.B.JumpSetsAlt.c0, UpperTheory.Reformulated.B.JumpSetsAlt.aE, UpperTheory.Reformulated.B.JumpSetsAlt.bE]
        · exact hgen _ ((hth σ₀).mp (by rw [hσ₀]; rfl))
      exact (IntermediateField.mem_fixedField_iff _ x).mp (hle hx) σ₀ (Subgroup.mem_zpowers σ₀)
