import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTamagawa
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TamagawaSpecialUnitary

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Filter Topology
open scoped TensorProduct

namespace GlobalTheory.TamCnt

def genLat (F : Type) {E : Type} [Field F] [Field E] [Algebra F E] {M : ℕ} (R : Type) [CommRing R] [Algebra F R]
    (S : Set R) (L : Set (Fin M → E)) : AddSubgroup (Fin M → R ⊗[F] E) :=
  AddSubgroup.closure {y | ∃ a ∈ S, ∃ x ∈ L, y = fun i => a ⊗ₜ[F] x i}

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {M : ℕ}
  (R : Type) [CommRing R] [Algebra F R] (S : Set R)

theorem tmul_smul_mem_genLat (Λ : Submodule (𝓞 E) (Fin M → E)) (I : Ideal (𝓞 E)) {i : 𝓞 E} (hi : i ∈ I)
    {z : Fin M → R ⊗[F] E} (hz : z ∈ genLat F R S (Λ : Set (Fin M → E))) :
    ((1 : R) ⊗ₜ[F] (i : E)) • z ∈ genLat F R S ((I • Λ : Submodule (𝓞 E) (Fin M → E)) : Set (Fin M → E)) := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, x, hx, rfl⟩ := hz
    refine AddSubgroup.subset_closure ⟨a, ha, i • x, Submodule.smul_mem_smul hi hx, ?_⟩
    funext j
    simp [Algebra.TensorProduct.tmul_mul_tmul, Algebra.smul_def]
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

theorem mulVec_mem_genLat_smul (Λ : Submodule (𝓞 E) (Fin M → E)) (I : Ideal (𝓞 E))
    (m : Matrix (Fin M) (Fin M) (R ⊗[F] E))
    (hm : ∀ y ∈ genLat F R S (Λ : Set (Fin M → E)), m *ᵥ y ∈ genLat F R S (Λ : Set (Fin M → E))) :
    ∀ y ∈ genLat F R S ((I • Λ : Submodule (𝓞 E) (Fin M → E)) : Set (Fin M → E)),
      m *ᵥ y ∈ genLat F R S ((I • Λ : Submodule (𝓞 E) (Fin M → E)) : Set (Fin M → E)) := by
  intro y hy
  induction hy using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, x, hx, rfl⟩ := hz
    induction hx using Submodule.smul_induction_on' with
    | smul i hi l hl =>
      have e : (fun j => a ⊗ₜ[F] (i • l) j) = ((1 : R) ⊗ₜ[F] (i : E)) • fun j => a ⊗ₜ[F] l j := by
        funext j
        simp [Algebra.TensorProduct.tmul_mul_tmul, Algebra.smul_def]
      rw [e, Matrix.mulVec_smul]
      exact tmul_smul_mem_genLat R S Λ I hi (hm _ (AddSubgroup.subset_closure ⟨a, ha, l, hl, rfl⟩))
    | add x hx x' hx' h1 h2 =>
      have e : (fun j => a ⊗ₜ[F] (x + x') j) = (fun j => a ⊗ₜ[F] x j) + fun j => a ⊗ₜ[F] x' j := by
        funext j
        simp [TensorProduct.tmul_add]
      rw [e, Matrix.mulVec_add]
      exact add_mem h1 h2
  | zero => simp
  | add x y _ _ hx hy => rw [Matrix.mulVec_add]; exact add_mem hx hy
  | neg x _ hx => rw [Matrix.mulVec_neg]; exact neg_mem hx

theorem genLat_mono {L L' : Set (Fin M → E)} (h : L ⊆ L') : genLat F R S L ≤ genLat F R S L' := by
  refine AddSubgroup.closure_mono ?_
  rintro y ⟨a, ha, x, hx, rfl⟩
  exact ⟨a, ha, x, h hx, rfl⟩

end Gen

section Adelic

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {M : ℕ}
  (σ : E →ₐ[F] E) (J : Matrix (Fin M) (Fin M) E)

theorem finMat_mul (g h : HA (AF F) σ J) : finMat σ J (g * h) = finMat σ J g * finMat σ J h := by
  unfold finMat
  exact Matrix.map_mul (f := (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)).toRingHom)

theorem finMat_one : finMat σ J (1 : HA (AF F) σ J) = 1 := by
  unfold finMat
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem finMat_inv_mul (g : HA (AF F) σ J) : finMat σ J g⁻¹ * finMat σ J g = 1 := by
  rw [← finMat_mul, inv_mul_cancel, finMat_one]

theorem finMat_mul_inv (g : HA (AF F) σ J) : finMat σ J g * finMat σ J g⁻¹ = 1 := by
  rw [← finMat_mul, mul_inv_cancel, finMat_one]

def latK (Λ : Submodule (𝓞 E) (Fin M → E)) (v : HeightOneSpectrum (𝓞 F)) (k : ℕ) :
    AddSubgroup (Fin M → Af F ⊗[F] E) :=
  latHat F E ((((v.asIdeal ^ k).map (algebraMap (𝓞 F) (𝓞 E))) • Λ : Submodule (𝓞 E) (Fin M → E)) :
    Set (Fin M → E))

theorem latK_anti (Λ : Submodule (𝓞 E) (Fin M → E)) (v : HeightOneSpectrum (𝓞 F)) (k : ℕ) :
    latK Λ v (k + 1) ≤ latK Λ v k := by
  refine genLat_mono (Af F) (intAf F) ?_
  refine Submodule.smul_mono_left (Ideal.map_mono (Ideal.pow_le_pow_right (Nat.le_succ k)))

theorem mulVec_mem_latK (Λ : Submodule (𝓞 E) (Fin M → E)) (v : HeightOneSpectrum (𝓞 F)) (k : ℕ)
    (m : Matrix (Fin M) (Fin M) (Af F ⊗[F] E))
    (hm : ∀ y, y ∈ latHat F E (Λ : Set (Fin M → E)) ↔ m *ᵥ y ∈ latHat F E (Λ : Set (Fin M → E)))
    {y : Fin M → Af F ⊗[F] E} (hy : y ∈ latK Λ v k) : m *ᵥ y ∈ latK Λ v k :=
  mulVec_mem_genLat_smul (Af F) (intAf F) Λ _ m (fun y hy => (hm y).1 hy) y hy

theorem stabHat_mul {Λ : Set (Fin M → E)} {g h : HA (AF F) σ J}
    (hg : GlobalTheory.Mem.Vol.StabHat F Λ (finMat σ J g)) (hh : GlobalTheory.Mem.Vol.StabHat F Λ (finMat σ J h)) :
    GlobalTheory.Mem.Vol.StabHat F Λ (finMat σ J (g * h)) := by
  intro y
  rw [finMat_mul, ← Matrix.mulVec_mulVec]
  exact (hh y).trans (hg _)

theorem stabHat_inv {Λ : Set (Fin M → E)} {g : HA (AF F) σ J}
    (hg : GlobalTheory.Mem.Vol.StabHat F Λ (finMat σ J g)) : GlobalTheory.Mem.Vol.StabHat F Λ (finMat σ J g⁻¹) := by
  intro y
  have := hg (finMat σ J g⁻¹ *ᵥ y)
  rw [Matrix.mulVec_mulVec, finMat_mul_inv, Matrix.one_mulVec] at this
  exact this.symm

theorem stabHat_one {Λ : Set (Fin M → E)} : GlobalTheory.Mem.Vol.StabHat F Λ (finMat σ J (1 : HA (AF F) σ J)) := by
  intro y
  rw [finMat_one, Matrix.one_mulVec]

def stabG (Λ : Submodule (𝓞 E) (Fin M → E)) : Subgroup (GlobalTheory.Published.SUAdelic σ J) where
  carrier := GlobalTheory.TamSU.stabSet σ J Λ
  one_mem' := stabHat_one σ J
  mul_mem' {a b} ha hb := stabHat_mul σ J ha hb
  inv_mem' {a} ha := stabHat_inv σ J ha

def congG (Λ : Submodule (𝓞 E) (Fin M → E)) (v : HeightOneSpectrum (𝓞 F)) (k : ℕ) :
    Subgroup (GlobalTheory.Published.SUAdelic σ J) where
  carrier := {h | h ∈ GlobalTheory.TamSU.stabSet σ J Λ ∧
    ∀ y ∈ latHat F E (Λ : Set (Fin M → E)), (finMat σ J h.1 - 1) *ᵥ y ∈ latK Λ v k}
  one_mem' := ⟨stabHat_one σ J, fun y _ => by
    rw [show ((1 : GlobalTheory.Published.SUAdelic σ J) : HA (AF F) σ J) = 1 from rfl, finMat_one, sub_self,
      Matrix.zero_mulVec]
    exact zero_mem _⟩
  mul_mem' {a b} ha hb := by
    refine ⟨stabHat_mul σ J ha.1 hb.1, fun y hy => ?_⟩
    have e : (finMat σ J (a * b).1 - 1) *ᵥ y =
        finMat σ J a.1 *ᵥ ((finMat σ J b.1 - 1) *ᵥ y) + (finMat σ J a.1 - 1) *ᵥ y := by
      rw [show (a * b).1 = a.1 * b.1 from rfl, finMat_mul, Matrix.mulVec_mulVec, ← Matrix.add_mulVec]
      congr 1
      rw [Matrix.mul_sub, Matrix.mul_one, sub_add_sub_cancel]
    rw [e]
    exact add_mem (mulVec_mem_latK Λ v k _ ha.1 (hb.2 y hy)) (ha.2 y hy)
  inv_mem' {a} ha := by
    refine ⟨stabHat_inv σ J ha.1, fun y hy => ?_⟩
    have e : (finMat σ J a⁻¹.1 - 1) *ᵥ y = -(finMat σ J a.1⁻¹ *ᵥ ((finMat σ J a.1 - 1) *ᵥ y)) := by
      rw [show a⁻¹.1 = a.1⁻¹ from rfl, Matrix.mulVec_mulVec, Matrix.mul_sub, finMat_inv_mul, Matrix.mul_one,
        ← Matrix.neg_mulVec, neg_sub]
    rw [e]
    exact neg_mem (mulVec_mem_latK Λ v k _ (stabHat_inv σ J ha.1) (ha.2 y hy))

theorem congG_le_stabG (Λ : Submodule (𝓞 E) (Fin M → E)) (v : HeightOneSpectrum (𝓞 F)) (k : ℕ) :
    congG σ J Λ v k ≤ stabG σ J Λ := fun _ h => h.1

theorem congG_anti (Λ : Submodule (𝓞 E) (Fin M → E)) (v : HeightOneSpectrum (𝓞 F)) (k : ℕ) :
    congG σ J Λ v (k + 1) ≤ congG σ J Λ v k :=
  fun _ h => ⟨h.1, fun y hy => latK_anti Λ v k (h.2 y hy)⟩

end Adelic

section Local

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {M : ℕ}
  (σ : E →ₐ[F] E) (J : Matrix (Fin M) (Fin M) E)

def compLat (v : HeightOneSpectrum (𝓞 F)) (L : Set (Fin M → E)) : AddSubgroup (Fin M → Fv F v ⊗[F] E) :=
  genLat F (Fv F v) (v.adicCompletionIntegers F : Set (Fv F v)) L

def compK (Λ : Submodule (𝓞 E) (Fin M → E)) (v : HeightOneSpectrum (𝓞 F)) (k : ℕ) :
    AddSubgroup (Fin M → Fv F v ⊗[F] E) :=
  compLat v ((((v.asIdeal ^ k).map (algebraMap (𝓞 F) (𝓞 E))) • Λ : Submodule (𝓞 E) (Fin M → E)) :
    Set (Fin M → E))

theorem mulVec_mem_compK (Λ : Submodule (𝓞 E) (Fin M → E)) (v : HeightOneSpectrum (𝓞 F)) (k : ℕ)
    (m : Matrix (Fin M) (Fin M) (Fv F v ⊗[F] E))
    (hm : ∀ y, y ∈ compLat v (Λ : Set (Fin M → E)) ↔ m *ᵥ y ∈ compLat v (Λ : Set (Fin M → E)))
    {y : Fin M → Fv F v ⊗[F] E} (hy : y ∈ compK Λ v k) : m *ᵥ y ∈ compK Λ v k :=
  mulVec_mem_genLat_smul (Fv F v) _ Λ _ m (fun y hy => (hm y).1 hy) y hy

def locCong (Λ : Submodule (𝓞 E) (Fin M → E)) (v : HeightOneSpectrum (𝓞 F)) (k : ℕ) :
    Subgroup (GL (Fin M) (Fv F v ⊗[F] E)) where
  carrier := {g | g ∈ HR (Fv F v) σ J ∧ (g : Matrix (Fin M) (Fin M) (Fv F v ⊗[F] E)).det = 1 ∧
    (∀ y, y ∈ compLat v (Λ : Set (Fin M → E)) ↔
      (g : Matrix (Fin M) (Fin M) (Fv F v ⊗[F] E)) *ᵥ y ∈ compLat v (Λ : Set (Fin M → E))) ∧
    ∀ y ∈ compLat v (Λ : Set (Fin M → E)),
      ((g : Matrix (Fin M) (Fin M) (Fv F v ⊗[F] E)) - 1) *ᵥ y ∈ compK Λ v k}
  one_mem' := ⟨one_mem _, by simp, fun y => by simp, fun y _ => by simp⟩
  mul_mem' {a b} ha hb := by
    refine ⟨mul_mem ha.1 hb.1, by rw [Units.val_mul, Matrix.det_mul, ha.2.1, hb.2.1, one_mul], fun y => ?_,
      fun y hy => ?_⟩
    · rw [Units.val_mul, ← Matrix.mulVec_mulVec]
      exact (hb.2.2.1 y).trans (ha.2.2.1 _)
    · have e : ((a * b : GL (Fin M) (Fv F v ⊗[F] E)) - 1 : Matrix (Fin M) (Fin M) (Fv F v ⊗[F] E)) *ᵥ y =
          (a : Matrix (Fin M) (Fin M) (Fv F v ⊗[F] E)) *ᵥ (((b : Matrix (Fin M) (Fin M) (Fv F v ⊗[F] E)) - 1) *ᵥ y) +
            ((a : Matrix (Fin M) (Fin M) (Fv F v ⊗[F] E)) - 1) *ᵥ y := by
        rw [Units.val_mul, Matrix.mulVec_mulVec, ← Matrix.add_mulVec]
        congr 1
        rw [Matrix.mul_sub, Matrix.mul_one, sub_add_sub_cancel]
      rw [e]
      exact add_mem (mulVec_mem_compK Λ v k _ ha.2.2.1 (hb.2.2.2 y hy)) (ha.2.2.2 y hy)
  inv_mem' {a} ha := by
    have hi : ∀ y, y ∈ compLat v (Λ : Set (Fin M → E)) ↔
        ((a⁻¹ : GL (Fin M) (Fv F v ⊗[F] E)) : Matrix (Fin M) (Fin M) (Fv F v ⊗[F] E)) *ᵥ y ∈
          compLat v (Λ : Set (Fin M → E)) := by
      intro y
      have := ha.2.2.1 (((a⁻¹ : GL (Fin M) (Fv F v ⊗[F] E)) : Matrix _ _ _) *ᵥ y)
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec] at this
      exact this.symm
    refine ⟨inv_mem ha.1, ?_, hi, fun y hy => ?_⟩
    · have h := congrArg Matrix.det (Units.inv_mul a)
      rwa [Matrix.det_mul, ha.2.1, mul_one, Matrix.det_one] at h
    · have e : (((a⁻¹ : GL (Fin M) (Fv F v ⊗[F] E)) : Matrix (Fin M) (Fin M) (Fv F v ⊗[F] E)) - 1) *ᵥ y =
          -(((a⁻¹ : GL (Fin M) (Fv F v ⊗[F] E)) : Matrix _ _ _) *ᵥ (((a : Matrix (Fin M) (Fin M) (Fv F v ⊗[F] E)) - 1) *ᵥ y)) := by
        rw [Matrix.mulVec_mulVec, Matrix.mul_sub, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one,
          ← Matrix.neg_mulVec, neg_sub]
      rw [e]
      exact neg_mem (mulVec_mem_compK Λ v k _ hi (ha.2.2.2 y hy))

end Local

section Count

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {M : ℕ}
  (σ : E →ₐ[F] E) (J : Matrix (Fin M) (Fin M) E)

theorem locCount_eq_relIndex (Λ : Submodule (𝓞 E) (Fin M → E)) (v : HeightOneSpectrum (𝓞 F)) (k : ℕ) :
    GlobalTheory.TamSU.locCount σ J Λ v k = (congG σ J Λ v k).relIndex (stabG σ J Λ) := by
  unfold GlobalTheory.TamSU.locCount Subgroup.relIndex Subgroup.index
  refine Nat.card_congr (Quot.congr (Equiv.subtypeEquivRight fun _ => Iff.rfl) fun a b => ?_)
  refine Iff.trans ?_ QuotientGroup.leftRel_apply.symm
  rw [Subgroup.mem_subgroupOf]
  have hA : GlobalTheory.Mem.Vol.StabHat F (Λ : Set (Fin M → E)) (finMat σ J a.1.1) := a.2
  have e1 : ∀ y, (finMat σ J (a.1⁻¹ * b.1).1 - 1) *ᵥ y =
      -(finMat σ J a.1.1⁻¹ *ᵥ ((finMat σ J a.1.1 - finMat σ J b.1.1) *ᵥ y)) := by
    intro y
    rw [show (a.1⁻¹ * b.1).1 = a.1.1⁻¹ * b.1.1 from rfl, finMat_mul, Matrix.mulVec_mulVec, Matrix.mul_sub,
      finMat_inv_mul, ← Matrix.neg_mulVec, neg_sub]
  have e2 : ∀ y, (finMat σ J a.1.1 - finMat σ J b.1.1) *ᵥ y =
      -(finMat σ J a.1.1 *ᵥ ((finMat σ J (a.1⁻¹ * b.1).1 - 1) *ᵥ y)) := by
    intro y
    rw [show (a.1⁻¹ * b.1).1 = a.1.1⁻¹ * b.1.1 from rfl, finMat_mul, Matrix.mulVec_mulVec, Matrix.mul_sub,
      ← Matrix.mul_assoc, finMat_mul_inv, Matrix.one_mul, Matrix.mul_one, ← Matrix.neg_mulVec, neg_sub]
  constructor
  · intro h
    refine ⟨(stabG σ J Λ).mul_mem ((stabG σ J Λ).inv_mem a.2) b.2, fun y hy => ?_⟩
    have := neg_mem (mulVec_mem_latK Λ v k _ (stabHat_inv σ J hA) (h y hy))
    rw [← e1] at this
    exact this
  · intro h y hy
    rw [e2]
    exact neg_mem (mulVec_mem_latK Λ v k _ hA (h.2 y hy))

end Count

end GlobalTheory.TamCnt
