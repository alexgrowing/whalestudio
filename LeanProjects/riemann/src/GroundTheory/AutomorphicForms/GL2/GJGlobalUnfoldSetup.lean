import Mathlib
import GroundTheory.AutomorphicForms.GL2.GJGlobalDefs
import GroundTheory.AutomorphicForms.GL2.GJGlobalUnfoldCount
import GroundTheory.AutomorphicForms.GL2.GJGlobalUnfoldRank
import GroundTheory.AutomorphicForms.AutomorphicFormSpaces
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.ExistsLintegralConstantTermL2SqLe

open MeasureTheory Set Function NumberField
open scoped ENNReal NNReal NumberField.AdeleRing

namespace GroundTheory.Automorphic.GJGlobal

noncomputable section

namespace UnfoldGL

open Reduction AutomorphicForm RightCosetSpace RankDecomp CuspidalSpectrum

theorem measurePreserving_of_mapsTo_lattice {V : Type*} [AddCommGroup V] [TopologicalSpace V]
    [IsTopologicalAddGroup V] [LocallyCompactSpace V] [SecondCountableTopology V]
    [MeasurableSpace V] [BorelSpace V] (ν : Measure V) [ν.IsAddHaarMeasure]
    {L : AddSubgroup V} [Countable L] {D : Set V} (hD : IsAddFundamentalDomain L D ν)
    (hDm : MeasurableSet D) (hD0 : ν D ≠ 0) (hDtop : ν D ≠ ∞) (φ : V ≃ₜ+ V)
    (hφ : ∀ ξ ∈ L, φ ξ ∈ L) (hφ' : ∀ ξ ∈ L, φ.symm ξ ∈ L) :
    MeasurePreserving φ ν ν := by
  have heq : ν.map φ = Measure.addHaarScalarFactor (ν.map φ) ν • ν :=
    Measure.isAddLeftInvariant_eq_smul _ _
  set c := Measure.addHaarScalarFactor (ν.map φ) ν with hcdef
  have hqmp : Measure.QuasiMeasurePreserving φ ν ν :=
    ⟨(map_continuous φ).measurable, by rw [heq]; exact Measure.smul_absolutelyContinuous⟩
  have hfd : IsAddFundamentalDomain L (φ ⁻¹' D) ν := by
    refine hD.preimage_of_equiv hqmp (e := fun ξ : L => (⟨φ.symm ξ, hφ' _ ξ.2⟩ : L)) ?_ ?_
    · refine ⟨fun a b hab => ?_, fun b => ⟨⟨φ b, hφ _ b.2⟩, ?_⟩⟩
      · have := congrArg (fun x : L => φ (x : V)) hab
        simp only [ContinuousAddEquiv.apply_symm_apply] at this
        exact Subtype.ext this
      · exact Subtype.ext (φ.symm_apply_apply _)
    · intro ξ x
      simp [AddSubgroup.vadd_def, map_add]
  have hmeas : ν (φ ⁻¹' D) = ν D := hfd.measure_eq hD
  have hc : (c : ℝ≥0∞) * ν D = 1 * ν D := by
    have := congrArg (fun m : Measure V => m D) heq
    rw [Measure.map_apply (map_continuous φ).measurable hDm, hmeas, Measure.smul_apply,
      ENNReal.smul_def, smul_eq_mul] at this
    rw [one_mul]
    exact this.symm
  have hc1 : c = 1 := by
    have := (ENNReal.mul_left_inj hD0 hDtop).1 hc
    exact_mod_cast this
  refine ⟨(map_continuous φ).measurable, ?_⟩
  rw [heq, hc1, one_smul]

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

theorem unipMeasure_unipFundamentalDomain_ne_zero (k : ℕ) :
    unipMeasure K n k (unipFundamentalDomain K n k) ≠ 0 := by
  rw [unipMeasure_unipFundamentalDomain]
  exact one_ne_zero

theorem unipMeasure_unipFundamentalDomain_ne_top (k : ℕ) :
    unipMeasure K n k (unipFundamentalDomain K n k) ≠ ∞ := by
  rw [unipMeasure_unipFundamentalDomain]
  exact ENNReal.one_ne_top

instance isNegInvariant_unipMeasure (k : ℕ) : (unipMeasure K n k).IsNegInvariant := by
  let φ : (UPos n k → 𝔸[K]) ≃ₜ+ (UPos n k → 𝔸[K]) :=
    { AddEquiv.neg (UPos n k → 𝔸[K]) with
      continuous_toFun := continuous_neg
      continuous_invFun := continuous_neg }
  have h := measurePreserving_of_mapsTo_lattice (unipMeasure K n k)
    isAddFundamentalDomain_unipFundamentalDomain measurableSet_unipFundamentalDomain
    (unipMeasure_unipFundamentalDomain_ne_zero k) (unipMeasure_unipFundamentalDomain_ne_top k) φ
    (fun ξ hξ => (unipLattice K n k).neg_mem hξ) (fun ξ hξ => (unipLattice K n k).neg_mem hξ)
  exact ⟨h.map_eq⟩

theorem unipOne_injective (k : ℕ) : Injective (unipOne K n k) := fun _ _ h =>
  unipGL_injective (congrArg Subtype.val h)

variable (K n) in

def ratOne : GL (Fin n) K →* normOneGL K n :=
  (AdelicGLn.diagonal K n).codRestrict (normOneGL K n)
    (fun γ => rationalGL_le_normOneGL ⟨γ, rfl⟩)

@[simp] theorem coe_ratOne (γ : GL (Fin n) K) :
    ((ratOne K n γ : normOneGL K n) : AdelicGLn.AdelicGL K n) = AdelicGLn.diagonal K n γ := rfl

theorem ratOne_injective : Injective (ratOne K n) := fun _ _ h =>
  AdelicGLn.diagonal_injective K n (congrArg Subtype.val h)

theorem mem_rationalGLOne_iff {x : normOneGL K n} : x ∈ rationalGLOne K n ↔ ∃ γ, ratOne K n γ = x := by
  constructor
  · rintro ⟨γ, hγ⟩
    exact ⟨γ, Subtype.ext hγ⟩
  · rintro ⟨γ, rfl⟩
    exact ⟨γ, rfl⟩

theorem coe_ratOne_matrix (γ : GL (Fin n) K) :
    (((ratOne K n γ : normOneGL K n) : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) =
      ratMat (γ : Matrix (Fin n) (Fin n) K) :=
  coe_diagonal γ

instance countable_GL : Countable (GL (Fin n) K) := by
  have := GroundTheory.Global.countable_numberField K
  have : Countable (Matrix (Fin n) (Fin n) K) := inferInstanceAs (Countable (Fin n → Fin n → K))
  exact Function.Injective.countable (f := fun γ : GL (Fin n) K => (γ : Matrix (Fin n) (Fin n) K))
    Units.val_injective

variable (K n) in

def parabolicOne (k : ℕ) : Subgroup (normOneGL K n) :=
  (parabolic (K := K) (n := n) k).map (ratOne K n)

theorem parabolicOne_le (k : ℕ) : parabolicOne K n k ≤ rationalGLOne K n := by
  rintro _ ⟨γ, -, rfl⟩
  exact mem_rationalGLOne_iff.2 ⟨γ, rfl⟩

instance countable_parabolicOne (k : ℕ) : Countable (parabolicOne K n k) := by
  have : ((parabolicOne K n k : Set (normOneGL K n))).Countable := by
    rw [parabolicOne, Subgroup.coe_map]
    exact (Set.countable_univ.mono (Set.subset_univ _)).image _
  exact this.to_subtype

instance discreteTopology_parabolicOne (k : ℕ) : DiscreteTopology (parabolicOne K n k) :=
  DiscreteTopology.of_subset (s := (rationalGLOne K n : Set (normOneGL K n)))
    discreteTopology_rationalGLOne (parabolicOne_le k)

theorem mem_parabolicOne_iff {k : ℕ} {q : normOneGL K n} :
    q ∈ parabolicOne K n k ↔ ∃ p ∈ parabolic (K := K) (n := n) k, ratOne K n p = q :=
  Subgroup.mem_map

theorem mul_blockEntry_mul {R : Type*} [CommRing R] {k : ℕ} {A B : Matrix (Fin n) (Fin n) R}
    (hA : ∀ i a : Fin n, k ≤ (i : ℕ) → (a : ℕ) < k → A i a = 0)
    (hB : ∀ b j : Fin n, k ≤ (b : ℕ) → (j : ℕ) < k → B b j = 0) (Z : UPos n k → R) :
    A * blockEntry Z * B = blockEntry (fun p : UPos n k => (A * blockEntry Z * B) p.1.1 p.1.2) := by
  ext i j
  rw [blockEntry_apply]
  split_ifs with h
  · rfl
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun b _ => ?_
    rw [Matrix.mul_apply]
    by_cases hi : k ≤ (i : ℕ)
    · rw [Finset.sum_eq_zero, zero_mul]
      intro a _
      by_cases ha : (a : ℕ) < k
      · rw [hA i a hi ha, zero_mul]
      · rw [blockEntry_apply, dif_neg (by omega), mul_zero]
    · have hj : (j : ℕ) < k := by omega
      by_cases hb : k ≤ (b : ℕ)
      · rw [hB b j hb hj, mul_zero]
      · rw [Finset.sum_eq_zero, zero_mul]
        intro a _
        rw [blockEntry_apply, dif_neg (by omega), mul_zero]

theorem blockEntry_injective {R : Type*} [CommRing R] {k : ℕ} :
    Injective (blockEntry : (UPos n k → R) → Matrix (Fin n) (Fin n) R) := by
  intro X Y h
  funext p
  have := congrFun (congrFun h p.1.1) p.1.2
  simpa [blockEntry_apply, p.2] using this

theorem entry_eq_zero_of_mem_parabolicOne {k : ℕ} {q : normOneGL K n} (hq : q ∈ parabolicOne K n k)
    {i j : Fin n} (hi : k ≤ (i : ℕ)) (hj : (j : ℕ) < k) :
    (((q : normOneGL K n) : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) i j = 0 := by
  obtain ⟨p, hp, rfl⟩ := mem_parabolicOne_iff.1 hq
  rw [coe_ratOne_matrix]
  simp [ratMat, hp.1 i j hi hj]

def conjUnip (k : ℕ) (q : normOneGL K n) : (UPos n k → 𝔸[K]) →+ (UPos n k → 𝔸[K]) where
  toFun Z p := ((((q⁻¹ : normOneGL K n) : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) *
    blockEntry Z * (((q : normOneGL K n) : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]))
      p.1.1 p.1.2
  map_zero' := by funext p; simp [blockEntry_zero]
  map_add' Z W := by funext p; simp [blockEntry_add, Matrix.mul_add, Matrix.add_mul]

theorem blockEntry_conjUnip {k : ℕ} {q : normOneGL K n} (hq : q ∈ parabolicOne K n k)
    (Z : UPos n k → 𝔸[K]) :
    blockEntry (conjUnip k q Z) =
      (((q⁻¹ : normOneGL K n) : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) *
        blockEntry Z * (((q : normOneGL K n) : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) :=
  (mul_blockEntry_mul (fun _ _ hi ha => entry_eq_zero_of_mem_parabolicOne (inv_mem hq) hi ha)
    (fun _ _ hb hj => entry_eq_zero_of_mem_parabolicOne hq hb hj) Z).symm

theorem coe_inv_mul_coe (q : normOneGL K n) :
    (((q⁻¹ : normOneGL K n) : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) *
      (((q : normOneGL K n) : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) = 1 := by
  rw [← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one, Units.val_one]

theorem coe_mul_coe_inv (q : normOneGL K n) :
    (((q : normOneGL K n) : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) *
      (((q⁻¹ : normOneGL K n) : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) = 1 := by
  rw [← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one, Units.val_one]

theorem conj_unipOne {k : ℕ} {q : normOneGL K n} (hq : q ∈ parabolicOne K n k) (Z : UPos n k → 𝔸[K]) :
    q⁻¹ * unipOne K n k Z * q = unipOne K n k (conjUnip k q Z) := by
  refine Subtype.ext (Units.ext ?_)
  simp only [Subgroup.coe_mul, Units.val_mul, coe_unipOne, coe_unipGL, unipMatrix]
  rw [blockEntry_conjUnip hq, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, coe_inv_mul_coe]

theorem conjUnip_conjUnip_inv {k : ℕ} {q : normOneGL K n} (hq : q ∈ parabolicOne K n k)
    (Z : UPos n k → 𝔸[K]) : conjUnip k q (conjUnip k q⁻¹ Z) = Z := by
  apply blockEntry_injective
  rw [blockEntry_conjUnip hq, blockEntry_conjUnip (inv_mem hq), inv_inv]
  simp only [← Matrix.mul_assoc]
  rw [coe_inv_mul_coe, Matrix.one_mul, Matrix.mul_assoc, coe_inv_mul_coe, Matrix.mul_one]

theorem conjUnip_mem_unipLattice {k : ℕ} {q : normOneGL K n} (hq : q ∈ parabolicOne K n k)
    {ξ : UPos n k → 𝔸[K]} (hξ : ξ ∈ unipLattice K n k) : conjUnip k q ξ ∈ unipLattice K n k := by
  obtain ⟨p, -, rfl⟩ := mem_parabolicOne_iff.1 hq
  obtain ⟨ξ₀, rfl⟩ := hξ
  have hξe : (AddMonoidHom.compLeft (algebraMap K 𝔸[K]).toAddMonoidHom (UPos n k)) ξ₀ =
      fun x => algebraMap K 𝔸[K] (ξ₀ x) := rfl
  rw [hξe]
  have hb : blockEntry (fun x => algebraMap K 𝔸[K] (ξ₀ x)) = ratMat (blockEntry ξ₀) := by
    ext i j
    simp only [blockEntry_apply, ratMat, Matrix.map_apply]
    split_ifs <;> simp
  refine ⟨fun x => ((p⁻¹ : GL (Fin n) K) * blockEntry ξ₀ * (p : GL (Fin n) K) :
    Matrix (Fin n) (Fin n) K) x.1.1 x.1.2, funext fun x => ?_⟩
  show algebraMap K 𝔸[K] _ = conjUnip k (ratOne K n p) (fun x => algebraMap K 𝔸[K] (ξ₀ x)) x
  have e : conjUnip k (ratOne K n p) (fun x => algebraMap K 𝔸[K] (ξ₀ x)) x =
      (ratMat ((p⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * ratMat (blockEntry ξ₀) *
        ratMat ((p : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) x.1.1 x.1.2 := by
    show ((((ratOne K n p)⁻¹ : normOneGL K n) : AdelicGLn.AdelicGL K n) * _ * _ :
      Matrix (Fin n) (Fin n) 𝔸[K]) x.1.1 x.1.2 = _
    rw [← map_inv, coe_ratOne_matrix, coe_ratOne_matrix, hb]
  rw [e, ← ratMat_mul, ← ratMat_mul]
  rfl

theorem continuous_conjUnip (k : ℕ) (q : normOneGL K n) : Continuous (conjUnip (K := K) k q) := by
  refine continuous_pi fun p => ?_
  have hb : Continuous (blockEntry : (UPos n k → 𝔸[K]) → Matrix (Fin n) (Fin n) 𝔸[K]) := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    simp only [blockEntry_apply]
    split_ifs
    · exact continuous_apply _
    · exact continuous_const
  set A₀ : Matrix (Fin n) (Fin n) 𝔸[K] :=
    (((q⁻¹ : normOneGL K n) : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K])
  set B₀ : Matrix (Fin n) (Fin n) 𝔸[K] :=
    (((q : normOneGL K n) : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K])
  have hm : Continuous (fun Z : UPos n k → 𝔸[K] => A₀ * blockEntry Z * B₀) :=
    ((continuous_const : Continuous fun _ : UPos n k → 𝔸[K] => A₀).matrix_mul hb).matrix_mul
      continuous_const
  exact (continuous_apply p.1.2).comp ((continuous_apply p.1.1).comp hm)

def conjUnipEquiv {k : ℕ} {q : normOneGL K n} (hq : q ∈ parabolicOne K n k) :
    (UPos n k → 𝔸[K]) ≃ₜ+ (UPos n k → 𝔸[K]) where
  toFun := conjUnip k q
  invFun := conjUnip k q⁻¹
  left_inv Z := by
    have := conjUnip_conjUnip_inv (inv_mem hq) Z
    rwa [inv_inv] at this
  right_inv Z := conjUnip_conjUnip_inv hq Z
  map_add' := (conjUnip k q).map_add
  continuous_toFun := continuous_conjUnip k q
  continuous_invFun := continuous_conjUnip k q⁻¹

theorem measurePreserving_conjUnip {k : ℕ} {q : normOneGL K n} (hq : q ∈ parabolicOne K n k) :
    MeasurePreserving (conjUnip k q) (unipMeasure K n k) (unipMeasure K n k) :=
  measurePreserving_of_mapsTo_lattice (unipMeasure K n k) isAddFundamentalDomain_unipFundamentalDomain
    measurableSet_unipFundamentalDomain (unipMeasure_unipFundamentalDomain_ne_zero k)
    (unipMeasure_unipFundamentalDomain_ne_top k) (conjUnipEquiv hq)
    (fun _ h => conjUnip_mem_unipLattice hq h) (fun _ h => conjUnip_mem_unipLattice (inv_mem hq) h)

omit [NumberField K] in
theorem isBlockUpper_unipMatrix {k : ℕ} (X : UPos n k → K) : IsBlockUpper k (unipMatrix X) := by
  intro i j hi hj
  simp only [unipMatrix, Matrix.add_apply, blockEntry_apply]
  rw [Matrix.one_apply, if_neg (by intro h; subst h; omega), dif_neg (by omega), add_zero]

theorem unipOne_mem_parabolicOne {k : ℕ} {ξ : UPos n k → 𝔸[K]} (hξ : ξ ∈ unipLattice K n k) :
    unipOne K n k ξ ∈ parabolicOne K n k := by
  obtain ⟨ξ₀, rfl⟩ := hξ
  refine mem_parabolicOne_iff.2 ⟨unipGL ξ₀, ⟨?_, ?_⟩, Subtype.ext (diagonal_unipGL ξ₀)⟩
  · rw [coe_unipGL]
    exact isBlockUpper_unipMatrix ξ₀
  · rw [coe_unipGL_inv]
    exact isBlockUpper_unipMatrix (-ξ₀)

theorem hyp (k : ℕ) :
    Unfold.Hyp (unipMeasure K n k) (unipOne K n k) (unipLattice K n k) (unipFundamentalDomain K n k)
      (parabolicOne K n k) (fundamentalDomain (parabolicOne K n k)) (conjUnip k) where
  map_add := unipOne_add k
  injective := unipOne_injective k
  measurable := (continuous_unipOne k).measurable
  isAddFundamentalDomain := isAddFundamentalDomain_unipFundamentalDomain
  measurableSet_D := measurableSet_unipFundamentalDomain
  measurableSet_E := measurableSet_fundamentalDomain _
  existsUnique := existsUnique_smul_mem_fundamentalDomain _
  mem := fun _ hξ => unipOne_mem_parabolicOne hξ
  conj := fun _ hq Z => conj_unipOne hq Z
  mapsTo := fun _ hq _ hξ => conjUnip_mem_unipLattice hq hξ
  measurePreserving := fun _ hq => measurePreserving_conjUnip hq

end UnfoldGL

end

end GroundTheory.Automorphic.GJGlobal
