import Formalism.WachLatticeTwists.RamifiedBlockRings.Statement

open Finset Classical

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.ringDataObjects

open Formalism.NG Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities

theorem densityMod (k A : Type*) [Field k] [Ring A] [Algebra k A] {ι : Type*} [Fintype ι]
    (V : ι → Type*) [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)] [∀ i, Module A (V i)]
    [∀ i, IsScalarTower k A (V i)] [∀ i, FiniteDimensional k (V i)]
    (hS : ∀ i, IsSemisimpleModule A (V i))
    (hsc : ∀ i, ∀ φ : V i →ₗ[A] V i, ∃ c : k, ∀ v, φ v = c • v)
    (hz : ∀ i j, i ≠ j → ∀ φ : V j →ₗ[A] V i, φ = 0)
    (f : ∀ i, V i →ₗ[k] V i) : ∃ a : A, ∀ i v, a • v = f i v := by
  have hφ : ∀ φ : Module.End A (∀ i, V i), ∃ c : ι → k, ∀ w i, φ w i = c i • w i := by
    intro φ
    choose c hc using fun i => hsc i ((LinearMap.proj i).comp (φ.comp (LinearMap.single A V i)))
    refine ⟨c, fun w i => ?_⟩
    have hw : w = ∑ j, Pi.single j (w j) := (Finset.univ_sum_single w).symm
    conv_lhs => rw [hw]
    rw [map_sum, Finset.sum_apply, Finset.sum_eq_single i]
    · exact hc i (w i)
    · intro j _ hj
      have := LinearMap.congr_fun
        (hz i j (Ne.symm hj) ((LinearMap.proj i).comp (φ.comp (LinearMap.single A V j)))) (w j)
      exact this
    · intro h; exact absurd (Finset.mem_univ i) h
  let F : Module.End (Module.End A (∀ i, V i)) (∀ i, V i) :=
    { toFun := fun w i => f i (w i)
      map_add' := fun w w' => by funext i; simp
      map_smul' := fun φ w => by
        obtain ⟨c, hc⟩ := hφ φ
        funext i
        simp only [Module.End.smul_def, RingHom.id_apply, hc, (f i).map_smul] }
  obtain ⟨a, ha⟩ := jacobson_density F (Finset.univ.image (Module.finBasis k (∀ i, V i)))
  let F' : (∀ i, V i) →ₗ[k] (∀ i, V i) := LinearMap.pi fun i => (f i).comp (LinearMap.proj i)
  have hEq : DistribSMul.toLinearMap k (∀ i, V i) a = F' := by
    refine (Module.finBasis k (∀ i, V i)).ext fun b => ?_
    have := ha (Module.finBasis k (∀ i, V i) b) (Finset.mem_image_of_mem _ (Finset.mem_univ b))
    exact this.symm
  refine ⟨a, fun i v => ?_⟩
  have := congrFun (LinearMap.congr_fun hEq (Pi.single i v)) i
  simpa [F'] using this

theorem toSquareBlock_mul_of_diag {K : Type*} [CommRing K] {d : Type*} [Fintype d] [DecidableEq d]
    {m : ℕ} (c : d → Fin m) (M N : Matrix d d K) (hM : ∀ a b, c a ≠ c b → M a b = 0) (i : Fin m) :
    (M * N).toSquareBlock c i = M.toSquareBlock c i * N.toSquareBlock c i := by
  ext ⟨a, ha⟩ ⟨b, hb⟩
  simp only [Matrix.toSquareBlock_def, Matrix.of_apply, Matrix.mul_apply]
  rw [← Finset.sum_subtype (Finset.univ.filter fun x => c x = i) (by simp)
    (fun x => M a x * N x b)]
  symm
  refine Finset.sum_subset (Finset.subset_univ _) fun x _ hx => ?_
  have hx' : c x ≠ i := by simpa using hx
  rw [hM a x (by rw [ha]; exact Ne.symm hx'), zero_mul]

theorem density : StatDensity := by
  intro K _ d _ _ G _ ρ m c P hG B hB
  obtain ⟨hP, hdiag, hirr, hint⟩ := hG
  have hdet : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hP
  have hPP : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hdet
  have hP'P : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hdet

  let σ : G →* Matrix d d K :=
    { toFun := fun g => P * ρ g * P⁻¹
      map_one' := by rw [map_one, Matrix.mul_one, hPP]
      map_mul' := fun g h => by
        have : P * ρ g * P⁻¹ * (P * ρ h * P⁻¹) = P * ρ g * (P⁻¹ * P) * ρ h * P⁻¹ := by
          simp only [Matrix.mul_assoc]
        rw [this, hP'P, Matrix.mul_one, map_mul]
        simp only [Matrix.mul_assoc] }
  have hσ : ∀ g, σ g = P * ρ g * P⁻¹ := fun g => rfl

  let τ : ∀ i : Fin m, G →* Matrix {a // c a = i} {a // c a = i} K := fun i =>
    { toFun := fun g => (σ g).toSquareBlock c i
      map_one' := by
        rw [map_one]
        ext ⟨a, ha⟩ ⟨b, hb⟩
        simp [Matrix.toSquareBlock_def, Matrix.one_apply]
      map_mul' := fun g h => by
        rw [map_mul]
        exact toSquareBlock_mul_of_diag c _ _ (hdiag g) i }
  have hτ : ∀ i g, τ i g = (P * ρ g * P⁻¹).toSquareBlock c i := fun i g => rfl
  let A := MonoidAlgebra K G
  let V : Fin m → Type _ := fun i => {a // c a = i} → K
  let L : A →ₐ[K] Matrix d d K := MonoidAlgebra.lift K (Matrix d d K) G σ
  let Lb : ∀ i, A →ₐ[K] Matrix {a // c a = i} {a // c a = i} K := fun i =>
    MonoidAlgebra.lift K _ G (τ i)
  have hof : ∀ g, L (MonoidAlgebra.of K G g) = σ g := fun g => MonoidAlgebra.lift_of σ g
  have hofb : ∀ i g, Lb i (MonoidAlgebra.of K G g) = τ i g := fun i g => MonoidAlgebra.lift_of (τ i) g
  let _ : ∀ i, AddCommGroup (V i) := fun i => inferInstanceAs (AddCommGroup ({a // c a = i} → K))
  let _ : ∀ i, Module K (V i) := fun i => inferInstanceAs (Module K ({a // c a = i} → K))
  have : ∀ i, FiniteDimensional K (V i) := fun i =>
    inferInstanceAs (FiniteDimensional K ({a // c a = i} → K))
  let _ : ∀ i, Module A (V i) := fun i => Module.compHom (V i)
    ((Matrix.toLinAlgEquiv' : Matrix {a // c a = i} {a // c a = i} K ≃ₐ[K] _).toAlgHom.comp
      (Lb i)).toRingHom
  have hact : ∀ i (a : A) (v : V i), a • v = (Lb i a).mulVec v := fun i a v => rfl
  have : ∀ i, IsScalarTower K A (V i) := fun i => ⟨fun x a v => by
    rw [hact, hact, map_smul, Matrix.smul_mulVec]⟩
  have hS : ∀ i, IsSemisimpleModule A (V i) := by
    intro i
    rcases isEmpty_or_nonempty {a // c a = i} with hn | hn
    · have : Subsingleton (V i) := inferInstanceAs (Subsingleton ({a // c a = i} → K))
      have : Subsingleton (Submodule A (V i)) := inferInstance
      exact (isSemisimpleModule_iff A (V i)).mpr Subsingleton.instComplementedLattice
    · have : Nontrivial (Submodule A (V i)) := by
        refine ⟨⊥, ⊤, fun h => ?_⟩
        have h2 : (fun _ : {a // c a = i} => (1 : K)) ∈ (⊤ : Submodule A (V i)) := Submodule.mem_top
        rw [← h, Submodule.mem_bot] at h2
        exact one_ne_zero (congrFun h2 (Classical.arbitrary _))
      suffices hso : IsSimpleOrder (Submodule A (V i)) from
        have := @IsSimpleModule.mk _ _ _ _ _ hso
        inferInstance
      refine ⟨fun W => ?_⟩
      rcases (hirr i).1 (W.restrictScalars K) (fun g v hv => by
        have := W.smul_mem (MonoidAlgebra.of K G g) hv
        rw [hact, hofb] at this
        exact this) with h | h
      · left; exact (Submodule.restrictScalars_eq_bot_iff K A (V i)).mp h
      · right; exact (Submodule.restrictScalars_eq_top_iff K A (V i)).mp h

  have hmat : ∀ i j (ψ : V j →ₗ[A] V i), ∃ M : Matrix {a // c a = i} {a // c a = j} K,
      (∀ v, M.mulVec v = ψ v) ∧ ∀ g, M * τ j g = τ i g * M := by
    intro i j ψ
    let M : Matrix {a // c a = i} {a // c a = j} K := LinearMap.toMatrix' (ψ.restrictScalars K)
    have hM : ∀ v, M.mulVec v = ψ v := fun v => by
      simp [M]
    refine ⟨M, hM, fun g => ?_⟩
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun v => ?_
    simp only [Matrix.toLin'_apply, ← Matrix.mulVec_mulVec]
    rw [hM, hM, ← hofb, ← hofb, ← hact, ← hact, map_smul]
  have hsc : ∀ i, ∀ ψ : V i →ₗ[A] V i, ∃ x : K, ∀ v, ψ v = x • v := by
    intro i ψ
    obtain ⟨M, hM, hMg⟩ := hmat i i ψ
    obtain ⟨x, hx⟩ := (hirr i).2 M hMg
    refine ⟨x, fun v => ?_⟩
    rw [← hM, hx, Matrix.smul_mulVec, Matrix.one_mulVec]
  have hz : ∀ i j, i ≠ j → ∀ ψ : V j →ₗ[A] V i, ψ = 0 := by
    intro i j hij ψ
    obtain ⟨M, hM, hMg⟩ := hmat i j ψ
    have h0 := hint i j hij M hMg
    refine LinearMap.ext fun v => ?_
    rw [← hM, h0, Matrix.zero_mulVec]
    rfl
  obtain ⟨a, ha⟩ := densityMod K A V hS hsc hz
    (fun i => Matrix.toLin' ((P * B * P⁻¹).toSquareBlock c i))

  have hLdiag : ∀ a : A, (∀ x y, c x ≠ c y → L a x y = 0) ∧
      ∀ i, (L a).toSquareBlock c i = Lb i a := by
    intro a
    refine MonoidAlgebra.induction_on (motive := fun a => (∀ x y, c x ≠ c y → L a x y = 0) ∧
      ∀ i, (L a).toSquareBlock c i = Lb i a) a ?_ ?_ ?_
    · intro g
      refine ⟨fun x y hxy => ?_, fun i => ?_⟩
      · rw [hof]; exact hdiag g x y hxy
      · rw [hof, hofb]; rfl
    · intro f g hf hg
      refine ⟨fun x y hxy => ?_, fun i => ?_⟩
      · rw [map_add, Matrix.add_apply, hf.1 x y hxy, hg.1 x y hxy, add_zero]
      · rw [map_add, map_add, ← hf.2 i, ← hg.2 i]; rfl
    · intro x f hf
      refine ⟨fun y z hyz => ?_, fun i => ?_⟩
      · rw [map_smul, Matrix.smul_apply, hf.1 y z hyz, smul_zero]
      · rw [map_smul, map_smul, ← hf.2 i]; rfl
  have hLa : L a = P * B * P⁻¹ := by
    have hb : ∀ i, Lb i a = (P * B * P⁻¹).toSquareBlock c i := by
      intro i
      apply Matrix.toLin'.injective
      refine LinearMap.ext fun v => ?_
      rw [Matrix.toLin'_apply, ← ha i v, hact]
    ext x y
    by_cases hxy : c x = c y
    · have := congrFun (congrFun (((hLdiag a).2 (c y)).trans (hb (c y))) ⟨x, hxy⟩) ⟨y, rfl⟩
      exact this
    · rw [(hLdiag a).1 x y hxy, hB x y hxy]
  have hspan : ∀ a : A, P⁻¹ * L a * P ∈ Submodule.span K (Set.range ρ) := by
    intro a
    refine MonoidAlgebra.induction_on
      (motive := fun a => P⁻¹ * L a * P ∈ Submodule.span K (Set.range ρ)) a ?_ ?_ ?_
    · intro g
      have : P⁻¹ * L (MonoidAlgebra.of K G g) * P = ρ g := by
        rw [hof, hσ]
        have : P⁻¹ * (P * ρ g * P⁻¹) * P = (P⁻¹ * P) * ρ g * (P⁻¹ * P) := by
          simp only [Matrix.mul_assoc]
        rw [this, hP'P, Matrix.one_mul, Matrix.mul_one]
      rw [this]; exact Submodule.subset_span ⟨g, rfl⟩
    · intro f g hf hg
      rw [map_add, Matrix.mul_add, Matrix.add_mul]; exact Submodule.add_mem _ hf hg
    · intro x f hf
      rw [map_smul, Matrix.mul_smul, Matrix.smul_mul]; exact Submodule.smul_mem _ _ hf
  have hfin : B = P⁻¹ * L a * P := by
    rw [hLa]
    have : P⁻¹ * (P * B * P⁻¹) * P = (P⁻¹ * P) * B * (P⁻¹ * P) := by
      simp only [Matrix.mul_assoc]
    rw [this, hP'P, Matrix.one_mul, Matrix.mul_one]
  rw [hfin]
  exact hspan a

end Formalism.RepresentationBoundsCohomology.ringDataObjects
