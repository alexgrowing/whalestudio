import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.CommonModel
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.GalOfCusp TensorProduct Module
open UpperTheory.Gal.crystallineComparison

private theorem step_fix (hco : CoFacts) {F L B : Type} [Field F] [Field L] [Algebra F L] [CommRing B] [Algebra F B] {a : ℕ}
    (x : Fin a → (Fin a → L) ⊗[F] B) (y : (Fin 1 → L) ⊗[F] B)
    (hy : co y 0 = Matrix.det (Matrix.of fun i k => co (x k) i))
    (T : End L (Fin a → L)) (A : Matrix (Fin a) (Fin a) L) (hT : ∀ v, T v = A.mulVec v)
    (T' : End L (Fin 1 → L)) (A' : Matrix (Fin 1) (Fin 1) L) (hT' : ∀ v, T' v = A'.mulVec v)
    (hdet : A'.det = A.det) (s : B →ₐ[F] B)
    (hfix : ∀ k, AlgebraTensorModule.map T s.toLinearMap (x k) = x k) :
    AlgebraTensorModule.map T' s.toLinearMap y = y := by
  obtain ⟨-, -, -, hmap, -⟩ := hco F L B a
  obtain ⟨-, -, -, hmap', hbij⟩ := hco F L B 1
  set D : Matrix (Fin a) (Fin a) (L ⊗[F] B) := Matrix.of fun i k => co (x k) i with hD
  have hM : D = A.map (algebraMap L (L ⊗[F] B)) * D.map (onR L s) := by
    ext i k
    have h1 := congrFun (hmap T A hT s (x k)) i
    rw [hfix k] at h1
    simpa [D, Matrix.mul_apply, Matrix.mulVec, dotProduct] using h1
  have key : D.det = algebraMap L (L ⊗[F] B) A.det * onR L s D.det := by
    conv_lhs => rw [hM]
    rw [Matrix.det_mul, RingHom.map_det, RingHom.map_det]
    rfl
  apply hbij.1
  have h1 := congrFun (hmap' T' A' hT' s y) 0
  have h3 : A' 0 0 = A.det := by rw [← hdet, Matrix.det_fin_one]
  show co _ 0 = co y 0
  rw [h1, hy]
  conv_rhs => rw [key]
  simp [Matrix.mulVec, dotProduct, h3, hy]

private theorem one_ext {l : ℕ} [Fact l.Prime] (P : LocPrime l) {K LL : FinExt l} {V : Type} [AddCommGroup V] [Module ↥LL.1 V]
    [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V) {a : ℕ} (x : Fin a → ↥(Dpst P ρ)) :
    ∃ K' : FinExt l, ∀ k, ∀ g : ↥(GK K), (g : GQ l) ∈ GK K' → stRep P ρ g (x k : V ⊗[ℚ_[l]] Bst P) = x k := by
  have hs : ∀ s : Finset (Fin a), ∃ K' : FinExt l, ∀ k ∈ s, ∀ g : ↥(GK K), (g : GQ l) ∈ GK K' →
      stRep P ρ g (x k : V ⊗[ℚ_[l]] Bst P) = x k := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨K, by simp⟩
    | insert k s hk ih =>
      obtain ⟨K₁, h₁⟩ := ih
      obtain ⟨K₂, h₂⟩ := (mem_Dpst P ρ).mp (x k).2
      refine ⟨supExt K₁ K₂, fun k' hk' g hg => ?_⟩
      rcases Finset.mem_insert.mp hk' with rfl | hk'
      · exact h₂ g (GK_le (K' := supExt K₁ K₂) le_sup_right hg)
      · exact h₁ k' hk' g (GK_le (K' := supExt K₁ K₂) le_sup_left hg)
  obtain ⟨K', h⟩ := hs Finset.univ
  exact ⟨K', fun k => h k (Finset.mem_univ k)⟩

theorem UpperTheory.Gal.crystallineComparison.detMem_of :
    CoFacts → DetMem := by
  intro hco l _ P K LL a ρ ρ' A A' hA hA' hdet x
  obtain ⟨K', hK'⟩ := one_ext P ρ x
  obtain ⟨y, hy⟩ := (hco ℚ_[l] ↥LL.1 (Bst P) 1).2.2.2.2.2
    (Matrix.det (Matrix.of fun i k => co (x k : (Fin a → ↥LL.1) ⊗[ℚ_[l]] Bst P) i))
  exact ⟨⟨y, (mem_Dpst P ρ').mpr ⟨K', fun g hg =>
    step_fix hco (fun k => (x k : (Fin a → ↥LL.1) ⊗[ℚ_[l]] Bst P)) y hy (ρ g) (A g) (hA g) (ρ' g) (A' g) (hA' g)
      (hdet g) (actSt P (g : GQ l)) fun k => hK' k g hg⟩⟩, hy⟩
