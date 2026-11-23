import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelExistsUniqueAct
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelEigenvectorsActionStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModelBaseChangeStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat
open TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.EigBase

section Linear

variable {O F F' V T : Type} [CommRing O] [Field F] [Field F'] [Algebra F F'] [AddCommGroup V] [Module F V]
  [AddCommGroup T] [Module F' T] [Module F T] [IsScalarTower F F' T]

theorem mem_eigSp {R E : Type} [CommRing R] [AddCommGroup E] [Module R E] (ρ : O →+* Module.End R E) (σ : O →+* R)
    (u : E) : u ∈ eigSp ρ σ ↔ ∀ a, ρ a u = σ a • u := by
  simp [eigSp, Submodule.mem_iInf, LinearMap.mem_ker, sub_eq_zero]

theorem linearIndependent_base {j : V →ₗ[F] T} (hj : IsBaseChange F' j) {n : ℕ} {u : Fin n → V}
    (hu : LinearIndependent F u) : LinearIndependent F' fun i => j (u i) := by
  have hs : LinearIndepOn F id (Set.range u) := hu.linearIndepOn_id
  let b := Module.Basis.extend hs
  let g : Fin n → (hs.extend (Set.subset_univ _)) := fun i => ⟨u i, hs.subset_extend _ ⟨i, rfl⟩⟩
  have hg : Function.Injective g := fun a c e => hu.injective (congrArg Subtype.val e)
  have e : (fun i => j (u i)) = (hj.basis b) ∘ g := by
    funext i
    simp [IsBaseChange.basis_apply, b, g]
  rw [e]
  exact (hj.basis b).linearIndependent.comp g hg

theorem equiv_baseChange {j : V →ₗ[F] T} (hj : IsBaseChange F' j) {ρ : O →+* Module.End F V}
    {ρ' : O →+* Module.End F' T} (σ : O →+* F) (hact : ∀ a e, ρ' a (j e) = j (ρ a e)) (a : O) (y : F' ⊗[F] V) :
    hj.equiv (LinearMap.baseChange F' (ρ a - σ a • LinearMap.id) y) =
      ρ' a (hj.equiv y) - algebraMap F F' (σ a) • hj.equiv y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul c w =>
    rw [LinearMap.baseChange_tmul, hj.equiv_tmul, hj.equiv_tmul, map_smul, hact, smul_comm (algebraMap F F' (σ a)) c,
      ← smul_sub]
    congr 1
    simp [algebraMap_smul]
  | add y z hy hz =>
    simp only [map_add, hy, hz, smul_add]
    abel

theorem exists_sum_of_mem_eigSp {j : V →ₗ[F] T} (hj : IsBaseChange F' j) {ρ : O →+* Module.End F V}
    {ρ' : O →+* Module.End F' T} (σ : O →+* F) (hact : ∀ a e, ρ' a (j e) = j (ρ a e)) {t : T}
    (ht : t ∈ eigSp ρ' ((algebraMap F F').comp σ)) :
    ∃ (J : Type) (B : J → F') (b : J →₀ V), (∀ k, b k ∈ eigSp ρ σ) ∧ t = b.sum fun k w => B k • j w := by
  classical
  let B := Module.Basis.ofVectorSpace F F'
  obtain ⟨b, hb⟩ := TensorProduct.eq_repr_basis_left B (hj.equiv.symm t)
  refine ⟨_, B, b, fun k => (mem_eigSp ρ σ _).2 fun a => ?_, ?_⟩
  · obtain ⟨A, hA⟩ : ∃ A : V →ₗ[F] V, A = ρ a - σ a • LinearMap.id := ⟨_, rfl⟩
    have h0 : LinearMap.baseChange F' A (hj.equiv.symm t) = 0 := by
      apply hj.equiv.injective
      rw [hA, equiv_baseChange hj σ hact, LinearEquiv.apply_symm_apply, map_zero]
      exact sub_eq_zero.2 ((mem_eigSp ρ' _ t).1 ht a)
    rw [← hb, map_finsuppSum] at h0
    simp only [LinearMap.baseChange_tmul] at h0
    have h1 : (b.mapRange A (map_zero A)).sum (fun i n => B i ⊗ₜ[F] n) = 0 := by
      rw [Finsupp.sum_mapRange_index (by simp)]
      exact h0
    have h2 := TensorProduct.sum_tmul_basis_left_eq_zero B _ h1
    have h3 := DFunLike.congr_fun h2 k
    simpa [hA, sub_eq_zero] using h3
  · rw [← hj.equiv.apply_symm_apply t, ← hb, map_finsuppSum]
    simp [hj.equiv_tmul]

theorem frame_base {j : V →ₗ[F] T} (hj : IsBaseChange F' j) {ρ : O →+* Module.End F V}
    {ρ' : O →+* Module.End F' T} (σ : O →+* F) (hact : ∀ a e, ρ' a (j e) = j (ρ a e)) {n : ℕ} {u : Fin n → V}
    (hu : LinearIndependent F u) (hs : Submodule.span F (Set.range u) = eigSp ρ σ) :
    LinearIndependent F' (fun i => j (u i)) ∧
      Submodule.span F' (Set.range fun i => j (u i)) = eigSp ρ' ((algebraMap F F').comp σ) := by
  refine ⟨linearIndependent_base hj hu, le_antisymm (Submodule.span_le.2 ?_) fun t ht => ?_⟩
  · rintro _ ⟨i, rfl⟩
    have hi : u i ∈ eigSp ρ σ := hs ▸ Submodule.subset_span ⟨i, rfl⟩
    refine (mem_eigSp ρ' _ _).2 fun a => ?_
    rw [hact, (mem_eigSp ρ σ _).1 hi a, map_smul]
    simp [algebraMap_smul]
  · obtain ⟨J, B, b, hb, rfl⟩ := exists_sum_of_mem_eigSp hj σ hact ht
    have key : ∀ w ∈ Submodule.span F (Set.range u),
        j w ∈ Submodule.span F' (Set.range fun i => j (u i)) := fun w hw => by
      induction hw using Submodule.span_induction with
      | mem w hw =>
        obtain ⟨i, rfl⟩ := hw
        exact Submodule.subset_span ⟨i, rfl⟩
      | zero => simp
      | add w z _ _ hw hz =>
        rw [map_add]
        exact Submodule.add_mem _ hw hz
      | smul c w _ hw =>
        rw [map_smul, ← algebraMap_smul F' c]
        exact Submodule.smul_mem _ _ hw
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (key _ (hs ▸ hb k))

end Linear

theorem eigFrame_base {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] [Smooth G.hom] {F F' : Type} [Field F]
    [Field F'] [Algebra F F'] (x : Sp F ⟶ S) {P : Type} [CommRing P] (act : OAct P G) (σ : P →+* F) {n : ℕ}
    (v : Fin n → (epsAt x ⟶ G)) (v' : Fin n → (epsAt (spMap (algebraMap F F') ≫ x) ⟶ G))
    (hv : ∀ i, (v' i).left = spMap (dualMap (algebraMap F F')) ≫ (v i).left) (h : IsEigFrame act x σ v) :
    IsEigFrame act (spMap (algebraMap F F') ≫ x) ((algebraMap F F').comp σ) v' := by
  obtain ⟨V, _, _, ⟨M⟩⟩ := lieModel_exists S G F x
  obtain ⟨T, _, _, _, _, M', j, hl, hj⟩ := GlobalTheory.T.exists_lie_model_base_change S G F F' x V M
  obtain ⟨ρ, hρ, -⟩ := lieModel_exists_unique_act S G F x V M P act.act act.hom act.one act.mul act.add
  obtain ⟨ρ', hρ', -⟩ := lieModel_exists_unique_act S G F' _ T M' P act.act act.hom act.one act.mul act.add
  have hl' : ∀ e, (M'.pt (j e)).left = spMap (dualMap (algebraMap F F')) ≫ (M.pt e).left := fun e => by
    have := hl e
    simpa [LieModel.Lifts] using this
  have hact : ∀ a e, ρ' a (j e) = j (ρ a e) := fun a e => M'.inj (Over.OverMorphism.ext (by
    rw [hρ' a (j e), Over.comp_left, hl', hl', hρ a e, Over.comp_left, Category.assoc]))
  choose u hu using fun i => M.onto (v i) (h.1 i).1
  obtain rfl : (fun k => M.pt (u k)) = v := funext hu
  obtain ⟨-, hf⟩ := GlobalTheory.T.lie_model_eigenvectors_action S F G x V M
  obtain ⟨hli, hsp⟩ := ((hf P act ρ σ hρ).2 n u).1 h
  have hvv : v' = fun k => M'.pt (j (u k)) := funext fun k => Over.OverMorphism.ext (by rw [hv k, hl'])
  rw [hvv]
  exact (((GlobalTheory.T.lie_model_eigenvectors_action S F' G _ T M').2 P act ρ' _ hρ').2 n _).2 (frame_base hj σ hact hli hsp)

theorem isEigFrame_base : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (F : Type) [Field F] (x : Sp F ⟶ S) [Smooth G.hom] (P : Type) [CommRing P] (act : OAct P G) (σ : P →+* F) (F' : Type) [Field F'] (f : F →+* F') (x' : Sp F' ⟶ S), spMap f ≫ x = x' → ∀ (n : ℕ) (v : Fin n → (epsAt x ⟶ G)) (v' : Fin n → (epsAt x' ⟶ G)), (∀ i, (v' i).left = spMap (dualMap f) ≫ (v i).left) → IsEigFrame act x σ v → IsEigFrame act x' (f.comp σ) v' := by
  intro S G _ _ F _ x _ P _ act σ F' _ f x' hx n v v' hv h
  letI := f.toAlgebra
  subst hx
  exact eigFrame_base x act σ v v' hv h

end GlobalTheory.CompanionTheory.Ar.EigBase
