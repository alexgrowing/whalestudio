import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
import Formalism.LocalToGlobal.ProjectiveLattices.ParCanon
import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
import Formalism.LocalToGlobal.ProjectiveLattices.ValSetAlgSubset
import Formalism.LocalToGlobal.ProjectiveLattices.IntAll
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import Formalism.LocalToGlobal.ProjectiveLattices.VolProofs
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member

namespace GlobalTheory.Member.RatElt

theorem hform_eq {A : Type} [CommRing A] {n : ℕ} (σ : A →+* A) (J : Matrix (Fin n) (Fin n) A) (x y : Fin n → A) :
    Formalism.UG.hform σ J x y = (σ ∘ x) ⬝ᵥ (J *ᵥ y) := by
  simp [Formalism.UG.hform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

theorem hform_mulVec {A : Type} [CommRing A] {n : ℕ} (σ : A →+* A) (J g : Matrix (Fin n) (Fin n) A)
    (x y : Fin n → A) :
    Formalism.UG.hform σ J (g *ᵥ x) (g *ᵥ y) = Formalism.UG.hform σ (Formalism.UG.cT σ g * J * g) x y := by
  have h : σ ∘ (g *ᵥ x) = (g.map σ) *ᵥ (σ ∘ x) := by
    funext i; exact RingHom.map_mulVec σ g x i
  rw [hform_eq, hform_eq, h, Formalism.UG.cT, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec (σ ∘ x) (g.map σ)ᵀ, Matrix.vecMul_transpose]

theorem hform_single {A : Type} [CommRing A] {n : ℕ} (σ : A →+* A) (J : Matrix (Fin n) (Fin n) A) (i j : Fin n) :
    Formalism.UG.hform σ J (Pi.single i 1) (Pi.single j 1) = J i j := by
  have h : σ ∘ (Pi.single i 1 : Fin n → A) = Pi.single i 1 := by
    funext k; by_cases hk : k = i
    · subst hk; simp
    · simp [Pi.single_eq_of_ne hk]
  rw [hform_eq, h]; simp

theorem mem_UJ_iff {A : Type} [CommRing A] {n : ℕ} (σ : A →+* A) (J : Matrix (Fin n) (Fin n) A)
    (g : GL (Fin n) A) :
    g ∈ Formalism.UG.UJ σ J ↔ ∀ x y, Formalism.UG.hform σ J ((g : Matrix (Fin n) (Fin n) A) *ᵥ x)
      ((g : Matrix (Fin n) (Fin n) A) *ᵥ y) = Formalism.UG.hform σ J x y := by
  change Formalism.UG.cT σ (g : Matrix (Fin n) (Fin n) A) * J * (g : Matrix (Fin n) (Fin n) A) = J ↔ _
  constructor
  · intro h x y; rw [hform_mulVec, h]
  · intro h; ext i j
    have := h (Pi.single i 1) (Pi.single j 1)
    rwa [hform_mulVec, hform_single, hform_single] at this

theorem bc_mem_HR_iff {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    [Nontrivial R] (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (g : GL (Fin n) E) :
    Formalism.UG.bc (inclR (F := F) R) g ∈ HR R σ J ↔ g ∈ Formalism.UG.UJ (σ : E →+* E) J := by
  have hinj : Function.Injective (inclR (F := F) (E := E) R) :=
    Algebra.TensorProduct.includeRight_injective (algebraMap F R).injective
  have hc : Formalism.UG.cT (sigR R σ) ((g : Matrix (Fin n) (Fin n) E).map (inclR (F := F) R)) =
      (Formalism.UG.cT (σ : E →+* E) (g : Matrix (Fin n) (Fin n) E)).map (inclR (F := F) R) := by
    ext i j; simp [Formalism.UG.cT, sigR, inclR]
  change Formalism.UG.cT (sigR R σ) ((g : Matrix (Fin n) (Fin n) E).map (inclR (F := F) R)) * J.map (inclR (F := F) R) *
      (g : Matrix (Fin n) (Fin n) E).map (inclR (F := F) R) = J.map (inclR (F := F) R) ↔
    Formalism.UG.cT (σ : E →+* E) (g : Matrix (Fin n) (Fin n) E) * J * (g : Matrix (Fin n) (Fin n) E) = J
  rw [hc, ← Matrix.map_mul, ← Matrix.map_mul]
  exact (Matrix.map_injective hinj).eq_iff

theorem bc_map_incl {F E : Type} [Field F] [Field E] [Algebra F E] {R S : Type} [CommRing R] [Algebra F R]
    [CommRing S] [Algebra F S] (φ : R →ₐ[F] S) {n : ℕ} (g : GL (Fin n) E) :
    (Formalism.UG.bc (Algebra.TensorProduct.map φ (AlgHom.id F E)).toRingHom (Formalism.UG.bc (inclR (F := F) R) g)).1 =
      (g : Matrix (Fin n) (Fin n) E).map (inclR (F := F) S) := by
  ext i j
  simp [Formalism.UG.bc, inclR]

variable {D : D7}

theorem herm_eq (V : HSp D) (x y : Fin V.rank → D.host.E) :
    herm (-V.gramᵀ) x y = - Formalism.UG.hform (D.sp.cm.sig : D.host.E →+* D.host.E) V.gram y x := by
  unfold herm Formalism.UG.hform
  rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  change x b * (-V.gram a b) * cc (y a) = -(cc (y a) * V.gram a b * x b)
  ring

theorem herm_iff (V : HSp D) (g : GL (Fin V.rank) D.host.E) :
    (∀ u v, herm (-V.gramᵀ) ((g : Matrix (Fin V.rank) (Fin V.rank) D.host.E) *ᵥ u)
      ((g : Matrix (Fin V.rank) (Fin V.rank) D.host.E) *ᵥ v) = herm (-V.gramᵀ) u v) ↔
    Formalism.UG.bc (incA D) g ∈ HR (AF D.host.F) D.sp.cm.sig V.gram := by
  have : Nontrivial (AF D.host.F) := (AdeleRing.algebraMap_injective (𝓞 D.host.F) D.host.F).nontrivial
  rw [bc_mem_HR_iff, mem_UJ_iff]
  simp only [herm_eq, neg_inj]
  exact forall_comm

theorem fin_eq {V : HSp D} {γ : GA D V} {γ' : GL (Fin V.rank) D.host.E} (h : IsRat V γ γ') :
    (finHom V γ).1 = (γ' : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (inclR (F := D.host.F) (Af D.host.F)) := by
  unfold finHom IsRat at *
  rw [MonoidHom.comp_apply, h]
  exact bc_map_incl _ _

theorem inf_eq {V : HSp D} {γ : GA D V} {γ' : GL (Fin V.rank) D.host.E} (h : IsRat V γ γ') :
    (infHom V γ).1 = (γ' : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (inclR (F := D.host.F) (Ainf D.host.F)) := by
  unfold infHom IsRat at *
  rw [MonoidHom.comp_apply, h]
  exact bc_map_incl _ _

theorem rational_elements : ∀ (D : D7) (V : HSp D), (∀ γ, γ ∈ GQ V ↔ ∃ γ', IsRat V γ γ') ∧ (∀ γ γ', IsRat V γ γ' → (∀ u v, herm (-V.gramᵀ) ((γ' : Matrix (Fin V.rank) (Fin V.rank) D.host.E) *ᵥ u) ((γ' : Matrix (Fin V.rank) (Fin V.rank) D.host.E) *ᵥ v) = herm (-V.gramᵀ) u v)) ∧ (∀ γ' : GL (Fin V.rank) D.host.E, (∀ u v, herm (-V.gramᵀ) ((γ' : Matrix (Fin V.rank) (Fin V.rank) D.host.E) *ᵥ u) ((γ' : Matrix (Fin V.rank) (Fin V.rank) D.host.E) *ᵥ v) = herm (-V.gramᵀ) u v) → ∃ γ, IsRat V γ γ') ∧ (∀ γ γ' δ δ', IsRat V γ γ' → IsRat V δ δ' → IsRat V (γ * δ) (γ' * δ') ∧ IsRat V γ⁻¹ γ'⁻¹) ∧ ∀ γ γ', IsRat V γ γ' → (∀ v, (finHom V γ).1 *ᵥ finVec V v = finVec V ((γ' : Matrix (Fin V.rank) (Fin V.rank) D.host.E) *ᵥ v)) ∧ ∀ τ θ, Formalism.MainNotions.StandardLattice.IsInfEmb τ θ → archM V θ γ = (γ' : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map τ := by
  intro D V
  have hmem : ∀ γ γ', IsRat V γ γ' → Formalism.UG.bc (incA D) γ' ∈ HR (AF D.host.F) D.sp.cm.sig V.gram := by
    intro γ γ' h
    rw [← h]; exact γ.2
  have : Nontrivial (AF D.host.F) := (AdeleRing.algebraMap_injective (𝓞 D.host.F) D.host.F).nontrivial
  refine ⟨fun γ => ⟨?_, ?_⟩, fun γ γ' h => (herm_iff V γ').2 (hmem γ γ' h),
    fun γ' h => ⟨⟨_, (herm_iff V γ').1 h⟩, rfl⟩, fun γ γ' δ δ' h k => ⟨?_, ?_⟩, fun γ γ' h => ⟨fun v => ?_, fun τ θ hθ => ?_⟩⟩
  · rintro ⟨γ', -, h⟩
    exact ⟨γ', h.symm⟩
  · rintro ⟨γ', h⟩
    exact ⟨γ', (bc_mem_HR_iff _ _ _ _).1 (hmem γ γ' h), h.symm⟩
  · unfold IsRat at *
    rw [map_mul, map_mul, h, k]
  · unfold IsRat at *
    rw [map_inv, map_inv, h]
  · rw [fin_eq h]
    funext i
    exact (RingHom.map_mulVec (inclR (F := D.host.F) (Af D.host.F))
      (γ' : Matrix (Fin V.rank) (Fin V.rank) D.host.E) v i).symm
  · unfold archM
    rw [inf_eq h]
    ext i j
    exact hθ.1 _

end GlobalTheory.Member.RatElt
