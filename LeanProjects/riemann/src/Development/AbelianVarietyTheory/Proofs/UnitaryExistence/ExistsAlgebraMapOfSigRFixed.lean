import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
import Formalism.LocalToGlobal.ProjectiveLattices.ParCanon
import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
import Formalism.LocalToGlobal.ProjectiveLattices.ValSetAlgSubset
import Formalism.LocalToGlobal.ProjectiveLattices.IntAll
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import Formalism.LocalToGlobal.ProjectiveLattices.VolProofs
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIsDetRoot

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member

namespace GlobalTheory.Member

theorem exists_algebraMap_of_sigR_fixed {F E : Type} [Field F] [CharZero F] [Field E] [Algebra F E]
    (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E)
    (htr : ∀ x : E, ∃ t : F, algebraMap F E t = x + σ x) (z : R ⊗[F] E) (hz : sigR R σ z = z) :
    ∃ a : R, algebraMap R (R ⊗[F] E) a = z := by
  have hT : ∀ z : R ⊗[F] E, ∃ t : R, z + sigR R σ z = t ⊗ₜ 1 := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | tmul a x =>
      obtain ⟨t, ht⟩ := htr x
      refine ⟨t • a, ?_⟩
      have h : sigR R σ (a ⊗ₜ x) = a ⊗ₜ σ x := by simp [sigR]
      rw [h, ← TensorProduct.tmul_add, ← ht, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
    | add x y hx hy =>
      obtain ⟨t, ht⟩ := hx
      obtain ⟨t', ht'⟩ := hy
      refine ⟨t + t', ?_⟩
      rw [map_add, TensorProduct.add_tmul, ← ht, ← ht']; ring
  obtain ⟨t, ht⟩ := hT z
  refine ⟨(2 : F)⁻¹ • t, ?_⟩
  rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
    ← TensorProduct.smul_tmul', ← ht, hz, ← two_smul F z, smul_smul, inv_mul_cancel₀ two_ne_zero, one_smul]

theorem exists_unit_of_sigR_fixed {F E : Type} [Field F] [CharZero F] [Field E] [Algebra F E]
    (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E)
    (htr : ∀ x : E, ∃ t : F, algebraMap F E t = x + σ x) (z : (R ⊗[F] E)ˣ)
    (hz : sigR R σ (z : R ⊗[F] E) = z) :
    ∃ a : Rˣ, Units.map (algebraMap R (R ⊗[F] E)).toMonoidHom a = z := by
  have hz' : sigR R σ ((z⁻¹ : (R ⊗[F] E)ˣ) : R ⊗[F] E) = (z⁻¹ : (R ⊗[F] E)ˣ) := by
    apply z.isUnit.mul_left_cancel
    conv_lhs => rw [← hz, ← map_mul]
    simp
  obtain ⟨a, ha⟩ := exists_algebraMap_of_sigR_fixed R σ htr _ hz
  obtain ⟨b, hb⟩ := exists_algebraMap_of_sigR_fixed R σ htr _ hz'
  have hinj : Function.Injective (algebraMap R (R ⊗[F] E)) :=
    Algebra.TensorProduct.includeLeft_injective (S := F) (algebraMap F E).injective
  have hab : a * b = 1 := hinj (by rw [map_mul, ha, hb, map_one]; simp)
  exact ⟨⟨a, b, hab, by rw [mul_comm, hab]⟩, Units.ext ha⟩

theorem exists_root_of_norm_one {E : Type} [Field E] (σ : E →+* E) (hσ : ∀ x, σ (σ x) = x)
    (hne : ∃ y, σ y ≠ y) (u : E) (hu : σ u * u = 1) : ∃ x : Eˣ, (x : E) = u * σ x := by
  by_cases h : 1 + u = 0
  · obtain ⟨y, hy⟩ := hne
    refine ⟨Units.mk0 (y - σ y) (sub_ne_zero.2 hy.symm), ?_⟩
    rw [Units.val_mk0, map_sub, hσ]
    linear_combination (y - σ y) * h
  · refine ⟨Units.mk0 (1 + u) h, ?_⟩
    rw [Units.val_mk0, map_add, map_one]
    linear_combination - hu

theorem isDetRoot_mul {D : D7} (V : HSp D) (g g' : GA D V) (x x' : (AE D)ˣ) (hx : IsDetRoot V g x)
    (hx' : IsDetRoot V g' x') : IsDetRoot V (g * g') (x * x') := by
  unfold IsDetRoot at *
  rw [Units.val_mul, (matHom V).map_mul, Units.val_mul, Matrix.det_mul, RingHom.map_mul]
  conv_lhs => rw [hx, hx']
  ring

theorem isDetRoot_laws : ∀ (D : D7) (V : HSp D), (∀ g : GA D V, ∃ x, IsDetRoot V g x) ∧ (∀ g x x', IsDetRoot V g x → IsDetRoot V g x' → ∃ a, x' = x * idF D a) ∧ (∀ γ ∈ GQ V, ∃ x : D.host.Eˣ, IsDetRoot V γ (Units.map (incA D).toMonoidHom x)) ∧ ∀ g g' x x', IsDetRoot V g x → IsDetRoot V g' x' → IsDetRoot V (g * g') (x * x') := by
  intro D V
  have hσ : ∀ x, D.sp.cm.sig (D.sp.cm.sig x) = x := fun x => star_star x
  refine ⟨GlobalTheory.RecDict.exists_isDetRoot D V, ?_, ?_, ?_⟩
  · intro g x x' hx hx'
    have htr : ∀ x : D.host.E, ∃ t : D.host.F, algebraMap _ _ t = x + D.sp.cm.sig x := by
      intro x
      apply (D.sp.cm.fixed _).1
      change D.sp.cm.sig _ = _
      rw [map_add, hσ, add_comm]
    unfold IsDetRoot at hx hx'
    obtain ⟨a, ha⟩ := exists_unit_of_sigR_fixed (AF D.host.F) D.sp.cm.sig htr (x⁻¹ * x') (by
      apply (x.isUnit.map (sigR (AF D.host.F) D.sp.cm.sig)).mul_left_cancel
      apply x.isUnit.mul_left_cancel
      rw [← map_mul, ← Units.val_mul, mul_inv_cancel_left, mul_left_comm, ← Units.val_mul, mul_inv_cancel_left]
      linear_combination (sigR (AF D.host.F) D.sp.cm.sig (x' : AE D)) * hx -
        (sigR (AF D.host.F) D.sp.cm.sig (x : AE D)) * hx')
    refine ⟨a, ?_⟩
    unfold idF
    rw [ha, mul_inv_cancel_left]
  · intro γ hγ
    obtain ⟨γ', -, hγ'⟩ := hγ
    have hdet : (Formalism.L2.Theta.mt V γ).det = incA D (γ' : Matrix (Fin V.rank) (Fin V.rank) D.host.E).det := by
      rw [RingHom.map_det]
      congr 1
      exact congrArg Units.val hγ'.symm
    have hc : ∀ y, cA D (incA D y) = incA D (D.sp.cm.sig y) := by
      intro y; simp [cA, sigR, inclR]
    have hinj : Function.Injective (incA D) :=
      Algebra.TensorProduct.includeRight_injective (AdeleRing.algebraMap_injective _ _)
    have hu := det_conj_mul V γ
    rw [hdet, hc, ← map_mul, ← map_one (incA D)] at hu
    obtain ⟨x, hx⟩ := exists_root_of_norm_one (D.sp.cm.sig : D.host.E →+* D.host.E) hσ
      (GlobalTheory.RecDict.cmData_sig_ne_id D.sp.cm) _ (hinj hu)
    refine ⟨x, ?_⟩
    have key : incA D (x : D.host.E) = (Formalism.L2.Theta.mt V γ).det * cA D (incA D (x : D.host.E)) := by
      rw [hdet, hc, ← map_mul]
      exact congrArg _ hx
    unfold IsDetRoot
    rw [Units.coe_map]
    exact key
  · exact isDetRoot_mul V

end GlobalTheory.Member
