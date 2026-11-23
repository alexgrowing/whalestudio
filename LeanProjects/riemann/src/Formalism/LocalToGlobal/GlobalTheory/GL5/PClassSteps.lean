import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassMass.UJClassMassOfOpen
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassFiniteness.AdelicBounds
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassFiniteness.LatticeClassesFiniteRefinement
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassFiniteness.PosDefOfDefiniteSignatureHolds

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.ClassSteps

open NumberField PI.UJClassFin PI.UJClassMass PI.UnitaryGroupMassFormula.UJClassMass Formalism.HermitianLatticesTheory
open scoped TensorProduct ComplexOrder

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem crd_smul_mem {V : Type} [AddCommGroup V] [Module E V] [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V] {M : ℕ}
    (b : Module.Basis (Fin M) E V) (L0 : Submodule (𝓞 E) V) (r : 𝓞 E) {x : Fin M → E} (hx : x ∈ crdOf b L0) :
    (r : E) • x ∈ crdOf b L0 := by
  show ∑ i, ((r : E) • x) i • b i ∈ L0
  have e : ∑ i, ((r : E) • x) i • b i = r • ∑ i, x i • b i := by
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Pi.smul_apply, smul_eq_mul, mul_smul, algebraMap_smul]
  rw [e]
  exact L0.smul_mem r hx

theorem latHat_smul {M : ℕ} (L : Set (Fin M → E)) (hL : ∀ r : 𝓞 E, ∀ x ∈ L, (r : E) • x ∈ L) (r : 𝓞 E)
    {y : Fin M → Af F ⊗[F] E} (hy : y ∈ latHat F E L) :
    inclR (F := F) (Af F) (r : E) • y ∈ latHat F E L := by
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨a, ha, x, hx, rfl⟩ := hy
    refine AddSubgroup.subset_closure ⟨a, ha, (r : E) • x, hL r x hx, ?_⟩
    funext i
    rw [Pi.smul_apply, smul_eq_mul, Pi.smul_apply, smul_eq_mul]
    show (1 : Af F) ⊗ₜ[F] (r : E) * a ⊗ₜ[F] x i = a ⊗ₜ[F] ((r : E) * x i)
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  | zero => rw [smul_zero]; exact zero_mem _
  | add y z _ _ h1 h2 => rw [smul_add]; exact add_mem h1 h2
  | neg y _ h1 => rw [smul_neg]; exact neg_mem h1

theorem vinc_zero {M : ℕ} : PI.UnitaryGroupMassFormula.UJClassFin.vinc (F := F) (0 : Fin M → E) = 0 := by
  funext i; exact map_zero _

theorem vinc_add {M : ℕ} (x y : Fin M → E) :
    PI.UnitaryGroupMassFormula.UJClassFin.vinc (F := F) (x + y) = PI.UnitaryGroupMassFormula.UJClassFin.vinc (F := F) x + PI.UnitaryGroupMassFormula.UJClassFin.vinc (F := F) y := by
  funext i; exact map_add _ _ _

theorem vinc_smul {M : ℕ} (c : E) (x : Fin M → E) :
    PI.UnitaryGroupMassFormula.UJClassFin.vinc (F := F) (c • x) = inclR (F := F) (Af F) c • PI.UnitaryGroupMassFormula.UJClassFin.vinc (F := F) x := by
  funext i; exact map_mul _ _ _

variable (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)

def lamSub (L : Set (Fin M → E)) (hL : ∀ r : 𝓞 E, ∀ x ∈ L, (r : E) • x ∈ L) (g : HA (AF F) σ J) :
    Submodule (𝓞 E) (Fin M → E) where
  carrier := PI.UnitaryGroupMassFormula.UJClassFin.abelian₂ σ J L g
  zero_mem' := by
    show (finMat σ J g⁻¹).mulVec (PI.UnitaryGroupMassFormula.UJClassFin.vinc (F := F) 0) ∈ latHat F E L
    rw [vinc_zero, Matrix.mulVec_zero]; exact zero_mem _
  add_mem' := by
    intro x y hx hy
    show (finMat σ J g⁻¹).mulVec (PI.UnitaryGroupMassFormula.UJClassFin.vinc (F := F) (x + y)) ∈ latHat F E L
    rw [vinc_add, Matrix.mulVec_add]; exact add_mem hx hy
  smul_mem' := by
    intro r x hx
    show (finMat σ J g⁻¹).mulVec (PI.UnitaryGroupMassFormula.UJClassFin.vinc (F := F) (r • x)) ∈ latHat F E L
    have e : r • x = (r : E) • x := by funext i; exact Algebra.smul_def r (x i)
    rw [e, vinc_smul, Matrix.mulVec_smul]
    exact latHat_smul L hL r hx

end Gen

def LatGenus : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E]
    (σ : E →ₐ[F] E) (V : Type) [AddCommGroup V] [Module E V] [Module (𝓞 E) V]
    [IsScalarTower (𝓞 E) E V] [FiniteDimensional E V]
    (h : V →ₗ⋆[E] V →ₗ[E] E) (M : ℕ) (b : Module.Basis (Fin M) E V) (L0 : Submodule (𝓞 E) V),
    (∀ a, σ a = star a) → (∃ θ : E, σ θ ≠ θ) →
    (∀ (τ : E →+* ℂ) (a : E), τ (star a) = starRingEnd ℂ (τ a)) →
    h.IsSymm → h.Nondegenerate → Submodule.IsLattice E L0 →
    (∀ τ : E →+* ℂ, HasSignature ((gramOf h b).map τ) M 0) →
    ∀ (g : HA (AF F) σ (gramOf h b)) (N : Submodule (𝓞 E) V),
      (N : Set V) = latSet σ (gramOf h b) b L0 g → Submodule.IsLattice E N → SameGenus h L0 N

theorem latLattice : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E]
    (σ : E →ₐ[F] E) (V : Type) [AddCommGroup V] [Module E V] [Module (𝓞 E) V]
    [IsScalarTower (𝓞 E) E V] [FiniteDimensional E V]
    (h : V →ₗ⋆[E] V →ₗ[E] E) (M : ℕ) (b : Module.Basis (Fin M) E V) (L0 : Submodule (𝓞 E) V),
    (∀ a, σ a = star a) →
    (∀ (τ : E →+* ℂ) (a : E), τ (star a) = starRingEnd ℂ (τ a)) →
    Submodule.IsLattice E L0 →
    (∀ τ : E →+* ℂ, HasSignature ((gramOf h b).map τ) M 0) →
    ∀ g : HA (AF F) σ (gramOf h b), ∃ N : Submodule (𝓞 E) V,
      (N : Set V) = latSet σ (gramOf h b) b L0 g ∧ Submodule.IsLattice E N := by
  intro F E _ _ _ _ _ _ σ V _ _ _ _ _ h M b L0 hσ hτ hL hsig g
  classical
  have hcrd := crdBounds F E V M b L0 hL
  obtain ⟨D, T, c0, hD, hT, hc0, hall⟩ :=
    PI.UnitaryGroupMassFormula.UJClassFin.adelic_bounds F E σ M (gramOf h b) (crdOf b L0) hσ hτ hsig hcrd.1 hcrd.2
  obtain ⟨-, ⟨k, hk0, hlow⟩, hint, -⟩ := hall g
  have hLs : ∀ r : 𝓞 E, ∀ x ∈ crdOf b L0, (r : E) • x ∈ crdOf b L0 := fun r x hx => crd_smul_mem b L0 r hx
  let Nc := lamSub σ (gramOf h b) (crdOf b L0) hLs g
  let e' : V ≃ₗ[𝓞 E] (Fin M → E) := b.equivFun.restrictScalars (𝓞 E)
  let N : Submodule (𝓞 E) V := Nc.comap e'.toLinearMap
  refine ⟨N, rfl, ?_, ?_⟩
  ·

    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    have hPD := PI.UnitaryGroupMassFormula.UJClassFin.posDefOfDefiniteSignature_holds M _ (hsig τ)
    have hdet : (gramOf h b).det ≠ 0 := by
      intro h0
      have : ((gramOf h b).map τ).det = 0 := by
        rw [show (gramOf h b).map τ = τ.mapMatrix (gramOf h b) from rfl, ← RingHom.map_det, h0, map_zero]
      exact hPD.det_pos.ne' this
    have hu : IsUnit (gramOf h b).det := isUnit_iff_ne_zero.mpr hdet
    obtain ⟨d, hd0, hdint⟩ := PI.UnitaryGroupMassFormula.UJClassFin.mat_den (gramOf h b)⁻¹
    have hJy : ∀ y ∈ Nc, ∀ i, IsIntegral ℤ ((D : E) * (k : E) * ((gramOf h b).mulVec y) i) := by
      intro y hy i
      have h1 := hint _ (hlow i 1 isIntegral_one) y hy
      have e : PI.HermLatFin.herm (σ : E →+* E) (gramOf h b) (Pi.single i ((k : E) * 1)) y =
          (k : E) * ((gramOf h b).mulVec y) i := by
        unfold PI.HermLatFin.herm
        rw [Finset.sum_eq_single i]
        · simp only [Pi.single_eq_same, mul_one, map_natCast, Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]
        · intro j _ hj
          simp [Pi.single_eq_of_ne hj]
        · intro hi; exact absurd (Finset.mem_univ i) hi
      rw [e, ← mul_assoc] at h1
      exact h1
    have hy_eq : ∀ y : Fin M → E, y = ((gramOf h b)⁻¹).mulVec ((gramOf h b).mulVec y) := by
      intro y
      rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec]
    have hfgc : Nc.FG := by
      refine PI.UnitaryGroupMassFormula.UJClassFin.fg_of_den Nc (d * D * k) (by positivity) fun y hy j => ?_
      have hyj : y j = ∑ i, (gramOf h b)⁻¹ j i * ((gramOf h b).mulVec y) i := by
        conv_lhs => rw [hy_eq y]
        rfl
      rw [hyj, Finset.mul_sum]
      refine IsIntegral.sum _ fun i _ => ?_
      have e : ((d * D * k : ℕ) : E) * ((gramOf h b)⁻¹ j i * ((gramOf h b).mulVec y) i) =
          ((d : E) * (gramOf h b)⁻¹ j i) * ((D : E) * (k : E) * ((gramOf h b).mulVec y) i) := by
        push_cast; ring
      rw [e]
      exact (hdint j i).mul (hJy y hy i)
    have hN : N = Nc.map e'.symm.toLinearMap := Submodule.comap_equiv_eq_map_symm e' Nc
    rw [hN]
    exact hfgc.map _
  ·
    rw [eq_top_iff, ← b.span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    have hk : (k : E) ≠ 0 := by exact_mod_cast hk0.ne'
    have hmem : (k : E) • b i ∈ N := by
      show b.equivFun ((k : E) • b i) ∈ PI.UnitaryGroupMassFormula.UJClassFin.abelian₂ σ (gramOf h b) (crdOf b L0) g
      have e : b.equivFun ((k : E) • b i) = Pi.single i ((k : E) * 1) := by
        funext j
        rw [map_smul, Pi.smul_apply, Module.Basis.equivFun_apply, b.repr_self, Finsupp.single_apply,
          Pi.single_apply, smul_eq_mul]
        split_ifs <;> simp_all
      rw [e]
      exact hlow i 1 isIntegral_one
    have e2 : b i = (k : E)⁻¹ • ((k : E) • b i) := by rw [smul_smul, inv_mul_cancel₀ hk, one_smul]
    rw [e2]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)

theorem latStep_of (hG : LatGenus) : LatStep := by
  intro F E _ _ _ _ _ _ σ V _ _ _ _ _ h M b L0 hσ hθ hτ hsymm hnd hL hsig g
  obtain ⟨N, hNs, hNl⟩ := latLattice F E σ V h M b L0 hσ hτ hL hsig g
  exact ⟨N, hNs, hNl, hG F E σ V h M b L0 hσ hθ hτ hsymm hnd hL hsig g N hNs hNl⟩

theorem uJClassMass_of_genus (hG : LatGenus) (hS : SurjStep) : PI.UJClassMass2.UJClassMass :=
  uJClassMass_of_open (latStep_of hG) hS

end Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.ClassSteps

end
