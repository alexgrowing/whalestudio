import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrysActApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QActMSubAlgebraMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSimpleRingOfIsSemisimpleRing
import GroundTheory.Brauer.BaseChangeCSA

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.UPel.HT.MoritaChar0

variable {p : ℕ} [Fact p.Prime] (D : Datum p)

theorem actF_mem_algO (x : D.F) : ((D.actF x : D.endO) : Module.End ℚ D.VQ) ∈ D.algO := by
  rw [← (integralBasis D.F).sum_repr x, map_sum]
  rw [AddSubmonoidClass.coe_finset_sum]
  refine Subalgebra.sum_mem _ fun i _ => ?_
  rw [map_smul, Subalgebra.coe_smul, integralBasis_apply, D.actF_coe, D.coe_actInt]
  exact Subalgebra.smul_mem _ (D.actQ_mem_algO _) _

def toAlgO : D.F →+* D.algO :=
  (D.endO.val.toRingHom.comp D.actF.toRingHom).codRestrict D.algO (actF_mem_algO D)

theorem toAlgO_comm (x : D.F) (a : D.algO) : toAlgO D x * a = a * toAlgO D x := by
  have h : ((D.actF x : D.endO) : Module.End ℚ D.VQ) ∈ Subalgebra.centralizer ℚ (D.algO : Set (Module.End ℚ D.VQ)) := by
    rw [D.centralizer_algO]; exact (D.actF x).2
  rw [Subalgebra.mem_centralizer_iff] at h
  exact Subtype.ext (h a a.2).symm

def algebraFAlgO : Algebra D.F D.algO := (toAlgO D).toAlgebra' (toAlgO_comm D)

attribute [local instance] algebraFAlgO

instance towerQFAlgO : IsScalarTower ℚ D.F D.algO :=
  IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)

instance finFAlgO : FiniteDimensional D.F D.algO := Module.Finite.of_restrictScalars_finite ℚ D.F D.algO

instance centralFAlgO : Algebra.IsCentral D.F D.algO := by
  refine ⟨fun z hz => ?_⟩
  rw [Subalgebra.mem_center_iff] at hz
  obtain ⟨c, hc⟩ := D.center_algO z z.2 fun h hh => congrArg Subtype.val (hz ⟨h, hh⟩)
  exact Algebra.mem_bot.2 ⟨c, Subtype.ext hc.symm⟩

theorem finrank_F_algO : Module.finrank D.F D.algO = D.m ^ 2 := by
  have h := Module.finrank_mul_finrank ℚ D.F D.algO
  rw [D.finrank_algO, mul_comm (D.m ^ 2)] at h
  exact Nat.eq_of_mul_eq_mul_left Module.finrank_pos h

theorem algebraMap_injective_of_charZero (K : Type) [Field K] [NumberField K] (k : Type) [Field k]
    [CharZero k] [Algebra (𝓞 K) k] : Function.Injective (algebraMap (𝓞 K) k) := by
  rw [injective_iff_map_eq_zero]
  intro c hc
  by_contra h0
  have hne := Ideal.comap_ne_bot_of_integral_mem (R := ℤ) (I := RingHom.ker (algebraMap (𝓞 K) k)) h0
    (RingHom.mem_ker.2 hc) (Algebra.IsIntegral.isIntegral c)
  apply hne
  rw [RingHom.comap_ker]
  exact (RingHom.injective_iff_ker_eq_bot _).1 (RingHom.injective_int _)

end GlobalTheory.UPel.HT.MoritaChar0

namespace GlobalTheory.UPel.HT.MoritaChar0

variable {p : ℕ} [Fact p.Prime] (D : Datum p)

attribute [local instance] algebraFAlgO

def algebraOFAlgO : Algebra (𝓞 D.F) D.algO :=
  ((algebraMap D.F D.algO).comp (algebraMap (𝓞 D.F) D.F)).toAlgebra' fun _ _ => Algebra.commutes _ _

attribute [local instance] algebraOFAlgO

instance towerOFAlgO : IsScalarTower (𝓞 D.F) D.F D.algO := IsScalarTower.of_algebraMap_eq fun _ => rfl

def ordToAlgO : D.O →ₐ[𝓞 D.F] D.algO where
  toRingHom := D.actQ.codRestrict D.algO D.actQ_mem_algO
  commutes' c := by
    apply Subtype.ext
    show D.actQ (algebraMap (𝓞 D.F) D.O c) = ((D.actF (c : D.F) : D.endO) : Module.End ℚ D.VQ)
    rw [D.actF_coe, D.coe_actInt]

instance isLocalizedModule_ordToAlgO :
    IsLocalizedModule (nonZeroDivisors (𝓞 D.F)) (ordToAlgO D).toLinearMap where
  map_units s := by
    rw [Module.End.isUnit_iff]
    have hs : ((s : 𝓞 D.F) : D.F) ≠ 0 := by
      intro h
      exact nonZeroDivisors.coe_ne_zero s (RingOfIntegers.coe_eq_zero_iff.1 h)
    have key : ∀ a : D.algO, algebraMap (𝓞 D.F) (Module.End (𝓞 D.F) D.algO) s a = ((s : 𝓞 D.F) : D.F) • a := by
      intro a
      rw [Module.algebraMap_end_apply, ← algebraMap_smul D.F (s : 𝓞 D.F) a]
    refine ⟨fun a b h => ?_, fun a => ⟨((s : 𝓞 D.F) : D.F)⁻¹ • a, ?_⟩⟩
    · rw [key, key] at h
      exact smul_right_injective _ hs h
    · rw [key, smul_inv_smul₀ hs]
  surj y := by
    obtain ⟨q, x, hx⟩ := D.exists_of_mem_algO y.2
    refine ⟨(q.num • x, ⟨(q.den : 𝓞 D.F), mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast q.den_ne_zero)⟩), ?_⟩
    apply Subtype.ext
    show (((q.den : 𝓞 D.F) • y : D.algO) : Module.End ℚ D.VQ) = D.actQ (q.num • x)
    rw [Nat.cast_smul_eq_nsmul, AddSubmonoidClass.coe_nsmul, hx, map_zsmul, ← Nat.cast_smul_eq_nsmul ℚ, smul_smul,
      ← Int.cast_smul_eq_zsmul ℚ, Rat.den_mul_eq_num]
  exists_of_eq h := ⟨1, by rw [one_smul, one_smul]; exact D.actQ_injective (congrArg Subtype.val h)⟩

end GlobalTheory.UPel.HT.MoritaChar0

namespace GlobalTheory.UPel.HT.MoritaChar0
attribute [local instance] algebraFAlgO algebraOFAlgO

theorem tensor_order_algEquiv_matrix : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (k : Type) [Field k]
    [IsAlgClosed k] [CharZero k] [Algebra (𝓞 D.F) k],
    Nonempty ((k ⊗[𝓞 D.F] D.O) ≃ₐ[k] Matrix (Fin D.m) (Fin D.m) k) := by
  intro p _ D k _ _ _ _
  have hinj := algebraMap_injective_of_charZero D.F k
  letI : Algebra D.F k := (IsFractionRing.lift hinj).toAlgebra
  haveI : IsScalarTower (𝓞 D.F) D.F k :=
    IsScalarTower.of_algebraMap_eq fun c => (IsFractionRing.lift_algebraMap hinj c).symm
  haveI : SMulCommClass D.F (𝓞 D.F) k := ⟨fun a b x => by simp only [Algebra.smul_def]; ring⟩
  have hF : IsBaseChange D.F (ordToAlgO D).toLinearMap :=
    IsLocalizedModule.isBaseChange (nonZeroDivisors (𝓞 D.F)) D.F _
  have hk : IsBaseChange k (TensorProduct.mk D.F k D.algO 1) := TensorProduct.isBaseChange D.F D.algO k
  have hc := hF.comp hk
  let φ : (k ⊗[𝓞 D.F] D.O) ≃ₐ[k] (k ⊗[D.F] D.algO) :=
    AlgEquiv.ofLinearEquiv hc.equiv (by
      rw [Algebra.TensorProduct.one_def, IsBaseChange.equiv_tmul]
      simp [Algebra.TensorProduct.one_def])
      (LinearMap.map_mul_of_map_mul_tmul fun a₁ a₂ b₁ b₂ => by
        simp [IsBaseChange.equiv_tmul, Algebra.TensorProduct.tmul_mul_tmul, TensorProduct.smul_tmul'])
  haveI : IsSimpleRing D.algO := D.algO_simple
  obtain ⟨n, _, ⟨e⟩⟩ := IsSimpleRing.exists_algEquiv_matrix_of_isAlgClosed k (k ⊗[D.F] D.algO)
  have hn : n = D.m := by
    have h1 := GroundTheory.Brauer.finrank_baseChange_eq D.F k D.algO
    rw [e.toLinearEquiv.finrank_eq, Module.finrank_matrix, Module.finrank_self, finrank_F_algO,
      Fintype.card_fin] at h1
    exact Nat.mul_self_inj.mp (by simpa [pow_two] using h1)
  subst hn
  exact ⟨φ.trans e⟩

end GlobalTheory.UPel.HT.MoritaChar0
