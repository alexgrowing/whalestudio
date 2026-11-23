import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.SubFamilyTwistPowSt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

noncomputable section

universe u v w

section

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]

theorem SubFamily.mem_twist_iff (F : SubFamily S x E) (Q : SubFamily S x Ω) (I J : Chart x) (h : I.1 ⊆ J.1)
    (y : E) : y ∈ (F.toSubSystem.twist Q.toSubSystem).sub J ↔
      ∃ a : chartRing S x I, IsUnit (chartIncl h a) ∧
        (a : Ω) • y ∈ (F.toSubSystem.twist Q.toSubSystem).sub I := by
  constructor
  · intro hy
    refine Submodule.span_induction (p := fun y _ => ∃ a : chartRing S x I, IsUnit (chartIncl h a) ∧
      (a : Ω) • y ∈ (F.toSubSystem.twist Q.toSubSystem).sub I) ?_ ?_ ?_ ?_ hy
    · rintro _ ⟨q, hq, z, hz, rfl⟩
      obtain ⟨a₁, ha₁, hq₁⟩ := (Q.mem_iff I J h q).mp hq
      obtain ⟨a₂, ha₂, hz₂⟩ := (F.mem_iff I J h z).mp hz
      refine ⟨a₁ * a₂, by rw [map_mul]; exact ha₁.mul ha₂, ?_⟩
      have e : ((a₁ * a₂ : chartRing S x I) : Ω) • (q • z) = ((a₁ : Ω) • q) • ((a₂ : Ω) • z) := by
        rw [Subalgebra.coe_mul, smul_eq_mul, smul_smul, smul_smul]
        congr 1
        ring
      rw [e]
      exact Submodule.subset_span ⟨_, hq₁, _, hz₂, rfl⟩
    · exact ⟨1, by rw [map_one]; exact isUnit_one, by rw [smul_zero]; exact Submodule.zero_mem _⟩
    · rintro y₁ y₂ _ _ ⟨a₁, ha₁, h₁⟩ ⟨a₂, ha₂, h₂⟩
      refine ⟨a₁ * a₂, by rw [map_mul]; exact ha₁.mul ha₂, ?_⟩
      have e : ((a₁ * a₂ : chartRing S x I) : Ω) • (y₁ + y₂) =
          a₂ • ((a₁ : Ω) • y₁) + a₁ • ((a₂ : Ω) • y₂) := by
        rw [Subalgebra.smul_def, Subalgebra.smul_def, smul_add, smul_smul, smul_smul, Subalgebra.coe_mul,
          mul_comm (a₂ : Ω) (a₁ : Ω)]
      rw [e]
      exact Submodule.add_mem _ (Submodule.smul_mem _ _ h₁) (Submodule.smul_mem _ _ h₂)
    · rintro b z _ ⟨a, ha, hz⟩
      obtain ⟨c, hc, hcb⟩ := exists_isUnit_mul_mem h b
      refine ⟨c * a, by rw [map_mul]; exact hc.mul ha, ?_⟩
      have e : ((c * a : chartRing S x I) : Ω) • (b • z) =
          (⟨_, hcb⟩ : chartRing S x I) • ((a : Ω) • z) := by
        rw [Subalgebra.smul_def, Subalgebra.smul_def, smul_smul, smul_smul, Subalgebra.coe_mul]
        congr 1
        ring
      rw [e]
      exact Submodule.smul_mem _ _ hz
  · rintro ⟨a, ⟨u, hu⟩, hay⟩
    have hJ := (F.toSubSystem.twist Q.toSubSystem).mono I J h _ hay
    have hinv : ((↑u⁻¹ : chartRing S x J) : Ω) * (a : Ω) = 1 := by
      have := congrArg Subtype.val (Units.inv_mul u)
      rw [hu] at this
      exact this
    have hy : y = (↑u⁻¹ : chartRing S x J) • ((a : Ω) • y) := by
      rw [Subalgebra.smul_def, smul_smul, hinv, one_smul]
    rw [hy]
    exact Submodule.smul_mem _ _ hJ

def SubFamily.twistFam (F : SubFamily S x E) (Q : SubFamily S x Ω) : SubFamily S x E where
  toSubSystem := F.toSubSystem.twist Q.toSubSystem
  mem_iff := F.mem_twist_iff Q

theorem SubFamily.exists_pow (Q : SubFamily S x Ω) (n : ℕ) :
    ∃ P : SubFamily S x Ω, P.toSubSystem = Q.toSubSystem.pow n := by
  induction n with
  | zero => exact ⟨(twistBundle S x 0).toSubFamily, rfl⟩
  | succ n ih =>
    obtain ⟨P, hP⟩ := ih
    refine ⟨P.twistFam Q, ?_⟩
    change P.toSubSystem.twist Q.toSubSystem = (Q.toSubSystem.pow n).twist Q.toSubSystem
    rw [hP]

end

theorem SubFamilyTwistPow.proof : SubFamilyTwistPow.Statement.{u, v, w} := by
  intro S _ Ω _ _ N x E _ _ _ _ F Q a
  obtain ⟨P, hP⟩ := SubFamily.exists_pow Q a
  exact ⟨F.twistFam P, by rw [← hP]; rfl⟩

end

end GroundTheory.Heights₂.Heights.Kleiman
