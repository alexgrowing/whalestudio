import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.CupSurjectivity.RhsF

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris

namespace CrystallineSemistableComparison.Onto

open Pb HT

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

theorem core (hC : CupLaws) (hS : Slant) (P : HTPre l K) {M : Model l K} (hM : M.Sm) {d : ℕ} (Dt : Dat hC P M d)
    (hfin : FiniteDimensional ℚ_[l] (M.V (2 + 2 * d))) (hI : P.Inj M (2 + 2 * d)) {a' n : ℕ} (x : Hdg M.q a' n) :
    tgt hC x Dt.N ∈ Sp P M n := by
  classical
  have hR : ∀ (α : ℕ) (φ' : Module.Dual K (Hdg M.q α (2 + 2 * d))), rhsF hC P Dt x φ' ∈ Sp P M n := by
    intro α φ'
    rw [← eid hC hS P hM Dt x φ']
    unfold lhsF Sp
    refine Submodule.add_mem _ (Submodule.sum_mem _ fun s _ => ?_) (Submodule.sum_mem _ fun s _ => ?_) <;>
      split_ifs <;>
      first
        | exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
        | exact Submodule.zero_mem _
  have hsum : ∀ G : Module.Dual K (Hdg M.q 0 0),
      ∑ s, P.h M 0 0 (M.toV 0 (Dt.b₀ s)) G = qC l Dt.N * kC K (G (oneH M.q)) := by
    intro G
    have e1 : ∑ s, P.h M 0 0 (M.toV 0 (Dt.b₀ s)) G = P.h M 0 0 (∑ s, M.toV 0 (Dt.b₀ s)) G := by
      rw [map_sum, AddMonoidHom.finsetSum_apply]
    rw [e1, Dt.sum₀, P.lin, P.one M hM Dt.one Dt.hone]
  let vec : (Σ α : ℕ, Module.Dual K (Hdg M.q α (2 + 2 * d))) → (Fin Dt.m₀ → ℂ_[l]) :=
    fun p s => P.h M p.1 (2 + 2 * d) (M.toV _ (Dt.a₀ s)) p.2
  have h1 : (fun _ => (1 : ℂ_[l])) ∈ Submodule.span ℂ_[l] (Set.range vec) := by
    by_contra hn
    obtain ⟨f, hf1, hf0⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hn inferInstance
    have hvan : ∀ p, f (vec p) = 0 := fun p => by
      have hm : f (vec p) ∈ (Submodule.span ℂ_[l] (Set.range vec)).map f :=
        Submodule.mem_map_of_mem (Submodule.subset_span ⟨p, rfl⟩)
      rw [hf0] at hm
      exact (Submodule.mem_bot _).mp hm
    let z : Fin Dt.m₀ → ℂ_[l] := fun s => f (fun j => if s = j then 1 else 0)
    have hfz : ∀ y, f y = ∑ s, y s * z s := fun y => by
      rw [LinearMap.pi_apply_eq_sum_univ f y]
      simp only [smul_eq_mul, z]
    obtain ⟨S, _, b0, hb0⟩ : ∃ (S : Set (M.V (2 + 2 * d))) (_ : Fintype S)
        (b0 : Module.Basis (Fin Dt.m₀ ⊕ S) ℚ_[l] (M.V (2 + 2 * d))),
        ∀ s, b0 (Sum.inl s) = M.toV _ (Dt.a₀ s) := by
      have hfi := Module.Finite.finite_basis (Module.Basis.sumExtend Dt.li)
      refine ⟨Module.Basis.sumExtendIndex Dt.li, ?_, Module.Basis.sumExtend Dt.li, fun s => ?_⟩
      · exact @Fintype.ofFinite _ (@Finite.of_injective _ _ hfi Sum.inr Sum.inr_injective)
      · simp only [Module.Basis.sumExtend, Module.Basis.reindex_apply, Module.Basis.coe_extend]
        rfl
    let e := Fintype.equivFin (Fin Dt.m₀ ⊕ S)
    let b := b0.reindex e
    let z' : Fin (Fintype.card (Fin Dt.m₀ ⊕ S)) → ℂ_[l] := fun i => Sum.elim z (fun _ => 0) (e.symm i)
    have hyp : ∀ (a : ℕ) (φ : Module.Dual K (Hdg M.q a (2 + 2 * d))),
        ∑ i, z' i * P.h M a (2 + 2 * d) (b i) φ = 0 := by
      intro a φ
      have hv := hvan ⟨a, φ⟩
      rw [hfz] at hv
      simp only [b, z', Module.Basis.reindex_apply]
      rw [Equiv.sum_comp e.symm (fun j => Sum.elim z (fun _ => 0) j * P.h M a (2 + 2 * d) (b0 j) φ),
        Fintype.sum_sum_type]
      simp only [Sum.elim_inl, Sum.elim_inr, zero_mul, Finset.sum_const_zero, add_zero, hb0]
      refine Eq.trans ?_ hv
      exact Finset.sum_congr rfl fun s _ => mul_comm _ _
    have hz' : z' = 0 := hI b z' hyp
    have hz : z = 0 := by
      funext s
      have hs := congrFun hz' (e (Sum.inl s))
      simpa [z'] using hs
    apply hf1
    rw [hfz]
    simp [hz]
  let Φ : (Fin Dt.m₀ → ℂ_[l]) →ₗ[ℂ_[l]] GF M n :=
    { toFun := fun c β ψ => ∑ s, c s * P.h M 0 0 (M.toV 0 (Dt.b₀ s)) (Gx hC x ψ)
      map_add' := fun c c' => by
        funext β ψ
        simp [add_mul, Finset.sum_add_distrib]
      map_smul' := fun r c => by
        funext β ψ
        simp [Finset.mul_sum, mul_assoc] }
  have hle : Submodule.span ℂ_[l] (Set.range vec) ≤ (Sp P M n).comap Φ := by
    rw [Submodule.span_le]
    rintro _ ⟨p, rfl⟩
    exact hR p.1 p.2
  have hmem := hle h1
  rw [Submodule.mem_comap] at hmem
  convert hmem using 1
  funext β ψ
  simp only [Φ, LinearMap.coe_mk, AddHom.coe_mk, one_mul]
  unfold tgt
  exact (hsum _).symm

end CrystallineSemistableComparison.Onto

end
