import ReciprocityTheory.ClassFieldTheory.LocalClassField.EulerDefs

namespace ReciprocityTheory.DiscreteGroups.LocalClassField.Euler

open _root_.Neutral.B1 Function

noncomputable section

section aux

variable (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))

def OLaddEquiv : OLadd p K ≃+ OK p K where
  toFun x := ⟨⟨x.1, x.2.1⟩, (mem_OK_iff p K _).2 x.2.2⟩
  invFun y := ⟨y.1.1, y.1.2, (mem_OK_iff p K _).1 y.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

theorem map_range_OLaddEquiv (z : ℤ) :
    (zmultiplesHom (OLadd p K →+ OLadd p K) (AddMonoidHom.id _) z).range.map (OLaddEquiv p K : OLadd p K →+ OK p K) =
      (Ideal.span {(z : OK p K)}).toAddSubgroup := by
  ext y
  rw [AddSubgroup.mem_map, Submodule.mem_toAddSubgroup, Ideal.mem_span_singleton']
  constructor
  · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
    refine ⟨OLaddEquiv p K x, ?_⟩
    have : (zmultiplesHom (OLadd p K →+ OLadd p K) (AddMonoidHom.id _) z) x = z • x := rfl
    rw [this]
    show _ = OLaddEquiv p K (z • x)
    rw [map_zsmul, zsmul_eq_mul, mul_comm]
  · rintro ⟨a, rfl⟩
    refine ⟨_, ⟨(OLaddEquiv p K).symm a, rfl⟩, ?_⟩
    have : (zmultiplesHom (OLadd p K →+ OLadd p K) (AddMonoidHom.id _) z) ((OLaddEquiv p K).symm a) =
      z • (OLaddEquiv p K).symm a := rfl
    rw [this]
    show OLaddEquiv p K (z • (OLaddEquiv p K).symm a) = _
    rw [map_zsmul, zsmul_eq_mul, mul_comm, AddEquiv.apply_symm_apply]

def quotOLaddEquiv (z : ℤ) :
    (OLadd p K ⧸ (zmultiplesHom (OLadd p K →+ OLadd p K) (AddMonoidHom.id _) z).range) ≃
      (OK p K ⧸ Ideal.span {(z : OK p K)}) :=
  (QuotientAddGroup.congr _ _ (OLaddEquiv p K) (map_range_OLaddEquiv p K z)).toEquiv

attribute [local instance] zpAlgOK

theorem card_OK_quot_natCast (hK : FiniteDimensional ℚ_[p] K) {n : ℕ} (hn : n ≠ 0) :
    Nat.card (OK p K ⧸ Ideal.span {(n : OK p K)}) = (p ^ padicValNat p n) ^ Module.finrank ℚ_[p] K := by
  have := isScalarTower_zp_OK p K
  have := isIntegralClosure_OK p K
  have := isTorsionFree_zp_K p K
  have : Module.Free ℤ_[p] (OK p K) := IsIntegralClosure.module_free ℤ_[p] ℚ_[p] K _
  have : Module.Finite ℤ_[p] (OK p K) := IsIntegralClosure.finite ℤ_[p] ℚ_[p] K _
  have hr := IsIntegralClosure.rank ℤ_[p] ℚ_[p] K (OK p K)
  have hn' : (n : OK p K) = algebraMap ℤ_[p] (OK p K) (n : ℕ) := (map_natCast _ _).symm
  rw [hn', ReciprocityTheory.Neutral.Cmp.card_quot_span_algebraMap (Module.finBasis ℤ_[p] (OK p K)),
    ReciprocityTheory.Neutral.Cmp.card_quot_natCast_padicInt p hn, Fintype.card_fin, hr]

end aux

attribute [local instance] zpAlgOK

variable (p : ℕ) [Fact p.Prime] {K L : IntermediateField ℚ_[p] (PadicAlgCl p)}

end

end ReciprocityTheory.DiscreteGroups.LocalClassField.Euler
