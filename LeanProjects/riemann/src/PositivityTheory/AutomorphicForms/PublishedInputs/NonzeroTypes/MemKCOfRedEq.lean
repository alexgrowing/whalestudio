import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.NonzeroLeviEigenvectorExists

noncomputable section

open scoped Classical

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix

namespace UpperTheory.TNZ.Grp.P_V0fin

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def lift {n : ℕ} (g : ↥(KO k (Fin n))) : GL (Fin n) 𝒪[k] := Classical.choose g.2

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
lemma lift_spec {n : ℕ} (g : ↥(KO k (Fin n))) :
    Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) (lift g) = (g : GL (Fin n) k) :=
  Classical.choose_spec g.2

def red {n : ℕ} (r : ℕ) (g : ↥(KO k (Fin n))) :
    Matrix (Fin n) (Fin n) (𝒪[k] ⧸ IsLocalRing.maximalIdeal 𝒪[k] ^ r) :=
  ((lift g : GL (Fin n) 𝒪[k]) : Matrix (Fin n) (Fin n) 𝒪[k]).map (Ideal.Quotient.mk _)

instance finQuot (r : ℕ) : Finite (𝒪[k] ⧸ IsLocalRing.maximalIdeal 𝒪[k] ^ r) :=
  IsLocalRing.finite_quotient_iff.mpr ⟨r, le_rfl⟩

instance finRed (n r : ℕ) : Finite (Matrix (Fin n) (Fin n) (𝒪[k] ⧸ IsLocalRing.maximalIdeal 𝒪[k] ^ r)) :=
  inferInstanceAs (Finite (Fin n → Fin n → (𝒪[k] ⧸ IsLocalRing.maximalIdeal 𝒪[k] ^ r)))

lemma mem_KC_of_red_eq {n : ℕ} (r : ℕ) (g g' : ↥(KO k (Fin n))) (h : red r g = red r g') :
    ((g⁻¹ * g' : ↥(KO k (Fin n))) : GL (Fin n) k) ∈ KC k n r := by
  refine ⟨(g⁻¹ * g').2, fun i j => ?_⟩
  have hu : ((g⁻¹ * g' : ↥(KO k (Fin n))) : GL (Fin n) k) =
      Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) ((lift g)⁻¹ * lift g') := by
    rw [map_mul, map_inv, lift_spec, lift_spec]; rfl
  have hd : ∀ l m, ((lift g' : GL (Fin n) 𝒪[k]) : Matrix (Fin n) (Fin n) 𝒪[k]) l m -
      ((lift g : GL (Fin n) 𝒪[k]) : Matrix (Fin n) (Fin n) 𝒪[k]) l m ∈ IsLocalRing.maximalIdeal 𝒪[k] ^ r := by
    intro l m
    have := congrFun (congrFun h l) m
    simp only [red, Matrix.map_apply] at this
    exact Ideal.Quotient.eq.mp this.symm
  have hM : (((lift g)⁻¹ * lift g' : GL (Fin n) 𝒪[k]) : Matrix (Fin n) (Fin n) 𝒪[k]) =
      1 + ((lift g)⁻¹ : GL (Fin n) 𝒪[k]).val *
        ((lift g' : GL (Fin n) 𝒪[k]).val - (lift g : GL (Fin n) 𝒪[k]).val) := by
    rw [Units.val_mul, Matrix.mul_sub, Units.inv_mul]; abel
  refine ⟨(((lift g)⁻¹ * lift g' : GL (Fin n) 𝒪[k]) : Matrix (Fin n) (Fin n) 𝒪[k]) i j -
      if i = j then 1 else 0, ?_, ?_⟩
  · rw [hM, Matrix.add_apply, Matrix.one_apply, add_sub_cancel_left, Matrix.mul_apply]
    exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_left _ _ (hd l j)
  · rw [hu]
    change _ = ((((lift g)⁻¹ * lift g' : GL (Fin n) 𝒪[k]) : Matrix (Fin n) (Fin n) 𝒪[k]).map
      (algebraMap 𝒪[k] k)) i j - _
    simp only [Matrix.map_apply, map_sub, apply_ite (algebraMap 𝒪[k] k), map_one, map_zero]

end P_V0fin

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem step_V0fin {n : ℕ} (G : Grp k n) : FixedSubspaceFiniteProp G := by
  intro _ _
  let φ := P_V0fin.red (k := k) (n := n) G.lev
  have hle : G.V0sp ≤ LinearMap.range (LinearMap.funLeft ℂ ℂ φ) := by
    intro f hf
    refine ⟨fun q => if hq : ∃ g, φ g = q then f (Classical.choose hq) else 0, ?_⟩
    funext g
    have hq : ∃ g', φ g' = φ g := ⟨g, rfl⟩
    simp only [LinearMap.funLeft_apply, dif_pos hq]
    have hk := P_V0fin.mem_KC_of_red_eq G.lev (Classical.choose hq) g (Classical.choose_spec hq)
    have := hf.2 (Classical.choose hq) ((Classical.choose hq)⁻¹ * g) hk
    rw [mul_inv_cancel_left] at this
    exact this.symm
  have : FiniteDimensional ℂ (LinearMap.range (LinearMap.funLeft ℂ ℂ φ)) :=
    LinearMap.finiteDimensional_range _
  exact Submodule.finiteDimensional_of_le hle

end UpperTheory.TNZ.Grp
