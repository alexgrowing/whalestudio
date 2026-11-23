import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassMass.Development

open NumberField PI.UJClassFin PI.UJClassMass Formalism.HermitianLatticesTheory Formalism.ThetaLiftIndependence

noncomputable section

namespace PI.UnitaryGroupMassFormula.UJClassMass

section Rat

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem ratMat_spec (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (γ : GamG σ J) :
    ratMat σ J γ ∈ UJ (σ : E →+* E) J ∧
      bc (inclR (AF F)) (ratMat σ J γ) = (γ.1 : HR (AF F) σ J).1 := by
  unfold ratMat
  first
  | exact Classical.choose_spec (p := fun m => m ∈ UJ (σ : E →+* E) J ∧
      bc (inclR (AF F)) m = (γ.1 : HR (AF F) σ J).1) _
  | (generalize_proofs h1 h2 h3 h4 h5 h6
     first
     | exact Classical.choose_spec h4
     | exact Classical.choose_spec h5
     | exact Classical.choose_spec h6
     | exact Classical.choose_spec h1)

def ratU (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (γ : GamG σ J) :
    UJ (σ : E →+* E) J :=
  ⟨ratMat σ J γ, (ratMat_spec σ J γ).1⟩

theorem emb_ratU (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (γ : GamG σ J) :
    PI.UnitaryGroupMassFormula.UJClassFin.emb σ J (ratU σ J γ) = (γ : HA (AF F) σ J) := by
  exact Subtype.ext (ratMat_spec σ J γ).2

theorem Lam_mul_sfin (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (L : Set (Fin M → E))
    (g : HA (AF F) σ J) (k : SFin σ J L) :
    PI.UnitaryGroupMassFormula.UJClassFin.abelian₂ σ J L (g * k) = PI.UnitaryGroupMassFormula.UJClassFin.abelian₂ σ J L g := by
  have hk : ∀ y, y ∈ latHat F E L ↔
      (finMat σ J ((k : HA (AF F) σ J)⁻¹)).mulVec y ∈ latHat F E L := (k⁻¹).2
  ext x
  simp only [UJClassFin.abelian₂, Set.mem_setOf_eq, mul_inv_rev]
  unfold finMat at hk ⊢
  unfold HA.mat at hk ⊢
  simp only [Subgroup.coe_mul, Units.val_mul, ← AlgHom.mapMatrix_apply, map_mul] at hk ⊢
  have e : ∀ a c : HA (AF F) σ J, (a * c).1 = a.1 * c.1 := fun a c => rfl
  rw [e, Units.val_mul, map_mul]
  simp only [AlgHom.mapMatrix_apply, ← Matrix.mulVec_mulVec] at hk ⊢
  exact (hk _).symm

end Rat

section Coord

variable {E V : Type} [Field E] [AddCommGroup V] [Module E V]

theorem equivFun_linOf {M : ℕ} (b : Module.Basis (Fin M) E V) (u : GL (Fin M) E) (v : V) :
    b.equivFun (linOf b u v) = (u : Matrix (Fin M) (Fin M) E).mulVec (b.equivFun v) := by
  unfold linOf
  first
  | simp only [LinearEquiv.ofLinear_apply, Matrix.toLin_apply, Basis.equivFun_apply,
      Basis.repr_sum_self]
  | simp [Matrix.toLin_apply, Basis.repr_sum_self]
  | (simp [Matrix.toLin_apply]
     ext j
     simp [Finset.sum_apply, Finsupp.single_apply])

theorem linOf_basis {M : ℕ} (b : Module.Basis (Fin M) E V) (u : GL (Fin M) E) (i : Fin M) :
    linOf b u (b i) = ∑ k, (u : Matrix (Fin M) (Fin M) E) k i • b k := by
  unfold linOf
  first
  | simp [Matrix.toLin_self]
  | rw [LinearEquiv.ofLinear_apply, Matrix.toLin_self]

end Coord

theorem isomStep : IsomStep := by
  unfold IsomStep
  intro F E _ _ _ _ _ _ σ V _ _ _ _ _ h M b L0 hσ hθ hτ hsymm hnd hlat hsig γ
  unfold iotaG isom
  set u := ratMat σ (gramOf h b) γ with hu
  have hU : Formalism.UG.cT (σ : E →+* E) (u : Matrix (Fin M) (Fin M) E) * gramOf h b *
      (u : Matrix (Fin M) (Fin M) E) = gramOf h b := (ratMat_spec σ (gramOf h b) γ).1
  have hG : ∀ k l, gramOf h b k l = h (b k) (b l) := fun k l => rfl
  have key : (h.comp (linOf b u : V →ₗ[E] V)).compl₂ (linOf b u : V →ₗ[E] V) = h := by
    refine LinearMap.ext_basis b b fun i j => ?_
    simp only [LinearMap.compl₂_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, linOf_basis]
    rw [show h (b i) (b j) = gramOf h b i j from (hG i j).symm, ← hU]
    simp only [Matrix.mul_apply, Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply, hG,
      AlgHom.coe_toRingHom, RingHom.coe_coe, hσ, Finset.sum_mul, Finset.mul_sum, map_sum,
      map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply,
      RingHom.id_apply]
    first
    | exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring
    | (rw [Finset.sum_comm]
       exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring)
  show ∀ x y, h (linOf b u x) (linOf b u y) = h x y
  intro x y
  conv_rhs => rw [← key]
  rfl

theorem equivStep : EquivStep := by
  intro F E _ _ _ _ _ _ σ V _ _ _ _ _ h M b L0 _ _ _ _ _ _ _ g γ k
  ext v
  change b.equivFun v ∈ PI.UnitaryGroupMassFormula.UJClassFin.abelian₂ σ (gramOf h b) (crdOf b L0)
      ((γ : HA (AF F) σ (gramOf h b)) * g * (k : HA (AF F) σ (gramOf h b))) ↔
    v ∈ (iotaG σ (gramOf h b) b γ : V → V) '' latSet σ (gramOf h b) b L0 g
  rw [Lam_mul_sfin, ← emb_ratU, PI.UnitaryGroupMassFormula.UJClassFin.Lam_emb_mul]
  constructor
  · rintro ⟨x, hx, hxv⟩
    refine ⟨b.equivFun.symm x, ?_, ?_⟩
    · show b.equivFun (b.equivFun.symm x) ∈ PI.UnitaryGroupMassFormula.UJClassFin.abelian₂ σ (gramOf h b) (crdOf b L0) g
      rwa [LinearEquiv.apply_symm_apply]
    · apply b.equivFun.injective
      change b.equivFun (linOf b _ _) = _
      rw [equivFun_linOf, LinearEquiv.apply_symm_apply]
      exact hxv
  · rintro ⟨w, hw, rfl⟩
    refine ⟨b.equivFun w, hw, ?_⟩
    change _ = b.equivFun (linOf b _ _)
    rw [equivFun_linOf]
    rfl

end PI.UnitaryGroupMassFormula.UJClassMass

end
