import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassMass.EquivFunLinOf

open NumberField PI.UJClassFin PI.UJClassMass Formalism.HermitianLatticesTheory Formalism.ThetaLiftIndependence
open scoped TensorProduct

noncomputable section

namespace PI.UnitaryGroupMassFormula.UJClassMass

def CrdBounds : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (V : Type) [AddCommGroup V] [Module E V] [Module (𝓞 E) V]
    [IsScalarTower (𝓞 E) E V] [FiniteDimensional E V]
    (M : ℕ) (b : Module.Basis (Fin M) E V) (L0 : Submodule (𝓞 E) V),
    Submodule.IsLattice E L0 →
    (∃ c : 𝓞 F, c ≠ 0 ∧ ∀ x ∈ crdOf b L0, ∀ i, IsIntegral ℤ ((c : F) • x i)) ∧
    (∃ c : 𝓞 F, c ≠ 0 ∧ ∀ i, ∀ e : E, IsIntegral ℤ e → Pi.single i ((c : F) • e) ∈ crdOf b L0)

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

instance nontrivialAF : Nontrivial (AF F) := by
  haveI : Nontrivial (Ainf F) := by
    first
    | exact inferInstance
    | (haveI : Nonempty (NumberField.InfinitePlace F) := inferInstance; exact Pi.nontrivial)
  first
  | exact inferInstance
  | exact inferInstanceAs (Nontrivial (Ainf F × Af F))
  | exact (Prod.nontrivial_left : Nontrivial (Ainf F × Af F))

theorem inclR_injective : Function.Injective (inclR (AF F) : E →+* AF F ⊗[F] E) :=
  Algebra.TensorProduct.includeRight_injective (R := F) (A := AF F) (B := E)
    (algebraMap F (AF F)).injective

theorem bc_injective {M : ℕ} :
    Function.Injective (bc (n := Fin M) (inclR (AF F) : E →+* AF F ⊗[F] E)) := by
  intro a a' e
  apply Units.ext
  ext i j
  have := congrArg (fun g : GL (Fin M) (AF F ⊗[F] E) => (g : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) i j) e
  exact inclR_injective this

theorem ratMat_emb (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (U : UJ (σ : E →+* E) J) :
    ratMat σ J ⟨PI.UnitaryGroupMassFormula.UJClassFin.emb σ J U, PI.UnitaryGroupMassFormula.UJClassFin.emb_mem σ J U⟩ = U :=
  bc_injective (ratMat_spec σ J _).2

end Gen

section Mat

variable {E V : Type} [Field E] [AddCommGroup V] [Module E V]

def matGL {M : ℕ} (b : Module.Basis (Fin M) E V) (u : V ≃ₗ[E] V) : GL (Fin M) E where
  val := LinearMap.toMatrix b b (u : V →ₗ[E] V)
  inv := LinearMap.toMatrix b b (u.symm : V →ₗ[E] V)
  val_inv := by
    rw [← LinearMap.toMatrix_comp, show (u : V →ₗ[E] V).comp (u.symm : V →ₗ[E] V) = LinearMap.id from
      by ext; simp, LinearMap.toMatrix_id]
  inv_val := by
    rw [← LinearMap.toMatrix_comp, show (u.symm : V →ₗ[E] V).comp (u : V →ₗ[E] V) = LinearMap.id from
      by ext; simp, LinearMap.toMatrix_id]

theorem linOf_matGL {M : ℕ} (b : Module.Basis (Fin M) E V) (u : V ≃ₗ[E] V) : linOf b (matGL b u) = u := by
  apply LinearEquiv.ext
  intro v
  change Matrix.toLin b b (LinearMap.toMatrix b b (u : V →ₗ[E] V)) v = u v
  rw [Matrix.toLin_toMatrix]
  rfl

theorem linOf_inj {M : ℕ} (b : Module.Basis (Fin M) E V) {U U' : GL (Fin M) E}
    (e : linOf b U = linOf b U') : U = U' := by
  apply Units.ext
  have := congrArg (fun w : V ≃ₗ[E] V => LinearMap.toMatrix b b (w : V →ₗ[E] V)) e
  simpa [linOf, LinearMap.toMatrix_toLin] using this

end Mat

section Gram

variable {E V : Type} [Field E] [StarRing E] [AddCommGroup V] [Module E V]

theorem gram_linOf {F : Type} [Field F] [Algebra F E] (σ : E →ₐ[F] E) (hσ : ∀ a, σ a = star a)
    (h : V →ₗ⋆[E] V →ₗ[E] E) {M : ℕ} (b : Module.Basis (Fin M) E V) (U : GL (Fin M) E) (i j : Fin M) :
    h (linOf b U (b i)) (linOf b U (b j)) =
      (cT (σ : E →+* E) (U : Matrix (Fin M) (Fin M) E) * gramOf h b * (U : Matrix (Fin M) (Fin M) E)) i j := by
  rw [linOf_basis, linOf_basis]
  simp only [map_sum, map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    Matrix.mul_apply, cT, Matrix.map_apply, Matrix.transpose_apply, gramOf, Finset.mul_sum,
    Finset.sum_mul, AlgHom.coe_toRingHom, hσ, starRingEnd_apply]
  refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ => ?_))
  simp only [RingHom.id_apply]
  ring

theorem matGL_mem {F : Type} [Field F] [Algebra F E] (σ : E →ₐ[F] E) (hσ : ∀ a, σ a = star a)
    (h : V →ₗ⋆[E] V →ₗ[E] E) {M : ℕ} (b : Module.Basis (Fin M) E V) {u : V ≃ₗ[E] V} (hu : u ∈ isom h) :
    matGL b u ∈ UJ (σ : E →+* E) (gramOf h b) := by
  show cT (σ : E →+* E) ((matGL b u : GL (Fin M) E) : Matrix (Fin M) (Fin M) E) * gramOf h b *
    ((matGL b u : GL (Fin M) E) : Matrix (Fin M) (Fin M) E) = gramOf h b
  ext i j
  rw [← gram_linOf σ hσ h b, linOf_matGL]
  exact hu (b i) (b j)

end Gram

section Sets

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {V : Type} [AddCommGroup V] [Module E V] [Module (𝓞 E) V]

theorem image_latSet (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (b : Module.Basis (Fin M) E V)
    (L0 : Submodule (𝓞 E) V) (U : GL (Fin M) E) (g : HA (AF F) σ J) :
    (linOf b U : V → V) '' latSet σ J b L0 g =
      {v | b.equivFun v ∈ (fun x => (U : Matrix (Fin M) (Fin M) E).mulVec x) ''
        PI.UnitaryGroupMassFormula.UJClassFin.abelian₂ σ J (crdOf b L0) g} := by
  ext v
  constructor
  · rintro ⟨w, hw, rfl⟩
    refine ⟨b.equivFun w, hw, ?_⟩
    rw [equivFun_linOf]
  · rintro ⟨x, hx, hxv⟩
    refine ⟨b.equivFun.symm x, ?_, ?_⟩
    · show b.equivFun (b.equivFun.symm x) ∈ PI.UnitaryGroupMassFormula.UJClassFin.abelian₂ σ J (crdOf b L0) g
      rwa [LinearEquiv.apply_symm_apply]
    · apply b.equivFun.injective
      change b.equivFun (linOf b _ _) = _
      rw [equivFun_linOf, LinearEquiv.apply_symm_apply]
      exact hxv

theorem set_of_coords_inj {M : ℕ} (b : Module.Basis (Fin M) E V) {A A' : Set (Fin M → E)}
    (e : {v : V | b.equivFun v ∈ A} = {v | b.equivFun v ∈ A'}) : A = A' := by
  ext x
  have h1 : b.equivFun.symm x ∈ {v : V | b.equivFun v ∈ A} ↔ b.equivFun.symm x ∈ {v : V | b.equivFun v ∈ A'} := by
    rw [e]
  simpa only [Set.mem_setOf_eq, LinearEquiv.apply_symm_apply] using h1

end Sets

theorem injStep_of (hR : PI.UnitaryGroupMassFormula.UJClassFin.RatDense) (hC : CrdBounds) : InjStep := by
  intro F E _ _ _ _ _ _ σ V _ _ _ _ _ h M b L0 hσ _ _ _ _ hL _ g g' u hu e
  obtain ⟨hb1, hb2⟩ := hC F E V M b L0 hL
  have hR' := hR F E σ M (gramOf h b) (crdOf b L0) hb1 hb2
  set U : UJ (σ : E →+* E) (gramOf h b) := ⟨matGL b u, matGL_mem σ hσ h b hu⟩ with hUdef
  have e1 : (linOf b (matGL b u) : V → V) '' latSet σ (gramOf h b) b L0 g' = latSet σ (gramOf h b) b L0 g := by
    rw [linOf_matGL]; exact e
  rw [image_latSet] at e1
  have e2 := set_of_coords_inj b e1
  have e3 : PI.UnitaryGroupMassFormula.UJClassFin.abelian₂ σ (gramOf h b) (crdOf b L0) (PI.UnitaryGroupMassFormula.UJClassFin.emb σ (gramOf h b) U * g') =
      PI.UnitaryGroupMassFormula.UJClassFin.abelian₂ σ (gramOf h b) (crdOf b L0) g := by
    rw [PI.UnitaryGroupMassFormula.UJClassFin.Lam_emb_mul]; exact e2
  have hk := PI.UnitaryGroupMassFormula.UJClassFin.sfin_of_Lam_eq σ (gramOf h b) (crdOf b L0) hR' _ _ e3
  refine ⟨⟨_, PI.UnitaryGroupMassFormula.UJClassFin.emb_mem σ (gramOf h b) U⟩, ⟨_, hk⟩, ?_⟩
  simp only [mul_inv_cancel_left]

theorem cardStep_of (hR : PI.UnitaryGroupMassFormula.UJClassFin.RatDense) (hC : CrdBounds) : CardStep := by
  intro F E _ _ _ _ _ _ σ V _ _ _ _ _ h M b L0 hσ hθ hτ hs hn hL hsig g
  obtain ⟨hb1, hb2⟩ := hC F E V M b L0 hL
  have hR' := hR F E σ M (gramOf h b) (crdOf b L0) hb1 hb2

  have wd : ∀ γ : stab (GamG σ (gramOf h b)) (SFin σ (gramOf h b) (crdOf b L0)) g,
      iotaG σ (gramOf h b) b γ.1 ∈ isom h ∧
        (iotaG σ (gramOf h b) b γ.1 : V → V) '' latSet σ (gramOf h b) b L0 g = latSet σ (gramOf h b) b L0 g := by
    intro γ
    refine ⟨isomStep F E σ V h M b L0 hσ hθ hτ hs hn hL hsig γ.1, ?_⟩
    have e1 := equivStep F E σ V h M b L0 hσ hθ hτ hs hn hL hsig g γ.1 1
    rw [← e1]
    have e2 : ((γ.1 : GamG σ (gramOf h b)) : HA (AF F) σ (gramOf h b)) * g *
        ((1 : SFin σ (gramOf h b) (crdOf b L0)) : HA (AF F) σ (gramOf h b)) =
        g * ((⟨_, γ.2⟩ : SFin σ (gramOf h b) (crdOf b L0)) : HA (AF F) σ (gramOf h b)) := by
      simp only [OneMemClass.coe_one, mul_one, mul_inv_cancel_left]
    rw [e2]
    show {v | b.equivFun v ∈ PI.UnitaryGroupMassFormula.UJClassFin.abelian₂ σ (gramOf h b) (crdOf b L0) (g * _)} =
      {v | b.equivFun v ∈ PI.UnitaryGroupMassFormula.UJClassFin.abelian₂ σ (gramOf h b) (crdOf b L0) g}
    rw [Lam_mul_sfin]
  let f : stab (GamG σ (gramOf h b)) (SFin σ (gramOf h b) (crdOf b L0)) g →
      {u : V ≃ₗ[E] V // u ∈ isom h ∧ (u : V → V) '' latSet σ (gramOf h b) b L0 g = latSet σ (gramOf h b) b L0 g} :=
    fun γ => ⟨iotaG σ (gramOf h b) b γ.1, wd γ⟩
  apply Nat.card_eq_of_bijective f
  refine ⟨?_, ?_⟩
  · intro γ γ' e
    have e1 : iotaG σ (gramOf h b) b γ.1 = iotaG σ (gramOf h b) b γ'.1 := congrArg Subtype.val e
    have e2 : ratMat σ (gramOf h b) γ.1 = ratMat σ (gramOf h b) γ'.1 := linOf_inj b e1
    have e3 : ratU σ (gramOf h b) γ.1 = ratU σ (gramOf h b) γ'.1 := Subtype.ext e2
    apply Subtype.ext
    apply Subtype.ext
    rw [← emb_ratU σ (gramOf h b) γ.1, ← emb_ratU σ (gramOf h b) γ'.1, e3]
  · rintro ⟨u, hu, hl⟩
    set U : UJ (σ : E →+* E) (gramOf h b) := ⟨matGL b u, matGL_mem σ hσ h b hu⟩ with hUdef
    let γ : GamG σ (gramOf h b) := ⟨PI.UnitaryGroupMassFormula.UJClassFin.emb σ (gramOf h b) U, PI.UnitaryGroupMassFormula.UJClassFin.emb_mem σ (gramOf h b) U⟩
    have hι : iotaG σ (gramOf h b) b γ = u := by
      show linOf b (ratMat σ (gramOf h b) γ) = u
      rw [ratMat_emb]
      exact linOf_matGL b u
    have e1 : (linOf b (matGL b u) : V → V) '' latSet σ (gramOf h b) b L0 g = latSet σ (gramOf h b) b L0 g := by
      rw [linOf_matGL]; exact hl
    rw [image_latSet] at e1
    have e2 := set_of_coords_inj b e1
    have e3 : PI.UnitaryGroupMassFormula.UJClassFin.abelian₂ σ (gramOf h b) (crdOf b L0) g =
        PI.UnitaryGroupMassFormula.UJClassFin.abelian₂ σ (gramOf h b) (crdOf b L0) ((γ : HA (AF F) σ (gramOf h b)) * g) := by
      rw [PI.UnitaryGroupMassFormula.UJClassFin.Lam_emb_mul]; exact e2.symm
    have hk := PI.UnitaryGroupMassFormula.UJClassFin.sfin_of_Lam_eq σ (gramOf h b) (crdOf b L0) hR' _ _ e3
    refine ⟨⟨γ, hk⟩, ?_⟩
    exact Subtype.ext hι

theorem uJClassMass_of_deep (hR : PI.UnitaryGroupMassFormula.UJClassFin.RatDense) (hC : CrdBounds) (s1 : LatStep) (s4 : SurjStep) :
    PI.UJClassMass2.UJClassMass :=
  uJClassMass_of s1 isomStep equivStep (injStep_of hR hC) s4 (cardStep_of hR hC)

end PI.UnitaryGroupMassFormula.UJClassMass

end
