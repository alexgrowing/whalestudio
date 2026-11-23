import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.DualLiftInjective

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj

namespace ReciprocityTheory.ChartRestriction.G.Chart

attribute [local instance] Over.cartesianMonoidalCategory

variable {R : Type} [CommRing R]

theorem spMap_id (P : Type) [CommRing P] [Algebra R P] : spMap (AlgHom.id R P) = 𝟙 (sp (R₀ := R) P) := by
  apply Over.OverMorphism.ext
  simp only [spMap_left, Over.id_left]
  exact Spec.map_id _

def qD (i : Fin 2) : DualNumber R →ₐ[R] JetR R (Fin 2) 1 :=
  TrivSqZeroExt.lift (Algebra.ofId R _) (LinearMap.toSpanSingleton R _ (zR 1 i))
    (fun a b => by
      simp only [LinearMap.toSpanSingleton_apply]
      rw [smul_mul_smul_comm]
      have : zR (R := R) 1 i * zR 1 i = 0 := by
        show Ideal.Quotient.mk _ (MvPolynomial.X i * MvPolynomial.X i) = 0
        rw [Ideal.Quotient.eq_zero_iff_mem, pow_two]
        exact Ideal.mul_mem_mul (Ideal.subset_span ⟨i, rfl⟩) (Ideal.subset_span ⟨i, rfl⟩)
      rw [this, smul_zero])
    (fun r a => by
      simp only [LinearMap.toSpanSingleton_apply, Algebra.smul_def, map_mul, Algebra.ofId_apply,
        Algebra.algebraMap_self, RingHom.id_apply]
      ring)
    (fun r a => by
      simp only [LinearMap.toSpanSingleton_apply, Algebra.smul_def, MulOpposite.smul_eq_mul_unop,
        MulOpposite.unop_op, map_mul, Algebra.ofId_apply, Algebra.algebraMap_self, RingHom.id_apply]
      ring)

theorem qD_apply (i : Fin 2) (a : DualNumber R) :
    qD i a = algebraMap R _ a.fst + a.snd • zR (R := R) 1 i := rfl

theorem jetAug_comp_qD (i : Fin 2) : (jetAug R (Fin 2) 1).comp (qD i) = fstD R := by
  ext a
  rw [AlgHom.comp_apply, qD_apply, map_add, map_smul, AlgHom.commutes, jetAug_zR, smul_zero, add_zero]
  rfl

theorem delta_sq : (RingHom.ker (TrivSqZeroExt.fstHom R R (R × R))) ^ (1 + 1) = ⊥ := by
  rw [← le_bot_iff, pow_two, Ideal.mul_le]
  intro a ha b hb
  have ha0 : a.fst = 0 := ha
  have hb0 : b.fst = 0 := hb
  rw [Ideal.mem_bot, show a = TrivSqZeroExt.inr a.snd from TrivSqZeroExt.ext ha0 rfl,
    show b = TrivSqZeroExt.inr b.snd from TrivSqZeroExt.ext hb0 rfl, TrivSqZeroExt.inr_mul_inr]

def deltaJ : JetR R (Fin 2) 1 →ₐ[R] TrivSqZeroExt R (R × R) :=
  jetLift R (RingHom.ker (TrivSqZeroExt.fstHom R R (R × R))) delta_sq
    (fun i => TrivSqZeroExt.inr (if i = 0 then ((1 : R), (0 : R)) else (0, 1)))
    (fun i => (RingHom.mem_ker).mpr rfl)

def rD (l : R × R →ₗ[R] R) : JetR R (Fin 2) 1 →ₐ[R] DualNumber R :=
  (TrivSqZeroExt.map l).comp deltaJ

theorem rD_zR (l : R × R →ₗ[R] R) (i : Fin 2) :
    rD l (zR 1 i) = TrivSqZeroExt.inr (l (if i = 0 then ((1 : R), (0 : R)) else (0, 1))) := by
  rw [rD, AlgHom.comp_apply, deltaJ, jetLift_zR, TrivSqZeroExt.map_inr]

theorem snd_rD_add (a : JetR R (Fin 2) 1) :
    (rD (LinearMap.fst R R R + LinearMap.snd R R R) a).snd =
      (rD (LinearMap.fst R R R) a).snd + (rD (LinearMap.snd R R R) a).snd := by
  simp only [rD, AlgHom.comp_apply, TrivSqZeroExt.snd_map, LinearMap.add_apply]

theorem fstD_comp_rD (l : R × R →ₗ[R] R) : (fstD R).comp (rD l) = jetAug R (Fin 2) 1 :=
  jet_ext fun i => by
    rw [AlgHom.comp_apply, rD_zR, jetAug_zR]
    exact inr_mem_kerD _

theorem rD_comp_qD (l : R × R →ₗ[R] R) (i : Fin 2) :
    (rD l).comp (qD i) = TrivSqZeroExt.map ((l (if i = 0 then ((1 : R), (0 : R)) else (0, 1))) • LinearMap.id) := by
  apply DualNumber.algHom_ext
  rw [AlgHom.comp_apply, qD_apply]
  simp only [DualNumber.fst_eps, DualNumber.snd_eps, map_zero, one_smul, zero_add, rD_zR]
  show _ = TrivSqZeroExt.map _ (TrivSqZeroExt.inr 1)
  rw [TrivSqZeroExt.map_inr, LinearMap.smul_apply, LinearMap.id_apply, smul_eq_mul, _root_.mul_one]

variable {G : Over (Spec (CommRingCat.of R))} [GrpObj G]

theorem isTan_mul {w₁ w₂ : sp (R₀ := R) (DualNumber R) ⟶ G} (h₁ : IsTan w₁) (h₂ : IsTan w₂) : IsTan (w₁ * w₂) := by
  rw [IsTan, MonObj.comp_mul, h₁, h₂, _root_.mul_one]

theorem isTan_one : IsTan (1 : sp (R₀ := R) (DualNumber R) ⟶ G) := comp_one' _

abbrev scaleD (c : R) : DualNumber R →ₐ[R] DualNumber R := TrivSqZeroExt.map (c • LinearMap.id)

theorem isTan_scale (c : R) {w : sp (R₀ := R) (DualNumber R) ⟶ G} (h : IsTan w) : IsTan (spMap (scaleD c) ≫ w) := by
  have : (fstD R).comp (scaleD c) = fstD R := by
    ext
    exact TrivSqZeroExt.fst_map _ _
  rw [IsTan, ← Category.assoc, spMap_comp, this]
  exact h

theorem scaleD_one : scaleD (1 : R) = AlgHom.id R (DualNumber R) := by
  apply DualNumber.algHom_ext
  show TrivSqZeroExt.map _ (TrivSqZeroExt.inr 1) = TrivSqZeroExt.inr 1
  rw [TrivSqZeroExt.map_inr, one_smul, LinearMap.id_apply]

theorem scaleD_zero : scaleD (0 : R) = (Algebra.ofId R (DualNumber R)).comp (fstD R) := by
  apply DualNumber.algHom_ext
  show TrivSqZeroExt.map _ (TrivSqZeroExt.inr 1) = (Algebra.ofId R (DualNumber R)) ((TrivSqZeroExt.inr (1 : R) : DualNumber R).fst)
  rw [TrivSqZeroExt.map_inr, zero_smul, LinearMap.zero_apply, TrivSqZeroExt.fst_inr, map_zero, TrivSqZeroExt.inr_zero]

theorem spMap_scaleD_zero {w : sp (R₀ := R) (DualNumber R) ⟶ G} (h : IsTan w) : spMap (scaleD (0 : R)) ≫ w = 1 := by
  rw [scaleD_zero, ← spMap_comp, Category.assoc, h, comp_one']

theorem restrictDiag_comp_incl_fst (l : R × R →ₗ[R] R) : (rD l).comp (qD 0) = scaleD (l ((1 : R), (0 : R))) := by
  rw [rD_comp_qD]; simp

theorem restrictDiag_comp_incl_snd (l : R × R →ₗ[R] R) : (rD l).comp (qD 1) = scaleD (l ((0 : R), (1 : R))) := by
  rw [rD_comp_qD]; simp

variable {n : ℕ} {x : ∀ m : ℕ, sp (R₀ := R) (JetR R (Fin n) m) ⟶ G} (hx : IsUnivChart G n x)

theorem tcoord_mul {w₁ w₂ : sp (R₀ := R) (DualNumber R) ⟶ G} (h₁ : IsTan w₁) (h₂ : IsTan w₂) :
    tcoord hx (w₁ * w₂) (isTan_mul h₁ h₂) = tcoord hx w₁ h₁ + tcoord hx w₂ h₂ := by
  let P : sp (R₀ := R) (JetR R (Fin 2) 1) ⟶ G := (spMap (qD 0) ≫ w₁) * (spMap (qD 1) ≫ w₂)
  have hP : spMap (jetAug R (Fin 2) 1) ≫ P = 1 := by
    rw [MonObj.comp_mul, ← Category.assoc, ← Category.assoc, spMap_comp, spMap_comp, jetAug_comp_qD,
      jetAug_comp_qD, h₁, h₂, _root_.mul_one]
  obtain ⟨ψ, ⟨hψ1, hψ2⟩, -⟩ := hx.2.2 _ (jetAug R (Fin 2) 1) 1 (ker_jetAug_pow (Fin 2) 1) P hP
  have key : ∀ l : R × R →ₗ[R] R,
      spMap (rD l) ≫ P = spMap (dualLift (fun j => (rD l (ψ (zR 1 j))).snd)) ≫ x 1 := by
    intro l
    rw [hψ2, ← Category.assoc, spMap_comp,
      eq_dualLift ((rD l).comp ψ) (by rw [← AlgHom.comp_assoc, fstD_comp_rD, hψ1])]
    rfl
  have hval : ∀ l : R × R →ₗ[R] R,
      spMap (rD l) ≫ P = (spMap (scaleD (l ((1 : R), (0 : R)))) ≫ w₁) * (spMap (scaleD (l ((0 : R), (1 : R)))) ≫ w₂) := by
    intro l
    rw [MonObj.comp_mul, ← Category.assoc, ← Category.assoc, spMap_comp, spMap_comp, restrictDiag_comp_incl_fst, restrictDiag_comp_incl_snd]
  have e1 : w₁ = spMap (dualLift (fun j => (rD (LinearMap.fst R R R) (ψ (zR 1 j))).snd)) ≫ x 1 := by
    rw [← key, hval]
    simp only [LinearMap.fst_apply, LinearMap.snd_apply]
    rw [scaleD_one, spMap_id, Category.id_comp, spMap_scaleD_zero h₂, _root_.mul_one]
  have e2 : w₂ = spMap (dualLift (fun j => (rD (LinearMap.snd R R R) (ψ (zR 1 j))).snd)) ≫ x 1 := by
    rw [← key, hval]
    simp only [LinearMap.fst_apply, LinearMap.snd_apply]
    rw [scaleD_one, spMap_id, Category.id_comp, spMap_scaleD_zero h₁, _root_.one_mul]
  have e12 : w₁ * w₂ = spMap (dualLift (fun j =>
      (rD (LinearMap.fst R R R + LinearMap.snd R R R) (ψ (zR 1 j))).snd)) ≫ x 1 := by
    rw [← key, hval]
    simp only [LinearMap.add_apply, LinearMap.fst_apply, LinearMap.snd_apply, add_zero, zero_add]
    rw [scaleD_one, spMap_id, Category.id_comp, Category.id_comp]
  rw [tcoord_eq hx _ _ _ e12, tcoord_eq hx _ _ _ e1, tcoord_eq hx _ _ _ e2]
  funext j
  exact snd_rD_add _

theorem tcoord_scale (c : R) {w : sp (R₀ := R) (DualNumber R) ⟶ G} (h : IsTan w) :
    tcoord hx (spMap (scaleD c) ≫ w) (isTan_scale c h) = c • tcoord hx w h := by
  apply tcoord_eq
  conv_lhs => rw [tcoord_spec hx w h]
  rw [← Category.assoc, spMap_comp]
  congr 2
  apply jet_ext
  intro j
  rw [AlgHom.comp_apply, dualLift_zR, dualLift_zR, TrivSqZeroExt.map_inr, LinearMap.smul_apply,
    LinearMap.id_apply, Pi.smul_apply]

theorem tcoord_one : tcoord hx (1 : sp (R₀ := R) (DualNumber R) ⟶ G) isTan_one = 0 := by
  apply tcoord_eq
  have : dualLift (R := R) (0 : Fin n → R) = (Algebra.ofId R (DualNumber R)).comp (jetAug R (Fin n) 1) :=
    jet_ext fun j => by
      rw [dualLift_zR, AlgHom.comp_apply, jetAug_zR, map_zero, Pi.zero_apply, TrivSqZeroExt.inr_zero]
  rw [this, ← spMap_comp, Category.assoc, spMap_jetAug_alt hx, comp_one']

end ReciprocityTheory.ChartRestriction.G.Chart
