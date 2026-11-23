import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TangentBijectionOfValues
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueTangentLift
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PushEquivSymmLeft
import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.IsLocallyConstantRankAtStalkEigenSub
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.TateIsoExistsLiftOfTwoData

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

noncomputable section

namespace GlobalTheory.PointUnif

section Deriv

open GlobalTheory.TangentOrigin GlobalTheory.LieEtale

variable {g g' : ℕ} {X Y : Scheme.{0}}

theorem evalPt_comp {R : Type} [CommRing R] (x : Sp R ⟶ X) (φ : X ⟶ Y) (U : Y.Opens)
    (h : ⊤ ≤ (x ≫ φ) ⁻¹ᵁ U) (f : Γ(Y, U)) :
    evalPt (x ≫ φ) U h f = evalPt x (φ ⁻¹ᵁ U) h ((φ.app U).hom f) := by
  have := Scheme.Hom.appLE_comp_appLE x φ U (φ ⁻¹ᵁ U) ⊤ le_rfl h
  unfold evalPt
  rw [← this, Scheme.Hom.app_eq_appLE]
  rfl

theorem valAt'_comp (x : Sp ℂ ⟶ X) (φ : X ⟶ Y) (U : Y.Opens) (f : Γ(Y, U)) :
    valAt' (x ≫ φ) U f = valAt' x (φ ⁻¹ᵁ U) ((φ.app U).hom f) := by
  by_cases h : ⊤ ≤ (x ≫ φ) ⁻¹ᵁ U
  · rw [valAt'_eq_evalPt _ _ h, valAt'_eq_evalPt x (φ ⁻¹ᵁ U) h, evalPt_comp]
  · have h' : ¬ ⊤ ≤ x ⁻¹ᵁ φ ⁻¹ᵁ U := h
    unfold valAt'
    rw [dif_neg h, dif_neg h']

theorem isHolTo_comp {e : (Fin g → ℂ) → (Sp ℂ ⟶ X)} (he : IsHolTo Set.univ e) (φ : X ⟶ Y) :
    IsHolTo Set.univ fun z => e z ≫ φ := by
  intro U f
  simp only [valAt'_comp]
  exact he (φ ⁻¹ᵁ U) ((φ.app U).hom f)

theorem isHolTo_linear {e : (Fin g → ℂ) → (Sp ℂ ⟶ X)} (he : IsHolTo Set.univ e)
    (F : (Fin g' → ℂ) →ₗ[ℂ] (Fin g → ℂ)) : IsHolTo Set.univ fun z => e (F z) := by
  intro U f
  have hF : Differentiable ℂ F := F.toContinuousLinearMap.differentiable
  exact ⟨(he U f).1.preimage hF.continuous, (he U f).2.comp hF.differentiableOn fun z hz => hz⟩

theorem isDerivAt0_iff {e : (Fin g → ℂ) → (Sp ℂ ⟶ X)} {w : Fin g → ℂ} {v : Sp (DualNumber ℂ) ⟶ X} :
    IsDerivAt0 e w v ↔ spMap fstC ≫ v = e 0 ∧ ∀ (U : X.Opens) (h : ⊤ ≤ v ⁻¹ᵁ U) (f : Γ(X, U)),
      (evalPt v U h f).snd = fderiv ℂ (fun z => valAt' (e z) U f) 0 w := Iff.rfl

theorem deriv_comp {e : (Fin g → ℂ) → (Sp ℂ ⟶ X)} {w : Fin g → ℂ} {v : Sp (DualNumber ℂ) ⟶ X}
    (h : IsDerivAt0 e w v) (φ : X ⟶ Y) : IsDerivAt0 (fun z => e z ≫ φ) w (v ≫ φ) := by
  rw [isDerivAt0_iff] at h ⊢
  refine ⟨by rw [← h.1, Category.assoc], fun U hU f => ?_⟩
  simp only [valAt'_comp]
  rw [evalPt_comp]
  exact h.2 _ _ _

theorem deriv_unique {e : (Fin g → ℂ) → (Sp ℂ ⟶ X)} {w : Fin g → ℂ} {v v' : Sp (DualNumber ℂ) ⟶ X}
    (h : IsDerivAt0 e w v) (h' : IsDerivAt0 e w v') : v = v' := by
  rw [isDerivAt0_iff] at h h'
  obtain ⟨_, ⟨U, hU, rfl⟩, hx, -⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (e 0 (default : PrimeSpectrum ℂ))) isOpen_univ
  have h0 : ⊤ ≤ e 0 ⁻¹ᵁ U := fun q _ => by
    rw [Subsingleton.elim (α := PrimeSpectrum ℂ) q default]; exact hx
  have hv : ⊤ ≤ v ⁻¹ᵁ U := (top_le_preimage_iff v U).2 (h.1 ▸ h0)
  have hv' : ⊤ ≤ v' ⁻¹ᵁ U := (top_le_preimage_iff v' U).2 (h'.1 ▸ h0)
  refine ext_evalPt hU hv hv' (RingHom.ext fun f => TrivSqZeroExt.ext ?_ ((h.2 U hv f).trans (h'.2 U hv' f).symm))
  have key : ∀ (u : Sp (DualNumber ℂ) ⟶ X) (hu : ⊤ ≤ u ⁻¹ᵁ U) (y : Sp ℂ ⟶ X) (hy : ⊤ ≤ y ⁻¹ᵁ U),
      spMap fstC ≫ u = y → (evalPt u U hu f).fst = evalPt y U hy f := by
    rintro u hu y hy rfl
    exact (evalPt_spMap_comp fstC u U hu hy f).symm
  exact (key v hv _ h0 h.1).trans (key v' hv' _ h0 h'.1).symm

theorem deriv_linear {e : (Fin g → ℂ) → (Sp ℂ ⟶ X)} (he : IsHolTo Set.univ e)
    (F : (Fin g' → ℂ) →ₗ[ℂ] (Fin g → ℂ)) {w : Fin g' → ℂ} {v : Sp (DualNumber ℂ) ⟶ X} :
    IsDerivAt0 (fun z => e (F z)) w v ↔ IsDerivAt0 e (F w) v := by
  rw [isDerivAt0_iff, isDerivAt0_iff, map_zero]
  refine and_congr_right fun h0 => forall₃_congr fun U hU f => ?_
  have hU0 : ⊤ ≤ e 0 ⁻¹ᵁ U := h0 ▸ (top_le_preimage_iff v U).1 hU
  have hd : DifferentiableAt ℂ (fun z => valAt' (e z) U f) (F.toContinuousLinearMap 0) := by
    rw [map_zero]
    exact (he U f).2.differentiableAt ((he U f).1.mem_nhds ⟨trivial, hU0⟩)
  have := (hd.hasFDerivAt.comp 0 F.toContinuousLinearMap.hasFDerivAt).fderiv
  rw [map_zero] at this
  have e2 : fderiv ℂ (fun z => valAt' (e (F z)) U f) 0 = _ := this
  rw [e2]
  rfl

theorem deriv_smul {e : (Fin g → ℂ) → (Sp ℂ ⟶ X)} {w : Fin g → ℂ} {v : Sp (DualNumber ℂ) ⟶ X}
    (h : IsDerivAt0 e w v) (c : ℂ) : IsDerivAt0 e (c • w) (spMap (epsScale c) ≫ v) := by
  rw [isDerivAt0_iff] at h ⊢
  have e0 : spMap fstC ≫ spMap (epsScale c) ≫ v = spMap fstC ≫ v := by
    rw [← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp]
    congr 3
    exact RingHom.ext fun r => TrivSqZeroExt.fst_map _ r
  refine ⟨e0.trans h.1, fun U hU f => ?_⟩
  have hv : ⊤ ≤ v ⁻¹ᵁ U := (top_le_preimage_iff v U).2 (e0 ▸ (top_le_preimage_iff _ U).1 hU)
  rw [evalPt_spMap_comp _ v U hv hU, map_smul, ← h.2 U hv f]
  simp [epsScale]

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] {y : Sp ℂ ⟶ S}

abbrev epsTwo (y : Sp ℂ ⟶ S) : Over S := Over.mk (spMap (algebraMap ℂ (TrivSqZeroExt ℂ (ℂ × ℂ))) ≫ y)

def toTwo (y : Sp ℂ ⟶ S) (l : ℂ →ₗ[ℂ] ℂ × ℂ) : epsTwo y ⟶ epsPt y :=
  Over.homMk (spMap (TrivSqZeroExt.map l).toRingHom) (by
    change _ ≫ _ ≫ y = _ ≫ y
    rw [← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp]
    congr 3
    exact RingHom.ext fun r => (TrivSqZeroExt.map l).commutes r)

def ofTwo (y : Sp ℂ ⟶ S) (l : ℂ × ℂ →ₗ[ℂ] ℂ) : epsPt y ⟶ epsTwo y :=
  Over.homMk (spMap (TrivSqZeroExt.map l).toRingHom) (by
    change _ ≫ _ ≫ y = _ ≫ y
    rw [← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp]
    congr 3
    exact RingHom.ext fun r => (TrivSqZeroExt.map l).commutes r)

theorem ofTwo_toTwo (l : ℂ →ₗ[ℂ] ℂ × ℂ) (l' : ℂ × ℂ →ₗ[ℂ] ℂ) :
    ofTwo y l' ≫ toTwo y l = epsPtScale y (l' (l 1)) := by
  refine Over.OverMorphism.ext ?_
  change spMap _ ≫ spMap _ = spMap _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  refine RingHom.ext fun x => ?_
  have : l' (l x.snd) = l' (l 1) * x.snd := by
    rw [mul_comm, ← smul_eq_mul, ← map_smul, ← map_smul, smul_eq_mul, _root_.mul_one]
  ext <;> simp [this, epsScale]

theorem epsPtScale_one : epsPtScale y 1 = 𝟙 _ := by
  refine Over.OverMorphism.ext ?_
  change spMap _ = 𝟙 _
  rw [← Spec.map_id]
  congr 1
  ext x <;> simp [epsScale]

theorem epsPtScale_zero {v : epsPt y ⟶ G} (hv : epsPtZero y ≫ v = 1) : epsPtScale y 0 ≫ v = 1 := by
  let s : epsPt y ⟶ Over.mk y := Over.homMk (spMap (algebraMap ℂ (DualNumber ℂ))) rfl
  have : epsPtScale y 0 = s ≫ epsPtZero y := by
    refine Over.OverMorphism.ext ?_
    change spMap _ = spMap _ ≫ spMap _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    refine RingHom.ext fun x => ?_
    ext <;> simp [epsScale, TrivSqZeroExt.algebraMap_eq_inl]
  rw [this, Category.assoc, hv, MonObj.comp_one]

theorem deriv_mul {e : (Fin g → ℂ) → (Sp ℂ ⟶ G.left)} {w w' : Fin g → ℂ} {v v' : epsPt y ⟶ G}
    (h0 : e 0 = (1 : Over.mk y ⟶ G).left)
    (h : IsDerivAt0 e w v.left) (h' : IsDerivAt0 e w' v'.left) : IsDerivAt0 e (w + w') (v * v').left := by
  have hv : epsPtZero y ≫ v = 1 := Over.OverMorphism.ext (h.1.trans h0)
  have hv' : epsPtZero y ≫ v' = 1 := Over.OverMorphism.ext (h'.1.trans h0)
  have hm : epsPtZero y ≫ (v * v') = 1 := by rw [MonObj.comp_mul, hv, hv', _root_.mul_one]
  have hm' : spMap fstC ≫ (v * v').left = e 0 := (congrArg (·.left) hm).trans h0.symm
  rw [isDerivAt0_iff] at h h' ⊢
  refine ⟨hm', fun U hU f => ?_⟩
  let u : epsTwo y ⟶ G := (toTwo y (LinearMap.inl ℂ ℂ ℂ) ≫ v) * (toTwo y (LinearMap.inr ℂ ℂ ℂ) ≫ v')
  have hu : ∀ l, ofTwo y l ≫ u = (epsPtScale y (l (1, 0)) ≫ v) * (epsPtScale y (l (0, 1)) ≫ v') := fun l => by
    simp only [u, MonObj.comp_mul, ← Category.assoc, ofTwo_toTwo]
    rfl
  have h1 : ofTwo y (LinearMap.fst ℂ ℂ ℂ) ≫ u = v := by
    rw [hu, LinearMap.fst_apply, LinearMap.fst_apply, epsPtScale_one, epsPtScale_zero hv', _root_.mul_one, Category.id_comp]
  have h2 : ofTwo y (LinearMap.snd ℂ ℂ ℂ) ≫ u = v' := by
    rw [hu, LinearMap.snd_apply, LinearMap.snd_apply, epsPtScale_one, epsPtScale_zero hv, _root_.one_mul, Category.id_comp]
  have h3 : ofTwo y (LinearMap.fst ℂ ℂ ℂ + LinearMap.snd ℂ ℂ ℂ) ≫ u = v * v' := by
    rw [hu]; simp [epsPtScale_one]
  have hU0 : ⊤ ≤ e 0 ⁻¹ᵁ U := hm' ▸ (top_le_preimage_iff _ U).1 hU
  have hU1 : ⊤ ≤ v.left ⁻¹ᵁ U := (top_le_preimage_iff _ U).2 (h.1 ▸ hU0)
  have hU2 : ⊤ ≤ v'.left ⁻¹ᵁ U := (top_le_preimage_iff _ U).2 (h'.1 ▸ hU0)
  have hsub : ∀ p q : PrimeSpectrum (TrivSqZeroExt ℂ (ℂ × ℂ)), p = q := by
    have k : ∀ z : PrimeSpectrum (TrivSqZeroExt ℂ (ℂ × ℂ)), ∀ a, a ∈ z.asIdeal ↔ a.fst = 0 := fun z a => by
      constructor
      · intro ha
        by_contra h0
        exact z.2.ne_top (z.asIdeal.eq_top_of_isUnit_mem ha (TrivSqZeroExt.isUnit_iff_isUnit_fst.2 (Ne.isUnit h0)))
      · intro ha
        refine z.2.mem_of_pow_mem 2 ?_
        rw [show a ^ 2 = 0 by ext <;> simp [pow_two, ha]]
        exact z.asIdeal.zero_mem
    intro p q
    ext a
    rw [k, k]
  have hUu : ⊤ ≤ u.left ⁻¹ᵁ U := fun p _ => by
    let q : (epsPt y).left := spMap fstC (default : PrimeSpectrum ℂ)
    have hq : v.left q ∈ U := hU1 (Set.mem_univ q)
    rw [← h1] at hq
    rw [hsub p ((ofTwo y (LinearMap.fst ℂ ℂ ℂ)).left q)]
    exact hq
  have key : ∀ (l : ℂ × ℂ →ₗ[ℂ] ℂ) (x : epsPt y ⟶ G) (hx : ⊤ ≤ x.left ⁻¹ᵁ U), ofTwo y l ≫ u = x →
      (evalPt (R := DualNumber ℂ) x.left U hx f).snd =
        l (evalPt (R := TrivSqZeroExt ℂ (ℂ × ℂ)) u.left U hUu f).snd := by
    rintro l x hx rfl
    exact (congrArg TrivSqZeroExt.snd (evalPt_spMap_comp (TrivSqZeroExt.map l).toRingHom u.left U hUu hx f)).trans
      (TrivSqZeroExt.snd_map _ _)
  rw [map_add, ← h.2 U hU1 f, ← h'.2 U hU2 f, key _ _ hU h3, key _ _ hU1 h1, key _ _ hU2 h2]
  rfl

end Deriv

end GlobalTheory.PointUnif
