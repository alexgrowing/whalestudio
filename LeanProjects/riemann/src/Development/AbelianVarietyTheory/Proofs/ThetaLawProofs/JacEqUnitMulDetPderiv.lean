import Mathlib
import Development.AbelianVarietyTheory.Definitions.KeyFormula.IsSquareDeterminantComparison
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.IsPluriharmonicSiegel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.MapsAtLeA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OneEqSpTranslZero
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.IsLieBasisIffIsUnitDet
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.MemNonzeroLocusVia
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosure

noncomputable section

namespace GlobalTheory.JacSer

section Algebra

open IsLocalRing MvPowerSeries GlobalTheory.SqZero

variable {O : Type} [CommRing O] [IsLocalRing O]

theorem isLocalRing_trivSqZeroExt (M : Type) [AddCommGroup M] [Module O M] [Module Oᵐᵒᵖ M] [IsCentralScalar O M] :
    IsLocalRing (TrivSqZeroExt O M) :=
  IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => by
    simp only [TrivSqZeroExt.isUnit_iff_isUnit_fst, TrivSqZeroExt.fst_sub, TrivSqZeroExt.fst_one]
    exact isUnit_or_isUnit_one_sub_self _

omit [IsLocalRing O] in

def dirPt {n : ℕ} (e : MvPowerSeries (Fin n) O →ₐ[O] O) (c : Fin n → O) :
    MvPowerSeries (Fin n) O →ₐ[O] DualNumber O :=
  addDer ((inlS O O).comp e) (TrivSqZeroExt.inrHom O O ∘ₗ
      ∑ j, c j • (e.toLinearMap ∘ₗ (pderiv O j : Derivation O _ _).toLinearMap))
    (fun a b => by
      ext
      · simp [TrivSqZeroExt.fst_sum]
      · simp [TrivSqZeroExt.snd_sum, Finset.mul_sum, ← Finset.sum_add_distrib, mul_add, mul_left_comm]
        exact Finset.sum_congr rfl fun _ _ => by ring)
    (fun _ _ => TrivSqZeroExt.inr_mul_inr _ _ _)

omit [IsLocalRing O] in
theorem dirPt_fst {n : ℕ} (e : MvPowerSeries (Fin n) O →ₐ[O] O) (c : Fin n → O) (a : MvPowerSeries (Fin n) O) :
    (dirPt e c a).fst = e a := add_zero (e a)

omit [IsLocalRing O] in
theorem dirPt_snd {n : ℕ} (e : MvPowerSeries (Fin n) O →ₐ[O] O) (c : Fin n → O) (a : MvPowerSeries (Fin n) O) :
    (dirPt e c a).snd = ∑ j, c j * e (pderiv O j a) :=
  (zero_add _).trans ((TrivSqZeroExt.snd_inr _ _).trans (by simp))

omit [IsLocalRing O] in
theorem dirPt_snd_X {n : ℕ} (e : MvPowerSeries (Fin n) O →ₐ[O] O) (c : Fin n → O) (i : Fin n) :
    (dirPt e c (X i)).snd = c i := by
  simp [dirPt_snd, pderiv_X, Pi.single_apply, apply_ite e]

variable [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O]

theorem snd_eq_sum {n : ℕ} (e : MvPowerSeries (Fin n) O →ₐ[O] O) (he : ∀ i, e (X i) ∈ maximalIdeal O)
    (ψ : MvPowerSeries (Fin n) O →ₐ[O] DualNumber O) (hψ : ∀ a, (ψ a).fst = e a) (a : MvPowerSeries (Fin n) O) :
    (ψ a).snd = ∑ j, (ψ (X j)).snd * e (pderiv O j a) := by
  have := isLocalRing_trivSqZeroExt (O := O) O
  have : Module.Finite O (DualNumber O) := inferInstanceAs (Module.Finite O (O × O))
  have := GlobalTheory.FormalIsogeny.isAdicComplete_maximalIdeal_of_finite O (DualNumber O)
  have h : ψ = dirPt e fun j => (ψ (X j)).snd :=
    mvPowerSeries_algHom_ext_of_isHausdorff (maximalIdeal (DualNumber O))
      (fun i h => he i (hψ _ ▸ TrivSqZeroExt.isUnit_iff_isUnit_fst.1 h))
      (fun i => TrivSqZeroExt.ext (by rw [hψ, dirPt_fst]) (by rw [dirPt_snd_X]))
  exact (congrArg (fun q => (q a).snd) h).trans (dirPt_snd _ _ _)

omit [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] in
theorem isLocalHom_of_X_mem {n : ℕ} (e : MvPowerSeries (Fin n) O →ₐ[O] O) (he : ∀ i, e (X i) ∈ maximalIdeal O) :
    IsLocalHom e.toRingHom := by
  refine ((IsLocalRing.local_hom_TFAE _).out 0 3).2 fun g hg => ?_
  have h1 := algHom_sub_constantCoeff_mem e he g
  have h2 := (FormalIsogeny.mem_maximalIdeal_iff_constantCoeff (g := g)).1 hg
  simpa using add_mem h1 h2

end Algebra

section Group

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap spMap_left spMap_comp spMap_id comp_one' IsTan fstD isTan_iff)
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp epsR IsTangent IsLieComb IsLieBasis)
open TrivSqZeroExt (inl inr)
open GlobalTheory.SqZero GlobalTheory.LieComb IsLocalRing MvPowerSeries

attribute [local instance] Over.cartesianMonoidalCategory

variable {O : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O]
  {G : Over (Spec (CommRingCat.of O))} [GrpObj G] [IsCommMonObj G] {n : ℕ} {v : Fin n → (epsR O ⟶ G)}

theorem exists_matrix (hv : IsLieBasis v) (j : sp (R₀ := O) (MvPowerSeries (Fin n) O) ⟶ G)
    (inj : ∀ {T : Type} [CommRing T] [Algebra O T] (φ ψ : MvPowerSeries (Fin n) O →ₐ[O] T),
      spMap φ ≫ j = spMap ψ ≫ j → ∀ i, φ (X i) = ψ (X i))
    (z : 𝟙_ _ ⟶ G) (u : MvPowerSeries (Fin n) O →ₐ[O] O) (hu0 : ∀ i, u (X i) ∈ maximalIdeal O)
    (hu : spMap u ≫ j = toUnit _ ≫ z)
    (χ : MvPowerSeries (Fin n) O →ₐ[O] TrivSqZeroExt O (Fin n → O))
    (hχ : spMap χ ≫ j = (toUnit _ ≫ z) * lieExp v (fun i => inr (Pi.single i 1))
      (fun _ => TrivSqZeroExt.inr_mul_inr _ _ _)) :
    ∃ C : Matrix (Fin n) (Fin n) O, IsUnit C.det ∧
      ∀ k, ∃ φ : MvPowerSeries (Fin n) O →ₐ[O] DualNumber O, spMap φ ≫ j = (toUnit _ ≫ z) * v k ∧
        ∀ a, (φ a).snd = ∑ i, u (pderiv O i a) * C i k := by
  have hz : ∀ {T T' : Type} [CommRing T] [Algebra O T] [CommRing T'] [Algebra O T'] (φ : T →ₐ[O] T'),
      spMap φ ≫ toUnit _ ≫ z = toUnit _ ≫ z := fun φ => by
    rw [← Category.assoc, comp_toUnit]
  have hfst : ∀ a, (χ a).fst = u a := by
    refine fun a => (AlgHom.congr_fun (mvPowerSeries_algHom_ext_of_isHausdorff (maximalIdeal O) hu0
      (inj u ((TrivSqZeroExt.fstHom O O _).comp χ) ?_)) a).symm
    rw [← spMap_comp, Category.assoc, hχ, MonObj.comp_mul, hz, comp_lieExp,
      lieExp_eq_one hv.1 _ (fun i => by rfl), mul_one, hu]
  let φ : (Fin n → O) → (MvPowerSeries (Fin n) O →ₐ[O] DualNumber O) := fun c =>
    (vecTo (inlS O O) (fun i => inr (c i)) (fun _ _ => TrivSqZeroExt.inr_mul_inr _ _ _)).comp χ
  have hφ : ∀ c, spMap (φ c) ≫ j = (toUnit _ ≫ z) * tanExp v c := fun c => by
    rw [← spMap_comp, Category.assoc, hχ, MonObj.comp_mul, hz, comp_lieExp]
    exact congrArg _ (lieExp_congr _ (fun i => vecTo_single _ _ _ i) _ _)
  have hφ1 : ∀ c a, (φ c a).fst = u a := fun c a => by
    simp [φ, vecTo_apply, TrivSqZeroExt.fst_sum, hfst]
  have hφ2 : ∀ c a, (φ c a).snd = ∑ k, (χ a).snd k * c k := fun c a => by
    simp [φ, vecTo_apply, TrivSqZeroExt.snd_sum, mul_comm]
  obtain ⟨-, hsurj⟩ := isLieBasisOver_self hv
  have hM : ∀ l : Fin n, ∃ c : Fin n → O, ∀ i, ∑ k, (χ (X i)).snd k * c k = (Pi.single l 1 : Fin n → O) i := by
    intro l
    have h1 : (fstS O O).comp (dirPt u (Pi.single l 1)) = u := AlgHom.ext fun a => dirPt_fst _ _ a
    obtain ⟨c, hc⟩ := hsurj ((toUnit _ ≫ z)⁻¹ * (spMap (dirPt u (Pi.single l 1)) ≫ j)) (by
      rw [IsTanOver, MonObj.comp_mul, GrpObj.comp_inv, hz, ← Category.assoc, spMap_comp, h1, hu,
        inv_mul_cancel])
    have h2 := inj (dirPt u (Pi.single l 1)) (φ c) (by rw [hφ, ← hc, mul_inv_cancel_left])
    exact ⟨c, fun i => by rw [← hφ2, ← h2, dirPt_snd_X]⟩
  choose M hM using hM
  refine ⟨Matrix.of fun i k => (χ (X i)).snd k, ?_, fun k => ⟨φ (Pi.single k 1), ?_, fun a => ?_⟩⟩
  · refine Matrix.isUnit_det_of_right_inverse (B := Matrix.of fun k l => M l k) (Matrix.ext fun i l => ?_)
    rw [Matrix.mul_apply, Matrix.one_apply]
    exact (hM l i).trans (Pi.single_apply _ _ _)
  · rw [hφ, tanExp_single hv.1]
  · rw [snd_eq_sum u hu0 _ (hφ1 _)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hφ2, mul_comm]
    simp [Pi.single_apply]

end Group

end GlobalTheory.JacSer

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa

theorem GlobalTheory.KeyKa.jac_eq_unit_mul_det_pderiv : ∀ (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (x : KeyIn O) (θ : Sp (MvPowerSeries (Fin x.P.g) O) ⟶ x.P.A.left) (z : Pt x) (e : (MvPowerSeries (Fin x.P.g) O) →ₐ[O] O), θ ≫ x.P.A.hom = spMap (algebraMap O (MvPowerSeries (Fin x.P.g) O)) → (∃ (V : x.P.A.left.Opens) (t : Fin x.P.g → Γ(x.P.A.left, V)), ⊤ ≤ θ ⁻¹ᵁ V ∧ ∀ i, valT (T := (MvPowerSeries (Fin x.P.g) O)) θ V (t i) = MvPowerSeries.X i) → (∀ (T : Type) [CommRing T] [IsLocalRing T] [Algebra O T] [IsAdicComplete (IsLocalRing.maximalIdeal T) T] (w : Sp T ⟶ x.P.A.left), w ≫ x.P.A.hom = spMap (algebraMap O T) → w (IsLocalRing.closedPoint T) = θ (IsLocalRing.closedPoint (MvPowerSeries (Fin x.P.g) O)) → ∃ e : (MvPowerSeries (Fin x.P.g) O) →ₐ[O] T, (∀ i, e (MvPowerSeries.X i) ∈ IsLocalRing.maximalIdeal T) ∧ spMap e.toRingHom ≫ θ = w) → (∀ i, e (MvPowerSeries.X i) ∈ IsLocalRing.maximalIdeal O) → spMap e.toRingHom ≫ θ = z.left → ∃ u : Oˣ, ∀ (n : ℕ) (s : Fin x.P.g → RR x n) (c : x.P.L.ι), ⊤ ≤ z.left ⁻¹ᵁ x.P.L.U c → jac x s z c = u * e (Matrix.of fun i j => MvPowerSeries.pderiv O j (valT (T := (MvPowerSeries (Fin x.P.g) O)) θ (x.P.L.U c) ((s i).f c))).det := by
  intro O _ _ _ _ x θ z e hθ ⟨V, t, hV, ht⟩ hlift he hz
  let j : Chart.sp (R₀ := O) (MvPowerSeries (Fin x.P.g) O) ⟶ x.P.A := Over.homMk θ hθ
  have hloc := GlobalTheory.JacSer.isLocalHom_of_X_mem e he
  have hcl : z.left (IsLocalRing.closedPoint O) = θ (IsLocalRing.closedPoint (MvPowerSeries (Fin x.P.g) O)) := by
    rw [← hz, ← IsLocalRing.comap_closedPoint e.toRingHom]
    rfl
  have hu : Chart.spMap e ≫ j = toUnit _ ≫ z := by
    apply Over.OverMorphism.ext
    have e1 : (toUnit (Chart.sp (R₀ := O) O)).left = 𝟙 (Sp O) := by
      rw [Over.toUnit_left]
      exact Spec.map_id _
    rw [Over.comp_left, Over.comp_left, e1]
    exact hz.trans (Category.id_comp _).symm
  have := GlobalTheory.JacSer.isLocalRing_trivSqZeroExt (O := O) (Fin x.P.g → O)
  have : Module.Finite O (TrivSqZeroExt O (Fin x.P.g → O)) :=
    inferInstanceAs (Module.Finite O (O × (Fin x.P.g → O)))
  have := GlobalTheory.FormalIsogeny.isAdicComplete_maximalIdeal_of_finite O (TrivSqZeroExt O (Fin x.P.g → O))
  let w : Chart.sp (R₀ := O) (TrivSqZeroExt O (Fin x.P.g → O)) ⟶ x.P.A :=
    (toUnit _ ≫ z) * GlobalTheory.SqZero.lieExp x.v (fun i => TrivSqZeroExt.inr (Pi.single i 1))
      (fun _ => TrivSqZeroExt.inr_mul_inr _ _ _)
  obtain ⟨χ, -, hχ⟩ := hlift (TrivSqZeroExt O (Fin x.P.g → O)) w.left (Over.w w) (by
    have h1 : IsLocalHom (TrivSqZeroExt.fstHom O O (Fin x.P.g → O)).toRingHom :=
      ⟨fun a ha => TrivSqZeroExt.isUnit_iff_isUnit_fst.2 ha⟩
    have h2 : Chart.spMap (TrivSqZeroExt.fstHom O O (Fin x.P.g → O)) ≫ w = Chart.spMap e ≫ j := by
      rw [hu, MonObj.comp_mul, GlobalTheory.SqZero.comp_lieExp, GlobalTheory.SqZero.lieExp_eq_one x.basis.1 _ (fun i => by rfl),
        _root_.mul_one, ← Category.assoc, comp_toUnit]
    have h3 := congrArg (fun q => q.left (IsLocalRing.closedPoint O)) h2
    rw [← IsLocalRing.comap_closedPoint (TrivSqZeroExt.fstHom O O (Fin x.P.g → O)).toRingHom,
      ← IsLocalRing.comap_closedPoint e.toRingHom]
    exact h3)
  obtain ⟨C, hC, hφ⟩ := GlobalTheory.JacSer.exists_matrix x.basis j (fun φ ψ h i => by
    have h1 : spMap φ.toRingHom ≫ θ = spMap ψ.toRingHom ≫ θ := congrArg (·.left) h
    have h2 := EtBaseChange.valT_spMap φ.toRingHom θ hV (t i)
    rw [h1, EtBaseChange.valT_spMap ψ.toRingHom θ hV, ht] at h2
    exact h2.symm) z e he hu χ (Over.OverMorphism.ext hχ)
  refine ⟨hC.unit, fun n s c hc => ?_⟩
  have hθc : ⊤ ≤ θ ⁻¹ᵁ x.P.L.U c := fun p _ =>
    ((IsLocalRing.specializes_closedPoint p).map θ.continuous).mem_open (x.P.L.U c).isOpen
      (hcl ▸ hc (x := IsLocalRing.closedPoint O) trivial)
  rw [IsUnit.unit_spec, _root_.mul_comm, AlgHom.map_det, ← Matrix.det_mul]
  refine congrArg Matrix.det (Matrix.ext fun i k => ?_)
  obtain ⟨φ, h1, h2⟩ := hφ k
  rw [Matrix.mul_apply, Matrix.of_apply]
  refine Eq.trans (congrArg TrivSqZeroExt.snd ?_) (h2 _)
  exact (congrArg (fun q : epsR O ⟶ x.P.A => valT (T := DualNumber O) q.left (x.P.L.U c) ((s i).f c)) h1.symm).trans
    (EtBaseChange.valT_spMap φ.toRingHom θ hθc _)

end
