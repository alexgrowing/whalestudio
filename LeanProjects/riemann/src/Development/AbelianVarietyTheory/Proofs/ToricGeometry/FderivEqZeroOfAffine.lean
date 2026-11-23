import Mathlib
import ReciprocityTheory.ThetaQuasiPeriods.ThetaQuasiPeriodStatement
import ReciprocityTheory.ThetaQuasiPeriods.Transl
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real

namespace GlobalTheory

namespace AdaptedCoord

variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)

theorem ex_comp (z : Fin g → ℂ) : (u.ex z).left ≫ A.hom = 𝟙 _ := by
  simp

theorem eventually_le {U : A.left.Opens} (h : ⊤ ≤ (u.ex 0).left ⁻¹ᵁ U) :
    ∀ᶠ z in 𝓝 (0 : Fin g → ℂ), ⊤ ≤ (u.ex z).left ⁻¹ᵁ U := (u.hol U 0).1.mem_nhds h

theorem differentiableAt_val {U : A.left.Opens} (h : ⊤ ≤ (u.ex 0).left ⁻¹ᵁ U) (f : Γ(A.left, U)) :
    DifferentiableAt ℂ (fun z => valAt' (u.ex z).left U f) 0 := (u.hol U f).2.differentiableAt ((u.hol U f).1.mem_nhds h)

def dirDeriv {U : A.left.Opens} (h : ⊤ ≤ (u.ex 0).left ⁻¹ᵁ U) (w : Fin g → ℂ) : Γ(A.left, U) →+ ℂ :=
  AddMonoidHom.mk' (fun f => fderiv ℂ (fun z => valAt' (u.ex z).left U f) 0 w) fun f f' => by
    simp only [valAt'_add]
    rw [fderiv_fun_add (differentiableAt_val u h f) (differentiableAt_val u h f')]
    rfl

theorem dirDeriv_apply {U : A.left.Opens} (h : ⊤ ≤ (u.ex 0).left ⁻¹ᵁ U) (w : Fin g → ℂ) (f : Γ(A.left, U)) :
    dirDeriv u h w f = fderiv ℂ (fun z => valAt' (u.ex z).left U f) 0 w := rfl

private theorem valAt'_constFn_of_comp_eq_id {X : Scheme.{0}} (x : Sp ℂ ⟶ X) (p : X ⟶ Sp ℂ) (hp : x ≫ p = 𝟙 _)
    (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (a : ℂ) : valAt' x U (constFn p U a) = a := by
  have key : ∀ (q : Sp ℂ ⟶ Sp ℂ) (e : ⊤ ≤ q ⁻¹ᵁ ⊤), q = 𝟙 _ →
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫ q.appLE ⊤ ⊤ e ≫ (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom =
        𝟙 _ := by
    rintro q e rfl
    simp [Scheme.Hom.appLE]
    erw [CategoryTheory.Functor.map_id]
    simp
  have hcomp : (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫ p.appLE ⊤ U (show U ≤ p ⁻¹ᵁ ⊤ from fun _ _ => trivial) ≫
      x.appLE U ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom = 𝟙 _ := by
    rw [Scheme.Hom.appLE_comp_appLE_assoc]
    exact key _ _ hp
  rw [valAt', dif_pos h]
  exact congrArg (fun φ => φ.hom a) hcomp

theorem dirDeriv_constFn {U : A.left.Opens} (h : ⊤ ≤ (u.ex 0).left ⁻¹ᵁ U) (w : Fin g → ℂ) (a : ℂ) :
    dirDeriv u h w (constFn A.hom U a) = 0 := by
  rw [dirDeriv_apply]
  have hev : (fun z => valAt' (u.ex z).left U (constFn A.hom U a)) =ᶠ[𝓝 0] fun _ => a := by
    filter_upwards [eventually_le u h] with z hz
    exact valAt'_constFn_of_comp_eq_id _ _ (ex_comp u z) U hz a
  rw [hev.fderiv_eq]
  simp

theorem dirDeriv_mul {U : A.left.Opens} (h : ⊤ ≤ (u.ex 0).left ⁻¹ᵁ U) (w : Fin g → ℂ) (f f' : Γ(A.left, U)) :
    dirDeriv u h w (f * f') =
      valAt' (u.ex 0).left U f * dirDeriv u h w f' + valAt' (u.ex 0).left U f' * dirDeriv u h w f := by
  rw [dirDeriv_apply, dirDeriv_apply, dirDeriv_apply]
  have hprod : (fun z => valAt' (u.ex z).left U (f * f')) =
      fun z => valAt' (u.ex z).left U f * valAt' (u.ex z).left U f' := by
    funext z
    exact valAt'_mul _ _ _ _
  rw [hprod, fderiv_fun_mul (differentiableAt_val u h f) (differentiableAt_val u h f')]
  simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul]

private theorem preimage_whole_of_closedPoint_mem' {X : Scheme.{0}} (x : Sp ℂ ⟶ X) (W : X.Opens) :
    ⊤ ≤ x ⁻¹ᵁ W ↔ x (default : PrimeSpectrum ℂ) ∈ W := by
  constructor
  · intro h
    exact h (show (default : PrimeSpectrum ℂ) ∈ (⊤ : (Sp ℂ).Opens) from trivial)
  · intro h q _
    have hq : q = (default : PrimeSpectrum ℂ) := @Subsingleton.elim (PrimeSpectrum ℂ) _ q default
    subst hq
    exact h

theorem fderiv_eq_zero_of_affine {U : A.left.Opens} (hU : IsAffineOpen U) (h : ⊤ ≤ (u.ex 0).left ⁻¹ᵁ U)
    (w : Fin g → ℂ) (hw : dirDeriv u h w = 0) (V : A.left.Opens) (f : Γ(A.left, V))
    (hV : ⊤ ≤ (u.ex 0).left ⁻¹ᵁ V) : fderiv ℂ (fun z => valAt' (u.ex z).left V f) 0 w = 0 := by
  classical

  have hxU := (preimage_whole_of_closedPoint_mem' (u.ex 0).left U).1 h
  have hxV := (preimage_whole_of_closedPoint_mem' (u.ex 0).left V).1 hV
  obtain ⟨b, hbV, hxb⟩ := hU.exists_basicOpen_le (V := V) ⟨_, hxV⟩ hxU
  have hb0 : ⊤ ≤ (u.ex 0).left ⁻¹ᵁ A.left.basicOpen b := (preimage_whole_of_closedPoint_mem' _ _).2 hxb
  have hloc := hU.isLocalization_basicOpen b
  obtain ⟨⟨a, s⟩, hs⟩ := IsLocalization.surj (Submonoid.powers b)
    (A.left.presheaf.map (homOfLE hbV).op f)
  dsimp only at hs
  have hres : ∀ z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ A.left.basicOpen b → ∀ c : Γ(A.left, U),
      valAt' (u.ex z).left (A.left.basicOpen b)
        (algebraMap Γ(A.left, U) Γ(A.left, A.left.basicOpen b) c) = valAt' (u.ex z).left U c :=
    fun z hz c => by
      exact valAt'_res _ (A.left.basicOpen_le b) c hz

  have hev : (fun z => valAt' (u.ex z).left V f * valAt' (u.ex z).left U (s : Γ(A.left, U))) =ᶠ[𝓝 0]
      fun z => valAt' (u.ex z).left U a := by
    filter_upwards [eventually_le u hb0] with z hz
    have hf : valAt' (u.ex z).left (A.left.basicOpen b) (A.left.presheaf.map (homOfLE hbV).op f) =
        valAt' (u.ex z).left V f := by
      exact valAt'_res _ hbV f hz
    rw [← hres z hz a, ← hres z hz (s : Γ(A.left, U)), ← hs, valAt'_mul, hf]
  have hDa : fderiv ℂ (fun z => valAt' (u.ex z).left U a) 0 w = 0 := by
    rw [← dirDeriv_apply u h w a, hw, AddMonoidHom.zero_apply]
  have hDs : fderiv ℂ (fun z => valAt' (u.ex z).left U (s : Γ(A.left, U))) 0 w = 0 := by
    rw [← dirDeriv_apply u h w (s : Γ(A.left, U)), hw, AddMonoidHom.zero_apply]

  have hs0 : valAt' (u.ex 0).left U (s : Γ(A.left, U)) ≠ 0 := by
    obtain ⟨v, hv⟩ := IsLocalization.map_units Γ(A.left, A.left.basicOpen b) s
    rw [← hres 0 hb0, ← hv]
    intro h0
    have hone := valAt'_mul (u.ex 0).left (A.left.basicOpen b) (v : Γ(A.left, A.left.basicOpen b))
      (↑v⁻¹ : Γ(A.left, A.left.basicOpen b))
    have h1 : valAt' (u.ex 0).left (A.left.basicOpen b) (1 : Γ(A.left, A.left.basicOpen b)) = 1 := by
      exact valAt'_one _ hb0
    rw [Units.mul_inv, h1, h0, zero_mul] at hone
    exact one_ne_zero hone

  have hmul := fderiv_fun_mul (differentiableAt_val u hV f) (differentiableAt_val u h (s : Γ(A.left, U)))
  rw [hev.fderiv_eq] at hmul
  have key := congrArg (fun L => L w) hmul
  simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul, hDa, hDs,
    mul_zero, zero_add] at key
  exact (mul_eq_zero.1 key.symm).resolve_left hs0

theorem apply_eq_sum (S : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (v : Fin g → ℂ) (i : Fin g) :
    S v i = ∑ j, S (Pi.single j 1) i * v j := by
  have hv : v = ∑ j, v j • Pi.single j (1 : ℂ) := by
    ext k
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hv]
  simp [map_sum, Finset.sum_apply, mul_comm]

private theorem valAt'_zero_toric_geometry {X : Scheme.{0}} (x : Sp ℂ ⟶ X) (U : X.Opens) :
    valAt' x U 0 = 0 := by
  unfold valAt'
  split_ifs <;> simp [valAt]

private theorem valAt'_finset_sum' {X : Scheme.{0}} (x : Sp ℂ ⟶ X) (U : X.Opens) {J : Type} (s : Finset J)
    (F : J → Γ(X, U)) : valAt' x U (∑ j ∈ s, F j) = ∑ j ∈ s, valAt' x U (F j) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · rw [Finset.sum_empty, Finset.sum_empty, valAt'_zero_toric_geometry]
  · intro j s hj ih
    rw [Finset.sum_insert hj, Finset.sum_insert hj, valAt'_add, ih]

end AdaptedCoord

open AdaptedCoord in

theorem exists_coord_adapted : (∀ (X : Over (Sp ℂ)) (g : ℕ), SmoothOfRelativeDimension g X.hom → ∀ e : (𝟙_ (Over (Sp ℂ)) ⟶ X), ∃ (W : Set (Fin g → ℂ)) (σ : (Fin g → ℂ) → (𝟙_ (Over (Sp ℂ)) ⟶ X)) (U : X.left.Opens) (t : Fin g → Γ(X.left, U)), IsOpen W ∧ 0 ∈ W ∧ σ 0 = e ∧ IsAffineOpen U ∧ (∀ (U : (X).left.Opens) (f : Γ((X).left, U)), IsOpen {w | w ∈ W ∧ ⊤ ≤ (σ w).left ⁻¹ᵁ U} ∧ DifferentiableOn ℂ (fun w => valAt' (σ w).left U f) {w | w ∈ W ∧ ⊤ ≤ (σ w).left ⁻¹ᵁ U}) ∧ (∀ w ∈ W, ⊤ ≤ (σ w).left ⁻¹ᵁ U ∧ ∀ i, valAt' (σ w).left U (t i) = w i) ∧ IsOpen[(TopologicalSpace.generateFrom {S : Set (𝟙_ (Over (Sp ℂ)) ⟶ X) | ∃ (U : X.left.Opens) (f : Γ(X.left, U)) (O : Set ℂ), IsOpen O ∧ S = {x | ⊤ ≤ (x).left ⁻¹ᵁ U ∧ valAt' x.left U f ∈ O}})] (σ '' W) ∧ (∀ D : Γ(X.left, U) →+ ℂ, (∀ a, D (constFn X.hom U a) = 0) → (∀ f f', D (f * f') = valAt' e.left U f * D f' + valAt' e.left U f' * D f) → (∀ i, D (t i) = 0) → D = 0)) → (∀ (A : Over (Sp ℂ)) [GrpObj A] (L : LB A.left) (g : ℕ) (u : HolUnif A L g), SmoothOfRelativeDimension g A.hom → (∀ w : Fin g → ℂ, (∀ (U : A.left.Opens) (f : Γ(A.left, U)), ⊤ ≤ (u.ex 0).left ⁻¹ᵁ U → fderiv ℂ (fun z => valAt' (u.ex z).left U f) 0 w = 0) → w = 0) → ∃ (U : A.left.Opens) (t : Fin g → Γ(A.left, U)), IsAffineOpen U ∧ ⊤ ≤ (u.ex 0).left ⁻¹ᵁ U ∧ (∀ D : Γ(A.left, U) →+ ℂ, (∀ a, D (constFn A.hom U a) = 0) → (∀ f f', D (f * f') = valAt' (u.ex 0).left U f * D f' + valAt' (u.ex 0).left U f' * D f) → (∀ i, D (t i) = 0) → D = 0) ∧ HasFDerivAt (fun w i => valAt' (u.ex w).left U (t i)) (ContinuousLinearMap.id ℂ (Fin g → ℂ)) 0) := by
  intro H A _ L g u hsm hinj
  obtain ⟨W, σ, U, t, -, hW0, hσ0, hU, -, hσW, -, hD⟩ := H A g hsm (u.ex 0)
  have h : ⊤ ≤ (u.ex 0).left ⁻¹ᵁ U := hσ0 ▸ (hσW 0 hW0).1
  have hφd : DifferentiableAt ℂ (fun z i => valAt' (u.ex z).left U (t i)) 0 :=
    differentiableAt_pi.2 fun i => differentiableAt_val u h (t i)

  obtain ⟨M, hMdef⟩ : ∃ M : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ),
      ∀ v, M v = fderiv ℂ (fun z i => valAt' (u.ex z).left U (t i)) 0 v :=
    ⟨(fderiv ℂ (fun z i => valAt' (u.ex z).left U (t i)) 0 : (Fin g → ℂ) →L[ℂ] (Fin g → ℂ)),
      fun _ => rfl⟩
  have hM : ∀ v i, M v i = dirDeriv u h v (t i) := by
    intro v i
    rw [hMdef, dirDeriv_apply, (hasFDerivAt_pi'.1 hφd.hasFDerivAt i).fderiv]
    rfl

  have hMinj : Function.Injective M := by
    intro v v' hvv
    have hv0 : v - v' = 0 := by
      apply hinj
      intro V f hV
      refine fderiv_eq_zero_of_affine u hU h (v - v') ?_ V f hV
      refine hD _ (fun a => dirDeriv_constFn u h _ a) (fun f f' => dirDeriv_mul u h _ f f') fun i => ?_
      rw [← hM, map_sub, hvv, sub_self]
      rfl
    exact sub_eq_zero.1 hv0
  obtain ⟨Sinv, hSM, hSinj⟩ : ∃ S : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), (∀ v, S (M v) = v) ∧ Function.Injective S := by
    let N := LinearEquiv.ofInjectiveEndo M hMinj
    refine ⟨N.symm.toLinearMap, fun v => ?_, N.symm.injective⟩
    have hN : N v = M v := by simp [N, LinearEquiv.coe_ofInjectiveEndo]
    rw [LinearEquiv.coe_coe, ← hN, LinearEquiv.symm_apply_apply]

  obtain ⟨t', ht'⟩ : ∃ t' : Fin g → Γ(A.left, U),
      ∀ i, t' i = ∑ j, constFn A.hom U (Sinv (Pi.single j 1) i) * t j :=
    ⟨fun i => ∑ j, constFn A.hom U (Sinv (Pi.single j 1) i) * t j, fun _ => rfl⟩
  have hc0 : ∀ c : ℂ, valAt' (u.ex 0).left U (constFn A.hom U c) = c :=
    fun c => valAt'_constFn_of_comp_eq_id _ _ (ex_comp u 0) U h c
  refine ⟨U, t', hU, h, ?_, ?_⟩
  · intro D hc hl hD'
    apply hD D hc hl
    have hS : Sinv (fun j => D (t j)) = 0 := by
      funext i
      have e : D (t' i) = ∑ j, Sinv (Pi.single j 1) i * D (t j) := by
        rw [ht', map_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hl, hc, hc0, mul_zero, add_zero]
      rw [apply_eq_sum]
      simp only [Pi.zero_apply]
      rw [← e, hD' i]
    have h0 : (fun j => D (t j)) = 0 := hSinj (hS.trans (map_zero Sinv).symm)
    exact fun j => congrFun h0 j
  · have hev : (fun w i => valAt' (u.ex w).left U (t' i)) =ᶠ[𝓝 0]
        fun w => Sinv (fun i => valAt' (u.ex w).left U (t i)) := by
      filter_upwards [eventually_le u h] with z hz
      funext i
      rw [ht', valAt'_finset_sum', apply_eq_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [valAt'_mul, valAt'_constFn_of_comp_eq_id _ _ (ex_comp u z) U hz]
    have hcomp : HasFDerivAt (fun w => Sinv (fun i => valAt' (u.ex w).left U (t i)))
        ((LinearMap.toContinuousLinearMap Sinv).comp
          (fderiv ℂ (fun z i => valAt' (u.ex z).left U (t i)) 0)) 0 :=
      (LinearMap.toContinuousLinearMap Sinv).hasFDerivAt.comp 0 hφd.hasFDerivAt
    have hid : (LinearMap.toContinuousLinearMap Sinv).comp
        (fderiv ℂ (fun z i => valAt' (u.ex z).left U (t i)) 0) = ContinuousLinearMap.id ℂ (Fin g → ℂ) := by
      refine ContinuousLinearMap.ext fun v => ?_
      rw [ContinuousLinearMap.comp_apply, ← hMdef, LinearMap.coe_toContinuousLinearMap', hSM]
      rfl
    rw [hid] at hcomp
    exact hcomp.congr_of_eventuallyEq hev

end GlobalTheory
