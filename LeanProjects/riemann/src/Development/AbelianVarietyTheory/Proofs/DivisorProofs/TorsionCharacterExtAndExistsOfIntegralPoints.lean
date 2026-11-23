import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.AlWellDefSt
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsAlgHomValuationSubring
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsReducedTorsionGeometricFibre
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.UnitOfBijectiveMulNatural
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SectionEqZeroOfForallGeometricPoint
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.EqOneOfPowEqOneOfCompEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEvalEqOfMultiplicativeOnPoints

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorsionCharacterExt

open Algebra.TensorProduct in

theorem tensor_eq_zero_of_forall_pair (O F : Type) [CommRing O] [Field F] [IsAlgClosed F]
    [Algebra O F] [Module.Flat O F] (hinj : Function.Injective (algebraMap O F)) (A : Type)
    [CommRing A] [Algebra O A] [Module.Finite O A] [Module.Flat O A]
    [_root_.IsReduced (F ⊗[O] A)] (t : A ⊗[O] A)
    (ht : ∀ x y : A →ₐ[O] F, lift x y (fun _ _ => Commute.all _ _) t = 0)
    (hmul : Function.Injective (LinearMap.mul' O F)) : t = 0 := by
  refine tensor_eq_zero_of_forall_geometric_point O F hinj A A t fun x => ?_
  apply (TensorProduct.comm O F A).injective
  rw [map_zero]
  refine tensor_eq_zero_of_forall_geometric_point O F hinj A F _ fun y => ?_
  apply hmul
  rw [map_zero, ← ht x y]
  clear ht
  induction t with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul a b => simp [mul_comm]

variable {O : Type} [CommRing O]

theorem exists_pair {A : Type} [CommRing A] [Algebra O A] {T : Over (Spec (CommRingCat.of O))}
    (x y : T ⟶ specO O A) : ∃ t : T ⟶ specO O (A ⊗[O] A),
      t ≫ ptMap Algebra.TensorProduct.includeLeft = x ∧
        t ≫ ptMap Algebra.TensorProduct.includeRight = y := by
  have h1 : ((lift x y).left ≫ (pullbackSpecIso O A A).hom) ≫
      Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom) = x.left := by
    rw [Category.assoc, pullbackSpecIso_hom_fst]
    exact congrArg Over.Hom.left (lift_fst x y)
  have h2 : ((lift x y).left ≫ (pullbackSpecIso O A A).hom) ≫
      (ptMap (Algebra.TensorProduct.includeRight : A →ₐ[O] A ⊗[O] A)).left = y.left := by
    refine (Category.assoc _ _ _).trans ?_
    refine (congrArg ((lift x y).left ≫ ·) (pullbackSpecIso_hom_snd O A A)).trans ?_
    exact congrArg Over.Hom.left (lift_snd x y)
  refine ⟨Over.homMk ((lift x y).left ≫ (pullbackSpecIso O A A).hom) ?_,
    Over.OverMorphism.ext h1, Over.OverMorphism.ext h2⟩
  rw [← Over.w y, ← h2, Category.assoc _ (ptMap _).left, Over.w]

end GlobalTheory.TorsionCharacterExt

namespace GlobalTheory

open KernelNoTorsion TangentPow TorsionCharacter GmPoints in

theorem torsionCharacter_ext_and_exists_of_integral_points :
    ∀ (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ (G : Over (Spec (CommRingCat.of O))) [GrpObj G] [IsCommMonObj G], ∀ N : ℕ, 1 ≤ N → IsFinite (torsion G N).hom → Flat (torsion G N).hom → (∀ f f' : torsion G N ⟶ Gm (Spec (CommRingCat.of O)), (∀ w : specO O O ⟶ torsion G N, w ≫ f = w ≫ f') → f = f') ∧ ∀ κ : (specO O O ⟶ G) → Cˣ, (∀ x y : specO O O ⟶ G, x ^ N = 1 → y ^ N = 1 → κ (x * y) = κ x * κ y) → ∃ f : torsion G N ⟶ Gm (Spec (CommRingCat.of O)), IsCharTors G N f ∧ ∀ w : specO O O ⟶ torsion G N, algebraMap O C (unitOf (w ≫ f) : O) = (κ (w ≫ torsion.ι G N) : C) := by
  intro C _ _ _ v O _ _ hv G _ _ N hN hfin hflat
  have hinj := hv.hom_inj
  have : IsDomain O := hinj.isDomain _
  have := ValuationRing.of_integers v hv
  have := hv.isFractionRing
  have : IsIntegrallyClosed O := inferInstance
  obtain ⟨A, _, _, _, _, ⟨e⟩⟩ := exists_finite_free (torsion G N)
  have hred := isReduced_torsion_geometric_fibre O C G N (Nat.cast_ne_zero.2 (by omega)) hfin
  have h0 : IsIso (specO O C ◁ e.hom).left :=
    inferInstanceAs (IsIso ((Over.forget _).map (specO O C ◁ e.hom)))
  have h3 : IsReduced (specO O C ⊗ specO O A).left :=
    isReduced_of_isOpenImmersion (specO O C ◁ e.hom).left
  have h4 : IsReduced (Spec (CommRingCat.of (C ⊗[O] A))) :=
    @isReduced_of_isOpenImmersion _ _ (pullbackSpecIso O C A).inv _ h3
  have hA : _root_.IsReduced (C ⊗[O] A) := (affine_isReduced_iff _).mp h4

  have hint : ∀ x : A →ₐ[O] C, ∃ ψ : A →ₐ[O] O, ∀ a, algebraMap O C (ψ a) = x a := fun x => by
    have h : ∀ a, ∃ y, algebraMap O C y = x a := fun a =>
      IsIntegrallyClosed.isIntegral_iff.1 ((Algebra.IsIntegral.isIntegral (R := O) a).map x)
    choose g hg using h
    exact ⟨{ toFun := g
             map_one' := hinj (by simp [hg])
             map_mul' := fun a b => hinj (by simp [hg])
             map_zero' := hinj (by simp [hg])
             map_add' := fun a b => hinj (by simp [hg])
             commutes' := fun r => hinj (by simp [hg]) }, hg⟩
  choose σ hσ using hint
  have hσu : ∀ (x : A →ₐ[O] C) (ψ : A →ₐ[O] O), (∀ a, algebraMap O C (ψ a) = x a) → σ x = ψ :=
    fun x ψ h => AlgHom.ext fun a => hinj ((hσ x a).trans (h a).symm)
  have hsep : ∀ a b : A, (∀ x : A →ₐ[O] C, x a = x b) → a = b := fun a b h =>
    sub_eq_zero.1 (FlatPoints.eq_zero_of_forall_point O C hinj A _ fun x => by
      rw [map_sub, h, sub_self])
  refine ⟨fun f f' h => ?_, fun κ hκ => ?_⟩
  · rw [← cancel_epi e.hom]
    refine unitOf_bijective.1 (Units.ext (hsep _ _ fun x => ?_))
    rw [← hσ, ← hσ, ← unitOf_ptMap, ← unitOf_ptMap, ← Category.assoc, h, Category.assoc]
  let j : specO O A ⟶ G := e.hom ≫ torsion.ι G N
  have hj : j ^ N = 1 := by rw [← MonObj.comp_pow, torsionι_pow, comp_one]
  have hp : ∀ {T} (t : T ⟶ specO O A), (t ≫ j) ^ N = 1 := fun t => by
    rw [← MonObj.comp_pow, hj, comp_one]
  have hjm : ∀ {T} (s t : T ⟶ specO O A), s ≫ j = t ≫ j → s = t := fun s t h =>
    (cancel_mono e.hom).1 (torsion_hom_ext (by simpa [j] using h))
  have hl : ∀ {T} (s : T ⟶ G), s ^ N = 1 → ∃ t : T ⟶ specO O A, t ≫ j = s := fun s hs =>
    ⟨torsionLift s hs ≫ e.inv, by simp [j, torsionLift_ι]⟩
  let i₁ : A →ₐ[O] A ⊗[O] A := Algebra.TensorProduct.includeLeft
  let i₂ : A →ₐ[O] A ⊗[O] A := Algebra.TensorProduct.includeRight
  obtain ⟨d, hd⟩ := hl ((ptMap i₁ ≫ j) * (ptMap i₂ ≫ j)) (by rw [mul_pow, hp, hp, _root_.mul_one])
  obtain ⟨Δ, rfl⟩ := exists_ptMap d
  obtain ⟨d, hε⟩ := hl (1 : specO O O ⟶ G) (one_pow N)
  obtain ⟨ε, rfl⟩ := exists_ptMap d
  let k : (A →ₐ[O] C) → Cˣ := fun x => κ (ptMap (σ x) ≫ j)
  have hk : ∀ x y : A →ₐ[O] C, k ((Algebra.TensorProduct.lift x y
      (fun _ _ => Commute.all _ _)).comp Δ) = k x * k y := fun x y => by
    have h1 : σ ((Algebra.TensorProduct.lift x y (fun _ _ => Commute.all _ _)).comp Δ) =
        (Algebra.TensorProduct.lift (σ x) (σ y) (fun _ _ => Commute.all _ _)).comp Δ := by
      refine hσu _ _ fun a => ?_
      rw [AlgHom.comp_apply, AlgHom.comp_apply]
      generalize Δ a = t
      induction t with
      | zero => simp
      | add a b ha hb => simp only [map_add, ha, hb]
      | tmul a b => simp only [Algebra.TensorProduct.lift_tmul, map_mul, hσ]
    simp only [k]
    rw [h1, ← ptMap_comp_ptMap, Category.assoc, hd, comp_mul, ← Category.assoc _ _ j,
      ← Category.assoc _ _ j, ptMap_comp_ptMap, ptMap_comp_ptMap, Algebra.TensorProduct.lift_comp_includeLeft,
      Algebra.TensorProduct.lift_comp_includeRight']
    exact hκ _ _ (hp _) (hp _)
  have hk1 : k ((Algebra.ofId O C).comp ε) = 1 := by
    have h1 : σ ((Algebra.ofId O C).comp ε) = ε := hσu _ _ fun a => rfl
    have h2 := hκ 1 1 (one_pow N) (one_pow N)
    rw [_root_.mul_one] at h2
    simp only [k]
    rw [h1, hε]
    exact left_eq_mul.1 h2
  obtain ⟨b, hb⟩ := GlobalTheory.exists_eval_eq_of_multiplicative_on_points O C A hA Δ ε (fun x => k x)
    (fun x y => by rw [hk, Units.val_mul]) (by rw [hk1, Units.val_one])
  obtain ⟨b', hb'⟩ := GlobalTheory.exists_eval_eq_of_multiplicative_on_points O C A hA Δ ε (fun x => ((k x)⁻¹ : Cˣ))
    (fun x y => by rw [hk, mul_inv, Units.val_mul]) (by rw [hk1, inv_one, Units.val_one])
  have hbb : b * b' = 1 := hsep _ _ fun x => by
    rw [map_mul, hb, hb', map_one, Units.mul_inv]
  obtain ⟨f₀, hf₀⟩ := (unitOf_bijective (O := O) (R := A)).2 (Units.mkOfMulEqOne b b' hbb)
  have hf : (unitOf f₀ : A) = b := by rw [hf₀]; rfl
  have hΔ : Δ b = i₁ b * i₂ b := by
    have : Module.Flat O C := IsLocalization.flat C (nonZeroDivisors O)
    refine sub_eq_zero.1 (TorsionCharacterExt.tensor_eq_zero_of_forall_pair O C hinj A _
      (fun x y => ?_) ?_)
    · have h := hb ((Algebra.TensorProduct.lift x y (fun _ _ => Commute.all _ _)).comp Δ)
      rw [hk, AlgHom.comp_apply, Units.val_mul, ← hb, ← hb] at h
      rw [map_sub, h]
      simp [i₁, i₂]
    · exact (IsLocalization.bijective_linearMap_mul' (nonZeroDivisors O) C).1
  have hmul : ptMap Δ ≫ f₀ = (ptMap i₁ ≫ f₀) * (ptMap i₂ ≫ f₀) := by
    refine unitOf_bijective.1 (Units.ext ?_)
    rw [unitOf_mul, Units.val_mul, unitOf_ptMap, unitOf_ptMap, unitOf_ptMap, hf, hΔ]
  refine ⟨e.inv ≫ f₀, fun T x y z h => ?_, fun w => ?_⟩
  · obtain ⟨t, ht₁, ht₂⟩ := TorsionCharacterExt.exists_pair (x ≫ e.inv) (y ≫ e.inv)
    have hz : z ≫ e.inv = t ≫ ptMap Δ := hjm _ _ (by
      rw [Category.assoc t, hd, comp_mul, ← Category.assoc t, ← Category.assoc t, ht₁, ht₂]
      simpa [j] using h)
    rw [← Category.assoc, hz, Category.assoc, hmul, comp_mul, ← Category.assoc t,
      ← Category.assoc t, ht₁, ht₂, Category.assoc, Category.assoc]
  · obtain ⟨ψ, hψ⟩ := exists_ptMap (w ≫ e.inv)
    have h1 : σ ((Algebra.ofId O C).comp ψ) = ψ := hσu _ _ fun a => rfl
    have h2 := hb ((Algebra.ofId O C).comp ψ)
    simp only [k] at h2
    rw [h1, ← hψ] at h2
    rw [← Category.assoc, hψ, unitOf_ptMap, hf]
    simpa [j] using h2

end GlobalTheory
