import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.FlagBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.EigLatBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.InversionStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Signature
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TangentBijectionOfValues
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIsLieBasisBaseChange
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.HolDifferentiableAt

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Filter Topology GlobalTheory.TangentOrigin

namespace GlobalTheory.HolLieFrame

theorem differentiableAt_of_forms {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {g : ℕ} (W : V → Fin g → ℂ)
    (b₀ : V) (H : ∀ w : Fin g → ℂ, (∀ L : V → ((Fin g → ℂ) →L[ℂ] ℂ), DifferentiableAt ℂ L b₀ →
      DifferentiableAt ℂ (fun b => L b (W b)) b₀ → L b₀ w = 0) → w = 0) : DifferentiableAt ℂ W b₀ := by
  let M : Submodule ℂ (Module.Dual ℂ (Fin g → ℂ)) :=
    { carrier := {l | ∃ L : V → ((Fin g → ℂ) →L[ℂ] ℂ), DifferentiableAt ℂ L b₀ ∧
        DifferentiableAt ℂ (fun b => L b (W b)) b₀ ∧ ∀ w, L b₀ w = l w}
      add_mem' := by
        rintro l l' ⟨L, h1, h2, h3⟩ ⟨L', h1', h2', h3'⟩
        exact ⟨fun b => L b + L' b, h1.add h1', h2.add h2', fun w => by simp [h3, h3']⟩
      zero_mem' := ⟨fun _ => 0, differentiableAt_const _, by simp, by simp⟩
      smul_mem' := by
        rintro c l ⟨L, h1, h2, h3⟩
        exact ⟨fun b => c • L b, h1.const_smul c, h2.const_smul c, fun w => by simp [h3]⟩ }
  have hM : M = ⊤ := by
    have h0 : M.dualCoannihilator = ⊥ := by
      refine eq_bot_iff.2 fun w hw => H w fun L h1 h2 => ?_
      exact (Submodule.mem_dualCoannihilator w).1 hw (L b₀).toLinearMap ⟨L, h1, h2, fun _ => rfl⟩
    rw [← Subspace.dualCoannihilator_dualAnnihilator_eq (W := M), h0, Submodule.dualAnnihilator_bot]
  have hj : ∀ j : Fin g, LinearMap.proj j ∈ M := fun j => hM ▸ Submodule.mem_top
  choose L h1 h2 h3 using hj
  let J : V → ((Fin g → ℂ) →L[ℂ] (Fin g → ℂ)) := fun b => ContinuousLinearMap.pi fun j => L j b
  have hJ : DifferentiableAt ℂ J b₀ :=
    (ContinuousLinearMap.piEquivL ℂ (Fin g → ℂ) (fun _ : Fin g => ℂ)).differentiableAt.comp b₀
      (differentiableAt_pi.2 h1)
  have hJ0 : IsUnit (J b₀) := by
    have : J b₀ = 1 := by
      ext1 w
      funext j
      exact h3 j w
    rw [this]; exact isUnit_one
  have hW : DifferentiableAt ℂ (fun b => J b (W b)) b₀ := differentiableAt_pi.2 h2
  refine ((hJ.inverse hJ0).clm_apply hW).congr_of_eventuallyEq ?_
  filter_upwards [hJ.continuousAt.eventually (Units.isOpen.mem_nhds hJ0)] with b hb
  have := congrArg (fun T : (Fin g → ℂ) →L[ℂ] (Fin g → ℂ) => T (W b)) (Ring.inverse_mul_cancel _ hb)
  exact this.symm

theorem evalPt_appLE {A : Type} [CommRing A] {X Y : Scheme.{0}} (v : Sp A ⟶ X) (φ : X ⟶ Y) (U : Y.Opens)
    (V : X.Opens) (e : V ≤ φ ⁻¹ᵁ U) (f : Γ(Y, U)) (hV : ⊤ ≤ v ⁻¹ᵁ V) (hU : ⊤ ≤ (v ≫ φ) ⁻¹ᵁ U) :
    evalPt v V hV ((φ.appLE U V e).hom f) = evalPt (v ≫ φ) U hU f := by
  simp only [evalPt, CommRingCat.hom_comp, RingHom.comp_apply]
  rw [← CommRingCat.comp_apply (φ.appLE U V e), Scheme.Hom.appLE_comp_appLE]

theorem exists_fraction {A : Type} [CommRing A] {X : Scheme.{0}} (ψ : Sp A ⟶ X) (U : X.Opens) (f : Γ(X, U))
    (t₀ : A →+* ℂ) (h₀ : ⊤ ≤ (spMap t₀ ≫ ψ) ⁻¹ᵁ U) :
    ∃ r a : A, t₀ r ≠ 0 ∧ ∀ (C : Type) [CommRing C] (t : A →+* C), IsUnit (t r) →
      ∃ h : ⊤ ≤ (spMap t ≫ ψ) ⁻¹ᵁ U, evalPt (spMap t ≫ ψ) U h f * t r = t a := by
  have hY := isAffineOpen_top (Sp A)
  obtain ⟨s, hsU, hs⟩ := hY.exists_basicOpen_le (V := ψ ⁻¹ᵁ U)
    ⟨_, (top_le_preimage_iff_mem _ _).1 ((top_le_preimage_comp _ ψ U).1 h₀)⟩ trivial
  have hloc := hY.isLocalization_basicOpen s
  obtain ⟨⟨a, _, n, rfl⟩, ha⟩ := IsLocalization.surj (Submonoid.powers s) ((ψ.appLE U _ hsU).hom f)
  have ha' : (ψ.appLE U _ hsU).hom f * resG _ ((Sp A).basicOpen_le s) (s ^ n) =
    resG _ ((Sp A).basicOpen_le s) a := ha
  obtain ⟨s, rfl⟩ := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of A)).inv).2 s
  obtain ⟨a, rfl⟩ := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of A)).inv).2 a
  have hs₀ : t₀ s ≠ 0 := by
    have := (top_le_preimage_basicOpen_iff _ _ _).1 ((top_le_preimage_iff_mem (spMap t₀) _).2 hs)
    rwa [valAt'_eq_evalPt _ _ le_rfl, evalPt_spMap] at this
  refine ⟨s ^ (n + 1), a * s, by rw [map_pow]; exact pow_ne_zero _ hs₀, fun C _ t ht => ?_⟩
  have hu : IsUnit (t s) := by
    rw [map_pow] at ht
    exact (isUnit_pow_iff n.succ_ne_zero).1 ht
  have hD : ⊤ ≤ spMap t ⁻¹ᵁ (Sp A).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of A)).inv s) := by
    rw [← evalPt_spMap t s] at hu
    have hu' := hu.map (Scheme.ΓSpecIso (CommRingCat.of C)).inv.hom
    simp only [evalPt, CommRingCat.hom_comp, RingHom.comp_apply, Iso.hom_inv_id_apply] at hu'
    have := Scheme.basicOpen_appLE (spMap t) ⊤ ⊤ le_rfl ((Scheme.ΓSpecIso (CommRingCat.of A)).inv s)
    rw [(Sp C).basicOpen_of_isUnit hu', top_inf_eq] at this
    exact this.le
  have h : ⊤ ≤ (spMap t ≫ ψ) ⁻¹ᵁ U := fun p hp => hsU (hD hp)
  refine ⟨h, ?_⟩
  have := congrArg (evalPt (spMap t) _ hD) ha'
  rw [map_mul, evalPt_appLE _ _ _ _ _ _ _ h, evalPt_res _ _ le_rfl, evalPt_res _ _ le_rfl, map_pow, evalPt_spMap,
    evalPt_spMap] at this
  rw [map_pow, pow_succ, ← _root_.mul_assoc, this, map_mul]

theorem exists_hol_snd {V R : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [CommRing R] {X : Scheme.{0}}
    (ψ : Sp (DualNumber R) ⟶ X) (ev : V → (R →+* ℂ)) (b₀ : V) (hev : ∀ c, DifferentiableAt ℂ (fun b => ev b c) b₀)
    (U : X.Opens) (f : Γ(X, U)) (h₀ : ⊤ ≤ (spMap (Chart.dualMapR (ev b₀)) ≫ ψ) ⁻¹ᵁ U) :
    ∃ F : V → ℂ, DifferentiableAt ℂ F b₀ ∧ ∀ᶠ b in 𝓝 b₀,
      ∃ h : ⊤ ≤ (spMap (Chart.dualMapR (ev b)) ≫ ψ) ⁻¹ᵁ U, (evalPt _ U h f).snd = F b := by
  have h₁ : ⊤ ≤ (spMap (fstC.comp (Chart.dualMapR (ev b₀))) ≫ ψ) ⁻¹ᵁ U := by
    have := (top_le_preimage_iff _ U).1 h₀
    rwa [← Category.assoc, ← Spec.map_comp] at this
  obtain ⟨r, a, hr, H⟩ := exists_fraction ψ U f _ h₁
  have hf : ∀ b (x : DualNumber R), (Chart.dualMapR (ev b) x).fst = ev b x.fst := fun b x => by simp [Chart.dualMapR]
  have hs : ∀ b (x : DualNumber R), (Chart.dualMapR (ev b) x).snd = ev b x.snd := fun b x => by simp [Chart.dualMapR]
  have hr' : ev b₀ r.fst ≠ 0 := (hf b₀ r) ▸ hr
  refine ⟨fun b => (ev b a.snd - ev b a.fst * (ev b r.fst)⁻¹ * ev b r.snd) * (ev b r.fst)⁻¹,
    ((hev a.snd).sub (((hev a.fst).mul ((hev r.fst).inv hr')).mul (hev r.snd))).mul ((hev r.fst).inv hr'), ?_⟩
  filter_upwards [(hev r.fst).continuousAt.eventually_ne hr'] with b hb
  obtain ⟨h, e⟩ := H _ (Chart.dualMapR (ev b)) (TrivSqZeroExt.isUnit_iff_isUnit_fst.2 (by rw [hf]; exact hb.isUnit))
  refine ⟨h, ?_⟩
  have e1 := congrArg TrivSqZeroExt.fst e
  have e2 := congrArg TrivSqZeroExt.snd e
  rw [TrivSqZeroExt.fst_mul, hf, hf] at e1
  rw [DualNumber.snd_mul, hf, hs, hs] at e2
  rw [← e1, ← e2]
  field_simp
  ring

theorem differentiableAt_ev {V R : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [CommRing R] {X : Scheme.{0}}
    {B : Set V} {y : V → (Sp ℂ ⟶ X)} (hy : IsHolTo B y) (j : Sp R ⟶ X) [IsOpenImmersion j] (ev : V → (R →+* ℂ))
    (h : ∀ b ∈ B, y b = spMap (ev b) ≫ j) {b₀ : V} (hb : b₀ ∈ B) (c : R) :
    DifferentiableAt ℂ (fun b => ev b c) b₀ := by
  have hle : ⊤ ≤ j ⁻¹ᵁ (j ''ᵁ ⊤) := (j.preimage_image_eq ⊤).ge
  have h₀ : ⊤ ≤ y b₀ ⁻¹ᵁ (j ''ᵁ ⊤) := by
    rw [h b₀ hb]
    exact fun p _ => hle (Set.mem_univ _)
  refine (LocalLift.hol_differentiableAt hy hb h₀
    ((j.appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of R)).inv c))).congr_of_eventuallyEq ?_
  filter_upwards [LocalLift.hol_eventually_mem hy hb h₀] with b hb'
  rw [h b hb'.1, ← valAt'_appLE _ j _ ⊤ hle _ le_rfl, valAt'_eq_evalPt _ _ le_rfl, ← evalPt_spMap (ev b) c,
    ← CommRingCat.comp_apply (j.appIso ⊤).inv, Scheme.Hom.appIso_inv_appLE]
  simp

theorem differentiableAt_fderiv {m g : ℕ} {X : Scheme.{0}} {B : Set (Fin m → ℂ)}
    {e : (Fin m → ℂ) → (Fin g → ℂ) → (Sp ℂ ⟶ X)}
    (he : IsHolTo (B ×ˢ Set.univ) (fun bz : (Fin m → ℂ) × (Fin g → ℂ) => e bz.1 bz.2)) {b₀ : Fin m → ℂ} (hb : b₀ ∈ B)
    (U : X.Opens) (f : Γ(X, U)) (h₀ : ⊤ ≤ e b₀ 0 ⁻¹ᵁ U) :
    DifferentiableAt ℂ (fun b => fderiv ℂ (fun z => valAt' (e b z) U f) 0) b₀ := by
  have h1 := SCV.analyticOnNhd_of_differentiableOn (he U f).1 (he U f).2 (b₀, 0) ⟨⟨hb, trivial⟩, h₀⟩
  have h2 := ContDiffAt.fderiv (𝕜 := ℂ) (f := fun b z => valAt' (e b z) U f) (g := fun _ => 0) (x₀ := b₀) (m := 1)
    (n := 2) h1.contDiffAt contDiffAt_const le_rfl
  exact h2.differentiableAt one_ne_zero

section Fibre

open GlobalTheory.GrpTangent

variable {G : Over (Sp ℂ)} [GrpObj G] {X : Scheme.{0}} {ψ : G.left ⟶ X} {g : ℕ} {e : (Fin g → ℂ) → (Sp ℂ ⟶ X)}

theorem isTangent_mul {v w : epsR ℂ ⟶ G} (hv : IsTangent v) (hw : IsTangent w) : IsTangent (v * w) := by
  rw [isTangent_iff] at hv hw ⊢
  rw [comp_mul, hv, hw, _root_.mul_one]

theorem isTangent_one : IsTangent (1 : epsR ℂ ⟶ G) := by
  rw [isTangent_iff, comp_one]

theorem evalPt_congr {A : Type} [CommRing A] {x y : Sp A ⟶ X} (h : x = y) (U : X.Opens) (hx : ⊤ ≤ x ⁻¹ᵁ U)
    (hy : ⊤ ≤ y ⁻¹ᵁ U) : evalPt x U hx = evalPt y U hy := by
  subst h; rfl

theorem tangent_base {v : epsR ℂ ⟶ G} (hv : IsTangent v) : spMap fstC ≫ v.left ≫ ψ = η[G].left ≫ ψ := by
  rw [← Category.assoc]
  exact congrArg (· ≫ ψ) hv

theorem tangent_le {v w : epsR ℂ ⟶ G} (hv : IsTangent v) (hw : IsTangent w) {U : X.Opens}
    (h : ⊤ ≤ (v.left ≫ ψ) ⁻¹ᵁ U) : ⊤ ≤ (w.left ≫ ψ) ⁻¹ᵁ U := by
  refine (top_le_preimage_iff _ U).2 ?_
  rw [tangent_base hw, ← tangent_base hv]
  exact (top_le_preimage_iff _ U).1 h

theorem snd_evalPt_mul {v w : epsR ℂ ⟶ G} (hv : IsTangent v) (hw : IsTangent w) (U : X.Opens) (f : Γ(X, U))
    (h : ⊤ ≤ ((v * w).left ≫ ψ) ⁻¹ᵁ U) (h₁ : ⊤ ≤ (v.left ≫ ψ) ⁻¹ᵁ U) (h₂ : ⊤ ≤ (w.left ≫ ψ) ⁻¹ᵁ U) :
    (evalPt (R := DualNumber ℂ) ((v * w).left ≫ ψ) U h f).snd =
      (evalPt (R := DualNumber ℂ) (v.left ≫ ψ) U h₁ f).snd + (evalPt (R := DualNumber ℂ) (w.left ≫ ψ) U h₂ f).snd := by
  let i₁ := LinearMap.inl ℂ ℂ ℂ
  let i₂ := LinearMap.inr ℂ ℂ ℂ
  let p := (sqZeroMap i₁ ≫ v) * (sqZeroMap i₂ ≫ w)
  have hp : ∀ l : ℂ × ℂ →ₗ[ℂ] ℂ, sqZeroMap l ≫ p = (epsScale (l (1, 0)) ≫ v) * (epsScale (l (0, 1)) ≫ w) := by
    intro l
    simp only [p, comp_mul, ← Category.assoc, sqZeroMap_comp_eq]
    rfl
  have e₁ : sqZeroMap (LinearMap.fst ℂ ℂ ℂ) ≫ p = v := by
    rw [hp]; simp [epsScale_one, epsScale_zero_comp hw]
  have e₂ : sqZeroMap (LinearMap.snd ℂ ℂ ℂ) ≫ p = w := by
    rw [hp]; simp [epsScale_one, epsScale_zero_comp hv]
  have e₃ : sqZeroMap (LinearMap.fst ℂ ℂ ℂ + LinearMap.snd ℂ ℂ ℂ) ≫ p = v * w := by
    rw [hp]; simp [epsScale_one]
  have hs : Function.Surjective (spMap (TrivSqZeroExt.map (LinearMap.fst ℂ ℂ ℂ)).toRingHom) := by
    refine (PrimeSpectrum.isHomeomorph_comap (TrivSqZeroExt.map (LinearMap.fst ℂ ℂ ℂ)).toRingHom
        (fun x => ⟨1, one_pos, TrivSqZeroExt.map i₁ x, by ext <;> simp [i₁]⟩) fun d hd => ?_).surjective
    have h : d.fst = 0 := by simpa using congrArg TrivSqZeroExt.fst hd
    exact ⟨2, by ext1 <;> simp [pow_two, h]⟩
  have hU : ⊤ ≤ (p.left ≫ ψ) ⁻¹ᵁ U := by
    intro q _
    obtain ⟨q, rfl⟩ := hs q
    rw [← e₁] at h₁
    exact h₁ (Set.mem_univ q)
  have key : ∀ (l : ℂ × ℂ →ₗ[ℂ] ℂ) (x : epsR ℂ ⟶ G) (hx : ⊤ ≤ (x.left ≫ ψ) ⁻¹ᵁ U), sqZeroMap l ≫ p = x →
      (evalPt (R := DualNumber ℂ) (x.left ≫ ψ) U hx f).snd =
        l (evalPt (R := TrivSqZeroExt ℂ (ℂ × ℂ)) (p.left ≫ ψ) U hU f).snd := by
    rintro l _ hx rfl
    have := evalPt_spMap_comp (TrivSqZeroExt.map l).toRingHom (p.left ≫ ψ) U hU hx f
    exact (congrArg TrivSqZeroExt.snd this).trans (TrivSqZeroExt.snd_map _ _)
  rw [key _ _ _ e₁, key _ _ _ e₂, key _ _ _ e₃]
  rfl

theorem isDerivAt0_mul {v w : epsR ℂ ⟶ G} (hv : IsTangent v) (hw : IsTangent w) {a b : Fin g → ℂ}
    (ha : IsDerivAt0 e a (v.left ≫ ψ)) (hb : IsDerivAt0 e b (w.left ≫ ψ)) :
    IsDerivAt0 e (a + b) ((v * w).left ≫ ψ) := by
  have hm := isTangent_mul hv hw
  refine ⟨(tangent_base hm).trans ((tangent_base hv).symm.trans ha.1), fun U h f => ?_⟩
  rw [map_add, ← ha.2 U (tangent_le hm hv h) f, ← hb.2 U (tangent_le hm hw h) f]
  exact snd_evalPt_mul hv hw U f h _ _

end Fibre

end GlobalTheory.HolLieFrame

namespace GlobalTheory

open HolLieFrame
open scoped Matrix nonZeroDivisors
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G.Key ReciprocityTheory.ChartRestriction.G.Key.Chi

end GlobalTheory
