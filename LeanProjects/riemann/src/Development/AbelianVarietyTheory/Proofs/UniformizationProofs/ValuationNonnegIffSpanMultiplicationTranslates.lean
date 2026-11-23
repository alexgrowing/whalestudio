import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DataRigidSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.VRatioGtStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ValuationMultiplicationInvariance
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PeriodicValuation
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBC
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
import Development.AbelianVarietyTheory.Definitions.Uniformization.AllDV
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFrameRatio
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsProjectiveRep
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpBijFAndExpandsFLin
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.DimEqRankAddDim
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.NuGeIffOfIsActOfOfQkToAkU
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsGenOfTop
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationTorsionIdentificationWithPairing
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniqueThetaConst
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PrimitiveExpansionThetaPullbackHeisenbergTranslaStatement

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

namespace GlobalTheory.ThetaSpan

theorem eq_sum_translates {F E G : Type} [Field F] [AddCommGroup E] [Module F E] [Module.Finite F E] [Fintype G]
    (U : G → E ≃ₗ[F] E) (e : G → G → F) (hU : ∀ x y w, U x (U y w) = e x y • U y (U x w))
    (hsep : ∀ x y, x ≠ y → ∃ z, e x z ≠ e y z) (hcard : Fintype.card G = Module.finrank F E ^ 2)
    (hn : (Module.finrank F E : F) ≠ 0) (f : E →ₗ[F] F) (s₀ : E) (hf : f s₀ ≠ 0) (s : E) :
    s = ∑ x, (f ((U x).symm s) / ((Module.finrank F E : F) * f s₀)) • U x s₀ := by
  classical
  have orth : ∀ x y, LinearMap.trace F E ((U y).symm.toLinearMap ∘ₗ (U x).toLinearMap) =
      if x = y then (Module.finrank F E : F) else 0 := by
    intro x y
    split_ifs with h
    · subst h
      have : (U x).symm.toLinearMap ∘ₗ (U x).toLinearMap = LinearMap.id := by ext w; simp
      rw [this, LinearMap.trace_id]
    · obtain ⟨z, hz⟩ := hsep x y h
      set M := (U y).symm.toLinearMap ∘ₗ (U x).toLinearMap with hM
      have h1 : e y z • (U z).symm.conj M = e x z • M := by
        ext w
        apply (U z).injective
        apply (U y).injective
        have a := hU y z ((U y).symm (U x w))
        simp only [hM, LinearMap.smul_apply, LinearEquiv.conj_apply_apply, LinearEquiv.symm_symm, map_smul,
          LinearEquiv.apply_symm_apply, LinearMap.comp_apply, LinearEquiv.coe_coe] at a ⊢
        rw [a, hU x z w, smul_comm]
      have h2 := congrArg (LinearMap.trace F E) h1
      rw [map_smul, map_smul, LinearMap.trace_conj', smul_eq_mul, smul_eq_mul] at h2
      by_contra h3
      exact hz (mul_right_cancel₀ h3 h2).symm
  have coef : ∀ (a : G → F) (y : G), LinearMap.trace F E ((U y).symm.toLinearMap ∘ₗ ∑ x, a x • (U x).toLinearMap) =
      a y * (Module.finrank F E : F) := by
    intro a y
    have : (U y).symm.toLinearMap ∘ₗ ∑ x, a x • (U x).toLinearMap =
        ∑ x, a x • ((U y).symm.toLinearMap ∘ₗ (U x).toLinearMap) := by
      ext w; simp
    rw [this, map_sum]
    simp only [map_smul, orth, smul_eq_mul, mul_ite, mul_zero]
    simp
  have hli : LinearIndependent F fun x => (U x).toLinearMap := by
    rw [Fintype.linearIndependent_iff]
    intro a ha y
    have := coef a y
    rw [ha, LinearMap.comp_zero, map_zero] at this
    exact (mul_eq_zero.1 this.symm).resolve_right hn
  have hsp : Submodule.span F (Set.range fun x => (U x).toLinearMap) = ⊤ :=
    hli.span_eq_top_of_card_eq_finrank' (by rw [Module.finrank_linearMap, hcard, sq])
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun F).1
    (hsp.ge (Submodule.mem_top (x := f.smulRight s)))
  have hc : ∀ y, a y = f ((U y).symm s) / (Module.finrank F E : F) := by
    intro y
    have := coef a y
    rw [ha, show (U y).symm.toLinearMap ∘ₗ f.smulRight s = f.smulRight ((U y).symm s) from by ext w; simp,
      LinearMap.trace_smulRight] at this
    rw [this, mul_div_cancel_right₀ _ hn]
  have h0 := congrArg (fun T : E →ₗ[F] E => (f s₀)⁻¹ • T s₀) ha
  simp only [LinearMap.smulRight_apply, LinearMap.sum_apply, LinearMap.smul_apply, LinearEquiv.coe_coe, smul_smul,
    inv_mul_cancel₀ hf, one_smul, Finset.smul_sum] at h0
  refine h0.symm.trans (Finset.sum_congr rfl fun x _ => ?_)
  rw [hc x]
  congr 1
  field_simp

theorem exists_transport {F Γ E M : Type} [Field F] [CommRing Γ] [AddCommGroup E] [Module F E] [AddCommGroup M]
    [Module Γ M] (κ : F → Γ) (Ψ : M ≃+ E) (h : ∀ c a, Ψ (κ c • a) = c • Ψ a) (ρ : M ≃ₗ[Γ] M) :
    ∃ U : E ≃ₗ[F] E, ∀ a, U (Ψ a) = Ψ (ρ a) := by
  refine ⟨{ (Ψ.symm.trans ρ.toAddEquiv).trans Ψ with map_smul' := fun c w => ?_ }, fun a => ?_⟩
  · obtain ⟨a, rfl⟩ := Ψ.surjective w
    show Ψ (ρ (Ψ.symm (c • Ψ a))) = c • Ψ (ρ (Ψ.symm (Ψ a)))
    rw [← h, Ψ.symm_apply_apply, Ψ.symm_apply_apply, map_smul, h]
  · show Ψ (ρ (Ψ.symm (Ψ a))) = _
    rw [Ψ.symm_apply_apply]

theorem exists_pos_le {I : Type} [Finite I] (a : I → WithTop ℚ) (h : ∀ i, 0 < a i) :
    ∃ r : ℚ, 0 < r ∧ ∀ i, (r : WithTop ℚ) ≤ a i := by
  cases isEmpty_or_nonempty I with
  | inl _ => exact ⟨1, one_pos, fun i => isEmptyElim i⟩
  | inr _ =>
    obtain ⟨i, hi⟩ := Finite.exists_min a
    by_cases ht : a i = ⊤
    · exact ⟨1, one_pos, fun j => le_top.trans (ht ▸ hi j)⟩
    · obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.1 ht
      refine ⟨r, ?_, fun j => hr ▸ hi j⟩
      have := h i
      rw [← hr] at this
      exact_mod_cast this

end GlobalTheory.ThetaSpan

namespace GlobalTheory.ThetaSpan
open GlobalTheory.UT.CoefBasic

theorem exists_value {R : Type} [CommRing R] [IsDomain R] (A : PolAV (Spec (CommRingCat.of (FractionRing R))))
    {F : Type} [Field F] [Algebra (FractionRing R) F] {ρ : LB.Gen (A.L.pull (eSec A.A))} (hρ : ρ.IsGen) {k : ℕ}
    (t : SecA A F k) : ∃ c : F, ∀ z J, Good A.L z J → sA t (ptSecT A.A 1).left z J =
      @id ((TFK (R := R) F).left.presheaf.stalk z) (cst (R := R) F z c) *
        (val (rigT A.A A.L ρ (TFK (R := R) F) (k : ℤ)) (𝟙 _) z J).val := by
  have hr : ∀ (z : (TFK (R := R) F).left) J, Good A.L z J →
      val (rigT A.A A.L ρ (TFK (R := R) F) (k : ℤ)) (𝟙 _) z J =
        val (L := A.L) (φ := fun _ : PUnit => eSec A.A) (ε := fun _ => 1) ρ (TFK (R := R) F).hom z J ^ (k : ℤ) := by
    intro z J hJ
    have hm := hJ.mem (fun _ : Fin 1 => (TFK (R := R) F).hom ≫ eSec A.A) (𝟙 _)
    refine (map_zpow _ _ _).trans (congrArg (· ^ (k : ℤ)) ?_)
    refine (gm_res _ z _ hm _).trans ((gm_pull (𝟙 _) (TFK (R := R) F).hom z _ (rigT_le A.A A.L _ hm) _).trans ?_)
    rfl
  obtain ⟨z⟩ := exists_pt (R := R) (F := F)
  obtain ⟨J', hJ'⟩ := exists_good' A.isLB (Z := (TFK (R := R) F).left) z
  obtain ⟨c, hc⟩ := cstH_surj z (@id ((TFK (R := R) F).left.presheaf.stalk z) (sA t (ptSecT A.A 1).left z J' *
    ((val (rigT A.A A.L ρ (TFK (R := R) F) (k : ℤ)) (𝟙 _) z J')⁻¹).val))
  refine ⟨c, fun z' J hJ => ?_⟩
  obtain rfl := pt_eq z z'
  have a₁ := sval_tr (L := A.L) (φ := fun _ : Fin 1 => (snd (TFK (R := R) F) A.A).left) (ε := fun _ => (k : ℤ)) t
    (ptSecT A.A (1 : TFK (R := R) F ⟶ A.A)).left hJ hJ'
  have a₂ := val_tr (L := A.L) (φ := fun _ : PUnit => eSec A.A) (ε := fun _ => 1) hρ (TFK (R := R) F).hom hJ hJ'
  have e : (ptSecT A.A (1 : TFK (R := R) F ⟶ A.A)).left ≫ (snd (TFK (R := R) F) A.A).left =
      (TFK (R := R) F).hom ≫ eSec A.A := by
    rw [← Over.comp_left, ptSecT, lift_snd]; rfl
  rw [Fintype.prod_unique, e] at a₁
  rw [Fintype.prod_unique, zpow_one] at a₂
  have hc' : @id ((TFK (R := R) F).left.presheaf.stalk z) (cst (R := R) F z c) = sA t (ptSecT A.A 1).left z J' *
      ((val (rigT A.A A.L ρ (TFK (R := R) F) (k : ℤ)) (𝟙 _) z J')⁻¹).val := (cst_eq z c).trans hc
  rw [hc', hr z J hJ, hr z J' hJ', a₂, mul_zpow, _root_.mul_assoc, ← Units.val_mul, inv_mul_cancel_comm_assoc]
  exact a₁.trans (_root_.mul_comm _ _)

theorem exists_comm (hL : Laws) {S : Scheme.{0}} [IsLocallyNoetherian S] (P : PolAV S) {F : Type} [Field F]
    [IsAlgClosed F] (q : Spec (CommRingCat.of F) ⟶ S) {N : ℕ} (hN : (N : F) ≠ 0)
    (θ : {x : Over.mk q ⟶ P.A // x ^ N = 1} → ThetaGrp P.A P.L N (Over.mk q)) (hθ : ∀ a, (θ a).pt = a.1) :
    ∃ e : {x : Over.mk q ⟶ P.A // x ^ N = 1} → {x : Over.mk q ⟶ P.A // x ^ N = 1} → Γ((Over.mk q).left, ⊤)ˣ,
      (∀ a b, CommIsOf P.A P.L N (θ a) (θ b) (e a b)) ∧ ∀ a b, a ≠ b → ∃ z, e a z ≠ e b z := by
  obtain ⟨hex, hmul, -, -⟩ := hL.weil S P N (Over.mk q)
  choose e he using fun a b : {x : Over.mk q ⟶ P.A // x ^ N = 1} => (hex a.1 b.1 a.2 b.2).exists
  refine ⟨e, fun a b => (GlobalLift.weilIs_iff_commIsOf hL.globalFns P.isAb P.isLB _ _ _).1 ?_, fun a b hab => ?_⟩
  · rw [hθ, hθ]
    exact he a b
  · by_contra h
    push Not at h
    have hd : (a.1 * b.1⁻¹) ^ N = 1 := by rw [mul_pow, inv_pow, a.2, b.2, inv_one, _root_.mul_one]
    refine hab (Subtype.ext (mul_inv_eq_one.1 (ThetaRep.eq_one_of_weilIs hL P q hN _ hd fun y hy => ?_)))
    have h₁ := hmul _ _ _ _ _ (he ⟨_, hd⟩ ⟨y, hy⟩) (he b ⟨y, hy⟩)
    rw [inv_mul_cancel_right] at h₁
    have h₂ := (hex a.1 y a.2 hy).unique h₁ (he a ⟨y, hy⟩)
    rw [h, mul_eq_right] at h₂
    exact h₂ ▸ he ⟨_, hd⟩ ⟨y, hy⟩

end GlobalTheory.ThetaSpan

namespace GlobalTheory.ThetaSpan

theorem transport_of_bijective {F Γ E M : Type} [Field F] [CommRing Γ] [AddCommGroup E] [Module F E] [AddCommGroup M]
    [Module Γ M] (κ : F ≃+* Γ) (Y : M → E) (hY : Function.Bijective Y)
    (h : ∀ c a a', Y (κ c • a + a') = c • Y a + Y a') :
    Module.finrank F E = Module.finrank Γ M ∧ ∃ U : (M ≃ₗ[Γ] M) → E ≃ₗ[F] E, (∀ ρ a, U ρ (Y a) = Y (ρ a)) ∧
      ∀ (ρ ρ' : M ≃ₗ[Γ] M) (c : Γ), (∀ a, ρ (ρ' a) = c • ρ' (ρ a)) → ∀ r, U ρ (U ρ' r) = κ.symm c • U ρ' (U ρ r) := by
  let E₀ : M →+ E := AddMonoidHom.mk' Y fun a a' => by
    have := h 1 a a'
    rwa [map_one, one_smul, one_smul] at this
  let Ψ := AddEquiv.ofBijective E₀ hY
  have hΨ : ∀ c a, Ψ (κ c • a) = c • Ψ a := fun c a => by
    have : Ψ (κ c • a + 0) = c • Ψ a + Ψ 0 := h c a 0
    rwa [add_zero, map_zero, add_zero] at this
  choose U hU using fun ρ => exists_transport κ Ψ hΨ ρ
  refine ⟨congrArg Cardinal.toNat (rank_eq_of_equiv_equiv κ Ψ.symm κ.bijective fun c r => ?_), U, hU,
    fun ρ ρ' c hc r => ?_⟩
  · obtain ⟨a, rfl⟩ := Ψ.surjective r
    rw [← hΨ, Ψ.symm_apply_apply, Ψ.symm_apply_apply]
  · obtain ⟨a, rfl⟩ := Ψ.surjective r
    rw [hU, hU, hU, hU, hc, ← hΨ, κ.apply_symm_apply]

theorem exists_operators (hG : GlobalFnsSt) {S : Scheme.{0}} (P : PolAV S) (k : ℤ) (T : Over S) {F E : Type} [Field F]
    [AddCommGroup E] [Module F E] (κ : F ≃+* Γ(T.left, ⊤)) (X : LB.Sec (LPow P.A P.L k T) → E)
    (hX : Function.Bijective X)
    (hlin : ∀ c t t' t'', (∀ j, t''.f j = liftFun P.A _ (κ c) * t.f j + t'.f j) → X t'' = c • X t + X t') :
    Module.finrank F E = Module.finrank Γ(T.left, ⊤) (SecM P.A P.L k T) ∧
    ∃ (U : ThetaGrp P.A P.L k T → E ≃ₗ[F] E), (∀ θ t, ∃ t', IsActOf P.A P.L k θ t t' ∧ X t' = U θ (X t)) ∧
      ∀ θ θ' c, CommIsOf P.A P.L k θ θ' c → ∀ r, U θ (U θ' r) = κ.symm c.val • U θ' (U θ r) := by
  have hE₀ : Function.Bijective fun a : SecM P.A P.L k T => X (SecM.toSec P.A a) := by
    refine ⟨fun a a' h => congrArg (SecM.ofSec P.A) (hX.1 h), fun r => ?_⟩
    obtain ⟨t, ht⟩ := hX.2 r
    exact ⟨SecM.ofSec P.A t, ht⟩
  obtain ⟨h₁, U, hU, hc⟩ := transport_of_bijective κ _ hE₀ fun c a a' => hlin c _ _ _ fun j => rfl
  obtain ⟨act, hact, hcomm, -, -⟩ := thetaGrp_acts_linearly hG S P k T
  exact ⟨h₁, fun θ => U (act θ),
    fun θ t => ⟨SecM.toSec P.A (act θ (SecM.ofSec P.A t)), (hact _ _ _).2 rfl, (hU _ (SecM.ofSec P.A t)).symm⟩,
    fun θ θ' c h => hc _ _ _ (hcomm _ _ _ h)⟩

end GlobalTheory.ThetaSpan

namespace GlobalTheory.UT
open GlobalTheory.ThetaSpan

theorem nuGe_zero_iff_span_translates : LL → TwistBCSpanStatement → TWM.VRatioGtStatement → TWStatement → UUStatement → AllUV fun {V} _ _ _ {ϖ} hϖ {D} Q {F} _ _ {v} hv {A} {G} _ _ U => ∀ w₀ ρ, NormW U.toUnifPre w₀ ρ → ∀ (th : SecA A F 1) (ϑ : Fam D.toPre F 1), U.ExpandsF F 1 w₀ th ϑ → Prim D Q v ϑ → ∀ (m : ℕ), Odd m → IsUnit (m : V) → 3 ≤ m → ∀ s : Fam D.toPre F (m ^ 2), NuGe D Q F v (m ^ 2) s 0 ↔ ∃ (n : ℕ) (a : Fin n → F) (x : Fin n → (TFK (R := V) F ⟶ A.A)) (t : Fin n → SecA A F (m ^ 2)) (c : Fin n → F) (r : Fin n → Fam D.toPre F (m ^ 2)), (∀ i, 0 ≤ v (a i) ∧ x i ^ (m ^ 2) = 1 ∧ ThC A ρ m th (x i) (t i) (c i) ∧ U.ExpandsF F (m ^ 2) w₀ (t i) (r i)) ∧ s = ∑ i, a i • r i := by
  intro hLL hBC hVR hTW hUU V _ _ _ _ hc ϖ hϖ D Q hQ F _ _ _ v hv A G _ _ hG U w₀ ρ hN th ϑ hth hprim m hm hmu _ s
  have hL := hLL.1
  have hP := GlobalTheory.T.primitive_expansion_thetaPullback_heisenbergTranslates hLL hBC hVR hTW hUU V hc ϖ hϖ D Q hQ F v hv A G hG U w₀ ρ hN th ϑ hth hprim m hm hmu
  constructor
  swap
  · rintro ⟨n, a, x, t, c, r, h, rfl⟩
    refine GlobalTheory.GermJets.nuGe_sum _ _ _ fun i _ => ?_
    obtain ⟨h₁, h₂, h₃, h₄⟩ := h i
    have := NuGe.smul Q (q := 0) h₁ ((isSmul_iff _ _ _).2 rfl) (hP _ _ _ _ h₂ h₃ h₄).1
    rwa [add_zero] at this
  intro hs
  have hA : AdmBase V (maximalIdeal V) := ⟨inferInstance, inferInstance, inferInstance, hc⟩
  have hN1 : 1 ≤ m ^ 2 := Nat.one_le_pow _ _ hm.pos
  have hvm : v (m : F) = 0 := by
    have := hv (algebraMap V (FractionRing V) m) 0 ⟨hmu.unit, by simp⟩
    rwa [map_natCast, map_natCast] at this
  have hm0 : (m : F) ≠ 0 := fun h => by
    rw [h, AddValuation.map_zero] at hvm
    exact WithTop.top_ne_zero hvm
  have hN0 : ((m ^ 2 : ℕ) : F) ≠ 0 := by rw [Nat.cast_pow]; exact pow_ne_zero _ hm0
  obtain ⟨hB, hlin⟩ := expBijF_and_expandsF_lin hLL V _ hA D A G hG U
  have hdim : A.g = D.toPre.rank + D.toPre.P.g := dim_eq_rank_add_dim hLL V _ hA D A G hG U
  obtain ⟨f, hf₁, hf₂, -⟩ := GlobalTheory.TorsionIso.torsion_eq hLL V _ hA D A G hG U F (m ^ 2) hN1
  have hT := GlobalTheory.existsUnique_thetaConst hLL V A F ρ hN.2.1 m hm th
  obtain ⟨b, hbi, hb0, hb⟩ := hUU V ϖ hϖ D Q hQ F v hv (Or.inl inferInstance) (m ^ 2) hN1
  obtain ⟨hB₁, hB₂⟩ := hB F (m ^ 2) hN1 w₀ hN.1

  choose E hE hEu using hB₁
  let κ : F ≃+* Γ((TFK (R := V) F).left, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of F)).symm.commRingCatIsoToRingEquiv
  have hEb : Function.Bijective E := by
    refine ⟨fun a a' h => (hB₂ (E a)).unique (hE _) (h ▸ hE a'), fun r => ?_⟩
    obtain ⟨t, ht, -⟩ := hB₂ r
    exact ⟨t, (hEu t r ht).symm⟩
  obtain ⟨hrk, T₀, hact, hcomm⟩ := exists_operators hL.globalFns A ((m ^ 2 : ℕ) : ℤ) (TFK (R := V) F) κ E hEb
    fun c t t' t'' h => (hEu _ _ (hlin F (m ^ 2) w₀ t t' t'' _ _ c (hE _) (hE _) h)).symm
  replace hrk : Module.finrank F (Fam D.toPre F (m ^ 2)) = (m ^ 2) ^ A.g :=
    hrk.trans (ThetaRep.finrank_secM hL.secBaseChange A hN1 (jFK (R := V) F))
  haveI : Module.Finite F (Fam D.toPre F (m ^ 2)) := Module.finite_of_finrank_pos (by rw [hrk]; positivity)
  let B := basisOfLinearIndependentOfCardEqFinrank' b hbi (by rw [Fintype.card_fin, hrk, hdim])
  have hBb : ∀ i, B i = b i := fun i => congrFun (coe_basisOfLinearIndependentOfCardEqFinrank' _ _ _) i
  have hint : ∀ r, NuGe D Q F v (m ^ 2) r 0 → ∀ i, 0 ≤ v (B.repr r i) := fun r hr i => by
    obtain ⟨c, h₁, rfl⟩ := (hb r).1 hr
    simp only [← hBb]
    rw [B.repr_sum_self]
    exact h₁ i

  have hcard : Nat.card {x : TFK (R := V) F ⟶ A.A // x ^ (m ^ 2) = 1} = (m ^ 2) ^ (2 * A.g) :=
    (hL.mulN _ A (m ^ 2) hN1).2.2.2.2 F (jFK (R := V) F) hN0
  haveI : Finite {x : TFK (R := V) F ⟶ A.A // x ^ (m ^ 2) = 1} :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; positivity)
  letI := Fintype.ofFinite {x : TFK (R := V) F ⟶ A.A // x ^ (m ^ 2) = 1}
  have hθ : ∀ x : {x : TFK (R := V) F ⟶ A.A // x ^ (m ^ 2) = 1},
      ∃ θ, SymLift A.A A.L ((m ^ 2 : ℕ) : ℤ) (m ^ 2) x.1 θ := fun x => by
    obtain ⟨_, ⟨_, _, θ, -, -, -, h, -⟩, -⟩ := hT x.1 x.2
    exact ⟨θ, h⟩
  choose θ hθ using hθ
  obtain ⟨e, he, hsep⟩ := exists_comm hL A (jFK (R := V) F) hN0 θ fun a => (hθ a).pt_eq
  let T := fun x => T₀ (θ x)
  choose act hact hTa using hact
  have hnu : ∀ x r q, NuGe D Q F v (m ^ 2) r q ↔ NuGe D Q F v (m ^ 2) (T x r) q := fun x r q => by
    obtain ⟨a, rfl⟩ := hEb.2 r
    obtain ⟨p, hp⟩ := hf₂ x.1 x.2
    rw [← hTa]
    exact nuGe_iff_of_isActOf_of_qkToAkU hL hTW V ϖ hϖ D A G U hB Q hQ F v hv (m ^ 2) hN1 w₀ hN.1 (θ x) p
      ((hf₁ p _).2 ((hθ x).pt_eq.trans hp.symm)) (m ^ 2) hN1 (by rw [(hθ x).pt_eq]; exact x.2) (hθ x).pow_eq
      _ _ _ _ (hE _) (hE _) (hact _ _) q

  obtain ⟨_, ⟨α, s₁, -, a₁, a₂, a₃, -⟩, -⟩ := hT 1 (one_pow _)
  choose c hcv using fun x => exists_value A hN.2.1 (k := m ^ 2) (act (θ x) s₁)
  have hC : ∀ x, ThC A ρ m th x.1 (act (θ x) s₁) (c x) := fun x =>
    ⟨α, s₁, θ x, a₁, a₂, a₃, hθ x, hact _ _, hcv x⟩
  set s₀ := E s₁ with hs₀
  have hEx : ∀ x, U.ExpandsF F (m ^ 2) w₀ (act (θ x) s₁) (T x s₀) := fun x => by
    rw [hs₀, ← hTa]; exact hE _
  obtain ⟨p₁, p₂⟩ := hP _ _ _ _ (one_pow _) (hC ⟨1, one_pow _⟩) (hEx _)
  rw [← hnu] at p₁
  simp only [← hnu] at p₂
  obtain ⟨i, hi⟩ : ∃ i, v (B.repr s₀ i) = 0 := by
    by_contra h
    push Not at h
    obtain ⟨r, hr, hr'⟩ := exists_pos_le (fun i => v (B.repr s₀ i)) fun i => lt_of_le_of_ne (hint _ p₁ i) (h i).symm
    refine p₂ r hr ?_
    rw [← B.sum_repr s₀]
    refine GlobalTheory.GermJets.nuGe_sum _ _ _ fun i _ => ?_
    have := NuGe.smul Q (hr' i) ((isSmul_iff _ _ _).2 rfl) (hb0 i)
    rwa [zero_add, ← hBb] at this
  have hi0 : B.coord i s₀ ≠ 0 := fun h => by
    rw [show B.repr s₀ i = 0 from h, AddValuation.map_zero] at hi
    exact WithTop.top_ne_zero hi
  have key := eq_sum_translates T (fun x y => κ.symm (e x y).val) (fun x y => hcomm _ _ _ (he x y))
    (fun x y h => by
      obtain ⟨z, hz⟩ := hsep x y h
      exact ⟨z, fun h' => hz (Units.ext (κ.symm.injective h'))⟩)
    (by rw [← Nat.card_eq_fintype_card, hcard, hrk, ← pow_mul, ← pow_mul, ← pow_mul]; congr 1; ring)
    (by rw [hrk, Nat.cast_pow]; exact pow_ne_zero _ hN0) (B.coord i) s₀ hi0 s
  let j := (Fintype.equivFin {x : TFK (R := V) F ⟶ A.A // x ^ (m ^ 2) = 1}).symm
  refine ⟨_, _, fun k => (j k).1, _, fun k => c (j k), fun k => T (j k) s₀,
    fun k => ⟨?_, (j k).2, hC _, hEx _⟩, key.trans (Equiv.sum_comp j _).symm⟩
  have h₁ := hint ((T (j k)).symm s) ((hnu (j k) _ _).2 (by rwa [LinearEquiv.apply_symm_apply])) i
  have h₂ : v ((Module.finrank F (Fam D.toPre F (m ^ 2)) : F) * B.coord i s₀) = 0 := by
    rw [AddValuation.map_mul, hrk, Nat.cast_pow, Nat.cast_pow, AddValuation.map_pow, AddValuation.map_pow, hvm,
      smul_zero, smul_zero, zero_add]
    exact hi
  have h₃ : (Module.finrank F (Fam D.toPre F (m ^ 2)) : F) * B.coord i s₀ ≠ 0 := fun h => by
    rw [h, AddValuation.map_zero] at h₂
    exact WithTop.top_ne_zero h₂
  have h₄ := AddValuation.map_mul v (B.coord i ((T (j k)).symm s) /
    ((Module.finrank F (Fam D.toPre F (m ^ 2)) : F) * B.coord i s₀))
    ((Module.finrank F (Fam D.toPre F (m ^ 2)) : F) * B.coord i s₀)
  rw [div_mul_cancel₀ _ h₃, h₂, add_zero] at h₄
  exact h₄ ▸ h₁

end GlobalTheory.UT
