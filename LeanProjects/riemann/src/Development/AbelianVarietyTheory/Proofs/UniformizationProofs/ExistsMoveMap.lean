import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.ThetaMove
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExpansionBijectiveOverFields
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniqueSecPull
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpandsAtTransport
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PowEqOneOfPush
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ThetaGrpActsLinearly

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ThetaSpecialise

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.FieldBaseChange

section Algebra

variable {S F F' N V V' : Type} [CommRing S] [IsDomain S] [ValuationRing S] [Field F] [Field F']
  [AddCommGroup N] [Module S N] [AddCommGroup V] [Module F V] [AddCommGroup V'] [Module F' V']

theorem exists_ratio {fS : S →+* F} {π : S →+* F'} (hf : Function.Injective fS) (mv : N →ₛₗ[fS] V) (mv' : N →ₛₗ[π] V')
    (ind : ∀ (n : ℕ) (c : Fin n → F), (∀ a : Fin n → S, ∑ i, fS (a i) * c i = 0 → ∀ i, a i = 0) →
      ∀ a : Fin n → N, ∑ i, c i • mv (a i) = 0 → ∀ i, a i = 0)
    {I : Type} (a b : I → N) (l : F) (h : ∀ i, mv (a i) = l • mv (b i)) (ha : ∃ i, mv' (a i) ≠ 0)
    (hb : ∃ i, mv' (b i) ≠ 0) : ∃ l' : F', l' ≠ 0 ∧ ∀ i, mv' (a i) = l' • mv' (b i) := by
  have inj : ∀ x y, mv x = mv y → x = y := fun x y e => sub_eq_zero.1 (ind 1 (fun _ => 1) (fun a ha i => by
    rw [Fin.sum_univ_one, _root_.mul_one] at ha
    rw [Subsingleton.elim i 0]; exact hf (ha.trans (map_zero _).symm)) (fun _ => x - y)
    (by rw [Fin.sum_univ_one, one_smul, map_sub, e, sub_self]) 0)
  obtain ⟨i, hi⟩ := ha
  obtain ⟨j, hj⟩ := hb
  by_cases H : ∀ a : Fin 2 → S, ∑ i, fS (a i) * ![1, -l] i = 0 → ∀ i, a i = 0
  · refine absurd ?_ hi
    have e : a i = 0 := ind 2 _ H ![a i, b i] (by simp [Fin.sum_univ_two, h]) 0
    rw [e, map_zero]
  · push_neg at H
    obtain ⟨u, hu, m, hm⟩ := H
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, _root_.mul_one, mul_neg] at hu
    have inj' : ∀ x, fS x = 0 → x = 0 := fun x e => hf (e.trans (map_zero _).symm)
    have h1 : u 1 ≠ 0 := fun e => by
      rw [e, map_zero, zero_mul, neg_zero, add_zero] at hu
      fin_cases m
      exacts [hm (inj' _ hu), hm e]
    have h1' : fS (u 1) ≠ 0 := fun e => h1 (inj' _ e)
    obtain ⟨t, ht | ht⟩ := ValuationRing.cond (u 0) (u 1)
    · have h0 : fS (u 0) ≠ 0 := fun e => h1' (by rw [← ht, map_mul, e, zero_mul])
      have e : fS t * l = 1 := mul_left_cancel₀ h0 (by rw [← ht, map_mul] at hu; linear_combination -hu)
      have k : ∀ i, mv' (b i) = π t • mv' (a i) := fun i => by
        rw [← map_smulₛₗ]
        exact congrArg mv' (inj _ _ (by rw [map_smulₛₗ, h, smul_smul, e, one_smul]))
      have p : π t ≠ 0 := fun e => hj (by rw [k, e, zero_smul])
      exact ⟨(π t)⁻¹, inv_ne_zero p, fun i => by rw [k, smul_smul, inv_mul_cancel₀ p, one_smul]⟩
    · have e : fS t = l := mul_left_cancel₀ h1' (by rw [← ht, map_mul] at hu; linear_combination hu)
      have k : ∀ i, mv' (a i) = π t • mv' (b i) := fun i => by
        rw [← map_smulₛₗ]
        exact congrArg mv' (inj _ _ (by rw [map_smulₛₗ, h, e]))
      exact ⟨π t, fun e => hi (by rw [k, e, zero_smul]), k⟩

end Algebra

section Flat

variable {S F : Type} [CommRing S] [CommRing F] {fS : S →+* F} {X Y Y' : Scheme.{0}}
  {π : Y ⟶ Spec (CommRingCat.of S)} {π' : Y' ⟶ Spec (CommRingCat.of F)} {p : Y' ⟶ Y}
  (H : IsPullback p π' π (Spec.map (CommRingCat.ofHom fS))) [Flat π]

theorem fn_indep {U : Y.Opens} (hU : IsAffineOpen U) {n : ℕ} (c : Fin n → F)
    (hc : ∀ a : Fin n → S, ∑ i, fS (a i) * c i = 0 → ∀ i, a i = 0) (a : Fin n → FnOver π U)
    (h : ∑ i, c i • pullFn H.w (le_refl (p ⁻¹ᵁ U)) (a i) = 0) (i : Fin n) : a i = 0 := by
  let : Algebra S F := fS.toAlgebra
  have po := (isIso_pushoutSection_iff H (US := ⊤) (UT := ⊤) (UX := U) (UY := p ⁻¹ᵁ U) le_top
    le_top (by simp)).mp (isIso_pushoutSection_of_isAffineOpen H _ _ _ (isAffineOpen_top _)
      (isAffineOpen_top _) hU)
  have po' : IsPushout (CommRingCat.ofHom (constHom π U)) (CommRingCat.ofHom fS) (p.app U)
      (CommRingCat.ofHom (constHom π' (p ⁻¹ᵁ U))) := by
    refine po.of_iso (Scheme.ΓSpecIso (.of S)) (Iso.refl _) (Scheme.ΓSpecIso (.of F)) (Iso.refl _) ?_ ?_ ?_ ?_
    · ext x; simp [constHom, Scheme.Hom.appLE]; rfl
    · rw [← Scheme.ΓSpecIso_naturality, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
      rfl
    · simp [Scheme.Hom.app_eq_appLE]
    · ext x; simp [constHom, Scheme.Hom.appLE]; rfl
  let : Algebra (FnOver π U) (FnOver π' (p ⁻¹ᵁ U)) := (p.app U).hom.toAlgebra
  let : Algebra S (FnOver π' (p ⁻¹ᵁ U)) := ((constHom π' (p ⁻¹ᵁ U)).comp fS).toAlgebra
  have : IsScalarTower S F (FnOver π' (p ⁻¹ᵁ U)) := .of_algebraMap_eq fun r ↦ rfl
  have : IsScalarTower S (FnOver π U) (FnOver π' (p ⁻¹ᵁ U)) :=
    .of_algebraMap_eq fun r ↦ (congrArg (fun q => q.hom r) po'.w).symm
  have hpo : Algebra.IsPushout S (FnOver π U) F (FnOver π' (p ⁻¹ᵁ U)) :=
    CommRingCat.isPushout_iff_isPushout.mp po'
  have fl : Module.Flat S (FnOver π U) := by
    have f₁ : RingHom.Flat (π.appLE ⊤ U le_top).hom :=
      HasRingHomProperty.appLE (P := @Flat) π inferInstance ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ le_top
    have f₂ : RingHom.Flat (Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom :=
      RingHom.Flat.of_bijective (ConcreteCategory.bijective_of_isIso _)
    exact f₂.comp f₁
  have li : LinearIndependent S c := Fintype.linearIndependent_iff.2 fun g hg => hc g hg
  have li' := Fintype.linearIndependent_iff.1 (Module.Flat.linearIndependent_one_tmul (S := FnOver π U) li)
  refine li' a (hpo.out.equiv.injective ?_) i
  rw [map_zero, ← h, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, hpo.out.equiv_tmul, one_smul, Algebra.smul_def, Algebra.smul_def, mul_comm]
  congr 1
  show _ = (Y'.presheaf.map (𝟙 _)).hom _
  rw [CategoryTheory.Functor.map_id]; rfl

theorem sec_indep {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} (ε : K → ℤ) {φ' : K → (Y' ⟶ X)}
    (hφ : ∀ k, φ' k = p ≫ φ k) {n : ℕ} (c : Fin n → F)
    (hc : ∀ a : Fin n → S, ∑ i, fS (a i) * c i = 0 → ∀ i, a i = 0) (a : Fin n → SecOver π (LB.LinComb L φ ε))
    (h : ∑ i, c i • pullOver L ε H.w hφ (a i) = 0) (i : Fin n) : a i = 0 := by
  refine SecOver.ext _ _ fun (j : K → L.ι) => fn_ext fun y hy => ?_
  obtain ⟨_, ⟨U, hU, rfl⟩, hyU, hle⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open hy (LB.wchart L φ j).isOpen
  have hle : U ≤ LB.wchart L φ j := hle
  have hle' : p ⁻¹ᵁ U ≤ LB.wchart L φ' j := fun z hz => (wchart_eq hφ j).ge (hle hz)
  have e := fn_indep H hU c hc (fun i => resFn π hle (chartLin π (LB.LinComb L φ ε) j (a i))) (by
    have := congrArg (resFn π' hle' ∘ₗ chartLin π' (LB.LinComb L φ' ε) j) h
    rw [map_zero, map_sum] at this
    refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) this
    rw [map_smul]
    refine congrArg (c i • ·) (fn_ext fun z hz => ?_)
    exact ((gs_pullFn H.w _ _ _ z hz).trans (gs_res (𝟙 Y' ≫ p) z hle hz _)).trans
      ((gs_res _ z hle' hz _).trans (gs_pullFn H.w _ _ _ z (hle' hz))).symm) i
  exact ((gs_res (𝟙 Y) y hle hyU _).symm.trans ((congrArg (gs (𝟙 Y) y U) e).trans (gs_zero' _ y U hyU))).trans
    (gs_zero' _ y _ hy).symm

end Flat

section Move

variable {X X' Y Y' : Scheme.{0}} {L : LB X} {L' : LB X'} {Φ : X' ⟶ X} {K : Type} [Fintype K]

def PSec (w : LB.Iso L' (L.pull Φ)) (φ' : K → (Y' ⟶ X')) (φ : K → (Y ⟶ X)) (ε : K → ℤ) (h : Y' ⟶ Y)
    (s' : LB.Sec (LB.LinComb L' φ' ε)) (s : LB.Sec (LB.LinComb L φ ε)) : Prop :=
  ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (p : K → L.ι) (q : K → L'.ι),
    (∀ κ, Φ (φ' κ (r z)) ∈ L.U (p κ)) → (∀ κ, φ' κ (r z) ∈ L'.U (q κ)) →
    gs (r ≫ h) z (LB.wchart L φ p) (s.f p) =
      (∏ κ, gw w (r ≫ φ' κ) z (p κ) (q κ) ^ ε κ).val * gs r z (LB.wchart L' φ' q) (s'.f q)

variable {w : LB.Iso L' (L.pull Φ)} {φ' : K → (Y' ⟶ X')} {φ : K → (Y ⟶ X)} {ε : K → ℤ} {h : Y' ⟶ Y}
  {S F : Type} [CommRing S] [CommRing F] {fS : S →+* F}
  {π : Y ⟶ Spec (CommRingCat.of S)} {π' : Y' ⟶ Spec (CommRingCat.of F)}

theorem exists_moveMap (hL : L.IsLB) (hL' : L'.IsLB) (hw : w.IsGen) (hc : ∀ κ, φ' κ ≫ Φ = h ≫ φ κ)
    (hp : h ≫ π = π' ≫ Spec.map (CommRingCat.ofHom fS)) :
    ∃ mv : SecOver π (LB.LinComb L φ ε) →ₛₗ[fS] SecOver π' (LB.LinComb L' φ' ε),
      ∀ s s', PSec w φ' φ ε h s' s ↔ mv s = s' := by
  have ex := SecPull.existsUnique_secPull _ _ _ _ _ _ _ hL hL' w hw K φ' φ ε h hc
  choose mv hmv using fun s : SecOver π (LB.LinComb L φ ε) => (ex s).exists
  have m : ∀ {Z : Scheme.{0}} {r : Z ⟶ Y'} {z : Z} {p : K → L.ι}, (∀ κ, Φ (φ' κ (r z)) ∈ L.U (p κ)) →
      (r ≫ h) z ∈ LB.wchart L φ p := fun hp => SecPull.mem_wchart_comp hc (Set.mem_iInter.2 hp)
  refine ⟨{ toFun := mv
            map_add' := fun a b => (ex _).unique (hmv _) fun Z r z p q hp hq => ?_
            map_smul' := fun c a => (ex _).unique (hmv _) fun Z r z p q hp₁ hq => ?_ },
    fun s s' => ⟨fun H => (ex s).unique (hmv s) H, fun H => H ▸ hmv s⟩⟩
  · refine (gs_add _ z _ (m hp) _ _).trans (Eq.trans ?_ (congrArg _ (gs_add r z _ (mem_wchart.2 hq) _ _)).symm)
    rw [mul_add]
    exact congrArg₂ (· + ·) (hmv a Z r z p q hp hq) (hmv b Z r z p q hp hq)
  · refine (gs_smul π _ z _ (m hp₁) _ _).trans
      (Eq.trans ?_ (congrArg _ (gs_smul π' r z _ (mem_wchart.2 hq) _ _)).symm)
    rw [mul_left_comm, Category.assoc, hp, ← Category.assoc, constVal_specMap]
    exact congrArg _ (hmv a Z r z p q hp₁ hq)

theorem move_indep (hL : L.IsLB) (hL' : L'.IsLB) (hc : ∀ κ, φ' κ ≫ Φ = h ≫ φ κ)
    (H : IsPullback h π' π (Spec.map (CommRingCat.ofHom fS))) [Flat π]
    (mv : SecOver π (LB.LinComb L φ ε) → SecOver π' (LB.LinComb L' φ' ε)) (hmv : ∀ s, PSec w φ' φ ε h (mv s) s)
    (n : ℕ) (c : Fin n → F) (hi : ∀ a : Fin n → S, ∑ i, fS (a i) * c i = 0 → ∀ i, a i = 0)
    (a : Fin n → SecOver π (LB.LinComb L φ ε)) (e : ∑ i, c i • mv (a i) = 0) (i : Fin n) : a i = 0 := by
  refine sec_indep H ε (φ' := fun κ => h ≫ φ κ) (fun _ => rfl) c hi a (sec_ext' hL fun y J hJ => ?_) i
  choose J' hJ' using fun ψ : Y' ⟶ X' => exists_chart hL' (ψ y)
  have hJ' : Good L' y J' := hJ'
  have e' := congrArg (fun t => sval t (𝟙 _) y J') e
  beta_reduce at e'
  rw [sval_sum' hJ', sval_zero' hJ'] at e'
  rw [sval_sum' hJ, sval_zero' hJ, ← mul_zero (∏ κ, ExpTrans.om w y J J' (𝟙 _ ≫ φ' κ) ^ ε κ).val, ← e',
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [sval_smul' hJ, sval_smul' hJ', sval_pullOver _ _ _ _ hJ,
    ExpTrans.sec_val w φ' φ ε h hc _ _ (𝟙 _) y (hmv (a i) _ (𝟙 _) y) hJ hJ', mul_left_comm]

end Move

end GlobalTheory.ThetaSpecialise
