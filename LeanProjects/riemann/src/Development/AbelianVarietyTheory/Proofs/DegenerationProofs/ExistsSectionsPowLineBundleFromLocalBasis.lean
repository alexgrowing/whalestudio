import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.LocTheta
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaSystemBaseSectionValueChart
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.BasisOriginValuesRegularAndUnit
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.BasisValueAtOrigin
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUnitExtendOfGeneric
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.LinearIndependentOnFibresOfClosedPoints
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FiniteResidueFieldOfIsClosedOfLocallyOfFiniteTyp
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsIntegralOfSmoothFieldOfConnectedSpace
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.PolBaseChangeOfRelAmpleLocal

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ZH.PowSec
open GlobalTheory.Points

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} {ρ : S.Real} {M : RatModel o Ω}
  {U₀ : M.Z.Opens} {Q : ZHPre ρ M U₀}

theorem spMap_id (Ω : Type) [Field Ω] : spMap (RingHom.id Ω) = 𝟙 (Sp Ω) := Spec.map_id _

theorem exists_origin (hU : (U₀ : Set M.Z).Nonempty) {a : Q.L.L.ι}
    (ha : ⊤ ≤ (M.pt ≫ eSec Q.G) ⁻¹ᵁ Q.L.L.U a) : ∃ ξ : Ω, ξ ^ ((S.r * S.N) ^ 2) = 1 ∧
      ∀ (c : S.J → Ω) (v : Ω), GV Q c a Ω (M.pt ≫ eSec Q.G) v →
        (c ⬝ᵥ S.ev 0) * (ξ * valF M.pt _ (Q.L.rig.s (fun _ => a)).val) ^ S.N = v := by
  have he : eSec Q.G ≫ Q.G.hom = 𝟙 M.Z := Over.w η[Q.G]
  obtain ⟨g, r, jP, h1, h2, h3, hj⟩ := exists_data' Q hU (M.pt ≫ eSec Q.G) (RingHom.id Ω)
    (by rw [spMap_id, Category.id_comp]; exact (Category.assoc _ _ _).trans ((congrArg (M.pt ≫ ·) he).trans
          (Category.comp_id _)))
  have : Mono Q.φ := (MorphismProperty.monomorphisms _).of_isPullback Q.cart.1.flip
    (inferInstanceAs (Mono U₀.ι))
  have h2' : (g ≫ pullback.snd _ _) ≫ U₀.ι = M.pt := by
    rw [Category.assoc, h2, spMap_id, Category.id_comp]
  obtain ⟨e', c1, c2⟩ : ∃ e' : U₀.toScheme ⟶ pullback ρ.P.A.hom Q.u₀, e' ≫ Q.φ = U₀.ι ≫ eSec Q.G ∧
      e' ≫ pullback.fst _ _ = Q.u₀ ≫ eSec ρ.P.A := by
    have c1 := PolBaseChange.eSec_comm Q.cart
    have c2 := PolBaseChange.eSec_comm (isGrpPullback_pullback ρ.P.A Q.u₀)
    exact ⟨_, c1, c2⟩
  have e1 : g = (g ≫ pullback.snd _ _) ≫ e' := by
    refine (cancel_mono Q.φ).1 (h1.trans (Eq.symm ((Category.assoc _ _ _).trans ?_)))
    refine (congrArg ((g ≫ pullback.snd _ _) ≫ ·) c1).trans ?_
    exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ eSec Q.G) h2')
  have e2 : g ≫ pullback.fst ρ.P.A.hom Q.u₀ = spMap S.R.val.toRingHom ≫ eSec ρ.P.A := by
    refine (congrArg (· ≫ pullback.fst ρ.P.A.hom Q.u₀) e1).trans ((Category.assoc _ _ _).trans ?_)
    refine (congrArg ((g ≫ pullback.snd _ _) ≫ ·) c2).trans ?_
    exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ eSec ρ.P.A) (Q.u₀_gen _ h2'))
  have ha' : ⊤ ≤ (g ≫ Q.φ) ⁻¹ᵁ Q.L.L.U a := h1 ▸ ha
  obtain ⟨ξ, hξ, hs⟩ := GlobalTheory.basis_value_at_origin o Ω S ρ Ω S.R.val.toRingHom r jP (h3.trans e2)
    ((top_le_preimage_iff _ _).1 (h3 ▸ hj))
  refine ⟨ξ, hξ, fun c v H => ?_⟩
  have e := H _ g r jP h1 h2 h3 hj
  have hw := Q.w_rig Ω g M.pt _ jP a h1 e2 ((top_le_preimage_iff _ _).1 hj) ((top_le_preimage_iff _ _).1 ha')
  simp only [hs, hw, zpow_natCast] at e
  refine mul_left_cancel₀ (pow_ne_zero S.N (val_unit_ne g (le_w Q hj ha') (Q.w.s (fun _ => jP, fun _ => a))))
    (Eq.trans ?_ e)
  rw [dotProduct, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  change _ = c l * (S.ev 0 l * _)
  ring

section Open
variable {W : M.Z.Opens} {j : Sp Ω ⟶ W.toScheme} (hj : j ≫ W.ι = M.pt)
include hj

theorem le_of_mem {z : W.toScheme} {V : W.toScheme.Opens} (hz : z ∈ V) : ⊤ ≤ j ⁻¹ᵁ V :=
  top_le_preimage_of_specializes (fun w => W.ι.isOpenEmbedding.isInducing.specializes_iff.1 (by
    rw [← Scheme.Hom.comp_apply, hj]; exact M.pt_specializes w _)) hz

theorem Reg.mem_O {z : W.toScheme} {F : ∀ (K : Type) [Field K], (Sp K ⟶ W.toScheme) → K} (h : Reg z F) :
    F Ω j ∈ M.O (W.ι z) := by
  obtain ⟨V, f, hz, hf⟩ := h
  rw [← hf Ω j (le_of_mem hj hz), ← NormGlue.valF_comp_appIso W.ι V f j, hj]
  exact RatModel.valF_mem_O (U := W.ι ''ᵁ V) ⟨z, hz, rfl⟩ _

theorem exists_unit_val (V : W.toScheme.Opens) (c : Ω)
    (h : ∀ z ∈ V, c ≠ 0 ∧ c ∈ M.O (W.ι z) ∧ c⁻¹ ∈ M.O (W.ι z)) :
    ∃ u : Γ(W.toScheme, V)ˣ, ⊤ ≤ j ⁻¹ᵁ V → valF j V u.val = c := by
  by_cases hV : ⊤ ≤ j ⁻¹ᵁ V
  swap
  · exact ⟨1, fun h => (hV h).elim⟩
  have hz : j (IsLocalRing.closedPoint Ω) ∈ V := hV trivial
  have hne : ((W.ι ''ᵁ V : M.Z.Opens) : Set M.Z).Nonempty := ⟨_, _, hz, rfl⟩
  obtain ⟨f, hf⟩ := (RatModel.mem_ringOn_iff_exists hne).1 ((RatModel.mem_ringOn (x := c)).2 (by
    rintro _ ⟨z, hz, rfl⟩; exact (h z hz).2.1))
  obtain ⟨f', hf'⟩ := (RatModel.mem_ringOn_iff_exists hne).1 ((RatModel.mem_ringOn (x := c⁻¹)).2 (by
    rintro _ ⟨z, hz, rfl⟩; exact (h z hz).2.2))
  have hu : IsUnit f := IsUnit.of_mul_eq_one f' (M.res_injective _ hne (by
    rw [map_mul, map_one, M.res_apply, M.res_apply, hf, hf', mul_inv_cancel₀ (h _ hz).1]))
  refine ⟨(hu.map (W.ι.appLE _ V (W.ι.preimage_image_eq V).ge).hom).unit, fun _ => ?_⟩
  refine (valR_appLE j W.ι _ hV f).trans ?_
  rw [hj]
  exact hf

end Open

theorem exists_local [ArithBase o Ω] (hS : S.Over₀ M U₀) {W : M.Z.Opens} (hW : (W : Set M.Z).Nonempty)
    {O : LB (Q.G.hom ⁻¹ᵁ W).toScheme} {τ : S.J → O.Sec} (hO : O.IsLB) (hτ : ⨆ i, nonzeroLocus (τ i) = ⊤)
    {b : S.J → S.J → Ω}
    (hp : ∀ (a : Q.L.L.ι) (k : O.ι) (K : Type) [Field K] (β : Ω →+* K) (h : Sp K ⟶ (Q.G.hom ⁻¹ᵁ W).toScheme),
      (h ≫ (Q.G.hom ⁻¹ᵁ W).ι) ≫ Q.G.hom = spMap β ≫ M.pt → ⊤ ≤ (h ≫ (Q.G.hom ⁻¹ᵁ W).ι) ⁻¹ᵁ Q.L.L.U a →
      ⊤ ≤ h ⁻¹ᵁ O.U k → ∃ v, Ratio Q (Q.G.hom ⁻¹ᵁ W).ι τ b a k K h v)
    (hA : ∀ z ∈ W, (∀ i, b i ⬝ᵥ S.ev 0 ∈ M.O z) ∧ ∃ i, b i ⬝ᵥ S.ev 0 ≠ 0 ∧ (b i ⬝ᵥ S.ev 0)⁻¹ ∈ M.O z)
    (a : Q.L.L.ι) (k : O.ι) :
    ∃ u : Γ((Q.G.hom ⁻¹ᵁ W).toScheme, LB.wchart Q.L.L (fun _ : Fin 1 => (Q.G.hom ⁻¹ᵁ W).ι) (fun _ => a) ⊓ O.U k)ˣ,
      ∀ (K : Type) [Field K] (β : Ω →+* K) (h : Sp K ⟶ (Q.G.hom ⁻¹ᵁ W).toScheme),
      (h ≫ (Q.G.hom ⁻¹ᵁ W).ι) ≫ Q.G.hom = spMap β ≫ M.pt → ⊤ ≤ (h ≫ (Q.G.hom ⁻¹ᵁ W).ι) ⁻¹ᵁ Q.L.L.U a →
      ⊤ ≤ h ⁻¹ᵁ O.U k → Ratio Q (Q.G.hom ⁻¹ᵁ W).ι τ b a k K h (valF h _ u.val) := by
  have := ArithBase.ded (o := o) (Ω := Ω)
  have := M.lft
  have : IsLocallyNoetherian M.Z := LocallyOfFiniteType.isLocallyNoetherian M.s
  have := Q.semi.smooth
  have := Q.semi.geomConnected
  have : GeometricallyIntegral Q.G.hom := grpObj_geometricallyIntegral_of_smooth _ Q.G
  have := IsNormalScheme.of_pred hS.normal
  have := EndoExtend.isPreimmersion_pt M
  have := EndoExtend.flat_pt M
  set ν := (Q.G.hom ⁻¹ᵁ W).ι with hν
  let p := Q.G.hom ∣_ W
  have hp' : p ≫ W.ι = ν ≫ Q.G.hom := morphismRestrict_ι _ _
  have : GeometricallyIntegral p :=
    MorphismProperty.of_isPullback (P := @GeometricallyIntegral) (isPullback_morphismRestrict Q.G.hom W).flip ‹_›
  let j : Sp Ω ⟶ W.toScheme := IsOpenImmersion.lift W.ι M.pt (by
    rw [Scheme.Opens.range_ι]; exact (top_le_preimage_iff _ _).1 (M.top_le_preimage_pt hW))
  have hj : j ≫ W.ι = M.pt := IsOpenImmersion.lift_fac _ _ _
  have sq : IsPullback (𝟙 _) j M.pt W.ι := .of_horiz_isIso_mono ⟨(Category.id_comp _).trans hj.symm⟩
  have : IsPreimmersion j := MorphismProperty.of_isPullback (P := @IsPreimmersion) sq ‹_›
  have : Flat j := MorphismProperty.of_isPullback (P := @Flat) sq ‹_›
  have : IsDominant j := ⟨dense_iff_inter_open.2 fun V hV ⟨z, hz⟩ =>
    ⟨_, le_of_mem hj (V := ⟨V, hV⟩) hz (x := IsLocalRing.closedPoint Ω) trivial, _, rfl⟩⟩
  have he₀ : eSec Q.G ≫ Q.G.hom = 𝟙 M.Z := Over.w η[Q.G]
  let e : W.toScheme ⟶ (Q.G.hom ⁻¹ᵁ W).toScheme := (isPullback_morphismRestrict Q.G.hom W).lift
    (𝟙 _) (W.ι ≫ eSec Q.G) (by
      exact (Category.id_comp _).trans ((Category.assoc _ _ _).trans ((congrArg (W.ι ≫ ·) he₀).trans
        (Category.comp_id _))).symm)
  have he : e ≫ p = 𝟙 _ := IsPullback.lift_fst _ _ _ _
  have he' : e ≫ ν = W.ι ≫ eSec Q.G := IsPullback.lift_snd _ _ _ _
  have : IsIntegral (pullback p j) :=
    GeometricallyIntegral.geometrically_isIntegral j _ _ (.of_hasPullback p j)
  let N := LB.div (LB.LinComb Q.L.L (K := Fin 1) (fun _ => ν) (fun _ => (S.N : ℤ))) O
  have hJ : (pullback.fst p j ≫ ν) ≫ Q.G.hom = pullback.snd p j ≫ M.pt := by
    rw [Category.assoc, ← hp', pullback.condition_assoc, hj]
  choose t ht using fun a : N.ι => exists_unit hS.ne hτ (hp (a.1 0) a.2) (pullback.fst p j) _ hJ
    (pullback.fst p j ⁻¹ᵁ N.U a) (fun _ hy => Set.mem_iInter.1 hy.1 0) (fun _ hy => hy.2)
  have hov : ∀ {K : Type} [Field K] (h : Sp K ⟶ pullback p j), ((h ≫ pullback.fst p j) ≫ ν) ≫ Q.G.hom =
      spMap (Spec.preimage (h ≫ pullback.snd p j)).hom ≫ M.pt := fun h => by
    rw [show spMap (Spec.preimage (h ≫ pullback.snd p j)).hom = h ≫ pullback.snd p j from Spec.map_preimage _,
      Category.assoc h _ M.pt, ← hJ]
    simp only [Category.assoc]
  obtain ⟨σ, hσ⟩ := GenericExtend.exists_unit_extend_of_generic W.toScheme _ Ω j
    ((isNormalScheme_iff_pred _).1 inferInstance) ‹_› ‹_› ‹_› p e N he inferInstance ‹_›
    (LB.isLB_div (LB.isLB_linComb Q.L.isLB _ _) hO) t (by
      rintro ⟨a, k⟩ ⟨a', k'⟩ K _ h h1 h2
      obtain ⟨a, rfl⟩ : ∃ jL, a = fun _ => jL := ⟨a 0, funext fun i => by rw [Subsingleton.elim i 0]⟩
      obtain ⟨a', rfl⟩ : ∃ jL, a' = fun _ => jL := ⟨a' 0, funext fun i => by rw [Subsingleton.elim i 0]⟩
      replace h1 := (top_le_preimage_iff _ _).2 h1
      replace h2 := (top_le_preimage_iff _ _).2 h2
      have a1 := of_le_wchart (le_preimage_mono _ inf_le_left h1) 0
      have a2 := of_le_wchart (le_preimage_mono _ inf_le_left h2) 0
      have k1 := le_preimage_mono _ inf_le_right h1
      have k2 := le_preimage_mono _ inf_le_right h2
      refine ((ht _ K h h1).unique hS.ne hτ (hov h) a1 k1 ((ht _ K h h2).chart a2 k2 a1 k1)).trans
        (congrArg (· * _) (Eq.symm ((val_div_g _ _ _ _ _ h1 h2).trans (congrArg (· * _) ?_))))
      exact val_linComb_g (I := Fin 1) _ _ _ _ _ _ a1 a2) (by
      intro a
      let h₀ : Sp Ω ⟶ pullback p j := pullback.lift (j ≫ e) (𝟙 _) (by simp [he])
      have hh₀ : h₀ ≫ pullback.fst p j = j ≫ e := pullback.lift_fst _ _ _
      have hh₁ : (j ≫ e) ≫ ν = M.pt ≫ eSec Q.G := by
        rw [Category.assoc, he']; exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ eSec Q.G) hj)
      obtain ⟨u, hu⟩ := exists_unit_val hj (e ⁻¹ᵁ N.U a) (valF h₀ _ (t a).val) (fun z hz => by
        have m0 : ⊤ ≤ (j ≫ e) ⁻¹ᵁ N.U a := le_of_mem hj hz
        have H := ht a Ω h₀ (by rw [← hh₀] at m0; exact m0)
        rw [hh₀] at H
        have m1 := of_le_wchart (le_preimage_mono _ inf_le_left m0) 0
        obtain ⟨ξ, hξ, hv⟩ := exists_origin (Q := Q) hS.ne (a := a.1 0) (hh₁ ▸ m1)
        have hv' := fun i => hv _ _ (hh₁ ▸ H.2 i)
        have hn : (S.r * S.N) ^ 2 ≠ 0 := pow_ne_zero _ (Nat.mul_ne_zero (by have := S.r_pos; omega)
          (by have := S.N_ge; omega))
        have hroot : ∀ x : Ω, x ^ ((S.r * S.N) ^ 2) = 1 → x ∈ M.O (W.ι z) := fun x hx => by
          have := RatModel.isIntegrallyClosed_O hS.normal (W.ι z)
          obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 (IsIntegral.of_pow (R := M.O (W.ι z))
            (Nat.pos_of_ne_zero hn) (hx ▸ isIntegral_one))
          exact hy ▸ y.2
        have m2 : W.ι z ∈ (Q.L.L.pull (eSec Q.G)).U (fun _ => a.1 0) := Set.mem_iInter.2 fun _ => by
          have : (e ≫ ν) z ∈ Q.L.L.U (a.1 0) := Set.mem_iInter.1 hz.1 0
          rw [he'] at this
          exact this
        have r1 := (Reg.val W.ι (Q.L.rig.s fun _ => a.1 0).val m2).mem_O hj
        have r2 := (Reg.inv W.ι (Q.L.rig.s fun _ => a.1 0).val (by
          rw [Scheme.basicOpen_of_isUnit _ (Units.isUnit _)]; exact m2)).mem_O hj
        have r3 := val_unit_ne M.pt (M.top_le_preimage_pt ⟨_, m2⟩) (Q.L.rig.s fun _ => a.1 0)
        simp only [hj] at r1 r2
        have x0 : ξ ≠ 0 := fun h => by rw [h, zero_pow hn] at hξ; exact zero_ne_one hξ
        obtain ⟨hA1, i', hA2, hA3⟩ := hA (W.ι z) z.2
        refine ⟨H.1, ?_, ?_⟩
        · obtain ⟨i, hi⟩ := exists_mem_basicOpen hτ (e z) hz.2
          have q : valF (j ≫ e) _ ((τ i).f a.2) ≠ 0 := ((le_preimage_basicOpen_iff (j ≫ e)
            (le_preimage_mono _ inf_le_right m0) _).1 (le_of_mem hj (V := e ⁻¹ᵁ Scheme.basicOpen _ ((τ i).f a.2)) hi)).ne_zero
          rw [(eq_mul_inv_iff_mul_eq₀ q).2 (hv' i).symm]
          exact mul_mem (mul_mem (hA1 i) (pow_mem (mul_mem (hroot ξ hξ) r1) _)) ((Reg.inv e _ hi).mem_O hj)
        · have q := mul_ne_zero hA2 (pow_ne_zero S.N (mul_ne_zero x0 r3))
          have key : ∀ A c t : Ω, A ≠ 0 → A = c * t → c⁻¹ = t * A⁻¹ := by
            rintro _ c t h rfl
            have := left_ne_zero_of_mul h
            have := right_ne_zero_of_mul h
            field_simp
          rw [key _ _ _ q (hv' i'), mul_inv, ← inv_pow, mul_inv]
          exact mul_mem ((Reg.val e _ hz.2).mem_O hj) (mul_mem hA3 (pow_mem (mul_mem
            (hroot _ (by rw [inv_pow, hξ, inv_one])) r2) _)))
      refine ⟨u, fun h hh hr => ?_⟩
      obtain rfl : h = h₀ := (cancel_mono (pullback.fst p j)).1 (hh.trans hh₀.symm)
      exact (hu ((top_le_preimage_iff (j ≫ e) _).2 hr)).symm)
  refine ⟨σ (fun _ => a, k), fun K _ β h h1 h2 h3 => ?_⟩
  obtain ⟨h, rfl⟩ : ∃ h' : Sp K ⟶ pullback p j, h' ≫ pullback.fst p j = h :=
    ⟨pullback.lift h (spMap β) ((cancel_mono W.ι).1 (by
      rw [Category.assoc, Category.assoc, hp', hj, ← h1, Category.assoc])), pullback.lift_fst _ _ _⟩
  have m : ⊤ ≤ (h ≫ pullback.fst p j) ⁻¹ᵁ N.U (fun _ => a, k) := le_inf' (le_wchart _ _ _ fun _ => h2) h3
  have := ht (fun _ => a, k) K h m
  rw [← hσ _ K h ((top_le_preimage_iff _ _).1 m)] at this
  exact this

theorem exists_pack [ArithBase o Ω] (hS : S.Over₀ M U₀) {EE : M.Lat S.J} (hQ : Q.SecO EE) {W : M.Z.Opens}
    (haff : IsAffineOpen W) (hW : (W : Set M.Z).Nonempty) {b : Matrix S.J S.J Ω} {d : Ω} (hd : d ≠ 0)
    (hb : ∀ z ∈ W, EE.E z = Submodule.span (M.O z) (Set.range b))
    (hA : ∀ z ∈ W, (∀ i, (b i ⬝ᵥ S.ev 0) / d ∈ M.O z) ∧
      ∃ i, (b i ⬝ᵥ S.ev 0) / d ≠ 0 ∧ ((b i ⬝ᵥ S.ev 0) / d)⁻¹ ∈ M.O z) :
    ∃ (O : LB (Q.G.hom ⁻¹ᵁ W).toScheme) (τ : S.J → O.Sec), O.IsLB ∧ ⨆ i, nonzeroLocus (τ i) = ⊤ ∧
      (∀ (a : Q.L.L.ι) (k : O.ι), ∃ u : Γ((Q.G.hom ⁻¹ᵁ W).toScheme,
          LB.wchart Q.L.L (fun _ : Fin 1 => (Q.G.hom ⁻¹ᵁ W).ι) (fun _ => a) ⊓ O.U k)ˣ,
        ∀ (K : Type) [Field K] (β : Ω →+* K) (h : Sp K ⟶ (Q.G.hom ⁻¹ᵁ W).toScheme),
        (h ≫ (Q.G.hom ⁻¹ᵁ W).ι) ≫ Q.G.hom = spMap β ≫ M.pt → ⊤ ≤ (h ≫ (Q.G.hom ⁻¹ᵁ W).ι) ⁻¹ᵁ Q.L.L.U a →
        ⊤ ≤ h ⁻¹ᵁ O.U k →
        Ratio Q (Q.G.hom ⁻¹ᵁ W).ι τ (fun i l => b i l / d) a k K h (valF h _ u.val)) ∧
      ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ M.Z), Set.range x ⊆ W → ∀ c : S.J → K,
        (∀ (g : Sp K ⟶ (Q.G.hom ⁻¹ᵁ W).toScheme) (k : O.ι), (g ≫ (Q.G.hom ⁻¹ᵁ W).ι) ≫ Q.G.hom = x →
          ∑ i, c i * valF g _ ((τ i).f k) = 0) → c = 0 := by
  obtain ⟨O, τ, hO, hτ, hp, hind, -⟩ := hQ W b haff hb
  refine ⟨O, τ, hO, hτ, exists_local hS hW hO hτ (fun a k K _ β h h1 h2 h3 => ?_) (fun z hz => ?_), ?_⟩
  · obtain ⟨g, r, jP, g1, g2, g3, gj⟩ := exists_data' Q hS.ne _ β h1
    obtain ⟨c, hc, H⟩ := hp K β g h r jP k g2 g1.symm g3 ((top_le_preimage_iff _ _).1 gj)
      ((top_le_preimage_iff _ _).1 h3)
    have z1 := zpow_ne_zero (S.N : ℤ) (val_unit_ne g (le_w Q gj (g1 ▸ h2)) (Q.w.s (fun _ => jP, fun _ => a)))
    have z2 : β d ≠ 0 := (map_ne_zero β).2 hd
    refine ⟨c / β d / _, div_ne_zero (div_ne_zero hc z2) z1, fun i => GV.of_one h2 g1 g2 g3 gj ?_⟩
    simp only [map_div₀, div_mul_eq_mul_div, ← Finset.sum_div, H]
    field_simp
  · have e : ∀ i, (fun l => b i l / d) ⬝ᵥ S.ev 0 = (b i ⬝ᵥ S.ev 0) / d := fun i => by
      simp only [dotProduct, div_mul_eq_mul_div, Finset.sum_div]
    simpa only [e] using hA z hz
  · intro K _ _ x hx c hc
    have := ArithBase.ft (o := o) (Ω := Ω)
    have := MinorModel.locallyOfFiniteType_int M
    have := jacobsonSpace_of_locallyOfFiniteType_int (M.s ≫ spMap (algebraMap ℤ o))
    have := Q.semi.smooth
    have hp' : Q.G.hom ∣_ W ≫ W.ι = (Q.G.hom ⁻¹ᵁ W).ι ≫ Q.G.hom := morphismRestrict_ι _ _
    let e := Fintype.equivFin S.J
    have hl : ∀ {K : Type} [Field K] (x : Sp K ⟶ M.Z), Set.range x ⊆ W → ∃ x' : Sp K ⟶ W.toScheme, x' ≫ W.ι = x :=
      fun x hx => ⟨IsOpenImmersion.lift W.ι x (by rwa [Scheme.Opens.range_ι]), IsOpenImmersion.lift_fac _ _ _⟩
    have hr : ∀ {K : Type} [Field K] (x : Sp K ⟶ W.toScheme), Set.range x = {x (IsLocalRing.closedPoint K)} :=
      fun x => Set.eq_singleton_iff_unique_mem.2 ⟨⟨_, rfl⟩, by
        rintro _ ⟨w, rfl⟩; exact congrArg x (Subsingleton.elim (α := PrimeSpectrum _) _ _)⟩
    obtain ⟨x, rfl⟩ := hl x hx
    have key := FibreLinInd.linearIndependent_on_fibres_of_closedPoints _ _
      (W.ι ≫ M.s ≫ spMap (algebraMap ℤ o)) (Q.G.hom ∣_ W) O hO _ (fun i => τ (e.symm i)) (fun z hz => by
        have h1 : IsClosed ({W.ι z} : Set M.Z) := isClosed_singleton_of_isLocallyClosed_singleton (by
          have := hz.isLocallyClosed.image W.ι.isOpenEmbedding.isInducing
            W.ι.isOpenEmbedding.isOpen_range.isLocallyClosed
          rwa [Set.image_singleton] at this)
        obtain ⟨K, _, y, hy, H⟩ := hind (W.ι z) z.2 h1
        obtain ⟨y, rfl⟩ := hl y (by rw [hy]; exact Set.singleton_subset_iff.2 z.2)
        have h2 : y (IsLocalRing.closedPoint K) = z := W.ι.isOpenEmbedding.injective
          (show (y ≫ W.ι) _ ∈ ({W.ι z} : Set M.Z) from hy ▸ ⟨_, rfl⟩)
        refine ⟨K, inferInstance, y, h2 ▸ hr y, fun c hc => ?_⟩
        have := H (c ∘ e) fun g k hg => by
          rw [← hc g k ((cancel_mono W.ι).1 (by rw [Category.assoc, hp', hg])), ← e.sum_comp]
          simp only [Function.comp_apply, Equiv.symm_apply_apply]
        exact funext fun i => by simpa using congrFun this (e.symm i)) _ K x (hr x) (c ∘ e.symm) (fun g k hg => by
        rw [← hc g k (by rw [Category.assoc, ← hp', ← Category.assoc, hg])]
        exact e.symm.sum_comp fun i => c i * valF g _ ((τ i).f k))
    exact funext fun i => by simpa using congrFun key (e i)

theorem exists_sections : GlobalTheory.Published.SemistableReductionSt → ThmUSt → Laws → Laws2 → UTorsSt → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (Q : ZHPre ρ M U₀), S.Over₀ M U₀ → S.IsEE M U₀ EE → Q.SecO EE → ∀ (W : M.Z.Opens) (x₀ : S.Gam) (b : Matrix S.J S.J Ω), (∀ z ∈ W, x₀ ∈ S.supI M z ∧ EE.E z = Submodule.span (M.O z) (Set.range b)) → ∃ σ : S.J → ∀ j, Γ(Q.G.left, Q.G.hom ⁻¹ᵁ W ⊓ (LB.LinComb Q.L.L (K := Fin 1) (fun _ => 𝟙 Q.G.left) (fun _ => (S.N : ℤ))).U j), (∀ i, σ i ∈ secOn (LB.LinComb Q.L.L (K := Fin 1) (fun _ => 𝟙 Q.G.left) (fun _ => (S.N : ℤ))) (Q.G.hom ⁻¹ᵁ W) ∧ GenVal ρ M U₀ Q.u₀ Q.G Q.φ Q.L.L Q.w S.N ρ.s (fun l => b i l / S.th x₀) _ (σ i)) ∧ ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ M.Z), Set.range x ⊆ W → (∀ g : Sp K ⟶ Q.G.left, g ≫ Q.G.hom = x → ∃ i j, valF g _ (σ i j) ≠ 0) ∧ ∀ c : S.J → K, (∀ (g : Sp K ⟶ Q.G.left) (j : _), g ≫ Q.G.hom = x → ∑ i, c i * valF g _ (σ i j) = 0) → c = 0 := by
  intro h1 h2 h3 h4 h5 o Ω _ _ _ _ S ρ M U₀ EE Q hS hE hQ W x₀ b hb
  have hloc := fun (z : M.Z) (hz : z ∈ W) => (exists_isAffineOpen_mem_and_subset hz).imp
    fun W' (h : IsAffineOpen W' ∧ z ∈ W' ∧ (W' : Set M.Z) ⊆ W) => And.intro h (exists_pack hS hQ h.1 ⟨z, h.2.1⟩
      (hb z hz).1.1 (fun y hy => (hb y (h.2.2 hy)).2) fun y hy =>
        basis_origin_values_regular_and_unit h1 h2 h3 h4 h5 o Ω S ρ M U₀ EE hS hE y x₀ b (hb y (h.2.2 hy)).1
          (hb y (h.2.2 hy)).2)
  obtain ⟨F, _, β, g, r, jP, g2, -, -, hξ⟩ := Q.exists_generic hS.ne
  have hβ : (g ≫ Q.φ) ≫ Q.G.hom = spMap β ≫ M.pt := by
    rw [Category.assoc, Q.cart.1.w]; exact g2
  generalize g ≫ Q.φ = ξ at hξ hβ
  clear g2 g r jP
  have hid : ∀ {K : Type} [Field K] {g : Sp K ⟶ Q.G.left} {j : Fin 1 → Q.L.L.ι},
      ⊤ ≤ g ⁻¹ᵁ (Q.G.hom ⁻¹ᵁ W ⊓ LB.wchart Q.L.L (fun _ => 𝟙 Q.G.left) j) → ⊤ ≤ g ⁻¹ᵁ Q.L.L.U (j 0) :=
    fun h _ hz => Set.mem_iInter.1 (h hz).2 0
  choose σ hσ using fun (i : S.J) (j : Fin 1 → Q.L.L.ι) =>
    exists_glue (Q.G.hom ⁻¹ᵁ W ⊓ LB.wchart Q.L.L (fun _ => 𝟙 Q.G.left) j)
      (GV Q (fun l => b i l / S.th x₀) (j 0)) ξ hξ (fun h v v' H H' => H.unique hS.ne hβ (hid h) H')
      (fun y hy => by
        obtain ⟨W', ⟨-, hz, -⟩, O, τ, hO, -, hu, -⟩ := hloc _ hy.1
        let y' : (Q.G.hom ⁻¹ᵁ W').toScheme := ⟨y, hz⟩
        obtain ⟨k, hk⟩ := exists_chart hO y'
        obtain ⟨u, hu⟩ := hu (j 0) k
        have hy' : y' ∈ LB.wchart Q.L.L (fun _ : Fin 1 => (Q.G.hom ⁻¹ᵁ W').ι) (fun _ => j 0) ⊓ O.U k :=
          ⟨Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hy.2 0, hk⟩
        refine ⟨_, ((Q.G.hom ⁻¹ᵁ W').ι.appIso _).inv.hom (u.val * resG _ inf_le_right ((τ i).f k)),
          ⟨y', hy', rfl⟩, fun K _ g q1 q2 => ?_⟩
        obtain ⟨h, rfl⟩ : ∃ h : Sp K ⟶ (Q.G.hom ⁻¹ᵁ W').toScheme, h ≫ (Q.G.hom ⁻¹ᵁ W').ι = g :=
          ⟨IsOpenImmersion.lift _ g (by
            rintro _ ⟨w, rfl⟩
            obtain ⟨v, -, hv⟩ := q1 (x := w) trivial
            exact ⟨v, hv⟩), IsOpenImmersion.lift_fac _ _ _⟩
        rw [Scheme.Hom.comp_preimage, Scheme.Hom.preimage_image_eq] at q1
        rw [NormGlue.valF_comp_appIso]
        intro β' g' r' jP' k1 k2 k3 kj
        refine ((hu K β' h (by rw [← k1, Category.assoc, Q.cart.1.w]; exact k2) (hid q2)
          (le_preimage_mono h inf_le_right q1)).2 i β' g' r' jP' k1 k2 k3 kj).trans (congrArg (_ * ·) ?_)
        exact ((valR_mul h _ q1 _ _).trans (congrArg (_ * ·) (valR_res h _ q1 _))).symm)
  refine ⟨σ, fun i => ⟨fun j j' => eq_of_valF_generic ξ hξ fun h => ?_, ?_⟩, fun K _ _ x hx => ?_⟩
  · obtain ⟨a, rfl⟩ : ∃ a, j = fun _ => a := ⟨j 0, funext fun i => by rw [Subsingleton.elim i 0]⟩
    obtain ⟨a', rfl⟩ : ∃ a, j' = fun _ => a := ⟨j' 0, funext fun i => by rw [Subsingleton.elim i 0]⟩
    have q1 := le_preimage_mono ξ inf_le_left h
    have q2 := le_inf' (le_preimage_mono ξ inf_le_left q1) (le_preimage_mono ξ inf_le_right h)
    refine (valR_res ξ _ h _).trans (Eq.trans ?_ ((valR_mul ξ _ h _ _).trans
      (congrArg₂ (· * ·) (valR_res ξ _ h _) (valR_res ξ _ h _))).symm)
    refine ((hσ i _ F ξ q1).unique hS.ne hβ (hid q1) ((hσ i _ F ξ q2).chart (hid q2) (hid q1))).trans
      (congrArg (· * _) ?_)
    exact (val_linComb_g (I := Fin 1) Q.L.L (𝟙 _) _ a a' ξ (hid q1) (hid q2)).symm
  · intro K _ β' g r jP jL k1 k2 k3 k4 k5
    exact hσ i (fun _ => jL) K _ (le_inf' ((top_le_preimage_iff _ _).2 k5)
      (le_wchart _ _ _ fun _ => (top_le_preimage_iff _ _).2 k4)) β' g r jP rfl k1 k2 ((top_le_preimage_iff _ _).2 k3)
  · obtain ⟨W', ⟨-, hz, hle⟩, O, τ, hO, hτ, hu, hind⟩ := hloc _ (hx ⟨IsLocalRing.closedPoint K, rfl⟩)
    have hx' : ⊤ ≤ x ⁻¹ᵁ W' := (le_preimage_iff x _).2 hz
    have hne : genericPoint Q.G.left ∈ Q.G.hom ⁻¹ᵁ W' := by
      change Q.G.hom _ ∈ W'
      rw [Q.hom_genericPoint]
      exact (genericPoint_specializes _).mem_open W'.isOpen hz
    have : Nonempty (Q.G.hom ⁻¹ᵁ W').toScheme := ⟨⟨_, hne⟩⟩
    have : IsIntegral (Q.G.hom ⁻¹ᵁ W').toScheme := isIntegral_of_isOpenImmersion (Q.G.hom ⁻¹ᵁ W').ι
    obtain ⟨ξ, rfl⟩ : ∃ h : Sp F ⟶ (Q.G.hom ⁻¹ᵁ W').toScheme, h ≫ (Q.G.hom ⁻¹ᵁ W').ι = ξ :=
      ⟨IsOpenImmersion.lift _ ξ (by
        rintro _ ⟨w, rfl⟩
        exact ⟨⟨_, hne⟩, (hξ w).symm⟩), IsOpenImmersion.lift_fac _ _ _⟩
    have hξ' : ∀ w, ξ w = genericPoint _ := fun w => (Q.G.hom ⁻¹ᵁ W').ι.isOpenEmbedding.injective
      ((hξ w).trans (genericPoint_eq_of_isOpenImmersion _).symm)
    have hrel : ∀ (a : Q.L.L.ι) (k : O.ι) (h : Sp K ⟶ (Q.G.hom ⁻¹ᵁ W').toScheme),
        ⊤ ≤ (h ≫ (Q.G.hom ⁻¹ᵁ W').ι) ⁻¹ᵁ Q.L.L.U a → ⊤ ≤ h ⁻¹ᵁ O.U k → ∃ v : K, v ≠ 0 ∧ ∀ i,
          valF (h ≫ (Q.G.hom ⁻¹ᵁ W').ι) _ (σ i fun _ => a) = v * valF h _ ((τ i).f k) := fun a k h q1 q2 => by
      obtain ⟨u, hu⟩ := hu a k
      have q := le_inf' (le_wchart Q.L.L _ (fun _ : Fin 1 => a) fun _ => q1) q2
      have hl : LB.wchart Q.L.L (fun _ : Fin 1 => (Q.G.hom ⁻¹ᵁ W').ι) (fun _ => a) ⊓ O.U k ≤ (Q.G.hom ⁻¹ᵁ W').ι ⁻¹ᵁ
          (Q.G.hom ⁻¹ᵁ W ⊓ LB.wchart Q.L.L (fun _ : Fin 1 => 𝟙 Q.G.left) fun _ => a) := fun y hy =>
        ⟨hle y.2, Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hy.1 0⟩
      refine ⟨_, val_unit_ne h q u, fun i => ?_⟩
      have e : ((Q.G.hom ⁻¹ᵁ W').ι.appLE _ _ hl).hom (σ i fun _ => a) = u.val * resG _ inf_le_right ((τ i).f k) :=
        eq_of_valF_generic ξ hξ' fun q => by
          have q' := le_preimage_comp ξ _ hl q
          refine (valR_appLE ξ _ hl q _).trans (Eq.trans ?_
            ((valR_mul ξ _ q _ _).trans (congrArg (_ * ·) (valR_res ξ _ q _))).symm)
          exact (hσ i _ F _ q').unique hS.ne hβ (hid q')
            ((hu F β ξ hβ (hid q') (le_preimage_mono ξ inf_le_right q)).2 i)
      exact (valR_appLE h _ hl q _).symm.trans ((congrArg (valR h _) e).trans
        ((valR_mul h _ q _ _).trans (congrArg (_ * ·) (valR_res h _ q _))))
    refine ⟨fun g hg => ?_, fun c hc => hind K x ((top_le_preimage_iff _ _).1 hx') c fun g k hg => ?_⟩
    · subst hg
      obtain ⟨h, rfl⟩ : ∃ h : Sp K ⟶ (Q.G.hom ⁻¹ᵁ W').toScheme, h ≫ (Q.G.hom ⁻¹ᵁ W').ι = g :=
        ⟨IsOpenImmersion.lift _ g (by
          rintro _ ⟨w, rfl⟩
          exact ⟨⟨_, hx' (x := w) trivial⟩, rfl⟩), IsOpenImmersion.lift_fac _ _ _⟩
      obtain ⟨a, ha⟩ := exists_le_preimage_of_iSup_eq_top (h ≫ (Q.G.hom ⁻¹ᵁ W').ι) Q.L.isLB.cover
      obtain ⟨k, hk⟩ := exists_le_preimage_of_iSup_eq_top h hO.cover
      obtain ⟨v, hv, H⟩ := hrel a k h ha hk
      obtain ⟨i, hi⟩ := exists_ne hτ h hk
      exact ⟨i, fun _ => a, (H i).trans_ne (mul_ne_zero hv hi)⟩
    · by_cases hk : ⊤ ≤ g ⁻¹ᵁ O.U k
      · obtain ⟨a, ha⟩ := exists_le_preimage_of_iSup_eq_top (g ≫ (Q.G.hom ⁻¹ᵁ W').ι) Q.L.isLB.cover
        obtain ⟨v, hv, H⟩ := hrel a k g ha hk
        refine mul_left_cancel₀ hv ((Finset.mul_sum _ _ _).trans (Eq.trans (Finset.sum_congr rfl fun i _ => ?_)
          ((hc _ (fun _ => a) hg).trans (mul_zero v).symm)))
        exact (mul_left_comm _ _ _).trans (congrArg (c i * ·) (H i).symm)
      · exact Finset.sum_eq_zero fun i _ => by rw [val_junk g hk, mul_zero]

end GlobalTheory.ZH.PowSec
