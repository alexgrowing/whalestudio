import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ThetaGenRank
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ThetaGenVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.GsScalJFK

set_option autoImplicit false
set_option linter.overlappingInstances false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.DVR.TG

open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out IsLocalRing

variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]

lemma isUnit_toW_of_K {Y : Scheme.{0}} (q : Y ⟶ Spec (CommRingCat.of (FractionRing R))) (W : Y.Opens) {r : R}
    (hr : r ≠ 0) : IsUnit (toW (q ≫ jK R) W r) := by
  have e1 : toW (q ≫ jK R) W r = (q.appLE ⊤ W le_top).hom
      ((Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv.hom (algebraMap R (FractionRing R) r)) := by
    rw [toW, RingHom.comp_apply]
    rw [← Scheme.Hom.appLE_comp_appLE (f := q) (g := jK R) ⊤ ⊤ W le_top le_top]
    rw [CommRingCat.comp_apply]
    congr 1
    have := congrArg (fun φ => φ.hom r) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap R (FractionRing R))))
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at this
    erw [Scheme.Hom.appLE_eq_app]
    exact this.symm
  rw [e1]
  exact ((isUnit_iff_ne_zero.2 ((map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 hr)).map _).map _

lemma base_eq_of_isDominant {X Y Z W : Scheme.{0}} {f g : X ⟶ Y} (s : Y ⟶ Z) [IsSeparated s]
    (h : f ≫ s = g ≫ s) (i0 : W ⟶ X) [IsDominant i0] (hU : i0 ≫ f = i0 ≫ g) (x : X) : f.base x = g.base x := by
  let X' : Over Z := Over.mk (f ≫ s)
  let Y' : Over Z := Over.mk s
  let U' : Over Z := Over.mk (i0 ≫ f ≫ s)
  let f' : X' ⟶ Y' := Over.homMk f
  let g' : X' ⟶ Y' := Over.homMk g
  let i0' : U' ⟶ X' := Over.homMk i0
  have : IsSeparated Y'.hom := ‹_›
  have : IsDominant (equalizer.ι f' g').left := by
    apply +allowSynthFailures IsDominant.of_comp (equalizer.lift i0' ?_).left
    · rwa [← Over.comp_left, equalizer.lift_ι]
    · ext1; exact hU
  have : Surjective (equalizer.ι f' g').left :=
    surjective_of_isDominant_of_isClosed_range _ (Scheme.Hom.isClosedEmbedding _).isClosed_range
  obtain ⟨z, rfl⟩ := (equalizer.ι f' g').left.surjective x
  have e := congr($(equalizer.condition f' g').left)
  rw [Over.comp_left, Over.comp_left] at e
  rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply]
  exact congrArg (fun φ => φ.base z) e

section PrB

variable (D) in
lemma prB_std : IsSchemeTheoreticallyDominant (DegPre.prB D.toPre (FractionRing R)).left ∧
    QuasiCompact (DegPre.prB D.toPre (FractionRing R)).left := by
  have := flat_B (D := D)
  have := isDominant_jF R
  have : IsSchemeTheoreticallyDominant (jF R) := IsSchemeTheoreticallyDominant.of_isDominant _
  have : IsIso (jFK (R := R) (FractionRing R)) := by
    have : IsIso (CommRingCat.ofHom (algebraMap (FractionRing R) (FractionRing R))) := by
      rw [Algebra.algebraMap_self]
      exact inferInstanceAs (IsIso (𝟙 (CommRingCat.of (FractionRing R))))
    infer_instance
  have : IsSchemeTheoreticallyDominant (TF (R := R) (FractionRing R)).hom :=
    inferInstanceAs (IsSchemeTheoreticallyDominant (jFK (R := R) (FractionRing R) ≫ jF R))
  have : QuasiCompact (TF (R := R) (FractionRing R)).hom :=
    inferInstanceAs (QuasiCompact (jFK (R := R) (FractionRing R) ≫ jF R))
  exact ⟨inferInstanceAs (IsSchemeTheoreticallyDominant (pullback.snd _ _)),
    inferInstanceAs (QuasiCompact (pullback.snd _ _))⟩

end PrB

lemma toW_of_K {Y : Scheme.{0}} (q : Y ⟶ Spec (CommRingCat.of (FractionRing R))) (W : Y.Opens) (r : R) :
    toW (q ≫ jK R) W r = (q.appLE ⊤ W le_top).hom
      ((Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv.hom (algebraMap R (FractionRing R) r)) := by
  rw [toW, RingHom.comp_apply]
  rw [← Scheme.Hom.appLE_comp_appLE (f := q) (g := jK R) ⊤ ⊤ W le_top le_top]
  rw [CommRingCat.comp_apply]
  congr 1
  have := congrArg (fun φ => φ.hom r) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap R (FractionRing R))))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at this
  erw [Scheme.Hom.appLE_eq_app]
  exact this.symm

lemma hBF : (DegPre.BF D.toPre (FractionRing R)).hom =
    (pullback.fst _ _ ≫ jFK (R := R) (FractionRing R)) ≫ jK R := by
  simp [DegPre.BF, TF]

lemma constBF_alg (a : R) (W : (DegPre.BF D.toPre (FractionRing R)).left.Opens) :
    DegPre.constBF D.toPre (FractionRing R) (algebraMap R (FractionRing R) a) W =
      toW (DegPre.BF D.toPre (FractionRing R)).hom W a := by
  rw [toW_congr hBF, toW_of_K]
  rw [← Scheme.Hom.appLE_comp_appLE (f := pullback.fst _ _) (g := jFK (R := R) (FractionRing R)) ⊤ ⊤ W le_top le_top]
  rw [CommRingCat.comp_apply]
  have := congrArg (fun φ => φ.hom (algebraMap R (FractionRing R) a))
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap (FractionRing R) (FractionRing R))))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom, Algebra.algebraMap_self,
    RingHom.id_apply] at this
  erw [Scheme.Hom.appLE_eq_app, ← this]
  rfl

set_option maxHeartbeats 1000000 in

theorem terms_vanish [IsDiscreteValuationRing R] {ϖ : R} (hϖ : Irreducible ϖ) (hI : I = maximalIdeal R)
    (F : Fam D.toPre (FractionRing R) 1) (g : ∀ α, D.toPre.SecB 1 α)
    (hgF : ∀ α, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre (FractionRing R) α) (DegPre.famε 1) (F.s α)
      (D.toPre.famφB α) (DegPre.famε 1) (g α) (DegPre.prB D.toPre (FractionRing R)).left 1) :
    ∀ mu, mu ≠ 0 → ∀ j, (pullback.fst D.toPre.P.A.hom (thick R I 0)).app _ ((g mu).f j) = 0 := by
  subst hI
  classical
  choose Q hQ using fun χ => QForm.exists_QVal hϖ D χ
  have hQ' : QForm.IsQ D.toPre ϖ Q := hQ
  have hv := valOver_vK hϖ
  obtain ⟨hstd, hqc⟩ := prB_std D
  have hs0 : VGe D (FractionRing R) (vK hϖ) 1 0 (F.s 0) 0 := by
    refine ⟨1, fun _ => 1, fun _ => g 0, fun _ => F.s 0, fun _ => hgF 0, fun _ => by simp, fun j => ?_⟩
    rw [Fin.sum_univ_one, ← map_one (algebraMap R (FractionRing R)), constBF_alg, map_one, _root_.one_mul]
  intro mu hmu
  have hm := SectionScalarValuation.fe_move hϖ hQ' hv 1 mu 0 F hs0
  have e01 : (0 : D.toPre.X) + 1 • mu = mu := by simp
  rw [e01] at hm
  have hb0 : QForm.bOf D.toPre Q mu 0 = 0 := by
    simp [QForm.bOf, QForm.Q_zero hϖ D hQ']
  have hq1 : 1 ≤ Q mu := QForm.Q_pos hϖ D hQ' hmu
  obtain ⟨N, a, σ, σF, hσF, hva, hsum⟩ := hm
  have hab : ∀ i, ∃ b : R, a i = algebraMap R (FractionRing R) (ϖ * b) := by
    intro i
    by_cases ha : a i = 0
    · exact ⟨0, by rw [ha, mul_zero, map_zero]⟩
    obtain ⟨n, hn⟩ := hasVal_of_ne_zero hϖ ha
    have h1 := hva i
    have hvn := hv _ _ hn
    rw [Algebra.algebraMap_self, RingHom.id_apply] at hvn
    rw [hvn, hb0] at h1
    have hn1 : 1 ≤ n := by
      have : ((0 : ℚ) + ((1 * Q mu + 0 : ℤ) : ℚ)) ≤ (n : ℚ) := by exact_mod_cast h1
      rw [zero_add] at this
      have : (1 : ℚ) ≤ n := le_trans (by exact_mod_cast (by omega : (1 : ℤ) ≤ 1 * Q mu + 0)) this
      exact_mod_cast this
    obtain ⟨u, hu⟩ := hn
    obtain ⟨d, hd⟩ : ∃ d : ℕ, n = d + 1 := ⟨(n - 1).toNat, by omega⟩
    refine ⟨ϖ ^ d * u, ?_⟩
    rw [hu, hd, zpow_add₀ (by exact (map_ne_zero_iff _ (IsFractionRing.injective R _)).2 hϖ.ne_zero),
      zpow_natCast, zpow_one]
    simp only [map_mul, map_pow]
    ring
  choose b hb using hab
  have := flat_B (D := D)
  have hdom : IsDominant (DegPre.prB D.toPre (FractionRing R)).left := inferInstance
  have key : ∀ j₂ : Fin 4 → D.toPre.P.L.ι,
      (∀ k k', (DegPre.prB D.toPre (FractionRing R)).left ≫ D.toPre.famφB mu k =
        (DegPre.prB D.toPre (FractionRing R)).left ≫ D.toPre.famφB mu k' → j₂ k = j₂ k') →
      (g mu).f j₂ = toW D.toPre.P.A.hom _ ϖ *
        ∑ i, toW D.toPre.P.A.hom _ (b i) * (σ i).f j₂ := by
    intro j₂ hcoh
    have hc : LB.Coh D.toPre.P.L (Sum.elim (DegPre.famφ D.toPre (FractionRing R) mu)
        (fun k => (DegPre.prB D.toPre (FractionRing R)).left ≫ D.toPre.famφB mu k)) (Sum.elim j₂ j₂) := by
      intro x y hxy
      rcases x with k | k <;> rcases y with k' | k' <;>
        simp only [Sum.elim_inl, Sum.elim_inr, GC.famφ_eq] at hxy ⊢ <;> exact hcoh k k' hxy
    have E1 := hgF mu j₂ j₂ hc
    have E2 := hsum j₂
    have E3 := fun i => hσF i j₂ j₂ hc
    have hle : (DegPre.prB D.toPre (FractionRing R)).left ⁻¹ᵁ LB.wchart D.toPre.P.L (D.toPre.famφB mu) j₂ ≤
        LB.wchart D.toPre.P.L (DegPre.famφ D.toPre (FractionRing R) mu) j₂ ⊓
          LB.wchart D.toPre.P.L (fun k => (DegPre.prB D.toPre (FractionRing R)).left ≫ D.toPre.famφB mu k) j₂ := by
      intro x hx
      refine ⟨Set.mem_iInter.2 fun k => ?_, Set.mem_iInter.2 fun k => ?_⟩
      · rw [GC.famφ_eq]; exact Set.mem_iInter.1 hx k
      · exact Set.mem_iInter.1 hx k
    apply Scheme.Hom.app_injective (DegPre.prB D.toPre (FractionRing R)).left
    apply map_inj_of_le_ge (inf_le_right.trans (wchart_comp_le _ _ j₂)) hle
    refine E1.trans ?_
    have hw : (DegPre.prB D.toPre (FractionRing R)).left ≫ D.toPre.P.A.hom = (DegPre.BF D.toPre (FractionRing R)).hom :=
      Over.w _
    rw [show resTop _ (1 : Γ((DegPre.BF D.toPre (FractionRing R)).left, ⊤)) = 1 from map_one _, _root_.one_mul, E2]
    simp only [map_sum, map_mul, app_toW, toW_congr hw]
    erw [map_sum, map_mul, map_sum]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have E3i := E3 i
    rw [show resTop _ (1 : Γ((DegPre.BF D.toPre (FractionRing R)).left, ⊤)) = 1 from map_one _, _root_.one_mul] at E3i
    erw [map_mul, map_mul, ← E3i, hb i, constBF_alg, toW_res, toW_res, toW_res, map_mul]
    rw [_root_.mul_assoc]
    rfl
  intro (j : Fin 4 → D.toPre.P.L.ι)
  set π := pullback.fst D.toPre.P.A.hom (thick R (maximalIdeal R) 0)
  refine TopCat.Presheaf.section_ext (pullback D.toPre.P.A.hom (thick R (maximalIdeal R) 0)).sheaf _ _ 0
    fun z hz => ?_
  choose ch hch using WeightPf.exists_chart D.toPre.P.L D.toPre.P.isLB
  let j₂ : Fin 4 → D.toPre.P.L.ι := fun k => ch ((D.toPre.famφB mu k).base (π.base z))
  have hcoh : ∀ k k', (DegPre.prB D.toPre (FractionRing R)).left ≫ D.toPre.famφB mu k =
      (DegPre.prB D.toPre (FractionRing R)).left ≫ D.toPre.famφB mu k' → j₂ k = j₂ k' := fun k k' h =>
    congrArg ch (base_eq_of_isDominant D.toPre.P.A.hom
      ((GC.famφB_over mu k).trans (GC.famφB_over mu k').symm) _ h (π.base z))
  have hK := key j₂ hcoh
  have hV : LB.wchart D.toPre.P.L (D.toPre.famφB mu) j ⊓ LB.wchart D.toPre.P.L (D.toPre.famφB mu) j₂ ≤
      LB.wchart D.toPre.P.L (D.toPre.famφB mu) j := inf_le_left
  have hzV : z ∈ π ⁻¹ᵁ (LB.wchart D.toPre.P.L (D.toPre.famφB mu) j ⊓ LB.wchart D.toPre.P.L (D.toPre.famφB mu) j₂) :=
    ⟨hz, Set.mem_iInter.2 fun k => hch _⟩
  have hres : (π.app _) ((D.toPre.P.A.left.presheaf.map (homOfLE hV).op).hom ((g mu).f j)) = 0 := by
    have c := (g mu).compat j j₂
    have hm : ϖ ∈ maximalIdeal R ^ (0 + 1) := by
      rw [zero_add, pow_one]; exact hϖ.not_isUnit
    have h2 : (π.app (LB.wchart D.toPre.P.L (D.toPre.famφB mu) j ⊓ LB.wchart D.toPre.P.L (D.toPre.famφB mu) j₂))
        ((D.toPre.P.A.left.presheaf.map (homOfLE (inf_le_right : LB.wchart D.toPre.P.L (D.toPre.famφB mu) j ⊓
          LB.wchart D.toPre.P.L (D.toPre.famφB mu) j₂ ≤ LB.wchart D.toPre.P.L (D.toPre.famφB mu) j₂)).op).hom
          ((g mu).f j₂)) = 0 := by
      rw [hK]
      erw [map_mul, toW_res, map_mul, app_toW_of_mem D.toPre.P.A.hom _ _ hm, zero_mul]
    erw [c, map_mul, h2]
    rw [mul_zero]
  have hz2 : π ⁻¹ᵁ (LB.wchart D.toPre.P.L (D.toPre.famφB mu) j ⊓ LB.wchart D.toPre.P.L (D.toPre.famφB mu) j₂) ≤
      π ⁻¹ᵁ LB.wchart D.toPre.P.L (D.toPre.famφB mu) j := π.preimage_mono hV
  show (pullback D.toPre.P.A.hom (thick R (maximalIdeal R) 0)).presheaf.germ _ z hz _ =
    (pullback D.toPre.P.A.hom (thick R (maximalIdeal R) 0)).presheaf.germ _ z hz 0
  erw [← TopCat.Presheaf.germ_res_apply _ (homOfLE hz2) z hzV, app_res π hV, hres, map_zero, map_zero]

end ReciprocityTheory.ChartRestriction.G.DVR.TG
