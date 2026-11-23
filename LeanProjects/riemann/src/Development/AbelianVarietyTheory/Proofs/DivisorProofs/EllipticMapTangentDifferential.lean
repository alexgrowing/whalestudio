import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueDetGen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnimodularSolCoords
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HolomorphicHomDetermined
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsUniqueLinearLiftOfHolomorphicAbelianVariet
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticePreservingMapGivesEndomorphism
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.HolPairB
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (upIdele IsLatOf)
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
open GlobalTheory.CMTorsion
open GlobalTheory.WeierstrassCurve (scheme toSpec mapHom)

open Filter Topology Polynomial

namespace GlobalTheory.CMTorsion.HolPt

theorem isHolTo_congr {B : Set ℂ} {Y : Scheme.{0}} {a a' : ℂ → (Sp ℂ ⟶ Y)} (h : IsHolTo B a)
    (he : ∀ b ∈ B, a' b = a b) : IsHolTo B a' := by
  intro U f
  have hs : {b ∈ B | ⊤ ≤ a' b ⁻¹ᵁ U} = {b ∈ B | ⊤ ≤ a b ⁻¹ᵁ U} := by
    ext b
    exact and_congr_right fun hb => by rw [he b hb]
  rw [hs]
  exact ⟨(h U f).1, (h U f).2.congr fun b hb => by rw [he b hb.1]⟩

theorem valAt'_spMap {A : Type} [CommRing A] (ψ : A →+* ℂ) (a : A) :
    valAt' (spMap ψ) ⊤ ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a) = ψ a := by
  have := ReciprocityTheory.ChartRestriction.G.PullbackSections.valAt'_specMap (CommRingCat.ofHom ψ) (𝟙 _) a
  rw [Category.id_comp] at this
  refine this.trans ((ReciprocityTheory.ChartRestriction.G.TB.ValAt.valAt'_of _ _ le_top _).trans ?_)
  simp [valAt, Scheme.Hom.appLE]

theorem isHolTo_spMap {R : Type} [CommRing R] {B : Set ℂ} (hB : IsOpen B) {Ψ : ℂ → (R →+* ℂ)}
    (h : ∀ a, DifferentiableOn ℂ (fun b => Ψ b a) B) : IsHolTo B fun b => spMap (Ψ b) :=
  ReciprocityTheory.ChartRestriction.G.PullbackSections.isHolTo_of_affine hB fun r => by
    obtain ⟨a, rfl⟩ := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).inv).2 r
    exact (h a).congr fun b _ => valAt'_spMap (Ψ b) a

theorem differentiableOn_eval₂ {B : Set ℂ} {a b : ℂ → ℂ} (ha : DifferentiableOn ℂ a B)
    (hb : DifferentiableOn ℂ b B) (p : ℂ[X][X]) :
    DifferentiableOn ℂ (fun t => p.eval₂ (eval₂RingHom (RingHom.id ℂ) (a t)) (b t)) B := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [eval₂_add]
    exact hp.add hq
  | monomial n c =>
    simp only [eval₂_monomial, coe_eval₂RingHom]
    exact (c.differentiable.comp_differentiableOn ha).mul (hb.pow n)

theorem differentiableOn_adjoinRoot {q : ℂ[X][X]} {B : Set ℂ} {a b : ℂ → ℂ} (ha : DifferentiableOn ℂ a B)
    (hb : DifferentiableOn ℂ b B) (Ψ : ℂ → (AdjoinRoot q →+* ℂ))
    (hΨ : ∀ t ∈ B, ∀ p, Ψ t (AdjoinRoot.mk q p) = p.eval₂ (eval₂RingHom (RingHom.id ℂ) (a t)) (b t))
    (r : AdjoinRoot q) : DifferentiableOn ℂ (fun t => Ψ t r) B := by
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective r
  exact (differentiableOn_eval₂ ha hb p).congr fun t ht => hΨ t ht p

theorem affine_equation (Λ : PeriodPair) (Ω : ℂ) (hΩ : Ω ≠ 0) (t : ℂ) (ht : t ∉ Λ.lattice) :
    ((curve Λ Ω).map (RingHom.id ℂ)).toAffine.Equation (Λ.weierstrassP t / Ω ^ 2)
      (Λ.derivWeierstrassP t / (2 * Ω ^ 3)) := by
  rw [WeierstrassCurve.map_id, WeierstrassCurve.Affine.equation_iff]
  have h := Λ.derivWeierstrassP_sq t ht
  simp only [curve]
  field_simp
  linear_combination 4 * h

end GlobalTheory.CMTorsion.HolPt

namespace GlobalTheory.CMTorsion.HolPt

open GlobalTheory.WeierstrassCurve in

theorem pt_eq_chartZ (Λ : PeriodPair) (Ω : ℂ) (hΩ : Ω ≠ 0) (t : ℂ) (ht : t ∉ Λ.lattice) :
    pt Λ Ω t = spMap (affineEval (curve Λ Ω) (RingHom.id ℂ) (Λ.weierstrassP t / Ω ^ 2)
      (Λ.derivWeierstrassP t / (2 * Ω ^ 3)) (affine_equation Λ Ω hΩ t ht)) ≫ chartZ (curve Λ Ω) := by
  rw [SpecMap_affineEval_chartZ]
  exact ptHom_congr _ _ _ _ rfl (by simp [coords, ht]) _

open GlobalTheory.WeierstrassCurve in

theorem isHolTo_off (Λ : PeriodPair) (Ω : ℂ) (hΩ : Ω ≠ 0) :
    IsHolTo ((Λ.lattice : Set ℂ)ᶜ) (pt Λ Ω) := by
  classical
  have hB : IsOpen ((Λ.lattice : Set ℂ)ᶜ) := Λ.isClosed_lattice.isOpen_compl
  have h2 : Λ.ω₁ / 2 ∉ Λ.lattice := Λ.ω₁_div_two_notMem_lattice
  let Ψ : ℂ → ((curve Λ Ω).toAffine.CoordinateRing →+* ℂ) := fun t =>
    if h : t ∉ Λ.lattice then affineEval (curve Λ Ω) (RingHom.id ℂ) (Λ.weierstrassP t / Ω ^ 2)
      (Λ.derivWeierstrassP t / (2 * Ω ^ 3)) (affine_equation Λ Ω hΩ t h)
    else affineEval (curve Λ Ω) (RingHom.id ℂ) (Λ.weierstrassP (Λ.ω₁ / 2) / Ω ^ 2)
      (Λ.derivWeierstrassP (Λ.ω₁ / 2) / (2 * Ω ^ 3)) (affine_equation Λ Ω hΩ _ h2)
  have hP : DifferentiableOn ℂ (fun t => Λ.weierstrassP t / Ω ^ 2) ((Λ.lattice : Set ℂ)ᶜ) :=
    fun t ht => ((Λ.analyticOnNhd_weierstrassP t ht).differentiableAt.div_const _).differentiableWithinAt
  have hP' : DifferentiableOn ℂ (fun t => Λ.derivWeierstrassP t / (2 * Ω ^ 3)) ((Λ.lattice : Set ℂ)ᶜ) :=
    fun t ht => ((Λ.analyticOnNhd_derivWeierstrassP t ht).differentiableAt.div_const _).differentiableWithinAt
  have hΨ : ∀ r, DifferentiableOn ℂ (fun t => Ψ t r) ((Λ.lattice : Set ℂ)ᶜ) :=
    differentiableOn_adjoinRoot hP hP' Ψ fun t ht p => by
      simp only [Ψ, dif_pos (show t ∉ Λ.lattice from ht), affineEval, AdjoinRoot.lift_mk]
  refine isHolTo_congr (ReciprocityTheory.ChartRestriction.G.PullbackSections.isHolTo_comp (isHolTo_spMap hB hΨ) (chartZ (curve Λ Ω)))
    fun t ht => ?_
  simp only [Ψ, dif_pos (show t ∉ Λ.lattice from ht)]
  exact pt_eq_chartZ Λ Ω hΩ t ht

end GlobalTheory.CMTorsion.HolPt

namespace GlobalTheory.CMTorsion.HolPt

open GlobalTheory.WeierstrassCurve in

theorem exists_isHolTo_near (Λ : PeriodPair) (Ω : ℂ) (hΩ : Ω ≠ 0) (l : ℂ) (hl : l ∈ Λ.lattice) :
    ∃ N : Set ℂ, IsOpen N ∧ l ∈ N ∧ IsHolTo N (pt Λ Ω) := by
  classical
  set A : ℂ → ℂ := fun t => Λ.weierstrassPExcept l t - 1 / l ^ 2 with hA
  set B : ℂ → ℂ := Λ.derivWeierstrassPExcept l with hB
  have hAa : AnalyticAt ℂ A l := (Λ.analyticAt_weierstrassPExcept l).sub analyticAt_const
  have hBa : AnalyticAt ℂ B l := Λ.analyticAt_derivWeierstrassPExcept l
  set D : ℂ → ℂ := fun t => -2 + B t * (t - l) ^ 3 with hD
  have hDc : ContinuousAt D l :=
    continuousAt_const.add (hBa.continuousAt.mul ((continuousAt_id.sub continuousAt_const).pow 3))
  have hD0 : D l ≠ 0 := by simp [hD]
  have hev : ∀ᶠ t in 𝓝 l, t ∉ (Λ.lattice : Set ℂ) \ {l} ∧ AnalyticAt ℂ A t ∧ AnalyticAt ℂ B t ∧ D t ≠ 0 :=
    Filter.Eventually.and (p := fun t => t ∉ (Λ.lattice : Set ℂ) \ {l}) (Λ.compl_lattice_sdiff_singleton_mem_nhds l)
      (hAa.eventually_analyticAt.and (hBa.eventually_analyticAt.and (hDc.eventually_ne hD0)))
  obtain ⟨N, hN, hNo, hlN⟩ := eventually_nhds_iff.1 hev
  have hAd : DifferentiableOn ℂ A N := fun t ht => (hN t ht).2.1.differentiableAt.differentiableWithinAt
  have hBd : DifferentiableOn ℂ B N := fun t ht => (hN t ht).2.2.1.differentiableAt.differentiableWithinAt
  have hDne : ∀ t ∈ N, D t ≠ 0 := fun t ht => (hN t ht).2.2.2
  set Z : ℂ → ℂ := fun t => -2 * Ω * ((t - l) + A t * (t - l) ^ 3) / D t with hZ
  set V : ℂ → ℂ := fun t => -2 * Ω ^ 3 * (t - l) ^ 3 / D t with hV
  have hDd : DifferentiableOn ℂ D N := (differentiableOn_const _).add (hBd.mul ((differentiableOn_id.sub
    (differentiableOn_const _)).pow 3))
  have hZd : DifferentiableOn ℂ Z N := (((differentiableOn_const _).mul ((differentiableOn_id.sub
    (differentiableOn_const _)).add (hAd.mul ((differentiableOn_id.sub (differentiableOn_const _)).pow 3))))).div
    hDd hDne
  have hVd : DifferentiableOn ℂ V N :=
    ((differentiableOn_const _).mul ((differentiableOn_id.sub (differentiableOn_const _)).pow 3)).div hDd hDne
  have key : ∀ t ∈ N, ∃ c : ℂ, c ≠ 0 ∧ coords Λ Ω t = c • ![Z t, -1, V t] := by
    intro t ht
    by_cases htl : t = l
    · subst htl
      refine ⟨-1, by norm_num, ?_⟩
      ext i
      fin_cases i <;> simp [coords, hl, hZ, hV]
    · have ht' : t ∉ Λ.lattice := fun h => (hN t ht).1 ⟨h, htl⟩
      have hs : t - l ≠ 0 := sub_ne_zero.2 htl
      have e1 := Λ.weierstrassPExcept_def ⟨l, hl⟩ t
      have e2 := Λ.derivWeierstrassPExcept_def ⟨l, hl⟩ t
      simp only at e1 e2
      have hAt : A t = Λ.weierstrassP t - 1 / (t - l) ^ 2 := by simp only [hA, e1]; ring
      have hBt : B t = Λ.derivWeierstrassP t + 2 / (t - l) ^ 3 := by simp only [hB, e2]
      have hDt : D t = Λ.derivWeierstrassP t * (t - l) ^ 3 := by
        simp only [hD, hBt]
        field_simp
        ring
      have hQ : Λ.derivWeierstrassP t ≠ 0 := by
        intro h0
        exact hDne t ht (by rw [hDt, h0, zero_mul])
      refine ⟨-(Λ.derivWeierstrassP t / (2 * Ω ^ 3)), by
        exact neg_ne_zero.2 (div_ne_zero hQ (by simp [hΩ])), ?_⟩
      ext i
      fin_cases i
      · simp only [coords, if_neg ht', hZ, hDt, hAt]
        simp
        field_simp
        ring
      · simp only [coords, if_neg ht']
        simp
      · simp only [coords, if_neg ht', hV, hDt]
        simp
        field_simp
  have heq : ∀ t ∈ N, ((curve Λ Ω).map (RingHom.id ℂ)).toProjective.Equation ![Z t, -1, V t] := by
    intro t ht
    obtain ⟨c, hc, h⟩ := key t ht
    have := (isUnimodularSol_coords Λ Ω t).equation
    rwa [h, WeierstrassCurve.Projective.equation_smul _ (IsUnit.mk0 c hc)] at this
  let Ψ : ℂ → (OriginRing (curve Λ Ω) →+* ℂ) := fun t =>
    if h : t ∈ N then originEval (curve Λ Ω) (RingHom.id ℂ) (Z t) (V t) (heq t h)
    else originEval (curve Λ Ω) (RingHom.id ℂ) (Z l) (V l) (heq l hlN)
  have hΨ : ∀ r, DifferentiableOn ℂ (fun t => Ψ t r) N :=
    differentiableOn_adjoinRoot hVd hZd Ψ fun t ht p => by
      simp only [Ψ, dif_pos ht, originEval, AdjoinRoot.lift_mk]
  refine ⟨N, hNo, hlN, isHolTo_congr (ReciprocityTheory.ChartRestriction.G.PullbackSections.isHolTo_comp (isHolTo_spMap hNo hΨ) (chartY (curve Λ Ω)))
    fun t ht => ?_⟩
  simp only [Ψ, dif_pos ht]
  rw [SpecMap_originEval_chartY]
  obtain ⟨c, hc, h⟩ := key t ht
  exact (ptHom_congr _ _ _ _ rfl h _).trans (ptHom_smul _ _ _ _ (IsUnit.mk0 c hc))

end GlobalTheory.CMTorsion.HolPt

namespace GlobalTheory.CMTorsion.HolPt

theorem isHolTo_pt (Λ : PeriodPair) (Ω : ℂ) (hΩ : Ω ≠ 0) : IsHolTo (Set.univ : Set ℂ) (pt Λ Ω) := by
  refine GlobalTheory.HolHom.isHolTo_of_holAt isOpen_univ fun z _ => ?_
  by_cases hz : z ∈ Λ.lattice
  · obtain ⟨N, -, hzN, hN⟩ := exists_isHolTo_near Λ Ω hΩ z hz
    exact GlobalTheory.HolHom.holAt_of_isHolTo hN hzN
  · exact GlobalTheory.HolHom.holAt_of_isHolTo (isHolTo_off Λ Ω hΩ) hz

end GlobalTheory.CMTorsion.HolPt

namespace GlobalTheory.CMTorsion

theorem exists_vector_of_additive_curve_hom : ∀ (F : Type) [Field F] [NumberField F] (𝔠 : FracId F) (X : Obj F 𝔠 (Sp ℂ)) (c : 𝔠.elt) (n : ℕ) (u : HolUnif X.A (X.diag c) n) (Λ : PeriodPair) (Ω : ℂ), Ω ≠ 0 → ∀ f : scheme (curve Λ Ω) ⟶ X.A.left, f ≫ X.A.hom = toSpec (curve Λ Ω) → ∀ e : ℂ → (𝟙_ (Over (Sp ℂ)) ⟶ X.A), (∀ z w, e (z + w) = e z * e w) → (∀ z, (e z).left = pt Λ Ω z ≫ f) → ∃ β₁ : Fin n → ℂ, ∀ z, pt Λ Ω z ≫ f = (u.ex (z • β₁)).left := by
  intro F _ _ 𝔠 X c n u Λ Ω hΩ f _ e he hef
  have hg := GlobalTheory.RealMult.Obj.holUnif_dim_eq X u
  subst hg
  obtain ⟨h₁, h₂⟩ := GlobalTheory.TorusTransfer.tangent_bijective u X.dim
  have hpt := HolPt.isHolTo_pt Λ Ω hΩ
  have hol : IsHolTo (Set.univ : Set (Fin 1 → ℂ)) (fun z => (e (z 0)).left) := by
    refine GlobalTheory.HolHom.isHolTo_of_holAt isOpen_univ fun z _ => ?_
    have h1 := ((GlobalTheory.HolHom.holAt_of_isHolTo hpt (Set.mem_univ (z 0))).comp f).precomp
      (k := fun z : Fin 1 → ℂ => z 0) (z := z) (by fun_prop)
    simpa only [hef] using h1
  obtain ⟨L, hL, -⟩ := GlobalTheory.existsUnique_linear_lift_of_isHolTo X.A X.ab (X.diag c) _ 1 u h₁ h₂
    (fun z => e (z 0)) (fun z w => he _ _) hol
  refine ⟨L (fun _ => 1), fun z => ?_⟩
  have hz : z • L (fun _ => 1) = L (fun _ => z) := by
    rw [← map_smul]
    congr 1
    funext
    simp
  rw [hz, hL, hef]

end GlobalTheory.CMTorsion
