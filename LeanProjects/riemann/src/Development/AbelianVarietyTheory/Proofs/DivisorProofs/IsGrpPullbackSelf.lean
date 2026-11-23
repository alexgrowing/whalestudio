import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
import Development.AbelianVarietyTheory.Definitions.Divisors.MinSt5OfMinSt4
import Development.AbelianVarietyTheory.Definitions.Divisors.IsChartMember
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommutatorPairingDeterminedAtGenericPoint
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsFiniteEtaleCoverConstantTorsion
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PushEquivSymmLeft
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsIffOfIsGrpPullbackComm
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaLevelAbelianSchemeGlueAffineCover
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TorsionSectionExtendsAbLocus
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpPullbackOfSameFibreWithSquareBundleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorsionSectionOfTorsionRationalOverFractioStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairingEqZpowOfFieldPointDomainStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.LevSpread

theorem eq_of_comp_eq {S : Scheme.{0}} (A : Over S) [GrpObj A] [IsCommMonObj A] (hA : IsAbelianScheme A) {n : ℕ}
    (hn : IsUnit (n : Γ(S, ⊤))) (Z : Over S) [PreconnectedSpace Z.left] (x y : Z ⟶ A) (hx : x ^ n = 1)
    (hy : y ^ n = 1) (T : Over S) (z : T ⟶ Z) [Nonempty T.left] (h : z ≫ x = z ≫ y) : x = y := by
  have hw : (x * y⁻¹) ^ n = 1 := by rw [mul_pow, inv_pow, hx, hy, inv_one, _root_.mul_one]
  obtain ⟨C, hC, hz⟩ := GlobalTheory.TorsionCover.exists_clopen_eq_one A hA hn (x * y⁻¹) hw
  have h1 : z ≫ (x * y⁻¹) = 1 := by
    show (preHom z) (x * y⁻¹) = 1
    rw [map_mul, map_inv]
    show (z ≫ x) * (z ≫ y)⁻¹ = 1
    rw [h, mul_inv_cancel]
  have hsub := (hz T z).1 h1
  obtain ⟨p⟩ := ‹Nonempty T.left›
  have hne : C.Nonempty := ⟨_, hsub ⟨p, rfl⟩⟩
  have huniv : C = Set.univ := hC.eq_univ hne
  have h2 : 𝟙 Z ≫ (x * y⁻¹) = 1 := (hz Z (𝟙 Z)).2 (by rw [huniv]; exact Set.subset_univ _)
  rw [Category.id_comp] at h2
  exact mul_inv_eq_one.1 h2

theorem isGrpPullback_self {S : Scheme.{0}} (G : Over S) [GrpObj G] : IsGrpPullback G G (𝟙 S) (𝟙 G.left) := by
  refine ⟨IsPullback.of_horiz_isIso ⟨by simp⟩, fun T x y x₀ y₀ hx hy => ?_⟩
  let ρ : Over.mk (T.hom ≫ 𝟙 S) ⟶ T := Over.homMk (𝟙 T.left) (by simp)
  have ex : x₀ = ρ ≫ x := Over.OverMorphism.ext (hx.trans ((Category.comp_id _).trans (Category.id_comp _).symm))
  have ey : y₀ = ρ ≫ y := Over.OverMorphism.ext (hy.trans ((Category.comp_id _).trans (Category.id_comp _).symm))
  rw [ex, ey, ← MonObj.comp_mul]
  exact (Category.id_comp _).trans (Category.comp_id _).symm

end GlobalTheory.LevSpread

namespace GlobalTheory.LevSpread

theorem l1 : ∀ (S T : Scheme.{0}) (A₀ : Over T) [GrpObj A₀] [IsCommMonObj A₀] (P₀ : LB (G2 A₀).left) (A : Over S) [GrpObj A] [IsCommMonObj A] (P : LB (G2 A).left) (f : T ⟶ S), P₀.IsLB → P.IsLB → SameFib A₀ P₀ (𝟙 _) A P f → ∃ (φ : A₀.left ⟶ A.left) (φ₂ : (G2 A₀).left ⟶ (G2 A).left), IsGrpPullback A₀ A f φ ∧ IsSquare φ φ₂ ∧ LBIso P₀ (P.pull φ₂) ∧ LBIso (P₀.pull (lift (𝟙 A₀) (𝟙 A₀)).left) ((P.pull (lift (𝟙 A) (𝟙 A)).left).pull φ) := GlobalTheory.T.grpPullback_of_sameFibreWithSquareBundle

theorem l2a : ∀ (R₀ : Type) [CommRing R₀] [IsDomain R₀] [IsNoetherianRing R₀] [IsIntegrallyClosed R₀] (A : Over (Sp R₀)) [GrpObj A] [IsCommMonObj A] (n : ℕ), IsAbelianScheme A → IsUnit (n : R₀) → TorsRat A n → ∀ (K : Type) [Field K] [IsAlgClosed K] (t : Sp K ⟶ Sp R₀) (x : Over.mk t ⟶ A), x ^ n = 1 → ∃ σ : 𝟙_ (Over (Sp R₀)) ⟶ A, σ ^ n = 1 ∧ toUnit (Over.mk t) ≫ σ = x := GlobalTheory.T.exists_torsionSection_of_torsionRationalOverFraction

theorem l2 : ∀ (R₀ : Type) [CommRing R₀] [IsDomain R₀] [IsNoetherianRing R₀] [IsIntegrallyClosed R₀] (A : Over (Sp R₀)) [GrpObj A] [IsCommMonObj A] (n : ℕ), IsAbelianScheme A → IsUnit (n : R₀) → TorsRat A n → ∀ (K : Type) [Field K] (t : Sp K ⟶ Sp R₀) (x : Over.mk t ⟶ A), x ^ n = 1 → ∃ σ : 𝟙_ (Over (Sp R₀)) ⟶ A, σ ^ n = 1 ∧ toUnit (Over.mk t) ≫ σ = x := by
  intro R₀ _ _ _ _ A _ _ n hA hnR hT K _ t x hx
  have hnΓ : IsUnit (n : Γ(Sp R₀, ⊤)) := by
    have := hnR.map (Scheme.ΓSpecIso (CommRingCat.of R₀)).inv.hom
    rwa [map_natCast] at this
  let t' : Sp (AlgebraicClosure K) ⟶ Sp R₀ := spMap (algebraMap K (AlgebraicClosure K)) ≫ t
  let z : Over.mk t' ⟶ Over.mk t := Over.homMk (spMap (algebraMap K (AlgebraicClosure K))) rfl
  obtain ⟨σ, hσ, hσx⟩ := l2a R₀ A n hA hnR hT (AlgebraicClosure K) t' (z ≫ x)
    (by rw [← MonObj.comp_pow, hx, MonObj.comp_one])
  refine ⟨σ, hσ, ?_⟩
  haveI : PreconnectedSpace (Over.mk t).left := inferInstanceAs (PreconnectedSpace (Sp K))
  haveI : Nonempty (Over.mk t').left := inferInstanceAs (Nonempty (Sp (AlgebraicClosure K)))
  refine eq_of_comp_eq A hA hnΓ (Over.mk t) _ x (by rw [← MonObj.comp_pow, hσ, MonObj.comp_one]) hx (Over.mk t') z ?_
  rw [← Category.assoc, show z ≫ toUnit (Over.mk t) = toUnit (Over.mk t') from toUnit_unique _ _, hσx]

theorem l3 : ∀ (O : Type) [CommRing O] [IsDomain O] (A : Over (Sp O)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (P : LB (G2 A).left), IsPPol A P → ∀ (N : ℕ), 0 < N → IsUnit (N : O) → ∀ (u v : 𝟙_ (Over (Sp O)) ⟶ A), u ^ N = 1 → v ^ N = 1 → ∀ (ζ : Oˣ), IsPrimitiveRoot ζ N → ∀ (m : ℤ) (K : Type) [Field K] (κ : O →+* K), Out.WeilIs A (P.pull (lift (𝟙 A) (𝟙 A)).left) N (toUnit (Over.mk (spMap κ)) ≫ u) (toUnit (Over.mk (spMap κ)) ≫ v) (unitOn (Units.map κ.toMonoidHom (ζ ^ m))) → ∀ (k : Type) [Field k] (ρ : O →+* k), Out.WeilIs A (P.pull (lift (𝟙 A) (𝟙 A)).left) N (toUnit (Over.mk (spMap ρ)) ≫ u) (toUnit (Over.mk (spMap ρ)) ≫ v) (unitOn (Units.map ρ.toMonoidHom (ζ ^ m))) := GlobalTheory.T.weilPairing_eq_zpow_of_fieldPoint_domain

theorem prim_map {n : ℕ} (hn : n ≠ 0) {R : Type} [CommRing R] [IsDomain R] (β : cycAway n →+* R) :
    IsPrimitiveRoot (β (zetaAway n)) n := by
  have h₁ : IsPrimitiveRoot (zetaAway n) n :=
    IsPrimitiveRoot.of_map_of_injective (f := (cycAway n).subtype) (Complex.isPrimitiveRoot_exp n hn) Subtype.val_injective
  have : NeZero (n : R) := ⟨by simpa using ((isUnit_natCast hn).map β).ne_zero⟩
  have h₂ := (h₁.isRoot_cyclotomic (Nat.pos_of_ne_zero hn)).map (f := β)
  rwa [Polynomial.map_cyclotomic, Polynomial.isRoot_cyclotomic_iff] at h₂

theorem level_spreads : ∀ (n : ℕ), 3 ≤ n → Odd n → ∀ (R₀ : Type) [CommRing R₀] [IsDomain R₀] [IsNoetherianRing R₀] [IsIntegrallyClosed R₀] (b : cycAway n →+* R₀) (A : Over (Sp R₀)) [GrpObj A] [IsCommMonObj A] (P : LB (G2 A).left), IsAbelianScheme A → IsPPol A P → TorsRat A n → ∀ (g : ℕ) (K : Type) [Field K] (κ : R₀ →+* K) (c₀ : SiegPre g n (zetaAway n) (spMap (κ.comp b))), c₀.Principal → SameFib c₀.A c₀.P (𝟙 _) A P (spMap κ) → ∃ c : SiegPre g n (zetaAway n) (spMap b), c.Principal ∧ SiegPB c₀ c (spMap κ) ∧ ∃ (a : c.A.left ⟶ A.left) (a₂ : (G2 c.A).left ⟶ (G2 A).left), IsGrpPullback c.A A (𝟙 _) a ∧ IsSquare a a₂ ∧ LBIso c.P (P.pull a₂) := by
  intro n hn3 hnodd R₀ _ _ _ _ b A _ _ P hA hP hT g K _ κ c₀ hc₀ hsf
  have hn0 : n ≠ 0 := by omega
  have hnR : IsUnit (n : R₀) := by simpa using (isUnit_natCast hn0).map b
  have hnΓ : IsUnit (n : Γ(Sp R₀, ⊤)) := by
    have := hnR.map (Scheme.ΓSpecIso (CommRingCat.of R₀)).inv.hom
    rwa [map_natCast] at this

  have hζc : IsPrimitiveRoot (zetaAway n) n :=
    IsPrimitiveRoot.of_map_of_injective (f := (cycAway n).subtype) (Complex.isPrimitiveRoot_exp n hn0) Subtype.val_injective
  let ζU : (cycAway n)ˣ := (hζc.isUnit hn0).unit
  have hζU : (ζU : cycAway n) = zetaAway n := rfl
  let ζR : R₀ˣ := Units.map b.toMonoidHom ζU
  have hζR : IsPrimitiveRoot ζR n := IsPrimitiveRoot.coe_units_iff.1 (prim_map hn0 b)

  obtain ⟨φ, φ₂, hφ, hsq, hiso, hdiag⟩ := l1 _ _ c₀.A c₀.P A P (spMap κ) c₀.isLB hP.1.1 hsf
  let E := GlobalTheory.ObjPull.pushEquiv hφ (𝟙_ (Over (Sp K)))
  have hxa : ∀ a, (E (c₀.lev a)) ^ n = 1 := fun a => by rw [← map_pow, c₀.lev_tors, map_one]
  choose σ hσn hσx using fun a => l2 R₀ A n hA hnR hT K _ (E (c₀.lev a)) (hxa a)
  have hcomp : ∀ a, (c₀.lev a).left ≫ φ = spMap κ ≫ (σ a).left := fun a => by
    have e := congrArg (fun w => w.left) (hσx a)
    simp only [Over.comp_left, GlobalTheory.ObjPull.toUnit_left'] at e
    rw [← GlobalTheory.ObjPull.pushEquiv_left hφ, ← e]
    exact congrArg (· ≫ (σ a).left) (Category.id_comp _)
  haveI : PreconnectedSpace (𝟙_ (Over (Sp R₀))).left := inferInstanceAs (PreconnectedSpace (Sp R₀))
  have inj : ∀ (T : Over (Sp R₀)) [Nonempty T.left] (s s' : 𝟙_ (Over (Sp R₀)) ⟶ A), s ^ n = 1 → s' ^ n = 1 →
      toUnit T ≫ s = toUnit T ≫ s' → s = s' := fun T _ s s' hs hs' h =>
    eq_of_comp_eq A hA hnΓ (𝟙_ _) s s' hs hs' T (toUnit T) h
  haveI : Nonempty (Over.mk ((𝟙_ (Over (Sp K))).hom ≫ spMap κ)).left := inferInstanceAs (Nonempty (Sp K))
  have hadd : ∀ a a', σ (a + a') = σ a * σ a' := fun a a' =>
    inj _ _ _ (hσn _) (by rw [mul_pow, hσn, hσn, _root_.mul_one])
      (by rw [MonObj.comp_mul, hσx, hσx, hσx, c₀.lev_add, map_mul])
  have one_iff : ∀ (T : Over (Sp R₀)) [Nonempty T.left] a, toUnit T ≫ σ a = 1 ↔ σ a = 1 := fun T _ a =>
    ⟨fun h => inj T (σ a) 1 (hσn a) (one_pow n) (h.trans (MonObj.comp_one _).symm),
      fun h => by rw [h, MonObj.comp_one]⟩
  let c : SiegPre g n (zetaAway n) (spMap b) :=
    { A := A
      ab := hA
      P := P
      isLB := hP.1.1
      rig₁ := hP.1.2.1
      rig₂ := hP.1.2.2.1
      symm := hP.1.2.2.2
      lev := σ
      lev_add := hadd
      lev_tors := hσn
      geom := ?_ }
  refine ⟨c, ⟨hP.2.1, hP.2.2⟩, ⟨φ, φ₂, hφ, hsq, hiso, hcomp⟩,
    ⟨𝟙 _, 𝟙 _, isGrpPullback_self A, ⟨(Category.id_comp _).trans (Category.comp_id _).symm,
      (Category.id_comp _).trans (Category.comp_id _).symm⟩, GlobalTheory.ThetaAffineGlue.lbIso_pull_id hP.1.1⟩⟩
  intro k _ _ x β z hxβ hz
  obtain ⟨ρ, rfl⟩ : ∃ ρ : R₀ →+* k, spMap ρ = x := ⟨(Spec.preimage x).hom, by simp [spMap]⟩
  have hβ : β = ρ.comp b := by
    have e : spMap (ρ.comp b) = spMap β := by rw [← hxβ]; exact Spec.map_comp _ _
    exact (congrArg CommRingCat.Hom.hom (Spec.map_injective e)).symm
  have hzU : z = Units.map ρ.toMonoidHom ζR := Units.ext (by rw [hz, hβ]; rfl)
  subst hzU
  let iK : K →+* AlgebraicClosure K := algebraMap K (AlgebraicClosure K)
  let x₀ : Sp (AlgebraicClosure K) ⟶ Sp K := spMap iK
  obtain ⟨g1, g2, g3⟩ := c₀.geom (AlgebraicClosure K) x₀ ((iK.comp κ).comp b)
    (Units.map ((iK.comp κ).comp b).toMonoidHom ζU) (by rw [← Spec.map_comp]; rfl) rfl
  let T₀ : Over (Sp R₀) := Over.mk ((Over.mk x₀).hom ≫ spMap κ)
  haveI : Nonempty T₀.left := inferInstanceAs (Nonempty (Sp (AlgebraicClosure K)))
  haveI : Nonempty (Over.mk (spMap ρ)).left := inferInstanceAs (Nonempty (Sp k))
  have push : ∀ a, GlobalTheory.ObjPull.pushEquiv hφ (Over.mk x₀) (toUnit _ ≫ c₀.lev a) = toUnit T₀ ≫ σ a := fun a => by
    apply Over.OverMorphism.ext
    rw [GlobalTheory.ObjPull.pushEquiv_left, Over.comp_left, Over.comp_left, Category.assoc, hcomp,
      GlobalTheory.ObjPull.toUnit_left', GlobalTheory.ObjPull.toUnit_left']
    exact (Category.assoc _ _ _).symm
  refine ⟨fun a => ?_, fun gg hg => ?_, fun a a' => ?_⟩
  · rw [one_iff, ← one_iff T₀, ← push, map_eq_one_iff _ (GlobalTheory.ObjPull.pushEquiv hφ _).injective]
    exact g1 a
  · obtain ⟨τ, hτn, hτ⟩ := l2 R₀ A n hA hnR hT k (spMap ρ) gg hg
    obtain ⟨a, ha⟩ := g2 ((GlobalTheory.ObjPull.pushEquiv hφ (Over.mk x₀)).symm (toUnit T₀ ≫ τ))
      (by rw [← map_pow, ← MonObj.comp_pow, hτn, MonObj.comp_one, map_one])
    refine ⟨a, ?_⟩
    have e : σ a = τ := inj T₀ _ _ (hσn a) hτn (by rw [← push, ha, MulEquiv.apply_symm_apply])
    rw [e, hτ]
  · have H' := (GlobalTheory.weilIs_iff_of_isGrpPullback_comm (Sp R₀) (Sp K) A c₀.A (spMap κ) φ
      (P.pull (lift (𝟙 A) (𝟙 A)).left) (c₀.P.pull (lift (𝟙 c₀.A) (𝟙 c₀.A)).left) (pull_isLB hP.1.1 _)
      (pull_isLB c₀.isLB _) hφ hdiag (Over.mk x₀) (n : ℤ) _ _ (toUnit T₀ ≫ σ a) (toUnit T₀ ≫ σ a') _
      (by rw [← push]; rfl) (by rw [← push]; rfl)).1 (g3 a a')
    have ht : (Over.mk x₀).hom ≫ spMap κ = spMap (iK.comp κ) := by
      show x₀ ≫ spMap κ = _
      rw [← Spec.map_comp]; rfl
    have hu : (Units.map ((iK.comp κ).comp b).toMonoidHom ζU) ^ (2 * omegaStd a a') =
        Units.map (iK.comp κ).toMonoidHom (ζR ^ (2 * omegaStd a a')) := by
      rw [map_zpow]; rfl
    rw [hu] at H'
    simp only [T₀] at H'
    rw [ht] at H'
    have H'' := l3 R₀ A hA P hP n (by omega) hnR (σ a) (σ a') (hσn a) (hσn a') ζR hζR (2 * omegaStd a a')
      (AlgebraicClosure K) (iK.comp κ) H' k ρ
    rw [← map_zpow]
    exact H''

end GlobalTheory.LevSpread
