import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueHomExtensionOfIsOpenImmersion
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RegularLocalRingNormalDomain
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SelfTorusExtensionCoordValuesEqOne
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPullbackDegPreStrictLineBundleIso
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsSquareUnique
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsTorusAndQuotientHom
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PolDeg

section Family

variable {o : Type} [CommRing o] {ζ : o} {g n : ℕ} (F : SFam g n ζ) {R : Type} [CommRing R] [IsDomain R]
  (y : Sp (FractionRing R) ⟶ F.X) {G₁ : Over (Sp R)} [GrpObj G₁] (α₁ : pullback G₁.hom (jK R) ⟶ F.univ.A.left)

def IsGenFibre : Prop := IsGrpPullback ((Over.pullback (jK R)).obj G₁) F.univ.A y α₁

def IsUnifAlong {R' : Type} [CommRing R'] [IsDomain R'] {I : Ideal R'} (ρ : R →+* R') {G' : Over (Sp R')} [GrpObj G']
    [IsCommMonObj G'] (π : G'.left ⟶ G₁.left) {D : DegData R' I} {A : PolAV (Sp (FractionRing R'))} (U : Unif I D A G') : Prop :=
  IsGrpPullback G' G₁ (spMap ρ) π ∧
    ∃ (κ : Sp (FractionRing R') ⟶ Sp (FractionRing R)) (πK : pullback G'.hom (jK R') ⟶ pullback G₁.hom (jK R))
      (α : A.A.left ⟶ F.univ.A.left) (α₂ : (G2 A.A).left ⟶ (G2 F.univ.A).left),
      κ ≫ jK R = jK R' ≫ spMap ρ ∧ πK ≫ pullback.fst G₁.hom (jK R) = pullback.fst G'.hom (jK R') ≫ π ∧
        IsGrpPullback A.A F.univ.A (κ ≫ y) α ∧ IsSquare α α₂ ∧ LBIso (abelian₂ A.A A.L) (F.univ.P.pull α₂) ∧
        U.gen.hom.left ≫ α = πK ≫ α₁

def IsMumfordFam [IsLocalRing R] (Q : Data R) : Prop :=
  IsCN R ∧ Q.IsPos (maximalIdeal R) ∧
  ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), IsCN R' → Function.Injective ρ → ρ.Finite →
    ∀ (D : DegData R' (maximalIdeal R')) (ε : D.toPre.X ≃+ Q.X), Refines Q ρ D.toPre ε →
      ∃ (G' : Over (Sp R')) (_ : GrpObj G') (_ : IsCommMonObj G') (π : G'.left ⟶ G₁.left) (A : PolAV (Sp (FractionRing R')))
        (U : Unif (maximalIdeal R') D A G'), IsUnifAlong F y α₁ ρ π U

variable {F y α₁}

theorem IsMumfordFam.isCN [IsLocalRing R] {Q : Data R} (h : IsMumfordFam F y α₁ Q) : IsCN R := h.1

theorem IsMumfordFam.isPos [IsLocalRing R] {Q : Data R} (h : IsMumfordFam F y α₁ Q) : Q.IsPos (maximalIdeal R) := h.2.1

theorem IsMumfordFam.unif [IsLocalRing R] {Q : Data R} (h : IsMumfordFam F y α₁ Q) :
    ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), IsCN R' → Function.Injective ρ → ρ.Finite →
    ∀ (D : DegData R' (maximalIdeal R')) (ε : D.toPre.X ≃+ Q.X), Refines Q ρ D.toPre ε →
      ∃ (G' : Over (Sp R')) (_ : GrpObj G') (_ : IsCommMonObj G') (π : G'.left ⟶ G₁.left) (A : PolAV (Sp (FractionRing R')))
        (U : Unif (maximalIdeal R') D A G'), IsUnifAlong F y α₁ ρ π U := h.2.2

end Family

example {o : Type} [CommRing o] {ζ : o} {g n : ℕ} (F : SFam g n ζ) (y : Sp (FractionRing (PowerSeries ℚ)) ⟶ F.X)
    (G₁ : Over (Sp (PowerSeries ℚ))) [GrpObj G₁] (α₁ : pullback G₁.hom (jK (PowerSeries ℚ)) ⟶ F.univ.A.left) :
    ¬ IsMumfordFam F y α₁ (Wit.tate 0) := fun h => Wit.not_isPos_tate_zero h.isPos

section Charts

variable {o : Type} [CommRing o] {ζ : o} {g n : ℕ} (F : SFam g n ζ) {S : Scheme.{0}} (s : S ⟶ Sp o) (j : F.X ⟶ S)

def PreChart [IsOpenImmersion j] (φ : InvFun ℤ) (BD : EffCartierData S) (d : ℕ) (x : S) : Prop :=
  ∃ (R : Type) (_ : CommRing R) (_ : IsRegularLocalRing R) (_ : IsDomain R) (b : o →+* R) (ξ : Sp R ⟶ S) (m : ℕ)
    (t : Fin m → R) (Q : Data R) (δ : Fin m → LinearMap.BilinForm ℤ Q.X) (a : Fin m → ℕ)
    (G₁ : Over (Sp R)) (_ : GrpObj G₁) (y : Sp (FractionRing R) ⟶ F.X) (α₁ : pullback G₁.hom (jK R) ⟶ F.univ.A.left),
    (IsAdicComplete (maximalIdeal R) R ∧ CharZero R ∧ ξ ≫ s = spMap b ∧ ξ (closedPoint R) = x ∧
      IsEtaleCompletion (Scheme.stalkClosedPointTo ξ).hom ∧
      ((residue R).comp (Scheme.stalkClosedPointTo ξ).hom).FormallyUnramified) ∧
    (IsRelParam b t ∧ idlAlong (Scheme.IdealSheafData.vanishingIdeal j.opensRange.compl) ξ = Ideal.span {∏ i, t i} ∧
      ∀ p : Sp R, ξ p ∈ Set.range j ↔ ∏ i, t i ∉ p.asIdeal) ∧
    (IsSemiAbelian G₁ ∧ (∀ p : Sp R, p ∈ abLocus G₁ ↔ ∏ i, t i ∉ p.asIdeal) ∧ y ≫ j = jK R ≫ ξ ∧ IsGenFibre F y α₁) ∧
    (IsMumfordFam F y α₁ Q ∧ Module.finrank ℤ Q.X ≤ g ∧ IsCone id φ δ ∧ (∀ z, z ≠ 0 → ∃ i, 0 < δ i z z) ∧
      Q.IsMonomialTau t fun i => (n : ℤ) • δ i) ∧
    (∀ i, (a i : ℝ) = d * φ.evalZ ((n : ℤ) • δ i)) ∧ idlAlong BD.idealSheaf ξ = Ideal.span {∏ i, t i ^ a i}

end Charts

section Generic

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R']

theorem exists_genericMap {ρ : R →+* R'} (hρ : Function.Injective ρ) :
    ∃ κ : Sp (FractionRing R') ⟶ Sp (FractionRing R), κ ≫ jK R = jK R' ≫ spMap ρ := by
  have h : Function.Injective ((algebraMap R' (FractionRing R')).comp ρ) := (IsFractionRing.injective R' _).comp hρ
  refine ⟨spMap (IsFractionRing.lift (K := FractionRing R) h), ?_⟩
  change spMap _ ≫ spMap (algebraMap R (FractionRing R)) = spMap (algebraMap R' (FractionRing R')) ≫ spMap ρ
  rw [← spMap_comp, ← spMap_comp]
  congr 1
  ext r
  simp

omit [IsDomain R] in

theorem ne_zero_of_isRelParam {o : Type} [CommRing o] [IsLocalRing R] {b : o →+* R} {m : ℕ} {t : Fin m → R}
    (h : IsRelParam b t) (i : Fin m) : t i ≠ 0 := fun h0 => by
  have h₁ := h.mem_of_mem_sq (Pi.single i 1) (by
    rw [Finset.sum_eq_single i (fun k _ hk => by simp [Pi.single_eq_of_ne hk]) (by simp), h0, mul_zero]
    exact zero_mem _) i
  exact (maximalIdeal.isMaximal R).ne_top ((Ideal.eq_top_iff_one _).2 (by simpa using h₁))

end Generic

section Good

variable {o : Type} [CommRing o] {ζ : o} {g n : ℕ} {F : SFam g n ζ} {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R]

theorem lbIso_pull_comp {X Y Z : Scheme.{0}} {L : LB X} {M : LB Y} {a : Y ⟶ X} (h : LBIso M (L.pull a)) (j : Z ⟶ Y)
    {a' : Z ⟶ X} (e : a' = j ≫ a) : LBIso (M.pull j) (L.pull a') :=
  LBIso.chartPull (Geo.Tor.chartPullPull M j j rfl) (Geo.Tor.chartPullSame L _ (fun _ => a) _ j fun _ => e) h

theorem isSquare_comp {S S' S'' : Scheme.{0}} {G : Over S} {G' : Over S'} {G'' : Over S''} {φ : G'.left ⟶ G.left}
    {φ₂ : (G' ⊗ G').left ⟶ (G ⊗ G).left} {ψ : G''.left ⟶ G'.left} {ψ₂ : (G'' ⊗ G'').left ⟶ (G' ⊗ G').left}
    (h' : IsSquare ψ ψ₂) (h : IsSquare φ φ₂) : IsSquare (ψ ≫ φ) (ψ₂ ≫ φ₂) :=
  ⟨by rw [Category.assoc, h.1, ← Category.assoc, h'.1, Category.assoc],
    by rw [Category.assoc, h.2, ← Category.assoc, h'.2, Category.assoc]⟩

end Good

section Compare

variable {o : Type} [CommRing o] {ζ : o} {g n : ℕ} {F : SFam g n ζ} {S : Scheme.{0}} {s : S ⟶ Sp o} {j : F.X ⟶ S}
  {G : Over S} [GrpObj G] {e : F.univ.A.left ⟶ G.left} {R : Type} [CommRing R] [IsDomain R]
  {y : Sp (FractionRing R) ⟶ F.X} {G₁ : Over (Sp R)} [GrpObj G₁] {α₁ : pullback G₁.hom (jK R) ⟶ F.univ.A.left}
  {ξ : Sp R ⟶ S} {π₁ : G₁.left ⟶ G.left}

theorem IsUnifAlong.isUnifOf (h₁ : IsGrpPullback G₁ G ξ π₁) (hy : y ≫ j = jK R ≫ ξ)
    (hα : α₁ ≫ e = pullback.fst G₁.hom (jK R) ≫ π₁) {R' : Type} [CommRing R'] [IsDomain R'] {I : Ideal R'} {ρ : R →+* R'}
    {G' : Over (Sp R')} [GrpObj G'] [IsCommMonObj G'] {π : G'.left ⟶ G₁.left} {D : DegData R' I}
    {A : PolAV (Sp (FractionRing R'))} {U : Unif I D A G'} (h : IsUnifAlong F y α₁ ρ π U) :
    IsUnifOf F j e (spMap ρ ≫ ξ) (π ≫ π₁) U := by
  obtain ⟨hπ, κ, πK, α, α₂, hκ, hK, hA, hsq, hL, hU⟩ := h
  refine ⟨hπ.comp h₁, κ ≫ y, α, α₂, ?_, hA, hsq, hL, ?_⟩
  · rw [Category.assoc, hy, ← Category.assoc, hκ, Category.assoc]
  · rw [← Category.assoc, hU, Category.assoc, hα, ← Category.assoc, hK, Category.assoc]

theorem IsMumfordFam.isMumfordOf [IsLocalRing R] (h₁ : IsGrpPullback G₁ G ξ π₁) (hy : y ≫ j = jK R ≫ ξ)
    (hα : α₁ ≫ e = pullback.fst G₁.hom (jK R) ≫ π₁) {Q : Data R} (h : IsMumfordFam F y α₁ Q) : IsMumfordOf F j e ξ Q := by
  refine ⟨h.isCN, h.isPos, fun R' _ _ _ ρ hR hρ hf D ε hD => ?_⟩
  obtain ⟨G', _, _, π, A, U, hU⟩ := h.unif R' ρ hR hρ hf D ε hD
  exact ⟨G', inferInstance, inferInstance, π ≫ π₁, A, U, hU.isUnifOf h₁ hy hα⟩

theorem IsGenFibre.exists_isGrpPullback [IsNoetherianRing R] [IsIntegrallyClosed R] (hG : IsSemiAbelian G)
    (he : IsGrpPullback F.univ.A G j e) (hG₁ : IsSemiAbelian G₁) (hy : y ≫ j = jK R ≫ ξ) (h : IsGenFibre F y α₁) :
    ∃ π₁ : G₁.left ⟶ G.left, IsGrpPullback G₁ G ξ π₁ ∧ α₁ ≫ e = pullback.fst G₁.hom (jK R) ≫ π₁ := by
  have h₀ := isGrpPullback_pullback G ξ
  have h₂ := (isGrpPullback_pullback ((Over.pullback ξ).obj G) (jK R)).comp h₀
  obtain ⟨E, hE, hE'⟩ := grpPullback_iso ((IsGrpPullback.comp h he).congr hy rfl) h₂
  obtain ⟨E₁, ⟨hE₁, hE₂⟩, -⟩ := GlobalTheory.SemiAbExtDomain.existsUnique_iso_extension_generic (FractionRing R) G₁
    ((Over.pullback ξ).obj G) hG₁ (IsSemiAbelian.pullback ξ G hG) E
  refine ⟨E₁.hom.left ≫ pullback.fst G.hom ξ, ((isGrpPullback_of_iso E₁).comp h₀).congr (Category.id_comp _) rfl, ?_⟩
  have h₃ : ((Over.pullback (jK R)).map E₁.hom).left ≫ pullback.fst ((Over.pullback ξ).obj G).hom (jK R) =
      pullback.fst G₁.hom (jK R) ≫ E₁.hom.left := pullback.lift_fst _ _ _
  have h₄ : E.hom = (Over.pullback (jK R)).map E₁.hom := hE₂.symm
  refine hE'.symm.trans ?_
  rw [h₄]
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ pullback.fst G.hom ξ) h₃).trans (Category.assoc _ _ _))

variable [IsOpenImmersion j] {φ : InvFun ℤ} {BD : EffCartierData S} {d : ℕ} {x : S}

theorem PreChart.hasPolChart (hG : IsSemiAbelian G) (he : IsGrpPullback F.univ.A G j e) (h : PreChart F s j φ BD d x) :
    HasPolChart F s j e φ BD d x := by
  obtain ⟨R, _, _, _, b, ξ, m, t, Q, δ, a, G₁, _, y, α₁, c₁, c₂, ⟨hG₁, -, hy, hα⟩, ⟨hM, c₃⟩, c₄⟩ := h
  have := (GlobalTheory.isDomain_and_isIntegrallyClosed_of_isRegularLocalRing R).2
  obtain ⟨π₁, h₁, h₂⟩ := hα.exists_isGrpPullback hG he hG₁ hy
  exact ⟨R, inferInstance, inferInstance, inferInstance, b, ξ, m, t, Q, δ, a, c₁, c₂, ⟨hM.isMumfordOf h₁ hy h₂, c₃⟩, c₄⟩

end Compare

end GlobalTheory.PolDeg
