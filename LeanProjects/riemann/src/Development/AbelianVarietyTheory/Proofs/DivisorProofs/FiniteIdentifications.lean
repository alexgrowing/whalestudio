import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsChartMember
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalSiegelObjectOddLevelRigid
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelObjectPullbackExistsAndPrincipal
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelStructurePullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAbelianSchemeOfIsGrpPullback

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SiegFibreFinite

open GlobalTheory.CechPic GlobalTheory.SiegelPull GlobalTheory.ZM.SiegPull

theorem finite_torsion {K : Type} [Field K] [IsAlgClosed K] (B : Over (Sp K)) [GrpObj B] (hB : IsAbelianScheme B)
    {n : ℕ} (hn : 1 ≤ n) : Finite {x : 𝟙_ (Over (Sp K)) ⟶ B // x ^ n = 1} := by
  have := hB.smooth
  have := GlobalTheory.MulFiniteAny.isFinite_mulA K B hB n hn
  have := GlobalTheory.TorsionDivisible.finite_fibre_points (Out.mulA B n) 1
  exact Finite.of_equiv _ (Equiv.subtypeEquivRight (p := fun x => x ≫ Out.mulA B n = 1) fun x => by
    rw [Out.mulA, MonObj.comp_pow, Category.comp_id])

theorem finite_over_point {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} (hL : L.IsLB)
    (hamp : Out.RelAmple A L) {K : Type} [Field K] [IsAlgClosed K] {B : Over (Sp K)} [GrpObj B]
    (hB : IsAbelianScheme B) (z : Sp K ⟶ S) (m : Pic B.left) :
    Set.Finite {φ : B.left ⟶ A.left | IsGrpPullback B A z φ ∧ pull φ (cls L hL) = m} := by
  rcases Set.eq_empty_or_nonempty {φ : B.left ⟶ A.left | IsGrpPullback B A z φ ∧ pull φ (cls L hL) = m} with
    h | ⟨φ₁, h₁, -⟩
  · rw [h]; exact Set.finite_empty
  obtain ⟨N, hN, hNK⟩ := GlobalTheory.AmpleFiniteOrder.exists_ge_cast_ne_zero K 3
  have := hB.comm
  obtain ⟨hfin, hdiv⟩ := GlobalTheory.TorsionDivisible.finite_torsion_and_divisible K B hB N hNK
  let U : Over (Sp K) := 𝟙_ (Over (Sp K))
  have hfin' : Finite {g : Over.mk (U.hom ≫ z) ⟶ A // g ^ N = 1} := by
    refine Finite.of_surjective (fun x : {x : U ⟶ B // x ^ N = 1} =>
      (⟨pushHom h₁ U x.1, by rw [← map_pow, x.2, map_one]⟩ : {g : Over.mk (U.hom ≫ z) ⟶ A // g ^ N = 1})) ?_
    rintro ⟨g, hg⟩
    obtain ⟨x, rfl⟩ := push_surjective h₁ U g
    exact ⟨⟨x, push_injective h₁ U (by rw [map_pow, hg, map_one])⟩, rfl⟩
  refine Set.finite_coe_iff.1 ?_
  refine Finite.of_injective (β := {x : U ⟶ B // x ^ N = 1} → {g : Over.mk (U.hom ≫ z) ⟶ A // g ^ N = 1})
    (fun φ x => ⟨pushHom φ.2.1 U x.1, by rw [← map_pow, x.2, map_one]⟩) ?_
  rintro ⟨φ, h, hc⟩ ⟨φ', h', hc'⟩ e
  have e₀ : ∀ x : U ⟶ B, x ^ N = 1 → x.left ≫ φ = x.left ≫ φ' := fun x hx =>
    congrArg (fun q => q.1.left) (congrFun e ⟨x, hx⟩)
  obtain ⟨σ, hσ, eσ⟩ := GlobalTheory.SiegRigid.exists_aut h h'
  have hu : IsMonHom (σ.hom * (𝟙 B)⁻¹) := by
    rw [Hom.mul_def, Hom.inv_def]; infer_instance
  obtain ⟨ψ, hψ, eψ⟩ := hdiv _ hu fun x hx => by
    have : x ≫ σ.hom = x := Over.OverMorphism.ext (h'.1.hom_ext
      (by rw [Over.comp_left, Category.assoc, eσ]; exact e₀ x hx) (by rw [Over.w, Over.w]))
    rw [MonObj.comp_mul, GrpObj.comp_inv, this, Category.comp_id, mul_inv_cancel]
  refine Subtype.ext (GlobalTheory.SiegRigid.eq_of_field hL hamp hB h h' (hc.trans hc'.symm) hN hNK fun Ω _ _ t x hx => ?_)
  have e₁ : x ≫ (σ.hom * (𝟙 B)⁻¹) = 1 := by
    rw [eψ, MonObj.comp_pow, ← MonObj.pow_comp, hx, MonObj.one_comp]
  rw [MonObj.comp_mul, GrpObj.comp_inv, Category.comp_id, mul_inv_eq_one] at e₁
  change x.left ≫ φ = x.left ≫ φ'
  rw [← eσ, ← Category.assoc, ← Over.comp_left, e₁]

theorem pull_diag {S S' : Scheme.{0}} {A : Over S} {B : Over S'} {φ : B.left ⟶ A.left}
    {φ₂ : (B ⊗ B).left ⟶ (A ⊗ A).left} (hs : IsSquare φ φ₂) (m : Pic (A ⊗ A).left) :
    pull φ (pull (lift (𝟙 A) (𝟙 A)).left m) = pull (lift (𝟙 B) (𝟙 B)).left (pull φ₂ m) := by
  have e : (lift (𝟙 B) (𝟙 B)).left ≫ φ₂ = φ ≫ (lift (𝟙 A) (𝟙 A)).left :=
    (Category.id_comp _).symm.trans (lift_sq hs (T := Over.mk (φ ≫ A.hom)) (T' := B) (𝟙 B.left) (𝟙 B) (𝟙 B)
      (Z := A) φ (𝟙 A) (𝟙 A) (by simp) (by simp))
  rw [← pull_comp, ← pull_comp, e]

variable {o : Type} [CommRing o] {ζ : o} {g n : ℕ}

theorem point_eq (F : SFam g n ζ) {R : Type} [CommRing R] [IsLocalRing R] {B : Over (Sp R)} [GrpObj B]
    {x x' : Sp R ⟶ F.X} {φ φ' : B.left ⟶ F.univ.A.left} {φ₂ φ₂' : (G2 B).left ⟶ (G2 F.univ.A).left}
    (hs : x ≫ F.s = x' ≫ F.s) (h : IsGrpPullback B F.univ.A x φ) (h' : IsGrpPullback B F.univ.A x' φ')
    (q : IsSquare φ φ₂) (q' : IsSquare φ' φ₂')
    (hc : pull φ₂ (cls F.univ.P F.univ.isLB) = pull φ₂' (cls F.univ.P F.univ.isLB))
    (hl : ∀ a, SiegelPull.secPull h (F.univ.lev a) = SiegelPull.secPull h' (F.univ.lev a)) : x = x' := by
  obtain ⟨c, hc₀⟩ := (GlobalTheory.siegPre_pullback g n o ζ F.X (Sp R) F.s _ x F.univ rfl).1
  refine F.inj R x x' _ c hs hc₀ ?_
  obtain ⟨χ, χ₂, k, r, w, l⟩ := hc₀
  obtain ⟨e, he, ee⟩ := grpPullback_iso k h
  have k' : IsGrpPullback c.A F.univ.A x' (e.hom.left ≫ φ') :=
    ((isGrpPullback_of_iso e).comp h').congr (Category.id_comp _) rfl
  refine ⟨e.hom.left ≫ φ', (e.hom ⊗ₘ e.hom).left ≫ φ₂', k', isSquare_comp (isSquare_tensor e.hom) q', ?_,
    fun a => ?_⟩
  · have e₂ : χ₂ = (e.hom ⊗ₘ e.hom).left ≫ φ₂ := isSquare_unique r (isSquare_comp (isSquare_tensor e.hom) q) ee.symm
    refine (cls_eq_iff c.isLB (pull_isLB F.univ.isLB _)).1 ?_
    rw [(cls_eq_iff c.isLB (pull_isLB F.univ.isLB _)).2 w, cls_pull F.univ.isLB, cls_pull F.univ.isLB, e₂, pull_comp,
      pull_comp, hc]
  · have e₃ : c.lev a ≫ e.hom = SiegelPull.secPull h (F.univ.lev a) := Over.OverMorphism.ext (h.1.hom_ext
      (by rw [Over.comp_left, Category.assoc, ee, SiegelPull.secPull_left]; exact l a) (by rw [Over.w, Over.w]))
    rw [← Category.assoc, ← Over.comp_left, e₃, hl, SiegelPull.secPull_left]

theorem finite_points (F : SFam g n ζ) (hn : 1 ≤ n) {K : Type} [Field K] [IsAlgClosed K] {B : Over (Sp K)} [GrpObj B]
    (hB : IsAbelianScheme B) (s : Sp K ⟶ Sp o) (m : Pic (G2 B).left) :
    Set.Finite {x : Sp K ⟶ F.X | x ≫ F.s = s ∧ ∃ (φ : B.left ⟶ F.univ.A.left)
      (φ₂ : (G2 B).left ⟶ (G2 F.univ.A).left), IsGrpPullback B F.univ.A x φ ∧ IsSquare φ φ₂ ∧
        pull φ₂ (cls F.univ.P F.univ.isLB) = m} := by
  have := finite_torsion B hB hn
  have := hB.comm
  refine Set.finite_coe_iff.1 ?_
  have H := fun x : {x : Sp K ⟶ F.X | x ≫ F.s = s ∧ ∃ (φ : B.left ⟶ F.univ.A.left)
      (φ₂ : (G2 B).left ⟶ (G2 F.univ.A).left), IsGrpPullback B F.univ.A x φ ∧ IsSquare φ φ₂ ∧
        pull φ₂ (cls F.univ.P F.univ.isLB) = m} => x.2.2
  choose φ φ₂ h q hc using H
  refine Finite.of_injective (β := (Fin g ⊕ Fin g) → {y : 𝟙_ (Over (Sp K)) ⟶ B // y ^ n = 1})
    (fun x i => ⟨SiegelPull.secPull (h x) (F.univ.lev (Pi.single i 1)), push_injective (h x) _ (by
      rw [map_pow, map_one, push_secPull', ← MonObj.comp_pow, F.univ.lev_tors, MonObj.comp_one])⟩) ?_
  intro x x' e
  refine Subtype.ext (point_eq F (x.2.1.trans x'.2.1.symm) (h x) (h x') (q x) (q x') ((hc x).trans (hc x').symm) ?_)
  let p := fun y => (AddMonoidHom.mk' (fun a => Additive.ofMul (SiegelPull.secPull (h y) (F.univ.lev a))) fun a b => by
      rw [← ofMul_mul]
      exact congrArg _ (push_injective (h y) _ (by
        rw [map_mul, push_secPull', push_secPull', push_secPull', F.univ.lev_add, MonObj.comp_mul])) :
    (Fin g ⊕ Fin g → ℤ) →+ Additive (𝟙_ (Over (Sp K)) ⟶ B))
  have hp : p x = p x' := AddMonoidHom.functions_ext' _ _ _ fun i => AddMonoidHom.ext_int
    (congrArg (fun z => Additive.ofMul z.1) (congrFun e i))
  exact fun a => congrArg Additive.toMul (DFunLike.congr_fun hp a)

theorem finite_identifications : ∀ (o' : Type) [CommRing o'] (ζ' : o') (g' n' : ℕ) (F' : SFam g' n' ζ'), 1 ≤ n' → ∀ (K : Type) [Field K] [IsAlgClosed K] (B : Over (Sp K)) [GrpObj B] (x₀ : Sp K ⟶ F'.X) (φ₀ : B.left ⟶ F'.univ.A.left) (φ₀₂ : (G2 B).left ⟶ (G2 F'.univ.A).left), IsGrpPullback B F'.univ.A x₀ φ₀ → IsSquare φ₀ φ₀₂ → ∀ p₀ : Sp K ⟶ B.left, Set.Finite {P' : Sp K ⟶ F'.univ.A.left | ∃ (x' : Sp K ⟶ F'.X) (φ : B.left ⟶ F'.univ.A.left) (φ₂ : (G2 B).left ⟶ (G2 F'.univ.A).left), x' ≫ F'.s = x₀ ≫ F'.s ∧ IsGrpPullback B F'.univ.A x' φ ∧ IsSquare φ φ₂ ∧ LBIso (F'.univ.P.pull φ₀₂) (F'.univ.P.pull φ₂) ∧ P' = p₀ ≫ φ} := by
  intro o _ ζ g n F hn K _ _ B _ x₀ φ₀ φ₀₂ h₀ _ p₀
  have hB : IsAbelianScheme B := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback F.univ.ab h₀
  let m := pull φ₀₂ (cls F.univ.P F.univ.isLB)
  have h₁ := finite_points F hn hB (x₀ ≫ F.s) m
  have h₂ := fun x => finite_over_point (pull_isLB F.univ.isLB _) F.princ.1 hB x (pull (lift (𝟙 B) (𝟙 B)).left m)
  refine ((h₁.biUnion fun x _ => h₂ x).image (p₀ ≫ ·)).subset ?_
  rintro _ ⟨x, φ, φ₂, hs, h, q, w, rfl⟩
  have e : pull φ₂ (cls F.univ.P F.univ.isLB) = m := by
    have := (cls_eq_iff (pull_isLB F.univ.isLB _) (pull_isLB F.univ.isLB _)).2 w
    rw [cls_pull F.univ.isLB, cls_pull F.univ.isLB] at this
    exact this.symm
  refine ⟨φ, Set.mem_biUnion (x := x) ⟨hs, φ, φ₂, h, q, e⟩ ⟨h, ?_⟩, rfl⟩
  rw [← e, ← pull_diag q]
  exact congrArg _ (cls_pull F.univ.isLB _ _)

end GlobalTheory.SiegFibreFinite
