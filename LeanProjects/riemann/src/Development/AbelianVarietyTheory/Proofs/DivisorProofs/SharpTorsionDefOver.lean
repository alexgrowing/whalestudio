import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsChartMember
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefOverOfFiniteOrbit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionIsoOfGroupPullbackGeneric
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.Sep

variable {V V₁ : Type} [CommRing V] [IsDomain V] [CommRing V₁] [IsDomain V₁]

theorem exists_points_equiv {W₀ : Type} [CommRing W₀] (ρ : V →+* V₁) (ib : W₀ →+* V) (Q : Data V) (D : DegPre V₁)
    (pr : Fin 8 → (D.P.A ⟶ (Over.pullback (spMap ρ)).obj Q.B)) (hpr : ∀ a, IsMonHom (pr a))
    (huniv : ∀ (T : Over (Sp V₁)) (y : Fin 8 → (T ⟶ (Over.pullback (spMap ρ)).obj Q.B)),
      ∃! x : T ⟶ D.P.A, ∀ a, x ≫ pr a = y a)
    (B₀ : Over (Sp W₀)) [GrpObj B₀] (β : Q.B.left ⟶ B₀.left) (hβ : IsGrpPullback Q.B B₀ (spMap ib) β)
    {X : Scheme.{0}} (t : X ⟶ Sp V₁) (g : X ⟶ Sp W₀) (hg : t ≫ spMap ρ ≫ spMap ib = g) :
    ∃ Φ : (Over.mk t ⟶ D.P.A) ≃* (Fin 8 → (Over.mk g ⟶ B₀)),
      ∀ x a, (Φ x a).left = x.left ≫ (pr a).left ≫ pullback.fst Q.B.hom (spMap ρ) ≫ β := by
  obtain ⟨E1, hE1⟩ := GlobalTheory.GroupBplus.Aff.exists_mulEquiv_points_of_isGrpPullback
    (isGrpPullback_pullback Q.B (spMap ρ)) t (t ≫ spMap ρ) rfl
  obtain ⟨E2, hE2⟩ := GlobalTheory.GroupBplus.Aff.exists_mulEquiv_points_of_isGrpPullback hβ (t ≫ spMap ρ) g
    (by rw [Category.assoc]; exact hg)
  let P : (Over.mk t ⟶ D.P.A) →* (Fin 8 → (Over.mk t ⟶ (Over.pullback (spMap ρ)).obj Q.B)) :=
    Pi.monoidHom fun a =>
      { toFun := fun x => x ≫ pr a
        map_one' := MonObj.one_comp _
        map_mul' := fun x y => MonObj.mul_comp _ _ _ }
  have hP : Function.Bijective P := by
    refine ⟨fun x y h => ?_, fun y => ?_⟩
    · obtain ⟨z, -, hz⟩ := huniv (Over.mk t) (P x)
      exact (hz x fun a => rfl).trans (hz y fun a => (congrFun h a).symm).symm
    · obtain ⟨z, hz, -⟩ := huniv (Over.mk t) y
      exact ⟨z, funext hz⟩
  refine ⟨(MulEquiv.ofBijective P hP).trans (MulEquiv.piCongrRight fun _ => E1.trans E2), fun x a => ?_⟩
  show (E2 (E1 (x ≫ pr a))).left = _
  rw [hE2, hE1, Over.comp_left]
  simp only [Category.assoc]

theorem spMap_three {A B C E : Type} [CommRing A] [CommRing B] [CommRing C] [CommRing E] (f : A →+* B) (g : B →+* C)
    (h : C →+* E) : spMap h ≫ spMap g ≫ spMap f = spMap ((h.comp g).comp f) := by
  simp only [spMap, ← Spec.map_comp]; rfl

theorem sharp_c_defOver {W₀ : Type} [CommRing W₀] (ρ : V →+* V₁) (ib : W₀ →+* V) (Q : Data V) (D : DegPre V₁)
    (e : (Fin 8 → Q.X) ≃+ D.X) (pr : Fin 8 → (D.P.A ⟶ (Over.pullback (spMap ρ)).obj Q.B))
    (hc : ∀ mu a, (D.c (e mu) ≫ pr a).left ≫ pullback.fst Q.B.hom (spMap ρ) = spMap ρ ≫ (Q.c (mu a)).left)
    (B₀ : Over (Sp W₀)) (β : Q.B.left ⟶ B₀.left) (c₀ : Q.X → (𝟙_ (Over (Sp W₀)) ⟶ B₀))
    (hβc : ∀ a, (Q.c a).left ≫ β = spMap ib ≫ (c₀ a).left)
    (K : Type) [Field K] (ev : V₁ →+* K) (k₀ : Subfield K) (hk : ∀ a, ev (ρ (ib a)) ∈ k₀) :
    ∀ mu a, DefOver k₀ (spMap ev ≫ (D.c (e mu) ≫ pr a).left ≫ pullback.fst Q.B.hom (spMap ρ) ≫ β) := by
  intro mu a
  have h : spMap ev ≫ (D.c (e mu) ≫ pr a).left ≫ pullback.fst Q.B.hom (spMap ρ) ≫ β =
      spMap ((ev.comp ρ).comp ib) ≫ (c₀ (mu a)).left := by
    rw [reassoc_of% (hc mu a), hβc, ← spMap_three]
    simp only [Category.assoc]
  rw [h]
  refine ⟨spMap (((ev.comp ρ).comp ib).codRestrict k₀ hk) ≫ (c₀ (mu a)).left, ?_⟩
  rw [← Category.assoc]
  congr 1
  simp only [spMap, ← Spec.map_comp]; rfl

theorem sharp_torsion_defOver {W₀ : Type} [CommRing W₀] [IsNoetherianRing V₁] (ρ : V →+* V₁) (ib : W₀ →+* V)
    (Q : Data V) (D : DegPre V₁)
    (pr : Fin 8 → (D.P.A ⟶ (Over.pullback (spMap ρ)).obj Q.B)) (hpr : ∀ a, IsMonHom (pr a))
    (huniv : ∀ (T : Over (Sp V₁)) (y : Fin 8 → (T ⟶ (Over.pullback (spMap ρ)).obj Q.B)),
      ∃! x : T ⟶ D.P.A, ∀ a, x ≫ pr a = y a)
    (B₀ : Over (Sp W₀)) [GrpObj B₀] (β : Q.B.left ⟶ B₀.left) (hβ : IsGrpPullback Q.B B₀ (spMap ib) β)
    (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (k₀ : Subfield K) (hk₀ : IsAlgClosed k₀)
    (hk : ∀ a, ev (ρ (ib a)) ∈ k₀) (N : ℕ) (hN : 1 ≤ N) (hNu : IsUnit (N : V₁))
    (x : Over.mk (spMap ev) ⟶ D.P.A) (hx : x ^ N = 1) (a : Fin 8) :
    DefOver k₀ (x.left ≫ (pr a).left ≫ pullback.fst Q.B.hom (spMap ρ) ≫ β) := by
  classical
  obtain ⟨Φ, hΦ⟩ := exists_points_equiv ρ ib Q D pr hpr huniv B₀ β hβ (spMap ev) (spMap ((ev.comp ρ).comp ib))
    (spMap_three _ _ _)
  have hNK : (N : K) ≠ 0 := by
    have := (hNu.map ev).ne_zero
    simpa using this
  have hcard := (GlobalTheory.abelianSchemeLaws_all.1.mulN (Sp V₁) D.P N hN).2.2.2.2 K (spMap ev) hNK
  have hfin : Finite {y : Over.mk (spMap ev) ⟶ D.P.A // y ^ N = 1} :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero _ (by omega))
  refine defOver_of_finite_orbit K k₀ hk₀ _ _ ((Set.finite_range fun y : {y : Over.mk (spMap ev) ⟶ D.P.A // y ^ N = 1} =>
    (Φ y.1 a).left).subset ?_)
  rintro _ ⟨σ, hσ, rfl⟩
  have hσf : spMap σ.toRingHom ≫ spMap ((ev.comp ρ).comp ib) = spMap ((ev.comp ρ).comp ib) := by
    simp only [spMap, ← Spec.map_comp]
    congr 2
    ext w
    exact hσ _ (hk w)
  let h : Over.mk (spMap ((ev.comp ρ).comp ib)) ⟶ Over.mk (spMap ((ev.comp ρ).comp ib)) :=
    Over.homMk (spMap σ.toRingHom) hσf
  refine ⟨⟨Φ.symm (fun b => h ≫ Φ x b), ?_⟩, ?_⟩
  · have e : (fun b => h ≫ Φ x b) ^ N = 1 := by
      funext b
      rw [Pi.pow_apply, ← MonObj.comp_pow, ← Pi.pow_apply, ← map_pow, hx, map_one, Pi.one_apply, MonObj.comp_one]
    rw [← map_pow, e, map_one]
  · show (Φ (Φ.symm fun b => h ≫ Φ x b) a).left = _
    rw [MulEquiv.apply_symm_apply, Over.comp_left, hΦ]
    rfl

example {W₀ : Type} [CommRing W₀] (W : Matrix (Fin 8) (Fin 8) ℤ) (Q : Data V) (ρ : V →+* V₁) (D : DegPre V₁)
    (e : (Fin 8 → Q.X) ≃+ D.X) (τ₀ : Gens Q) (ib : W₀ →+* V) (h₁ : SharpRef W Q ρ D e) (h₂ : FromBase Q τ₀ ib) :
    ∃ (pr : Fin 8 → (D.P.A ⟶ (Over.pullback (spMap ρ)).obj Q.B)) (_ : ∀ a, IsMonHom (pr a))
      (B₀ : Over (Sp W₀)) (_ : GrpObj B₀) (β : Q.B.left ⟶ B₀.left) (c₀ : Q.X → (𝟙_ (Over (Sp W₀)) ⟶ B₀)),
      (∀ (T : Over (Sp V₁)) (y : Fin 8 → (T ⟶ (Over.pullback (spMap ρ)).obj Q.B)), ∃! x : T ⟶ D.P.A, ∀ a, x ≫ pr a = y a) ∧
      (∀ mu a, (D.c (e mu) ≫ pr a).left ≫ pullback.fst Q.B.hom (spMap ρ) = spMap ρ ≫ (Q.c (mu a)).left) ∧
      IsGrpPullback Q.B B₀ (spMap ib) β ∧ ∀ a, (Q.c a).left ≫ β = spMap ib ≫ (c₀ a).left := by
  obtain ⟨pr, -, hpr, hu, -, hc, -⟩ := h₁
  obtain ⟨B₀, iG, -, -, c₀, -, β, -, -, -, -, hβ, -, -, hβc, -, -⟩ := h₂
  exact ⟨pr, hpr, B₀, iG, β, c₀, hu, hc, hβ, hβc⟩

end GlobalTheory.Poinc.Sep
