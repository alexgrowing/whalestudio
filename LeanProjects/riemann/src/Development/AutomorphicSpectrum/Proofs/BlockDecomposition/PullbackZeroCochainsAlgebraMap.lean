import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.HodgeWedgeFields.H1CommutesBaseChange

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge

namespace GlobalTheory.CompanionTheory.HodgeLow

theorem qIsoAt_transport {R A₀ A₁ A₂ B₀ B₁ B₂ A₀' A₁' A₂' B₀' B₁' B₂' : Type} [CommRing R]
    [AddCommGroup A₀] [AddCommGroup A₁] [AddCommGroup A₂]
    [AddCommGroup B₀] [AddCommGroup B₁] [AddCommGroup B₂]
    [AddCommGroup A₀'] [AddCommGroup A₁'] [AddCommGroup A₂']
    [AddCommGroup B₀'] [AddCommGroup B₁'] [AddCommGroup B₂']
    [Module R A₀] [Module R A₁] [Module R A₂] [Module R B₀] [Module R B₁] [Module R B₂]
    [Module R A₀'] [Module R A₁'] [Module R A₂'] [Module R B₀'] [Module R B₁'] [Module R B₂']
    {a₀ : A₀ →ₗ[R] A₁} {a₁ : A₁ →ₗ[R] A₂} {b₀ : B₀ →ₗ[R] B₁} {b₁ : B₁ →ₗ[R] B₂} {f : A₁ →ₗ[R] B₁}
    {a₀' : A₀' →ₗ[R] A₁'} {a₁' : A₁' →ₗ[R] A₂'} {b₀' : B₀' →ₗ[R] B₁'} {b₁' : B₁' →ₗ[R] B₂'}
    {f' : A₁' →ₗ[R] B₁'}
    (ea₀ : A₀ ≃ₗ[R] A₀') (ea₁ : A₁ ≃ₗ[R] A₁') (ea₂ : A₂ ≃ₗ[R] A₂')
    (eb₀ : B₀ ≃ₗ[R] B₀') (eb₁ : B₁ ≃ₗ[R] B₁') (eb₂ : B₂ ≃ₗ[R] B₂')
    (ha₀ : ∀ x, ea₁ (a₀ x) = a₀' (ea₀ x)) (ha₁ : ∀ x, ea₂ (a₁ x) = a₁' (ea₁ x))
    (hb₀ : ∀ x, eb₁ (b₀ x) = b₀' (eb₀ x)) (hb₁ : ∀ x, eb₂ (b₁ x) = b₁' (eb₁ x))
    (hf : ∀ x, eb₁ (f x) = f' (ea₁ x)) (h : QIsoAt a₀ a₁ b₀ b₁ f) :
    QIsoAt a₀' a₁' b₀' b₁' f' := by
  refine ⟨fun x' hx' ⟨y', hy'⟩ ↦ ?_, fun z' hz' ↦ ?_⟩
  · obtain ⟨x, rfl⟩ := ea₁.surjective x'
    obtain ⟨y, rfl⟩ := eb₀.surjective y'
    have h1 : a₁ x = 0 := ea₂.injective (by rw [ha₁, hx', map_zero])
    have h2 : b₀ y = f x := eb₁.injective (by rw [hb₀, hy', hf])
    obtain ⟨w, rfl⟩ := h.1 x h1 ⟨y, h2⟩
    exact ⟨ea₀ w, (ha₀ w).symm⟩
  · obtain ⟨z, rfl⟩ := eb₁.surjective z'
    have h1 : b₁ z = 0 := eb₂.injective (by rw [hb₁, hz', map_zero])
    obtain ⟨x, y, hx, hy⟩ := h.2 z h1
    refine ⟨ea₁ x, eb₀ y, by rw [← ha₁, hx, map_zero], ?_⟩
    rw [← hf, ← map_sub, hy, hb₀]

section

variable {R : Type} [CommRing R] {C C' : Type} [Category.{0} C] [Category.{0} C']
  {F : C ⥤ CommAlgCat.{0} R} {F' : C' ⥤ CommAlgCat.{0} R}

theorem d2_apply (z : C2 F) {T T' T'' T''' : C} (φ : T ⟶ T') (ψ : T' ⟶ T'') (χ : T'' ⟶ T''') :
    d2 F z T T' T'' T''' φ ψ χ = z T' T'' T''' ψ χ - z T T'' T''' (φ ≫ ψ) χ +
      z T T' T''' φ (ψ ≫ χ) - mp F χ (z T T' T'' φ ψ) := rfl

theorem mem_Z2_iff (z : C2 F) : z ∈ Z2 F ↔ d2 F z = 0 := by
  refine ⟨fun h ↦ ?_, fun h T T' T'' T''' φ ψ χ ↦ ?_⟩
  · funext T T' T'' T''' φ ψ χ
    rw [d2_apply]
    have := h φ ψ χ
    simp only [Pi.zero_apply]
    linear_combination -this
  · have : d2 F z T T' T'' T''' φ ψ χ = 0 := by rw [h]; rfl
    rw [d2_apply] at this
    linear_combination -this

def pullbackZeroCochains (m : CoefMap (RingHom.id R) F F') : C0 F →ₗ[R] C0 F' where
  toFun g T := m.α T (g (m.G.obj T))
  map_add' _ _ := funext fun _ ↦ map_add _ _ _
  map_smul' _ _ := funext fun _ ↦ m.smul _ _ _

def pullbackOneCochains (m : CoefMap (RingHom.id R) F F') : C1 F →ₗ[R] C1 F' where
  toFun f T T' φ := m.α T' (f _ _ (m.G.map φ))
  map_add' _ _ := by funext T T' φ; exact map_add _ _ _
  map_smul' _ _ := by funext T T' φ; exact m.smul _ _ _

def pullbackTwoCochains (m : CoefMap (RingHom.id R) F F') : C2 F →ₗ[R] C2 F' where
  toFun z T T' T'' φ ψ := m.α T'' (z _ _ _ (m.G.map φ) (m.G.map ψ))
  map_add' _ _ := by funext T T' T'' φ ψ; exact map_add _ _ _
  map_smul' _ _ := by funext T T' T'' φ ψ; exact m.smul _ _ _

theorem cn_heq {n : ℕ} (f : Cn F n) {c c' : Fin (n + 1) ⥤ C} (h : c = c') : HEq (f c) (f c') := by
  subst h; rfl

theorem mk₀_comp (G : C' ⥤ C) (T : C') :
    ComposableArrows.mk₀ T ⋙ G = ComposableArrows.mk₀ (G.obj T) :=
  ComposableArrows.ext (fun i ↦ by fin_cases i; rfl) (fun i hi ↦ by omega)

theorem mk₁_comp (G : C' ⥤ C) {T T' : C'} (φ : T ⟶ T') :
    ComposableArrows.mk₁ φ ⋙ G = ComposableArrows.mk₁ (G.map φ) :=
  ComposableArrows.ext₁ rfl rfl (by
    change G.map φ = 𝟙 _ ≫ G.map φ ≫ 𝟙 _
    simp)

theorem mk₂_comp (G : C' ⥤ C) {T T' T'' : C'} (φ : T ⟶ T') (ψ : T' ⟶ T'') :
    ComposableArrows.mk₂ φ ψ ⋙ G = ComposableArrows.mk₂ (G.map φ) (G.map ψ) :=
  ComposableArrows.ext (fun i ↦ by fin_cases i <;> rfl) (fun i hi ↦ by
    obtain rfl | rfl : i = 0 ∨ i = 1 := by omega
    · change G.map φ = 𝟙 _ ≫ G.map φ ≫ 𝟙 _
      simp
    · change G.map ψ = 𝟙 _ ≫ G.map ψ ≫ 𝟙 _
      simp)

theorem pull1_bijective (m : CoefMap (RingHom.id R) F F')
    (h : QIsoAt (d0 F) (d1 F) (d0 F') (d1 F') (pullbackOneCochains m)) : Function.Bijective m.pull1 := by
  refine ⟨(injective_iff_map_eq_zero m.pull1).2 fun c hc ↦ ?_, fun c' ↦ ?_⟩
  · obtain ⟨f, rfl⟩ := H1.mk_surjective F c
    rw [CoefMap.pullCohomologyOne_class] at hc
    obtain ⟨g, hg⟩ := H1.mk_eq_zero.1 hc
    have hf : d1 F f.1 = 0 := LinearMap.mem_ker.1 (commAlgFunctorCocyclesOne_eq_ker F ▸ f.2)
    obtain ⟨y, hy⟩ := h.1 f.1 hf ⟨g, hg⟩
    exact H1.mk_eq_zero.2 ⟨y, hy⟩
  · obtain ⟨f', rfl⟩ := H1.mk_surjective F' c'
    have hf : d1 F' f'.1 = 0 := LinearMap.mem_ker.1 (commAlgFunctorCocyclesOne_eq_ker F' ▸ f'.2)
    obtain ⟨x, y, hx, hy⟩ := h.2 f'.1 hf
    have hxm : x ∈ Z1 F := by rw [commAlgFunctorCocyclesOne_eq_ker]; exact hx
    refine ⟨H1.mk F ⟨x, hxm⟩, ?_⟩
    rw [CoefMap.pullCohomologyOne_class, H1.mk_eq_mk]
    exact ⟨y, hy.symm⟩

theorem pull2_bijective (m : CoefMap (RingHom.id R) F F')
    (h : QIsoAt (d1 F) (d2 F) (d1 F') (d2 F') (pullbackTwoCochains m)) : Function.Bijective m.pull2 := by
  refine ⟨(injective_iff_map_eq_zero m.pull2).2 fun c hc ↦ ?_, fun c' ↦ ?_⟩
  · obtain ⟨f, rfl⟩ := H2.mk_surjective F c
    rw [CoefMap.pullCohomologyTwo_class] at hc
    obtain ⟨g, hg⟩ := H2.mk_eq_zero.1 hc
    obtain ⟨y, hy⟩ := h.1 f.1 ((mem_Z2_iff _).1 f.2) ⟨g, hg⟩
    exact H2.mk_eq_zero.2 ⟨y, hy⟩
  · obtain ⟨f', rfl⟩ := H2.mk_surjective F' c'
    obtain ⟨x, y, hx, hy⟩ := h.2 f'.1 ((mem_Z2_iff _).1 f'.2)
    refine ⟨H2.mk F ⟨x, (mem_Z2_iff _).2 hx⟩, ?_⟩
    rw [CoefMap.pullCohomologyTwo_class, H2.mk_eq_mk]
    exact ⟨y, hy.symm⟩

theorem pullbackZeroCochains_algebraMap (m : CoefMap (RingHom.id R) F F') (r : R) :
    pullbackZeroCochains m (algebraMap R (C0 F) r) = algebraMap R (C0 F') r := by
  funext T
  change m.α T (algebraMap R _ r) = algebraMap R _ r
  rw [Algebra.algebraMap_eq_smul_one, m.smul, map_one, Algebra.algebraMap_eq_smul_one]
  rfl

theorem d0_algebraMap (r : R) : d0 F (algebraMap R (C0 F) r) = 0 := by
  funext T T' φ
  rw [amitsur_d0_apply]
  change algebraMap R _ r - mp F φ (algebraMap R _ r) = 0
  rw [AlgHom.commutes, sub_self]

theorem d0_pullbackZeroCochains (m : CoefMap (RingHom.id R) F F') (g : C0 F) :
    d0 F' (pullbackZeroCochains m g) = pullbackOneCochains m (d0 F g) := by
  funext T T' φ
  change m.α T' (g _) - mp F' φ (m.α T (g _)) = m.α T' (g _ - mp F (m.G.map φ) (g _))
  rw [map_sub, m.naturality]

theorem stein_iff (m : CoefMap (RingHom.id R) F F')
    (h : QIsoAt (0 : R →ₗ[R] C0 F) (d0 F) (0 : R →ₗ[R] C0 F') (d0 F') (pullbackZeroCochains m)) :
    Stein F ↔ Stein F' := by
  have hk : ∀ x, d0 F x = 0 → pullbackZeroCochains m x = 0 → x = 0 := fun x hx hp ↦ by
    obtain ⟨y, hy⟩ := h.1 x hx ⟨0, by rw [hp]; rfl⟩
    exact hy.symm
  have hs : ∀ z, d0 F' z = 0 → ∃ x, d0 F x = 0 ∧ pullbackZeroCochains m x = z := fun z hz ↦ by
    obtain ⟨x, y, hx, hy⟩ := h.2 z hz
    exact ⟨x, hx, sub_eq_zero.1 hy⟩
  constructor
  · rintro ⟨he, hi⟩
    refine ⟨fun y ↦ ⟨fun hy ↦ ?_, ?_⟩, fun r r' hr ↦ hi ?_⟩
    · obtain ⟨x, hx, rfl⟩ := hs y hy
      obtain ⟨r, rfl⟩ := (he x).1 hx
      exact ⟨r, (pullbackZeroCochains_algebraMap m r).symm⟩
    · rintro ⟨r, rfl⟩
      exact d0_algebraMap r
    · rw [← sub_eq_zero, ← map_sub]
      refine hk _ (d0_algebraMap _) ?_
      rw [pullbackZeroCochains_algebraMap, map_sub, hr, sub_self]
  · rintro ⟨he, hi⟩
    refine ⟨fun y ↦ ⟨fun hy ↦ ?_, ?_⟩, fun r r' hr ↦ hi ?_⟩
    · have h0 : d0 F' (pullbackZeroCochains m y) = 0 := by rw [d0_pullbackZeroCochains, hy, map_zero]
      obtain ⟨r, hr⟩ := (he _).1 h0
      refine ⟨r, ?_⟩
      have hr' : algebraMap R (C0 F') r = pullbackZeroCochains m y := hr
      have e : y - algebraMap R (C0 F) r = 0 := hk _ (by rw [map_sub, hy, d0_algebraMap, sub_self])
        (by rw [map_sub, pullbackZeroCochains_algebraMap, hr', sub_self])
      exact (sub_eq_zero.1 e).symm
    · rintro ⟨r, rfl⟩
      exact d0_algebraMap r
    · rw [← pullbackZeroCochains_algebraMap m, ← pullbackZeroCochains_algebraMap m, hr]

end

theorem lowSt_of_dictSt : DictSt → LowSt := by
  intro hD R _ C C' _ _ F F' m hQ
  obtain ⟨e₀, e₁, e₂, e₃, v₀, v₁, v₂, v₃, c₀, c₁, c₂⟩ := hD R C F
  obtain ⟨e₀', e₁', e₂', e₃', v₀', v₁', v₂', v₃', c₀', c₁', c₂'⟩ := hD R C' F'
  have p0 : ∀ f, e₀' (pulln m 0 f) = pullbackZeroCochains m (e₀ f) := fun f ↦ by
    funext T
    rw [v₀']
    change m.α T (f (ComposableArrows.mk₀ T ⋙ m.G)) = m.α T (e₀ f (m.G.obj T))
    rw [v₀]
    exact congrArg (m.α T) (eq_of_heq (cn_heq f (mk₀_comp m.G T)))
  have p1 : ∀ f, e₁' (pulln m 1 f) = pullbackOneCochains m (e₁ f) := fun f ↦ by
    funext T T' φ
    rw [v₁']
    change m.α T' (f (ComposableArrows.mk₁ φ ⋙ m.G)) = m.α T' (e₁ f _ _ (m.G.map φ))
    rw [v₁]
    exact congrArg (m.α T') (eq_of_heq (cn_heq f (mk₁_comp m.G φ)))
  have p2 : ∀ f, e₂' (pulln m 2 f) = pullbackTwoCochains m (e₂ f) := fun f ↦ by
    funext T T' T'' φ ψ
    rw [v₂']
    change m.α T'' (f (ComposableArrows.mk₂ φ ψ ⋙ m.G)) = m.α T'' (e₂ f _ _ _ (m.G.map φ) (m.G.map ψ))
    rw [v₂]
    exact congrArg (m.α T'') (eq_of_heq (cn_heq f (mk₂_comp m.G φ ψ)))
  refine ⟨pull1_bijective m ?_, pull2_bijective m ?_, stein_iff m ?_⟩
  · exact qIsoAt_transport e₀ e₁ e₂ e₀' e₁' e₂' c₀ c₁ c₀' c₁' p1 (hQ.2 0)
  · exact qIsoAt_transport e₁ e₂ e₃ e₁' e₂' e₃' c₁ c₂ c₁' c₂' p2 (hQ.2 1)
  · exact qIsoAt_transport (LinearEquiv.refl R R) e₀ e₁ (LinearEquiv.refl R R) e₀' e₁'
      (fun _ ↦ map_zero _) c₀ (fun _ ↦ map_zero _) c₀' p0 hQ.1

end GlobalTheory.CompanionTheory.HodgeLow
