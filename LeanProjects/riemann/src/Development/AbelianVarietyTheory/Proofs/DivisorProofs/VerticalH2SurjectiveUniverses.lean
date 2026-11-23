import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PullbackBijectiveDegreesOneTwo
open CategoryTheory GlobalTheory.CxCoh

set_option autoImplicit false
namespace GlobalTheory.CxCoh.VertSurjTwo
universe a b
variable {C' : Type b} [Category.{0} C']

theorem core {L L' : Cx C'} (a0 : ∀ T, L.M0.obj T →+ L'.M0.obj T) (a1 : ∀ T, L.M1.obj T →+ L'.M1.obj T)
    (a2 : ∀ T, L.M2.obj T →+ L'.M2.obj T)
    (a0m : ∀ {T T' : C'} (φ : T ⟶ T') x, a0 T' (L.M0.map φ x) = L'.M0.map φ (a0 T x))
    (a1m : ∀ {T T' : C'} (φ : T ⟶ T') x, a1 T' (L.M1.map φ x) = L'.M1.map φ (a1 T x))
    (a2m : ∀ {T T' : C'} (φ : T ⟶ T') x, a2 T' (L.M2.map φ x) = L'.M2.map φ (a2 T x))
    (ad0 : ∀ T x, a1 T (L.d0 T x) = L'.d0 T (a0 T x)) (ad1 : ∀ T x, a2 T (L.d1 T x) = L'.d1 T (a1 T x))
    (hq : ∀ T, IsQ (L.d0 T) (L.d1 T) (L.d2 T) (L'.d0 T) (L'.d1 T) (L'.d2 T) (a0 T) (a1 T) (a2 T))
    (c' : L'.T2) (hc' : c' ∈ L'.Z2) :
    ∃ c ∈ L.Z2, ∃ g : L'.T1, c' = ((fun T T' T'' φ ψ ↦ a0 T'' (c.1 T T' T'' φ ψ)),
      (fun T T' φ ↦ a1 T' (c.2.1 T T' φ)), fun T ↦ a2 T (c.2.2 T)) + L'.D1 g := by
  obtain ⟨z', α', η'⟩ := c'
  obtain ⟨hz, hα, hη, hd⟩ := hc'
  simp only at hz hα hη hd
  choose η w hη0 hηw using fun T ↦ (hq T).surj2 (η' T) (hd T)
  have key2 : ∀ (T T' : C') (φ : T ⟶ T'), a2 T' (η T' - L.M2.map φ (η T)) =
      L'.d1 T' (α' T T' φ + L'.M1.map φ (w T) - w T') := by
    intro T T' φ
    have h := hη T T' φ
    rw [hηw T', hηw T] at h
    simp only [map_sub, map_add, a2m, ← L'.diffOne_natural] at h ⊢
    linear_combination (norm := abel1) h
  have cl2 : ∀ (T T' : C') (φ : T ⟶ T'), L.d2 T' (η T' - L.M2.map φ (η T)) = 0 := by
    intro T T' φ
    rw [map_sub, L.diffTwo_natural, hη0, hη0, map_zero, sub_zero]
  choose α₁ hα₁ using fun T T' φ ↦ (hq T').inj2 _ _ (cl2 T T' φ) (key2 T T' φ)

  have cl1 : ∀ (T T' : C') (φ : T ⟶ T'),
      L'.d1 T' (α' T T' φ + L'.M1.map φ (w T) - w T' - a1 T' (α₁ T T' φ)) = 0 := by
    intro T T' φ
    rw [map_sub (L'.d1 T'), ← key2, ← ad1, hα₁, sub_self]
  choose α₂ f hα₂0 hα₂ using fun T T' φ ↦ (hq T').surj1 _ (cl1 T T' φ)
  obtain ⟨α, hA, hB⟩ : ∃ α : L.M1.c1, (∀ (T T' : C') (φ : T ⟶ T'), L.d1 T' (α T T' φ) = η T' - L.M2.map φ (η T)) ∧
      ∀ (T T' : C') (φ : T ⟶ T'), α' T T' φ + L'.M1.map φ (w T) - w T' = a1 T' (α T T' φ) + L'.d0 T' (f T T' φ) := by
    refine ⟨fun T T' φ ↦ α₁ T T' φ + α₂ T T' φ, fun T T' φ ↦ ?_, fun T T' φ ↦ ?_⟩
    · simp only [map_add, hα₁, hα₂0, add_zero]
    · have h := hα₂ T T' φ
      simp only [map_add]
      linear_combination (norm := abel1) h
  have clβ : ∀ (T T' T'' : C') (φ : T ⟶ T') (ψ : T' ⟶ T''),
      L.d1 T'' (α T T'' (φ ≫ ψ) - L.M1.map ψ (α T T' φ) - α T' T'' ψ) = 0 := by
    intro T T' T'' φ ψ
    simp only [map_sub, hA, L.diffOne_natural, L.M2.map_comp]
    abel
  have keyβ : ∀ (T T' T'' : C') (φ : T ⟶ T') (ψ : T' ⟶ T''),
      a1 T'' (α T T'' (φ ≫ ψ) - L.M1.map ψ (α T T' φ) - α T' T'' ψ) =
        L'.d0 T'' (z' T T' T'' φ ψ + (L'.M0.map ψ (f T T' φ) - f T T'' (φ ≫ ψ) + f T' T'' ψ)) := by
    intro T T' T'' φ ψ
    have e1 := hB T T'' (φ ≫ ψ)
    have e2 := congrArg (L'.M1.map ψ) (hB T T' φ)
    have e3 := hB T' T'' ψ
    have h := hα T T' T'' φ ψ
    simp only [map_add, map_sub, ← L'.M1.map_comp, ← L'.diffZero_natural] at e2
    simp only [map_add, map_sub, a1m]
    linear_combination (norm := abel1) e2 + e3 + h - e1
  choose z₁ hz₁ using fun T T' T'' φ ψ ↦ (hq T'').inj1 _ _ (clβ T T' T'' φ ψ) (keyβ T T' T'' φ ψ)
  have cl0 : ∀ (T T' T'' : C') (φ : T ⟶ T') (ψ : T' ⟶ T''),
      L'.d0 T'' (z' T T' T'' φ ψ + (L'.M0.map ψ (f T T' φ) - f T T'' (φ ≫ ψ) + f T' T'' ψ) -
        a0 T'' (z₁ T T' T'' φ ψ)) = 0 := by
    intro T T' T'' φ ψ
    rw [map_sub (L'.d0 T''), ← keyβ, ← ad0, hz₁, sub_self]
  choose z₂ hz₂0 hz₂ using fun T T' T'' φ ψ ↦ (hq T'').surj0 _ (cl0 T T' T'' φ ψ)
  obtain ⟨z, hzd, hza⟩ : ∃ z : L.M0.c2, (∀ (T T' T'' : C') (φ : T ⟶ T') (ψ : T' ⟶ T''),
      L.d0 T'' (z T T' T'' φ ψ) = α T T'' (φ ≫ ψ) - L.M1.map ψ (α T T' φ) - α T' T'' ψ) ∧
      ∀ (T T' T'' : C') (φ : T ⟶ T') (ψ : T' ⟶ T''),
      a0 T'' (z T T' T'' φ ψ) = z' T T' T'' φ ψ + (L'.M0.map ψ (f T T' φ) - f T T'' (φ ≫ ψ) + f T' T'' ψ) := by
    refine ⟨fun T T' T'' φ ψ ↦ z₁ T T' T'' φ ψ + z₂ T T' T'' φ ψ, fun T T' T'' φ ψ ↦ ?_, fun T T' T'' φ ψ ↦ ?_⟩
    · simp only [map_add, hz₁, hz₂0, add_zero]
    · simp only [map_add, hz₂]
      abel
  have hzc : ∀ (T T' T'' T''' : C') (φ : T ⟶ T') (ψ : T' ⟶ T'') (χ : T'' ⟶ T'''),
      L.M0.map χ (z T T' T'' φ ψ) + z T T'' T''' (φ ≫ ψ) χ = z T T' T''' φ (ψ ≫ χ) + z T' T'' T''' ψ χ := by
    intro T T' T'' T''' φ ψ χ
    refine sub_eq_zero.mp ((hq T''').inj0 _ ?_ ?_)
    · simp only [map_sub, map_add, L.diffZero_natural, hzd, L.M1.map_comp, Category.assoc]
      abel
    · have h := hz T T' T'' T''' φ ψ χ
      simp only [map_sub, map_add, a0m, hza, ← L'.M0.map_comp, Category.assoc]
      linear_combination (norm := abel1) h
  refine ⟨(z, α, η), ⟨hzc, fun T T' T'' φ ψ ↦ ?_, fun T T' φ ↦ ?_, hη0⟩, (-f, w), ?_⟩
  · show α T T'' (φ ≫ ψ) = L.M1.map ψ (α T T' φ) + α T' T'' ψ + L.d0 T'' (z T T' T'' φ ψ)
    rw [hzd]; abel
  · show η T' = L.M2.map φ (η T) + L.d1 T' (α T T' φ)
    rw [hA]; abel
  · refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · funext T T' T'' φ ψ
      simp [Cx.D1, hza]
      abel
    · funext T T' φ
      have h := hB T T' φ
      simp [Cx.D1]
      linear_combination (norm := abel1) h
    · funext T
      simp [Cx.D1, hηw T]

theorem vertical_h2_surjective {C : Type a} [Category.{0} C] {K : Cx C} {K' : Cx C'} (m : CxMap K K')
    (hq : m.QAll) : Function.Surjective m.vert.h2 := by
  intro y
  obtain ⟨⟨c', hc'⟩, rfl⟩ := QuotientAddGroup.mk_surjective y
  obtain ⟨c, hc, g, hg⟩ := core (L := K.res m.G) m.a0 m.a1 m.a2 m.compDegreeZero_natural m.compDegreeOne_natural m.compDegreeTwo_natural m.comp_commutes_diffZero m.comp_commutes_diffOne hq c' hc'
  refine ⟨QuotientAddGroup.mk ⟨c, hc⟩, ?_⟩
  rw [CxMap.h2, QuotientAddGroup.map_mk, QuotientAddGroup.eq]
  refine ⟨g, ?_⟩
  show K'.D1 g = -(m.vert.p2 c) + c'
  rw [hg]
  show K'.D1 g = -(m.vert.p2 c) + (m.vert.p2 c + K'.D1 g)
  abel

theorem main.{a', b'} : VertHas.{a', b'} (fun m ↦ Function.Surjective m.h2) :=
  fun m hq ↦ vertical_h2_surjective m hq

theorem inst : VertHas.{1,1} (fun m ↦ Function.Surjective m.h2) ∧
    VertHas.{1,0} (fun m ↦ Function.Surjective m.h2) ∧ VertHas.{0,0} (fun m ↦ Function.Surjective m.h2) :=
  ⟨main, main, main⟩

end GlobalTheory.CxCoh.VertSurjTwo
