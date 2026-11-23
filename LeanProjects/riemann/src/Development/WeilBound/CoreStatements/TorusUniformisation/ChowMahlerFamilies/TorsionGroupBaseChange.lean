import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsLatFamilyCongr

open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

namespace PositivityTheory.Xgn.TorsionGroupBaseChange

theorem pow_congr {S Y : Scheme.{0}} {G : Over S} [GrpObj G] {f f' : Y ⟶ S} (h : f = f') (N : ℕ)
    (g : Over.mk f ⟶ G) (g' : Over.mk f' ⟶ G) (hg : g.left = g'.left) : g ^ N = 1 ↔ g' ^ N = 1 := by
  subst h
  have : g = g' := Over.OverMorphism.ext hg
  rw [this]

theorem mul_congr {S Y : Scheme.{0}} {G : Over S} [GrpObj G] {f f' : Y ⟶ S} (h : f = f')
    (u v : Over.mk f ⟶ G) (u' v' : Over.mk f' ⟶ G) (hu : u.left = u'.left) (hv : v.left = v'.left) :
    (u * v).left = (u' * v').left := by
  subst h
  have h1 : u = u' := Over.OverMorphism.ext hu
  have h2 : v = v' := Over.OverMorphism.ext hv
  rw [h1, h2]

def Kill {S Y : Scheme.{0}} (G : Over S) [GrpObj G] (N : ℕ) (g : Y ⟶ G.left) : Prop :=
  (Over.homMk g rfl : Over.mk (g ≫ G.hom) ⟶ G) ^ N = 1

theorem kernel' {R : Type} [CommRing R] [IsDomain R] {T : Type} [CommGroup T] {Γ : QFGroup R T}
    {S : Scheme.{0}} {G : Over S} [GrpObj G] {x : Spec (CommRingCat.of R) ⟶ S} {N : ℕ}
    {i : Γ.G.left ⟶ G.left} (h : Γ.IsTorsionAlong G x N i) {Y : Scheme.{0}}
    (b : Y ⟶ Spec (CommRingCat.of R)) (g : Y ⟶ G.left) (hg : g ≫ G.hom = b ≫ x) :
    Kill G N g ↔ ∃ y : Y ⟶ Γ.G.left, y ≫ Γ.G.hom = b ∧ y ≫ i = g := by
  unfold Kill
  constructor
  · intro hk
    let Y' : Over (Spec (CommRingCat.of R)) := Over.mk b
    let g₀ : Over.mk (Y'.hom ≫ x) ⟶ G := Over.homMk g hg
    have hk' : g₀ ^ N = 1 := (pow_congr hg.symm N g₀ (Over.homMk g rfl) rfl).2 hk
    obtain ⟨y, hy⟩ := (h.kernel Y' g₀).1 hk'
    exact ⟨y.left, Over.w y, by simpa [g₀] using hy⟩
  · rintro ⟨y, hy1, hy2⟩
    let Y' : Over (Spec (CommRingCat.of R)) := Over.mk b
    let g₀ : Over.mk (Y'.hom ≫ x) ⟶ G := Over.homMk g hg
    have hk' : g₀ ^ N = 1 :=
      (h.kernel Y' g₀).2 ⟨Over.homMk y hy1, by simpa [g₀] using hy2⟩
    exact (pow_congr hg.symm N g₀ (Over.homMk g rfl) rfl).1 hk'

theorem inj' {R : Type} [CommRing R] [IsDomain R] {T : Type} [CommGroup T] {Γ : QFGroup R T}
    {S : Scheme.{0}} {G : Over S} [GrpObj G] {x : Spec (CommRingCat.of R) ⟶ S} {N : ℕ}
    {i : Γ.G.left ⟶ G.left} (h : Γ.IsTorsionAlong G x N i) {Y : Scheme.{0}}
    (y z : Y ⟶ Γ.G.left) (h1 : y ≫ Γ.G.hom = z ≫ Γ.G.hom) (h2 : y ≫ i = z ≫ i) : y = z := by
  let Y' : Over (Spec (CommRingCat.of R)) := Over.mk (z ≫ Γ.G.hom)
  have := h.inj Y' (Over.homMk y h1) (Over.homMk z rfl) (by simpa using h2)
  simpa using congrArg Over.Hom.left this

end PositivityTheory.Xgn.TorsionGroupBaseChange

open PositivityTheory.Xgn.TorsionGroupBaseChange in
theorem PositivityTheory.Xgn.torsion_group_base_change : ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] [Algebra R R'] (T : Type) [CommGroup T] (Γ : QFGroup R T) (Γ' : QFGroup R' T) (S : Scheme.{0}) (G : Over S) [GrpObj G] (x : Spec (CommRingCat.of R) ⟶ S) (x' : Spec (CommRingCat.of R') ⟶ S), Spec.map (CommRingCat.ofHom (algebraMap R R')) ≫ x = x' → ∀ (N : ℕ) (i : Γ.G.left ⟶ G.left) (i' : Γ'.G.left ⟶ G.left), Γ.IsTorsionAlong G x N i → Γ'.IsTorsionAlong G x' N i' → ∀ (a : FractionRing R →+* FractionRing R'), a.comp (algebraMap R (FractionRing R)) = (algebraMap R' (FractionRing R')).comp (algebraMap R R') → (∀ t, Spec.map (CommRingCat.ofHom a) ≫ (Γ.pt t).left ≫ i = (Γ'.pt t).left ≫ i') → ∃ F : Γ'.G.left ⟶ Γ.G.left, F ≫ i = i' ∧ Γ'.IsBaseChange Γ (algebraMap R R') F := by
  intro R R' _ _ _ _ _ T _ Γ Γ' S G _ x x' hx N i i' h h' a ha hpt
  have hKi' : Kill G N i' := (kernel' h' Γ'.G.hom i' h'.isOver).2 ⟨𝟙 _, by simp, by simp⟩
  have hi'x : i' ≫ G.hom = (Γ'.G.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R R'))) ≫ x := by
    rw [Category.assoc, hx]
    exact h'.isOver
  obtain ⟨F, hF1, hF2⟩ := (kernel' h _ i' hi'x).1 hKi'
  refine ⟨F, hF2, ?_⟩
  have lift : ∀ {Z : Scheme.{0}} (u : Z ⟶ Γ.G.left) (v : Z ⟶ Spec (CommRingCat.of R')),
      u ≫ Γ.G.hom = v ≫ Spec.map (CommRingCat.ofHom (algebraMap R R')) →
      ∃ l : Z ⟶ Γ'.G.left, l ≫ F = u ∧ l ≫ Γ'.G.hom = v := by
    intro Z u v huv
    have hk : Kill G N (u ≫ i) :=
      (kernel' h (u ≫ Γ.G.hom) (u ≫ i) (by simp only [Category.assoc, h.isOver])).2 ⟨u, rfl, rfl⟩
    have hg : (u ≫ i) ≫ G.hom = v ≫ x' := by
      rw [Category.assoc, h.isOver, ← Category.assoc, huv, Category.assoc, hx]
    obtain ⟨l, hl1, hl2⟩ := (kernel' h' v (u ≫ i) hg).1 hk
    refine ⟨l, inj' h _ _ ?_ ?_, hl1⟩
    · rw [Category.assoc, hF1, ← Category.assoc, hl1, huv]
    · rw [Category.assoc, hF2, hl2]
  have uniq : ∀ {Z : Scheme.{0}} (l₁ l₂ : Z ⟶ Γ'.G.left), l₁ ≫ F = l₂ ≫ F →
      l₁ ≫ Γ'.G.hom = l₂ ≫ Γ'.G.hom → l₁ = l₂ := by
    intro Z l₁ l₂ e1 e2
    refine inj' h' _ _ e2 ?_
    rw [← hF2, ← Category.assoc, e1, Category.assoc]
  refine ⟨?_, ?_, ?_⟩
  · refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk hF1
      (fun s => Classical.choose (lift s.fst s.snd s.condition))
      (fun s => (Classical.choose_spec (lift s.fst s.snd s.condition)).1)
      (fun s => (Classical.choose_spec (lift s.fst s.snd s.condition)).2)
      (fun s m h1 h2 => uniq _ _ ?_ ?_))
    · rw [h1, (Classical.choose_spec (lift s.fst s.snd s.condition)).1]
    · rw [h2, (Classical.choose_spec (lift s.fst s.snd s.condition)).2]
  · intro S' u v u₀ v₀ hu hv
    apply inj' h
    · simp only [Category.assoc, hF1, Over.w, Over.w_assoc, Over.mk_hom]
    · let U₀ : Over.mk ((Over.mk (S'.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R R')))).hom ≫ x) ⟶ G :=
        Over.homMk (u₀.left ≫ i) (by simp [h.isOver])
      let V₀ : Over.mk ((Over.mk (S'.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R R')))).hom ≫ x) ⟶ G :=
        Over.homMk (v₀.left ≫ i) (by simp [h.isOver])
      let U₁ : Over.mk (S'.hom ≫ x') ⟶ G := Over.homMk (u.left ≫ i') (by simp [h'.isOver])
      let V₁ : Over.mk (S'.hom ≫ x') ⟶ G := Over.homMk (v.left ≫ i') (by simp [h'.isOver])
      have e0 := h.mul (Over.mk (S'.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R R')))) u₀ v₀ U₀ V₀ rfl rfl
      have e1 := h'.mul S' u v U₁ V₁ rfl rfl
      have e2 : (U₀ * V₀).left = (U₁ * V₁).left :=
        mul_congr (by simp [hx]) U₀ V₀ U₁ V₁ (by simp [U₀, U₁, hu, hF2]) (by simp [V₀, V₁, hv, hF2])
      rw [← e0, e2, e1, Category.assoc, hF2]
  · refine ⟨FractionRing R, inferInstance, algebraMap R (FractionRing R), RingHom.id _, a,
      fun t => (Γ.pt t).left, fun _ _ e => e, RingHom.id_comp _, ha, fun t => ?_, fun t => ?_, fun t => ?_⟩
    · exact Over.w (Γ.pt t)
    · simp
    · apply inj' h
      · simp only [Category.assoc, Over.w, hF1, Over.w_assoc, Over.mk_hom]
        rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, ha]
      · simp only [Category.assoc, hF2]
        exact hpt t
