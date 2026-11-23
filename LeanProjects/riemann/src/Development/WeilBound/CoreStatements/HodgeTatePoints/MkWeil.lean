import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GenWeil
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHTFormOver
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPushEquiv

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace PositivityTheory.HtPt.Mk

theorem epi_fieldMap {Ω K : Type} [Field Ω] [Field K] (a : Ω →+* K) : Epi (Spec.map (CommRingCat.ofHom a)) := by
  have : Flat (Spec.map (CommRingCat.ofHom a)) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    let _ := a.toAlgebra
    exact (inferInstance : Module.Flat Ω K)
  have : Surjective (Spec.map (CommRingCat.ofHom a)) :=
    ⟨fun z => ⟨IsLocalRing.closedPoint K, Subsingleton.elim (α := PrimeSpectrum Ω) _ _⟩⟩
  exact Flat.epi_of_flat_of_surjective _

theorem spec_map_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    Spec.map (CommRingCat.ofHom (g.comp f)) = Spec.map (CommRingCat.ofHom g) ≫ Spec.map (CommRingCat.ofHom f) := by
  rw [CommRingCat.ofHom_comp, Spec.map_comp]

theorem card_char_le (T K : Type) [Group T] [Finite T] [Field K] :
    Finite (T →* Kˣ) ∧ Nat.card (T →* Kˣ) ≤ Nat.card T := by
  classical
  have := Fintype.ofFinite T
  have hinj : Function.Injective (fun χ : T →* Kˣ => (Units.coeHom K).comp χ) := fun a b h =>
    MonoidHom.ext fun t => Units.ext (DFunLike.congr_fun h t)
  have hli := (linearIndependent_monoidHom T K).comp _ hinj
  have hf : Finite (T →* Kˣ) := hli.finite
  refine ⟨hf, ?_⟩
  have := Fintype.ofFinite (T →* Kˣ)
  have h := hli.fintype_card_le_finrank
  rw [Module.finrank_fintype_fun_eq_card] at h
  rwa [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]

theorem char_descend {T K K' : Type} [Group T] [Finite T] [Field K] [Field K'] (i : K →+* K')
    (hsep : ∀ t : T, (∀ χ : T →* Kˣ, χ t = 1) → t = 1) (χ' : T →* K'ˣ) :
    ∃ χ : T →* Kˣ, ∀ t, (χ' t : K') = i (χ t) := by
  obtain ⟨h1, -⟩ := card_char_le T K
  obtain ⟨h2, c2⟩ := card_char_le T K'
  obtain ⟨h3, c3⟩ := card_char_le (T →* Kˣ) K
  let ev : T →* ((T →* Kˣ) →* Kˣ) := MonoidHom.mk' (fun t => MonoidHom.mk' (fun χ => χ t) fun _ _ => rfl)
    fun a b => MonoidHom.ext fun χ => map_mul χ a b
  have hev : Function.Injective ev := (injective_iff_map_eq_one ev).2 fun t h =>
    hsep t fun χ => DFunLike.congr_fun h χ
  have c4 := Nat.card_le_card_of_injective _ hev
  let m : (T →* Kˣ) → (T →* K'ˣ) := fun χ => (Units.map i.toMonoidHom).comp χ
  have hm : Function.Injective m := fun a b h =>
    MonoidHom.ext fun t => Units.ext (i.injective (congrArg Units.val (DFunLike.congr_fun h t)))
  have hb := hm.bijective_of_nat_card_le (c2.trans (c4.trans c3))
  obtain ⟨χ, rfl⟩ := hb.2 χ'
  exact ⟨χ, fun t => rfl⟩

theorem ht_weil_pull : ∀ (X X' : Scheme.{0}) (Ω Ω' : Type) [Field Ω] [Field Ω'] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (ξ' : Spec (CommRingCat.of Ω') ⟶ X') (f : X' ⟶ X) (i : Ω →+* Ω'), GlobalTheory.CompanionTheory.Ar.Dominates ξ' ξ f i → ∀ (G : Over X) [GrpObj G] [IsCommMonObj G] (G' : Over X') [GrpObj G'] (φ : G'.left ⟶ G.left), IsGrpPullback G' G f φ → ∀ (L : LB G.left) (L' : LB G'.left), L.IsLB → L'.IsLB → LBIso L' (L.pull φ) → ∀ n : ℕ, FullTorsion G ξ n → FullTorsion G' ξ' n ∧ ∀ e, GenWeil G L ξ n e → ∃ e', GenWeil G' L' ξ' n e' ∧ ∀ (x g : Over.mk ξ ⟶ G) (x' g' : Over.mk ξ' ⟶ G'), x ^ n = 1 → g ^ n = 1 → x'.left ≫ φ = spMap i ≫ x.left → g'.left ≫ φ = spMap i ≫ g.left → (e' x' g' : Ω') = i (e x g) := by
  intro X X' Ω Ω' _ _ ξ ξ' f i hd G _ _ G' _ φ hp L L' hL hL' hw n hF
  have hd' : spMap i ≫ ξ = ξ' ≫ f := hd.symm
  have hsp : ∀ {k : Type} [Field k] (a : Ω' →+* k), spMap (a.comp i) = spMap a ≫ spMap i := fun a =>
    spec_map_comp i a
  have hdk : ∀ {k : Type} [Field k] (a : Ω' →+* k), spMap (a.comp i) ≫ ξ = (spMap a ≫ ξ') ≫ f := fun a => by
    rw [hsp, Category.assoc, hd', Category.assoc]
  obtain ⟨E, hE⟩ := GlobalTheory.LiePull.exists_pushEquiv hp (Over.mk ξ') (spMap i ≫ ξ) hd'
  let ψ : Over.mk (spMap i ≫ ξ) ⟶ Over.mk ξ := Over.homMk (spMap i) rfl
  let inc : (Over.mk ξ ⟶ G) →* (Over.mk ξ' ⟶ G') :=
    E.symm.toMonoidHom.comp (MonoidHom.mk' (fun x => ψ ≫ x) fun x y => MonObj.comp_mul ψ x y)
  have hinc : ∀ x, (inc x).left ≫ φ = spMap i ≫ x.left := fun x => by
    rw [← hE]
    exact congrArg (·.left) (E.apply_symm_apply (ψ ≫ x))
  have hext : ∀ {T : Over X'} (a b : T ⟶ G'), a.left ≫ φ = b.left ≫ φ → a = b := fun a b h =>
    Over.OverMorphism.ext (hp.1.hom_ext h ((Over.w a).trans (Over.w b).symm))
  have hepi := epi_fieldMap i
  have hinj : Function.Injective inc := fun a b h => Over.OverMorphism.ext
    ((cancel_epi (spMap i)).1 (by rw [← hinc, ← hinc, h]))
  have hsurj : ∀ x', x' ^ n = 1 → ∃ x, x ^ n = 1 ∧ inc x = x' := fun x' hx' => by
    obtain ⟨x, hx⟩ := hF Ω' i (E x') (by rw [← map_pow, hx', map_one])
    have e : inc x = x' := hext _ _ (by rw [hinc, ← hx, hE])
    exact ⟨x, hinj (by rw [map_pow, e, hx', map_one]), e⟩
  have hpow : ∀ x, x ^ n = 1 → inc x ^ n = 1 := fun x hx => by rw [← map_pow, hx, map_one]
  refine ⟨fun k _ a g hg => ?_, fun e hW => ?_⟩
  · obtain ⟨Ek, hEk⟩ := GlobalTheory.LiePull.exists_pushEquiv hp (Over.mk (spMap a ≫ ξ')) (spMap (a.comp i) ≫ ξ) (hdk a)
    obtain ⟨x, hx⟩ := hF k (a.comp i) (Ek g) (by rw [← map_pow, hg, map_one])
    refine ⟨inc x, hp.1.hom_ext ?_ ?_⟩
    · rw [← hEk, hx, Category.assoc, hinc, hsp, Category.assoc]
    · rw [Category.assoc, Over.w, Over.w]; rfl
  let r := Function.invFun inc
  have hr : ∀ x, r (inc x) = x := Function.leftInverse_invFun hinj
  refine ⟨fun x' g' => Units.map i.toMonoidHom (e (r x') (r g')), ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · have := hW.finite
    refine Finite.of_surjective (fun x : {x : Over.mk ξ ⟶ G // x ^ n = 1} => (⟨inc x, hpow _ x.2⟩ :
      {x : Over.mk ξ' ⟶ G' // x ^ n = 1})) fun x' => ?_
    obtain ⟨x, hx, e⟩ := hsurj _ x'.2
    exact ⟨⟨x, hx⟩, Subtype.ext e⟩
  · intro x y g hx hy hg
    obtain ⟨x, hx₀, rfl⟩ := hsurj x hx
    replace hx := hx₀
    obtain ⟨y, hy₀, rfl⟩ := hsurj y hy
    replace hy := hy₀
    obtain ⟨g, hg₀, rfl⟩ := hsurj g hg
    replace hg := hg₀
    simp only [← map_mul, hr]
    rw [hW.mul_left x y g hx hy hg]
  · intro x y g hx hy hg
    obtain ⟨x, hx₀, rfl⟩ := hsurj x hx
    replace hx := hx₀
    obtain ⟨y, hy₀, rfl⟩ := hsurj y hy
    replace hy := hy₀
    obtain ⟨g, hg₀, rfl⟩ := hsurj g hg
    replace hg := hg₀
    simp only [← map_mul, hr]
    rw [hW.mul_right x y g hx hy hg]
  · intro χ' hχ'
    let T : Subgroup (Over.mk ξ ⟶ G) := (powMonoidHom n : (Over.mk ξ ⟶ G) →* (Over.mk ξ ⟶ G)).ker
    have hT : ∀ t : T, t.1 ^ n = 1 := fun t => t.2
    have : Finite T := hW.finite
    obtain ⟨χ, hχ⟩ := char_descend (T := T) i (fun t ht => Subtype.ext (hW.nondeg t.1 (hT t) fun x hx =>
        ht (MonoidHom.mk' (fun s => e x s.1) fun s s' => hW.mul_right x _ _ hx (hT s) (hT s'))))
      (MonoidHom.mk' (fun t => χ' (inc t.1)) fun s t => by
        rw [← hχ' _ _ (hpow _ (hT s)) (hpow _ (hT t)), ← map_mul]; rfl)
    classical
    obtain ⟨x, hx, hxe⟩ := hW.perfect (fun g => if h : g ^ n = 1 then χ ⟨g, h⟩ else 1) fun g g' hg hg' => by
      have hgg : (g * g') ^ n = 1 := by rw [mul_pow, hg, hg', _root_.one_mul]
      rw [dif_pos hg, dif_pos hg', dif_pos hgg, ← map_mul]; rfl
    refine ⟨inc x, hpow x hx, fun g hg => ?_⟩
    obtain ⟨g, hg₀, rfl⟩ := hsurj g hg
    replace hg := hg₀
    have h1 := hxe g hg
    rw [dif_pos hg] at h1
    rw [hr, hr, ← h1]
    exact Units.ext (hχ ⟨g, hg⟩)
  · intro g hg h
    obtain ⟨g, hg₀, rfl⟩ := hsurj g hg
    replace hg := hg₀
    rw [hW.nondeg g hg fun x hx => ?_, map_one]
    have h1 := congrArg Units.val (h (inc x) (hpow x hx))
    rw [hr, hr] at h1
    exact Units.ext (i.injective (h1.trans (map_one i).symm))
  · intro x g hx hg k _ _ a xk gk c hxk hgk
    obtain ⟨x, hx₀, rfl⟩ := hsurj x hx
    replace hx := hx₀
    obtain ⟨g, hg₀, rfl⟩ := hsurj g hg
    replace hg := hg₀
    rw [hr, hr]
    obtain ⟨Ek, hEk⟩ := GlobalTheory.LiePull.exists_pushEquiv hp (Over.mk (spMap a ≫ ξ')) (spMap (a.comp i) ≫ ξ) (hdk a)
    have key : ∀ (z : Spec (CommRingCat.of k) ⟶ X) (hz : z = (spMap a ≫ ξ') ≫ f) (x₀ g₀ : Over.mk z ⟶ G),
        x₀.left = xk.left ≫ φ → g₀.left = gk.left ≫ φ →
          (Out.WeilIs G' L' n xk gk (unitOn c) ↔ Out.WeilIs G L n x₀ g₀ (unitOn c)) := by
      intro z hz x₀ g₀ h1 h2
      subst hz
      exact GlobalTheory.weilIs_grpPullback_of_comm _ _ G G' f φ L L' hL hL' hp hw _ n xk gk x₀ g₀ _ h1 h2
    rw [key _ (hdk a) (Ek xk) (Ek gk) (hEk _) (hEk _)]
    have hcomp : ∀ (y : Over.mk ξ ⟶ G) (yk : Over.mk (spMap a ≫ ξ') ⟶ G'), yk.left = spMap a ≫ (inc y).left →
        (Ek yk).left = spMap (a.comp i) ≫ y.left := fun y yk h =>
      (hEk yk).trans ((congrArg (· ≫ φ) h).trans ((Category.assoc _ _ _).trans
        ((congrArg (spMap a ≫ ·) (hinc y)).trans ((Category.assoc _ _ _).symm.trans
          (congrArg (· ≫ y.left) (hsp a).symm)))))
    exact hW.weil x g hx hg k (a.comp i) (Ek xk) (Ek gk) c (hcomp x xk hxk) (hcomp g gk hgk)
  · intro x g x' g' _ _ h1 h2
    obtain rfl : inc x = x' := hext _ _ ((hinc x).trans h1.symm)
    obtain rfl : inc g = g' := hext _ _ ((hinc g).trans h2.symm)
    simp only [hr]
    rfl

end PositivityTheory.HtPt.Mk
