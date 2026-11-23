import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalFunctionAppOfPreservesGenericPointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMulPowMemCartierMultipleOfRegularLocusStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.Desc

theorem fnOf_app_const {Y Z : Scheme.{0}} [IsIntegral Y] {R₁ : Type} [CommRing R₁] (f : Y ⟶ Z) (c : Z ⟶ Sp R₁)
    (U : Z.Opens) (h : genericPoint Y ∈ f ⁻¹ᵁ U) (r : R₁) :
    fnOf (f ⁻¹ᵁ U) h ((f.app U).hom ((Z.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom
      (c.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R₁)).inv.hom r)))) = GlobalTheory.Desc.cst (f ≫ c) r := by
  have hn := congrArg (fun φ => φ.hom (c.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R₁)).inv.hom r)))
    (f.naturality (homOfLE (le_top : U ≤ ⊤)).op)
  simp only [CommRingCat.comp_apply] at hn
  rw [hn]
  exact fnOf_resG (X := Y) (le_top : f ⁻¹ᵁ U ≤ ⊤) h _

theorem app_surjective_of_factor {R F : Type} [CommRing R] [Field F] {c₀ : R →+* F} {N : ℕ → Set F}
    {P : Scheme.{0}} [IsIntegral P] {p : P ⟶ Sp R} {ψ : P.functionField →+* F} {Dp : ℕ → F → P.Opens}
    (hP : IsModel c₀ N p ψ Dp) {R₁ : Type} [CommRing R₁] {Y Z : Scheme.{0}} [IsIntegral Y] [CompactSpace Y]
    (f : Y ⟶ Z) (a : Z ⟶ P) (c : Z ⟶ Sp R₁) (θ : F →+* Y.functionField) (D₁ : CartierDiv Y)
    (hspan : ∀ k, Sec D₁ k = spanBy (GlobalTheory.Desc.cst (f ≫ c)) (θ '' N k)) (hff : PFF (𝟙 _) (f ≫ a) (θ.comp ψ))
    (k : ℕ) (hk : 1 ≤ k) (b : F) (hb : b ∈ N k) (hloc : ∀ y, (f ≫ a) y ∈ Dp k b ↔ y ∈ locus D₁ k (θ b)) :
    Function.Surjective (f.app (a ⁻¹ᵁ Dp k b)) := by
  intro s
  by_cases hW : genericPoint Y ∈ f ⁻¹ᵁ a ⁻¹ᵁ Dp k b
  swap
  · exact ⟨0, fn_ext fun h => absurd h hW⟩

  have hgen : genericPoint Y ∈ locus D₁ k (θ b) := (hloc _).1 hW
  have hθb0 : θ b ≠ 0 := CartierDiv.GeneratesAt.ne_zero (D := k • D₁) hgen
  have hb0 : b ≠ 0 := fun e => hθb0 (by rw [e, map_zero])
  have hPg : genericPoint P ∈ Dp k b := (hP.gen k hk b hb).2 hb0

  have hreg : ∀ y ∈ locus D₁ k (θ b), RegAt y (fnOf (f ⁻¹ᵁ a ⁻¹ᵁ Dp k b) hW s) :=
    fun y hy => regAt_fnOf (U := f ⁻¹ᵁ a ⁻¹ᵁ Dp k b) (x := y) ((hloc y).2 hy) hW s
  have hbsec : θ b ∈ Sec D₁ k := by
    rw [hspan k]
    exact subset_spanBy _ _ ⟨b, hb, rfl⟩
  obtain ⟨n, hn⟩ := GlobalTheory.T.exists_mul_pow_mem_cartierMultiple_of_regular_locus Y D₁ k (θ b) hbsec _ hreg
  rw [hspan] at hn
  obtain ⟨M, r, t, ht, hsum⟩ := hn
  choose u hu hut using ht

  have hv : ∀ i, ∃ v, (∀ z ∈ Dp k b, RegAt z v) ∧ ψ v = u i / b ^ n :=
    fun i => (hP.ring k hk b hb hb0 (u i / b ^ n)).2 ⟨n, u i, hu i, rfl⟩
  choose v hvreg hvψ using hv
  have hA : ∀ i, ∃ A : Γ(P, Dp k b), fnOf (Dp k b) hPg A = v i := fun i => exists_fnOf_eq hPg (hvreg i)
  choose A hA using hA
  have hterm : ∀ i, fnOf (f ⁻¹ᵁ a ⁻¹ᵁ Dp k b) hW ((f.app (a ⁻¹ᵁ Dp k b)).hom
      ((Z.presheaf.map (homOfLE (le_top : a ⁻¹ᵁ Dp k b ≤ ⊤)).op).hom
        (c.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R₁)).inv.hom (r i))) * (a.app (Dp k b)).hom (A i))) =
      cst (f ≫ c) (r i) * t i / θ b ^ n := by
    intro i
    rw [map_mul, map_mul, fnOf_app_const f c _ hW (r i)]
    have e := GlobalTheory.T.rationalFunction_app_of_preservesGenericPoint P Y (f ≫ a) (θ.comp ψ) hff (Dp k b) hPg hW (A i)
    rw [hA i, RingHom.comp_apply, hvψ i, map_div₀, map_pow, hut i] at e
    rw [mul_div_assoc, ← e]
    rfl
  refine ⟨∑ i, (Z.presheaf.map (homOfLE (le_top : a ⁻¹ᵁ Dp k b ≤ ⊤)).op).hom
      (c.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R₁)).inv.hom (r i))) * (a.app (Dp k b)).hom (A i),
    fnOf_injective _ hW ?_⟩
  rw [map_sum, map_sum]
  simp_rw [hterm]
  rw [← Finset.sum_div, ← hsum, mul_div_assoc, div_self (pow_ne_zero n hθb0), _root_.mul_one]

theorem lift_app_surjective : ∀ (R F : Type) [CommRing R] [IsDomain R] [Field F] (c₀ : R →+* F) (N : ℕ → Set F), GradedFam c₀ N → ∀ (P : Scheme.{0}) [IsIntegral P] (p : P ⟶ Sp R) (ψ : P.functionField →+* F) (Dp : ℕ → F → P.Opens), IsModel c₀ N p ψ Dp → ∀ (R₁ : Type) [CommRing R₁] [IsDomain R₁] (ρ : R →+* R₁), ρ.Flat → Function.Injective c₀ → ∀ (Y : Scheme.{0}) [IsIntegral Y] [CompactSpace Y] [QuasiSeparatedSpace Y] (q : Y ⟶ Sp R₁) (θ : F →+* Y.functionField) (D₁ : CartierDiv Y), θ.comp c₀ = (GlobalTheory.Desc.cst q).comp ρ → LinDisj c₀ (GlobalTheory.Desc.cst q) θ → AmpleDiv D₁ → (∀ k, Sec D₁ k = spanBy (GlobalTheory.Desc.cst q) (θ '' N k)) → ∀ m : Y ⟶ P, PFF (𝟙 _) m (θ.comp ψ) → (∀ k, 1 ≤ k → ∀ b ∈ N k, ∀ y, m y ∈ Dp k b ↔ y ∈ locus D₁ k (θ b)) → ∀ (hm : m ≫ p = q ≫ spMap ρ) (k : ℕ), 1 ≤ k → ∀ b ∈ N k, Function.Surjective ((pullback.lift m q hm).app ((pullback.fst p (spMap ρ)) ⁻¹ᵁ Dp k b)) := by
  intro R F _ _ _ c₀ N _ P _ p ψ Dp hP R₁ _ _ ρ _ _ Y _ _ _ q θ D₁ _ _ _ hspan m hff hloc hm k hk b hb
  have hfc : pullback.lift m q hm ≫ pullback.snd p (spMap ρ) = q := pullback.lift_snd _ _ _
  have hfa : pullback.lift m q hm ≫ pullback.fst p (spMap ρ) = m := pullback.lift_fst _ _ _
  exact app_surjective_of_factor hP (pullback.lift m q hm) (pullback.fst p (spMap ρ)) (pullback.snd p (spMap ρ)) θ D₁
    (by rw [hfc]; exact hspan) (by rw [hfa]; exact hff) k hk b hb (by rw [hfa]; exact hloc k hk b hb)

end GlobalTheory.Desc
