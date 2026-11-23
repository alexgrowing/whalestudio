import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TanRel
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPolAVSectionInverseImage
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.DegenerationValuesIntOfAdmissibleBase
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.MBLow.DiscNorm

theorem norm_eq_zpow {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V} (hϖ : Irreducible ϖ)
    {C : Type} [NormedField C] (f : FractionRing V →+* C) (hf : ∀ r : V, ‖f (algebraMap V _ r)‖ ≤ 1)
    {k : FractionRing V} (hk : k ≠ 0) : ∃ n : ℤ, ‖f k‖ = ‖f (algebraMap V _ ϖ)‖ ^ n := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := V) k
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have ha0 : a ≠ 0 := by rintro rfl; simp at hk
  set g : V →+* C := f.comp (algebraMap V _)
  have key : ∀ x : V, x ≠ 0 → ∃ m : ℕ, ‖g x‖ = ‖g ϖ‖ ^ m := fun x hx => by
    obtain ⟨m, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx hϖ
    refine ⟨m, ?_⟩
    rw [map_mul, norm_mul, map_pow, norm_pow, GlobalTheory.Ex.IntVal.norm_unit g hf u.isUnit, _root_.one_mul]
  obtain ⟨ma, ea⟩ := key a ha0
  obtain ⟨mb, eb⟩ := key b hb0
  have ht : ‖g ϖ‖ ≠ 0 := by
    rw [norm_ne_zero_iff]
    intro h
    exact hϖ.ne_zero (IsFractionRing.injective V (FractionRing V) (f.injective (by simpa [g] using h)))
  refine ⟨(ma : ℤ) - mb, ?_⟩
  show ‖f (algebraMap V _ a / algebraMap V _ b)‖ = ‖g ϖ‖ ^ ((ma : ℤ) - mb)
  rw [map_div₀, norm_div]
  show ‖g a‖ / ‖g b‖ = _
  rw [zpow_sub₀ ht, zpow_natCast, zpow_natCast]
  exact congrArg₂ (· / ·) ea eb

theorem vF_eq_alg {R : Type} [CommRing R] [IsDomain R] {F : Type} [Field F] [Algebra (FractionRing R) F]
    {X : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → ((TK R).left ⟶ X)} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb L φ ε)) (J : (Sp F ⟶ X) → L.ι)
    (hW : ⊤ ≤ jFK (R := R) F ⁻¹ᵁ LB.wchart L φ (fun k => J (jFK (R := R) F ≫ φ k))) :
    ∃ k : FractionRing R, k ≠ 0 ∧ vF t (jFK (R := R) F) J = algebraMap (FractionRing R) F k := by
  set W := LB.wchart L φ (fun k => J (jFK (R := R) F ≫ φ k))
  have h' : ⊤ ≤ (𝟙 (TK R).left) ⁻¹ᵁ W := by
    intro x _
    obtain ⟨y⟩ : Nonempty (Sp F) := inferInstance
    have hy := hW (Set.mem_univ y)
    have hs : Subsingleton (PrimeSpectrum (FractionRing R)) := inferInstance
    have : (jFK (R := R) F).base y = x := @Subsingleton.elim (PrimeSpectrum (FractionRing R)) hs _ _
    rw [← this]; exact hy
  refine ⟨GlobalTheory.Ex.IntVal.evR (𝟙 _) W h' (t.s _).val, ?_, ?_⟩
  · exact ((Units.isUnit _).map _).ne_zero
  · have := GlobalTheory.Ex.IntVal.valF_comp (algebraMap (FractionRing R) F) (𝟙 (TK R).left) W h' (t.s _).val
    have e : spMap (algebraMap (FractionRing R) F) ≫ 𝟙 (TK R).left = jFK (R := R) F := Category.comp_id _
    rw [e] at this
    exact this

theorem main : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V), Irreducible ϖ → ∀ (D : DegData V (IsLocalRing.maximalIdeal V)) (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [Algebra (FractionRing V) C], CExt V (IsLocalRing.maximalIdeal V) C → ∀ (N : NumD C) (ν : NumOf D.toPre C N), ν.IntN → ‖ν.rg‖ = 1 ∧ ∀ χ, ∃ n : ℤ, ‖(N.ψ χ : C)‖ = ‖toF V C ϖ‖ ^ n := by
  intro V _ _ _ ϖ hϖ D C _ _ _ hC N ν hν
  obtain ⟨S, hS, hI⟩ := hν
  let f : V →+* C := toF V C
  let g : V →+* S := f.codRestrict S fun x => (hS _).2 (hC.1 x)
  have hg : spMap S.subtype ≫ spMap g = (TF (R := V) C).hom := by
    show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp]; rfl
  have hrig : ‖ν.rg‖ = 1 := GlobalTheory.Ex.IntVal.norm_vF hS hI _ _ (spMap g) hg fun _ =>
      (congrArg ((TF (R := V) C).hom ≫ ·) (Over.w η[D.toPre.P.A])).trans (Category.comp_id _)
  refine ⟨hrig, fun χ => ?_⟩
  have hW : ⊤ ≤ jFK (R := V) C ⁻¹ᵁ LB.wchart D.toPre.P.L (fun _ : PUnit => D.toPre.xK (ν.eX χ))
      (fun _ => ν.J (jFK (R := V) C ≫ D.toPre.xK (ν.eX χ))) := fun y hy => Set.mem_iInter.2 fun _ => ν.good _ hy
  obtain ⟨k, hk, ek⟩ := vF_eq_alg (D.toPre.psi (ν.eX χ)) ν.J hW
  obtain ⟨n, hn⟩ := norm_eq_zpow hϖ (algebraMap (FractionRing V) C) hC.1 hk
  refine ⟨n, ?_⟩
  rw [ν.ψ_eq, norm_mul]
  change _ * ‖ν.rg‖ = _
  rw [hrig, _root_.mul_one, ek, hn]
  rfl

end GlobalTheory.MBLow.DiscNorm
