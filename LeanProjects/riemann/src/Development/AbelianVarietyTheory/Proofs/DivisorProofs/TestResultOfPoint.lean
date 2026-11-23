import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsWeilChar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagFramePrimeTangentCompat
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IoOfLeOneIff

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.ArInt GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.Mean4O GlobalTheory.LineNorm GlobalTheory.CoverNorm GlobalTheory.VertForm
open GlobalTheory.HtGen GlobalTheory.TrivFlag GlobalTheory.WholeFlag
open Formalism.MainNotions.DIV.Cons (intO)
open MonObj
open scoped TensorProduct NNReal

namespace GlobalTheory.HalfGeo

attribute [local instance] Over.cartesianMonoidalCategory

open GlobalTheory.LineNorm.Chart GlobalTheory.LieMet

theorem testSt_of_ptSt : PtSt → TestSt := by
  intro hPt E _ _ _ H X _ t hX F _ _ Y V ρ' ρ hρ g f T hind v hp c J hgen U U' hU hU' n n' e e' h h' M M' he he' hd hd'
    hM hM' ε y z yt hz hyt hin hin' hiso ψ₀ hψ₀
  obtain ⟨y, hy⟩ := y
  dsimp only at hz hψ₀ ⊢
  subst hz
  subst hψ₀
  have h1 := ioOf_le_one_iff (resP v) (residueCharacteristic_mem v) ε
  generalize ioOf (resP v) ε = io at h1 hiso ⊢
  let ioO : ε.O →+* intO ℂ_[resP v] := (io.comp ε.O.subtype).codRestrict _ fun b => (h1 b).2 b.2
  have hio : (intO ℂ_[resP v]).subtype.comp ioO = io.comp ε.O.subtype := rfl
  have hmem : ∀ W : V.X.Opens, ⊤ ≤ yt ⁻¹ᵁ W → V.j (below z) ∈ W := fun W hW => by
    have : (spMap ε.O.subtype ≫ yt) (IsLocalRing.closedPoint _) ∈ W := hW (Set.mem_univ _)
    rwa [hyt] at this
  obtain ⟨α, a, hα, ha, hMα⟩ := hM _ (hmem U hin)
  obtain ⟨α', a', hα', ha', hMα'⟩ := hM' _ (hmem U' hin')
  obtain ⟨ψ, hψ⟩ : ∃ ψ : V.G.presheaf.stalk (below z) →+* ℂ_[resP v],
    ψ = io.comp (Scheme.stalkClosedPointTo z).hom := ⟨_, rfl⟩
  obtain ⟨β, hβ, hβα, hb⟩ := GlobalTheory.HtGen.FlagPoint.chart V.j ρ' ε.O io ioO hio z yt hyt hU hin e α hα a _ ha ψ hψ
  obtain ⟨β', hβ', hβα', hb'⟩ := GlobalTheory.HtGen.FlagPoint.chart V.j ρ' ε.O io ioO hio z yt hyt hU' hin' e' α' hα' a' _ ha' ψ hψ
  obtain ⟨φ, hφ⟩ : ∃ φ : Y.X.presheaf.stalk (V.π (below z)) →+* ℂ_[resP v],
    φ = io.comp (Scheme.stalkClosedPointTo (z ≫ V.π)).hom := ⟨_, rfl⟩
  have hφψ : ψ.comp (V.π.stalkMap (below z)).hom = φ := by
    rw [hφ, hψ, Scheme.stalkClosedPointTo_comp]; rfl
  simp only [dual_comp _ ψ, hφψ] at hb hb'
  have hx : spMap φ ≫ GlobalTheory.ShFam.stalkPt Y (V.π (below z)) ≫ ρ =
      spMap (intO ℂ_[resP v]).subtype ≫ (spMap ioO ≫ yt) ≫ ρ' := by
    have e1 : spMap (Scheme.stalkClosedPointTo z).hom ≫ V.G.fromSpecStalk (below z) = z :=
      Scheme.Spec_stalkClosedPointTo_fromSpecStalk z
    have e2 : spMap (V.π.stalkMap (below z)).hom ≫ GlobalTheory.ShFam.stalkPt Y (V.π (below z)) =
        V.G.fromSpecStalk (below z) ≫ V.π := Scheme.SpecMap_stalkMap_fromSpecStalk V.π
    rw [← hφψ, ← spMap_comp', Category.assoc, ← Category.assoc _ _ ρ, e2, Category.assoc, ← hρ, hψ, ← spMap_comp',
      Category.assoc, ← Category.assoc _ (V.G.fromSpecStalk _), e1, Category.assoc,
      ← Category.assoc (spMap (intO ℂ_[resP v]).subtype), spMap_comp', hio, ← spMap_comp', Category.assoc,
      ← Category.assoc _ yt, hyt, Category.assoc]
  have hy0 : spMap (intO ℂ_[resP v]).subtype ≫ spMap ioO ≫ yt = spMap io ≫ z ≫ V.j := by
    rw [← Category.assoc, spMap_comp', hio, ← spMap_comp', Category.assoc, hyt]
  have hB := GlobalTheory.LineNorm.WedgeMax.isTanBasis_map t β he
  have hB' := GlobalTheory.LineNorm.WedgeMax.isTanBasis_map t β' he'
  rw [← Category.assoc, hβ] at hB
  rw [← Category.assoc, hβ'] at hB'
  have hli : LinearIndependent ℂ_[resP v] fun l i => ψ (a l i) :=
    linInd (GlobalTheory.LineNorm.WedgeMax.isTanBasis_map t _ hB).1 hb (hx ▸ hind _ _ φ)
  obtain ⟨k1, k2⟩ := hPt E H X t hX (resP v) ((spMap ioO ≫ yt) ≫ ρ') n n' _ _ hB hB' g
    (fun j => c j (spMap ioO ≫ yt)) J _ _ (hgen _) (hiso _ hy0) (hd β _ hβ) (hd' β' _ hβ') _ _ _ hli hb hb'
  rw [← hx] at k1 k2
  have hval : ∀ r, io (TrueGeo.valAt z (algebraMap (V.G.presheaf.stalk (below z)) V.G.functionField r)) = ψ r :=
    fun r => by rw [hψ, Base.valAt_stalk]; rfl
  have hm : (valMat V M (T (V.π (below z))) z).map io =
      Matrix.of fun r l => ∑ i, ((β (h r i) : intO ℂ_[resP v]) : ℂ_[resP v]) * ψ (a l i) := by
    ext r l
    simp only [Matrix.map_apply, valMat, Matrix.of_apply]
    rw [hMα, hval, map_sum]
    simp only [map_mul, hβα]
  have hm' : (valMat V M' (T (V.π (below z))) z).map io =
      Matrix.of fun r l => ∑ i, ((β' (h' r i) : intO ℂ_[resP v]) : ℂ_[resP v]) * ψ (a' l i) := by
    ext r l
    simp only [Matrix.map_apply, valMat, Matrix.of_apply]
    rw [hMα', hval, map_sum]
    simp only [map_mul, hβα']
  subst hφ
  refine ⟨k1, ?_⟩
  exact (congrArg₂ (fun A B => Clauses (fun b : ℂ_[resP v] => ‖b‖) J _ A B) hm hm').mpr k2

end GlobalTheory.HalfGeo
