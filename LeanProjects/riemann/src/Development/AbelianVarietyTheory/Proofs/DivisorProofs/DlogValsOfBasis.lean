import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsWeilChar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatMatTransposeMulGram
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LengthLetters
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagFramePrimeTangentCompat
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IoOfLeOneIff
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.Mean4O GlobalTheory.LineNorm GlobalTheory.CoverNorm GlobalTheory.HtGen GlobalTheory.TrivFlag GlobalTheory.WholeFlag GlobalTheory.HalfGeo
open Formalism.MainNotions.DIV.Cons (intO)
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.HalfGeo.DlogFrame

open GlobalTheory.LineNorm.Chart GlobalTheory.LieMet

theorem dlogVals_of_basis {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {X : Scheme.{0}} (t : SAB H X) {p : ℕ} [Fact p.Prime] (xO : Sp ↥(intO ℂ_[p]) ⟶ X) {n N g k : ℕ}
    (χ : Fin N → TorsChar t xO (p ^ n)) (e : Fin k → (Sp (DualNumber ↥(intO ℂ_[p])) ⟶ t.G.left))
    (he : IsTanBasis t xO e) (h : Fin N → Fin k → ↥(intO ℂ_[p])) (hd : ∀ j, DlogIs t p n (χ j) e (h j))
    (u : Fin g → (Sp (DualNumber ℂ_[p]) ⟶ t.G.left)) (a : Fin g → Fin k → ℂ_[p])
    (ha : ∀ l, IsCombAtG t (spMap (intO ℂ_[p]).subtype ≫ xO) (fun i => spMap (dualMap (intO ℂ_[p]).subtype) ≫ e i)
      (a l) (u l)) :
    GlobalTheory.EqHalf.DlogVals t xO χ u (Matrix.of fun r l => ∑ i, (h r i : ℂ_[p]) * a l i) := by
  intro vO cf hv hcf m
  have hid : spMap (RingHom.id ↥(intO ℂ_[p])) = 𝟙 _ := Spec.map_id _
  have hid' : spMap (dualMap (RingHom.id ↥(intO ℂ_[p]))) = 𝟙 _ := by
    have : dualMap (RingHom.id ↥(intO ℂ_[p])) = RingHom.id _ := by
      refine RingHom.ext fun z => ?_
      ext <;> simp [dualMap]
    rw [this]
    exact Spec.map_id _
  have h0 := he.2 _ (RingHom.id _) vO (by rwa [hid, Category.id_comp])
  simp only [hid, hid', Category.id_comp] at h0
  obtain ⟨a', ha', -⟩ := h0
  have heC := GlobalTheory.LineNorm.WedgeMax.isTanBasis_map t (intO ℂ_[p]).subtype he
  have h1 := GlobalTheory.LatDRFree.comb_map t (intO ℂ_[p]).subtype ha'
  have h2 := comb_comb heC.1 ha hcf
  have h3 := (he.2 _ (intO ℂ_[p]).subtype _ (comb_tan heC.1 h1)).unique h1 h2
  refine ⟨∑ i, h m i * a' i, ?_, hd m a' vO ha'⟩
  have h4 : ∀ i, (a' i : ℂ_[p]) = ∑ l, cf l * a l i := fun i => by
    simpa [Finset.sum_apply] using congrFun h3 i
  change (intO ℂ_[p]).subtype _ = _
  rw [map_sum]
  simp only [map_mul, Subring.coe_subtype, h4, Matrix.of_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem dlogVals_valMat : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (t : SAB H X)
    (F : Type) [Field F] [NumberField F] (Y : Var F) (V : Cover Y) (ρ' : V.X ⟶ X) (ρ : Y.X ⟶ X), V.j ≫ ρ' = V.π ≫ ρ →
    ∀ (g : ℕ) (f : ∀ y : Y.X, Fin g → (Sp (DualNumber (Y.X.presheaf.stalk y)) ⟶ t.G.left))
    (T : Y.X → Matrix (Fin g) (Fin g) Y.Fn) (v : HeightOneSpectrum (𝓞 F)) [Fact (resP v).Prime] (n : ℕ)
    (ε : GlobalTheory.TrueGeo.Ext v) (y : AlgPt Y) (z : Sp (AlgebraicClosure F) ⟶ V.G) (yt : Sp ε.O ⟶ V.X), z ≫ V.π = y.1 →
    spMap ε.O.subtype ≫ yt = z ≫ V.j →
    ∀ ψ : Y.X.presheaf.stalk (below y.1) →+* ℂ_[resP v], ψ = (ioOf (resP v) ε).comp (Scheme.stalkClosedPointTo y.1).hom →
    ∃ yO : Sp ↥(intO ℂ_[resP v]) ⟶ V.X, spMap (intO ℂ_[resP v]).subtype ≫ yO = spMap (ioOf (resP v) ε) ≫ z ≫ V.j ∧
      spMap (intO ℂ_[resP v]).subtype ≫ yO ≫ ρ' = spMap ψ ≫ GlobalTheory.ShFam.stalkPt Y (below y.1) ≫ ρ ∧
      ∀ (χ : Fin (g + g) → TorsChar t (yO ≫ ρ') (resP v ^ n)) (U : V.X.Opens) (hU : IsAffineOpen U) (k : ℕ)
        (e : Fin k → (Sp (DualNumber Γ(V.X, U)) ⟶ t.G.left)) (h : Fin (g + g) → Fin k → Γ(V.X, U))
        (M : Matrix (Fin (g + g)) (Fin g) V.G.functionField),
        IsTanBasis t (hU.fromSpec ≫ ρ') e → ChartVal V ρ' f T hU e h M → ⊤ ≤ yt ⁻¹ᵁ U →
        (∀ x : Γ(V.X, U) →+* ↥(intO ℂ_[resP v]), spMap x ≫ hU.fromSpec = yO →
          ∀ j, DlogIs t (resP v) n (χ j) (fun i => spMap (dualMap x) ≫ e i) (fun i => x (h j i))) →
        GlobalTheory.EqHalf.DlogVals t (yO ≫ ρ') χ (fun l => spMap (dualMap ψ) ≫ f (below y.1) l)
          ((valMat V M (T (below y.1)) z).map (ioOf (resP v) ε)) := by
  intro E _ _ _ H X t F _ _ Y V ρ' ρ hρ g f T v hp n ε y z yt hz hyt ψ₀ hψ₀
  obtain ⟨y, hy⟩ := y
  dsimp only at hz hψ₀ ⊢
  subst hz
  subst hψ₀
  have h1 := ioOf_le_one_iff (resP v) (residueCharacteristic_mem v) ε
  generalize ioOf (resP v) ε = io at h1 ⊢
  let ioO : ε.O →+* intO ℂ_[resP v] := (io.comp ε.O.subtype).codRestrict _ fun b => (h1 b).2 b.2
  have hio : (intO ℂ_[resP v]).subtype.comp ioO = io.comp ε.O.subtype := rfl
  obtain ⟨ψ, hψ⟩ : ∃ ψ : V.G.presheaf.stalk (below z) →+* ℂ_[resP v],
    ψ = io.comp (Scheme.stalkClosedPointTo z).hom := ⟨_, rfl⟩
  obtain ⟨φ, hφ⟩ : ∃ φ : Y.X.presheaf.stalk (V.π (below z)) →+* ℂ_[resP v],
    φ = io.comp (Scheme.stalkClosedPointTo (z ≫ V.π)).hom := ⟨_, rfl⟩
  have hφψ : ψ.comp (V.π.stalkMap (below z)).hom = φ := by
    rw [hφ, hψ, Scheme.stalkClosedPointTo_comp]; rfl
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
  refine ⟨spMap ioO ≫ yt, hy0, by subst hφ; exact hx.symm, ?_⟩
  intro χ U hU k e h M he hM hin hd
  have hmem : V.j (below z) ∈ U := by
    have : (spMap ε.O.subtype ≫ yt) (IsLocalRing.closedPoint _) ∈ U := hin (Set.mem_univ _)
    rwa [hyt] at this
  obtain ⟨α, a, hα, ha, hMα⟩ := hM _ hmem
  obtain ⟨β, hβ, hβα, hb⟩ := GlobalTheory.HtGen.FlagPoint.chart V.j ρ' ε.O io ioO hio z yt hyt hU hin e α hα a _ ha ψ hψ
  simp only [dual_comp _ ψ, hφψ] at hb
  have hB := GlobalTheory.LineNorm.WedgeMax.isTanBasis_map t β he
  rw [← Category.assoc, hβ] at hB
  have hval : ∀ r, io (TrueGeo.valAt z (algebraMap (V.G.presheaf.stalk (below z)) V.G.functionField r)) = ψ r :=
    fun r => by rw [hψ, Base.valAt_stalk]; rfl
  have hm : (valMat V M (T (V.π (below z))) z).map io =
      Matrix.of fun r l => ∑ i, ((β (h r i) : intO ℂ_[resP v]) : ℂ_[resP v]) * ψ (a l i) := by
    ext r l
    simp only [Matrix.map_apply, valMat, Matrix.of_apply]
    rw [hMα, hval, map_sum]
    simp only [map_mul, hβα]
  have key := dlogVals_of_basis t _ χ _ hB _ (hd β hβ) _ _ hb
  rw [← hm] at key
  subst hφ
  exact key

end GlobalTheory.HalfGeo.DlogFrame
