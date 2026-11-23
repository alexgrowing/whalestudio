import Mathlib
import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import Formalism.LocalToGlobal.ProjectiveLattices.NormsFree
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.IsOrth
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FullLinearLevelCoverBaseChangeTorsor
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree GlobalTheory.EtaForm GlobalTheory.EtaAn GlobalTheory.ArcQ
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace LevelPeriods

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {σ : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)}

theorem exists_periods (Fu : FamilyUnif Xo σ ty) (i : Fin Fu.n) (Pm : (Fu.Di i).La →+ (Fin g → ℂ))
    (hP : IsPeriod (Fu.Di i) ty Pm) (N : ℕ) (hN : 0 < N)
    (ev : LatMod Dw N → (ptO Xo (Fu.u i Pm) ⟶ Xo.univ.t.G)) (hev : IsFullLev Xo N (Fu.u i Pm) ev) :
    ∃ a : LatMod Dw N → (Fu.Di i).La, (∀ q, ev q = Fu.ex i Pm ((N : ℂ)⁻¹ • Pm (a q)) ∧ ev q ^ N = 1) ∧
      ∀ (n : ℕ) (z : Fin n → LatMod Dw N), Submodule.span (𝓞 E) (Set.range z) = ⊤ → ∀ u : (Fu.Di i).La,
        ∃ (cf : Fin n → 𝓞 E) (v : (Fu.Di i).La), u = ∑ b, cf b • a (z b) + N • v := by
  have hN0 : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  let f : (Fin g → ℂ) →+ Additive (ptO Xo (Fu.u i Pm) ⟶ Xo.univ.t.G) :=
    AddMonoidHom.mk' (fun z => Additive.ofMul (Fu.ex i Pm z)) fun z w => congrArg Additive.ofMul (Fu.ex_add i Pm hP z w)
  let e : LatMod Dw N →+ Additive (ptO Xo (Fu.u i Pm) ⟶ Xo.univ.t.G) :=
    AddMonoidHom.mk' (fun q => Additive.ofMul (ev q)) fun a b => congrArg Additive.ofMul (hev.1 a b)
  have hker : ∀ z, f z = 0 ↔ z ∈ Pm.range := fun z => Fu.ex_ker i Pm hP z
  have hNN : ∀ z : Fin g → ℂ, N • ((N : ℂ)⁻¹ • z) = z := fun z => by
    rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, mul_inv_cancel₀ hN0, one_smul]
  have hNN' : ∀ z : Fin g → ℂ, (N : ℂ)⁻¹ • (N • z) = z := fun z => by
    rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hN0, one_smul]
  have hpow : ∀ q, ev q ^ N = 1 := FullLevel.pow_eq_one Xo hev
  have hex : ∀ q, ∃ a, e q = f ((N : ℂ)⁻¹ • Pm a) := fun q => by
    obtain ⟨z, hz⟩ := Fu.ex_onto i Pm hP (ev q)
    have hz' : f z = e q := congrArg Additive.ofMul hz
    have h0 : N • e q = 0 := congrArg Additive.ofMul (hpow q)
    rw [← hz', ← map_nsmul, hker] at h0
    obtain ⟨a, ha⟩ := h0
    exact ⟨a, by rw [ha, hNN', hz']⟩
  choose a ha using hex
  refine ⟨a, fun q => ⟨congrArg Additive.toMul (ha q), hpow q⟩, fun n z hz u => ?_⟩
  have hu : N • f ((N : ℂ)⁻¹ • Pm u) = 0 := by
    rw [← map_nsmul, hNN, hker]
    exact ⟨u, rfl⟩
  obtain ⟨q, hq⟩ := FullLevel.onto_of_local Xo GlobalTheory.firstFiveLaws.1 hN hev (Fu.ex i Pm ((N : ℂ)⁻¹ • Pm u))
    (congrArg Additive.toMul hu)
  have hq' : e q = f ((N : ℂ)⁻¹ • Pm u) := congrArg Additive.ofMul hq
  obtain ⟨cf, hcf⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 E)).1 (hz ▸ Submodule.mem_top : q ∈ Submodule.span (𝓞 E) (Set.range z))
  have hlin : ∀ (o : 𝓞 E) r, e (o • r) = f ((N : ℂ)⁻¹ • Pm (o • a r)) := fun o r => by
    have h1 : (N : ℂ)⁻¹ • Pm (o • a r) = fun k => ty k (o : E) * ((N : ℂ)⁻¹ • Pm (a r)) k := by
      funext k
      simp only [Pi.smul_apply, smul_eq_mul, hP.1]
      ring
    have h2 : ev r = Fu.ex i Pm ((N : ℂ)⁻¹ • Pm (a r)) := congrArg Additive.toMul (ha r)
    refine congrArg Additive.ofMul (?_ : ev (o • r) = Fu.ex i Pm _)
    rw [h1, Fu.ex_lin i Pm hP, hev.2.1, h2]
  have hsum : e q = f ((N : ℂ)⁻¹ • Pm (∑ b, cf b • a (z b))) := by
    rw [← hcf, map_sum, map_sum, Finset.smul_sum, map_sum]
    exact Finset.sum_congr rfl fun b _ => hlin _ _
  have h0 : f ((N : ℂ)⁻¹ • Pm (u - ∑ b, cf b • a (z b))) = 0 := by
    rw [map_sub, smul_sub, map_sub, ← hq', ← hsum, sub_self]
  obtain ⟨v, hv⟩ := (hker _).1 h0
  refine ⟨cf, v, ?_⟩
  have h1 : N • v = u - ∑ b, cf b • a (z b) := hP.2.1 (by rw [map_nsmul, hv, hNN])
  rw [h1, add_sub_cancel]

end LevelPeriods

theorem fullLevel_eq_exp_periods :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty) (i : Fin Fu.n) (Pm : (Fu.Di i).La →+ (Fin g → ℂ)) (y : FrPt Xo c (CAt σ)), IsPeriod (Fu.Di i) ty Pm → y.x = Fu.u i Pm → ∀ (N : ℕ), 0 < N → ∀ ev : LatMod Dw N → (ptO Xo y.x ⟶ Xo.univ.t.G), IsFullLev Xo N y.x ev → ∃ a : LatMod Dw N → (Fu.Di i).La, (∀ q, (ev q).left = (Fu.ex i Pm ((N : ℂ)⁻¹ • Pm (a q))).left ∧ ev q ^ N = 1) ∧ ∀ (n : ℕ) (z : Fin n → LatMod Dw N), Submodule.span (𝓞 E) (Set.range z) = ⊤ → ∀ u : (Fu.Di i).La, ∃ (cf : Fin n → 𝓞 E) (v : (Fu.Di i).La), u = ∑ b, cf b • a (z b) + N • v := by
  intro E _ _ _ H Dw l Xo c σ g ty Fu i Pm y hP hy N hN ev hev
  obtain ⟨x, _, _, _, _, _, _, _⟩ := y
  dsimp only at hy ev hev ⊢
  subst hy
  obtain ⟨a, h1, h2⟩ := LevelPeriods.exists_periods Fu i Pm hP N hN ev hev
  exact ⟨a, fun q => ⟨congrArg CommaMorphism.left (h1 q).1, (h1 q).2⟩, h2⟩

end GlobalTheory
