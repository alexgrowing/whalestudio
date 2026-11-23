import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValAtAlgebraMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SumLogEmbeddingAddFinsumLogAdicAbvEqZero

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions

namespace GlobalTheory.TrueGeo.IndScale

section Values

variable {k K : Type} [Field k] [Field K] {Z : Scheme.{0}} [IsIntegral Z] (p : Z ⟶ Sp k)

theorem unitAt_constFn (x : Z) {a : k} (ha : a ≠ 0) : UnitAt x (Cartier.constFn p a) :=
  unitAt_fnOf (U := ⊤) (x := x) trivial trivial (ha.isUnit.map (algX p ⊤)).unit

theorem valAt_constFn (φ : k →+* K) (y : Sp K ⟶ Z) (hy : y ≫ p = spMap φ) (a : k) :
    valAt y (Cartier.constFn p a) = φ a := by
  have h := OfModel.valAt_fnOf y (U := ⊤) trivial le_top (algX p ⊤ a)
  refine h.trans ?_
  have e1 : p.appLE ⊤ ⊤ le_top ≫ y.appLE ⊤ ⊤ le_top = (spMap φ).appTop := by
    refine (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).trans ?_
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    simp only [hy]
    rfl
  have e2 := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ)
  have e3 : (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ p.appLE ⊤ ⊤ le_top ≫ y.appLE ⊤ ⊤ le_top ≫
      (Scheme.ΓSpecIso (CommRingCat.of K)).hom = CommRingCat.ofHom φ := by
    rw [← Category.assoc (p.appLE ⊤ ⊤ le_top), e1, e2, Iso.inv_hom_id_assoc]
  exact congrArg (fun ψ => ψ.hom a) e3

theorem valAt_ne_zero (y : Sp K ⟶ Z) {f : Z.functionField} (hf : UnitAt (below y) f) : valAt y f ≠ 0 := by
  obtain ⟨a, ha, rfl⟩ := hf
  rw [OfModel.valAt_algebraMap]
  exact (ha.map _).ne_zero

theorem ratVal_constFn {σ : k →+* ℂ} (y : CxPts p σ) (a : k) :
    ratVal (Cartier.constFn p a) y = σ a :=
  (ratVal_fnOf (y := y) mem_ptsIn_top trivial (algX p ⊤ a)).trans (ev_algX mem_ptsIn_top a)

end Values

theorem induced_shift : ∀ (F : Type) [Field F] [NumberField F] (C : CxSt F) (Y : Var F) (A : Adl C Y)
    (M : TrueGeo.Model Y) (L : HermLB M.p) (k : ℕ+) (cf : HeightOneSpectrum (𝓞 F) → ℝ) (b : 𝓞 F), b ≠ 0 →
    ∀ ht : ∀ σ : 𝓞 F →+* ℂ, Real.log ‖((starRingEnd ℂ).comp σ) b‖ = Real.log ‖σ b‖, A.Induced M L k cf →
    A.Induced M (L.shift (fun σ => Real.log ‖σ b‖) ht) k (fun v => cf v +
      Real.log (NumberField.HeightOneSpectrum.adicAbv F v (algebraMap (𝓞 F) F b)) / (((k : ℕ) : ℝ) * (A.n : ℕ))) := by
  intro F _ _ C Y A M L k cf b hb ht ⟨hfin, r, hr, hinf, hv⟩
  have hb' : algebraMap (𝓞 F) F b ≠ 0 := (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective _ _)).2 hb
  have hu (x : Y.X) := unitAt_constFn Y.str x hb'
  let c : Y.Fnˣ := Units.mk0 (Cartier.constFn Y.str (algebraMap (𝓞 F) F b)) (hu (genericPoint Y.X)).ne_zero
  have hc : (c : Y.Fn) = Cartier.constFn Y.str (algebraMap (𝓞 F) F b) := rfl
  refine ⟨?_, fun i => r i * c, ⟨hr.isLB, (hr.add_principal c).isRatSec, fun i x hx => ?_⟩, ?_, ?_⟩
  · refine (hfin.union (sum_log_embedding_add_finsum_log_adicAbv_eq_zero F _ hb').1).subset fun v h => ?_
    by_contra h'
    simp only [Set.mem_union, Function.mem_support, not_or, not_not] at h'
    exact h (by simp only [h'.1, h'.2, zero_div, add_zero])
  · refine (hr.isEqn i x hx).iff_unitAt.2 ?_
    rw [Units.val_mul, mul_div_cancel_left₀ _ (r i).ne_zero]
    exact hu x
  · intro σ y y' i f hy hi hf
    have h₁ : RegAt (under y) (f * (r i : Y.Fn)) := (hr.isEqn i _ hi).regularAt_iff.1 hf
    have h₂ : 0 < ‖σ (algebraMap (𝓞 F) F b)‖ := norm_pos_iff.2 ((map_ne_zero σ).2 hb')
    refine (hinf σ y y' i f hy hi hf).trans ?_
    change _ = ‖ratVal (f * ((r i : Y.Fn) * (c : Y.Fn))) y‖ ^ 2 *
      Real.exp (-((L.φ _).φ (i PUnit.unit) y' + 2 * Real.log ‖σ (algebraMap (𝓞 F) F b)‖))
    rw [← mul_assoc, hc, ratVal_mul h₁ (hu _).regAt, ratVal_constFn, norm_mul, neg_add, Real.exp_add,
      Real.exp_neg (2 * _), show (2 : ℝ) * Real.log ‖σ (algebraMap (𝓞 F) F b)‖ =
        Real.log (‖σ (algebraMap (𝓞 F) F b)‖ ^ 2) by rw [Real.log_pow]; norm_num,
      Real.exp_log (pow_pos h₂ 2)]
    field_simp
  · intro v e y yt i h hi
    have h₁ : below y.1 ∈ (L.B.pull M.j).U i := OfModel.le_chart M L.B e y yt h hi trivial
    have h₂ : UnitAt (below y.1) (((eqn A.D (below y.1))⁻¹ ^ (k : ℕ) * r i : Y.Fnˣ) : Y.Fn) := by
      have := ((A.D.exists_isEqn (below y.1)).choose_spec.nsmul k).iff_unitAt.1 (hr.isEqn i _ h₁)
      rwa [div_eq_inv_mul, ← Units.val_inv_eq_inv_val, ← Units.val_mul, ← inv_pow] at this
    have hk : ((k : ℕ) : ℝ) ≠ 0 := by exact_mod_cast k.ne_zero
    have hn : ((A.n : ℕ) : ℝ) ≠ 0 := by exact_mod_cast A.n.ne_zero
    refine (hv v e y yt i h hi).trans ?_
    rw [← mul_assoc, Units.val_mul _ c, hc, OfModel.valAt_mul _ h₂.regAt (hu _).regAt,
      valAt_constFn Y.str _ y.1 y.2, map_mul, e.w_alg,
      Real.log_mul (e.w.ne_zero (valAt_ne_zero _ h₂)) (AbsoluteValue.ne_zero _ hb')]
    field_simp
    ring

end GlobalTheory.TrueGeo.IndScale
