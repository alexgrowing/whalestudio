import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaValues.IsNullVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsFramedPointBaseChangeAlgHom
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaNullValueExistsUniqueNaturalLinear
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.EtaValAtExistsUniqueNatural
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameChangeCommBaseChange
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LowerTriIsUnitDet

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.EtaForm
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.EtaForm.ScalarWeight

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

theorem finite_aut (Dw : Datum H) {k : ℕ} (hk : 0 < k) : Finite (LevGrp Dw k) := by
  haveI : Finite (LatMod Dw k) := by
    haveI := Dw.fin
    haveI : Module.Finite ℤ (LatMod Dw k) := Module.Finite.trans (𝓞 E) _
    refine Module.finite_of_fg_torsion (M := LatMod Dw k) fun x => ?_
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ x
    refine ⟨⟨(k : ℤ), mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast hk.ne')⟩, ?_⟩
    change (k : ℤ) • Submodule.mkQ (Ideal.span {(k : 𝓞 E)} • ⊤ : Submodule (𝓞 E) Dw.La) x = 0
    rw [natCast_zsmul, ← map_nsmul]
    refine (Submodule.Quotient.mk_eq_zero _).2 ?_
    rw [← Nat.cast_smul_eq_nsmul (𝓞 E)]
    exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) Submodule.mem_top
  exact Finite.of_injective (fun g : LevGrp Dw k => (g : LatMod Dw k → LatMod Dw k)) DFunLike.coe_injective

theorem etaExpr_scale {S : Type} [CommRing S] {k : ℕ} (hk : 0 < k) {J : Type} [Fintype J] {n : ℕ} (cf : J → ℤ)
    (x : J → Fin n → LatMod Dw k) (w : LatMod Dw k → S) (t : S) :
    etaExpr k cf x (fun q => t * w q) = t ^ (n * Nat.card (LevGrp Dw k)) * etaExpr k cf x w := by
  haveI := finite_aut Dw hk
  haveI := Fintype.ofFinite (LevGrp Dw k)
  unfold etaExpr
  rw [finprod_eq_prod_of_fintype, finprod_eq_prod_of_fintype, Nat.card_eq_fintype_card, pow_mul,
    ← Finset.card_univ, ← Finset.prod_const, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun g _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  ring

variable {Xo : Moduli Dw l} {c : Coeff l}

theorem frBor_baseChange {S T : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T]
    (φ : S →ₐ[c.F] T) {t : Ix Dw → Sˣ} {y y' : FrPt Xo c S} {z z' : FrPt Xo c T} (h : FrBor t y y')
    (hz : FrMap φ y z) (hz' : FrMap φ y' z') : FrBor (fun i => Units.map (φ : S →* T) (t i)) z z' := by
  obtain ⟨g, hg2, hg1, hg⟩ := (GlobalTheory.Frames.frBor_iff_frChg y y' t).1 h
  have hc := (GlobalTheory.Frames.ChgBC.frChg_baseChange E H Dw l Xo c S T φ y y' z z' g _ hg hz).1 hz'
  exact (GlobalTheory.Frames.frBor_iff_frChg z z' _).2
    ⟨fun τ => (g τ).map φ, fun τ i j hij => by simp [hg2 τ i j hij], fun τ i => by simp [hg1], hc⟩

theorem exists_level_of_eq {k : ℕ} {S : Type} [CommRing S] {x₀ x₁ : Sp S ⟶ Xo.X} (h : x₁ = x₀)
    {ev : LatMod Dw k → (ptO Xo x₀ ⟶ Xo.univ.t.G)} (hev : IsFullLev Xo k x₀ ev) :
    ∃ ev' : LatMod Dw k → (ptO Xo x₁ ⟶ Xo.univ.t.G), IsFullLev Xo k x₁ ev' ∧ ∀ q, (ev' q).left = (ev q).left := by
  subst h
  exact ⟨ev, hev, fun _ => rfl⟩

theorem etaValAt_frBor (hL : Laws) {R : ℕ} (hR : Odd R) {J : Type} [Fintype J] {n : ℕ} {cf : J → ℤ}
    {x : J → Fin n → LatMod Dw (R ^ 4)} {S : Type} [CommRing S] [Algebra c.F S] {t : Ix Dw → Sˣ}
    {y y' : FrPt Xo c S} (h : FrBor t y y') {v : S} (hv : EtaValAt Xo c R cf x y v) :
    EtaValAt Xo c R cf x y' ((t none : S) ^ (n * Nat.card (LevGrp Dw (R ^ 4))) * v) := by
  obtain ⟨S', _, _, φ, z, ev, w, hφ, hz, hev, hw, hv⟩ := hv
  obtain ⟨z', hz'⟩ := GlobalTheory.FramedBaseChange.exists_frMap hL E H Dw l Xo c S S' φ y'
  have hb := frBor_baseChange φ h hz hz'
  obtain ⟨ev', hev', he⟩ := exists_level_of_eq hb.1 hev
  refine ⟨S', _, _, φ, z', ev', fun q => φ (t none) * w q, hφ, hz', hev', fun q => ?_, ?_⟩
  · exact (GlobalTheory.nullValue_existsUnique_natural_linear hL E H Dw l Xo c (R ^ 2) hR.pow).2.2 S' z z' _ hb (ev q) (ev' q) (he q) (w q) (hw q)
  · rw [etaExpr_scale (pow_pos hR.pos _), map_mul, map_pow, hv]

end GlobalTheory.EtaForm.ScalarWeight

namespace GlobalTheory.EtaForm

theorem isEtaRule_existsUnique_mem_sec : Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (R : ℕ), Odd R → ∀ (J : Type) [Fintype J] (n : ℕ) (cf : J → ℤ) (x : J → Fin n → LatMod Dw (R ^ 4)), (∃! f, IsEtaRule Xo c R cf x f) ∧ ∀ f, IsEtaRule Xo c R cf x f → f ∈ sec Xo c 0 (n * Nat.card (LevGrp Dw (R ^ 4))) := by
  intro hL E _ _ _ H Dw l Xo c R hR J _ n cf x
  obtain ⟨hex, hnat⟩ := GlobalTheory.EtaForm.etaValAt_existsUnique_natural hL E H Dw l Xo c R hR J n cf x
  refine ⟨⟨fun p y => (hex p.R y).exists.choose, fun p y => (hex p.R y).exists.choose_spec, fun f hf => ?_⟩,
    fun f hf => ⟨fun p q φ y z h => ?_, fun p t y y' h => ?_⟩⟩
  · funext p y
    exact (hex p.R y).unique (hf p y) (hex p.R y).exists.choose_spec
  · exact (hnat p.R q.R φ y z h _ _ (hf p y) (hf q z)).symm
  · rw [(hex p.R y').unique (hf p y') (ScalarWeight.etaValAt_frBor hL hR h (hf p y))]
    congr 1
    simp [wchar, ex, Fintype.prod_option]

end GlobalTheory.EtaForm
