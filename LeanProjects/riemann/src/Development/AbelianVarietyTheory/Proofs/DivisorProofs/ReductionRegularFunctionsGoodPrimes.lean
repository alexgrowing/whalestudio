import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullFrameRight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodReductionExtendsRegular
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAlgebraicPointSpecializing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitAtPointsOverPrimeBound
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.WholeFlag GlobalTheory.ShFam.Pad

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Mean4O.Cover.MaxUnit

theorem unitAt_of_w_valAt_eq_one {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)}
    (e : TrueGeo.Ext v) {Z : Scheme.{0}} [IsIntegral Z] (yt : Sp e.O ⟶ Z) {g : Z.functionField}
    (hg : RegAt (yt (IsLocalRing.closedPoint e.O)) g)
    (h1 : e.w (valAt (spMap e.O.subtype ≫ yt) g) = 1) : UnitAt (yt (IsLocalRing.closedPoint e.O)) g := by
  obtain ⟨W₀, hW₀, s, hs⟩ := hg.exists_fnOf
  have ht : ⊤ ≤ yt ⁻¹ᵁ W₀ := HtGen.IntPt.top_le_of_closedPoint yt hW₀
  have ht' : ⊤ ≤ (spMap e.O.subtype ≫ yt) ⁻¹ᵁ W₀ := fun q _ => ht (x := spMap e.O.subtype q) trivial
  have hb : below (spMap e.O.subtype ≫ yt) ∈ W₀ := ht' trivial
  have hev := OfModel.eval_pull e.O.subtype (𝟙 Z) (spMap e.O.subtype ≫ yt) yt (Category.comp_id _).symm
    (U := W₀) (W := W₀) le_rfl ht' ht s
  have hid : ((𝟙 Z : Z ⟶ Z).appLE W₀ W₀ le_rfl).hom s = s := by
    have : (𝟙 Z : Z ⟶ Z).appLE W₀ W₀ le_rfl = 𝟙 _ := (Category.id_comp _).trans (Z.presheaf.map_id _)
    rw [this]
    rfl
  rw [hid] at hev
  rw [← hs, OfModel.valAt_fnOf _ hb ht', hev] at h1
  change e.w ((_ : e.O) : AlgebraicClosure F) = 1 at h1
  rw [HtGen.IntPt.w_eq_one_iff, RegCrit.isUnit_eval_iff yt ht s,
    ← unitAt_fnOf_iff hW₀ (gen_mem hW₀), hs] at h1
  exact h1

theorem main : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (V : Cover Y) (p : ℕ), p.Prime → ∀ (W : Y.X.Opens), genericPoint Y.X ∈ W → ∀ (U : V.X.Opens) {S : Type} (f : S → V.X.functionField), (∀ s (z : V.G), V.j z ∈ U → RegAt (V.j z) (f s)) → (∀ v : HeightOneSpectrum (𝓞 F), resP v = p → ∀ (e : TrueGeo.Ext v) (y : AlgPt Y), below y.1 ∈ W → ∀ (z : Sp (AlgebraicClosure F) ⟶ V.G) (yt : Sp e.O ⟶ V.X), z ≫ V.π = y.1 → spMap e.O.subtype ≫ yt = z ≫ V.j → ⊤ ≤ yt ⁻¹ᵁ U → (∀ s, e.w (valAt (z ≫ V.j) (f s)) ≤ 1) ∧ ∃ s, e.w (valAt (z ≫ V.j) (f s)) = 1) → ∀ x ∈ U, ¬ IsUnit (p : V.X.presheaf.stalk x) → ∃ s, UnitAt x (f s) := by
  intro F _ _ Y V p hp W hW U S f hgen hval x hxU hx
  obtain ⟨v, e, y, z, yt, hres, hyW, hzy, hc, hU, hsp⟩ :=
    GlobalTheory.Mean4O.Cover.ThroughFibre.exists_algPt_through F Y V p hp W hW U x hxU hx
  obtain ⟨-, s, hs⟩ := hval v hres e y hyW z yt hzy hc hU
  refine ⟨s, ?_⟩
  set c := yt (IsLocalRing.closedPoint e.O) with hcdef
  have hcU : c ∈ U := hU trivial
  have hpx : (p : 𝓞 F) ∈ (V.p x).asIdeal := by
    by_contra h
    exact hx ((GlobalTheory.Mean4O.Cover.RegOverP.isUnit_natCast_stalk_iff V x p).2 h)
  have hle : (V.p x).asIdeal ≤ (V.p c).asIdeal :=
    (PrimeSpectrum.le_iff_specializes _ _).2 (hsp.map V.p.continuous)
  have hnc : ¬ IsUnit (p : V.X.presheaf.stalk c) := fun h =>
    (GlobalTheory.Mean4O.Cover.RegOverP.isUnit_natCast_stalk_iff V c p).1 h (hle hpx)
  have hreg : RegAt c (f s) :=
    GlobalTheory.Mean4O.Cover.RegOverP.regAt_of_values_over F Y V p hp W hW U (f s) (fun z' hz' => hgen s z' hz')
      (fun v' hv' e' y' hy' z' yt' h1 h2 h3 => (hval v' hv' e' y' hy' z' yt' h1 h2 h3).1 s) c hcU hnc
  have hs' : e.w (valAt (spMap e.O.subtype ≫ yt) (f s)) = 1 := by rw [hc]; exact hs
  exact GlobalTheory.NormExt.unitAt_of_specializes hsp (unitAt_of_w_valAt_eq_one e yt hreg hs')

end GlobalTheory.Mean4O.Cover.MaxUnit
