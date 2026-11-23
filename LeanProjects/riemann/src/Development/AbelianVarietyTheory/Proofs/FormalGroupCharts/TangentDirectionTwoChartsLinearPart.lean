import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwoChartAtlas.AdditionLawSecondIdentity
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExpChartJet

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp
open Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdJet Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun Formalism.MainNotions.ModuliIntegralCharts.H1.GermD
open Formalism.MainNotions.ModuliIntegralCharts.H1.ExpChartJetA Formalism.MainNotions.ModuliIntegralCharts.H1.ExpChartJet

namespace GlobalTheory.ChartCmp.CoordDir

section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {V : Type} [CommRing V]
  {t : SAB H (Sp V)} {d : ℕ}

def tanPt (x : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G) (g : Fin 1 × Fin d → V) :
    overAt (𝟙 (Sp V)) (DualNumber V) ⟶ t.G :=
  Formalism.L2.Pj.homAt (𝟙 (Sp V)) (tp g) ≫ x 1

theorem tp_zero : (tp (0 : Fin 1 × Fin d → V)) =
      (Algebra.ofId V (DualNumber V)).comp (jetAug : Jet V (Fin 1 × Fin d) (0 + 1) →ₐ[V] V) := by
  apply jet_hom_ext
  intro q
  rw [tp_mk, AlgHom.comp_apply]
  show TrivSqZeroExt.inr (0 : V) =
    algebraMap V (DualNumber V) (MvPolynomial.aeval (fun _ => (0 : V)) (MvPolynomial.X q))
  rw [MvPolynomial.aeval_X, map_zero, TrivSqZeroExt.inr_zero]

theorem fst_tp (g : Fin 1 × Fin d → V) : (TrivSqZeroExt.fstHom V V V).comp (tp g) =
      (jetAug : Jet V (Fin 1 × Fin d) (0 + 1) →ₐ[V] V) := by
  apply jet_hom_ext
  intro q
  rw [AlgHom.comp_apply, tp_mk]
  show (0 : V) = MvPolynomial.aeval (fun _ => (0 : V)) (MvPolynomial.X q)
  rw [MvPolynomial.aeval_X]

variable {κ : Type} [Fintype κ] {G : FGLaw V d} {act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) V}
  {tg : κ → (Sp (DualNumber V) ⟶ t.G.left)} {uv : κ → Fin d → V} {x : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G}

theorem tanPt_zero (hx : IsChartG t (𝟙 (Sp V)) d G.F act tg uv x) : tanPt x 0 = 1 := by
  have hz : Formalism.L2.Pj.homAt (𝟙 (Sp V)) (jetAug : Jet V (Fin 1 × Fin d) (0 + 1) →ₐ[V] V) ≫ x 1 = 1 := hx.zero 1
  rw [tanPt, tp_zero, ← GermD.homAt_comp, Category.assoc, hz, MonObj.comp_one]

theorem tanPt_add (hx : IsChartG t (𝟙 (Sp V)) d G.F act tg uv x) (g g' : Fin 1 × Fin d → V) :
    tanPt x (g + g') = tanPt x g * tanPt x g' := by
  let T : Jet V (Fin 2 × Fin d) (0 + 1) →ₐ[V] DualNumber V :=
    tp (fun p : Fin 2 × Fin d => (![fun j => g (0, j), fun j => g' (0, j)] : Fin 2 → Fin d → V) p.1 p.2)
  have hT : T = tp (fun p : Fin 2 × Fin d =>
    (![fun j => g (0, j), fun j => g' (0, j)] : Fin 2 → Fin d → V) p.1 p.2) := rfl
  have hc : ∀ i : Fin 2, T.comp (jetCopy d (0 + 1) i) =
      tp (fun q : Fin 1 × Fin d => (![fun j => g (0, j), fun j => g' (0, j)] : Fin 2 → Fin d → V) i q.2) := by
    intro i
    apply jet_hom_ext
    intro q
    rw [AlgHom.comp_apply, jetCopy, jetMap_mk, MvPolynomial.aeval_X, hT, tp_mk, tp_mk]
  have h0 : tp (fun q : Fin 1 × Fin d =>
      (![fun j => g (0, j), fun j => g' (0, j)] : Fin 2 → Fin d → V) 0 q.2) = tp g := by
    congr 1
    funext q
    simp only [Matrix.cons_val_zero, fin_one_pair_eq]
  have h1 : tp (fun q : Fin 1 × Fin d =>
      (![fun j => g (0, j), fun j => g' (0, j)] : Fin 2 → Fin d → V) 1 q.2) = tp g' := by
    congr 1
    funext q
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero, fin_one_pair_eq]
  have hF : T.comp (jetSubstPS (m := 0 + 1) (fun p : Fin 1 × Fin d => G.F p.2)) = tp (g + g') := by
    apply jet_hom_ext
    intro q
    rw [AlgHom.comp_apply, jetSubstPS_mk (0 + 1) (fun p : Fin 1 × Fin d => G.F p.2) (fun p => G.const p.2),
      hT, tp_psJet, tp_mk, G.const, TrivSqZeroExt.inl_zero, zero_add, lin_F]
    simp only [Pi.add_apply, fin_one_pair_eq]
  have hl : Formalism.L2.Pj.homAt (𝟙 (Sp V)) (jetSubstPS (m := 0 + 1) (fun p : Fin 1 × Fin d => G.F p.2)) ≫ x 1 =
      (Formalism.L2.Pj.homAt (𝟙 (Sp V)) (jetCopy d (0 + 1) (0 : Fin 2)) ≫ x 1) *
        (Formalism.L2.Pj.homAt (𝟙 (Sp V)) (jetCopy d (0 + 1) (1 : Fin 2)) ≫ x 1) :=
    hx.law 1
  have e := congrArg (fun f => Formalism.L2.Pj.homAt (𝟙 (Sp V)) T ≫ f) hl
  simp only [MonObj.comp_mul, ← Category.assoc, GermD.homAt_comp, hc, hF, h0, h1] at e
  exact e

theorem tanPt_sum (hx : IsChartG t (𝟙 (Sp V)) d G.F act tg uv x) : ∀ (n : ℕ) (f : Fin n → Fin 1 × Fin d → V),
    tanPt x (∑ i, f i) = (List.ofFn fun i => tanPt x (f i)).prod
  | 0, f => by rw [Fin.sum_univ_zero, List.ofFn_zero, List.prod_nil, tanPt_zero hx]
  | n + 1, f => by rw [Fin.sum_univ_succ, tanPt_add hx, tanPt_sum hx n, List.ofFn_succ, List.prod_cons]

theorem eps_tanPt (x : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G) (a : V) (g : Fin 1 × Fin d → V) :
    spMap (epsMul a) ≫ (Formalism.L2.Pj.homAt (𝟙 (Sp V)) (tp g) ≫ x 1).left = (tanPt x (a • g)).left := by
  have h : (TrivSqZeroExt.map (a • LinearMap.id : V →ₗ[V] V)).comp (tp g) = tp (a • g) := by
    apply jet_hom_ext
    intro q
    rw [AlgHom.comp_apply, tp_mk, tp_mk, TrivSqZeroExt.map_inr]
    rfl
  rw [tanPt, ← h]
  simp only [Over.comp_left, Formalism.L2.Pj.homAt, Over.homMk_left, ← Category.assoc, spMap, epsMul, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp]
  rfl

theorem comb_eq (hx : IsChartG t (𝟙 (Sp V)) d G.F act tg uv x) {u : Fin d → V} {v : Sp (DualNumber V) ⟶ t.G.left}
    (h : IsCombAtG t (𝟙 (Sp V)) (dirs x) u v) : (tanPt x fun q => u q.2).left = v := by
  obtain ⟨w, hw, hprod⟩ := h
  have hw' : w = fun i => tanPt x (u i • fun q : Fin 1 × Fin d => if q = ((0 : Fin 1), i) then (1 : V) else 0) := by
    funext i
    apply Over.OverMorphism.ext
    rw [hw i, dirs, jetTan_eq_tp, eps_tanPt]
  have hq : ∀ (q : Fin 1 × Fin d) (i : Fin d), (q = ((0 : Fin 1), i)) = (i = q.2) := fun q i =>
    propext ⟨fun h => by rw [h], fun h => by rw [h, fin_one_pair_eq]⟩
  have hs : (∑ i, u i • fun q : Fin 1 × Fin d => if q = ((0 : Fin 1), i) then (1 : V) else 0) =
      fun q => u q.2 := by
    funext q
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul, hq, mul_ite, _root_.mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
      if_true]
  rw [← hs, tanPt_sum hx, ← hprod, hw']

theorem tanPt_rel {x x' : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G} {φ : Pt V 1 d}
    (hφ : ∀ i, MvPowerSeries.constantCoeff (φ i) = 0) (h : CoordRel x x' φ) (u : Fin d → V) :
    tanPt x' (fun q => u q.2) = tanPt x (fun q => (dLin φ).mulVec u q.2) := by
  have hF : (tp (fun q : Fin 1 × Fin d => u q.2)).comp (jetSubstPS (m := 0 + 1) (fun p : Fin 1 × Fin d => φ p.2)) =
      tp (fun q : Fin 1 × Fin d => (dLin φ).mulVec u q.2) := by
    apply jet_hom_ext
    intro q
    rw [AlgHom.comp_apply, jetSubstPS_mk (0 + 1) (fun p : Fin 1 × Fin d => φ p.2) (fun p => hφ p.2),
      tp_psJet, tp_mk, hφ, TrivSqZeroExt.inl_zero, zero_add]
    congr 1
    simp only [Fintype.sum_prod_type, Fin.sum_univ_one, Matrix.mulVec, dotProduct, dLin]
    exact Finset.sum_congr rfl fun j _ => _root_.mul_comm _ _
  have h1 : x' 1 = Formalism.L2.Pj.homAt (𝟙 (Sp V)) (jetSubstPS (m := 0 + 1) (fun p : Fin 1 × Fin d => φ p.2)) ≫ x 1 := h 1
  rw [tanPt, tanPt, h1, ← Category.assoc, GermD.homAt_comp, hF]

theorem tanPt_inj {x : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G} (hx : GlobalTheory.PowGerm.IsUnivJ t.G (Fin 1 × Fin d) x)
    {g g' : Fin 1 × Fin d → V} (h : tanPt x g = tanPt x g') : g = g' := by
  have hz : Formalism.L2.Pj.homAt (𝟙 (Sp V)) (jetAug : Jet V (Fin 1 × Fin d) (0 + 1) →ₐ[V] V) ≫ x 1 = 1 := hx.2.1 1
  have h0 : Formalism.L2.Pj.homAt (𝟙 (Sp V)) (TrivSqZeroExt.fstHom V V V) ≫ tanPt x g = 1 := by
    rw [tanPt, ← Category.assoc, GermD.homAt_comp, fst_tp, hz]
  have e : tp g = tp g' :=
    (hx.2.2 (DualNumber V) (TrivSqZeroExt.fstHom V V V) (0 + 1) ker_fst_sq (tanPt x g) h0).unique
      ⟨fst_tp g, rfl⟩ ⟨fst_tp g', h⟩
  funext q
  have := congrArg (fun ψ : Jet V (Fin 1 × Fin d) (0 + 1) →ₐ[V] DualNumber V =>
    ψ (Ideal.Quotient.mk _ (MvPolynomial.X q))) e
  simp only [tp_mk] at this
  exact TrivSqZeroExt.inr_injective this

end

theorem coord_dir : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (V : Type) [CommRing V] (t : SAB H (Sp V)) (d : ℕ) (B B' : FB V d (𝓞 E)) (κ κ' : Type) [Fintype κ] [Fintype κ'] (tg : κ → (Sp (DualNumber V) ⟶ t.G.left)) (tg' : κ' → (Sp (DualNumber V) ⟶ t.G.left)) (uv : κ → Fin d → V) (uv' : κ' → Fin d → V) (x x' : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G) (φ : Pt V 1 d), IsChartG t (𝟙 (Sp V)) d B.G.F B.A.act tg uv x → IsChartG t (𝟙 (Sp V)) d B'.G.F B'.A.act tg' uv' x' → GlobalTheory.PowGerm.IsUnivJ t.G (Fin 1 × Fin d) x → (∀ i, MvPowerSeries.constantCoeff (φ i) = 0) → CoordRel x x' φ → ∀ (u u' : Fin d → V) (v : Sp (DualNumber V) ⟶ t.G.left), IsCombAtG t (𝟙 (Sp V)) (dirs x) u v → IsCombAtG t (𝟙 (Sp V)) (dirs x') u' v → u = (dLin φ).mulVec u' := by
  intro E _ _ _ H _ V _ t d B B' κ κ' _ _ tg tg' uv uv' x x' φ hx hx' hU hφ hrel u u' v hu hu'
  have e : tanPt x (fun q => u q.2) = tanPt x (fun q => (dLin φ).mulVec u' q.2) := by
    rw [← tanPt_rel hφ hrel]
    apply Over.OverMorphism.ext
    rw [comb_eq hx hu, comb_eq hx' hu']
  funext j
  exact congrFun (tanPt_inj hU e) (0, j)

end GlobalTheory.ChartCmp.CoordDir
