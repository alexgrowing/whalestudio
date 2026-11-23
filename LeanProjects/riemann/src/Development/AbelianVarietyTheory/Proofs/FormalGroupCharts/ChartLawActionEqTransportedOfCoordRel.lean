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
namespace GlobalTheory.ChartCmp.CoordLaw
open Formalism.MainNotions.ModuliIntegralCharts.H1

variable {V : Type} [CommRing V] {d : ℕ}

theorem ev_one_eq {n : ℕ} (a : Pt V n d) (f : PS V 1 d) :
    ev ![a] f = MvPowerSeries.subst (fun p : Fin 1 × Fin d => a p.2) f := by
  unfold ev
  congr 1
  funext p
  rw [Matrix.cons_val_fin_one]

theorem cc_ev {k n : ℕ} (a : Fin k → Pt V n d) (ha : ∀ j i, MvPowerSeries.constantCoeff (a j i) = 0) (f : PS V k d)
    (hf : MvPowerSeries.constantCoeff f = 0) : MvPowerSeries.constantCoeff (ev a f) = 0 :=
  MvPowerSeries.constantCoeff_subst_eq_zero (a := fun p : Fin k × Fin d => a p.1 p.2)
    (MvPowerSeries.hasSubst_of_constantCoeff_zero fun p => ha p.1 p.2) (fun p => ha p.1 p.2) hf

theorem cc_comp1 {n : ℕ} {φ : Pt V 1 d} {a : Pt V n d} (hφ : ∀ i, MvPowerSeries.constantCoeff (φ i) = 0)
    (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) (i : Fin d) : MvPowerSeries.constantCoeff (comp1 φ a i) = 0 :=
  cc_ev _ (fun j i => by rw [Matrix.cons_val_fin_one]; exact ha i) _ (hφ i)

theorem germCompOne_assoc_of_constantCoeff_zero {n : ℕ} (ψ φ : Pt V 1 d) (a : Pt V n d) (hφ : ∀ i, MvPowerSeries.constantCoeff (φ i) = 0)
    (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) : comp1 (comp1 ψ φ) a = comp1 ψ (comp1 φ a) := by
  funext i
  simp only [comp1, ev_one_eq]
  exact MvPowerSeries.subst_comp_subst_apply
    (MvPowerSeries.hasSubst_of_constantCoeff_zero fun p : Fin 1 × Fin d => hφ p.2)
    (MvPowerSeries.hasSubst_of_constantCoeff_zero fun p : Fin 1 × Fin d => ha p.2) _

theorem germCompOne_identityPoint_left {n : ℕ} (a : Pt V n d) (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) :
    comp1 (pt V (n := 1) d 0) a = a := by
  funext i
  simp only [comp1, ev_one_eq, pt]
  exact MvPowerSeries.subst_X (MvPowerSeries.hasSubst_of_constantCoeff_zero fun p : Fin 1 × Fin d => ha p.2) _

theorem eq_comp1_inv {n : ℕ} {φ φi : Pt V 1 d} (h : IsInvPair φ φi) {a b : Pt V n d}
    (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) (e : comp1 φ a = b) : a = comp1 φi b := by
  rw [← e, ← germCompOne_assoc_of_constantCoeff_zero φi φ a h.1 ha, h.2.2.2, germCompOne_identityPoint_left a ha]

def sub (m : ℕ) {k n : ℕ} (a : Fin k → Pt V n d) : jOG (𝟙 (Sp V)) d m n ⟶ jOG (𝟙 (Sp V)) d m k :=
  Formalism.L2.Pj.homAt (𝟙 (Sp V)) (jetSubstPS (m := m) fun p : Fin k × Fin d => a p.1 p.2)

def sub1 (m : ℕ) {n : ℕ} (a : Pt V n d) : jOG (𝟙 (Sp V)) d m n ⟶ jOG (𝟙 (Sp V)) d m 1 :=
  Formalism.L2.Pj.homAt (𝟙 (Sp V)) (jetSubstPS (m := m) fun p : Fin 1 × Fin d => a p.2)

theorem hom_comp (m : ℕ) {κ κ' κ'' : Type} [Fintype κ'] [DecidableEq κ'] [Fintype κ''] [DecidableEq κ'']
    (g : κ → MvPowerSeries κ' V) (h : κ' → MvPowerSeries κ'' V) (hg : ∀ i, MvPowerSeries.constantCoeff (g i) = 0)
    (hh : ∀ i, MvPowerSeries.constantCoeff (h i) = 0) :
    Formalism.L2.Pj.homAt (𝟙 (Sp V)) (jetSubstPS (m := m) h) ≫ Formalism.L2.Pj.homAt (𝟙 (Sp V)) (jetSubstPS (m := m) g) =
      Formalism.L2.Pj.homAt (𝟙 (Sp V)) (jetSubstPS (m := m) fun i => MvPowerSeries.subst h (g i)) := by
  rw [GermD.homAt_comp]
  congr 1
  apply GermD.jet_hom_ext
  intro i
  rw [AlgHom.comp_apply, ExpChartJet.jetSubstPS_mk m g hg, ExpChartJet.jetSubstPS_psJet m h hh,
    ExpChartJet.jetSubstPS_mk m _ (fun i => MvPowerSeries.constantCoeff_subst_eq_zero
      (MvPowerSeries.hasSubst_of_constantCoeff_zero hh) hh (hg i))]

theorem jetSchemeMap_pointFamily_comp_singlePoint (m : ℕ) {k n : ℕ} (a : Fin k → Pt V n d) (b : Pt V k d)
    (ha : ∀ j i, MvPowerSeries.constantCoeff (a j i) = 0) (hb : ∀ i, MvPowerSeries.constantCoeff (b i) = 0) :
    sub m a ≫ sub1 m b = sub1 m (fun i => ev a (b i)) :=
  hom_comp m _ _ (fun p => hb p.2) (fun p => ha p.1 p.2)

theorem jetSchemeMap_singlePoint_comp_singlePoint (m : ℕ) {n : ℕ} (a : Pt V n d) (φ : Pt V 1 d)
    (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) (hφ : ∀ i, MvPowerSeries.constantCoeff (φ i) = 0) :
    sub1 m a ≫ sub1 m φ = sub1 m (comp1 φ a) := by
  have e : sub1 m (comp1 φ a) = Formalism.L2.Pj.homAt (𝟙 (Sp V)) (jetSubstPS (m := m) fun p : Fin 1 × Fin d =>
      MvPowerSeries.subst (fun q : Fin 1 × Fin d => a q.2) (φ p.2)) := by
    simp only [sub1, comp1, ev_one_eq]
  rw [e]
  exact hom_comp m _ _ (fun p => hφ p.2) (fun p => ha p.2)

theorem eq_of_jetSchemeMap_singlePoint_universal {G : Over (Sp V)} [GrpObj G] {x : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ G}
    (hx : GlobalTheory.PowGerm.IsUnivJ G (Fin 1 × Fin d) x) {n : ℕ} {a b : Pt V n d}
    (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) (hb : ∀ i, MvPowerSeries.constantCoeff (b i) = 0)
    (h : ∀ m, sub1 m a ≫ x m = sub1 m b ≫ x m) : a = b := by
  funext i
  refine GermFun.psJet_inj fun m => ?_
  have hk : RingHom.ker (jetAug : Jet V (Fin n × Fin d) m →ₐ[V] V) ^ (m + 1) = ⊥ := by
    have ea : (jetAug : Jet V (Fin n × Fin d) m →ₐ[V] V) = Chart.jetAug V _ m := Chart.jet_ext fun j => rfl
    rw [ea]
    exact Chart.ker_jetAug_pow _ m
  have aa := ExpChartJet.aug_comp_jetSubstPS m (fun p : Fin 1 × Fin d => a p.2) (fun p => ha p.2)
  have ab := ExpChartJet.aug_comp_jetSubstPS m (fun p : Fin 1 × Fin d => b p.2) (fun p => hb p.2)
  have h1 : Formalism.L2.Pj.homAt (𝟙 (Sp V)) (jetAug : Jet V (Fin n × Fin d) m →ₐ[V] V) ≫ (sub1 m a ≫ x m) = 1 := by
    rw [sub1, ← Category.assoc, GermD.homAt_comp, aa]
    exact hx.2.1 m
  have e := (hx.2.2 _ jetAug m hk _ h1).unique ⟨aa, rfl⟩ ⟨ab, h m⟩
  have e' := AlgHom.congr_fun e (Ideal.Quotient.mk _ (MvPolynomial.X ((0 : Fin 1), i)))
  rwa [ExpChartJet.jetSubstPS_mk m (fun p : Fin 1 × Fin d => a p.2) (fun p => ha p.2),
    ExpChartJet.jetSubstPS_mk m (fun p : Fin 1 × Fin d => b p.2) (fun p => hb p.2)] at e'

theorem jptG_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (t : SAB H (Sp V))
    (x : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G) (m : ℕ) {n : ℕ} (i : Fin n) :
    jptG t (𝟙 (Sp V)) d x m i = sub1 m (pt V d i) ≫ x m := by
  have e : jetCopy (S := V) d m i = jetSubstPS (m := m) (fun p : Fin 1 × Fin d => pt V d i p.2) := by
    apply GermD.jet_hom_ext
    intro p
    rw [ExpChartJet.jetSubstPS_mk m (fun p : Fin 1 × Fin d => pt V d i p.2) (fun _ => MvPowerSeries.constantCoeff_X _),
      jetCopy, GermD.jetMap_mk, MvPolynomial.aeval_X, pt, ← MvPolynomial.coe_X]
    rw [psJet, FBIdJet.psTrunc_eq, FBIdJet.mk_trunc_coe]
  rw [jptG, e]
  rfl

end GlobalTheory.ChartCmp.CoordLaw

open GlobalTheory.ChartCmp.CoordLaw in

theorem GlobalTheory.ChartCmp.law_act_of_coordRel : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (V : Type) [CommRing V] (t : SAB H (Sp V)) (d : ℕ) (B B' : FB V d (𝓞 E)) (κ κ' : Type) [Fintype κ] [Fintype κ'] (tg : κ → (Sp (DualNumber V) ⟶ t.G.left)) (tg' : κ' → (Sp (DualNumber V) ⟶ t.G.left)) (uv : κ → Fin d → V) (uv' : κ' → Fin d → V) (x x' : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G) (φ φi : Pt V 1 d), IsChartG t (𝟙 (Sp V)) d B.G.F B.A.act tg uv x → IsChartG t (𝟙 (Sp V)) d B'.G.F B'.A.act tg' uv' x' → GlobalTheory.PowGerm.IsUnivJ t.G (Fin 1 × Fin d) x → IsInvPair φ φi → CoordRel x x' φ → (∀ i, B'.G.F i = transF B.G.F φ φi i) ∧ ∀ a, B'.A.act a = comp1 φi (comp1 (B.A.act a) φ) := by
  intro E _ _ _ H _ V _ t d B B' κ κ' _ _ tg tg' uv uv' x x' φ φi hc hc' hu hinv hrel
  have hφ := hinv.1
  have hr : ∀ m, x' m = sub1 m φ ≫ x m := hrel
  have hpt : ∀ (j : Fin 2) i, MvPowerSeries.constantCoeff (pt V d j i) = 0 := fun j i => MvPowerSeries.constantCoeff_X _
  refine ⟨?_, fun a => ?_⟩
  · let A : Fin 2 → Pt V 2 d := ![comp1 φ (pt V (n := 2) d 0), comp1 φ (pt V (n := 2) d 1)]
    have hA : ∀ j i, MvPowerSeries.constantCoeff (A j i) = 0 := by
      intro j i
      fin_cases j <;> exact cc_comp1 hφ (hpt _) i
    have hX : ∀ j, (fun i => ev A (pt V d j i)) = A j := fun j => funext fun i =>
      MvPowerSeries.subst_X (MvPowerSeries.hasSubst_of_constantCoeff_zero fun p : Fin 2 × Fin d => hA p.1 p.2) (j, i)
    have key : comp1 φ B'.G.F = addOf B.G.F (comp1 φ (pt V (n := 2) d 0)) (comp1 φ (pt V (n := 2) d 1)) := by
      refine eq_of_jetSchemeMap_singlePoint_universal hu (cc_comp1 hφ B'.G.const) (fun i => cc_ev A hA _ (B.G.const i)) fun m => ?_
      have l : sub1 m B.G.F ≫ x m = _ := hc.law m
      have l' : sub1 m B'.G.F ≫ x' m = _ := hc'.law m
      have l2 := congrArg (fun f => sub m A ≫ f) l
      simp only [jptG_eq, MonObj.comp_mul, ← Category.assoc, jetSchemeMap_pointFamily_comp_singlePoint m A _ hA B.G.const, jetSchemeMap_pointFamily_comp_singlePoint m A _ hA (hpt _),
        hX] at l2
      simp only [jptG_eq, hr m, ← Category.assoc, jetSchemeMap_singlePoint_comp_singlePoint m _ φ B'.G.const hφ, jetSchemeMap_singlePoint_comp_singlePoint m _ φ (hpt _) hφ] at l'
      exact l'.trans l2.symm
    exact fun i => congrFun (eq_comp1_inv hinv B'.G.const key) i
  · refine eq_comp1_inv hinv (B'.A.const a) ?_
    refine eq_of_jetSchemeMap_singlePoint_universal hu (cc_comp1 hφ (B'.A.const a)) (cc_comp1 (B.A.const a) hφ) fun m => ?_
    have l : x m ≫ t.act.act a = sub1 m (B.A.act a) ≫ x m := hc.act m a
    have l' : x' m ≫ t.act.act a = sub1 m (B'.A.act a) ≫ x' m := hc'.act m a
    rw [← jetSchemeMap_singlePoint_comp_singlePoint m _ φ (B'.A.const a) hφ, ← jetSchemeMap_singlePoint_comp_singlePoint m φ _ hφ (B.A.const a), Category.assoc, Category.assoc, ← hr m,
      ← l', ← l, hr m, Category.assoc]
