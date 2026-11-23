import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.ColumnSplitting

variable {D : D7} {n t : ℕ} {B W : HSp D}

def c1 (hn : W.rank + t = n) {a : ℕ} (U : Mx D a n) : Mx D a W.rank :=
  U.submatrix id fun j => finCongr hn (Fin.castAdd t j)

def c2 (hn : W.rank + t = n) {a : ℕ} (U : Mx D a n) : Mx D a t :=
  U.submatrix id fun j => finCongr hn (Fin.natAdd W.rank j)

def ww (W : HSp D) (x₀ : Matrix (Fin W.rank) (Fin W.rank) D.host.E) (h : GA D W) : Mx D W.rank W.rank :=
  mm (mt W h⁻¹) (rat x₀)

def ac (V : HSp D) {a b : ℕ} (g : GA D V) (z : Mx D V.rank a × Mx D V.rank b) : Mx D V.rank a × Mx D V.rank b :=
  (mm (mt V g) z.1, mm (mt V g) z.2)

abbrev Par (D : D7) (n t : ℕ) (W : HSp D) : Type := GA D W × Mx D t n × Mx D W.rank t

def zp (d : HypDec B W t) (hn : W.rank + t = n) (x₀ : Matrix (Fin W.rank) (Fin W.rank) D.host.E) (p : Par D n t W) :
    Mx D B.rank W.rank × Mx D B.rank t :=
  (mm d.jX (c1 hn p.2.1) + mm d.j0 (ww W x₀ p.1),
    mm (mm d.jX (c1 hn p.2.1) + mm d.j0 (ww W x₀ p.1)) p.2.2 + mm d.jX (c2 hn p.2.1))

def Q0 {d : HypDec B W t} (I : IkD d n) (μ : Measure (Mx D W.rank t)) : Measure (Par D n t W) :=
  I.m.prod (I.μ₁.prod μ)

def rho {d : HypDec B W t} (hn : W.rank + t = n) (I : IkD d n) (μ : Measure (Mx D W.rank t))
    (x₀ : Matrix (Fin W.rank) (Fin W.rank) D.host.E) : Measure (Mx D B.rank W.rank × Mx D B.rank t) :=
  (Q0 I μ).map (zp d hn x₀)

def nuT {d : HypDec B W t} (hn : W.rank + t = n) (I : IkD d n) (μ : Measure (Mx D W.rank t))
    (x₀ : Matrix (Fin W.rank) (Fin W.rank) D.host.E) : Measure (Mx D B.rank W.rank × Mx D B.rank t) :=
  (I.νK.prod (Q0 I μ)).map fun p => ac B ((p.1 : GA D B)⁻¹) (zp d hn x₀ p.2)

end GlobalTheory.CompanionTheory.ColumnSplitting

namespace GlobalTheory.CompanionTheory.ColumnSplitting
variable {D : D7} {n t : ℕ} {B W : HSp D}

theorem top_mx (a b : ℕ) : IsTopologicalAddGroup (Mx D a b) ∧ LocallyCompactSpace (Mx D a b) ∧ SecondCountableTopology (Mx D a b) ∧
    T2Space (Mx D a b) ∧ BorelSpace (Mx D a b) := by
  obtain ⟨i1, i2, i3, i4, -, -⟩ := lattice_Mx D a b
  exact ⟨i1, i2, i3, i4, ⟨rfl⟩⟩

theorem continuous_first_column_block (hn : W.rank + t = n) {a : ℕ} : Continuous (c1 (D := D) (W := W) hn (a := a)) :=
  continuous_id.matrix_submatrix _ _

theorem continuous_second_column_block (hn : W.rank + t = n) {a : ℕ} : Continuous (c2 (D := D) (W := W) hn (a := a)) :=
  continuous_id.matrix_submatrix _ _

theorem continuous_ww (x₀ : Matrix (Fin W.rank) (Fin W.rank) D.host.E) : Continuous (ww W x₀) := by
  have := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  obtain ⟨-, -, -, -, h5, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D W
  exact ((continuous_mt W).comp continuous_inv).matrix_mul continuous_const

theorem continuous_zp (d : HypDec B W t) (hn : W.rank + t = n) (x₀ : Matrix (Fin W.rank) (Fin W.rank) D.host.E) :
    Continuous (zp d hn x₀) := by
  have := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  have hT := (top_mx (D := D) B.rank W.rank).1
  have hT2 := (top_mx (D := D) B.rank t).1
  have h1 : Continuous fun p : Par D n t W => mm d.jX (c1 hn p.2.1) + mm d.j0 (ww W x₀ p.1) :=
    (continuous_const.matrix_mul ((continuous_first_column_block hn).comp (continuous_fst.comp continuous_snd))).add
      (continuous_const.matrix_mul ((continuous_ww x₀).comp continuous_fst))
  exact h1.prodMk ((h1.matrix_mul (continuous_snd.comp continuous_snd)).add
    (continuous_const.matrix_mul ((continuous_second_column_block hn).comp (continuous_fst.comp continuous_snd))))

theorem continuous_ac (V : HSp D) {a b : ℕ} :
    Continuous fun u : GA D V × (Mx D V.rank a × Mx D V.rank b) => ac V u.1 u.2 := by
  have := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  exact (((continuous_mt V).comp continuous_fst).matrix_mul (continuous_fst.comp continuous_snd)).prodMk
    (((continuous_mt V).comp continuous_fst).matrix_mul (continuous_snd.comp continuous_snd))

theorem top_pair (a b c : ℕ) : BorelSpace (Mx D a b × Mx D a c) ∧ SecondCountableTopology (Mx D a b × Mx D a c) := by
  obtain ⟨-, -, h3, -, h5⟩ := top_mx (D := D) a b
  obtain ⟨-, -, h3', -, h5'⟩ := top_mx (D := D) a c
  exact ⟨inferInstance, inferInstance⟩

theorem top_par (n t : ℕ) (W : HSp D) : BorelSpace (Par D n t W) ∧ SecondCountableTopology (Par D n t W) := by
  obtain ⟨-, -, h3, -, h5⟩ := top_mx (D := D) t n
  obtain ⟨-, -, h3', -, h5'⟩ := top_mx (D := D) W.rank t
  obtain ⟨-, g2, -, g4, -, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D W
  have : BorelSpace (GA D W) := ⟨rfl⟩
  exact ⟨inferInstance, inferInstance⟩

theorem measurable_zp (d : HypDec B W t) (hn : W.rank + t = n) (x₀ : Matrix (Fin W.rank) (Fin W.rank) D.host.E) :
    Measurable (zp d hn x₀) := by
  obtain ⟨h1, h2⟩ := top_par (D := D) n t W
  obtain ⟨g1, g2⟩ := top_pair (D := D) B.rank W.rank t
  have o1 : OpensMeasurableSpace (Par D n t W) := h1.opensMeasurable
  exact (continuous_zp d hn x₀).measurable

theorem sigmaFinite_parameter_product_measure {d : HypDec B W t} (I : IkD d n) (μ : Measure (Mx D W.rank t)) (hμ : μ.IsAddHaarMeasure) :
    SigmaFinite (Q0 I μ) := by
  obtain ⟨-, i2, i3, i4, i5⟩ := top_mx (D := D) t n
  obtain ⟨-, j2, j3, j4, j5⟩ := top_mx (D := D) W.rank t
  obtain ⟨-, g2, g3, -, -, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D W
  have : BorelSpace (GA D W) := ⟨rfl⟩
  obtain ⟨hc, 𝓕, hf⟩ := I.cov₁
  have := hf.1
  have := I.haar
  unfold Q0
  infer_instance

end GlobalTheory.CompanionTheory.ColumnSplitting

namespace GlobalTheory.CompanionTheory.ColumnSplitting
variable {D : D7} {n t : ℕ} {B W : HSp D}

def XU (d : HypDec B W t) (hn : W.rank + t = n) (x₀ : Matrix (Fin W.rank) (Fin W.rank) D.host.E) (h : GA D W) (U : Mx D t n) :
    Mx D B.rank n :=
  mm d.jX U + mm d.j0 (jn hn (ww W x₀ h) 0)

theorem measurable_pi {d : HypDec B W t} (hn : W.rank + t = n) (I : IkD d n)
    (x₀ : Matrix (Fin W.rank) (Fin W.rank) D.host.E) :
    Measurable fun p : I.l.K × Par D n t W => ac B ((p.1 : GA D B)⁻¹) (zp d hn x₀ p.2) := by
  obtain ⟨h1, h2⟩ := top_par (D := D) n t W
  obtain ⟨g1, g2⟩ := top_pair (D := D) B.rank W.rank t
  obtain ⟨-, k2, -, -, k5, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D B
  have hB : BorelSpace (GA D B) := ⟨rfl⟩
  have hK : BorelSpace I.l.K := Subtype.borelSpace _
  have o0 : OpensMeasurableSpace (Par D n t W) := h1.opensMeasurable
  have oK : OpensMeasurableSpace I.l.K := hK.opensMeasurable
  have e1 : SecondCountableTopologyEither I.l.K (Par D n t W) := ⟨Or.inr h2⟩
  have o1 : OpensMeasurableSpace (I.l.K × Par D n t W) := Prod.opensMeasurableSpace
  have hc : Continuous fun p : I.l.K × Par D n t W => ac B ((p.1 : GA D B)⁻¹) (zp d hn x₀ p.2) :=
    (continuous_ac B).comp (((continuous_subtype_val.comp continuous_fst).inv).prodMk
      ((continuous_zp d hn x₀).comp continuous_snd))
  exact hc.measurable

end GlobalTheory.CompanionTheory.ColumnSplitting

namespace GlobalTheory.CompanionTheory.ColumnSplitting

def Dom : Prop := ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (a b c : ℕ) (ι : Fin c → Fin b), Function.Injective ι →
  ∀ Φ ∈ schwartzA θ a b, ∃ M ∈ schwartzA θ a c, (∀ y, 0 ≤ (M y).re ∧ (M y).im = 0) ∧
    ∀ x : Mx D a b, ‖Φ x‖ ≤ (M (x.submatrix id ι)).re

def OrbFin : Prop := ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (W : HSp D) (m : Measure (GA D W)), m.IsHaarMeasure →
  ∀ (x₀ : Matrix (Fin W.rank) (Fin W.rank) D.host.E), x₀.det ≠ 0 → ∀ N ∈ schwartzA θ W.rank W.rank,
    ∫⁻ h, ‖N (ww W x₀ h)‖ₑ ∂m < ⊤

def ZpEq : Prop := ∀ (D : D7) (n t : ℕ) (B W : HSp D) (d : HypDec B W t) (hn : W.rank + t = n) (b₀ : HermE D W.rank),
  b₀.1.det ≠ 0 → ∀ x₀, gramQ W x₀ = b₀.1 → ∀ p : Par D n t W,
    ip B (zp d hn x₀ p).1 (zp d hn x₀ p).1 = rat b₀.1 ∧ yv B b₀ (zp d hn x₀ p) = p.2.2 ∧ qv B b₀ (zp d hn x₀ p) = 0

def AcEq : Prop := ∀ (D : D7) (r t : ℕ) (V : HSp D) (b₀ : HermE D r) (g : GA D V) (z : Mx D V.rank r × Mx D V.rank t),
  ip V (ac V g z).1 (ac V g z).1 = ip V z.1 z.1 ∧ yv V b₀ (ac V g z) = yv V b₀ z ∧ qv V b₀ (ac V g z) = qv V b₀ z

def JnPi : Prop := ∀ (D : D7) (n t : ℕ) (B W : HSp D) (d : HypDec B W t) (hn : W.rank + t = n) x₀ (g : GA D B) (p : Par D n t W),
  jn hn (ac B g (zp d hn x₀ p)).1 (ac B g (zp d hn x₀ p)).2 =
    mm (mt B g) (mm (XU d hn x₀ p.1 p.2.1) (bl hn 1 p.2.2 0 1))

def JnBl : Prop := ∀ (D : D7) (n t a : ℕ) (r : ℕ) (hn : r + t = n) (w : Mx D a r) (v : Mx D a t) (y : Mx D r t),
  mm (jn hn w v) (bl hn 1 y 0 1) = jn hn w (mm w y + v)

def Ext0 : Prop := ∀ (D : D7) (n t : ℕ) (W : HSp D) (hn : W.rank + t = n) x₀ (h : GA D W),
  mm (mt W h⁻¹) (rat (ext0 hn x₀)) = jn hn (ww W x₀ h) 0

def Shift : Prop := ∀ (D : D7) (n t : ℕ) (B W : HSp D) (d : HypDec B W t) (hn : W.rank + t = n) (I : IkD d n)
  (Φ : Mx D B.rank n → ℂ) (y : Mx D W.rank t) (a : Mx D W.rank n),
    ikp I (fun X => Φ (mm X (bl hn 1 y 0 1))) a = ikp I Φ (mm a (bl hn 1 y 0 1))

def IkLint : Prop := ∀ (D : D7) (n t : ℕ) (B W : HSp D) (d : HypDec B W t) (I : IkD d n) θ, IsInfFam θ →
  ∀ M ∈ schwartzA θ B.rank n, (∀ x, 0 ≤ (M x).re ∧ (M x).im = 0) → ∀ a : Mx D W.rank n,
    ∫⁻ U, ∫⁻ k : I.l.K, ‖M (mm (mt B ((k : GA D B)⁻¹)) (mm d.jX U + mm d.j0 a))‖ₑ ∂I.νK ∂I.μ₁ = ‖ikp I M a‖ₑ

def Fub4 : Prop := ∀ (α β γ δ : Type) [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ] [MeasurableSpace δ]
  (a : Measure α) (b : Measure β) (c : Measure γ) (e : Measure δ) [SFinite a] [SFinite b] [SFinite c] [SFinite e],
  (∀ f : α × β × γ × δ → ℂ, Integrable f (a.prod (b.prod (c.prod e))) →
    ∫ p, f p ∂(a.prod (b.prod (c.prod e))) = ∫ y, ∫ h, ∫ u, ∫ k, f (k, h, u, y) ∂a ∂c ∂b ∂e) ∧
  (∀ f : α × β × γ × δ → ℝ≥0∞, Measurable f →
    ∫⁻ p, f p ∂(a.prod (b.prod (c.prod e))) = ∫⁻ y, ∫⁻ h, ∫⁻ u, ∫⁻ k, f (k, h, u, y) ∂a ∂c ∂b ∂e)

def Law : Prop := ∀ (D : D7) (n t : ℕ) (B W : HSp D) (d : HypDec B W t) (hn : W.rank + t = n) (I : IkD d n)
  (μ : Measure (Mx D W.rank t)), μ.IsAddHaarMeasure → ∀ x₀ (q : GlobalTheory.RegSW.stab d),
    (rho hn I μ x₀).map (ac B (q : GA D B)) = ((GlobalTheory.RegSW.absDet d q)⁻¹ ^ (W.rank + t) : ℝ≥0) • rho hn I μ x₀

def core {D : D7} {n t : ℕ} {B W : HSp D} {d : HypDec B W t} (hn : W.rank + t = n) (I : IkD d n) (x₀ : Matrix (Fin W.rank) (Fin W.rank) D.host.E)
    (Φ : Mx D B.rank n → ℂ) (η : Mx D W.rank t → ℂ) (p : I.l.K × Par D n t W) : ℂ :=
  Φ (mm (mt B ((p.1 : GA D B)⁻¹)) (mm (XU d hn x₀ p.2.1 p.2.2.1) (bl hn 1 p.2.2.2 0 1))) * conj (η p.2.2.2)

end GlobalTheory.CompanionTheory.ColumnSplitting

end
