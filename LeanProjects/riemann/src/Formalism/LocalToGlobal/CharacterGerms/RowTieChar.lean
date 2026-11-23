import Formalism.LocalToGlobal.CharacterGerms.RowTieTop

set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ}
  {I : Fin 2 → Type} [∀ g, Fintype (I g)]

def FBChart.IsChar (Y : FBChart C V O dd) (χ : PS C 1 dd) : Prop :=
  IntS V χ ∧ MvPowerSeries.constantCoeff χ = 1 ∧
    ev (n := 2) ![addOf Y.B.G.F (pt C dd 0) (pt C dd 1)] χ = ev (n := 2) ![pt C dd 0] χ * ev (n := 2) ![pt C dd 1] χ

def dlogC (χ : PS C 1 dd) (i : Fin dd) : C := MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), i) 1) χ

def PairData.yOf {Y : FBChart C V O dd} (p : PairData Y d I) (g : Fin 2) (χ : PS C 1 dd) (x : I g) : C :=
  ∑ i, dlogC χ i * p.u g x i

private theorem ge_zero_mul_of_vf (V : VF C) {a b : C} (ha : V.Ge 0 a) (hb : V.Ge 0 b) : V.Ge 0 (a * b) := by
  unfold VF.Ge at *
  rw [V.v.map_mul]
  rw [WithTop.coe_zero] at *
  exact add_nonneg ha hb

private theorem ge_zero_finset_sum (V : VF C) {ι : Type} (s : Finset ι) (f : ι → C) (h : ∀ i ∈ s, V.Ge 0 (f i)) :
    V.Ge 0 (∑ i ∈ s, f i) := by
  classical
  revert h
  refine Finset.induction_on s ?_ ?_
  · intro _
    rw [Finset.sum_empty]
    unfold VF.Ge
    rw [AddValuation.map_zero]
    exact le_top
  · intro a s ha ih h
    rw [Finset.sum_insert ha]
    have h1 := h a (Finset.mem_insert_self a s)
    have h2 := ih fun i hi => h i (Finset.mem_insert_of_mem hi)
    unfold VF.Ge at h1 h2 ⊢
    exact le_trans (le_min h1 h2) (V.v.map_add _ _)

theorem PairData.yOf_int {Y : FBChart C V O dd} (p : PairData Y d I) (g : Fin 2) {χ : PS C 1 dd} (h : Y.IsChar χ)
    (x : I g) : V.Ge 0 (p.yOf g χ x) := by
  unfold PairData.yOf
  exact ge_zero_finset_sum V _ _ fun i _ => ge_zero_mul_of_vf V (h.1 _) (p.u_int g x i)

def CharGermSt : Prop :=
  ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ)
    (Y : FBChart C V O dd) (d : ℕ) [NeZero d] (I : Fin 2 → Type) [∀ g, Fintype (I g)] (p : PairData Y d I)
    (Hc : ∀ g, (Y.raw p).CartHyp V g) (χ : PS C 1 dd), Y.IsChar χ →
    ∀ (g : Fin 2) (S : ∀ g, Sys (RawChart.cart (Hc g))) (t : ∀ g, I g → MvPowerSeries (I g) C), (∀ g, (S g).IsT (t g)) →
      upG g (mvExp (∑ x : I g, p.yOf g χ x • (MvPowerSeries.X x : MvPowerSeries (I g) C))) ∈ IntGerm V t

def CHCharSt (Y : FBChart C V O dd) (p : PairData Y d I) : Prop :=
  ∀ g a, p.big g a → ∀ w : Fin p.n → I g → C, IsSat V w → (∀ c x, p.ty g x ≠ a → w c x = 0) →
    ∃ χ : Fin p.n → PS C 1 dd, (∀ ρ, Y.IsChar (χ ρ)) ∧
      ((Y.raw p).AltC →
        V.v (Matrix.of fun ρ c : Fin p.n => ∑ x, p.yOf g (χ ρ) x * w c x).det ≤
          (((p.n : ℝ) * gam V.l + ((p.j : ℝ) + p.j') / ((V.l : ℝ) - 1) : ℝ) : WithTop ℝ)) ∧
      ((∀ a, p.big g a) →
        V.v (Matrix.of fun ρ c : Fin p.n => ∑ x, p.yOf g (χ ρ) x * w c x).det ≤
          ((((p.j : ℝ) + p.j') / ((V.l : ℝ) - 1) : ℝ) : WithTop ℝ))

theorem chSt_of_char [NeZero d] (hG : CharGermSt) (Y : FBChart C V O dd) (p : PairData Y d I) (h : CHCharSt Y p)
    (Hc : ∀ g, (Y.raw p).CartHyp V g) : RawChart.CHSt Hc := by
  intro g a hbig w hw hw0
  obtain ⟨χ, hχ, h1, h2⟩ := h g a hbig w hw hw0
  refine ⟨fun ρ x => p.yOf g (χ ρ) x, fun ρ x => p.yOf_int g (hχ ρ) x, ?_, h1, h2⟩
  intro S t ht ρ
  exact hG C V O dd Y d I p Hc (χ ρ) (hχ ρ) g S t ht

section Chart

open Formalism.L2.Pj NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)]

def CharacterHypothesisCharts : Prop :=
  (∀ a : 𝓞 E, star a = H.bar a) →
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C3 : IntChart T io y)
    (C : Type) [Field C] [CharZero C] (V : VF C) (ι : T.Fr →+* C), EmbOK T V ι →
    ∀ (k : ℕ) (Y : FBChart C V (𝓞 E) (chD C3.ch)), IsBC C3 ι k Y →
    ∀ (Orb : Type) (d : ℕ) [NeZero d] (lab : Lab E Orb d) (ha : LabArith V io ι lab) (hg : LabGeo C3 ι Y lab),
    lab.RankOK Dw → ∀ o, CHCharSt Y (pairOfLab ha hg o)

theorem chart_hypothesis_of_character (hG : CharGermSt) (h : CharacterHypothesisCharts Xo c) : CharacterHypothesisAllCharts Xo c := by
  intro hs T io y C3 C _ _ V ι hemb k Y hbc Orb d _ lab ha hg hrk o Hc
  exact chSt_of_char hG Y _ (h hs T io y C3 C V ι hemb k Y hbc Orb d lab ha hg hrk o) Hc

end Chart

end Formalism.L2.FormalSeriesBounds
