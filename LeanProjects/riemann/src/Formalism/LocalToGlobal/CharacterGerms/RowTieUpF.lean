import Formalism.LocalToGlobal.CharacterGerms.ChartHypothesisOfCharacters

set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ CharacteristicFromRanks

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ} [NeZero d]
  {I : Fin 2 → Type} [∀ g, Fintype (I g)]

def UPCharSt (Y : FBChart C V O dd) (p : PairData Y d I) (Hc : ∀ g, (Y.raw p).CartHyp V g) : Prop :=
  ∃ (h : Fin 2 → ℕ) (χ : ∀ g, Fin (h g) → PS C 1 dd), (∀ g i, Y.IsChar (χ g i)) ∧
    ∀ g a, p.big g a →
      ∃ e : Fin (pT (fun g => RawChart.cart (Hc g)) g a) ≃ {x : I g // (RawChart.cart (Hc g)).ty (Sum.inl x) = a},
        ((Y.raw p).AltC →
          S4.lenCoker V.v (Matrix.of fun c i => p.yOf g (χ g i) (e c)) ≤
            ((upB V.l (p.n + p.j) p.j' (gam V.l) : ℝ) : WithTop ℝ)) ∧
        ((∀ b, p.big g b) →
          S4.lenCoker V.v (Matrix.of fun c i => p.yOf g (χ g i) (e c)) ≤
            ((upB V.l (p.n + p.j) p.j' 0 : ℝ) : WithTop ℝ))

theorem chSt_of_upChar (Y : FBChart C V O dd) (p : PairData Y d I) (hr : (Y.raw p).RankHyp)
    (Hc : ∀ g, (Y.raw p).CartHyp V g) (h : UPCharSt Y p Hc) : RawChart.CHSt Hc := by
  obtain ⟨hh, χ, hχ, hUP⟩ := h
  exact CH_of_UP (fun g => RawChart.cart (Hc g)) p.n p.j p.j' p.big hr.big_compl hh
    (fun g i x => p.yOf g (χ g i) x) (fun g i x => p.yOf_int g (hχ g i) x) hUP
    (fun g i S t ht => charGerm_holds C V O dd Y d I p Hc (χ g i) (hχ g i) g S t ht)

section Chart

open Formalism.L2.Pj NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)]

def UpperCharacterCharts : Prop :=
  (∀ a : 𝓞 E, star a = H.bar a) →
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C3 : IntChart T io y)
    (C : Type) [Field C] [CharZero C] (V : VF C) (ι : T.Fr →+* C), EmbOK T V ι →
    ∀ (k : ℕ) (Y : FBChart C V (𝓞 E) (chD C3.ch)), IsBC C3 ι k Y →
    ∀ (Orb : Type) (d : ℕ) [NeZero d] (lab : Lab E Orb d) (ha : LabArith V io ι lab) (hg : LabGeo C3 ι Y lab),
    lab.RankOK Dw → ∀ o (Hc : ∀ g, (Y.raw (pairOfLab ha hg o)).CartHyp V g), UPCharSt Y (pairOfLab ha hg o) Hc

end Chart

end Formalism.L2.FormalSeriesBounds
