import Mathlib
import Development.AutomorphicArithmetic.OrbitLabellings.RowDefs
import Formalism.LocalToGlobal.CharacterGerms.RowTieMemCFin
import Formalism.LocalToGlobal.CharacterGerms.RowTieFlagS
import Formalism.LocalToGlobal.CharacterGerms.RowTieSelfCuts
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SeparatedEmbeddingsDirectionsTypedBasisStatement

open scoped BigOperators
open Classical
open Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.RF UpperTheory.G2 NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

private theorem UpperTheory.extend_sigma_coefficients_by_zero {A C W : Type} [Fintype A] [Field C] [AddCommGroup W] [Module C W] (m : A → ℕ)
    (e : (Σ s : A, Fin (m s)) → W) (a : A) (b : Fin (m a) → C) :
    ∃ b' : (Σ s : A, Fin (m s)) → C, (∀ q, q.1 ≠ a → b' q = 0) ∧ ∑ x, b x • e ⟨a, x⟩ = ∑ q, b' q • e q := by
  refine ⟨fun q => if h : q.1 = a then b (h ▸ q.2) else 0, fun q hq => dif_neg hq, ?_⟩
  rw [Fintype.sum_sigma, Finset.sum_eq_single a]
  · simp
  · intro s _ hs
    simp [hs]
  · simp

theorem UpperTheory.labelSetGeo_of_labelSetArith :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (lv : Level H)
    (Xo : Moduli Dw lv) (c : Coeff lv) [StarRing (𝓞 E)], (∀ x : 𝓞 E, star x = H.bar x) →
    ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C3 : IntChart T io y) (C : Type) [Field C] [CharZero C] (V : VF C)
    (ι : T.Fr →+* C), EmbOK T V ι → ∀ (k : ℕ) (Y : FBChart C V (𝓞 E) (chD C3.ch)), IsBC C3 ι k Y →
    ∀ (Orb : Type) [Fintype Orb] (d : ℕ) [NeZero d] (lab : Formalism.L2.FormalSeriesBounds.LabS E C Orb d) (ha : LabSArith V io ι lab),
    LabSGeo C3 ι Y lab := by
  intro E _ _ _ H Dw lv Xo c _ hstar T io y C3 C _ _ V ι hι k Y hY Orb _ d _ lab ha
  have hsep1 : ∀ o (s s' : ZMod d), s ≠ s' →
      ∃ a : 𝓞 E, V.v (emA3 io ι (lab.tau o s) a - emA3 io ι (lab.tau o s') a) = 0 :=
    fun o s s' h => ha.sep (o, s) (o, s') fun e => h (Prod.mk.inj e).2
  have hgeo := fun o => GlobalTheory.T.separatedEmbeddings_directions_typedBasis E H Dw lv Xo c hstar T io y C3 C V ι hι k Y hY (ZMod d) (lab.tau o) (hsep1 o)
  refine labSGeo_of hstar hι ha ⟨fun o x a => (hgeo o).2.1 x.1 x.2 a, fun o => ?_, fun o a v hv => ?_⟩
  · obtain ⟨w, h1, h2⟩ := (hgeo o).2.2.1
    exact ⟨w, h1, fun q q' => (h2 q q').trans (by congr)⟩
  · obtain ⟨b, hb⟩ := (hgeo o).2.2.2 a v hv
    obtain ⟨b', h1, h2⟩ := UpperTheory.extend_sigma_coefficients_by_zero (fun s => Dw.mult (lab.tau o s)) (selfLieBasisVector C3 ι lab o) a b
    exact ⟨b', h1, hb.trans h2⟩
