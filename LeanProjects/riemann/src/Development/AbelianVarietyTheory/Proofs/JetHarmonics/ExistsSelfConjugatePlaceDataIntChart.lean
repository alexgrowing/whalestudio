import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.IsSelfOf
import Development.AbelianVarietyTheory.Definitions.Jets.TwoPlaces
import Formalism.LocalToGlobal.CharacterGerms.RowTieLab
import Formalism.LocalToGlobal.CharacterGerms.RowTieTop
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsMatrixStandardToHyperbolicInertPlaceStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CmEmbeddingsIntegralAndDistinctModMaximalStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsIdempotentFrobeniusOrbitUnramifiedStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SeparatedEmbeddingsDirectionsTypedBasisStatement

open scoped BigOperators TensorProduct
open Classical NumberField IsDedekindDomain Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.DIV Formalism.BasicNotions GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.GoodDepth
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.RowAt

theorem sum_sigma_extend {A C W : Type} [Fintype A] [Field C] [AddCommGroup W] [Module C W] (m : A → ℕ)
    (e : (Σ s : A, Fin (m s)) → W) (a : A) (b : Fin (m a) → C) :
    ∃ b' : (Σ s : A, Fin (m s)) → C, (∀ q, q.1 ≠ a → b' q = 0) ∧ ∑ x, b x • e ⟨a, x⟩ = ∑ q, b' q • e q := by
  refine ⟨fun q => if h : q.1 = a then b (h ▸ q.2) else 0, fun q hq => dif_neg hq, ?_⟩
  rw [Fintype.sum_sigma, Finset.sum_eq_single a]
  · simp
  · intro s _ hs
    simp [hs]
  · simp

theorem card_sigma_fst_add {d : ℕ} [NeZero d] (m : ZMod d → ℕ) (h a : ZMod d) :
    (Finset.univ.filter fun x : (Σ a : ZMod d, Fin (m a)) => x.1 + h = a).card = m (a - h) := by
  rw [← card_sigma_fst m (a - h)]
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact eq_sub_iff_add_eq.symm

theorem exists_selfData : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (lv : Level H) (Xo : Moduli Dw lv) (c : Coeff lv) [StarRing (𝓞 E)], (∀ x : 𝓞 E, star x = H.bar x) → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C3 : IntChart T io y) (C : Type) [Field C] [CharZero C] (V : VF C) (ι : T.Fr →+* C), EmbOK T V ι → ∀ (k : ℕ) (Y : FBChart C V (𝓞 E) (chD C3.ch)), IsBC C3 ι k Y → ∀ (Orb : Type) [Fintype Orb] (lab : LabS E Orb), ArithS V io ι lab → ∃ p : ∀ o, SelfData Y 2 (lab.II Dw o), IsSelfOf C3 ι Y lab p ∧ SelfSep Y p ∧ (lab.RankOK Dw → ∀ o, (Y.rawSelf (p o)).RankHyp ∧ (Y.rawSelf (p o)).AltC) := by
  intro E _ _ _ H Dw lv Xo c _ hstar T io y C3 C _ _ V ι hι k Y hY Orb _ lab ha
  obtain ⟨hint, hsep⟩ := GlobalTheory.T.cmEmbeddings_integral_and_distinct_mod_maximal E H lv c T io C V ι hι ha.unr
  have hsep' : ∀ x x' : Orb × ZMod 2, x ≠ x' →
      ∃ a : 𝓞 E, V.v (emA3 io ι (lab.tau x.1 x.2) a - emA3 io ι (lab.tau x'.1 x'.2) a) = 0 :=
    fun x x' h => hsep _ _ fun e => h (ha.inj e)
  have hsep1 : ∀ o (s s' : ZMod 2), s ≠ s' →
      ∃ a : 𝓞 E, V.v (emA3 io ι (lab.tau o s) a - emA3 io ι (lab.tau o s') a) = 0 :=
    fun o s s' h => hsep' (o, s) (o, s') fun e => h (Prod.mk.inj e).2
  have hconj : ∀ o (a : ZMod 2) (x : 𝓞 E), emA3 io ι (lab.tau o a) (star x) = emA3 io ι (lab.tau o (a + 1)) x := by
    intro o a x
    rw [ha.conj o a, embedding_conjugate hstar]
  have hgeo := fun o => GlobalTheory.T.separatedEmbeddings_directions_typedBasis E H Dw lv Xo c hstar T io y C3 C V ι hι k Y hY (ZMod 2) (lab.tau o) (hsep1 o)
  have := Y.algClosed
  have hgm := fun o => GlobalTheory.T.exists_matrix_standard_to_hyperbolic_inertPlace C V Y.l_odd Y.cpl (𝓞 E) (fun a => emA3 io ι (lab.tau o a))
    (fun a x => hint _ x) (ha.frob o) (hsep1 o 0 1 (by decide)) (hconj o)
  choose gm hlim hhyp using hgm
  let p : ∀ o, SelfData Y 2 (lab.II Dw o) := fun o =>
    { em := fun a => emA3 io ι (lab.tau o a)
      em_int := fun a x => hint _ x
      em_frob := ha.frob o
      em_sep := hsep1 o
      em_unr := GlobalTheory.T.exists_idempotent_frobeniusOrbit_unramified E H lv c T io C V ι hι ha.unr 2 (lab.tau o) (ha.frob o)
      hd := 1
      hd_ne := by decide
      hd_two := by decide
      em_conj := hconj o
      e := fun x i => ι (chartUnitVectors C3 ⟨lab.tau o x.1, x.2⟩ i)
      ty0 := fun x => x.1
      e_int := fun x i => (hgeo o).1 x.1 x.2 i
      e_eig := fun x a => (hgeo o).2.1 x.1 x.2 a
      e_sat := by
        obtain ⟨w, h1, h2⟩ := (hgeo o).2.2.1
        exact ⟨w, h1, fun q q' => by convert h2 q q'⟩
      e_full := fun a v hv => by
        obtain ⟨b, hb⟩ := (hgeo o).2.2.2 a v hv
        obtain ⟨b', h1, h2⟩ := sum_sigma_extend (fun s => Dw.mult (lab.tau o s))
          (fun (x : lab.II Dw o) i => ι (chartUnitVectors C3 ⟨lab.tau o x.1, x.2⟩ i)) a b
        exact ⟨b', h1, hb.trans h2⟩
      gm := gm o
      gm_lim := hlim o
      gm_hyp := hhyp o
      n := lab.n
      j := lab.j
      j' := lab.j'
      big := fun g s => s = ((g.val : ℕ) : ZMod 2) }
  refine ⟨p, ⟨fun _ _ => rfl, fun _ => rfl, fun _ _ _ => rfl, fun _ _ => rfl, fun _ => rfl, fun _ => rfl,
    fun _ => rfl, fun _ _ _ => Iff.rfl⟩, hsep', fun hr o => ⟨⟨?_, ?_, ?_⟩, by decide, ?_⟩⟩
  · show ∀ (g : Fin 2) (a : ZMod 2), a = (((1 - g).val : ℕ) : ZMod 2) ↔ ¬ a = ((g.val : ℕ) : ZMod 2)
    decide
  · intro g a hb
    change a = ((g.val : ℕ) : ZMod 2) at hb
    subst hb
    fin_cases g
    · exact (card_sigma_fst (fun a => Dw.mult (lab.tau o a)) _).trans (hr o).1
    · exact (card_sigma_fst_add (fun a => Dw.mult (lab.tau o a)) 1 _).trans (hr o).1
  · intro g a hb
    change ¬ a = ((g.val : ℕ) : ZMod 2) at hb
    fin_cases g
    · obtain rfl : a = 1 := by revert hb; revert a; decide
      exact (card_sigma_fst (fun a => Dw.mult (lab.tau o a)) _).trans (hr o).2
    · obtain rfl : a = 0 := by revert hb; revert a; decide
      exact (card_sigma_fst_add (fun a => Dw.mult (lab.tau o a)) 1 _).trans (hr o).2
  · show ∀ a : ZMod 2, a = (((0 : Fin 2).val : ℕ) : ZMod 2) ↔ Even a.val
    decide

end GlobalTheory.RowAt
