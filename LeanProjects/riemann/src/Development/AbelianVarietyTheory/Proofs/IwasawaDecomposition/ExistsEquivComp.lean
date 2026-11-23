import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FlagComponentFramedPointFrame
import Formalism.LocalToGlobal.ProjectiveLattices.MulCMemSec
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
import Formalism.LocalToGlobal.ProjectiveLattices.CompSplitPfD
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.LinearDisjointAlgebraicClosure
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsComponentOfModelCharts

noncomputable section

namespace GlobalTheory.UnifComp

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj
  GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.AllWt

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem ptF_frMap {S T : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T]
    {φ : S →ₐ[c.F] T} {y : FrPt Xo c S} {z : FrPt Xo c T} (h : FrMap φ y z) :
    ptF z = spMap φ.toRingHom ≫ ptF y := by
  apply pullback.hom_ext
  · rw [ptF, pullback.lift_fst, Category.assoc, ptF, pullback.lift_fst, h.1]
  · rw [ptF, pullback.lift_snd, Category.assoc, ptF, pullback.lift_snd, ← Spec.map_comp]
    congr 1
    ext a
    exact (φ.commutes a).symm

theorem ptF_frBor {S : Type} [CommRing S] [Algebra c.F S] {t : Ix Dw → Sˣ} {y z : FrPt Xo c S}
    (h : FrBor t y z) : ptF z = ptF y := by
  apply pullback.hom_ext
  · rw [ptF, pullback.lift_fst, ptF, pullback.lift_fst, h.1]
  · rw [ptF, pullback.lift_snd, ptF, pullback.lift_snd]

theorem liesOn_chart {h : GenFrEx Xo c} (C : GlobalTheory.Reg.FChart h) : LiesOn C.Z C.y := by
  intro s
  let η : Sp C.R := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum C.R)
  let s₀ : Sp (Om C.Z) := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (Om C.Z))
  have e : spMap C.R.val.toRingHom s₀ = η :=
    PrimeSpectrum.ext (Ideal.comap_bot_of_injective C.R.val.toRingHom Subtype.val_injective)
  have h1 : ptF C.y η ∈ (C.Z : Set (Xo.XF c)) := by
    have := liesOn_genFr h C.Z s₀
    rw [← ptF_frBor C.bor, ptF_frMap C.gen, Scheme.Hom.comp_apply, e] at this
    exact this
  have h2 : η ⤳ s := (PrimeSpectrum.le_iff_specializes (R := C.R) _ _).1 bot_le
  exact (h2.map (ptF C.y).continuous).mem_closed (isClosed_of_mem_irreducibleComponents _ C.Z.2) h1

theorem exists_liesOn {σ : c.F →+* ℂ} {r : ℕ} (U : Formalism.L2.PjFree.Unf Xo c σ r) (hU : Formalism.L2.PjFree.IsUnf U)
    (k : U.Comp) : ∃ Z : Comp Xo c, ∀ x : (U.X k).dom, LiesOn Z (U.un k x) := by
  obtain ⟨-, -, h, hA⟩ := GlobalTheory.Reg.evLaws_genFr_atlas E H Dw l Xo c
  obtain ⟨Z, hZ⟩ := GlobalTheory.OneComp.exists_comp_of_charts E H Dw l Xo c σ r U hU h k
  refine ⟨Z, fun x s => ?_⟩
  letI : Field (CAt σ) := inferInstanceAs (Field ℂ)
  obtain ⟨C, ψ, z, t, hz, hb⟩ := hA h (CAt σ) (U.un k x)
  rw [← hZ x C ψ z t hz hb, ptF_frBor hb, ptF_frMap hz, Scheme.Hom.comp_apply]
  exact liesOn_chart C _

theorem eq_of_carries {σ : c.F →+* ℂ} {r : ℕ} {U : Formalism.L2.PjFree.Unf Xo c σ r} {h : GenFrEx Xo c} {k : U.Comp}
    {Z Z' : Comp Xo c} (hk : GlobalTheory.CompModel.CarriesGeneric U h k Z) (h' : ∀ x : (U.X k).dom, LiesOn Z' (U.un k x)) :
    Z' = Z := by
  obtain ⟨P, w, x, t, hw, ht⟩ := hk
  by_contra hne
  let s : Sp (CAt σ) := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum ℂ)
  refine Set.disjoint_left.1 (CompSplitPfD.cspD_comp_disj Xo c Z' Z hne) (h' x s) ?_
  rw [← ptF_frBor ht, ptF_frMap hw, Scheme.Hom.comp_apply]
  exact liesOn_genFr h Z _

theorem exists_equiv_comp : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (N : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ N), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → (∀ k, (U.X k).dom.Nonempty) → FnAlgClosed Xo c → ∃ q : U.Comp ≃ Comp Xo c, ∀ k (x : (U.X k).dom) (s : Sp (CAt σ)), GlobalTheory.AllWt.ptF (U.un k x) s ∈ (q k).1 := by
  intro E _ _ _ H Dw l Xo c σ N U hσ hU _ hF
  obtain ⟨-, -, h, -⟩ := GlobalTheory.Reg.evLaws_genFr_atlas E H Dw l Xo c
  choose q hq using exists_liesOn U hU
  refine ⟨Equiv.ofBijective q ⟨fun k k' e => ?_, fun Z => ?_⟩, fun k x s => hq k x s⟩
  · obtain ⟨Z, hZ⟩ := GlobalTheory.CompModel.exists_comp U hσ hU h k
    obtain ⟨Z', hZ'⟩ := GlobalTheory.CompModel.exists_comp U hσ hU h k'
    obtain rfl : Z = Z' := (eq_of_carries hZ (hq k)).symm.trans (e.trans (eq_of_carries hZ' (hq k')))
    obtain ⟨P, w, x, t, hw, ht⟩ := hZ
    obtain ⟨P', w', x', t', hw', ht'⟩ := hZ'
    exact GlobalTheory.GeomConn.comp_eq_of_fnAlgClosed E H Dw l Xo c σ N U.toPj hσ hU hF h Z k k' x x'
      ⟨P, w, t, hw, ht⟩ ⟨P', w', t', hw', ht'⟩
  · obtain ⟨k, hk⟩ := GlobalTheory.CompModel.exists_model U hU h Z
    exact ⟨k, eq_of_carries hk (hq k)⟩

end GlobalTheory.UnifComp
