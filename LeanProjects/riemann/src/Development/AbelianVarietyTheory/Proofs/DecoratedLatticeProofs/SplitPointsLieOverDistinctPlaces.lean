import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TwTransAlt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseFieldsPrimesOk
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
import Formalism.LocalToGlobal.Columns.BaseLemmas

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AdForm.PlacesDistinct

variable {D : D7}

theorem placeIdem_unique {v : HeightOneSpectrum (𝓞 D.host.F)} {ε ε' : AF D.host.F}
    (h : IsPlaceIdem D v ε) (h' : IsPlaceIdem D v ε') : ε = ε' := by
  obtain ⟨α, rfl, h1, h2⟩ := h
  obtain ⟨α', rfl, h1', h2'⟩ := h'
  congr 1
  refine RestrictedProduct.ext _ _ fun u => ?_
  by_cases hu : u = v
  · subst hu
    exact h1.trans h1'.symm
  · exact (h2 u hu).trans (h2' u hu).symm

theorem finPart_idem_int {e : AE D} {w : HeightOneSpectrum (𝓞 D.host.E)} (h : Formalism.L2.NTheta.IsIdemAt e w) :
    finPart D e ∈ intAE D := by
  have h1 := (h.2 1 one_ne_zero).not
  have hw : (1 : 𝓞 D.host.E) ∉ w.asIdeal := fun h => w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h)
  have := not_not.1 (h1.1 hw)
  simpa using this

theorem conj_mem_of {e e' : AE D} {w w' : HeightOneSpectrum (𝓞 D.host.E)} (h : Formalism.L2.NTheta.IsIdemAt e w)
    (h' : Formalism.L2.NTheta.IsIdemAt e' w') (hsum : e + cA D e = e' + cA D e') {x x' : 𝓞 D.host.E} (hx' : (x' : D.host.E) = star (x : D.host.E))
    (hx0 : x ≠ 0) (hxw : x ∈ w.asIdeal) (hxw' : x ∉ w'.asIdeal) : x' ∈ w'.asIdeal := by
  have hx'0 : x' ≠ 0 := by
    intro h0
    apply hx0
    have : star (x : D.host.E) = 0 := by rw [← hx', h0]; rfl
    exact RingOfIntegers.coe_eq_zero_iff.mp (star_eq_zero.mp this)
  have hN : finPart D (e * incA D ((x : D.host.E)⁻¹)) ∉ intAE D := (h.2 x hx0).1 hxw
  have hI' : finPart D (e' * incA D ((x : D.host.E)⁻¹)) ∈ intAE D := not_not.1 (mt (h'.2 x hx0).2 hxw')
  have he := finPart_idem_int h
  have hee : e = e * e' + e * cA D e' := by
    rw [← mul_add, ← hsum, mul_add, h.1.1, h.1.2.1, add_zero]
  have hsplit : e * incA D ((x : D.host.E)⁻¹) =
      e * (e' * incA D ((x : D.host.E)⁻¹)) + e * (cA D e' * incA D ((x : D.host.E)⁻¹)) := by
    conv_lhs => rw [hee]
    ring
  have hA : finPart D (e * (e' * incA D ((x : D.host.E)⁻¹))) ∈ intAE D := by
    rw [map_mul]; exact GlobalTheory.FinPl.FrameLat.mul_mem_intAE he hI'
  have hB : finPart D (cA D e' * incA D ((x : D.host.E)⁻¹)) ∉ intAE D := by
    intro hB
    apply hN
    rw [hsplit, map_add]
    refine add_mem hA ?_
    rw [map_mul]; exact GlobalTheory.FinPl.FrameLat.mul_mem_intAE he hB
  have hC : cA D e' * incA D ((x : D.host.E)⁻¹) = cA D (e' * incA D ((x' : D.host.E)⁻¹)) := by
    rw [map_mul, GlobalTheory.FinPl.FrameLat.cA_incA, hx', star_inv₀, star_star]
  rw [hC, GlobalTheory.FinPl.FrameLat.cA_int_iff] at hB
  exact (h'.2 x' hx'0).2 hB

theorem prime_eq {e e' : AE D} {w w' : HeightOneSpectrum (𝓞 D.host.E)} (h : Formalism.L2.NTheta.IsIdemAt e w)
    (h' : Formalism.L2.NTheta.IsIdemAt e' w') (hsum : e + cA D e = e' + cA D e') {π π' : 𝓞 D.host.E}
    (hπ' : (π' : D.host.E) = star (π : D.host.E)) (hw : π ∈ w.asIdeal) (hw' : π ∈ w'.asIdeal)
    (hc : π' ∉ w'.asIdeal) : w = w' := by
  by_contra hne
  have hnle : ¬ w.asIdeal ≤ w'.asIdeal := by
    intro hle
    apply hne
    exact HeightOneSpectrum.ext (w.isMaximal.eq_of_le w'.isPrime.ne_top hle)
  obtain ⟨x₀, hx₀w, hx₀w'⟩ := Set.not_subset.1 hnle
  have hx₀0 : x₀ ≠ 0 := fun h0 => hx₀w' (h0 ▸ w'.asIdeal.zero_mem)
  have hy : π + x₀ ∉ w'.asIdeal := fun hm => hx₀w' (by simpa using w'.asIdeal.sub_mem hm hw')
  have hy0 : π + x₀ ≠ 0 := fun h0 => hy (h0 ▸ w'.asIdeal.zero_mem)
  obtain ⟨c₀, hc₀⟩ : ∃ c : 𝓞 D.host.E, (c : D.host.E) = star (x₀ : D.host.E) :=
    ⟨⟨star (x₀ : D.host.E), (x₀.2).map (starRingEnd D.host.E).toIntAlgHom⟩, rfl⟩
  have h1 : c₀ ∈ w'.asIdeal := conj_mem_of h h' hsum hc₀ hx₀0 hx₀w hx₀w'
  have h2 : π' + c₀ ∈ w'.asIdeal :=
    conj_mem_of h h' hsum (x := π + x₀) (by push_cast; rw [star_add]; exact congrArg₂ (· + ·) hπ' hc₀) hy0 (w.asIdeal.add_mem hw hx₀w) hy
  exact hc (by simpa using w'.asIdeal.sub_mem h2 h1)

end GlobalTheory.AdForm.PlacesDistinct

open GlobalTheory.AdForm.PlacesDistinct in

theorem GlobalTheory.AdForm.StdT.places_injective : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word)
    {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {ι : Type}
    (p : ι → SplitPt (I.rec7 l Z) k) (β : ∀ j i, Frame (p i) ((I.rec7 l Z).sp.X j) (Fin ((I.rec7 l Z).sp.X j).rank))
    (Q : ∀ j, ι → Pair k (Fin ((I.rec7 l Z).sp.X j).rank)) (L : ∀ j, Lat ((I.rec7 l Z).sp.X j)),
    GlobalTheory.AdForm.StdT I l Z u p β Q L → Function.Injective fun i => (p i).v := by
  intro B X I _ _ l Z u k _ _ _ _ ι p β Q L hS
  obtain ⟨⟨e, he⟩, -⟩ := hS
  obtain ⟨-, hPr, -⟩ := GlobalTheory.Mem.Col2.base_fields_primes_ok B X
  have hcop : IsCoprime (X.piT u) (B.fields.conjO (X.piT u)) := hPr.piT_cop u
  have hne : X.piT u ≠ 0 := by
    intro h0
    rw [h0, map_zero, isCoprime_zero_left] at hcop
    exact not_isUnit_zero hcop
  intro i i' hv
  have hv : (p i).v = (p i').v := hv
  apply e.injective
  apply Subtype.ext
  have hmem : ∀ j, X.piT u ∈ (e j).1.asIdeal := fun j => (Formalism.L2.Col.mem_divs hne _).1 (e j).2
  obtain ⟨ε, hε, hε'⟩ := (p i).above
  obtain ⟨ε', hε2, hε2'⟩ := (p i').above
  rw [hv] at hε
  have hsum : (p i).e + cA (I.rec7 l Z) (p i).e = (p i').e + cA (I.rec7 l Z) (p i').e := by
    rw [hε', hε2', placeIdem_unique hε hε2]
  refine prime_eq (he i) (he i') hsum (π := X.piT u) (π' := B.fields.conjO (X.piT u)) rfl (hmem i) (hmem i') ?_
  intro hc
  obtain ⟨a, b, hab⟩ := hcop
  exact (e i').1.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
    (hab ▸ (e i').1.asIdeal.add_mem (Ideal.mul_mem_left _ a (hmem i')) (Ideal.mul_mem_left _ b hc)))

end
