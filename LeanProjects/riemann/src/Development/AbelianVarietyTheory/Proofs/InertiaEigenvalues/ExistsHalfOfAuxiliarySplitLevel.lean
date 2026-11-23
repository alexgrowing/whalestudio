import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.RationalRayLevels
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsHalfOfBasePins
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.MainNotions.StandardLattice Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.CoverRead

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HalfCharacter

theorem exists_half_of_auxiliary_split_level : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ pd : ℕ, GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.IsAuxiliarySplitSquarefreeLevel D T.Q.l.M pd →
  ∃ I : Ideal (𝓞 D.host.E), I = Ideal.span {x | x ∈ I ∧ x ∈ Algebra.adjoin ℤ {T.Q.H.w0}} ∧
    I * I.map (T.Q.H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) = Ideal.span {(pd : 𝓞 D.host.E)} ∧
    I ⊔ I.map (T.Q.H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) = ⊤ := by
  intro D T hJ pd haux
  obtain ⟨hodd, -, hjac, -, -⟩ := haux
  have hH : T.Q.PinHost := hJ.toLawsM.pins.1
  have hw : T.Q.H.w0 = w0E D := by
    have h1 := T.Q.H.two_weight_eq_one_add_root
    have h3 : T.Q.H.rt = rtE D := RingOfIntegers.ext hH.2.1
    rw [h3, ← two_w0E D] at h1
    exact mul_left_cancel₀ two_ne_zero h1
  have hb : (T.Q.H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) = bH D :=
    RingHom.ext fun a => RingOfIntegers.ext (T.Q.H.bar_eq a)
  have hsp : ∀ p ∈ pd.primeFactorsList, SplitOK D p := by
    intro p hp
    have hpr := Nat.prime_of_mem_primeFactorsList hp
    have hdvd := Nat.dvd_of_mem_primeFactorsList hp
    refine ⟨hpr, ?_, hjac p hpr hdvd⟩
    rintro rfl
    exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 hdvd)
  have hpd0 : pd ≠ 0 := hodd.pos.ne'
  refine ⟨MbOf D pd.primeFactorsList, ?_, ?_, ?_⟩
  · rw [hw]; exact MbOf_fromK D _
  · rw [hb]
    have h := MbProd_of D pd.primeFactorsList hsp
    unfold MbProdLaw at h
    rw [h, Nat.prod_primeFactorsList hpd0]
  · rw [hb]; exact MbCop_of D _ hsp

end GlobalTheory.HalfCharacter
