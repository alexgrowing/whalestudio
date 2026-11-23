import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.TwistedSlicesSquareIntegrable

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec

namespace PositivityTheory.Rg.Rs.SatakeVectors

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E]

theorem absNorm_cpow_ne_zero (w : HeightOneSpectrum (𝓞 E)) (s : ℂ) :
    (((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ s) ≠ 0 := by
  have h : ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.2 (NumberField.HeightOneSpectrum.one_lt_absNorm w).ne_bot
  exact fun e => h ((Complex.cpow_eq_zero_iff _ _).1 e).1

def qU (w : HeightOneSpectrum (𝓞 E)) (s : ℂ) : ℂˣ :=
  Units.mk0 (((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ s) (absNorm_cpow_ne_zero w s)

@[simp] theorem qU_val (w : HeightOneSpectrum (𝓞 E)) (s : ℂ) :
    ((qU w s : ℂˣ) : ℂ) = ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ s := rfl

def SatLike {m : ℕ} (U : Submodule ℂ (Sm E m)) (w : HeightOneSpectrum (𝓞 E)) (S : Multiset ℂˣ) : Prop :=
  ∀ ψ ∈ U, (∀ k ∈ GlobalTheory.LFun.KGL w m, finRep E m (locGL E m w k) ψ = ψ) → ψ ≠ 0 →
    GlobalTheory.LFun.IsSatVecGL w ((finRep E m).comp (locGL E m w)) ψ S

theorem satLike_of_satV {m : ℕ} {V : Submodule ℂ (Sm E m)} {w : HeightOneSpectrum (𝓞 E)} {B : Multiset ℂˣ}
    (h : SatV V w B) : SatLike V w B := h.2

theorem satTw_eq (w : HeightOneSpectrum (𝓞 E)) (z : ℂ) (B : Multiset ℂˣ) :
    satTw w z B = (B.map (· * qU w (-z))).map fun b : ℂˣ => (b : ℂ) := by
  simp [satTw, Multiset.map_map, Function.comp_def]

end PositivityTheory.Rg.Rs.SatakeVectors

end
