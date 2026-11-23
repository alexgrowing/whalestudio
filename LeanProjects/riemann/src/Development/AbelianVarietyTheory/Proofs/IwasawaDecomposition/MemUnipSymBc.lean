import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodAtOfFixRed
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiagGLConjApply
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsDiagonalConjEdgeSumAddCharFiniteField

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.SymFrame

variable {D : D7}

def EwAt (X : HidaSetting D) (w : HeightOneSpectrum (𝓞 D.host.E)) : Prop :=
  ∀ y ∈ X.B.I.Lf, (1 - X.ew) • y ∈ wLf X w

open Classical in

def epsW (X : HidaSetting D) (w : HeightOneSpectrum (𝓞 D.host.E)) : Fin D.R.k → VA X.B.I :=
  if EwAt X w then X.bw else fun i => X.bwd (Fin.rev i)

def symVec (X : HidaSetting D) (w : HeightOneSpectrum (𝓞 D.host.E)) : Fin D.R.r → VA X.B.I :=
  GlobalTheory.SeeConjRead.flagV D.R.rS D.R.k D.R.r X.e0 X.f0 (epsW X w) X.z0

def IsMatIn (X : HidaSetting D) (w : HeightOneSpectrum (𝓞 D.host.E)) {g : ℕ} (u : Fin D.R.r → VA X.B.I) (x : X.B.I.Gf)
    (N : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod g)) : Prop :=
  ∀ i, X.B.I.fmat x *ᵥ u i - ∑ j, (((N j i).val : ℕ) : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) • u j ∈ wLf X w

end GlobalTheory.Mem.SymFrame

end

namespace GlobalTheory.Mem.SymFrame

theorem isMatIn_perm {D : D7} {X : HidaSetting D} {w : HeightOneSpectrum (𝓞 D.host.E)} {g : ℕ}
    (s : Fin D.R.r → VA X.B.I) (x : X.B.I.Gf) (N : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod g)) (π : Equiv.Perm (Fin D.R.r))
    (hN : IsMatIn X w (fun j => s (π.symm j)) x N) : IsMatIn X w s x (N.submatrix π π) := by
  intro i
  have h1 := hN (π i)
  rw [← Equiv.sum_comp π] at h1
  simpa [Matrix.submatrix_apply] using h1

theorem mem_unipSym_bc {κ κ' : Type} [CommRing κ] [CommRing κ'] (f : κ ≃+* κ') {r ρ k : ℕ} (u : GL (Fin r) κ) :
    Formalism.UG.bc (f : κ →+* κ') u ∈ unipSym κ' r ρ k ↔ u ∈ unipSym κ r ρ k := by
  have e : ∀ i j, ((Formalism.UG.bc (f : κ →+* κ') u : GL (Fin r) κ') : Matrix (Fin r) (Fin r) κ') i j =
      f ((u : Matrix (Fin r) (Fin r) κ) i j) := fun _ _ => rfl
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    refine ⟨⟨fun i j hij => ?_, fun i => ?_⟩, fun i j ha hb hc => ?_⟩
    · have := h1 hij; rw [e] at this; exact f.injective (this.trans (map_zero f).symm)
    · have := h2 i; rw [e] at this; exact f.injective (this.trans (map_one f).symm)
    · have := h3 i j ha hb hc; rw [e] at this; exact f.injective (this.trans (map_zero f).symm)
  · rintro ⟨⟨h1, h2⟩, h3⟩
    refine ⟨⟨fun i j hij => ?_, fun i => ?_⟩, fun i j ha hb hc => ?_⟩
    · show ((Formalism.UG.bc (f : κ →+* κ') u : GL (Fin r) κ') : Matrix (Fin r) (Fin r) κ') i j = 0
      rw [e, h1 hij, map_zero]
    · rw [e, h2 i, map_one]
    · rw [e, h3 i j ha hb hc, map_zero]

theorem edgeSum_bc {κ κ' : Type} [CommRing κ] [CommRing κ'] (f : κ ≃+* κ') {r : ℕ} (Ed : Fin r → Fin r → Prop)
    [DecidableRel Ed] (u : GL (Fin r) κ) : edgeSum Ed (Formalism.UG.bc (f : κ →+* κ') u) = f (edgeSum Ed u) := by
  unfold edgeSum
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs
  · rfl
  · rw [map_zero]

end GlobalTheory.Mem.SymFrame
