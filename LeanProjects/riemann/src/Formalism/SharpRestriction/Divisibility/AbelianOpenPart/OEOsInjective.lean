import Mathlib
import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.KaSmallNonpos

noncomputable section

namespace Formalism.MainNotions.DIV.Cons

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions

section OE

variable (D : D7) (hinj : Function.Injective D.what₂.OtoLL)

def oEOsFun (x : 𝓞 D.host.E) : D.what₂.O := Classical.choose (D.O_contains x)

theorem oEOsFun_spec (x : 𝓞 D.host.E) :
    D.what₂.OtoLL (oEOsFun D x) = (D.embE.comp (algebraMap (𝓞 D.host.E) D.host.E)) x :=
  Classical.choose_spec (D.O_contains x)

def oEOs : 𝓞 D.host.E →+* D.what₂.O where
  toFun := oEOsFun D
  map_one' := hinj (by rw [oEOsFun_spec, map_one, map_one])
  map_mul' x y := hinj (by rw [map_mul, oEOsFun_spec, oEOsFun_spec, oEOsFun_spec, map_mul])
  map_zero' := hinj (by rw [oEOsFun_spec, map_zero, map_zero])
  map_add' x y := hinj (by rw [map_add, oEOsFun_spec, oEOsFun_spec, oEOsFun_spec, map_add])

theorem oEOs_injective : Function.Injective (oEOs D hinj) := by
  intro x y hxy
  have h : D.what₂.OtoLL (oEOsFun D x) = D.what₂.OtoLL (oEOsFun D y) := by
    change D.what₂.OtoLL (oEOs D hinj x) = D.what₂.OtoLL (oEOs D hinj y)
    rw [hxy]
  rw [oEOsFun_spec, oEOsFun_spec, RingHom.comp_apply, RingHom.comp_apply] at h
  exact FaithfulSMul.algebraMap_injective (𝓞 D.host.E) D.host.E (D.embE.injective h)

def iE (B : WeightFamilies.Prov D) : 𝓞 D.host.E →+* 𝓞 B.KO := B.eO.symm.toRingHom.comp (oEOs D hinj)

theorem iE_injective (B : WeightFamilies.Prov D) : Function.Injective (iE D hinj B) :=
  B.eO.symm.injective.comp (oEOs_injective D hinj)

end OE

section Scal

variable {D : D7} {j : ℕ}

def Dplus (w : WeightFamilies.Wt D j) : ℕ := ∑ τ, ∑ i, w.aP τ i

def Dminus (w : WeightFamilies.Wt D j) : ℕ := ∑ τ, ∑ i, w.aM τ i

def piBarO (EX : ErrX D) (i : Fin 2) : 𝓞 D.host.E :=
  NumberField.RingOfIntegers.mapRingHom D.host.conj.toAlgHom.toRingHom (EX.piG i)

def nnW (B : WeightFamilies.Prov D) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (w : WeightFamilies.Wt D j) : 𝓞 B.KO :=
  ∏ i : Fin 2, iE D hinj B (EX.piG i) ^ Dplus w * iE D hinj B (piBarO EX i) ^ Dminus w

def vd2 (D : D7) : ℝ := Real.logb 2 D.host.QS

def c2 (D : D7) (w : WeightFamilies.Wt D j) : ℕ := WeightAlgebra.DF w

def cHalf (w : WeightFamilies.Wt D j) : ℕ := ⌈(WeightAlgebra.DF w : ℝ) / 2⌉₊

def pPow (D : D7) (a b b' : ℕ) : ℕ := D.host.QS ^ a * D.host.q ^ b * D.host.d ^ b'

def po (D : D7) : ℕ := D.host.pde

def po2 (D : D7) : ℕ := D.host.pde'

def zOwnP (D : D7) (p : ℕ) (w : WeightFamilies.Wt D j) : ℕ := p ^ (WeightAlgebra.DF w + 2 * D.R.f * D.R.r * w.n)

def zOwn (D : D7) (w : WeightFamilies.Wt D j) : ℕ := zOwnP D (po D) w

def scalOfP (B : WeightFamilies.Prov D) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (p : ℕ)
    (ka wL wF : WeightFamilies.Wt D j) (T : ℕ) : WeightAlgebra.Scal B where
  sW := nnW B hinj EX wL * (pPow D (c2 D wL) (cHalf wL) (cHalf wL) : 𝓞 B.KO)
  sF := (zOwnP D p wF : 𝓞 B.KO) * nnW B hinj EX wF * (pPow D (c2 D wF) (cHalf wF) (cHalf wF) : 𝓞 B.KO)
  s0 := (zOwnP D p (WeightAlgebra.wadd wF (WeightAlgebra.wsmul (WeightFamilies.dimY D j) wL)) : 𝓞 B.KO) * nnW B hinj EX wL ^ WeightFamilies.dimY D j *
    nnW B hinj EX wF * (pPow D (WeightFamilies.dimY D j * c2 D wL + c2 D wF) (WeightFamilies.dimY D j * cHalf wL + cHalf wF)
      (WeightFamilies.dimY D j * cHalf wL + cHalf wF) : 𝓞 B.KO)
  sK := (zOwnP D p ka : 𝓞 B.KO) * nnW B hinj EX wL ^ T * nnW B hinj EX wF *
    (pPow D (T * c2 D wL + c2 D wF) (T * cHalf wL + cHalf wF) (T * cHalf wL + cHalf wF) : 𝓞 B.KO)

def scalOf (B : WeightFamilies.Prov D) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D)
    (ka wL wF : WeightFamilies.Wt D j) (T : ℕ) : WeightAlgebra.Scal B :=
  scalOfP B hinj EX (po D) ka wL wF T

end Scal

section Run

variable {D : D7} {L : SizeData₂ D} {P : ParameterChoice' D L}

def kaR (T : ParamsT D L P) (hK : DV.KapDef D) (j : ℕ) : WeightFamilies.Wt D j := kaWt D hK (even_nV T) j

def lR (T : ParamsT D L P) (hK : DV.KapDef D) (j : ℕ) : WeightFamilies.Wt D j :=
  lWt D (kaR T hK j) T.TO T.nWn (even_nW T)

def fR (T : ParamsT D L P) (hK : DV.KapDef D) (j : ℕ) : WeightFamilies.Wt D j :=
  fWt D (kaR T hK j) (lR T hK j) T.TO T.nP (even_nP T)

open Classical in

def nusOf (B : WeightFamilies.Prov D) {j : ℕ} (wL : WeightFamilies.Wt D j) (nuWW : HeightOneSpectrum (𝓞 B.KO) → ℝ)
    (la : HeightOneSpectrum (𝓞 B.KO)) : ℝ :=
  if h : ∃ i : Fin 2, ((D.host.g i : ℕ) : 𝓞 B.KO) ∈ la.asIdeal then
    (eWL B.KO la : ℝ) * (WeightAlgebra.DF wL : ℝ) / ((D.host.g (Classical.choose h) : ℝ) - 1)
  else (eWL B.KO la : ℝ) * (nuWW la +
    (if ((D.host.QS : ℕ) : 𝓞 B.KO) ∈ la.asIdeal then
        (padicValNat (ringChar (𝓞 B.KO ⧸ la.asIdeal)) D.host.QS : ℝ) * (c2 D wL : ℝ)
     else if ((D.host.q : ℕ) : 𝓞 B.KO) ∈ la.asIdeal ∨ ((D.host.d : ℕ) : 𝓞 B.KO) ∈ la.asIdeal then (cHalf wL : ℝ)
     else 0))

def runOfP (T : ParamsT D L P) (hK : DV.KapDef D) (B : WeightFamilies.Prov D) (hinj : Function.Injective D.what₂.OtoLL)
    (EX : ErrX D) (p : ℕ) (nuWW : ℕ → HeightOneSpectrum (𝓞 B.KO) → ℝ) (j : ℕ) : LiftErrorLocal.Run D B j where
  S := scalOfP B hinj EX p (kaR T hK j) (lR T hK j) (fR T hK j) T.TO
  ka := kaR T hK j
  wL := lR T hK j
  wF := fR T hK j
  nP := T.nP
  nW := T.nWn
  h0 := LevelStarExponents.h0 L - 4
  n1 := D.R.r
  n2 := T.nWn - D.R.r
  nus := nusOf B (lR T hK j) (nuWW j)

def runOf (T : ParamsT D L P) (hK : DV.KapDef D) (B : WeightFamilies.Prov D) (hinj : Function.Injective D.what₂.OtoLL)
    (EX : ErrX D) (nuWW : ℕ → HeightOneSpectrum (𝓞 B.KO) → ℝ) (j : ℕ) : LiftErrorLocal.Run D B j :=
  runOfP T hK B hinj EX (po D) nuWW j

def runOf2 (T : ParamsT D L P) (hK : DV.KapDef D) (B : WeightFamilies.Prov D) (hinj : Function.Injective D.what₂.OtoLL)
    (EX : ErrX D) (nuWW : ℕ → HeightOneSpectrum (𝓞 B.KO) → ℝ) (j : ℕ) : LiftErrorLocal.Run D B j :=
  runOfP T hK B hinj EX (po2 D) nuWW j

end Run

end Formalism.MainNotions.DIV.Cons
