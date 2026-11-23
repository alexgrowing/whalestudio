import Development.WeilBound.HeckeVectors.HeckeDoubleCosets.DoubleCosetLemmas.LocLaw

noncomputable section

namespace CompanionTheory.D.Upq.DoubleCosetLemmas

open NumberField IsDedekindDomain Matrix Formalism.UG GlobalTheory.LFun GlobalTheory.CompanionTheory.Ipf.Val MeasureTheory
open GlobalTheory.CompanionTheory.QL (bAA bAD bDA bDD chi0 pEl instMeasMat)

variable {K : Type} [Field K] [NumberField K] {v : HeightOneSpectrum (𝓞 K)} {r d c : ℕ}
  {δS δT : (Cv v)ˣ →* ℂˣ}
  {J : Subgroup (GL (Fin (r + c)) (Cv v))} {J' : Subgroup (GL (Fin (r + d)) (Cv v))}

def FT (δS δT : (Cv v)ˣ →* ℂˣ) (h : GL (Fin (r + d)) (Cv v) → ℂ)
    (y : Matrix (Fin (r + d)) (Fin (r + c)) (Cv v)) (z : GL (Fin (r + d)) (Cv v)) : ℂ :=
  h z * linAct v δS δT 1 z (phiB v δT r d c) y

def FS (δS δT : (Cv v)ˣ →* ℂˣ) (h : GL (Fin (r + c)) (Cv v) → ℂ)
    (y : Matrix (Fin (r + d)) (Fin (r + c)) (Cv v)) (z : GL (Fin (r + c)) (Cv v)) : ℂ :=
  h z * linAct v δS δT z 1 (phiB v δT r d c) y

def one0 (v : HeightOneSpectrum (𝓞 K)) (d c : ℕ) : Matrix (Fin d) (Fin c) (Cv v) → ℂ :=
  Set.indicator {x | ∀ i j, Valued.v (x i j) ≤ 1} 1

section Laws

variable (hS : IsTame v δS) (hT : IsTame v δT)
  (he : ∀ x : (Cv v)ˣ, Valued.v (x : Cv v) = 1 → δS x = δT x)
include hS hT he

end Laws

open Classical in

def eps (δ : (Cv v)ˣ →* ℂˣ) (x : Matrix (Fin r) (Fin r) (Cv v)) : ℂ :=
  if UnM x then chi0 δ x.det else 0

end CompanionTheory.D.Upq.DoubleCosetLemmas
