import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.PropagationTheoremGL2

set_option linter.overlappingInstances false

noncomputable section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

namespace UpperTheory.V.Pr

structure Setup {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O]
    [Algebra ℤ_[l] O] (F : Frame l (ResidueField O)) (n : ℕ) : Type 1 where
  n23 : n = 2 ∨ n = 3
  C₀ : ℕ
  ok : F.Ok C₀
  big : F.Big C₀
  lne : (l : O) ≠ 0
  G : W.GFrame l
  r : W.Resid G O n
  K : TwLink F r
  B : W.UniversalOrdinaryDeterminantRing r
  S : Space O F n

namespace Setup

variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O]
  [Algebra ℤ_[l] O] {F : Frame l (ResidueField O)} {n : ℕ} (T : Setup F n)

abbrev IsPhi (Φ : T.B.B →ₐ[O] T.S.B) : Prop := T.K.IsPhi T.B T.S Φ

def phi (Φ : T.B.B →ₐ[O] T.S.B) {x : Ideal T.S.A} (L : T.S.Loc x) : T.B.B →ₐ[O] L.R := L.ι.comp (T.S.inc.comp Φ)

def back (Φ : T.B.B →ₐ[O] T.S.B) {x : Ideal T.S.A} (L : T.S.Loc x) (P : Ideal L.R) [P.IsPrime] : PrimeSpectrum T.B.B :=
  ⟨P.comap (T.phi Φ L : T.B.B →+* L.R), inferInstance⟩

def PhiEx : Prop := ∃ Φ, T.IsPhi Φ ∧ Function.Surjective Φ

def FinLamOf : Prop :=
  ∀ Φ, T.IsPhi Φ → Function.Surjective Φ → ∀ (Λ : W.LamObj T.r) (J : Ideal T.B.B),
    ((Ideal.Quotient.mk J).comp (Λ.toPair T.B.u : Λ.Λ →+* T.B.B)).Finite → T.S.FinLam (J.map Φ)

def PointEx : Prop :=
  ∀ Φ, T.IsPhi Φ → ∀ (x : Ideal T.S.A) (L : T.S.Loc x) (p : Ideal L.R), p.IsPrime → qdim p = 1 → (l : L.R) ∈ p →
    ∃ (y : W.Point T.r) (j : L.R →ₐ[O] y.A), RingHom.ker j = p ∧ IsLocalHom j ∧
      W.mat y.ρ = T.K.tw (L.ρ.map (j : L.R →+* y.A)) ∧ y.ψ = T.K.twψ (L.ρ.map (j : L.R →+* y.A)) ∧
      T.B.IsPt y (j.comp (T.phi Φ L))

def NiceOf : Prop :=
  ∀ (x : Ideal T.S.A) (L : T.S.Loc x) (y : W.Point T.r) (j : L.R →ₐ[O] y.A), IsLocalHom j → Nice L.ρ (RingHom.ker j) →
    W.mat y.ρ = T.K.tw (L.ρ.map (j : L.R →+* y.A)) → y.ψ = T.K.twψ (L.ρ.map (j : L.R →+* y.A)) →
    y.N1 ∧ y.N3 ∧ (L.ρ.TI (RingHom.ker j) → y.TypeI) ∧ (L.ρ.TE (RingHom.ker j) → y.TypeE)

def StableOf : Prop :=
  ∀ Φ, T.IsPhi Φ → ∀ (x : Ideal T.S.A) (L : T.S.Loc x) (P : Ideal L.R) [P.IsPrime], L.ρ.TI P → T.B.IsStable (T.back Φ L P)

def FirstPrimeConditionTransfer : Prop :=
  ∀ Φ, T.IsPhi Φ → (∀ y : W.Point T.r, y.N4) → ∀ J, T.B.P1core J → P1' T.S (J.map Φ)

def IdealSpecializationPoint (J : Ideal T.B.B) : Prop :=
  ∃ (K' : Type) (_ : Field K') (_ : IsAlgClosed K') (_ : Algebra O K') (φ : T.B.B →ₐ[O] K') (ρ : NRep F n K'),
    MatIrr ⊤ ρ.r ∧ J ≤ RingHom.ker φ ∧ T.B.u.D.map (φ : T.B.B →+* K') = W.GDet.ofRep (T.K.tw ρ)

def Unr0 (J : Ideal T.B.B) : Prop :=
  ∀ g ∈ T.G.I0, (T.B.u.D.map (Ideal.Quotient.mk J)).Kills (MonoidAlgebra.single (g : T.G.G₀) (1 : T.B.B ⧸ J) - 1)

def DimT (J : Ideal T.B.B) : Prop := ∀ Z ∈ J.minimalPrimes, qdim Z = ((1 + n * F.d : ℕ) : WithBot ℕ∞)

def CurveSpecializationHypothesis : Prop :=
  ∀ Φ, T.IsPhi Φ → ∀ J, T.Unr0 J → T.DimT J → T.IdealSpecializationPoint J → SeedIn T.S (J.map Φ)

def GoodPt (J : Ideal T.B.B) : Prop :=
  ∀ (A : Type) [CommRing A] [Algebra O A] [IsCD O A] (ρ : NRep F n A), IsLiftA O ρ →
    ∀ (K' : Type) [Field K'] (j : A →+* K'), Function.Injective j → MatIrr ⊤ (ρ.map j).r →
    ∃ f : T.B.B →ₐ[O] A, J ≤ RingHom.ker f ∧ T.B.u.Maps (f : T.B.B →+* A) (W.GDet.ofRep (T.K.tw ρ)) (T.K.twψ ρ)

def GoodPtOf : Prop := ∀ Φ, T.IsPhi Φ → ∀ J, AllGood T.S (J.map Φ) → T.GoodPt J

structure ModIn (J : Ideal T.B.B) : Prop where
  fin : ∃ Λ : W.LamObj T.r, ((Ideal.Quotient.mk J).comp (Λ.toPair T.B.u : Λ.Λ →+* T.B.B)).Finite
  dim : T.DimT J
  unr : T.Unr0 J
  n4 : ∀ y : W.Point T.r, y.N4
  p1 : T.B.P1core J
  p3 : T.B.P3core J
  seed : T.IdealSpecializationPoint J

end Setup

section Three

variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O]
  [Algebra ℤ_[l] O] {F : Frame l (ResidueField O)} (T : Setup F 3)

def Setup.ThickOf : Prop :=
  ∀ Φ, T.IsPhi Φ → ∀ (x : Ideal T.S.A) (L : T.S.Loc x) (P : Ideal L.R) [P.IsPrime], Thick L.ρ P →
    T.B.IsThick (T.back Φ L P)

def Setup.SecondThirdPrimeConditionTransfer : Prop :=
  ∀ Φ, T.IsPhi Φ → (∀ y : W.Point T.r, y.N4) → ∀ J, T.B.P3core J → P23' T.S (J.map Φ)

end Three

def AbsMain : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O]
    [Algebra ℤ_[l] O] (F : Frame l (ResidueField O)) (T₂ : Setup F 2) (T₃ : Setup F 3) (J₂ : Ideal T₂.B.B)
    (J₃ : Ideal T₃.B.B), T₂.ModIn J₂ → T₃.ModIn J₃ →
    T₂.GoodPt J₂ ∧ T₃.GoodPt J₃ ∧ FinPt O F 3

end UpperTheory.V.Pr

end
