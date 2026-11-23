import Mathlib
import Formalism.LocalToGlobal.Divisibility.Tuples

noncomputable section

open NumberField IsDedekindDomain TensorProduct Formalism.UG Formalism.DivisionValues Formalism.EigenvalueLevelCeiling

namespace Formalism.L2.DIV

section Proved

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {L : Type} [Field L]

theorem mem_tupGrp {S : Set ℕ} (ξ : Chr F E L) : ξ ∈ tupGrp F E L S ↔
    ((ratId F E).range ≤ ξ.ker ∧ (∃ N : ℕ, 0 < N ∧ congN F E N ≤ ξ.ker) ∧ IsOfFinOrder ξ) ∧
      (idF F E).range ≤ ξ.ker ∧ (∀ v : HeightOneSpectrum (𝓞 F), wildAt E v ≤ ξ.ker) ∧
      ∀ v : HeightOneSpectrum (𝓞 F), ¬ GoodPl E S v → inertAt E v ≤ ξ.ker := by
  simp only [tupGrp, finChar, Subgroup.mem_inf, Subgroup.mem_iInf, mem_kills, CommGroup.mem_torsion]
  constructor
  · rintro ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩
    exact ⟨⟨h1, h2, h3⟩, h4, h5, h6⟩
  · rintro ⟨⟨h1, h2, h3⟩, h4, h5, h6⟩
    exact ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩

theorem tilde_norm_quotient (σ : E →ₐ[F] E) (ξ : Chr F E L) (h : (h90 σ).ker ≤ ξ.ker) (x : (AfE F E)ˣ) :
    tilde σ ξ ⟨h90 σ x, x, rfl⟩ = ξ x := by
  rw [tilde, dif_pos h]
  exact MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ x

theorem detTw_of_det (σ : E →ₐ[F] E) (ξ : Chr F E L) (h : (h90 σ).ker ≤ ξ.ker) {n : ℕ}
    (g : GL (Fin n) (AfE F E)) (x : (AfE F E)ˣ) (hx : h90 σ x = Matrix.GeneralLinearGroup.det g) :
    detTw σ ξ g = ξ x := by
  have hm : Matrix.GeneralLinearGroup.det g ∈ (h90 σ).range := ⟨x, hx⟩
  rw [detTw, dif_pos hm, ← tilde_norm_quotient σ ξ h x]
  congr 1
  exact Subtype.ext hx.symm

end Proved

section ProvedK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {K : Type} [Field K] [NumberField K] [StarRing K] {S : Set ℕ}

theorem tup_finOrder (ξ : Tup F E K S) : IsOfFinOrder (ξ : Chr F E K) := ((mem_tupGrp (ξ : Chr F E K)).mp ξ.2).1.2.2

end ProvedK

theorem IsBaseChar.good {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {L : Type}
    [Field L] {S : Set ℕ} {p : ℕ} (δ : Tup F E L S) (h : IsBaseChar p (δ : Chr F E L))
    (v : HeightOneSpectrum (𝓞 F)) (hv : plc v = p) : GoodPl E S v := by
  by_contra hg
  have h1 : (δ : Chr F E L) ∈ kills Lˣ (inertAt E v) := by
    exact ((mem_tupGrp (δ : Chr F E L)).mp δ.2).2.2.2 v hg
  have h2 : (15 : ℕ) ∣ 1 := ((h.2 v).1 hv 1).mp fun x hx => by
    have := h1 hx
    rw [MonoidHom.mem_ker] at this
    rw [this, one_pow]
  omega

theorem Tup.good {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {L : Type} [Field L]
    {S : Set ℕ} (ξ : Tup F E L S) {v : HeightOneSpectrum (𝓞 F)} (hv : v ∈ Qprime (ξ : Chr F E L)) : GoodPl E S v := by
  by_contra hg
  exact hv (((mem_tupGrp (ξ : Chr F E L)).mp ξ.2).2.2.2 v hg)

def IsConjOf {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) : Prop :=
  σ ≠ AlgHom.id F E ∧ (∀ e, σ (σ e) = e) ∧ ∀ e, σ e = e → ∃ a : F, algebraMap F E a = e

def FixedIsIdF : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsConjOf σ → (h90 σ).ker = (idF F E).range

def Hilbert90FiniteIdeles : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsConjOf σ → U1 σ = (h90 σ).range

def DetInUnitaryOne : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ)
    (J : Matrix (Fin n) (Fin n) E), IsUnit J.det →
    ∀ g ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F), Matrix.GeneralLinearGroup.det g ∈ U1 σ

def DetTwMul : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (L : Type) [Field L]
    (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (ξ : Chr F E L),
    IsConjOf σ → IsUnit J.det → (idF F E).range ≤ ξ.ker →
    ∀ g ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F), ∀ g' ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F),
      detTw σ ξ (g * g') = detTw σ ξ g * detTw σ ξ g'

def DetTwRat : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (L : Type) [Field L]
    (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (ξ : Chr F E L),
    IsConjOf σ → IsUnit J.det → (idF F E).range ≤ ξ.ker → (ratId F E).range ≤ ξ.ker →
    ∀ g ∈ ratPts σ J (FiniteAdeleRing (𝓞 F) F), detTw σ ξ g = 1

def DetTwSq : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (L : Type) [Field L]
    (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (ξ : Chr F E L),
    IsConjOf σ → IsUnit J.det → (idF F E).range ≤ ξ.ker →
    ∀ g ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F), ξ (Matrix.GeneralLinearGroup.det g) = detTw σ ξ g ^ 2

def ConjInv : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (L : Type) [Field L]
    (σ : E →ₐ[F] E) (ξ : Chr F E L), IsConjOf σ → (idF F E).range ≤ ξ.ker → ξ.comp (conjId σ) = ξ⁻¹

def FinOrdAuto : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (L : Type) [Field L],
    kills Lˣ (ratId F E).range ⊓ openChr F E L ≤ CommGroup.torsion (Chr F E L)

def QprimeFinite : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (L : Type) [Field L]
    (ξ : Chr F E L), ξ ∈ openChr F E L → (Qprime ξ).Finite

def ResCharEx : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (L : Type) [Field L]
    (ξ : Chr F E L), (∀ v : HeightOneSpectrum (𝓞 F), wildAt E v ≤ ξ.ker) →
    ∀ P : HeightOneSpectrum (𝓞 E), ∃! χ, IsResChar ξ P χ

def ResCharMul : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (L : Type) [Field L]
    (ξ η : Chr F E L), (∀ v : HeightOneSpectrum (𝓞 F), wildAt E v ≤ ξ.ker) →
    (∀ v : HeightOneSpectrum (𝓞 F), wildAt E v ≤ η.ker) →
    ∀ P : HeightOneSpectrum (𝓞 E), resChar (ξ * η) P = resChar ξ P * resChar η P

def ResCharRam : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (L : Type) [Field L],
    Module.finrank F E = 2 →
    ∀ (ξ : Chr F E L), (∀ v : HeightOneSpectrum (𝓞 F), wildAt E v ≤ ξ.ker) → (idF F E).range ≤ ξ.ker →
    ∀ (v : HeightOneSpectrum (𝓞 F)) (P P' : HeightOneSpectrum (𝓞 E)), P ≠ P' →
      Ideal.map (algebraMap (𝓞 F) (𝓞 E)) v.asIdeal = P.asIdeal * P'.asIdeal →
      (v ∈ Qprime ξ ↔ resChar ξ P ≠ 1)

def ResCharConj : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (L : Type) [Field L]
    (ξ : Chr F E L), (∀ v : HeightOneSpectrum (𝓞 F), wildAt E v ≤ ξ.ker) → (idF F E).range ≤ ξ.ker →
    ∀ (v : HeightOneSpectrum (𝓞 F)) (P P' : HeightOneSpectrum (𝓞 E)), P ≠ P' →
      Ideal.map (algebraMap (𝓞 F) (𝓞 E)) v.asIdeal = P.asIdeal * P'.asIdeal →
      ∀ (n : 𝓞 F) (a : (𝓞 E ⧸ P.asIdeal)ˣ) (a' : (𝓞 E ⧸ P'.asIdeal)ˣ),
        (a : 𝓞 E ⧸ P.asIdeal) = Ideal.Quotient.mk P.asIdeal (algebraMap (𝓞 F) (𝓞 E) n) →
        (a' : 𝓞 E ⧸ P'.asIdeal) = Ideal.Quotient.mk P'.asIdeal (algebraMap (𝓞 F) (𝓞 E) n) →
        resChar ξ P a * resChar ξ P' a' = 1

def InertOrdRes : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (L : Type) [Field L],
    Module.finrank F E = 2 →
    ∀ (ξ : Chr F E L), (∀ v : HeightOneSpectrum (𝓞 F), wildAt E v ≤ ξ.ker) → (idF F E).range ≤ ξ.ker →
    ∀ (v : HeightOneSpectrum (𝓞 F)) (P P' : HeightOneSpectrum (𝓞 E)), P ≠ P' →
      Ideal.map (algebraMap (𝓞 F) (𝓞 E)) v.asIdeal = P.asIdeal * P'.asIdeal →
      ∀ n : ℕ, InertOrd ξ v n ↔ orderOf (resChar ξ P) = n

def DegOnePlc : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)), DegOne v → Ideal.absNorm v.asIdeal = plc v

def BasePrime : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (L : Type) [Field L],
    Module.finrank F E = 2 →
    ∀ (S : Set ℕ) (p : ℕ) (δ : Tup F E L S), IsBaseChar p (δ : Chr F E L) → p % 15 = 1

def TildeLocal : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (L : Type) [Field L]
    (σ : E →ₐ[F] E) (ξ : Chr F E L), IsConjOf σ →
    (∀ v : HeightOneSpectrum (𝓞 F), wildAt E v ≤ ξ.ker) → (idF F E).range ≤ ξ.ker →
    ∀ (P : HeightOneSpectrum (𝓞 E)) (v : HeightOneSpectrum (𝓞 F)), P.asIdeal.under (𝓞 F) = v.asIdeal →
    ∀ (u : (RInt F E)ˣ) (a : (𝓞 E ⧸ P.asIdeal)ˣ) (b : 𝓞 E), Ideal.Quotient.mk P.asIdeal b = a →
      Units.map (RInt F E).subtype.toMonoidHom u ∈ suppAt E v →
      (u : RInt F E) - toRInt F E b ∈ P.asIdeal.map (toRInt F E) →
      (∀ P' : HeightOneSpectrum (𝓞 E), P' ≠ P → (u : RInt F E) - 1 ∈ P'.asIdeal.map (toRInt F E)) →
      tilde σ ξ ⟨h90 σ (Units.map (RInt F E).subtype.toMonoidHom u), _, rfl⟩ = resChar ξ P a

def Mu0Quot : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (L : Type) [Field L]
    (σ : E →ₐ[F] E) (Ψ : Finset (E →+* L)) (e : (E →+* L) → ℤ) (G : Set ℕ) (μ μ' : Chr F E L),
    IsMu0 σ Ψ e G μ → IsMu0 σ Ψ e G μ' → μ * μ'⁻¹ ∈ finChar F E L

end Formalism.L2.DIV

end
