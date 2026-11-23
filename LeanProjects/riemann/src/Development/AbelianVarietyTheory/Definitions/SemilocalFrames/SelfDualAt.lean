import Mathlib
import Formalism.LocalToGlobal.HermitianForms.PsiZeroNontrivialCharacter
import Formalism.SharpRestriction.LevelLetterCocycles.DataN
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.AfsplitB

noncomputable section

open Formalism.BasicNotions Formalism.UG NumberField IsDedekindDomain Matrix
open scoped TensorProduct

namespace GlobalTheory.St.G

abbrev Ad (F : Type) [Field F] [NumberField F] : Type := FiniteAdeleRing (𝓞 F) F

abbrev OAd (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] : Subring (E ⊗[F] Ad F) :=
  tensInt (F := F) (Ad F) (intOE E) (intAd F)

def SplitsIn (E : Type) [Field E] [NumberField E] (p : ℕ) : Prop :=
  (placesOver E p).ncard = Module.finrank ℚ E

section Lat

variable (F : Type) {E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

abbrev hat (L : Submodule (𝓞 E) (Fin n → E)) : Submodule (OAd F E) (Fin n → E ⊗[F] Ad F) :=
  latS (F := F) (Ad F) (OAd F E) L

variable {F}

abbrev loc (v : HeightOneSpectrum (𝓞 F)) (L : Submodule (𝓞 E) (Fin n → E)) :
    Submodule (intV E v) (Fin n → E ⊗[F] v.adicCompletion F) :=
  latS (F := F) (v.adicCompletion F) (intV E v) L

def IsLat (L : Submodule (𝓞 E) (Fin n → E)) : Prop :=
  Module.Finite (𝓞 E) L ∧ Submodule.span E (L : Set (Fin n → E)) = ⊤

def prVec (v : HeightOneSpectrum (𝓞 F)) (x : Fin n → E ⊗[F] Ad F) : Fin n → E ⊗[F] v.adicCompletion F :=
  fun i => prV (E := E) v (x i)

variable (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E)

abbrev dualL (L : Submodule (𝓞 E) (Fin n → E)) : Submodule (𝓞 E) (Fin n → E) :=
  Submodule.span (𝓞 E) (dualSet (σ : E →+* E) J L)

def hR (R : Type) [CommRing R] [Algebra F R] (x y : Fin n → E ⊗[F] R) : E ⊗[F] R :=
  hform (sigR σ R) (J.map (inclE (F := F) R)) x y

def TLat (T f : ℕ) (L : Submodule (𝓞 E) (Fin n → E)) : Prop :=
  IsLat L ∧ (∀ x ∈ L, x ∈ dualSet (σ : E →+* E) J L) ∧ (∀ y ∈ dualSet (σ : E →+* E) J L, (T : E) • y ∈ L) ∧
  L.toAddSubgroup.relIndex (dualL σ J L).toAddSubgroup = T ^ (2 * f) ∧
  ∀ v : HeightOneSpectrum (𝓞 F), (T : 𝓞 F) ∈ v.asIdeal → ∃ x ∈ loc v (dualL σ J L), x ∉ loc v L

def SelfDualAt (v : HeightOneSpectrum (𝓞 F)) (L : Submodule (𝓞 E) (Fin n → E)) : Prop :=
  ∀ y, y ∈ loc v L ↔ ∀ z ∈ loc v L, hR σ J (v.adicCompletion F) z y ∈ intV E v

end Lat

def InModL {A : Type} [CommRing A] {O : Subring A} {n : ℕ} (Λ : Submodule O (Fin n → A)) (m : ℕ)
    (S : Set (Fin n → A)) (x : Fin n → A) : Prop :=
  ∃ s ∈ Submodule.span O S, ∃ z ∈ Λ, x = s + (m : A) • z

def supSum {A : Type} [CommRing A] {n k : ℕ} (h : (Fin n → A) → (Fin n → A) → A) (b bd : Fin k → Fin n → A)
    (y : Matrix (Fin n) (Fin n) A) : A :=
  ∑ i : Fin k, if hi : i.1 + 1 < k then h (bd i) (y *ᵥ b ⟨i.1 + 1, hi⟩) else 0

section Frame

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
  (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E)

structure AdFrame (Λ : Submodule (OAd F E) (Fin n → E ⊗[F] Ad F)) (g k : ℕ) where
  eps : E ⊗[F] Ad F
  eps_idem : eps * eps = eps
  eps_orth : eps * sigR σ (Ad F) eps = 0
  eps_int : eps ∈ OAd F E
  eps_full : ∀ y ∈ Λ, ∃ z ∈ Λ, (1 - eps - sigR σ (Ad F) eps) • y = (g : E ⊗[F] Ad F) • z
  b : Fin k → Fin n → E ⊗[F] Ad F
  bd : Fin k → Fin n → E ⊗[F] Ad F
  b_mem : ∀ i, b i ∈ Λ
  bd_mem : ∀ i, bd i ∈ Λ
  b_eps : ∀ i, b i = eps • b i
  bd_eps : ∀ i, bd i = sigR σ (Ad F) eps • bd i
  dual : ∀ i j, ∃ t ∈ OAd F E, hR σ J (Ad F) (bd i) (b j) - (if i = j then eps else 0) = (g : E ⊗[F] Ad F) * t
  span : ∀ y ∈ Λ, InModL Λ g (Set.range b ∪ Set.range bd) y
  psi : E ⊗[F] Ad F → ℂ
  psi_add : ∀ x y, psi (x + y) = psi x * psi y
  psi_int : ∀ x ∈ OAd F E, psi x = 1
  psi_rat : ∀ x : E, psi (inclE (F := F) (Ad F) x) *
    Complex.exp (2 * Real.pi * Complex.I * ((Algebra.trace ℚ E x : ℚ) : ℂ)) = 1

variable {σ J} {Λ : Submodule (OAd F E) (Fin n → E ⊗[F] Ad F)} {g k : ℕ}

def AdFrame.InK (Fr : AdFrame σ J Λ g k) (y : GL (Fin n) (E ⊗[F] Ad F)) : Prop :=
  y ∈ stabGL Λ ∧
  (∀ x, (∀ z ∈ Λ, hR σ J (Ad F) z x ∈ OAd F E) → (y.1 - 1) *ᵥ x ∈ Λ) ∧
  ∀ i : Fin k, InModL Λ g (Fr.b '' {j | j.1 < i.1}) ((y.1 - 1) *ᵥ Fr.b i)

def AdFrame.chi (Fr : AdFrame σ J Λ g k) (y : GL (Fin n) (E ⊗[F] Ad F)) : ℂ :=
  Fr.psi (algebraMap F (E ⊗[F] Ad F) ((g : F)⁻¹) * supSum (hR σ J (Ad F)) Fr.b Fr.bd y.1)

def AdFrame.LocK (Fr : AdFrame σ J Λ g k) (L : Submodule (𝓞 E) (Fin n → E)) (v : HeightOneSpectrum (𝓞 F))
    (y : GL (Fin n) (E ⊗[F] v.adicCompletion F)) : Prop :=
  ∀ i : Fin k, InModL (loc v L) g ((fun j => prVec v (Fr.b j)) '' {j | j.1 < i.1}) ((y.1 - 1) *ᵥ prVec v (Fr.b i))

def AdFrame.locChi (Fr : AdFrame σ J Λ g k) (v : HeightOneSpectrum (𝓞 F))
    (y : GL (Fin n) (E ⊗[F] v.adicCompletion F)) : ℂ :=
  Fr.psi (Formalism.UG.P.afsplitIE v (algebraMap F (E ⊗[F] v.adicCompletion F) ((g : F)⁻¹) *
    supSum (hR σ J (v.adicCompletion F)) (fun j => prVec v (Fr.b j)) (fun j => prVec v (Fr.bd j)) y.1))

end Frame

end GlobalTheory.St.G

end
