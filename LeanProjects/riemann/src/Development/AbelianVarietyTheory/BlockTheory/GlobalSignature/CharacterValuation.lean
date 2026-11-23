import Mathlib
import Formalism.LocalToGlobal.Columns.ScaledRamifiedLattice
import Formalism.LocalToGlobal.KernelLattices.ThDistC

open NumberField IsDedekindDomain nonZeroDivisors

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.CharacterValuation

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions

def val_vp {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) (p : ℕ) (x : K) : ℚ :=
  (ordE w x : ℚ) / (ordE w (p : K) : ℚ)

def UnitAt {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) (x : K) : Prop := w.valuation K x = 1

section Lat

variable {E : Type} [Field E] [NumberField E] [StarRing E]

def vpIdeal (P : HeightOneSpectrum (𝓞 E)) : Submodule (𝓞 E) E :=
  (((P.asIdeal : FractionalIdeal (𝓞 E)⁰ E) * ((conjPrime₂ P).asIdeal : FractionalIdeal (𝓞 E)⁰ E)⁻¹ : FractionalIdeal (𝓞 E)⁰ E) :
    Submodule (𝓞 E) E)

def vpLat (P : HeightOneSpectrum (𝓞 E)) : Submodule (𝓞 E) (Sp E 1) :=
  (vpIdeal P).comap ((LinearMap.proj (0 : Fin 1) : Sp E 1 →ₗ[E] E).restrictScalars (𝓞 E))

def StdOver {n : ℕ} (p : ℕ) (N : Submodule (𝓞 E) (Sp E n)) : Prop :=
  ∀ P : HeightOneSpectrum (𝓞 E), (p : 𝓞 E) ∈ P.asIdeal → localization₂ P.asIdeal N = stdAt E n P

def IsFrames {n : ℕ} {SB : Finset (HeightOneSpectrum (𝓞 E))} (N : Submodule (𝓞 E) (Sp E n)) (fr : Frs E n SB) : Prop :=
  ∀ (P : SB) (x : Sp E n), fr P x ∈ localization₂ P.1.asIdeal N ↔ x ∈ stdAt E n P.1

end Lat

section Chi

variable {D : D7} {X : Fields} (s : Seam D X) (χ : TaylorLogMetric.IdE D → ℂ)

def idTo (I : Submodule (𝓞 X.E) X.E) : TaylorLogMetric.IdE D :=
  Submodule.span (𝓞 D.host.E) (s.iE '' (I : Set X.E))

def ChiInK : Prop := ∀ 𝔞 : TaylorLogMetric.IdE D, TaylorLogMetric.N1 D 𝔞 → ∃ k : X.K, s.σ₀ k = χ 𝔞

def chiK (𝔞 : TaylorLogMetric.IdE D) : X.K := desc s.σ₀ (χ 𝔞)

def chiVp (P : HeightOneSpectrum (𝓞 X.E)) : X.K := chiK s χ (idTo s (vpIdeal P))

def chiDet {n : ℕ} (N : Submodule (𝓞 X.E) (Sp X.E n)) : X.K :=
  chiK s χ (TaylorLogMetric.detId D (StandardLatticesGL3.stdL D n) (s.lat N))

def chiFK (a b : ℕ) (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) : X.K :=
  desc s.σ₀ (Base.chiFac χ a b (s.lat N) (s.lat N'))

example {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (cD : D.what₂.Tau → ℂ) (a b : ℕ)
    (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) :
    chiFK s χ a b N N' = desc (ambOf s B χ cD).σ₀ ((ambOf s B χ cD).chiF a b N N') := rfl

end Chi

section Rho

variable {D : D7} (Z : Dat) (s : Seam D Z.X) (χ : TaylorLogMetric.IdE D → ℂ)
  (sel : HeightOneSpectrum (𝓞 Z.X.F) → HeightOneSpectrum (𝓞 Z.X.E)) {S : Set ℕ}
  (mu : Tup Z.X.F Z.X.E Z.X.K S) (cst : LocCst Z.X (rowSG Z.Pr sel mu))

def muInv (i : ℕ) {n : ℕ} (N : Submodule (𝓞 Z.X.E) (Sp Z.X.E n)) (fr : Frs Z.X.E n (rowSG Z.Pr sel mu)) : Z.X.K :=
  muInvDet sel (rowSG Z.Pr sel mu) (mUof Z.Ch mu i) (muAtT Z.Ch sel mu cst i) N fr

def scal (i : ℕ) {a b : ℕ} (N : Submodule (𝓞 Z.X.E) (Sp Z.X.E a)) (fr : Frs Z.X.E a (rowSG Z.Pr sel mu))
    (N' : Submodule (𝓞 Z.X.E) (Sp Z.X.E b)) (fr' : Frs Z.X.E b (rowSG Z.Pr sel mu)) : Z.X.K :=
  muInv Z sel mu cst i N fr * (muInv Z sel mu cst i N' fr')⁻¹

def rho (i : ℕ) {n : ℕ} (N : Submodule (𝓞 Z.X.E) (Sp Z.X.E n)) (fr : Frs Z.X.E n (rowSG Z.Pr sel mu)) : Z.X.K :=
  muInv Z sel mu cst i N fr * chiDet s χ N ^ (-((Z.R.N (i + 1) / 2 : ℕ) : ℤ))

def rho' (i : ℕ) {n : ℕ} (N : Submodule (𝓞 Z.X.E) (Sp Z.X.E n)) (fr : Frs Z.X.E n (rowSG Z.Pr sel mu)) : Z.X.K :=
  (muInv Z sel mu cst i N fr)⁻¹ * chiDet s χ N ^ (((Z.R.N i / 2 : ℕ) : ℤ))

def sPrime (i : Fin Z.R.m) (τ : Z.X.Tau) : ℚ := sExp' Z.R ((Z.W.row τ).e i) (i.1 + 1)

def sPlain (i : Fin Z.R.m) (τ : Z.X.Tau) : ℚ := sExp Z.R ((Z.W.row τ).e i) (i.1 + 1)

theorem muAt_eq_muAtT (h : MuqTie Z.Ch sel mu cst) (i : ℕ) (hi : i < Z.R.m) :
    muAt Z.Ch sel mu cst i = muAtT Z.Ch sel mu cst i := by
  funext P
  unfold muAt muAtT
  by_cases hP : P.1 ∈ Z.Pr.vGs
  · simp only [if_pos hP]
  · simp only [if_neg hP, h i hi P hP]

def PartA (u : Z.Pr.Word) : Prop :=
  ∀ P ∈ Z.Pr.vT u,
    (∀ σ : Z.X.K →+* ℂ, ‖σ (chiVp s χ P)‖ = 1) ∧
    (∀ w : HeightOneSpectrum (𝓞 Z.X.K), ((Z.Pr.T u : ℕ) : 𝓞 Z.X.K) ∉ w.asIdeal → UnitAt w (chiVp s χ P)) ∧
    ∀ w : HeightOneSpectrum (𝓞 Z.X.K), ((Z.Pr.T u : ℕ) : 𝓞 Z.X.K) ∈ w.asIdeal → ∀ τ : Z.X.Tau,
      (SeesP w τ P → val_vp w (Z.Pr.T u) (chiVp s χ P) = -1) ∧
      (SeesPbar w τ P → val_vp w (Z.Pr.T u) (chiVp s χ P) = 1)

def PartBChi (u : Z.Pr.Word) (w : HeightOneSpectrum (𝓞 Z.X.K)) : Prop :=
  (∀ 𝔞 : TaylorLogMetric.IdE D, TaylorLogMetric.N1 D 𝔞 →
    (∀ P : HeightOneSpectrum (𝓞 D.host.E), ((Z.Pr.T u : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal →
      localization₂ P.asIdeal 𝔞 = localization₂ P.asIdeal (1 : Submodule (𝓞 D.host.E) D.host.E)) →
    UnitAt w (chiK s χ 𝔞)) ∧
  (∀ (n : ℕ) (N : Submodule (𝓞 Z.X.E) (Sp Z.X.E n)), IsSdLat N → StdOver (Z.Pr.T u) N → UnitAt w (chiDet s χ N)) ∧
  ∀ (a b : ℕ) (N : Submodule (𝓞 Z.X.E) (Sp Z.X.E a)) (N' : Submodule (𝓞 Z.X.E) (Sp Z.X.E b)), Even a → Even b →
    IsSdLat N → IsSdLat N' → StdOver (Z.Pr.T u) N → StdOver (Z.Pr.T u) N' → UnitAt w (chiFK s χ a b N N')

def PartBMu (u : Z.Pr.Word) (w : HeightOneSpectrum (𝓞 Z.X.K)) (i : ℕ) : Prop :=
  (∀ (n : ℕ) (N : Submodule (𝓞 Z.X.E) (Sp Z.X.E n)), IsSdLat N → StdOver (Z.Pr.T u) N →
    UnitAt w (muOff sel (rowSG Z.Pr sel mu) (mUof Z.Ch mu i) N) ∧
    ∀ fr : Frs Z.X.E n (rowSG Z.Pr sel mu), IsFrames N fr →
      UnitAt w (muInv Z sel mu cst i N fr) ∧ UnitAt w (rho Z s χ sel mu cst i N fr) ∧ UnitAt w (rho' Z s χ sel mu cst i N fr)) ∧
  ∀ (a b : ℕ) (N : Submodule (𝓞 Z.X.E) (Sp Z.X.E a)) (fr : Frs Z.X.E a (rowSG Z.Pr sel mu))
    (N' : Submodule (𝓞 Z.X.E) (Sp Z.X.E b)) (fr' : Frs Z.X.E b (rowSG Z.Pr sel mu)),
    IsSdLat N → IsSdLat N' → StdOver (Z.Pr.T u) N → StdOver (Z.Pr.T u) N' → IsFrames N fr → IsFrames N' fr' →
    UnitAt w (scal Z sel mu cst i N fr N' fr')

def PartC (u : Z.Pr.Word) (w : HeightOneSpectrum (𝓞 Z.X.K)) (i : Fin Z.R.m) : Prop :=
  ∀ P ∈ Z.Pr.vT u, ∀ τ : Z.X.Tau, SeesP w τ P ∨ SeesPbar w τ P →
    rho Z s χ sel mu cst i.1 (vpLat P) (fun _ => 1) ≠ 0 ∧ rho' Z s χ sel mu cst i.1 (vpLat P) (fun _ => 1) ≠ 0 ∧
    val_vp w (Z.Pr.T u) (rho Z s χ sel mu cst i.1 (vpLat P) (fun _ => 1)) =
      sPrime Z i τ * val_vp w (Z.Pr.T u) (chiVp s χ P) ∧
    val_vp w (Z.Pr.T u) (rho' Z s χ sel mu cst i.1 (vpLat P) (fun _ => 1)) =
      -sPlain Z i τ * val_vp w (Z.Pr.T u) (chiVp s χ P)

def PartD (i : ℕ) : Prop :=
  ∀ (n : ℕ) (N : Submodule (𝓞 Z.X.E) (Sp Z.X.E n)) (fr : Frs Z.X.E n (rowSG Z.Pr sel mu)), IsSdLat N → IsFrames N fr →
    chiDet s χ N ≠ 0 ∧
    rho Z s χ sel mu cst i N fr * rho' Z s χ sel mu cst i N fr = chiDet s χ N ^ (-(((Z.R.t + 1) / 2 : ℕ) : ℤ))

def UnramOver {X : Fields} (ξ : Chr X.F X.E X.K) (p : ℕ) : Prop :=
  ∀ v : HeightOneSpectrum (𝓞 X.F), (p : 𝓞 X.F) ∈ v.asIdeal → v ∉ Qprime ξ

end Rho

def CharValAtT : Prop :=
  ∀ (Z : Dat) (D : D7) (s : Seam D Z.X) (χ : TaylorLogMetric.IdE D → ℂ) (u : Z.Pr.Word),
    Z.Ok → s.Ok → s.σ₀ = Z.sig0 → TaylorLogMetric.IsChi D χ → ChiInK s χ →
    PartA Z s χ u ∧
    (∀ w : HeightOneSpectrum (𝓞 Z.X.K), ((Z.Pr.T u : ℕ) : 𝓞 Z.X.K) ∈ w.asIdeal → PartBChi Z s χ u w) ∧
    ∀ (m0 : Fin Z.R.m → Formalism.L2.Host.HChar Z.X.E) (eta : Formalism.L2.Host.HChar Z.X.E),
      Z.Ch.Tied Z.sig0 (fun j τ => (Z.W.row τ).e j) m0 eta →
      ∀ (sel : HeightOneSpectrum (𝓞 Z.X.F) → HeightOneSpectrum (𝓞 Z.X.E)), IsSel Z.X sel →
      ∀ (S : Set ℕ) (mu : Tup Z.X.F Z.X.E Z.X.K S),
        UnramOver (mu : Chr Z.X.F Z.X.E Z.X.K) (Z.Pr.T u) → (∀ k, UnramOver (mu : Chr Z.X.F Z.X.E Z.X.K) (Z.Pr.g k)) →
      ∀ cst : LocCst Z.X (rowSG Z.Pr sel mu), MuqTieG (Pr := Z.Pr) (R := Z.R) sel mu cst Z.sig0 m0 →
      ∀ i : Fin Z.R.m,
        (∀ w : HeightOneSpectrum (𝓞 Z.X.K), ((Z.Pr.T u : ℕ) : 𝓞 Z.X.K) ∈ w.asIdeal →
          PartBMu Z s χ sel mu cst u w i.1 ∧ PartC Z s χ sel mu cst u w i) ∧
        PartD Z s χ sel mu cst i.1

example {E : Type} [Field E] [NumberField E] [StarRing E] (n p : ℕ) (SB : Finset (HeightOneSpectrum (𝓞 E))) :
    StdOver p (stdLat E n) ∧ IsFrames (SB := SB) (stdLat E n) (fun _ => 1) :=
  ⟨fun _ _ => rfl, fun _ _ => Iff.rfl⟩

theorem UnitAt.ne_zero {K : Type} [Field K] [NumberField K] {w : HeightOneSpectrum (𝓞 K)} {x : K} (h : UnitAt w x) : x ≠ 0 := by
  rintro rfl
  simp [UnitAt] at h

end GlobalTheory.IndefiniteRowSideFullHecke.CharacterValuation
