import Mathlib
import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
import Formalism.LocalToGlobal.KernelLattices.ThDistC

open NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.StandardKernelAtTorus

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions

section Adjoint

variable {E : Type} [Field E] [StarRing E] {a b : ℕ}

def adj (x : HomE E a b) : HomE E b a where
  toFun w := fun α => ∑ β : Fin b, star (x (Pi.single α 1) β) * w β
  map_add' w w' := by funext α; simp [mul_add, Finset.sum_add_distrib]
  map_smul' c w := by funext α; simp [Finset.mul_sum, mul_left_comm]

theorem adj_single (x : HomE E a b) (β : Fin b) (α : Fin a) :
    adj x (Pi.single β 1) α = star (x (Pi.single α 1) β) := by
  simp [adj, Pi.single_apply]

end Adjoint

section Sets

variable {E : Type} [Field E] [NumberField E] [StarRing E] {a b : ℕ} {ST SG SG' : Finset (HeightOneSpectrum (𝓞 E))}

def StdAtT {n : ℕ} (d : Deco E n ST SG) : Prop := ∀ P : ST, d.at P.1 = stdAt E n P.1

def suppPts (d : Deco E a ST SG) (d' : Deco E b ST SG') : Set (HomE E a b) :=
  {x | ∀ P : ST, ∀ y ∈ d.at P.1, x y ∈ d'.at P.1 ∧ d'.f P (x y) = d.f P y}

def dualPts (d : Deco E a ST SG) (d' : Deco E b ST SG') : Set (HomE E a b) :=
  {x | ∀ P : ST, ∀ y ∈ d'.at P.1, d'.f P y = 0 → adj x y ∈ d.at P.1}

end Sets

section Table

variable {X : Fields} {a b : ℕ}

def diracMom {p : ℕ} [Fact p.Prime] (ι : X.K →+* ℂ_[p]) (uu : X.Tau → ℂ_[p]) (x : HomE X.E a b)
    (m : DVar X.Tau a b →₀ ℕ) : ℂ_[p] :=
  m.prod fun k n => (uu k.1 * ι (X.emb k.1 (adj x (Pi.single k.2.1 1) k.2.2))) ^ n

def kerTable (A : Amb X) (Sall : Finset (HeightOneSpectrum (𝓞 X.E))) (cA cB : ℕ)
    (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) (Ξ : HomE X.E a b → X.K)
    (m : DVar X.Tau a b →₀ ℕ) : X.K :=
  latSum (divLat cA (homAt Sall N N')) (mulLat cB (homAt Sall N N')) fun x => Ξ x * A.jetK Sall N N' cB x m

def RatAt (A : Amb X) (Sall : Finset (HeightOneSpectrum (𝓞 X.E))) (cA cB : ℕ)
    (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) (Ξ : HomE X.E a b → X.K)
    (m : DVar X.Tau a b →₀ ℕ) : Prop :=
  ∀ x ∈ divLat cA (homAt Sall N N'), Ξ x ≠ 0 →
    ∃ k : X.K, A.σ₀ k = (A.chiF a b N N')⁻¹ * jetC A.cD (A.thInd Sall N N' cB x) m

def InMomClosure {p : ℕ} [Fact p.Prime] {I H : Type} (G : Set I) (t : I → ℂ_[p]) (κ : ℂ_[p]) (Z : Set H) (mom : H → I → ℂ_[p]) : Prop :=
  ∀ M : Finset I, (∀ m ∈ M, m ∈ G) → ∀ ε : ℝ, 0 < ε →
    ∃ (n : ℕ) (r : Fin n → ℂ_[p]) (z : Fin n → H), (∀ i, ‖r i‖ ≤ 1) ∧ (∀ i, z i ∈ Z) ∧
      ∀ m ∈ M, ‖t m - κ * ∑ i, r i * mom (z i) m‖ < ε

end Table

def Induces {K : Type} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime] (ι : K →+* ℂ_[p]) (w : HeightOneSpectrum (𝓞 K)) : Prop :=
  ∀ k : 𝓞 K, ‖ι (k : K)‖ < 1 ↔ k ∈ w.asIdeal

def OffT {E : Type} [Field E] [NumberField E] [StarRing E] (SB : Finset (HeightOneSpectrum (𝓞 E))) (q₁ c T : ℕ) : Prop :=
  ∀ P ∈ SB, conjPrime₂ P ∉ SB ∧ ((2 : ℕ) : 𝓞 E) ∉ P.asIdeal ∧ (q₁ : 𝓞 E) ∉ P.asIdeal ∧ (c : 𝓞 E) ∉ P.asIdeal ∧ (T : 𝓞 E) ∉ P.asIdeal

def DatumOffT {X : Fields} {a b : ℕ} (SB Sall : Finset (HeightOneSpectrum (𝓞 X.E))) (cA cB' : ℕ)
    (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) (w : HeightOneSpectrum (𝓞 X.K))
    (Φ : HomE X.E a b → X.K) : Prop :=
  (∀ x ∈ divLat cA (homAt Sall N N'), ∀ x' ∈ divLat cA (homAt Sall N N'), x - x' ∈ mulLat cB' (homAt SB N N') → Φ x = Φ x') ∧
  ∀ x ∈ divLat cA (homAt Sall N N'), w.valuation X.K (Φ x) ≤ 1

def MomAt {X : Fields} (A : Amb X) (Pr : Primes X) (u : Pr.Word) (good : Finset (HeightOneSpectrum (𝓞 X.E)) → Prop)
    {p : ℕ} [Fact p.Prime] (w : HeightOneSpectrum (𝓞 X.K)) (ι : X.K →+* ℂ_[p]) (uu : X.Tau → ℂ_[p]) : Prop :=
  ∀ (a b : ℕ), Even a → Even b →
  ∀ (SB Sall : Finset (HeightOneSpectrum (𝓞 X.E))), good SB → (∀ P, P ∈ Sall ↔ P ∈ Pr.vT u ∨ P ∈ SB) →
  ∀ (SG SG' : Finset (HeightOneSpectrum (𝓞 X.E))) (d : DecoSet X.E a (Pr.vT u) SG) (d' : DecoSet X.E b (Pr.vT u) SG'),
    StdAtT d.1 → StdAtT d'.1 →
  ∀ (cA cB' : ℕ), Nat.Coprime cA (Pr.T u) → Nat.Coprime cB' (Pr.T u) →
  ∀ Φ : HomE X.E a b → X.K, DatumOffT SB Sall cA cB' d.1.N d'.1.N w Φ →
    (seenBarC Pr u w →
      InMomClosure {m | RatAt A Sall cA (Pr.T u * cB') d.1.N d'.1.N (fun x => phiT X.K d.1 d'.1 x * Φ x) m}
        (fun m => ι (kerTable A Sall cA (Pr.T u * cB') d.1.N d'.1.N (fun x => phiT X.K d.1 d'.1 x * Φ x) m))
        1 (suppPts d.1 d'.1) (diracMom ι uu)) ∧
    (seenC Pr u w →
      InMomClosure {m | RatAt A Sall cA (Pr.T u * cB') d.1.N d'.1.N (fun x => phiT X.K d.1 d'.1 x * Φ x) m}
        (fun m => ι (kerTable A Sall cA (Pr.T u * cB') d.1.N d'.1.N (fun x => phiT X.K d.1 d'.1 x * Φ x) m))
        (((p : ℂ_[p]) ^ (X.f * a))⁻¹) (dualPts d.1 d'.1) (diracMom ι uu))

def MomT : Prop :=
  ∀ (D : D7) (X : Fields) (s : Seam D X), s.Ok → X.Ok →
  ∀ (Pr : Primes X), Pr.Ok → X.IsCond Pr.cond →
  ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), TaylorLogMetric.IsCurveIdeal D cc → TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
  ∀ (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ), TaylorLogMetric.IsChi D χ → IsDgen D cD →
  ∀ (u : Pr.Word), Nat.Coprime (Ideal.absNorm cc) (Pr.T u) →
  ∀ (p : ℕ) [Fact p.Prime], p = Pr.T u →
  ∀ (w : HeightOneSpectrum (𝓞 X.K)) (ι : X.K →+* ℂ_[p]), Induces ι w →
    ∃ uu : X.Tau → ℂ_[p], (∀ τ, ‖uu τ‖ = 1) ∧
      MomAt (ambOf s B χ cD) Pr u (fun SB => OffT SB D.host.q (Ideal.absNorm cc) (Pr.T u)) w ι uu

end GlobalTheory.IndefiniteRowSideFullHecke.StandardKernelAtTorus
