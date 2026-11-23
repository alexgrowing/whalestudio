import Mathlib
import Formalism.LocalToGlobal.Columns.AbelianHostFieldConditions
import Formalism.LocalToGlobal.Columns.StdLatUnimodular
import Formalism.LocalToGlobal.Columns.ScaledRamifiedLattice
import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
import Formalism.LocalToGlobal.KernelLattices.XiIndCClass
import Formalism.LocalToGlobal.KernelLattices.LateralTheory
import Formalism.LocalToGlobal.KernelLattices.ThDistC

open NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker

section Supp

variable {E : Type} [Field E] [NumberField E] [StarRing E] {a b : ℕ}

def adj (x : HomE E a b) : HomE E b a := Matrix.toLin' (LinearMap.toMatrix' x).conjTranspose

omit [NumberField E] in

theorem adj_single (x : HomE E a b) (α : Fin a) (β : Fin b) :
    adj x (Pi.single β 1) α = star (x (Pi.single α 1) β) := by
  rw [adj, Matrix.toLin'_apply, Matrix.mulVec_single_one]
  simp [LinearMap.toMatrix'_apply]

variable {ST SG SG' : Finset (HeightOneSpectrum (𝓞 E))}

def suppBar (d : Deco E a ST SG) (d' : Deco E b ST SG') : Set (HomE E a b) :=
  {x | ∀ P : ST, ∀ y ∈ d.at P.1, x y ∈ d'.at P.1 ∧ d'.f P (x y) = d.f P y}

def suppP (d : Deco E a ST SG) (d' : Deco E b ST SG') : Set (HomE E a b) :=
  {x | ∀ P : ST, ∀ y ∈ d'.at P.1, d'.f P y = 0 → adj x y ∈ d.at P.1}

def StdAtT {n : ℕ} (d : Deco E n ST SG) : Prop := ∀ P : ST, d.at P.1 = stdAt E n P.1

end Supp

section Mom

variable {p : ℕ} [Fact p.Prime]

def InIntClosure {H I : Type} (Sup : Set H) (tab : H → I → ℂ_[p]) (M : Set I) (J : I → ℂ_[p]) : Prop :=
  ∀ F : Finset I, (F : Set I) ⊆ M → ∀ ε : ℝ, 0 < ε →
    ∃ c : H →₀ ℂ_[p], (c.support : Set H) ⊆ Sup ∧ (∀ x, ‖c x‖ ≤ 1) ∧
      ∀ m ∈ F, ‖J m - c.sum fun x r => r * tab x m‖ < ε

theorem InIntClosure.single {H I : Type} {Sup : Set H} (tab : H → I → ℂ_[p]) (M : Set I) {x : H} (hx : x ∈ Sup) :
    InIntClosure Sup tab M (tab x) := by
  classical
  intro F _ ε hε
  refine ⟨Finsupp.single x 1, ?_, ?_, ?_⟩
  · intro y hy
    have := Finsupp.support_single_subset (Finset.mem_coe.1 hy)
    rw [Finset.mem_singleton] at this
    exact this ▸ hx
  · intro y
    rw [Finsupp.single_apply]
    split_ifs <;> simp
  · intro m _
    simp [hε]

variable {X : Fields} {a b : ℕ}

def Induces (ι : X.K →+* ℂ_[p]) (w : HeightOneSpectrum (𝓞 X.K)) : Prop :=
  ∀ y : 𝓞 X.K, y ∈ w.asIdeal ↔ ‖ι (y : X.K)‖ < 1

def ptTab (ι : X.K →+* ℂ_[p]) (u : X.Tau → ℂ_[p]) (x : HomE X.E a b) (m : DVar X.Tau a b →₀ ℕ) : ℂ_[p] :=
  m.prod fun k n => (u k.1 * ι (X.emb k.1 (adj x (Pi.single k.2.1 1) k.2.2))) ^ n

end Mom

section Tab

variable {X : Fields} (A : Amb X) {a b : ℕ} (S : Finset (HeightOneSpectrum (𝓞 X.E))) (cA cB : ℕ)
  (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) (Ξ : HomE X.E a b → X.K)

def jetSum (m : DVar X.Tau a b →₀ ℕ) : X.K :=
  latSum (divLat cA (homAt S N N')) (mulLat cB (homAt S N N')) fun x => Ξ x * A.jetK S N N' cB x m

def RatIdx : Set (DVar X.Tau a b →₀ ℕ) :=
  {m | ∀ x ∈ divLat cA (homAt S N N'), Ξ x ≠ 0 →
    ∃ k : X.K, A.σ₀ k = (A.chiF a b N N')⁻¹ * jetC A.cD (A.thInd S N N' cB x) m}

def OffDatum (SB : Finset (HeightOneSpectrum (𝓞 X.E))) (w : HeightOneSpectrum (𝓞 X.K)) (Ξ₀ : HomE X.E a b → X.K) : Prop :=
  ∀ x ∈ divLat cA (homAt SB N N'),
    w.valuation X.K (Ξ₀ x) ≤ 1 ∧ ∀ y ∈ mulLat cB (homAt SB N N'), Ξ₀ (x + y) = Ξ₀ x

end Tab

def AnaOk (D : Dat) {H : D7} (s : Seam H D.X) (cc : Ideal (𝓞 H.host.K)) (δ : ℂ) (χ : TaylorLogMetric.IdE H → ℂ)
    (cD : H.what₂.Tau → ℂ) : Prop :=
  s.Ok ∧ s.σ₀ = D.sig0 ∧ TaylorLogMetric.IsCurveIdeal H cc ∧ TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice H cc δ ∧ TaylorLogMetric.IsChi H χ ∧ IsDgen H cD

def MomAt (D : Dat) {H : D7} (cc : Ideal (𝓞 H.host.K)) (A : Amb D.X) (u : D.Pr.Word) [Fact (D.Pr.T u).Prime]
    (w : HeightOneSpectrum (𝓞 D.X.K)) (ι : D.X.K →+* ℂ_[D.Pr.T u]) (un : D.X.Tau → ℂ_[D.Pr.T u]) : Prop :=
  ∀ (sel : HeightOneSpectrum (𝓞 D.X.F) → HeightOneSpectrum (𝓞 D.X.E)) (S : Set ℕ) (mu : Tup D.X.F D.X.E D.X.K S)
    (cst : LocCst D.X (rowSG D.Pr sel mu)),
    IsSel D.X sel → hostS H.host.q H.host.d (D.Pr.g 0) (D.Pr.g 1) (Set.range D.Pr.T) ⊆ S →
    (∀ P ∈ rowSG D.Pr sel mu, Nat.Coprime (Ideal.absNorm cc) (qOf P)) →
    ∀ (i b : ℕ), i < D.R.m → b = D.R.N (i + 1) →
    ∀ (SG SG' : Finset (HeightOneSpectrum (𝓞 D.X.E)))
      (d : DecoSet D.X.E (D.R.N i) (D.Pr.vT u) SG) (d' : DecoSet D.X.E b (D.Pr.vT u) SG'),
      StdAtT d.1 → StdAtT d'.1 →
      ∀ Ξ₀ : HomE D.X.E (D.R.N i) b → D.X.K,
        OffDatum (cAof sel mu cst) (cBof sel mu cst u) d.1.N d'.1.N (rowSG D.Pr sel mu) w Ξ₀ →
        (seenBarC D.Pr u w →
          InIntClosure (suppBar d.1 d'.1) (ptTab ι un)
            (RatIdx A (Sall sel mu u) (cAof sel mu cst) (cBof sel mu cst u) d.1.N d'.1.N fun x => phiT D.X.K d.1 d'.1 x * Ξ₀ x)
            fun m => ι (jetSum A (Sall sel mu u) (cAof sel mu cst) (cBof sel mu cst u) d.1.N d'.1.N
              (fun x => phiT D.X.K d.1 d'.1 x * Ξ₀ x) m)) ∧
        (seenC D.Pr u w →
          InIntClosure (suppP d.1 d'.1)
            (fun x m => ((D.Pr.T u : ℂ_[D.Pr.T u]) ^ (D.X.f * D.R.N i))⁻¹ * ptTab ι un x m)
            (RatIdx A (Sall sel mu u) (cAof sel mu cst) (cBof sel mu cst u) d.1.N d'.1.N fun x => phiT D.X.K d.1 d'.1 x * Ξ₀ x)
            fun m => ι (jetSum A (Sall sel mu u) (cAof sel mu cst) (cBof sel mu cst u) d.1.N d'.1.N
              (fun x => phiT D.X.K d.1 d'.1 x * Ξ₀ x) m))

def JetMoments : Prop :=
  ∀ (D : Dat), D.Ok →
  ∀ (H : D7) (s : Seam H D.X) (cc : Ideal (𝓞 H.host.K)) (δ : ℂ) (B : Base H cc δ) (χ : TaylorLogMetric.IdE H → ℂ) (cD : H.what₂.Tau → ℂ),
    AnaOk D s cc δ χ cD →
    ∀ (u : D.Pr.Word) [Fact (D.Pr.T u).Prime], Nat.Coprime (Ideal.absNorm cc) (D.Pr.T u) →
    ∀ (w : HeightOneSpectrum (𝓞 D.X.K)) (ι : D.X.K →+* ℂ_[D.Pr.T u]), Induces ι w →
      ∃ un : D.X.Tau → ℂ_[D.Pr.T u], (∀ τ, ‖un τ‖ = 1) ∧ MomAt D cc (ambOf s B χ cD) u w ι un

end GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable
