import Mathlib
import Formalism.LocalToGlobal.KernelLattices.ThDistC
import Formalism.SharpRestriction.GlobalSchurBounds.GL3Columns
import Formalism.SharpRestriction.Divisibility.OrbitPlaces

open NumberField IsDedekindDomain

noncomputable section

namespace Formalism.L2.Ker

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Th1.H

def IntOff (S : Finset ℕ) (r : ℂ) : Prop :=
  r ∈ TaylorLogMetric.Qbar ∧ ∀ (p : ℕ) [Fact p.Prime] (lam : TaylorLogMetric.Qbar →+* ℂ_[p]), p ∉ S → ‖TaylorLogMetric.lamC lam r‖ ≤ 1

def SNum (S : Finset ℕ) (a : ℕ) : Prop := 0 < a ∧ ∀ q : ℕ, q.Prime → q ∣ a → q ∈ S

section Gen

variable {V : Type} [AddCommGroup V] [Module ℂ V]

def TorS (Λ : AddSubgroup V) (S : Finset ℕ) (x : V) : Prop := ∃ a : ℕ, SNum S a ∧ a • x ∈ Λ

def IsKerG (H : Sesq V) (Λ : AddSubgroup V) (S : Finset ℕ) (e Θ : V → ℂ) : Prop :=
  ∃ (n : ℕ) (r : Fin n → ℂ) (t : Fin n → V), (∀ k, IntOff S (r k)) ∧ (∀ k, TorS Λ S (t k)) ∧
    Θ = fun z => ∑ k, r k * opU H (t k) e z

def LatInt (H : Sesq V) (c : ℝ) (Λ : AddSubgroup V) : Prop :=
  IsHerm H ∧ (∀ x ∈ Λ, ∀ y ∈ Λ, ∃ m : ℤ, altE H x y = (m : ℝ)) ∧ ∀ x ∈ Λ, ∃ m : ℤ, qOf c H x = (m : ℝ)

end Gen

def XiLKer : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (H : Sesq V) (c : ℝ) (Λ : AddSubgroup V) (S : Finset ℕ) (SX SA SB : Finset V)
    (Φ e : V → ℂ), LatInt H c Λ → (∀ x ∈ SX, TorS Λ S x) → (∀ x ∈ SA, TorS Λ S x) → (∀ x ∈ SB, TorS Λ S x) → SNum S SA.card →
    (∀ x ∈ SX, ∀ s ∈ SA, IntOff S (Φ (s - x))) → IsKerG H Λ S e (xiL H (alphaQ c H) 1 SX SA SB Φ e)

def XiIndKer : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (H : Sesq V) (c : ℝ) (Λ M : AddSubgroup V) (S : Finset ℕ) (SA SB : Finset V)
    (e : V → ℂ) (s : V) (vol : ℝ), 0 < vol → LatInt H c Λ → TorS Λ S s → (∀ x ∈ SA, TorS Λ S x) → (∀ x ∈ SB, TorS Λ S x) → SNum S SA.card →
    IsKerG H Λ S e fun z => ((Real.sqrt vol : ℝ) : ℂ)⁻¹ * xiInd H (alphaQ c H) vol M SA SB e s z

def KerBridge : Prop :=
  ∀ (D : D7) (T : TaylorLogMetric.Tor D) (e : TaylorLogMetric.FamE D) (S : Finset ℕ) (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (Θ : TaylorLogMetric.VC D N N' → ℂ),
    IsKerG (formV (TaylorLogMetric.area T.abelian₂) D.what₂.Tau N N') (TaylorLogMetric.La D T L L') S (e N N' L L') Θ ↔ GL3Theta.IsKer D T e S L L' Θ

def HalvesTor : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (ι : Type) [Fintype ι] (a b : ℕ) (emb : ι → E →+* ℂ) (δ : ℂ)
    (AA0 : Submodule (𝓞 E) E) (SS : Finset (HeightOneSpectrum (𝓞 E)))
    (N : Submodule (𝓞 E) (Formalism.L2.Col.Sp E a)) (N' : Submodule (𝓞 E) (Formalism.L2.Col.Sp E b)) (c : ℕ), 0 < c →
    (∀ x ∈ AC emb δ AA0 SS N N' c, c • x ∈ LamC emb δ AA0 N N') ∧ (∀ x ∈ BC emb δ AA0 SS N N' c, c • x ∈ LamC emb δ AA0 N N') ∧
    ∀ x ∈ LamC emb δ AA0 N N', c • x ∈ BC emb δ AA0 SS N N' c

def ThCKer : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (ι : Type) [Fintype ι] (a b : ℕ) (emb : ι → E →+* ℂ) (δ : ℂ) (d : ℕ) (sc : ℝ)
    (AA0 : Submodule (𝓞 E) E) (SS : Finset (HeightOneSpectrum (𝓞 E)))
    (N : Submodule (𝓞 E) (Formalism.L2.Col.Sp E a)) (N' : Submodule (𝓞 E) (Formalism.L2.Col.Sp E b)) (c : ℕ) (S : Finset ℕ)
    (Ξ : Formalism.L2.Col.HomE E a b → ℂ) (θ : VV ι a b → ℂ),
    LatInt (HV sc) (Real.sqrt d / 2) (LamC emb δ AA0 N N') →
    relIdx (LamC emb δ AA0 N N') (AC emb δ AA0 SS N N' c) ≠ 0 →
    relIdx (BC emb δ AA0 SS N N' c) (LamC emb δ AA0 N N' ⊓ AC emb δ AA0 SS N N' c) ≠ 0 →
    relIdx (LamC emb δ AA0 N N') (BC emb δ AA0 SS N N' c) ≠ 0 →
    SNum S c → (∀ x, IntOff S (Ξ x)) →
      IsKerG (HV sc) (LamC emb δ AA0 N N') S θ (thC emb δ d sc AA0 SS N N' c Ξ θ)

section Read

open Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.L2.DIV

variable {D : D7} {X : Fields}

def Seam.push (s : Seam D X) {a b : ℕ} (F : VCx X.Tau a b → ℂ) : TaylorLogMetric.VC D a b → ℂ := fun z => F fun τ => z (s.iT τ)

def Seam.pt (s : Seam D X) {a b : ℕ} (t : VCx X.Tau a b) : TaylorLogMetric.VC D a b := fun τ => t (s.iT.symm τ)

def Seam.LatTie (s : Seam D X) (T : TaylorLogMetric.Tor D) (A : Amb X) {a b : ℕ} (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) : Prop :=
  ∀ t ∈ LamC (X.embC A.σ₀) A.δ A.AA N N', s.pt t ∈ TaylorLogMetric.La D T (s.lat N) (s.lat N')

variable {u : D.what₂.Word} (C : ColumnChain D.R D.what₂.Tau (D.hcW u))

structure KerRead (X : Fields) where
  SS : Finset (HeightOneSpectrum (𝓞 X.E))
  lev : ℕ
  N : ∀ i, C.cls i → Submodule (𝓞 X.E) (Sp X.E (D.R.N i))
  Xi : ∀ i, C.cls i → C.cls (i + 1) → HomE X.E (D.R.N i) (D.R.N (i + 1)) → ℂ
  pin : ∀ i, C.cls i → Prop

variable {C}

def KerRead.Th (r : KerRead C X) (s : Seam D X) (A : Amb X) (i : ℕ) (c : C.cls i) (c' : C.cls (i + 1)) :
    TaylorLogMetric.VC D (D.R.N i) (D.R.N (i + 1)) → ℂ :=
  s.push (thC (X.embC A.σ₀) A.δ A.d A.sc A.AA r.SS (r.N i c) (r.N (i + 1) c') r.lev (r.Xi i c c') (A.e _ _ (r.N i c) (r.N (i + 1) c')))

variable {Pr : Primes X} (Ch : Chars X Pr D.R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr D.R (QE sel (mu : Chr X.F X.E X.K)))

def KerRead.IsChain (r : KerRead C X) (σ : X.K →+* ℂ) (v : Pr.Word) (m2 : ℕ) : Prop :=
  r.SS = Sall sel mu v ∧ r.lev = levC sel mu cst v ∧
  ∃ (pt : ∀ i, i ≤ m2 + 1 → C.cls i → ChPt (R := D.R) sel mu v i) (ix : ∀ i, i ≤ m2 → C.cls i → L.β i)
    (yb : C.cls (m2 + 1) → Set (Sp X.E (D.R.N (m2 + 1)))) (row : C.cls (m2 + 1 + 1) → Option (RowPt Pr D.R sel mu)),
    (∀ i (hi : i ≤ m2 + 1) c, r.N i c = (pt i hi c).deco.1.N) ∧
    (∀ c', yb c' ∈ ybSet sel mu cst (pt (m2 + 1) le_rfl c').deco.1.N) ∧
    (∀ i (hi : i < m2) c c' x, r.Xi i c c' x =
      σ (XiEntry Ch sel mu cst L i (ix i hi.le c) (ix (i + 1) hi c') (pt i (by omega) c) (pt (i + 1) (by omega) c') x)) ∧
    (∀ c c' x, r.Xi m2 c c' x =
      σ (XiCpl1 Ch sel mu cst L m2 (ix m2 le_rfl c) (pt m2 (Nat.le_succ _) c) (pt (m2 + 1) le_rfl c') (yb c') x)) ∧
    (∀ c' d, row c' = some d → HEq (r.N (m2 + 1 + 1) c') (tilQ sel mu v d).1.N) ∧
    (∀ c c' d, row c' = some d → HEq (r.Xi (m2 + 1) c c') fun x => σ (XiCpl2 Ch sel mu cst m2 (pt (m2 + 1) le_rfl c) (yb c) d x)) ∧
    (∀ i, i ≤ m2 + 1 → ∀ c, r.pin i c) ∧ ∀ c', r.pin (m2 + 1 + 1) c' ↔ ∃ d, row c' = some d

def KerRead.Hyp (r : KerRead C X) (s : Seam D X) (A : Amb X) (T : TaylorLogMetric.Tor D) (e : TaylorLogMetric.FamE D) (S0 : Finset ℕ) (i : ℕ) : Prop :=
  A.sc = (TaylorLogMetric.area T.abelian₂)⁻¹ ∧ SNum S0 r.lev ∧ ∀ (c : C.cls i) (c' : C.cls (i + 1)),
    s.push (A.e _ _ (r.N i c) (r.N (i + 1) c')) = e _ _ (s.lat (r.N i c)) (s.lat (r.N (i + 1) c')) ∧
    s.LatTie T A (r.N i c) (r.N (i + 1) c') ∧
    LatInt (HV A.sc) (Real.sqrt A.d / 2) (LamC (X.embC A.σ₀) A.δ A.AA (r.N i c) (r.N (i + 1) c')) ∧
    relIdx (LamC (X.embC A.σ₀) A.δ A.AA (r.N i c) (r.N (i + 1) c')) (AC (X.embC A.σ₀) A.δ A.AA r.SS (r.N i c) (r.N (i + 1) c') r.lev) ≠ 0 ∧
    relIdx (BC (X.embC A.σ₀) A.δ A.AA r.SS (r.N i c) (r.N (i + 1) c') r.lev)
      (LamC (X.embC A.σ₀) A.δ A.AA (r.N i c) (r.N (i + 1) c') ⊓ AC (X.embC A.σ₀) A.δ A.AA r.SS (r.N i c) (r.N (i + 1) c') r.lev) ≠ 0 ∧
    relIdx (LamC (X.embC A.σ₀) A.δ A.AA (r.N i c) (r.N (i + 1) c')) (BC (X.embC A.σ₀) A.δ A.AA r.SS (r.N i c) (r.N (i + 1) c') r.lev) ≠ 0 ∧
    ∀ x, IntOff S0 (r.Xi i c c' x)

end Read

def ReadIsKer : Prop :=
  ∀ (D : D7) (X : Formalism.L2.Col.Fields) (u : D.what₂.Word) (C : ColumnChain D.R D.what₂.Tau (D.hcW u)) (r : KerRead C X) (s : Seam D X) (A : Amb X)
    (T : TaylorLogMetric.Tor D) (e : TaylorLogMetric.FamE D) (S0 : Finset ℕ) (i : ℕ), r.Hyp s A T e S0 i →
    ∀ c c', GL3Theta.IsKer D T e S0 (s.lat (r.N i c)) (s.lat (r.N (i + 1) c')) (r.Th s A i c c')

section Wt

open MvPolynomial Formalism.L2.DIV

variable {K : Type} [Field K] {ι : Type} [Fintype ι] {a b n : ℕ}

def colSub (β : ι → Matrix (Fin n) (Fin n) K) : Pol K ι n →ₐ[K] Pol K ι n :=
  aeval fun v => ∑ r : Fin n, C (β v.1 r v.2.2) * X (v.1, v.2.1, r)

def IsBor (β : ι → Matrix (Fin n) (Fin n) K) : Prop :=
  ∀ τ, (∀ r s, s < r → β τ r s = 0) ∧ ∀ r, β τ r r ≠ 0

def WtPol (K : Type) [Field K] {ι : Type} [Fintype ι] {n : ℕ} (ν : ι → Fin n → ℕ) : Submodule K (Pol K ι n) where
  carrier := {Q | ∀ β : ι → Matrix (Fin n) (Fin n) K, IsBor β → colSub β Q = (∏ τ, ∏ r, β τ r r ^ ν τ r) • Q}
  add_mem' := by
    intro P Q hP hQ β hβ
    rw [map_add, hP β hβ, hQ β hβ, smul_add]
  zero_mem' := by
    intro β _
    rw [map_zero, smul_zero]
  smul_mem' := by
    intro c Q hQ β hβ
    rw [map_smul, hQ β hβ, smul_comm]

def extNu (b : ℕ) (ν : ι → Fin a → ℕ) : ι → Fin b → ℕ := fun τ r => if h : r.1 < a then ν τ ⟨r.1, h⟩ else 0

end Wt

def JetWt : Prop :=
  ∀ (K : Type) [Field K] (ι : Type) [Fintype ι] (a b : ℕ), a ≤ b → ∀ (J : (DVar ι a b →₀ ℕ) → K) (ν : ι → Fin a → ℕ),
    ∀ Q ∈ WtPol K ν, jetMap J (fun _ => 0) Q ∈ WtPol K (extNu b ν)

section UnfG

open MvPolynomial Formalism.L2.DIV

variable {ι : Type} [Fintype ι] {a b : ℕ} {Y Y' : Type}

def frPolyG (fr : Y → ι → Matrix (Fin a) (Fin a) ℂ) : Pol ℂ ι a →ₗ[ℂ] (Y → ℂ) where
  toFun Q := fun y => eval (fun k : ι × Fin a × Fin a => fr y k.1 k.2.1 k.2.2) Q
  map_add' P Q := by funext y; simp
  map_smul' c Q := by funext y; simp

def frInvG (fr : Y → ι → Matrix (Fin a) (Fin a) ℂ) : (Y → ℂ) →ₗ[ℂ] Pol ℂ ι a :=
  Classical.epsilon fun g => g ∘ₗ frPolyG fr = LinearMap.id

def unfG (fr : Y → ι → Matrix (Fin a) (Fin a) ℂ) (fr' : Y' → ι → Matrix (Fin b) (Fin b) ℂ) (cD : ι → ℂ) (Θ : VCx ι a b → ℂ) :
    (Y → ℂ) →ₗ[ℂ] (Y' → ℂ) :=
  frPolyG fr' ∘ₗ jetMap (jetC cD Θ) (fun _ => 0) ∘ₗ frInvG fr

def evG {K : Type} [Field K] (fr : Y → ι → Matrix (Fin a) (Fin a) ℂ) (sh : ι → ℤ) (σ : K →+* ℂ) (P : Pol K ι a) : Y → ℂ :=
  fun y => (∏ τ, (fr y τ).det ^ sh τ) * eval₂ σ (fun k : ι × Fin a × Fin a => fr y k.1 k.2.1 k.2.2) P

def IsVLam (fr : Y → ι → Matrix (Fin a) (Fin a) ℂ) (lam : ι → Fin a → ℤ) (f : Y → ℂ) : Prop :=
  (∃ (Q : Pol ℂ ι a) (k : ι → ℕ), ∀ y, f y * ∏ τ, (fr y τ).det ^ k τ = frPolyG fr Q y) ∧
  ∀ (y y₂ : Y) (β : ι → Matrix (Fin a) (Fin a) ℂ), IsBor β → (∀ τ, fr y₂ τ = fr y τ * β τ) → f y₂ = (∏ τ, ∏ r, β τ r r ^ lam τ r) * f y

end UnfG

def UnfGEv : Prop :=
  ∀ (K : Type) [Field K] (ι : Type) [Fintype ι] (a b : ℕ) (Y Y' : Type) (fr : Y → ι → Matrix (Fin a) (Fin a) ℂ) (fr' : Y' → ι → Matrix (Fin b) (Fin b) ℂ),
    Function.Injective (frPolyG fr) → (∀ y τ, (fr y τ).det ≠ 0) →
    ∀ (σ : K →+* ℂ) (cD : ι → ℂ) (Θ : VCx ι a b → ℂ) (J : (DVar ι a b →₀ ℕ) → K) (z : ℂ), (∀ m, σ (J m) = z * jetC cD Θ m) →
    ∀ (sh sS sD : ι → ℤ) (n : ι → ℕ), (∀ τ, sh τ + sS τ = n τ) → ∀ P : DIV.Pol K ι a,
      evG fr' (fun τ => -sD τ) σ (jetMap J n P) =
        z • mulFun (fun y' => (∏ τ, (fr' y' τ).det ^ sD τ)⁻¹) (unfG fr fr' cD Θ (mulFun (fun y => ∏ τ, (fr y τ).det ^ sS τ) (evG fr sh σ P)))

def ThDistUnf : Prop :=
  ∀ (X : Formalism.L2.Col.Fields) (A : Amb X) (a b : ℕ) (Sall SB : Finset (HeightOneSpectrum (𝓞 X.E))) (D : ℕ)
    (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (mU : HeightOneSpectrum (𝓞 X.E) → X.Kˣ) (mI : SB → X.E → X.K)
    (lam : X.Tau → DomWeight a) (lam' : X.Tau → DomWeight b) (n : X.Tau → ℕ), JetInVV X.K lam lam' n → A.JetsRat a b Sall D →
    ∀ (Y Y' : Type) (fr : Y → X.Tau → Matrix (Fin a) (Fin a) ℂ) (fr' : Y' → X.Tau → Matrix (Fin b) (Fin b) ℂ),
    Function.Injective (frPolyG fr) → (∀ y τ, (fr y τ).det ≠ 0) → ∀ (sh sS sD : X.Tau → ℤ), (∀ τ, sh τ + sS τ = n τ) →
    ∀ (N : Submodule (𝓞 X.E) (Formalism.L2.Col.Sp X.E a)) (f : Formalism.L2.Col.Frs X.E a SB) (N' : Submodule (𝓞 X.E) (Formalism.L2.Col.Sp X.E b)) (f' : Formalism.L2.Col.Frs X.E b SB)
      (c : ℕ) (x : Formalism.L2.Col.HomE X.E a b), InRange Sall D c N N' x → ∀ P : DIV.VV X.K lam,
      evG fr' (fun τ => -sD τ) A.σ₀ ((thDistC A Sall SB D sel mU mI lam lam' n N f N' f' c x P : DIV.VV X.K lam') : DIV.Pol X.K X.Tau b) =
        (A.σ₀ (muInvDet sel SB mU mI N f * (muInvDet sel SB mU mI N' f')⁻¹) * (A.chiF a b N N')⁻¹) •
          mulFun (fun y' => (∏ τ, (fr' y' τ).det ^ sD τ)⁻¹)
            (unfG fr fr' A.cD (A.thInd Sall N N' c x) (mulFun (fun y => ∏ τ, (fr y τ).det ^ sS τ) (evG fr sh A.σ₀ (P : DIV.Pol X.K X.Tau a))))

def SharpVIs : Prop :=
  ∀ (ι : Type) [Fintype ι] (a : ℕ) (Y : Type) (fr : Y → ι → Matrix (Fin a) (Fin a) ℂ),
    (∀ f : ι → Matrix (Fin a) (Fin a) ℂ, (∃ y, fr y = f) ↔ ∀ τ, (f τ).det ≠ 0) →
    ∀ (lam : ι → Fin a → ℤ) (sS : ι → ℤ) (ν : ι → Fin a → ℕ), (∀ τ r, lam τ r + sS τ = ν τ r) → ∀ F : Y → ℂ,
      (∃ Q ∈ WtPol ℂ ν, F = frPolyG fr Q) ↔
        (∃ f, IsVLam fr lam f ∧ F = mulFun (fun y => ∏ τ, (fr y τ).det ^ sS τ) f) ∧ ∃ Q, F = frPolyG fr Q

def SharpPoly : Prop :=
  ∀ (ι : Type) [Fintype ι] (a : ℕ) (Y : Type) (fr : Y → ι → Matrix (Fin a) (Fin a) ℂ),
    (∀ f : ι → Matrix (Fin a) (Fin a) ℂ, (∃ y, fr y = f) ↔ ∀ τ, (f τ).det ≠ 0) →
    ∀ (lam : ι → Fin a → ℤ) (sS : ι → ℤ) (ν : ι → Fin a → ℕ), (∀ τ r, lam τ r + sS τ = ν τ r) → ∀ f, IsVLam fr lam f →
      ∃ Q, mulFun (fun y => ∏ τ, (fr y τ).det ^ sS τ) f = frPolyG fr Q

def VVInWt : Prop :=
  ∀ (K : Type) [Field K] (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n) (k : ι → ℕ), ∀ P ∈ DIV.VV K lam,
    P * ∏ τ, frDet K n τ ^ k τ ∈ WtPol K (fun τ r => (lam τ).natW r + k τ)

def WtInVV : Prop :=
  ∀ (K : Type) [Field K] [Infinite K] (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n),
    WtPol K (fun τ r => (lam τ).natW r) ≤ DIV.VV K lam

def JetInVVRed : Prop :=
  VVInWt → WtInVV → ∀ (K : Type) [Field K] [Infinite K] (ι : Type) [Fintype ι] (a b : ℕ), a ≤ b →
    ∀ (lam : ι → DomWeight a) (lam' : ι → DomWeight b) (n : ι → ℕ),
    (∀ τ r, (lam' τ).natW r = extNu b (fun τ r => (lam τ).natW r + n τ) τ r) → JetInVV K lam lam' n

def JetInVVOf : Prop :=
  ∀ (K : Type) [Field K] [Infinite K] (ι : Type) [Fintype ι] (a b : ℕ), a ≤ b →
    ∀ (lam : ι → DomWeight a) (lam' : ι → DomWeight b) (n : ι → ℕ),
    (∀ τ r, (lam' τ).natW r = extNu b (fun τ r => (lam τ).natW r + n τ) τ r) → JetInVV K lam lam' n

def NarrowSat : Prop :=
  ∀ (ι : Type) [Fintype ι] (a b : ℕ) (Y Y' : Type) (fr : Y → ι → Matrix (Fin a) (Fin a) ℂ) (fr' : Y' → ι → Matrix (Fin b) (Fin b) ℂ), a ≤ b →
    Function.Injective (frPolyG fr) → ∀ (cD : ι → ℂ) (Θ : VCx ι a b → ℂ) (ν : ι → Fin a → ℕ),
    ∃ U : (Y → ℂ) →ₗ[ℂ] (Y' → ℂ), (∀ F, ∃ Q' ∈ WtPol ℂ (extNu b ν), U F = frPolyG fr' Q') ∧
      ∀ Q ∈ WtPol ℂ ν, U (frPolyG fr Q) = unfG fr fr' cD Θ (frPolyG fr Q)

def nuT (D : D7) (u : D.what₂.Word) (i : ℕ) : D.what₂.Tau → Fin (D.R.N i) → ℕ := fun τ r => ⌊DV.nuRow D u (i + 1) τ r⌋₊

def NuTIs : Prop :=
  ∀ (D : D7) (u : D.what₂.Word) (i : ℕ), i < D.R.m → ∀ (τ : D.what₂.Tau) (r : Fin (D.R.N i)),
    ((nuT D u i τ r : ℕ) : ℝ) = DV.nuRow D u (i + 1) τ r ∧ 0 < nuT D u i τ r

section Unf

variable {D : D7} {u : D.what₂.Word} {C : ColumnChain D.R D.what₂.Tau (D.hcW u)}

def frPoly (O : GL3Theta.LiftObj D C) (i : ℕ) : MvPolynomial (GL3Theta.FrV D (D.R.N i)) ℂ →ₗ[ℂ] (C.Y i → ℂ) where
  toFun Q := fun y => GL3Theta.evFr D Q (O.frm i y)
  map_add' P Q := by funext y; simp [GL3Theta.evFr]
  map_smul' a Q := by funext y; simp [GL3Theta.evFr]

def frInv (O : GL3Theta.LiftObj D C) (i : ℕ) : (C.Y i → ℂ) →ₗ[ℂ] MvPolynomial (GL3Theta.FrV D (D.R.N i)) ℂ :=
  Classical.epsilon fun g => g ∘ₗ frPoly O i = LinearMap.id

def unfC (O : GL3Theta.LiftObj D C) (i : ℕ) (Θ : TaylorLogMetric.VC D (D.R.N i) (D.R.N (i + 1)) → ℂ) : (C.Y i → ℂ) →ₗ[ℂ] (C.Y (i + 1) → ℂ) :=
  frPoly O (i + 1) ∘ₗ jetMap (ι := D.what₂.Tau) (jetC O.dgen Θ) (fun _ => 0) ∘ₗ frInv O i

def chainC (O : GL3Theta.LiftObj D C) : ColumnChain D.R D.what₂.Tau (D.hcW u) :=
  C.twist { C.ownData with unf := fun i c c' => unfC O i (O.Th i c c') }

def liftC (O : GL3Theta.LiftObj D C) : GL3Theta.LiftObj D (chainC O) where
  mt := O.mt
  L0 := O.L0
  lattice_integral_coordinates := O.lattice_integral_coordinates
  lat := O.lat
  dt := O.dt
  dt_lat := O.dt_lat
  c13 := O.c13
  frm := O.frm
  frm_inj := O.frm_inj
  frm_range := O.frm_range
  frm_de := O.frm_de
  dgen := O.dgen
  dgen_gen := O.dgen_gen
  S := O.S
  Th := O.Th

def withTh (O : GL3Theta.LiftObj D C) (S : Finset ℕ) (Th : ∀ i, C.cls i → C.cls (i + 1) → TaylorLogMetric.VC D (D.R.N i) (D.R.N (i + 1)) → ℂ) : GL3Theta.LiftObj D C :=
  { O with S := S, Th := Th }

def UnfIs (O : GL3Theta.LiftObj D C) (i : ℕ) (ν : D.what₂.Tau → Fin (D.R.N i) → ℕ) : Prop :=
  ∀ c c', ∀ Q ∈ WtPol ℂ ν, C.unf i c c' (frPoly O i Q) = unfC O i (O.Th i c c') (frPoly O i Q)

def UnfIsAll (O : GL3Theta.LiftObj D C) (i : ℕ) : Prop :=
  ∀ c c' (Q : MvPolynomial (GL3Theta.FrV D (D.R.N i)) ℂ), C.unf i c c' (frPoly O i Q) = unfC O i (O.Th i c c') (frPoly O i Q)

end Unf

def FrPolyInj : Prop :=
  ∀ (D : D7) (u : D.what₂.Word) (C : ColumnChain D.R D.what₂.Tau (D.hcW u)) (O : GL3Theta.LiftObj D C) (i : ℕ), i ≤ D.R.m →
    Function.Injective (frPoly O i)

def UnfCFormula : Prop :=
  ∀ (D : D7) (u : D.what₂.Word) (C : ColumnChain D.R D.what₂.Tau (D.hcW u)) (O : GL3Theta.LiftObj D C) (i : ℕ), i ≤ D.R.m →
    ∀ (Θ : TaylorLogMetric.VC D (D.R.N i) (D.R.N (i + 1)) → ℂ) (Q : MvPolynomial (GL3Theta.FrV D (D.R.N i)) ℂ) (y' : C.Y (i + 1)),
      unfC O i Θ (fun y => GL3Theta.evFr D Q (O.frm i y)) y' = GL3Theta.applyAt0 D (GL3Theta.polD D O.dgen Q (O.frm (i + 1) y')) Θ

def UnfIsIff : Prop :=
  ∀ (D : D7) (u : D.what₂.Word) (C : ColumnChain D.R D.what₂.Tau (D.hcW u)) (O : GL3Theta.LiftObj D C) (i : ℕ), i ≤ D.R.m →
    ∀ ν : D.what₂.Tau → Fin (D.R.N i) → ℕ, (UnfIs O i ν ↔ ∀ c c', ∀ Q ∈ WtPol ℂ ν, ∀ y' : C.Y (i + 1),
      C.unf i c c' (fun y => GL3Theta.evFr D Q (O.frm i y)) y' = GL3Theta.applyAt0 D (GL3Theta.polD D O.dgen Q (O.frm (i + 1) y')) (O.Th i c c'))

def UnfIsAllIff : Prop :=
  ∀ (D : D7) (u : D.what₂.Word) (C : ColumnChain D.R D.what₂.Tau (D.hcW u)) (O : GL3Theta.LiftObj D C) (i : ℕ), i ≤ D.R.m →
    (UnfIsAll O i ↔ ∀ c c' (Q : MvPolynomial (GL3Theta.FrV D (D.R.N i)) ℂ) (y' : C.Y (i + 1)),
      C.unf i c c' (fun y => GL3Theta.evFr D Q (O.frm i y)) y' = GL3Theta.applyAt0 D (GL3Theta.polD D O.dgen Q (O.frm (i + 1) y')) (O.Th i c c'))

def LiftTieC : Prop :=
  ∀ (D : D7) (T : TaylorLogMetric.Tor D) (e : TaylorLogMetric.FamE D) (u : D.what₂.Word) (C : ColumnChain D.R D.what₂.Tau (D.hcW u)) (O : GL3Theta.LiftObj D C) (i : ℕ),
    i ≤ D.R.m → (∀ c c', GL3Theta.IsKer D T e O.S (O.lat i c).1 (O.lat (i + 1) c').1 (O.Th i c c')) → GL3Theta.liftTie D T e (liftC O) i

def LiftTieRead : Prop :=
  ∀ (D : D7) (X : Formalism.L2.Col.Fields) (u : D.what₂.Word) (C : ColumnChain D.R D.what₂.Tau (D.hcW u)) (O : GL3Theta.LiftObj D C) (r : KerRead C X)
    (s : Seam D X) (A : Amb X) (T : TaylorLogMetric.Tor D) (e : TaylorLogMetric.FamE D) (S0 : Finset ℕ) (i : ℕ), i ≤ D.R.m → r.Hyp s A T e S0 i →
    (∀ c, (O.lat i c).1 = s.lat (r.N i c)) → (∀ c', (O.lat (i + 1) c').1 = s.lat (r.N (i + 1) c')) →
    GL3Theta.liftTie D T e (liftC (withTh O S0 (r.Th s A))) i ∧
    (GL3Theta.liftTie D T e (withTh O S0 (r.Th s A)) i ↔ UnfIsAll (withTh O S0 (r.Th s A)) i)

def UnfCIsG : Prop :=
  ∀ (D : D7) (u : D.what₂.Word) (C : ColumnChain D.R D.what₂.Tau (D.hcW u)) (O : GL3Theta.LiftObj D C) (i : ℕ)
    (Θ : TaylorLogMetric.VC D (D.R.N i) (D.R.N (i + 1)) → ℂ), unfC O i Θ = unfG (O.frm i) (O.frm (i + 1)) O.dgen Θ

def UnfCWt : Prop :=
  ∀ (D : D7) (u : D.what₂.Word) (C : ColumnChain D.R D.what₂.Tau (D.hcW u)) (O : GL3Theta.LiftObj D C) (i : ℕ), i ≤ D.R.m →
    ∀ (Θ : TaylorLogMetric.VC D (D.R.N i) (D.R.N (i + 1)) → ℂ) (ν : D.what₂.Tau → Fin (D.R.N i) → ℕ), ∀ Q ∈ WtPol ℂ ν,
      ∃ Q' ∈ WtPol ℂ (extNu (D.R.N (i + 1)) ν), unfC O i Θ (frPoly O i Q) = frPoly O (i + 1) Q'

def UnfCVLam : Prop :=
  ∀ (D : D7) (u : D.what₂.Word) (C : ColumnChain D.R D.what₂.Tau (D.hcW u)) (O : GL3Theta.LiftObj D C) (i : ℕ), i < D.R.m →
    ∀ (Θ : TaylorLogMetric.VC D (D.R.N i) (D.R.N (i + 1)) → ℂ) (ν : D.what₂.Tau → Fin (D.R.N i) → ℕ), ∀ Q ∈ WtPol ℂ ν,
      IsVLam (O.frm (i + 1)) (fun τ r => (extNu (D.R.N (i + 1)) ν τ r : ℤ) - C.sDiv i τ) (C.divDe i (unfC O i Θ (frPoly O i Q)))

def ChainCEv : Prop :=
  ∀ (D : D7) (u : D.what₂.Word) (C : ColumnChain D.R D.what₂.Tau (D.hcW u)) (O : GL3Theta.LiftObj D C) (i : ℕ), i < D.R.m →
    ∀ (K : Type) [Field K] (σ : K →+* ℂ) (c : C.cls i) (c' : C.cls (i + 1)) (J : (DVar D.what₂.Tau (D.R.N i) (D.R.N (i + 1)) →₀ ℕ) → K) (z : ℂ),
    (∀ m, σ (J m) = z * jetC O.dgen (O.Th i c c') m) → ∀ (sh : D.what₂.Tau → ℤ) (n : D.what₂.Tau → ℕ), (∀ τ, sh τ + C.sSharp i τ = n τ) →
    ∀ P : DIV.Pol K D.what₂.Tau (D.R.N i),
      evG (O.frm (i + 1)) (fun τ => -C.sDiv i τ) σ (jetMap J n P) =
        z • (chainC O).divDe i ((chainC O).unf i c c' ((chainC O).sharp i (evG (O.frm i) sh σ P)))

def AllForcesZero : Prop :=
  ∀ (D : D7) (u : D.what₂.Word) (C : ColumnChain D.R D.what₂.Tau (D.hcW u)) (O : GL3Theta.LiftObj D C) (i : ℕ), i < D.R.m → UnfIsAll O i →
    ∀ ν' : D.what₂.Tau → Fin (D.R.N (i + 1)) → ℕ, (∃ τ r, ν' τ r ≠ 0) →
    (∀ c c' F, ∃ Q' ∈ WtPol ℂ ν', C.unf i c c' F = frPoly O (i + 1) Q') → ∀ c c', O.Th i c c' 0 = 0

def FormsSharp : Prop :=
  SharpPoly → ∀ (D : D7) (u : D.what₂.Word) (C : ColumnChain D.R D.what₂.Tau (D.hcW u)) (O : GL3Theta.LiftObj D C) (i : ℕ), i ≤ D.R.m →
    ∀ (ν : D.what₂.Tau → Fin (D.R.N i) → ℕ) (f : C.Y i → ℂ), IsVLam (O.frm i) (fun τ r => (ν τ r : ℤ) - C.sSharp i τ) f →
      ∃ Q ∈ WtPol ℂ ν, C.sharp i f = frPoly O i Q

def TiedOnModels : Prop :=
  ∀ (D : D7) (u : D.what₂.Word) (C : ColumnChain D.R D.what₂.Tau (D.hcW u)) (O : GL3Theta.LiftObj D C) (i : ℕ), i < D.R.m →
    ∀ ν : D.what₂.Tau → Fin (D.R.N i) → ℕ, UnfIs O i ν →
    ∀ (K : Type) [Field K] (σ : K →+* ℂ) (lam : D.what₂.Tau → DomWeight (D.R.N i)) (n : D.what₂.Tau → ℕ), (∀ τ r, (lam τ).natW r + n τ = ν τ r) →
    ∀ (c : C.cls i) (c' : C.cls (i + 1)) (J : (DVar D.what₂.Tau (D.R.N i) (D.R.N (i + 1)) →₀ ℕ) → K) (z : ℂ),
    (∀ m, σ (J m) = z * jetC O.dgen (O.Th i c c') m) → ∀ sh : D.what₂.Tau → ℤ, (∀ τ, sh τ + C.sSharp i τ = n τ) → ∀ P ∈ DIV.VV K lam,
      z • C.Kmap i c c' (evG (O.frm i) sh σ P) =
        (C.rhoDet i c * C.rhoDet' i c') • evG (O.frm (i + 1)) (fun τ => -C.sDiv i τ) σ (jetMap J n P)

def LiftFormulaTied : Prop :=
  ∀ (D : D7) (u : D.what₂.Word) (C : ColumnChain D.R D.what₂.Tau (D.hcW u)) (O : GL3Theta.LiftObj D C) (i : ℕ), i < D.R.m →
    ∀ ν : D.what₂.Tau → Fin (D.R.N i) → ℕ, UnfIs O i ν →
    ∀ (φ : C.cls i → C.Y i → ℂ) (Q : C.cls i → MvPolynomial (GL3Theta.FrV D (D.R.N i)) ℂ), (∀ c, Q c ∈ WtPol ℂ ν) →
    (∀ c, C.sharp i (φ c) = frPoly O i (Q c)) → ∀ (c' : C.cls (i + 1)) (y' : C.Y (i + 1)),
      C.K i φ c' y' = ∑ c, (((Nat.card (C.stab i c) : ℕ) : ℂ)⁻¹) *
        ((((GL3Theta.rhoOf D O.mt i (O.dt i c) : ℂˣ) : ℂ) * ((GL3Theta.rhoOf' D O.mt i (O.dt (i + 1) c') : ℂˣ) : ℂ)) *
          ((∏ τ, (C.de (i + 1) y' τ) ^ (C.sDiv i τ))⁻¹ *
            GL3Theta.applyAt0 D (GL3Theta.polD D O.dgen (Q c) (O.frm (i + 1) y')) (O.Th i c c')))

def TransAlg (D : D7) (T : TaylorLogMetric.Tor D) (e : TaylorLogMetric.FamE D) : Prop :=
  ∀ N N' L L', TaylorLogMetric.admitted D N N' L L' → (∀ k : ℕ, ContDiff ℂ k (e N N' L L')) ∧
    ∀ t : TaylorLogMetric.VC D N N', (∃ a : ℕ, 0 < a ∧ a • t ∈ TaylorLogMetric.La D T L L') → ∀ α, TaylorLogMetric.taylor D (TaylorLogMetric.U D T t (e N N' L L')) α ∈ TaylorLogMetric.Qbar

def KerCombOf : Prop :=
  ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (e : TaylorLogMetric.FamE D), TransAlg D (TaylorLogMetric.tor0 D cc δ) e → GL3Theta.kerComb D cc δ e

section Ent

open Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.L2.DIV

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {K : G.Consts} {Y : DivX D} {cX : ExtraC}

structure KerEntTied (ex : Extra D L hT Gi Gl K Y cX) where
  cc : Ideal (𝓞 D.host.K)
  cc_rec : cc = D.host.ccK
  cc_ok : TaylorLogMetric.IsCurveIdeal D cc
  δ : ℂ
  δ_ok : TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ
  B : Base D cc δ
  χ : TaylorLogMetric.IdE D → ℂ
  χ_ok : TaylorLogMetric.IsChi D χ
  idl : D.Dt ⧸ D.UO → TaylorLogMetric.IdE D
  idl_ok : TaylorLogMetric.RelDetPinned D idl
  χ_rec : χ = TaylorLogMetric.chiRec D idl
  cD : D.what₂.Tau → ℂ
  X : Fields
  seam : Seam D X
  seam_ok : seam.Ok
  Pr : Primes X
  pr_ok : Pr.Ok
  g_rec : ∀ i, Pr.g i = D.host.g i
  Ch : Chars X Pr D.R.m
  sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)
  S : Set ℕ
  word : D.what₂.Word → Pr.Word
  T_rec : ∀ u, Pr.T (word u) = (D.mem u).A.T
  tup : D.what₂.Tup → Tup X.F X.E X.K S
  Q_rec : ∀ μ (p : ℕ), p ∈ Y.Qp μ ↔ p.Prime ∧ ∃ P ∈ QE sel (tup μ : Chr X.F X.E X.K), (p : 𝓞 X.E) ∈ P.asIdeal
  cst : ∀ μ, LocCst X (rowSG Pr sel (tup μ))
  idx : ∀ μ, ChIdx X Pr D.R (QE sel (tup μ : Chr X.F X.E X.K))
  m2 : ℕ
  glob : ChGlob X D.R.m
  glob_σ : glob.σ₀ = seam.σ₀
  glob_xi : seam.iE glob.xi0 = D.host.xi0
  idx_ok : ∀ μ, (idx μ).Ok Ch sel (tup μ) (cst μ) glob m2
  O : ∀ u μ, GL3Theta.LiftObj D (D.chTw u μ)
  rd : ∀ u μ, KerRead (D.chTw u μ) X
  rd_chain : ∀ u μ, (rd u μ).IsChain Ch sel (tup μ) (cst μ) (idx μ) seam.σ₀ (word u) m2
  O_dgen : ∀ u μ, (O u μ).dgen = cD
  O_S : ∀ u μ, (O u μ).S = insert (D.mem u).A.T ({D.host.g 0, D.host.g 1} ∪ Y.Qp μ)
  O_lat : ∀ u μ i c, ((O u μ).lat i c).1 = seam.lat ((rd u μ).N i c)
  O_Th : ∀ u μ i c c', (O u μ).Th i c c' = (rd u μ).Th seam (ambOf seam B χ cD) i c c'
  unf : ∀ u μ i, i < D.R.m → UnfIs (O u μ) i (nuT D u i)
  ent : KerEnt D Y ex.tw
  ent_lam : ∀ u w (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)), (ex.ker u w h).lam = ent.lam w
  kf : ∀ u μ w, LevFree Y u μ w → GL3Columns.KFTie ent (O u μ) w
  kf_un : ∀ u μ w (h : LevFree Y u μ w), (kf u μ w h).UnIs
  served : ∀ u w (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)), ThAtServed (ex.ker u w h) ent

def KerEntTied.amb {ex : Extra D L hT Gi Gl K Y cX} (t : KerEntTied ex) : Amb t.X := ambOf t.seam t.B t.χ t.cD

def KerEntTied.AAUnit {ex : Extra D L hT Gi Gl K Y cX} (t : KerEntTied ex) : Prop :=
  ∀ u μ, t.amb.AAUnit (Sall t.sel (t.tup μ) (t.word u))

def KerEntTied.Hyp {ex : Extra D L hT Gi Gl K Y cX} (t : KerEntTied ex) : Prop :=
  ∀ u μ i, i < D.R.m → (t.rd u μ).Hyp t.seam t.amb t.B.tor (t.B.eNat t.χ) (t.O u μ).S i

def KerEntTied.UnfAll {ex : Extra D L hT Gi Gl K Y cX} (t : KerEntTied ex) : Prop :=
  ∀ u μ i, i < D.R.m → UnfIsAll (t.O u μ) i

end Ent

def TiedKj : Prop :=
  ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC)
    (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex), t.Hyp → t.UnfAll → ∀ u μ, GL3Theta.kjTie D t.B.tor (t.B.eNat t.χ) u μ

def TiedLift : Prop :=
  ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC)
    (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex) u μ (i : ℕ), i < D.R.m →
    ∀ (φ : (D.chTw u μ).cls i → (D.chTw u μ).Y i → ℂ) (Q : (D.chTw u μ).cls i → MvPolynomial (GL3Theta.FrV D (D.R.N i)) ℂ), (∀ c, Q c ∈ WtPol ℂ (nuT D u i)) →
    (∀ c, (D.chTw u μ).sharp i (φ c) = frPoly (t.O u μ) i (Q c)) → ∀ (c' : (D.chTw u μ).cls (i + 1)) (y' : (D.chTw u μ).Y (i + 1)),
      (D.chTw u μ).K i φ c' y' = ∑ c, (((Nat.card ((D.chTw u μ).stab i c) : ℕ) : ℂ)⁻¹) *
        ((((GL3Theta.rhoOf D (t.O u μ).mt i ((t.O u μ).dt i c) : ℂˣ) : ℂ) * ((GL3Theta.rhoOf' D (t.O u μ).mt i ((t.O u μ).dt (i + 1) c') : ℂˣ) : ℂ)) *
          ((∏ τ, ((D.chTw u μ).de (i + 1) y' τ) ^ ((D.chTw u μ).sDiv i τ))⁻¹ *
            GL3Theta.applyAt0 D (GL3Theta.polD D (t.O u μ).dgen (Q c) ((t.O u μ).frm (i + 1) y')) ((t.rd u μ).Th t.seam t.amb i c c')))

def KFormTied : Prop :=
  ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC)
    (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex) (Ee : OrbitPlaces.Ent D), (∀ u i, Ee.nu u i = nuD D u i) → Ee.Th = t.ent.Th →
    OrbitPlaces.ConclusionW D → GL3Columns.kfAll t.ent t.O → OrbitPlaces.KmapRat t.ent → OrbitPlaces.KFi D ex.tw → OrbitPlaces.KForm Ee Y ex.tw 0

def FirstKernelLawReading : Prop :=
  ∀ (D : D7) (X : Formalism.L2.Col.Fields) (u : D.what₂.Word) (C : ColumnChain D.R D.what₂.Tau (D.hcW u)) (r : KerRead C X) (s : Seam D X) (A : Amb X)
    (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (e : TaylorLogMetric.FamE D) (S0 : Finset ℕ) (i : ℕ), r.Hyp s A (TaylorLogMetric.tor0 D cc δ) e S0 i →
    TransAlg D (TaylorLogMetric.tor0 D cc δ) e → ∀ c c', TaylorLogMetric.admitted D _ _ (s.lat (r.N i c)) (s.lat (r.N (i + 1) c')) →
    ∀ (p : ℕ) [Fact p.Prime] (lam : TaylorLogMetric.Qbar →+* ℂ_[p]), p ∉ S0 →
      TaylorLogMetric.IsComb D (TaylorLogMetric.tor0 D cc δ) e lam (s.lat (r.N i c)) (s.lat (r.N (i + 1) c')) (TaylorLogMetric.pSer D lam (r.Th s A i c c'))

def KerAlgOf : Prop :=
  ∀ (D : D7) (T : TaylorLogMetric.Tor D) (e : TaylorLogMetric.FamE D) (S : Finset ℕ) (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (Θ : TaylorLogMetric.VC D N N' → ℂ), TransAlg D T e → TaylorLogMetric.admitted D N N' L L' →
    GL3Theta.IsKer D T e S L L' Θ → TaylorLogMetric.CoefIn D Θ TaylorLogMetric.Qbar

def TiedInputs : Prop :=
  ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC)
    (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex),
    (t.UnfAll → ∀ u μ, ∀ i < D.R.m, ∀ dg, GL3Columns.liftTieH D (t.O u μ) i dg) ∧
    (t.Hyp → TransAlg D t.B.tor (t.B.eNat t.χ) → ∀ u μ, GL3Columns.ThAlg (t.O u μ))

def LatIntOfFacts : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (ι : Type) [Fintype ι] (a b : ℕ) (emb : ι → E →+* ℂ) (δ : ℂ) (d : ℕ) (sc : ℝ)
    (AA0 : Submodule (𝓞 E) E) (N : Submodule (𝓞 E) (Formalism.L2.Col.Sp E a)) (N' : Submodule (𝓞 E) (Formalism.L2.Col.Sp E b)),
    LaFacts emb δ d sc AA0 N N' → LatInt (HV sc) (Real.sqrt d / 2) (LamC emb δ AA0 N N')

def AmbOfHyp : Prop :=
  ∀ (D : D7) (X : Formalism.L2.Col.Fields) (s : Seam D X) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ),
    (ambOf s B χ cD).sc = (TaylorLogMetric.area B.tor.abelian₂)⁻¹ ∧
    ∀ (a b : ℕ) (N : Submodule (𝓞 X.E) (Formalism.L2.Col.Sp X.E a)) (N' : Submodule (𝓞 X.E) (Formalism.L2.Col.Sp X.E b)),
      s.push ((ambOf s B χ cD).e a b N N') = B.eNat χ a b (s.lat N) (s.lat N')

section ReadBack

open Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.L2.DIV

def ReadEntry : Prop :=
  ∀ (D : D7) (X : Fields) (u : D.what₂.Word) (C : ColumnChain D.R D.what₂.Tau (D.hcW u)) (r : KerRead C X) (s : Seam D X) (A : Amb X)
    (Pr : Primes X) (Ch : Chars X Pr D.R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ)
    (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr D.R (QE sel (mu : Chr X.F X.E X.K)))
    (σ : X.K →+* ℂ) (v : Pr.Word) (m2 : ℕ), r.IsChain Ch sel mu cst L σ v m2 →
    ∃ (pt : ∀ i, i ≤ m2 + 1 → C.cls i → ChPt (R := D.R) sel mu v i) (ix : ∀ i, i ≤ m2 → C.cls i → L.β i)
      (yb : C.cls (m2 + 1) → Set (Sp X.E (D.R.N (m2 + 1)))),
      (∀ i (hi : i < m2) c c', r.Th s A i c c' = s.push (thEntry Ch sel mu cst L (X.embC A.σ₀) σ A.δ A.d A.sc A.AA i (ix i hi.le c) (ix (i + 1) hi c')
        (pt i (by omega) c) (pt (i + 1) (by omega) c') (A.e _ _ (pt i (by omega) c).deco.1.N (pt (i + 1) (by omega) c').deco.1.N))) ∧
      ∀ c c', r.Th s A m2 c c' = s.push (thCpl1 Ch sel mu cst L (X.embC A.σ₀) σ A.δ A.d A.sc A.AA m2 (ix m2 le_rfl c)
        (pt m2 (Nat.le_succ _) c) (pt (m2 + 1) le_rfl c') (yb c') (A.e _ _ (pt m2 (Nat.le_succ _) c).deco.1.N (pt (m2 + 1) le_rfl c').deco.1.N))

end ReadBack

def SeamLat : Prop :=
  ∀ (D : D7) (X : Formalism.L2.Col.Fields) (s : Seam D X) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ),
    s.Ok → ∀ (a b : ℕ) (N : Submodule (𝓞 X.E) (Formalism.L2.Col.Sp X.E a)) (N' : Submodule (𝓞 X.E) (Formalism.L2.Col.Sp X.E b)),
      s.LatTie B.tor (ambOf s B χ cD) N N'

def LatIntSeam : Prop :=
  ∀ (D : D7) (X : Formalism.L2.Col.Fields) (s : Seam D X) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ),
    s.Ok → TaylorLogMetric.IsCurveIdeal D cc → TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
    ∀ (a b : ℕ) (N : Submodule (𝓞 X.E) (Formalism.L2.Col.Sp X.E a)) (N' : Submodule (𝓞 X.E) (Formalism.L2.Col.Sp X.E b)), TaylorLogMetric.admitted D a b (s.lat N) (s.lat N') →
      LatInt (HV (ambOf s B χ cD : Amb X).sc) (Real.sqrt (ambOf s B χ cD : Amb X).d / 2)
        (LamC (X.embC (ambOf s B χ cD : Amb X).σ₀) (ambOf s B χ cD : Amb X).δ (ambOf s B χ cD : Amb X).AA N N')

section Hyp0

open Formalism.L2.Col

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {K : G.Consts} {Y : DivX D} {cX : ExtraC}

def KerEntTied.Hyp0 {ex : Extra D L hT Gi Gl K Y cX} (t : KerEntTied ex) : Prop :=
  t.amb.AA.FG ∧ ∀ u μ i, i < D.R.m → ∀ (c : (D.chTw u μ).cls i) (c' : (D.chTw u μ).cls (i + 1)), (t.rd u μ).pin (i + 1) c' →
    IsSdLat ((t.rd u μ).N i c) ∧ IsSdLat ((t.rd u μ).N (i + 1) c') ∧
    ∀ x, IntOff (t.O u μ).S ((t.rd u μ).Xi i c c' x)

def KerEntTied.HypFree {ex : Extra D L hT Gi Gl K Y cX} (t : KerEntTied ex) : Prop :=
  ∀ u μ i, i < D.R.m → ∀ (c : (D.chTw u μ).cls i) (c' : (D.chTw u μ).cls (i + 1)), ¬ (t.rd u μ).pin (i + 1) c' →
    IsSdLat ((t.rd u μ).N i c) ∧ IsSdLat ((t.rd u μ).N (i + 1) c') ∧
    ∀ x, IntOff (t.O u μ).S ((t.rd u μ).Xi i c c' x)

end Hyp0

def LevSNum : Prop :=
  ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC)
    (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex) u μ, SNum (t.O u μ).S (t.rd u μ).lev

def HypOfHyp0 : Prop :=
  ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC)
    (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex), t.Hyp0 → t.HypFree → t.Hyp

def ThIndKer : Prop :=
  ∀ (X : Formalism.L2.Col.Fields) (A : Amb X) (a b : ℕ) (SS : Finset (HeightOneSpectrum (𝓞 X.E))) (N : Submodule (𝓞 X.E) (Formalism.L2.Col.Sp X.E a))
    (N' : Submodule (𝓞 X.E) (Formalism.L2.Col.Sp X.E b)) (c : ℕ) (x : Formalism.L2.Col.HomE X.E a b) (S0 : Finset ℕ), 0 < volC A.AA SS N N' →
    LatInt (HV A.sc) (Real.sqrt A.d / 2) (LamC (X.embC A.σ₀) A.δ A.AA N N') →
    relIdx (BC (X.embC A.σ₀) A.δ A.AA SS N N' c) (LamC (X.embC A.σ₀) A.δ A.AA N N' ⊓ AC (X.embC A.σ₀) A.δ A.AA SS N N' c) ≠ 0 →
    relIdx (LamC (X.embC A.σ₀) A.δ A.AA N N') (BC (X.embC A.σ₀) A.δ A.AA SS N N' c) ≠ 0 → SNum S0 c →
    TorS (LamC (X.embC A.σ₀) A.δ A.AA N N') S0 (embH (X.embC A.σ₀) A.δ (A.liftW SS N N' c x)) →
      IsKerG (HV A.sc) (LamC (X.embC A.σ₀) A.δ A.AA N N') S0 (A.e a b N N') (A.thInd SS N N' c x)

def Base.AlgT {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) : Prop :=
  ∀ N N' L L', TaylorLogMetric.admitted D N N' L L' → ∀ t : TaylorLogMetric.VC D N N', (∃ a : ℕ, 0 < a ∧ a • t ∈ TaylorLogMetric.La D B.tor L L') →
    ∀ α, TaylorLogMetric.taylor D (TaylorLogMetric.U D B.tor t (B.eNat χ N N' L L')) α ∈ TaylorLogMetric.Qbar

def TransAlgENat : Prop :=
  ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ), TaylorLogMetric.IsCurveIdeal D cc → TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ → δ ≠ 0 →
    B.StdOK → B.AlgT χ → TransAlg D B.tor (B.eNat χ)

def ChiCancel : Prop :=
  ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC)
    (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex) u μ (i : ℕ) (c : (D.chTw u μ).cls i) (c' : (D.chTw u μ).cls (i + 1)),
    ((GL3Theta.rhoOf D (t.O u μ).mt i ((t.O u μ).dt i c) : ℂˣ) : ℂ) * ((GL3Theta.rhoOf' D (t.O u μ).mt i ((t.O u μ).dt (i + 1) c') : ℂˣ) : ℂ) *
        Base.chiFac t.χ (D.R.N i) (D.R.N (i + 1)) ((t.O u μ).lat i c).1 ((t.O u μ).lat (i + 1) c').1 =
      ((((t.O u μ).mt (i + 1) ((t.O u μ).dt i c))⁻¹ * (t.O u μ).mt (i + 1) ((t.O u μ).dt (i + 1) c') : ℂˣ) : ℂ)

def KfAllTied : Prop :=
  ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC)
    (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex) (cc' : Ideal (𝓞 D.host.K)) (δ' : ℂ) (e' : TaylorLogMetric.FamE D) (Q : GL3Columns.DtAd D),
    GL3Columns.aux₃ D cc' δ' e' Q → GL3Theta.rhoUse D → (∀ u μ, GL3Theta.rhoThreeOf D (D.chTw u μ) (t.O u μ).mt) → (∀ u μ, GL3Columns.RhoAlg (t.O u μ)) →
    t.Hyp → t.UnfAll → TransAlg D t.B.tor (t.B.eNat t.χ) → GL3Columns.kfAll t.ent t.O

def IdxOfFG : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (ι : Type) [Fintype ι] (a b : ℕ) (emb : ι → E →+* ℂ) (δ : ℂ)
    (AA0 : Submodule (𝓞 E) E) (SS : Finset (HeightOneSpectrum (𝓞 E)))
    (N : Submodule (𝓞 E) (Formalism.L2.Col.Sp E a)) (N' : Submodule (𝓞 E) (Formalism.L2.Col.Sp E b)) (c : ℕ), 0 < c → (LamC emb δ AA0 N N').FG →
    relIdx (LamC emb δ AA0 N N') (AC emb δ AA0 SS N N' c) ≠ 0 ∧
    relIdx (BC emb δ AA0 SS N N' c) (LamC emb δ AA0 N N' ⊓ AC emb δ AA0 SS N N' c) ≠ 0 ∧
    relIdx (LamC emb δ AA0 N N') (BC emb δ AA0 SS N N' c) ≠ 0

def LamFG : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (ι : Type) [Fintype ι] (a b : ℕ) (emb : ι → E →+* ℂ) (δ : ℂ)
    (AA0 : Submodule (𝓞 E) E) (N : Submodule (𝓞 E) (Formalism.L2.Col.Sp E a)) (N' : Submodule (𝓞 E) (Formalism.L2.Col.Sp E b)),
    N'.FG → Submodule.span E (N : Set (Formalism.L2.Col.Sp E a)) = ⊤ → AA0.FG → (LamC emb δ AA0 N N').FG

end Formalism.L2.Ker
