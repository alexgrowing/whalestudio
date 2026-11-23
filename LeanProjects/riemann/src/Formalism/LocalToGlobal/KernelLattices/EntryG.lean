import Formalism.LocalToGlobal.ExponentGrids.EntryG
import Formalism.LocalToGlobal.KernelLattices.ColInst

noncomputable section
open scoped BigOperators ComplexConjugate
open NumberField IsDedekindDomain MvPolynomial

namespace Formalism.L2.Ker

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Th1.H
open Formalism.L2.AlgTh (KerStd SplitS)
open Formalism.DivisionValues (vw)

section Cf

variable {K : Type} [Field K] {ι : Type} [Fintype ι] {a b : ℕ}

open Classical in

def oneAt (m : DVar ι a b →₀ ℕ) : (DVar ι a b →₀ ℕ) → K := fun m' => if m' = m then 1 else 0

def jetCf (lam : ι → DomWeight a) (lam' : ι → DomWeight b) (n : ι → ℕ) (ℓ : Module.Dual K (DIV.VV K lam')) (P : DIV.VV K lam)
    (m : DVar ι a b →₀ ℕ) : K :=
  ℓ (jetOp lam lam' (oneAt m) n P)

open Classical in

def jetSupp (b : ℕ) (n : ι → ℕ) (P : Pol K ι a) : Finset (DVar ι a b →₀ ℕ) :=
  (subD K ι a b (P * ∏ τ, frDet K a τ ^ n τ)).support.image fun μ => μ.comapDomain Sum.inr Sum.inr_injective.injOn

end Cf

def LevAtG (p cA cB c₀ cA' : ℕ) : Prop :=
  0 < cA ∧ 0 < cB ∧ (∃ k, cB = p * c₀ * k) ∧ cA' ∣ cA ∧ ¬ p ∣ c₀ ∧ ¬ p ∣ cA'

section AtG

variable {X : Fields} (A : Amb X) {p : ℕ} [Fact p.Prime] {a b : ℕ}

def XiAtG (ι : ℂ ≃+* ℂ_[p]) (S : Finset (HeightOneSpectrum (𝓞 X.E))) (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b))
    (c₀ cA' : ℕ) (e : ℝ) (Ξ : HomE X.E a b → X.K) : Prop :=
  (∀ x y, y ∈ mulLat (p * c₀) (homAt S N N') → Ξ (x + y) = Ξ x) ∧
  (∀ x, x ∉ divLat cA' (homAt S N N') → Ξ x = 0) ∧
  ∀ x, ‖ι (A.σ₀ (Ξ x))‖ ≤ ‖(p : ℂ_[p])‖ ^ e

def JetCfInt (ι : ℂ ≃+* ℂ_[p]) (lam : X.Tau → DomWeight a) (lam' : X.Tau → DomWeight b) (n : X.Tau → ℕ)
    (ℓ : Module.Dual X.K (DIV.VV X.K lam')) (P : DIV.VV X.K lam) : Prop :=
  ∀ m, ‖ι (A.σ₀ (jetCf lam lam' n ℓ P m))‖ ≤ 1

def StepAtG (a₀ : ℕ) (b₀ c₀' : ℤ) (ha : 0 < a₀) (hd : 0 < A.d) (lam₀ : ℂ) (hlam : lam₀ ≠ 0) (ι : ℂ ≃+* ℂ_[p]) (ϖ : ℂ) (pE : 𝓞 X.E)
    (S : Finset (HeightOneSpectrum (𝓞 X.E))) (D : ℕ) (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) : Prop :=
  IsSdLat N ∧ IsSdLat N' ∧ KerStd A N N' a₀ b₀ c₀' ha hd lam₀ hlam p ι ∧ A.LaHyp a b S ∧ SplitS A S p ϖ pE ∧ A.JetAdd a b S D

end AtG

section Lat

variable {K : Type} [Field K] [NumberField K] [StarRing K] {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V]

def LatIntAt (w : HeightOneSpectrum (𝓞 K)) (Λ : Submodule (𝓞 K) V) (v : V) : Prop := ∃ s : 𝓞 K, s ∉ w.asIdeal ∧ (s : K) • v ∈ Λ

def NabInDelAt (w : HeightOneSpectrum (𝓞 K)) (Nab Del : Submodule (𝓞 K) V) : Prop := ∀ v ∈ Nab, LatIntAt w Del v

def CoordIntAt (w : HeightOneSpectrum (𝓞 K)) (Λ : Submodule (𝓞 K) V) (ℓ : Module.Dual K V) : Prop :=
  ∀ v ∈ Λ, ℓ v = 0 ∨ 0 ≤ vw w (ℓ v)

end Lat

def JetDelNab {X : Fields} {a b : ℕ} (w : HeightOneSpectrum (𝓞 X.K)) (lam : X.Tau → DomWeight a) (lam' : X.Tau → DomWeight b) (n : X.Tau → ℕ)
    (Λ : Submodule (𝓞 X.K) (DIV.VV X.K lam)) (Λ' : Submodule (𝓞 X.K) (DIV.VV X.K lam')) : Prop :=
  ∀ m, ∀ P ∈ Λ, LatIntAt w Λ' (jetOp lam lam' (oneAt m) n P)

section AtRec

open Formalism.DivisionValues (PlOver)

def StdOver {E : Type} [Field E] [NumberField E] {n : ℕ} (g : ℕ) (Lat : Submodule (𝓞 E) (Sp E n)) : Prop :=
  ∀ P : HeightOneSpectrum (𝓞 E), (g : 𝓞 E) ∈ P.asIdeal → localization₂ P.asIdeal Lat = stdAt E n P

def JetNabG : Prop :=
  ∀ (X : Fields) (a b : ℕ) (lam : X.Tau → DomWeight a) (lam' : X.Tau → DomWeight b) (n : X.Tau → ℕ)
    (Lat : Submodule (𝓞 X.E) (Sp X.E a)) (Lat' : Submodule (𝓞 X.E) (Sp X.E b)) (w : HeightOneSpectrum (𝓞 X.K)) (g : ℕ),
    g.Prime → PlOver g w → JetInVV X.K lam lam' n → Submodule.IsLattice X.E Lat → Submodule.IsLattice X.E Lat' → StdOver g Lat → StdOver g Lat' →
    JetDelNab w lam lam' n (nabAtr X.emb lam Lat) (nabAtr X.emb lam' Lat')

def NabCoordG : Prop :=
  ∀ (X : Fields) (n : ℕ) (lam : X.Tau → DomWeight n) (Lat : Submodule (𝓞 X.E) (Sp X.E n)) (w : HeightOneSpectrum (𝓞 X.K)) (g : ℕ),
    g.Prime → PlOver g w → Submodule.IsLattice X.E Lat → StdOver g Lat →
    (∀ i, LatIntAt w (nabAtr X.emb lam Lat) (bVV X.K lam i)) ∧ ∀ i, CoordIntAt w (nabAtr X.emb lam Lat) ((bVV X.K lam).coord i)

def NabDelG : Prop :=
  ∀ (X : Fields) (n : ℕ) (lam : X.Tau → DomWeight n) (Lat : Submodule (𝓞 X.E) (Sp X.E n)) (w : HeightOneSpectrum (𝓞 X.K)) (g : ℕ),
    g.Prime → PlOver g w → Submodule.IsLattice X.E Lat → (∀ τ i, (lam τ).natW i + n < g) →
    NabInDelAt w (nabAtr X.emb lam Lat) (delAtr X.emb lam Lat)

end AtRec

section Hyp

variable {X : Fields} (A : Amb X) {p : ℕ} [Fact p.Prime] {a b : ℕ}

def VVHomog (K : Type) [Field K] {ι : Type} [Fintype ι] {a : ℕ} (lam : ι → DomWeight a) (d : ℕ) : Prop :=
  ∀ P ∈ DIV.VV K lam, (P : Pol K ι a).IsHomogeneous d

def KerEntryHyp (a₀ : ℕ) (b₀ c₀' : ℤ) (ha : 0 < a₀) (hd : 0 < A.d) (lam₀ : ℂ) (hlam : lam₀ ≠ 0) (ι : ℂ ≃+* ℂ_[p]) (ϖ : ℂ) (pE : 𝓞 X.E)
    (D : ℕ) (e : ℝ) (S SB : Finset (HeightOneSpectrum (𝓞 X.E))) (cA cB : ℕ)
    (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (mU : HeightOneSpectrum (𝓞 X.E) → X.Kˣ) (mI : SB → X.E → X.K)
    (lam : X.Tau → DomWeight a) (lam' : X.Tau → DomWeight b) (n : X.Tau → ℕ)
    (N : Submodule (𝓞 X.E) (Sp X.E a)) (fr : Frs X.E a SB) (N' : Submodule (𝓞 X.E) (Sp X.E b)) (fr' : Frs X.E b SB)
    (Ξ : HomE X.E a b → X.K) (ℓ : Module.Dual X.K (DIV.VV X.K lam')) (P : DIV.VV X.K lam) : Prop :=
  ∃ c₀ cA' : ℕ, LevAtG p cA cB c₀ cA' ∧ StepAtG A a₀ b₀ c₀' ha hd lam₀ hlam ι ϖ pE S (cA * cB) N N' ∧ XiAtG A ι S N N' c₀ cA' e Ξ ∧
    ‖ι (A.σ₀ (muInvDet sel SB mU mI N fr * (muInvDet sel SB mU mI N' fr')⁻¹))‖ ≤ 1 ∧ JetCfInt A ι lam lam' n ℓ P ∧
    ∀ m ∈ jetSupp b n (P : Pol X.K X.Tau a), m.degree = D

end Hyp

section Rec

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {Sg : Set ℕ}
  (mu : Tup X.F X.E X.K Sg) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K)))
  (A : Amb X) {p : ℕ} [Fact p.Prime]

def StepEntryHyp (a₀ : ℕ) (b₀ c₀' : ℤ) (ha : 0 < a₀) (hd : 0 < A.d) (lam₀ : ℂ) (hlam : lam₀ ≠ 0) (ι : ℂ ≃+* ℂ_[p]) (ϖ : ℂ) (pE : 𝓞 X.E)
    (D : ℕ) (e : ℝ) (u : Pr.Word) (i : ℕ) {b : ℕ} (lam' : X.Tau → DomWeight b)
    (N : Submodule (𝓞 X.E) (Sp X.E (R.N i))) (fr : Frs X.E (R.N i) (rowSG Pr sel mu)) (N' : Submodule (𝓞 X.E) (Sp X.E b))
    (fr' : Frs X.E b (rowSG Pr sel mu)) (Ξ : HomE X.E (R.N i) b → X.K) (ℓ : Module.Dual X.K (DIV.VV X.K lam'))
    (P : DIV.VV X.K (W.lamTrue u i)) : Prop :=
  KerEntryHyp A a₀ b₀ c₀' ha hd lam₀ hlam ι ϖ pE D e (Sall sel mu u) (rowSG Pr sel mu) (cAof sel mu cst) (cBof sel mu cst u) sel (mUof Ch mu i)
    (muAt Ch sel mu cst i) (W.lamTrue u i) lam' (nuLast W u i) N fr N' fr' Ξ ℓ P

end Rec

section Paths

open Module NumberField IsDedekindDomain

open Formalism.L2.Col Formalism.L2.DIV

section Generic

variable {K : Type} [Field K] [NumberField K] [StarRing K]

variable (Q : KerChain K)

def Nd (j : ℕ) : Type := (Q.F j).Cl × (Q.F j).ιV

instance (j : ℕ) : Fintype (Nd Q j) :=
  letI := (Q.hF j).fintypeCl
  inferInstanceAs (Fintype ((Q.F j).Cl × (Q.F j).ιV))

def famRep (j : ℕ) (c : (Q.F j).Cl) : (Q.F j).D c.1 := ((Q.F j).mem c.1).outSec.rep c.2

def famWt (j : ℕ) (c : (Q.F j).Cl) : ℕ := (((Q.F j).mem c.1).toCSDOf (Q.hF j c.1) ((Q.F j).mem c.1).outSec).wt c.2

structure ChBas where

  B : ∀ j (c : (Q.F j).Cl), Basis (Q.F j).ιV K (Q.F j).V

  BS : Q.S.Cl → Basis Q.S.ιV K Q.S.V

variable {Q} (Bb : ChBas Q)

def crd (j : ℕ) (ν : Nd Q j) : (Q.F j).Forms →ₗ[K] K :=
  (Bb.B j ν.1).coord ν.2 ∘ₗ (LinearMap.proj (famRep Q j ν.1)) ∘ₗ ((Q.F j).mem ν.1.1).EqFun.subtype ∘ₗ LinearMap.proj ν.1.1

def entM (j : ℕ) (ν : Nd Q j) (ν' : Nd Q (j + 1)) : K :=
  (Bb.B (j + 1) ν'.1).coord ν'.2 ((Q.kk j ν.1.1 ν'.1.1).k (famRep Q j ν.1) (famRep Q (j + 1) ν'.1) (Bb.B j ν.1 ν.2))

variable (Q) in

def PthTo : ∀ j : ℕ, Nd Q j → Type
  | 0, _ => Unit
  | j + 1, _ => Σ ν : Nd Q j, PthTo j ν

instance PthTo.fintype : ∀ (j : ℕ) (ν : Nd Q j), Fintype (PthTo Q j ν)
  | 0, _ => inferInstanceAs (Fintype Unit)
  | j + 1, _ =>
    letI := fun ν => PthTo.fintype j ν
    inferInstanceAs (Fintype (Σ ν : Nd Q j, PthTo Q j ν))

def PthTo.first : ∀ (j : ℕ) (ν : Nd Q j), PthTo Q j ν → Nd Q 0
  | 0, ν, _ => ν
  | j + 1, _, ⟨ν, p⟩ => PthTo.first j ν p

def PthTo.gam : ∀ (j : ℕ) (ν : Nd Q j), PthTo Q j ν → ℕ → ℕ
  | 0, _, _ => fun _ => 1
  | j + 1, _, ⟨ν, p⟩ => Function.update (PthTo.gam j ν p) j (famWt Q j ν.1)

def PthTo.ent : ∀ (j : ℕ) (ν : Nd Q j), PthTo Q j ν → ℕ → K
  | 0, _, _ => fun _ => 1
  | j + 1, ν', ⟨ν, p⟩ => Function.update (PthTo.ent j ν p) j (entM Bb j ν ν')

variable (Q) in

def MidNd : Type := Σ c : Q.S.Cl, {y // y ∈ (Q.Y.fin (Q.S.outSec.rep c)).toFinset} × Q.S.ιV

instance : Fintype (MidNd Q) :=
  letI := Q.hS.fintypeCl
  inferInstanceAs (Fintype (Σ c : Q.S.Cl, {y // y ∈ (Q.Y.fin (Q.S.outSec.rep c)).toFinset} × Q.S.ιV))

def midWt (μ : MidNd Q) : ℕ := (Q.S.toCSDOf Q.hS Q.S.outSec).wt μ.1

def ent1 (ν : Nd Q Q.n) (μ : MidNd Q) : K :=
  (Bb.BS μ.1).coord μ.2.2 ((Q.cp ν.1.1).k1 (famRep Q Q.n ν.1) (Q.S.outSec.rep μ.1) μ.2.1.1 (Bb.B Q.n ν.1 ν.2))

def ent2 (b : (Q.F Q.n).β) (μ : MidNd Q) (d₁ : Q.S₁.D) (ℓ : Q.S₁.V →ₗ[K] K) : K :=
  ℓ ((Q.cp b).k2 (Q.S.outSec.rep μ.1) μ.2.1.1 d₁ (Bb.BS μ.1 μ.2.2))

structure LastDat (S₁ : GSD K) (Bsp : Type) [AddCommGroup Bsp] [Module K Bsp] where

  Cl : Type
  [finCl : Fintype Cl]

  pt : Cl → S₁.D

  wt : Cl → ℕ

  V₂ : Type
  [addV : AddCommGroup V₂]
  [modV : Module K V₂]

  ι₂ : Type
  [finι : Fintype ι₂]

  β : S₁.V →ₗ[K] V₂ →ₗ[K] K

  ev : Cl → Bsp →ₗ[K] V₂

  B1 : Cl → Basis S₁.ιV K S₁.V

  B2 : Cl → Basis ι₂ K V₂

attribute [instance] LastDat.finCl LastDat.addV LastDat.modV LastDat.finι

variable {Bsp : Type} [AddCommGroup Bsp] [Module K Bsp]

def LastDat.Is {S₁ : GSD K} (T : LastDat S₁ Bsp) (Λ : S₁.EqFun →ₗ[K] Module.Dual K Bsp) : Prop :=
  ∀ (ψ : S₁.EqFun) (F : Bsp), Λ ψ F = ∑ c : T.Cl, ((T.wt c : K))⁻¹ * T.β ((ψ : S₁.D → S₁.V) (T.pt c)) (T.ev c F)

variable (T : LastDat Q.S₁ Bsp)

variable (Q) in

abbrev ChPath (T : LastDat Q.S₁ Bsp) : Type := (T.Cl × Q.S₁.ιV × T.ι₂) × MidNd Q × (Σ ν : Nd Q Q.n, PthTo Q Q.n ν)

def ChPath.gamN (π : ChPath Q T) : ℕ → ℕ :=
  Function.update (Function.update (PthTo.gam Q.n π.2.2.1 π.2.2.2) Q.n (famWt Q Q.n π.2.2.1.1)) (Q.n + 1) (midWt π.2.1)

def ChPath.entN (π : ChPath Q T) : ℕ → K :=
  Function.update (Function.update (PthTo.ent Bb Q.n π.2.2.1 π.2.2.2) Q.n (ent1 Bb π.2.2.1 π.2.1)) (Q.n + 1)
    (ent2 Bb π.2.2.1.1.1 π.2.1 (T.pt π.1.1) ((T.B1 π.1.1).coord π.1.2.1))

variable {l : ℕ} [Fact l.Prime] {J : Type} [Fintype J] {Asp : Type} [AddCommGroup Asp] [Module K Asp]

def chainPaths (ι' : K →+* ℂ_[l]) (eJ : J ≃ Fin (Q.n + 2)) (f : Asp →ₗ[K] (Q.F 0).Forms) : PathData K l J Asp Bsp where
  Pi := ChPath Q T
  fPi := inferInstance
  x π := crd Bb 0 (PthTo.first Q.n π.2.2.1 π.2.2.2) ∘ₗ f
  y π := (T.B2 π.1.1).coord π.1.2.2 ∘ₗ T.ev π.1.1
  r π := ι' (T.β (T.B1 π.1.1 π.1.2.1) (T.B2 π.1.1 π.1.2.2))
  gam π j := if (eJ j : ℕ) = 0 then 1 else ChPath.gamN T π (eJ j)
  gamP π := T.wt π.1.1
  eps π j := if (eJ j : ℕ) = 0 then ((ChPath.gamN T π 0 : ℕ) : ℂ_[l])⁻¹ else 1
  e π j := ι' (ChPath.entN Bb T π (eJ j))

def FirstInt (w : HeightOneSpectrum (𝓞 K)) (f : Asp →ₗ[K] (Q.F 0).Forms) (NA : Set Asp) : Prop :=
  ∀ ν : Nd Q 0, ∀ φ ∈ NA, crd Bb 0 ν (f φ) = 0 ∨ 0 ≤ Formalism.DivisionValues.vw w (crd Bb 0 ν (f φ))

def RowInt (w : HeightOneSpectrum (𝓞 K)) (NB : Set Bsp) : Prop :=
  ∀ c k, ∀ F ∈ NB, (T.B2 c).coord k (T.ev c F) = 0 ∨ 0 ≤ Formalism.DivisionValues.vw w ((T.B2 c).coord k (T.ev c F))

def LastMapInt (ι' : K →+* ℂ_[l]) : Prop := ∀ c i k, ‖ι' (T.β (T.B1 c i) (T.B2 c k))‖ ≤ 1

def StabOk (D : ℕ) : Prop :=
  D ≠ 0 ∧ (∀ j, j ≤ Q.n → ∀ c, famWt Q j c ∣ D) ∧ (∀ μ : MidNd Q, midWt μ ∣ D) ∧ ∀ c, T.wt c ∣ D

def EntAll (eJ : J ≃ Fin (Q.n + 2)) (Pm : J → K → Prop) : Prop :=
  ∀ j : J, ((eJ j : ℕ) < Q.n → ∀ ν ν', Pm j (entM Bb (eJ j) ν ν')) ∧ ((eJ j : ℕ) = Q.n → ∀ ν μ, Pm j (ent1 Bb ν μ)) ∧
    ((eJ j : ℕ) = Q.n + 1 → ∀ b μ c i₁, Pm j (ent2 Bb b μ (T.pt c) ((T.B1 c).coord i₁)))

end Generic

section Transport

variable {K : Type} [Field K] [NumberField K] [StarRing K]

def rhoEq (S : GSD K) (γ : S.G) : S.V ≃ₗ[K] S.V :=
  LinearEquiv.ofLinear (S.ρ γ) (S.ρ γ⁻¹)
    (by
      ext v
      have h := LinearMap.congr_fun (map_mul S.ρ γ γ⁻¹).symm v
      rw [mul_inv_cancel, map_one] at h
      exact h)
    (by
      ext v
      have h := LinearMap.congr_fun (map_mul S.ρ γ⁻¹ γ).symm v
      rw [inv_mul_cancel, map_one] at h
      exact h)

def mvTo (S : GSD K) (s : S.Sec) (c : S.Cl) : S.G :=
  Classical.choose ((S.cls_eq_iff (S.outSec.rep c) (s.rep c)).mp ((S.outSec.spec c).trans (s.spec c).symm))

structure ChGood (Q : KerChain K) where

  s : ∀ j b, ((Q.F j).mem b).Sec

  sS : Q.S.Sec

  B : ∀ j, (Q.F j).Cl → Basis (Q.F j).ιV K (Q.F j).V

  BS : Q.S.Cl → Basis Q.S.ιV K Q.S.V

variable {Q : KerChain K} (G : ChGood Q)

def ChGood.bas : ChBas Q where
  B j c := (G.B j c).map (rhoEq ((Q.F j).mem c.1) (mvTo ((Q.F j).mem c.1) (G.s j c.1) c.2))
  BS c := (G.BS c).map (rhoEq Q.S (mvTo Q.S G.sS c))

def ChGood.yAt (μ : MidNd Q) : Q.Y.Yb := (mvTo Q.S G.sS μ.1)⁻¹ • μ.2.1.1

variable {Bsp : Type} [AddCommGroup Bsp] [Module K Bsp] {J : Type}

def EntAllAt {Cl₁ : Type} (eJ : J ≃ Fin (Q.n + 2)) (Pm : J → K → Prop) (ptg : Cl₁ → Q.S₁.D) (B1g : Cl₁ → Basis Q.S₁.ιV K Q.S₁.V) : Prop :=
  ∀ j : J,
    ((eJ j : ℕ) < Q.n → ∀ (c : (Q.F (eJ j)).Cl) (c' : (Q.F ((eJ j : ℕ) + 1)).Cl) i i',
      Pm j ((G.B ((eJ j : ℕ) + 1) c').coord i' ((Q.kk (eJ j) c.1 c'.1).k ((G.s (eJ j) c.1).rep c.2) ((G.s ((eJ j : ℕ) + 1) c'.1).rep c'.2) (G.B (eJ j) c i)))) ∧
    ((eJ j : ℕ) = Q.n → ∀ (c : (Q.F Q.n).Cl) i (c' : Q.S.Cl) (y : Q.Y.Yb), y ∈ Q.Y.ys (G.sS.rep c') → ∀ i',
      Pm j ((G.BS c').coord i' ((Q.cp c.1).k1 ((G.s Q.n c.1).rep c.2) (G.sS.rep c') y (G.B Q.n c i)))) ∧
    ((eJ j : ℕ) = Q.n + 1 → ∀ (b : (Q.F Q.n).β) (c' : Q.S.Cl) (y : Q.Y.Yb), y ∈ Q.Y.ys (G.sS.rep c') → ∀ i' c₁ i₁,
      Pm j ((B1g c₁).coord i₁ ((Q.cp b).k2 (G.sS.rep c') y (ptg c₁) (G.BS c' i'))))

def FirstIntAt {Asp : Type} [AddCommGroup Asp] [Module K Asp] (w : HeightOneSpectrum (𝓞 K)) (f : Asp →ₗ[K] (Q.F 0).Forms) (NA : Set Asp) : Prop :=
  ∀ (c : (Q.F 0).Cl) (i : (Q.F 0).ιV), ∀ φ ∈ NA,
    (G.B 0 c).coord i ((f φ c.1 : (Q.F 0).D c.1 → (Q.F 0).V) ((G.s 0 c.1).rep c.2)) = 0 ∨
      0 ≤ Formalism.DivisionValues.vw w ((G.B 0 c).coord i ((f φ c.1 : (Q.F 0).D c.1 → (Q.F 0).V) ((G.s 0 c.1).rep c.2)))

end Transport

section Place

open Formalism.L2.Indef Formalism.L2.AtG.EntryG Formalism.L2.AlgTh

variable {X : Fields}

end Place

section Record

open Formalism.BasicNotions Formalism.L2.Indef Formalism.L2.AtG.EntryG Formalism.L2.AlgTh

variable {X : Fields} {Pr : Primes X} {Rk : Ranks} {W : Wts X Pr.Word Rk} {Ch : Chars X Pr Rk.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {Sg : Set ℕ}

def lastRec {mu : Tup X.F X.E X.K Sg} {P : LevFam X.E X.K Rk.r Pr.vGs} (hP : (mtildeGSD W Ch sel mu P).Ok) (Xg : Finset (G0 X.E Pr.vGs Rk.r → X.K))
    (u : Pr.Word) {n : ℕ} (ev : (Fin n → X.K) →ₗ[X.K] V0X W Ch sel mu Xg P)
    (B1 : (mtildeGSD W Ch sel mu P).Cl → Basis (evGSD W Ch sel mu P u).ιV X.K (evGSD W Ch sel mu P u).V)
    (B2 : (mtildeGSD W Ch sel mu P).Cl → Basis (VVIdx W.sgTrue) X.K (DIV.VV X.K W.sgTrue)) :
    LastDat (evGSD W Ch sel mu P u) (Fin n → X.K) where
  Cl := (mtildeGSD W Ch sel mu P).Cl
  finCl := hP.fintypeCl
  pt c := (mtildeGSD W Ch sel mu P).outSec.rep c
  wt c := ((mtildeGSD W Ch sel mu P).toCSDOf hP (mtildeGSD W Ch sel mu P).outSec).wt c
  V₂ := DIV.VV X.K W.sgTrue
  ι₂ := VVIdx W.sgTrue
  β := (pairBK (K := X.K) W.sgTrue) ∘ₗ brC W u
  ev c := LinearMap.proj ((mtildeGSD W Ch sel mu P).outSec.rep c) ∘ₗ (mtildeKGSD W Ch sel mu).EqFun.subtype ∘ₗ
    (V0X W Ch sel mu Xg P).subtype ∘ₗ ev
  B1 := B1
  B2 := B2

abbrev recQ {mu : Tup X.F X.E X.K Sg} {cst : LocCst X (rowSG Pr sel mu)} {L : ChIdx X Pr Rk (QE sel (mu : Chr X.F X.E X.K))}
    {P : LevFam X.E X.K Rk.r Pr.vGs} {u : Pr.Word} {m2 : ℕ} {b : L.β (m2 + 1)} {hY : YbHyp (R := Rk) sel mu cst L u m2 b} (Am : Amb X)
    (hK : KerEquivC W Ch sel mu cst L Am u m2 b hY P) (hF : ∀ j, (chF W sel mu L u j).Ok) (hE : (evGSD W Ch sel mu P u).Ok) : KerChain X.K :=
  KerChain.ofCol W Ch sel mu cst L (chKerC W Ch sel mu cst L Am u m2 b hY P hK) hF hE

section Entries

variable {mu : Tup X.F X.E X.K Sg} {cst : LocCst X (rowSG Pr sel mu)} {L : ChIdx X Pr Rk (QE sel (mu : Chr X.F X.E X.K))}
  {P : LevFam X.E X.K Rk.r Pr.vGs} {u : Pr.Word} {m2 : ℕ} {b : L.β (m2 + 1)} {hY : YbHyp (R := Rk) sel mu cst L u m2 b} {Am : Amb X}
  {hK : KerEquivC W Ch sel mu cst L Am u m2 b hY P} {hF : ∀ j, (chF W sel mu L u j).Ok} {hE : (evGSD W Ch sel mu P u).Ok}
  (Bb : ChBas (recQ Am hK hF hE))

end Entries

section Steps

variable {mu : Tup X.F X.E X.K Sg} {cst : LocCst X (rowSG Pr sel mu)} {L : ChIdx X Pr Rk (QE sel (mu : Chr X.F X.E X.K))}
  {P : LevFam X.E X.K Rk.r Pr.vGs} {u : Pr.Word} {m2 : ℕ} {b : L.β (m2 + 1)} {hY : YbHyp (R := Rk) sel mu cst L u m2 b} {Am : Amb X}
  {hK : KerEquivC W Ch sel mu cst L Am u m2 b hY P} {hF : ∀ j, (chF W sel mu L u j).Ok} {hE : (evGSD W Ch sel mu P u).Ok}
  {g : ℕ} [Fact g.Prime] {J : Type}

def StepsAtG (G : ChGood (recQ Am hK hF hE)) {Cl₁ : Type} (ptg : Cl₁ → RowPt Pr Rk sel mu)
    (B1g : Cl₁ → Basis (evGSD W Ch sel mu P u).ιV X.K (evGSD W Ch sel mu P u).V) (eJ : J ≃ Fin (m2 + 2))
    (a₀ : ℕ) (b₀ c₀ : ℤ) (ha : 0 < a₀) (hd : 0 < Am.d) (lam : ℂ) (hlam : lam ≠ 0) (ι : ℂ ≃+* ℂ_[g]) (ϖ : ℂ) (pE : 𝓞 X.E)
    (Dg : J → ℕ) (e : J → ℝ) : Prop :=
  ∀ j : J,
    ((eJ j : ℕ) < m2 → ∀ (c : (chF W sel mu L u (eJ j)).Cl) (c' : (chF W sel mu L u ((eJ j : ℕ) + 1)).Cl) i i',
      StepEntryHyp W Ch sel mu cst Am a₀ b₀ c₀ ha hd lam hlam ι ϖ pE (Dg j) (e j) u (eJ j) (W.lamTrue u ((eJ j : ℕ) + 1))
        ((G.s (eJ j) c.1).rep c.2 : ChPt (R := Rk) sel mu u (eJ j)).deco.1.N (frsF sel mu ((G.s (eJ j) c.1).rep c.2 : ChPt (R := Rk) sel mu u (eJ j)))
        ((G.s ((eJ j : ℕ) + 1) c'.1).rep c'.2 : ChPt (R := Rk) sel mu u ((eJ j : ℕ) + 1)).deco.1.N
        (frsF sel mu ((G.s ((eJ j : ℕ) + 1) c'.1).rep c'.2 : ChPt (R := Rk) sel mu u ((eJ j : ℕ) + 1)))
        (XiEntry Ch sel mu cst L (eJ j) c.1 c'.1 ((G.s (eJ j) c.1).rep c.2) ((G.s ((eJ j : ℕ) + 1) c'.1).rep c'.2))
        ((G.B ((eJ j : ℕ) + 1) c').coord i') (G.B (eJ j) c i)) ∧
    ((eJ j : ℕ) = m2 → ∀ (c : (chF W sel mu L u m2).Cl) i (c' : (midGSD W sel mu L u m2 b).Cl) (Y : Set (Sp X.E (Rk.N (m2 + 1)))),
      Y ∈ ybSet sel mu cst (G.sS.rep c' : ChPt (R := Rk) sel mu u (m2 + 1)).deco.1.N → ∀ i',
      StepEntryHyp W Ch sel mu cst Am a₀ b₀ c₀ ha hd lam hlam ι ϖ pE (Dg j) (e j) u m2 (W.lamTrue u (m2 + 1))
        ((G.s m2 c.1).rep c.2 : ChPt (R := Rk) sel mu u m2).deco.1.N (frsF sel mu ((G.s m2 c.1).rep c.2 : ChPt (R := Rk) sel mu u m2))
        (G.sS.rep c' : ChPt (R := Rk) sel mu u (m2 + 1)).deco.1.N (frsF sel mu (G.sS.rep c' : ChPt (R := Rk) sel mu u (m2 + 1)))
        (XiCpl1 Ch sel mu cst L m2 c.1 ((G.s m2 c.1).rep c.2) (G.sS.rep c') Y) ((G.BS c').coord i') (G.B m2 c i)) ∧
    ((eJ j : ℕ) = m2 + 1 → ∀ (c' : (midGSD W sel mu L u m2 b).Cl) (Y : Set (Sp X.E (Rk.N (m2 + 1)))),
      Y ∈ ybSet sel mu cst (G.sS.rep c' : ChPt (R := Rk) sel mu u (m2 + 1)).deco.1.N → ∀ i' c₁ i₁,
      StepEntryHyp W Ch sel mu cst Am a₀ b₀ c₀ ha hd lam hlam ι ϖ pE (Dg j) (e j) u (m2 + 1) (W.lamTrue u Rk.m)
        (G.sS.rep c' : ChPt (R := Rk) sel mu u (m2 + 1)).deco.1.N (frsF sel mu (G.sS.rep c' : ChPt (R := Rk) sel mu u (m2 + 1)))
        (tilQ sel mu u (ptg c₁)).1.N (frsT sel mu u (ptg c₁)) (XiCpl2 Ch sel mu cst m2 (G.sS.rep c') Y (ptg c₁))
        ((B1g c₁).coord i₁) (G.BS c' i'))

def RanksAre (Rk : Ranks) (m2 : ℕ) (eJ : J ≃ Fin (m2 + 2)) (ab : J → ℕ × ℕ) : Prop :=
  ∀ j : J, ((eJ j : ℕ) < m2 → ab j = (Rk.N (eJ j), Rk.N ((eJ j : ℕ) + 1))) ∧ ((eJ j : ℕ) = m2 → ab j = (Rk.N m2, Rk.N (m2 + 1))) ∧
    ((eJ j : ℕ) = m2 + 1 → ab j = (Rk.N (m2 + 1), Rk.N Rk.m))

end Steps

end Record

end Paths

end Formalism.L2.Ker
