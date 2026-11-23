import Mathlib
import Formalism.LocalToGlobal.KernelLattices.JetFieldLeKR
import Formalism.LocalToGlobal.KernelLattices.ColInst

open NumberField IsDedekindDomain

noncomputable section

namespace Formalism.L2.Ker

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Th1.H Formalism.MainNotions

def opDeg {ι : Type} {a : ℕ} (lam : ι → DomWeight a) (n : ι → ℕ) (τ : ι) : ℕ := ∑ r, ((lam τ).natW r + n τ)

def stepDeg {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (u : Pr.Word) (i : ℕ) : X.Tau → ℕ := opDeg (W.lamTrue u i) (nuLast W u i)

def StepDegIs : Prop :=
  ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (W : Wts X Pr.Word R) (u : Pr.Word) (i : ℕ), i < R.m → ∀ τ : X.Tau,
    ((stepDeg W u i τ : ℕ) : ℤ) = ∑ r, (W.nuW u (i + 1) τ).w r

section Deg

variable {X : Fields} (A : Amb X) (a b : ℕ) (Sall : Finset (HeightOneSpectrum (𝓞 X.E))) (D : ℕ) (dg : X.Tau → ℕ)

def Amb.JetAddDeg : Prop :=
  ∀ (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) (c c' : ℕ) (x : HomE X.E a b), 0 < c → 0 < c' →
    InRange Sall D (c * c') N N' x → ∀ m, (∀ τ, degAt m τ = dg τ) → A.jetK Sall N N' c x m =
      latSum (mulLat c (homAt Sall N N')) (mulLat (c * c') (homAt Sall N N')) fun y => A.jetK Sall N N' (c * c') (x + y) m

def Amb.AnaStepD : Prop :=
  A.LaHyp a b Sall ∧ A.ESmooth a b ∧ A.JetsRatDeg a b Sall D dg

end Deg

section Inst

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu))
  (A : Amb X) (u : Pr.Word) (m2 : ℕ)

def ThHypD : Prop :=
  (∀ i, i ≤ m2 → A.AnaStepD (R.N i) (R.N (i + 1)) (Sall sel mu u) (cAof sel mu cst * cBof sel mu cst u) (stepDeg W u i)) ∧
  A.AnaStepD (R.N (m2 + 1)) (R.N R.m) (Sall sel mu u) (cAof sel mu cst * cBof sel mu cst u) (stepDeg W u (m2 + 1)) ∧
  (∀ i, i ≤ m2 → ThEquivP ((chThT W Ch sel mu cst A u m2).th i) (Sall sel mu u) (cAof sel mu cst * cBof sel mu cst u)
      (colValF W sel mu u i).rho (colValF W sel mu u (i + 1)).rho) ∧
  ThEquivP (chThT W Ch sel mu cst A u m2).top (Sall sel mu u) (cAof sel mu cst * cBof sel mu cst u)
      (colValF W sel mu u (m2 + 1)).rho (colVal W u R.m (Pr.vT u) (rowSG Pr sel mu)).rho

end Inst

section InstN

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (G : ChGlob X R.m)
  {D : D7} (s : Seam D X) {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) (u : Pr.Word) (m2 : ℕ)

def ThHypND : Prop :=
  NatOk s cc δ χ cD G.σ₀ ∧ LawTies W Ch sel mu cst G ∧ ThHypD W Ch sel mu cst (ambOf s B χ cD) u m2

end InstN

def ThHypDOf : Prop :=
  ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ)
    (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (A : Amb X) (u : Pr.Word) (m2 : ℕ), ThHyp W Ch sel mu cst A u m2 → ThHypD W Ch sel mu cst A u m2

def ThDistUnfD : Prop :=
  ∀ (X : Formalism.L2.Col.Fields) (A : Amb X) (a b : ℕ) (Sall SB : Finset (HeightOneSpectrum (𝓞 X.E))) (D : ℕ)
    (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (mU : HeightOneSpectrum (𝓞 X.E) → X.Kˣ) (mI : SB → X.E → X.K)
    (lam : X.Tau → DomWeight a) (lam' : X.Tau → DomWeight b) (n : X.Tau → ℕ), JetInVV X.K lam lam' n → A.JetsRatDeg a b Sall D (opDeg lam n) →
    ∀ (Y Y' : Type) (fr : Y → X.Tau → Matrix (Fin a) (Fin a) ℂ) (fr' : Y' → X.Tau → Matrix (Fin b) (Fin b) ℂ),
    Function.Injective (frPolyG fr) → (∀ y τ, (fr y τ).det ≠ 0) → ∀ (sh sS sD : X.Tau → ℤ), (∀ τ, sh τ + sS τ = n τ) →
    ∀ (N : Submodule (𝓞 X.E) (Formalism.L2.Col.Sp X.E a)) (f : Formalism.L2.Col.Frs X.E a SB) (N' : Submodule (𝓞 X.E) (Formalism.L2.Col.Sp X.E b)) (f' : Formalism.L2.Col.Frs X.E b SB)
      (c : ℕ) (x : Formalism.L2.Col.HomE X.E a b), InRange Sall D c N N' x → ∀ P : DIV.VV X.K lam,
      evG fr' (fun τ => -sD τ) A.σ₀ ((thDistC A Sall SB D sel mU mI lam lam' n N f N' f' c x P : DIV.VV X.K lam') : DIV.Pol X.K X.Tau b) =
        (A.σ₀ (muInvDet sel SB mU mI N f * (muInvDet sel SB mU mI N' f')⁻¹) * (A.chiF a b N N')⁻¹) •
          mulFun (fun y' => (∏ τ, (fr' y' τ).det ^ sD τ)⁻¹)
            (unfG fr fr' A.cD (A.thInd Sall N N' c x) (mulFun (fun y => ∏ τ, (fr y τ).det ^ sS τ) (evG fr sh A.σ₀ (P : DIV.Pol X.K X.Tau a))))

def TabKSpecD : Prop :=
  ∀ (X : Fields) (A : Amb X) (a b : ℕ) (Sall : Finset (HeightOneSpectrum (𝓞 X.E))) (cA cB : ℕ) (dg : X.Tau → ℕ), 0 < cA → 0 < cB → A.ESmooth a b →
    A.JetsRatDeg a b Sall (cA * cB) dg → ∀ (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)), IsSdLat N → IsSdLat N' →
    ∀ (Ξ : HomE X.E a b → X.K) (m : DVar X.Tau a b →₀ ℕ), (∀ τ, degAt m τ = dg τ) →
      A.σ₀ (A.tabK Sall cA cB N N' Ξ m) = (A.chiF a b N N')⁻¹ * jetC A.cD (A.thDat Sall cA cB N N' Ξ) m

section FieldDeg

variable {X : Fields} (A : Amb X) (a b : ℕ) (Sall : Finset (HeightOneSpectrum (𝓞 X.E))) (D : ℕ) (dg : X.Tau → ℕ)

def Amb.jetSetDeg : Set ℂ :=
  {z | ∃ (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) (c : ℕ) (x : HomE X.E a b) (m : DVar X.Tau a b →₀ ℕ),
    InRange Sall D c N N' x ∧ (∀ τ, degAt m τ = dg τ) ∧ z = (A.chiF a b N N')⁻¹ * jetC A.cD (A.thInd Sall N N' c x) m}

def Amb.jetFieldDeg : IntermediateField ℚ ℂ := IntermediateField.adjoin ℚ (A.jetSetDeg a b Sall D dg)

end FieldDeg

def JetsRatDegIff : Prop :=
  ∀ (X : Fields) (A : Amb X) (a b : ℕ) (Sall : Finset (HeightOneSpectrum (𝓞 X.E))) (D : ℕ) (dg : X.Tau → ℕ),
    A.JetsRatDeg a b Sall D dg ↔ ∀ z ∈ A.jetFieldDeg a b Sall D dg, ∃ k : X.K, A.σ₀ k = z

def JetsRatDegWithK : Prop :=
  ∀ (X : Fields) (A : Amb X) (M : IntermediateField ℚ ℂ) [NumberField M] [StarRing M] (hM : ∀ τ x, X.embC A.σ₀ τ x ∈ M)
    (a b : ℕ) (Sall : Finset (HeightOneSpectrum (𝓞 X.E))) (D : ℕ) (dg : X.Tau → ℕ), A.jetFieldDeg a b Sall D dg ≤ M → (A.withK M hM).JetsRatDeg a b Sall D dg

def Amb.descentTableFirst {X : Fields} (A : Amb X) {a b : ℕ} (Sall : Finset (HeightOneSpectrum (𝓞 X.E))) (cA cB : ℕ) (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b))
    (Ξ : HomE X.E a b → X.K) (m : DVar X.Tau a b →₀ ℕ) : X.K :=
  desc A.σ₀ ((A.chiF a b N N')⁻¹ * jetC A.cD (A.thDat Sall cA cB N N' Ξ) m)

def Amb.EntRat {X : Fields} (A : Amb X) {a b : ℕ} (Sall : Finset (HeightOneSpectrum (𝓞 X.E))) (cA cB : ℕ) (dg : X.Tau → ℕ) (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b))
    (Ξ : HomE X.E a b → X.K) : Prop :=
  ∀ m : DVar X.Tau a b →₀ ℕ, (∀ τ, degAt m τ = dg τ) → ∃ k : X.K, A.σ₀ k = (A.chiF a b N N')⁻¹ * jetC A.cD (A.thDat Sall cA cB N N' Ξ) m

def DescentTableSpec : Prop :=
  ∀ (X : Fields) (A : Amb X) (a b : ℕ) (Sall : Finset (HeightOneSpectrum (𝓞 X.E))) (cA cB : ℕ) (dg : X.Tau → ℕ) (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b))
    (Ξ : HomE X.E a b → X.K), A.EntRat Sall cA cB dg N N' Ξ → ∀ m : DVar X.Tau a b →₀ ℕ, (∀ τ, degAt m τ = dg τ) →
      A.σ₀ (A.descentTableFirst Sall cA cB N N' Ξ m) = (A.chiF a b N N')⁻¹ * jetC A.cD (A.thDat Sall cA cB N N' Ξ) m

def DescentTablesAgree : Prop :=
  ∀ (X : Fields) (A : Amb X) (a b : ℕ) (Sall : Finset (HeightOneSpectrum (𝓞 X.E))) (cA cB : ℕ) (dg : X.Tau → ℕ), 0 < cA → 0 < cB → A.ESmooth a b →
    A.JetsRatDeg a b Sall (cA * cB) dg → ∀ (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)), IsSdLat N → IsSdLat N' →
    ∀ (Ξ : HomE X.E a b → X.K), A.EntRat Sall cA cB dg N N' Ξ ∧ ∀ m : DVar X.Tau a b →₀ ℕ, (∀ τ, degAt m τ = dg τ) →
      A.descentTableFirst Sall cA cB N N' Ξ m = A.tabK Sall cA cB N N' Ξ m

section Tied

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {K : G.Consts} {Y : DivX D} {cX : ExtraC}

def KerEntTied.FieldTie {ex : Extra D L hT Gi Gl K Y cX} (t : KerEntTied ex) : Prop :=
  ∀ k : D.what₂.LL, ∃ y : t.X.K, t.seam.σ₀ y = D.what₂.embLL k

def KerEntTied.RKCos {ex : Extra D L hT Gi Gl K Y cX} (t : KerEntTied ex) : Prop :=
  ∀ u μ, Formalism.BasicNotions.DV.Used D μ → ∀ i, i < D.R.m → ∀ (N : Submodule (𝓞 t.X.E) (Sp t.X.E (D.R.N i))) (N' : Submodule (𝓞 t.X.E) (Sp t.X.E (D.R.N (i + 1)))) (c : ℕ)
    (x : HomE t.X.E (D.R.N i) (D.R.N (i + 1))),
    InRange (Sall t.sel (t.tup μ) (t.word u)) (cAof t.sel (t.tup μ) (t.cst μ) * cBof t.sel (t.tup μ) (t.cst μ) (t.word u)) c N N' x →
    ∀ m : DVar t.X.Tau (D.R.N i) (D.R.N (i + 1)) →₀ ℕ, (∀ τ, degAt m τ = ∑ r, nuT D u i (t.seam.iT τ) r) →
    ∃ k : D.what₂.LL, D.what₂.embLL k = (t.amb.chiF _ _ N N')⁻¹ * jetC t.amb.cD (t.amb.thInd (Sall t.sel (t.tup μ) (t.word u)) N N' c x) m

end Tied

def StepsRatDegOfCos : Prop :=
  ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC)
    (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex), t.FieldTie → t.RKCos → ∀ u μ, Formalism.BasicNotions.DV.Used D μ → ∀ i, i < D.R.m →
    t.amb.JetsRatDeg (D.R.N i) (D.R.N (i + 1)) (Sall t.sel (t.tup μ) (t.word u)) (cAof t.sel (t.tup μ) (t.cst μ) * cBof t.sel (t.tup μ) (t.cst μ) (t.word u))
      fun τ => ∑ r, nuT D u i (t.seam.iT τ) r

section Reps

variable {X : Fields} (A : Amb X) (a b : ℕ) (Sall : Finset (HeightOneSpectrum (𝓞 X.E))) (D : ℕ) (dg : X.Tau → ℕ)

def Amb.RatAt (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) : Prop :=
  ∀ (c : ℕ) (x : HomE X.E a b), InRange Sall D c N N' x →
    ∀ m : DVar X.Tau a b →₀ ℕ, (∀ τ, degAt m τ = dg τ) → ∃ k : X.K, A.σ₀ k = (A.chiF a b N N')⁻¹ * jetC A.cD (A.thInd Sall N N' c x) m

def Amb.IndEntire : Prop :=
  ∀ (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) (c : ℕ) (x : HomE X.E a b), InRange Sall D c N N' x →
    ContDiff ℂ ⊤ (A.thInd Sall N N' c x)

end Reps

def IsRepSet {E : Type} [Field E] [NumberField E] [StarRing E] (a b : ℕ) (Rp : Set (Submodule (𝓞 E) (Sp E a) × Submodule (𝓞 E) (Sp E b))) : Prop :=
  ∀ (N : Submodule (𝓞 E) (Sp E a)) (N' : Submodule (𝓞 E) (Sp E b)), IsSdLat N → IsSdLat N' →
    ∃ p ∈ Rp, IsSdLat p.1 ∧ IsSdLat p.2 ∧ ∃ (γ : UF E a) (γ' : UF E b), N = gmap γ.1 p.1 ∧ N' = gmap γ'.1 p.2

def JetsRatDegOfReps : Prop :=
  ∀ (X : Fields) (A : Amb X) (a b : ℕ) (Sall : Finset (HeightOneSpectrum (𝓞 X.E))) (D : ℕ) (dg : X.Tau → ℕ)
    (Rp : Set (Submodule (𝓞 X.E) (Sp X.E a) × Submodule (𝓞 X.E) (Sp X.E b))), IsRepSet a b Rp → A.ThIndEq a b Sall D → A.ChiLaw a b → A.IndEntire a b Sall D →
    (∀ p ∈ Rp, A.RatAt a b Sall D dg p.1 p.2) → A.JetsRatDeg a b Sall D dg

def Amb.EEntire {X : Fields} (A : Amb X) (a b : ℕ) : Prop :=
  ∀ (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)), IsSdLat N → IsSdLat N' → ContDiff ℂ ⊤ (A.e a b N N')

section TiedRep

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {K : G.Consts} {Y : DivX D} {cX : ExtraC}

def KerEntTied.RKCosRep {ex : Extra D L hT Gi Gl K Y cX} (t : KerEntTied ex)
    (Rp : ∀ i, Set (Submodule (𝓞 t.X.E) (Sp t.X.E (D.R.N i)) × Submodule (𝓞 t.X.E) (Sp t.X.E (D.R.N (i + 1))))) : Prop :=
  ∀ u μ, Formalism.BasicNotions.DV.Used D μ → ∀ i, i < D.R.m → ∀ p ∈ Rp i, ∀ (c : ℕ) (x : HomE t.X.E (D.R.N i) (D.R.N (i + 1))),
    InRange (Sall t.sel (t.tup μ) (t.word u)) (cAof t.sel (t.tup μ) (t.cst μ) * cBof t.sel (t.tup μ) (t.cst μ) (t.word u)) c p.1 p.2 x →
    ∀ m : DVar t.X.Tau (D.R.N i) (D.R.N (i + 1)) →₀ ℕ, (∀ τ, degAt m τ = ∑ r, nuT D u i (t.seam.iT τ) r) →
    ∃ k : D.what₂.LL, D.what₂.embLL k = (t.amb.chiF _ _ p.1 p.2)⁻¹ * jetC t.amb.cD (t.amb.thInd (Sall t.sel (t.tup μ) (t.word u)) p.1 p.2 c x) m

end TiedRep

def StepsRatDegOfCosRep : Prop :=
  ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC)
    (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex)
    (Rp : ∀ i, Set (Submodule (𝓞 t.X.E) (Sp t.X.E (D.R.N i)) × Submodule (𝓞 t.X.E) (Sp t.X.E (D.R.N (i + 1))))),
    t.FieldTie → t.RKCosRep Rp → ∀ u μ, Formalism.BasicNotions.DV.Used D μ → ∀ i, i < D.R.m → IsRepSet _ _ (Rp i) →
    t.amb.ThIndEq (D.R.N i) (D.R.N (i + 1)) (Sall t.sel (t.tup μ) (t.word u)) (cAof t.sel (t.tup μ) (t.cst μ) * cBof t.sel (t.tup μ) (t.cst μ) (t.word u)) →
    t.amb.ChiLaw (D.R.N i) (D.R.N (i + 1)) → t.amb.EEntire (D.R.N i) (D.R.N (i + 1)) →
    t.amb.JetsRatDeg (D.R.N i) (D.R.N (i + 1)) (Sall t.sel (t.tup μ) (t.word u)) (cAof t.sel (t.tup μ) (t.cst μ) * cBof t.sel (t.tup μ) (t.cst μ) (t.word u))
      fun τ => ∑ r, nuT D u i (t.seam.iT τ) r

def Amb.kerOne {X : Fields} (A : Amb X) {a b : ℕ} (Sall SB : Finset (HeightOneSpectrum (𝓞 X.E))) (cA cB : ℕ) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E))
    (mU : HeightOneSpectrum (𝓞 X.E) → X.Kˣ) (mI : SB → X.E → X.K) (lam : X.Tau → DomWeight a) (lam' : X.Tau → DomWeight b) (n : X.Tau → ℕ)
    (N : Submodule (𝓞 X.E) (Sp X.E a)) (fr : Frs X.E a SB) (N' : Submodule (𝓞 X.E) (Sp X.E b)) (fr' : Frs X.E b SB) (Ξ : HomE X.E a b → X.K) :
    DIV.VV X.K lam →ₗ[X.K] DIV.VV X.K lam' :=
  (muInvDet sel SB mU mI N fr * (muInvDet sel SB mU mI N' fr')⁻¹) • jetOp lam lam' (A.descentTableFirst Sall cA cB N N' Ξ) n

def KerOneEq : Prop :=
  ∀ (X : Fields) (A : Amb X) (a b : ℕ) (Sall SB : Finset (HeightOneSpectrum (𝓞 X.E))) (cA cB : ℕ), 0 < cA → 0 < cB →
    ∀ (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (mU : HeightOneSpectrum (𝓞 X.E) → X.Kˣ) (mI : SB → X.E → X.K)
    (lam : X.Tau → DomWeight a) (lam' : X.Tau → DomWeight b) (n : X.Tau → ℕ), A.ESmooth a b → A.JetsRatDeg a b Sall (cA * cB) (opDeg lam n) →
    ∀ (N : Submodule (𝓞 X.E) (Sp X.E a)) (fr : Frs X.E a SB) (N' : Submodule (𝓞 X.E) (Sp X.E b)) (fr' : Frs X.E b SB), IsSdLat N → IsSdLat N' →
    ∀ Ξ : HomE X.E a b → X.K, A.kerOne Sall SB cA cB sel mU mI lam lam' n N fr N' fr' Ξ =
      kerOf (thDistC A Sall SB (cA * cB) sel mU mI lam lam' n) Sall cA cB N fr N' fr' Ξ

def EntRatOfRho : Prop :=
  ∀ (X : Fields) (A : Amb X) (a b : ℕ) (Sall : Finset (HeightOneSpectrum (𝓞 X.E))) (cA cB : ℕ) (dg : X.Tau → ℕ) (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b))
    (Ξ : HomE X.E a b → X.K) (z : ℂ) (s : X.K), s ≠ 0 → z = A.σ₀ s * (A.chiF a b N N')⁻¹ →
    (∀ m : DVar X.Tau a b →₀ ℕ, (∀ τ, degAt m τ = dg τ) → ∃ k : X.K, A.σ₀ k = z * jetC A.cD (A.thDat Sall cA cB N N' Ξ) m) → A.EntRat Sall cA cB dg N N' Ξ

def JetSetDegOfReps : Prop :=
  ∀ (X : Fields) (A : Amb X) (a b : ℕ) (Sall : Finset (HeightOneSpectrum (𝓞 X.E))) (D : ℕ) (dg : X.Tau → ℕ)
    (Rp : Set (Submodule (𝓞 X.E) (Sp X.E a) × Submodule (𝓞 X.E) (Sp X.E b))) (F : Subfield ℂ), IsRepSet a b Rp → A.ThIndEq a b Sall D → A.ChiLaw a b → A.IndEntire a b Sall D →
    (∀ τ x, X.embC A.σ₀ τ x ∈ F) →
    (∀ p ∈ Rp, ∀ (c : ℕ) (x : HomE X.E a b), InRange Sall D c p.1 p.2 x → ∀ m : DVar X.Tau a b →₀ ℕ, (∀ τ, degAt m τ = dg τ) →
      (A.chiF a b p.1 p.2)⁻¹ * jetC A.cD (A.thInd Sall p.1 p.2 c x) m ∈ F) →
    ∀ z ∈ A.jetSetDeg a b Sall D dg, z ∈ F

def KerEntTied.DegTie {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {K : G.Consts} {Y : DivX D} {cX : ExtraC}
    {ex : Extra D L hT Gi Gl K Y cX} (t : KerEntTied ex) (W : Wts t.X t.Pr.Word D.R) : Prop :=
  ∀ u i, i < D.R.m → ∀ τ : t.X.Tau, stepDeg W (t.word u) i τ = ∑ r, nuT D u i (t.seam.iT τ) r

def StepsRatStepDeg : Prop :=
  ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC)
    (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex) (W : Wts t.X t.Pr.Word D.R), t.FieldTie → t.RKCos → t.DegTie W → ∀ u μ, Formalism.BasicNotions.DV.Used D μ → ∀ i, i < D.R.m →
    t.amb.JetsRatDeg (D.R.N i) (D.R.N (i + 1)) (Sall t.sel (t.tup μ) (t.word u)) (cAof t.sel (t.tup μ) (t.cst μ) * cBof t.sel (t.tup μ) (t.cst μ) (t.word u))
      (stepDeg W (t.word u) i)

end Formalism.L2.Ker
