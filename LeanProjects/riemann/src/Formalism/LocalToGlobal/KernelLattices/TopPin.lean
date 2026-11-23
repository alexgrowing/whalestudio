import Formalism.LocalToGlobal.KernelLattices.FirstKernelLawReading
import Formalism.LocalToGlobal.KernelLattices.ThDatRead
import Formalism.LocalToGlobal.Columns.ChainInstY
import Formalism.LocalToGlobal.Columns.ChainTwFrA

open NumberField IsDedekindDomain

noncomputable section

namespace Formalism.L2.Ker

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.L2.DIV

section Row

variable {X : Fields} {Pr : Primes X} {R : Ranks} (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (v : Pr.Word)

open Classical in

def AtRow (d : RowPt Pr R sel mu) (p' : DecoF X.E (R.N R.m) (Pr.vT v) Pr.vGs (QE sel (mu : Chr X.F X.E X.K))) : Prop :=
  p'.deco = tilC sel mu v d ∧ ∀ (P : HeightOneSpectrum (𝓞 X.E)) (hP : P ∈ QE sel (mu : Chr X.F X.E X.K)),
    p'.fr ⟨P, hP⟩ = (Sc.Fr.topFrA (R := R) sel mu v (Finset.subset_union_left : Pr.vGs ⊆ rowSG Pr sel mu)
      (fun _ hP => Finset.mem_union_right _ hP)).fr ⟨P, hP⟩ d

def OverRow {j : ℕ} (d : RowPt Pr R sel mu) (p : ChPt (R := R) sel mu v j) : Prop :=
  ∃ p' : DecoF X.E (R.N R.m) (Pr.vT v) Pr.vGs (QE sel (mu : Chr X.F X.E X.K)), HEq p p' ∧ AtRow sel mu v d p'

end Row

section Pin

variable {D : D7} {X : Fields} {u : D.what₂.Word} {C : ColumnChain D.R D.what₂.Tau (D.hcW u)}
variable {Pr : Primes X} (Ch : Chars X Pr D.R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr D.R (QE sel (mu : Chr X.F X.E X.K)))

def KerRead.TopPinAt (r : KerRead C X) (σ : X.K →+* ℂ) (v : Pr.Word) (m2 : ℕ) (p1 : C.cls (m2 + 1) → ChPt (R := D.R) sel mu v (m2 + 1))
    (yb : C.cls (m2 + 1) → Set (Sp X.E (D.R.N (m2 + 1)))) (pT : C.cls (m2 + 1 + 1) → ChPt (R := D.R) sel mu v (m2 + 1 + 1)) : Prop :=
  (∀ c', r.N (m2 + 1 + 1) c' = (pT c').deco.1.N) ∧
    ∀ c c' x, r.Xi (m2 + 1) c c' x = σ (XiTop Ch sel mu cst (m2 + 1) (p1 c) (yb c) (pT c') x)

def KerRead.TopPin (r : KerRead C X) (σ : X.K →+* ℂ) (v : Pr.Word) (m2 : ℕ) : Prop :=
  ∃ (p1 : C.cls (m2 + 1) → ChPt (R := D.R) sel mu v (m2 + 1)) (yb : C.cls (m2 + 1) → Set (Sp X.E (D.R.N (m2 + 1))))
    (pT : C.cls (m2 + 1 + 1) → ChPt (R := D.R) sel mu v (m2 + 1 + 1)),
    (∀ c, r.N (m2 + 1) c = (p1 c).deco.1.N) ∧ (∀ c, yb c ∈ ybSet sel mu cst (p1 c).deco.1.N) ∧ r.TopPinAt Ch sel mu cst σ v m2 p1 yb pT

def KerRead.IsChainTop (r : KerRead C X) (σ : X.K →+* ℂ) (v : Pr.Word) (m2 : ℕ) : Prop :=
  r.SS = Sall sel mu v ∧ r.lev = levC sel mu cst v ∧
  ∃ (pt : ∀ i, i ≤ m2 + 1 → C.cls i → ChPt (R := D.R) sel mu v i) (ix : ∀ i, i ≤ m2 → C.cls i → L.β i)
    (yb : C.cls (m2 + 1) → Set (Sp X.E (D.R.N (m2 + 1)))) (pT : C.cls (m2 + 1 + 1) → ChPt (R := D.R) sel mu v (m2 + 1 + 1)),
    (∀ i (hi : i ≤ m2 + 1) c, r.N i c = (pt i hi c).deco.1.N) ∧
    (∀ c', yb c' ∈ ybSet sel mu cst (pt (m2 + 1) le_rfl c').deco.1.N) ∧
    (∀ i (hi : i < m2) c c' x, r.Xi i c c' x =
      σ (XiEntry Ch sel mu cst L i (ix i hi.le c) (ix (i + 1) hi c') (pt i (by omega) c) (pt (i + 1) (by omega) c') x)) ∧
    (∀ c c' x, r.Xi m2 c c' x =
      σ (XiCpl1 Ch sel mu cst L m2 (ix m2 le_rfl c) (pt m2 (Nat.le_succ _) c) (pt (m2 + 1) le_rfl c') (yb c') x)) ∧
    r.TopPinAt Ch sel mu cst σ v m2 (pt (m2 + 1) le_rfl) yb pT ∧
    (∀ i, i ≤ m2 + 1 → ∀ c, r.pin i c) ∧ ∀ c', r.pin (m2 + 1 + 1) c' ↔ ∃ d, OverRow sel mu v d (pT c')

end Pin

section Stmt

def TopChain : Prop :=
  ∀ (D : D7) (X : Fields) (u : D.what₂.Word) (C : ColumnChain D.R D.what₂.Tau (D.hcW u)) (r : KerRead C X) (Pr : Primes X) (Ch : Chars X Pr D.R.m)
    (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ) (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu))
    (L : ChIdx X Pr D.R (QE sel (mu : Chr X.F X.E X.K))) (σ : X.K →+* ℂ) (v : Pr.Word) (m2 : ℕ), X.Ok → Pr.Ok → cst.Ok → D.R.m = m2 + 2 →
    (∀ w : rowSG Pr sel mu, Pr.piT v ∉ w.1.asIdeal) → r.IsChainTop Ch sel mu cst L σ v m2 → r.IsChain Ch sel mu cst L σ v m2

def TopOfChainTop : Prop :=
  ∀ (D : D7) (X : Fields) (u : D.what₂.Word) (C : ColumnChain D.R D.what₂.Tau (D.hcW u)) (r : KerRead C X) (Pr : Primes X) (Ch : Chars X Pr D.R.m)
    (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ) (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu))
    (L : ChIdx X Pr D.R (QE sel (mu : Chr X.F X.E X.K))) (σ : X.K →+* ℂ) (v : Pr.Word) (m2 : ℕ),
    r.IsChainTop Ch sel mu cst L σ v m2 → r.TopPin Ch sel mu cst σ v m2

def TopRead : Prop :=
  ∀ (D : D7) (X : Fields) (u : D.what₂.Word) (C : ColumnChain D.R D.what₂.Tau (D.hcW u)) (r : KerRead C X) (s : Seam D X) (A : Amb X) (Pr : Primes X)
    (Ch : Chars X Pr D.R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ) (mu : Tup X.F X.E X.K S)
    (cst : LocCst X (rowSG Pr sel mu)) (σ : X.K →+* ℂ) (v : Pr.Word) (m2 : ℕ) (p1 : C.cls (m2 + 1) → ChPt (R := D.R) sel mu v (m2 + 1))
    (yb : C.cls (m2 + 1) → Set (Sp X.E (D.R.N (m2 + 1)))) (pT : C.cls (m2 + 1 + 1) → ChPt (R := D.R) sel mu v (m2 + 1 + 1)),
    r.SS = Sall sel mu v → r.lev = levC sel mu cst v → (∀ c, r.N (m2 + 1) c = (p1 c).deco.1.N) → r.TopPinAt Ch sel mu cst σ v m2 p1 yb pT →
    ∀ c c', r.Th s A (m2 + 1) c c' =
      s.push (thC (X.embC A.σ₀) A.δ A.d A.sc A.AA (Sall sel mu v) (p1 c).deco.1.N (pT c').deco.1.N (levC sel mu cst v)
        (fun x => σ (XiTop Ch sel mu cst (m2 + 1) (p1 c) (yb c) (pT c') x)) (A.e _ _ (p1 c).deco.1.N (pT c').deco.1.N))

def TopFree : Prop :=
  ∀ (D : D7) (X : Fields) (u : D.what₂.Word) (C : ColumnChain D.R D.what₂.Tau (D.hcW u)) (r r' : KerRead C X) (Pr : Primes X) (Ch : Chars X Pr D.R.m)
    (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ) (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu))
    (L : ChIdx X Pr D.R (QE sel (mu : Chr X.F X.E X.K))) (σ : X.K →+* ℂ) (v : Pr.Word) (m2 : ℕ),
    r.IsChain Ch sel mu cst L σ v m2 → (∀ c', ¬ r.pin (m2 + 1 + 1) c') → r'.SS = r.SS → r'.lev = r.lev → r'.pin = r.pin →
    (∀ i, i ≤ m2 + 1 → r'.N i = r.N i) → (∀ i, i ≤ m2 → r'.Xi i = r.Xi i) → r'.IsChain Ch sel mu cst L σ v m2

def TopRigid : Prop :=
  ∀ (D : D7) (X : Fields) (u : D.what₂.Word) (C : ColumnChain D.R D.what₂.Tau (D.hcW u)) (r r' : KerRead C X) (Pr : Primes X) (Ch : Chars X Pr D.R.m)
    (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ) (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu))
    (σ : X.K →+* ℂ) (v : Pr.Word) (m2 : ℕ) (p1 : C.cls (m2 + 1) → ChPt (R := D.R) sel mu v (m2 + 1))
    (yb : C.cls (m2 + 1) → Set (Sp X.E (D.R.N (m2 + 1)))) (pT : C.cls (m2 + 1 + 1) → ChPt (R := D.R) sel mu v (m2 + 1 + 1)),
    r.TopPinAt Ch sel mu cst σ v m2 p1 yb pT → r'.TopPinAt Ch sel mu cst σ v m2 p1 yb pT →
    r'.N (m2 + 1 + 1) = r.N (m2 + 1 + 1) ∧ r'.Xi (m2 + 1) = r.Xi (m2 + 1)

def TopSd : Prop :=
  ∀ (D : D7) (X : Fields) (u : D.what₂.Word) (C : ColumnChain D.R D.what₂.Tau (D.hcW u)) (r : KerRead C X) (Pr : Primes X) (Ch : Chars X Pr D.R.m)
    (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ) (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu))
    (L : ChIdx X Pr D.R (QE sel (mu : Chr X.F X.E X.K))) (σ : X.K →+* ℂ) (v : Pr.Word) (m2 : ℕ),
    r.IsChainTop Ch sel mu cst L σ v m2 → ∀ i, i ≤ m2 + 1 + 1 → ∀ c, IsSdLat (r.N i c)

def TopStrict : Prop :=
  ∀ (D : D7) (X : Fields) (u : D.what₂.Word) (C : ColumnChain D.R D.what₂.Tau (D.hcW u)) (r : KerRead C X) (Pr : Primes X) (Ch : Chars X Pr D.R.m)
    (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ) (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu))
    (L : ChIdx X Pr D.R (QE sel (mu : Chr X.F X.E X.K))) (σ : X.K →+* ℂ) (v : Pr.Word) (m2 : ℕ),
    r.IsChain Ch sel mu cst L σ v m2 → (∀ c', ¬ r.pin (m2 + 1 + 1) c') → Nonempty (C.cls (m2 + 1 + 1)) →
    ∃ r' : KerRead C X, r'.IsChain Ch sel mu cst L σ v m2 ∧ ¬ r'.IsChainTop Ch sel mu cst L σ v m2

def XiTopAdm {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
    (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) {u : Pr.Word} (i : ℕ) (p : ChPt (R := R) sel mu u i) (Y : Set (Sp X.E (R.N i)))
    (p' : ChPt (R := R) sel mu u (i + 1)) : Prop :=
  (∀ x ∈ divLat (cAof sel mu cst) (homAt (Sall sel mu u) p.deco.1.N p'.deco.1.N),
    ∀ y ∈ mulLat (cBof sel mu cst u) (homAt (Sall sel mu u) p.deco.1.N p'.deco.1.N),
      XiTop Ch sel mu cst i p Y p' (x + y) = XiTop Ch sel mu cst i p Y p' x) ∧
  ∀ x, x ∉ divLat (cAof sel mu cst) (homAt (Sall sel mu u) p.deco.1.N p'.deco.1.N) → XiTop Ch sel mu cst i p Y p' x = 0

def XiTopAdmRef : Prop :=
  ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ)
    (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (m2 : ℕ) (u : Pr.Word) (p : ChPt (R := R) sel mu u (m2 + 1))
    (Y : Set (Sp X.E (R.N (m2 + 1)))) (p' : ChPt (R := R) sel mu u (m2 + 1 + 1)), X.Ok → Pr.Ok → cst.Ok → R.m = m2 + 2 →
    QE sel (mu : Chr X.F X.E X.K) = ∅ → Y ∈ ybSet sel mu cst p.deco.1.N → XiTopAdm Ch sel mu cst (m2 + 1) p Y p'

def ReadThDatTop : Prop :=
  ∀ (D : D7) (X : Fields) (u : D.what₂.Word) (C : ColumnChain D.R D.what₂.Tau (D.hcW u)) (r : KerRead C X) (s : Seam D X) (A : Amb X) (Pr : Primes X)
    (Ch : Chars X Pr D.R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ) (mu : Tup X.F X.E X.K S)
    (cst : LocCst X (rowSG Pr sel mu)) (v : Pr.Word) (m2 : ℕ) (p1 : C.cls (m2 + 1) → ChPt (R := D.R) sel mu v (m2 + 1))
    (yb : C.cls (m2 + 1) → Set (Sp X.E (D.R.N (m2 + 1)))) (pT : C.cls (m2 + 1 + 1) → ChPt (R := D.R) sel mu v (m2 + 1 + 1)),
    r.SS = Sall sel mu v → r.lev = levC sel mu cst v → (∀ c, r.N (m2 + 1) c = (p1 c).deco.1.N) → r.TopPinAt Ch sel mu cst A.σ₀ v m2 p1 yb pT →
    0 < Pr.T v → A.LaHyp (D.R.N (m2 + 1)) (D.R.N (m2 + 1 + 1)) (Sall sel mu v) →
    ∀ c c', XiTopAdm Ch sel mu cst (m2 + 1) (p1 c) (yb c) (pT c') →
      r.Th s A (m2 + 1) c c' = s.push (A.thDat (Sall sel mu v) (cAof sel mu cst) (cBof sel mu cst v) (p1 c).deco.1.N (pT c').deco.1.N
        (XiTop Ch sel mu cst (m2 + 1) (p1 c) (yb c) (pT c')))

def XiTopNe : Prop :=
  ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ)
    (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (u : Pr.Word), X.Ok → Pr.Ok → cst.Ok → R.m = 2 →
    QE sel (mu : Chr X.F X.E X.K) = ∅ → (∀ w : Pr.vGs, Pr.piT u ∉ w.1.asIdeal) → cst.sharp = false → (∀ P a, cst.psi P a ≠ 0) →
    ∃ (p : ChPt (R := R) sel mu u (0 + 1)) (Y : Set (Sp X.E (R.N (0 + 1)))) (p' : ChPt (R := R) sel mu u (0 + 1 + 1))
      (x : HomE X.E (R.N (0 + 1)) (R.N (0 + 1 + 1))), Y ∈ ybSet sel mu cst p.deco.1.N ∧ XiTop Ch sel mu cst (0 + 1) p Y p' x ≠ 0

end Stmt

section Comparison₂

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {K : G.Consts} {Y : DivX D} {cX : ExtraC}

def KerEntTied.TopPinned {ex : Extra D L hT Gi Gl K Y cX} (t : KerEntTied ex) : Prop :=
  ∀ u μ, (t.rd u μ).IsChainTop t.Ch t.sel (t.tup μ) (t.cst μ) (t.idx μ) t.seam.σ₀ (t.word u) t.m2

def KerEntTied.TopInt {ex : Extra D L hT Gi Gl K Y cX} (t : KerEntTied ex) : Prop :=
  ∀ u μ (c : (D.chTw u μ).cls (t.m2 + 1)) (c' : (D.chTw u μ).cls (t.m2 + 1 + 1)), ¬ (t.rd u μ).pin (t.m2 + 1 + 1) c' →
    ∀ x, IntOff (t.O u μ).S ((t.rd u μ).Xi (t.m2 + 1) c c' x)

end Comparison₂

def HypFreeOfTop : Prop :=
  ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC)
    (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex), t.TopPinned → t.TopInt → t.HypFree

end Formalism.L2.Ker
