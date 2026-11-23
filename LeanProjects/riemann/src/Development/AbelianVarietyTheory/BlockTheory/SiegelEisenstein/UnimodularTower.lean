import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.ProductFirstZerothParts
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnfoldingConstantsPos
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChainOnto
open scoped TensorProduct InnerProductSpace ComplexConjugate

namespace GlobalTheory.IndefiniteRowSideFullHecke.UnimodularTower

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

abbrev Fn (D : D7) (u : D.what₂.Word) (i : ℕ) : Type := Formalism.MainNotions.product_first_zeroth_parts.Fn D u i

abbrev Fm (D : D7) (u : D.what₂.Word) (i : ℕ) : Submodule ℂ (Fn D u i) := (D.fm u).Fi i

abbrev Ram (D : D7) (u : D.what₂.Word) (i : ℕ) : Submodule ℂ (Fn D u i) := Formalism.MainNotions.product_first_zeroth_parts.MramI D u i

abbrev Eps (D : D7) (u : D.what₂.Word) : Type := ∀ v : (D.mem u).A.vT, ((D.mem u).A.Fv v)ˣ

def ffStar (D : D7) (u : D.what₂.Word) (i : ℕ) (ε : Eps D u) : Fn D u i →ₗ[ℂ] Fn D u i :=
  (Finset.univ : Finset (D.mem u).A.vT).toList.foldr (fun v g =>
    (Formalism.MainNotions.product_first_zeroth_parts.dia D u i v (ε v) ∘ₗ Formalism.MainNotions.product_first_zeroth_parts.Uop D u i v ∘ₗ Formalism.MainNotions.product_first_zeroth_parts.GsD D u i v) ∘ₗ g) LinearMap.id

structure Passage (D : D7) (u : D.what₂.Word) : Prop where
  ff_ram : ∀ i, i + 2 ≤ D.R.m → ∀ ε, ∀ φ ∈ Ram D u i, ffStar D u i ε φ ∈ Ram D u i
  ker_ram : ∀ i, i + 3 ≤ D.R.m → ∀ φ ∈ Ram D u i, Formalism.MainNotions.product_first_zeroth_parts.KT D u i φ ∈ Ram D u (i + 1)
  comm : ∀ i, i + 3 ≤ D.R.m → ∃ a : ℂ, a ≠ 0 ∧ ∀ ε, ∀ φ ∈ Ram D u i,
    ffStar D u (i + 1) ε (Formalism.MainNotions.product_first_zeroth_parts.KT D u i φ) = a • Formalism.MainNotions.product_first_zeroth_parts.KT D u i (ffStar D u i ε φ)
  bij : ∀ ε, Set.BijOn (ffStar D u 0 ε) (Ram D u 0) (Ram D u 0)

def IsSharp (c : Com D) : Prop :=
  (∃ pb, Lev.IsTypePlaces D.host.g pb c.Pg) ∧
  ∃ ψ0 : ∀ PP : Pl D.host.E, AddChar (kP PP) ℂ, IsGenericPsi c.Pg ψ0 ∧
    ∃ π : Equiv.Perm (Fin D.R.r), IsSymOrd D.R.rS D.R.k π ∧
      (∀ g, g ∈ c.P.H ↔ reord π g ∈ (PsharpSym c.Pg D.R.r D.R.rS D.R.k ψ0).H) ∧
      ∀ g hg hg', c.P.chi ⟨g, hg⟩ = (PsharpSym c.Pg D.R.r D.R.rS D.R.k ψ0).chi ⟨reord π g, hg'⟩

def colPar (D : D7) (u : D.what₂.Word) (j : ℕ) : D.what₂.Tau → SPar :=
  (TPar.ofWord D u (Ptw D).eta (Ptw D).eta_half).Xpar j

def Represents (L : HSp D) (a : D.host.E) : Prop := ∃ z : Fin L.rank → D.host.E, star z ⬝ᵥ L.gram *ᵥ z = a

def dcos {V : HSp D} (R : Subgroup (GA D V)) (b : GA D V) (K : Subgroup (GA D V)) : Set (GA D V) :=
  {h | ∃ r ∈ R, ∃ x ∈ GinfC V, ∃ κ ∈ K, h = r * x * b * κ}

def Unimod {V : HSp D} (R : Subgroup (GA D V)) (μ : Measure R) : Prop :=
  IsClosed (R : Set (GA D V)) ∧ μ.IsHaarMeasure ∧ μ.IsInvInvariant

structure RowOn (V : HSp D) where
  par : D.what₂.Tau → SPar
  M : DSModel V par
  Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)
  β : GL (Fin V.rank) (Lev.EAf D)
  L : LevDat D.host.E ℂ V.rank
  ν : Measure (GA D V)
  fd : Set (GA D V)

abbrev RowOn.st {V : HSp D} (r : RowOn V) : PiLocalization₂ D := ⟨V, r.par, r.M, r.Λ, r.β, r.L, r.ν, r.fd⟩

abbrev RowOn.lev {V : HSp D} (r : RowOn V) : Subgroup (GA D V) := Lev.levG V r.β r.L

structure RowOn.Is (c : Com D) (j : ℕ) {V : HSp D} (r : RowOn V) : Prop where
  is : r.st.Is c j
  rapid : ∀ (y : r.st.CC c) w, RapidDec V (PiLocalization₂.val y w)

structure ColOn (c : Com D) (u : D.what₂.Word) (X : HSp D) (j : ℕ) where
  M : DSModel X (colPar D u j)
  K : Subgroup (GA D X)
  a : Fm D u j →ₗ[ℂ] MultT c.θ M (K : Set (GA D X)) (fun _ => 1)

variable {c : Com D} {u : D.what₂.Word}

abbrev ColOn.sc {X : HSp D} {j : ℕ} (A : ColOn c u X j) (φ : Fm D u j) (v : SmT A.M) : GA D X → ℂ :=
  (A.a φ : SmT A.M →ₗ[ℂ] (GA D X → ℂ)) v

structure ColOn.Is {X : HSp D} {j : ℕ} (A : ColOn c u X j) : Prop where
  rank : X.rank = D.R.N j
  sig : ∀ τ : D.host.E →+* ℂ, X.sig τ = (D.R.N j, 0)
  fin : A.K ≤ GfC X
  opn : ∃ U : Subgroup (GA D X), IsOpen (U : Set (GA D X)) ∧ U ⊓ GfC X ≤ A.K
  inj : Function.Injective A.a
  cont : ∀ φ v, IsContAut X (A.sc φ v)

structure ColStep {X X' : HSp D} {j : ℕ} (A : ColOn c u X j) (A' : ColOn c u X' (j + 1)) where
  om : Om X X'
  f : WO X X' → ℂ
  it : PolF D X'.rank X.rank →ₗ[ℂ] SmT A.M →ₗ[ℂ] SmT A'.M

section ColStep

variable {X X' : HSp D} {j : ℕ} {A : ColOn c u X j} {A' : ColOn c u X' (j + 1)}

def ColStep.pt (k : ColStep A A') : PolF D X'.rank X.rank → (WO X X' → ℂ) :=
  pureTensorO c.ψ c.θ X X' (cart A.M) (cart A'.M) (onb A.M) (onb A'.M) k.f

def ColStep.lift (k : ColStep A A') (vol : Vol X) (φ : GA D X → ℂ) (P : PolF D X'.rank X.rank) : GA D X' → ℂ :=
  liftT k.om vol.μ vol.𝓕 φ (k.pt P)

structure ColStep.Is (k : ColStep A A') (vol : Vol X) : Prop where
  weil : IsWeilDatumO c.ψ X X' (c.μ (j + 1)) (c.μ (j + 1)) k.om
  theta : ∀ P, IsThetaFunO c.ψ X X' (k.pt P)
  maps : ∀ φ ∈ Fm D u j, Formalism.MainNotions.product_first_zeroth_parts.KT D u j φ ∈ Fm D u (j + 1)
  it_ne : k.it ≠ 0
  sum : ∀ (φ : Fm D u j) (φ' : Fm D u (j + 1)), (φ' : Fn D u (j + 1)) = Formalism.MainNotions.product_first_zeroth_parts.KT D u j φ →
    ∀ P v, k.lift vol (A.sc φ v) P = A'.sc φ' (k.it P v)

end ColStep

structure RowStep (j : ℕ) {V V₀ W W₀ : HSp D} {ρ σ : ℕ} {r : RowOn V} {r' : RowOn W} (p : ChainOnto.Step c r.st r'.st)
    (s : Unf.Step c.ψ V V₀ W W₀ ρ σ) : Prop where
  is : p.Is j
  onto : r.st.KF ≤ Submodule.span ℂ {x | ∃ P, ∃ w ∈ r'.st.KF, x = p.It P w}
  χV : s.χV = c.chS j
  χW : s.χW = c.chT j
  om : s.om = p.ω
  μ : s.vW.μ = r'.ν
  fd : s.vW.𝓕 = r'.fd

structure Node (c : Com D) (u : D.what₂.Word) (ρ j : ℕ) where
  B : BesLev D ρ
  row : RowOn B.V
  col : ColOn c u B.A j
  b : GA D B.V

structure Node.Is {ρ j : ℕ} (N : Node c u ρ j) : Prop where
  row : N.row.Is c j
  col : N.col.Is
  line : Represents N.B.L (-((D.mem u).A.T : D.host.E))
  base : N.b ∈ GfC N.B.V
  unimod : Unimod (besGrp N.B.d N.B.o) N.B.μR

structure Dbl {σ j : ℕ} (N : Node c u (σ + 1) j) (N' : Node c u σ (j + 1 + 1)) where
  J : JacLev D (σ + 1)
  row : RowOn J.W
  col : ColOn c u J.W₀ (j + 1)
  b : GA D J.W
  s₁ : StepBF c.ψ N.B J
  s₂ : StepFB c.ψ J N'.B
  l : Link N.B N'.B.L N'.B.ζ
  vL : VolM D N'.B.L.rank J.W₀.rank
  p₁ : ChainOnto.Step c N.row.st row.st
  p₂ : ChainOnto.Step c row.st N'.row.st
  k₁ : ColStep N.col col
  k₂ : ColStep col N'.col
  ε : Eps D u

section Dbl

variable {σ j : ℕ} {N : Node c u (σ + 1) j} {N' : Node c u σ (j + 1 + 1)}

def Dbl.hand (d : Dbl N N') (P₁ : PolF D d.J.W.rank N.B.V.rank) (P₂ : PolF D N'.B.V.rank d.J.W.rank) (φ : GA D N.B.A → ℂ)
    (g : GA D N.B.V) (h₁ : GA D d.J.W) (h₂ : GA D N'.B.V) : GA D N'.B.A → ℂ :=
  Chain.hand d.s₁ d.s₂ d.l d.vL (d.p₁.pt P₁) (d.p₂.pt P₂) φ g h₁ h₂

structure Dbl.Is (d : Dbl N N') : Prop where
  row : d.row.Is c (j + 1)
  col : d.col.Is
  base : d.b ∈ GfC d.J.W
  unimod : Unimod (jacGrp d.J.d) d.J.μR
  step₁ : RowStep (j + 1) d.p₁ d.s₁
  step₂ : RowStep (j + 1 + 1) d.p₂ d.s₂
  ker₁ : d.k₁.Is N.B.vA
  ker₂ : d.k₂.Is d.J.v0
  supp₁ : ∀ P₁ P₂ (φ : Fm D u j), (φ : Fn D u j) ∈ Ram D u j → ∀ v, ∀ x ∈ GinfC N.B.V,
    ∀ h₁ ∉ dcos (jacGrp d.J.d) d.b d.row.lev, ∀ h₂, d.hand P₁ P₂ (N.col.sc φ v) (x * N.b) h₁ h₂ = 0
  supp₂ : ∀ P₁ P₂ (φ : Fm D u j), (φ : Fn D u j) ∈ Ram D u j → ∀ v, ∀ x ∈ GinfC N.B.V, ∀ x₁ ∈ GinfC d.J.W,
    ∀ h₂ ∉ dcos (besGrp N'.B.d N'.B.o) N'.b N'.row.lev, d.hand P₁ P₂ (N.col.sc φ v) (x * N.b) (x₁ * d.b) h₂ = 0
  val : ∀ P₁ P₂, ∀ x ∈ GinfC N.B.V, ∀ x₁ ∈ GinfC d.J.W, ∀ x₂ ∈ GinfC N'.B.V,
    ∃ (n : ℕ) (Q₁ : Fin n → PolF D d.J.W₀.rank N.B.A.rank) (Q₂ : Fin n → PolF D N'.B.A.rank d.J.W₀.rank),
      ∀ φ φ' : Fm D u j, (φ : Fn D u j) ∈ Ram D u j → (φ' : Fn D u j) = ffStar D u j d.ε φ → ∀ v,
        d.hand P₁ P₂ (N.col.sc φ v) (x * N.b) (x₁ * d.b) (x₂ * N'.b) =
          ∑ i, d.k₂.lift d.J.v0 (d.k₁.lift N.B.vA (N.col.sc φ' v) (Q₁ i)) (Q₂ i)

end Dbl

structure Fin2 {j : ℕ} (N : Node c u 0 j) {T : HSp D} (top : RowOn T) where
  t : Last c.ψ T N.B
  row : RowOn t.J.W
  col₁ : ColOn c u t.J.W (j + 1)
  X : HSp D
  L : HSp D
  o : OrthDec X T L
  col₂ : ColOn c u X (j + 1 + 1)
  p₁ : ChainOnto.Step c N.row.st row.st
  p₂ : ChainOnto.Step c row.st top.st
  k₁ : ColStep N.col col₁
  k₂ : ColStep col₁ col₂
  ε : Eps D u
  ι : (D.mem u).P.Mt ≃ₗ[ℂ] top.st.CC c
  br : SmT col₂.M →ₗ[ℂ] SmT top.M →ₗ[ℂ] ℂ

section Fin2

variable {j : ℕ} {N : Node c u 0 j} {T : HSp D} {top : RowOn T}

def Fin2.inner (e : Fin2 N top) (P₁ : PolF D e.t.J.W.rank N.B.V.rank) (P₂ : PolF D T.rank e.t.J.W.rank) (φ : GA D N.B.A → ℂ)
    (g : GA D N.B.V) (h' : GA D T) : ℂ :=
  ∫ h in e.t.s.vW.𝓕, e.t.om (h, h') (e.p₂.pt P₂) 0 * (∫ h₀ in N.B.vA.𝓕,
    φ h₀ * e.t.s.om (embA N.B.d N.B.o h₀, h) (e.t.s.om (g, 1) (e.p₁.pt P₁)) 0 ∂N.B.vA.μ) ∂e.t.s.vW.μ

theorem Fin2.Q_eq (e : Fin2 N top) (P₁ P₂ φ g) (F : GA D T → ℂ) :
    e.t.Q φ (e.t.s.om (g, 1) (e.p₁.pt P₁)) (e.p₂.pt P₂) F = ∫ h' in e.t.vT.𝓕, F h' * e.inner P₁ P₂ φ g h' ∂e.t.vT.μ := rfl

structure Fin2.Is (e : Fin2 N top) : Prop where
  idx : j + 1 + 1 = D.R.m
  row : e.row.Is c (j + 1)
  top_is : top.st.Is c (j + 1 + 1)
  top_cont : ∀ (y : top.st.CC c) w, IsContAut T (PiLocalization₂.val y w)
  col₁ : e.col₁.Is
  col₂ : e.col₂.Is
  line : e.L.rank = 1 ∧ Represents e.L ((D.mem u).A.T : D.host.E)
  step₁ : RowStep (j + 1) e.p₁ e.t.s
  is₂ : e.p₂.Is (j + 1 + 1)
  onto₂ : e.row.st.KF ≤ Submodule.span ℂ {x | ∃ P, ∃ w ∈ top.st.KF, x = e.p₂.It P w}
  χS : e.t.χS = c.chS (j + 1 + 1)
  χT : e.t.χT = c.chT (j + 1 + 1)
  om : e.t.om = e.p₂.ω
  μ : e.t.vT.μ = top.ν
  fd : e.t.vT.𝓕 = top.fd
  ker₁ : e.k₁.Is N.B.vA
  ker₂ : e.k₂.Is e.t.s.vW
  val : ∀ P₁ P₂, ∀ x ∈ GinfC N.B.V,
    ∃ (n : ℕ) (Q₁ : Fin n → PolF D e.t.J.W.rank N.B.A.rank) (Q₂ : Fin n → PolF D e.X.rank e.t.J.W.rank),
      ∀ φ φ' : Fm D u j, (φ : Fn D u j) ∈ Ram D u j → (φ' : Fn D u j) = ffStar D u j e.ε φ → ∀ v h',
        e.inner P₁ P₂ (N.col.sc φ v) (x * N.b) h' =
          ∑ i, e.k₂.lift e.t.s.vW (e.k₁.lift N.B.vA (N.col.sc φ' v) (Q₁ i)) (Q₂ i) (e.o.emb (h', 1))
  br_ne : e.br ≠ 0
  period : ∀ (φ : Fm D u (j + 1 + 1)) (φ' : Fn D u D.R.m), HEq φ' (φ : Fn D u (j + 1 + 1)) → ∀ (F : (D.mem u).P.Mt) v w,
    ∫ h' in top.fd, PiLocalization₂.val (e.ι F) w h' * e.col₂.sc φ v (e.o.emb (h', 1)) ∂top.ν = e.br v w * (D.mem u).P.Ptil φ' F

end Fin2

inductive Tower (c : Com D) (u : D.what₂.Word) {T : HSp D} (top : RowOn T) : (ρ j : ℕ) → Node c u ρ j → Type 1
  | last {j : ℕ} {N : Node c u 0 j} (e : Fin2 N top) : Tower c u top 0 j N
  | step {σ j : ℕ} {N : Node c u (σ + 1) j} (N' : Node c u σ (j + 1 + 1)) (d : Dbl N N')
      (t : Tower c u top σ (j + 1 + 1) N') : Tower c u top (σ + 1) j N

inductive Tower.Is {T : HSp D} {top : RowOn T} : {ρ j : ℕ} → {N : Node c u ρ j} → Tower c u top ρ j N → Prop
  | last {j : ℕ} {N : Node c u 0 j} (e : Fin2 N top) (hN : N.Is) (he : e.Is) : Tower.Is (.last e)
  | step {σ j : ℕ} {N : Node c u (σ + 1) j} (N' : Node c u σ (j + 1 + 1)) (d : Dbl N N') (t : Tower c u top σ (j + 1 + 1) N')
      (hN : N.Is) (hd : d.Is) (ht : t.Is) : Tower.Is (.step N' d t)

theorem Tower.Is.index {T : HSp D} {top : RowOn T} {ρ j : ℕ} {N : Node c u ρ j} {t : Tower c u top ρ j N} (h : t.Is) :
    j + 2 * ρ + 2 = D.R.m := by
  induction h with
  | last e _ he => have := he.idx; omega
  | step _ _ _ _ _ _ ih => omega

def LinkP {ρ : ℕ} (N : Node c u ρ 0) : Prop :=
  ∃ (cj : N.row.st.CC c →ₗ⋆[ℂ] D.s.HH) (U : Ram D u 0 →ₗ[ℂ] D.s.Cu u) (ℓ : SmT N.col.M →ₗ[ℂ] SmT N.row.M →ₗ[ℂ] ℂ),
    Function.Bijective cj ∧ Function.Injective U ∧ (∀ φ, U φ ∈ ramCu D u) ∧ (∃ v, ∃ w ∈ N.row.st.KF, ℓ v w ≠ 0) ∧
    ∀ (φ : Fm D u 0) (h : (φ : Fn D u 0) ∈ Ram D u 0) (e : N.row.st.CC c) v w,
      N.B.per c.ψ (N.col.sc φ v) (rTrans N.b (PiLocalization₂.val e w)) = ℓ v w * ⟪cj e, D.s.Pu u (U ⟨φ, h⟩)⟫_ℂ

def Laws (D : D7) (u : D.what₂.Word) : Prop :=
  Passage D u ∧ ∃ c : Com D, c.Is ∧ IsSharp c ∧ ∃ (T : HSp D) (top : RowOn T) (N : Node c u D.R.rS 0)
    (t : Tower c u top D.R.rS 0 N), t.Is ∧ LinkP N

def Suffices (D : D7) (u : D.what₂.Word) : Prop :=
  GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.NodeGap D → DoubleStep D → LastLaw D → LevelLaw D → ChainOnto.OntoAll D → Laws D u → GlobalTheory.Core.Rk.KerIncl D u

example (D : D7) : 0 + 2 * D.R.rS + 2 = D.R.m := by
  obtain ⟨t, ht⟩ := D.R.m_even
  have h2 := D.R.two_le_m
  simp only [Ranks.rS]
  omega

example {V : HSp D} (R K : Subgroup (GA D V)) (b : GA D V) : b ∈ dcos R b K :=
  ⟨1, one_mem _, 1, one_mem _, 1, one_mem _, by simp⟩

example (D : D7) (u : D.what₂.Word) : Ram D u 0 = (D.mem u).A.Mram := Formalism.MainNotions.product_first_zeroth_parts.MramI_zero D u

end GlobalTheory.IndefiniteRowSideFullHecke.UnimodularTower

end
