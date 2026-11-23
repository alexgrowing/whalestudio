import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TopOrthEmb
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealLineOfPeriodsOnLine
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsBiSmooth
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CombAtSingleZero

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw
open scoped NNReal

namespace GlobalTheory.RowVal

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable def NIter {ι : Type} [DecidableEq ι] {H : ι → Type} [∀ i, Group (H i)] [∀ i, MeasurableSpace (H i)] {R : ∀ i, Subgroup (H i)}
    (ρ : ∀ i, Measure (R i)) (μ : ∀ i, Measure (H i)) (q : (∀ i, H i) → ℂ) : List ι → (∀ i, H i) → ℂ → Prop
  | [], h, z => z = q h
  | i :: l, h, z => ∃ f : H i → ℂ, IsQuotIntL1 (ρ i) (μ i) f z ∧ ∀ g, NIter ρ μ q l (Function.update h i g) (f g)

def cellWt {B : Type} [Group B] [MeasurableSpace B] {R : Subgroup B} (ρ : Measure R) (μ : Measure B) (K : Subgroup B) (b : B) : ℂ :=
  ((μ.real (K : Set B) / ρ.real {r : R | b⁻¹ * r.1 * b ∈ K} : ℝ) : ℂ)

section Grid

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc)

abbrev Pts : Type := ∀ j : ℕ, GA D (G.V (.grid D.R.m j))

variable (D) in

def idx : List ℕ := List.range' 1 (D.R.m - 2)

def rowGrp (j : ℕ) : Subgroup (GA D (G.V (.grid D.R.m j))) :=
  if h : j + 2 * ((D.R.m - 1 - j) / 2) + 1 = D.R.m then jacGrp (rowJac G j (by omega) ((D.R.m - 1 - j) / 2) (by omega))
  else if h' : j + 2 * ((D.R.m - 2 - j) / 2) + 2 = D.R.m then
    besGrp (besDecAt G j _ h') (GlobalTheory.OrthSumExists.orthDecHsum D _ _) else ⊥

def latGrp (j : ℕ) : Subgroup (GA D (G.V (.grid D.R.m j))) :=
  GfC _ ⊓ (G.levMax (.grid D.R.m j)).comap (Lev.finE _)

abbrev BiFam : Type := ∀ j : ℕ, WO (G.V (.top j)) (G.V (.top (j + 1))) → WO (G.V (.top (j + 1))) (G.V (.top (j + 1 + 1))) → ℂ

abbrev ColPt : Type := ∀ j : ℕ, WO (G.V (.top j)) (G.V (.top (j + 1)))

abbrev RowPt : Type := ∀ i : Fin D.R.m, WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T))

variable {G}

def evT (C : BiFam G) (f : SchRow G) (u : ColPt G) (y : RowPt G) : ℂ :=
  (∏ k ∈ Finset.range (D.R.m / 2), C (2 * k) (u (2 * k)) (u (2 * k + 1))) * ∏ i, f i (y i)

variable (W : G.Weil) (M : Vol G) (t : T)

def biL (j : ℕ) (φ : Fn G (.top j)) (C : WO (G.V (.top j)) (G.V (.top (j + 1))) → WO (G.V (.top (j + 1))) (G.V (.top (j + 1 + 1))) → ℂ) :
    Fn G (.top (j + 1 + 1)) := fun h₂ =>
  ∫ h₁ in M.fd (.top (j + 1)), (∫ h₀ in M.fd (.top j), φ h₀ *
    W.om (.top t (j + 1)) (h₁, h₂) (fun v => W.om (.top t j) (h₀, h₁) (fun u => C u v) 0) 0 ∂M.ν (.top j)) ∂M.ν (.top (j + 1))

noncomputable def jPer (C : BiFam G) (F : Fn G (.grid D.R.m D.R.m)) : (σ j : ℕ) → j + 2 * σ + 2 = D.R.m → Fn G (.top j) → ℂ
  | 0, j, hj, φ => ∫ h' in M.fd (.grid D.R.m D.R.m),
      F h' * biL W M t j φ (C j) (GlobalTheory.RowChain.topEmb G (show D.R.m = j + 1 + 1 by omega) h') ∂M.ν (.grid D.R.m D.R.m)
  | σ + 1, j, hj, φ => jPer C F σ (j + 1 + 1) (by omega) (biL W M t j φ (C j))

def per (C : BiFam G) (f : SchRow G) (P : PolRow G) (φ : Fn G (.top 0)) (F : Fn G (.grid 0 D.R.m)) : ℂ :=
  jPer W M t C (liftP W M (rowPath T D.R.m D.R.m) (rowFam D.R.m D.R.m fun i => W.fock (.chi i D.R.m) (f i) (P i)) F)
    ((D.R.m - 2) / 2) 0 top_idx φ

variable {M t}

def conAt (hM : M.Is t) (Φ : SchDown G t) (h : Pts G) : BiFam G := fun j =>
  if h0 : j + 2 * 0 + 2 = D.R.m then
    lastDat W hM j h0 (GlobalTheory.Unf.Inhab.nonempty_volN _).some (h j) (Φ ⟨j, by omega⟩)
      (castSch G (show j + 1 + 1 = D.R.m by omega) (Φ ⟨j + 1, by omega⟩))
  else if hj : j + 2 * ((D.R.m - 4 - j) / 2 + 1) + 2 = D.R.m then
    GlobalTheory.Unf.contr (linkAt hM j _ hj (GlobalTheory.Unf.Inhab.nonempty_volN _).some (by omega) (GlobalTheory.Unf.Inhab.nonempty_volN _).some)
      (G.V (.top (j + 1))) ((GlobalTheory.Unf.Inhab.nonempty_volM D _ _).some)
      (GlobalTheory.Unf.flatBF (B := besAt G hM j _ hj (GlobalTheory.Unf.Inhab.nonempty_volN _).some)
        (J := jacAt G hM (j + 1) ((D.R.m - 4 - j) / 2 + 1) (by omega))
        (stepAt G W t hM j (by omega) (besDecAt G j _ hj) (rowJac G (j + 1) (by omega) ((D.R.m - 4 - j) / 2 + 1) (by omega)))
        (W.om (.mu t D.R.m j) (h j, h (j + 1)) (Φ ⟨j, by omega⟩)))
      (GlobalTheory.Unf.flatFB (J := jacAt G hM (j + 1) ((D.R.m - 4 - j) / 2 + 1) (by omega))
        (B := besAt G hM (j + 1 + 1) ((D.R.m - 4 - j) / 2) (by omega) (GlobalTheory.Unf.Inhab.nonempty_volN _).some)
        (stepAt G W t hM (j + 1) (by omega) (rowJac G (j + 1) (by omega) ((D.R.m - 4 - j) / 2 + 1) (by omega))
          (besDecAt G (j + 1 + 1) ((D.R.m - 4 - j) / 2) (by omega)))
        (W.om (.mu t D.R.m (j + 1)) (h (j + 1), h (j + 1 + 1)) (Φ ⟨j + 1, by omega⟩)))
  else 0

variable (t) in

def fockD (f : SchDown G t) (P : PolDown G) : SchDown G t := fun j => W.fock (.mu t D.R.m j) (f j) (P j)

def tot (hM : M.Is t) (P : PolRow G × PolDown G) (τ : SchRow G × SchDown G t →₀ ℂ) (φ : Fn G (.top 0)) (F : Fn G (.grid 0 D.R.m))
    (h : Pts G) : ℂ :=
  τ.sum fun d c => c * per W M t (conAt W hM (fockD W t d.2 P.2) h) d.1 P.1 φ F

def IsHaarDef (M : Vol G) : Prop :=
  ∀ X : Node, DefNode D.R.m X → X ≠ .top D.R.m → (M.ν X).IsHaarMeasure ∧ IsFundamentalDomain (GQ (G.V X)) (M.fd X) (M.ν X)

def Scales (M M' : Vol G) (s : Node → ℝ≥0) : Prop := ∀ X : Node, DefNode D.R.m X → X ≠ .top D.R.m → M.ν X = s X • M'.ν X

variable (D) in

def sProd (s : Node → ℝ≥0) : ℂ :=
  (∏ j ∈ Finset.range D.R.m, ((s (.top j) : ℝ) : ℂ)) * ∏ i ∈ Finset.range (D.R.m + 1), ((s (.grid i D.R.m) : ℝ) : ℂ)

def Good (C : BiFam G) (f : SchRow G) : Prop :=
  (∀ j, Even j → j < D.R.m → IsBiTheta W.ψ _ _ _ (C j)) ∧ ∀ i, IsThetaFunO W.ψ _ _ (f i)

def IsRealFam (C : BiFam G) : Prop :=
  ∀ j, Even j → j < D.R.m → IsBiVac W.ψ _ _ _ (G.Λ (.top j) : Set _) (G.Λ (.top (j + 1)) : Set _) (G.Λ (.top (j + 1 + 1)) : Set _) (C j) ∧
    IsBiSmooth (C j)

def IsCombOf {p : Pair T} (d : FinDatum G t p) (c : WO (G.pS p) (G.pT p) →₀ ℂ) : Prop :=
  IsFinComb c ∧ (∀ u ∈ c.support, IsHalf (d.e + cA D d.e) u) ∧ ∀ f₀, IsThetaFunO W.ψ _ _ f₀ →
    IsLatVac (heisO W.ψ _ _) (latO (G.pS p) (G.pT p) (G.latS p : Set _) (G.latT p : Set _) fun _ => True) f₀ →
    d.IsTheta W (G.latS p) (G.latT p) f₀ (comb W.ψ _ _ c f₀)

variable (G) in

abbrev Combs : Type := (∀ j : ℕ, WO (G.V (.top j)) (G.V (.top (j + 1))) →₀ ℂ) ×
  ∀ i : Fin D.R.m, WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T)) →₀ ℂ

def IsCombs (τ : PureDat G t →₀ ℂ) (c : PureDat G t → Combs G) : Prop :=
  ∀ d ∈ τ.support, (∀ j : Fin D.R.m, IsCombOf W (d.1 j) ((c d).1 j)) ∧ ∀ i, IsCombOf W (d.2 i) ((c d).2 i)

def combC (c : Combs G) (C : BiFam G) : BiFam G := fun j => biComb W.ψ _ _ _ (c.1 j) (c.1 (j + 1)) (C j)

variable {W} in

def combR (ρ : RealMatch W) (c : Combs G) : SchRow G := fun i => comb W.ψ _ _ (c.2 i) (ρ.vX i D.R.m)

variable (G) in

def IsTilt (j : ℕ) (g : GA D (G.V (.grid D.R.m j))) : Prop :=
  g ∈ GQ _ ∧ (Even j → g = 1) ∧ ∀ σ (h₁ : j < D.R.m) (h₂ : D.R.m - 1 - j = 2 * σ),
    HMul.hMul (mt _ g) ((rowJac G j h₁ σ h₂).i₀.map (incA D)) = (rowJac G j h₁ σ h₂).i₀.map (incA D) ∧
    HMul.hMul (mt _ g) ((rowJac G j h₁ σ h₂).e.map (incA D)) =
      ((rowJac G j h₁ σ h₂).e * diagonal fun a : Fin σ => (D.host.xi0 ^ a.1)⁻¹).map (incA D) ∧
    HMul.hMul (mt _ g) ((rowJac G j h₁ σ h₂).e'.map (incA D)) =
      ((rowJac G j h₁ σ h₂).e' * diagonal fun a : Fin σ => star (D.host.xi0 ^ a.1)).map (incA D)

variable (G t) in

def sgnAt (s : ℤˣ) (w : Pl D.host.E) (j : ℕ) : GL (Fin ((locGrid G t w).rank (D.R.m, j))) (Kw w) :=
  GlobalTheory.SplitFlip.diagGL fun a => if Odd j ∧ topRank (locGrid G t w) j + (D.R.m - 1 - j) / 2 ≤ a.1
    then Units.map (Int.castRingHom (Kw w)).toMonoidHom s else 1

variable (t) in

def HasLoc (B : Frames G) {j : ℕ} (hj : j ≤ D.R.m) (r : GA D (G.V (.grid D.R.m j)))
    (g : ∀ w : locPl G t, GL (Fin ((locGrid G t w.1).rank (D.R.m, j))) (Kw w.1)) : Prop :=
  ∃ e, IsIdemSum e (locPl G t) ∧ SuppAt e _ r ∧
    ∀ w : locPl G t, inBasis (rank_vertex G t w.1 (X := (D.R.m, j)) ⟨le_rfl, hj⟩) (B.β D.R.m j) w.1 (Lev.finE (G.V (.grid D.R.m j)) r) = g w

def IsFinOf {V : HSp D} (g b : GA D V) : Prop := b ∈ GfC V ∧ ∃ a ∈ GinfC V, a * b = g

variable (t) in

def IsRep (B : Frames G) (s : ℤˣ) (β : CosFam G t) (b : Pts G) : Prop :=
  (∀ j, j ∉ idx D → b j = 1) ∧ ∀ j ∈ idx D, ∀ hj : j ≤ D.R.m, ∃ δ r, IsTilt G j δ ∧
    HasLoc t B hj r (fun w => sgnAt G t s w.1 j * (repsAt G t w.1).elt (β w) (D.R.m, j)) ∧ IsFinOf (δ * r) (b j)

variable (t) in

def IsBase (B : Frames G) (b : Pts G) : Prop :=
  HasLoc t B (Nat.zero_le _) (b 0) (fun w => (stair (locGrid G t w.1) (unifAt w.1) (cosExp G w.1) 0)⁻¹) ∧
    (∀ j ∈ idx D, ∃ δ, IsTilt G j δ ∧ IsFinOf δ (b j)) ∧ ∀ j, j ≠ 0 → j ∉ idx D → b j = 1

def IsRealPt (a : Pts G) : Prop := (∀ j, a j ∈ GinfC _) ∧ ∀ j, j ∉ idx D → a j = 1

variable (t) in

def Stair (β : CosFam G t) : Prop :=
  ∀ w : locPl G t, w.1 ∈ G.pl.W0 → ∀ i, β w i = DoubleCoset.mk _ _ (stair (locGrid G t w.1) (unifAt w.1) (cosExp G w.1) (i + 1))

def wt (ρ : ∀ j, Measure ((rowGrp G j).subgroupOf (GfC _))) (μ : ∀ j, Measure (GfC (G.V (.grid D.R.m j)))) (b : Pts G) : ℂ :=
  open Classical in ((idx D).map fun j => if h : b j ∈ GfC _ then cellWt (ρ j) (μ j) ((latGrp G j).subgroupOf _) ⟨b j, h⟩ else 0).prod

end Grid

section Generic

variable {ι : Type} [DecidableEq ι] {H : ι → Type} [∀ i, Group (H i)] [∀ i, TopologicalSpace (H i)] [∀ i, MeasurableSpace (H i)]

structure Split {H : Type} [Group H] [TopologicalSpace H] [MeasurableSpace H] (A B R K : Subgroup H) : Prop where
  clA : IsClosed (A : Set H)
  clB : IsClosed (B : Set H)
  clR : IsClosed (R : Set H)
  comm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a
  prod : ∃ e : (A × B) ≃ₜ H, ∀ p, e p = p.1 * p.2
  split : ∀ a ∈ A, ∀ b ∈ B, a * b ∈ R → a ∈ R ∧ b ∈ R
  le : K ≤ B
  cpt : IsCompact (K : Set H)
  opn : IsOpen ((K.subgroupOf B : Subgroup B) : Set B)
  uniR : ∀ μ : Measure R, μ.IsHaarMeasure → μ.IsInvInvariant
  uniRB : ∀ μ : Measure (R.subgroupOf B), μ.IsHaarMeasure → μ.IsInvInvariant
  uniB : ∀ μ : Measure B, μ.IsHaarMeasure → μ.IsMulRightInvariant

def BiInv (R K : ∀ i, Subgroup (H i)) (l : List ι) (q : (∀ i, H i) → ℂ) : Prop :=
  ∀ i ∈ l, ∀ h, (∀ r ∈ R i, q (Function.update h i (r * h i)) = q h) ∧ ∀ k ∈ K i, q (Function.update h i (h i * k)) = q h

def InCells (A R K : ∀ i, Subgroup (H i)) (l : List ι) (b h : ∀ i, H i) : Prop :=
  ∀ i ∈ l, ∃ r ∈ R i, ∃ a ∈ A i, ∃ k ∈ K i, h i = r * a * b i * k

end Generic

def CellVan : Prop :=
  ∀ (ι : Type) [DecidableEq ι] (H : ι → Type) [∀ i, Group (H i)] [∀ i, TopologicalSpace (H i)] [∀ i, IsTopologicalGroup (H i)]
    [∀ i, SecondCountableTopology (H i)] [∀ i, LocallyCompactSpace (H i)] [∀ i, T2Space (H i)] [∀ i, MeasurableSpace (H i)]
    [∀ i, BorelSpace (H i)] (A B R K : ∀ i, Subgroup (H i)) (l : List ι), l.Nodup → (∀ i ∈ l, Split (A i) (B i) (R i) (K i)) →
    ∀ (ρ : ∀ i, Measure (R i)) (μ : ∀ i, Measure (H i)) (ρ' : ∀ i, Measure ((R i).subgroupOf (B i))) (μ' : ∀ i, Measure (B i)),
    (∀ i ∈ l, (ρ i).IsHaarMeasure ∧ (μ i).IsHaarMeasure ∧ (ρ' i).IsHaarMeasure ∧ (μ' i).IsHaarMeasure) →
    ∀ (X : Fin 2 → Type) (S : ∀ n, Finset (X n)) (b : ∀ n, X n → ∀ i, H i) (w : ∀ n, X n → ℂ) (q : Fin 2 → (∀ i, H i) → ℂ)
      (z α : Fin 2 → ℂ),
      (∀ n, ∀ β ∈ S n, (∀ i, i ∉ l → b n β i = 1) ∧ ∃ hb : ∀ i, b n β i ∈ B i,
        w n β = (l.map fun i => cellWt (ρ' i) (μ' i) ((K i).subgroupOf (B i)) ⟨b n β i, hb i⟩).prod) →
      (∀ n, ∀ β ∈ S n, ∀ β' ∈ S n, InCells A R K l (b n β) (b n β') → β = β') →
      (∀ n, BiInv R K l (q n)) → (∀ n h, (∀ i, i ∉ l → h i = 1) → q n h ≠ 0 → ∃ β ∈ S n, InCells A R K l (b n β) h) →
      (∀ n, NIter ρ μ (q n) l 1 (z n)) →
      (∀ a : ∀ i, H i, (∀ i, a i ∈ A i) → (∀ i, i ∉ l → a i = 1) → ∑ n, α n * ∑ β ∈ S n, w n β * q n (a * b n β) = 0) →
      ∑ n, α n * z n = 0

section
variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R)

def lhs (t : T) (M : Vol ch.G) (τi : PolRow ch.G × PolDown ch.G →₀ ℂ) (τ : SchRow ch.G × SchDown ch.G t →₀ ℂ) (a : Fin ch.n)
    (y : (R.HX t).H) : ℂ :=
  Bplus ch.W ch.M (colFn ch a) (liftT ch.W M (oppPath t D.R.m) (oppTens ch.W t τi τ) (formTop ch t y))

def GrpAt : Prop := ∀ j ∈ idx D, Split (GinfC _) (GfC _) (rowGrp ch.G j) (latGrp ch.G j)

def LinAt : Prop := ∀ t a τ, IsFlipFin t ch.S.B ch.rm (ch.Phi a) τ → ∀ M : Vol ch.G, M.Is t → ∀ τi y,
  lhs ch t M τi τ a y = τi.sum fun P c => c * lhs ch t M (Finsupp.single P 1) τ a y

def IterAt : Prop :=
  ∃ (ρ : ∀ j, Measure (rowGrp ch.G j)) (μ : ∀ j, Measure (GA D (ch.G.V (.grid D.R.m j)))),
    (∀ j ∈ idx D, (ρ j).IsHaarMeasure ∧ (μ j).IsHaarMeasure) ∧
    ∀ t a τ, IsFlipFin t ch.S.B ch.rm (ch.Phi a) τ → ∀ (M : Vol ch.G) (hM : M.Is t) P y,
      NIter ρ μ (tot ch.W hM P τ (colFn ch a) (formTop ch t y)) (idx D) 1 (lhs ch t M (Finsupp.single P 1) τ a y)

def InvAt : Prop := ∀ t a τ, IsFlipFin t ch.S.B ch.rm (ch.Phi a) τ → ∀ (M : Vol ch.G) (hM : M.Is t) P y,
  BiInv (rowGrp ch.G) (latGrp ch.G) (idx D) (tot ch.W hM P τ (colFn ch a) (formTop ch t y))

def RepAt (s : ℤˣ) : Prop := ∀ t, (∀ β, ∃ b, IsRep t ch.S.B s β b) ∧ ∀ β β' b b', IsRep t ch.S.B s β b → IsRep t ch.S.B s β' b' →
  InCells (fun _ => GinfC _) (rowGrp ch.G) (latGrp ch.G) (idx D) b b' → β = β'

def SuppOn (s : ℤˣ) : Prop := ∀ t a τ, IsFlipFin t ch.S.B ch.rm (ch.Phi a) τ → ∀ (M : Vol ch.G) (hM : M.Is t) P y
  (b : CosFam ch.G t → Pts ch.G), (∀ β, IsRep t ch.S.B s β (b β)) → ∀ h, (∀ j, j ∉ idx D → h j = 1) →
  tot ch.W hM P τ (colFn ch a) (formTop ch t y) h ≠ 0 →
    ∃ β ∈ ch.S.supp t (ch.Phi a), InCells (fun _ => GinfC _) (rowGrp ch.G) (latGrp ch.G) (idx D) (b β) h

def ValAt (s : ℤˣ) : Prop :=
  ∃ z : T → ℂˣ, (∀ t, z t ∈ xiVals R.toLevCh t) ∧
    ∀ (ρ : ∀ j, Measure ((rowGrp ch.G j).subgroupOf (GfC _))) (μ : ∀ j, Measure (GfC (ch.G.V (.grid D.R.m j)))),
      (∀ j ∈ idx D, (ρ j).IsHaarMeasure ∧ (μ j).IsHaarMeasure) → ∀ P (p : Pts ch.G), IsRealPt p →
      ∃ σ : PolCol ch.G × PolRow ch.G →₀ ℂ, ∀ t a τ, IsFlipFin t ch.S.B ch.rm (ch.Phi a) τ → ∀ (M : Vol ch.G) (hM : M.Is t),
        ∀ β ∈ ch.S.supp t (ch.Phi a), ∀ b, IsRep t ch.S.B s β b → ∀ M' τ', IsTermVol t ch.S.toGridChoice (ch.Phi a) β M' →
          ch.S.IsExpansion t (ch.Phi a) β τ' → ∀ y,
          wt ρ μ b * tot ch.W hM P τ (colFn ch a) (formTop ch t y) (p * b) =
            (z t : ℂ)⁻¹ * ((∏ w, ((ch.S.term t (ch.Phi a) β w).coef : ℂ)) *
              defTot t ch.S.toGridChoice M' σ τ' (colFn ch a) (formTop ch t y))

def FlatAt (s : ℤˣ) : Prop :=
  ∃ z : T → ℂˣ, (∀ t, z t ∈ xiVals R.toLevCh t) ∧ ∀ (P : PolDown ch.G) (p : Pts ch.G), IsRealPt p →
    ∃ C, IsRealFam ch.W C ∧ ∀ t Φ τ, IsFlipFin t ch.S.B ch.rm Φ τ → ∀ (M : Vol ch.G) (hM : M.Is t) β b, IsRep t ch.S.B s β b →
      ∀ τ' c, ch.S.IsExpansion t Φ β τ' → IsCombs ch.W τ' c → ∃ ζ : ℂ, (Stair t β → ζ = (z t : ℂ)⁻¹) ∧ ∀ u y,
        (τ.sum fun d x => x * evT (conAt ch.W hM (fockD ch.W t d.2 P) (p * b)) d.1 u y) =
          ζ * τ'.sum fun d x => x * evT (combC ch.W (c d) C) (combR ch.rm (c d)) u y

def LocAt (s : ℤˣ) : Prop :=
  ∃ (κ : ℂ) (z : T → ℂˣ), (∀ t, z t ∈ xiVals R.toLevCh t) ∧ ∀ t Φ τ, IsFlipFin t ch.S.B ch.rm Φ τ →
    ∀ (M : Vol ch.G) (hM : M.Is t) β b b₀, IsRep t ch.S.B s β b → IsBase t ch.S.B b₀ →
      ∀ τ' c, ch.S.IsExpansion t Φ β τ' → IsCombs ch.W τ' c → ∃ ζ : ℂ, (Stair t β → ζ = κ * (z t : ℂ)⁻¹) ∧
        ∀ (P : PolDown ch.G) (p : Pts ch.G), IsRealPt p → ∀ u y,
        (τ.sum fun d x => x * evT (conAt ch.W hM (fockD ch.W t d.2 P) (p * b)) d.1 u y) =
          ζ * τ'.sum fun d x => x * evT (combC ch.W (c d)
            (conAt ch.W hM (fockD ch.W t (fun j => ch.rm.vT D.R.m j) P) (p * b₀))) (combR ch.rm (c d)) u y

def VacAt : Prop :=
  (∀ t, ∃ b₀, IsBase t ch.S.B b₀) ∧ ∃ z : T → ℕ → ℂˣ, (∀ t j, z t j ∈ xiVals R.toLevCh t) ∧
    ∀ (P : PolDown ch.G) (p : Pts ch.G), IsRealPt p → ∃ C, IsRealFam ch.W C ∧ ∀ t (M : Vol ch.G) (hM : M.Is t) b₀,
      IsBase t ch.S.B b₀ → ∀ j, Even j → j < D.R.m →
        conAt ch.W hM (fockD ch.W t (fun j => ch.rm.vT D.R.m j) P) (p * b₀) j = (z t j : ℂ) • C j

def TensAt : Prop := ∀ t (M : Vol ch.G), IsHaarDef M → ∀ φ F, GlobalTheory.Unf.IsContAut _ φ → GlobalTheory.Unf.IsContAut _ F →
  ∀ (I : Type) (S : Finset I) (x : I → ℂ) (C : I → BiFam ch.G) (f : I → SchRow ch.G), (∀ i ∈ S, Good ch.W (C i) (f i)) →
    (∀ u y, ∑ i ∈ S, x i * evT (C i) (f i) u y = 0) → ∀ P, ∑ i ∈ S, x i * per ch.W M t (C i) (f i) P φ F = 0

def VolAt : Prop := ∀ t (M M' : Vol ch.G) s, IsHaarDef M → IsHaarDef M' → Scales M M' s → ∀ φ F, GlobalTheory.Unf.IsContAut _ φ →
  GlobalTheory.Unf.IsContAut _ F → ∀ C f, Good ch.W C f → ∀ P, per ch.W M t C f P φ F = sProd D s * per ch.W M' t C f P φ F

def WtAt (s : ℤˣ) : Prop :=
  ∀ (ρ : ∀ j, Measure ((rowGrp ch.G j).subgroupOf (GfC _))) (μ : ∀ j, Measure (GfC (ch.G.V (.grid D.R.m j)))),
    (∀ j ∈ idx D, (ρ j).IsHaarMeasure ∧ (μ j).IsHaarMeasure) → ∃ c : ℂ, ∀ t Φ β b, IsRep t ch.S.B s β b →
      ∀ M M' : Vol ch.G, M.Is t → IsTermVol t ch.S.toGridChoice Φ β M' →
        ∃ x, Scales M M' x ∧ wt ρ μ b * sProd D x = c * ∏ w, ((ch.S.term t Φ β w).coef : ℂ)

def FockAt : Prop :=
  ∃ z : T → ℂˣ, (∀ t, z t ∈ xiVals R.toLevCh t) ∧ ∀ C, IsRealFam ch.W C → ∀ P : PolRow ch.G,
    ∃ σ : PolCol ch.G × PolRow ch.G →₀ ℂ, ∀ t a β (M : Vol ch.G), IsHaarDef M → ch.S.SumOK t (ch.Phi a) → ∀ τ c,
      ch.S.IsExpansion t (ch.Phi a) β τ → IsCombs ch.W τ c → ∀ y,
      (τ.sum fun d x => x * per ch.W M t (combC ch.W (c d) C) (combR ch.rm (c d)) P (colFn ch a) (formTop ch t y)) =
        (z t : ℂ)⁻¹ * defTot t ch.S.toGridChoice M σ τ (colFn ch a) (formTop ch t y)

def BasicAt : Prop :=
  (∀ a, GlobalTheory.Unf.IsContAut _ (colFn ch a)) ∧ (∀ t y, GlobalTheory.Unf.IsContAut _ (formTop ch t y)) ∧
  (∀ t (M : Vol ch.G), M.Is t → IsHaarDef M) ∧ (∀ t Φ β M, IsTermVol t ch.S.toGridChoice Φ β M → IsHaarDef M) ∧
  (∀ t Φ τ, IsFlipFin t ch.S.B ch.rm Φ τ → ∀ (M : Vol ch.G) (hM : M.Is t), ∀ d ∈ τ.support, ∀ P h,
    Good ch.W (conAt ch.W hM (fockD ch.W t d.2 P) h) d.1) ∧
  (∀ C, IsRealFam ch.W C → ∀ c : Combs ch.G, (∀ j, j < D.R.m → IsFinComb (c.1 j)) → Good ch.W (combC ch.W c C) (combR ch.rm c)) ∧
  ∀ t Φ β τ, ch.S.IsExpansion t Φ β τ → ∃ c, IsCombs ch.W τ c

def OneAt : Prop := ∀ t Φ, ∀ β ∈ ch.S.supp t Φ, Stair t β

def OffAt : Prop := ∀ t Φ τ, IsFlipFin t ch.S.B ch.rm Φ τ → ∀ (M : Vol ch.G) (hM : M.Is t), ∀ d ∈ τ.support, ∀ P (h : Pts ch.G),
  h 0 = 1 → (∀ j, Even j → j < D.R.m → conAt ch.W hM (fockD ch.W t d.2 P) h j ≠ 0) → ∀ j ∈ idx D, ∀ hj : j ≤ D.R.m,
    ∃ r ∈ rowGrp ch.G j, ∃ a ∈ GinfC _, ∃ δ x g, IsTilt ch.G j δ ∧ HasLoc t ch.S.B hj x g ∧ ∃ k ∈ latGrp ch.G j,
      h j = r * a * (δ * x) * k

end

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R)

def ConLin : Prop := ∀ t (M : Vol ch.G) (hM : M.Is t) P h (I : Type) (S : Finset I) (x : I → ℂ) (f : I → SchRow ch.G)
  (Φ : I → SchDown ch.G t), (∀ i ∈ S, ∀ j, IsThetaFunO ch.W.ψ _ _ (Φ i j)) →
  (∀ (y : RowPt ch.G) (v : ∀ j : Fin D.R.m, WO (ch.G.V (.grid D.R.m j)) (ch.G.V (.grid D.R.m (j + 1)))),
    ∑ i ∈ S, x i * ((∏ n, f i n (y n)) * ∏ j, Φ i j (v j)) = 0) →
  ∀ u y, ∑ i ∈ S, x i * evT (conAt ch.W hM (fockD ch.W t (Φ i) P) h) (f i) u y = 0

def KFix : Prop := ∀ t Φ τ, IsFlipFin t ch.S.B ch.rm Φ τ → ∀ j ∈ idx D, ∀ k ∈ latGrp ch.G j,
  ∀ (y : RowPt ch.G) (v : ∀ j : Fin D.R.m, WO (ch.G.V (.grid D.R.m j)) (ch.G.V (.grid D.R.m (j + 1)))),
    (τ.sum fun d x => x * ((∏ n, d.1 n (y n)) * ∏ i : Fin D.R.m, ch.W.om (.mu t D.R.m i)
      ((Pi.mulSingle j k : Pts ch.G) i, (Pi.mulSingle j k : Pts ch.G) (i + 1)) (d.2 i) (v i))) =
    τ.sum fun d x => x * ((∏ n, d.1 n (y n)) * ∏ i, d.2 i (v i))

def RInv : Prop := ∀ t (M : Vol ch.G) (hM : M.Is t) (Φ : SchDown ch.G t) (f : SchRow ch.G), (∀ j, IsThetaFunO ch.W.ψ _ _ (Φ j)) →
  (∀ i, IsThetaFunO ch.W.ψ _ _ (f i)) → ∀ P φ F, GlobalTheory.Unf.IsContAut _ φ → GlobalTheory.Unf.IsContAut _ F → ∀ j ∈ idx D, ∀ r ∈ rowGrp ch.G j,
    ∀ h, per ch.W M t (conAt ch.W hM Φ (Function.update h j (r * h j))) f P φ F = per ch.W M t (conAt ch.W hM Φ h) f P φ F

def RealEqAt : Prop := ∀ t t' j, j < D.R.m →
  (∀ a ∈ GinfC _, ∀ b ∈ GinfC _, ∀ f, IsThetaFunO ch.W.ψ _ _ f → ch.W.om (.top t j) (a, b) f = ch.W.om (.top t' j) (a, b) f) ∧
  ∀ a ∈ GinfC _, ∀ b ∈ GinfC _, ∀ f, IsThetaFunO ch.W.ψ _ _ f →
    ch.W.om (.mu t D.R.m j) (a, b) f = ch.W.om (.mu t' D.R.m j) (a, b) f

def IsColVac (v : ∀ j : ℕ, WO (ch.G.V (.top j)) (ch.G.V (.top (j + 1))) → ℂ) : Prop :=
  ∀ t j, j < D.R.m → ch.W.IsVac (.top t j) (v j)

def MovedAt : Prop :=
  ∃ v, IsColVac ch v ∧ ∃ (κ κ' : ℕ → ℂˣ) (z : T → ℕ → ℂˣ), (∀ t j, z t j ∈ xiVals R.toLevCh t) ∧
    ∀ t a β τ c, ch.S.SumOK t (ch.Phi a) → ch.S.IsExpansion t (ch.Phi a) β τ → IsCombs ch.W τ c → ∀ d ∈ τ.support,
      (∀ j : Fin D.R.m, movedVec t ch.S.toGridChoice (d.1 j) = ((κ j * z t j : ℂˣ) : ℂ) • comb ch.W.ψ _ _ ((c d).1 j) (v j)) ∧
      ∀ i : Fin D.R.m, movedVec t ch.S.toGridChoice (d.2 i) = (κ' i : ℂ) • combR ch.rm (c d) i

def ColFock : Prop := ∀ v, IsColVac ch v → ∀ C, IsRealFam ch.W C → ∃ σ : PolCol ch.G →₀ ℂ, ∀ t (M : Vol ch.G), IsHaarDef M →
  ∀ a (c : Combs ch.G), (∀ j, j < D.R.m → IsFinComb (c.1 j)) → ∀ F, GlobalTheory.Unf.IsContAut _ F →
    jPer ch.W M t (combC ch.W c C) F ((D.R.m - 2) / 2) 0 top_idx (colFn ch a) = σ.sum fun Q x => x *
      ∫ h in M.fd (.grid D.R.m D.R.m), liftP ch.W M (colPath t D.R.m) (colFam t D.R.m fun j =>
        ch.W.fock (.top t j) (comb ch.W.ψ _ _ (c.1 j) (v j)) (Q j)) (colFn ch a) (stabilizerEmbedding ch.G.sp.topDec h) * F h
        ∂M.ν (.grid D.R.m D.R.m)

open GlobalTheory.FinPl in

def ShapeAt : Prop :=
  ∃ (N : ∀ j, Lat (ch.G.V (.grid D.R.m j))) (N₀ : ∀ j, Lat (GlobalTheory.Doubling.hsum (ch.G.V (.top j)) (GlobalTheory.SeeSaw.Model.nLine D)))
    (LL : ℕ → Lat (GlobalTheory.SeeSaw.Model.nLine D)) (LZ : Lat (pLine D)),
    (∀ t b, IsBase t ch.S.B b → ∀ j, j ≤ D.R.m → Moves _ (b j) (ch.G.Λ (.grid D.R.m j)) (N j) fun _ => True) ∧
    IsSelfDualC _ LZ ∧ (∀ v, OrthAt (topOrth ch.G) (ch.G.Λ (.top D.R.m)) (ch.G.Λ (.grid D.R.m D.R.m)) LZ v) ∧
    ∀ t (M : Vol ch.G) (hM : M.Is t) j σ (hj : j + 2 * σ + 2 = D.R.m) vN (v : GlobalTheory.FinPl.Pl D),
      IsSelfDualC _ (LL j) ∧ OrthAt (besAt ch.G hM j σ hj vN).o (N₀ j) (ch.G.Λ (.top j)) (LL j) v ∧
      GoodBF ch.W.ψ (besAt ch.G hM j σ hj vN) (jacAt ch.G hM (j + 1) σ (by omega)) (N j) (N₀ j) (N (j + 1)) (ch.G.Λ (.top (j + 1))) v ∧
      (∀ i (hi : i + 1 = j), ∀ hi' : i + 2 * (σ + 1) + 1 = D.R.m, AdaptFB ch.W.ψ (jacAt ch.G hM i (σ + 1) hi')
        (besAt ch.G hM (i + 1) σ (by omega) (GlobalTheory.Unf.Inhab.nonempty_volN _).some) (N i) (ch.G.Λ (.top i)) (N (i + 1)) (N₀ (i + 1)) v) ∧
      (σ = 0 → ∀ w ∈ latO (ch.G.V (.top (j + 1))) (pLine D) (ch.G.Λ (.top (j + 1)) : Set _) (LZ : Set _) (· = v),
        kap lastTau _ w ∈ latO (GlobalTheory.SeeSaw.Model.nLine D) (ch.G.V (.top (j + 1))) (LL j : Set _) (ch.G.Λ (.top (j + 1)) : Set _) (· = v)) ∧
      ((∀ w ∈ locPl ch.G t, w.under (𝓞 D.host.F) ≠ v) → ∀ i, i < D.R.m →
        GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D (ch.G.chrS (.mu t D.R.m i)) v ∧ GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D (ch.G.chrT (.mu t D.R.m i)) v)

def VacReal : Prop := ∀ t (M : Vol ch.G) (hM : M.Is t) b, IsBase t ch.S.B b → ∀ (P : PolDown ch.G) (p : Pts ch.G), IsRealPt p →
  IsRealFam ch.W (conAt ch.W hM (fockD ch.W t (fun j => ch.rm.vT D.R.m j) P) (p * b))

def VacTw : Prop := (∀ t, ∃ b, IsBase t ch.S.B b) ∧ ∃ z : T → ℕ → ℂˣ, (∀ t j, z t j ∈ xiVals R.toLevCh t) ∧
  ∀ t t' (M M' : Vol ch.G) (hM : M.Is t) (hM' : M'.Is t') b b', IsBase t ch.S.B b → IsBase t' ch.S.B b' →
    ∀ (P : PolDown ch.G) (p : Pts ch.G), IsRealPt p → ∀ j, Even j → j < D.R.m →
      (z t' j : ℂ) • conAt ch.W hM (fockD ch.W t (fun j => ch.rm.vT D.R.m j) P) (p * b) j =
        (z t j : ℂ) • conAt ch.W hM' (fockD ch.W t' (fun j => ch.rm.vT D.R.m j) P) (p * b') j

def CoverAt (s : ℤˣ) : Prop := ∀ t (b : CosFam ch.G t → Pts ch.G), (∀ β, IsRep t ch.S.B s β (b β)) → ∀ h : Pts ch.G,
  (∀ j ∈ idx D, ∀ hj : j ≤ D.R.m, ∃ r ∈ rowGrp ch.G j, ∃ a ∈ GinfC _, ∃ δ x g, IsTilt ch.G j δ ∧ HasLoc t ch.S.B hj x g ∧
    ∃ k ∈ latGrp ch.G j, h j = r * a * (δ * x) * k) →
  ∃ β, InCells (fun _ => GinfC _) (rowGrp ch.G) (latGrp ch.G) (idx D) (b β) h

variable {ch} in

def OneLoc (t : T) (w : Pl D.host.E) (e : AE D) (r : Pts ch.G)
    (g : ∀ j, GL (Fin ((locGrid ch.G t w).rank (D.R.m, j))) (Kw w)) : Prop :=
  ∀ j (hj : j ≤ D.R.m), SuppAt e _ (r j) ∧ inBasis (rank_vertex ch.G t w (X := (D.R.m, j)) ⟨le_rfl, hj⟩) (ch.S.B.β D.R.m j) w
    (Lev.finE (ch.G.V (.grid D.R.m j)) (r j)) = g j

open Classical in

def PlaceAt (s : ℤˣ) : Prop :=
  ∃ (κ : Pl D.host.E → ℂ) (z : T → Pl D.host.E → ℂˣ), (∀ t w, z t w ∈ xiVals R.toLevCh t) ∧ (∀ w, w ∉ ch.G.pl.W0 → κ w = 1) ∧
    ∀ t, ∀ w ∈ locPl ch.G t, ∀ β : Cosets (G := locGrid ch.G t w) one_le_sLen (givenLevel ch.G t w), ∃ ζ : ℂ,
      ((w ∈ ch.G.pl.W0 → ∀ i, β i = DoubleCoset.mk _ _ (stair (locGrid ch.G t w) (unifAt w) (cosExp ch.G w) (i + 1))) →
        ζ = κ w * (z t w : ℂ)⁻¹) ∧
      ∀ e, IsIdemSum e {w} → ∀ (M : Vol ch.G) (hM : M.Is t) (r r₀ h : Pts ch.G),
        OneLoc t w e r (fun j => if j ∈ idx D then sgnAt ch.G t s w j * (repsAt ch.G t w).elt β (D.R.m, j) else 1) →
        OneLoc t w e r₀ (fun j => if j = 0 then (stair (locGrid ch.G t w) (unifAt w) (cosExp ch.G w) j)⁻¹ else 1) →
        (∀ j, j ≤ D.R.m → ∃ δ, IsTilt ch.G j δ ∧ δ⁻¹ * h j ∈ GlobalTheory.FinPl.grpOff _ (· = w.under (𝓞 D.host.F))) →
        ∀ (φ : ∀ b : GlobalTheory.SplitFlip.Edge, Matrix (Fin ((locGrid ch.G t w).rank b.tgt)) (Fin ((locGrid ch.G t w).rank b.src)) (Kw w) → ℂ),
          (∀ i j x, φ (.ex i j) x = 1) → ∀ v f : SchDown ch.G t, (∀ j, IsThetaFunO ch.W.ψ _ _ (v j)) →
          (∀ j : Fin D.R.m, IsLocVec ch.W (.mu t D.R.m j) e (v j) (fun y => if IsHalf e y then φ (.theta D.R.m j)
            (ch.S.B.coord t w (X := (D.R.m, j + 1)) (Y := (D.R.m, j)) ⟨le_rfl, j.2⟩ ⟨le_rfl, j.2.le⟩
              (y.map fun a => cpt w (toEAf D a))) else 0) (f j)) →
          ∀ (I : Type) (S : Finset I) (x : I → ℂ) (d : I → ∀ j : Fin D.R.m, FinDatum ch.G t (.top t j)) (c : I → Combs ch.G),
            (∀ i ∈ S, ∀ j : Fin D.R.m, (d i j).e = e ∧ IsCombOf ch.W (d i j) ((c i).1 j)) →
            (∀ y : ∀ j : Fin D.R.m, WO (ch.G.V (.top j)) (ch.G.V (.top (j + 1))), (∀ j, IsHalf e (y j)) →
              ∑ i ∈ S, x i * ∏ j, (d i j).fn (y j) = flatTensor one_le_sLen (psiAt ch.W w) (unitVol w)
                (moved (locGrid ch.G t w) (keepAt ch.G w) ((repsAt ch.G t w).elt β)
                  ((locGrid ch.G t w).lines₂ (GlobalTheory.SplitFlip.oppositePath D.R.m) φ)) (ch.S.toGridChoice.colAt t w y) 0) →
            ∀ u, evT (conAt ch.W hM f (h * r)) 1 u 0 = ζ * ∑ i ∈ S, x i * evT (combC ch.W (c i) (conAt ch.W hM v (h * r₀))) 1 u 0

end GlobalTheory.RowVal

end
