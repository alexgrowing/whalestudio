import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterIdeleCharacterMatchUnique
import Formalism.LocalToGlobal.IndefiniteReal.HeckeNonvanishing.Imports
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx

noncomputable section

namespace GlobalTheory.RowEx.CarryTr

open GlobalTheory.Mem

theorem lat_eq_of_sd {D : D7} {V : HSp D} {β β' : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)}
    {Λ Λ' : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} (h : Formalism.IndefR.Links.IsSDFrame V β Λ 1)
    (h' : Formalism.IndefR.Links.IsSDFrame V β' Λ' 1) : Λ = Λ' := by
  obtain ⟨c, -, -, -, h1, h2⟩ := h
  obtain ⟨c', -, -, -, h1', h2'⟩ := h'
  ext x
  constructor
  · intro hx; simpa using h1' x (by simpa using h2 x hx)
  · intro hx; simpa using h1 x (by simpa using h2' x hx)

def trGL {D : D7} {R : Type} [Semiring R] {V V' : HSp D} (e : V' = V) (β : GL (Fin V.rank) R) : GL (Fin V'.rank) R :=
  e ▸ β

theorem trGL_heq {D : D7} {R : Type} [Semiring R] {V V' : HSp D} (e : V' = V) (β : GL (Fin V.rank) R) :
    HEq (trGL e β) β := by
  subst e; rfl

theorem isFrame_tr {D : D7} {V V' : HSp D} (e : V' = V) {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}
    {Λ' : Submodule (𝓞 D.host.E) (Fin V'.rank → D.host.E)} (hΛ : HEq Λ' Λ) {β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)}
    (h : IsFrame β Λ) : IsFrame (trGL e β) Λ' := by
  subst e; cases hΛ; exact h

open Matrix in

theorem uLat_tr {D : D7} {V V' : HSp D} (e : V' = V) {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}
    {Λ' : Submodule (𝓞 D.host.E) (Fin V'.rank → D.host.E)} (hΛ : HEq Λ' Λ) {f : GL (Fin V.rank) D.host.E}
    {f' : GL (Fin V'.rank) D.host.E} (hf : HEq f' f) {u : GfC V} {u' : GfC V'} (hu : HEq u' u)
    (h : ∀ v, v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat f) ↔
      (Formalism.IndefR.Lev.finE V u.1).1 *ᵥ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ) :
    ∀ v, v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat f') ↔
      (Formalism.IndefR.Lev.finE V' u'.1).1 *ᵥ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ' := by
  subst e; cases hΛ; cases hf; cases hu; exact h

def trU {D : D7} {V V' : HSp D} (e : V' = V) (x : GfC V) : GfC V' := e ▸ x

theorem trU_heq {D : D7} {V V' : HSp D} (e : V' = V) (x : GfC V) : HEq (trU e x) x := by
  subst e; rfl

theorem frOn_tr {D : D7} {V V' : HSp D} (e : V' = V) {f : GL (Fin V.rank) D.host.E} {f' : GL (Fin V'.rank) D.host.E}
    (hf : HEq f' f) (h : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) f.1 * V.gram * f.1 = 1) :
    Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) f'.1 * V'.gram * f'.1 = 1 := by
  subst e; cases hf; exact h

theorem uSupp_tr {D : D7} {V V' : HSp D} (e : V' = V) {u : GfC V} {u' : GfC V'} (hu : HEq u' u) {S : Finset ℕ}
    (h : ∃ (P : Finset (Pl D.host.E)) (e : AE D), IsIdemSum e P ∧ SuppAt e V u.1 ∧ ∀ w ∈ P, Off S w) :
    ∃ (P : Finset (Pl D.host.E)) (e : AE D), IsIdemSum e P ∧ SuppAt e V' u'.1 ∧ ∀ w ∈ P, Off S w := by
  subst e; cases hu; exact h

open Matrix in

theorem top_tr {D : D7} {A A' B B' : HSp D} (eA : A' = A) (eB : B' = B) {ι : A.V →ₗ[D.host.E] B.V}
    {ι' : A'.V →ₗ[D.host.E] B'.V} (hι : HEq ι' ι) {a : Matrix (Fin B.rank) (Fin 1) D.host.E}
    {a' : Matrix (Fin B'.rank) (Fin 1) D.host.E} (ha : HEq a' a) (r : A.rank + 1 = B.rank) (r' : A'.rank + 1 = B'.rank)
    {fA : GL (Fin A.rank) D.host.E} {fA' : GL (Fin A'.rank) D.host.E} (hfA : HEq fA' fA)
    {fB : GL (Fin B.rank) D.host.E} {fB' : GL (Fin B'.rank) D.host.E} (hfB : HEq fB' fB)
    {uA : GfC A} {uA' : GfC A'} (huA : HEq uA' uA) {uB : GfC B} {uB' : GfC B'} (huB : HEq uB' uB)
    (h1 : ∀ i (k : Fin A.rank), fB.1 i (Formalism.L2.Col.Br.iC r.symm k) = (frameMat _ _ ι * fA.1) i k)
    (h2 : ∀ i, fB.1 i (Formalism.L2.Col.Br.iL r.symm) = a i 0)
    (h3 : HMul.hMul (mt B uB.1) ((frameMat _ _ ι).map (incA D)) = HMul.hMul ((frameMat _ _ ι).map (incA D)) (mt A uA.1))
    (h4 : mt B uB.1 *ᵥ (fun i => incA D (a i 0)) = fun i => incA D (a i 0)) :
    (∀ i (k : Fin A'.rank), fB'.1 i (Formalism.L2.Col.Br.iC r'.symm k) = (frameMat _ _ ι' * fA'.1) i k) ∧
    (∀ i, fB'.1 i (Formalism.L2.Col.Br.iL r'.symm) = a' i 0) ∧
    HMul.hMul (mt B' uB'.1) ((frameMat _ _ ι').map (incA D)) = HMul.hMul ((frameMat _ _ ι').map (incA D)) (mt A' uA'.1) ∧
    mt B' uB'.1 *ᵥ (fun i => incA D (a' i 0)) = fun i => incA D (a' i 0) := by
  subst eA eB
  cases hι; cases ha; cases hfA; cases hfB; cases huA; cases huB
  exact ⟨h1, h2, h3, h4⟩

abbrev dOf {D : D7} {T : Type} (_ : LevCh D T) : D7 := D

open Matrix in

theorem sumFrame_tr {D : D7} {A A' B B' : HSp D} (eA : A' = A) (eB : B' = B) {c : ℕ} {ι : A.V →ₗ[D.host.E] B.V}
    {ι' : A'.V →ₗ[D.host.E] B'.V} (hι : HEq ι' ι) {a : Matrix (Fin B.rank) (Fin c) D.host.E}
    {a' : Matrix (Fin B'.rank) (Fin c) D.host.E} (ha : HEq a' a) (r : A.rank + c = B.rank) (r' : A'.rank + c = B'.rank)
    {w : Pl D.host.E} {β : GL (Fin A.rank) (Formalism.IndefR.Lev.EAf D)} {β' : GL (Fin A'.rank) (Formalism.IndefR.Lev.EAf D)} (hβ : HEq β' β)
    {γ : GL (Fin B.rank) (Formalism.IndefR.Lev.EAf D)} {γ' : GL (Fin B'.rank) (Formalism.IndefR.Lev.EAf D)} (hγ : HEq γ' γ)
    {u : Fin c → Kw w}
    (h : (GlobalTheory.StdFrames.loc w γ).val.submatrix id (GlobalTheory.FunObj.frame r) = fromCols ((frameMat B A ι).map (algebraMap D.host.E (Kw w)) * (GlobalTheory.StdFrames.loc w β).val)
      (a.map (algebraMap D.host.E (Kw w)) * diagonal u)) :
    (GlobalTheory.StdFrames.loc w γ').val.submatrix id (GlobalTheory.FunObj.frame r') = fromCols ((frameMat B' A' ι').map (algebraMap D.host.E (Kw w)) * (GlobalTheory.StdFrames.loc w β').val)
      (a'.map (algebraMap D.host.E (Kw w)) * diagonal u) := by
  subst eA eB
  cases hι; cases ha; cases hβ; cases hγ; exact h

theorem isFrame_tr' {D : D7} {V V' : HSp D} (e : V' = V) {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}
    {Λ' : Submodule (𝓞 D.host.E) (Fin V'.rank → D.host.E)} (hΛ : HEq Λ' Λ) {β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)}
    {β' : GL (Fin V'.rank) (Formalism.IndefR.Lev.EAf D)} (hβ : HEq β' β) (h : IsFrame β Λ) : IsFrame β' Λ' := by
  subst e; cases hΛ; cases hβ; exact h

theorem val_heq {D : D7} {V V' : HSp D} (e : V' = V) {u : GfC V} {u' : GfC V'} (h : HEq u' u) : HEq u'.1 u.1 := by
  subst e; cases h; rfl

def trFun {α : Sort _} {F : α → Sort _} {a a' : α} (e : a' = a) (x : F a) : F a' := e ▸ x

theorem trFun_heq {α : Sort _} {F : α → Sort _} {a a' : α} (e : a' = a) (x : F a) : HEq (trFun (F := F) e x) x := by
  subst e; rfl

theorem neg_heq {D : D7} {V V' : HSp D} (e : V' = V) {c : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ}
    {c' : D.what₂.Tau → Matrix (Fin V'.rank) (Fin V'.rank) ℂ} (h : HEq c' c) : HEq (fun τ => -c' τ) (fun τ => -c τ) := by
  subst e; cases h; rfl

theorem colLat_heq {D : D7} {V V' : HSp D} (e : V' = V) {f : GL (Fin V.rank) D.host.E} {f' : GL (Fin V'.rank) D.host.E}
    (h : HEq f' f) : HEq ((colLat f' : Submodule (𝓞 D.host.E) (Fin V'.rank → D.host.E)) : Set (Fin V'.rank → D.host.E))
      ((colLat f : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) : Set (Fin V.rank → D.host.E)) := by
  subst e; cases h; rfl

theorem frC_heq {D : D7} {V V' : HSp D} (e : V' = V) {f : GL (Fin V.rank) D.host.E} {f' : GL (Fin V'.rank) D.host.E}
    (h : HEq f' f) : HEq (fun τ : D.what₂.Tau => (f'.1).map (tauE D τ)) (fun τ : D.what₂.Tau => (f.1).map (tauE D τ)) := by
  subst e; cases h; rfl

theorem oddGenerator_condition_of_rank_eq_heq {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ t0 : ℂ} {n n' k k' : ℕ} (en : n' = n) (ek : k' = k)
    {e : Formalism.MainNotions.TaylorLogMetric.VC D n k → ℂ} {e' : Formalism.MainNotions.TaylorLogMetric.VC D n' k' → ℂ} (he : HEq e' e)
    (h : Formalism.MainNotions.StandardLatticesGL3.oddE0 D cc δ t0 n k e) : Formalism.MainNotions.StandardLatticesGL3.oddE0 D cc δ t0 n' k' e' := by
  subst en ek; cases he; exact h

theorem vac_tr {D : D7} {ψ ψ' : AddChar (AF D.host.F) ℂ} (eψ : ψ' = ψ) {θ θ' : Formalism.IndefR.Datum.InfFam D} (eθ : θ' = θ)
    {S S' T T' : HSp D} (eS : S' = S) (eT : T' = T)
    {cS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ} {cS' : D.what₂.Tau → Matrix (Fin S'.rank) (Fin S'.rank) ℂ} (hcS : HEq cS' cS)
    {cT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ} {cT' : D.what₂.Tau → Matrix (Fin T'.rank) (Fin T'.rank) ℂ} (hcT : HEq cT' cT)
    {ΛS : Set (Fin S.rank → D.host.E)} {ΛS' : Set (Fin S'.rank → D.host.E)} (hΛS : HEq ΛS' ΛS)
    {ΛT : Set (Fin T.rank → D.host.E)} {ΛT' : Set (Fin T'.rank → D.host.E)} (hΛT : HEq ΛT' ΛT)
    {f : Formalism.IndefR.Datum.WO S T → ℂ} {f' : Formalism.IndefR.Datum.WO S' T' → ℂ} (hf : HEq f' f)
    (h : Formalism.IndefR.Datum.IsVacO ψ θ S T cS cT ΛS ΛT f) : Formalism.IndefR.Datum.IsVacO ψ' θ' S' T' cS' cT' ΛS' ΛT' f' := by
  subst eψ eθ eS eT; cases hcS; cases hcT; cases hΛS; cases hΛT; cases hf; exact h

theorem fockVectorNormalisation_of_space_eq_heq {D : D7} {ψ ψ' : AddChar (AF D.host.F) ℂ} (eψ : ψ' = ψ) {θ θ' : Formalism.IndefR.Datum.InfFam D} (eθ : θ' = θ)
    {S S' T T' : HSp D} (eS : S' = S) (eT : T' = T)
    {cS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ} {cS' : D.what₂.Tau → Matrix (Fin S'.rank) (Fin S'.rank) ℂ} (hcS : HEq cS' cS)
    {cT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ} {cT' : D.what₂.Tau → Matrix (Fin T'.rank) (Fin T'.rank) ℂ} (hcT : HEq cT' cT)
    {bS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ} {bS' : D.what₂.Tau → Matrix (Fin S'.rank) (Fin S'.rank) ℂ} (hbS : HEq bS' bS)
    {bT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ} {bT' : D.what₂.Tau → Matrix (Fin T'.rank) (Fin T'.rank) ℂ} (hbT : HEq bT' bT)
    {f : Formalism.IndefR.Datum.WO S T → ℂ} {f' : Formalism.IndefR.Datum.WO S' T' → ℂ} (hf : HEq f' f)
    {e : Formalism.MainNotions.TaylorLogMetric.VC D S.rank T.rank → ℂ} {e' : Formalism.MainNotions.TaylorLogMetric.VC D S'.rank T'.rank → ℂ} (he : HEq e' e)
    (c : ℂˣ) (o : ℂ →+* ℂ) (δ : ℂ)
    (h : ∀ k : FVar D T.rank S.rank →₀ ℕ, pureTensorO ψ θ S T cS cT bS bT f (MvPolynomial.monomial k 1) 0 =
      c * o ((k.prod fun v n => period δ v.1 ^ n) * Formalism.MainNotions.GL3Theta.applyAt0 D (MvPolynomial.monomial k 1) e)) :
    ∀ k : FVar D T'.rank S'.rank →₀ ℕ, pureTensorO ψ' θ' S' T' cS' cT' bS' bT' f' (MvPolynomial.monomial k 1) 0 =
      c * o ((k.prod fun v n => period δ v.1 ^ n) * Formalism.MainNotions.GL3Theta.applyAt0 D (MvPolynomial.monomial k 1) e') := by
  subst eψ eθ eS eT; cases hcS; cases hcT; cases hbS; cases hbT; cases hf; cases he; exact h

theorem rk_eq {D : D7} {V V' : HSp D} (e : V' = V) : V'.rank = V.rank := by rw [e]

end GlobalTheory.RowEx.CarryTr

namespace GlobalTheory.RowEx

open GlobalTheory.Mem GlobalTheory.RowEx.CarryTr

set_option maxHeartbeats 4000000 in

theorem carryS : CarryS := by
  intro X X' T T' L L' μ₀ μ₀' ι hL sc G G' hG W W' hW S
  obtain ⟨m, hm⟩ : ∃ m, X.toD7.R.m = m := ⟨_, rfl⟩
  have h2m : 2 ≤ m := hm ▸ X.toD7.R.two_le_m
  obtain ⟨m', hm'⟩ : ∃ m', X'.toD7.R.m = m' := ⟨_, rfl⟩
  obtain ⟨B, C, Wr, V, Ss, N, Gj⟩ := X
  obtain ⟨B', C', Wr', V', Ss', N', Gj'⟩ := X'
  have h := hL.pre
  cases B
  cases B'
  dsimp only at h
  subst h
  have em : m = m' := hm.symm.trans hm'
  subst em
  have eQ : ∀ t, L'.Q t = L.Q (ι t) := fun t => eq_of_heq (hL.Q t)
  obtain ⟨f, f', hf, hC, hC'⟩ := hL.C
  have hf' : f' = f := eq_of_heq hf
  subst hf'
  have eMu0 : ∀ j, 1 ≤ j → j ≤ m → L'.mu0 j = L.mu0 j := by
    intro j h1 h2
    obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
    have hk : k < _ := Nat.lt_of_lt_of_le (Nat.lt_succ_self k) (h2.trans_eq hm.symm)
    have a := hL.is'.mu0 ⟨k, hk⟩
    have b := hL.is.mu0 ⟨k, hk⟩
    rw [hC'] at a
    rw [hC] at b
    exact GlobalTheory.ChrEqUnique.idc_unique _ _ _ _ a b
  have eXi : ∀ t, L'.xi t = L.xi (ι t) := fun t => by
    have a := hL.is'.xi t
    rw [eq_of_heq (hL.xi t)] at a
    exact GlobalTheory.ChrEqUnique.idc_unique _ _ _ _ a (hL.is.xi (ι t))
  have eMu : ∀ t j, 1 ≤ j → j ≤ m → L'.mu t j = L.mu (ι t) j := fun t j h1 h2 => by
    show L'.mu0 j * L'.xi t = L.mu0 j * L.xi (ι t)
    rw [eMu0 j h1 h2, eXi]; try rfl
  have ev0 : G'.pl.v0 = G.pl.v0 := eq_of_heq hG.v0
  have ew : G'.pl.w = G.pl.w := eq_of_heq hG.w
  have eS0 : G'.pl.S0 = G.pl.S0 := by unfold ChiGrid.Places.S0; rw [ev0]; rfl
  have eW0 : G'.pl.W0 = G.pl.W0 := by unfold ChiGrid.Places.W0; rw [eS0, ew]; try rfl
  have ecos : ∀ w, cosExp G' w = cosExp G w := fun w => by
    unfold cosExp ChiGrid.Places.depth; rw [eW0, ev0]; rfl
  have eloc : ∀ t, locPl G' t = locPl G (ι t) := fun t => by unfold locPl; rw [eW0, eQ]; try rfl

  have eΛX : L'.ΛX = L.ΛX := lat_eq_of_sd hL.is'.βX hL.is.βX
  have eV0 : G'.V (.grid 0 m) = G.V (.grid 0 m) :=
    hm ▸ (congrArg LSp.sp (colY_m L')).trans (congrArg LSp.sp (colY_m L)).symm
  have eΛ0 : HEq (G'.Λ (.grid 0 m)) (G.Λ (.grid 0 m)) :=
    hm ▸ ((congr_arg_heq LSp.lat (colY_m L')).trans (heq_of_eq eΛX)).trans (congr_arg_heq LSp.lat (colY_m L)).symm
  have eVd : ∀ Y, DefNode m Y → G'.V Y = G.V Y ∧ HEq (G'.Λ Y) (G.Λ Y) := by
    rintro (⟨_ | i, j⟩ | i | j) hY
    · obtain ⟨-, rfl⟩ := hY; exact ⟨eV0, eΛ0⟩
    · exact ⟨eq_of_heq (hG.grid i j).1, (hG.grid i j).2⟩
    · exact absurd hY id
    · exact ⟨eq_of_heq (hG.top j).1, (hG.top j).2⟩

  obtain ⟨k, hk⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩

  classical
  have eVs : ∀ i j, i ≠ 0 → (G'.sp.Vs i j).sp = (G.sp.Vs i j).sp := fun i j h => by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero h; exact eq_of_heq (hG.grid k j).1
  have eΛs : ∀ i j, i ≠ 0 → HEq (G'.sp.Vs i j).lat (G.sp.Vs i j).lat := fun i j h => by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero h; exact (hG.grid k j).2
  obtain ⟨B', hB'⟩ : ∃ B' : Frames G', ∀ i j, i ≠ 0 → HEq (B'.β i j) (S.B.β i j) := by
    refine ⟨⟨fun i j => if h : i = 0 then 1 else trGL (eVs i j h) (S.B.βs i j), fun i j h1 h2 h3 => ?_⟩, fun i j h => ?_⟩
    · have h0 : i ≠ 0 := by omega
      simp only [dif_neg h0]
      exact isFrame_tr _ (eΛs i j h0) (S.B.isFrame i j h1 (h2.trans_eq (hm.trans hm.symm)) (h3.trans_eq (hm.trans hm.symm)))
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero h
      dsimp only [Frames.β]
      rw [dif_neg h]
      exact trGL_heq _ _
  have eVt : ∀ j, G'.V (.top j) = G.V (.top j) := fun j => eq_of_heq (hG.top j).1

  have eVd' : ∀ Y, DefNode m Y → G'.V Y = G.V Y := fun Y h => (eVd Y h).1
  obtain ⟨fr', hfr⟩ : ∃ fr' : ∀ Y : Node, GL (Fin (G'.V Y).rank) _, ∀ Y, DefNode m Y → HEq (fr' Y) (S.N.fr Y) :=
    ⟨fun Y => if h : DefNode m Y then trGL (eVd' Y h) (S.N.fr Y) else 1, fun Y h => by
      simp only [dif_pos h]; exact trGL_heq _ _⟩
  obtain ⟨u', hu'⟩ : ∃ u' : ∀ Y : Node, GfC (D := dOf L) (G'.V Y), ∀ Y, DefNode m Y → HEq (u' Y) (S.N.u Y) :=
    ⟨fun Y => if h : DefNode m Y then trU (eVd' Y h) (S.N.u Y) else 1, fun Y h => by
      simp only [dif_pos h]; exact trU_heq _ _⟩

  have hTd : DefNode m (.top _) := hm'.le
  have hGd : DefNode m (.grid _ _) := (⟨hm'.le, hm'⟩ : _ ≤ m ∧ _ = m)
  have hTop := top_tr (D := dOf L) (eVd' _ hGd) (eVd' _ hTd) hG.topDec.1 hG.topDec.2 G.sp.topDec.rank G'.sp.topDec.rank
    (hfr _ hGd) (hfr _ hTd) (hu' _ hGd) (hu' _ hTd) S.N.fr_top S.N.fr_last S.N.u_top S.N.u_last
  obtain ⟨N', hNS, hN'⟩ : ∃ N' : Std G' Set.univ, N'.S = S.N.S ∧
      ∀ Y, DefNode m Y → HEq (N'.fr Y) (S.N.fr Y) ∧ HEq (N'.u Y) (S.N.u Y) := by
    refine ⟨{ S := S.N.S, prime := S.N.prime, off := ?_, unr := ?_, fr := fr', fr_on := ?_, u := ((by with_unfolding_all exact (u' :))), u_supp := ?_,
              u_lat := ?_, fr_top := ((by with_unfolding_all exact (hTop.1 :))), fr_last := ((by with_unfolding_all exact (hTop.2.1 :))),
              u_top := ((by with_unfolding_all exact (hTop.2.2.1 :))), u_last := ((by with_unfolding_all exact (hTop.2.2.2 :))) }, rfl,
      fun Y h => ⟨hfr Y h, (by with_unfolding_all exact (hu' Y h :))⟩⟩
    · intro w hw
      obtain ⟨a, b, c⟩ := S.N.off w hw
      exact ⟨by rw [eS0]; exact a, fun t _ w' hw' => b (ι t) trivial w' (by rw [← eQ]; exact hw'), c⟩
    · intro w hw e he t _ j h1 h2
      rw [eMu t j h1 (h2.trans_eq hm')]
      exact S.N.unr w hw e he (ι t) trivial j h1 (h2.trans_eq (hm'.trans hm.symm))
    · intro Y hY
      have h : DefNode m Y := hm' ▸ hY
      exact (by with_unfolding_all exact (frOn_tr (D := dOf L) (eVd' Y h) (hfr Y h) (S.N.fr_on Y (hm.symm ▸ h)) :))
    · intro Y hY
      have h : DefNode m Y := hm' ▸ hY
      exact (by with_unfolding_all exact (uSupp_tr (D := dOf L) (eVd' Y h) (hu' Y h) (S.N.u_supp Y (hm.symm ▸ h)) :))
    · intro Y hY
      have h : DefNode m Y := hm' ▸ hY
      exact (by with_unfolding_all exact (uLat_tr (D := dOf L) (eVd' Y h) (eVd Y h).2 (hfr Y h) (hu' Y h) (S.N.u_lat Y (hm.symm ▸ h)) :))

  obtain ⟨βp', hβp'⟩ : ∃ βp' : ∀ j, GL (Fin (G'.V (.top j)).rank) (Formalism.IndefR.Lev.EAf (dOf L)), ∀ j, HEq (βp' j) (S.βp j) :=
    ⟨fun j => trGL (eVt j) (S.βp j), fun j => trGL_heq _ _⟩
  have hm0 : ∀ {n : ℕ}, n = m → n ≠ 0 := fun h => by omega
  have eVm : ∀ j, G'.V (.grid _ j) = G.V (.grid _ j) := fun j => by
    have := (hG.grid k j).1
    rw [← hk, ← hm'] at this
    exact eq_of_heq this

  have eψ : W'.ψ = W.ψ := eq_of_heq hW.ψ
  have eθ : W'.θ = W.θ := eq_of_heq hW.θ
  have eP : ∀ p, DefPair m p → G'.pS p = G.pS (mapPair ι p) ∧ G'.pT p = G.pT (mapPair ι p) := by
    rintro (⟨i, j⟩ | ⟨t, i, j⟩ | i | ⟨t, j⟩) hp
    · exact ⟨congrArg negSp (eVd' (.grid (i + 1) j) ⟨hp.1, hp.2⟩), eVd' (.grid i j) ⟨by have := hp.1; omega, hp.2⟩⟩
    · exact absurd hp id
    · exact absurd hp id
    · exact ⟨eVt j, eVt (j + 1)⟩
  have hmap : ∀ p, DefPair m p → DefPair m (mapPair ι p) := by
    rintro (⟨i, j⟩ | ⟨t, i, j⟩ | i | ⟨t, j⟩) hp <;> exact hp
  obtain ⟨e0', he0', ze0'⟩ : ∃ e0' : ∀ p : Pair T', Formalism.MainNotions.TaylorLogMetric.VC (dOf L) (G'.pS p).rank (G'.pT p).rank → ℂ,
      (∀ p, DefPair m p → HEq (e0' p) (S.Z.e0 (mapPair ι p))) ∧ ∀ p, ¬ DefPair m p → e0' p = 0 := by
    refine ⟨fun p => if h : DefPair m p then trFun (F := fun nk : ℕ × ℕ => Formalism.MainNotions.TaylorLogMetric.VC (dOf L) nk.1 nk.2 → ℂ)
      (Prod.ext (rk_eq (eP p h).1) (rk_eq (eP p h).2) : ((G'.pS p).rank, (G'.pT p).rank) =
        ((G.pS (mapPair ι p)).rank, (G.pT (mapPair ι p)).rank)) (S.Z.e0 (mapPair ι p)) else 0,
      fun p h => ?_, fun p h => ?_⟩
    · simp only [dif_pos h]; exact trFun_heq _ _
    · simp only [dif_neg h]
  obtain ⟨vac', hvac', zvac'⟩ : ∃ vac' : ∀ p : Pair T', Formalism.IndefR.Datum.WO (D := dOf L) (G'.pS p) (G'.pT p) → ℂ,
      (∀ p, DefPair m p → HEq (vac' p) (S.Z.vac (mapPair ι p))) ∧ ∀ p, ¬ DefPair m p → vac' p = 0 := by
    refine ⟨fun p => if h : DefPair m p then trFun (F := fun ST : HSp (dOf L) × HSp (dOf L) => Formalism.IndefR.Datum.WO ST.1 ST.2 → ℂ)
      (Prod.ext (eP p h).1 (eP p h).2 : (G'.pS p, G'.pT p) = (G.pS (mapPair ι p), G.pT (mapPair ι p))) (S.Z.vac (mapPair ι p))
      else 0, fun p h => ?_, fun p h => ?_⟩
    · simp only [dif_pos h]; exact trFun_heq _ _
    · simp only [dif_neg h]
  have hDN : ∀ Y, DefNode m Y → DefNode _ Y := fun Y h => hm'.symm ▸ h
  have vacDD : ∀ ψ θ (S T : HSp (dOf L)) cS cT LS LT f, Formalism.IndefR.Datum.IsVacO (D := dOf L) ψ θ S T cS cT LS LT f →
      Formalism.IndefR.Datum.IsVacO (D := dOf L') ψ θ S T cS cT LS LT f := by
    rintro ψ θ S T cS cT LS LT f ⟨h1, ⟨hinf, ⟨q, l, c, s⟩, hlat, hfock, hnorm⟩⟩
    exact ⟨(by with_unfolding_all exact (h1 :)), ⟨(by with_unfolding_all exact (hinf :)), ⟨(by with_unfolding_all exact (q :)), (by with_unfolding_all exact (l :)), (by with_unfolding_all exact (c :)), (by with_unfolding_all exact (s :))⟩, (by with_unfolding_all exact (hlat :)),
      (by with_unfolding_all exact (hfock :)), (by with_unfolding_all exact (hnorm :))⟩⟩
  obtain ⟨Z', hZδ, hZ'⟩ : ∃ Z' : Normal W' N', Z'.δ = S.Z.δ ∧
      ∀ p, DefPair m p → HEq (Z'.vac p) (S.Z.vac (mapPair ι p)) ∧ Z'.c0 p = S.Z.c0 (mapPair ι p) := by
    refine ⟨{ δ := S.Z.δ, crv := ((by with_unfolding_all exact (S.Z.crv :))), t0 := S.Z.t0, pt0 := ((by with_unfolding_all exact (S.Z.pt0 :))), e0 := ((by with_unfolding_all exact (e0' :))),
              e0_is := ?_, vac := ((by with_unfolding_all exact (vac' :))), vac_is := ?_, c0 := fun p => S.Z.c0 (mapPair ι p), kernelNorm_constant_spec := ?_,
              free := ?_ }, rfl, fun p h => ⟨(by with_unfolding_all exact (hvac' p h :)), rfl⟩⟩
    · intro p hp
      have h : DefPair m p := hm' ▸ hp
      exact (by with_unfolding_all exact (oddGenerator_condition_of_rank_eq_heq (D := dOf L) (rk_eq (eP p h).1) (rk_eq (eP p h).2) (he0' p h)
        (S.Z.e0_is (mapPair ι p) (hm.symm ▸ hmap p h)) :))
    · intro p hp
      have h : DefPair m p := hm' ▸ hp
      rcases p with ⟨i, j⟩ | ⟨t, i, j⟩ | i | ⟨t, j⟩
      · have hS := eVd' (.grid (i + 1) j) ⟨h.1, h.2⟩
        have hT := eVd' (.grid i j) ⟨by have := h.1; omega, h.2⟩
        exact (by with_unfolding_all exact (vacDD _ _ _ _ _ _ _ _ _ <| vac_tr (D := dOf L) eψ eθ (congrArg negSp hS) hT (neg_heq hS (hW.cart _ (hDN (.grid (i + 1) j) ⟨h.1, h.2⟩)))
          (hW.cart _ (hDN (.grid i j) ⟨by have := h.1; omega, h.2⟩)) (colLat_heq hS (hN' (.grid (i + 1) j) ⟨h.1, h.2⟩).1)
          (colLat_heq hT (hN' (.grid i j) ⟨by have := h.1; omega, h.2⟩).1) (hvac' _ h) (S.Z.vac_is (.chi i j) (hm.symm ▸ h)) :))
      · exact absurd h id
      · exact absurd h id
      · have hS := eVt j
        have hT := eVt (j + 1)
        exact (by with_unfolding_all exact (vacDD _ _ _ _ _ _ _ _ _ <| vac_tr (D := dOf L) eψ eθ hS hT (hW.cart _ (hDN (.top j) (by have h' : j + 1 ≤ m := h; show j ≤ m; omega)))
          (hW.cart _ (hDN (.top (j + 1)) h)) (colLat_heq hS (hN' (.top j) (by have h' : j + 1 ≤ m := h; show j ≤ m; omega)).1)
          (colLat_heq hT (hN' (.top (j + 1)) h).1) (hvac' _ h) (S.Z.vac_is (.top (ι t) j) (hm.symm ▸ h)) :))
    · intro p hp
      have h : DefPair m p := hm' ▸ hp
      rcases p with ⟨i, j⟩ | ⟨t, i, j⟩ | i | ⟨t, j⟩
      · have hS := eVd' (.grid (i + 1) j) ⟨h.1, h.2⟩
        have hT := eVd' (.grid i j) ⟨by have := h.1; omega, h.2⟩
        exact (by with_unfolding_all exact (fockVectorNormalisation_of_space_eq_heq (D := dOf L) eψ eθ (congrArg negSp hS) hT (neg_heq hS (hW.cart _ (hDN (.grid (i + 1) j) ⟨h.1, h.2⟩)))
          (hW.cart _ (hDN (.grid i j) ⟨by have := h.1; omega, h.2⟩)) (frC_heq hS (hN' (.grid (i + 1) j) ⟨h.1, h.2⟩).1)
          (frC_heq hT (hN' (.grid i j) ⟨by have := h.1; omega, h.2⟩).1) (hvac' _ h) (he0' _ h) _ _ _
          (S.Z.kernelNorm_constant_spec (.chi i j) (hm.symm ▸ h)) :))
      · exact absurd h id
      · exact absurd h id
      · have hS := eVt j
        have hT := eVt (j + 1)
        exact (by with_unfolding_all exact (fockVectorNormalisation_of_space_eq_heq (D := dOf L) eψ eθ hS hT (hW.cart _ (hDN (.top j) (by have h' : j + 1 ≤ m := h; show j ≤ m; omega)))
          (hW.cart _ (hDN (.top (j + 1)) h)) (frC_heq hS (hN' (.top j) (by have h' : j + 1 ≤ m := h; show j ≤ m; omega)).1)
          (frC_heq hT (hN' (.top (j + 1)) h).1) (hvac' _ h) (he0' _ h) _ _ _ (S.Z.kernelNorm_constant_spec (.top (ι t) j) (hm.symm ▸ h)) :))
    · intro t t' j
      by_cases hj : DefPair m (Pair.top t j : Pair T')
      · have hj' : DefPair m (Pair.top t' j : Pair T') := hj
        obtain ⟨f1, f2, f3⟩ := S.Z.free (ι t) (ι t') j
        refine ⟨?_, ?_, f3⟩
        · exact (by with_unfolding_all exact (eq_of_heq ((he0' _ hj).trans ((heq_of_eq f1).trans (he0' _ hj').symm)) :))
        · exact (by with_unfolding_all exact (eq_of_heq ((hvac' _ hj).trans ((heq_of_eq f2).trans (hvac' _ hj').symm)) :))
      · have hj' : ¬ DefPair m (Pair.top t' j : Pair T') := hj
        obtain ⟨_, _, f3⟩ := S.Z.free (ι t) (ι t') j
        exact ⟨(by with_unfolding_all exact ((ze0' _ hj).trans (ze0' _ hj').symm :)), (by with_unfolding_all exact ((zvac' _ hj).trans (zvac' _ hj').symm :)), f3⟩
  refine ⟨{ B := B', βp := ((by with_unfolding_all exact (βp' :))), βp_is := ?_, row := ?_, last := ?_, N := N', Z := Z',
            PA := ((by with_unfolding_all exact (S.PA :))), PA_dvd := ((by with_unfolding_all exact (S.PA_dvd :))), PA_one := ((by with_unfolding_all exact (S.PA_one :))) }, ?_⟩
  · intro j hj
    exact (by with_unfolding_all exact (isFrame_tr' (D := dOf L) (eVt j) (hG.top j).2 (hβp' j) (S.βp_is j hj) :))
  · intro t _ w hw j hj
    have hw' : w ∈ locPl G (ι t) := by rw [← eloc]; exact hw
    have h := S.row (ι t) trivial w hw' j hj
    rw [ecos w]
    exact (by with_unfolding_all exact (sumFrame_tr (D := dOf L) (eVt j) (eVm j) (hG.rowDec j hj hj).1 (hG.rowDec j hj hj).2 (G.rowDec j hj).rank
      (G'.rowDec j hj).rank (hβp' j) (hB' _ j (hm0 hm')) h :))
  · intro t _ w hw
    have hw' : w ∈ locPl G (ι t) := by rw [← eloc]; exact hw
    have h := S.last (ι t) trivial w hw'
    exact (by with_unfolding_all exact (sumFrame_tr (D := dOf L) (eVd' _ hGd) (eVt _) hG.topDec.1 hG.topDec.2 G.sp.topDec.rank G'.sp.topDec.rank
      (hB' _ _ (hm0 hm')) (hβp' _) h :))
  · refine ⟨fun i j => hB' (i + 1) j (Nat.succ_ne_zero i), fun j => (by with_unfolding_all exact (hβp' j :)), fun Y hY => ?_, hZδ,
      fun p hp => hZ' p (hm' ▸ hp), (by with_unfolding_all exact ((HEq.refl S.PA) :))⟩
    have h : DefNode m Y := hm' ▸ hY
    exact ⟨(hN' Y h).1, (by with_unfolding_all exact (val_heq (D := dOf L) (eVd' Y h) (hN' Y h).2 :))⟩

end GlobalTheory.RowEx

end
