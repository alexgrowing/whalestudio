import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Formalism.LocalToGlobal.IndefiniteReal.HeckeNonvanishing.Imports
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCosetSameLocalCosetSetsOtherBaseLatticeStatement
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

namespace GlobalTheory.RowEx.Carry

open GlobalTheory.FunObj Matrix GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.StdFrames ValuativeRel
open scoped TensorProduct nonZeroDivisors Pointwise

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw GlobalTheory.FunObj.borelSpaceKw

local macro:max "kc% " e:term:max : term => `((by kexactB $e))

def SameD : Prop := ∀ {D : D7} {T T' : Type} {L : LevCh D T} {L' : LevCh D T'} {sc : Consts} (G : GridData L sc) (G' : GridData L' sc)
    (B : FunObj.Frames G) (B' : FunObj.Frames G') (ι : T' → T),
    IsSDFrame (Yc D 0) (L.βY 0) (L.ΛY 0) (D.host.g 0 * D.host.g 1) →
    IsSDFrame (Yc D 0) (L'.βY 0) (L'.ΛY 0) (D.host.g 0 * D.host.g 1) →
    L'.C = L.C → L'.Pg = L.Pg → (∀ t, L'.xiH t = L.xiH (ι t)) → (∀ t, L'.Q t = L.Q (ι t)) →
    G'.pl.v0 = G.pl.v0 → G'.pl.w = G.pl.w → G'.ch.chiH = G.ch.chiH →
    (∀ i, G'.sp.Vs (i + 1) 0 = G.sp.Vs (i + 1) 0) → (∀ i, HEq (B'.βs (i + 1) 0) (B.βs (i + 1) 0)) →
    ∀ Φ' : G'.Datum, ∃ Φ : G.Datum, ∀ t w, w ∈ FunObj.locPl G' t →
      FunObj.locGrid G' t w = FunObj.locGrid G (ι t) w ∧ HEq (FunObj.givenLevel G' t w) (FunObj.givenLevel G (ι t) w) ∧
      FunObj.cosExp G' w = FunObj.cosExp G w ∧ HEq (FunObj.givenStage t w B' Φ') (FunObj.givenStage (ι t) w B Φ)

def CosZero : Prop := ∀ {D : D7} {T T' : Type} {L : LevCh D T} {L' : LevCh D T'} {sc : Consts} (G : GridData L sc) (G' : GridData L' sc)
    (B : FunObj.Frames G) (B' : FunObj.Frames G'),
    IsSDFrame (Yc D 0) (L.βY 0) (L.ΛY 0) (D.host.g 0 * D.host.g 1) →
    IsSDFrame (Yc D 0) (L'.βY 0) (L'.ΛY 0) (D.host.g 0 * D.host.g 1) →
    G'.pl.v0 = G.pl.v0 → G'.pl.w = G.pl.w → G'.sp.Vs 1 0 = G.sp.Vs 1 0 → HEq (B'.βs 1 0) (B.βs 1 0) →
    ∀ (h : 0 < D.R.m) (κ' : G'.CosAt 0), ∃ κ : G.CosAt 0, ∀ (t : T') (t₀ : T) (w : Pl D.host.E),
      FunObj.cosetSet t w B' h κ' = FunObj.cosetSet t₀ w B h κ

def cosSetGen {D : D7} (w : Pl D.host.E) (X1 X0 : LSp D) (b1 : GL (Fin X1.sp.rank) (Formalism.IndefR.Lev.EAf D))
    (b0 : GL (Fin X0.sp.rank) (Formalism.IndefR.Lev.EAf D)) (e : ℕ) (𝔪 : Ideal (𝓞 D.host.E)) {n1 n0 : ℕ}
    (h1 : n1 = X1.sp.rank) (h0 : n0 = X0.sp.rank) (κ : Cos X1.lat X0.lat 𝔪) : Set (Matrix (Fin n1) (Fin n0) (Kw w)) :=
  {x | ∃ y : homLat X1.lat X0.lat, Cos.mk 𝔪 y = κ ∧
    x - ((((loc w b0)⁻¹).val * (y.1.map (algebraMap D.host.E (Kw w))) * (loc w b1).val).submatrix
      (Fin.cast h0) (Fin.cast h1))ᵀ ∈ matLat (Fin n1) (unifAt w ^ e • stdLat (Kw w) (Fin n0))}

theorem cosetSet_eq_gen {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (B : Frames G) (t : T)
    (w : Pl D.host.E) {i : ℕ} (hi : i < D.R.m) (κ : G.CosAt i) :
    cosetSet t w B hi κ = cosSetGen w (G.node (.grid (i + 1) 0)) (G.node (.grid i 0)) (B.β (i + 1) 0) (B.β i 0) (cosExp G w)
      G.modul (rank_vertex G t w (X := (i + 1, 0)) ⟨hi, Nat.zero_le _⟩) (rank_vertex G t w (X := (i, 0)) ⟨hi.le, Nat.zero_le _⟩) κ :=
  rfl

theorem cosSetGen_congr {D : D7} (w : Pl D.host.E) {X1 X1' X0 X0' : LSp D} (h1 : X1' = X1) (h0 : X0' = X0)
    {b1 : GL (Fin X1.sp.rank) (Formalism.IndefR.Lev.EAf D)} {b1' : GL (Fin X1'.sp.rank) (Formalism.IndefR.Lev.EAf D)} (hb1 : HEq b1' b1)
    {b0 : GL (Fin X0.sp.rank) (Formalism.IndefR.Lev.EAf D)} {b0' : GL (Fin X0'.sp.rank) (Formalism.IndefR.Lev.EAf D)} (hb0 : HEq b0' b0)
    {e e' : ℕ} (he : e' = e) {𝔪 𝔪' : Ideal (𝓞 D.host.E)} (hm : 𝔪' = 𝔪) {n1 n0 : ℕ} (r1 : n1 = X1.sp.rank)
    (r0 : n0 = X0.sp.rank) (r1' : n1 = X1'.sp.rank) (r0' : n0 = X0'.sp.rank) {κ : Cos X1.lat X0.lat 𝔪}
    {κ' : Cos X1'.lat X0'.lat 𝔪'} (hκ : HEq κ' κ) :
    cosSetGen w X1' X0' b1' b0' e' 𝔪' r1' r0' κ' = cosSetGen w X1 X0 b1 b0 e 𝔪 r1 r0 κ := by
  subst h1 h0 he hm
  cases hb1
  cases hb0
  cases hκ
  rfl

theorem cos_congr {D : D7} {X1 X1' X0 X0' : LSp D} (h1 : X1' = X1) (h0 : X0' = X0) (𝔪 : Ideal (𝓞 D.host.E)) :
    Cos X1'.lat X0'.lat 𝔪 = Cos X1.lat X0.lat 𝔪 := by
  subst h1 h0
  rfl

theorem stage_heq {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {Γ Γ' : SplitFlip.Grid k} (h : Γ = Γ') (p : List Edge) {l : Γ.Level} {l' : Γ'.Level} (hl : HEq l l')
    {d : ∀ b : Edge, Matrix (Fin (Γ.rank b.tgt)) (Fin (Γ.rank b.src)) k → ℂ}
    {d' : ∀ b : Edge, Matrix (Fin (Γ'.rank b.tgt)) (Fin (Γ'.rank b.src)) k → ℂ} (hd : HEq d d') :
    HEq (⟨p, l, Γ.lines₂ p d⟩ : Γ.PiLocalization₂) (⟨p, l', Γ'.lines₂ p d'⟩ : Γ'.PiLocalization₂) := by
  subst h
  cases hl
  cases hd
  rfl

abbrev gOf {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (_ : Frames G) : GridData L sc := G

set_option maxHeartbeats 1000000 in
theorem sameD_of_cosZero (hz : CosZero) : SameD := by
  intro D T T' L L' sc G G' B B' ι hY hY' hC hPg hxi hQ hv0 hw hchi hVs hβ Φ'
  have hm : 0 < D.R.m := by have := D.R.two_le_m; omega
  obtain ⟨κ0, hκ0⟩ := hz G G' B B' hY hY' hv0 hw (hVs 0) (hβ 0) hm (Φ' ⟨0, hm⟩)
  have hmod : G'.modul = G.modul := by
    unfold GridData.modul Places.modul Places.S0 Places.depth
    rw [hv0, hw]
  have hcos : ∀ w, cosExp G' w = cosExp G w := fun w => by
    unfold cosExp Places.W0 Places.S0 Places.depth
    rw [hv0, hw]
  have eC : ∀ i (h : i + 1 < D.R.m), G'.CosAt (i + 1) = G.CosAt (i + 1) := fun i h =>
    by show Cos _ _ G'.modul = Cos _ _ G.modul; rw [hmod]; exact cos_congr (hVs (i + 1)) (hVs i) G.modul
  obtain ⟨C, xiH, mu0, eta, xi, Pg, Q, chi, xiR, ΛY, ΛX, ΛV, ΛW, βY, βX, βV, βW⟩ := L
  obtain ⟨C', xiH', mu0', eta', xi', Pg', Q', chi', xiR', ΛY', ΛX', ΛV', ΛW', βY', βX', βV', βW'⟩ := L'
  dsimp only at hC hPg hxi hQ
  subst hC hPg
  obtain rfl : xiH' = xiH ∘ ι := funext hxi
  obtain rfl : Q' = Q ∘ ι := funext hQ
  obtain ⟨pl, ⟨chiH, chi₁, chi_eq, triv, inf, unr, lev1, wild, lev0⟩, sp⟩ := G
  obtain ⟨pl', ⟨chiH', chi₁', chi_eq', triv', inf', unr', lev1', wild', lev0'⟩, sp'⟩ := G'
  dsimp only at hchi
  subst chiH'
  let Φ : (gOf B).Datum := fun i => match i with
    | ⟨0, _⟩ => κ0
    | ⟨i + 1, h⟩ => cast (eC i h) (Φ' ⟨i + 1, h⟩)
  refine ⟨Φ, fun t w _ => ?_⟩
  have hloc : locGrid (gOf B') t w = locGrid (gOf B) (ι t) w := rfl
  have hlev : givenLevel (gOf B') t w = givenLevel (gOf B) (ι t) w := by
    funext X
    rcases X with ⟨_ | i, _ | j⟩
    · simp only [givenLevel, hcos w]
      try rfl
    · rfl
    · simp only [givenLevel, hcos w]
      try rfl
    · rfl
  have hd : givenDatum t w B' Φ' = givenDatum (ι t) w B Φ := by
    funext b
    rcases b with ⟨_ | i, j⟩ | ⟨_ | i, _ | j⟩
    · rfl
    · rfl
    · simp only [givenDatum, dif_pos hm]
      exact congrArg (fun s => Set.indicator s 1) (hκ0 t (ι t) w)
    · rfl
    · simp only [givenDatum]
      split_ifs with hi
      · rw [cosetSet_eq_gen, cosetSet_eq_gen]
        exact congrArg (fun s => Set.indicator s 1) (cosSetGen_congr w (hVs (i + 1)) (hVs i) (hβ (i + 1)) (hβ i) (hcos w)
          hmod _ _ _ _ (cast_heq _ _).symm)
      · rfl
    · rfl
  exact ⟨hloc, heq_of_eq hlev, hcos w, stage_heq hloc _ (heq_of_eq hlev) (heq_of_eq hd)⟩

theorem flips_tensor_heq {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] {Γ Γ' : SplitFlip.Grid k} (hΓ : Γ = Γ') {S : Γ.PiLocalization₂} {S' : Γ'.PiLocalization₂} (hS : HEq S S')
    (s : SplitFlip.Assignment) {ψ ψ' : AddChar k Circle} (hψ : ψ = ψ') (ϖ : kˣ) {e e' : ℕ} (he : e = e') (l : List (ℕ × ℕ)) :
    HEq (S.flips s ψ ϖ e l).tensor (S'.flips s ψ' ϖ e' l).tensor := by
  subst hΓ hψ he
  cases hS
  rfl

theorem tflip_eq {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (B : FunObj.Frames G)
    (t : T) (Φ : G.Datum) (w : Pl D.host.E) : FunObj.Tflip W B t Φ w =
      ((FunObj.givenStage t w B Φ).flips .one (FunObj.psiAt W w) (FunObj.unifAt w) (FunObj.depthAt G w)
        (FunObj.flipOrder D.R.m)).tensor := rfl

theorem lsp_eq {D : D7} {x : LSp D} {s : HSp D} {l : Submodule (𝓞 D.host.E) (Fin s.rank → D.host.E)} (hs : s = x.sp)
    (hl : HEq l x.lat) : (⟨s, l⟩ : LSp D) = x := by
  cases x
  subst hs
  cases hl
  rfl

abbrev dOf {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (_ : GridData L sc) : D7 := D

abbrev lOf {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (_ : GridData L sc) : LevCh D T := L

set_option maxHeartbeats 4000000 in
theorem trFlip_of_same (hsame : SameD) : TrFlip := by
  intro X X' T T' L L' sc G G' W W' S S' μ₀ μ₀' ι hA Φ'
  obtain ⟨hl, hg, hw, hs⟩ := hA
  obtain ⟨hpre, hLis, hLis', hC, hbase, hxi, hQ, hβX, hβX'⟩ := hl
  obtain ⟨f, f', hff, hCf, hCf'⟩ := hC
  obtain ⟨C₁, xiH₁, mu0₁, eta₁, xi₁, Pg₁, Q₁, chi₁, xiR₁, ΛY₁, ΛX₁, ΛV₁, ΛW₁, βY₁, βX₁, βV₁, βW₁⟩ := L
  obtain ⟨C₂, xiH₂, mu0₂, eta₂, xi₂, Pg₂, Q₂, chi₂, xiR₂, ΛY₂, ΛX₂, ΛV₂, ΛW₂, βY₂, βX₂, βV₂, βW₂⟩ := L'
  dsimp only at hCf hCf'
  subst hCf hCf'
  obtain ⟨Bx, Cx, Wx, Vx, Sx, Nx, Gx⟩ := X
  obtain ⟨Bx', Cx', Wx', Vx', Sx', Nx', Gx'⟩ := X'
  obtain ⟨P⟩ := Bx
  obtain ⟨P'⟩ := Bx'
  dsimp only at hpre
  subst P'
  obtain ⟨R⟩ := P
  obtain ⟨re, rk, rm⟩ := R
  obtain ⟨m, rfl⟩ : ∃ m, rm = m + 1 := ⟨rm - 1, by omega⟩
  have hff' := eq_of_heq hff
  subst f'
  let Lc : LevCh (dOf G) T' :=
    { C := (lOf G).C, xiH := (by with_unfolding_all exact (xiH₂ :)), mu0 := (by with_unfolding_all exact (mu0₂ :)), eta := (by with_unfolding_all exact (eta₂ :)), xi := (by with_unfolding_all exact (xi₂ :)), Pg := (by with_unfolding_all exact (Pg₂ :)),
      Q := (by with_unfolding_all exact (Q₂ :)), chi := (by with_unfolding_all exact (chi₂ :)), xiR := (by with_unfolding_all exact (xiR₂ :)), ΛY := (by with_unfolding_all exact (ΛY₂ :)), ΛX := (by with_unfolding_all exact (ΛX₂ :)), ΛV := (by with_unfolding_all exact (ΛV₂ :)), ΛW := (by with_unfolding_all exact (ΛW₂ :)),
      βY := (by with_unfolding_all exact (βY₂ :)), βX := (by with_unfolding_all exact (βX₂ :)), βV := (by with_unfolding_all exact (βV₂ :)), βW := (by with_unfolding_all exact (βW₂ :)) }
  let plc : Places Lc :=
    { v0 := (by with_unfolding_all exact (G'.pl.v0 :)), basePlace_over_qZero := (by with_unfolding_all exact (G'.pl.basePlace_over_qZero :)), w := (by with_unfolding_all exact (G'.pl.w :)), w_over := (by with_unfolding_all exact (G'.pl.w_over :)),
      w_split := (by with_unfolding_all exact (G'.pl.w_split :)), w_g := (by with_unfolding_all exact (G'.pl.w_g :)), w_de := (by with_unfolding_all exact (G'.pl.w_de :)), w_Q := (by with_unfolding_all exact (G'.pl.w_Q :)),
      levelPlace_ne_basePlace := (by with_unfolding_all exact (G'.pl.levelPlace_ne_basePlace :)) }
  let chc : Chars plc sc.cGap :=
    { chiH := (by with_unfolding_all exact (G'.ch.chiH :)), chi := (by with_unfolding_all exact (G'.ch.chi :)), chi_eq := (by with_unfolding_all exact (G'.ch.chi_eq :)), triv := (by with_unfolding_all exact (G'.ch.triv :)),
      inf := (by with_unfolding_all exact (G'.ch.inf :)), unr := (by with_unfolding_all exact (G'.ch.unr :)), lev1 := (by with_unfolding_all exact (G'.ch.lev1 :)), wild := (by with_unfolding_all exact (G'.ch.wild :)), lev0 := (by with_unfolding_all exact (G'.ch.lev0 :)) }
  let spc : Vertices Lc (plc.stA sc) (plc.stAbar sc) :=
    { Vs := fun i j => ⟨(G'.sp.Vs i j).sp, (G'.sp.Vs i j).lat⟩
      P := fun i => ⟨(G'.sp.P i).sp, (G'.sp.P i).lat⟩
      Xs := fun j => ⟨(G'.sp.Xs j).sp, (G'.sp.Xs j).lat⟩
      V_is := fun i j h1 h2 h3 => let v := G'.sp.V_is i j h1 h2 h3; ⟨(by with_unfolding_all exact (v.rank :)), (by with_unfolding_all exact (v.sigOK :)), (by with_unfolding_all exact (v.sig :)), (by with_unfolding_all exact (v.sd :))⟩
      P_is := fun i h1 => let v := G'.sp.P_is i h1; ⟨(by with_unfolding_all exact (v.rank :)), (by with_unfolding_all exact (v.sigOK :)), (by with_unfolding_all exact (v.sig :)), (by with_unfolding_all exact (v.sd :))⟩
      X_is := fun j h1 h2 => let v := G'.sp.X_is j h1 h2; ⟨(by with_unfolding_all exact (v.rank :)), (by with_unfolding_all exact (v.sigOK :)), (by with_unfolding_all exact (v.sig :)), (by with_unfolding_all exact (v.sd :))⟩
      dec0 := let d := G'.sp.dec0; ⟨d.ι, (by with_unfolding_all exact (d.isom :)), d.a, (by with_unfolding_all exact (d.gram :)), (by with_unfolding_all exact (d.perp :)), (by with_unfolding_all exact (d.rank :))⟩
      lat0 := (by with_unfolding_all exact (G'.sp.lat0 :))
      colDec := fun i h h' => match i, h, h' with
        | 0, h, _ => absurd h (by omega)
        | i + 1, h, h' => let d := G'.sp.colDec (i + 1) h h'; ⟨d.ι, (by with_unfolding_all exact (d.isom :)), d.a, (by with_unfolding_all exact (d.gram :)), (by with_unfolding_all exact (d.perp :)), (by with_unfolding_all exact (d.rank :))⟩
      colLat := fun i h h' => match i, h, h' with
        | 0, h, _ => absurd h (by omega)
        | i + 1, h, h' => (by with_unfolding_all exact ((G'.sp.colLat (i + 1) h h') :))
      rowDecS := fun j h => let d := G'.sp.rowDecS j h; ⟨d.ι, (by with_unfolding_all exact (d.isom :)), d.a, (by with_unfolding_all exact (d.gram :)), (by with_unfolding_all exact (d.perp :)), (by with_unfolding_all exact (d.rank :))⟩
      rowLat := fun j h => (by with_unfolding_all exact ((G'.sp.rowLat j h) :))
      topDec := let d := G'.sp.topDec; ⟨d.ι, (by with_unfolding_all exact (d.isom :)), d.a, (by with_unfolding_all exact (d.gram :)), (by with_unfolding_all exact (d.perp :)), (by with_unfolding_all exact (d.rank :))⟩
      topLat := (by with_unfolding_all exact (G'.sp.topLat :)) }
  let Gc : GridData Lc sc := ⟨plc, chc, spc⟩
  let Bc : FunObj.Frames Gc := ⟨(by with_unfolding_all exact (S'.B.βs :)), (by with_unfolding_all exact (S'.B.isFrame :))⟩
  let Φc : Gc.Datum := fun i => match i with
    | ⟨0, h⟩ => (by with_unfolding_all exact ((Φ' ⟨0, h⟩) :))
    | ⟨i + 1, h⟩ => (by with_unfolding_all exact ((Φ' ⟨i + 1, h⟩) :))
  have hPg : Lc.Pg = (lOf G).Pg := Finset.ext fun PP =>
    ((by with_unfolding_all exact ((hLis'.Pg PP) :)) : PP ∈ Lc.Pg ↔ ∃ k, Lc.C.P.Div k PP).trans (hLis.Pg PP).symm
  obtain ⟨Φ, hΦ⟩ := hsame G Gc S.B Bc ι (hLis.βY 0 (Nat.succ_pos m)) ((by with_unfolding_all exact ((hLis'.βY 0 (Nat.succ_pos m)) :))) rfl hPg
    (fun t => (by with_unfolding_all exact ((eq_of_heq (hxi t)) :))) (fun t => (by with_unfolding_all exact ((eq_of_heq (hQ t)) :))) ((by with_unfolding_all exact ((eq_of_heq hg.v0) :))) ((by with_unfolding_all exact ((eq_of_heq hg.w) :)))
    ((by with_unfolding_all exact ((eq_of_heq hg.chiH) :))) (fun i => lsp_eq ((by with_unfolding_all exact ((eq_of_heq (hg.grid i 0).1) :))) ((by with_unfolding_all exact ((hg.grid i 0).2 :))))
    (fun i => (by with_unfolding_all exact ((hs.β i 0) :))) Φc
  refine ⟨Φ, fun t w w' hww hw' => ?_⟩
  have e : w' = w := (by with_unfolding_all exact ((eq_of_heq hww) :))
  subst e
  obtain ⟨h1, h2, h3, h4⟩ := hΦ t w' ((by with_unfolding_all exact (hw' :)))
  have e1 : locGrid G' t w' = locGrid G (ι t) w' := (by with_unfolding_all exact (h1 :))
  refine ⟨heq_of_eq e1, (by with_unfolding_all exact (h2 :)), ?_⟩
  have hd : givenDatum (G := G') t w' S'.B Φ' = (by with_unfolding_all exact ((givenDatum (G := Gc) t w' Bc Φc) :)) := by
    funext b
    rcases b with ⟨_ | i, j⟩ | ⟨_ | i, _ | j⟩ <;> rfl
  have T3 : HEq (givenStage (G := G') t w' S'.B Φ') (givenStage (G := Gc) t w' Bc Φc) := by
    unfold givenStage
    rw [hd]
    exact (by with_unfolding_all exact ((HEq.refl (givenStage (G := Gc) t w' Bc Φc)) :))
  have eψ := eq_of_heq hw.ψ
  have hψ : psiAt W' w' = psiAt W w' := by
    ext x
    change W'.ψ _ = W.ψ _
    rw [eψ]
    rfl
  have hdep : depthAt G' w' = depthAt G w' := (by with_unfolding_all exact ((congrArg (max · 1) h3) :))
  exact (by with_unfolding_all exact ((flips_tensor_heq e1 (T3.trans h4) .one hψ (unifAt w') hdep (flipOrder (m + 1))) :))

theorem flippedTensorsTransferToGrid_proof : TrFlip := trFlip_of_same (sameD_of_cosZero GlobalTheory.T.exists_coset_same_localCosetSets_other_baseLattice)

end GlobalTheory.RowEx.Carry
