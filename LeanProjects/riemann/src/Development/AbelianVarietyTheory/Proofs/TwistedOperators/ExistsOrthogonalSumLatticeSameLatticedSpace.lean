import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NodeAgree
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ReLatSelf

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped Pointwise TensorProduct InnerProductSpace nonZeroDivisors

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GridJoin

open GlobalTheory.ChiGrid GlobalTheory.VolRatioCompare

variable {D : D7}

def SameSp (V V' : HSp D) : Prop := ∃ L h1 h2, V' = reLat V L h1 h2

theorem SameSp.refl (V : HSp D) : SameSp V V := by
  refine ⟨V.L0, V.standardTuple_isLattice, V.baseLattice_isUnimodular, ?_⟩
  cases V
  rfl

theorem SameSp.neg {V V' : HSp D} (h : SameSp V V') : SameSp (negSp V) (negSp V') := by
  obtain ⟨L, h1, h2, rfl⟩ := h
  exact ⟨L, h1, (negSp (reLat V L h1 h2)).baseLattice_isUnimodular, rfl⟩

theorem SameSp.rank {V V' : HSp D} (h : SameSp V V') : V'.rank = V.rank := by
  obtain ⟨L, h1, h2, rfl⟩ := h
  rfl

def SameL (X X' : LSp D) : Prop := ∃ L h1 h2, X' = ⟨reLat X.sp L h1 h2, X.lat⟩

theorem SameL.refl (X : LSp D) : SameL X X := by
  refine ⟨X.sp.L0, X.sp.standardTuple_isLattice, X.sp.baseLattice_isUnimodular, ?_⟩
  obtain ⟨sp, lat⟩ := X
  cases sp
  rfl

theorem SameL.sp {X X' : LSp D} (h : SameL X X') : SameSp X.sp X'.sp := by
  obtain ⟨L, h1, h2, rfl⟩ := h
  exact ⟨L, h1, h2, rfl⟩

theorem SameL.lat {X X' : LSp D} (h : SameL X X') : HEq X'.lat X.lat := by
  obtain ⟨L, h1, h2, rfl⟩ := h
  exact HEq.rfl

theorem SameL.isV {X X' : LSp D} (h : SameL X X') {ν q : ℕ} (hX : X.IsV ν q) : X'.IsV ν q := by
  obtain ⟨L, h1, h2, rfl⟩ := h
  exact ⟨hX.rank, hX.sigOK, hX.sig, hX.sd⟩

theorem hT_frame (V : HSp D) (x y : V.V) :
    V.hT x y = ∑ i, ∑ j, star (V.frame.equivFun x i) * V.gram i j * V.frame.equivFun y j := by
  conv_lhs => rw [← V.frame.sum_equivFun x, ← V.frame.sum_equivFun y]
  simp only [map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, map_smul, smul_eq_mul,
    Finset.mul_sum, HSpace.gram, starRingEnd_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

private theorem exists_unimodular_lattice_eq_lat_of_isSelfDualC (X : LSp D) (h : IsSelfDualC X.sp X.lat) :
    ∃ (L : Submodule (𝓞 D.host.E) X.sp.V) (h1 : Submodule.IsLattice D.host.E L)
      (h2 : Formalism.HermitianLatticesTheory.IsUnimodular X.sp.hT L),
      (X.lat : Set (Fin X.sp.rank → D.host.E)) = {x | ∑ i, x i • X.sp.frame i ∈ L} := by
  classical
  obtain ⟨hlat, hsd⟩ := h
  let e : (Fin X.sp.rank → D.host.E) →ₗ[𝓞 D.host.E] X.sp.V :=
    (X.sp.frame.equivFun.symm : (Fin X.sp.rank → D.host.E) →ₗ[D.host.E] X.sp.V).restrictScalars (𝓞 D.host.E)
  have he : ∀ c, e c = ∑ i, c i • X.sp.frame i := fun c => X.sp.frame.equivFun_symm_apply c
  have hinv : ∀ c, X.sp.frame.equivFun (e c) = c := fun c => X.sp.frame.equivFun.apply_symm_apply c
  have hmem : ∀ c, e c ∈ X.lat.map e ↔ c ∈ X.lat := fun c =>
    ⟨fun hc => by
      obtain ⟨c', hc', hcc⟩ := Submodule.mem_map.1 hc
      have : c' = c := by rw [← hinv c', hcc, hinv]
      exact this ▸ hc', fun hc => Submodule.mem_map_of_mem hc⟩
  have hsurj : ∀ v : X.sp.V, e (X.sp.frame.equivFun v) = v := fun v => X.sp.frame.equivFun.symm_apply_apply v
  have h1 : Submodule.IsLattice D.host.E (X.lat.map e) := by
    refine ⟨hlat.fg.map e, ?_⟩
    have himg : ((X.lat.map e : Submodule (𝓞 D.host.E) X.sp.V) : Set X.sp.V) =
        (X.sp.frame.equivFun.symm : (Fin X.sp.rank → D.host.E) →ₗ[D.host.E] X.sp.V) '' (X.lat : Set _) :=
      Submodule.map_coe e X.lat
    rw [himg, Submodule.span_image, hlat.span_eq_top, Submodule.map_top, LinearEquiv.range]
  have h2 : Formalism.HermitianLatticesTheory.IsUnimodular X.sp.hT (X.lat.map e) := by
    unfold Formalism.HermitianLatticesTheory.IsUnimodular Formalism.HermitianLatticesTheory.dual Formalism.E.hdual
    ext v
    rw [← hsurj v, hmem, hsd]
    simp only [Submodule.mem_iInf, Submodule.mem_comap, LinearMap.restrictScalars_apply, Submodule.mem_one]
    constructor
    · intro H a ha
      obtain ⟨t, ht⟩ := H (e a) ((hmem a).2 ha)
      refine ⟨t, ?_⟩
      rw [RingOfIntegers.coe_eq_algebraMap, ht, hT_frame, hinv, hinv]
    · intro H y hy
      obtain ⟨a, ha, rfl⟩ := Submodule.mem_map.1 hy
      obtain ⟨t, ht⟩ := H a ha
      refine ⟨t, ?_⟩
      rw [← RingOfIntegers.coe_eq_algebraMap, ht, hT_frame, hinv, hinv]
  refine ⟨X.lat.map e, h1, h2, ?_⟩
  ext x
  simp only [Set.mem_setOf_eq, SetLike.mem_coe]
  rw [← he x, hmem x]

theorem exists_sameL (X : LSp D) : ∃ X', SameL X X' ∧ (IsSelfDualC X.sp X.lat → (X'.lat : Set _) = L0c D X'.sp) := by
  by_cases hsd : IsSelfDualC X.sp X.lat
  · obtain ⟨L, h1, h2, hL⟩ := exists_unimodular_lattice_eq_lat_of_isSelfDualC X hsd
    exact ⟨⟨reLat X.sp L h1 h2, X.lat⟩, ⟨L, h1, h2, rfl⟩, fun _ => hL⟩
  · exact ⟨X, SameL.refl X, fun h => absurd h hsd⟩

theorem exists_orthogonalSum_lattice_sameLatticedSpace {X Y X' Y' : LSp D} (hX : SameL X X') (hY : SameL Y Y') {c : ℕ} {ε : D.host.E}
    (d : HermitianOrthogonalExtensionData X.sp Y.sp c ε) (𝔟 : Fin c → FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) (h : Y.lat = d.lat X.lat 𝔟) :
    ∃ d' : HermitianOrthogonalExtensionData X'.sp Y'.sp c ε, Y'.lat = d'.lat X'.lat 𝔟 := by
  obtain ⟨L, h1, h2, rfl⟩ := hX
  obtain ⟨L', h1', h2', rfl⟩ := hY
  exact ⟨⟨d.ι, d.isom, d.a, d.gram, d.perp, d.rank⟩, h⟩

variable {T : Type} {L : LevCh D T} {sc : Consts}

theorem exists_vertices (G : GridData L sc) : ∃ sp : Vertices L (G.pl.stA sc) (G.pl.stAbar sc),
    (∀ X, SameL (G.node X) ((⟨G.pl, G.ch, sp⟩ : GridData L sc).node X)) ∧
    ∀ X : Node, X.InRange D.R.m → (∀ j, X ≠ .grid 0 j) →
      (((⟨G.pl, G.ch, sp⟩ : GridData L sc).Λ X : Set _) = L0c D ((⟨G.pl, G.ch, sp⟩ : GridData L sc).V X)) := by
  classical
  choose f hf hfL using fun X : LSp D => exists_sameL X
  have hV : ∀ i j, SameL (vtxOf L G.sp.Vs i j) (vtxOf L (fun i j => f (G.sp.Vs i j)) i j) := by
    intro i j
    cases i with
    | zero => exact SameL.refl _
    | succ i => exact hf _
  have hXo : ∀ j, SameL (xOf (G.sp.P D.R.m) G.sp.Xs j) (xOf (f (G.sp.P D.R.m)) (fun j => f (G.sp.Xs j)) j) := by
    intro j
    cases j with
    | zero => exact hf _
    | succ j => exact hf _
  obtain ⟨d0, hd0⟩ := exists_orthogonalSum_lattice_sameLatticedSpace (SameL.refl ⟨Yc D 0, L.ΛY 0⟩) (hf (G.sp.P 0)) G.sp.dec0 _ G.sp.lat0
  choose cD hcD using fun i (h : 1 ≤ i) (h' : i ≤ D.R.m) =>
    exists_orthogonalSum_lattice_sameLatticedSpace (hf (G.sp.P i)) (hV i 0) (G.sp.colDec i h h') _ (G.sp.colLat i h h')
  choose rD hrD using fun j (h : j + 1 < D.R.m) =>
    exists_orthogonalSum_lattice_sameLatticedSpace (hf (G.sp.Xs (j + 1))) (hV D.R.m (j + 1)) (G.sp.rowDecS j h) _ (G.sp.rowLat j h)
  obtain ⟨tD, htD⟩ := exists_orthogonalSum_lattice_sameLatticedSpace (hV D.R.m D.R.m) (hXo D.R.m) G.sp.topDec _ G.sp.topLat
  refine ⟨{
      Vs := fun i j => f (G.sp.Vs i j), P := fun i => f (G.sp.P i), Xs := fun j => f (G.sp.Xs j),
      V_is := fun i j h1 h2 h3 => (hf _).isV (G.sp.V_is i j h1 h2 h3),
      P_is := fun i h => (hf _).isV (G.sp.P_is i h),
      X_is := fun j h1 h2 => (hf _).isV (G.sp.X_is j h1 h2),
      dec0 := d0, lat0 := hd0, colDec := cD, colLat := hcD, rowDecS := rD, rowLat := hrD,
      topDec := tD, topLat := htD }, ?_, ?_⟩
  · intro X
    cases X with
    | grid i j => exact hV i j
    | core i => exact hf _
    | top j => exact hXo j
  · intro X hX h0
    have hsd := (G.isV hX h0).sd
    cases X with
    | grid i j =>
      cases i with
      | zero => exact absurd rfl (h0 j)
      | succ i => exact hfL _ hsd
    | core i => exact hfL _ hsd
    | top j =>
      cases j with
      | zero => exact hfL _ hsd
      | succ j => exact hfL _ hsd

section Move

variable {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D}

theorem SameSp.ex_mat {V V' : HSp D} (h : SameSp V V') (s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) :
    ∃ s' : D.what₂.Tau → Matrix (Fin V'.rank) (Fin V'.rank) ℂ, HEq s' s := by
  obtain ⟨L, h1, h2, rfl⟩ := h
  exact ⟨s, HEq.rfl⟩

theorem SameSp.cart {V V' : HSp D} (h : SameSp V V') {s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ}
    {s' : D.what₂.Tau → Matrix (Fin V'.rank) (Fin V'.rank) ℂ} (e : HEq s' s) {τ} (hs : IsCartanInv (gramAt D V τ) (s τ)) :
    IsCartanInv (gramAt D V' τ) (s' τ) := by
  obtain ⟨L, h1, h2, rfl⟩ := h
  obtain rfl := eq_of_heq e
  exact hs

theorem SameSp.onb {V V' : HSp D} (h : SameSp V V') {s b : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ}
    {s' b' : D.what₂.Tau → Matrix (Fin V'.rank) (Fin V'.rank) ℂ} (e : HEq s' s) (e' : HEq b' b) {τ}
    (hs : ∃ ε : Fin V.rank → Bool, (b τ)ᴴ * gramAt D V τ * b τ = Formalism.REAL.Jm ε ∧ s τ * b τ = b τ * Formalism.REAL.Jm ε) :
    ∃ ε : Fin V'.rank → Bool, (b' τ)ᴴ * gramAt D V' τ * b' τ = Formalism.REAL.Jm ε ∧ s' τ * b' τ = b' τ * Formalism.REAL.Jm ε := by
  obtain ⟨L, h1, h2, rfl⟩ := h
  obtain rfl := eq_of_heq e
  obtain rfl := eq_of_heq e'
  exact hs

private theorem isThetaFunO_reLat_reLat_eq {S U : HSp D} (L : Submodule (𝓞 D.host.E) S.V) (h1 : Submodule.IsLattice D.host.E L)
    (h2 : Formalism.HermitianLatticesTheory.IsUnimodular S.hT L) (L' : Submodule (𝓞 D.host.E) U.V) (h1' : Submodule.IsLattice D.host.E L')
    (h2' : Formalism.HermitianLatticesTheory.IsUnimodular U.hT L') :
    IsThetaFunO ψ (reLat S L h1 h2) (reLat U L' h1' h2') = IsThetaFunO ψ S U :=
  funext fun _ => propext ⟨fun h => { h with }, fun h => { h with }⟩

theorem ex_om {S S' U U' : HSp D} (h : SameSp S S') (h' : SameSp U U')
    (ω : GA D S × GA D U →* Module.End ℂ (WO S U → ℂ)) : ∃ ω' : GA D S' × GA D U' →* Module.End ℂ (WO S' U' → ℂ),
      HEq ω' ω ∧ ∀ χ χ', IsWeilDatumO ψ S U χ χ' ω → IsWeilDatumO ψ S' U' χ χ' ω' := by
  obtain ⟨L, h1, h2, rfl⟩ := h
  obtain ⟨L', h1', h2', rfl⟩ := h'
  have hE := isThetaFunO_reLat_reLat_eq (ψ := ψ) L h1 h2 L' h1' h2'
  refine ⟨ω, HEq.rfl, fun _ _ hω => ?_⟩
  cases hω
  constructor <;> (try rw [hE]) <;> assumption

private theorem isThetaFunO_negSp_reLat_reLat_eq {V U : HSp D} (L : Submodule (𝓞 D.host.E) V.V) (h1 : Submodule.IsLattice D.host.E L)
    (h2 : Formalism.HermitianLatticesTheory.IsUnimodular V.hT L) (L' : Submodule (𝓞 D.host.E) U.V) (h1' : Submodule.IsLattice D.host.E L')
    (h2' : Formalism.HermitianLatticesTheory.IsUnimodular U.hT L') :
    IsThetaFunO ψ (negSp (reLat V L h1 h2)) (reLat U L' h1' h2') = IsThetaFunO ψ (negSp V) U :=
  funext fun _ => propext ⟨fun h => { h with }, fun h => { h with }⟩

theorem ex_vac {X X' Y Y' : LSp D} (h : SameL X X') (h' : SameL Y Y') (𝔪 : Ideal (𝓞 D.host.E))
    {s : D.what₂.Tau → Matrix (Fin X.sp.rank) (Fin X.sp.rank) ℂ} {s' : D.what₂.Tau → Matrix (Fin X'.sp.rank) (Fin X'.sp.rank) ℂ}
    (e : HEq s' s) {u : D.what₂.Tau → Matrix (Fin Y.sp.rank) (Fin Y.sp.rank) ℂ}
    {u' : D.what₂.Tau → Matrix (Fin Y'.sp.rank) (Fin Y'.sp.rank) ℂ} (e' : HEq u' u)
    (f : WO (negSp X.sp) Y.sp → ℂ) (c : Cos X.lat Y.lat 𝔪 → WO (negSp X.sp) Y.sp → ℂ) :
    ∃ (f' : WO (negSp X'.sp) Y'.sp → ℂ) (c' : Cos X'.lat Y'.lat 𝔪 → WO (negSp X'.sp) Y'.sp → ℂ), HEq f' f ∧
      (∀ κ', ∃ κ, HEq (c' κ') (c κ)) ∧ (∀ κ, ∃ κ', HEq (c' κ') (c κ)) ∧
      (IsVacO ψ θ (negSp X.sp) Y.sp (fun τ => -s τ) u (X.lat : Set _) (Y.lat : Set _) f →
        IsVacO ψ θ (negSp X'.sp) Y'.sp (fun τ => -s' τ) u' (X'.lat : Set _) (Y'.lat : Set _) f') ∧
      ∀ i : AE D, (∀ κ, IsThetaAt ψ (symplO _ _) (heisO ψ _ _) i
          (latO (negSp X.sp) Y.sp (X.lat : Set _) (Y.lat : Set _) fun _ => True) 1 f (cosInd i κ) (c κ)) →
        ∀ κ, IsThetaAt ψ (symplO _ _) (heisO ψ _ _) i
          (latO (negSp X'.sp) Y'.sp (X'.lat : Set _) (Y'.lat : Set _) fun _ => True) 1 f' (cosInd i κ) (c' κ) := by
  obtain ⟨L, h1, h2, rfl⟩ := h
  obtain ⟨L', h1', h2', rfl⟩ := h'
  obtain rfl := eq_of_heq e
  obtain rfl := eq_of_heq e'
  refine ⟨f, c, HEq.rfl, fun κ => ⟨κ, HEq.rfl⟩, fun κ => ⟨κ, HEq.rfl⟩, fun hv => ?_, fun _ hi κ => hi κ⟩
  unfold IsVacO at hv ⊢
  dsimp only
  rw [isThetaFunO_negSp_reLat_reLat_eq (ψ := ψ) L h1 h2 L' h1' h2']
  exact hv

end Move

structure SameWeil {G G' : GridData L sc} (W : G.Weil) (W' : G'.Weil) : Prop where

  pl : G'.pl = G.pl

  chiH : G'.ch.chiH = G.ch.chiH

  chi : G'.ch.chi = G.ch.chi

  node : ∀ X, SameL (G.node X) (G'.node X)

  ψ : W'.ψ = W.ψ

  θ : W'.θ = W.θ

  cart : ∀ X, HEq (W'.cart X) (W.cart X)

  onb : ∀ X, HEq (W'.onb X) (W.onb X)

  om : ∀ p, HEq (W'.om p) (W.om p)

  vac : ∀ i, HEq (W'.vac i) (W.vac i)

  cos : ∀ i, (∀ κ', ∃ κ, HEq (W'.cosVec i κ') (W.cosVec i κ)) ∧ ∀ κ, ∃ κ', HEq (W'.cosVec i κ') (W.cosVec i κ)

theorem exists_sameWeil {G : GridData L sc} (W : G.Weil) : ∃ (G' : GridData L sc) (W' : G'.Weil), SameWeil W W' ∧
    ∀ X : Node, X.InRange D.R.m → (∀ j, X ≠ .grid 0 j) → (G'.Λ X : Set _) = L0c D (G'.V X) := by
  classical
  obtain ⟨sp, hsp, hL⟩ := exists_vertices G
  let G₁ : GridData L sc := ⟨G.pl, G.ch, sp⟩
  have hN : ∀ X, SameL (G.node X) (G₁.node X) := hsp
  have hS : ∀ p : Pair T, SameSp (G.pS p) (G₁.pS p) := by
    intro p
    cases p with
    | chi i j => exact (hN _).sp.neg
    | mu t i j => exact (hN _).sp
    | core i => exact (hN _).sp.neg
    | top t j => exact (hN _).sp
  have hT : ∀ p : Pair T, SameSp (G.pT p) (G₁.pT p) := by
    intro p
    cases p <;> exact (hN _).sp
  have hcS : ∀ p, G₁.chrS p = G.chrS p := fun p => by
    unfold GridData.chrS
    rw [(hS p).rank]
    rfl
  have hcT : ∀ p, G₁.chrT p = G.chrT p := fun p => by
    unfold GridData.chrT
    rw [(hT p).rank]
    rfl
  choose cart' hcart' using fun X => (hN X).sp.ex_mat (W.cart X)
  choose onb' honb' using fun X => (hN X).sp.ex_mat (W.onb X)
  choose om' hom' hom'' using fun p => ex_om (ψ := W.ψ) (hS p) (hT p) (W.om p)
  choose vac' cos' hvac' hcos1 hcos2 hvis hthe using fun i =>
    ex_vac (ψ := W.ψ) (θ := W.θ) (hN (.grid (i + 1) 0)) (hN (.grid i 0)) G.modul
      (hcart' (.grid (i + 1) 0)) (hcart' (.grid i 0)) (W.vac i) (W.cosVec i)
  let W₁ : G₁.Weil :=
    { ψ := W.ψ, ψ_std := W.ψ_std, θ := W.θ, θ_is := W.θ_is,
      cart := cart', cart_is := fun X hX τ => (hN X).sp.cart (hcart' X) (W.cart_is X hX τ),
      onb := onb', onb_is := fun X hX τ => (hN X).sp.onb (hcart' X) (honb' X) (W.onb_is X hX τ),
      om := om', om_is := fun p hp => by
        rw [hcS p, hcT p]
        exact hom'' p _ _ (W.om_is p hp),
      vac := vac', vac_is := fun i hi => hvis i (W.vac_is i hi),
      cosVec := cos', cosVec_is := by
        obtain ⟨e, he, hc⟩ := W.cosVec_is
        exact ⟨e, he, fun i hi κ => hthe i e (hc i hi) κ⟩ }
  exact ⟨G₁, W₁, {
    pl := rfl, chiH := rfl, chi := rfl, node := hN, ψ := rfl, θ := rfl, cart := hcart', onb := honb',
    om := hom', vac := hvac', cos := fun i => ⟨hcos1 i, hcos2 i⟩ }, hL⟩

theorem SameSp.perm {V V' : HSp D} (h : SameSp V V') {b : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ}
    {b' : D.what₂.Tau → Matrix (Fin V'.rank) (Fin V'.rank) ℂ} (e : HEq b' b) (σ' : D.what₂.Tau → Equiv.Perm (Fin V'.rank)) :
    ∃ σ : D.what₂.Tau → Equiv.Perm (Fin V.rank),
      HEq (fun τ => (b' τ).submatrix id (σ' τ)) (fun τ => (b τ).submatrix id (σ τ)) := by
  obtain ⟨L, h1, h2, rfl⟩ := h
  obtain rfl := eq_of_heq e
  exact ⟨σ', HEq.rfl⟩

end GlobalTheory.GridJoin

namespace GlobalTheory.GridJoin

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {sc : GlobalTheory.ChiGrid.Consts}

structure NodeMatch (N : GlobalTheory.Grid.Node D) {G' : GlobalTheory.ChiGrid.GridData R.toLevCh sc} (W : G'.Weil) (X : GlobalTheory.ChiGrid.Node) :
    Prop where

  sp : SameSp (G'.V X) N.V

  lat : HEq N.Λ (G'.Λ X)

  cart : HEq (Formalism.IndefR.Links.cart N.M) (W.cart X)

  onb : X ≠ .top 0 → ∃ σ : D.what₂.Tau → Equiv.Perm (Fin (G'.V X).rank),
    HEq (Formalism.IndefR.Links.onb N.M) fun τ => (W.onb X τ).submatrix id (σ τ)

structure SpMatch (G : GlobalTheory.Grid.GridPre R) {G' : GlobalTheory.ChiGrid.GridData R.toLevCh sc} (W : G'.Weil) : Prop where

  row : ∀ j, j ≤ D.R.m → NodeAgree (G.V 0 j) W (.grid 0 j)

  vert : ∀ i j, i ≤ D.R.m → j ≤ D.R.m → NodeMatch (G.V i j) W (.grid i j)

  core : ∀ i, i ≤ D.R.m → NodeMatch (G.P i) W (.core i)

  top : ∀ j, j ≤ D.R.m → NodeMatch (G.Xp j) W (.top j)

  q0 : G.q0 = GlobalTheory.ChiGrid.q0 D

  w0 : G.w0 = G'.pl.w G'.pl.v0

  e0 : G.e0 = G'.pl.depth sc G'.pl.v0

  places : G.toPlaceDat.W R.Pg = G'.pl.W0

  lvl : G.lvl R = G'.modul

  chiH : ∀ i, 1 ≤ i → i ≤ D.R.m → G.chiH i = G'.ch.chiH i

  chi : ∀ i, 1 ≤ i → i ≤ D.R.m → G.chi i = G'.ch.chi i

def Match (G : GlobalTheory.Grid.GridPre R) {G' : GlobalTheory.ChiGrid.GridData R.toLevCh sc} (W : G'.Weil) : Prop :=
  SpMatch G W ∧ ArrAgree G W

theorem SameWeil.over {G G' : GlobalTheory.ChiGrid.GridData R.toLevCh sc} {W : G.Weil} {W' : G'.Weil} (h : SameWeil W W')
    (hW : W.Over R) : W'.Over R :=
  ⟨h.ψ.trans hW.ψ, h.θ.trans hW.θ, fun j hj => (h.cart _).trans (hW.cartY j hj), (h.cart _).trans hW.cartX,
    fun j hj => (h.onb _).trans (hW.onbY j hj), (h.onb _).trans hW.onbX,
    fun t k hk => (h.om _).trans (hW.omY t k hk), fun t k hk => (h.om _).trans (hW.omX t k hk)⟩

theorem NodeAgree.nodeMatch_of {N : GlobalTheory.Grid.Node D} {G G' : GlobalTheory.ChiGrid.GridData R.toLevCh sc} {W : G.Weil} {W₁ W₂ : G'.Weil}
    (h : SameWeil W W₁) (hc : W₂.cart = W₁.cart) {X : GlobalTheory.ChiGrid.Node}
    (hb : X ≠ .top 0 → ∀ τ, ∃ σ : Equiv.Perm (Fin (G'.V X).rank), W₂.onb X τ = (W₁.onb X τ).submatrix id σ)
    (a : NodeAgree N W₂ X) : NodeMatch N W X := by
  have hN := h.node X
  refine ⟨?_, a.lat.trans hN.lat, a.cart.trans ((heq_of_eq (congrFun hc X)).trans (h.cart X)), fun hX => ?_⟩
  · rw [a.sp]
    exact hN.sp
  · choose σ₁ hσ₁ using hb hX
    obtain ⟨σ, hσ⟩ := hN.sp.perm (h.onb X) σ₁
    exact ⟨σ, a.onb.trans ((heq_of_eq (funext hσ₁)).trans hσ)⟩

theorem ArrAgree.of_sameWeil {G₀ : GlobalTheory.Grid.GridPre R} {G G' : GlobalTheory.ChiGrid.GridData R.toLevCh sc} {W : G.Weil} {W₁ W₂ : G'.Weil}
    (h : SameWeil W W₁) (ho : W₂.om = W₁.om) (hv : W₂.vac = W₁.vac) (hc : W₂.cosVec = W₁.cosVec) (a : ArrAgree G₀ W₂) :
    ArrAgree G₀ W := by
  refine ⟨fun i j hi hj => (a.omX i j hi hj).trans ((heq_of_eq (congrFun ho _)).trans (h.om _)),
    fun t i j hi hj => (a.omT t i j hi hj).trans ((heq_of_eq (congrFun ho _)).trans (h.om _)),
    fun t j hj => (a.omC t j hj).trans ((heq_of_eq (congrFun ho _)).trans (h.om _)),
    fun i hi => (a.omD i hi).trans ((heq_of_eq (congrFun ho _)).trans (h.om _)),
    fun i hi => (a.vacX i hi).trans ((heq_of_eq (congrFun hv i)).trans (h.vac i)),
    fun i hi => ⟨fun c => ?_, fun κ => ?_⟩⟩
  · obtain ⟨κ', hκ'⟩ := (a.cos i hi).1 c
    obtain ⟨κ, hκ⟩ := (h.cos i).1 κ'
    exact ⟨κ, (hκ'.trans (heq_of_eq (congrFun (congrFun hc i) κ'))).trans hκ⟩
  · obtain ⟨κ', hκ'⟩ := (h.cos i).2 κ
    obtain ⟨c, hc'⟩ := (a.cos i hi).2 κ'
    exact ⟨c, (hc'.trans (heq_of_eq (congrFun (congrFun hc i) κ'))).trans hκ'⟩

end GlobalTheory.GridJoin
