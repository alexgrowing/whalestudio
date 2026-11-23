import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RhoDetPrimeEqMuTildeMulChiPow

noncomputable section

namespace GlobalTheory.Mem

open Formalism.BasicNotions NumberField IsDedekindDomain

structure RowsRest (B : Base) (C : Cols B) where
  muAt : B.places.Pl → C.Tup
  muAt_conj : ∀ w, muAt (B.places.conj w) = muAt w
  muTw : B.places.Pl → C.Tup
  muTw_conj : ∀ w, muTw (B.places.conj w) = muTw w
  muAt_or : ∀ w, muAt w = C.mu0 ∨ muAt w = muTw w
  EE : Type
  [instEE : NormedAddCommGroup EE]
  [instEEi : InnerProductSpace ℂ EE]
  [instEEf : FiniteDimensional ℂ EE]
  Drows : ℕ
  onb : OrthonormalBasis (Fin Drows) ℂ EE
  Dall : ℕ
  delp : ℝ
  delp_le_one : delp ≤ 1
  D_eq : (Drows : ℝ) = (1 - delp) * Dall
  EE0 : Type
  [instEE0 : NormedAddCommGroup EE0]
  [instEE0i : InnerProductSpace ℂ EE0]
  [instEE0f : FiniteDimensional ℂ EE0]
  D0 : ℕ
  onb0 : OrthonormalBasis (Fin D0) ℂ EE0
  FT : Type
  [instFT : Fintype FT]
  [instFTd : DecidableEq FT]
  ft : Fin Drows → FT
  ft0 : Fin D0 → FT
  Amb : C.Tup → Type
  [instAmb : ∀ μ, NormedAddCommGroup (Amb μ)]
  [instAmbi : ∀ μ, InnerProductSpace ℂ (Amb μ)]
  [instAmbf : ∀ μ, FiniteDimensional ℂ (Amb μ)]
  Mult : C.Tup → ℕ → Type
  [instMult : ∀ μ j, NormedAddCommGroup (Mult μ j)]
  [instMulti : ∀ μ j, InnerProductSpace ℂ (Mult μ j)]
  [instMultf : ∀ μ j, FiniteDimensional ℂ (Mult μ j)]
  multZero : ∀ μ, Mult μ 0 ≃ₗᵢ[ℂ] EE
  multTop : ∀ μ, Mult μ B.R.m ≃ₗᵢ[ℂ] Amb μ
  io : ∀ μ j, Mult μ (j + 1) →ₗ[ℂ] Mult μ j
  Mtilde : ∀ μ, Rows.OLat B.O (B.embLL.comp B.OtoLL) (Amb μ)
  eOp : ∀ μ, Amb μ →ₗ[ℂ] Amb μ
  eOp_idem : ∀ μ, eOp μ ∘ₗ eOp μ = eOp μ
  eOp_sa : ∀ μ, (eOp μ).IsSymmetric
  Mu : B.Word → Type
  [instMu : ∀ u, NormedAddCommGroup (Mu u)]
  [instMui : ∀ u, InnerProductSpace ℂ (Mu u)]
  [instMuf : ∀ u, FiniteDimensional ℂ (Mu u)]
  perCol : ∀ u (μ : C.Tup), Mu u → Amb μ → ℂ
  Bu : ∀ u, Mu u → EE → ℂ
  ze : B.Word → C.Tup → B.LLˣ
  rowsRest_wordColumnUnit_baseTuple : ∀ u, ze u C.mu0 = 1
  Mj : ℕ → Type
  [instMj : ∀ j, NormedAddCommGroup (Mj j)]
  [instMji : ∀ j, InnerProductSpace ℂ (Mj j)]
  [instMjf : ∀ j, FiniteDimensional ℂ (Mj j)]
  MjLat : ∀ j, Rows.OLat B.O (B.embLL.comp B.OtoLL) (Mj j)
  kaBig : ∀ j, Tau B.R → Fin (B.R.sigW j).1 → ℤ
  kaSmall : ∀ j, Tau B.R → Fin (B.R.sigW j).2 → ℤ
  Mt : C.Tup → ℕ → Type
  [instMt : ∀ μ j, NormedAddCommGroup (Mt μ j)]
  [instMti : ∀ μ j, InnerProductSpace ℂ (Mt μ j)]
  [instMtf : ∀ μ j, FiniteDimensional ℂ (Mt μ j)]
  MtLat : ∀ μ j, Rows.OLat B.O (B.embLL.comp B.OtoLL) (Mt μ j)
  MtL : C.Tup → ℕ → Type
  [instMtL : ∀ μ j, AddCommGroup (MtL μ j)]
  [instMtLm : ∀ μ j, Module B.LL (MtL μ j)]
  jMt : ∀ μ j, MtL μ j →ₛₗ[B.embLL] Mt μ j
  jMt_basis : ∀ μ j, ∀ b : Module.Basis (Module.Free.ChooseBasisIndex B.LL (MtL μ j)) B.LL (MtL μ j),
    LinearIndependent ℂ (fun i => jMt μ j (b i)) ∧ Submodule.span ℂ (Set.range (fun i => jMt μ j (b i))) = ⊤
  MtLat_sub : ∀ μ j, ∀ x ∈ (MtLat μ j).gen, x ∈ Set.range (jMt μ j)
  eMt : ∀ μ j, Mt μ j →ₗ[ℂ] Mt μ j
  eMt_idem : ∀ μ j, eMt μ j ∘ₗ eMt μ j = eMt μ j
  eMt_sa : ∀ μ j, (eMt μ j).IsSymmetric
  eMt_LL : ∀ μ j (x : MtL μ j), ∃ y : MtL μ j, jMt μ j y = eMt μ j (jMt μ j x)
  thetaP : ∀ μ j, Mt μ j →ₗ[ℂ] Mj j
  isot : ∀ j, FT → Submodule ℂ (Mj j)
  lamP : C.Tup → ℕ → FT → ℝ
  Ij : C.Tup → ℕ → B.places.Pl → ℤ
  jw : C.Tup → ℕ → B.places.Pl → ℤ
  etaJ : ℕ → B.places.Pl → ℚ
  etaJ_nonneg : ∀ j w, 0 ≤ etaJ j w
  shaLen : ℕ → ℕ → ℚ
  shaLen_nonneg : ∀ l e, 0 ≤ shaLen l e
  eMu : ∀ u, Mu u ≃ₗ[ℂ] (C.mem u).A.Mram
  eMt0 : ∀ u, (C.mem u).P.Mt ≃ₗ[ℂ] Amb C.mu0
  perCol_base_eq_PtilCol : ∀ u (φ : Mu u) (F : Amb C.mu0),
    perCol u C.mu0 φ F = (C.mem u).P.PtilCol ((eMu u φ : (C.mem u).A.Mram) :
      (C.mem u).C.cls 0 → (C.mem u).C.Y 0 → ℂ) ((eMt0 u).symm F)
  Bu_linL : ∀ u (F : EE), IsLinearMap ℂ (fun φ : Mu u => Bu u φ F)
  Bu_linR : ∀ u (φ : Mu u), IsLinearMap ℂ (fun F : EE => Bu u φ F)
  eMtTw : ∀ u μ, (C.PTw u μ).Mt ≃ₗ[ℂ] Amb μ
  perCol_tie : ∀ u μ, μ ≠ C.mu0 → ∀ (φ : Mu u) (F : Amb μ), perCol u μ φ F =
    (C.PTw u μ).PtilCol (C.e0Tw u μ ((eMu u φ : (C.mem u).A.Mram) : (C.mem u).C.cls 0 → (C.mem u).C.Y 0 → ℂ))
      ((eMtTw u μ).symm F)
  eMu_isom : ∀ u (φ ψ : Mu u), inner ℂ φ ψ =
    (C.fm u).ipC 0 ((eMu u φ : (C.mem u).A.Mram) : (C.mem u).C.cls 0 → (C.mem u).C.Y 0 → ℂ)
      ((eMu u ψ : (C.mem u).A.Mram) : (C.mem u).C.cls 0 → (C.mem u).C.Y 0 → ℂ)

attribute [instance] RowsRest.instEE RowsRest.instEEi RowsRest.instEEf RowsRest.instEE0 RowsRest.instEE0i RowsRest.instEE0f RowsRest.instFT RowsRest.instFTd RowsRest.instAmb RowsRest.instAmbi RowsRest.instAmbf RowsRest.instMult RowsRest.instMulti RowsRest.instMultf RowsRest.instMu RowsRest.instMui RowsRest.instMuf RowsRest.instMj RowsRest.instMji RowsRest.instMjf RowsRest.instMt RowsRest.instMti RowsRest.instMtf RowsRest.instMtL RowsRest.instMtLm

@[reducible] def RowsRest.what₂ {B : Base} {C : Cols B} (W : RowsRest B C) : Rows.Data B.R where
  LL := B.LL
  embLL := B.embLL
  places := B.places
  O := B.O
  OtoLL := B.OtoLL
  Tau := Tau B.R
  card_Tau := card_Tau B.host
  Tup := C.Tup
  mu0 := C.mu0
  muStar := C.muStar
  muStar' := C.muStar'
  Dstar := B.Dstar
  restRowsFiniteGroupCard := B.toPre.restRowsFiniteGroupCard
  restRowsFiniteGroupCard_pos := B.toPre.restRowsFiniteGroupCard_pos
  Word := B.Word
  muAt := W.muAt
  muAt_conj := W.muAt_conj
  muTw := W.muTw
  muTw_conj := W.muTw_conj
  muAt_or := W.muAt_or
  EE := W.EE
  Drows := W.Drows
  onb := W.onb
  Dall := W.Dall
  delp := W.delp
  delp_le_one := W.delp_le_one
  D_eq := W.D_eq
  EE0 := W.EE0
  D0 := W.D0
  onb0 := W.onb0
  FT := W.FT
  ft := W.ft
  ft0 := W.ft0
  Amb := W.Amb
  Mult := W.Mult
  multZero := W.multZero
  multTop := W.multTop
  io := W.io
  Mtilde := W.Mtilde
  eOp := W.eOp
  eOp_idem := W.eOp_idem
  eOp_sa := W.eOp_sa
  Mu := W.Mu
  perCol := W.perCol
  Bu := W.Bu
  ze := W.ze
  rowsRest_wordColumnUnit_baseTuple := W.rowsRest_wordColumnUnit_baseTuple
  Mj := W.Mj
  MjLat := W.MjLat
  kaBig := W.kaBig
  kaSmall := W.kaSmall
  Mt := W.Mt
  MtLat := W.MtLat
  MtL := W.MtL
  jMt := W.jMt
  jMt_basis := W.jMt_basis
  MtLat_sub := W.MtLat_sub
  eMt := W.eMt
  eMt_idem := W.eMt_idem
  eMt_sa := W.eMt_sa
  eMt_LL := W.eMt_LL
  thetaP := W.thetaP
  isot := W.isot
  lamP := W.lamP
  Ij := W.Ij
  jw := W.jw
  etaJ := W.etaJ
  etaJ_nonneg := W.etaJ_nonneg
  shaLen := W.shaLen
  shaLen_nonneg := W.shaLen_nonneg

instance {B : Base} {C : Cols B} (W : RowsRest B C) : NumberField W.what₂.LL := B.nfLL
instance {B : Base} {C : Cols B} (W : RowsRest B C) : StarRing W.what₂.LL := B.starLL
instance {B : Base} {C : Cols B} (W : RowsRest B C) : Fintype W.what₂.Word := B.wordFin

end GlobalTheory.Mem

end
