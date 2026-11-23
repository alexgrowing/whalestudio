import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.SignAtBasePlaceEqEmbedding
import Formalism.LocalToGlobal.IndefiniteReal.HeckeNonvanishing.Imports

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Rows NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 2000000

namespace GlobalTheory.TwInputs.Move

section Defs

variable {R : Ranks} {H : Host R}

set_option genInjectivity false in
set_option genSizeOfSpec false in

structure RestRows (rows₀ : Rows.Data R) where
  LL : Type
  instLL : Field LL
  embLL : LL →+* ℂ
  places : Places LL
  O : Type
  instO : CommRing O
  OtoLL : O →+* LL
  Tup : Type
  mu0 : Tup
  muStar : Tup
  muStar' : Tup
  muAt : places.Pl → Tup
  muAt_conj : ∀ w, muAt (places.conj w) = muAt w
  muTw : places.Pl → Tup
  muTw_conj : ∀ w, muTw (places.conj w) = muTw w
  muAt_or : ∀ w, muAt w = mu0 ∨ muAt w = muTw w
  EE : Type
  instEE : NormedAddCommGroup EE
  instEEi : InnerProductSpace ℂ EE
  instEEf : FiniteDimensional ℂ EE
  Drows : ℕ
  onb : OrthonormalBasis (Fin Drows) ℂ EE
  Dall : ℕ
  delp : ℝ
  delp_le_one : delp ≤ 1
  D_eq : (Drows : ℝ) = (1 - delp) * Dall
  EE0 : Type
  instEE0 : NormedAddCommGroup EE0
  instEE0i : InnerProductSpace ℂ EE0
  instEE0f : FiniteDimensional ℂ EE0
  D0 : ℕ
  onb0 : OrthonormalBasis (Fin D0) ℂ EE0
  FT : Type
  instFT : Fintype FT
  instFTd : DecidableEq FT
  ft : Fin Drows → FT
  ft0 : Fin D0 → FT
  Dstar : ℝ
  Amb : Tup → Type
  instAmb : ∀ μ, NormedAddCommGroup (Amb μ)
  instAmbi : ∀ μ, InnerProductSpace ℂ (Amb μ)
  instAmbf : ∀ μ, FiniteDimensional ℂ (Amb μ)
  Mult : Tup → ℕ → Type
  instMult : ∀ μ j, NormedAddCommGroup (Mult μ j)
  instMulti : ∀ μ j, InnerProductSpace ℂ (Mult μ j)
  instMultf : ∀ μ j, FiniteDimensional ℂ (Mult μ j)
  multZero : ∀ μ, Mult μ 0 ≃ₗᵢ[ℂ] EE
  multTop : ∀ μ, Mult μ R.m ≃ₗᵢ[ℂ] Amb μ
  io : ∀ μ j, Mult μ (j + 1) →ₗ[ℂ] Mult μ j
  Mtilde : ∀ μ, OLat O (embLL.comp OtoLL) (Amb μ)
  eOp : ∀ μ, Amb μ →ₗ[ℂ] Amb μ
  eOp_idem : ∀ μ, eOp μ ∘ₗ eOp μ = eOp μ
  eOp_sa : ∀ μ, (eOp μ).IsSymmetric
  restRowsFiniteGroupCard : ℕ
  restRowsFiniteGroupCard_pos : 0 < restRowsFiniteGroupCard
  Word : Type
  Mu : Word → Type
  instMu : ∀ u, NormedAddCommGroup (Mu u)
  instMui : ∀ u, InnerProductSpace ℂ (Mu u)
  instMuf : ∀ u, FiniteDimensional ℂ (Mu u)
  perCol : ∀ u (μ : Tup), Mu u → Amb μ → ℂ
  Bu : ∀ u, Mu u → EE → ℂ
  ze : Word → Tup → LLˣ
  rowsRest_wordColumnUnit_baseTuple : ∀ u, ze u mu0 = 1
  Mj : ℕ → Type
  instMj : ∀ j, NormedAddCommGroup (Mj j)
  instMji : ∀ j, InnerProductSpace ℂ (Mj j)
  instMjf : ∀ j, FiniteDimensional ℂ (Mj j)
  MjLat : ∀ j, OLat O (embLL.comp OtoLL) (Mj j)
  kaBig : ∀ j, rows₀.Tau → Fin (R.sigW j).1 → ℤ
  kaSmall : ∀ j, rows₀.Tau → Fin (R.sigW j).2 → ℤ
  Mt : Tup → ℕ → Type
  instMt : ∀ μ j, NormedAddCommGroup (Mt μ j)
  instMti : ∀ μ j, InnerProductSpace ℂ (Mt μ j)
  instMtf : ∀ μ j, FiniteDimensional ℂ (Mt μ j)
  MtLat : ∀ μ j, OLat O (embLL.comp OtoLL) (Mt μ j)
  MtL : Tup → ℕ → Type
  instMtL : ∀ μ j, AddCommGroup (MtL μ j)
  instMtLm : ∀ μ j, Module LL (MtL μ j)
  jMt : ∀ μ j, MtL μ j →ₛₗ[embLL] Mt μ j
  jMt_basis : ∀ μ j, ∀ b : Module.Basis (Module.Free.ChooseBasisIndex LL (MtL μ j)) LL (MtL μ j),
    LinearIndependent ℂ (fun i => jMt μ j (b i)) ∧ Submodule.span ℂ (Set.range (fun i => jMt μ j (b i))) = ⊤
  MtLat_sub : ∀ μ j, ∀ x ∈ (MtLat μ j).gen, x ∈ Set.range (jMt μ j)
  eMt : ∀ μ j, Mt μ j →ₗ[ℂ] Mt μ j
  eMt_idem : ∀ μ j, eMt μ j ∘ₗ eMt μ j = eMt μ j
  eMt_sa : ∀ μ j, (eMt μ j).IsSymmetric
  eMt_LL : ∀ μ j (x : MtL μ j), ∃ y : MtL μ j, jMt μ j y = eMt μ j (jMt μ j x)
  thetaP : ∀ μ j, Mt μ j →ₗ[ℂ] Mj j
  isot : ∀ j, FT → Submodule ℂ (Mj j)
  lamP : Tup → ℕ → FT → ℝ
  Ij : Tup → ℕ → places.Pl → ℤ
  jw : Tup → ℕ → places.Pl → ℤ
  etaJ : ℕ → places.Pl → ℚ
  etaJ_nonneg : ∀ j w, 0 ≤ etaJ j w
  shaLen : ℕ → ℕ → ℚ
  shaLen_nonneg : ∀ l e, 0 ≤ shaLen l e

def overRows (rows₀ : Rows.Data R) (r : RestRows rows₀) : Rows.Data R where
  LL := r.LL
  instLL := r.instLL
  embLL := r.embLL
  places := r.places
  O := r.O
  instO := r.instO
  OtoLL := r.OtoLL
  Tau := rows₀.Tau
  instTau := rows₀.instTau
  card_Tau := rows₀.card_Tau
  Tup := r.Tup
  mu0 := r.mu0
  muStar := r.muStar
  muStar' := r.muStar'
  muAt := r.muAt
  muAt_conj := r.muAt_conj
  muTw := r.muTw
  muTw_conj := r.muTw_conj
  muAt_or := r.muAt_or
  EE := r.EE
  instEE := r.instEE
  instEEi := r.instEEi
  instEEf := r.instEEf
  Drows := r.Drows
  onb := r.onb
  Dall := r.Dall
  delp := r.delp
  delp_le_one := r.delp_le_one
  D_eq := r.D_eq
  EE0 := r.EE0
  instEE0 := r.instEE0
  instEE0i := r.instEE0i
  instEE0f := r.instEE0f
  D0 := r.D0
  onb0 := r.onb0
  FT := r.FT
  instFT := r.instFT
  instFTd := r.instFTd
  ft := r.ft
  ft0 := r.ft0
  Dstar := r.Dstar
  Amb := r.Amb
  instAmb := r.instAmb
  instAmbi := r.instAmbi
  instAmbf := r.instAmbf
  Mult := r.Mult
  instMult := r.instMult
  instMulti := r.instMulti
  instMultf := r.instMultf
  multZero := r.multZero
  multTop := r.multTop
  io := r.io
  Mtilde := r.Mtilde
  eOp := r.eOp
  eOp_idem := r.eOp_idem
  eOp_sa := r.eOp_sa
  restRowsFiniteGroupCard := r.restRowsFiniteGroupCard
  restRowsFiniteGroupCard_pos := r.restRowsFiniteGroupCard_pos
  Word := r.Word
  Mu := r.Mu
  instMu := r.instMu
  instMui := r.instMui
  instMuf := r.instMuf
  perCol := r.perCol
  Bu := r.Bu
  ze := r.ze
  rowsRest_wordColumnUnit_baseTuple := r.rowsRest_wordColumnUnit_baseTuple
  Mj := r.Mj
  instMj := r.instMj
  instMji := r.instMji
  instMjf := r.instMjf
  MjLat := r.MjLat
  kaBig := r.kaBig
  kaSmall := r.kaSmall
  Mt := r.Mt
  instMt := r.instMt
  instMti := r.instMti
  instMtf := r.instMtf
  MtLat := r.MtLat
  MtL := r.MtL
  instMtL := r.instMtL
  instMtLm := r.instMtLm
  jMt := r.jMt
  jMt_basis := r.jMt_basis
  MtLat_sub := r.MtLat_sub
  eMt := r.eMt
  eMt_idem := r.eMt_idem
  eMt_sa := r.eMt_sa
  eMt_LL := r.eMt_LL
  thetaP := r.thetaP
  isot := r.isot
  lamP := r.lamP
  Ij := r.Ij
  jw := r.jw
  etaJ := r.etaJ
  etaJ_nonneg := r.etaJ_nonneg
  shaLen := r.shaLen
  shaLen_nonneg := r.shaLen_nonneg

variable {rows₀ : Rows.Data R}

set_option genInjectivity false in
set_option genSizeOfSpec false in

structure RestN (N₀ : NData R H rows₀) (what₂ : Rows.Data R) where
  ldat : ∀ (p : ℕ) [Fact p.Prime], Formalism.GaloisCohomology.LData H.E N₀.Om p
  sha_eq : ∀ (p : ℕ) [Fact p.Prime] (e : ℕ), 0 < e → e < R.t → ∀ n : ℕ,
    Formalism.GaloisCohomology.shaLen (ldat p) (e : ℤ) = (n : ℕ∞) → what₂.shaLen p e = (n : ℚ)
  Loc : Type
  l : Loc → ℕ
  lPrime : ∀ i, Fact (l i).Prime
  j : Loc → ℕ
  j_range : ∀ i, 1 ≤ j i ∧ j i ≤ R.m
  mu : Loc → what₂.Tup
  w : Loc → what₂.places.Pl
  w_l : ∀ i, what₂.places.resChar (w i) = l i
  mu_w : ∀ i, mu i = what₂.muTw (w i)
  w_tw : ∀ i, what₂.muAt (w i) ≠ what₂.mu0
  locs : ℕ → what₂.places.Pl → Finset Loc
  locs_mem : ∀ j' w' i, i ∈ locs j' w' ↔ j i = j' ∧ w i = w'
  O : Loc → Type
  instO : ∀ i, CommRing (O i)
  domO : ∀ i, IsDomain (O i)
  dvrO : ∀ i, IsDiscreteValuationRing (O i)
  algO : ∀ i, Algebra ℤ_[l i] (O i)
  finO : ∀ i, Module.Finite ℤ_[l i] (O i)
  topO : ∀ i, TopologicalSpace (O i)
  trO : ∀ i, IsTopologicalRing (O i)
  O_adic : ∀ i, IsAdic (IsLocalRing.maximalIdeal (O i))
  O_complete : ∀ i, IsAdicComplete (IsLocalRing.maximalIdeal (O i)) (O i)
  embK : ∀ i, what₂.LL →+* FractionRing (O i)
  embK_w : ∀ i (x : what₂.LL), 0 ≤ what₂.places.val (w i) x ↔
    embK i x ∈ (algebraMap (O i) (FractionRing (O i))).range
  X : Loc → Type
  finX : ∀ i, Fintype (X i)
  neX : ∀ i, Nonempty (X i)
  T : ∀ i, Subalgebra (O i) (X i → O i)
  T_local : ∀ i, IsLocalRing (T i)
  T_sep : ∀ i (x y : X i), x ≠ y → ∃ f ∈ T i, (f : X i → O i) x ≠ (f : X i → O i) y
  Mt : Loc → Type
  acgMt : ∀ i, AddCommGroup (Mt i)
  modMt : ∀ i, Module (O i) (Mt i)
  freeMt : ∀ i, Module.Free (O i) (Mt i)
  finMt : ∀ i, Module.Finite (O i) (Mt i)
  act : ∀ i, T i →ₐ[O i] Module.End (O i) (Mt i)
  act_inj : ∀ i, Function.Injective (act i)
  prMt : ∀ i, what₂.MtL (mu i) (j i) →ₛₗ[embK i] TensorProduct (O i) (FractionRing (O i)) (Mt i)
  prMt_span : ∀ i, Submodule.span (FractionRing (O i)) (Set.range (prMt i)) = ⊤
  prMt_lat : ∀ i, Submodule.span (O i)
      (prMt i '' {x | what₂.jMt (mu i) (j i) x ∈ (what₂.MtLat (mu i) (j i)).gen}) =
    LinearMap.range (TensorProduct.mk (O i) (FractionRing (O i)) (Mt i) 1)
  eig_ne : ∀ i x, heckeEig (T i) (act i) x ≠ ⊥
  chi : ∀ i, ℕ → (G H.E N₀.Om →* (O i)ˣ)
  chi_cont : ∀ i c, Continuous (fun g => ((chi i c g : (O i)ˣ) : O i))
  chi_def : ∀ i c, 1 ≤ c → c ≤ R.t → chi i c = chi i 1 *
    ((Units.map (algebraMap ℤ_[l i] (O i)).toMonoidHom).comp
      (cycZ (F := H.E) (Ω := N₀.Om) (l i))) ^ (-((c : ℤ) - 1))
  Z : ∀ i, Finset (X i)
  Zgood : ∀ i, Finset (X i)
  s0 : Loc → ℕ
  restNLevelExponent_of_odd : ∀ i, l i ≠ 2 → s0 i = max 1 (H.QS.factorization (l i))
  restNLevelExponent_of_two : ∀ i, l i = 2 → s0 i = H.QS.factorization 2
  S : Loc → Finset (HeightOneSpectrum (𝓞 H.E))
  Q : Loc → Finset (HeightOneSpectrum (𝓞 H.E))
  SQ_split : ∀ i v, v ∈ S i ∨ v ∈ Q i → IsSplitPl H v
  SQ_disj : ∀ i, Disjoint (S i) (Q i)
  SQ_l : ∀ i v, v ∈ S i ∨ v ∈ Q i → v ∉ placesOver H.E (l i)
  S_def : ∀ i v, v ∈ S i ↔ (v ∈ placesOver H.E (H.g 0) ∨ v ∈ placesOver H.E (H.g 1) ∨
      v ∈ placesOver H.E (if l i = H.pde then H.pde' else H.pde)) ∧ v ∉ placesOver H.E (l i)
  hT : ∀ i, HeightOneSpectrum (𝓞 H.E) → ℕ → T i
  T_gen : ∀ i, Algebra.adjoin (O i) {f : X i → O i | ∃ v k, IsSplitPl H v ∧
      v ∉ placesOver H.E (l i) ∧ v ∉ S i ∧ v ∉ Q i ∧ 1 ≤ k ∧ k ≤ R.nV ∧ f = (hT i v k : X i → O i)} =
    T i
  gam0 : Loc → HeightOneSpectrum (𝓞 H.E) → G H.E N₀.Om
  locNd_chebotarevPlace_mem : ∀ i v, gam0 i v ∈ Ine (F := H.E) (N₀.plOm.1 v)
  restN_tameGenerator_generates : ∀ i v, v ∈ S i ∨ v ∈ Q i → TameGenAt (N₀.plOm.1 v) (gam0 i v)
  chi_ram_Q : ∀ i, ∀ v ∈ Q i, ∃ g ∈ Ine (F := H.E) (N₀.plOm.1 v), chi i 1 g ≠ 1
  Bj : Loc → Type
  acgBj : ∀ i, AddCommGroup (Bj i)
  modBj : ∀ i, Module (O i) (Bj i)
  freeBj : ∀ i, Module.Free (O i) (Bj i)
  finBj : ∀ i, Module.Finite (O i) (Bj i)
  lab : ∀ k, what₂.FT → N₀.PlG k → Polynomial (ZMod (H.g k))
  lab_monic : ∀ k σ v, (lab k σ v).Monic ∧ (lab k σ v).natDegree = R.r
  chiT : ∀ k, N₀.PlG k → Fin R.m → (ZMod (H.g k))ˣ
  restN_card_levelGroup_eq : what₂.restRowsFiniteGroupCard = ∏ k : Fin 2, (Nat.card (GL (Fin R.r) (ZMod (H.g k)))) ^ R.f

def overN (N₀ : NData R H rows₀) (what₂ : Rows.Data R) (r : RestN N₀ what₂) : NData R H what₂ where
  Om := N₀.Om
  instOm := N₀.instOm
  algOm := N₀.algOm
  acOm := N₀.acOm
  plOm := N₀.plOm
  ldat := r.ldat
  sha_eq := r.sha_eq
  Loc := r.Loc
  l := r.l
  lPrime := r.lPrime
  j := r.j
  j_range := r.j_range
  mu := r.mu
  w := r.w
  w_l := r.w_l
  mu_w := r.mu_w
  w_tw := r.w_tw
  locs := r.locs
  locs_mem := r.locs_mem
  O := r.O
  instO := r.instO
  domO := r.domO
  dvrO := r.dvrO
  algO := r.algO
  finO := r.finO
  topO := r.topO
  trO := r.trO
  O_adic := r.O_adic
  O_complete := r.O_complete
  embK := r.embK
  embK_w := r.embK_w
  X := r.X
  finX := r.finX
  neX := r.neX
  T := r.T
  T_local := r.T_local
  T_sep := r.T_sep
  Mt := r.Mt
  acgMt := r.acgMt
  modMt := r.modMt
  freeMt := r.freeMt
  finMt := r.finMt
  act := r.act
  act_inj := r.act_inj
  prMt := r.prMt
  prMt_span := r.prMt_span
  prMt_lat := r.prMt_lat
  eig_ne := r.eig_ne
  chi := r.chi
  chi_cont := r.chi_cont
  chi_def := r.chi_def
  Z := r.Z
  Zgood := r.Zgood
  s0 := r.s0
  restNLevelExponent_of_odd := r.restNLevelExponent_of_odd
  restNLevelExponent_of_two := r.restNLevelExponent_of_two
  S := r.S
  Q := r.Q
  SQ_split := r.SQ_split
  SQ_disj := r.SQ_disj
  SQ_l := r.SQ_l
  S_def := r.S_def
  hT := r.hT
  T_gen := r.T_gen
  gam0 := r.gam0
  locNd_chebotarevPlace_mem := r.locNd_chebotarevPlace_mem
  restN_tameGenerator_generates := r.restN_tameGenerator_generates
  chi_ram_Q := r.chi_ram_Q
  Bj := r.Bj
  acgBj := r.acgBj
  modBj := r.modBj
  freeBj := r.freeBj
  finBj := r.finBj
  g_split := N₀.g_split
  PlG := N₀.PlG
  finPlG := N₀.finPlG
  card_PlG := N₀.card_PlG
  lab := r.lab
  lab_monic := r.lab_monic
  chiT := r.chiT
  restN_card_levelGroup_eq := r.restN_card_levelGroup_eq

variable [NumberField rows₀.LL] [StarRing rows₀.LL] {LL₀ : IntermediateField ℚ rows₀.LL} {N₀ : NData R H rows₀}

set_option genInjectivity false in
set_option genSizeOfSpec false in

structure RestX (X₀ : NTw R H rows₀ LL₀ N₀) (what₂ : Rows.Data R) [NumberField what₂.LL] [StarRing what₂.LL]
    (LL0 : IntermediateField ℚ what₂.LL) (nR : RestN N₀ what₂) where
  emb0 : ∀ i, LL0 →+* FractionRing (X₀.O0 i)
  emb0b : ∀ i, LL0 →+* FractionRing (X₀.O0 i)
  restX_coefficientEmbedding_conj : ∀ i (x y : LL0), (y : what₂.LL) = star (x : what₂.LL) → emb0b i x = emb0 i y
  topO : ∀ i, TopologicalSpace (X₀.O i)
  trO : ∀ i, IsTopologicalRing (X₀.O i)
  O_adic : ∀ i, IsAdic (IsLocalRing.maximalIdeal (X₀.O i))
  ThetaPsi : ∀ i j b k, Finset (HeightOneSpectrum (𝓞 H.E)) → (G H.E N₀.Om →* (X₀.Ok i k)ˣ) →
    Submodule (X₀.Ok i k) (TensorProduct (X₀.O i) (X₀.Ok i k) (X₀.B i j b))
  ThetaPsi_one : ∀ i j b k, ThetaPsi i j b k ∅ 1 = (X₀.Theta i j b).baseChange (X₀.Ok i k)
  finLam : ∀ i, Fintype (X₀.abelian₂ i)
  jL : ∀ i, X₀.abelian₂ i → ℕ
  s2 : ∀ i, X₀.abelian₂ i → ℤ
  jL_range : ∀ i lam, 1 ≤ jL i lam ∧ jL i lam ≤ R.m
  lamG : ∀ i, X₀.abelian₂ i → (G H.E N₀.Om →* (X₀.O i)ˣ)
  lamG_cont : ∀ i lam, Continuous (fun g => ((lamG i lam g : (X₀.O i)ˣ) : X₀.O i))
  lamG_unr : ∀ i lam v, v ∉ X₀.S0 i → ∀ A : ValuationSubring N₀.Om, IsPlaceOver A v →
    ∀ σ ∈ Ine (F := H.E) A, lamG i lam σ = 1
  lamG_pD : ∀ i lam, ∀ v ∈ X₀.pD i, ∀ A : ValuationSubring N₀.Om, IsPlaceOver A v →
    ∀ σ ∈ Ine (F := H.E) A, ∃ n : ℕ,
      (lamG i lam σ * (Units.map (algebraMap (X₀.O0 i) (X₀.O i)).toMonoidHom
        (if X₀.sideL i lam then X₀.delta i σ else (X₀.delta i σ)⁻¹))⁻¹) ^ (Ideal.absNorm v.asIdeal ^ n) = 1
  lamG_anti : ∀ i lam, AntiHom X₀.cc (lamG i lam)
  Xv : ∀ i, X₀.abelian₂ i → HeightOneSpectrum (𝓞 H.E) → X₀.O i
  Xv_def : ∀ i lam P, P ∉ X₀.S0 i → ∀ σ : G H.E N₀.Om, IsFrob (F := H.E) (N₀.plOm.1 P) (normV P) σ →
    Xv i lam P = ((lamG i lam σ : (X₀.O i)ˣ) : X₀.O i)
  qs : ∀ i, X₀.abelian₂ i → HeightOneSpectrum (𝓞 H.E) → FractionRing (X₀.O i)
  qs_sq : ∀ i lam P, P ∉ X₀.S0 i → qs i lam P ^ 2 = ((Ideal.absNorm P.asIdeal : ℕ) : FractionRing (X₀.O i)) ^ (-(s2 i lam))
  qs_conj : ∀ i lam P P', IsConjPl H P P' → qs i lam P = qs i lam P'
  res : ∀ i (Q Q' : Finset (HeightOneSpectrum (𝓞 H.E))), Q' ⊆ Q → (X₀.RCG i Q →* X₀.RCG i Q')
  res_art : ∀ i Q Q' (h : Q' ⊆ Q), (res i Q Q' h).comp (X₀.art i Q) = X₀.art i Q'
  twOf : (overN N₀ what₂ nR).Loc → X₀.Tw
  twSide : (overN N₀ what₂ nR).Loc → Bool
  twOf_l : ∀ a, X₀.l (twOf a) = (overN N₀ what₂ nR).l a
  twist₂ : ∀ a, X₀.O0 (twOf a) →+* (overN N₀ what₂ nR).O a
  twO_emb : ∀ a (x : LL0) (y : X₀.O0 (twOf a)),
    algebraMap (X₀.O0 (twOf a)) (FractionRing (X₀.O0 (twOf a))) y =
      (if twSide a then emb0 (twOf a) else emb0b (twOf a)) x →
    (overN N₀ what₂ nR).embK a (x : what₂.LL) = algebraMap ((overN N₀ what₂ nR).O a) (FractionRing ((overN N₀ what₂ nR).O a)) (twist₂ a y)
  psiL : ∀ a : (overN N₀ what₂ nR).Loc, G H.E N₀.Om →* ((overN N₀ what₂ nR).O a)ˣ
  psiL_ord : ∀ a g, ∃ n : ℕ, psiL a g ^ ((overN N₀ what₂ nR).l a ^ n) = 1
  psiL_open : ∀ a, IsOpen ((psiL a).ker : Set (G H.E N₀.Om))
  psiL_anti : ∀ a, AntiHom X₀.cc (psiL a)
  psiL_ram : ∀ a, RamExactly (psiL a) ↑((overN N₀ what₂ nR).Q a)
  psiL_l : ∀ a v, v ∈ placesOver H.E ((overN N₀ what₂ nR).l a) → ∀ A : ValuationSubring N₀.Om, IsPlaceOver A v →
    ∀ σ ∈ Dec (F := H.E) A, psiL a σ = 1
  chi_tw : ∀ a, (overN N₀ what₂ nR).chi a 1 =
    (Units.map (twist₂ a).toMonoidHom).comp (X₀.chi1 (twOf a) ((overN N₀ what₂ nR).j a) (twSide a)) * psiL a

def overX (X₀ : NTw R H rows₀ LL₀ N₀) (what₂ : Rows.Data R) [NumberField what₂.LL] [StarRing what₂.LL]
    (LL0 : IntermediateField ℚ what₂.LL) (n : RestN N₀ what₂) (r : RestX X₀ what₂ LL0 n) :
    NTw R H what₂ LL0 (overN N₀ what₂ n) where
  cc := X₀.cc
  cc_cm := X₀.cc_cm
  Tw := X₀.Tw
  l := X₀.l
  lPrime := X₀.lPrime
  O0 := X₀.O0
  crO0 := X₀.crO0
  twistBaseCoefficientRing_isDomain := X₀.twistBaseCoefficientRing_isDomain
  twistBaseCoefficientRing_isDVR := X₀.twistBaseCoefficientRing_isDVR
  algO0 := X₀.algO0
  twistBaseCoefficientRing_finite_padic := X₀.twistBaseCoefficientRing_finite_padic
  twistBaseCoefficientRing_residueField_finite := X₀.twistBaseCoefficientRing_residueField_finite
  topO0 := X₀.topO0
  twistBaseCoefficientRing_topologicalRing := X₀.twistBaseCoefficientRing_topologicalRing
  twistBaseCoefficientRing_isAdic := X₀.twistBaseCoefficientRing_isAdic
  emb0 := r.emb0
  emb0b := r.emb0b
  restX_coefficientEmbedding_conj := r.restX_coefficientEmbedding_conj
  O := X₀.O
  crO := X₀.crO
  domO := X₀.domO
  dvrO := X₀.dvrO
  algO := X₀.algO
  O_inj := X₀.O_inj
  O_l := X₀.O_l
  topO := r.topO
  trO := r.trO
  O_adic := r.O_adic
  resO_ac := X₀.resO_ac
  O_complete := X₀.O_complete
  Ok := X₀.Ok
  crOk := X₀.crOk
  domOk := X₀.domOk
  dvrOk := X₀.dvrOk
  algOk := X₀.algOk
  Ok_inj := X₀.Ok_inj
  Ok_fin := X₀.Ok_fin
  zk := X₀.zk
  zk_prim := X₀.zk_prim
  Ok_gen := X₀.Ok_gen
  pD := X₀.pD
  pD_eq := X₀.pD_eq
  delta := X₀.delta
  delta_open := X₀.delta_open
  delta_anti := X₀.delta_anti
  delta_ram := X₀.delta_ram
  delta_15 := X₀.delta_15
  delta_tame := X₀.delta_tame
  chi1 := X₀.chi1
  twistCharacterFamily_continuous := X₀.twistCharacterFamily_continuous
  twistCharacterFamily_unramified := X₀.twistCharacterFamily_unramified
  twistCharacterFamily_at_auxiliaryPlaces := X₀.twistCharacterFamily_at_auxiliaryPlaces
  twistCharacterFamily_tame := X₀.twistCharacterFamily_tame
  Sig := X₀.Sig
  finSig := X₀.finSig
  jS := X₀.jS
  jS_range := X₀.jS_range
  side := X₀.side
  rhoS := X₀.rhoS
  rhoS_cont := X₀.rhoS_cont
  S0 := X₀.S0
  twistExcludedPlaces_contains_residueChar := X₀.twistExcludedPlaces_contains_residueChar
  placesOver_subset_exceptional := X₀.placesOver_subset_exceptional
  primes_subset_exceptional := X₀.primes_subset_exceptional
  B := X₀.B
  acgB := X₀.acgB
  modB := X₀.modB
  freeB := X₀.freeB
  finB := X₀.finB
  Theta := X₀.Theta
  ThetaPsi := r.ThetaPsi
  ThetaPsi_one := r.ThetaPsi_one
  hk := X₀.hk
  hk_zero := X₀.hk_zero
  hEig := X₀.hEig
  abelian₂ := X₀.abelian₂
  finLam := r.finLam
  jL := r.jL
  sideL := X₀.sideL
  s2 := r.s2
  jL_range := r.jL_range
  lamG := r.lamG
  lamG_cont := r.lamG_cont
  lamG_unr := r.lamG_unr
  lamG_pD := r.lamG_pD
  lamG_anti := r.lamG_anti
  Xv := r.Xv
  Xv_def := r.Xv_def
  qs := r.qs
  qs_sq := r.qs_sq
  qs_conj := r.qs_conj
  RCG := X₀.RCG
  grpRCG := X₀.grpRCG
  finRCG := X₀.finRCG
  RCG_l := X₀.RCG_l
  art := X₀.art
  art_surj := X₀.art_surj
  art_cont := X₀.art_cont
  art_anti := X₀.art_anti
  art_unr := X₀.art_unr
  art_univ := X₀.art_univ
  res := r.res
  res_art := r.res_art
  th := X₀.th
  twOf := r.twOf
  twSide := r.twSide
  twOf_l := r.twOf_l
  twist₂ := r.twist₂
  twO_emb := r.twO_emb
  psiL := r.psiL
  psiL_ord := r.psiL_ord
  psiL_open := r.psiL_open
  psiL_anti := r.psiL_anti
  psiL_ram := r.psiL_ram
  psiL_l := r.psiL_l
  chi_tw := r.chi_tw

variable {X₀ : NTw R H rows₀ LL₀ N₀}

set_option genInjectivity false in
set_option genSizeOfSpec false in

structure RestY (Y₀ : NExp R H rows₀ LL₀ N₀ X₀) (what₂ : Rows.Data R) [NumberField what₂.LL] [StarRing what₂.LL]
    (LL0 : IntermediateField ℚ what₂.LL) (n : RestN N₀ what₂) (x : RestX X₀ what₂ LL0 n) where
  eLL0 : G0g N₀ → LL0
  eAlg_def : ∀ i b (g : G0g N₀), (Y₀.eAlg i b).coeff g =
    IsFractionRing.map (A := X₀.O0 i) (B := X₀.O i) (K := FractionRing (X₀.O0 i))
      (L := FractionRing (X₀.O i)) (X₀.O_inj i) ((if b then x.emb0 i else x.emb0b i) (eLL0 g))
  twPsi : ∀ i j b k (ψ : G H.E N₀.Om →* (X₀.Ok i k)ˣ),
    Y₀.Fm i j b →ₗ[X₀.O i] (X₀.Ok i k ⊗[X₀.O i] Y₀.Fm i j b)
  twPsi_one : ∀ i j b k (f : Y₀.Fm i j b), twPsi i j b k 1 f = (1 : X₀.Ok i k) ⊗ₜ[X₀.O i] f
  twDel : ∀ i j b (Q : Finset (PlE H)) (M : ℕ),
    Y₀.Fm i j b →ₗ[X₀.O i] (Y₀.Fm i j b ⊗[X₀.O i] AddMonoidAlgebra (X₀.O i) (DelQM H (X₀.l i) Q M))
  eH : ∀ i j b, Module.End (FractionRing (X₀.O i)) (Y₀.Fm i j b)
  eH_idem : ∀ i j b, eH i j b * eH i j b = eH i j b

def overY (Y₀ : NExp R H rows₀ LL₀ N₀ X₀) (what₂ : Rows.Data R) [NumberField what₂.LL] [StarRing what₂.LL]
    (LL0 : IntermediateField ℚ what₂.LL) (n : RestN N₀ what₂) (x : RestX X₀ what₂ LL0 n)
    (r : RestY Y₀ what₂ LL0 n x) : NExp R H what₂ LL0 (overN N₀ what₂ n) (overX X₀ what₂ LL0 n x) where
  Fm := Y₀.Fm
  acgFm := Y₀.acgFm
  modFmK := Y₀.modFmK
  modFmO := Y₀.modFmO
  towFm := Y₀.towFm
  fdFm := Y₀.fdFm
  actG := Y₀.actG
  U := Y₀.U
  psiU := Y₀.psiU
  eAlg := Y₀.eAlg
  eLL0 := r.eLL0
  eAlg_def := r.eAlg_def
  eAlg_idem := Y₀.eAlg_idem
  eAlg_central := Y₀.eAlg_central
  Bsup := Y₀.Bsup
  Dat := Y₀.Dat
  th := Y₀.th
  lev := Y₀.lev
  thPsi := Y₀.thPsi
  thPsi_one := Y₀.thPsi_one
  thU := Y₀.thU
  twPsi := r.twPsi
  twPsi_one := r.twPsi_one
  twDel := r.twDel
  delU := Y₀.delU
  delU_unr := Y₀.delU_unr
  delU_l := Y₀.delU_l
  delU_anti := Y₀.delU_anti
  delU_open := Y₀.delU_open
  delU_res := Y₀.delU_res
  delU_conj := Y₀.delU_conj
  MtV := Y₀.MtV
  acgMt := Y₀.acgMt
  modMtK := Y₀.modMtK
  modMtO := Y₀.modMtO
  towMt := Y₀.towMt
  fdMt := Y₀.fdMt
  MtLat := Y₀.MtLat
  MtLat_fg := Y₀.MtLat_fg
  MtLat_span := Y₀.MtLat_span
  thP := Y₀.thP
  hkF := Y₀.hkF
  embB := Y₀.embB
  embB_inj := Y₀.embB_inj
  eH := r.eH
  eH_idem := r.eH_idem

end Defs

set_option genInjectivity false in
set_option genSizeOfSpec false in

structure Rest (D : D7) where
  vol : @HSpace D.host.E _ _ D.host.cmStar → ℝ
  vol_pos : ∀ W, 0 < vol W
  rowsR : RestRows D.what₂
  wordFin : Fintype (overRows D.what₂ rowsR).Word
  u₀ : (overRows D.what₂ rowsR).Word
  hcW : (overRows D.what₂ rowsR).Word → (overRows D.what₂ rowsR).Tau → HCParam D.R
  hcW_base : hcW u₀ = D.hc
  hcW_v : ∀ u τ, (hcW u τ).v = (D.hc τ).v
  hcW_b : ∀ u τ, (hcW u τ).b = (D.hc τ).b
  hcW_e : ∀ u τ, (hcW u τ).e = (D.hc τ).e
  hcW_first : ∀ u τ (h : 0 < D.R.k), (hcW u τ).u ⟨0, h⟩ = (D.hc τ).u ⟨0, h⟩
  hcW_last : ∀ u τ (h : 0 < D.R.k), (hcW u τ).u ⟨D.R.k - 1, by omega⟩ = (D.hc τ).u ⟨D.R.k - 1, by omega⟩
  mem : ∀ u : (overRows D.what₂ rowsR).Word, Member D.R (overRows D.what₂ rowsR).Tau (hcW u)
  nfLL : NumberField (overRows D.what₂ rowsR).LL
  starLL : StarRing (overRows D.what₂ rowsR).LL
  tcLL : NumberField.IsTotallyComplex (overRows D.what₂ rowsR).LL
  galLL : IsGalois ℚ (overRows D.what₂ rowsR).LL
  starLL_cx : ∀ x : (overRows D.what₂ rowsR).LL, (overRows D.what₂ rowsR).embLL (star x) = starRingEnd ℂ ((overRows D.what₂ rowsR).embLL x)
  div : DivData (overRows D.what₂ rowsR).LL (overRows D.what₂ rowsR).Word
  div_good : (∀ v, IsUnit (div.RR.X v).det) ∧ ∀ u v, IsUnit ((div.Nu u).X v).det
  embE : D.host.E →+* (overRows D.what₂ rowsR).LL
  embE_φ₀ : (overRows D.what₂ rowsR).embLL.comp embE = D.host.φ₀
  conjF : D.host.E →ₐ[D.host.F] D.host.E
  conjF_eq : ∀ x, conjF x = D.host.conj x
  embE_conj : ∀ x : D.host.E, embE (D.host.conj x) = star (embE x)
  LL0 : IntermediateField ℚ (overRows D.what₂ rowsR).LL
  hostField_le_fixedField : ∀ x : D.host.E, embE x ∈ LL0
  O_int : ∀ y : (overRows D.what₂ rowsR).O, IsIntegral ℤ ((overRows D.what₂ rowsR).OtoLL y)
  O_contains : ∀ x : 𝓞 D.host.E, ∃ y : (overRows D.what₂ rowsR).O, (overRows D.what₂ rowsR).OtoLL y = embE (x : D.host.E)
  plEq : (overRows D.what₂ rowsR).places.Pl ≃ HeightOneSpectrum (𝓞 (overRows D.what₂ rowsR).LL)
  val_eq : ∀ w (x : (overRows D.what₂ rowsR).LL), x ≠ 0 → (overRows D.what₂ rowsR).places.val w x = ((vAdd (plEq w) x : ℤ) : WithTop ℤ)
  ram_eq : ∀ w, (overRows D.what₂ rowsR).places.ramIdx w = eWL (overRows D.what₂ rowsR).LL (plEq w)
  conj_val : ∀ w (x : (overRows D.what₂ rowsR).LL), (overRows D.what₂ rowsR).places.val ((overRows D.what₂ rowsR).places.conj w) x = (overRows D.what₂ rowsR).places.val w (star x)
  T_level : ∀ u, (mem u).A.T ∈ D.host.levelPrimes
  T_norm : ∀ u, ∃ π : 𝓞 D.host.E, (π : D.host.E) ∈ D.host.K ∧
    (π : D.host.E) * D.host.conj (π : D.host.E) = ((mem u).A.T : D.host.E) ∧
    (π - 1) ∈ Ideal.span {((D.host.QS * D.host.q * D.host.d * (D.host.g 0 * D.host.g 1) ^ 2 : ℕ) : 𝓞 D.host.E)}
  sp_T : letI := D.host.cmStar; D.sp.T = (mem u₀).A.T
  cOf : (overRows D.what₂ rowsR).Word → D.host.E
  cOf_ne : ∀ u, cOf u ≠ 0
  cOf_eq : ∀ u, cOf u * D.host.conj (cOf u) * ((mem u).A.T : D.host.E) = ((mem u₀).A.T : D.host.E)
  T_win : ∀ u, (mem u).A.Tstar ≤ ((mem u).A.T : ℝ) ∧
    ((mem u).A.T : ℝ) ≤ (1 + 1 / ((D.R.f : ℝ) * D.R.k)) * (mem u).A.Tstar
  GamP_eq : ∀ u, (mem u).A.GamP = (mem u₀).A.GamP
  T_ne_pde : ∀ u, (mem u).A.T ≠ D.host.pde ∧ (mem u).A.T ≠ D.host.pde'
  Dstar_eq : ∀ u, (mem u).A.Dstar = (overRows D.what₂ rowsR).Dstar
  clsLat : letI := D.host.cmStar; ∀ u i, (mem u).C.cls i → Submodule (𝓞 D.host.E) (D.sp.X i).V
  clsLat_lat : letI := D.host.cmStar; ∀ u i c, Submodule.IsLattice D.host.E (clsLat u i c)
  eMu : ∀ u, (overRows D.what₂ rowsR).Mu u ≃ₗ[ℂ] (mem u).A.Mram
  eMt : ∀ u, (mem u).P.Mt ≃ₗ[ℂ] (overRows D.what₂ rowsR).Amb (overRows D.what₂ rowsR).mu0
  perCol_base_eq_PtilCol : ∀ u (φ : (overRows D.what₂ rowsR).Mu u) (F : (overRows D.what₂ rowsR).Amb (overRows D.what₂ rowsR).mu0),
    (overRows D.what₂ rowsR).perCol u (overRows D.what₂ rowsR).mu0 φ F = (mem u).P.PtilCol ((eMu u φ : (mem u).A.Mram) :
      (mem u).C.cls 0 → (mem u).C.Y 0 → ℂ) ((eMt u).symm F)
  Bu_linL : ∀ u (F : (overRows D.what₂ rowsR).EE), IsLinearMap ℂ (fun φ : (overRows D.what₂ rowsR).Mu u => (overRows D.what₂ rowsR).Bu u φ F)
  Bu_linR : ∀ u (φ : (overRows D.what₂ rowsR).Mu u), IsLinearMap ℂ (fun F : (overRows D.what₂ rowsR).EE => (overRows D.what₂ rowsR).Bu u φ F)
  chTw : ∀ u, (overRows D.what₂ rowsR).Tup → ColumnChain D.R (overRows D.what₂ rowsR).Tau (hcW u)
  memberColumns_twistedChain_base : ∀ u, chTw u (overRows D.what₂ rowsR).mu0 = (mem u).C
  e0Tw : ∀ u μ, ((mem u).C.cls 0 → (mem u).C.Y 0 → ℂ) ≃ₗ[ℂ] ((chTw u μ).cls 0 → (chTw u μ).Y 0 → ℂ)
  PTw : ∀ u μ, PeriodMap D.R (chTw u μ)
  eMtTw : ∀ u μ, (PTw u μ).Mt ≃ₗ[ℂ] (overRows D.what₂ rowsR).Amb μ
  perCol_tie : ∀ u μ, μ ≠ (overRows D.what₂ rowsR).mu0 → ∀ (φ : (overRows D.what₂ rowsR).Mu u) (F : (overRows D.what₂ rowsR).Amb μ), (overRows D.what₂ rowsR).perCol u μ φ F =
    (PTw u μ).PtilCol (e0Tw u μ ((eMu u φ : (mem u).A.Mram) : (mem u).C.cls 0 → (mem u).C.Y 0 → ℂ))
      ((eMtTw u μ).symm F)
  jEE : div.RR.V →ₛₗ[(overRows D.what₂ rowsR).embLL] (overRows D.what₂ rowsR).EE
  jEE_basis : LinearIndependent ℂ (fun i => jEE (div.RR.b i)) ∧
    Submodule.span ℂ (Set.range (fun i => jEE (div.RR.b i))) = ⊤
  jN : ∀ u, (div.Nu u).V →ₛₗ[(overRows D.what₂ rowsR).embLL] (overRows D.what₂ rowsR).Mu u
  jN_basis : ∀ u, LinearIndependent ℂ (fun i => jN u ((div.Nu u).b i)) ∧
    Submodule.span ℂ (Set.range (fun i => jN u ((div.Nu u).b i))) = ⊤
  Dall_eq : div.Dall = (overRows D.what₂ rowsR).Dall
  delP_eq : div.delP = (overRows D.what₂ rowsR).delp
  Dt : Type
  instDt : CommGroup Dt
  detCls : ∀ u i, (mem u).C.cls i → Dt
  muTil : ℕ → Dt →* ℂˣ
  chiD : Dt →* ℂˣ
  UO : Subgroup Dt
  chiD_UO : ∀ x ∈ UO, chiD x = 1
  e1Dt : letI := D.host.cmStar; unitary D.host.E →* Dt
  rest_detCharacter_on_unitary_eq : letI := D.host.cmStar; ∀ z : unitary D.host.E,
    ((chiD (e1Dt z) : ℂˣ) : ℂ) = ∏ τ : (overRows D.what₂ rowsR).Tau, (D.host.emb ((D.eTau τ : D.R.Psi) : D.R.GG) (z : D.host.E))⁻¹
  relDet : letI := D.host.cmStar; ∀ N, SDLat D.host.E N → SDLat D.host.E N → Dt ⧸ UO
  relDet_self : letI := D.host.cmStar; ∀ N L, relDet N L L = 1
  relDet_mul : letI := D.host.cmStar; ∀ N L L' L'', relDet N L L' * relDet N L' L'' = relDet N L L''
  relDet_smul : letI := D.host.cmStar; ∀ N (L L' : SDLat D.host.E N) (γ : Matrix.unitaryGroup (Fin N) D.host.E),
    L'.1 = SDLat.smulLat (γ : Matrix (Fin N) (Fin N) D.host.E) L.1 → relDet N L L' = QuotientGroup.mk (e1Dt ⟨(γ : Matrix (Fin N) (Fin N) D.host.E).det, Matrix.det_of_mem_unitary γ.2⟩)
  rhoDet_eq_inv_muTilde_chiD_pow : ∀ u i (c : (mem u).C.cls i),
    (mem u).C.rhoDet i c = (((muTil (i + 1) (detCls u i c))⁻¹ *
      (chiD (detCls u i c)) ^ (-(((D.R.N (i + 1)) / 2 : ℕ) : ℤ)) : ℂˣ) : ℂ)
  rhoDetPrime_eq_muTilde_mul_chi_pow : ∀ u i (c : (mem u).C.cls (i + 1)),
    (mem u).C.rhoDet' i c = ((muTil (i + 1) (detCls u (i + 1) c) *
      (chiD (detCls u (i + 1) c)) ^ ((((D.R.N i) / 2 : ℕ) : ℤ)) : ℂˣ) : ℂ)
  dsig : (overRows D.what₂ rowsR).Tau → ℝ
  dsig_pos : ∀ ρ, 0 < dsig ρ
  s : Formalism.MainNotions.S.Draft.SData D.R D.host.F D.host.E conjF (overRows D.what₂ rowsR).Word (overRows D.what₂ rowsR).Tau hcW
  s_split : ∀ p, (s.atP p).split.isSome ↔
    Formalism.MainNotions.S.Loc.resChar p ∈ ({D.host.g 0, D.host.g 1} : Finset ℕ)
  s_HH : Module.finrank ℂ s.HH = (overRows D.what₂ rowsR).Dall
  s_Cu : ∀ u, s.Cu u ≃ₗ[ℂ] (mem u).A.Mu0
  s_PlF : s.PlF ≃ HeightOneSpectrum (𝓞 D.host.F)
  locA : ∀ (l : ℕ) [Fact l.Prime], LocAinf l (D.loc l)
  locT : ∀ (l : ℕ) [Fact l.Prime], LocTied l (D.loc l) (locA l)
  ndR : RestN D.nd (overRows D.what₂ rowsR)
  ntwR : RestX D.ntw (overRows D.what₂ rowsR) LL0 ndR
  naut : NAut (overN D.nd (overRows D.what₂ rowsR) ndR)
  nbc : NBC naut
  nexpR : RestY D.nexp (overRows D.what₂ rowsR) LL0 ndR ntwR
  ntypes : NTypes naut
  nStage_trivialCharacter_compat : ntypes.IdempotentMatchesAction
  nStage_trivialCharacter_coeff_eq : ∀ g : G0g (overN D.nd (overRows D.what₂ rowsR) ndR), (overRows D.what₂ rowsR).embLL (((overY D.nexp (overRows D.what₂ rowsR) LL0 ndR ntwR nexpR).eLL0 g : ↥LL0) : (overRows D.what₂ rowsR).LL) = ntypes.e0.coeff g
  nth : NTh D.R D.host (overRows D.what₂ rowsR) LL0 (overN D.nd (overRows D.what₂ rowsR) ndR) (overX D.ntw (overRows D.what₂ rowsR) LL0 ndR ntwR) (overY D.nexp (overRows D.what₂ rowsR) LL0 ndR ntwR nexpR)
  nbr : ∀ (i : (overN D.nd (overRows D.what₂ rowsR) ndR).Loc) (w : HeightOneSpectrum (𝓞 D.host.E)), w ∈ Formalism.BasicNotions.placesOver D.host.E ((overN D.nd (overRows D.what₂ rowsR) ndR).l i) →
    Formalism.BasicNotions.LocBridge ((overN D.nd (overRows D.what₂ rowsR) ndR).l i) D.host.E (overN D.nd (overRows D.what₂ rowsR) ndR).Om (ReciprocityTheory.Gal.Dec (F := D.host.E) ((overN D.nd (overRows D.what₂ rowsR) ndR).plOm.1 w)) ((overN D.nd (overRows D.what₂ rowsR) ndR).O i)
  nbr_ind : ∀ (i : (overN D.nd (overRows D.what₂ rowsR) ndR).Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ Formalism.BasicNotions.placesOver D.host.E ((overN D.nd (overRows D.what₂ rowsR) ndR).l i))
    (x : (overN D.nd (overRows D.what₂ rowsR) ndR).Om), x ∈ (overN D.nd (overRows D.what₂ rowsR) ndR).plOm.1 w ↔ ‖(nbr i w hw).j x‖ ≤ 1
  self_good : ∀ (i : (overN D.nd (overRows D.what₂ rowsR) ndR).Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ Formalism.BasicNotions.placesOver D.host.E ((overN D.nd (overRows D.what₂ rowsR) ndR).l i)),
    Formalism.BasicNotions.Loc.GoodCoef D.host.condN (nbr i w hw).LL
  loc_tie : Formalism.MainNotions.N.LocTie (overN D.nd (overRows D.what₂ rowsR) ndR) naut D.loc nbr
  bc_tie : Formalism.MainNotions.N.BcTie (overN D.nd (overRows D.what₂ rowsR) ndR) naut ntypes
  rbar_tie : Formalism.MainNotions.N.RbarTie (overN D.nd (overRows D.what₂ rowsR) ndR) naut ntypes
  mtpar_tie : Formalism.MainNotions.N.MtParTie (overN D.nd (overRows D.what₂ rowsR) ndR) naut ntypes
  Z_tie : ∀ i x, x ∈ (overN D.nd (overRows D.what₂ rowsR) ndR).Z i ↔ x ∈ Formalism.MainNotions.N.ZN (overN D.nd (overRows D.what₂ rowsR) ndR) naut i
  Zgood_tie : ∀ i x, x ∈ (overN D.nd (overRows D.what₂ rowsR) ndR).Zgood i ↔ x ∈ Formalism.MainNotions.N.ZgoodN (overN D.nd (overRows D.what₂ rowsR) ndR) naut i
  etaJ_tie : ∀ j w, 1 ≤ j → j ≤ D.R.m → (overRows D.what₂ rowsR).etaJ j w = ∑ i ∈ (overN D.nd (overRows D.what₂ rowsR) ndR).locs j w, (overN D.nd (overRows D.what₂ rowsR) ndR).etaLoc i
  fm : ∀ u, MemberForms (overRows D.what₂ rowsR).LL (overRows D.what₂ rowsR).embLL (overRows D.what₂ rowsR).places (overRows D.what₂ rowsR).Tau (hcW u) (mem u).C (mem u).A (mem u).P
  eMu_isom : ∀ u (φ ψ : (overRows D.what₂ rowsR).Mu u), inner ℂ φ ψ =
    (fm u).ipC 0 ((eMu u φ : (mem u).A.Mram) : (mem u).C.cls 0 → (mem u).C.Y 0 → ℂ)
      ((eMu u ψ : (mem u).A.Mram) : (mem u).C.cls 0 → (mem u).C.Y 0 → ℂ)
  nuIn : ∀ u, (div.Nu u).V →ₗ[(overRows D.what₂ rowsR).LL] ((fm u).lat 0).V
  nuIn_inj : ∀ u, Function.Injective (nuIn u)
  nuIn_range : ∀ u, LinearMap.range (nuIn u) = (fm u).ramSub
  nuIn_jN : ∀ u (x : (div.Nu u).V),
    ((eMu u (jN u x) : (mem u).A.Mram) : (mem u).C.cls 0 → (mem u).C.Y 0 → ℂ) = (fm u).emb 0 (nuIn u x)
  nuIn_norm : ∀ u v (x : (div.Nu u).V), Formalism.HermitianLatticesTheory.normAt (div.Nu u).b (div.Nu u).X v x =
    Formalism.HermitianLatticesTheory.normAt ((fm u).lat 0).b ((fm u).lat 0).X v (nuIn u x)
  jEE_norm : ∀ x : div.RR.V,
    Formalism.HermitianLatticesTheory.normAt div.RR.b div.RR.X (InfinitePlace.mk (overRows D.what₂ rowsR).embLL) x = ‖jEE x‖
  s_Cu_isom : ∀ u (x y : s.Cu u), inner ℂ x y =
    (fm u).ipC 0 ((s_Cu u x : (mem u).A.Mu0) : (mem u).C.cls 0 → (mem u).C.Y 0 → ℂ)
      ((s_Cu u y : (mem u).A.Mu0) : (mem u).C.cls 0 → (mem u).C.Y 0 → ℂ)
  sEE : (overRows D.what₂ rowsR).EE →ₗᵢ⋆[ℂ] s.HH
  cd : CDHaar
  jet : ThetaJet D.R D.host
  jetU : jet.Sit → (overRows D.what₂ rowsR).Word
  jetL : ∀ i, (mem (jetU i)).C.cls (jet.jOf i - 1)
  jetL' : ∀ i, (mem (jetU i)).C.cls (jet.jOf i)
  jetW : jet.Sit → (overRows D.what₂ rowsR).places.Pl
  jetW_l : ∀ i, (overRows D.what₂ rowsR).places.resChar (jetW i) = (jet.loc i).l
  jetTau : ∀ i, ZMod (jet.loc i).d → (overRows D.what₂ rowsR).Tau
  jetW1 : jet.Sit1 → (overRows D.what₂ rowsR).places.Pl
  resChar_thetaJetPlaceDegOne : ∀ i, (overRows D.what₂ rowsR).places.resChar (jetW1 i) = (jet.loc1 i).l
  jetTau1 : jet.Sit1 → (overRows D.what₂ rowsR).Tau
  jetU1 : jet.Sit1 → (overRows D.what₂ rowsR).Word
  jetL1 : ∀ i, (mem (jetU1 i)).C.cls (jet.j1Of i - 1)
  jetL1' : ∀ i, (mem (jetU1 i)).C.cls (jet.j1Of i)
  gx : GlobalExtra (overRows D.what₂ rowsR).LL (overRows D.what₂ rowsR).Tau
  gat : ∀ u (w : (overRows D.what₂ rowsR).places.Pl), GIdx D.host (mem u).A.T ((overRows D.what₂ rowsR).places.resChar w) →
    Formalism.MainNotions.G.GAtP ((overRows D.what₂ rowsR).places.resChar w)
  gat_d : ∀ u w h, (gat u w h).d = Module.finrank ℂ (mem u).A.Mu0

def overD (D : D7) (r : Rest D) : D7 where
  R := D.R
  host := D.host
  sp := D.sp
  vol := r.vol
  vol_pos := r.vol_pos
  what₂ := overRows D.what₂ r.rowsR
  eTau := D.eTau
  hc := D.hc
  wordFin := r.wordFin
  u₀ := r.u₀
  hcW := r.hcW
  hcW_base := r.hcW_base
  hcW_v := r.hcW_v
  hcW_b := r.hcW_b
  hcW_e := r.hcW_e
  hcW_first := r.hcW_first
  hcW_last := r.hcW_last
  mem := r.mem
  nfLL := r.nfLL
  starLL := r.starLL
  tcLL := r.tcLL
  galLL := r.galLL
  starLL_cx := r.starLL_cx
  div := r.div
  div_good := r.div_good
  embE := r.embE
  embE_φ₀ := r.embE_φ₀
  conjF := r.conjF
  conjF_eq := r.conjF_eq
  embE_conj := r.embE_conj
  LL0 := r.LL0
  hostField_le_fixedField := r.hostField_le_fixedField
  O_int := r.O_int
  O_contains := r.O_contains
  plEq := r.plEq
  val_eq := r.val_eq
  ram_eq := r.ram_eq
  conj_val := r.conj_val
  T_level := r.T_level
  T_norm := r.T_norm
  sp_T := r.sp_T
  cOf := r.cOf
  cOf_ne := r.cOf_ne
  cOf_eq := r.cOf_eq
  T_win := r.T_win
  GamP_eq := r.GamP_eq
  T_ne_pde := r.T_ne_pde
  Dstar_eq := r.Dstar_eq
  clsLat := r.clsLat
  clsLat_lat := r.clsLat_lat
  eMu := r.eMu
  eMt := r.eMt
  perCol_base_eq_PtilCol := r.perCol_base_eq_PtilCol
  Bu_linL := r.Bu_linL
  Bu_linR := r.Bu_linR
  chTw := r.chTw
  memberColumns_twistedChain_base := r.memberColumns_twistedChain_base
  e0Tw := r.e0Tw
  PTw := r.PTw
  eMtTw := r.eMtTw
  perCol_tie := r.perCol_tie
  jEE := r.jEE
  jEE_basis := r.jEE_basis
  jN := r.jN
  jN_basis := r.jN_basis
  Dall_eq := r.Dall_eq
  delP_eq := r.delP_eq
  Dt := r.Dt
  instDt := r.instDt
  detCls := r.detCls
  muTil := r.muTil
  chiD := r.chiD
  UO := r.UO
  chiD_UO := r.chiD_UO
  e1Dt := r.e1Dt
  rest_detCharacter_on_unitary_eq := r.rest_detCharacter_on_unitary_eq
  relDet := r.relDet
  relDet_self := r.relDet_self
  relDet_mul := r.relDet_mul
  relDet_smul := r.relDet_smul
  rhoDet_eq_inv_muTilde_chiD_pow := r.rhoDet_eq_inv_muTilde_chiD_pow
  rhoDetPrime_eq_muTilde_mul_chi_pow := r.rhoDetPrime_eq_muTilde_mul_chi_pow
  dsig := r.dsig
  dsig_pos := r.dsig_pos
  s := r.s
  s_split := r.s_split
  s_HH := r.s_HH
  s_Cu := r.s_Cu
  s_PlF := r.s_PlF
  loc := D.loc
  locA := r.locA
  locT := r.locT
  nd := overN D.nd _ r.ndR
  ntw := @overX _ _ _ _ _ _ _ D.ntw _ r.nfLL r.starLL r.LL0 r.ndR r.ntwR
  naut := r.naut
  nbc := r.nbc
  nexp := @overY _ _ _ _ _ _ _ _ D.nexp _ r.nfLL r.starLL r.LL0 r.ndR r.ntwR r.nexpR
  ntypes := r.ntypes
  nStage_trivialCharacter_compat := r.nStage_trivialCharacter_compat
  nStage_trivialCharacter_coeff_eq := r.nStage_trivialCharacter_coeff_eq
  nth := r.nth
  nbr := r.nbr
  nbr_ind := r.nbr_ind
  self_good := r.self_good
  ntwbr := D.ntwbr
  ntwbr_ind := D.ntwbr_ind
  loc_tie := r.loc_tie
  bc_tie := r.bc_tie
  rbar_tie := r.rbar_tie
  mtpar_tie := r.mtpar_tie
  Z_tie := r.Z_tie
  Zgood_tie := r.Zgood_tie
  etaJ_tie := r.etaJ_tie
  fm := r.fm
  eMu_isom := r.eMu_isom
  nuIn := r.nuIn
  nuIn_inj := r.nuIn_inj
  nuIn_range := r.nuIn_range
  nuIn_jN := r.nuIn_jN
  nuIn_norm := r.nuIn_norm
  jEE_norm := r.jEE_norm
  s_Cu_isom := r.s_Cu_isom
  sEE := r.sEE
  cd := r.cd
  jet := r.jet
  jetU := r.jetU
  jetL := r.jetL
  jetL' := r.jetL'
  jetW := r.jetW
  jetW_l := r.jetW_l
  jetTau := r.jetTau
  jetW1 := r.jetW1
  resChar_thetaJetPlaceDegOne := r.resChar_thetaJetPlaceDegOne
  jetTau1 := r.jetTau1
  jetU1 := r.jetU1
  jetL1 := r.jetL1
  jetL1' := r.jetL1'
  gx := r.gx
  gat := r.gat
  gat_d := r.gat_d
  Y_sigval := D.Y_sigval

section Elim
variable {R : Ranks} {H : Host R}

theorem exists_restRows (r₀ r : Rows.Data R)
    (hTau : HEq r₀.Tau r.Tau) (hinstTau : HEq r₀.instTau r.instTau) :
    ∃ x, r = overRows r₀ x := by
  obtain @⟨aLL, ainstLL, aembLL, aplaces, aO, ainstO, aOtoLL, aTau, ainstTau, acard_Tau, aTup, amu0, amuStar, amuStar',
    amuAt, amuAt_conj, amuTw, amuTw_conj, amuAt_or, aEE, ainstEE, ainstEEi, ainstEEf, aDrows, aonb, aDall, adelp,
    adelp_le_one, aD_eq, aEE0, ainstEE0, ainstEE0i, ainstEE0f, aD0, aonb0, aFT, ainstFT, ainstFTd, aft, aft0,
    aDstar, aAmb, ainstAmb, ainstAmbi, ainstAmbf, aMult, ainstMult, ainstMulti, ainstMultf, amultZero, amultTop,
    aio, aMtilde, aeOp, aeOp_idem, aeOp_sa, acardG0g, acardG0g_pos, aWord, aMu, ainstMu, ainstMui, ainstMuf,
    aperCol, aBu, aze, aze_mu0, aMj, ainstMj, ainstMji, ainstMjf, aMjLat, akaBig, akaSmall, aMt, ainstMt, ainstMti,
    ainstMtf, aMtLat, aMtL, ainstMtL, ainstMtLm, ajMt, ajMt_basis, aMtLat_sub, aeMt, aeMt_idem, aeMt_sa, aeMt_LL,
    athetaP, aisot, alamP, aIj, ajw, aetaJ, aetaJ_nonneg, ashaLen, ashaLen_nonneg⟩ := r
  dsimp only at *
  subst hTau; subst hinstTau
  exact ⟨⟨aLL, ainstLL, aembLL, aplaces, aO, ainstO, aOtoLL, aTup, amu0, amuStar, amuStar', amuAt, amuAt_conj, amuTw,
    amuTw_conj, amuAt_or, aEE, ainstEE, ainstEEi, ainstEEf, aDrows, aonb, aDall, adelp, adelp_le_one, aD_eq, aEE0,
    ainstEE0, ainstEE0i, ainstEE0f, aD0, aonb0, aFT, ainstFT, ainstFTd, aft, aft0, aDstar, aAmb, ainstAmb,
    ainstAmbi, ainstAmbf, aMult, ainstMult, ainstMulti, ainstMultf, amultZero, amultTop, aio, aMtilde, aeOp,
    aeOp_idem, aeOp_sa, acardG0g, acardG0g_pos, aWord, aMu, ainstMu, ainstMui, ainstMuf, aperCol, aBu, aze,
    aze_mu0, aMj, ainstMj, ainstMji, ainstMjf, aMjLat, akaBig, akaSmall, aMt, ainstMt, ainstMti, ainstMtf, aMtLat,
    aMtL, ainstMtL, ainstMtLm, ajMt, ajMt_basis, aMtLat_sub, aeMt, aeMt_idem, aeMt_sa, aeMt_LL, athetaP, aisot,
    alamP, aIj, ajw, aetaJ, aetaJ_nonneg, ashaLen, ashaLen_nonneg⟩, rfl⟩

theorem exists_restN {r₀ r : Rows.Data R} (N₀ : NData R H r₀) (N : NData R H r)
    (hOm : HEq N₀.Om N.Om) (hinstOm : HEq N₀.instOm N.instOm) (halgOm : HEq N₀.algOm N.algOm) (hplOm : HEq N₀.plOm N.plOm)
    (hPlG : HEq N₀.PlG N.PlG) (hfinPlG : HEq N₀.finPlG N.finPlG) :
    ∃ x, N = overN N₀ r x := by
  obtain @⟨aOm, ainstOm, aalgOm, aacOm, aplOm, aldat, asha_eq, aLoc, al, alPrime, aj, aj_range, amu, aw, aw_l, amu_w,
    aw_tw, alocs, alocs_mem, aO, ainstO, adomO, advrO, aalgO, afinO, atopO, atrO, aO_adic, aO_complete, aembK,
    aembK_w, aX, afinX, aneX, aT, aT_local, aT_sep, aMt, aacgMt, amodMt, afreeMt, afinMt, aact, aact_inj, aprMt,
    aprMt_span, aprMt_lat, aeig_ne, achi, achi_cont, achi_def, aZ, aZgood, as0, as0_odd, as0_two, aS, aQ,
    aSQ_split, aSQ_disj, aSQ_l, aS_def, ahT, aT_gen, agam0, agam0_mem, agam0_gen, achi_ram_Q, aBj, aacgBj, amodBj,
    afreeBj, afinBj, ag_split, aPlG, afinPlG, acard_PlG, alab, alab_monic, achiT, acardG0g_eq⟩ := N
  dsimp only at *
  subst hOm; subst hinstOm; subst halgOm; subst hplOm; subst hPlG; subst hfinPlG
  exact ⟨⟨aldat, asha_eq, aLoc, al, alPrime, aj, aj_range, amu, aw, aw_l, amu_w, aw_tw, alocs, alocs_mem, aO, ainstO,
    adomO, advrO, aalgO, afinO, atopO, atrO, aO_adic, aO_complete, aembK, aembK_w, aX, afinX, aneX, aT, aT_local,
    aT_sep, aMt, aacgMt, amodMt, afreeMt, afinMt, aact, aact_inj, aprMt, aprMt_span, aprMt_lat, aeig_ne, achi,
    achi_cont, achi_def, aZ, aZgood, as0, as0_odd, as0_two, aS, aQ, aSQ_split, aSQ_disj, aSQ_l, aS_def, ahT,
    aT_gen, agam0, agam0_mem, agam0_gen, achi_ram_Q, aBj, aacgBj, amodBj, afreeBj, afinBj, alab, alab_monic, achiT,
    acardG0g_eq⟩, rfl⟩

variable {r₀ r : Rows.Data R} [NumberField r₀.LL] [StarRing r₀.LL] [NumberField r.LL] [StarRing r.LL]
  {L₀ : IntermediateField ℚ r₀.LL} {L : IntermediateField ℚ r.LL} {N₀ : NData R H r₀} {n : RestN N₀ r}

theorem exists_restX (X₀ : NTw R H r₀ L₀ N₀) (X : NTw R H r L (overN N₀ r n))
    (hcc : HEq X₀.cc X.cc) (hTw : HEq X₀.Tw X.Tw) (hl : HEq X₀.l X.l) (hO0 : HEq X₀.O0 X.O0)
    (hcrO0 : HEq X₀.crO0 X.crO0) (halgO0 : HEq X₀.algO0 X.algO0) (htopO0 : HEq X₀.topO0 X.topO0) (hO : HEq X₀.O X.O)
    (hcrO : HEq X₀.crO X.crO) (halgO : HEq X₀.algO X.algO) (hOk : HEq X₀.Ok X.Ok) (hcrOk : HEq X₀.crOk X.crOk)
    (halgOk : HEq X₀.algOk X.algOk) (hzk : HEq X₀.zk X.zk) (hpD : HEq X₀.pD X.pD) (hdelta : HEq X₀.delta X.delta)
    (hchi1 : HEq X₀.chi1 X.chi1) (hSig : HEq X₀.Sig X.Sig) (hfinSig : HEq X₀.finSig X.finSig) (hjS : HEq X₀.jS X.jS)
    (hside : HEq X₀.side X.side) (hrhoS : HEq X₀.rhoS X.rhoS) (hS0 : HEq X₀.S0 X.S0) (hB : HEq X₀.B X.B)
    (hacgB : HEq X₀.acgB X.acgB) (hmodB : HEq X₀.modB X.modB) (hTheta : HEq X₀.Theta X.Theta) (hhk : HEq X₀.hk X.hk)
    (hhEig : HEq X₀.hEig X.hEig) (hLam : HEq X₀.abelian₂ X.abelian₂) (hsideL : HEq X₀.sideL X.sideL) (hRCG : HEq X₀.RCG X.RCG)
    (hgrpRCG : HEq X₀.grpRCG X.grpRCG) (hfinRCG : HEq X₀.finRCG X.finRCG) (hart : HEq X₀.art X.art) (hth : HEq X₀.th X.th) :
    ∃ x, X = overX X₀ r L n x := by
  obtain @⟨acc, acc_cm, aTw, al, alPrime, aO0, acrO0, adomO0, advrO0, aalgO0, afinO0, aresO0_fin, atopO0, atrO0, aO0_adic,
    aemb0, aemb0b, aemb0b_conj, aO, acrO, adomO, advrO, aalgO, aO_inj, aO_l, atopO, atrO, aO_adic, aresO_ac,
    aO_complete, aOk, acrOk, adomOk, advrOk, aalgOk, aOk_inj, aOk_fin, azk, azk_prim, aOk_gen, apD, apD_eq, adelta,
    adelta_open, adelta_anti, adelta_ram, adelta_15, adelta_tame, achi1, achi1_cont, achi1_unr, achi1_pD,
    achi1_tame, aSig, afinSig, ajS, ajS_range, aside, arhoS, arhoS_cont, aS0, aS0_l, aS0_g, aS0_pD, aB, aacgB,
    amodB, afreeB, afinB, aTheta, aThetaPsi, aThetaPsi_one, ahk, ahk_zero, ahEig, aLam, afinLam, ajL, asideL, as2,
    ajL_range, alamG, alamG_cont, alamG_unr, alamG_pD, alamG_anti, aXv, aXv_def, aqs, aqs_sq, aqs_conj, aRCG,
    agrpRCG, afinRCG, aRCG_l, aart, aart_surj, aart_cont, aart_anti, aart_unr, aart_univ, ares, ares_art, ath,
    atwOf, atwSide, atwOf_l, atwO, atwO_emb, apsiL, apsiL_ord, apsiL_open, apsiL_anti, apsiL_ram, apsiL_l, achi_tw⟩ := X
  dsimp only at *
  subst hcc; subst hTw; subst hl; subst hO0; subst hcrO0; subst halgO0
  subst htopO0; subst hO; subst hcrO; subst halgO; subst hOk; subst hcrOk
  subst halgOk; subst hzk; subst hpD; subst hdelta; subst hchi1; subst hSig
  subst hfinSig; subst hjS; subst hside; subst hrhoS; subst hS0; subst hB
  subst hacgB; subst hmodB; subst hTheta; subst hhk; subst hhEig; subst hLam
  subst hsideL; subst hRCG; subst hgrpRCG; subst hfinRCG; subst hart; subst hth
  exact ⟨⟨aemb0, aemb0b, aemb0b_conj, atopO, atrO, aO_adic, aThetaPsi, aThetaPsi_one, afinLam, ajL, as2, ajL_range,
    alamG, alamG_cont, alamG_unr, alamG_pD, alamG_anti, aXv, aXv_def, aqs, aqs_sq, aqs_conj, ares, ares_art, atwOf,
    atwSide, atwOf_l, atwO, atwO_emb, apsiL, apsiL_ord, apsiL_open, apsiL_anti, apsiL_ram, apsiL_l, achi_tw⟩, rfl⟩

theorem exists_restY {X₀ : NTw R H r₀ L₀ N₀} {x : RestX X₀ r L n} (Y₀ : NExp R H r₀ L₀ N₀ X₀)
    (Y : NExp R H r L (overN N₀ r n) (overX X₀ r L n x))
    (hFm : HEq Y₀.Fm Y.Fm) (hacgFm : HEq Y₀.acgFm Y.acgFm) (hmodFmK : HEq Y₀.modFmK Y.modFmK) (hmodFmO : HEq Y₀.modFmO Y.modFmO)
    (hactG : HEq Y₀.actG Y.actG) (hU : HEq Y₀.U Y.U) (hpsiU : HEq Y₀.psiU Y.psiU) (heAlg : HEq Y₀.eAlg Y.eAlg)
    (hBsup : HEq Y₀.Bsup Y.Bsup) (hDat : HEq Y₀.Dat Y.Dat) (hth : HEq Y₀.th Y.th) (hlev : HEq Y₀.lev Y.lev)
    (hthPsi : HEq Y₀.thPsi Y.thPsi) (hthU : HEq Y₀.thU Y.thU) (hdelU : HEq Y₀.delU Y.delU) (hMtV : HEq Y₀.MtV Y.MtV)
    (hacgMt : HEq Y₀.acgMt Y.acgMt) (hmodMtK : HEq Y₀.modMtK Y.modMtK) (hmodMtO : HEq Y₀.modMtO Y.modMtO) (hMtLat : HEq Y₀.MtLat Y.MtLat)
    (hthP : HEq Y₀.thP Y.thP) (hhkF : HEq Y₀.hkF Y.hkF) (hembB : HEq Y₀.embB Y.embB) :
    ∃ y, Y = overY Y₀ r L n x y := by
  obtain @⟨aFm, aacgFm, amodFmK, amodFmO, atowFm, afdFm, aactG, aU, apsiU, aeAlg, aeLL0, aeAlg_def, aeAlg_idem,
    aeAlg_central, aBsup, aDat, ath, alev, athPsi, athPsi_one, athU, atwPsi, atwPsi_one, atwDel, adelU, adelU_unr,
    adelU_l, adelU_anti, adelU_open, adelU_res, adelU_conj, aMtV, aacgMt, amodMtK, amodMtO, atowMt, afdMt, aMtLat,
    aMtLat_fg, aMtLat_span, athP, ahkF, aembB, aembB_inj, aeH, aeH_idem⟩ := Y
  dsimp only at *
  subst hFm; subst hacgFm; subst hmodFmK; subst hmodFmO; subst hactG; subst hU
  subst hpsiU; subst heAlg; subst hBsup; subst hDat; subst hth; subst hlev
  subst hthPsi; subst hthU; subst hdelU; subst hMtV; subst hacgMt; subst hmodMtK
  subst hmodMtO; subst hMtLat; subst hthP; subst hhkF; subst hembB
  exact ⟨⟨aeLL0, aeAlg_def, atwPsi, atwPsi_one, atwDel, aeH, aeH_idem⟩, rfl⟩

end Elim

set_option maxRecDepth 100000 in

theorem CopyTw.exists_rest {D D' : D7} {ι : D.what₂.LL →+* D'.what₂.LL} {e : ↥D'.LL0 ≃+* ↥D.LL0} (h : CopyTw D D' ι e) :
    ∃ r, D' = overD D r := by
  have hT := h.instTau
  have hP : HEq D.nd.finPlG D'.nd.finPlG :=
    Subsingleton.helim (congrArg (fun P : Fin 2 → Type => ∀ k, Fintype (P k)) (eq_of_heq h.gal.PlG)) _ _
  obtain ⟨⟨⟨a1, a2, a3, n1, n2, n3, n4, n5⟩, x, y, br, -⟩, sp, Tau, eTau, hc, -, -, -, -, -, delta, B, acgB, modB, Theta, hk,
    Bsup, embB, thU, delU⟩ := h
  obtain ⟨xcc, xTw, xl, fixedFieldTransport_baseIntegerRing_heq, fixedFieldTransport_baseIntegerCommRing_heq, fixedFieldTransport_baseIntegerAlgebra_heq, fixedFieldTransport_baseIntegerTopology_heq, xO, xcrO, xalgO, xOk, xcrOk, xalgOk, xzk, xpD, xchi1, xSig, xfinSig,
    xjS, xside, xrhoS, fixedFieldTransport_initialPlaceSet_heq, xhEig, xLam, xsideL, xRCG, xgrpRCG, xfinRCG, xart, xth⟩ := x
  obtain ⟨yFm, yacgFm, ymodFmK, ymodFmO, yactG, yU, ypsiU, yeAlg, yDat, yth, ylev, ythPsi, yMtV, yacgMt, ymodMtK,
    ymodMtO, yMtLat, ythP, yhkF⟩ := y
  clear ι e
  obtain @⟨aR, ahost, asp, avol, avol_pos, arows, aeTau, ahc, awordFin, au₀, ahcW, ahcW_base, ahcW_v, ahcW_b, ahcW_e,
    ahcW_first, ahcW_last, amem, anfLL, astarLL, atcLL, agalLL, astarLL_cx, adiv, adiv_good, aembE, aembE_φ₀,
    aconjF, aconjF_eq, aembE_conj, aLL0, aE_le_LL0, aO_int, aO_contains, aplEq, aval_eq, aram_eq, aconj_val,
    aT_level, aT_norm, asp_T, acOf, acOf_ne, acOf_eq, aT_win, aGamP_eq, aT_ne_pde, aDstar_eq, aclsLat, aclsLat_lat,
    aeMu, aeMt, aperCol_mu0, aBu_linL, aBu_linR, achTw, achTw_mu0, ae0Tw, aPTw, aeMtTw, aperCol_tie, ajEE,
    ajEE_basis, ajN, ajN_basis, aDall_eq, adelP_eq, aDt, ainstDt, adetCls, amuTil, achiD, aUO, achiD_UO, ae1Dt,
    achiD_E1, arelDet, arelDet_self, arelDet_mul, arelDet_smul, arho_C13, arho'_C13, adsig, adsig_pos, as,
    as_split, as_HH, as_Cu, as_PlF, aloc, alocA, alocT, and, antw, anaut, anbc, anexp, antypes, ae0_tie, ae0_LL0,
    anth, anbr, anbr_ind, aself_good, antwbr, antwbr_ind, aloc_tie, abc_tie, arbar_tie, amtpar_tie, aZ_tie,
    aZgood_tie, aetaJ_tie, afm, aeMu_isom, anuIn, anuIn_inj, anuIn_range, anuIn_jN, anuIn_norm, ajEE_norm,
    as_Cu_isom, asEE, acd, ajet, ajetU, ajetL, ajetL', ajetW, ajetW_l, ajetTau, ajetW1, ajetW1_l, ajetTau1, ajetU1,
    ajetL1, ajetL1', agx, agat, agat_d, aY_sigval⟩ := D'
  dsimp only at *
  subst a1; subst a2; subst a3; subst sp
  obtain ⟨brows, rfl⟩ := exists_restRows _ _ (heq_of_eq Tau) hT
  subst eTau; subst hc
  obtain ⟨bnd, rfl⟩ := exists_restN _ _ n1 n2 n3 n4 n5 hP
  obtain ⟨bntw, rfl⟩ := exists_restX D.ntw antw xcc xTw xl fixedFieldTransport_baseIntegerRing_heq fixedFieldTransport_baseIntegerCommRing_heq fixedFieldTransport_baseIntegerAlgebra_heq fixedFieldTransport_baseIntegerTopology_heq xO xcrO xalgO xOk xcrOk
    xalgOk xzk xpD delta xchi1 xSig xfinSig xjS xside xrhoS fixedFieldTransport_initialPlaceSet_heq B
    acgB modB Theta hk xhEig xLam xsideL xRCG xgrpRCG xfinRCG xart xth
  obtain ⟨bnexp, rfl⟩ := exists_restY D.nexp anexp yFm yacgFm ymodFmK ymodFmO yactG yU ypsiU yeAlg Bsup yDat yth ylev
    ythPsi thU delU yMtV yacgMt ymodMtK ymodMtO yMtLat ythP yhkF embB
  subst br
  exact ⟨⟨avol, avol_pos, brows, awordFin, au₀, ahcW, ahcW_base, ahcW_v, ahcW_b, ahcW_e, ahcW_first, ahcW_last, amem,
    anfLL, astarLL, atcLL, agalLL, astarLL_cx, adiv, adiv_good, aembE, aembE_φ₀, aconjF, aconjF_eq, aembE_conj,
    aLL0, aE_le_LL0, aO_int, aO_contains, aplEq, aval_eq, aram_eq, aconj_val, aT_level, aT_norm, asp_T, acOf,
    acOf_ne, acOf_eq, aT_win, aGamP_eq, aT_ne_pde, aDstar_eq, aclsLat, aclsLat_lat, aeMu, aeMt, aperCol_mu0,
    aBu_linL, aBu_linR, achTw, achTw_mu0, ae0Tw, aPTw, aeMtTw, aperCol_tie, ajEE, ajEE_basis, ajN, ajN_basis,
    aDall_eq, adelP_eq, aDt, ainstDt, adetCls, amuTil, achiD, aUO, achiD_UO, ae1Dt, achiD_E1, arelDet,
    arelDet_self, arelDet_mul, arelDet_smul, arho_C13, arho'_C13, adsig, adsig_pos, as, as_split, as_HH, as_Cu,
    as_PlF, alocA, alocT, bnd, bntw, anaut, anbc, bnexp, antypes, ae0_tie, ae0_LL0, anth, anbr, anbr_ind,
    aself_good, aloc_tie, abc_tie, arbar_tie, amtpar_tie, aZ_tie, aZgood_tie, aetaJ_tie, afm,
    aeMu_isom, anuIn, anuIn_inj, anuIn_range, anuIn_jN, anuIn_norm, ajEE_norm, as_Cu_isom, asEE, acd, ajet, ajetU,
    ajetL, ajetL', ajetW, ajetW_l, ajetTau, ajetW1, ajetW1_l, ajetTau1, ajetU1, ajetL1, ajetL1', agx, agat, agat_d⟩, rfl⟩

example (D : D7) : Nonempty (Rest D) := let ⟨r, _⟩ := (CopyTw.refl D).exists_rest; ⟨r⟩

end GlobalTheory.TwInputs.Move

end

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open Formalism.L2.Host (embLL0 CharFrame)
open GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwInputs.Move

variable {D D' : D7}

structure SameTwist {A : Type} [CommGroup A] (t : Twist D A) (t' : Twist D' A) : Prop where
  Q : HEq t.Q t'.Q
  chi : HEq t.chi t'.chi
  res : HEq t.res t'.res

structure SameBase {S T : HSp D} {S' T' : HSp D'} (B : Base S T) (B' : Base S' T') : Prop where
  ψ : HEq B.F.ψ B'.F.ψ
  θ : HEq B.F.θ B'.F.θ
  sT : HEq B.F.sT B'.F.sT
  BS : HEq B.F.BS B'.F.BS
  BT : HEq B.F.BT B'.F.BT
  ΛS : HEq B.F.ΛS B'.F.ΛS
  ΛT : HEq B.F.ΛT B'.F.ΛT
  βS : HEq B.F.βS B'.F.βS
  βT : HEq B.F.βT B'.F.βT
  f₀ : HEq B.F.f₀ B'.F.f₀
  Pg : HEq B.G.Pg B'.G.Pg
  P : HEq B.G.P B'.G.P
  mu : HEq B.G.mu B'.G.mu
  de : SameTwist B.de B'.de
  p : HEq B.w.p B'.w.p
  q : HEq B.w.q B'.w.q
  ap : HEq B.w.ap B'.w.ap
  am : HEq B.w.am B'.w.am
  c : HEq B.w.c B'.w.c
  lam : HEq B.w.lam B'.w.lam
  mu0 : HEq B.mu0 B'.mu0
  eta : HEq B.eta B'.eta

structure SameData (ρ : Setup D.ntw) (ρ' : Setup D'.ntw) : Prop where
  κ : HEq ρ.rc.κ ρ'.rc.κ
  art : HEq ρ.rc.art ρ'.rc.art
  ch : HEq ρ.ch ρ'.ch
  bad : HEq ρ.bad ρ'.bad
  e : HEq ρ.e ρ'.e
  ek : HEq ρ.ek ρ'.ek
  B : ∀ i i', HEq i i' → ∀ (j : Fin D.R.m) (j' : Fin D'.R.m), (j : ℕ) = j' → ∀ b, SameBase (ρ.B i j b) (ρ'.B i' j' b)
  om : HEq ρ.om ρ'.om
  Cl : ∀ i i', HEq i i' → ∀ (j : Fin D.R.m) (j' : Fin D'.R.m), (j : ℕ) = j' → ∀ b t t', SameTwist t t' →
    ρ.Cl i j b t = ρ'.Cl i' j' b t' ∧ HEq (ρ.rep i j b t) (ρ'.rep i' j' b t')
  β : HEq ρ.β ρ'.β
  eG : ∀ i i', HEq i i' → ∀ (j : Fin D.R.m) (j' : Fin D'.R.m), (j : ℕ) = j' → ∀ b, HEq (ρ.eG i j b) (ρ'.eG i' j' b)

theorem SameTwist.refl {A : Type} [CommGroup A] (t : Twist D A) : SameTwist t t := ⟨.rfl, .rfl, .rfl⟩

theorem SameTwist.eq {A : Type} [CommGroup A] {t t' : Twist D A} (h : SameTwist t t') : t = t' := by
  cases t; cases t'
  obtain ⟨h1, h2, h3⟩ := h
  cases h1; cases h2; cases h3
  rfl

theorem SameBase.refl {S T : HSp D} (B : Base S T) : SameBase B B :=
  ⟨.rfl, .rfl, .rfl, .rfl, .rfl, .rfl, .rfl, .rfl, .rfl, .rfl, .rfl, .rfl, .rfl, .refl _, .rfl, .rfl, .rfl, .rfl, .rfl, .rfl, .rfl, .rfl⟩

theorem SameBase.eq {S T : HSp D} {B B' : Base S T} (h : SameBase B B') : B = B' := by
  obtain ⟨_, ⟨_, _, _, _, _, _, _, _, _, _⟩, ⟨_, _, _⟩, _, ⟨_, _, _, _, _, _⟩, _, _⟩ := B
  obtain ⟨_, ⟨_, _, _, _, _, _, _, _, _, _⟩, ⟨_, _, _⟩, _, ⟨_, _, _, _, _, _⟩, _, _⟩ := B'
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21⟩ := h
  have a := a13.eq
  dsimp only at *
  cases a0; cases a1; cases a2; cases a3; cases a4; cases a5; cases a6; cases a7; cases a8; cases a9; cases a10; cases a11; cases a12; cases a14; cases a15; cases a16; cases a17; cases a18; cases a19; cases a20; cases a21; cases a
  rfl

theorem SameData.refl (ρ : Setup D.ntw) : SameData ρ ρ :=
  ⟨.rfl, .rfl, .rfl, .rfl, .rfl, .rfl, fun _ _ hi _ _ hj _ => by cases hi; cases Fin.ext hj; exact .refl _, .rfl,
    fun _ _ hi _ _ hj _ _ _ ht => by cases hi; cases Fin.ext hj; cases ht.eq; exact ⟨rfl, .rfl⟩, .rfl,
    fun _ _ hi _ _ hj _ => by cases hi; cases Fin.ext hj; exact .rfl⟩

theorem SameData.eq {ρ ρ' : Setup D.ntw} (h : SameData ρ ρ') : ρ = ρ' := by
  have hB : ρ.B = ρ'.B := funext fun i => funext fun j => funext fun b => (h.B i i .rfl j j rfl b).eq
  have hC : ρ.Cl = ρ'.Cl := funext fun i => funext fun j => funext fun b => funext fun t => (h.Cl i i .rfl j j rfl b t t (.refl t)).1
  have hr := fun i j b t => (h.Cl i i .rfl j j rfl b t t (.refl t)).2
  have hg := fun i j b => h.eG i i .rfl j j rfl b
  obtain ⟨h1, h2, h3, h4, h5, h6, -, h8, -, h10, -⟩ := h
  obtain @⟨⟨_, _⟩, _, _, _, _, _, _, _, f, r, _, g⟩ := ρ
  obtain @⟨⟨_, _⟩, _, _, _, _, _, _, _, f', r', _, g'⟩ := ρ'
  dsimp only at *
  cases h1; cases h2; cases h3; cases h4; cases h5; cases h6; cases h8; cases h10; cases hB; cases hC
  obtain rfl : f = f' := Subsingleton.elim _ _
  obtain rfl : r = r' := funext fun i => funext fun j => funext fun b => funext fun t => eq_of_heq (hr i j b t)
  obtain rfl : g = g' := funext fun i => funext fun j => funext fun b => eq_of_heq (hg i j b)
  rfl

section Up

variable (r : Rest D)

def twistUp {A : Type} [CommGroup A] (t : Twist D A) : Twist (overD D r) A := ⟨(t.Q), (t.chi), (t.res)⟩

def twistDn {A : Type} [CommGroup A] (t : Twist (overD D r) A) : Twist D A := ⟨(t.Q), (t.chi), (t.res)⟩

def baseUp {S T : HSp D} (B : Base S T) : Base (D := overD D r) ((S)) ((T)) :=
  ⟨(B.hr), ⟨(B.F.ψ), (B.F.θ), (B.F.sT), (B.F.BS), (B.F.BT), (B.F.ΛS), (B.F.ΛT), (B.F.βS), (B.F.βT), (B.F.f₀)⟩, ⟨(B.G.Pg), (B.G.P), (B.G.mu)⟩, twistUp r B.de,
    ⟨(B.w.p), (B.w.q), (B.w.ap), (B.w.am), (B.w.c), (B.w.lam)⟩, (B.mu0), (B.eta)⟩

def setupUp (ρ : Setup D.ntw) : Setup (overD D r).ntw :=
  @Setup.mk (overD D r) _ _ ⟨(ρ.rc.κ), (ρ.rc.art)⟩ ((ρ.ch)) ((ρ.bad)) ((ρ.e)) ((ρ.ek))
    ((fun (i : @Formalism.BasicNotions.NTw.Tw (Formalism.BasicNotions.D7.R D) (Formalism.BasicNotions.D7.host D) (Formalism.BasicNotions.D7.what₂ D) (Formalism.BasicNotions.D7.nfLL D) (Formalism.BasicNotions.D7.starLL D) (Formalism.BasicNotions.D7.LL0 D) (Formalism.BasicNotions.D7.nd D) (Formalism.BasicNotions.D7.ntw D)) (j : Fin (Formalism.BasicNotions.Ranks.m (Formalism.BasicNotions.D7.R D))) (b : Bool) ↦ @GlobalTheory.TwInputs.Move.baseUp D r (Formalism.IndefR.Links.Vc D j) (Formalism.IndefR.Links.Wc D j) (@GlobalTheory.SeriesTie.Setup.B D (Formalism.BasicNotions.D7.nd D) (Formalism.BasicNotions.D7.ntw D) ρ i j b))) ((ρ.om)) ((fun (i : @Formalism.BasicNotions.NTw.Tw (Formalism.BasicNotions.D7.R D) (Formalism.BasicNotions.D7.host D) (Formalism.BasicNotions.D7.what₂ D) (Formalism.BasicNotions.D7.nfLL D) (Formalism.BasicNotions.D7.starLL D) (Formalism.BasicNotions.D7.LL0 D) (Formalism.BasicNotions.D7.nd D) (Formalism.BasicNotions.D7.ntw D)) (j : Fin (Formalism.BasicNotions.Ranks.m (Formalism.BasicNotions.D7.R D))) (b : Bool) (t : @GlobalTheory.ExportSeries.Twist (GlobalTheory.TwInputs.Move.overD D r) Circle Circle.instCommGroup) ↦ @GlobalTheory.SeriesTie.Setup.Cl D (Formalism.BasicNotions.D7.nd D) (Formalism.BasicNotions.D7.ntw D) ρ i j b (@GlobalTheory.TwInputs.Move.twistDn D r Circle Circle.instCommGroup t)))
    ((fun (i : @Formalism.BasicNotions.NTw.Tw (Formalism.BasicNotions.D7.R D) (Formalism.BasicNotions.D7.host D) (Formalism.BasicNotions.D7.what₂ D) (Formalism.BasicNotions.D7.nfLL D) (Formalism.BasicNotions.D7.starLL D) (Formalism.BasicNotions.D7.LL0 D) (Formalism.BasicNotions.D7.nd D) (Formalism.BasicNotions.D7.ntw D)) (j : Fin (Formalism.BasicNotions.Ranks.m (Formalism.BasicNotions.D7.R D))) (b : Bool) (t : @GlobalTheory.ExportSeries.Twist (GlobalTheory.TwInputs.Move.overD D r) Circle Circle.instCommGroup) ↦ @GlobalTheory.SeriesTie.Setup.finCl D (Formalism.BasicNotions.D7.nd D) (Formalism.BasicNotions.D7.ntw D) ρ i j b (@GlobalTheory.TwInputs.Move.twistDn D r Circle Circle.instCommGroup t))) ((fun (i : @Formalism.BasicNotions.NTw.Tw (Formalism.BasicNotions.D7.R D) (Formalism.BasicNotions.D7.host D) (Formalism.BasicNotions.D7.what₂ D) (Formalism.BasicNotions.D7.nfLL D) (Formalism.BasicNotions.D7.starLL D) (Formalism.BasicNotions.D7.LL0 D) (Formalism.BasicNotions.D7.nd D) (Formalism.BasicNotions.D7.ntw D)) (j : Fin (Formalism.BasicNotions.Ranks.m (Formalism.BasicNotions.D7.R D))) (b : Bool) (t : @GlobalTheory.ExportSeries.Twist (GlobalTheory.TwInputs.Move.overD D r) Circle Circle.instCommGroup) ↦ @GlobalTheory.SeriesTie.Setup.rep D (Formalism.BasicNotions.D7.nd D) (Formalism.BasicNotions.D7.ntw D) ρ i j b (@GlobalTheory.TwInputs.Move.twistDn D r Circle Circle.instCommGroup t))) ((ρ.β)) ((ρ.eG))

theorem sameTwist_dn {A : Type} [CommGroup A] {t : Twist D A} {t' : Twist (overD D r) A} (h : SameTwist t t') : t = twistDn r t' :=
  SameTwist.eq ⟨(h.Q), (h.chi), (h.res)⟩

theorem sameBase_up {S T : HSp D} (B : Base S T) : SameBase B (baseUp r B) :=
  ⟨(HEq.refl B.F.ψ), (HEq.refl B.F.θ), (HEq.refl B.F.sT), (HEq.refl B.F.BS), (HEq.refl B.F.BT), (HEq.refl B.F.ΛS), (HEq.refl B.F.ΛT), (HEq.refl B.F.βS), (HEq.refl B.F.βT), (HEq.refl B.F.f₀), (HEq.refl B.G.Pg), (HEq.refl B.G.P), (HEq.refl B.G.mu),
    ⟨(HEq.refl B.de.Q), (HEq.refl B.de.chi), (HEq.refl B.de.res)⟩, (HEq.refl B.w.p), (HEq.refl B.w.q), (HEq.refl B.w.ap), (HEq.refl B.w.am), (HEq.refl B.w.c), (HEq.refl B.w.lam),
    (HEq.refl B.mu0), (HEq.refl B.eta)⟩

theorem sameData_up (ρ : Setup D.ntw) : SameData ρ (setupUp r ρ) := by
  have hB : ∀ (i i' : D.ntw.Tw), HEq i i' → ∀ (j j' : Fin D.R.m), (j : ℕ) = j' → ∀ b, SameBase (ρ.B i j b) (baseUp r (ρ.B i' j' b)) :=
    fun _ _ hi _ _ hj _ => by cases hi; cases Fin.ext hj; exact sameBase_up r _
  have hC : ∀ (i i' : D.ntw.Tw), HEq i i' → ∀ (j j' : Fin D.R.m), (j : ℕ) = j' → ∀ b (t : Twist D Circle) (t' : Twist (overD D r) Circle),
      SameTwist t t' → ρ.Cl i j b t = ρ.Cl i' j' b (twistDn r t') ∧ HEq (ρ.rep i j b t) (ρ.rep i' j' b (twistDn r t')) :=
    fun _ _ hi _ _ hj _ _ _ ht => by cases hi; cases Fin.ext hj; cases sameTwist_dn r ht; exact ⟨rfl, .rfl⟩
  have hG : ∀ (i i' : D.ntw.Tw), HEq i i' → ∀ (j j' : Fin D.R.m), (j : ℕ) = j' → ∀ b, HEq (ρ.eG i j b) (ρ.eG i' j' b) :=
    fun _ _ hi _ _ hj _ => by cases hi; cases Fin.ext hj; exact .rfl
  exact ⟨(HEq.refl ρ.rc.κ), (HEq.refl ρ.rc.art), (HEq.refl ρ.ch), (HEq.refl ρ.bad), (HEq.refl ρ.e), (HEq.refl ρ.ek), (hB), (HEq.refl ρ.om), (hC),
    (HEq.refl ρ.β), (hG)⟩

end Up

theorem SameTwist.symm {A : Type} [CommGroup A] {t : Twist D A} {t' : Twist D' A} (h : SameTwist t t') : SameTwist t' t :=
  ⟨h.Q.symm, h.chi.symm, h.res.symm⟩

theorem SameTwist.trans {D'' : D7} {A : Type} [CommGroup A] {t : Twist D A} {t' : Twist D' A} {t'' : Twist D'' A} (h : SameTwist t t')
    (h' : SameTwist t' t'') : SameTwist t t'' := ⟨h.Q.trans h'.Q, h.chi.trans h'.chi, h.res.trans h'.res⟩

theorem SameBase.eq_of {S T : HSp D} {S' T' : HSp D'} {B : Base S T} {B₁ B₂ : Base S' T'} (h : SameBase B B₁) (h' : SameBase B B₂) :
    SameBase B₁ B₂ :=
  ⟨h.ψ.symm.trans h'.ψ, h.θ.symm.trans h'.θ, h.sT.symm.trans h'.sT, h.BS.symm.trans h'.BS, h.BT.symm.trans h'.BT, h.ΛS.symm.trans h'.ΛS, h.ΛT.symm.trans h'.ΛT, h.βS.symm.trans h'.βS, h.βT.symm.trans h'.βT, h.f₀.symm.trans h'.f₀, h.Pg.symm.trans h'.Pg, h.P.symm.trans h'.P, h.mu.symm.trans h'.mu, h.de.symm.trans h'.de, h.p.symm.trans h'.p, h.q.symm.trans h'.q, h.ap.symm.trans h'.ap, h.am.symm.trans h'.am, h.c.symm.trans h'.c, h.lam.symm.trans h'.lam, h.mu0.symm.trans h'.mu0, h.eta.symm.trans h'.eta⟩

theorem SameData.eq_up (r : Rest D) {ρ : Setup D.ntw} {ρ' : Setup (overD D r).ntw} (h : SameData ρ ρ') : ρ' = setupUp r ρ := by
  have u := sameData_up r ρ
  refine SameData.eq ⟨h.κ.symm.trans u.κ, h.art.symm.trans u.art, h.ch.symm.trans u.ch, h.bad.symm.trans u.bad, h.e.symm.trans u.e, h.ek.symm.trans u.ek, fun i i' hi j j' hj b => ?_,
    h.om.symm.trans u.om, fun i i' hi j j' hj b t t' ht => ?_, h.β.symm.trans u.β, fun i i' hi j j' hj b => ?_⟩
  · cases hi; cases Fin.ext hj
    exact (h.B ((i)) i ((HEq.refl i)) ((j)) j ((@Eq.refl Nat (@Fin.val (overD D r).R.m j))) b).eq_of
      (u.B ((i)) i ((HEq.refl i)) ((j)) j ((@Eq.refl Nat (@Fin.val (overD D r).R.m j))) b)
  · cases hi; cases Fin.ext hj; cases ht.eq
    have s : SameTwist (twistDn r t) t := ⟨(HEq.refl t.Q), (HEq.refl t.chi), (HEq.refl t.res)⟩
    have a := h.Cl ((i)) i ((HEq.refl i)) ((j)) j ((@Eq.refl Nat (@Fin.val (overD D r).R.m j))) b _ t s
    have c := u.Cl ((i)) i ((HEq.refl i)) ((j)) j ((@Eq.refl Nat (@Fin.val (overD D r).R.m j))) b _ t s
    exact ⟨a.1.symm.trans c.1, a.2.symm.trans c.2⟩
  · cases hi; cases Fin.ext hj
    exact (h.eG ((i)) i ((HEq.refl i)) ((j)) j ((@Eq.refl Nat (@Fin.val (overD D r).R.m j))) b).symm.trans
      (u.eG ((i)) i ((HEq.refl i)) ((j)) j ((@Eq.refl Nat (@Fin.val (overD D r).R.m j))) b)

theorem CopyTw.exists_sameData {ι : D.what₂.LL →+* D'.what₂.LL} {e : ↥D'.LL0 ≃+* ↥D.LL0} (h : CopyTw D D' ι e) (ρ : Setup D.ntw) :
    ∃ ρ' : Setup D'.ntw, SameData ρ ρ' := by
  obtain ⟨r, rfl⟩ := h.exists_rest
  exact ⟨setupUp r ρ, sameData_up r ρ⟩

end GlobalTheory.TwInputs.Move

end
