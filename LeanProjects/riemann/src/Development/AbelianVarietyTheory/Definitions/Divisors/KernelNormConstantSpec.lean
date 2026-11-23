import Mathlib
import Formalism.LocalToGlobal.KernelLattices.ThDistC
import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open scoped TensorProduct nonZeroDivisors
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker

namespace GlobalTheory.FunObj

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {T : Type}

open Classical in

def wtOf (n : ℕ) (E : Finset ℚ) : DomWeight n :=
  if h : E.card = n ∧ InCoset (((n : ℚ) - 1) / 2) E then
    ⟨fun a => ⌊highestWeight E h.1 a⌋, fun _ _ hab => Int.floor_mono (highestWeight_antitone h.1 h.2 hab)⟩
  else ⟨0, antitone_const⟩

theorem wtOf_cast {n : ℕ} {E : Finset ℚ} (h : E.card = n) (hE : InCoset (((n : ℚ) - 1) / 2) E) (a : Fin n) :
    ((wtOf n E).w a : ℚ) = highestWeight E h a := by
  obtain ⟨z, hz⟩ := highestWeight_int h hE a
  simp [wtOf, dif_pos (And.intro h hE), hz]

theorem wtOf_top_zero (C : ℝ) (τ : D.what₂.Tau) :
    wtOf (rankP D D.R.m) (entries (Node.par D C (.top 0) τ)) = La D C τ := by
  have e : entries (Node.par D C (.top 0) τ) = (num D C τ).weightX 0 := entries_plus _
  have h : InCoset (((rankP D D.R.m : ℚ) - 1) / 2) ((num D C τ).weightX 0) := fun x hx => by
    obtain ⟨y, rfl⟩ := inCoset_weightX_zero (G := num D C τ) (odd_sLen D) x hx
    obtain ⟨u, hu⟩ := even_rankP D D.R.m
    exact ⟨y + 1 - u, by rw [hu]; push_cast; ring⟩
  rw [e, wtOf, dif_pos ⟨card_weight D C τ, h⟩]
  rfl

def dualSubst (K ι : Type) [Field K] (n : ℕ) : Pol K ι n →ₐ[K] Pol K ι n :=
  aeval fun v => (Matrix.of fun a s : Fin n => (X (v.1, a, s) : Pol K ι n)).adjugate v.2.2.rev v.2.1

def IsFunForm {K ι : Type} [Field K] [Fintype ι] {n : ℕ} (σ : ι → DomWeight n) (F : VV K σ)
    (f : VV K fun τ => (σ τ).dual) : Prop :=
  f.1 * ∏ τ, frDet K n τ ^ (∑ a, (σ τ).natW a) =
    dualSubst K ι n F.1 * ∏ τ, frDet K n τ ^ (-(σ τ).dual.detShift - (σ τ).detShift).toNat

def DefNode (m : ℕ) : Node → Prop
  | .top j => j ≤ m
  | .grid i j => i ≤ m ∧ j = m
  | .core _ => False

def DefPair (m : ℕ) : Pair T → Prop
  | .top _ j => j + 1 ≤ m
  | .chi i j => i + 1 ≤ m ∧ j = m
  | _ => False

theorem DefPair.nodes {m : ℕ} {p : Pair T} (h : DefPair m p) : DefNode m p.small ∧ DefNode m p.big := by
  cases p <;> simp only [DefPair, DefNode] at h ⊢ <;> omega

def opp : Pair T → (ℂ →+* ℂ)
  | .chi _ _ => starRingEnd ℂ
  | .core _ => starRingEnd ℂ
  | _ => RingHom.id ℂ

def period (δ : ℂ) (τ : D.what₂.Tau) : ℂ := δ / (Real.sqrt (2 * Real.pi * ‖tauE D τ D.host.xi0‖) : ℂ)

variable {L : LevCh D T} {sc : Consts} (G : ChiGrid.GridData L sc)

def listedWt (X : Node) (τ : D.what₂.Tau) : DomWeight (G.V X).rank := wtOf _ (entries (Node.par D sc.cGap X τ))

def wt : ∀ X : Node, D.what₂.Tau → DomWeight (G.V X).rank
  | .grid i j, τ => (listedWt G (.grid i j) τ).dual
  | .core i, τ => listedWt G (.core i) τ
  | .top j, τ => listedWt G (.top j) τ

theorem wt_top_zero (h : (G.V (.top 0)).rank = rankP D D.R.m) (τ : D.what₂.Tau) (a : Fin (G.V (.top 0)).rank) :
    (wt G (.top 0) τ).w a = (La D sc.cGap τ).w (Fin.cast h a) := by
  have key : ∀ n (h : n = rankP D D.R.m) (a : Fin n),
      (wtOf n (entries (Node.par D sc.cGap (.top 0) τ))).w a = (La D sc.cGap τ).w (Fin.cast h a) := by
    rintro _ rfl a
    rw [wtOf_top_zero]; rfl
  exact key _ h a

def nuEnd (p : Pair T) (τ : D.what₂.Tau) : ℕ :=
  if h : (G.V p.small).rank - 1 < (G.V p.big).rank then (wt G p.big τ).natW ⟨_, h⟩ else 0

def fockDeg (p : Pair T) (τ : D.what₂.Tau) : ℕ := ∑ a, (wt G p.big τ).natW a

def WtOK (p : Pair T) : Prop :=
  (∀ τ, IsHC (G.V p.small).rank (Node.par D sc.cGap p.small τ) ∧ IsHC (G.V p.big).rank (Node.par D sc.cGap p.big τ)) ∧
    JetInVV ℂ (wt G p.small) (wt G p.big) (nuEnd G p)

def fvar : ∀ p : Pair T, DVar D.what₂.Tau (G.V p.small).rank (G.V p.big).rank → FVar D (G.pT p).rank (G.pS p).rank
  | .chi _ _, k => (k.1, k.2.2, k.2.1)
  | .mu _ _ _, k => k
  | .core _, k => (k.1, k.2.2, k.2.1)
  | .top _ _, k => k

abbrev FinPt (X : Node) : Type := GfC (G.V X)

abbrev VertexFrames : Type := ∀ X : Node, D.what₂.Tau → Matrix (Fin (G.V X).rank) (Fin (G.V X).rank) ℂ

structure FinDatum (t : T) (p : Pair T) where

  P : Finset (Pl D.host.E)

  P_over : ∀ w ∈ P, w.under (𝓞 D.host.F) ∈ G.pl.S0 ∨ ∃ w' ∈ L.Q t, w.under (𝓞 D.host.F) = w'.under (𝓞 D.host.F)

  e : AE D

  e_is : IsIdemSum e P

  fn : WO (G.pS p) (G.pT p) → ℂ

  sb : IsSBHalf e (latO (G.pS p) (G.pT p) (G.latS p : Set _) (G.latT p : Set _) fun _ => True) fn

  z : GA D (G.pS p)

  z_cen : ∃ c : AE D, mt _ z = c • (1 : Matrix _ _ (AE D))

  z_supp : ∃ (P' : Finset (Pl D.host.E)) (e' : AE D), IsIdemSum e' P' ∧ SuppAt e' _ z ∧ ∀ w ∈ P',
    FractionalIdeal.count D.host.E w D.host.AA ≠ 0 ∨ FractionalIdeal.count D.host.E w D.host.AAbar ≠ 0

theorem halfInd_congr {m n : ℕ} {e : AE D} {Λ Λ' : AddSubgroup (Mx D m n)} {x y : Mx D m n}
    (h : (x ∈ Λ ∧ IsHalf e x) ↔ (y ∈ Λ' ∧ IsHalf e y)) : halfInd e Λ x = halfInd e Λ' y := by
  unfold halfInd
  by_cases h1 : x ∈ Λ ∧ IsHalf e x
  · rw [if_pos h1, if_pos (h.1 h1)]
  · rw [if_neg h1, if_neg (h.not.1 h1)]

def FinDatum.ind (t : T) (p : Pair T) (P : Finset (Pl D.host.E))
    (h : ∀ w ∈ P, w.under (𝓞 D.host.F) ∈ G.pl.S0 ∨ ∃ w' ∈ L.Q t, w.under (𝓞 D.host.F) = w'.under (𝓞 D.host.F))
    (e : AE D) (he : IsIdemSum e P) : FinDatum G t p where
  P := P
  P_over := h
  e := e
  e_is := he
  fn := halfInd e (latO (G.pS p) (G.pT p) (G.latS p : Set _) (G.latT p : Set _) fun _ => True)
  sb := by
    refine ⟨fun x hx => ?_, 1, one_pos, fun u hu hu' x => ?_, fun x hx => ?_⟩
    · by_contra h; exact hx (if_neg fun h' => h h'.2)
    · rw [one_smul]
      have h1 : IsHalf e (x + u) ↔ IsHalf e x := forall₂_congr fun i j => by
        rw [Matrix.add_apply, mul_add, hu' i j, add_left_inj]
      exact halfInd_congr (and_congr (AddSubgroup.add_mem_cancel_right _ hu) h1)
    · rw [one_smul]; by_contra h; exact hx (if_neg fun h' => h h'.1)
  z := 1
  z_cen := ⟨1, by simp [Formalism.L2.Theta.mt]⟩
  z_supp := ⟨∅, 0, ⟨⟨0, by simp, by simp⟩, by simp⟩, fun i j => by simp [Formalism.L2.Theta.mt], by simp⟩

def FinDatum.vacuum (t : T) (p : Pair T) : FinDatum G t p :=
  FinDatum.ind G t p ∅ (by simp) 0 ⟨⟨0, by simp, by simp⟩, by simp⟩

variable {G} (W : G.Weil)

def FinDatum.IsTheta {t : T} {p : Pair T} (d : FinDatum G t p) (ΛS : Submodule (𝓞 D.host.E) (Fin (G.pS p).rank → D.host.E))
    (ΛT : Submodule (𝓞 D.host.E) (Fin (G.pT p).rank → D.host.E)) (f₀ f : WO (G.pS p) (G.pT p) → ℂ) : Prop :=
  IsThetaAt W.ψ (symplO _ _) (heisO W.ψ _ _) d.e (latO (G.pS p) (G.pT p) (ΛS : Set _) (ΛT : Set _) fun _ => True) 1 f₀ d.fn f

def FinDatum.vec {t : T} {p : Pair T} (d : FinDatum G t p) (ΛS : Submodule (𝓞 D.host.E) (Fin (G.pS p).rank → D.host.E))
    (ΛT : Submodule (𝓞 D.host.E) (Fin (G.pT p).rank → D.host.E)) (f₀ : WO (G.pS p) (G.pT p) → ℂ) : WO (G.pS p) (G.pT p) → ℂ :=
  W.om p (d.z, 1) (Classical.epsilon (d.IsTheta W ΛS ΛT f₀))

theorem FinDatum.vec_eq {t : T} {p : Pair T} {d : FinDatum G t p} {ΛS ΛT f₀ f} (h : d.IsTheta W ΛS ΛT f₀ f) :
    d.vec W ΛS ΛT f₀ = W.om p (d.z, 1) f := by
  obtain ⟨Tm, hT⟩ := h.1
  rw [FinDatum.vec, (Classical.epsilon_spec (p := d.IsTheta W ΛS ΛT f₀) ⟨f, h⟩).2 Tm hT, h.2 Tm hT]

def kerFin (p : Pair T) (f : WO (G.pS p) (G.pT p) → ℂ) (x : FinPt G p.small) (y : FinPt G p.big) : ℂ := W.ker p f x y

def fockIn (B : VertexFrames G) (p : Pair T) (f : WO (G.pS p) (G.pT p) → ℂ) :
    PolF D (G.pT p).rank (G.pS p).rank →ₗ[ℂ] (WO (G.pS p) (G.pT p) → ℂ) :=
  pureTensorO W.ψ W.θ _ _ (G.cartS W.cart p) (G.onT W.cart p) (G.onS B p) (G.onT B p) f

theorem fockIn_onb (p : Pair T) (f : WO (G.pS p) (G.pT p) → ℂ) : fockIn W W.onb p f = W.fock p f := rfl

def jetTab (B : VertexFrames G) (p : Pair T) (f : WO (G.pS p) (G.pT p) → ℂ) (x : FinPt G p.small) (y : FinPt G p.big)
    (k : DVar D.what₂.Tau (G.V p.small).rank (G.V p.big).rank →₀ ℕ) : ℂ :=
  kerFin W p (fockIn W B p f (monomial (k.mapDomain (fvar G p)) 1)) x y

def fockComp (B : VertexFrames G) (p : Pair T) (f : WO (G.pS p) (G.pT p) → ℂ) (x : FinPt G p.small) (y : FinPt G p.big) :
    VV ℂ (wt G p.small) →ₗ[ℂ] VV ℂ (wt G p.big) :=
  jetOp _ _ (jetTab W B p f x y) (nuEnd G p)

def Off (S : Finset ℕ) (w : Pl D.host.E) : Prop := ∀ q ∈ S, (q : 𝓞 D.host.E) ∉ w.asIdeal

def UnrIdem (χ : (AE D)ˣ →* Circle) (e : AE D) : Prop :=
  ∀ x : (AE D)ˣ, e * x + (1 - e) = x → finPart D (x : AE D) ∈ intAE D → finPart D ((x⁻¹ : (AE D)ˣ) : AE D) ∈ intAE D → χ x = 1

variable (G) in

def topEmb : Matrix (Fin (G.V (.top D.R.m)).rank) (Fin (G.V (.grid D.R.m D.R.m)).rank) (AE D) :=
  (frameMat _ _ G.sp.topDec.ι).map (incA D)

variable (G) in

def topVec : Fin (G.V (.top D.R.m)).rank → AE D := fun i => incA D (G.sp.topDec.a i 0)

variable (G) in

structure Std (U : Set T) where

  S : Finset ℕ

  prime : ∀ q ∈ S, q.Prime

  off : ∀ w : Pl D.host.E, Off S w → w.under (𝓞 D.host.F) ∉ G.pl.S0 ∧
    (∀ t ∈ U, ∀ w' ∈ L.Q t, w.under (𝓞 D.host.F) ≠ w'.under (𝓞 D.host.F)) ∧
    ((D.host.condN * D.host.g 0 * D.host.g 1 * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal

  unr : ∀ w : Pl D.host.E, Off S w → ∀ e, Formalism.L2.NTheta.IsIdemAt e w → ∀ t ∈ U, ∀ j, 1 ≤ j → j ≤ D.R.m → UnrIdem (L.mu t j) e

  fr : ∀ X : Node, GL (Fin (G.V X).rank) D.host.E

  fr_on : ∀ X, DefNode D.R.m X → Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (fr X).1 * (G.V X).gram * (fr X).1 = 1

  u : ∀ X : Node, FinPt G X

  u_supp : ∀ X, DefNode D.R.m X → ∃ (P : Finset (Pl D.host.E)) (e : AE D),
    IsIdemSum e P ∧ SuppAt e _ (u X).1 ∧ ∀ w ∈ P, Off S w

  u_lat : ∀ X, DefNode D.R.m X → ∀ v, v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat (fr X)) ↔
    (Formalism.IndefR.Lev.finE (G.V X) (u X).1).1 *ᵥ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (G.Λ X)

  fr_top : ∀ i (k : Fin (G.V (.grid D.R.m D.R.m)).rank), (fr (.top D.R.m)).1 i (Formalism.L2.Col.Br.iC G.sp.topDec.rank.symm k) =
    (frameMat _ _ G.sp.topDec.ι * (fr (.grid D.R.m D.R.m)).1) i k

  fr_last : ∀ i, (fr (.top D.R.m)).1 i (Formalism.L2.Col.Br.iL G.sp.topDec.rank.symm) = G.sp.topDec.a i 0

  u_top : HMul.hMul (mt (G.V (.top D.R.m)) (u (.top D.R.m)).1) (topEmb G) =
    HMul.hMul (topEmb G) (mt (G.V (.grid D.R.m D.R.m)) (u (.grid D.R.m D.R.m)).1)

  u_last : mt (G.V (.top D.R.m)) (u (.top D.R.m)).1 *ᵥ topVec G = topVec G

namespace Std

variable {U : Set T} (N : Std G U)

def frC : VertexFrames G := fun X τ => (N.fr X).1.map (tauE D τ)

def latS : ∀ p : Pair T, Submodule (𝓞 D.host.E) (Fin (G.pS p).rank → D.host.E)
  | .chi i j => colLat (N.fr (.grid (i + 1) j))
  | .mu _ i j => colLat (N.fr (.grid i j))
  | .core i => colLat (N.fr (.core (i + 1)))
  | .top _ j => colLat (N.fr (.top j))

def latT : ∀ p : Pair T, Submodule (𝓞 D.host.E) (Fin (G.pT p).rank → D.host.E)
  | .chi i j => colLat (N.fr (.grid i j))
  | .mu _ i j => colLat (N.fr (.grid i (j + 1)))
  | .core i => colLat (N.fr (.core i))
  | .top _ j => colLat (N.fr (.top (j + 1)))

end Std

structure Normal {U : Set T} (N : Std G U) where

  δ : ℂ

  crv : Formalism.MainNotions.StandardLatticesGL3.Crv D D.host.ccK δ

  t0 : ℂ

  pt0 : Formalism.MainNotions.GL3Theta.IsTwoTorsionPointUnkilled D (Formalism.MainNotions.TaylorLogMetric.lamOf D D.host.ccK δ) t0

  e0 : ∀ p : Pair T, Formalism.MainNotions.TaylorLogMetric.VC D (G.pS p).rank (G.pT p).rank → ℂ

  e0_is : ∀ p, DefPair D.R.m p → Formalism.MainNotions.StandardLatticesGL3.oddE0 D D.host.ccK δ t0 _ _ (e0 p)

  vac : ∀ p : Pair T, WO (G.pS p) (G.pT p) → ℂ

  vac_is : ∀ p, DefPair D.R.m p →
    IsVacO W.ψ W.θ _ _ (G.cartS W.cart p) (G.onT W.cart p) (N.latS p : Set _) (N.latT p : Set _) (vac p)

  c0 : Pair T → ℂˣ

  kernelNorm_constant_spec : ∀ p, DefPair D.R.m p → ∀ k : FVar D (G.pT p).rank (G.pS p).rank →₀ ℕ,
    fockIn W N.frC p (vac p) (monomial k 1) 0 =
      c0 p * opp p ((k.prod fun v n => period δ v.1 ^ n) * Formalism.MainNotions.GL3Theta.applyAt0 D (monomial k 1) (e0 p))

  free : ∀ t t' j, e0 (.top t j) = e0 (.top t' j) ∧ vac (.top t j) = vac (.top t' j) ∧ c0 (.top t j) = c0 (.top t' j)

namespace Normal

variable {W} {U : Set T} {N : Std G U} (Z : Normal W N) {t : T} {p : Pair T}

def vec (d : FinDatum G t p) : WO (G.pS p) (G.pT p) → ℂ := d.vec W (N.latS p) (N.latT p) (Z.vac p)

def HasVec (d : FinDatum G t p) : Prop := ∃ f, d.IsTheta W (N.latS p) (N.latT p) (Z.vac p) f

def scal (c : D.what₂.Tau → ℂ) (p : Pair T) : ℂ :=
  ((Z.c0 p)⁻¹ : ℂˣ) * ∏ τ, opp p (c τ / period Z.δ τ) ^ fockDeg G p τ

def kkMap (c : D.what₂.Tau → ℂ) (d : FinDatum G t p) (x : FinPt G p.small) (y : FinPt G p.big) :
    VV ℂ (wt G p.small) →ₗ[ℂ] VV ℂ (wt G p.big) :=
  Z.scal c p • fockComp W N.frC p (Z.vec d) (x * N.u _) (y * N.u _)

def kkFr (c : D.what₂.Tau → ℂ) (d : FinDatum G t p) (x : FinPt G p.small) (y : FinPt G p.big) :
    VV ℂ (wt G p.small) →ₗ[ℂ] VV ℂ (wt G p.big) :=
  rhoVr (tauE D) (wt G p.big) (N.fr _) ∘ₗ Z.kkMap c d x y ∘ₗ rhoVr (tauE D) (wt G p.small) (N.fr _)⁻¹

open Classical in

def kkIn (c : D.what₂.Tau → ℂ) (d : FinDatum G t p) (x : FinPt G p.small) (y : FinPt G p.big) :
    Matrix (VVIdx (wt G p.big)) (VVIdx (wt G p.small)) ℂ :=
  LinearMap.toMatrix (bVV ℂ _) (bVV ℂ _) (Z.kkMap c d x y)

def kk (d : FinDatum G t p) (x : FinPt G p.small) (y : FinPt G p.big) :
    Matrix (VVIdx (wt G p.big)) (VVIdx (wt G p.small)) ℂ := Z.kkIn 1 d x y

def IsRatIn (c : D.what₂.Tau → ℂ) (d : FinDatum G t p) (x : FinPt G p.small) (y : FinPt G p.big) : Prop :=
  ∀ a b, Z.kkIn c d x y a b ∈ Set.range D.what₂.embLL

def IsRatAt (d : FinDatum G t p) (x : FinPt G p.small) (y : FinPt G p.big) : Prop := Z.IsRatIn 1 d x y

theorem kkIn_eq (c : D.what₂.Tau → ℂ) (d : FinDatum G t p) (x : FinPt G p.small) (y : FinPt G p.big) :
    Z.kkIn c d x y = (∏ τ, opp p (c τ) ^ fockDeg G p τ) • Z.kk d x y := by
  rw [kk, kkIn, kkIn, ← map_smul, kkMap, kkMap, smul_smul]
  congr 2
  simp only [scal, div_eq_mul_inv, map_mul, mul_pow, Finset.prod_mul_distrib, Pi.one_apply, map_one, one_pow,
    Finset.prod_const_one]
  ring

theorem isTheta_vacuum (t : T) (p : Pair T) :
    (FinDatum.vacuum G t p).IsTheta W (N.latS p) (N.latT p) (Z.vac p) (Z.vac p) := by
  have h0 : ∀ x : WO (G.pS p) (G.pT p), IsHalf (0 : AE D) x → x = 0 := fun x hx =>
    Matrix.ext fun i j => by rw [← hx i j, zero_mul]; rfl
  have hi : ∀ Λ Λ' : AddSubgroup (WO (G.pS p) (G.pT p)), halfInd (0 : AE D) Λ = halfInd 0 Λ' := fun Λ Λ' => funext fun x => by
    have : (x ∈ Λ ∧ IsHalf (0 : AE D) x) ↔ (x ∈ Λ' ∧ IsHalf (0 : AE D) x) :=
      and_congr_left fun hx => by rw [h0 x hx]; simp
    exact halfInd_congr this
  have hz : ∀ f, heisO W.ψ (G.pS p) (G.pT p) 0 f = f := fun f => funext fun w => by simp [heisO, symplOH, symplO, hO]
  refine ⟨⟨(LinearMap.proj 0 : (_ → ℂ) →ₗ[ℂ] ℂ).smulRight (Z.vac p), fun Φ _ x hx => ?_, fun Φ _ y hy => ?_, ?_⟩,
    fun Tm hT => ?_⟩
  · obtain rfl := h0 x hx
    rw [hz]; simp
  · obtain rfl := h0 y (by simpa [FinDatum.vacuum, FinDatum.ind] using hy)
    rw [hz]; simp [symplO, hO]
  · simp [halfInd, IsHalf]
  · have := hT.vac
    rw [one_smul] at this
    exact this.symm.trans (congrArg Tm (hi _ _))

theorem jetTab_vacuum (t : T) (hp : DefPair D.R.m p) (k : DVar D.what₂.Tau (G.V p.small).rank (G.V p.big).rank →₀ ℕ) :
    jetTab W N.frC p (Z.vec (FinDatum.vacuum G t p)) ((N.u _)⁻¹ * N.u _) ((N.u _)⁻¹ * N.u _) k =
      Z.c0 p * opp p (((k.mapDomain (fvar G p)).prod fun v n => period Z.δ v.1 ^ n) *
        Formalism.MainNotions.GL3Theta.applyAt0 D (monomial (k.mapDomain (fvar G p)) 1) (Z.e0 p)) := by
  have h1 : G.toPair p 1 1 = 1 := by cases p <;> simp [GridData.toPair, Prod.ext_iff]
  have h2 : W.om p (1, 1) = 1 := map_one _
  rw [← Z.kernelNorm_constant_spec p hp, vec, FinDatum.vec_eq W (Z.isTheta_vacuum t p), inv_mul_cancel, inv_mul_cancel]
  simp [jetTab, kerFin, GridData.Weil.ker, thetaKO, h1, h2, FinDatum.vacuum, FinDatum.ind]

end Normal

example : ((wtOf 2 {3 / 2, -1 / 2}).w 0 : ℚ) = 1 := by
  have h : ({3 / 2, -1 / 2} : Finset ℚ).card = 2 := by decide +kernel
  rw [wtOf_cast h (by
    intro x hx
    rcases Finset.mem_insert.1 hx with rfl | hx
    · exact ⟨1, by norm_num⟩
    · exact ⟨-1, by rw [Finset.mem_singleton.1 hx]; norm_num⟩), highestWeight,
    descEnum_unique h (f := ![3 / 2, -1 / 2]) (by decide +kernel) (by decide +kernel)]
  norm_num

example (i j : ℕ) : opp (.chi i j : Pair T) Complex.I = -Complex.I := Complex.conj_I

end GlobalTheory.FunObj
