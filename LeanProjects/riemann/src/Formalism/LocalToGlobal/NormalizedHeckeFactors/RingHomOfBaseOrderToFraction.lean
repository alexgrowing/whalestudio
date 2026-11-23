import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalToGlobal.GaloisLevelStructure.TiedHecke
import Formalism.LocalToGlobal.GaloisLevelStructure.TiedLevel
import Formalism.LocalToGlobal.NormalizedHeckeFactors.ExpDefs
import Formalism.SharpRestriction.LevelLetterCocycles.TWSet

noncomputable section

open Formalism.BasicNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain
open scoped TensorProduct

namespace Formalism.L2

namespace NX

def badV (D : D7) (i : D.ntw.Tw) (Q : Finset (PlE D.host)) :
    Set (HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E))) :=
  {v | ∃ w : PlE D.host, NG.OverPl w v ∧
    (w ∈ Q ∨ (∃ k, w ∈ placesOver D.host.E (D.host.g k)) ∨ w ∈ D.ntw.pD i)}

def heckeSetF (D : D7) (i : D.ntw.Tw) (j : ℕ) (b : Bool) :
    Set (Module.End (FractionRing (D.ntw.O i)) (D.nexp.Fm i j b)) :=
  {T | ∃ (k : ℕ) (P : PlE D.host), 1 ≤ k ∧ k ≤ D.R.r ∧ IsSplitPl D.host P ∧ P ∉ D.ntw.S0 i ∧
    T = D.nexp.hkF i j b k P}

abbrev TWSet (D : D7) (i : D.ntw.Tw) (Q : Finset (PlE D.host)) : Prop :=
  Formalism.MainNotions.NAdm.TWSet D.ntw i Q

abbrev AdmQ (D : D7) (i : D.ntw.Tw) (Q : Finset (PlE D.host)) (M : ℕ) : Prop :=
  Formalism.MainNotions.NAdm.AdmQ D.ntw i Q M

def AdmTw (D : D7) (i : D.ntw.Tw) (k : ℕ) (Q : Finset (PlE D.host))
    (ψ : G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ) : Prop :=
  TWSet D i Q ∧ (∀ P ∈ Q, P ∉ D.ntw.pD i ∧ ∀ k' : Fin 2, P ∉ placesOver D.host.E (D.host.g k')) ∧
    IsOpen (ψ.ker : Set (G D.host.E D.nd.Om)) ∧ AntiHom D.ntw.cc ψ ∧ (∀ σ, ∃ N : ℕ, ψ σ ^ (D.ntw.l i ^ N) = 1) ∧
    ∀ P, P ∉ Q → ∀ A : ValuationSubring D.nd.Om, IsPlaceOver A P → ∀ σ ∈ Ine (F := D.host.E) A, ψ σ = 1

section Tame

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]

def TameRep (P : HeightOneSpectrum (𝓞 E)) (e : ℤ) (σ : G E Ω) (u : 𝓞 E) : Prop :=
  ∃ A : ValuationSubring Ω, IsPlaceOver A P ∧ σ ∈ Ine (F := E) A ∧ ∃ (ϖ : 𝓞 E) (π : Ω), ϖ ∈ P.asIdeal ∧
    ϖ ∉ P.asIdeal ^ 2 ∧ π ^ (normV P - 1) = algebraMap E Ω (ϖ : E) ∧
    A.valuation (σ π / π - (algebraMap E Ω (u : E)) ^ e) < 1

open Classical in

def tameVal {M : Type} [Monoid M] (φ : G E Ω →* M) (P : HeightOneSpectrum (𝓞 E)) (e : ℤ) (u : 𝓞 E) : M :=
  if h : ∃ σ, TameRep P e σ u then φ h.choose else 1

end Tame

open Classical in

def resRep {L : Type} [Field L] [NumberField L] [IsCMField L] (s : SplitPlace L) (P : HeightOneSpectrum (𝓞 L))
    (x : s.v.adicCompletion (maximalRealSubfield L)) : 𝓞 L :=
  if h : ∃ u : 𝓞 L, u ∉ P.asIdeal ∧ Valued.v (s.i (u : L) - x) < 1 then h.choose else 1

abbrev Kk (D : D7) (i : D.ntw.Tw) (k : ℕ) : Type := FractionRing (D.ntw.Ok i k)

def toKk (D : D7) (i : D.ntw.Tw) (k : ℕ) : FractionRing (D.ntw.O i) →+* Kk D i k :=
  IsFractionRing.map (A := D.ntw.O i) (B := D.ntw.Ok i k) (K := FractionRing (D.ntw.O i))
    (L := FractionRing (D.ntw.Ok i k)) (j := algebraMap (D.ntw.O i) (D.ntw.Ok i k)) (D.ntw.Ok_inj i k)

def ofOk (D : D7) (i : D.ntw.Tw) (k : ℕ) : D.ntw.Ok i k →+* Kk D i k := algebraMap _ _

def ofO0 (D : D7) (i : D.ntw.Tw) (k : ℕ) : D.ntw.O0 i →+* Kk D i k :=
  (ofOk D i k).comp ((algebraMap (D.ntw.O i) (D.ntw.Ok i k)).comp (algebraMap (D.ntw.O0 i) (D.ntw.O i)))

def ringHomOfBaseOrderToFraction (D : D7) (i : D.ntw.Tw) : D.ntw.O0 i →+* FractionRing (D.ntw.O i) :=
  (algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i))).comp (algebraMap (D.ntw.O0 i) (D.ntw.O i))

abbrev pG (D : D7) (kv : Σ k : Fin 2, D.nd.PlG k) : PlE D.host := D.naut.plGw kv.1 kv.2

open Classical in

def xiRed (D : D7) (kv : Σ k : Fin 2, D.nd.PlG k) : ZMod (D.host.g kv.1) :=
  if h : ∃ x : ZMod (D.host.g kv.1), ∃ a c : 𝓞 D.host.E, c ∉ (pG D kv).asIdeal ∧ (a : D.host.E) = D.host.xi0 * c ∧
      ((x.val : 𝓞 D.host.E) * c - a) ∈ (pG D kv).asIdeal then h.choose else 0

open Classical in

def psiUTot (D : D7) (i : D.ntw.Tw) (b : Bool) (u : G0g D.nd) : FractionRing (D.ntw.O i) :=
  if h : u ∈ D.nexp.U then ((D.nexp.psiU i b ⟨u, h⟩ : (FractionRing (D.ntw.O i))ˣ) : FractionRing (D.ntw.O i)) else 1

open Classical in

def gVal (D : D7) (i : D.ntw.Tw) (k : ℕ) (b : Bool) (kv : Σ k : Fin 2, D.nd.PlG k) (s : SplitPlace D.host.E)
    (red : s.v.adicCompletionIntegers (maximalRealSubfield D.host.E) →+* ZMod (D.host.g kv.1))
    (τ : (ZMod (D.host.g kv.1))ˣ →* (FractionRing (D.ntw.O i))ˣ)
    (x : Matrix (Fin D.R.nV) (Fin D.R.nV) (s.v.adicCompletion (maximalRealSubfield D.host.E))) : Kk D i k :=
  toKk D i k (psiUTot D i b (Pi.mulSingle kv
    (glOf (redMat s.v red (topR (Nat.le_add_right D.R.r D.R.t : D.R.r ≤ D.R.nV) x))))) *
  (if h : IsUnit (red (intLift s.v (detT D.R.r x))) then
    toKk D i k ((τ h.unit : (FractionRing (D.ntw.O i))ˣ) : FractionRing (D.ntw.O i)) else 1)

abbrev locM {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} (s : SplitPlace L) (κ : GAf L n) :
    Matrix (Fin n) (Fin n) (s.v.adicCompletion (maximalRealSubfield L)) :=
  ((s.loc n κ : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) :
    Matrix (Fin n) (Fin n) (s.v.adicCompletion (maximalRealSubfield L)))

structure MtVReal (D : D7) (i : D.ntw.Tw) (j : ℕ) (b : Bool) (k : ℕ) (Q : Finset (PlE D.host))
    (ψ : G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ) (e : ℤ) (W₀ : Type) [AddCommGroup W₀]
    [Module (FractionRing (D.ntw.O i)) W₀] (ρ₀ : Representation (FractionRing (D.ntw.O i)) (GQ D.host.E D.R.nV) W₀)
    (τ : ∀ kv : (Σ kk : Fin 2, D.nd.PlG kk), (ZMod (D.host.g kv.1))ˣ →* (FractionRing (D.ntw.O i))ˣ) where

  W : Type
  [acg : AddCommGroup W]
  [mod : Module (Kk D i k) W]
  [fd : FiniteDimensional (Kk D i k) W]
  ρ : Representation (Kk D i k) (GQ D.host.E D.R.nV) W
  irr : ρ.IsIrreducible
  alg : IsAlgWeightF D.host.E D.R.nV (Kk D i k) ρ

  bc : ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι) (b₀ : Module.Basis ι (FractionRing (D.ntw.O i)) W₀)
    (b₁ : Module.Basis ι (Kk D i k) W), ∀ γ : GQ D.host.E D.R.nV,
      LinearMap.toMatrix b₁ b₁ (ρ γ) = (LinearMap.toMatrix b₀ b₀ (ρ₀ γ)).map (toKk D i k)

  J : Subgroup (GAf D.host.E D.R.nV)
  χ : J →* (Kk D i k)ˣ
  J_open : ∃ N : ℕ, 0 < N ∧ ∀ κ, NG.Cong D.host.E D.R.nV N κ → ∃ h : κ ∈ J, χ ⟨κ, h⟩ = 1

  hyp : HypOutsideF J χ (badV D i Q)

  QP : Finset (PlE D.host)
  QP_sub : QP ⊆ Q
  QP_cover : ∀ P ∈ Q, ∃ P' ∈ QP, P' = P ∨ IsConjPl D.host P P'
  QP_nconj : ∀ P ∈ QP, ∀ P' ∈ QP, ¬ IsConjPl D.host P P'

  DP : Finset (PlE D.host)
  DP_sub : DP ⊆ D.ntw.pD i
  DP_cover : ∀ P ∈ D.ntw.pD i, ∃ P' ∈ DP, P' = P ∨ IsConjPl D.host P P'
  DP_nconj : ∀ P ∈ DP, ∀ P' ∈ DP, ¬ IsConjPl D.host P P'

  sp : PlE D.host → SplitPlace D.host.E
  sp_w : ∀ P, (P ∈ QP ∨ P ∈ DP ∨ ∃ kv, P = pG D kv) → (sp P).w = P

  redG : ∀ kv : (Σ kk : Fin 2, D.nd.PlG kk),
    (sp (pG D kv)).v.adicCompletionIntegers (maximalRealSubfield D.host.E) →+* ZMod (D.host.g kv.1)

  J_mem : ∀ κ : GAf D.host.E D.R.nV, κ ∈ J ↔ κ ∈ Umax D.host.E D.R.nV ∧
    (∀ kv, InLevG (sp (pG D kv)).v D.R.r (locM (sp (pG D kv)) κ)) ∧
    (∀ P ∈ QP, InParah (sp P).v D.R.r (locM (sp P) κ)) ∧ (∀ P ∈ DP, InParah (sp P).v D.R.r (locM (sp P) κ))

  chi_eq : ∀ κ (h : κ ∈ J), ((χ ⟨κ, h⟩ : (Kk D i k)ˣ) : Kk D i k) =
    (∏ kv : (Σ kk : Fin 2, D.nd.PlG kk), gVal D i k b kv (sp (pG D kv)) (redG kv) (τ kv) (locM (sp (pG D kv)) κ)) *
    (∏ P ∈ QP, ofOk D i k (tameVal ψ P e (resRep (sp P) P (detT D.R.r (locM (sp P) κ)))).1) *
    (∏ P ∈ DP, ofO0 D i k (tameVal (D.ntw.delta i) P (if b then e else -e)
      (resRep (sp P) P (detT D.R.r (locM (sp P) κ)))).1)

  real : D.nexp.MtV i j b k Q ψ ≃ₗ[Kk D i k] TypeSpF D.host.E D.R.nV (Kk D i k) ρ J χ

attribute [instance] MtVReal.acg MtVReal.mod MtVReal.fd

section HW

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {K : Type} [Field K]

open Classical in

def evPtF (c : L →+* L) (τ : L →+* K) (B : GL (Fin n) K) : (L →+* K) × Fin n × Fin n → K := fun p =>
  if p.1 = τ then B.val p.2.1 p.2.2
  else if p.1 = τ.comp c then (B⁻¹).val p.2.2 p.2.1
  else if p.2.1 = p.2.2 then 1 else 0

def HWAtF (c : L →+* L) {W : Type} [AddCommGroup W] [Module K W] (ρ : Representation K (GQ L n) W) (τ : L →+* K)
    (lam : Fin n → ℤ) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι) (b : Module.Basis ι K W)
    (P : ι → ι → MvPolynomial ((L →+* K) × Fin n × Fin n) K),
    (∀ (γ : GQ L n) (γ₀ : GL (Fin n) L),
      (((γ : GAf L n) : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) =
        (γ₀ : Matrix (Fin n) (Fin n) L).map (Algebra.TensorProduct.includeLeftRingHom) →
      LinearMap.toMatrix b b (ρ γ) =
        fun a a' => MvPolynomial.eval (fun p => p.1 ((γ₀ : Matrix (Fin n) (Fin n) L) p.2.1 p.2.2)) (P a a')) ∧
    ∃ v : ι → K, v ≠ 0 ∧ ∀ B : GL (Fin n) K, B.val.BlockTriangular id →
      Matrix.mulVec (Matrix.of fun a a' => MvPolynomial.eval (evPtF c τ B) (P a a')) v =
        (∏ a, (B.val a a) ^ (lam a)) • v

theorem hwAtF_trivial (c : L →+* L) (τ : L →+* K) :
    HWAtF (n := n) c (Representation.trivial K (GQ L n) K) τ 0 := by
  refine ⟨Unit, inferInstance, inferInstance, Module.Basis.singleton Unit K, fun _ _ => 1,
    fun γ γ₀ _ => ?_, fun _ => 1, fun h => one_ne_zero (congrFun h ()), fun B _ => ?_⟩
  · ext a a'
    simp [LinearMap.toMatrix_apply, Representation.trivial]
  · ext a
    simp [Matrix.mulVec, dotProduct]

end HW

def embEL0 (D : D7) : D.host.E →+* ↥D.LL0 where
  toFun x := ⟨D.embE x, D.hostField_le_fixedField x⟩
  map_one' := Subtype.ext (map_one D.embE)
  map_mul' x y := Subtype.ext (map_mul D.embE x y)
  map_zero' := Subtype.ext (map_zero D.embE)
  map_add' x y := Subtype.ext (map_add D.embE x y)

def cE (D : D7) : D.host.E →+* D.host.E := (D.host.conj : D.host.E →+* D.host.E)

def kEmb (D : D7) (i : D.ntw.Tw) (b : Bool) (t : D.what₂.Tau) : D.host.E →+* FractionRing (D.ntw.O i) :=
  (IsFractionRing.map (A := D.ntw.O0 i) (B := D.ntw.O i) (K := FractionRing (D.ntw.O0 i))
      (L := FractionRing (D.ntw.O i)) (D.ntw.O_inj i)).comp
    ((if b then D.ntw.emb0 i else D.ntw.emb0b i).comp
      ((embEL0 D).comp
        (D.host.sigmaOf ((D.eTau t : D.R.Psi) : D.R.GG) : D.host.E →+* D.host.E)))

theorem embLL_embEL0 (D : D7) (t : D.what₂.Tau) (x : D.host.E) :
    D.what₂.embLL ((embEL0 D (D.host.sigmaOf ((D.eTau t : D.R.Psi) : D.R.GG) x) : ↥D.LL0) :
      D.what₂.LL) = embT D t x := by
  have h := congrArg (fun f : D.host.E →+* ℂ =>
    f (D.host.sigmaOf ((D.eTau t : D.R.Psi) : D.R.GG) x)) D.embE_φ₀
  simpa [embEL0, embT, Host.emb] using h

end NX

open NX

structure NExpTied (D : D7) where

  U_eq : D.nexp.U = Uup (fun kv : (Σ k : Fin 2, D.nd.PlG k) => D.host.g kv.1) D.R.r

  psiU_gen : ∀ i b, IsStdGeneric (fun kv : (Σ k : Fin 2, D.nd.PlG k) => D.host.g kv.1) D.R.r (D.nexp.psiU i b)

  psiU_side : ∀ i (u : D.nexp.U), D.nexp.psiU i false u = (D.nexp.psiU i true u)⁻¹

  psiU_xi : ∀ i b, ∃ θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (FractionRing (D.ntw.O i))ˣ,
    (2 ≤ D.R.r → ∀ kk, θ kk ≠ 1) ∧ ∀ u : D.nexp.U, D.nexp.psiU i b u = ∏ kv : (Σ kk : Fin 2, D.nd.PlG kk),
      θ kv.1 (Multiplicative.ofAdd (xiRed D kv *
        supSum D.R.r (((u : G0g D.nd) kv : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) :
          Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1)))))

  delU_cont : ∀ i (Q : Finset (PlE D.host)) (M : ℕ), IsOpen ((D.nexp.delU i Q M).ker : Set (G D.host.E D.nd.Om))

  delU_ine : ∀ i (Q : Finset (PlE D.host)) (M : ℕ), AdmQ D i Q M → ∀ P (hP : P ∈ Q),
    (∀ A : ValuationSubring D.nd.Om, IsPlaceOver A P →
      Function.Surjective fun σ : Ine (F := D.host.E) A => Multiplicative.toAdd (D.nexp.delU i Q M σ) ⟨P, hP⟩) ∧
    ∀ P' ∈ Q, P' ≠ P → ¬ IsConjPl D.host P P' → ∀ A : ValuationSubring D.nd.Om, IsPlaceOver A P' →
      ∀ σ ∈ Ine (F := D.host.E) A, Multiplicative.toAdd (D.nexp.delU i Q M σ) ⟨P, hP⟩ = 0

  thU_empty : ∀ i j b M (d : D.nexp.Dat i j b), 1 ≤ j → j ≤ D.R.m →
    D.nexp.thU i j b ∅ M d = D.nexp.th i j b d ⊗ₜ[D.ntw.O i] (1 : AddMonoidAlgebra (D.ntw.O i) (DelQM D.host (D.ntw.l i) ∅ M))

  sgnT : ℤ

  sgnT_one : sgnT = 1

  Wt : D.ntw.Tw → ℕ → Bool → Type
  [acgWt : ∀ i j b, AddCommGroup (Wt i j b)]
  [modWt : ∀ i j b, Module (FractionRing (D.ntw.O i)) (Wt i j b)]
  [fdWt : ∀ i j b, FiniteDimensional (FractionRing (D.ntw.O i)) (Wt i j b)]
  rhoW : ∀ i j b, Representation (FractionRing (D.ntw.O i)) (GQ D.host.E D.R.nV) (Wt i j b)
  rhoW_irr : ∀ i j b, 1 ≤ j → j ≤ D.R.m → (rhoW i j b).IsIrreducible
  rhoW_alg : ∀ i j b, 1 ≤ j → j ≤ D.R.m → IsAlgWeightF D.host.E D.R.nV (FractionRing (D.ntw.O i)) (rhoW i j b)

  tauG : ∀ i, ℕ → Bool → ∀ kv : (Σ k : Fin 2, D.nd.PlG k), (ZMod (D.host.g kv.1))ˣ →* (FractionRing (D.ntw.O i))ˣ

  sgnG : ℤ

  sgnG_one : sgnG = 1

  tau_galois_first_character : ∀ i j b kv (x : (ZMod (D.host.g kv.1))ˣ) (u : 𝓞 D.host.E), 1 ≤ j → j ≤ D.R.m → pG D kv ∉ placesOver D.host.E (D.ntw.l i) →
    (((x : ZMod (D.host.g kv.1)).val : 𝓞 D.host.E) - u) ∈ (pG D kv).asIdeal →
    ((tauG i j b kv x : (FractionRing (D.ntw.O i))ˣ) : FractionRing (D.ntw.O i)) =
      ringHomOfBaseOrderToFraction D i (tameVal (D.ntw.chi1 i j b) (pG D kv) (sgnG * sgnT) u).1

  mtV : ∀ i j b k Q ψ, 1 ≤ j → j ≤ D.R.m → AdmTw D i k Q ψ →
    MtVReal D i j b k Q ψ sgnT (Wt i j b) (rhoW i j b) (tauG i j b)

  rhoW_hw : ∀ i j b (t : D.what₂.Tau), 1 ≤ j → j ≤ D.R.m →
    ∃ lam : Fin D.R.nV → ℤ, HWAtF (cE D) (rhoW i j b).dual (kEmb D i b t) lam

  rhoW_wt : ∀ i j b (t : D.what₂.Tau) (hj : 1 ≤ j) (hjm : j ≤ D.R.m) (sh : ℂ) (lam : Fin D.R.nV → ℤ),
    D.naut.infG D.naut.etaT (embT D t) = {sh} → HWAtF (cE D) (rhoW i j b).dual (kEmb D i b t) lam →
    NG.infOf lam = NG.paramV D.R (D.hc t) ⟨j - 1, by omega⟩ sh

attribute [instance] NExpTied.acgWt NExpTied.modWt NExpTied.fdWt

theorem eAlg_eq_of_eLL0_eq {R : Ranks} {H : Host R} {what₂ : Rows.Data R} [NumberField what₂.LL] [StarRing what₂.LL]
    {LL0 : IntermediateField ℚ what₂.LL} {N : NData R H what₂} {tw : NTw R H what₂ LL0 N} (Y Y' : NExp R H what₂ LL0 N tw)
    (h : Y.eLL0 = Y'.eLL0) (i : tw.Tw) (b : Bool) : Y.eAlg i b = Y'.eAlg i b := by
  refine MonoidAlgebra.ext (Finsupp.ext fun g => ?_)
  rw [Y.eAlg_def, Y'.eAlg_def, h]

theorem NExpTied.primRoot {D : D7} (T : NExpTied D) (hr : 2 ≤ D.R.r) (i : D.ntw.Tw) (k : Fin 2)
    (v : D.nd.PlG k) : ∃ ζ : FractionRing (D.ntw.O i), IsPrimitiveRoot ζ (D.host.g k) := by
  obtain ⟨θ, hθ, -⟩ := T.psiU_gen i true
  exact ⟨_, char_one_prim (D.host.g_prime k) (θ ⟨k, v⟩) (hθ hr ⟨k, v⟩)⟩

theorem NExpTied.psiU_ne_one {D : D7} (T : NExpTied D) (hr : 2 ≤ D.R.r) (i : D.ntw.Tw) (b : Bool) (k : Fin 2)
    (v : D.nd.PlG k) : ∃ u : D.nexp.U, D.nexp.psiU i b u ≠ 1 := by
  classical
  have : NeZero (D.host.g k) := ⟨(D.host.g_prime k).ne_zero⟩
  obtain ⟨θ, hθ, hψ⟩ := T.psiU_gen i b
  have hu : tvAt (p := fun kv : (Σ k : Fin 2, D.nd.PlG k) => D.host.g kv.1) hr ⟨k, v⟩ ∈ D.nexp.U := by
    rw [T.U_eq]; exact tvAt_mem hr _
  refine ⟨⟨_, hu⟩, ?_⟩
  rw [hψ, stdVal_tvAt]
  exact char_one_ne (θ ⟨k, v⟩) (hθ hr ⟨k, v⟩)

theorem NExpTied.U_ne_bot {D : D7} (T : NExpTied D) (hr : 2 ≤ D.R.r) (i : D.ntw.Tw) (k : Fin 2) (v : D.nd.PlG k) :
    D.nexp.U ≠ ⊥ := by
  intro h
  obtain ⟨u, hu⟩ := T.psiU_ne_one hr i true k v
  have : u = 1 := Subtype.ext (by simpa [h] using u.2)
  exact hu (by rw [this, map_one])

theorem NX.isStdGeneric_inv {ι : Type} [Fintype ι] {p : ι → ℕ} {r : ℕ} {K : Type} [Field K] {S : Subgroup (GProd p r)}
    (ψ ψ' : S →* Kˣ) (h : ∀ u, ψ' u = (ψ u)⁻¹) (hg : IsStdGeneric p r ψ) : IsStdGeneric p r ψ' := by
  obtain ⟨θ, hθ, hψ⟩ := hg
  refine ⟨fun x => (θ x)⁻¹, fun hr x hx => hθ hr x (inv_eq_one.mp hx), fun u => ?_⟩
  rw [h, hψ]
  simp only [stdVal, MonoidHom.inv_apply, Finset.prod_inv_distrib]

theorem NExpTied.delU_ne_one {D : D7} (T : NExpTied D) {i : D.ntw.Tw} {Q : Finset (PlE D.host)} {M : ℕ}
    (hQ : NX.AdmQ D i Q M) (hM : 1 ≤ M) {P : PlE D.host} (hP : P ∈ Q)
    (A : ValuationSubring D.nd.Om) (hA : IsPlaceOver A P) : D.nexp.delU i Q M ≠ 1 := by
  intro h1
  have hl : (D.ntw.l i).Prime := (D.ntw.lPrime i).out
  have h2 : 1 < D.ntw.l i ^ M := Nat.one_lt_pow (by omega) hl.one_lt
  have : Fact (1 < D.ntw.l i ^ M) := ⟨h2⟩
  obtain ⟨σ, hσ⟩ := (T.delU_ine i Q M hQ P hP).1 A hA 1
  rw [h1] at hσ
  simp at hσ

theorem NExpTied.delU_fac {D : D7} (T : NExpTied D) (i : D.ntw.Tw) (Q : Finset (PlE D.host)) (M : ℕ) (hQ : TWSet D i Q) :
    ∃ f : D.ntw.RCG i Q →* Multiplicative (DelQM D.host (D.ntw.l i) Q M),
      D.nexp.delU i Q M = f.comp (D.ntw.art i Q) := by
  have : Fact (D.ntw.l i).Prime := D.ntw.lPrime i
  have : NeZero (D.ntw.l i ^ M) := ⟨pow_ne_zero _ (Fact.out : (D.ntw.l i).Prime).ne_zero⟩
  obtain ⟨f, hf⟩ := D.ntw.art_univ i Q (fun v hv => (hQ v hv).2)
    (Multiplicative (DelQM D.host (D.ntw.l i) Q M))
    (fun x => ⟨M, by
      apply Multiplicative.toAdd.injective
      funext q
      simp [toAdd_pow, nsmul_eq_mul]⟩)
    (D.nexp.delU i Q M) (T.delU_cont i Q M) (D.nexp.delU_anti i Q M)
    (fun v hv A hA σ hσ => D.nexp.delU_unr i Q M v hv A hA σ hσ)
  exact ⟨f, hf.symm⟩

namespace NX

theorem MtVReal.conds_one {D : D7} {i : D.ntw.Tw} {j : ℕ} {b : Bool} {k : ℕ} {Q : Finset (PlE D.host)}
    {ψ : G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ} {e : ℤ} {W₀ : Type} [AddCommGroup W₀]
    [Module (FractionRing (D.ntw.O i)) W₀] {ρ₀ : Representation (FractionRing (D.ntw.O i)) (GQ D.host.E D.R.nV) W₀}
    {τ : ∀ kv : (Σ kk : Fin 2, D.nd.PlG kk), (ZMod (D.host.g kv.1))ˣ →* (FractionRing (D.ntw.O i))ˣ}
    (M : MtVReal D i j b k Q ψ e W₀ ρ₀ τ) :
    (1 : GAf D.host.E D.R.nV) ∈ Umax D.host.E D.R.nV ∧
    (∀ kv, InLevG (M.sp (pG D kv)).v D.R.r (locM (M.sp (pG D kv)) (1 : GAf D.host.E D.R.nV))) ∧
    (∀ P ∈ M.QP, InParah (M.sp P).v D.R.r (locM (M.sp P) (1 : GAf D.host.E D.R.nV))) ∧
    (∀ P ∈ M.DP, InParah (M.sp P).v D.R.r (locM (M.sp P) (1 : GAf D.host.E D.R.nV))) := by
  refine ⟨(Umax D.host.E D.R.nV).one_mem, fun kv => ?_, fun P _ => ?_, fun P _ => ?_⟩
  · simpa [locM] using inLevG_one (n := D.R.nV) (M.sp (pG D kv)).v D.R.r
  · simpa [locM] using inParah_one (n := D.R.nV) (M.sp P).v D.R.r
  · simpa [locM] using inParah_one (n := D.R.nV) (M.sp P).v D.R.r

theorem gVal_isUnit (D : D7) (i : D.ntw.Tw) (k : ℕ) (b : Bool) (kv : Σ k : Fin 2, D.nd.PlG k)
    (s : SplitPlace D.host.E) (red : s.v.adicCompletionIntegers (maximalRealSubfield D.host.E) →+* ZMod (D.host.g kv.1))
    (τ : (ZMod (D.host.g kv.1))ˣ →* (FractionRing (D.ntw.O i))ˣ)
    (x : Matrix (Fin D.R.nV) (Fin D.R.nV) (s.v.adicCompletion (maximalRealSubfield D.host.E))) :
    IsUnit (gVal D i k b kv s red τ x) := by
  classical
  unfold gVal
  refine IsUnit.mul (IsUnit.map _ ?_) ?_
  · unfold psiUTot
    split_ifs
    · exact Units.isUnit _
    · exact isUnit_one
  · split_ifs
    · exact (Units.isUnit _).map _
    · exact isUnit_one

theorem MtVReal.qprod_eq {D : D7} {i : D.ntw.Tw} {j : ℕ} {b : Bool} {k : ℕ} {Q : Finset (PlE D.host)}
    {ψ ψ' : G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ} {e : ℤ} {W₀ : Type} [AddCommGroup W₀]
    [Module (FractionRing (D.ntw.O i)) W₀] {ρ₀ : Representation (FractionRing (D.ntw.O i)) (GQ D.host.E D.R.nV) W₀}
    {τ : ∀ kv : (Σ kk : Fin 2, D.nd.PlG kk), (ZMod (D.host.g kv.1))ˣ →* (FractionRing (D.ntw.O i))ˣ}
    (M : MtVReal D i j b k Q ψ e W₀ ρ₀ τ) (M' : MtVReal D i j b k Q ψ' e W₀ ρ₀ τ)
    (hJ : M.J = M'.J) (hχ : ∀ κ (h : κ ∈ M.J) (h' : κ ∈ M'.J), M.χ ⟨κ, h⟩ = M'.χ ⟨κ, h'⟩)
    (hQP : M'.QP = M.QP) (hDP : M'.DP = M.DP) (hsp : M'.sp = M.sp)
    (hg : ∀ κ, (∏ kv : (Σ kk : Fin 2, D.nd.PlG kk),
        gVal D i k b kv (M.sp (pG D kv)) (M.redG kv) (τ kv) (locM (M.sp (pG D kv)) κ)) =
      ∏ kv : (Σ kk : Fin 2, D.nd.PlG kk),
        gVal D i k b kv (M'.sp (pG D kv)) (M'.redG kv) (τ kv) (locM (M'.sp (pG D kv)) κ))
    (κ : GAf D.host.E D.R.nV) (h : κ ∈ M.J) :
    (∏ P ∈ M.QP, ofOk D i k (tameVal ψ P e (resRep (M.sp P) P (detT D.R.r (locM (M.sp P) κ)))).1) =
      ∏ P ∈ M.QP, ofOk D i k (tameVal ψ' P e (resRep (M.sp P) P (detT D.R.r (locM (M.sp P) κ)))).1 := by
  have h' : κ ∈ M'.J := hJ ▸ h
  have e1 := M.chi_eq κ h
  have e2 := M'.chi_eq κ h'
  rw [hχ κ h h', e2, hQP, hDP, ← hg κ, hsp] at e1
  have hA : (∏ kv : (Σ kk : Fin 2, D.nd.PlG kk),
      gVal D i k b kv (M.sp (pG D kv)) (M.redG kv) (τ kv) (locM (M.sp (pG D kv)) κ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun kv _ => (gVal_isUnit D i k b kv _ _ _ _).ne_zero
  have hC : (∏ P ∈ M.DP, ofO0 D i k (tameVal (D.ntw.delta i) P (if b then e else -e)
      (resRep (M.sp P) P (detT D.R.r (locM (M.sp P) κ)))).1) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun P _ => ((Units.isUnit _).map (ofO0 D i k)).ne_zero
  exact (mul_left_cancel₀ hA (mul_right_cancel₀ hC e1)).symm

example {D : D7} {i : D.ntw.Tw} {j : ℕ} {b : Bool} {k : ℕ} {Q : Finset (PlE D.host)}
    {ψ ψ' : G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ} {e : ℤ} {W₀ : Type} [AddCommGroup W₀]
    [Module (FractionRing (D.ntw.O i)) W₀] {ρ₀ : Representation (FractionRing (D.ntw.O i)) (GQ D.host.E D.R.nV) W₀}
    {τ : ∀ kv : (Σ kk : Fin 2, D.nd.PlG kk), (ZMod (D.host.g kv.1))ˣ →* (FractionRing (D.ntw.O i))ˣ}
    (M : MtVReal D i j b k Q ψ e W₀ ρ₀ τ)
    (E' : D.nexp.MtV i j b k Q ψ' ≃ₗ[Kk D i k] D.nexp.MtV i j b k Q ψ) : True := by
  fail_if_success
    have _x : MtVReal D i j b k Q ψ' e W₀ ρ₀ τ := { M with real := E'.trans M.real }
  trivial

def MtVReal.transferTame {D : D7} {i : D.ntw.Tw} {j : ℕ} {b : Bool} {k : ℕ} {Q : Finset (PlE D.host)}
    {ψ ψ' : G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ} {e : ℤ} {W₀ : Type} [AddCommGroup W₀]
    [Module (FractionRing (D.ntw.O i)) W₀] {ρ₀ : Representation (FractionRing (D.ntw.O i)) (GQ D.host.E D.R.nV) W₀}
    {τ : ∀ kv : (Σ kk : Fin 2, D.nd.PlG kk), (ZMod (D.host.g kv.1))ˣ →* (FractionRing (D.ntw.O i))ˣ}
    (M : MtVReal D i j b k Q ψ e W₀ ρ₀ τ) (hT : ∀ P u, tameVal ψ P e u = tameVal ψ' P e u)
    (E' : D.nexp.MtV i j b k Q ψ' ≃ₗ[Kk D i k] D.nexp.MtV i j b k Q ψ) :
    MtVReal D i j b k Q ψ' e W₀ ρ₀ τ :=
  { M with
    chi_eq := fun κ h => by rw [M.chi_eq κ h]; simp only [hT]
    real := E'.trans M.real }

theorem MtVReal.finrank_W {D : D7} {i : D.ntw.Tw} {j : ℕ} {b : Bool} {k : ℕ} {Q : Finset (PlE D.host)}
    {ψ : G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ} {e : ℤ} {W₀ : Type} [AddCommGroup W₀]
    [Module (FractionRing (D.ntw.O i)) W₀] {ρ₀ : Representation (FractionRing (D.ntw.O i)) (GQ D.host.E D.R.nV) W₀}
    {τ : ∀ kv : (Σ kk : Fin 2, D.nd.PlG kk), (ZMod (D.host.g kv.1))ˣ →* (FractionRing (D.ntw.O i))ˣ}
    (M : MtVReal D i j b k Q ψ e W₀ ρ₀ τ) :
    Module.finrank (Kk D i k) M.W = Module.finrank (FractionRing (D.ntw.O i)) W₀ := by
  obtain ⟨ι, _, _, b₀, b₁, -⟩ := M.bc
  rw [Module.finrank_eq_card_basis b₀, Module.finrank_eq_card_basis b₁]

end NX

theorem NExpTied.infOf_hw_eq {D : D7} (T T' : NExpTied D) (i : D.ntw.Tw) (j : ℕ) (b : Bool) (t : D.what₂.Tau) (hj : 1 ≤ j)
    (hjm : j ≤ D.R.m) (sh : ℂ) (hsh : D.naut.infG D.naut.etaT (embT D t) = {sh}) {lam lam' : Fin D.R.nV → ℤ}
    (h : HWAtF (cE D) (T.rhoW i j b).dual (kEmb D i b t) lam)
    (h' : HWAtF (cE D) (T'.rhoW i j b).dual (kEmb D i b t) lam') : NG.infOf lam = NG.infOf lam' := by
  rw [T.rhoW_wt i j b t hj hjm sh lam hsh h, T'.rhoW_wt i j b t hj hjm sh lam' hsh h']

def HWDet (D : D7) (i : D.ntw.Tw) (b : Bool) : Prop :=
  ∀ (W W' : Type) [AddCommGroup W] [Module (FractionRing (D.ntw.O i)) W] [AddCommGroup W']
    [Module (FractionRing (D.ntw.O i)) W'] (ρ : Representation (FractionRing (D.ntw.O i)) (GQ D.host.E D.R.nV) W)
    (ρ' : Representation (FractionRing (D.ntw.O i)) (GQ D.host.E D.R.nV) W'),
    ρ.IsIrreducible → ρ'.IsIrreducible → IsAlgWeightF D.host.E D.R.nV (FractionRing (D.ntw.O i)) ρ →
    IsAlgWeightF D.host.E D.R.nV (FractionRing (D.ntw.O i)) ρ' →
    (∀ t : D.what₂.Tau, ∃ lam lam' : Fin D.R.nV → ℤ, HWAtF (cE D) ρ.dual (kEmb D i b t) lam ∧
      HWAtF (cE D) ρ'.dual (kEmb D i b t) lam' ∧ NG.infOf lam = NG.infOf lam') →
    ∃ e : W ≃ₗ[FractionRing (D.ntw.O i)] W', ∀ γ x, e (ρ γ x) = ρ' γ (e x)

theorem NExpTied.rhoW_iso {D : D7} (T T' : NExpTied D) (i : D.ntw.Tw) (j : ℕ) (b : Bool) (hj : 1 ≤ j) (hjm : j ≤ D.R.m)
    (hsh : ∀ t : D.what₂.Tau, ∃ sh, D.naut.infG D.naut.etaT (embT D t) = {sh}) (hD : HWDet D i b) :
    ∃ e : T.Wt i j b ≃ₗ[FractionRing (D.ntw.O i)] T'.Wt i j b,
      ∀ γ x, e (T.rhoW i j b γ x) = T'.rhoW i j b γ (e x) := by
  refine hD _ _ (T.rhoW i j b) (T'.rhoW i j b) (T.rhoW_irr i j b hj hjm) (T'.rhoW_irr i j b hj hjm) (T.rhoW_alg i j b hj hjm)
    (T'.rhoW_alg i j b hj hjm) fun t => ?_
  obtain ⟨sh, hs⟩ := hsh t
  obtain ⟨lam, hl⟩ := T.rhoW_hw i j b t hj hjm
  obtain ⟨lam', hl'⟩ := T'.rhoW_hw i j b t hj hjm
  exact ⟨lam, lam', hl, hl', T.infOf_hw_eq T' i j b t hj hjm sh hs hl hl'⟩

end Formalism.L2
