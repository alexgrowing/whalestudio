import Formalism.LocalToGlobal.IndefiniteReal.Bridge
import Formalism.LocalToGlobal.Divisibility.CoefMod
import Formalism.LocalToGlobal.Divisibility.DefGroup
import Formalism.LocalToGlobal.IndefiniteReal.IndefiniteWeightData

open NumberField IsDedekindDomain
open scoped TensorProduct

noncomputable section

namespace Formalism.IndefR.Bridge

open Formalism.L2.Theta Formalism.L2.DIV Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.HermitianLatticesTheory Formalism.BasicNotions

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7}

def hLat (V : Formalism.BasicNotions.TH.HSp D) (h : Gf V) : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E) :=
  Submodule.span (𝓞 D.host.E)
    (Set.ofPred fun x : Fin V.rank → D.host.E =>
      (Units.val ((h⁻¹ : Gf V) : GL (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E))).mulVec
          (fun i => (1 : Af D.host.F) ⊗ₜ[D.host.F] x i) ∈ latHat D.host.F D.host.E (L0c D V))

def IsRatMat (V : Formalism.BasicNotions.TH.HSp D) (γ : GQ V) (γE : GL (Fin V.rank) D.host.E) : Prop :=
  matHom V (γ : GA D V) = Formalism.UG.bc (incA D) γE

def CoefTie (V : Formalism.BasicNotions.TH.HSp D) (C : CoefDat D V) {S : CSD D.what₂.LL} {J : Subgroup (Gf V)} {χ : J →* ℂˣ}
    (P : ClassPres (ratF V) S D.what₂.embLL C.ρ J χ) (lam : D.what₂.Tau → DomWeight V.rank)
    (c0 : VV D.what₂.LL lam →ₛₗ[D.what₂.embLL] C.W)
    (pair : VV D.what₂.LL lam →ₗ⋆[D.what₂.LL] VV D.what₂.LL lam →ₗ[D.what₂.LL] D.what₂.LL)
    (nab del : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E) → Submodule (𝓞 D.what₂.LL) (VV D.what₂.LL lam)) : Prop :=
  ∃ e : S.V ≃ₗ[D.what₂.LL] VV D.what₂.LL lam,
    (∀ i j, (bVV D.what₂.LL lam).repr (e (S.bV i)) j ∈ Formalism.DivisionValues.cmMax D.what₂.LL) ∧
    (∀ x, P.coef x = c0 (e x)) ∧
    (∀ x x', pair (e x) (e x') = S.pair x x') ∧
    (∀ c, (S.Nab c).map ((e : S.V →ₗ[D.what₂.LL] VV D.what₂.LL lam).restrictScalars (𝓞 D.what₂.LL)) =
      nab (hLat V (P.y c))) ∧
    (∀ c, (S.Del c).map ((e : S.V →ₗ[D.what₂.LL] VV D.what₂.LL lam).restrictScalars (𝓞 D.what₂.LL)) =
      del (hLat V (P.y c)))

def CoefMapTie (V : Formalism.BasicNotions.TH.HSp D) (C : CoefDat D V) {lam : D.what₂.Tau → DomWeight V.rank}
    (c0 : VV D.what₂.LL lam →ₛₗ[D.what₂.embLL] C.W)
    (rho : GL (Fin V.rank) D.host.E →* Module.End D.what₂.LL (VV D.what₂.LL lam)) : Prop :=
  (∀ (γ : GQ V) (γE : GL (Fin V.rank) D.host.E), IsRatMat V γ γE → ∀ v, c0 (rho γE v) = C.ρ γ (c0 v)) ∧
    LinearIndependent ℂ (fun i => c0 (bVV D.what₂.LL lam i)) ∧
    Submodule.span ℂ (Set.range fun i => c0 (bVV D.what₂.LL lam i)) = ⊤

def SplitOff (P : Pl D.host.E) (S : Set (Pl D.host.E)) : Prop :=
  conjIdeal (K := D.host.E) P.asIdeal ≠ P.asIdeal ∧ P ∉ S ∧ ∀ Q ∈ S, Q.asIdeal ≠ conjIdeal (K := D.host.E) P.asIdeal

def IsWtOfPar {N : ℕ} (lam : DomWeight N) (S : Formalism.BasicNotions.TH.SPar) : Prop :=
  S.card = N ∧ ∃ c : Fin N → ℚ, StrictAnti c ∧ (∀ i, ∃ s, (c i, s) ∈ S) ∧ ∀ i, (lam.w i : ℚ) = c i - rhoVec N i

def lamRdef (P : Formalism.BasicNotions.TH.TPar D) (τ : D.what₂.Tau) : DomWeight D.sp.X'.rank :=
  open Classical in
  if h : ∃ lam : DomWeight D.sp.X'.rank, IsWtOfPar lam (P.Dpar D.R.m τ) then h.choose
  else ⟨0, antitone_const⟩

def LamRForced (P : Formalism.BasicNotions.TH.TPar D) : Prop :=
  ∀ τ, IsWtOfPar (lamRdef P τ) (P.Dpar D.R.m τ)

def IsLamPrime {N : ℕ} (lam : DomWeight N) (j : ℕ) (τ : D.what₂.Tau) : Prop :=
  ∃ (hj : 1 ≤ j ∧ j - 1 < D.R.m) (W : Formalism.IndefR.IndefiniteWeightData.WeightData), W.k = D.R.k ∧ W.m = D.R.m ∧ W.t = D.R.t ∧ W.j = j ∧
    (W.e : ℚ) = (D.hc τ).e ⟨j - 1, hj.2⟩ ∧
    (∀ a : Fin (D.R.k - 1), (W.v (a + 2) : ℚ) = (D.hc τ).v a) ∧
    (∀ a : Fin D.R.m, (W.b (a + 1) : ℚ) = (D.hc τ).b a) ∧
    ∀ i : Fin N, (lam.w i : ℚ) = W.lamPrime (i + 1)

def lamLdef (n j : ℕ) (τ : D.what₂.Tau) : DomWeight n :=
  open Classical in
  if h : ∃ lam : DomWeight n, IsLamPrime lam j τ then h.choose else ⟨0, antitone_const⟩

def LamLForced (D : Formalism.BasicNotions.D7) : Prop :=
  ∀ j : ℕ, 1 ≤ j → j ≤ D.R.m → ∀ τ : D.what₂.Tau, IsLamPrime (D := D) (lamLdef (D := D) (D.sp.V j).rank j τ) j τ

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {m : ℕ}

structure FamTie {A : FamIn D.what₂.LL G Pl0 T m} {cR : CoefDat D D.sp.X'} {cL : ∀ i : Fin m, CoefDat D (D.sp.V ((i : ℕ) + 1))}
    {lR : ∀ t, LevEnv D D.sp.X' (A.ok t × ℕ)} {lL : ∀ (i : Fin m) t, LevEnv D (D.sp.V ((i : ℕ) + 1)) (A.ok t × ℕ)}
    (B : FamReal D A cR cL lR lL)
    (pl : Pl0 → Pl D.host.E) (S : Set (Pl D.host.E)) (Qt : T → Finset (Pl D.host.E))
    (tauL : D.what₂.Tau → (D.host.E →+* D.what₂.LL))
    (lamR : D.what₂.Tau → DomWeight D.sp.X'.rank)
    (lamL : ∀ (i : Fin m), D.what₂.Tau → DomWeight (D.sp.V ((i : ℕ) + 1)).rank)
    (gramR : Matrix (Fin D.sp.X'.rank) (Fin D.sp.X'.rank) D.host.E)
    (c0R : VV D.what₂.LL lamR →ₛₗ[D.what₂.embLL] cR.W)
    (c0L : ∀ i : Fin m, VV D.what₂.LL (lamL i) →ₛₗ[D.what₂.embLL] (cL i).W) : Prop where
  ranks : m = D.R.m ∧ A.r = D.R.r ∧ A.t = D.R.t
  v0 : A.v0 = InfinitePlace.mk D.what₂.embLL
  tauL_ok : ∀ τ, D.what₂.embLL.comp (tauL τ) = Formalism.BasicNotions.TH.tauE D τ
  pl_inj : Function.Injective pl
  q : ∀ P, A.q P = Nat.card (kP (pl P))
  S_fin : S.Finite
  ok : ∀ t P, P ∈ A.ok t ↔ SplitOff (pl P) (S ∪ (Qt t : Set (Pl D.host.E)))
  gramR_eq : gramR = D.sp.X'.gram ∨ gramR = -D.sp.X'.gram
  mapR : CoefMapTie D.sp.X' cR c0R (rhoV tauL lamR)
  mapL : ∀ i : Fin m, CoefMapTie (D.sp.V ((i : ℕ) + 1)) (cL i) (c0L i) (rhoVr tauL (lamL i))
  coefR : ∀ t, CoefTie D.sp.X' cR (B.R t).pres lamR c0R (pairV tauL lamR gramR) (nabAt tauL lamR) (delAt tauL lamR)
  coefL : ∀ (i : Fin m) t, CoefTie (D.sp.V ((i : ℕ) + 1)) (cL i) (B.L i t).pres (lamL i) (c0L i)
    (pairVr tauL (lamL i)
      (if D.sp.Vneg ((i : ℕ) + 1) then -(D.sp.V ((i : ℕ) + 1)).gram else (D.sp.V ((i : ℕ) + 1)).gram))
    (nabAtr tauL (lamL i)) (delAtr tauL (lamL i))

end Formalism.IndefR.Bridge
