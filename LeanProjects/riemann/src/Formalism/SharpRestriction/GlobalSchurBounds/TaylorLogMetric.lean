import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.ParConsts
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice

noncomputable section

namespace Formalism.MainNotions.TaylorLogMetric

open NumberField Formalism.BasicNotions Classical
open scoped Pointwise

def vec22 (D : D7) (T : Tor D) (e : FamE D) : Prop :=
  ∀ N N' L L', admitted D N N' L L' →
    e N N' L L' ∈ Th D T L L' ∧ e N N' L L' ≠ 0 ∧
    ∃ M : IntermediateField ℚ ℂ, FiniteDimensional ℚ M ∧ CoefIn D (e N N' L L') M

def per22 (D : D7) (T : Tor D) : Prop :=
  ∀ (M : IntermediateField ℚ ℂ) [NumberField M], DataIn D T M →
    ∀ τ : D.what₂.Tau, meanLogOm D T.abelian₂ M τ = logOmVal D

def th22 (D : D7) (T : Tor D) (C : ℝ) (e : FamE D) : Prop :=
  (∀ N N' L₁ L₁' L₂ L₂', admitted D N N' L₁ L₁' → admitted D N N' L₂ L₂' →
    normSq D T (La D T L₁ L₁') (e N N' L₁ L₁') = normSq D T (La D T L₂ L₂') (e N N' L₂ L₂')) ∧
  (∀ Lsc : ℝ, Real.log D.host.v + |logDerivativeAtOne D| ≤ Lsc →
    ∀ N N' L L', admitted D N N' L L' →
      ∀ (M : IntermediateField ℚ ℂ) [FiniteDimensional ℚ M], DataIn D T M → CoefIn D (e N N' L L') M →
        meanLogNormSq D T L L' M (e N N' L L') ≤ C * (fF D : ℝ) * (N : ℝ) * (N' : ℝ) * Lsc) ∧
  (∀ N N' L₁ L₁' L₂ L₂', admitted D N N' L₁ L₁' → admitted D N N' L₂ L₂' →
    ∀ (M : IntermediateField ℚ ℂ) [FiniteDimensional ℚ M], DataIn D T M →
      CoefIn D (e N N' L₁ L₁') M → CoefIn D (e N N' L₂ L₂') M → ∀ ρ : M →ₐ[ℚ] ℂ,
        normSq D (torConj D T M ρ) (La D (torConj D T M ρ) L₁ L₁') (fnConj D M ρ (e N N' L₁ L₁')) =
          normSq D (torConj D T M ρ) (La D (torConj D T M ρ) L₂ L₂') (fnConj D M ρ (e N N' L₂ L₂'))) ∧
  (∀ N N' L L', admitted D N N' L L' → ∀ x : VC D N N',
    normSq D T (La D T L L') (U D T x (e N N' L L')) = normSq D T (La D T L L') (e N N' L L'))

def eq22 (D : D7) (T : Tor D) (χ : IdE D → ℂ) (e : FamE D) : Prop :=
  letI := D.host.cmStar
  (∀ N N' (L : SDLat D.host.E N) (L' : SDLat D.host.E N'), Even N → Even N' →
    ∀ (γ : Matrix.unitaryGroup (Fin N) D.host.E) (γ' : Matrix.unitaryGroup (Fin N') D.host.E),
      pull D T (γ : Matrix (Fin N) (Fin N) D.host.E) (γ' : Matrix (Fin N') (Fin N') D.host.E)
          (e N N' L.1 L'.1) =
        e N N' (SDLat.smulLat (γ : Matrix (Fin N) (Fin N) D.host.E) L.1)
          (SDLat.smulLat (γ' : Matrix (Fin N') (Fin N') D.host.E) L'.1)) ∧
  (∀ N N' (L : SDLat D.host.E N) (L' L'' : SDLat D.host.E N'), Even N → Even N' →
    e N N' L.1 L''.1 = fun z => (χ (detId D L'.1 L''.1)) ^ (-((N / 2 : ℕ) : ℤ)) *
      Iop D T (La D T L.1 L'.1) (La D T L.1 L''.1) (e N N' L.1 L'.1) z) ∧
  (∀ N N' (L L₁ : SDLat D.host.E N) (L' : SDLat D.host.E N'), Even N → Even N' →
    e N N' L₁.1 L'.1 = fun z => (χ (detId D L.1 L₁.1)) ^ (((N' / 2 : ℕ) : ℤ)) *
      Iop D T (La D T L.1 L'.1) (La D T L₁.1 L'.1) (e N N' L.1 L'.1) z)

def chiQ (D : D7) : D.Dt ⧸ D.UO →* ℂˣ :=
  QuotientGroup.lift D.UO D.chiD (fun x hx => MonoidHom.mem_ker.mpr (D.chiD_UO x hx))

def RelDetPinned (D : D7) (idl : D.Dt ⧸ D.UO → IdE D) : Prop :=
  letI := D.host.cmStar
  Function.Injective idl ∧ (∀ 𝔞, N1 D 𝔞 ↔ ∃ x, idl x = 𝔞) ∧ (∀ x y, idl (x * y) = idl x * idl y) ∧
  (∀ z : unitary D.host.E, idl (QuotientGroup.mk (D.e1Dt z)) =
    Submodule.span (𝓞 D.host.E) {(z : D.host.E)}) ∧
  ∀ N (L L' : SDLat D.host.E N), idl (D.relDet N L L') = detId D L.1 L'.1

def chiRec (D : D7) (idl : D.Dt ⧸ D.UO → IdE D) : IdE D → ℂ :=
  fun 𝔞 => if h : ∃ x, idl x = 𝔞 then ((chiQ D h.choose : ℂˣ) : ℂ) else 0

def RelativeDeterminantEquation (D : D7) (T : Tor D) (e : FamE D) : Prop :=
  letI := D.host.cmStar
  (∀ N N' (L : SDLat D.host.E N) (L' : SDLat D.host.E N'), Even N → Even N' →
    ∀ (γ : Matrix.unitaryGroup (Fin N) D.host.E) (γ' : Matrix.unitaryGroup (Fin N') D.host.E),
      pull D T (γ : Matrix (Fin N) (Fin N) D.host.E) (γ' : Matrix (Fin N') (Fin N') D.host.E)
          (e N N' L.1 L'.1) =
        e N N' (SDLat.smulLat (γ : Matrix (Fin N) (Fin N) D.host.E) L.1)
          (SDLat.smulLat (γ' : Matrix (Fin N') (Fin N') D.host.E) L'.1)) ∧
  (∀ N N' (L : SDLat D.host.E N) (L' L'' : SDLat D.host.E N'), Even N → Even N' →
    e N N' L.1 L''.1 = fun z => ((chiQ D (D.relDet N' L' L'') ^ (-((N / 2 : ℕ) : ℤ)) : ℂˣ) : ℂ) *
      Iop D T (La D T L.1 L'.1) (La D T L.1 L''.1) (e N N' L.1 L'.1) z) ∧
  (∀ N N' (L L₁ : SDLat D.host.E N) (L' : SDLat D.host.E N'), Even N → Even N' →
    e N N' L₁.1 L'.1 = fun z => ((chiQ D (D.relDet N L L₁) ^ (((N' / 2 : ℕ) : ℤ)) : ℂˣ) : ℂ) *
      Iop D T (La D T L.1 L'.1) (La D T L₁.1 L'.1) (e N N' L.1 L'.1) z)

theorem chiRec_idl (D : D7) (idl : D.Dt ⧸ D.UO → IdE D) (h : Function.Injective idl) (x : D.Dt ⧸ D.UO) :
    chiRec D idl (idl x) = ((chiQ D x : ℂˣ) : ℂ) := by
  have hx : ∃ y, idl y = idl x := ⟨x, rfl⟩
  unfold chiRec
  rw [dif_pos hx, h hx.choose_spec]

def DualB (D : D7) {N : ℕ} (P : D.what₂.Tau → Matrix (Fin N) (Fin N) D.host.E) : Prop :=
  ∀ τ, ((P (tauSg D τ)).map D.host.conj).transpose * P τ = 1

def zB (D : D7) {N N' : ℕ} {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p])
    (P : D.what₂.Tau → Matrix (Fin N) (Fin N) D.host.E) (P' : D.what₂.Tau → Matrix (Fin N') (Fin N') D.host.E)
    (τ : D.what₂.Tau) (a : Fin N') (b : Fin N) : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p] :=
  ∑ i : Fin N', ∑ j : Fin N,
    algebraMap ℂ_[p] (MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p])
      ((((P' τ).map (tauEmb D lam τ))⁻¹) a i * ((P τ).map (tauEmb D lam τ)) j b) * MvPowerSeries.X (τ, i, j)

def QdB (D : D7) {N N' : ℕ} {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (u : D.what₂.Tau → ℂ_[p])
    (P : D.what₂.Tau → Matrix (Fin N) (Fin N) D.host.E) (P' : D.what₂.Tau → Matrix (Fin N') (Fin N') D.host.E) :
    MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p] :=
  ∑ τ : D.what₂.Tau, ∑ a : Fin N', ∑ b : Fin N,
    algebraMap ℂ_[p] (MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p]) (u τ) *
      zB D lam P P' τ a b * zB D lam P P' (tauSg D τ) a b

def int22 (D : D7) (T : Tor D) (e : FamE D) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (N N' : ℕ)
    (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)),
    admitted D N N' L L' →
    (p ≠ D.host.d → ∀ F : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p], IsComb D T e lam L L' F →
      (∀ (C : WeierstrassCurve.VariableChange ℂ_[p]) (wq : PowerSeries ℂ_[p]) (r : ℕ)
          (b : Fin r → Matrix (Fin N') (Fin N) D.host.E),
        IsModel lam T.abelian₂ C → IsWq (C • wModel lam T.abelian₂) wq → LocBasis D p (YYl D L L') b →
        Orthonormal D b →
        IntegralMv (atLog D lam T.abelian₂ C wq b F * ePh lam T.abelian₂ C wq r)) ∧
      JetsInt D lam (YYl D L L') F ∧
      ((p = 2 ∨ jacobiSym (-(D.host.d : ℤ)) p = 1) →
        ∀ (C : WeierstrassCurve.VariableChange ℂ_[p]) (wq : PowerSeries ℂ_[p]) (r : ℕ)
          (b : Fin r → Matrix (Fin N') (Fin N) D.host.E),
        IsModel lam T.abelian₂ C → IsWq (C • wModel lam T.abelian₂) wq → LocBasis D p (YYl D L L') b →
        IntegralMv (atLog D lam T.abelian₂ C wq b F))) ∧
    (p = D.host.d →
      ∃ S : ℂ_[p], ‖S‖ ≤ (p : ℝ) ^ ((1 : ℝ) / 2) ∧
        ∃ u : D.what₂.Tau → ℂ_[p], (∀ τ, ‖u τ‖ = 1) ∧ (∀ τ, u (tauSg D τ) = u τ) ∧
          ∀ (P : D.what₂.Tau → Matrix (Fin N) (Fin N) D.host.E)
            (P' : D.what₂.Tau → Matrix (Fin N') (Fin N') D.host.E),
          (∀ τ, LocBasisW D (tauEmb D lam τ) L (P τ)) → (∀ τ, LocBasisW D (tauEmb D lam τ) L' (P' τ)) →
          DualB D P → DualB D P' →
          ∀ F : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p], IsComb D T e lam L L' F →
          ∃ F₀, F = expMv (-(algebraMap ℂ_[p] _ S) * QdB D lam u P P') * F₀ ∧
            JetsInt D lam (YYl D L L') F₀)

def mom22 (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (e : FamE D) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]),
    (p = 2 ∨ jacobiSym (-(D.host.d : ℤ)) p = 1) → Nat.Coprime (Ideal.absNorm cc) p →
    ∃ Ω : ℂ_[p], IsOmP lam (tor0 D cc δ).abelian₂ Ω ∧
    ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
      (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (r : ℕ)
      (b : Fin r → Matrix (Fin N') (Fin N) D.host.E),
      admitted D N N' L L' → NNBasis D (tor0 D cc δ) δ p L L' b →
      ∃ μ : C(Fin r → ℤ_[p], ℂ_[p]) →L[ℂ_[p]] ℂ_[p], ‖μ‖ ≤ 1 ∧
        (∀ (m : ℕ) (y : Fin m → Matrix (Fin N') (Fin N) D.host.E) (g : C(Fin r → ℤ_[p], ℂ_[p])),
          (∀ a, g a = ∏ j, pairN D lam Ω b (y j) a) →
          jet D lam y (pSer D lam (e N N' L L')) = μ g) ∧
        ∀ (n : ℕ) (ε : 𝓞 D.host.K) (Φ : LocallyConstant (Fin r → ℤ_[p]) ℂ),
          IsIdem D lam (2 * n + 2) ε → (∀ a, Φ a ∈ Qbar) → FactorsMod n Φ →
          ∀ (m : ℕ) (y : Fin m → Matrix (Fin N') (Fin N) D.host.E) (g : C(Fin r → ℤ_[p], ℂ_[p])),
            (∀ a, g a = lamC lam (Φ a) * ∏ j, pairN D lam Ω b (y j) a) →
            jet D lam y (pSer D lam (XiF D (tor0 D cc δ) δ p n ε b Φ (e N N' L L'))) = μ g

def LargerSupportMomentCondition (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (e : FamE D) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]),
    (p = 2 ∨ jacobiSym (-(D.host.d : ℤ)) p = 1) → Nat.Coprime (Ideal.absNorm cc) p →
    ∀ (N N' : ℕ) (L L₁ : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
      (L' L₂ : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (r : ℕ)
      (b b₁ : Fin r → Matrix (Fin N') (Fin N) D.host.E) (c : Fin r → Fin r → D.host.K),
      admitted D N N' L L' → admitted D N N' L₁ L₂ → EqAway D p L L₁ → EqAway D p L' L₂ →
      NNBasis D (tor0 D cc δ) δ p L L' b → NNBasis D (tor0 D cc δ) δ p L₁ L₂ b₁ →
      (∀ j, b j = ∑ i, ((c i j : D.host.K) : D.host.E) • b₁ i) →
      (∀ i j, ‖lamC lam (D.host.φ₀ (D.host.conj ((c i j : D.host.K) : D.host.E)))‖ ≤ 1) →
      ∀ (n : ℕ) (ε : 𝓞 D.host.K) (Φ : LocallyConstant (Fin r → ℤ_[p]) ℂ),
        IsIdem D lam (2 * n + 2) ε → FactorsMod n Φ →
        (∀ a, Φ a = if ∃ x : Fin r → ℤ_[p], ∀ i, zc (a i) =
            ∑ j, lamC lam (D.host.φ₀ (D.host.conj ((c i j : D.host.K) : D.host.E))) * zc (x j)
          then 1 else 0) →
        ∃ κ : ℂ, κ ∈ Qbar ∧ ‖lamC lam κ‖ = 1 ∧
          XiF D (tor0 D cc δ) δ p n ε b₁ Φ (e N N' L₁ L₂) = fun z => κ * e N N' L L' z

def sE (D : D7) {N N' p d : ℕ} [Fact p.Prime] (Po : Pos D p d) (v : {v // v ∈ Po.V}) (e : ZMod d)
    (a : Fin N) (b : Fin N') : MvPowerSeries (TVar D Po N N') ℂ_[p] :=
  fun α => ∑ l ∈ Finset.range ((α.sum fun _ k => k) + 1),
    if α = Finsupp.single ((e - 2 * (l : ZMod d), (v, a, b)) : TVar D Po N N') ((p ^ 2) ^ l)
    then (-1 : ℂ_[p]) ^ l else 0

def hh (D : D7) {N N' p d : ℕ} [Fact p.Prime] [NeZero d] (Po : Pos D p d) (v : {v // v ∈ Po.V})
    (u : ZMod d → ℂ_[p]) : MvPowerSeries (TVar D Po N N') ℂ_[p] :=
  ∑ s : ZMod d, algebraMap ℂ_[p] (MvPowerSeries (TVar D Po N N') ℂ_[p]) (u s) *
    ∑ a : Fin N, ∑ b : Fin N', sE D Po v s a b ^ p * sE D Po v (s + 1) a b

def InProd (D : D7) {N N' p d : ℕ} [Fact p.Prime] (Po : Pos D p d)
    (h : {v // v ∈ Po.V} → MvPowerSeries (TVar D Po N N') ℂ_[p])
    (F : MvPowerSeries (TVar D Po N N') ℂ_[p]) : Prop :=
  ∃ g : ({v // v ∈ Po.V} → ℕ) → MvPowerSeries (TVar D Po N N') ℂ_[p], (∀ i, IntegralMv (g i)) ∧
    ∀ α, MvPowerSeries.coeff α F =
      ∑ i ∈ Fintype.piFinset (fun _ : {v // v ∈ Po.V} => Finset.range ((α.sum fun _ k => k) + 1)),
        MvPowerSeries.coeff α
          (algebraMap ℂ_[p] (MvPowerSeries (TVar D Po N N') ℂ_[p]) (∏ v, ((p : ℂ_[p]) ^ i v)⁻¹) *
            (∏ v, h v ^ i v) * g i)

def str22 (D : D7) (T : Tor D) (e : FamE D) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]),
    5 ≤ p → jacobiSym (-(D.host.d : ℤ)) p = -1 → AllSplit D p →
    ∃ ep : ℂ_[p], InW ep ∧ ‖ep‖ = 1 ∧
    ∀ (d : ℕ) [NeZero d] (Po : Pos D p d) (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
      (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E))
      (P : {v // v ∈ Po.V} → Matrix (Fin N) (Fin N) D.host.E)
      (P' : {v // v ∈ Po.V} → Matrix (Fin N') (Fin N') D.host.E) (ϖ : ℂ_[p]),
      admitted D N N' L L' → (∀ v, LocBasisW D (posEmb D lam Po.φ v.1 (0 : ZMod d)) L (P v)) →
      (∀ v, LocBasisW D (posEmb D lam Po.φ v.1 (0 : ZMod d)) L' (P' v)) →
      ϖ ^ (p ^ 2 - 1) = (p : ℂ_[p]) →
      ∃ u : {v // v ∈ Po.V} → ZMod d → ℂ_[p], (∀ v s, IsIntP (u v s)) ∧
        ∀ F : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p], IsComb D T e lam L L' F →
        ∀ h' : {v // v ∈ Po.V} → MvPowerSeries (TVar D Po N N') ℂ_[p],
          (∀ v, ∃ G : MvPowerSeries (TVar D Po N N') ℂ_[p], IntegralMv G ∧ MvPowerSeries.constantCoeff G = 0 ∧
            h' v = hh D Po v (u v) + algebraMap ℂ_[p] _ (p : ℂ_[p]) * G) →
          InProd D Po h' (atLin (fun k j => ep * chg D lam Po P P' k j * ϖ)
            (fun j => MvPowerSeries.X j) F)

def adm1 (D : D7) : Prop :=
  (∀ 𝔭 : Ideal (𝓞 D.host.F), 𝔭.IsPrime → 𝔭 ≠ ⊥ → 𝔭.ramificationIdxIn (𝓞 D.host.E) = 1) ∧
  (∀ x : D.host.E, (∃ m : ℕ, 0 < m ∧ x ^ m = 1) → Algebra.norm D.host.K x = 1) ∧
  (∀ p : ℕ, p.Prime → p ∣ D.host.condN →
    ∀ 𝔭 : Ideal (𝓞 D.host.F), 𝔭.IsPrime → 𝔭.LiesOver (Ideal.span {(p : ℤ)}) →
      (Ideal.primesOver 𝔭 (𝓞 D.host.E)).ncard = 2) ∧
  (∀ p : ℕ, p.Prime → p ∣ D.host.QS * D.host.q →
    (Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 D.host.K)).ncard = 2) ∧
  (∀ 𝔭 : Ideal (𝓞 D.host.K), 𝔭.IsPrime → 𝔭 ≠ ⊥ → 1 < 𝔭.ramificationIdxIn (𝓞 D.host.E) →
    ((D.host.QS * D.host.q : ℕ) : 𝓞 D.host.K) ∈ 𝔭) ∧
  (∀ P : Ideal (𝓞 D.host.E), P.IsPrime → (D.host.d : 𝓞 D.host.E) ∈ P →
    ∀ σ : D.host.E ≃ₐ[ℚ] D.host.E,
      ((∀ x : 𝓞 D.host.E, ∃ y ∈ P, (y : D.host.E) = σ (x : D.host.E) - (x : D.host.E)) ↔
        (D.host.galE σ = 1 ∨
          D.host.galE σ = ((1, -1), 1))))

def AdmittedStatements (D : D7) : Prop := adm1 D

theorem isChi_chiRec (D : D7) (idl : D.Dt ⧸ D.UO → IdE D) (h : RelDetPinned D idl) :
    IsChi D (chiRec D idl) := by
  obtain ⟨hinj, hN, hmul, hz, -⟩ := h
  refine ⟨?_, ?_⟩
  · intro 𝔞 𝔟 ha hb
    obtain ⟨x, rfl⟩ := (hN 𝔞).1 ha
    obtain ⟨y, rfl⟩ := (hN 𝔟).1 hb
    rw [← hmul, chiRec_idl D idl hinj, chiRec_idl D idl hinj, chiRec_idl D idl hinj, map_mul]
    simp
  · intro z
    rw [← hz z, chiRec_idl D idl hinj]
    exact D.rest_detCharacter_on_unitary_eq z

def aux₃ (D : D7) (C : ℝ) : Prop :=
  ∀ cc : Ideal (𝓞 D.host.K), IsCurveIdeal D cc → ∀ δ : ℂ, IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
    per22 D (tor0 D cc δ) ∧ (∃ χ, IsChi D χ) ∧
    ∀ χ, IsChi D χ →
    ∃ e : FamE D, vec22 D (tor0 D cc δ) e ∧ th22 D (tor0 D cc δ) C e ∧ eq22 D (tor0 D cc δ) χ e ∧
      int22 D (tor0 D cc δ) e ∧ mom22 D cc δ e ∧ LargerSupportMomentCondition D cc δ e ∧ str22 D (tor0 D cc δ) e

def Stmt (D : D7) (C : ℝ) : Prop := AdmittedStatements D → aux₃ D C

def CurveIdealTorusProperties (D : D7) (C : ℝ) : Prop :=
  ∀ cc : Ideal (𝓞 D.host.K), IsCurveIdeal D cc → ∀ δ : ℂ, IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
    per22 D (tor0 D cc δ) ∧
    ∃ e : FamE D, vec22 D (tor0 D cc δ) e ∧ th22 D (tor0 D cc δ) C e ∧ RelativeDeterminantEquation D (tor0 D cc δ) e ∧
      int22 D (tor0 D cc δ) e ∧ mom22 D cc δ e ∧ LargerSupportMomentCondition D cc δ e ∧ str22 D (tor0 D cc δ) e

def AdmF {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop := ∀ x (i : Fm.Ix x), AdmittedStatements (Fm.D x i)

def ConclusionOnFamily {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (C : ℝ) : Prop :=
  ∀ x (i : Fm.Ix x), aux₃ (Fm.D x i) C

def StatementFamilyConstant {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (C : ℝ) : Prop :=
  AdmF Fm → ConclusionOnFamily Fm C

def KudlaFamilyStatement {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop :=
  AdmF Fm → ∃ C : ℝ, ConclusionOnFamily Fm C

end Formalism.MainNotions.TaylorLogMetric
