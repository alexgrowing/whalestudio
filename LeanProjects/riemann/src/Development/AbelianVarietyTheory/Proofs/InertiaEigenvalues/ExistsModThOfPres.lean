import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.JSmul
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsQuotOfAdmissible
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachDeltaInvariantsReductionIsLatticeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PhiGammaReductionBaseLatticeBoundsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SenMultisetBaseLatticeEqJumpsModStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EPolyBase
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RankOneReductionFrobeniusPullbackEqShiftStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ReductionSum

noncomputable section

open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps GlobalTheory.Present Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open Formalism.MainNotions.N (twistRep coefRep)
open Formalism.GaloisCohomology (scalRep)
open scoped LaurentSeries PowerSeries Pointwise

namespace GlobalTheory.BasePairs

def RedN {l : ℕ} [Fact l.Prime] {P : LocPrime l} {H : LocHW l P} {S : TopSit P} {k : Type} [Field k]
    [Algebra S.O k] {R : RingPG k l} {ι : k⸨X⸩ →ₐ[k] k⸨X⸩} {F : DFun R S.n S.G}
    {τ : ZMod S.n → ZMod (Module.finrank ℚ_[l] ↥(K0 S.K))} {γ : (S.W H).Gam} (p : Pres (S.W H) F ι τ γ)
    (T : LocLat S.G ℚ_[l] ↥S.LL.1 S.O) (A : Ob k S.G) (q : ↥T.L.T →ₗ[S.O] (Fin A.m → k)) (N : Lats k S.n A.m) :
    Prop :=
  ∀ i y, y ∈ N i ↔ ∃ x : ↥(DΔ (S.W H) T), (x : (S.W H).DD T) ∈ (S.W H).N T ∧ p.j T A q i x = y

theorem exists_modTh_of_pres {l : ℕ} [Fact l.Prime] {P : LocPrime l} {H : LocHW l P} {S : TopSit P} {k : Type}
    [Field k] [Algebra S.O k] [CharP k l] {R : RingPG k l} {ι : k⸨X⸩ →ₐ[k] k⸨X⸩} {F : DFun R S.n S.G}
    {τ : ZMod S.n → ZMod (Module.finrank ℚ_[l] ↥(K0 S.K))} {γ : (S.W H).Gam} (p : Pres (S.W H) F ι τ γ)
    (hC : S.CrysCalc) (hk : S.IsRes k) (hι : GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.IsCyclotomic R ι)
    (hτ : ∀ i, (S.W H).emb (τ i) = S.emb i) (hγ : ((S.W H).χΓ γ : S.O) = 1 + (l : S.O))
    (hQ : GlobalTheory.WachUse.QN (S.W H)) :
    ∃ M : ModTh F S.D, (∀ σ, (M.ω σ : k) = algebraMap S.O k (S.Γ.ε σ)) ∧
      (∃ q : ↥S.Γ.T₀.L.T →ₗ[S.O] (Fin M.T.m → k), Function.Surjective q ∧
        KerIs S.Γ.lam q ∧ ∀ σ x, q (twistRep S.Γ.W₀ S.Γ.χ₁⁻¹ σ x) = M.T.ρ σ (q x)) ∧
      ∀ (A : Ob k S.G) (N : Type) [AddCommGroup N] [Module S.O N] (π : Representation S.O S.G N)
        (e : N ≃ₗ[S.O] (Fin A.m → k)), S.admitted π → (∀ σ x, e (twistRep π S.Γ.χ₁⁻¹ σ x) = A.ρ σ (e x)) →
        ∃ L, M.Model A L := by
  have hG : IsTopGal (P.PD S.K) S.emb S.D S.Γ := S.hyp.2.1
  have : FiniteDimensional ℚ_[l] ↥S.LL.1 := S.LL.2
  have : IsDiscreteValuationRing S.O := by
    unfold TopSit.O Formalism.BasicNotions.Loc.OL
    exact GlobalTheory.isDiscreteValuationRing_integralClosure_padicInt l ↥S.LL.1
  have : IsFractionRing S.O ↥S.LL.1 := by
    unfold TopSit.O Formalism.BasicNotions.Loc.OL
    exact GlobalTheory.isFractionRing_integralClosure_padicInt l ↥S.LL.1
  have hθ : IsCrysChar (P.PD S.K) S.emb S.Γ.χ₁⁻¹ (fun i => -S.D.w i) :=
    (hC.2.1 S.Γ.T₀ S.D.U S.Γ.χ₁ S.D.w hG.2.1 hG.2.2.1).2
  have hlam : Irreducible S.Γ.lam := S.hyp.1.2.2.2.2.2
  have hpoly : ∀ (T : LocLat S.G ℚ_[l] ↥S.LL.1 S.O) (A : Ob k S.G) q (U : ZMod S.n → Multiset ℤ),
      Onto T A q → KerIs S.Γ.lam q → CrysWith (P.PD S.K) S.emb T.ρ U →
      ∀ N : Lats k S.n A.m, RedN p T A q N → ∀ (i : ZMod S.n) (s : ℕ),
      (∀ u ∈ U i, ∀ a : ℕ, a < s → (l : ℤ) ∣ (a : ℤ) - u → (a : ℤ) = u) → EPoly ((F.D A).γ i) (N i) s := by
    intro T A q U hq hK hc N hN i s hs
    exact BaseLatticeE.ePoly_base H S k hk ι F τ γ p hι hτ hγ hQ T A q U hq hK hc N hN i s hs
  exact exists_real hθ hk hlam hC.1 hC.2.1 p.obj
    (fun T A q U hq hK hc => GlobalTheory.T.wachDeltaInvariants_reduction_isLattice H S k hk ι F τ γ p hι hτ hγ hQ T A q U hq hK hc)
    (fun T A q U hq hK hc N hN w w' hw =>
      GlobalTheory.T.phiGamma_reduction_base_lattice_bounds H S k hk ι F τ γ p hι hτ hγ hQ T A q U hq hK hc N hN w w' hw)
    (fun T A q U hq hK hc N hN i x =>
      GlobalTheory.T.senMultiset_base_lattice_eq_jumps_mod H S k hk ι F τ γ p hι hτ hγ hQ T A q U hq hK hc N hN i x)
    hpoly
    (fun T A q U hq hK hc N hN a hm ha i =>
      GlobalTheory.T.rankOne_reduction_frobeniusPullback_eq_shift H S k hk ι F τ γ p hι hτ hγ hQ T A q U hq hK hc N hN a hm ha i)
    (fun T A q U hq hK hc T' A' q' U' hq' hK' hc' Z C r V hr hKr hcr f g a b hb hs ha hb' hfa hgb
        N N' L hN hN' hL i =>
      GlobalTheory.Present.SumRed.reduction_sum H S k hk ι F τ γ p hι hτ hγ hQ T A q U hq hK hc T' A' q' U' hq' hK'
        hc' Z C r V hr hKr hcr f g a b hb hs ha hb' hfa hgb N N' L hN hN' hL i)
    hG hC.2.2.1 (fun ω hω e h0 h1 => omega_pow_ne_one S k ω hω e h0 h1)

theorem real_of_presented : ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} (AI : LocAinf l P) (H : LocHW l P)
    (E : LocFon l P AI H) (S : TopSit P), S.RealD H → GlobalTheory.WachUse.QN (S.W H) → S.CrysCalc → S.Real := by
  intro l _ P AI H _ S hR hQ hC
  unfold TopSit.Real
  intro k _ _ _ hk
  have h1 := @hR k _ _ _ hk
  obtain ⟨R, ι, hι, F, τ, γ, hτ, hγ, hp⟩ := h1
  have h2 := exists_modTh_of_pres (H := H) (S := S) (k := k) (R := R) (ι := ι) (F := F)
    (τ := τ) (γ := γ) hp.some hC hk hι hτ hγ hQ
  exact ⟨R, ι, hι, F, h2⟩

end GlobalTheory.BasePairs
