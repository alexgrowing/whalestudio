import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.FirstChernCompatibleL
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.BocksteinBaseChangeP
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.CrystallineDeRhamFirstChernExists
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.Pull
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.IsProperOfProj
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.IsFirstChernDeRhamUnique
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.RSubOneMem
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LogarithmicDerivatives.CrystallineFirstChernExistsUnique

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Limits GlobalTheory.LogCris GroundTheory.PAdicHodge

namespace CrystallineSemistableComparison.Pb

set_option maxHeartbeats 1000000

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

theorem sum_coord {K B V : Type _} [Field K] [CommRing B] [AddCommGroup V] [Module K V] {V' : Type _} [AddCommGroup V'] [Module K V']
    {V'' : Type _} [AddCommGroup V''] [Module K V''] (o : K →+* B) {m m' : ℕ} (b : Module.Basis (Fin m) K V) (b' : Module.Basis (Fin m') K V')
    (μ : V →ₗ[K] V' →ₗ[K] V'') (φ : Module.Dual K V'') (x : V) (y : V') :
    ∑ s, ∑ s', o (b.coord s x) * o (b'.coord s' y) * o (φ (μ (b s) (b' s'))) = o (φ (μ x y)) := by
  conv_rhs => rw [← b.sum_repr x, ← b'.sum_repr y]
  simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, smul_eq_mul, map_mul, Module.Basis.coord_apply,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun s' _ => by ring

theorem kap_pow (L : KapL (l := l) (K := K) Amp) {M : Model l K} (a : (dat Amp).Ch M) (hM : M.Sm) (x : ((dat Amp).H a).N 2)
    (c : HdR M.q 2) (hx : ∀ φ, L.κ a 2 x φ = (per l K).o (φ c)) :
    ∀ (k : ℕ) (z : ((dat Amp).H a).N (2 * k)), IsPow (N := ((dat Amp).H a).N) ((dat Amp).H a).one ((dat Amp).H a).cup x k z →
      ∀ φ, L.κ a (2 * k) z φ = (per l K).o (φ (powK M.q c k))
  | 0, z, hz, φ => L.one a hM z hz φ
  | k + 1, z, ⟨y, hy, hz⟩, φ => by
    have := (m_fin M hM (2 * k)).1
    have := (m_fin M hM 2).1
    have h := L.cup a hM y x z hz (Module.finBasis _ _) (Module.finBasis _ _) φ
    refine h.trans ?_
    simp only [kap_pow L a hM x c hx k y hy, hx, ← cupR_eq]
    exact (sum_coord _ _ _ (cupR M (2 * k) 2) φ _ _).trans (congrArg (fun t => (per l K).o (φ t)) (cupR_eq M _ _ _ _))

theorem pow_ex {M : Model l K} (a : (dat Amp).Ch M) (x : ((dat Amp).H a).N 2) :
    ∀ k : ℕ, ∃ z : ((dat Amp).H a).N (2 * k), IsPow (N := ((dat Amp).H a).N) ((dat Amp).H a).one ((dat Amp).H a).cup x k z
  | 0 => ⟨(⟨fun n => CH.oneH _, fun n => (B.compatH l).one _ _ false n.le_succ⟩ : (M.HS false 0).lim), fun _ => rfl⟩
  | k + 1 => by
    obtain ⟨y, hy⟩ := pow_ex a x k
    refine ⟨(⟨fun n => (CH.mulP (B.OcA (B.schFn M.p) (okToOC l K) false n)).cup rfl ((show (M.HS false (2 * k)).lim from y).1 n)
      ((show (M.HS false 2).lim from x).1 n), fun n => ?_⟩ : (M.HS false (2 * k + 2)).lim), y, hy, fun _ => rfl⟩
    refine ((B.compatH l).cup _ _ false n.le_succ rfl _ _).trans ?_
    exact congrArg₂ _ ((show (M.HS false (2 * k)).lim from y).2 n) ((show (M.HS false 2).lim from x).2 n)

theorem pmap [FiniteDimensional ℚ_[l] K] : Nonempty (PMap Model.Sm (dat (l := l) (K := K) Amp)) := by
  obtain ⟨L, hL⟩ := crystalline_deRham_firstChern_exists (l := l) (K := K)
  refine ⟨⟨L.κ, cupR, m_fin, m_top, fun M _ => cupR_fil M, L.lin, L.lin', L.act, L.nat, L.fil, ?_, ?_⟩⟩
  · intro M a hM i j x y z h m m' b b' φ
    simp only [cupR_eq]
    exact L.cup a hM x y z h b b' φ
  · intro M a hM d hd
    have := hd.1
    have := hd.2
    have hK : IsTautologicalLine M.q (lineK a.1) := isTwistingSheaf_pullback (OK l K).subtype M.p a.1 a.2
    obtain ⟨N, i, -, -, hi⟩ := a.2
    obtain ⟨x, hx⟩ := firstChern_acris_family_exists M a.1 (sSup_𝒱D a.1 N i hi)
    obtain ⟨c, hc⟩ := isFirstChernDeRham_exists M.q d _ hK
    obtain ⟨z, hz⟩ := pow_ex a x d
    obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_eq_one K (powK_ne_zero M.q d _ hK c hc)
    refine ⟨x, z, φ, hx, hz, ?_⟩
    rw [kap_pow L a hM x c (hL a hM x c hx hc) d z hz φ, hφ, map_one]
    exact ⟨one_mem _, 1, one_mem _, mul_one 1⟩

theorem pSeam : BocksteinBaseChangeP := fun l _ K _ =>
  ⟨Amp, fun _ _ h => isO1_etale h, fun M hM => isO1_exists M.p hM.1.1, pmap, fun r => fmap r Amp⟩

end CrystallineSemistableComparison.Pb
