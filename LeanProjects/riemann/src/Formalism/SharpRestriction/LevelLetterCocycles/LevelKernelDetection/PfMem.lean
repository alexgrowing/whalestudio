import Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.LevBMemFil
import Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.EvaluationExpansionAtRoot
import Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.XPowDvdOfComponents
import Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.CombineProd
import Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.PowerSeriesCancelBounded

noncomputable section

namespace Formalism.MainNotions.N.Ln03.Pf

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.MainNotions.WachCoordinates Formalism.MainNotions.WachCoordinates.Br Formalism.ExponentWindows Formalism.ExponentWindows.G Formalism.MainNotions.N.Ln03.K8

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL : Type} [Field LL] [Algebra Qp LL]
    {O : Type} [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n] {W : LocWach PD LL O v n}
    {Lb : LevB W} {hR : Ring9 W} {uZ : ℤ_[PD.p]ˣ} {ιZ : ℤ_[PD.p] →+* O}
    {T : LocLat G Qp LL O} {C : Coord W (baseIdOf hR) T} {c : ZMod n}

theorem mem_holds [IsDomain O] [IsDiscreteValuationRing O] [IsFractionRing O LL] (hP4 : LevelMapHodgeFiltration W)
    (hSat : Sat W) (hcrys : IsCrys PD T.ρ)
    (hLb : ∀ (i : ZMod n) (ζ : LL) (x : ↥(W.N T)) (k : ℤ),
      W.levN T i ζ x k = ιV PD (LL := LL) (V := T.V) (Lb.levB T i ζ x k))
    (hmod : Formalism.MainNotions.DeltaInvariantLattices.wachModuleOverLetters W T W.π₀) (hP3 : Formalism.MainNotions.DeltaInvariantLattices.p3 W T) (hfree : (latOf C).Free c)
    (hζ : ∃ ζ : LL, IsPrimitiveRoot ζ (PD.p ^ n))
    {ell : ℕ} (hell : ell ≤ n) {H : ℕ → ℕ} {κ : PowerSeries O} {r : ℕ} {lam : Fin r → Dc W T c} (m : ℕ)
    (hκ : κ = Formalism.ExponentWindows.abelian₂ (baseIdOf hR).Bs.p H ell * ∏ s ∈ Finset.range ell, (baseIdOf hR).Bs.p s ^ m)
    (hk1b : ∀ s < ell, ∃ ε : (PowerSeries (KsW W s))ˣ,
      rhoL hR c s ((baseIdOf hR).Bs.p s) = (ε : PowerSeries (KsW W s)) * PowerSeries.X)
    (hunits : ∀ s < ell, IsUnit (rhoL hR c s PowerSeries.X) ∧
      ∀ s' < ell, s' ≠ s → IsUnit (rhoL hR c s ((baseIdOf hR).Bs.p s')))
    (hfilt : ∀ s < ell, IsFilt (FilD W T c s)) (ϖ : O)
    (hcompl : ∀ s < ell, ∀ (k : ℕ) (a : PowerSeries O), PowerSeries.X ^ k ∣ rhoL hR c s a →
      ∃ (N : ℕ) (z : PowerSeries O), PowerSeries.C (ϖ ^ N) * a = (baseIdOf hR).Bs.p s ^ k * z)
    (hϖ : ∃ (N : ℕ) (u : O), ((PD.p : ℕ) : O) ^ N = ϖ * u)
    (Hy : LvHyp Lb hR uZ ιZ C c ell (Formalism.ExponentWindows.abelian₂ (baseIdOf hR).Bs.p H ell) κ lam)
    (f' : PowerSeries O) (kind : ℕ → Kind) (b : ℕ → ℕ) (η : ℕ) :
    (lvData Hy f' kind b η).Mem := by
  intro x
  have hκE : κ = ∏ s ∈ Finset.range ell, (baseIdOf hR).Bs.p s ^ (H s + m) := by
    rw [hκ, Formalism.ExponentWindows.abelian₂, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun s _ => (pow_add _ _ _).symm
  have hloc : ∀ s (hs : s < ell), (lvData Hy f' kind b η).loc s x ∈ (lvData Hy f' kind b η).Nl s ↔
      Ring.inverse (HahnSeries.ofPowerSeries ℤ (KsW W s) (rhoL hR c s κ)) •
        expN Lb s T c ⟨C.t c (κ • (x : C.V)), Hy.kap x x.2⟩ ∈ Xi (KsW W s) (fun i => FilD W T c s (-i)) := by
    intro s hs
    change prL s (locM Lb C Hy.delta ell _ κ Hy.kap Hy.expSemi Hy.locInv x) ∈ Xi _ _ ↔ _
    rw [prL_of_lt s hs]
    rfl
  constructor
  · intro hx s hs
    rw [hloc s hs]
    have hm : (baseIdOf hR).d κ • ((⟨C.t c x, hx⟩ : ↥(W.N T)) : W.DD T) ∈ W.N T := by
      have h0 := Hy.kap x x.2
      change C.t c (κ • (x : C.V)) ∈ W.N T at h0
      rwa [C.t_smul] at h0
    have e1 : (⟨C.t c (κ • (x : C.V)), Hy.kap x x.2⟩ : ↥(W.N T)) = ⟨(baseIdOf hR).d κ • C.t c x, hm⟩ :=
      Subtype.ext (C.t_smul c κ x)
    rw [e1, Hy.expSemi s κ ⟨C.t c x, hx⟩ hm, smul_smul]
    by_cases hu : IsUnit (HahnSeries.ofPowerSeries ℤ (KsW W s) (rhoL hR c s κ))
    · rw [Ring.inverse_mul_cancel _ hu, one_smul]
      exact expN_mem_xi hP4 hcrys hLb s _
    · rw [Ring.inverse_non_unit _ hu, zero_mul, zero_smul]
      exact zero_mem _
  · intro h
    have hy : κ • (x : C.V) ∈ (latOf C).N c := Hy.kap x x.2
    have hdet : ∀ s < ell, ∃ y' ∈ (latOf C).N c,
        κ • (x : C.V) = (baseIdOf hR).Bs.p s ^ (H s + m) • y' := by
      intro s hs
      have h1 : Ring.inverse (HahnSeries.ofPowerSeries ℤ (KsW W s)
          (rhoL hR c s (∏ s' ∈ Finset.range ell, (baseIdOf hR).Bs.p s' ^ (H s' + m)))) •
          expN Lb s T c ⟨C.t c (κ • (x : C.V)), hy⟩ ∈ Xi (KsW W s) (fun i => FilD W T c s (-i)) := by
        rw [← hκE]
        exact (hloc s hs).1 (h s hs)
      exact detect hP4 hSat hcrys hLb hmod hP3 hfree ϖ ell hcompl hϖ s hs (hfilt s hs) (H s + m) _ hy
        ((levelCond_iff ell hk1b hunits (fun s' => H s' + m) s hs _ hy Hy.filAnti).1 h1)
    obtain ⟨y', hy', hyy⟩ := combine hSat hcrys ell (fun s' => H s' + m) _ hy hdet
    have hp0 : ∀ s < ell, (baseIdOf hR).Bs.p s ≠ 0 := by
      intro s hs h0
      obtain ⟨ζ, hζ⟩ := hζ
      have hdvd : PD.p ^ (s + 1) ∣ PD.p ^ n := pow_dvd_pow _ (by omega)
      have hprim : IsPrimitiveRoot (ζ ^ (PD.p ^ n / PD.p ^ (s + 1))) (PD.p ^ (s + 1)) := by
        have := hζ.pow_of_dvd (Nat.div_pos (Nat.le_of_dvd (pow_pos PD.hp.pos _) hdvd)
          (pow_pos PD.hp.pos _)).ne' (Nat.div_dvd_of_dvd hdvd)
        rwa [Nat.div_div_self hdvd (pow_pos PD.hp.pos _).ne'] at this
      have : Nonempty (Rs LL PD.p s) :=
        ⟨⟨_, (mem_primitiveRoots (pow_pos PD.hp.pos _)).2 hprim⟩⟩
      obtain ⟨ε, hε⟩ := hk1b s hs
      rw [h0, map_zero] at hε
      exact PowerSeries.X_ne_zero ((Units.mul_right_eq_zero ε).1 hε.symm)
    have hκ0 : κ ≠ 0 := by
      rw [hκE]
      exact Finset.prod_ne_zero_iff.2 fun s hs => pow_ne_zero _ (hp0 s (Finset.mem_range.1 hs))
    have hxy : (x : C.V) = y' := by
      apply smul_cancel κ hκ0
      rw [hyy, ← hκE]
    rw [hxy]
    exact hy'

end Formalism.MainNotions.N.Ln03.Pf

end
