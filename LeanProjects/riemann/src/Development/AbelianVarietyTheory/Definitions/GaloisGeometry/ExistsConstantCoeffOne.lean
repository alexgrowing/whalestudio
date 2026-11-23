import Mathlib
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.StatementE
import Formalism.LocalToGlobal.KernelLattices.LateralTheory
import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.IsHypPair
import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.RenameBlockSingleVariableSeries
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.SingleLetterBiextensionRelation
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.EisensteinRecursion

noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (thetaS phFF NormRel)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog at1 lgF)

namespace GlobalTheory.KerStd

def CurveData (l : ℕ) [Fact l.Prime] (g2 g3 s2 ε : MaximalUnramifiedExtension l) (σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l) (F : MvPowerSeries (Fin 2) (MaximalUnramifiedExtension l)) : Prop :=
  5 ≤ l ∧ ‖g2‖ ≤ 1 ∧ ‖g3‖ ≤ 1 ∧ ‖ε‖ = 1 ∧ (∀ n, ‖PowerSeries.coeff n (thetaS l g2 g3 ε)‖ ≤ 1) ∧
    UnrOK (MaximalUnramifiedExtension l) l σ ∧ IsLawOfLog l F ∧
    ∀ α : MaximalUnramifiedExtension l, ‖α‖ = 1 → σ (σ α) = α → NormRel l σ (phFF l g2 g3 s2 ε) α

def HostLog (l : ℕ) [Fact l.Prime] (g2 g3 s2 ε : MaximalUnramifiedExtension l) {n : Type} [Fintype n] (Θ : MvPowerSeries n ℂ_[l]) : Prop :=
  Formalism.DworkPowerSeriesWeights.Integral
    (Formalism.DworkPowerSeriesWeights.mvExp (∑ i : n, at1 i (PowerSeries.map (MaximalUnramifiedExtension l).subtype (phFF l g2 g3 s2 ε)) : MvPowerSeries n ℂ_[l]) *
      (MvPowerSeries.subst (fun i : n => (at1 i (lgF ℂ_[l] l) : MvPowerSeries n ℂ_[l])) Θ : MvPowerSeries n ℂ_[l]))

abbrev HypPair {K : Type} [NormedField K] (σ : K →+* K) {E n : Type} [DecidableEq E] [Fintype n] (f f' : E → n → K) : Prop :=
  Formalism.L2.Th1.Top.IsHypPair σ f f'

def thOrth (D : D7) {N N' r : ℕ} {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (c : ℂ_[p])
    (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (F₀ : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p]) :
    MvPowerSeries (Fin r) ℂ_[p] :=
  MvPowerSeries.subst (fun k : D.what₂.Tau × Fin N' × Fin N =>
    ∑ i, MvPowerSeries.C (c * lamC lam (embT D k.1 (b i k.2.1 k.2.2))) * MvPowerSeries.X i) F₀

def HostAt {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Formalism.L2.Ker.Base D cc δ) (χ : IdE D → ℂ) (p : ℕ) [Fact p.Prime]
    (lam : Qbar →+* ℂ_[p]) : Prop :=
  ∃ (c : ℂ_[p]) (g2 g3 s2 ε : MaximalUnramifiedExtension p) (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p) (F : MvPowerSeries (Fin 2) (MaximalUnramifiedExtension p)),
    ‖c‖ = 1 ∧ CurveData p g2 g3 s2 ε σ F ∧
    ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)),
      admitted D N N' L L' → ∃ (r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E),
        LocBasis D p (YYl D L L') b ∧ TaylorLogMetric.Orthonormal D b ∧
        ∀ G, IsComb D B.tor (B.eNat χ) lam L L' G → HostLog p g2 g3 s2 ε (thOrth D lam c b G)

theorem CurveData.exists_of_cm (h2 : Formalism.L2.Th1.CM.CM2) (h3 : Formalism.L2.Th1.CM.CM3) (h4 : Formalism.L2.Th1.CM.CM4)
    (d : ℕ) (L : PeriodPair) (hsq : Squarefree d) (hd4 : d % 4 = 3)
    (hcm : Formalism.L2.Th1.CM.HasCMBy d L)
    (l : ℕ) [Fact l.Prime] (h5 : 5 ≤ l) (hd : ¬ l ∣ d) (hin : ¬ ∃ a : ZMod l, a ^ 2 = -((d : ℕ) : ZMod l)) :
    ∃ (g2 g3 s2 ε : MaximalUnramifiedExtension l) (σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l) (F : MvPowerSeries (Fin 2) (MaximalUnramifiedExtension l)),
      CurveData l g2 g3 s2 ε σ F ∧ ‖(g2 : ℂ_[l]) ^ 3 - 27 * (g3 : ℂ_[l]) ^ 2‖ = 1 := by
  obtain ⟨ι⟩ := Formalism.L2.Th1.F.iotaExists l
  obtain ⟨g2, g3, ε, hg, hε, hth⟩ := Formalism.L2.Th1.D.FAux.model l h2 h3 d L hsq hd4 hcm h5 hd hin ι
  obtain ⟨s2, -, -, hN⟩ := Formalism.L2.Th1.D.nrcmOfCM4 h4 d L hsq hd4 hcm l h5 hd hin ι g2 g3 ε hg hε hth
  obtain ⟨σ, hσ, ⟨F, hF⟩, -⟩ := Formalism.L2.Th1.D.fieldDataCM l h5
  exact ⟨g2, g3, s2, ε, σ, F, ⟨h5, hg.2.2.1, hg.2.2.2.1, hε, hth, hσ, hF, hN σ hσ⟩, hg.2.2.2.2.1⟩

theorem CurveData.exists_five [Fact (Nat.Prime 5)] (h2 : Formalism.L2.Th1.CM.CM2) (h3 : Formalism.L2.Th1.CM.CM3) (h4 : Formalism.L2.Th1.CM.CM4) :
    ∃ (g2 g3 s2 ε : MaximalUnramifiedExtension 5) (σ : MaximalUnramifiedExtension 5 →+* MaximalUnramifiedExtension 5) (F : MvPowerSeries (Fin 2) (MaximalUnramifiedExtension 5)),
      CurveData 5 g2 g3 s2 ε σ F ∧ ‖(g2 : ℂ_[5]) ^ 3 - 27 * (g3 : ℂ_[5]) ^ 2‖ = 1 := by
  have h0 : ∀ a : Fin 5, a * a + 2 ≠ 0 := by decide
  refine CurveData.exists_of_cm h2 h3 h4 7 _ (by norm_num : Nat.Prime 7).prime.squarefree (by norm_num)
    (Formalism.L2.Th1.F.cmPairHasCMBy 1 1 2 7 (by norm_num) (by norm_num) (by norm_num) (by decide)) 5 le_rfl (by decide) ?_
  rintro ⟨a, ha⟩
  have h5 : ((5 : ℕ) : ZMod 5) = 0 := ZMod.natCast_self 5
  have h1 : a * a + 2 = 0 := by
    push_cast at ha h5
    linear_combination ha - h5
  exact h0 a h1

theorem HypPair.exists_unramified (l : ℕ) [Fact l.Prime] (h5 : 5 ≤ l) (σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l) (hσ : UnrOK (MaximalUnramifiedExtension l) l σ)
    (E : Type) [Fintype E] [DecidableEq E] : ∃ f f' : E → (Bool × E) → MaximalUnramifiedExtension l, HypPair σ f f' := by
  obtain ⟨σ₀, -, -, hz⟩ := Formalism.L2.Th1.D.fieldDataCM l h5
  obtain ⟨ζ, -, -, hζ, -⟩ := hz 2 (by decide)
  exact Formalism.L2.Th1.Top.InhA.hyp_of_gram l σ hσ ⟨ζ, hζ⟩ E

theorem HypPair.exists_lift (l : ℕ) [Fact l.Prime] (h5 : 5 ≤ l) (E : Type) [Fintype E] [DecidableEq E] :
    ∃ σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l, UnrOK (MaximalUnramifiedExtension l) l σ ∧ ∃ f f' : E → (Bool × E) → MaximalUnramifiedExtension l, HypPair σ f f' := by
  obtain ⟨σ, hσ, -⟩ := Formalism.L2.Th1.D.fieldDataCM l h5
  exact ⟨σ, hσ, HypPair.exists_unramified l h5 σ hσ E⟩

theorem HypPair.symm {K : Type} [NormedField K] {σ : K →+* K} {E n : Type} [DecidableEq E] [Fintype n] {f f' : E → n → K}
    (h : HypPair σ f f') : HypPair σ f' f := by
  obtain ⟨a, b, c, d, e⟩ := h
  refine ⟨b, a, d, c, fun x y => ?_⟩
  have := congrArg σ (e y x)
  rw [map_sum] at this
  simp only [map_mul, (a _ _).2] at this
  rw [show (∑ i, σ (f' x i) * f y i) = ∑ i, f y i * σ (f' x i) from Finset.sum_congr rfl fun i _ => mul_comm _ _, this]
  by_cases hxy : x = y
  · subst hxy; simp
  · have h' : ¬ y = x := fun q => hxy q.symm
    simp [hxy, h']

example {K : Type} [NormedField K] (σ : K →+* K) (f f' : Unit → Unit → K) : ¬ HypPair σ f f' := by
  rintro ⟨-, -, c, -, e⟩
  have h1 := c () ()
  have h2 := e () ()
  simp only [Finset.univ_unique, Finset.sum_singleton, if_true, mul_eq_zero, map_eq_zero, or_self] at h1 h2
  rw [h1] at h2
  simp at h2

theorem HostLog.iff_phSum (l : ℕ) [Fact l.Prime] (g2 g3 s2 ε : MaximalUnramifiedExtension l) {n : Type} [Fintype n] (Θ : MvPowerSeries n ℂ_[l]) :
    HostLog l g2 g3 s2 ε Θ ↔ Formalism.DworkPowerSeriesWeights.Integral
      (Formalism.DworkPowerSeriesWeights.mvExp (Formalism.L2.Th1.E.phSum (Formalism.L2.Th1.Top.phL l g2 g3 s2 ε) : MvPowerSeries n ℂ_[l]) *
        (MvPowerSeries.subst (fun i : n => (at1 i (lgF ℂ_[l] l) : MvPowerSeries n ℂ_[l])) Θ : MvPowerSeries n ℂ_[l])) :=
  Iff.rfl

theorem HostLog.constantCoeff_subst {K σ τ : Type} [Field K] [Finite σ] {a : σ → MvPowerSeries τ K}
    (ha : ∀ s, MvPowerSeries.constantCoeff (a s) = 0) (f : MvPowerSeries σ K) :
    MvPowerSeries.constantCoeff (MvPowerSeries.subst a f : MvPowerSeries τ K) = MvPowerSeries.constantCoeff f := by
  have hs := MvPowerSeries.hasSubst_of_constantCoeff_zero ha
  have e : f = (f - MvPowerSeries.C (MvPowerSeries.constantCoeff f)) + MvPowerSeries.C (MvPowerSeries.constantCoeff f) := by ring
  conv_lhs => rw [e]
  rw [MvPowerSeries.subst_add hs, map_add, MvPowerSeries.constantCoeff_subst_eq_zero hs ha (by simp), zero_add,
    MvPowerSeries.subst_C]
  simp

theorem HostLog.constantCoeff_factor (l : ℕ) [Fact l.Prime] (g2 g3 s2 ε : MaximalUnramifiedExtension l) (n : Type) [Fintype n] :
    MvPowerSeries.constantCoeff
      (Formalism.DworkPowerSeriesWeights.mvExp (∑ i : n, at1 i (PowerSeries.map (MaximalUnramifiedExtension l).subtype (phFF l g2 g3 s2 ε)) : MvPowerSeries n ℂ_[l])) = 1 := by
  have hl : 2 ≤ l := (Fact.out : l.Prime).two_le
  have key : ∀ {a : MvPowerSeries n ℂ_[l]} (_ : MvPowerSeries.constantCoeff a = 0) (f : PowerSeries ℂ_[l]),
      MvPowerSeries.constantCoeff (PowerSeries.subst a f : MvPowerSeries n ℂ_[l]) = PowerSeries.constantCoeff f :=
    fun {a} ha f => HostLog.constantCoeff_subst (σ := Unit) (a := fun _ => a) (fun _ => ha) f
  rw [Formalism.DworkPowerSeriesWeights.mvExp, key]
  · simp
  · rw [map_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [at1, key (by simp), ← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, Formalism.L2.Th1.D.FAux.cc_phFF hl, map_zero]

theorem HostLog.norm_constantCoeff_le {l : ℕ} [Fact l.Prime] {g2 g3 s2 ε : MaximalUnramifiedExtension l} {n : Type} [Fintype n]
    {Θ : MvPowerSeries n ℂ_[l]} (h : HostLog l g2 g3 s2 ε Θ) : ‖MvPowerSeries.constantCoeff Θ‖ ≤ 1 := by
  have hp := Formalism.L2.Th1.D.BrC.logPair (K := ℂ_[l]) (Fact.out : l.Prime).two_le
  have h0 := h 0
  rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, map_mul, HostLog.constantCoeff_factor, one_mul,
    HostLog.constantCoeff_subst] at h0
  · exact h0
  · exact fun i => Formalism.L2.Th1.C.Pts.constantCoeff_subst_l hp (MvPowerSeries.constantCoeff_X i)

theorem HostLog.exists_constantCoeff_one (l : ℕ) [Fact l.Prime] (g2 g3 s2 ε : MaximalUnramifiedExtension l) (n : Type) [Fintype n] :
    ∃ Θ : MvPowerSeries n ℂ_[l], MvPowerSeries.constantCoeff Θ = 1 ∧ HostLog l g2 g3 s2 ε Θ := by
  classical
  have hp := Formalism.L2.Th1.D.BrC.logPair (K := ℂ_[l]) (Fact.out : l.Prime).two_le
  have hE1 := HostLog.constantCoeff_factor l g2 g3 s2 ε n
  set E : MvPowerSeries n ℂ_[l] :=
    Formalism.DworkPowerSeriesWeights.mvExp (∑ i : n, at1 i (PowerSeries.map (MaximalUnramifiedExtension l).subtype (phFF l g2 g3 s2 ε)) : MvPowerSeries n ℂ_[l]) with hE
  have ha : ∀ i : n, MvPowerSeries.constantCoeff (at1 i (Formalism.L2.Th1.D.expF ℂ_[l] l) : MvPowerSeries n ℂ_[l]) = 0 :=
    fun i => Formalism.L2.Th1.C.Pts.constantCoeff_subst_linv hp (MvPowerSeries.constantCoeff_X i)
  have hb : ∀ i : n, MvPowerSeries.constantCoeff (at1 i (lgF ℂ_[l] l) : MvPowerSeries n ℂ_[l]) = 0 :=
    fun i => Formalism.L2.Th1.C.Pts.constantCoeff_subst_l hp (MvPowerSeries.constantCoeff_X i)
  refine ⟨MvPowerSeries.subst (fun i : n => (at1 i (Formalism.L2.Th1.D.expF ℂ_[l] l) : MvPowerSeries n ℂ_[l])) E⁻¹, ?_, ?_⟩
  · rw [HostLog.constantCoeff_subst ha, MvPowerSeries.constantCoeff_inv, hE1, inv_one]
  · unfold HostLog
    rw [← hE, MvPowerSeries.subst_comp_subst_apply (MvPowerSeries.hasSubst_of_constantCoeff_zero ha)
      (MvPowerSeries.hasSubst_of_constantCoeff_zero hb)]
    have : (fun i : n => MvPowerSeries.subst (fun i : n => (at1 i (lgF ℂ_[l] l) : MvPowerSeries n ℂ_[l]))
        (at1 i (Formalism.L2.Th1.D.expF ℂ_[l] l) : MvPowerSeries n ℂ_[l])) = MvPowerSeries.X := by
      funext i
      conv_lhs => rw [at1]
      rw [Formalism.L2.Th1.C.Pts.substMv_subst (MvPowerSeries.constantCoeff_X i) hb,
        MvPowerSeries.subst_X (MvPowerSeries.hasSubst_of_constantCoeff_zero hb)]
      exact Formalism.L2.Th1.C.Pts.subst_linv_l hp (MvPowerSeries.constantCoeff_X i)
    rw [this, MvPowerSeries.subst_self, id, MvPowerSeries.mul_inv_cancel _ (by rw [hE1]; exact one_ne_zero)]
    intro m
    rw [MvPowerSeries.coeff_one]
    split_ifs <;> simp

theorem thOrth.hasSubst (D : D7) {N N' r : ℕ} {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (c : ℂ_[p])
    (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) :
    MvPowerSeries.HasSubst (fun k : D.what₂.Tau × Fin N' × Fin N =>
      (∑ i, MvPowerSeries.C (c * lamC lam (embT D k.1 (b i k.2.1 k.2.2))) * MvPowerSeries.X i : MvPowerSeries (Fin r) ℂ_[p])) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero fun k => by simp

theorem thOrth.apply_X (D : D7) {N N' r : ℕ} {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (c : ℂ_[p])
    (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (k : D.what₂.Tau × Fin N' × Fin N) :
    thOrth D lam c b (MvPowerSeries.X k) =
      ∑ i, MvPowerSeries.C (c * lamC lam (embT D k.1 (b i k.2.1 k.2.2))) * MvPowerSeries.X i :=
  MvPowerSeries.subst_X (thOrth.hasSubst D lam c b) k

theorem thOrth.constantCoeff_eq (D : D7) {N N' r : ℕ} {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (c : ℂ_[p])
    (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (G : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p]) :
    MvPowerSeries.constantCoeff (thOrth D lam c b G) = MvPowerSeries.constantCoeff G :=
  HostLog.constantCoeff_subst (fun k => by simp) G

end GlobalTheory.KerStd
