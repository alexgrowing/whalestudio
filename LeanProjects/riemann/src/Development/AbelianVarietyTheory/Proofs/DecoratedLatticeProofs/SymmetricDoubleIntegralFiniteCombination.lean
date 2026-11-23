import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchwartzBruhatSelfAverageHeisenberg
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsWeilSourceActionAndSmooth
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.QuotientIntegralLinear
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ProperTriple
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchwartzFourierTransformPiSurjectiveSchwartzBruh

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal opEFJ IsQuotIntFJ)

noncomputable section
namespace GlobalTheory.PosOne.SymComb
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasMat
open GlobalTheory.RootEx.Unfolding (opL orbit_locallyConstant)

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k]

theorem isQuotIntFJ_linear {n : Type} [Fintype n] [DecidableEq n] {c ρ : ℕ} (hp : 1 ≤ ρ) (hpc : ρ < c)
    (ν : Measure k) [ν.IsAddHaarMeasure] (μX : Measure (GL n k)) [μX.IsHaarMeasure]
    (μG : Measure (GL (n ⊕ Fin c) k)) [μG.IsHaarMeasure] {f f' : GL (n ⊕ Fin c) k → ℂ} (a : ℂ) {z z' : ℂ} :
    IsQuotIntFJ ν μX μG ρ f z → IsQuotIntFJ ν μX μG ρ f' z' →
      IsQuotIntFJ ν μX μG ρ (fun h => a * f h + f' h) (a * z + z') := by
  classical
  rintro ⟨F, hF, h1, h2⟩ ⟨F', hF', h1', h2'⟩
  haveI := GlobalTheory.SplitWeil.secondCountable k
  haveI := GlobalTheory.SplitWeil.t2Space k
  obtain ⟨bX, lX, sX, -⟩ := GlobalTheory.SplitWeil.volGL_haar k n ν
  obtain ⟨bG, lG, sG, -⟩ := GlobalTheory.SplitWeil.volGL_haar k (n ⊕ Fin c) ν
  haveI := QuotLinear.finiteOnCompacts_volN (n := n) (c := c) (p := ρ + 1) ν
  haveI : LocallyCompactSpace (N k n c (ρ + 1)) :=
    (QuotLinear.isClosed_N (k := k) (n := n) (c := c) (p := ρ + 1)).isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology (N k n c (ρ + 1)) := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : IsLocallyFiniteMeasure (volN ν n c (ρ + 1)) := isLocallyFiniteMeasure_of_isFiniteMeasureOnCompacts
  haveI : SigmaFinite (volN ν n c (ρ + 1)) := sigmaFinite_of_locallyFinite
  let m : Measure (n → k) := Measure.pi fun _ => ν
  let ι : GL n k × N k n c (ρ + 1) × (n → k) → GL (n ⊕ Fin c) k := fun z =>
    embX c z.1 * (z.2.1 : GL (n ⊕ Fin c) k) * colE c (ρ + 1) z.2.2
  let M : Measure (GL n k × N k n c (ρ + 1) × (n → k)) := μX.prod ((volN ν n c (ρ + 1)).prod m)
  have hm : Continuous ι :=
    ((QuotLinear.continuous_embX.comp continuous_fst).mul (continuous_subtype_val.comp continuous_snd.fst)).mul
      (ExchangeSupport.continuous_colE.comp continuous_snd.snd)
  have hint : ∀ φ ∈ SB (GL (n ⊕ Fin c) k), ∀ h, Integrable (fun z => φ (ι z * h)) M := by
    intro φ hφ h
    obtain ⟨D, hD, hD'⟩ := GlobalTheory.RootEx.ProperTriple.proper_triple k n c ρ hp hpc _
      (hφ.2.isCompact.image (continuous_mul_right h⁻¹))
    refine (hφ.1.continuous.comp (hm.mul continuous_const)).integrable_of_hasCompactSupport ?_
    refine HasCompactSupport.intro hD fun z hz => ?_
    by_contra h0
    exact hz (hD' z ⟨_, subset_tsupport _ h0, by simp [ι]⟩)
  have hprod : ∀ φ ∈ SB (GL (n ⊕ Fin c) k), ∀ h, (∫ g, (∫ u : N k n c (ρ + 1), (∫ β : n → k,
      φ (embX c g * (u : GL (n ⊕ Fin c) k) * colE c (ρ + 1) β * h) ∂m) ∂(volN ν n c (ρ + 1))) ∂μX) =
      ∫ z, φ (ι z * h) ∂M := by
    intro φ hφ h
    rw [integral_prod _ (hint φ hφ h)]
    exact integral_congr_ae ((hint φ hφ h).prod_right_ae.mono fun x hx => (integral_prod _ hx).symm)
  have hs : a • F + F' ∈ SB (GL (n ⊕ Fin c) k) := add_mem (Submodule.smul_mem _ a hF) hF'
  refine ⟨a • F + F', hs, fun h => ?_, ?_⟩
  · beta_reduce
    rw [hprod _ hs, h1, h1', hprod _ hF, hprod _ hF', ← integral_const_mul,
      ← integral_add ((hint _ hF h).const_mul a) (hint _ hF' h)]
    rfl
  · have i : Integrable F μG := hF.1.continuous.integrable_of_hasCompactSupport hF.2
    have j : Integrable F' μG := hF'.1.continuous.integrable_of_hasCompactSupport hF'.2
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [integral_add (i.const_mul a) j, integral_const_mul, h2, h2']

theorem rel_sum {G ι : Type} (Q : (G → ℂ) → ℂ → Prop) (h0 : Q (fun _ => 0) 0)
    (hl : ∀ (a : ℂ) f f' z z', Q f z → Q f' z' → Q (fun h => a * f h + f' h) (a * z + z'))
    (s : Finset ι) (a : ι → ℂ) (f : ι → G → ℂ) (z : ι → ℂ) (h : ∀ i ∈ s, Q (f i) (z i)) :
    Q (fun g => ∑ i ∈ s, a i * f i g) (∑ i ∈ s, a i * z i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using h0
  | insert j s hj ih =>
    simp only [Finset.sum_insert hj]
    exact hl _ _ _ _ _ (h j (Finset.mem_insert_self _ _)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem tensorVal_unique {n₀ n₁ n₂ : Type} [Fintype n₀] [DecidableEq n₀] [Fintype n₁] [DecidableEq n₁] [Fintype n₂]
    [DecidableEq n₂] {c ρ : ℕ} (h1 : 1 ≤ ρ) (h2 : ρ ≤ c) {ψ : AddChar k Circle} (hψ : Continuous ψ) (hψ1 : ψ ≠ 1)
    {ν : Measure k} (hν : IsSelfDual ψ ν) {A : Type} [AddCommGroup A] [Module ℂ A]
    (T : SB (Matrix n₁ n₀ k) →ₗ[ℂ] SB (Matrix n₂ n₁ k) →ₗ[ℂ] A →ₗ[ℂ] ℂ) (F : A)
    (Φ : SB (Matrix (n₂ ⊕ Fin c) (n₁ ⊕ Fin (c + 1)) k)) (Θ : Matrix n₁ n₀ k → (n₁ → k) → ℂ) {z z' : ℂ}
    (hz : HasTensorVal (fun Ψ Φ₀ => app (T Ψ) (opEFJ ψ ν ρ Φ₀.1 Φ.1) F) Θ z)
    (hz' : HasTensorVal (fun Ψ Φ₀ => app (T Ψ) (opEFJ ψ ν ρ Φ₀.1 Φ.1) F) Θ z') : z = z' := by
  haveI := hν.1
  haveI := GlobalTheory.SplitWeil.secondCountable k
  haveI := GlobalTheory.SplitWeil.t2Space k
  have hk : IsOpen (((1 : kˣ →* ℂˣ).ker : Subgroup kˣ) : Set kˣ) := by simp
  obtain ⟨⟨r, hr⟩, hsm⟩ := GlobalTheory.PosOne.isSrc_exists_isSmoothRep k (n₁ ⊕ Fin (c + 1)) (n₂ ⊕ Fin c) 1 hk
  have hav := (GlobalTheory.PosOne.avg_self_and_props k n₂ n₁ c ρ h1 h2 ψ hψ hψ1 ν hν 1 hk Φ).2
  let C : (n₁ → k) → SB (Matrix n₁ n₀ k) →ₗ[ℂ] ℂ := fun u =>
    (T.flip (opL hψ ν ρ (r (rowE (c + 1) ρ u) Φ))).flip F
  have hC : IsLocallyConstant C :=
    ((orbit_locallyConstant (hsm r hr) Φ).comp_continuous ExchangeSupport.continuous_rowE).comp
      fun v => (T.flip (opL hψ ν ρ v)).flip F
  have key : ∀ Ψ (Φ₀ : SB (n₁ → k)), app (T Ψ) (opEFJ ψ ν ρ Φ₀.1 Φ.1) F =
      ∫ u, GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.hat ψ ν Φ₀.1 u * C u Ψ ∂(Measure.pi fun _ => ν) := by
    intro Ψ Φ₀
    obtain ⟨hmem, hE, hL⟩ := hav Φ₀
    have e := hE 1
    rw [om_one, om_one] at e
    have l := hL r hr (((T Ψ).flip F).comp (opL hψ ν ρ))
    rw [GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.app_coe _ ⟨_, hmem⟩] at l
    rw [← e]
    exact (congrArg (fun t : A →ₗ[ℂ] ℂ => t F) (GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.app_coe (T Ψ) (opL hψ ν ρ ⟨_, hmem⟩))).trans l
  have hh := (GlobalTheory.T.schwartzFourierTransformPi_surjective_schwartzBruhat k n₁ ψ hψ hψ1 ν hν).1
  have int1 : ∀ Ψ (Φ₀ : SB (n₁ → k)),
      Integrable (fun u => GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.hat ψ ν Φ₀.1 u * C u Ψ) (Measure.pi fun _ => ν) := fun Ψ Φ₀ =>
    FourierJacobi.sb_int ⟨(hh Φ₀).1.mul (hC.comp fun l => l Ψ), (hh Φ₀).2.mul_right⟩
  have int2 : ∀ (Φ₀ : SB (n₁ → k)) (u : n₁ → k),
      Integrable (fun β => Φ₀.1 β * (ψ (u ⬝ᵥ β) : ℂ)) (Measure.pi fun _ => ν) := fun Φ₀ u =>
    (Φ₀.2.1.continuous.mul ((continuous_induced_dom.comp hψ).comp
      (continuous_const.dotProduct continuous_id))).integrable_of_hasCompactSupport Φ₀.2.2.mul_right
  have val : ∀ (m : ℕ) (Ψ : Fin m → SB (Matrix n₁ n₀ k)) (Φ₀ : Fin m → SB (n₁ → k)),
      (∀ x y, Θ x y = ∑ i, (Ψ i).1 x * (Φ₀ i).1 y) → ∑ i, app (T (Ψ i)) (opEFJ ψ ν ρ (Φ₀ i).1 Φ.1) F =
      ∫ u, app (C u) (fun x => GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.hat ψ ν (Θ x) u) ∂(Measure.pi fun _ => ν) := by
    intro m Ψ Φ₀ hd
    simp only [key]
    rw [← integral_finset_sum _ fun i _ => int1 _ _]
    congr 1; funext u
    have : (fun x => GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.hat ψ ν (Θ x) u) =
        (∑ i, GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.hat ψ ν (Φ₀ i).1 u • Ψ i : SB (Matrix n₁ n₀ k)).1 := by
      funext x
      simp only [GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.hat, hd, Finset.sum_mul, mul_assoc]
      rw [integral_finset_sum _ fun i _ => (int2 _ u).const_mul _]
      simp [integral_const_mul, mul_comm]
    rw [this, GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.app_coe]
    simp
  obtain ⟨m, Ψ, Φ₀, hd, rfl⟩ := hz
  obtain ⟨m', Ψ', Φ₀', hd', rfl⟩ := hz'
  exact (val m Ψ Φ₀ hd).trans (val m' Ψ' Φ₀' hd').symm

end GlobalTheory.PosOne.SymComb

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos SymDbl OneDbl comb)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PosOne.SymComb

section
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasMat

theorem symmetricDoubleIntegral_combination_of_pointValues : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k]
    (n₀ n₁ n₂ : Type) [Fintype n₀] [DecidableEq n₀] [Fintype n₁] [DecidableEq n₁] [Fintype n₂] [DecidableEq n₂] (c ρ : ℕ),
    c + 1 = 2 * ρ → ∀ (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (ν : Measure k), IsSelfDual ψ ν →
  ∀ (μ₁ μ₂ : kˣ →* ℂˣ) (m₁ : Measure (GL n₁ k)) (G₁ : Measure (GL (n₁ ⊕ Fin (c + 1)) k)) (m₂ : Measure (GL n₂ k))
    (G₂ : Measure (GL (n₂ ⊕ Fin c) k)), m₁.IsHaarMeasure → G₁.IsHaarMeasure → m₂.IsHaarMeasure → G₂.IsHaarMeasure →
  ∀ (A : Type) [AddCommGroup A] [Module ℂ A] (τ : Representation ℂ (GL (n₂ ⊕ Fin c) k) A), IsSmoothRep τ →
  ∀ (T : SB (Matrix n₁ n₀ k) →ₗ[ℂ] SB (Matrix n₂ n₁ k) →ₗ[ℂ] A →ₗ[ℂ] ℂ), TriPos ψ μ₁ μ₂ ρ τ T →
  ∀ (F : A) (P₁ : SB (Matrix (n₁ ⊕ Fin (c + 1)) (n₀ ⊕ Fin (c + 1 + 1)) k)) (P₂ : SB (Matrix (n₂ ⊕ Fin c) (n₁ ⊕ Fin (c + 1)) k))
    (e : GL (n₀ ⊕ Fin (c + 1 + 1)) k →₀ ℂ) (z : GL (n₀ ⊕ Fin (c + 1 + 1)) k → ℂ)
    (v : GL (n₀ ⊕ Fin (c + 1 + 1)) k → GL (n₁ ⊕ Fin (c + 1)) k → GL (n₂ ⊕ Fin c) k → ℂ),
    (∀ a ∈ e.support, SymDbl ψ ν m₁ G₁ m₂ G₂ μ₁ μ₂ ρ τ T F (om μ₁ a 1 P₁.1) P₂.1 (z a)) →
    (∀ a ∈ e.support, ∀ x y, HasTensorVal (fun Ψ Φ₀ => app (T Ψ) (opEFJ ψ ν ρ Φ₀.1 (om μ₂ x y P₂.1)) (τ y F))
      (fl ψ ν μ₁ ρ (om μ₁ a x P₁.1)) (v a x y)) →
    ∃ u : GL (n₁ ⊕ Fin (c + 1)) k → ℂ, (∀ x, IsQuotInt ν m₂ G₂ ρ (fun y => comb e fun a => v a x y) (u x)) ∧
      IsQuotIntFJ ν m₁ G₁ ρ u (comb e z) := by
  intro k _ _ _ _ _ _ n₀ n₁ n₂ _ _ _ _ _ _ c ρ hc ψ hψ hψ1 ν hν μ₁ μ₂ m₁ G₁ m₂ G₂ i₁ j₁ i₂ j₂ A _ _ τ _ T _ F P₁ P₂
    e z v hz hv
  classical
  haveI := hν.1
  have h1 : 1 ≤ ρ := by omega
  have h2 : ρ ≤ c := by omega
  have q0 : IsQuotInt ν m₂ G₂ ρ (fun _ => 0) 0 := ⟨0, zero_mem _, fun _ => by simp, by simp⟩
  have ql := fun (a : ℂ) f f' z z' => QuotLinear.isQuotInt_linear k n₂ c ρ h1 h2 ν m₂ G₂ f f' a z z'
  have step : ∀ a, ∃ f : GL (n₁ ⊕ Fin (c + 1)) k → ℂ, a ∈ e.support →
      (∀ x, IsQuotInt ν m₂ G₂ ρ (fun y => v a x y) (f x)) ∧ IsQuotIntFJ ν m₁ G₁ ρ f (z a) := by
    intro a
    by_cases ha : a ∈ e.support
    swap
    · exact ⟨0, fun h => absurd h ha⟩
    obtain ⟨w, hw, f, hf, hq⟩ := hz a ha
    refine ⟨f, fun _ => ⟨fun x => ?_, hq⟩⟩
    obtain ⟨m, Ψ, Φ₀, hd, hfx⟩ := hf x
    rw [← om_mul, one_mul, mul_one] at hd
    have s := rel_sum _ q0 ql Finset.univ (fun _ => 1) _ _ fun i _ => hw x (Ψ i) (Φ₀ i)
    simp only [one_mul] at s
    rw [hfx]
    convert s using 2 with y
    exact tensorVal_unique h1 h2 hψ hψ1 hν T (τ y F) ⟨_, om_mem_SB μ₂ x y P₂.2⟩ _ (hv a ha x y) ⟨m, Ψ, Φ₀, hd, rfl⟩
  choose f hf using step
  refine ⟨fun x => ∑ a ∈ e.support, e a * f a x, fun x => ?_, ?_⟩
  · exact rel_sum _ q0 ql e.support e _ _ fun a ha => (hf a ha).1 x
  · exact rel_sum (IsQuotIntFJ ν m₁ G₁ ρ) ⟨0, zero_mem _, fun _ => by simp, by simp⟩
      (fun a _ _ _ _ => isQuotIntFJ_linear h1 (by omega) ν m₁ G₁ a) e.support e f z fun a ha => (hf a ha).2

end

theorem symDbl_comb : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k]
    (n₀ n₁ n₂ : Type) [Fintype n₀] [DecidableEq n₀] [Fintype n₁] [DecidableEq n₁] [Fintype n₂] [DecidableEq n₂] (c ρ : ℕ),
    c + 1 = 2 * ρ → ∀ (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (ν : Measure k), IsSelfDual ψ ν →
  ∀ (μ₁ μ₂ : kˣ →* ℂˣ) (m₁ : Measure (GL n₁ k)) (G₁ : Measure (GL (n₁ ⊕ Fin (c + 1)) k)) (m₂ : Measure (GL n₂ k))
    (G₂ : Measure (GL (n₂ ⊕ Fin c) k)), m₁.IsHaarMeasure → G₁.IsHaarMeasure → m₂.IsHaarMeasure → G₂.IsHaarMeasure →
  ∀ (A : Type) [AddCommGroup A] [Module ℂ A] (τ : Representation ℂ (GL (n₂ ⊕ Fin c) k) A), IsSmoothRep τ →
  ∀ (T : SB (Matrix n₁ n₀ k) →ₗ[ℂ] SB (Matrix n₂ n₁ k) →ₗ[ℂ] A →ₗ[ℂ] ℂ), TriPos ψ μ₁ μ₂ ρ τ T →
  ∀ (F : A) (P₁ : SB (Matrix (n₁ ⊕ Fin (c + 1)) (n₀ ⊕ Fin (c + 1 + 1)) k)) (P₂ : SB (Matrix (n₂ ⊕ Fin c) (n₁ ⊕ Fin (c + 1)) k))
    (e : GL (n₀ ⊕ Fin (c + 1 + 1)) k →₀ ℂ) (z : GL (n₀ ⊕ Fin (c + 1 + 1)) k → ℂ)
    (v : GL (n₀ ⊕ Fin (c + 1 + 1)) k → GL (n₁ ⊕ Fin (c + 1)) k → GL (n₂ ⊕ Fin c) k → ℂ),
    (∀ a ∈ e.support, SymDbl ψ ν m₁ G₁ m₂ G₂ μ₁ μ₂ ρ τ T F (om μ₁ a 1 P₁.1) P₂.1 (z a)) →
    (∀ a ∈ e.support, ∀ x y, HasTensorVal (fun Ψ Φ₀ => app (T Ψ) (opEFJ ψ ν ρ Φ₀.1 (om μ₂ x y P₂.1)) (τ y F))
      (fl ψ ν μ₁ ρ (om μ₁ a x P₁.1)) (v a x y)) →
    ∃ u : GL (n₁ ⊕ Fin (c + 1)) k → ℂ, (∀ x, IsQuotInt ν m₂ G₂ ρ (fun y => comb e fun a => v a x y) (u x)) ∧
      IsQuotIntFJ ν m₁ G₁ ρ u (comb e z) :=
  symmetricDoubleIntegral_combination_of_pointValues

end GlobalTheory.PosOne.SymComb
