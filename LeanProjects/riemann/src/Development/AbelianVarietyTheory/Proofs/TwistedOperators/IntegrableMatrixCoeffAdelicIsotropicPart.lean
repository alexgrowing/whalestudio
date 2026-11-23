import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaSeriesSummableOnCovolumeDomain
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaSquareIntegrable
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallyWeilMatrixCoeffFinitePointInvariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompletedHomLatticeMultipleMemOpenLevel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompletedHomLatticeFinitelyGenerated
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsOpenNsmulCompletedHomLatticeFiniteAdelic
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CoefInteg

open GlobalTheory.OrientedHeis GlobalTheory.FockCompare
open GlobalTheory.Ker (ipO)

section Coords

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ}

theorem exists_coords_all (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1)) (S T : HSp D)
    (U : AddSubgroup (WO S T)) (hU : IsOpen (U : Set (WO S T))) :
    ∃ (n : ℕ) (b : Fin n → ℝ →+ WO S T) (ℓ : WO S T → Fin n → ℝ),
      (∀ i, Formalism.L2.Theta.IsRealDir T S (b i)) ∧
      (∀ w i (t : ℝ), ψ (symplO S T (b i t) w) = Complex.exp (t * (2 * Real.pi * Complex.I * (ℓ w i : ℝ)))) ∧
      (∀ i, Continuous fun w => ℓ w i) ∧ (∀ w w' i, ℓ (w + w') i = ℓ w i + ℓ w' i) ∧
      Function.Injective (fun y : Matrix (Fin T.rank) (Fin S.rank) D.host.E => ℓ (ratW T S y)) ∧
      ∀ y, (∀ v ∈ U, v.map (infPart D) = 0 → ψ (symplO S T v (ratW T S y)) = 1) → ∀ i, ∃ k : ℤ, ℓ (ratW T S y) i = k := by
  classical
  obtain ⟨θ, hθ⟩ := hψ.2.1
  obtain ⟨σ, h⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  let rat : Matrix (Fin T.rank) (Fin S.rank) D.host.E →+ WO S T := (incA D).toAddMonoidHom.mapMatrix
  have hrat : ∀ y, rat y = ratW T S y := fun _ => rfl
  let z : Matrix (Fin T.rank) (Fin S.rank) D.host.E →+ RW T S := (piW θ T S).comp rat
  let fpart : Matrix (Fin T.rank) (Fin S.rank) D.host.E →+ WO S T := rat - (iotaW σ T S).comp z
  have hfin : ∀ y, (fpart y).map (infPart D) = 0 := fun y => by
    have hp : piW θ T S (fpart y) = 0 := by
      show piW θ T S (rat y - iotaW σ T S (piW θ T S (rat y))) = 0
      rw [AddMonoidHom.map_sub, h.pi_iota, sub_self]
    ext i j
    exact ThetaCont.infPart_eq_zero h _ fun τ => congrFun (congrFun (congrFun hp τ) i) j
  let e := Module.finBasis ℚ (Matrix (Fin T.rank) (Fin S.rank) D.host.E)
  choose N hN hNU using fun i => GlobalTheory.SplitScalar.exists_nsmul_mem U hU (hfin (e i))
  let lam := fun i => N i • e i
  have hchar : ∀ w i (t : ℝ), ψ (symplO S T (GlobalTheory.TwFour.realLine σ S T (z (lam i)) t) w) = _ :=
    fun w i t => GlobalTheory.TwFour.psi_realLine h hψ w (z (lam i)) t
  refine ⟨_, fun i => GlobalTheory.TwFour.realLine σ S T (z (lam i)), fun w i => omO S T (piW θ T S w) (z (lam i)),
    fun i => GlobalTheory.TwFour.isRealDir_realLine h _, hchar, fun i => ?_, fun w w' i => ?_, ?_, ?_⟩
  · have hom : Continuous fun x : RW T S => omO S T x (z (lam i)) :=
      LinearMap.continuous_of_finiteDimensional ((omO S T).flip (z (lam i)))
    exact hom.comp (continuous_pi' hθ T S)
  · show omO S T (piW θ T S (w + w')) (z (lam i)) = omO S T (piW θ T S w) (z (lam i)) + omO S T (piW θ T S w') (z (lam i))
    rw [map_add, map_add, LinearMap.add_apply]
  · intro y y' hyy
    by_contra hne
    have hd : y - y' ≠ 0 := sub_ne_zero.2 hne
    let Λ : Matrix (Fin T.rank) (Fin S.rank) D.host.E →+ ℝ :=
      { toFun := fun l => omO S T (z (y - y')) (z l)
        map_zero' := by rw [map_zero, map_zero]
        map_add' := fun a b => by rw [map_add, map_add] }
    have h1 : ∀ i, Λ (lam i) = 0 := fun i => by
      have := congrFun hyy i
      show omO S T (z (y - y')) (z (lam i)) = 0
      rw [map_sub, map_sub, LinearMap.sub_apply, sub_eq_zero]
      exact this
    have h2 : ∀ i, Λ (e i) = 0 := fun i => by
      have := h1 i
      simp only [lam, map_nsmul, nsmul_eq_mul] at this
      exact (mul_eq_zero.1 this).resolve_left (Nat.cast_ne_zero.2 (hN i).ne')
    have h3 : Λ.toRatLinearMap = 0 := e.ext fun i => h2 i
    have h4 : ∀ l, Λ l = 0 := fun l => LinearMap.congr_fun h3 l
    obtain ⟨i, j, hij⟩ : ∃ i j, (y - y') i j ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      exact hd (Matrix.ext hcon)
    obtain ⟨_, ⟨g, rfl⟩, hγ⟩ := GlobalTheory.RatAnnih.exists_symplO_eq S T (rat (y - y')) i j ((y - y') i j)⁻¹
    have h5 : symplO S T (rat (y - y')) (rat g) = algebraMap D.host.F (AF D.host.F) 2 := by
      haveI : Module.Finite D.host.F D.host.E := Module.finite_of_finrank_pos (by rw [D.sp.cm.deg2]; norm_num)
      have e1 : incA D ((y - y') i j)⁻¹ * rat (y - y') i j = incA D 1 := by
        show incA D ((y - y') i j)⁻¹ * incA D ((y - y') i j) = _
        rw [← map_mul, inv_mul_cancel₀ hij]
      have e2 : Algebra.trace D.host.F D.host.E 1 = 2 := by
        rw [← map_one (algebraMap D.host.F D.host.E), Algebra.trace_algebraMap, D.sp.cm.deg2]
        norm_num
      refine hγ.trans ?_
      rw [e1, ← e2]
      exact GlobalTheory.SymplecticOrthogonalSesquilinear.trace_one_tmul _ 1
    have h6 := GlobalTheory.TwFour.omO_rat h _ _ _ h5
    have h7 : omO S T (z (y - y')) (z g) = 0 := h4 g
    have h8 : (Algebra.trace ℚ D.host.F (2 : D.host.F) : ℚ) = 0 := by
      have h9 : ((Algebra.trace ℚ D.host.F (2 : D.host.F) : ℚ) : ℝ) = 0 := h6.symm.trans h7
      exact_mod_cast h9
    have h10 : (2 : D.host.F) = algebraMap ℚ D.host.F 2 := by simp
    rw [h10, Algebra.trace_algebraMap, nsmul_eq_mul] at h8
    have h11 : (0 : ℕ) < Module.finrank ℚ D.host.F := Module.finrank_pos
    have h12 : ((Module.finrank ℚ D.host.F : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.2 h11.ne'
    exact h12 (by simpa using h8)
  · intro y hy i
    have hv : fpart (lam i) ∈ U := by
      simp only [lam, map_nsmul]
      exact hNU i
    have h1 := hy _ hv (hfin _)
    obtain ⟨a, ha⟩ := GlobalTheory.SymplecticOrthogonalSesquilinear.symplO_rat D S T (lam i) y
    have h2 : ψ (symplO S T (ratW T S (lam i)) (ratW T S y)) = 1 := (congrArg ψ ha).trans (hψ.1.2.2.1 a)
    have h3 : ratW T S (lam i) = GlobalTheory.TwFour.realLine σ S T (z (lam i)) 1 + fpart (lam i) := by
      show rat (lam i) = iotaW σ T S ((1 : ℝ) • z (lam i)) + (rat (lam i) - iotaW σ T S (z (lam i)))
      rw [one_smul]
      abel
    rw [h3, (GlobalTheory.SymplecticOrthogonalSesquilinear.symplO_alt D S T).1, ψ.map_add_eq_mul, h1, mul_one, hchar] at h2
    obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.1 h2
    refine ⟨k, ?_⟩
    have h2pi : (2 * Real.pi * Complex.I) ≠ 0 := Complex.two_pi_I_ne_zero
    have : ((omO S T (piW θ T S (ratW T S y)) (z (lam i)) : ℝ) : ℂ) = (k : ℂ) := by
      apply mul_left_cancel₀ h2pi
      push_cast at hk ⊢
      linear_combination hk
    exact_mod_cast this

end Coords

theorem prod_bound₂ {Fn Y ι : Type} [DecidableEq ι] (P : Fn → Prop) (Dop : ι → Fn → Fn) (hP : ∀ i f, P f → P (Dop i f))
    (T : Y → Fn → Fn → ℂ) (hb : ∀ f g, P f → P g → ∃ C, ∀ y, ‖T y f g‖ ≤ C) (ℓ : Y → ι → ℝ)
    (hrel : ∀ i f g y, P f → P g → |ℓ y i| * ‖T y f g‖ ≤ ‖T y (Dop i f) g‖ + ‖T y f (Dop i g)‖) (s : Finset ι) :
    ∀ f g, P f → P g → ∃ C, ∀ y, (∏ i ∈ s, (1 + ℓ y i ^ 2)) * ‖T y f g‖ ≤ C := by
  induction s using Finset.induction_on with
  | empty =>
    intro f g hf hg
    obtain ⟨C, hC⟩ := hb f g hf hg
    exact ⟨C, fun y => by simpa using hC y⟩
  | insert i s hi ih =>
    intro f g hf hg
    have hdf := hP i f hf
    have hdg := hP i g hg
    obtain ⟨C₁, h₁⟩ := ih f g hf hg
    obtain ⟨C₂, h₂⟩ := ih _ g (hP i _ hdf) hg
    obtain ⟨C₃, h₃⟩ := ih _ _ hdf hdg
    obtain ⟨C₄, h₄⟩ := ih f _ hf (hP i _ hdg)
    refine ⟨C₁ + C₂ + 2 * C₃ + C₄, fun y => ?_⟩
    rw [Finset.prod_insert hi]
    have hp : 0 ≤ ∏ j ∈ s, (1 + ℓ y j ^ 2) := Finset.prod_nonneg fun j _ => by positivity
    have e1 := hrel i f g y hf hg
    have e2 := hrel i _ g y hdf hg
    have e2' := hrel i f _ y hf hdg
    have e3 : ℓ y i ^ 2 * ‖T y f g‖ ≤ ‖T y (Dop i (Dop i f)) g‖ + 2 * ‖T y (Dop i f) (Dop i g)‖ + ‖T y f (Dop i (Dop i g))‖ := by
      calc ℓ y i ^ 2 * ‖T y f g‖ = |ℓ y i| * (|ℓ y i| * ‖T y f g‖) := by rw [← mul_assoc, abs_mul_abs_self, sq]
        _ ≤ |ℓ y i| * (‖T y (Dop i f) g‖ + ‖T y f (Dop i g)‖) := mul_le_mul_of_nonneg_left e1 (abs_nonneg _)
        _ = |ℓ y i| * ‖T y (Dop i f) g‖ + |ℓ y i| * ‖T y f (Dop i g)‖ := by ring
        _ ≤ _ := by linarith
    have e4 := mul_le_mul_of_nonneg_left e3 hp
    have a2 := h₂ y
    have a3 := h₃ y
    have a4 := h₄ y
    have a1 := h₁ y
    calc (1 + ℓ y i ^ 2) * (∏ j ∈ s, (1 + ℓ y j ^ 2)) * ‖T y f g‖
        = (∏ j ∈ s, (1 + ℓ y j ^ 2)) * ‖T y f g‖ + (∏ j ∈ s, (1 + ℓ y j ^ 2)) * (ℓ y i ^ 2 * ‖T y f g‖) := by ring
      _ ≤ _ := by nlinarith

section Coef

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {V W : HSp D} {μ : Measure (WO V W)} {𝓕 : Set (WO V W)}

theorem ipO_smul_left (c : ℂ) (f g : WO V W → ℂ) : ipO μ 𝓕 (c • f) g = c * ipO μ 𝓕 f g := by
  unfold GlobalTheory.Ker.ipO
  rw [← integral_const_mul]
  simp only [Pi.smul_apply, smul_eq_mul, mul_assoc]

theorem coef_level (hψ : IsStdChar D ψ (-1)) (hμ : μ.IsAddHaarMeasure) (h𝓕 : IsAddFundamentalDomain (ratL W V) 𝓕 μ)
    {f g : WO V W → ℂ} (hf : IsThetaFunO ψ V W f) (hg : IsThetaFunO ψ V W g) (u v : WO V W)
    (hv : heisO ψ V W v f = f) (hv' : heisO ψ V W v g = g) :
    ipO μ 𝓕 (heisO ψ V W u f) g = ψ (symplO V W v u) * ipO μ 𝓕 (heisO ψ V W u f) g := by
  have hu := GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hf u
  have h := GlobalTheory.Size.ipO_heisO hψ hμ h𝓕 hu hg v
  rw [GlobalTheory.TwFour.heisO_comm, hv, hv', ipO_smul_left] at h
  exact h.symm

theorem coef_rel (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) {L : ℝ →+ WO V W} (hL : Formalism.L2.Theta.IsRealDir W V L)
    (hμ : μ.IsAddHaarMeasure) (h𝓕 : IsAddFundamentalDomain (ratL W V) 𝓕 μ)
    {f g : WO V W → ℂ} (hf : IsThetaFunO ψ V W f) (hg : IsThetaFunO ψ V W g) (u : WO V W) (c : ℂ)
    (hc : ∀ t : ℝ, ψ (symplO V W (L t) u) = Complex.exp (t * c)) :
    c * ipO μ 𝓕 (heisO ψ V W u f) g =
      -ipO μ 𝓕 (heisO ψ V W u (dLine ψ V W L f)) g - ipO μ 𝓕 (heisO ψ V W u f) (dLine ψ V W L g) := by
  have hu := GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hf u
  have hu' := GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ (theta_dLine hθ hψ hL hf) u
  have hI := fun {g g'} => GlobalTheory.Size.integrableOn_mul_conj (f := g) (f' := g') hψ hμ h𝓕
  have h := GlobalTheory.ThetaSquare.ipO_dLine hψ hθ hL hμ h𝓕 hu hg
  rw [GlobalTheory.TwFour.dLine_heisO hθ hψ hL hf u c hc] at h
  have hadd : ipO μ 𝓕 (c • heisO ψ V W u f + heisO ψ V W u (dLine ψ V W L f)) g =
      c * ipO μ 𝓕 (heisO ψ V W u f) g + ipO μ 𝓕 (heisO ψ V W u (dLine ψ V W L f)) g := by
    unfold GlobalTheory.Ker.ipO
    have e : ∀ x, (c • heisO ψ V W u f + heisO ψ V W u (dLine ψ V W L f)) x * conj (g x) =
        c * (heisO ψ V W u f x * conj (g x)) + heisO ψ V W u (dLine ψ V W L f) x * conj (g x) := fun x => by
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    simp_rw [e]
    rw [integral_add ((hI hu hg).const_mul c) (hI hu' hg), integral_const_mul]
  rw [hadd] at h
  linear_combination h

theorem norm_coef_le [IsFiniteMeasure (μ.restrict 𝓕)] (hψ : IsStdChar D ψ (-1)) {f g : WO V W → ℂ} {a b : ℝ} (ha : ∀ w, ‖f w‖ ≤ a) (hb : ∀ w, ‖g w‖ ≤ b)
    (u : WO V W) : ‖ipO μ 𝓕 (heisO ψ V W u f) g‖ ≤ a * b * (μ.restrict 𝓕).real Set.univ := by
  have h0 : 0 ≤ a := (norm_nonneg _).trans (ha 0)
  refine norm_integral_le_of_norm_le_const (.of_forall fun x => ?_)
  rw [norm_mul, Complex.norm_conj, GlobalTheory.ThetaSquare.norm_heisO hψ]
  exact mul_le_mul (ha _) (hb _) (norm_nonneg _) h0

theorem continuous_coef (hψ : IsStdChar D ψ (-1)) (hμ : μ.IsAddHaarMeasure) (h𝓕 : IsAddFundamentalDomain (ratL W V) 𝓕 μ)
    {f g : WO V W → ℂ} (hf : IsThetaFunO ψ V W f) (hg : IsThetaFunO ψ V W g) {X : Type} [TopologicalSpace X]
    [FirstCountableTopology X] {A : X → WO V W} (hA : Continuous A) :
    Continuous fun x => ipO μ 𝓕 (heisO ψ V W (A x) f) g := by
  have : IsFiniteMeasure (μ.restrict 𝓕) := isFiniteMeasure_restrict.2 (GlobalTheory.Size.measure_dom hμ h𝓕).2
  obtain ⟨a, ha⟩ := theta_bounded hψ hf
  obtain ⟨b, hb⟩ := theta_bounded hψ hg
  have h0 : 0 ≤ a := (norm_nonneg _).trans (ha 0)
  refine continuous_of_dominated (bound := fun _ => a * b)
    (fun x => (GlobalTheory.Size.integrableOn_mul_conj hψ hμ h𝓕 (GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hf _) hg).aestronglyMeasurable)
    (fun x => .of_forall fun w => ?_) (integrable_const _) (.of_forall fun w => ?_)
  · rw [norm_mul, Complex.norm_conj, GlobalTheory.ThetaSquare.norm_heisO hψ]
    exact mul_le_mul (ha _) (hb _) (norm_nonneg _) h0
  · refine Continuous.mul (Continuous.mul ?_ ?_) continuous_const
    · exact hψ.1.1.comp (continuous_symplOH continuous_const hA)
    · exact hf.cont.comp (continuous_const.add hA)

end Coef

theorem integrable_of_translates {X Y : Type} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X] [T2Space X]
    [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [μ.IsAddHaarMeasure] [Countable Y]
    (r : Y → X) (K : Set X) (hK : IsCompact K) (hcov : ∀ x, ∃ y, r y + x ∈ K) (c : X → ℂ) (hc : Continuous c) (T : Y → ℝ)
    (hT : ∀ y x, r y + x ∈ K → ‖c x‖ ≤ T y) (hs : Summable T) : Integrable c μ := by
  have hmeas : ∀ y, MeasurableSet ((fun x => r y + x) ⁻¹' K) := fun y =>
    (hK.isClosed.preimage (continuous_const.add continuous_id)).measurableSet
  have hm : ∀ y, μ ((fun x => r y + x) ⁻¹' K) = μ K := fun y => measure_preimage_add μ (r y) K
  have hfin : ∀ y, μ ((fun x => r y + x) ⁻¹' K) < ⊤ := fun y => by rw [hm]; exact hK.measure_lt_top
  have hU : ⋃ y, (fun x => r y + x) ⁻¹' K = Set.univ := Set.eq_univ_of_forall fun x => by
    obtain ⟨y, hy⟩ := hcov x
    exact Set.mem_iUnion.2 ⟨y, hy⟩
  have h := integrableOn_iUnion_of_summable_integral_norm (μ := μ) (f := c)
    (fun y => Measure.integrableOn_of_bounded (hfin y).ne hc.aestronglyMeasurable (M := T y)
      ((ae_restrict_iff' (hmeas y)).2 (.of_forall fun x hx => hT y x hx)))
    (Summable.of_nonneg_of_le (fun y => integral_nonneg fun x => norm_nonneg _) (fun y => ?_)
      (hs.mul_right (μ.real K)))
  · rwa [hU, integrableOn_univ] at h
  · have h1 := norm_setIntegral_le_of_norm_le_const (μ := μ) (s := (fun x => r y + x) ⁻¹' K) (f := fun x => ‖c x‖) (C := T y)
      (hfin y) (fun x hx => by simpa using hT y x hx)
    have h2 : μ.real ((fun x => r y + x) ⁻¹' K) = μ.real K := by simp only [Measure.real, hm]
    rw [h2] at h1
    exact (le_abs_self _).trans h1

section Finite

variable {D : D7}

theorem exists_nsmul_compact {S T : HSp D} (P : AddSubgroup (WO S T)) (hP : IsOpen (P : Set (WO S T)))
    (hreal : ∀ x : WO S T, x.map (finPart D) = 0 → x ∈ P) {K : Set (WO S T)} (hK : IsCompact K) :
    ∃ M : ℕ, 0 < M ∧ ∀ x ∈ K, M • x ∈ P := by
  classical
  obtain ⟨i1, -⟩ := GlobalTheory.AdelicMatrixLattice.lattice D T S
  haveI : IsTopologicalAddGroup (WO S T) := i1
  haveI : ContinuousSub (WO S T) := IsTopologicalAddGroup.to_continuousSub
  have ht : ∀ x : WO S T, IsOpen {y : WO S T | y - x ∈ P} := fun x => hP.preimage (continuous_id.sub continuous_const)
  have hone : ∀ k : WO S T, ∃ N : ℕ, 0 < N ∧ N • k ∈ P := fun k => by
    obtain ⟨N, hN, h⟩ := GlobalTheory.SplitScalar.exists_nsmul_mem P hP (GlobalTheory.Mem.CoefInv.fin_part k)
    refine ⟨N, hN, ?_⟩
    have e : k = (k - GlobalTheory.SplitScalar.realIdem D • k) + GlobalTheory.SplitScalar.realIdem D • k := by abel
    rw [e, nsmul_add]
    exact P.add_mem h (P.nsmul_mem (hreal _ (GlobalTheory.Mem.CoefInv.real_part k)) N)
  choose N hN hNP using hone
  obtain ⟨t, -, hcov⟩ := hK.elim_nhds_subcover (fun x => {y : WO S T | y - x ∈ P})
    (fun x _ => (ht x).mem_nhds (by simp [P.zero_mem]))
  refine ⟨∏ x ∈ t, N x, Finset.prod_pos fun x _ => hN x, fun y hy => ?_⟩
  obtain ⟨x, hx, hyx⟩ := Set.mem_iUnion₂.1 (hcov hy)
  have e : y = (y - x) + x := by abel
  rw [e, nsmul_add]
  refine P.add_mem (P.nsmul_mem hyx _) ?_
  obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem N hx
  rw [hc, mul_comm, mul_smul]
  exact P.nsmul_mem (hNP x) c

end Finite

section Lat

variable {D : D7} {S T : HSp D}

set_option synthInstance.maxHeartbeats 200000 in
theorem eq_nsmul_of_parts {v l : WO S T} {n : ℕ} (hv0 : v.map (infPart D) = 0) (hl0 : l.map (infPart D) = 0)
    (h : (v - (1 : ℕ) • (n • l)).map (finPart D) = 0) : v = n • l := by
  rw [one_smul] at h
  ext i j
  refine sub_eq_zero.1 (GlobalTheory.LatVac.eq_zero_of_parts _ ?_ (congrFun (congrFun h i) j))
  show infPart D (v i j - n • l i j) = 0
  rw [nsmul_eq_mul, RingHom.map_sub, RingHom.map_mul, show infPart D (v i j) = 0 from congrFun (congrFun hv0 i) j,
    show infPart D (l i j) = 0 from congrFun (congrFun hl0 i) j, mul_zero, sub_zero]

set_option synthInstance.maxHeartbeats 200000 in
theorem psi_nsmul_lat {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
    {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT)
    {l l₁ k : WO S T} (hl : l ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True)
    (hl₁ : l₁ ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True)
    (N M : ℕ) (hk : (M • k - (1 : ℕ) • l₁).map (finPart D) = 0) : ψ (symplO S T (N • M • l) k) = 1 := by
  rw [one_smul] at hk
  have hNl := AddSubgroup.nsmul_mem _ hl N
  rw [smul_comm N M l, GlobalTheory.Mem.CoefInv.symplO_nsmul, show M • k = l₁ + (M • k - l₁) by abel,
    (GlobalTheory.SymplecticOrthogonalSesquilinear.symplO_alt D S T).2.1, ψ.map_add_eq_mul,
    GlobalTheory.LatVac.char_sympl_eq_one hψ hS hT hNl hl₁, one_mul,
    GlobalTheory.SplitScalar.symplO_skew S T (M • k - l₁) (N • l),
    GlobalTheory.SplitScalar.symplO_real_fin S T hk (GlobalTheory.SplitScalar.latO_fin hNl), neg_zero, ψ.map_zero_eq_one]

end Lat

section Main

set_option synthInstance.maxHeartbeats 100000 in

theorem core (D : D7) (V W S : HSp D) (hS : S.gram = 1) (C C' : Matrix (Fin V.rank) (Fin S.rank) D.host.E)
    (h1 : adj D C * V.gram * C' = 1) (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1))
    (μ : Measure (Mx D W.rank S.rank)) (hμ : μ.IsAddHaarMeasure) (μV : Measure (WO V W)) (𝓕V : Set (WO V W))
    (hμV : μV.IsAddHaarMeasure) (h𝓕V : IsAddFundamentalDomain (ratL W V) 𝓕V μV) (F G : WO V W → ℂ)
    (hF : IsThetaFunO ψ V W F) (hG : IsThetaFunO ψ V W G) :
    Integrable (fun y : Mx D W.rank S.rank => ∫ w in 𝓕V, heisO ψ V W (isoPart V W C y) F w * star (G w) ∂μV) μ := by
  classical
  obtain ⟨θ, hθ⟩ := hψ.2.1
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hKc⟩ := GlobalTheory.AdelicMatrixLattice.lattice D W S
  haveI : IsTopologicalAddGroup (WO S W) := i1
  haveI : LocallyCompactSpace (WO S W) := i2
  haveI : SecondCountableTopology (WO S W) := i3
  haveI : T2Space (WO S W) := i4
  haveI : BorelSpace (WO S W) := ⟨rfl⟩
  haveI := hμ
  have : IsFiniteMeasure (μV.restrict 𝓕V) := isFiniteMeasure_restrict.2 (GlobalTheory.Size.measure_dom hμV h𝓕V).2
  let Dh : WO S W →+ WO V W :=
    { toFun := isoPart V W C', map_zero' := Matrix.zero_mul _, map_add' := fun a b => Matrix.add_mul a b _ }
  have hAc : Continuous (isoPart V W C) := Continuous.matrix_mul continuous_id continuous_const
  have hDc : Continuous (isoPart V W C') := Continuous.matrix_mul continuous_id continuous_const
  have hpair : ∀ a b : WO S W, symplO V W (isoPart V W C' a) (isoPart V W C b) = symplO S W a b := fun a b => by
    rw [GlobalTheory.SplitScalar.symplO_skew V W (isoPart V W C b) (isoPart V W C' a),
      GlobalTheory.TwFour.symplO_isoPart_pair V W S hS C C' h1 b a, GlobalTheory.SplitScalar.symplO_skew S W b a]

  obtain ⟨UF, hUF, hUFf⟩ := hF.level
  obtain ⟨UG, hUG, hUGf⟩ := hG.level
  let U₀ : AddSubgroup (WO S W) := (UF ⊓ UG).comap Dh
  have hU₀ : IsOpen (U₀ : Set (WO S W)) := (hUF.inter hUG).preimage hDc
  have hfix : ∀ v ∈ U₀, v.map (infPart D) = 0 →
      heisO ψ V W (isoPart V W C' v) F = F ∧ heisO ψ V W (isoPart V W C' v) G = G := fun v hv hv0 => by
    have h0 := GlobalTheory.TwFour.isoPart_map_eq_zero (infPart D) V W C' hv0
    have hv' : Dh v ∈ UF ⊓ UG := hv
    exact ⟨hUFf _ hv'.1 h0, hUGf _ hv'.2 h0⟩
  let T : WO S W → (WO V W → ℂ) → (WO V W → ℂ) → ℂ := fun w f g => ipO μV 𝓕V (heisO ψ V W (isoPart V W C w) f) g
  have hsupp : ∀ w, T w F G ≠ 0 → ∀ v ∈ U₀, v.map (infPart D) = 0 → ψ (symplO S W v w) = 1 := fun w hw v hv hv0 => by
    obtain ⟨h₁, h₂⟩ := hfix v hv hv0
    have h := coef_level hψ hμV h𝓕V hF hG (isoPart V W C w) _ h₁ h₂
    rw [hpair] at h
    exact mul_right_cancel₀ hw (h.symm.trans (one_mul _).symm)

  have hSd := GlobalTheory.PlaceModel.isSelfDualC_latFrame S
  have hWd := GlobalTheory.PlaceModel.isSelfDualC_latFrame W
  let L : AddSubgroup (WO S W) := latO S W (GlobalTheory.PlaceModel.latFrame S : Set (Fin S.rank → D.host.E))
    (GlobalTheory.PlaceModel.latFrame W : Set (Fin W.rank → D.host.E)) fun _ => True
  obtain ⟨N, hN, hNU⟩ := (GlobalTheory.LatLevel.level_of_generators D S W _ _ hSd hWd
    (GlobalTheory.LatFinGen.latO_finitely_generated D S W _ _ hSd hWd)).1 U₀ hU₀
  let P₀ : AddSubgroup (WO S W) := GlobalTheory.LatLevel.finSat L
  have hP₀ : IsOpen (P₀ : Set (WO S W)) := by
    convert GlobalTheory.LatOpen.isOpen_nsmul_latO D S W _ _ hSd hWd 1 one_pos using 1
    exact Set.ext fun x => GlobalTheory.LatLevel.mem_finSat _ x
  have hreal : ∀ x : WO S W, x.map (finPart D) = 0 → x ∈ P₀ := fun x hx =>
    (GlobalTheory.LatLevel.mem_finSat _ x).2 ⟨0, L.zero_mem, by simpa using hx⟩
  obtain ⟨M, hM, hMK⟩ := exists_nsmul_compact P₀ hP₀ hreal hK
  let Q : AddSubgroup (WO S W) := GlobalTheory.LatLevel.finSat (L.map (nsmulAddMonoidHom (N * M)))
  have hQ : IsOpen (Q : Set (WO S W)) := by
    convert GlobalTheory.LatOpen.isOpen_nsmul_latO D S W _ _ hSd hWd (N * M) (mul_pos hN hM) using 1
    refine Set.ext fun x => (GlobalTheory.LatLevel.mem_finSat _ x).trans ⟨?_, ?_⟩
    · rintro ⟨_, ⟨l, hl, rfl⟩, h⟩
      exact ⟨l, hl, by simpa using h⟩
    · rintro ⟨l, hl, h⟩
      exact ⟨(N * M) • l, ⟨l, hl, rfl⟩, by simpa using h⟩

  have hkey : ∀ (y : Matrix (Fin W.rank) (Fin S.rank) D.host.E) (k : WO S W), k ∈ K → T (ratW W S y + k) F G ≠ 0 →
      ∀ v ∈ Q, v.map (infPart D) = 0 → ψ (symplO S W v (ratW W S y)) = 1 := by
    intro y k hk hne v hv hv0
    obtain ⟨_, ⟨l, hl, rfl⟩, hvl⟩ := (GlobalTheory.LatLevel.mem_finSat _ v).1 hv
    have hv' : v = (N * M) • l := eq_nsmul_of_parts hv0 (GlobalTheory.SplitScalar.latO_fin hl) hvl
    subst hv'
    have hA : ψ (symplO S W (N • M • l) (ratW W S y + k)) = 1 :=
      hsupp _ hne _ (hNU _ (L.nsmul_mem hl M)) (GlobalTheory.SplitScalar.latO_fin (L.nsmul_mem (L.nsmul_mem hl M) N))
    obtain ⟨l₁, hl₁, hk₁⟩ := (GlobalTheory.LatLevel.mem_finSat _ _).1 (hMK k hk)
    have hB : ψ (symplO S W (N • M • l) k) = 1 := psi_nsmul_lat hψ hSd hWd hl hl₁ N M hk₁
    rw [(GlobalTheory.SymplecticOrthogonalSesquilinear.symplO_alt D S W).2.1, ψ.map_add_eq_mul, hB, mul_one] at hA
    rw [← smul_smul]
    exact hA

  obtain ⟨n, b, ℓ, hb, hchar, hℓc, hℓa, hinj, hint⟩ := exists_coords_all ψ hψ S W Q hQ
  let Ldir : Fin n → ℝ →+ WO V W := fun i => Dh.comp (b i)
  have hL : ∀ i, Formalism.L2.Theta.IsRealDir W V (Ldir i) := fun i =>
    ⟨hDc.comp (hb i).1, fun t => GlobalTheory.TwFour.isoPart_map_eq_zero (finPart D) V W C' ((hb i).2 t)⟩
  have hc : ∀ w i (t : ℝ), ψ (symplO V W (Ldir i t) (isoPart V W C w)) =
      Complex.exp (t * (2 * Real.pi * Complex.I * (ℓ w i : ℝ))) := fun w i t => by
    show ψ (symplO V W (isoPart V W C' (b i t)) (isoPart V W C w)) = _
    rw [hpair]
    exact hchar w i t
  have hrel : ∀ i f g w, IsThetaFunO ψ V W f → IsThetaFunO ψ V W g →
      |ℓ w i| * ‖T w f g‖ ≤ ‖T w (dLine ψ V W (Ldir i) f) g‖ + ‖T w f (dLine ψ V W (Ldir i) g)‖ := by
    intro i f g w hf hg
    have h := coef_rel hψ hθ (hL i) hμV h𝓕V hf hg (isoPart V W C w) _ (hc w i)
    have h2 := congrArg norm h
    rw [norm_mul] at h2
    have h3 : ‖2 * Real.pi * Complex.I * ((ℓ w i : ℝ) : ℂ)‖ = 2 * Real.pi * |ℓ w i| := by
      simp [abs_of_pos Real.pi_pos]
    rw [h3] at h2
    have h4 := norm_sub_le (-T w (dLine ψ V W (Ldir i) f) g) (T w f (dLine ψ V W (Ldir i) g))
    rw [norm_neg] at h4
    have hpi : (1 : ℝ) ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
    have hn : 0 ≤ |ℓ w i| * ‖T w f g‖ := by positivity
    calc |ℓ w i| * ‖T w f g‖ ≤ 2 * Real.pi * (|ℓ w i| * ‖T w f g‖) := le_mul_of_one_le_left hn hpi
      _ = ‖-T w (dLine ψ V W (Ldir i) f) g - T w f (dLine ψ V W (Ldir i) g)‖ := by rw [← mul_assoc]; exact h2
      _ ≤ _ := h4
  have hbd : ∀ f g, IsThetaFunO ψ V W f → IsThetaFunO ψ V W g → ∃ c, ∀ w, ‖T w f g‖ ≤ c := fun f g hf hg => by
    obtain ⟨a, ha⟩ := theta_bounded hψ hf
    obtain ⟨a', ha'⟩ := theta_bounded hψ hg
    exact ⟨a * a' * (μV.restrict 𝓕V).real Set.univ, fun w => norm_coef_le hψ ha ha' _⟩
  obtain ⟨Cb, hCb⟩ := prod_bound₂ (IsThetaFunO ψ V W) (fun i => dLine ψ V W (Ldir i))
    (fun i f hf => theta_dLine hθ hψ (hL i) hf) T hbd ℓ hrel Finset.univ F G hF hG
  have hCb0 : 0 ≤ Cb := le_trans (by positivity) (hCb 0)

  choose Mi hMi using fun i => hK.exists_bound_of_continuousOn (hℓc i).continuousOn
  let A : ℝ := ∏ i, (2 * (1 + Mi i ^ 2))
  have hA0 : 0 ≤ A := Finset.prod_nonneg fun i _ => by positivity
  have hfac : ∀ (a c m : ℝ), |c| ≤ m → 1 + (a - c) ^ 2 ≤ 2 * (1 + m ^ 2) * (1 + a ^ 2) := by
    intro a c m hcm
    have h1 : c ^ 2 ≤ m ^ 2 := sq_le_sq' (abs_le.1 hcm).1 (abs_le.1 hcm).2
    nlinarith [sq_nonneg (a + c), sq_nonneg a, sq_nonneg c, mul_nonneg (sq_nonneg a) (sq_nonneg m)]
  have hPpos : ∀ y : Matrix (Fin W.rank) (Fin S.rank) D.host.E, 0 < ∏ i, (1 + ℓ (ratW W S y) i ^ 2) := fun y =>
    Finset.prod_pos fun i _ => by positivity
  let Bd : Matrix (Fin W.rank) (Fin S.rank) D.host.E → ℝ := fun y =>
    if ∃ k ∈ K, T (ratW W S y + k) F G ≠ 0 then A * Cb / ∏ i, (1 + ℓ (ratW W S y) i ^ 2) else 0
  have hBd0 : ∀ y, 0 ≤ Bd y := fun y => by
    simp only [Bd]
    split_ifs
    · exact div_nonneg (mul_nonneg hA0 hCb0) (hPpos y).le
    · exact le_rfl
  have hBd : ∀ y k, k ∈ K → ‖T (ratW W S y + k) F G‖ ≤ Bd y := by
    intro y k hk
    by_cases h0 : T (ratW W S y + k) F G = 0
    · rw [h0, norm_zero]
      exact hBd0 y
    · simp only [Bd]
      rw [if_pos ⟨k, hk, h0⟩, le_div_iff₀ (hPpos y)]
      have hx := hCb (ratW W S y + k)
      have hprod : ∏ i, (1 + ℓ (ratW W S y) i ^ 2) ≤ A * ∏ i, (1 + ℓ (ratW W S y + k) i ^ 2) := by
        rw [← Finset.prod_mul_distrib]
        refine Finset.prod_le_prod (fun i _ => by positivity) (fun i _ => ?_)
        have e : ℓ (ratW W S y) i = ℓ (ratW W S y + k) i - ℓ k i := by rw [hℓa]; ring
        rw [e]
        have := hMi i k hk
        rw [Real.norm_eq_abs] at this
        exact hfac _ _ _ this
      calc ‖T (ratW W S y + k) F G‖ * ∏ i, (1 + ℓ (ratW W S y) i ^ 2)
          ≤ ‖T (ratW W S y + k) F G‖ * (A * ∏ i, (1 + ℓ (ratW W S y + k) i ^ 2)) :=
            mul_le_mul_of_nonneg_left hprod (norm_nonneg _)
        _ = A * ((∏ i, (1 + ℓ (ratW W S y + k) i ^ 2)) * ‖T (ratW W S y + k) F G‖) := by ring
        _ ≤ A * Cb := mul_le_mul_of_nonneg_left hx hA0
  have : Countable (Matrix (Fin W.rank) (Fin S.rank) D.host.E) :=
    (Module.finBasis ℚ (Matrix (Fin W.rank) (Fin S.rank) D.host.E)).equivFun.injective.countable
  have hsum : Summable fun y => ‖((Bd y : ℝ) : ℂ)‖ := by
    refine GlobalTheory.TwFour.summable_norm_of_lattice (fun y => ((Bd y : ℝ) : ℂ)) (fun y => ℓ (ratW W S y)) hinj
      (fun y hy => ?_) (A * Cb) (fun y => ?_)
    · have hc' : ∃ k ∈ K, T (ratW W S y + k) F G ≠ 0 := by
        by_contra hcon
        apply hy
        simp only [Bd, if_neg hcon, Complex.ofReal_zero]
      obtain ⟨k, hk, hne⟩ := hc'
      exact hint y (hkey y k hk hne)
    · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hBd0 y)]
      simp only [Bd]
      split_ifs
      · rw [mul_div_cancel₀ _ (hPpos y).ne']
      · rw [mul_zero]
        exact mul_nonneg hA0 hCb0
  have hneg : ∀ y : Matrix (Fin W.rank) (Fin S.rank) D.host.E, ratW W S (-y) = -ratW W S y := fun y =>
    Matrix.map_neg _ (fun a => map_neg (incA D) a) y
  have key := integrable_of_translates μ (fun y : Matrix (Fin W.rank) (Fin S.rank) D.host.E => -ratW W S y) K hK
    (fun x => ?_) (fun y => T y F G) (continuous_coef hψ hμV h𝓕V hF hG hAc)
    (fun y => ‖((Bd y : ℝ) : ℂ)‖) (fun y x hx => ?_) hsum
  · exact key
  · obtain ⟨γ, hγ, hk⟩ := hKc x
    obtain ⟨y, rfl⟩ := hγ
    refine ⟨-y, ?_⟩
    show -ratW W S (-y) + x ∈ K
    rw [hneg, neg_neg]
    exact hk
  · have h := hBd y (-ratW W S y + x) hx
    rw [← add_assoc, add_neg_cancel, zero_add] at h
    refine h.trans ?_
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact le_abs_self _

end Main

end GlobalTheory.CoefInteg

namespace GlobalTheory.CoefInteg

theorem integrable_coef : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → ∀ C' : Matrix (Fin V.rank) (Fin r) D.host.E, adj D C * V.gram * C' = 1 → adj D C' * V.gram * C' = 0 → adj D C' * V.gram * B = 0 → ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (μ : Measure (Mx D W.rank r)), μ.IsAddHaarMeasure → ∀ (μV : Measure (WO V W)) (𝓕V : Set (WO V W)), μV.IsAddHaarMeasure → IsAddFundamentalDomain (ratL W V) 𝓕V μV → ∀ F G, IsThetaFunO ψ V W F → IsThetaFunO ψ V W G → Integrable (fun y : Mx D W.rank r => ∫ w in 𝓕V, heisO ψ V W (isoPart V W C (y)) F w * star (G w) ∂μV) μ := by
  intro D V V' W r C B _ C' h1 _ _ ψ hψ μ hμ μV 𝓕V hμV h𝓕V F G hF hG
  have hg : (GlobalTheory.Size.posSp D r).gram = 1 := by
    funext i j
    refine (Examples₂.stdSpace_gram_apply (E := D.host.E) Examples₂.star_isIntegral r (fun _ => false) r 0 i j).trans ?_
    change (if i = j then (Examples₂.sgn false : D.host.E) else 0) = if i = j then 1 else 0
    by_cases h : i = j <;> simp [h, Examples₂.sgn]
  exact core D V W (GlobalTheory.Size.posSp D r) hg C C' h1 ψ hψ μ hμ μV 𝓕V hμV h𝓕V F G hF hG

end GlobalTheory.CoefInteg

end
