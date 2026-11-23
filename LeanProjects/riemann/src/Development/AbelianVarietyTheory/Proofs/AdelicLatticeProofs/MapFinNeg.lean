import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
import Development.AbelianVarietyTheory.Proofs.HeightProofs.SmoothIffRealCoordinatesAndRealLines
import Development.AbelianVarietyTheory.Proofs.HeightProofs.CocompactTensor
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsInverseChart
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ContinuousBicharacterWeilSetupStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsRealPlaceSymplecticFormPositiveComplexStruStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HomSymplecticHalfFormAlgebraicLawsContinuousStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsOpenNsmulCompletedHomLatticeFiniteAdelicStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FiniteRationalPointsCompletedLatticeStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsSemicharacterCompletedSelfDualLatticeStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsNormaliseMeanSquareOfCocompactStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.VacuumO
open GlobalTheory.FockCompare

variable {D : D7}

theorem map_fin_add {m n : ℕ} {x y : Mx D m n} (hx : x.map (finPart D) = 0) (hy : y.map (finPart D) = 0) :
    (x + y).map (finPart D) = 0 := by
  funext i j
  have e1 : finPart D (x i j) = 0 := congrFun (congrFun hx i) j
  have e2 : finPart D (y i j) = 0 := congrFun (congrFun hy i) j
  show finPart D (x i j + y i j) = 0
  rw [RingHom.map_add, e1, e2, add_zero]

theorem map_fin_neg {m n : ℕ} {x : Mx D m n} (hx : x.map (finPart D) = 0) : (-x).map (finPart D) = 0 := by
  funext i j
  have e1 : finPart D (x i j) = 0 := congrFun (congrFun hx i) j
  show finPart D (-x i j) = 0
  rw [RingHom.map_neg, e1, neg_zero]

def thick {m n : ℕ} (Λ : AddSubgroup (Mx D m n)) (N : ℕ) : AddSubgroup (Mx D m n) where
  carrier := {x | ∃ l ∈ Λ, (x - N • l).map (finPart D) = 0}
  zero_mem' := ⟨0, Λ.zero_mem, by
    funext i j
    show finPart D (((0 : Mx D m n) - N • (0 : Mx D m n)) i j) = 0
    rw [nsmul_zero, sub_zero]
    exact RingHom.map_zero _⟩
  add_mem' := by
    rintro x y ⟨l, hl, hx⟩ ⟨l', hl', hy⟩
    refine ⟨l + l', Λ.add_mem hl hl', ?_⟩
    have e : x + y - N • (l + l') = (x - N • l) + (y - N • l') := by rw [nsmul_add]; abel
    rw [e]
    exact map_fin_add hx hy
  neg_mem' := by
    rintro x ⟨l, hl, hx⟩
    refine ⟨-l, Λ.neg_mem hl, ?_⟩
    have e : -x - N • (-l) = -(x - N • l) := by rw [neg_nsmul]; abel
    rw [e]
    exact map_fin_neg hx

theorem piW_eq_zero (θ : InfFam D) (S T : HSp D) {u : WO S T} (hu : u.map (infPart D) = 0) : piW θ T S u = 0 := by
  funext τ i j
  have e : infPart D (u i j) = 0 := congrFun (congrFun hu i) j
  show θ τ (infPart D (u i j)) = 0
  rw [e, RingHom.map_zero]

theorem lineAt_eq {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} (hσ : Chart θ σ) (S T : HSp D) (τ : D.what₂.Tau)
    (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) (v : RW T S) (h1 : v τ = z) (h2 : ∀ τ', τ' ≠ τ → v τ' = 0) (t : ℝ) :
    lineAt θ τ z t = iotaW σ T S (t • v) := by
  have hL : IsLineAt θ τ z (lineAt θ τ z) :=
    Classical.epsilon_spec (GlobalTheory.RealLineAt.lineAt_exists D θ hσ.inf _ _ τ z)
  refine hσ.real_ext (V := T) (W := S) (hL.2.1 t) (hσ.real_iota T S _) ?_
  rw [hσ.pi_iota]
  funext τ'
  refine (hL.2.2 t τ').trans ?_
  by_cases h : τ' = τ
  · rw [if_pos h, h, Pi.smul_apply, h1]
    funext i j
    exact (Complex.real_smul).symm
  · rw [if_neg h, Pi.smul_apply, h2 τ' h, smul_zero]
    rfl

theorem exists_ne_zero (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ)
    (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ)
    (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (hS : ∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) (hT : ∀ τ, IsCartanInv (gramAt D T τ) (sT τ))
    (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E))
    (dS : IsSelfDualC S ΛS) (dT : IsSelfDualC T ΛT) :
    ∃ f : WO S T → ℂ, f ≠ 0 ∧ ∀ c : ℂ, IsThetaFunO ψ S T (fun w => c * f w) ∧
      IsLatVac (heisO ψ S T) (latO S T ΛS ΛT fun _ => True) (fun w => c * f w) ∧
      ∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) (fun w => c * f w) := by
  classical
  obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  obtain ⟨om, J, hom, hJ, halt, hJJ, hsym, hpos⟩ := GlobalTheory.T.exists_realPlace_symplecticForm_positiveComplexStructure D ψ θ S T sS sT hψ hθ hS hT
  obtain ⟨aL, aR, a0, -, acont, arat, -, -, -⟩ := GlobalTheory.T.homSymplecticHalfForm_algebraic_laws_continuous D S T
  obtain ⟨hinf, χ, c0, c1, c2, c3, c4, c5⟩ := GlobalTheory.T.exists_semicharacter_completedSelfDualLattice D S T ΛS ΛT ψ hψ dS dT
  have htop : IsTopologicalAddGroup (WO S T) := (GlobalTheory.AdelicMatrixLattice.lattice D T S).1
  set Λ : AddSubgroup (WO S T) := latO S T ΛS ΛT fun _ => True with hΛ
  have hp2 : ∀ u ∈ Λ, piW θ T S (2 • u) = 0 := fun u hu => by
    rw [map_nsmul, piW_eq_zero θ S T (hinf u hu), smul_zero]
  have hlev : ∀ u ∈ thick Λ 2, ∃ l ∈ Λ, u - iotaW σ T S (piW θ T S u) = 2 • l := by
    rintro u ⟨l, hl, hu⟩
    refine ⟨l, hl, ?_⟩
    have e := hσ.iota_pi (V := T) (W := S) (x := u - 2 • l) hu
    rw [map_sub, hp2 l hl, sub_zero] at e
    rw [e]
    abel
  obtain ⟨f, f0, fc, fq, fl, fs, fv⟩ := GlobalTheory.T.continuous_bicharacter_weil_setup (WO S T) (RW T S) (piW θ T S) (iotaW σ T S)
    (fun x y => ψ (symplOH S T x y)) om J (ratL T S) (thick Λ 1) (thick Λ 2) χ
    (continuous_pi' hθ T S) (hσ.continuous_iota T S) (hσ.pi_iota T S)
    (fun x y z => by simp only [aL, AddChar.map_add_eq_mul])
    (fun x y z => by simp only [aR, AddChar.map_add_eq_mul])
    (fun x => by simp only [a0, AddChar.map_zero_eq_one])
    (fun x y => hψ.1.2.1 _) (hψ.1.1.comp acont)
    (fun x v => by
      have e := hom x (iotaW σ T S v) (hσ.real_iota T S v)
      rw [hσ.pi_iota] at e
      exact e)
    halt hJJ hsym hpos
    (fun g hg g' hg' => by
      obtain ⟨a, ha⟩ := arat g hg g' hg'
      simp only [ha]
      exact hψ.1.2.2.1 a)
    (by
      rintro _ ⟨g, rfl⟩ h
      have : g = 0 := by
        funext i j
        have e : θ (D.eTau.symm 1) (infPart D (incA D (g i j))) = 0 :=
          congrFun (congrFun (congrFun h (D.eTau.symm 1)) i) j
        rw [comp_incA hθ] at e
        exact (tauE D _).injective (e.trans (RingHom.map_zero _).symm)
      rw [this, map_zero])
    (fun v => ⟨0, Λ.zero_mem, by rw [nsmul_zero, sub_zero]; exact hσ.real_iota T S v⟩)
    (fun R => by
      refine ((GlobalTheory.T.finite_rational_points_completed_lattice D S T ΛS ΛT dS dT R).image (ratW T S)).subset ?_
      rintro _ ⟨⟨g, rfl⟩, ⟨l, hl, h1⟩, h2⟩
      refine ⟨g, ⟨⟨l, hl, ?_⟩, fun τ i j => ?_⟩, rfl⟩
      · rw [one_nsmul] at h1
        exact h1
      · rw [← comp_incA hθ]
        let y : RW T S := piW θ T S (ratW T S g)
        exact ((norm_le_pi_norm (y τ i) j).trans ((norm_le_pi_norm (y τ) i).trans (norm_le_pi_norm y τ))).trans h2)
    (fun x hx => c0 x fun ⟨l, hl, h⟩ => hx ⟨l, hl, by rw [one_nsmul]; exact h⟩)
    c1 c2 (fun x v => c3 x _ (hσ.real_iota T S v))
    (GlobalTheory.T.isOpen_nsmul_completedHomLattice_finiteAdelic D S T ΛS ΛT dS dT 2 two_pos)
    (fun u hu x => by
      obtain ⟨l, hl, e⟩ := hlev u hu
      rw [e]
      exact c4 l hl x)
  have hh : ∀ (c : ℂ) (u : WO S T), piW θ T S u = 0 → (∀ x, ψ (symplOH S T x u) * χ (x + u) = χ x) →
      heisO ψ S T u (fun w => c * f w) = fun w => c * f w := fun c u h1 h2 => by
    funext w
    show ψ (symplOH S T w u) * (c * f (w + u)) = c * f w
    rw [mul_left_comm, ← fl u h1 h2 w]
  refine ⟨f, f0, fun c => ⟨⟨fun g w => ?_, ⟨thick Λ 2, GlobalTheory.T.isOpen_nsmul_completedHomLattice_finiteAdelic D S T ΛS ΛT dS dT 2 two_pos, fun u hu h => ?_⟩,
    continuous_const.mul fc, fun k L hL hL0 w => ?_⟩, ⟨fun u hu => hh c _ (hp2 u hu) (c4 u hu),
      fun e he u hu h => hh c u (piW_eq_zero θ S T (hinf u hu)) (c5 e he u hu h)⟩, fun τ z => ?_⟩⟩
  · have e : ψ (symplOH S T (ratW T S g) w) * f (ratW T S g + w) = f w := fq (ratW T S g) ⟨g, rfl⟩ w
    show c * f (ratW T S g + w) = _ * (c * f w)
    rw [← e, mul_left_comm, ← mul_assoc (ψ _), ← AddChar.map_add_eq_mul, neg_add_cancel,
      AddChar.map_zero_eq_one, one_mul]
  · obtain ⟨l, hl, e⟩ := hlev u hu
    rw [piW_eq_zero θ S T h, map_zero, sub_zero] at e
    rw [e]
    exact hh c _ (hp2 l hl) (c4 l hl)
  · exact contDiff_const.mul (((smooth_iff_sm_and_real_lines D θ σ hσ T S).1 f).2 fs k L hL hL0 w)
  · funext w
    let v : RW T S := Pi.single τ z
    have v1 : v τ = z := Pi.single_eq_same _ _
    have v2 : ∀ τ', τ' ≠ τ → v τ' = 0 := fun τ' h => Pi.single_eq_of_ne h _
    have l1 := lineAt_eq hσ S T τ z v v1 v2
    have l2 := lineAt_eq hσ S T τ (cplxO (sS τ) (sT τ) z) (J v) (by rw [hJ, v1]) (fun τ' h => by
      rw [hJ, v2 τ' h]
      have : cplxO (sS τ') (sT τ') (0 : Matrix (Fin T.rank) (Fin S.rank) ℂ) = 0 := by simp [cplxO]
      exact this)
    have e := fv w v
    show deriv (fun t : ℝ => ψ (symplOH S T w (lineAt θ τ z t)) * (c * f (w + lineAt θ τ z t))) 0 +
      Complex.I * deriv (fun t : ℝ => ψ (symplOH S T w (lineAt θ τ (cplxO (sS τ) (sT τ) z) t)) *
        (c * f (w + lineAt θ τ (cplxO (sS τ) (sT τ) z) t))) 0 = 0
    simp only [l1, l2, mul_left_comm _ c, deriv_const_mul_field']
    rw [← mul_add]
    exact mul_eq_zero_of_right c e

theorem vacExists : ∀ D : D7, VacExistsO D := by
  intro D ψ θ hψ hθ S T sS sT _ _ hS hT ΛS ΛT dS dT
  obtain ⟨f, f0, hf⟩ := exists_ne_zero ψ θ hψ hθ S T sS sT hS hT ΛS ΛT dS dT
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hcov⟩ := GlobalTheory.AdelicMatrixLattice.lattice D T S
  let _ : MeasurableSpace (WO S T) := measMx _ _
  have : BorelSpace (WO S T) := ⟨rfl⟩
  have h1 := (hf 1).1
  simp only [one_mul] at h1
  obtain ⟨⟨μ, 𝓕, hμ⟩, c, hc⟩ := GlobalTheory.T.exists_normalise_meanSquare_of_cocompact' (WO S T) (ratL T S) K hK hcov f h1.cont f0 (by
    rintro _ ⟨g, rfl⟩ w
    have e := h1.quasi g w
    have e' := congrArg norm e
    rw [norm_mul, hψ.1.2.1, one_mul] at e'
    exact e')
  exact ⟨fun w => c * f w, hψ, hθ, (hf c).1, (hf c).2.1, (hf c).2.2, ⟨(μ, 𝓕), hμ⟩,
    fun p hp => hc p.1 p.2 hp.1 hp.2.1 hp.2.2⟩

end GlobalTheory.VacuumO
end
