import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceDatumCarriedBackToBaseVacuum
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergFixAndKillThetaOffSupportMove
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PtYAndItYOfPair
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsGrowthSobNeTopOfIsAutFunSm
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StrongApproximationDecomposition
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCompactAdele
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsSelfDualLatticeAtPlaceComapUnitarySupported
import Formalism.LocalToGlobal.NumberFieldFamilies.ThetaCX
import Development.AutomorphicSpectrum.Proofs.TwistedProofs.NormDetLeFactorialMulProd

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped Pointwise TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Grid GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle GlobalTheory.ConstRatio

noncomputable section
namespace GlobalTheory.CompanionTheory.Ipf.Bdd
variable {D : D7}

def _root_.GlobalTheory.CompanionTheory.Ipf.mul {a b c : ℕ} (x : Mx D a b) (y : Mx D b c) : Mx D a c :=
  HMul.hMul (x : Matrix (Fin a) (Fin b) (AE D)) (y : Matrix (Fin b) (Fin c) (AE D))

def _root_.GlobalTheory.CompanionTheory.Ipf.rat {a b : ℕ} (γ : Matrix (Fin a) (Fin b) D.host.E) : Mx D a b := γ.map (incA D)

theorem infPart_incA (c : D.host.E) : infPart D (incA D c) = (1 : Ainf D.host.F) ⊗ₜ[D.host.F] c := by
  simp [infPart, incA, inclR]

theorem infPart_cA (z : AE D) : infPart D (cA D z) = sigR (Ainf D.host.F) D.sp.cm.sig (infPart D z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem compAt_mulM {m k n : ℕ} (θ : InfFam D) (τ : D.what₂.Tau) (A : Mx D m k) (B : Mx D k n) :
    compAt θ τ (mul A B) = compAt θ τ A * compAt θ τ B := by
  unfold compAt mul
  exact Matrix.map_mul (f := (θ τ).comp (infPart D))

theorem compAt_rat {m k : ℕ} {θ : InfFam D} (hθ : IsInfFam θ) (τ : D.what₂.Tau) (γ : Matrix (Fin m) (Fin k) D.host.E) :
    compAt θ τ (rat γ) = γ.map (tauE D τ) := by
  ext i j
  simp only [compAt, rat, Matrix.map_apply]
  rw [infPart_incA]
  exact (hθ τ).1 _

theorem norm_det_compAt {θ : InfFam D} (hθ : IsInfFam θ) (τ : D.what₂.Tau) (V : HSp D) (g : GA D V) :
    ‖(compAt θ τ (mt V g)).det‖ = 1 := by
  have h : ((mt V g).map (cA D))ᵀ * V.gram.map (incA D) * mt V g = V.gram.map (incA D) := g.2
  set ρ : AE D →+* ℂ := (θ τ).comp (infPart D) with hρ
  have hc : ∀ z, ρ (cA D z) = starRingEnd ℂ (ρ z) := fun z => by
    simp only [hρ, RingHom.comp_apply]
    rw [infPart_cA]
    exact GlobalTheory.Mem.VolExists.infEmb_sigR (GlobalTheory.DefiniteQuotient.cmExt D) (hθ τ) _
  have hd := congrArg (fun M => ρ M.det) h
  simp only [Matrix.det_mul, Matrix.det_transpose, map_mul] at hd
  have e1 : ρ (((mt V g).map (cA D)).det) = starRingEnd ℂ (ρ (mt V g).det) := by
    rw [← hc]
    congr 1
    exact ((cA D).map_det _).symm
  have e2 : ρ (V.gram.map (incA D)).det ≠ 0 := by
    have : (V.gram.map (incA D)).det = incA D V.gram.det := ((incA D).map_det _).symm
    rw [this]
    have : ρ (incA D V.gram.det) = tauE D τ V.gram.det := by
      simp only [hρ, RingHom.comp_apply]
      rw [infPart_incA]
      exact (hθ τ).1 _
    rw [this]
    exact (map_ne_zero _).2 (GlobalTheory.StabCompact.det_gram_ne_zero V)
  have e3 : (compAt θ τ (mt V g)).det = ρ (mt V g).det := (ρ.map_det _).symm
  rw [e3]
  rw [e1] at hd
  have h4 : starRingEnd ℂ (ρ (mt V g).det) * ρ (mt V g).det = 1 := by
    refine mul_right_cancel₀ e2 ?_
    calc _ = starRingEnd ℂ (ρ (mt V g).det) * ρ (V.gram.map (incA D)).det * ρ (mt V g).det := by ring
      _ = ρ (V.gram.map (incA D)).det := hd
      _ = _ := by ring
  rw [Complex.conj_mul'] at h4
  have h5 : (‖ρ (mt V g).det‖ : ℝ) ^ 2 = 1 := by exact_mod_cast h4
  have h6 : (0 : ℝ) ≤ ‖ρ (mt V g).det‖ := norm_nonneg _
  nlinarith [sq_nonneg (‖ρ (mt V g).det‖ - 1), sq_nonneg (‖ρ (mt V g).det‖ + 1)]

theorem isOpen_nsmul_mem (N : ℕ) :
    IsOpen {y : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E | N • y ∈ intAE D} := by
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.StabFin.addGrpF (F := D.host.F) (E := D.host.E)
  have h1 : IsOpen {z : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E | z ∈ intAE D} := by
    have := GlobalTheory.IdeleParts.isOpen_nsmul_adelicCompletion_integers D.host.F D.host.E 1 one_pos
    rw [← GlobalTheory.IdeleParts.integralFiniteAdeles_eq_adelicCompletion_integers] at this
    have e : {z : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E | z ∈ intAE D} = {z | ∃ y ∈ intAE D, z = 1 • y} := by
      ext z
      simp
    rw [e]
    exact this
  exact h1.preimage (continuous_nsmul N)

theorem den_one (z : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) : ∃ N : ℕ, 0 < N ∧ N • z ∈ intAE D := by
  obtain ⟨n, hn, h⟩ := GlobalTheory.IwaPlace.SdComap.exists_natCast_mul_mem_intAE (D := D) z
  exact ⟨n, hn, by rwa [nsmul_eq_mul]⟩

theorem exists_den {K : Set (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)} (hK : IsCompact K) :
    ∃ N : ℕ, 0 < N ∧ ∀ x ∈ K, N • x ∈ intAE D := by
  refine hK.induction_on (p := fun S => ∃ N : ℕ, 0 < N ∧ ∀ x ∈ S, N • x ∈ intAE D)
    ⟨1, one_pos, by simp⟩ ?_ ?_ ?_
  · rintro s t hst ⟨N, hN, h⟩
    exact ⟨N, hN, fun x hx => h x (hst hx)⟩
  · rintro s t ⟨N, hN, h⟩ ⟨M, hM, h'⟩
    refine ⟨N * M, by positivity, ?_⟩
    rintro x (hx | hx)
    · rw [mul_comm, mul_smul]
      exact AddSubgroup.nsmul_mem _ (h x hx) M
    · rw [mul_smul]
      exact AddSubgroup.nsmul_mem _ (h' x hx) N
  · intro x _
    obtain ⟨N, hN, hx⟩ := den_one x
    exact ⟨_, mem_nhdsWithin_of_mem_nhds ((isOpen_nsmul_mem N).mem_nhds hx), N, hN, fun y hy => hy⟩

def intR (D : D7) : Subring D.host.E := (algebraMap (𝓞 D.host.E) D.host.E).range

theorem mem_intR_of_finPart {a : D.host.E} (h : finPart D (incA D a) ∈ intAE D) : a ∈ intR D := by
  have h1 := (GlobalTheory.SplitDec.rat_int_iff (D := D) a).1 ((GlobalTheory.SplitDec.int_iff _).1 h)
  obtain ⟨y, hy⟩ := Submodule.mem_one.1 h1
  exact ⟨y, hy⟩

theorem one_le_prod_tauE (z : D.host.E) (hz : z ∈ intR D) (h0 : z ≠ 0) : 1 ≤ ∏ τ, ‖tauE D τ z‖ := by
  obtain ⟨r, rfl⟩ := hz
  have h1 := NumberField.InfinitePlace.prod_eq_abs_norm (algebraMap (𝓞 D.host.E) D.host.E r)
  have hb := Formalism.L2.Fam.ThC.plE_bij D
  have h2 : ∏ w : InfinitePlace D.host.E, w (algebraMap (𝓞 D.host.E) D.host.E r) ^ w.mult =
      ∏ τ, ‖tauE D τ (algebraMap (𝓞 D.host.E) D.host.E r)‖ ^ 2 := by
    rw [← hb.prod_comp]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [InfinitePlace.mult, if_neg (by simpa [InfinitePlace.isComplex_iff] using Formalism.L2.Fam.ThC.plE_complex τ)]
    rfl
  have hr : r ≠ 0 := fun e => h0 (by rw [e, map_zero])
  have h3 : (1 : ℝ) ≤ |((Algebra.norm ℚ (algebraMap (𝓞 D.host.E) D.host.E r) : ℚ) : ℝ)| := by
    have e := Algebra.coe_norm_int r
    have hn : Algebra.norm ℤ r ≠ 0 := Algebra.norm_ne_zero_iff.2 hr
    have e' : (algebraMap (𝓞 D.host.E) D.host.E r) = (r : D.host.E) := rfl
    rw [e', ← e]
    have : (1 : ℤ) ≤ |Algebra.norm ℤ r| := Int.one_le_abs hn
    have h' : ((1 : ℤ) : ℝ) ≤ ((|Algebra.norm ℤ r| : ℤ) : ℝ) := by exact_mod_cast this
    simpa using h'
  have h4 : (1 : ℝ) ≤ (∏ τ, ‖tauE D τ (algebraMap (𝓞 D.host.E) D.host.E r)‖) ^ 2 := by
    rw [← Finset.prod_pow, ← h2, h1]
    exact_mod_cast h3
  have h5 : (0 : ℝ) ≤ ∏ τ, ‖tauE D τ (algebraMap (𝓞 D.host.E) D.host.E r)‖ :=
    Finset.prod_nonneg fun _ _ => norm_nonneg _
  nlinarith

theorem mul_mem_int {x y : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E} (hx : x ∈ intAE D) (hy : y ∈ intAE D) :
    x * y ∈ intAE D := by
  rw [GlobalTheory.IdemSupport.mem_intAE_iff] at *
  rw [map_mul]
  exact mul_mem hx hy

theorem exists_den_matrix {a b : ℕ}
    {K : Set (Matrix (Fin a) (Fin b) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E))} (hK : IsCompact K) :
    ∃ N : ℕ, 0 < N ∧ ∀ m ∈ K, ∀ i j, N • m i j ∈ intAE D := by
  have h : ∀ p : Fin a × Fin b, ∃ N : ℕ, 0 < N ∧ ∀ x ∈ (fun m : Matrix (Fin a) (Fin b) _ => m p.1 p.2) '' K, N • x ∈ intAE D :=
    fun p => exists_den (hK.image (continuous_id.matrix_elem p.1 p.2))
  choose N hN h using h
  refine ⟨∏ p, N p, Finset.prod_pos fun p _ => hN p, fun m hm i j => ?_⟩
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ (i, j)), mul_comm, mul_smul]
  exact AddSubgroup.nsmul_mem _ (h (i, j) _ ⟨m, hm, rfl⟩) _

theorem nonempty_tau (D : D7) : Nonempty D.what₂.Tau := ⟨D.eTau.symm (Classical.arbitrary _)⟩

end GlobalTheory.CompanionTheory.Ipf.Bdd

end
