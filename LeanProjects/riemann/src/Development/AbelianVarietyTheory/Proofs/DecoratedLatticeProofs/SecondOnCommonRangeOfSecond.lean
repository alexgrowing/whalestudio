import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.AdelicConjTransposeBlockMatrixTwoByTwoFin
import Development.AbelianVarietyTheory.BlockTheory.SiegelEisenstein.GramMatrixAdjoint
import Development.AbelianVarietyTheory.Definitions.Foundations.MemL2OfBoundedContinuousInvariant
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsSchwartzBruhatAdelicMatrixOfMemAdelicSchwartz
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchwartzBruhatAdelicMatrixContinuousLeMajorantStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSummableBoundSchwartzMajorantRationalTransStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualOfCovolumeOneStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RationalAdelicMatricesSelfAnnihilatorStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IwasawaDecompositionUnitary
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryUnnSubgroupEqTopOfLeviUnipotentWeylStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelParabolicUnnMatrixBlockUpperTriangular

noncomputable section
open scoped Matrix NNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SiegelWeilLitCompare

open GlobalTheory.StdUnn GlobalTheory.StdUnn.Model
open GlobalTheory.IndefiniteRowSideFullHecke
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

variable {D : D7} {n : ℕ}

theorem summable_rat {θ : InfFam D} (hθ : IsInfFam θ) {m : ℕ} (φ : schwartzA θ m n) :
    Summable fun ξ : Matrix (Fin m) (Fin n) D.host.E => ‖φ.1 (ξ.map (incA D))‖ := by
  obtain ⟨N, hN⟩ := GlobalTheory.T.exists_summable_bound_schwartz_majorant_rational_translates D θ hθ m n
  obtain ⟨-, K, hK, hC⟩ := GlobalTheory.T.schwartzBruhatAdelicMatrix_continuous_le_majorant D θ hθ m n φ.1
    (GlobalTheory.SchwartzPure.isSchwartzBruhat_of_mem_schwartzA D θ hθ m n φ.1 φ.2)
  obtain ⟨C, hC⟩ := hC N
  obtain ⟨b, hb, hb'⟩ := hN K {0} hK isCompact_singleton
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun ξ => (hC _).trans ?_) (hb.mul_left |C|)
  have := hb' 0 rfl ξ
  rw [zero_add] at this
  exact mul_le_mul (le_abs_self C) this (GlobalTheory.Unf.maj_nonneg _ _ _ _) (abs_nonneg C)

theorem gramQ_adj {m : ℕ} {T : Matrix (Fin m) (Fin m) D.host.E} (hT : IsHermND D.sp.cm.sig T) (x y : Mx D m n) :
    adj (GramMatrixBlocks.gramQ T x y) = GramMatrixBlocks.gramQ T y x := by
  have h : adj (rat T : Mx D m m) = rat T := by
    ext i j
    exact (GlobalTheory.DualPairCheck.cA_incA _).trans (congrArg (incA D) (hT.1 i j))
  change adj ((adj x ⬝ (rat T : Mx D m m)) ⬝ y) = (adj y ⬝ (rat T : Mx D m m)) ⬝ x
  rw [adj_mul, adj_mul, adj_adj, h, Matrix.mul_assoc]

theorem selfDual_of_covolOne {m : ℕ} {T : Matrix (Fin m) (Fin m) D.host.E} (hT : IsHermND D.sp.cm.sig T)
    {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) {μ : Measure (Mx D m n)} {𝓕 : Set (Mx D m n)}
    (hμ : IsCovolOne (ratMx D m n) μ 𝓕) : SelfDual μ (GramMatrixBlocks.pairing (n := n) T ψ) := by
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hKc⟩ := lattice_Mx D m n
  haveI : BorelSpace (Mx D m n) := ⟨rfl⟩
  obtain ⟨h1, h2⟩ := GlobalTheory.T.rationalAdelicMatrices_self_annihilator D m n T hT ψ hψ
  have hs : ∀ x y : Mx D m n, GramMatrixBlocks.pairing T ψ x y = GramMatrixBlocks.pairing T ψ y x := fun x y => by
    unfold GramMatrixBlocks.pairing GramMatrixBlocks.trA
    rw [← gramQ_adj hT x y, ← GlobalTheory.DualPairCheck.trace_cA (Matrix.trace (GramMatrixBlocks.gramQ T x y))]
    congr 2
    simp only [Matrix.trace, map_sum]
    rfl
  refine GlobalTheory.T.selfDual_of_fundamentalDomain_volume_eq_one _ (ratMx D m n) K hK hKc _ (fun y => ?_) hs (fun x x' y => ?_) (fun x y => hψ.2.1 _) h1 h2 μ 𝓕
    hμ.1 hμ.2.1 hμ.2.2
  · simp only [hs _ y]
    haveI := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
    haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
    have ht : Continuous (GramMatrixBlocks.trA (D := D)) :=
      IsModuleTopology.continuous_of_linearMap (Algebra.trace (AF D.host.F) (AE D))
    exact hψ.1.comp (ht.comp (continuous_const.matrix_mul continuous_id).matrix_trace)
  · simp only [hs _ y]
    unfold GramMatrixBlocks.pairing GramMatrixBlocks.trA GramMatrixBlocks.gramQ GramMatrixBlocks.mmul
    rw [Matrix.mul_add, Matrix.trace_add, map_add, AddChar.map_add_eq_mul]

theorem mem_siegelParabolic_of_lowerLeft_entries_eq_zero {g : G D n}
    (h : ∀ i j, mat g (finSumFinEquiv (.inr i)) (finSumFinEquiv (.inl j)) = 0)
    (h' : ∀ i j, mat g⁻¹ (finSumFinEquiv (.inr i)) (finSumFinEquiv (.inl j)) = 0) : g ∈ P D n := by
  have key : ∀ g : G D n, (∀ i j, mat g (finSumFinEquiv (.inr i)) (finSumFinEquiv (.inl j)) = 0) →
      ∀ x ∈ upperHalf D n, (mat g).mulVec x ∈ upperHalf D n := by
    intro g h x hx
    ext i
    have hx' : ∀ j, x (finSumFinEquiv (Sum.inr j : Fin n ⊕ Fin n)) = 0 := fun j => congrFun hx j
    simp only [LinearMap.funLeft_apply, Matrix.mulVec, dotProduct, Pi.zero_apply]
    rw [← finSumFinEquiv.sum_comp, Fintype.sum_sum_type]
    simp only [h, hx', zero_mul, mul_zero, Finset.sum_const_zero, add_zero]
  refine fun x => ⟨key g h x, fun hx => ?_⟩
  have := key _ h' _ hx
  change (mat g⁻¹).mulVec ((mat g).mulVec x) ∈ _ at this
  rwa [Matrix.mulVec_mulVec, show mat g⁻¹ * mat g = mat (g⁻¹ * g) from rfl, inv_mul_cancel,
    show mat (1 : G D n) = 1 from rfl, Matrix.one_mulVec] at this

theorem siegel_eq : GramMatrixBlocks.siegel D n = P D n := by
  have lower : ∀ g : G D n, g ∈ GramMatrixBlocks.siegel D n →
      ∀ i j, mat g (finSumFinEquiv (.inr i)) (finSumFinEquiv (.inl j)) = 0 := fun g hg i j =>
    hg (by simp [GramMatrixBlocks.blockIdx])
  ext g
  refine ⟨fun hg => mem_siegelParabolic_of_lowerLeft_entries_eq_zero (lower g hg) (lower _ ((GramMatrixBlocks.siegel D n).inv_mem hg)), fun hg i j hij => ?_⟩
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
  rcases i with i | i <;> rcases j with j | j
  · simp [GramMatrixBlocks.blockIdx] at hij
  · simp [GramMatrixBlocks.blockIdx] at hij
  · exact lower_eq_zero hg i j
  · simp [GramMatrixBlocks.blockIdx] at hij

theorem hE_equivFun (V : HSp D) (x y : V.V) :
    hE D.sp.cm.sig V.gram (V.frame.equivFun x) (V.frame.equivFun y) = V.hT x y := by
  conv_rhs => rw [← V.frame.sum_equivFun x, ← V.frame.sum_equivFun y]
  simp only [hE, Formalism.UG.hform, HSpace.gram, map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ₂, map_smul, smul_eq_mul,
    LinearMap.smul_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  change star _ * _ * _ = _ * (star _ * _)
  ring

theorem wittIdx_eq (V : HSp D) : GramMatrixBlocks.wittIdx V.gram = Formalism.MainNotions.SchurIrreducible.wittIdx V := by
  unfold GramMatrixBlocks.wittIdx Formalism.MainNotions.SchurIrreducible.wittIdx
  refine congrArg sSup (Set.ext fun r => ⟨?_, ?_⟩)
  · rintro ⟨W, hW, hr⟩
    refine ⟨W.map V.frame.equivFun.symm.toLinearMap, (LinearEquiv.finrank_map_eq V.frame.equivFun.symm W).trans hr, ?_⟩
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    refine (hE_equivFun V _ _).symm.trans ?_
    rw [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
    exact hW x hx y hy
  · rintro ⟨W, hr, hW⟩
    refine ⟨W.map V.frame.equivFun.toLinearMap, ?_, (LinearEquiv.finrank_map_eq V.frame.equivFun W).trans hr⟩
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    exact (hE_equivFun V x y).trans (hW x hx y hy)

variable {V : HSp D} {θ : InfFam D} {ψ : AddChar (AF D.host.F) ℂ} {χ : (AE D)ˣ →* Circle}

theorem gramQ_eq (x y : Mx D V.rank n) : GramMatrixBlocks.gramQ V.gram x y = StdUnn.inner V x y := Matrix.mul_assoc _ _ _

def resG (ω : GramMatrixBlocks.Rep θ n V.gram) : G D n →* Module.End ℂ (schwartzA θ V.rank n) := ω.comp (MonoidHom.inl _ _)

theorem isWeilSch_unique {μ : Measure (Mx D V.rank n)} {ω ω' : G D n →* Module.End ℂ (schwartzA θ V.rank n)}
    (h : IsWeilSch ψ χ θ V μ ω) (h' : IsWeilSch ψ χ θ V μ ω') : ω = ω' := by
  have := GlobalTheory.T.unitaryUnn_subgroup_eq_top_of_leviUnipotentWeyl D n (ω.toHomUnits.eqLocus ω'.toHomUnits)
    (fun g a hg => Units.ext (LinearMap.ext fun Φ => Subtype.ext (funext fun x =>
      (h.levi g a hg Φ x).trans (h'.levi g a hg Φ x).symm)))
    (fun g b hg => Units.ext (LinearMap.ext fun Φ => Subtype.ext (funext fun x =>
      (h.unip g b hg Φ x).trans (h'.unip g b hg Φ x).symm)))
    (fun g hg => Units.ext (LinearMap.ext fun Φ => Subtype.ext (funext fun x =>
      (h.weyl g hg Φ x).trans (h'.weyl g hg Φ x).symm)))
  refine MonoidHom.ext fun g => ?_
  have hg : g ∈ ω.toHomUnits.eqLocus ω'.toHomUnits := this ▸ Subgroup.mem_top g
  exact congrArg Units.val hg

theorem sect_eq (ω : GramMatrixBlocks.Rep θ n V.gram) (H : G D n → ℝ≥0) (Φ : schwartzA θ V.rank n) (z : ℂ) :
    GramMatrixBlocks.sect H ω Φ z = sect (resG ω) H Φ z := rfl

theorem summable_iff (ω : GramMatrixBlocks.Rep θ n V.gram) (H : G D n → ℝ≥0) (Φ : schwartzA θ V.rank n) (g : G D n) (z : ℂ) :
    (Summable fun γ => ‖GramMatrixBlocks.eisTerm H ω Φ g z γ‖) ↔ Eis.CosetConv (P D n) (GF D n) (sect (resG ω) H Φ z) g := by
  rw [← siegel_eq]
  rfl

theorem tsum_eq (ω : GramMatrixBlocks.Rep θ n V.gram) (H : G D n → ℝ≥0) (Φ : schwartzA θ V.rank n) (g : G D n) (z : ℂ) :
    ∑' γ, GramMatrixBlocks.eisTerm H ω Φ g z γ = Eis.cosetSum (P D n) (GF D n) (sect (resG ω) H Φ z) g := by
  rw [← siegel_eq]
  rfl

theorem leftInv_theta (ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)) (Φ : schwartzA θ V.rank n) (g : G D n) :
    LeftInv (GQ V) (theta ω Φ g) := by
  intro γ hγ h
  obtain ⟨u, hu⟩ : ∃ u : GL (Fin V.rank) D.host.E, mt V γ⁻¹ = rat u.1 := by
    obtain ⟨u, -, hu⟩ := (GQ V).inv_mem hγ
    exact ⟨u, (congrArg Units.val hu).symm⟩
  let e : Matrix (Fin V.rank) (Fin n) D.host.E ≃ Matrix (Fin V.rank) (Fin n) D.host.E :=
    ⟨fun ξ => u.1 * ξ, fun ξ => (u⁻¹).1 * ξ, fun ξ => by simp [← Matrix.mul_assoc], fun ξ => by simp [← Matrix.mul_assoc]⟩
  refine (tsum_congr fun ξ => ?_).trans (e.tsum_eq _)
  have : mt V (γ * h)⁻¹ = mt V h⁻¹ * mt V γ⁻¹ := by rw [mul_inv_rev]; rfl
  rw [this, hu, Matrix.mul_assoc, ← rat_mul]
  rfl

def ContinuesAt {m : ℕ} {T : Matrix (Fin m) (Fin m) D.host.E} (α : GramMatrixBlocks.GG D n → ℝ≥0) (ω : GramMatrixBlocks.Rep θ n T)
    (Φ : GramMatrixBlocks.Sch θ m n) (g : GramMatrixBlocks.GG D n) : Prop :=
  ∃ E : ℂ → ℂ, MeromorphicOn E Set.univ ∧ ∀ s : ℂ, (n : ℝ) / 2 < s.re → E s = ∑' γ, GramMatrixBlocks.eisTerm α ω Φ g s γ

def SecondOnCommonRange : Prop :=
  ∀ (D : D7) (n : ℕ) (V : HSp D), n < V.rank → V.rank ≤ 2 * n → n + Formalism.MainNotions.SchurIrreducible.wittIdx V < V.rank →
    GramMatrixBlocks.FormulaFor n V.gram

def WeilExists : Prop :=
  ∀ (D : D7) (n : ℕ) (V : HSp D), n < V.rank → V.rank ≤ 2 * n → n + Formalism.MainNotions.SchurIrreducible.wittIdx V < V.rank →
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (χ : (AE D)ˣ →* Circle) (θ : InfFam D),
    IsCharAF D.host.F ψ → IsHeckeChar D χ → ResEta D χ V.rank → IsInfFam θ →
    ∃ ω : GramMatrixBlocks.Rep θ n V.gram, GramMatrixBlocks.IsWeil ψ χ ω

def PlaneContinuation : Prop :=
  ∀ (D : D7) (n : ℕ) (V : HSp D), n < V.rank → V.rank ≤ 2 * n → n + Formalism.MainNotions.SchurIrreducible.wittIdx V < V.rank →
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (χ : (AE D)ˣ →* Circle) (θ : InfFam D),
    IsCharAF D.host.F ψ → IsHeckeChar D χ → ResEta D χ V.rank → IsInfFam θ →
  ∀ ω : GramMatrixBlocks.Rep θ n V.gram, GramMatrixBlocks.IsWeil ψ χ ω → ∀ α : GramMatrixBlocks.GG D n → ℝ≥0, GramMatrixBlocks.IsAbsLevi α →
  ∀ c : D.what₂.Tau → ℝ, GramMatrixBlocks.IsRealPart ψ θ c →
  ∀ s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ, (∀ τ, IsCartanInv (V.gram.map (tauE D τ)) (s τ)) →
  ∀ Φ : GramMatrixBlocks.Sch θ V.rank n, Φ.1 ∈ GramMatrixBlocks.fockSpace θ n V.gram c s → ∀ g, ContinuesAt α ω Φ g

end GlobalTheory.SiegelWeilLitCompare

end
