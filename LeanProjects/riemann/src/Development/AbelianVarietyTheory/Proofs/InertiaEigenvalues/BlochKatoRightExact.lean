import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TensorFundamentalExactSequenceCrystallineStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBlochKatoCocycleOfCrysDeRhamPairStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineCoboundaryLiftStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsDeRhamOfIsCrystallineSpan
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OfShortExact
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamSubrepQuotientAndStrictness

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.BKRightExact

section Generic

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']

section Res

variable (L : Type) [Field L] [Algebra Qp L] [Algebra L LL] [Module L V] [IsScalarTower L LL V]
  [IsScalarTower Qp L V] (ρ : Representation LL G V)

def res : Representation L G V where
  toFun g := (ρ g).restrictScalars L
  map_one' := by ext; simp
  map_mul' g h := by ext; simp

theorem Dcris_res : Dcris PD (res L ρ) = (Dcris PD ρ).restrictScalars L := by
  ext x
  simp only [Dcris, Submodule.restrictScalars_mem, Submodule.mem_iInf, LinearMap.mem_ker,
    LinearMap.sub_apply, LinearMap.id_apply]
  rfl

theorem DdR_res : DdR PD (res L ρ) = (DdR PD ρ).restrictScalars L := by
  ext x
  simp only [DdR, Submodule.restrictScalars_mem, Submodule.mem_iInf, LinearMap.mem_ker,
    LinearMap.sub_apply, LinearMap.id_apply]
  rfl

theorem isCrys_res (h : IsCrys PD ρ) : IsCrys PD (res L ρ) := by
  unfold IsCrys at h ⊢
  rw [Dcris_res]
  change finrank L ↥(Dcris PD ρ) = _
  rw [← Module.finrank_mul_finrank L LL ↥(Dcris PD ρ), ← Module.finrank_mul_finrank L LL V, h,
    mul_left_comm]

theorem isDR_of_res [FiniteDimensional L LL] (h : IsDR PD (res L ρ)) : IsDR PD ρ := by
  unfold IsDR at h ⊢
  rw [DdR_res] at h
  change finrank L ↥(DdR PD ρ) = _ at h
  rw [← Module.finrank_mul_finrank L LL ↥(DdR PD ρ), ← Module.finrank_mul_finrank L LL V,
    mul_left_comm] at h
  exact Nat.eq_of_mul_eq_mul_left Module.finrank_pos h

end Res

variable (f : V →ₗ[LL] V')

theorem map_φVB (x : V ⊗[Qp] B) :
    AlgebraTensorModule.map f (LinearMap.id : B →ₗ[Qp] B) (φVB PD (LL := LL) x) =
      φVB PD (LL := LL) (AlgebraTensorModule.map f (LinearMap.id : B →ₗ[Qp] B) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [φVB]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem map_ιV (x : V ⊗[Qp] B) :
    AlgebraTensorModule.map f (LinearMap.id : BdR →ₗ[Qp] BdR) (ιV PD (LL := LL) x) =
      ιV PD (LL := LL) (AlgebraTensorModule.map f (LinearMap.id : B →ₗ[Qp] B) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [ιV]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem map_mem_FilV {a : ℤ} {y : V ⊗[Qp] BdR} (hy : y ∈ FilV PD (LL := LL) (V := V) a) :
    AlgebraTensorModule.map f (LinearMap.id : BdR →ₗ[Qp] BdR) y ∈ FilV PD (LL := LL) (V := V') a := by
  obtain ⟨z, rfl⟩ := hy
  refine ⟨AlgebraTensorModule.map f LinearMap.id z, ?_⟩
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp
  | add x y hx hy => simp only [map_add, hx, hy]

theorem map_actVB {ρ : Representation LL G V} {ρ' : Representation LL G V'}
    (hf : ∀ g x, f (ρ g x) = ρ' g (f x)) (g : G) (x : V ⊗[Qp] B) :
    AlgebraTensorModule.map f (LinearMap.id : B →ₗ[Qp] B) (actVB PD ρ g x) =
      actVB PD ρ' g (AlgebraTensorModule.map f (LinearMap.id : B →ₗ[Qp] B) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [actVB, hf]
  | add x y hx hy => simp only [map_add, hx, hy]

include PD in
theorem tmul_one_injective {v w : V} (h : v ⊗ₜ[Qp] (1 : B) = w ⊗ₜ[Qp] (1 : B)) : v = w := by
  have h1 : (1 : B) ≠ 0 := fun h0 => PD.not_mem_filtration_two (by
    rw [← mul_one PD.t, h0, mul_zero, map_zero]; exact Submodule.zero_mem _)
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_eq_one Qp h1
  have := congrArg (fun z => TensorProduct.rid Qp V (LinearMap.lTensor V φ z)) h
  simpa [hφ] using this

end Generic

theorem lift_periods {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} (T : LocTied l P AI)
    (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [FiniteDimensional ℚ_[l] LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V]
    [FiniteDimensional LL V] (ρ : Representation LL ↥(GK K) V)
    {V' : Type} [AddCommGroup V'] [Module LL V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] LL V']
    [FiniteDimensional LL V'] (ρ' : Representation LL ↥(GK K) V') (f : V →ₗ[LL] V')
    (hf : ∀ g x, f (ρ g x) = ρ' g (f x)) (hs : Function.Surjective f) (h : IsCrys (P.PD K) ρ) :
    IsDR (P.PD K) ρ' ∧
      (∀ y ∈ Dcris (P.PD K) ρ', ∃ x ∈ Dcris (P.PD K) ρ,
        AlgebraTensorModule.map f (LinearMap.id : P.R.B →ₗ[ℚ_[l]] P.R.B) x = y) ∧
      ∀ y ∈ DdR (P.PD K) ρ', ∃ x ∈ DdR (P.PD K) ρ,
        AlgebraTensorModule.map f (LinearMap.id : P.R.BdR →ₗ[ℚ_[l]] P.R.BdR) x = y := by
  let L : FinExt l := ⟨⊥, inferInstance⟩
  letI : Algebra ↥L.1 LL :=
    ((algebraMap ℚ_[l] LL).comp (IntermediateField.botEquiv ℚ_[l] (Om l)).toRingEquiv.toRingHom).toAlgebra
  haveI : IsScalarTower ℚ_[l] ↥L.1 LL := IsScalarTower.of_algebraMap_eq fun x =>
    (congrArg (algebraMap ℚ_[l] LL) ((IntermediateField.botEquiv ℚ_[l] (Om l)).commutes x)).symm
  haveI : FiniteDimensional ↥L.1 LL := Module.Finite.of_restrictScalars_finite ℚ_[l] _ _
  letI : Module ↥L.1 V := Module.compHom V (algebraMap ↥L.1 LL)
  letI : Module ↥L.1 V' := Module.compHom V' (algebraMap ↥L.1 LL)
  haveI : IsScalarTower ↥L.1 LL V := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  haveI : IsScalarTower ↥L.1 LL V' := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  haveI : IsScalarTower ℚ_[l] ↥L.1 V := IsScalarTower.to₁₂₄ ℚ_[l] ↥L.1 LL V
  haveI : IsScalarTower ℚ_[l] ↥L.1 V' := IsScalarTower.to₁₂₄ ℚ_[l] ↥L.1 LL V'
  haveI : FiniteDimensional ↥L.1 V := Module.Finite.trans LL V
  haveI : FiniteDimensional ↥L.1 V' := Module.Finite.trans LL V'
  have hc := isCrys_res (P.PD K) ↥L.1 ρ h
  have hd := (GlobalTheory.Per.CrisDR.isDR_of_isCrys l P AI T K L V _ hc).1
  obtain ⟨-, h1⟩ := (GlobalTheory.Per.CrysSubQuot.crys_sub_quot l P AI T K L V (res ↥L.1 ρ) V' (res ↥L.1 ρ')
    (f.restrictScalars ↥L.1) hf).2 hs hc
  obtain ⟨h2, h3⟩ := (GlobalTheory.DRSubQuot.deRham_sub_quot l P AI T K L V (res ↥L.1 ρ) V' (res ↥L.1 ρ')
    (f.restrictScalars ↥L.1) hf).2 hs hd
  rw [Dcris_res, Dcris_res] at h1
  rw [DdR_res, DdR_res] at h3
  refine ⟨isDR_of_res (P.PD K) ↥L.1 ρ' h2, h1, fun y hy => ?_⟩
  obtain ⟨a, ha⟩ := GlobalTheory.DRFil.exists_mem_FilV (P.PD K) (LL := ↥L.1) y
  obtain ⟨x, hx, hxy⟩ := h3 a y ⟨hy, ha⟩
  exact ⟨x, hx.1, hxy⟩

theorem bkARightExact_of_tied : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ K : FinExt l, Formalism.MainNotions.LocalSituation.bkARightExact (P.PD K) := by
  intro l _ P AI T K LL _ _ _ O _ _ hO A A' f hf hs hA _ c' hc'
  haveI := hO.2.1
  obtain ⟨hdr, hl1, hl2⟩ := lift_periods T K LL A.ρ A'.ρ f hf hs hA
  obtain ⟨-, x', hx'⟩ := hc'
  obtain ⟨hd1, d₂', hd2, hfil⟩ := GlobalTheory.T.crystalline_coboundary_lift l P AI T K LL O hO A' hdr c' x' hx'
  obtain ⟨d₁, hd₁, e₁⟩ := hl1 _ hd1
  obtain ⟨d₂, hd₂, e₂⟩ := hl2 _ hd2
  obtain ⟨x, y, c, hy, hx1, hx2, hc, hcx⟩ := GlobalTheory.T.exists_blochKato_cocycle_of_crys_deRham_pair l P AI T K LL O hO A d₁ hd₁ d₂ hd₂
  refine ⟨c, hc, ?_⟩
  rw [← hx1, map_sub, map_φVB] at e₁
  rw [← hx2, map_sub, map_ιV] at e₂
  obtain ⟨v, hv⟩ := (GlobalTheory.T.tensor_fundamental_exact_sequence_crystalline l P AI T K LL A'.V).2
    (AlgebraTensorModule.map f (LinearMap.id : P.R.B →ₗ[ℚ_[l]] P.R.B) x - x')
    (by rw [map_sub, eq_comm, sub_eq_sub_iff_sub_eq_sub]; exact e₁)
    (by
      have := Submodule.sub_mem _ (map_mem_FilV (P.PD K) f hy) hfil
      rw [← e₂] at this
      rw [map_sub]
      convert this using 1
      abel)
  refine ⟨v, funext fun g => tmul_one_injective (P.PD K) ?_⟩
  have h1 := congrArg (AlgebraTensorModule.map f (LinearMap.id : P.R.B →ₗ[ℚ_[l]] P.R.B)) (hcx g)
  rw [map_sub, map_actVB (P.PD K) f hf, AlgebraTensorModule.map_tmul, LinearMap.id_apply] at h1
  have h2 : actVB (P.PD K) A'.ρ g (v ⊗ₜ[ℚ_[l]] (1 : P.R.B)) = A'.ρ g v ⊗ₜ[ℚ_[l]] (1 : P.R.B) := by
    simp [actVB]
  change (A'.ρ g v - v) ⊗ₜ[ℚ_[l]] (1 : P.R.B) = (f (c g) - c' g) ⊗ₜ[ℚ_[l]] (1 : P.R.B)
  rw [sub_tmul, sub_tmul, h1, hx', ← h2, ← hv, map_sub]
  abel

end GlobalTheory.BKRightExact
