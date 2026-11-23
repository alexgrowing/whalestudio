import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonModel
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BhattScholzeCoefficientsOfPadicIntLattices
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteDimensionalDstOfIsSst

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.LayerSst

open Module

section Sum

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) {K : FinExt l}
  {ι : Type} [Fintype ι] [DecidableEq ι]
  {V : ι → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module ℚ_[l] (V i)]
  {V' : Type} [AddCommGroup V'] [Module ℚ_[l] V']
  {ρ : ∀ i, Representation ℚ_[l] ↥(GK K) (V i)} {ρ' : Representation ℚ_[l] ↥(GK K) V'}
  {E : V' ≃ₗ[ℚ_[l]] (∀ i, V i)}
  (hE : ∀ g x i, E (ρ' g x) i = ρ i g (E x i))
include hE

theorem mem_Dst_iff (x : V' ⊗[ℚ_[l]] Bst P) :
    x ∈ Dst P ρ' ↔ ∀ i, GlobalTheory.BlockSum.tensComp E (Bst P) x i ∈ Dst P (ρ i) := by
  simp only [mem_Dst]
  rw [forall_comm]
  refine forall_congr' fun g => ?_
  rw [← (GlobalTheory.BlockSum.tensComp E (Bst P)).injective.eq_iff, funext_iff]
  refine forall_congr' fun i => ?_
  have key : GlobalTheory.BlockSum.tensComp E (Bst P) (stRep P ρ' g x) i =
      stRep P (ρ i) g (GlobalTheory.BlockSum.tensComp E (Bst P) x i) :=
    GlobalTheory.BlockSum.tensComp_map E (ρ' g) (fun i => ρ i g) (hE g) (actSt P (g : GQ l)).toLinearMap x i
  rw [key]

theorem isSst_sum [∀ i, FiniteDimensional ℚ_[l] (V i)] (h : ∀ i, IsSst P (ρ i)) : IsSst P ρ' := by
  have := fun i => finiteDimensional_Dst_of_isSst l P K (V i) (ρ i) (h i)
  unfold IsSst at h ⊢
  rw [GlobalTheory.BlockSum.finrank_eq_sum (GlobalTheory.BlockSum.tensComp E (Bst P)) _ _ (mem_Dst_iff P hE), E.finrank_eq,
    Module.finrank_pi_fintype, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => h i

end Sum

theorem isSst_resQ {l : ℕ} [Fact l.Prime] (P : LocPrime l) {K : FinExt l} {LL : Type} [Field LL] [Algebra ℚ_[l] LL]
    [FiniteDimensional ℚ_[l] LL] {V : Type} [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V]
    (ρ : Representation LL ↥(GK K) V) (h : IsSst P ρ) : IsSst P (GlobalTheory.PstCoeff.resQ ρ) := by
  have hD : Dst P (GlobalTheory.PstCoeff.resQ ρ) = (Dst P ρ).restrictScalars ℚ_[l] := by
    ext x
    simp [mem_Dst, GlobalTheory.PstCoeff.stRep_resQ]
  have e : finrank ℚ_[l] ↥(Dst P (GlobalTheory.PstCoeff.resQ ρ)) = finrank ℚ_[l] LL * finrank LL ↥(Dst P ρ) := by
    rw [hD, finrank_mul_finrank]
    rfl
  rw [IsSst, e, h, ← finrank_mul_finrank ℚ_[l] LL V]
  ring

section Layer

variable {l : ℕ} [Fact l.Prime] {K L₀ : FinExt l} {a d : ℕ} {Cl : Set (↥(GK K) →* GL (Fin a) (Om l))}
  {ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]} (Ly : Layer L₀ Cl ρ)

def matL (k : Fin Ly.m) (g : ↥(GK K)) : Matrix (Fin a) (Fin a) ↥(Ly.L k).1 :=
  fun i j => ⟨(Ly.rep k g).val i j, Ly.rep_mem k g i j⟩

def repL (k : Fin Ly.m) : ↥(GK K) →* GL (Fin a) ↥(Ly.L k).1 :=
  MonoidHom.toHomUnits
    { toFun := matL Ly k
      map_one' := by
        ext i j
        simp only [matL, map_one, Units.val_one, Matrix.one_apply]
        split_ifs <;> rfl
      map_mul' := fun g h => by
        ext i j
        simp [matL, Matrix.mul_apply] }

theorem repL_val (k : Fin Ly.m) (g : ↥(GK K)) (i j : Fin a) :
    (((repL Ly k g).val i j : ↥(Ly.L k).1) : Om l) = (Ly.rep k g).val i j := rfl

def RL (k : Fin Ly.m) : Representation ↥(Ly.L k).1 ↥(GK K) (Fin a → ↥(Ly.L k).1) :=
  ((Matrix.toLinAlgEquiv' : Matrix (Fin a) (Fin a) ↥(Ly.L k).1 ≃ₐ[↥(Ly.L k).1] _) : _ →* _).comp
    ((Units.coeHom _).comp (repL Ly k))

theorem RL_apply (k : Fin Ly.m) (g : ↥(GK K)) (v : Fin a → ↥(Ly.L k).1) : RL Ly k g v = (repL Ly k g).val *ᵥ v := by
  simp [RL, Matrix.toLinAlgEquiv'_apply]

def coordM (v : Fin d → ℚ_[l]) (k : Fin Ly.m) : Matrix (Fin a) (Fin a) (Om l) :=
  ∑ s, algebraMap ℚ_[l] (Om l) (v s) • Ly.b s k

theorem coordM_mem (v : Fin d → ℚ_[l]) (k : Fin Ly.m) (i j : Fin a) : coordM Ly v k i j ∈ (Ly.L k).1 := by
  simp only [coordM, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  exact sum_mem fun s _ => mul_mem (IntermediateField.algebraMap_mem _ _) (Ly.b_mem s k i j)

theorem sum_b (v : Fin d → ℚ_[l]) : ∑ s, v s • Ly.b s = fun k => coordM Ly v k := by
  funext k
  simp [coordM, Finset.sum_apply, algebraMap_smul]

end Layer

section Layer2

variable {l : ℕ} [Fact l.Prime] {K L₀ : FinExt l} {a d : ℕ} {Cl : Set (↥(GK K) →* GL (Fin a) (Om l))}
  {ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]} (Ly : Layer L₀ Cl ρ)

def coordLin : (Fin d → ℚ_[l]) →ₗ[ℚ_[l]] ((p : Fin Ly.m × Fin a) → Fin a → ↥(Ly.L p.1).1) where
  toFun v p i := ⟨coordM Ly v p.1 i p.2, coordM_mem Ly v p.1 i p.2⟩
  map_add' v w := by
    funext p i
    apply Subtype.ext
    simp [coordM, Finset.sum_add_distrib, add_smul, Matrix.sum_apply]
  map_smul' c v := by
    funext p i
    apply Subtype.ext
    show coordM Ly (c • v) p.1 i p.2 = c • coordM Ly v p.1 i p.2
    simp only [coordM, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Pi.smul_apply, map_mul, Finset.smul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Algebra.smul_def, mul_assoc]

theorem coordLin_apply (v : Fin d → ℚ_[l]) (p : Fin Ly.m × Fin a) (i : Fin a) :
    ((coordLin Ly v p i : ↥(Ly.L p.1).1) : Om l) = coordM Ly v p.1 i p.2 := rfl

theorem coordLin_bijective : Function.Bijective (coordLin Ly) := by
  constructor
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    have h0 : ∑ s, v s • Ly.b s = 0 := by
      rw [sum_b]
      funext k i j
      have := congrArg Subtype.val (congrFun (congrFun hv (k, j)) i)
      exact this
    exact funext (Fintype.linearIndependent_iff.1 Ly.indep v h0)
  · intro y
    let x : Fin Ly.m → Matrix (Fin a) (Fin a) (Om l) := fun k i j => ((y (k, j) i : ↥(Ly.L k).1) : Om l)
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℚ_[l]).1 (Ly.span x fun k i j => (y (k, j) i).2)
    refine ⟨c, ?_⟩
    funext p i
    apply Subtype.ext
    rw [coordLin_apply]
    rw [sum_b] at hc
    exact congrFun (congrFun (congrFun hc p.1) i) p.2

def coordEquiv : (Fin d → ℚ_[l]) ≃ₗ[ℚ_[l]] ((p : Fin Ly.m × Fin a) → Fin a → ↥(Ly.L p.1).1) :=
  LinearEquiv.ofBijective (coordLin Ly) (coordLin_bijective Ly)

theorem coordM_mulVec (g : ↥(GK K)) (v : Fin d → ℚ_[l]) (k : Fin Ly.m) :
    coordM Ly (((ρ g).val.map (algebraMap ℤ_[l] ℚ_[l])) *ᵥ v) k = (Ly.rep k g).val * coordM Ly v k := by
  have hr : ∀ t, (Ly.rep k g).val * Ly.b t k = ∑ s, zOm l ((ρ g).val s t) • Ly.b s k :=
    fun t => (Ly.reads k).equi g t
  calc coordM Ly (((ρ g).val.map (algebraMap ℤ_[l] ℚ_[l])) *ᵥ v) k
      = ∑ s, ∑ t, (algebraMap ℚ_[l] (Om l) (v t) * zOm l ((ρ g).val s t)) • Ly.b s k := by
        simp only [coordM, Matrix.mulVec, dotProduct, map_sum, map_mul, Finset.sum_smul, Matrix.map_apply]
        refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => ?_
        rw [mul_comm]
        rfl
    _ = ∑ t, ∑ s, (algebraMap ℚ_[l] (Om l) (v t) * zOm l ((ρ g).val s t)) • Ly.b s k := Finset.sum_comm
    _ = (Ly.rep k g).val * coordM Ly v k := by
        simp only [coordM, Finset.mul_sum, Matrix.mul_smul, hr, Finset.smul_sum, smul_smul]

theorem coordEquiv_equi (g : ↥(GK K)) (v : Fin d → ℚ_[l]) (p : Fin Ly.m × Fin a) :
    coordEquiv Ly (qRep ρ g v) p = GlobalTheory.PstCoeff.resQ (RL Ly p.1) g (coordEquiv Ly v p) := by
  funext i
  apply Subtype.ext
  have hq : qRep ρ g v = ((ρ g).val.map (algebraMap ℤ_[l] ℚ_[l])) *ᵥ v := by
    simp [qRep, Matrix.toLinAlgEquiv'_apply]
  rw [GlobalTheory.PstCoeff.resQ_apply, RL_apply]
  change coordM Ly (qRep ρ g v) p.1 i p.2 = _
  rw [hq, coordM_mulVec, Matrix.mul_apply]
  simp [Matrix.mulVec, dotProduct, repL_val, coordEquiv, coordLin_apply]

end Layer2

theorem main : ∀ (l : ℕ) [Fact l.Prime] (K L₀ : FinExt l) (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (a : ℕ) (Cl : Set (↥(GK K) →* GL (Fin a) (Om l))) (d : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]) (Ly : Layer L₀ Cl ρ), ((∀ ρ₁ ∈ Cl, ∀ (L : FinExt l) (r' : ↥(GK K) →* GL (Fin a) ↥L.1) (R : Representation ↥L.1 ↥(GK K) (Fin a → ↥L.1)), L₀.1 ≤ L.1 → (∀ g v, R g v = (r' g).val *ᵥ v) → (∀ g i j, (((r' g).val i j : ↥L.1) : Om l) = (ρ₁ g).val i j) → IsSst P R) → IsSst P (qRep ρ)) ∧ ((∀ ρ₁ ∈ Cl, (∀ (L : FinExt l) (r' : ↥(GK K) →* GL (Fin a) ↥L.1) (R : Representation ↥L.1 ↥(GK K) (Fin a → ↥L.1)), L₀.1 ≤ L.1 → (∀ g v, R g v = (r' g).val *ᵥ v) → (∀ g i j, (((r' g).val i j : ↥L.1) : Om l) = (ρ₁ g).val i j) → IsCrys (P.PD K) R)) → IsCrys (P.PD K) (qRep ρ)) := by
  intro l _ K L₀ P AI T a Cl d ρ Ly
  have hfin : ∀ p : Fin Ly.m × Fin a, FiniteDimensional ℚ_[l] (Fin a → ↥(Ly.L p.1).1) := fun p => by
    have := (Ly.L p.1).2
    infer_instance
  have hE := coordEquiv_equi Ly
  refine ⟨fun hS => ?_, fun hC => ?_⟩
  · refine isSst_sum P (E := coordEquiv Ly) (fun g x p => hE g x p) fun p => ?_
    have := (Ly.L p.1).2
    exact isSst_resQ P _ (hS (Ly.rep p.1) (Ly.mem p.1) (Ly.L p.1) (repL Ly p.1) (RL Ly p.1) (Ly.le p.1)
      (fun g v => RL_apply Ly p.1 g v) (fun g i j => repL_val Ly p.1 g i j))
  · refine GlobalTheory.BlockSum.isCrys_sum (P.PD K) (E := coordEquiv Ly) (fun g x p => hE g x p) fun p => ?_
    have := (Ly.L p.1).2
    exact (GlobalTheory.BSCoeff.isCrys_resQ_iff P (RL Ly p.1)).2 (hC (Ly.rep p.1) (Ly.mem p.1) (Ly.L p.1) (repL Ly p.1)
      (RL Ly p.1) (Ly.le p.1) (fun g v => RL_apply Ly p.1 g v) (fun g i j => repL_val Ly p.1 g i j))

end GlobalTheory.LayerSst
