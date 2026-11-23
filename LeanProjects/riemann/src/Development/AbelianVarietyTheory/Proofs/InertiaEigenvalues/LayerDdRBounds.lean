import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LinearIndepOnOfInvariant
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SecondTwistSmallIffExactlyAtAndFinClause
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EventuallyClosedOfDictClosed
import Formalism.SharpRestriction.LevelLetterCocycles.JsetEmb
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.LayerJumps

open Module

theorem stab_of_steps {L M : Type} [Field L] [AddCommGroup M] [Module L M] (F : ℤ → Submodule L M)
    (anti : ∀ a, F (a + 1) ≤ F a) (fin : ∀ a, FiniteDimensional L (F a)) (N : ℕ)
    (h : ∀ a : ℤ, (N : ℤ) < |a| → finrank L (F (a + 1)) = finrank L (F a)) :
    (∀ a ≤ -(N : ℤ), F a = F (-(N : ℤ))) ∧ ∀ b, (N : ℤ) + 1 ≤ b → F b = F ((N : ℤ) + 1) := by
  constructor
  · intro a ha
    induction a, ha using Int.le_induction_down with
    | base => rfl
    | pred a ha ih =>
      rw [← ih]
      have h1 := h (a - 1) (by rw [abs_of_neg (by omega)]; omega)
      rw [sub_add_cancel] at h1
      exact (Submodule.eq_of_le_of_finrank_eq (by simpa using anti (a - 1)) h1).symm
  · intro b hb
    induction b, hb using Int.le_induction with
    | base => rfl
    | succ b hb ih =>
      rw [← ih]
      have h1 := h b (by rw [abs_of_pos (by omega)]; omega)
      exact Submodule.eq_of_le_of_finrank_eq (anti b) h1

section Periods

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)

theorem rTensor_mem_filV {LL LL' V W : Type} [Field LL] [Algebra Qp LL] [Field LL'] [Algebra Qp LL']
    [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [AddCommGroup W] [Module LL' W] [Module Qp W] [IsScalarTower Qp LL' W]
    (f : V →ₗ[Qp] W) (a : ℤ) (x : V ⊗[Qp] BdR) (hx : x ∈ FilV PD (LL := LL) (V := V) a) :
    f.rTensor BdR x ∈ FilV PD (LL := LL') (V := W) a := by
  obtain ⟨y, rfl⟩ := hx
  refine ⟨f.rTensor _ y, ?_⟩
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul v c => simp
  | add x y hx hy => simp only [map_add, hx, hy]

theorem rTensor_mem_DdR {LL LL' V W : Type} [Field LL] [Algebra Qp LL] [Field LL'] [Algebra Qp LL']
    [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [AddCommGroup W] [Module LL' W] [Module Qp W] [IsScalarTower Qp LL' W]
    (ρ : Representation LL G V) (σ : Representation LL' G W)
    (f : V →ₗ[Qp] W) (hf : ∀ g v, f (ρ g v) = σ g (f v)) (x : V ⊗[Qp] BdR) (hx : x ∈ DdR PD ρ) :
    f.rTensor BdR x ∈ DdR PD σ := by
  have key : ∀ g (y : V ⊗[Qp] BdR), actVdR PD σ g (f.rTensor BdR y) = f.rTensor BdR (actVdR PD ρ g y) := by
    intro g y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul v c => simp [actVdR, hf]
    | add x y hx hy => simp only [map_add, hx, hy]
  simp only [DdR, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
    sub_eq_zero] at hx ⊢
  intro g
  rw [key, hx g]

end Periods

theorem exists_sum_comp {Qp V ι : Type} [Field Qp] [AddCommGroup V] [Module Qp V] [Fintype ι] [DecidableEq ι]
    {W : ι → Type} [∀ i, AddCommGroup (W i)] [∀ i, Module Qp (W i)] (f : ∀ i, V →ₗ[Qp] W i)
    (hf : ∀ v, (∀ i, f i v = 0) → v = 0) :
    ∃ g : ∀ i, W i →ₗ[Qp] V, ∀ v, ∑ i, g i (f i v) = v := by
  have hinj : LinearMap.ker (LinearMap.pi f) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro v hv
    exact hf v fun i => congrFun hv i
  obtain ⟨G, hG⟩ := LinearMap.exists_leftInverse_of_injective _ hinj
  refine ⟨fun i => G.comp (LinearMap.single Qp W i), fun v => ?_⟩
  have h1 := LinearMap.congr_fun hG v
  simp only [LinearMap.comp_apply, LinearMap.id_apply] at h1
  simp only [LinearMap.comp_apply, LinearMap.coe_single]
  rw [← map_sum, Finset.univ_sum_single]
  exact h1

theorem sum_rTensor {Qp V ι BdR : Type} [Field Qp] [AddCommGroup V] [Module Qp V] [Fintype ι]
    [AddCommGroup BdR] [Module Qp BdR]
    {W : ι → Type} [∀ i, AddCommGroup (W i)] [∀ i, Module Qp (W i)] (f : ∀ i, V →ₗ[Qp] W i)
    (g : ∀ i, W i →ₗ[Qp] V) (h : ∀ v, ∑ i, g i (f i v) = v) (x : V ⊗[Qp] BdR) :
    ∑ i, (g i).rTensor BdR ((f i).rTensor BdR x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v c => simp only [LinearMap.rTensor_tmul]; rw [← TensorProduct.sum_tmul, h]
  | add x y hx hy => simp only [map_add, Finset.sum_add_distrib, hx, hy]

end GlobalTheory.LayerJumps

namespace GlobalTheory.LayerJumps

open Module

section Factor

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]

theorem factor_bounds [CharZero Qp] [Fintype (K →ₐ[Qp] LL)]
    (hcard : Fintype.card (K →ₐ[Qp] LL) = finrank Qp K) (hF : IsField BdR) [Module.Finite Qp V]
    (ρ : Representation LL G V) (J : (K →ₐ[Qp] LL) → Multiset ℤ) (N : ℕ)
    (hJ : ∀ τ, ∀ n ∈ J τ, |n| ≤ N) (hm : ∀ τ n, multV PD ρ τ n = ((J τ).count n : ℤ)) :
    DdR PD ρ ≤ FilV PD (LL := LL) (V := V) (-(N : ℤ)) ∧
      DdR PD ρ ⊓ FilV PD (LL := LL) (V := V) ((N : ℤ) + 1) = ⊥ := by
  haveI := GlobalTheory.Cmp.SmallJumps.finite_ddR_of_isField PD hF ρ
  have fin : ∀ τ a, FiniteDimensional LL (FildR PD ρ τ a) := fun τ a =>
    Submodule.finiteDimensional_of_le (S₂ := DdR PD ρ) (inf_le_left.trans inf_le_left)
  have anti : ∀ τ a, FildR PD ρ τ (a + 1) ≤ FildR PD ρ τ a := fun τ a =>
    inf_le_inf_left _ (GlobalTheory.Cmp.SmallJumps.filV_anti PD (by omega))
  have st : ∀ τ, (∀ a ≤ -(N : ℤ), FildR PD ρ τ a = FildR PD ρ τ (-(N : ℤ))) ∧
      ∀ b, (N : ℤ) + 1 ≤ b → FildR PD ρ τ b = FildR PD ρ τ ((N : ℤ) + 1) := by
    intro τ
    refine stab_of_steps (FildR PD ρ τ) (anti τ) (fin τ) N fun a ha => ?_
    have h1 := hm τ a
    have h2 : (J τ).count a = 0 := Multiset.count_eq_zero.2 fun hmem => by
      have := hJ τ a hmem
      omega
    rw [h2, multV] at h1
    omega
  have zero : ∀ τ, FildR PD ρ τ ((N : ℤ) + 1) = ⊥ := by
    intro τ
    refine (Submodule.eq_bot_iff _).2 fun y hy => GlobalTheory.Cmp.JumpDict.filV_sep PD (LL := LL) y fun b => ?_
    rcases le_total b ((N : ℤ) + 1) with hb | hb
    · exact GlobalTheory.Cmp.SmallJumps.filV_anti PD hb (Submodule.mem_inf.1 hy).2
    · rw [← (st τ).2 b hb] at hy
      exact (Submodule.mem_inf.1 hy).2
  refine ⟨fun x hx => ?_, ?_⟩
  · obtain ⟨a, ha⟩ := GlobalTheory.Cmp.SmallJumps.filV_exh PD (LL := LL) (V := V) x
    rcases le_total a (-(N : ℤ)) with h | h
    · have hx' : x ∈ DdR PD ρ ⊓ FilV PD (LL := LL) (V := V) a := Submodule.mem_inf.2 ⟨hx, ha⟩
      rw [Formalism.MainNotions.N.JsetEmb.de_rham_filtration_eq_iSup_embeddings PD hcard ρ a] at hx'
      have hle : (⨆ τ : K →ₐ[Qp] LL, FildR PD ρ τ a) ≤ FilV PD (LL := LL) (V := V) (-(N : ℤ)) :=
        iSup_le fun τ => by rw [(st τ).1 a h]; exact inf_le_right
      exact hle hx'
    · exact GlobalTheory.Cmp.SmallJumps.filV_anti PD h ha
  · rw [Formalism.MainNotions.N.JsetEmb.de_rham_filtration_eq_iSup_embeddings PD hcard ρ]
    simp [zero]

end Factor

end GlobalTheory.LayerJumps

namespace GlobalTheory.LayerJumps

open Module

variable {l : ℕ} [Fact l.Prime]

def matL (L : FinExt l) {a : ℕ} (M : Matrix (Fin a) (Fin a) (Om l)) (h : ∀ i j, M i j ∈ L.1) :
    Matrix (Fin a) (Fin a) ↥L.1 := fun i j => ⟨M i j, h i j⟩

theorem map_matL (L : FinExt l) {a : ℕ} (M : Matrix (Fin a) (Fin a) (Om l)) (h : ∀ i j, M i j ∈ L.1) :
    (algebraMap ↥L.1 (Om l)).mapMatrix (matL L M h) = M := by
  ext i j
  rfl

theorem mapMatrix_inj (L : FinExt l) {a : ℕ} :
    Function.Injective ((algebraMap ↥L.1 (Om l)).mapMatrix : Matrix (Fin a) (Fin a) ↥L.1 →+* _) := by
  intro A B h
  ext i j
  exact congrFun (congrFun h i) j

def repL {Γ : Type} [Group Γ] (L : FinExt l) {a : ℕ} (r : Γ →* GL (Fin a) (Om l))
    (h : ∀ g i j, (r g).val i j ∈ L.1) : Γ →* GL (Fin a) ↥L.1 where
  toFun g :=
    { val := matL L (r g).val (h g)
      inv := matL L (r g⁻¹).val (h g⁻¹)
      val_inv := mapMatrix_inj L (by
        rw [map_mul, map_matL, map_matL, map_one, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one,
          Units.val_one])
      inv_val := mapMatrix_inj L (by
        rw [map_mul, map_matL, map_matL, map_one, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one,
          Units.val_one]) }
  map_one' := Units.ext (mapMatrix_inj L (by
    simp only [map_matL, map_one, Units.val_one]))
  map_mul' g g' := Units.ext (mapMatrix_inj L (by
    simp only [Units.val_mul, map_mul, map_matL]))

def matRepL {Γ : Type} [Group Γ] (L : FinExt l) {a : ℕ} (r : Γ →* GL (Fin a) ↥L.1) :
    Representation ↥L.1 Γ (Fin a → ↥L.1) :=
  ((Matrix.toLinAlgEquiv' : Matrix (Fin a) (Fin a) ↥L.1 ≃ₐ[↥L.1] _) : _ →* _).comp ((Units.coeHom _).comp r)

theorem matRepL_apply {Γ : Type} [Group Γ] (L : FinExt l) {a : ℕ} (r : Γ →* GL (Fin a) ↥L.1) (g : Γ)
    (v : Fin a → ↥L.1) : matRepL L r g v = (r g).val *ᵥ v := by
  simp [matRepL, Matrix.toLinAlgEquiv'_apply]

end GlobalTheory.LayerJumps

namespace GlobalTheory.LayerJumps

open Module

variable {l : ℕ} [Fact l.Prime]

def colMap {Γ : Type} [Group Γ] {a d : ℕ} {L₀ : FinExt l} {Cl : Set (Γ →* GL (Fin a) (Om l))}
    {ρ : Γ →* GL (Fin d) ℤ_[l]} (Ly : Layer L₀ Cl ρ) (k : Fin Ly.m) (c : Fin a) :
    (Fin d → ℚ_[l]) →ₗ[ℚ_[l]] (Fin a → ↥(Ly.L k).1) :=
  ∑ j, (LinearMap.proj j : (Fin d → ℚ_[l]) →ₗ[ℚ_[l]] ℚ_[l]).smulRight
    (fun i => (⟨Ly.b j k i c, Ly.b_mem j k i c⟩ : ↥(Ly.L k).1))

theorem colMap_coe {Γ : Type} [Group Γ] {a d : ℕ} {L₀ : FinExt l} {Cl : Set (Γ →* GL (Fin a) (Om l))}
    {ρ : Γ →* GL (Fin d) ℤ_[l]} (Ly : Layer L₀ Cl ρ) (k : Fin Ly.m) (c : Fin a) (v : Fin d → ℚ_[l])
    (i : Fin a) :
    algebraMap ↥(Ly.L k).1 (Om l) (colMap Ly k c v i) = ∑ j, algebraMap ℚ_[l] (Om l) (v j) * Ly.b j k i c := by
  simp only [colMap, LinearMap.sum_apply, Finset.sum_apply, LinearMap.smulRight_apply,
    LinearMap.proj_apply, Pi.smul_apply, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply]
  rfl

theorem colMap_equi {Γ : Type} [Group Γ] {a d : ℕ} {L₀ : FinExt l} {Cl : Set (Γ →* GL (Fin a) (Om l))}
    {ρ : Γ →* GL (Fin d) ℤ_[l]} (Ly : Layer L₀ Cl ρ) (k : Fin Ly.m) (c : Fin a) (g : Γ)
    (v : Fin d → ℚ_[l]) :
    colMap Ly k c (qRep ρ g v) =
      matRepL (Ly.L k) (repL (Ly.L k) (Ly.rep k) (Ly.rep_mem k)) g (colMap Ly k c v) := by
  rw [matRepL_apply]
  funext i₀
  apply (algebraMap ↥(Ly.L k).1 (Om l)).injective
  rw [colMap_coe]
  have hread : ∀ j, ∑ i', (Ly.rep k g).val i₀ i' * Ly.b j k i' c =
      ∑ i, zOm l ((ρ g).val i j) * Ly.b i k i₀ c := by
    intro j
    have := congrArg (fun M => M i₀ c) ((Ly.reads k).equi g j)
    simpa [Matrix.mul_apply, Matrix.sum_apply, smul_eq_mul] using this
  have hL : algebraMap ↥(Ly.L k).1 (Om l) (((repL (Ly.L k) (Ly.rep k) (Ly.rep_mem k) g).val *ᵥ colMap Ly k c v) i₀) =
      ∑ i', (Ly.rep k g).val i₀ i' * ∑ j, algebraMap ℚ_[l] (Om l) (v j) * Ly.b j k i' c := by
    simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, colMap_coe]
    rfl
  rw [hL]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  have h2 : ∀ j, ∑ i', (Ly.rep k g).val i₀ i' * (algebraMap ℚ_[l] (Om l) (v j) * Ly.b j k i' c) =
      algebraMap ℚ_[l] (Om l) (v j) * ∑ i, zOm l ((ρ g).val i j) * Ly.b i k i₀ c := by
    intro j
    rw [← hread j, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i' _ => by ring
  simp only [h2, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [qRep, MonoidHom.coe_comp, Function.comp_apply]
  show algebraMap ℚ_[l] (Om l) ((((ρ g).val.map (algebraMap ℤ_[l] ℚ_[l])) *ᵥ v) i) * _ = _
  simp only [Matrix.mulVec, dotProduct, map_sum, Finset.sum_mul,
    RingHom.mapMatrix_apply, Matrix.map_apply, Units.coeHom_apply, map_mul, zOm, RingHom.comp_apply]
  refine Finset.sum_congr rfl fun x _ => by ring

end GlobalTheory.LayerJumps

namespace GlobalTheory.LayerJumps

open Module

variable {l : ℕ} [Fact l.Prime]

theorem colMap_inj {Γ : Type} [Group Γ] {a d : ℕ} {L₀ : FinExt l} {Cl : Set (Γ →* GL (Fin a) (Om l))}
    {ρ : Γ →* GL (Fin d) ℤ_[l]} (Ly : Layer L₀ Cl ρ) (v : Fin d → ℚ_[l])
    (h : ∀ kc : Fin Ly.m × Fin a, colMap Ly kc.1 kc.2 v = 0) : v = 0 := by
  have hs : ∑ j, v j • Ly.b j = 0 := by
    funext k
    ext i c
    have := congrArg (fun w => algebraMap ↥(Ly.L k).1 (Om l) (w i)) (h (k, c))
    simp only [colMap_coe, Pi.zero_apply, map_zero] at this
    simp only [Finset.sum_apply, Pi.smul_apply, Matrix.sum_apply, Matrix.smul_apply, Pi.zero_apply,
      Matrix.zero_apply]
    simpa only [Algebra.smul_def] using this
  funext j
  exact Fintype.linearIndependent_iff.1 Ly.indep v hs j

theorem card_emb_of_le (K L₀ L : FinExt l) (hK : ∀ (τ : ↥K.1 →ₐ[ℚ_[l]] Om l) (x : ↥K.1), τ x ∈ L₀.1)
    (hle : L₀.1 ≤ L.1) [Fintype (↥K.1 →ₐ[ℚ_[l]] ↥L.1)] :
    Fintype.card (↥K.1 →ₐ[ℚ_[l]] ↥L.1) = finrank ℚ_[l] ↥K.1 := by
  have := K.2
  rw [← AlgHom.card ℚ_[l] ↥K.1 (Om l)]
  refine Fintype.card_congr (Equiv.ofBijective (fun τ => L.1.val.comp τ) ⟨fun τ τ' hτ => ?_, fun σ => ?_⟩)
  · ext x
    exact congrArg (fun f : ↥K.1 →ₐ[ℚ_[l]] Om l => f x) hτ
  · have hm : ∀ x, σ x ∈ L.1.toSubalgebra := fun x => hle (hK σ x)
    exact ⟨σ.codRestrict _ hm, rfl⟩

theorem layer_DdR_bounds : ∀ (l : ℕ) [Fact l.Prime] (K L₀ : FinExt l) (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (a : ℕ) (Cl : Set (↥(GK K) →* GL (Fin a) (Om l))) (J : (↥K.1 →ₐ[ℚ_[l]] Om l) → Multiset ℤ) (N : ℕ), (∀ (τ : ↥K.1 →ₐ[ℚ_[l]] Om l) (x : ↥K.1), τ x ∈ L₀.1) → (∀ τ, ∀ n ∈ J τ, |n| ≤ N) → ∀ (d : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]) (Ly : Layer L₀ Cl ρ), (∀ ρ₁ ∈ Cl, (∀ (L : FinExt l) (r' : ↥(GK K) →* GL (Fin a) ↥L.1) (R : Representation ↥L.1 ↥(GK K) (Fin a → ↥L.1)), L₀.1 ≤ L.1 → (∀ g v, R g v = (r' g).val *ᵥ v) → (∀ g i j, (((r' g).val i j : ↥L.1) : Om l) = (ρ₁ g).val i j) → IsSst P R ∧ ∀ (τ : ↥K.1 →ₐ[ℚ_[l]] ↥L.1) (n : ℤ), multV (P.PD K) R τ n = ((J (L.1.val.comp τ)).count n : ℤ))) → (DdR (P.PD K) (qRep ρ) ≤ FilV (P.PD K) (LL := ℚ_[l]) (V := Fin d → ℚ_[l]) (-(N : ℤ)) ∧ DdR (P.PD K) (qRep ρ) ⊓ FilV (P.PD K) (LL := ℚ_[l]) (V := Fin d → ℚ_[l]) ((N : ℤ) + 1) = ⊥) := by
  intro l _ K L₀ P AI T a Cl J N hK hJ d ρ Ly hCl
  have hF : IsField P.R.BdR := GlobalTheory.Per.FontaineBound.isField_of_tied T
  have fac : ∀ k : Fin Ly.m,
      DdR (P.PD K) (matRepL (Ly.L k) (repL (Ly.L k) (Ly.rep k) (Ly.rep_mem k))) ≤
          FilV (P.PD K) (LL := ↥(Ly.L k).1) (V := Fin a → ↥(Ly.L k).1) (-(N : ℤ)) ∧
        DdR (P.PD K) (matRepL (Ly.L k) (repL (Ly.L k) (Ly.rep k) (Ly.rep_mem k))) ⊓
          FilV (P.PD K) (LL := ↥(Ly.L k).1) (V := Fin a → ↥(Ly.L k).1) ((N : ℤ) + 1) = ⊥ := by
    intro k
    have := (Ly.L k).2
    have := K.2
    letI : Fintype (↥K.1 →ₐ[ℚ_[l]] ↥(Ly.L k).1) := Fintype.ofFinite _
    have hcl := hCl (Ly.rep k) (Ly.mem k) (Ly.L k) (repL (Ly.L k) (Ly.rep k) (Ly.rep_mem k))
      (matRepL (Ly.L k) (repL (Ly.L k) (Ly.rep k) (Ly.rep_mem k))) (Ly.le k)
      (fun g v => matRepL_apply _ _ g v) (fun g i j => rfl)
    exact factor_bounds (P.PD K) (card_emb_of_le K L₀ (Ly.L k) hK (Ly.le k)) hF _
      (fun τ => J ((Ly.L k).1.val.comp τ)) N (fun τ => hJ _) hcl.2
  obtain ⟨gi, hgi⟩ := exists_sum_comp (fun kc : Fin Ly.m × Fin a => colMap Ly kc.1 kc.2) (colMap_inj Ly)
  have hsum := sum_rTensor (BdR := P.R.BdR) _ gi hgi
  have hD : ∀ (kc : Fin Ly.m × Fin a) x, x ∈ DdR (P.PD K) (qRep ρ) →
      (colMap Ly kc.1 kc.2).rTensor P.R.BdR x ∈
        DdR (P.PD K) (matRepL (Ly.L kc.1) (repL (Ly.L kc.1) (Ly.rep kc.1) (Ly.rep_mem kc.1))) :=
    fun kc x hx => rTensor_mem_DdR (P.PD K) _ _ _ (fun g v => colMap_equi Ly kc.1 kc.2 g v) x hx
  constructor
  · intro x hx
    rw [← hsum x]
    exact Submodule.sum_mem _ fun kc _ =>
      rTensor_mem_filV (P.PD K) (LL := ↥(Ly.L kc.1).1) _ _ _ ((fac kc.1).1 (hD kc x hx))
  · refine (Submodule.eq_bot_iff _).2 fun x hx => ?_
    obtain ⟨hx1, hx2⟩ := Submodule.mem_inf.1 hx
    rw [← hsum x]
    refine Finset.sum_eq_zero fun kc _ => ?_
    have h3 : (colMap Ly kc.1 kc.2).rTensor P.R.BdR x ∈
        DdR (P.PD K) (matRepL (Ly.L kc.1) (repL (Ly.L kc.1) (Ly.rep kc.1) (Ly.rep_mem kc.1))) ⊓
          FilV (P.PD K) (LL := ↥(Ly.L kc.1).1) (V := Fin a → ↥(Ly.L kc.1).1) ((N : ℤ) + 1) :=
      Submodule.mem_inf.2 ⟨hD kc x hx1, rTensor_mem_filV (P.PD K) (LL := ℚ_[l]) _ _ _ hx2⟩
    rw [(fac kc.1).2] at h3
    rw [(Submodule.mem_bot _).1 h3, map_zero]

end GlobalTheory.LayerJumps
