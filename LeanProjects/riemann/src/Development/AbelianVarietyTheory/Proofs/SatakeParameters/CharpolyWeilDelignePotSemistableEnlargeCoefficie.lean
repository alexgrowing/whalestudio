import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FiniteDimensionalWdSpace
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CommuteIsNilpotentOfUnipotent
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinrankLetterHomComp

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial GlobalTheory.Pst
open GlobalTheory.WeilDeligne TensorProduct Module Formalism.WeaklyAdmissibleFiltrations

namespace GlobalTheory.Pst.EnlargeCoeff

section Letter

variable {K₁ K₂ U D₁ D₂ : Type} [Field K₁] [Field K₂] [Field U]
  [AddCommGroup D₁] [Module K₁ D₁] [AddCommGroup D₂] [Module K₂ D₂]
  (m₁ : U →+* End K₁ D₁) (m₂ : U →+* End K₂ D₂) (F : Type) [Field F] [Algebra K₁ F] [Algebra K₂ F]
  (τ : U →+* F) (s : K₁ →+* K₂) (hs : ∀ a, algebraMap K₂ F (s a) = algebraMap K₁ F a)
  (T : D₁ →+ D₂) (hT : ∀ (a : K₁) x, T (a • x) = s a • T x)

def chg₀ : F ⊗[K₁] D₁ →ₗ[F] Letter m₂ F τ :=
  letI : Module K₁ (Letter m₂ F τ) := Module.compHom _ (algebraMap K₁ F)
  haveI : IsScalarTower K₁ F (Letter m₂ F τ) := ⟨fun a c y => by rw [Algebra.smul_def, mul_smul]; rfl⟩
  LinearMap.liftBaseChange F
    { toFun := fun x => letterMk m₂ F τ (T x)
      map_add' := fun x y => by rw [map_add, letterMk_add]
      map_smul' := fun a x => by
        rw [hT, letterMk_smul, hs]; rfl }

theorem chg₀_tmul (a : F) (x : D₁) : chg₀ m₂ F τ s hs T hT (a ⊗ₜ x) = a • letterMk m₂ F τ (T x) := by
  rw [chg₀, LinearMap.liftBaseChange_tmul]; rfl

variable (hm : ∀ c x, T (m₁ c x) = m₂ c (T x))

def chg : Letter m₁ F τ →ₗ[F] Letter m₂ F τ :=
  (letterKer m₁ F τ).liftQ (chg₀ m₂ F τ s hs T hT) (iSup_le fun c => by
    rintro _ ⟨y, rfl⟩
    rw [LinearMap.mem_ker]
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a x =>
      rw [LinearMap.sub_apply, LinearMap.baseChange_tmul, LinearMap.smul_apply, LinearMap.id_apply, map_sub,
        map_smul, chg₀_tmul, chg₀_tmul, hm, letterMk_mul, smul_smul, smul_smul, mul_comm, sub_self]
    | add x y hx hy => rw [map_add, map_add, hx, hy, add_zero])

@[simp] theorem chg_mk (x : D₁) :
    chg m₁ m₂ F τ s hs T hT hm (letterMk m₁ F τ x) = letterMk m₂ F τ (T x) := by
  show chg₀ m₂ F τ s hs T hT (1 ⊗ₜ x) = _
  rw [chg₀_tmul, one_smul]

theorem chg_letterMap (S₁ : End K₁ D₁) (hS₁ : ∀ c, S₁ * m₁ c = m₁ c * S₁) (S₂ : End K₂ D₂)
    (hS₂ : ∀ c, S₂ * m₂ c = m₂ c * S₂) (hTS : ∀ x, T (S₁ x) = S₂ (T x)) (y : Letter m₁ F τ) :
    chg m₁ m₂ F τ s hs T hT hm (letterMap m₁ F τ S₁ hS₁ y) = letterMap m₂ F τ S₂ hS₂ (chg m₁ m₂ F τ s hs T hT hm y) := by
  have : (chg m₁ m₂ F τ s hs T hT hm).comp (letterMap m₁ F τ S₁ hS₁) =
      (letterMap m₂ F τ S₂ hS₂).comp (chg m₁ m₂ F τ s hs T hT hm) :=
    letter_hom_ext m₁ F τ fun x => by simp only [LinearMap.comp_apply, letterMap_mk, chg_mk, hTS]
  exact LinearMap.congr_fun this y

end Letter

end GlobalTheory.Pst.EnlargeCoeff

namespace GlobalTheory.Pst.EnlargeCoeff

section Tens

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) {LL LL' : Type} [Field LL] [Algebra ℚ_[l] LL]
  [Field LL'] [Algebra ℚ_[l] LL']
  {V V' : Type} [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V]
  [AddCommGroup V'] [Module LL' V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] LL' V']
  (f : V →ₗ[ℚ_[l]] V')

def tensQ : V ⊗[ℚ_[l]] Bst P →ₗ[ℚ_[l]] V' ⊗[ℚ_[l]] Bst P := TensorProduct.map f LinearMap.id

@[simp] theorem tensQ_tmul (v : V) (b : Bst P) : tensQ P f (v ⊗ₜ b) = f v ⊗ₜ b := rfl

theorem tensQ_onB (S : End ℚ_[l] (Bst P)) (x : V ⊗[ℚ_[l]] Bst P) :
    tensQ P f (onB P LL V S x) = onB P LL' V' S (tensQ P f x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

variable {K : FinExt l} {ρ : Representation LL ↥(GK K) V} {ρ' : Representation LL' ↥(GK K) V'} {f}

theorem tensQ_stRep (hf : ∀ g v, f (ρ g v) = ρ' g (f v)) (g : ↥(GK K)) (x : V ⊗[ℚ_[l]] Bst P) :
    tensQ P f (stRep P ρ g x) = stRep P ρ' g (tensQ P f x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [hf]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem tensQ_mem_Dpst (hf : ∀ g v, f (ρ g v) = ρ' g (f v)) (x : V ⊗[ℚ_[l]] Bst P) (hx : x ∈ Dpst P ρ) :
    tensQ P f x ∈ Dpst P ρ' := by
  obtain ⟨K', hK⟩ := (mem_Dpst P ρ).mp hx
  exact (mem_Dpst P ρ').mpr ⟨K', fun g hg => by rw [← tensQ_stRep P hf, hK g hg]⟩

def dQ (hf : ∀ g v, f (ρ g v) = ρ' g (f v)) : ↥(Dpst P ρ) →+ ↥(Dpst P ρ') where
  toFun x := ⟨tensQ P f x, tensQ_mem_Dpst P hf x x.2⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' x y := Subtype.ext (map_add _ _ _)

@[simp] theorem coe_dQ (hf : ∀ g v, f (ρ g v) = ρ' g (f v)) (x : ↥(Dpst P ρ)) :
    (dQ P hf x : V' ⊗[ℚ_[l]] Bst P) = tensQ P f x := rfl

variable (hf : ∀ g v, f (ρ g v) = ρ' g (f v))
include hf

theorem dQ_phiD (x : ↥(Dpst P ρ)) : dQ P hf (phiD P ρ x) = phiD P ρ' (dQ P hf x) :=
  Subtype.ext (tensQ_onB P f _ x.1)

theorem dQ_mulD (c : ↥(MaximalUnramifiedExtension l)) (x : ↥(Dpst P ρ)) : dQ P hf (mulD P ρ c x) = mulD P ρ' c (dQ P hf x) :=
  Subtype.ext (tensQ_onB P f _ x.1)

theorem dQ_actD (g : ↥(GK K)) (x : ↥(Dpst P ρ)) : dQ P hf (actD P ρ g x) = actD P ρ' g (dQ P hf x) :=
  Subtype.ext (tensQ_stRep P hf g x.1)

theorem dQ_phiU_zpow [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P ρ)] [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P ρ')]
    (n : ℤ) (x : ↥(Dpst P ρ)) :
    dQ P hf (((phiU P ρ ^ n : (End LL ↥(Dpst P ρ))ˣ) : End LL ↥(Dpst P ρ)) x) =
      ((phiU P ρ' ^ n : (End LL' ↥(Dpst P ρ'))ˣ) : End LL' ↥(Dpst P ρ')) (dQ P hf x) := by
  have hinv : ∀ y, dQ P hf ((((phiU P ρ)⁻¹ : (End LL ↥(Dpst P ρ))ˣ) : End LL ↥(Dpst P ρ)) y) =
      (((phiU P ρ')⁻¹ : (End LL' ↥(Dpst P ρ'))ˣ) : End LL' ↥(Dpst P ρ')) (dQ P hf y) := by
    intro y
    have h1 : phiD P ρ' (dQ P hf ((((phiU P ρ)⁻¹ : (End LL ↥(Dpst P ρ))ˣ) : End LL ↥(Dpst P ρ)) y)) =
        dQ P hf y := by
      rw [← dQ_phiD, ← coe_phiU, ← End.mul_apply, Units.mul_inv]; rfl
    rw [← h1, ← coe_phiU, ← End.mul_apply, Units.inv_mul]; rfl
  induction n using Int.induction_on generalizing x with
  | zero => simp
  | succ n ih =>
    rw [zpow_add_one, zpow_add_one, Units.val_mul, Units.val_mul, End.mul_apply, End.mul_apply, ih, coe_phiU,
      coe_phiU, dQ_phiD]
  | pred n ih =>
    rw [zpow_sub_one, zpow_sub_one, Units.val_mul, Units.val_mul, End.mul_apply, End.mul_apply, ih, hinv]

end Tens

end GlobalTheory.Pst.EnlargeCoeff

namespace GlobalTheory.Pst.EnlargeCoeff

section Weil

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l)
  {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)}
  {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
  (Bw : LocBridge l E Ω (Dec (F := E) A) O) (h : IsPlaceOver A w)
  {LL LL' : Type} [Field LL] [Algebra ℚ_[l] LL] [Field LL'] [Algebra ℚ_[l] LL']
  {V V' : Type} [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V]
  [AddCommGroup V'] [Module LL' V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] LL' V']
  {ρ : Representation LL ↥(GK Bw.Kw) V} {ρ' : Representation LL' ↥(GK Bw.Kw) V'} {f : V →ₗ[ℚ_[l]] V'}
  (hf : ∀ g v, f (ρ g v) = ρ' g (f v))
  [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P ρ)] [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P ρ')]

theorem dQ_weilD (σ : ↥(Weil h)) (x : ↥(Dpst P ρ)) :
    dQ P hf (weilD Bw h P ρ σ x) = weilD Bw h P ρ' σ (dQ P hf x) := by
  rw [weilD_apply, weilD_apply, End.mul_apply, End.mul_apply]
  exact (dQ_actD P hf _ _).trans (congrArg _ (dQ_phiU_zpow P hf _ x))

end Weil

section Incl

variable {l : ℕ} [Fact l.Prime] {L₁ L₂ : FinExt l} (hL : L₁.1 ≤ L₂.1) (m : ℕ)

def incV : (Fin m → ↥L₁.1) →ₗ[ℚ_[l]] (Fin m → ↥L₂.1) :=
  (IntermediateField.inclusion hL).toLinearMap.compLeft (Fin m)

variable {m}

@[simp] theorem incV_apply (v : Fin m → ↥L₁.1) (i : Fin m) : incV hL m v i = IntermediateField.inclusion hL (v i) :=
  rfl

theorem incV_smul (a : ↥L₁.1) (v : Fin m → ↥L₁.1) :
    incV hL m (a • v) = IntermediateField.inclusion hL a • incV hL m v := by
  funext i; simp [smul_eq_mul]

theorem incV_mulVec (M : Matrix (Fin m) (Fin m) ↥L₁.1) (v : Fin m → ↥L₁.1) :
    incV hL m (M.mulVec v) = (M.map (IntermediateField.inclusion hL)).mulVec (incV hL m v) := by
  funext i
  exact RingHom.map_mulVec (IntermediateField.inclusion hL).toRingHom M v i

end Incl

end GlobalTheory.Pst.EnlargeCoeff

namespace GlobalTheory.Pst.EnlargeCoeff

section Decomp

variable {l : ℕ} [Fact l.Prime] {L₁ L₂ : FinExt l} (hL : L₁.1 ≤ L₂.1) {m : ℕ}

theorem exists_decomp : ∃ (n : ℕ) (b : Fin n → ↥L₂.1) (π : Fin n → (Fin m → ↥L₂.1) →ₗ[ℚ_[l]] (Fin m → ↥L₁.1)),
    (∀ j (M : Matrix (Fin m) (Fin m) ↥L₁.1) v,
      π j ((M.map (IntermediateField.inclusion hL)).mulVec v) = M.mulVec (π j v)) ∧
    ∀ v, ∑ j, b j • incV hL m (π j v) = v := by
  letI : Algebra ↥L₁.1 ↥L₂.1 := (IntermediateField.inclusion hL).toRingHom.toAlgebra
  haveI : IsScalarTower ℚ_[l] ↥L₁.1 ↥L₂.1 :=
    IsScalarTower.of_algebraMap_eq fun c => ((IntermediateField.inclusion hL).commutes c).symm
  haveI := L₂.2
  haveI : Module.Finite ↥L₁.1 ↥L₂.1 := Module.Finite.of_restrictScalars_finite ℚ_[l] ↥L₁.1 ↥L₂.1
  let B := Module.finBasis ↥L₁.1 ↥L₂.1
  have hsm : ∀ (a : ↥L₁.1) (y : ↥L₂.1), IntermediateField.inclusion hL a * y = a • y := fun a y => rfl
  refine ⟨_, fun j => B j, fun j => ((B.coord j).restrictScalars ℚ_[l]).compLeft (Fin m), ?_, ?_⟩
  · intro j M v
    funext i
    simp only [LinearMap.compLeft, LinearMap.coe_mk, AddHom.coe_mk, Function.comp_apply,
      LinearMap.coe_restrictScalars, Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, hsm, map_smul,
      smul_eq_mul]
  · intro v
    funext i
    simp only [Finset.sum_apply, Pi.smul_apply, incV_apply, LinearMap.compLeft, LinearMap.coe_mk,
      AddHom.coe_mk, Function.comp_apply, LinearMap.coe_restrictScalars, Basis.coord_apply, smul_eq_mul]
    conv_rhs => rw [← B.sum_repr (v i)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_comm, hsm]

end Decomp

end GlobalTheory.Pst.EnlargeCoeff

namespace GlobalTheory.Pst.EnlargeCoeff

section General

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) (ι : Om l ≃+* ℂ)
  {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)}
  {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
  (Bw : LocBridge l E Ω (Dec (F := E) A) O) (h : IsPlaceOver A w) (hj : Induces Bw)
  {L₁ L₂ : FinExt l}
  {V₁ V₂ : Type} [AddCommGroup V₁] [Module ↥L₁.1 V₁] [Module ℚ_[l] V₁] [IsScalarTower ℚ_[l] ↥L₁.1 V₁]
  [AddCommGroup V₂] [Module ↥L₂.1 V₂] [Module ℚ_[l] V₂] [IsScalarTower ℚ_[l] ↥L₂.1 V₂]
  {ρ₁ : Representation ↥L₁.1 ↥(GK Bw.Kw) V₁} {ρ₂ : Representation ↥L₂.1 ↥(GK Bw.Kw) V₂}

theorem tensQ_smul (s : ↥L₁.1 →+* ↥L₂.1) {f : V₁ →ₗ[ℚ_[l]] V₂} (hfs : ∀ (a : ↥L₁.1) v, f (a • v) = s a • f v)
    (a : ↥L₁.1) (x : V₁ ⊗[ℚ_[l]] Bst P) : tensQ P f (a • x) = s a • tensQ P f x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v c => show f (a • v) ⊗ₜ c = s a • (f v ⊗ₜ c); rw [hfs, smul_tmul']
  | add x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add]

theorem sum_tensQ {f : V₁ →ₗ[ℚ_[l]] V₂} {n : ℕ} (b : Fin n → ↥L₂.1) (π : Fin n → V₂ →ₗ[ℚ_[l]] V₁)
    (hsum : ∀ v, ∑ j, b j • f (π j v) = v) (z : V₂ ⊗[ℚ_[l]] Bst P) :
    ∑ j, b j • tensQ P f (tensQ P (π j) z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul v c =>
    conv_rhs => rw [← hsum v]
    rw [sum_tmul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [tensQ_tmul, tensQ_tmul, smul_tmul']
  | add x y hx hy => simp only [map_add, smul_add, Finset.sum_add_distrib, hx, hy]

variable [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P ρ₁)] [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P ρ₂)]

theorem charpoly_wdRho_eq (s : ↥L₁.1 →+* ↥L₂.1) (hs : ∀ a, (s a : Om l) = (a : Om l))
    {f : V₁ →ₗ[ℚ_[l]] V₂} (hf : ∀ g v, f (ρ₁ g v) = ρ₂ g (f v)) (hfs : ∀ (a : ↥L₁.1) v, f (a • v) = s a • f v)
    {n : ℕ} (b : Fin n → ↥L₂.1) (π : Fin n → V₂ →ₗ[ℚ_[l]] V₁) (hπ : ∀ j g v, π j (ρ₂ g v) = ρ₁ g (π j v))
    (hsum : ∀ v, ∑ j, b j • f (π j v) = v)
    (hdim : finrank ℂ (WDSpace P ι ρ₁) ≤ finrank ℂ (WDSpace P ι ρ₂)) (σ : ↥(Weil h)) :
    (wdRho P ι Bw h hj ρ₂ σ).charpoly = (wdRho P ι Bw h hj ρ₁ σ).charpoly := by
  have hT : ∀ (a : ↥L₁.1) (x : ↥(Dpst P ρ₁)), dQ P hf (a • x) = s a • dQ P hf x := fun a x =>
    Subtype.ext (tensQ_smul P s hfs a x.1)
  letI := algC ι L₁
  letI := algC ι L₂
  let Φ := chg (mulD P ρ₁) (mulD P ρ₂) ℂ (urC ι) s (fun a => congrArg ι (hs a)) (dQ P hf) hT (dQ_mulD P hf)
  have hΦ : ∀ y, Φ (wdRho P ι Bw h hj ρ₁ σ y) = wdRho P ι Bw h hj ρ₂ σ (Φ y) :=
    chg_letterMap _ _ _ _ _ _ _ _ _ _ (weilD_mulD Bw h P ρ₁ hj σ) _ (weilD_mulD Bw h P ρ₂ hj σ)
      (dQ_weilD P Bw h hf σ)
  have hsurj : Function.Surjective Φ := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← span_wdMk P ι ρ₂, Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    have hx : x = ∑ j, b j • dQ P hf (dQ P (hπ j) x) := by
      apply Subtype.ext
      simp only [Submodule.coe_sum, Submodule.coe_smul, coe_dQ]
      exact (sum_tensQ P b π hsum x.1).symm
    have hms := map_sum (AddMonoidHom.mk' (wdMk P ι ρ₂) (wdMk_add P ι ρ₂))
      (fun j => b j • dQ P hf (dQ P (hπ j) x)) Finset.univ
    simp only [AddMonoidHom.mk'_apply] at hms
    rw [hx, hms]
    refine Submodule.sum_mem _ fun j _ => ?_
    rw [wdMk_smul]
    exact Submodule.smul_mem _ _ ⟨wdMk P ι ρ₁ (dQ P (hπ j) x), chg_mk _ _ _ _ _ _ _ _ _ _⟩
  have hdvd := DpstMap.charpoly_dvd_of_surjective Φ hsurj _ _ hΦ
  refine (Polynomial.eq_of_monic_of_dvd_of_natDegree_le (LinearMap.charpoly_monic _) (LinearMap.charpoly_monic _)
    hdvd ?_).symm
  rw [LinearMap.charpoly_natDegree, LinearMap.charpoly_natDegree]
  exact hdim

end General

end GlobalTheory.Pst.EnlargeCoeff

namespace GlobalTheory.Pst.EnlargeCoeff

theorem charPol_wdPst_enlarge {l : ℕ} [Fact l.Prime] (P : LocPrime l) (ι : Om l ≃+* ℂ) {E Ω : Type} [Field E]
    [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {A : ValuationSubring Ω}
    {w : HeightOneSpectrum (𝓞 E)} {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
    (Bw : LocBridge l E Ω (Dec (F := E) A) O) (h : IsPlaceOver A w) (hj : Induces Bw) {m : ℕ} {L₁ L₂ : FinExt l}
    (hL : L₁.1 ≤ L₂.1) (r₁ : ↥(Dec (F := E) A) →* GL (Fin m) ↥L₁.1) :
    IsPst P (Bw.repE L₁ r₁) → IsPst P (Bw.repE L₂ (mapRep (IntermediateField.inclusion hL).toRingHom r₁)) →
    ∀ σ : ↥(Weil h), WD.charPol (wdPst P ι Bw h hj (Bw.repE L₂ (mapRep (IntermediateField.inclusion hL).toRingHom r₁))) σ =
      WD.charPol (wdPst P ι Bw h hj (Bw.repE L₁ r₁)) σ := by
  intro hV₁ hV₂ σ
  haveI := hV₁.finite
  haveI := hV₂.finite
  obtain ⟨n, b, π, hπ, hsum⟩ := exists_decomp hL (m := m)
  have hf : ∀ g v, incV hL m (Bw.repE L₁ r₁ g v) =
      Bw.repE L₂ (mapRep (IntermediateField.inclusion hL).toRingHom r₁) g (incV hL m v) :=
    fun g v => incV_mulVec hL _ v
  have hπ' : ∀ (j : Fin n) (g : ↥(GK Bw.Kw)) (v : Fin m → ↥L₂.1),
      π j (Bw.repE L₂ (mapRep (IntermediateField.inclusion hL).toRingHom r₁) g v) = Bw.repE L₁ r₁ g (π j v) :=
    fun j g v => hπ j (r₁ (Bw.e.symm g) : Matrix (Fin m) (Fin m) ↥L₁.1) v
  have hdim : finrank ℂ (WDSpace P ι (Bw.repE L₁ r₁)) ≤
      finrank ℂ (WDSpace P ι (Bw.repE L₂ (mapRep (IntermediateField.inclusion hL).toRingHom r₁))) :=
    ((GlobalTheory.Pst.LetterDim.finrank_wdSpace l P ι Bw.Kw L₁ _ _ hV₁).trans ((Module.finrank_fin_fun _).trans
      ((Module.finrank_fin_fun _).symm.trans (GlobalTheory.Pst.LetterDim.finrank_wdSpace l P ι Bw.Kw L₂ _ _ hV₂).symm))).le
  refine (DpstMap.charPol_wdPst P ι Bw h hj (Bw.repE L₂ (mapRep (IntermediateField.inclusion hL).toRingHom r₁)) hV₂ σ).trans
    (Eq.trans ?_ (DpstMap.charPol_wdPst P ι Bw h hj (Bw.repE L₁ r₁) hV₁ σ).symm)
  exact charpoly_wdRho_eq P ι Bw h hj (IntermediateField.inclusion hL).toRingHom (fun _ => rfl) hf (incV_smul hL)
    b π hπ' hsum hdim σ

end GlobalTheory.Pst.EnlargeCoeff
