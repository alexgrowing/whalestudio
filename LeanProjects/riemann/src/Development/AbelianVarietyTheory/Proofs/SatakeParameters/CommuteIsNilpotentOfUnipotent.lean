import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FiniteDimensionalWdSpace
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CharpolyEqOfIsNilpotentSub
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.CharpolyBlockAndInvariantUnderStabilizerNilradic

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Polynomial TensorProduct Module
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne

namespace GlobalTheory.Pst.DpstMap

section Letter

variable {LL U D D' : Type} [Field LL] [Field U] [AddCommGroup D] [Module LL D] [AddCommGroup D'] [Module LL D']
  (m : U →+* End LL D) (m' : U →+* End LL D') (F : Type) [Field F] [Algebra LL F] (τ : U →+* F)

def letterLin (T : D →ₗ[LL] D') (hT : ∀ c, T ∘ₗ m c = m' c ∘ₗ T) : Letter m F τ →ₗ[F] Letter m' F τ :=
  Submodule.mapQ _ _ (T.baseChange F) (iSup_le fun c => by
    rintro _ ⟨y, rfl⟩
    refine Submodule.mem_iSup_of_mem c ⟨T.baseChange F y, ?_⟩
    have := LinearMap.congr_fun (congrArg (LinearMap.baseChange F) (hT c)) y
    rw [LinearMap.baseChange_comp, LinearMap.baseChange_comp, LinearMap.comp_apply, LinearMap.comp_apply] at this
    simp [this])

@[simp] theorem letterLin_mk (T : D →ₗ[LL] D') (hT : ∀ c, T ∘ₗ m c = m' c ∘ₗ T) (x : D) :
    letterLin m m' F τ T hT (letterMk m F τ x) = letterMk m' F τ (T x) := rfl

end Letter

section Dmap

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) {K : FinExt l} {LL : Type} [Field LL] [Algebra ℚ_[l] LL]
  {V V' : Type} [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V]
  [AddCommGroup V'] [Module LL V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] LL V']
  (ρ : Representation LL ↥(GK K) V) (ρ' : Representation LL ↥(GK K) V') (f : V →ₗ[LL] V')

def tensV : V ⊗[ℚ_[l]] Bst P →ₗ[LL] V' ⊗[ℚ_[l]] Bst P := AlgebraTensorModule.map f LinearMap.id

@[simp] theorem tensV_tmul (v : V) (b : Bst P) : tensV P f (v ⊗ₜ b) = f v ⊗ₜ b := rfl

theorem tensV_onB (T : End ℚ_[l] (Bst P)) (x : V ⊗[ℚ_[l]] Bst P) :
    tensV P f (onB P LL V T x) = onB P LL V' T (tensV P f x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem tensV_stRep (hf : ∀ g v, f (ρ g v) = ρ' g (f v)) (g : ↥(GK K)) (x : V ⊗[ℚ_[l]] Bst P) :
    tensV P f (stRep P ρ g x) = stRep P ρ' g (tensV P f x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [hf]
  | add x y hx hy => simp only [map_add, hx, hy]

variable {ρ ρ' f}

theorem tensV_mem_Dpst (hf : ∀ g v, f (ρ g v) = ρ' g (f v)) (x : V ⊗[ℚ_[l]] Bst P) (hx : x ∈ Dpst P ρ) :
    tensV P f x ∈ Dpst P ρ' := by
  obtain ⟨K', hK⟩ := (mem_Dpst P ρ).mp hx
  exact (mem_Dpst P ρ').mpr ⟨K', fun g hg => by rw [← tensV_stRep P ρ ρ' f hf, hK g hg]⟩

def dmap (hf : ∀ g v, f (ρ g v) = ρ' g (f v)) : ↥(Dpst P ρ) →ₗ[LL] ↥(Dpst P ρ') :=
  (tensV P f).restrict (tensV_mem_Dpst P hf)

@[simp] theorem coe_dmap (hf : ∀ g v, f (ρ g v) = ρ' g (f v)) (x : ↥(Dpst P ρ)) :
    (dmap P hf x : V' ⊗[ℚ_[l]] Bst P) = tensV P f x := rfl

variable (hf : ∀ g v, f (ρ g v) = ρ' g (f v))
include hf

theorem dmap_phiD (x : ↥(Dpst P ρ)) : dmap P hf (phiD P ρ x) = phiD P ρ' (dmap P hf x) :=
  Subtype.ext (tensV_onB P f _ x.1)

theorem dmap_monD (x : ↥(Dpst P ρ)) : dmap P hf (monD P ρ x) = monD P ρ' (dmap P hf x) :=
  Subtype.ext (tensV_onB P f _ x.1)

theorem dmap_actD (g : ↥(GK K)) (x : ↥(Dpst P ρ)) : dmap P hf (actD P ρ g x) = actD P ρ' g (dmap P hf x) :=
  Subtype.ext (tensV_stRep P ρ ρ' f hf g x.1)

theorem dmap_mulD (c : ↥(MaximalUnramifiedExtension l)) (x : ↥(Dpst P ρ)) : dmap P hf (mulD P ρ c x) = mulD P ρ' c (dmap P hf x) :=
  Subtype.ext (tensV_onB P f _ x.1)

theorem dmap_phiU_zpow [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P ρ)] [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P ρ')]
    (n : ℤ) (x : ↥(Dpst P ρ)) :
    dmap P hf (((phiU P ρ ^ n : (End LL ↥(Dpst P ρ))ˣ) : End LL ↥(Dpst P ρ)) x) =
      ((phiU P ρ' ^ n : (End LL ↥(Dpst P ρ'))ˣ) : End LL ↥(Dpst P ρ')) (dmap P hf x) := by
  have hinv : ∀ y, dmap P hf ((((phiU P ρ)⁻¹ : (End LL ↥(Dpst P ρ))ˣ) : End LL ↥(Dpst P ρ)) y) =
      (((phiU P ρ')⁻¹ : (End LL ↥(Dpst P ρ'))ˣ) : End LL ↥(Dpst P ρ')) (dmap P hf y) := by
    intro y
    have h1 : phiD P ρ' (dmap P hf ((((phiU P ρ)⁻¹ : (End LL ↥(Dpst P ρ))ˣ) : End LL ↥(Dpst P ρ)) y)) =
        dmap P hf y := by
      rw [← dmap_phiD, ← coe_phiU, ← End.mul_apply, Units.mul_inv]; rfl
    rw [← h1, ← coe_phiU, ← End.mul_apply, Units.inv_mul]; rfl
  induction n using Int.induction_on generalizing x with
  | zero => simp
  | succ n ih =>
    rw [zpow_add_one, zpow_add_one, Units.val_mul, Units.val_mul, End.mul_apply, End.mul_apply, ih, coe_phiU,
      coe_phiU, dmap_phiD]
  | pred n ih =>
    rw [zpow_sub_one, zpow_sub_one, Units.val_mul, Units.val_mul, End.mul_apply, End.mul_apply, ih, hinv]

end Dmap

section Lin

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) (ι : Om l ≃+* ℂ) {K LL : FinExt l}
  {V V' : Type} [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V]
  [AddCommGroup V'] [Module ↥LL.1 V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] ↥LL.1 V']
  {ρ : Representation ↥LL.1 ↥(GK K) V} {ρ' : Representation ↥LL.1 ↥(GK K) V'} {f : V →ₗ[↥LL.1] V'}
  (hf : ∀ g v, f (ρ g v) = ρ' g (f v))

def wdLin : WDSpace P ι ρ →ₗ[ℂ] WDSpace P ι ρ' :=
  letI := algC ι LL
  letterLin (mulD P ρ) (mulD P ρ') ℂ (urC ι) (dmap P hf) fun c => LinearMap.ext fun x => dmap_mulD P hf c x

@[simp] theorem wdLin_mk (x : ↥(Dpst P ρ)) : wdLin P ι hf (wdMk P ι ρ x) = wdMk P ι ρ' (dmap P hf x) := rfl

theorem wdLin_wdN (y : WDSpace P ι ρ) : wdLin P ι hf (wdN P ι ρ y) = wdN P ι ρ' (wdLin P ι hf y) := by
  have : (wdLin P ι hf).comp (wdN P ι ρ) = (wdN P ι ρ').comp (wdLin P ι hf) :=
    LinearMap.ext_on_range (span_wdMk P ι ρ) fun x => by
      simp only [LinearMap.comp_apply, wdN_mk, wdLin_mk, dmap_monD]
  exact LinearMap.congr_fun this y

end Lin

section Weil

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) (ι : Om l ≃+* ℂ)
  {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)}
  {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
  (Bw : LocBridge l E Ω (Dec (F := E) A) O) (h : IsPlaceOver A w) (hj : Induces Bw)
  {LL : FinExt l}
  {V V' : Type} [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V]
  [AddCommGroup V'] [Module ↥LL.1 V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] ↥LL.1 V']
  {ρ : Representation ↥LL.1 ↥(GK Bw.Kw) V} {ρ' : Representation ↥LL.1 ↥(GK Bw.Kw) V'} {f : V →ₗ[↥LL.1] V'}
  (hf : ∀ g v, f (ρ g v) = ρ' g (f v))
  [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P ρ)] [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P ρ')]

theorem dmap_weilD (σ : ↥(Weil h)) (x : ↥(Dpst P ρ)) :
    dmap P hf (weilD Bw h P ρ σ x) = weilD Bw h P ρ' σ (dmap P hf x) := by
  rw [weilD_apply, weilD_apply]
  exact (dmap_actD P hf _ _).trans (congrArg _ (dmap_phiU_zpow P hf _ x))

theorem wdLin_wdRho (σ : ↥(Weil h)) (y : WDSpace P ι ρ) :
    wdLin P ι hf (wdRho P ι Bw h hj ρ σ y) = wdRho P ι Bw h hj ρ' σ (wdLin P ι hf y) := by
  have : (wdLin P ι hf).comp (wdRho P ι Bw h hj ρ σ) = (wdRho P ι Bw h hj ρ' σ).comp (wdLin P ι hf) :=
    LinearMap.ext_on_range (span_wdMk P ι ρ) fun x => by
      simp only [LinearMap.comp_apply, wdRho_mk, wdLin_mk, dmap_weilD]
  exact LinearMap.congr_fun this y

end Weil

section Charpoly

theorem charpoly_dvd_of_surjective {K M M' : Type} [Field K] [AddCommGroup M] [Module K M] [FiniteDimensional K M]
    [AddCommGroup M'] [Module K M'] [FiniteDimensional K M'] (F : M →ₗ[K] M') (hF : Function.Surjective F)
    (T : Module.End K M) (T' : Module.End K M') (hT : ∀ x, F (T x) = T' (F x)) :
    T'.charpoly ∣ T.charpoly := by
  have hA : ∀ x ∈ LinearMap.ker F, T x ∈ LinearMap.ker F := fun x hx => by
    rw [LinearMap.mem_ker] at hx ⊢; rw [hT, hx, map_zero]
  rw [GlobalTheory.CuspGL.charpoly_eq_restrict_mul_mapQ (LinearMap.ker F) T hA]
  refine Dvd.intro_left (T.restrict hA).charpoly ?_
  let e := F.quotKerEquivOfSurjective hF
  have he : (LinearMap.ker F).mapQ (LinearMap.ker F) T (fun x hx => hA x hx) = e.symm.conj T' := by
    refine LinearMap.ext fun y => ?_
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ y
    rw [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.symm_symm]
    apply e.injective
    rw [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, Submodule.mkQ_apply, Submodule.mapQ_apply]
    simp only [e, LinearMap.quotKerEquivOfSurjective_apply_mk, hT]
    rfl
  rw [he, LinearEquiv.charpoly_conj]

theorem isNilpotent_zpow_sub_one {R : Type} [Ring R] (u : Rˣ) (hu : IsNilpotent ((u : R) - 1)) (n : ℤ) :
    IsNilpotent (((u ^ n : Rˣ) : R) - 1) := by
  have hnat : ∀ k : ℕ, IsNilpotent ((u : R) ^ k - 1) := fun k => by
    rw [← geom_sum_mul]
    refine Commute.isNilpotent_mul_left ?_ hu
    exact Commute.sum_left _ _ _ fun i _ =>
      ((Commute.refl (u : R)).sub_right (Commute.one_right _)).pow_left i
  rcases n with k | k
  · rw [Int.ofNat_eq_natCast, zpow_natCast, Units.val_pow_eq_pow_val]
    exact hnat k
  · rw [zpow_negSucc]
    have e : (((u ^ (k + 1))⁻¹ : Rˣ) : R) - 1 = (((u ^ (k + 1))⁻¹ : Rˣ) : R) * -(((u : R) ^ (k + 1)) - 1) := by
      rw [mul_neg, mul_sub, mul_one, ← Units.val_pow_eq_pow_val, Units.inv_mul]; abel
    rw [e]
    refine Commute.isNilpotent_mul_left ?_ (hnat (k + 1)).neg
    refine Commute.neg_right ?_
    rw [← Units.val_pow_eq_pow_val]
    exact (Commute.units_inv_left (Commute.refl _)).sub_right (Commute.one_right _)

theorem commute_isNilpotent_of_unipotent {R : Type} [Ring R] {a b : R} (u : Rˣ) (hu : IsNilpotent ((u : R) - 1))
    (n : ℤ) (hc : Commute (u : R) b) (hb : b = a * ((u ^ n : Rˣ) : R)) : Commute a b ∧ IsNilpotent (b - a) := by
  have hUb : Commute ((u ^ n : Rˣ) : R) b := hc.units_zpow_left n
  have ha : a = b * (((u ^ n)⁻¹ : Rˣ) : R) := by rw [hb, mul_assoc, Units.mul_inv, mul_one]
  have haU : Commute a ((u ^ n : Rˣ) : R) := by
    rw [ha]
    exact hUb.symm.mul_left (Commute.units_inv_left (Commute.refl _))
  refine ⟨?_, ?_⟩
  · rw [hb]; exact (Commute.refl a).mul_right haU
  · have e : b - a = a * (((u ^ n : Rˣ) : R) - 1) := by rw [hb, mul_sub, mul_one]
    rw [e]
    exact Commute.isNilpotent_mul_left (haU.sub_right (Commute.one_right _)) (isNilpotent_zpow_sub_one u hu n)

end Charpoly

section Semisimple

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) (ι : Om l ≃+* ℂ)
  {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)}
  {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
  (Bw : LocBridge l E Ω (Dec (F := E) A) O) (h : IsPlaceOver A w) (hj : Induces Bw)
  {LL : FinExt l} {V : Type} [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V]
  (ρ : Representation ↥LL.1 ↥(GK Bw.Kw) V) [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P ρ)]

theorem charpoly_wdRep (σ : ↥(Weil h)) :
    ((wdRep P ι Bw h hj ρ).ρ σ).charpoly = (wdRho P ι Bw h hj ρ σ).charpoly := by
  obtain ⟨u, -, hu, -, hcomm, hρ⟩ := wdRep_spec P ι Bw h hj ρ
  obtain ⟨h1, h2⟩ := commute_isNilpotent_of_unipotent u hu (deg σ) (hcomm σ) (hρ σ)
  exact GlobalTheory.WeilDeligne.charpoly_eq_of_isNilpotent_sub h1 h2

theorem charPol_wdPst [FiniteDimensional ↥LL.1 V] (hV : IsPst P ρ) (σ : ↥(Weil h)) :
    WD.charPol (wdPst P ι Bw h hj ρ) σ = (wdRho P ι Bw h hj ρ σ).charpoly := by
  rw [wdPst_of_isPst ι Bw h hj hV, WD.charPol_mk, charpoly_wdRep]

end Semisimple

end GlobalTheory.Pst.DpstMap
