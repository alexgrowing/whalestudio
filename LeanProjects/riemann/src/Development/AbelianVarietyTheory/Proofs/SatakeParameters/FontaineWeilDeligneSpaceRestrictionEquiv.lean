import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RestrictsSelf
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeilDeligneParamAboveLIndependentLocalEmbedding
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormVZpowDegEq
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL

noncomputable section

namespace GlobalTheory.Pst.ResLetter

open TensorProduct Module

theorem zpow_intertwine {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (T : M →+ N) (a : (Module.End R M)ˣ) (b : (Module.End R N)ˣ) (hab : ∀ x, T ((a : Module.End R M) x) = (b : Module.End R N) (T x)) (n : ℤ) (x : M) :
    T (((a ^ n : (Module.End R M)ˣ) : Module.End R M) x) = ((b ^ n : (Module.End R N)ˣ) : Module.End R N) (T x) := by
  have hinv : ∀ y, T (((a⁻¹ : (Module.End R M)ˣ) : Module.End R M) y) =
      ((b⁻¹ : (Module.End R N)ˣ) : Module.End R N) (T y) := by
    intro y
    have h1 : (b : Module.End R N) (T (((a⁻¹ : (Module.End R M)ˣ) : Module.End R M) y)) = T y := by
      rw [← hab, ← Module.End.mul_apply, ← Units.val_mul, mul_inv_cancel, Units.val_one, Module.End.one_apply]
    rw [← h1, ← Module.End.mul_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one, Module.End.one_apply]
  induction n using Int.induction_on generalizing x with
  | zero => simp
  | succ n ih =>
    rw [zpow_add_one, zpow_add_one, Units.val_mul, Units.val_mul, Module.End.mul_apply, Module.End.mul_apply, ih, hab]
  | pred n ih =>
    rw [zpow_sub_one, zpow_sub_one, Units.val_mul, Units.val_mul, Module.End.mul_apply, Module.End.mul_apply, ih, hinv]

section Gen

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) {LL : FinExt l} {V : Type} [AddCommGroup V]
  [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] {K K' : FinExt l}
  (ρ : Representation ↥LL.1 ↥(GK K) V) (hle : K.1 ≤ K'.1)

def toRes : ↥(Dpst P ρ) →+ ↥(Dpst P (GlobalTheory.Pst.resTo ρ hle)) where
  toFun x := ⟨x.1, by rw [GlobalTheory.Pst.Dpst_resTo]; exact x.2⟩
  map_zero' := rfl
  map_add' _ _ := rfl

def ofRes : ↥(Dpst P (GlobalTheory.Pst.resTo ρ hle)) →+ ↥(Dpst P ρ) where
  toFun x := ⟨x.1, by rw [← GlobalTheory.Pst.Dpst_resTo P ρ hle]; exact x.2⟩
  map_zero' := rfl
  map_add' _ _ := rfl

theorem toRes_ofRes (x : ↥(Dpst P (GlobalTheory.Pst.resTo ρ hle))) : toRes P ρ hle (ofRes P ρ hle x) = x := rfl
theorem ofRes_toRes (x : ↥(Dpst P ρ)) : ofRes P ρ hle (toRes P ρ hle x) = x := rfl

theorem toRes_smul (a : ↥LL.1) (x : ↥(Dpst P ρ)) :
    toRes P ρ hle (a • x) = (RingHom.id _ a) • toRes P ρ hle x := rfl
theorem ofRes_smul (a : ↥LL.1) (x : ↥(Dpst P (GlobalTheory.Pst.resTo ρ hle))) :
    ofRes P ρ hle (a • x) = (RingHom.id _ a) • ofRes P ρ hle x := rfl

theorem toRes_mulD (c : ↥(MaximalUnramifiedExtension l)) (x : ↥(Dpst P ρ)) :
    toRes P ρ hle (mulD P ρ c x) = mulD P (GlobalTheory.Pst.resTo ρ hle) c (toRes P ρ hle x) := rfl
theorem ofRes_mulD (c : ↥(MaximalUnramifiedExtension l)) (x : ↥(Dpst P (GlobalTheory.Pst.resTo ρ hle))) :
    ofRes P ρ hle (mulD P (GlobalTheory.Pst.resTo ρ hle) c x) = mulD P ρ c (ofRes P ρ hle x) := rfl
theorem toRes_phiD (x : ↥(Dpst P ρ)) :
    toRes P ρ hle (phiD P ρ x) = phiD P (GlobalTheory.Pst.resTo ρ hle) (toRes P ρ hle x) := rfl
theorem toRes_monD (x : ↥(Dpst P ρ)) :
    toRes P ρ hle (monD P ρ x) = monD P (GlobalTheory.Pst.resTo ρ hle) (toRes P ρ hle x) := rfl

theorem toRes_actD (g : ↥(GK K)) (g' : ↥(GK K')) (hg : (g' : GQ l) = (g : GQ l)) (x : ↥(Dpst P ρ)) :
    toRes P ρ hle (actD P ρ g x) = actD P (GlobalTheory.Pst.resTo ρ hle) g' (toRes P ρ hle x) := by
  have e : Subgroup.inclusion (GK_le hle) g' = g := Subtype.ext hg
  subst e
  rfl

theorem toRes_phiU_zpow [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P ρ)]
    [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P (GlobalTheory.Pst.resTo ρ hle))] (n : ℤ) (x : ↥(Dpst P ρ)) :
    toRes P ρ hle (((phiU P ρ ^ n : (End ↥LL.1 ↥(Dpst P ρ))ˣ) : End ↥LL.1 ↥(Dpst P ρ)) x) =
      ((phiU P (GlobalTheory.Pst.resTo ρ hle) ^ n : (End ↥LL.1 ↥(Dpst P (GlobalTheory.Pst.resTo ρ hle)))ˣ) :
        End ↥LL.1 ↥(Dpst P (GlobalTheory.Pst.resTo ρ hle))) (toRes P ρ hle x) :=
  zpow_intertwine (toRes P ρ hle) (phiU P ρ) (phiU P (GlobalTheory.Pst.resTo ρ hle)) (fun y => toRes_phiD P ρ hle y) n x

end Gen

section Weil

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) {K L Ω : Type} [Field Ω] [Field K] [NumberField K]
  [Algebra K Ω] [IsAlgClosure K Ω] [Field L] [NumberField L] [Algebra L Ω] [IsAlgClosure L Ω]
  {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 K)} {v' : HeightOneSpectrum (𝓞 L)}
  {h : IsPlaceOver A v} {h' : IsPlaceOver A v'}
  {O O' : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] [CommRing O'] [Algebra ℤ_[l] O']
  [TopologicalSpace O'] {Bw : LocBridge l K Ω (Dec (F := K) A) O} {Bw' : LocBridge l L Ω (Dec (F := L) A) O'}
  {LL : FinExt l} {V : Type} [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V]

theorem alpha_eq (hj : GlobalTheory.Pst.Induces Bw) (hj' : GlobalTheory.Pst.Induces Bw') (σ : Weil h) (σ' : Weil h')
    (hσ : ∀ z : Ω, (σ : G K Ω) z = (σ' : G L Ω) z) : alpha l σ' = alpha l σ := by
  have e := GlobalTheory.LocLanglands.normV_zpow_deg_eq σ' σ hσ
  rw [GlobalTheory.Pst.normV_eq_pow (hj'.mem_placesOver h'), GlobalTheory.Pst.normV_eq_pow (hj.mem_placesOver h)] at e
  push_cast at e
  simp only [← zpow_natCast, ← zpow_mul] at e
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  exact zpow_right_injective₀ (zero_lt_one.trans hl) hl.ne' e

variable (ρ : Representation ↥LL.1 ↥(GK Bw.Kw) V) (hle : Bw.Kw.1 ≤ Bw'.Kw.1)
  [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P ρ)] [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P (GlobalTheory.Pst.resTo ρ hle))]

theorem toRes_weilD (σ : Weil h) (σ' : Weil h')
    (hg : (weilToGK Bw' h' σ' : GQ l) = (weilToGK Bw h σ : GQ l)) (ha : alpha l σ' = alpha l σ)
    (x : ↥(Dpst P ρ)) :
    toRes P ρ hle (weilD Bw h P ρ σ x) = weilD Bw' h' P (GlobalTheory.Pst.resTo ρ hle) σ' (toRes P ρ hle x) := by
  calc toRes P ρ hle (weilD Bw h P ρ σ x)
      = toRes P ρ hle (actD P ρ (weilToGK Bw h σ)
          (((phiU P ρ ^ (-alpha l σ) : (End ↥LL.1 ↥(Dpst P ρ))ˣ) : End ↥LL.1 ↥(Dpst P ρ)) x)) := rfl
    _ = actD P (GlobalTheory.Pst.resTo ρ hle) (weilToGK Bw' h' σ') (toRes P ρ hle
          (((phiU P ρ ^ (-alpha l σ) : (End ↥LL.1 ↥(Dpst P ρ))ˣ) : End ↥LL.1 ↥(Dpst P ρ)) x)) :=
        toRes_actD P ρ hle _ _ hg _
    _ = actD P (GlobalTheory.Pst.resTo ρ hle) (weilToGK Bw' h' σ')
          (((phiU P (GlobalTheory.Pst.resTo ρ hle) ^ (-alpha l σ) : (End ↥LL.1 ↥(Dpst P (GlobalTheory.Pst.resTo ρ hle)))ˣ) :
            End ↥LL.1 ↥(Dpst P (GlobalTheory.Pst.resTo ρ hle))) (toRes P ρ hle x)) :=
        congrArg _ (toRes_phiU_zpow P ρ hle _ x)
    _ = weilD Bw' h' P (GlobalTheory.Pst.resTo ρ hle) σ' (toRes P ρ hle x) := by rw [← ha]; rfl

variable (ι : Om l ≃+* ℂ)

theorem wdHom_ext {M : Type*} [AddCommGroup M] [Module ℂ M] {f g : WDSpace P ι ρ →ₗ[ℂ] M}
    (hfg : ∀ x, f (wdMk P ι ρ x) = g (wdMk P ι ρ x)) : f = g :=
  LinearMap.ext_on_range (span_wdMk P ι ρ) hfg

def resEquiv : WDSpace P ι ρ ≃ₗ[ℂ] WDSpace P ι (GlobalTheory.Pst.resTo ρ hle) :=
  letI := algC ι LL
  LinearEquiv.ofLinear
    (EnlargeCoeff.chg (mulD P ρ) (mulD P (GlobalTheory.Pst.resTo ρ hle)) ℂ (urC ι) (RingHom.id _) (fun _ => rfl)
      (toRes P ρ hle) (toRes_smul P ρ hle) (toRes_mulD P ρ hle))
    (EnlargeCoeff.chg (mulD P (GlobalTheory.Pst.resTo ρ hle)) (mulD P ρ) ℂ (urC ι) (RingHom.id _) (fun _ => rfl)
      (ofRes P ρ hle) (ofRes_smul P ρ hle) (ofRes_mulD P ρ hle))
    (letter_hom_ext _ _ _ fun x => by
      rw [LinearMap.comp_apply, EnlargeCoeff.chg_mk, EnlargeCoeff.chg_mk, toRes_ofRes, LinearMap.id_apply])
    (letter_hom_ext _ _ _ fun x => by
      rw [LinearMap.comp_apply, EnlargeCoeff.chg_mk, EnlargeCoeff.chg_mk, ofRes_toRes, LinearMap.id_apply])

theorem resEquiv_mk (x : ↥(Dpst P ρ)) :
    resEquiv P ρ hle ι (wdMk P ι ρ x) = wdMk P ι (GlobalTheory.Pst.resTo ρ hle) (toRes P ρ hle x) :=
  letI := algC ι LL
  EnlargeCoeff.chg_mk _ _ _ _ _ _ _ _ (toRes_mulD P ρ hle) x

theorem resEquiv_wdN (y : WDSpace P ι ρ) :
    resEquiv P ρ hle ι (wdN P ι ρ y) = wdN P ι (GlobalTheory.Pst.resTo ρ hle) (resEquiv P ρ hle ι y) := by
  have : (resEquiv P ρ hle ι).toLinearMap ∘ₗ wdN P ι ρ =
      wdN P ι (GlobalTheory.Pst.resTo ρ hle) ∘ₗ (resEquiv P ρ hle ι).toLinearMap :=
    wdHom_ext P ρ ι fun x => by
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, wdN_mk, resEquiv_mk, toRes_monD]
  exact LinearMap.congr_fun this y

theorem resEquiv_wdRho (hj : GlobalTheory.Pst.Induces Bw) (hj' : GlobalTheory.Pst.Induces Bw') (σ : Weil h) (σ' : Weil h')
    (hg : (weilToGK Bw' h' σ' : GQ l) = (weilToGK Bw h σ : GQ l)) (ha : alpha l σ' = alpha l σ)
    (y : WDSpace P ι ρ) :
    resEquiv P ρ hle ι (wdRho P ι Bw h hj ρ σ y) =
      wdRho P ι Bw' h' hj' (GlobalTheory.Pst.resTo ρ hle) σ' (resEquiv P ρ hle ι y) := by
  have : (resEquiv P ρ hle ι).toLinearMap ∘ₗ wdRho P ι Bw h hj ρ σ =
      wdRho P ι Bw' h' hj' (GlobalTheory.Pst.resTo ρ hle) σ' ∘ₗ (resEquiv P ρ hle ι).toLinearMap :=
    wdHom_ext P ρ ι fun x => by
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, wdRho_mk, resEquiv_mk, toRes_weilD P ρ hle σ σ' hg ha]
  exact LinearMap.congr_fun this y

end Weil

theorem wdSpace_resTo_equiv : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (ι : Qbar l ≃+* ℂ) (K L Ω : Type) [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω] [Field L] [NumberField L] [Algebra L Ω] [IsAlgClosure L Ω] [Algebra K L] [IsScalarTower K L Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 K)) (v' : HeightOneSpectrum (𝓞 L)) (h : IsPlaceOver A v) (h' : IsPlaceOver A v') (O O' : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] [CommRing O'] [Algebra ℤ_[l] O'] [TopologicalSpace O'] (Bw : LocBridge l K Ω (Dec (F := K) A) O) (Bw' : LocBridge l L Ω (Dec (F := L) A) O') (hj : GlobalTheory.Pst.Induces Bw) (hj' : GlobalTheory.Pst.Induces Bw') (hle : Bw.Kw.1 ≤ Bw'.Kw.1), (∀ (σ : Weil h) (σ' : Weil h'), (∀ z : Ω, (σ : G K Ω) z = (σ' : G L Ω) z) → (weilToGK Bw' h' σ' : GQ l) = (weilToGK Bw h σ : GQ l)) → ∀ (LL : FinExt l) (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK Bw.Kw) V) [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P ρ)] [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P (GlobalTheory.Pst.resTo ρ hle))], IsPst P ρ → ∃ e : WDSpace P ι ρ ≃ₗ[ℂ] WDSpace P ι (GlobalTheory.Pst.resTo ρ hle), (∀ (σ : Weil h) (σ' : Weil h'), (∀ z : Ω, (σ : G K Ω) z = (σ' : G L Ω) z) → ∀ x, e (wdRho P ι Bw h hj ρ σ x) = wdRho P ι Bw' h' hj' (GlobalTheory.Pst.resTo ρ hle) σ' (e x)) ∧ ∀ x, e (wdN P ι ρ x) = wdN P ι (GlobalTheory.Pst.resTo ρ hle) (e x) := by
  intro l _ P ι K L Ω _ _ _ _ _ _ _ _ _ _ _ A v v' h h' O O' _ _ _ _ _ _ Bw Bw' hj hj' hle hW LL V _ _ _ _ _ ρ _ _ _
  exact ⟨resEquiv P ρ hle ι, fun σ σ' hσ x =>
    resEquiv_wdRho P ρ hle ι hj hj' σ σ' (hW σ σ' hσ) (alpha_eq hj hj' σ σ' hσ) x,
    fun x => resEquiv_wdN P ρ hle ι x⟩

end GlobalTheory.Pst.ResLetter
