import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.GermCompatId
import Development.AutomorphicArithmetic.GenericGermInjectivity.CoverGeneric
import Development.AutomorphicArithmetic.CommutativeAlgebra.FunctionFieldOfFiniteEtaleCover
import Development.AutomorphicArithmetic.Foundations.PullbackRestriction.AppRes
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FlatHermRootLineDegree
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.GenericGermDifferentialFormPullbackDominantStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RiemannFormHermitianLattice
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CechHomologyEquivFamStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.GenericGermDifferentialFormRestrictAffineOpenStatement

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.HodgeCoh GlobalTheory.CechDR GlobalTheory.PD KaehlerDifferential GlobalTheory.W1 GlobalTheory.W1.Lef

set_option autoImplicit false

noncomputable section

namespace UpperTheory.PullbackConnectingMap

section Signs

variable {k : Type} [Field k] {ι κ : Type} [LinearOrder ι] [LinearOrder κ] {E E' : Type}
  [AddCommGroup E] [Module k E] [AddCommGroup E'] [Module k E']

open Classical in
theorem pullC_apply (τ : κ → ι) (φ : E →ₗ[k] E') (c : Finset ι → E) (s : Finset κ) :
    pullC τ φ c s = if Set.InjOn τ s then sortSign τ s • φ (c (s.image τ)) else 0 := rfl

theorem pullC_inj (τ : κ → ι) (φ : E →ₗ[k] E') (c : Finset ι → E) {s : Finset κ}
    (h : Set.InjOn τ s) : pullC τ φ c s = sortSign τ s • φ (c (s.image τ)) := by
  rw [pullC_apply, if_pos h]

theorem pullC_ninj (τ : κ → ι) (φ : E →ₗ[k] E') (c : Finset ι → E) {s : Finset κ}
    (h : ¬ Set.InjOn τ s) : pullC τ φ c s = 0 := by
  rw [pullC_apply, if_neg h]

private theorem cubeSign_eq_prod' {α : Type} [LinearOrder α] (t : Finset α) (i : α) :
    cubeSign t i = ∏ y ∈ t, if y < i then (-1 : ℤ) else 1 := by
  rw [cubeSign.eq_1, Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]

private theorem sortSign_eq_sortSign_erase_mul {α β : Type} [LinearOrder α] [LinearOrder β] (τ : β → α) {s : Finset β}
    {j : β} (hj : j ∈ s) :
    sortSign τ s = sortSign τ (s.erase j) * ((∏ y ∈ s, if j < y ∧ τ y < τ j then (-1 : ℤ) else 1) *
      ∏ y ∈ s, if y < j ∧ τ j < τ y then (-1 : ℤ) else 1) := by
  rw [sortSign.eq_1, sortSign.eq_1, ← Finset.mul_prod_erase s _ hj]
  have h1 : ∀ a ∈ s.erase j, (∏ b ∈ s, if a < b ∧ τ b < τ a then (-1 : ℤ) else 1) =
      (if a < j ∧ τ j < τ a then -1 else 1) * ∏ b ∈ s.erase j, if a < b ∧ τ b < τ a then -1 else 1 :=
    fun a _ => (Finset.mul_prod_erase s _ hj).symm
  rw [Finset.prod_congr rfl h1, Finset.prod_mul_distrib]
  have h2 : (∏ a ∈ s.erase j, if a < j ∧ τ j < τ a then (-1 : ℤ) else 1) =
      ∏ a ∈ s, if a < j ∧ τ j < τ a then -1 else 1 := by
    rw [← Finset.mul_prod_erase s _ hj]
    simp
  rw [h2]
  ring

private theorem sortSign_mul_cubeSign_image {α β : Type} [LinearOrder α] [LinearOrder β] (τ : β → α) {s : Finset β}
    {j : β} (hj : j ∈ s) (hinj : Set.InjOn τ s) :
    sortSign τ s * cubeSign (s.image τ) (τ j) = cubeSign s j * sortSign τ (s.erase j) := by
  rw [sortSign_eq_sortSign_erase_mul τ hj, cubeSign_eq_prod', cubeSign_eq_prod',
    Finset.prod_image (fun x hx y hy h => hinj hx hy h)]
  have key : ∀ y ∈ s, ((if j < y ∧ τ y < τ j then (-1 : ℤ) else 1) *
      (if y < j ∧ τ j < τ y then -1 else 1)) * (if τ y < τ j then -1 else 1) =
      if y < j then -1 else 1 := by
    intro y hy
    by_cases hyj : y = j
    · subst hyj
      simp
    have hne : τ y ≠ τ j := fun e => hyj (hinj hy hj e)
    split_ifs <;> simp_all <;> order
  rw [mul_assoc, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib, Finset.prod_congr rfl key]
  ring

private theorem prod_mul_prod_eq_one_of_sq_one {β : Type} {s : Finset β} (f : β → ℤ) (hf : ∀ y, f y * f y = 1) :
    (∏ y ∈ s, f y) * ∏ y ∈ s, f y = 1 := by
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_eq_one fun y _ => hf y

private theorem cubeSign_mul_sortSign_erase_eq_neg_of_collide {α β : Type} [LinearOrder α] [LinearOrder β] (τ : β → α) {s : Finset β}
    {a b : β} (ha : a ∈ s) (hb : b ∈ s) (hab : a < b) (he : τ a = τ b)
    (hinj : Set.InjOn τ (s.erase b)) :
    cubeSign s a * sortSign τ (s.erase a) = -(cubeSign s b * sortSign τ (s.erase b)) := by
  have sq : ∀ (P : β → Prop) [DecidablePred P],
      (∏ y ∈ s, if P y then (-1 : ℤ) else 1) * (∏ y ∈ s, if P y then (-1 : ℤ) else 1) = 1 :=
    fun P _ => prod_mul_prod_eq_one_of_sq_one _ fun y => by split_ifs <;> norm_num
  have key : cubeSign s b * ((∏ y ∈ s, if b < y ∧ τ y < τ b then (-1 : ℤ) else 1) *
      ∏ y ∈ s, if y < b ∧ τ b < τ y then (-1 : ℤ) else 1) =
      -(cubeSign s a * ((∏ y ∈ s, if a < y ∧ τ y < τ a then (-1 : ℤ) else 1) *
      ∏ y ∈ s, if y < a ∧ τ a < τ y then (-1 : ℤ) else 1)) := by
    rw [cubeSign_eq_prod', cubeSign_eq_prod', ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib,
      ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    have pt : ∀ y ∈ s, (if y < b then (-1 : ℤ) else 1) * ((if b < y ∧ τ y < τ b then -1 else 1) *
        (if y < b ∧ τ b < τ y then -1 else 1)) =
        (if y = a then -1 else 1) * ((if y < a then (-1 : ℤ) else 1) *
        ((if a < y ∧ τ y < τ a then -1 else 1) * (if y < a ∧ τ a < τ y then -1 else 1))) := by
      intro y hy
      by_cases hya : y = a
      · subst hya
        simp [hab, he]
      by_cases hyb : y = b
      · subst hyb
        simp [hya, he, lt_asymm hab]
      have hne : τ y ≠ τ a := fun e =>
        hya (hinj (Finset.mem_erase.2 ⟨hyb, hy⟩) (Finset.mem_erase.2 ⟨hab.ne, ha⟩) e)
      rw [← he]
      rcases lt_or_gt_of_ne hne with h3 | h3 <;> rcases lt_or_gt_of_ne hya with h1 | h1 <;>
        rcases lt_or_gt_of_ne hyb with h2 | h2
      all_goals first
        | (exfalso; order)
        | simp [h1, h2, h3, hya, hyb, lt_asymm h1, lt_asymm h2, lt_asymm h3]
    rw [Finset.prod_congr rfl pt, Finset.prod_mul_distrib, Finset.prod_ite_eq' s a, if_pos ha]
    ring
  have eA := sortSign_eq_sortSign_erase_mul τ ha
  have eB := sortSign_eq_sortSign_erase_mul τ hb
  have s1 := sq (fun y => a < y ∧ τ y < τ a)
  have s2 := sq (fun y => y < a ∧ τ a < τ y)
  have s3 := sq (fun y => b < y ∧ τ y < τ b)
  have s4 := sq (fun y => y < b ∧ τ b < τ y)
  linear_combination (-(cubeSign s a) * sortSign τ (s.erase a)) * s1
    + (-(cubeSign s a) * sortSign τ (s.erase a) * ((∏ y ∈ s, if a < y ∧ τ y < τ a then (-1 : ℤ) else 1) *
      (∏ y ∈ s, if a < y ∧ τ y < τ a then (-1 : ℤ) else 1))) * s2
    + (-(cubeSign s a) * ((∏ y ∈ s, if a < y ∧ τ y < τ a then (-1 : ℤ) else 1) *
      ∏ y ∈ s, if y < a ∧ τ a < τ y then (-1 : ℤ) else 1)) * eA
    + (-(cubeSign s b) * sortSign τ (s.erase b)) * s3
    + (-(cubeSign s b) * sortSign τ (s.erase b) * ((∏ y ∈ s, if b < y ∧ τ y < τ b then (-1 : ℤ) else 1) *
      (∏ y ∈ s, if b < y ∧ τ y < τ b then (-1 : ℤ) else 1))) * s4
    + (-(cubeSign s b) * ((∏ y ∈ s, if b < y ∧ τ y < τ b then (-1 : ℤ) else 1) *
      ∏ y ∈ s, if y < b ∧ τ b < τ y then (-1 : ℤ) else 1)) * eB
    + sortSign τ s * key

private theorem injOn_erase_of_injOn_erase_of_eq {α β : Type} [LinearOrder β] (τ : β → α) {s : Finset β} {a b : β}
    (ha : a ∈ s) (hab : a ≠ b) (he : τ a = τ b) (h : Set.InjOn τ ↑(s.erase b)) :
    Set.InjOn τ ↑(s.erase a) := by
  intro x hx y hy hxy
  rw [Finset.mem_coe, Finset.mem_erase] at hx hy
  by_cases hxb : x = b
  · by_cases hyb : y = b
    · rw [hxb, hyb]
    · subst hxb
      exact absurd (h (Finset.mem_erase.2 ⟨hyb, hy.2⟩) (Finset.mem_erase.2 ⟨hab, ha⟩)
        (hxy.symm.trans he.symm)) hy.1
  · by_cases hyb : y = b
    · subst hyb
      exact absurd (h (Finset.mem_erase.2 ⟨hxb, hx.2⟩) (Finset.mem_erase.2 ⟨hab, ha⟩)
        (hxy.trans he.symm)) hx.1
    · exact h (Finset.mem_erase.2 ⟨hxb, hx.2⟩) (Finset.mem_erase.2 ⟨hyb, hy.2⟩) hxy

private theorem image_erase_eq_erase_image_of_injOn {α β : Type} [LinearOrder α] [LinearOrder β] (τ : β → α) {s : Finset β}
    {j : β} (hj : j ∈ s) (hinj : Set.InjOn τ s) :
    (s.image τ).erase (τ j) = (s.erase j).image τ := by
  ext x
  simp only [Finset.mem_erase, Finset.mem_image]
  constructor
  · rintro ⟨hx, y, hy, rfl⟩
    exact ⟨y, ⟨fun e => hx (by rw [e]), hy⟩, rfl⟩
  · rintro ⟨y, ⟨hyj, hy⟩, rfl⟩
    exact ⟨fun e => hyj (hinj hy hj e), y, hy, rfl⟩

private theorem image_erase_eq_of_eq_apply {α β : Type} [LinearOrder α] [LinearOrder β] (τ : β → α) {s : Finset β}
    {a b : β} (ha : a ∈ s) (hb : b ∈ s) (hab : a ≠ b) (he : τ a = τ b) :
    (s.erase a).image τ = (s.erase b).image τ := by
  ext x
  simp only [Finset.mem_image, Finset.mem_erase]
  constructor
  · rintro ⟨y, ⟨hya, hy⟩, rfl⟩
    by_cases hyb : y = b
    · exact ⟨a, ⟨hab, ha⟩, by rw [hyb, he]⟩
    · exact ⟨y, ⟨hyb, hy⟩, rfl⟩
  · rintro ⟨y, ⟨hyb, hy⟩, rfl⟩
    by_cases hya : y = a
    · exact ⟨b, ⟨hab.symm, hb⟩, by rw [hya, he]⟩
    · exact ⟨y, ⟨hya, hy⟩, rfl⟩

theorem pullC_delta (τ : κ → ι) (φ : E →ₗ[k] E') (c : Finset ι → E) :
    pullC τ φ (deltaL k ι E c) = deltaL k κ E' (pullC τ φ c) := by
  funext s
  rw [pullC_apply]
  simp only [deltaL.eq_1, LinearMap.coe_mk, AddHom.coe_mk, DI.delta.eq_1]
  split_ifs with hinj
  · rw [map_sum, Finset.smul_sum, Finset.sum_image (fun x hx y hy h => hinj hx hy h)]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hinj' : Set.InjOn τ ↑(s.erase j) := hinj.mono (Finset.coe_subset.2 (Finset.erase_subset j s))
    rw [pullC_inj τ φ c hinj', map_zsmul, smul_smul, smul_smul, sortSign_mul_cubeSign_image τ hj hinj,
      image_erase_eq_erase_image_of_injOn τ hj hinj]
  · have hcol : ∃ a ∈ s, ∃ b ∈ s, a < b ∧ τ a = τ b := by
      by_contra hno
      push_neg at hno
      apply hinj
      intro x hx y hy hxy
      rcases lt_trichotomy x y with h | h | h
      · exact absurd hxy (hno x hx y hy h)
      · exact h
      · exact absurd hxy.symm (hno y hy x hx h)
    obtain ⟨a, ha, b, hb, hab, he⟩ := hcol
    rw [Finset.sum_eq_add_of_mem a b ha hb hab.ne ?_]
    · by_cases hia : Set.InjOn τ ↑(s.erase a)
      · have hib : Set.InjOn τ ↑(s.erase b) := injOn_erase_of_injOn_erase_of_eq τ hb hab.ne' he.symm hia
        rw [pullC_inj τ φ c hia, pullC_inj τ φ c hib, smul_smul, smul_smul,
          image_erase_eq_of_eq_apply τ ha hb hab.ne he, cubeSign_mul_sortSign_erase_eq_neg_of_collide τ ha hb hab he hib, neg_smul,
          neg_add_cancel]
      · have hib : ¬ Set.InjOn τ ↑(s.erase b) := fun h => hia (injOn_erase_of_injOn_erase_of_eq τ ha hab.ne he h)
        rw [pullC_ninj τ φ c hia, pullC_ninj τ φ c hib, smul_zero, smul_zero, add_zero]
    · intro j hj hjab
      rw [pullC_ninj τ φ c, smul_zero]
      intro h
      exact hab.ne (h (Finset.mem_erase.2 ⟨hjab.1.symm, ha⟩) (Finset.mem_erase.2 ⟨hjab.2.symm, hb⟩) he)

end Signs

section Field

variable {B B' K L : Type} [CommRing B] [CommRing B'] [IsDomain B] [IsDomain B'] [Field K] [Field L]
  [Algebra B B'] [Algebra B K] [Algebra K L] [Algebra B' L] [Algebra B L]
  [IsScalarTower B K L] [IsScalarTower B B' L] [IsFractionRing B K] [IsFractionRing B' L]

end Field

section Germ

variable {Z : Scheme.{0}} [IsIntegral Z] {p : Z ⟶ Sp ℂ} [Smooth p] [inst : Algebra ℂ Z.functionField]
  {ι : Type} {U : ι → Z.Opens} {B : Finset ι → Subalgebra ℂ Z.functionField}

theorem germ_inj_range (hinst : inst = ffAlg p) (hU : IsAffCover p U B) (a : ℕ) {s : Finset ι}
    (hs : s.Nonempty) {V : Z.Opens} (hVs : V = s.inf U) (hV : IsAffineOpen V)
    (hη : genericPoint Z ∈ V) :
    letI := algΓ p
    Function.Injective (formGermI p a hV hη hinst) ∧
      LinearMap.range (formGermI p a hV hη hinst) = omB ℂ Z.functionField (B s) a := by
  subst hinst
  subst hVs
  letI := algΓ p
  letI : Algebra ℂ Z.functionField := ffAlg p
  letI : Algebra (Sec p (s.inf U)) Z.functionField := (germSec p hη).toAlgebra
  haveI : IsScalarTower ℂ (Sec p (s.inf U)) Z.functionField := by
    refine ⟨fun r b y => ?_⟩
    show germSec p hη (r • b) * y = r • (germSec p hη b * y)
    rw [semiHom_germSec p hη r b, smul_mul_assoc]
    rfl
  haveI : IsFractionRing (Sec p (s.inf U)) Z.functionField :=
    @functionField_isFractionRing_of_isAffineOpen Z _ (s.inf U) hV ⟨⟨genericPoint Z, hη⟩⟩
  haveI : Algebra.Smooth ℂ (Sec p (s.inf U)) := by
    have e : s.inf U ≤ p ⁻¹ᵁ ⊤ := by simp
    have h1 := p.smooth_appLE (isAffineOpen_top (Sp ℂ)) hV e
    have hb : Function.Bijective (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom :=
      Function.bijective_iff_has_inverse.mpr ⟨(Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom,
        fun x => by simp, fun x => by simp⟩
    have h2 := RingHom.Smooth.comp (RingHom.Smooth.of_bijective hb) h1
    rw [← RingHom.smooth_algebraMap]
    exact h2
  obtain ⟨hinj, hrange⟩ :=
    mOm_injective_and_omB ℂ Z.functionField (Sec p (s.inf U)) (B s) (hU.ring s hs) a
  rw [formGermI_ffAlg]
  have key : ∀ x, formGerm p a hV hη x =
      (((semiHom_algebraMap ℂ (Sec p (s.inf U)) Z.functionField).mOm a
        ((toOmEquiv p a hV).symm (sectionsOn.toΓ _ _ x))) : DR ℂ Z.functionField) := fun x => rfl
  refine ⟨fun x y h => ?_, ?_⟩
  · rw [key, key] at h
    exact (sectionsOn.toΓ _ _).injective ((toOmEquiv p a hV).symm.injective (hinj (Subtype.ext h)))
  · ext y
    rw [LinearMap.mem_range, hrange y]
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨_, (key x).symm⟩
    · rintro ⟨z, rfl⟩
      refine ⟨(sectionsOn.toΓ _ _).symm (toOmEquiv p a hV z), ?_⟩
      rw [key, AddEquiv.apply_symm_apply, LinearEquiv.symm_apply_apply]

end Germ

section Cmp

open UpperTheory.GenericCoverClass

variable {Z : Scheme.{0}} [IsIntegral Z] (p : Z ⟶ Sp ℂ) [Smooth p] [inst : Algebra ℂ Z.functionField]
  {ι : Type} {U : ι → Z.Opens} {B : Finset ι → Subalgebra ℂ Z.functionField}

theorem cechOpen_eq (s : Finset ι) : cechOpen ⊤ U s = s.inf U := by
  rw [cechOpen_eq_inf, top_inf_eq]

theorem gm_inj (hinst : inst = ffAlg p) (hU : IsAffCover p U B) (a : ℕ) (s : Finset ι)
    (hs : s.Nonempty) : letI := algΓ p; Function.Injective (gm p hinst hU a s) := by
  letI := algΓ p
  rw [gm_pos hinst hU a hs]
  exact (germ_inj_range hinst hU a hs (cechOpen_eq s) _ _).1

theorem gm_range (hinst : inst = ffAlg p) (hU : IsAffCover p U B) (a : ℕ) (s : Finset ι)
    (hs : s.Nonempty) :
    letI := algΓ p; LinearMap.range (gm p hinst hU a s) = omB ℂ Z.functionField (B s) a := by
  letI := algΓ p
  rw [gm_pos hinst hU a hs]
  exact (germ_inj_range hinst hU a hs (cechOpen_eq s) _ _).2

theorem gm_res (hinst : inst = ffAlg p) (hU : IsAffCover p U B) (a : ℕ) (s t : Finset ι) (h : s ⊆ t)
    (hs : s.Nonempty) (y) : letI := algΓ p
    gm p hinst hU a t (Cube.res (cechCube ℂ (Omega p a) ⊤ U) h y) = gm p hinst hU a s y := by
  letI := algΓ p
  rw [gm_pos hinst hU a hs, gm_pos hinst hU a (hs.mono h)]
  exact GlobalTheory.T.genericGerm_differentialForm_restrict_affineOpen Z p hinst a _ _ _ _ _ _ _ y

variable [LinearOrder ι] [Fintype ι]

def cube (hinst : inst = ffAlg p) (hU : IsAffCover p U B) (a b : ℕ) :
    letI := algΓ p
    (cechComplex (cechCube ℂ (Omega p a) ⊤ U)).homology b ≃ₗ[ℂ]
      (GlobalTheory.PD.cech fun I => omB ℂ Z.functionField (B I) a).H (b : ℤ) :=
  letI := algΓ p
  Classical.choose (GlobalTheory.T.cechHomologyEquivFamAlt ℂ ι (DR ℂ Z.functionField)
    (fun I => omB ℂ Z.functionField (B I) a) (cechCube ℂ (Omega p a) ⊤ U) (gm p hinst hU a)
    (gm_inj p hinst hU a) (gm_range p hinst hU a) (gm_res p hinst hU a) b)

def cmp (hinst : inst = ffAlg p) (hU : IsAffCover p U B) (a b : ℕ) :
    hodgeH p a b ≃ₗ[ℂ] (GlobalTheory.PD.cech fun I => omB ℂ Z.functionField (B I) a).H b :=
  letI := algΓ p
  (cechHEquivCoh ℂ hU.cover (cover_biInf hU) (Omega p a) b).symm ≪≫ₗ cube p hinst hU a b

end Cmp

section Bridge

end Bridge

section CechMem

variable {k : Type} [Field k] {ι : Type} [LinearOrder ι] {E : Type} [AddCommGroup E] [Module k E]

theorem mem_cechC {F : Finset ι → Submodule k E} {n : ℤ} {c : Finset ι → E} :
    c ∈ cechC F n ↔ ∀ s, (s.Nonempty ∧ (s.card : ℤ) = n + 1 → c s ∈ F s) ∧
      (¬ (s.Nonempty ∧ (s.card : ℤ) = n + 1) → c s = 0) := by
  rw [cechC.eq_1, Submodule.mem_pi]
  refine ⟨fun h s => ?_, fun h s _ => ?_⟩
  · have hs' := h s (Set.mem_univ _)
    split_ifs at hs' with hs
    · exact ⟨fun _ => hs', fun h' => (h' hs).elim⟩
    · exact ⟨fun h' => (hs h').elim, fun _ => (Submodule.mem_bot k).1 hs'⟩
  · split_ifs with hs
    · exact (h s).1 hs
    · exact (Submodule.mem_bot k).2 ((h s).2 hs)

end CechMem

section Pull

open UpperTheory.GenericCoverClass

variable {Z Z' : Scheme.{0}} [IsIntegral Z] [IsIntegral Z'] {p : Z ⟶ Sp ℂ} {p' : Z' ⟶ Sp ℂ}
  [Smooth p] [Smooth p'] [inst : Algebra ℂ Z.functionField] [inst' : Algebra ℂ Z'.functionField]
  {ι κ : Type} [LinearOrder ι] [Fintype ι] [LinearOrder κ] [Fintype κ]
  {U : ι → Z.Opens} {U' : κ → Z'.Opens} {B : Finset ι → Subalgebra ℂ Z.functionField}
  {B' : Finset κ → Subalgebra ℂ Z'.functionField}

private theorem preimage_finset_inf {X X' : Scheme.{0}} (g : X' ⟶ X) {α : Type} (V : α → X.Opens)
    (s : Finset α) : g ⁻¹ᵁ s.inf V = s.inf fun i => g ⁻¹ᵁ V i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.inf_insert, Finset.inf_insert, ← ih]
    ext z
    simp

theorem cechOpen_le (f : Z' ⟶ Z) (τ : κ → ι) (hτ : ∀ i, U' i ≤ f ⁻¹ᵁ U (τ i)) (t : Finset κ) :
    cechOpen ⊤ U' t ≤ f ⁻¹ᵁ cechOpen ⊤ U (t.image τ) := by
  rw [cechOpen_eq_inf, cechOpen_eq_inf, top_inf_eq, top_inf_eq, preimage_finset_inf]
  refine Finset.le_inf fun i hi => ?_
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hi
  exact (Finset.inf_le hj).trans (hτ j)

set_option maxHeartbeats 800000 in

theorem gm_pull (hinst : inst = ffAlg p) (hinst' : inst' = ffAlg p') (hU : IsAffCover p U B)
    (hU' : IsAffCover p' U' B') (f : Z' ⟶ Z) (hf : f ≫ p = p')
    (ψ : Z.functionField →ₐ[ℂ] Z'.functionField)
    (φ : DR ℂ Z.functionField →ₗ[ℂ] DR ℂ Z'.functionField) (τ : κ → ι) (hφ : IsDRMap ℂ ψ φ)
    (hψ : GermCompat f ψ) (hτ : ∀ i, U' i ≤ f ⁻¹ᵁ U (τ i)) (a : ℕ) {s : Finset κ} (hs : s.Nonempty)
    (x) : letI := algΓ p; letI := algΓ p'
    gm p' hinst' hU' a s (sectionsOn.res ℂ (Omega p' a) (cechOpen_le f τ hτ s)
      (sectionsOn.mapOver (appTop_algebraMap hf) (omegaPull hf a) _ x)) =
      φ (gm p hinst hU a (s.image τ) x) := by
  subst hinst hinst'
  letI := algΓ p; letI := algΓ p'
  letI : Algebra ℂ Z.functionField := ffAlg p
  letI : Algebra ℂ Z'.functionField := ffAlg p'
  have hne : (s.image τ).Nonempty := hs.image τ
  rw [GenericCoverClass.gm_pos _ hU a hne, GenericCoverClass.gm_pos _ hU' a hs, formGermI_ffAlg, formGermI_ffAlg]
  have hW : IsAffineOpen (cechOpen ⊤ U (s.image τ)) := by
    rw [cechOpen_eq]; exact hU.affine _ hne
  have hW' : IsAffineOpen (cechOpen ⊤ U' s) := by
    rw [cechOpen_eq]; exact hU'.affine _ hs
  have hη : genericPoint Z ∈ cechOpen ⊤ U (s.image τ) := by
    rw [cechOpen_eq]; exact hU.ne _
  have hη' : genericPoint Z' ∈ cechOpen ⊤ U' s := by
    rw [cechOpen_eq]; exact hU'.ne _
  obtain ⟨ω, hω⟩ := toOm_surjective (s := p) (j := a) hW (sectionsOn.toΓ _ _ x)
  have hR : formGerm p a hW hη x = (semiHom_germSec p hη).mDR ↑ω := by
    show (semiHom_germSec p hη).mDR ↑((toOmEquiv p a hW).symm (sectionsOn.toΓ _ _ x)) = _
    rw [← hω, ← toOmEquiv_apply p a hW, LinearEquiv.symm_apply_apply]
  have hL0 : sectionsOn.toΓ _ _ ((sectionsOn.res ℂ (Omega p' a) (cechOpen_le f τ hτ s))
      ((sectionsOn.mapOver (appTop_algebraMap hf) (omegaPull hf a) _) x)) =
      toOm p' a _ (formRes p' (cechOpen_le f τ hτ s) a (formPull hf _ a ω)) := by
    rw [← res_toOm, toOm_apply, ← omegaPull_toOmega, ← toOm_apply, hω]
    have h2 := sectionsOn.toΓ_mapOver (appTop_algebraMap hf) (omegaPull hf a) _ x
    erw [← h2]
    rfl
  have hL : formGerm p' a hW' hη' ((sectionsOn.res ℂ (Omega p' a) (cechOpen_le f τ hτ s))
      ((sectionsOn.mapOver (appTop_algebraMap hf) (omegaPull hf a) _) x)) =
      (semiHom_germSec p' hη').mDR ↑(formRes p' (cechOpen_le f τ hτ s) a (formPull hf _ a ω)) := by
    show (semiHom_germSec p' hη').mDR ↑((toOmEquiv p' a hW').symm (sectionsOn.toΓ _ _ _)) = _
    rw [hL0, ← toOmEquiv_apply p' a hW', LinearEquiv.symm_apply_apply]
  refine hL.trans ((?_ : _ = φ ((semiHom_germSec p hη).mDR ↑ω)).trans (congrArg φ hR).symm)
  have hmem : (semiHom_germSec p hη).mDR ↑ω ∈ omB ℂ Z.functionField (B (s.image τ)) a := by
    have hr := (germ_inj_range rfl hU a hne (cechOpen_eq _) hW hη).2
    rw [formGermI_ffAlg] at hr
    rw [← hR, ← hr]
    exact LinearMap.mem_range_self _ _
  have hLem : ∀ y ∈ omB ℂ Z.functionField (B (s.image τ)) a,
      φ y = (SemiHom.of_algHom ψ).mDR y := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨b, -, v, -, rfl⟩ := hy
      rw [hφ, SemiHom.mDR_smul]
      congr 1
      simp only [ExteriorAlgebra.ιMulti_apply, map_list_prod, List.map_ofFn, Function.comp_def,
        SemiHom.mDR_ι, SemiHom.m1_D]
      rfl
    | zero => simp
    | add y z _ _ hy hz => rw [map_add, map_add, hy, hz]
    | smul r y _ hy =>
      rw [map_smul, hy, ← algebraMap_smul Z.functionField r y, SemiHom.mDR_smul,
        ← algebraMap_smul Z'.functionField r]
      congr 1
      exact (ψ.commutes r).symm
  have hpt : ∀ b : Sec p (cechOpen ⊤ U (s.image τ)),
      germSec p' hη' (Sec.res p' (cechOpen_le f τ hτ s) (appSec p p' f _ b)) = ψ (germSec p hη b) := by
    intro b
    have h1 := hψ _ hη (cechOpen_le f τ hτ s hη') b
    refine Eq.trans ?_ h1.symm
    exact TopCat.Presheaf.germ_res_apply _ _ _ _ _
  rw [hLem _ hmem]
  have hG := SemiHom.comp (semiHom_germSec p hη) (SemiHom.of_algHom ψ)
  have hRG := SemiHom.comp (SemiHom.of_algHom (Sec.res p' (cechOpen_le f τ hτ s))) (semiHom_germSec p' hη')
  rw [← SemiHom.coe_mOm, ← SemiHom.coe_mOm, ← SemiHom.coe_mOm]
  congr 1
  rw [SemiHom.mOm_mOm (semiHom_germSec p hη) (SemiHom.of_algHom ψ) hG (fun _ => rfl)]
  show (semiHom_germSec p' hη').mOm a ((SemiHom.of_algHom (Sec.res p' (cechOpen_le f τ hτ s))).mOm a
    (SemiHom.mOm _ a ω)) = _
  rw [SemiHom.mOm_mOm (SemiHom.of_algHom (Sec.res p' (cechOpen_le f τ hτ s))) (semiHom_germSec p' hη') hRG
    (fun _ => rfl)]
  exact SemiHom.mOm_mOm _ hRG hG (fun b => hpt b) ω

theorem pullC_isMap (hinst : inst = ffAlg p) (hinst' : inst' = ffAlg p') (hU : IsAffCover p U B)
    (hU' : IsAffCover p' U' B') (f : Z' ⟶ Z) (hf : f ≫ p = p')
    (ψ : Z.functionField →ₐ[ℂ] Z'.functionField)
    (φ : DR ℂ Z.functionField →ₗ[ℂ] DR ℂ Z'.functionField) (τ : κ → ι) (hφ : IsDRMap ℂ ψ φ)
    (hψ : GermCompat f ψ) (hτ : ∀ i, U' i ≤ f ⁻¹ᵁ U (τ i)) (a : ℕ) :
    IsMap (omCx B a) (omCx B' a) (pullC τ φ) := by
  intro n x hx
  change x ∈ cechC (fun I => omB ℂ Z.functionField (B I) a) n at hx
  change pullC τ φ x ∈ cechC (fun I => omB ℂ Z'.functionField (B' I) a) n ∧
    pullC τ φ (deltaL ℂ ι _ x) = deltaL ℂ κ _ (pullC τ φ x)
  refine ⟨?_, pullC_delta τ φ x⟩
  rw [mem_cechC] at hx ⊢
  intro s
  by_cases hinj : Set.InjOn τ s
  · have hcard : (s.image τ).card = s.card := Finset.card_image_of_injOn hinj
    have hne : (s.image τ).Nonempty ↔ s.Nonempty := Finset.image_nonempty
    rw [pullC_inj τ φ x hinj]
    refine ⟨fun hs => ?_, fun hs => ?_⟩
    · have hmem := (hx (s.image τ)).1 ⟨hne.2 hs.1, by rw [hcard]; exact hs.2⟩
      letI := algΓ p
      letI := algΓ p'
      rw [← gm_range p hinst hU a _ (hne.2 hs.1)] at hmem
      obtain ⟨y, hy⟩ := hmem
      apply Submodule.smul_of_tower_mem
      rw [← hy, ← gm_range p' hinst' hU' a s hs.1,
        ← gm_pull hinst hinst' hU hU' f hf ψ φ τ hφ hψ hτ a hs.1 y]
      exact LinearMap.mem_range_self _ _
    · rw [(hx (s.image τ)).2 (by rw [hne, hcard]; exact hs), map_zero, smul_zero]
  · rw [pullC_ninj τ φ x hinj]
    exact ⟨fun _ => Submodule.zero_mem _, fun _ => rfl⟩

end Pull

section Trace

open UpperTheory.GenericCoverClass

variable {Z Y : Scheme.{0}} [IsIntegral Z] [IsIntegral Y] {p : Z ⟶ Sp ℂ} {p' : Y ⟶ Sp ℂ}
  [Smooth p] [Smooth p'] [inst : Algebra ℂ Z.functionField] [inst' : Algebra ℂ Y.functionField]
  {c : Y ⟶ Z} {ι : Type} {U : ι → Z.Opens} {B : Finset ι → Subalgebra ℂ Z.functionField}
  {B' : Finset ι → Subalgebra ℂ Y.functionField}

omit [IsIntegral Z] [IsIntegral Y] in
theorem pre_eq (s : Finset ι) : c ⁻¹ᵁ cechOpen ⊤ U s = s.inf fun i => c ⁻¹ᵁ U i := by
  rw [cechOpen_eq_inf, top_inf_eq, preimage_finset_inf]

theorem pre_affine (hU' : IsAffCover p' (fun i => c ⁻¹ᵁ U i) B') {s : Finset ι} (h : s.Nonempty) :
    IsAffineOpen (c ⁻¹ᵁ cechOpen ⊤ U s) := by
  rw [pre_eq]; exact hU'.affine s h

theorem pre_generic (hU' : IsAffCover p' (fun i => c ⁻¹ᵁ U i) B') (s : Finset ι) :
    genericPoint Y ∈ c ⁻¹ᵁ cechOpen ⊤ U s := by
  rw [pre_eq]; exact hU'.ne s

end Trace

section TraceCmp

open UpperTheory.GenericCoverClass

variable {Z Y : Scheme.{0}} [IsIntegral Z] [IsIntegral Y] {p : Z ⟶ Sp ℂ} (p' : Y ⟶ Sp ℂ)
  [Smooth p] [Smooth p'] [inst : Algebra ℂ Z.functionField] [inst' : Algebra ℂ Y.functionField]
  {c : Y ⟶ Z} {ι : Type} {U : ι → Z.Opens} {B : Finset ι → Subalgebra ℂ Z.functionField}
  {B' : Finset ι → Subalgebra ℂ Y.functionField}

abbrev lift (hc : c ≫ p = p') (a : ℕ) (W : Z.Opens) :
    letI := algΓ p; letI := algΓ p'
    sectionsOn ((Scheme.Modules.pushforward c).obj (Omega p' a)) W →ₗ[ℂ]
      sectionsOn (Omega p' a) (c ⁻¹ᵁ W) :=
  letI := algΓ p; letI := algΓ p'
  sectionsOn.mapOver (appTop_algebraMap hc) (𝟙 _) W

theorem lift_bijective (hc : c ≫ p = p') (a : ℕ) (W : Z.Opens) :
    letI := algΓ p; letI := algΓ p'
    Function.Bijective (lift p' hc a W) := by
  letI := algΓ p; letI := algΓ p'
  show Function.Bijective (sectionsOn.mapOver (appTop_algebraMap hc) (𝟙 _) W)
  rw [sectionsOn.mapOver.eq_1]
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  have key : ∀ y, (ConcreteCategory.hom
      (Scheme.Modules.Hom.app (𝟙 ((Scheme.Modules.pushforward c).obj (Omega p' a))) W)) y = y :=
    fun y => rfl
  simp only [key]
  constructor
  · intro x y h
    exact (sectionsOn.toΓ _ W).injective ((sectionsOn.toΓ (Omega p' a) (c ⁻¹ᵁ W)).symm.injective h)
  · intro y
    refine ⟨(sectionsOn.toΓ ((Scheme.Modules.pushforward c).obj (Omega p' a)) W).symm
      (sectionsOn.toΓ (Omega p' a) (c ⁻¹ᵁ W) y), ?_⟩
    simp only [LinearMap.coe_mk, AddHom.coe_mk]
    erw [AddEquiv.apply_symm_apply]
    exact (sectionsOn.toΓ (Omega p' a) (c ⁻¹ᵁ W)).symm_apply_apply y

def gq (hc : c ≫ p = p') (hinst' : inst' = ffAlg p') (hU' : IsAffCover p' (fun i => c ⁻¹ᵁ U i) B')
    (a : ℕ) (s : Finset ι) :
    letI := algΓ p
    (cechCube ℂ ((Scheme.Modules.pushforward c).obj (Omega p' a)) ⊤ U).obj s →ₗ[ℂ]
      DR ℂ Y.functionField :=
  letI := algΓ p; letI := algΓ p'
  if h : s.Nonempty then
    formGermI p' a (pre_affine hU' h) (pre_generic hU' s) hinst' ∘ₗ lift p' hc a (cechOpen ⊤ U s)
  else 0

theorem gq_pos (hc : c ≫ p = p') (hinst' : inst' = ffAlg p')
    (hU' : IsAffCover p' (fun i => c ⁻¹ᵁ U i) B') (a : ℕ) {s : Finset ι} (h : s.Nonempty) :
    letI := algΓ p; letI := algΓ p'
    gq p' hc hinst' hU' a s =
      formGermI p' a (pre_affine hU' h) (pre_generic hU' s) hinst' ∘ₗ
        lift p' hc a (cechOpen ⊤ U s) := dif_pos h

theorem gq_range (hc : c ≫ p = p') (hinst' : inst' = ffAlg p')
    (hU' : IsAffCover p' (fun i => c ⁻¹ᵁ U i) B') (a : ℕ) (s : Finset ι) (h : s.Nonempty) :
    letI := algΓ p
    LinearMap.range (gq p' hc hinst' hU' a s) = omB ℂ Y.functionField (B' s) a := by
  letI := algΓ p; letI := algΓ p'
  rw [gq_pos p' hc hinst' hU' a h,
    ← (germ_inj_range hinst' hU' a h (pre_eq s) (pre_affine hU' h) (pre_generic hU' s)).2]
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨_, rfl⟩
  · rintro ⟨x, rfl⟩
    obtain ⟨z, rfl⟩ := (lift_bijective p' hc a (cechOpen ⊤ U s)).2 x
    exact ⟨z, rfl⟩

variable [Algebra Z.functionField Y.functionField] [IsScalarTower ℂ Z.functionField Y.functionField]

abbrev trL (Z Y : Scheme.{0}) [IsIntegral Z] [IsIntegral Y] [Algebra ℂ Z.functionField]
    [Algebra ℂ Y.functionField] [Algebra Z.functionField Y.functionField]
    [IsScalarTower ℂ Z.functionField Y.functionField] (ι : Type) :
    (Finset ι → DR ℂ Y.functionField) →ₗ[ℂ] (Finset ι → DR ℂ Z.functionField) :=
  LinearMap.pi fun s => (trDR ℂ Z.functionField Y.functionField).comp (LinearMap.proj s)

variable [LinearOrder ι] [IsFinite c] [Etale c]

private theorem mapDR_eq_semiHom_algebraMap_mDR (K L : Type) [Field K] [Field L] [Algebra ℂ K] [Algebra ℂ L] [Algebra K L]
    [IsScalarTower ℂ K L] (y : DR ℂ K) :
    mapDR ℂ K L y = (semiHom_algebraMap ℂ K L).mDR y := by
  induction y using ExteriorAlgebra.induction with
  | algebraMap r =>
    rw [AlgHom.commutes, SemiHom.mDR_algebraMap, IsScalarTower.algebraMap_apply K L (DR ℂ L)]
  | ι x =>
    rw [SemiHom.mDR_ι, SemiHom.oneFormMap_eq_kaehlerDifferential_map _ (fun _ => rfl)]
    show ExteriorAlgebra.lift K ⟨map1 ℂ K L, _⟩ (ExteriorAlgebra.ι K x) = _
    rw [ExteriorAlgebra.lift_ι_apply]
    rfl
  | mul a b ha hb => rw [map_mul, map_mul, ha, hb]
  | add a b ha hb => rw [map_add, map_add, ha, hb]

private theorem isTrDR_trDR (K L : Type) [Field K] [Field L] [Algebra ℂ K] [Algebra ℂ L] [Algebra K L]
    [IsScalarTower ℂ K L] [FiniteDimensional K L] : IsTrDR ℂ K L (trDR ℂ K L) := by
  classical
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℂ K).injective
  haveI : Algebra.IsSeparable K L := inferInstance
  haveI : Algebra.Etale K L :=
    ⟨Algebra.FormallyEtale.of_isSeparable K L, Algebra.FinitePresentation.of_finiteType.mp inferInstance⟩
  let T0 : DR ℂ L →+ DR ℂ K :=
    (DirectSum.toAddMonoid fun j => ((⋀[K]^j (Ω[K⁄ℂ])).subtype.toAddMonoidHom.comp
      (formTrace ℂ K L j).toAddMonoidHom)).comp
      (DirectSum.decomposeAddEquiv (fun i : ℕ => ⋀[L]^i (Ω[L⁄ℂ]))).toAddMonoidHom
  have hT0 : ∀ j (z : ⋀[L]^j (Ω[L⁄ℂ])), T0 (z : DR ℂ L) = ((formTrace ℂ K L j z : Om ℂ K j) : DR ℂ K) := by
    intro j z
    simp [T0, DirectSum.decomposeAddEquiv_apply, DirectSum.decompose_coe, DirectSum.toAddMonoid_of]
  have hsm : ∀ (r : ℂ) (y : DR ℂ L), T0 (r • y) = r • T0 y := by
    intro r y
    induction y using DirectSum.Decomposition.inductionOn (fun i : ℕ => ⋀[L]^i (Ω[L⁄ℂ])) with
    | zero => simp
    | add m m' hm hm' => rw [smul_add, map_add, map_add, hm, hm', smul_add]
    | homogeneous m =>
      rw [← algebraMap_smul K r (m : DR ℂ L), ← Submodule.coe_smul_of_tower, hT0, hT0, map_smul,
        Submodule.coe_smul_of_tower, algebraMap_smul]
  let T : DR ℂ L →ₗ[ℂ] DR ℂ K := { toFun := T0, map_add' := T0.map_add, map_smul' := hsm }
  have hT : IsTrDR ℂ K L T := by
    intro b ω
    induction ω using DirectSum.Decomposition.inductionOn (fun i : ℕ => ⋀[K]^i (Ω[K⁄ℂ])) with
    | zero => simp
    | add m m' hm hm' => rw [map_add, smul_add, map_add, hm, hm', smul_add]
    | homogeneous x =>
      have hx : mapDR ℂ K L (x : DR ℂ K) = ((formLin ℂ K L _ x : Om ℂ L _) : DR ℂ L) := by
        rw [mapDR_eq_semiHom_algebraMap_mDR]
        exact (SemiHom.coe_mOm _ x).symm
      show T0 (b • mapDR ℂ K L (x : DR ℂ K)) = _
      rw [hx, ← Submodule.coe_smul, hT0, formTrace_smul_formLin, Submodule.coe_smul_of_tower]
      congr 1
      unfold etTrace
      rw [algTrace_eq_trace]
  have hex : ∃ T : DR ℂ L →ₗ[ℂ] DR ℂ K, IsTrDR ℂ K L T := ⟨T, hT⟩
  unfold trDR
  rw [dif_pos hex]
  exact hex.choose_spec

private theorem germSec_secTrace_eq_trace {Z Y : Scheme.{0}} [IsIntegral Z] [IsIntegral Y] (p : Z ⟶ Sp ℂ) (p' : Y ⟶ Sp ℂ)
    {c : Y ⟶ Z} [IsFinite c] [Etale c] [Algebra Z.functionField Y.functionField]
    (hg : GermCompat c (algebraMap Z.functionField Y.functionField))
    {W : Z.Opens} (hW : IsAffineOpen W) (hη : genericPoint Z ∈ W) (hη' : genericPoint Y ∈ c ⁻¹ᵁ W)
    (b : Sec p' (c ⁻¹ᵁ W)) :
    germSec p hη (secTrace p p' hW b) = Algebra.trace Z.functionField Y.functionField (germSec p' hη' b) := by
  letI : Algebra (Sec p W) (Sec p' (c ⁻¹ᵁ W)) := secAlg p p' c W
  haveI : Module.Finite (Sec p W) (Sec p' (c ⁻¹ᵁ W)) := c.finite_app W hW
  haveI : Algebra.Etale (Sec p W) (Sec p' (c ⁻¹ᵁ W)) := by
    have h := c.etale_appLE hW (hW.preimage c) le_rfl
    rw [Scheme.Hom.appLE_eq_app] at h
    exact h
  haveI := projective_of_etale (Sec p W) (Sec p' (c ⁻¹ᵁ W))
  change germSec p hη (algTrace (Sec p W) (Sec p' (c ⁻¹ᵁ W)) b) = _
  letI : Algebra (Sec p W) Z.functionField := (germSec p hη).toAlgebra
  letI : Algebra (Sec p' (c ⁻¹ᵁ W)) Y.functionField := (germSec p' hη').toAlgebra
  letI : Algebra (Sec p W) Y.functionField := ((germSec p' hη').comp (appSec p p' c W)).toAlgebra
  haveI : IsScalarTower (Sec p W) (Sec p' (c ⁻¹ᵁ W)) Y.functionField :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower (Sec p W) Z.functionField Y.functionField :=
    IsScalarTower.of_algebraMap_eq (fun x => (hg W hη hη' x).symm)
  haveI : IsFractionRing (Sec p W) Z.functionField :=
    @functionField_isFractionRing_of_isAffineOpen Z _ W hW ⟨⟨genericPoint Z, hη⟩⟩
  haveI : IsFractionRing (Sec p' (c ⁻¹ᵁ W)) Y.functionField :=
    @functionField_isFractionRing_of_isAffineOpen Y _ (c ⁻¹ᵁ W) (hW.preimage c) ⟨⟨genericPoint Y, hη'⟩⟩
  haveI : IsDomain (Sec p' (c ⁻¹ᵁ W)) :=
    Function.Injective.isDomain (algebraMap (Sec p' (c ⁻¹ᵁ W)) Y.functionField)
      (IsFractionRing.injective (Sec p' (c ⁻¹ᵁ W)) Y.functionField)
  haveI : IsDomain (Sec p W) :=
    Function.Injective.isDomain (algebraMap (Sec p W) Z.functionField)
      (IsFractionRing.injective (Sec p W) Z.functionField)
  haveI hloc : IsLocalization (Algebra.algebraMapSubmonoid (Sec p' (c ⁻¹ᵁ W)) (nonZeroDivisors (Sec p W)))
      Y.functionField := by
    rw [isLocalization_iff]
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨y, s, hs, rfl⟩
      rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply (Sec p W) Z.functionField]
      exact (IsLocalization.map_units Z.functionField ⟨s, hs⟩).map _
    · intro z
      obtain ⟨⟨x, t, ht⟩, hz⟩ := IsLocalization.surj (nonZeroDivisors (Sec p' (c ⁻¹ᵁ W))) z
      have ht0 : t ≠ 0 := nonZeroDivisors.ne_zero ht
      have hI := Ideal.comap_ne_bot_of_integral_mem ht0 (Ideal.mem_span_singleton_self t)
        (Algebra.IsIntegral.isIntegral (R := Sec p W) t)
      obtain ⟨n, hn, hn0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
      rw [Ideal.mem_comap, Ideal.mem_span_singleton'] at hn
      obtain ⟨d, hd⟩ := hn
      refine ⟨⟨x * d, ⟨algebraMap _ _ n, n, mem_nonZeroDivisors_of_ne_zero hn0, rfl⟩⟩, ?_⟩
      simp only at hz ⊢
      rw [← hd]
      simp only [map_mul]
      linear_combination (algebraMap _ Y.functionField d) * hz
    · intro x y hxy
      exact ⟨1, by rw [IsFractionRing.injective (Sec p' (c ⁻¹ᵁ W)) Y.functionField hxy]⟩
  haveI : Algebra.IsPushout (Sec p W) (Sec p' (c ⁻¹ᵁ W)) Z.functionField Y.functionField :=
    Algebra.isPushout_of_isLocalization (nonZeroDivisors (Sec p W)) Z.functionField _ _
  haveI : Algebra.IsPushout (Sec p W) Z.functionField (Sec p' (c ⁻¹ᵁ W)) Y.functionField :=
    Algebra.IsPushout.symm ‹_›
  haveI : Module.Finite Z.functionField Y.functionField :=
    Module.Finite.of_isLocalization (Sec p W) (Sec p' (c ⁻¹ᵁ W)) (nonZeroDivisors (Sec p W))
  have key := algTrace_of_isPushout (B := Sec p W) (B' := Sec p' (c ⁻¹ᵁ W)) (C := Z.functionField)
    (C' := Y.functionField) b
  rw [algTrace_eq_trace] at key
  exact key.symm

private theorem kaehlerDifferential_map_eq_semiHom_m1 (K L : Type) [Field K] [Field L] [Algebra ℂ K] [Algebra ℂ L] [Algebra K L]
    [IsScalarTower ℂ K L] (ω : Ω[K⁄ℂ]) :
    KaehlerDifferential.map ℂ ℂ K L ω = (semiHom_algebraMap ℂ K L).m1 ω := by
  have hsp : ω ∈ Submodule.span K (Set.range (KaehlerDifferential.D ℂ K)) := by
    rw [KaehlerDifferential.span_range_derivation]; trivial
  induction hsp using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨t, rfl⟩ := hy
    rw [KaehlerDifferential.map_D, SemiHom.m1_D]
  | zero => simp
  | add y z _ _ hy hz => rw [map_add, map_add, hy, hz]
  | smul r y _ hy =>
    rw [LinearMap.map_smul_of_tower, hy]
    show _ = (semiHom_algebraMap ℂ K L).m1' (r • y)
    rw [LinearMap.map_smulₛₗ, algebra_compatible_smul L r]
    rfl

private theorem mapDR_eq_semiHom_mDR (K L : Type) [Field K] [Field L] [Algebra ℂ K] [Algebra ℂ L] [Algebra K L]
    [IsScalarTower ℂ K L] (x : DR ℂ K) :
    mapDR ℂ K L x = (semiHom_algebraMap ℂ K L).mDR x := by
  induction x using ExteriorAlgebra.induction with
  | algebraMap r =>
    rw [AlgHom.commutes, SemiHom.mDR_algebraMap]
    rfl
  | ι ω =>
    rw [SemiHom.mDR_ι]
    show (ExteriorAlgebra.lift K ⟨map1 ℂ K L, kaehlerOneFormsToExtensionDeRham_mul_self ℂ K L⟩) (ExteriorAlgebra.ι K ω) = _
    rw [ExteriorAlgebra.lift_ι_apply]
    show ExteriorAlgebra.ι L (KaehlerDifferential.map ℂ ℂ K L ω) = _
    rw [kaehlerDifferential_map_eq_semiHom_m1]
  | mul x y hx hy => rw [map_mul, map_mul, hx, hy]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

set_option maxHeartbeats 800000 in

theorem gm_trace (hc : c ≫ p = p') (hinst : inst = ffAlg p) (hinst' : inst' = ffAlg p')
    (hU : IsAffCover p U B) (hU' : IsAffCover p' (fun i => c ⁻¹ᵁ U i) B')
    (hg : GermCompat c (algebraMap Z.functionField Y.functionField))
    (hfin : FiniteDimensional Z.functionField Y.functionField)
    (a : ℕ) {s : Finset ι} (hs : s.Nonempty) (y) :
    letI := algΓ p; letI := algΓ p'
    gm p hinst hU a s (sectionsOn.map ℂ (omegaTrace hc a) _ y) =
      trDR ℂ Z.functionField Y.functionField (gq p' hc hinst' hU' a s y) := by
  subst hinst hinst'
  letI := algΓ p; letI := algΓ p'
  letI : Algebra ℂ Z.functionField := ffAlg p
  letI : Algebra ℂ Y.functionField := ffAlg p'
  rw [GenericCoverClass.gm_pos _ hU a hs, gq_pos p' hc rfl hU' a hs, formGermI_ffAlg, formGermI_ffAlg]
  have hW : IsAffineOpen (cechOpen ⊤ U s) := by
    rw [cechOpen_eq]; exact hU.affine _ hs
  have hη : genericPoint Z ∈ cechOpen ⊤ U s := by
    rw [cechOpen_eq]; exact hU.ne _
  have hW' := pre_affine hU' hs
  have hη' := pre_generic hU' s
  obtain ⟨η, hη0⟩ := toOm_surjective (s := p') (j := a) hW' (sectionsOn.toΓ _ _ y)
  have hL : formGerm p a hW hη (sectionsOn.map ℂ (omegaTrace hc a) _ y) =
      (semiHom_germSec p hη).mDR ↑(formTraceU hc hW a η) := by
    show (semiHom_germSec p hη).mDR ↑((toOmEquiv p a hW).symm (sectionsOn.toΓ _ _ _)) = _
    have h2 : sectionsOn.toΓ _ _ (sectionsOn.map ℂ (omegaTrace hc a) (cechOpen ⊤ U s) y) =
        toOm p a _ (formTraceU hc hW a η) := by
      rw [← omegaTrace_app_toOm hc a hW η, hη0]
      rfl
    rw [h2, ← toOmEquiv_apply p a hW, LinearEquiv.symm_apply_apply]
  have hR : formGerm p' a (pre_affine hU' hs) (pre_generic hU' s) (lift p' hc a (cechOpen ⊤ U s) y) =
      (semiHom_germSec p' hη').mDR ↑η := by
    show (semiHom_germSec p' hη').mDR ↑((toOmEquiv p' a hW').symm (sectionsOn.toΓ _ _ _)) = _
    have h2 : sectionsOn.toΓ _ _ (lift p' hc a (cechOpen ⊤ U s) y) = toOm p' a _ η := by
      rw [hη0]
      exact sectionsOn.toΓ_mapOver (appTop_algebraMap hc) (𝟙 _) _ y
    rw [h2, ← toOmEquiv_apply p' a hW', LinearEquiv.symm_apply_apply]
  refine (congrArg _ ?_).trans (hL.trans ((?_ : _ = trDR ℂ Z.functionField Y.functionField
    ((semiHom_germSec p' hη').mDR ↑η)).trans (congrArg _ hR).symm))
  · rfl
  clear hL hR hη0
  have hTr := isTrDR_trDR Z.functionField Y.functionField
  induction η using formOm_induction hc hW with
  | h0 => simp
  | ha y z hy hz =>
    rw [map_add, Submodule.coe_add, map_add, hy, hz, Submodule.coe_add, map_add, map_add]
  | hm b' ω =>
    have e1 : formTraceU hc hW a (b' • formPull hc _ a ω) = secTrace p p' hW b' • ω :=
      formTraceU_smul_formPull hc hW b' ω
    have e2 : (semiHom_germSec p hη).mDR ↑(secTrace p p' hW b' • ω) =
        germSec p hη (secTrace p p' hW b') • (semiHom_germSec p hη).mDR ↑ω :=
      SemiHom.mDR_smul _ _ _
    have e3 : (semiHom_germSec p' hη').mDR ↑(b' • formPull hc (cechOpen ⊤ U s) a ω) =
        germSec p' hη' b' • (semiHom_germSec p' hη').mDR ↑(formPull hc (cechOpen ⊤ U s) a ω) :=
      SemiHom.mDR_smul _ _ _
    rw [e1, e2, e3, germSec_secTrace_eq_trace p p' hg hW hη hη' b']
    have hC : (semiHom_germSec p' hη').mDR ↑(formPull hc (cechOpen ⊤ U s) a ω) =
        mapDR ℂ Z.functionField Y.functionField ((semiHom_germSec p hη).mDR ↑ω) := by
      rw [mapDR_eq_semiHom_mDR, ← SemiHom.coe_mOm, ← SemiHom.coe_mOm, ← SemiHom.coe_mOm]
      congr 1
      rw [SemiHom.mOm_mOm (semiHom_germSec p hη) (semiHom_algebraMap ℂ Z.functionField Y.functionField)
        (SemiHom.comp (semiHom_germSec p hη) (semiHom_algebraMap ℂ Z.functionField Y.functionField))
        (fun _ => rfl)]
      show (semiHom_germSec p' hη').mOm a (SemiHom.mOm _ a ω) = _
      exact SemiHom.mOm_mOm (B := Sec p (cechOpen ⊤ U s)) (B' := Sec p' (c ⁻¹ᵁ cechOpen ⊤ U s))
        (B'' := Y.functionField) _ (semiHom_germSec p' hη')
        (SemiHom.comp (semiHom_germSec p hη) (semiHom_algebraMap ℂ Z.functionField Y.functionField))
        (fun g => (hg _ hη hη' g).symm) ω
    rw [hC, hTr]

theorem trL_isMap (hc : c ≫ p = p') (hinst : inst = ffAlg p) (hinst' : inst' = ffAlg p')
    (hU : IsAffCover p U B) (hU' : IsAffCover p' (fun i => c ⁻¹ᵁ U i) B')
    (hg : GermCompat c (algebraMap Z.functionField Y.functionField))
    (hfin : FiniteDimensional Z.functionField Y.functionField) (a : ℕ) :
    IsMap (omCx B' a) (omCx B a) (trL Z Y ι) := by
  intro n x hx
  change x ∈ cechC (fun I => omB ℂ Y.functionField (B' I) a) n at hx
  change trL Z Y ι x ∈ cechC (fun I => omB ℂ Z.functionField (B I) a) n ∧
    trL Z Y ι (deltaL ℂ ι _ x) = deltaL ℂ ι _ (trL Z Y ι x)
  refine ⟨?_, ?_⟩
  · rw [mem_cechC] at hx ⊢
    intro s
    refine ⟨fun hs => ?_, fun hs => ?_⟩
    · have hmem := (hx s).1 hs
      letI := algΓ p
      letI := algΓ p'
      rw [← gq_range p' hc hinst' hU' a s hs.1] at hmem
      obtain ⟨y, hy⟩ := hmem
      show trDR ℂ Z.functionField Y.functionField (x s) ∈ _
      rw [← hy, ← gm_trace p' hc hinst hinst' hU hU' hg hfin a hs.1 y, ← gm_range p hinst hU a s hs.1]
      exact LinearMap.mem_range_self _ _
    · show trDR ℂ Z.functionField Y.functionField (x s) = 0
      rw [(hx s).2 hs, map_zero]
  · funext s
    simp only [trL, LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.proj_apply, deltaL.eq_1,
      LinearMap.coe_mk, AddHom.coe_mk, DI.delta.eq_1, map_sum]
    exact Finset.sum_congr rfl fun i _ => map_zsmul _ _ _

end TraceCmp

section TraceMain

open UpperTheory.GenericCoverClass

variable {Z Y : Scheme.{0}} [IsIntegral Z] [IsIntegral Y] {p : Z ⟶ Sp ℂ} {p' : Y ⟶ Sp ℂ}
  [Smooth p] [Smooth p'] [inst : Algebra ℂ Z.functionField] [inst' : Algebra ℂ Y.functionField]
  {c : Y ⟶ Z} [IsFinite c] [Etale c] {ι : Type} [LinearOrder ι] [Fintype ι] {U : ι → Z.Opens}
  {B : Finset ι → Subalgebra ℂ Z.functionField} {B' : Finset ι → Subalgebra ℂ Y.functionField}
  [Algebra Z.functionField Y.functionField] [IsScalarTower ℂ Z.functionField Y.functionField]

end TraceMain

section Quot

variable {k : Type} [Field k] {M M' : Type} [AddCommGroup M] [Module k M] [AddCommGroup M'] [Module k M']

end Quot

end UpperTheory.PullbackConnectingMap
