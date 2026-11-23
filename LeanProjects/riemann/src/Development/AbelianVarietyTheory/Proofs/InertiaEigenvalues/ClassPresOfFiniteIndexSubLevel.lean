import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LinksW
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RealSideCharacterMatch

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SubLevel

open Formalism.IndefR.Bridge GlobalTheory.CharChange

section Gen

variable {G Γ : Type} [Group G] [Group Γ] (ι : Γ →* G)

def dcRel (J' : Subgroup G) : Setoid G where
  r h h' := ∃ (γ : Γ) (k : J'), h' = ι γ * h * (k : G)
  iseqv := {
    refl := fun h => ⟨1, 1, by simp⟩
    symm := fun {h h'} ⟨γ, k, e⟩ => ⟨γ⁻¹, k⁻¹, by rw [e, map_inv, Subgroup.coe_inv]; group⟩
    trans := fun {h h' h''} ⟨γ, k, e⟩ ⟨γ₂, k₂, e₂⟩ =>
      ⟨γ₂ * γ, k * k₂, by rw [e₂, e, map_mul, Subgroup.coe_mul]; group⟩ }

theorem stab_mono_mem {J J' : Subgroup G} (hJ : J' ≤ J) {y k : G} (hk : k ∈ J) {g : Γ}
    (hg : g ∈ stab ι J' (y * k)) : g ∈ stab ι J y := by
  rw [mem_stab ι] at hg ⊢
  have h1 : (y * k)⁻¹ * ι g * (y * k) ∈ J := hJ hg
  have e : y⁻¹ * ι g * y = k * ((y * k)⁻¹ * ι g * (y * k)) * k⁻¹ := by group
  rw [e]
  exact J.mul_mem (J.mul_mem hk h1) (J.inv_mem hk)

end Gen

section Main

variable {G Γ : Type} [Group G] [Group Γ] {ι : Γ →* G}
variable {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable {S : CSD K} {σ : K →+* ℂ} {ρ : Γ →* Module.End ℂ W} {J : Subgroup G} {χ : J →* ℂˣ}
variable (P : ClassPres ι S σ ρ J χ) (J' : Subgroup G)

def yN (c : Quotient (dcRel ι J')) : G := P.y (P.decC c.out) * (P.decK c.out : G)

theorem yN_rel (c : Quotient (dcRel ι J')) : (dcRel ι J').r (yN P J' c) c.out := by
  show ∃ (γ : Γ) (k : J'), c.out = ι γ * yN P J' c * (k : G)
  refine ⟨P.decG c.out, 1, ?_⟩
  show c.out = ι (P.decG c.out) * (P.y (P.decC c.out) * (P.decK c.out : G)) * ((1 : J') : G)
  rw [Subgroup.coe_one, mul_one, ← mul_assoc]
  exact P.dec_spec c.out

theorem mk_yN (c : Quotient (dcRel ι J')) : Quotient.mk (dcRel ι J') (yN P J' c) = c :=
  (Quotient.sound (yN_rel P J' c)).trans (Quotient.out_eq c)

theorem reps_new : IsReps ι J' (yN P J') := by
  intro h
  refine ⟨Quotient.mk (dcRel ι J') h, ?_, ?_⟩
  · exact Quotient.exact (mk_yN P J' (Quotient.mk (dcRel ι J') h))
  · rintro i ⟨γ, k, e⟩
    have hr : (dcRel ι J').r (yN P J' i) h := ⟨γ, k, e⟩
    exact (mk_yN P J' i).symm.trans (Quotient.sound hr)

theorem stabN_finite (hJ : J' ≤ J) (c : Quotient (dcRel ι J')) : Finite (stab ι J' (yN P J' c)) := by
  haveI : Finite (stab ι J (P.y (P.decC c.out))) := Finite.of_equiv _ (P.stabI (P.decC c.out)).toEquiv
  refine Finite.of_injective
    (fun g : stab ι J' (yN P J' c) =>
      (⟨(g : Γ), stab_mono_mem ι hJ (P.decK c.out).2 g.2⟩ : stab ι J (P.y (P.decC c.out)))) ?_
  intro a b hab
  have hv := congrArg Subtype.val hab
  exact Subtype.ext hv

include P in
theorem cl_finite (hfi : (J'.subgroupOf J).FiniteIndex) : Finite (Quotient (dcRel ι J')) := by
  haveI := hfi
  refine Finite.of_surjective
    (fun p : S.Cl × (J ⧸ J'.subgroupOf J) => Quotient.mk (dcRel ι J') (P.y p.1 * ((p.2.out : J) : G))) ?_
  intro c
  obtain ⟨d, γ, k, e⟩ : ∃ (d : S.Cl) (γ : Γ) (k : J), c.out = ι γ * P.y d * (k : G) :=
    ⟨_, _, _, P.dec_spec c.out⟩
  obtain ⟨j, hj⟩ := QuotientGroup.mk_out_eq_mul (s := J'.subgroupOf J) k
  have hjJ' : ((j : J) : G) ∈ J' := Subgroup.mem_subgroupOf.1 j.2
  refine ⟨(d, (QuotientGroup.mk k : J ⧸ J'.subgroupOf J)), ?_⟩
  show Quotient.mk (dcRel ι J') (P.y d * (((QuotientGroup.mk k : J ⧸ J'.subgroupOf J).out : J) : G)) = c
  rw [hj]
  have hr : (dcRel ι J').r (P.y d * ((k * (j : J) : J) : G)) c.out := by
    refine ⟨γ, ⟨((j : J) : G)⁻¹, J'.inv_mem hjJ'⟩, ?_⟩
    show c.out = ι γ * (P.y d * ((k : G) * ((j : J) : G))) * ((j : J) : G)⁻¹
    rw [e]
    group
  exact (Quotient.sound hr).trans (Quotient.out_eq c)

variable (χ' : J' →* ℂˣ) (hχ' : ∀ k, ∃ a : K, σ a = ((χ' k : ℂˣ) : ℂ))
  (hρ : ∀ γ x, ∃ x', P.coef x' = ρ γ (P.coef x))

def rhoG (y : G) (g : stab ι J' y) (x : S.V) : W :=
  (χ' (stabK ι g) : ℂ) • ρ (g : Γ) (P.coef x)

include hχ' hρ in
theorem rhoG_rg (y : G) (g : stab ι J' y) (x : S.V) : InRg P (rhoG P J' χ' y g x) := by
  obtain ⟨x', hx'⟩ := hρ (g : Γ) x
  obtain ⟨a, ha⟩ := hχ' (stabK ι g)
  refine ⟨a • x', ?_⟩
  rw [map_smulₛₗ, hx', ha]
  rfl

def rhoGE (y : G) (g : stab ι J' y) : Module.End K S.V where
  toFun x := cinv P (rhoG P J' χ' y g x)
  map_add' x x' := by
    apply coef_injective P
    rw [map_add, coef_cinv P (rhoG_rg P J' χ' hχ' hρ _ _ _), coef_cinv P (rhoG_rg P J' χ' hχ' hρ _ _ _),
      coef_cinv P (rhoG_rg P J' χ' hχ' hρ _ _ _)]
    simp only [rhoG, map_add, smul_add]
  map_smul' b x := by
    apply coef_injective P
    rw [map_smulₛₗ, coef_cinv P (rhoG_rg P J' χ' hχ' hρ _ _ _), coef_cinv P (rhoG_rg P J' χ' hχ' hρ _ _ _)]
    simp only [rhoG, map_smulₛₗ, RingHom.id_apply, map_smul]
    rw [smul_comm]

theorem coef_rhoGE (y : G) (g : stab ι J' y) (x : S.V) :
    P.coef (rhoGE P J' χ' hχ' hρ y g x) = rhoG P J' χ' y g x :=
  coef_cinv P (rhoG_rg P J' χ' hχ' hρ y g x)

def rhoGN (y : G) : stab ι J' y →* Module.End K S.V where
  toFun := rhoGE P J' χ' hχ' hρ y
  map_one' := by
    apply LinearMap.ext; intro x
    apply coef_injective P
    rw [coef_rhoGE]
    simp [rhoG, stabK_one']
  map_mul' g g' := by
    apply LinearMap.ext; intro x
    apply coef_injective P
    rw [Module.End.mul_apply, coef_rhoGE, coef_rhoGE]
    simp only [rhoG, coef_rhoGE, map_mul, stabK_mul', Subgroup.coe_mul, Units.val_mul, Module.End.mul_apply, map_smul,
      smul_smul, mul_comm]

end Main

end GlobalTheory.SubLevel

namespace GlobalTheory

open Formalism.IndefR.Bridge GlobalTheory.SubLevel

theorem classPres_subLevel : ∀ {G Γ : Type} [Group G] [Group Γ] (ι : Γ →* G) {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] {K : Type} [Field K] [NumberField K] [StarRing K] (σ : K →+* ℂ) (S : CSD K) (ρ : Γ →* Module.End ℂ W) (J : Subgroup G) (χ : J →* ℂˣ) (P : Bridge.ClassPres ι S σ ρ J χ) (J' : Subgroup G), J' ≤ J → (J'.subgroupOf J).FiniteIndex → ∀ χ' : J' →* ℂˣ, (∀ k, ∃ a : K, σ a = ((χ' k : ℂˣ) : ℂ)) → (∀ γ x, ∃ x', P.coef x' = ρ γ (P.coef x)) → ∃ (Cl : Type) (fC : Fintype Cl) (π : Cl → S.Cl) (k : Cl → J) (Gam : Cl → Type) (gG : ∀ c, Group (Gam c)) (fG : ∀ c, Fintype (Gam c)) (ρ' : ∀ c, Gam c →* Module.End K S.V) (P' : Bridge.ClassPres ι ({ S with Cl := Cl, finCl := fC, Gam := Gam, grpGam := gG, finGam := fG, ρ := ρ', Nab := fun c => S.Nab (π c), Del := fun c => S.Del (π c) } : CSD K) σ ρ J' χ'), (∀ c : Cl, P'.y c = P.y (π c) * (k c : G)) ∧ P'.coef = P.coef := by
  intro G Γ _ _ ι W _ _ K _ _ _ σ S ρ J χ P J' hJ hfi χ' hχ' hρ
  haveI : Finite (Quotient (SubLevel.dcRel ι J')) := SubLevel.cl_finite P J' hfi
  letI fC : Fintype (Quotient (SubLevel.dcRel ι J')) := Fintype.ofFinite _
  haveI hfS : ∀ c, Finite (stab ι J' (SubLevel.yN P J' c)) := fun c => SubLevel.stabN_finite P J' hJ c
  letI fG : ∀ c, Fintype (stab ι J' (SubLevel.yN P J' c)) := fun c => Fintype.ofFinite _
  exact ⟨Quotient (SubLevel.dcRel ι J'), fC, fun c => P.decC c.out, fun c => P.decK c.out,
    fun c => stab ι J' (SubLevel.yN P J' c), fun c => inferInstance, fG,
    fun c => SubLevel.rhoGN P J' χ' hχ' hρ (SubLevel.yN P J' c),
    { y := SubLevel.yN P J'
      reps := SubLevel.reps_new P J'
      stabI := fun c => MulEquiv.refl _
      coef := P.coef
      coef_li := P.coef_li
      coef_span := P.coef_span
      coef_pair := P.coef_pair
      coef_act := fun c g x => SubLevel.coef_rhoGE P J' χ' hχ' hρ (SubLevel.yN P J' c) g x },
    fun c => rfl, rfl⟩

end GlobalTheory
