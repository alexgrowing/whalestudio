import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ResBound
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied

open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped LaurentSeries PowerSeries
namespace GlobalTheory.TopSteps

theorem mem_cob_of_repr_mem_herrB : ∀ {k G : Type} [Field k] [Group G] {l n : ℕ} [Fact l.Prime] [CharP k l]
    [NeZero n] {R : RingPG k l} (F : DFun R n G) (A : Ob k G) (z : G → Fin A.m → k)
    (b g : ZMod n → Vc k A.m), Repr F A z b g → (b, g) ∈ herrB (F.D A) → z ∈ cob A := by
  intro k G _ _ l n _ _ _ R F A z b g hR hB
  obtain ⟨E, a, p, e, ε, hE, ha, hp, hinj, hex, hpe, hρe, hε⟩ := hR
  unfold GlobalTheory.Models.herrB at hB
  obtain ⟨x, hx⟩ := LinearMap.mem_range.mp hB

  have hbx : ∀ i, b i = (F.D A).φ i (x (i - 1)) - x i := fun i => by
    have h := congrArg (fun q => q.1 i) hx
    simp at h
    exact h.symm
  have hgx : ∀ i, g i = (F.D A).γ i (x i) - x i := fun i => by
    have h := congrArg (fun q => q.2 i) hx
    simp at h
    exact h.symm
  have hA : F.Obj A := F.obj_sub A E a ha hinj hE
  have h1 : F.Obj (GlobalTheory.Models.chr (1 : G →* kˣ)) := F.obj_one

  set η : ZMod n → Vc k E.m := fun i => ε i - F.map A E a i (x i) with hη
  have hηφ : ∀ i, (F.D E).φ i (η (i - 1)) = η i := by
    intro i
    have h2 := (hε i).2.1
    rw [hbx i, map_sub, F.map_φ A E a hA hE ha] at h2
    simp only [hη, map_sub]
    rw [sub_eq_sub_iff_sub_eq_sub]
    exact h2.symm
  have hηγ : ∀ i, (F.D E).γ i (η i) = η i := by
    intro i
    have h3 := (hε i).2.2
    rw [hgx i, map_sub, F.map_γ A E a hA hE ha] at h3
    simp only [hη, map_sub]
    rw [sub_eq_sub_iff_sub_eq_sub]
    exact h3.symm
  obtain ⟨f, hf, hfη⟩ := F.fix E hE η hηφ hηγ

  have hmap0 : ∀ i y, F.map A (GlobalTheory.Models.chr (1 : G →* kˣ)) 0 i y = 0 := by
    intro i y
    have h := F.map_smul A (GlobalTheory.Models.chr (1 : G →* kˣ)) 0 0 hA h1 (fun _ _ => by simp) i y
    simpa using h
  have hpa : p ∘ₗ a = 0 := LinearMap.ext fun y => hex.apply_apply_eq_zero y
  have hpa_map : ∀ i y, F.map E (GlobalTheory.Models.chr (1 : G →* kˣ)) p i (F.map A E a i y) = 0 := by
    intro i y
    have h := F.map_comp A E (GlobalTheory.Models.chr (1 : G →* kˣ)) a p hA hE h1 ha hp i
    rw [hpa] at h
    have h' := LinearMap.congr_fun h y
    simpa [hmap0] using h'.symm

  set one : Fin 1 → k := fun _ => 1 with hone
  set c : k := p (f one) 0 with hc
  have hqc : ∀ v : Fin 1 → k, p (f v) = c • v := by
    intro v
    have hv : v = v 0 • one := funext fun j => by
      obtain rfl : j = 0 := Subsingleton.elim _ _
      simp [hone]
    rw [hv, map_smul, map_smul]
    funext j
    obtain rfl : j = 0 := Subsingleton.elim _ _
    simp [hc, hone, mul_comm]
  have hq : p ∘ₗ f = c • LinearMap.id := LinearMap.ext fun v => by simp [hqc]
  have hidH : GlobalTheory.Models.IsHom (GlobalTheory.Models.chr (1 : G →* kˣ)) (GlobalTheory.Models.chr (1 : G →* kˣ)) LinearMap.id :=
    fun _ _ => rfl

  have hcu : c • F.unit 0 = F.unit 0 := by
    have hcomp := F.map_comp _ E _ f p h1 hE h1 hf hp 0
    have hval := LinearMap.congr_fun hcomp (F.unit 0)
    rw [LinearMap.comp_apply, hfη 0, hη, map_sub, (hε 0).1, hpa_map, sub_zero, hq,
      F.map_smul _ _ _ c h1 h1 hidH, F.map_id _ h1] at hval
    simpa using hval
  have hc1 : c = 1 := by
    by_contra hne
    have hu : (c - 1) • F.unit 0 = 0 := by rw [sub_smul, one_smul, hcu, sub_self]
    apply F.unit_ne 0
    have h := inv_smul_smul₀ (sub_ne_zero.mpr hne) (F.unit 0)
    rw [hu, smul_zero] at h
    exact h.symm

  have hpw : p (f one) = one := by rw [hqc, hc1, one_smul]
  have hρ1 : ∀ σ (v : Fin 1 → k), (GlobalTheory.Models.chr (1 : G →* kˣ)).ρ σ v = v := fun σ v => by
    change ((1 : G →* kˣ) σ : k) • LinearMap.id v = v
    simp
  have hw : ∀ σ, E.ρ σ (f one) = f one := fun σ => by
    rw [← hf σ one, hρ1]

  have hker : p (e - f one) = 0 := by rw [map_sub, hpe, hpw, sub_self]
  obtain ⟨y, hy⟩ := (hex (e - f one)).1 hker
  have hkey : ∀ σ, A.ρ σ y = y + z σ := fun σ => by
    apply hinj
    rw [ha σ y, hy, map_sub, hρe σ, hw σ, map_add, hy]
    abel
  unfold GlobalTheory.Models.cob
  refine LinearMap.mem_range.mpr ⟨y, funext fun σ => ?_⟩
  simp only [LinearMap.pi_apply, LinearMap.sub_apply, LinearMap.id_apply]
  rw [hkey σ]
  abel

end GlobalTheory.TopSteps
