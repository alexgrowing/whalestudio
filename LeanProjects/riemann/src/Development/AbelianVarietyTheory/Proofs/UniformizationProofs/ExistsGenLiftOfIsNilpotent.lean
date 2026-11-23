import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.BijectiveSmulChartSec
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsQuasicoherentOfForallExistsAffine

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.GenLift

open GlobalTheory.LB

variable {X Y : Scheme.{0}}

theorem pullSec_surjective_of_le (f : Y ⟶ X) [IsClosedImmersion f] {L : LB X} (hL : L.IsLB)
    {V : X.Opens} (hV : IsAffineOpen V) (i : L.ι) (h : V ≤ L.U i) :
    Function.Surjective (pullSec L f V) := by
  intro s
  have h' : f ⁻¹ᵁ V ≤ (L.pull f).U (fun _ => i) :=
    (f.preimage_mono h).trans (pull_U f (fun _ => i)).ge
  obtain ⟨a, ha⟩ := f.app_surjective V hV (chartEquiv (Semi.LB.isLB_pull hL f) (fun _ => i) h' s)
  refine ⟨(chartEquiv hL i h).symm a, ?_⟩
  apply (chartEquiv (Semi.LB.isLB_pull hL f) (fun _ => i) h').injective
  rw [chartEquiv_pullSec f hL (fun _ => i) h h', LinearEquiv.apply_symm_apply]
  exact ha

theorem pullSec_surjective (f : Y ⟶ X) [IsClosedImmersion f] [IsAffine X] {L : LB X}
    (hL : L.IsLB) : Function.Surjective (pullSec L f ⊤) := by
  intro s
  haveI := isQuasicoherent_toMod hL
  haveI := isQuasicoherent_toMod (Semi.LB.isLB_pull hL f)
  let I : Ideal Γ(X, ⊤) :=
    { carrier := {c | ∃ σ, pullSec L f ⊤ σ = (f.app ⊤).hom c • s}
      add_mem' := by
        rintro a b ⟨σ, hσ⟩ ⟨τ, hτ⟩
        exact ⟨σ + τ, by rw [map_add, hσ, hτ, map_add, add_smul]⟩
      zero_mem' := ⟨0, by rw [map_zero, map_zero, zero_smul]⟩
      smul_mem' := by
        rintro a b ⟨σ, hσ⟩
        exact ⟨a • σ, by rw [LinearMap.map_smulₛₗ, hσ, smul_eq_mul, map_mul, mul_smul]⟩ }
  have key : ∀ x : X, ∃ c ∈ I, x ∈ X.basicOpen c := by
    intro x
    obtain ⟨i, hi⟩ := exists_chart hL x
    obtain ⟨a, ha, hx⟩ := (isAffineOpen_top X).exists_basicOpen_le ⟨x, hi⟩ (Opens.mem_top x)
    obtain ⟨u, hu⟩ := pullSec_surjective_of_le f hL ((isAffineOpen_top X).basicOpen a) i ha
      ((toMod (L.pull f)).presheaf.map (homOfLE (f.preimage_mono (X.basicOpen_le a))).op s)
    obtain ⟨n, σ, hσ⟩ := QCoh.exists_pow_smul_eq_res (toMod L) (isAffineOpen_top X) a
      (X.basicOpen_le a) rfl u
    obtain ⟨m, hm⟩ := QCoh.exists_pow_smul_eq_zero (toMod (L.pull f))
      ((isAffineOpen_top X).preimage f) ((f.app ⊤).hom a) (f.preimage_mono (X.basicOpen_le a))
      (f.preimage_basicOpen a) (pullSec L f ⊤ σ - (f.app ⊤).hom a ^ n • s) (by
        rw [map_sub, ← pullSec_map f (X.basicOpen_le a), ← hσ, LinearMap.map_smulₛₗ, hu, Scheme.Modules.map_smul,
          map_pow, map_pow, sub_eq_zero]
        congr 2
        exact congrArg (fun q => q.hom a) (f.naturality (homOfLE (X.basicOpen_le a)).op))
    refine ⟨a ^ (m + n + 1), ?_, by rwa [X.basicOpen_pow a (Nat.succ_pos _)]⟩
    rw [pow_succ']
    refine I.mul_mem_left a ⟨a ^ m • σ, ?_⟩
    rw [smul_sub, sub_eq_zero] at hm
    rw [LinearMap.map_smulₛₗ, map_pow, hm, map_pow, pow_add, mul_smul]
  have hI : I = ⊤ := by
    rw [← Ideal.span_eq I, ← (isAffineOpen_top X).iSup_basicOpen_eq_self_iff]
    refine top_le_iff.1 fun x _ => ?_
    obtain ⟨c, hc, hx⟩ := key x
    exact Opens.mem_iSup.2 ⟨⟨c, hc⟩, hx⟩
  obtain ⟨σ, hσ⟩ : (1 : Γ(X, ⊤)) ∈ I := hI ▸ Submodule.mem_top
  exact ⟨σ, by rw [hσ, map_one, one_smul]⟩

theorem isUnit_of_isUnit_app (f : Y ⟶ X) [Surjective f] {U : X.Opens} (a : Γ(X, U))
    (ha : IsUnit ((f.app U).hom a)) : IsUnit a := by
  refine X.toRingedSpace.isUnit_of_isUnit_germ U a fun x hx => ?_
  obtain ⟨y, rfl⟩ := f.surjective x
  have h₁ : y ∈ Y.basicOpen ((f.app U).hom a) := by
    rw [Y.basicOpen_of_isUnit ha]; exact hx
  have h₂ : y ∈ f ⁻¹ᵁ X.basicOpen a := by rw [f.preimage_basicOpen]; exact h₁
  exact (X.mem_basicOpen a (f y) hx).1 h₂

theorem exists_genPull_eq (f : Y ⟶ X) [IsClosedImmersion f] [Surjective f] [IsAffine X]
    {L : LB X} (hL : L.IsLB) (t₀ : LB.Gen (L.pull f)) (ht₀ : t₀.IsGen) :
    ∃ t : LB.Gen L, t.IsGen ∧ LB.genPull L t f = t₀ := by
  obtain ⟨σ, hσ⟩ := pullSec_surjective f hL (ofSec (genSec t₀ ht₀) _)
  obtain ⟨s, rfl⟩ := (globalEquiv L).symm.surjective σ
  have e : ∀ j : (L.pull f).ι,
      (f.appLE _ _ (pull_U_le f j)).hom (s.f (j PUnit.unit)) = (t₀.s j).val := fun j => by
    rw [← globalEquiv_pullSec_f f s j]
    exact congrArg (fun z : LB.Sec (L.pull f) => z.f j)
      ((congrArg (globalEquiv (L.pull f)) hσ).trans
        ((globalEquiv (L.pull f)).apply_symm_apply (genSec t₀ ht₀)))
  have hu : ∀ i, IsUnit (s.f i) := fun i => by
    refine isUnit_of_isUnit_app f _ ?_
    have h := ((e fun _ => i).symm ▸ (t₀.s fun _ => i).isUnit :
      IsUnit ((f.appLE _ _ (pull_U_le f fun _ => i)).hom (s.f i))).map
      (resG Y (pull_U f fun _ => i).ge)
    rwa [resG_appLE, Scheme.Hom.appLE_eq_app] at h
  refine ⟨⟨fun i => (hu i).unit⟩, fun i j => Units.ext (s.compat i j), ?_⟩
  cases t₀ with | mk t₀ => ?_
  exact congrArg LB.Gen.mk (funext fun j => Units.ext (e j))

end GlobalTheory.GenLift
