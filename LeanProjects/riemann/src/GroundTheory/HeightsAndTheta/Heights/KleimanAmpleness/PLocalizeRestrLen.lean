import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.LocalizeRestrLenSt
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.MulMemSecsTwistIdealSys
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial Kleiman

theorem LocalizeRestrLen.proof : LocalizeRestrLen.Statement := by
  intro S _ 𝔪 _ O _ _ _ Ω _ _ _ _ N x pp' hpp' F
  set p := pp'.comap (MvPolynomial.map (algebraMap S O) : Poly S N →+* Poly O N) with hp_def
  set G := F.twist (idealSys x p) with hG_def
  have hG : (F.baseChange O).twist (idealSys x pp') = G.baseChange O := by
    rw [idealSys_localize 𝔪 pp', hG_def, baseChange_twist]
  have hCO : ∀ m ∈ 𝔪, C (algebraMap S O m) ∈ pp' := fun m hm =>
    hpp' (Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ hm))
  have hCS : ∀ m ∈ 𝔪, C m ∈ p := fun m hm => by
    rw [hp_def, Ideal.mem_comap]
    change MvPolynomial.map (algebraMap S O) (C m) ∈ pp'
    rw [map_C]
    exact hCO m hm
  have killS : ∀ m ∈ 𝔪, ∀ y ∈ F.secs, algebraMap S Ω m * y ∈ G.secs := fun m hm y hy =>
    mul_mem_secs_twist_idealSys p (hCS m hm) F hy
  have killO : ∀ m ∈ 𝔪, ∀ y ∈ (F.baseChange O).secs, algebraMap S Ω m * y ∈ (G.baseChange O).secs := by
    intro m hm y hy
    rw [← hG, IsScalarTower.algebraMap_apply S O Ω]
    exact mul_mem_secs_twist_idealSys pp' (hCO m hm) _ hy
  unfold restrLen
  rw [hG]
  let P' := ((G.baseChange O).secs).comap (F.baseChange O).secs.subtype
  let φ : F.secs →ₗ[S] ((F.baseChange O).secs ⧸ P') :=
    { toFun := fun y => Submodule.Quotient.mk ⟨(y : Ω), mem_secs_baseChange y.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hker : LinearMap.ker φ = G.secs.comap F.secs.subtype := by
    ext ⟨y, hy⟩
    rw [LinearMap.mem_ker, Submodule.mem_comap, Submodule.subtype_apply]
    change Submodule.Quotient.mk _ = 0 ↔ _
    rw [Submodule.Quotient.mk_eq_zero]
    change y ∈ (G.baseChange O).secs ↔ y ∈ G.secs
    constructor
    · intro h
      obtain ⟨t, ht, hty⟩ := exists_mul_mem_secs 𝔪 h
      obtain ⟨u, i, hi, hui⟩ := Ideal.IsMaximal.exists_inv (inferInstance : 𝔪.IsMaximal) ht
      have h1 : algebraMap S Ω u * algebraMap S Ω t + algebraMap S Ω i = 1 := by
        rw [← map_mul, ← map_add, hui, map_one]
      have e : y = algebraMap S Ω u * (algebraMap S Ω t * y) + algebraMap S Ω i * y := by
        linear_combination (-y) * h1
      rw [e]
      refine add_mem ?_ (killS i hi y hy)
      rw [← Algebra.smul_def]
      exact G.secs.smul_mem u hty
    · exact fun h => mem_secs_baseChange h
  have hsurj : Function.Surjective φ := by
    intro q
    obtain ⟨⟨w, hw⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    obtain ⟨t, ht, htw⟩ := exists_mul_mem_secs 𝔪 hw
    obtain ⟨u, i, hi, hui⟩ := Ideal.IsMaximal.exists_inv (inferInstance : 𝔪.IsMaximal) ht
    have h1 : algebraMap S Ω u * algebraMap S Ω t + algebraMap S Ω i = 1 := by
      rw [← map_mul, ← map_add, hui, map_one]
    refine ⟨u • ⟨_, htw⟩, ?_⟩
    change Submodule.Quotient.mk _ = Submodule.Quotient.mk _
    rw [Submodule.Quotient.eq]
    change u • (algebraMap S Ω t * w) - w ∈ (G.baseChange O).secs
    have e : u • (algebraMap S Ω t * w) - w = -(algebraMap S Ω i * w) := by
      rw [Algebra.smul_def]
      linear_combination w * h1
    rw [e]
    exact neg_mem (killO i hi w hw)
  have hkill : ∀ m ∈ 𝔪, ∀ q : (F.baseChange O).secs ⧸ P', m • q = 0 := by
    intro m hm q
    obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    change m • (w : Ω) ∈ (G.baseChange O).secs
    rw [Algebra.smul_def]
    exact killO m hm w w.2
  rw [← length_eq_of_killed 𝔪 hkill,
    ((Submodule.quotEquivOfEq _ _ hker.symm).trans (φ.quotKerEquivOfSurjective hsurj)).length_eq]

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
