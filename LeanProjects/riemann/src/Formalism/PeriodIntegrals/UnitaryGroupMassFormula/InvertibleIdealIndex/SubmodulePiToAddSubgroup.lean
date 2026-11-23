import Mathlib
import Formalism.PeriodIntegrals.InvIdealIdxPi

noncomputable section

namespace PI.InvIdealIdxPiWork

open NumberField nonZeroDivisors

theorem map_compLeft_pi {ι : Type} {G G' : Type*} [AddGroup G] [AddGroup G'] (φ : G →+ G')
    (A : ι → AddSubgroup G) :
    (AddSubgroup.pi Set.univ A).map (φ.compLeft ι) =
      AddSubgroup.pi Set.univ (fun i => (A i).map φ) := by
  ext y
  simp only [AddSubgroup.mem_map, AddSubgroup.mem_pi, Set.mem_univ, true_implies, forall_const]
  constructor
  · rintro ⟨x, hx, rfl⟩ i
    exact ⟨x i, hx i, rfl⟩
  · intro h
    choose x hx hxy using h
    exact ⟨x, hx, funext hxy⟩

theorem pi_mono {ι : Type} {G : Type*} [AddGroup G] {A B : ι → AddSubgroup G}
    (h : ∀ i, A i ≤ B i) : AddSubgroup.pi Set.univ A ≤ AddSubgroup.pi Set.univ B := by
  intro x hx
  rw [AddSubgroup.mem_pi] at hx ⊢
  exact fun i hi => h i (hx i hi)

theorem submodule_pi_toAddSubgroup {ι : Type} {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    (p : ι → Submodule R M) :
    (Submodule.pi Set.univ p).toAddSubgroup =
      AddSubgroup.pi Set.univ (fun i => (p i).toAddSubgroup) := by
  ext x
  simp only [Submodule.mem_toAddSubgroup, Submodule.mem_pi, AddSubgroup.mem_pi]

variable {E : Type} [Field E] [NumberField E]

abbrev idS (I : Ideal (𝓞 E)) : AddSubgroup E :=
  ((I : FractionalIdeal (𝓞 E)⁰ E) : Submodule (𝓞 E) E).toAddSubgroup

theorem idS_eq_map (I : Ideal (𝓞 E)) :
    idS I = I.toAddSubgroup.map (algebraMap (𝓞 E) E).toAddMonoidHom := by
  ext x
  simp only [idS, Submodule.mem_toAddSubgroup, FractionalIdeal.mem_coe, FractionalIdeal.mem_coeIdeal,
    AddSubgroup.mem_map, RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe]

theorem idS_mono {I I' : Ideal (𝓞 E)} (h : I ≤ I') : idS (E := E) I ≤ idS I' := by
  rw [idS_eq_map, idS_eq_map]
  exact AddSubgroup.map_mono (by intro x hx; exact h hx)

theorem map_mul_inv (J K : Ideal (𝓞 E)) (hJ : J ≠ ⊥) (a : 𝓞 E) (hK : Ideal.span {a} = J * K) :
    ((((J : FractionalIdeal (𝓞 E)⁰ E)⁻¹ : FractionalIdeal (𝓞 E)⁰ E) :
        Submodule (𝓞 E) E).toAddSubgroup).map (AddMonoidHom.mulLeft (algebraMap (𝓞 E) E a)) =
      idS K := by
  have hJ0 : (J : FractionalIdeal (𝓞 E)⁰ E) ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.mpr hJ
  have key : FractionalIdeal.spanSingleton (𝓞 E)⁰ (algebraMap (𝓞 E) E a) *
      (J : FractionalIdeal (𝓞 E)⁰ E)⁻¹ = (K : FractionalIdeal (𝓞 E)⁰ E) := by
    rw [← FractionalIdeal.coeIdeal_span_singleton, hK, FractionalIdeal.coeIdeal_mul,
      mul_comm (J : FractionalIdeal (𝓞 E)⁰ E), mul_assoc, mul_inv_cancel₀ hJ0, mul_one]
  ext x
  simp only [idS, Submodule.mem_toAddSubgroup, AddSubgroup.mem_map, FractionalIdeal.mem_coe,
    AddMonoidHom.coe_mulLeft]
  rw [← key, FractionalIdeal.mem_singleton_mul]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, hy, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, hy, rfl⟩

theorem relIndex_pi_idS {ι : Type} [Fintype ι] (I : ι → Ideal (𝓞 E)) :
    (AddSubgroup.pi Set.univ (fun i => idS (I i))).relIndex
      (AddSubgroup.pi Set.univ (fun _ : ι => idS (E := E) ⊤)) = ∏ i, Ideal.absNorm (I i) := by
  have hinj : Function.Injective ((algebraMap (𝓞 E) E).toAddMonoidHom.compLeft ι) := by
    intro x y h
    funext i
    exact IsFractionRing.injective (𝓞 E) E (congrFun h i)
  have htop : AddSubgroup.pi Set.univ (fun _ : ι => (⊤ : Ideal (𝓞 E)).toAddSubgroup) = ⊤ := by
    ext x
    simp [AddSubgroup.mem_pi]
  simp_rw [idS_eq_map]
  rw [← map_compLeft_pi (algebraMap (𝓞 E) E).toAddMonoidHom (fun i => (I i).toAddSubgroup),
    ← map_compLeft_pi (algebraMap (𝓞 E) E).toAddMonoidHom (fun _ : ι => (⊤ : Ideal (𝓞 E)).toAddSubgroup),
    AddSubgroup.relIndex_map_map_of_injective _ _ hinj, htop, AddSubgroup.relIndex_top_right,
    AddSubgroup.index_pi]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Ideal.absNorm_apply]
  rfl

theorem main : PI.InvIdealIdxPi := by
  unfold PI.InvIdealIdxPi
  intro E _ _ ι _ J hJ
  have hex : ∀ i, ∃ b ∈ J i, b ≠ 0 := fun i => Submodule.exists_mem_ne_zero_of_ne_bot (hJ i)
  choose b hbJ hb0 using hex
  obtain ⟨a, ha_def⟩ : ∃ a : 𝓞 E, a = ∏ i, b i := ⟨_, rfl⟩
  have ha0 : a ≠ 0 := by
    rw [ha_def]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => hb0 i
  have haJ : ∀ i, a ∈ J i := by
    intro i
    obtain ⟨d, hd⟩ := Finset.dvd_prod_of_mem b (Finset.mem_univ i)
    rw [ha_def, hd]
    exact (J i).mul_mem_right d (hbJ i)
  have hdiv : ∀ i, ∃ K : Ideal (𝓞 E), Ideal.span {a} = J i * K := by
    intro i
    obtain ⟨K, hK⟩ := Ideal.dvd_iff_le.mpr (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr (haJ i)))
    exact ⟨K, hK⟩
  choose K hK using hdiv
  have hc : algebraMap (𝓞 E) E a ≠ 0 := by
    intro h
    exact ha0 (IsFractionRing.injective (𝓞 E) E (h.trans (map_zero _).symm))
  have hφ : Function.Injective ((AddMonoidHom.mulLeft (algebraMap (𝓞 E) E a)).compLeft ι) := by
    intro x y h
    funext i
    exact mul_left_cancel₀ hc (congrFun h i)
  have h1 : (1 : Submodule (𝓞 E) E) =
      ((((⊤ : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E)⁻¹ : FractionalIdeal (𝓞 E)⁰ E) : Submodule (𝓞 E) E) := by
    rw [FractionalIdeal.coeIdeal_top, inv_one, FractionalIdeal.coe_one]
  have e1 : (fun i => ((((J i : FractionalIdeal (𝓞 E)⁰ E)⁻¹ : FractionalIdeal (𝓞 E)⁰ E) :
      Submodule (𝓞 E) E).toAddSubgroup).map (AddMonoidHom.mulLeft (algebraMap (𝓞 E) E a))) =
      fun i => idS (K i) :=
    funext fun i => map_mul_inv (J i) (K i) (hJ i) a (hK i)
  have e0 : (fun _ : ι => ((((⊤ : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E)⁻¹ : FractionalIdeal (𝓞 E)⁰ E) :
      Submodule (𝓞 E) E).toAddSubgroup.map (AddMonoidHom.mulLeft (algebraMap (𝓞 E) E a))) =
      fun _ => idS (Ideal.span {a}) :=
    funext fun _ => map_mul_inv ⊤ (Ideal.span {a}) top_ne_bot a (by rw [Ideal.top_mul])
  rw [submodule_pi_toAddSubgroup, submodule_pi_toAddSubgroup, h1,
    ← AddSubgroup.relIndex_map_map_of_injective _ _ hφ, map_compLeft_pi, map_compLeft_pi, e0, e1]
  have hAB : AddSubgroup.pi Set.univ (fun _ : ι => idS (E := E) (Ideal.span {a})) ≤
      AddSubgroup.pi Set.univ (fun i => idS (K i)) :=
    pi_mono fun i => idS_mono ((hK i).le.trans (by first | exact Ideal.mul_le_right | exact Ideal.mul_le_left))
  have hBC : AddSubgroup.pi Set.univ (fun i => idS (E := E) (K i)) ≤
      AddSubgroup.pi Set.univ (fun _ : ι => idS (E := E) ⊤) :=
    pi_mono fun _ => idS_mono le_top
  have hm := AddSubgroup.relIndex_mul_relIndex _ _ _ hAB hBC
  rw [relIndex_pi_idS K, relIndex_pi_idS (fun _ => Ideal.span {a})] at hm
  have hR : ∏ _i : ι, Ideal.absNorm (Ideal.span {a}) =
      (∏ i, Ideal.absNorm (J i)) * ∏ i, Ideal.absNorm (K i) := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun i _ => by rw [hK i, map_mul]
  have hP : ∏ i, Ideal.absNorm (K i) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr fun i _ => ?_
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    intro h
    have := hK i
    rw [h, Ideal.mul_bot, Ideal.span_singleton_eq_bot] at this
    exact ha0 this
  exact mul_right_cancel₀ hP (hm.trans hR)

end PI.InvIdealIdxPiWork

end
