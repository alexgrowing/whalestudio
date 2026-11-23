import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IdealEqBotOfFlatQuotientOfMapMaximalIdeal

open TensorProduct LinearMap IsLocalRing

namespace PositivityTheory.HtPt.Pfib

open GlobalTheory.LocalFlat

theorem lTensor_map_injective {R A M : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M] [Module.Flat R M]
    (p : Ideal R) :
    Function.Injective ((p.map (algebraMap R A)).subtype.lTensor M) := by
  let I := p.map (algebraMap R A)
  let c : p →ₗ[R] I :=
    { toFun := fun r => ⟨algebraMap R A r, Ideal.mem_map_of_mem _ r.2⟩
      map_add' := fun r s => Subtype.ext (by simp)
      map_smul' := fun r s => Subtype.ext (by simp [Algebra.smul_def]) }
  let φ : M ⊗[R] p →ₗ[R] M ⊗[A] I :=
    TensorProduct.mapOfCompatibleSMul A R R M I ∘ₗ c.lTensor M
  have hφ : ∀ m r, φ (m ⊗ₜ r) = m ⊗ₜ[A] c r := fun _ _ => rfl
  have hsurj : ∀ x, x ∈ LinearMap.range φ := by
    intro x
    induction x with
    | zero => exact zero_mem _
    | add a b ha hb => exact add_mem ha hb
    | tmul m i =>
      obtain ⟨i, hi⟩ := i
      induction hi using Submodule.span_induction generalizing m with
      | mem x hx =>
        obtain ⟨r, hr, rfl⟩ := hx
        exact ⟨m ⊗ₜ ⟨r, hr⟩, rfl⟩
      | zero =>
        change m ⊗ₜ[A] (0 : I) ∈ _
        rw [tmul_zero]
        exact zero_mem _
      | add x y hx hy ihx ihy =>
        change m ⊗ₜ[A] ((⟨x, hx⟩ : I) + ⟨y, hy⟩) ∈ _
        rw [tmul_add]
        exact add_mem (ihx m) (ihy m)
      | smul a x hx ih =>
        change m ⊗ₜ[A] (a • (⟨x, hx⟩ : I)) ∈ _
        rw [← smul_tmul]
        exact ih _
  have hcomp : ∀ y, TensorProduct.rid A M (I.subtype.lTensor M (φ y)) =
      TensorProduct.rid R M (p.subtype.lTensor M y) := by
    intro y
    induction y with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]
    | tmul m r => simp [hφ, c]
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨y, rfl⟩ := hsurj x
  have h0 := hcomp y
  rw [hx, map_zero, eq_comm, map_eq_zero_iff _ (TensorProduct.rid R M).injective,
    map_eq_zero_iff _ (Module.Flat.lTensor_preserves_injective_linearMap p.subtype
      p.injective_subtype)] at h0
  rw [h0, map_zero]

section Devissage

variable {A : Type} [CommRing A] {M : Type} [AddCommGroup M] [Module A M]

theorem exists_of_lTensor_eq {F G N : Type} [AddCommGroup F] [Module A F] [AddCommGroup G]
    [Module A G] [AddCommGroup N] [Module A N] (f : F →ₗ[A] N) (g : G →ₗ[A] N)
    (hs : Function.Surjective (f.coprod g)) (x : M ⊗[A] F) (y : M ⊗[A] G)
    (h : f.lTensor M x + g.lTensor M y = 0) :
    ∃ z : M ⊗[A] ker (f.coprod g),
      (fst A F G ∘ₗ (ker (f.coprod g)).subtype).lTensor M z = x ∧
      (snd A F G ∘ₗ (ker (f.coprod g)).subtype).lTensor M z = y := by
  have hex := lTensor_exact M (f.coprod g).exact_subtype_ker_map hs
  have h0 : (f.coprod g).lTensor M ((inl A F G).lTensor M x + (inr A F G).lTensor M y) = 0 := by
    rw [map_add, ← lTensor_comp_apply, ← lTensor_comp_apply, coprod_inl, coprod_inr, h]
  obtain ⟨z, hz⟩ := (hex _).mp h0
  refine ⟨z, ?_, ?_⟩
  · rw [lTensor_comp_apply, hz, map_add, ← lTensor_comp_apply, ← lTensor_comp_apply,
      fst_comp_inl, fst_comp_inr]
    simp
  · rw [lTensor_comp_apply, hz, map_add, ← lTensor_comp_apply, ← lTensor_comp_apply,
      snd_comp_inl, snd_comp_inr]
    simp

theorem lTensor_injective_of_le_range {I : Ideal A} (hrel : RelationsLift I M)
    (hI : Function.Injective (I.subtype.lTensor M)) {F : Type} [AddCommGroup F] [Module A F]
    (f : F →ₗ[A] A) (hf : Function.Injective f) (hle : I ≤ range f) :
    Function.Injective (f.lTensor M) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨y, rfl⟩ := hrel F f x (by rw [hx]; simp)
  let e₀ : Submodule.comap f I →ₗ[A] I := f.restrict fun _ h => h
  have he : Function.Bijective e₀ := by
    refine ⟨fun a b hab => Subtype.ext (hf (congrArg Subtype.val hab)), fun i => ?_⟩
    obtain ⟨a, ha⟩ := hle i.2
    exact ⟨⟨a, by rw [Submodule.mem_comap, ha]; exact i.2⟩, Subtype.ext ha⟩
  let e := LinearEquiv.ofBijective e₀ he
  have hy : I.subtype.lTensor M (e.toLinearMap.lTensor M y) = 0 := by
    rw [← hx, ← lTensor_comp_apply, ← lTensor_comp_apply]
    rfl
  rw [map_eq_zero_iff _ hI] at hy
  have : y = 0 := (LinearEquiv.lTensor M e).injective (hy.trans (map_zero _).symm)
  rw [this, map_zero]

theorem lTensor_injective_of_pow_le [IsNoetherianRing A] {I : Ideal A} (hrel : RelationsLift I M)
    (hI : Function.Injective (I.subtype.lTensor M)) (n : ℕ) (J : Ideal A) (hJ : I ^ n ≤ J) :
    Function.Injective (J.subtype.lTensor M) := by
  induction J using WellFoundedGT.induction with
  | ind J ih =>
  by_cases hex : ∃ a, a ∉ J ∧ ∀ i ∈ I, i * a ∈ J
  · obtain ⟨a, ha, hIa⟩ := hex
    let J' : Ideal A := J ⊔ Ideal.span {a}
    have haJ' : a ∈ J' := Submodule.mem_sup_right (Ideal.mem_span_singleton_self a)
    have hlt : J < J' := lt_of_le_of_ne le_sup_left fun h => ha (h ▸ haJ')
    have h' := ih J' hlt (hJ.trans hlt.le)
    let f : J →ₗ[A] J' := Submodule.inclusion hlt.le
    let g : A →ₗ[A] J' := toSpanSingleton A J' ⟨a, haJ'⟩
    have hs : Function.Surjective (f.coprod g) := by
      rintro ⟨b, hb⟩
      obtain ⟨j, hj, c, hc, rfl⟩ := Submodule.mem_sup.mp hb
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hc
      exact ⟨(⟨j, hj⟩, c), rfl⟩
    rw [injective_iff_map_eq_zero]
    intro x hx
    have hfx : f.lTensor M x = 0 := by
      apply h'
      rw [← lTensor_comp_apply, map_zero]
      exact hx
    obtain ⟨z, hz1, hz2⟩ := exists_of_lTensor_eq f g hs x 0 (by rw [hfx, map_zero, add_zero])
    have hinj : Function.Injective
        ((snd A J A ∘ₗ (ker (f.coprod g)).subtype).lTensor M) := by
      refine lTensor_injective_of_le_range hrel hI _ ?_ fun i hi => ?_
      · rw [injective_iff_map_eq_zero]
        rintro ⟨⟨j, c⟩, hjc⟩ hc
        have hc' : c = 0 := hc
        subst hc'
        have h1 : (j : A) + (0 : A) • a = 0 := congrArg Subtype.val hjc
        have h2 : j = 0 := Subtype.ext (by simpa using h1)
        subst h2
        rfl
      · refine ⟨⟨(⟨-(i * a), neg_mem (hIa i hi)⟩, i), ?_⟩, rfl⟩
        refine Subtype.ext ?_
        change -(i * a) + i • a = 0
        simp
    have hz : z = 0 := hinj (hz2.trans (map_zero _).symm)
    rw [← hz1, hz, map_zero]
  · push Not at hex
    have htop : ∀ m : ℕ, I ^ m ≤ J → (1 : A) ∈ J := by
      intro m
      induction m with
      | zero => intro h; exact h (by simp)
      | succ m ihm =>
        intro h
        refine ihm fun a ha => ?_
        by_contra haJ
        obtain ⟨i, hi, hia⟩ := hex a haJ
        exact hia (h (by rw [pow_succ']; exact Ideal.mul_mem_mul hi ha))
    refine lTensor_injective_of_le_range hrel hI _ J.injective_subtype ?_
    rw [Submodule.range_subtype, (Ideal.eq_top_iff_one J).mpr (htop n hJ)]
    exact le_top

theorem relationsLift_of_injective {J : Ideal A}
    (h : ∀ J' : Ideal A, J ≤ J' → Function.Injective (J'.subtype.lTensor M)) :
    RelationsLift J M := by
  intro F _ _ f x hx
  have hy : ∀ m ∈ J • (⊤ : Submodule A M),
      ∃ y : M ⊗[A] J, TensorProduct.rid A M (J.subtype.lTensor M y) = m := by
    intro m hm
    induction hm using Submodule.smul_induction_on' with
    | smul r hr m _ => exact ⟨m ⊗ₜ ⟨r, hr⟩, by simp⟩
    | add a _ b _ ha hb =>
      obtain ⟨a', rfl⟩ := ha
      obtain ⟨b', rfl⟩ := hb
      exact ⟨a' + b', by simp⟩
  obtain ⟨y, hy⟩ := hy _ hx
  have hy' := (TensorProduct.rid A M).injective hy
  let J' : Ideal A := range f ⊔ J
  let f' : F →ₗ[A] J' := f.codRestrict J' fun a => Submodule.mem_sup_left ⟨a, rfl⟩
  let g : J →ₗ[A] J' := Submodule.inclusion le_sup_right
  have hs : Function.Surjective (f'.coprod g) := by
    rintro ⟨b, hb⟩
    obtain ⟨_, ⟨a, rfl⟩, c, hc, rfl⟩ := Submodule.mem_sup.mp hb
    exact ⟨(a, ⟨c, hc⟩), rfl⟩
  have h0 : f'.lTensor M x + g.lTensor M (-y) = 0 := by
    apply h J' le_sup_right
    rw [map_add, ← lTensor_comp_apply, ← lTensor_comp_apply, map_zero, map_neg]
    change f.lTensor M x + -(J.subtype.lTensor M y) = 0
    rw [hy', add_neg_cancel]
  obtain ⟨z, hz, -⟩ := exists_of_lTensor_eq f' g hs x (-y) h0
  refine range_lTensor_le _ _ ?_ ⟨z, hz⟩
  rintro ⟨⟨a, j⟩, haj⟩
  have h1 : f a + (j : A) = 0 := congrArg Subtype.val haj
  change f a ∈ J
  rw [eq_neg_of_add_eq_zero_left h1]
  exact neg_mem j.2

theorem flat_of_relationsLift_of_injective [IsNoetherianRing A] (B : Type) [CommRing B]
    [Algebra A B] [IsNoetherianRing B] [Module B M] [IsScalarTower A B M] [Module.Finite B M]
    {I : Ideal A} (hI : I.map (algebraMap A B) ≤ Ideal.jacobson ⊥) (hrel : RelationsLift I M)
    (hinj : Function.Injective (I.subtype.lTensor M)) : Module.Flat A M :=
  flat_of_relationsLift B hI fun n =>
    relationsLift_of_injective fun J hJ => lTensor_injective_of_pow_le hrel hinj n J hJ

end Devissage

theorem fibre_crit_ring : ∀ (R A B : Type) [CommRing R] [CommRing A] [CommRing B] [IsLocalRing R] [IsLocalRing A] [IsLocalRing B] [IsNoetherianRing R] [IsNoetherianRing A] [IsNoetherianRing B] [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B] [IsLocalHom (algebraMap R A)] [IsLocalHom (algebraMap A B)], Module.Flat R B → (Algebra.TensorProduct.map (AlgHom.id R (IsLocalRing.ResidueField R)) (IsScalarTower.toAlgHom R A B)).toRingHom.Flat → Module.Flat A B := by
  intro R A B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hB h
  refine flat_of_relationsLift_of_injective B (I := (maximalIdeal R).map (algebraMap R A)) ?_ ?_
    (lTensor_map_injective _)
  · exact ((Ideal.map_mono (map_maximalIdeal_le _)).trans (map_maximalIdeal_le _)).trans
      (maximalIdeal_le_jacobson _)
  · refine relationsLift_of_square
      ((Algebra.TensorProduct.includeRight : A →ₐ[R] ResidueField R ⊗[R] A) :
        A →+* ResidueField R ⊗[R] A)
      ((Algebra.TensorProduct.includeRight : B →ₐ[R] ResidueField R ⊗[R] B) :
        B →+* ResidueField R ⊗[R] B) _
      (Algebra.TensorProduct.includeRight_surjective _ residue_surjective)
      (Algebra.TensorProduct.includeRight_surjective _ residue_surjective)
      (GlobalTheory.ker_includeRight_quotient A (maximalIdeal R)) ?_ ?_ h
    · rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq]
      exact GlobalTheory.ker_includeRight_quotient B (maximalIdeal R)
    · ext a
      simp

end PositivityTheory.HtPt.Pfib
