import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.UnipotentIdempotents.TCont
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.V00
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ExistsCoprimePowOfMemIneKer

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp UpperTheory.V.Ws.Lk

private theorem range_open (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω]
    [IsAlgClosure L Ω] : IsOpen ((W.resP L Ω).range : Set (G (W.Lp L) Ω)) := by
  obtain ⟨α, hα⟩ := Field.exists_primitive_element (W.Lp L) L
  have hadj : Algebra.adjoin (W.Lp L) {α} = ⊤ :=
    (IntermediateField.adjoin_simple_eq_top_iff_of_isAlgebraic
      (Algebra.IsAlgebraic.isAlgebraic α)).mp hα
  have hset : ((W.resP L Ω).range : Set (G (W.Lp L) Ω)) =
      {τ | τ (algebraMap L Ω α) = algebraMap L Ω α} := by
    ext τ
    constructor
    · rintro ⟨σ, rfl⟩
      exact σ.commutes α
    · intro hτ
      have hext : (τ.toAlgHom.comp (IsScalarTower.toAlgHom (W.Lp L) L Ω)) =
          IsScalarTower.toAlgHom (W.Lp L) L Ω := by
        refine AlgHom.ext_of_adjoin_eq_top hadj ?_
        intro x hx
        rw [Set.mem_singleton_iff] at hx
        subst hx
        exact hτ
      have hfix : ∀ l : L, τ (algebraMap L Ω l) = algebraMap L Ω l := fun l =>
        DFunLike.congr_fun hext l
      refine ⟨{ τ with commutes' := hfix }, ?_⟩
      ext x
      rfl
  rw [hset]
  exact isOpen_setOf_apply (algebraMap L Ω α) (fun y => y = algebraMap L Ω α)

theorem UpperTheory.V.Ws.Lk.v0Ex :
    ∀ (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [CharZero Ω] [Algebra L Ω] [IsAlgClosure L Ω] (U : Subgroup (G L Ω)), IsOpen (U : Set (G L Ω)) → ∀ (g : G L Ω) (M : ℕ), M ≠ 0 → ∃ (v : W.Plc (W.Lp L)) (A : ValuationSubring Ω) (p : ℕ), p.Prime ∧ ¬ p ∣ M ∧ ((p : ℕ) : 𝓞 (W.Lp L)) ∈ v.asIdeal ∧ normV v = p ∧ IsPlaceOver A v ∧ Dec (F := W.Lp L) A ≤ (W.resP L Ω).range ∧ (∀ d ∈ Dec (F := L) A, ∃ n : ℤ, d⁻¹ * g ^ n ∈ U) ∧ ∃ d ∈ Dec (F := L) A, d⁻¹ * g ∈ U := by
  intro L Ω _ _ _ _ _ _ _ U hU g M hM
  have hinj : Function.Injective (W.resP L Ω) := fun a b h =>
    AlgEquiv.ext fun x => DFunLike.congr_fun h x
  have hemb := (W.continuous_resP (L := L) (Ω := Ω)).isClosedEmbedding hinj
  have himg : IsOpen ((W.resP L Ω) '' (U : Set (G L Ω))) := by
    obtain ⟨t, ht, hpre⟩ := hemb.isInducing.isOpen_iff.mp hU
    rw [← hpre, Set.image_preimage_eq_inter_range]
    refine ht.inter ?_
    rw [← MonoidHom.coe_range]
    exact range_open L Ω
  obtain ⟨N, hN⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one himg
    ⟨1, U.one_mem, map_one _⟩
  obtain ⟨v, A, p, σ, -, hp, hpM, -, hpv, hnv, -, hAv, hIne, hfrob, hσg⟩ :=
    Loc.v00 (F := W.Lp L) (Ω := Ω) N.toSubgroup N.isOpen' (W.resP L Ω g) ∅ M hM
  have hback : ∀ x : G L Ω, W.resP L Ω x ∈ N.toSubgroup → x ∈ U := by
    intro x hx
    obtain ⟨u, hu, hux⟩ := hN hx
    rw [hinj hux] at hu
    exact hu
  have hdec : ∀ d : G L Ω, d ∈ Dec (F := L) A ↔ W.resP L Ω d ∈ Dec (F := W.Lp L) A := by
    intro d
    rw [mem_Dec, mem_Dec]
    exact Iff.rfl
  have hσH : σ ∈ Subgroup.zpowers (W.resP L Ω g) ⊔ N.toSubgroup := by
    have h1 : W.resP L Ω g ∈ Subgroup.zpowers (W.resP L Ω g) ⊔ N.toSubgroup :=
      Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
    have h2 : σ⁻¹ * W.resP L Ω g ∈ Subgroup.zpowers (W.resP L Ω g) ⊔ N.toSubgroup :=
      Subgroup.mem_sup_right hσg
    have h3 := Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ h2)
    have h4 : W.resP L Ω g * (σ⁻¹ * W.resP L Ω g)⁻¹ = σ := by group
    rwa [h4] at h3
  have hHclosed : IsClosed ((Subgroup.zpowers (W.resP L Ω g) ⊔ N.toSubgroup :
      Subgroup (G (W.Lp L) Ω)) : Set (G (W.Lp L) Ω)) :=
    Subgroup.isClosed_of_isOpen _ (Subgroup.isOpen_mono le_sup_right N.isOpen')
  have hDecH : Dec (F := W.Lp L) A ≤ Subgroup.zpowers (W.resP L Ω g) ⊔ N.toSubgroup := by
    intro d hd
    have hfrob' : IsFrob A (normV v) σ := by
      rw [hnv]
      exact hfrob
    have hcl := GlobalTheory.TameQuot.closure_frob_sup_Ine (W.Lp L) Ω A v hAv ⟨σ, hfrob.1⟩ hfrob'
    have hle : (Subgroup.zpowers (⟨σ, hfrob.1⟩ : Dec (F := W.Lp L) A) ⊔
        (Ine A).subgroupOf (Dec (F := W.Lp L) A)) ≤
        (Subgroup.zpowers (W.resP L Ω g) ⊔ N.toSubgroup).subgroupOf (Dec (F := W.Lp L) A) := by
      refine sup_le ?_ ?_
      · rw [Subgroup.zpowers_le, Subgroup.mem_subgroupOf]
        exact hσH
      · intro x hx
        rw [Subgroup.mem_subgroupOf] at hx ⊢
        exact Subgroup.mem_sup_right (hIne hx)
    have hclosed : IsClosed (((Subgroup.zpowers (W.resP L Ω g) ⊔ N.toSubgroup).subgroupOf
        (Dec (F := W.Lp L) A) : Subgroup (Dec (F := W.Lp L) A)) : Set (Dec (F := W.Lp L) A)) :=
      hHclosed.preimage continuous_subtype_val
    have hmin := Subgroup.topologicalClosure_minimal _ hle hclosed
    rw [hcl] at hmin
    exact Subgroup.mem_subgroupOf.mp (hmin (Subgroup.mem_top (⟨d, hd⟩ : Dec (F := W.Lp L) A)))
  have hHrange : Subgroup.zpowers (W.resP L Ω g) ⊔ N.toSubgroup ≤ (W.resP L Ω).range := by
    refine sup_le ?_ ?_
    · rw [Subgroup.zpowers_le]
      exact ⟨g, rfl⟩
    · intro x hx
      obtain ⟨u, -, hu⟩ := hN hx
      exact ⟨u, hu⟩
  obtain ⟨d0, hd0⟩ := hHrange hσH
  refine ⟨v, A, p, hp, hpM, hpv, hnv, hAv, hDecH.trans hHrange, ?_, d0, ?_, ?_⟩
  · intro d hd
    obtain ⟨y, hy, z, hz, hyz⟩ := Subgroup.mem_sup_of_normal_right.mp (hDecH ((hdec d).mp hd))
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    refine ⟨n, hback _ ?_⟩
    rw [map_mul, map_inv, map_zpow, ← hyz]
    have h5 : (W.resP L Ω g ^ n * z)⁻¹ * W.resP L Ω g ^ n = z⁻¹ := by group
    rw [h5]
    exact N.toSubgroup.inv_mem hz
  · rw [hdec, hd0]
    exact hfrob.1
  · apply hback
    rw [map_mul, map_inv, hd0]
    exact hσg
