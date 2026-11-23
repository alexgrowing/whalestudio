import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.ExistsSetLift
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.ExistsGradedLiftUnitaryLocalTame
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.ExistsLiftD
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.ExistsLiftU
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.ExistsSmallExtensionFactorizationOfFunctional
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.LiftAlongSurjectionGraded
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.CardDualResidueFieldEqCardOfMaximalIdealSmulEqZe
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.GradedMatrixMulInv
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.LocAtPushOfLocAt

open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia

open UpperTheory.V.UnitaryThreeInertia.Obs in
theorem UpperTheory.V.UnitaryThreeInertia.exists_unobstructed :
    ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CharZero O] [Finite (ResidueField O)]
      {G Γ ι : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
      [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [T2Space Γ] [TotallyDisconnectedSpace Γ] [Finite ι] (F : Frame O G Γ ι), F.Ok →
    F.LocVan → ∀ g₁, F.Marked g₁ → ∀ {R R' : Type} [CommRing R] [Algebra O R] [IsCO O R] [CommRing R'] [Algebra O R'] [IsCO O R'] (𝒜 : ℤ → Submodule O R) [GradedAlgebra 𝒜] (p : R →ₐ[O] R') (j : ℤ), Function.Surjective p → SmallExt O 𝒜 (RingHom.ker p) j →
    Module.Finite (ResidueField O) (F.Ob j) → Nat.card (ResidueField O) ^ Module.finrank (ResidueField O) (F.Ob j) < Nat.card (RingHom.ker p) →
      ∀ (r' : Γ →* GG 3 R'), F.IsPt g₁ r' → (∀ g, ∃ X, GrMat 𝒜 X ∧ X.map p = (r' g).mat) →
      ∃ (R'' : Type) (_ : CommRing R'') (_ : Algebra O R'') (_ : IsCO O R'') (p₁ : R →ₐ[O] R'') (q : R'' →ₐ[O] R') (r : Γ →* GG 3 R''),
        Function.Surjective p₁ ∧ q.comp p₁ = p ∧ ¬ Function.Injective q ∧ F.IsPt g₁ r ∧ push q r = r' := by
  intro O _ _ _ _ _ _ G Γ ι _ _ _ _ _ _ _ _ _ _ _ _ _ F hF hV g₁ hg₁ R R' _ _ _ _ _ _ 𝒜 _ p j hp hI hfin hlt r' hr' hgr
  have := hI.fin
  have : Finite R' := Finite.of_surjective p hp
  have hS : Sm (incl O (RingHom.ker p)) := ⟨fun y => hI.le y.2, fun x hx y => by
    have := Ideal.mul_mem_mul hx y.2
    rwa [hI.kill, Ideal.mem_bot] at this⟩
  have hinj : Function.Injective (incl O (RingHom.ker p)) := Subtype.val_injective
  have hlc := lc_mats r' hr'.cont
  have hloc : ∀ v, Continuous (F.loc v) := fun v => hF.π_cont.comp continuous_subtype_val
  obtain ⟨s, hs, hsc, hsg⟩ := exists_setLift 𝒜 p hp r' hlc hgr
  have hsr : ∀ g, (s g).right = F.η g := fun g =>
    (congrArg SemidirectProduct.right (hs g)).trans (hr'.mult g)
  have hsm : ∀ g, EntIn (maximalIdeal R) ((s g).mat - ((r0 F.η F.Ψ g).mat).map (algebraMap O R)) := fun g =>
    red_of_map p _ _ g _ (by rw [hs]; exact hr'.red g)
  have hsl : IsLocallyConstant s := lc_of_mat s hsc (by rw [funext hsr]; exact hF.η_cont)
  have hex : ∀ v, ∃ r : F.D v →* GG 3 R, push p r = r'.comp (F.loc v) ∧ F.LocAt v r ∧ IsLocallyConstant (mats r) ∧
      ∀ g, GrMat 𝒜 (r g).mat := fun v => by
    have h0 : Red (F.ηv v) (F.Ψv v) (r'.comp (F.loc v)) := ⟨fun g => hr'.mult _, fun g => hr'.red _⟩
    have hc : IsLocallyConstant (mats (r'.comp (F.loc v))) := hlc.comp_continuous (hloc v)
    by_cases h1 : v = F.vl
    · exact exists_graded_lift_unitary_local_tame F hF hV 𝒜 p j hp hI v h1 _ h0 (hr'.loc v) hc fun g => hgr _
    by_cases h2 : v ∈ F.Sb
    · exact exists_lift_d F hF hV 𝒜 p j hp hI v h2 _ h0 (hr'.loc v) hc fun g => hgr _
    · exact exists_lift_u F hF hV 𝒜 p j hp hI v (fun h3 => h3.elim h1 h2) _ h0 (hr'.loc v) hc fun g => hgr _
  choose ρ hρ hρl hρc hρg using hex
  have hρ' : ∀ v g, GG.map (p : R →+* R') (ρ v g) = r' (F.loc v g) := fun v g => DFunLike.congr_fun (hρ v) g
  have hρr : ∀ v, Red (F.ηv v) (F.Ψv v) (ρ v) := fun v =>
    ⟨fun g => (congrArg SemidirectProduct.right (hρ' v g)).trans (hr'.mult _),
      fun g => red_of_map p _ _ g _ (by rw [hρ']; exact hr'.red _)⟩
  have hρL : ∀ v, IsLocallyConstant (ρ v) := fun v => lc_of_mat _ (hρc v) (by
    rw [funext (hρr v).mult]; exact hF.η_cont.comp_continuous (hloc v))
  have hmul : ∀ x y : GG 3 R, GrMat 𝒜 x.mat → GrMat 𝒜 y.mat → GrMat 𝒜 (x * y⁻¹).mat := fun x y hx hy =>
    (UpperTheory.graded_matrix_mul_inv 𝒜 x y⁻¹ hx (UpperTheory.graded_matrix_mul_inv 𝒜 y y hy hy).2).1
  choose K hK hKw using fun gg : Γ × Γ => exists_ex 𝒜 p j hI.wt hS (s gg.1 * s gg.2) (s (gg.1 * gg.2))
    (by rw [map_mul, hs, hs, hs, map_mul]) (hmul _ _ (UpperTheory.graded_matrix_mul_inv 𝒜 _ _ (hsg _) (hsg _)).1 (hsg _))
  choose A hA hAw using fun (v : ι) (g : F.D v) => exists_ex 𝒜 p j hI.wt hS (s (F.loc v g)) (ρ v g)
    (by rw [hs, hρ']) (hmul _ _ (hsg _) (hρg _ _))
  have hKc : IsLocallyConstant K := by
    refine IsLocallyConstant.desc K hS.ex ?_ fun _ _ => hS.ex_inj hinj
    have e : hS.ex ∘ K = fun gg => s gg.1 * s gg.2 * (s (gg.1 * gg.2))⁻¹ := funext fun gg => by
      rw [hK gg, mul_inv_cancel_right]; rfl
    rw [e]
    exact ((hsl.comp_continuous continuous_fst).mul (hsl.comp_continuous continuous_snd)).mul
      (hsl.comp_continuous continuous_mul).inv
  have hAc : ∀ v, IsLocallyConstant (A v) := fun v => by
    refine IsLocallyConstant.desc (A v) hS.ex ?_ fun _ _ => hS.ex_inj hinj
    have e : hS.ex ∘ A v = fun g => s (F.loc v g) * (ρ v g)⁻¹ := funext fun g => by
      rw [hA v g, mul_inv_cancel_right]; rfl
    rw [e]
    exact (hsl.comp_continuous (hloc v)).mul (hρL v).inv
  let κ : (RingHom.ker p →ₗ[O] ResidueField O) → Γ × Γ → Gb (ResidueField O) j := fun φ gg =>
    ⟨(K gg).map φ, fun a b hab => by rw [Matrix.map_apply, hKw gg a b hab, map_zero]⟩
  let α : (RingHom.ker p →ₗ[O] ResidueField O) → ∀ v, F.D v → Gb (ResidueField O) j := fun φ v g =>
    ⟨(A v g).map φ, fun a b hab => by rw [Matrix.map_apply, hAw v g a b hab, map_zero]⟩
  have hval : Function.Injective (Gb.val : Gb (ResidueField O) j → _) := Subtype.val_injective
  have hZ : ∀ φ, (κ φ, α φ) ∈ F.framedTwoCocycles j := fun φ => by
    refine ⟨⟨?_, fun g g' k => hval ?_⟩, (Submodule.mem_iInf _).2 fun v => ⟨?_, ?_⟩⟩
    · exact (IsLocallyConstant.desc (κ φ) Gb.val (hKc.comp fun Y => Y.map φ) hval).continuous
    · have e := congrArg (fun Y => Y.map φ) (hS.coc F.η F.Ψ hinj s hsr hsm K (fun g g' => hK (g, g')) g g' k)
      simp only [Matrix.map_sub _ (map_sub φ), Matrix.map_add _ (map_add φ), act_map,
        Matrix.map_zero _ (map_zero φ)] at e
      show (F.gbar j g (κ φ (g', k))).val - _ + _ - _ = _
      rw [Frame.gbar, Frame.Ψbar, act_val]
      exact e
    · exact (IsLocallyConstant.desc (α φ v) Gb.val ((hAc v).comp fun Y => Y.map φ) hval).continuous
    · funext ⟨g, g'⟩
      apply hval
      have e := congrArg (fun Y => Y.map φ) (hS.cob (F.ηv v) (F.Ψv v) hinj (fun g => s (F.loc v g)) (ρ v) (hρr v)
        (fun gg => K (F.loc v gg.1, F.loc v gg.2)) (fun g g' => by rw [map_mul]; exact hK (_, _)) (A v) (hA v) g g')
      simp only [Matrix.map_sub _ (map_sub φ), Matrix.map_add _ (map_add φ), act_map] at e
      show (F.gbar j (F.loc v g) (α φ v g')).val - _ + _ = _
      rw [Frame.gbar, Frame.Ψbar, act_val]
      exact e
  obtain ⟨φ, hφ, hB⟩ : ∃ φ, φ ≠ 0 ∧ (κ φ, α φ) ∈ F.framedTwoCoboundaries j := by
    have : Finite (F.Ob j) := Module.finite_of_finite (ResidueField O)
    have hn : ¬ Function.Injective fun φ => (Submodule.Quotient.mk ⟨_, hZ φ⟩ : F.Ob j) := fun hi => by
      have h1 := Nat.card_le_card_of_injective _ hi
      rw [UpperTheory.card_dual_residueField_eq_card_of_maximalIdeal_smul_eq_zero (O := O) (N := RingHom.ker p) (fun a ha x => Subtype.ext (by
        have h2 := hS.kill (algebraMap O R a) (map_nonunit (algebraMap O R) a ha) x
        rw [← Algebra.smul_def] at h2
        exact h2))] at h1
      rw [← Module.natCard_eq_pow_finrank (K := ResidueField O) (V := F.Ob j)] at hlt
      exact absurd hlt (not_lt.2 h1)
    obtain ⟨φ₁, φ₂, e, hne⟩ := Function.not_injective_iff.1 hn
    refine ⟨φ₁ - φ₂, sub_ne_zero.2 hne, ?_⟩
    exact (Submodule.Quotient.eq _).1 e
  obtain ⟨R'', _, _, _, p₁, q, ε, hp₁, hq, hqi, hε, hqε, hm, hk⟩ := UpperTheory.exists_small_extension_factorization_of_functional p hI.kill hI.le φ hφ
  have hS' : Sm ε := ⟨hm, hk⟩
  have hqp : ∀ x : GG 3 R, GG.map (q : R'' →+* R') (GG.map (p₁ : R →+* R'') x) = GG.map (p : R →+* R') x :=
    fun x => by rw [← hq]; rfl
  obtain ⟨r, hr, hrc, hrs⟩ := unobs F hF hV hS' j (fun g => GG.map (p₁ : R →+* R'') (s g)) hsr
    (fun g => red_of_map q _ _ g _ (by rw [hqp, hs]; exact hr'.red g)) (hsc.comp fun X => X.map p₁)
    (fun v => push p₁ (ρ v))
    (fun v => ⟨(hρr v).mult, fun g => red_of_map q _ _ g _ (by
      rw [MonoidHom.comp_apply, hqp, hρ']; exact hr'.red _)⟩)
    (fun v => UpperTheory.locAt_push_of_locAt F p₁ v _ (hρl v)) (κ φ) (α φ)
    (fun g g' => by rw [← map_mul, hK (g, g'), map_mul, map_ex hS hS' p₁ φ hε]; rfl)
    (fun v g => by rw [hA v g, map_mul, map_ex hS hS' p₁ φ hε]; rfl) hB
  have hqs : Function.Surjective q := by
    rw [← hq] at hp
    exact Function.Surjective.of_comp hp
  obtain ⟨r₂, h1, h2⟩ := UpperTheory.lift_along_surjection_graded F hF g₁ hg₁ q hqs r r' hr hrc (MonoidHom.ext fun g => by
    obtain ⟨Y, hY⟩ := hrs g
    rw [MonoidHom.comp_apply, hY, map_mul, map_ex_one hS' q hqε, one_mul, hqp, hs]) hr'.toCondN
  exact ⟨R'', inferInstance, inferInstance, inferInstance, p₁, q, r₂, hp₁, hq, hqi, h1, h2⟩
