import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.SubThickRees
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.IsCompl

set_option backward.isDefEq.respectTransparency false

namespace GlobalTheory.CompanionTheory.EtaleLift

open TensorProduct

noncomputable def tensorAwayEquiv {Q Qb M D : Type} [CommRing Q] [CommRing Qb] [CommRing M] [CommRing D]
    [Algebra Q Qb] [Algebra Q M] [Algebra Q D] [Algebra M D] [IsScalarTower Q M D]
    (J : M) [IsLocalization.Away J D] (h : IsUnit ((1 : Qb) ⊗ₜ[Q] J)) :
    Qb ⊗[Q] M ≃ₐ[Qb] Qb ⊗[Q] D :=
  let f : M →+* Qb ⊗[Q] M := (Algebra.TensorProduct.includeRight : M →ₐ[Q] Qb ⊗[Q] M).toRingHom
  let l : D →+* Qb ⊗[Q] M := IsLocalization.Away.lift J (g := f) h
  have hl : ∀ m, l (algebraMap M D m) = (1 : Qb) ⊗ₜ[Q] m := fun m =>
    IsLocalization.Away.lift_eq J h m
  let la : D →ₐ[Q] Qb ⊗[Q] M :=
    { l with
      commutes' := fun r => by
        change l (algebraMap Q D r) = _
        rw [IsScalarTower.algebraMap_apply Q M D, hl]
        exact Algebra.TensorProduct.includeRight.commutes r }
  AlgEquiv.ofAlgHom
    (Algebra.TensorProduct.map (AlgHom.id Qb Qb) (IsScalarTower.toAlgHom Q M D))
    (Algebra.TensorProduct.lift (Algebra.ofId Qb _) la fun _ _ => Commute.all _ _)
    (by
      ext d
      have key : ((Algebra.TensorProduct.map (AlgHom.id Qb Qb) (IsScalarTower.toAlgHom Q M D)).toRingHom.comp
          l).comp (algebraMap M D) = (Algebra.TensorProduct.includeRight : D →ₐ[Q] Qb ⊗[Q] D).toRingHom.comp
          (algebraMap M D) := by
        ext m
        simp [hl]
      have := IsLocalization.ringHom_ext (Submonoid.powers J) key
      have h2 : Algebra.TensorProduct.map (AlgHom.id Qb Qb) (IsScalarTower.toAlgHom Q M D) (l d) =
          (1 : Qb) ⊗ₜ[Q] d := DFunLike.congr_fun this d
      simpa [la, ← Algebra.TensorProduct.one_def] using h2)
    (by
      ext m
      simp [hl, la])

theorem exists_etale_lift_of_surjective {Q Qb : Type} [CommRing Q] [CommRing Qb] [Algebra Q Qb]
    (hs : Function.Surjective (algebraMap Q Qb))
    (A0 : Type) [CommRing A0] [Algebra Qb A0] [hE : Algebra.Etale Qb A0] :
    ∃ (D : Type) (_ : CommRing D) (_ : Algebra Q D), Algebra.Etale Q D ∧
      Nonempty (Qb ⊗[Q] D ≃ₐ[Qb] A0) := by
  obtain ⟨ι, σ, _, _, P, hP⟩ :=
    ((Algebra.Etale.iff_isStandardSmoothOfRelativeDimension_zero (R := Qb) (S := A0)).mp hE).out
  classical
  have := Fintype.ofFinite σ
  have hsurj := MvPolynomial.map_surjective (σ := ι) (algebraMap Q Qb) hs
  choose g hg using fun j : σ => hsurj (P.relation j)
  let N := Algebra.PreSubmersivePresentation.naive (R := Q) (v := g) P.map P.map_inj
  let Nb := N.baseChange Qb
  have hrel : ∀ j, Nb.relation j = P.relation j := by
    intro j
    show MvPolynomial.map (algebraMap Q Qb) (g j) = P.relation j
    exact hg j
  have hker : RingHom.ker (MvPolynomial.aeval (R := Qb) Nb.val) =
      RingHom.ker (MvPolynomial.aeval (R := Qb) P.val) := by
    rw [← Algebra.Generators.ker_eq_ker_aeval_val, ← Algebra.Generators.ker_eq_ker_aeval_val,
      ← Nb.span_range_relation_eq_ker, ← P.span_range_relation_eq_ker]
    congr 1
    ext x
    simp [hrel]
  let e : Qb ⊗[Q] (MvPolynomial ι Q ⧸ Ideal.span (Set.range g)) ≃ₐ[Qb] A0 :=
    (Ideal.quotientKerAlgEquivOfSurjective Nb.aeval_val_surjective).symm.trans
      ((Ideal.quotientEquivAlgOfEq Qb hker).trans
        (Ideal.quotientKerAlgEquivOfSurjective P.aeval_val_surjective))
  have He : ∀ x, e (MvPolynomial.aeval (R := Qb) Nb.val x) = MvPolynomial.aeval (R := Qb) P.val x := by
    intro x
    have h1 : (Ideal.quotientKerAlgEquivOfSurjective Nb.aeval_val_surjective).symm
        (MvPolynomial.aeval (R := Qb) Nb.val x) = Ideal.Quotient.mk _ x := by
      rw [AlgEquiv.symm_apply_eq]; rfl
    simp only [e, AlgEquiv.trans_apply, h1, Ideal.quotientEquivAlgOfEq_mk]
    rfl
  have hM : Nb.jacobiMatrix = P.jacobiMatrix := by
    ext i j
    rw [Nb.jacobiMatrix_apply, P.jacobiMatrix_apply, hrel]
    rfl
  have hjacb : IsUnit Nb.jacobian := by
    have h2 : e Nb.jacobian = P.jacobian := by
      rw [Nb.jacobian_eq_jacobiMatrix_det, P.jacobian_eq_jacobiMatrix_det,
        Algebra.Generators.algebraMap_apply, Algebra.Generators.algebraMap_apply, hM]
      exact He _
    exact (isUnit_map_iff e _).mp (h2 ▸ P.jacobian_isUnit)
  have hjac : IsUnit ((1 : Qb) ⊗ₜ[Q] N.jacobian) := by
    rw [← Algebra.PreSubmersivePresentation.baseChange_jacobian]
    exact hjacb
  let L := Algebra.SubmersivePresentation.localizationAway (Localization.Away N.jacobian) N.jacobian
  let S : Algebra.SubmersivePresentation Q (Localization.Away N.jacobian) (Unit ⊕ ι) (Unit ⊕ σ) :=
    { __ := L.toPreSubmersivePresentation.comp N
      jacobian_isUnit := by
        rw [Algebra.PreSubmersivePresentation.comp_jacobian_eq_jacobian_smul_jacobian,
          Algebra.smul_def]
        exact (IsLocalization.Away.algebraMap_isUnit _).mul L.jacobian_isUnit }
  have hst : Algebra.IsStandardSmoothOfRelativeDimension 0 Q (Localization.Away N.jacobian) := by
    refine S.isStandardSmoothOfRelativeDimension ?_
    refine (Algebra.PreSubmersivePresentation.dimension_comp_eq_dimension_add_dimension
      L.toPreSubmersivePresentation N).trans ?_
    have hN : N.dimension = 0 := by rw [← hP]; rfl
    rw [hN]
    simp [Algebra.Presentation.dimension]
  exact ⟨Localization.Away N.jacobian, inferInstance, inferInstance, inferInstance,
    ⟨(tensorAwayEquiv N.jacobian hjac).symm.trans e⟩⟩

theorem tensor_existsUnique_lift {P Qb R B : Type} [CommRing P] [CommRing Qb] [CommRing R] [CommRing B]
    [Algebra P Qb] [Algebra P R] (u : Qb →+* B) (g : R →+* B)
    (h : ∀ p, g (algebraMap P R p) = u (algebraMap P Qb p)) :
    ∃! w : Qb ⊗[P] R →+* B, (∀ b, w (b ⊗ₜ[P] 1) = u b) ∧ ∀ r, w ((1 : Qb) ⊗ₜ[P] r) = g r := by
  letI : Algebra P B := (u.comp (algebraMap P Qb)).toAlgebra
  let ua : Qb →ₐ[P] B := { u with commutes' := fun _ => rfl }
  let ga : R →ₐ[P] B := { g with commutes' := h }
  refine ⟨(Algebra.TensorProduct.productMap ua ga).toRingHom, ⟨fun b => ?_, fun r => ?_⟩, ?_⟩
  · simp [ua]
  · simp [ga]
  · rintro w ⟨h1, h2⟩
    refine RingHom.ext fun x => ?_
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul b r =>
      have : b ⊗ₜ[P] r = (b ⊗ₜ[P] (1 : R)) * ((1 : Qb) ⊗ₜ[P] r) := by simp
      rw [this, map_mul, h1, h2]
      simp [ua, ga]

theorem exists_lift_hom {P Q Qb R : Type} [CommRing P] [CommRing Q] [CommRing Qb] [CommRing R]
    (ρ : P →+* R) (μ : P →+* Qb) (π : Q →+* Qb) (hs : Function.Surjective π) (hρ : ρ.Etale) :
    ∃ (D : Type) (_ : CommRing D) (q : Q →+* D), q.Etale ∧ ∀ L : Ideal D, L = (RingHom.ker π).map q →
      ∃ (jb : Qb →+* D ⧸ L) (j : R →+* D ⧸ L), (∀ x, jb (π x) = Ideal.Quotient.mk L (q x)) ∧
        j.comp ρ = jb.comp μ ∧
        ∀ (B : Type) [CommRing B] (u : Qb →+* B) (g : R →+* B), g.comp ρ = u.comp μ →
          ∃! w : (D ⧸ L) →+* B, w.comp jb = u ∧ w.comp j = g := by
  letI := ρ.toAlgebra
  letI := μ.toAlgebra
  letI := π.toAlgebra
  haveI : Algebra.Etale P R := hρ
  obtain ⟨D, _, _, hD, ⟨e⟩⟩ := exists_etale_lift_of_surjective (Q := Q) (Qb := Qb) hs (Qb ⊗[P] R)
  refine ⟨D, inferInstance, algebraMap Q D, RingHom.etale_algebraMap.mpr hD, ?_⟩
  rintro L rfl
  set L : Ideal D := (RingHom.ker π).map (algebraMap Q D) with hL
  let c : Q →+* D ⧸ L := (Ideal.Quotient.mk L).comp (algebraMap Q D)
  have hc : RingHom.ker π ≤ RingHom.ker c := by
    intro x hx
    rw [RingHom.mem_ker]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem _ hx)
  let jb0 : Qb →+* D ⧸ L := π.liftOfSurjective hs ⟨c, hc⟩
  have hjb0 : ∀ x, jb0 (π x) = c x := fun x =>
    RingHom.liftOfRightInverse_comp_apply π _ _ ⟨c, hc⟩ x
  let jba : Qb →ₐ[Q] D ⧸ L := { jb0 with commutes' := hjb0 }
  let F1 : Qb ⊗[Q] D →ₐ[Q] D ⧸ L := Algebra.TensorProduct.productMap jba (Ideal.Quotient.mkₐ Q L)
  have hF1 : ∀ b d, F1 (b ⊗ₜ[Q] d) = jb0 b * Ideal.Quotient.mk L d := fun b d => by
    simp [F1, jba]
  have hone : ∀ x : Q, (1 : Qb) ⊗ₜ[Q] (algebraMap Q D x) = (π x) ⊗ₜ[Q] (1 : D) := fun x => by
    rw [Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul, TensorProduct.smul_tmul',
      Algebra.smul_def, mul_one]
    rfl
  let ir : D →+* Qb ⊗[Q] D := (Algebra.TensorProduct.includeRight : D →ₐ[Q] Qb ⊗[Q] D).toRingHom
  have hkill : ∀ a ∈ L, ir a = 0 := by
    have : L ≤ RingHom.ker ir := by
      refine Ideal.map_le_iff_le_comap.mpr fun x hx => ?_
      rw [Ideal.mem_comap, RingHom.mem_ker]
      change (1 : Qb) ⊗ₜ[Q] (algebraMap Q D x) = 0
      rw [hone, RingHom.mem_ker.mp hx, TensorProduct.zero_tmul]
    exact fun a ha => this ha
  let F2 : D ⧸ L →+* Qb ⊗[Q] D := Ideal.Quotient.lift L ir hkill
  have hF2 : ∀ d, F2 (Ideal.Quotient.mk L d) = (1 : Qb) ⊗ₜ[Q] d := fun d => rfl
  let F : Qb ⊗[Q] D ≃+* D ⧸ L := RingEquiv.ofRingHom F1.toRingHom F2
    (by
      apply Ideal.Quotient.ringHom_ext
      ext d
      change F1 (F2 (Ideal.Quotient.mk L d)) = _
      rw [hF2, hF1, map_one, one_mul]
      rfl)
    (by
      refine RingHom.ext fun x => ?_
      change F2 (F1 x) = x
      induction x using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => simp only [map_add, hx, hy]
      | tmul b d =>
        obtain ⟨x, rfl⟩ := hs b
        rw [hF1, hjb0, map_mul]
        change F2 (Ideal.Quotient.mk L (algebraMap Q D x)) * F2 (Ideal.Quotient.mk L d) = _
        rw [hF2, hF2, hone]
        simp)
  have hFl : ∀ b d, F (b ⊗ₜ[Q] d) = jb0 b * Ideal.Quotient.mk L d := hF1
  let ψ : Qb ⊗[P] R ≃+* D ⧸ L := e.symm.toRingEquiv.trans F
  have hψ : ∀ b, ψ (b ⊗ₜ[P] (1 : R)) = jb0 b := fun b => by
    have h1 : e.symm (b ⊗ₜ[P] (1 : R)) = b ⊗ₜ[Q] (1 : D) :=
      e.symm.commutes b
    change F (e.symm (b ⊗ₜ[P] (1 : R))) = _
    rw [h1, hFl, map_one, mul_one]
  let il : Qb →+* Qb ⊗[P] R := (Algebra.TensorProduct.includeLeft : Qb →ₐ[P] Qb ⊗[P] R).toRingHom
  let ir' : R →+* Qb ⊗[P] R := (Algebra.TensorProduct.includeRight : R →ₐ[P] Qb ⊗[P] R).toRingHom
  refine ⟨jb0, (ψ : _ →+* _).comp ir', hjb0, ?_, ?_⟩
  · ext p
    change ψ ((1 : Qb) ⊗ₜ[P] (algebraMap P R p)) = jb0 (algebraMap P Qb p)
    rw [← hψ]
    congr 1
    rw [Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul, TensorProduct.smul_tmul',
      Algebra.smul_def, mul_one]
  · intro B _ u g hg
    obtain ⟨w, ⟨h1, h2⟩, hw⟩ := tensor_existsUnique_lift (P := P) u g
      (fun p => DFunLike.congr_fun hg p)
    refine ⟨w.comp (ψ.symm : _ →+* _), ⟨?_, ?_⟩, ?_⟩
    · ext b
      change w (ψ.symm (jb0 b)) = u b
      rw [← hψ, RingEquiv.symm_apply_apply, h1]
    · ext r
      change w (ψ.symm (ψ ((1 : Qb) ⊗ₜ[P] r))) = g r
      rw [RingEquiv.symm_apply_apply, h2]
    · rintro w' ⟨h3, h4⟩
      have : w'.comp (ψ : _ →+* _) = w := by
        refine hw _ ⟨fun b => ?_, fun r => ?_⟩
        · change w' (ψ (b ⊗ₜ[P] 1)) = u b
          rw [hψ]
          exact DFunLike.congr_fun h3 b
        · exact DFunLike.congr_fun h4 r
      rw [← this]
      ext x
      simp

theorem nonempty_lift {O R Λ : Type} [CommRing O] [CommRing R] [CommRing Λ] (a : O →+* R) {d : ℕ}
    (T : Fin d → R) (I : Ideal Λ) (κ : O →+* Λ ⧸ I)
    (het : (MvPolynomial.eval₂Hom a T).Etale) : Nonempty (CrystallineSemistableComparison.B.Lift a T Λ I κ) := by
  let μ : MvPolynomial (Fin d) O →+* MvPolynomial (Fin d) (Λ ⧸ I) := MvPolynomial.map κ
  let π : MvPolynomial (Fin d) Λ →+* MvPolynomial (Fin d) (Λ ⧸ I) :=
    MvPolynomial.map (Ideal.Quotient.mk I)
  have hs : Function.Surjective π := MvPolynomial.map_surjective _ Ideal.Quotient.mk_surjective
  obtain ⟨D, _, q, hq, hL⟩ := exists_lift_hom (MvPolynomial.eval₂Hom a T) μ π hs het
  let i : Λ →+* D := q.comp MvPolynomial.C
  let t : Fin d → D := fun k => q (MvPolynomial.X k)
  have hqe : MvPolynomial.eval₂Hom i t = q := by
    apply MvPolynomial.ringHom_ext <;> simp [i, t]
  have hker : I.map i = (RingHom.ker π).map q := by
    have h0 : RingHom.ker π = I.map (MvPolynomial.C : Λ →+* MvPolynomial (Fin d) Λ) := by
      ext f
      rw [RingHom.mem_ker, MvPolynomial.mem_map_C_iff]
      constructor
      · intro hf m
        have := congrArg (MvPolynomial.coeff m) hf
        rw [MvPolynomial.coeff_map, MvPolynomial.coeff_zero] at this
        exact Ideal.Quotient.eq_zero_iff_mem.mp this
      · intro hf
        ext m
        rw [MvPolynomial.coeff_map, MvPolynomial.coeff_zero]
        exact Ideal.Quotient.eq_zero_iff_mem.mpr (hf m)
    rw [h0, Ideal.map_map]
  obtain ⟨jb, j, h1, h2, h3⟩ := hL (I.map i) hker
  have hjbC : ∀ x, jb (MvPolynomial.C (Ideal.Quotient.mk I x)) = Ideal.Quotient.mk _ (i x) := by
    intro x
    have := h1 (MvPolynomial.C x)
    rwa [show π (MvPolynomial.C x) = MvPolynomial.C (Ideal.Quotient.mk I x) by simp [π]] at this
  have hjbX : ∀ k, jb (MvPolynomial.X k) = Ideal.Quotient.mk _ (t k) := by
    intro k
    have := h1 (MvPolynomial.X k)
    rwa [show π (MvPolynomial.X k) = MvPolynomial.X k by simp [π]] at this
  have hj' : ∀ o x, Ideal.Quotient.mk I x = κ o → j (a o) = Ideal.Quotient.mk _ (i x) := by
    intro o x hx
    have e1 : MvPolynomial.eval₂Hom a T (MvPolynomial.C o) = a o := by simp
    have e2 : μ (MvPolynomial.C o) = MvPolynomial.C (Ideal.Quotient.mk I x) := by simp [μ, hx]
    have := DFunLike.congr_fun h2 (MvPolynomial.C o)
    rw [RingHom.comp_apply, RingHom.comp_apply, e1, e2, hjbC] at this
    exact this
  have hT' : ∀ k, j (T k) = Ideal.Quotient.mk _ (t k) := by
    intro k
    have e1 : MvPolynomial.eval₂Hom a T (MvPolynomial.X k) = T k := by simp
    have e2 : μ (MvPolynomial.X k) = MvPolynomial.X k := by simp [μ]
    have := DFunLike.congr_fun h2 (MvPolynomial.X k)
    rw [RingHom.comp_apply, RingHom.comp_apply, e1, e2, hjbX] at this
    exact this
  refine ⟨{ D := D, i := i, t := t, et := by rw [hqe]; exact hq, j := j, hj := hj', hT := hT',
            univ := ?_ }⟩
  intro B _ h g hI hg
  let hb : Λ ⧸ I →+* B := Ideal.Quotient.lift I h hI
  let u : MvPolynomial (Fin d) (Λ ⧸ I) →+* B := MvPolynomial.eval₂Hom hb fun k => g (T k)
  have huC : ∀ x, u (MvPolynomial.C (Ideal.Quotient.mk I x)) = h x := by
    intro x
    simp [u, hb]
  have huX : ∀ k, u (MvPolynomial.X k) = g (T k) := by
    intro k
    simp [u]
  have hc : g.comp (MvPolynomial.eval₂Hom a T) = u.comp μ := by
    apply MvPolynomial.ringHom_ext
    · intro o
      obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective (κ o)
      have e2 : μ (MvPolynomial.C o) = MvPolynomial.C (Ideal.Quotient.mk I x) := by simp [μ, hx]
      rw [RingHom.comp_apply, RingHom.comp_apply, e2, huC, MvPolynomial.coe_eval₂Hom,
        MvPolynomial.eval₂_C]
      exact hg o x hx
    · intro k
      have e2 : μ (MvPolynomial.X k) = MvPolynomial.X k := by simp [μ]
      rw [RingHom.comp_apply, RingHom.comp_apply, e2, huX, MvPolynomial.coe_eval₂Hom,
        MvPolynomial.eval₂_X]
  obtain ⟨w, ⟨hw1, hw2⟩, hw⟩ := h3 B u g hc
  have hwi : ∀ x, w (Ideal.Quotient.mk _ (i x)) = h x := by
    intro x
    rw [← hjbC, ← huC, ← hw1]
    rfl
  refine ⟨w.comp (Ideal.Quotient.mk _), ⟨RingHom.ext hwi, ?_⟩, ?_⟩
  · intro r z hz
    change w (Ideal.Quotient.mk _ z) = g r
    rw [hz]
    exact DFunLike.congr_fun hw2 r
  · rintro f' ⟨hf1, hf2⟩
    have hk : ∀ y ∈ I.map i, f' y = 0 := by
      have hle : I.map i ≤ RingHom.ker f' := Ideal.map_le_iff_le_comap.mpr fun x hx => by
        rw [Ideal.mem_comap, RingHom.mem_ker]
        exact (DFunLike.congr_fun hf1 x).trans (hI x hx)
      exact fun y hy => hle hy
    let w' : D ⧸ I.map i →+* B := Ideal.Quotient.lift _ f' hk
    have hw' : ∀ z, w' (Ideal.Quotient.mk _ z) = f' z := fun z => rfl
    have hww : w' = w := by
      refine hw w' ⟨?_, ?_⟩
      · apply MvPolynomial.ringHom_ext
        · intro c
          obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective c
          rw [RingHom.comp_apply, hjbC, hw', huC]
          exact DFunLike.congr_fun hf1 x
        · intro k
          rw [RingHom.comp_apply, hjbX, hw', huX]
          exact hf2 (T k) (t k) (hT' k).symm
      · refine RingHom.ext fun r => ?_
        obtain ⟨z, hz⟩ := Ideal.Quotient.mk_surjective (j r)
        rw [RingHom.comp_apply, ← hz, hw']
        exact hf2 r z hz
    rw [← hww]
    exact RingHom.ext fun z => rfl

end GlobalTheory.CompanionTheory.EtaleLift
