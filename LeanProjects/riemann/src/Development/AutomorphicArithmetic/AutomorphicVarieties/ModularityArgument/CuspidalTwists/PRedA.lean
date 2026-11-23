import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalTwists.PromodularityCaseThree
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.SpaceMap
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RedDim
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RedDual
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoQuot
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoRes

open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Cu

private theorem lifts_map {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] {Φ : Fr O Γ} {Λ : Type} [CommRing Λ]
    [IsLocalRing Λ] {a : O →+* Λ} {c : PD Φ.ι Γ (ResidueField Λ)} {R R' : Type} [CommRing R] [Algebra Λ R] [IsCO Λ R]
    [CommRing R'] [Algebra Λ R'] [IsCO Λ R'] {P : PD Φ.ι Γ R} (h : Φ.Lifts a c P) (f : R →ₐ[Λ] R') :
    Φ.Lifts a c (P.map (f : R →+* R')) := by
  refine ⟨?_, h.cont.map _ fun y hy => ?_, ?_⟩
  · have h1 := h.pair.map (f : R →+* R')
    rwa [← RingHom.comp_assoc, AlgHom.comp_algebraMap] at h1
  · show f y ∈ maximalIdeal R'
    rw [← res_eq_zero_iff Λ, res_map, res_eq_zero_iff]
    exact hy
  · rw [PD.map_map, ← h.red]
    congr 1
    exact RingHom.ext fun x => res_map f x

private theorem lc_dual {Γ k : Type} [TopologicalSpace Γ] [Field k] {f : Γ → DualNumber k}
    (h : AdicCont (maximalIdeal (DualNumber k)) f) : IsLocallyConstant f := by
  have hm : ∀ x : DualNumber k, x ∈ maximalIdeal (DualNumber k) → x.fst = 0 := fun x hx => by
    rwa [mem_maximalIdeal, mem_nonunits_iff, TrivSqZeroExt.isUnit_iff_isUnit_fst, isUnit_iff_ne_zero, not_not] at hx
  have h2 : maximalIdeal (DualNumber k) ^ 2 = ⊥ := by
    rw [sq, eq_bot_iff, Ideal.mul_le]
    intro x hx y hy
    rw [Ideal.mem_bot]
    ext <;> simp [hm x hx, hm y hy]
  refine IsLocallyConstant.desc f _ (h 2) fun x y e => ?_
  rw [Ideal.Quotient.eq, h2, Ideal.mem_bot, sub_eq_zero] at e
  exact e

private theorem hom_of_der {O A k : Type} [CommRing O] [CommRing A] [Algebra O A] [CommRing k] [Algebra O k]
    (x : A →ₐ[O] k) (D : A →ₗ[O] k) (hD : D ∈ PtDer x k) :
    ∃ y : A →ₐ[O] DualNumber k, ∀ f, (y f).fst = x f ∧ (y f).snd = D f := by
  have hD' : ∀ f g, D (f * g) = x f • D g + x g • D f := hD
  have h1 : D 1 = 0 := by
    have := hD' 1 1
    simp only [mul_one, map_one, one_smul] at this
    exact left_eq_add.1 this
  refine ⟨{ toFun := fun f => (x f, D f)
            map_one' := TrivSqZeroExt.ext (map_one x) h1
            map_mul' := fun f g => TrivSqZeroExt.ext (map_mul x f g) ?_
            map_zero' := TrivSqZeroExt.ext (map_zero x) (map_zero D)
            map_add' := fun f g => TrivSqZeroExt.ext (map_add x f g) (map_add D f g)
            commutes' := fun t => TrivSqZeroExt.ext (x.commutes t) ?_ }, fun f => ⟨rfl, rfl⟩⟩
  · refine Eq.trans ?_ (DualNumber.snd_mul ((x f, D f) : DualNumber k) (x g, D g)).symm
    show D (f * g) = x f * D g + D f * x g
    rw [hD', smul_eq_mul, smul_eq_mul, mul_comm (D f)]
  · show D (algebraMap O A t) = 0
    rw [Algebra.algebraMap_eq_smul_one, map_smul, h1, smul_zero]

theorem UpperTheory.V.Cu.redA_of : RedTanA → RedA := by
  intro htan
  unfold RedTanA at htan
  unfold RedA
  intro O Γ _ _ _ _ _ _ Φ l _ Λ _ _ _ _ _ a hstd d C hB c hc hA hent R _ _ _ P hP S hS hY
  set I := redIdeal S P.r with hI
  by_cases htop : I = ⊤
  · haveI : Subsingleton (R ⧸ I) := Ideal.Quotient.subsingleton_iff.2 htop
    rw [ringKrullDim_eq_bot_of_subsingleton]
    exact bot_le
  haveI : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.2 htop
  let p : R →ₐ[Λ] R ⧸ I := Ideal.Quotient.mkₐ Λ I
  have hp : Function.Surjective p := Ideal.Quotient.mkₐ_surjective Λ I
  haveI : IsCO Λ (R ⧸ I) := co_quot Λ R (R ⧸ I) p hp
  haveI : IsCO Λ (DualNumber (ResidueField Λ)) := (co_res Λ).2
  have hr : ∀ g i j, res Λ R (P.r g i j) = c.r g i j := fun g i j =>
    congrArg (fun Q : PD Φ.ι Γ (ResidueField Λ) => Q.r g i j) hP.1.red
  have hn : ∀ v i j, res Λ R (P.n v i j) = c.n v i j := fun v i j =>
    congrArg (fun Q : PD Φ.ι Γ (ResidueField Λ) => Q.n v i j) hP.1.red
  have hz : ∀ g i j, i ≠ j → wt i j ∉ S → p (P.r g i j) = 0 := fun g i j h1 h2 =>
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span ⟨g, i, j, h1, h2, rfl⟩)
  have hsupp : Supp S c.r := fun g i j h1 h2 => by rw [← hr, ← res_map p, hz g i j h1 h2, map_zero]
  refine redDim (Λ := Λ) (R ⧸ I) (d + 20 * C) ?_
  let L : PtDer (res Λ (R ⧸ I)) (ResidueField Λ) →ₗ[ResidueField Λ]
      (Γ → M4 (ResidueField Λ)) × (Φ.ι → M4 (ResidueField Λ)) :=
    { toFun := fun D => (fun g => (P.r g).map (fun x => D.1 (p x)) * c.r g⁻¹,
        fun v => (P.n v).map (fun x => D.1 (p x)) * adj (c.n v))
      map_add' := fun D D' => Prod.ext
        (_root_.funext fun g => add_mul ((P.r g).map fun x => D.1 (p x)) ((P.r g).map fun x => D'.1 (p x)) _)
        (_root_.funext fun v => add_mul ((P.n v).map fun x => D.1 (p x)) ((P.n v).map fun x => D'.1 (p x)) _)
      map_smul' := fun t D => Prod.ext
        (_root_.funext fun g => Matrix.smul_mul t ((P.r g).map fun x => D.1 (p x)) _)
        (_root_.funext fun v => Matrix.smul_mul t ((P.n v).map fun x => D.1 (p x)) _) }
  have hy : ∀ D : PtDer (res Λ (R ⧸ I)) (ResidueField Λ), ∃ y : (R ⧸ I) →ₐ[Λ] DualNumber (ResidueField Λ),
      ∀ f, (y f).fst = res Λ (R ⧸ I) f ∧ (y f).snd = D.1 f := fun D =>
    hom_of_der _ D.1 D.2
  have hmem : ∀ D, L D ∈ Submodule.span (ResidueField Λ) (Φ.Tan S c) := fun D => by
    obtain ⟨y, hy⟩ := hy D
    have hl := lifts_map hP.1 (y.comp p)
    have h := redDual Φ _ S c _ (fun _ => rfl) hl.pair (fun i j => lc_dual (hl.cont i j))
      (fun g i j => ((hy _).1.trans (res_map p _)).trans (hr g i j))
      (fun v i j => ((hy _).1.trans (res_map p _)).trans (hn v i j))
      (fun g i j h1 h2 => by
        show y (p (P.r g i j)) = 0
        rw [hz g i j h1 h2, map_zero])
    refine Submodule.subset_span ?_
    convert h using 1
    refine Prod.ext (_root_.funext fun g => ?_) (_root_.funext fun v => ?_)
    · exact congrArg (· * c.r g⁻¹) (Matrix.ext fun i j => (hy _).2.symm)
    · exact congrArg (· * adj (c.n v)) (Matrix.ext fun i j => (hy _).2.symm)
  have hinj : Function.Injective L := by
    rw [injective_iff_map_eq_zero]
    intro D hD
    obtain ⟨y, h1⟩ := hy D
    obtain ⟨y0, h0⟩ := hy 0
    have e1 : ∀ g i j, D.1 (p (P.r g i j)) = 0 := fun g i j => by
      have e : (P.r g).map (fun x => D.1 (p x)) * c.r g⁻¹ = 0 := congrFun (congrArg Prod.fst hD) g
      have e' := congrArg (· * c.r g) e
      simp only [mul_assoc, ← map_mul, inv_mul_cancel, map_one, mul_one, zero_mul] at e'
      exact congrFun (congrFun e' i) j
    have e2 : ∀ v i j, D.1 (p (P.n v i j)) = 0 := fun v i j => by
      have e : (P.n v).map (fun x => D.1 (p x)) * adj (c.n v) = 0 := congrFun (congrArg Prod.snd hD) v
      have e' := congrArg (· * c.n v) e
      have hu : adj (c.n v) * c.n v = 1 := (hc.pair.low v).1.trans (one_smul _ _)
      simp only [mul_assoc, hu, mul_one, zero_mul] at e'
      exact congrFun (congrFun e' i) j
    have key : ∀ x, D.1 x = 0 → y x = y0 x := fun x hx =>
      TrivSqZeroExt.ext ((h1 x).1.trans (h0 x).1.symm) (((h1 x).2.trans hx).trans (h0 x).2.symm)
    have e : y.comp p = y0.comp p := by
      refine (hP.2 _ _ (lifts_map hP.1 (y0.comp p))).unique ?_ rfl
      exact PD.ext (MonoidHom.ext fun g => Matrix.ext fun i j => key _ (e1 g i j))
        (_root_.funext fun v => Matrix.ext fun i j => key _ (e2 v i j))
    refine Subtype.ext (LinearMap.ext fun x => ?_)
    obtain ⟨x, rfl⟩ := hp x
    have e3 : y (p x) = y0 (p x) := AlgHom.congr_fun e x
    rw [← (h1 _).2, e3, (h0 _).2]
  have hle := LinearMap.rank_le_of_injective (L.codRestrict _ hmem) fun x x' e => hinj (congrArg Subtype.val e)
  have hmemS : ∀ w : ℤ × ℤ, w ≠ (0, 0) → Ent c.r w → w ∈ S := by
    rintro w hw ⟨g, i, j, hij, hne⟩
    by_contra hS'
    have hij' : i ≠ j := by
      rintro rfl
      apply hw
      rw [← hij]
      simp [wt]
    exact hne (hsupp g i j hij' (by rw [hij]; exact hS'))
  have hcond : -wPs ∈ S ∨ (-wBe ∈ S ∧ -wTh ∈ S ∧ S ≠ yY) := by
    rcases hent with h | ⟨h1, h2⟩
    · exact Or.inl (hmemS _ (by decide) h)
    · exact Or.inr ⟨hmemS _ (by decide) h1,
        hmemS _ (by decide) h2, hY⟩
  refine hle.trans ((htan Φ _ hstd.ok d C hB c hc hA S hS hcond hsupp).trans ?_)
  push_cast
  rfl
