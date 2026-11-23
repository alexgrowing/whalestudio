import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Uniformization.SeriesFrame
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.HrelPf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntFamPull
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.MixedCrossIdentityGenericFibre
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationBaseChange
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem Modif.eq_comp_gp {R : Type} [CommRing R] [IsDomain R] (M : Modif R) {F : Type} [Field F]
    (ψ : FractionRing R →+* F) (x : Sp F ⟶ M.S) (hx : x ≫ M.π = spMap ψ ≫ jK R) : x = spMap ψ ≫ M.gp := by
  have := M.integral
  have hd := M.dominant
  let pt : Sp F := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum F)
  obtain ⟨B, e₀, hoi, P, hP⟩ : ∃ (B : CommRingCat) (e₀ : Spec B ⟶ M.S), IsOpenImmersion e₀ ∧ ∃ P, e₀ P = x pt :=
    ⟨_, M.S.affineCover.f (M.S.affineCover.idx (x pt)), M.S.affineCover.map_prop _, M.S.affineCover.covers (x pt)⟩
  have hsub : Set.range M.gp ⊆ Set.range e₀ := by
    obtain ⟨a, ha⟩ := hd.denseRange.exists_mem_open e₀.isOpenEmbedding.isOpen_range ⟨e₀ P, P, rfl⟩
    rintro _ ⟨x, rfl⟩
    rwa [Subsingleton.elim x a]
  have hsub' : Set.range x ⊆ Set.range e₀ := by
    rintro _ ⟨y, rfl⟩
    rw [Subsingleton.elim y pt]
    exact ⟨P, hP⟩
  obtain ⟨g', hfac⟩ : ∃ g', g' ≫ e₀ = M.gp := ⟨_, IsOpenImmersion.lift_fac e₀ M.gp hsub⟩
  obtain ⟨x', hfx⟩ : ∃ x', x' ≫ e₀ = x := ⟨_, IsOpenImmersion.lift_fac e₀ x hsub'⟩
  obtain ⟨g, rfl⟩ := Spec.map_surjective g'
  obtain ⟨g₁, rfl⟩ := Spec.map_surjective x'
  obtain ⟨ρ, hρ⟩ := Spec.map_surjective (e₀ ≫ M.π)
  have hcomp : ρ ≫ g = CommRingCat.ofHom (algebraMap R (FractionRing R)) := by
    apply Spec.map_injective
    rw [Spec.map_comp, hρ, ← Category.assoc, hfac, M.gp_π]
  have hcomp₁ : ρ ≫ g₁ = CommRingCat.ofHom (algebraMap R (FractionRing R)) ≫ CommRingCat.ofHom ψ := by
    apply Spec.map_injective
    rw [Spec.map_comp, hρ, ← Category.assoc, hfx, hx, Spec.map_comp]
  have hc : ∀ r, g.hom (ρ.hom r) = algebraMap R (FractionRing R) r := fun r => congrArg (fun f => f.hom r) hcomp
  have hc₁ : ∀ r, g₁.hom (ρ.hom r) = ψ (algebraMap R (FractionRing R) r) := fun r => congrArg (fun f => f.hom r) hcomp₁
  have hden : DenseRange (Spec.map g) := by
    rw [denseRange_iff_closure_range, e₀.isOpenEmbedding.isInducing.closure_eq_preimage_closure_image,
      ← Set.range_comp]
    have : (e₀ ∘ Spec.map g) = M.gp := by funext x; rw [← hfac]; rfl
    rw [this, hd.denseRange.closure_range, Set.preimage_univ]
  have hinj : Function.Injective g.hom := by
    have h2 := (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical g.hom).1 hden
    have hr := (affine_isReduced_iff _).1 (isReduced_of_isOpenImmersion e₀)
    rw [nilradical_eq_zero] at h2
    exact (RingHom.injective_iff_ker_eq_bot _).2 (le_bot_iff.1 h2)
  have key : g₁ = g ≫ CommRingCat.ofHom ψ := by
    ext b
    show g₁.hom b = ψ (g.hom b)
    obtain ⟨a, s, hs, hxs⟩ := IsFractionRing.div_surjective (A := R) (g.hom b)
    have hs0 : algebraMap R (FractionRing R) s ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hs
    have h0 : ρ.hom s * b = ρ.hom a := hinj (by rw [map_mul, hc, hc, ← hxs, mul_div_cancel₀ _ hs0])
    have h1 := congrArg g₁.hom h0
    rw [map_mul, hc₁, hc₁] at h1
    rw [← hxs, map_div₀, ← h1, mul_div_cancel_left₀ _ ((map_ne_zero ψ).2 hs0)]
  rw [← hfx, ← hfac, key, Spec.map_comp, Category.assoc]

theorem PullB.unique {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'}
    {D : DegPre R} {D' : DegPre R'} {hD : IsPullDeg φ D D'} {k : ℕ} {x : D'.X} {b : D.SecB k (hD.xe x)}
    {b₁ b₂ : D'.SecB k x} (H₁ : PullB hD x b b₁) (H₂ : PullB hD x b b₂) : b₁ = b₂ := by
  refine DVR.SecOps.sec_ext fun q => fn_ext fun y hy => ?_
  choose p hp using fun κ => exists_chart D.P.isLB ((hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) (D'.famφB x κ y))
  have e₁ := H₁ _ (𝟙 _) y p q hp (Set.mem_iInter.1 hy)
  have e₂ := H₂ _ (𝟙 _) y p q hp (Set.mem_iInter.1 hy)
  exact (Units.mul_right_inj _).1 (e₁.symm.trans e₂)

theorem PullB.eq_zero {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'}
    (hφ : Function.Injective φ) {D : DegPre R} {D' : DegPre R'} {hD : IsPullDeg φ D D'} {k : ℕ} {x : D'.X}
    {b : D.SecB k (hD.xe x)} {b' : D'.SecB k x} (H : PullB hD x b b') (h : ∀ q, b'.f q = 0) (p) : b.f p = 0 := by
  have : IsDominant (specOf φ) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical φ).2 (by
    rw [(RingHom.injective_iff_ker_eq_bot _).1 hφ]; exact bot_le)⟩
  have := IsSchemeTheoreticallyDominant.of_isDominant (specOf φ)
  have : Smooth D.P.A.hom := D.P.isAb.smooth
  have : IsSchemeTheoreticallyDominant (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) :=
    IsSchemeTheoreticallyDominant.of_isPullback (pull_grp hD).1.flip
  have : QuasiCompact (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) :=
    MorphismProperty.of_isPullback (P := @QuasiCompact) (pull_grp hD).1.flip inferInstance
  apply (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)).app_injective
  rw [map_zero]
  refine fn_ext fun y hy => ?_
  choose q hq using fun κ => exists_chart D'.P.isLB (D'.famφB x κ y)
  have e := H _ (𝟙 _) y p q (fun κ => by
    have a := Set.mem_iInter.1 hy κ
    exact (congrArg (fun m => m y ∈ D.P.L.U (p κ)) (ExpGTrans.famφB_pull hD x κ)).mpr a) hq
  have e' := e.trans ((congrArg _ ((congrArg (gs _ y _) (h q)).trans (DVR.hr_gs_zero _ _ _))).trans (mul_zero _))
  exact (gs_pull _ _ y _ hy _).trans (e'.trans (DVR.hr_gs_zero _ _ _).symm)

theorem expands_zero {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
    {A : PolAV (Sp (FractionRing R))} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (k : ℕ) :
    U.Expands k DVR.SecOps.secZero 0 := by
  refine ⟨1, one_ne_zero, DVR.SecOps.secZero, fun _ => DVR.SecOps.secZero, fun j₁ j₂ _ => ?_, fun α j₁ j₂ _ => ?_,
    fun e => ⟨∅, fun α _ j => map_zero _, fun p j₁ jf jt _ _ => ?_⟩⟩
  · exact ((congrArg _ (map_zero _)).trans (map_zero _)).trans ((congrArg _ (map_zero _)).trans (mul_zero _)).symm
  · exact ((congrArg _ (map_zero _)).trans (map_zero _)).trans ((congrArg _ (map_zero _)).trans (mul_zero _)).symm
  · exact ((congrArg _ ((congrArg _ (map_zero _)).trans (map_zero _))).trans (mul_zero _)).trans (Finset.sum_empty).symm

theorem IntFam.f_eq_zero {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R} {k : ℕ} (F : IntFam I D k)
    (h : F.F = 0) (x : D.X) (q) : (F.f x).f q = 0 := by
  have h₀ : GeneratorPullback.SecScal D.P.L (DegPre.famφ D (FractionRing R) x) (DegPre.famε k) (F.F.s x)
      (D.famφB x) (DegPre.famε k) DVR.SecOps.secZero (DegPre.prB D (FractionRing R)).left 1 := by
    rw [h]
    intro j₁ j₂ _
    exact ((congrArg _ (map_zero _)).trans (map_zero _)).trans ((congrArg _ (map_zero _)).trans (mul_zero _)).symm
  exact (IntegralExpansion.secIsMul_of_secScal D.P.isLB D.P.A.hom (a := 1) (IntegralExpansion.prB_app_injective D) h₀
    (by rw [Over.w (DegPre.prB D (FractionRing R))]; exact F.ext x) q).trans (mul_zero _)

theorem IntFam.eq_zero_of_two_scalars {W : Type} [CommRing W] [IsDomain W] {I : Ideal W} {D : DegData W I}
    {A : PolAV (Sp (FractionRing W))} {G : Over (Sp W)} [GrpObj G] [IsCommMonObj G] (U : Unif I D A G) {k : ℕ} (hk : 1 ≤ k)
    (F : IntFam I D.toPre k) {σ₁ σ₂ : H0 U.LG.L k} (e₁ : ∀ e, U.ExpandsAt e k σ₁ F.f) (e₂ : ∀ e, U.ExpandsAt e k σ₂ F.f)
    {b b' : W} (hb : b ≠ b') (H : ∀ y J, Good U.LG.L y J → ∃ u : ((pullback G.hom (jK W)).presheaf.stalk y)ˣ,
      gs (pullback.fst G.hom (jK W)) y ⊤ (scal G.hom b) * u.val * sval σ₁ (pullback.fst G.hom (jK W)) y J =
        gs (pullback.fst G.hom (jK W)) y ⊤ (scal G.hom b') * u.val * sval σ₂ (pullback.fst G.hom (jK W)) y J) :
    F.F = 0 := by
  have res : ∀ σ : H0 U.LG.L k, (∀ e, U.ExpandsAt e k σ F.f) → ∃ s : U.SecK k, U.Expands k s F.F ∧
      ∀ y J, Good U.LG.L y J → sval σ (pullback.fst G.hom (jK W)) y J = sval s (𝟙 _) y J := fun σ e => by
    obtain ⟨s, hs⟩ := UnifBaseChange.exists_secScal_one U.LG.L (fun _ : Fin 1 => 𝟙 G.left) (fun _ => (k : ℤ))
      (pullback.fst G.hom (jK W)) (fun _ => pullback.fst G.hom (jK W)) (funext fun _ => (Category.comp_id _).symm) σ
    refine ⟨s, ⟨1, one_ne_zero, σ, F.f, ?_, F.ext, e⟩, fun y J hJ => ?_⟩
    · rw [UnifBaseChange.scal_one]; exact hs
    · have v := DVR.hr_secScal_sval hs (𝟙 _) y hJ
      rwa [Category.id_comp, gs_eq _ y ⊤ trivial, map_one, map_one, _root_.one_mul] at v
  obtain ⟨s₁, x₁, v₁⟩ := res σ₁ e₁
  obtain ⟨s₂, x₂, v₂⟩ := res σ₂ e₂
  obtain rfl : s₁ = s₂ := ((U.expand k hk).2 F.F).unique x₁ x₂
  have hz : s₁ = DVR.SecOps.secZero := by
    refine DVR.SecOps.sec_ext (sec_ext_val U.LG.isLB fun y J hJ => ?_)
    obtain ⟨u, e⟩ := H y J hJ
    rw [v₁ y J hJ, v₂ y J hJ, ← sub_eq_zero, ← sub_mul, ← sub_mul] at e
    have hu : IsUnit (gs (pullback.fst G.hom (jK W)) y ⊤ (scal G.hom (b - b'))) := by
      rw [GenericCross.gs_scal, pullback.condition]
      exact GenericCross.isUnit_cst _ y (sub_ne_zero.2 hb)
    have hs : gs (pullback.fst G.hom (jK W)) y ⊤ (scal G.hom (b - b')) =
        gs (pullback.fst G.hom (jK W)) y ⊤ (scal G.hom b) - gs (pullback.fst G.hom (jK W)) y ⊤ (scal G.hom b') := by
      simp only [gs_eq _ y ⊤ trivial, scal, map_sub]
    rw [hs] at hu
    exact ((hu.mul u.isUnit).mul_right_eq_zero.1 e).trans (DVR.hr_gs_zero _ _ _).symm
  rw [hz] at x₁
  exact ((U.expand k hk).1 _).unique x₁ (expands_zero U.toUnifPre k)

theorem exists_fractionRing_square {R W : Type} [CommRing R] [IsDomain R] [CommRing W] [IsDomain W] (φ : R →+* W) (h : Function.Injective φ) :
    ∃ ψ : FractionRing R →+* FractionRing W, jK W ≫ spMap φ = spMap ψ ≫ jK R := by
  have hi : Function.Injective ((algebraMap W (FractionRing W)).comp φ) := (IsFractionRing.injective W _).comp h
  have h₀ : (algebraMap W (FractionRing W)).comp φ = (IsFractionRing.lift hi).comp (algebraMap R (FractionRing R)) :=
    RingHom.ext fun r => by rw [RingHom.comp_apply (IsFractionRing.lift hi), IsFractionRing.lift_algebraMap]
  refine ⟨IsFractionRing.lift hi, ?_⟩
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, ← h₀]

theorem Trait.exists_generic_map {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {D : DegData R (maximalIdeal R)}
    {C : LabCover D} {W : Type} [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) :
    ∃ p' : pullback T.G.hom (jK W) ⟶ C.A.A.left, pullback.fst T.G.hom (jK W) ≫ T.β = p' ≫ C.α := by
  obtain ⟨ψ, h₀⟩ := exists_fractionRing_square T.φ T.inj
  have hψ : jK W ≫ T.ξ = spMap ψ ≫ C.gp := C.toModif.eq_comp_gp ψ _ (by rw [Category.assoc, T.ξ_π, h₀])
  have w₁ : T.β ≫ C.G.hom = T.G.hom ≫ T.ξ := T.cart.1.w
  have w₂ : pullback.fst T.G.hom (jK W) ≫ T.G.hom = pullback.snd T.G.hom (jK W) ≫ jK W := pullback.condition
  have w₃ : (pullback.fst T.G.hom (jK W) ≫ T.β) ≫ C.G.hom = (pullback.snd T.G.hom (jK W) ≫ spMap ψ) ≫ C.gp := by
    rw [Category.assoc, w₁, reassoc_of% w₂, hψ, Category.assoc]
  have hp : IsPullback C.α C.A.A.hom C.G.hom C.gp := C.α_cart.1
  exact ⟨hp.lift _ _ w₃, (hp.lift_fst _ _ w₃).symm⟩

theorem Trait.exp_unique : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (k : ℕ), 1 ≤ k → ∀ (s : SecK C.P.L.L C.α k) (F : IntFam (maximalIdeal R) D.toPre k), (∃ α j, (F.f α).f j ≠ 0) → ∀ a b b' : W, a ≠ 0 → T.Exp a b s F → T.Exp a b' s F → b = b' := by
  intro R _ _ _ hR D C W _ _ _ T k hk s F hF a b b' _ h₁ h₂
  obtain ⟨α, j, hne⟩ := hF
  obtain ⟨σ₁, ⟨σ₁', f₁, c₁, p₁, e₁⟩, g₁⟩ := h₁
  obtain ⟨σ₂, ⟨σ₂', f₂, c₂, p₂, e₂⟩, g₂⟩ := h₂
  by_contra hb
  apply hne
  obtain ⟨F', hF'⟩ := exists_intFam_pull R hR D W T.φ T.D' T.hD T.inj T.loc k F
  rw [show f₁ = F'.f from funext fun x => (p₁ x).unique (hF' x)] at e₁
  rw [show f₂ = F'.f from funext fun x => (p₂ x).unique (hF' x)] at e₂
  obtain ⟨p', hp'⟩ := T.exists_generic_map
  have h₀ : F'.F = 0 := F'.eq_zero_of_two_scalars T.U hk e₁ e₂ hb fun y J' hJ' => by
    choose J hJ using fun χ : pullback T.G.hom (jK W) ⟶ C.G.left => exists_chart C.P.L.isLB (χ y)
    exact ⟨_, (c₁ _ _ y J J' hJ hJ').symm.trans ((g₁ _ _ p' hp' y J hJ).trans
      ((g₂ _ _ p' hp' y J hJ).symm.trans (c₂ _ _ y J J' hJ hJ')))⟩
  obtain ⟨x, rfl⟩ := T.hD.xe.surjective α
  exact (hF' x).eq_zero T.inj (F'.f_eq_zero h₀ x) j

end GlobalTheory.Mum
