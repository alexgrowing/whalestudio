import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.IsCharZeroPt
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.CondConj
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.NormEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.NormUniq
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.MapTor

open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia

private theorem map_tor {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (t : Aˣ) :
    GeneralLinearGroup.map f (tor A t) = tor B (Units.map f.toMonoidHom t) :=
  _root_.UpperTheory.Reformulated.B.H71.map_tor f t

private theorem map_conjBy {A B D : Type} [CommRing A] [CommRing B] [Group D] (f : A →+* B) (h : GL (Fin 3) A)
    (r : D →* GG 3 A) :
    (GG.map f).comp (conjBy h r) = conjBy (GeneralLinearGroup.map f h) ((GG.map f).comp r) := by
  have e : GG.map f (GG.ofGL h) = GG.ofGL (GeneralLinearGroup.map f h) := by
    unfold GG.map
    rw [SemidirectProduct.map_inl]
  refine MonoidHom.ext fun g => ?_
  simp only [conjBy, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_inv, e]

private theorem conj_conj {A D : Type} [CommRing A] [Group D] (h h' : GL (Fin 3) A) (r : D →* GG 3 A) :
    conjBy (h * h') r = conjBy h (conjBy h' r) := by
  ext1 g
  simp only [conjBy, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul,
    _root_.mul_inv_rev, mul_assoc, MulAut.mul_apply]

private theorem conj_one {A D : Type} [CommRing A] [Group D] (r : D →* GG 3 A) : conjBy 1 r = r := by
  ext1 g
  simp [conjBy]

private theorem conj_mat {A D : Type} [CommRing A] [Group D] (h : GL (Fin 3) A) (r : D →* GG 3 A) (g : D) :
    (conjBy h r g).mat = (h : Matrix _ _ A) * (r g).mat *
      ((sgnAct 3 A (r g).right h⁻¹ : GL (Fin 3) A) : Matrix _ _ A) := by
  have : (conjBy h r g).left = h * (r g).left * sgnAct 3 A (r g).right h⁻¹ := by
    simp [conjBy, SemidirectProduct.mul_left, SemidirectProduct.inv_left]
  simp only [GG.mat, this, Units.val_mul]

private theorem setup {O : Type} [CommRing O] [IsLocalRing O] {G Γ ι : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [Group Γ] [TopologicalSpace Γ] (F : Frame O G Γ ι) (hF : F.Ok) (g₁ : Γ)
    (hg : F.Marked g₁) {R : Type} [CommRing R] [Algebra O R] [IsLocalRing R] (r : Γ →* GG 3 R)
    (hr : Red F.η F.Ψ r) :
    ∃ Ψ : Γ →* (ResidueField R)ˣ, IsUnit (2 : R) ∧ Marks F.η Ψ F.c g₁ ∧
      (GG.map (residue R)).comp r = r0 F.η Ψ := by
  refine ⟨(Units.map ((residue R).comp (algebraMap O R)).toMonoidHom).comp F.Ψ, ?_,
    ⟨hF.csq, hF.ηc, by simp [hF.Ψc], hg.1, ?_⟩, ?_⟩
  · simpa [map_ofNat] using hF.two.map (algebraMap O R)
  · simpa using hg.2.map ((residue R).comp (algebraMap O R))
  · refine MonoidHom.ext fun g => SemidirectProduct.ext (Units.ext ?_) (hr.mult g)
    rw [unitaryThreeReflection_left, MonoidHom.comp_apply, MonoidHom.comp_apply, ← map_tor]
    ext a b
    exact Ideal.Quotient.eq.2 (hr.red g a b)

theorem UpperTheory.lift_along_surjection_graded :
    ∀ {O : Type} [CommRing O] [IsLocalRing O] {G Γ ι : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group Γ] [TopologicalSpace Γ] (F : Frame O G Γ ι), F.Ok → ∀ g₁, F.Marked g₁ → ∀ {R R' : Type} [CommRing R] [Algebra O R] [IsCO O R] [CommRing R'] [Algebra O R'] [IsCO O R'] (q : R →ₐ[O] R'), Function.Surjective q → ∀ (r : Γ →* GG 3 R) (r' : Γ →* GG 3 R'), F.Cond r → IsLocallyConstant (mats r) → push q r = r' → F.CondN g₁ r' →
     ∃ r₂ : Γ →* GG 3 R, F.IsPt g₁ r₂ ∧ push q r₂ = r' := by
  intro O _ _ G Γ ι _ _ _ _ _ F hF g₁ hg R R' _ _ _ _ _ _ q hq r r' hr hlc hp hr'
  haveI : IsAdicComplete (maximalIdeal R) R := IsCO.complete (O := O)
  have hm : ∀ x : R, q x ∈ maximalIdeal R' ↔ x ∈ maximalIdeal R := fun x => by
    rw [← res_eq_zero_iff O, res_map, res_eq_zero_iff]
  have hent : ∀ (h : GL (Fin 3) R), InHat (GeneralLinearGroup.map (q : R →+* R') h) ↔ InHat h := fun h => by
    refine forall_congr' fun a => forall_congr' fun b => ?_
    rw [← hm]
    refine iff_of_eq (congrArg (· ∈ maximalIdeal R') ?_)
    by_cases hab : a = b <;> simp [Matrix.one_apply, hab]
  obtain ⟨Ψ, h2, hM, hred⟩ := setup F hF g₁ hg r hr.toRed
  obtain ⟨Ψ', h2', hM', hred'⟩ := setup F hF g₁ hg r' hr'.toRed
  obtain ⟨h, hh, hN⟩ := exists_normalised F.η Ψ F.c g₁ r h2 hM hred
  have hpush : ∀ H : GL (Fin 3) R, push q (conjBy H r) =
      conjBy (GeneralLinearGroup.map (q : R →+* R') H) r' := fun H => by
    rw [← hp]; exact map_conjBy _ _ _
  have hN' : Normalised F.c g₁ (conjBy (GeneralLinearGroup.map (q : R →+* R') h) r') := by
    rw [← hpush]
    refine ⟨?_, ?_, ?_⟩
    · rw [MonoidHom.comp_apply, GG.map_mat, hN.atc, Matrix.map_one _ (map_zero _) (map_one _)]
    · have := congrArg q hN.z12
      simpa [zmat] using this
    · have := congrArg q hN.z21
      simpa [zmat] using this
  obtain ⟨t', -, ht'⟩ := normalised_unique F.η Ψ' F.c g₁ r' _ h2' hM' hred' ((hent h).2 hh) hr'.norm hN'
  obtain ⟨t₀, ht₀⟩ := hq t'
  obtain ⟨t, rfl⟩ : IsUnit t₀ := by
    by_contra hn
    have := (hm t₀).2 hn
    rw [ht₀] at this
    exact this t'.isUnit
  have ht : Units.map (q : R →+* R').toMonoidHom t = t' := Units.ext ht₀
  have hH : GeneralLinearGroup.map (q : R →+* R') (tor R t⁻¹ * h) = 1 := by
    rw [map_mul, ht', map_tor, map_inv, ht, map_inv, inv_mul_cancel]
  have hHhat : InHat (tor R t⁻¹ * h) := by
    rw [← hent, hH]
    intro a b
    simp
  refine ⟨conjBy (tor R t⁻¹ * h) r, ⟨⟨(cond_conj F _ hHhat).2 r hr, ?_⟩, fun n => ?_⟩, ?_⟩
  · rw [conj_conj]
    exact (conjBy_tor _ _).2.2.1 _ _ hN
  · generalize tor R t⁻¹ * h = H
    have := (hlc.prodMk hF.η_cont).comp fun p : Matrix (Fin 3) (Fin 3) R × ℤˣ =>
      ((H : Matrix _ _ R) * p.1 * ((sgnAct 3 R p.2 H⁻¹ : GL (Fin 3) R) : Matrix _ _ R)).map
        (Ideal.Quotient.mk (maximalIdeal R ^ n))
    convert this using 1
    funext g
    rw [conj_mat, hr.mult g]
    rfl
  · rw [hpush, hH, conj_one]
