import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TorMatch
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelTraitCharacterGroupFinrankLeGenusThree
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNoetherianRingStalk
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagOfMatRel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EndCharExistsOfIsMonHom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EssFiniteTypeIntStalk
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMatEnd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BetaPos
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSurjectiveDiagonalLatticeMapTraitStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMinimalPsiCoordinateAssociatedFourierPowerStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.PsiCoordExistsUniqueUpToUnitLocal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeeperThetaValueGaloisConjugateExtension
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsSemiAbelianOfGenericAbelianOfClosedIsGt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniformBaseChange.PullGt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.Poinc.Clocx

theorem exists_pull_endo {S S' : Scheme.{0}} {s : S' ⟶ S} {G : Over S'} {H : Over S} [GrpObj G] [GrpObj H]
    {gm : G.left ⟶ H.left} (hp : IsGrpPullback G H s gm) (f : H ⟶ H) [IsMonHom f] :
    ∃ fR : G ⟶ G, IsMonHom fR ∧ fR.left ≫ gm = gm ≫ f.left := by
  let l : G.left ⟶ G.left := hp.1.lift (gm ≫ f.left) G.hom (by rw [Category.assoc, Over.w f, hp.1.w])
  let fR : G ⟶ G := Over.homMk l (hp.1.lift_snd _ _ _)
  have e : fR.left ≫ gm = gm ≫ f.left := hp.1.lift_fst _ _ _
  exact ⟨fR, PullGtPf.isMonHom_of_grpPullback hp hp f fR e, e⟩

theorem isSemiAbelian_of_isGrpPullback {S S' : Scheme.{0}} {s : S' ⟶ S} {G : Over S'} {H : Over S} [GrpObj G]
    [IsCommMonObj G] [GrpObj H] {gm : G.left ⟶ H.left} (hp : IsGrpPullback G H s gm) (hH : IsSemiAbelian H) :
    IsSemiAbelian G := by
  let e : G ≅ (Over.pullback s).obj H := Over.isoMk hp.1.isoPullback (by simp)
  haveI : IsMonHom e.hom := PullGtPf.isMonHom_of_grpPullback hp (isGrpPullback_pullback H s) (𝟙 H) e.hom
    (by simp [e])
  exact GlobalTheory.isSemiAbelian_of_grpIso e (IsSemiAbelian.pullback s H hH)

theorem le_of_assoc_pow {V' : Type} [CommRing V'] [IsDomain V'] {p x y : V'} (hp : Irreducible p) {a b : ℤ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hx : Associated x (p ^ a.toNat)) (hy : Associated y (p ^ b.toNat)) (hxy : x ∣ y) :
    a ≤ b := by
  have h1 : p ^ a.toNat ∣ p ^ b.toNat := (hx.symm.dvd.trans hxy).trans hy.dvd
  rw [pow_dvd_pow_iff hp.ne_zero hp.not_isUnit] at h1
  omega

theorem congMod_iff {X A B : Type} [AddCommGroup X] (φ : X ≃+ (A → B → ℤ)) (N : ℕ) (y y' : X) :
    CongMod N y y' ↔ ∀ u i, (N : ℤ) ∣ φ y u i - φ y' u i := by
  constructor
  · rintro ⟨w, rfl⟩ u i
    exact ⟨φ w u i, by simp [map_add, map_nsmul]⟩
  · intro h
    choose d hd using h
    refine ⟨φ.symm d, φ.injective ?_⟩
    funext u i
    have := hd u i
    simp only [map_add, map_nsmul, AddEquiv.apply_symm_apply]
    change φ y u i = φ y' u i + N • d u i
    rw [nsmul_eq_mul]
    linarith

theorem mem_maximalIdeal_of_square {X : Scheme.{0}} (x : X) [IsNoetherianRing (X.presheaf.stalk x)] {R : Type}
    [CommRing R] [IsLocalRing R] (j : X.presheaf.stalk x →+* R) (hj : IsCpl j) {V V' : Type} [CommRing V]
    [IsLocalRing V] [CommRing V'] [IsLocalRing V'] (h : V →+* V') [IsLocalHom h] (g' : R →+* V') (ξ : Sp V ⟶ X)
    (hξ : ξ (closedPoint V) = x) (hsq : spMap g' ≫ spMap j ≫ X.fromSpecStalk x = spMap h ≫ ξ) :
    ∀ r ∈ maximalIdeal R, g' r ∈ maximalIdeal V' := by
  obtain ⟨pV, hpV⟩ : ∃ p : Sp V', p = IsLocalRing.closedPoint V' := ⟨_, rfl⟩
  have hpt := congrArg (fun φ : Sp V' ⟶ X => φ pV) hsq
  simp only [Scheme.Hom.comp_apply] at hpt
  have h1 : (spMap h) pV = closedPoint V := hpV ▸ IsLocalRing.comap_closedPoint h
  rw [h1, hξ] at hpt
  have h2 := (X.fromSpecStalk x).isEmbedding.injective (hpt.trans (Scheme.fromSpecStalk_closedPoint (x := x)).symm)

  have h3 : (maximalIdeal (X.presheaf.stalk x)) ≤ (maximalIdeal V').comap (g'.comp j) := by
    have := congrArg PrimeSpectrum.asIdeal h2
    intro a ha
    have e : ((spMap j) ((spMap g') pV)).asIdeal = (maximalIdeal V').comap (g'.comp j) := by subst hpV; rfl
    rw [← e, this]
    exact ha
  obtain ⟨e, he⟩ := hj
  have hm : maximalIdeal R ≤ (maximalIdeal (X.presheaf.stalk x)).map j := by
    intro r hr
    have hr' : e.symm r ∈ maximalIdeal (AdicCompletion (maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x)) := by
      intro hu
      exact hr (by simpa using hu.map e)
    rw [AdicCompletion.maximalIdeal_eq_map] at hr'
    have := Ideal.mem_map_of_mem (e : _ →+* R) hr'
    rw [Ideal.map_map] at this
    have hj' : (e : AdicCompletion (maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x) →+* R).comp
        (algebraMap _ _) = j := RingHom.ext fun a => he a
    rw [hj'] at this
    simpa using this
  intro r hr
  have h4 : (maximalIdeal (X.presheaf.stalk x)).map (g'.comp j) ≤ maximalIdeal V' := Ideal.map_le_iff_le_comap.2 h3
  rw [← Ideal.map_map] at h4
  exact h4 (Ideal.mem_map_of_mem g' (hm hr))

end GlobalTheory.Poinc.Clocx

namespace GlobalTheory.Poinc.Clocx

theorem ordEq_of_assoc {g n : ℕ} {o : Type} [CommRing o] {ζ : o} {F : SFam g n ζ} {o' Ω : Type} [CommRing o']
    [Field Ω] [Algebra o' Ω] (M : RatModel o' Ω) (x : M.Z) (T : Trait F) (ξ : Sp T.V ⟶ M.Z)
    (hs : ξ (IsLocalRing.closedPoint T.V) ⤳ x) {V' : Type} [CommRing V'] [IsDomain V'] (h : T.V →+* V')
    (g' : M.Z.presheaf.stalk x →+* V') (hinj : Function.Injective h) (hirr : Irreducible (h T.ϖ))
    (hsq : spMap g' ≫ M.Z.fromSpecStalk x = spMap h ≫ ξ) (a : M.Z.presheaf.stalk x) (q : ℕ)
    (ha : Associated (g' a) (h T.ϖ ^ q)) : OrdEq M T ξ (M.stalkHom x a) q := by
  set v := RatModel.valLoc ξ x hs (M.stalkEquiv x a) with hv
  have e1 : M.val (jK T.V ≫ ξ) (M.stalkHom x a) = algebraMap T.V (FractionRing T.V) v :=
    RatModel.val_spMap_comp (algebraMap T.V (FractionRing T.V)) ξ hs (M.stalkEquiv x a)
  have e2 : M.val (spMap ((algebraMap V' (FractionRing V')).comp h) ≫ ξ) (M.stalkHom x a) =
      (algebraMap V' (FractionRing V')).comp h v :=
    RatModel.val_spMap_comp _ ξ hs (M.stalkEquiv x a)
  have e3 : spMap ((algebraMap V' (FractionRing V')).comp h) ≫ ξ = jK V' ≫ spMap g' ≫ M.Z.fromSpecStalk x := by
    rw [hsq, ← Category.assoc]
    congr 1
    rw [← Spec.map_comp]
    rfl
  rw [e3, GlobalTheory.Poinc.Sep.GalVal.val_stalkHom] at e2
  have e4 : h v = g' a := (IsFractionRing.injective V' (FractionRing V') e2).symm
  have hv0 : v ≠ 0 := by
    intro h0
    rw [h0, map_zero] at e4
    rw [← e4] at ha
    exact pow_ne_zero q hirr.ne_zero (ha.eq_zero_iff.1 rfl)
  obtain ⟨k, u, hku⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hv0 T.irr
  have hk : k = q := by
    have h5 : Associated (h T.ϖ ^ k) (h T.ϖ ^ q) := by
      have : Associated (h T.ϖ ^ k) (h v) := by
        rw [hku, map_mul, map_pow]
        exact ⟨(Units.map h.toMonoidHom u), by simp [mul_comm]⟩
      exact (this.trans (e4 ▸ ha))
    apply le_antisymm
    · exact (pow_dvd_pow_iff hirr.ne_zero hirr.not_isUnit).1 h5.dvd
    · exact (pow_dvd_pow_iff hirr.ne_zero hirr.not_isUnit).1 h5.symm.dvd
  refine ⟨u, ?_⟩
  rw [e1, hku, hk, mul_comm]

theorem isLocalHom_of_irreducible {V V' : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CommRing V']
    (h : V →+* V') {ϖ : V} (hϖ : Irreducible ϖ) (hh : Irreducible (h ϖ)) : IsLocalHom h := by
  refine ⟨fun a ha => ?_⟩
  by_contra hna
  have hm : a ∈ maximalIdeal V := hna
  rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ, Ideal.mem_span_singleton] at hm
  obtain ⟨b, rfl⟩ := hm
  rw [map_mul] at ha
  exact hh.not_isUnit (isUnit_of_mul_isUnit_left ha)

end GlobalTheory.Poinc.Clocx

open GlobalTheory.Poinc.Clocx GlobalTheory.Poinc.Eq8.DiagMat in

theorem GlobalTheory.Poinc.Clocx.exists_at_closedPoint : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] [ArithBase o' Ω] (S : ThetaSys o' Ω) (ρ : S.Real) (u : Sp S.R ⟶ F.X), S.Big → SharpOver F W ρ.P u → (∀ w, (spMap S.R.val.toRingHom ≫ u) w ∈ genericPoints F.X) → ∀ (_ : NeZero S.N) (M : RatModel o' Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (FinalForm : ZHOut ρ M U₀ EE), S.admitted M U₀ → S.IsEE M U₀ EE → ∀ x : M.Z, IsClosed ({x} : Set M.Z) → ∃ (r : ℕ) (b₀ : LinearMap.BilinForm ℤ (Fin r → ℤ)) (μ : (Fin 8 → Fin r → ZMod S.N) → (Fin 8 → Fin r → ℤ)) (e : (Fin 8 → Fin r → ZMod S.N) → Ω), r ≤ g ∧ (∀ x y, b₀ x y = b₀ y x) ∧ (∀ x, x ≠ 0 → 0 < b₀ x x) ∧ (∀ c u i, ((μ c u i : ℤ) : ZMod S.N) = c u i) ∧ (∀ c (α : Fin 8 → Fin r → ℤ), (∀ u i, ((α u i : ℤ) : ZMod S.N) = c u i) → qW W b₀ (μ c) ≤ qW W b₀ α) ∧ (∀ c, e c ≠ 0 ∧ ∃ (T₀ : AddSubgroup S.Gam) (c' : T₀ →+ ZMod S.N) (κ : S.J × (T₀ → ZMod ((S.r * S.N) ^ 2))) (x₀ : S.Gam), S.IsoFree T₀ ∧ e c = S.FF T₀ c' κ / S.th x₀) ∧ ∀ (T : Trait F) (ξ : Sp T.V ⟶ M.Z), ThroughU M U₀ FinalForm.u₀ u T ξ → ξ (IsLocalRing.closedPoint T.V) ⤳ x → ∃ π : (Fin r → ℤ) →+ T.D.toPre.X, Function.Surjective π ∧ (∀ c (α : Fin 8 → Fin r → ℤ), (∀ u i, ((α u i : ℤ) : ZMod S.N) = c u i) → qW W (T.β.compl₁₂ π.toIntLinearMap π.toIntLinearMap) (μ c) ≤ qW W (T.β.compl₁₂ π.toIntLinearMap π.toIntLinearMap) α) ∧ ∀ c, 0 ≤ qW W (T.β.compl₁₂ π.toIntLinearMap π.toIntLinearMap) (μ c) ∧ OrdEq M T ξ (e c ^ S.N) (qW W (T.β.compl₁₂ π.toIntLinearMap π.toIntLinearMap) (μ c)).toNat := by
  intro g n hg hn hodd F W hW o' Ω _ _ _ _ S ρ u hBig hsharp _ hN M U₀ EE FinalForm hAdm hEE x hx
  have hU : (U₀ : Set M.Z).Nonempty := hAdm.1.ne
  obtain ⟨c, pr, hSB⟩ := (sharpOver_iff F W ρ.P u).1 hsharp
  obtain ⟨R, _, _, _, j, G, _, _, gm, D, A, U, hB, hcpl, hpb, hLB, hpsiU⟩ :=
    GlobalTheory.Poinc.CompletedStalk.exists_completion_unif o' Ω S ρ hBig M U₀ EE FinalForm hAdm hEE x hx
  haveI : CharZero R := hB.2
  have hRi : IsIntegrallyClosed R := hB.1.2.2.1
  have hGsemi : IsSemiAbelian G := isSemiAbelian_of_isGrpPullback hpb FinalForm.semi
  have hm : ∀ a b, ∃ (mab : D.toPre.X →+ D.toPre.X), ∃ (f : FinalForm.G ⟶ FinalForm.G) (fR : G ⟶ G), MatOn FinalForm pr a b f ∧
      IsMonHom fR ∧ fR.left ≫ gm = gm ≫ f.left ∧ EndChar U fR mab := by
    intro a b
    obtain ⟨f, hf⟩ := matOn_exists o' Ω S ρ M U₀ EE FinalForm hU c.A pr hSB.2.1 hSB.2.2.1 a b
    haveI : IsMonHom f := hf.1
    obtain ⟨fR, hfR, hfR'⟩ := exists_pull_endo hpb f
    obtain ⟨mab, hmab⟩ := endChar_exists_of_isMonHom R hB G hGsemi D A U fR hfR
    exact ⟨mab, f, fR, hf, hfR, hfR', hmab⟩
  choose m hm using hm
  have key := fun (T : Trait F) (ξ : Sp T.V ⟶ M.Z) (hT : ThroughU M U₀ FinalForm.u₀ u T ξ)
      (hs : ξ (IsLocalRing.closedPoint T.V) ⤳ x) =>
    GlobalTheory.T.exists_surjective_diagonal_lattice_map_trait g n hg hn hodd F W hW o' Ω S ρ hBig M U₀ EE FinalForm hAdm hEE x hx u c pr hSB R j hB hcpl G gm hpb D A U
      hLB hpsiU m hm T ξ hT hs

  obtain ⟨T₀, ξ₀, hT₀, hξ₀⟩ :=
    GlobalTheory.Poinc.TraitCen.exists_trait_cen g n _ (zetaAway n) F o' Ω M U₀ hU (Sp S.R) FinalForm.u₀ u x hx
  obtain ⟨V₀, _, _, _, h₀, g₀, ρ₀, hh₀, hirr₀, hsq₀, hρ₀s, hord₀, hrel₀⟩ := key T₀ ξ₀ hT₀ (hξ₀ ▸ specializes_rfl)
  haveI := GlobalTheory.Poinc.TraitCen.isNoetherianRing_stalk M x
  haveI := isLocalHom_of_irreducible h₀ T₀.irr hirr₀
  have hloc₀ := mem_maximalIdeal_of_square x j hcpl h₀ g₀ ξ₀ hξ₀ hsq₀
  have hρ₀i : Function.Injective ρ₀ := by
    rw [injective_iff_map_eq_zero]
    intro y hy
    by_contra hy0
    obtain ⟨r, hr, -, hrm, -⟩ := (GlobalTheory.PsiCoordLocal.main R D hRi y).1
    have h1 := (hord₀ y r hr).2
    have h0 : qW W T₀.β (ρ₀ y) = 0 := by rw [hy]; simp [qW]
    rw [h0, Int.toNat_zero, pow_zero, associated_one_iff_isUnit] at h1
    exact (hloc₀ r (hrm hy0)) h1
  let e₀ : D.toPre.X ≃+ (Fin 8 → T₀.D.toPre.X) := AddEquiv.ofBijective ρ₀ ⟨hρ₀i, hρ₀s⟩
  let rk := Module.finrank ℤ T₀.D.toPre.X
  let ι : T₀.D.toPre.X ≃ₗ[ℤ] (Fin rk → ℤ) := (Module.finBasis ℤ T₀.D.toPre.X).equivFun
  let κE : D.toPre.X ≃+ (Fin 8 → Fin rk → ℤ) := e₀.trans (AddEquiv.piCongrRight fun _ => ι.toAddEquiv)
  have hκ : ∀ y u, κE y u = ι (ρ₀ y u) := fun _ _ => rfl
  have hκ' : ∀ y u, ι.symm (κE y u) = ρ₀ y u := fun y u => by rw [hκ]; exact ι.symm_apply_apply _
  let cz : (Fin 8 → Fin rk → ZMod S.N) → (Fin 8 → Fin rk → ℤ) := fun cl u i => ((cl u i).val : ℤ)
  have hcz : ∀ cl u i, ((cz cl u i : ℤ) : ZMod S.N) = cl u i := fun cl u i => by simp [cz]
  have hQ : ∀ cl : Fin 8 → Fin rk → ZMod S.N, ∃ (mu : D.toPre.X) (ee : Ω) (aa : M.Z.presheaf.stalk x),
      CongMod S.N mu (κE.symm (cz cl)) ∧
      (∀ α, CongMod S.N α (κE.symm (cz cl)) → ∀ r s, PsiCoord D.toPre mu r → PsiCoord D.toPre α s → r ∣ s) ∧
      ee ≠ 0 ∧ (∃ (T₁ : AddSubgroup S.Gam) (c' : T₁ →+ ZMod S.N) (κ : S.J × (T₁ → ZMod ((S.r * S.N) ^ 2)))
        (x₀ : S.Gam), S.IsoFree T₁ ∧ ee = S.FF T₁ c' κ / S.th x₀) ∧
      M.stalkHom x aa = ee ^ S.N ∧ ∀ r, PsiCoord D.toPre mu r → Associated (j aa) r := by
    intro cl
    obtain ⟨mu, h1, h2, ee, aa, h3, h4, h5, h6⟩ := GlobalTheory.T.exists_minimal_psiCoordinate_associated_fourierPower o' Ω S ρ hBig M U₀ EE FinalForm hAdm hEE x hx R j hB hcpl G
      gm hpb D A U hLB hpsiU (κE.symm (cz cl))
    exact ⟨mu, ee, aa, h1, h2, h3, h4, h5, h6⟩
  choose mu ee aa hmuC hmuMin hee hFF hEa hassoc using hQ
  have hcong : ∀ cl (y : D.toPre.X), CongMod S.N y (κE.symm (cz cl)) ↔ ∀ u i, ((κE y u i : ℤ) : ZMod S.N) = cl u i := by
    intro cl y
    rw [congMod_iff κE]
    simp only [AddEquiv.apply_symm_apply]
    refine forall_congr' fun u => forall_congr' fun i => ?_
    rw [← hcz cl u i, eq_comm, ZMod.intCast_eq_intCast_iff_dvd_sub]
  let b₀ : LinearMap.BilinForm ℤ (Fin rk → ℤ) := T₀.β.compl₁₂ ι.symm.toLinearMap ι.symm.toLinearMap
  have hqb : ∀ v, qW W b₀ v = qW W T₀.β (fun u => ι.symm (v u)) := fun v => rfl
  have cmp : ∀ (T : Trait F) (V' : Type) [CommRing V'] [IsDomain V'] (h : T.V →+* V') (g' : R →+* V')
      (ρT : D.toPre.X →+ (Fin 8 → T.D.toPre.X)), Irreducible (h T.ϖ) →
      (∀ y r, PsiCoord D.toPre y r → 0 ≤ qW W T.β (ρT y) ∧ Associated (g' r) (h T.ϖ ^ (qW W T.β (ρT y)).toNat)) →
      ∀ cl y, CongMod S.N y (κE.symm (cz cl)) → qW W T.β (ρT (mu cl)) ≤ qW W T.β (ρT y) := by
    intro T V' _ _ h g' ρT hirr hord cl y hy
    obtain ⟨r₁, hr₁, -⟩ := (GlobalTheory.PsiCoordLocal.main R D hRi (mu cl)).1
    obtain ⟨r₂, hr₂, -⟩ := (GlobalTheory.PsiCoordLocal.main R D hRi y).1
    obtain ⟨h1, a1⟩ := hord _ _ hr₁
    obtain ⟨h2, a2⟩ := hord _ _ hr₂
    exact le_of_assoc_pow hirr h1 h2 a1 a2 (map_dvd g' (hmuMin cl y hy r₁ r₂ hr₁ hr₂))
  refine ⟨rk, b₀, fun cl => κE (mu cl), ee, Trait.finrank_le_of_three_le g n F hn T₀, fun _ _ => T₀.symm _ _,
    ?_, ?_, ?_, ?_, ?_⟩
  · intro v hv
    exact Trait.beta_pos g n _ (zetaAway n) F T₀ (ι.symm v) ((LinearEquiv.map_ne_zero_iff ι.symm).2 hv)
  · intro cl u i
    exact (hcong cl (mu cl)).1 (hmuC cl) u i
  · intro cl α hα
    have hy : CongMod S.N (κE.symm α) (κE.symm (cz cl)) := (hcong cl _).2 (by simpa using hα)
    have h1 := cmp T₀ V₀ h₀ g₀ ρ₀ hirr₀ hord₀ cl _ hy
    have e1 : (fun u => ι.symm (κE (mu cl) u)) = ρ₀ (mu cl) := funext (hκ' _)
    have e2 : (fun u => ι.symm (α u)) = ρ₀ (κE.symm α) := by
      funext u; rw [← hκ', AddEquiv.apply_symm_apply]
    rw [hqb, hqb, e1, e2]
    exact h1
  · intro cl
    exact ⟨hee cl, hFF cl⟩
  · intro T ξ hT hs
    obtain ⟨V', _, _, _, h, g', ρT, hinj, hirr, hsq, hsurj, hord, hrel⟩ := key T ξ hT hs
    obtain ⟨πT, hπs, hπ⟩ := exists_diag_of_matRel W hW D.toPre.X T₀.D.toPre.X T.D.toPre.X m e₀ ρT hsurj
      (fun a b y => hrel₀ a b y) hrel
    let π : (Fin rk → ℤ) →+ T.D.toPre.X := πT.comp ι.symm.toLinearMap.toAddMonoidHom
    have hqπ : ∀ v, qW W (T.β.compl₁₂ π.toIntLinearMap π.toIntLinearMap) v =
        qW W T.β (fun u => πT (ι.symm (v u))) := fun v => rfl
    have hρT : ∀ y, (fun u => πT (ι.symm (κE y u))) = ρT y := fun y => funext fun u => by
      rw [hκ', hπ]; rfl
    refine ⟨π, hπs.comp ι.symm.surjective, ?_, ?_⟩
    · intro cl α hα
      have hy : CongMod S.N (κE.symm α) (κE.symm (cz cl)) := (hcong cl _).2 (by simpa using hα)
      have h1 := cmp T V' h g' ρT hirr hord cl _ hy
      have e2 : (fun u => πT (ι.symm (α u))) = ρT (κE.symm α) := by rw [← hρT, AddEquiv.apply_symm_apply]
      rw [hqπ, hqπ, hρT, e2]
      exact h1
    · intro cl
      rw [hqπ, hρT]
      obtain ⟨r₁, hr₁, -⟩ := (GlobalTheory.PsiCoordLocal.main R D hRi (mu cl)).1
      obtain ⟨h1, a1⟩ := hord _ _ hr₁
      refine ⟨h1, ?_⟩
      rw [← hEa cl]
      have hsq' : spMap (g'.comp j) ≫ M.Z.fromSpecStalk x = spMap h ≫ ξ := by
        rw [← hsq, ← Category.assoc]
        congr 1
        rw [← Spec.map_comp]
        rfl
      exact ordEq_of_assoc M x T ξ hs h (g'.comp j) hinj hirr hsq' (aa cl) _ (((hassoc cl r₁ hr₁).map g').trans a1)
