import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TorMatch
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEighthPowerTraitLatticeEquivLocalExtStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSurjectiveLatticeCoordMapEquivariantDvrStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftAdicCompletion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SharpByPull
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EndCharExistsOfIsMonHom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedPointCompletionPositiveResidueChar
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.PsiCoordExistsUniqueUpToUnitLocal
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ModelPointsEqOfSameDegenerationData
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsSemiAbelianOfGenericAbelianOfClosedIsGt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.Poinc.Eq8.TraitOne

theorem factor_stalk (X : Scheme.{0}) (x : X) (V : Type) [CommRing V] [IsLocalRing V] (ξ : Sp V ⟶ X)
    (hx : ξ (IsLocalRing.closedPoint V) ⤳ x) :
    ∃ f : X.presheaf.stalk x →+* V, spMap f ≫ X.fromSpecStalk x = ξ := by
  refine ⟨(Scheme.stalkClosedPointTo ξ).hom.comp (X.presheaf.stalkSpecializes hx).hom, ?_⟩
  have e1 := Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ
  have e2 := Scheme.SpecMap_stalkSpecializes_fromSpecStalk hx
  conv_rhs => rw [← e1, ← e2]
  show Spec.map (CommRingCat.ofHom _) ≫ _ = _
  rw [← Category.assoc, ← Spec.map_comp]
  rfl

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (a : A →+* B) (b : B →+* C) :
    spMap (b.comp a) = spMap b ≫ spMap a := by
  rw [← Spec.map_comp]
  rfl

theorem subset_abLocus {o' Ω : Type} [CommRing o'] [Field Ω] [Algebra o' Ω] {S : ThetaSys o' Ω} {ρ : S.Real}
    {M : RatModel o' Ω} {U₀ : M.Z.Opens} {EE : M.Lat S.J} (FinalForm : ZHOut ρ M U₀ EE) :
    (U₀ : Set M.Z) ⊆ abLocus FinalForm.G := by
  intro z hz
  obtain ⟨z', rfl⟩ : z ∈ Set.range U₀.ι := by rw [Scheme.Opens.range_ι]; exact hz
  rw [abLocus_pullback (G' := (Over.pullback FinalForm.u₀).obj ρ.P.A) abLocusOne FinalForm.semi FinalForm.cart.1]
  intro K _ _ t _
  haveI := ρ.P.isAb.proper
  show IsProper (pullback.snd (pullback.snd ρ.P.A.hom FinalForm.u₀) t)
  infer_instance

theorem main : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] [ArithBase o' Ω] (S : ThetaSys o' Ω) (ρ : S.Real), S.Big → ∀ (M : RatModel o' Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (FinalForm : ZHOut ρ M U₀ EE), S.admitted M U₀ → S.IsEE M U₀ EE → ∀ x : M.Z, IsClosed ({x} : Set M.Z) → ∀ (u : Sp S.R ⟶ F.X) c pr, SharpBy F W ρ.P u c pr → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (j : M.Z.presheaf.stalk x →+* R), GlobalTheory.Mum.Base R → IsCpl j → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (gm : G.left ⟶ FinalForm.G.left), IsGrpPullback G FinalForm.G (spMap j ≫ M.Z.fromSpecStalk x) gm → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G), LBIso U.LG.L (FinalForm.L.L.pull gm) → (∀ y, PsiUnitOn D.toPre y ((spMap j ≫ M.Z.fromSpecStalk x) ⁻¹' abLocus FinalForm.G)) → ∀ m : Fin 8 → Fin 8 → (D.toPre.X →+ D.toPre.X), (∀ a b, ∃ (f : FinalForm.G ⟶ FinalForm.G) (fR : G ⟶ G), MatOn FinalForm pr a b f ∧ IsMonHom fR ∧ fR.left ≫ gm = gm ≫ f.left ∧ EndChar U fR (m a b)) → ∀ (T : Trait F) (ξ : Sp T.V ⟶ M.Z), ThroughU M U₀ FinalForm.u₀ u T ξ → ξ (IsLocalRing.closedPoint T.V) ⤳ x → ∃ (V' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsDiscreteValuationRing V') (h : T.V →+* V') (g' : R →+* V') (ρT : D.toPre.X →+ (Fin 8 → T.D.toPre.X)), Function.Injective h ∧ Irreducible (h T.ϖ) ∧ spMap g' ≫ (spMap j ≫ M.Z.fromSpecStalk x) = spMap h ≫ ξ ∧ Function.Surjective ρT ∧ (∀ y r, PsiCoord D.toPre y r → 0 ≤ qW W T.β (ρT y) ∧ Associated (g' r) (h T.ϖ ^ (qW W T.β (ρT y)).toNat)) ∧ ∀ a b y, MatRel W a b (ρT y) (ρT (m a b y)) := by
  intro g n hg hn hodd F W hW o' Ω _ _ _ hA S ρ hBig M U₀ EE FinalForm hAdm hEE x hx u c pr hS R _ _ _ j hR hj G _ _ gm hgm
    D A U hLB hPsi m hm T ξ hξU hsp
  set ξR : Sp R ⟶ M.Z := spMap j ≫ M.Z.fromSpecStalk x with hξR
  obtain ⟨hft, hpj⟩ := GlobalTheory.UPoinc.ClosedPt.closedPoint_cpl_residueChar o' Ω M x hx
  obtain ⟨-, p, hp, hpm⟩ := hpj R j hj
  obtain ⟨f, hf⟩ := factor_stalk M.Z x T.V ξ hsp
  obtain ⟨V', _, _, _, h, g', hc, hinj, hloc, hcomp, hirr⟩ :=
    GlobalTheory.TraitLift.exists_lift_of_isCpl (M.Z.presheaf.stalk x) R T.V j hj f
  have heq : spMap g' ≫ ξR = spMap h ≫ ξ := by
    rw [hξR, ← hf, ← Category.assoc, ← Category.assoc, ← spMap_comp', ← spMap_comp', hcomp]
  haveI : CharZero V' := (RingHom.charZero_iff hinj).1 inferInstance
  have hBV : GlobalTheory.Mum.Base V' := ⟨⟨inferInstance, inferInstance, inferInstance, hc⟩, inferInstance⟩
  have hle : nonZeroDivisors T.V ≤ (nonZeroDivisors V').comap h :=
    nonZeroDivisors_le_comap_nonZeroDivisors_of_injective h hinj
  let hK : FractionRing T.V →+* FractionRing V' := IsLocalization.map (FractionRing V') h hle
  have hKc : ∀ a, hK (algebraMap T.V _ a) = algebraMap V' _ (h a) := IsLocalization.map_eq hle
  have hjK : spMap hK ≫ jK T.V = jK V' ≫ spMap h := by
    show spMap hK ≫ spMap (algebraMap T.V (FractionRing T.V)) = spMap (algebraMap V' (FractionRing V')) ≫ spMap h
    rw [← spMap_comp', ← spMap_comp']
    congr 1
    ext a
    exact hKc a
  obtain ⟨ξ₀, hξ₀, hξ₀y⟩ := hξU
  set ξ' : Sp V' ⟶ M.Z := spMap g' ≫ ξR with hξ'
  have hξ₀' : (spMap hK ≫ ξ₀) ≫ U₀.ι = jK V' ≫ ξ' := by
    rw [Category.assoc, hξ₀, ← Category.assoc, hjK, Category.assoc, heq]
  have hsub := subset_abLocus FinalForm
  let w' : Sp V' := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum V')
  have hw'U : ξ' w' ∈ (U₀ : Set M.Z) := by
    have e1 : w' = jK V' (IsLocalRing.closedPoint (FractionRing V')) := by
      apply PrimeSpectrum.ext
      show (⊥ : Ideal V') = Ideal.comap (algebraMap V' (FractionRing V')) (IsLocalRing.closedPoint (FractionRing V')).asIdeal
      rw [Ideal.eq_bot_of_prime (IsLocalRing.closedPoint (FractionRing V')).asIdeal, ← RingHom.ker_eq_comap_bot]
      exact ((RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective V' (FractionRing V'))).symm
    rw [e1]
    show (jK V' ≫ ξ') (IsLocalRing.closedPoint (FractionRing V')) ∈ (U₀ : Set M.Z)
    rw [← hξ₀']
    show U₀.ι ((spMap hK ≫ ξ₀) (IsLocalRing.closedPoint (FractionRing V'))) ∈ (U₀ : Set M.Z)
    rw [← Scheme.Opens.range_ι]
    exact ⟨_, rfl⟩
  obtain ⟨D', A', U', hLB', hPsi'⟩ := FinalForm.unif V' inferInstance inferInstance hc ξ' ⟨w', hsub hw'U⟩
  have hG'semi : IsSemiAbelian ((Over.pullback ξ').obj FinalForm.G) := IsSemiAbelian.pullback ξ' FinalForm.G FinalForm.semi
  have hpb' := isGrpPullback_pullback FinalForm.G ξ'
  have h'' : IsGrpPullback ((Over.pullback (spMap g')).obj G) FinalForm.G ξ' (pullback.fst G.hom (spMap g') ≫ gm) :=
    (isGrpPullback_pullback G (spMap g')).comp hgm
  obtain ⟨e, he1, he2⟩ := grpPullback_iso hpb' h''
  haveI := he1
  set β : ((Over.pullback ξ').obj FinalForm.G).left ⟶ G.left := e.hom.left ≫ pullback.fst G.hom (spMap g') with hβdef
  have hβ : IsGrpPullback ((Over.pullback ξ').obj FinalForm.G) G (spMap g') β :=
    ((isGrpPullback_of_iso e).comp (isGrpPullback_pullback G (spMap g'))).congr (Category.id_comp _) rfl
  have hβgm : β ≫ gm = pullback.fst FinalForm.G.hom ξ' := by
    rw [hβdef, Category.assoc, he2]
  clear_value β
  have hGsemi : IsSemiAbelian G := by
    obtain ⟨e2, he21, -⟩ := grpPullback_iso hgm (isGrpPullback_pullback FinalForm.G ξR)
    haveI := he21
    exact GlobalTheory.isSemiAbelian_of_grpIso e2 (IsSemiAbelian.pullback ξR FinalForm.G FinalForm.semi)
  have hLBβ : LBIso U'.LG.L (U.LG.L.pull β) := by
    have h1 : LBIso (U.LG.L.pull β) (FinalForm.L.L.pull (pullback.fst FinalForm.G.hom ξ')) :=
      GlobalTheory.Ex.GenericFibre.lbIso_pull hLB β hβgm.symm
    exact LBIso.trans U'.LG.isLB (pull_isLB FinalForm.L.isLB _) (pull_isLB U.LG.isLB _) hLB' (LBIso.symm h1)
  have hWo : IsOpen (ξR ⁻¹' (U₀ : Set M.Z)) := U₀.isOpen.preimage ξR.continuous
  have hPsiWo : ∀ y, PsiUnitOn D.toPre y (ξR ⁻¹' (U₀ : Set M.Z)) := fun y j' V hV hVW =>
    hPsi y j' V hV (hVW.trans (Set.preimage_mono hsub))
  have hker : (⟨RingHom.ker g', RingHom.ker_isPrime g'⟩ : PrimeSpectrum R) ∈ ξR ⁻¹' (U₀ : Set M.Z) := by
    have e3 : (⟨RingHom.ker g', RingHom.ker_isPrime g'⟩ : PrimeSpectrum R) = spMap g' w' :=
      PrimeSpectrum.ext (RingHom.ker_eq_comap_bot g')
    show ξR _ ∈ (U₀ : Set M.Z)
    rw [e3]
    exact hw'U
  obtain ⟨ρ0, hsurj, hcoord, hequiv⟩ := GlobalTheory.T.exists_surjective_lattice_coordMap_equivariant_dvr R hR G hGsemi D A U V' hBV inferInstance
    ((Over.pullback ξ').obj FinalForm.G) hG'semi D' A' U' g' β p hp hpm _ hWo hPsiWo hker hβ hLBβ
  obtain ⟨c', pr', hS', hmat⟩ := GlobalTheory.Poinc.Eq8.PullAlong.main g n _ _ F W o' Ω S ρ u c pr hS M U₀ EE FinalForm V' hBV
    ((Over.pullback ξ').obj FinalForm.G) hG'semi D' A' U' ξ' (pullback.fst FinalForm.G.hom ξ') hpb' hLB' (spMap hK ≫ ξ₀) hξ₀'
  have hpt : (spMap hK ≫ ξ₀) ≫ FinalForm.u₀ ≫ u = spMap hK ≫ T.y := by
    rw [Category.assoc, hξ₀y]
  have key : ∀ (v : Sp (FractionRing V') ⟶ F.X), v = spMap hK ≫ T.y → ∀ c₁ pr₁, SharpBy F W A' v c₁ pr₁ →
      ∃ e : D'.toPre.X ≃+ (Fin 8 → T.D.toPre.X), (∀ y r, PsiCoord D'.toPre y r → 0 ≤ qW W T.β (e y) ∧
        Associated r (h T.ϖ ^ (qW W T.β (e y)).toNat)) ∧ ∀ (a b : Fin 8) (f : (Over.pullback ξ').obj FinalForm.G ⟶ (Over.pullback ξ').obj FinalForm.G)
        (f₁ : A'.A ⟶ A'.A) (m : D'.toPre.X →+ D'.toPre.X), IsMonHom f → MatEnd pr₁ a b f₁ →
        (Over.pullback (jK V')).map f ≫ U'.gen.hom = U'.gen.hom ≫ f₁ → EndChar U' f m → ∀ y, MatRel W a b (e y) (e (m y)) := by
    rintro v rfl c₁ pr₁ hS₁
    exact GlobalTheory.T.exists_eighthPowerTrait_lattice_equiv_localExt g n _ _ F W hW T V' hBV inferInstance _ hG'semi D' A' U' h hK hloc hKc c₁ pr₁ hS₁
  obtain ⟨e8, hord, hrel⟩ := key _ hpt c' pr' hS'
  refine ⟨V', inferInstance, inferInstance, inferInstance, h, g', e8.toAddMonoidHom.comp ρ0, hinj, hirr _ T.irr, heq,
    e8.surjective.comp hsurj, ?_, ?_⟩
  · intro y r hr
    obtain ⟨⟨r', hr', -⟩, -⟩ := GlobalTheory.PsiCoordLocal.main V' D' inferInstance (ρ0 y)
    obtain ⟨h0, has⟩ := hord (ρ0 y) r' hr'
    exact ⟨h0, (hcoord y r r' hr hr').trans has⟩
  · intro a b y
    obtain ⟨f, fR, hMO, hfR, hcomm, hEC⟩ := hm a b
    haveI : IsMonHom f := hMO.1
    let f' : (Over.pullback ξ').obj FinalForm.G ⟶ (Over.pullback ξ').obj FinalForm.G := (Over.pullback ξ').map f
    have hf'fst : f'.left ≫ pullback.fst FinalForm.G.hom ξ' = pullback.fst FinalForm.G.hom ξ' ≫ f.left := pullback.lift_fst _ _ _
    have hf' : IsMonHom f' := PullGtPf.isMonHom_of_grpPullback hpb' hpb' f f' hf'fst
    have hf'β : f'.left ≫ β = β ≫ fR.left := by
      apply hgm.1.hom_ext
      · calc (f'.left ≫ β) ≫ gm = f'.left ≫ (β ≫ gm) := Category.assoc _ _ _
          _ = pullback.fst FinalForm.G.hom ξ' ≫ f.left := by rw [hβgm, hf'fst]
          _ = (β ≫ gm) ≫ f.left := by rw [hβgm]
          _ = (β ≫ fR.left) ≫ gm := by rw [Category.assoc, Category.assoc, hcomm]
      · calc (f'.left ≫ β) ≫ G.hom = f'.left ≫ (β ≫ G.hom) := Category.assoc _ _ _
          _ = ((Over.pullback ξ').obj FinalForm.G).hom ≫ spMap g' := by rw [hβ.1.w, ← Category.assoc, Over.w f']
          _ = β ≫ G.hom := hβ.1.w.symm
          _ = (β ≫ fR.left) ≫ G.hom := by rw [Category.assoc, Over.w fR]
    obtain ⟨m', hm'⟩ := endChar_exists_of_isMonHom V' hBV _ hG'semi D' A' U' f' hf'
    have hq := hequiv fR f' hfR hf' hf'β (m a b) m' hEC hm' y
    obtain ⟨f₁, hf₁, hf₁c⟩ := hmat a b f f' hMO hf'fst
    have hr := hrel a b f' f₁ m' hf' hf₁ hf₁c hm' (ρ0 y)
    simpa [hq] using hr

end GlobalTheory.Poinc.Eq8.TraitOne
