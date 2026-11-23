import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.HeckeFixedPointCMCycleClass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueLinearLiftOfHom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedComplexFibreMarkedLatticeClass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationAtTransportIsometryStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

private theorem lin_eq_of_exp {g : ℕ} {Q : Type*} [Group Q] (e : (Fin g → ℂ) → Q) (A : AddSubgroup (Fin g → ℂ))
    (hA : DiscreteTopology A) (hadd : ∀ z w, e (z + w) = e z * e w) (hker : ∀ z, e z = 1 ↔ z ∈ A)
    (M M' : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (h : ∀ z, e (M z) = e (M' z)) : M = M' := by
  have hd : ∀ z, M z - M' z ∈ A := by
    intro z
    rw [← hker]
    have := hadd (M z - M' z) (M' z)
    rw [sub_add_cancel, h] at this
    exact mul_eq_right.mp this.symm
  refine LinearMap.ext fun z => ?_
  have key : ∀ r : ℝ, (r : ℂ) • (M z - M' z) ∈ A := fun r => by
    have := hd ((r : ℂ) • z)
    rwa [map_smul, map_smul, ← smul_sub] at this
  exact sub_eq_zero.mp (GlobalTheory.HeckeUnif.eq_zero_of_real_smul_mem A hA _ key)

private theorem exists_linearEquiv_of_isog {X : Scheme.{0}} {A B : Over X} [GrpObj A] [IsCommMonObj A] [GrpObj B]
    [IsCommMonObj B] (g : ℕ) (hA : IsAbelianScheme A) (hAs : SmoothOfRelativeDimension g A.hom)
    (hB : IsAbelianScheme B) (hBs : SmoothOfRelativeDimension g B.hom) (y : Sp ℂ ⟶ X)
    (e : (Fin g → ℂ) → (Over.mk y ⟶ A)) (E : (Fin g → ℂ) → (Over.mk y ⟶ B)) (he : IsExp y e) (hE : IsExp y E)
    (Ae Be : AddSubgroup (Fin g → ℂ)) (hAe : DiscreteTopology Ae) (hBe : DiscreteTopology Be)
    (hke : ∀ z, e z = 1 ↔ z ∈ Ae) (hkE : ∀ z, E z = 1 ↔ z ∈ Be)
    (ψ : A ⟶ B) (ψ' : B ⟶ A) [IsMonHom ψ] [IsMonHom ψ'] (d : ℕ) (hd : d ≠ 0)
    (h1 : ψ ≫ ψ' = (𝟙 A) ^ d) (h2 : ψ' ≫ ψ = (𝟙 B) ^ d) :
    ∃ H : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ), (∀ z, E (H z) = e z ≫ ψ) ∧ (∀ z ∈ Ae, H z ∈ Be) ∧
      ∀ z ∈ Be, (d : ℂ) • H.symm z ∈ Ae := by
  have hol : ∀ {C C' : Over X} (u : (Fin g → ℂ) → (Over.mk y ⟶ C)) (f : C ⟶ C'), IsHolTo Set.univ (fun z => (u z).left) →
      IsHolTo Set.univ (fun z => (u z ≫ f).left) := by
    intro C C' u f hu
    have : (fun z => (u z ≫ f).left) = fun z => (u z).left ≫ f.left := funext fun z => by simp only [Over.comp_left]
    rw [this]
    exact ReciprocityTheory.ChartRestriction.G.PullbackSections.isHolTo_comp hu _
  obtain ⟨M₀, hM₀, -⟩ := GlobalTheory.HeckeUnif.existsUnique_linear_lift_of_hom X B g hB hBs y E (fun z => e z ≫ ψ) hE
    (fun z w => by rw [he.1, MonObj.mul_comp]) (hol e ψ he.2.2.1)
  obtain ⟨M₁, hM₁, -⟩ := GlobalTheory.HeckeUnif.existsUnique_linear_lift_of_hom X A g hA hAs y e (fun z => E z ≫ ψ') he
    (fun z w => by rw [hE.1, MonObj.mul_comp]) (hol E ψ' hE.2.2.1)
  have hpe : ∀ z, e ((d : ℂ) • z) = e z ^ d := fun z => by
    rw [Nat.cast_smul_eq_nsmul]
    exact GlobalTheory.UPel.HT.unifCls_exp_nsmul e he.1 d z
  have hpE : ∀ z, E ((d : ℂ) • z) = E z ^ d := fun z => by
    rw [Nat.cast_smul_eq_nsmul]
    exact GlobalTheory.UPel.HT.unifCls_exp_nsmul E hE.1 d z
  have h10 : M₁ ∘ₗ M₀ = (d : ℂ) • LinearMap.id := lin_eq_of_exp e Ae hAe he.1 hke _ _ fun z => by
    show e (M₁ (M₀ z)) = e ((d : ℂ) • z)
    rw [hM₁, hM₀, hpe, Category.assoc, h1, MonObj.comp_pow, Category.comp_id]
  have h01 : M₀ ∘ₗ M₁ = (d : ℂ) • LinearMap.id := lin_eq_of_exp E Be hBe hE.1 hkE _ _ fun z => by
    show E (M₀ (M₁ z)) = E ((d : ℂ) • z)
    rw [hM₀, hM₁, hpE, Category.assoc, h2, MonObj.comp_pow, Category.comp_id]
  have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd
  let H : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ) := LinearEquiv.ofLinear M₀ ((d : ℂ)⁻¹ • M₁)
    (by
      rw [LinearMap.comp_smul, h01, smul_smul, inv_mul_cancel₀ hd', one_smul])
    (by
      rw [LinearMap.smul_comp, h10, smul_smul, inv_mul_cancel₀ hd', one_smul])
  refine ⟨H, fun z => hM₀ z, fun z hz => ?_, fun z hz => ?_⟩
  · rw [← hkE]
    show E (M₀ z) = 1
    rw [hM₀, (hke z).2 hz, MonObj.one_comp]
  · have : (d : ℂ) • H.symm z = M₁ z := by
      show (d : ℂ) • ((d : ℂ)⁻¹ • M₁ z) = M₁ z
      rw [smul_smul, mul_inv_cancel₀ hd', one_smul]
    rw [this, ← hke, hM₁, (hkE z).2 hz, MonObj.one_comp]

theorem UpperTheory.Gal.W2.isogAt_of :
    UpperTheory.Gal.W2.TateWit → UpperTheory.Gal.W2.PerLin → UpperTheory.Gal.W2.IsogAt := by
  intro hTW hPL p _ D G L gb N N' h hLev X X' c hX hL hX' hL' ρ hF D' t P x e hU
  obtain ⟨hN3, hNp, hN'3, hN'p, -, -⟩ := hLev
  have hN : 0 < N := by omega
  have hN' : 0 < N' := by omega
  obtain ⟨hmon, hact, ⟨ψ', d, hmon', -, hψψ', hψ'ψ, hdp⟩, hTate⟩ := c.tr
  haveI := hmon
  haveI := hmon'
  have hd : d ≠ 0 := by
    rintro rfl
    have := (Fact.out : p.Prime).one_lt
    simp only [Nat.coprime_zero_left] at hdp
    omega
  have hys : (x ≫ c.q) ≫ X.s = spMap (RingHom.id ℂ) := by
    rw [Category.assoc, c.ov]
    exact hU.1
  have hpts : ∃ (D'' : PLat D.O D.inv) (t'' : D.La → D''.La) (P₁ : D''.La →+ (Fin D.g → ℂ))
      (E : (Fin D.g → ℂ) → (Over.mk (x ≫ c.q) ⟶ X.univ.A)), D.Cls N D'' t'' ∧
        UnifAt (gfam X.univ hX hL) (RingHom.id ℂ) ρ N D'' t'' P₁ (x ≫ c.q) E := hF.pts (x ≫ c.q) hys
  obtain ⟨D'', t'', P₁, E, hC, hE⟩ := hpts
  have hO : SmoothOfRelativeDimension D.g c.o.A.hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange D.g).of_isPullback c.φ.cart.1 hX
  have hPo' : c.o.P.IsLB := c.o.isLB
  have hPM : X.univ.P.IsLB := X.univ.isLB
  have hLo : (c.o.P.pull (lift (𝟙 c.o.A) (𝟙 c.o.A)).left).IsLB := pull_isLB hPo' _
  have isoB : LBIso (c.o.P.pull (lift (𝟙 c.o.A) (𝟙 c.o.A)).left)
      ((X.univ.P.pull (lift (𝟙 X.univ.A) (𝟙 X.univ.A)).left).pull c.φ.φ) := by
    refine (GlobalTheory.CechPic.cls_eq_iff (pull_isLB hPo' _) (pull_isLB (pull_isLB hPM _) _)).1 ?_
    rw [GlobalTheory.CechPic.cls_pull hPo', (GlobalTheory.CechPic.cls_eq_iff hPo' (pull_isLB hPM _)).2 c.φ.pol, GlobalTheory.CechPic.cls_pull hPM,
      ← GlobalTheory.CechPic.pull_comp, GlobalTheory.DiagAmpleBC.diag_comp X.univ.A c.o.A c.φ.φ c.φ.φ₂ c.φ.sq, GlobalTheory.CechPic.pull_comp,
      GlobalTheory.CechPic.cls_pull (pull_isLB hPM _), GlobalTheory.CechPic.cls_pull hPM]
  obtain ⟨E', hE', hEE'⟩ := (GlobalTheory.unifAt_correspond_of_cartesian D.O D.inv D.g ρ ℂ ℂ (RingHom.id ℂ) (RingHom.id ℂ) D.La
    (gfam X.univ hX hL) (gfam c.o hO hLo) N c.q c.φ.φ c.φ.cart c.φ.act isoB c.φ.eta D'' t'' P₁ x hU.1 hys).2 E hE
  obtain ⟨H, hEH, hHmem, hHmem'⟩ := exists_linearEquiv_of_isog D.g X'.univ.ab hX' c.o.ab hO x e E' hU.2.2.1 hE'.2.2.1
    P.range P₁.range hU.2.1.2.2.1 hE'.2.1.2.2.1 hU.2.2.2.1 hE'.2.2.2.1 c.ψ ψ' d hd hψψ' hψ'ψ
  have hHρ : ∀ (a : D.O) z, H (ρ a *ᵥ z) = ρ a *ᵥ H z := by
    intro a z
    have := lin_eq_of_exp E' P₁.range hE'.2.1.2.2.1 hE'.2.2.1.1 hE'.2.2.2.1
      ((H : (Fin D.g → ℂ) →ₗ[ℂ] (Fin D.g → ℂ)) ∘ₗ Matrix.mulVecLin (ρ a))
      (Matrix.mulVecLin (ρ a) ∘ₗ (H : (Fin D.g → ℂ) →ₗ[ℂ] (Fin D.g → ℂ))) (fun z => by
        show E' (H (ρ a *ᵥ z)) = E' (ρ a *ᵥ H z)
        have e1 : E' (ρ a *ᵥ H z) = E' (H z) ≫ c.o.act.act a := hE'.2.2.2.2.1 a (H z)
        have e2 : e (ρ a *ᵥ z) = e z ≫ X'.univ.act.act a := hU.2.2.2.2.1 a z
        rw [hEH, e1, hEH, e2]
        exact (Category.assoc _ _ _).trans ((congrArg (fun u => e z ≫ u) (hact a)).trans (Category.assoc _ _ _).symm))
    exact LinearMap.congr_fun this z
  have hHρ' : ∀ (a : D.O) z, H.symm (ρ a *ᵥ z) = ρ a *ᵥ H.symm z := by
    intro a z
    apply H.injective
    rw [hHρ, H.apply_symm_apply, H.apply_symm_apply]
  let P'' : D''.La →+ (Fin D.g → ℂ) := (H.symm : (Fin D.g → ℂ) →ₗ[ℂ] (Fin D.g → ℂ)).toAddMonoidHom.comp P₁
  have hP'' : ∀ u, P'' u = H.symm (P₁ u) := fun u => rfl
  have hmat : ∀ z, LinearMap.toMatrix' (H.symm : (Fin D.g → ℂ) →ₗ[ℂ] (Fin D.g → ℂ)) *ᵥ z = H.symm z := fun z =>
    LinearMap.toMatrix'_mulVec _ z
  have hper'' : IsPeriod D'' ρ P'' := hPL D.O D.inv D.g ρ D'' P₁ P''
    (LinearMap.toMatrix' (H.symm : (Fin D.g → ℂ) →ₗ[ℂ] (Fin D.g → ℂ))) hE'.2.1
    (by
      rw [LinearMap.det_toMatrix']
      exact (LinearEquiv.isUnit_det' H.symm).ne_zero)
    (fun a => Matrix.toLin'.injective (LinearMap.ext fun z => by
      rw [Matrix.toLin'_apply, Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hmat, hmat, hHρ']))
    (fun u => (hmat _).symm)
  have hmark : IsMarkedIsom N D'' D'' t'' t'' (LinearEquiv.refl D.O D''.La) :=
    ⟨fun _ _ => rfl, fun a => ⟨0, by simp⟩⟩
  have hE2 : UnifAt (gfam X.univ hX hL) (RingHom.id ℂ) ρ N D'' t'' P'' (x ≫ c.q) (fun z => E (H z)) :=
    GlobalTheory.T.uniformisationAt_transport_isometry D.O D.inv D.g ρ ℂ (RingHom.id ℂ) D.La (gfam X.univ hX hL) N D'' D'' t'' t'' P₁ P'' (x ≫ c.q) E
      (LinearEquiv.refl D.O D''.La) H.symm hN hE hmark (fun _ => rfl) hper''
  have hE3 : UnifAt (gfam c.o hO hLo) (RingHom.id ℂ) ρ N D'' t'' P'' x (fun z => E' (H z)) :=
    GlobalTheory.T.uniformisationAt_transport_isometry D.O D.inv D.g ρ ℂ (RingHom.id ℂ) D.La (gfam c.o hO hLo) N D'' D'' t'' t'' P₁ P'' x E'
      (LinearEquiv.refl D.O D''.La) H.symm hN hE' hmark (fun _ => rfl) hper''
  have hι : ∀ u, ∃ v, P₁ v = H (P u) := by
    intro u
    exact hHmem (P u) ⟨u, rfl⟩
  choose fι hfι using hι
  have hPf : ∀ u, P'' (fι u) = P u := fun u => by
    rw [hP'', hfι, H.symm_apply_apply]
  have hinj'' : Function.Injective P'' := hper''.2.1
  let inc : D'.La →ₗ[D.O] D''.La :=
    { toFun := fι
      map_add' := fun u v => hinj'' (by rw [map_add, hPf, hPf, hPf, map_add])
      map_smul' := fun a u => hinj'' (by rw [RingHom.id_apply, hper''.1, hPf, hPf]; exact hU.2.1.1 a u) }
  have hPinc : ∀ u, P'' (inc u) = P u := hPf
  obtain ⟨I', I'', hI', hI'', hT⟩ := hTate ℂ x (RingHom.id ℂ) hU.1
  obtain ⟨f, nu, hw, hfN, hfe⟩ := hTW p D gb N' X'.X X'.s X'.univ hX' hL' ρ D' t P x e hN' hN'p hU I' hI'
  obtain ⟨f'', nu'', hw'', hfN'', hfe''⟩ := hTW p D gb N X'.X X'.s c.o hO hLo ρ D'' t'' P'' x _ hN hNp hE3 I'' hI''
  refine ⟨D'', t'', P'', fun z => E (H z), inc, d, hC, hE2, hPinc, fun z => ?_, hdp, fun u'' => ?_,
    f, nu, f'', nu'', hw, hw'', hfN, hfN'', fun n hn hnp a b => ?_⟩
  · show (E (H z)).left = (e z).left ≫ c.ψ.left ≫ c.φ.φ
    rw [hEE' (H z), hEH z]
    exact Category.assoc _ _ _
  · obtain ⟨u, hu⟩ := hHmem' (P₁ u'') ⟨u'', rfl⟩
    refine ⟨u, hinj'' ?_⟩
    rw [hPinc, hu, map_nsmul, ← Nat.cast_smul_eq_nsmul ℂ]
    rfl
  · rw [← hT n hn hnp a b]
    have h1 : I'.ev n a ≫ c.ψ = E' (H ((n : ℂ)⁻¹ • P'' (inc (f n a)))) := by
      rw [hfe n hn hnp a, hPinc, hEH]
    rw [h1, hfe'' n hn hnp b]
    exact (GlobalTheory.UPel.HT.unifCls_eq_iff (fun z => E' (H z)) P'' hE3.2.2.1.1 hE3.2.2.2.1 hinj'' hn _ _).symm
