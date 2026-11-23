import Mathlib
import Development.AbelianVarietyTheory.Definitions.KeyFormula.IsSquareDeterminantComparison
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.IsPluriharmonicSiegel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.MapsAtLeA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OneEqSpTranslZero
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.IndepOnEmpty
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.BasisPowerSectionsLocalBaseChange
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.PwIsoIsGen
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsKeyPBRing
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsGenSimilitudePull
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsNormalisedIsoPullbackMulByM
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsNormalisingUnitSimilitudeOrigin
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsSectionBoxProductDivGenerator
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsSquareDeterminantComparisonIsAlgClosed
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsPointThetaPullbacksIsUnit
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.EqOfSimilitudeIsoQuotientKernelInvariantStatement
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.BasisBaseChangeRelativeBasisPulledBackSectionsStatement
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.PullbackSectionsBasisAffineBaseChangeOfAffineStatement
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.PullbackSectionsBasisOfAffineOpensStatement
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.PullbackSectionsSpanTwistedOfIndepSpanStatement
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.BoxProductsSpanExternalPowersOfBoxSpanStatement
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.SimilitudeIsoThetaProductBaseChangeStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa

noncomputable section
namespace GlobalTheory.SimilLocal

open GlobalTheory.RelBasis GlobalTheory.SimilDet

theorem det_ne_zero : Out.Laws → ∀ (K : Type) [Field K] [IsAlgClosed K] (x : KeyIn K) (m N : ℕ) (al : Matrix (Fin 4) (Fin 4) ℤ) (b : Fin N → RR x m) (ξ : (Fin 4 → Fin N) → Fin 4 → Pt x) (w : ∀ I, LB.Gen (LB.LinComb x.P.L (K := Fin 4 ⊕ Fin 4) (Sum.elim (fun r => (alMap x al r (ξ I r)).left) (fun c => (Out.powPr x.P.A c).left)) (Sum.elim (fun _ => 1) (fun _ => -(m : ℤ))))) (Q : Matrix (Fin 4 → Fin N) (Fin 4 → Fin N) K), (m : K) ≠ 0 → al.transpose * al = (m : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ) → Function.Injective ξ → (∀ I, (w I).IsGen) → (∀ I, ∀ (Z : Scheme.{0}) (ρ : Z ⟶ (Out.powObj x.P.A 4).left) (z : Z) J, Good x.P.L z J → ∏ r, gs (ρ ≫ (alMap x al r (ξ I r)).left) z (x.P.L.U (J (ρ ≫ (alMap x al r (ξ I r)).left))) (x.th.f (J (ρ ≫ (alMap x al r (ξ I r)).left))) = (val (w I) ρ z J).val * ∑ I' : Fin 4 → Fin N, gs ρ z ⊤ (cst (Out.powObj x.P.A 4).hom ⊤ (Q I I')) * ∏ c, gs (ρ ≫ (Out.powPr x.P.A c).left) z (x.P.L.U (J (ρ ≫ (Out.powPr x.P.A c).left))) ((b (I' c)).f (J (ρ ≫ (Out.powPr x.P.A c).left)))) → Q.det ≠ 0 := by
  intro laws K _ _ x m N al b ξ w Q hm hal hξ hw hE
  classical
  have hL := x.P.isLB
  intro h0
  obtain ⟨c, hc, hcQ⟩ := Matrix.exists_vecMul_eq_zero_iff.2 h0
  obtain ⟨I₀, -⟩ := Function.ne_iff.1 hc
  refine hc ?_
  let S : Over (Sp K) := 𝟙_ _
  let T := Out.powObj x.P.A 4
  haveI : IsIntegral S.left := inferInstanceAs (IsIntegral (Spec (CommRingCat.of K)))
  haveI : Subsingleton S.left := inferInstanceAs (Subsingleton (PrimeSpectrum K))
  let p : S.left := IsLocalRing.closedPoint K
  choose J hJ using fun χ : S.left ⟶ x.P.A.left => exists_chart hL (χ p)
  replace hJ : Good x.P.L p J := hJ
  let ev : Γ(S.left, ⊤) →+* S.left.presheaf.stalk p := (S.left.presheaf.germ ⊤ p trivial).hom
  have hev : ∀ (y : S ⟶ T) a, gs (y.left ≫ T.hom) p ⊤ a = ev a := fun y a => by
    rw [Over.w y]
    exact gs_eq (𝟙 S.left) p ⊤ trivial a
  let κ : K →+* S.left.presheaf.stalk p := ev.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
  choose a ha using fun I v => exists_transl_ratio laws x m al (ξ I₀) (ξ I) (w I₀) (w I) (hw I₀) (hw I) v
  let u : (Fin 4 → Fin N) → (S ⟶ T) → (S.left.presheaf.stalk p)ˣ := fun I y =>
    val (w I₀) y.left p J * (val (w I) y.left p J)⁻¹
  have hu : ∀ I (v : ker x al) (y : S ⟶ T), (u I (v.1 * y)).val = ev (a I v) * (u I y).val := fun I v y => by
    have := ha I v _ y.left p J hJ
    rw [hev, ← Over.comp_left, pt_tr] at this
    rw [← this, ← Units.val_mul, inv_mul_cancel_right]
  let χ : (Fin 4 → Fin N) → ker x al →* S.left.presheaf.stalk p := fun I =>
    { toFun := fun v => ev (a I v)
      map_one' := by
        have := hu I 1 1
        rw [Submonoid.coe_one, _root_.one_mul] at this
        exact (Units.mul_left_inj (u I 1)).1 (this.symm.trans (_root_.one_mul _).symm)
      map_mul' := fun v v' => by
        have := hu I (v * v') 1
        rw [Submonoid.coe_mul, _root_.mul_assoc, hu, hu, ← _root_.mul_assoc] at this
        exact ((Units.mul_left_inj (u I 1)).1 this).symm }
  have hχ : Function.Injective χ := fun I I' h => by
    have e := GlobalTheory.T.eq_of_similitudeIso_quotient_kernel_invariant laws K x m al (ξ I) (ξ I') (w I) (w I') hm hal (hw I) (hw I') (fun v hv Z r z J hJ => by
      have e₁ : a I ⟨v, hv⟩ = a I' ⟨v, hv⟩ := fn_ext (X := S.left) fun y _ => by
        obtain rfl : y = p := Subsingleton.elim _ _
        exact (gs_eq (𝟙 S.left) p ⊤ trivial _).trans ((DFunLike.congr_fun h ⟨v, hv⟩).trans
          (gs_eq (𝟙 S.left) p ⊤ trivial _).symm)
      have e₂ := Units.ext ((ha I ⟨v, hv⟩ Z r z J hJ).trans (e₁ ▸ (ha I' ⟨v, hv⟩ Z r z J hJ).symm))
      have alg : ∀ {U : Type} [CommGroup U] (A B B' C D D' : U),
          A * B⁻¹ * (C * D⁻¹)⁻¹ = A * B'⁻¹ * (C * D'⁻¹)⁻¹ → B * D' = B' * D := fun A B B' C D D' h => by
        rw [mul_inv, mul_inv, inv_inv, inv_inv, _root_.mul_assoc, _root_.mul_assoc, mul_right_inj, mul_left_comm,
          mul_left_comm B'⁻¹, mul_right_inj, inv_mul_eq_iff_eq_mul] at h
        rw [h, mul_left_comm B', mul_inv_cancel_left]
      exact alg _ _ _ _ _ _ e₂)
    exact hξ e
  let θ : (Fin 4 → Fin N) → (S ⟶ T) → S.left.presheaf.stalk p := fun I y =>
    ∏ r, gs (y.left ≫ (alMap x al r (ξ I r)).left) p _ (x.th.f (J (y.left ≫ (alMap x al r (ξ I r)).left)))
  refine eq_zero_of_eigen κ χ hχ (fun v y => v.1 * y) (fun I y => θ I y * (u I y).val) (fun I v y => ?_)
    (fun I => ?_) c (fun y => ?_)
  · have e : θ I (v.1 * y) = θ I y := Finset.prod_congr rfl fun r _ =>
      congrArg (fun ψ : S.left ⟶ x.P.A.left => gs ψ p _ (x.th.f (J ψ))) (by
        rw [← Over.comp_left, ← Over.comp_left, ← pt_tr, Category.assoc, tr_alMap])
    simp only [hu, e]
    exact mul_left_comm _ _ _
  · obtain ⟨y, hy⟩ := GlobalTheory.SimilNonvan.exists_pt_isUnit laws K x m al (ξ I) hm hal
    exact ⟨y, mul_ne_zero (Finset.prod_ne_zero_iff.2 fun r _ => (hy p J hJ r).ne_zero) (Units.ne_zero _)⟩
  · have e : ∀ I, θ I y * (u I y).val = (val (w I₀) y.left p J).val * ∑ I', κ (Q I I') *
        ∏ c, gs (y.left ≫ (Out.powPr x.P.A c).left) p _ ((b (I' c)).f (J (y.left ≫ (Out.powPr x.P.A c).left))) :=
      fun I => by
      have e₁ : θ I y = _ := hE I _ y.left p J hJ
      rw [e₁, mul_right_comm, ← Units.val_mul, mul_comm (val (w I) y.left p J),
        inv_mul_cancel_right]
      refine congrArg _ (Finset.sum_congr rfl fun I' _ => ?_)
      rw [gs_cst, hev]
      rfl
    simp only [e, mul_left_comm _ (val (w I₀) y.left p J).val, ← Finset.mul_sum]
    refine mul_eq_zero_of_right _ ?_
    simp only [Finset.mul_sum, ← _root_.mul_assoc, ← map_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun I' _ => ?_
    rw [← Finset.sum_mul, ← map_sum, show ∑ I, c I * Q I I' = 0 from congrFun hcQ I', map_zero, zero_mul]

theorem exists_coords_pow (laws : Out.Laws) (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (x : KeyIn R)
    (m : ℕ) (hm : 1 ≤ m) (b : Fin (m ^ x.P.g) → RR x m) (hb : IsBasis x b) (n : ℕ)
    (s : LB.Sec (LB.LinComb x.P.L (K := Fin n) (fun c => (Out.powPr x.P.A c).left) (fun _ => (m : ℤ)))) :
    ∃ q : (Fin n → Fin (m ^ x.P.g)) → R, ∀ (Z : Scheme.{0}) (r : Z ⟶ (Out.powObj x.P.A n).left) (z : Z) J,
      Good x.P.L z J → sval s r z J = ∑ I, gs r z ⊤ (cst (Out.powObj x.P.A n).hom ⊤ (q I)) *
        ∏ c, gs (r ≫ (Out.powPr x.P.A c).left) z (x.P.L.U (J (r ≫ (Out.powPr x.P.A c).left)))
          ((b (I c)).f (J (r ≫ (Out.powPr x.P.A c).left))) := by
  refine GlobalTheory.T.boxProducts_span_external_powers_of_boxSpan R x.P.A x.P.L m _ b x.P.isLB (fun T => ?_) n s
  refine GlobalTheory.T.pullbackSectionsSpanTwisted_of_indep_span _ _ _ _ _ _ b _ _ x.P.isLB (GlobalTheory.T.pullbackSections_basis_of_affine_opens _ _ _ _ _ _ b _ _ ?_)
  refine GlobalTheory.T.pullbackSections_basis_affine_baseChange_of_affine R _ x.P.A.hom x.P.L _ _ b (fun R' _ f => ?_) _ _ T.hom _ _
    (IsPullback.of_hasPullback x.P.A.hom T.hom)
  obtain ⟨x', hx'⟩ := GlobalTheory.KeyPow.keyIn_baseChange laws.polBaseChange R R' x f
  obtain ⟨h₁, h₂⟩ := GlobalTheory.KeyVia.main R R' x x' f
  obtain ⟨φ, w, hv⟩ := h₁.1 hx'
  choose b' hb' using fun k => ((h₂ φ w hv).1 m (b k)).exists
  have hP : IsPullback φ x'.P.A.hom x.P.A.hom (spMap f) := by
    obtain ⟨he, hg, F, ⟨hP, -⟩, -⟩ := hv
    exact hP
  exact ⟨_, x'.P.A.hom, φ, hP, GlobalTheory.T.basisBaseChange_relativeBasis_pulledBackSections R R' x x' f φ w m _ b b' hv hb'
    ((GlobalTheory.KeyBasis.main laws R x m hm).2 b hb R' f x' φ w b' hv hb')⟩

theorem exists_l2Val : Out.Laws → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsPrincipalIdealRing R] (x : KeyIn R) (m : ℕ) (al : Matrix (Fin 4) (Fin 4) ℤ) (b : Fin (m ^ x.P.g) → RR x m) (ξ : (Fin 4 → Fin (m ^ x.P.g)) → Fin 4 → Pt x), IsUnit (m : R) → al.transpose * al = (m : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ) → IsBasis x b → (∀ I I', I ≠ I' → ∀ p : Sp R, ∃ r, (ξ I r).left p ≠ (ξ I' r).left p) → (∀ I c, (List.ofFn fun r : Fin 4 => ξ I r ^ al r c).prod = 1) → ∃ lam, IsSquareDeterminantComparison x m al b lam := by
  intro laws R _ _ _ _ x m al b ξ hm hal hb hξ hk
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact not_isUnit_zero (M₀ := R) (by simpa using hm)
  obtain ⟨mu, hmu, hmu'⟩ := GlobalTheory.KeyKa.exists_normalised_mulPull laws R x m
  choose w hw using fun I => GlobalTheory.SimilPull.exists_gen_similitude_pull laws R x m al (ξ I) hal (hk I)
  choose rho hrho using fun I => GlobalTheory.SimilUnit.exists_normalising_unit R x m al (ξ I) mu (w I) hm0 hal (hk I) hmu (hw I)
  choose s hs using fun I => GlobalTheory.KeyQuot.exists_sec_quot _ _ x.P.L x.P.isLB _ _ _ _ (m : ℤ) x.th (w I) (hw I)
  choose Q hQ using fun I => exists_coords_pow laws R x m (Nat.one_le_iff_ne_zero.2 hm0) b hb 4 (s I)
  have hZ : ∀ I, ∀ (Z : Scheme.{0}) (ρ : Z ⟶ (Out.powObj x.P.A 4).left) (z : Z) J, Good x.P.L z J → ∏ r, gs (ρ ≫ (alMap x al r (ξ I r)).left) z (x.P.L.U (J (ρ ≫ (alMap x al r (ξ I r)).left))) (x.th.f (J (ρ ≫ (alMap x al r (ξ I r)).left))) = (val (w I) ρ z J).val * ∑ I' : Fin 4 → Fin (m ^ x.P.g), gs ρ z ⊤ (cst (Out.powObj x.P.A 4).hom ⊤ (Q I I')) * ∏ c, gs (ρ ≫ (Out.powPr x.P.A c).left) z (x.P.L.U (J (ρ ≫ (Out.powPr x.P.A c).left))) ((b (I' c)).f (J (ρ ≫ (Out.powPr x.P.A c).left))) := by
    intro I Z ρ z J hJ
    rw [← hQ I Z ρ z J hJ]
    exact hs I Z ρ z J hJ
  have hE : ∀ I, ∀ (y : (Out.powObj x.P.A 4).left) J, Good x.P.L y J → ∏ r, gs (alMap x al r (ξ I r)).left y _ (x.th.f (J (alMap x al r (ξ I r)).left)) = (val (w I) (𝟙 _) y J).val * ∑ I' : Fin 4 → Fin (m ^ x.P.g), gs (𝟙 _) y ⊤ (cst (Out.powObj x.P.A 4).hom ⊤ (Q I I')) * ∏ c, gs (Out.powPr x.P.A c).left y (x.P.L.U (J (Out.powPr x.P.A c).left)) ((b (I' c)).f (J (Out.powPr x.P.A c).left)) := by
    intro I y J hJ
    have e₁ := hZ I _ (𝟙 _) y J hJ
    have c₁ : ∀ ψ : (Out.powObj x.P.A 4).left ⟶ x.P.A.left,
        gs (𝟙 _ ≫ ψ) y (x.P.L.U (J (𝟙 _ ≫ ψ))) (x.th.f (J (𝟙 _ ≫ ψ))) = gs ψ y (x.P.L.U (J ψ)) (x.th.f (J ψ)) :=
      fun ψ => by rw [Category.id_comp]
    have c₂ : ∀ (ψ : (Out.powObj x.P.A 4).left ⟶ x.P.A.left) k,
        gs (𝟙 _ ≫ ψ) y (x.P.L.U (J (𝟙 _ ≫ ψ))) ((b k).f (J (𝟙 _ ≫ ψ))) = gs ψ y (x.P.L.U (J ψ)) ((b k).f (J ψ)) :=
      fun ψ k => by rw [Category.id_comp]
    simpa only [c₁, c₂] using e₁
  have hdet : IsUnit (Matrix.det (Matrix.of Q)) := by
    let k := AlgebraicClosure (IsLocalRing.ResidueField R)
    let f : R →+* k := (algebraMap (IsLocalRing.ResidueField R) k).comp (IsLocalRing.residue R)
    obtain ⟨x', hx'⟩ := GlobalTheory.KeyPow.keyIn_baseChange laws.polBaseChange R k x f
    obtain ⟨h₁, h₂⟩ := GlobalTheory.KeyVia.main R k x x' f
    obtain ⟨φ, u, hv⟩ := h₁.1 hx'
    choose b' hb' using fun j => ((h₂ φ u hv).1 m (b j)).exists
    choose ξ' hξ' using fun I r => ((h₂ φ u hv).2.1 (ξ I r)).exists
    choose w' hw' hE' using fun I =>
      GlobalTheory.T.similitudeIso_thetaProduct_baseChange R k x x' f φ u m _ al b b' (ξ I) (ξ' I) (w I) (Q I) hv hb' (hξ' I) (hw I) (hZ I)
    have hinj : Function.Injective ξ' := fun I I' e => by
      by_contra hne
      obtain ⟨r, hr⟩ := hξ I I' hne (spMap f (IsLocalRing.closedPoint k))
      have e' : spMap f ≫ (ξ I r).left = spMap f ≫ (ξ I' r).left := by rw [← hξ' I r, ← hξ' I' r, e]
      exact hr (congrArg (fun q => q (IsLocalRing.closedPoint k)) e')
    have hne := det_ne_zero laws k x' m _ al b' ξ' w' ((Matrix.of Q).map f)
      (by simpa only [map_natCast] using (hm.map f).ne_zero) hal hinj hw' hE'
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det] at hne
    by_contra hu
    refine hne ?_
    have : IsLocalRing.residue R (Matrix.det (Matrix.of Q)) = 0 := (IsLocalRing.residue_eq_zero_iff _).2 hu
    show algebraMap (IsLocalRing.ResidueField R) k (IsLocalRing.residue R _) = 0
    rw [this, map_zero]
  refine ⟨hdet.unit ^ (2 * m ^ 2) * ∏ I, rho I ^ 2, ξ, mu, w, Matrix.of Q, rho, hξ, hk, hmu, hw,
    fun p J hJ => ⟨hmu' p J hJ, fun I => hrho I p J hJ⟩, hE, ?_⟩
  simp only [Units.val_mul, Units.val_pow_eq_pow_val, IsUnit.unit_spec, Units.coe_prod]

end GlobalTheory.SimilLocal
