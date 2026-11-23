import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SpecializesGenericImage
import Development.AbelianVarietyTheory.Definitions.Divisors.TorMatch
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EssFiniteTypeIntStalk
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EndCharExistsOfIsMonHom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterGroupFinrankLeMinSignatureUnitaryTrait
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.PsiCoordExistsUniqueUpToUnitLocal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMinimalPsiCoordinateAssociatedFourierPowerStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegerActionSemiAbelianAlongTraitsOpenStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryTraitCentredClosedPointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformiserOrderEqOfAssociatedStalkImageStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BalancedPosDefFiniteProjectiveLatticeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTraitLatticeMapAtClosedPointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompletedLocalRingEndomorphismCharacterActStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocalHomCompletedStalkToDvrOverTraitStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open GlobalTheory
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.UPoinc.ClosedPt

theorem cpl_isIntegrallyClosed : ∀ (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] [ArithBase o' Ω] (M : RatModel o' Ω) (x : M.Z), IsIntegrallyClosed (M.Z.presheaf.stalk x) → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (j : M.Z.presheaf.stalk x →+* R), IsCpl j → IsIntegrallyClosed R := by
  intro o' Ω _ _ _ hA M x hic R _ _ _ j hC
  obtain ⟨e, -⟩ := hC
  have hinjΩ := M.stalkHom_injective x
  haveI : IsDomain (M.Z.presheaf.stalk x) := hinjΩ.isDomain
  haveI : CharZero Ω := hA.char
  haveI : CharZero (M.Z.presheaf.stalk x) := (RingHom.charZero_iff hinjΩ).2 inferInstance
  haveI := hic
  haveI : Algebra.EssFiniteType ℤ (M.Z.presheaf.stalk x) := GlobalTheory.Poinc.CompletedStalk.essFiniteType_int_stalk M x
  obtain ⟨hRd, hRi⟩ := GlobalTheory.AnalyticNormality.completion_isDomain_and_isIntegrallyClosed (M.Z.presheaf.stalk x)
  exact IsIntegrallyClosed.of_equiv e

theorem exists_cong_of_cast {N n : ℕ} (v w : Fin n → ℤ) (h : ∀ i, ((v i : ℤ) : ZMod N) = ((w i : ℤ) : ZMod N)) :
    ∃ k : Fin n → ℤ, v = w + N • k := by
  have : ∀ i, ∃ k : ℤ, v i = w i + N * k := fun i => by
    obtain ⟨k, hk⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub (w i) (v i) N).1 (h i).symm
    exact ⟨k, by linarith⟩
  choose k hk using this
  exact ⟨k, funext fun i => by simp [hk i, nsmul_eq_mul]⟩

theorem be_le_of_dvd {R V' X : Type} [CommRing R] [CommRing V'] [IsDomain V'] [AddCommGroup X] (g' : R →+* V') {w : V'}
    (hw : Irreducible w) (be : LinearMap.BilinForm ℤ X) {a b : X} {r s : R}
    (ha : 0 ≤ be a a ∧ Associated (g' r ^ 2) (w ^ (be a a).toNat))
    (hb : 0 ≤ be b b ∧ Associated (g' s ^ 2) (w ^ (be b b).toNat)) (hrs : r ∣ s) : be a a ≤ be b b := by
  have h0 : g' r ^ 2 ∣ g' s ^ 2 := pow_dvd_pow_of_dvd (map_dvd g' hrs) 2
  have h1 : w ^ (be a a).toNat ∣ w ^ (be b b).toNat :=
    (ha.2.dvd_iff_dvd_left).1 ((hb.2.dvd_iff_dvd_right).1 h0)
  have h2 := (pow_dvd_pow_iff hw.ne_zero hw.not_isUnit).1 h1
  have := Int.toNat_of_nonneg ha.1
  have := Int.toNat_of_nonneg hb.1
  omega

theorem exists_lattice_data : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (X₁ : USetup C) (M : RatModel X₁.o₁ X₁.Ω₁) (U₀ : M.Z.Opens) (EE : M.Lat X₁.S.J) (out : ZHOut X₁.ρ M U₀ EE), X₁.S.admitted M U₀ → X₁.S.IsEE M U₀ EE → ∀ x : M.Z, IsClosed ({x} : Set M.Z) → ∃ (X : Type) (_ : AddCommGroup X) (_ : Module (𝓞 E) X) (_ : Module.Finite (𝓞 E) X) (_ : Module.Projective (𝓞 E) X) (n : ℕ) (eb : X ≃ₗ[ℤ] (Fin n → ℤ)) (b₀ : LinearMap.BilinForm ℤ X) (μ : (Fin n → ZMod X₁.S.N) → X) (e : (Fin n → ZMod X₁.S.N) → X₁.Ω₁), Module.finrank (𝓞 E) X ≤ min Dw.p Dw.q ∧ b₀ ∈ balForms H.bar X ∧ (∀ y, y ≠ 0 → 0 < b₀ y y) ∧ (∀ cl i, ((eb (μ cl) i : ℤ) : ZMod X₁.S.N) = cl i) ∧ (∀ cl (α : X), (∀ i, ((eb α i : ℤ) : ZMod X₁.S.N) = cl i) → b₀ (μ cl) (μ cl) ≤ b₀ α α) ∧ (∀ cl, e cl ≠ 0 ∧ ∃ (T₀ : AddSubgroup X₁.S.Gam) (c' : T₀ →+ ZMod X₁.S.N) (κ : X₁.S.J × (T₀ → ZMod ((X₁.S.r * X₁.S.N) ^ 2))) (x₀ : X₁.S.Gam), X₁.S.IsoFree T₀ ∧ e cl = X₁.S.FF T₀ c' κ / X₁.S.th x₀) ∧ ∀ (T : UTrait Xo c) (ξ : Sp T.V ⟶ M.Z), (∃ ξ₀ : Sp (FractionRing T.V) ⟶ U₀.toScheme, ξ₀ ≫ U₀.ι = jK T.V ≫ ξ ∧ X₁.Lies (ξ₀ ≫ out.u₀) T.y) → ξ (IsLocalRing.closedPoint T.V) ⤳ x → ∃ π : X →ₗ[𝓞 E] T.P.D.toPre.X, Function.Surjective π ∧ (∀ cl (α : X), (∀ i, ((eb α i : ℤ) : ZMod X₁.S.N) = cl i) → T.be (π (μ cl)) (π (μ cl)) ≤ T.be (π α) (π α)) ∧ ∀ cl, UOrdEq M T ξ (e cl ^ (2 * X₁.S.N)) (T.be (π (μ cl)) (π (μ cl))).toNat := by
  intro E _ _ _ H Dw l Xo c C X₁ M U₀ EE out hAdm hEE x hx
  obtain ⟨R, _, _, _, j, G, _, _, gm, D, A, U, hB, hC, hpb, hL, hPsi⟩ :=
    GlobalTheory.Poinc.CompletedStalk.exists_completion_unif X₁.o₁ X₁.Ω₁ X₁.S X₁.ρ X₁.big M U₀ EE out hAdm hEE x hx
  obtain ⟨f, hfm, hfT⟩ := GlobalTheory.T.integerAction_semiAbelian_along_traits_open E H Dw l Xo c C X₁ M U₀ EE out hAdm
  have hR := fun a => GlobalTheory.T.exists_completedLocalRing_endomorphism_character_action X₁.o₁ X₁.Ω₁ X₁.S X₁.ρ M U₀ EE out x R j hB G gm hpb D A U (f a) (hfm a)
  choose fR m hfR using hR
  obtain ⟨T₀, ξ₀, hT₀, hξ₀⟩ := GlobalTheory.T.exists_unitaryTrait_centred_closedPoint E H Dw l Xo c C X₁ M U₀ EE out hAdm x hx
  have tr := GlobalTheory.T.exists_trait_lattice_map_at_closedPoint E H Dw l Xo c C X₁ M U₀ EE out hAdm f hfm hfT x hx R j hB hC G gm hpb D A U hL hPsi m
    (fun a => ⟨fR a, hfR a⟩)
  obtain ⟨V₀, _, _, _, h₀, g₀, ρ₀, -, hirr₀, hsq₀, hsurj₀, hco₀, hlin₀⟩ :=
    tr T₀ ξ₀ hT₀ (by rw [hξ₀])
  haveI : CharZero R := hB.2
  haveI : IsIntegrallyClosed R := cpl_isIntegrallyClosed X₁.o₁ X₁.Ω₁ M x (hAdm.1.normal x).2 R j hC
  have hco : ∀ y, ∃ r, PsiCoord D.toPre y r ∧ (y ≠ 0 → r ∈ maximalIdeal R) := fun y => by
    obtain ⟨r, h1, -, h3, -⟩ := (GlobalTheory.PsiCoordLocal.main R D inferInstance y).1
    exact ⟨r, h1, h3⟩
  obtain ⟨hdvr₀, -, -⟩ := T₀.cdvr
  haveI := hdvr₀
  haveI : IsLocalHom g₀ := GlobalTheory.T.isLocalHom_completedStalk_to_dvr_over_trait X₁.o₁ X₁.Ω₁ M x R j hC T₀.V T₀.ϖ V₀ h₀ g₀ ξ₀ hirr₀ hξ₀ hsq₀
  have hinj : Function.Injective ρ₀ := by
    refine (injective_iff_map_eq_zero ρ₀).2 fun y h0 => by_contra fun hy => ?_
    obtain ⟨r, hr, hrm⟩ := hco y
    obtain ⟨-, has⟩ := hco₀ y r hr
    simp only [h0, map_zero, LinearMap.zero_apply, Int.toNat_zero, pow_zero] at has
    have hu : IsUnit (g₀ r) := (isUnit_pow_iff two_ne_zero).1 (has.isUnit_iff.2 isUnit_one)
    exact (mem_maximalIdeal r |>.1 (hrm hy)) ((isUnit_map_iff g₀ r).1 hu)
  let e₀ : D.toPre.X ≃+ T₀.P.D.toPre.X := AddEquiv.ofBijective ρ₀ ⟨hinj, hsurj₀⟩
  have he₀ : ∀ y, e₀ y = ρ₀ y := fun _ => rfl
  obtain ⟨hbal, hposdef, hfin, hproj, n, ⟨eb⟩⟩ := GlobalTheory.T.balanced_posDef_finite_projective_lattice E H Dw l Xo c T₀
  let ℓ : ZMod X₁.S.N → ℤ := Function.surjInv ZMod.intCast_surjective
  have hℓ : ∀ z, ((ℓ z : ℤ) : ZMod X₁.S.N) = z := Function.surjInv_eq _
  let α₀ : (Fin n → ZMod X₁.S.N) → D.toPre.X := fun cl => e₀.symm (eb.symm (fun i => ℓ (cl i)))
  have hq := fun cl => GlobalTheory.T.exists_minimal_psiCoordinate_associated_fourierPower X₁.o₁ X₁.Ω₁ X₁.S X₁.ρ X₁.big M U₀ EE out hAdm hEE x hx R j hB hC G gm hpb D A U hL
    hPsi (α₀ cl)
  choose mu hmu1 hmu2 e a he hFF hae hja using hq

  have hcong : ∀ cl (α : T₀.P.D.toPre.X), (∀ i, ((eb α i : ℤ) : ZMod X₁.S.N) = cl i) →
      CongMod X₁.S.N (e₀.symm α) (α₀ cl) := by
    intro cl α hα
    obtain ⟨k, hk⟩ := exists_cong_of_cast (N := X₁.S.N) (eb α) (fun i => ℓ (cl i)) (fun i => by rw [hα, hℓ])
    refine ⟨e₀.symm (eb.symm k), e₀.injective (eb.injective ?_)⟩
    simp only [α₀, map_add, map_nsmul, AddEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
    exact hk
  refine ⟨T₀.P.D.toPre.X, inferInstance, inferInstance, hfin, hproj, n, eb, T₀.be, fun cl => ρ₀ (mu cl), e,
    UTrait.finrank_le_min E H Dw l Xo c T₀, hbal, hposdef, ?_, ?_, fun cl => ⟨he cl, hFF cl⟩, ?_⟩
  · intro cl i
    obtain ⟨w, hw⟩ := hmu1 cl
    show ((eb (ρ₀ (mu cl)) i : ℤ) : ZMod X₁.S.N) = cl i
    rw [← he₀, hw, map_add, map_nsmul, AddEquiv.apply_symm_apply, map_add, map_nsmul, LinearEquiv.apply_symm_apply]
    simp [hℓ, nsmul_eq_mul]
  · intro cl α hα
    obtain ⟨r, hr, -⟩ := hco (mu cl)
    obtain ⟨s, hs, -⟩ := hco (e₀.symm α)
    have := be_le_of_dvd g₀ hirr₀ T₀.be (hco₀ _ r hr) (hco₀ _ s hs) (hmu2 cl _ (hcong cl α hα) r s hr hs)
    rwa [← he₀ (e₀.symm α), AddEquiv.apply_symm_apply] at this
  · intro T ξ hT hsp
    obtain ⟨V', _, _, _, h, g', ρT, hh, hirr, hsq, hsurjT, hcoT, hlinT⟩ := tr T ξ hT hsp
    have hsm : ∀ (c' : 𝓞 E) (z : T₀.P.D.toPre.X), ρT (e₀.symm (c' • z)) = c' • ρT (e₀.symm z) := by
      intro c' z
      obtain ⟨a', rfl⟩ := H.bar.surjective c'
      have hz : H.bar a' • z = e₀ (m a' (e₀.symm z)) := by
        rw [he₀, hlin₀, ← he₀, AddEquiv.apply_symm_apply]
      rw [hz, AddEquiv.symm_apply_apply, hlinT]
    let π : T₀.P.D.toPre.X →ₗ[𝓞 E] T.P.D.toPre.X :=
      { toFun := fun z => ρT (e₀.symm z)
        map_add' := fun y z => by simp only [map_add]
        map_smul' := fun c' z => hsm c' z }
    have hπ : ∀ y, π (ρ₀ y) = ρT y := fun y => by
      show ρT (e₀.symm (ρ₀ y)) = ρT y
      rw [← he₀, AddEquiv.symm_apply_apply]
    refine ⟨π, fun z => ?_, ?_, ?_⟩
    · obtain ⟨y, rfl⟩ := hsurjT z
      exact ⟨ρ₀ y, hπ y⟩
    · intro cl α hα
      obtain ⟨r, hr, -⟩ := hco (mu cl)
      obtain ⟨s, hs, -⟩ := hco (e₀.symm α)
      have := be_le_of_dvd g' hirr T.be (hcoT _ r hr) (hcoT _ s hs) (hmu2 cl _ (hcong cl α hα) r s hr hs)
      rwa [hπ, show π α = ρT (e₀.symm α) from rfl]
    · intro cl
      obtain ⟨r, hr, -⟩ := hco (mu cl)
      obtain ⟨-, has⟩ := hcoT (mu cl) r hr
      rw [hπ]
      have hord := GlobalTheory.T.uniformiserOrder_eq_of_associated_stalkImage E H Dw l Xo c X₁.o₁ X₁.Ω₁ M x T ξ hsp R j V' h g' hh hirr hsq (a cl ^ 2) _
        (by rw [map_pow, map_pow]; exact (((hja cl r hr).map g').pow_pow (n := 2)).trans has)
      rwa [map_pow, hae cl, ← pow_mul, mul_comm] at hord

end GlobalTheory.UPoinc.ClosedPt
