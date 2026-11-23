import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SymTupOne
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.MinSt2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvdOfDvdInAllCompleteDVRNormalNoetherianStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCdvrDominating
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NzEverywhere
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaConstantsPrimitivePrincipallyPolarisedTraitStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSymmetricFunctionsDegreeFactorialPrimitiveUStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaConstantListAlgClosedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipallyPolarisedFibreIffOfGrpPullbackStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaLevelAbelianSchemeGlueAffineCover
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UMin.IntTheta

section Pull
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {a : ℤ}

theorem sec_ext' {X : Scheme.{0}} {M : LB X} {s s' : LB.Sec M} (h : ∀ j, s.f j = s'.f j) : s = s' := by
  obtain ⟨f₁, p₁⟩ := s
  obtain ⟨f₂, p₂⟩ := s'
  obtain rfl : f₁ = f₂ := funext h
  rfl

theorem gs_pullS' {T T' : Over S} (h : T' ⟶ T) (s : LB.Sec (LPow A L a T)) {Z : Scheme.{0}}
    (r : Z ⟶ (T' ⊗ A).left) (z : Z) (j : Fin 1 → L.ι) (hz : r z ∈ (LPow A L a T').U j) :
    gs r z ((LPow A L a T').U j) ((VVRank.pullS A a h s).f j) =
      gs (r ≫ (h ▷ A).left) z ((LPow A L a T).U j) (s.f j) :=
  (gs_res r z (chart_le_res A L (h ▷ A) (whiskerRight_snd _ _) a j) hz _).trans
    (gs_pull r (h ▷ A).left z _ (chart_le_res A L (h ▷ A) (whiskerRight_snd _ _) a j hz) _)

theorem pullS_comp' {T T' T'' : Over S} (h' : T'' ⟶ T') (h : T' ⟶ T) (s : LB.Sec (LPow A L a T)) :
    VVRank.pullS A a h' (VVRank.pullS A a h s) = VVRank.pullS A a (h' ≫ h) s :=
  sec_ext' fun j => fn_ext fun y hy => by
    refine (gs_pullS' h' _ _ y j hy).trans ((gs_pullS' h _ _ y j
      (chart_le_res A L (h' ▷ A) (whiskerRight_snd _ _) a j hy)).trans (Eq.trans ?_ (gs_pullS' _ _ _ y j hy).symm))
    rw [comp_whiskerRight, Over.comp_left]
    rfl

theorem pullS_heq {T : Over S} {Y : Scheme.{0}} {y₁ y₂ : Y ⟶ S} (e : y₁ = y₂) (h₁ : Over.mk y₁ ⟶ T)
    (h₂ : Over.mk y₂ ⟶ T) (he : h₁.left = h₂.left) (s : LB.Sec (LPow A L a T)) :
    HEq (VVRank.pullS A a h₁ s) (VVRank.pullS A a h₂ s) := by
  subst e
  obtain rfl : h₁ = h₂ := Over.OverMorphism.ext he
  rfl

end Pull

section Sec
variable {S : Scheme.{0}} (G : Over S) [GrpObj G] (L : LB G.left)

theorem pull_pull {R K K' : Type} [CommRing R] [CommRing K] [CommRing K'] {x : Sp R ⟶ S} (θ : SecAt G L x)
    (i : R →+* K) (i' : K →+* K') :
    HEq (SecAt.pull G L (SecAt.pull G L θ i) i') (SecAt.pull G L θ (i'.comp i)) := by
  unfold SecAt.pull
  rw [pullS_comp']
  refine pullS_heq ?_ _ _ ?_ θ
  · rw [spMap_comp, Category.assoc]
  · simp only [Over.comp_left, Over.homMk_left]
    exact (spMap_comp i i').symm

theorem pull_heq_of_eq {R K : Type} [CommRing R] [CommRing K] {x : Sp R ⟶ S} (θ : SecAt G L x)
    {i₁ i₂ : R →+* K} (h : i₁ = i₂) : HEq (SecAt.pull G L θ i₁) (SecAt.pull G L θ i₂) := by
  subst h; rfl

variable {G L} in
theorem thList_of_heq (ρ : LB.Gen (L.pull (eSec G))) (m : ℕ) {K : Type} [Field K] {x₁ x₂ : Sp K ⟶ S} (e : x₁ = x₂)
    {θ₁ : SecAt G L x₁} {θ₂ : SecAt G L x₂} (h : HEq θ₁ θ₂) {N : ℕ} {pt : Fin N → (Over.mk x₁ ⟶ G)} {c : Fin N → K}
    (H : ThList G L ρ m x₁ θ₁ pt c) : ∃ pt' : Fin N → (Over.mk x₂ ⟶ G), ThList G L ρ m x₂ θ₂ pt' c := by
  subst e
  obtain rfl := eq_of_heq h
  exact ⟨pt, H⟩

end Sec

end GlobalTheory.UMin.IntTheta

namespace GlobalTheory.UMin.IntTheta

theorem at_cdvr (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S : Scheme.{0}) (t : SAB H S)
    (g m N : ℕ) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (χ : Sp R ⟶ S) (σ : SecAt t.G t.PP.L χ)
    (e : Fin N → FractionRing R) (hm : Odd m) (hm3 : 3 ≤ m) (hmu : IsUnit (m : R)) (hN : N = m ^ (4 * g))
    (hP : PolFib t.G t.PP.L g (spMap (algebraMap R (FractionRing R)) ≫ χ)) (hNZ : NZ t.G t.PP.L χ σ)
    (hS : SymAt t.G t.PP.L t.PP.rig m (spMap (algebraMap R (FractionRing R)) ≫ χ)
      (SecAt.pull t.G t.PP.L σ (algebraMap R (FractionRing R))) e)
    (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (hV : GlobalTheory.LN.CDvr V) (φ : R →+* V)
    (F : FractionRing R →+* FractionRing V)
    (hring₀ : F.comp (algebraMap R (FractionRing R)) = (algebraMap V (FractionRing V)).comp φ) :
    ∃ eV : Fin N → V, (∀ j, algebraMap V (FractionRing V) (eV j) = F (e j)) ∧ ∃ j, IsUnit (eV j) := by
  obtain ⟨hdvr, -, -⟩ := (GlobalTheory.LN.cDvr_iff V).1 hV
  obtain ⟨i, hi⟩ : ∃ i : V →+* AlgebraicClosure (FractionRing V),
      i = (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp (algebraMap V (FractionRing V)) :=
    ⟨_, rfl⟩
  obtain ⟨i', hi'⟩ : ∃ i' : FractionRing R →+* AlgebraicClosure (FractionRing V),
      i' = (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp F := ⟨_, rfl⟩
  have hring : i'.comp (algebraMap R (FractionRing R)) = i.comp φ := by
    rw [hi, hi', RingHom.comp_assoc, hring₀, RingHom.comp_assoc]

  have : IsMonHom (Iso.refl t.G).hom := inferInstanceAs (IsMonHom (𝟙 t.G))
  have hid : IsGrpPullback t.G t.G (𝟙 _) (𝟙 t.G.left) := isGrpPullback_of_iso (Iso.refl t.G)
  have hmove : ∀ (R' : Type) [CommRing R'] (x : Sp R' ⟶ S), ∀ (R'' : Type) [CommRing R''] (j : R' →+* R''),
      PolFib t.G t.PP.L g x → PolFib t.G t.PP.L g (spMap j ≫ x) := fun R' _ x =>
    (GlobalTheory.T.principallyPolarisedFibre_iff_of_grpPullback S S t.G t.PP.L t.G t.PP.L (𝟙 S) (𝟙 t.G.left) t.PP.isLB t.PP.isLB hid
      (GlobalTheory.ThetaAffineGlue.lbIso_pull_id t.PP.isLB) g R' x).2
  have hPK : PolFib t.G t.PP.L g (spMap i' ≫ spMap (algebraMap R (FractionRing R)) ≫ χ) :=
    hmove _ _ _ i' hP
  have hmK : ((m : ℕ) : AlgebraicClosure (FractionRing V)) ≠ 0 := by
    have := (hmu.map (i'.comp (algebraMap R (FractionRing R)))).ne_zero
    simpa using this
  obtain ⟨pt, c, hT⟩ := GlobalTheory.T.exists_thetaConstantList_algClosed S t.G t.PP.L t.PP.rig t.PP.isLB t.PP.rigGen g m N
    (AlgebraicClosure (FractionRing V)) _
    (SecAt.pull t.G t.PP.L (SecAt.pull t.G t.PP.L σ (algebraMap R (FractionRing R))) i') hm hmK hN hPK
  have hsym := hS _ i' pt c hT

  have ex : spMap i' ≫ spMap (algebraMap R (FractionRing R)) ≫ χ = spMap i ≫ spMap φ ≫ χ := by
    rw [← Category.assoc, ← Category.assoc, ← spMap_comp, ← spMap_comp, hring]
  have hθ : HEq (SecAt.pull t.G t.PP.L (SecAt.pull t.G t.PP.L σ (algebraMap R (FractionRing R))) i')
      (SecAt.pull t.G t.PP.L (SecAt.pull t.G t.PP.L σ φ) i) :=
    ((pull_pull t.G t.PP.L σ _ i').trans (pull_heq_of_eq t.G t.PP.L σ hring)).trans
      (pull_pull t.G t.PP.L σ φ i).symm
  obtain ⟨pt', hT'⟩ := thList_of_heq t.PP.rig m ex hθ hT
  have hPV : PolFib t.G t.PP.L g (jK V ≫ spMap φ ≫ χ) := by
    have e₁ : jK V ≫ spMap φ ≫ χ = spMap F ≫ spMap (algebraMap R (FractionRing R)) ≫ χ := by
      rw [← Category.assoc, ← Category.assoc, ← spMap_comp, ← spMap_comp, hring₀]
    rw [e₁]; exact hmove _ _ _ F hP
  have hNZV := GlobalTheory.UMin.nz_pull S t.G t.PP.L t.PP.isLB t.semi R V χ σ φ hNZ
  have hmV : IsUnit ((m : ℕ) : V) := by simpa using hmu.map φ
  have hinj : Function.Injective i := by
    rw [hi, RingHom.coe_comp]
    exact (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).injective.comp
      (IsFractionRing.injective V (FractionRing V))
  have hprim := GlobalTheory.T.thetaConstants_primitive_principallyPolarised_trait E H S t g V hV (spMap φ ≫ χ) hPV (SecAt.pull t.G t.PP.L σ φ) hNZV m N hm hm3 hmV
    (AlgebraicClosure (FractionRing V)) i pt' c hinj hT'
  rw [hi] at hprim
  refine GlobalTheory.T.thetaSymmetricFunctionsDegreeFactorial_primitive_unit V (AlgebraicClosure (FractionRing V)) (algebraMap (FractionRing V) _) N c (fun j => F (e j))
    hprim (fun j => ?_)
  rw [← hsym j, hi']; rfl

end GlobalTheory.UMin.IntTheta

namespace GlobalTheory.UMin.IntTheta

theorem comp_inj {R V : Type} [CommRing R] [CommRing V] [IsDomain V] (φ : R →+* V) (hφ : Function.Injective φ) :
    Function.Injective ((algebraMap V (FractionRing V)).comp φ) := by
  rw [RingHom.coe_comp]; exact (IsFractionRing.injective V (FractionRing V)).comp hφ

theorem integral_with_unit : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S : Scheme.{0}) (t : SAB H S) (g m N : ℕ) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsIntegrallyClosed R] [CharZero R] (χ : Sp R ⟶ S) (σ : SecAt t.G t.PP.L χ) (e : Fin N → FractionRing R), Odd m → 3 ≤ m → IsUnit (m : R) → N = m ^ (4 * g) → PolFib t.G t.PP.L g (spMap (algebraMap R (FractionRing R)) ≫ χ) → NZ t.G t.PP.L χ σ → SymAt t.G t.PP.L t.PP.rig m (spMap (algebraMap R (FractionRing R)) ≫ χ) (SecAt.pull t.G t.PP.L σ (algebraMap R (FractionRing R))) e → ∃ e' : Fin N → R, (∀ j, algebraMap R (FractionRing R) (e' j) = e j) ∧ ∃ j, IsUnit (e' j) := by
  intro E _ _ _ H S t g m N R _ _ _ _ _ _ χ σ e hm hm3 hmu hN hP hNZ hS
  have key : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.LN.CDvr V → ∀ (φ : R →+* V)
      (hg : Function.Injective ((algebraMap V (FractionRing V)).comp φ)), ∃ eV : Fin N → V,
        (∀ j, algebraMap V (FractionRing V) (eV j) = IsFractionRing.lift hg (e j)) ∧ ∃ j, IsUnit (eV j) := by
    intro V _ _ _ hV φ hg
    have h₀ : (IsFractionRing.lift (K := FractionRing R) hg).comp (algebraMap R (FractionRing R)) =
        (algebraMap V (FractionRing V)).comp φ := by
      ext r
      rw [RingHom.comp_apply, IsFractionRing.lift_algebraMap]
    exact at_cdvr E H S t g m N R χ σ e hm hm3 hmu hN hP hNZ hS V hV φ _ h₀
  have hint : ∀ j, ∃ r : R, algebraMap R (FractionRing R) r = e j := by
    intro j
    obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.mk'_surjective (nonZeroDivisors R) (e j)
    change IsLocalization.mk' (FractionRing R) a b = e j at hab
    have hb0 : (b : R) ≠ 0 := nonZeroDivisors.ne_zero b.2
    have hdvd : (b : R) ∣ a := GlobalTheory.T.dvd_of_dvd_in_all_completeDVR_normal_noetherian R a b hb0 fun V _ _ _ hV φ hφ => by
      obtain ⟨eV, he, -⟩ := key V hV φ (comp_inj φ hφ)
      refine ⟨eV j, ?_⟩
      apply IsFractionRing.injective V (FractionRing V)
      have h1 := he j
      rw [← hab, IsFractionRing.lift_mk'] at h1
      have hb' : ((algebraMap V (FractionRing V)).comp φ) (b : R) ≠ 0 :=
        fun h => hb0 ((comp_inj φ hφ) (h.trans (map_zero _).symm))
      rw [eq_div_iff hb'] at h1
      simp only [RingHom.comp_apply] at h1
      rw [map_mul, ← h1, mul_comm]
    obtain ⟨r, hr⟩ := hdvd
    refine ⟨r, ?_⟩
    rw [← hab, hr, IsLocalization.mk'_mul_cancel_left]
  choose e' he' using hint
  refine ⟨e', he', ?_⟩
  obtain ⟨V, _, _, _, φ, hV, hφ, hloc⟩ := GlobalTheory.DvrDom.exists_cdvr_dominating R
  obtain ⟨eV, he, j, hu⟩ := key V hV φ (comp_inj φ hφ)
  have hj : φ (e' j) = eV j := by
    apply IsFractionRing.injective V (FractionRing V)
    rw [he j, ← he' j, IsFractionRing.lift_algebraMap, RingHom.comp_apply]
  refine ⟨j, (isUnit_map_iff φ _).1 ?_⟩
  rw [hj]; exact hu

end GlobalTheory.UMin.IntTheta
