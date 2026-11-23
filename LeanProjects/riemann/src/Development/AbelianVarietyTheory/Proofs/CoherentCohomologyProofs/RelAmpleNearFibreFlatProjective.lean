import Mathlib
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ExistsAwayFracOfMemHomLoc
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CubeTotalComplexAcyclicOfSlicesInductionOnCard
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FirstCohomologyVanishesOfIsoOfIsGen
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.SerreVanishingH1Twist
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsSectionLiftFibreNoFirstCohomologyStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SectionPull
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsProperOfIsProjBy
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsHomogeneousXPowMulAddXPowMul
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsHomOfVeryAmpleBy
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.VeryAmpleByPw
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.VeryAmpleByPwOfAffineLoci
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RelAmpleIffVeryAmpleBy
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw TopologicalSpace

namespace GlobalTheory.AmpleNear

section Geometry

variable {Y Y' W P S T : Scheme.{0}}

theorem isProper_lift (ψ : Y' ⟶ P) (f' : Y' ⟶ T) [IsProper f'] (q : P ⟶ S) [IsSeparated q]
    (t : T ⟶ S) (h : ψ ≫ q = f' ≫ t) : IsProper (pullback.lift ψ f' h) := by
  have : IsProper (pullback.lift ψ f' h ≫ pullback.snd q t) := by rwa [pullback.lift_snd]
  exact .of_comp _ (pullback.snd q t)

theorem isFinite_lift (ψ : Y' ⟶ P) (f' : Y' ⟶ T) [IsProper f'] (q : P ⟶ S) [IsSeparated q]
    (t : T ⟶ S) [IsAffineHom t] (h : ψ ≫ q = f' ≫ t) {ι : Type} (D : ι → P.Opens)
    (hD : ⨆ i, D i = ⊤) (hD' : ∀ i, IsAffineOpen (D i)) (hψ : ∀ i, IsAffineOpen (ψ ⁻¹ᵁ D i)) :
    IsFinite (pullback.lift ψ f' h) := by
  have := isProper_lift ψ f' q t h
  have : IsAffineHom (pullback.fst q t) :=
    isAffineHom_isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback q t).flip ‹_›
  have : IsAffineHom (pullback.lift ψ f' h) := by
    refine isAffineHom_of_forall_exists_isAffineOpen _ fun x => ?_
    obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (hD.ge (Set.mem_univ (pullback.fst q t x)))
    refine ⟨pullback.fst q t ⁻¹ᵁ D i, hi, (hD' i).preimage _, ?_⟩
    rw [← Scheme.Hom.comp_preimage, pullback.lift_fst]
    exact hψ i
  exact IsFinite.iff_isProper_and_isAffineHom.2 ⟨‹_›, ‹_›⟩

theorem isAffineHom_of_locallyQuasiFinite (ψ : Y' ⟶ P) [LocallyQuasiFinite ψ] (f' : Y' ⟶ T)
    [IsProper f'] (q : P ⟶ S) [IsSeparated q] (t : T ⟶ S) [IsAffineHom t] (h : ψ ≫ q = f' ≫ t) :
    IsAffineHom ψ := by
  have := isProper_lift ψ f' q t h
  have e : pullback.lift ψ f' h ≫ pullback.fst q t = ψ := pullback.lift_fst _ _ _
  have : LocallyQuasiFinite (pullback.lift ψ f' h ≫ pullback.fst q t) := by rwa [e]
  have : LocallyQuasiFinite (pullback.lift ψ f' h) := .of_comp _ (pullback.fst q t)
  have := IsFinite.of_isProper_of_locallyQuasiFinite (pullback.lift ψ f' h)
  have : IsAffineHom (pullback.fst q t) :=
    isAffineHom_isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback q t).flip ‹_›
  rw [← e]
  infer_instance

theorem exists_nhds_quasiFinite (f : Y ⟶ S) [IsProper f] (j : W ⟶ Y) [IsOpenImmersion j]
    (q : P ⟶ S) [IsSeparated q] (φ : W ⟶ P) [LocallyOfFiniteType φ] (hφ : φ ≫ q = j ≫ f)
    (t : T ⟶ S) [IsAffineHom t] (ρ : Y' ⟶ W) (f' : Y' ⟶ T) (h : IsPullback (ρ ≫ j) f' f t)
    {ι : Type} (D : ι → P.Opens) (hD : ⨆ i, D i = ⊤) (hD' : ∀ i, IsAffineOpen (D i))
    (hψ : ∀ i, IsAffineOpen ((ρ ≫ φ) ⁻¹ᵁ D i)) (s : T) :
    ∃ U : S.Opens, t s ∈ U ∧ f ⁻¹ᵁ U ≤ j ''ᵁ φ.quasiFiniteLocus := by
  have : IsProper f' := MorphismProperty.of_isPullback (P := @IsProper) h ‹_›
  have hw : (ρ ≫ φ) ≫ q = f' ≫ t := by rw [Category.assoc, hφ, ← Category.assoc, h.w]
  have hfin := isFinite_lift (ρ ≫ φ) f' q t hw D hD hD' hψ
  have h₁ : IsPullback ρ f' (j ≫ f) t := by
    refine ⟨⟨by rw [← Category.assoc, h.w]⟩, ⟨PullbackCone.IsLimit.mk _
      (fun c => h.lift (c.fst ≫ j) c.snd (by rw [Category.assoc, c.condition])) (fun c => ?_)
      (fun c => h.lift_snd _ _ _) fun c m h1 h2 => ?_⟩⟩
    · rw [← cancel_mono j, Category.assoc, h.lift_fst]
    · refine h.hom_ext ?_ ?_
      · rw [h.lift_fst, ← Category.assoc, h1]
      · rw [h.lift_snd, h2]
  have h₂ : IsPullback ρ (pullback.lift (ρ ≫ φ) f' hw) φ (pullback.fst q t) := by
    refine IsPullback.of_bot ?_ (pullback.lift_fst _ _ _).symm (IsPullback.of_hasPullback q t)
    rwa [pullback.lift_snd, hφ]
  refine ⟨⟨_, (f.isClosedMap _ (j ''ᵁ φ.quasiFiniteLocus).isOpen.isClosed_compl).isOpen_compl⟩,
    ?_, fun y hy => by_contra fun H => hy ⟨y, H, rfl⟩⟩
  rintro ⟨y, hy, hys⟩
  obtain ⟨z, rfl, -⟩ := Scheme.exists_preimage_of_isPullback h y s hys
  refine hy ⟨ρ z, ?_, (Scheme.Hom.comp_apply _ _ _).symm⟩
  have hf : (φ ⁻¹' {φ (ρ z)}).Finite := by
    refine (((pullback.lift (ρ ≫ φ) f' hw).finite_preimage_singleton
      (pullback.lift (ρ ≫ φ) f' hw z)).image ρ).subset fun w hw' => ?_
    obtain ⟨z', h1, h2⟩ := Scheme.exists_preimage_of_isPullback h₂ w
      (pullback.lift (ρ ≫ φ) f' hw z) (by
        rw [← Scheme.Hom.comp_apply, pullback.lift_fst, Scheme.Hom.comp_apply]; exact hw')
    exact ⟨z', h2, h1⟩
  have : Finite (φ.fiber (φ (ρ z))) := (φ.fiberHomeo _).finite_iff.mpr hf
  exact Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber.mpr (isOpen_discrete _)

theorem exists_isAffineHom (f : Y ⟶ S) [IsProper f] (j : W ⟶ Y) [IsOpenImmersion j]
    (q : P ⟶ S) [IsSeparated q] (φ : W ⟶ P) [LocallyOfFiniteType φ] (hφ : φ ≫ q = j ≫ f)
    (t : T ⟶ S) [IsAffineHom t] [IsOpenImmersion t] (π : Y' ⟶ Y) (f' : Y' ⟶ T)
    (h : IsPullback π f' f t) (hπ : ∀ y, π y ∈ j ''ᵁ φ.quasiFiniteLocus) :
    ∃ ρ : Y' ⟶ W, ρ ≫ j = π ∧ IsAffineHom (ρ ≫ φ) := by
  have : IsProper f' := MorphismProperty.of_isPullback (P := @IsProper) h ‹_›
  have : IsOpenImmersion π := MorphismProperty.of_isPullback (P := @IsOpenImmersion) h.flip ‹_›
  have hr : Set.range π ⊆ Set.range j := by
    rintro _ ⟨y, rfl⟩
    obtain ⟨w, -, hw⟩ := hπ y
    exact ⟨w, hw⟩
  have e := IsOpenImmersion.lift_fac j π hr
  refine ⟨IsOpenImmersion.lift j π hr, e, ?_⟩
  generalize IsOpenImmersion.lift j π hr = ρ at e
  subst e
  have : IsOpenImmersion ρ := .of_comp ρ j
  have : LocallyQuasiFinite (ρ ≫ φ) := by
    rw [← Scheme.Hom.quasiFiniteLocus_eq_top_iff, Scheme.Hom.quasiFiniteLocus_comp]
    refine top_le_iff.1 fun y _ => ?_
    obtain ⟨w, hw, e⟩ := hπ y
    obtain rfl : w = ρ y := j.injective (e.trans (Scheme.Hom.comp_apply _ _ _))
    exact hw
  exact isAffineHom_of_locallyQuasiFinite _ f' q t
    (by rw [Category.assoc, hφ, ← Category.assoc, h.w])

end Geometry

section Powers

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {X Y : Scheme.{0}}

theorem res_res {U V W : X.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) (u : Γ(X, U)ˣ) :
    res h₂ (res h₁ u) = res (h₂.trans h₁) u :=
  Units.ext (rs_rs h₁ h₂ u.val)

theorem pw_pw (H : LB X) (a b : ℤ) : AbLaw.pw (AbLaw.pw H a) b = AbLaw.pw H (a * b) := by
  exact congrArg (fun g => (⟨H.ι, H.U, g⟩ : LB X))
    (funext fun i => funext fun j => (zpow_mul (H.g i j) a b).symm)

theorem pw_pull (H : LB X) (f : Y ⟶ X) (a : ℤ) :
    (AbLaw.pw H a).pull f = AbLaw.pw (H.pull f) a := by
  have : ((AbLaw.pw H a).pull f).g = (AbLaw.pw (H.pull f) a).g := by
    funext j j'
    change (∏ k : PUnit, (res _ (pullU f _ (H.g (j k) (j' k) ^ a))) ^ (1 : ℤ)) =
      (∏ k : PUnit, (res _ (pullU f _ (H.g (j k) (j' k)))) ^ (1 : ℤ)) ^ a
    simp only [Fintype.prod_unique, zpow_one, map_zpow]
  exact congrArg (fun g => (⟨(H.pull f).ι, (H.pull f).U, g⟩ : LB Y)) this

theorem cocycle_on {H : LB X} (hH : H.IsLB) (i j k : H.ι) {W : X.Opens} (hi : W ≤ H.U i)
    (hj : W ≤ H.U j) (hk : W ≤ H.U k) :
    res (le_inf hi hj) (H.g i j) * res (le_inf hj hk) (H.g j k) = res (le_inf hi hk) (H.g i k) := by
  have h := congrArg (res (le_inf (le_inf hi hj) hk : W ≤ H.U i ⊓ H.U j ⊓ H.U k)) (hH.cocycle i j k)
  simpa only [map_mul, res_res] using h

theorem rel_on {H : LB X} (hH : H.IsLB) (i k i' k' : H.ι) {W : X.Opens} (hi : W ≤ H.U i)
    (hk : W ≤ H.U k) (hi' : W ≤ H.U i') (hk' : W ≤ H.U k') :
    res (le_inf hi hk) (H.g i k) = res (le_inf hi hi') (H.g i i') * (res (le_inf hk hk') (H.g k k'))⁻¹ *
      res (le_inf hi' hk') (H.g i' k') := by
  rw [mul_right_comm, eq_mul_inv_iff_mul_eq, cocycle_on hH i k k' hi hk hk',
    cocycle_on hH i i' k' hi hi' hk']

theorem lbIso_tw {H : LB X} (hH : H.IsLB) (t : ℤ) : LBIso (AbLaw.pw H (t + 1)) (tw H H t) := by
  refine ⟨⟨fun p => res (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
      H.U p.1.1 ⊓ H.U p.1.2 ⊓ H.U p.2 ≤ H.U p.1.1 ⊓ H.U p.2) (H.g p.1.1 p.2) *
    res (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
      H.U p.1.1 ⊓ H.U p.1.2 ⊓ H.U p.2 ≤ H.U p.1.2 ⊓ H.U p.2) (H.g p.1.2 p.2) ^ t⟩, ?_⟩
  rintro ⟨⟨i, j : H.ι⟩, k : H.ι⟩ ⟨⟨i', j' : H.ι⟩, k' : H.ι⟩
  let W : X.Opens := H.U i ⊓ H.U j ⊓ H.U k ⊓ (H.U i' ⊓ H.U j' ⊓ H.U k')
  have hi : W ≤ H.U i := inf_le_left.trans (inf_le_left.trans inf_le_left)
  have hj : W ≤ H.U j := inf_le_left.trans (inf_le_left.trans inf_le_right)
  have hk : W ≤ H.U k := inf_le_left.trans inf_le_right
  have hi' : W ≤ H.U i' := inf_le_right.trans (inf_le_left.trans inf_le_left)
  have hj' : W ≤ H.U j' := inf_le_right.trans (inf_le_left.trans inf_le_right)
  have hk' : W ≤ H.U k' := inf_le_right.trans inf_le_right
  change res (inf_le_left : W ≤ H.U i ⊓ H.U j ⊓ H.U k) (res _ (H.g i k) * res _ (H.g j k) ^ t) =
    (res (V := W) (U := H.U i ⊓ H.U j ⊓ (H.U i' ⊓ H.U j')) _
        (res (V := H.U i ⊓ H.U j ⊓ (H.U i' ⊓ H.U j')) _ (H.g i i') *
          (res (V := H.U i ⊓ H.U j ⊓ (H.U i' ⊓ H.U j')) _ (H.g j j' ^ (-t)))⁻¹) *
      (res (V := W) _ (H.g k k' ^ (t + 1)))⁻¹) *
    res (inf_le_right : W ≤ H.U i' ⊓ H.U j' ⊓ H.U k') (res _ (H.g i' k') * res _ (H.g j' k') ^ t)
  simp only [map_mul, map_inv, map_zpow, res_res]
  erw [res_res, res_res]
  rw [rel_on hH i k i' k' hi hk hi' hk', rel_on hH j k j' k' hj hk hj' hk']
  simp only [zpow_neg, inv_inv, mul_zpow, inv_zpow, zpow_add_one, mul_inv]
  ac_rfl

theorem exists_pw_h1Zero (R : Type) [CommRing R] [IsNoetherianRing R]
    (B : Over (Spec (CommRingCat.of R))) (L : LB B.left) (hL : L.IsLB) (h : RelAmple B L) :
    ∃ d : ℕ, 1 ≤ d ∧ FirstCohomologyVanishes (AbLaw.pw L d) ∧
      ∃ (n : ℕ) (s : Fin (n + 1) → LB.Sec (AbLaw.pw L d)), VeryAmpleBy B.hom (AbLaw.pw L d) s := by
  obtain ⟨d₀, hd₀, n₀, s₀, hs₀⟩ := (Unif.relAmple_iff_veryAmpleBy R B L hL).1 h
  have hH := isLB_pw hL (d₀ : ℤ)
  obtain ⟨t₀, ht₀⟩ := exists_h1Zero_tw_of_veryAmpleBy R B.left B.hom _ n₀ s₀ _ hH hH hs₀
  have h1 := ht₀ (t₀.toNat : ℤ) (Int.self_le_toNat t₀)
  obtain ⟨w, hw⟩ := lbIso_tw hH (t₀.toNat : ℤ)
  have h2 := H1Iso.firstCohomologyVanishes_of_iso_of_isGen (isLB_tw hH hH _).cover (isLB_pw hH _) w hw h1
  have h3 := veryAmpleBy_pw R B.left B.hom _ n₀ s₀ hH hs₀ (t₀.toNat + 1) (Nat.le_add_left _ _)
  have e : AbLaw.pw (AbLaw.pw L (d₀ : ℤ)) ((t₀.toNat + 1 : ℕ) : ℤ) =
      AbLaw.pw L ((d₀ * (t₀.toNat + 1) : ℕ) : ℤ) := by
    rw [pw_pw, Nat.cast_mul]
  refine ⟨d₀ * (t₀.toNat + 1), Nat.mul_pos hd₀ (Nat.succ_pos _), ?_, ?_⟩
  · rw [← e, Nat.cast_add, Nat.cast_one]
    exact h2
  · rw [← e]
    exact h3

end Powers

section Sections

variable {Y Y₀ : Scheme.{0}} {R K : Type} [CommRing R] [Field K]

theorem preimage_nonzeroLocus_of_pull_eq {f : Y ⟶ Spec (CommRingCat.of R)}
    {f₀ : Y₀ ⟶ Spec (CommRingCat.of K)} {π : Y₀ ⟶ Y} {g : R →+* K}
    (w : π ≫ f = f₀ ≫ Spec.map (CommRingCat.ofHom g)) (M : LB Y) (x : SecOnR f M ⊤)
    (x₀ : SecOnR f₀ (M.pull π) ⊤) {c : K} (hc : c ≠ 0)
    (h : SecOnR.pull M w ⊤ ⊤ le_top x = c • x₀) :
    π ⁻¹ᵁ nonzeroLocus (SecOnR.topEquiv f M x) =
      nonzeroLocus (SecOnR.topEquiv f₀ (M.pull π) x₀) := by
  have e₁ : SecOnR.topEquiv f₀ (M.pull π) (SecOnR.pull M w ⊤ ⊤ le_top x) =
      secPull (SecOnR.topEquiv f M x) π := by
    refine DVR.SecOps.sec_ext fun i => ?_
    refine (congrArg (rs Y₀ _) (SecOn.coord_pullLE π le_top x i)).trans ?_
    change (π.appLE _ _ _ ≫ Y₀.presheaf.map _).hom _ = (Y.presheaf.map _ ≫ π.appLE _ _ _).hom _
    rw [Scheme.Hom.appLE_map, Scheme.Hom.map_appLE]
    rfl
  have e₂ : SecOnR.topEquiv f₀ (M.pull π) (c • x₀) =
      DVR.SecOps.secScale (cst f₀ ⊤ c) (SecOnR.topEquiv f₀ (M.pull π) x₀) := by
    rw [SecOnR.smul_def, map_smul]
    rfl
  rw [← nonzeroLocus_secPull, ← e₁, h, e₂, nonzeroLocus_secScale,
    Scheme.basicOpen_of_isUnit _ (hc.isUnit.map _), top_inf_eq]

theorem exists_hom_preimage_eq (f : Y ⟶ Spec (CommRingCat.of R)) (H : LB Y) (hH : H.IsLB) {n : ℕ}
    (s : Fin (n + 1) → LB.Sec H) (hs : ⨆ i, nonzeroLocus (s i) = ⊤) :
    ∃ (P : Scheme.{0}) (q : P ⟶ Spec (CommRingCat.of R)) (φ : Y ⟶ P) (D : Fin (n + 1) → P.Opens),
      IsProper q ∧ φ ≫ q = f ∧ ⨆ i, D i = ⊤ ∧ (∀ i, IsAffineOpen (D i)) ∧
        ∀ i, φ ⁻¹ᵁ D i = nonzeroLocus (s i) := by
  obtain ⟨P, q, O, t, hO, ht, hJ⟩ := ProjQuot.exists_veryAmpleBy_of_ideal R n ⊥ (fun F hF t => by
    rw [Ideal.mem_bot.1 hF, map_zero]; exact Ideal.zero_mem _)
  obtain ⟨φ, w, h1, h2, h3⟩ := exists_hom_of_veryAmpleBy R P q O n t hO ht Y f H s hH hs
    (fun d F hF h0 k => by
      obtain ⟨m, hm⟩ := (hJ d F hF).1 h0 0
      have : F = 0 := (MvPolynomial.isRegular_X_pow (R := R) (n := (0 : Fin (n + 1))) m).left
        ((Ideal.mem_bot.1 hm).trans (mul_zero _).symm)
      rw [this, map_zero])
  exact ⟨P, q, φ, fun i => nonzeroLocus (t i), isProper_of_isProjBy R P q ⟨O, hO, n, t, ht⟩, h1,
    ht.1, fun i => (ht.2 i).1,
    fun i => ((SecPullIso.section_pull P Y φ O H w hO hH h2 (t i)).2 (s i) (h3 i)).symm⟩

theorem relAmple_of_affine_loci {S : Scheme.{0}} [IsAffine S] (A : Over S) [IsProper A.hom]
    (L : LB A.left) (hL : L.IsLB) {d : ℕ} (hd : 1 ≤ d) {n : ℕ} (s : Fin (n + 1) → LB.Sec (pw L d))
    (hs : ⨆ i, nonzeroLocus (s i) = ⊤) (hs' : ∀ i, IsAffineOpen (nonzeroLocus (s i))) :
    RelAmple A L := by
  let A' : Over (Spec (CommRingCat.of Γ(S, ⊤))) := Over.mk (A.hom ≫ S.isoSpec.hom)
  have : IsProper A'.hom := inferInstanceAs (IsProper (A.hom ≫ S.isoSpec.hom))
  obtain ⟨e, he, h⟩ := veryAmpleBy_pw_of_affine_loci Γ(S, ⊤) A.left A'.hom (pw L d) n s
    (isLB_pw hL d) hs hs'
  rw [pw_pw, ← Nat.cast_mul] at h
  have h' : RelAmple A' L := (Unif.relAmple_iff_veryAmpleBy Γ(S, ⊤) A' L hL).2
    ⟨d * e, Nat.mul_pos hd he, h⟩
  exact (relAmple_iff_isAmpleLB_of_isAffine A hL).2 (isAmpleLB_of_relAmple_of_isAffine A' hL h')

theorem exists_affine_loci_near (f : Y ⟶ Spec (CommRingCat.of R)) [IsProper f] (H : LB Y)
    (hH : H.IsLB) {n : ℕ} (s : Fin (n + 1) → LB.Sec H) (g : R →+* K) (π : Y₀ ⟶ Y)
    (f₀ : Y₀ ⟶ Spec (CommRingCat.of K)) (h : IsPullback π f₀ f (Spec.map (CommRingCat.ofHom g)))
    (hs : ⨆ i, π ⁻¹ᵁ nonzeroLocus (s i) = ⊤) (hs' : ∀ i, IsAffineOpen (π ⁻¹ᵁ nonzeroLocus (s i))) :
    ∃ r : R, g r ≠ 0 ∧ ∀ (Y' : Scheme.{0}) (π' : Y' ⟶ Y) f', IsPullback π' f' f
      (Scheme.Opens.ι (X := Spec (CommRingCat.of R)) (PrimeSpectrum.basicOpen r)) →
      ⨆ i, π' ⁻¹ᵁ nonzeroLocus (s i) = ⊤ ∧ ∀ i, IsAffineOpen (π' ⁻¹ᵁ nonzeroLocus (s i)) := by
  let W : Y.Opens := ⨆ i, nonzeroLocus (s i)
  obtain ⟨P, q, φ, D, hq, hφ, hD, hD', hφD⟩ := exists_hom_preimage_eq (W.ι ≫ f) (H.pull W.ι)
    (LB.isLB_pull hH _) (fun i => secPull (s i) W.ι) (by
      simp only [nonzeroLocus_secPull]
      rw [← Scheme.Hom.preimage_iSup]
      exact W.ι_preimage_self)
  simp only [nonzeroLocus_secPull] at hφD
  have key : ∀ {Z : Scheme.{0}} (ρ : Z ⟶ W) i,
      (ρ ≫ φ) ⁻¹ᵁ D i = (ρ ≫ W.ι) ⁻¹ᵁ nonzeroLocus (s i) := fun ρ i => by
    rw [Scheme.Hom.comp_preimage, Scheme.Hom.comp_preimage, hφD]
  have : LocallyOfFiniteType (φ ≫ q) := by rw [hφ]; infer_instance
  have : LocallyOfFiniteType φ := locallyOfFiniteType_of_comp φ q
  have hr : Set.range π ⊆ Set.range W.ι := by
    rintro _ ⟨y, rfl⟩
    obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (hs.ge (Set.mem_univ y))
    exact ⟨⟨π y, Opens.mem_iSup.2 ⟨i, hi⟩⟩, rfl⟩
  have e := IsOpenImmersion.lift_fac W.ι π hr
  generalize IsOpenImmersion.lift W.ι π hr = ρ at e
  subst e
  obtain ⟨U, hU, hU'⟩ := exists_nhds_quasiFinite f W.ι q φ hφ _ ρ f₀ h D hD hD'
    (fun i => (key ρ i).symm ▸ hs' i) (⊥ : PrimeSpectrum K)
  obtain ⟨_, ⟨r, rfl⟩, hr1, hr2⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hU U.isOpen
  refine ⟨r, hr1, fun Y' π' f' h' => ?_⟩
  have : IsAffine (Scheme.Opens.toScheme (X := Spec (CommRingCat.of R))
    (PrimeSpectrum.basicOpen r)) := IsAffineOpen.Spec_basicOpen (R := CommRingCat.of R) r
  have : IsOpenImmersion (Scheme.Opens.ι (X := Spec (CommRingCat.of R))
    (PrimeSpectrum.basicOpen r)) := Scheme.Opens.instIsOpenImmersionι (X := Spec (CommRingCat.of R)) _
  obtain ⟨ρ', rfl, hρ'⟩ := exists_isAffineHom f W.ι q φ hφ
    (Scheme.Opens.ι (X := Spec (CommRingCat.of R)) (PrimeSpectrum.basicOpen r)) π' f' h' fun y => hU' (hr2 (by
    change (π' ≫ f) y ∈ _
    rw [h'.w]
    exact (f' y).2))
  simp only [← key]
  exact ⟨by rw [← Scheme.Hom.preimage_iSup, hD]; rfl, fun i => (hD' i).preimage _⟩

end Sections

theorem relAmple_near_fibre : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (B : Over (Spec (CommRingCat.of R))) (L : LB B.left), Flat B.hom → IsProjBy B.hom → L.IsLB → ∀ (K : Type) [Field K] (g : R →+* K), (∀ y : K, ∃ a b : R, g b ≠ 0 ∧ y * g b = g a) → RelAmple ((Over.pullback (Spec.map (CommRingCat.ofHom g))).obj B) (L.pull (pullback.fst B.hom (Spec.map (CommRingCat.ofHom g)))) → ∃ r : R, g r ≠ 0 ∧ RelAmple ((Over.pullback (Scheme.Opens.ι (X := Spec (CommRingCat.of R)) (PrimeSpectrum.basicOpen r))).obj B) (L.pull (pullback.fst B.hom (Scheme.Opens.ι (X := Spec (CommRingCat.of R)) (PrimeSpectrum.basicOpen r)))) := by
  intro R _ _ B L hF hP hL K _ g hg hA
  have hp := isProper_of_isProjBy R B.left B.hom hP
  have h := IsPullback.of_hasPullback B.hom (Spec.map (CommRingCat.ofHom g))
  obtain ⟨d, hd, h0, hv⟩ := exists_pw_h1Zero K _ _ (LB.isLB_pull hL _) hA
  have hv' : FirstCohomologyVanishes ((pw L d).pull (pullback.fst B.hom (Spec.map (CommRingCat.ofHom g)))) ∧
      ∃ (n : ℕ) (s : Fin (n + 1) → LB.Sec ((pw L d).pull
        (pullback.fst B.hom (Spec.map (CommRingCat.ofHom g))))),
      ⨆ i, nonzeroLocus (s i) = ⊤ ∧ ∀ i, IsAffineOpen (nonzeroLocus (s i)) := by
    rw [pw_pull]
    obtain ⟨n, s, hs⟩ := hv
    exact ⟨h0, n, s, hs.1, fun i => (hs.2 i).1⟩
  obtain ⟨h1, n, s₀, hs₀, hs₀'⟩ := hv'
  choose c x hc hx using fun i => GlobalTheory.T.exists_section_lift_fibre_noFirstCohomology R B.left B.hom (pw L d) hF hP (isLB_pw hL d) K g hg
    _ _ _ h h1 ((SecOnR.topEquiv _ _).symm (s₀ i))
  have e := fun i => preimage_nonzeroLocus_of_pull_eq h.w (pw L d) (x i) _ (hc i) (hx i)
  simp only [LinearEquiv.apply_symm_apply] at e
  obtain ⟨r, hr, hr'⟩ := exists_affine_loci_near B.hom (pw L d) (isLB_pw hL d)
    (fun i => SecOnR.topEquiv B.hom _ (x i)) g _ _ h (by simpa only [e] using hs₀)
    (by simpa only [e] using hs₀')
  refine ⟨r, hr, ?_⟩
  let j := Scheme.Opens.ι (X := Spec (CommRingCat.of R)) (PrimeSpectrum.basicOpen r)
  have : IsAffine (Scheme.Opens.toScheme (X := Spec (CommRingCat.of R))
    (PrimeSpectrum.basicOpen r)) := IsAffineOpen.Spec_basicOpen (R := CommRingCat.of R) r
  have hv : ∃ s : Fin (n + 1) → LB.Sec (pw (L.pull (pullback.fst B.hom j)) d),
      ⨆ i, nonzeroLocus (s i) = ⊤ ∧ ∀ i, IsAffineOpen (nonzeroLocus (s i)) := by
    rw [← pw_pull]
    refine ⟨fun i => secPull (SecOnR.topEquiv B.hom _ (x i)) _, ?_⟩
    simp only [nonzeroLocus_secPull]
    exact hr' _ _ _ (IsPullback.of_hasPullback B.hom j)
  obtain ⟨s, hs, hs'⟩ := hv
  have : IsProper ((Over.pullback j).obj B).hom := inferInstanceAs (IsProper (pullback.snd B.hom j))
  exact relAmple_of_affine_loci ((Over.pullback j).obj B) _ (LB.isLB_pull hL _) hd s hs hs'

end GlobalTheory.AmpleNear
