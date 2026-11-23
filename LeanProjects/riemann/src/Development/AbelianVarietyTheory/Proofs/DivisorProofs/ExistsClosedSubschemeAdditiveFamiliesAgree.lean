import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsClosedSubschemeLocallyTrivialProductLineBu
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TrivOnOfSubsingleton
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsProjOverOfIsProjOverBase
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.TrivPullCompIff
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SecLinOfSecScal

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.DualLocus

theorem exists_ideal_locTriv_noeth (hG : GlobalFnsSt) (R : Type) [CommRing R] [IsNoetherianRing R]
    (B : Over (Spec (CommRingCat.of R))) [GrpObj B] (hB : IsAbelianScheme B) (F : LB B.left) (hF : F.IsLB) :
    ∃ I : Ideal R, ∀ (R' : Type) [CommRing R'] (g : R →+* R') (X' : Scheme.{0}) (π : X' ⟶ B.left)
      (f' : X' ⟶ Spec (CommRingCat.of R')), IsPullback π f' B.hom (Spec.map (CommRingCat.ofHom g)) →
      ((∀ p : Spec (CommRingCat.of R'), ∃ U : (Spec (CommRingCat.of R')).Opens, p ∈ U ∧
        Triv ((F.pull π).pull (f' ⁻¹ᵁ U).ι)) ↔ I ≤ RingHom.ker g) := by
  haveI := hB.proper
  haveI := hB.geomConnected
  haveI := hB.smooth
  have hP := ProperFinite.nonempty_perf_of_isProper (R := R) B.hom hF
  have hQ := ProperFinite.nonempty_perf_of_isProper (R := R) B.hom (isLB_pw hF (-1))
  have hC := GlobalTheory.TrivLocus.isClosed_trivLocus R _ B.hom F hF hP hQ hB.proper
    (GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ _ hB.smooth hB.geomConnected)
  obtain ⟨I, hI⟩ := TrivRep.exists_ideal (TrivRep.TrivOn B.hom F) (TrivRep.TrivOn.comp B.hom F) (fun p => by
    by_cases hp : p ∈ {p : PrimeSpectrum R | ∃ (K : Type) (_ : Field K) (g : R →+* K) (X' : Scheme.{0})
      (π : X' ⟶ B.left) (f' : X' ⟶ Spec (CommRingCat.of K)), RingHom.ker g = p.asIdeal ∧
        IsPullback π f' B.hom (Spec.map (CommRingCat.ofHom g)) ∧ Triv (F.pull π)}
    · obtain ⟨K, _, g₀, X₀, π₀, f₀, hk, h₀, ht⟩ := hp
      obtain ⟨r, I, hr, -, H⟩ := GlobalTheory.AbLaw.Seesaw.seesaw R _ B.hom F hF hP inferInstance inferInstance K g₀ X₀ π₀ f₀
        h₀ (CubeOpen.bijective_appTop hG B hB h₀) ht
      exact ⟨r, hk ▸ hr, I, fun S _ g hu => H S g _ _ _ (IsPullback.of_hasPullback _ _) hu⟩
    · obtain ⟨_, ⟨r, rfl⟩, hr, hU⟩ := PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
        (Set.mem_compl hp) hC.isOpen_compl
      refine ⟨r, hr, ⊤, fun S _ g hu => ⟨fun ht => ?_, fun h => ?_⟩⟩
      · rcases subsingleton_or_nontrivial S with _ | _
        · exact fun a _ => Subsingleton.elim _ _
        obtain ⟨m, hm⟩ := Ideal.exists_maximal S
        letI := Ideal.Quotient.field m
        let g' := (Ideal.Quotient.mk m).comp g
        refine (hU (a := ⟨RingHom.ker g', RingHom.ker_isPrime g'⟩) (hu.map (Ideal.Quotient.mk m)).ne_zero ?_).elim
        exact ⟨S ⧸ m, inferInstance, g', _, _, _, rfl, IsPullback.of_hasPullback _ _, ht.comp B.hom F S g _ _⟩
      · haveI : Subsingleton S := subsingleton_of_zero_eq_one
          ((h (Submodule.mem_top (x := 1))).symm.trans (map_one g))
        exact TrivRep.trivOn_of_subsingleton B.hom F S g)
  refine ⟨I, fun S _ g X' π f' h => ?_⟩
  rw [← hI S g]
  exact forall_congr' fun q => TrivRep.loc_iff B.hom F h q

variable {S : Scheme.{0}} (A : Over S)

theorem isPullback_lift {Y T : Over S} (y : Y ⟶ T) :
    IsPullback (lift (fst A Y) (snd A Y ≫ y)).left (snd A Y).left (snd A T).left y.left := by
  have h₀ : IsPullback (pullback.fst A.hom T.hom) (snd A T).left A.hom T.hom :=
    IsPullback.of_hasPullback A.hom T.hom
  have e₁ : (lift (fst A Y) (snd A Y ≫ y)).left ≫ pullback.fst A.hom T.hom = (fst A Y).left := by
    rw [show pullback.fst A.hom T.hom = (fst A T).left from rfl, ← Over.comp_left, lift_fst]
  have big : IsPullback ((lift (fst A Y) (snd A Y ≫ y)).left ≫ pullback.fst A.hom T.hom) (snd A Y).left A.hom
      (y.left ≫ T.hom) := by
    have := IsPullback.of_hasPullback A.hom Y.hom
    rw [e₁, Over.w y]
    exact this
  exact IsPullback.of_right big (by rw [← Over.comp_left, lift_snd, Over.comp_left]) h₀

theorem exists_closed_locTriv_noeth (hG : GlobalFnsSt) {T : Over S} [GrpObj A] [IsLocallyNoetherian T.left]
    (hA : IsAbelianScheme A) (F : LB (A ⊗ T).left) (hF : F.IsLB) :
    ∃ (G : Over S) (i : G ⟶ T), IsClosedImmersion i.left ∧ ∀ (Y : Over S) (y : Y ⟶ T),
      TrivSubscheme.LocTrivOver (snd A T).left F Y.left y.left ↔ ∃ z : Y ⟶ G, z ≫ i = y := by
  have h₀ : IsPullback (pullback.fst A.hom T.hom) (snd A T).left A.hom T.hom :=
    IsPullback.of_hasPullback A.hom T.hom
  obtain ⟨I, hI⟩ := TrivSubscheme.exists_idealSheaf (TrivSubscheme.LocTrivOver (snd A T).left F)
    TrivSubscheme.LocTrivOver.comp TrivSubscheme.locTrivOver_of_affine (fun U => by
      haveI := IsLocallyNoetherian.component_noetherian U
      let t : Spec (CommRingCat.of Γ(T.left, U)) ⟶ S := U.2.fromSpec ≫ T.hom
      have h₁ : IsPullback (pullback.fst A.hom t) (pullback.snd A.hom t) A.hom (U.2.fromSpec ≫ T.hom) :=
        IsPullback.of_hasPullback _ _
      let φ := h₀.lift _ _ (h₁.w.trans (Category.assoc _ _ _).symm)
      have h₂ : IsPullback φ (pullback.snd A.hom t) (snd A T).left U.2.fromSpec :=
        IsPullback.of_right (by rw [h₀.lift_fst]; exact h₁) (h₀.lift_snd _ _ _) h₀
      obtain ⟨I, hI⟩ := exists_ideal_locTriv_noeth hG Γ(T.left, U) ((Over.pullback t).obj A)
        (CubeGen.isAb_baseChange hA t) (F.pull φ) (LB.isLB_pull hF φ)
      refine ⟨I, fun R g => ?_⟩
      have h₃ := IsPullback.of_hasPullback (pullback.snd A.hom t) (Spec.map g)
      rw [← hI R g.hom _ _ _ h₃, TrivSubscheme.locTrivOver_iff (h₃.paste_horiz h₂)]
      refine forall_congr' fun y => exists_congr fun V => and_congr_right fun _ => ?_
      rw [← Category.assoc]
      exact ((TrivSubscheme.triv_pull_iff _ _ _).trans (TrivSubscheme.triv_pull_iff _ _ _)).symm)
  refine ⟨Over.mk (I.subschemeι ≫ T.hom), Over.homMk I.subschemeι rfl,
    inferInstanceAs (IsClosedImmersion I.subschemeι), fun Y y => ?_⟩
  rw [hI]
  constructor
  · intro h
    have h' : I.subschemeι.ker ≤ y.left.ker := by rwa [Scheme.IdealSheafData.ker_subschemeι]
    refine ⟨Over.homMk (IsClosedImmersion.lift I.subschemeι y.left h') ?_, ?_⟩
    · exact (IsClosedImmersion.lift_fac_assoc _ _ _ _).trans (Over.w y)
    · exact Over.OverMorphism.ext (IsClosedImmersion.lift_fac _ _ _)
  · rintro ⟨z, rfl⟩
    exact I.ker_subschemeι.ge.trans (Scheme.Hom.le_ker_comp z.left I.subschemeι)

variable {A} [GrpObj A]

theorem same_iff_locTriv (hG : GlobalFnsSt) (hA : IsAbelianScheme A) {T : Over S} {N N' : LB (A ⊗ T).left}
    (hN : Fam A N) (hN' : Fam A N') {F : LB (A ⊗ T).left} (hF : F.IsLB)
    (hc : cls F hF = cls N hN.isLB - cls N' hN'.isLB) (Y : Over S) (y : Y ⟶ T) :
    Same A N N' y y ↔ TrivSubscheme.LocTrivOver (snd A T).left F Y.left y.left := by
  let ψ := (lift (fst A Y) (snd A Y ≫ y)).left
  let p := (snd A Y).left
  let e := (lift (1 : Y ⟶ A) (𝟙 Y)).left
  have he : e ≫ p = 𝟙 Y.left := by
    simp only [e, p]
    rw [← Over.comp_left, lift_snd, Over.id_left]
  have hs : Same A N N' y y ↔ CechPic.pull ψ (cls F hF) = 0 := by
    rw [same_iff hN.isLB hN'.isLB, hc, map_sub, sub_eq_zero]
    rfl
  have key : ∀ {Z : Scheme.{0}} (r : Z ⟶ (A ⊗ Y).left),
      Triv (F.pull (r ≫ ψ)) ↔ CechPic.pull r (CechPic.pull ψ (cls F hF)) = 0 := fun r => by
    rw [← pull_comp, ← cls_pull hF _ (pull_isLB hF _)]
    exact (cls_eq_zero_iff (pull_isLB hF _)).symm
  have z₀ : CechPic.pull (e ≫ ψ) (cls F hF) = 0 := by
    have ee : e ≫ ψ = (lift (1 : Y ⟶ A) y).left := by
      simp only [e, ψ]
      rw [← Over.comp_left, comp_lift, lift_fst, lift_snd_assoc, Category.id_comp]
    rw [ee, hc, map_sub]
    have a := hN.add.evc_one hN.isLB y
    have b := hN'.add.evc_one hN'.isLB y
    simp only [evc] at a b
    rw [a, b, sub_zero]
  rw [TrivSubscheme.locTrivOver_iff (isPullback_lift A y), hs]
  constructor
  · intro h q
    exact ⟨⊤, trivial, (key _).2 (by rw [h, map_zero])⟩
  · intro h
    have cl : ∀ {Z : Scheme.{0}} (φ' : Fin 2 → (Z ⟶ (A ⊗ T).left)),
        Triv (LB.LinComb F φ' ![1, -1]) ↔
          CechPic.pull (φ' 0) (cls F hF) - CechPic.pull (φ' 1) (cls F hF) = 0 := fun φ' => by
      refine (cls_eq_zero_iff (LB.isLB_linComb hF _ _)).symm.trans ?_
      rw [cls_linComb hF, Fin.sum_univ_two]
      simp [sub_eq_add_neg]
    have sec : ∀ {Z : Scheme.{0}} (r : Z ⟶ (A ⊗ Y).left),
        CechPic.pull (r ≫ p ≫ e ≫ ψ) (cls F hF) = 0 := fun r => by
      rw [pull_comp, pull_comp, z₀, map_zero, map_zero]
    have T₀ : Triv (LB.LinComb F ![ψ, p ≫ e ≫ ψ] ![1, -1]) := by
      refine CubeGen.triv_of_local hF _ _ p e he (fun Z b U _ k => ?_) (fun V => ?_) (fun s => ?_)
      · have w : b ≫ e ≫ p ≫ e ≫ ψ = b ≫ e ≫ ψ := by
          rw [reassoc_of% he]
        simp [Fin.prod_univ_two, w]
      · let YV : Over S := Over.mk (V.ι ≫ Y.hom)
        let v : YV ⟶ Y := Over.homMk V.ι rfl
        exact ⟨_, _, (snd A YV).left, isPullback_lift A v, surj_snd hG hA YV⟩
      · obtain ⟨U, hU, ht⟩ := h s
        refine ⟨U, hU, ?_⟩
        unfold CubeGen.TrivAt
        rw [cl]
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
        rw [sec, sub_zero, pull_comp]
        exact (key _).1 ht
    have := (cl _).1 T₀
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at this
    have s₁ := sec (𝟙 _)
    rw [Category.id_comp] at s₁
    rwa [s₁, sub_zero] at this

theorem exists_closed_same : ∀ (S : Scheme.{0}) (A T : Over S) [GrpObj A] [IsLocallyNoetherian T.left],
    IsAbelianScheme A → ∀ (N N' : LB (A ⊗ T).left), Fam A N → Fam A N' → ∃ (G : Over S) (i : G ⟶ T),
      IsClosedImmersion i.left ∧ ∀ (Y : Over S) (y : Y ⟶ T), Same A N N' y y ↔ ∃ z : Y ⟶ G, z ≫ i = y := by
  intro S A T _ _ hA N N' hN hN'
  obtain ⟨F, hF, hc⟩ := cls_surj (cls N hN.isLB - cls N' hN'.isLB)
  obtain ⟨G, i, hi, hG⟩ := exists_closed_locTriv_noeth A ExpansionTotal.globalFns hA F hF
  exact ⟨G, i, hi, fun Y y => (same_iff_locTriv ExpansionTotal.globalFns hA hN hN' hF hc Y y).trans (hG Y y)⟩

end GlobalTheory.DualLocus
