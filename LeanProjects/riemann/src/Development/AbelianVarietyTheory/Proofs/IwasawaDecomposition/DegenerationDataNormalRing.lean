import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSiegPull
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LineBundleIsoOfGenericIsoNormalLocalBaseStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.AdjointEndomorphismsCubeLBOfDenseFibres
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAbelianSchemeOfIsGrpPullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.SiegLoc GlobalTheory.LN GlobalTheory
open scoped CategoryTheory.Obj

noncomputable section

open MonoidalCategory CartesianMonoidalCategory MonObj

namespace GlobalTheory.UnifLamFibre

open GlobalTheory.CechPic

theorem lam_congr {S X : Scheme.{0}} {G : Over S} [GrpObj G] {a b : X ⟶ S} (h : a = b) (c : Pic G.left)
    (x y : Over.mk a ⟶ G) (x' y' : Over.mk b ⟶ G) (hx : x.left = x'.left) (hy : y.left = y'.left) :
    lam c x y = lam c x' y' := by
  subst h
  obtain rfl : x = x' := Over.OverMorphism.ext hx
  obtain rfl : y = y' := Over.OverMorphism.ext hy
  rfl

theorem isSquare_unique {S S' : Scheme.{0}} {G' : Over S'} {G : Over S} {φ : G'.left ⟶ G.left}
    {a b : (G' ⊗ G').left ⟶ (G ⊗ G).left} (ha : IsSquare φ a) (hb : IsSquare φ b) : a = b :=
  (IsPullback.of_hasPullback G.hom G.hom).hom_ext (ha.1.trans hb.1.symm) (ha.2.trans hb.2.symm)

theorem exists_factor_atPrime {R K : Type} [CommRing R] [Field K] (x : Sp K ⟶ Sp R) (P : Ideal R) [P.IsPrime]
    (hP : (x (closedPoint K)).asIdeal = P) :
    ∃ xp : Sp K ⟶ Sp (Localization.AtPrime P), xp ≫ spMap (algebraMap R (Localization.AtPrime P)) = x := by
  obtain ⟨f, rfl⟩ := Spec.map_surjective x
  have hP' : ∀ s : R, s ∈ P ↔ f.hom s = 0 := fun s => by
    rw [← hP]
    show f.hom s ∈ IsLocalRing.maximalIdeal K ↔ _
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_iff_ne_zero, not_not]
  let l := IsLocalization.lift (M := P.primeCompl) (S := Localization.AtPrime P) (g := f.hom) fun s =>
      isUnit_iff_ne_zero.2 fun h0 => s.2 ((hP' s).2 h0)
  refine ⟨Spec.map (CommRingCat.ofHom l), ?_⟩
  rw [← Spec.map_comp]
  congr 1
  ext r
  exact IsLocalization.lift_eq _ r

theorem exists_factor_open {R : Type} [CommRing R] (P : Ideal R) [P.IsPrime] {S Z : Scheme.{0}} (ξ : Sp R ⟶ S)
    (j : Z ⟶ S) [IsOpenImmersion j] (h : ξ ⟨P, inferInstance⟩ ∈ Set.range j) :
    ∃ yp : Sp (Localization.AtPrime P) ⟶ Z, yp ≫ j = spMap (algebraMap R (Localization.AtPrime P)) ≫ ξ := by
  refine ⟨IsOpenImmersion.lift j _ ?_, IsOpenImmersion.lift_fac _ _ _⟩
  rintro _ ⟨q, rfl⟩
  have hq : (spMap (algebraMap R (Localization.AtPrime P)) q) ⤳ (⟨P, inferInstance⟩ : Sp R) := by
    show (PrimeSpectrum.comap (algebraMap R (Localization.AtPrime P)) q) ⤳ (⟨P, inferInstance⟩ : PrimeSpectrum R)
    rw [← PrimeSpectrum.le_iff_specializes]
    show Ideal.comap _ q.asIdeal ≤ P
    exact (Ideal.comap_mono (IsLocalRing.le_maximalIdeal q.isPrime.ne_top)).trans
      (IsLocalization.AtPrime.comap_maximalIdeal (Localization.AtPrime P) P).le
  exact (hq.map (ξ.base.hom.continuous)).mem_open j.isOpenEmbedding.isOpen_range h

attribute [-instance] instAlgebraAtPrimeFractionRing in

theorem exists_generic_factor {R : Type} [CommRing R] [IsDomain R] (P : Ideal R) [P.IsPrime] :
    ∃ κ : Sp (FractionRing (Localization.AtPrime P)) ⟶ Sp (FractionRing R),
      jK (Localization.AtPrime P) ≫ spMap (algebraMap R (Localization.AtPrime P)) = κ ≫ jK R := by
  have hinj : Function.Injective (algebraMap R (Localization.AtPrime P)) :=
    IsLocalization.injective _ P.primeCompl_le_nonZeroDivisors
  refine ⟨spMap (IsLocalization.map (M := nonZeroDivisors R) (T := nonZeroDivisors (Localization.AtPrime P)) _
    (algebraMap R (Localization.AtPrime P)) (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ hinj)), ?_⟩
  simp only [spMap, jK, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext r
  rw [RingHom.comp_apply, RingHom.comp_apply, IsLocalization.map_eq]

theorem square_ext {S Z : Scheme.{0}} {G : Over S} {a b : Z ⟶ (G ⊗ G).left} (h₁ : a ≫ (fst G G).left = b ≫ (fst G G).left)
    (h₂ : a ≫ (snd G G).left = b ≫ (snd G G).left) : a = b :=
  (IsPullback.of_hasPullback G.hom G.hom).hom_ext h₁ h₂

theorem generic_eq {R Rp : Type} [CommRing R] [CommRing Rp]
    (loc : Sp Rp ⟶ Sp R) (κ : Sp (FractionRing Rp) ⟶ Sp (FractionRing R)) (hι : jK Rp ≫ loc = κ ≫ jK R)
    {G' : Over (Sp R)} [GrpObj G'] {Gp : Over (Sp Rp)} [GrpObj Gp] {βp : Gp.left ⟶ G'.left}
    (hβp : IsGrpPullback Gp G' loc βp)
    {A : Over (Sp (FractionRing R))} [GrpObj A] (gen : (Over.pullback (jK R)).obj G' ≅ A) [IsMonHom gen.hom]
    {X S : Scheme.{0}} {Fu : Over X} {Gu : Over S} (e : Fu.left ⟶ Gu.left) [Mono e] (π : G'.left ⟶ Gu.left)
    (α0 : A.left ⟶ Fu.left) (α0₂ : (G2 A).left ⟶ (G2 Fu).left) (hsq0 : IsSquare α0 α0₂)
    (hgen : gen.hom.left ≫ α0 ≫ e = pullback.fst G'.hom (jK R) ≫ π)
    (αp : Gp.left ⟶ Fu.left) (αp₂ : (G2 Gp).left ⟶ (G2 Fu).left) (hsqp : IsSquare αp αp₂) (hαp : αp ≫ e = βp ≫ π)
    (cL : Pic G'.left) (cA : Pic A.left) (cP : Pic (G2 Fu).left)
    (hext : pull gen.hom.left cA = pull (pullback.fst G'.hom (jK R)) cL)
    (hΛ : lam cA (fst A A) (snd A A) = pull α0₂ cP) :
    pull (pullback.fst (G2 Gp).hom (jK Rp)) (lam (pull βp cL) (fst Gp Gp) (snd Gp Gp)) =
      pull (pullback.fst (G2 Gp).hom (jK Rp)) (pull αp₂ cP) := by
  let T : Over (Sp Rp) := Over.mk (pullback.fst (G2 Gp).hom (jK Rp) ≫ (G2 Gp).hom)
  let Fm : T ⟶ G2 Gp := Over.homMk (pullback.fst (G2 Gp).hom (jK Rp)) rfl
  change pull Fm.left _ = pull Fm.left _
  rw [pull_lam, ← pull_comp, lam_pull_of_isGrpPullback hβp]
  let t := pullback.snd (G2 Gp).hom (jK Rp) ≫ κ
  have ht : T.hom ≫ loc = t ≫ jK R := by
    simp only [T, t, Over.mk_hom, Category.assoc, ← hι]
    rw [pullback.condition_assoc]
  have hK := isGrpPullback_pullback G' (jK R)
  have hw : ∀ u : T ⟶ Gp, (u.left ≫ βp) ≫ G'.hom = t ≫ jK R := fun u => by
    rw [Category.assoc, hβp.1.w, ← Category.assoc, Over.w u, ht]
  let v : (T ⟶ Gp) → (Over.mk t ⟶ (Over.pullback (jK R)).obj G') := fun u =>
    Over.homMk (pullback.lift (u.left ≫ βp) t (hw u)) (pullback.lift_snd _ _ _)
  have hv : ∀ u, (v u).left ≫ pullback.fst G'.hom (jK R) = u.left ≫ βp := fun u => pullback.lift_fst _ _ _
  have e₁ : lam cL (pushHom hβp T (Fm ≫ fst Gp Gp)) (pushHom hβp T (Fm ≫ snd Gp Gp)) =
      lam cL (pushHom hK _ (v (Fm ≫ fst Gp Gp))) (pushHom hK _ (v (Fm ≫ snd Gp Gp))) :=
    lam_congr ht _ _ _ _ _ (hv _).symm (hv _).symm
  rw [e₁, ← lam_pull_of_isGrpPullback hK, ← hext, lam_pull gen.hom]
  set w₁ := v (Fm ≫ fst Gp Gp) ≫ gen.hom
  set w₂ := v (Fm ≫ snd Gp Gp) ≫ gen.hom
  have e₂ : lam cA w₁ w₂ = pull (lift w₁ w₂).left (lam cA (fst A A) (snd A A)) := by
    rw [pull_lam, lift_fst, lift_snd]
  rw [e₂, hΛ, ← pull_comp]
  have key : ∀ u : T ⟶ Gp, (v u ≫ gen.hom).left ≫ α0 = u.left ≫ αp := fun u => by
    rw [← cancel_mono e]
    simp only [Over.comp_left, Category.assoc, hgen, hαp]
    rw [reassoc_of% (hv u)]
  refine congrArg (fun m => pull m cP) (square_ext ?_ ?_)
  · rw [Category.assoc, Category.assoc, hsq0.1, hsqp.1, ← Category.assoc, ← Category.assoc, ← Over.comp_left,
      ← Over.comp_left, lift_fst, key]
  · rw [Category.assoc, Category.assoc, hsq0.2, hsqp.2, ← Category.assoc, ← Category.assoc, ← Over.comp_left,
      ← Over.comp_left, lift_snd, key]

theorem lam_pull_eq_univ : ∀ (o : Type) [CommRing o] (ζ : o) (g n : ℕ) (F : SFam g n ζ) (S : Scheme.{0}) (j : F.X ⟶ S) [IsOpenImmersion j] (G : Over S) [GrpObj G] (e : F.univ.A.left ⟶ G.left), IsGrpPullback F.univ.A G j e → ∀ (R : Type) [CommRing R] [IsDomain R], IsNoetherianRing R → IsIntegrallyClosed R → ∀ (I : Ideal R) (ξ : Sp R ⟶ S) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'] (π : G'.left ⟶ G.left) (D : DegData R I) (A : PolAV (Sp (FractionRing R))) (U : Unif I D A G'), IsUnifOf F j e ξ π U → ∀ (K : Type) [Field K] (x : Sp K ⟶ Sp R) (y : Sp K ⟶ F.X) (B : Over (Sp K)) [GrpObj B] (β : B.left ⟶ G'.left) (α : B.left ⟶ F.univ.A.left) (α₂ : (G2 B).left ⟶ (G2 F.univ.A).left), y ≫ j = x ≫ ξ → IsGrpPullback B G' x β → IsGrpPullback B F.univ.A y α → α ≫ e = β ≫ π → IsSquare α α₂ → LBIso (abelian₂ B (U.LG.L.pull β)) (F.univ.P.pull α₂) := by
  intro o _ ζ g n F S j _ G _ e he R _ _ hRn hRi I ξ G' _ _ π D A U hU K _ x y B _ β α α₂ hyx hβ hα hαβ hα₂
  obtain ⟨hπ, y0, α0, α0₂, hy0, hα0, hsq0, hΛ0, hgen0⟩ := hU
  haveI := hRn
  haveI := hRi
  obtain ⟨P, hP⟩ : ∃ P : Ideal R, (x (closedPoint K)).asIdeal = P := ⟨_, rfl⟩
  haveI : P.IsPrime := hP ▸ (x (closedPoint K)).isPrime
  haveI : IsIntegrallyClosed (Localization.AtPrime P) :=
    isIntegrallyClosed_of_isLocalization _ P.primeCompl P.primeCompl_le_nonZeroDivisors
  obtain ⟨xp, hxp⟩ := exists_factor_atPrime x P hP
  have hxP : (x (closedPoint K) : Sp R) = ⟨P, inferInstance⟩ := PrimeSpectrum.ext hP
  obtain ⟨yp, hyp⟩ := exists_factor_open P ξ j ⟨y (closedPoint K), by
    rw [← hxP]; exact congrArg (fun f : Sp K ⟶ S => f (closedPoint K)) hyx⟩
  set loc := spMap (algebraMap R (Localization.AtPrime P))
  let Gp := (Over.pullback loc).obj G'
  have hβp : IsGrpPullback Gp G' loc (pullback.fst G'.hom loc) := isGrpPullback_pullback G' loc
  set βp := pullback.fst G'.hom loc
  have hc : (βp ≫ π) ≫ G.hom = (Gp.hom ≫ yp) ≫ j := by
    rw [Category.assoc, hπ.1.w, ← Category.assoc, hβp.1.w, Category.assoc, Category.assoc, hyp]
  let αp : Gp.left ⟶ F.univ.A.left := he.1.lift (βp ≫ π) (Gp.hom ≫ yp) hc
  have hαpe : αp ≫ e = βp ≫ π := he.1.lift_fst _ _ _
  have hαpw : αp ≫ F.univ.A.hom = Gp.hom ≫ yp := he.1.lift_snd _ _ _
  have hαp : IsGrpPullback Gp F.univ.A yp αp :=
    IsGrpPullback.cancel he (by rw [hyp, hαpe]; exact hβp.comp hπ) hαpw
  haveI hab : IsAbelianScheme Gp := PolPull.isAbelianScheme_of_isGrpPullback F.univ.ab hαp
  haveI := hab.smooth
  haveI := hab.geomConnected
  haveI := hab.proper
  haveI : IsOpenImmersion e := MorphismProperty.of_isPullback (P := @IsOpenImmersion) he.1.flip inferInstance
  let αp₂ : (G2 Gp).left ⟶ (G2 F.univ.A).left :=
    (IsPullback.of_hasPullback F.univ.A.hom F.univ.A.hom).lift ((fst Gp Gp).left ≫ αp) ((snd Gp Gp).left ≫ αp) (by
      rw [Category.assoc, Category.assoc, hαpw, ← Category.assoc, ← Category.assoc, Over.w (fst Gp Gp),
        Over.w (snd Gp Gp)])
  have hsqp : IsSquare αp αp₂ :=
    ⟨(IsPullback.of_hasPullback F.univ.A.hom F.univ.A.hom).lift_fst _ _ _,
      (IsPullback.of_hasPullback F.univ.A.hom F.univ.A.hom).lift_snd _ _ _⟩
  have hL := U.LG.isLB
  have hLp := pull_isLB hL βp
  have h₁ : (abelian₂ Gp (U.LG.L.pull βp)).IsLB := LB.isLB_linComb hLp _ _
  have h₂ : (F.univ.P.pull αp₂).IsLB := pull_isLB F.univ.isLB _
  have c₁ : cls _ h₁ = lam (CechPic.pull βp (cls _ hL)) (fst Gp Gp) (snd Gp Gp) := by
    rw [← cls_pull hL βp hLp]; exact cls_cube_two hLp _ _ h₁
  have hsm : Smooth (G2 Gp).hom := smooth_square_hom Gp
  have hqc : QuasiCompact (G2 Gp).hom := by
    rw [← Over.w (fst Gp Gp)]
    show QuasiCompact (pullback.fst Gp.hom Gp.hom ≫ Gp.hom)
    infer_instance
  have hgi : GeometricallyIntegral (G2 Gp).hom := geometricallyIntegral_square_hom Gp
  have key : LBIso (abelian₂ Gp (U.LG.L.pull βp)) (F.univ.P.pull αp₂) := by
    refine GlobalTheory.T.lineBundleIso_of_generic_iso_normal_local_base (Localization.AtPrime P) inferInstance inferInstance (G2 Gp).left (G2 Gp).hom
      η[G2 Gp].left hsm hqc hgi (Over.w η[G2 Gp]) _ _ h₁ h₂ ?_
    refine (cls_eq_iff (pull_isLB h₁ _) (pull_isLB h₂ _)).1 ?_
    rw [cls_pull h₁, cls_pull h₂, c₁, cls_pull F.univ.isLB]
    obtain ⟨κ, hι⟩ := exists_generic_factor P
    have hA := A.isLB
    have hext : CechPic.pull U.gen.hom.left (cls _ hA) = CechPic.pull (pullback.fst G'.hom (jK R)) (cls _ hL) := by
      have := (cls_eq_iff (pull_isLB hA U.gen.hom.left) (pull_isLB hL (pullback.fst G'.hom (jK R)))).2 U.ext
      rwa [cls_pull hA, cls_pull hL] at this
    have hΛ : lam (cls _ hA) (fst A.A A.A) (snd A.A A.A) = CechPic.pull α0₂ (cls _ F.univ.isLB) := by
      have hl : (abelian₂ A.A A.L).IsLB := LB.isLB_linComb hA _ _
      have := (cls_eq_iff hl (pull_isLB F.univ.isLB α0₂)).2 hΛ0
      rw [cls_pull F.univ.isLB] at this
      exact (cls_cube_two hA _ _ hl).symm.trans this
    haveI := U.gen_hom
    exact generic_eq loc κ hι hβp U.gen e π α0 α0₂ hsq0 hgen0 αp αp₂ hsqp hαpe _ _ _ hext hΛ
  have hw₀ : β ≫ G'.hom = (B.hom ≫ xp) ≫ loc := by rw [hβ.1.w, Category.assoc, hxp]
  let δ : B.left ⟶ Gp.left := pullback.lift β (B.hom ≫ xp) hw₀
  have hδβ : δ ≫ βp = β := pullback.lift_fst _ _ _
  have hδw : δ ≫ Gp.hom = B.hom ≫ xp := pullback.lift_snd _ _ _
  have hδ : IsGrpPullback B Gp xp δ := IsGrpPullback.cancel hβp (by rw [hδβ, hxp]; exact hβ) hδw
  have hαδ : δ ≫ αp = α := by
    rw [← cancel_mono e, Category.assoc, hαpe, reassoc_of% hδβ, hαβ]
  let Q : Over.mk ((G2 B).hom ≫ xp) ⟶ G2 Gp := lift (pushHom hδ _ (fst B B)) (pushHom hδ _ (snd B B))
  have hQ : Q.left ≫ αp₂ = α₂ := by
    refine isSquare_unique (φ := α) ⟨?_, ?_⟩ hα₂
    · rw [Category.assoc, hsqp.1, ← Category.assoc, ← Over.comp_left, lift_fst]
      show ((fst B B).left ≫ δ) ≫ αp = _
      rw [Category.assoc, hαδ]
    · rw [Category.assoc, hsqp.2, ← Category.assoc, ← Over.comp_left, lift_snd]
      show ((snd B B).left ≫ δ) ≫ αp = _
      rw [Category.assoc, hαδ]
  have hLβ := pull_isLB hL β
  have hB₁ : (abelian₂ B (U.LG.L.pull β)).IsLB := LB.isLB_linComb hLβ _ _
  have c₂ : cls _ hB₁ = lam (CechPic.pull β (cls _ hL)) (fst B B) (snd B B) := by
    rw [← cls_pull hL β hLβ]; exact cls_cube_two hLβ _ _ hB₁
  have k := (cls_eq_iff h₁ h₂).2 key
  rw [c₁, cls_pull F.univ.isLB] at k
  refine (cls_eq_iff hB₁ (pull_isLB F.univ.isLB α₂)).1 ?_
  rw [c₂, cls_pull F.univ.isLB, ← hδβ, pull_comp, lam_pull_of_isGrpPullback hδ]
  have e₃ : lam (CechPic.pull βp (cls _ hL)) (pushHom hδ _ (fst B B)) (pushHom hδ _ (snd B B)) =
      CechPic.pull Q.left (lam (CechPic.pull βp (cls _ hL)) (fst Gp Gp) (snd Gp Gp)) := by
    rw [pull_lam, lift_fst, lift_snd]
  rw [e₃, k, ← pull_comp, hQ]

end GlobalTheory.UnifLamFibre
