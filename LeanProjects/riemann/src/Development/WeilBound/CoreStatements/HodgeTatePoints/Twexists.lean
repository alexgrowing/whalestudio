import Mathlib
import Development.AutomorphicSpectrum.Statements.GeometryStatements.IsPolLatticePlane
import Development.AutomorphicSpectrum.Statements.GeometryStatements.HTChartExists
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionEmbeddingGeometricPoints
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PowFlatLocallyQuasiFinite
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FormallyUnramifiedMulInvertibleInteger

noncomputable section

namespace PositivityTheory.HtPt.Twexists

section General
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT GlobalTheory.CompanionTheory.Ar.BT.Tors ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj

section Props
variable {Z : Scheme.{0}} {A B : Over Z} [GrpObj B] [IsCommMonObj B] {N : ℕ} {j : A ⟶ B}

theorem kernel_isPullback (hp : IsPullback j (toUnit A) ((𝟙 B) ^ N) η[B]) :
    IsPullback j.left A.hom ((𝟙 B) ^ N).left (η[B]).left := by
  have h := hp.map (Over.forget Z)
  simpa using h

theorem kernel_props' (hp : IsPullback j (toUnit A) ((𝟙 B) ^ N) η[B])
    [Flat ((𝟙 B) ^ N).left] [LocallyQuasiFinite ((𝟙 B) ^ N).left] [LocallyOfFinitePresentation ((𝟙 B) ^ N).left]
    [IsSeparated B.hom] [QuasiCompact B.hom] :
    Flat A.hom ∧ LocallyQuasiFinite A.hom ∧ IsSeparated A.hom ∧ QuasiCompact A.hom ∧
      LocallyOfFinitePresentation A.hom := by
  have h1 := kernel_isPullback hp
  haveI : IsSeparated (((𝟙 B) ^ N).left ≫ B.hom) := by rw [Over.w]; infer_instance
  haveI : QuasiCompact (((𝟙 B) ^ N).left ≫ B.hom) := by rw [Over.w]; infer_instance
  haveI : IsSeparated ((𝟙 B) ^ N).left := IsSeparated.of_comp _ B.hom
  haveI : QuasiCompact ((𝟙 B) ^ N).left := QuasiCompact.of_comp _ B.hom
  exact ⟨MorphismProperty.of_isPullback (P := @Flat) h1 inferInstance,
    MorphismProperty.of_isPullback (P := @LocallyQuasiFinite) h1 inferInstance,
    MorphismProperty.of_isPullback (P := @IsSeparated) h1 inferInstance,
    MorphismProperty.of_isPullback (P := @QuasiCompact) h1 inferInstance,
    MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation) h1 inferInstance⟩

theorem kernel_base_etale' {W : Scheme.{0}} (c : W ⟶ Z) (hp : IsPullback j (toUnit A) ((𝟙 B) ^ N) η[B])
    (hN : IsUnit (N : Γ(W, ⊤))) [Flat A.hom] [LocallyOfFinitePresentation A.hom] :
    Etale (pullback.snd A.hom c) := by
  have h1 := kernel_isPullback hp
  set m := ((𝟙 B) ^ N).left with hm
  set mW := ((Over.pullback c).map ((𝟙 B) ^ N)).left with hmW
  have hfu : FormallyUnramified mW := by
    rw [hmW, ← GlobalTheory.MulEtaleDvr.mulN_eq_pow, GlobalTheory.MulEtaleDvr.pullback_map_mulN]
    exact GlobalTheory.formallyUnramified_mulN _ _ _ hN
  have hr := GlobalTheory.AbLaw.MulN.isPullback_baseChange c ((𝟙 B) ^ N)
  have hpb := IsPullback.of_hasPullback A.hom c
  have hbig : IsPullback (pullback.fst A.hom c ≫ j.left) (pullback.snd A.hom c) m (c ≫ (η[B]).left) :=
    IsPullback.paste_horiz hpb h1
  let s : W ⟶ pullback B.hom c := pullback.lift (c ≫ (η[B]).left) (𝟙 W) (by
    rw [Category.assoc, Over.w (η[B])]
    simp)
  let t : pullback A.hom c ⟶ pullback B.hom c := pullback.lift (pullback.fst A.hom c ≫ j.left) (pullback.snd A.hom c) (by
    rw [Category.assoc, Over.w j, pullback.condition])
  have ht1 : t ≫ pullback.fst B.hom c = pullback.fst A.hom c ≫ j.left := pullback.lift_fst _ _ _
  have hs1 : s ≫ pullback.fst B.hom c = c ≫ (η[B]).left := pullback.lift_fst _ _ _
  have ht2 : t ≫ pullback.snd B.hom c = pullback.snd A.hom c := pullback.lift_snd _ _ _
  have hs2 : s ≫ pullback.snd B.hom c = 𝟙 W := pullback.lift_snd _ _ _
  have hw : mW ≫ pullback.snd B.hom c = pullback.snd B.hom c :=
    Over.w ((Over.pullback c).map ((𝟙 B) ^ N))
  have hsq : t ≫ mW = pullback.snd A.hom c ≫ s := by
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, hs1, ← hr.w, ← Category.assoc, ht1, Category.assoc, h1.w,
        ← Category.assoc, pullback.condition, Category.assoc]
    · rw [Category.assoc, Category.assoc, hw, ht2, hs2, Category.comp_id]
  have hleft : IsPullback t (pullback.snd A.hom c) mW s := by
    apply IsPullback.of_right _ hsq hr
    rw [ht1, hs1]
    exact hbig
  have hU : FormallyUnramified (pullback.snd A.hom c) :=
    MorphismProperty.of_isPullback (P := @FormallyUnramified) hleft hfu
  have hF : Flat (pullback.snd A.hom c) := MorphismProperty.of_isPullback (P := @Flat) hpb inferInstance
  have hL : LocallyOfFinitePresentation (pullback.snd A.hom c) :=
    MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation) hpb inferInstance
  exact Etale.iff_flat_and_formallyUnramified.2 ⟨hF, hU, hL⟩

end Props

theorem lofp_pullback_map {S' S : Scheme.{0}} [IsLocallyNoetherian S] (x : S' ⟶ S) {G : Over S}
    [LocallyOfFiniteType G.hom] (u : G ⟶ G) : LocallyOfFinitePresentation ((Over.pullback x).map u).left := by
  haveI : LocallyOfFiniteType (u.left ≫ G.hom) := by rw [Over.w]; infer_instance
  haveI : LocallyOfFiniteType u.left := locallyOfFiniteType_of_comp u.left G.hom
  haveI : IsLocallyNoetherian G.left := LocallyOfFiniteType.isLocallyNoetherian G.hom
  have hu : LocallyOfFinitePresentation u.left := lofp_of_noeth u.left
  exact MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation)
    (GlobalTheory.AbLaw.MulN.isPullback_baseChange x u) hu

theorem exists_genPt {R : Type} [CommRing R] [IsDomain R] [IsAlgClosed (FractionRing R)]
    (A : Over (Spec (CommRingCat.of R))) [LocallyQuasiFinite A.hom] [LocallyOfFiniteType A.hom] (g : A.left)
    (hg : (A.hom g).asIdeal = ⊥) :
    ∃ (c : genPt R ⟶ A) (u : Spec (CommRingCat.of (FractionRing R))), c.left u = g := by
  obtain ⟨Ω, _, _, a, c, hc, hcg⟩ := exists_geom_point A.hom g hg
  letI : Algebra (FractionRing R) Ω := a.toAlgebra
  haveI : IsIntegrallyClosedIn (FractionRing R) Ω := isIntegrallyClosedIn_iff.2
    ⟨(algebraMap (FractionRing R) Ω).injective, fun {x} hx =>
      minpoly.mem_range_of_degree_eq_one _ x (IsAlgClosed.degree_eq_one_of_irreducible _ (minpoly.irreducible hx))⟩
  have hpb := IsPullback.of_hasPullback A.hom (genPt R).hom
  haveI : LocallyQuasiFinite (pullback.snd A.hom (genPt R).hom) :=
    MorphismProperty.of_isPullback (P := @LocallyQuasiFinite) hpb inferInstance
  let x : Spec (CommRingCat.of Ω) ⟶ pullback A.hom (genPt R).hom :=
    pullback.lift c (Spec.map (CommRingCat.ofHom a)) hc
  obtain ⟨x₀, hx₀, hf₀, -⟩ := GlobalTheory.OnePoint.exists_section_of_locallyQuasiFinite
    (pullback.snd A.hom (genPt R).hom) Ω x (pullback.lift_snd _ _ _)
  have hx₀' : Spec.map (CommRingCat.ofHom a) ≫ x₀ = x := hx₀
  let c' : genPt R ⟶ A := Over.homMk (x₀ ≫ pullback.fst A.hom (genPt R).hom) (by
    rw [Category.assoc, pullback.condition, ← Category.assoc, hf₀]
    simp)
  let u0 : Spec (CommRingCat.of Ω) := IsLocalRing.closedPoint Ω
  refine ⟨c', Spec.map (CommRingCat.ofHom a) u0, ?_⟩
  have key : (Spec.map (CommRingCat.ofHom a) ≫ x₀ ≫ pullback.fst A.hom (genPt R).hom) u0 = g := by
    rw [← Category.assoc, hx₀', pullback.lift_fst]
    exact hcg u0
  simpa [c'] using key

section Main
variable {R : Type} [CommRing R] [IsDomain R] {T : Type} [CommGroup T]
  {S : Scheme.{0}} {G : Over S} {x : Spec (CommRingCat.of R) ⟶ S} {N : ℕ}

theorem isUnit_natCast_frac [CharZero R] (hN : N ≠ 0) :
    IsUnit (N : Γ(Spec (CommRingCat.of (FractionRing R)), ⊤)) := by
  have h1 : (N : FractionRing R) ≠ 0 := by
    rw [← map_natCast (algebraMap R (FractionRing R))]
    intro h
    exact hN (Nat.cast_eq_zero.mp ((IsFractionRing.injective R (FractionRing R)) (h.trans (map_zero _).symm)))
  have h2 := (IsUnit.mk0 _ h1).map (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv.hom
  simpa using h2

theorem qfGroup_of_kernel [GrpObj G] [IsCommMonObj G]
    {A : Over (Spec (CommRingCat.of R))} [GrpObj A] [IsCommMonObj A]
    {j : A ⟶ (Over.pullback x).obj G} [IsMonHom j]
    (hp : IsPullback j (toUnit A) ((𝟙 ((Over.pullback x).obj G)) ^ N) η[(Over.pullback x).obj G])
    (hflat : Flat A.hom) (hqf : LocallyQuasiFinite A.hom) (hsep : IsSeparated A.hom) (hqc : QuasiCompact A.hom)
    (hfp : LocallyOfFinitePresentation A.hom) (hred : IsReduced (pullback A.hom (genPt R).hom))
    (τ : T →* (Over.mk ((genPt R).hom ≫ x) ⟶ G)) (hinj : Function.Injective τ) (hτ : ∀ t, τ t ^ N = 1)
    (hpt : ∀ g : A.left, (A.hom g).asIdeal = ⊥ → ∃ (c : genPt R ⟶ A) (u : Spec (CommRingCat.of (FractionRing R))),
      c.left u = g)
    (hsurj : ∀ g : Over.mk ((genPt R).hom ≫ x) ⟶ G, g ^ N = 1 → ∃ t, g = τ t) :
    ∃ (Γ : QFGroup R T) (i : Γ.G.left ⟶ G.left), Γ.IsTorsionAlong G x N i ∧ ∀ t, (Γ.pt t).left ≫ i = (τ t).left := by
  classical
  haveI hmono : Mono j := mono_of_pullback hp
  have hi : ∀ {Y : Over (Spec (CommRingCat.of R))} (y : Y ⟶ A) (g : Over.mk (Y.hom ≫ x) ⟶ G),
      y ≫ j = toPull x G g → y.left ≫ j.left ≫ pullback.fst G.hom x = g.left := by
    intro Y y g h
    rw [← toPull_fst x G g, ← h]
    simp
  have hi' : ∀ {Y : Over (Spec (CommRingCat.of R))} (y : Y ⟶ A) (g : Over.mk (Y.hom ≫ x) ⟶ G),
      y.left ≫ j.left ≫ pullback.fst G.hom x = g.left → y ≫ j = toPull x G g := by
    intro Y y g h
    apply hom_ext_pull
    rw [toPull_fst, ← h]
    simp
  have hP : ∀ {Y : Over (Spec (CommRingCat.of R))} (g : Over.mk (Y.hom ≫ x) ⟶ G),
      toPull x G g = toPullHom x G Y g := fun g => rfl
  have hlift : ∀ t, ∃ w : genPt R ⟶ A, w ≫ j = toPull x G (τ t) := fun t =>
    lift_of_torsion hp _ (by rw [hP, ← map_pow, hτ, map_one])
  choose z hz using hlift
  have hzu : ∀ t (w : genPt R ⟶ A), w ≫ j = toPull x G (τ t) → w = z t := fun t w hw => by
    rw [← hz t] at hw
    exact (cancel_mono j).1 hw
  let pt : T →* (genPt R ⟶ A) :=
    { toFun := z
      map_one' := (hzu 1 1 (by rw [hP, map_one, map_one]; simp)).symm
      map_mul' := fun s t => (hzu (s * t) (z s * z t)
        (by rw [MonObj.mul_comp, hz, hz, hP, hP, hP, map_mul, map_mul])).symm }
  let Γ : QFGroup R T :=
    { G := A
      grp := inferInstance
      comm := inferInstance
      flat := hflat
      quasiFinite := hqf
      separated := hsep
      quasiCompact := hqc
      finPres := hfp
      pt := pt
      pt_inj := by
        intro s t u v huv
        have h1 : (z s).left = (z t).left :=
          eq_of_same_point A.hom (z s).left (z t).left (Over.w (z s)) (Over.w (z t)) u v huv
        have h2 : z s = z t := Over.OverMorphism.ext h1
        have h3 : toPull x G (τ s) = toPull x G (τ t) := by rw [← hz s, ← hz t, h2]
        exact hinj (toPull_inj h3)
      pt_onto := by
        intro g hg
        obtain ⟨c, u, hcu⟩ := hpt g hg
        have htor : (ofPull x G (c ≫ j)) ^ N = 1 := by
          apply toPull_inj
          rw [hP, hP, map_pow, map_one, ← hP, toPull_ofPull]
          exact torsion_of_comp hp c
        obtain ⟨t, ht⟩ := hsurj _ htor
        have hct : c = z t := hzu t c (by rw [← ht, toPull_ofPull])
        exact ⟨t, u, by rw [← hcu, hct]; rfl⟩
      gen_reduced := hred }
  refine ⟨Γ, j.left ≫ pullback.fst G.hom x, ⟨?_, ?_, ?_, ?_⟩, fun t => hi (z t) (τ t) (hz t)⟩
  · show (j.left ≫ pullback.fst G.hom x) ≫ G.hom = A.hom ≫ x
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    congr 1
    exact Over.w j
  · intro Y y w y₀ w₀ hy hw
    have e1 := hi' y y₀ hy.symm
    have e2 := hi' w w₀ hw.symm
    have e3 : (y * w) ≫ j = toPull x G (y₀ * w₀) := by
      rw [MonObj.mul_comp, e1, e2, hP, hP, hP, map_mul]
    exact (hi (y * w) (y₀ * w₀) e3).symm
  · intro Y y w h
    apply (cancel_mono j).1
    apply hom_ext_pull
    simpa using h
  · intro Y g
    constructor
    · intro hg
      have htor : (toPull x G g) ^ N = 1 := by
        rw [hP, ← map_pow, hg, map_one]
      obtain ⟨y, hy⟩ := lift_of_torsion hp _ htor
      exact ⟨y, hi y g hy⟩
    · rintro ⟨y, hy⟩
      have e := hi' y g hy
      apply toPull_inj
      rw [hP, hP, map_pow, map_one, ← hP, ← e]
      exact torsion_of_comp hp y

theorem exists_qfGroup [CharZero R] [IsAlgClosed (FractionRing R)] [IsLocallyNoetherian S] [GrpObj G]
    (hG : IsSemiAbelian G) (hN : N ≠ 0)
    (τ : T →* (Over.mk ((genPt R).hom ≫ x) ⟶ G)) (hinj : Function.Injective τ) (hτ : ∀ t, τ t ^ N = 1)
    (hsurj : ∀ g : Over.mk ((genPt R).hom ≫ x) ⟶ G, g ^ N = 1 → ∃ t, g = τ t) :
    ∃ (Γ : QFGroup R T) (i : Γ.G.left ⟶ G.left), Γ.IsTorsionAlong G x N i ∧ ∀ t, (Γ.pt t).left ≫ i = (τ t).left := by
  haveI : IsCommMonObj G := hG.comm
  haveI : Smooth G.hom := hG.smooth
  haveI : IsSeparated G.hom := hG.separated
  haveI : QuasiCompact G.hom := hG.quasiCompact
  have heq : (Over.pullback x).map ((𝟙 G) ^ N) = (𝟙 ((Over.pullback x).obj G)) ^ N := by
    rw [← GlobalTheory.MulEtaleDvr.mulN_eq_pow, GlobalTheory.MulEtaleDvr.pullback_map_mulN, GlobalTheory.MulEtaleDvr.mulN_eq_pow]
  have hpb0 := IsPullback.of_hasPullback ((𝟙 ((Over.pullback x).obj G)) ^ N) (η[(Over.pullback x).obj G])
  have hp : IsPullback (pullback.fst ((𝟙 ((Over.pullback x).obj G)) ^ N) (η[(Over.pullback x).obj G]))
      (toUnit _) ((𝟙 ((Over.pullback x).obj G)) ^ N) η[(Over.pullback x).obj G] := by
    convert hpb0 using 1
    exact toUnit_unique _ _
  obtain ⟨_, _, _⟩ := exists_kernel_grp hp
  have hfl := GlobalTheory.SemiAbMulFlat.flat_and_locallyQuasiFinite_pow S G hG N hN
  have hbc := GlobalTheory.AbLaw.MulN.isPullback_baseChange x ((𝟙 G) ^ N)
  haveI : Flat ((𝟙 ((Over.pullback x).obj G)) ^ N).left := by
    rw [← heq]
    exact MorphismProperty.of_isPullback (P := @Flat) hbc hfl.1
  haveI : LocallyQuasiFinite ((𝟙 ((Over.pullback x).obj G)) ^ N).left := by
    rw [← heq]
    exact MorphismProperty.of_isPullback (P := @LocallyQuasiFinite) hbc hfl.2
  haveI : LocallyOfFinitePresentation ((𝟙 ((Over.pullback x).obj G)) ^ N).left := by
    rw [← heq]
    exact lofp_pullback_map x ((𝟙 G) ^ N)
  haveI : IsSeparated ((Over.pullback x).obj G).hom := by
    show IsSeparated (pullback.snd G.hom x)
    infer_instance
  haveI : QuasiCompact ((Over.pullback x).obj G).hom := by
    show QuasiCompact (pullback.snd G.hom x)
    infer_instance
  obtain ⟨hflat, hqf, hsep, hqc, hfp⟩ := kernel_props' hp
  haveI := hflat
  haveI := hqf
  haveI := hfp
  have hpt := fun g hg => exists_genPt (pullback ((𝟙 ((Over.pullback x).obj G)) ^ N) (η[(Over.pullback x).obj G])) g hg
  haveI := kernel_base_etale' (genPt R).hom hp (isUnit_natCast_frac hN)
  haveI : IsReduced (genPt R).left := by
    show IsReduced (Spec (CommRingCat.of (FractionRing R)))
    infer_instance
  have hred := GlobalTheory.isReduced_of_smooth_of_isReduced
    (pullback.snd (pullback ((𝟙 ((Over.pullback x).obj G)) ^ N) (η[(Over.pullback x).obj G])).hom (genPt R).hom)
  exact qfGroup_of_kernel hp hflat hqf hsep hqc hfp hred τ hinj hτ hpt hsurj

end Main

end General

section Level
open GlobalTheory.CompanionTheory.Ar.HT

theorem exists_levHom {La Q : Type} [AddCommGroup La] [Group Q] (p n : ℕ) (f : La → Q)
    (add : ∀ a b, f (a + b) = f a * f b) (ker : ∀ a, f a = 1 ↔ ∃ b, a = (p ^ n) • b) :
    ∃ τ : LevGrp La p n →* Q, Function.Injective τ ∧ ∀ a, τ (lev p n a) = f a := by
  let K := (p ^ n • (LinearMap.id : La →ₗ[ℤ] La)).range
  have key : ∀ a b : La, Submodule.Quotient.mk (p := K) a = Submodule.Quotient.mk b → f a = f b := by
    intro a b h
    rw [Submodule.Quotient.eq] at h
    obtain ⟨c, hc⟩ := h
    have h0 : f (a - b) = 1 := (ker _).2 ⟨c, by rw [← hc, LinearMap.smul_apply, LinearMap.id_apply]⟩
    calc f a = f ((a - b) + b) := by rw [sub_add_cancel]
      _ = f b := by rw [add, h0, one_mul]
  let g : La ⧸ K → Q := fun q => Quotient.liftOn' q f (fun a b h => key a b (Quotient.sound h))
  have hg : ∀ a, g (Submodule.Quotient.mk a) = f a := fun a => rfl
  have f0 : f 0 = 1 := (ker 0).2 ⟨0, by simp⟩
  let τ : LevGrp La p n →* Q :=
    { toFun := fun t => g (Multiplicative.toAdd t)
      map_one' := f0
      map_mul' := by
        intro x y
        obtain ⟨a, ha⟩ := Submodule.Quotient.mk_surjective K (Multiplicative.toAdd x)
        obtain ⟨b, hb⟩ := Submodule.Quotient.mk_surjective K (Multiplicative.toAdd y)
        have hx : x = Multiplicative.ofAdd (Submodule.Quotient.mk a) := by rw [ha]; rfl
        have hy : y = Multiplicative.ofAdd (Submodule.Quotient.mk b) := by rw [hb]; rfl
        subst hx hy
        show g (Submodule.Quotient.mk a + Submodule.Quotient.mk b) = g (Submodule.Quotient.mk a) * g (Submodule.Quotient.mk b)
        rw [← Submodule.Quotient.mk_add, hg, hg, hg, add] }
  refine ⟨τ, ?_, fun a => rfl⟩
  rw [injective_iff_map_eq_one]
  intro x hx
  obtain ⟨a, ha⟩ := Submodule.Quotient.mk_surjective K (Multiplicative.toAdd x)
  have hx' : x = Multiplicative.ofAdd (Submodule.Quotient.mk a) := by rw [ha]; rfl
  subst hx'
  have hfa : f a = 1 := hx
  obtain ⟨b, hb⟩ := (ker a).1 hfa
  have hz : Submodule.Quotient.mk (p := K) a = 0 :=
    (Submodule.Quotient.mk_eq_zero K).2 ⟨b, by rw [LinearMap.smul_apply, LinearMap.id_apply, hb]⟩
  rw [hz]
  rfl

theorem lev_surjective {La : Type} [AddCommGroup La] (p n : ℕ) (t : LevGrp La p n) : ∃ a, lev p n a = t := by
  obtain ⟨a, ha⟩ := Submodule.Quotient.mk_surjective _ (Multiplicative.toAdd t)
  exact ⟨a, by rw [lev, ha]; rfl⟩

end Level

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

set_option maxHeartbeats 800000 in

theorem tower_exists : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (S : Scheme.{0}) [IsLocallyNoetherian S] (t : SAB H S) (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [IsDomain O] [CharZero O] [IsAlgClosed (FractionRing O)] (y : Sp O ⟶ S) (I : TateIso D (FractionRing O) (Over.mk ((BT.genPt O).hom ≫ y) ⟶ t.G) (fun a g => g ≫ t.act.act a) (fun n g g' c => Out.WeilIs t.G t.PP.L n g g' (unitOn c))), ∃ X : TorsTower p t.G y D.La, (∀ n (a : D.La), ((X.Γ n).pt (lev p n a)).left ≫ X.i n = (I.ev (p ^ n) a).left) ∧ ∀ a : 𝓞 E, X.Induces (t.act.act a) (DistribMulAction.toAddMonoidHom D.La a) := by
  intro E _ _ _ H D S _ t p hp O _ _ _ _ y I
  have hp0 : ∀ n : ℕ, 0 < p ^ n := fun n => pow_pos hp.out.pos n
  have hev_pow : ∀ (N : ℕ), 0 < N → ∀ (k : ℕ) (a : D.La), I.ev N (k • a) = I.ev N a ^ k := by
    intro N hN k a
    induction k with
    | zero => rw [zero_smul, pow_zero]; exact (I.ker N hN 0).2 ⟨0, by rw [smul_zero]⟩
    | succ k ih => rw [succ_nsmul, I.add, ih, pow_succ]
  have hstep : ∀ n : ℕ, ∃ (Γ : QFGroup O (LevGrp D.La p n)) (i : Γ.G.left ⟶ t.G.left),
      Γ.IsTorsionAlong t.G y (p ^ n) i ∧ ∀ a, (Γ.pt (lev p n a)).left ≫ i = (I.ev (p ^ n) a).left := by
    intro n
    obtain ⟨τ, hinj, hτa⟩ := exists_levHom p n (I.ev (p ^ n)) (I.add _) (I.ker _ (hp0 n))
    have hτ : ∀ s, τ s ^ (p ^ n) = 1 := by
      intro s
      obtain ⟨a, rfl⟩ := lev_surjective p n s
      rw [hτa]
      exact (I.onto _ (hp0 n) _).2 ⟨a, rfl⟩
    have hsurj : ∀ g, g ^ (p ^ n) = 1 → ∃ s, g = τ s := by
      intro g hg
      obtain ⟨a, ha⟩ := (I.onto _ (hp0 n) g).1 hg
      exact ⟨lev p n a, by rw [hτa, ha]⟩
    obtain ⟨Γ, i, htor, hpt⟩ := exists_qfGroup t.semi (hp0 n).ne' τ hinj hτ hsurj
    exact ⟨Γ, i, htor, fun a => by rw [hpt, hτa]⟩
  choose Γ i htor hpt using hstep
  refine ⟨⟨Γ, i, htor, ?_⟩, fun n a => hpt n a, ?_⟩
  · intro n a
    rw [hpt, hpt, hev_pow _ (hp0 (n + 1)), pow_succ, I.tower _ _ (hp0 n) hp.out.pos]
  · intro a n b
    have e1 := hpt n ((DistribMulAction.toAddMonoidHom D.La a) b)
    have e2 := hpt n b
    have e3 : I.ev (p ^ n) ((DistribMulAction.toAddMonoidHom D.La a) b) = I.ev (p ^ n) b ≫ t.act.act a :=
      I.lin _ a b
    rw [e1, e3, Over.comp_left, ← e2, Category.assoc]

end PositivityTheory.HtPt.Twexists
