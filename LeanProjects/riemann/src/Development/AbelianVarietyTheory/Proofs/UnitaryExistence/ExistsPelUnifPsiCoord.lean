import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.BetaAtSymm
import Formalism.LocalToGlobal.ProjectiveLattices.OneLtAbsNormReal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigIsoCongr
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.DimSplitPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.QkToAkBaseChange
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsPullFOfGenRel
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationTripleLinearTorsionIso
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.PelCoordPull

theorem exists_gen_on {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (W : (Sp R).Opens)
    (hW : (W : Set (Sp R)).Nonempty) (χ : D.X) (H : PsiUnitOn D χ W) :
    ∃ t : LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => (toUnit (TW W) ≫ D.c χ).left) (fun _ => -1)), t.IsGen ∧
      LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ t (jK R ∣_ W)) (LB.pullGen D.P.L _ _ (D.psi χ) (jK R ⁻¹ᵁ W).ι) := by
  obtain ⟨z⟩ : Nonempty (TK R).left := inferInstanceAs (Nonempty (PrimeSpectrum (FractionRing R)))
  have dn := TauPull.jK_mem (R := R) z
  have inj := TauPull.gm_injective_of_dense (jK R) z dn
  let U : (PUnit → D.P.L.ι) → (Sp R).Opens := fun j =>
    W ⊓ LB.wchart D.P.L (Y := Sp R) (fun _ : PUnit => (D.c χ).left) j
  have glue : ∀ j : PUnit → D.P.L.ι, ∃ s : Γ(Sp R, U j)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ (TK R).left) (y : Z),
      jK R (r y) ∈ U j →
      gm (r ≫ jK R) y _ s = gm r y (LB.wchart D.P.L (fun _ : PUnit => D.xK χ) j) ((D.psi χ).s j) := by
    intro j
    have loc : ∀ V : {V : (Sp R).Opens // IsAffineOpen V ∧ V ≤ U j}, ∃ s : Γ(Sp R, V.1)ˣ,
        ∀ (Z : Scheme.{0}) (r : Z ⟶ (TK R).left) (y : Z), jK R (r y) ∈ V.1 →
        gm (r ≫ jK R) y _ s = gm r y (LB.wchart D.P.L (fun _ : PUnit => D.xK χ) j) ((D.psi χ).s j) := by
      rintro ⟨V, hV, hU⟩
      have h : jK R ⁻¹ᵁ V ≤ (LB.LinComb D.P.L (K := PUnit) (fun _ => D.xK χ) (fun _ => -1)).U j :=
        fun y hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 (hU hy).2 k
      obtain ⟨a, ha, e⟩ := H j V hV (fun y hy => (hU hy).1) (fun y hy => Set.mem_iInter.1 (hU hy).2 PUnit.unit) h
      refine ⟨ha.unit, fun Z r y hz => ?_⟩
      have e' : pullU (jK R) V ha.unit = res h ((D.psi χ).s j) := Units.ext e
      have p := gm_pull r (jK R) y V hz ha.unit
      rw [e'] at p
      exact p.symm.trans (gm_res r y h hz _)
    choose s hs using loc
    obtain ⟨a, ha⟩ := glue_unit (U j) (fun V : {V : (Sp R).Opens // IsAffineOpen V ∧ V ≤ U j} => V.1) (fun V => V.2.2)
      (fun y hy => by
        obtain ⟨_, ⟨V, hV, rfl⟩, hy', hle⟩ := (Sp R).isBasis_affineOpens.exists_subset_of_mem_open hy (U j).isOpen
        exact Opens.mem_iSup.2 ⟨⟨V, hV, hle⟩, hy'⟩) s (fun V V' y hy => by
        have hz : jK R z ∈ V.1 ⊓ V'.1 := dn _ ⟨y, hy⟩
        have k₁ := hs V _ (𝟙 _) z hz.1
        have k₂ := hs V' _ (𝟙 _) z hz.2
        rw [Category.id_comp] at k₁ k₂
        have : res (inf_le_left : V.1 ⊓ V'.1 ≤ _) (s V) = res inf_le_right (s V') := inj _ hz
          ((gm_res _ z _ hz _).trans (k₁.trans ((gm_res _ z _ hz _).trans k₂).symm))
        exact (gm_res _ y inf_le_left hy _).symm.trans ((congrArg (gm _ y _) this).trans (gm_res _ y _ hy _)))
    refine ⟨a, fun Z r y hz => ?_⟩
    obtain ⟨_, ⟨V, hV, rfl⟩, hy', hle⟩ := (Sp R).isBasis_affineOpens.exists_subset_of_mem_open hz (U j).isOpen
    exact (gm_res (r ≫ jK R) y hle hy' a).symm.trans
      ((congrArg (gm _ y _) (ha ⟨V, hV, hle⟩)).trans (hs ⟨V, hV, hle⟩ Z r y hy'))
  choose s hs using glue
  have hss : Subsingleton (TK R).left := inferInstanceAs (Subsingleton (PrimeSpectrum (FractionRing R)))
  obtain ⟨lam, hlam⟩ : ∃ lam : (TK R).left ⟶ W.toScheme, lam ≫ W.ι = jK R :=
    ⟨IsOpenImmersion.lift W.ι (jK R) (by
      rintro _ ⟨y, rfl⟩
      rw [Scheme.Opens.range_ι, Subsingleton.elim y z]
      exact dn _ hW), IsOpenImmersion.lift_fac _ _ _⟩
  have hz : W.ι (lam z) = jK R z := congrArg (fun q => q z) hlam
  have dn' : ∀ V : W.toScheme.Opens, (V : Set W.toScheme).Nonempty → lam z ∈ V := fun V ⟨y, hy⟩ => by
    obtain ⟨y', hy', e⟩ := dn (W.ι ''ᵁ V) ⟨_, y, hy, rfl⟩
    rwa [W.ι.isOpenEmbedding.injective (e.trans hz.symm)] at hy'
  have inj' := TauPull.gm_injective_of_dense lam z dn'
  have le : ∀ j, LB.wchart D.P.L (fun _ : PUnit => (toUnit (TW W) ≫ D.c χ).left) j ≤ W.ι ⁻¹ᵁ U j := fun j y hy =>
    ⟨y.2, Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k⟩
  have hv : ∀ j (Z : Scheme.{0}) (r : Z ⟶ (TK R).left) (y : Z),
      (r ≫ lam) y ∈ LB.wchart D.P.L (fun _ : PUnit => (toUnit (TW W) ≫ D.c χ).left) j →
      gm (r ≫ lam) y _ (res (le j) (pullU W.ι _ (s j))) =
        gm r y (LB.wchart D.P.L (fun _ : PUnit => D.xK χ) j) ((D.psi χ).s j) := fun j Z r y hy => by
    refine (gm_res _ y _ hy _).trans ((gm_pull (r ≫ lam) W.ι y (U j) (le j hy) _).trans ?_)
    rw [Category.assoc, hlam]
    exact hs j Z r y ((congrArg (fun q => q (r y) ∈ U j) hlam).mp (le j hy))
  have hc : lam ≫ (toUnit (TW W) ≫ D.c χ).left = D.xK χ := by
    show lam ≫ W.ι ≫ (D.c χ).left = jK R ≫ (D.c χ).left
    rw [reassoc_of% hlam]
  have hm : ∀ j, lam z ∈ LB.wchart D.P.L (fun _ : PUnit => (toUnit (TW W) ≫ D.c χ).left) j →
      z ∈ LB.wchart D.P.L (fun _ : PUnit => D.xK χ) j := fun j h => Set.mem_iInter.2 fun k =>
    (congrArg (fun q => q z ∈ D.P.L.U (j k)) hc).mp (Set.mem_iInter.1 h k)
  refine ⟨⟨fun j => res (le j) (pullU W.ι _ (s j))⟩, fun j j' => unit_ext fun y hy => congrArg (gm _ y _) ?_,
    corr_of_val D.P.isLB fun y J hJ => ?_⟩
  · have hz : lam z ∈ LB.wchart D.P.L (fun _ : PUnit => (toUnit (TW W) ≫ D.c χ).left) j ⊓
        LB.wchart D.P.L (fun _ : PUnit => (toUnit (TW W) ≫ D.c χ).left) j' := dn' _ ⟨y, hy⟩
    have k₁ := hv j _ (𝟙 _) z hz.1
    have k₂ := hv j' _ (𝟙 _) z hz.2
    rw [Category.id_comp] at k₁ k₂
    refine inj' _ hz (((gm_res _ z _ hz _).trans k₁).trans (Eq.symm ?_))
    refine ((map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_linComb D.P.L _ _ lam z j j' hz.1 hz.2)
      ((gm_res _ z _ hz _).trans k₂))).trans (Eq.symm ?_)
    refine (gen_trans (D.psi_gen χ) (𝟙 _) z (j' := j') (hm j hz.1) (hm j' hz.2)).trans (congrArg₂ (· * ·) ?_ rfl)
    simp only [trF, Category.id_comp, hc]
  · have e : jK R ∣_ W = (jK R ⁻¹ᵁ W).ι ≫ lam := by
      rw [← cancel_mono W.ι, Category.assoc, hlam, morphismRestrict_ι]
    refine (val_pull hJ _ _ _).trans (Eq.trans ?_ (val_pull hJ _ _ _).symm)
    rw [Category.id_comp, Category.id_comp, e, val_of (D.psi χ) _ y J
      (fun _ => J (((jK R ⁻¹ᵁ W).ι ≫ lam) ≫ (toUnit (TW W) ≫ D.c χ).left)) (fun _ => by rw [Category.assoc, hc])]
    exact hv _ _ _ y (hJ.mem _ _)

theorem nonempty_psiOn {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (W : (Sp R).Opens)
    (hW : (W : Set (Sp R)).Nonempty) (H : ∀ χ, PsiUnitOn D χ W) : Nonempty (PsiOn D W) := by
  choose t ht h using fun χ => exists_gen_on D W hW χ (H χ)
  exact ⟨⟨t, ht, h⟩⟩

theorem toOpen_top {R : Type} [CommRing R] [IsDomain R] (r : R) :
    DegPre.toOpen (R := R) ⊤ r = (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r := by
  show ((Spec (CommRingCat.of R)).presheaf.map (𝟙 _)).hom _ = _
  rw [CategoryTheory.Functor.map_id]; rfl

theorem gs_coord {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {W : (Sp R).Opens} (ψ : PsiOn D W) (χ : D.X) (r : R)
    (j : PUnit → D.P.L.ι) (hj : (⊤ : (Sp R).Opens) ≤ (D.c χ).left ⁻¹ᵁ D.P.L.U (j PUnit.unit))
    (h : jK R ⁻¹ᵁ ⊤ ≤ (LB.LinComb D.P.L (K := PUnit) (fun _ => D.xK χ) (fun _ => -1)).U j)
    (e : ((jK R).app ⊤).hom (DegPre.toOpen (R := R) ⊤ r) =
      ((TK R).left.presheaf.map (homOfLE h).op).hom ((D.psi χ).s j).val)
    {Z : Scheme.{0}} (g : Z ⟶ W.toScheme) (z : Z) :
    (gm g z (LB.wchart D.P.L (fun _ : PUnit => (toUnit (TW W) ≫ D.c χ).left) j) ((ψ.psi χ).s j)).val =
      gs (g ≫ W.ι) z ⊤ (DegPre.toOpen (R := R) ⊤ r) := by
  have mem : ∀ y : W.toScheme, y ∈ LB.wchart D.P.L (fun _ : PUnit => (toUnit (TW W) ≫ D.c χ).left) j := fun y =>
    Set.mem_iInter.2 fun _ => hj (Set.mem_univ (W.ι y))
  have le : LB.wchart D.P.L (fun _ : PUnit => (toUnit (TW W) ≫ D.c χ).left) j ≤ W.ι ⁻¹ᵁ ⊤ := le_top
  have key : ((ψ.psi χ).s j).val = (W.toScheme.presheaf.map (homOfLE le).op).hom
      ((W.ι.app ⊤).hom (DegPre.toOpen (R := R) ⊤ r)) := by
    apply PsiEvenPull.app_injective_generic W
    refine fn_ext fun y hy => (gs_pull (𝟙 _) _ y _ hy _).trans (Eq.trans ?_ (gs_pull (𝟙 _) _ y _ hy _).symm)
    have m₁ := mem ((jK R ∣_ W) y)
    have m₂ : (jK R ⁻¹ᵁ W).ι y ∈ LB.wchart D.P.L (fun _ : PUnit => D.xK χ) j := h trivial
    have k := (gm_pullGen D.P.L _ _ (ψ.psi χ) (jK R ∣_ W) (𝟙 _) y j
        (Set.mem_iInter.2 fun k => Set.mem_iInter.1 m₁ k)).symm.trans
      ((gm_corr D.P.L (ψ.psi_eq χ) (𝟙 _) y (j PUnit.unit) (Set.mem_iInter.2 fun k => Set.mem_iInter.1 m₁ k)
        (Set.mem_iInter.2 fun k => Set.mem_iInter.1 m₂ k)).trans
        (gm_pullGen D.P.L _ _ (D.psi χ) (jK R ⁻¹ᵁ W).ι (𝟙 _) y j (Set.mem_iInter.2 fun k => Set.mem_iInter.1 m₂ k)))
    rw [Category.id_comp, Category.id_comp] at k
    rw [Category.id_comp]
    refine (gs_unit _ y _ m₁ _).trans ((congrArg Units.val k).trans ((gs_unit _ y _ m₂ _).symm.trans
      ((gs_res (jK R ⁻¹ᵁ W).ι y h trivial _).symm.trans ?_)))
    refine (congrArg (gs _ y _) e.symm).trans ((gs_pull _ (jK R) y ⊤ trivial _).trans (Eq.symm ?_))
    refine (gs_res _ y le m₁ _).trans ((gs_pull _ W.ι y ⊤ trivial _).trans ?_)
    rw [morphismRestrict_ι]
  refine (gs_unit g z _ (mem _) _).symm.trans ((congrArg (gs g z _) key).trans ?_)
  exact (gs_res g z le (mem _) _).trans (gs_pull g W.ι z ⊤ trivial _)

theorem psiCoord_pull {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] [IsLocalRing R']
    {φ : R →+* R'} {D : DegPre R} {D' : DegPre R'} (hD : IsPullDeg φ D D') (x : D'.X) (r : R)
    (hr : PsiCoord D (hD.xe x) r) : ∃ u : R'ˣ, PsiCoord D' x (u * φ r) := by
  obtain ⟨j, hj, h, e⟩ := hr
  let cx : Sp R' ⟶ D'.P.A.left := (D'.c x).left
  obtain ⟨q, hq⟩ := exists_chart D'.P.isLB (cx (closedPoint R'))
  have hq' : cx ⁻¹ᵁ D'.P.L.U q = ⊤ := Scheme.preimage_eq_top_of_closedPoint_mem cx hq
  have hV : (⊤ : (Sp R').Opens) ≤ cx ⁻¹ᵁ ((D.P.L.pull (PsiEvenPull.proj hD)).U (fun _ => j PUnit.unit) ⊓ D'.P.L.U q) :=
    fun y _ => ⟨mem_pull.2 ((congrArg (fun f => f y ∈ D.P.L.U (j PUnit.unit)) (hD.c_pr x)).mpr
      (hj (Set.mem_univ (specOf φ y)))), hq'.ge (Set.mem_univ y)⟩
  let u₀ : Γ(Sp R', ⊤)ˣ := res hV (pullU cx _ (hD.w.s (fun _ => j PUnit.unit, q)))
  let u : R'ˣ := Units.map (Scheme.ΓSpecIso (CommRingCat.of R')).hom.hom.toMonoidHom u₀
  have hu : DegPre.toOpen (R := R') ⊤ u = u₀.val := by
    rw [toOpen_top]; exact (Scheme.ΓSpecIso (CommRingCat.of R')).hom_inv_id_apply u₀.val
  have h' : jK R' ⁻¹ᵁ ⊤ ≤ (LB.LinComb D'.P.L (K := PUnit) (fun _ => D'.xK x) (fun _ => -1)).U (fun _ => q) :=
    fun y _ => Set.mem_iInter.2 fun _ => hq'.ge (Set.mem_univ (jK R' y))
  refine ⟨u, fun _ => q, hq'.ge, h', fn_ext (X := (TK R').left) fun z hz => ?_⟩
  have hx : (𝟙 (TK R').left ≫ D'.xK x) ≫ PsiEvenPull.proj hD = (𝟙 _ ≫ hD.g) ≫ (toUnit (TW hD.W) ≫ D.c (hD.xe x)).left :=
    ((ArcSpecialise.pmaps_psiOn hD hD.psiW (𝟙 _) hD.g (hD.g_comm.trans (Category.id_comp _).symm) x).1).trans
      (Category.assoc _ _ _).symm
  have mV := hV (Set.mem_univ (jK R' z))
  obtain ⟨J, hJ, eJ⟩ := exists_good D.P.L D.P.isLB z (K := PUnit) (fun _ => (𝟙 (TK R').left ≫ D'.xK x) ≫ PsiEvenPull.proj hD)
    (fun _ => j PUnit.unit) (fun _ _ _ => rfl) (fun _ => (mem_pull (F := PsiEvenPull.proj hD)).1 mV.1)
  obtain ⟨J', hJ', eJ'⟩ := exists_good D'.P.L D'.P.isLB z (K := PUnit) (fun _ => 𝟙 (TK R').left ≫ D'.xK x)
    (fun _ => q) (fun _ _ _ => rfl) (fun _ => mV.2)
  have k := PsiEvenPull.psi_pull hD x (𝟙 _) z hJ hJ'
  rw [eJ PUnit.unit, eJ' PUnit.unit, val_of _ _ z J j (fun _ => by rw [← hx]; exact eJ PUnit.unit),
    val_of _ _ z J' (fun _ => q) (fun _ => eJ' PUnit.unit), eq_inv_mul_iff_mul_eq] at k
  have k₁ := gs_coord hD.psiW (hD.xe x) r j hj h e (𝟙 _ ≫ hD.g) z
  have k₂ : gs ((𝟙 _ ≫ hD.g) ≫ hD.W.ι) z ⊤ (DegPre.toOpen (R := R) ⊤ r) =
      gs (jK R') z ⊤ (DegPre.toOpen (R := R') ⊤ (φ r)) := by
    rw [Category.id_comp, hD.g_comm, toOpen_top, toOpen_top]
    refine (gs_pull (jK R') (specOf φ) z ⊤ trivial _).symm.trans (congrArg (gs (jK R') z ⊤) ?_)
    exact (congrArg (fun f => f.hom r) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ))).symm
  have k₃ : gs (jK R') z ⊤ u₀.val = (Geo.Tor.gw hD.w (𝟙 _ ≫ D'.xK x) z (j PUnit.unit) q).val := by
    refine (gs_unit _ z ⊤ trivial _).trans (congrArg Units.val ((gm_res _ z hV trivial _).trans
      ((gm_pull (jK R') cx z _ mV _).trans ?_)))
    rw [Category.id_comp]; rfl
  refine (gs_pull (𝟙 _) (jK R') z ⊤ trivial _).trans (Eq.trans ?_ (gs_res (𝟙 _) z h' hz _).symm)
  rw [Category.id_comp, map_mul, hu]
  refine (gs_mul _ z ⊤ trivial _ _).trans ((congrArg₂ (fun a b : (TK R').left.presheaf.stalk z => a * b) k₃ (k₁.trans k₂).symm).trans ?_)
  exact (congrArg Units.val k).trans (gs_unit _ z _ (h' hz) _).symm

theorem dim_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {R : Type}
    [CommRing R] [IsDomain R] (t : SAB H (Sp R)) {K K' : Type} [Field K] [Field K'] (A : PolAV (Sp K))
    (A' : PolAV (Sp K')) {f : Sp K ⟶ Sp R} {f' : Sp K' ⟶ Sp R} {g : A.A.left ⟶ t.G.left} {g' : A'.A.left ⟶ t.G.left}
    (h : IsPullback g A.A.hom t.G.hom f) (h' : IsPullback g' A'.A.hom t.G.hom f') : A'.g = A.g := by
  have := t.semi.smooth
  have := t.semi.geomConnected
  have : ConnectedSpace (Sp R) := inferInstanceAs (ConnectedSpace (PrimeSpectrum R))
  have : ConnectedSpace t.G.left := GeometricallyConnected.connectedSpace t.G.hom t.G.hom.isOpenMap
  obtain ⟨d, hd⟩ := exists_dim_of_preconnected t.G.hom (Classical.arbitrary _)
  exact (H1.dim_unique _ A'.smoothDim ((smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback h' hd)
      (eSec A'.A (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum K'))).trans
    (H1.dim_unique _ A.smoothDim ((smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback h hd)
      (eSec A.A (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum K))).symm

theorem exists_pelUnif_psiCoord : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CharZero R] (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] [CharZero R'] (φ : R →+* R') (t : SAB H (Sp R)) (t' : SAB H (Sp R')) (_ : SABMap t' t (spMap φ)) (U : PELUnif (maximalIdeal R) t) (W : Set (Sp R)), IsNoetherianRing R → IsIntegrallyClosed R → IsAdicComplete (maximalIdeal R) R → IsNoetherianRing R' → IsIntegrallyClosed R' → IsAdicComplete (maximalIdeal R') R' → (∀ a ∈ maximalIdeal R, φ a ∈ maximalIdeal R') → IsOpen W → W ⊆ abLocus t.G → (∀ y, PsiUnitOn U.D.toPre y W) → (⟨RingHom.ker φ, RingHom.ker_isPrime φ⟩ : PrimeSpectrum R) ∈ W → (∃ P : PolAV (Sp (FractionRing R')), ∃ gen : (Over.pullback (jK R')).obj t'.G ≅ P.A, IsMonHom gen.hom ∧ ∃ w : LB.Iso (P.L.pull gen.hom.left) (t'.PP.L.pull (pullback.fst t'.G.hom (jK R'))), w.IsGen) → ∃ (U' : PELUnif (maximalIdeal R') t') (e : U.D.toPre.X ≃ₗ[𝓞 E] U'.D.toPre.X), ∀ χ r, PsiCoord U.D.toPre χ r → ∃ u : R'ˣ, PsiCoord U'.D.toPre (e χ) (u * φ r) := by
  intro E _ _ _ H R _ _ _ _ R' _ _ _ _ φ t t' m U W n₁ n₂ n₃ n₁' n₂' n₃' hφ hWo _ hψ hker ⟨A', eA, mE, wA₀⟩
  letI := H.starRing
  obtain ⟨-, -, -, h4, h5⟩ := GlobalTheory.firstFiveLaws
  have hR : AdmBase R (maximalIdeal R) := ⟨n₁, inferInstance, n₂, n₃⟩
  have hR' : AdmBase R' (maximalIdeal R') := ⟨n₁', inferInstance, n₂', n₃'⟩
  have hI : (maximalIdeal R).map φ ≤ maximalIdeal R' := Ideal.map_le_iff_le_comap.2 hφ
  obtain ⟨bc, mbc, hbc⟩ := grpPullback_iso m.cart (isGrpPullback_pullback t.G (spMap φ))
  obtain ⟨wL, heL, gL, rL⟩ := rigIso_congr U.bundle m.cm m.lin hbc (e := specOf φ) m.base.symm
  have hgen : (specOf φ).base (genericPoint (Spec (CommRingCat.of R'))) ∈ (⟨W, hWo⟩ : (Sp R).Opens) := by
    have : (specOf φ).base (genericPoint (Spec (CommRingCat.of R'))) =
        (⟨RingHom.ker φ, RingHom.ker_isPrime φ⟩ : PrimeSpectrum R) := by
      rw [genericPoint_eq_bot_of_affine]
      exact PrimeSpectrum.ext rfl
    rw [this]; exact hker
  have gpA : IsGrpPullback A'.A t'.G (jK R') (eA.inv.left ≫ pullback.fst t'.G.hom (jK R')) := by
    have : IsMonHom eA.symm.hom := by show IsMonHom eA.inv; infer_instance
    exact ((isGrpPullback_of_iso eA.symm).comp (isGrpPullback_pullback t'.G (jK R'))).congr
      (Category.id_comp _) rfl
  have dA : A'.g = U.A.g := dim_eq t U.A A' (ThetaBaseChange.grp_generic U.U.toUnifPre).1 (gpA.comp m.cart).1
  have wA : LBIso (A'.L.pull eA.hom.left) (U.U.LG.L.pull (pullback.fst t'.G.hom (jK R') ≫
      bc.hom.left ≫ pullback.fst t.G.hom (specOf φ))) :=
    LBIso.trans (pull_isLB A'.isLB _) (pull_isLB t'.PP.isLB _) (pull_isLB U.U.LG.isLB _) wA₀
      (LBIso.chartPull (Geo.Tor.chartPullPull t'.PP.L _ _ rfl)
        (chartPullSame U.U.LG.L _ (fun _ => bc.hom.left ≫ pullback.fst t.G.hom (specOf φ)) _ _ fun _ => rfl) ⟨wL, gL⟩)
  obtain ⟨D', hD, U', hLG, -, hPU⟩ := h4.unifBaseChange R R' _ _ hR hR' φ hI U.D U.A t.G t.semi U.U ⟨W, hWo⟩
    (nonempty_psiOn U.D.toPre ⟨W, hWo⟩ ⟨_, hker⟩ hψ) hgen t'.G bc mbc A' dA eA mE wA t'.PP wL heL gL rL
  obtain ⟨oA', extA⟩ := PELOfUnif.exists_oAct_unif U'.toUnifPre t'.act.toRingAct (by rw [hLG]; exact t'.adj)
  obtain ⟨mod', oD', xl, -, lin', w0'⟩ := h5.oLinBaseChange R R' _ _ hR hR' φ U.D U.A t.G U.U t'.G bc mbc
    A' D' hD U' hPU (𝓞 E) U.oD U.oA t.act.toRingAct U.lin t'.act.toRingAct (fun x => by
      apply Over.OverMorphism.ext
      apply pullback.hom_ext
      · have a : ((Over.pullback (specOf φ)).map (t.act.toRingAct.act x)).left ≫ pullback.fst t.G.hom (specOf φ) =
            pullback.fst t.G.hom (specOf φ) ≫ (t.act.act x).left := pullback.lift_fst _ _ _
        rw [Over.comp_left, Over.comp_left, Category.assoc, Category.assoc, a, ← Category.assoc bc.hom.left]
        exact (congrArg (_ ≫ ·) hbc).trans ((m.act x).trans (congrArg (· ≫ _) hbc.symm))
      · exact (Over.w _).trans (Over.w _).symm) oA' extA
  let P' : PELUnif (maximalIdeal R') t' :=
    { D := D', mod := mod', oD := oD', A := A', oA := oA', U := U', bundle := hLG, lin := lin', w0 := w0' H.w0 U.w0 }
  let xe : D'.toPre.X ≃ₗ[𝓞 E] U.D.toPre.X := { hD.xe with map_smul' := xl }
  refine ⟨P', xe.symm, fun χ r hr => psiCoord_pull hD (xe.symm χ) r ?_⟩
  have e : hD.xe (xe.symm χ) = χ := xe.apply_symm_apply χ
  rwa [e]

end GlobalTheory.PelCoordPull
