import Mathlib
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.PsJetEqToJetOfNonempty
import Formalism.LocalToGlobal.CharacterGerms.NondegenerateCharts
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ESecCompOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CompatAlongOfSquare
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PulledComparisonEven
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TripleProductPointCompProjection
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CubeConclusionIff
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsWithoutCohomology
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TorsionIsoIffAt
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.RelAmpleOfGenericIso
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF GlobalTheory.CubeFib
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.L2.Pj Formalism.L2.FormalSeriesBounds

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.SpecialFibreExt

section Groups

variable {S S' : Scheme.{0}} {f : S' ⟶ S}

theorem exists_ext_baseChange {X : Type} [AddCommGroup X] {G B : Over S} {G' B' : Over S'} [GrpObj G] [GrpObj B]
    [GrpObj G'] [GrpObj B'] {F : G'.left ⟶ G.left} {p : B'.left ⟶ B.left} (hF : IsGrpPullback G' G f F)
    (hB : IsGrpPullback B' B f p) (q : G ⟶ B) [IsMonHom q] (i : splitTorus S X ⟶ G) [IsMonHom i]
    (hk : IsPullback i (toUnit _) q (η[B])) :
    ∃ (q' : G' ⟶ B') (i' : splitTorus S' X ⟶ G'), IsMonHom q' ∧ IsMonHom i' ∧ IsPullback F q'.left q.left p ∧
      IsPullback i' (toUnit _) q' (η[B']) := by
  obtain ⟨i', hi, -⟩ := UU.existsUnique_torusCompat hF.1 i
  have w : (F ≫ q.left) ≫ B.hom = G'.hom ≫ f := by rw [Category.assoc, Over.w, hF.1.w]
  let q' : G' ⟶ B' := Over.homMk (hB.1.lift _ _ w) (hB.1.lift_snd _ _ w)
  have hq : q'.left ≫ p = F ≫ q.left := hB.1.lift_fst _ _ w
  have sq : IsPullback F q'.left q.left p := by
    refine IsPullback.of_bot ?_ hq.symm hB.1
    rw [Over.w, Over.w]; exact hF.1
  refine ⟨q', i', UU.isMonHom_of_over_isMonHom hF hB q q' hq, hi.isMonHom hF, sq, ?_⟩
  have k₀ : IsPullback i.left (splitTorus S X).hom q.left (η[B]).left := by
    have := hk.map (Over.forget S)
    rw [← Rosenlicht.toUnit_left]
    exact this
  have k₁ := (SplitTorus.isPullback_bcMap f X).paste_horiz k₀
  have e₁ : SplitTorus.bcMap f X ≫ i.left = i'.left ≫ F := UU.torusCompat_iff.1 hi
  have e₂ := UU.eSec_comp_of_isGrpPullback hB
  have w' : i'.left ≫ q'.left = (splitTorus S' X).hom ≫ (η[B']).left := by
    refine hB.1.hom_ext ?_ ?_
    · rw [Category.assoc, hq, ← Category.assoc, ← e₁, k₁.w]
      exact (congrArg (_ ≫ ·) e₂.symm).trans (Category.assoc _ _ _).symm
    · rw [Category.assoc, Over.w, Over.w, Category.assoc, Over.w]
      exact (Category.comp_id _).symm
  rw [e₁] at k₁
  have k₂ : IsPullback i'.left (splitTorus S' X).hom q'.left (η[B']).left :=
    IsPullback.of_right (k₁.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp) (by simp)
      (by simp) (by simpa using e₂.symm)) w' sq
  rw [← Rosenlicht.toUnit_left] at k₂ w'
  exact IsPullback.of_map (Over.forget S') (Over.OverMorphism.ext w') k₂

end Groups

section Cube

variable {S S' S'' : Scheme.{0}} {G : Over S} {G' : Over S'} {G'' : Over S''} [GrpObj G] [IsCommMonObj G] [GrpObj G']
  [IsCommMonObj G'] [GrpObj G''] [IsCommMonObj G'']

def comp (m' : CubeMap G'' G') (m : CubeMap G' G) : CubeMap G'' G where
  F := m'.F ≫ m.F
  F3 := m'.F3 ≫ m.F3
  e := m'.e ≫ m.e
  e_comm := by rw [← Category.assoc, m'.e_comm, Category.assoc, m.e_comm, Category.assoc]
  psum_comm I := by rw [← Category.assoc, m'.psum_comm, Category.assoc, m.psum_comm, Category.assoc]

theorem comp_eqs (m : CubeMap G' G) (m' : CubeMap G'' G') (n : CubeMap G'' G) (h : n.F = m'.F ≫ m.F) :
    n.F3 = m'.F3 ≫ m.F3 ∧ n.e = m'.e ≫ m.e := by
  have a : eSec G ≫ G.hom = 𝟙 _ := Over.w η[G]
  refine ⟨hom_ext_triple _ fun i => ?_, ?_⟩
  · rw [cubeMap_comp_proj_three, h, Category.assoc, cubeMap_comp_proj_three, ← Category.assoc m'.F3, cubeMap_comp_proj_three, Category.assoc]
  · have h₁ : n.e ≫ eSec G = (m'.e ≫ m.e) ≫ eSec G := by
      rw [← n.e_comm, h]; exact (comp m' m).e_comm
    have h₂ := congrArg (· ≫ G.hom) h₁
    simp only [Category.assoc, a] at h₂
    exact (Category.comp_id _).symm.trans (h₂.trans (congrArg _ (Category.comp_id _)))

end Cube

section Level

open GlobalTheory.WCub GlobalTheory.UnifPullRig

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]

variable (I G) in

def cubeFst (e : ℕ) : CubeMap (thickObj R I e G) G where
  F := (fstG I e G).left
  F3 := tri (thick R I e) (fstG I e G) (x3 _)
  e := thick R I e
  e_comm := eSec_fstG I e G
  psum_comm J := (tri_thφ (thick R I e) (fstG I e G) (x3 _) (𝟙 _) (Category.id_comp _).symm (⟨J⟩ : thK.{0})).symm

def cubeAb {D : DegPre R} {e : ℕ} (g : GtCoord I D e G) : CubeMap (thickObj R I e G) D.P.A where
  F := g.pG.left
  F3 := tri (thick R I e) g.pG (x3 _)
  e := thick R I e
  e_comm := eSec_pG I g
  psum_comm J := by
    have := g.q_hom
    exact (tri_thφ (thick R I e) g.pG (x3 _) g.q rfl (⟨J⟩ : thK.{0})).symm

theorem exists_level (U : UnifPre I D A G) (e : ℕ) :
    ∃ (L : RigLB (thickObj R I e G)) (c : CubicalStr _ L), (cubeFst I G e).IsPullCubical c U.cubG ∧
      (cubeAb (U.gt e)).IsPullCubical c D.toPre.cub := by
  obtain ⟨hL, hr, h, -⟩ := Out.CubePf.cubePull _ _ _ _ (cubeFst I G e) U.LG U.cubG
  obtain ⟨c, hc, h⟩ := (GtCubeCompare.cubical_clause_iff _ _ _ hL hr).1 h
  refine ⟨_, c, h, (isPullCubical_iff _ _ _).2 ⟨U.w e, (isGen_iff _).1 (U.w_gen e), ?_, ?_⟩⟩
  · intro Z r z p q hp hq
    have hp₀ := eSec_pG I (U.gt e)
    have hf := eSec_fstG I e G
    have m₁ : r z ∈ eSec (thickObj R I e G) ⁻¹ᵁ
        ((D.toPre.P.L.pull (U.gt e).pG.left).U (fun _ => p ⟨⟩) ⊓ (U.LG.L.pull (fstG I e G).left).U (q ⟨⟩)) :=
      ⟨mem_pull.2 (hp ⟨⟩), hq ⟨⟩⟩
    have m₂ : r z ∈ thick R I e ⁻¹ᵁ (U.LG.L.pull (eSec G)).U (q ⟨⟩) :=
      mem_pull.2 ((congrArg (fun a => a (r z) ∈ U.LG.L.U (q ⟨⟩ ⟨⟩)) hf).mp (mem_pull.1 (hq ⟨⟩)))
    have m₃ : r z ∈ thick R I e ⁻¹ᵁ (D.toPre.P.L.pull (eSec D.toPre.P.A)).U (fun _ => p ⟨⟩) :=
      mem_pull.2 ((congrArg (fun a => a (r z) ∈ D.toPre.P.L.U (p ⟨⟩)) hp₀).mp (hp ⟨⟩))
    have W := congrArg (gm r z _) (U.w_rig e (fun _ => p ⟨⟩, q ⟨⟩) (_ ⊓ _ ⊓ _) (inf_le_left.trans inf_le_left)
      (inf_le_left.trans inf_le_right) inf_le_right)
    rw [Fintype.prod_unique, zpow_one]
    refine ((gm_res r z _ (by exact ⟨⟨m₁, m₂⟩, m₃⟩) _).trans (gm_pull r _ z _ m₃ _)).symm.trans (W.symm.trans
      ((map_mul _ _ _).trans (congrArg₂ (· * ·)
        ((gm_res r z _ (by exact ⟨⟨m₁, m₂⟩, m₃⟩) _).trans (gm_pull r _ z _ m₁ _)) ?_)))
    exact (gm_res r z _ (by exact ⟨⟨m₁, m₂⟩, m₃⟩) _).trans
      (gm_res r z _ (by exact Set.mem_iInter.2 hq) _).symm
  · refine EvenPull.pmaps_of_section (K := thK.{0}) (φ' := thφ (thickObj R I e G) (x3 _))
      (φ := thφ D.toPre.P.A (x3 _)) (ε := thε) (L' := U.LG.L.pull (fstG I e G).left) (w := U.w e)
      ((isGen_iff _).1 (U.w_gen e)) D.toPre.P.isLB hL (cubeAb (U.gt e)).F3
      (fun k => (cubeAb (U.gt e)).psum_comm k.down) c.t c.isGen D.toPre.cub.t D.toPre.cub.isGen (𝟙 _) (𝟙 _)
      (Category.id_comp _) (by simpa using Function.surjective_id) (fun y J J' hJ hJ' => ?_)
    have := (U.gt e).q_hom
    have := mono_fstG I e G
    let x := x3 (thickObj R I e G)
    have f₃ := fun k : thK.{0} => tri_thφ (thick R I e) (fstG I e G) x (𝟙 _) (Category.id_comp _).symm k
    have f₄ := fun k : thK.{0} => tri_thφ (thick R I e) (U.gt e).pG x (U.gt e).q rfl k
    let jM : thK.{0} → D.toPre.P.L.ι := fun k =>
      J (tri (thick R I e) (U.gt e).pG x ≫ thφ D.toPre.P.A (x3 D.toPre.P.A) k)
    let jL : thK.{0} → U.LG.L.ι := fun k => J' (thφ (thickObj R I e G) x k) ⟨⟩
    have mM : ∀ k, (tri (thick R I e) (U.gt e).pG x ≫ thφ D.toPre.P.A (x3 D.toPre.P.A) k) y ∈
        D.toPre.P.L.U (jM k) := fun k => hJ _
    have mL : ∀ k, (tri (thick R I e) (fstG I e G) x ≫ thφ G (x3 G) k) y ∈ U.LG.L.U (jL k) := fun k => by
      rw [f₃ k]; exact (mem_pull (F := (fstG I e G).left)).1 (hJ' (thφ (thickObj R I e G) x k))
    have e₂ := (clause_iff (tri (thick R I e) (U.gt e).pG x) (tri (thick R I e) (fstG I e G) x)
      (fun k : thK.{0} => (psum (thickObj R I e G) x k.down).left) _ _ _ (D.toPre.cub.t.s jM) (U.cubG.t.s jL)
      (fun k => (U.w e).s (fun _ => jM k, fun _ => jL k)) thε).1
      (U.w_cub e _ x jL jM (fun a b h => congrArg (fun ψ => J' ψ ⟨⟩)
        ((cancel_mono (fstG I e G).left).1 ((f₃ a).symm.trans (h.trans (f₃ b))))) (fun a b e => congrArg J e)) y
      (Set.mem_iInter.2 mM) (Set.mem_iInter.2 mL) (fun k => ⟨mem_pull.2 (by
        have := mM k; rw [f₄ k] at this; exact this), hJ' (thφ (thickObj R I e G) x k)⟩)
    simp only [Category.id_comp]
    refine e₂.trans (congrArg₂ (· * ·) (Finset.prod_congr rfl fun k _ => congrArg (· ^ thε k) ?_) ?_)
    · exact congrArg (fun a => gw (U.w e) (psum (thickObj R I e G) x k.down).left y (J a) (fun _ => jL k)) (f₄ k)
    · refine Eq.trans ?_ (val_of (L := U.LG.L.pull (fstG I e G).left) (φ := thφ (thickObj R I e G) x) (ε := thε) c.t
        (𝟙 _) y J' (fun k => J' (thφ (thickObj R I e G) x k)) (fun k => congrArg J' (Category.id_comp _))).symm
      rw [hc]
      exact (gm_rp₁ _ y _ _ _ (by exact Set.mem_iInter.2 fun k => hJ' (thφ (thickObj R I e G) x k)) _).symm

end Level

theorem exists_fib {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
    {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
    {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (e : ℕ) {k : Type} [Field k]
    (s : Sp k ⟶ Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) :
    ∃ (φ : Fib k) (m : CubeMap φ.G G), IsGrpPullback φ.G G (s ≫ thick R I e) m.F ∧ m.e = s ≫ thick R I e ∧
      m.IsPullCubical φ.cub U.cubG := by
  obtain ⟨L, c, h₁, h₂⟩ := exists_level U e
  have gG := isGrpPullback_pullback (thickObj R I e G) s
  have gE := isGrpPullback_pullback G (thick R I e)
  have gB := isGrpPullback_pullback D.toPre.P.A (thick R I e)
  obtain ⟨hL, hr, ⟨c', h'⟩, -⟩ := Out.CubePf.cubePull _ _ _ _ (cubeMapOf gG) L c
  obtain ⟨P, g, hg, -, hmul, w, hw⟩ := GlobalTheory.polBaseChange_holds _ _ (s ≫ thick R I e) D.toPre.P
  have gP : IsGrpPullback P.A D.toPre.P.A (s ≫ thick R I e) g := ⟨hg, fun T x y x₀ y₀ hx hy => by
    obtain rfl : x₀ = toBase hg.w x := Over.OverMorphism.ext hx
    obtain rfl : y₀ = toBase hg.w y := Over.OverMorphism.ext hy
    rw [← hmul]; rfl⟩
  have wg : g ≫ D.toPre.P.A.hom = (P.A.hom ≫ s) ≫ thick R I e := hg.w.trans (Category.assoc _ _ _).symm
  have hp : gB.1.lift _ _ wg ≫ pullback.fst _ _ = g := gB.1.lift_fst _ _ wg
  have gP' : IsGrpPullback P.A (thickObj R I e D.toPre.P.A) s (gB.1.lift _ _ wg) :=
    gB.cancel (gP.congr rfl hp.symm) (gB.1.lift_snd _ _ wg)
  have := (U.gt e).q_hom
  have := (U.gt e).i_hom
  obtain ⟨q, i, hq, hi, sq, ker⟩ := exists_ext_baseChange gG gP' (U.gt e).q (U.gt e).i (U.gt e).isKernel
  obtain ⟨rig, hrig⟩ := P.rigid
  obtain ⟨cB⟩ := (GlobalTheory.firstFiveLaws.1.cube _ P ⟨P.L, rig, P.isLB, hrig⟩ rfl).1
  have hB := TripleModel.isPullCubical_of_lbIso GlobalTheory.globalFns_holds P.isAb gP cB D.toPre.cub
    (LBIso.symm ⟨w, hw⟩)
  have hF : (comp (cubeMapOf gG) (cubeAb (U.gt e))).F = (CubeMap.ofHom q).F ≫ (cubeMapOf gP).F := by
    show pullback.fst _ _ ≫ (U.gt e).q.left ≫ pullback.fst _ _ = q.left ≫ g
    rw [← Category.assoc, sq.w, Category.assoc, hp]
  have hs : Smooth ((Over.pullback s).obj (thickObj R I e G)).hom :=
    MorphismProperty.of_isPullback (P := @Smooth) (gG.comp gE).1 U.smooth
  refine ⟨{ G := (Over.pullback s).obj (thickObj R I e G), smooth := hs, L := _, cub := c', P := P, rig := rig
            rig_gen := hrig, cubB := cB, q := q
            q_flat := MorphismProperty.of_isPullback (P := @Flat) sq (U.gt e).q_flat
            q_surj := MorphismProperty.of_isPullback (P := @Surjective) sq (U.gt e).q_surj
            q_affine := isAffineHom_isStableUnderBaseChange.of_isPullback sq (U.gt e).q_affine
            X := D.toPre.X, i := i, i_hom := hi, isKernel := ker
            pull := pullCubCancel _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hF (comp_eqs _ _ _ hF).1 (comp_eqs _ _ _ hF).2 hB
              (pullCubComp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rfl rfl rfl h₂ h') },
    comp (cubeMapOf gG) (cubeFst I G e), gG.comp gE, rfl,
    pullCubComp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rfl rfl rfl h₁ h'⟩

theorem exists_specialFibre : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (T : CDVR) (t : SAB H (Sp T.V)) (P : PELUnif (maximalIdeal T.V) t) (k : Type) [Field k] (r : T.V →+* k), IsLocalHom r → ∃ (φ : Fib k) (m : CubeMap φ.G t.G), IsGrpPullback φ.G t.G (spMap r) m.F ∧ m.e = spMap r ∧ m.IsPullCubical φ.cub t.cub := by
  intro E _ _ _ H T t P k _ r hr
  have h₀ : ∀ a ∈ maximalIdeal T.V ^ (0 + 1), r a = 0 := fun a ha => by
    rw [zero_add, pow_one] at ha
    by_contra h
    exact ha (hr.map_nonunit a (Ne.isUnit h))
  have hs : spMap (Ideal.Quotient.lift _ r h₀) ≫ thick T.V (maximalIdeal T.V) 0 = spMap r := by
    show Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  obtain ⟨φ, m, h₁, h₂, h₃⟩ := exists_fib P.U.toUnifPre 0 (spMap (Ideal.Quotient.lift _ r h₀))
  refine ⟨φ, m, h₁.congr hs rfl, h₂.trans hs, ?_⟩
  have key : ∀ (M : RigLB t.G) (c : CubicalStr t.G M), M = t.PP → HEq c t.cub → m.IsPullCubical φ.cub c →
      m.IsPullCubical φ.cub t.cub := by
    rintro M c rfl h h'
    exact eq_of_heq h ▸ h'
  exact key _ _ P.bundle (PelUnifCompare.cubG_heq P) h₃

end GlobalTheory.SpecialFibreExt
