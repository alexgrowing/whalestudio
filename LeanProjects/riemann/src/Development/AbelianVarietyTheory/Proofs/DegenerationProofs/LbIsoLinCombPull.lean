import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.RigGen
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsNormalSchemeSp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AbelianSchemeProperClosureDataBasicProperties
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FiniteResidueFieldIntegralClosurePadicInt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.LineBundleIsoExtendOfNormalBaseStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.LineBundleSymmetryHypothesisBaseChange
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPrimitiveNormalisation
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.PowObjGeometricallyConnected

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ

noncomputable section

namespace GlobalTheory.SymExtend

theorem lbIso_linComb_pull {X X' Y Y' : Scheme.{0}} {L : LB X} (hL : L.IsLB) (F : X' ⟶ X) {K : Type} [Fintype K]
    (φ' : K → (Y' ⟶ X')) (φ : K → (Y ⟶ X)) (ε : K → ℤ) (h : Y' ⟶ Y) (hc : ∀ k, φ' k ≫ F = h ≫ φ k) :
    LBIso (LB.LinComb (L.pull F) φ' ε) ((LB.LinComb L φ ε).pull h) :=
  have r : LBIso (LB.LinComb L φ ε) (LB.LinComb L φ ε) := (GlobalTheory.PrimNorm.lbIso_iff hL φ ε φ ε).2 rfl
  LBIso.chartPull (chartPullLinComb L F φ' φ ε h hc) (chartPullPull _ h h rfl) r

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G]

theorem lbIso_cube_zero (PP : RigLB G) {T : Over S} {n : ℕ} (x : Fin n → (T ⟶ G)) (z : 𝟙_ (Over S) ⟶ T)
    (hz : ∀ i, z ≫ x i = 1) : LBIso ((cubeLB G x PP.L).pull z.left) (PP.L.pull (eSec G)) := by
  have h1 : GlobalTheory.PrimNorm.cls PP.L (eSec G) = 1 := by
    have := (GlobalTheory.PrimNorm.hasGen_iff PP.isLB (K := PUnit) (fun _ => eSec G) (fun _ => 1)).1 ⟨PP.rig, PP.rigGen⟩
    simpa using this
  have h2 : ∀ I : Finset (Fin n), z.left ≫ (psum G x I).left = eSec G := fun I => by
    have e : z ≫ psum G x I = psum G (fun i => z ≫ x i) I := psum_hom (preHom z) x I
    have e' : psum G (fun i => z ≫ x i) I = 1 := by
      have := psum_hom (1 : (T ⟶ G) →* (𝟙_ (Over S) ⟶ G)) x I
      rw [funext hz]
      exact this.symm
    rw [← Over.comp_left, e, e', ← MonObj.one_eq_one]
    rfl
  refine GlobalTheory.PrimNorm.lbIso_nested PP.isLB _ _ _ _ _ _ ?_
  simp only [h2, h1, one_zpow, Finset.prod_const_one]

variable {U : Scheme.{0}} {A : Over U} [GrpObj A] [IsCommMonObj A] {j : U ⟶ S} {a : A.left ⟶ G.left}

omit [IsCommMonObj G] [IsCommMonObj A] in

theorem isPullback_square (h : IsGrpPullback A G j a) :
    IsPullback (lift (pushPt h.1.w (fst A A)) (pushPt h.1.w (snd A A))).left (A ⊗ A).hom (G ⊗ G).hom j := by
  let l := lift (pushPt h.1.w (fst A A)) (pushPt h.1.w (snd A A))
  have l₁ : l.left ≫ pullback.fst G.hom G.hom = pullback.fst A.hom A.hom ≫ a :=
    congrArg (fun z => z.left) (lift_fst (pushPt h.1.w (fst A A)) (pushPt h.1.w (snd A A)))
  have l₂ : l.left ≫ pullback.snd G.hom G.hom = pullback.snd A.hom A.hom ≫ a :=
    congrArg (fun z => z.left) (lift_snd (pushPt h.1.w (fst A A)) (pushPt h.1.w (snd A A)))
  have big : IsPullback (pullback.snd A.hom A.hom ≫ a) (pullback.fst A.hom A.hom) G.hom (A.hom ≫ j) :=
    (IsPullback.of_hasPullback A.hom A.hom).flip.paste_horiz h.1
  have h₁ : IsPullback l.left (pullback.fst A.hom A.hom) (pullback.fst G.hom G.hom) a := by
    refine IsPullback.of_right (h₁₂ := pullback.snd G.hom G.hom) (v₁₃ := G.hom) (h₂₂ := G.hom) ?_
      l₁ (IsPullback.of_hasPullback G.hom G.hom).flip
    rw [l₂, h.1.w]
    exact big
  exact h₁.paste_vert h.1

theorem hypS_extend [IsIntegral S] [IsLocallyNoetherian S] (hS : Geo.Tor.IsNormalScheme S) [Nonempty U] [IsOpenImmersion j]
    [Smooth G.hom] [GeometricallyConnected G.hom] (h : IsGrpPullback A G j a)
    (ext : ∀ α : A ⟶ A, IsMonHom α → ∃! F : G ⟶ G, IsMonHom F ∧ a ≫ F.left = α.left ≫ a)
    (LA : LB A.left) (PP : RigLB G) (hLA : LA.IsLB) (hb : LBIso (PP.L.pull a) LA) (H : GlobalTheory.ZH.HypS A LA) :
    GlobalTheory.ZH.HypS G PP.L := by
  obtain ⟨w', wd', hw', hwd', hs, hp, ha⟩ := H
  obtain ⟨w, ⟨hw, ew⟩, -⟩ := ext w' hw'
  obtain ⟨wd, ⟨hwd, ewd⟩, -⟩ := ext wd' hwd'
  have hL := PP.isLB
  have hB : (PP.L.pull a).IsLB := pull_isLB hL a
  have push : ∀ {u' : A ⟶ A} {u : G ⟶ G}, a ≫ u.left = u'.left ≫ a → ∀ {T : Over U} (x : T ⟶ A),
      pushPt h.1.w (x ≫ u') = pushPt h.1.w x ≫ u := fun e _ x =>
    Over.OverMorphism.ext (by
      show (x.left ≫ _) ≫ _ = (x.left ≫ _) ≫ _
      rw [Category.assoc, ← e, Category.assoc])
  have pa := @push _ _ ew
  have pd := @push _ _ ewd
  have cube : ∀ {T : Over S} {T' : Over U} (x : Fin 2 → (T ⟶ G)) (x' : Fin 2 → (T' ⟶ A))
      (V : Over.mk (T'.hom ≫ j) ⟶ T), (∀ i, pushPt h.1.w (x' i) = V ≫ x i) →
      LBIso (cubeLB A x' LA) ((cubeLB G x PP.L).pull V.left) := fun x x' V hx =>
    LBIso.trans (DVR.linComb_isLB _ hLA _ _) (DVR.linComb_isLB _ hB _ _)
      (pull_isLB (DVR.linComb_isLB _ hL _ _) _) (GlobalTheory.PowPrimitive.lbIso_linComb hb.symm _ _)
      (lbIso_linComb_pull hL a _ _ _ V.left fun I => psum_push h _ _ V hx I.down)
  have cl : ∀ {T : Over S} (x : Fin 2 → (T ⟶ G)), (cubeLB G x PP.L).IsLB := fun x => DVR.linComb_isLB _ hL _ _
  have cl' : ∀ {T : Over U} (x : Fin 2 → (T ⟶ A)), (cubeLB A x LA).IsLB := fun x => DVR.linComb_isLB _ hLA _ _
  have w1 : (1 : 𝟙_ (Over S) ⟶ G) ≫ w = 1 := MonObj.one_comp w
  have wd1 : (1 : 𝟙_ (Over S) ⟶ G) ≫ wd = 1 := MonObj.one_comp wd
  refine ⟨w, wd, hw, hwd, ?_, ?_, ?_⟩
  · obtain ⟨F, -, hF⟩ := ext (𝟙 A) inferInstance
    refine (hF _ ⟨GlobalTheory.Serre.isMonHom_mul w wd, ?_⟩).trans (hF _ ⟨inferInstance, by simp⟩).symm
    have b : pushPt h.1.w (w' * wd') = pushPt h.1.w w' * pushPt h.1.w wd' := map_mul (pushHom h A) _ _
    have c := pa (𝟙 A)
    have d := pd (𝟙 A)
    rw [Category.id_comp] at c d
    rw [c, d, ← MonObj.comp_mul, hs] at b
    have e : 𝟙 A.left ≫ a = (𝟙 A.left ≫ a) ≫ (w * wd).left := congrArg (fun z => z.left) b
    simp only [Category.id_comp] at e
    simpa using e.symm
  · let V := pushPt h.1.w (𝟙 A)
    have hV : V.left = a := Category.id_comp _
    have c := cube ![𝟙 G, w] ![𝟙 A, w'] V (fun i => by
      fin_cases i
      · simp [V]
      · exact (congrArg (pushPt h.1.w) (Category.id_comp _).symm).trans (pa _))
    rw [hV] at c
    refine (GlobalTheory.T.lineBundleIso_extend_of_normal_base S hS U G.left A.left j G.hom (eSec G) a A.hom inferInstance
      (GlobalTheory.geometricallyIntegral_of_smooth _) (Over.w η[G]) h.1 _ _ hL (cl _)
      (hb.trans hB hLA (pull_isLB (cl _) _) (hp.trans hLA (cl' _) (pull_isLB (cl _) _) c))).1 ?_
    refine (lbIso_cube_zero PP ![𝟙 G, w] η[G] fun i => ?_).symm
    rw [MonObj.one_eq_one]
    fin_cases i
    · simp
    · exact w1
  · let V := lift (pushPt h.1.w (fst A A)) (pushPt h.1.w (snd A A))
    have c₁ := cube ![fst G G ≫ w, snd G G] ![fst A A ≫ w', snd A A] V (fun i => by
      fin_cases i
      · exact (pa _).trans (by simp [V])
      · simp [V])
    have c₂ := cube ![fst G G, snd G G ≫ wd] ![fst A A, snd A A ≫ wd'] V (fun i => by
      fin_cases i
      · simp [V]
      · exact (pd _).trans (by simp [V]))
    let z : 𝟙_ (Over S) ⟶ G ⊗ G := lift 1 1
    refine (GlobalTheory.T.lineBundleIso_extend_of_normal_base S hS U (G ⊗ G).left (A ⊗ A).left j (G ⊗ G).hom z.left V.left (A ⊗ A).hom
      (GlobalTheory.smooth_tensorObj_hom G G) (GlobalTheory.geometricallyIntegral_tensorObj_hom G G) (Over.w z)
      (isPullback_square h) _ _ (cl _) (cl _)
      (c₁.symm.trans (pull_isLB (cl _) _) (cl' _) (pull_isLB (cl _) _)
        (ha.trans (cl' _) (cl' _) (pull_isLB (cl _) _) c₂))).1 ?_
    refine LBIso.trans (pull_isLB (cl _) _) (pull_isLB hL _) (pull_isLB (cl _) _)
      (lbIso_cube_zero PP _ z fun i => ?_) (lbIso_cube_zero PP _ z fun i => ?_).symm
    · fin_cases i
      · simpa [z] using w1
      · simp [z]
    · fin_cases i
      · simp [z]
      · simpa [z] using wd1

end GlobalTheory.SymExtend
