import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSiegPull
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjPull
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsReducedIsNormalSchemeIsLocallyNoetherianOfSmoo
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSabExtension
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GenericPartDenseProOpen
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.EndoLbIsoSymmetryHypothesisExtendNormalModel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCubicalRigidifiedExtensionStatement
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.SiegLoc GlobalTheory
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.GenFibreTripleExt

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CechPic GlobalTheory.TripleExt

theorem exists_sab_of {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) {U Y : Scheme.{0}} (f : U ⟶ Y)
    (hpic : ∀ {Hs HU : Scheme.{0}} (p : Hs ⟶ Y) (e : Y ⟶ Hs) (jH : HU ⟶ Hs) (pU : HU ⟶ U), Smooth p →
      GeometricallyIntegral p → e ≫ p = 𝟙 _ → IsPullback jH pU p f → ∀ α β : Pic Hs,
        pull jH α = pull jH β → pull e α = pull e β → α = β)
    (G : Over Y) [GrpObj G] [IsCommMonObj G] (semi : IsSemiAbelian G) (act : OAct (𝓞 E) G) (t₀ : SAB H U)
    (a : t₀.G.left ⟶ G.left) (h : IsGrpPullback t₀.G G f a)
    (hact : ∀ x, (t₀.act.act x).left ≫ a = a ≫ (act.act x).left)
    (hcub : ∃ (PP : RigLB G) (cub : CubicalStr G PP) (m : CubeMap t₀.G G), m.F = a ∧ m.e = f ∧
      m.IsPullCubical t₀.cub cub ∧ (t₀.PP.IsSymmetric → PP.IsSymmetric)) :
    ∃ (PP : RigLB G) (cub : CubicalStr G PP) (h₁ : _) (h₂ : _) (h₃ : _)
      (m : SABMap t₀ (SAB.mk G semi act PP cub h₁ h₂ h₃) f), m.φ = a := by
  have := semi.smooth
  have := semi.geomConnected
  obtain ⟨PP, cub, m, rfl, hme, hlin, hsym⟩ := hcub
  have hc₀ : cls t₀.PP.L t₀.PP.isLB = pull m.F (cls PP.L PP.isLB) := by
    obtain ⟨w, hw, -⟩ := hlin
    exact (cls_eq_iff t₀.PP.isLB (pull_isLB PP.isLB _)).2 ⟨w, hw⟩
  have hrig : pull (eSec G) (cls PP.L PP.isLB) = 0 :=
    (cls_eq_zero_iff (pull_isLB PP.isLB _)).2 ⟨PP.rig, PP.rigGen⟩
  have pa : ∀ {T : Over U} (x : T ⟶ t₀.G) b,
      pushPt h.1.w (x ≫ t₀.act.act b) = pushPt h.1.w x ≫ act.act b := fun x b =>
    Over.OverMorphism.ext (by
      show (x.left ≫ _) ≫ _ = (x.left ≫ _) ≫ _
      rw [Category.assoc, hact, Category.assoc])
  have ha1 : ∀ b, η[G] ≫ act.act b = η[G] := fun b => by have := act.hom b; exact IsMonHom.one_hom _
  refine ⟨PP, cub, hsym t₀.sym, fun b => ?_, ?_, ⟨m, h, hme, hact, hlin⟩, rfl⟩
  · refine (cls_eq_iff (isLB_cube _ PP.isLB) (isLB_cube _ PP.isLB)).1 ?_
    rw [cls_cube _ PP.isLB, cls_cube _ PP.isLB]
    have hsm : Smooth (G ⊗ G).hom := by
      show Smooth (pullback.fst G.hom G.hom ≫ G.hom)
      infer_instance
    have hgc : GeometricallyConnected (G ⊗ G).hom := by
      show GeometricallyConnected (pullback.fst G.hom G.hom ≫ G.hom)
      exact GeometricallyConnected.comp _ _
    let T' : Over U := Over.mk (pullback.snd (G ⊗ G).hom f)
    let u : Over.mk (T'.hom ≫ f) ⟶ G ⊗ G := Over.homMk (pullback.fst (G ⊗ G).hom f) pullback.condition
    have hy : ∀ y : G ⊗ G ⟶ G, ∃ y' : T' ⟶ t₀.G, pushPt h.1.w y' = u ≫ y := fun y =>
      ⟨Over.homMk (h.1.lift (u ≫ y).left T'.hom (Over.w (u ≫ y))) (h.1.lift_snd _ _ _),
        Over.OverMorphism.ext (h.1.lift_fst _ _ _)⟩
    obtain ⟨y₁, hy₁⟩ := hy (fst G G)
    obtain ⟨y₂, hy₂⟩ := hy (snd G G)
    let e : 𝟙_ (Over Y) ⟶ G ⊗ G := lift η[G] η[G]
    refine hpic (G ⊗ G).hom e.left u.left T'.hom hsm
      (geometricallyIntegral_of_smooth_of_geometricallyConnected_fibres _) (Over.w e)
      (IsPullback.of_hasPullback _ _) _ _ ?_ ?_
    · have h₀ := (cls_eq_iff (isLB_cube _ t₀.PP.isLB) (isLB_cube _ t₀.PP.isLB)).2 (t₀.adj b)
      rw [cls_cube _ t₀.PP.isLB, cls_cube _ t₀.PP.isLB, hc₀] at h₀
      have h₁ := congrArg (pull (lift y₁ y₂).left) h₀
      rw [pull_cubeCls_pre, pull_cubeCls_pre] at h₁
      refine (pull_cubeCls_push h _ _ u (fun i => ?_) _).trans
        (h₁.trans (pull_cubeCls_push h _ _ u (fun i => ?_) _).symm)
      · fin_cases i
        · simp [pa, hy₁]
        · simp [hy₂]
      · fin_cases i
        · simp [hy₁]
        · simp [pa, hy₂]
    · refine (pull_cubeCls_pre e _ _).trans (Eq.trans ?_ (pull_cubeCls_pre e _ _).symm)
      congr 1
      funext i
      fin_cases i <;> simp [e, ha1]
  · refine (cls_eq_iff PP.isLB (isLB_cube _ PP.isLB)).1 ?_
    rw [cls_cube _ PP.isLB]
    refine hpic G.hom (eSec G) m.F t₀.G.hom inferInstance
      (geometricallyIntegral_of_smooth_of_geometricallyConnected_fibres _) (Over.w η[G]) h.1 _ _ ?_ ?_
    · have h₀ := (cls_eq_iff t₀.PP.isLB (isLB_cube _ t₀.PP.isLB)).2 t₀.prim
      rw [cls_cube _ t₀.PP.isLB, hc₀] at h₀
      have h₁ := pull_cubeCls_push h ![𝟙 t₀.G, t₀.act.act H.w0] ![𝟙 G, act.act H.w0] (pushPt h.1.w (𝟙 t₀.G))
        (fun i => by
          fin_cases i
          · simp
          · exact (congrArg (pushPt h.1.w) (Category.id_comp _).symm).trans (pa _ _)) (cls PP.L PP.isLB)
      have e : (pushPt h.1.w (𝟙 t₀.G)).left = m.F := Category.id_comp _
      rw [e] at h₁
      exact h₀.trans h₁.symm
    · refine hrig.trans (Eq.trans ?_ (pull_cubeCls_pre η[G] _ _).symm)
      refine (cubeCls_one (n := 2) _ hrig).symm.trans ?_
      congr 1
      funext i
      fin_cases i <;> simp [ha1]

end GlobalTheory.GenFibreTripleExt

namespace GlobalTheory.GenFibreTripleExt

open CategoryTheory Limits GlobalTheory.CechPic

theorem exists_sab_extension_genFibre : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R K : Type) [CommRing R] [Field K] (ω : R →+* K) (U Y : Scheme.{0}) (sY : Y ⟶ Sp R) (jQ : U ⟶ pullback sY (spMap ω)) (G' : Over Y) [GrpObj G'] [IsCommMonObj G'] (semi : IsSemiAbelian G') (act : OAct (𝓞 E) G') (t₀ : SAB H U) (φ : t₀.G.left ⟶ G'.left), IsDedFrac ω → Geo.Tor.IsNormalScheme Y → IsProjOver sY → Flat sY → IsOpenImmersion jQ → Dense (Set.range jQ) → IsProper t₀.G.hom → IsGrpPullback t₀.G G' (jQ ≫ pullback.fst _ _) φ → (∀ a, (t₀.act.act a).left ≫ φ = φ ≫ (act.act a).left) → ∀ M : LB G'.left, M.IsLB → LBIso (M.pull φ) t₀.PP.L → ∃ (PP : RigLB G') (cub : CubicalStr G' PP) (h₁ : _) (h₂ : _) (h₃ : _) (m : SABMap t₀ (SAB.mk G' semi act PP cub h₁ h₂ h₃) (jQ ≫ pullback.fst _ _)), m.φ = φ := by
  intro E _ _ _ H R K _ _ ω U Y sY jQ G' _ _ semi act t₀ φ hded hnorm hproj hflat hjQ hdense _ h hact M hM hMa
  have := semi.smooth
  have := semi.geomConnected
  obtain ⟨⟨_, _⟩, _, _⟩ := hded
  letI := ω.toAlgebra
  obtain ⟨_, -, -, _, _, _, _⟩ := GlobalTheory.genericPart_dense_proOpen R K Y U sY jQ hflat hproj hjQ hdense
  refine exists_sab_of H (jQ ≫ pullback.fst _ _) ?_ G' semi act t₀ φ h hact
    (GlobalTheory.T.exists_cubical_rigidified_extension Y U (jQ ≫ pullback.fst _ _) hnorm G' t₀.G φ h t₀.PP t₀.cub M hM hMa)
  intro Hs HU p e jH pU hp hg he hj α β h₁ h₂
  have : Smooth (Over.mk p).hom := hp
  have : GeometricallyIntegral (Over.mk p).hom := hg
  refine GlobalTheory.ZH.EndoExtend.pic_ext (jQ ≫ pullback.fst _ _) hnorm (Over.mk p) e he h₂ ?_
  have k : pullback.fst p (jQ ≫ pullback.fst _ _) = hj.isoPullback.inv ≫ jH := hj.isoPullback_inv_fst.symm
  show pull (pullback.fst p (jQ ≫ pullback.fst _ _)) α = pull (pullback.fst p (jQ ≫ pullback.fst _ _)) β
  rw [k, pull_comp, pull_comp, h₁]

end GlobalTheory.GenFibreTripleExt
