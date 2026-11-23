import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.LeftZeroDuality.H1StructureDimLe
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsPowMulOfAway
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual PositivityTheory.ObstructionTrivialLocus GlobalTheory.CompanionTheory.TrivLoc
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompanionTheory.TrivLoc

theorem isPullback_lift_snd {S : Scheme.{0}} (A X Y : Over S) (q : X ⟶ Y) :
    IsPullback (lift (fst A X) (snd A X ≫ q)).left (snd A X).left (snd A Y).left q.left := by
  have hX : IsPullback (fst A X).left (snd A X).left A.hom X.hom := by
    simpa only [Over.fst_left, Over.snd_left] using IsPullback.of_hasPullback A.hom X.hom
  have hY : IsPullback (fst A Y).left (snd A Y).left A.hom Y.hom := by
    simpa only [Over.fst_left, Over.snd_left] using IsPullback.of_hasPullback A.hom Y.hom
  have e₁ : (lift (fst A X) (snd A X ≫ q)).left ≫ (fst A Y).left = (fst A X).left := by
    rw [← Over.comp_left, lift_fst]
  have e₂ : (lift (fst A X) (snd A X ≫ q)).left ≫ (snd A Y).left = (snd A X).left ≫ q.left := by
    rw [← Over.comp_left, lift_snd, Over.comp_left]
  have hout : IsPullback ((lift (fst A X) (snd A X ≫ q)).left ≫ (fst A Y).left) (snd A X).left
      A.hom (q.left ≫ Y.hom) := by
    rw [e₁, Over.w q]
    exact hX
  exact IsPullback.of_right hout e₂ hY

theorem triv_pull_iso {P Q X : Scheme.{0}} {L : LB X} (e : P ≅ Q) (a : Q ⟶ X) :
    Triv (L.pull (e.hom ≫ a)) ↔ Triv (L.pull a) := by
  constructor
  · intro h
    have := GlobalTheory.Biadditive.triv_pull_comp h e.inv
    rwa [Iso.inv_hom_id_assoc] at this
  · intro h
    exact GlobalTheory.Biadditive.triv_pull_comp h e.hom

theorem triv_pull_iff_locus {S : Scheme.{0}} {A Y T₀ : Over S} (N : LB (A ⊗ Y).left) (v : T₀ ⟶ Y)
    {W X' : Scheme.{0}} (t : W ⟶ T₀.left) (π : X' ⟶ (A ⊗ T₀).left) (f' : X' ⟶ W)
    (h : IsPullback π f' (snd A T₀).left t) :
    Triv ((ev N (fst A T₀) (snd A T₀ ≫ v)).pull π) ↔ Locus N (t ≫ v.left) := by
  let T' : Over S := Over.mk ((t ≫ v.left) ≫ Y.hom)
  let u : T' ⟶ T₀ := Over.homMk t (by simp [T'])
  let w : T' ⟶ Y := Over.homMk (t ≫ v.left) rfl
  have huv : u ≫ v = w := by ext; simp [u, w]
  have hp : IsPullback (lift (fst A T') (snd A T' ≫ u)).left (snd A T').left (snd A T₀).left t :=
    isPullback_lift_snd A T' T₀ u
  let e : X' ≅ (A ⊗ T').left := h.isoIsPullback _ _ hp
  have he : e.hom ≫ (lift (fst A T') (snd A T' ≫ u)).left = π := h.isoIsPullback_hom_fst _ _ hp
  have hc : (lift (fst A T') (snd A T' ≫ u)).left ≫ (lift (fst A T₀) (snd A T₀ ≫ v)).left =
      (lift (fst A T') (snd A T' ≫ w)).left := by
    rw [← Over.comp_left, ← huv]
    congr 1
    ext <;> simp
  have h1 : Triv ((ev N (fst A T₀) (snd A T₀ ≫ v)).pull π) ↔
      Triv (N.pull (π ≫ (lift (fst A T₀) (snd A T₀ ≫ v)).left)) :=
    GlobalTheory.AbLaw.CubeGen.triv_pull_iff N (fun _ : PUnit => (lift (fst A T₀) (snd A T₀ ≫ v)).left) (fun _ => 1) π
  rw [h1, ← he, Category.assoc, hc, triv_pull_iso]
  rfl

theorem family_props {R : Type} [CommRing R] [IsNoetherianRing R] {W : Scheme.{0}} (f : W ⟶ Spec (CommRingCat.of R))
    [Smooth f] [IsProper f] [GeometricallyConnected f] (s : Spec (CommRingCat.of R) ⟶ W) (hs : s ≫ f = 𝟙 _)
    {M : LB W} (hM : M.IsLB) :
    Nonempty (Perf f M) ∧ Nonempty (Perf f (pw M (-1))) ∧ GeometricallyIntegral f ∧ Surjective f := by
  refine ⟨GlobalTheory.ProperFinite.nonempty_perf_of_isProper (R := R) f hM,
    GlobalTheory.ProperFinite.nonempty_perf_of_isProper (R := R) f (isLB_pw hM _),
    GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ _ inferInstance inferInstance, ?_⟩
  have : Surjective (s ≫ f) := by rw [hs]; infer_instance
  exact Surjective.of_comp s f

theorem exists_chart_family : ∀ (S : Scheme.{0}) (A Y : Over S) [GrpObj A], IsAbelianScheme A → ∀ N : LB (A ⊗ Y).left, N.IsLB →
    ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (j : Spec (CommRingCat.of R) ⟶ Y.left),
    ∃ (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)) (M : LB X), M.IsLB ∧ Nonempty (Perf f M) ∧
      Nonempty (Perf f (pw M (-1))) ∧ IsProper f ∧ GeometricallyIntegral f ∧ Surjective f ∧
      (∀ (K : Type) [Field K] (g₀ : R →+* K) (X₀ : Scheme.{0}) (π₀ : X₀ ⟶ X) (f₀ : X₀ ⟶ Spec (CommRingCat.of K)),
        IsPullback π₀ f₀ f (Spec.map (CommRingCat.ofHom g₀)) → Function.Bijective f₀.appTop.hom) ∧
      ∀ (R' : Type) [CommRing R'] (g : R →+* R') (X' : Scheme.{0}) (π : X' ⟶ X)
        (f' : X' ⟶ Spec (CommRingCat.of R')), IsPullback π f' f (Spec.map (CommRingCat.ofHom g)) →
        (Triv (M.pull π) ↔ Locus N (Spec.map (CommRingCat.ofHom g) ≫ j)) := by
  intro S A Y _ hA N hN R _ _ j
  have hB : IsAbelianScheme ((Over.pullback (j ≫ Y.hom)).obj A) := GlobalTheory.AbLaw.CubeGen.isAb_baseChange hA (j ≫ Y.hom)
  let T₀ : Over S := Over.mk (j ≫ Y.hom)
  let v : T₀ ⟶ Y := Over.homMk j rfl
  let f : (A ⊗ T₀).left ⟶ Spec (CommRingCat.of R) := (snd A T₀).left
  let M : LB (A ⊗ T₀).left := ev N (fst A T₀) (snd A T₀ ≫ v)
  have hM : M.IsLB := pull_isLB hN _
  have sm : Smooth f := hB.smooth
  have pr : IsProper f := hB.proper
  have gc : GeometricallyConnected f := hB.geomConnected
  let s : Spec (CommRingCat.of R) ⟶ (A ⊗ T₀).left := (η[(Over.pullback (j ≫ Y.hom)).obj A]).left
  have hs : s ≫ f = 𝟙 _ := Over.w (η[(Over.pullback (j ≫ Y.hom)).obj A])
  obtain ⟨p₁, p₂, p₃, p₄⟩ := family_props f s hs hM
  refine ⟨(A ⊗ T₀).left, f, M, hM, p₁, p₂, pr, p₃, p₄, ?_, ?_⟩
  · intro K _ g₀ X₀ π₀ f₀ h
    exact GlobalTheory.AbLaw.CubeOpen.bijective_appTop GlobalTheory.globalFns_holds _ hB h
  · intro R' _ g X' π f' h
    exact triv_pull_iff_locus N v _ π f' h

end GlobalTheory.CompanionTheory.TrivLoc
