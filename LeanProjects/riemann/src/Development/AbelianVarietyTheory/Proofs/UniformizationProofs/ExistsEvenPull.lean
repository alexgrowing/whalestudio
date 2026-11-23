import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ConnectedSpaceOfSection
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ESecCompOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsPullbackKernelBaseChange
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsCPMapCompCancel
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsNormalisedGen
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.BiTrivLiftOfIsNilpotentStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CubTrivDeltaAndEvenUnique
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsEvenCubicalTrivialisationLiftNilpotentStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsDescendThrough
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsCPMapDescends

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section
namespace GlobalTheory.UU.TowerEx

theorem toBase_mul {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {F : G'.left ⟶ G.left} (h : IsGrpPullback G' G f F) (hw : F ≫ G.hom = G'.hom ≫ f) (T : Over S') (x y : T ⟶ G') :
    toBase hw (x * y) = toBase hw x * toBase hw y :=
  Over.OverMorphism.ext (h.2 T x y _ _ rfl rfl).symm

theorem exists_congr {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [IsCommMonObj G] [GrpObj G']
    [IsCommMonObj G'] {P : CP G} {P' : CP G'} {f f' : S' ⟶ S} {F F' : G'.left ⟶ G.left} {hw} {w}
    (h : IsCPMap P' P f F hw w) (e : f = f') (e' : F = F') (hw') : ∃ w', IsCPMap P' P f' F' hw' w' := by
  subst e e'
  exact ⟨w, h⟩

theorem exists_cancel {S S' S'' : Scheme.{0}} {G : Over S} {G' : Over S'} {G'' : Over S''} [GrpObj G] [IsCommMonObj G]
    [GrpObj G'] [IsCommMonObj G'] [GrpObj G''] [IsCommMonObj G''] {P : CP G} {P' : CP G'} {P'' : CP G''} {f : S' ⟶ S}
    {f' : S'' ⟶ S'} {f'' : S'' ⟶ S} {F : G'.left ⟶ G.left} {F' : G''.left ⟶ G'.left} {F'' : G''.left ⟶ G.left}
    {hw w hw'' w''} (h : IsCPMap P' P f F hw w) (h'' : IsCPMap P'' P f'' F'' hw'' w'')
    (hF : IsGrpPullback G'' G' f' F') (e : f' ≫ f = f'') (e' : F' ≫ F = F'') :
    ∃ w', IsCPMap P'' P' f' F' hF.1.w w' := by
  subst e e'
  exact ((isCPMap_comp_cancel _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hF.1.w _ h).2 (toBase_mul hF _) _ h'').imp fun _ => And.left

theorem exists_even_pull {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [IsCommMonObj G] [GrpObj G']
    [IsCommMonObj G'] {P : CP G} {P' : CP G'} {f : S' ⟶ S} {F : G'.left ⟶ G.left} {hw} {w}
    (h : IsCPMap P' P f F hw w) {X : Type} [AddCommGroup X] {i : splitTorus S X ⟶ G} {i' : splitTorus S' X ⟶ G'}
    [IsMonHom i'] (hi : TorusCompat f F i' i) (σ : CubTriv P.c i) (hσ : σ.Even) :
    ∃ σ' : CubTriv P'.c i', σ'.Even := by
  have hE := SplitTorus.isGrpPullback_bcMap f X
  rw [torusCompat_iff] at hi
  have hc : ∀ k : Fin 2, ![i'.left, (1 : splitTorus S' X ⟶ G').left] k ≫ F =
      SplitTorus.bcMap f X ≫ ![i.left, (1 : splitTorus S X ⟶ G).left] k := fun k => by
    fin_cases k
    · exact hi.symm
    · show (1 : splitTorus S' X ⟶ G').left ≫ F = SplitTorus.bcMap f X ≫ (1 : splitTorus S X ⟶ G).left
      rw [one_left_comp h.mul, one_left, ← Category.assoc, hE.1.w]
  obtain ⟨s, hs, Hs⟩ := CubTransport.exists_pmaps ((isGen_iff w).1 h.gen) P.L.isLB P'.L.isLB _ hc σ.s σ.gen
  let β := toBaseHom (toBase_mul hE hE.1.w)
  have hβ : ∀ {T : Over S'} (t : T ⟶ splitTorus S' X), β T t ≫ i = toBase hw (t ≫ i') := fun t =>
    Over.OverMorphism.ext (by
      show (t.left ≫ SplitTorus.bcMap f X) ≫ i.left = (t.left ≫ i'.left) ≫ F
      rw [Category.assoc, hi, Category.assoc])
  have vs : ∀ (T : Over S') (z : T.left) (J') (J), Good P'.L.L z J' → Good P.L.L z J →
      ∀ W : (T ⟶ G') → (T.left.presheaf.stalk z)ˣ, (∀ x, W x = gw w x.left z (J (x.left ≫ F)) (J' x.left)) →
      ∀ t : T ⟶ splitTorus S' X, @id (T.left.presheaf.stalk z)ˣ (val σ.s (β T t).left z J) =
        W (t ≫ i') * (W 1)⁻¹ * val s t.left z J' := by
    intro T z J' J hJ' hJ W hW t
    refine (CubTransport.val_pmaps hc Hs t.left hJ hJ').trans (congrArg₂ (· * ·) ?_ rfl)
    rw [hW, hW]
    exact CubTrivTorus.prod_cubTriv i' t (fun q => gw w q z (J (q ≫ F)) (J' q))
  refine ⟨⟨s, hs, fun T x y u z J' hJ' => ?_⟩, fun T x z J' hJ' => ?_⟩
  · obtain ⟨J, hJ⟩ := exists_good_pt P.L.isLB z
    obtain ⟨W, hW⟩ : ∃ W : (T ⟶ G') → (T.left.presheaf.stalk z)ˣ,
      ∀ x, W x = gw w x.left z (J (x.left ≫ F)) (J' x.left) := ⟨_, fun _ => rfl⟩
    have a := (h.vals T z J' J hJ' hJ W hW).2.2 (x ≫ i') (y ≫ i') (u ≫ i')
    obtain ⟨Z, hZ⟩ : ∃ Z : (T ⟶ splitTorus S' X) → (T.left.presheaf.stalk z)ˣ,
      ∀ t, Z t = val σ.s (β T t).left z J := ⟨_, fun _ => rfl⟩
    have b := σ.cub _ (β T x) (β T y) (β T u) z J hJ
    simp only [← map_mul, hβ] at b
    have b' : Z (x * y * u) * Z x * Z y * Z u = @id (T.left.presheaf.stalk z)ˣ
        (cubV P.c (T := Over.mk (T.hom ≫ f)) z J (toBase hw (x ≫ i')) (toBase hw (y ≫ i')) (toBase hw (u ≫ i'))) *
        Z (x * y) * Z (x * u) * Z (y * u) := by
      simp only [hZ]; exact b
    have v : ∀ t, Z t = W (t ≫ i') * (W 1)⁻¹ * val s t.left z J' := fun t => (hZ t).trans (vs T z J' J hJ' hJ W hW t)
    generalize @id (T.left.presheaf.stalk z)ˣ
        (cubV P.c (T := Over.mk (T.hom ≫ f)) z J (toBase hw (x ≫ i')) (toBase hw (y ≫ i')) (toBase hw (u ≫ i'))) = C
      at a b'
    simp only [v, MonObj.mul_comp] at b'
    apply Additive.ofMul.injective
    have a' := congrArg Additive.ofMul a
    have b'' := congrArg Additive.ofMul b'
    simp only [ofMul_mul, ofMul_inv] at a' b'' ⊢
    linear_combination (norm := abel) a' + b''
  · obtain ⟨J, hJ⟩ := exists_good_pt P.L.isLB z
    obtain ⟨W, hW⟩ : ∃ W : (T ⟶ G') → (T.left.presheaf.stalk z)ˣ,
      ∀ x, W x = gw w x.left z (J (x.left ≫ F)) (J' x.left) := ⟨_, fun _ => rfl⟩
    have a := (h.vals T z J' J hJ' hJ W hW).2.1 (x ≫ i')
    have b := hσ _ (β T x) z J hJ
    rw [← map_inv, hβ] at b
    have b' : W (x⁻¹ ≫ i') * (W 1)⁻¹ * val s (x⁻¹).left z J' =
        val P.sym ((x ≫ i').left ≫ F) z J * (W (x ≫ i') * (W 1)⁻¹ * val s x.left z J') := by
      rw [← vs T z J' J hJ' hJ W hW, ← vs T z J' J hJ' hJ W hW]; exact b
    rw [GrpObj.inv_comp] at b'
    show val s _ z J' = _ * val s _ z J'
    apply Additive.ofMul.injective
    have a' := congrArg Additive.ofMul a
    have b'' := congrArg Additive.ofMul b'
    simp only [ofMul_mul, ofMul_inv] at a' b'' ⊢
    linear_combination (norm := abel) a' + b''

theorem nonempty_biTriv (A : Type) [CommRing A] [IsLocalRing A] (hA : IsNilpotent (IsLocalRing.maximalIdeal A))
    {X : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (G : Over (Spec (CommRingCat.of A))) [GrpObj G]
    [IsCommMonObj G] [Smooth G.hom] [GeometricallyConnected G.hom] (P : CP G) (i : splitTorus _ X ⟶ G)
    (hi : IsMonHom i) : Nonempty (BiTriv P.c i) := by
  letI : Field (A ⧸ IsLocalRing.maximalIdeal A) := Ideal.Quotient.field _
  let f := red (IsLocalRing.maximalIdeal A)
  have hF := isGrpPullback_pullback G f
  have : Smooth ((Over.pullback f).obj G).hom := by show Smooth (pullback.snd G.hom f); infer_instance
  have : GeometricallyConnected ((Over.pullback f).obj G).hom := by
    show GeometricallyConnected (pullback.snd G.hom f); infer_instance
  have : ConnectedSpace (Spec (CommRingCat.of (A ⧸ IsLocalRing.maximalIdeal A))) :=
    SplitTorus.connectedSpace_of_isLocalRing _
  have := (GroupConn.connectedSpace_group _ ((Over.pullback f).obj G)).1
  obtain ⟨i₀, h₀, -⟩ := existsUnique_torusCompat (G' := (Over.pullback f).obj G) hF.1 i
  obtain ⟨_, _, _, _, _, _, _, hP⟩ := exists_isCPMap P (toBase_mul hF hF.1.w) _ (pull_isLB P.L.isLB _) _
    (pullIso_isGen P.L.isLB _)
  exact T.nonempty_biTriv_of_nonempty_biTriv_reduction A _ hA X G _ _ _ hF P _ _ hP i i₀ hi (h₀.isMonHom hF) h₀
    (BiextTriv.main _ X _ _ _ i₀ (h₀.isMonHom hF))

theorem nonempty_desc (A : Type) [CommRing A] [IsLocalRing A] (hA : IsNilpotent (IsLocalRing.maximalIdeal A))
    {X : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (G : Over (Spec (CommRingCat.of A))) [GrpObj G]
    [IsCommMonObj G] [Smooth G.hom] [GeometricallyConnected G.hom] (P : CP G) (Q : TQ G X)
    (h : ∃ σ : CubTriv P.c Q.i, σ.Even) : Nonempty (Q.Desc P) := by
  have : ConnectedSpace (Spec (CommRingCat.of A)) := SplitTorus.connectedSpace_of_isLocalRing _
  have := (GroupConn.connectedSpace_group _ G).1
  exact UU.nonempty_desc _ X G Q P (nonempty_biTriv A hA G P Q.i Q.i_hom) h

theorem exists_lift {A A' : Type} [CommRing A] [IsLocalRing A] [CommRing A'] [Nontrivial A']
    (hA : IsNilpotent (IsLocalRing.maximalIdeal A)) (φ : A →+* A') (hφ : Function.Surjective φ)
    {X : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (G : Over (Spec (CommRingCat.of A))) [GrpObj G]
    [IsCommMonObj G] [Smooth G.hom] [GeometricallyConnected G.hom] (G' : Over (Spec (CommRingCat.of A'))) [GrpObj G']
    [IsCommMonObj G'] {F : G'.left ⟶ G.left} (hF : IsGrpPullback G' G (Spec.map (CommRingCat.ofHom φ)) F)
    {P : CP G} {P' : CP G'} {hw} {w} (hP : IsCPMap P' P (Spec.map (CommRingCat.ofHom φ)) F hw w) (Q' : TQ G' X)
    (h : ∃ σ : CubTriv P'.c Q'.i, σ.Even) :
    ∃ Q : TQ G X, TorusCompat (Spec.map (CommRingCat.ofHom φ)) F Q'.i Q.i ∧ ∃ σ : CubTriv P.c Q.i, σ.Even := by
  have hJ : RingHom.ker φ ≠ ⊤ := RingHom.ker_ne_top φ
  have hN : IsNilpotent (RingHom.ker φ) := by
    obtain ⟨n, hn⟩ := hA
    exact ⟨n, le_bot_iff.1 ((Ideal.pow_right_mono (IsLocalRing.le_maximalIdeal hJ) n).trans hn.le)⟩
  let e := (RingHom.quotientKerEquivOfSurjective hφ).symm
  let g : Spec (CommRingCat.of (A ⧸ RingHom.ker φ)) ⟶ Spec (CommRingCat.of A') := Spec.map e.toCommRingCatIso.hom
  have hg : g ≫ Spec.map (CommRingCat.ofHom φ) = red (RingHom.ker φ) := by
    rw [← Spec.map_comp]
    refine congrArg Spec.map (CommRingCat.hom_ext (RingHom.ext fun a => ?_))
    exact (RingHom.quotientKerEquivOfSurjective hφ).symm_apply_eq.2 rfl
  have hG := isGrpPullback_pullback G' g
  have hF₀ := (hG.comp hF).congr hg rfl
  obtain ⟨Q₀, h₀⟩ := exists_tq_baseChange _ _ g X G' _ _ hG Q'
  obtain ⟨Q, hQ⟩ := TorusQuotLift.main A _ hN X G _ _ hF₀ Q₀
  refine ⟨Q, ?_, ?_⟩
  · have : IsIso (SplitTorus.bcMap g X) := (SplitTorus.isGrpPullback_bcMap g X).1.isIso_fst_of_isIso
    rw [torusCompat_iff] at h₀ hQ ⊢
    rw [← cancel_epi (SplitTorus.bcMap g X), ← Category.assoc, ← bcMap_comp, hg, hQ, ← Category.assoc, ← h₀,
      Category.assoc]
  · obtain ⟨_, _, _, _, _, _, _, hP₀⟩ := exists_isCPMap P' (toBase_mul hG hG.1.w) _ (pull_isLB P'.L.isLB _) _
      (pullIso_isGen P'.L.isLB _)
    obtain ⟨_, -, h₁⟩ := hP.exists_comp hP₀ (hG.comp hF).1.w
    obtain ⟨_, h₂⟩ := exists_congr h₁ hg rfl hF₀.1.w
    obtain ⟨σ, hσ⟩ := h
    have := Q₀.i_hom
    exact T.exists_even_cubicalTrivialisation_lift_nilpotent A _ hN hJ X G _ _ _ hF₀ P _ _ h₂ Q.i Q₀.i Q.i_hom Q₀.i_hom hQ
      (nonempty_biTriv A hA G P Q.i Q.i_hom) (exists_even_pull hP₀ h₀ σ hσ)

theorem exists_transition {S S' : Scheme.{0}} [ConnectedSpace S'] {f : S' ⟶ S} {X : Type} [AddCommGroup X]
    [Module.Free ℤ X] {G : Over S} {G' : Over S'} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G']
    [ConnectedSpace G'.left] {F : G'.left ⟶ G.left} (hF : IsGrpPullback G' G f F) {P : CP G} {P' : CP G'} {hw} {w}
    (hP : IsCPMap P' P f F hw w) {Q : TQ G X} {Q' : TQ G' X} (h : TorusCompat f F Q'.i Q.i) (D : Q.Desc P)
    (D' : Q'.Desc P') :
    ∃ β : Q'.B.left ⟶ Q.B.left, IsCPPullback D'.M D.M f β ∧ Q'.q.left ≫ β = F ≫ Q.q.left := by
  obtain ⟨β, hq, hβ⟩ := TQ.exists_isGrpPullback _ _ f X G G' F hF Q Q' h
  obtain ⟨_, -, h₁⟩ := D.map.exists_comp hP (by rw [Category.assoc, Over.w, Category.comp_id, hw])
  obtain ⟨_, h₂⟩ := exists_congr h₁ (Category.comp_id f) hq.symm (by
    rw [Category.assoc, hβ.1.w, ← Category.assoc, Over.w])
  exact ⟨β, ⟨hβ, isCPMap_descends _ _ f X G' Q' P' D' Q.B D.M β hβ.1.w _ _ (toBase_mul hβ _) h₂⟩, hq⟩

end GlobalTheory.UU.TowerEx
end
