import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.SystemPrimesDistinctLevelsGeThree
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsPullCubicalOfIso
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.BijectiveRestrictPointsOfEtaleOfHenselian
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsReducedAlgebraOfSmoothOfIsNoetherianRing
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ConnectedSpaceSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CmModelCoefficientSubringDedekindCompatibleEmbed
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.SqrtNegDiscMemCoeffField
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CardTorsionAbelianVariety
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.ThetaMove
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

noncomputable section

namespace GlobalTheory.Models.RankZero

def Triv {X : Scheme.{0}} (L : LB X) : Prop := ∃ t : LB.Gen L, t.IsGen

section Bundles

variable {X Y : Scheme.{0}}

theorem Triv.linComb {L : LB X} (h : Triv L) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ) :
    Triv (LB.LinComb L φ ε) := by
  obtain ⟨t, ht⟩ := h
  refine ⟨⟨fun j => ∏ k, res (LB.wchart_le L φ j k) (pullU (φ k) _ (t.s (j k))) ^ ε k⟩, fun i j => ?_⟩
  refine unit_ext fun y hy => ?_
  have v : ∀ j : K → L.ι, y ∈ LB.wchart L φ j →
      gm (𝟙 Y) y (LB.wchart L φ j) (∏ k, res (LB.wchart_le L φ j k) (pullU (φ k) _ (t.s (j k))) ^ ε k) =
        ∏ k, gm (φ k) y (L.U (j k)) (t.s (j k)) ^ ε k := fun j hj =>
    (map_prod _ _ _).trans (Finset.prod_congr rfl fun k _ => (map_zpow _ _ _).trans (congrArg (· ^ ε k)
      (gm_rp₁ (φ k) y _ _ (LB.wchart_le L φ j k) hj _)))
  refine ((gm_res _ y _ hy _).trans (v i hy.1)).trans (Eq.symm ((map_mul _ _ _).trans ((congrArg₂ (· * ·)
    (gm_linComb L φ ε (𝟙 Y) y i j hy.1 hy.2) ((gm_res _ y _ hy _).trans (v j hy.2))).trans ?_)))
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  have hm : φ k y ∈ L.U (i k) ⊓ L.U (j k) := ⟨LB.wchart_le L φ i k hy.1, LB.wchart_le L φ j k hy.2⟩
  rw [← mul_zpow, Category.id_comp]
  exact congrArg (· ^ ε k) (((gm_res (φ k) y _ hm _).symm.trans ((congrArg (gm (φ k) y _) (ht (i k) (j k))).trans
    ((map_mul _ _ _).trans (congrArg₂ (· * ·) rfl (gm_res (φ k) y _ hm _))))).symm)

theorem Triv.of_pull {L : LB X} {F : Y ⟶ X} (h : Triv (L.pull F)) (ρ : X ⟶ Y) (e : ρ ≫ F = 𝟙 X) : Triv L := by
  obtain ⟨t, ht⟩ := h
  exact gen_chartPull (chartPullSec L F ρ e) t ht

theorem Triv.lbIso {L M : LB X} (h : Triv L) (h' : Triv M) : LBIso L M := by
  obtain ⟨t, ht⟩ := h
  obtain ⟨u, hu⟩ := h'
  refine ⟨⟨fun p => res inf_le_left (u.s p.1) * (res inf_le_right (t.s p.2))⁻¹⟩, fun p q => unit_ext fun y hy => ?_⟩
  have v : ∀ p : M.ι × L.ι, y ∈ M.U p.1 ⊓ L.U p.2 →
      gm (𝟙 X) y (M.U p.1 ⊓ L.U p.2) (res inf_le_left (u.s p.1) * (res inf_le_right (t.s p.2))⁻¹) =
        gm (𝟙 X) y _ (u.s p.1) * (gm (𝟙 X) y _ (t.s p.2))⁻¹ := fun p hp =>
    (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res _ y _ hp _) ((map_inv _ _).trans
      (congrArg (·⁻¹) (gm_res _ y _ hp _))))
  have w : ∀ {N : LB X} (s : LB.Gen N), s.IsGen → ∀ i j, y ∈ N.U i ⊓ N.U j →
      gm (𝟙 X) y _ (s.s i) = gm (𝟙 X) y _ (N.g i j) * gm (𝟙 X) y _ (s.s j) := fun s hs i j hm =>
    (gm_res _ y _ hm _).symm.trans ((congrArg (gm (𝟙 X) y _) (hs i j)).trans
      ((map_mul _ _ _).trans (congrArg₂ (· * ·) rfl (gm_res _ y _ hm _))))
  refine ((gm_res _ y _ hy _).trans (v p hy.1)).trans (Eq.symm ((map_mul _ _ _).trans ((congrArg₂ (· * ·)
    (gm_div L M (𝟙 X) y p q hy) ((gm_res _ y _ hy _).trans (v q hy.2))).trans ?_)))
  rw [w u hu p.1 q.1 ⟨hy.1.1, hy.2.1⟩, w t ht p.2 q.2 ⟨hy.1.2, hy.2.2⟩, mul_inv, _root_.mul_mul_mul_comm]

theorem triv_trivLB (X : Scheme.{0}) : Triv (Out.Inh.trivLB X) :=
  ⟨⟨fun _ => 1⟩, ZJ.isGen_one_of_g_eq_one _ fun _ _ => rfl⟩

end Bundles

section Groups

variable {S S' : Scheme.{0}}

theorem hom_unique {G : Over S} (hG : IsIso G.hom) {T : Over S} (x y : T ⟶ G) : x = y :=
  Over.OverMorphism.ext (by rw [← cancel_mono G.hom, Over.w, Over.w])

theorem left_unique {G : Over S} (hG : IsIso G.hom) {T : Scheme.{0}} {x y : T ⟶ G.left} (h : x ≫ G.hom = y ≫ G.hom) :
    x = y := (cancel_mono G.hom).1 h

theorem isIso_unit (S : Scheme.{0}) : IsIso (𝟙_ (Over S)).hom := inferInstanceAs (IsIso (𝟙 S))

theorem isIso_tensor {G G' : Over S} (hG : IsIso G.hom) (hG' : IsIso G'.hom) : IsIso (G ⊗ G').hom := by
  have : IsIso (fst G G').left := inferInstanceAs (IsIso (pullback.fst G.hom G'.hom))
  rw [← Over.w (fst G G')]
  infer_instance

theorem isIso_left {G G' : Over S} (hG : IsIso G.hom) (hG' : IsIso G'.hom) (x : G ⟶ G') : IsIso x.left :=
  IsIso.of_isIso_fac_right (Over.w x)

theorem section_w {G : Over S} (x : 𝟙_ (Over S) ⟶ G) : x.left ≫ G.hom = 𝟙 S := Over.w x

theorem triv_of_pull {G G' : Over S} (hG : IsIso G.hom) (hG' : IsIso G'.hom) (x : G ⟶ G') {L : LB G'.left}
    (h : Triv (L.pull x.left)) : Triv L :=
  have := isIso_left hG hG' x
  h.of_pull (inv x.left) (IsIso.inv_hom_id _)

theorem triv_rig {G : Over S} [GrpObj G] (hG : IsIso G.hom) (L : RigLB G) : Triv L.L :=
  triv_of_pull (isIso_unit S) hG η[G] ⟨L.rig, L.rigGen⟩

def zmap {G' : Over S'} {G : Over S} (hG : IsIso G.hom) (f : S' ⟶ S) : G'.left ⟶ G.left := G'.hom ≫ f ≫ inv G.hom

theorem zmap_w {G' : Over S'} {G : Over S} (hG : IsIso G.hom) (f : S' ⟶ S) :
    zmap (G' := G') hG f ≫ G.hom = G'.hom ≫ f := by simp [zmap]

theorem isGrpPullback_zero {G' : Over S'} {G : Over S} [GrpObj G'] [GrpObj G] (hG' : IsIso G'.hom) (hG : IsIso G.hom)
    (f : S' ⟶ S) : IsGrpPullback G' G f (zmap hG f) :=
  ⟨IsPullback.of_vert_isIso ⟨zmap_w hG f⟩, fun T x y x₀ y₀ _ _ => left_unique hG (by
    rw [Over.w, Category.assoc, zmap_w, ← Category.assoc, Over.w]; rfl)⟩

theorem isSquare_zero {G' : Over S'} {G : Over S} (hG : IsIso G.hom) (f : S' ⟶ S) :
    IsSquare (zmap (G' := G') hG f) (zmap (isIso_tensor hG hG) f) :=
  ⟨left_unique hG (by rw [Category.assoc, Over.w, Category.assoc, zmap_w, zmap_w, ← Category.assoc, Over.w]),
    left_unique hG (by rw [Category.assoc, Over.w, Category.assoc, zmap_w, zmap_w, ← Category.assoc, Over.w])⟩

theorem isAbelianScheme_zero {G : Over S} [GrpObj G] [IsCommMonObj G] (hG : IsIso G.hom) : IsAbelianScheme G :=
  ⟨inferInstance, inferInstance, inferInstance, MorphismProperty.of_isPullback (P := @GeometricallyConnected)
    (isGrpPullback_zero hG (isIso_unit S) (𝟙 S)).1 (UU.isAbelianScheme_unit S).geomConnected⟩

theorem sec_comm {G' : Over S'} {G : Over S} (hG : IsIso G.hom) {f : S' ⟶ S} {φ : G'.left ⟶ G.left}
    (w : φ ≫ G.hom = G'.hom ≫ f) (x' : 𝟙_ (Over S') ⟶ G') (x : 𝟙_ (Over S) ⟶ G) : x'.left ≫ φ = f ≫ x.left :=
  left_unique hG ((Category.assoc _ _ _).trans ((congrArg (x'.left ≫ ·) w).trans ((Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ f) (section_w x')).trans ((Category.id_comp f).trans ((Category.comp_id f).symm.trans
      ((congrArg (f ≫ ·) (section_w x).symm).trans (Category.assoc _ _ _).symm)))))))

theorem weilIs_zero {G : Over S} [GrpObj G] (hG : IsIso G.hom) {L : LB G.left} (hL : L.IsLB) (h : Triv L) (k : ℤ)
    {T : Over S} (x y : T ⟶ G) : Out.WeilIs G L k x y 1 := by
  intro p
  refine ⟨⊤, trivial, ?_, fun θx θy _ _ => corr_of_val hL fun z J hJ => ?_⟩
  · obtain ⟨a, ha⟩ := h.linComb ![(snd _ G).left, (Out.translPt G (Out.overResι ⊤ ≫ x)).left] ![k, -k]
    obtain ⟨b, hb⟩ := h.linComb ![(snd _ G).left, (Out.translPt G (Out.overResι ⊤ ≫ y)).left] ![k, -k]
    exact ⟨⟨_, a, ha⟩, ⟨_, b, hb⟩, rfl, rfl⟩
  · have e : ∀ u : Out.overRes (T := T) ⊤ ⟶ G, Out.translT G u = 𝟙 _ := fun u =>
      CartesianMonoidalCategory.hom_ext _ _ (by simp [Out.translT]) (hom_unique hG _ _)
    refine ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl (val_pull hJ _ _ _))).trans (Eq.symm
      (((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans
        (congrArg₂ (· * ·) rfl (val_pull hJ _ _ _))) (H1.val_constGen _ _ _ _ _))).trans ?_))
    rw [e, e, Out.unitRes, map_one, map_one, _root_.mul_one, Over.id_left, Category.comp_id]
    exact mul_comm _ _

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem nonempty_sabMap {t' : SAB H S'} {t : SAB H S} (h' : IsIso t'.G.hom) (h : IsIso t.G.hom) (f : S' ⟶ S) :
    Nonempty (SABMap t' t f) := by
  obtain ⟨t₁, ⟨m⟩⟩ := Inhab.exists_pull f t
  have h₁ : IsIso t₁.G.hom := MorphismProperty.of_isPullback (P := MorphismProperty.isomorphisms _) m.cart.1 h
  let α : t'.G ⟶ t₁.G := Over.homMk (zmap h₁ (𝟙 _)) (by simp [zmap_w])
  have : IsMonHom α := ⟨hom_unique h₁ _ _, hom_unique h₁ _ _⟩
  let n : SABMap t' t₁ (𝟙 _) := ⟨CubeMap.ofHom α, isGrpPullback_zero h' h₁ _, rfl,
    fun a => congrArg (fun q => q.left) (hom_unique h₁ (t'.act.act a ≫ α) (α ≫ t₁.act.act a)),
    HeckePoint.isPullCubical_of_iso globalFns_holds (isAbelianScheme_zero h') α _ _
      ((triv_rig h' _).lbIso ((triv_rig h₁ _).linComb _ _))⟩
  obtain ⟨r, -⟩ := ObjMaps.exists_sab_comp m n
  exact ⟨Category.id_comp f ▸ r⟩

end Groups

theorem surjective_unit
    (hc : ∀ (k : Type) [Field k] [IsAlgClosed k] (B : Over (Sp k)) [GrpObj B] (g N : ℕ), IsAbelianScheme B →
      SmoothOfRelativeDimension g B.hom → (N : k) ≠ 0 → Nat.card {x : 𝟙_ (Over (Sp k)) ⟶ B // x ^ N = 1} = N ^ (2 * g))
    {k : Type} [Field k] [IsAlgClosed k] (B : Over (Sp k)) [GrpObj B] (hB : IsAbelianScheme B) {N : ℕ} (h₁ : 1 < N)
    (hN : (N : k) ≠ 0) (h : ∀ x : 𝟙_ (Over (Sp k)) ⟶ B, x ^ N = 1 → x = 1) : Function.Surjective (eSec B) := by
  obtain ⟨g, hg⟩ := AbelianDim.exists_relDim k B hB
  have h1 : Nat.card {x : 𝟙_ (Over (Sp k)) ⟶ B // x ^ N = 1} = 1 := by
    rw [Nat.card_eq_one_iff_exists]
    exact ⟨⟨1, one_pow N⟩, fun x => Subtype.ext (h x.1 x.2)⟩
  rw [hc k B g N hB hg hN] at h1
  obtain rfl : g = 0 := by
    rcases (Nat.pow_eq_one.1 h1) with h | h <;> omega
  have := hB.proper
  have := hB.geomConnected
  have := hB.smooth
  have : Etale B.hom := (Etale.iff_smoothOfRelativeDimension_zero _).2 hg
  obtain ⟨ho, hcl⟩ := isOpenImmersion_and_isClosedImmersion_of_section_of_etale B.hom (eSec B) (section_w η[B])
  have : ConnectedSpace B.left := (GroupConn.connectedSpace_group _ B).1
  have hne : (Set.range (eSec B)).Nonempty := ⟨_, (default : PrimeSpectrum k), rfl⟩
  exact Set.range_eq_univ.1 (IsClopen.eq_univ ⟨(eSec B).isClosedEmbedding.isClosed_range,
    (eSec B).isOpenEmbedding.isOpen_range⟩ hne)

theorem isIso_of_no_torsion
    (hc : ∀ (k : Type) [Field k] [IsAlgClosed k] (B : Over (Sp k)) [GrpObj B] (g N : ℕ), IsAbelianScheme B →
      SmoothOfRelativeDimension g B.hom → (N : k) ≠ 0 → Nat.card {x : 𝟙_ (Over (Sp k)) ⟶ B // x ^ N = 1} = N ^ (2 * g))
    {S : Scheme.{0}} [IsReduced S] (G : Over S) [GrpObj G] (hG : IsAbelianScheme G)
    (h : ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S), ∃ N : ℕ, 1 < N ∧ (N : k) ≠ 0 ∧
      ∀ g : Over.mk x ⟶ G, g ^ N = 1 → g = 1) : IsIso G.hom := by
  have := hG.proper
  have := hG.smooth
  have := hG.comm
  have : IsReduced G.left := isReduced_of_smooth_of_isReduced G.hom
  have hcl := isClosedImmersion_of_section_of_isSeparated G.hom (eSec G) (section_w η[G])
  have hs : Surjective (eSec G) := by
    refine ⟨fun y => ?_⟩
    let k := AlgebraicClosure (G.left.residueField y)
    let u : Sp k ⟶ G.left := Spec.map (CommRingCat.ofHom (algebraMap (G.left.residueField y) k)) ≫
      G.left.fromSpecResidueField y
    have hu : ∀ p, u p = y := fun p => Scheme.fromSpecResidueField_apply y _
    let x := u ≫ G.hom
    have hp := isGrpPullback_pullback G x
    have hB := isAbelianScheme_pullback_obj x G hG
    have := hB.comm
    obtain ⟨N, h₁, hN, ht⟩ := h k ((𝟙_ (Over (Sp k))).hom ≫ x)
    have hsB := surjective_unit hc _ hB h₁ hN fun g hg => by
      have e := ht (pushHom hp _ g) (by rw [← map_pow, hg, map_one])
      rw [← map_one (pushHom hp (𝟙_ _))] at e
      exact Over.OverMorphism.ext (hp.1.hom_ext (congrArg (fun q => q.left) e) (by rw [Over.w, Over.w]))
    obtain ⟨p, hp'⟩ := hsB (hp.1.lift u (𝟙 _) (Category.id_comp _).symm (default : PrimeSpectrum k))
    refine ⟨x p, ?_⟩
    have e₁ := congrArg (fun q => q p) (cubeMapOf hp).e_comm
    have e₂ := congrArg (fun q => q (default : PrimeSpectrum k)) (hp.1.lift_fst u (𝟙 _) (Category.id_comp _).symm)
    exact e₁.symm.trans ((congrArg (pullback.fst G.hom x) hp').trans (e₂.trans (hu _)))
  have : IsIso (eSec G) := isIso_of_isClosedImmersion_of_surjective _
  have : IsIso (eSec G ≫ G.hom) := by
    rw [show eSec G ≫ G.hom = 𝟙 S from section_w η[G]]
    exact inferInstanceAs (IsIso (𝟙 S))
  exact IsIso.of_isIso_comp_left (eSec G) G.hom

abbrev Count : Prop := ∀ (k : Type) [Field k] [IsAlgClosed k] (B : Over (Sp k)) [GrpObj B] (g N : ℕ),
  IsAbelianScheme B → SmoothOfRelativeDimension g B.hom → (N : k) ≠ 0 →
    Nat.card {x : 𝟙_ (Over (Sp k)) ⟶ B // x ^ N = 1} = N ^ (2 * g)

theorem spMap_comp {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R →+* R') (g : R' →+* R'') :
    spMap g ≫ spMap f = spMap (g.comp f) := (Spec.map_comp _ _).symm

theorem exists_spMap {R R' : Type} [CommRing R] [CommRing R'] (x : Sp R' ⟶ Sp R) : ∃ β : R →+* R', x = spMap β := by
  obtain ⟨φ, rfl⟩ := Spec.map_surjective x
  exact ⟨φ.hom, rfl⟩

theorem isQProjOver_of_isIso {R : Type} [CommRing R] {X : Scheme.{0}} (f : X ⟶ Sp R) (hf : IsIso f) :
    IsQProjOver f := by
  obtain ⟨N, i, hi, h⟩ := Inhab.isProjOver_id R
  exact ⟨N, f ≫ i, inferInstance, inferInstance, by rw [Category.assoc, h, Category.comp_id]⟩

theorem eq_constPt_of {R k : Type} [CommRing R] [Field k] (x : Sp (DualNumber k) ⟶ Sp R)
    (h : ∀ β : R →+* DualNumber k,
      β = ((algebraMap k (DualNumber k)).comp (TrivSqZeroExt.fstHom k k k).toRingHom).comp β) : x = constPt x := by
  obtain ⟨β, rfl⟩ := exists_spMap x
  rw [constPt, spMap_comp, spMap_comp]
  exact congrArg spMap (h β)

theorem eq_constPt_field {F k : Type} [Field F] [CharZero F] [Algebra.IsAlgebraic ℚ F] [Field k]
    (x : Sp (DualNumber k) ⟶ Sp F) : x = constPt x := by
  refine eq_constPt_of x fun φ => ?_
  letI : Algebra ℚ (DualNumber k) := (φ.comp (algebraMap ℚ F)).toAlgebra
  have : Algebra.FormallyUnramified ℚ F := Algebra.FormallyUnramified.of_isSeparable ℚ F
  have := Algebra.FormallyUnramified.ext' (R := ℚ) (A := F) (B := DualNumber k)
    (TrivSqZeroExt.fstHom k k k).toRingHom ⟨2, TrivSqZeroExt.kerIdeal_sq k k⟩ φ.toRatAlgHom
    ((algebraMap k (DualNumber k)).comp ((TrivSqZeroExt.fstHom k k k).toRingHom.comp φ)).toRatAlgHom
    (fun a => by simp [TrivSqZeroExt.algebraMap_eq_inl])
  exact RingHom.ext fun a => DFunLike.congr_fun this a

section Objects

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}

theorem subsingleton_La (hD : D.p + D.q = 0) : Subsingleton D.La := by
  have := D.fin
  have := D.proj
  have : Module.Flat (𝓞 E) D.La := inferInstance
  exact Module.finrank_zero_iff.mp (D.rank.trans hD)

theorem isIso_zeroTriple (S : Scheme.{0}) : IsIso (Inhab.zeroTriple H S).G.hom := isIso_unit S

theorem lieMult_zero {S : Scheme.{0}} {O k : Type} [CommRing O] [Field k] {G : Over S} [GrpObj G] (hG : IsIso G.hom)
    (act : OAct O G) (t : Sp k ⟶ S) (τ : O →+* k) {n : ℕ} (hn : n = 0) : LieMult act t τ n := by
  subst hn
  exact ⟨Fin.elim0, fun i => i.elim0, fun w _ => ⟨Fin.elim0, ⟨Fin.elim0, fun i => i.elim0, hom_unique hG _ _⟩,
    fun _ _ => Subsingleton.elim _ _⟩⟩

def zeroObj (hD : D.p + D.q = 0) (l : Level H) {S : Scheme.{0}} (s : S ⟶ Sp (KA l)) : Obj D l (baseKA l) s where
  t := Inhab.zeroTriple H S
  proper := Inhab.isProper_zeroTriple S
  ample := (Out.Inh.zeroPolAV S).ample
  ktriv := fun _ _ _ _ _ => hom_unique (isIso_zeroTriple S) _ _
  eta := fun _ => 1
  eta_add := fun _ _ => (_root_.mul_one _).symm
  eta_ker := fun _ _ => rfl
  etaA := fun _ => 1
  etaA_add := fun _ _ => (_root_.mul_one _).symm
  etaA_ker := fun _ => rfl
  geom := fun k _ _ x β _ => by
    have hz := isIso_zeroTriple (H := H) S
    have := subsingleton_La hD
    have := BaseRing.finiteDimensional_KA l
    obtain ⟨ζ, h₁, h₂, h₃⟩ := HostModel.exists_roots (KA l) k β
    refine ⟨fun τ => ⟨fun _ => lieMult_zero hz _ _ _ (by omega), fun _ => lieMult_zero hz _ _ _ (by omega)⟩,
      ⟨ζ, h₁, h₂, fun _ _ => 1, fun _ _ _ => hom_unique hz _ _, fun _ _ _ => hom_unique hz _ _,
        fun _ _ _ => ⟨fun _ => ⟨0, Subsingleton.elim _ _⟩, fun _ => rfl⟩,
        fun _ _ _ => ⟨fun _ => ⟨0, hom_unique hz _ _⟩, fun _ => hom_unique hz _ _⟩,
        fun _ _ _ _ _ => hom_unique hz _ _, fun n _ a b => ?_⟩,
      h₃ _ l.A_pos _ rfl, fun _ => hom_unique hz _ _, fun _ _ => hom_unique hz _ _⟩
    have e : unitOn (ζ n ^ D.EF a b) = 1 := by
      rw [Subsingleton.elim b 0, map_zero, zpow_zero, unitOn, map_one]
    rw [e]
    exact weilIs_zero hz (Inhab.zeroTriple H S).PP.isLB (triv_rig hz _) _ _ _

theorem isIso_obj (hc : Count) (hD : D.p + D.q = 0) {l : Level H} {B : Type} [CommRing B] {b : Base l B}
    {S : Scheme.{0}} [IsReduced S] {s : S ⟶ Sp B} (o : Obj D l b s) : IsIso o.t.G.hom := by
  refine isIso_of_no_torsion hc _ ⟨o.t.semi.comm, o.t.semi.smooth, o.proper, o.t.semi.geomConnected⟩ fun k _ _ x => ?_
  obtain ⟨β, hβ⟩ := exists_spMap (x ≫ s)
  obtain ⟨-, I, -⟩ := o.geom k x β hβ
  have := subsingleton_La hD
  refine ⟨2, one_lt_two, ?_, fun g hg => ?_⟩
  · have := ((b.unit 2 two_pos).map β).ne_zero
    rwa [map_natCast] at this
  · obtain ⟨a, rfl⟩ := (I.onto 2 two_pos g).1 hg
    exact (I.ker 2 two_pos a).2 ⟨0, Subsingleton.elim _ _⟩

theorem nonempty_objMap {l : Level H} {B B' : Type} [CommRing B] [CommRing B'] {b : Base l B} {b' : Base l B'}
    {S S' : Scheme.{0}} {s : S ⟶ Sp B} {s' : S' ⟶ Sp B'} {o' : Obj D l b' s'} {o : Obj D l b s}
    (h' : IsIso o'.t.G.hom) (h : IsIso o.t.G.hom) (f : S' ⟶ S) : Nonempty (ObjMap o' o f) := by
  obtain ⟨m⟩ := nonempty_sabMap h' h f
  exact ⟨⟨m, fun _ => sec_comm h m.cart.1.w _ _, fun _ => sec_comm h m.cart.1.w _ _⟩⟩

def zeroModuli (hc : Count) (hD : D.p + D.q = 0) (l : Level H) : Moduli D l where
  X := Sp (KA l)
  s := 𝟙 _
  qproj := isQProjOver_of_isIso _ inferInstance
  smooth := by
    have : D.dim = 0 := by rw [Datum.dim, show D.q = 0 by omega, mul_zero]
    rw [this]
    infer_instance
  univ := zeroObj hD l _
  rep := fun S s' _ o => ⟨s', ⟨Category.comp_id _, nonempty_objMap (isIso_obj hc hD o) (isIso_zeroTriple _) _⟩,
    fun f hf => (Category.comp_id f).symm.trans hf.1⟩
  unram := fun k _ x _ _ _ =>
    have := BaseRing.finiteDimensional_KA l
    eq_constPt_field x

theorem isIso_moduli (hc : Count) (hD : D.p + D.q = 0) {l : Level H} (Xo : Moduli D l) :
    IsIso Xo.s ∧ IsIso Xo.univ.t.G.hom := by
  have := Xo.smooth
  have : Smooth Xo.s := SmoothOfRelativeDimension.smooth D.dim Xo.s
  have hr : IsReduced Xo.X := isReduced_of_smooth_of_isReduced Xo.s
  have h := isIso_obj hc hD Xo.univ
  obtain ⟨g, ⟨hg, -⟩, -⟩ := Xo.rep (Sp (KA l)) (𝟙 _) inferInstance (zeroObj hD l _)
  refine ⟨⟨g, (Xo.rep _ Xo.s hr Xo.univ).unique ⟨?_, nonempty_objMap h h _⟩ ⟨Category.id_comp _, nonempty_objMap h h _⟩,
    hg⟩, h⟩
  rw [Category.assoc, hg, Category.comp_id]

end Objects

section Siegel

variable {N : ℕ} {B B' : Type} [CommRing B] [CommRing B'] {ζ : B} {ζ' : B'} {S S' : Scheme.{0}}

def zeroSieg (N : ℕ) (ζ : B) (s : S ⟶ Sp B) : SiegPre 0 N ζ s where
  A := 𝟙_ _
  ab := UU.isAbelianScheme_unit S
  P := Out.Inh.trivLB _
  isLB := Out.Inh.trivLB_isLB _
  rig₁ := (triv_trivLB _).linComb _ _
  rig₂ := (triv_trivLB _).linComb _ _
  symm := (triv_trivLB _).lbIso ((triv_trivLB _).linComb _ _)
  lev := fun _ => 1
  lev_add := fun _ _ => (_root_.mul_one _).symm
  lev_tors := fun _ => one_pow _
  geom := fun k _ _ x β z _ _ => by
    refine ⟨fun a => ⟨fun _ => ⟨0, Subsingleton.elim _ _⟩, fun _ => toUnit_unique _ _⟩,
      fun _ _ => ⟨0, toUnit_unique _ _⟩, fun a b => ?_⟩
    have e : unitOn (z ^ (2 * omegaStd a b)) = 1 := by
      rw [omegaStd, Fin.sum_univ_zero, mul_zero, zpow_zero, unitOn, map_one]
    rw [e]
    exact weilIs_zero (isIso_unit S) (pull_isLB (Out.Inh.trivLB_isLB _) _) ((triv_trivLB _).linComb _ _) _ _ _

theorem principal_zeroSieg {R : Type} [CommRing R] (s : Sp R ⟶ Sp B) : (zeroSieg N ζ s).Principal := by
  refine ⟨?_, fun _ _ _ => toUnit_unique _ _⟩
  obtain ⟨w, hw⟩ : LBIso (zeroSieg N ζ s).diag ((Out.Inh.trivLB _).pull (𝟙 _)) :=
    ((triv_trivLB _).linComb _ _).lbIso ((triv_trivLB _).linComb _ _)
  exact relAmple_pull (A := 𝟙_ _) (f := 𝟙 _) (φ := 𝟙 _)
    (IsPullback.of_horiz_isIso ⟨(Category.id_comp _).trans (Category.comp_id _).symm⟩) (Out.Inh.trivLB_isLB _)
    (pull_isLB (Out.Inh.trivLB_isLB _) _) ((isGen_iff w).1 hw) ⊤ (isAffineOpen_top _) (fun _ => trivial)
    (Out.Inh.zeroPolAV _).ample

theorem siegPB_zero {h : ℕ} {s : S ⟶ Sp B} {s' : S' ⟶ Sp B'} {o' : SiegPre h N ζ' s'} {o : SiegPre h N ζ s}
    (h' : IsIso o'.A.hom) (h : IsIso o.A.hom) (f : S' ⟶ S) : SiegPB o' o f :=
  ⟨_, _, isGrpPullback_zero h' h f, isSquare_zero h f,
    (triv_of_pull h' (isIso_tensor h' h') _ o'.rig₁).lbIso ((triv_of_pull h (isIso_tensor h h) _ o.rig₁).linComb _ _),
    fun _ => sec_comm h (zmap_w h f) _ _⟩

theorem natCast_mul_inv {p N n : ℕ} (hp : p.Prime) (hn : n.Coprime p) (h : (n : ℂ)⁻¹ ∈ ZP p N) :
    (n : ZP p N) * ⟨_, h⟩ = 1 := by
  have : n ≠ 0 := by
    rintro rfl
    exact hp.one_lt.ne' (Nat.coprime_zero_left _ |>.1 hn)
  exact Subtype.ext (by simpa using mul_inv_cancel₀ (Nat.cast_ne_zero.2 this : (n : ℂ) ≠ 0))

theorem isUnit_natCast {p N n : ℕ} (hp : p.Prime) (hn : n.Coprime p) : IsUnit (n : ZP p N) :=
  IsUnit.of_mul_eq_one _ (natCast_mul_inv hp hn (Subring.subset_closure (Or.inr ⟨n, hn, rfl⟩)))

theorem zeta_pow_eq_one (p : ℕ) (hN : 0 < N) : zetaZP p N ^ N = 1 := Subtype.ext (BaseRing.zeta_pow_self hN)

theorem isIso_sieg (hc : Count) {p : ℕ} (hp : p.Prime) (h₁ : 1 < N) (hN : N.Coprime p) [IsReduced S]
    {s : S ⟶ Sp (ZP p N)} (o : SiegPre 0 N (zetaZP p N) s) : IsIso o.A.hom := by
  refine isIso_of_no_torsion hc _ o.ab fun k _ _ x => ?_
  obtain ⟨β, hβ⟩ := exists_spMap (x ≫ s)
  have hu : IsUnit (β (zetaZP p N)) :=
    ((isUnit_pow_iff (by omega : N ≠ 0)).1 (zeta_pow_eq_one p (by omega : 0 < N) ▸ isUnit_one)).map β
  obtain ⟨e₁, e₂, -⟩ := o.geom k x β hu.unit hβ rfl
  refine ⟨N, h₁, ?_, fun g hg => ?_⟩
  · have := ((isUnit_natCast (N := N) hp hN).map β).ne_zero
    rwa [map_natCast] at this
  · obtain ⟨a, rfl⟩ := e₂ g hg
    exact (e₁ a).2 ⟨0, Subsingleton.elim _ _⟩

theorem eq_constPt_ZP {p : ℕ} (hp : p.Prime) (h₁ : 0 < N) (hN : N.Coprime p) {k : Type} [Field k]
    (x : Sp (DualNumber k) ⟶ Sp (ZP p N)) : x = constPt x := by
  refine eq_constPt_of x fun β => ?_
  generalize hδ : ((algebraMap k (DualNumber k)).comp (TrivSqZeroExt.fstHom k k k).toRingHom).comp β = δ
  refine RingHom.ext fun ⟨y, hy⟩ => ?_
  induction hy using Subring.closure_induction with
  | mem y hy =>
    rcases hy with rfl | ⟨n, hn, rfl⟩
    · subst hδ
      have hz : β (zetaZP p N) ^ N = 1 := by rw [← map_pow, zeta_pow_eq_one p h₁, map_one]
      have hk : (N : k) ≠ 0 := by
        have := (((isUnit_natCast (N := N) hp hN).map β).map (TrivSqZeroExt.fstHom k k k)).ne_zero
        rwa [map_natCast, map_natCast] at this
      have ha : (β (zetaZP p N)).fst ≠ 0 := fun h0 => by
        have := congrArg TrivSqZeroExt.fst hz
        rw [TrivSqZeroExt.fst_pow, h0, zero_pow h₁.ne', TrivSqZeroExt.fst_one] at this
        exact zero_ne_one this
      have hb := congrArg TrivSqZeroExt.snd hz
      rw [TrivSqZeroExt.snd_pow, TrivSqZeroExt.snd_one, nsmul_eq_mul, smul_eq_mul] at hb
      have hb' := (mul_eq_zero.1 ((mul_eq_zero.1 hb).resolve_left hk)).resolve_left (pow_ne_zero _ ha)
      exact TrivSqZeroExt.ext (x := β (zetaZP p N)) rfl hb'
    · have e := natCast_mul_inv (N := N) hp hn (Subring.subset_closure (Or.inr ⟨n, hn, rfl⟩))
      have e₁ := congrArg β e
      have e₂ := congrArg δ e
      rw [map_mul, map_natCast, map_one] at e₁ e₂
      exact left_inv_eq_right_inv ((mul_comm _ _).trans e₁) e₂
  | zero => exact (map_zero β).trans (map_zero δ).symm
  | one => exact (map_one β).trans (map_one δ).symm
  | add a b ha hb h h' =>
    exact (map_add β ⟨a, ha⟩ ⟨b, hb⟩).trans ((congrArg₂ (· + ·) h h').trans (map_add δ ⟨a, ha⟩ ⟨b, hb⟩).symm)
  | neg a ha h => exact (map_neg β ⟨a, ha⟩).trans ((congrArg (- ·) h).trans (map_neg δ ⟨a, ha⟩).symm)
  | mul a b ha hb h h' =>
    exact (map_mul β ⟨a, ha⟩ ⟨b, hb⟩).trans ((congrArg₂ (· * ·) h h').trans (map_mul δ ⟨a, ha⟩ ⟨b, hb⟩).symm)

def zeroFamily (hc : Count) {p : ℕ} (hp : p.Prime) (h₁ : 1 < N) (hN : N.Coprime p) : SiegelFamily 0 p N where
  X := Sp (ZP p N)
  s := 𝟙 _
  smooth := inferInstanceAs (SmoothOfRelativeDimension 0 (𝟙 _))
  qc := inferInstance
  univ := zeroSieg _ _ _
  princ := principal_zeroSieg _
  points := fun C O _ _ _ _ _ _ _ _ hO _ β o _ _ =>
    have : _root_.IsReduced O := isReduced_of_injective (algebraMap O C) hO.1
    ⟨spMap β, Category.comp_id _, siegPB_zero (isIso_sieg hc hp h₁ hN o) (isIso_unit _) _⟩
  unram := fun _ _ x _ _ _ => eq_constPt_ZP hp (by omega) hN x

end Siegel

section Full

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {n N : ℕ}

def inc (n : ℕ) (l : Level H) (h : l.A = N) : RZ H n N →+* KA l :=
  (RZ H n N).subtype.codRestrict (KA l) fun x => BaseRing.RZ_le_KA l n (h ▸ x.2)

theorem eq_inc {l : Level H} (h : l.A = N) {β : RZ H n N →+* KA l}
    (hβ : IsInc (RZ H n N).subtype (KA l).val.toRingHom β) : β = inc n l h :=
  RingHom.ext fun x => Subtype.ext (hβ x)

theorem map_inc_mem {l : Level H} (h : l.A = N) (σ : KA l →+* KA l) (hσ : σ (baseKA l).ρ = (baseKA l).ρ)
    (x : RZ H n N) : ((σ (inc n l h x) : KA l) : ℂ) ∈ RZ H n N := by
  obtain ⟨y, hy⟩ := x
  induction hy using Subring.closure_induction with
  | mem y hy =>
    rcases hy with rfl | rfl | rfl
    · show ((σ ((1 + (baseKA l).ρ) / 2) : KA l) : ℂ) ∈ _
      rw [map_div₀, map_add, map_one, hσ, map_ofNat]
      exact Subring.subset_closure (Or.inl rfl)
    · show ((σ ((n : KA l)⁻¹) : KA l) : ℂ) ∈ _
      rw [map_inv₀, map_natCast]
      exact Subring.subset_closure (Or.inr (Or.inl rfl))
    · subst h
      have : NeZero l.A := ⟨l.A_pos.ne'⟩
      obtain ⟨i, -, hi⟩ := (baseKA l).ζ_prim.eq_pow_of_pow_eq_one (ξ := σ (baseKA l).ζ)
        (by rw [← map_pow, (baseKA l).ζ_prim.pow_eq_one, map_one])
      show ((σ (baseKA l).ζ : KA l) : ℂ) ∈ _
      rw [← hi]
      exact pow_mem (Subring.subset_closure (Or.inr (Or.inr rfl)) : zeta l.A ∈ RZ H n l.A) i
  | zero => exact (congrArg Subtype.val (map_zero (σ.comp (inc n l h)))).symm ▸ zero_mem _
  | one => exact (congrArg Subtype.val (map_one (σ.comp (inc n l h)))).symm ▸ one_mem _
  | add a b ha hb h₁ h₂ =>
    exact (congrArg Subtype.val (map_add (σ.comp (inc n l h)) ⟨a, ha⟩ ⟨b, hb⟩)).symm ▸ add_mem h₁ h₂
  | neg a ha h₁ => exact (congrArg Subtype.val (map_neg (σ.comp (inc n l h)) ⟨a, ha⟩)).symm ▸ neg_mem h₁
  | mul a b ha hb h₁ h₂ =>
    exact (congrArg Subtype.val (map_mul (σ.comp (inc n l h)) ⟨a, ha⟩ ⟨b, hb⟩)).symm ▸ mul_mem h₁ h₂

def restr {l : Level H} (h : l.A = N) (σ : KA l →+* KA l) (hσ : σ (baseKA l).ρ = (baseKA l).ρ) :
    RZ H n N →+* RZ H n N :=
  ((KA l).val.toRingHom.comp (σ.comp (inc n l h))).codRestrict _ (map_inc_mem h σ hσ)

theorem restr_comp {l : Level H} (h : l.A = N) (σ τ : KA l →+* KA l) (hσ : σ (baseKA l).ρ = (baseKA l).ρ)
    (hτ : τ (baseKA l).ρ = (baseKA l).ρ) (e : ∀ x, σ (τ x) = x) :
    spMap (restr (n := n) h σ hσ) ≫ spMap (restr h τ hτ) = 𝟙 _ := by
  have : (restr (n := n) h σ hσ).comp (restr h τ hτ) = RingHom.id _ :=
    RingHom.ext fun x => Subtype.ext (congrArg (fun y : KA l => (y : ℂ)) (e (inc n l h x)))
  rw [spMap_comp, this]
  exact Spec.map_id _

theorem isIso_top (X : Scheme.{0}) : IsIso (⊤ : X.Opens).ι := inferInstanceAs (IsIso X.topIso.hom)

theorem siegel_zero (hc : Count) (hD : D.p + D.q = 0) {g p : ℕ} (hg : g = 0) (hp : p.Prime) (h₁ : 1 < N)
    (hN : N.Coprime p) : ∃ (Ag : SiegelFamily g p N) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] D.La),
      (∀ x y, D.EF (bas x) (bas y) = omegaStd x y) ∧
      ∀ (O : Type) [CommRing O] (z : ZP p N →+* O) (T : Scheme.{0}) (sT : T ⟶ Sp O) (tT : SAB H T)
        (levT : D.La → (𝟙_ (Over T) ⟶ tT.G)), IsIso sT → IsIso tT.G.hom →
        ∃ w : T ⟶ pullback Ag.s (spMap z), SiegData sT tT levT Ag z bas w ∧ IsFinite w ∧ FormallyUnramified w := by
  subst hg
  have := subsingleton_La hD
  refine ⟨zeroFamily hc hp h₁ hN, LinearEquiv.ofSubsingleton _ _, fun x y => ?_, fun O _ z T sT tT levT hs ht => ?_⟩
  · rw [omegaStd, Fin.sum_univ_zero, Subsingleton.elim (LinearEquiv.ofSubsingleton _ _ y) (0 : D.La), map_zero]
  · have : IsIso (zeroFamily hc hp h₁ hN).s := inferInstanceAs (IsIso (𝟙 _))
    refine ⟨sT ≫ inv (pullback.snd _ _), ⟨zeroSieg _ _ _, _, _, isGrpPullback_zero (isIso_unit T) ht _,
      isSquare_zero ht _, (triv_trivLB _).lbIso (((triv_rig ht _).linComb _ _).linComb _ _),
      fun _ => (sec_comm ht (zmap_w ht _) _ _).trans (Category.id_comp _), by simp,
      siegPB_zero (isIso_unit _) (isIso_unit _) _⟩, inferInstance, inferInstance⟩

theorem nonempty_top (hc : Count) (hD : D.p + D.q = 0) (Xo : ∀ l : Level H, Moduli D l) {J : ℕ} (hn : n.Prime)
    (hJ : 1 ≤ J) : Nonempty (Top Xo n (n ^ J)) := by
  have h₁ : 1 < n ^ J := Nat.one_lt_pow (by omega) hn.one_lt
  have : IsDedekindDomain (RZ H n (n ^ J)) :=
    BaseRing.isDedekindDomain_RZ (HostModel.level H (n ^ J) (by omega)) hn.pos (dvd_refl (n ^ J))
  let Z := Sp (RZ H n (n ^ J))
  have hz := isIso_zeroTriple (H := H) Z
  have hab : abLocus (Inhab.zeroTriple H Z).G = Set.univ := Inhab.abLocus_eq_univ _ (Inhab.isProper_zeroTriple Z)
  have htop := isIso_top Z
  have hX := fun l => isIso_moduli hc hD (Xo l)
  let m : ∀ l h, SABMap (Xo l).univ.t (Inhab.zeroTriple H Z) ((Xo l).s ≫ spMap (inc n l h)) :=
    fun l h => (nonempty_sabMap (hX l).2 hz _).some
  obtain ⟨mU⟩ := nonempty_sabMap (isIso_zeroTriple (H := H) (⊤ : Z.Opens).toScheme) hz (⊤ : Z.Opens).ι
  refine ⟨{ Z := Z, s := 𝟙 _, normal := ZJ.isNormalScheme_sp _, proj := Inhab.isProjOver_id _, flat := inferInstance
            t := Inhab.zeroTriple H Z, qproj := isQProjOver_of_isIso _ inferInstance
            good := Inhab.good_zeroTriple Z, ga := hab ▸ Set.subset_univ _
            a := fun l h => (Xo l).s ≫ spMap (inc n l h), m := m
            fin := fun l h β hβ => ?_, compat := fun l l' h h' r ν k hk hr _ => ?_
            sym := fun l h r _ _ σ hσ hr _ => ?_
            U := ⊤, U_eq := hab.symm, MM := Z, sM := 𝟙 _, tM := Inhab.zeroTriple H Z, lev := fun _ => 1
            MM_red := inferInstance, MM_flat := inferInstance, MM_ab := Inhab.isProper_zeroTriple Z
            u := (⊤ : Z.Opens).ι, u_over := rfl, u_fin := inferInstance, u_surj := inferInstance
            u_gen := ⟨⊤, fun _ _ => trivial, inferInstance⟩
            tU := Inhab.zeroTriple H _, mU := mU, mM := mU
            lev_eq := fun l h a' x y ha hy => ?_, sieg := fun p hp hpn => ?_ }⟩
  · obtain rfl := eq_inc h hβ
    have := (hX l).1
    have := isIso_top (pullback (𝟙 Z) (spMap (inc n l h)))
    refine ⟨⊤, (Xo l).s ≫ inv (pullback.snd _ _) ≫ inv (Scheme.Opens.ι ⊤), by rw [hab]; rfl, inferInstance,
      inferInstance, ?_, by simp⟩
    have e : pullback.fst (𝟙 Z) (spMap (inc n l h)) = pullback.snd _ _ ≫ spMap (inc n l h) :=
      (Category.comp_id _).symm.trans pullback.condition
    rw [e]
    simp
  · have e : r ≫ (Xo l).s ≫ spMap (inc n l h) = (Xo l').s ≫ spMap (inc n l' h') := by
      rw [← Category.assoc, hr, Category.assoc, spMap_comp, eq_inc h' (β := k.comp (inc n l h)) fun x => hk _]
    refine ⟨e, left_unique hz ?_⟩
    rw [Category.assoc, (m l h).cart.1.w, (m l' h').cart.1.w, ← Category.assoc, ν.cart.1.w, Category.assoc, e]
  · have hσ' : σ.symm (baseKA l).ρ = (baseKA l).ρ := σ.symm_apply_eq.2 hσ.symm
    refine ⟨⟨spMap (restr h σ.toRingHom hσ), spMap (restr h σ.symm.toRingHom hσ'),
      restr_comp h _ _ _ _ σ.apply_symm_apply, restr_comp h _ _ _ _ σ.symm_apply_apply⟩, ?_⟩
    rw [← Category.assoc, hr, Category.assoc, Category.assoc, spMap_comp, spMap_comp]
    rfl
  · rw [← Category.assoc, ha]
    exact hy.trans (sec_comm hz (m l h).cart.1.w _ _)
  · obtain ⟨Ag, bas, e₁, e₂⟩ := siegel_zero (H := H) hc hD (g := Module.finrank ℚ E / 2 * (D.p + D.q))
      (by rw [hD, mul_zero]) hp h₁ (((Nat.coprime_primes hn hp).2 hpn.symm).pow_left J)
    exact ⟨Ag, bas, e₁, fun O _ _ z b _ _ _ T sT f tT ν levT hpb _ => e₂ O z T sT tT levT
      (MorphismProperty.of_isPullback (P := MorphismProperty.isomorphisms _) hpb (inferInstanceAs (IsIso (𝟙 Z))))
      (MorphismProperty.of_isPullback (P := MorphismProperty.isomorphisms _) ν.cart.1 hz)⟩

end Full

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H), D.p + D.q = 0 → Nonempty (∀ l : Level H, Moduli D l) ∧ ∀ (Xo : ∀ l : Level H, Moduli D l) (n J : ℕ), AuxiliaryInertOddPrime H n → 1 ≤ J → Nonempty (Top Xo n (n ^ J)) :=
  fun _ _ _ _ _ _ hD => ⟨⟨zeroModuli GlobalTheory.card_torsion_abelianVariety hD⟩, fun Xo _ _ hn hJ => nonempty_top GlobalTheory.card_torsion_abelianVariety hD Xo hn.1 hJ⟩

end GlobalTheory.Models.RankZero

end
