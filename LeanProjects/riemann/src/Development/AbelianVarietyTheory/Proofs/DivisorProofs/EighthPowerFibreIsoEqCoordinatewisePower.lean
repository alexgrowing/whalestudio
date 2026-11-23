import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsChartMember
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AmpleRigidLevelRigid
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.FinitePointsOfIsOpenImmersion
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAbelianSchemeAndRelDimOfIsGrpPullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeEighthPowerProductMonHomStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EighthPowerIsoDiagonalOfLPowerTorsionActionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreIsoGrpPullbackIdentityTransportStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.PoincDiag

@[reassoc]
theorem mapFst {S S' : Scheme.{0}} (t : S' ⟶ S) {X Y : Over S} (φ : X ⟶ Y) :
    ((Over.pullback t).map φ).left ≫ pullback.fst Y.hom t = pullback.fst X.hom t ≫ φ.left := by
  simp only [Over.pullback_map_left]; exact pullback.lift_fst _ _ _

@[reassoc]
theorem mapSnd {S S' : Scheme.{0}} (t : S' ⟶ S) {X Y : Over S} (φ : X ⟶ Y) :
    ((Over.pullback t).map φ).left ≫ pullback.snd Y.hom t = pullback.snd X.hom t := by
  simp only [Over.pullback_map_left]; exact pullback.lift_snd _ _ _

theorem abBC : ∀ (R R' : Type) [CommRing R] [CommRing R'] (f : R →+* R') (B : Over (Sp R)) [GrpObj B] (g : ℕ), IsAbelianScheme B → SmoothOfRelativeDimension g B.hom → IsAbelianScheme ((Over.pullback (spMap f)).obj B) ∧ SmoothOfRelativeDimension g ((Over.pullback (spMap f)).obj B).hom := by
  intro R R' _ _ f B _ g hB hd
  exact GlobalTheory.AbBaseChange.isAbelianScheme_and_relDim_of_isGrpPullback f B _ _ g
    (ReciprocityTheory.ChartRestriction.G.Geo.Tor.isGrpPullback_pullback B (spMap f)) hB hd

theorem torsPull : ∀ (S S' : Scheme.{0}) (t : S' ⟶ S) (X : Over S) [GrpObj X] (z : 𝟙_ (Over S') ⟶ (Over.pullback t).obj X) (y : Over.mk t ⟶ X) (n : ℕ), y.left = z.left ≫ pullback.fst X.hom t → z ^ n = 1 → y ^ n = 1 := by
  intro S S' t X _ z y n hy hz
  have hgp := ReciprocityTheory.ChartRestriction.G.Geo.Tor.isGrpPullback_pullback X t
  let k : Over.mk ((𝟙_ (Over S')).hom ≫ t) ⟶ Over.mk t := Over.homMk (𝟙 _) (by simp)
  have hw : ((1 : 𝟙_ (Over S') ⟶ (Over.pullback t).obj X).left ≫ pullback.fst X.hom t) ≫ X.hom = (Over.mk t).hom := by
    have e := Over.w (1 : 𝟙_ (Over S') ⟶ (Over.pullback t).obj X)
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    simp only [Over.pullback_obj_hom] at e
    rw [e]
    simp
  let u : Over.mk t ⟶ X := Over.homMk ((1 : 𝟙_ (Over S') ⟶ (Over.pullback t).obj X).left ≫ pullback.fst X.hom t) hw
  have hu : u = 1 := by
    have h := hgp.2 (𝟙_ (Over S')) 1 1 (k ≫ u) (k ≫ u) (by simp [k, u]) (by simp [k, u])
    rw [← MonObj.comp_mul, _root_.mul_one] at h
    have e : u * u = u := Over.OverMorphism.ext (by simpa [k, u] using h)
    exact mul_eq_left.1 e
  have hp : ∀ m : ℕ, (y ^ m).left = (z ^ m).left ≫ pullback.fst X.hom t := by
    intro m
    induction m with
    | zero =>
      simp only [pow_zero]
      rw [← hu]
      rfl
    | succ m ih =>
      have h := hgp.2 (𝟙_ (Over S')) (z ^ m) z (k ≫ y ^ m) (k ≫ y) (by simp [k, ih]) (by simp [k, hy])
      rw [← MonObj.comp_mul, ← pow_succ, ← pow_succ] at h
      simpa [k] using h
  apply Over.OverMorphism.ext
  rw [hp n, hz, ← hu]
  rfl

theorem fibreIso_eq_pow : ∀ (l : ℕ), l.Prime → Odd l → ∀ W : Matrix (Fin 8) (Fin 8) ℤ, IsE8 W → ∀ j, 1 ≤ j → ∀ (V V₁ : Type) [CommRing V] [IsDomain V] [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsUnit (l : V₁) → ∀ (Q : Data V) (ρ : V →+* V₁), Function.Injective ρ → ∀ (D : DegPre V₁), ∀ (pr : Fin 8 → (D.P.A ⟶ (Over.pullback (spMap ρ)).obj Q.B)) (w : LB.Iso D.P.L (LB.LinComb Q.M.L (K := (Fin 8 × Fin 8) × Fin 4) (fun k => lamPts (pr k.1.1) (pr k.1.2) k.2 ≫ pullback.fst Q.B.hom (spMap ρ)) (fun k => -(W k.1.1 k.1.2 * negε k.2)))), (∀ a, IsMonHom (pr a)) → (∀ (T : Over (Sp V₁)) (y : Fin 8 → (T ⟶ (Over.pullback (spMap ρ)).obj Q.B)), ∃! x : T ⟶ D.P.A, ∀ a, x ≫ pr a = y a) → w.IsGen → ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (σ : K ≃+* K), ∀ (f : ((Over.pullback (spMap ev)).obj D.P.A).left ⟶ ((Over.pullback (spMap (σ.toRingHom.comp ev))).obj D.P.A).left), IsGrpPullback ((Over.pullback (spMap ev)).obj D.P.A) ((Over.pullback (spMap (σ.toRingHom.comp ev))).obj D.P.A) (𝟙 _) f → LBIso (D.P.L.pull (pullback.fst D.P.A.hom (spMap ev))) (D.P.L.pull (f ≫ pullback.fst D.P.A.hom (spMap (σ.toRingHom.comp ev)))) → (∀ (y : Over.mk (spMap ev) ⟶ D.P.A), (∃ k : ℕ, y ^ (l ^ k) = 1) → ∀ q : Sp K ⟶ ((Over.pullback (spMap ev)).obj D.P.A).left, q ≫ pullback.fst D.P.A.hom (spMap ev) = y.left → q ≫ pullback.snd D.P.A.hom (spMap ev) = 𝟙 _ → q ≫ f ≫ pullback.fst D.P.A.hom (spMap (σ.toRingHom.comp ev)) = spMap σ.toRingHom ≫ y.left) → ∃ f₁ : ((Over.pullback (spMap (ev.comp ρ))).obj Q.B).left ⟶ ((Over.pullback (spMap (σ.toRingHom.comp (ev.comp ρ)))).obj Q.B).left, IsGrpPullback ((Over.pullback (spMap (ev.comp ρ))).obj Q.B) ((Over.pullback (spMap (σ.toRingHom.comp (ev.comp ρ)))).obj Q.B) (𝟙 _) f₁ ∧ ∀ (a : Fin 8) (T : Scheme.{0}) (x : T ⟶ ((Over.pullback (spMap ev)).obj D.P.A).left) (y : T ⟶ ((Over.pullback (spMap (ev.comp ρ))).obj Q.B).left), y ≫ pullback.fst Q.B.hom (spMap (ev.comp ρ)) = x ≫ pullback.fst D.P.A.hom (spMap ev) ≫ (pr a).left ≫ pullback.fst Q.B.hom (spMap ρ) → y ≫ pullback.snd Q.B.hom (spMap (ev.comp ρ)) = x ≫ pullback.snd D.P.A.hom (spMap ev) → x ≫ f ≫ pullback.fst D.P.A.hom (spMap (σ.toRingHom.comp ev)) ≫ (pr a).left ≫ pullback.fst Q.B.hom (spMap ρ) = y ≫ f₁ ≫ pullback.fst Q.B.hom (spMap (σ.toRingHom.comp (ev.comp ρ))) := by
  intro l hl hodd W hW j hj V V₁ _ _ _ _ _ hlu Q ρ hρ D pr w hpr huniv hw K _ _ ev σ f hf hL htor
  haveI := D.P.isAb.comm
  have hfw : f ≫ ((Over.pullback (spMap (σ.toRingHom.comp ev))).obj D.P.A).hom = ((Over.pullback (spMap ev)).obj D.P.A).hom := by
    simpa using hf.1.w
  let F : (Over.pullback (spMap ev)).obj D.P.A ⟶ (Over.pullback (spMap (σ.toRingHom.comp ev))).obj D.P.A := Over.homMk f hfw
  haveI : IsIso f := hf.1.isIso_fst_of_isIso
  haveI hFi : IsIso F := by
    have : IsIso ((Over.forget _).map F) := by change IsIso f; infer_instance
    exact isIso_of_reflects_iso F (Over.forget _)
  haveI hFm : IsMonHom F := GlobalTheory.AmpleRigid.isMonHom_of_mul_comp F
    (fun T x y => GlobalTheory.AmpleRigid.mul_comp_of_grpPullback_id F hf x y)
  obtain ⟨hm₀, hu₀⟩ := GlobalTheory.T.isMonHom_pullback_pr_and_unique_lift_fin_eight _ _ (spMap ev) D.P.A _ pr hpr huniv
  obtain ⟨hm₁, hu₁⟩ := GlobalTheory.T.isMonHom_pullback_pr_and_unique_lift_fin_eight _ _ (spMap (σ.toRingHom.comp ev)) D.P.A _ pr hpr huniv
  have hBab := abBC V V₁ ρ Q.B Q.g Q.isAb Q.smoothDim
  have hB₀ := (abBC V₁ K ev _ Q.g hBab.1 hBab.2).1
  have hB₁ := (abBC V₁ K (σ.toRingHom.comp ev) _ Q.g hBab.1 hBab.2).1
  have hlK : (l : K) ≠ 0 := by
    have := hlu.map ev
    rw [map_natCast] at this
    exact this.ne_zero

  have key : ∀ (z : 𝟙_ (Over (Sp K)) ⟶ (Over.pullback (spMap ev)).obj D.P.A), (∃ k : ℕ, z ^ (l ^ k) = 1) → ∀ a,
      (z ≫ F ≫ (Over.pullback (spMap (σ.toRingHom.comp ev))).map (pr a)).left ≫
          pullback.fst ((Over.pullback (spMap ρ)).obj Q.B).hom (spMap (σ.toRingHom.comp ev)) =
        spMap σ.toRingHom ≫ (z ≫ (Over.pullback (spMap ev)).map (pr a)).left ≫
          pullback.fst ((Over.pullback (spMap ρ)).obj Q.B).hom (spMap ev) := by
    rintro z ⟨k, hk⟩ a
    have hzw : z.left ≫ pullback.snd D.P.A.hom (spMap ev) = 𝟙 _ := by simpa using Over.w z
    have hyw : (z.left ≫ pullback.fst D.P.A.hom (spMap ev)) ≫ D.P.A.hom = (Over.mk (spMap ev)).hom := by
      rw [Category.assoc, pullback.condition, ← Category.assoc, hzw, Category.id_comp]; rfl
    let y : Over.mk (spMap ev) ⟶ D.P.A := Over.homMk (z.left ≫ pullback.fst D.P.A.hom (spMap ev)) hyw
    have hy : y ^ (l ^ k) = 1 := torsPull _ _ (spMap ev) D.P.A z y (l ^ k) rfl hk
    have h := htor y ⟨k, hy⟩ z.left rfl hzw
    simp only [Over.comp_left, Category.assoc]
    rw [mapFst, mapFst]
    change z.left ≫ f ≫ _ = _
    rw [reassoc_of% h]
    rfl
  have htors : ∀ (z z' : 𝟙_ (Over (Sp K)) ⟶ (Over.pullback (spMap ev)).obj D.P.A), (∃ k : ℕ, z ^ (l ^ k) = 1) →
      (∃ k : ℕ, z' ^ (l ^ k) = 1) → ∀ a a', z ≫ (Over.pullback (spMap ev)).map (pr a) = z' ≫ (Over.pullback (spMap ev)).map (pr a') →
      z ≫ F ≫ (Over.pullback (spMap (σ.toRingHom.comp ev))).map (pr a) = z' ≫ F ≫ (Over.pullback (spMap (σ.toRingHom.comp ev))).map (pr a') := by
    intro z z' hz hz' a a' he
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · rw [key z hz a, key z' hz' a', he]
    · exact (Over.w (z ≫ F ≫ (Over.pullback (spMap (σ.toRingHom.comp ev))).map (pr a))).trans
        (Over.w (z' ≫ F ≫ (Over.pullback (spMap (σ.toRingHom.comp ev))).map (pr a'))).symm
  obtain ⟨f₁', hm, hiso, hco⟩ := GlobalTheory.T.eighthPower_iso_diagonal_of_lPower_torsion_action K _ _ _ _ (GlobalTheory.isSemiAbelian_of_isAbelianScheme _ hB₀)
    (GlobalTheory.isSemiAbelian_of_isAbelianScheme _ hB₁) l hl hlK _ _ hm₀ hm₁ hu₀ hu₁ F hFm hFi htors
  obtain ⟨f₁, hf₁, hcoord⟩ := GlobalTheory.T.fibre_iso_grpPullback_identity_transport V V₁ K Q.B ρ ev σ f₁' hm hiso
  refine ⟨f₁, hf₁, fun a T x y h1 h2 => ?_⟩
  have hc : f ≫ ((Over.pullback (spMap (σ.toRingHom.comp ev))).map (pr a)).left =
      ((Over.pullback (spMap ev)).map (pr a)).left ≫ f₁'.left := congrArg (·.left) (hco a)
  have := hcoord T (x ≫ ((Over.pullback (spMap ev)).map (pr a)).left) y
    (by rw [h1, Category.assoc, mapFst_assoc]) (by rw [h2, Category.assoc, mapSnd])
  rw [← this, Category.assoc, ← reassoc_of% hc, mapFst_assoc]

end GlobalTheory.PoincDiag
