import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LnStepFalse
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AffineOpenChartCompStructureEqSpMap
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LieLatticeLocalBasisDescription
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentModuleLocallyFreeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralPointOfLocalCoverStatement

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj
open GlobalTheory.TrueGeo GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.Toroidal GlobalTheory.LocM.Frm GlobalTheory.HeightParts
open GlobalTheory.GradedNorm GlobalTheory.LieHt
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.LieSmooth

set_option autoImplicit false
noncomputable section
open MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LieCover

theorem bcTan_congr {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}} {t : SAB H X} {S T : Type} [CommRing S] [CommRing T] {φ φ' : S →+* T} (e : φ = φ') {x : Sp S ⟶ X} {x' : Sp T ⟶ X} (h : spMap φ ≫ x = x') (h' : spMap φ' ≫ x = x') (v : TanM x t.G) :
    bcTan (t := t) φ h v = bcTan φ' h' v := by
  subst e; rfl

theorem bcTan_bcTan {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}} {t : SAB H X} {S T U : Type} [CommRing S] [CommRing T] [CommRing U] (φ : S →+* T) (ψ : T →+* U) {x : Sp S ⟶ X} {x' : Sp T ⟶ X} {x'' : Sp U ⟶ X} (h1 : spMap φ ≫ x = x') (h2 : spMap ψ ≫ x' = x'') (h3 : spMap (ψ.comp φ) ≫ x = x'') (v : TanM x t.G) :
    bcTan ψ h2 (bcTan φ h1 v) = bcTan (ψ.comp φ) h3 v :=
  GlobalTheory.LieMet.tan_ext (by rw [left_bcTan, left_bcTan, left_bcTan, GlobalTheory.FlagMod.dualMap_comp, ← spMap_comp', Category.assoc])

theorem bcTan_eq_tanPull {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}} {t : SAB H X} {S T : Type} [CommRing S] [CommRing T] (φ : S →+* T) {x : Sp S ⟶ X} {x' : Sp T ⟶ X} (h : spMap φ ≫ x = x') (v : TanM x t.G) :
    bcTan φ h v = GlobalTheory.FlagMod.tanPull φ h v :=
  GlobalTheory.LieMet.tan_ext (by rw [left_bcTan, GlobalTheory.FlagMod.tanPull_left])

theorem sum_comb {k M : Type} [CommRing k] [AddCommGroup M] [Module k M] {n m : ℕ} (x : Fin m → k) (Y : Fin m → Fin n → k) (u : Fin n → M) :
    ∑ q, (∑ s, x s • Y s) q • u q = ∑ s, x s • ∑ q, Y s q • u q := by
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_smul, Finset.smul_sum, smul_smul]
  exact Finset.sum_comm

end GlobalTheory.LieCover

open GlobalTheory.LieCover in

theorem GlobalTheory.LieCover.exists_cover_lieCoordLat : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}} (t : SAB H X) {K : Type} [Field K] [NumberField K] {xO : Sp (𝓞 K) ⟶ X} {xK : Sp K ⟶ X} (hx : spMap (algebraMap (𝓞 K) K) ≫ xO = xK) {n : ℕ} (b : Fin n → TanM xK t.G), TanBasis t b → ∃ (m : ℕ) (r : Fin m → 𝓞 K) (M : Fin m → Matrix (Fin n) (Fin n) K), Ideal.span (Set.range r) = ⊤ ∧ (∀ i, r i ≠ 0 ∧ (M i).det ≠ 0) ∧ (∀ c, c ∈ lieCoordLat t hx b ↔ ∀ i, ∃ (k : ℕ) (a : Fin n → 𝓞 K), r i ^ k • c = ∑ j, a j • M i j) ∧ ∀ (i : Fin m) (S : Type) [CommRing S] (ψ : 𝓞 K →+* S), IsUnit (ψ (r i)) → ∀ (T : Type) [Field T] (ι' : S →+* T) (j : K →+* T), ι'.comp ψ = j.comp (algebraMap (𝓞 K) K) → ∀ (xT : Sp T ⟶ X) (hT : spMap j ≫ xK = xT) (vO : Sp (DualNumber S) ⟶ t.G.left), IsTanAtG t (spMap ψ ≫ xO) vO → ∃ a : Fin n → S, spMap (dualMap ι') ≫ vO = combLeft t (fun q => bcTan j hT (b q)) (∑ s, ι' (a s) • fun q => j (M i s q)) := by
  intro E _ _ _ H X t K _ _ xO xK hx n b hb
  classical
  obtain ⟨hb1, hb2⟩ := hb
  have hinj : Function.Injective (algebraMap (𝓞 K) K) := IsFractionRing.injective _ _
  obtain ⟨m, r, hr, hQ⟩ := GlobalTheory.CM.LieGlue.exists_finite_cover _ (GlobalTheory.T.tangent_module_locally_free t xO)
  choose hr0 d D hli hsp using hQ
  have hu : ∀ i, IsUnit (algebraMap (𝓞 K) K (r i)) := fun i => ((map_ne_zero_iff _ hinj).2 (hr0 i)).isUnit
  let g : ∀ i, Localization.Away (r i) →+* K := fun i => IsLocalization.Away.lift (r i) (hu i)
  have hg : ∀ i, (g i).comp (algebraMap (𝓞 K) _) = algebraMap (𝓞 K) K := fun i => IsLocalization.Away.lift_comp _ _
  have hxi : ∀ i, spMap (g i) ≫ spMap (algebraMap (𝓞 K) (Localization.Away (r i))) ≫ xO = xK := fun i => by
    rw [← Category.assoc, spMap_comp', hg i, hx]
  let bb : Module.Basis (Fin n) K (TanM xK t.G) := Module.Basis.mk hb1 hb2.ge
  have hbb : ∀ q, bb q = b q := fun q => Module.Basis.mk_apply _ _ q
  let B : ∀ i, Module.Basis (Fin (d i)) (Localization.Away (r i)) (TanM (spMap (algebraMap (𝓞 K) (Localization.Away (r i))) ≫ xO) t.G) :=
    fun i => Module.Basis.mk (hli i) (hsp i).ge
  let BK : ∀ i, Module.Basis (Fin (d i)) K (TanM xK t.G) := fun i => GlobalTheory.DRFlag.basPull (g i) (hxi i) (B i)
  let ei : ∀ i, Fin (d i) ≃ Fin n := fun i => (BK i).indexEquiv bb
  let B' : ∀ i, Module.Basis (Fin n) (Localization.Away (r i)) (TanM (spMap (algebraMap (𝓞 K) (Localization.Away (r i))) ≫ xO) t.G) :=
    fun i => (B i).reindex (ei i)
  let C : ∀ i, Module.Basis (Fin n) K (TanM xK t.G) := fun i => (BK i).reindex (ei i)
  have hC : ∀ i s, C i s = bcTan (g i) (hxi i) (B' i s) := fun i s => by
    simp only [C, B', BK, Module.Basis.reindex_apply, GlobalTheory.DRFlag.basPull_apply, bcTan_eq_tanPull]
  let M : Fin m → Matrix (Fin n) (Fin n) K := fun i s q => bb.repr (C i s) q
  have hM : ∀ i s, C i s = ∑ q, M i s q • b q := fun i s => by
    simp only [M, ← hbb]; exact (bb.sum_repr _).symm
  have hdet : ∀ i, (M i).det ≠ 0 := fun i => by
    have e : M i = (bb.toMatrix (C i)).transpose := by ext s q; rfl
    letI := bb.invertibleToMatrix (C i)
    rw [e, Matrix.det_transpose]
    exact (Matrix.isUnit_det_of_invertible _).ne_zero
  clear_value M C B' ei BK B
  have key : ∀ i (a : Fin n → Localization.Away (r i)),
      bcTan (g i) (hxi i) (∑ s, a s • B' i s) = ∑ q, (∑ s, g i (a s) • M i s) q • b q := fun i a => by
    refine Eq.trans ?_ (sum_comb (fun s => g i (a s)) (fun s => M i s) b).symm
    rw [map_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [map_smulₛₗ, ← hC i s, hM i s]
  have lin : ∀ c c' : Fin n → K, ∑ q, c q • b q = ∑ q, c' q • b q → c = c' := fun c c' h =>
    funext (Fintype.linearIndependent_iffₛ.1 hb1 c c' h)
  refine ⟨m, r, M, hr, fun i => ⟨hr0 i, hdet i⟩, fun c => ?_, ?_⟩
  · simp only [← fun i => GlobalTheory.CM.LieGlue.exists_comb_iff (r i) (g i) (hg i) (M i) c]
    constructor
    · rintro ⟨w, hw⟩ i
      refine ⟨(B' i).repr (bcTan (algebraMap (𝓞 K) (Localization.Away (r i))) rfl w), ?_⟩
      apply lin
      rw [← key, (B' i).sum_repr, bcTan_bcTan _ _ _ _ (by rw [hg i, hx]), ← hw]
      exact (bcTan_congr (hg i) _ _ _).symm
    · intro hc
      choose a ha using hc
      obtain ⟨v, hv⟩ := GlobalTheory.T.integral_point_of_local_cover t (algebraMap (𝓞 K) K) hinj r hr g hg hx hxi (∑ q, c q • b q)
        (fun i => ∑ s, a i s • B' i s) (fun i => by rw [key, ← ha i])
      exact ⟨v, hv⟩
  · intro i S _ ψ hψu T _ ι' j hιj xT hT vO hvO
    let ψ' : Localization.Away (r i) →+* S := IsLocalization.Away.lift (r i) hψu
    have hψ' : ψ'.comp (algebraMap (𝓞 K) _) = ψ := IsLocalization.Away.lift_comp _ _
    have h1 : spMap ψ' ≫ spMap (algebraMap (𝓞 K) (Localization.Away (r i))) ≫ xO = spMap ψ ≫ xO := by
      rw [← Category.assoc, spMap_comp', hψ']
    have h2 : spMap ι' ≫ spMap ψ ≫ xO = xT := by
      rw [← Category.assoc, spMap_comp', hιj, ← spMap_comp', Category.assoc, hx, hT]
    let BS := GlobalTheory.DRFlag.basPull ψ' h1 (B' i)
    let V := GlobalTheory.LieMet.tanOf hvO
    obtain ⟨a, hV⟩ : ∃ a : Fin n → S, V = ∑ s, a s • bcTan ψ' h1 (B' i s) := ⟨BS.repr V, by
      conv_lhs => rw [← BS.sum_repr V]
      simp only [BS, GlobalTheory.DRFlag.basPull_apply, bcTan_eq_tanPull]⟩
    have hring : ι'.comp ψ' = j.comp (g i) := IsLocalization.ringHom_ext (Submonoid.powers (r i)) (by
      rw [RingHom.comp_assoc, hψ', hιj, RingHom.comp_assoc, hg i])
    refine ⟨a, ?_⟩
    have e1 : spMap (dualMap ι') ≫ vO = (tv (bcTan ι' h2 V)).left := by
      rw [left_bcTan, GlobalTheory.LieMet.left_tanOf]
    rw [e1, combLeft]
    congr 2
    refine Eq.trans ?_ (sum_comb (fun s => ι' (a s)) (fun s q => j (M i s q)) (fun q => bcTan j hT (b q))).symm
    rw [hV, map_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    have h3 : spMap (ι'.comp ψ') ≫ spMap (algebraMap (𝓞 K) (Localization.Away (r i))) ≫ xO = xT := by
      rw [← spMap_comp', Category.assoc, h1, h2]
    rw [map_smulₛₗ, bcTan_bcTan (t := t) ψ' ι' h1 h2 h3 (B' i s)]
    congr 1
    have e2 : bcTan j hT (C i s) = ∑ q, j (M i s q) • bcTan j hT (b q) := by
      rw [hM i s, map_sum]; exact Finset.sum_congr rfl fun q _ => map_smulₛₗ _ _ _
    have h4 : spMap (j.comp (g i)) ≫ spMap (algebraMap (𝓞 K) (Localization.Away (r i))) ≫ xO = xT := by
      rw [← spMap_comp', Category.assoc, hxi i, hT]
    exact (bcTan_congr hring h3 h4 (B' i s)).trans ((bcTan_bcTan (t := t) (g i) j (hxi i) hT h4 (B' i s)).symm.trans
      ((congrArg (bcTan j hT) (hC i s)).symm.trans e2))
