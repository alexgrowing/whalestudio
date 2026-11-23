import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusInvariantHeatOperatorPreservesWeight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRaynaudTorusWeightFunctionInvariantFieldStatement
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AwayToAwayRightEqOfComp
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TangentBijectionOfValues
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.NonemptyTorusExtensionOfIsGt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUnitCharts
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LieBridgeG
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Heat.CoeffWt

open GlobalTheory.ZH.CrdCalc (valR_res valR_spMap)
open ReciprocityTheory.ChartRestriction.G.Chart (sp)
open TrivSqZeroExt (inl inr)

section Group

variable {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] {n : ℕ}

theorem isGrpPullback_self {S : Scheme.{0}} (G : Over S) [GrpObj G] : IsGrpPullback G G (𝟙 S) (𝟙 G.left) := by
  refine ⟨IsPullback.of_horiz_isIso ⟨by simp⟩, fun T x y x₀ y₀ hx hy => ?_⟩
  let ρ : Over.mk (T.hom ≫ 𝟙 S) ⟶ T := Over.homMk (𝟙 T.left) (by simp)
  have ex : x₀ = ρ ≫ x := Over.OverMorphism.ext (hx.trans ((Category.comp_id _).trans (Category.id_comp _).symm))
  have ey : y₀ = ρ ≫ y := Over.OverMorphism.ext (hy.trans ((Category.comp_id _).trans (Category.id_comp _).symm))
  rw [ex, ey, ← MonObj.comp_mul]
  exact (Category.id_comp _).trans (Category.comp_id _).symm

theorem exists_isLieBasis (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) G)) :
    ∃ u : Fin n → (epsR R ⟶ G), IsLieBasis u ∧ ∀ i, (u i).left = (tv (v i)).left := by
  have h := isGrpPullback_self G
  choose u e using fun i => PullbackSections.push_surj h (tv (v i))
  have ts : ∀ f : Fin n → TanM (𝟙 (Sp R)) G, tv (∑ i, f i) = ∏ i, tv (f i) := fun f => by
    simp only [tv, toMul_sum, Subgroup.val_finset_prod]
  have key : ∀ a p m, pushHom h (epsR R) p = tv m → (IsLieComb a u p ↔ m = ∑ k, a k • v k) := fun a p m hp => by
    rw [PullbackSections.isLieComb_iff h, hp]
    simp only [e]
    exact ⟨fun q => PullbackSections.tanM_ext (q.trans (by rw [ts]; rfl)), fun q => (congrArg tv q).trans (by rw [ts]; rfl)⟩
  refine ⟨u, ⟨fun i => (PullbackSections.isTangent_iff h _).2 (by rw [e]; exact PullbackSections.tv_mem _), fun p hp => ?_⟩,
    fun i => (Category.comp_id _).symm.trans (congrArg (fun q => q.left) (e i))⟩
  simp only [key _ p (PullbackSections.mkT _ ((PullbackSections.isTangent_iff h p).1 hp)) rfl]
  refine ⟨v.repr _, (v.sum_repr _).symm, fun c hc => ?_⟩
  rw [hc]
  funext i
  simp [Finsupp.single_apply]

theorem top_le_of_fst {B : Type} [CommRing B] {X : Scheme.{0}} (w : Sp (DualNumber B) ⟶ X) (O : X.Opens)
    (h : ⊤ ≤ (spMap (TrivSqZeroExt.fstHom B B B).toRingHom ≫ w) ⁻¹ᵁ O) : ⊤ ≤ w ⁻¹ᵁ O := by
  intro p _
  have hs : Function.Surjective (PrimeSpectrum.comap (TrivSqZeroExt.fstHom B B B).toRingHom) := by
    rw [← Set.range_eq_univ, range_comap_of_surjective _ _ (fun s => ⟨inl s, rfl⟩), PrimeSpectrum.zeroLocus_eq_univ_iff]
    intro a ha
    exact GlobalTheory.SqZero.nil_of_fstS (R := B) a ha
  obtain ⟨q, rfl⟩ := hs p
  exact h (Set.mem_univ q)

variable {B : Type} [CommRing B] [Algebra R B]

theorem valR_translate {v : TanM (𝟙 (Sp R)) G} {u : epsR R ⟶ G} (hu : u.left = (tv v).left) (ht : IsTangent u)
    {dd : Fld G.left} (hd : IsInv G v dd) (e : B) (he : e * e = 0) (z : sp (R₀ := R) B ⟶ G) (O : G.left.Opens)
    (h : ⊤ ≤ z.left ⁻¹ᵁ O) :
    ⊤ ≤ ((Chart.spMap (SqZero.epsTo R e he) ≫ u : sp (R₀ := R) B ⟶ G) * z).left ⁻¹ᵁ O ∧ ∀ f,
      valR (A := B) ((Chart.spMap (SqZero.epsTo R e he) ≫ u : sp (R₀ := R) B ⟶ G) * z).left O f =
        valR (A := B) z.left O f + e * valR (A := B) z.left O (dd O f) := by
  have hz : z.left ≫ G.hom = spMap (algebraMap R B) := Over.w z
  let w : sp (R₀ := R) (DualNumber B) ⟶ G :=
    (Chart.spMap (SqZero.inlS R B) ≫ z) * (Chart.spMap (SqZero.dualMap (Algebra.ofId R B)) ≫ u)
  have hw : IsTr G (algebraMap R B) z.left v w.left := by
    let ρ : tEpsG (z.left ≫ G.hom) ⟶ sp (R₀ := R) (DualNumber B) := Over.homMk (𝟙 _) (by
      rw [hz]
      refine (Category.id_comp _).trans ?_
      exact (Spec.map_comp (CommRingCat.ofHom (algebraMap R B)) (CommRingCat.ofHom (algebraMap B (DualNumber B)))))
    refine ⟨ρ ≫ Chart.spMap (SqZero.inlS R B) ≫ z, ρ ≫ Chart.spMap (SqZero.dualMap (Algebra.ofId R B)) ≫ u,
      Category.id_comp _, (Category.id_comp _).trans ?_, ?_⟩
    · rw [← hu]
      refine congrArg (fun q : DualNumber R →+* DualNumber B => spMap q ≫ u.left) (RingHom.ext fun a => ?_)
      ext <;> simp [dualMap, Algebra.smul_def, TrivSqZeroExt.algebraMap_eq_inl]
    · rw [← MonObj.comp_mul]
      exact Category.id_comp _
  have h0 : Chart.spMap (SqZero.fstS R B) ≫ w = z := by
    rw [MonObj.comp_mul, ← Category.assoc, ← Category.assoc, Chart.spMap_comp, Chart.spMap_comp,
      SqZero.fstS_comp_dualMap, ← Chart.spMap_comp (SqZero.fstS R R), Category.assoc,
      show Chart.spMap (SqZero.fstS R R) ≫ u = 1 from (Chart.isTan_iff _).2 ht, MonObj.comp_one, _root_.mul_one,
      show (SqZero.fstS R B).comp (SqZero.inlS R B) = AlgHom.id R B from AlgHom.ext fun _ => rfl, Chart.spMap_id,
      Category.id_comp]
  have h0' : spMap (TrivSqZeroExt.fstHom B B B).toRingHom ≫ w.left = z.left := congrArg (fun q => q.left) h0
  have hwO : ⊤ ≤ w.left ⁻¹ᵁ O := top_le_of_fst (B := B) w.left O (by rw [h0']; exact h)
  have h1 : Chart.spMap (SqZero.dualTo (AlgHom.id R B) e he) ≫ w =
      (Chart.spMap (SqZero.epsTo R e he) ≫ u : sp (R₀ := R) B ⟶ G) * z := by
    rw [MonObj.comp_mul, ← Category.assoc, ← Category.assoc, Chart.spMap_comp, Chart.spMap_comp,
      show (SqZero.dualTo (AlgHom.id R B) e he).comp (SqZero.inlS R B) = AlgHom.id R B from
        AlgHom.ext fun _ => by simp [SqZero.dualTo_apply], Chart.spMap_id, Category.id_comp, _root_.mul_comm,
      show (SqZero.dualTo (AlgHom.id R B) e he).comp (SqZero.dualMap (Algebra.ofId R B)) = SqZero.epsTo R e he from
        AlgHom.ext fun _ => by simp [SqZero.dualTo_apply, SqZero.epsTo]]
  rw [← h1]
  obtain ⟨a₁, a₂⟩ := valR_spMap (SqZero.dualTo (AlgHom.id R B) e he).toRingHom w.left O hwO
  refine ⟨a₁, fun f => (a₂ f).trans ?_⟩
  have b₁ := (valR_spMap (TrivSqZeroExt.fstHom B B B).toRingHom w.left O hwO).2 f
  rw [h0'] at b₁
  rw [← hd.2 B (algebraMap R B) z.left w.left O f hz h hw, b₁, _root_.mul_comm]
  rfl

theorem valR_prod {v : Fin n → TanM (𝟙 (Sp R)) G} {u : Fin n → (epsR R ⟶ G)} (hu : ∀ i, (u i).left = (tv (v i)).left)
    (ht : ∀ i, IsTangent (u i)) {dd : Fin n → Fld G.left} (hd : ∀ i, IsInv G (v i) (dd i)) (e : Fin n → B)
    (he : ∀ i j, e i * e j = 0) (z : sp (R₀ := R) B ⟶ G) (O : G.left.Opens) (h : ⊤ ≤ z.left ⁻¹ᵁ O) (s : Finset (Fin n)) :
    ⊤ ≤ ((∏ i ∈ s, (Chart.spMap (SqZero.epsTo R (e i) (he i i)) ≫ u i : sp (R₀ := R) B ⟶ G)) * z).left ⁻¹ᵁ O ∧ ∀ f,
      valR (A := B) ((∏ i ∈ s, (Chart.spMap (SqZero.epsTo R (e i) (he i i)) ≫ u i : sp (R₀ := R) B ⟶ G)) * z).left O f =
        valR (A := B) z.left O f + ∑ i ∈ s, e i * valR (A := B) z.left O (dd i O f) := by
  induction s using Finset.induction_on with
  | empty => simpa using h
  | insert a s ha ih =>
    obtain ⟨h₁, H₁⟩ := ih
    obtain ⟨h₂, H₂⟩ := valR_translate (hu a) (ht a) (hd a) (e a) (he a a) _ O h₁
    rw [Finset.prod_insert ha, _root_.mul_assoc]
    refine ⟨h₂, fun f => ?_⟩
    rw [H₂, H₁, H₁, Finset.sum_insert ha, mul_add, Finset.mul_sum]
    simp only [← _root_.mul_assoc, he, zero_mul, Finset.sum_const_zero]
    ring

theorem exists_tangent [Smooth G.hom] (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) G)) {dd : Fin n → Fld G.left}
    (hd : ∀ i, IsInv G (v i) (dd i)) (z : sp (R₀ := R) B ⟶ G) (e : Fin n → B) :
    ∃ w w' : sp (R₀ := R) (DualNumber B) ⟶ G, (w = w' → e = 0) ∧ ∀ O, ⊤ ≤ z.left ⁻¹ᵁ O →
      ⊤ ≤ w.left ⁻¹ᵁ O ∧ ⊤ ≤ w'.left ⁻¹ᵁ O ∧ ∀ f, ∑ i, e i * valR (A := B) z.left O (dd i O f) = 0 →
        valR (A := DualNumber B) w.left O f = valR (A := DualNumber B) w'.left O f := by
  obtain ⟨u, hb, hu⟩ := exists_isLieBasis v
  refine ⟨SqZero.tanExp u e * (Chart.spMap (SqZero.inlS R B) ≫ z), Chart.spMap (SqZero.inlS R B) ≫ z, fun h => ?_,
    fun O h => ?_⟩
  · have h1 : SqZero.tanExp u e = SqZero.tanExp u 0 := (mul_eq_right.1 h).trans
      (SqZero.lieExp_eq_one hb.1 _ (fun _ => rfl) _).symm
    have := (SqZero.expBij (DualNumber B) hb _ (SqZero.ker_fst_sq (R := R) (S := B) B)).1 _ _
      (fun _ => rfl) (fun _ => rfl) _ _ h1
    exact funext fun i => congrArg TrivSqZeroExt.snd (congrFun this i)
  · obtain ⟨a₁, a₂⟩ := valR_spMap (SqZero.inlS R B).toRingHom z.left O h
    obtain ⟨b₁, b₂⟩ := valR_prod hu hb.1 hd (fun i => (inr (e i) : DualNumber B))
      (fun _ _ => TrivSqZeroExt.inr_mul_inr _ _ _) (Chart.spMap (SqZero.inlS R B) ≫ z) O a₁ Finset.univ
    refine ⟨b₁, a₁, fun f hf => (b₂ f).trans (add_eq_left.2 ?_)⟩
    have a₃ : ∀ g, valR (A := DualNumber B) (Chart.spMap (SqZero.inlS R B) ≫ z).left O g =
      inl (valR (A := B) z.left O g) := a₂
    simp only [a₃]
    ext
    · simp [TrivSqZeroExt.fst_sum]
    · simpa [TrivSqZeroExt.snd_sum, _root_.mul_comm] using hf

end Group

section Raynaud

open GlobalTheory.TorusModel (cv pt_ext isPull_iff)

theorem gs_valR {S : Type} [CommRing S] {X : Scheme.{0}} (b : Sp S ⟶ X) {V W : X.Opens} (hV : V ≤ W)
    (hb : ⊤ ≤ b ⁻¹ᵁ V) (s : Γ(X, W)) (z : Sp S) :
    gs (𝟙 _) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom (valR b V (rsT s V))) = gs b z W s := by
  rw [valR, dif_pos hb, Iso.hom_inv_id_apply, rsT, dif_pos hV]
  refine (gs_res (𝟙 _) z hb trivial _).trans ((gs_pull (𝟙 _) b z V (hb trivial) _).trans ?_)
  rw [Category.id_comp]
  exact gs_res b z hV (hb trivial) _

theorem valR_app {S : Type} [CommRing S] {X Z : Scheme.{0}} (b : Sp S ⟶ X) (q : X ⟶ Z) (V : Z.Opens)
    (hb : ⊤ ≤ b ⁻¹ᵁ (q ⁻¹ᵁ V)) (g : Γ(Z, V)) : valR b (q ⁻¹ᵁ V) ((q.app V).hom g) = valR (b ≫ q) V g := by
  have hb' : ⊤ ≤ (b ≫ q) ⁻¹ᵁ V := hb
  rw [valR, valR, dif_pos hb, dif_pos hb']
  rfl

theorem gm_comp' {X Y Z : Scheme.{0}} (r : Z ⟶ Y) (q : Y ⟶ X) (z : Z) (U : X.Opens) (h : q (r z) ∈ U) (a : Γ(X, U)ˣ) :
    gm (r ≫ q) z U a = Units.map (r.stalkMap z).hom.toMonoidHom (gm q (r z) U a) := by
  refine Units.ext ?_
  rw [← gs_unit (r ≫ q) z U h, ← gs_pull r q z U h, gs_stalkMap r z (q ⁻¹ᵁ U) h, gs_pull (𝟙 Y) q (r z) U h,
    Category.id_comp, gs_unit q (r z) U h]
  rfl

variable {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O Q.X]
  {oa : Q.OAct O} (Y : Ray oa)

theorem comp_gtφT {T T' : Over (Sp R)} (ρ : T' ⟶ T) (b : T ⟶ Q.P.A) (χ : Q.X) (k : Fin 4) :
    ρ.left ≫ DegPre.gtφT Q T b χ k = DegPre.gtφT Q T' (ρ ≫ b) χ k := by
  fin_cases k
  · exact congrArg (fun q => q.left) ((MonObj.comp_mul ρ (DVR.cP Q T χ) b).trans
      (congrArg (· * (ρ ≫ b)) (DVR.comp_cP Q ρ χ)))
  · exact congrArg (fun q => q.left) (DVR.comp_cP Q ρ χ)
  · rfl
  · exact congrArg (fun q : T' ⟶ Q.P.A => q.left) (MonObj.comp_one ρ)

theorem cv_eq {T : Over (Sp R)} (x : T ⟶ Y.H) (b : T ⟶ Q.P.A) (hb : x ≫ Y.q = b) (χ : Q.X) (j : Fin 4 → Q.P.L.ι)
    (y : T.left) (J) (hJ : Good Q.P.L y J) (hy : x.left y ∈ LB.wchart Q.P.L (DegPre.gtφT Q Y.H Y.q χ) j) :
    cv (Y.Φ T x) χ y J = trF (DegPre.gtφT Q T b χ) DegPre.gtε (𝟙 _) y (fun k => J (DegPre.gtφT Q T b χ k)) j *
      gm x.left y (LB.wchart Q.P.L (DegPre.gtφT Q Y.H Y.q χ) j) (((Y.Φ Y.H (𝟙 _)).s χ).s j) := by
  subst hb
  have h := ((isPull_iff _ _ _).1 (Y.rep.1 T Y.H x (𝟙 _))).2 χ y J hJ
  rw [Category.comp_id] at h
  refine h.trans ((gen_trans ((Y.Φ Y.H (𝟙 _)).isGen χ) x.left y (hJ.mem _ _) hy).trans ?_)
  congr 1
  refine Finset.prod_congr rfl fun k _ => ?_
  have e := comp_gtφT x Y.q χ k
  beta_reduce
  rw [Category.id_comp, ← e]
  rfl

theorem isWt_app (V : Q.P.A.left.Opens) (g : Γ(Q.P.A.left, V)) :
    IsWt Y 0 (Y.q.left ⁻¹ᵁ V) ((Y.q.left.app V).hom g) := by
  intro S _ φ x x' c a a' ha ha' hV hV' hq hc
  have e : a' ≫ Y.q.left = a ≫ Y.q.left := by
    subst ha ha'
    exact congrArg (fun q => q.left) hq
  rw [valR_app _ _ _ hV', valR_app _ _ _ hV, e, WtAlg.c_zero x x' c hc, Units.val_one, _root_.one_mul]

theorem isWt_coord (χ : Q.X) (j : Fin 4 → Q.P.L.ι) (V : Y.H.left.Opens)
    (hV : V ≤ LB.wchart Q.P.L (DegPre.gtφT Q Y.H Y.q χ) j) :
    IsWt Y χ V (rsT (O₀ := LB.wchart Q.P.L (DegPre.gtφT Q Y.H Y.q χ) j) (((Y.Φ Y.H (𝟙 _)).s χ).s j).val V) := by
  intro S _ φ x x' c a a' ha ha' hV₁ hV₂ hq hc
  subst ha ha'
  apply (Scheme.ΓSpecIso (CommRingCat.of S)).commRingCatIsoToRingEquiv.symm.injective
  refine fn_ext fun z _ => ?_
  choose J hJ using fun ψ : Sp S ⟶ Q.P.A.left => exists_chart Q.P.isLB (ψ z)
  have t := hc χ z J hJ
  have m₁ := hV (hV₁ (show z ∈ (⊤ : (Sp S).Opens) from trivial))
  have m₂ := hV (hV₂ (show z ∈ (⊤ : (Sp S).Opens) from trivial))
  have t₁ := cv_eq Y x _ rfl χ j z J hJ m₁
  have t₂ := cv_eq Y x' _ hq χ j z J hJ m₂
  have t₃ := mul_left_cancel (t₂.symm.trans (t.trans ((congrArg (_ * ·) t₁).trans (_root_.mul_left_comm _ _ _))))
  show gs (𝟙 _) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom _) =
    gs (𝟙 _) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom _)
  refine (gs_valR (S := S) x'.left hV hV₂ _ z).trans (Eq.trans ?_
    ((congrArg (gs (𝟙 _) z ⊤) (map_mul _ _ _)).trans (gs_mul (𝟙 _) z ⊤ trivial _ _)).symm)
  exact (gs_unit _ z _ m₂ _).trans ((congrArg Units.val t₃).trans
    (congrArg₂ (· * ·) (gs_unit (𝟙 _) z ⊤ trivial (unitOn (c χ))).symm
      ((gs_unit _ z _ m₁ _).symm.trans (gs_valR (S := S) x.left hV hV₁ _ z).symm)))

theorem eq_of_valR {B : Type} [CommRing B] {ψ : R →+* B} (w w' : Over.mk (spMap ψ) ⟶ Y.H) (V : Q.P.A.left.Opens)
    (p : Y.H.left) (hp : p ∈ Y.q.left ⁻¹ᵁ V)
    (h : ∀ V', V' ≤ V → p ∈ Y.q.left ⁻¹ᵁ V' → ⊤ ≤ w.left ⁻¹ᵁ (Y.q.left ⁻¹ᵁ V') ∧ ⊤ ≤ w'.left ⁻¹ᵁ (Y.q.left ⁻¹ᵁ V') ∧
      ∀ α f, IsWt Y α (Y.q.left ⁻¹ᵁ V') f → valR (A := B) w.left _ f = valR (A := B) w'.left _ f) : w = w' := by
  have hq : w' ≫ Y.q = w ≫ Y.q := by
    obtain ⟨_, ⟨W, hW, rfl⟩, hx, hle⟩ := Q.P.A.left.isBasis_affineOpens.exists_subset_of_mem_open
      (show Y.q.left p ∈ V from hp) V.isOpen
    obtain ⟨h₁, h₂, h₃⟩ := h W hle hx
    refine Over.OverMorphism.ext (TangentOrigin.ext_evalPt (R := B) hW h₂ h₁ (RingHom.ext fun g => ?_))
    have := h₃ 0 _ (isWt_app Y W g)
    rw [valR_app (S := B) _ _ _ h₁, valR_app (S := B) _ _ _ h₂] at this
    exact (dif_pos h₂).symm.trans (this.symm.trans (dif_pos h₁))
  refine (Y.Φ _).injective (pt_ext (by rw [Y.Φ_b, Y.Φ_b, hq]) fun χ y J hJ => ?_)
  choose j hj using fun k => exists_chart Q.P.isLB (DegPre.gtφT Q Q.P.A (𝟙 _) χ k (Y.q.left p))
  obtain ⟨h₁, h₂, h₃⟩ := h (V ⊓ LB.wchart Q.P.L (DegPre.gtφT Q Q.P.A (𝟙 _) χ) j) inf_le_left
    ⟨hp, Set.mem_iInter.2 hj⟩
  have hV : Y.q.left ⁻¹ᵁ (V ⊓ LB.wchart Q.P.L (DegPre.gtφT Q Q.P.A (𝟙 _) χ) j) ≤
      LB.wchart Q.P.L (DegPre.gtφT Q Y.H Y.q χ) j := fun t ht => Set.mem_iInter.2 fun k => by
    have e := comp_gtφT Y.q (𝟙 _) χ k
    rw [Category.comp_id] at e
    rw [← e]
    exact Set.mem_iInter.1 ht.2 k
  have m₁ := hV (h₁ (show y ∈ (⊤ : (Sp B).Opens) from trivial))
  have m₂ := hV (h₂ (show y ∈ (⊤ : (Sp B).Opens) from trivial))
  rw [cv_eq Y w _ rfl χ j y J hJ m₁, cv_eq Y w' _ hq χ j y J hJ m₂]
  congr 1
  refine Units.ext ((gs_unit _ y _ m₁ _).symm.trans (Eq.trans ?_ (gs_unit _ y _ m₂ _)))
  refine (gs_valR (S := B) _ hV h₁ _ y).symm.trans (Eq.trans ?_ (gs_valR (S := B) _ hV h₂ _ y))
  rw [h₃ χ _ (isWt_coord Y χ j _ hV)]

theorem isWt_of_local (α : Q.X) (V : Y.H.left.Opens) (f : Γ(Y.H.left, V))
    (h : ∀ (S : Type) [CommRing S] [IsLocalRing S] (φ : R →+* S) (x x' : Over.mk (spMap φ) ⟶ Y.H) (c : Q.X → Sˣ),
      ⊤ ≤ x.left ⁻¹ᵁ V → ⊤ ≤ x'.left ⁻¹ᵁ V → x' ≫ Y.q = x ≫ Y.q →
      (∀ χ y J, Good Q.P.L y J → val ((Y.Φ _ x').s χ) (𝟙 _) y J =
        gm (𝟙 (Over.mk (spMap φ)).left) y ⊤ (unitOn (c χ)) * val ((Y.Φ _ x).s χ) (𝟙 _) y J) →
      valR (A := S) x'.left V f = c α * valR (A := S) x.left V f) : IsWt Y α V f := by
  intro S _ φ x x' c a a' ha ha' hV hV' hq hc
  subst ha ha'
  refine sub_eq_zero.1 (eq_zero_of_localization _ fun P hP => (map_sub _ _ _).trans (sub_eq_zero.2 ?_))
  let l := algebraMap S (Localization.AtPrime P)
  let k : Over.mk (spMap (l.comp φ)) ⟶ Over.mk (spMap φ) := Over.homMk (spMap l)
    (Spec.map_comp (CommRingCat.ofHom φ) (CommRingCat.ofHom l)).symm
  obtain ⟨a₁, a₂⟩ := valR_spMap l x.left V hV
  obtain ⟨b₁, b₂⟩ := valR_spMap l x'.left V hV'
  have := h _ (l.comp φ) (k ≫ x) (k ≫ x') (fun χ => Units.map l.toMonoidHom (c χ)) a₁ b₁
    (by rw [Category.assoc, Category.assoc, hq]) fun χ y J hJ => by
      have hJ' : Good Q.P.L (k.left y) fun ψ => J (k.left ≫ ψ) := fun ψ => hJ (k.left ≫ ψ)
      have key : ∀ u : Over.mk (spMap φ) ⟶ Y.H, val ((Y.Φ _ (k ≫ u)).s χ) (𝟙 _) y J =
          Units.map (k.left.stalkMap y).hom.toMonoidHom
            (val ((Y.Φ _ u).s χ) (𝟙 _) (k.left y) fun ψ => J (k.left ≫ ψ)) := fun u => by
        refine (((isPull_iff _ _ _).1 (Y.rep.1 _ _ k u)).2 χ y J hJ).trans ?_
        rw [val_of _ (𝟙 _) _ _ (fun i => J (k.left ≫ DegPre.gtφT Q _ (Y.Φ _ u).b χ i)) (fun i => by rw [Category.id_comp])]
        refine Eq.trans ?_ (gm_comp' k.left (𝟙 _) y _ (hJ.mem _ k.left) _)
        rw [Category.comp_id]
        rfl
      rw [key, key, hc χ _ _ hJ', map_mul, ← gm_comp' k.left (𝟙 _) y ⊤ trivial]
      congr 1
      refine Units.ext ?_
      rw [gm_val _ _ ⊤ trivial, gm_val _ _ ⊤ trivial]
      refine congrArg ((Sp (Localization.AtPrime P)).presheaf.germ ⊤ y trivial).hom ?_
      exact (congrArg (fun q => q.hom (c χ : S)) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom l))).symm
  rw [map_mul]
  exact (b₂ f).symm.trans (this.trans (congrArg (_ * ·) (a₂ f)))

end Raynaud

theorem isWt_coeff : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (v a) (dd a)) →
    ∀ (V : Q.P.A.left.Opens) (δ : Fld Y.H.left), IsField (Y.q.left ⁻¹ᵁ V) δ → (∀ O, O ≤ Y.q.left ⁻¹ᵁ V → ∀ r, δ O (constFn Y.H.hom O r) = 0) →
    (∀ (α : Q.X) (V' : Q.P.A.left.Opens), V' ≤ V → ∀ f, IsWt Y α (Y.q.left ⁻¹ᵁ V') f → IsWt Y α (Y.q.left ⁻¹ᵁ V') (δ _ f)) →
    ∀ c : Fin n → Γ(Y.H.left, Y.q.left ⁻¹ᵁ V), (∀ O, O ≤ Y.q.left ⁻¹ᵁ V → ∀ f, δ O f = ∑ a, rsT (c a) O * dd a O f) →
    ∀ a, IsWt Y 0 _ (c a) := by
  intro R _ _ Q O _ _ _ oa Y n v dd hd V δ _ _ hδ cf hcf a
  refine isWt_of_local Y 0 _ _ fun S _ _ φ x x' c hV hV' hq hc => ?_
  have : Smooth Y.H.hom := (GlobalTheory.isSemiAbelian_of_isGt _ _ _ Y.isGt).smooth
  letI : Algebra R S := φ.toAlgebra
  obtain ⟨w, w', h₀, h₁⟩ := exists_tangent (B := S) v hd x'
    fun i => valR (A := S) x'.left _ (cf i) - valR (A := S) x.left _ (cf i)
  have e : x'.left ≫ Y.q.left = x.left ≫ Y.q.left := congrArg (fun q => q.left) hq
  have := h₀ (eq_of_valR Y w w' V (x'.left (closedPoint S)) (hV' trivial) fun V' hle hp => by
    have m' : ⊤ ≤ x'.left ⁻¹ᵁ (Y.q.left ⁻¹ᵁ V') := (Scheme.preimage_eq_top_of_closedPoint_mem (R := .of S) x'.left hp).ge
    have m : ⊤ ≤ x.left ⁻¹ᵁ (Y.q.left ⁻¹ᵁ V') := by
      rw [← Scheme.Hom.comp_preimage, ← e]; exact m'
    have hle' : Y.q.left ⁻¹ᵁ V' ≤ Y.q.left ⁻¹ᵁ V := Y.q.left.preimage_mono hle
    obtain ⟨a₁, a₂, a₃⟩ := h₁ _ m'
    refine ⟨a₁, a₂, fun α f hf => a₃ f ?_⟩
    have ev : ∀ b : Sp S ⟶ Y.H.left, ⊤ ≤ b ⁻¹ᵁ (Y.q.left ⁻¹ᵁ V') →
        valR b _ (δ _ f) = ∑ i, valR b _ (cf i) * valR b _ (dd i _ f) := fun b hb => by
      rw [hcf _ hle', GlobalTheory.ZH.CrdCalc.valR_eq _ _ hb, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul, ← GlobalTheory.ZH.CrdCalc.valR_eq _ _ hb, ← GlobalTheory.ZH.CrdCalc.valR_eq _ _ hb, rsT, dif_pos hle', valR_res _ _ hb]
    have t := hδ α V' hle f hf S φ x x' c _ _ rfl rfl m m' hq hc
    have td := fun i => GlobalTheory.T.isRaynaudTorusWeightFunction_invariantField Y (v i) (dd i) (hd i) α _ f hf S φ x x' c _ _ rfl rfl m m' hq hc
    rw [ev _ m, ev _ m', Finset.mul_sum] at t
    simp only [sub_mul, Finset.sum_sub_distrib]
    refine sub_eq_zero.2 (t.trans (Finset.sum_congr rfl fun i _ => ?_))
    exact (_root_.mul_left_comm _ _ _).trans (congrArg (_ * ·) (td i).symm))
  rw [WtAlg.c_zero x x' c hc, Units.val_one, _root_.one_mul]
  exact sub_eq_zero.1 (congrFun this a)

end GlobalTheory.Heat.CoeffWt
