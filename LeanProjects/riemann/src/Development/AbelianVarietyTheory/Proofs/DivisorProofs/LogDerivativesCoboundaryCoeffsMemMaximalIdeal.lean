import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AwayToAwayRightEqOfComp
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUnitCharts
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.CommGroupCoboundaryRelationIdentity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjectiveSpMapFst
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LieBridgeG

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

namespace GlobalTheory.Heat.DlogIndep

open GlobalTheory.ZH.CrdCalc (valR_res valR_spMap valR_eq valHom)
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

end Group

open GlobalTheory.TangentCob ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF GlobalTheory.CubeFib GlobalTheory.AddCurve in

theorem eq_one_of_coboundary {k : Type} [CommRing k] {B : Over (Sp k)} [GrpObj B] {L : LB B.left}
    (hL : L.IsLB) (hK : KTriv B L) {D : Type} [CommRing D] [Algebra k D] (e : D) (he : e * e = 0)
    (x0 : algOver k D ⟶ B) (H : ∀ j, Γ(B.left, L.U j))
    (hx : ∀ (S : Type) [CommRing S] [Algebra k S] (φ : D →ₐ[k] S) (y : algOver k S ⟶ B) (U : B.left.Opens),
      ⊤ ≤ y.left ⁻¹ᵁ U → ⊤ ≤ ((algOverHom φ ≫ x0) * y).left ⁻¹ᵁ U)
    (h : ∀ (S : Type) [CommRing S] [Algebra k S] (φ : D →ₐ[k] S) (y : algOver k S ⟶ B) (j j' : L.ι),
      ⊤ ≤ y.left ⁻¹ᵁ L.U j → ⊤ ≤ y.left ⁻¹ᵁ L.U j' →
        valR (A := S) ((algOverHom φ ≫ x0) * y).left (L.U j ⊓ L.U j') (L.g j j').val =
          valR (A := S) y.left (L.U j ⊓ L.U j') (L.g j j').val *
            (1 + φ e * (valR (A := S) y.left (L.U j) (H j) - valR (A := S) y.left (L.U j') (H j')))) : x0 = 1 := by
  let T : Over (Sp k) := algOver k D
  let m : T ⊗ B ⟶ B := (fst T B ≫ x0) * snd T B
  let e0 : Γ(Sp D, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of D)).inv.hom e
  have he0 : e0 * e0 = 0 := (map_mul _ _ _).symm.trans ((congrArg _ he).trans (map_zero _))
  have pt : ∀ z : (T ⊗ B).left, ∃ (_ : Algebra k ((T ⊗ B).left.presheaf.stalk z))
      (φ : D →ₐ[k] (T ⊗ B).left.presheaf.stalk z) (y : algOver k ((T ⊗ B).left.presheaf.stalk z) ⟶ B),
      y.left = (T ⊗ B).left.fromSpecStalk z ≫ (snd T B).left ∧
      ((algOverHom φ ≫ x0) * y).left = (T ⊗ B).left.fromSpecStalk z ≫ m.left ∧
      φ e = gs (𝟙 _) z ⊤ (((fst T B).left.app ⊤).hom e0) := by
    intro z
    obtain ⟨i, φ, r, hr, hφ, hd⟩ := exists_alg (B := B) D (S := (T ⊗ B).left.presheaf.stalk z)
      ((T ⊗ B).left.fromSpecStalk z)
    refine ⟨i, φ, r ≫ snd T B, congrArg (· ≫ (snd T B).left) hr, ?_, ?_⟩
    · have : (algOverHom φ ≫ x0) * (r ≫ snd T B) = r ≫ m := by
        rw [← hφ, Category.assoc]
        exact (MonObj.comp_mul _ _ _).symm
      exact (congrArg (·.left) this).trans (congrArg (· ≫ m.left) hr)
    · exact (hd _).trans ((valR_stalk (fst T B).left z ⊤ trivial e0).trans
        (gs_pull (𝟙 _) (fst T B).left z ⊤ trivial e0).symm)
  have hmp : ∀ (z : (T ⊗ B).left) (U : B.left.Opens), (snd T B).left z ∈ U → m.left z ∈ U := by
    intro z U hz
    obtain ⟨_, φ, y, h1, h2, -⟩ := pt z
    have := hx _ φ y U (by rw [h1]; exact (top_le_stalk_iff _ z U).2 hz)
    rw [h2] at this
    exact (top_le_stalk_iff _ z U).1 this
  obtain ⟨c, hc⟩ := exists_isGen L hL m.left (snd T B).left (((fst T B).left.app ⊤).hom e0)
    ((map_mul _ _ _).symm.trans ((congrArg _ he0).trans (map_zero _))) H hmp (fun z j j' hj hj' => by
      obtain ⟨_, φ, y, h1, h2, h3⟩ := pt z
      have := h _ φ y j j' (by rw [h1]; exact (top_le_stalk_iff _ z _).2 hj)
        (by rw [h1]; exact (top_le_stalk_iff _ z _).2 hj')
      rw [h1, h2, h3] at this
      rw [← valR_stalk _ z _ hj, ← valR_stalk _ z _ hj', ← valR_stalk _ z (L.U j ⊓ L.U j') ⟨hj, hj'⟩,
        ← valR_stalk _ z (L.U j ⊓ L.U j') ⟨hmp z _ hj, hmp z _ hj'⟩]
      exact this)
  exact hK D _ x0 fun _ => ⟨⊤, trivial,
    gen_chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull (translDiff B L x0) _ _ rfl) c hc⟩

theorem pbT_id {X : Scheme.{0}} (O : X.Opens) (s : Γ(X, O)) : pbT (𝟙 X) s O = s := by
  rw [pbT, dif_pos (show O ≤ (𝟙 X : X ⟶ X) ⁻¹ᵁ O from le_rfl)]
  exact (congrArg (fun φ => φ.hom s) (Scheme.Hom.appLE_eq_app (𝟙 X) (U := O))).trans rfl

theorem mem_maximalIdeal_of_isCob : ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (B : Over (Sp A)) [GrpObj B] [IsCommMonObj B] (g : ℕ) (L : LB B.left), IsAbelianScheme B → SmoothOfRelativeDimension g B.hom → L.IsLB → RelAmple B L → KTriv B L → (∀ i, IsAffineOpen (L.U i)) → Finite L.ι → ∀ (v : Fin g → TanM (𝟙 (Sp A)) B) (dd : Fin g → Fld B.left), (∀ a, IsInv B (v a) (dd a)) → (∀ w : TanM (𝟙 (Sp A)) B, ∃! cf : Fin g → A, w = ∑ a, cf a • v a) → ∀ (c : Fin g → A) (N : ℕ) (t : Fin N → A) (z : Fin N → C1 L.U), (∀ k, t k ∈ maximalIdeal A) → IsCob L.U (fun i j => ∑ a, constFn B.hom _ (c a) * dlg B (𝟙 _) L (dd a) i j (L.U i ⊓ L.U j) - ∑ k, constFn B.hom _ (t k) * z k i j) → ∀ a, c a ∈ maximalIdeal A := by
  intro A _ _ _ B _ _ g L _ hs hL _ hK _ _ v dd hd hv c N t z ht ⟨b, hb⟩
  have : Smooth B.hom := SmoothOfRelativeDimension.smooth g B.hom
  let β : Module.Basis (Fin g) A (TanM (𝟙 (Sp A)) B) := Module.Basis.mk (v := v)
    (Fintype.linearIndependent_iff.2 fun a ha i => congrFun ((hv 0).unique ha.symm (y₂ := 0) (by simp)) i)
    (fun m _ => by
      obtain ⟨a, ha, -⟩ := hv m
      rw [ha]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))
  obtain ⟨u, hu, hl⟩ := exists_isLieBasis β
  simp only [β, Module.Basis.mk_apply] at hl
  let k := ResidueField A
  let e : Fin g → k := fun a => residue A (c a)
  have hφ : ∀ (S : Type) [CommRing S] [Algebra A S] (φ : DualNumber k →ₐ[A] S) (a : A),
      φ (inr (residue A a)) = φ DualNumber.eps * algebraMap A S a := fun S _ _ φ a => by
    rw [← φ.commutes, ← map_mul]
    congr 1
    ext
    · simp
    · simp [TrivSqZeroExt.algebraMap_eq_inl']
      rfl
  have key : ∀ (S : Type) [CommRing S] [Algebra A S] (φ : DualNumber k →ₐ[A] S) (y : sp (R₀ := A) S ⟶ B)
      (U : B.left.Opens), ⊤ ≤ y.left ⁻¹ᵁ U → ⊤ ≤ ((Chart.spMap φ ≫ SqZero.tanExp u e) * y).left ⁻¹ᵁ U ∧ ∀ f,
      valR (A := S) ((Chart.spMap φ ≫ SqZero.tanExp u e) * y).left U f =
        valR (A := S) y.left U f + ∑ i, φ (inr (e i)) * valR (A := S) y.left U (dd i U f) := fun S _ _ φ y U hU => by
    rw [SqZero.comp_lieExp]
    exact valR_prod hl hu.1 hd (fun i => φ (inr (e i)))
      (fun i j => by rw [← map_mul, TrivSqZeroExt.inr_mul_inr, map_zero]) y U hU Finset.univ
  have h1 : SqZero.tanExp u e = 1 := eq_one_of_coboundary hL hK (DualNumber.eps : DualNumber k)
    DualNumber.eps_mul_eps _ (fun j => -b j) (fun S _ _ φ y U hU => (key S φ y U hU).1) fun S _ _ φ y j j' hj hj' => by
      have hU : ⊤ ≤ y.left ⁻¹ᵁ (L.U j ⊓ L.U j') := fun p hp => ⟨hj hp, hj' hp⟩
      have hy : y.left ≫ B.hom = spMap (algebraMap A S) := Over.w y
      have hc : ∀ a, valHom (R := S) y.left _ hU (constFn B.hom _ a) = algebraMap A S a := fun a =>
        (valR_eq (R := S) _ _ hU _).symm.trans (GlobalTheory.InvFieldRing.valR_constFn _ _ _ hy _ hU a)
      have e₁ := congrArg (valHom (R := S) y.left _ hU) (hb j j')
      have r₁ : valHom (R := S) y.left _ hU (rsT (b j) _) = valHom (R := S) y.left _ hj (b j) := by
        rw [rsT, dif_pos inf_le_left, ← valR_eq, ← valR_eq]
        exact valR_res _ _ hU _
      have r₂ : valHom (R := S) y.left _ hU (rsT (b j') _) = valHom (R := S) y.left _ hj' (b j') := by
        rw [rsT, dif_pos inf_le_right, ← valR_eq, ← valR_eq]
        exact valR_res _ _ hU _
      simp only [dlg, pbT_id, map_sub, map_sum, map_mul, hc, r₁, r₂] at e₁
      have e₂ : valHom (R := S) y.left _ hU (L.g j j').val * valHom (R := S) y.left _ hU (L.g j j')⁻¹.val = 1 := by
        rw [← map_mul, Units.mul_inv, map_one]
      have e₃ : ∀ i, φ DualNumber.eps * algebraMap A S (t i) = 0 := fun i => by
        rw [← hφ, (residue_eq_zero_iff _).2 (ht i), TrivSqZeroExt.inr_zero, map_zero]
      refine ((key S φ y _ hU).2 _).trans ?_
      simp only [valR_eq (R := S) _ _ hU, valR_eq (R := S) _ _ hj, valR_eq (R := S) _ _ hj', map_neg, e, hφ]
      rw [neg_sub_neg, ← e₁, mul_sub, Finset.mul_sum, Finset.mul_sum, mul_add, _root_.mul_one]
      simp only [← _root_.mul_assoc (φ _) (algebraMap A S (t _)), e₃, zero_mul, Finset.sum_const_zero, sub_zero,
        Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      linear_combination (-(φ DualNumber.eps * algebraMap A S (c i) *
        valHom (R := S) y.left _ hU (dd i _ (L.g j j').val))) * e₂
  have h2 : SqZero.tanExp u e = SqZero.tanExp u 0 := h1.trans
    (SqZero.lieExp_eq_one hu.1 _ (fun _ => rfl) _).symm
  have h3 := (SqZero.expBij (DualNumber k) hu _ (SqZero.ker_fst_sq (R := A) (S := k) k)).1 _ _
    (fun _ => rfl) (fun _ => rfl) _ _ h2
  exact fun a => (residue_eq_zero_iff _).1 (congrArg TrivSqZeroExt.snd (congrFun h3 a))

end GlobalTheory.Heat.DlogIndep
