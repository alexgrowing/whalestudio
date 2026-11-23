import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.BijectiveSmulChartSec
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LeISupInfPreimage
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTorFieldZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusInvariantLiftAddInvariantCombination
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AwayToAwayRightEqOfComp
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUnitCharts
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

namespace GlobalTheory.HeatMod.TorField

open GlobalTheory.ZH.CrdCalc (valR_res valR_spMap)
open ReciprocityTheory.ChartRestriction.G.Chart (sp)
open TrivSqZeroExt (inl inr)
open ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht (coord coord_comp)

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
  have hwO : ⊤ ≤ w.left ⁻¹ᵁ O := InvWt.top_le_preimage_of_fst (S := B) w.left z.left O h0' h
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

section Raynaud

variable {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O Q.X]
  {oa : Q.OAct O} (Y : Ray oa)

theorem valR_torus_mul {S : Type} [CommRing S] {φ : R →+* S} (t : Over.mk (spMap φ) ⟶ splitTorus (Sp R) (RayEv.Chr Q))
    (c : Q.X → Sˣ) (hc : ∀ χ : Q.X, (coord t).hom (AddMonoidAlgebra.single χ 1) = (unitOn (c χ)).val)
    (x : Over.mk (spMap φ) ⟶ Y.H) {α : Q.X} {W : Y.H.left.Opens} {f : Γ(Y.H.left, W)} (hf : IsWt Y α W f)
    (h : ⊤ ≤ x.left ⁻¹ᵁ W) (h' : ⊤ ≤ ((t ≫ Y.i) * x).left ⁻¹ᵁ W) :
    valR (A := S) ((t ≫ Y.i) * x).left W f = c α * valR (A := S) x.left W f := by
  have hqm : IsMonHom Y.q := Y.q_linear.isMonHom
  refine hf S φ x ((t ≫ Y.i) * x) c _ _ rfl rfl h h' ?_ fun χ y J hJ => ?_
  · rw [MonObj.mul_comp, Category.assoc, Y.i_q, MonObj.comp_one, _root_.one_mul]
  · have h1 := ((GlobalTheory.TorusModel.isAdd_iff _ _ _).1 (Y.rep.2 _ x (t ≫ Y.i))).2 χ y J hJ
    have C : IsCub (DVR.th Q (T := Over.mk (spMap φ)) y J) := isCub_cubV Q.cub hJ
    rw [(Y.Φ_i t).1, C.face₃, _root_.mul_one, _root_.mul_comm x] at h1
    refine h1.trans ((_root_.mul_comm _ _).trans (congrArg (· * _) (Units.ext ?_)))
    exact ((Y.Φ_i t).2 χ y J hJ).trans ((congrArg (gs _ y ⊤) (hc χ)).trans (gs_unit _ y ⊤ trivial _))

def epsUnit {S : Type} [CommRing S] (a : S) : (DualNumber S)ˣ :=
  ⟨1 + inr a, 1 + inr (-a), by ext <;> simp, by ext <;> simp⟩

def torTan (ℓ : Q.X →+ R) : sp (R₀ := R) (DualNumber R) ⟶ splitTorus (Sp R) (RayEv.Chr Q) :=
  Diag.ofChar _
    { toFun := fun χ => (unitOn (epsUnit (ℓ χ.toAdd))).val
      map_one' := by
        have : epsUnit (ℓ 0) = 1 := Units.ext (by ext <;> simp [epsUnit])
        exact (congrArg (fun u => (unitOn u).val) this).trans (map_one (Scheme.ΓSpecIso (CommRingCat.of (DualNumber R))).inv.hom)
      map_mul' := fun a b => by
        have : ∀ a b : Q.X, epsUnit (ℓ (a + b)) = epsUnit (ℓ a) * epsUnit (ℓ b) := fun a b =>
          Units.ext (by ext <;> simp [epsUnit, _root_.add_comm])
        exact (congrArg (fun u => (unitOn u).val) (this a.toAdd b.toAdd)).trans
          (map_mul (Scheme.ΓSpecIso (CommRingCat.of (DualNumber R))).inv.hom _ _) }

theorem coord_torTan (ℓ : Q.X →+ R) {B : Type} [CommRing B] [Algebra R B] (ψ : DualNumber R →ₐ[R] B) (χ : Q.X) :
    (coord (Chart.spMap ψ ≫ torTan ℓ)).hom (AddMonoidAlgebra.single χ 1) =
      (unitOn (Units.map ψ.toRingHom.toMonoidHom (epsUnit (ℓ χ)))).val := by
  rw [coord_comp, ← InvWt.map_unitOn]
  exact congrArg (spMap ψ.toRingHom).appTop.hom (Diag.coord_ofChar _ _ χ)

theorem isTangent_torTan (ℓ : Q.X →+ R) : IsTangent (torTan ℓ ≫ Y.i) := by
  have := Y.i_linear.isMonHom
  refine (Chart.isTan_iff _).1 ?_
  have e : Chart.spMap (Chart.fstD R) ≫ torTan ℓ = 1 := Diag.hom_ext fun χ => by
    refine (coord_torTan ℓ _ χ).trans (Eq.trans ?_ (Diag.coord_one _ χ).symm)
    have : Units.map (Chart.fstD R).toRingHom.toMonoidHom (epsUnit (ℓ χ)) = 1 := Units.ext (by
      show (1 + inr (ℓ χ) : DualNumber R).fst = 1
      simp)
    exact (congrArg (fun u => (unitOn u).val) this).trans (map_one (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)
  rw [Chart.IsTan, ← Category.assoc, e, MonObj.one_comp]

theorem exists_comb {n : ℕ} (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) {dd : Fin n → Fld Y.H.left}
    (hd : ∀ a, IsInv Y.H (v a) (dd a)) (ℓ : Q.X →+ R) : ∃ c : Fin n → R, ∀ (α : Q.X) (W : Y.H.left.Opens) f,
      IsWt Y α W f → combF Y.H.hom dd c W f = constFn Y.H.hom W (ℓ α) * f := by
  obtain ⟨u, hb, hu⟩ := exists_isLieBasis v
  obtain ⟨c, hc, -⟩ := hb.2 _ (isTangent_torTan Y ℓ)
  rw [SqZero.isLieComb_iff_lieExp] at hc
  refine ⟨c, fun α W f hf => sub_eq_zero.1 (Adjust.eq_zero_of_valR_points _ _ fun S _ g hg => ?_)⟩
  obtain ⟨φ', hφ'⟩ := Spec.map_surjective (R := CommRingCat.of R) (S := CommRingCat.of S) (g ≫ Y.H.hom)
  let φ : R →+* S := φ'.hom
  have hφ : g ≫ Y.H.hom = spMap φ := hφ'.symm
  letI : Algebra R S := φ.toAlgebra
  let z : sp (R₀ := R) S ⟶ Y.H := Over.homMk g hφ
  let ψ : DualNumber R →ₐ[R] DualNumber S := SqZero.dualMap (Algebra.ofId R S)
  have hψ : ∀ a : R, ψ (inr a) = inr (φ a) := fun a => SqZero.dualMap_inr _ _
  obtain ⟨a₁, a₂⟩ := valR_spMap (SqZero.inlS R S).toRingHom g W hg
  obtain ⟨b₁, b₂⟩ := valR_prod hu hb.1 hd (fun i => ψ (inr (c i)))
    (fun _ _ => by rw [← map_mul, TrivSqZeroExt.inr_mul_inr, map_zero]) (Chart.spMap (SqZero.inlS R S) ≫ z) W a₁ Finset.univ
  have e := congrArg (Chart.spMap ψ ≫ ·) hc
  simp only [SqZero.comp_lieExp, ← Category.assoc] at e
  rw [SqZero.lieExp] at e
  rw [← e] at b₁ b₂
  have k := valR_torus_mul Y (S := DualNumber S) (φ := algebraMap R (DualNumber S)) (Chart.spMap ψ ≫ torTan ℓ) _
    (coord_torTan ℓ ψ) (Chart.spMap (SqZero.inlS R S) ≫ z) hf a₁ b₁
  have a₃ : ∀ s, valR (A := DualNumber S) (Chart.spMap (SqZero.inlS R S) ≫ z).left W s = inl (valR g W s) := a₂
  have k' := congrArg TrivSqZeroExt.snd ((b₂ f).symm.trans k)
  have hu' : ((Units.map ψ.toRingHom.toMonoidHom (epsUnit (ℓ α)) : (DualNumber S)ˣ) : DualNumber S) = 1 + inr (φ (ℓ α)) := by
    rw [← hψ, ← map_one ψ, ← map_add]; rfl
  simp only [a₃, hψ, hu'] at k'
  rw [WtAlg.valR_sub' _ _ hg, WtAlg.valR_mul'' _ _ hg, Adjust.valR_const _ φ g hφ W hg, combF,
    GlobalTheory.ZH.CrdCalc.valR_eq _ _ hg, map_sum, sub_eq_zero]
  simp only [← GlobalTheory.ZH.CrdCalc.valR_eq _ _ hg, WtAlg.valR_mul'' _ _ hg, Adjust.valR_const _ φ g hφ W hg]
  simpa [TrivSqZeroExt.snd_sum, _root_.mul_comm] using k'

theorem isWt_pbT (U : Q.P.A.left.Opens) (g : Γ(Q.P.A.left, U)) (W : Y.H.left.Opens) (hW : W ≤ Y.q.left ⁻¹ᵁ U) :
    IsWt Y 0 W (pbT Y.q.left g W) := by
  intro S _ φ x x' c a a' ha ha' hV hV' hq hc
  have e : a' ≫ Y.q.left = a ≫ Y.q.left := by
    subst ha ha'
    exact congrArg (fun q => q.left) hq
  rw [GlobalTheory.KS.pbT_of_le _ hW, HolHom.valR_appLE _ _ _ _ _ _ hV', HolHom.valR_appLE _ _ _ _ _ _ hV, e,
    WtAlg.c_zero x x' c hc, Units.val_one, _root_.one_mul]

end Raynaud

theorem isField_combF {R : Type} [CommRing R] {Z : Scheme.{0}} (s : Z ⟶ Sp R) {n : ℕ} (dd : Fin n → Fld Z) (c : Fin n → R)
    (h : ∀ a, IsField ⊤ (dd a)) : IsField ⊤ (combF s dd c) := by
  have := Adjust.isField_add_comb (fun _ _ => 0) dd (fun a => constFn s ⊤ (c a)) (isField_zero ⊤) h
  simp only [zero_add, GlobalTheory.KS.rsT_constFn s le_top] at this
  exact this

theorem field_pow_mul {Z : Scheme.{0}} {F : Fld Z} (hF : IsField ⊤ F) (W : Z.Opens) (g : Γ(Z, W)) (hg : F W g = 0)
    (k : ℕ) (f : Γ(Z, W)) : F W (g ^ k * f) = g ^ k * F W f := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ', _root_.mul_assoc, hF.2.1 W le_top, hg, mul_zero, add_zero, ih, _root_.mul_assoc]

theorem exists_isTorField : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (Dd : DegData R (maximalIdeal R)) (O : Type) [CommRing O] [StarRing O] [Module O Dd.toPre.X] (oa : Dd.toPre.OAct O) (Y : Ray oa) (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (v a) (dd a)) → ∀ ℓ : Dd.toPre.X →+ R, ∃ c : Fin n → R, GlobalTheory.HeatMod.IsTorField Y (GlobalTheory.HeatMod.combF Y.H.hom dd c) ℓ := by
  intro R _ _ _ _ _ _ Dd O _ _ _ oa Y n v dd hd ℓ
  obtain ⟨c, hc⟩ := exists_comb Y v hd ℓ
  have hF := isField_combF Y.H.hom dd c fun a => (hd a).1
  refine ⟨c, hF, fun W r => ?_, fun α W _ f hf => hc α W f hf, fun U g W k f hW => field_pow_mul hF W _ ?_ k f⟩
  · simp only [combF, fun a => Adjust.inv_constFn Y.H (v a) (dd a) (hd a) W r, mul_zero, Finset.sum_const_zero]
  · rw [hc 0 W _ (isWt_pbT Y U g W hW), map_zero]
    simp [constFn]

end GlobalTheory.HeatMod.TorField
