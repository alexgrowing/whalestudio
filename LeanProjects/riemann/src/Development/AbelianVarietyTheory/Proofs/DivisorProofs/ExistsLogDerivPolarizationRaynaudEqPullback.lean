import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasisRaynaudTangentInvariantFields
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusInvariantLiftAddInvariantCombination
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRaynaudTorusWeightFunctionInvariantField
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.BijectiveRestrictPointsOfEtaleOfHenselian
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AwayToAwayRightEqOfComp
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUnitCharts
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LeISupInfPreimage

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

namespace GlobalTheory.Heat.LiePush

open GlobalTheory.ZH.CrdCalc (valR_res valR_spMap)
open ReciprocityTheory.ChartRestriction.G.Chart (sp)
open TrivSqZeroExt (inl inr)

section Group

variable {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] {n : ℕ}
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

section Hom

variable {R : Type} [CommRing R] {G G' : Over (Sp R)} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G']

def pushL (φ : G ⟶ G') [IsMonHom φ] : TanM (𝟙 (Sp R)) G →ₗ[R] TanM (𝟙 (Sp R)) G' where
  toFun v := PullbackSections.mkT (tv v ≫ φ) (((smT_comp _ 0 (tv v) φ).trans (by rw [PullbackSections.tv_mem, MonObj.one_comp])))
  map_add' u v := PullbackSections.tanM_ext (MonObj.mul_comp (tv u) (tv v) φ)
  map_smul' a v := PullbackSections.tanM_ext (smT_comp _ a (tv v) φ).symm

theorem tv_pushL (φ : G ⟶ G') [IsMonHom φ] (v : TanM (𝟙 (Sp R)) G) : tv (pushL φ v) = tv v ≫ φ := rfl

theorem pushL_surjective [IsLocalRing R] (φ : G ⟶ G') [IsMonHom φ] [Smooth φ.left] :
    Function.Surjective (pushL φ) := by
  intro m
  let π : DualNumber R →+* R := (TrivSqZeroExt.fstHom R R R).toRingHom
  have hπ : Function.Surjective π := fun r => ⟨inl r, rfl⟩
  have hn : IsNilpotent (RingHom.ker π) := by
    refine ⟨2, ?_⟩
    rw [pow_two, Ideal.zero_eq_bot, eq_bot_iff, Ideal.mul_le]
    intro x hx y hy
    have hx : x.fst = 0 := hx
    have hy : y.fst = 0 := hy
    rw [Ideal.mem_bot]
    ext <;> simp [hx, hy]
  haveI : IsClosedImmersion (spMap π) := IsClosedImmersion.spec_of_surjective _ hπ
  have hη : (η[G] : _ ⟶ G).left ≫ φ.left = spMap π ≫ (tv m).left := by
    rw [← Over.comp_left, IsMonHom.one_hom]
    exact (RayBasis.isTangent_pt m).symm
  obtain ⟨W, hW, l, hl, hl'⟩ := exists_local_lift_of_smooth φ.left (spMap π)
    (isNilpotent_ker_specMap (CommRingCat.ofHom π) hn) (η[G] : _ ⟶ G).left (tv m).left hη
    (spMap π (closedPoint R))
  have hW' : W = ⊤ := by
    refine top_le_iff.1 (InvWt.top_le_preimage_of_fst (𝟙 _) (spMap π) W (Category.comp_id _) ?_)
    exact ((closedPoint_mem_iff (spMap π ⁻¹ᵁ W)).1 hW).ge
  subst hW'
  let l' : Sp (DualNumber R) ⟶ G.left := (Sp (DualNumber R)).topIso.inv ≫ l
  have h₁ : l' ≫ φ.left = (tv m).left := by
    simp only [l', Category.assoc, hl]
    rw [← Scheme.topIso_hom, Iso.inv_hom_id_assoc]
  have h₂ : spMap π ≫ l' = (η[G] : _ ⟶ G).left := by
    haveI : IsIso (spMap π ⁻¹ᵁ ⊤).ι := inferInstanceAs (IsIso (Sp R).topIso.hom)
    rw [← cancel_epi (spMap π ⁻¹ᵁ ⊤).ι, ← hl', ← morphismRestrict_ι_assoc]
    simp only [l']
    rw [← Scheme.topIso_hom, Iso.hom_inv_id_assoc]
  let V : overAt (𝟙 (Sp R)) (DualNumber R) ⟶ G := Over.homMk l' (by
    rw [← Over.w φ, ← Category.assoc, h₁]
    exact Over.w (tv m))
  have hV : smT (𝟙 (Sp R)) 0 V = 1 := by
    apply Over.OverMorphism.ext
    rw [smT_left, Hom.one_def, Over.comp_left, Over.toUnit_left, ← h₂]
    show spMap (epsMul 0) ≫ l' = (spMap (algebraMap R (DualNumber R)) ≫ 𝟙 _) ≫ spMap π ≫ l'
    rw [Category.comp_id, ← Category.assoc _ (spMap π), ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    refine congrArg (fun q : DualNumber R →+* DualNumber R => spMap q ≫ l') (RingHom.ext fun a => ?_)
    ext <;> simp [epsMul, π, TrivSqZeroExt.algebraMap_eq_inl]
  exact ⟨PullbackSections.mkT V hV, PullbackSections.tanM_ext (Over.OverMorphism.ext h₁)⟩

theorem comp_prod {T T' : Over (Sp R)} (k : T ⟶ T') {κ : Type} (s : Finset κ) (x : κ → (T' ⟶ G)) :
    k ≫ ∏ i ∈ s, x i = ∏ i ∈ s, k ≫ x i := by
  classical
  induction s using Finset.induction_on with
  | empty => exact MonObj.comp_one k
  | insert i s hi ih => rw [Finset.prod_insert hi, Finset.prod_insert hi, MonObj.comp_mul, ih]

theorem epsTo_inr (S : Type) [CommRing S] [Algebra R S] (c : R) :
    SqZero.epsTo R (inr (algebraMap R S c) : DualNumber S) (TrivSqZeroExt.inr_mul_inr _ _ _) =
      (SqZero.epsTo R (inr 1 : DualNumber S) (TrivSqZeroExt.inr_mul_inr _ _ _)).comp
        (TrivSqZeroExt.map (c • LinearMap.id)) := by
  refine DualNumber.algHom_ext ?_
  rw [SqZero.epsTo_eps]
  change _ = SqZero.epsTo R (inr 1 : DualNumber S) (TrivSqZeroExt.inr_mul_inr _ _ _) (TrivSqZeroExt.map _ (inr 1))
  rw [TrivSqZeroExt.map_inr]
  ext <;> simp [SqZero.epsTo, SqZero.dualTo_apply, TrivSqZeroExt.algebraMap_eq_inl']

open GlobalTheory.InvFieldRing in

theorem isInv_pbT (φ : G ⟶ G') [IsMonHom φ] {v : TanM (𝟙 (Sp R)) G} {d : Fld G.left} (hd : IsInv G v d) {g : ℕ}
    {w : Fin g → TanM (𝟙 (Sp R)) G'} {d' : Fin g → Fld G'.left} (hd' : ∀ a, IsInv G' (w a) (d' a)) (c : Fin g → R)
    (hc : pushL φ v = ∑ a, c a • w a) (U : G'.left.Opens) (s : Γ(G'.left, U)) (W : G.left.Opens)
    (hW : W ≤ φ.left ⁻¹ᵁ U) :
    d W (pbT φ.left s W) = pbT φ.left (∑ a, constFn G'.hom U (c a) * d' a U s) W := by
  rw [← sub_eq_zero]
  refine Adjust.eq_zero_of_valR_points _ _ fun S _ x hx => ?_
  obtain ⟨ψ', hψ'⟩ := Spec.map_surjective (R := CommRingCat.of R) (S := CommRingCat.of S) (x ≫ G.hom)
  letI : Algebra R S := ψ'.hom.toAlgebra
  have hψ : x ≫ G.hom = spMap (algebraMap R S) := hψ'.symm
  let z : sp (R₀ := R) S ⟶ G := Over.homMk x hψ
  let z' : sp (R₀ := R) (DualNumber S) ⟶ G := Chart.spMap (SqZero.inlS R S) ≫ z
  obtain ⟨a₁, a₂⟩ := valR_spMap (SqZero.inlS R S).toRingHom x W hx
  have hxU : ⊤ ≤ (x ≫ φ.left) ⁻¹ᵁ U := hx.trans (x.preimage_mono hW)
  obtain ⟨b₁, b₂⟩ := valR_spMap (SqZero.inlS R S).toRingHom (x ≫ φ.left) U hxU
  obtain ⟨c₁, c₂⟩ := valR_translate (u := RayBasis.pt v) rfl (RayBasis.isTangent_pt v) hd
    (inr 1 : DualNumber S) (TrivSqZeroExt.inr_mul_inr _ _ _) z' W a₁
  obtain ⟨-, d₂⟩ := valR_prod (u := fun a => RayBasis.pt (w a)) (fun _ => rfl) (fun a => RayBasis.isTangent_pt (w a)) hd'
    (fun a => (inr (algebraMap R S (c a)) : DualNumber S)) (fun _ _ => TrivSqZeroExt.inr_mul_inr _ _ _) (z' ≫ φ) U b₁
    Finset.univ
  let k : sp (R₀ := R) (DualNumber S) ⟶ overAt (𝟙 (Sp R)) (DualNumber R) :=
    Chart.spMap (SqZero.epsTo R (inr 1 : DualNumber S) (TrivSqZeroExt.inr_mul_inr _ _ _)) ≫
      Over.homMk (𝟙 _) ((Category.id_comp _).trans (Category.comp_id _))
  have hk : k.left = spMap (SqZero.epsTo R (inr 1 : DualNumber S) (TrivSqZeroExt.inr_mul_inr _ _ _)).toRingHom :=
    Category.comp_id _
  have e₁ : (Chart.spMap (SqZero.epsTo R (inr 1 : DualNumber S) (TrivSqZeroExt.inr_mul_inr _ _ _)) ≫ RayBasis.pt v :
      sp (R₀ := R) (DualNumber S) ⟶ G) = k ≫ tv v :=
    Over.OverMorphism.ext (by rw [Over.comp_left, Over.comp_left, hk]; rfl)
  have e₂ : ∀ a, (Chart.spMap (SqZero.epsTo R (inr (algebraMap R S (c a)) : DualNumber S)
      (TrivSqZeroExt.inr_mul_inr _ _ _)) ≫ RayBasis.pt (w a) : sp (R₀ := R) (DualNumber S) ⟶ G') =
        k ≫ tv (c a • w a) := fun a => Over.OverMorphism.ext (by
    rw [Over.comp_left, Over.comp_left, hk, PullbackSections.tv_smul, smT_left, ← Category.assoc, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp]
    refine congrArg (fun q : DualNumber R →+* DualNumber S => spMap q ≫ (tv (w a)).left) (RingHom.ext fun y => ?_)
    exact (AlgHom.congr_fun (epsTo_inr S (c a)) y))
  have e₃ : (k ≫ tv v * z') ≫ φ = (∏ a, k ≫ tv (c a • w a)) * (z' ≫ φ) := by
    rw [MonObj.mul_comp, Category.assoc, ← tv_pushL, hc, RayBasis.tv_sum, comp_prod]
  rw [e₁] at c₁ c₂
  simp only [e₂] at d₂
  have f₁ := c₂ (pbT φ.left s W)
  have f₂ := d₂ s
  rw [← e₃, Over.comp_left, ← valR_appLE _ _ _ _ hW c₁, ← GlobalTheory.KS.pbT_of_le, f₁, Over.comp_left _ _ _ z' φ,
    ← valR_appLE z'.left _ _ _ hW a₁, ← GlobalTheory.KS.pbT_of_le, add_right_inj] at f₂
  have a₃ : ∀ f, valR (A := DualNumber S) z'.left W f = inl (valR x W f) := a₂
  have b₃ : ∀ f, valR (A := DualNumber S) (z'.left ≫ φ.left) U f = inl (valR (x ≫ φ.left) U f) := b₂
  simp only [a₃, b₃] at f₂
  have f₃ := congrArg TrivSqZeroExt.snd f₂
  simp only [TrivSqZeroExt.snd_sum, TrivSqZeroExt.inr_mul_inl, TrivSqZeroExt.snd_inr, MulOpposite.smul_eq_mul_unop,
    MulOpposite.unop_op, _root_.one_mul] at f₃
  rw [HolHom.valR_eq _ _ hx, map_sub, ← HolHom.valR_eq _ _ hx, ← HolHom.valR_eq _ _ hx, f₃,
    GlobalTheory.KS.pbT_of_le _ hW, valR_appLE _ _ _ _ hW hx, HolHom.valR_eq _ _ hxU, map_sum, sub_eq_zero]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_mul, ← HolHom.valR_eq _ _ hxU, ← HolHom.valR_eq _ _ hxU,
    valR_constFn _ G'.hom (algebraMap R S) (by rw [Category.assoc, Over.w φ, hψ]) U hxU]

end Hom

theorem pbT_id {Z : Scheme.{0}} {U : Z.Opens} (s : Γ(Z, U)) : pbT (𝟙 Z) s U = s := by
  rw [GlobalTheory.KS.pbT_of_le (𝟙 Z) (O₀ := U) (O := U) le_rfl]
  exact (congrArg (fun φ => φ.hom s) (Scheme.Hom.appLE_eq_app (𝟙 Z) (U := U))).trans rfl

theorem exists_dlg_eq_pbT : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (Dd : DegData R (maximalIdeal R)) (O : Type) [CommRing O] [StarRing O] [Module O Dd.toPre.X] (oa : Dd.toPre.OAct O) (Y : Ray oa) (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (v a) (dd a)) → ∃ (g : ℕ) (w : Fin g → TanM (𝟙 (Sp R)) Dd.toPre.P.A) (dd' : Fin g → Fld Dd.toPre.P.A.left) (M : Fin n → Fin g → R) (N : Fin g → Fin n → R), (∀ a, IsInv Dd.toPre.P.A (w a) (dd' a)) ∧ (∀ u : TanM (𝟙 (Sp R)) Dd.toPre.P.A, ∃ cf : Fin g → R, u = ∑ a, cf a • w a) ∧ (∀ a a', ∑ b, N a b * M b a' = if a = a' then 1 else 0) ∧ ∀ (b : Fin n) (i i' : Dd.toPre.P.L.ι) (W : Y.H.left.Opens), W ≤ Y.q.left ⁻¹ᵁ (Dd.toPre.P.L.U i ⊓ Dd.toPre.P.L.U i') → dlg Y.H Y.q.left Dd.toPre.P.L (dd b) i i' W = pbT Y.q.left (∑ a, constFn Dd.toPre.P.A.hom _ (M b a) * dlg Dd.toPre.P.A (𝟙 _) Dd.toPre.P.L (dd' a) i i' (Dd.toPre.P.L.U i ⊓ Dd.toPre.P.L.U i')) W := by
  intro R _ _ _ _ _ _ Dd O _ _ _ oa Y n v dd hdd
  haveI : IsMonHom Y.q := Y.q_linear.isMonHom
  haveI : Smooth Y.q.left := Y.smooth_q
  obtain ⟨g, ⟨w⟩⟩ := RayBasis.exists_basis (G := Dd.toPre.P.A) Dd.toPre.P.isAb.smooth
  choose dd' hdd' using fun a => RayBasis.exists_isInv (w a)
  choose u hu using fun a => pushL_surjective Y.q (w a)
  refine ⟨g, w, dd', fun b a => w.repr (pushL Y.q (v b)) a, fun a b => v.repr (u a) b, hdd',
    fun m => ⟨w.repr m, (w.sum_repr m).symm⟩, fun a a' => ?_, fun b i i' W hW => ?_⟩
  · have h := congrArg (fun m => w.repr (pushL Y.q m) a') (v.sum_repr (u a))
    simp only [map_sum, map_smul, hu, Finsupp.finset_sum_apply, Finsupp.smul_apply, smul_eq_mul,
      Module.Basis.repr_self, Finsupp.single_apply] at h
    exact h
  · simp only [dlg, pbT_id]
    rw [isInv_pbT Y.q (hdd b) hdd' _ (w.sum_repr _).symm _ _ W hW, ← GlobalTheory.KS.pbT_mul, Finset.sum_mul]
    simp only [_root_.mul_assoc]

end GlobalTheory.Heat.LiePush
