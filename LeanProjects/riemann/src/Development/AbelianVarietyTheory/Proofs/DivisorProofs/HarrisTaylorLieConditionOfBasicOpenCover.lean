import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieRankAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LieBridgeA
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualNumberMorphismEqOfLocal

noncomputable section

namespace GlobalTheory.UPel.HT.LieLoc

open scoped TensorProduct

section Alg

variable {R' O M : Type} [CommRing R'] [CommRing O] [AddCommGroup M] [Module R' M]
  (μ : O →+* Module.End R' M)

def lam : R' ⊗[ℤ] O →ₐ[R'] Module.End R' M :=
  Algebra.TensorProduct.lift (Algebra.ofId R' (Module.End R' M)) μ.toIntAlgHom
    (fun r c => (Algebra.commute_algebraMap_left r (μ c) :
      Commute (Algebra.ofId R' (Module.End R' M) r) (μ.toIntAlgHom c)))

theorem lam_tmul (r : R') (c : O) : lam μ (r ⊗ₜ c) = algebraMap R' _ r * μ c := by
  exact Algebra.TensorProduct.lift_tmul _ _ _ _ _

def gen (τ : O →+* R') (c : O) : R' ⊗[ℤ] O := (1 : R') ⊗ₜ c - algebraMap R' (R' ⊗[ℤ] O) (τ c)

theorem lam_gen (τ : O →+* R') (c : O) : lam μ (gen τ c) = μ c - algebraMap R' _ (τ c) := by
  rw [gen, map_sub, lam_tmul, AlgHom.commutes, map_one, one_mul]

theorem lam_gen_apply (τ : O →+* R') (c : O) (m : M) : lam μ (gen τ c) m = μ c m - τ c • m := by
  rw [lam_gen, LinearMap.sub_apply, Module.algebraMap_end_apply]

theorem lam_prod_gen {a : ℕ} (τ : Fin a → O →+* R') (c : Fin a → O) :
    lam μ (∏ i, gen (τ i) (c i)) = (List.ofFn fun i => μ (c i) - algebraMap R' _ (τ i (c i))).prod := by
  rw [← List.prod_ofFn, map_list_prod, List.map_ofFn]
  congr 1
  exact List.ofFn_inj.2 (funext fun i => lam_gen μ (τ i) (c i))

theorem kill_of_decomp {a : ℕ} (τ : Fin a → O →+* R') (v : M) (w : Fin a → M)
    (hw : ∀ i c, μ c (w i) = τ i c • w i) (hv : v = ∑ i, w i) (c : Fin a → O) :
    (List.ofFn fun i => μ (c i) - algebraMap R' _ (τ i (c i))).prod v = 0 := by
  classical
  rw [← lam_prod_gen, hv, map_sum]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ j), map_mul, Module.End.mul_apply, lam_gen_apply, hw,
    sub_self, map_zero]

theorem sup_gen_eq_top (τ₁ τ₂ : O →+* R') (h : Ideal.span (Set.range fun x => τ₁ x - τ₂ x) = ⊤) :
    Ideal.span (Set.range (gen τ₁)) ⊔ Ideal.span (Set.range (gen τ₂)) = ⊤ := by
  have h' := congrArg (Ideal.map (algebraMap R' (R' ⊗[ℤ] O))) h
  rw [Ideal.map_span, Ideal.map_top] at h'
  rw [eq_top_iff, ← h', Ideal.span_le]
  rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
  have e : algebraMap R' (R' ⊗[ℤ] O) (τ₁ x - τ₂ x) = gen τ₂ x - gen τ₁ x := by
    simp only [gen, map_sub]; abel
  rw [SetLike.mem_coe, e]
  exact sub_mem (Ideal.mem_sup_right (Ideal.subset_span ⟨x, rfl⟩))
    (Ideal.mem_sup_left (Ideal.subset_span ⟨x, rfl⟩))

theorem decomp_of_kill {a : ℕ} (τ : Fin a → O →+* R')
    (hτ : ∀ i j, i ≠ j → Ideal.span (Set.range fun x => τ i x - τ j x) = ⊤) (v : M)
    (hv : ∀ c : Fin a → O, (List.ofFn fun i => μ (c i) - algebraMap R' _ (τ i (c i))).prod v = 0) :
    ∃ w : Fin a → M, (∀ i c, μ c (w i) = τ i c • w i) ∧ v = ∑ i, w i := by
  classical
  letI : Module (R' ⊗[ℤ] O) M := Module.compHom M (lam μ).toRingHom
  have hsm : ∀ (b : R' ⊗[ℤ] O) (m : M), b • m = lam μ b m := fun _ _ => rfl
  let I : Fin a → Ideal (R' ⊗[ℤ] O) := fun i => Ideal.span (Set.range (gen (τ i)))
  have hp : ((Finset.univ : Finset (Fin a)) : Set (Fin a)).Pairwise fun i j => I i ⊔ I j = ⊤ :=
    fun i _ j _ hij => sup_gen_eq_top (τ i) (τ j) (hτ i j hij)
  have hmem : v ∈ Submodule.torsionBySet (R' ⊗[ℤ] O) M ↑(⨅ i ∈ (Finset.univ : Finset (Fin a)), I i) := by
    rw [← Ideal.prod_eq_iInf_of_pairwise_isCoprime (fun i hi j hj hij =>
      (Ideal.isCoprime_iff_sup_eq).2 (hp hi hj hij))]
    simp only [I]
    rw [Ideal.prod_span, ← Submodule.torsionBySet_eq_torsionBySet_span, Submodule.mem_torsionBySet_iff]
    rintro ⟨b, hb⟩
    obtain ⟨g, hg, rfl⟩ := (Set.mem_finset_prod _ _ _).1 hb
    have hc : ∀ i, ∃ c, gen (τ i) c = g i := fun i => hg (Finset.mem_univ i)
    choose c hc using hc
    show lam μ (∏ i, g i) v = 0
    rw [show (∏ i, g i) = ∏ i, gen (τ i) (c i) from Finset.prod_congr rfl fun i _ => (hc i).symm, lam_prod_gen]
    exact hv c
  rw [← Submodule.iSup_torsionBySet_ideal_eq_torsionBySet_iInf hp, Submodule.mem_iSup_finset_iff_exists_sum] at hmem
  obtain ⟨w, hw⟩ := hmem
  refine ⟨fun i => w i, fun i c => ?_, hw.symm⟩
  have h0 := (Submodule.mem_torsionBySet_iff _ _).1 (w i).2 ⟨gen (τ i) c, Ideal.subset_span ⟨c, rfl⟩⟩
  rw [hsm, lam_gen_apply, sub_eq_zero] at h0
  exact h0

end Alg

section Geo

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections GlobalTheory.UPel.HT

theorem spMap_comp_loc {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {R' : Type} [CommRing R']

theorem tan_iff (x : Sp R' ⟶ S) (v : epsPtR x ⟶ A) :
    spMap (TrivSqZeroExt.fstHom R' R' R').toRingHom ≫ v.left = (1 : Over.mk x ⟶ A).left ↔
      Formalism.L2.Pj.smT x 0 v = 1 := by
  have e1 : spMap (TrivSqZeroExt.fstHom R' R' R').toRingHom ≫ spMap (algebraMap R' (DualNumber R')) = 𝟙 _ := by
    rw [spMap_comp_loc]
    have : (TrivSqZeroExt.fstHom R' R' R').toRingHom.comp (algebraMap R' (DualNumber R')) = RingHom.id R' := by
      ext r; simp [TrivSqZeroExt.algebraMap_eq_inl]
    rw [this]
    exact Spec.map_id _
  let j : Over.mk x ⟶ epsPtR x := Over.homMk (spMap (TrivSqZeroExt.fstHom R' R' R').toRingHom) (by
    show spMap _ ≫ spMap (algebraMap R' (DualNumber R')) ≫ x = x
    rw [← Category.assoc, e1, Category.id_comp])
  let h : epsPtR x ⟶ Over.mk x := Over.homMk (spMap (algebraMap R' (DualNumber R'))) rfl
  have ejh : j ≫ h = 𝟙 _ := Over.OverMorphism.ext (by simp only [Over.comp_left, Over.homMk_left, j, h, e1]; rfl)
  have e0 : Formalism.L2.Pj.homAt x (Formalism.L2.Pj.tm ((0 : R') • (LinearMap.id : R' →ₗ[R'] R'))) = h ≫ j := by
    apply Over.OverMorphism.ext
    simp only [Formalism.L2.Pj.homAt, Over.comp_left, Over.homMk_left, j, h, spMap_comp_loc]
    congr 2
    ext r <;> simp [TrivSqZeroExt.algebraMap_eq_inl]
  have es : Formalism.L2.Pj.smT x 0 v = h ≫ (j ≫ v) := by
    rw [Formalism.L2.Pj.smT, e0, Category.assoc]
  constructor
  · intro hv
    have hj : j ≫ v = 1 := Over.OverMorphism.ext (by simpa [j] using hv)
    rw [es, hj, MonObj.comp_one]
  · intro hv
    have hj : j ≫ v = 1 := by
      calc j ≫ v = (j ≫ h) ≫ (j ≫ v) := by rw [ejh, Category.id_comp]
        _ = j ≫ Formalism.L2.Pj.smT x 0 v := by rw [es, Category.assoc]
        _ = 1 := by rw [hv, MonObj.comp_one]
    have := congrArg (fun φ => φ.left) hj
    simpa [j] using this

theorem scal_iff {p : ℕ} [Fact p.Prime] {D : Datum p} (act : OActN D.O A) (x : Sp R' ⟶ S) (c' : 𝓞 D.F) (c : R')
    (V : TanM x A) :
    (tv V ≫ act.act (algebraMap (𝓞 D.F) D.O c')).left = spMap (epsScaleR c) ≫ (tv V).left ↔
      actR (x0 := x) (act.toF D) c' V = c • V := by
  constructor
  · intro h
    exact tanM_ext (Over.OverMorphism.ext h)
  · intro h
    exact congrArg (fun W => (tv W).left) h

theorem tv_sum (x : Sp R' ⟶ S) {n : ℕ} (W : Fin n → TanM x A) :
    tv (∑ i, W i) = (List.ofFn fun i => tv (W i)).prod := by
  classical
  rw [List.prod_ofFn]
  have key : ∀ s : Finset (Fin n), tv (∑ i ∈ s, W i) = ∏ i ∈ s, tv (W i) := by
    intro s
    induction s using Finset.induction_on with
    | empty => rw [Finset.sum_empty, Finset.prod_empty]; rfl
    | insert i s hi ih => rw [Finset.sum_insert hi, Finset.prod_insert hi, tv_add, ih]
  exact key _

variable {R'' : Type} [CommRing R'']

def rho (x : Sp R' ⟶ S) (g : R' →+* R'') : epsPtR (spMap g ≫ x) ⟶ epsPtR x :=
  Over.homMk (spMap (Formalism.L2.Pj.dualMap g)) (by
    show spMap _ ≫ spMap (algebraMap R' (DualNumber R')) ≫ x = spMap (algebraMap R'' (DualNumber R'')) ≫ spMap g ≫ x
    rw [← Category.assoc, ← Category.assoc, spMap_comp_loc, spMap_comp_loc]
    have e : (Formalism.L2.Pj.dualMap g).comp (algebraMap R' (DualNumber R')) =
        (algebraMap R'' (DualNumber R'')).comp g := by
      refine RingHom.ext fun z => TrivSqZeroExt.ext ?_ ?_ <;>
        simp [Formalism.L2.Pj.dualMap, TrivSqZeroExt.algebraMap_eq_inl]
    rw [e])

theorem smT_rho (x : Sp R' ⟶ S) (g : R' →+* R'') (c : R') (w : epsPtR x ⟶ A) :
    Formalism.L2.Pj.smT (spMap g ≫ x) (g c) (rho x g ≫ w) = rho x g ≫ Formalism.L2.Pj.smT x c w := by
  apply Over.OverMorphism.ext
  simp only [Over.comp_left, Formalism.L2.Pj.smT_left, rho, Over.homMk_left, ← Category.assoc, spMap_comp_loc]
  have e : (epsMul (g c)).comp (Formalism.L2.Pj.dualMap g) = (Formalism.L2.Pj.dualMap g).comp (epsMul c) := by
    refine RingHom.ext fun z => TrivSqZeroExt.ext ?_ ?_ <;>
      simp [Formalism.L2.Pj.dualMap, epsMul, mul_comm]
  rw [e]

theorem rho_tan (x : Sp R' ⟶ S) (g : R' →+* R'') (V : TanM x A) :
    Formalism.L2.Pj.smT (spMap g ≫ x) 0 (rho x g ≫ tv V) = 1 := by
  rw [← map_zero g, smT_rho, tv_mem, MonObj.comp_one]

def res (x : Sp R' ⟶ S) (g : R' →+* R'') (V : TanM x A) : TanM (spMap g ≫ x) A :=
  mkT (rho x g ≫ tv V) (rho_tan x g V)

theorem tv_res (x : Sp R' ⟶ S) (g : R' →+* R'') (V : TanM x A) : tv (res x g V) = rho x g ≫ tv V := rfl

def resHom (x : Sp R' ⟶ S) (g : R' →+* R'') : TanM x A →+ TanM (spMap g ≫ x) A :=
  AddMonoidHom.mk' (res x g) fun V W => tanM_ext (by
    rw [tv_res, tv_add, tv_add, tv_res, tv_res, MonObj.comp_mul])

theorem res_smul (x : Sp R' ⟶ S) (g : R' →+* R'') (c : R') (V : TanM x A) :
    res x g (c • V) = g c • res x g V :=
  tanM_ext (by rw [tv_res, tv_smul, tv_smul, tv_res, smT_rho])

theorem res_actR {O : Type} [CommRing O] (Oa : OAct O A) (x : Sp R' ⟶ S) (g : R' →+* R'') (c : O) (V : TanM x A) :
    res x g (actR (x0 := x) Oa c V) = actR (x0 := spMap g ≫ x) Oa c (res x g V) :=
  tanM_ext (by simp only [tv_res, tv_actR, Category.assoc])

theorem res_prod {O : Type} [CommRing O] (Oa : OAct O A) (x : Sp R' ⟶ S) (g : R' →+* R'') :
    ∀ {a : ℕ} (τ : Fin a → O →+* R') (c : Fin a → O) (V : TanM x A),
    res x g ((List.ofFn fun i => actR (x0 := x) Oa (c i) - algebraMap R' _ (τ i (c i))).prod V) =
      (List.ofFn fun i => actR (x0 := spMap g ≫ x) Oa (c i) - algebraMap R'' _ (g (τ i (c i)))).prod
        (res x g V) := by
  intro a
  induction a with
  | zero => intro τ c V; simp
  | succ n ih =>
    intro τ c V
    rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons, Module.End.mul_apply,
      Module.End.mul_apply, ← ih (fun i => τ i.succ) (fun i => c i.succ), LinearMap.sub_apply, LinearMap.sub_apply,
      Module.algebraMap_end_apply, Module.algebraMap_end_apply]
    change resHom x g _ = _
    rw [map_sub]
    change res x g _ - res x g _ = _
    rw [res_actR, res_smul]

theorem eq_zero_of_res (x : Sp R' ⟶ S) (t : Finset R') (ht : Ideal.span (t : Set R') = ⊤) (U : TanM x A)
    (h : ∀ r ∈ t, res x (algebraMap R' (Localization.Away r)) U = 0) : U = 0 := by
  apply tanM_ext
  rw [tv_zero]
  apply Over.OverMorphism.ext
  refine GlobalTheory.ArLieBase.hom_ext_dualNumber_away ht fun a => ?_
  have h1 : rho x (algebraMap R' (Localization.Away (a : R'))) ≫ tv U =
      rho x (algebraMap R' (Localization.Away (a : R'))) ≫ (1 : epsPtR x ⟶ A) := by
    rw [MonObj.comp_one]
    exact congrArg tv (h a.1 a.2)
  exact congrArg (fun φ => φ.left) h1

theorem lieAt_of_cover : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (S : Scheme.{0})
    (A : Over S) [GrpObj A] [IsCommMonObj A] (act : OActN D.O A) (R' : Type) [CommRing R'] (β : R →+* R')
    (x : Sp R' ⟶ S) (t : Finset R'), Ideal.span (t : Set R') = ⊤ →
    (∀ r ∈ t, LieAt b act ((algebraMap R' (Localization.Away r)).comp β)
      (spMap (algebraMap R' (Localization.Away r)) ≫ x)) →
    LieAt b act β x := by
  intro p _ D R _ b S A _ _ act R' _ β x t ht hloc v hv
  obtain ⟨hv1, hv2⟩ := hv
  let τ : Fin D.a → 𝓞 D.F →+* R' := fun i => β.comp (b.t i)
  have hτ : ∀ i j, i ≠ j → Ideal.span (Set.range fun y => τ i y - τ j y) = ⊤ := by
    intro i j hij
    have h := congrArg (Ideal.map β) (b.comax i j hij)
    rw [Ideal.map_span, Ideal.map_top, ← Set.range_comp] at h
    simpa [τ, Function.comp_def, map_sub] using h
  let V : TanM x A := mkT v ((tan_iff x v).1 hv1)
  have hVω : actR (x0 := x) (act.toF D) D.ω V = β b.ρ • V := (scal_iff act x D.ω (β b.ρ) V).1 hv2
  have hkill : ∀ c : Fin D.a → 𝓞 D.F,
      (List.ofFn fun i => actR (x0 := x) (act.toF D) (c i) - algebraMap R' _ (τ i (c i))).prod V = 0 := by
    intro c
    apply eq_zero_of_res x t ht
    intro r hr
    rw [res_prod]
    have hω : actR (x0 := spMap (algebraMap R' (Localization.Away r)) ≫ x) (act.toF D) D.ω
        (res x (algebraMap R' (Localization.Away r)) V) =
        ((algebraMap R' (Localization.Away r)).comp β) b.ρ • res x (algebraMap R' (Localization.Away r)) V := by
      rw [← res_actR, hVω, res_smul]
      rfl
    obtain ⟨w, hw, hvw⟩ := hloc r hr (tv (res x (algebraMap R' (Localization.Away r)) V))
      ⟨(tan_iff _ _).2 (tv_mem _), (scal_iff act _ D.ω _ _).2 hω⟩
    let W : Fin D.a → TanM (spMap (algebraMap R' (Localization.Away r)) ≫ x) A :=
      fun i => mkT (w i) ((tan_iff _ _).1 (hw i 0).1)
    refine kill_of_decomp (actR (x0 := spMap (algebraMap R' (Localization.Away r)) ≫ x) (act.toF D))
      (fun i => (algebraMap R' (Localization.Away r)).comp (τ i)) _ W (fun i c' => ?_) ?_ c
    · exact (scal_iff act _ c' _ (W i)).1 (hw i c').2
    · apply tanM_ext
      rw [tv_sum]
      exact hvw
  obtain ⟨W, hW, hVW⟩ := decomp_of_kill (actR (x0 := x) (act.toF D)) τ hτ V hkill
  refine ⟨fun i => tv (W i), fun i c => ⟨(tan_iff _ _).2 (tv_mem _), (scal_iff act x c _ (W i)).2 (hW i c)⟩, ?_⟩
  show tv V = _
  rw [hVW, tv_sum]

end Geo

end GlobalTheory.UPel.HT.LieLoc
