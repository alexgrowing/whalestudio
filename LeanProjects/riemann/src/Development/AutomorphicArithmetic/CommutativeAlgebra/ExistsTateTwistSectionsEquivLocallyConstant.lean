import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.LocallyExactCech
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.EtaleProperBaseChange
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.A6supp
import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.TateTwistSectionsLocallyGenerated
import Development.AutomorphicArithmetic.CommutativeAlgebra.LocallyHoldsOfForallAndMonoAndInterAndPullback
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleLocallyHoldsOfPointwiseCoverOrAffineLocal
import Development.AutomorphicArithmetic.CommutativeAlgebra.TateTwistGeneratorOfPrimitiveRootAndRootsEtaleLo
import Development.AutomorphicArithmetic.CommutativeAlgebra.ContinuousSectionsBijectiveAdditiveNatural
import Development.AutomorphicArithmetic.CommutativeAlgebra.ConstantSheafCyclicGeneratorOfOrder

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace UpperTheory.Cb.SecLc
open UpperTheory.Et

variable {R : Type} [CommRing R]

private theorem rs_comp (M : PMod R) {W V U : Scheme.{0}} (f : W ⟶ V) (g : V ⟶ U) (z : sec M U) :
    rs M (f ≫ g) z = rs M f (rs M g z) := by
  simp [rs]

private theorem rs_nsmul (M : PMod R) {V U : Scheme.{0}} (g : V ⟶ U) (c : ℕ) (z : sec M U) :
    rs M g (c • z) = c • rs M g z :=
  map_nsmul _ _ _

private abbrev Rel (M N : PMod R) {U : Scheme.{0}} (g : sec M U) (h : sec N U) (y : sec M U)
    (z : sec N U) : Prop :=
  LocT Scheme.etaleTopology U fun _ k => ∃ c : ℕ, rs M k y = c • rs M k g ∧ rs N k z = c • rs N k h

end UpperTheory.Cb.SecLc

private theorem exists_sec_locT_rs_eq_of_compatible {R : Type} [CommRing R] (N : UpperTheory.Et.PMod R)
    (hN : Presheaf.IsSheaf Scheme.etaleTopology N) {U : Scheme}
    (P : (V : Scheme) → (V ⟶ U) → Prop) (hP : UpperTheory.Et.LocT Scheme.etaleTopology U P)
    (s : ∀ (V : Scheme) (k : V ⟶ U), P V k → UpperTheory.Et.sec N V)
    (hc : ∀ (V1 V2 W : Scheme) (k1 : V1 ⟶ U) (k2 : V2 ⟶ U) (f1 : W ⟶ V1) (f2 : W ⟶ V2)
      (h1 : P V1 k1) (h2 : P V2 k2),
      f1 ≫ k1 = f2 ≫ k2 → UpperTheory.Et.rs N f1 (s V1 k1 h1) = UpperTheory.Et.rs N f2 (s V2 k2 h2)) :
    ∃ z : UpperTheory.Et.sec N U, UpperTheory.Et.LocT Scheme.etaleTopology U
      fun V k => ∃ hk : P V k, UpperTheory.Et.rs N k z = s V k hk := by
  obtain ⟨S, hS, hSP⟩ := hP
  have hsh := (isSheaf_iff_isSheaf_of_type _ _).mp
    ((Presheaf.isSheaf_iff_isSheaf_forget Scheme.etaleTopology N (forget _)).mp hN) S hS
  let x : Presieve.FamilyOfElements (N ⋙ forget _) S.arrows := fun V k hk => s V k (hSP V k hk)
  have hx : x.Compatible := by
    intro Y1 Y2 Z g1 g2 f1 f2 h1 h2 hcomm
    exact hc Y1 Y2 Z f1 f2 g1 g2 _ _ hcomm
  obtain ⟨z, hz, -⟩ := hsh x hx
  exact ⟨z, S, hS, fun V k hk => ⟨hSP V k hk, hz k hk⟩⟩

private theorem pmod_rs_zero {R : Type} [CommRing R] (M : UpperTheory.Et.PMod R) {V U : Scheme}
    (k : V ⟶ U) : UpperTheory.Et.rs M k 0 = 0 := by
  simpa using UpperTheory.Cb.SecLc.rs_nsmul M k 0 0

private theorem nsmul_eq_nsmul_of_nsmul_eq_nsmul_of_exact_order {A B : Type*} [AddCommGroup A] [AddCommGroup B] (q : ℕ) (hq : 0 < q)
    (x : A) (hx : q • x = 0) (hdiv : ∀ c : ℕ, c • x = 0 → q ∣ c) (y : B) (hy : q • y = 0)
    (c c' : ℕ) (h : c • x = c' • x) : c • y = c' • y := by
  have hm : ∀ z : A, q • z = 0 → ∀ n : ℕ, n • z = (n % q) • z := by
    intro z hz n
    conv_lhs => rw [← Nat.mod_add_div n q]
    rw [add_nsmul, mul_comm q, mul_nsmul', hz, nsmul_zero, add_zero]
  have hm' : ∀ z : B, q • z = 0 → ∀ n : ℕ, n • z = (n % q) • z := by
    intro z hz n
    conv_lhs => rw [← Nat.mod_add_div n q]
    rw [add_nsmul, mul_comm q, mul_nsmul', hz, nsmul_zero, add_zero]
  have e : (c % q) • x = (c' % q) • x := by rw [← hm x hx, ← hm x hx, h]
  have key : c % q = c' % q := by
    rcases le_total (c' % q) (c % q) with hle | hle
    · have h0 : (c % q - c' % q) • x = 0 := by
        rw [← Nat.sub_add_cancel hle, add_nsmul] at e
        simpa using e
      have := Nat.eq_zero_of_dvd_of_lt (hdiv _ h0)
        (lt_of_le_of_lt (Nat.sub_le _ _) (Nat.mod_lt _ hq))
      omega
    · have h0 : (c' % q - c % q) • x = 0 := by
        rw [← Nat.sub_add_cancel hle, add_nsmul] at e
        simpa using e.symm
      have := Nat.eq_zero_of_dvd_of_lt (hdiv _ h0)
        (lt_of_le_of_lt (Nat.sub_le _ _) (Nat.mod_lt _ hq))
      omega
  rw [hm' y hy c, hm' y hy c', key]

private theorem sec_eq_of_isSheaf_of_not_nonempty {R : Type} [CommRing R] (N : UpperTheory.Et.PMod R)
    (hN : Presheaf.IsSheaf Scheme.etaleTopology N) {W : Scheme} (hW : ¬ Nonempty ↥W)
    (a b : UpperTheory.Et.sec N W) : a = b := by
  have h0 : a - b = 0 := by
    refine (UpperTheory.locallyHolds_of_forall_and_mono_and_inter_and_pullback Scheme.etaleTopology).2.2.2.2.2.2.1 R N hN W (a - b) ?_
    refine (UpperTheory.etaleLocallyHolds_of_pointwise_cover_or_affine_local W _ ?_).1 ?_
    · intro V V' g k hg
      rw [UpperTheory.Cb.SecLc.rs_comp, hg, pmod_rs_zero]
    · intro x
      exact (hW ⟨x⟩).elim
  exact sub_eq_zero.mp h0

private theorem nsmul_rs_eq_nsmul_rs_of_gen_of_nsmul_eq_zero {R : Type} [CommRing R] (M N : UpperTheory.Et.PMod R)
    (hN : Presheaf.IsSheaf Scheme.etaleTopology N) (q : ℕ) (hq : 0 < q) {U : Scheme}
    (g : UpperTheory.Et.sec M U) (h : UpperTheory.Et.sec N U) (hg : UpperTheory.Et.Gen Scheme.etaleTopology q M g)
    (hh : q • h = 0) {W : Scheme} (k : W ⟶ U) (c c' : ℕ)
    (e : c • UpperTheory.Et.rs M k g = c' • UpperTheory.Et.rs M k g) :
    c • UpperTheory.Et.rs N k h = c' • UpperTheory.Et.rs N k h := by
  by_cases hW : Nonempty ↥W
  · refine nsmul_eq_nsmul_of_nsmul_eq_nsmul_of_exact_order q hq (UpperTheory.Et.rs M k g) ?_ ?_ (UpperTheory.Et.rs N k h) ?_ c c' e
    · rw [← UpperTheory.Cb.SecLc.rs_nsmul, hg.1, pmod_rs_zero]
    · intro c hc
      exact hg.2.1 W k c hW hc
    · rw [← UpperTheory.Cb.SecLc.rs_nsmul, hh, pmod_rs_zero]
  · exact sec_eq_of_isSheaf_of_not_nonempty N hN hW _ _

private theorem pmod_rs_sub {R : Type} [CommRing R] (M : UpperTheory.Et.PMod R) {V U : Scheme}
    (k : V ⟶ U) (a b : UpperTheory.Et.sec M U) :
    UpperTheory.Et.rs M k (a - b) = UpperTheory.Et.rs M k a - UpperTheory.Et.rs M k b :=
  map_sub _ _ _

private theorem pmod_rs_add {R : Type} [CommRing R] (M : UpperTheory.Et.PMod R) {V U : Scheme}
    (k : V ⟶ U) (a b : UpperTheory.Et.sec M U) :
    UpperTheory.Et.rs M k (a + b) = UpperTheory.Et.rs M k a + UpperTheory.Et.rs M k b :=
  map_add _ _ _

private theorem exists_secLc_rel_of_gen_of_nsmul_eq_zero {R : Type} [CommRing R] (M N : UpperTheory.Et.PMod R)
    (hN : Presheaf.IsSheaf Scheme.etaleTopology N) (q : ℕ) (hq : 0 < q) {U : Scheme}
    (g : UpperTheory.Et.sec M U) (h : UpperTheory.Et.sec N U) (hg : UpperTheory.Et.Gen Scheme.etaleTopology q M g)
    (hh : q • h = 0) (y : UpperTheory.Et.sec M U) : ∃ z, UpperTheory.Cb.SecLc.Rel M N g h y z := by
  have hy := hg.2.2 U (𝟙 U) y
  simp only [Category.comp_id] at hy
  obtain ⟨z, hz⟩ := exists_sec_locT_rs_eq_of_compatible N hN
    (fun V k => ∃ c : ℕ, UpperTheory.Et.rs M k y = c • UpperTheory.Et.rs M k g) hy
    (fun V k hk => hk.choose • UpperTheory.Et.rs N k h) (by
      intro V1 V2 W k1 k2 f1 f2 h1 h2 hc
      rw [UpperTheory.Cb.SecLc.rs_nsmul, UpperTheory.Cb.SecLc.rs_nsmul, ← UpperTheory.Cb.SecLc.rs_comp,
        ← UpperTheory.Cb.SecLc.rs_comp, hc]
      apply nsmul_rs_eq_nsmul_rs_of_gen_of_nsmul_eq_zero M N hN q hq g h hg hh
      have e1 := congrArg (UpperTheory.Et.rs M f1) h1.choose_spec
      have e2 := congrArg (UpperTheory.Et.rs M f2) h2.choose_spec
      rw [← UpperTheory.Cb.SecLc.rs_comp, UpperTheory.Cb.SecLc.rs_nsmul, ← UpperTheory.Cb.SecLc.rs_comp] at e1 e2
      rw [hc] at e1
      exact e1.symm.trans e2)
  refine ⟨z, (UpperTheory.locallyHolds_of_forall_and_mono_and_inter_and_pullback Scheme.etaleTopology).2.1 U _ _ hz ?_⟩
  rintro V k ⟨hk, e⟩
  exact ⟨hk.choose, hk.choose_spec, e⟩

private theorem secLc_rel_right_unique_of_gen_of_nsmul_eq_zero {R : Type} [CommRing R] (M N : UpperTheory.Et.PMod R)
    (hN : Presheaf.IsSheaf Scheme.etaleTopology N) (q : ℕ) (hq : 0 < q) {U : Scheme}
    (g : UpperTheory.Et.sec M U) (h : UpperTheory.Et.sec N U) (hg : UpperTheory.Et.Gen Scheme.etaleTopology q M g)
    (hh : q • h = 0) {y : UpperTheory.Et.sec M U} {z z' : UpperTheory.Et.sec N U}
    (h1 : UpperTheory.Cb.SecLc.Rel M N g h y z) (h2 : UpperTheory.Cb.SecLc.Rel M N g h y z') : z = z' := by
  have h12 := (UpperTheory.locallyHolds_of_forall_and_mono_and_inter_and_pullback Scheme.etaleTopology).2.2.1 U _ _ h1 h2
  have h0 : z - z' = 0 := by
    refine (UpperTheory.locallyHolds_of_forall_and_mono_and_inter_and_pullback Scheme.etaleTopology).2.2.2.2.2.2.1 R N hN U (z - z') ?_
    refine (UpperTheory.locallyHolds_of_forall_and_mono_and_inter_and_pullback Scheme.etaleTopology).2.1 U _ _ h12 ?_
    rintro V k ⟨⟨c, ey, ez⟩, ⟨c', ey', ez'⟩⟩
    rw [pmod_rs_sub, ez, ez', nsmul_rs_eq_nsmul_rs_of_gen_of_nsmul_eq_zero M N hN q hq g h hg hh k c c' (ey.symm.trans ey'),
      sub_self]
  exact sub_eq_zero.mp h0

private theorem secLc_rel_add {R : Type} [CommRing R] (M N : UpperTheory.Et.PMod R) {U : Scheme}
    (g : UpperTheory.Et.sec M U) (h : UpperTheory.Et.sec N U) {y y' : UpperTheory.Et.sec M U} {z z' : UpperTheory.Et.sec N U}
    (h1 : UpperTheory.Cb.SecLc.Rel M N g h y z) (h2 : UpperTheory.Cb.SecLc.Rel M N g h y' z') :
    UpperTheory.Cb.SecLc.Rel M N g h (y + y') (z + z') := by
  refine (UpperTheory.locallyHolds_of_forall_and_mono_and_inter_and_pullback Scheme.etaleTopology).2.1 U _ _
    ((UpperTheory.locallyHolds_of_forall_and_mono_and_inter_and_pullback Scheme.etaleTopology).2.2.1 U _ _ h1 h2) ?_
  rintro V k ⟨⟨c, ey, ez⟩, ⟨c', ey', ez'⟩⟩
  exact ⟨c + c', by rw [pmod_rs_add, ey, ey', add_nsmul], by rw [pmod_rs_add, ez, ez', add_nsmul]⟩

private theorem secLc_rel_rs {R : Type} [CommRing R] (M N : UpperTheory.Et.PMod R) {U : Scheme}
    (g : UpperTheory.Et.sec M U) (h : UpperTheory.Et.sec N U) {y : UpperTheory.Et.sec M U} {z : UpperTheory.Et.sec N U}
    (hr : UpperTheory.Cb.SecLc.Rel M N g h y z) {W : Scheme} (k : W ⟶ U) :
    UpperTheory.Cb.SecLc.Rel M N (UpperTheory.Et.rs M k g) (UpperTheory.Et.rs N k h) (UpperTheory.Et.rs M k y)
      (UpperTheory.Et.rs N k z) := by
  refine (UpperTheory.locallyHolds_of_forall_and_mono_and_inter_and_pullback Scheme.etaleTopology).2.1 W _ _
    ((UpperTheory.locallyHolds_of_forall_and_mono_and_inter_and_pullback Scheme.etaleTopology).2.2.2.1 U W k _ hr) ?_
  rintro V k' ⟨c, ey, ez⟩
  exact ⟨c, by rw [← UpperTheory.Cb.SecLc.rs_comp, ← UpperTheory.Cb.SecLc.rs_comp, ey],
    by rw [← UpperTheory.Cb.SecLc.rs_comp, ← UpperTheory.Cb.SecLc.rs_comp, ez]⟩

private theorem secLc_rel_symm {R : Type} [CommRing R] (M N : UpperTheory.Et.PMod R) {U : Scheme}
    (g : UpperTheory.Et.sec M U) (h : UpperTheory.Et.sec N U) {y : UpperTheory.Et.sec M U} {z : UpperTheory.Et.sec N U}
    (hr : UpperTheory.Cb.SecLc.Rel M N g h y z) : UpperTheory.Cb.SecLc.Rel N M h g z y := by
  refine (UpperTheory.locallyHolds_of_forall_and_mono_and_inter_and_pullback Scheme.etaleTopology).2.1 U _ _ hr ?_
  rintro V k ⟨c, ey, ez⟩
  exact ⟨c, ez, ey⟩

private theorem exists_sec_addEquiv_secLc_rel_of_gen {R : Type} [CommRing R] (M N : UpperTheory.Et.PMod R)
    (hM : Presheaf.IsSheaf Scheme.etaleTopology M) (hN : Presheaf.IsSheaf Scheme.etaleTopology N)
    (q : ℕ) (hq : 0 < q) {U : Scheme} (g : UpperTheory.Et.sec M U) (h : UpperTheory.Et.sec N U)
    (hg : UpperTheory.Et.Gen Scheme.etaleTopology q M g) (hh : UpperTheory.Et.Gen Scheme.etaleTopology q N h) :
    ∃ φ : UpperTheory.Et.sec M U ≃+ UpperTheory.Et.sec N U, ∀ y, UpperTheory.Cb.SecLc.Rel M N g h y (φ y) := by
  choose f hf using exists_secLc_rel_of_gen_of_nsmul_eq_zero M N hN q hq g h hg hh.1
  have fadd : ∀ a b, f (a + b) = f a + f b := fun a b =>
    secLc_rel_right_unique_of_gen_of_nsmul_eq_zero M N hN q hq g h hg hh.1 (hf (a + b)) (secLc_rel_add M N g h (hf a) (hf b))
  have finj : Function.Injective f := by
    intro a b e
    have ha := secLc_rel_symm M N g h (hf a)
    have hb := secLc_rel_symm M N g h (hf b)
    rw [e] at ha
    exact secLc_rel_right_unique_of_gen_of_nsmul_eq_zero N M hM q hq h g hh hg.1 ha hb
  have fsurj : Function.Surjective f := by
    intro z
    obtain ⟨y, hy⟩ := exists_secLc_rel_of_gen_of_nsmul_eq_zero N M hM q hq h g hh hg.1 z
    exact ⟨y, secLc_rel_right_unique_of_gen_of_nsmul_eq_zero M N hN q hq g h hg hh.1 (hf y) (secLc_rel_symm N M h g hy)⟩
  exact ⟨AddEquiv.ofBijective (AddMonoidHom.mk' f fadd) ⟨finj, fsurj⟩, hf⟩

private theorem sec_res_twGen (q : ℕ) (i : ℤ) (V' V : Scheme) (g : V' ⟶ V)
    (ζ : Prim q Γ(V, ⊤)) : Sec.res g (twGen i ζ) = twGen i (ζ.map g.appTop.hom) := by
  unfold twGen Sec.res ofRings.sec
  have h := (toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q i)).naturality g.op
  have h2 := congrArg (fun f => ModuleCat.Hom.hom f
    (Submodule.Quotient.mk (Finsupp.single ζ 1) : (Scheme.Γ ⋙ twF q i).obj (op V))) h
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h2
  erw [← h2]
  refine congrArg (ModuleCat.Hom.hom
    ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q i)).app (op V'))) ?_
  simp only [Functor.comp_map, twF, ModuleCat.hom_ofHom]
  erw [Submodule.mapQ_apply, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
  rfl

open UpperTheory.Cb.SecLc in
theorem UpperTheory.exists_tateTwist_sections_equiv_locallyConstant :
    ∀ (q : ℕ) [NeZero q] (i : ℤ), ∃ E : ∀ (V : Scheme.{0}), Prim q Γ(V, ⊤) → (Sec (tw q i) V ≃+ LocallyConstant V (ZMod q)), ∀ (V' V : Scheme.{0}) (g : V' ⟶ V) (ζ : Prim q Γ(V, ⊤)) (s : Sec (tw q i) V), E V' (ζ.map g.appTop.hom) (Sec.res g s) = (E V ζ s).comap ⟨g, g.continuous⟩ := by
  intro q _ i
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hM : Presheaf.IsSheaf Scheme.etaleTopology (tw q i).obj := (tw q i).property
  have hN : Presheaf.IsSheaf Scheme.etaleTopology (UpperTheory.Et.cSh (ZMod q) (ZMod q)).obj :=
    Presheaf.IsSheaf.of_le Scheme.etaleTopology_le_proetaleTopology
      (UpperTheory.Et.cSh (ZMod q) (ZMod q)).property
  have hone : ∀ V : Scheme, UpperTheory.Et.Gen Scheme.etaleTopology q (UpperTheory.Et.cSh (ZMod q) (ZMod q)).obj
      (UpperTheory.Et.cSec (ZMod q) (ZMod q) (ContinuousMap.const V (1 : ZMod q))) := by
    intro V
    refine UpperTheory.constantSheaf_cyclic_generator_of_order (ZMod q) (ZMod q) q 1 (by simp) ?_ ?_ V
    · intro c hc
      rw [nsmul_eq_mul, mul_one] at hc
      exact (ZMod.natCast_eq_zero_iff c q).mp hc
    · intro x
      exact ⟨x.val, by simp⟩
  have hgen : ∀ (V : Scheme) (ζ : Prim q Γ(V, ⊤)),
      UpperTheory.Et.Gen Scheme.etaleTopology q (tw q i).obj (twGen i ζ) :=
    fun V ζ => (UpperTheory.tateTwist_generator_of_primitiveRoot_and_roots_etaleLocal q i V).1 ζ
  choose φ hφ using fun (V : Scheme) (ζ : Prim q Γ(V, ⊤)) =>
    exists_sec_addEquiv_secLc_rel_of_gen (tw q i).obj _ hM hN q hq _ _ (hgen V ζ) (hone V)
  let B : ∀ V : Scheme, C(V, ZMod q) ≃+ UpperTheory.Et.sec (UpperTheory.Et.cSh (ZMod q) (ZMod q)).obj V :=
    fun V => AddEquiv.ofBijective
      (AddMonoidHom.mk' (UpperTheory.Et.cSec (ZMod q) (ZMod q)) (UpperTheory.continuousSections_bijective_additive_natural (ZMod q) (ZMod q) V).2.1)
      (UpperTheory.continuousSections_bijective_additive_natural (ZMod q) (ZMod q) V).1
  let C : ∀ V : Scheme, LocallyConstant V (ZMod q) ≃+ C(V, ZMod q) :=
    fun V => AddEquiv.ofBijective LocallyConstant.toContinuousMapAddMonoidHom
      ⟨LocallyConstant.toContinuousMap_injective,
        fun f => ⟨⟨f, (IsLocallyConstant.iff_continuous f).mpr f.continuous⟩, rfl⟩⟩
  refine ⟨fun V ζ => (φ V ζ).trans ((B V).symm.trans (C V).symm), ?_⟩
  intro V' V g ζ s
  have hB : ∀ f : C(V, ZMod q), B V' (C V' (((C V).symm f).comap ⟨g, g.continuous⟩)) =
      UpperTheory.Et.rs _ g (B V f) := by
    intro f
    show UpperTheory.Et.cSec (ZMod q) (ZMod q) _ = UpperTheory.Et.rs _ g (UpperTheory.Et.cSec (ZMod q) (ZMod q) f)
    rw [(UpperTheory.continuousSections_bijective_additive_natural (ZMod q) (ZMod q) V).2.2.1]
    congr 1
    ext x
    exact congrArg (fun u : C(V, ZMod q) => u (g.base x)) ((C V).apply_symm_apply f)
  have e1 : UpperTheory.Et.rs (tw q i).obj g (twGen i ζ) = twGen i (ζ.map g.appTop.hom) :=
    sec_res_twGen q i V' V g ζ
  have e2 : UpperTheory.Et.rs _ g (UpperTheory.Et.cSec (ZMod q) (ZMod q) (ContinuousMap.const V (1 : ZMod q))) =
      UpperTheory.Et.cSec (ZMod q) (ZMod q) (ContinuousMap.const V' (1 : ZMod q)) := by
    rw [(UpperTheory.continuousSections_bijective_additive_natural (ZMod q) (ZMod q) V).2.2.1]
    rfl
  have hr := secLc_rel_rs _ _ _ _ (hφ V ζ s) g
  rw [e1, e2] at hr
  have key := secLc_rel_right_unique_of_gen_of_nsmul_eq_zero _ _ hN q hq _ _ (hgen V' _) (hone V').1 (hφ V' _ (Sec.res g s)) hr
  apply (C V').injective
  apply (B V').injective
  simp only [AddEquiv.trans_apply, AddEquiv.apply_symm_apply]
  rw [hB, AddEquiv.apply_symm_apply]
  exact key
