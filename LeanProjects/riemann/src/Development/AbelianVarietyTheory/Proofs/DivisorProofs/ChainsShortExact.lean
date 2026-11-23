import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HypercohomologyLongExactFirstOfInjectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChosenInjectiveResolutionEtaleSheafPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSpaceChainsMayerVietorisShortExact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HypercohomologyPullbackBiprodInlInrBijective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MonoFreeEtaleMayerVietorisLeftMapStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleMayerVietorisFreeRightEpiStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleMayerVietorisFreeSequenceExactStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMayerVietorisConnectingExact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreeEtaleSheafExcisionShortExact
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
open scoped TensorProduct

namespace GlobalTheory.EtC.MVEtale

theorem cpull_neg {R : Type} [CommRing R] {K L : Cx R} (g : K ⟶ L) (I : Cx R) (n : ℤ) (x : CohomologyClass L I n) :
    cpull (-g) I n x = -cpull g I n x := by
  have h := BiprodCls.cpull_add g (-g) I n x
  rw [add_neg_cancel, BiprodCls.cpull_zero] at h
  exact eq_neg_of_add_eq_zero_right h.symm

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
open scoped TensorProduct in
theorem _root_.GlobalTheory.EtC.MVEtale.cpull_lift_neg {R : Type} [CommRing R] {K M N : _root_.GlobalTheory.EtC.Cx R} (a : K ⟶ M) (b : K ⟶ N) (I : _root_.GlobalTheory.EtC.Cx R) (n : ℤ)
    (x : CohomologyClass (M ⊞ N) I n) :
    _root_.GlobalTheory.EtC.cpull (biprod.lift a (-b)) I n x =
      _root_.GlobalTheory.EtC.cpull a I n (_root_.GlobalTheory.EtC.cpull (biprod.inl : M ⟶ M ⊞ N) I n x) - _root_.GlobalTheory.EtC.cpull b I n (_root_.GlobalTheory.EtC.cpull (biprod.inr : N ⟶ M ⊞ N) I n x) := by
  rw [biprod.lift_eq, _root_.GlobalTheory.EtC.BiprodCls.cpull_add, Preadditive.neg_comp,
    _root_.GlobalTheory.EtC.MayerVietoris.cpull_neg, _root_.GlobalTheory.EtC.BiprodCls.cpull_cpull,
    _root_.GlobalTheory.EtC.BiprodCls.cpull_cpull, sub_eq_add_neg]

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
open scoped TensorProduct in
theorem _root_.GlobalTheory.EtC.MVEtale.cpull_desc_pair {R : Type} [CommRing R] {M N L : _root_.GlobalTheory.EtC.Cx R} (c : M ⟶ L) (d : N ⟶ L) (I : _root_.GlobalTheory.EtC.Cx R) (n : ℤ)
    (z : CohomologyClass L I n) :
    (_root_.GlobalTheory.EtC.cpull (biprod.inl : M ⟶ M ⊞ N) I n (_root_.GlobalTheory.EtC.cpull (biprod.desc c d) I n z),
      _root_.GlobalTheory.EtC.cpull (biprod.inr : N ⟶ M ⊞ N) I n (_root_.GlobalTheory.EtC.cpull (biprod.desc c d) I n z)) = (_root_.GlobalTheory.EtC.cpull c I n z, _root_.GlobalTheory.EtC.cpull d I n z) := by
  rw [_root_.GlobalTheory.EtC.BiprodCls.cpull_cpull, _root_.GlobalTheory.EtC.BiprodCls.cpull_cpull, biprod.inl_desc,
    biprod.inr_desc]

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
open scoped TensorProduct in
theorem _root_.GlobalTheory.EtC.MVEtale.chains_shortExact (R : Type) [CommRing R] (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A']
    [Algebra.Etale A A'] (f : A)
    (h1 : ∀ a' : A', ∃ a : A, a' - algebraMap A A' a ∈ Ideal.span {algebraMap A A' f})
    (h2 : ∀ a : A, algebraMap A A' a ∈ Ideal.span {algebraMap A A' f} → a ∈ Ideal.span {f}) :
    ∃ w, (ShortComplex.mk (biprod.lift ((_root_.GlobalTheory.EtC.chains R).map (_root_.GlobalTheory.EtC.spMap (Localization.awayMap (algebraMap A A') f)))
      (-(_root_.GlobalTheory.EtC.chains R).map (_root_.GlobalTheory.EtC.spMap (algebraMap A' (Localization.Away (algebraMap A A' f))))))
      (biprod.desc ((_root_.GlobalTheory.EtC.chains R).map (_root_.GlobalTheory.EtC.spMap (algebraMap A (Localization.Away f)))) ((_root_.GlobalTheory.EtC.chains R).map (_root_.GlobalTheory.EtC.spMap (algebraMap A A')))) w).ShortExact := by
  have hcomp : (Localization.awayMap (algebraMap A A') f).comp (algebraMap A (Localization.Away f)) =
      (algebraMap A' (Localization.Away (algebraMap A A' f))).comp (algebraMap A A') :=
    IsLocalization.map_comp _
  have hsq : _root_.GlobalTheory.EtC.spMap (Localization.awayMap (algebraMap A A') f) ≫
      _root_.GlobalTheory.EtC.spMap (algebraMap A (Localization.Away f)) =
      _root_.GlobalTheory.EtC.spMap (algebraMap A' (Localization.Away (algebraMap A A' f))) ≫
      _root_.GlobalTheory.EtC.spMap (algebraMap A A') := by
    unfold _root_.GlobalTheory.EtC.spMap
    rw [← Functor.map_comp, ← Functor.map_comp, ← Spec.map_comp, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hcomp]
  have hchains := ((_root_.GlobalTheory.EtC.chains R).map_comp _ _).symm.trans
    ((congrArg (_root_.GlobalTheory.EtC.chains R).map hsq).trans
      ((_root_.GlobalTheory.EtC.chains R).map_comp _ _))
  obtain ⟨w', hw'⟩ := _root_.GlobalTheory.EtC.MVExact.mv_exact R A A' f h1 h2
  have hfree := _root_.GlobalTheory.EtC.MVFree.shortExact R A A' f ⟨h1, h2⟩ w'
  have w : biprod.lift ((_root_.GlobalTheory.EtC.chains R).map (_root_.GlobalTheory.EtC.spMap (Localization.awayMap (algebraMap A A') f)))
      (-(_root_.GlobalTheory.EtC.chains R).map (_root_.GlobalTheory.EtC.spMap (algebraMap A' (Localization.Away (algebraMap A A' f))))) ≫
      biprod.desc ((_root_.GlobalTheory.EtC.chains R).map (_root_.GlobalTheory.EtC.spMap (algebraMap A (Localization.Away f))))
        ((_root_.GlobalTheory.EtC.chains R).map (_root_.GlobalTheory.EtC.spMap (algebraMap A A'))) = 0 := by
    rw [biprod.lift_desc, Preadditive.neg_comp, hchains, add_neg_cancel]
  refine ⟨w, HomologicalComplex.shortExact_of_degreewise_shortExact _ fun i => ?_⟩
  rcases lt_or_ge 0 i with hi | hi
  · have hX₁ := _root_.GlobalTheory.EtC.chains_isZero_pos R
      (_root_.GlobalTheory.EtC.sp (Localization.Away (algebraMap A A' f))) i hi
    have hX₃ := _root_.GlobalTheory.EtC.chains_isZero_pos R (_root_.GlobalTheory.EtC.sp A) i hi
    have hX₂ : IsZero (((_root_.GlobalTheory.EtC.chains R).obj (_root_.GlobalTheory.EtC.sp (Localization.Away f)) ⊞
        (_root_.GlobalTheory.EtC.chains R).obj (_root_.GlobalTheory.EtC.sp A')).X i) :=
      IsZero.of_iso ((biprod_isZero_iff _ _).2
        ⟨_root_.GlobalTheory.EtC.chains_isZero_pos R _ i hi, _root_.GlobalTheory.EtC.chains_isZero_pos R _ i hi⟩)
        (HomologicalComplex.biprodXIso _ _ i)
    exact
      { exact := ShortComplex.exact_of_isZero_X₂ _ hX₂
        mono_f := ⟨fun _ _ _ => hX₁.eq_of_tgt _ _⟩
        epi_g := ⟨fun _ _ _ => hX₃.eq_of_src _ _⟩ }
  · obtain ⟨p, rfl⟩ : ∃ p : ℕ, i = -(p : ℤ) := ⟨i.natAbs, by omega⟩
    exact _root_.GlobalTheory.EtC.mv_map_shortExact (HomologicalComplex.eval _ _ (-(p : ℤ)))
      (a := (_root_.GlobalTheory.EtC.chains R).map (_root_.GlobalTheory.EtC.spMap (Localization.awayMap (algebraMap A A') f)))
      (b := (_root_.GlobalTheory.EtC.chains R).map (_root_.GlobalTheory.EtC.spMap (algebraMap A' (Localization.Away (algebraMap A A' f)))))
      (f := (_root_.GlobalTheory.EtC.chains R).map (_root_.GlobalTheory.EtC.spMap (algebraMap A (Localization.Away f))))
      (g := (_root_.GlobalTheory.EtC.chains R).map (_root_.GlobalTheory.EtC.spMap (algebraMap A A')))
      (W' := (_root_.GlobalTheory.EtC.free R).obj (yoneda.obj (Spec (CommRingCat.of (Localization.Away ((algebraMap A A') f))))))
      (X' := (_root_.GlobalTheory.EtC.free R).obj (yoneda.obj (Spec (CommRingCat.of (Localization.Away f)))))
      (Y' := (_root_.GlobalTheory.EtC.free R).obj (yoneda.obj (Spec (CommRingCat.of A'))))
      (Z' := (_root_.GlobalTheory.EtC.free R).obj (yoneda.obj (Spec (CommRingCat.of A))))
      (a' := (_root_.GlobalTheory.EtC.free R).map (yoneda.map (Spec.map (CommRingCat.ofHom (Localization.awayMap (algebraMap A A') f)))))
      (b' := (_root_.GlobalTheory.EtC.free R).map (yoneda.map (Spec.map (CommRingCat.ofHom (algebraMap A' (Localization.Away (algebraMap A A' f)))))))
      (f' := (_root_.GlobalTheory.EtC.free R).map (yoneda.map (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away f))))))
      (g' := (_root_.GlobalTheory.EtC.free R).map (yoneda.map (Spec.map (CommRingCat.ofHom (algebraMap A A')))))
      (_root_.GlobalTheory.EtC.chainsXIso R _ p) (_root_.GlobalTheory.EtC.chainsXIso R _ p)
      (_root_.GlobalTheory.EtC.chainsXIso R _ p) (_root_.GlobalTheory.EtC.chainsXIso R _ p)
      (_root_.GlobalTheory.EtC.chainsXIso_naturality R _ p)
      (_root_.GlobalTheory.EtC.chainsXIso_naturality R _ p)
      (_root_.GlobalTheory.EtC.chainsXIso_naturality R _ p)
      (_root_.GlobalTheory.EtC.chainsXIso_naturality R _ p) w w' hfree

end GlobalTheory.EtC.MVEtale
