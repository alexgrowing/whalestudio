import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ScalarCommutation.TypeSlice
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ScalarCommutation.VanForms
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ScalarCommutation.VanPairs
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ScalarCommutation.CuspIdeal
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ScalarCommutation.PolySupp
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ScalarCommutation.ClsMove
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDoubleCosetDefiniteHermitianFormLevelStatement
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ScalarCommutation.CommOfOpen
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ScalarCommutation.SpecAlg

set_option autoImplicit false

noncomputable section

open MeasureTheory Matrix NumberField Polynomial GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCx GlobalTheory.LKDef GlobalTheory.RootSumWeights GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open UpperTheory.Gal.CertificateRingHomMap (wop wmul)
open UpperTheory.Gal.LocalSmoothExtension
open Formalism.UG (Hecke)
open scoped TensorProduct Classical

namespace UpperTheory.Gal.Spc

section Abstract

variable {H : Type} [Group H] {K : Subgroup H} {M : Type} [AddCommGroup M] [Module ℂ M]
  {T : (H → ℂ) → Module.End ℂ M} {J : Type}

private theorem polyFn_single (ψ : J → H → ℂ) (w : List J) (c : ℂ) (f : H → ℂ) :
    polyFn K ψ (Finsupp.single w c) f = c • wordFn K ψ w f :=
  Finsupp.sum_single_index (zero_smul _ _)

private theorem polyFn_zero (ψ : J → H → ℂ) (f : H → ℂ) : polyFn K ψ 0 f = 0 :=
  Finsupp.sum_zero_index

private theorem polyFn_add (ψ : J → H → ℂ) (s t : List J →₀ ℂ) (f : H → ℂ) :
    polyFn K ψ (s + t) f = polyFn K ψ s f + polyFn K ψ t f :=
  Finsupp.sum_add_index' (fun _ => zero_smul _ _) (fun _ _ _ => add_smul _ _ _)

private theorem word_mem (ψ : J → H → ℂ) (f : H → ℂ) (hmem : ∀ s, polyFn K ψ s f ∈ Hecke ℂ K) (w : List J) :
    wordFn K ψ w f ∈ Hecke ℂ K := by
  have h := hmem (Finsupp.single w 1)
  rwa [polyFn_single, one_smul] at h

private theorem T_word (hmul : ∀ f ∈ Hecke ℂ K, ∀ f' ∈ Hecke ℂ K, T (Formalism.UG.conv K f f') = T f * T f')
    (ψ : J → H → ℂ) (hψ : ∀ j, ψ j ∈ Hecke ℂ K) (f : H → ℂ) (hmem : ∀ w, wordFn K ψ w f ∈ Hecke ℂ K) (w : List J) :
    T (wordFn K ψ w f) = (w.map fun j => T (ψ j)).prod * T f := by
  induction w with
  | nil => simp [wordFn]
  | cons j w ih =>
    have h : wordFn K ψ (j :: w) f = Formalism.UG.conv K (ψ j) (wordFn K ψ w f) := rfl
    rw [h, hmul _ (hψ j) _ (hmem w), ih, List.map_cons, List.prod_cons, mul_assoc]

private theorem T_poly (hT0 : T 0 = 0) (hmul : ∀ f ∈ Hecke ℂ K, ∀ f' ∈ Hecke ℂ K, T (Formalism.UG.conv K f f') = T f * T f')
    (hlin : ∀ f ∈ Hecke ℂ K, ∀ f' ∈ Hecke ℂ K, ∀ c : ℂ, T (c • f + f') = c • T f + T f')
    (ψ : J → H → ℂ) (hψ : ∀ j, ψ j ∈ Hecke ℂ K) (f : H → ℂ) (hmem : ∀ s, polyFn K ψ s f ∈ Hecke ℂ K)
    (s : List J →₀ ℂ) : T (polyFn K ψ s f) = wop (fun j => T (ψ j)) s * T f := by
  induction s using Finsupp.induction_linear with
  | zero => rw [polyFn_zero, hT0, UpperTheory.Gal.CertificateRingHomMap.wop_zero, zero_mul]
  | add s t hs ht =>
    have h : polyFn K ψ (s + t) f = (1 : ℂ) • polyFn K ψ s f + polyFn K ψ t f := by
      rw [one_smul, polyFn_add]
    rw [h, hlin _ (hmem s) _ (hmem t), one_smul, hs, ht, UpperTheory.Gal.CertificateRingHomMap.wop_add, add_mul]
  | single w c =>
    have h : polyFn K ψ (Finsupp.single w c) f = c • wordFn K ψ w f + 0 := by
      rw [polyFn_single, add_zero]
    rw [h, hlin _ (word_mem ψ f hmem w) _ (Submodule.zero_mem _), hT0, add_zero,
      T_word hmul ψ hψ f (word_mem ψ f hmem) w, UpperTheory.Gal.CertificateRingHomMap.wop_single, smul_mul_assoc]

private theorem T_pow (hmul : ∀ f ∈ Hecke ℂ K, ∀ f' ∈ Hecke ℂ K, T (Formalism.UG.conv K f f') = T f * T f')
    (u e : H → ℂ) (hu : u ∈ Hecke ℂ K) (hmem : ∀ n, powFn K u e n ∈ Hecke ℂ K) (n : ℕ) :
    T (powFn K u e n) = T u ^ n * T e := by
  induction n with
  | zero => simp [powFn]
  | succ n ih =>
    have h : powFn K u e (n + 1) = Formalism.UG.conv K u (powFn K u e n) := Function.iterate_succ_apply' _ _ _
    rw [h, hmul _ hu _ (hmem n), ih, pow_succ', mul_assoc]

private theorem C_pow {C : (H → ℂ) → Prop}
    (hid : ∀ a ∈ Hecke ℂ K, ∀ f ∈ Hecke ℂ K, C f → C (Formalism.UG.conv K a f))
    (u e : H → ℂ) (hu : u ∈ Hecke ℂ K) (he : C e) (hmem : ∀ n, powFn K u e n ∈ Hecke ℂ K) (n : ℕ) :
    C (powFn K u e n) := by
  induction n with
  | zero => exact he
  | succ n ih =>
    have h : powFn K u e (n + 1) = Formalism.UG.conv K u (powFn K u e n) := Function.iterate_succ_apply' _ _ _
    rw [h]
    exact hid _ hu _ (hmem n) ih

private theorem C_word {C : (H → ℂ) → Prop}
    (hid : ∀ a ∈ Hecke ℂ K, ∀ f ∈ Hecke ℂ K, C f → C (Formalism.UG.conv K a f))
    (ψ : J → H → ℂ) (hψ : ∀ j, ψ j ∈ Hecke ℂ K) (f : H → ℂ) (hf : C f)
    (hmem : ∀ w, wordFn K ψ w f ∈ Hecke ℂ K) (w : List J) : C (wordFn K ψ w f) := by
  induction w with
  | nil => exact hf
  | cons j w ih => exact hid _ (hψ j) _ (hmem w) ih

private theorem C_poly {C : (H → ℂ) → Prop}
    (hid : ∀ a ∈ Hecke ℂ K, ∀ f ∈ Hecke ℂ K, C f → C (Formalism.UG.conv K a f)) (h0 : C 0)
    (hlin : ∀ f ∈ Hecke ℂ K, ∀ f' ∈ Hecke ℂ K, ∀ c : ℂ, C f → C f' → C (c • f + f'))
    (ψ : J → H → ℂ) (hψ : ∀ j, ψ j ∈ Hecke ℂ K) (f : H → ℂ) (hf : C f)
    (hmem : ∀ s, polyFn K ψ s f ∈ Hecke ℂ K) (s : List J →₀ ℂ) : C (polyFn K ψ s f) := by
  induction s using Finsupp.induction_linear with
  | zero => rw [polyFn_zero]; exact h0
  | add s t hs ht =>
    have h : polyFn K ψ (s + t) f = (1 : ℂ) • polyFn K ψ s f + polyFn K ψ t f := by
      rw [one_smul, polyFn_add]
    rw [h]
    exact hlin _ (hmem s) _ (hmem t) _ hs ht
  | single w c =>
    have h : polyFn K ψ (Finsupp.single w c) f = c • wordFn K ψ w f + 0 := by
      rw [polyFn_single, add_zero]
    rw [h]
    exact hlin _ (word_mem ψ f hmem w) _ (Submodule.zero_mem _) _
      (C_word hid ψ hψ f hf (word_mem ψ f hmem) w) h0

private theorem hecke_relation_image (hmul : ∀ f ∈ Hecke ℂ K, ∀ f' ∈ Hecke ℂ K, T (Formalism.UG.conv K f f') = T f * T f')
    (ψ : J → H → ℂ) (e u u' : H → ℂ) (hψ : ∀ j, ψ j ∈ Hecke ℂ K) (he : e ∈ Hecke ℂ K) (hu : u ∈ Hecke ℂ K)
    (hu' : u' ∈ Hecke ℂ K) (hrel : Rel (Formalism.UG.conv K) ψ e u u') (hB : Formalism.UG.conv K u e ∈ Hecke ℂ K)
    (hA : ∀ j, Formalism.UG.conv K (ψ j) e ∈ Hecke ℂ K) :
    Rel (· * ·) (fun j => T (ψ j)) (T e) (T u) (T u') := by
  refine ⟨?_, fun j => ?_, ?_, fun j j' => ?_, fun j => ?_, ?_⟩
  · have h := congrArg T hrel.idem
    rwa [hmul _ he _ he] at h
  · have h := congrArg T (hrel.eT j)
    rwa [hmul _ he _ (hA j), hmul _ (hψ j) _ he] at h
  · have h := congrArg T hrel.eu
    rwa [hmul _ he _ hB, hmul _ hu _ he] at h
  · have h := congrArg T (hrel.TT j j')
    rwa [hmul _ (hψ j) _ (hA j'), hmul _ (hψ j') _ he, hmul _ (hψ j') _ (hA j), hmul _ (hψ j) _ he] at h
  · have h := congrArg T (hrel.uT j)
    rwa [hmul _ hu _ (hA j), hmul _ (hψ j) _ he, hmul _ (hψ j) _ hB, hmul _ hu _ he] at h
  · have h := congrArg T hrel.inv
    rwa [hmul _ hu' _ hB, hmul _ hu _ he] at h

end Abstract

private theorem forms_fin {Γ H V : Type} [Group Γ] [Group H] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ι : Γ →* H) (K : Subgroup H) (ξ : Representation ℂ Γ V)
    (hf : Finite (DoubleCoset.Quotient (ι.range : Set H) (K : Set H))) :
    FiniteDimensional ℂ (HeckeTraceForms.forms ι K ξ) := by
  haveI := hf
  obtain ⟨r, hr⟩ : ∃ r : DoubleCoset.Quotient (ι.range : Set H) (K : Set H) → H, ∀ g : H,
      ∃ γ : Γ, ∃ k ∈ K, g = ι γ * r (DoubleCoset.mk ι.range K g) * k := by
    refine ⟨fun q => Quotient.out q, fun g => ?_⟩
    obtain ⟨h, ⟨γ, rfl⟩, k, hk, e⟩ := (DoubleCoset.eq ι.range K _ _).1
      (DoubleCoset.out_eq' ι.range K (DoubleCoset.mk ι.range K g))
    exact ⟨γ, k, hk, e⟩
  let L : HeckeTraceForms.forms ι K ξ →ₗ[ℂ] (DoubleCoset.Quotient (ι.range : Set H) (K : Set H) → V) :=
    { toFun := fun φ q => (φ : H → V) (r q)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  refine FiniteDimensional.of_injective L ?_
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro φ hφ
  apply Subtype.ext
  funext g
  have h0 : (φ : H → V) (r (DoubleCoset.mk ι.range K g)) = 0 :=
    congrFun hφ (DoubleCoset.mk ι.range K g)
  obtain ⟨γ, k, hk, e⟩ := hr g
  have h1 : (φ : H → V) g = ξ γ ((φ : H → V) (r (DoubleCoset.mk ι.range K g))) := by
    conv_lhs => rw [e]
    rw [φ.2.2 k hk, φ.2.1]
  rw [h1, h0, map_zero]
  rfl

def SpecOfF : Prop := ForPlaces fun p _ G Lv C R => Finite (DFCls G) →
  ∀ (D : Datum p) (L : GlobalTheory.LKGeo.Link D G) (lam : (D.F →+* ℂ) → Fin G.n → ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (ξ : Representation ℂ (G.Cˣ × ℚˣ) V), IsWt L lam ξ →
    ∀ (J : Type) (ψ : J → G.GAf → ℂ) (θ : J → ℂ) (e u u' : G.GAf → ℂ),
    (∀ j, ψ j ∈ Hecke ℂ Lv.K.toSubgroup) → e ∈ Hecke ℂ Lv.K.toSubgroup → u ∈ Hecke ℂ Lv.K.toSubgroup →
    u' ∈ Hecke ℂ Lv.K.toSubgroup → Rel (Formalism.UG.conv Lv.K.toSubgroup) ψ e u u' → C e →
    (∀ n : ℕ, 1 ≤ n → ∃ A : Set G.GAf, (∀ g ∈ A, R g ∧ RegAf G g) ∧ (∀ j a, ψ j a ≠ 0 → ∀ g ∈ A, a * g ∈ A) ∧
      ∀ g, powFn Lv.K.toSubgroup u e n g ≠ 0 → g ∈ A) →
    HasEig G ξ Lv.K.toSubgroup ψ θ e → ∃ n : ℕ, 1 ≤ n ∧ Spec L lam Lv.K.toSubgroup ψ θ (powFn Lv.K.toSubgroup u e n)

end UpperTheory.Gal.Spc

theorem UpperTheory.Gal.Spc.specOfF :
    UpperTheory.Gal.Spc.SpecOfF := by
  intro p _ G hGa Lv k _ _ _ _ _ _ _ P H _ _ _ _ S k₁ _ _ P₁ hfin D L lam V _ _ _ ξ hwt J ψ θ e u u' hψ he hu hu' hrel hCe hA hEig
  have hW := words p G Lv J ψ e u u' hψ he hu hrel
  have hp : ∀ n, powFn Lv.K.toSubgroup u e n ∈ Hecke ℂ Lv.K.toSubgroup := fun n => (hW n).1
  have hpoly : ∀ n s, polyFn Lv.K.toSubgroup ψ s (powFn Lv.K.toSubgroup u e n) ∈ Hecke ℂ Lv.K.toSubgroup :=
    fun n => (hW n).2.1
  obtain ⟨hCi, hC0, hCl⟩ := cuspIdeal p G hGa Lv k P H S k₁ P₁
  obtain ⟨q₀, Φ₀, hΦ₀, hne, hΦe, hΦψ⟩ := clsMove p G V ξ Lv.K.toSubgroup J ψ θ e hEig
  letI : Fintype (DFCls G) := Fintype.ofFinite _
  have hop := fun q : DFCls G => opAlg p G Lv V ξ (Quot.out q)
  choose T hT0 hT using hop
  haveI hfd' : ∀ q : DFCls G, FiniteDimensional ℂ (HeckeTraceForms.forms (Quot.out q).emb (Lv.K.toSubgroup.prod (Kp G))
      (ξ.comp (grp G (Quot.out q).β).subtype)) := fun q =>
    forms_fin (Quot.out q).emb _ _ (GlobalTheory.T.finite_doubleCoset_definiteHermitianForm_level p G hGa Lv (Kp G) (Subgroup.Commensurable.refl _) (Quot.out q))
  have hmul : ∀ q, ∀ f ∈ Hecke ℂ Lv.K.toSubgroup, ∀ f' ∈ Hecke ℂ Lv.K.toSubgroup,
      T q (Formalism.UG.conv Lv.K.toSubgroup f f') = T q f * T q f' := fun q f hf f' hf' => ((hT q f hf).2.2 f' hf').1
  have hlin : ∀ q, ∀ f ∈ Hecke ℂ Lv.K.toSubgroup, ∀ f' ∈ Hecke ℂ Lv.K.toSubgroup, ∀ c : ℂ,
      T q (c • f + f') = c • T q f + T q f' := fun q f hf f' hf' => ((hT q f hf).2.2 f' hf').2
  have hB : Formalism.UG.conv Lv.K.toSubgroup u e ∈ Hecke ℂ Lv.K.toSubgroup := hp 1
  have hAj : ∀ j, Formalism.UG.conv Lv.K.toSubgroup (ψ j) e ∈ Hecke ℂ Lv.K.toSubgroup := fun j =>
    word_mem ψ _ (hpoly 0) [j]
  have key := specAlg (DFCls G) J
    (fun q => HeckeTraceForms.forms (Quot.out q).emb (Lv.K.toSubgroup.prod (Kp G)) (ξ.comp (grp G (Quot.out q).β).subtype))
    (fun q j => T q (ψ j)) (fun q => T q e) (fun q => T q u) (fun q => T q u') θ
    (fun q => hecke_relation_image (hmul q) ψ e u u' hψ he hu hu' hrel hB hAj)
    ⟨q₀, ⟨Φ₀, hΦ₀⟩, fun h => hne (congrArg Subtype.val h),
      Subtype.ext (((hT q₀ e he).1 ⟨Φ₀, hΦ₀⟩).trans hΦe),
      fun j => Subtype.ext (((hT q₀ (ψ j) (hψ j)).1 ⟨Φ₀, hΦ₀⟩).trans (hΦψ j))⟩
  obtain ⟨n, hn, a, ha⟩ := key
  refine ⟨n, hn, (hW n).2.2.1, V, inferInstance, inferInstance, inferInstance, ξ, hwt, fun s hs => ⟨a, ?_, ?_⟩⟩
  · obtain ⟨A, hAR, hAψ, hAp⟩ := hA n hn
    have hsup := (hW n).2.2.2 A hAψ hAp
    have hCF : S.Cusp (polyFn Lv.K.toSubgroup ψ (wmul a s) (powFn Lv.K.toSubgroup u e n)) :=
      C_poly hCi hC0 hCl ψ hψ _ (C_pow hCi u e hu hCe hp n) (hpoly n) _
    have hR : ∀ g, polyFn Lv.K.toSubgroup ψ (wmul a s) (powFn Lv.K.toSubgroup u e n) g ≠ 0 →
        (P₁.at g).charpoly.Separable := fun g hg => (hAR g (hsup _ g hg)).1
    exact ⟨fun g hg => (hAR g (hsup _ g hg)).2,
      vanPairs p G hGa Lv k P H S k₁ P₁ _ (hpoly n _) hCF hR,
      vanForms p G hGa Lv k P H S k₁ P₁ _ (hpoly n _) hCF hR⟩
  · have hq : ∀ q : DFCls G, (Quot.out q).trace ξ Lv.K.toSubgroup
        (polyFn Lv.K.toSubgroup ψ (wmul a s) (powFn Lv.K.toSubgroup u e n)) (Kp G) (oneP G) =
        LinearMap.trace ℂ _ (wop (fun j => T q (ψ j)) (wmul a s) * (T q u ^ n * T q e)) := fun q => by
      rw [(hT q _ (hpoly n _)).2.1, T_poly (hT0 q) (hmul q) (hlin q) ψ hψ _ (hpoly n),
        T_pow (hmul q) u e hu hp n]
    unfold dTrace
    rw [finsum_eq_sum_of_fintype]
    simp only [hq]
    exact ha s hs
