import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.CycleSplitFiltStepSt
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.GenericPointSectionHypotheses
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.TwistAlg
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSectionCountDropFiltStep
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSurjectiveClosed
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial Filter

noncomputable section

universe u w

namespace CycleSplit.Filt.Step

theorem length_ne_top_of_smul_eq_zero {S : Type u} [CommRing S] {T : Type w} [AddCommGroup T] [Module S T]
    [Module.Finite S T] (𝔪 : Ideal S) [𝔪.IsMaximal] (h : ∀ a ∈ 𝔪, ∀ t : T, a • t = 0) :
    Module.length S T ≠ ⊤ := by
  let := Ideal.Quotient.field 𝔪
  have hT : Module.IsTorsionBySet S T 𝔪 := by
    intro t a
    exact h a a.2 t
  let : Module (S ⧸ 𝔪) T := hT.module
  have : IsScalarTower S (S ⧸ 𝔪) T := hT.isScalarTower
  have : Module.Finite (S ⧸ 𝔪) T := Module.Finite.of_restrictScalars_finite S (S ⧸ 𝔪) T
  rw [Module.length_eq_of_surjective (R := S ⧸ 𝔪) (M := T) Ideal.Quotient.mk_surjective]
  exact Module.length_ne_top

theorem proof (hSC : SurjectiveClosed.Statement.{u, w}) (hFS : FiniteSections.Statement.{u, w}) :
    CycleSplit.Filt.Step.Statement.{u, w} := by
  classical
  intro S _ _ Ω _ _ N x 𝔪 h𝔪 K pp g e hKh hK h𝔪K hg hpph hpp Q
  obtain ⟨c₀, hc₀⟩ := hSC S Ω N x Q pp hpph
  filter_upwards [eventually_ge_atTop (c₀ + e).toNat] with c hc
  have hce : c₀ ≤ (c : ℤ) - e := by
    have := Int.toNat_le.mp hc
    omega
  set F : SubSystem S x Ω := Q.twist (twistSys S x (c : ℤ)) with hF
  set F' : SubSystem S x Ω := Q.twist (twistSys S x ((c : ℤ) - e)) with hF'
  have hF'eq : F' = F.twist (twistSys S x (-(e : ℤ))) := by
    rw [hF', hF, SubSystem.twist_assoc, twistSys_twist_eq_add, sub_eq_add_neg]
  have hsub : ∀ (J : Ideal (Poly S N)) (I : Chart x),
      (F.twist (idealSys x J)).sub I = idealMod J I * F.sub I :=
    fun J I ↦ SubSystem.twist_sub_eq_mul_of_line _ _ I
  have hF's : ∀ I, F'.sub I = twistMod S x (-(e : ℤ)) I * F.sub I := fun I ↦ by
    rw [hF'eq]; exact SubSystem.twist_sub_eq_mul_of_line _ _ I
  have hF'p : ∀ I, (F'.twist (idealSys x pp)).sub I =
      idealMod pp I * (twistMod S x (-(e : ℤ)) I * F.sub I) := fun I ↦ by
    rw [SubSystem.twist_sub_eq_mul_of_line, hF's]; rfl
  have hinv : ∀ I, ∃ Q' : Submodule (chartRing S x I) Ω, F.sub I * Q' = 1 :=
    fun I ↦ (Q.tensorProd (twistBundle S x (c : ℤ))).invertible I

  have hgK' : ∀ I : Chart x, ∀ y ∈ F'.sub I,
      aeval x g * y ∈ (F.twist (idealSys x (K ⊔ Ideal.span {g}))).sub I := by
    intro I y hy
    obtain ⟨i, hi⟩ := I.2.1
    rw [hF's, twistMod_eq_span _ I hi] at hy
    obtain ⟨q, hq, rfl⟩ := Submodule.mem_span_singleton_mul.mp hy
    rw [hsub]
    have hγ : aeval x g / x i ^ e ∈ idealMod (K ⊔ Ideal.span {g}) I :=
      Submodule.subset_span ⟨g, X i ^ e, e, Ideal.mem_sup_right (Ideal.mem_span_singleton_self g),
        pow_mem (X_mem_monos hi) e, hg, isHomogeneous_X_pow i e, by simp⟩
    have h1 : aeval x g * (x i ^ (-(e : ℤ)) * q) = aeval x g / x i ^ e * q := by
      rw [← mul_assoc, zpow_neg, zpow_natCast, div_eq_mul_inv]
    rw [h1]
    exact Submodule.mul_mem_mul hγ hq
  have hU : ∀ I (y : Ω), y ∈ F'.sub I → aeval x g * y ∈ (F.twist (idealSys x K)).sub I →
      y ∈ (F'.twist (idealSys x pp)).sub I := by
    intro I y hy hgy
    obtain ⟨i, hi⟩ := I.2.1
    obtain ⟨Q', hQ'⟩ := hinv I
    rw [hF's] at hy
    rw [hsub] at hgy
    rw [hF'p]
    exact SectionCount.Drop.Filt.Step.mem_chart_of_mul_mem hK hpp hg I hi _ Q' hQ' hy hgy
  have hC : ∀ I (y : Ω), y ∈ (F'.twist (idealSys x pp)).sub I →
      aeval x g * y ∈ (F.twist (idealSys x K)).sub I := by
    intro I y hy
    obtain ⟨i, hi⟩ := I.2.1
    rw [hF'p] at hy
    rw [hsub]
    exact SectionCount.Drop.Filt.Step.mul_mem_chart hpp hg I hi _ hy
  have hE : ∀ s ∈ (F.twist (idealSys x (K ⊔ Ideal.span {g}))).secs, ∀ I,
      ∃ y ∈ F'.sub I, s - aeval x g * y ∈ (F.twist (idealSys x K)).sub I := by
    intro s hs I
    obtain ⟨i, hi⟩ := I.2.1
    have hsI := SectionCount.Drop.Filt.Step.mem_secs_iff'.mp hs I
    rw [hsub] at hsI
    rw [hF's, hsub]
    exact SectionCount.Drop.Filt.Step.exists_chart hKh hg I hi _ hsI

  have hWV : ∀ z, z ∈ (F.twist (idealSys x K)).secs →
      z ∈ (F.twist (idealSys x (K ⊔ Ideal.span {g}))).secs := by
    intro z hz
    refine SectionCount.Drop.Filt.Step.mem_secs_iff'.mpr fun I ↦ ?_
    have h1 := SectionCount.Drop.Filt.Step.mem_secs_iff'.mp hz I
    rw [hsub] at h1 ⊢
    have hle : idealMod K I ≤ idealMod (K ⊔ Ideal.span {g}) I := by
      refine Submodule.span_mono ?_
      rintro _ ⟨f, s, d, hf, hs, hfd, hsd, rfl⟩
      exact ⟨f, s, d, Ideal.mem_sup_left hf, hs, hfd, hsd, rfl⟩
    exact (Submodule.mul_le.mpr fun m hm n hn ↦ Submodule.mul_mem_mul (hle hm) hn) h1
  have hVH : ∀ z, z ∈ (F.twist (idealSys x (K ⊔ Ideal.span {g}))).secs → z ∈ F.secs := fun z hz ↦
    SectionCount.Drop.Filt.Step.mem_secs_iff'.mpr fun I ↦ SurjectiveClosed.twist_idealSys_le F _ I (SectionCount.Drop.Filt.Step.mem_secs_iff'.mp hz I)
  have hgsec : ∀ y ∈ F'.secs, aeval x g * y ∈ (F.twist (idealSys x (K ⊔ Ideal.span {g}))).secs :=
    fun y hy ↦ SectionCount.Drop.Filt.Step.mem_secs_iff'.mpr fun I ↦ hgK' I y (SectionCount.Drop.Filt.Step.mem_secs_iff'.mp hy I)

  have hlift : ∀ s ∈ (F.twist (idealSys x (K ⊔ Ideal.span {g}))).secs,
      ∃ t ∈ F'.secs, s - aeval x g * t ∈ (F.twist (idealSys x K)).secs := by
    intro s hs
    choose y hy hys using hE s hs
    have hcomp : ∀ (I₁ I₂ : Chart x), I₁.1 ⊆ I₂.1 →
        y I₁ - y I₂ ∈ (F'.twist (idealSys x pp)).sub I₂ := by
      intro I₁ I₂ h
      refine hU I₂ _ (sub_mem (F'.mono I₁ I₂ h _ (hy I₁)) (hy I₂)) ?_
      have h1 := sub_mem (hys I₂) ((F.twist (idealSys x K)).mono I₁ I₂ h _ (hys I₁))
      convert h1 using 1
      ring
    obtain ⟨t, ht, htI⟩ := hc₀ _ hce y hy hcomp
    refine ⟨t, ht, SectionCount.Drop.Filt.Step.mem_secs_iff'.mpr fun I ↦ ?_⟩
    have h1 := add_mem (hys I) (hC I _ (neg_mem (htI I)))
    convert h1 using 1
    ring

  set H := F.secs with hH
  set H' := F'.secs with hH'
  set A := ((F.twist (idealSys x K)).secs).comap H.subtype with hA
  set B := ((F.twist (idealSys x (K ⊔ Ideal.span {g}))).secs).comap H.subtype with hB
  set P := ((F'.twist (idealSys x pp)).secs).comap H'.subtype with hP
  have hAB : A ≤ B := fun z hz ↦ Submodule.mem_comap.mpr (hWV _ (Submodule.mem_comap.mp hz))
  let μ0 : H' →ₗ[S] H := (LinearMap.mulLeft S (aeval x g)).restrict (p := H') (q := H)
    (fun y hy ↦ hVH _ (hgsec y hy))
  let μ : H' →ₗ[S] H ⧸ A := A.mkQ ∘ₗ μ0
  have hμ : ∀ y : H', y ∈ P ↔ μ y = 0 := by
    intro y
    rw [LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
      Submodule.mem_comap, Submodule.mem_comap]
    change (y : Ω) ∈ _ ↔ aeval x g * (y : Ω) ∈ _
    constructor
    · intro h
      exact SectionCount.Drop.Filt.Step.mem_secs_iff'.mpr fun I ↦ hC I _ (SectionCount.Drop.Filt.Step.mem_secs_iff'.mp h I)
    · intro h
      exact SectionCount.Drop.Filt.Step.mem_secs_iff'.mpr fun I ↦ hU I _ (SectionCount.Drop.Filt.Step.mem_secs_iff'.mp y.2 I) (SectionCount.Drop.Filt.Step.mem_secs_iff'.mp h I)
  let μb : (H' ⧸ P) →ₗ[S] H ⧸ A := P.liftQ μ (fun y hy ↦ (hμ y).mp hy)
  have hinj : Function.Injective μb := by
    rw [← LinearMap.ker_eq_bot]
    exact Submodule.ker_liftQ_eq_bot _ _ _ (fun y hy ↦ (hμ y).mpr hy)
  let π : (H ⧸ A) →ₗ[S] H ⧸ B := Submodule.factor hAB
  have hsurj : Function.Surjective π := by
    intro z
    obtain ⟨m, rfl⟩ := Submodule.mkQ_surjective B z
    exact ⟨A.mkQ m, rfl⟩
  have hex : Function.Exact μb π := by
    intro z
    obtain ⟨m, rfl⟩ := Submodule.mkQ_surjective A z
    change B.mkQ m = 0 ↔ _
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]
    constructor
    · intro hm
      obtain ⟨t, ht, hst⟩ := hlift _ hm
      change (m : Ω) - aeval x g * t ∈ _ at hst
      refine ⟨P.mkQ ⟨t, ht⟩, ?_⟩
      change A.mkQ (μ0 ⟨t, ht⟩) = A.mkQ m
      rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq, Submodule.mem_comap]
      change aeval x g * t - (m : Ω) ∈ _
      have h1 := neg_mem hst
      convert h1 using 1
      ring
    · rintro ⟨w, hw⟩
      obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective P w
      change A.mkQ (μ0 y) = A.mkQ m at hw
      rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq, Submodule.mem_comap] at hw
      change aeval x g * (y : Ω) - m ∈ _ at hw
      change (m : Ω) ∈ _
      have h1 := sub_mem (hgsec _ y.2) (hWV _ hw)
      convert h1 using 1
      ring
  have hlen := Module.length_eq_add_of_exact μb π hinj hsurj hex

  have hfin : Module.length S (H ⧸ A) ≠ ⊤ := by
    by_cases hx : x = 0
    · have hE0 : IsEmpty (Chart x) := ⟨fun I ↦ by
        obtain ⟨i, hi⟩ := I.2.1
        exact (mem_support x).mp (I.2.2 hi) (by simp [hx])⟩
      have hAt : A = ⊤ := eq_top_iff.mpr fun m _ ↦
        Submodule.mem_comap.mpr (SectionCount.Drop.Filt.Step.mem_secs_iff'.mpr fun I ↦ isEmptyElim I)
      have : Subsingleton (H ⧸ A) := Submodule.Quotient.subsingleton_iff.mpr hAt
      rw [Module.length_eq_zero]
      exact ENat.zero_ne_top
    · have : Module.Finite S H := (hFS S Ω N x (Q.tensorProd (twistBundle S x (c : ℤ))) hx).1
      have := h𝔪
      refine length_ne_top_of_smul_eq_zero 𝔪 fun a ha z ↦ ?_
      obtain ⟨m, rfl⟩ := Submodule.mkQ_surjective A z
      rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]
      change a • (m : Ω) ∈ _
      refine SectionCount.Drop.Filt.Step.mem_secs_iff'.mpr fun I ↦ ?_
      rw [hsub, Algebra.smul_def]
      refine Submodule.mul_mem_mul ?_ (SectionCount.Drop.Filt.Step.mem_secs_iff'.mp m.2 I)
      exact Submodule.subset_span ⟨C a, 1, 0, h𝔪K (Ideal.mem_map_of_mem _ ha), one_mem _,
        isHomogeneous_C _ _, isHomogeneous_one _ _, by simp⟩
  have hB' : Module.length S (H ⧸ B) ≠ ⊤ := fun h ↦ hfin (by rw [hlen, h, add_top])
  have hP' : Module.length S (H' ⧸ P) ≠ ⊤ := fun h ↦ hfin (by rw [hlen, h, top_add])
  change ((Module.length S (H ⧸ A)).toNat : ℤ) =
    ((Module.length S (H ⧸ B)).toNat : ℤ) + ((Module.length S (H' ⧸ P)).toNat : ℤ)
  rw [hlen, ENat.toNat_add hP' hB']
  push_cast
  ring

end CycleSplit.Filt.Step

end

end GroundTheory.Heights₂.Heights.Kleiman
