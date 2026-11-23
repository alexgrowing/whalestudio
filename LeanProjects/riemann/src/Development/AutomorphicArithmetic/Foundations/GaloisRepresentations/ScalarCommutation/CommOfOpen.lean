import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ScalarCommutation.TypeSlice
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.HeckeActMem
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.HeckeConvolutionMemHolds

set_option autoImplicit false

noncomputable section

open Formalism.UG GlobalTheory.LKDef

namespace UpperTheory.Gal.Spc

section Abstract

variable {H₁ H₂ Γ V : Type} [Group H₁] [Group H₂] [Group Γ] [AddCommGroup V] [Module ℂ V]
  (ι : Γ →* H₁ × H₂) (K₁ : Subgroup H₁) (K₂ : Subgroup H₂) (ξ : Representation ℂ Γ V)

variable {K₁} in
private theorem hecke_right {f : H₁ → ℂ} (hf : f ∈ Hecke ℂ K₁) (h : H₁) (c : K₁) : f (h * c) = f h := by
  have := hf.1 1 c h
  simpa using this

variable {K₁} in
private theorem hecke_left {f : H₁ → ℂ} (hf : f ∈ Hecke ℂ K₁) (h : H₁) (c : K₁) : f (c * h) = f h := by
  have := hf.1 c 1 h
  simpa using this

variable {K₁} in
private theorem fin_act (hK : IsCommensurated K₁) {f : H₁ → ℂ} (hf : f ∈ Hecke ℂ K₁) (Φ : H₁ × H₂ → V) (g : H₁ × H₂) :
    (Function.support fun x : H₁ ⧸ K₁ => f x.out • Φ (g * (x.out, 1))).Finite :=
  (P.finite_supp K₁ hK f hf).subset fun x hx h0 => hx (by simp [h0])

variable {ι K₁ K₂ ξ} in
private theorem form_right {Φ : H₁ × H₂ → V} (hΦ : Φ ∈ HeckeTraceForms.forms ι (K₁.prod K₂) ξ) (g : H₁ × H₂) {k₁ : H₁} {k₂ : H₂}
    (h₁ : k₁ ∈ K₁) (h₂ : k₂ ∈ K₂) : Φ (g * (k₁, k₂)) = Φ g :=
  hΦ.2 _ (Subgroup.mem_prod.2 ⟨h₁, h₂⟩) g

variable {ι K₁ K₂ ξ} in
private theorem act_mem (hK : IsCommensurated K₁) {f : H₁ → ℂ} (hf : f ∈ Hecke ℂ K₁) {Φ : H₁ × H₂ → V}
    (hΦ : Φ ∈ HeckeTraceForms.forms ι (K₁.prod K₂) ξ) : hActK K₁ f Φ ∈ HeckeTraceForms.forms ι (K₁.prod K₂) ξ := by
  refine ⟨fun γ g => ?_, fun k hk g => ?_⟩
  · unfold hActK
    rw [map_finsum (ξ γ) (fin_act hK hf Φ g)]
    refine finsum_congr fun x => ?_
    rw [map_smul, mul_assoc, hΦ.1]
  · obtain ⟨h₁, h₂⟩ := Subgroup.mem_prod.1 hk
    unfold hActK
    have key := P.finsum_out_mul K₁ k.1 (fun h => f h • Φ (g * (h, 1))) (fun h c => by
      have e : g * (h * (c : H₁), (1 : H₂)) = g * (h, 1) * ((c : H₁), (1 : H₂)) := by
        simp [mul_assoc]
      show f (h * c) • Φ (g * (h * (c : H₁), (1 : H₂))) = f h • Φ (g * (h, 1))
      rw [hecke_right hf, e, form_right hΦ _ c.2 (one_mem _)])
    refine Eq.trans ?_ key
    refine finsum_congr fun x => ?_
    have e : g * k * (x.out, (1 : H₂)) = g * (k.1 * x.out, 1) * ((1 : H₁), k.2) := by
      ext <;> simp [mul_assoc]
    show _ = f (k.1 * x.out) • Φ (g * (k.1 * x.out, 1))
    rw [e, form_right hΦ _ (one_mem _) h₂, hecke_left hf x.out ⟨k.1, h₁⟩]

private def act (hK : IsCommensurated K₁) {f : H₁ → ℂ} (hf : f ∈ Hecke ℂ K₁) :
    Module.End ℂ (HeckeTraceForms.forms ι (K₁.prod K₂) ξ) where
  toFun Φ := ⟨hActK K₁ f Φ, act_mem hK hf Φ.2⟩
  map_add' a b := by
    apply Subtype.ext
    funext g
    show (∑ᶠ x : H₁ ⧸ K₁, f x.out • ((a : H₁ × H₂ → V) (g * (x.out, 1)) + (b : H₁ × H₂ → V) (g * (x.out, 1)))) =
      (∑ᶠ x : H₁ ⧸ K₁, f x.out • (a : H₁ × H₂ → V) (g * (x.out, 1))) +
        ∑ᶠ x : H₁ ⧸ K₁, f x.out • (b : H₁ × H₂ → V) (g * (x.out, 1))
    simp only [smul_add]
    exact finsum_add_distrib (fin_act hK hf _ g) (fin_act hK hf _ g)
  map_smul' c a := by
    apply Subtype.ext
    funext g
    show (∑ᶠ x : H₁ ⧸ K₁, f x.out • (c • (a : H₁ × H₂ → V) (g * (x.out, 1)))) =
      c • ∑ᶠ x : H₁ ⧸ K₁, f x.out • (a : H₁ × H₂ → V) (g * (x.out, 1))
    rw [smul_finsum' c (show Function.HasFiniteSupport
      (fun x : H₁ ⧸ K₁ => f x.out • (a : H₁ × H₂ → V) (g * (x.out, 1))) from fin_act hK hf _ g)]
    exact finsum_congr fun x => smul_comm _ _ _

variable {K₁} in
private theorem act_mul (hK : IsCommensurated K₁) {f₁ f₂ : H₁ → ℂ} (h₁ : f₁ ∈ Hecke ℂ K₁) (h₂ : f₂ ∈ Hecke ℂ K₁)
    {Φ : H₁ × H₂ → V} (hΦ : ∀ (k : H₁), k ∈ K₁ → ∀ g, Φ (g * (k, 1)) = Φ g) :
    hActK K₁ (conv K₁ f₁ f₂) Φ = hActK K₁ f₁ (hActK K₁ f₂ Φ) := by
  funext g
  let φ : H₁ → V := fun x => Φ (g * (x, 1))
  have hφ : φ ∈ AMF ℂ (⊥ : Subgroup H₁) K₁ (1 : Representation ℂ (⊥ : Subgroup H₁) V) := by
    rintro ⟨γ, hγ⟩ x ⟨κ, hκ⟩
    obtain rfl : γ = 1 := Subgroup.mem_bot.1 hγ
    have e : g * ((1 : H₁) * x * κ, (1 : H₂)) = g * (x, 1) * (κ, 1) := by simp [mul_assoc]
    show Φ (g * ((1 : H₁) * x * κ, (1 : H₂))) = Φ (g * (x, 1))
    rw [e, hΦ κ hκ]
  have key := congrFun (P.hecke_act_mul H₁ ⊥ K₁ ℂ V 1 hK f₁ h₁ f₂ h₂ φ hφ) 1
  have e1 : ∀ (f : H₁ → ℂ) (a : H₁), hAct K₁ f φ a = hActK K₁ f Φ (g * (a, 1)) := by
    intro f a
    unfold hAct hActK
    refine finsum_congr fun x => ?_
    have e : g * (a * x.out, (1 : H₂)) = g * (a, 1) * (x.out, 1) := by simp [mul_assoc]
    show f x.out • Φ (g * (a * x.out, (1 : H₂))) = _
    rw [e]
  have l : hActK K₁ (conv K₁ f₁ f₂) Φ g = hAct K₁ (conv K₁ f₁ f₂) φ 1 := by
    rw [e1]
    exact congrArg _ (mul_one g).symm
  have r : hActK K₁ f₁ (hActK K₁ f₂ Φ) g = hAct K₁ f₁ (hAct K₁ f₂ φ) 1 := by
    show (∑ᶠ x : H₁ ⧸ K₁, f₁ x.out • hActK K₁ f₂ Φ (g * (x.out, 1))) =
      ∑ᶠ x : H₁ ⧸ K₁, f₁ x.out • hAct K₁ f₂ φ (1 * x.out)
    refine finsum_congr fun x => ?_
    rw [e1, one_mul]
  rw [l, r, key]

variable {ι K₁ K₂ ξ} in
private theorem act_isHecke (hK : IsCommensurated K₁) {f : H₁ → ℂ} (hf : f ∈ Hecke ℂ K₁) :
    HeckeTraceForms.IsHecke ι (K₁.prod K₂) ξ (fun h => f h.1 * Set.indicator (K₂ : Set H₂) (1 : H₂ → ℂ) h.2)
      (act ι K₁ K₂ ξ hK hf) := by
  intro φ g
  let e : H₁ ⧸ K₁ → (H₁ × H₂) ⧸ (K₁.prod K₂) := fun q => QuotientGroup.mk (q.out, 1)
  have he : Function.Injective e := by
    intro a b hab
    have h := QuotientGroup.eq.1 hab
    have h1 := (Subgroup.mem_prod.1 h).1
    rw [← QuotientGroup.out_eq' a, ← QuotientGroup.out_eq' b]
    exact QuotientGroup.eq.2 (by simpa using h1)
  set A : (H₁ × H₂) ⧸ (K₁.prod K₂) → V := fun h =>
    (f h.out.1 * Set.indicator (K₂ : Set H₂) (1 : H₂ → ℂ) h.out.2) • (φ : H₁ × H₂ → V) (g * h.out) with hA
  have hsupp : ∀ h, A h ≠ 0 → h ∈ Set.range e := by
    intro h hh
    have h2 : h.out.2 ∈ K₂ := by
      by_contra hn
      exact hh (by simp [hA, Set.indicator_of_notMem (show h.out.2 ∉ (K₂ : Set H₂) from hn)])
    refine ⟨QuotientGroup.mk h.out.1, ?_⟩
    obtain ⟨c, hc⟩ := QuotientGroup.mk_out_eq_mul K₁ h.out.1
    show QuotientGroup.mk ((QuotientGroup.mk h.out.1 : H₁ ⧸ K₁).out, (1 : H₂)) = h
    rw [hc, ← QuotientGroup.out_eq' h]
    refine QuotientGroup.eq.2 (Subgroup.mem_prod.2 ?_)
    simp only [QuotientGroup.out_eq']
    refine ⟨?_, ?_⟩
    · simpa using K₁.inv_mem c.2
    · simpa using h2
  have hval : ∀ q, A (e q) = f q.out • (φ : H₁ × H₂ → V) (g * (q.out, 1)) := by
    intro q
    obtain ⟨c, hc⟩ := QuotientGroup.mk_out_eq_mul (K₁.prod K₂) ((q.out, 1) : H₁ × H₂)
    obtain ⟨c₁, c₂⟩ := Subgroup.mem_prod.1 c.2
    have ho : (e q).out = (q.out, 1) * (c : H₁ × H₂) := hc
    simp only [hA]
    rw [ho]
    have e2 : g * (((q.out, 1) : H₁ × H₂) * (c : H₁ × H₂)) = g * (q.out, 1) * ((c : H₁ × H₂).1, (c : H₁ × H₂).2) := by
      rw [mul_assoc]
    rw [e2, form_right φ.2 _ c₁ c₂]
    congr 1
    have i2 : ((((q.out, 1) : H₁ × H₂) * (c : H₁ × H₂)).2) ∈ (K₂ : Set H₂) := by simpa using c₂
    rw [Set.indicator_of_mem i2]
    have := hecke_right hf q.out ⟨_, c₁⟩
    simpa using this
  have hsum : (∑ᶠ h, A h) = ∑ᶠ q, A (e q) := by
    rw [← finsum_mem_range he, finsum_mem_def]
    refine finsum_congr fun h => ?_
    by_cases hr : h ∈ Set.range e
    · rw [Set.indicator_of_mem hr]
    · rw [Set.indicator_of_notMem hr]
      by_contra hne
      exact hr (hsupp h hne)
  show hActK K₁ f φ g = ∑ᶠ h, A h
  rw [hsum]
  exact finsum_congr fun q => (hval q).symm

private theorem abs_main (hK : IsCommensurated K₁) :
    ∃ T : (H₁ → ℂ) → Module.End ℂ (HeckeTraceForms.forms ι (K₁.prod K₂) ξ), T 0 = 0 ∧
      ∀ f ∈ Hecke ℂ K₁, (∀ Φ, (T f Φ : H₁ × H₂ → V) = hActK K₁ f Φ) ∧
        HeckeTraceForms.heckeTrace ι (K₁.prod K₂) ξ (fun h => f h.1 * Set.indicator (K₂ : Set H₂) (1 : H₂ → ℂ) h.2) =
          LinearMap.trace ℂ _ (T f) ∧
        ∀ f' ∈ Hecke ℂ K₁, T (conv K₁ f f') = T f * T f' ∧ ∀ c : ℂ, T (c • f + f') = c • T f + T f' := by
  classical
  let T : (H₁ → ℂ) → Module.End ℂ (HeckeTraceForms.forms ι (K₁.prod K₂) ξ) := fun f =>
    if h : f ∈ Hecke ℂ K₁ then act ι K₁ K₂ ξ hK h else 0
  have hT : ∀ f (h : f ∈ Hecke ℂ K₁), T f = act ι K₁ K₂ ξ hK h := fun f h => dif_pos h
  have hTa : ∀ f (h : f ∈ Hecke ℂ K₁) Φ, (T f Φ : H₁ × H₂ → V) = hActK K₁ f Φ := fun f h Φ => by rw [hT f h]; rfl
  refine ⟨T, ?_, fun f hf => ⟨hTa f hf, ?_, fun f' hf' => ⟨?_, fun c => ?_⟩⟩⟩
  · apply LinearMap.ext
    intro Φ
    apply Subtype.ext
    rw [hTa 0 (Submodule.zero_mem _)]
    funext g
    simp [hActK]
  · have hI := act_isHecke (ι := ι) (K₂ := K₂) (ξ := ξ) hK hf
    have hex : ∃ T', HeckeTraceForms.IsHecke ι (K₁.prod K₂) ξ
        (fun h => f h.1 * Set.indicator (K₂ : Set H₂) (1 : H₂ → ℂ) h.2) T' := ⟨_, hI⟩
    rw [HeckeTraceForms.heckeTrace, dif_pos hex, hT f hf]
    congr 1
    apply LinearMap.ext
    intro Φ
    apply Subtype.ext
    funext g
    rw [hex.choose_spec Φ g, hI Φ g]
  · apply LinearMap.ext
    intro Φ
    apply Subtype.ext
    have hc := P.hecke_convolution_mem_holds H₁ K₁ ℂ hK f hf f' hf'
    rw [hTa _ hc, Module.End.mul_apply, hTa f hf, hTa f' hf']
    exact act_mul hK hf hf' fun k hk g => form_right Φ.2 g hk (one_mem _)
  · apply LinearMap.ext
    intro Φ
    apply Subtype.ext
    have hc : c • f + f' ∈ Hecke ℂ K₁ := Submodule.add_mem _ (Submodule.smul_mem _ c hf) hf'
    rw [hTa _ hc]
    show _ = c • (T f Φ : H₁ × H₂ → V) + (T f' Φ : H₁ × H₂ → V)
    rw [hTa f hf, hTa f' hf']
    funext g
    show (∑ᶠ x : H₁ ⧸ K₁, (c • f + f') x.out • (Φ : H₁ × H₂ → V) (g * (x.out, 1))) =
      c • (∑ᶠ x : H₁ ⧸ K₁, f x.out • (Φ : H₁ × H₂ → V) (g * (x.out, 1))) +
        ∑ᶠ x : H₁ ⧸ K₁, f' x.out • (Φ : H₁ × H₂ → V) (g * (x.out, 1))
    have hA : Function.HasFiniteSupport
        (fun x : H₁ ⧸ K₁ => f x.out • (Φ : H₁ × H₂ → V) (g * (x.out, 1))) := fin_act hK hf _ g
    have hB : Function.HasFiniteSupport
        (fun x : H₁ ⧸ K₁ => f' x.out • (Φ : H₁ × H₂ → V) (g * (x.out, 1))) := fin_act hK hf' _ g
    have hC : Function.HasFiniteSupport
        (fun x : H₁ ⧸ K₁ => c • f x.out • (Φ : H₁ × H₂ → V) (g * (x.out, 1))) :=
      Set.Finite.subset hA fun x hx h0 => hx (by
        show c • f x.out • (Φ : H₁ × H₂ → V) (g * (x.out, 1)) = 0
        rw [show f x.out • (Φ : H₁ × H₂ → V) (g * (x.out, 1)) = 0 from h0, smul_zero])
    rw [smul_finsum' c hA, ← finsum_add_distrib hC hB]
    refine finsum_congr fun x => ?_
    simp [add_smul, mul_smul]

end Abstract

private theorem comm_of_open {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] (K : Subgroup H)
    (ho : IsOpen (K : Set H)) (hc : IsCompact (K : Set H)) : IsCommensurated K := by
  intro g
  have : CompactSpace K := isCompact_iff_compactSpace.1 hc
  have h1 : IsOpen ((K.map (MulAut.conj g).toMonoidHom : Subgroup H) : Set H) := by
    rw [Subgroup.coe_map]
    exact ((Homeomorph.mulLeft g).trans (Homeomorph.mulRight g⁻¹)).isOpenMap _ ho
  have h2 : IsOpen (((K.map (MulAut.conj g).toMonoidHom).subgroupOf K : Subgroup K) : Set K) :=
    h1.preimage continuous_subtype_val
  have := Subgroup.quotient_finite_of_isOpen _ h2
  exact Subgroup.index_ne_zero_iff_finite.2 this

end UpperTheory.Gal.Spc

theorem UpperTheory.Gal.Spc.opAlg :
    UpperTheory.Gal.Spc.OpAlg := by
  intro p _ G Lv V _ _ ξ B
  exact UpperTheory.Gal.Spc.abs_main B.emb Lv.K.toSubgroup (UpperTheory.Gal.LocalSmoothExtension.Kp G) (ξ.comp (GlobalTheory.LKCx.grp G B.β).subtype)
    (UpperTheory.Gal.Spc.comm_of_open _ Lv.K.isOpen Lv.compact)
