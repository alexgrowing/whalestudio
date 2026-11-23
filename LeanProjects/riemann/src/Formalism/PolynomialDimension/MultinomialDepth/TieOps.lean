import Formalism.PolynomialDimension.MultinomialDepth.PartnerM
import Formalism.MahlerMeasure.MahlerMeasureProofs.WeightSpaceDimensionMonotone
import Formalism.MahlerMeasure.MahlerMeasureProofs.GamInt
import Formalism.MahlerMeasure.MahlerMeasureProofs.LieMat

namespace Formalism.CountingSumsFrames.TO

open Formalism.GM.DimensionMonotonicity Finset

namespace GlX

variable {K V : Type} [Field K] [CharZero K] [AddCommGroup V] [Module K V] {r : ℕ} (G : GlW K V r)

theorem cas_hw {μ : Fin r → ℤ} {x : V} (h : G.IsHW μ x) : G.Cas x = ((GlW.casI μ : ℤ) : K) • x := by
  have h' := h
  unfold Formalism.GM.DimensionMonotonicity.GlW.IsHW Formalism.GM.DimensionMonotonicity.GlW.IsWt at h'
  obtain ⟨hw, hr⟩ := h'
  have hd : ∀ c, G.E c c x = ((μ c : ℤ) : K) • x := fun c => by
    have := G.diag c μ x
    rwa [hw] at this
  have hterm : ∀ a b, G.E a b (G.E b a x) =
      (((if a = b then μ a * μ a else if a < b then μ a - μ b else 0 : ℤ)) : K) • x := by
    intro a b
    split_ifs with hab hlt
    · subst hab
      rw [hd, map_smul, hd, smul_smul, Int.cast_mul]
    · have hc := G.comm a b b a x
      simp only [if_true, eq_self_iff_true] at hc
      rw [hr a b hlt, map_zero, sub_zero] at hc
      rw [hc, hd, hd, ← sub_smul, Int.cast_sub]
    · have hba : b < a := lt_of_le_of_ne (not_lt.mp hlt) (Ne.symm hab)
      rw [hr b a hba, map_zero, Int.cast_zero, zero_smul]
  have hC : G.Cas x = ∑ a, ∑ b, G.E a b (G.E b a x) := by
    simp only [Formalism.GM.DimensionMonotonicity.GlW.Cas, LinearMap.sum_apply, LinearMap.comp_apply]
  rw [hC]
  simp only [hterm, Formalism.GM.DimensionMonotonicity.GlW.casI, Int.cast_sum, Finset.sum_smul]

private theorem cprod_eig_lemma {x : V} {e : ℤ} (hx : G.Cas x = ((e : ℤ) : K) • x) (cs : List ℤ) :
    G.cprod cs x = (cs.map (fun c => (((e - c : ℤ)) : K))).prod • x := by
  induction cs with
  | nil => simp [Formalism.GM.DimensionMonotonicity.GlW.cprod]
  | cons c cs ih =>
    simp only [Formalism.GM.DimensionMonotonicity.GlW.cprod, LinearMap.comp_apply, ih, List.map_cons, List.prod_cons]
    rw [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, map_smul, hx, smul_comm _ (((e : ℤ) : K)),
      ← sub_smul, smul_smul, Int.cast_sub]

theorem cprod_kill {x : V} {e : ℤ} (hx : G.Cas x = ((e : ℤ) : K) • x) (cs : List ℤ) (he : e ∈ cs) :
    G.cprod cs x = 0 := by
  rw [cprod_eig_lemma G hx cs]
  have h0 : (cs.map (fun c => (((e - c : ℤ)) : K))).prod = 0 :=
    List.prod_eq_zero (List.mem_map.mpr ⟨e, he, by simp⟩)
  rw [h0, zero_smul]

noncomputable def qlist (S : Finset (Fin r → ℤ)) (c : ℤ) : List ℤ := ((S.image GlW.casI).erase c).toList

theorem qlist_ne (S : Finset (Fin r → ℤ)) (c : ℤ) : ∀ x ∈ qlist S c, x ≠ c := by
  intro x hx
  unfold qlist at hx
  rw [Finset.mem_toList] at hx
  exact Finset.ne_of_mem_erase hx

theorem mem_qlist {S : Finset (Fin r → ℤ)} {c : ℤ} {ν : Fin r → ℤ} (hν : ν ∈ S) (hne : GlW.casI ν ≠ c) :
    GlW.casI ν ∈ qlist S c := by
  unfold qlist
  rw [Finset.mem_toList]
  exact Finset.mem_erase.mpr ⟨hne, Finset.mem_image_of_mem _ hν⟩

private theorem cas_wt_lemma_2 {U : Submodule K V} (hU : G.Stable U) {μ : Fin r → ℤ} {v : V} (hv : G.IsWt μ v)
    (hr : ∀ a b, a < b → G.E a b v ∈ U) : G.Cas v - ((GlW.casI μ : ℤ) : K) • v ∈ U := by
  have hw := hv
  unfold Formalism.GM.DimensionMonotonicity.GlW.IsWt at hw
  have hd : ∀ c, G.E c c v = ((μ c : ℤ) : K) • v := fun c => by
    have := G.diag c μ v
    rwa [hw] at this
  have hterm : ∀ a b, G.E a b (G.E b a v) -
      (((if a = b then μ a * μ a else if a < b then μ a - μ b else 0 : ℤ)) : K) • v ∈ U := by
    intro a b
    split_ifs with hab hlt
    · subst hab
      rw [hd, map_smul, hd, smul_smul, Int.cast_mul, sub_self]
      exact zero_mem _
    · have hc := G.comm a b b a v
      simp only [if_true, eq_self_iff_true] at hc
      have e : G.E a b (G.E b a v) - (((μ a - μ b : ℤ)) : K) • v = G.E b a (G.E a b v) := by
        rw [Int.cast_sub, sub_smul, ← hd a, ← hd b, ← hc]
        abel
      rw [e]
      exact hU b a _ (hr a b hlt)
    · have hba : b < a := lt_of_le_of_ne (not_lt.mp hlt) (Ne.symm hab)
      rw [Int.cast_zero, zero_smul, sub_zero]
      exact hU a b _ (hr b a hba)
  have e2 : G.Cas v - ((GlW.casI μ : ℤ) : K) • v = ∑ a, ∑ b, (G.E a b (G.E b a v) -
      (((if a = b then μ a * μ a else if a < b then μ a - μ b else 0 : ℤ)) : K) • v) := by
    simp only [Formalism.GM.DimensionMonotonicity.GlW.Cas, Formalism.GM.DimensionMonotonicity.GlW.casI, LinearMap.sum_apply, LinearMap.comp_apply,
      Int.cast_sum, Finset.sum_smul, Finset.sum_sub_distrib]
  rw [e2]
  exact sum_mem fun a _ => sum_mem fun b _ => hterm a b

theorem cprod_mod {U : Submodule K V} (hU : G.Stable U) {μ : Fin r → ℤ} {v : V} (hv : G.IsWt μ v)
    (hr : ∀ a b, a < b → G.E a b v ∈ U) (cs : List ℤ) :
    G.cprod cs v - (cs.map (fun c => (((GlW.casI μ - c : ℤ)) : K))).prod • v ∈ U := by
  have hcas : ∀ y ∈ U, G.Cas y ∈ U := fun y hy => by
    simp only [Formalism.GM.DimensionMonotonicity.GlW.Cas, LinearMap.sum_apply, LinearMap.comp_apply]
    exact sum_mem fun a _ => sum_mem fun b _ => hU a b _ (hU b a y hy)
  induction cs with
  | nil => simp [Formalism.GM.DimensionMonotonicity.GlW.cprod]
  | cons c cs ih =>
    have key : G.cprod (c :: cs) v - ((c :: cs).map (fun c => (((GlW.casI μ - c : ℤ)) : K))).prod • v =
        (cs.map (fun c => (((GlW.casI μ - c : ℤ)) : K))).prod • (G.Cas v - ((GlW.casI μ : ℤ) : K) • v) +
        (G.Cas (G.cprod cs v - (cs.map (fun c => (((GlW.casI μ - c : ℤ)) : K))).prod • v) -
          ((c : ℤ) : K) • (G.cprod cs v - (cs.map (fun c => (((GlW.casI μ - c : ℤ)) : K))).prod • v)) := by
      simp only [Formalism.GM.DimensionMonotonicity.GlW.cprod, LinearMap.comp_apply, List.map_cons, List.prod_cons,
        LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, map_sub, map_smul, Int.cast_sub]
      module
    rw [key]
    exact add_mem (U.smul_mem _ (cas_wt_lemma_2 G hU hv hr)) (sub_mem (hcas _ ih) (U.smul_mem _ ih))

theorem iSup_stable {ι : Sort*} {U : ι → Submodule K V} (hU : ∀ i, G.Stable (U i)) : G.Stable (⨆ i, U i) := by
  unfold Formalism.GM.DimensionMonotonicity.GlW.Stable at *
  intro a b x hx
  refine Submodule.iSup_induction U (motive := fun x => G.E a b x ∈ ⨆ i, U i) hx ?_ ?_ ?_
  · intro i y hy
    exact Submodule.mem_iSup_of_mem i (hU i a b y hy)
  · simp
  · intro y z hy hz
    rw [map_add]
    exact add_mem hy hz

theorem inf_stable {U U' : Submodule K V} (hU : G.Stable U) (hU' : G.Stable U') : G.Stable (U ⊓ U') := by
  unfold Formalism.GM.DimensionMonotonicity.GlW.Stable at *
  intro a b x hx
  rw [Submodule.mem_inf] at hx ⊢
  exact ⟨hU a b x hx.1, hU' a b x hx.2⟩

theorem gen_kill {W : Submodule K V} (hW : G.Stable W) {S : Finset (Fin r → ℤ)}
    (hS : ∀ x ∈ W, ∀ μ ∉ S, G.comp μ x = 0) {la : Fin r → ℤ} {v : V} (hv : G.IsHW la v) (hvW : v ∈ W)
    (hv0 : v ≠ 0) {μ ν : Fin r → ℤ} (hμ : DomW μ) (hle : Dle μ ν) (hne : Dle ν la → la ≠ μ) :
    ∀ x ∈ G.gS {v}, G.cprod (qlist S (GlW.casI μ)) (G.comp ν x) = 0 := by
  intro x hx
  have hy : G.comp ν x ∈ G.gS {v} := G.graded_of (G.gS_stable _) ν x hx
  by_cases h0 : G.comp ν x = 0
  · rw [h0, map_zero]
  have hνla : Dle ν la := G.wt_le_of_mem hv hx h0
  have hla : DomW la := G.dom_of_hwmod G.bot_stable hW ⟨S, hS⟩ hvW (by rwa [Submodule.mem_bot])
      hv.1 (fun a b h => by rw [hv.2 a b h]; exact Submodule.zero_mem _)
  have hlt := cas_lt hμ hla (Dle_trans hle hνla) (hne hνla).symm
  have hlaS : la ∈ S := by
    by_contra hn
    exact hv0 (by have := hS v hvW la hn; rwa [hv.1] at this)
  exact cprod_kill G (G.Cas_gS hv hy) _ (mem_qlist hlaS hlt.ne')

end GlX

end Formalism.CountingSumsFrames.TO

namespace Formalism.CountingSumsFrames.TO

open Formalism.GM.DimensionMonotonicity Finset

namespace GlX

variable {K V : Type} [Field K] [CharZero K] [AddCommGroup V] [Module K V] {r : ℕ} (G : GlW K V r)

theorem span_hw {W : Submodule K V} (hW : G.Stable W) {S : Finset (Fin r → ℤ)}
    (hS : ∀ x ∈ W, ∀ μ ∉ S, G.comp μ x = 0) {ι : Type*} (h : ι → V) (la : ι → Fin r → ℤ)
    (hh : ∀ i, G.IsHW (la i) (h i)) (hhW : ∀ i, h i ∈ W) (hh0 : ∀ i, h i ≠ 0)
    (hsp : ∀ μ v, v ∈ W → G.IsHW μ v → v ∈ Submodule.span K (Set.range h)) :
    W ≤ ⨆ i, G.gS {h i} := by
  classical
  have hUs : G.Stable (⨆ i, G.gS {h i}) := iSup_stable G (fun i => G.gS_stable _)
  by_contra hn
  obtain ⟨v, hvW, hvU, μ, hvw, hr⟩ := G.exists_hwmod (G.graded_of hW) (G.raising_of hW) ⟨S, hS⟩ hn
  have hμ : DomW μ := G.dom_of_hwmod hUs hW ⟨S, hS⟩ hvW hvU hvw hr
  have hs : (((qlist S (GlW.casI μ)).map (fun c => (((GlW.casI μ - c : ℤ)) : K))).prod) ≠ 0 :=
    cprod_ne (V := V) (GlW.casI μ) _ (qlist_ne S _)
  have hmod := cprod_mod G hUs hvw hr (qlist S (GlW.casI μ))
  have hv'U : ((((qlist S (GlW.casI μ)).map (fun c => (((GlW.casI μ - c : ℤ)) : K))).prod)⁻¹ •
      G.cprod (qlist S (GlW.casI μ)) v) - v ∈ ⨆ i, G.gS {h i} := by
    have := Submodule.smul_mem _ ((((qlist S (GlW.casI μ)).map (fun c => (((GlW.casI μ - c : ℤ)) : K))).prod)⁻¹) hmod
    rwa [smul_sub, smul_smul, inv_mul_cancel₀ hs, one_smul] at this
  have hkill : ∀ a b, a < b → ∀ y ∈ ⨆ i, G.gS {h i},
      G.cprod (qlist S (GlW.casI μ)) (G.comp (μ + dl a b) y) = 0 := by
    intro a b hab y hy
    refine Submodule.iSup_induction _ (motive := fun y => G.cprod (qlist S (GlW.casI μ)) (G.comp (μ + dl a b) y) = 0) hy
      (fun i x hx => gen_kill G hW hS (hh i) (hhW i) (hh0 i) hμ (Dle_raise μ hab) ?_ x hx) (by simp) ?_
    · intro hle hlaμ
      rw [hlaμ] at hle
      have := Dle_antisymm hle (Dle_raise μ hab)
      exact dl_ne_zero (ne_of_lt hab) (by simpa using this)
    · intro x y hx hy; rw [map_add, map_add, hx, hy, add_zero]
  apply hvU
  have hv'hw : G.IsHW μ ((((qlist S (GlW.casI μ)).map (fun c => (((GlW.casI μ - c : ℤ)) : K))).prod)⁻¹ •
      G.cprod (qlist S (GlW.casI μ)) v) := by
    refine ⟨?_, fun a b hab => ?_⟩
    · show G.comp μ _ = _
      rw [map_smul, G.comp_cprod, hvw]
    · rw [map_smul, G.E_cprod]
      have hw := G.isWt_E hvw a b
      have := hkill a b hab _ (hr a b hab)
      rw [hw] at this
      rw [this, smul_zero]
  have hin := hsp μ _ (W.smul_mem _ (G.cprod_mem hW _ hvW)) hv'hw
  have hin' : _ ∈ ⨆ i, G.gS {h i} := Submodule.span_le.mpr (by
    rintro _ ⟨i, rfl⟩; exact Submodule.mem_iSup_of_mem i (G.subset_gS _ (Set.mem_singleton _))) hin
  have hfin := Submodule.sub_mem _ hin' hv'U
  rwa [sub_sub_cancel] at hfin

theorem indep_hw {W : Submodule K V} (hW : G.Stable W) {S : Finset (Fin r → ℤ)}
    (hS : ∀ x ∈ W, ∀ μ ∉ S, G.comp μ x = 0) {ι : Type*} (h : ι → V) (la : ι → Fin r → ℤ)
    (hh : ∀ i, G.IsHW (la i) (h i)) (hhW : ∀ i, h i ∈ W) (hli : LinearIndependent K h) :
    iSupIndep (fun i => G.gS {h i}) := by
  classical
  have hh0 : ∀ i, h i ≠ 0 := fun i => hli.ne_zero i
  intro i
  rw [Submodule.disjoint_def]
  intro x0 hx01 hx02
  by_contra hx00
  have hKs : G.Stable (G.gS {h i} ⊓ ⨆ (j) (_ : j ≠ i), G.gS {h j}) :=
    inf_stable G (G.gS_stable _) (iSup_stable G fun j => iSup_stable G fun _ => G.gS_stable _)
  have hgW : G.gS {h i} ≤ W := G.gS_le (by simpa using hhW i) hW
  have hn' : ¬ (G.gS {h i} ⊓ ⨆ (j) (_ : j ≠ i), G.gS {h j}) ≤ ⊥ := fun h' =>
    hx00 ((Submodule.mem_bot K).mp (h' ⟨hx01, hx02⟩))
  obtain ⟨y, hyK, hy0, ν, hyw, hyr⟩ := G.exists_hwmod (G.graded_of hKs) (G.raising_of hKs)
    ⟨S, fun x hx => hS x (hgW hx.1)⟩ hn'
  have hyhw : G.IsHW ν y := ⟨hyw, fun a b hab => (Submodule.mem_bot K).mp (hyr a b hab)⟩
  have hy0' : y ≠ 0 := fun h' => hy0 (by rw [h']; exact Submodule.zero_mem _)
  obtain ⟨-, c, hyc⟩ := G.hw_in_gS (hh i) hW ⟨S, hS⟩ (hhW i) hyK.1 hyhw hy0'
  have hc0 : c ≠ 0 := by rintro rfl; exact hy0' (by rw [hyc, zero_smul])
  have hiK : h i ∈ ⨆ (j) (_ : j ≠ i), G.gS {h j} := by
    have := Submodule.smul_mem _ c⁻¹ hyK.2
    rwa [hyc, smul_smul, inv_mul_cancel₀ hc0, one_smul] at this
  have hμ : DomW (la i) := G.dom_of_hwmod G.bot_stable hW ⟨S, hS⟩ (hhW i) (by rw [Submodule.mem_bot]; exact hh0 i)
    (hh i).1 (fun a b hab => by rw [(hh i).2 a b hab]; exact Submodule.zero_mem _)
  have hs : (((qlist S (GlW.casI (la i))).map (fun c => (((GlW.casI (la i) - c : ℤ)) : K))).prod) ≠ 0 :=
    cprod_ne (V := V) (GlW.casI (la i)) _ (qlist_ne S _)
  have hQ : ∀ x ∈ ⨆ (j) (_ : j ≠ i), G.gS {h j},
      G.cprod (qlist S (GlW.casI (la i))) (G.comp (la i) x) ∈ Submodule.span K (h '' {j | j ≠ i}) := by
    intro x hx
    refine Submodule.iSup_induction _ (motive := fun x =>
      G.cprod (qlist S (GlW.casI (la i))) (G.comp (la i) x) ∈ Submodule.span K (h '' {j | j ≠ i})) hx
      (fun j x hx => ?_) (by simp) (fun x y hx hy => by rw [map_add, map_add]; exact Submodule.add_mem _ hx hy)
    refine Submodule.iSup_induction _ (motive := fun x =>
      G.cprod (qlist S (GlW.casI (la i))) (G.comp (la i) x) ∈ Submodule.span K (h '' {j | j ≠ i})) hx
      (fun hj x hx => ?_) (by simp) (fun x y hx hy => by rw [map_add, map_add]; exact Submodule.add_mem _ hx hy)
    by_cases hlj : la j = la i
    · obtain ⟨c', hc'⟩ := G.comp_top_of_mem (hh j) hx
      have e : G.comp (la i) x = c' • h j := by rw [← hlj]; exact hc'
      rw [e, map_smul, cprod_eig G (cas_hw G (hh j)) _, smul_smul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, hj, rfl⟩)
    · rw [gen_kill G hW hS (hh j) (hhW j) (hh0 j) hμ (Dle_refl _) (fun _ => hlj) x hx]
      exact Submodule.zero_mem _
  have h1 := hQ _ hiK
  rw [(hh i).1, cprod_eig G (cas_hw G (hh i)) _] at h1
  have h2 := Submodule.smul_mem _ ((((qlist S (GlW.casI (la i))).map (fun c => (((GlW.casI (la i) - c : ℤ)) : K))).prod)⁻¹) h1
  rw [smul_smul, inv_mul_cancel₀ hs, one_smul] at h2
  exact hli.notMem_span_image (s := {j | j ≠ i}) (x := i) (by simp) h2

end GlX

end Formalism.CountingSumsFrames.TO

namespace Formalism.CountingSumsFrames.TO

open Formalism.GM.DimensionMonotonicity Finset

namespace GlX

variable {K V : Type} [Field K] [CharZero K] [AddCommGroup V] [Module K V] {r : ℕ} (G : GlW K V r)

def act : List (Fin r × Fin r) → V →ₗ[K] V
  | [] => LinearMap.id
  | ab :: w => G.E ab.1 ab.2 ∘ₗ act w

noncomputable def Lv (v : V) : (List (Fin r × Fin r) →₀ K) →ₗ[K] V :=
  Finsupp.linearCombination K (fun w => act G w v)

theorem act_mem {U : Submodule K V} (hU : G.Stable U) (w : List (Fin r × Fin r)) {x : V} (hx : x ∈ U) :
    act G w x ∈ U := by
  induction w with
  | nil => simpa [act] using hx
  | cons ab w ih =>
    simp only [act, LinearMap.comp_apply]
    exact hU _ _ _ ih

theorem E_Lv (v : V) (a b : Fin r) (c : List (Fin r × Fin r) →₀ K) :
    G.E a b (Lv G v c) = Lv G v (Finsupp.mapDomain (List.cons (a, b)) c) := by
  unfold Lv
  rw [Finsupp.linearCombination_mapDomain]
  simp only [Finsupp.linearCombination_apply, Finsupp.sum, map_sum, map_smul,
    Function.comp_apply, act, LinearMap.comp_apply]

theorem range_Lv (v : V) : LinearMap.range (Lv G v) = G.gS {v} := by
  apply le_antisymm
  · intro y hy
    obtain ⟨c, rfl⟩ := LinearMap.mem_range.mp hy
    unfold Formalism.GM.DimensionMonotonicity.GlW.gS
    rw [Submodule.mem_sInf]
    rintro U ⟨hvU, hU⟩
    unfold Lv
    rw [Finsupp.linearCombination_apply]
    rw [Finsupp.sum]
    exact sum_mem fun w _ => U.smul_mem _ (act_mem G hU w (hvU (Set.mem_singleton v)))
  · have h1 : ({v} : Set V) ⊆ LinearMap.range (Lv G v) := by
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      rw [hx]
      exact LinearMap.mem_range.mpr ⟨Finsupp.single [] 1, by simp [Lv, act]⟩
    have h2 : G.Stable (LinearMap.range (Lv G v)) := by
      unfold Formalism.GM.DimensionMonotonicity.GlW.Stable
      intro a b y hy
      obtain ⟨c, rfl⟩ := LinearMap.mem_range.mp hy
      exact LinearMap.mem_range.mpr ⟨_, (E_Lv G v a b c).symm⟩
    unfold Formalism.GM.DimensionMonotonicity.GlW.gS
    exact sInf_le (And.intro h1 h2)

theorem Lv_add (v v' : V) (c : List (Fin r × Fin r) →₀ K) : Lv G (v + v') c = Lv G v c + Lv G v' c := by
  simp [Lv, Finsupp.linearCombination_apply, map_add, smul_add, Finsupp.sum_add]

theorem Lv_smul (t : K) (v : V) (c : List (Fin r × Fin r) →₀ K) : Lv G (t • v) c = t • Lv G v c := by
  simp only [Lv, Finsupp.linearCombination_apply, Finsupp.sum, map_smul, Finset.smul_sum, smul_comm t]

theorem ker_le {W : Submodule K V} (hW : G.Stable W) (hWf : G.FinW W) {la : Fin r → ℤ} {h h' : V}
    (hh : G.IsHW la h) (hh' : G.IsHW la h') (hhW : h ∈ W) (hh'W : h' ∈ W) (h0 : h ≠ 0) :
    LinearMap.ker (Lv G h) ≤ LinearMap.ker (Lv G h') := by
  intro c hc
  rw [LinearMap.mem_ker] at hc ⊢
  by_contra hx
  have hs : G.IsHW la (h + h') := ⟨by show G.comp la (h + h') = h + h'; rw [map_add, hh.1, hh'.1],
    fun a b hab => by rw [map_add, hh.2 a b hab, hh'.2 a b hab, add_zero]⟩
  have hxs : Lv G h' c ∈ G.gS {h + h'} := by rw [← range_Lv]; exact ⟨c, by rw [Lv_add, hc, zero_add]⟩
  have hxh : Lv G h' c ∈ G.gS {h'} := by rw [← range_Lv]; exact ⟨c, rfl⟩
  have hKs : G.Stable (G.gS {h + h'} ⊓ G.gS {h'}) := inf_stable G (G.gS_stable _) (G.gS_stable _)
  have hgW : G.gS {h'} ≤ W := G.gS_le (by simpa using hh'W) hW
  obtain ⟨S, hS⟩ := hWf
  have hn : ¬ (G.gS {h + h'} ⊓ G.gS {h'}) ≤ ⊥ := fun hle => hx ((Submodule.mem_bot K).mp (hle ⟨hxs, hxh⟩))
  obtain ⟨y, hyK, hy0, ν, hyw, hyr⟩ := G.exists_hwmod (G.graded_of hKs) (G.raising_of hKs)
    ⟨S, fun z hz => hS z (hgW hz.2)⟩ hn
  have hyhw : G.IsHW ν y := ⟨hyw, fun a b hab => (Submodule.mem_bot K).mp (hyr a b hab)⟩
  have hy0' : y ≠ 0 := fun e => hy0 (by rw [e]; exact Submodule.zero_mem _)
  obtain ⟨-, c1, hc1⟩ := G.hw_in_gS hh' hW ⟨S, hS⟩ hh'W hyK.2 hyhw hy0'
  obtain ⟨-, c2, hc2⟩ := G.hw_in_gS hs hW ⟨S, hS⟩ (W.add_mem hhW hh'W) hyK.1 hyhw hy0'
  by_cases hc2z : c2 = 0
  · rw [hc2z, zero_smul] at hc2; exact hy0' hc2
  · have e0 : c2 • h = (c1 - c2) • h' := by rw [sub_smul, ← hc1, hc2, smul_add, add_sub_cancel_right]
    have e : h = (c2⁻¹ * (c1 - c2)) • h' := by
      rw [mul_smul, ← e0, smul_smul, inv_mul_cancel₀ hc2z, one_smul]
    have e2 : Lv G h c = (c2⁻¹ * (c1 - c2)) • Lv G h' c := by
      conv_lhs => rw [e]
      rw [Lv_smul]
    rw [hc] at e2
    have ht : c2⁻¹ * (c1 - c2) = 0 := by
      rcases smul_eq_zero.mp e2.symm with h1 | h1
      · exact h1
      · exact absurd h1 hx
    rw [ht, zero_smul] at e
    exact h0 e

noncomputable def tr {h h' : V} (hk : LinearMap.ker (Lv G h) ≤ LinearMap.ker (Lv G h')) :
    LinearMap.range (Lv G h) →ₗ[K] V :=
  (LinearMap.ker (Lv G h)).liftQ (Lv G h') hk ∘ₗ (Lv G h).quotKerEquivRange.symm.toLinearMap

theorem tr_apply {h h' : V} (hk : LinearMap.ker (Lv G h) ≤ LinearMap.ker (Lv G h'))
    (c : List (Fin r × Fin r) →₀ K) : tr G hk ⟨Lv G h c, LinearMap.mem_range_self _ c⟩ = Lv G h' c := by
  simp only [tr, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.quotKerEquivRange_symm_apply_image,
    Submodule.mkQ_apply, Submodule.liftQ_apply]

end GlX

end Formalism.CountingSumsFrames.TO

namespace Formalism.CountingSumsFrames.TO

open Formalism.GM.DimensionMonotonicity Finset

namespace GlX

variable {K V : Type} [Field K] [CharZero K] [AddCommGroup V] [Module K V] {r : ℕ} (G : GlW K V r)

theorem tr_mem {h h' : V} (hk : LinearMap.ker (Lv G h) ≤ LinearMap.ker (Lv G h')) (y : LinearMap.range (Lv G h)) :
    tr G hk y ∈ LinearMap.range (Lv G h') := by
  obtain ⟨y, hy⟩ := y
  obtain ⟨c, rfl⟩ := LinearMap.mem_range.mp hy
  rw [show tr G hk ⟨Lv G h c, hy⟩ = Lv G h' c from tr_apply G hk c]
  exact LinearMap.mem_range_self _ _

theorem isWt_of_eig {μ : Fin r → ℤ} {z : V} (hz : ∀ c, G.E c c z = ((μ c : ℤ) : K) • z) : G.IsWt μ z := by
  unfold Formalism.GM.DimensionMonotonicity.GlW.IsWt
  obtain ⟨S, hS⟩ := G.dec z
  have hkill : ∀ ν, ν ≠ μ → G.comp ν z = 0 := by
    intro ν hne
    obtain ⟨c, hc⟩ : ∃ c, ν c ≠ μ c := by
      by_contra h
      push_neg at h
      exact hne (funext h)
    have h1 := G.shift c c ν z
    have hdl : Formalism.GM.DimensionMonotonicity.dl c c = (0 : Fin r → ℤ) := by simp [Formalism.GM.DimensionMonotonicity.dl]
    rw [hdl, sub_zero, G.diag c ν z, hz c, map_smul] at h1
    have h2 : (((ν c : ℤ) : K) - ((μ c : ℤ) : K)) • G.comp ν z = 0 := by
      rw [sub_smul, h1, sub_self]
    have h3 : (((ν c : ℤ) : K) - ((μ c : ℤ) : K)) ≠ 0 := by
      rw [sub_ne_zero]
      exact_mod_cast hc
    exact (smul_eq_zero.mp h2).resolve_left h3
  have hsum := G.sum_comp z S hS
  rw [Finset.sum_eq_single μ (fun ν _ hne => hkill ν hne) (fun hμ => hS μ hμ)] at hsum
  exact hsum

end GlX

section Proj

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]

theorem proj_exists {W : Submodule K V} {ι : Type*} [DecidableEq ι] (R : ι → Submodule K V)
    (hind : iSupIndep R) (hRW : ∀ i, R i ≤ W) (hWR : W ≤ ⨆ i, R i) :
    ∃ π : ι → V →ₗ[K] V, (∀ i x, π i x ∈ R i) ∧ (∀ i, ∀ x ∈ R i, π i x = x) ∧
      (∀ i j, j ≠ i → ∀ x ∈ R j, π i x = 0) := by
  obtain ⟨D, hD⟩ := Submodule.exists_isCompl W
  have hc : ∀ i, IsCompl (R i) ((⨆ (j) (_ : j ≠ i), R j) ⊔ D) := by
    intro i
    constructor
    · rw [Submodule.disjoint_def]
      intro x hx hx2
      obtain ⟨y, hy, d, hd, rfl⟩ := Submodule.mem_sup.mp hx2
      have hyW : y ∈ W := (iSup_le fun j => iSup_le fun _ => hRW j) hy
      have hdW : d ∈ W := by
        have := W.sub_mem (hRW i hx) hyW
        rwa [add_sub_cancel_left] at this
      have hd0 : d = 0 := (Submodule.disjoint_def.mp hD.disjoint) d hdW hd
      subst hd0
      rw [add_zero] at hx ⊢
      exact (Submodule.disjoint_def.mp (hind i)) y hx hy
    · rw [codisjoint_iff, eq_top_iff]
      calc ⊤ = W ⊔ D := hD.codisjoint.eq_top.symm
        _ ≤ (⨆ j, R j) ⊔ D := sup_le_sup_right hWR D
        _ = R i ⊔ ((⨆ (j) (_ : j ≠ i), R j) ⊔ D) := by rw [iSup_split_single R i, sup_assoc]
  refine ⟨fun i => (R i).subtype ∘ₗ (R i).projectionOnto _ (hc i), fun i x => by simp,
    fun i x hx => ?_, fun i j hji x hx => ?_⟩
  · have := Submodule.projectionOnto_apply_left (hc i) ⟨x, hx⟩
    simp only [LinearMap.comp_apply, Submodule.subtype_apply]
    rw [this]
  · have hxq : x ∈ (⨆ (j) (_ : j ≠ i), R j) ⊔ D :=
      Submodule.mem_sup_left (Submodule.mem_iSup_of_mem j (Submodule.mem_iSup_of_mem hji hx))
    have := Submodule.projectionOnto_apply_right (hc i) ⟨x, hxq⟩
    simp only [LinearMap.comp_apply, Submodule.subtype_apply]
    rw [this]; rfl

theorem proj_comm {W : Submodule K V} {ι : Type*} (R : ι → Submodule K V) (hWR : W ≤ ⨆ i, R i)
    (π : ι → V →ₗ[K] V) (h2 : ∀ i, ∀ x ∈ R i, π i x = x) (h3 : ∀ i j, j ≠ i → ∀ x ∈ R j, π i x = 0)
    (A : V →ₗ[K] V) (hA : ∀ j, ∀ x ∈ R j, A x ∈ R j) : ∀ i, ∀ x ∈ W, π i (A x) = A (π i x) := by
  intro i x hx
  refine Submodule.iSup_induction R (motive := fun x => π i (A x) = A (π i x)) (hWR hx) ?_ ?_ ?_
  · intro j y hy
    by_cases hij : j = i
    · rw [hij] at hy
      rw [h2 i _ (hA i y hy), h2 i y hy]
    · rw [h3 i j hij _ (hA j y hy), h3 i j hij y hy, map_zero]
  · simp
  · intro y z hy hz
    simp only [map_add, hy, hz]

end Proj

end Formalism.CountingSumsFrames.TO

namespace Formalism.CountingSumsFrames.TO

open MvPolynomial Finset

section Ext

variable {K : Type} [Field K] {σ : Type} [DecidableEq σ] (fs : σ → Prop) [DecidablePred fs]

def frst (m : σ →₀ ℕ) : σ →₀ ℕ := m.filter fs

def ltr (m : σ →₀ ℕ) : σ →₀ ℕ := m.filter (fun v => ¬ fs v)

def IsF (g : MvPolynomial σ K) : Prop := ∀ m ∈ g.support, ∀ v, m v ≠ 0 → fs v

def IsL (q : MvPolynomial σ K) : Prop := ∀ m ∈ q.support, ∀ v, m v ≠ 0 → ¬ fs v

theorem frst_add_ltr (m : σ →₀ ℕ) : frst fs m + ltr fs m = m := Finsupp.filter_pos_add_filter_neg m fs

theorem frst_of {m : σ →₀ ℕ} (h : ∀ v, m v ≠ 0 → fs v) : frst fs m = m := by
  ext v
  unfold frst
  rw [Finsupp.filter_apply]
  split_ifs with hv
  · rfl
  · by_contra hne
    exact hv (h v (Ne.symm hne))
theorem ltr_of {m : σ →₀ ℕ} (h : ∀ v, m v ≠ 0 → fs v) : ltr fs m = 0 := by
  ext v
  unfold ltr
  rw [Finsupp.filter_apply, Finsupp.coe_zero, Pi.zero_apply]
  by_cases hv : fs v
  · simp [hv]
  · have : m v = 0 := by
      by_contra hne
      exact hv (h v hne)
    simp [hv, this]
theorem frst_of' {m : σ →₀ ℕ} (h : ∀ v, m v ≠ 0 → ¬ fs v) : frst fs m = 0 := by
  ext v
  unfold frst
  rw [Finsupp.filter_apply, Finsupp.coe_zero, Pi.zero_apply]
  split_ifs with hv
  · by_contra hne
    exact h v hne hv
  · rfl
theorem ltr_of' {m : σ →₀ ℕ} (h : ∀ v, m v ≠ 0 → ¬ fs v) : ltr fs m = m := by
  ext v
  unfold ltr
  rw [Finsupp.filter_apply]
  by_cases hv : fs v
  · have : m v = 0 := by
      by_contra hne
      exact h v hne hv
    simp [hv, this]
  · simp [hv]
theorem frst_add (m m' : σ →₀ ℕ) : frst fs (m + m') = frst fs m + frst fs m' := by
  unfold frst
  exact Finsupp.filter_add
theorem ltr_add (m m' : σ →₀ ℕ) : ltr fs (m + m') = ltr fs m + ltr fs m' := by
  unfold ltr
  exact Finsupp.filter_add
theorem frst_isF (m : σ →₀ ℕ) : ∀ v, frst fs m v ≠ 0 → fs v := by
  intro v hv
  unfold frst at hv
  rw [Finsupp.filter_apply] at hv
  by_contra h
  exact hv (if_neg h)
theorem ltr_isL (m : σ →₀ ℕ) : ∀ v, ltr fs m v ≠ 0 → ¬ fs v := by
  intro v hv h
  unfold ltr at hv
  simp [Finsupp.filter_apply, h] at hv

noncomputable def ext (φ : MvPolynomial σ K →ₗ[K] MvPolynomial σ K) : MvPolynomial σ K →ₗ[K] MvPolynomial σ K :=
  (basisMonomials σ K).constr K (fun m => φ (monomial (frst fs m) 1) * monomial (ltr fs m) 1)

noncomputable def slc (m : σ →₀ ℕ) : MvPolynomial σ K →ₗ[K] MvPolynomial σ K :=
  (basisMonomials σ K).constr K (fun m' => if ltr fs m' = m then monomial (frst fs m') 1 else 0)

theorem monomial_eq_basis (m : σ →₀ ℕ) (a : K) : monomial m a = a • (basisMonomials σ K) m := by
  simp only [coe_basisMonomials, smul_monomial, smul_eq_mul, mul_one]

theorem ext_monomial (φ : MvPolynomial σ K →ₗ[K] MvPolynomial σ K) (m : σ →₀ ℕ) (a : K) :
    ext fs φ (monomial m a) = a • (φ (monomial (frst fs m) 1) * monomial (ltr fs m) 1) := by
  rw [monomial_eq_basis m a, map_smul]
  simp only [ext, Module.Basis.constr_basis]

theorem sl_monomial (m m' : σ →₀ ℕ) (a : K) :
    slc fs m (monomial m' a) = if ltr fs m' = m then monomial (frst fs m') a else 0 := by
  rw [monomial_eq_basis m' a, map_smul]
  simp only [slc, Module.Basis.constr_basis]
  split_ifs <;> simp [smul_monomial]

theorem ext_add (φ ψ : MvPolynomial σ K →ₗ[K] MvPolynomial σ K) : ext fs (φ + ψ) = ext fs φ + ext fs ψ := by
  refine (basisMonomials σ K).ext fun m => ?_
  simp only [coe_basisMonomials, ext_monomial, LinearMap.add_apply, add_mul, one_smul]

theorem ext_sum {ι : Type*} (s : Finset ι) (φ : ι → MvPolynomial σ K →ₗ[K] MvPolynomial σ K) :
    ext fs (∑ i ∈ s, φ i) = ∑ i ∈ s, ext fs (φ i) := by
  refine (basisMonomials σ K).ext fun m => ?_
  simp only [coe_basisMonomials, ext_monomial, LinearMap.sum_apply, Finset.sum_mul, one_smul]

theorem ext_mul (φ : MvPolynomial σ K →ₗ[K] MvPolynomial σ K) {g q : MvPolynomial σ K} (hg : IsF fs g)
    (hq : IsL fs q) : ext fs φ (g * q) = φ g * q := by
  classical
  rw [g.as_sum, q.as_sum, Finset.sum_mul_sum, map_sum, map_sum, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun b hb => ?_
  rw [monomial_mul, ext_monomial, frst_add, ltr_add, frst_of fs (hg a ha), ltr_of fs (hg a ha),
    frst_of' fs (hq b hb), ltr_of' fs (hq b hb), add_zero, zero_add]
  have h1 : (monomial a (coeff a g) : MvPolynomial σ K) = coeff a g • monomial a 1 := by
    rw [smul_monomial, smul_eq_mul, mul_one]
  have h2 : (monomial b (coeff b q) : MvPolynomial σ K) = coeff b q • monomial b 1 := by
    rw [smul_monomial, smul_eq_mul, mul_one]
  rw [h1, h2, map_smul, smul_mul_assoc, mul_smul_comm, smul_smul]

theorem sl_mul (m : σ →₀ ℕ) {g q : MvPolynomial σ K} (hg : IsF fs g) (hq : IsL fs q) :
    slc fs m (g * q) = coeff m q • g := by
  classical
  conv_lhs => rw [g.as_sum, q.as_sum, Finset.sum_mul_sum, map_sum]
  conv_rhs => rw [g.as_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [map_sum]
  have key : ∀ b ∈ q.support, slc fs m (monomial a (coeff a g) * monomial b (coeff b q)) =
      if b = m then monomial a (coeff a g * coeff m q) else 0 := by
    intro b hb
    rw [monomial_mul, sl_monomial, frst_add, ltr_add, frst_of fs (hg a ha), ltr_of fs (hg a ha),
      frst_of' fs (hq b hb), ltr_of' fs (hq b hb), add_zero, zero_add]
    split_ifs with h
    · rw [h]
    · rfl
  rw [Finset.sum_congr rfl key, Finset.sum_ite_eq']
  split_ifs with hm
  · rw [smul_monomial, smul_eq_mul, mul_comm (coeff a g)]
  · simp only [mem_support_iff, not_not] at hm
    rw [hm, zero_smul]

theorem ext_eq_sum (φ : MvPolynomial σ K →ₗ[K] MvPolynomial σ K) (x : MvPolynomial σ K) (S : Finset (σ →₀ ℕ))
    (hS : ∀ m ∈ x.support, ltr fs m ∈ S) : ext fs φ x = ∑ m ∈ S, φ (slc fs m x) * monomial m 1 := by
  conv_lhs => rw [x.as_sum]
  conv_rhs => rw [x.as_sum]
  simp_rw [map_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d hd => ?_
  simp_rw [sl_monomial, apply_ite φ, map_zero, ite_mul, zero_mul]
  rw [Finset.sum_ite_eq S (ltr fs d), if_pos (hS d hd), ext_monomial]
  have h1 : (monomial (frst fs d) (coeff d x) : MvPolynomial σ K) = coeff d x • monomial (frst fs d) 1 := by
    rw [smul_monomial, smul_eq_mul, mul_one]
  rw [h1, map_smul, smul_mul_assoc]

theorem eq_sum_sl (x : MvPolynomial σ K) (S : Finset (σ →₀ ℕ)) (hS : ∀ m ∈ x.support, ltr fs m ∈ S) :
    x = ∑ m ∈ S, slc fs m x * monomial m 1 := by
  conv_lhs => rw [x.as_sum]
  conv_rhs => rw [x.as_sum]
  simp_rw [map_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d hd => ?_
  simp_rw [sl_monomial, ite_mul, zero_mul]
  rw [Finset.sum_ite_eq S (ltr fs d), if_pos (hS d hd), monomial_mul, mul_one, frst_add_ltr]

theorem sl_isF (m : σ →₀ ℕ) (x : MvPolynomial σ K) : IsF fs (slc fs m x) := by
  intro m' hm' v hv
  rw [x.as_sum, map_sum] at hm'
  obtain ⟨d, -, hd⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum hm')
  rw [sl_monomial] at hd
  split_ifs at hd
  · have := support_monomial_subset hd
    rw [Finset.mem_singleton] at this
    subst this
    exact frst_isF fs d v hv
  · simp at hd

theorem isL_monomial_ltr (m : σ →₀ ℕ) (a : K) : IsL fs (monomial (ltr fs m) a) := by
  intro m' hm' v hv
  have := support_monomial_subset hm'
  rw [Finset.mem_singleton] at this
  subst this
  exact ltr_isL fs m v hv

theorem isF_monomial_frst (m : σ →₀ ℕ) (a : K) : IsF fs (monomial (frst fs m) a) := by
  intro m' hm' v hv
  have := support_monomial_subset hm'
  rw [Finset.mem_singleton] at this
  subst this
  exact frst_isF fs m v hv

theorem monomial_split (m : σ →₀ ℕ) (a : K) :
    monomial m a = monomial (frst fs m) a * monomial (ltr fs m) 1 := by
  rw [monomial_mul, mul_one, frst_add_ltr]

end Ext

end Formalism.CountingSumsFrames.TO

namespace Formalism.CountingSumsFrames.TO

open MvPolynomial Finset Formalism.GM.DimensionMonotonicity Formalism.GM.M

variable {p : ℕ} [Fact p.Prime] {N r : ℕ}

def fsj (N r j0 : ℕ) : Fin N × Fin r → Prop := fun v => (v.1 : ℕ) < j0

instance (N r j0 : ℕ) : DecidablePred (fsj N r j0) := fun v => Nat.decLt _ _

def wlat (N r j0 : ℕ) : Fin N × Fin r → ℤ := fun v => if (v.1 : ℕ) < j0 then 0 else 1

def wfir (N r j0 : ℕ) : Fin N × Fin r → ℤ := fun v => if (v.1 : ℕ) < j0 then 1 else 0

theorem weight_eq_zero_iff {σ : Type} (w : σ → ℤ) (hw : ∀ v, 0 ≤ w v) (m : σ →₀ ℕ) :
    Finsupp.weight w m = 0 ↔ ∀ v, m v ≠ 0 → w v = 0 := by
  rw [Finsupp.weight_apply, Finsupp.sum, Finset.sum_eq_zero_iff_of_nonneg (fun v _ => nsmul_nonneg (hw v) _)]
  constructor
  · intro h v hv
    have := h v (Finsupp.mem_support_iff.mpr hv)
    rw [nsmul_eq_mul] at this
    rcases mul_eq_zero.mp this with h0 | h0
    · exact absurd (by exact_mod_cast h0 : m v = 0) hv
    · exact h0
  · intro h v hv
    rw [h v (Finsupp.mem_support_iff.mp hv), smul_zero]

theorem isF_iff (j0 : ℕ) (g : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    IsF (fsj N r j0) g ↔ g ∈ weightedHomogeneousSubmodule ℚ_[p] (wlat N r j0) 0 := by
  rw [mem_weightedHomogeneousSubmodule]
  have hw : ∀ v, 0 ≤ wlat N r j0 v := fun v => by
    unfold wlat
    split_ifs <;> norm_num
  have key : ∀ d : Fin N × Fin r →₀ ℕ, Finsupp.weight (wlat N r j0) d = 0 ↔ ∀ v, d v ≠ 0 → fsj N r j0 v := by
    intro d
    rw [weight_eq_zero_iff _ hw]
    refine forall_congr' fun v => imp_congr_right fun _ => ?_
    unfold wlat fsj
    split_ifs with h <;> simp [h]
  constructor
  · intro h d hd
    exact (key d).mpr (h d (mem_support_iff.mpr hd))
  · intro h d hd v hv
    exact (key d).mp (h (mem_support_iff.mp hd)) v hv

theorem isL_iff (j0 : ℕ) (g : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    IsL (fsj N r j0) g ↔ g ∈ weightedHomogeneousSubmodule ℚ_[p] (wfir N r j0) 0 := by
  rw [mem_weightedHomogeneousSubmodule]
  have hw : ∀ v, 0 ≤ wfir N r j0 v := fun v => by
    unfold wfir
    split_ifs <;> norm_num
  have key : ∀ d : Fin N × Fin r →₀ ℕ, Finsupp.weight (wfir N r j0) d = 0 ↔ ∀ v, d v ≠ 0 → ¬ fsj N r j0 v := by
    intro d
    rw [weight_eq_zero_iff _ hw]
    refine forall_congr' fun v => imp_congr_right fun _ => ?_
    unfold wfir fsj
    split_ifs with h <;> simp [h]
  constructor
  · intro h d hd
    exact (key d).mpr (h d (mem_support_iff.mpr hd))
  · intro h d hd v hv
    exact (key d).mp (h (mem_support_iff.mp hd)) v hv

theorem glAct_isF (L : Letters N) (j0 J : ℕ) (c d : Fin r) {g : MvPolynomial (Fin N × Fin r) ℚ_[p]}
    (hg : IsF (fsj N r j0) g) : IsF (fsj N r j0) (glAct p L J c d g) := by
  rw [isF_iff] at hg ⊢
  exact glAct_lw L J c d (wlat N r j0) (fun i c c' => rfl) hg

theorem glAct_isL (L : Letters N) (j0 J : ℕ) (c d : Fin r) {g : MvPolynomial (Fin N × Fin r) ℚ_[p]}
    (hg : IsL (fsj N r j0) g) : IsL (fsj N r j0) (glAct p L J c d g) := by
  rw [isL_iff] at hg ⊢
  exact glAct_lw L J c d (wfir N r j0) (fun i c c' => rfl) hg

theorem midAct_isF (L : Letters N) (j0 J : ℕ) (c d : Fin r) {g : MvPolynomial (Fin N × Fin r) ℚ_[p]}
    (hg : IsF (fsj N r j0) g) : midAct p L j0 J c d g = 0 := by
  rw [midAct, LinearMap.sum_apply]
  refine Finset.sum_eq_zero fun i _ => ?_
  split_ifs with h
  · rw [Formalism.GM.FrozenVariableComponents.top_apply]
    have hz : ∀ e : Fin r, pderiv (i, e) g = 0 := fun e => pderiv_eq_zero_of fun m hm => by
      by_contra hne; have := hg m hm (i, e) hne; simp [fsj] at this; omega
    split_ifs <;> simp [hz]
  · rfl

theorem killL_of_isL {j0 J : ℕ} (hJ : J ≤ j0) {q : MvPolynomial (Fin N × Fin r) ℚ_[p]} (hq : IsL (fsj N r j0) q) :
    ∀ m ∈ q.support, ∀ v : Fin N × Fin r, (v.1 : ℕ) < J → m v = 0 := by
  intro m hm v hv
  by_contra hne
  exact hq m hm v hne (show fsj N r j0 v from lt_of_lt_of_le hv hJ)

theorem slc_glAct (L : Letters N) {j0 J : ℕ} (hJ : J ≤ j0) (c d : Fin r) (m : Fin N × Fin r →₀ ℕ)
    (x : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    slc (fsj N r j0) m (glAct p L J c d x) = glAct p L J c d (slc (fsj N r j0) m x) := by
  induction x using MvPolynomial.induction_on' with
  | monomial m' a =>
    rw [monomial_split (fsj N r j0) m' a,
      glAct_mul_kill L J c d _ (killL_of_isL hJ (isL_monomial_ltr _ m' 1)),
      sl_mul _ m (glAct_isF L j0 J c d (isF_monomial_frst _ m' a)) (isL_monomial_ltr _ m' 1),
      sl_mul _ m (isF_monomial_frst _ m' a) (isL_monomial_ltr _ m' 1), map_smul]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

theorem weight_wv_zero (L : Letters N) {j0 J : ℕ} (hJ : J ≤ j0) (m : Fin N × Fin r →₀ ℕ)
    (hm : ∀ v, m v ≠ 0 → ¬ fsj N r j0 v) : Finsupp.weight (wv L J) m = 0 := by
  rw [Finsupp.weight_apply, Finsupp.sum]
  refine Finset.sum_eq_zero fun v hv => ?_
  have h1 := hm v (Finsupp.mem_support_iff.mp hv)
  have h2 : ¬ ((v.1 : ℕ) < J) := fun h => h1 (show fsj N r j0 v from lt_of_lt_of_le h hJ)
  simp [Formalism.GM.DimensionMonotonicity.wv, h2]

theorem slc_wh (L : Letters N) {j0 J : ℕ} (hJ : J ≤ j0) (m : Fin N × Fin r →₀ ℕ) {ν : Fin r → ℤ}
    {x : MvPolynomial (Fin N × Fin r) ℚ_[p]} (hx : x ∈ weightedHomogeneousSubmodule ℚ_[p] (wv L J) ν) :
    slc (fsj N r j0) m x ∈ weightedHomogeneousSubmodule ℚ_[p] (wv L J) ν := by
  rw [mem_weightedHomogeneousSubmodule] at hx ⊢
  intro d hd
  have hd' : d ∈ (slc (fsj N r j0) m x).support := mem_support_iff.mpr hd
  rw [x.as_sum, map_sum] at hd'
  obtain ⟨e, he, hde⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum hd')
  rw [sl_monomial] at hde
  split_ifs at hde
  · have := support_monomial_subset hde
    rw [Finset.mem_singleton] at this
    subst this
    have hw := hx (mem_support_iff.mp he)
    rw [← frst_add_ltr (fsj N r j0) e, map_add, weight_wv_zero L hJ _ (ltr_isL _ e), add_zero] at hw
    exact hw
  · simp at hde

end Formalism.CountingSumsFrames.TO

namespace Formalism.CountingSumsFrames.TO

open MvPolynomial Finset Formalism.GM.DimensionMonotonicity Formalism.GM.M

variable {p : ℕ} [Fact p.Prime] {N r : ℕ}

theorem slc_ycond [NeZero r] (L : Letters N) {j0 J : ℕ} (hJ : J ≤ j0) (M : WithTop ℤ) (m : Fin N × Fin r →₀ ℕ)
    {F : MvPolynomial (Fin N × Fin r) ℚ_[p]} (hF : F ∈ YCond p L J M) : slc (fsj N r j0) m F ∈ YCond p L J M :=
  ycond_of_comm L J M (slc (fsj N r j0) m) (fun c d F => slc_glAct L hJ c d m F) (fun ν F hF => slc_wh L hJ m hF) F hF

theorem slc_pol (L : Letters N) (j0 : ℕ) (m : Fin N × Fin r →₀ ℕ) {x : MvPolynomial (Fin N × Fin r) ℚ_[p]}
    (hx : x ∈ Pol p r L) : slc (fsj N r j0) m x ∈ Pol p r (Lz L j0) := by
  unfold Formalism.GM.M.Pol at hx ⊢
  rw [mem_restrictSupport_iff] at hx ⊢
  intro d hd
  rw [Finset.mem_coe, x.as_sum, map_sum] at hd
  obtain ⟨e, he, hde⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum hd)
  rw [sl_monomial] at hde
  split_ifs at hde
  · have := support_monomial_subset hde
    rw [Finset.mem_singleton] at this
    subst this
    have hme : Formalism.GM.M.MultiDeg L e := hx (Finset.mem_coe.mpr he)
    intro i
    simp only [Formalism.GM.DimensionMonotonicity.Lz]
    split_ifs with hi
    · rw [← hme i]
      refine Finset.sum_congr rfl fun c _ => ?_
      simp [frst, Finsupp.filter_apply, fsj, hi]
    · refine Finset.sum_eq_zero fun c _ => ?_
      simp [frst, Finsupp.filter_apply, fsj, hi]
  · simp at hde

theorem isF_of_polLz (L : Letters N) (j0 : ℕ) {y : MvPolynomial (Fin N × Fin r) ℚ_[p]}
    (hy : y ∈ Pol p r (Lz L j0)) : IsF (fsj N r j0) y := by
  intro m hm v hv
  unfold Formalism.GM.M.Pol at hy
  rw [mem_restrictSupport_iff] at hy
  have hmd : Formalism.GM.M.MultiDeg (Lz L j0) m := hy (Finset.mem_coe.mpr hm)
  by_contra hv'
  have hv'' : ¬ ((v.1 : ℕ) < j0) := hv'
  have h1 := hmd v.1
  simp only [Formalism.GM.DimensionMonotonicity.Lz] at h1
  rw [if_neg hv''] at h1
  have h2 : m (v.1, v.2) = 0 := (Finset.sum_eq_zero_iff.mp h1) v.2 (Finset.mem_univ _)
  exact hv h2

theorem mul_ltr_pol (L : Letters N) (j0 : ℕ) {g : MvPolynomial (Fin N × Fin r) ℚ_[p]} (hg : g ∈ Pol p r (Lz L j0))
    {m' : Fin N × Fin r →₀ ℕ} (hm : MultiDeg L m') : g * monomial (ltr (fsj N r j0) m') 1 ∈ Pol p r L := by
  unfold Formalism.GM.M.Pol at hg ⊢
  rw [mem_restrictSupport_iff] at hg ⊢
  intro d hd
  rw [Finset.mem_coe] at hd
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp (support_mul _ _ hd)
  have hb' := support_monomial_subset hb
  rw [Finset.mem_singleton] at hb'
  subst hb'
  have hma : Formalism.GM.M.MultiDeg (Lz L j0) a := hg (Finset.mem_coe.mpr ha)
  intro i
  have h1 := hma i
  have h2 := hm i
  simp only [Formalism.GM.DimensionMonotonicity.Lz] at h1
  simp only [Finsupp.add_apply, Finset.sum_add_distrib]
  split_ifs at h1 with hi
  · rw [h1]
    have h3 : ∑ c, ltr (fsj N r j0) m' (i, c) = 0 :=
      Finset.sum_eq_zero fun c _ => by simp [ltr, Finsupp.filter_apply, fsj, hi]
    rw [h3, add_zero]
  · rw [h1, zero_add, ← h2]
    refine Finset.sum_congr rfl fun c _ => ?_
    simp [ltr, Finsupp.filter_apply, fsj, hi]

theorem midAct_eq (L : Letters N) {j0 J : ℕ} (hJ : j0 ≤ J) (c d : Fin r) (x : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    midAct p L j0 J c d x = glAct p L J c d x - glAct p L j0 c d x := by
  rw [glAct_split L hJ c d, LinearMap.add_apply]; abel

theorem midAct_isL (L : Letters N) {j0 J : ℕ} (hJ : j0 ≤ J) (c d : Fin r) {q : MvPolynomial (Fin N × Fin r) ℚ_[p]}
    (hq : IsL (fsj N r j0) q) : IsL (fsj N r j0) (midAct p L j0 J c d q) := by
  rw [midAct_eq L hJ, isL_iff]
  exact Submodule.sub_mem _ ((isL_iff _ _).mp (glAct_isL L j0 J c d hq)) ((isL_iff _ _).mp (glAct_isL L j0 j0 c d hq))

theorem midAct_mul_F (L : Letters N) {j0 J : ℕ} (hJ : j0 ≤ J) (c d : Fin r) {g q : MvPolynomial (Fin N × Fin r) ℚ_[p]}
    (hg : IsF (fsj N r j0) g) : midAct p L j0 J c d (g * q) = g * midAct p L j0 J c d q := by
  have h0 := midAct_isF L j0 J c d hg
  rw [midAct_eq L hJ] at h0 ⊢
  rw [midAct_eq L hJ c d q, Formalism.GM.M.FB.glAct_mul, Formalism.GM.M.FB.glAct_mul]
  have : q * glAct p L J c d g - q * glAct p L j0 c d g = 0 := by rw [← mul_sub, h0, mul_zero]
  linear_combination this

theorem ext_glAct (L : Letters N) {j0 J : ℕ} (hJ : j0 ≤ J) (φ : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hφ1 : ∀ c d x, φ (glAct p L j0 c d x) = glAct p L j0 c d (φ x)) (hφF : ∀ x, IsF (fsj N r j0) (φ x))
    (c d : Fin r) (x : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    ext (fsj N r j0) φ (glAct p L J c d x) = glAct p L J c d (ext (fsj N r j0) φ x) := by
  induction x using MvPolynomial.induction_on' with
  | monomial m' a =>
    have hg := isF_monomial_frst (fsj N r j0) m' a
    have hq := isL_monomial_ltr (fsj N r j0) m' (1 : ℚ_[p])
    rw [monomial_split (fsj N r j0) m' a, ext_mul _ φ hg hq, glAct_split L hJ c d, LinearMap.add_apply,
      LinearMap.add_apply, glAct_mul_kill L j0 c d _ (killL_of_isL le_rfl hq), midAct_mul_F L hJ c d hg,
      glAct_mul_kill L j0 c d _ (killL_of_isL le_rfl hq), midAct_mul_F L hJ c d (hφF _), map_add,
      ext_mul _ φ (glAct_isF L j0 j0 c d hg) hq, ext_mul _ φ hg (midAct_isL L hJ c d hq), hφ1]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem weight_first (L : Letters N) {j0 J : ℕ} (hJ : j0 ≤ J) (m : Fin N × Fin r →₀ ℕ)
    (hm : ∀ v, m v ≠ 0 → fsj N r j0 v) : Finsupp.weight (wv L J) m = Finsupp.weight (wv L j0) m := by
  rw [Finsupp.weight_apply, Finsupp.weight_apply, Finsupp.sum, Finsupp.sum]
  refine Finset.sum_congr rfl fun v hv => ?_
  have h1 : (v.1 : ℕ) < j0 := hm v (Finsupp.mem_support_iff.mp hv)
  have h2 : (v.1 : ℕ) < J := lt_of_lt_of_le h1 hJ
  simp [Formalism.GM.DimensionMonotonicity.wv, h1, h2]

theorem wh_first (L : Letters N) {j0 J : ℕ} (hJ : j0 ≤ J) {ν : Fin r → ℤ} {y : MvPolynomial (Fin N × Fin r) ℚ_[p]}
    (hF : IsF (fsj N r j0) y) (hy : y ∈ weightedHomogeneousSubmodule ℚ_[p] (wv L j0) ν) :
    y ∈ weightedHomogeneousSubmodule ℚ_[p] (wv L J) ν := by
  rw [mem_weightedHomogeneousSubmodule] at hy ⊢
  intro d hd
  rw [weight_first L hJ d (hF d (mem_support_iff.mpr hd))]
  exact hy hd

theorem ext_wh (L : Letters N) {j0 J : ℕ} (hJ : j0 ≤ J) (φ : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hφw : ∀ ν x, x ∈ weightedHomogeneousSubmodule ℚ_[p] (wv L j0) ν → φ x ∈ weightedHomogeneousSubmodule ℚ_[p] (wv L j0) ν)
    (hφF : ∀ x, IsF (fsj N r j0) (φ x)) (ν : Fin r → ℤ) (x : MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hx : x ∈ weightedHomogeneousSubmodule ℚ_[p] (wv L J) ν) :
    ext (fsj N r j0) φ x ∈ weightedHomogeneousSubmodule ℚ_[p] (wv L J) ν := by
  classical
  rw [x.as_sum, map_sum]
  refine Submodule.sum_mem _ fun m' hm' => ?_
  rw [ext_monomial]
  refine Submodule.smul_mem _ _ ?_
  have h1 : Finsupp.weight (wv L J) m' = ν := hx (mem_support_iff.mp hm')
  have hf : φ (monomial (frst (fsj N r j0) m') 1) ∈ weightedHomogeneousSubmodule ℚ_[p] (wv L J)
      (Finsupp.weight (wv L J) (frst (fsj N r j0) m')) := by
    rw [weight_first L hJ _ (frst_isF _ m')]
    exact wh_first L hJ (hφF _) (hφw _ _ (isWeightedHomogeneous_monomial _ _ _ rfl))
  have hl : IsWeightedHomogeneous (wv L J) (monomial (ltr (fsj N r j0) m') (1 : ℚ_[p]))
      (Finsupp.weight (wv L J) (ltr (fsj N r j0) m')) := isWeightedHomogeneous_monomial _ _ _ rfl
  rw [mem_weightedHomogeneousSubmodule] at hf ⊢
  rw [← h1]
  conv_rhs => rw [← frst_add_ltr (fsj N r j0) m']
  rw [map_add]
  exact hf.mul hl

end Formalism.CountingSumsFrames.TO

namespace Formalism.CountingSumsFrames.TO

open MvPolynomial Finset Formalism.GM.DimensionMonotonicity Formalism.GM.M

variable {p : ℕ} [Fact p.Prime] {N r : ℕ}

def Mup {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ) (j0 : ℕ) : Fin q → WithTop ℤ :=
  fun k => if J k < j0 then M k else ⊤

noncomputable def Cset (p : ℕ) [Fact p.Prime] [NeZero r] (L : Letters N) (j0 : ℕ) {q : ℕ} (J : Fin q → ℕ)
    (M : Fin q → WithTop ℤ) : Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]) :=
  Pol p r (Lz L j0) ⊓ ⨅ k, YCond p L (J k) (Mup J M j0 k)

theorem slc_C [NeZero r] (L : Letters N) (j0 : ℕ) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ)
    {x : MvPolynomial (Fin N × Fin r) ℚ_[p]} (hx : x ∈ Y p L J M) (m : Fin N × Fin r →₀ ℕ) :
    slc (fsj N r j0) m x ∈ Cset p L j0 J M := by
  obtain ⟨hxP, hxY⟩ := Submodule.mem_inf.mp hx
  refine Submodule.mem_inf.mpr ⟨slc_pol L j0 m hxP, (Submodule.mem_iInf _).mpr fun k => ?_⟩
  by_cases hk : J k < j0
  · rw [Mup, if_pos hk]
    exact slc_ycond L (le_of_lt hk) (M k) m ((Submodule.mem_iInf _).mp hxY k)
  · rw [Mup, if_neg hk, ycond_top]; exact Submodule.mem_top

theorem ext_Y [NeZero r] (L : Letters N) (j0 : ℕ) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ)
    (φ : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hφ1 : ∀ c d x, φ (glAct p L j0 c d x) = glAct p L j0 c d (φ x))
    (hφw : ∀ ν x, x ∈ weightedHomogeneousSubmodule ℚ_[p] (wv L j0) ν → φ x ∈ weightedHomogeneousSubmodule ℚ_[p] (wv L j0) ν)
    (hφP : ∀ x, φ x ∈ Pol p r (Lz L j0)) (hφC : ∀ x ∈ Cset p L j0 J M, φ x ∈ Cset p L j0 J M) :
    ∀ x ∈ Y p L J M, ext (fsj N r j0) φ x ∈ Y p L J M := by
  classical
  intro x hx
  obtain ⟨hxP, hxY⟩ := Submodule.mem_inf.mp hx
  have hφF : ∀ x, IsF (fsj N r j0) (φ x) := fun x => isF_of_polLz L j0 (hφP x)
  have hsum := ext_eq_sum (fsj N r j0) φ x (x.support.image (ltr (fsj N r j0)))
    (fun m hm => Finset.mem_image_of_mem _ hm)
  refine Submodule.mem_inf.mpr ⟨?_, (Submodule.mem_iInf _).mpr fun k => ?_⟩
  · rw [hsum]
    refine Submodule.sum_mem _ fun m hm => ?_
    obtain ⟨m', hm', rfl⟩ := Finset.mem_image.mp hm
    exact mul_ltr_pol L j0 (hφP _) (((MvPolynomial.mem_restrictSupport_iff ℚ_[p]).mp hxP) hm')
  · by_cases hk : J k < j0
    · rw [hsum]
      refine Submodule.sum_mem _ fun m hm => ?_
      obtain ⟨m', hm', rfl⟩ := Finset.mem_image.mp hm
      have h1 := (Submodule.mem_iInf _).mp (Submodule.mem_inf.mp (hφC _ (slc_C L j0 J M hx (ltr (fsj N r j0) m')))).2 k
      rw [Mup, if_pos hk] at h1
      rw [mul_comm]
      exact ycond_mul_B L (le_of_lt hk) (M k) (killL_of_isL le_rfl (isL_monomial_ltr _ m' 1)) _ h1
    · have hJ : j0 ≤ J k := by omega
      exact ycond_of_comm L (J k) (M k) (ext (fsj N r j0) φ) (ext_glAct L hJ φ hφ1 hφF)
        (fun ν F hF => ext_wh L hJ φ hφw hφF ν F hF) x ((Submodule.mem_iInf _).mp hxY k)

noncomputable def psi (p : ℕ) [Fact p.Prime] (L : Letters N) (j0 : ℕ) :
    MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p] :=
  weightedHomogeneousComponent (wL N r) (fun i => ((Lz L j0).deg i : ℤ))

theorem psi_mem (L : Letters N) (j0 : ℕ) (x : MvPolynomial (Fin N × Fin r) ℚ_[p]) : psi p L j0 x ∈ Pol p r (Lz L j0) := by
  rw [pol_iff]; exact weightedHomogeneousComponent_isWeightedHomogeneous _ _

theorem psi_id (L : Letters N) (j0 : ℕ) {x : MvPolynomial (Fin N × Fin r) ℚ_[p]} (hx : x ∈ Pol p r (Lz L j0)) :
    psi p L j0 x = x := by
  rw [pol_iff] at hx
  rw [psi, weightedHomogeneousComponent_of_mem hx, if_pos rfl]

private theorem whc_same_lemma {σ M : Type} [AddCommMonoid M] (w : σ → M) {m : M} {φ : MvPolynomial σ ℚ_[p]}
    (h : φ ∈ weightedHomogeneousSubmodule ℚ_[p] w m) : weightedHomogeneousComponent w m φ = φ := by
  classical
  rw [mem_weightedHomogeneousSubmodule] at h
  ext d
  rw [coeff_weightedHomogeneousComponent]
  split_ifs with hd
  · rfl
  · by_contra hne
    exact hd (h (Ne.symm hne))

private theorem whc_ne_lemma_2 {σ M : Type} [AddCommMonoid M] (w : σ → M) {m n : M} {φ : MvPolynomial σ ℚ_[p]}
    (h : φ ∈ weightedHomogeneousSubmodule ℚ_[p] w m) (hnm : n ≠ m) : weightedHomogeneousComponent w n φ = 0 := by
  classical
  rw [mem_weightedHomogeneousSubmodule] at h
  ext d
  rw [coeff_weightedHomogeneousComponent, coeff_zero]
  split_ifs with hd
  · by_contra hne
    exact hnm (hd.symm.trans (h hne))
  · rfl

theorem whc_comm {σ M : Type} [AddCommMonoid M] (w : σ → M) (A : MvPolynomial σ ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial σ ℚ_[p])
    (hA : ∀ D x, x ∈ weightedHomogeneousSubmodule ℚ_[p] w D → A x ∈ weightedHomogeneousSubmodule ℚ_[p] w D)
    (D : M) (x : MvPolynomial σ ℚ_[p]) :
    weightedHomogeneousComponent w D (A x) = A (weightedHomogeneousComponent w D x) := by
  classical
  refine MvPolynomial.induction_on' x (fun d a => ?_) (fun f g hf hg => ?_)
  · have h0 : monomial d a ∈ weightedHomogeneousSubmodule ℚ_[p] w (Finsupp.weight w d) :=
      (mem_weightedHomogeneousSubmodule ..).mpr (isWeightedHomogeneous_monomial w d a rfl)
    have h1 := hA _ _ h0
    by_cases h : Finsupp.weight w d = D
    · subst h
      rw [whc_same_lemma w h0, whc_same_lemma w h1]
    · rw [whc_ne_lemma_2 w h0 (Ne.symm h), whc_ne_lemma_2 w h1 (Ne.symm h), map_zero]
  · simp only [map_add, hf, hg]

theorem whc_keep {σ M M' : Type} [AddCommMonoid M] [AddCommMonoid M'] (w : σ → M) (w' : σ → M') (ν : M')
    (D : M) {x : MvPolynomial σ ℚ_[p]} (hx : x ∈ weightedHomogeneousSubmodule ℚ_[p] w D) :
    weightedHomogeneousComponent w' ν x ∈ weightedHomogeneousSubmodule ℚ_[p] w D := by
  classical
  rw [mem_weightedHomogeneousSubmodule] at hx ⊢
  intro d hd
  rw [coeff_weightedHomogeneousComponent] at hd
  split_ifs at hd with h
  · exact hx hd
  · exact absurd rfl hd

theorem psi_glAct (L L' : Letters N) (j0 j : ℕ) (c d : Fin r) (x : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    psi p L j0 (glAct p L' j c d x) = glAct p L' j c d (psi p L j0 x) :=
  whc_comm _ _ (fun D x hx => glAct_wL L' j c d hx) _ x

end Formalism.CountingSumsFrames.TO

namespace Formalism.CountingSumsFrames.TO

open MvPolynomial Finset Formalism.GM.DimensionMonotonicity Formalism.GM.M

variable {p : ℕ} [Fact p.Prime] {N r : ℕ}

theorem C_stable [NeZero r] (L : Letters N) (j0 : ℕ) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ) :
    (GA p (r := r) L j0).Stable (Cset p L j0 J M) := by
  intro c d x hx
  obtain ⟨hxP, hxY⟩ := Submodule.mem_inf.mp hx
  refine Submodule.mem_inf.mpr ⟨pol_stable L (Lz L j0) j0 c d x hxP, (Submodule.mem_iInf _).mpr fun k => ?_⟩
  have h1 := (Submodule.mem_iInf _).mp hxY k
  by_cases hk : J k < j0
  · rw [Mup, if_pos hk] at h1 ⊢
    exact ycond_glAct_le L (le_of_lt hk) (M k) c d h1
  · rw [Mup, if_neg hk, Formalism.GM.DimensionMonotonicity.ycond_top]; exact Submodule.mem_top

theorem polynomial_finite_weights (L : Letters N) (j0 : ℕ) : (GA p L j0).FinW (Pol p r (Lz L j0)) :=
  pol_finW (Lz L j0) j0

end Formalism.CountingSumsFrames.TO

namespace Formalism.CountingSumsFrames.TO

open Formalism.GM.DimensionMonotonicity Finset

namespace GlX

variable {K V : Type} [Field K] [CharZero K] [AddCommGroup V] [Module K V] {r : ℕ} (G : GlW K V r)

theorem Lv_single_nil (v : V) : Lv G v (Finsupp.single [] 1) = v := by
  simp [Lv, act]

theorem Lv_zero (c : List (Fin r × Fin r) →₀ K) : Lv G (0 : V) c = 0 := by
  first
    | simp [Lv, Finsupp.linearCombination_apply]
    | simp [Lv]

theorem eqExt_core {W : Submodule K V} (hW : G.Stable W) (hWf : G.FinW W) {ι : Type} [Fintype ι] [DecidableEq ι]
    (h g : ι → V) (la : ι → Fin r → ℤ) (hh : ∀ i, G.IsHW (la i) (h i)) (hhW : ∀ i, h i ∈ W)
    (hli : LinearIndependent K h) (hsp : W ≤ ⨆ i, G.gS {h i})
    (hg : ∀ i, G.IsHW (la i) (g i)) (hgW : ∀ i, g i ∈ W) :
    ∃ φ : V →ₗ[K] V, ∀ i c, φ (Lv G (h i) c) = Lv G (g i) c := by
  have h0 : ∀ i, h i ≠ 0 := fun i => hli.ne_zero i
  have hk : ∀ i, LinearMap.ker (Lv G (h i)) ≤ LinearMap.ker (Lv G (g i)) := fun i =>
    ker_le G hW hWf (hh i) (hg i) (hhW i) (hgW i) (h0 i)
  obtain ⟨S, hS⟩ := hWf
  have hind := indep_hw G hW hS h la hh hhW hli
  have hRW : ∀ i, G.gS {h i} ≤ W := fun i => G.gS_le (by simpa using hhW i) hW
  obtain ⟨π, hπ1, hπ2, hπ3⟩ := proj_exists (fun i => G.gS {h i}) hind hRW hsp
  have hπr : ∀ i x, π i x ∈ LinearMap.range (Lv G (h i)) := fun i x => by rw [range_Lv]; exact hπ1 i x
  refine ⟨∑ i, tr G (hk i) ∘ₗ (π i).codRestrict (LinearMap.range (Lv G (h i))) (hπr i), fun i c => ?_⟩
  have hmem : Lv G (h i) c ∈ G.gS {h i} := by rw [← range_Lv]; exact LinearMap.mem_range_self _ c
  rw [LinearMap.sum_apply, Finset.sum_eq_single i]
  · rw [LinearMap.comp_apply]
    have e : (π i).codRestrict (LinearMap.range (Lv G (h i))) (hπr i) (Lv G (h i) c) =
        ⟨Lv G (h i) c, LinearMap.mem_range_self _ c⟩ := by
      ext; exact hπ2 i _ hmem
    rw [e, tr_apply]
  · intro j _ hji
    rw [LinearMap.comp_apply]
    have e : (π j).codRestrict (LinearMap.range (Lv G (h j))) (hπr j) (Lv G (h i) c) = 0 := by
      ext; exact hπ3 j i (Ne.symm hji) _ hmem
    rw [e, map_zero]
  · intro hi; exact absurd (Finset.mem_univ i) hi

theorem eqExt {W : Submodule K V} (hW : G.Stable W) (hWf : G.FinW W) {ι : Type} [Fintype ι] [DecidableEq ι]
    (h g : ι → V) (la : ι → Fin r → ℤ) (hh : ∀ i, G.IsHW (la i) (h i)) (hhW : ∀ i, h i ∈ W)
    (hli : LinearIndependent K h) (hsp : W ≤ ⨆ i, G.gS {h i})
    (hg : ∀ i, G.IsHW (la i) (g i)) (hgW : ∀ i, g i ∈ W) :
    ∃ φ : V →ₗ[K] V, (∀ i, φ (h i) = g i) ∧ (∀ x ∈ W, ∀ a b, φ (G.E a b x) = G.E a b (φ x)) ∧
      (∀ x ∈ W, φ x ∈ W) ∧ (∀ i, ∀ x ∈ G.gS {h i}, φ x ∈ G.gS {g i}) ∧
      (∀ i, g i ≠ 0 → ∀ x ∈ G.gS {h i}, φ x = 0 → x = 0) ∧
      (∀ i, g i = h i → ∀ x ∈ G.gS {h i}, φ x = x) ∧ (∀ i, g i = 0 → ∀ x ∈ G.gS {h i}, φ x = 0) := by
  obtain ⟨φ, hφ⟩ := eqExt_core G hW hWf h g la hh hhW hli hsp hg hgW
  have hrep : ∀ i, ∀ x ∈ G.gS {h i}, ∃ c, x = Lv G (h i) c := by
    intro i x hx
    rw [← range_Lv] at hx
    obtain ⟨c, rfl⟩ := hx
    exact ⟨c, rfl⟩
  have hgS : ∀ i c, Lv G (g i) c ∈ G.gS {g i} := fun i c => by
    rw [← range_Lv]; exact LinearMap.mem_range_self _ c
  refine ⟨φ, fun i => ?_, fun x hx a b => ?_, fun x hx => ?_, fun i x hx => ?_, fun i hgi x hx hx0 => ?_,
    fun i hgi x hx => ?_, fun i hgi x hx => ?_⟩
  · have := hφ i (Finsupp.single [] 1)
    rwa [Lv_single_nil, Lv_single_nil] at this
  · refine Submodule.iSup_induction (fun i => G.gS {h i}) (motive := fun x => φ (G.E a b x) = G.E a b (φ x))
      (hsp hx) (fun j y hy => ?_) (by simp) (fun x y hx hy => by simp only [map_add, hx, hy])
    obtain ⟨c, rfl⟩ := hrep j y hy
    rw [E_Lv, hφ, hφ, E_Lv]
  · refine Submodule.iSup_induction (fun i => G.gS {h i}) (motive := fun x => φ x ∈ W)
      (hsp hx) (fun j y hy => ?_) (by simp) (fun x y hx hy => by rw [map_add]; exact W.add_mem hx hy)
    obtain ⟨c, rfl⟩ := hrep j y hy
    rw [hφ]
    exact (G.gS_le (by simpa using hgW j) hW) (hgS j c)
  · obtain ⟨c, rfl⟩ := hrep i x hx
    rw [hφ]; exact hgS i c
  · obtain ⟨c, rfl⟩ := hrep i x hx
    rw [hφ] at hx0
    exact LinearMap.mem_ker.mp (ker_le G hW hWf (hg i) (hh i) (hgW i) (hhW i) hgi (LinearMap.mem_ker.mpr hx0))
  · obtain ⟨c, rfl⟩ := hrep i x hx
    rw [hφ, hgi]
  · obtain ⟨c, rfl⟩ := hrep i x hx
    rw [hφ, hgi, Lv_zero]

theorem form_zero {W : Submodule K V} (hW : G.Stable W) {ι : Type} (h : ι → V) (la : ι → Fin r → ℤ)
    (hh : ∀ i, G.IsHW (la i) (h i)) (hhW : ∀ i, h i ∈ W) (hsp : W ≤ ⨆ i, G.gS {h i})
    (B : V →ₗ[K] V →ₗ[K] K) (hB : ∀ x ∈ W, ∀ y ∈ W, ∀ a b, B (G.E a b x) y = B x (G.E b a y))
    (h0 : ∀ i j, la i = la j → B (h i) (h j) = 0) : ∀ x ∈ W, ∀ y ∈ W, B x y = 0 := by

  have h1 : ∀ i j, B (h i) (h j) = 0 := by
    intro i j
    by_cases hij : la i = la j
    · exact h0 i j hij
    · obtain ⟨c, hc⟩ : ∃ c, la i c ≠ la j c := by
        by_contra hcon; exact hij (funext fun c => by by_contra hc; exact hcon ⟨c, hc⟩)
      have e := hB (h i) (hhW i) (h j) (hhW j) c c
      rw [G.E_diag_of_isWt (hh i).1, G.E_diag_of_isWt (hh j).1, map_smul, map_smul, LinearMap.smul_apply,
        smul_eq_mul, smul_eq_mul] at e
      have e2 : (((la i c : ℤ) : K) - ((la j c : ℤ) : K)) * B (h i) (h j) = 0 := by rw [sub_mul, e, sub_self]
      rcases mul_eq_zero.mp e2 with h3 | h3
      · exfalso; apply hc
        have : ((la i c : ℤ) : K) = ((la j c : ℤ) : K) := sub_eq_zero.mp h3
        exact_mod_cast this
      · exact h3

  have h2 : ∀ i, ∀ y ∈ W, B (h i) y = 0 := by
    intro i y hy
    have hle : ∀ j, G.gS {h j} ≤ W ⊓ LinearMap.ker (B (h i)) := by
      intro j
      refine (G.gS_le_Lw (hh j)).trans (G.Lw_le (h j) ⟨hhW j, LinearMap.mem_ker.mpr (h1 i j)⟩ ?_)
      intro a b hba x hx
      refine ⟨hW a b x hx.1, LinearMap.mem_ker.mpr ?_⟩
      rw [← hB (h i) (hhW i) x hx.1 b a, (hh i).2 b a hba, map_zero, LinearMap.zero_apply]
    exact LinearMap.mem_ker.mp ((iSup_le hle) (hsp hy)).2

  let U : Submodule K V :=
    { carrier := {x | x ∈ W ∧ ∀ y ∈ W, B x y = 0}
      add_mem' := fun {x x'} hx hx' => ⟨W.add_mem hx.1 hx'.1, fun y hy => by
        rw [map_add, LinearMap.add_apply, hx.2 y hy, hx'.2 y hy, add_zero]⟩
      zero_mem' := ⟨W.zero_mem, fun y _ => by rw [map_zero, LinearMap.zero_apply]⟩
      smul_mem' := fun t x hx => ⟨W.smul_mem t hx.1, fun y hy => by
        rw [map_smul, LinearMap.smul_apply, hx.2 y hy, smul_zero]⟩ }
  have hU : G.Stable U := fun a b x hx => ⟨hW a b x hx.1, fun y hy => by
    rw [hB x hx.1 y hy a b]; exact hx.2 _ (hW b a y hy)⟩
  have hle : ∀ i, G.gS {h i} ≤ U := fun i =>
    G.gS_le (by intro z hz; rw [Set.mem_singleton_iff] at hz; subst hz; exact ⟨hhW i, h2 i⟩) hU
  intro x hx y hy
  exact ((iSup_le hle) (hsp hx)).2 y hy

end GlX

end Formalism.CountingSumsFrames.TO

namespace Formalism.CountingSumsFrames.TO

open Formalism.GM Formalism.GM.M Formalism.GM.DimensionMonotonicity MvPolynomial Finset

variable {p : ℕ} [Fact p.Prime] {N r : ℕ}

theorem isWt_iff (L : Letters N) (j : ℕ) (la : Fin r → ℤ) (x : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    (GA p L j).IsWt la x ↔ x ∈ WtSpC p L j univ la := by
  show weightedHomogeneousComponent (wv L j) la x = x ↔ _
  rw [WtSpC, mem_restrictSupport_iff]
  constructor
  · intro h m hm c _
    have hw : IsWeightedHomogeneous (wv L j) x la := by
      rw [← h]; exact weightedHomogeneousComponent_isWeightedHomogeneous la x
    rw [← weight_wv, hw (mem_support_iff.mp (Finset.mem_coe.mp hm))]
  · intro h
    apply weightedHomogeneousComponent_eq_self
    intro m hm
    funext c
    rw [weight_wv]
    exact h (Finset.mem_coe.mpr (mem_support_iff.mpr hm)) c (mem_univ c)

theorem isHW_iff (L : Letters N) (j : ℕ) (la : Fin r → ℤ) (x : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    (GA p L j).IsHW la x ↔ x ∈ HWC p L j univ la := by
  unfold GlW.IsHW HWC
  rw [isWt_iff, Submodule.mem_inf]
  simp only [Submodule.mem_iInf, LinearMap.mem_ker]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun c d hcd => h2 c d hcd.2.2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun a b hab => h2 a b ⟨mem_univ _, mem_univ _, hab⟩⟩

noncomputable def fockB (p : ℕ) [Fact p.Prime] (σ : Type) [Fintype σ] [DecidableEq σ] :
    MvPolynomial σ ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial σ ℚ_[p] →ₗ[ℚ_[p]] ℚ_[p] :=
  LinearMap.mk₂ ℚ_[p] (fun F G => fock p F G)
    (fun F F' G => gammaIntegralityLemmas.fock_add_left F F' G)
    (fun c F G => by rw [gammaIntegralityLemmas.fock_smul_left, smul_eq_mul])
    (fun F G G' => by
      rw [gammaIntegralityLemmas.fock_symm F (G + G'), gammaIntegralityLemmas.fock_add_left, gammaIntegralityLemmas.fock_symm G F, gammaIntegralityLemmas.fock_symm G' F])
    (fun c F G => by rw [gammaIntegralityLemmas.fock_smul_right, smul_eq_mul])

theorem fockB_apply {σ : Type} [Fintype σ] [DecidableEq σ] (F G : MvPolynomial σ ℚ_[p]) :
    fockB p σ F G = fock p F G := rfl

theorem fock_XD {σ : Type} [Fintype σ] [DecidableEq σ] (u v : σ) (x y : MvPolynomial σ ℚ_[p]) :
    fock p (X u * pderiv v x) y = fock p x (X v * pderiv u y) := by
  rw [gammaIntegralityLemmas.fock_X_mul, gammaIntegralityLemmas.fock_symm, ← gammaIntegralityLemmas.fock_X_mul, gammaIntegralityLemmas.fock_symm]

theorem fock_glAct (L : Letters N) (j : ℕ) (c d : Fin r) (x y : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    fock p (glAct p L j c d x) y = fock p x (glAct p L j d c y) := by
  simp only [glAct, LinearMap.sum_apply]
  rw [gammaIntegralityLemmas.fock_sum_left, gammaIntegralityLemmas.fock_sum_right]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← fockB_apply, ← fockB_apply]
  split_ifs with h1 h2
  · simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply, Derivation.coeFn_coe, fockB_apply]
    exact fock_XD _ _ _ _
  · simp only [LinearMap.neg_apply, LinearMap.comp_apply, LinearMap.mulLeft_apply, Derivation.coeFn_coe,
      map_neg, fockB_apply]
    exact congrArg Neg.neg (fock_XD _ _ _ _)
  · simp

theorem wf_add_disj (j0 : ℕ) (a m : Fin N × Fin r →₀ ℕ) (ha : ∀ v, a v ≠ 0 → fsj N r j0 v)
    (hm : ∀ v, m v ≠ 0 → ¬ fsj N r j0 v) :
    gammaIntegralityLemmas.wf (p := p) (a + m) = gammaIntegralityLemmas.wf a * gammaIntegralityLemmas.wf m := by
  unfold gammaIntegralityLemmas.wf
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun v _ => ?_
  by_cases hv : a v = 0
  · simp [hv]
  · have : m v = 0 := by
      by_contra h
      exact hm v h (ha v hv)
    simp [this]

theorem add_eq_add_iff_disj (j0 : ℕ) (a b m m' : Fin N × Fin r →₀ ℕ) (ha : ∀ v, a v ≠ 0 → fsj N r j0 v)
    (hb : ∀ v, b v ≠ 0 → fsj N r j0 v) (hm : ∀ v, m v ≠ 0 → ¬ fsj N r j0 v)
    (hm' : ∀ v, m' v ≠ 0 → ¬ fsj N r j0 v) : a + m = b + m' ↔ a = b ∧ m = m' := by
  constructor
  · intro h
    have h1 := congrArg (frst (fsj N r j0)) h
    have h2 := congrArg (ltr (fsj N r j0)) h
    rw [frst_add, frst_add, frst_of _ ha, frst_of _ hb, frst_of' _ hm, frst_of' _ hm', add_zero, add_zero] at h1
    rw [ltr_add, ltr_add, ltr_of _ ha, ltr_of _ hb, ltr_of' _ hm, ltr_of' _ hm', zero_add, zero_add] at h2
    exact ⟨h1, h2⟩
  · rintro ⟨rfl, rfl⟩
    rfl

theorem fock_mul_monomial_orthogonal (j0 : ℕ) (s t : Finset (Fin N × Fin r →₀ ℕ)) (cg cg' : (Fin N × Fin r →₀ ℕ) → ℚ_[p])
    (hs : ∀ a ∈ s, ∀ v, a v ≠ 0 → fsj N r j0 v) (ht : ∀ b ∈ t, ∀ v, b v ≠ 0 → fsj N r j0 v)
    (m m' : Fin N × Fin r →₀ ℕ) (hm : ∀ v, m v ≠ 0 → ¬ fsj N r j0 v)
    (hm' : ∀ v, m' v ≠ 0 → ¬ fsj N r j0 v) :
    fock p ((∑ a ∈ s, monomial a (cg a)) * monomial m 1) ((∑ b ∈ t, monomial b (cg' b)) * monomial m' 1) =
      if m = m' then fock p (∑ a ∈ s, monomial a (cg a)) (∑ b ∈ t, monomial b (cg' b)) *
        (m.prod fun _ k => (k.factorial : ℚ_[p])) else 0 := by
  rw [Finset.sum_mul, Finset.sum_mul, gammaIntegralityLemmas.fock_sum_left, gammaIntegralityLemmas.fock_sum_left, gammaIntegralityLemmas.prod_eq_wf]
  simp only [gammaIntegralityLemmas.fock_sum_right, monomial_mul, mul_one, gammaIntegralityLemmas.fock_monomial]
  by_cases hmm : m = m'
  · rw [if_pos hmm, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun b hb => ?_
    by_cases hab : a = b
    · rw [if_pos hab, if_pos (by rw [hab, hmm]), wf_add_disj j0 a m (hs a ha) hm]; ring
    · rw [if_neg hab, if_neg (fun h => hab ((add_eq_add_iff_disj j0 a b m m' (hs a ha) (ht b hb) hm hm').mp h).1),
        zero_mul]
  · rw [if_neg hmm]
    refine Finset.sum_eq_zero fun a ha => Finset.sum_eq_zero fun b hb => ?_
    rw [if_neg (fun h => hmm ((add_eq_add_iff_disj j0 a b m m' (hs a ha) (ht b hb) hm hm').mp h).2)]

theorem fock_mul_mono (j0 : ℕ) {g g' : MvPolynomial (Fin N × Fin r) ℚ_[p]} (hg : IsF (fsj N r j0) g)
    (hg' : IsF (fsj N r j0) g') (m m' : Fin N × Fin r →₀ ℕ) (hm : ∀ v, m v ≠ 0 → ¬ fsj N r j0 v)
    (hm' : ∀ v, m' v ≠ 0 → ¬ fsj N r j0 v) :
    fock p (g * monomial m 1) (g' * monomial m' 1) =
      if m = m' then fock p g g' * (m.prod fun _ k => (k.factorial : ℚ_[p])) else 0 := by
  have := fock_mul_monomial_orthogonal j0 g.support g'.support (fun a => coeff a g) (fun b => coeff b g')
    (fun a ha => hg a ha) (fun b hb => hg' b hb) m m' hm hm'
  rwa [← g.as_sum, ← g'.as_sum] at this

theorem fock_ext_reduce (j0 : ℕ)
    (A φ1 φ2 : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p]) (c : ℚ_[p])
    (Cs : Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]))
    (hA : ∀ g q, IsL (fsj N r j0) q → A (g * q) = A g * q)
    (hAF : ∀ g, IsF (fsj N r j0) g → IsF (fsj N r j0) (A g))
    (h1 : ∀ x, IsF (fsj N r j0) (φ1 x)) (h2 : ∀ x, IsF (fsj N r j0) (φ2 x))
    (hcore : ∀ g ∈ Cs, ∀ g' ∈ Cs, fock p (A g) (φ1 g') = c * fock p (φ2 g) g')
    (u u' : MvPolynomial (Fin N × Fin r) ℚ_[p]) (hu : ∀ m, slc (fsj N r j0) m u ∈ Cs)
    (hu' : ∀ m, slc (fsj N r j0) m u' ∈ Cs) :
    fock p (A u) (ext (fsj N r j0) φ1 u') = c * fock p (ext (fsj N r j0) φ2 u) u' := by
  classical
  set S : Finset (Fin N × Fin r →₀ ℕ) := (u.support ∪ u'.support).image (ltr (fsj N r j0)) with hS
  have hSu : ∀ m ∈ u.support, ltr (fsj N r j0) m ∈ S := fun m hm =>
    Finset.mem_image_of_mem _ (Finset.mem_union_left _ hm)
  have hSu' : ∀ m ∈ u'.support, ltr (fsj N r j0) m ∈ S := fun m hm =>
    Finset.mem_image_of_mem _ (Finset.mem_union_right _ hm)
  have hSl : ∀ m ∈ S, ∀ v, m v ≠ 0 → ¬ fsj N r j0 v := by
    intro m hm
    obtain ⟨m0, _, rfl⟩ := Finset.mem_image.mp hm
    exact ltr_isL _ m0
  have hSL : ∀ m ∈ S, IsL (fsj N r j0) (monomial m (1 : ℚ_[p])) := by
    intro m hm
    obtain ⟨m0, _, rfl⟩ := Finset.mem_image.mp hm
    exact isL_monomial_ltr _ m0 1
  have hAu : A u = ∑ m ∈ S, A (slc (fsj N r j0) m u) * monomial m 1 := by
    conv_lhs => rw [eq_sum_sl (fsj N r j0) u S hSu]
    rw [map_sum]
    exact Finset.sum_congr rfl fun m hm => hA _ _ (hSL m hm)
  rw [hAu, ext_eq_sum (fsj N r j0) φ1 u' S hSu', ext_eq_sum (fsj N r j0) φ2 u S hSu]
  conv_rhs => rw [eq_sum_sl (fsj N r j0) u' S hSu']
  rw [gammaIntegralityLemmas.fock_sum_left, gammaIntegralityLemmas.fock_sum_left, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [gammaIntegralityLemmas.fock_sum_right, gammaIntegralityLemmas.fock_sum_right, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m' hm' => ?_
  rw [fock_mul_mono j0 (hAF _ (sl_isF _ m u)) (h1 _) m m' (hSl m hm) (hSl m' hm'),
    fock_mul_mono j0 (h2 _) (sl_isF _ m' u') m m' (hSl m hm) (hSl m' hm')]
  split_ifs with h
  · rw [hcore _ (hu m) _ (hu' m')]; ring
  · simp

end Formalism.CountingSumsFrames.TO

namespace Formalism.CountingSumsFrames.TO

open Formalism.GM Formalism.GM.M Formalism.GM.DimensionMonotonicity MvPolynomial Finset

section OpsAux

variable {k σ : Type} [Field k]

theorem tiePhi_mem' {r : ℕ} (w e : Fin r → σ) (o n z : ℕ) :
    (Formalism.GM.tiePhi w e o n z : Module.End k (MvPolynomial σ k)) ∈ FockB.Ops (Set.range w ∪ Set.range e) := by
  unfold Formalism.GM.tiePhi
  refine sum_mem fun j _ => Subalgebra.smul_mem _ ?_ _
  rw [← Module.End.mul_eq_comp]
  refine mul_mem (pow_mem ?_ _) (pow_mem ?_ _)
  · exact FockB.mulLeft_mem (sum_mem fun c _ => mul_mem (FockB.X_mem (Or.inl ⟨c, rfl⟩))
      (FockB.X_mem (Or.inr ⟨c, rfl⟩)))
  · unfold Formalism.GM.tieF
    refine sum_mem fun c _ => ?_
    rw [← Module.End.mul_eq_comp]
    exact mul_mem (FockB.pderiv_mem (Or.inl ⟨c, rfl⟩)) (FockB.pderiv_mem (Or.inr ⟨c, rfl⟩))

theorem ops_mul_free (S : Set σ) {T : Module.End k (MvPolynomial σ k)} (hT : T ∈ FockB.Ops S)
    (q : MvPolynomial σ k) (hq : ∀ m ∈ q.support, ∀ v ∈ S, m v = 0) (g : MvPolynomial σ k) :
    T (g * q) = T g * q := by
  have hc : Commute (LinearMap.mulRight k q : Module.End k (MvPolynomial σ k)) T := by
    refine Algebra.commute_of_mem_adjoin_of_forall_mem_commute hT (fun b hb => ?_)
    obtain ⟨u, hu, rfl | rfl⟩ := hb
    · rw [commute_iff_eq]
      refine LinearMap.ext fun f => ?_
      simp only [Module.End.mul_apply, LinearMap.mulLeft_apply, LinearMap.mulRight_apply]
      ring
    · rw [commute_iff_eq]
      refine LinearMap.ext fun f => ?_
      simp only [Module.End.mul_apply, LinearMap.mulRight_apply, Derivation.coeFn_coe]
      rw [pderiv_mul, ProjS.pderiv_of_free u q (fun m hm => hq m hm u hu), mul_zero, add_zero]
  have := LinearMap.congr_fun hc.eq g
  simp only [Module.End.mul_apply, LinearMap.mulRight_apply] at this
  exact this.symm

theorem ops_keep_pred (S : Set σ) (P : σ → Prop) (hS : ∀ v ∈ S, P v) {T : Module.End k (MvPolynomial σ k)}
    (hT : T ∈ FockB.Ops S) (g : MvPolynomial σ k) (hg : ∀ m ∈ g.support, ∀ v, m v ≠ 0 → P v) :
    ∀ m ∈ (T g).support, ∀ v, m v ≠ 0 → P v := by
  have h1 := ops_keep_supp S {m : σ →₀ ℕ | ∀ v, m v ≠ 0 → P v} (fun m m' h hm v hv => by
    by_cases hvS : v ∈ S
    · exact hS v hvS
    · exact hm v (by rw [h v hvS]; exact hv)) hT g (by
      rw [mem_restrictSupport_iff]
      intro m hm
      exact hg m (Finset.mem_coe.mp hm))
  rw [mem_restrictSupport_iff] at h1
  intro m hm
  exact h1 (Finset.mem_coe.mpr hm)

theorem ext_ops_comm [DecidableEq σ] (fs : σ → Prop) [DecidablePred fs] (S : Set σ) (hS : ∀ v ∈ S, ¬ fs v)
    {T : Module.End k (MvPolynomial σ k)} (hT : T ∈ FockB.Ops S)
    (φ : MvPolynomial σ k →ₗ[k] MvPolynomial σ k) (hφ : ∀ x, IsF fs (φ x)) (x : MvPolynomial σ k) :
    ext fs φ (T x) = T (ext fs φ x) := by
  have hfree : ∀ g : MvPolynomial σ k, IsF fs g → ∀ m ∈ g.support, ∀ v ∈ S, m v = 0 := by
    intro g hg m hm v hv
    by_contra h
    exact hS v hv (hg m hm v h)
  induction x using MvPolynomial.induction_on' with
  | monomial m a =>
    rw [monomial_split fs m a]
    have hg := isF_monomial_frst (K := k) fs m a
    have hq := isL_monomial_ltr (K := k) fs m 1
    have hTq : IsL fs (T (monomial (ltr fs m) 1)) := ops_keep_pred S (fun v => ¬ fs v) hS hT _ hq
    have e1 : T (monomial (frst fs m) a * monomial (ltr fs m) 1) = monomial (frst fs m) a * T (monomial (ltr fs m) 1) := by
      rw [mul_comm, ops_mul_free S hT _ (hfree _ hg), mul_comm]
    have e2 : T (φ (monomial (frst fs m) a) * monomial (ltr fs m) 1) =
        φ (monomial (frst fs m) a) * T (monomial (ltr fs m) 1) := by
      rw [mul_comm, ops_mul_free S hT _ (hfree _ (hφ _)), mul_comm]
    rw [ext_mul fs φ hg hq, e1, ext_mul fs φ hg hTq, e2]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem tieE_rename {τ : Type} {r : ℕ} (ι : σ → τ) (w e : Fin r → σ) (F : MvPolynomial σ k) :
    Formalism.GM.tieE (fun c => ι (w c)) (fun c => ι (e c)) (rename ι F) = rename ι (Formalism.GM.tieE w e F) := by
  simp only [Formalism.GM.tieE, LinearMap.mulLeft_apply, map_mul, map_sum, rename_X]

theorem tieF_rename {τ : Type} {r : ℕ} (ι : σ → τ) (hι : Function.Injective ι) (w e : Fin r → σ)
    (F : MvPolynomial σ k) :
    Formalism.GM.tieF (fun c => ι (w c)) (fun c => ι (e c)) (rename ι F) = rename ι (Formalism.GM.tieF w e F) := by
  simp only [Formalism.GM.tieF, LinearMap.sum_apply, LinearMap.comp_apply, Derivation.coeFn_coe, map_sum,
    pderiv_rename hι]

theorem tiePhi_rename {τ : Type} {r : ℕ} (ι : σ → τ) (hι : Function.Injective ι) (w e : Fin r → σ) (o n z : ℕ)
    (F : MvPolynomial σ k) :
    Formalism.GM.tiePhi (fun c => ι (w c)) (fun c => ι (e c)) o n z (rename ι F) =
      rename ι (Formalism.GM.tiePhi w e o n z F) := by
  have hE : ∀ (j : ℕ) (G : MvPolynomial σ k),
      ((Formalism.GM.tieE (fun c => ι (w c)) (fun c => ι (e c))) ^ j) (rename ι G) =
        rename ι (((Formalism.GM.tieE w e) ^ j) G) := by
    intro j
    induction j with
    | zero => intro G; simp
    | succ j ih => intro G; rw [pow_succ, Module.End.mul_apply, tieE_rename, ih, pow_succ, Module.End.mul_apply]
  have hF : ∀ (j : ℕ) (G : MvPolynomial σ k),
      ((Formalism.GM.tieF (fun c => ι (w c)) (fun c => ι (e c))) ^ j) (rename ι G) =
        rename ι (((Formalism.GM.tieF w e) ^ j) G) := by
    intro j
    induction j with
    | zero => intro G; simp
    | succ j ih => intro G; rw [pow_succ, Module.End.mul_apply, tieF_rename ι hι, ih, pow_succ, Module.End.mul_apply]
  simp only [Formalism.GM.tiePhi, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply, map_sum, hF, hE]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← AlgHom.toLinearMap_apply (rename ι), map_smul]
  rfl

end OpsAux

variable {p : ℕ} [Fact p.Prime] {N r : ℕ}

theorem fock_rename {σ τ : Type} (ι : σ → τ) (hι : Function.Injective ι) (F F' : MvPolynomial σ ℚ_[p]) :
    fock p (rename ι F) (rename ι F') = fock p F F' := by
  classical
  unfold fock
  rw [support_rename_of_injective hι, Finset.sum_image (fun a _ b _ h => Finsupp.mapDomain_injective hι h)]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [coeff_rename_mapDomain ι hι, coeff_rename_mapDomain ι hι, Finsupp.prod_mapDomain_index_inj hι]

theorem fock_nondeg {σ : Type} (z : MvPolynomial σ ℚ_[p]) (h : ∀ y, fock p z y = 0) : z = 0 := by
  by_contra hz
  obtain ⟨m, hm⟩ : ∃ m, m ∈ z.support := by
    by_contra hc; push Not at hc
    exact hz (MvPolynomial.support_eq_empty.mp (Finset.eq_empty_of_forall_notMem hc))
  have h1 := Formalism.CountingSumsFrames.fock_monomial z m hm
  rw [h] at h1
  have h2 : (m.prod fun _ k => (k.factorial : ℚ_[p])) ≠ 0 := by
    rw [Finsupp.prod]
    exact Finset.prod_ne_zero_iff.mpr fun v _ => by exact_mod_cast Nat.factorial_ne_zero _
  exact (mul_ne_zero (mem_support_iff.mp hm) h2) h1.symm

theorem phi_mem' (L : Letters N) (T : TieData) (j : Fin T.t) (h : T.pos j + 1 < N) :
    (T.phi p L j : Module.End ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p])) ∈
      FockB.Ops {v : Fin N × Fin r | (v.1 : ℕ) = T.pos j ∨ (v.1 : ℕ) = T.pos j + 1} := by
  unfold TieData.phi
  rw [dif_pos h]
  unfold tiePhiAt
  refine FockB.ops_mono ?_ (tiePhi_mem' _ _ _ _ _)
  rintro v (⟨c, rfl⟩ | ⟨c, rfl⟩)
  · left; rfl
  · right; rfl

section Comparison₂

variable (L : Letters N) (T : TieData) (hadm : T.Admissible L) (i : Fin T.t)

include hadm

theorem phi_mul_later (g q : MvPolynomial (Fin N × Fin r) ℚ_[p]) (hq : IsL (fsj N r (T.pos i + 1 + 1)) q) :
    T.phi p L i (g * q) = T.phi p L i g * q := by
  have hK := hK_of_adm L T hadm i
  refine ops_mul_free _ (phi_mem' L T i (by omega)) q (fun m hm v hv => ?_) g
  by_contra h
  have := hq m hm v h
  simp only [fsj] at this
  rcases hv with hv | hv <;> omega

theorem phi_isF (g : MvPolynomial (Fin N × Fin r) ℚ_[p]) (hg : IsF (fsj N r (T.pos i + 1 + 1)) g) :
    IsF (fsj N r (T.pos i + 1 + 1)) (T.phi p L i g) := by
  have hK := hK_of_adm L T hadm i
  refine ops_keep_pred _ (fsj N r (T.pos i + 1 + 1)) (fun v hv => ?_) (phi_mem' L T i (by omega)) g hg
  simp only [fsj]
  rcases hv with hv | hv <;> omega

theorem phi_glAct (c d : Fin r) (x : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    T.phi p L i (glAct p L (T.pos i + 1 + 1) c d x) = glAct p L (T.pos i + 1 + 1) c d (T.phi p L i x) := by
  classical
  obtain ⟨h, hva, hvb⟩ := hadm.2.1 i
  set a : Fin N := ⟨T.pos i, by omega⟩ with ha
  set b : Fin N := ⟨T.pos i + 1, h⟩ with hb
  have hE : ∀ (c d : Fin r) (y : MvPolynomial (Fin N × Fin r) ℚ_[p]),
      glAct p L (T.pos i + 1 + 1) c d (Formalism.GM.tieE (fun c : Fin r => (a, c)) (fun c : Fin r => (b, c)) y) =
        Formalism.GM.tieE (fun c : Fin r => (a, c)) (fun c : Fin r => (b, c)) (glAct p L (T.pos i + 1 + 1) c d y) := by
    intro c d y
    simp only [Formalism.GM.tieE, LinearMap.mulLeft_apply]
    rw [Formalism.GM.M.FB.glAct_mul]
    have h0 : glAct p L (T.pos i + 1 + 1) c d (∑ e : Fin r, X (a, e) * X (b, e)) = 0 := by
      rw [map_sum]
      have : ∀ e : Fin r, glAct p L (T.pos i + 1 + 1) c d (X (a, e) * X (b, e)) =
          (if e = c then -(X (a, c) * X (b, d)) else 0) + (if e = d then X (a, c) * X (b, d) else 0) := by
        intro e
        have hXa : glAct p L (T.pos i + 1 + 1) c d (X (a, e)) = if e = d then X (a, c) else 0 := by
          rw [glAct_X_gen, if_pos (show (a : ℕ) < T.pos i + 1 + 1 by show T.pos i < _; omega), hva]; simp
        have hXb : glAct p L (T.pos i + 1 + 1) c d (X (b, e)) = if e = c then -X (b, d) else 0 := by
          rw [glAct_X_gen, if_pos (show (b : ℕ) < T.pos i + 1 + 1 by show T.pos i + 1 < _; omega), hvb]; simp
        rw [Formalism.GM.M.FB.glAct_mul, hXa, hXb]
        split_ifs with h1 h2 h2
        · subst h1; subst h2; ring
        · subst h1; ring
        · subst h2; ring
        · ring
      simp only [this, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      ring
    rw [h0, mul_zero, add_zero]
  have hF : ∀ (c d : Fin r) (y : MvPolynomial (Fin N × Fin r) ℚ_[p]),
      glAct p L (T.pos i + 1 + 1) c d (Formalism.GM.tieF (fun c : Fin r => (a, c)) (fun c : Fin r => (b, c)) y) =
        Formalism.GM.tieF (fun c : Fin r => (a, c)) (fun c : Fin r => (b, c)) (glAct p L (T.pos i + 1 + 1) c d y) := by
    intro c d y
    rw [← sub_eq_zero]
    apply fock_nondeg
    intro u
    rw [gammaIntegralityLemmas.fock_symm, sub_eq_add_neg, gammaIntegralityLemmas.fock_symm, gammaIntegralityLemmas.fock_add_left, ← neg_one_smul ℚ_[p],
      gammaIntegralityLemmas.fock_smul_left, fock_glAct, gammaIntegralityLemmas.fock_symm _ (glAct p L (T.pos i + 1 + 1) d c u),
      ← gammaIntegralityLemmas.fock_E, ← hE, gammaIntegralityLemmas.fock_symm, ← fock_glAct,
      gammaIntegralityLemmas.fock_symm (Formalism.GM.tieF _ _ _) u, ← gammaIntegralityLemmas.fock_E, gammaIntegralityLemmas.fock_symm _ (Formalism.GM.tieE _ _ u)]
    ring
  have cE : Commute (glAct p L (T.pos i + 1 + 1) c d : Module.End ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]))
      (Formalism.GM.tieE (fun c : Fin r => (a, c)) (fun c : Fin r => (b, c))) := by
    rw [commute_iff_eq]; exact LinearMap.ext fun y => hE c d y
  have cF : Commute (glAct p L (T.pos i + 1 + 1) c d : Module.End ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]))
      (Formalism.GM.tieF (fun c : Fin r => (a, c)) (fun c : Fin r => (b, c))) := by
    rw [commute_iff_eq]; exact LinearMap.ext fun y => hF c d y
  have cP : Commute (glAct p L (T.pos i + 1 + 1) c d : Module.End ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]))
      (T.phi p L i) := by
    unfold TieData.phi
    rw [dif_pos h]
    unfold tiePhiAt Formalism.GM.tiePhi
    refine Commute.sum_right _ _ _ fun j _ => Commute.smul_right ?_ _
    rw [← Module.End.mul_eq_comp]
    exact (cE.pow_right j).mul_right (cF.pow_right j)
  exact (LinearMap.congr_fun cP.eq x).symm

theorem phi_ext_comm (j : Fin T.t) (hij : i < j)
    (φ : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hφ : ∀ x, IsF (fsj N r (T.pos i + 1 + 1)) (φ x)) (x : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    ext (fsj N r (T.pos i + 1 + 1)) φ (T.phi p L j x) = T.phi p L j (ext (fsj N r (T.pos i + 1 + 1)) φ x) := by
  have hK := hK_of_adm L T hadm j
  have hlt : T.pos i < T.pos j := hadm.1 hij
  have hne : T.pos j ≠ T.pos i + 1 := by
    intro he
    obtain ⟨h1, -, hb⟩ := hadm.2.1 i
    obtain ⟨h2, ha, -⟩ := hadm.2.1 j
    have : (⟨T.pos j, by omega⟩ : Fin N) = ⟨T.pos i + 1, h1⟩ := Fin.ext he
    rw [this, hb] at ha
    exact Bool.false_ne_true ha
  refine ext_ops_comm (fsj N r (T.pos i + 1 + 1)) _ (fun v hv => ?_) (phi_mem' L T j (by omega)) φ hφ x
  simp only [fsj]
  rcases hv with hv | hv <;> omega

end Comparison₂

section Tie2

variable [NeZero N] (LL : Letters N) (T : TieData) (hadm : T.Admissible LL) (i : Fin T.t)

include hadm

theorem fock_Ffull (ρ : Fin r) (n : Fin T.t → ℕ) (f f' : MvPolynomial (Fin (T.pos i + 1) × Fin r) ℚ_[p]) :
    fock p (T.Ffull p (LL.setTies T n) i ρ (n i) f) (T.Ffull p (LL.setTies T n) i ρ (n i) f') =
      fock p (freeze p ((LL.setTies T n).takeD (T.pos i + 1)) ρ (n i) f)
        (freeze p ((LL.setTies T n).takeD (T.pos i + 1)) ρ (n i) f') := by
  rw [Ffull_eq, Ffull_eq]
  exact fock_rename _ (inclusion_prodMap_injective (hK_of_adm LL T hadm i)) _ _

theorem phi_Ffull (ρ : Fin r) (n : Fin T.t → ℕ) (f : MvPolynomial (Fin (T.pos i + 1) × Fin r) ℚ_[p]) :
    T.phi p (LL.setTies T n) i (T.Ffull p (LL.setTies T n) i ρ (n i) f) =
      rename (fun x : Fin (T.pos i + 1 + 1) × Fin r => (ιF N (T.pos i + 1) x.1, x.2))
        (tiePhiAt p (((LL.setTies T n).takeD (T.pos i + 1)).snoc (n i)) (Fin.castSucc (Fin.last (T.pos i)))
          (Fin.last (T.pos i + 1)) (T.z i) (freeze p ((LL.setTies T n).takeD (T.pos i + 1)) ρ (n i) f)) := by
  have hK := hK_of_adm LL T hadm i
  have h : T.pos i + 1 < N := by omega
  rw [Ffull_eq]
  unfold TieData.phi
  rw [dif_pos h]
  unfold tiePhiAt
  rw [← tiePhi_rename _ (inclusion_prodMap_injective hK)]
  have e1 : ιF N (T.pos i + 1) (Fin.castSucc (Fin.last (T.pos i))) = ⟨T.pos i, by omega⟩ := by
    apply Fin.ext; rw [ιF_val hK]; simp
  have e2 : ιF N (T.pos i + 1) (Fin.last (T.pos i + 1)) = ⟨T.pos i + 1, h⟩ := by
    apply Fin.ext; rw [ιF_val hK]; simp
  have d1 : (((LL.setTies T n).takeD (T.pos i + 1)).snoc (n i)).deg (Fin.castSucc (Fin.last (T.pos i))) =
      (LL.setTies T n).deg ⟨T.pos i, by omega⟩ := by
    rw [Formalism.GM.FrozenVariableComponents.snoc_deg_castSucc]
    simp [Letters.takeD, (by omega : T.pos i < N)]
  have d2 : (((LL.setTies T n).takeD (T.pos i + 1)).snoc (n i)).deg (Fin.last (T.pos i + 1)) =
      (LL.setTies T n).deg ⟨T.pos i + 1, h⟩ := by
    rw [Formalism.GM.FrozenVariableComponents.snoc_deg_last, setTies_deg_eta LL T hadm i n h]
  rw [d1, d2]
  simp only [e1, e2]

theorem gam_eq (ρ : Fin r) (n : Fin T.t → ℕ) (f f' : MvPolynomial (Fin (T.pos i + 1) × Fin r) ℚ_[p]) :
    tieGam p ((LL.setTies T n).takeD (T.pos i + 1)) ρ (T.z i) (n i) f f' =
      (((((LL.setTies T n).takeD (T.pos i + 1)).deg (Fin.last (T.pos i)) + n i + r + T.z i - 1).choose
          (((LL.setTies T n).takeD (T.pos i + 1)).deg (Fin.last (T.pos i))) : ℕ) : ℚ_[p]) *
        fock p (T.phi p (LL.setTies T n) i (T.Ffull p (LL.setTies T n) i ρ (n i) f))
          (T.Ffull p (LL.setTies T n) i ρ (n i) f') /
        ((((n i - ((LL.setTies T n).takeD (T.pos i + 1)).total).factorial *
            ((LL.setTies T n).takeD (T.pos i + 1)).total.factorial : ℕ) : ℚ_[p]) *
          ∏ x, ((((LL.setTies T n).takeD (T.pos i + 1)).deg x).factorial : ℚ_[p])) := by
  rw [phi_Ffull LL T hadm i ρ n f, Ffull_eq, fock_rename _ (inclusion_prodMap_injective (hK_of_adm LL T hadm i))]
  rfl

end Tie2

end Formalism.CountingSumsFrames.TO

namespace Formalism.CountingSumsFrames.TO

open Formalism.GM Formalism.GM.M MvPolynomial Finset

variable {p : ℕ} [Fact p.Prime]

theorem gamma_zero_exponent_le (K r a : ℕ) (hr : 1 ≤ r) (κ : ℝ) (hκ : ((K + 3) * r ^ 2 : ℝ) * lgV2 p a r ≤ κ) :
    (K + 2) * (r * Nat.log p (2 * a)) ≤ ⌈κ⌉₊ := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have ha0 : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  have hlog : (Nat.log p (2 * a) : ℝ) ≤ lgV2 p a r := by
    unfold lgV2
    have h0 : 0 ≤ Real.logb p (8 * a + r) := Real.logb_nonneg hp1 (by linarith)
    by_cases ha : a = 0
    · have hz : Nat.log p (2 * a) = 0 := by rw [ha]; simp
      rw [hz, Nat.cast_zero]
      linarith
    · have h1 : (Nat.log p (2 * a) : ℝ) ≤ Real.logb p ((2 * a : ℕ) : ℝ) := Real.natLog_le_logb _ _
      have hapos : (0 : ℝ) < a := by exact_mod_cast Nat.pos_of_ne_zero ha
      have h2 : Real.logb p ((2 * a : ℕ) : ℝ) ≤ Real.logb p (8 * a + r) := by
        apply Real.logb_le_logb_of_le hp1
        · push_cast; linarith
        · push_cast; linarith
      linarith
  have hl0 : (0 : ℝ) ≤ (Nat.log p (2 * a) : ℝ) := Nat.cast_nonneg _
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  have h3 : (((K + 2) * (r * Nat.log p (2 * a)) : ℕ) : ℝ) ≤ κ := by
    push_cast
    calc ((K : ℝ) + 2) * ((r : ℝ) * (Nat.log p (2 * a) : ℝ))
        ≤ ((K : ℝ) + 3) * ((r : ℝ) ^ 2 * lgV2 p a r) := by
          apply mul_le_mul (by linarith) _ (by positivity) (by positivity)
          apply mul_le_mul _ hlog hl0 (by positivity)
          nlinarith
      _ = ((K + 3) * r ^ 2 : ℝ) * lgV2 p a r := by ring
      _ ≤ κ := hκ
  exact_mod_cast h3.trans (Nat.le_ceil κ)

theorem gamma_zero_integral_alt (K r : ℕ) (LLw : Letters (K + 1)) (ρ : Fin r) (n a : ℕ) (κ : ℝ)
    (hS : LLw.total ≤ n) (hn : n ≤ 2 * a) (hκ : ((K + 3) * r ^ 2 : ℝ) * lgV2 p a r ≤ κ)
    (f f' : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) (hf : f ∈ PolZ p r LLw) (hf' : f' ∈ PolZ p r LLw) :
    ‖(p : ℚ_[p]) ^ ⌈κ⌉₊ * (fock p (freeze p LLw ρ n f) (freeze p LLw ρ n f') /
      ((((n - LLw.total).factorial * LLw.total.factorial : ℕ) : ℚ_[p]) *
        ∏ i, ((LLw.deg i).factorial : ℚ_[p])))‖ ≤ 1 := by
  classical
  have hr : 1 ≤ r := Nat.one_le_iff_ne_zero.mpr (fun h => by subst h; exact ρ.elim0)
  obtain ⟨hfP, hfI⟩ := Submodule.mem_inf.mp hf
  obtain ⟨hfP', hfI'⟩ := Submodule.mem_inf.mp hf'
  obtain ⟨hFP, -, hFI⟩ := Formalism.GM.extendMapsTo p (K + 1) r LLw ρ n hS f hfP
  obtain ⟨-, -, hFI'⟩ := Formalism.GM.extendMapsTo p (K + 1) r LLw ρ n hS f' hfP'
  set F := freeze p LLw ρ n f with hF
  set F' := freeze p LLw ρ n f' with hF'
  have hc := gammaIntegralityLemmas.intPol_coeff F (hFI hfI)
  have hc' := gammaIntegralityLemmas.intPol_coeff F' (hFI' hfI')
  set Den : ℕ := ((n - LLw.total).factorial * LLw.total.factorial) * ∏ i, (LLw.deg i).factorial with hDen
  have hDen0 : Den ≠ 0 := by
    rw [hDen]
    exact Nat.mul_ne_zero (Nat.mul_ne_zero (Nat.factorial_pos _).ne' (Nat.factorial_pos _).ne')
      (Finset.prod_ne_zero_iff.mpr fun i _ => (Nat.factorial_pos _).ne')
  have hDcast : ((((n - LLw.total).factorial * LLw.total.factorial : ℕ) : ℚ_[p]) *
        ∏ i, ((LLw.deg i).factorial : ℚ_[p])) = (Den : ℚ_[p]) := by
    rw [hDen]; push_cast; ring
  rw [hDcast, gammaIntegralityLemmas.fock_def', Finset.sum_div, Finset.mul_sum]
  refine gammaIntegralityLemmas.norm_sum_le_bound _ _ 1 zero_le_one ?_
  intro m hm
  have hmd : MultiDeg (LLw.snoc n) m := by
    rw [Pol, mem_restrictSupport_iff] at hFP
    exact hFP (Finset.mem_coe.mpr hm)
  set Num : ℕ := ∏ v : Fin (K + 1 + 1) × Fin r, (m v).factorial with hNum
  have hNum0 : Num ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => (Nat.factorial_pos _).ne'
  have hwf : gammaIntegralityLemmas.wf (p := p) m = (Num : ℚ_[p]) := by
    rw [hNum, gammaIntegralityLemmas.wf]; push_cast; rfl
  rw [hwf]
  have hδ : ∀ i, gammaIntegralityLemmas.δv m i = (LLw.snoc n).deg i := fun i => hmd i
  have hT : ∀ i, gammaIntegralityLemmas.δv m i ≤ 2 * a := by
    intro i
    rw [hδ]
    refine Fin.lastCases ?_ (fun i => ?_) i
    · rw [FrozenVariableComponents.snoc_deg_last]; exact hn
    · rw [FrozenVariableComponents.snoc_deg_castSucc]
      exact (gammaIntegralityLemmas.deg_le_total LLw i).trans (hS.trans hn)
  have h1 := gammaIntegralityLemmas.vW_ge (p := p) m (T := 2 * a) (B := Nat.log p (2 * a)) le_rfl hT
  rw [Fin.sum_univ_castSucc] at h1
  simp only [hδ, FrozenVariableComponents.snoc_deg_last, FrozenVariableComponents.snoc_deg_castSucc] at h1
  have h2 : padicValNat p Den = padicValNat p (n - LLw.total).factorial + padicValNat p LLw.total.factorial +
      ∑ i, padicValNat p (LLw.deg i).factorial := by
    rw [hDen, padicValNat.mul (Nat.mul_ne_zero (Nat.factorial_pos _).ne' (Nat.factorial_pos _).ne')
      (Finset.prod_ne_zero_iff.mpr fun i _ => (Nat.factorial_pos _).ne'),
      padicValNat.mul (Nat.factorial_pos _).ne' (Nat.factorial_pos _).ne',
      gammaIntegralityLemmas.v_prod _ _ (fun i _ => (Nat.factorial_pos _).ne')]
  have h3 : padicValNat p (n - LLw.total).factorial + padicValNat p LLw.total.factorial ≤
      padicValNat p n.factorial := by
    have e := Nat.choose_mul_factorial_mul_factorial hS
    rw [← e, padicValNat.mul (Nat.mul_ne_zero (Nat.choose_pos hS).ne' (Nat.factorial_pos _).ne')
      (Nat.factorial_pos _).ne', padicValNat.mul (Nat.choose_pos hS).ne' (Nat.factorial_pos _).ne']
    omega
  have h4 := gamma_zero_exponent_le (p := p) K r a hr κ hκ
  have h5 := gammaIntegralityLemmas.norm_K (p := p) ⌈κ⌉₊ (coeff m F) (coeff m F') 0 0 (by simpa using hc m) (by simpa using hc' m)
    Num Den hNum0 hDen0 1 norm_one (by
      have : (padicValNat p Den : ℤ) ≤ (padicValNat p Num : ℤ) + (⌈κ⌉₊ : ℤ) := by
        have : padicValNat p Den ≤ padicValNat p Num + ⌈κ⌉₊ := by
          rw [h2]
          have h1' : ∑ i, padicValNat p (LLw.deg i).factorial + padicValNat p n.factorial ≤
              padicValNat p Num + (K + 2) * (r * Nat.log p (2 * a)) := h1
          omega
        exact_mod_cast this
      omega)
  rw [one_mul] at h5
  exact h5

end Formalism.CountingSumsFrames.TO

namespace Formalism.CountingSumsFrames.TO

open Formalism.GM Formalism.GM.M Formalism.GM.DimensionMonotonicity MvPolynomial Finset

variable {p : ℕ} [Fact p.Prime] {N r : ℕ}

structure IsProjC [NeZero r] (L : Letters N) (j0 e : ℕ) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ)
    (Pi : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p]) : Prop where
  comm : ∀ c d x, Pi (glAct p L j0 c d x) = glAct p L j0 c d (Pi x)
  wh : ∀ ν x, x ∈ weightedHomogeneousSubmodule ℚ_[p] (wv L j0) ν →
    Pi x ∈ weightedHomogeneousSubmodule ℚ_[p] (wv L j0) ν
  pol : ∀ L' : Letters N, L'.vec = L.vec → ∀ x ∈ Pol p r L', Pi x ∈ Pol p r L'
  ycond : ∀ x k, Pi x ∈ YCond p L (J k) (Mup J M j0 k)
  fix : ∀ L' : Letters N, L'.vec = L.vec → ∀ x ∈ Pol p r L', (∀ k, x ∈ YCond p L (J k) (Mup J M j0 k)) → Pi x = x
  int : ∀ x ∈ PolZ p r L, ((p : ℚ_[p]) ^ e) • Pi x ∈ IntPol p (Fin N × Fin r)
  mul : ∀ g q, IsL (fsj N r j0) q → Pi (g * q) = Pi g * q

theorem wtsp_iff_wh (L : Letters N) (j : ℕ) (μ : Fin r → ℤ) (x : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    x ∈ WtSpC p L j univ μ ↔ x ∈ weightedHomogeneousSubmodule ℚ_[p] (wv L j) μ := by
  rw [WtSpC, mem_restrictSupport_iff, mem_weightedHomogeneousSubmodule]
  constructor
  · intro h m hm
    funext c
    rw [weight_wv]
    exact h (Finset.mem_coe.mpr (mem_support_iff.mpr hm)) c (Finset.mem_univ c)
  · intro h m hm c _
    rw [← weight_wv, h (mem_support_iff.mp (Finset.mem_coe.mp hm))]

theorem hwc_keep (L : Letters N) (j : ℕ) (la : Fin r → ℤ)
    (Q : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hc : ∀ c d x, Q (glAct p L j c d x) = glAct p L j c d (Q x)) :
    ∀ x ∈ HWC p L j univ la, Q x ∈ HWC p L j univ la := by
  intro x hx
  obtain ⟨h1, h2⟩ := Submodule.mem_inf.mp hx
  refine Submodule.mem_inf.mpr ⟨comm_wtsp L j Q (fun c x => hc c c x) la x h1, ?_⟩
  simp only [Submodule.mem_iInf, LinearMap.mem_ker] at h2 ⊢
  intro c d hcd
  rw [← hc, h2 c d hcd, map_zero]

theorem iso_keep_comm (L : Letters N) (j : ℕ)
    (Q : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hc : ∀ c d x, Q (glAct p L j c d x) = glAct p L j c d (Q x)) (la : Fin r → ℤ) :
    ∀ x ∈ IsoC p L j univ la, Q x ∈ IsoC p L j univ la :=
  isoC_keep L j la Q hc (hwc_keep L j la Q hc)

theorem iso_keep_glAct (L : Letters N) {j j0 : ℕ} (hj : j ≤ j0) (c d : Fin r) (la : Fin r → ℤ) :
    ∀ x ∈ IsoC p L j univ la, glAct p L j0 c d x ∈ IsoC p L j univ la := by
  intro x hx
  rw [glAct_split L hj c d, LinearMap.add_apply]
  exact Submodule.add_mem _ (isoC_glStable L j la c d x hx)
    (iso_keep_comm L j (midAct p L j j0 c d) (fun c' d' y => midAct_comm L j j0 c d c' d' y) la x hx)

theorem iso_keep_mul (L : Letters N) {j j0 : ℕ} (hj : j ≤ j0) {q : MvPolynomial (Fin N × Fin r) ℚ_[p]}
    (hq : IsL (fsj N r j0) q) (la : Fin r → ℤ) :
    ∀ x ∈ IsoC p L j univ la, LinearMap.mulRight ℚ_[p] q x ∈ IsoC p L j univ la :=
  iso_keep_comm L j (LinearMap.mulRight ℚ_[p] q) (fun c d x => by
    simp only [LinearMap.mulRight_apply]
    exact (glAct_mul_kill L j c d x (killL_of_isL hj hq)).symm) la

theorem isTypeProj_congr (L L' : Letters N) (h : L'.vec = L.vec) (j : ℕ) (Cs : Finset (Fin r)) (T : Set (Fin r → ℤ))
    (P : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hP : IsTypeProj p L j Cs T P) : IsTypeProj p L' j Cs T P := by
  obtain ⟨v, d⟩ := L
  obtain ⟨v', d'⟩ := L'
  simp only at h
  subst h
  exact hP

theorem ycond_congr [NeZero r] (L L' : Letters N) (h : L'.vec = L.vec) (j : ℕ) (Mt : WithTop ℤ) :
    YCond p (r := r) L' j Mt = YCond p (r := r) L j Mt := by
  obtain ⟨v, d⟩ := L
  obtain ⟨v', d'⟩ := L'
  simp only at h
  subst h
  rfl

theorem lcomp_fixed {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V] [LinearOrder ι] (P : ι → V →ₗ[K] V)
    (x : V) (hx : ∀ j, P j x = x) : ∀ l : List ι, lcomp P l x = x
  | [] => rfl
  | a :: l => by rw [lcomp_cons, LinearMap.comp_apply, lcomp_fixed P x hx l, hx a]

theorem lcomp_commQ {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V] [LinearOrder ι] (P : ι → V →ₗ[K] V)
    (Q : V →ₗ[K] V) (h : ∀ j x, P j (Q x) = Q (P j x)) : ∀ (l : List ι) (x : V), lcomp P l (Q x) = Q (lcomp P l x)
  | [], _ => rfl
  | a :: l, x => by
    rw [lcomp_cons, LinearMap.comp_apply, LinearMap.comp_apply, lcomp_commQ P Q h l x, h a]

theorem projC [NeZero r] (L : Letters N) (ρ : Fin r) (e1 j0 : ℕ) (hj0 : j0 ≤ N) (hHP : HypP p L ρ e1) {q : ℕ}
    (J : Fin q → ℕ) (M : Fin q → WithTop ℤ) :
    ∃ Pi : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p],
      IsProjC L j0 (e1 * j0) J M Pi := by
  obtain ⟨hP1, hP2⟩ := hHP
  let Tj : Fin j0 → Set (Fin r → ℤ) := fun j => {la | ∀ k, J k = (j : ℕ) → ((la 0 : ℤ) : WithTop ℤ) ≤ M k}
  have hex : ∀ j : Fin j0, ∃ P, IsTypeProj p L j univ (Tj j) P ∧ (∀ F G, fock p (P F) G = fock p F (P G)) ∧
      ∀ F ∈ PolZ p r L, ((p : ℚ_[p]) ^ e1) • P F ∈ IntPol p (Fin N × Fin r) :=
    fun j => hP1 j (le_trans (le_of_lt j.isLt) hj0) univ (Or.inl rfl) (Tj j)
      (fun la la' h => by rw [show la = la' from funext fun c => h c (mem_univ c)])
  choose P hPt _hPsa hPint using hex
  have hPP : ∀ j x, P j (P j x) = P j x := fun j x => LinearMap.congr_fun (hPt j).1 x
  have hcomm : ∀ j j' x, P j (P j' x) = P j' (P j x) := by
    intro j j' x
    rcases le_total (j : ℕ) (j' : ℕ) with h | h
    · exact LinearMap.congr_fun (hP2 j j' univ univ (Tj j) (Tj j') (P j) (P j') h subset_rfl (Or.inl rfl)
        (Or.inl rfl) (hPt j) (hPt j')) x
    · exact (LinearMap.congr_fun (hP2 j' j univ univ (Tj j') (Tj j) (P j') (P j) h subset_rfl (Or.inl rfl)
        (Or.inl rfl) (hPt j') (hPt j)) x).symm
  have hPpol : ∀ L' : Letters N, L'.vec = L.vec → ∀ j, ∀ x ∈ Pol p r L', P j x ∈ Pol p r L' := fun L' hL' j =>
    typeProj_pol L' j (Tj j) (P j) (isTypeProj_congr L L' hL' j univ (Tj j) (P j) (hPt j))
  have hgl : ∀ c d x, lcomp P (List.finRange j0) (glAct p L j0 c d x) =
      glAct p L j0 c d (lcomp P (List.finRange j0) x) := fun c d x =>
    lcomp_commQ P (glAct p L j0 c d) (fun j y => typeProj_comm L j (Tj j) (P j) (hPt j) (glAct p L j0 c d)
      (fun la => iso_keep_glAct L (le_of_lt j.isLt) c d la) y) _ x
  refine ⟨lcomp P (List.finRange j0), hgl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro ν x hx
    rw [← wtsp_iff_wh] at hx ⊢
    exact comm_wtsp L j0 _ (fun c y => hgl c c y) ν x hx
  · intro L' hL' x hx
    exact lcomp_keep P (Pol p r L' : Set _) _ (fun j _ u hu => hPpol L' hL' j u hu) x hx
  · intro x k
    by_cases hk : J k < j0
    · rw [Mup, if_pos hk]
      have hfix : P ⟨J k, hk⟩ (lcomp P (List.finRange j0) x) = lcomp P (List.finRange j0) x :=
        lcomp_fix P hPP hcomm _ ⟨J k, hk⟩ (List.mem_finRange _) x
      have h1 : lcomp P (List.finRange j0) x ∈ LinearMap.range (P ⟨J k, hk⟩) := ⟨_, hfix⟩
      rw [(hPt ⟨J k, hk⟩).2.1] at h1
      exact (iSup₂_le fun la hla => isoC_le_ycond L (J k) la (M k) (hla k rfl)) h1
    · rw [Mup, if_neg hk, Formalism.GM.DimensionMonotonicity.ycond_top]; exact Submodule.mem_top
  · intro L' hL' x hxP hxY
    refine lcomp_fixed P x (fun j => ?_) _
    have hPt' := isTypeProj_congr L L' hL' j univ (Tj j) (P j) (hPt j)
    set S : Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]) :=
      Pol p r L' ⊓ ⨅ (k : Fin q) (_ : J k = (j : ℕ)), YCond p (r := r) L' j (M k) with hSdef
    have hmemS : ∀ x, x ∈ S ↔ x ∈ Pol p r L' ∧ ∀ k, J k = (j : ℕ) → x ∈ YCond p (r := r) L' j (M k) := by
      intro x; simp only [hSdef, Submodule.mem_inf, Submodule.mem_iInf]
    have hfix := proj_fix L' j (Tj j) (P j) hPt' S inf_le_left
      (fun c d x hx => by
        rw [hmemS] at hx ⊢
        exact ⟨Formalism.CountingSumsFrames.glAct_pol L' j c d x hx.1, fun k hk => ycond_glStable L' j (M k) c d x (hx.2 k hk)⟩)
      (fun x hx => by
        rw [hmemS] at hx ⊢
        exact ⟨hPpol L' hL' j x hx.1, fun k hk => typeProj_ycond L' j (Tj j) (P j) hPt' (M k) x (hx.2 k hk)⟩)
      (fun h hh hh0 μ hμ => by
        rw [hmemS] at hh
        intro k hk
        have h1 := ycond_le_supp L' j (M k) (hh.2 k hk)
        obtain ⟨m, hm⟩ : ∃ m, m ∈ h.support := by
          by_contra hc; push Not at hc
          exact hh0 (MvPolynomial.support_eq_empty.mp (Finset.eq_empty_of_forall_notMem hc))
        rw [mem_restrictSupport_iff] at h1
        have h2 := h1 (Finset.mem_coe.mpr hm)
        have h3 := (Submodule.mem_inf.mp hμ).1
        rw [WtSpC, mem_restrictSupport_iff] at h3
        have h4 := h3 (Finset.mem_coe.mpr hm) 0 (Finset.mem_univ _)
        simp only [Set.mem_ofPred_eq] at h2
        rw [h4] at h2
        exact h2)
    apply hfix
    rw [hmemS]
    refine ⟨hxP, fun k hk => ?_⟩
    have := hxY k
    rw [Mup, if_pos (by rw [hk]; exact j.isLt), hk] at this
    rw [ycond_congr L L' hL']
    exact this
  · intro x hx
    have := lcomp_int L e1 P (hPpol L rfl) hPint (List.finRange j0) x hx
    rw [List.length_finRange] at this
    exact (Submodule.mem_inf.mp this).2
  · intro g q hq
    have := lcomp_commQ P (LinearMap.mulRight ℚ_[p] q) (fun j y => typeProj_comm L j (Tj j) (P j) (hPt j)
      (LinearMap.mulRight ℚ_[p] q) (fun la => iso_keep_mul L (le_of_lt j.isLt) hq la) y) (List.finRange j0) g
    simpa only [LinearMap.mulRight_apply] using this

end Formalism.CountingSumsFrames.TO

namespace Formalism.CountingSumsFrames.TO

open Formalism.GM Formalism.GM.M Formalism.GM.DimensionMonotonicity MvPolynomial Finset

variable {p : ℕ} [Fact p.Prime] {N r : ℕ}

section Leib

variable {σ : Type} (A : MvPolynomial σ ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial σ ℚ_[p])
  (hA : ∀ a b, A (a * b) = a * A b + b * A a)

include hA

theorem pow_mul_killed {u' : MvPolynomial σ ℚ_[p]} (hu' : A u' = 0) (k : ℕ) :
    ∀ f, (A ^ k) (f * u') = (A ^ k) f * u' := by
  induction k with
  | zero => intro f; simp
  | succ k ih =>
    intro f
    rw [pow_succ A k, Module.End.mul_apply, Module.End.mul_apply, hA, hu', mul_zero, zero_add, mul_comm u', ih]

theorem pow_succ_mul_gen {u u' : MvPolynomial σ ℚ_[p]} (hu : A u = u') (hu' : A u' = 0) (k : ℕ) :
    ∀ f, (A ^ (k + 1)) (f * u) = (A ^ (k + 1)) f * u + ((k + 1 : ℕ) : ℚ_[p]) • ((A ^ k) f * u') := by
  induction k with
  | zero =>
    intro f
    simp only [zero_add, pow_one, pow_zero, Module.End.one_apply, hA, hu, Nat.cast_one, one_smul]
    ring
  | succ k ih =>
    intro f
    have e1 : (A ^ (k + 1 + 1)) (f * u) = (A ^ (k + 1)) (A (f * u)) := by
      rw [pow_succ A (k + 1), Module.End.mul_apply]
    have e2 : (A ^ (k + 1 + 1)) f = (A ^ (k + 1)) (A f) := by
      rw [pow_succ A (k + 1), Module.End.mul_apply]
    have e3 : (A ^ (k + 1)) f = (A ^ k) (A f) := by
      rw [pow_succ A k, Module.End.mul_apply]
    rw [e1, e2, hA, hu, map_add, pow_mul_killed A hA hu' (k + 1), mul_comm u, ih, ← e3,
      Nat.cast_succ (k + 1), add_smul, one_smul]
    abel

end Leib

theorem glAct_C' (L : Letters N) (j : ℕ) (c d : Fin r) (a : ℚ_[p]) :
    glAct p L j c d (C a) = 0 := by
  rw [Formalism.GM.FrozenVariableComponents.glAct_apply]
  refine Finset.sum_eq_zero fun i _ => ?_
  split_ifs <;> simp

theorem glAct_X_int (L : Letters N) (j : ℕ) (c d : Fin r) (v : Fin N × Fin r) :
    glAct p L j c d (X v) ∈ IntPol p (Fin N × Fin r) := by
  obtain ⟨i, a⟩ := v
  rw [glAct_X_gen]
  split_ifs
  · exact FrozenVariableLemmas.intPol_X p _
  · exact Submodule.zero_mem _
  · exact Submodule.neg_mem _ (FrozenVariableLemmas.intPol_X p _)
  · exact Submodule.zero_mem _
  · exact Submodule.zero_mem _

theorem glAct_glAct_X (L : Letters N) (j : ℕ) (c d : Fin r) (hcd : c ≠ d) (v : Fin N × Fin r) :
    glAct p L j c d (glAct p L j c d (X v)) = 0 := by
  obtain ⟨i, a⟩ := v
  rw [glAct_X_gen]
  split_ifs with h1 h2 h3 h3
  · rw [glAct_X_gen, if_pos h1, if_pos h2, if_neg hcd]
  · exact map_zero _
  · rw [map_neg, glAct_X_gen, if_pos h1, if_neg h2, if_neg (Ne.symm hcd), neg_zero]
  · exact map_zero _
  · exact map_zero _

theorem divpow_int (L : Letters N) (j : ℕ) (c d : Fin r) (hcd : c ≠ d) (k : ℕ)
    (x : MvPolynomial (Fin N × Fin r) ℚ_[p]) (hx : x ∈ IntPol p (Fin N × Fin r)) :
    (((k.factorial : ℚ_[p]))⁻¹) • ((glAct p L j c d) ^ k) x ∈ IntPol p (Fin N × Fin r) := by
  obtain ⟨x₀, rfl⟩ := (FrozenVariableLemmas.intPol_iff p x).mp hx
  clear hx
  induction x₀ using MvPolynomial.induction_on generalizing k with
  | C a =>
    rw [map_C]
    cases k with
    | zero => simpa using (FrozenVariableLemmas.intPol_iff p _).mpr ⟨C a, map_C _ _⟩
    | succ k =>
      rw [pow_succ, Module.End.mul_apply, glAct_C', map_zero, smul_zero]
      exact Submodule.zero_mem _
  | add f g hf hg =>
    rw [map_add, map_add, smul_add]
    exact Submodule.add_mem _ (hf k) (hg k)
  | mul_X f v hf =>
    rw [map_mul, map_X]
    cases k with
    | zero =>
      have := hf 0
      simp only [Nat.factorial_zero, Nat.cast_one, inv_one, pow_zero, Module.End.one_apply, one_smul] at this ⊢
      exact FrozenVariableLemmas.intPol_mul p this (FrozenVariableLemmas.intPol_X p v)
    | succ k =>
      rw [pow_succ_mul_gen (glAct p L j c d) (fun a b => Formalism.GM.M.FB.glAct_mul L j c d a b) rfl
        (glAct_glAct_X L j c d hcd v) k, smul_add, smul_smul]
      have e : (((k + 1).factorial : ℚ_[p]))⁻¹ * ((k + 1 : ℕ) : ℚ_[p]) = ((k.factorial : ℚ_[p]))⁻¹ := by
        have h1 : ((k + 1 : ℕ) : ℚ_[p]) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
        have h2 : ((k.factorial : ℕ) : ℚ_[p]) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
        rw [Nat.factorial_succ, Nat.cast_mul]
        field_simp
      rw [e, ← smul_mul_assoc, ← smul_mul_assoc]
      exact Submodule.add_mem _ (FrozenVariableLemmas.intPol_mul p (hf (k + 1)) (FrozenVariableLemmas.intPol_X p v))
        (FrozenVariableLemmas.intPol_mul p (hf k) (glAct_X_int L j c d v))

theorem comm_pow (L : Letters N) (j0 : ℕ)
    (Tm : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hcomm : ∀ c d x, Tm (glAct p L j0 c d x) = glAct p L j0 c d (Tm x)) (c d : Fin r) (k : ℕ) :
    ∀ x, Tm (((glAct p L j0 c d) ^ k) x) = ((glAct p L j0 c d) ^ k) (Tm x) := by
  induction k with
  | zero => intro x; simp
  | succ k ih =>
    intro x
    rw [pow_succ', Module.End.mul_apply, Module.End.mul_apply, hcomm, ih]

theorem int_main (L : Letters N) (ρ : Fin r) (e1 j0 : ℕ) (hj0 : j0 ≤ N) (hHP : HypP p L ρ e1) (hHW : HypW p (r := r) L e1)
    (Tm : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p]) (K0 : ℕ)
    (hcomm : ∀ c d x, Tm (glAct p L j0 c d x) = glAct p L j0 c d (Tm x))
    (hhw : ∀ la : Fin r → ℤ, ∀ h ∈ HWC p L j0 univ la ⊓ Pol p r L, h ∈ IntPol p (Fin N × Fin r) →
      ((p : ℚ_[p]) ^ K0) • Tm h ∈ IntPol p (Fin N × Fin r)) :
    ∀ y ∈ PolZ p r L, ((p : ℚ_[p]) ^ (K0 + 2 * e1)) • Tm y ∈ IntPol p (Fin N × Fin r) := by
  classical
  obtain ⟨hP1, -⟩ := hHP
  have hsat : ∀ T : Set (Fin r → ℤ), CsSaturated (univ : Finset (Fin r)) T := fun T la la' h => by
    rw [show la = la' from funext fun c => h c (mem_univ c)]

  have htop : (⨆ la : Fin r → ℤ, IsoC p L j0 univ la) = ⊤ := by
    obtain ⟨P0, ⟨hPP, hran, hker⟩, -, -⟩ := hP1 j0 hj0 univ (Or.inl rfl) Set.univ (hsat _)
    have hk : LinearMap.ker P0 = ⊥ := by
      rw [hker]; simp
    have hid : ∀ x, P0 x = x := by
      intro x
      have : P0 x - x ∈ LinearMap.ker P0 := by
        rw [LinearMap.mem_ker, map_sub, sub_eq_zero]; exact LinearMap.congr_fun hPP x
      rw [hk, Submodule.mem_bot, sub_eq_zero] at this
      exact this
    have hr : LinearMap.range P0 = ⊤ := by
      rw [eq_top_iff]; intro x _; exact ⟨x, hid x⟩
    rw [← hr, hran]; simp
  have hex : ∀ la : Fin r → ℤ, ∃ P, IsTypeProj p L j0 univ {la} P ∧
      ∀ F ∈ PolZ p r L, ((p : ℚ_[p]) ^ e1) • P F ∈ IntPol p (Fin N × Fin r) := fun la => by
    obtain ⟨P, h1, -, h3⟩ := hP1 j0 hj0 univ (Or.inl rfl) {la} (hsat _)
    exact ⟨P, h1, h3⟩
  choose P hPt hPint using hex

  set S : Submodule ℤ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]) :=
    (IntPol p (Fin N × Fin r)).comap ((((p : ℚ_[p]) ^ K0) • Tm).restrictScalars ℤ_[p]) with hS
  have hmemS : ∀ x, x ∈ S ↔ ((p : ℚ_[p]) ^ K0) • Tm x ∈ IntPol p (Fin N × Fin r) := fun x => Iff.rfl
  have hWeyl : ∀ la : Fin r → ℤ, ∀ h, (h ∈ HWC p L j0 univ la ⊓ Pol p r L ∧ h ∈ IntPol p (Fin N × Fin r)) →
      WeylLat p L j0 h ≤ S := by
    intro la h hh
    refine sInf_le ⟨(hmemS h).mpr (hhw la h hh.1 hh.2), ?_⟩
    intro c d hcd k x hx
    rw [hmemS] at hx ⊢
    rw [map_smul, comm_pow L j0 Tm hcomm c d k x, smul_comm, ← map_smul]
    exact divpow_int L j0 c d hcd k _ hx
  intro y hy
  have hyP : y ∈ Pol p r L := (Submodule.mem_inf.mp hy).1
  have hyT : y ∈ ⨆ la : Fin r → ℤ, IsoC p L j0 univ la := by rw [htop]; exact Submodule.mem_top
  obtain ⟨f, hf, hsum⟩ := (Submodule.mem_iSup_iff_exists_finsupp _ _).mp hyT
  have hPfix : ∀ la, ∀ x ∈ IsoC p L j0 univ la, P la x = x := by
    intro la x hx
    have : x ∈ LinearMap.range (P la) := by
      rw [(hPt la).2.1]
      exact (le_iSup₂ (f := fun la' (_ : la' ∈ ({la} : Set (Fin r → ℤ))) => IsoC p L j0 univ la') la rfl) hx
    obtain ⟨z, rfl⟩ := this
    exact LinearMap.congr_fun (hPt la).1 z
  have hPkill : ∀ la mu, mu ≠ la → ∀ x ∈ IsoC p L j0 univ mu, P la x = 0 := by
    intro la mu hne x hx
    have : x ∈ LinearMap.ker (P la) := by
      rw [(hPt la).2.2]
      exact (le_iSup₂ (f := fun la' (_ : la' ∉ ({la} : Set (Fin r → ℤ))) => IsoC p L j0 univ la') mu hne) hx
    exact this
  have hPy : ∀ la, P la y = f la := by
    intro la
    rw [← hsum, Finsupp.sum, map_sum]
    rw [Finset.sum_eq_single la]
    · exact hPfix la _ (hf la)
    · intro mu _ hne; exact hPkill la mu hne _ (hf mu)
    · intro hla
      rw [Finsupp.notMem_support_iff.mp hla, map_zero]
  have hterm : ∀ la, ((p : ℚ_[p]) ^ (K0 + 2 * e1)) • Tm (P la y) ∈ IntPol p (Fin N × Fin r) := by
    intro la
    have h1 : ((p : ℚ_[p]) ^ e1) • P la y ∈ IntPol p (Fin N × Fin r) := hPint la y hy
    have h2 : ((p : ℚ_[p]) ^ e1) • P la y ∈ IsoC p L j0 univ la ⊓ Pol p r L :=
      Submodule.smul_mem _ _ (Submodule.mem_inf.mpr ⟨by rw [hPy]; exact hf la,
        typeProj_pol L j0 {la} (P la) (hPt la) y hyP⟩)
    have h3 := hHW j0 hj0 la _ h2 h1
    have h4 : ((p : ℚ_[p]) ^ e1) • ((p : ℚ_[p]) ^ e1) • P la y ∈ S :=
      (iSup₂_le fun h hh => hWeyl la h hh) h3
    rw [hmemS, map_smul, map_smul, smul_smul, smul_smul] at h4
    have e : (p : ℚ_[p]) ^ (K0 + 2 * e1) = (p : ℚ_[p]) ^ K0 * (p : ℚ_[p]) ^ e1 * (p : ℚ_[p]) ^ e1 := by
      rw [pow_add, two_mul, pow_add, mul_assoc]
    rw [e]; exact h4
  have hy2 : y = ∑ la ∈ f.support, P la y := by
    conv_lhs => rw [← hsum, Finsupp.sum]
    exact Finset.sum_congr rfl fun la _ => (hPy la).symm
  rw [hy2, map_sum, Finset.smul_sum]
  exact Submodule.sum_mem _ fun la _ => hterm la

end Formalism.CountingSumsFrames.TO

namespace Formalism.CountingSumsFrames.TO

open Formalism.GM Formalism.GM.M Formalism.GM.DimensionMonotonicity Formalism.GM.TM MvPolynomial Finset

variable {p : ℕ} [Fact p.Prime] {N r : ℕ}

noncomputable def FfL (p : ℕ) [Fact p.Prime] {N r : ℕ} [NeZero N] (L : Letters N) (T : TieData) (i : Fin T.t) (ρ : Fin r)
    (n : ℕ) : MvPolynomial (Fin (T.pos i + 1) × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p] where
  toFun := T.Ffull p L i ρ n
  map_add' := by
    intro f g
    simp only [TieData.Ffull, freeze, map_add, mul_add]
  map_smul' := by
    intro c f
    simp only [TieData.Ffull, freeze, map_smul, mul_smul_comm, RingHom.id_apply]

theorem FfL_apply [NeZero N] (L : Letters N) (T : TieData) (i : Fin T.t) (ρ : Fin r) (n : ℕ)
    (f : MvPolynomial (Fin (T.pos i + 1) × Fin r) ℚ_[p]) : FfL p L T i ρ n f = T.Ffull p L i ρ n f := rfl

theorem wtsp_iff {M : ℕ} (L : Letters M) (j : ℕ) (la : Fin r → ℤ) (x : MvPolynomial (Fin M × Fin r) ℚ_[p]) :
    x ∈ WtSpC p L j univ la ↔ IsWeightedHomogeneous (wv L j) x la := by
  rw [WtSpC, mem_restrictSupport_iff]
  constructor
  · intro h m hm
    funext c
    rw [weight_wv]
    exact h (Finset.mem_coe.mpr (mem_support_iff.mpr hm)) c (mem_univ c)
  · intro h m hm c _
    rw [← weight_wv, h (mem_support_iff.mp (Finset.mem_coe.mp hm))]

theorem intPol_rename {σ τ : Type} (e : σ → τ) {y : MvPolynomial σ ℚ_[p]} (hy : y ∈ IntPol p σ) :
    rename e y ∈ IntPol p τ := by
  obtain ⟨P, rfl⟩ := LinearMap.mem_range.mp hy
  refine LinearMap.mem_range.mpr ⟨rename e P, ?_⟩
  simp only [AlgHom.toLinearMap_apply, mapAlgHom_apply, map_rename]

section Comparison₂

variable [NeZero N] [NeZero r] (LL : Letters N) (T : TieData) (hadm : T.Admissible LL) (i : Fin T.t) (ρ : Fin r)
  (hρ : (ρ : ℕ) = r - 1) (n : Fin T.t → ℕ) (hS : ((LL.setTies T n).takeD (T.pos i + 1)).total ≤ n i)

include hadm hS

theorem Ffull_int (f : MvPolynomial (Fin (T.pos i + 1) × Fin r) ℚ_[p])
    (hf : f ∈ PolZ p r ((LL.setTies T n).takeD (T.pos i + 1))) :
    T.Ffull p (LL.setTies T n) i ρ (n i) f ∈ IntPol p (Fin N × Fin r) := by
  obtain ⟨hP, hI⟩ := Submodule.mem_inf.mp hf
  have h1 := (Formalism.GM.extendMapsTo p (T.pos i + 1) r _ ρ (n i) hS f hP).2.2 hI
  rw [Ffull_eq]
  exact intPol_rename _ h1

theorem Ffull_C (w : Fin r → ℤ) (f : MvPolynomial (Fin (T.pos i + 1) × Fin r) ℚ_[p])
    (hf : f ∈ MMw p ((LL.setTies T n).takeD (T.pos i + 1)) T.J (T.thrUpTo i) ρ w) :
    T.Ffull p (LL.setTies T n) i ρ (n i) f ∈ Cset p (LL.setTies T n) (T.pos i + 1 + 1) T.J T.thr := by
  have hP : f ∈ Pol p r ((LL.setTies T n).takeD (T.pos i + 1)) :=
    (Submodule.mem_inf.mp (Submodule.mem_inf.mp (Submodule.mem_inf.mp hf).1).1).1
  refine Submodule.mem_inf.mpr ⟨Ffull_pol LL T hadm i ρ n f hP hS, (Submodule.mem_iInf _).mpr fun k => ?_⟩
  by_cases hk : T.J k < T.pos i + 1 + 1
  · rw [Mup, if_pos hk]
    exact Ffull_ycond LL T hadm i ρ n w f hf hS k (by omega)
  · rw [Mup, if_neg hk, Formalism.GM.DimensionMonotonicity.ycond_top]; exact Submodule.mem_top

theorem Ffull_inj (f : MvPolynomial (Fin (T.pos i + 1) × Fin r) ℚ_[p])
    (hP : f ∈ Pol p r ((LL.setTies T n).takeD (T.pos i + 1)))
    (h0 : T.Ffull p (LL.setTies T n) i ρ (n i) f = 0) : f = 0 := by
  have hK := hK_of_adm LL T hadm i
  rw [Ffull_eq] at h0
  have h1 : freeze p ((LL.setTies T n).takeD (T.pos i + 1)) ρ (n i) f = 0 := by
    apply rename_injective _ (inclusion_prodMap_injective (r := r) hK)
    rw [h0, map_zero]
  exact (Formalism.GM.extendBijOn p (T.pos i + 1) r ((LL.setTies T n).takeD (T.pos i + 1)) ρ (n i) hS).1 f hP 0
    (Submodule.zero_mem _) (by rw [h1, freeze_zero])

omit hS in
theorem deg_compat (a : Fin (T.pos i + 1 + 1)) :
    (LL.setTies T n).deg (ιF N (T.pos i + 1) a) = (((LL.setTies T n).takeD (T.pos i + 1)).snoc (n i)).deg a := by
  have hK := hK_of_adm LL T hadm i
  induction a using Fin.lastCases with
  | last =>
    rw [Formalism.GM.M.FB.snoc_deg_last]
    have : ιF N (T.pos i + 1) (Fin.last (T.pos i + 1)) = ⟨T.pos i + 1, by omega⟩ := by
      apply Fin.ext; rw [ιF_val hK]; simp
    rw [this]; exact setTies_deg_eta LL T hadm i n _
  | cast a =>
    rw [Formalism.GM.M.FB.snoc_deg_castSucc]
    have : ιF N (T.pos i + 1) (Fin.castSucc a) = ⟨a, by omega⟩ := by
      apply Fin.ext; rw [ιF_val hK]; simp
    rw [this]
    simp [Letters.takeD, (by omega : (a : ℕ) < N)]

omit hS in

theorem ycond_pull (J : ℕ) (M : WithTop ℤ) (F : MvPolynomial (Fin (T.pos i + 1 + 1) × Fin r) ℚ_[p])
    (h : rename (fun x : Fin (T.pos i + 1 + 1) × Fin r => (ιF N (T.pos i + 1) x.1, x.2)) F ∈ YCond p LL J M) :
    F ∈ YCond p (((LL.setTies T n).takeD (T.pos i + 1)).snoc (n i)) J M := by
  classical
  have hK := hK_of_adm LL T hadm i
  have hι := inclusion_prodMap_injective (N := N) (r := r) hK
  set S : Submodule ℚ_[p] (MvPolynomial (Fin (T.pos i + 1 + 1) × Fin r) ℚ_[p]) := (YCond p LL J M).comap
    (rename (fun x : Fin (T.pos i + 1 + 1) × Fin r => (ιF N (T.pos i + 1) x.1, x.2))).toLinearMap with hSd
  have hle : S ≤ YCond p (((LL.setTies T n).takeD (T.pos i + 1)).snoc (n i)) J M := by
    refine le_sSup ⟨?_, ?_⟩
    · intro G hG
      rw [mem_restrictSupport_iff]
      intro m hm
      have h1 := Formalism.CountingSumsFrames.ycond_le_supp LL J M (Submodule.mem_comap.mp hG)
      rw [mem_restrictSupport_iff] at h1
      have h2 : Finsupp.mapDomain (fun x : Fin (T.pos i + 1 + 1) × Fin r => (ιF N (T.pos i + 1) x.1, x.2)) m ∈
          (rename (fun x : Fin (T.pos i + 1 + 1) × Fin r => (ιF N (T.pos i + 1) x.1, x.2)) G).support := by
        rw [support_rename_of_injective hι]; exact Finset.mem_image_of_mem _ hm
      have h3 : ((wt LL J 0 (Finsupp.mapDomain (fun x : Fin (T.pos i + 1 + 1) × Fin r =>
          (ιF N (T.pos i + 1) x.1, x.2)) m) : ℤ) : WithTop ℤ) ≤ M := h1 (Finset.mem_coe.mpr h2)
      rw [← weight_wv, weight_mapDomain, wv_compat LL T hadm i n (n i), weight_wv] at h3
      exact h3
    · intro c d G hG
      rw [hSd, Submodule.mem_comap, AlgHom.toLinearMap_apply,
        glAct_rename (((LL.setTies T n).takeD (T.pos i + 1)).snoc (n i)) LL (ιF N (T.pos i + 1)) (ιF_val hK)
          (fun a => vec_compat LL T hadm i n (n i) a) J c d G]
      exact Formalism.CountingSumsFrames.ycond_glStable LL J M c d _ (Submodule.mem_comap.mp hG)
  exact hle (Submodule.mem_comap.mpr h)

include hρ

theorem hw_is_Ffull (μ : Fin r → ℤ) (v : MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hv : v ∈ Cset p (LL.setTies T n) (T.pos i + 1 + 1) T.J T.thr)
    (hw : (GA p (LL.setTies T n) (T.pos i + 1 + 1)).IsHW μ v) (hint : v ∈ IntPol p (Fin N × Fin r)) :
    ∃ f ∈ MMwZ p ((LL.setTies T n).takeD (T.pos i + 1)) T.J (T.thrUpTo i) ρ (μ + ((n i : ℕ) : ℤ) • Pi.single ρ 1),
      v = T.Ffull p (LL.setTies T n) i ρ (n i) f := by
  classical
  have hK := hK_of_adm LL T hadm i
  set LLK := (LL.setTies T n).takeD (T.pos i + 1) with hLLK
  let ι : Fin (T.pos i + 1 + 1) × Fin r → Fin N × Fin r := fun x => (ιF N (T.pos i + 1) x.1, x.2)
  have hι : Function.Injective ι := inclusion_prodMap_injective (r := r) hK
  obtain ⟨hvP, hvY⟩ := Submodule.mem_inf.mp hv
  have hvF := isF_of_polLz _ _ hvP
  obtain ⟨F, hF⟩ : ∃ F, rename ι F = v := by
    apply exists_rename_eq_of_vars_subset_range v ι hι
    intro x hx
    rw [Finset.mem_coe, mem_vars] at hx
    obtain ⟨m, hm, hxm⟩ := hx
    have hlt : (x.1 : ℕ) < T.pos i + 1 + 1 := hvF m hm x (Finsupp.mem_support_iff.mp hxm)
    exact ⟨(⟨x.1, hlt⟩, x.2), Prod.ext (Fin.ext (ιF_val hK _)) rfl⟩
  have hsupp : ∀ m ∈ F.support, Finsupp.mapDomain ι m ∈ v.support := by
    intro m hm; rw [← hF, support_rename_of_injective hι]; exact Finset.mem_image_of_mem _ hm
  have hFP : F ∈ Pol p r (LLK.snoc (n i)) := by
    rw [Pol, mem_restrictSupport_iff]
    intro m hm a
    have h1 : MultiDeg (Lz (LL.setTies T n) (T.pos i + 1 + 1)) (Finsupp.mapDomain ι m) :=
      ((MvPolynomial.mem_restrictSupport_iff ℚ_[p]).mp hvP) (Finset.mem_coe.mpr (hsupp m hm))
    have h2 := h1 (ιF N (T.pos i + 1) a)
    have h3 : ∀ c, Finsupp.mapDomain ι m (ιF N (T.pos i + 1) a, c) = m (a, c) :=
      fun c => Finsupp.mapDomain_apply hι m (a, c)
    simp only [h3] at h2
    rw [h2]
    simp only [Lz]
    rw [if_pos (by rw [ιF_val hK]; exact a.isLt), deg_compat LL T hadm i n]
  have hFI : F ∈ IntPol p (Fin (T.pos i + 1 + 1) × Fin r) := mem_intPol_of_norm _ fun m => by
    have := Formalism.CountingSumsFrames.intPol_norm v hint (Finsupp.mapDomain ι m)
    rwa [← hF, coeff_rename_mapDomain ι hι] at this
  have hgl : ∀ J c d, rename ι (glAct p (LLK.snoc (n i)) J c d F) = glAct p LL J c d v := by
    intro J c d
    rw [← hF]
    exact glAct_rename (LLK.snoc (n i)) LL (ιF N (T.pos i + 1)) (ιF_val hK)
      (fun a => vec_compat LL T hadm i n (n i) a) J c d F
  have hraise : ∀ a b, a < b → glAct p (LLK.snoc (n i)) (T.pos i + 1 + 1) a b F = 0 := by
    intro a b hab
    apply rename_injective ι hι
    rw [hgl, map_zero]
    exact hw.2 a b hab
  have hinv : IsFrozenInv p LLK ρ (n i) F := fun c hc => hraise c ρ (Fin.lt_def.mpr (by
    have := c.isLt
    have : (c : ℕ) ≠ ρ := fun h => hc (Fin.ext h)
    omega))
  obtain ⟨f, hfZ, hfF⟩ := (Formalism.GM.extendBijOn p (T.pos i + 1) r LLK ρ (n i) hS).2 F
    (Submodule.mem_inf.mpr ⟨hFP, hFI⟩) hinv
  have hfP : f ∈ Pol p r LLK := (Submodule.mem_inf.mp hfZ).1
  let J' : Fin T.q → ℕ := fun k => min (T.J k) (T.pos i + 1)
  have hFY : freeze p LLK ρ (n i) f ∈ Y p (LLK.snoc (n i)) J' (T.thrUpTo i) := by
    rw [hfF]
    refine Submodule.mem_inf.mpr ⟨hFP, (Submodule.mem_iInf _).mpr fun k => ?_⟩
    by_cases hk : T.J k ≤ T.pos i + 1
    · have e1 : J' k = T.J k := min_eq_left hk
      have e2 : T.thrUpTo i k = T.thr k := by simp [TieData.thrUpTo, hk]
      rw [e1, e2]
      apply ycond_pull LL T hadm i n
      have h1 := (Submodule.mem_iInf _).mp hvY k
      rw [Mup, if_pos (by omega)] at h1
      rw [← hF] at h1
      exact h1
    · have ht : T.thrUpTo i k = ⊤ := by simp [TieData.thrUpTo, hk]
      rw [ht, Formalism.GM.DimensionMonotonicity.ycond_top]; exact Submodule.mem_top
  have hfY' := (Formalism.GM.extendWeightBounded p (T.pos i + 1) r LLK ρ (n i) J' (T.thrUpTo i) hS
    (fun k => min_le_right _ _) f hfP).mpr hFY
  have hfY : f ∈ Y p LLK T.J (T.thrUpTo i) := by
    refine Submodule.mem_inf.mpr ⟨hfP, (Submodule.mem_iInf _).mpr fun k => ?_⟩
    have h1 := (Submodule.mem_iInf _).mp (Submodule.mem_inf.mp hfY').2 k
    by_cases hk : T.J k ≤ T.pos i + 1
    · simpa [J', min_eq_left hk] using h1
    · have ht : T.thrUpTo i k = ⊤ := by simp [TieData.thrUpTo, hk]
      rw [ht, Formalism.GM.DimensionMonotonicity.ycond_top]; exact Submodule.mem_top

  set w : Fin r → ℤ := μ + ((n i : ℕ) : ℤ) • Pi.single ρ 1 with hwd
  have hvW : IsWeightedHomogeneous (wv LL (T.pos i + 1 + 1)) v μ := by
    have h1 := weightedHomogeneousComponent_isWeightedHomogeneous (R := ℚ_[p]) (w := wv LL (T.pos i + 1 + 1)) μ v
    have h2 : weightedHomogeneousComponent (wv LL (T.pos i + 1 + 1)) μ v = v := hw.1
    rwa [h2] at h1
  have hFw : IsWeightedHomogeneous (wv (LLK.snoc (n i)) (T.pos i + 1 + 1)) F μ := by
    intro m hm
    have h1 := hvW (mem_support_iff.mp (hsupp m (mem_support_iff.mpr hm)))
    rwa [weight_mapDomain, wv_compat LL T hadm i n (n i)] at h1
  have hcP : ∀ w', weightedHomogeneousComponent (wv LLK (T.pos i + 1)) w' f ∈ Pol p r LLK := by
    intro w'
    rw [pol_iff] at hfP ⊢
    exact (mem_weightedHomogeneousSubmodule _ _ _ _).mp
      (whc_keep _ _ w' _ ((mem_weightedHomogeneousSubmodule _ _ _ _).mpr hfP))
  have hcW : ∀ w', IsWeightedHomogeneous (wv (LLK.snoc (n i)) (T.pos i + 1 + 1))
      (freeze p LLK ρ (n i) (weightedHomogeneousComponent (wv LLK (T.pos i + 1)) w' f))
      (w' - ((n i : ℕ) : ℤ) • Pi.single ρ 1) := fun w' =>
    freeze_wh LLK ρ (n i) hS w' _ (hcP w')
      ((wtsp_iff LLK (T.pos i + 1) w' _).mpr (weightedHomogeneousComponent_isWeightedHomogeneous w' f))
  have hcomp : f = weightedHomogeneousComponent (wv LLK (T.pos i + 1)) w f := by
    obtain ⟨S, hS0⟩ := (GA p LLK (T.pos i + 1)).dec f
    have hS' : ∀ μ' ∉ S, weightedHomogeneousComponent (wv LLK (T.pos i + 1)) μ' f = 0 := hS0
    have hsum : ∑ μ' ∈ S, weightedHomogeneousComponent (wv LLK (T.pos i + 1)) μ' f = f :=
      (GA p LLK (T.pos i + 1)).sum_comp f S hS0
    have hfr : freeze p LLK ρ (n i) f =
        ∑ w' ∈ S, freeze p LLK ρ (n i) (weightedHomogeneousComponent (wv LLK (T.pos i + 1)) w' f) := by
      conv_lhs => rw [← hsum]
      simp only [freeze, map_sum, Finset.mul_sum]
    have h5 : F = freeze p LLK ρ (n i) (weightedHomogeneousComponent (wv LLK (T.pos i + 1)) w f) := by
      have h6 : weightedHomogeneousComponent (wv (LLK.snoc (n i)) (T.pos i + 1 + 1)) μ F = F := by
        rw [weightedHomogeneousComponent_of_mem hFw, if_pos rfl]
      rw [← h6, ← hfF, hfr, map_sum]
      simp only [weightedHomogeneousComponent_of_mem (hcW _)]
      have hiff : ∀ w', μ = w' - ((n i : ℕ) : ℤ) • Pi.single ρ 1 ↔ w' = w := by
        intro w'; rw [hwd]; constructor
        · intro h; rw [h]; abel
        · intro h; rw [h]; abel
      simp only [hiff]
      rw [Finset.sum_ite_eq' S w]
      split_ifs with hwS
      · rfl
      · rw [hS' w hwS, freeze_zero]
    exact (Formalism.GM.extendBijOn p (T.pos i + 1) r LLK ρ (n i) hS).1 f hfP _ (hcP w) (by rw [hfF, ← h5])
  have hfW : f ∈ WtSpC p LLK (T.pos i + 1) univ w := by
    rw [wtsp_iff, hcomp]
    exact weightedHomogeneousComponent_isWeightedHomogeneous w f
  have hfH : f ∈ HWC p LLK (T.pos i + 1) (univ.erase ρ) w := by
    refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
    · rw [WtSpC, mem_restrictSupport_iff] at hfW ⊢
      intro m hm c _
      exact hfW hm c (mem_univ c)
    · simp only [Submodule.mem_iInf, LinearMap.mem_ker]
      intro a b hab
      have ha : a ≠ ρ := (Finset.mem_erase.mp hab.1).1
      have hb : b ≠ ρ := (Finset.mem_erase.mp hab.2.1).1
      have h1 := glAct_freeze_gen LLK (n i) ρ a b ha hb f
      rw [hfF, hraise a b hab.2.2] at h1
      exact (Formalism.GM.extendBijOn p (T.pos i + 1) r LLK ρ (n i) hS).1 _
        (Formalism.GM.DimensionMonotonicity.glAct_pol LLK LLK (T.pos i + 1) a b hfP) 0 (Submodule.zero_mem _) (by rw [← h1, freeze_zero])
  refine ⟨f, Submodule.mem_inf.mpr ⟨Submodule.mem_inf.mpr ⟨Submodule.mem_inf.mpr ⟨hfY, hfH⟩, hfW⟩,
    (Submodule.mem_inf.mp hfZ).2⟩, ?_⟩
  rw [Ffull_eq, hfF]
  exact hF.symm

omit hρ

theorem Ffull_indep (Ω : Finset (Fin r → ℤ)) (nb : (Fin r → ℤ) → ℕ)
    (f : ∀ w, Fin (nb w) → MvPolynomial (Fin (T.pos i + 1) × Fin r) ℚ_[p])
    (hf : ∀ w a, f w a ∈ MMw p ((LL.setTies T n).takeD (T.pos i + 1)) T.J (T.thrUpTo i) ρ w)
    (hli : ∀ w, LinearIndependent ℚ_[p] (f w)) :
    LinearIndependent ℚ_[p] (fun x : (Σ w : Ω, Fin (nb w.1)) => T.Ffull p (LL.setTies T n) i ρ (n i) (f x.1.1 x.2)) := by
  classical
  set LLK := (LL.setTies T n).takeD (T.pos i + 1) with hLLK
  have hPf : ∀ w a, f w a ∈ Pol p r LLK := fun w a =>
    (Submodule.mem_inf.mp (Submodule.mem_inf.mp (Submodule.mem_inf.mp (hf w a)).1).1).1
  rw [Fintype.linearIndependent_iff]
  intro c hc x0
  have h1 : T.Ffull p (LL.setTies T n) i ρ (n i) (∑ x : (Σ w : Ω, Fin (nb w.1)), c x • f x.1.1 x.2) = 0 := by
    rw [← FfL_apply, map_sum, ← hc]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [map_smul, FfL_apply]
  have hsumP : (∑ x : (Σ w : Ω, Fin (nb w.1)), c x • f x.1.1 x.2) ∈ Pol p r LLK :=
    Submodule.sum_mem _ fun x _ => Submodule.smul_mem _ _ (hPf _ _)
  have h2 := Ffull_inj LL T hadm i ρ n hS _ hsumP h1
  have h3 := congrArg (weightedHomogeneousComponent (wv LLK (T.pos i + 1)) x0.1.1) h2
  rw [map_sum, map_zero, Fintype.sum_sigma] at h3
  have h4 : ∀ (w : Ω) (a : Fin (nb w.1)),
      weightedHomogeneousComponent (wv LLK (T.pos i + 1)) x0.1.1 (c ⟨w, a⟩ • f w.1 a) =
        if x0.1 = w then c ⟨w, a⟩ • f w.1 a else 0 := by
    intro w a
    have hW : IsWeightedHomogeneous (wv LLK (T.pos i + 1)) (f w.1 a) w.1 :=
      (wtsp_iff LLK (T.pos i + 1) w.1 _).mp (Submodule.mem_inf.mp (hf w.1 a)).2
    rw [map_smul, weightedHomogeneousComponent_of_mem hW]
    by_cases h : x0.1 = w
    · rw [if_pos h, if_pos (congrArg Subtype.val h)]
    · rw [if_neg h, if_neg (fun h' => h (Subtype.ext h')), smul_zero]
  simp only [h4] at h3
  rw [Finset.sum_eq_single x0.1 (fun w _ hw => by simp [Ne.symm hw]) (fun h => absurd (Finset.mem_univ _) h)] at h3
  simp only [if_true] at h3
  have := Fintype.linearIndependent_iff.mp (hli x0.1.1) (fun a => c ⟨x0.1, a⟩) h3 x0.2
  simpa using this

omit hadm hS

theorem mmw_finite :
    {w : Fin r → ℤ | MMw p ((LL.setTies T n).takeD (T.pos i + 1)) T.J (T.thrUpTo i) ρ w ≠ ⊥}.Finite := by
  classical
  refine ((pol_finite (r := r) ((LL.setTies T n).takeD (T.pos i + 1))).image
    (fun m => fun c => wt ((LL.setTies T n).takeD (T.pos i + 1)) (T.pos i + 1) c m)).subset ?_
  intro w hw
  obtain ⟨f, hf, hf0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hw
  have hP : f ∈ Pol p r ((LL.setTies T n).takeD (T.pos i + 1)) :=
    (Submodule.mem_inf.mp (Submodule.mem_inf.mp (Submodule.mem_inf.mp hf).1).1).1
  have hW := (Submodule.mem_inf.mp hf).2
  obtain ⟨m, hm⟩ : ∃ m, m ∈ f.support := by
    by_contra hc; push Not at hc
    exact hf0 (MvPolynomial.support_eq_empty.mp (Finset.eq_empty_of_forall_notMem hc))
  rw [Pol, mem_restrictSupport_iff] at hP
  rw [WtSpC, mem_restrictSupport_iff] at hW
  exact ⟨m, hP (Finset.mem_coe.mpr hm), funext fun c => hW (Finset.mem_coe.mpr hm) c (mem_univ c)⟩

end Comparison₂

end Formalism.CountingSumsFrames.TO

namespace Formalism.CountingSumsFrames.TO

open Formalism.GM Formalism.GM.M Formalism.GM.DimensionMonotonicity MvPolynomial Finset

variable {p : ℕ} [Fact p.Prime] {N r : ℕ}

structure IsEqC [NeZero r] (L : Letters N) (j0 : ℕ) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ)
    (φ : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p]) : Prop where
  comm : ∀ x ∈ Cset p L j0 J M, ∀ a b, φ (glAct p L j0 a b x) = glAct p L j0 a b (φ x)
  mem : ∀ x ∈ Cset p L j0 J M, φ x ∈ Cset p L j0 J M

noncomputable def inOp (L : Letters N) (j0 : ℕ)
    (Pi φ : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p] :=
  φ ∘ₗ Pi ∘ₗ psi p L j0

noncomputable def bigOp (L : Letters N) (j0 : ℕ)
    (Pi φ : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p] :=
  ext (fsj N r j0) (inOp L j0 Pi φ)

section Gen

variable {K : Type} [Field K] {σ : Type} [DecidableEq σ] (fs : σ → Prop) [DecidablePred fs]

theorem slc_ext (φ : MvPolynomial σ K →ₗ[K] MvPolynomial σ K) (hφ : ∀ x, IsF fs (φ x)) (m : σ →₀ ℕ)
    (x : MvPolynomial σ K) : slc fs m (ext fs φ x) = φ (slc fs m x) := by
  classical
  induction x using MvPolynomial.induction_on' with
  | monomial m' a =>
    rw [ext_monomial, map_smul, sl_mul fs m (hφ _) (isL_monomial_ltr fs m' 1), sl_monomial, coeff_monomial]
    split_ifs with h
    · rw [one_smul, ← map_smul, smul_monomial, smul_eq_mul, mul_one]
    · rw [zero_smul, smul_zero, map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]

end Gen

theorem slc_int (j0 : ℕ) (m : Fin N × Fin r →₀ ℕ) {x : MvPolynomial (Fin N × Fin r) ℚ_[p]}
    (hx : x ∈ IntPol p (Fin N × Fin r)) : slc (fsj N r j0) m x ∈ IntPol p (Fin N × Fin r) := by
  classical
  rw [x.as_sum, map_sum]
  refine Submodule.sum_mem _ fun m' _ => ?_
  rw [sl_monomial]
  split_ifs
  · refine TM.mem_intPol_of_norm _ fun k => ?_
    rw [coeff_monomial]
    split_ifs
    · exact intPol_norm x hx m'
    · simp
  · exact Submodule.zero_mem _

theorem int_of_mul_monomial {σ : Type} (g : MvPolynomial σ ℚ_[p]) (m : σ →₀ ℕ)
    (h : g * monomial m 1 ∈ IntPol p σ) : g ∈ IntPol p σ := by
  refine TM.mem_intPol_of_norm _ fun k => ?_
  have := intPol_norm _ h (k + m)
  rwa [coeff_mul_monomial, mul_one] at this

theorem int_monomial_one {σ : Type} (m : σ →₀ ℕ) : (monomial m 1 : MvPolynomial σ ℚ_[p]) ∈ IntPol p σ := by
  unfold Formalism.GM.M.IntPol
  exact LinearMap.mem_range.mpr ⟨monomial m 1, by simp [MvPolynomial.mapAlgHom_apply, MvPolynomial.map_monomial]⟩

theorem isWt_iff_wh (L : Letters N) (j : ℕ) (ν : Fin r → ℤ) (x : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    (GA p L j).IsWt ν x ↔ x ∈ weightedHomogeneousSubmodule ℚ_[p] (wv L j) ν := by
  constructor
  · intro h
    have h' : weightedHomogeneousComponent (wv L j) ν x = x := h
    rw [← h']
    exact weightedHomogeneousComponent_mem _ _ _
  · intro h
    show weightedHomogeneousComponent (wv L j) ν x = x
    rw [weightedHomogeneousComponent_of_mem h, if_pos rfl]

section

variable [NeZero r] (L : Letters N) (j0 e : ℕ) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ)
  (Pi φ : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
  (hPi : IsProjC L j0 e J M Pi) (hφ : IsEqC L j0 J M φ)

include hPi

theorem piPsi_mem (x : MvPolynomial (Fin N × Fin r) ℚ_[p]) : Pi (psi p L j0 x) ∈ Cset p L j0 J M :=
  Submodule.mem_inf.mpr ⟨hPi.pol (Lz L j0) rfl _ (psi_mem L j0 x), (Submodule.mem_iInf _).mpr fun k => hPi.ycond _ k⟩

theorem inOp_C (g : MvPolynomial (Fin N × Fin r) ℚ_[p]) (hg : g ∈ Cset p L j0 J M) : inOp L j0 Pi φ g = φ g := by
  obtain ⟨h1, h2⟩ := Submodule.mem_inf.mp hg
  simp only [inOp, LinearMap.comp_apply]
  rw [psi_id L j0 h1, hPi.fix (Lz L j0) rfl g h1 (fun k => (Submodule.mem_iInf _).mp h2 k)]

include hφ

theorem inOp_mem (x : MvPolynomial (Fin N × Fin r) ℚ_[p]) : inOp L j0 Pi φ x ∈ Cset p L j0 J M := by
  exact hφ.mem _ (piPsi_mem L j0 e J M Pi hPi x)

theorem inOp_isF (x : MvPolynomial (Fin N × Fin r) ℚ_[p]) : IsF (fsj N r j0) (inOp L j0 Pi φ x) := by
  exact isF_of_polLz L j0 (Submodule.mem_inf.mp (inOp_mem L j0 e J M Pi φ hPi hφ x)).1

theorem inOp_glAct (c d : Fin r) (x : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    inOp L j0 Pi φ (glAct p L j0 c d x) = glAct p L j0 c d (inOp L j0 Pi φ x) := by
  simp only [inOp, LinearMap.comp_apply]
  rw [psi_glAct, hPi.comm, hφ.comm _ (piPsi_mem L j0 e J M Pi hPi x)]

theorem eqC_wh (ν : Fin r → ℤ) (y : MvPolynomial (Fin N × Fin r) ℚ_[p]) (hy : y ∈ Cset p L j0 J M)
    (hw : y ∈ weightedHomogeneousSubmodule ℚ_[p] (wv L j0) ν) :
    φ y ∈ weightedHomogeneousSubmodule ℚ_[p] (wv L j0) ν := by
  rw [← isWt_iff_wh] at hw ⊢
  refine GlX.isWt_of_eig (GA p L j0) fun c => ?_
  have h1 : glAct p L j0 c c y = ((ν c : ℤ) : ℚ_[p]) • y := (GA p L j0).E_diag_of_isWt hw c
  show glAct p L j0 c c (φ y) = _
  rw [← hφ.comm y hy, h1, map_smul]

theorem inOp_wh (ν : Fin r → ℤ) (x : MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hx : x ∈ weightedHomogeneousSubmodule ℚ_[p] (wv L j0) ν) :
    inOp L j0 Pi φ x ∈ weightedHomogeneousSubmodule ℚ_[p] (wv L j0) ν := by
  simp only [inOp, LinearMap.comp_apply]
  exact eqC_wh L j0 e J M Pi φ hPi hφ ν _ (piPsi_mem L j0 e J M Pi hPi x) (hPi.wh ν _ (whc_keep _ _ _ _ hx))

theorem bigOp_glAct (c d : Fin r) (x : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    bigOp L j0 Pi φ (glAct p L j0 c d x) = glAct p L j0 c d (bigOp L j0 Pi φ x) := by
  exact ext_glAct L le_rfl _ (inOp_glAct L j0 e J M Pi φ hPi hφ) (inOp_isF L j0 e J M Pi φ hPi hφ) c d x

theorem bigOp_Y : ∀ y ∈ Y p L J M, bigOp L j0 Pi φ y ∈ Y p L J M := by
  exact ext_Y L j0 J M _ (inOp_glAct L j0 e J M Pi φ hPi hφ) (inOp_wh L j0 e J M Pi φ hPi hφ)
    (fun x => (Submodule.mem_inf.mp (inOp_mem L j0 e J M Pi φ hPi hφ x)).1)
    (fun x _ => inOp_mem L j0 e J M Pi φ hPi hφ x)

theorem bigOp_slc (m : Fin N × Fin r →₀ ℕ) (x : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    slc (fsj N r j0) m (bigOp L j0 Pi φ x) = inOp L j0 Pi φ (slc (fsj N r j0) m x) := by
  exact slc_ext _ _ (inOp_isF L j0 e J M Pi φ hPi hφ) m x

theorem bigOp_span (VF : Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]))
    (hVF : ∀ g ∈ Cset p L j0 J M, φ g ∈ VF) (x : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    bigOp L j0 Pi φ x ∈ Submodule.span ℚ_[p] {x | ∃ g ∈ VF,
      ∃ q ∈ MvPolynomial.supported ℚ_[p] {v : Fin N × Fin r | j0 ≤ (v.1 : ℕ)}, x = g * q} := by
  classical
  rw [bigOp, ext_eq_sum (fsj N r j0) _ x (x.support.image (ltr (fsj N r j0)))
    (fun m hm => Finset.mem_image_of_mem _ hm)]
  refine Submodule.sum_mem _ fun m hm => Submodule.subset_span ?_
  obtain ⟨m', _, rfl⟩ := Finset.mem_image.mp hm
  refine ⟨_, hVF _ (piPsi_mem L j0 e J M Pi hPi (slc (fsj N r j0) (ltr (fsj N r j0) m') x)), _, ?_, rfl⟩
  rw [mem_supported, vars_monomial one_ne_zero]
  intro v hv
  have := ltr_isL (fsj N r j0) m' v (Finsupp.mem_support_iff.mp (Finset.mem_coe.mp hv))
  simp only [fsj, not_lt] at this
  exact this

theorem bigOp_int
    (hint : ∀ μ v, v ∈ Cset p L j0 J M → (GA p L j0).IsHW μ v → v ∈ IntPol p (Fin N × Fin r) →
      φ v ∈ IntPol p (Fin N × Fin r))
    (la : Fin r → ℤ) (x : MvPolynomial (Fin N × Fin r) ℚ_[p]) (hx : x ∈ HWC p L j0 univ la ⊓ Pol p r L)
    (hxi : x ∈ IntPol p (Fin N × Fin r)) :
    ((p : ℚ_[p]) ^ e) • bigOp L j0 Pi φ x ∈ IntPol p (Fin N × Fin r) := by
  classical
  obtain ⟨hxH, hxP⟩ := Submodule.mem_inf.mp hx
  obtain ⟨hxW, hxE⟩ := (isHW_iff L j0 la x).mpr hxH
  rw [bigOp, ext_eq_sum (fsj N r j0) _ x (x.support.image (ltr (fsj N r j0)))
    (fun m hm => Finset.mem_image_of_mem _ hm), Finset.smul_sum]
  refine Submodule.sum_mem _ fun m hm => ?_
  obtain ⟨m', hm', rfl⟩ := Finset.mem_image.mp hm
  set s := slc (fsj N r j0) (ltr (fsj N r j0) m') x with hs
  have hsP : s ∈ Pol p r (Lz L j0) := slc_pol L j0 _ hxP
  have hsI : s ∈ IntPol p (Fin N × Fin r) := slc_int j0 _ hxi
  have hmd : MultiDeg L m' := ((MvPolynomial.mem_restrictSupport_iff ℚ_[p]).mp hxP) hm'
  have hsm : s * monomial (ltr (fsj N r j0) m') 1 ∈ PolZ p r L :=
    Submodule.mem_inf.mpr ⟨mul_ltr_pol L j0 hsP hmd, FrozenVariableLemmas.intPol_mul p hsI (int_monomial_one _)⟩
  have h1 := hPi.int _ hsm
  rw [hPi.mul _ _ (isL_monomial_ltr (fsj N r j0) m' 1), ← smul_mul_assoc] at h1
  have hvI : ((p : ℚ_[p]) ^ e) • Pi s ∈ IntPol p (Fin N × Fin r) := int_of_mul_monomial _ _ h1
  have hPs : Pi s ∈ Cset p L j0 J M := by
    have := piPsi_mem L j0 e J M Pi hPi s
    rwa [psi_id L j0 hsP] at this
  have hvC : ((p : ℚ_[p]) ^ e) • Pi s ∈ Cset p L j0 J M := Submodule.smul_mem _ _ hPs
  have hsW : s ∈ weightedHomogeneousSubmodule ℚ_[p] (wv L j0) la :=
    slc_wh L le_rfl _ ((isWt_iff_wh L j0 la x).mp hxW)
  have hvH : (GA p L j0).IsHW la (((p : ℚ_[p]) ^ e) • Pi s) := by
    refine ⟨(isWt_iff_wh L j0 la _).mpr (Submodule.smul_mem _ _ (hPi.wh la _ hsW)), fun a b hab => ?_⟩
    show glAct p L j0 a b _ = 0
    have h0 : glAct p L j0 a b x = 0 := hxE a b hab
    rw [map_smul, ← hPi.comm, hs, ← slc_glAct L le_rfl a b, h0, map_zero, map_zero, smul_zero]
  have h2 := hint la _ hvC hvH hvI
  rw [map_smul] at h2
  have e3 : inOp L j0 Pi φ s = φ (Pi s) := by
    simp only [inOp, LinearMap.comp_apply]; rw [psi_id L j0 hsP]
  rw [e3, ← smul_mul_assoc]
  exact FrozenVariableLemmas.intPol_mul p h2 (int_monomial_one _)

end

end Formalism.CountingSumsFrames.TO

namespace Formalism.CountingSumsFrames.TO

open Formalism.GM Formalism.GM.M Formalism.GM.DimensionMonotonicity MvPolynomial Finset

variable {p : ℕ} [Fact p.Prime] {N r : ℕ}

noncomputable def YYs [NeZero r] (L : Letters N) (j0 : ℕ) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ)
    (v : MvPolynomial (Fin N × Fin r) ℚ_[p]) : Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]) :=
  Y p L J M ⊓ Submodule.span ℚ_[p] {x | ∃ g ∈ (GA p L j0).gS {v},
      ∃ q ∈ MvPolynomial.supported ℚ_[p] {v : Fin N × Fin r | j0 ≤ (v.1 : ℕ)}, x = g * q}

theorem eq_of_slc {K : Type} [Field K] {σ : Type} [DecidableEq σ] (fs : σ → Prop) [DecidablePred fs]
    (x y : MvPolynomial σ K) (hxy : ∀ m, slc fs m x = slc fs m y) : x = y := by
  classical
  have hx := eq_sum_sl fs x ((x.support ∪ y.support).image (ltr fs))
    (fun m hm => Finset.mem_image_of_mem _ (Finset.mem_union_left _ hm))
  have hy := eq_sum_sl fs y ((x.support ∪ y.support).image (ltr fs))
    (fun m hm => Finset.mem_image_of_mem _ (Finset.mem_union_right _ hm))
  exact hx.trans ((Finset.sum_congr rfl fun m _ => by rw [hxy m]).trans hy.symm)

theorem finrank_biSup_le {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V] (Yv : Submodule K V)
    [FiniteDimensional K Yv] (A : ι → Submodule K V) (hA : ∀ i, A i ≤ Yv) (s : Finset ι) :
    Module.finrank K (⨆ i ∈ s, A i : Submodule K V) ≤ ∑ i ∈ s, Module.finrank K (A i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have : (⨆ i ∈ (∅ : Finset ι), A i : Submodule K V) = ⊥ := by simp
    rw [this]; simp
  | insert a s ha ih =>
    rw [Finset.iSup_insert, Finset.sum_insert ha]
    have : FiniteDimensional K (A a) := Submodule.finiteDimensional_of_le (hA a)
    have : FiniteDimensional K (⨆ i ∈ s, A i : Submodule K V) :=
      Submodule.finiteDimensional_of_le (iSup₂_le fun i _ => hA i)
    exact (Submodule.finrank_add_le_finrank_add_finrank _ _).trans (Nat.add_le_add_left ih _)

theorem isHW_zero {K V : Type} [Field K] [AddCommGroup V] [Module K V] {r : ℕ} (G : GlW K V r) (μ : Fin r → ℤ) :
    G.IsHW μ 0 := by
  unfold Formalism.GM.DimensionMonotonicity.GlW.IsHW Formalism.GM.DimensionMonotonicity.GlW.IsWt
  exact ⟨map_zero _, fun a b _ => map_zero _⟩

theorem C_finW [NeZero r] (L : Letters N) (j0 : ℕ) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ) :
    (GA p (r := r) L j0).FinW (Cset p L j0 J M) := by
  obtain ⟨S, hS⟩ := polynomial_finite_weights (p := p) (r := r) L j0
  exact ⟨S, fun x hx => hS x (Submodule.mem_inf.mp hx).1⟩

theorem Y_fd [NeZero r] (L : Letters N) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ) :
    FiniteDimensional ℚ_[p] (Y p (r := r) L J M) := by
  have := pol_fd (p := p) (r := r) L
  exact Submodule.finiteDimensional_of_le (inf_le_left : Y p (r := r) L J M ≤ Pol p r L)

theorem slc_span (L : Letters N) (j0 : ℕ) (VF : Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]))
    (hVF : VF ≤ Pol p r (Lz L j0)) {z : MvPolynomial (Fin N × Fin r) ℚ_[p]}
    (hz : z ∈ Submodule.span ℚ_[p] {x | ∃ g ∈ VF,
      ∃ q ∈ MvPolynomial.supported ℚ_[p] {v : Fin N × Fin r | j0 ≤ (v.1 : ℕ)}, x = g * q})
    (m : Fin N × Fin r →₀ ℕ) : slc (fsj N r j0) m z ∈ VF := by
  classical
  obtain ⟨s, a, hs, ha, rfl⟩ := rep_span VF j0 hz
  rw [map_sum]
  refine Submodule.sum_mem _ fun b hb => ?_
  have hL : IsL (fsj N r j0) (monomial b (1 : ℚ_[p])) := by
    intro m' hm' v hv hfs
    have : m' = b := Finset.mem_singleton.mp (support_monomial_subset hm')
    subst this
    exact hv (hs m' hb v hfs)
  rw [sl_mul (fsj N r j0) m (isF_of_polLz L j0 (hVF (ha b))) hL]
  exact VF.smul_mem _ (ha b)

section

variable [NeZero r] (L : Letters N) (j0 e : ℕ) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ)
  (Pi : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
  (hPi : IsProjC L j0 e J M Pi)
  {ι : Type} [Fintype ι] [DecidableEq ι] (h : ι → MvPolynomial (Fin N × Fin r) ℚ_[p]) (la : ι → Fin r → ℤ)
  (hh : ∀ i, (GA p L j0).IsHW (la i) (h i)) (hhC : ∀ i, h i ∈ Cset p L j0 J M)
  (hli : LinearIndependent ℚ_[p] h) (hsp : Cset p (r := r) L j0 J M ≤ ⨆ i, (GA p L j0).gS {h i})

include hPi hh hhC hli hsp

theorem count_le (bad : ι → Prop) [DecidablePred bad]
    (ϖ : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hϖ : IsEqC L j0 J M ϖ) (hgood : ∀ i, ¬ bad i → ∀ x ∈ (GA p L j0).gS {h i}, ϖ x = x)
    (hbad : ∀ i, bad i → ∀ x ∈ (GA p L j0).gS {h i}, ϖ x = 0) :
    Module.finrank ℚ_[p] (Y p (r := r) L J M) -
      Module.finrank ℚ_[p] ((Y p L J M ⊓ LinearMap.ker (bigOp L j0 Pi ϖ - LinearMap.id) :
        Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]))) ≤
      ∑ i ∈ univ.filter bad, Module.finrank ℚ_[p] (YYs L j0 J M (h i)) := by
  classical
  have hex : ∀ i : ι, ∃ φ : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p],
      IsEqC L j0 J M φ ∧ (∀ x ∈ (GA p (r := r) L j0).gS {h i}, φ x = x) ∧
        (∀ k, k ≠ i → ∀ x ∈ (GA p (r := r) L j0).gS {h k}, φ x = 0) := by
    intro i
    obtain ⟨φ, -, hφE, hφC, -, -, hφ1, hφ0⟩ := GlX.eqExt (GA p (r := r) L j0) (C_stable L j0 J M)
      (C_finW L j0 J M) h (fun k => if k = i then h k else 0) la hh hhC hli hsp
      (fun k => by
        by_cases hk : k = i
        · simpa [hk] using hh i
        · simpa [hk] using isHW_zero (GA p (r := r) L j0) (la k))
      (fun k => by
        by_cases hk : k = i
        · simpa [hk] using hhC i
        · simp [hk])
    exact ⟨φ, ⟨hφE, hφC⟩, hφ1 i (by simp), fun k hk => hφ0 k (by simp [hk])⟩
  choose π hπEq hπ1 hπ0 using hex

  have hπVF : ∀ i, ∀ g ∈ Cset p L j0 J M, π i g ∈ (GA p (r := r) L j0).gS {h i} := by
    intro i g hg
    refine Submodule.iSup_induction _ (motive := fun x => π i x ∈ (GA p (r := r) L j0).gS {h i}) (hsp hg) ?_
      (by simp) (fun x y hx hy => by rw [map_add]; exact add_mem hx hy)
    intro k x hx
    by_cases hk : k = i
    · subst hk; rw [hπ1 k x hx]; exact hx
    · rw [hπ0 i k hk x hx]; exact zero_mem _

  have hdec : ∀ g ∈ Cset p L j0 J M, g - ϖ g = ∑ i ∈ univ.filter bad, π i g := by
    intro g hg
    refine Submodule.iSup_induction _ (motive := fun x => x - ϖ x = ∑ i ∈ univ.filter bad, π i x) (hsp hg) ?_
      (by simp) (fun x y hx hy => by
        simp only [map_add, Finset.sum_add_distrib, ← hx, ← hy]; abel)
    intro k x hx
    by_cases hk : bad k
    · rw [hbad k hk x hx, sub_zero, Finset.sum_eq_single k (fun i _ hik => hπ0 i k (Ne.symm hik) x hx)
        (fun hk' => absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk⟩) hk'), hπ1 k x hx]
    · rw [hgood k hk x hx, sub_self]
      refine (Finset.sum_eq_zero fun i hi => hπ0 i k ?_ x hx).symm
      rintro rfl
      exact hk (Finset.mem_filter.mp hi).2

  have hdecY : ∀ y ∈ Y p L J M, y - bigOp L j0 Pi ϖ y = ∑ i ∈ univ.filter bad, bigOp L j0 Pi (π i) y := by
    intro y hy
    apply eq_of_slc (fsj N r j0)
    intro m
    have hc := slc_C L j0 J M hy m
    rw [map_sub, map_sum, bigOp_slc L j0 e J M Pi ϖ hPi hϖ m y, inOp_C L j0 e J M Pi ϖ hPi _ hc, hdec _ hc]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [bigOp_slc L j0 e J M Pi (π i) hPi (hπEq i) m y, inOp_C L j0 e J M Pi (π i) hPi _ hc]
  have hfd := Y_fd (p := p) (r := r) L J M
  set Z : Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]) := ⨆ i ∈ univ.filter bad, YYs L j0 J M (h i) with hZ
  have hZY : Z ≤ Y p L J M := iSup₂_le fun i _ => inf_le_left
  have hZfd : FiniteDimensional ℚ_[p] Z := Submodule.finiteDimensional_of_le hZY
  set f : Y p (r := r) L J M →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p] :=
    (bigOp L j0 Pi ϖ - LinearMap.id) ∘ₗ (Y p (r := r) L J M).subtype with hf
  have hran : LinearMap.range f ≤ Z := by
    rintro _ ⟨y, rfl⟩
    have h1 : f y = -(∑ i ∈ univ.filter bad, bigOp L j0 Pi (π i) y.1) := by
      rw [← hdecY y.1 y.2]; simp [hf]
    rw [h1]
    refine Z.neg_mem (Submodule.sum_mem _ fun i hi => ?_)
    refine (le_iSup₂ (f := fun i (_ : i ∈ univ.filter bad) => YYs L j0 J M (h i)) i hi) ?_
    exact Submodule.mem_inf.mpr ⟨bigOp_Y L j0 e J M Pi (π i) hPi (hπEq i) y.1 y.2,
      bigOp_span L j0 e J M Pi (π i) hPi (hπEq i) _ (hπVF i) y.1⟩
  have hker : Module.finrank ℚ_[p] (LinearMap.ker f) =
      Module.finrank ℚ_[p] ((Y p L J M ⊓ LinearMap.ker (bigOp L j0 Pi ϖ - LinearMap.id) :
        Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]))) := by
    rw [hf, LinearMap.ker_comp, ← Submodule.map_comap_subtype, Submodule.finrank_map_subtype_eq]
  have hrn := LinearMap.finrank_range_add_finrank_ker f
  have h1 : Module.finrank ℚ_[p] (LinearMap.range f) ≤ Module.finrank ℚ_[p] Z := Submodule.finrank_mono hran
  have h2 : Module.finrank ℚ_[p] Z ≤ ∑ i ∈ univ.filter bad, Module.finrank ℚ_[p] (YYs L j0 J M (h i)) :=
    finrank_biSup_le (Y p (r := r) L J M) (fun i => YYs L j0 J M (h i)) (fun i => inf_le_left) (univ.filter bad)
  rw [← hker]
  omega

theorem transport_le (i0 : ι) (v : MvPolynomial (Fin N × Fin r) ℚ_[p]) (hv : (GA p L j0).IsHW (la i0) v)
    (hvC : v ∈ Cset p L j0 J M) (hv0 : v ≠ 0) :
    Module.finrank ℚ_[p] (YYs L j0 J M (h i0)) ≤ Module.finrank ℚ_[p] (YYs L j0 J M v) := by
  classical
  obtain ⟨φ, -, hφE, hφC, hφg, hφinj, -, hφ0⟩ := GlX.eqExt (GA p (r := r) L j0) (C_stable L j0 J M)
    (C_finW L j0 J M) h (fun k => if k = i0 then v else 0) la hh hhC hli hsp
    (fun k => by
      by_cases hk : k = i0
      · subst hk; simpa using hv
      · simpa [hk] using isHW_zero (GA p (r := r) L j0) (la k))
    (fun k => by
      by_cases hk : k = i0
      · simpa [hk] using hvC
      · simp [hk])
  have hEq : IsEqC L j0 J M φ := ⟨hφE, hφC⟩
  have hVF : ∀ g ∈ Cset p L j0 J M, φ g ∈ (GA p (r := r) L j0).gS {v} := by
    intro g hg
    refine Submodule.iSup_induction _ (motive := fun x => φ x ∈ (GA p (r := r) L j0).gS {v}) (hsp hg) ?_
      (by simp) (fun x y hx hy => by rw [map_add]; exact add_mem hx hy)
    intro k x hx
    by_cases hk : k = i0
    · subst hk
      have := hφg k x hx
      simpa using this
    · rw [hφ0 k (by simp [hk]) x hx]; exact zero_mem _
  have hgSC : (GA p (r := r) L j0).gS {h i0} ≤ Cset p L j0 J M :=
    (GA p (r := r) L j0).gS_le (by simpa using hhC i0) (C_stable L j0 J M)
  have hmap : ∀ z ∈ YYs L j0 J M (h i0), bigOp L j0 Pi φ z ∈ YYs L j0 J M v := fun z hz =>
    Submodule.mem_inf.mpr ⟨bigOp_Y L j0 e J M Pi φ hPi hEq z (Submodule.mem_inf.mp hz).1,
      bigOp_span L j0 e J M Pi φ hPi hEq _ hVF z⟩
  have hinj : ∀ z ∈ YYs L j0 J M (h i0), bigOp L j0 Pi φ z = 0 → z = 0 := by
    intro z hz h0
    apply eq_of_slc (fsj N r j0)
    intro m
    have h1 : slc (fsj N r j0) m z ∈ (GA p (r := r) L j0).gS {h i0} :=
      slc_span L j0 _ (hgSC.trans inf_le_left) (Submodule.mem_inf.mp hz).2 m
    have h2 := bigOp_slc L j0 e J M Pi φ hPi hEq m z
    rw [h0, map_zero, inOp_C L j0 e J M Pi φ hPi _ (hgSC h1)] at h2
    rw [map_zero]
    exact hφinj i0 (by simpa using hv0) _ h1 h2.symm
  have hfd := Y_fd (p := p) (r := r) L J M
  have : FiniteDimensional ℚ_[p] (YYs L j0 J M v) :=
    Submodule.finiteDimensional_of_le (inf_le_left : YYs L j0 J M v ≤ Y p L J M)
  refine LinearMap.finrank_le_finrank_of_injective (f := (bigOp L j0 Pi φ).restrict hmap) ?_
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro z hz
  apply Subtype.ext
  apply hinj z.1 z.2
  exact congrArg Subtype.val hz

end

end Formalism.CountingSumsFrames.TO

namespace Formalism.CountingSumsFrames.TO

open Formalism.GM Formalism.GM.M Formalism.GM.DimensionMonotonicity MvPolynomial Finset

variable {p : ℕ} [Fact p.Prime]

theorem int_smul_mem {σ : Type} (S : Submodule ℤ_[p] (MvPolynomial σ ℚ_[p])) (c : ℚ_[p]) (hc : ‖c‖ ≤ 1)
    (x : MvPolynomial σ ℚ_[p]) (hx : x ∈ S) : c • x ∈ S := by
  have h := S.smul_mem (⟨c, hc⟩ : ℤ_[p]) hx
  first
    | exact h
    | (convert h using 1; ext m; simp [MvPolynomial.coeff_smul]; done)
    | (convert h using 1; ext m; simp [MvPolynomial.coeff_smul, Algebra.smul_def]; done)

theorem smith_bases {σ : Type} (nb : ℕ) (f : Fin nb → MvPolynomial σ ℚ_[p])
    (Lat : Submodule ℤ_[p] (MvPolynomial σ ℚ_[p]))
    (hli : LinearIndependent ℤ_[p] f) (hsp : Submodule.span ℤ_[p] (Set.range f) = Lat)
    (B : MvPolynomial σ ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial σ ℚ_[p] →ₗ[ℚ_[p]] ℚ_[p])
    (U V : Matrix (Fin nb) (Fin nb) ℚ_[p]) (dg : Fin nb → ℚ_[p])
    (hU : ∀ x y, ‖U x y‖ ≤ 1) (hV : ∀ x y, ‖V x y‖ ≤ 1) (hUd : ‖U.det‖ = 1) (hVd : ‖V.det‖ = 1)
    (hfac : (Matrix.of fun x y => B (f x) (f y)) = U * Matrix.diagonal dg * V) :
    ∃ f' f'' : Fin nb → MvPolynomial σ ℚ_[p], (∀ a, f' a ∈ Lat) ∧ (∀ a, f'' a ∈ Lat) ∧
      LinearIndependent ℚ_[p] f' ∧ Lat ≤ Submodule.span ℤ_[p] (Set.range f') ∧
      ∀ a b, B (f' a) (f'' b) = if a = b then dg a else 0 := by
  classical
  have hUu : IsUnit U.det := by
    rw [isUnit_iff_ne_zero]; intro h; rw [h, norm_zero] at hUd; exact zero_ne_one hUd
  have hVu : IsUnit V.det := by
    rw [isUnit_iff_ne_zero]; intro h; rw [h, norm_zero] at hVd; exact zero_ne_one hVd
  have hUi := fun x y => DetBound.norm_inv_entry_le U hU hUd x y
  have hVi := fun x y => DetBound.norm_inv_entry_le V hV hVd x y
  have hliQ : LinearIndependent ℚ_[p] f := (LinearIndependent.iff_fractionRing ℤ_[p] ℚ_[p]).mp hli
  have hfL : ∀ x, f x ∈ Lat := fun x => hsp ▸ Submodule.subset_span ⟨x, rfl⟩
  have hback : ∀ x, f x = ∑ a, U x a • ∑ y, U⁻¹ a y • f y := by
    intro x
    simp only [Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_smul]
    have : ∀ y, ∑ a, U x a * U⁻¹ a y = (1 : Matrix (Fin nb) (Fin nb) ℚ_[p]) x y := by
      intro y
      rw [← Matrix.mul_nonsing_inv U hUu, Matrix.mul_apply]
    simp only [this, Matrix.one_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  refine ⟨fun a => ∑ x, U⁻¹ a x • f x, fun b => ∑ y, V⁻¹ y b • f y, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun a => Lat.sum_mem fun x _ => int_smul_mem Lat _ (hUi a x) _ (hfL x)
  · exact fun b => Lat.sum_mem fun y _ => int_smul_mem Lat _ (hVi y b) _ (hfL y)
  · rw [Fintype.linearIndependent_iff]
    intro g hg
    simp only [Finset.smul_sum, smul_smul] at hg
    rw [Finset.sum_comm] at hg
    simp only [← Finset.sum_smul] at hg
    have h0 := Fintype.linearIndependent_iff.mp hliQ _ hg
    have h1 : Matrix.vecMul g U⁻¹ = 0 := by
      funext x
      simpa [Matrix.vecMul, dotProduct] using h0 x
    have h2 : Matrix.vecMul (Matrix.vecMul g U⁻¹) U = g := by
      rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul U hUu, Matrix.vecMul_one]
    intro a
    rw [← h2, h1, Matrix.zero_vecMul]; rfl
  · rw [← hsp, Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    rw [hback x]
    exact Submodule.sum_mem _ fun a _ => int_smul_mem _ _ (hU x a) _ (Submodule.subset_span ⟨a, rfl⟩)
  · intro a b
    have e : B (∑ x, U⁻¹ a x • f x) (∑ y, V⁻¹ y b • f y) =
        (U⁻¹ * (Matrix.of fun x y => B (f x) (f y)) * V⁻¹) a b := by
      simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, Matrix.mul_apply,
        Matrix.of_apply, Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
      ring
    rw [e, hfac]
    have : U⁻¹ * (U * Matrix.diagonal dg * V) * V⁻¹ = Matrix.diagonal dg := by
      rw [Matrix.mul_assoc U, ← Matrix.mul_assoc U⁻¹, Matrix.nonsing_inv_mul U hUu, Matrix.one_mul, Matrix.mul_assoc,
        Matrix.mul_nonsing_inv V hVu, Matrix.mul_one]
    rw [this, Matrix.diagonal_apply]

theorem good_norm (E : ℝ) (hE : 0 ≤ E) (d : ℚ_[p]) (hd : ¬ ‖d‖ < (p : ℝ) ^ (-E)) :
    ‖(p : ℚ_[p]) ^ ⌊E⌋₊ / d‖ ≤ 1 ∧ d ≠ 0 := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hp0 : (0 : ℝ) < p := by linarith
  have hd0 : d ≠ 0 := by
    intro h
    apply hd
    rw [h, norm_zero]
    exact Real.rpow_pos_of_pos hp0 _
  refine ⟨?_, hd0⟩
  rw [not_lt, Padic.norm_eq_zpow_neg_valuation hd0, ← Real.rpow_intCast, Real.rpow_le_rpow_left_iff hp1] at hd
  have hk : ((d.valuation : ℤ) : ℝ) ≤ E := by push_cast at hd; linarith
  have hk' : d.valuation ≤ (⌊E⌋₊ : ℤ) := by
    by_cases h0 : d.valuation ≤ 0
    · exact h0.trans (Int.natCast_nonneg _)
    · push Not at h0
      have h1 : ((d.valuation.toNat : ℕ) : ℝ) ≤ E := by
        have : ((d.valuation.toNat : ℕ) : ℤ) = d.valuation := Int.toNat_of_nonneg h0.le
        calc ((d.valuation.toNat : ℕ) : ℝ) = (((d.valuation.toNat : ℕ) : ℤ) : ℝ) := by push_cast; rfl
          _ = ((d.valuation : ℤ) : ℝ) := by rw [this]
          _ ≤ E := hk
      have h2 := Nat.le_floor h1
      omega
  rw [norm_div, norm_pow, Padic.norm_p, Padic.norm_eq_zpow_neg_valuation hd0, div_le_one (zpow_pos hp0 _),
    inv_pow, ← zpow_natCast, ← zpow_neg]
  exact zpow_le_zpow_right₀ hp1.le (by omega)

theorem K_bound (N r a j0 : ℕ) (κ : ℝ) (hr : 2 ≤ r) (hj0 : j0 ≤ N)
    (hκ : ((N + 2) * r ^ 2 : ℝ) * lgV2 p a r ≤ κ) :
    ((⌈κ / (N + 2)⌉₊ * j0 + 2 * ⌈κ / (N + 2)⌉₊ : ℕ) : ℝ) ≤ 3 * κ := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hlg1 : 1 ≤ lgV2 p a r := by
    unfold lgV2
    have : (1 : ℝ) ≤ 8 * (a : ℝ) + r := by
      have : (2 : ℝ) ≤ r := by exact_mod_cast hr
      have : (0 : ℝ) ≤ a := Nat.cast_nonneg a
      linarith
    have := Real.logb_nonneg hp1 this
    linarith
  have hr2 : (4 : ℝ) ≤ (r : ℝ) ^ 2 := by
    have : (2 : ℝ) ≤ r := by exact_mod_cast hr
    nlinarith
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hκN : ((N : ℝ) + 2) * 4 ≤ κ := by
    have h1 : ((N : ℝ) + 2) * 4 ≤ ((N : ℝ) + 2) * (r : ℝ) ^ 2 := mul_le_mul_of_nonneg_left hr2 (by positivity)
    have h2 : ((N : ℝ) + 2) * (r : ℝ) ^ 2 ≤ ((N : ℝ) + 2) * (r : ℝ) ^ 2 * lgV2 p a r :=
      le_mul_of_one_le_right (by positivity) hlg1
    linarith
  have hκ0 : 0 ≤ κ := by nlinarith
  have hce : ((⌈κ / (N + 2)⌉₊ : ℕ) : ℝ) < κ / (N + 2) + 1 := Nat.ceil_lt_add_one (by positivity)
  have hj : (j0 : ℝ) ≤ N := by exact_mod_cast hj0
  have hj' : (0 : ℝ) ≤ j0 := Nat.cast_nonneg j0
  have h3 : κ / (N + 2) * (N + 2) = κ := by
    field_simp
  push_cast
  calc ((⌈κ / (N + 2)⌉₊ : ℕ) : ℝ) * j0 + 2 * ((⌈κ / (N + 2)⌉₊ : ℕ) : ℝ)
      = ((⌈κ / (N + 2)⌉₊ : ℕ) : ℝ) * (j0 + 2) := by ring
    _ ≤ (κ / (N + 2) + 1) * (j0 + 2) := mul_le_mul_of_nonneg_right hce.le (by positivity)
    _ ≤ (κ / (N + 2) + 1) * (N + 2) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ = κ / (N + 2) * (N + 2) + (N + 2) := by ring
    _ ≤ 3 * κ := by rw [h3]; linarith

theorem S_eq_total {N : ℕ} (L : Letters N) (T : TieData) (i : Fin T.t) (h : T.pos i + 1 < N) :
    (L.takeD (T.pos i + 1)).total = T.S L i := by
  classical
  let F : ℕ → ℕ := fun k => if hk : k < N then L.deg ⟨k, hk⟩ else 0
  have h1 : (L.takeD (T.pos i + 1)).total = ∑ k ∈ range (T.pos i + 1), F k := by
    rw [← Fin.sum_univ_eq_sum_range]
    rfl
  have h2 : T.S L i = ∑ k ∈ range N, if k ≤ T.pos i then F k else 0 := by
    rw [← Fin.sum_univ_eq_sum_range (fun k => if k ≤ T.pos i then F k else 0) N]
    unfold TieData.S
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [F, a.isLt, dif_pos, Fin.eta]
  rw [h1, h2, ← Finset.sum_filter]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext k
  simp only [Finset.mem_range, Finset.mem_filter]
  omega

end Formalism.CountingSumsFrames.TO

namespace Formalism.CountingSumsFrames.TO

open Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.GM.DimensionMonotonicity MvPolynomial Finset

variable {p : ℕ} [Fact p.Prime] {N r : ℕ}

theorem smul_int {σ : Type} {c : ℚ_[p]} (hc : ‖c‖ ≤ 1) {x : MvPolynomial σ ℚ_[p]} (hx : x ∈ IntPol p σ) :
    c • x ∈ IntPol p σ := int_smul_mem (IntPol p σ) c hc x hx

theorem norm_p_pow_le (k : ℕ) : ‖(p : ℚ_[p]) ^ k‖ ≤ 1 := by
  rw [norm_pow]
  exact pow_le_one₀ (norm_nonneg _) (by rw [Padic.norm_p]; exact inv_le_one_of_one_le₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt.le))

theorem exists_pow_int {σ : Type} (v : MvPolynomial σ ℚ_[p]) : ∃ k : ℕ, ((p : ℚ_[p]) ^ k) • v ∈ IntPol p σ := by
  classical
  induction v using MvPolynomial.induction_on' with
  | monomial m a =>
    have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
    obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt ‖a‖ hp1
    refine ⟨k, mem_intPol_of_norm _ fun m' => ?_⟩
    rw [coeff_smul, coeff_monomial, smul_eq_mul]
    split_ifs
    · rw [norm_mul, norm_pow, Padic.norm_p, inv_pow]
      rw [inv_mul_le_iff₀ (by positivity), mul_one]
      exact hk.le
    · simp
  | add x y hx hy =>
    obtain ⟨k1, h1⟩ := hx
    obtain ⟨k2, h2⟩ := hy
    refine ⟨k1 + k2, ?_⟩
    have e : ((p : ℚ_[p]) ^ (k1 + k2)) • (x + y) =
        ((p : ℚ_[p]) ^ k2) • (((p : ℚ_[p]) ^ k1) • x) + ((p : ℚ_[p]) ^ k1) • (((p : ℚ_[p]) ^ k2) • y) := by
      rw [smul_add, smul_smul, smul_smul, pow_add]
      congr 2; ring
    rw [e]
    exact Submodule.add_mem _ (smul_int (norm_p_pow_le k2) h1) (smul_int (norm_p_pow_le k1) h2)

theorem Cset_thrUpTo [NeZero r] (L : Letters N) (T : TieData) (i : Fin T.t) :
    Cset p (r := r) L (T.pos i + 1 + 1) T.J (T.thrUpTo i) = Cset p L (T.pos i + 1 + 1) T.J T.thr := by
  unfold Cset
  congr 1
  refine iInf_congr fun k => ?_
  unfold Mup TieData.thrUpTo
  by_cases h : T.J k < T.pos i + 1 + 1
  · rw [if_pos h, if_pos h, if_pos (by omega)]
  · rw [if_neg h, if_neg h]

theorem YYsp_eq [NeZero N] [NeZero r] (LL : Letters N) (T : TieData) (i : Fin T.t) (ρ : Fin r) (n : Fin T.t → ℕ)
    (f : MvPolynomial (Fin (T.pos i + 1) × Fin r) ℚ_[p]) :
    T.YYsp p LL i ρ n f =
      YYs (LL.setTies T n) (T.pos i + 1 + 1) T.J T.thr (T.Ffull p (LL.setTies T n) i ρ (n i) f) := by
  unfold TieData.YYsp YYs
  rw [gSpan_eq]
  rfl

theorem isHW_smul (L : Letters N) (j : ℕ) (la : Fin r → ℤ) (c : ℚ_[p]) {x : MvPolynomial (Fin N × Fin r) ℚ_[p]}
    (hx : (GA p L j).IsHW la x) : (GA p L j).IsHW la (c • x) := by
  rw [isHW_iff] at hx ⊢
  exact Submodule.smul_mem _ _ hx

theorem isHW_zero' (L : Letters N) (j : ℕ) (la : Fin r → ℤ) :
    (GA p L j).IsHW la (0 : MvPolynomial (Fin N × Fin r) ℚ_[p]) := by
  rw [isHW_iff]
  exact Submodule.zero_mem _

theorem tie_core [NeZero r] (L : Letters N) (T : TieData) (hadm : T.Admissible L) (i : Fin T.t) (ρ : Fin r) (e1 : ℕ)
    (hK : T.pos i + 1 + 1 ≤ N) (hHP : HypP p L ρ e1) (hHW : HypW p (r := r) L e1) (E : ℝ) (hE : 0 ≤ E)
    {ι : Type} [Fintype ι] [DecidableEq ι] (h' h'' : ι → MvPolynomial (Fin N × Fin r) ℚ_[p]) (la : ι → Fin r → ℤ)
    (hh : ∀ x, (GA p L (T.pos i + 1 + 1)).IsHW (la x) (h' x))
    (hhC : ∀ x, h' x ∈ Cset p L (T.pos i + 1 + 1) T.J T.thr)
    (hli : LinearIndependent ℚ_[p] h')
    (hspZ : ∀ μ v, v ∈ Cset p L (T.pos i + 1 + 1) T.J T.thr → (GA p L (T.pos i + 1 + 1)).IsHW μ v →
      v ∈ IntPol p (Fin N × Fin r) → v ∈ Submodule.span ℤ_[p] (Set.range h'))
    (hh2 : ∀ x, (GA p L (T.pos i + 1 + 1)).IsHW (la x) (h'' x))
    (hh2C : ∀ x, h'' x ∈ Cset p L (T.pos i + 1 + 1) T.J T.thr)
    (hh2i : ∀ x, h'' x ∈ IntPol p (Fin N × Fin r))
    (d : ι → ℚ_[p]) (cst : ℚ_[p])
    (hdiag : ∀ x y, la x = la y → cst * fock p (T.phi p L i (h' x)) (h'' y) = if x = y then d x else 0)
    (hG0 : ∀ x y, ‖cst * fock p (h' x) (h' y)‖ ≤ 1)
    (vv : ι → MvPolynomial (Fin N × Fin r) ℚ_[p]) (hvv : ∀ x, (GA p L (T.pos i + 1 + 1)).IsHW (la x) (vv x))
    (hvvC : ∀ x, vv x ∈ Cset p L (T.pos i + 1 + 1) T.J T.thr) (hvv0 : ∀ x, vv x ≠ 0) :
    ∃ Tm πm : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p],
      (∀ y ∈ Y p (r := r) L T.J T.thr, Tm y ∈ Y p (r := r) L T.J T.thr) ∧
      (∀ y ∈ YZ p (r := r) L T.J T.thr,
        ((p : ℚ_[p]) ^ (e1 * (T.pos i + 1 + 1) + 2 * e1)) • Tm y ∈ IntPol p (Fin N × Fin r)) ∧
      (∀ u ∈ Y p (r := r) L T.J (T.thrUpTo i), ∀ u' ∈ Y p (r := r) L T.J T.thr,
        fockN p L (T.phi p L i u) (Tm u') = (p : ℚ_[p]) ^ ⌊E⌋₊ * fockN p L (πm u) u') ∧
      (∀ j : Fin T.t, i < j → ∀ u, πm (T.phi p L j u) = T.phi p L j (πm u)) ∧
      Module.finrank ℚ_[p] (Y p (r := r) L T.J T.thr) -
        Module.finrank ℚ_[p] ((Y p (r := r) L T.J T.thr ⊓ LinearMap.ker (πm - LinearMap.id) :
          Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]))) ≤
        ∑ x ∈ univ.filter (fun x => ‖d x‖ < (p : ℝ) ^ (-E)),
          Module.finrank ℚ_[p] (YYs L (T.pos i + 1 + 1) T.J T.thr (vv x)) := by
  classical
  obtain ⟨Pi, hPi⟩ := projC L ρ e1 (T.pos i + 1 + 1) hK hHP T.J T.thr
  have hCst := C_stable (p := p) (r := r) L (T.pos i + 1 + 1) T.J T.thr
  have hCf : (GA p L (T.pos i + 1 + 1)).FinW (Cset p (r := r) L (T.pos i + 1 + 1) T.J T.thr) := by
    obtain ⟨S, hS⟩ := polynomial_finite_weights (p := p) (r := r) L (T.pos i + 1 + 1)
    exact ⟨S, fun x hx => hS x (Submodule.mem_inf.mp hx).1⟩
  have hp0 : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hspQ : ∀ μ v, v ∈ Cset p L (T.pos i + 1 + 1) T.J T.thr → (GA p L (T.pos i + 1 + 1)).IsHW μ v →
      v ∈ Submodule.span ℚ_[p] (Set.range h') := by
    intro μ v hv hw
    obtain ⟨k, hk⟩ := exists_pow_int v
    have h1 := hspZ μ (((p : ℚ_[p]) ^ k) • v) (Submodule.smul_mem _ _ hv) (isHW_smul L _ μ _ hw) hk
    have h2 : ((p : ℚ_[p]) ^ k) • v ∈ Submodule.span ℚ_[p] (Set.range h') :=
      Submodule.span_le_restrictScalars ℤ_[p] ℚ_[p] _ h1
    exact (Submodule.smul_mem_iff _ (pow_ne_zero _ hp0)).mp h2
  have hsp : Cset p (r := r) L (T.pos i + 1 + 1) T.J T.thr ≤ ⨆ x, (GA p L (T.pos i + 1 + 1)).gS {h' x} := by
    obtain ⟨S, hS⟩ := hCf
    exact GlX.span_hw (GA p L (T.pos i + 1 + 1)) hCst hS h' la hh hhC (fun x => hli.ne_zero x) hspQ
  set c : ℚ_[p] := (p : ℚ_[p]) ^ ⌊E⌋₊ with hc
  let gϖ : ι → MvPolynomial (Fin N × Fin r) ℚ_[p] := fun x => if ‖d x‖ < (p : ℝ) ^ (-E) then 0 else h' x
  let tc : ι → ι → ℚ_[p] := fun z y =>
    if la z = la y ∧ ¬ ‖d z‖ < (p : ℝ) ^ (-E) then (c / d z) * (cst * fock p (h' z) (h' y)) else 0
  let gτ : ι → MvPolynomial (Fin N × Fin r) ℚ_[p] := fun y => ∑ z, tc z y • h'' z
  have hgϖ : ∀ x, (GA p L (T.pos i + 1 + 1)).IsHW (la x) (gϖ x) := by
    intro x
    by_cases hx : ‖d x‖ < (p : ℝ) ^ (-E)
    · simp only [gϖ, if_pos hx]; exact isHW_zero' L _ _
    · simp only [gϖ, if_neg hx]; exact hh x
  have hgϖC : ∀ x, gϖ x ∈ Cset p L (T.pos i + 1 + 1) T.J T.thr := by
    intro x
    by_cases hx : ‖d x‖ < (p : ℝ) ^ (-E)
    · simp only [gϖ, if_pos hx]; exact Submodule.zero_mem _
    · simp only [gϖ, if_neg hx]; exact hhC x
  have hgτ : ∀ y, (GA p L (T.pos i + 1 + 1)).IsHW (la y) (gτ y) := by
    intro y
    rw [isHW_iff]
    refine Submodule.sum_mem _ fun z _ => ?_
    by_cases hz : la z = la y ∧ ¬ ‖d z‖ < (p : ℝ) ^ (-E)
    · refine Submodule.smul_mem _ _ ?_
      rw [← isHW_iff, ← hz.1]; exact hh2 z
    · simp only [tc, if_neg hz, zero_smul]; exact Submodule.zero_mem _
  have hgτC : ∀ y, gτ y ∈ Cset p L (T.pos i + 1 + 1) T.J T.thr :=
    fun y => Submodule.sum_mem _ fun z _ => Submodule.smul_mem _ _ (hh2C z)
  have htc : ∀ z y, ‖tc z y‖ ≤ 1 := by
    intro z y
    by_cases hz : la z = la y ∧ ¬ ‖d z‖ < (p : ℝ) ^ (-E)
    · simp only [tc, if_pos hz, norm_mul]
      exact mul_le_one₀ (good_norm E hE (d z) hz.2).1 (by positivity) (by rw [← norm_mul]; exact hG0 z y)
    · simp only [tc, if_neg hz, norm_zero]; exact zero_le_one
  have hgτi : ∀ y, gτ y ∈ IntPol p (Fin N × Fin r) :=
    fun y => Submodule.sum_mem _ fun z _ => smul_int (htc z y) (hh2i z)
  obtain ⟨ϖ, hϖ1, hϖ2, hϖ3, -, -, hϖ6, hϖ7⟩ :=
    GlX.eqExt (GA p L (T.pos i + 1 + 1)) hCst hCf h' gϖ la hh hhC hli hsp hgϖ hgϖC
  obtain ⟨τ, hτ1, hτ2, hτ3, -, -, -, -⟩ :=
    GlX.eqExt (GA p L (T.pos i + 1 + 1)) hCst hCf h' gτ la hh hhC hli hsp hgτ hgτC
  have hEϖ : IsEqC L (T.pos i + 1 + 1) T.J T.thr ϖ := ⟨hϖ2, hϖ3⟩
  have hEτ : IsEqC L (T.pos i + 1 + 1) T.J T.thr τ := ⟨hτ2, hτ3⟩
  refine ⟨bigOp L (T.pos i + 1 + 1) Pi τ, bigOp L (T.pos i + 1 + 1) Pi ϖ,
    bigOp_Y L (T.pos i + 1 + 1) _ T.J T.thr Pi τ hPi hEτ, ?_, ?_, ?_, ?_⟩
  ·
    intro y hy
    have hint : ∀ μ v, v ∈ Cset p L (T.pos i + 1 + 1) T.J T.thr → (GA p L (T.pos i + 1 + 1)).IsHW μ v →
        v ∈ IntPol p (Fin N × Fin r) → τ v ∈ IntPol p (Fin N × Fin r) := by
      intro μ v hv hw hvi
      have h1 := hspZ μ v hv hw hvi
      refine Submodule.span_induction (p := fun v _ => τ v ∈ IntPol p (Fin N × Fin r)) ?_ ?_ ?_ ?_ h1
      · rintro _ ⟨x, rfl⟩
        rw [hτ1]; exact hgτi x
      · rw [map_zero]; exact Submodule.zero_mem _
      · intro a b _ _ ha hb
        rw [map_add]; exact Submodule.add_mem _ ha hb
      · intro a b _ hb
        rw [LinearMap.map_smul_of_tower]; exact Submodule.smul_mem _ a hb
    exact int_main L ρ e1 (T.pos i + 1 + 1) hK hHP hHW (bigOp L (T.pos i + 1 + 1) Pi τ) (e1 * (T.pos i + 1 + 1))
      (bigOp_glAct L (T.pos i + 1 + 1) _ T.J T.thr Pi τ hPi hEτ)
      (fun la0 x hx hxi => bigOp_int L (T.pos i + 1 + 1) _ T.J T.thr Pi τ hPi hEτ hint la0 x hx hxi)
      y (Submodule.mem_inf.mp hy).2
  ·
    intro u hu u' hu'
    have hcore : ∀ g ∈ Cset p L (T.pos i + 1 + 1) T.J T.thr, ∀ g' ∈ Cset p L (T.pos i + 1 + 1) T.J T.thr,
        fock p (T.phi p L i g) (inOp L (T.pos i + 1 + 1) Pi τ g') =
          c * fock p (inOp L (T.pos i + 1 + 1) Pi ϖ g) g' := by
      intro g hg g' hg'
      rw [inOp_C L (T.pos i + 1 + 1) _ T.J T.thr Pi τ hPi g' hg', inOp_C L (T.pos i + 1 + 1) _ T.J T.thr Pi ϖ hPi g hg]
      let B : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] ℚ_[p] :=
        (fockB p (Fin N × Fin r)).compl₁₂ (T.phi p L i) τ - c • (fockB p (Fin N × Fin r)).compl₁₂ ϖ LinearMap.id
      have hBa : ∀ x y, B x y = fock p (T.phi p L i x) (τ y) - c * fock p (ϖ x) y := by
        intro x y
        simp [B, fockB_apply]
      have hBz := GlX.form_zero (GA p L (T.pos i + 1 + 1)) hCst h' la hh hhC hsp B ?_ ?_ g hg g' hg'
      · rw [hBa] at hBz; exact sub_eq_zero.mp hBz
      · intro x hx y hy a b
        rw [hBa, hBa]
        change fock p (T.phi p L i (glAct p L (T.pos i + 1 + 1) a b x)) (τ y) -
          c * fock p (ϖ (glAct p L (T.pos i + 1 + 1) a b x)) y =
          fock p (T.phi p L i x) (τ (glAct p L (T.pos i + 1 + 1) b a y)) -
          c * fock p (ϖ x) (glAct p L (T.pos i + 1 + 1) b a y)
        rw [phi_glAct L T hadm i a b x, fock_glAct, hEτ.comm y hy b a, hEϖ.comm x hx a b, fock_glAct]
      · intro x y hxy
        rw [hBa, hτ1, hϖ1]
        have hterm : ∀ z, tc z y * fock p (T.phi p L i (h' x)) (h'' z) =
            if z = x then (if ‖d x‖ < (p : ℝ) ^ (-E) then 0 else c * fock p (h' x) (h' y)) else 0 := by
          intro z
          by_cases hz : la z = la y ∧ ¬ ‖d z‖ < (p : ℝ) ^ (-E)
          · have h1 := hdiag x z (hxy.trans hz.1.symm)
            simp only [tc, if_pos hz]
            have h2 : c / d z * (cst * fock p (h' z) (h' y)) * fock p (T.phi p L i (h' x)) (h'' z) =
                c / d z * fock p (h' z) (h' y) * (cst * fock p (T.phi p L i (h' x)) (h'' z)) := by ring
            rw [h2, h1]
            by_cases hzx : z = x
            · subst hzx
              rw [if_pos rfl, if_pos rfl, if_neg hz.2]
              have hd0 := (good_norm E hE (d z) hz.2).2
              field_simp
            · rw [if_neg (Ne.symm hzx), if_neg hzx, mul_zero]
          · simp only [tc, if_neg hz, zero_mul]
            by_cases hzx : z = x
            · subst hzx
              rw [if_pos rfl]
              have : ‖d z‖ < (p : ℝ) ^ (-E) := by
                by_contra h; exact hz ⟨hxy, h⟩
              rw [if_pos this]
            · rw [if_neg hzx]
        have hsum : fock p (T.phi p L i (h' x)) (gτ y) =
            if ‖d x‖ < (p : ℝ) ^ (-E) then 0 else c * fock p (h' x) (h' y) := by
          simp only [gτ]
          rw [gammaIntegralityLemmas.fock_sum_right]
          simp only [gammaIntegralityLemmas.fock_smul_right, hterm]
          rw [Finset.sum_ite_eq']
          simp
        rw [hsum]
        by_cases hx : ‖d x‖ < (p : ℝ) ^ (-E)
        · simp only [gϖ, if_pos hx]
          rw [gammaIntegralityLemmas.fock_zero_left]; ring
        · simp only [gϖ, if_neg hx]
          ring
    have key := fock_ext_reduce (T.pos i + 1 + 1) (T.phi p L i) (inOp L (T.pos i + 1 + 1) Pi τ)
      (inOp L (T.pos i + 1 + 1) Pi ϖ) c (Cset p L (T.pos i + 1 + 1) T.J T.thr)
      (phi_mul_later L T hadm i) (phi_isF L T hadm i)
      (inOp_isF L (T.pos i + 1 + 1) _ T.J T.thr Pi τ hPi hEτ) (inOp_isF L (T.pos i + 1 + 1) _ T.J T.thr Pi ϖ hPi hEϖ)
      hcore u u'
      (fun m => by rw [← Cset_thrUpTo]; exact slc_C L (T.pos i + 1 + 1) T.J (T.thrUpTo i) hu m)
      (fun m => slc_C L (T.pos i + 1 + 1) T.J T.thr hu' m)
    unfold fockN
    change fock p (T.phi p L i u) (ext (fsj N r (T.pos i + 1 + 1)) (inOp L (T.pos i + 1 + 1) Pi τ) u') / _ =
      c * (fock p (ext (fsj N r (T.pos i + 1 + 1)) (inOp L (T.pos i + 1 + 1) Pi ϖ) u) u' / _)
    rw [key, mul_div_assoc]
  · intro j hij u
    exact phi_ext_comm L T hadm i j hij _ (inOp_isF L (T.pos i + 1 + 1) _ T.J T.thr Pi ϖ hPi hEϖ) u
  · exact (count_le L (T.pos i + 1 + 1) _ T.J T.thr Pi hPi h' la hh hhC hli hsp
      (fun x => ‖d x‖ < (p : ℝ) ^ (-E)) ϖ hEϖ
      (fun x hx => hϖ6 x (by simp only [gϖ, if_neg hx]))
      (fun x hx => hϖ7 x (by simp only [gϖ, if_pos hx]))).trans
      (Finset.sum_le_sum fun x _ => transport_le L (T.pos i + 1 + 1) _ T.J T.thr Pi hPi h' la hh hhC hli hsp x (vv x)
        (hvv x) (hvvC x) (hvv0 x))

theorem mmwZ_mmw [NeZero r] {K : ℕ} (LLw : Letters K) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ) (ρ : Fin r)
    (w : Fin r → ℤ) {g : MvPolynomial (Fin K × Fin r) ℚ_[p]} (hg : g ∈ MMwZ p LLw J M ρ w) :
    g ∈ MMw p LLw J M ρ w := (Submodule.mem_inf.mp hg).1

theorem mmwZ_polZ [NeZero r] {K : ℕ} (LLw : Letters K) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ) (ρ : Fin r)
    (w : Fin r → ℤ) {g : MvPolynomial (Fin K × Fin r) ℚ_[p]} (hg : g ∈ MMwZ p LLw J M ρ w) :
    g ∈ PolZ p r LLw :=
  Submodule.mem_inf.mpr ⟨(Submodule.mem_inf.mp (Submodule.mem_inf.mp (Submodule.mem_inf.mp
    (Submodule.mem_inf.mp hg).1).1).1).1, (Submodule.mem_inf.mp hg).2⟩

theorem tieOps_main : Formalism.CountingSumsFrames.TieOps := by
  refine ⟨3, by norm_num, ?_⟩
  intro p _ N r _ _ LL T a E κ n ρ _hp2 hr hρ hadm hE hSn hdeg _hz hκ hHP hHW _hL4 nb f U V dg fw hf hUV hfw i
  classical
  have hK : T.pos i + 1 + 1 ≤ N := hK_of_adm LL T hadm i
  have hS : ((LL.setTies T n).takeD (T.pos i + 1)).total ≤ n i := by
    rw [S_eq_total (LL.setTies T n) T i (by omega)]; exact hSn i
  have hni : n i ≤ 2 * a := by
    have := hdeg ⟨T.pos i + 1, by omega⟩
    rwa [setTies_deg_eta LL T hadm i n (by omega)] at this
  obtain ⟨coef, hcoef⟩ : ∃ coef : ℕ, coef =
      (((LL.setTies T n).takeD (T.pos i + 1)).deg (Fin.last (T.pos i)) + n i + r + T.z i - 1).choose
          (((LL.setTies T n).takeD (T.pos i + 1)).deg (Fin.last (T.pos i))) := ⟨_, rfl⟩
  obtain ⟨NN, hNN⟩ : ∃ NN : ℚ_[p], NN =
      ((((n i - ((LL.setTies T n).takeD (T.pos i + 1)).total).factorial *
            ((LL.setTies T n).takeD (T.pos i + 1)).total.factorial : ℕ) : ℚ_[p]) *
          ∏ x, ((((LL.setTies T n).takeD (T.pos i + 1)).deg x).factorial : ℚ_[p])) := ⟨_, rfl⟩
  obtain ⟨cst, hcst⟩ : ∃ cst : ℚ_[p], cst = (p : ℚ_[p]) ^ ⌈κ⌉₊ * (coef : ℚ_[p]) / NN := ⟨_, rfl⟩
  have hgam : ∀ g g', (p : ℚ_[p]) ^ ⌈κ⌉₊ * tieGam p ((LL.setTies T n).takeD (T.pos i + 1)) ρ (T.z i) (n i) g g' =
      cst * fock p (T.phi p (LL.setTies T n) i (T.Ffull p (LL.setTies T n) i ρ (n i) g))
        (T.Ffull p (LL.setTies T n) i ρ (n i) g') := by
    intro g g'
    rw [gam_eq LL T hadm i ρ n g g', ← hcoef, ← hNN, hcst]
    ring
  let B : MvPolynomial (Fin (T.pos i + 1) × Fin r) ℚ_[p] →ₗ[ℚ_[p]]
      MvPolynomial (Fin (T.pos i + 1) × Fin r) ℚ_[p] →ₗ[ℚ_[p]] ℚ_[p] :=
    cst • ((fockB p (Fin N × Fin r)).compl₁₂ ((T.phi p (LL.setTies T n) i) ∘ₗ FfL p (LL.setTies T n) T i ρ (n i))
      (FfL p (LL.setTies T n) T i ρ (n i)))
  have hB : ∀ g g', B g g' = cst * fock p (T.phi p (LL.setTies T n) i (T.Ffull p (LL.setTies T n) i ρ (n i) g))
        (T.Ffull p (LL.setTies T n) i ρ (n i) g') := by
    intro g g'
    simp [B, fockB_apply, FfL_apply]
  have hsm : ∀ w, ∃ f' f'' : Fin (nb i w) → MvPolynomial (Fin (T.pos i + 1) × Fin r) ℚ_[p],
      (∀ a, f' a ∈ MMwZ p ((LL.setTies T n).takeD (T.pos i + 1)) T.J (T.thrUpTo i) ρ w) ∧
      (∀ a, f'' a ∈ MMwZ p ((LL.setTies T n).takeD (T.pos i + 1)) T.J (T.thrUpTo i) ρ w) ∧
      LinearIndependent ℚ_[p] f' ∧
      MMwZ p ((LL.setTies T n).takeD (T.pos i + 1)) T.J (T.thrUpTo i) ρ w ≤ Submodule.span ℤ_[p] (Set.range f') ∧
      ∀ a b, B (f' a) (f'' b) = if a = b then dg i w a else 0 := by
    intro w
    obtain ⟨hU1, hV1, hU2, hV2, hfac⟩ := hUV i w
    refine smith_bases (nb i w) (f i w) _ (hf i w).1 (hf i w).2 B (U i w) (V i w) (dg i w) hU1 hV1 hU2 hV2 ?_
    rw [← hfac]
    ext x y
    simp only [Matrix.of_apply]
    rw [hB, hgam]
  choose f' f'' hf'1 hf''1 hf'li hf'sp hf'diag using hsm
  obtain ⟨Ω, hΩ⟩ : ∃ Ω : Finset (Fin r → ℤ), ∀ w, w ∈ Ω ↔
      MMw p ((LL.setTies T n).takeD (T.pos i + 1)) T.J (T.thrUpTo i) ρ w ≠ ⊥ :=
    ⟨(mmw_finite (p := p) LL T i ρ n).toFinset, fun w => by simp⟩
  have hnb0 : ∀ w, w ∉ Ω → nb i w = 0 := by
    intro w hw
    by_contra h0
    have hbot : MMw p ((LL.setTies T n).takeD (T.pos i + 1)) T.J (T.thrUpTo i) ρ w = ⊥ := by
      by_contra h; exact hw ((hΩ w).mpr h)
    have hmem : f i w ⟨0, Nat.pos_of_ne_zero h0⟩ ∈
        MMwZ p ((LL.setTies T n).takeD (T.pos i + 1)) T.J (T.thrUpTo i) ρ w := by
      rw [← (hf i w).2]; exact Submodule.subset_span ⟨_, rfl⟩
    have h1 := mmwZ_mmw _ _ _ _ _ hmem
    rw [hbot, Submodule.mem_bot] at h1
    exact (hf i w).1.ne_zero _ h1
  have hκ' : ((T.pos i + 3) * r ^ 2 : ℝ) * lgV2 p a r ≤ κ := by
    refine le_trans ?_ hκ
    have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
    have hlg : 0 ≤ lgV2 p a r := by
      unfold lgV2
      have : (1 : ℝ) ≤ 8 * (a : ℝ) + r := by
        have : (2 : ℝ) ≤ r := by exact_mod_cast hr
        have : (0 : ℝ) ≤ a := Nat.cast_nonneg a
        linarith
      have := Real.logb_nonneg hp1 this
      linarith
    have h1 : ((T.pos i : ℝ) + 3) ≤ (N : ℝ) + 2 := by
      have : ((T.pos i + 1 + 1 : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast hK
      push_cast at this; linarith
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1 (by positivity)) hlg
  have hspZ : ∀ μ v, v ∈ Cset p (LL.setTies T n) (T.pos i + 1 + 1) T.J T.thr →
      (GA p (LL.setTies T n) (T.pos i + 1 + 1)).IsHW μ v → v ∈ IntPol p (Fin N × Fin r) →
      v ∈ Submodule.span ℤ_[p] (Set.range fun x : (Σ w : Ω, Fin (nb i w.1)) =>
          T.Ffull p (LL.setTies T n) i ρ (n i) (f' x.1.1 x.2)) := by
    intro μ v hv hw hvi
    obtain ⟨g, hg, rfl⟩ := hw_is_Ffull LL T hadm i ρ hρ n hS μ v hv hw hvi
    by_cases hwΩ : (μ + ((n i : ℕ) : ℤ) • Pi.single ρ 1) ∈ Ω
    · have hg' := hf'sp _ hg
      refine Submodule.span_induction (p := fun g _ => T.Ffull p (LL.setTies T n) i ρ (n i) g ∈
        Submodule.span ℤ_[p] (Set.range fun x : (Σ w : Ω, Fin (nb i w.1)) =>
          T.Ffull p (LL.setTies T n) i ρ (n i) (f' x.1.1 x.2))) ?_ ?_ ?_ ?_ hg'
      · rintro _ ⟨b, rfl⟩
        exact Submodule.subset_span ⟨⟨⟨_, hwΩ⟩, b⟩, rfl⟩
      · rw [← FfL_apply, map_zero]; exact Submodule.zero_mem _
      · intro x y _ _ hx hy
        rw [← FfL_apply, map_add]; exact Submodule.add_mem _ hx hy
      · intro c x _ hx
        rw [← FfL_apply, LinearMap.map_smul_of_tower]; exact Submodule.smul_mem _ c hx
    · have hbot : MMw p ((LL.setTies T n).takeD (T.pos i + 1)) T.J (T.thrUpTo i) ρ
          (μ + ((n i : ℕ) : ℤ) • Pi.single ρ 1) = ⊥ := by
        by_contra h; exact hwΩ ((hΩ _).mpr h)
      have h1 := mmwZ_mmw _ _ _ _ _ hg
      rw [hbot, Submodule.mem_bot] at h1
      rw [h1, ← FfL_apply, map_zero]; exact Submodule.zero_mem _
  have hdiag : ∀ x y : (Σ w : Ω, Fin (nb i w.1)),
      x.1.1 - ((n i : ℕ) : ℤ) • (Pi.single ρ 1 : Fin r → ℤ) = y.1.1 - ((n i : ℕ) : ℤ) • Pi.single ρ 1 →
      cst * fock p (T.phi p (LL.setTies T n) i (T.Ffull p (LL.setTies T n) i ρ (n i) (f' x.1.1 x.2)))
        (T.Ffull p (LL.setTies T n) i ρ (n i) (f'' y.1.1 y.2)) = if x = y then dg i x.1.1 x.2 else 0 := by
    rintro ⟨⟨w, hw⟩, b⟩ ⟨⟨w', hw'⟩, b'⟩ hla
    have hww : w = w' := sub_left_injective hla
    subst hww
    have := hf'diag w b b'
    rw [hB] at this
    simp only
    rw [this]
    by_cases hbb : b = b'
    · subst hbb; simp
    · rw [if_neg hbb, if_neg]
      intro h
      apply hbb
      simpa using h
  have hG0 : ∀ x y : (Σ w : Ω, Fin (nb i w.1)),
      ‖cst * fock p (T.Ffull p (LL.setTies T n) i ρ (n i) (f' x.1.1 x.2))
        (T.Ffull p (LL.setTies T n) i ρ (n i) (f' y.1.1 y.2))‖ ≤ 1 := by
    intro x y
    rw [fock_Ffull LL T hadm i ρ n]
    have hg := gamma_zero_integral_alt (p := p) (T.pos i) r ((LL.setTies T n).takeD (T.pos i + 1)) ρ (n i) a κ hS hni hκ'
      (f' x.1.1 x.2) (f' y.1.1 y.2) (mmwZ_polZ _ _ _ _ _ (hf'1 x.1.1 x.2)) (mmwZ_polZ _ _ _ _ _ (hf'1 y.1.1 y.2))
    rw [← hNN] at hg
    have e : cst * fock p (freeze p ((LL.setTies T n).takeD (T.pos i + 1)) ρ (n i) (f' x.1.1 x.2))
        (freeze p ((LL.setTies T n).takeD (T.pos i + 1)) ρ (n i) (f' y.1.1 y.2)) =
        (coef : ℚ_[p]) * ((p : ℚ_[p]) ^ ⌈κ⌉₊ *
          (fock p (freeze p ((LL.setTies T n).takeD (T.pos i + 1)) ρ (n i) (f' x.1.1 x.2))
        (freeze p ((LL.setTies T n).takeD (T.pos i + 1)) ρ (n i) (f' y.1.1 y.2)) / NN)) := by
      rw [hcst]; ring
    rw [e, norm_mul]
    exact mul_le_one₀ (gammaIntegralityLemmas.norm_natCast_le_one' coef) (norm_nonneg _) hg
  obtain ⟨Tm, πm, h1, h2, h3, h4, h5⟩ := tie_core (LL.setTies T n) T hadm i ρ ⌈κ / (N + 2)⌉₊ hK hHP hHW E (by linarith)
    (ι := Σ w : Ω, Fin (nb i w.1))
    (fun x => T.Ffull p (LL.setTies T n) i ρ (n i) (f' x.1.1 x.2))
    (fun x => T.Ffull p (LL.setTies T n) i ρ (n i) (f'' x.1.1 x.2))
    (fun x => x.1.1 - ((n i : ℕ) : ℤ) • Pi.single ρ 1)
    (fun x => Ffull_hw LL T hadm i ρ hρ n x.1.1 _ (mmwZ_mmw _ _ _ _ _ (hf'1 x.1.1 x.2)) hS)
    (fun x => Ffull_C LL T hadm i ρ n hS x.1.1 _ (mmwZ_mmw _ _ _ _ _ (hf'1 x.1.1 x.2)))
    (Ffull_indep LL T hadm i ρ n hS Ω (nb i) f' (fun w a => mmwZ_mmw _ _ _ _ _ (hf'1 w a)) hf'li)
    hspZ
    (fun x => Ffull_hw LL T hadm i ρ hρ n x.1.1 _ (mmwZ_mmw _ _ _ _ _ (hf''1 x.1.1 x.2)) hS)
    (fun x => Ffull_C LL T hadm i ρ n hS x.1.1 _ (mmwZ_mmw _ _ _ _ _ (hf''1 x.1.1 x.2)))
    (fun x => Ffull_int LL T hadm i ρ n hS _ (mmwZ_polZ _ _ _ _ _ (hf''1 x.1.1 x.2)))
    (fun x => dg i x.1.1 x.2) cst hdiag hG0
    (fun x => T.Ffull p (LL.setTies T n) i ρ (n i) (fw i x.1.1))
    (fun x => Ffull_hw LL T hadm i ρ hρ n x.1.1 _ (hfw i x.1.1).1 hS)
    (fun x => Ffull_C LL T hadm i ρ n hS x.1.1 _ (hfw i x.1.1).1)
    (fun x => Ffull_ne LL T hadm i ρ n x.1.1 _ (hfw i x.1.1).1 ((hfw i x.1.1).2 ((hΩ _).mp x.1.2)) hS)
  refine ⟨Tm, πm, ⌈κ / (N + 2)⌉₊ * (T.pos i + 1 + 1) + 2 * ⌈κ / (N + 2)⌉₊,
    K_bound N r a (T.pos i + 1 + 1) κ hr hK hκ, h1, h2, h3, fun j hij u _ => h4 j hij u, ?_⟩
  have hsumN : ∑ x ∈ univ.filter (fun x : (Σ w : Ω, Fin (nb i w.1)) => ‖dg i x.1.1 x.2‖ < (p : ℝ) ^ (-E)),
      Module.finrank ℚ_[p] (YYs (LL.setTies T n) (T.pos i + 1 + 1) T.J T.thr
        (T.Ffull p (LL.setTies T n) i ρ (n i) (fw i x.1.1))) =
      ∑ w ∈ Ω, (univ.filter (fun b => ‖dg i w b‖ < (p : ℝ) ^ (-E))).card *
        Module.finrank ℚ_[p] (T.YYsp p LL i ρ n (fw i w)) := by
    rw [Finset.sum_filter, Fintype.sum_sigma, ← Finset.sum_coe_sort Ω]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [← Finset.sum_filter, YYsp_eq]
    exact Finset.sum_const_nat (fun _ _ => rfl)
  have hfs : ∑ᶠ w, ((univ.filter (fun b => ‖dg i w b‖ < (p : ℝ) ^ (-E))).card : ℝ) *
        (Module.finrank ℚ_[p] (T.YYsp p LL i ρ n (fw i w)) : ℝ) =
      ∑ w ∈ Ω, ((univ.filter (fun b => ‖dg i w b‖ < (p : ℝ) ^ (-E))).card : ℝ) *
        (Module.finrank ℚ_[p] (T.YYsp p LL i ρ n (fw i w)) : ℝ) := by
    refine finsum_eq_sum_of_support_subset _ fun w hw => ?_
    rw [Finset.mem_coe]
    by_contra hwΩ
    refine hw ?_
    have hle : (univ.filter (fun b => ‖dg i w b‖ < (p : ℝ) ^ (-E))).card ≤ nb i w :=
      (Finset.card_le_univ _).trans (by simp)
    have hle0 := Nat.le_zero.mp (hle.trans (hnb0 w hwΩ).le)
    simp only [hle0, Nat.cast_zero, zero_mul]
  rw [hfs]
  rw [hsumN] at h5
  exact_mod_cast h5

end Formalism.CountingSumsFrames.TO

namespace Formalism.CountingSumsFrames

theorem level_operators_exist : Formalism.CountingSumsFrames.TieOps := TO.tieOps_main

end Formalism.CountingSumsFrames
