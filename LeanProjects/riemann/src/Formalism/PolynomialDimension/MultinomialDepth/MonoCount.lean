import Formalism.MahlerMeasure.MahlerMeasureProofs.WeightSpaceDimensionMonotone

namespace Formalism.CountingSumsFrames

open Formalism.GM.DimensionMonotonicity Finset

namespace GlX

variable {K V : Type} [Field K] [CharZero K] [AddCommGroup V] [Module K V] {r : ℕ} (G : GlW K V r)

theorem cas_hw {μ : Fin r → ℤ} {x : V} (h : G.IsHW μ x) : G.Cas x = ((GlW.casI μ : ℤ) : K) • x := by
  have hd : ∀ c, G.E c c x = ((μ c : ℤ) : K) • x := fun c => by
    have e := G.diag c μ x
    rwa [h.1] at e
  unfold GlW.Cas GlW.casI
  simp only [LinearMap.sum_apply, LinearMap.comp_apply, Int.cast_sum, Finset.sum_smul]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rcases lt_trichotomy a b with hab | hab | hab
  · have hc := G.comm a b b a x
    simp only [if_true] at hc
    rw [h.2 a b hab, map_zero, sub_zero] at hc
    rw [hc, hd, hd, if_neg hab.ne, if_pos hab, ← sub_smul]
    push_cast
    rfl
  · subst hab
    rw [hd, map_smul, hd, smul_smul, if_pos rfl]
    push_cast
    rfl
  · rw [h.2 b a hab, map_zero, if_neg hab.ne', if_neg (not_lt.mpr hab.le)]
    simp

theorem cprod_kill {x : V} {e : ℤ} (hx : G.Cas x = ((e : ℤ) : K) • x) (cs : List ℤ) (he : e ∈ cs) :
    G.cprod cs x = 0 := by
  have key : ∀ cs : List ℤ, G.cprod cs x = (cs.map fun c => ((e - c : ℤ) : K)).prod • x := by
    intro cs
    induction cs with
    | nil =>
      show x = _
      simp
    | cons c cs ih =>
      show ((G.Cas - ((c : ℤ) : K) • LinearMap.id : V →ₗ[K] V)) (G.cprod cs x) = _
      rw [ih, List.map_cons, List.prod_cons, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, map_smul, hx,
        smul_smul, smul_smul, ← sub_smul]
      congr 1
      push_cast
      ring
  rw [key]
  have hmem : ((e - e : ℤ) : K) ∈ cs.map fun c => ((e - c : ℤ) : K) := List.mem_map.mpr ⟨e, he, rfl⟩
  rw [List.prod_eq_zero (by simpa using hmem), zero_smul]

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

theorem cprod_mod {U : Submodule K V} (hU : G.Stable U) {μ : Fin r → ℤ} {v : V} (hv : G.IsWt μ v)
    (hr : ∀ a b, a < b → G.E a b v ∈ U) (cs : List ℤ) :
    G.cprod cs v - (cs.map (fun c => (((GlW.casI μ - c : ℤ)) : K))).prod • v ∈ U := by
  induction cs with
  | nil => simp [GlW.cprod]
  | cons c cs ih =>
    rw [G.cprod_cons, List.map_cons, List.prod_cons]
    have hc := G.Cas_hwmod hU hv hr
    have e : G.Cas (G.cprod cs v) - ((c : ℤ) : K) • G.cprod cs v -
        ((((GlW.casI μ - c : ℤ)) : K) * (cs.map (fun c => (((GlW.casI μ - c : ℤ)) : K))).prod) • v =
      (G.Cas (G.cprod cs v - (cs.map (fun c => (((GlW.casI μ - c : ℤ)) : K))).prod • v) -
        ((c : ℤ) : K) • (G.cprod cs v - (cs.map (fun c => (((GlW.casI μ - c : ℤ)) : K))).prod • v)) +
        (cs.map (fun c => (((GlW.casI μ - c : ℤ)) : K))).prod • (G.Cas v - ((GlW.casI μ : ℤ) : K) • v) := by
      rw [map_sub, map_smul]; push_cast; module
    rw [e]
    exact U.add_mem (U.sub_mem (G.Cas_mem hU ih) (U.smul_mem _ ih)) (U.smul_mem _ hc)

theorem iSup_stable {ι : Sort*} {U : ι → Submodule K V} (hU : ∀ i, G.Stable (U i)) : G.Stable (⨆ i, U i) := by
  intro a b x hx
  have hle : (⨆ i, U i) ≤ (⨆ i, U i).comap (G.E a b) :=
    iSup_le fun i y hy => Submodule.mem_iSup_of_mem i (hU i a b y hy)
  exact hle hx

theorem inf_stable {U U' : Submodule K V} (hU : G.Stable U) (hU' : G.Stable U') : G.Stable (U ⊓ U') := by
  exact fun a b x hx => ⟨hU a b x hx.1, hU' a b x hx.2⟩

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

end Formalism.CountingSumsFrames

namespace Formalism.CountingSumsFrames

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

end Formalism.CountingSumsFrames

namespace Formalism.CountingSumsFrames

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
  | nil => exact hx
  | cons ab w ih => exact hU ab.1 ab.2 _ ih

theorem E_Lv (v : V) (a b : Fin r) (c : List (Fin r × Fin r) →₀ K) :
    G.E a b (Lv G v c) = Lv G v (Finsupp.mapDomain (List.cons (a, b)) c) := by
  unfold Lv
  rw [Finsupp.linearCombination_mapDomain, Finsupp.apply_linearCombination]
  rfl

theorem range_Lv (v : V) : LinearMap.range (Lv G v) = G.gS {v} := by
  have hv : v ∈ G.gS {v} := Submodule.mem_sInf.mpr fun U hU => hU.1 (Set.mem_singleton v)
  have hst : G.Stable (G.gS {v}) := fun a b x hx =>
    Submodule.mem_sInf.mpr fun U hU => hU.2 a b x (Submodule.mem_sInf.mp hx U hU)
  apply le_antisymm
  · rintro _ ⟨c, rfl⟩
    unfold Lv
    rw [Finsupp.linearCombination_apply]
    exact Submodule.sum_mem _ fun w _ => Submodule.smul_mem _ _ (act_mem G hst w hv)
  · have hR : G.Stable (LinearMap.range (Lv G v)) := fun a b x hx => by
      obtain ⟨c, rfl⟩ := hx
      rw [E_Lv]
      exact LinearMap.mem_range_self _ _
    have hvR : v ∈ LinearMap.range (Lv G v) := ⟨Finsupp.single [] 1, by
      unfold Lv
      rw [Finsupp.linearCombination_single, one_smul]
      rfl⟩
    exact sInf_le (show LinearMap.range (Lv G v) ∈ {U : Submodule K V | {v} ⊆ (U : Set V) ∧ G.Stable U} from
      ⟨Set.singleton_subset_iff.mpr hvR, hR⟩)

theorem Lv_add (v v' : V) (c : List (Fin r × Fin r) →₀ K) : Lv G (v + v') c = Lv G v c + Lv G v' c := by
  unfold Lv
  simp only [Finsupp.linearCombination_apply, map_add, smul_add, Finsupp.sum_add]

theorem Lv_smul (t : K) (v : V) (c : List (Fin r × Fin r) →₀ K) : Lv G (t • v) c = t • Lv G v c := by
  unfold Lv
  simp only [Finsupp.linearCombination_apply, Finsupp.sum, map_smul, Finset.smul_sum]
  exact Finset.sum_congr rfl fun w _ => smul_comm _ _ _

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
  unfold tr
  rw [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, LinearMap.quotKerEquivRange_symm_apply_image,
    Submodule.mkQ_apply, Submodule.liftQ_apply]

end GlX

end Formalism.CountingSumsFrames

namespace Formalism.CountingSumsFrames

open Formalism.GM.DimensionMonotonicity Finset

namespace GlX

variable {K V : Type} [Field K] [CharZero K] [AddCommGroup V] [Module K V] {r : ℕ} (G : GlW K V r)

theorem tr_E {h h' : V} (hk : LinearMap.ker (Lv G h) ≤ LinearMap.ker (Lv G h')) (a b : Fin r)
    (y : LinearMap.range (Lv G h)) (hy : G.E a b y ∈ LinearMap.range (Lv G h)) :
    tr G hk ⟨G.E a b y, hy⟩ = G.E a b (tr G hk y) := by
  obtain ⟨y, c, rfl⟩ := y
  rw [show (⟨G.E a b _, hy⟩ : LinearMap.range (Lv G h)) =
      ⟨Lv G h (Finsupp.mapDomain (List.cons (a, b)) c), LinearMap.mem_range_self _ _⟩ from
    Subtype.ext (E_Lv G h a b c), tr_apply, tr_apply, E_Lv]

theorem tr_mem {h h' : V} (hk : LinearMap.ker (Lv G h) ≤ LinearMap.ker (Lv G h')) (y : LinearMap.range (Lv G h)) :
    tr G hk y ∈ LinearMap.range (Lv G h') := by
  obtain ⟨y, c, rfl⟩ := y
  rw [tr_apply]
  exact LinearMap.mem_range_self _ _

theorem tr_tr {h h' : V} (hk : LinearMap.ker (Lv G h) ≤ LinearMap.ker (Lv G h'))
    (hk' : LinearMap.ker (Lv G h') ≤ LinearMap.ker (Lv G h)) (y : LinearMap.range (Lv G h)) :
    tr G hk' ⟨tr G hk y, tr_mem G hk y⟩ = y := by
  obtain ⟨y, c, rfl⟩ := y
  have e : (⟨tr G hk ⟨Lv G h c, LinearMap.mem_range_self _ c⟩, tr_mem G hk _⟩ : LinearMap.range (Lv G h')) =
      ⟨Lv G h' c, LinearMap.mem_range_self _ c⟩ := Subtype.ext (tr_apply G hk c)
  rw [e, tr_apply]

theorem isWt_of_eig {μ : Fin r → ℤ} {z : V} (hz : ∀ c, G.E c c z = ((μ c : ℤ) : K) • z) : G.IsWt μ z := by
  classical
  obtain ⟨S, hS⟩ := G.dec z
  have hz' := G.sum_comp z (insert μ S) (fun ν hν => hS ν (fun h => hν (Finset.mem_insert_of_mem h)))
  have h0 : ∀ ν, ν ≠ μ → G.comp ν z = 0 := by
    intro ν hν
    obtain ⟨c, hc⟩ : ∃ c, ν c ≠ μ c := by
      by_contra h; exact hν (funext fun c => by by_contra hc; exact h ⟨c, hc⟩)
    have e1 := G.comp_Ecc ν c z
    rw [hz c, map_smul] at e1
    have : (((μ c : ℤ) : K) - ((ν c : ℤ) : K)) • G.comp ν z = 0 := by rw [sub_smul, e1, sub_self]
    rcases smul_eq_zero.mp this with h | h
    · exfalso; apply hc
      have : ((μ c : ℤ) : K) = ((ν c : ℤ) : K) := sub_eq_zero.mp h
      exact_mod_cast this.symm
    · exact h
  show G.comp μ z = z
  conv_rhs => rw [← hz']
  rw [Finset.sum_eq_single μ (fun ν _ hν => h0 ν hν) (fun h => absurd (Finset.mem_insert_self μ S) h)]

theorem comp_comm_of {W : Submodule K V} (hW : G.Graded W) (φ : V →ₗ[K] V)
    (hφ : ∀ x ∈ W, ∀ c, φ (G.E c c x) = G.E c c (φ x)) :
    ∀ x ∈ W, ∀ μ, φ (G.comp μ x) = G.comp μ (φ x) := by
  classical
  intro x hx μ
  have hwt : ∀ ν, G.IsWt ν (φ (G.comp ν x)) := fun ν => isWt_of_eig G (fun c => by
    rw [← hφ _ (hW ν x hx) c, G.diag, map_smul])
  obtain ⟨S, hS⟩ := G.dec x
  have hx' := G.sum_comp x (insert μ S) (fun ν hν => hS ν (fun h => hν (Finset.mem_insert_of_mem h)))
  conv_rhs => rw [← hx']
  rw [map_sum, map_sum, Finset.sum_eq_single μ (fun ν _ hν => by rw [G.comp_of_isWt (hwt ν), if_neg (Ne.symm hν)])
    (fun h => absurd (Finset.mem_insert_self μ S) h), G.comp_of_isWt (hwt μ), if_pos rfl]

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

theorem proj_sum {W : Submodule K V} {ι : Type*} [Fintype ι] (R : ι → Submodule K V) (hWR : W ≤ ⨆ i, R i)
    (π : ι → V →ₗ[K] V) (h2 : ∀ i, ∀ x ∈ R i, π i x = x) (h3 : ∀ i j, j ≠ i → ∀ x ∈ R j, π i x = 0) :
    ∀ x ∈ W, ∑ i, π i x = x := by
  intro x hx
  exact Submodule.iSup_induction R (motive := fun x => ∑ i, π i x = x) (hWR hx)
    (fun j y hy => by
      show ∑ i, π i y = y
      rw [Finset.sum_eq_single j]
      · exact h2 j y hy
      · intro i _ hij
        exact h3 i j (Ne.symm hij) y hy
      · intro hj
        exact absurd (Finset.mem_univ _) hj)
    (by simp)
    (fun y z hy hz => by
      show ∑ i, π i (y + z) = y + z
      simp only [map_add, Finset.sum_add_distrib]
      rw [hy, hz])

theorem proj_comm {W : Submodule K V} {ι : Type*} (R : ι → Submodule K V) (hWR : W ≤ ⨆ i, R i)
    (π : ι → V →ₗ[K] V) (h2 : ∀ i, ∀ x ∈ R i, π i x = x) (h3 : ∀ i j, j ≠ i → ∀ x ∈ R j, π i x = 0)
    (A : V →ₗ[K] V) (hA : ∀ j, ∀ x ∈ R j, A x ∈ R j) : ∀ i, ∀ x ∈ W, π i (A x) = A (π i x) := by
  intro i x hx
  exact Submodule.iSup_induction R (motive := fun x => π i (A x) = A (π i x)) (hWR hx)
    (fun j y hy => by
      show π i (A y) = A (π i y)
      by_cases hji : j = i
      · subst hji
        rw [h2 j _ (hA j y hy), h2 j y hy]
      · rw [h3 i j hji _ (hA j y hy), h3 i j hji y hy, map_zero])
    (by simp)
    (fun y z hy hz => by
      show π i (A (y + z)) = A (π i (y + z))
      simp only [map_add]
      rw [hy, hz])

end Proj

end Formalism.CountingSumsFrames

namespace Formalism.CountingSumsFrames

open MvPolynomial Finset

section Ext

variable {K : Type} [Field K] {σ : Type} [DecidableEq σ] (fs : σ → Prop) [DecidablePred fs]

def frst (m : σ →₀ ℕ) : σ →₀ ℕ := m.filter fs

def ltr (m : σ →₀ ℕ) : σ →₀ ℕ := m.filter (fun v => ¬ fs v)

def IsF (g : MvPolynomial σ K) : Prop := ∀ m ∈ g.support, ∀ v, m v ≠ 0 → fs v

def IsL (q : MvPolynomial σ K) : Prop := ∀ m ∈ q.support, ∀ v, m v ≠ 0 → ¬ fs v

theorem frst_add_ltr (m : σ →₀ ℕ) : frst fs m + ltr fs m = m := by
  unfold frst ltr
  exact Finsupp.filter_pos_add_filter_neg _ _

theorem frst_of {m : σ →₀ ℕ} (h : ∀ v, m v ≠ 0 → fs v) : frst fs m = m := by
  unfold frst
  exact (Finsupp.filter_eq_self_iff _ _).mpr h
theorem ltr_of {m : σ →₀ ℕ} (h : ∀ v, m v ≠ 0 → fs v) : ltr fs m = 0 := by
  unfold ltr
  exact (Finsupp.filter_eq_zero_iff _ _).mpr fun v hv => by
    by_contra h0
    exact hv (h v h0)
theorem frst_of' {m : σ →₀ ℕ} (h : ∀ v, m v ≠ 0 → ¬ fs v) : frst fs m = 0 := by
  unfold frst
  exact (Finsupp.filter_eq_zero_iff _ _).mpr fun v hv => by
    by_contra h0
    exact h v h0 hv
theorem ltr_of' {m : σ →₀ ℕ} (h : ∀ v, m v ≠ 0 → ¬ fs v) : ltr fs m = m := by
  unfold ltr
  exact (Finsupp.filter_eq_self_iff _ _).mpr h
theorem frst_add (m m' : σ →₀ ℕ) : frst fs (m + m') = frst fs m + frst fs m' := by
  unfold frst
  exact Finsupp.filter_add
theorem ltr_add (m m' : σ →₀ ℕ) : ltr fs (m + m') = ltr fs m + ltr fs m' := by
  unfold ltr
  exact Finsupp.filter_add
theorem frst_isF (m : σ →₀ ℕ) : ∀ v, frst fs m v ≠ 0 → fs v := by
  intro v hv
  by_contra h
  apply hv
  unfold frst
  rw [Finsupp.filter_apply_neg _ _ h]
theorem ltr_isL (m : σ →₀ ℕ) : ∀ v, ltr fs m v ≠ 0 → ¬ fs v := by
  intro v hv h
  apply hv
  unfold ltr
  rw [Finsupp.filter_apply_neg (fun v => ¬ fs v) m (not_not.mpr h)]

noncomputable def ext (φ : MvPolynomial σ K →ₗ[K] MvPolynomial σ K) : MvPolynomial σ K →ₗ[K] MvPolynomial σ K :=
  (basisMonomials σ K).constr K (fun m => φ (monomial (frst fs m) 1) * monomial (ltr fs m) 1)

noncomputable def slc (m : σ →₀ ℕ) : MvPolynomial σ K →ₗ[K] MvPolynomial σ K :=
  (basisMonomials σ K).constr K (fun m' => if ltr fs m' = m then monomial (frst fs m') 1 else 0)

theorem monomial_eq_basis (m : σ →₀ ℕ) (a : K) : monomial m a = a • (basisMonomials σ K) m := by
  simp [MvPolynomial.coe_basisMonomials, MvPolynomial.smul_monomial]

theorem ext_monomial (φ : MvPolynomial σ K →ₗ[K] MvPolynomial σ K) (m : σ →₀ ℕ) (a : K) :
    ext fs φ (monomial m a) = a • (φ (monomial (frst fs m) 1) * monomial (ltr fs m) 1) := by
  rw [monomial_eq_basis, map_smul]
  unfold Formalism.CountingSumsFrames.ext
  rw [Module.Basis.constr_basis]

theorem sl_monomial (m m' : σ →₀ ℕ) (a : K) :
    slc fs m (monomial m' a) = if ltr fs m' = m then monomial (frst fs m') a else 0 := by
  rw [monomial_eq_basis, map_smul]
  unfold slc
  rw [Module.Basis.constr_basis]
  split_ifs <;> simp [MvPolynomial.smul_monomial]

theorem ext_add (φ ψ : MvPolynomial σ K →ₗ[K] MvPolynomial σ K) : ext fs (φ + ψ) = ext fs φ + ext fs ψ := by
  refine (basisMonomials σ K).ext fun m => ?_
  simp only [Formalism.CountingSumsFrames.ext, LinearMap.add_apply, Module.Basis.constr_basis, add_mul]

theorem ext_sum {ι : Type*} (s : Finset ι) (φ : ι → MvPolynomial σ K →ₗ[K] MvPolynomial σ K) :
    ext fs (∑ i ∈ s, φ i) = ∑ i ∈ s, ext fs (φ i) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp only [Finset.sum_empty]
    refine (basisMonomials σ K).ext fun m => ?_
    simp only [Formalism.CountingSumsFrames.ext, Module.Basis.constr_basis, LinearMap.zero_apply, zero_mul]
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ext_add, ih]

theorem ext_mul (φ : MvPolynomial σ K →ₗ[K] MvPolynomial σ K) {g q : MvPolynomial σ K} (hg : IsF fs g)
    (hq : IsL fs q) : ext fs φ (g * q) = φ g * q := by
  rw [g.as_sum, q.as_sum]
  simp only [Finset.mul_sum, Finset.sum_mul, map_sum]
  refine Finset.sum_congr rfl fun m' hm' => Finset.sum_congr rfl fun m hm => ?_
  rw [MvPolynomial.monomial_mul, ext_monomial, frst_add, ltr_add, frst_of fs (hg m hm), frst_of' fs (hq m' hm'),
    ltr_of fs (hg m hm), ltr_of' fs (hq m' hm'), add_zero, zero_add,
    show monomial m (coeff m g) = coeff m g • monomial m (1 : K) by rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one],
    map_smul,
    show monomial m' (coeff m' q) = coeff m' q • monomial m' (1 : K) by rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one],
    smul_mul_smul_comm]

theorem sl_mul (m : σ →₀ ℕ) {g q : MvPolynomial σ K} (hg : IsF fs g) (hq : IsL fs q) :
    slc fs m (g * q) = coeff m q • g := by
  conv_lhs => rw [g.as_sum, q.as_sum]
  simp only [Finset.sum_mul, Finset.mul_sum, map_sum]
  have key : ∀ a ∈ g.support, ∀ b ∈ q.support,
      slc fs m (monomial a (coeff a g) * monomial b (coeff b q)) = if b = m then coeff m q • monomial a (coeff a g) else 0 := by
    intro a ha b hb
    rw [MvPolynomial.monomial_mul, sl_monomial, frst_add, ltr_add, frst_of fs (hg a ha), frst_of' fs (hq b hb),
      ltr_of fs (hg a ha), ltr_of' fs (hq b hb), add_zero, zero_add]
    split_ifs with h
    · subst h
      rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_comm]
    · rfl
  rw [Finset.sum_congr rfl fun b hb => Finset.sum_congr rfl fun a ha => key a ha b hb, Finset.sum_comm]
  by_cases hm : m ∈ q.support
  · simp only [Finset.sum_ite_eq', Finset.sum_ite_eq, hm, if_true]
    rw [← Finset.smul_sum, ← g.as_sum]
  · have h0 : coeff m q = 0 := by simpa using hm
    simp only [Finset.sum_ite_eq', Finset.sum_ite_eq, hm, if_false, Finset.sum_const_zero, h0, zero_smul]

theorem ext_eq_sum (φ : MvPolynomial σ K →ₗ[K] MvPolynomial σ K) (x : MvPolynomial σ K) (S : Finset (σ →₀ ℕ))
    (hS : ∀ m ∈ x.support, ltr fs m ∈ S) : ext fs φ x = ∑ m ∈ S, φ (slc fs m x) * monomial m 1 := by
  classical
  have e : ∀ m' ∈ x.support, ext fs φ (monomial m' (coeff m' x)) =
      ∑ m ∈ S, φ (slc fs m (monomial m' (coeff m' x))) * monomial m 1 := by
    intro m' hm'
    simp_rw [sl_monomial]
    rw [Finset.sum_eq_single (ltr fs m') (fun b _ hb => by rw [if_neg (Ne.symm hb), map_zero, zero_mul])
      (fun h => absurd (hS m' hm') h), if_pos rfl, ext_monomial, ← smul_mul_assoc, ← map_smul, smul_monomial,
      smul_eq_mul, mul_one]
  conv_lhs => rw [x.as_sum]
  rw [map_sum, Finset.sum_congr rfl e, Finset.sum_comm]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [← Finset.sum_mul, ← map_sum, ← map_sum, ← x.as_sum]

theorem eq_sum_sl (x : MvPolynomial σ K) (S : Finset (σ →₀ ℕ)) (hS : ∀ m ∈ x.support, ltr fs m ∈ S) :
    x = ∑ m ∈ S, slc fs m x * monomial m 1 := by
  conv_rhs => rw [x.as_sum]
  simp only [map_sum, Finset.sum_mul, sl_monomial, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  conv_lhs => rw [x.as_sum]
  refine Finset.sum_congr rfl fun m' hm' => ?_
  rw [Finset.sum_ite_eq, if_pos (hS m' hm'), MvPolynomial.monomial_mul, frst_add_ltr, mul_one]

theorem isL_monomial_ltr (m : σ →₀ ℕ) (a : K) : IsL fs (monomial (ltr fs m) a) := by
  intro m' hm' v hv
  have e := MvPolynomial.support_monomial_subset hm'
  rw [Finset.mem_singleton] at e
  subst e
  exact ltr_isL fs m v hv

theorem isF_monomial_frst (m : σ →₀ ℕ) (a : K) : IsF fs (monomial (frst fs m) a) := by
  intro m' hm' v hv
  have e := MvPolynomial.support_monomial_subset hm'
  rw [Finset.mem_singleton] at e
  subst e
  exact frst_isF fs m v hv

theorem monomial_split (m : σ →₀ ℕ) (a : K) :
    monomial m a = monomial (frst fs m) a * monomial (ltr fs m) 1 := by
  rw [MvPolynomial.monomial_mul, frst_add_ltr, mul_one]

end Ext

end Formalism.CountingSumsFrames

namespace Formalism.CountingSumsFrames

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
    have e := h v (Finsupp.mem_support_iff.mpr hv)
    rcases smul_eq_zero.mp e with h1 | h1
    · exact absurd h1 hv
    · exact h1
  · intro h v hv
    rw [h v (Finsupp.mem_support_iff.mp hv), smul_zero]

theorem isF_iff (j0 : ℕ) (g : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    IsF (fsj N r j0) g ↔ g ∈ weightedHomogeneousSubmodule ℚ_[p] (wlat N r j0) 0 := by
  rw [mem_weightedHomogeneousSubmodule]
  constructor
  · intro h m hm
    refine (weight_eq_zero_iff _ (fun v => by unfold wlat; split_ifs <;> omega) m).mpr fun v hv => ?_
    have := h m (mem_support_iff.mpr hm) v hv
    simp [wlat, fsj] at this ⊢; omega
  · intro h m hm v hv
    have := (weight_eq_zero_iff _ (fun v => by unfold wlat; split_ifs <;> omega) m).mp
      (h (mem_support_iff.mp hm)) v hv
    unfold wlat at this; unfold fsj; split_ifs at this with h1
    · exact h1
    · omega

theorem isL_iff (j0 : ℕ) (g : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    IsL (fsj N r j0) g ↔ g ∈ weightedHomogeneousSubmodule ℚ_[p] (wfir N r j0) 0 := by
  rw [mem_weightedHomogeneousSubmodule]
  constructor
  · intro h m hm
    refine (weight_eq_zero_iff _ (fun v => by unfold wfir; split_ifs <;> omega) m).mpr fun v hv => ?_
    have := h m (mem_support_iff.mpr hm) v hv
    simp [wfir, fsj] at this ⊢; omega
  · intro h m hm v hv
    have := (weight_eq_zero_iff _ (fun v => by unfold wfir; split_ifs <;> omega) m).mp
      (h (mem_support_iff.mp hm)) v hv
    unfold wfir at this; unfold fsj; split_ifs at this with h1
    · omega
    · exact h1

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
  by_contra h
  exact hq m hm v h (by unfold fsj; omega)

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
  classical
  rw [Finsupp.weight_apply, Finsupp.sum]
  refine Finset.sum_eq_zero fun v hv => ?_
  have := hm v (Finsupp.mem_support_iff.mp hv)
  simp only [fsj, not_lt] at this
  have h3 : ¬ (v.1 : ℕ) < J := by omega
  simp [wv, h3]

theorem slc_wh (L : Letters N) {j0 J : ℕ} (hJ : J ≤ j0) (m : Fin N × Fin r →₀ ℕ) {ν : Fin r → ℤ}
    {x : MvPolynomial (Fin N × Fin r) ℚ_[p]} (hx : x ∈ weightedHomogeneousSubmodule ℚ_[p] (wv L J) ν) :
    slc (fsj N r j0) m x ∈ weightedHomogeneousSubmodule ℚ_[p] (wv L J) ν := by
  classical
  rw [x.as_sum, map_sum]
  refine Submodule.sum_mem _ fun m' hm' => ?_
  rw [sl_monomial]
  split_ifs
  · rw [mem_weightedHomogeneousSubmodule]
    apply isWeightedHomogeneous_monomial
    have h1 : Finsupp.weight (wv L J) m' = ν := hx (mem_support_iff.mp hm')
    have h2 := weight_wv_zero L hJ (ltr (fsj N r j0) m') (ltr_isL _ m')
    rw [← h1]
    conv_rhs => rw [← frst_add_ltr (fsj N r j0) m']
    rw [map_add, h2, add_zero]
  · exact Submodule.zero_mem _

end Formalism.CountingSumsFrames

namespace Formalism.CountingSumsFrames

open MvPolynomial Finset Formalism.GM.DimensionMonotonicity Formalism.GM.M

variable {p : ℕ} [Fact p.Prime] {N r : ℕ}

theorem slc_ycond [NeZero r] (L : Letters N) {j0 J : ℕ} (hJ : J ≤ j0) (M : WithTop ℤ) (m : Fin N × Fin r →₀ ℕ)
    {F : MvPolynomial (Fin N × Fin r) ℚ_[p]} (hF : F ∈ YCond p L J M) : slc (fsj N r j0) m F ∈ YCond p L J M :=
  ycond_of_comm L J M (slc (fsj N r j0) m) (fun c d F => slc_glAct L hJ c d m F) (fun ν F hF => slc_wh L hJ m hF) F hF

theorem slc_pol (L : Letters N) (j0 : ℕ) (m : Fin N × Fin r →₀ ℕ) {x : MvPolynomial (Fin N × Fin r) ℚ_[p]}
    (hx : x ∈ Pol p r L) : slc (fsj N r j0) m x ∈ Pol p r (Lz L j0) := by
  classical
  rw [x.as_sum, map_sum]
  refine Submodule.sum_mem _ fun m' hm' => ?_
  rw [sl_monomial]
  split_ifs
  · rw [Pol, MvPolynomial.mem_restrictSupport_iff]
    refine (Finset.coe_subset.mpr (support_monomial_subset)).trans ?_
    intro d hd
    rw [Finset.coe_singleton, Set.mem_singleton_iff] at hd; subst hd
    have hmd : MultiDeg L m' := ((MvPolynomial.mem_restrictSupport_iff ℚ_[p]).mp hx) hm'
    intro i
    simp only [frst, Finsupp.filter_apply, fsj, Lz]
    split_ifs with h
    · simpa [h] using hmd i
    · simp [h]
  · exact Submodule.zero_mem _

theorem isF_of_polLz (L : Letters N) (j0 : ℕ) {y : MvPolynomial (Fin N × Fin r) ℚ_[p]}
    (hy : y ∈ Pol p r (Lz L j0)) : IsF (fsj N r j0) y := by
  intro m hm v hv
  have hmd : MultiDeg (Lz L j0) m := ((MvPolynomial.mem_restrictSupport_iff ℚ_[p]).mp hy) hm
  by_contra h
  have h1 := hmd v.1
  simp only [Lz, fsj] at h1 h
  rw [if_neg h] at h1
  have := (Finset.sum_eq_zero_iff.mp h1) v.2 (Finset.mem_univ _)
  exact hv this

theorem mul_ltr_pol (L : Letters N) (j0 : ℕ) {g : MvPolynomial (Fin N × Fin r) ℚ_[p]} (hg : g ∈ Pol p r (Lz L j0))
    {m' : Fin N × Fin r →₀ ℕ} (hm : MultiDeg L m') : g * monomial (ltr (fsj N r j0) m') 1 ∈ Pol p r L := by
  rw [pol_iff] at hg ⊢
  have hq : IsWeightedHomogeneous (wL N r) (monomial (ltr (fsj N r j0) m') (1 : ℚ_[p]))
      (Finsupp.weight (wL N r) (ltr (fsj N r j0) m')) := isWeightedHomogeneous_monomial _ _ _ rfl
  convert hg.mul hq using 1
  funext i
  rw [Pi.add_apply, weight_wL]
  by_cases h : (i : ℕ) < j0
  · have e : ∑ c, ((ltr (fsj N r j0) m' (i, c) : ℕ) : ℤ) = 0 := Finset.sum_eq_zero fun c _ => by
      rw [ltr, Finsupp.filter_apply, if_neg (by simp [fsj]; omega)]; simp
    rw [e, add_zero]; simp [Lz, h]
  · have e : ∑ c, ((ltr (fsj N r j0) m' (i, c) : ℕ) : ℤ) = L.deg i := by
      rw [← hm i]; push_cast
      exact Finset.sum_congr rfl fun c _ => by rw [ltr, Finsupp.filter_apply, if_pos (by simp [fsj]; omega)]
    rw [e]; simp [Lz, h]

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
  classical
  rw [Finsupp.weight_apply, Finsupp.weight_apply, Finsupp.sum, Finsupp.sum]
  refine Finset.sum_congr rfl fun v hv => ?_
  have := hm v (Finsupp.mem_support_iff.mp hv)
  simp only [fsj] at this
  have h2 : (v.1 : ℕ) < J := by omega
  simp [wv, this, h2]

theorem wh_first (L : Letters N) {j0 J : ℕ} (hJ : j0 ≤ J) {ν : Fin r → ℤ} {y : MvPolynomial (Fin N × Fin r) ℚ_[p]}
    (hF : IsF (fsj N r j0) y) (hy : y ∈ weightedHomogeneousSubmodule ℚ_[p] (wv L j0) ν) :
    y ∈ weightedHomogeneousSubmodule ℚ_[p] (wv L J) ν := by
  rw [mem_weightedHomogeneousSubmodule] at hy ⊢
  intro m hm
  rw [weight_first L hJ m (hF m (mem_support_iff.mpr hm))]
  exact hy hm

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

end Formalism.CountingSumsFrames

namespace Formalism.CountingSumsFrames

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

theorem whc_comm {σ M : Type} [AddCommMonoid M] (w : σ → M) (A : MvPolynomial σ ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial σ ℚ_[p])
    (hA : ∀ D x, x ∈ weightedHomogeneousSubmodule ℚ_[p] w D → A x ∈ weightedHomogeneousSubmodule ℚ_[p] w D)
    (D : M) (x : MvPolynomial σ ℚ_[p]) :
    weightedHomogeneousComponent w D (A x) = A (weightedHomogeneousComponent w D x) := by
  classical
  have hx : x = ∑ ν ∈ x.support.image (Finsupp.weight w), weightedHomogeneousComponent w ν x := by
    ext d
    rw [coeff_sum]
    simp only [coeff_weightedHomogeneousComponent]
    rw [Finset.sum_ite_eq]
    split_ifs with h
    · rfl
    · by_contra hne
      exact h (Finset.mem_image.mpr ⟨d, mem_support_iff.mpr hne, rfl⟩)
  conv_lhs => rw [hx]
  rw [map_sum, map_sum]
  have e : ∀ ν, weightedHomogeneousComponent w D (A (weightedHomogeneousComponent w ν x)) =
      if ν = D then A (weightedHomogeneousComponent w ν x) else 0 := fun ν => by
    rw [weightedHomogeneousComponent_of_mem (hA ν _ (weightedHomogeneousComponent_mem w x ν))]
    by_cases h : ν = D
    · subst h; simp
    · rw [if_neg h, if_neg (Ne.symm h)]
  simp only [e, Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [weightedHomogeneousComponent_eq_zero', map_zero]
    intro d hd h'
    exact h (Finset.mem_image.mpr ⟨d, hd, h'⟩)

theorem whc_keep {σ M M' : Type} [AddCommMonoid M] [AddCommMonoid M'] (w : σ → M) (w' : σ → M') (ν : M')
    (D : M) {x : MvPolynomial σ ℚ_[p]} (hx : x ∈ weightedHomogeneousSubmodule ℚ_[p] w D) :
    weightedHomogeneousComponent w' ν x ∈ weightedHomogeneousSubmodule ℚ_[p] w D := by
  classical
  rw [mem_weightedHomogeneousSubmodule] at hx ⊢
  intro m hm
  rw [coeff_weightedHomogeneousComponent] at hm
  split_ifs at hm
  · exact hx hm
  · exact absurd rfl hm

theorem psi_glAct (L L' : Letters N) (j0 j : ℕ) (c d : Fin r) (x : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    psi p L j0 (glAct p L' j c d x) = glAct p L' j c d (psi p L j0 x) :=
  whc_comm _ _ (fun D x hx => glAct_wL L' j c d hx) _ x

theorem psi_comp (L L' : Letters N) (j0 j : ℕ) (ν : Fin r → ℤ) (x : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    psi p L j0 ((GA p L' j).comp ν x) = (GA p L' j).comp ν (psi p L j0 x) :=
  whc_comm _ ((GA p L' j).comp ν) (fun D x hx => whc_keep _ _ _ _ hx) _ x

theorem phi_props (L : Letters N) (j0 : ℕ)
    (π : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hπP : ∀ x ∈ Pol p r (Lz L j0), π x ∈ Pol p r (Lz L j0))
    (hπE : ∀ x ∈ Pol p r (Lz L j0), ∀ c d, π (glAct p L j0 c d x) = glAct p L j0 c d (π x))
    (hπc : ∀ x ∈ Pol p r (Lz L j0), ∀ ν, π ((GA p L j0).comp ν x) = (GA p L j0).comp ν (π x)) :
    (∀ c d x, (π ∘ₗ psi p L j0) (glAct p L j0 c d x) = glAct p L j0 c d ((π ∘ₗ psi p L j0) x)) ∧
    (∀ ν x, x ∈ weightedHomogeneousSubmodule ℚ_[p] (wv L j0) ν →
      (π ∘ₗ psi p L j0) x ∈ weightedHomogeneousSubmodule ℚ_[p] (wv L j0) ν) ∧
    (∀ x, (π ∘ₗ psi p L j0) x ∈ Pol p r (Lz L j0)) := by
  refine ⟨fun c d x => ?_, fun ν x hx => ?_, fun x => hπP _ (psi_mem L j0 x)⟩
  · simp only [LinearMap.comp_apply]
    rw [psi_glAct, hπE _ (psi_mem L j0 x)]
  · have e : (GA p L j0).comp ν x = x := by
      show weightedHomogeneousComponent (wv L j0) ν x = x
      rw [weightedHomogeneousComponent_of_mem hx, if_pos rfl]
    simp only [LinearMap.comp_apply]
    rw [← e, psi_comp, hπc _ (psi_mem L j0 x)]
    exact weightedHomogeneousComponent_mem _ _ _

end Formalism.CountingSumsFrames

namespace Formalism.CountingSumsFrames

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
  · rw [Mup, if_neg hk, ycond_top]; exact Submodule.mem_top

theorem polynomial_finite_weights (L : Letters N) (j0 : ℕ) : (GA p L j0).FinW (Pol p r (Lz L j0)) :=
  pol_finW (Lz L j0) j0

theorem exists_pi [NeZero r] (L : Letters N) (j0 : ℕ) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ)
    {ι : Type} [Fintype ι] [DecidableEq ι] (h : ι → MvPolynomial (Fin N × Fin r) ℚ_[p]) (la : ι → Fin r → ℤ)
    (hh : ∀ i, (GA p L j0).IsHW (la i) (h i)) (hhP : ∀ i, h i ∈ Pol p r (Lz L j0))
    (hli : LinearIndependent ℚ_[p] h)
    (hsp : ∀ μ v, v ∈ Pol p r (Lz L j0) → (GA p L j0).IsHW μ v → v ∈ Submodule.span ℚ_[p] (Set.range h))
    (hspC : ∀ μ v, v ∈ Cset p L j0 J M → (GA p L j0).IsHW μ v →
      v ∈ Submodule.span ℚ_[p] (h '' {i | h i ∈ Cset p L j0 J M})) :
    ∃ π : ι → MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p],
      (∀ i x, π i x ∈ (GA p L j0).gS {h i}) ∧ (∀ i, ∀ x ∈ (GA p L j0).gS {h i}, π i x = x) ∧
      (∀ i j, j ≠ i → ∀ x ∈ (GA p L j0).gS {h j}, π i x = 0) ∧
      (∀ x ∈ Pol p r (Lz L j0), ∑ i, π i x = x) ∧
      (∀ i, ∀ x ∈ Cset p L j0 J M, π i x ∈ Cset p L j0 J M) ∧
      (∀ i, h i ∉ Cset p L j0 J M → ∀ x ∈ Cset p L j0 J M, π i x = 0) ∧
      (∀ i, ∀ x ∈ Pol p r (Lz L j0), ∀ c d, π i (glAct p L j0 c d x) = glAct p L j0 c d (π i x)) ∧
      (∀ i, ∀ x ∈ Pol p r (Lz L j0), ∀ ν, π i ((GA p L j0).comp ν x) = (GA p L j0).comp ν (π i x)) := by
  classical
  have hP1s : (GA p L j0).Stable (Pol p r (Lz L j0)) := pol_stable L (Lz L j0) j0
  obtain ⟨S, hS⟩ := polynomial_finite_weights (p := p) (r := r) L j0
  have hind := GlX.indep_hw (GA p L j0) hP1s hS h la hh hhP hli
  have hRW : ∀ i, (GA p L j0).gS {h i} ≤ Pol p r (Lz L j0) := fun i =>
    (GA p L j0).gS_le (by simpa using hhP i) hP1s
  have hWR := GlX.span_hw (GA p L j0) hP1s hS h la hh hhP (fun i => hli.ne_zero i) hsp
  obtain ⟨π, h1, h2, h3⟩ := proj_exists (W := Pol p r (Lz L j0)) (fun i => (GA p L j0).gS {h i}) hind hRW hWR
  have hCs := C_stable (p := p) (r := r) L j0 J M
  have hCW : Cset p L j0 J M ≤ Pol p r (Lz L j0) := inf_le_left
  have hCR : Cset p L j0 J M ≤ ⨆ (j : {j // h j ∈ Cset p L j0 J M}), (GA p L j0).gS {h j} := by
    refine GlX.span_hw (GA p L j0) hCs (fun x hx => hS x (hCW hx)) (fun j : {j // h j ∈ Cset p L j0 J M} => h j)
      (fun j => la j) (fun j => hh j) (fun j => j.2) (fun j => hli.ne_zero (j : ι)) ?_
    intro μ v hv hvh
    have := hspC μ v hv hvh
    rwa [Set.image_eq_range] at this
  refine ⟨π, h1, h2, h3, proj_sum _ hWR π h2 h3, fun i x hx => ?_, fun i hi x hx => ?_, fun i x hx c d => ?_,
    fun i x hx ν => ?_⟩
  · refine Submodule.iSup_induction _ (motive := fun x => π i x ∈ Cset p L j0 J M) (hCR hx) (fun j y hy => ?_)
      (by simp) (fun x y hx hy => by rw [map_add]; exact Submodule.add_mem _ hx hy)
    by_cases hji : (j : ι) = i
    · rw [h2 i y (hji ▸ hy)]
      exact (GA p L j0).gS_le (by simpa using j.2) hCs hy
    · rw [h3 i j hji y hy]; exact Submodule.zero_mem _
  · refine Submodule.iSup_induction _ (motive := fun x => π i x = 0) (hCR hx) (fun j y hy => ?_)
      (by simp) (fun x y hx hy => by rw [map_add, hx, hy, add_zero])
    exact h3 i j (fun hji => hi (hji ▸ j.2)) y hy
  · exact proj_comm _ hWR π h2 h3 (glAct p L j0 c d) (fun j x hx => (GA p L j0).gS_stable _ c d x hx) i x hx
  · exact proj_comm _ hWR π h2 h3 ((GA p L j0).comp ν)
      (fun j x hx => (GA p L j0).graded_of ((GA p L j0).gS_stable _) ν x hx) i x hx

end Formalism.CountingSumsFrames

namespace Formalism.CountingSumsFrames

open MvPolynomial Finset Formalism.GM.DimensionMonotonicity Formalism.GM.M

theorem finrank_of_proj {K V : Type} [Field K] [AddCommGroup V] [Module K V] (Y : Submodule K V)
    [FiniteDimensional K Y] {ι : Type} [Fintype ι] [DecidableEq ι] (Q : ι → Submodule K V) (P : ι → V →ₗ[K] V)
    (hQY : ∀ i, Q i ≤ Y) (c1 : ∀ i, ∀ x ∈ Y, P i x ∈ Q i) (c2 : ∀ i, ∀ x ∈ Q i, P i x = x)
    (c3 : ∀ i j, i ≠ j → ∀ x ∈ Q j, P i x = 0) (c4 : ∀ x ∈ Y, ∑ i, P i x = x) :
    Module.finrank K Y = ∑ i, Module.finrank K (Q i) := by
  haveI : ∀ i, FiniteDimensional K (Q i) := fun i => Submodule.finiteDimensional_of_le (hQY i)
  let f : Y →ₗ[K] (∀ i, Q i) :=
    LinearMap.pi fun i => ((P i).comp Y.subtype).codRestrict (Q i) (fun x => c1 i x x.2)
  let g : (∀ i, Q i) →ₗ[K] Y := ∑ i, (Submodule.inclusion (hQY i)).comp (LinearMap.proj i)
  have hgf : ∀ x : Y, g (f x) = x := by
    intro x
    apply Subtype.ext
    simp only [g, f, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply, LinearMap.pi_apply,
      LinearMap.codRestrict_apply, Submodule.coe_sum, Submodule.coe_inclusion, Submodule.subtype_apply]
    exact c4 x x.2
  have hfg : ∀ q, f (g q) = q := by
    intro q
    funext j
    apply Subtype.ext
    show P j (↑(g q)) = ↑(q j)
    simp only [g, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply, Submodule.coe_sum,
      Submodule.coe_inclusion]
    rw [map_sum, Finset.sum_eq_single j]
    · exact c2 j _ (q j).2
    · intro i _ hij
      exact c3 j i (Ne.symm hij) _ (q i).2
    · intro hj
      exact absurd (Finset.mem_univ _) hj
  let e : Y ≃ₗ[K] (∀ i, Q i) := LinearEquiv.ofLinear f g (LinearMap.ext hfg) (LinearMap.ext hgf)
  rw [e.finrank_eq, Module.finrank_pi_fintype]

variable {p : ℕ} [Fact p.Prime] {N r : ℕ}

noncomputable def YYs (p : ℕ) [Fact p.Prime] [NeZero r] (L : Letters N) (j0 : ℕ) {q : ℕ} (J : Fin q → ℕ)
    (M : Fin q → WithTop ℤ) (F : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]) :=
  Y p L J M ⊓ Submodule.span ℚ_[p] {x | ∃ g ∈ (GA p L j0).gS {F},
    ∃ q ∈ MvPolynomial.supported ℚ_[p] {v : Fin N × Fin r | j0 ≤ (v.1 : ℕ)}, x = g * q}

theorem monomial_ltr_supported (j0 : ℕ) (m : Fin N × Fin r →₀ ℕ) :
    (monomial (ltr (fsj N r j0) m) (1 : ℚ_[p])) ∈ MvPolynomial.supported ℚ_[p] {v : Fin N × Fin r | j0 ≤ (v.1 : ℕ)} := by
  rw [MvPolynomial.mem_supported, MvPolynomial.vars_monomial one_ne_zero]
  intro v hv
  have e := ltr_isL (fsj N r j0) m v (Finsupp.mem_support_iff.mp (Finset.mem_coe.mp hv))
  simp only [fsj, not_lt] at e
  exact e

theorem ext_mem_span (j0 : ℕ) (U : Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]))
    (φ : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p]) (hφ : ∀ x, φ x ∈ U)
    (x : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    ext (fsj N r j0) φ x ∈ Submodule.span ℚ_[p] {x | ∃ g ∈ U,
      ∃ q ∈ MvPolynomial.supported ℚ_[p] {v : Fin N × Fin r | j0 ≤ (v.1 : ℕ)}, x = g * q} := by
  classical
  rw [ext_eq_sum (fsj N r j0) φ x (x.support.image (ltr (fsj N r j0))) (fun m hm => Finset.mem_image_of_mem _ hm)]
  refine Submodule.sum_mem _ fun m hm => ?_
  obtain ⟨m', -, rfl⟩ := Finset.mem_image.mp hm
  exact Submodule.subset_span ⟨_, hφ _, _, monomial_ltr_supported j0 m', rfl⟩

theorem isL_monomial_of (j0 : ℕ) (b : Fin N × Fin r →₀ ℕ) (hb : ∀ v : Fin N × Fin r, (v.1 : ℕ) < j0 → b v = 0) (a : ℚ_[p]) :
    IsL (fsj N r j0) (monomial b a) := by
  intro m hm v hv hlt
  have e := MvPolynomial.support_monomial_subset hm
  rw [Finset.mem_singleton] at e
  subst e
  exact hv (hb v hlt)

theorem ext_rep (L : Letters N) (j0 : ℕ) (U : Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]))
    (hU : U ≤ Pol p r (Lz L j0)) {x : MvPolynomial (Fin N × Fin r) ℚ_[p]}
    (hx : x ∈ Submodule.span ℚ_[p] {x | ∃ g ∈ U,
      ∃ q ∈ MvPolynomial.supported ℚ_[p] {v : Fin N × Fin r | j0 ≤ (v.1 : ℕ)}, x = g * q}) :
    ∃ s : Finset (Fin N × Fin r →₀ ℕ), ∃ a : (Fin N × Fin r →₀ ℕ) → MvPolynomial (Fin N × Fin r) ℚ_[p],
      (∀ b, a b ∈ U) ∧ x = ∑ b ∈ s, a b * monomial b 1 ∧
      ∀ a' : (Fin N × Fin r →₀ ℕ) → MvPolynomial (Fin N × Fin r) ℚ_[p], (∀ b, a' b ∈ Pol p r (Lz L j0)) →
        ∀ φ : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p],
        ext (fsj N r j0) φ (∑ b ∈ s, a' b * monomial b 1) = ∑ b ∈ s, φ (a' b) * monomial b 1 := by
  obtain ⟨s, a, hs, ha, hxs⟩ := rep_span U j0 hx
  refine ⟨s, a, ha, hxs, fun a' ha' φ => ?_⟩
  rw [map_sum]
  exact Finset.sum_congr rfl fun b hb => ext_mul _ φ (isF_of_polLz L j0 (ha' b)) (isL_monomial_of j0 b (hs b hb) 1)

end Formalism.CountingSumsFrames

namespace Formalism.CountingSumsFrames

open MvPolynomial Finset Formalism.GM.DimensionMonotonicity Formalism.GM.M

theorem GlX.exists_theta {K V : Type} [Field K] [CharZero K] [AddCommGroup V] [Module K V] {r : ℕ} (G : GlW K V r)
    {W : Submodule K V} (hW : G.Stable W) (hWf : G.FinW W) {la : Fin r → ℤ} {h h' : V}
    (hh : G.IsHW la h) (hh' : G.IsHW la h') (hhW : h ∈ W) (hh'W : h' ∈ W) (h0 : h ≠ 0) (h0' : h' ≠ 0)
    (π π' : V →ₗ[K] V) (h1 : ∀ x, π x ∈ G.gS {h}) (h2 : ∀ x ∈ G.gS {h}, π x = x)
    (hE : ∀ x ∈ W, ∀ c d, π (G.E c d x) = G.E c d (π x))
    (h1' : ∀ x, π' x ∈ G.gS {h'}) (h2' : ∀ x ∈ G.gS {h'}, π' x = x)
    (hE' : ∀ x ∈ W, ∀ c d, π' (G.E c d x) = G.E c d (π' x)) :
    ∃ θ θ' : V →ₗ[K] V, (∀ x, θ x ∈ G.gS {h'}) ∧ (∀ x ∈ W, ∀ c d, θ (G.E c d x) = G.E c d (θ x)) ∧
      (∀ x, θ' x ∈ G.gS {h}) ∧ (∀ x ∈ W, ∀ c d, θ' (G.E c d x) = G.E c d (θ' x)) ∧
      (∀ x ∈ G.gS {h}, θ' (θ x) = x) := by
  have hk := GlX.ker_le G hW hWf hh hh' hhW hh'W h0
  have hk' := GlX.ker_le G hW hWf hh' hh hh'W hhW h0'
  let ρ : V →ₗ[K] LinearMap.range (GlX.Lv G h) := π.codRestrict _ (fun x => by rw [GlX.range_Lv]; exact h1 x)
  let ρ' : V →ₗ[K] LinearMap.range (GlX.Lv G h') := π'.codRestrict _ (fun x => by rw [GlX.range_Lv]; exact h1' x)
  have hρ : ∀ x, ((ρ x : LinearMap.range (GlX.Lv G h)) : V) = π x := fun x => rfl
  have hρ' : ∀ x, ((ρ' x : LinearMap.range (GlX.Lv G h')) : V) = π' x := fun x => rfl
  refine ⟨GlX.tr G hk ∘ₗ ρ, GlX.tr G hk' ∘ₗ ρ', fun x => ?_, fun x hx c d => ?_, fun x => ?_, fun x hx c d => ?_,
    fun x hx => ?_⟩
  · rw [← GlX.range_Lv]; exact GlX.tr_mem G hk _
  · have hy : G.E c d (ρ x) ∈ LinearMap.range (GlX.Lv G h) :=
      (GlX.range_Lv G h).ge (G.gS_stable _ c d _ (h1 x))
    have e : ρ (G.E c d x) = ⟨G.E c d (ρ x), hy⟩ := Subtype.ext (hE x hx c d)
    simp only [LinearMap.comp_apply]
    rw [e, GlX.tr_E]
  · rw [← GlX.range_Lv]; exact GlX.tr_mem G hk' _
  · have hy : G.E c d (ρ' x) ∈ LinearMap.range (GlX.Lv G h') :=
      (GlX.range_Lv G h').ge (G.gS_stable _ c d _ (h1' x))
    have e : ρ' (G.E c d x) = ⟨G.E c d (ρ' x), hy⟩ := Subtype.ext (hE' x hx c d)
    simp only [LinearMap.comp_apply]
    rw [e, GlX.tr_E]
  · simp only [LinearMap.comp_apply]
    have hm : GlX.tr G hk (ρ x) ∈ G.gS {h'} := by rw [← GlX.range_Lv]; exact GlX.tr_mem G hk _
    have e : ρ' (GlX.tr G hk (ρ x)) = ⟨GlX.tr G hk (ρ x), GlX.tr_mem G hk _⟩ := Subtype.ext (h2' _ hm)
    rw [e, GlX.tr_tr G hk hk', hρ, h2 x hx]

end Formalism.CountingSumsFrames

namespace Formalism.CountingSumsFrames

open MvPolynomial Finset Formalism.GM.DimensionMonotonicity Formalism.GM.M

variable {p : ℕ} [Fact p.Prime] {N r : ℕ}

theorem Y_fd [NeZero r] (L : Letters N) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ) :
    FiniteDimensional ℚ_[p] (Y p (r := r) L J M) := by
  haveI := pol_fd (p := p) (r := r) L
  exact Submodule.finiteDimensional_of_le (inf_le_left : Y p (r := r) L J M ≤ Pol p r L)

theorem count_Y [NeZero r] (L : Letters N) (j0 : ℕ) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ)
    {ι : Type} [Fintype ι] [DecidableEq ι] (h : ι → MvPolynomial (Fin N × Fin r) ℚ_[p]) (la : ι → Fin r → ℤ)
    (hh : ∀ i, (GA p L j0).IsHW (la i) (h i)) (hhP : ∀ i, h i ∈ Pol p r (Lz L j0))
    (hli : LinearIndependent ℚ_[p] h)
    (hsp : ∀ μ v, v ∈ Pol p r (Lz L j0) → (GA p L j0).IsHW μ v → v ∈ Submodule.span ℚ_[p] (Set.range h))
    (hspC : ∀ μ v, v ∈ Cset p L j0 J M → (GA p L j0).IsHW μ v →
      v ∈ Submodule.span ℚ_[p] (h '' {i | h i ∈ Cset p L j0 J M})) :
    Module.finrank ℚ_[p] (Y p (r := r) L J M) = ∑ i, Module.finrank ℚ_[p] (YYs p L j0 J M (h i)) ∧
    (∀ i, h i ∉ Cset p L j0 J M → YYs p L j0 J M (h i) = ⊥) ∧
    (∀ i j, h i ∈ Cset p L j0 J M → h j ∈ Cset p L j0 J M → la i = la j →
      Module.finrank ℚ_[p] (YYs p L j0 J M (h i)) ≤ Module.finrank ℚ_[p] (YYs p L j0 J M (h j))) := by
  classical
  obtain ⟨π, h1, h2, h3, hsum, hC, hC0, hE, hc⟩ := exists_pi L j0 J M h la hh hhP hli hsp hspC
  have hP1s : (GA p L j0).Stable (Pol p r (Lz L j0)) := pol_stable L (Lz L j0) j0
  have hCs := C_stable (p := p) (r := r) L j0 J M
  have hCW : Cset p L j0 J M ≤ Pol p r (Lz L j0) := inf_le_left
  have hRW : ∀ i, (GA p L j0).gS {h i} ≤ Pol p r (Lz L j0) := fun i =>
    (GA p L j0).gS_le (by simpa using hhP i) hP1s
  haveI := Y_fd (p := p) (r := r) L J M
  have hPY : ∀ i, ∀ x ∈ Y p L J M, ext (fsj N r j0) (π i ∘ₗ psi p L j0) x ∈ Y p L J M := by
    intro i
    obtain ⟨a1, a2, a3⟩ := phi_props L j0 (π i) (fun x _ => hRW i (h1 i x)) (hE i) (hc i)
    refine ext_Y L j0 J M _ a1 a2 a3 (fun x hx => ?_)
    rw [LinearMap.comp_apply, psi_id L j0 (hCW hx)]; exact hC i x hx
  have c2 : ∀ i, ∀ x ∈ YYs p L j0 J M (h i), ext (fsj N r j0) (π i ∘ₗ psi p L j0) x = x := by
    intro i x hx
    obtain ⟨s, a, ha, hxs, hext⟩ := ext_rep L j0 _ (hRW i) hx.2
    conv_lhs => rw [hxs]
    rw [hext a (fun b => hRW i (ha b))]
    conv_rhs => rw [hxs]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [LinearMap.comp_apply, psi_id L j0 (hRW i (ha b)), h2 i _ (ha b)]
  have hslsum : ∀ (φ : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
      (x : MvPolynomial (Fin N × Fin r) ℚ_[p]), ext (fsj N r j0) φ x =
      ∑ m ∈ x.support.image (ltr (fsj N r j0)), φ (slc (fsj N r j0) m x) * monomial m 1 := fun φ x =>
    ext_eq_sum (fsj N r j0) φ x _ (fun m hm => Finset.mem_image_of_mem _ hm)
  refine ⟨?_, ?_, ?_⟩
  · refine finrank_of_proj (Y p L J M) (fun i => YYs p L j0 J M (h i))
      (fun i => ext (fsj N r j0) (π i ∘ₗ psi p L j0)) (fun i => inf_le_left) (fun i x hx => ?_) c2
      (fun i j hij x hx => ?_) (fun x hx => ?_)
    · exact ⟨hPY i x hx, ext_mem_span j0 _ (π i ∘ₗ psi p L j0) (fun y => h1 i _) x⟩
    · obtain ⟨s, a, ha, hxs, hext⟩ := ext_rep L j0 _ (hRW j) hx.2
      rw [hxs, hext a (fun b => hRW j (ha b))]
      refine Finset.sum_eq_zero fun b _ => ?_
      rw [LinearMap.comp_apply, psi_id L j0 (hRW j (ha b)), h3 i j (Ne.symm hij) _ (ha b), zero_mul]
    · simp_rw [hslsum]
      rw [Finset.sum_comm]
      conv_rhs => rw [eq_sum_sl (fsj N r j0) x (x.support.image (ltr (fsj N r j0)))
        (fun m hm => Finset.mem_image_of_mem _ hm)]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [← Finset.sum_mul]
      congr 1
      have hP := slc_pol L j0 m (Submodule.mem_inf.mp hx).1
      simp only [LinearMap.comp_apply, psi_id L j0 hP]
      exact hsum _ hP
  · intro i hi
    rw [eq_bot_iff]
    intro x hx
    rw [Submodule.mem_bot, ← c2 i x hx, hslsum]
    refine Finset.sum_eq_zero fun m _ => ?_
    have hCm := slc_C L j0 J M hx.1 m
    rw [LinearMap.comp_apply, psi_id L j0 (hCW hCm), hC0 i hi _ hCm, zero_mul]
  · intro i j hi hj hij
    obtain ⟨θ, θ', t1, t2, t3, t4, t5⟩ := GlX.exists_theta (GA p L j0) hP1s (polynomial_finite_weights L j0) (hh i) (hij ▸ hh j)
      (hhP i) (hhP j) (hli.ne_zero i) (hli.ne_zero j) (π i) (π j) (h1 i) (h2 i) (hE i) (h1 j) (h2 j) (hE j)
    have hRC : (GA p L j0).gS {h j} ≤ Cset p L j0 J M := (GA p L j0).gS_le (by simpa using hj) hCs
    have hTY : ∀ x ∈ Y p L J M, ext (fsj N r j0) (θ ∘ₗ psi p L j0) x ∈ Y p L J M := by
      obtain ⟨a1, a2, a3⟩ := phi_props L j0 θ (fun x _ => hRW j (t1 x)) t2
        (GlX.comp_comm_of (GA p L j0) ((GA p L j0).graded_of hP1s) θ (fun x hx c => t2 x hx c c))
      exact ext_Y L j0 J M _ a1 a2 a3 (fun x _ => hRC (t1 _))
    let f : YYs p L j0 J M (h i) →ₗ[ℚ_[p]] YYs p L j0 J M (h j) :=
      ((ext (fsj N r j0) (θ ∘ₗ psi p L j0)).comp (YYs p L j0 J M (h i)).subtype).codRestrict _
        (fun x => ⟨hTY x x.2.1, ext_mem_span j0 _ (θ ∘ₗ psi p L j0) (fun y => t1 _) _⟩)
    have hf : Function.Injective f := by
      have hl : ∀ x : YYs p L j0 J M (h i), ext (fsj N r j0) (θ' ∘ₗ psi p L j0) (f x : MvPolynomial (Fin N × Fin r) ℚ_[p]) = x := by
        intro x
        obtain ⟨s, a, ha, hxs, hext⟩ := ext_rep L j0 _ (hRW i) x.2.2
        show ext (fsj N r j0) (θ' ∘ₗ psi p L j0) (ext (fsj N r j0) (θ ∘ₗ psi p L j0) (x : MvPolynomial (Fin N × Fin r) ℚ_[p])) = x
        conv_lhs => rw [hxs]
        rw [hext a (fun b => hRW i (ha b)), hext (fun b => (θ ∘ₗ psi p L j0) (a b)) (fun b => hRW j (t1 _))]
        conv_rhs => rw [hxs]
        refine Finset.sum_congr rfl fun b _ => ?_
        simp only [LinearMap.comp_apply]
        rw [psi_id L j0 (hRW i (ha b)), psi_id L j0 (hRW j (t1 _)), t5 _ (ha b)]
      intro x y hxy
      apply Subtype.ext
      rw [← hl x, ← hl y, hxy]
    haveI : FiniteDimensional ℚ_[p] (YYs p L j0 J M (h j)) :=
      Submodule.finiteDimensional_of_le (inf_le_left : YYs p L j0 J M (h j) ≤ Y p L J M)
    exact LinearMap.finrank_le_finrank_of_injective hf

end Formalism.CountingSumsFrames

namespace Formalism.CountingSumsFrames

open Finset

theorem basis_chain {K V : Type} [Field K] [AddCommGroup V] [Module K V] (A B : Submodule K V) (hAB : A ≤ B)
    [FiniteDimensional K B] (e : V) (he : e ∈ A) :
    ∃ b : Finset V, ((b : Set V) ⊆ (B : Set V)) ∧ LinearIndepOn K id (b : Set V) ∧
      ((B : Set V) ⊆ Submodule.span K (b : Set V)) ∧ (e ≠ 0 → e ∈ b) ∧
      ((A : Set V) ⊆ Submodule.span K ((b : Set V) ∩ (A : Set V))) ∧
      ∀ [DecidablePred (· ∈ A)], (b.filter (· ∈ A)).card = Module.finrank K A := by
  classical
  have hs : LinearIndepOn K id {x : V | x = e ∧ e ≠ 0} := by
    by_cases h0 : e = 0
    · have : {x : V | x = e ∧ e ≠ 0} = ∅ := by ext x; simp [h0]
      rw [this]; exact linearIndepOn_empty K id
    · have : {x : V | x = e ∧ e ≠ 0} = {e} := by ext x; simp [h0]
      rw [this]; exact LinearIndepOn.singleton (by simpa using h0)
  have hst : {x : V | x = e ∧ e ≠ 0} ⊆ (A : Set V) := by rintro x ⟨rfl, -⟩; exact he
  obtain ⟨bA, hbA, hsbA, hAsp, hliA⟩ := exists_linearIndepOn_id_extension hs hst
  obtain ⟨b, hbB, hbAb, hBsp, hli⟩ := exists_linearIndepOn_id_extension hliA (hbA.trans hAB)
  have hfin : b.Finite := by
    have h1 : LinearIndependent K (fun x : b => (⟨x.1, hbB x.2⟩ : B)) := by
      apply LinearIndependent.of_comp B.subtype
      exact hli
    have := h1.finite
    exact Set.toFinite b
  have hbA' : b ∩ (A : Set V) = bA := by
    apply Set.Subset.antisymm
    · rintro x ⟨hxb, hxA⟩
      by_contra hx
      have h2 : LinearIndependent K (fun x : b => (x : V)) := hli
      have h3 := h2.notMem_span_image (s := {y : b | (y : V) ∈ bA}) (x := ⟨x, hxb⟩) (by simpa using hx)
      apply h3
      have e1 : (fun x : b => (x : V)) '' {y : b | (y : V) ∈ bA} = bA := by
        ext z; constructor
        · rintro ⟨y, hy, rfl⟩; exact hy
        · intro hz; exact ⟨⟨z, hbAb hz⟩, hz, rfl⟩
      rw [e1]; exact hAsp hxA
    · intro x hx; exact ⟨hbAb hx, hbA hx⟩
  refine ⟨hfin.toFinset, by simpa using hbB, by simpa using hli, by simpa using hBsp,
    fun h0 => by simpa using hbAb (hsbA ⟨rfl, h0⟩), by simpa [hbA'] using hAsp, ?_⟩
  intro _
  have e2 : ((hfin.toFinset.filter (· ∈ A) : Finset V) : Set V) = bA := by
    rw [← hbA']; ext x; simp
  have h4 : LinearIndepOn K id ((hfin.toFinset.filter (· ∈ A) : Finset V) : Set V) := by rw [e2]; exact hliA
  have e3 : Submodule.span K bA = A := le_antisymm (Submodule.span_le.mpr hbA) hAsp
  rw [← finrank_span_finset_eq_card h4, e2, e3]

end Formalism.CountingSumsFrames

namespace Formalism.CountingSumsFrames

open MvPolynomial Finset Formalism.GM.DimensionMonotonicity Formalism.GM.M

def GlX.HWs {K V : Type} [Field K] [AddCommGroup V] [Module K V] {r : ℕ} (G : GlW K V r) (μ : Fin r → ℤ) :
    Submodule K V where
  carrier := {v | G.IsHW μ v}
  add_mem' := by
    intro x y hx hy
    exact ⟨by show G.comp μ (x + y) = x + y; rw [map_add, hx.1, hy.1],
      fun a b hab => by rw [map_add, hx.2 a b hab, hy.2 a b hab, add_zero]⟩
  zero_mem' := ⟨by show G.comp μ 0 = 0; exact map_zero _, fun a b _ => map_zero _⟩
  smul_mem' := by
    intro c x hx
    exact ⟨by show G.comp μ (c • x) = c • x; rw [map_smul, hx.1],
      fun a b hab => by rw [map_smul, hx.2 a b hab, smul_zero]⟩

variable {p : ℕ} [Fact p.Prime] {N r : ℕ}

theorem count_HW [NeZero r] (L : Letters N) (j0 : ℕ) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ)
    (S : Finset (Fin r → ℤ)) (hS : ∀ x ∈ Pol p r (Lz L j0), ∀ μ ∉ S, (GA p L j0).comp μ x = 0)
    (e : (Fin r → ℤ) → MvPolynomial (Fin N × Fin r) ℚ_[p])
    (he : ∀ μ, e μ ∈ GlX.HWs (GA p L j0) μ ⊓ Cset p L j0 J M)
    (he0 : ∀ μ, GlX.HWs (GA p L j0) μ ⊓ Cset p L j0 J M ≠ ⊥ → e μ ≠ 0) :
    Module.finrank ℚ_[p] (Y p (r := r) L J M) =
      ∑ μ ∈ S, Module.finrank ℚ_[p] (GlX.HWs (GA p L j0) μ ⊓ Cset p L j0 J M : Submodule ℚ_[p] _) *
        Module.finrank ℚ_[p] (YYs p L j0 J M (e μ)) := by
  classical
  have hCW : Cset p L j0 J M ≤ Pol p r (Lz L j0) := inf_le_left
  haveI := pol_fd (p := p) (r := r) (Lz L j0)
  haveI : ∀ μ, FiniteDimensional ℚ_[p] (GlX.HWs (GA p L j0) μ ⊓ Pol p r (Lz L j0) : Submodule ℚ_[p] _) :=
    fun μ => Submodule.finiteDimensional_of_le inf_le_right
  choose b hbB hbli hbsp hbe hbA hbcard using fun μ => basis_chain
    (GlX.HWs (GA p L j0) μ ⊓ Cset p L j0 J M) (GlX.HWs (GA p L j0) μ ⊓ Pol p r (Lz L j0))
    (inf_le_inf_left _ hCW) (e μ) (he μ)
  have hbHW : ∀ μ x, x ∈ b μ → (GA p L j0).IsHW μ x := fun μ x hx => (hbB μ hx).1
  have hbP : ∀ μ x, x ∈ b μ → x ∈ Pol p r (Lz L j0) := fun μ x hx => (hbB μ hx).2
  have hμS : ∀ μ v, v ∈ Pol p r (Lz L j0) → (GA p L j0).IsHW μ v → v ≠ 0 → μ ∈ S := by
    intro μ v hv hvh hv0
    by_contra hn
    exact hv0 (by have := hS v hv μ hn; rwa [hvh.1] at this)
  let h : ((μ : {μ // μ ∈ S}) × {x // x ∈ b μ.1}) → MvPolynomial (Fin N × Fin r) ℚ_[p] := fun i => i.2.1
  let la : ((μ : {μ // μ ∈ S}) × {x // x ∈ b μ.1}) → Fin r → ℤ := fun i => i.1.1
  have hli : LinearIndependent ℚ_[p] h := by
    rw [Fintype.linearIndependent_iff]
    rintro g hg ⟨ν, x⟩
    have h1 : ∑ y : {y // y ∈ b ν.1}, g ⟨ν, y⟩ • (y.1 : MvPolynomial (Fin N × Fin r) ℚ_[p]) = 0 := by
      have h0 := congrArg ((GA p L j0).comp ν.1) hg
      rw [map_zero, Fintype.sum_sigma, map_sum, Finset.sum_eq_single ν] at h0
      · rw [map_sum] at h0
        rw [← h0]
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [map_smul]
        show _ = g ⟨ν, y⟩ • (GA p L j0).comp ν.1 y.1
        rw [(hbHW ν.1 y.1 y.2).1]
      · intro μ _ hμ
        rw [map_sum]
        refine Finset.sum_eq_zero fun y _ => ?_
        rw [map_smul]
        show g ⟨μ, y⟩ • (GA p L j0).comp ν.1 y.1 = 0
        rw [(GA p L j0).comp_of_isWt (hbHW μ.1 y.1 y.2).1, if_neg (fun hh => hμ (Subtype.ext hh.symm)), smul_zero]
      · simp
    have h2 := (linearIndepOn_finset_iff.mp (hbli ν.1)) (fun y => if hy : y ∈ b ν.1 then g ⟨ν, ⟨y, hy⟩⟩ else 0) (by
      rw [← Finset.sum_attach, ← h1, Finset.univ_eq_attach]
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [dif_pos y.2]; rfl) x.1 x.2
    simpa [x.2] using h2
  obtain ⟨k1, k2, k3⟩ := count_Y L j0 J M h la (fun i => hbHW _ _ i.2.2) (fun i => hbP _ _ i.2.2) hli
    (by
      intro μ v hv hvh
      by_cases hv0 : v = 0
      · rw [hv0]; exact Submodule.zero_mem _
      · have hμ := hμS μ v hv hvh hv0
        refine Submodule.span_mono ?_ (hbsp μ ⟨hvh, hv⟩)
        intro x hx
        exact ⟨⟨⟨μ, hμ⟩, ⟨x, hx⟩⟩, rfl⟩)
    (by
      intro μ v hv hvh
      by_cases hv0 : v = 0
      · rw [hv0]; exact Submodule.zero_mem _
      · have hμ := hμS μ v (hCW hv) hvh hv0
        refine Submodule.span_mono ?_ (hbA μ ⟨hvh, hv⟩)
        rintro x ⟨hx, hxA⟩
        exact ⟨⟨⟨μ, hμ⟩, ⟨x, hx⟩⟩, hxA.2, rfl⟩)
  rw [k1, Fintype.sum_sigma, ← Finset.sum_coe_sort S]
  refine Finset.sum_congr rfl fun μ _ => ?_
  show ∑ y : {y // y ∈ b μ.1}, Module.finrank ℚ_[p] (YYs p L j0 J M y.1) = _
  rw [Finset.sum_coe_sort (b μ.1) (fun y => Module.finrank ℚ_[p] (YYs p L j0 J M y)),
    ← Finset.sum_filter_add_sum_filter_not (b μ.1) (· ∈ GlX.HWs (GA p L j0) μ.1 ⊓ Cset p L j0 J M)]
  have z2 : ∑ x ∈ (b μ.1).filter (fun x => ¬ x ∈ GlX.HWs (GA p L j0) μ.1 ⊓ Cset p L j0 J M),
      Module.finrank ℚ_[p] (YYs p L j0 J M x) = 0 := by
    refine Finset.sum_eq_zero fun x hx => ?_
    obtain ⟨hxb, hxA⟩ := Finset.mem_filter.mp hx
    have := k2 ⟨μ, ⟨x, hxb⟩⟩ (fun hC => hxA ⟨hbHW _ _ hxb, hC⟩)
    show Module.finrank ℚ_[p] (YYs p L j0 J M x) = 0
    have e1 : YYs p L j0 J M x = ⊥ := this
    rw [e1]; exact finrank_bot _ _
  have z1 : ∀ x ∈ (b μ.1).filter (· ∈ GlX.HWs (GA p L j0) μ.1 ⊓ Cset p L j0 J M),
      Module.finrank ℚ_[p] (YYs p L j0 J M x) = Module.finrank ℚ_[p] (YYs p L j0 J M (e μ.1)) := by
    intro x hx
    obtain ⟨hxb, hxA⟩ := Finset.mem_filter.mp hx
    have hx0 : x ≠ 0 := (hli.ne_zero ⟨μ, ⟨x, hxb⟩⟩ : h ⟨μ, ⟨x, hxb⟩⟩ ≠ 0)
    have hne : GlX.HWs (GA p L j0) μ.1 ⊓ Cset p L j0 J M ≠ ⊥ := fun hb => hx0 (by
      rw [hb] at hxA; exact (Submodule.mem_bot _).mp hxA)
    have heb := hbe μ.1 (he0 μ.1 hne)
    exact le_antisymm (k3 ⟨μ, ⟨x, hxb⟩⟩ ⟨μ, ⟨e μ.1, heb⟩⟩ hxA.2 (he μ.1).2 rfl)
      (k3 ⟨μ, ⟨e μ.1, heb⟩⟩ ⟨μ, ⟨x, hxb⟩⟩ (he μ.1).2 hxA.2 rfl)
  rw [z2, add_zero, Finset.sum_congr rfl z1, Finset.sum_const, hbcard, smul_eq_mul]

end Formalism.CountingSumsFrames

namespace Formalism.CountingSumsFrames

open MvPolynomial Finset Formalism.GM.DimensionMonotonicity Formalism.GM.M

variable {p : ℕ} [Fact p.Prime] {K r : ℕ}

theorem freeze_surj (LL : Letters K) (ρ : Fin r) (n : ℕ) (hS : LL.total ≤ n)
    (F : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) (hFpol' : F ∈ Pol p r (LL.snoc n))
    (hinv : IsFrozenInv p LL ρ n F) :
    ∃ f ∈ Pol p r LL, freeze p LL ρ n f = F ∧ ∀ m', coeff m' f = coeff (FB.ext n ρ m') F := by
  have hFrow : ∀ m ∈ F.support, ∑ c, m (Fin.last K, c) = n := fun m hm => by
    have h : MultiDeg (LL.snoc n) m := hFpol' (Finset.mem_coe.mpr hm)
    simpa using h (Fin.last K)
  have hcoeff := FB.coeff_ev ρ n F hFrow
  have hfpol : FB.ev p ρ F ∈ Pol p r LL := by
    rw [Pol, mem_restrictSupport_iff]
    intro m' hm'
    rw [Finset.mem_coe, mem_support_iff, hcoeff] at hm'
    have h : MultiDeg (LL.snoc n) (FB.ext n ρ m') := hFpol' (Finset.mem_coe.mpr (mem_support_iff.mpr hm'))
    intro i
    simpa using h (Fin.castSucc i)
  refine ⟨FB.ev p ρ F, hfpol, ?_, hcoeff⟩
  have hFhom : IsWeightedHomogeneous (FB.wL K r) F n := fun m hm => by
    rw [FB.weight_wL]; exact hFrow m (mem_support_iff.mpr hm)
  have hGhom : IsWeightedHomogeneous (FB.wL K r) (F - freeze p LL ρ n (FB.ev p ρ F)) n :=
    hFhom.sub (FB.hom_freeze LL ρ n hS _ hfpol)
  have hGrow : ∀ m ∈ (F - freeze p LL ρ n (FB.ev p ρ F)).support, ∑ c, m (Fin.last K, c) = n :=
    fun m hm => by rw [← FB.weight_wL]; exact hGhom (mem_support_iff.mp hm)
  have hGev : FB.ev p ρ (F - freeze p LL ρ n (FB.ev p ρ F)) = 0 := by
    rw [map_sub, FB.ev_freeze, sub_self]
  have hGinv : IsFrozenInv p LL ρ n (F - freeze p LL ρ n (FB.ev p ρ F)) := fun c hc => by
    rw [map_sub, hinv c hc, FB.freeze_inv LL ρ n _ c hc, sub_self]
  have h0 : ∀ m, FB.kk ρ m = 0 → coeff m (F - freeze p LL ρ n (FB.ev p ρ F)) = 0 := by
    intro m hm
    by_contra hne
    have hrow := hGrow m (mem_support_iff.mpr hne)
    have hZ : ∀ c, c ≠ ρ → m (Fin.last K, c) = 0 := fun c hc =>
      Finset.sum_eq_zero_iff.mp hm c (Finset.mem_erase.mpr ⟨hc, Finset.mem_univ _⟩)
    apply hne
    rw [FB.eq_ext_res n ρ m hZ hrow, ← FB.coeff_ev ρ n _ hGrow, hGev, coeff_zero]
  exact (sub_eq_zero.mp (FB.vanish LL n ρ _ hGinv h0)).symm

theorem wt_ext (LL : Letters K) (n : ℕ) (ρ c : Fin r) (m' : Fin K × Fin r →₀ ℕ) :
    wt (LL.snoc n) (K + 1) c (FB.ext n ρ m') = wt LL K c m' - (if c = ρ then (n : ℤ) else 0) := by
  unfold wt
  rw [Fin.sum_univ_castSucc]
  simp only [FB.ext_castSucc, FB.ext_last, FB.snoc_vec_castSucc, FB.snoc_vec_last, Fin.val_castSucc, Fin.val_last,
    Nat.lt_succ_self, if_true, Bool.false_eq_true, if_false]
  have e : ∀ i : Fin K, ((i : ℕ) < K + 1) = True := fun i => by simp
  have e' : ∀ i : Fin K, ((i : ℕ) < K) = True := fun i => by simp
  simp only [e, e', if_true]
  split_ifs <;> simp [sub_eq_add_neg]

theorem small_onto [NeZero r] (LK : Letters K) (ρ : Fin r) (hρ : (ρ : ℕ) = r - 1) (n : ℕ) (hS : LK.total ≤ n)
    {q : ℕ} (J : Fin q → ℕ) (Mt : Fin q → WithTop ℤ) (hJ : ∀ k, J k ≤ K) (μ : Fin r → ℤ)
    (F : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) (hFP : F ∈ Pol p r (LK.snoc n))
    (hFY : ∀ k, F ∈ YCond p (LK.snoc n) (J k) (Mt k))
    (hFw : IsWeightedHomogeneous (wv (LK.snoc n) (K + 1)) F μ)
    (hFr : ∀ a b, a < b → glAct p (LK.snoc n) (K + 1) a b F = 0) :
    ∃ f, f ∈ MMw p LK J Mt ρ (μ + ((n : ℕ) : ℤ) • Pi.single ρ 1) ∧ freeze p LK ρ n f = F := by
  classical
  have hlt : ∀ c : Fin r, c ≠ ρ → c < ρ := by
    intro c hc
    have h1 := c.isLt
    have h2 : (c : ℕ) ≠ ρ := fun h => hc (Fin.ext h)
    show (c : ℕ) < ρ
    omega
  obtain ⟨f, hfP, hfF, hco⟩ := freeze_surj LK ρ n hS F hFP (fun c hc => hFr c ρ (hlt c hc))
  refine ⟨f, ?_, hfF⟩
  have hW : f ∈ WtSpC p LK K univ (μ + ((n : ℕ) : ℤ) • Pi.single ρ 1) := by
    rw [WtSpC, mem_restrictSupport_iff]
    intro m' hm' c _
    rw [Finset.mem_coe, mem_support_iff, hco] at hm'
    have h1 := congrFun (hFw hm') c
    rw [weight_wv, wt_ext] at h1
    simp only [Pi.add_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
    split_ifs at h1 ⊢ <;> simp at h1 ⊢ <;> omega
  refine Submodule.mem_inf.mpr ⟨Submodule.mem_inf.mpr ⟨?_, Submodule.mem_inf.mpr ⟨?_, ?_⟩⟩, hW⟩
  · refine (Formalism.GM.extendWeightBounded p K r LK ρ n J Mt hS hJ f hfP).mpr ?_
    rw [hfF]
    exact Submodule.mem_inf.mpr ⟨hFP, (Submodule.mem_iInf _).mpr hFY⟩
  · rw [WtSpC, mem_restrictSupport_iff] at hW ⊢
    intro m' hm' c _
    exact hW hm' c (Finset.mem_univ c)
  · simp only [Submodule.mem_iInf, LinearMap.mem_ker]
    rintro a b ⟨ha, hb, hab⟩
    have ha' := Finset.ne_of_mem_erase ha
    have hb' := Finset.ne_of_mem_erase hb
    have h1 := glAct_freeze_gen LK n ρ a b ha' hb' f
    rw [hfF, hFr a b hab] at h1
    exact (Formalism.GM.extendBijOn p K r LK ρ n hS).1 _ (glAct_pol LK LK K a b hfP) 0 (Submodule.zero_mem _)
      (by rw [← h1, freeze_zero])

end Formalism.CountingSumsFrames

namespace Formalism.CountingSumsFrames

open MvPolynomial Finset Formalism.GM.DimensionMonotonicity Formalism.GM.M

variable {p : ℕ} [Fact p.Prime] {N r : ℕ}

theorem ycond_comap [NeZero r] {M' : ℕ} (LA : Letters M') (LB : Letters N) (ι : Fin M' → Fin N)
    (hι : ∀ a, ((ι a) : ℕ) = a) (hv : ∀ a, LB.vec (ι a) = LA.vec a)
    (hinj : Function.Injective (fun x : Fin M' × Fin r => (ι x.1, x.2))) (j : ℕ) (Mth : WithTop ℤ)
    (hwv : (wv LB j) ∘ (fun x : Fin M' × Fin r => (ι x.1, x.2)) = wv LA j)
    {F' : MvPolynomial (Fin M' × Fin r) ℚ_[p]}
    (hF : rename (fun x : Fin M' × Fin r => (ι x.1, x.2)) F' ∈ YCond p LB j Mth) : F' ∈ YCond p LA j Mth := by
  classical
  have hle : (YCond p LB j Mth).comap (rename (fun x : Fin M' × Fin r => (ι x.1, x.2))).toLinearMap ≤
      YCond p LA j Mth := by
    refine le_sSup ⟨?_, ?_⟩
    · intro G hG
      rw [mem_restrictSupport_iff]
      intro m hm
      show ((wt LA j 0 m : ℤ) : WithTop ℤ) ≤ Mth
      have h1 : Finsupp.mapDomain (fun x : Fin M' × Fin r => (ι x.1, x.2)) m ∈
          (rename (fun x : Fin M' × Fin r => (ι x.1, x.2)) G).support := by
        rw [support_rename_of_injective hinj]; exact Finset.mem_image_of_mem _ hm
      have h2 := Formalism.GM.FrozenVariableComponents.wt_le_of_mem p LB j Mth _ hG _ h1
      rwa [← weight_wv, weight_mapDomain, hwv, weight_wv] at h2
    · intro c d G hG
      show rename _ (glAct p LA j c d G) ∈ YCond p LB j Mth
      rw [glAct_rename LA LB ι hι hv j c d G]
      exact Formalism.GM.FrozenVariableComponents.ycond_stable p LB j Mth c d _ hG
  exact hle hF

section Comparison₂
variable [NeZero N] (LL : Letters N) (T : TieData) (hadm : T.Admissible LL) (i : Fin T.t)

include hadm

theorem deg_compat (n : Fin T.t → ℕ) (a : Fin (T.pos i + 1 + 1)) :
    (((LL.setTies T n).takeD (T.pos i + 1)).snoc (n i)).deg a = (LL.setTies T n).deg (ιF N (T.pos i + 1) a) := by
  have hK := hK_of_adm LL T hadm i
  induction a using Fin.lastCases with
  | last =>
    rw [Formalism.GM.M.FB.snoc_deg_last]
    have e : ιF N (T.pos i + 1) (Fin.last (T.pos i + 1)) = ⟨T.pos i + 1, by omega⟩ := by
      apply Fin.ext; rw [ιF_val hK]; simp
    rw [e, setTies_deg_eta LL T hadm i n]
  | cast a =>
    rw [Formalism.GM.M.FB.snoc_deg_castSucc]
    have ha : (a : ℕ) < N := by have := a.isLt; omega
    have e : ιF N (T.pos i + 1) (Fin.castSucc a) = ⟨a, ha⟩ := by
      apply Fin.ext; rw [ιF_val hK]; simp
    rw [e]
    simp [Letters.takeD, ha]

theorem pol_comap (n : Fin T.t → ℕ) {v' : MvPolynomial (Fin (T.pos i + 1 + 1) × Fin r) ℚ_[p]}
    (hv : rename (fun x : Fin (T.pos i + 1 + 1) × Fin r => (ιF N (T.pos i + 1) x.1, x.2)) v' ∈
      Pol p r (Lz (LL.setTies T n) (T.pos i + 1 + 1))) :
    v' ∈ Pol p r (((LL.setTies T n).takeD (T.pos i + 1)).snoc (n i)) := by
  classical
  have hK := hK_of_adm LL T hadm i
  rw [Pol, mem_restrictSupport_iff]
  intro m' hm' a
  have h1 : Finsupp.mapDomain (fun x : Fin (T.pos i + 1 + 1) × Fin r => (ιF N (T.pos i + 1) x.1, x.2)) m' ∈
      (rename (fun x : Fin (T.pos i + 1 + 1) × Fin r => (ιF N (T.pos i + 1) x.1, x.2)) v').support := by
    rw [support_rename_of_injective (inclusion_prodMap_injective (r := r) hK)]; exact Finset.mem_image_of_mem _ hm'
  have h2 : MultiDeg _ _ := ((mem_restrictSupport_iff ℚ_[p]).mp hv) h1
  have h3 := h2 (ιF N (T.pos i + 1) a)
  have e : ∀ c, Finsupp.mapDomain (fun x : Fin (T.pos i + 1 + 1) × Fin r => (ιF N (T.pos i + 1) x.1, x.2)) m'
      (ιF N (T.pos i + 1) a, c) = m' (a, c) := fun c =>
    Finsupp.mapDomain_apply (inclusion_prodMap_injective (r := r) hK) m' (a, c)
  simp only [e] at h3
  rw [h3, deg_compat LL T hadm i n a]
  have : ((ιF N (T.pos i + 1) a : Fin N) : ℕ) < T.pos i + 1 + 1 := by rw [ιF_val hK]; exact a.isLt
  show (if ((ιF N (T.pos i + 1) a : Fin N) : ℕ) < T.pos i + 1 + 1 then
    (LL.setTies T n).deg (ιF N (T.pos i + 1) a) else 0) = _
  rw [if_pos this]

theorem exists_small (n : Fin T.t → ℕ) {v : MvPolynomial (Fin N × Fin r) ℚ_[p]}
    (hv : v ∈ Pol p r (Lz (LL.setTies T n) (T.pos i + 1 + 1))) :
    ∃ v', rename (fun x : Fin (T.pos i + 1 + 1) × Fin r => (ιF N (T.pos i + 1) x.1, x.2)) v' = v := by
  have hK := hK_of_adm LL T hadm i
  refine exists_rename_eq_of_vars_subset_range v _ (inclusion_prodMap_injective (r := r) hK) ?_
  intro x hx
  obtain ⟨m, hm, hxm⟩ := (mem_vars_iff_mem_support x).mp hx
  have h1 : (x.1 : ℕ) < T.pos i + 1 + 1 := isF_of_polLz _ _ hv m hm x (Finsupp.mem_support_iff.mp hxm)
  refine ⟨(⟨x.1, h1⟩, x.2), ?_⟩
  apply Prod.ext
  · apply Fin.ext; simp [ιF_val hK]
  · rfl

theorem Y_min_eq [NeZero r] (LK : Letters (T.pos i + 1)) :
    Y p (r := r) LK (fun k => min (T.J k) (T.pos i + 1)) (T.thrUpTo i) = Y p LK T.J (T.thrUpTo i) := by
  unfold Y
  congr 1
  refine iInf_congr fun k => ?_
  show YCond p LK (min (T.J k) (T.pos i + 1)) _ = _
  by_cases hk : T.J k ≤ T.pos i + 1
  · rw [min_eq_left hk]
  · have ht : T.thrUpTo i k = ⊤ := by simp [TieData.thrUpTo, hk]
    rw [ht, ycond_top, ycond_top]

theorem tie_onto [NeZero r] (ρ : Fin r) (hρ : (ρ : ℕ) = r - 1) (n : Fin T.t → ℕ)
    (hS : ((LL.setTies T n).takeD (T.pos i + 1)).total ≤ n i) (μ : Fin r → ℤ)
    {v : MvPolynomial (Fin N × Fin r) ℚ_[p]}
    (hv : v ∈ GlX.HWs (GA p (LL.setTies T n) (T.pos i + 1 + 1)) μ ⊓
      Cset p (LL.setTies T n) (T.pos i + 1 + 1) T.J T.thr) :
    ∃ f ∈ MMw p ((LL.setTies T n).takeD (T.pos i + 1)) T.J (T.thrUpTo i) ρ (μ + ((n i : ℕ) : ℤ) • Pi.single ρ 1),
      T.Ffull p (LL.setTies T n) i ρ (n i) f = v := by
  classical
  have hK := hK_of_adm LL T hadm i
  obtain ⟨hvH, hvC⟩ := Submodule.mem_inf.mp hv
  obtain ⟨hvP, hvY⟩ := Submodule.mem_inf.mp hvC
  have hvH' : (GA p LL (T.pos i + 1 + 1)).IsHW μ v := hvH
  obtain ⟨v', rfl⟩ := exists_small LL T hadm i n hvP
  have hinj := inclusion_prodMap_injective (N := N) (r := r) hK
  have hA : ∀ k, v' ∈ YCond p (((LL.setTies T n).takeD (T.pos i + 1)).snoc (n i)) (min (T.J k) (T.pos i + 1))
      (T.thrUpTo i k) := by
    intro k
    by_cases hk : T.J k ≤ T.pos i + 1
    · have h1 := (Submodule.mem_iInf _).mp hvY k
      rw [Mup, if_pos (by omega)] at h1
      have e2 : T.thrUpTo i k = T.thr k := by simp [TieData.thrUpTo, hk]
      rw [min_eq_left hk, e2]
      exact ycond_comap _ LL (ιF N (T.pos i + 1)) (ιF_val hK) (fun a => vec_compat LL T hadm i n (n i) a) hinj
        (T.J k) (T.thr k) (wv_compat LL T hadm i n (n i) (T.J k)) h1
    · have ht : T.thrUpTo i k = ⊤ := by simp [TieData.thrUpTo, hk]
      rw [ht, ycond_top]; exact Submodule.mem_top
  have hB : IsWeightedHomogeneous (wv (((LL.setTies T n).takeD (T.pos i + 1)).snoc (n i)) (T.pos i + 1 + 1)) v' μ := by
    intro m' hm'
    have h1 : IsWeightedHomogeneous (wv LL (T.pos i + 1 + 1))
        (rename (fun x : Fin (T.pos i + 1 + 1) × Fin r => (ιF N (T.pos i + 1) x.1, x.2)) v') μ := by
      have h0 : weightedHomogeneousComponent (wv LL (T.pos i + 1 + 1)) μ _ = _ := hvH'.1
      rw [← h0]; exact weightedHomogeneousComponent_isWeightedHomogeneous _ _
    have h2 : coeff (Finsupp.mapDomain (fun x : Fin (T.pos i + 1 + 1) × Fin r => (ιF N (T.pos i + 1) x.1, x.2)) m')
        (rename (fun x : Fin (T.pos i + 1 + 1) × Fin r => (ιF N (T.pos i + 1) x.1, x.2)) v') ≠ 0 := by
      rw [coeff_rename_mapDomain _ hinj]; exact hm'
    have h3 := h1 h2
    rwa [weight_mapDomain, wv_compat LL T hadm i n (n i)] at h3
  have hC : ∀ a b, a < b → glAct p (((LL.setTies T n).takeD (T.pos i + 1)).snoc (n i)) (T.pos i + 1 + 1) a b v' = 0 := by
    intro a b hab
    apply rename_injective _ hinj
    rw [glAct_rename _ LL (ιF N (T.pos i + 1)) (ιF_val hK) (fun a => vec_compat LL T hadm i n (n i) a), map_zero]
    exact hvH'.2 a b hab
  obtain ⟨f, hf, hfv⟩ := small_onto ((LL.setTies T n).takeD (T.pos i + 1)) ρ hρ (n i) hS
    (fun k => min (T.J k) (T.pos i + 1)) (T.thrUpTo i) (fun k => min_le_right _ _) μ v'
    (pol_comap LL T hadm i n hvP) hA hB hC
  refine ⟨f, ?_, ?_⟩
  · unfold MMw at hf ⊢
    rwa [Y_min_eq LL T hadm i] at hf
  · rw [Ffull_eq, hfv]

theorem tie_into [NeZero r] (ρ : Fin r) (hρ : (ρ : ℕ) = r - 1) (n : Fin T.t → ℕ)
    (hS : ((LL.setTies T n).takeD (T.pos i + 1)).total ≤ n i) (w : Fin r → ℤ)
    {f : MvPolynomial (Fin (T.pos i + 1) × Fin r) ℚ_[p]}
    (hf : f ∈ MMw p ((LL.setTies T n).takeD (T.pos i + 1)) T.J (T.thrUpTo i) ρ w) :
    T.Ffull p (LL.setTies T n) i ρ (n i) f ∈
      GlX.HWs (GA p (LL.setTies T n) (T.pos i + 1 + 1)) (w - ((n i : ℕ) : ℤ) • Pi.single ρ 1) ⊓
      Cset p (LL.setTies T n) (T.pos i + 1 + 1) T.J T.thr := by
  have hP : f ∈ Pol p r ((LL.setTies T n).takeD (T.pos i + 1)) :=
    (Submodule.mem_inf.mp (Submodule.mem_inf.mp (Submodule.mem_inf.mp hf).1).1).1
  refine Submodule.mem_inf.mpr ⟨Ffull_hw LL T hadm i ρ hρ n w f hf hS, Submodule.mem_inf.mpr
    ⟨Ffull_pol LL T hadm i ρ n f hP hS, (Submodule.mem_iInf _).mpr fun k => ?_⟩⟩
  by_cases hk : T.J k < T.pos i + 1 + 1
  · rw [Mup, if_pos hk]
    exact Ffull_ycond LL T hadm i ρ n w f hf hS k (by omega)
  · rw [Mup, if_neg hk, ycond_top]; exact Submodule.mem_top

end Comparison₂

end Formalism.CountingSumsFrames

namespace Formalism.CountingSumsFrames

open MvPolynomial Finset Formalism.GM.DimensionMonotonicity Formalism.GM.M

variable {p : ℕ} [Fact p.Prime] {N r : ℕ}

noncomputable def FrL (p : ℕ) [Fact p.Prime] [NeZero N] (L : Letters N) (T : TieData) (i : Fin T.t) (ρ : Fin r) (n0 : ℕ) :
    MvPolynomial (Fin (T.pos i + 1) × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p] :=
  (rename (fun x : Fin (T.pos i + 1 + 1) × Fin r => (ιF N (T.pos i + 1) x.1, x.2))).toLinearMap ∘ₗ
    (LinearMap.mulLeft ℚ_[p] (X (Fin.last (T.pos i + 1), ρ) ^ (n0 - (L.takeD (T.pos i + 1)).total))) ∘ₗ
    (aeval (freezeSub p (L.takeD (T.pos i + 1)) ρ)).toLinearMap

theorem FrL_apply [NeZero N] (L : Letters N) (T : TieData) (i : Fin T.t) (ρ : Fin r) (n0 : ℕ)
    (f : MvPolynomial (Fin (T.pos i + 1) × Fin r) ℚ_[p]) : FrL p L T i ρ n0 f = T.Ffull p L i ρ n0 f := rfl

section Comparison₂
variable [NeZero N] (LL : Letters N) (T : TieData) (hadm : T.Admissible LL) (i : Fin T.t)

include hadm

theorem finrank_MMw [NeZero r] (ρ : Fin r) (hρ : (ρ : ℕ) = r - 1) (n : Fin T.t → ℕ)
    (hS : ((LL.setTies T n).takeD (T.pos i + 1)).total ≤ n i) (w : Fin r → ℤ) :
    Module.finrank ℚ_[p] (MMw p ((LL.setTies T n).takeD (T.pos i + 1)) T.J (T.thrUpTo i) ρ w) =
      Module.finrank ℚ_[p] (GlX.HWs (GA p (LL.setTies T n) (T.pos i + 1 + 1)) (w - ((n i : ℕ) : ℤ) • Pi.single ρ 1) ⊓
        Cset p (LL.setTies T n) (T.pos i + 1 + 1) T.J T.thr : Submodule ℚ_[p] _) := by
  let Φ : MMw p ((LL.setTies T n).takeD (T.pos i + 1)) T.J (T.thrUpTo i) ρ w →ₗ[ℚ_[p]]
      (GlX.HWs (GA p (LL.setTies T n) (T.pos i + 1 + 1)) (w - ((n i : ℕ) : ℤ) • Pi.single ρ 1) ⊓
        Cset p (LL.setTies T n) (T.pos i + 1 + 1) T.J T.thr : Submodule ℚ_[p] _) :=
    ((FrL p (LL.setTies T n) T i ρ (n i)).comp (Submodule.subtype _)).codRestrict _
      (fun f => tie_into LL T hadm i ρ hρ n hS w f.2)
  have hΦ : ∀ f, ((Φ f : _) : MvPolynomial (Fin N × Fin r) ℚ_[p]) = T.Ffull p (LL.setTies T n) i ρ (n i) f.1 :=
    fun f => rfl
  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro f hf
    by_contra h0
    have h1 := Ffull_ne LL T hadm i ρ n w f.1 f.2 (fun h => h0 (Subtype.ext h)) hS
    apply h1
    rw [← hΦ f, hf]; rfl
  have hsurj : Function.Surjective Φ := by
    intro v
    obtain ⟨f, hf, hfv⟩ := tie_onto LL T hadm i ρ hρ n hS _ v.2
    rw [sub_add_cancel] at hf
    exact ⟨⟨f, hf⟩, Subtype.ext hfv⟩
  exact (LinearEquiv.ofBijective Φ ⟨hinj, hsurj⟩).finrank_eq

end Comparison₂

theorem YYsp_eq [NeZero N] [NeZero r] (LL : Letters N) (T : TieData) (i : Fin T.t) (ρ : Fin r) (n : Fin T.t → ℕ)
    (f : MvPolynomial (Fin (T.pos i + 1) × Fin r) ℚ_[p]) :
    T.YYsp p LL i ρ n f = YYs p (LL.setTies T n) (T.pos i + 1 + 1) T.J T.thr
      (T.Ffull p (LL.setTies T n) i ρ (n i) f) := by
  unfold TieData.YYsp YYs
  rw [gSpan_eq LL T n (T.pos i + 2) (T.Ffull p (LL.setTies T n) i ρ (n i) f)]
  rfl

theorem monomial_count : Formalism.GM.M.MonoCount := by
  intro p _ N r _ _ LL T hadm ρ hρ _ i n hS fw hfw
  classical
  obtain ⟨S, hSw⟩ := polynomial_finite_weights (p := p) (r := r) (LL.setTies T n) (T.pos i + 1 + 1)
  have hmem0 : ∀ μ : Fin r → ℤ, GlX.HWs (GA p (LL.setTies T n) (T.pos i + 1 + 1)) μ ⊓
      Cset p (LL.setTies T n) (T.pos i + 1 + 1) T.J T.thr ≠ ⊥ →
      ∃ v ∈ GlX.HWs (GA p (LL.setTies T n) (T.pos i + 1 + 1)) μ ⊓
        Cset p (LL.setTies T n) (T.pos i + 1 + 1) T.J T.thr, v ≠ 0 := fun μ h =>
    Submodule.exists_mem_ne_zero_of_ne_bot h
  have hcount := count_HW (LL.setTies T n) (T.pos i + 1 + 1) T.J T.thr S hSw
    (fun μ => T.Ffull p (LL.setTies T n) i ρ (n i) (fw (μ + ((n i : ℕ) : ℤ) • Pi.single ρ 1)))
    (fun μ => by
      have := tie_into LL T hadm i ρ hρ n hS _ (hfw (μ + ((n i : ℕ) : ℤ) • Pi.single ρ 1)).1
      rwa [add_sub_cancel_right] at this)
    (fun μ hne => by
      obtain ⟨v, hv, hv0⟩ := hmem0 μ hne
      obtain ⟨f, hf, hfv⟩ := tie_onto LL T hadm i ρ hρ n hS μ hv
      have hf0 : f ≠ 0 := by
        rintro rfl
        apply hv0
        rw [← hfv, ← FrL_apply, map_zero]
      have hb : MMw p ((LL.setTies T n).takeD (T.pos i + 1)) T.J (T.thrUpTo i) ρ
          (μ + ((n i : ℕ) : ℤ) • Pi.single ρ 1) ≠ ⊥ := fun hb => hf0 (by
        rw [hb] at hf; exact (Submodule.mem_bot _).mp hf)
      exact Ffull_ne LL T hadm i ρ n _ _ (hfw _).1 ((hfw _).2 hb) hS)
  rw [hcount]
  obtain ⟨g, hg⟩ : ∃ g : (Fin r → ℤ) → ℕ, g = fun μ =>
      Module.finrank ℚ_[p] (GlX.HWs (GA p (LL.setTies T n) (T.pos i + 1 + 1)) μ ⊓
          Cset p (LL.setTies T n) (T.pos i + 1 + 1) T.J T.thr : Submodule ℚ_[p] _) *
        Module.finrank ℚ_[p] (YYs p (LL.setTies T n) (T.pos i + 1 + 1) T.J T.thr
          (T.Ffull p (LL.setTies T n) i ρ (n i) (fw (μ + ((n i : ℕ) : ℤ) • Pi.single ρ 1)))) := ⟨_, rfl⟩
  have hterm : ∀ w, Module.finrank ℚ_[p] (MMw p ((LL.setTies T n).takeD (T.pos i + 1)) T.J (T.thrUpTo i) ρ w) *
      Module.finrank ℚ_[p] (T.YYsp p LL i ρ n (fw w)) =
      g (Equiv.subRight (((n i : ℕ) : ℤ) • (Pi.single ρ 1 : Fin r → ℤ)) w) := by
    intro w
    have e : Equiv.subRight (((n i : ℕ) : ℤ) • (Pi.single ρ 1 : Fin r → ℤ)) w =
      w - ((n i : ℕ) : ℤ) • (Pi.single ρ 1 : Fin r → ℤ) := rfl
    rw [e, hg]
    show _ = Module.finrank ℚ_[p] (GlX.HWs (GA p (LL.setTies T n) (T.pos i + 1 + 1))
          (w - ((n i : ℕ) : ℤ) • (Pi.single ρ 1 : Fin r → ℤ)) ⊓
          Cset p (LL.setTies T n) (T.pos i + 1 + 1) T.J T.thr : Submodule ℚ_[p] _) *
        Module.finrank ℚ_[p] (YYs p (LL.setTies T n) (T.pos i + 1 + 1) T.J T.thr
          (T.Ffull p (LL.setTies T n) i ρ (n i) (fw (w - ((n i : ℕ) : ℤ) • (Pi.single ρ 1 : Fin r → ℤ) +
            ((n i : ℕ) : ℤ) • Pi.single ρ 1))))
    rw [sub_add_cancel, finrank_MMw LL T hadm i ρ hρ n hS w, YYsp_eq]
  have hsum : ∑ μ ∈ S, Module.finrank ℚ_[p] (GlX.HWs (GA p (LL.setTies T n) (T.pos i + 1 + 1)) μ ⊓
          Cset p (LL.setTies T n) (T.pos i + 1 + 1) T.J T.thr : Submodule ℚ_[p] _) *
        Module.finrank ℚ_[p] (YYs p (LL.setTies T n) (T.pos i + 1 + 1) T.J T.thr
          (T.Ffull p (LL.setTies T n) i ρ (n i) (fw (μ + ((n i : ℕ) : ℤ) • Pi.single ρ 1)))) = ∑ μ ∈ S, g μ := by
    rw [hg]
  rw [hsum]
  simp_rw [hterm]
  rw [finsum_comp_equiv (Equiv.subRight (((n i : ℕ) : ℤ) • (Pi.single ρ 1 : Fin r → ℤ))) (f := g),
    finsum_eq_sum_of_support_subset]
  intro μ hμ
  rw [Function.mem_support, hg] at hμ
  have h1 : GlX.HWs (GA p (LL.setTies T n) (T.pos i + 1 + 1)) μ ⊓
      Cset p (LL.setTies T n) (T.pos i + 1 + 1) T.J T.thr ≠ ⊥ := by
    intro hb
    apply hμ
    beta_reduce
    rw [hb, finrank_bot, zero_mul]
  obtain ⟨v, hv, hv0⟩ := hmem0 μ h1
  by_contra hn
  apply hv0
  have h2 := hSw v hv.2.1 μ hn
  have h3 : (GA p (LL.setTies T n) (T.pos i + 1 + 1)).comp μ v = v := hv.1.1
  rw [← h3, h2]

end Formalism.CountingSumsFrames
