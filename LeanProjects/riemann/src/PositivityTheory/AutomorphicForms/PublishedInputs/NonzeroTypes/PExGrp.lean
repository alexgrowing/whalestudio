import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.CJDefs

noncomputable section

open scoped Classical

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix

namespace UpperTheory.TNZ

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

namespace Grp

namespace P_exGrp

theorem exists_level (μ : kˣ →* ℂˣ) (hμ : IsSmoothChar μ) :
    ∃ c : ℕ, ∀ u : 𝒪[k]ˣ, (u : 𝒪[k]) - 1 ∈ IsLocalRing.maximalIdeal 𝒪[k] ^ c → res μ u = 1 := by
  have hopen : IsOpen (μ.ker : Set kˣ) := hμ
  obtain ⟨V, hVo, hV⟩ := (Units.isEmbedding_val₀ (G₀ := k)).isInducing.isOpen_iff.mp hopen
  have h1 : (1 : k) ∈ V := by
    have : (1 : kˣ) ∈ (Units.val ⁻¹' V) := by rw [hV]; exact μ.ker.one_mem
    simpa using this
  obtain ⟨γ, hγ⟩ := (IsValuativeTopology.mem_nhds_iff' (R := k)).mp (hVo.mem_nhds h1)
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[k]
  have hlt : valuation k (algebraMap 𝒪[k] k ϖ) < 1 :=
    (Valuation.integer.integers (valuation k)).valuation_irreducible_lt_one hϖ
  have : MulArchimedean (ValueGroupWithZero k) :=
    ValuativeRel.isRankLeOne_iff_mulArchimedean.mp inferInstance
  obtain ⟨c, hc⟩ := exists_pow_lt₀ hlt γ
  refine ⟨c, fun u hu => ?_⟩
  have hm : IsLocalRing.maximalIdeal 𝒪[k] = Ideal.span {ϖ} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ
  rw [hm, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hu
  obtain ⟨t, ht⟩ := hu
  have e : ((u : 𝒪[k]) : k) - 1 = (algebraMap 𝒪[k] k ϖ) ^ c * algebraMap 𝒪[k] k t := by
    have := congrArg (algebraMap 𝒪[k] k) ht
    rw [map_sub, map_one, map_mul, map_pow] at this
    exact this
  have ht1 : valuation k (algebraMap 𝒪[k] k t) ≤ 1 := t.2
  have hv : valuation k (((u : 𝒪[k]) : k) - 1) < γ := by
    rw [e, map_mul, map_pow]
    calc valuation k (algebraMap 𝒪[k] k ϖ) ^ c * valuation k (algebraMap 𝒪[k] k t)
        ≤ valuation k (algebraMap 𝒪[k] k ϖ) ^ c := mul_le_of_le_one_right' ht1
      _ < γ := hc
  have hmem : ((u : 𝒪[k]) : k) ∈ V := hγ hv
  have hk : unitIncl k u ∈ μ.ker := by
    have : unitIncl k u ∈ (Units.val ⁻¹' V : Set kˣ) := hmem
    rw [hV] at this
    exact this
  exact hk

def Good {α : Type} (d : α → α → ℕ) (l : List α) : Prop :=
  ∀ (a a' b' b : ℕ) (h1 : a ≤ a') (h2 : a' < b') (h3 : b' ≤ b) (hb : b < l.length),
    d (l[a']'(by omega)) (l[b']'(by omega)) ≤ d (l[a]'(by omega)) (l[b])

theorem exists_idempotent_mul_natPow_of_mul {α : Type} (d : α → α → ℕ) (S : Finset α) :
    (∀ x ∈ S, d x x = 0) → (∀ x ∈ S, ∀ y ∈ S, d x y = d y x) →
    (∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S, d x z ≤ max (d x y) (d y z)) →
    ∃ l : List α, l.Nodup ∧ (∀ x, x ∈ l ↔ x ∈ S) ∧ Good d l := by
  induction S using Finset.strongInduction with
  | H S ih =>
  intro h0 hs hu
  set r : ℕ := (S ×ˢ S).sup (fun p => d p.1 p.2) with hr
  have hle : ∀ x ∈ S, ∀ y ∈ S, d x y ≤ r := fun x hx y hy =>
    Finset.le_sup (f := fun p : α × α => d p.1 p.2) (b := (x, y)) (Finset.mem_product.mpr ⟨hx, hy⟩)
  by_cases hr0 : r = 0
  · refine ⟨S.toList, Finset.nodup_toList S, fun x => Finset.mem_toList, ?_⟩
    intro a a' b' b h1 h2 h3 hb
    have := hle (S.toList[a']'(by omega)) (Finset.mem_toList.mp (List.getElem_mem _))
      (S.toList[b']'(by omega)) (Finset.mem_toList.mp (List.getElem_mem _))
    omega
  · have hSne : S.Nonempty := by
      by_contra hne
      rw [Finset.not_nonempty_iff_eq_empty] at hne
      apply hr0
      rw [hr, hne]
      simp
    obtain ⟨x, hx⟩ := hSne
    obtain ⟨p, hp, hpr⟩ := Finset.exists_mem_eq_sup (S ×ˢ S) ⟨(x, x), Finset.mem_product.mpr ⟨hx, hx⟩⟩
      (fun p : α × α => d p.1 p.2)
    rw [← hr] at hpr
    obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
    set A := S.filter (fun y => d x y < r) with hA
    set B := S.filter (fun y => ¬ d x y < r) with hB
    have hAS : A ⊂ S := by
      rw [hA, Finset.filter_ssubset]
      by_contra hall
      push Not at hall
      have h1 := hu p.1 hp1 x hx p.2 hp2
      rw [hs p.1 hp1 x hx] at h1
      have h2 := hall p.1 hp1
      have h3 := hall p.2 hp2
      have : max (d x p.1) (d x p.2) < r := max_lt h2 h3
      omega
    have hBS : B ⊂ S := by
      rw [hB, Finset.filter_ssubset]
      refine ⟨x, hx, ?_⟩
      rw [h0 x hx]
      push Not
      omega
    have memA : ∀ y, y ∈ A ↔ y ∈ S ∧ d x y < r := fun y => Finset.mem_filter
    have memB : ∀ y, y ∈ B ↔ y ∈ S ∧ ¬ d x y < r := fun y => Finset.mem_filter
    obtain ⟨lA, nA, mA, gA⟩ := ih A hAS (fun y hy => h0 y ((memA y).mp hy).1)
      (fun y hy z hz => hs y ((memA y).mp hy).1 z ((memA z).mp hz).1)
      (fun y hy z hz w hw => hu y ((memA y).mp hy).1 z ((memA z).mp hz).1 w ((memA w).mp hw).1)
    obtain ⟨lB, nB, mB, gB⟩ := ih B hBS (fun y hy => h0 y ((memB y).mp hy).1)
      (fun y hy z hz => hs y ((memB y).mp hy).1 z ((memB z).mp hz).1)
      (fun y hy z hz w hw => hu y ((memB y).mp hy).1 z ((memB z).mp hz).1 w ((memB w).mp hw).1)
    have hmem : ∀ y, y ∈ lA ++ lB ↔ y ∈ S := by
      intro y
      rw [List.mem_append, mA, mB, memA, memB]
      tauto
    refine ⟨lA ++ lB, ?_, hmem, ?_⟩
    · rw [List.nodup_append]
      refine ⟨nA, nB, ?_⟩
      intro y hy z hz hyz
      subst hyz
      exact ((memB y).mp ((mB y).mp hz)).2 ((memA y).mp ((mA y).mp hy)).2
    · intro a a' b' b h1 h2 h3 hb
      have hlen : (lA ++ lB).length = lA.length + lB.length := List.length_append
      have eL : ∀ i (hi : i < lA.length) (h : i < (lA ++ lB).length), (lA ++ lB)[i] = lA[i] :=
        fun i hi h => List.getElem_append_left hi
      have eR : ∀ i (hi : lA.length ≤ i) (h : i < (lA ++ lB).length),
          (lA ++ lB)[i] = lB[i - lA.length]'(by omega) :=
        fun i hi h => List.getElem_append_right hi
      have inS : ∀ i (h : i < (lA ++ lB).length), (lA ++ lB)[i] ∈ S :=
        fun i h => (hmem _).mp (List.getElem_mem _)
      by_cases hbA : b < lA.length
      · rw [eL a (by omega), eL a' (by omega), eL b' (by omega), eL b hbA]
        exact gA a a' b' b h1 h2 h3 hbA
      · by_cases haA : lA.length ≤ a
        · rw [eR a haA, eR a' (by omega), eR b' (by omega), eR b (by omega)]
          exact gB (a - lA.length) (a' - lA.length) (b' - lA.length) (b - lA.length) (by omega) (by omega)
            (by omega) (by omega)
        · push Not at hbA haA
          have hxa : d x (lA ++ lB)[a] < r := by
            rw [eL a haA]
            exact ((memA _).mp ((mA _).mp (List.getElem_mem _))).2
          have hxb : ¬ d x (lA ++ lB)[b] < r := by
            rw [eR b hbA]
            exact ((memB _).mp ((mB _).mp (List.getElem_mem _))).2
          have hab : r ≤ d (lA ++ lB)[a] (lA ++ lB)[b] := by
            by_contra hlt
            push Not at hlt
            have := hu x hx _ (inS a (by omega)) _ (inS b hb)
            have : max (d x (lA ++ lB)[a]) (d (lA ++ lB)[a] (lA ++ lB)[b]) < r := max_lt hxa hlt
            omega
          exact le_trans (hle _ (inS a' (by omega)) _ (inS b' (by omega))) hab

theorem exists_good_list {α : Type} (S : Finset α) (d : α → α → ℕ)
    (h0 : ∀ x ∈ S, d x x = 0) (hs : ∀ x ∈ S, ∀ y ∈ S, d x y = d y x)
    (hu : ∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S, d x z ≤ max (d x y) (d y z)) :
    ∃ l : List α, l.Nodup ∧ (∀ x, x ∈ l ↔ x ∈ S) ∧
      ∀ (a a' b' b : ℕ) (h1 : a ≤ a') (h2 : a' < b') (h3 : b' ≤ b) (hb : b < l.length),
        d (l[a']'(by omega)) (l[b']'(by omega)) ≤ d (l[a]'(by omega)) (l[b]) :=
  exists_idempotent_mul_natPow_of_mul d S h0 hs hu

def Lv (ψ : 𝒪[k]ˣ →* ℂˣ) : Set ℕ :=
  {c | ∀ u : 𝒪[k]ˣ, (u : 𝒪[k]) - 1 ∈ IsLocalRing.maximalIdeal 𝒪[k] ^ c → ψ u = 1}

theorem Lv_mono (ψ : 𝒪[k]ˣ →* ℂˣ) {c c' : ℕ} (h : c ≤ c') (hc : c ∈ Lv ψ) : c' ∈ Lv ψ :=
  fun u hu => hc u (Ideal.pow_le_pow_right h hu)

theorem cond_div_self (ψ : 𝒪[k]ˣ →* ℂˣ) : cond (ψ / ψ) = 0 := by
  apply Nat.sInf_eq_zero.mpr
  left
  intro u _
  simp

theorem cond_div_comm (ψ φ : 𝒪[k]ˣ →* ℂˣ) : cond (ψ / φ) = cond (φ / ψ) := by
  unfold cond
  congr 1
  ext c
  simp only [Set.mem_ofPred_eq, MonoidHom.div_apply, div_eq_one]
  exact forall_congr' fun u => imp_congr_right fun _ => eq_comm

theorem cond_div_ultra (ψ φ ξ : 𝒪[k]ˣ →* ℂˣ) (h1 : (Lv ψ).Nonempty) (h2 : (Lv φ).Nonempty) (h3 : (Lv ξ).Nonempty) :
    cond (ψ / ξ) ≤ max (cond (ψ / φ)) (cond (φ / ξ)) := by
  obtain ⟨c1, hc1⟩ := h1
  obtain ⟨c2, hc2⟩ := h2
  obtain ⟨c3, hc3⟩ := h3
  have hA : cond (ψ / φ) ∈ Lv (ψ / φ) := Nat.sInf_mem ⟨max c1 c2, fun u hu => by
    rw [MonoidHom.div_apply, Lv_mono ψ (le_max_left _ _) hc1 u hu, Lv_mono φ (le_max_right _ _) hc2 u hu, div_one]⟩
  have hB : cond (φ / ξ) ∈ Lv (φ / ξ) := Nat.sInf_mem ⟨max c2 c3, fun u hu => by
    rw [MonoidHom.div_apply, Lv_mono φ (le_max_left _ _) hc2 u hu, Lv_mono ξ (le_max_right _ _) hc3 u hu, div_one]⟩
  apply Nat.sInf_le
  intro u hu
  have e1 := Lv_mono _ (le_max_left _ _) hA u hu
  have e2 := Lv_mono _ (le_max_right _ _) hB u hu
  rw [MonoidHom.div_apply, div_eq_one] at e1 e2 ⊢
  rw [e1, e2]

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem res_div (μ ν : kˣ →* ℂˣ) : res (μ / ν) = res μ / res ν := by
  ext u
  simp [res, MonoidHom.div_apply]

end P_exGrp

open P_exGrp in

theorem step_exGrp : ExistsGroupElementProp (k := k) := by
  intro n χ hχ
  let S : Finset (𝒪[k]ˣ →* ℂˣ) := Finset.univ.image (fun i => res (χ i))
  have hLv : ∀ ψ ∈ S, (Lv ψ).Nonempty := by
    intro ψ hψ
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hψ
    exact exists_level (χ i) (hχ i)
  obtain ⟨l, hnd, hmem, hgood⟩ := exists_good_list S (fun ψ φ => cond (ψ / φ))
    (fun x _ => cond_div_self x) (fun x _ y _ => cond_div_comm x y)
    (fun x hx y hy z hz => cond_div_ultra x y z (hLv x hx) (hLv y hy) (hLv z hz))
  have hinS : ∀ i, res (χ i) ∈ l := fun i => (hmem _).mpr (Finset.mem_image_of_mem _ (Finset.mem_univ i))
  have hex : ∀ i, ∃ a : Fin l.length, l[(a : ℕ)] = res (χ i) := by
    intro i
    obtain ⟨a, ha, h⟩ := List.mem_iff_getElem.mp (hinS i)
    exact ⟨⟨a, ha⟩, h⟩
  let f : Fin n → Fin l.length := fun i => Classical.choose (hex i)
  have hf : ∀ i, l[((f i : Fin l.length) : ℕ)] = res (χ i) := fun i => Classical.choose_spec (hex i)
  have hrep : ∀ a : Fin l.length, ∃ i, res (χ i) = l[(a : ℕ)] := by
    intro a
    have : l[(a : ℕ)] ∈ S := (hmem _).mp (List.getElem_mem _)
    obtain ⟨i, -, h⟩ := Finset.mem_image.mp this
    exact ⟨i, h⟩
  let rep : Fin l.length → Fin n := fun a => Classical.choose (hrep a)
  have hrep' : ∀ a, res (χ (rep a)) = l[(a : ℕ)] := fun a => Classical.choose_spec (hrep a)
  have hfrep : ∀ a, f (rep a) = a := by
    intro a
    apply Fin.ext
    exact (hnd.getElem_inj_iff).mp ((hf (rep a)).trans (hrep' a))
  let G : Grp k n :=
    { s := l.length
      d := fun a => Fintype.card {i // f i = a}
      pos := fun a => Fintype.card_pos_iff.mpr ⟨⟨rep a, hfrep a⟩⟩
      hd := by
        rw [← Fintype.card_sigma, Fintype.card_congr (Equiv.sigmaFiberEquiv f), Fintype.card_fin]
      μ := fun a => χ (rep a)
      smooth := fun a => hχ (rep a)
      dist := by
        intro a b hab h
        apply hab
        apply Fin.ext
        rw [hrep', hrep'] at h
        exact (hnd.getElem_inj_iff).mp h
      ball := by
        intro a a' b' b h1 h2 h3
        unfold cc
        rw [res_div, res_div, hrep', hrep', hrep', hrep']
        exact hgood a a' b' b h1 h2 h3 b.isLt }
  let τ : (Σ a : Fin G.s, Fin (G.d a)) ≃ Fin n :=
    (Equiv.sigmaCongrRight (fun a => (Fintype.equivFin {i // f i = a}).symm)).trans (Equiv.sigmaFiberEquiv f)
  refine ⟨G, G.e.symm.trans τ, fun i => ?_⟩
  have key : f ((G.e.symm.trans τ) i) = G.bl i := ((Fintype.equivFin {j // f j = (G.e.symm i).1}).symm (G.e.symm i).2).2
  calc res (χ ((G.e.symm.trans τ) i)) = l[((f ((G.e.symm.trans τ) i) : Fin l.length) : ℕ)] := (hf _).symm
    _ = l[((G.bl i : Fin l.length) : ℕ)] := by simp only [key]
    _ = res (G.chi i) := (hrep' (G.bl i)).symm

end Grp

end UpperTheory.TNZ
