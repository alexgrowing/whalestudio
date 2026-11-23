import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.MatchT
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalAlgebraHolds
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryLevelSubgroupProperties
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCompactSupportDcos

noncomputable section

open NumberField IsDedekindDomain Polynomial
open GlobalTheory.BCT GlobalTheory.UnitaryBC PositivityTheory.Rg.Bc.ArchbcB.B PositivityTheory.Rg.BcB.F.MT
open PositivityTheory.Rg.BcB.F.Eig (lconv)
open PositivityTheory.Rg.BcB.F.U (lpow lone)
open PositivityTheory.Rg.BcN.F2 (mconv)
open Formalism.UG (qV)
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.MatchPow

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]

theorem isHecke_continuous {L : Subgroup G} (ho : IsOpen (L : Set G)) {f : G → ℂ} (h : IsHecke L f) : Continuous f := by
  refine IsLocallyConstant.continuous ((IsLocallyConstant.iff_eventually_eq f).2 fun x => ?_)
  have hop : IsOpen {y : G | x⁻¹ * y ∈ L} := ho.preimage (continuous_const.mul continuous_id)
  filter_upwards [hop.mem_nhds (by simp [L.one_mem] : x ∈ {y : G | x⁻¹ * y ∈ L})] with y hy
  have := (h.2 _ hy x).2
  rwa [mul_inv_cancel_left] at this

theorem isHecke_zero (L : Subgroup G) : IsHecke L (fun _ : G => (0 : ℂ)) :=
  ⟨HasCompactSupport.zero, fun _ _ _ => ⟨rfl, rfl⟩⟩

theorem isHecke_const_mul {L : Subgroup G} {f : G → ℂ} (z : ℂ) (h : IsHecke L f) : IsHecke L (fun y => z * f y) :=
  GlobalTheory.CompanionTheory.LocHecke.isHecke_smul z h

theorem isHecke_sum {L : Subgroup G} {I : Type} [Fintype I] {f : I → G → ℂ} (h : ∀ i, IsHecke L (f i)) :
    IsHecke L (fun y => ∑ i, f i y) := by
  refine ⟨?_, fun k hk x => ⟨?_, ?_⟩⟩
  · have key : ∀ s : Finset I, HasCompactSupport (fun y => ∑ i ∈ s, f i y) := by
      intro s
      induction s using Finset.induction_on with
      | empty =>
        simp only [Finset.sum_empty]
        exact HasCompactSupport.zero
      | insert a s ha ih =>
        simp only [Finset.sum_insert ha]
        exact (h a).1.add ih
    exact key Finset.univ
  · exact Finset.sum_congr rfl fun i _ => ((h i).2 k hk x).1
  · exact Finset.sum_congr rfl fun i _ => ((h i).2 k hk x).2

theorem conv_const {K L : Subgroup G} (ho : IsOpen (L : Set G)) (hle : L ≤ K) (hidx : L.relIndex K ≠ 0)
    {f g : G → ℂ} (hf : IsHecke L f) (hg : IsHecke L g) (r : ℂ) (y : G) :
    hint K (fun z => f z * (r * g (z⁻¹ * y))) = r * hint K (fun z => f z * g (z⁻¹ * y)) := by
  have h1 := GlobalTheory.CompanionTheory.LocHecke.conv_formula ho hle hidx hf (isHecke_const_mul r hg) y
  have h2 := GlobalTheory.CompanionTheory.LocHecke.conv_formula ho hle hidx hf hg y
  have e : ∑ᶠ q : G ⧸ L, f q.out * (r * g (q.out⁻¹ * y)) = r * ∑ᶠ q : G ⧸ L, f q.out * g (q.out⁻¹ * y) := by
    rw [mul_finsum]
    exact finsum_congr fun q => by ring
  rw [h1, h2, e, mul_left_comm]

theorem conv_sum_sum {K L : Subgroup G} (ho : IsOpen (L : Set G)) (hle : L ≤ K) (hidx : L.relIndex K ≠ 0)
    {I J : Type} [Fintype I] [Fintype J] (a : I → ℂ) (f : I → G → ℂ) (b : J → ℂ) (g : J → G → ℂ)
    (hf : ∀ i, IsHecke L (f i)) (hg : ∀ j, IsHecke L (g j)) (y : G) :
    hint K (fun z => (∑ i, a i * f i z) * (∑ j, b j * g j (z⁻¹ * y))) =
      ∑ i, ∑ j, a i * b j * hint K (fun z => f i z * g j (z⁻¹ * y)) := by
  have hF : IsHecke L (fun z => ∑ i, a i * f i z) := isHecke_sum fun i => isHecke_const_mul _ (hf i)
  have hG : IsHecke L (fun z => ∑ j, b j * g j z) := isHecke_sum fun j => isHecke_const_mul _ (hg j)
  have h1 := GlobalTheory.CompanionTheory.LocHecke.conv_formula ho hle hidx hF hG y
  have hfin : ∀ i j, (Function.support fun q : G ⧸ L => f i q.out * g j (q.out⁻¹ * y)).Finite := fun i j =>
    (GlobalTheory.TwTrLin.finite_out_support ho (hf i).1).subset fun q hq => left_ne_zero_of_mul hq
  rw [h1]
  have e : ∀ q : G ⧸ L, (∑ i, a i * f i q.out) * (∑ j, b j * g j (q.out⁻¹ * y)) =
      ∑ i, ∑ j, a i * b j * (f i q.out * g j (q.out⁻¹ * y)) := by
    intro q
    rw [Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  simp_rw [e]
  rw [finsum_sum_comm _ _ fun i _ => ?_, Finset.mul_sum]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [finsum_sum_comm _ _ fun j _ => ?_, Finset.mul_sum]
    · refine Finset.sum_congr rfl fun j _ => ?_
      rw [GlobalTheory.CompanionTheory.LocHecke.conv_formula ho hle hidx (hf i) (hg j) y, ← mul_finsum]
      ring
    · exact (hfin i j).subset fun q hq h0 => hq (by simp [h0])
  · refine Set.Finite.subset (Set.Finite.biUnion (Finset.univ : Finset J).finite_toSet fun j _ => hfin i j) ?_
    intro q hq
    obtain ⟨j, -, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero hq
    have : f i q.out * g j (q.out⁻¹ * y) ≠ 0 := fun h0 => hj (by simp [h0])
    exact Set.mem_biUnion (Finset.mem_coe.2 (Finset.mem_univ j)) this

theorem conv_unit {K L : Subgroup G} (hle : L ≤ K) (hidx : L.relIndex K ≠ 0) {f : G → ℂ}
    (hr : ∀ k ∈ L, ∀ x, f (x * k) = f x) (y : G) :
    hint K (fun z => f z * (L : Set G).indicator (fun _ => ((L.relIndex K : ℕ) : ℂ)) (z⁻¹ * y)) = f y := by
  have hmem : ∀ q : G ⧸ L, q ≠ QuotientGroup.mk y → q.out⁻¹ * y ∉ L := by
    intro q hq hm
    apply hq
    rw [← QuotientGroup.out_eq' q]
    exact QuotientGroup.eq.2 hm
  have hc : ((L.relIndex K : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hidx
  rw [GlobalTheory.CompanionTheory.LocHecke.hint_eq K L hle hidx _ ?_ ?_]
  · rw [finsum_eq_single _ (QuotientGroup.mk y : G ⧸ L) ?_]
    · obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul L y
      have h2 : (QuotientGroup.mk y : G ⧸ L).out⁻¹ * y ∈ L := by
        have e : (y * (h : G))⁻¹ * y = (h : G)⁻¹ := by group
        rw [hh, e]
        exact L.inv_mem h.2
      rw [Set.indicator_of_mem (by exact h2), hh, hr _ h.2]
      field_simp
    · intro q hq
      rw [Set.indicator_of_notMem (hmem q hq), mul_zero]
  · intro k hk x
    rw [hr k hk x]
    congr 1
    have : (x * k)⁻¹ * y = k⁻¹ * (x⁻¹ * y) := by group
    rw [this]
    have hiff : k⁻¹ * (x⁻¹ * y) ∈ L ↔ x⁻¹ * y ∈ L := L.mul_mem_cancel_left (L.inv_mem hk)
    simp only [Set.indicator, SetLike.mem_coe, hiff]
  · refine (Set.finite_singleton (QuotientGroup.mk y : G ⧸ L)).subset fun q hq => ?_
    by_contra hne
    apply hq
    rw [Set.indicator_of_notMem (hmem q hne), mul_zero]

end Generic

theorem cone_anti {m : ℕ} {l : Fin m → ℤ} (h : Cone l) : Antitone l := by
  have key : ∀ d : ℕ, ∀ i j : Fin m, (j : ℕ) = i + d → l j ≤ l i := by
    intro d
    induction d with
    | zero =>
      intro i j e
      exact le_of_eq (congrArg l (Fin.ext e))
    | succ d ih =>
      intro i j e
      have hlt : (i : ℕ) + d < m := by have := j.2; omega
      have h1 := ih i ⟨i + d, hlt⟩ rfl
      have h2 := h.1 ⟨i + d, hlt⟩ j (by simp only []; omega)
      linarith
  intro i j hij
  exact key (j - i) i j (by have : (i : ℕ) ≤ j := hij; omega)

theorem cone_add {m : ℕ} {l l' : Fin m → ℤ} (h : Cone l) (h' : Cone l') : Cone (l + l') := by
  refine ⟨fun i j e => ?_, fun i => ?_⟩
  · have := h.1 i j e
    have := h'.1 i j e
    simp only [Pi.add_apply]
    linarith
  · have := h.2 i
    have := h'.2 i
    simp only [Pi.add_apply]
    linarith

theorem lOf_add {n : ℕ} (x x' : Fin n → ℤ) : lOf (x + x') = lOf x + lOf x' := by
  funext i
  simp only [lOf, Pi.add_apply]
  ring

theorem vRes_add {n : ℕ} (a : ℕ) {l l' : Fin (n / 2) → ℤ} (h : Cone l) (h' : Cone l') (s : Finset (Fin (n / 2))) :
    vRes n a (l + l') s = vRes n a l s + vRes n a l' s := by
  have hm : ∀ i j : Fin (n / 2), max (l i + l' i) (l j + l' j) = max (l i) (l j) + max (l' i) (l' j) := by
    intro i j
    rcases le_total i j with hij | hij
    · have h1 := cone_anti h hij
      have h2 := cone_anti h' hij
      rw [max_eq_left h1, max_eq_left h2, max_eq_left (add_le_add h1 h2)]
    · have h1 := cone_anti h hij
      have h2 := cone_anti h' hij
      rw [max_eq_right h1, max_eq_right h2, max_eq_right (add_le_add h1 h2)]
  unfold vRes
  simp only [Pi.add_apply, hm, Finset.sum_add_distrib]
  split_ifs <;> ring

theorem restr_anti {n m : ℕ} {x : Fin n → ℤ} (hx : StrictAnti x) (S : Finset (Fin n)) (h : S.card = m) :
    Antitone (restr x S h) := fun _ _ hij => hx.antitone ((S.orderEmbOfFin h).monotone hij)

theorem relIndex_prod {A B : Type} [Group A] [Group B] (H K : Subgroup A) (H' K' : Subgroup B) :
    (H.prod H').relIndex (K.prod K') = H.relIndex K * H'.relIndex K' := by
  unfold Subgroup.relIndex
  rw [← Subgroup.index_prod,
    ← Subgroup.index_comap_of_surjective ((H.subgroupOf K).prod (H'.subgroupOf K'))
      (f := (Subgroup.prodEquiv K K').toMonoidHom) (Subgroup.prodEquiv K K').surjective]
  congr 1

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem fU_left {w : Pl E} {n : ℕ} (b : GLw n w) (ϖ : (w.adicCompletion E)ˣ) (l : Fin (n / 2) → ℤ) {k : UL n w}
    (hk : k ∈ iwU n w b) (γ : UL n w) : fU n w b ϖ l (k * γ) = fU n w b ϖ l γ := by
  have : (∃ x ∈ iwU n w b, ∃ z ∈ iwU n w b, (k * γ).1 = x.1 * (b * tdiag ϖ (wexp n l) * b⁻¹) * z.1) ↔
      (∃ x ∈ iwU n w b, ∃ z ∈ iwU n w b, γ.1 = x.1 * (b * tdiag ϖ (wexp n l) * b⁻¹) * z.1) := by
    constructor
    · rintro ⟨x, hx, z, hz, e⟩
      refine ⟨k⁻¹ * x, mul_mem (inv_mem hk) hx, z, hz, ?_⟩
      have e' : k.1 * γ.1 = x.1 * (b * tdiag ϖ (wexp n l) * b⁻¹) * z.1 := e
      show γ.1 = k.1⁻¹ * x.1 * (b * tdiag ϖ (wexp n l) * b⁻¹) * z.1
      calc γ.1 = k.1⁻¹ * (k.1 * γ.1) := by group
        _ = _ := by rw [e']; simp only [mul_assoc]
    · rintro ⟨x, hx, z, hz, e⟩
      refine ⟨k * x, mul_mem hk hx, z, hz, ?_⟩
      show k.1 * γ.1 = k.1 * x.1 * (b * tdiag ϖ (wexp n l) * b⁻¹) * z.1
      rw [e]
      simp only [mul_assoc]
  simp only [fU, this]

theorem fU_right {w : Pl E} {n : ℕ} (b : GLw n w) (ϖ : (w.adicCompletion E)ˣ) (l : Fin (n / 2) → ℤ) {k : UL n w}
    (hk : k ∈ iwU n w b) (γ : UL n w) : fU n w b ϖ l (γ * k) = fU n w b ϖ l γ := by
  have : (∃ x ∈ iwU n w b, ∃ z ∈ iwU n w b, (γ * k).1 = x.1 * (b * tdiag ϖ (wexp n l) * b⁻¹) * z.1) ↔
      (∃ x ∈ iwU n w b, ∃ z ∈ iwU n w b, γ.1 = x.1 * (b * tdiag ϖ (wexp n l) * b⁻¹) * z.1) := by
    constructor
    · rintro ⟨x, hx, z, hz, e⟩
      refine ⟨x, hx, z * k⁻¹, mul_mem hz (inv_mem hk), ?_⟩
      have e' : γ.1 * k.1 = x.1 * (b * tdiag ϖ (wexp n l) * b⁻¹) * z.1 := e
      show γ.1 = x.1 * (b * tdiag ϖ (wexp n l) * b⁻¹) * (z.1 * k.1⁻¹)
      calc γ.1 = (γ.1 * k.1) * k.1⁻¹ := by group
        _ = _ := by rw [e']; simp only [mul_assoc]
    · rintro ⟨x, hx, z, hz, e⟩
      refine ⟨x, hx, z * k, mul_mem hz hk, ?_⟩
      show γ.1 * k.1 = x.1 * (b * tdiag ϖ (wexp n l) * b⁻¹) * (z.1 * k.1)
      rw [e]
      simp only [mul_assoc]
  simp only [fU, this]

theorem fU_hecke {w : Pl E} (hw : ¬ IsSplitAt w) {n : ℕ} (b : GLw n w) (ϖ : (w.adicCompletion E)ˣ)
    (l : Fin (n / 2) → ℤ) (hc : Continuous (cj w)) : IsHecke (iwU n w b) (fU n w b ϖ l) :=
  ⟨(GlobalTheory.CompanionTheory.IwLevels.isCompact_support_fU hw n b ϖ l hc).closure,
    fun _ hk x => ⟨fU_left b ϖ l hk x, fU_right b ϖ l hk x⟩⟩

theorem dcos_left' {n : ℕ} {w : Pl E} (t : GLw n w) {i : GLw n w} (hi : i ∈ iwGL n w) (g : GLw n w) :
    dcos n w t (i * g) = dcos n w t g := by
  have : (∃ x ∈ iwGL n w, ∃ z ∈ iwGL n w, i * g = x * t * z) ↔ (∃ x ∈ iwGL n w, ∃ z ∈ iwGL n w, g = x * t * z) := by
    constructor
    · rintro ⟨x, hx, z, hz, e⟩
      refine ⟨i⁻¹ * x, mul_mem (inv_mem hi) hx, z, hz, ?_⟩
      calc g = i⁻¹ * (i * g) := by group
        _ = _ := by rw [e]; simp only [mul_assoc]
    · rintro ⟨x, hx, z, hz, e⟩
      exact ⟨i * x, mul_mem hi hx, z, hz, by rw [e]; simp only [mul_assoc]⟩
  simp only [dcos, this]

theorem dcos_right' {n : ℕ} {w : Pl E} (t : GLw n w) {i : GLw n w} (hi : i ∈ iwGL n w) (g : GLw n w) :
    dcos n w t (g * i) = dcos n w t g := by
  have : (∃ x ∈ iwGL n w, ∃ z ∈ iwGL n w, g * i = x * t * z) ↔ (∃ x ∈ iwGL n w, ∃ z ∈ iwGL n w, g = x * t * z) := by
    constructor
    · rintro ⟨x, hx, z, hz, e⟩
      refine ⟨x, hx, z * i⁻¹, mul_mem hz (inv_mem hi), ?_⟩
      calc g = (g * i) * i⁻¹ := by group
        _ = _ := by rw [e]; simp only [mul_assoc]
    · rintro ⟨x, hx, z, hz, e⟩
      exact ⟨x, hx, z * i, mul_mem hz hi, by rw [e]; simp only [mul_assoc]⟩
  simp only [dcos, this]

def dd (a b : ℕ) (w : Pl E) (t₁ : GLw a w) (t₂ : GLw b w) : GLw a w × GLw b w → ℂ :=
  fun m => dcos a w t₁ m.1 * dcos b w t₂ m.2

theorem dd_hecke (a b : ℕ) (w : Pl E) (t₁ : GLw a w) (t₂ : GLw b w) :
    IsHecke ((iwGL a w).prod (iwGL b w)) (dd a b w t₁ t₂) := by
  have h1 := GlobalTheory.CompanionTheory.IwFacts.isCompact_support_dcos w a t₁
  have h2 := GlobalTheory.CompanionTheory.IwFacts.isCompact_support_dcos w b t₂
  refine ⟨HasCompactSupport.intro' (h1.prod h2) (h1.prod h2).isClosed fun y hy => ?_, fun k hk x => ⟨?_, ?_⟩⟩
  · by_contra hne
    exact hy ⟨left_ne_zero_of_mul hne, right_ne_zero_of_mul hne⟩
  · simp only [dd, Prod.fst_mul, Prod.snd_mul, dcos_left' _ hk.1, dcos_left' _ hk.2]
  · simp only [dd, Prod.fst_mul, Prod.snd_mul, dcos_right' _ hk.1, dcos_right' _ hk.2]

theorem iwahori_pair_open (a b : ℕ) (w : Pl E) : IsOpen (((iwGL a w).prod (iwGL b w) : Subgroup _) : Set (GLw a w × GLw b w)) := by
  rw [Subgroup.coe_prod]
  exact (GlobalTheory.SmGL.IwahoriOnto.isOpen_iwahori (w.adicCompletion E) (Fin a)).prod
    (GlobalTheory.SmGL.IwahoriOnto.isOpen_iwahori (w.adicCompletion E) (Fin b))

theorem iwahori_pair_le_maximal (a b : ℕ) (w : Pl E) :
    (iwGL a w).prod (iwGL b w) ≤ (GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w b) :=
  Subgroup.prod_mono (GlobalTheory.CompanionTheory.IwLevels.iwGL_le_KGL w a) (GlobalTheory.CompanionTheory.IwLevels.iwGL_le_KGL w b)

theorem iw_idx (a : ℕ) (w : Pl E) : (iwGL a w).relIndex (GlobalTheory.LFun.KGL w a) ≠ 0 :=
  GlobalTheory.CompanionTheory.IwLevels.relIndex_ne_zero (GlobalTheory.SmGL.IwahoriOnto.isOpen_iwahori (w.adicCompletion E) (Fin a))
    (GlobalTheory.CompanionTheory.IwLevels.isCompact_KGL w a)

theorem iwahori_pair_index_ne_zero (a b : ℕ) (w : Pl E) :
    ((iwGL a w).prod (iwGL b w)).relIndex ((GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w b)) ≠ 0 := by
  rw [relIndex_prod]
  exact mul_ne_zero (iw_idx a w) (iw_idx b w)

def tm (n : ℕ) (w : Pl E) (ϖ : (w.adicCompletion E)ˣ) (a : ℕ) (x : Fin n → ℤ) (s : Finset (Fin (n / 2)))
    (y : GLw a w × GLw (n - a) w) : ℂ :=
  if h : admitted n a s then
    (-qh w) ^ (-vRes n a (lOf x) s) *
      dd a (n - a) w (tdiag ϖ (restr x _ h.2.2.2.1)) (tdiag ϖ (restr x _ h.2.2.2.2)) y
  else 0

theorem tm_hecke (n : ℕ) (w : Pl E) (ϖ : (w.adicCompletion E)ˣ) (a : ℕ) (x : Fin n → ℤ) (s : Finset (Fin (n / 2))) :
    IsHecke ((iwGL a w).prod (iwGL (n - a) w)) (tm n w ϖ a x s) := by
  by_cases h : admitted n a s
  · have e : tm n w ϖ a x s = fun y => (-qh w) ^ (-vRes n a (lOf x) s) *
        dd a (n - a) w (tdiag ϖ (restr x _ h.2.2.2.1)) (tdiag ϖ (restr x _ h.2.2.2.2)) y := by
      funext y
      exact dif_pos h
    rw [e]
    exact isHecke_const_mul _ (dd_hecke _ _ _ _ _)
  · have e : tm n w ϖ a x s = fun _ => 0 := by
      funext y
      exact dif_neg h
    rw [e]
    exact isHecke_zero _

theorem entT_eq (n : ℕ) (w : Pl E) (ϖ : (w.adicCompletion E)ˣ) (a : ℕ) {J : Type} [Fintype J] (c : J → ℂ)
    (x : J → Fin n → ℤ) (s : Finset (Fin (n / 2))) (y : GLw a w × GLw (n - a) w) :
    entT n w ϖ a c x s y = ∑ j, c j * tm n w ϖ a (x j) s y := by
  unfold entT tm
  by_cases h : admitted n a s
  · simp only [dif_pos h, dd]
    exact Finset.sum_congr rfl fun j _ => by ring
  · simp [dif_neg h]

theorem entT_hecke (n : ℕ) (w : Pl E) (ϖ : (w.adicCompletion E)ˣ) (a : ℕ) {J : Type} [Fintype J] (c : J → ℂ)
    (x : J → Fin n → ℤ) (s : Finset (Fin (n / 2))) :
    IsHecke ((iwGL a w).prod (iwGL (n - a) w)) (entT n w ϖ a c x s) := by
  have e : entT n w ϖ a c x s = fun y => ∑ j, c j * tm n w ϖ a (x j) s y := funext (entT_eq n w ϖ a c x s)
  rw [e]
  exact isHecke_sum fun j => isHecke_const_mul _ (tm_hecke n w ϖ a (x j) s)

theorem phiX_eq (n : ℕ) (w : Pl E) (b : GLw n w) (ϖ : (w.adicCompletion E)ˣ) (x : Fin n → ℤ) (a : ℕ)
    (y : GLw a w × GLw (n - a) w) : phiX n w b ϖ x a y = cR n a w b * ∑ s, tm n w ϖ a x s y := by
  unfold phiX
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  by_cases hA : admitted n a s
  · rw [dif_pos (⟨hA.1, hA.2.1, hA.2.2.1⟩ : _ ∧ _ ∧ _), dif_pos hA.2.2.2.1, dif_pos hA.2.2.2.2]
    unfold tm
    rw [dif_pos hA]
    unfold cR dd
    ring
  · have : tm n w ϖ a x s y = 0 := dif_neg hA
    rw [this, mul_zero]
    split_ifs with h1 h2 h3
    · exact absurd ⟨h1.1, h1.2.1, h1.2.2, h2, h3⟩ hA
    · rfl
    · rfl
    · rfl

theorem phiX_hecke (n : ℕ) (w : Pl E) (b : GLw n w) (ϖ : (w.adicCompletion E)ˣ) (x : Fin n → ℤ) (a : ℕ) :
    IsHecke ((iwGL a w).prod (iwGL (n - a) w)) (phiX n w b ϖ x a) := by
  have e : phiX n w b ϖ x a = fun y => cR n a w b * ∑ s, tm n w ϖ a x s y := funext (phiX_eq n w b ϖ x a)
  rw [e]
  exact isHecke_const_mul _ (isHecke_sum fun s => tm_hecke n w ϖ a x s)

theorem qh_ne {w : Pl E} : -qh w ≠ 0 := by
  refine neg_ne_zero.2 ?_
  unfold qh
  have h : 0 < (qV E w : ℝ) := Nat.cast_pos.2 (Nat.pos_of_ne_zero (GlobalTheory.LFun.qV_ne_zero w))
  exact_mod_cast (Real.sqrt_pos.2 h).ne'

theorem pow_add_q {w : Pl E} (n a : ℕ) {l l' : Fin (n / 2) → ℤ} (h : Cone l) (h' : Cone l') (s : Finset (Fin (n / 2))) :
    (-qh w) ^ (-vRes n a (l + l') s) = (-qh w) ^ (-vRes n a l s) * (-qh w) ^ (-vRes n a l' s) := by
  rw [vRes_add a h h', neg_add, zpow_add₀ qh_ne]

theorem entT_adm (n : ℕ) (w : Pl E) (ϖ : (w.adicCompletion E)ˣ) (a : ℕ) {J : Type} [Fintype J] (c : J → ℂ)
    (x : J → Fin n → ℤ) {s : Finset (Fin (n / 2))} (h : admitted n a s) (y : GLw a w × GLw (n - a) w) :
    entT n w ϖ a c x s y = ∑ j, (c j * (-qh w) ^ (-vRes n a (lOf (x j)) s)) *
      dd a (n - a) w (tdiag ϖ (restr (x j) _ h.2.2.2.1)) (tdiag ϖ (restr (x j) _ h.2.2.2.2)) y := by
  unfold entT
  rw [dif_pos h]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [dd]
  ring

abbrev beta (a b : ℕ) (w : Pl E) : ℂ :=
  ((((iwGL a w).prod (iwGL b w)).relIndex ((GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w b)) : ℕ) : ℂ)⁻¹

abbrev alpha (n : ℕ) (w : Pl E) (b : GLw n w) : ℂ := (((iwU n w b).relIndex (KL n w) : ℕ) : ℂ)⁻¹

theorem mconv_entT (hD : DcosMul) {w : Pl E} (n : ℕ) (ϖ : (w.adicCompletion E)ˣ) (hϖ : IsUnifAt ϖ) (a : ℕ)
    {J J' : Type} [Fintype J] [Fintype J'] (c : J → ℂ) (x : J → Fin n → ℤ) (c' : J' → ℂ) (x' : J' → Fin n → ℤ)
    (hx : ∀ j, StrictAnti (x j) ∧ Cone (lOf (x j))) (hx' : ∀ j, StrictAnti (x' j) ∧ Cone (lOf (x' j)))
    (r : ℂ) (s : Finset (Fin (n / 2))) :
    mconv (entT n w ϖ a c x s) (fun y => r * entT n w ϖ a c' x' s y) =
      fun y => (r * beta a (n - a) w) *
        entT n w ϖ a (fun p : J × J' => c p.1 * c' p.2) (fun p => x p.1 + x' p.2) s y := by
  funext y
  by_cases h : admitted n a s
  · have ho := iwahori_pair_open a (n - a) w
    have hle := iwahori_pair_le_maximal a (n - a) w
    have hidx := iwahori_pair_index_ne_zero a (n - a) w
    have e1 : entT n w ϖ a c x s = fun z => ∑ j, (c j * (-qh w) ^ (-vRes n a (lOf (x j)) s)) *
        dd a (n - a) w (tdiag ϖ (restr (x j) _ h.2.2.2.1)) (tdiag ϖ (restr (x j) _ h.2.2.2.2)) z :=
      funext (entT_adm n w ϖ a c x h)
    have e2 : entT n w ϖ a c' x' s = fun z => ∑ j, (c' j * (-qh w) ^ (-vRes n a (lOf (x' j)) s)) *
        dd a (n - a) w (tdiag ϖ (restr (x' j) _ h.2.2.2.1)) (tdiag ϖ (restr (x' j) _ h.2.2.2.2)) z :=
      funext (entT_adm n w ϖ a c' x' h)
    have s1 : mconv (entT n w ϖ a c x s) (fun y => r * entT n w ϖ a c' x' s y) y =
        r * hint ((GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w (n - a)))
          (fun z => entT n w ϖ a c x s z * entT n w ϖ a c' x' s (z⁻¹ * y)) :=
      conv_const ho hle hidx (entT_hecke n w ϖ a c x s) (entT_hecke n w ϖ a c' x' s) r y
    have s2 := conv_sum_sum ho hle hidx (fun j => c j * (-qh w) ^ (-vRes n a (lOf (x j)) s))
      (fun j => dd a (n - a) w (tdiag ϖ (restr (x j) _ h.2.2.2.1)) (tdiag ϖ (restr (x j) _ h.2.2.2.2)))
      (fun j => c' j * (-qh w) ^ (-vRes n a (lOf (x' j)) s))
      (fun j => dd a (n - a) w (tdiag ϖ (restr (x' j) _ h.2.2.2.1)) (tdiag ϖ (restr (x' j) _ h.2.2.2.2)))
      (fun j => dd_hecke _ _ _ _ _) (fun j => dd_hecke _ _ _ _ _) y
    have s3 : ∀ j j', hint ((GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w (n - a))) (fun z =>
          dd a (n - a) w (tdiag ϖ (restr (x j) _ h.2.2.2.1)) (tdiag ϖ (restr (x j) _ h.2.2.2.2)) z *
          dd a (n - a) w (tdiag ϖ (restr (x' j') _ h.2.2.2.1)) (tdiag ϖ (restr (x' j') _ h.2.2.2.2)) (z⁻¹ * y)) =
        beta a (n - a) w * dd a (n - a) w (tdiag ϖ (restr (x j + x' j') _ h.2.2.2.1))
          (tdiag ϖ (restr (x j + x' j') _ h.2.2.2.2)) y := fun j j' =>
      congrFun (hD E w ϖ hϖ a (n - a) _ _ _ _ (restr_anti (hx j).1 _ _) (restr_anti (hx' j').1 _ _)
        (restr_anti (hx j).1 _ _) (restr_anti (hx' j').1 _ _)) y
    rw [s1, e1, e2]
    refine (congrArg (fun t : ℂ => r * t) s2).trans ?_
    simp only [s3]
    rw [entT_adm n w ϖ a _ _ h y, Fintype.sum_prod_type]
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun j' _ => ?_
    simp only [lOf_add, pow_add_q n a (hx j).2 (hx' j').2 s]
    ring
  · have e1 : entT n w ϖ a c x s = fun _ => 0 := by
      funext z
      exact dif_neg h
    have e2 : entT n w ϖ a (fun p : J × J' => c p.1 * c' p.2) (fun p => x p.1 + x' p.2) s y = 0 := dif_neg h
    rw [e2, e1, mul_zero]
    simp [mconv, hint]

theorem lconv_comb (hFU : FUMul) (hU : Unr E) {w : Pl E} (hw : ¬ IsSplitAt w) {n : ℕ} {b : GLw n w} (hb : IsWitt n w b)
    {ϖ : (w.adicCompletion E)ˣ} (hϖ : IsUnifAt ϖ) {J J' : Type} [Fintype J] [Fintype J'] (c : J → ℂ)
    (x : J → Fin n → ℤ) (c' : J' → ℂ) (x' : J' → Fin n → ℤ)
    (hx : ∀ j, StrictAnti (x j) ∧ Cone (lOf (x j))) (hx' : ∀ j, StrictAnti (x' j) ∧ Cone (lOf (x' j))) (r : ℂ) :
    lconv (fun γ => ∑ j, c j * fU n w b ϖ (lOf (x j)) γ) (fun γ => r * ∑ j, c' j * fU n w b ϖ (lOf (x' j)) γ) =
      fun γ => (r * alpha n w b) * ∑ p : J × J', (c p.1 * c' p.2) * fU n w b ϖ (lOf (x p.1 + x' p.2)) γ := by
  funext y
  have hc : Continuous (cj w) := (GlobalTheory.T.placeConjugation_properties_cmField E hU w).1
  have ho := GlobalTheory.CompanionTheory.IwLevels.isOpen_iwU n w b
  have hle := GlobalTheory.CompanionTheory.IwLevels.iwU_le_KL n w b hb.1
  have hidx : (iwU n w b).relIndex (KL n w) ≠ 0 :=
    GlobalTheory.CompanionTheory.IwLevels.relIndex_ne_zero ho (GlobalTheory.CompanionTheory.IwLevels.isCompact_KL hw n hc)
  have hH : ∀ l, IsHecke (iwU n w b) (fU n w b ϖ l) := fun l => fU_hecke hw b ϖ l hc
  have hS : ∀ {I : Type} [Fintype I] (d : I → ℂ) (z : I → Fin n → ℤ),
      IsHecke (iwU n w b) (fun γ => ∑ j, d j * fU n w b ϖ (lOf (z j)) γ) := fun d z =>
    isHecke_sum fun j => isHecke_const_mul _ (hH _)
  have s1 : lconv (fun γ => ∑ j, c j * fU n w b ϖ (lOf (x j)) γ)
      (fun γ => r * ∑ j, c' j * fU n w b ϖ (lOf (x' j)) γ) y =
      r * hint (KL n w) (fun z => (∑ j, c j * fU n w b ϖ (lOf (x j)) z) *
        (∑ j, c' j * fU n w b ϖ (lOf (x' j)) (z⁻¹ * y))) :=
    conv_const ho hle hidx (hS c x) (hS c' x') r y
  have s2 := conv_sum_sum ho hle hidx c (fun j => fU n w b ϖ (lOf (x j))) c' (fun j => fU n w b ϖ (lOf (x' j)))
    (fun j => hH _) (fun j => hH _) y
  have s3 : ∀ j j', hint (KL n w) (fun z => fU n w b ϖ (lOf (x j)) z * fU n w b ϖ (lOf (x' j')) (z⁻¹ * y)) =
      alpha n w b * fU n w b ϖ (lOf (x j + x' j')) y := fun j j' => by
    have := congrFun (hFU E hU w hw n b hb ϖ hϖ _ _ (hx j).2 (hx' j').2) y
    rw [lOf_add]
    exact this
  rw [s1, s2]
  simp only [s3]
  rw [Fintype.sum_prod_type]
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun j' _ => ?_
  ring

theorem pow_claim (hFU : FUMul) (hD : DcosMul) (hU : Unr E) {w : Pl E} (hw : ¬ IsSplitAt w) {n : ℕ} (a : ℕ)
    {b : GLw n w} (hb : IsWitt n w b) {ϖ : (w.adicCompletion E)ˣ} (hϖ : IsUnifAt ϖ) {J : Type} [Fintype J]
    (c : J → ℂ) (x : J → Fin n → ℤ) (hx : ∀ j, StrictAnti (x j) ∧ Cone (lOf (x j))) (k : ℕ) :
    ∃ (J' : Type) (_ : Fintype J') (c' : J' → ℂ) (x' : J' → Fin n → ℤ),
      (∀ j, StrictAnti (x' j) ∧ Cone (lOf (x' j))) ∧
      lpow (iwU n w b) (fun γ => ∑ j, c j * fU n w b ϖ (lOf (x j)) γ) (k + 1) =
        (fun γ => alpha n w b ^ k * ∑ j, c' j * fU n w b ϖ (lOf (x' j)) γ) ∧
      ∀ s, mpow w (entT n w ϖ a c x s) (k + 1) = fun y => beta a (n - a) w ^ k * entT n w ϖ a c' x' s y := by
  induction k with
  | zero =>
    refine ⟨J, inferInstance, c, x, hx, ?_, fun s => ?_⟩
    · have hc : Continuous (cj w) := (GlobalTheory.T.placeConjugation_properties_cmField E hU w).1
      have ho := GlobalTheory.CompanionTheory.IwLevels.isOpen_iwU n w b
      have hle := GlobalTheory.CompanionTheory.IwLevels.iwU_le_KL n w b hb.1
      have hidx : (iwU n w b).relIndex (KL n w) ≠ 0 :=
        GlobalTheory.CompanionTheory.IwLevels.relIndex_ne_zero ho (GlobalTheory.CompanionTheory.IwLevels.isCompact_KL hw n hc)
      have hq : IsHecke (iwU n w b) (fun γ => ∑ j, c j * fU n w b ϖ (lOf (x j)) γ) :=
        isHecke_sum fun j => isHecke_const_mul _ (fU_hecke hw b ϖ _ hc)
      funext y
      have := conv_unit (f := fun γ => ∑ j, c j * fU n w b ϖ (lOf (x j)) γ) hle hidx (fun k hk z => (hq.2 k hk z).2) y
      rw [pow_zero, one_mul]
      exact this
    · funext y
      have := conv_unit (iwahori_pair_le_maximal a (n - a) w) (iwahori_pair_index_ne_zero a (n - a) w)
        (fun k hk z => ((entT_hecke n w ϖ a c x s).2 k hk z).2) y
      rw [pow_zero, one_mul]
      exact this
  | succ k ih =>
    obtain ⟨J', _, c', x', hx', e1, e2⟩ := ih
    refine ⟨J × J', inferInstance, fun p => c p.1 * c' p.2, fun p => x p.1 + x' p.2, fun p => ⟨?_, ?_⟩, ?_, fun s => ?_⟩
    · exact fun i j hij => add_lt_add ((hx p.1).1 hij) ((hx' p.2).1 hij)
    · rw [lOf_add]
      exact cone_add (hx p.1).2 (hx' p.2).2
    · show lconv _ (lpow (iwU n w b) _ (k + 1)) = _
      rw [e1, lconv_comb hFU hU hw hb hϖ c x c' x' hx hx', pow_succ]
    · show mconv _ (mpow w _ (k + 1)) = _
      rw [e2, mconv_entT hD n ϖ hϖ a c x c' x' hx hx', pow_succ]

theorem matchTOf : MatchTOf := by
  intro hM4 hFU hD hLin E _ _ _ hU w hw n a ha b hb ϖ hϖ J _ c x hx k hk
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  obtain ⟨J', _, c', x', hx', e1, e2⟩ := pow_claim hFU hD hU hw a hb hϖ c x hx k
  have hc : Continuous (cj w) := (GlobalTheory.T.placeConjugation_properties_cmField E hU w).1
  have hoU := GlobalTheory.CompanionTheory.IwLevels.isOpen_iwU n w b
  have hoG := iwahori_pair_open a (n - a) w
  have hm := hLin E n a (n - a) w 1 J' (fun j => alpha n w b ^ k * c' j) (fun j => fU n w b ϖ (lOf (x' j)))
    (fun j => phiX n w b ϖ (x' j) a)
    (fun j => ⟨isHecke_continuous hoU (fU_hecke hw b ϖ _ hc), (fU_hecke hw b ϖ _ hc).1,
      isHecke_continuous hoG (phiX_hecke n w b ϖ _ a), (phiX_hecke n w b ϖ _ a).1⟩)
    (fun j => (hM4 E hU w hw n a ha b hb ϖ hϖ (x' j) (hx' j).1 (hx' j).2).1)
  have hcon : cR n a w b * beta a (n - a) w = alpha n w b := by
    have h1 : (((iwGL a w).relIndex (GlobalTheory.LFun.KGL w a) : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (iw_idx a w)
    have h2 : (((iwGL (n - a) w).relIndex (GlobalTheory.LFun.KGL w (n - a)) : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (iw_idx (n - a) w)
    unfold cR beta alpha
    rw [relIndex_prod, Nat.cast_mul]
    field_simp
  have ef : lpow (iwU n w b) (fun γ => ∑ j, c j * fU n w b ϖ (lOf (x j)) γ) (k + 1) =
      fun γ => ∑ j, (alpha n w b ^ k * c' j) * fU n w b ϖ (lOf (x' j)) γ := by
    rw [e1]
    funext γ
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have eφ : (fun y => cR n a w b ^ (k + 1) * ∑ s, mpow w (entT n w ϖ a c x s) (k + 1) y) =
      fun y => ∑ j, (alpha n w b ^ k * c' j) * phiX n w b ϖ (x' j) a y := by
    funext y
    simp only [e2, entT_eq, phiX_eq]
    have e3 : ∑ s, beta a (n - a) w ^ k * ∑ j, c' j * tm n w ϖ a (x' j) s y =
        beta a (n - a) w ^ k * ∑ j, c' j * ∑ s, tm n w ϖ a (x' j) s y := by
      rw [← Finset.mul_sum, Finset.sum_comm]
      simp only [Finset.mul_sum]
    rw [e3, ← hcon, mul_pow, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [ef, eφ]
  exact hm

end GlobalTheory.CompanionTheory.MatchPow

end
