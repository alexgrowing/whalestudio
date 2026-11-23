import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Slopes
import GroundTheory.HeightsAndTheta.Heights.Slopes.StatementsSupInf
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField

noncomputable section

namespace CanonicalFiltration

variable {K : Type} [Field K] [NumberField K] (E : HermitianBundle.{0} K)

theorem rank_mono {A B : Submodule (𝓞 K) E.carrier} (h : A ≤ B) : E.rank A ≤ E.rank B :=
  Submodule.finrank_mono h

theorem rank_sup_add_rank_inf (A B : Submodule (𝓞 K) E.carrier) :
    E.rank (A ⊔ B) + E.rank (A ⊓ B) = E.rank A + E.rank B := by
  have h := Submodule.rank_sup_add_rank_inf_eq A B
  unfold HermitianBundle.rank
  rw [← Module.finrank_eq_rank, ← Module.finrank_eq_rank, ← Module.finrank_eq_rank,
    ← Module.finrank_eq_rank] at h
  exact_mod_cast h

theorem le_of_saturated_of_rank_le {F H : Submodule (𝓞 K) E.carrier} (hF : E.Saturated F)
    (hFH : F ≤ H) (hr : E.rank H ≤ E.rank F) : H ≤ F := by
  intro x hx
  set N : Submodule (𝓞 K) H := F.comap H.subtype
  have hN : Module.finrank (𝓞 K) N = E.rank F := (Submodule.comapSubtypeEquivOfLe hFH).finrank_eq
  have hq := Submodule.finrank_quotient_add_finrank N
  have hH : Module.finrank (𝓞 K) H = E.rank H := rfl
  have h0 : Module.finrank (𝓞 K) (H ⧸ N) = 0 := by omega
  have htor := Module.finrank_eq_zero_iff_isTorsion.mp h0
  obtain ⟨⟨a, ha⟩, hax⟩ := @htor (Submodule.Quotient.mk (⟨x, hx⟩ : H))
  have hmk : Submodule.Quotient.mk (p := N) (a • (⟨x, hx⟩ : H)) = 0 := by
    rw [Submodule.Quotient.mk_smul]
    exact hax
  have hmem := (Submodule.Quotient.mk_eq_zero N).mp hmk
  exact hF a x (nonZeroDivisors.ne_zero ha) hmem

theorem rank_lt_of_saturated {F H : Submodule (𝓞 K) E.carrier} (hF : E.Saturated F) (hFH : F < H) :
    E.rank F < E.rank H := by
  by_contra h
  exact hFH.not_ge (le_of_saturated_of_rank_le E hF hFH.le (not_lt.mp h))

def saturation (G : Submodule (𝓞 K) E.carrier) : Submodule (𝓞 K) E.carrier where
  carrier := {x | ∃ a : 𝓞 K, a ≠ 0 ∧ a • x ∈ G}
  add_mem' := by
    rintro x y ⟨a, ha, hx⟩ ⟨b, hb, hy⟩
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    have h1 : (a * b) • x = b • (a • x) := by rw [mul_comm, mul_smul]
    have h2 : (a * b) • y = a • (b • y) := by rw [mul_smul]
    rw [smul_add, h1, h2]
    exact G.add_mem (G.smul_mem b hx) (G.smul_mem a hy)
  zero_mem' := ⟨1, one_ne_zero, by rw [smul_zero]; exact G.zero_mem⟩
  smul_mem' := by
    rintro c x ⟨a, ha, hx⟩
    refine ⟨a, ha, ?_⟩
    rw [smul_comm]
    exact G.smul_mem c hx

theorem le_saturation (G : Submodule (𝓞 K) E.carrier) : G ≤ saturation E G :=
  fun x hx ↦ ⟨1, one_ne_zero, by rw [one_smul]; exact hx⟩

theorem saturated_of_saturation_le {G : Submodule (𝓞 K) E.carrier} (h : saturation E G ≤ G) :
    E.Saturated G :=
  fun a _ ha hx ↦ h ⟨a, ha, hx⟩

theorem rank_saturation (G : Submodule (𝓞 K) E.carrier) : E.rank (saturation E G) = E.rank G := by
  set S := saturation E G
  set N : Submodule (𝓞 K) S := G.comap S.subtype
  have hN : Module.finrank (𝓞 K) N = E.rank G :=
    (Submodule.comapSubtypeEquivOfLe (le_saturation E G)).finrank_eq
  have hq := Submodule.finrank_quotient_add_finrank N
  have htor : Module.IsTorsion (𝓞 K) (S ⧸ N) := by
    intro q
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective N q
    obtain ⟨a, ha, hay⟩ := y.2
    refine ⟨⟨a, mem_nonZeroDivisors_of_ne_zero ha⟩, ?_⟩
    rw [Submonoid.smul_def, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    exact hay
  have h0 := Module.finrank_eq_zero_iff_isTorsion.mpr htor
  have hS : Module.finrank (𝓞 K) S = E.rank S := rfl
  omega

theorem degree_le_of_le_of_rank_eq {G S : Submodule (𝓞 K) E.carrier} (hGS : G ≤ S)
    (hr : E.rank G = E.rank S) : E.degree G ≤ E.degree S := by
  obtain ⟨s, hs⟩ := E.exists_linearIndependent_rank G
  let t : Fin (E.rank G) → S := fun i ↦ Submodule.inclusion hGS (s i)
  have ht : LinearIndependent (𝓞 K) t :=
    hs.map' _ (LinearMap.ker_eq_bot.mpr (Submodule.inclusion_injective hGS))
  rw [E.degree_eq_of_linearIndependent G hs (Fintype.card_fin _),
    E.degree_eq_of_linearIndependent S ht (by rw [Fintype.card_fin]; exact hr)]
  refine sub_le_sub_right ?_ _
  have hspan : Submodule.span (𝓞 K) (Set.range t) =
      (Submodule.span (𝓞 K) (Set.range s)).map (Submodule.inclusion hGS) := by
    rw [Submodule.map_span, ← Set.range_comp]
    rfl
  have hle : Submodule.span (𝓞 K) (Set.range s) ≤
      (Submodule.span (𝓞 K) (Set.range t)).comap (Submodule.inclusion hGS) := by
    rw [hspan]
    exact Submodule.le_comap_map _ _
  let φ := Submodule.mapQ _ _ (Submodule.inclusion hGS) hle
  have hinj : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro m hm
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ m
    rw [Submodule.mkQ_apply, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero, hspan] at hm
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    obtain ⟨y, hy, hyx⟩ := hm
    rwa [Submodule.inclusion_injective hGS hyx] at hy
  have hfin : Finite (S ⧸ Submodule.span (𝓞 K) (Set.range t)) :=
    finite_quotient_span ht (by rw [Fintype.card_fin]; exact hr)
  have hfin' : Finite (G ⧸ Submodule.span (𝓞 K) (Set.range s)) := Finite.of_injective φ hinj
  have hcard := Nat.card_le_card_of_injective φ hinj
  have hpos : 0 < Nat.card (G ⧸ Submodule.span (𝓞 K) (Set.range s)) := Nat.card_pos
  exact Real.log_le_log (by exact_mod_cast hpos) (by exact_mod_cast hcard)

theorem normDegree_sup_inf (hsub : DegreeSupInf.Statement) (A B : Submodule (𝓞 K) E.carrier) :
    E.normDegree A + E.normDegree B ≤ E.normDegree (A ⊔ B) + E.normDegree (A ⊓ B) := by
  have hd : (0 : ℝ) < Module.finrank ℚ K := by exact_mod_cast Module.finrank_pos
  simp only [HermitianBundle.normDegree]
  rw [← add_div, ← add_div]
  exact div_le_div_of_nonneg_right (hsub K E A B) hd.le

theorem defect_sup_inf (hsub : DegreeSupInf.Statement) (s : ℝ) (A B : Submodule (𝓞 K) E.carrier) :
    (E.normDegree A - s * E.rank A) + (E.normDegree B - s * E.rank B) ≤
      (E.normDegree (A ⊔ B) - s * E.rank (A ⊔ B)) + (E.normDegree (A ⊓ B) - s * E.rank (A ⊓ B)) := by
  have h1 := normDegree_sup_inf E hsub A B
  have hr : ((E.rank (A ⊔ B) : ℕ) : ℝ) + E.rank (A ⊓ B) = E.rank A + E.rank B := by
    exact_mod_cast rank_sup_add_rank_inf E A B
  have h2 : s * (E.rank (A ⊔ B) : ℝ) + s * E.rank (A ⊓ B) = s * E.rank A + s * E.rank B := by
    rw [← mul_add, ← mul_add, hr]
  linarith

theorem relSlope_le_iff {F H : Submodule (𝓞 K) E.carrier} (h : E.rank F < E.rank H) (s : ℝ) :
    E.relSlope F H ≤ s ↔ E.normDegree H - s * E.rank H ≤ E.normDegree F - s * E.rank F := by
  have hpos : (0 : ℝ) < (E.rank H : ℝ) - E.rank F := sub_pos.mpr (by exact_mod_cast h)
  rw [HermitianBundle.relSlope, div_le_iff₀ hpos, mul_sub]
  constructor <;> intro h' <;> linarith

theorem le_relSlope_iff {F H : Submodule (𝓞 K) E.carrier} (h : E.rank F < E.rank H) (s : ℝ) :
    s ≤ E.relSlope F H ↔ E.normDegree F - s * E.rank F ≤ E.normDegree H - s * E.rank H := by
  have hpos : (0 : ℝ) < (E.rank H : ℝ) - E.rank F := sub_pos.mpr (by exact_mod_cast h)
  rw [HermitianBundle.relSlope, le_div_iff₀ hpos, mul_sub]
  constructor <;> intro h' <;> linarith

theorem relSlope_lt_iff {F H : Submodule (𝓞 K) E.carrier} (h : E.rank F < E.rank H) (s : ℝ) :
    E.relSlope F H < s ↔ E.normDegree H - s * E.rank H < E.normDegree F - s * E.rank F := by
  rw [← not_le, le_relSlope_iff E h, not_le]

theorem exists_relMax (hfin : DegreeBoundedFinite.Statement) (hsub : DegreeSupInf.Statement)
    {F : Submodule (𝓞 K) E.carrier} (hF : E.Saturated F) (hFt : F < ⊤) :
    ∃ G, F < G ∧ E.Saturated G ∧ (∀ H, F < H → E.relSlope F H ≤ E.relSlope F G) ∧
      ∀ H, F < H → E.relSlope F H = E.relSlope F G → H ≤ G := by
  set c0 := E.relSlope F ⊤
  set n : ℝ := (E.rank ⊤ : ℝ)
  have hd : (0 : ℝ) < Module.finrank ℚ K := by exact_mod_cast Module.finrank_pos
  let S : Set (Submodule (𝓞 K) E.carrier) := {H | F < H ∧ c0 ≤ E.relSlope F H}
  have hSfin : S.Finite := by
    refine (hfin K E ((E.normDegree F - |c0| * n) * Module.finrank ℚ K)).subset ?_
    rintro H ⟨hFH, hc⟩
    show (E.normDegree F - |c0| * n) * Module.finrank ℚ K ≤ E.degree H
    have hr := rank_lt_of_saturated E hF hFH
    have hrr : (0 : ℝ) < (E.rank H : ℝ) - E.rank F := sub_pos.mpr (by exact_mod_cast hr)
    have hrH : (E.rank H : ℝ) ≤ n := (Nat.cast_le (α := ℝ)).mpr (rank_mono E (le_top : H ≤ ⊤))
    have hrF : (0 : ℝ) ≤ E.rank F := Nat.cast_nonneg _
    rw [le_relSlope_iff E hr] at hc
    have e1 : 0 ≤ (|c0| + c0) * ((E.rank H : ℝ) - E.rank F) :=
      mul_nonneg (by linarith [neg_abs_le c0]) hrr.le
    have e2 : 0 ≤ |c0| * (n - ((E.rank H : ℝ) - E.rank F)) := mul_nonneg (abs_nonneg _) (by linarith)
    have h3 : E.normDegree F - |c0| * n ≤ E.normDegree H := by nlinarith
    have h4 : E.normDegree H * Module.finrank ℚ K = E.degree H := by
      unfold HermitianBundle.normDegree
      field_simp
    nlinarith
  have hSne : S.Nonempty := ⟨⊤, hFt, le_rfl⟩
  obtain ⟨G0, hG0S, hG0max⟩ := Set.exists_max_image S (E.relSlope F) hSfin hSne
  set s := E.relSlope F G0
  have hmax : ∀ H, F < H → E.relSlope F H ≤ s := by
    intro H hH
    by_cases hc : c0 ≤ E.relSlope F H
    · exact hG0max H ⟨hH, hc⟩
    · exact (lt_of_not_ge hc).le.trans hG0S.2
  have hmax' : ∀ I, F ≤ I → E.normDegree I - s * E.rank I ≤ E.normDegree F - s * E.rank F := by
    intro I hI
    rcases hI.lt_or_eq with hI | rfl
    · exact (relSlope_le_iff E (rank_lt_of_saturated E hF hI) s).mp (hmax I hI)
    · exact le_rfl
  let T : Set (Submodule (𝓞 K) E.carrier) := {H | F < H ∧ E.relSlope F H = s}
  have hTfin : T.Finite := hSfin.subset fun H hH ↦ ⟨hH.1, hG0S.2.trans hH.2.ge⟩
  obtain ⟨G, hGT, hGmax⟩ := hTfin.exists_maximal ⟨G0, hG0S.1, rfl⟩
  have hsupT : ∀ H ∈ T, G ⊔ H ∈ T := by
    intro H hH
    have hFU : F < G ⊔ H := lt_of_lt_of_le hGT.1 le_sup_left
    refine ⟨hFU, le_antisymm (hmax _ hFU) ?_⟩
    rw [le_relSlope_iff E (rank_lt_of_saturated E hF hFU)]
    have hI := hmax' (G ⊓ H) (le_inf hGT.1.le hH.1.le)
    have hG := (le_relSlope_iff E (rank_lt_of_saturated E hF hGT.1) s).mp hGT.2.ge
    have hH' := (le_relSlope_iff E (rank_lt_of_saturated E hF hH.1) s).mp hH.2.ge
    have hsm := defect_sup_inf E hsub s G H
    linarith
  have hlarge : ∀ H, F < H → E.relSlope F H = s → H ≤ G := fun H hFH hs ↦
    le_sup_right.trans (hGmax (hsupT H ⟨hFH, hs⟩) le_sup_left)
  have hsat : E.Saturated G := by
    refine saturated_of_saturation_le E (hlarge _ (lt_of_lt_of_le hGT.1 (le_saturation E G)) ?_)
    have hFS : F < saturation E G := lt_of_lt_of_le hGT.1 (le_saturation E G)
    refine le_antisymm (hmax _ hFS) ?_
    rw [le_relSlope_iff E (rank_lt_of_saturated E hF hFS)]
    have hG := (le_relSlope_iff E (rank_lt_of_saturated E hF hGT.1) s).mp hGT.2.ge
    have hdeg := degree_le_of_le_of_rank_eq E (le_saturation E G) (rank_saturation E G).symm
    have hnd : E.normDegree G ≤ E.normDegree (saturation E G) :=
      div_le_div_of_nonneg_right hdeg hd.le
    rw [rank_saturation E G]
    linarith
  refine ⟨G, hGT.1, hsat, fun H hH ↦ (hmax H hH).trans_eq hGT.2.symm, fun H hH heq ↦ ?_⟩
  exact hlarge H hH (heq.trans hGT.2)

structure IsCanonicalFrom (F : Submodule (𝓞 K) E.carrier) {m : ℕ}
    (f : Fin (m + 1) → Submodule (𝓞 K) E.carrier) : Prop where
  bot : f 0 = F
  top : f (Fin.last m) = ⊤
  strictMono : StrictMono f
  saturated : ∀ i, E.Saturated (f i)
  semistable : ∀ (i : Fin m) (G : Submodule (𝓞 K) E.carrier), f i.castSucc < G → G ≤ f i.succ →
    E.relSlope (f i.castSucc) G ≤ E.relSlope (f i.castSucc) (f i.succ)
  anti : StrictAnti fun i : Fin m ↦ E.relSlope (f i.castSucc) (f i.succ)

theorem isCanonicalFrom_bot_iff {m : ℕ} (f : Fin (m + 1) → Submodule (𝓞 K) E.carrier) :
    IsCanonicalFrom E ⊥ f ↔ E.IsCanonicalFiltration f :=
  ⟨fun h ↦ ⟨h.bot, h.top, h.strictMono, h.saturated, h.semistable, h.anti⟩,
    fun h ↦ ⟨h.bot, h.top, h.strictMono, h.saturated, h.semistable, h.anti⟩⟩

theorem isCanonicalFrom_cons {F G : Submodule (𝓞 K) E.carrier} {m : ℕ}
    {g : Fin (m + 1) → Submodule (𝓞 K) E.carrier} (hF : E.Saturated F) (hFG : F < G)
    (hmax : ∀ H, F < H → E.relSlope F H ≤ E.relSlope F G)
    (hlarge : ∀ H, F < H → E.relSlope F H = E.relSlope F G → H ≤ G)
    (hg : IsCanonicalFrom E G g) :
    IsCanonicalFrom E F (Fin.cons F g : Fin (m + 2) → Submodule (𝓞 K) E.carrier) := by
  have hg0 : g 0 = G := hg.bot
  refine ⟨Fin.cons_zero _ _, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← Fin.succ_last, Fin.cons_succ]
    exact hg.top
  · rw [Fin.strictMono_iff_lt_succ]
    intro i
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · rw [Fin.castSucc_zero, Fin.cons_zero, Fin.cons_succ, hg0]
      exact hFG
    · rw [← Fin.succ_castSucc, Fin.cons_succ, Fin.cons_succ]
      exact hg.strictMono Fin.castSucc_lt_succ
  · intro i
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · rw [Fin.cons_zero]
      exact hF
    · rw [Fin.cons_succ]
      exact hg.saturated j
  · intro i H
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · rw [Fin.castSucc_zero, Fin.cons_zero, Fin.cons_succ, hg0]
      intro h1 _
      exact hmax H h1
    · rw [← Fin.succ_castSucc, Fin.cons_succ, Fin.cons_succ]
      exact hg.semistable j H
  · rcases m with _ | k
    · have : Subsingleton (Fin (0 + 1)) := inferInstanceAs (Subsingleton (Fin 1))
      exact Subsingleton.strictAnti _
    rw [Fin.strictAnti_iff_succ_lt]
    intro i
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · simp only [← Fin.succ_castSucc, Fin.cons_succ, Fin.cons_zero, Fin.castSucc_zero, hg0]
      have hG1 : G < g (Fin.succ 0) := by
        rw [← hg0]
        exact hg.strictMono (Fin.succ_pos 0)
      have hrFG := rank_lt_of_saturated E hF hFG
      have hrG1 := rank_lt_of_saturated E (hg0 ▸ hg.saturated 0) hG1
      by_contra hcon
      rw [not_lt, le_relSlope_iff E hrG1] at hcon
      have h1 := (le_relSlope_iff E hrFG (E.relSlope F G)).mp le_rfl
      have h2 : E.relSlope F G ≤ E.relSlope F (g (Fin.succ 0)) := by
        rw [le_relSlope_iff E (hrFG.trans hrG1)]
        linarith
      have h3 := hlarge _ (hFG.trans hG1) (le_antisymm (hmax _ (hFG.trans hG1)) h2)
      exact hG1.not_ge h3
    · simp only [← Fin.succ_castSucc, Fin.cons_succ]
      have h := hg.anti (Fin.castSucc_lt_succ (i := j))
      simp only [← Fin.succ_castSucc] at h
      exact h

theorem IsCanonicalFrom.tail {F : Submodule (𝓞 K) E.carrier} {k : ℕ}
    {g : Fin (k + 2) → Submodule (𝓞 K) E.carrier} (hg : IsCanonicalFrom E F g) :
    IsCanonicalFrom E (g 1) (Fin.tail g) := by
  refine ⟨?_, ?_, hg.strictMono.comp (Fin.strictMono_succ), fun i ↦ hg.saturated _, ?_, ?_⟩
  · show g (Fin.succ 0) = g 1
    rw [Fin.succ_zero_eq_one]
  · show g (Fin.succ (Fin.last k)) = ⊤
    rw [Fin.succ_last]
    exact hg.top
  · intro i H
    show g (Fin.succ (Fin.castSucc i)) < H → H ≤ g (Fin.succ (Fin.succ i)) →
      E.relSlope (g (Fin.succ (Fin.castSucc i))) H ≤
        E.relSlope (g (Fin.succ (Fin.castSucc i))) (g (Fin.succ (Fin.succ i)))
    rw [Fin.succ_castSucc]
    exact hg.semistable i.succ H
  · intro a b hab
    show E.relSlope (g (Fin.succ (Fin.castSucc b))) (g (Fin.succ (Fin.succ b))) <
      E.relSlope (g (Fin.succ (Fin.castSucc a))) (g (Fin.succ (Fin.succ a)))
    rw [Fin.succ_castSucc, Fin.succ_castSucc]
    exact hg.anti (Fin.succ_lt_succ_iff.mpr hab)

theorem IsCanonicalFrom.relSlope_le (hsub : DegreeSupInf.Statement) {F : Submodule (𝓞 K) E.carrier}
    {k : ℕ} {g : Fin (k + 2) → Submodule (𝓞 K) E.carrier} (hg : IsCanonicalFrom E F g)
    {H : Submodule (𝓞 K) E.carrier} (hFH : F < H) :
    E.relSlope F H ≤ E.relSlope F (g 1) ∧ (E.relSlope F H = E.relSlope F (g 1) → H ≤ g 1) := by
  have hF : E.Saturated F := hg.bot ▸ hg.saturated 0
  have hone : (1 : Fin (k + 2)) = ⟨1, by omega⟩ := Fin.ext (by simp)
  have hzero : g ⟨0, by omega⟩ = F := by
    rw [← hg.bot]
    exact congrArg g (Fin.ext (by simp))
  rw [hone]
  set s0 := E.relSlope F (g ⟨1, by omega⟩) with hs0
  have key : ∀ j : ℕ, ∀ (hj : j + 1 < k + 2) (H : Submodule (𝓞 K) E.carrier), F < H →
      H ≤ g ⟨j + 1, hj⟩ → E.relSlope F H ≤ s0 ∧ (E.relSlope F H = s0 → H ≤ g ⟨1, by omega⟩) := by
    intro j
    induction j with
    | zero =>
      intro hj H hFH hHle
      have hz' : g (Fin.castSucc (⟨0, by omega⟩ : Fin (k + 1))) = F := hzero
      have h := hg.semistable ⟨0, by omega⟩ H (by rw [hz']; exact hFH) hHle
      rw [hz'] at h
      exact ⟨h, fun _ ↦ hHle⟩
    | succ j ih =>
      intro hj H hFH hHle
      by_cases hHA : H ≤ g ⟨j + 1, by omega⟩
      · exact ih (by omega) H hFH hHA
      have hFA : F ≤ g ⟨j + 1, by omega⟩ := by
        rw [← hzero]
        exact hg.strictMono.monotone (Fin.mk_le_mk.mpr (by omega))
      have hAsat : E.Saturated (g ⟨j + 1, by omega⟩) := hg.saturated _
      have hAB : g ⟨j + 1, by omega⟩ ≤ g ⟨j + 1 + 1, hj⟩ :=
        hg.strictMono.monotone (Fin.mk_le_mk.mpr (by omega))
      have hAU : g ⟨j + 1, by omega⟩ < H ⊔ g ⟨j + 1, by omega⟩ :=
        lt_of_le_of_ne le_sup_right (fun h ↦ hHA (le_sup_left.trans h.ge))
      have hUB : H ⊔ g ⟨j + 1, by omega⟩ ≤ g ⟨j + 1 + 1, hj⟩ := sup_le hHle hAB
      have hss : E.relSlope (g ⟨j + 1, by omega⟩) (H ⊔ g ⟨j + 1, by omega⟩) ≤
          E.relSlope (g ⟨j + 1, by omega⟩) (g ⟨j + 1 + 1, hj⟩) :=
        hg.semistable ⟨j + 1, by omega⟩ _ hAU hUB
      have hanti := hg.anti
        (show (⟨0, by omega⟩ : Fin (k + 1)) < ⟨j + 1, by omega⟩ from Fin.mk_lt_mk.mpr (by omega))
      simp only [Fin.castSucc_mk, Fin.succ_mk, zero_add] at hanti
      rw [hzero] at hanti
      have hU := lt_of_le_of_lt hss hanti
      rw [relSlope_lt_iff E (rank_lt_of_saturated E hAsat hAU)] at hU
      have hsm := defect_sup_inf E hsub s0 H (g ⟨j + 1, by omega⟩)
      have hI : E.normDegree (H ⊓ g ⟨j + 1, by omega⟩) - s0 * E.rank (H ⊓ g ⟨j + 1, by omega⟩) ≤
          E.normDegree F - s0 * E.rank F := by
        rcases (le_inf hFH.le hFA : F ≤ H ⊓ g ⟨j + 1, by omega⟩).lt_or_eq with hlt | heq
        · exact (relSlope_le_iff E (rank_lt_of_saturated E hF hlt) s0).mp
            (ih (by omega) _ hlt inf_le_right).1
        · rw [← heq]
      have hlt : E.relSlope F H < s0 := by
        rw [relSlope_lt_iff E (rank_lt_of_saturated E hF hFH)]
        linarith
      exact ⟨hlt.le, fun h ↦ absurd h hlt.ne⟩
  have htop : g ⟨k + 1, by omega⟩ = ⊤ := hg.top
  exact key k (by omega) H hFH (by rw [htop]; exact le_top)

theorem range_eq_of_isCanonicalFrom (hsub : DegreeSupInf.Statement) (F : Submodule (𝓞 K) E.carrier) :
    ∀ {m m' : ℕ} {f : Fin (m + 1) → Submodule (𝓞 K) E.carrier}
      {f' : Fin (m' + 1) → Submodule (𝓞 K) E.carrier},
      IsCanonicalFrom E F f → IsCanonicalFrom E F f' → Set.range f = Set.range f' := by
  induction F using WellFoundedGT.induction with
  | ind F ih =>
  intro m m' f f' hf hf'
  have hone : ∀ i : Fin (0 + 1), i = 0 := fun i ↦ Fin.ext (by rw [Fin.val_zero]; have := i.isLt; omega)
  rcases m with _ | k <;> rcases m' with _ | k'
  · have : f = f' := funext fun i ↦ by rw [hone i, hf.bot, hf'.bot]
    rw [this]
  · have hFt : F = ⊤ := by rw [← hf.bot]; exact hf.top
    have := hf'.strictMono (Fin.succ_pos (0 : Fin (k' + 1)))
    rw [hf'.bot, hFt] at this
    exact absurd this not_top_lt
  · have hFt : F = ⊤ := by rw [← hf'.bot]; exact hf'.top
    have := hf.strictMono (Fin.succ_pos (0 : Fin (k + 1)))
    rw [hf.bot, hFt] at this
    exact absurd this not_top_lt
  · have h01 : ∀ n : ℕ, (0 : Fin (n + 2)) < 1 := fun n ↦ by
      rw [Fin.lt_def, Fin.val_zero, Fin.val_one]
      omega
    have hF1 : F < f 1 := hf.bot ▸ hf.strictMono (h01 k)
    have hF1' : F < f' 1 := hf'.bot ▸ hf'.strictMono (h01 k')
    have a := hf.relSlope_le E hsub hF1'
    have b := hf'.relSlope_le E hsub hF1
    have heq : f 1 = f' 1 :=
      le_antisymm (b.2 (le_antisymm b.1 a.1)) (a.2 (le_antisymm a.1 b.1))
    have ht := ih (f 1) hF1 hf.tail (by rw [heq]; exact hf'.tail)
    rw [← Fin.cons_self_tail f, ← Fin.cons_self_tail f', Fin.range_cons, Fin.range_cons, ht, hf.bot,
      hf'.bot]

theorem exists_isCanonicalFrom (hfin : DegreeBoundedFinite.Statement) (hsub : DegreeSupInf.Statement)
    (F : Submodule (𝓞 K) E.carrier) :
    E.Saturated F → ∃ (m : ℕ) (f : Fin (m + 1) → Submodule (𝓞 K) E.carrier), IsCanonicalFrom E F f := by
  induction F using WellFoundedGT.induction with
  | ind F ih =>
  intro hF
  rcases (le_top : F ≤ ⊤).lt_or_eq with hFt | rfl
  · obtain ⟨G, hFG, hG, hmax, hlarge⟩ := exists_relMax E hfin hsub hF hFt
    obtain ⟨m, g, hg⟩ := ih G hFG hG
    exact ⟨m + 1, _, isCanonicalFrom_cons E hF hFG hmax hlarge hg⟩
  · refine ⟨0, fun _ ↦ ⊤, rfl, rfl, ?_, fun _ ↦ E.saturated_top, fun i ↦ i.elim0, fun i ↦ i.elim0⟩
    intro a b hab
    exact absurd (Fin.lt_def.mp hab) (by have := a.isLt; have := b.isLt; omega)

end CanonicalFiltration

theorem CanonicalFiltration.proof (h₁ : DegreeBoundedFinite.Statement) (h₂ : DegreeSupInf.Statement) :
    CanonicalFiltration.Statement := by
  intro K _ _ E
  obtain ⟨m, f, hf⟩ := CanonicalFiltration.exists_isCanonicalFrom E h₁ h₂ ⊥ E.saturated_bot
  refine ⟨m, f, (CanonicalFiltration.isCanonicalFrom_bot_iff E f).mp hf, fun m' g hg ↦ ?_⟩
  exact CanonicalFiltration.range_eq_of_isCanonicalFrom E h₂ ⊥
    ((CanonicalFiltration.isCanonicalFrom_bot_iff E g).mpr hg) hf

example (K : Type) [Field K] [NumberField K] :
    CanonicalFiltration.IsCanonicalFrom (HermitianBundle.integers K) ⊥
      (trivialFlag (HermitianBundle.integers K)) :=
  (CanonicalFiltration.isCanonicalFrom_bot_iff _ _).mpr (isCanonicalFiltration_integers K)

end

end GroundTheory.Heights₂.Heights
