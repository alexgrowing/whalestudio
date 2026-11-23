import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsSemilocMaxIdeals
import GroundTheory.HeightsAndTheta.Heights.Intersections.StFibreOverFinite
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsSemilocIntegral
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsLocRingDimOne
import GroundTheory.HeightsAndTheta.Heights.Intersections.AvoidRing
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 IndefiniteRowSideFullHecke.Inter

namespace SemilocMaxIdeals

open regularityLocalFlat_holds

set_option linter.unusedSectionVars false

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  (P : Ideal (MRing ι)) [P.IsPrime] (𝒲 : Set (Ideal (MRing ι)))

theorem notMem_mul {I : Ideal (MRing ι)} (hI : I.IsPrime) {a b : MRing ι} (ha : a ∉ I) (hb : b ∉ I) :
    a * b ∉ I :=
  fun h => (hI.mem_or_mem h).elim ha hb

theorem one_notMem {I : Ideal (MRing ι)} (hI : I.IsPrime) : (1 : MRing ι) ∉ I :=
  fun h => hI.ne_top ((Ideal.eq_top_iff_one I).mpr h)

theorem fracHom_ne_zero {w : MRing ι} (hw : w ∉ P) : fracHom P w ≠ 0 :=
  fun h => hw (fracHom_eq_zero_iff.mp h)

theorem exists_frac (h𝒲 : ∀ W ∈ 𝒲, W.IsPrime) (x : semiLocRing P 𝒲) :
    ∃ (u w : MRing ι) (a : K → ℕ), IsMultiHomog u a ∧ IsMultiHomog w a ∧ w ∉ P ∧ (∀ W ∈ 𝒲, w ∉ W) ∧
      (x : FractionRing (MRing ι ⧸ P)) * fracHom P w = fracHom P u := by
  obtain ⟨x, hx⟩ := x
  induction hx using Subring.closure_induction with
  | mem x hx =>
    obtain ⟨u, w, a, hw, hwW, hu, hwa, rfl⟩ := hx
    exact ⟨u, w, a, hu, hwa, fun h => nonZeroDivisors.ne_zero hw (Ideal.Quotient.eq_zero_iff_mem.mpr h), hwW,
      IsLocalization.mk'_spec _ _ _⟩
  | zero =>
    exact ⟨0, 1, 0, homog_zero 0, homog_one, one_notMem ‹_›, fun W hW => one_notMem (h𝒲 W hW), by simp⟩
  | one =>
    exact ⟨1, 1, 0, homog_one, homog_one, one_notMem ‹_›, fun W hW => one_notMem (h𝒲 W hW), by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨u, w, a, hu, hw, hwP, hwW, hx⟩ := hx
    obtain ⟨u', w', a', hu', hw', hwP', hwW', hy⟩ := hy
    refine ⟨u * w' + u' * w, w * w', a + a', homog_add (homog_mul hu hw') ?_, homog_mul hw hw',
      notMem_mul ‹_› hwP hwP', fun W hW => notMem_mul (h𝒲 W hW) (hwW W hW) (hwW' W hW), ?_⟩
    · rw [add_comm a a']
      exact homog_mul hu' hw
    · simp only [map_add, map_mul]
      rw [← hx, ← hy]
      ring
  | neg x _ hx =>
    obtain ⟨u, w, a, hu, hw, hwP, hwW, hx⟩ := hx
    exact ⟨-u, w, a, homog_neg hu, hw, hwP, hwW, by rw [map_neg, ← hx, neg_mul]⟩
  | mul x y _ _ hx hy =>
    obtain ⟨u, w, a, hu, hw, hwP, hwW, hx⟩ := hx
    obtain ⟨u', w', a', hu', hw', hwP', hwW', hy⟩ := hy
    refine ⟨u * u', w * w', a + a', homog_mul hu hu', homog_mul hw hw', notMem_mul ‹_› hwP hwP',
      fun W hW => notMem_mul (h𝒲 W hW) (hwW W hW) (hwW' W hW), ?_⟩
    simp only [map_mul]
    rw [← hx, ← hy]
    ring

theorem frac_mem {u w : MRing ι} {a : K → ℕ} (hu : IsMultiHomog u a) (hw : IsMultiHomog w a) (hwP : w ∉ P)
    (hwW : ∀ W ∈ 𝒲, w ∉ W) : fracHom P u / fracHom P w ∈ semiLocRing P 𝒲 := by
  have hw' : Ideal.Quotient.mk P w ∈ nonZeroDivisors (MRing ι ⧸ P) :=
    mem_nonZeroDivisors_of_ne_zero (by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem])
  refine Subring.subset_closure ⟨u, w, a, hw', hwW, hu, hw, ?_⟩
  rw [IsFractionRing.mk'_eq_div]
  rfl

theorem mem_semiMaxIdeal_iff {W' : Ideal (MRing ι)} [W'.IsPrime] (hW' : W' ∈ 𝒲) (hPW : P ≤ W')
    [IsLocalRing (locRing P W')] (b : semiLocRing P 𝒲) {u w : MRing ι} {a : K → ℕ} (hu : IsMultiHomog u a)
    (hw : IsMultiHomog w a) (hwW : w ∉ W')
    (hb : (b : FractionRing (MRing ι ⧸ P)) * fracHom P w = fracHom P u) :
    b ∈ semiMaxIdeal P 𝒲 W' hW' ↔ u ∈ W' := by
  unfold semiMaxIdeal
  rw [Ideal.mem_comap]
  exact mem_maximalIdeal_iff hPW _ hu hw hwW (by rw [semiToLoc_coe]; exact hb)

theorem isUnit_of (b : semiLocRing P 𝒲) {u w : MRing ι} {a : K → ℕ} (hu : IsMultiHomog u a)
    (hw : IsMultiHomog w a) (huP : u ∉ P) (huW : ∀ W ∈ 𝒲, u ∉ W)
    (hb : (b : FractionRing (MRing ι ⧸ P)) * fracHom P w = fracHom P u) : IsUnit b := by
  refine IsUnit.of_mul_eq_one (⟨_, frac_mem P 𝒲 hw hu huP huW⟩ : semiLocRing P 𝒲) (Subtype.ext ?_)
  change (b : FractionRing (MRing ι ⧸ P)) * (fracHom P w / fracHom P u) = 1
  rw [mul_div_assoc', hb, div_self (fracHom_ne_zero P huP)]

theorem exists_scale (hfin : 𝒲.Finite) (h𝒲 : ∀ W ∈ 𝒲, IsMultiProjPrime W) (a : K → ℕ) {W' : Ideal (MRing ι)}
    (hr : IsRelevant W') (hp : W'.IsPrime) :
    ∃ (t h : MRing ι) (d : K → ℕ), IsMultiHomog t d ∧ IsMultiHomog h (a + d) ∧ t ∉ W' ∧ ∀ W ∈ 𝒲, h ∉ W := by
  obtain ⟨d₀, hd₀⟩ := AvoidRing.exists_form_avoid 𝒲 hfin h𝒲
  obtain ⟨h, hh, hhW⟩ := hd₀ (a + d₀) le_add_self
  obtain ⟨t, ht, htW⟩ := exists_form_notMem hr hp d₀
  exact ⟨t, h, d₀, ht, hh, htW, hhW⟩

variable {P 𝒲}

theorem le_of_semiMaxIdeal_le (hfin : 𝒲.Finite) (h𝒲 : ∀ W ∈ 𝒲, IsMultiProjPrime W ∧ P ≤ W)
    {W₁ W₂ : Ideal (MRing ι)} (h₁ : W₁ ∈ 𝒲) (h₂ : W₂ ∈ 𝒲) [IsLocalRing (locRing P W₁)]
    [IsLocalRing (locRing P W₂)] (hle : semiMaxIdeal P 𝒲 W₁ h₁ ≤ semiMaxIdeal P 𝒲 W₂ h₂) : W₁ ≤ W₂ := by
  obtain ⟨⟨hp1, ⟨S, hS, hW1⟩, -⟩, hP1⟩ := h𝒲 W₁ h₁
  obtain ⟨⟨hp2, -, hr2⟩, hP2⟩ := h𝒲 W₂ h₂
  have hmem : ∀ f ∈ S, f ∈ W₁ := fun f hf => hW1 ▸ Ideal.subset_span hf
  rw [hW1, Ideal.span_le]
  intro f hfS
  obtain ⟨a, hfa⟩ := hS f hfS
  obtain ⟨t, h, d, ht, hh, htW, hhW⟩ := exists_scale 𝒲 hfin (fun W hW => (h𝒲 W hW).1) a hr2 hp2
  have hhP : h ∉ P := fun hP => hhW W₁ h₁ (hP1 hP)
  let b : semiLocRing P 𝒲 := ⟨_, frac_mem P 𝒲 (homog_mul hfa ht) hh hhP hhW⟩
  have hb : (b : FractionRing (MRing ι ⧸ P)) * fracHom P h = fracHom P (f * t) :=
    div_mul_cancel₀ _ (fracHom_ne_zero P hhP)
  have h1 : b ∈ semiMaxIdeal P 𝒲 W₁ h₁ :=
    (mem_semiMaxIdeal_iff P 𝒲 h₁ hP1 b (homog_mul hfa ht) hh (hhW W₁ h₁) hb).mpr
      (W₁.mul_mem_right t (hmem f hfS))
  have h2 := (mem_semiMaxIdeal_iff P 𝒲 h₂ hP2 b (homog_mul hfa ht) hh (hhW W₂ h₂) hb).mp (hle h1)
  exact (hp2.mem_or_mem h2).resolve_right htW

theorem isLocalization (hfin : 𝒲.Finite) (h𝒲 : ∀ W ∈ 𝒲, IsMultiProjPrime W ∧ P ≤ W) {W' : Ideal (MRing ι)}
    (hW' : W' ∈ 𝒲) [IsLocalRing (locRing P W')] :
    letI := (semiToLoc P 𝒲 W' hW').toAlgebra
    IsLocalization.AtPrime (locRing P W') (semiMaxIdeal P 𝒲 W' hW') := by
  let := (semiToLoc P 𝒲 W' hW').toAlgebra
  obtain ⟨⟨hp, -, hr⟩, hPW⟩ := h𝒲 W' hW'
  refine (isLocalization_iff _ _).mpr ⟨?_, ?_, ?_⟩
  · rintro ⟨c, hc⟩
    by_contra hu
    exact hc (Ideal.mem_comap.mpr ((IsLocalRing.mem_maximalIdeal _).mpr hu))
  · intro z
    obtain ⟨u, w, a, hu, hw, hwW, hz⟩ := (mem_locRing_iff hPW).mp z.2
    obtain ⟨t, h, d, ht, hh, htW, hhW⟩ := exists_scale 𝒲 hfin (fun W hW => (h𝒲 W hW).1) a hr hp
    have hhP : h ∉ P := fun hP => hhW W' hW' (hPW hP)
    let b : semiLocRing P 𝒲 := ⟨_, frac_mem P 𝒲 (homog_mul hu ht) hh hhP hhW⟩
    let c : semiLocRing P 𝒲 := ⟨_, frac_mem P 𝒲 (homog_mul hw ht) hh hhP hhW⟩
    have hc : c ∉ semiMaxIdeal P 𝒲 W' hW' := by
      rw [mem_semiMaxIdeal_iff P 𝒲 hW' hPW c (homog_mul hw ht) hh (hhW W' hW')
        (div_mul_cancel₀ _ (fracHom_ne_zero P hhP))]
      exact notMem_mul hp hwW htW
    refine ⟨(b, ⟨c, show c ∈ (semiMaxIdeal P 𝒲 W' hW').primeCompl from hc⟩), Subtype.ext ?_⟩
    change (z : FractionRing (MRing ι ⧸ P)) * (fracHom P (w * t) / fracHom P h) = fracHom P (u * t) / fracHom P h
    rw [map_mul, map_mul, ← hz]
    ring
  · intro x y hxy
    have e : x = y := by
      have := congrArg Subtype.val hxy
      rw [RingHom.algebraMap_toAlgebra, semiToLoc_coe, semiToLoc_coe] at this
      exact Subtype.ext this
    exact ⟨1, by rw [e]⟩

theorem exists_eq_of_isMaximal (hfin : 𝒲.Finite) (h𝒲 : ∀ W ∈ 𝒲, IsMultiProjPrime W ∧ P ≤ W)
    (hne : 𝒲.Nonempty) (M : Ideal (semiLocRing P 𝒲)) (hM : M.IsMaximal) :
    ∃ (W' : Ideal (MRing ι)) (hW' : W' ∈ 𝒲), ∀ [IsLocalRing (locRing P W')], M = semiMaxIdeal P 𝒲 W' hW' := by
  classical
  have : Fintype 𝒲 := hfin.fintype
  obtain ⟨W0, hW0⟩ := hne
  let f : 𝒲 → Ideal (semiLocRing P 𝒲) := fun W =>
    have := (h𝒲 W W.2).1.1
    have := isLocalRing (h𝒲 W W.2).2
    semiMaxIdeal P 𝒲 W W.2
  have hcov : (M : Set (semiLocRing P 𝒲)) ⊆ ⋃ i ∈ ((Finset.univ : Finset 𝒲) : Set 𝒲), (f i : Set _) := by
    intro b hbM
    obtain ⟨u, w, a, hu, hw, hwP, hwW, hb⟩ := exists_frac P 𝒲 (fun W hW => (h𝒲 W hW).1.1) b
    by_contra hnot
    have huW : ∀ W ∈ 𝒲, u ∉ W := by
      intro W hW huW
      have := (h𝒲 W hW).1.1
      have := isLocalRing (h𝒲 W hW).2
      refine hnot (Set.mem_biUnion (x := (⟨W, hW⟩ : 𝒲)) (Finset.mem_coe.mpr (Finset.mem_univ _)) ?_)
      exact (mem_semiMaxIdeal_iff P 𝒲 hW (h𝒲 W hW).2 b hu hw (hwW W hW) hb).mpr huW
    have huP : u ∉ P := fun h => huW W0 hW0 ((h𝒲 W0 hW0).2 h)
    exact hM.ne_top (Ideal.eq_top_of_isUnit_mem _ hbM (isUnit_of P 𝒲 b hu hw huP huW hb))
  obtain ⟨⟨W', hW'⟩, -, hle⟩ := (Ideal.subset_union_prime (⟨W0, hW0⟩ : 𝒲) (⟨W0, hW0⟩ : 𝒲)
    (fun i _ _ _ => by dsimp only [f]; infer_instance)).mp hcov
  refine ⟨W', hW', ?_⟩
  intro _
  have := (h𝒲 W' hW').1.1
  exact hM.eq_of_le (Ideal.IsPrime.ne_top inferInstance) hle

end SemilocMaxIdeals

open SemilocMaxIdeals regularityLocalFlat_holds in

theorem SemilocMaxIdeals.proof (hFin : FibreOverFinite.Statement) (hInc : FibreIncomp.Statement)
    (hInt : SemilocIntegral.Statement) (hDim : LocRingDimOne.Statement) : SemilocMaxIdeals.Statement := by
  intro K _ ι _ K' _ ι' _ κ v P' n s α W hv hP' hZ hs hsP hW
  have := hP'.2.1.1
  have hfin := hFin K ι K' ι' κ v P' n s α W hv hP' hZ hs hsP hW
  have h𝒲 : ∀ W' ∈ fibreOver v P' W, IsMultiProjPrime W' ∧ P' ≤ W' := fun W' h => ⟨h.1, h.2.1⟩
  have hcov : ∀ M : Ideal (semiLocRing P' (fibreOver v P' W)), M.IsMaximal →
      ∃ (W' : Ideal (MRing ι')) (hW' : W' ∈ fibreOver v P' W), ∀ [IsLocalRing (locRing P' W')],
        M = semiMaxIdeal P' (fibreOver v P' W) W' hW' := by
    intro M hM
    rcases (fibreOver v P' W).eq_empty_or_nonempty with he | hne
    · exfalso
      have hfield : IsField (semiLocRing P' (fibreOver v P' W)) := by
        refine ⟨⟨0, 1, fun h => zero_ne_one (congrArg Subtype.val h)⟩, mul_comm, fun {b} hb0 => ?_⟩
        obtain ⟨u, w, a, hu, hw, hwP, hwW, hb⟩ := exists_frac P' _ (fun W' h => (h𝒲 W' h).1.1) b
        have huP : u ∉ P' := by
          intro huP
          rw [(fracHom_eq_zero_iff (P := P')).mpr huP] at hb
          exact hb0 (Subtype.ext ((mul_eq_zero.mp hb).resolve_right (fracHom_ne_zero P' hwP)))
        exact (isUnit_of P' _ b hu hw huP (by simp [he]) hb).exists_right_inv
      have := imageZ_isPrime_of_prime v P'
      let := (locToSemiloc hv P' W).toAlgebra
      have := hInt K ι K' ι' κ v P' n s α W hv hP' hZ hs hsP hW
      have hinj : Function.Injective (algebraMap (locRing (imageZ v P') W) (semiLocRing P' (fibreOver v P' W))) := by
        intro x y hxy
        have := congrArg Subtype.val hxy
        rw [RingHom.algebraMap_toAlgebra, locToSemiloc_coe, locToSemiloc_coe] at this
        exact Subtype.ext ((fracMapZ v P').injective this)
      have hd := (hDim K ι (imageZ v P') s α W hZ.2.1 hs hsP hW).2.2
      rw [ringKrullDim_eq_zero_of_isField (isField_of_isIntegral_of_isField hinj hfield)] at hd
      exact zero_ne_one hd
    · exact exists_eq_of_isMaximal hfin h𝒲 hne M hM
  refine ⟨fun W' hW' _ => ⟨?_, isLocalization (P := P') hfin h𝒲 hW'⟩, ?_, hcov⟩
  swap
  · intro W₁ W₂ h₁ h₂ _ _ he
    have := (h𝒲 W₁ h₁).1.1
    have := (h𝒲 W₂ h₂).1.1
    exact le_antisymm (le_of_semiMaxIdeal_le (P := P') hfin h𝒲 h₁ h₂ he.le)
      (le_of_semiMaxIdeal_le (P := P') hfin h𝒲 h₂ h₁ he.ge)
  have := (h𝒲 W' hW').1.1
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _
    (Ideal.IsPrime.ne_top (semiMaxIdeal.isPrime P' (fibreOver v P' W) W' hW'))
  obtain ⟨W₂, h₂, hM₂⟩ := hcov M hM
  have := (h𝒲 W₂ h₂).1.1
  have := isLocalRing (h𝒲 W₂ h₂).2
  have e : M = semiMaxIdeal P' (fibreOver v P' W) W₂ h₂ := hM₂
  have hW₂ : W' = W₂ := hInc K ι K' ι' κ v P' n s α W hv hP' hZ hs hsP hW W' W₂ hW' h₂
    (le_of_semiMaxIdeal_le hfin h𝒲 hW' h₂ (hle.trans e.le))
  subst hW₂
  rw [e] at hM
  exact hM

end GroundTheory.Heights₂.Heights.Inter
