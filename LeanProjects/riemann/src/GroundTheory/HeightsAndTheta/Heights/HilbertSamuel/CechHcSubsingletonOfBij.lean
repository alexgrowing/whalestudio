import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ImportsTail
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PQuotPartGraded
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.H1VanishGeneratedOfLocalizedSubsingleton
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace H1VanishingDevissage

variable {S : Type} [CommRing S] {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type}
  [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)]
  {M : Type} [AddCommGroup M] [Module (MRingOver S ι) M] [Module S M] [IsScalarTower S (MRingOver S ι) M]

theorem cechHc_subsingleton_iff (𝓜 : (K → ℤ) → Submodule S M) (c : K → ℤ) (n : ℕ) :
    Subsingleton (KH.cechHc ι 𝓜 c n) ↔ KH.cechZc ι 𝓜 c n ≤ KH.cechBc ι 𝓜 c n := by
  show Subsingleton (_ ⧸ _) ↔ _
  rw [Submodule.Quotient.subsingleton_iff, Submodule.comap_subtype_eq_top]

omit [LinearOrder K] [∀ k, LinearOrder (ι k)] in

theorem locPart_shift (𝓜 : (K → ℤ) → Submodule S M) (T : Submonoid (MRingOver S ι)) (c x : K → ℤ) :
    KH.locPart ι (fun d => 𝓜 (d + c)) T x = KH.locPart ι 𝓜 T (x + c) := by
  have h : ∀ a : K → ℕ, x + (fun k => (a k : ℤ)) + c = x + c + fun k => (a k : ℤ) :=
    fun _ => add_right_comm _ _ _
  simp only [KH.locPart, h]

omit [LinearOrder K] [∀ k, LinearOrder (ι k)] in

theorem cechCc_shift (𝓜 : (K → ℤ) → Submodule S M) (c x : K → ℤ) (n : ℕ) :
    KH.cechCc ι (fun d => 𝓜 (d + c)) x n = KH.cechCc ι 𝓜 (x + c) n := by
  simp only [KH.cechCc, locPart_shift]

theorem cechHc_shift_iff (𝓜 : (K → ℤ) → Submodule S M) (c x : K → ℤ) (n : ℕ) :
    Subsingleton (KH.cechHc ι (fun d => 𝓜 (d + c)) x n) ↔ Subsingleton (KH.cechHc ι 𝓜 (x + c) n) := by
  rw [cechHc_subsingleton_iff, cechHc_subsingleton_iff]
  cases n <;> simp only [KH.cechZc, KH.cechBc, cechCc_shift]

omit [LinearOrder K] [∀ k, LinearOrder (ι k)] in

theorem isMGraded_shift {𝓜 : (K → ℤ) → Submodule S M} (h : KH.IsMGraded S ι 𝓜) (c : K → ℤ) :
    KH.IsMGraded S ι (fun d => 𝓜 (d + c)) := by
  refine ⟨?_, fun a d p m hp hm => ?_⟩
  · have h1 := (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top 𝓜).1 h.1
    refine (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).2
      ⟨h1.1.comp (add_left_injective c), ?_⟩
    rw [← h1.2]
    exact (Equiv.addRight c).iSup_comp (g := 𝓜)
  · have := h.2 a (d + c) p m hp hm
    rwa [add_right_comm] at this

theorem cechHc_subsingleton_of_bij (hSES : KH.CechSESStatement)
    {A B : Type} [AddCommGroup A] [Module (MRingOver S ι) A] [Module S A] [IsScalarTower S (MRingOver S ι) A]
    [AddCommGroup B] [Module (MRingOver S ι) B] [Module S B] [IsScalarTower S (MRingOver S ι) B]
    (𝓐 : (K → ℤ) → Submodule S A) (𝓑 : (K → ℤ) → Submodule S B) (g : A →ₗ[MRingOver S ι] B)
    (hA : KH.IsMGraded S ι 𝓐) (hB : KH.IsMGraded S ι 𝓑) (hg : KH.IsMGradedMap S ι 𝓐 𝓑 g)
    (hinj : Function.Injective g) (hsurj : Function.Surjective g) (c : K → ℤ) (n : ℕ)
    (h : Subsingleton (KH.cechHc ι 𝓐 c n)) : Subsingleton (KH.cechHc ι 𝓑 c n) := by
  have hhG : KH.IsMGradedMap S ι 𝓑 (fun _ : K → ℤ => (⊥ : Submodule S PUnit)) 0 :=
    fun _ _ _ => Submodule.zero_mem _
  have hex : LinearMap.range g = LinearMap.ker (0 : B →ₗ[MRingOver S ι] PUnit) := by
    rw [LinearMap.range_eq_top.2 hsurj, LinearMap.ker_zero]
  have hU' : Subsingleton (KH.cechHc ι (fun _ : K → ℤ => (⊥ : Submodule S PUnit)) c n) := by
    have : Subsingleton (KH.CechC S ι PUnit n) :=
      ⟨fun f g => funext fun I => Subsingleton.elim (α := LocalizedModule _ PUnit) _ _⟩
    refine ⟨fun x y => ?_⟩
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    rw [Subsingleton.elim x y]
  exact (hSES S K ι A B PUnit 𝓐 𝓑 _ g 0 hA hB isMGraded_punit hg hhG hinj
    (fun _ => ⟨0, Subsingleton.elim _ _⟩) hex c n).1 h hU'

end H1VanishingDevissage

theorem H1VanishingDevissage.proof (hPF : KH.PrimeFiltStatement) (hSES : KH.CechSESStatement)
    (hGQ : GradedSubquot.Statement) : H1VanishingDevissage.Statement := by
  intro S _ K _ _ ι _ _ V N hS hP M _ _ _ _ 𝓜 hfin hgr hV e
  obtain ⟨r, m, c, 𝔭, hm, h𝔭, hcol, hspan⟩ := hPF S K ι M 𝓜 hS hfin hgr
  let G : ℕ → Set M := fun j => m '' {l | (l : ℕ) < j}
  let F : ℕ → Submodule (MRingOver S ι) M := fun j => Submodule.span _ (G j)
  have hGh : ∀ j, ∀ x ∈ G j, ∃ c', x ∈ 𝓜 c' := by
    rintro j _ ⟨l, -, rfl⟩
    exact ⟨c l, hm l⟩
  have hFmono : ∀ {i j : ℕ}, i ≤ j → F i ≤ F j := fun hij =>
    Submodule.span_mono (Set.image_mono fun l (hl : (l : ℕ) < _) => lt_of_lt_of_le hl hij)
  have hgrF : ∀ j, KH.IsMGraded S ι (subGrading 𝓜 (F j)) := fun j =>
    (hGQ S K ι M 𝓜 (G j) (G j) hgr (hGh j) (hGh j) le_rfl).1
  have key : ∀ j ≤ r, ∃ c₁ : ℕ, ∀ n : ℕ, c₁ ≤ n →
      Subsingleton (KH.cechHc ι (subGrading 𝓜 (F j)) (e + n • N) 1) := by
    intro j
    induction j with
    | zero =>
      intro _
      have hF0 : F 0 = ⊥ := by simp [F, G]
      refine ⟨0, fun n _ => (h1_vanish_generated_of_localized_subsingleton
        (fun _ _ => loc_subsingleton_of_kill (Submonoid.one_mem _) fun y => ?_) _ _).1⟩
      rw [one_smul]
      have hy : (y : M) ∈ (⊥ : Submodule (MRingOver S ι) M) := by
        rw [← hF0]
        exact y.2
      exact Submodule.coe_eq_zero.mp ((Submodule.mem_bot _).1 hy)
    | succ j ih =>
      intro hj
      obtain ⟨c₀, hc₀⟩ := ih (Nat.le_of_succ_le hj)
      let l : Fin r := ⟨j, hj⟩
      let L : Submodule (MRingOver S ι) (F (j + 1)) := (F j).comap (F (j + 1)).subtype
      have hq := (hGQ S K ι M 𝓜 (G j) (G (j + 1)) hgr (hGh j) (hGh (j + 1)) (hFmono (Nat.le_succ j))).2
      have hml : m l ∈ F (j + 1) := Submodule.subset_span ⟨l, Nat.lt_succ_self j, rfl⟩

      let ψ : MRingOver S ι →ₗ[MRingOver S ι] (F (j + 1) ⧸ L) :=
        LinearMap.toSpanSingleton _ _ (L.mkQ ⟨m l, hml⟩)
      have hψ : ∀ p, ψ p = L.mkQ (p • ⟨m l, hml⟩) := fun p => (L.mkQ.map_smul p _).symm
      have hker : ∀ p, ψ p = 0 ↔ p ∈ 𝔭 l := by
        intro p
        rw [hψ, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
        exact hcol l p
      let φ : (MRingOver S ι ⧸ 𝔭 l) →ₗ[MRingOver S ι] (F (j + 1) ⧸ L) :=
        (𝔭 l).liftQ ψ fun p hp => (LinearMap.mem_ker).2 ((hker p).2 hp)
      have hφ : ∀ p, φ (Ideal.Quotient.mk (𝔭 l) p) = ψ p := fun _ => rfl
      have hinj : Function.Injective φ := LinearMap.ker_eq_bot.1
        (Submodule.ker_liftQ_eq_bot _ _ _ fun p hp => (hker p).1 (LinearMap.mem_ker.1 hp))

      have hdec : ∀ y ∈ F (j + 1), ∃ p : MRingOver S ι, y - p • m l ∈ F j := by
        intro y hy
        induction hy using Submodule.span_induction with
        | mem x hx =>
          obtain ⟨l', hl', rfl⟩ := hx
          rcases Nat.lt_succ_iff_lt_or_eq.1 hl' with h | h
          · exact ⟨0, by rw [zero_smul, sub_zero]; exact Submodule.subset_span ⟨l', h, rfl⟩⟩
          · exact ⟨1, by rw [one_smul, show l' = l from Fin.ext h, sub_self]; exact (F j).zero_mem⟩
        | zero => exact ⟨0, by rw [zero_smul, sub_zero]; exact (F j).zero_mem⟩
        | add x y _ _ hx hy =>
          obtain ⟨p, hp⟩ := hx
          obtain ⟨p', hp'⟩ := hy
          refine ⟨p + p', ?_⟩
          have : x + y - (p + p') • m l = (x - p • m l) + (y - p' • m l) := by rw [add_smul]; abel
          rw [this]
          exact (F j).add_mem hp hp'
        | smul a x _ hx =>
          obtain ⟨p, hp⟩ := hx
          refine ⟨a * p, ?_⟩
          rw [mul_smul, ← smul_sub]
          exact (F j).smul_mem a hp
      have hsurj : Function.Surjective φ := by
        intro q
        obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective L q
        obtain ⟨p, hp⟩ := hdec y y.2
        refine ⟨Ideal.Quotient.mk (𝔭 l) p, ?_⟩
        rw [hφ, hψ, Submodule.mkQ_apply, Submodule.Quotient.eq]
        show ((p • ⟨m l, hml⟩ - y : F (j + 1)) : M) ∈ F j
        rw [Submodule.coe_sub, Submodule.coe_smul, ← neg_sub]
        exact (F j).neg_mem hp
      obtain ⟨c₂, hc₂⟩ : ∃ c₂ : ℕ, ∀ n : ℕ, c₂ ≤ n →
          Subsingleton (KH.cechHc ι (quotGrading (subGrading 𝓜 (F (j + 1))) L) (e + n • N) 1) := by
        by_cases hrel : IsMultiProjPrime (𝔭 l)
        ·
          obtain ⟨c₂, hc₂⟩ := hP (𝔭 l) hrel (hV.trans (h𝔭 l).2.2) (e + -c l)
          have hA := isMGraded_shift (QuotPartGraded.proof S K ι (𝔭 l) (h𝔭 l).2.1) (-c l)
          have hG : KH.IsMGradedMap S ι (fun d => KH.quotPart S (𝔭 l) (d + -c l))
              (quotGrading (subGrading 𝓜 (F (j + 1))) L) φ := by
            intro d x hx
            refine (Submodule.span_le (p := (quotGrading (subGrading 𝓜 (F (j + 1))) L d).comap
              (φ.restrictScalars S))).2 ?_ hx
            rintro _ ⟨p, ⟨h0, hp⟩, rfl⟩
            refine ⟨p • ⟨m l, hml⟩, ?_, (hψ p).symm⟩
            have h := hgr.2 _ (c l) p (m l) hp (hm l)
            have hd : c l + (fun k => (((d + -c l) k).toNat : ℤ)) = d := by
              funext k
              have := h0 k
              simp only [Pi.add_apply, Pi.neg_apply] at this ⊢
              rw [Int.toNat_of_nonneg this]
              ring
            rw [hd] at h
            exact h
          refine ⟨c₂, fun n hn => cechHc_subsingleton_of_bij hSES _ _ φ hA hq hG hinj hsurj _ _ ?_⟩
          rw [cechHc_shift_iff, show e + n • N + -c l = e + -c l + n • N by abel]
          exact hc₂ n hn
        · have hirr : ¬ IsRelevant (𝔭 l) := fun h => hrel ⟨(h𝔭 l).1, (h𝔭 l).2.1, h⟩
          simp only [IsRelevant, not_forall, not_exists, not_not] at hirr
          obtain ⟨k, hk⟩ := hirr
          refine ⟨0, fun n _ => (h1_vanish_generated_of_localized_subsingleton (fun _ I => ?_) _ _).1⟩
          obtain ⟨i, hi⟩ := I.2.1 k
          refine loc_subsingleton_of_kill (Submonoid.subset_closure ⟨k, i, hi, rfl⟩) fun y => ?_
          obtain ⟨y, rfl⟩ := hsurj y
          obtain ⟨p', rfl⟩ := Ideal.Quotient.mk_surjective y
          rw [← LinearMap.map_smul, show (X ⟨k, i⟩ : MRingOver S ι) • Ideal.Quotient.mk (𝔭 l) p' =
            Ideal.Quotient.mk (𝔭 l) (X ⟨k, i⟩ * p') from rfl, hφ]
          exact (hker _).2 (Ideal.mul_mem_right _ _ (hk i))
      refine ⟨max c₀ c₂, fun n hn => ?_⟩
      let g := Submodule.inclusion (hFmono (Nat.le_succ j))
      have hex : LinearMap.range g = LinearMap.ker L.mkQ := by
        rw [Submodule.range_inclusion, Submodule.ker_mkQ]
      have hgG : KH.IsMGradedMap S ι (subGrading 𝓜 (F j)) (subGrading 𝓜 (F (j + 1))) g := fun _ _ hx => hx
      have hhG : KH.IsMGradedMap S ι (subGrading 𝓜 (F (j + 1))) (quotGrading (subGrading 𝓜 (F (j + 1))) L)
          L.mkQ := fun _ _ hx => Submodule.mem_map_of_mem hx
      exact (hSES S K ι _ _ _ _ _ _ g L.mkQ (hgrF j) (hgrF (j + 1)) hq hgG hhG
        (Submodule.inclusion_injective _) (Submodule.mkQ_surjective _) hex (e + n • N) 1).1
        (hc₀ n (le_of_max_le_left hn)) (hc₂ n (le_of_max_le_right hn))
  have hFr : F r = ⊤ := by
    rw [← hspan]
    simp [F, G]
  obtain ⟨c₁, hc₁⟩ := key r le_rfl
  exact ⟨c₁, fun n hn => cechHc_subsingleton_of_bij hSES _ 𝓜 (F r).subtype (hgrF r) hgr (fun _ _ hx => hx)
    (Submodule.injective_subtype _) (fun y => ⟨⟨y, hFr ▸ Submodule.mem_top⟩, rfl⟩) _ _ (hc₁ n hn)⟩

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
