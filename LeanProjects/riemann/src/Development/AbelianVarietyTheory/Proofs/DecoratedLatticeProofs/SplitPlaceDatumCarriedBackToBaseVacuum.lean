import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CombAtSingleZero
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceBaseVacuumDatumExistsUnique
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair)

noncomputable section
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.DatumBack

open GlobalTheory.PlaceModel GlobalTheory.PlaceDatum GlobalTheory.FinPl.OverProof GlobalTheory.FinPl.LatMem

theorem ind_nsmul_mem_of_ne_zero {G : Type} [AddCommGroup G] {χ : G → G → ℂ} {X Y L L' : AddSubgroup G}
    (M : Submodule ℂ (G → ℂ)) (h : IsBichar χ) (hL : L ≤ X) (hL' : L' ≤ Y) (hLL' : ∀ u ∈ L, ∀ y ∈ L', χ u y = 1)
    (hX : ∀ x ∈ X, (∀ y ∈ L', χ x y = 1) → x ∈ L)
    (dX : ∀ k : ℕ, 0 < k → ∀ x ∈ X, ∃ x' ∈ X, k • x' = x) (dY : ∀ k : ℕ, 0 < k → ∀ y ∈ Y, ∃ y' ∈ Y, k • y' = y)
    (tf : ∀ k : ℕ, 0 < k → Function.Injective fun t : G => k • t)
    (hfin : ∀ k : ℕ, 0 < k → ∃ R : Set G, R.Finite ∧ ∀ t ∈ L, ∃ r ∈ R, ∃ u ∈ L, t = r + k • u)
    (hMX : ∀ Θ ∈ M, ∀ x ∈ X, (fun t => Θ (t + x)) ∈ M) (hMY : ∀ Θ ∈ M, ∀ y ∈ Y, (fun t => χ t y * Θ t) ∈ M)
    (Φ : G → ℂ) (hΦ : Φ ∈ M) (h1 : ∀ t, Φ t ≠ 0 → t ∈ X) (k : ℕ) (hk : 0 < k)
    (h2 : ∀ u ∈ L, ∀ t, Φ (t + k • u) = Φ t) (h3 : ∀ t, Φ t ≠ 0 → k • t ∈ L) (h0 : Φ ≠ 0) :
    ind (L.map (nsmulAddMonoidHom k)) ∈ M := by
  classical
  set K := L.map (nsmulAddMonoidHom k) with hKdef
  have hKL : K ≤ L := by
    rintro _ ⟨u, hu, rfl⟩
    exact nsmul_mem hu k
  obtain ⟨t₀, ht₀⟩ : ∃ t₀, Φ t₀ ≠ 0 := by
    by_contra hh
    push_neg at hh
    exact h0 (funext hh)
  set Φ₁ : G → ℂ := fun t => Φ (t + t₀) with hΦ₁
  have hM1 : Φ₁ ∈ M := hMX Φ hΦ t₀ (h1 t₀ ht₀)
  have hkt₀ := h3 t₀ ht₀
  have s2 : ∀ u ∈ K, ∀ t, Φ₁ (t + u) = Φ₁ t := by
    rintro _ ⟨u₀, hu₀, rfl⟩ t
    simp only [hΦ₁]
    rw [add_right_comm]
    exact h2 u₀ hu₀ _
  have s3 : ∀ t, Φ₁ t ≠ 0 → k • t ∈ L := by
    intro t ht
    have := sub_mem (h3 _ ht) hkt₀
    rwa [nsmul_add, add_sub_cancel_right] at this
  obtain ⟨R2, hR2, hR2'⟩ := hfin (k * k) (Nat.mul_pos hk hk)
  have hP : ((fun t : G => k • t) ⁻¹' R2).Finite := hR2.preimage (tf k hk).injOn
  have key : ∀ R : Finset G, ∃ Θ ∈ M, (∀ t ∈ K, Θ t = Φ₁ t) ∧ (∀ t, Φ₁ t = 0 → Θ t = 0) ∧
      ∀ r ∈ R, k • r ∈ L → r ∉ K → ∀ u ∈ K, Θ (r + u) = 0 := by
    intro R
    induction R using Finset.induction_on with
    | empty => exact ⟨Φ₁, hM1, fun _ _ => rfl, fun _ hh => hh, by simp⟩
    | insert r R _ ih =>
      obtain ⟨Θ, hΘ, g1, g2, g3⟩ := ih
      by_cases hr : k • r ∈ L ∧ r ∉ K
      · have hrX : r ∈ X := by
          obtain ⟨x', hx', hx'e⟩ := dX k hk _ (hL hr.1)
          rw [← tf k hk hx'e]
          exact hx'
        obtain ⟨r', hr', rfl⟩ := dX k hk r hrX
        have hr'L : r' ∉ L := fun hh => hr.2 ⟨r', hh, rfl⟩
        have : ¬ ∀ y ∈ L', χ r' y = 1 := fun hh => hr'L (hX r' hr' hh)
        push_neg at this
        obtain ⟨y, hy, hne⟩ := this
        obtain ⟨y', hy', rfl⟩ := dY k hk y (hL' hy)
        rw [← h.nsmul] at hne
        have hK1 : ∀ u ∈ K, χ u y' = 1 := by
          rintro _ ⟨u, hu, rfl⟩
          exact (h.nsmul k u y').trans (hLL' u hu _ hy)
        have hne' : χ (k • r') y' - 1 ≠ 0 := sub_ne_zero.2 hne
        refine ⟨(χ (k • r') y' - 1)⁻¹ • (χ (k • r') y' • Θ - fun t => χ t y' * Θ t),
          M.smul_mem _ (sub_mem (M.smul_mem _ hΘ) (hMY Θ hΘ y' hy')), fun t ht => ?_, fun t ht => ?_,
          fun s hs hsL hsK u hu => ?_⟩
        · show (χ (k • r') y' - 1)⁻¹ * (χ (k • r') y' * Θ t - χ t y' * Θ t) = Φ₁ t
          rw [hK1 t ht, g1 t ht, one_mul,
            show χ (k • r') y' * Φ₁ t - Φ₁ t = (χ (k • r') y' - 1) * Φ₁ t by ring, ← mul_assoc,
            inv_mul_cancel₀ hne', one_mul]
        · show (χ (k • r') y' - 1)⁻¹ * (χ (k • r') y' * Θ t - χ t y' * Θ t) = 0
          rw [g2 t ht, mul_zero, mul_zero, sub_zero, mul_zero]
        · show (χ (k • r') y' - 1)⁻¹ * (χ (k • r') y' * Θ (s + u) - χ (s + u) y' * Θ (s + u)) = 0
          rcases Finset.mem_insert.1 hs with rfl | hs
          · rw [h.left, hK1 u hu, mul_one, sub_self, mul_zero]
          · rw [g3 s hs hsL hsK u hu, mul_zero, mul_zero, sub_zero, mul_zero]
      · refine ⟨Θ, hΘ, g1, g2, fun s hs hsL hsK u hu => ?_⟩
        rcases Finset.mem_insert.1 hs with rfl | hs
        · exact absurd ⟨hsL, hsK⟩ hr
        · exact g3 s hs hsL hsK u hu
  obtain ⟨Θ, hΘ, g1, g2, g3⟩ := key hP.toFinset
  have hΘeq : Θ = Φ t₀ • ind K := by
    funext t
    by_cases ht : t ∈ K
    · have e0 := s2 t ht 0
      rw [zero_add] at e0
      rw [g1 t ht, e0]
      simp [ind, ht, hΦ₁]
    · simp only [Pi.smul_apply, ind, if_neg ht, smul_zero]
      by_contra hne
      have hΦt : Φ₁ t ≠ 0 := fun hh => hne (g2 t hh)
      have hkt := s3 t hΦt
      obtain ⟨r, hr, u, hu, hre⟩ := hR2' _ hkt
      have huK : k • u ∈ K := ⟨u, hu, rfl⟩
      have hs : t - k • u ∈ (fun t : G => k • t) ⁻¹' R2 := by
        change k • (t - k • u) ∈ R2
        rwa [nsmul_sub, hre, smul_smul, add_sub_cancel_right]
      have hsL : k • (t - k • u) ∈ L := by
        rw [nsmul_sub]
        exact sub_mem hkt (nsmul_mem (hKL huK) k)
      have hsK : t - k • u ∉ K := fun hh => ht (by simpa using add_mem hh huK)
      have := g3 _ (hP.mem_toFinset.2 hs) hsL hsK _ huK
      rw [sub_add_cancel] at this
      exact hne this
  have hI : ind K = (Φ t₀)⁻¹ • Θ := by rw [hΘeq, smul_smul, inv_mul_cancel₀ ht₀, one_smul]
  rw [hI]
  exact M.smul_mem _ hΘ

theorem mem_of_cosets {G : Type} [AddCommGroup G] {X K : AddSubgroup G} (M : Submodule ℂ (G → ℂ))
    (hMX : ∀ Θ ∈ M, ∀ x ∈ X, (fun t => Θ (t + x)) ∈ M) (hK : ind K ∈ M) (P : Finset G) :
    ∀ Φ : G → ℂ, (∀ t, Φ t ≠ 0 → t ∈ X) → (∀ u ∈ K, ∀ t, Φ (t + u) = Φ t) →
      (∀ t, Φ t ≠ 0 → ∃ s ∈ P, ∃ u ∈ K, t = s + u) → Φ ∈ M := by
  classical
  induction P using Finset.induction_on with
  | empty =>
    intro Φ _ _ h3
    convert M.zero_mem using 1
    funext t
    by_contra ht
    simpa using h3 t ht
  | insert s P _ ih =>
    intro Φ h1 h2 h3
    by_cases hs : Φ s = 0
    · refine ih Φ h1 h2 fun t ht => ?_
      obtain ⟨s', hs', u, hu, rfl⟩ := h3 t ht
      rcases Finset.mem_insert.1 hs' with rfl | hs'
      · exact absurd ((h2 u hu _).trans hs) ht
      · exact ⟨s', hs', u, hu, rfl⟩
    · have hsX := h1 s hs
      have hm := M.smul_mem (Φ s) (hMX _ hK _ (neg_mem hsX))
      have hval : ∀ t, (Φ - Φ s • fun t => ind K (t + -s)) t ≠ 0 → Φ t ≠ 0 ∧ t + -s ∉ K := by
        intro t ht
        have hn : t + -s ∉ K := fun hh => ht (by
          have := h2 _ hh s
          rw [show s + (t + -s) = t by abel] at this
          simp [ind, hh, this])
        exact ⟨by simpa [ind, hn] using ht, hn⟩
      have := ih (Φ - Φ s • fun t => ind K (t + -s)) (fun t ht => h1 t (hval t ht).1) (fun u hu t => by
        simp only [Pi.sub_apply, Pi.smul_apply, h2 u hu]
        rw [add_right_comm, ind_add K _ hu]) fun t ht => by
          obtain ⟨s', hs', u, hu, rfl⟩ := h3 t (hval t ht).1
          rcases Finset.mem_insert.1 hs' with rfl | hs'
          · exact absurd (by simpa using hu) (hval _ ht).2
          · exact ⟨s', hs', u, hu, rfl⟩
      simpa using add_mem this hm

theorem ind_mem_of_ind_nsmul {G : Type} [AddCommGroup G] {X L : AddSubgroup G} (M : Submodule ℂ (G → ℂ)) (hL : L ≤ X)
    (hMX : ∀ Θ ∈ M, ∀ x ∈ X, (fun t => Θ (t + x)) ∈ M) (k : ℕ)
    (hfin : ∃ R : Set G, R.Finite ∧ ∀ t ∈ L, ∃ r ∈ R, ∃ u ∈ L, t = r + k • u)
    (hK : ind (L.map (nsmulAddMonoidHom k)) ∈ M) : ind L ∈ M := by
  obtain ⟨R, hR, hR'⟩ := hfin
  have hKL : L.map (nsmulAddMonoidHom k) ≤ L := by
    rintro _ ⟨u, hu, rfl⟩
    exact nsmul_mem hu k
  refine mem_of_cosets M hMX hK hR.toFinset (ind L) (fun t ht => hL ?_) (fun u hu t => ind_add L t (hKL hu))
    fun t ht => ?_
  · by_contra h; exact ht (by simp [ind, h])
  · have htL : t ∈ L := by by_contra h; exact ht (by simp [ind, h])
    obtain ⟨r, hr, u, hu, rfl⟩ := hR' t htL
    exact ⟨r, hR.mem_toFinset.2 hr, k • u, ⟨u, hu, rfl⟩, rfl⟩

theorem isSBHalf_zero' {D : D7} {S T : HSp D} (e : AE D) (Λ : AddSubgroup (WO S T)) : IsSBHalf e Λ (0 : WO S T → ℂ) :=
  ⟨fun t h => absurd rfl h, 1, one_pos, fun _ _ _ _ => rfl, fun t h => absurd rfl h⟩

theorem isHalf_nsmul' {D : D7} {m n : ℕ} {e : AE D} {u : Mx D m n} (hu : IsHalf e u) (N : ℕ) : IsHalf e (N • u) :=
  fun i j => by rw [Matrix.smul_apply, nsmul_eq_mul, mul_left_comm, hu i j]

theorem isSBHalf_add' {D : D7} {S T : HSp D} {e : AE D} {Λ : AddSubgroup (WO S T)} {f g : WO S T → ℂ}
    (hf : IsSBHalf e Λ f) (hg : IsSBHalf e Λ g) : IsSBHalf e Λ (f + g) := by
  obtain ⟨f1, a, ha, f2, f3⟩ := hf
  obtain ⟨g1, b, hb, g2, g3⟩ := hg
  refine ⟨fun t ht => ?_, a * b, Nat.mul_pos ha hb, fun u hu hh t => ?_, fun t ht => ?_⟩
  · by_cases h : f t = 0
    · exact g1 t (by simpa [h] using ht)
    · exact f1 t h
  · have e1 : (a * b) • u = a • (b • u) := (smul_smul a b u).symm
    have e2 : (a * b) • u = b • (a • u) := by rw [smul_smul, mul_comm]
    simp only [Pi.add_apply]
    rw [e1, f2 _ (nsmul_mem hu b) (isHalf_nsmul' hh b), ← e1, e2, g2 _ (nsmul_mem hu a) (isHalf_nsmul' hh a)]
  · have e1 : (a * b) • t = b • (a • t) := by rw [smul_smul, mul_comm]
    have e2 : (a * b) • t = a • (b • t) := (smul_smul a b t).symm
    by_cases h : f t = 0
    · rw [e2]; exact nsmul_mem (g3 t (by simpa [h] using ht)) a
    · rw [e1]; exact nsmul_mem (f3 t h) b

theorem isSBHalf_smul' {D : D7} {S T : HSp D} {e : AE D} {Λ : AddSubgroup (WO S T)} (c : ℂ) {f : WO S T → ℂ}
    (hf : IsSBHalf e Λ f) : IsSBHalf e Λ (c • f) := by
  obtain ⟨f1, a, ha, f2, f3⟩ := hf
  refine ⟨fun t ht => f1 t (right_ne_zero_of_mul ht), a, ha, fun u hu hh t => ?_, fun t ht => f3 t (right_ne_zero_of_mul ht)⟩
  simp only [Pi.smul_apply, smul_eq_mul, f2 u hu hh t]

theorem isSBHalf_of_mem_waveSpan {D : D7} {S T : HSp D} (ψ : AddChar (AF D.host.F) ℂ) (e : AE D) (Λ : AddSubgroup (WO S T))
    (hLL' : ∀ u ∈ Λ ⊓ half S T e, ∀ y ∈ Λ ⊓ half S T (cA D e), ψ (symplO S T u y) = 1)
    (hdX : ∀ x ∈ half S T e, ∃ k : ℕ, 0 < k ∧ k • x ∈ Λ)
    (hdY : ∀ y ∈ half S T (cA D e), ∃ k : ℕ, 0 < k ∧ k • y ∈ Λ) :
    ∀ Θ ∈ waveSpan (fun x y : WO S T => ψ (symplO S T x y)) (half S T e) (half S T (cA D e)) (Λ ⊓ half S T e),
      IsSBHalf e Λ Θ := by
  have hb := isBichar_symplO S T ψ
  intro Θ hΘ
  induction hΘ using Submodule.span_induction with
  | mem _ hh =>
    obtain ⟨x, hx, y, hy, rfl⟩ := hh
    obtain ⟨kx, hkx, hxΛ⟩ := hdX x hx
    obtain ⟨ky, hky, hyΛ⟩ := hdY y hy
    have hyL : ky • y ∈ Λ ⊓ half S T (cA D e) := ⟨hyΛ, nsmul_mem hy ky⟩
    refine ⟨fun t ht => ?_, ky * kx, Nat.mul_pos hky hkx, fun u hu hh t => ?_, fun t ht => ?_⟩
    · have h1 : t + x ∈ Λ ⊓ half S T e := by by_contra h; exact ht (by simp [wave, ind, h])
      have : t ∈ half S T e := by simpa using sub_mem (AddSubgroup.mem_inf.1 h1).2 hx
      exact (isHalf_iff S T).2 this
    · have huL : kx • u ∈ Λ ⊓ half S T e := ⟨nsmul_mem hu kx, nsmul_mem ((isHalf_iff S T).1 hh) kx⟩
      have hK : (ky * kx) • u ∈ Λ ⊓ half S T e := by rw [← smul_smul]; exact nsmul_mem huL ky
      have hχ : ψ (symplO S T ((ky * kx) • u) y) = 1 := by
        rw [← smul_smul, hb.nsmul]; exact hLL' _ huL _ hyL
      simp only [wave]
      rw [show t + (ky * kx) • u + x = t + x + (ky * kx) • u by abel, ind_add _ _ hK, hb.left, hχ, mul_one]
    · have h1 : t + x ∈ Λ ⊓ half S T e := by by_contra h; exact ht (by simp [wave, ind, h])
      have hx' : (ky * kx) • x ∈ Λ := by rw [← smul_smul]; exact nsmul_mem hxΛ ky
      have := sub_mem (nsmul_mem (AddSubgroup.mem_inf.1 h1).1 (ky * kx)) hx'
      rwa [nsmul_add, add_sub_cancel_right] at this
  | zero => exact isSBHalf_zero' e Λ
  | add f g _ _ hf hg => exact isSBHalf_add' hf hg
  | smul c f _ hf => exact isSBHalf_smul' c hf

variable {D : D7} {S T : HSp D}

theorem comb_eq_lc (ψ : AddChar (AF D.host.F) ℂ) (c : WO S T →₀ ℂ) (f : WO S T → ℂ) :
    comb ψ S T c f = Finsupp.linearCombination ℂ (fun u => heisO ψ S T u f) c := by
  rw [Finsupp.linearCombination_apply, Finsupp.sum]; rfl

theorem heisO_zero_left (ψ : AddChar (AF D.host.F) ℂ) (f : WO S T → ℂ) : heisO ψ S T 0 f = f := by
  funext t; simp [heisO, symplOH, symplO_zero_right]

theorem heisO_comb (ψ : AddChar (AF D.host.F) ℂ) (x : WO S T) (c : WO S T →₀ ℂ) (g : WO S T → ℂ) :
    heisO ψ S T x (comb ψ S T c g) =
      comb ψ S T (c.sum fun u a => Finsupp.single (x + u) (a * ψ (symplOH S T x u))) g := by
  rw [comb_eq_lc, comb_eq_lc, map_finsuppSum]
  change heisL S T ψ x (Finsupp.linearCombination ℂ _ c) = _
  rw [Finsupp.linearCombination_apply, map_finsuppSum]
  refine Finsupp.sum_congr fun u _ => ?_
  rw [Finsupp.linearCombination_single, LinearMap.map_smul]
  change c u • heisL S T ψ x (heisL S T ψ u g) = _
  rw [heisL_heisL, smul_smul]
  rfl

theorem half_le_sum {e : AE D} (he : cA D e * e = 0) : half S T e ≤ half S T (e + cA D e) := fun u hu => by
  rw [mem_half] at hu ⊢
  have h0 : cA D e • u = 0 := by rw [← hu, smul_smul, he, zero_smul]
  rw [add_smul, hu, h0, add_zero]

theorem half_le_sum' {e : AE D} (he : e * cA D e = 0) : half S T (cA D e) ≤ half S T (e + cA D e) := fun u hu => by
  rw [mem_half] at hu ⊢
  have h0 : e • u = 0 := by rw [← hu, smul_smul, he, zero_smul]
  rw [add_smul, hu, h0, zero_add]

def reach (ψ : AddChar (AF D.host.F) ℂ) (e : AE D) (Λ : AddSubgroup (WO S T)) (Φ : WO S T → ℂ) :
    Submodule ℂ (WO S T → ℂ) where
  carrier := {Θ | Θ ∈ waveSpan (fun x y : WO S T => ψ (symplO S T x y)) (half S T e) (half S T (cA D e))
      (Λ ⊓ half S T e) ∧ ∃ c : WO S T →₀ ℂ, (∀ u ∈ c.support, u ∈ half S T (e + cA D e)) ∧
      ∀ f₀ Tm, IsPlaceModel ψ (symplO S T) (heisO ψ S T) e Λ 1 f₀ Tm → Tm Θ = comb ψ S T c (Tm Φ)}
  add_mem' {a b} ha hb := by
    classical
    obtain ⟨ha1, c, hc, hc'⟩ := ha
    obtain ⟨hb1, d, hd, hd'⟩ := hb
    refine ⟨add_mem ha1 hb1, c + d, fun u hu => ?_, fun f₀ Tm hT => ?_⟩
    · rcases Finset.mem_union.1 (Finsupp.support_add hu) with h | h
      · exact hc u h
      · exact hd u h
    · rw [map_add, hc' f₀ Tm hT, hd' f₀ Tm hT, comb_eq_lc, comb_eq_lc, comb_eq_lc, map_add]
  zero_mem' := ⟨zero_mem _, 0, by simp, fun f₀ Tm _ => by rw [map_zero, comb_eq_lc, map_zero]⟩
  smul_mem' a b hb := by
    obtain ⟨hb1, d, hd, hd'⟩ := hb
    refine ⟨Submodule.smul_mem _ a hb1, a • d, fun u hu => hd u (Finsupp.support_smul hu), fun f₀ Tm hT => ?_⟩
    rw [map_smul, hd' f₀ Tm hT, comb_eq_lc, comb_eq_lc, map_smul]

theorem mem_reach {ψ : AddChar (AF D.host.F) ℂ} {e : AE D} {Λ : AddSubgroup (WO S T)} {Φ Θ : WO S T → ℂ} :
    Θ ∈ reach ψ e Λ Φ ↔ Θ ∈ waveSpan (fun x y : WO S T => ψ (symplO S T x y)) (half S T e) (half S T (cA D e))
      (Λ ⊓ half S T e) ∧ ∃ c : WO S T →₀ ℂ, (∀ u ∈ c.support, u ∈ half S T (e + cA D e)) ∧
      ∀ f₀ Tm, IsPlaceModel ψ (symplO S T) (heisO ψ S T) e Λ 1 f₀ Tm → Tm Θ = comb ψ S T c (Tm Φ) := Iff.rfl

theorem support_shift {c : WO S T →₀ ℂ} {x : WO S T} {φ : WO S T → ℂ} {H : AddSubgroup (WO S T)} (hx : x ∈ H)
    (hc : ∀ u ∈ c.support, u ∈ H) : ∀ u ∈ (c.sum fun u a => Finsupp.single (x + u) (a * φ u)).support, u ∈ H := by
  classical
  intro u hu
  obtain ⟨w, hw, hu'⟩ := Finset.mem_biUnion.1 (Finsupp.support_sum hu)
  rw [Finset.mem_singleton.1 (Finsupp.support_single_subset hu')]
  exact add_mem hx (hc w hw)

theorem reach_trans {ψ : AddChar (AF D.host.F) ℂ} {e : AE D} {Λ : AddSubgroup (WO S T)} {Φ : WO S T → ℂ}
    (he : cA D e * e = 0)
    (hsb : ∀ Θ ∈ waveSpan (fun x y : WO S T => ψ (symplO S T x y)) (half S T e) (half S T (cA D e))
      (Λ ⊓ half S T e), IsSBHalf e Λ Θ) :
    ∀ Θ ∈ reach ψ e Λ Φ, ∀ x ∈ half S T e, (fun t => Θ (t + x)) ∈ reach ψ e Λ Φ := by
  intro Θ hΘ x hx
  obtain ⟨h1, c, hc, hc'⟩ := mem_reach.1 hΘ
  refine mem_reach.2 ⟨trans_mem h1 hx, _, support_shift (φ := fun u => ψ (symplOH S T x u)) (half_le_sum he hx) hc, fun f₀ Tm hT => ?_⟩
  rw [hT.trans Θ (hsb Θ h1) x ((isHalf_iff S T).2 hx), hc' f₀ Tm hT, heisO_comb]

theorem reach_modul {ψ : AddChar (AF D.host.F) ℂ} {e : AE D} {Λ : AddSubgroup (WO S T)} {Φ : WO S T → ℂ}
    (he : e * cA D e = 0)
    (hsb : ∀ Θ ∈ waveSpan (fun x y : WO S T => ψ (symplO S T x y)) (half S T e) (half S T (cA D e))
      (Λ ⊓ half S T e), IsSBHalf e Λ Θ) :
    ∀ Θ ∈ reach ψ e Λ Φ, ∀ y ∈ half S T (cA D e), (fun t => ψ (symplO S T t y) * Θ t) ∈ reach ψ e Λ Φ := by
  intro Θ hΘ y hy
  obtain ⟨h1, c, hc, hc'⟩ := mem_reach.1 hΘ
  refine mem_reach.2 ⟨modul_mem (isBichar_symplO S T ψ) h1 hy, _, support_shift (φ := fun u => ψ (symplOH S T y u)) (half_le_sum' he hy) hc, fun f₀ Tm hT => ?_⟩
  rw [hT.modul Θ (hsb Θ h1) y ((isHalf_iff S T).2 hy), hc' f₀ Tm hT, heisO_comb]

theorem exists_back (ψ : AddChar (AF D.host.F) ℂ) {e : AE D} (hec : e * cA D e = 0) (Λ : AddSubgroup (WO S T))
    (hLL' : ∀ u ∈ Λ ⊓ half S T e, ∀ y ∈ Λ ⊓ half S T (cA D e), ψ (symplO S T u y) = 1)
    (hX : ∀ x ∈ half S T e, (∀ y ∈ Λ ⊓ half S T (cA D e), ψ (symplO S T x y) = 1) → x ∈ Λ ⊓ half S T e)
    (hfin : ∀ k : ℕ, 0 < k → ∃ R : Set (WO S T), R.Finite ∧
      ∀ t ∈ Λ ⊓ half S T e, ∃ r ∈ R, ∃ u ∈ Λ ⊓ half S T e, t = r + k • u)
    (hdX : ∀ x ∈ half S T e, ∃ k : ℕ, 0 < k ∧ k • x ∈ Λ) (hdY : ∀ y ∈ half S T (cA D e), ∃ k : ℕ, 0 < k ∧ k • y ∈ Λ)
    {Φ : WO S T → ℂ} (hΦ : IsSBHalf e Λ Φ) (h0 : Φ ≠ 0) :
    ∃ c : WO S T →₀ ℂ, (∀ u ∈ c.support, u ∈ half S T (e + cA D e)) ∧
      ∀ f₀ Tm, IsPlaceModel ψ (symplO S T) (heisO ψ S T) e Λ 1 f₀ Tm → Tm (halfInd e Λ) = comb ψ S T c (Tm Φ) := by
  have tf : ∀ k : ℕ, 0 < k → Function.Injective fun t : WO S T => k • t := fun k hk a b hab => by
    rw [← inv_smul_nsmul S T hk a, ← inv_smul_nsmul S T hk b]
    exact congrArg _ hab
  have hb := isBichar_symplO S T ψ
  have hce : cA D e * e = 0 := by rw [mul_comm, hec]
  have hsb := isSBHalf_of_mem_waveSpan ψ e Λ hLL' hdX hdY
  obtain ⟨h1, k, hk, h2, h3⟩ := hΦ
  have hW : Φ ∈ waveSpan (fun x y : WO S T => ψ (symplO S T x y)) (half S T e) (half S T (cA D e))
      (Λ ⊓ half S T e) :=
    mem_waveSpan hb inf_le_right inf_le_right hLL' hX (half_div S T e) (half_div S T _) tf hfin Φ
      (fun t ht => (isHalf_iff S T).1 (h1 t ht)) k hk (fun u hu => h2 u hu.1 ((isHalf_iff S T).2 hu.2))
      fun t ht => ⟨h3 t ht, (half S T e).nsmul_mem ((isHalf_iff S T).1 (h1 t ht)) _⟩
  have hM : Φ ∈ reach ψ e Λ Φ := mem_reach.2 ⟨hW, Finsupp.single 0 1, fun u hu => by
    classical
    rw [Finset.mem_singleton.1 (Finsupp.support_single_subset hu)]; exact zero_mem _, fun f₀ Tm _ => by
    rw [comb_eq_lc, Finsupp.linearCombination_single, one_smul, heisO_zero_left]⟩
  have hK := ind_nsmul_mem_of_ne_zero (reach ψ e Λ Φ) hb inf_le_right inf_le_right hLL' hX (half_div S T e) (half_div S T _) tf hfin
    (reach_trans hce hsb) (reach_modul hec hsb) Φ hM (fun t ht => (isHalf_iff S T).1 (h1 t ht)) k hk
    (fun u hu => h2 u hu.1 ((isHalf_iff S T).2 hu.2))
    (fun t ht => ⟨h3 t ht, (half S T e).nsmul_mem ((isHalf_iff S T).1 (h1 t ht)) _⟩) h0
  have hL := ind_mem_of_ind_nsmul (reach ψ e Λ Φ) inf_le_right (reach_trans hce hsb) k (hfin k hk) hK
  rw [← halfInd_eq_ind] at hL
  exact (mem_reach.1 hL).2

theorem mxAt_of_half {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : SplitPt D k) {u : WO S T} (hu : u ∈ half S T (p.e + cA D p.e)) : MxAt (· = p.v) u := by
  obtain ⟨ε, ⟨β, rfl, -, h0⟩, heq⟩ := p.above
  have hm : algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 β) ∈ idAt D (· = p.v) := tmul_mem_idAt h0 1
  intro i j
  rw [← (isHalf_iff S T).2 hu i j, heq]
  exact Ideal.mul_mem_right _ _ hm

theorem datumBack : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → p.UnitAA → ∀ (S T : HSp D) (α : Frame p S n') (β : Frame p T n) (LS : Lat S) (LT : Lat T), IsSelfDualC S LS → IsSelfDualC T LT → ∀ (Ψ : Matrix n n' k → ℂ) (c : WO S T →₀ ℂ), CombAt (· = p.v) c → (∀ f₀, Vac ψ S T LS LT (· = p.v) f₀ → Over ψ α β LS LT f₀ Ψ (comb ψ S T c f₀)) → ∃ e : WO S T →₀ ℂ, CombAt (· = p.v) e ∧ ∀ g f, Over ψ α β LS LT g Ψ f → Vac ψ S T LS LT (· = p.v) (comb ψ S T e f) ∧ comb ψ S T c (comb ψ S T e f) = f := by
  intro D k _ _ _ _ p n n' _ _ _ _ ψ hψ _ S T α β LS LT hS hT Ψ c _ hc
  obtain ⟨ε, hε, heq⟩ := p.above
  have hs := p.split
  have he := hs.1
  have hec := hs.2.1
  have heε : algebraMap (AF D.host.F) (AE D) ε * p.e = p.e := by rw [← heq]; linear_combination he + hec
  obtain ⟨hLL', hX, -, hfin, hden⟩ := dualPair hψ hS hT hs hε heq
  have hdX : ∀ x ∈ half S T p.e, ∃ k : ℕ, 0 < k ∧ k • x ∈ latO S T (LS : Set _) (LT : Set _) (· = p.v) := by
    intro x hx
    obtain ⟨k, hk, hkx⟩ := exists_nsmul_mem_latO' hS.1 hT.1 x (infPart_half hε heε hx)
    refine ⟨k, hk, ?_⟩
    have := (idem_smul_mem hε he heε hkx).1
    rwa [smul_comm, (mem_half S T).1 hx] at this
  by_cases hΨ : Ψ ∈ SB (Matrix n n' k)
  swap
  · exact ⟨0, fun u hu => by simp at hu, fun g f hf => absurd hf.2.2.2.1 hΨ⟩
  have hΦ := isSBHalf_extFun D k p n n' S T α β LS LT hS hT Ψ hΨ
  by_cases h0 : extFun α β Ψ = 0
  · refine ⟨0, fun u hu => by simp at hu, fun g f hf => ?_⟩
    obtain ⟨Tm, hTm⟩ := hf.2.2.2.2.1
    have hfe : f = Tm (extFun α β Ψ) := hf.2.2.2.2.2 Tm hTm
    rw [h0, map_zero] at hfe
    subst hfe
    have hz : ∀ d : WO S T →₀ ℂ, comb ψ S T d (0 : WO S T → ℂ) = 0 := fun d => by
      simp [comb, heisO_zero_fun]
    rw [hz, hz]
    exact ⟨⟨GlobalTheory.WeilVacMove.isTheta_zero, isLatVac_zero ψ S T _⟩, rfl⟩
  obtain ⟨e, heS, heT⟩ := exists_back ψ hec _ hLL' hX hfin hdX hden hΦ h0
  refine ⟨e, fun u hu => mxAt_of_half p (heS u hu), fun g f hf => ?_⟩
  obtain ⟨Tm, hTm⟩ := hf.2.2.2.2.1
  have hfe : f = Tm (extFun α β Ψ) := hf.2.2.2.2.2 Tm hTm
  have hg : comb ψ S T e f = g := by
    have hv := hTm.vac
    rw [one_smul] at hv
    rw [hfe, ← heT g Tm hTm, hv]
  rw [hg]
  refine ⟨hf.2.2.1, ?_⟩
  rw [hfe]
  exact (hc g hf.2.2.1).2.2.2.2.2 Tm hTm

end GlobalTheory.FinPl.DatumBack

end
