import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsFrameVec
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open AlgebraicGeometry CategoryTheory
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.RootUnit

section Lin

variable {Ω : Type} [Field Ω] {L : Type} [AddCommGroup L] [Module Ω L] {r : ℕ}

theorem exists_coeff_of_mem {c : Fin r → L} {s : Set (Fin r)} {x : L} (h : x ∈ Submodule.span Ω (c '' s)) :
    ∃ f : Fin r → Ω, (∀ j, j ∉ s → f j = 0) ∧ x = ∑ j, f j • c j := by
  obtain ⟨l, hl, rfl⟩ := (Finsupp.mem_span_image_iff_linearCombination Ω).mp h
  refine ⟨l, fun j hj => ?_, ?_⟩
  · by_contra hne
    exact hj (hl (Finsupp.mem_support_iff.mpr hne))
  · rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype]
    intro i
    exact zero_smul _ _

theorem coeff_unique {c : Fin r → L} (hc : LinearIndependent Ω c) {f g : Fin r → Ω}
    (h : ∑ j, f j • c j = ∑ j, g j • c j) (j : Fin r) : f j = g j := by
  have h0 : ∑ j, (f - g) j • c j = 0 := by
    simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib, h, sub_self]
  have := Fintype.linearIndependent_iff.mp hc (f - g) h0 j
  rwa [Pi.sub_apply, sub_eq_zero] at this

theorem flag_change {b c : Fin r → L} {T : Matrix (Fin r) (Fin r) Ω} (hb : LinearIndependent Ω b)
    (hf : ∀ i : ℕ, flagStep Ω b i = flagStep Ω c i) (hT : ∀ i, b i = ∑ j, T i j • c j) :
    LinearIndependent Ω c ∧ ∀ i j, i < j → T i j = 0 := by
  have hr : ∀ v : Fin r → L, flagStep Ω v r = Submodule.span Ω (Set.range v) := by
    intro v
    show Submodule.span Ω (v '' {k : Fin r | (k : ℕ) < r}) = _
    rw [← Set.image_univ]
    congr 2
    ext k
    simp [k.isLt]
  have hc : LinearIndependent Ω c := by
    rw [linearIndependent_iff_card_eq_finrank_span]
    show Fintype.card (Fin r) = Module.finrank Ω (Submodule.span Ω (Set.range c))
    rw [← hr c, ← hf r, hr b, finrank_span_eq_card hb]
  refine ⟨hc, fun i j hij => ?_⟩
  have hmem : b i ∈ Submodule.span Ω (c '' {k : Fin r | (k : ℕ) < (i : ℕ) + 1}) := by
    have h1 : b i ∈ flagStep Ω b ((i : ℕ) + 1) := Submodule.subset_span ⟨i, Nat.lt_succ_self _, rfl⟩
    rw [hf] at h1
    exact h1
  obtain ⟨f, hf0, hfx⟩ := exists_coeff_of_mem hmem
  rw [coeff_unique hc ((hT i).symm.trans hfx) j]
  refine hf0 j (fun hj => ?_)
  have h2 : (i : ℕ) < j := hij
  have h3 : (j : ℕ) < (i : ℕ) + 1 := hj
  omega

theorem span_gr_eq (A : Subring Ω) {b c : Fin r → L} {T : Matrix (Fin r) (Fin r) Ω} (hb : LinearIndependent Ω b)
    (hf : ∀ i : ℕ, flagStep Ω b i = flagStep Ω c i) (hT : ∀ i, b i = ∑ j, T i j • c j) (i : Fin r) :
    Submodule.span A {t : Ω | ∃ e ∈ Submodule.span A (Set.range b), e - t • c i ∈ flagStep Ω c i} =
      Submodule.span A {T i i} := by
  obtain ⟨hc, htri⟩ := flag_change hb hf hT
  have hterm : ∀ (v : Fin r → L) (g : Fin r → Ω), (∀ k, i < k → g k = 0) →
      ∑ k ∈ Finset.univ.erase i, g k • v k ∈ flagStep Ω v i := by
    intro v g hg
    refine Submodule.sum_mem _ fun k hk => ?_
    rcases lt_trichotomy k i with hki | hki | hki
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, hki, rfl⟩)
    · exact absurd hki (Finset.ne_of_mem_erase hk)
    · rw [hg k hki, zero_smul]
      exact Submodule.zero_mem _
  have hbi : b i - T i i • c i ∈ flagStep Ω c i := by
    have := hterm c (fun j => T i j) (fun k hk => htri i k hk)
    rwa [Finset.sum_erase_eq_sub (Finset.mem_univ i), ← hT i] at this
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro t ⟨e, he, het⟩
    obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun A).mp he
    set α : Fin r → Ω := fun k => (a k : Ω) with hα
    have hsum : ∑ k, a k • b k = ∑ k, α k • b k := rfl
    rw [hsum] at het
    have hci : c i ∈ flagStep Ω c ((i : ℕ) + 1) := Submodule.subset_span ⟨i, Nat.lt_succ_self _, rfl⟩
    have hmono : flagStep Ω c i ≤ flagStep Ω c ((i : ℕ) + 1) :=
      Submodule.span_mono (Set.image_mono fun k (hk : (k : ℕ) < i) => Nat.lt_succ_of_lt hk)
    have he1 : ∑ k, α k • b k ∈ Submodule.span Ω (b '' {k : Fin r | (k : ℕ) < (i : ℕ) + 1}) := by
      have h1 : ∑ k, α k • b k ∈ flagStep Ω c ((i : ℕ) + 1) := by
        have := add_mem (hmono het) (Submodule.smul_mem _ t hci)
        rwa [sub_add_cancel] at this
      rw [← hf] at h1
      exact h1
    obtain ⟨f, hf0, hfe⟩ := exists_coeff_of_mem he1
    have hαz : ∀ k, i < k → α k = 0 := by
      intro k hk
      rw [coeff_unique hb hfe k]
      refine hf0 k (fun hk' => ?_)
      have h2 : (i : ℕ) < k := hk
      have h3 : (k : ℕ) < (i : ℕ) + 1 := hk'
      omega
    have hC : ∑ k, α k • b k - α i • b i ∈ flagStep Ω c i := by
      rw [← hf, ← Finset.sum_erase_eq_sub (Finset.mem_univ i)]
      exact hterm b α hαz
    have hE : (α i * T i i - t) • c i ∈ flagStep Ω c i := by
      have heq : (α i * T i i - t) • c i =
          (∑ k, α k • b k - t • c i) - (∑ k, α k • b k - α i • b i) - α i • (b i - T i i • c i) := by
        rw [sub_smul, mul_smul, smul_sub]
        abel
      rw [heq]
      exact sub_mem (sub_mem het hC) (Submodule.smul_mem _ (α i) hbi)
    have ht : t = α i * T i i := by
      by_contra hne
      have hne' : α i * T i i - t ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
      have hmem : c i ∈ flagStep Ω c i := by
        have := Submodule.smul_mem _ (α i * T i i - t)⁻¹ hE
        rwa [smul_smul, inv_mul_cancel₀ hne', one_smul] at this
      exact hc.notMem_span_image (s := {k : Fin r | (k : ℕ) < i}) (x := i) (fun h => lt_irrefl (i : ℕ) h) hmem
    rw [ht]
    exact Submodule.mem_span_singleton.mpr ⟨a i, rfl⟩
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    exact Submodule.subset_span ⟨b i, Submodule.subset_span ⟨i, rfl⟩, hbi⟩

end Lin

section Lines

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}

theorem zpow_mem_span {A : Subring Ω} {s σ : Ω} (hs : s ≠ 0) (hσ : σ ≠ 0)
    (h : Submodule.span A {σ} = Submodule.span A {s}) (a : ℤ) : σ ^ a ∈ Submodule.span A {s ^ a} := by
  have h1 : σ ∈ Submodule.span A {s} := by
    rw [← h]
    exact Submodule.mem_span_singleton_self σ
  have h2 : s ∈ Submodule.span A {σ} := by
    rw [h]
    exact Submodule.mem_span_singleton_self s
  obtain ⟨u, hu⟩ := Submodule.mem_span_singleton.mp h1
  obtain ⟨v, hv⟩ := Submodule.mem_span_singleton.mp h2
  have hu' : (u : Ω) * s = σ := hu
  have hv' : (v : Ω) * σ = s := hv
  have huv : (u : Ω) * v = 1 := by
    have h3 : (u : Ω) * v * σ = 1 * σ := by rw [mul_assoc, hv', hu', one_mul]
    exact mul_right_cancel₀ hσ h3
  have hmem : ∀ n : ℤ, (u : Ω) ^ n ∈ A := by
    intro n
    rcases n with n | n
    · simpa using pow_mem u.2 n
    · have h4 : (u : Ω) ^ (Int.negSucc n) = (v : Ω) ^ (n + 1) := by
        rw [zpow_negSucc, ← inv_pow, inv_eq_of_mul_eq_one_right huv]
      rw [h4]
      exact pow_mem v.2 _
  rw [Submodule.mem_span_singleton]
  refine ⟨⟨(u : Ω) ^ a, hmem a⟩, ?_⟩
  show (u : Ω) ^ a * s ^ a = σ ^ a
  rw [← mul_zpow, hu']

theorem unit_of_tens (Λ : Lat ξ Ω) (q : Cpt ξ) (a : ℤ) {s M : Ω} (hs : Λ.IsGenAt q s) (hM0 : M ≠ 0)
    (hM : Lat.tens (fun _ : Unit => Λ) (fun _ => a) q = Submodule.span (regAt ξ q) {M}) :
    M * s ^ (-a) ∈ regAt ξ q ∧ (M * s ^ (-a))⁻¹ ∈ regAt ξ q := by
  have hs0 : s ≠ 0 := hs.1
  have hsa : s ^ a ∈ Lat.tens (fun _ : Unit => Λ) (fun _ => a) q := by
    apply Submodule.subset_span
    exact ⟨fun _ => s, fun _ => hs, by simp⟩
  have hle : Lat.tens (fun _ : Unit => Λ) (fun _ => a) q ≤ Submodule.span (regAt ξ q) {s ^ a} := by
    apply Submodule.span_le.mpr
    rintro t ⟨σ', hσ', rfl⟩
    have hσ := hσ' ()
    have heq : Submodule.span (regAt ξ q) {σ' ()} = Submodule.span (regAt ξ q) {s} := hσ.2.symm.trans hs.2
    simpa using zpow_mem_span hs0 hσ.1 heq a
  have hMmem : M ∈ Lat.tens (fun _ : Unit => Λ) (fun _ => a) q := by
    rw [hM]
    exact Submodule.mem_span_singleton_self M
  obtain ⟨r', hr'⟩ := Submodule.mem_span_singleton.mp (hle hMmem)
  rw [hM] at hsa
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp hsa
  have hr1 : (r' : Ω) * s ^ a = M := hr'
  have hr2 : (r : Ω) * M = s ^ a := hr
  have hsa0 : s ^ a ≠ 0 := zpow_ne_zero a hs0
  constructor
  · have h5 : M * s ^ (-a) = r' := by
      rw [← hr1, zpow_neg, mul_assoc, mul_inv_cancel₀ hsa0, mul_one]
    rw [h5]
    exact r'.2
  · have h6 : (M * s ^ (-a))⁻¹ = r := by
      rw [zpow_neg, mul_inv, inv_inv, ← hr2, mul_comm (r : Ω) M, ← mul_assoc, inv_mul_cancel₀ hM0, one_mul]
    rw [h6]
    exact r.2

end Lines

theorem root_unit : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (SS : Finset ℕ) (RM : Top.RootModel (CMType H) (Dw.p + Dw.q)) (Sys : PB.AnSys (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))) (Fx : FixedData Y Sys) (Or : RootOrigin Y SS RM Fx) (ρ : RootIx Dw) (q : Cpt Or.𝔐.ξ) (ch : (k : RM.K) → RM.ι k), InChart Or.𝔐.ξ (fun c' : (k : RM.K) → RM.ι k => ∏ k, RM.y ⟨k, c' k⟩) ch q → ∀ (b : Fin (labelRk Dw (HodgeCpt.rootIdx Dw ρ).1) → Or.𝔐.Li) (Tm : Matrix (Fin (labelRk Dw (HodgeCpt.rootIdx Dw ρ).1)) (Fin (labelRk Dw (HodgeCpt.rootIdx Dw ρ).1)) RM.Ω), (∀ i : ℕ, flagStep RM.Ω b i = flagStep RM.Ω (Or.Fl.b (HodgeCpt.rootIdx Dw ρ).1) i) → (Or.𝔐.V (HodgeCpt.rootIdx Dw ρ).1).IsFrameAt b q → (∀ i, b i = ∑ j, Tm i j • Or.Fl.b (HodgeCpt.rootIdx Dw ρ).1 j) → (∀ i, Tm i i ≠ 0) → ((∏ k, RM.y ⟨k, ch k⟩ ^ RM.xdeg ρ k) * Or.e ρ) * (Tm (HodgeCpt.rootIdx Dw ρ).2 (HodgeCpt.rootIdx Dw ρ).2) ^ (-HodgeCpt.rootSgn Dw ρ) ∈ regAt Or.𝔐.ξ q ∧ (((∏ k, RM.y ⟨k, ch k⟩ ^ RM.xdeg ρ k) * Or.e ρ) * (Tm (HodgeCpt.rootIdx Dw ρ).2 (HodgeCpt.rootIdx Dw ρ).2) ^ (-HodgeCpt.rootSgn Dw ρ))⁻¹ ∈ regAt Or.𝔐.ξ q := by
  intro E _ _ _ H Dw l Xo c O _ β Y SS RM Sys Fx Or ρ q ch hch b Tm hfl hfr hT hd
  have hL : (Or.Fl.rootLat ρ).IsDegOn Set.univ RM.y (RM.xdeg ρ) (Or.e ρ) := Or.lines ρ
  obtain ⟨_, hL2⟩ := hL
  have hdeg : Lat.tens (fun _ : Unit => (Or.𝔐.V (HodgeCpt.rootIdx Dw ρ).1).gr
      (Or.Fl.b (HodgeCpt.rootIdx Dw ρ).1) (HodgeCpt.rootIdx Dw ρ).2) (fun _ => HodgeCpt.rootSgn Dw ρ) q =
      Submodule.span (regAt Or.𝔐.ξ q) {(∏ k, RM.y ⟨k, ch k⟩ ^ RM.xdeg ρ k) * Or.e ρ} :=
    hL2 q (Set.mem_univ q) ch hch
  have hgr : ((Or.𝔐.V (HodgeCpt.rootIdx Dw ρ).1).gr (Or.Fl.b (HodgeCpt.rootIdx Dw ρ).1)
      (HodgeCpt.rootIdx Dw ρ).2).IsGenAt q (Tm (HodgeCpt.rootIdx Dw ρ).2 (HodgeCpt.rootIdx Dw ρ).2) := by
    refine ⟨hd _, ?_⟩
    have h1 := span_gr_eq (regAt Or.𝔐.ξ q) hfr.1 hfl hT (HodgeCpt.rootIdx Dw ρ).2
    rw [← hfr.2] at h1
    exact h1
  have hM0 : (∏ k, RM.y ⟨k, ch k⟩ ^ RM.xdeg ρ k) * Or.e ρ ≠ 0 := by
    intro h0
    have hmem : Tm (HodgeCpt.rootIdx Dw ρ).2 (HodgeCpt.rootIdx Dw ρ).2 ^ HodgeCpt.rootSgn Dw ρ ∈
        Lat.tens (fun _ : Unit => (Or.𝔐.V (HodgeCpt.rootIdx Dw ρ).1).gr
          (Or.Fl.b (HodgeCpt.rootIdx Dw ρ).1) (HodgeCpt.rootIdx Dw ρ).2) (fun _ => HodgeCpt.rootSgn Dw ρ) q := by
      apply Submodule.subset_span
      exact ⟨fun _ => Tm (HodgeCpt.rootIdx Dw ρ).2 (HodgeCpt.rootIdx Dw ρ).2, fun _ => hgr, by simp⟩
    rw [hdeg, h0] at hmem
    obtain ⟨x, hx⟩ := Submodule.mem_span_singleton.mp hmem
    have hx' : (x : RM.Ω) * 0 = _ := hx
    rw [mul_zero] at hx'
    exact zpow_ne_zero _ (hd _) hx'.symm
  exact unit_of_tens _ q _ hgr hM0 hdeg

end GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.RootUnit
