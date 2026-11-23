import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.PowerSeriesOneAddConstMulXMulInv
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GammaConditionShiftAndDivVariableMemStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GenEigenMultiplicityLaurentShiftEqSumSenStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NabBijectiveWindow

noncomputable section
namespace GlobalTheory.PhiGam.PolarCount
open scoped LaurentSeries PowerSeries
open GlobalTheory.PhiGam Module

section lin
variable {k : Type} [Field k] {U : Type} [AddCommGroup U] [Module k U]

theorem rank_nullity {W : Type} [AddCommGroup W] [Module k W] (A : Submodule k U) [FiniteDimensional k A]
    (f : U →ₗ[k] W) :
    finrank k (A.map f) + finrank k (A ⊓ LinearMap.ker f : Submodule k U) = finrank k A := by
  have h := LinearMap.finrank_range_add_finrank_ker (f.domRestrict A)
  rw [LinearMap.range_domRestrict, LinearMap.ker_domRestrict] at h
  rw [← h, ← Submodule.map_comap_subtype, Submodule.finrank_map_subtype_eq]

theorem finrank_quot (A B : Submodule k U) :
    finrank k (↥A ⧸ B.submoduleOf A) = finrank k (A.map B.mkQ) := by
  have h := (LinearMap.quotKerEquivRange (B.mkQ.domRestrict A)).finrank_eq
  rw [LinearMap.range_domRestrict, LinearMap.ker_domRestrict, Submodule.ker_mkQ] at h
  exact h

theorem count (T : Module.End k U) (F L N Z S S' : Submodule k U) [FiniteDimensional k S]
    [FiniteDimensional k S'] (hLN : L ≤ N) (hNF : N ≤ F) (hTL : L ≤ L.comap T) (hF' : F ≤ S' ⊔ L)
    (hF : F ≤ S ⊔ F.map T ⊔ L) (he : ∀ x ∈ N, (∃ m : ℕ, (T ^ m) x ∈ L) → T x ∈ L)
    (hZ : ∀ x ∈ Z, x ∈ F ∧ T x ∈ L) :
    finrank k (↥Z ⧸ N.submoduleOf Z) + gmult T N L 0 ≤ finrank k S := by
  unfold gmult
  rw [finrank_quot, finrank_quot]
  rw [map_zero (algebraMap k (Module.End k U)), sub_zero]
  set Tb : (U ⧸ L) →ₗ[k] (U ⧸ L) := L.mapQ L T hTL with hTb
  set h : (U ⧸ L) →ₗ[k] (U ⧸ N) := Submodule.factor hLN with hh
  set Fb := F.map L.mkQ with hFb
  have hL0 : L.map L.mkQ = ⊥ := by simp
  have hfin : FiniteDimensional k Fb := by
    have : Fb ≤ S'.map L.mkQ := by
      have := Submodule.map_mono (f := L.mkQ) hF'
      rwa [Submodule.map_sup, hL0, sup_bot_eq] at this
    exact Submodule.finiteDimensional_of_le this
  set Kb : Submodule k (U ⧸ L) := Fb ⊓ LinearMap.ker Tb with hKb
  have hKfin : FiniteDimensional k Kb := Submodule.finiteDimensional_of_le inf_le_left
  have h1 := rank_nullity Fb Tb
  rw [← hKb] at h1
  have h2 : Fb ≤ S.map L.mkQ ⊔ Fb.map Tb := by
    have := Submodule.map_mono (f := L.mkQ) hF
    rw [Submodule.map_sup, hL0, sup_bot_eq, Submodule.map_sup] at this
    refine this.trans (sup_le_sup_left ?_ _)
    rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨L.mkQ x, ⟨x, hx, rfl⟩, rfl⟩
  have h3 := Submodule.finrank_mono h2
  have h4 := Submodule.finrank_add_le_finrank_add_finrank (S.map L.mkQ) (Fb.map Tb)
  have h5 := Submodule.finrank_map_le L.mkQ S
  have h6 := rank_nullity Kb h
  have hmem : ∀ x ∈ F, T x ∈ L → L.mkQ x ∈ Kb := by
    intro x hx hT
    refine ⟨⟨x, hx, rfl⟩, ?_⟩
    show L.mkQ (T x) = 0
    simpa using hT
  have h7 : Z.map N.mkQ ≤ Kb.map h := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨L.mkQ x, hmem x (hZ x hx).1 (hZ x hx).2, rfl⟩
  have h8 : (N ⊓ ⨆ m : ℕ, L.comap (T ^ m)).map L.mkQ ≤ Kb ⊓ LinearMap.ker h := by
    rintro _ ⟨x, ⟨hxN, hx⟩, rfl⟩
    refine ⟨hmem x (hNF hxN) (he x hxN ?_), ?_⟩
    · have hmono : Monotone (fun m : ℕ => L.comap (T ^ m)) := by
        refine monotone_nat_of_le_succ fun m y hy => ?_
        show (T ^ (m + 1)) y ∈ L
        rw [pow_succ']
        exact hTL hy
      exact (Submodule.mem_iSup_of_directed _ hmono.directed_le).1 hx
    · show N.mkQ x = 0
      simpa using hxN
  have h9 := Submodule.finrank_mono h7
  have h10 := Submodule.finrank_mono h8
  omega
end lin

variable {k : Type} [Field k] {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V] [Module k V]
  [IsScalarTower k⟦X⟧ k⸨X⸩ V] [IsScalarTower k k⸨X⸩ V] [IsScalarTower k k⟦X⟧ V]

theorem vv_ne : vv k ≠ 0 := by
  unfold vv; exact HahnSeries.single_ne_zero one_ne_zero

theorem vv_eq : vv k = ((PowerSeries.X : k⟦X⟧) : k⸨X⸩) := by
  unfold vv; simp

theorem coe_smul (b : k⟦X⟧) (x : V) : (b : k⸨X⸩) • x = b • x :=
  algebraMap_smul k⸨X⸩ b x

theorem mem_sh {a : ℤ} {N : Submodule k⟦X⟧ V} {x : V} : x ∈ sh a N ↔ ∃ y ∈ N, vv k ^ a • y = x := by
  unfold sh; rw [Submodule.mem_map]; rfl

theorem smul_mem_sh {a : ℤ} (b : ℤ) {N : Submodule k⟦X⟧ V} {x : V} (h : x ∈ sh a N) :
    vv k ^ b • x ∈ sh (a + b) N := by
  obtain ⟨y, hy, rfl⟩ := mem_sh.1 h
  exact mem_sh.2 ⟨y, hy, by rw [smul_smul, ← zpow_add₀ vv_ne, add_comm]⟩

theorem sh_zero (N : Submodule k⟦X⟧ V) : sh 0 N = N := by
  ext x; simp [mem_sh]

theorem sh_sh (a b : ℤ) (N : Submodule k⟦X⟧ V) : sh b (sh a N) = sh (a + b) N := by
  ext x
  constructor
  · intro h
    obtain ⟨y, hy, rfl⟩ := mem_sh.1 h
    exact smul_mem_sh b hy
  · intro h
    refine mem_sh.2 ⟨vv k ^ (-b) • x, ?_, ?_⟩
    · simpa using smul_mem_sh (-b) h
    · rw [smul_smul, ← zpow_add₀ vv_ne]; simp

theorem sh_mono (a : ℤ) {N P : Submodule k⟦X⟧ V} (h : N ≤ P) : sh a N ≤ sh a P :=
  Submodule.map_mono h

theorem sh_anti {a b : ℤ} (h : a ≤ b) (N : Submodule k⟦X⟧ V) : sh b N ≤ sh a N := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := mem_sh.1 hx
  obtain ⟨m, rfl⟩ := Int.le.dest h
  refine mem_sh.2 ⟨(PowerSeries.X ^ m : k⟦X⟧) • y, N.smul_mem _ hy, ?_⟩
  rw [← coe_smul, smul_smul, zpow_add₀ vv_ne, zpow_natCast, vv_eq, map_pow]

theorem nab_apply (g : V →ₗ[k] V) (x : V) : nab g x = vv k ^ (-1 : ℤ) • (g x - x) := by
  rw [zpow_neg_one]; rfl

theorem span_le {ι : Type} (e : ι → V) (P : Submodule k⟦X⟧ V) (hP : Submodule.span k⟦X⟧ (Set.range e) = P) :
    P.restrictScalars k ≤ Submodule.span k (Set.range e) ⊔ (sh 1 P).restrictScalars k := by
  intro x hx
  rw [Submodule.restrictScalars_mem, ← hP, Finsupp.mem_span_range_iff_exists_finsupp] at hx
  obtain ⟨c, rfl⟩ := hx
  refine Submodule.sum_mem _ fun i _ => ?_
  show c i • e i ∈ _
  have he : e i ∈ P := hP ▸ Submodule.subset_span ⟨i, rfl⟩
  obtain ⟨d, hd⟩ : ∃ d : k⟦X⟧, c i = algebraMap k k⟦X⟧ (PowerSeries.constantCoeff (c i)) + PowerSeries.X * d :=
    ⟨_, by rw [add_comm]; exact PowerSeries.eq_X_mul_shift_add_const (c i)⟩
  rw [hd, add_smul, algebraMap_smul]
  refine Submodule.add_mem_sup (Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)) ?_
  refine mem_sh.2 ⟨d • e i, P.smul_mem _ he, ?_⟩
  rw [zpow_one, vv_eq, coe_smul, mul_smul]

theorem fin_quot (N : Submodule k⟦X⟧ V) (hN : N.FG) (a : ℤ) (m : ℕ) :
    ∃ S : Submodule k V, FiniteDimensional k S ∧
      (sh a N).restrictScalars k ≤ S ⊔ (sh (a + m) N).restrictScalars k := by
  induction m with
  | zero => exact ⟨⊥, inferInstance, by simp⟩
  | succ m ih =>
    obtain ⟨S, hS, h⟩ := ih
    have hfg : (sh (a + m) N).FG := hN.map _
    obtain ⟨n, e, he⟩ := Submodule.fg_iff_exists_fin_generating_family.1 hfg
    have h2 := span_le e _ he
    rw [sh_sh] at h2
    have : FiniteDimensional k (Submodule.span k (Set.range e)) :=
      FiniteDimensional.span_of_finite k (Set.finite_range e)
    refine ⟨S ⊔ Submodule.span k (Set.range e), inferInstance, h.trans ?_⟩
    rw [sup_assoc]
    refine sup_le_sup_left ?_ _
    rw [Nat.cast_succ, ← add_assoc]
    exact h2

theorem gens [FiniteDimensional k⸨X⸩ V] (N : Submodule k⟦X⟧ V) (hN : N.FG) :
    ∃ (n : ℕ) (e : Fin n → V), n ≤ finrank k⸨X⸩ V ∧ Submodule.span k⟦X⟧ (Set.range e) = N := by
  have : Module.Finite k⟦X⟧ N := Module.Finite.iff_fg.2 hN
  have : Module.IsTorsionFree k⟦X⟧ V := Module.IsTorsionFree.trans_faithfulSMul k⟦X⟧ k⸨X⸩ V
  have : Module.Free k⟦X⟧ N := inferInstance
  let b := Module.finBasis k⟦X⟧ N
  refine ⟨_, N.subtype ∘ b, ?_, ?_⟩
  · have hli : LinearIndependent k⟦X⟧ (N.subtype ∘ b) := b.linearIndependent.map' _ N.ker_subtype
    have := ((LinearIndependent.iff_fractionRing k⟦X⟧ k⸨X⸩).1 hli).fintype_card_le_finrank
    simpa using this
  · rw [Set.range_comp, ← Submodule.map_span, b.span_eq, Submodule.map_top, Submodule.range_subtype]

theorem phi_sh {l : ℕ} (R : RingPG k l) (f : V →ₗ[k] V) (hf : Semi R.φ f) (N : Submodule k⟦X⟧ V) (t : ℕ)
    {y : V} (hy : y ∈ sh t N) : f y ∈ sh (l * t : ℕ) (pull f N) := by
  obtain ⟨z, hz, rfl⟩ := mem_sh.1 hy
  obtain ⟨u, hu⟩ := R.φ_v
  refine mem_sh.2 ⟨((u : k⟦X⟧) ^ t) • f z, Submodule.smul_mem _ _ (Submodule.subset_span ⟨z, hz, rfl⟩), ?_⟩
  rw [hf, zpow_natCast, zpow_natCast, map_pow, hu, ← coe_smul, smul_smul, map_pow, mul_pow, ← pow_mul, mul_comm]

theorem psi_mem (f ψ : V →ₗ[k] V) (ψ0 : k⸨X⸩ →ₗ[k] k⸨X⸩) (h : ∀ (a : k⸨X⸩) x, ψ (a • f x) = ψ0 a • x) (a : ℤ)
    (h0 : ∀ b : k⟦X⟧, ∃ c : k⟦X⟧, (c : k⸨X⸩) = ψ0 (vv k ^ a * (b : k⸨X⸩))) (N : Submodule k⟦X⟧ V)
    {y : V} (hy : y ∈ sh a (pull f N)) : ψ y ∈ N := by
  obtain ⟨z, hz, rfl⟩ := mem_sh.1 hy
  suffices H : ∀ b : k⟦X⟧, ψ (vv k ^ a • b • z) ∈ N by simpa using H 1
  clear hy
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨x, hx, rfl⟩ := hx
    intro b
    obtain ⟨c, hc⟩ := h0 b
    rw [← coe_smul, smul_smul, h, ← hc, coe_smul]
    exact N.smul_mem _ hx
  | zero => intro b; simp
  | add x y _ _ hx hy => intro b; rw [smul_add, smul_add, map_add]; exact N.add_mem (hx b) (hy b)
  | smul c x _ hx => intro b; rw [smul_smul b c]; exact hx _

theorem main : ∀ {k : Type} [Field k] {l : ℕ} [Fact l.Prime] [CharP k l] (R : RingPG k l) {n : ℕ} [NeZero n] {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V] [Module k V] [IsScalarTower k⟦X⟧ k⸨X⸩ V] [IsScalarTower k k⸨X⸩ V] [IsScalarTower k k⟦X⟧ V] [FiniteDimensional k⸨X⸩ V] (D : ModPG R n V), ∀ (ψ : ZMod n → V →ₗ[k] V) (ψ0 : k⸨X⸩ →ₗ[k] k⸨X⸩), (∀ i a x, ψ i (a • D.φ i x) = ψ0 a • x) → (∀ a b, ψ0 (R.φ a * b) = a * ψ0 b) → ψ0 1 = 1 → (∀ i x, ψ i (D.γ i x) = D.γ (i - 1) (ψ i x)) → (∀ a : ℤ, 2 - (l : ℤ) ≤ a → a ≤ 1 → ψ0 '' {x | ∃ b : k⟦X⟧, x = vv k ^ a * (b : k⸨X⸩)} = Set.range (fun b : k⟦X⟧ => (b : k⸨X⸩))) → ∀ (i : ZMod n) (N₀ N : Submodule k⟦X⟧ V) (ws s : ℕ) (w : ℤ), IsLat N₀ → IsLat N → CondC (D.γ (i - 1)) N₀ → CondC (D.γ i) N → 1 ≤ ws → ws + 7 ≤ l → sh ws N ≤ pull (D.φ i) N₀ → pull (D.φ i) N₀ ≤ sh (-w) N → (ws : ℤ) + 2 ≤ l * (s + 3) - w → (∀ a : ℕ, a ≤ s + 1 → sen (D.γ (i - 1)) N₀ (a : k) = 0) → (∀ y ∈ sh (1 - ws) (pull (D.φ i) N₀), ψ i y = 0 → ∃ x ∈ sh (-ws) (pull (D.φ i) N₀), ψ i x = 0 ∧ D.γ i x - x = y) → (∀ x ∈ N, (∃ m : ℕ, ((nab (D.γ i)) ^ m) x ∈ sh (ws + 1) N) → nab (D.γ i) x ∈ sh (ws + 1) N) → ∀ Z : Submodule k V, (∀ x ∈ Z, x ∈ sh (-ws) (pull (D.φ i) N₀) ∧ D.γ i x - x ∈ sh (ws + 2) N) → Module.finrank k (↥Z ⧸ (N.restrictScalars k).submoduleOf Z) + ∑ a ∈ Finset.range (ws + 1), sen (D.γ i) N (a : k) ≤ Module.finrank k⸨X⸩ V := by
  intro k _ l _ _ R n _ V _ _ _ _ _ _ _ _ D ψ ψ0 hψ _ hψ1 _ hP i N₀ N ws s w hN₀ hN hC₀ hC hws hl hb ha hd hs
    hPSI he Z hZ
  have hv : vv k ≠ 0 := vv_ne
  have hr := GlobalTheory.T.genEigenMultiplicity_laurentShift_eq_sum_sen R (D.γ i) (D.γ_semi i) N hN hC 0 (ws + 1) 0
  simp only [zero_add, Int.cast_natCast, sh_zero] at hr
  rw [← hr, Nat.cast_succ]
  obtain ⟨r, e, hre, hspan⟩ := gens N₀ hN₀.1
  set M := pull (D.φ i) N₀ with hM
  let A : V →ₗ[k] V := ((vv k ^ (-1 : ℤ) • (LinearMap.id : V →ₗ[k⸨X⸩] V)).restrictScalars k) ∘ₗ D.φ i
  have hA : ∀ x, A x = vv k ^ (-1 : ℤ) • D.φ i x := fun _ => rfl
  have : FiniteDimensional k (Submodule.span k (Set.range e)) :=
    FiniteDimensional.span_of_finite k (Set.finite_range e)
  have hS : finrank k ((Submodule.span k (Set.range e)).map A) ≤ finrank k⸨X⸩ V := by
    refine (Submodule.finrank_map_le _ _).trans (le_trans ?_ hre)
    exact (finrank_range_le_card (R := k) e).trans (by simp)
  obtain ⟨S', hS', hF'⟩ := fin_quot N hN.1 (min (-w + -ws) (ws + 1)) (ws + 1 - min (-w + -ws) (ws + 1)).toNat
  rw [Int.toNat_of_nonneg (by omega), add_sub_cancel] at hF'
  have hNF : N ≤ sh (-ws) M := by
    have := sh_mono (-ws) hb
    rwa [sh_sh, add_neg_cancel, sh_zero] at this
  have hMF : M ≤ sh (-ws) M := by
    have := sh_anti (show (-ws : ℤ) ≤ 0 by omega) M
    rwa [sh_zero] at this
  refine le_trans (count (nab (D.γ i)) ((sh (-ws) M).restrictScalars k) ((sh (ws + 1) N).restrictScalars k)
    (N.restrictScalars k) Z ((Submodule.span k (Set.range e)).map A) S' ?_ hNF ?_ ?_ ?_ he ?_) hS
  · have := sh_anti (show (0 : ℤ) ≤ ws + 1 by omega) N
    rwa [sh_zero] at this
  · intro x hx
    exact (GlobalTheory.T.gammaCondition_shift_and_divVariable_mem R (D.γ i) (D.γ_semi i) N hC (ws + 1)).2 x hx
  · refine le_trans ?_ hF'
    intro x hx
    have := sh_mono (-ws) ha hx
    rw [sh_sh] at this
    exact sh_anti (min_le_left _ _) N this
  · intro x hx
    have h1 : vv k ^ (1 : ℤ) • x ∈ sh (1 - ws) M := by
      have := smul_mem_sh 1 hx
      rwa [neg_add_eq_sub] at this
    have hy : ψ i (vv k ^ (1 : ℤ) • x) ∈ N₀ := by
      refine psi_mem (D.φ i) (ψ i) ψ0 (hψ i) (1 - ws) (fun b => ?_) N₀ h1
      have : ψ0 (vv k ^ (1 - ws : ℤ) * (b : k⸨X⸩)) ∈ Set.range (fun b : k⟦X⟧ => (b : k⸨X⸩)) := by
        rw [← hP (1 - ws) (by omega) (by omega)]
        exact ⟨_, ⟨b, rfl⟩, rfl⟩
      exact this
    set y := ψ i (vv k ^ (1 : ℤ) • x) with hydef
    have hφM : ∀ z ∈ N₀, D.φ i z ∈ M := fun z hz => Submodule.subset_span ⟨z, hz, rfl⟩
    have hM1 : M ≤ sh (1 - ws) M := by
      have := sh_anti (show (1 - ws : ℤ) ≤ 0 by omega) M
      rwa [sh_zero] at this
    obtain ⟨x', hx', -, hx'e⟩ := hPSI (vv k ^ (1 : ℤ) • x - D.φ i y) (Submodule.sub_mem _ h1 (hM1 (hφM y hy)))
      (by
        have := hψ i 1 y
        rw [one_smul, hψ1, one_smul] at this
        rw [map_sub, this, sub_self])
    obtain ⟨y1, hy1, y2, hy2, hy12⟩ := Submodule.mem_sup.1 (span_le e N₀ hspan hy)
    obtain ⟨y3, hy3, rfl⟩ := mem_sh.1 hy2
    obtain ⟨z, hz, hz'⟩ := (GlobalTheory.PhiGam.Window.nab_bijective_window R (D.γ (i - 1)) (D.γ_semi _) N₀ hN₀ hC₀ 0 (s + 2) (fun j hj => by
      simpa using hs j (by omega))).2 y3 (by rwa [sh_zero])
    rw [sh_zero] at hz
    have hz2 : vv k ^ (1 : ℤ) • (y3 - nab (D.γ (i - 1)) z) ∈ sh ((s + 3 : ℕ) : ℤ) N₀ := by
      have := smul_mem_sh 1 hz'
      convert this using 2
      push_cast; ring
    have hz3 := smul_mem_sh (-1) (sh_mono _ ha (phi_sh R (D.φ i) (D.φ_semi i) N₀ _ hz2))
    rw [sh_sh] at hz3
    have hz4 := sh_anti (a := (ws : ℤ) + 1) (by push_cast; omega) N hz3
    have hvv : ∀ u : V, vv k ^ (1 : ℤ) • vv k ^ (-1 : ℤ) • u = u := fun u => by
      rw [smul_smul, ← zpow_add₀ hv]; simp
    have hvv' : ∀ u : V, vv k ^ (-1 : ℤ) • vv k ^ (1 : ℤ) • u = u := fun u => by
      rw [smul_smul, ← zpow_add₀ hv]; simp
    have key : x = A y1 + nab (D.γ i) (x' + D.φ i z) +
        vv k ^ (-1 : ℤ) • D.φ i (vv k ^ (1 : ℤ) • (y3 - nab (D.γ (i - 1)) z)) := by
      rw [hA, map_add, nab_apply, nab_apply, nab_apply, hx'e, ← hy12, smul_sub (vv k ^ (1 : ℤ)), hvv,
        ← D.comm, map_sub, map_sub, map_add, ← smul_add, ← smul_add, ← smul_add]
      rw [← hvv' x, hvv]
      congr 1
      abel
    rw [key]
    exact Submodule.add_mem_sup (Submodule.add_mem_sup ⟨y1, hy1, rfl⟩
      ⟨x' + D.φ i z, Submodule.add_mem _ hx' (hMF (hφM z hz)), rfl⟩) hz4
  · intro x hx
    refine ⟨(hZ x hx).1, ?_⟩
    have := smul_mem_sh (-1) (hZ x hx).2
    rw [nab_apply]
    show _ ∈ sh (ws + 1) N
    convert this using 2
    ring

end GlobalTheory.PhiGam.PolarCount
