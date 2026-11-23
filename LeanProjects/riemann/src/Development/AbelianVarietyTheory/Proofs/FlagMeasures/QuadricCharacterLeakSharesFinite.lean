import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsPrincipalIdealRingOfHenselian
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsNormOneOrthTriple
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BasisOfIsCompl
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianDoubleCosetTermBasicFacts
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermExponentsNonnegAndDefectGroupBoundStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CongruenceSubgroupLatticeStabilizer
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ProperIdealsOfHenselian
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsTraceChar
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExpandByConductor
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TwoGeometricSumsIndexBound
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormGaussSumLe
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianLocalCharacterSumStatement

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.QuadricShare

open GlobalTheory.HL.GaussSummand

theorem sum_char_eq_zero {E V : Type} [CommRing E] [AddCommGroup V] [Module E V] {O : Subring E}
    (UU : Submodule O V) (p : E) (R : Finset V) (hRU : ∀ u ∈ R, u ∈ UU)
    (hR : ∀ u ∈ UU, ∃! w, w ∈ R ∧ ∃ y ∈ UU, u - w = p • y) (χ : AddChar V ℂ)
    (hχ : ∀ u ∈ UU, χ (p • u) = 1) (u₀ : V) (hu₀ : u₀ ∈ R) (hne : χ u₀ ≠ 1) :
    ∑ u ∈ R, χ u = 0 := by
  have hex : ∀ w ∈ R, ∃ w', w' ∈ R ∧ ∃ y ∈ UU, (w + u₀) - w' = p • y := fun w hw =>
    (hR _ (UU.add_mem (hRU w hw) (hRU u₀ hu₀))).exists
  choose! σ hσR hσ using hex
  have hinj : Set.InjOn σ R := by
    intro w hw w' hw' h
    obtain ⟨y, hy, e⟩ := hσ w hw
    obtain ⟨y', hy', e'⟩ := hσ w' hw'
    refine (hR w (hRU w hw)).unique ⟨hw, 0, UU.zero_mem, by simp⟩ ⟨hw', y - y', UU.sub_mem hy hy', ?_⟩
    rw [smul_sub, ← e, ← e', h]; abel
  have himg : R.image σ = R := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 hx
      exact hσR w hw
    · rw [Finset.card_image_of_injOn hinj]
  have h1 : ∑ u ∈ R, χ u = ∑ u ∈ R, χ u * χ u₀ := by
    conv_lhs => rw [← himg, Finset.sum_image hinj]
    refine Finset.sum_congr rfl fun w hw => ?_
    obtain ⟨y, hy, e⟩ := hσ w hw
    have : w + u₀ = σ w + p • y := by rw [← e]; abel
    rw [← AddChar.map_add_eq_mul, this, AddChar.map_add_eq_mul, hχ y hy, mul_one]
  rw [← Finset.sum_mul] at h1
  have h2 : (∑ u ∈ R, χ u) * (1 - χ u₀) = 0 := by rw [mul_sub, mul_one, ← h1, sub_self]
  exact (mul_eq_zero.1 h2).resolve_right (sub_ne_zero.2 hne.symm)

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E)
  {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E)

theorem exists_norm (hH : IsHermND L Hm) (ϖ : 𝒪[F]) (hϖ : Irreducible ϖ)
    (UU : Submodule L.O (Fin n → E)) (hUU : ∀ x ∈ UU, ∀ y ∈ UU, hf L Hm x y ∈ L.O) :
    ∃ (nrm : (Fin n → E) → F) (Q : (Fin n → E) → 𝒪[F]), (∀ u, algebraMap F E (nrm u) = hf L Hm u u) ∧
      (∀ u ∈ UU, (Q u : F) = nrm u) ∧
      ∀ (a : ℕ), ∀ u ∈ UU, (ϖ ^ a ∣ Q u ↔ ∃ c : 𝒪[F], hf L Hm u u = algebraMap F E ((ϖ : F) ^ a * c)) := by
  obtain ⟨-, -, -, -, hint, -, -, -⟩ := GlobalTheory.UnramOrder.order_facts L ϖ hϖ
  have hinj := GlobalTheory.UnramOrder.algebraMap_inj L
  choose nrm hnrm using fun u : Fin n → E => (L.cj_fix _).1 (cj_hf L Hm hH.1 u u)
  have hQ : ∀ u ∈ UU, nrm u ∈ 𝒪[F] := fun u hu => (hint _).1 (by rw [hnrm]; exact hUU u hu u hu)
  refine ⟨nrm, fun u => if h : nrm u ∈ 𝒪[F] then ⟨nrm u, h⟩ else 0, hnrm, fun u hu => ?_,
    fun a u hu => ?_⟩
  · simp only [dif_pos (hQ u hu)]
  · simp only [dif_pos (hQ u hu)]
    constructor
    · rintro ⟨c, hc⟩
      refine ⟨c, ?_⟩
      have := congrArg (fun x : 𝒪[F] => (x : F)) hc
      simp only [Subring.coe_mul, SubmonoidClass.coe_pow] at this
      rw [← hnrm, this]
    · rintro ⟨c, hc⟩
      rw [← hnrm] at hc
      exact ⟨c, Subtype.ext (by simpa using hinj hc)⟩

theorem char_share (hH : IsHermND L Hm) (ϖ : 𝒪[F]) (hϖ : Irreducible ϖ)
    (UU : Submodule L.O (Fin n → E)) (hUU : ∀ x ∈ UU, ∀ y ∈ UU, hf L Hm x y ∈ L.O)
    (ρ : ℕ) (hρ : 4 ≤ ρ) (e : Fin ρ → Fin n → E) (he : ∀ a, e a ∈ UU)
    (hee : ∀ a b, hf L Hm (e a) (e b) = if a = b then 1 else 0) (a N : ℕ) (haN : a ≤ N)
    (R : Finset (Fin n → E)) (hRU : ∀ u ∈ R, u ∈ UU)
    (hR : ∀ u ∈ UU, ∃! w, w ∈ R ∧ ∃ y ∈ UU, u - w = algebraMap F E ((ϖ : F) ^ N) • y)
    (Z : (Fin n → E) → Prop)
    (hZ : ∀ u, Z u ↔ ∃ c : 𝒪[F], hf L Hm u u = algebraMap F E ((ϖ : F) ^ a * c))
    (χ : AddChar (Fin n → E) ℂ) (hχ1 : ∀ u, ‖χ u‖ = 1)
    (hχ : ∀ u ∈ UU, χ (algebraMap F E ((ϖ : F) ^ N) • u) = 1) :
    ‖(∑ u ∈ R.filter Z, χ u) * (resQ ϖ : ℂ) ^ a - ∑ u ∈ R, χ u‖ ≤
      8 / 7 * (resQ ϖ : ℝ) ^ (1 - (ρ : ℤ)) * R.card := by
  obtain ⟨-, -, -, -, -, -, hq, -⟩ := GlobalTheory.UnramOrder.order_facts L ϖ hϖ
  obtain ⟨ψ, hψ1, hψ, -⟩ := GlobalTheory.TraceChar.exists_trace_char L
  obtain ⟨nrm, Q, hnrm, hQ, hdvd⟩ := exists_norm L Hm hH ϖ hϖ UU hUU
  have hfil : R.filter Z = R.filter (fun u => ϖ ^ a ∣ Q u) :=
    Finset.filter_congr fun u hu => by rw [hZ, hdvd a u (hRU u hu)]
  have h := GlobalTheory.HL.CharCond.expand_by_conductor ϖ hϖ ψ hψ R Q χ a
    (fun i => (R.card : ℝ) * (resQ ϖ : ℝ) ^ (-(i * ρ : ℤ))) (fun i hi hia t u₀ ht => by
      rw [Finset.sum_congr rfl fun u hu => by rw [hQ u (hRU u hu)]]
      exact norm_gauss_sum_le L Hm hH ϖ hϖ ψ hψ1 hψ UU hUU ρ e he hee i N hi (hia.trans haN) t u₀ ht
        χ hχ1 hχ R nrm hnrm hRU hR)
  rw [hfil]
  refine h.trans ?_
  have h2 := (GlobalTheory.two_geometric_sums_index_bound (resQ ϖ) ρ a hq hρ).1
  refine le_trans (le_of_eq ?_) (mul_le_mul_of_nonneg_right h2 (Nat.cast_nonneg _))
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem prime_share (hH : IsHermND L Hm) (ϖ : 𝒪[F]) (hϖ : Irreducible ϖ)
    (UU : Submodule L.O (Fin n → E)) (hUU : ∀ x ∈ UU, ∀ y ∈ UU, hf L Hm x y ∈ L.O)
    (ρ : ℕ) (hρ : 4 ≤ ρ) (e : Fin ρ → Fin n → E) (he : ∀ a, e a ∈ UU)
    (hee : ∀ a b, hf L Hm (e a) (e b) = if a = b then 1 else 0) (a N : ℕ) (haN : a ≤ N)
    (R : Finset (Fin n → E)) (hRU : ∀ u ∈ R, u ∈ UU)
    (hR : ∀ u ∈ UU, ∃! w, w ∈ R ∧ ∃ y ∈ UU, u - w = algebraMap F E ((ϖ : F) ^ N) • y)
    (Z : (Fin n → E) → Prop)
    (hZ : ∀ u, Z u ↔ ∃ c : 𝒪[F], hf L Hm u u = algebraMap F E ((ϖ : F) ^ a * c))
    (π : E) (j : ℕ) (hπ : π ∈ L.O) (hπj : π * L.cj π = algebraMap F E ((ϖ : F) ^ j))
    (hπN : ∃ c ∈ L.O, algebraMap F E ((ϖ : F) ^ N) = π * c) :
    ((R.filter fun u => Z u ∧ ∀ a, ∃ c ∈ L.O, hf L Hm u (e a) = π * c).card : ℝ) * (resQ ϖ : ℝ) ^ a ≤
      8 / 7 * (resQ ϖ : ℝ) ^ ((j : ℤ) - j * ρ) * R.card := by
  obtain ⟨-, -, -, -, -, -, hq, -⟩ := GlobalTheory.UnramOrder.order_facts L ϖ hϖ
  obtain ⟨ψ, hψ1, hψ, -⟩ := GlobalTheory.TraceChar.exists_trace_char L
  obtain ⟨nrm, Q, hnrm, hQ, hdvd⟩ := exists_norm L Hm hH ϖ hϖ UU hUU
  obtain ⟨hc, hg⟩ := GlobalTheory.T.hermitian_local_character_sum L Hm hH ϖ hϖ ψ hψ1 hψ UU hUU ρ e he hee π j N hπ hπj hπN R nrm hnrm
    hRU hR
  set R' := R.filter fun u => ∀ a, ∃ c ∈ L.O, hf L Hm u (e a) = π * c with hR'
  have hfil : (R.filter fun u => Z u ∧ ∀ a, ∃ c ∈ L.O, hf L Hm u (e a) = π * c)
      = R'.filter (fun u => ϖ ^ a ∣ Q u) := by
    rw [hR', Finset.filter_filter]
    exact Finset.filter_congr fun u hu => by rw [hZ, hdvd a u (hRU u hu), and_comm]
  have h := GlobalTheory.HL.CharCond.expand_by_conductor ϖ hϖ ψ hψ R' Q (fun _ => 1) a
    (fun i => (R.card : ℝ) * (resQ ϖ : ℝ) ^ (-(j * ρ : ℤ)) * (resQ ϖ : ℝ) ^ (-(((i - j : ℕ) : ℤ) * ρ)))
    (fun i hi hia t u₀ ht => by
      rw [Finset.sum_congr rfl fun u hu => by
        rw [hQ u (hRU u (Finset.mem_filter.1 hu).1), mul_one]]
      exact hg i (hia.trans haN) t u₀ ht)
  rw [hfil]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at h
  have h1 : ((R'.filter (fun u => ϖ ^ a ∣ Q u)).card : ℝ) * (resQ ϖ : ℝ) ^ a - R'.card ≤
      ‖((R'.filter (fun u => ϖ ^ a ∣ Q u)).card : ℂ) * (resQ ϖ : ℂ) ^ a - R'.card‖ := by
    refine (le_abs_self _).trans (le_of_eq ?_)
    rw [← Real.norm_eq_abs, ← Complex.norm_real]
    push_cast; rfl
  have h2 := (GlobalTheory.two_geometric_sums_index_bound (resQ ϖ) ρ a hq hρ).2 j
  have hq0 : (0 : ℝ) < resQ ϖ := by exact_mod_cast (by omega : 0 < resQ ϖ)
  have h3 := mul_le_mul_of_nonneg_left h2
    (by positivity : (0 : ℝ) ≤ (R.card : ℝ) * (resQ ϖ : ℝ) ^ (-(j * ρ : ℤ)))
  rw [mul_add, mul_one, Finset.mul_sum] at h3
  have h4 : ∑ i ∈ Finset.Icc 1 a, ((resQ ϖ : ℝ) ^ i - (resQ ϖ : ℝ) ^ (i - 1)) *
      ((R.card : ℝ) * (resQ ϖ : ℝ) ^ (-(j * ρ : ℤ)) * (resQ ϖ : ℝ) ^ (-(((i - j : ℕ) : ℤ) * ρ))) =
      ∑ i ∈ Finset.Icc 1 a, (R.card : ℝ) * (resQ ϖ : ℝ) ^ (-(j * ρ : ℤ)) *
      (((resQ ϖ : ℝ) ^ i - (resQ ϖ : ℝ) ^ (i - 1)) * (resQ ϖ : ℝ) ^ (-(((i - j : ℕ) : ℤ) * ρ))) :=
    Finset.sum_congr rfl fun i _ => by ring
  have h5 : 8 / 7 * (resQ ϖ : ℝ) ^ ((j : ℤ) - j * ρ) * R.card =
      (R.card : ℝ) * (resQ ϖ : ℝ) ^ (-(j * ρ : ℤ)) * (8 / 7 * (resQ ϖ : ℝ) ^ j) := by
    rw [sub_eq_add_neg, zpow_add₀ hq0.ne', zpow_natCast]; ring
  rw [h5]
  rw [h4] at h
  linarith

theorem leak_share (hH : IsHermND L Hm) (ϖ : 𝒪[F]) (hϖ : Irreducible ϖ)
    (UU : Submodule L.O (Fin n → E)) (hUU : ∀ x ∈ UU, ∀ y ∈ UU, hf L Hm x y ∈ L.O)
    (ρ : ℕ) (hρ : 4 ≤ ρ) (e : Fin ρ → Fin n → E) (W : Submodule L.O (Fin n → E)) (hW : W ≤ UU)
    (he : ∀ a, e a ∈ W)
    (hee : ∀ a b, hf L Hm (e a) (e b) = if a = b then 1 else 0) (a N : ℕ) (haN : a + 1 ≤ N)
    (R : Finset (Fin n → E)) (hRU : ∀ u ∈ R, u ∈ UU)
    (hR : ∀ u ∈ UU, ∃! w, w ∈ R ∧ ∃ y ∈ UU, u - w = algebraMap F E ((ϖ : F) ^ N) • y)
    (Z : (Fin n → E) → Prop)
    (hZ : ∀ u, Z u ↔ ∃ c : 𝒪[F], hf L Hm u u = algebraMap F E ((ϖ : F) ^ a * c)) :
    ((R.filter fun u => Z u ∧ ¬ ∃ y ∈ W, hf L Hm u y = 1).card : ℝ) * (resQ ϖ : ℝ) ^ a ≤
      16 / 7 * (resQ ϖ : ℝ) ^ (1 - (ρ : ℤ)) * R.card := by
  obtain ⟨-, hcj, -, -, hint, -, hq, -⟩ := GlobalTheory.UnramOrder.order_facts L ϖ hϖ
  have hq1 : (1 : ℝ) ≤ resQ ϖ := by exact_mod_cast (by omega : 1 ≤ resQ ϖ)
  have hp : algebraMap F E ϖ ∈ L.O := (hint _).2 ϖ.2
  have hps := prime_share L Hm hH ϖ hϖ UU hUU ρ hρ e (fun a => hW (he a)) hee a N (by omega) R hRU hR
    Z hZ
  have hI : ∀ u ∈ R, (¬ ∃ y ∈ W, hf L Hm u y = 1) → ∃ I : Ideal L.O, I ≠ ⊤ ∧
      ∀ a, ∃ x ∈ I, (x : E) = hf L Hm u (e a) := by
    intro u hu hne
    let I : Ideal L.O :=
      { carrier := {x | ∃ y ∈ W, hf L Hm u y = x}
        zero_mem' := ⟨0, W.zero_mem, by simp [hf]⟩
        add_mem' := by
          rintro x x' ⟨y, hy, e⟩ ⟨y', hy', e'⟩
          exact ⟨y + y', W.add_mem hy hy', by rw [hf_add_right, e, e']; rfl⟩
        smul_mem' := by
          rintro c x ⟨y, hy, e⟩
          refine ⟨L.cj c • y, CongFin.smul_mem_of W (hcj c c.2).1 hy, ?_⟩
          rw [hf_smul_right, L.cj_cj, e]; rfl }
    refine ⟨I, fun h => hne ((Ideal.eq_top_iff_one I).1 h), fun a => ?_⟩
    exact ⟨⟨_, hUU u (hRU u hu) _ (hW (he a))⟩, ⟨e a, he a, rfl⟩, rfl⟩
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  have hM : algebraMap F E ((ϖ : F) ^ M) ∈ L.O := by rw [map_pow]; exact L.O.pow_mem hp M
  have hqa : (0 : ℝ) ≤ (resQ ϖ : ℝ) ^ a := by positivity
  have hR0 : (0 : ℝ) ≤ R.card := Nat.cast_nonneg _
  rcases GlobalTheory.UnramOrder.proper_ideals L ϖ hϖ with h | ⟨π, hπ, hππ, h⟩
  · have h1 := hps (algebraMap F E ϖ) 2 hp (by rw [AlgEquiv.commutes, ← map_mul, sq])
      ⟨_, hM, by rw [← map_mul, pow_succ']⟩
    have hsub : (R.filter fun u => Z u ∧ ¬ ∃ y ∈ W, hf L Hm u y = 1) ⊆
        R.filter fun u => Z u ∧ ∀ a, ∃ c ∈ L.O, hf L Hm u (e a) = algebraMap F E ϖ * c := by
      intro u hu
      obtain ⟨hu, hz, hne⟩ := Finset.mem_filter.1 hu
      obtain ⟨I, hI, hIe⟩ := hI u hu hne
      refine Finset.mem_filter.2 ⟨hu, hz, fun a => ?_⟩
      obtain ⟨x, hx, e⟩ := hIe a
      exact e ▸ h I hI x hx
    have h2 : ((R.filter fun u => Z u ∧ ¬ ∃ y ∈ W, hf L Hm u y = 1).card : ℝ) ≤ _ :=
      Nat.cast_le.2 (Finset.card_le_card hsub)
    have h3 : (resQ ϖ : ℝ) ^ (((2 : ℕ) : ℤ) - (2 : ℕ) * ρ) ≤ (resQ ϖ : ℝ) ^ (1 - (ρ : ℤ)) :=
      zpow_le_zpow_right₀ hq1 (by push_cast; omega)
    have h4 : (0 : ℝ) ≤ (resQ ϖ : ℝ) ^ (1 - (ρ : ℤ)) := by positivity
    refine (mul_le_mul_of_nonneg_right h2 hqa).trans (h1.trans ?_)
    exact mul_le_mul_of_nonneg_right
      ((mul_le_mul_of_nonneg_left h3 (by norm_num)).trans (by linarith only [h4])) hR0
  · have h1 := hps π 1 hπ (by rw [hππ, pow_one])
      ⟨L.cj π * algebraMap F E ((ϖ : F) ^ M), L.O.mul_mem (hcj π hπ).1 hM, by
        rw [← mul_assoc, hππ, ← map_mul, pow_succ']⟩
    have h1' := hps (L.cj π) 1 (hcj π hπ).1 (by rw [L.cj_cj, mul_comm, hππ, pow_one])
      ⟨π * algebraMap F E ((ϖ : F) ^ M), L.O.mul_mem hπ hM, by
        rw [← mul_assoc, mul_comm _ π, hππ, ← map_mul, pow_succ']⟩
    have hsub : (R.filter fun u => Z u ∧ ¬ ∃ y ∈ W, hf L Hm u y = 1) ⊆
        (R.filter fun u => Z u ∧ ∀ a, ∃ c ∈ L.O, hf L Hm u (e a) = π * c) ∪
        (R.filter fun u => Z u ∧ ∀ a, ∃ c ∈ L.O, hf L Hm u (e a) = L.cj π * c) := by
      intro u hu
      obtain ⟨hu, hz, hne⟩ := Finset.mem_filter.1 hu
      obtain ⟨I, hI, hIe⟩ := hI u hu hne
      rcases h I hI with h | h
      · refine Finset.mem_union_left _ (Finset.mem_filter.2 ⟨hu, hz, fun a => ?_⟩)
        obtain ⟨x, hx, e⟩ := hIe a
        exact e ▸ h x hx
      · refine Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hu, hz, fun a => ?_⟩)
        obtain ⟨x, hx, e⟩ := hIe a
        exact e ▸ h x hx
    have h2 : ((R.filter fun u => Z u ∧ ¬ ∃ y ∈ W, hf L Hm u y = 1).card : ℝ) ≤ _ :=
      Nat.cast_le.2 ((Finset.card_le_card hsub).trans (Finset.card_union_le _ _))
    rw [Nat.cast_add] at h2
    have h3 := mul_le_mul_of_nonneg_right h2 hqa
    simp only [Nat.cast_one, one_mul] at h1 h1'
    rw [add_mul] at h3
    linarith

theorem integral_of_reps (ϖ : 𝒪[F]) (hϖ : Irreducible ϖ) (Λ : Submodule L.O (Fin n → E))
    (hΛ : IsSD L Hm Λ) (UU : Submodule L.O (Fin n → E)) (hUΛ : UU ≤ Λ) (N : ℕ) (hN : 1 ≤ N)
    (R : Finset (Fin n → E))
    (hR : ∀ u ∈ UU, ∃! w, w ∈ R ∧ ∃ y ∈ UU, u - w = algebraMap F E ((ϖ : F) ^ N) • y)
    (y : Fin n → E) (hy : ∀ u ∈ R, algebraMap F E ((ϖ : F) ^ N) * hf L Hm y u ∈ L.O) :
    ∀ u ∈ UU, algebraMap F E ((ϖ : F) ^ N) * hf L Hm y u ∈ L.O := by
  obtain ⟨-, -, -, -, hint, -, -, -⟩ := GlobalTheory.UnramOrder.order_facts L ϖ hϖ
  have hp : algebraMap F E ϖ ∈ L.O := (hint _).2 ϖ.2
  obtain ⟨M, hM⟩ := CongFin.exists_pow_smul_mem hp (CongFin.exists_pow_mul_mem L ϖ hϖ)
    (Submodule.span L.O {y}) Λ (Submodule.fg_span_singleton y) hΛ.1.2
  have hMy := hM y (Submodule.mem_span_singleton_self y)
  simp only [map_pow] at hR hy ⊢
  have hcp : L.cj (algebraMap F E ϖ ^ N) = algebraMap F E ϖ ^ N := by
    rw [map_pow, AlgEquiv.commutes]
  set p := algebraMap F E ϖ with hpdef
  have key : ∀ m : ℕ, (∀ u ∈ UU, p ^ m * (p ^ N * hf L Hm y u) ∈ L.O) →
      ∀ u ∈ UU, p ^ N * hf L Hm y u ∈ L.O := by
    intro m
    induction m with
    | zero => intro h u hu; simpa using h u hu
    | succ m ih =>
      intro h
      refine ih fun u hu => ?_
      obtain ⟨w, ⟨hw, z, hz, e⟩, -⟩ := hR u hu
      have e' : u = w + p ^ N • z := by rw [← e]; abel
      obtain ⟨K, rfl⟩ : ∃ K, N = K + 1 := ⟨N - 1, by omega⟩
      rw [e', hf_add_right, hf_smul_right, hcp]
      have := L.O.add_mem (L.O.mul_mem (L.O.pow_mem hp m) (hy w hw))
        (L.O.mul_mem (L.O.pow_mem hp K) (h z hz))
      convert this using 1
      ring
  refine key M fun u hu => ?_
  have h1 := (hΛ.2 u).2 (hUΛ hu) _ hMy
  rw [hf_smul_left] at h1
  rw [mul_left_comm]
  exact L.O.mul_mem (L.O.pow_mem hp N) h1

omit [IsNonarchimedeanLocalField F] [CharZero F] in
theorem perp_anti {A B : Submodule E (Fin n → E)} (h : A ≤ B) : perp L Hm B ≤ perp L Hm A :=
  fun _ hx y hy => hx y (h hy)

theorem shares : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), 4 * r + 7 ≤ k → ∀ (J : ℕ) (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → ∀ (N : ℕ) (R : Finset S.V) (Z : S.V → Prop), S.a + 1 ≤ N → (∀ u, Z u ↔ ∃ c : 𝒪[F], S.h u u = algebraMap F E ((S.ϖ : F) ^ S.a * c)) → (∀ u ∈ R, u ∈ Λ ∧ u ∈ perp L S.Hm (S.spanTo S.f J ⊔ S.spanTo S.f' J)) → (∀ u ∈ Λ, u ∈ perp L S.Hm (S.spanTo S.f J ⊔ S.spanTo S.f' J) → ∃! w, w ∈ R ∧ ∃ y ∈ Λ, u - w = algebraMap F E ((S.ϖ : F) ^ N) • y) → |((R.filter Z).card : ℝ) - R.card / (S.q : ℝ) ^ S.a| ≤ 8 / 7 * (S.q : ℝ) ^ (1 - ((k : ℤ) - 2 * r - 3)) * (R.card / (S.q : ℝ) ^ S.a) ∧ (((R.filter fun u => Z u ∧ ¬ ∃ y ∈ Λ, y ∈ S.W0 ∧ S.h u y = 1).card : ℝ) ≤ 16 / 7 * (S.q : ℝ) ^ (1 - ((k : ℤ) - 2 * r - 3)) * (R.card / (S.q : ℝ) ^ S.a)) ∧ ∀ y : S.V, (∀ u ∈ R, algebraMap F E ((S.ϖ : F) ^ N) * S.h y u ∈ L.O) → (∃ u ∈ R, L.psi0 (S.h y u) ≠ 1) → ‖∑ u ∈ R.filter Z, L.psi0 (S.h y u)‖ ≤ 8 / 7 * (S.q : ℝ) ^ (1 - ((k : ℤ) - 2 * r - 3)) * (R.card / (S.q : ℝ) ^ S.a) := by
  intro F _ _ _ _ _ E _ _ _ L r k S hk J d Λ hT N R Z haN hZ hRU hR
  obtain ⟨-, hcj, -, -, hint, -, hq, -⟩ := GlobalTheory.UnramOrder.order_facts L S.ϖ S.ϖ_irr
  have hSD := (GlobalTheory.HL.TermBasic.term_basic L r k S d Λ hT).1
  have hli := (GlobalTheory.FrameBasic.main L r k S).1
  obtain ⟨a, ha⟩ := Int.eq_ofNat_of_zero_le (GlobalTheory.T.term_exponents_nonneg_and_defect_group_bound L r k S d Λ hT).1
  rw [ha] at haN hZ ⊢
  simp only [zpow_natCast] at hZ ⊢
  have haN' : a + 1 ≤ N := by omega
  obtain ⟨e, he, hee⟩ := GlobalTheory.HL.OrthCompl.exists_orthonormal_perp L S.Hm S.herm Λ hSD _ _
    (hli.comp finSumFinEquiv.symm finSumFinEquiv.symm.injective)
  have hsp : ∀ j, S.spanTo S.f j ⊔ S.spanTo S.f' j ≤
      Submodule.span E (Set.range (Sum.elim S.f S.f' ∘ finSumFinEquiv.symm)) := by
    intro j
    rw [finSumFinEquiv.symm.surjective.range_comp]
    refine sup_le (Submodule.span_mono ?_) (Submodule.span_mono ?_)
    · rintro _ ⟨i, -, rfl⟩; exact ⟨Sum.inl i, rfl⟩
    · rintro _ ⟨i, -, rfl⟩; exact ⟨Sum.inr i, rfl⟩
  let ρ := k + 2 * r + 1 - 2 * (r + 1 + (r + 1))
  have hρdef : ρ = k + 2 * r + 1 - 2 * (r + 1 + (r + 1)) := rfl
  have hρ : 4 ≤ ρ := by omega
  have hρ' : (k : ℤ) - 2 * r - 3 = ρ := by omega
  rw [hρ']
  let UU : Submodule L.O S.V :=
    Λ ⊓ (perp L S.Hm (S.spanTo S.f J ⊔ S.spanTo S.f' J)).restrictScalars L.O
  let W : Submodule L.O S.V := Λ ⊓ S.W0.restrictScalars L.O
  have hJ : S.spanTo S.f J ⊔ S.spanTo S.f' J ≤ S.ME :=
    sup_le_sup (Submodule.span_mono (Set.image_mono fun i _ => i.2))
      (Submodule.span_mono (Set.image_mono fun i _ => i.2))
  have hW : W ≤ UU := fun x hx => ⟨hx.1, perp_anti L S.Hm hJ hx.2⟩
  have heW : ∀ i, e i ∈ W := fun i => ⟨(he i).1, perp_anti L S.Hm (hsp (r + 1)) (he i).2⟩
  have hUU : ∀ x ∈ UU, ∀ y ∈ UU, hf L S.Hm x y ∈ L.O := fun x hx y hy => (hSD.2 y).2 hy.1 x hx.1
  have hRU' : ∀ u ∈ R, u ∈ UU := hRU
  have hu : IsUnit (algebraMap F E ((S.ϖ : F) ^ N)) :=
    ((IsUnit.mk0 (S.ϖ : F) (fun h => S.ϖ_irr.ne_zero (Subtype.ext h))).pow N).map _
  have hR' : ∀ u ∈ UU, ∃! w, w ∈ R ∧ ∃ y ∈ UU, u - w = algebraMap F E ((S.ϖ : F) ^ N) • y := by
    intro u hu'
    refine (existsUnique_congr fun w => and_congr_right fun hw => ?_).1 (hR u hu'.1 hu'.2)
    constructor
    · rintro ⟨y, hy, e⟩
      refine ⟨y, ⟨hy, ?_⟩, e⟩
      have h1 : algebraMap F E ((S.ϖ : F) ^ N) • y ∈
          perp L S.Hm (S.spanTo S.f J ⊔ S.spanTo S.f' J) :=
        e ▸ Submodule.sub_mem _ hu'.2 (hRU w hw).2
      exact (Submodule.smul_mem_iff_of_isUnit _ hu).1 h1
    · rintro ⟨y, hy, e⟩
      exact ⟨y, hy.1, e⟩
  have hcs := char_share L S.Hm S.herm S.ϖ S.ϖ_irr UU hUU ρ hρ e (fun i => hW (heW i)) hee a N
    (by omega) R hRU' hR' Z hZ
  have hqa : (0 : ℝ) < (S.q : ℝ) ^ a := by
    have : (0 : ℝ) < S.q := by exact_mod_cast (by omega : 0 < resQ S.ϖ)
    positivity
  refine ⟨?_, ?_, fun y hy ⟨u₀, hu₀, hne⟩ => ?_⟩
  · have h := hcs 1 (by simp) (by simp)
    simp only [AddChar.one_apply, Finset.sum_const, nsmul_eq_mul, mul_one] at h
    have h1 : ‖((R.filter Z).card : ℂ) * (resQ S.ϖ : ℂ) ^ a - R.card‖ =
        |((R.filter Z).card : ℝ) * (S.q : ℝ) ^ a - R.card| := by
      rw [← Real.norm_eq_abs, ← Complex.norm_real]
      push_cast; rfl
    rw [h1] at h
    rw [← mul_div_assoc, le_div_iff₀ hqa, ← abs_of_pos hqa, ← abs_mul, abs_of_pos hqa, sub_mul,
      div_mul_cancel₀ _ hqa.ne']
    exact h
  · have h := leak_share L S.Hm S.herm S.ϖ S.ϖ_irr UU hUU ρ hρ e W hW heW hee a N haN' R hRU' hR' Z hZ
    rw [← mul_div_assoc, le_div_iff₀ hqa]
    refine le_trans (mul_le_mul_of_nonneg_right (Nat.cast_le.2 (Finset.card_le_card ?_)) hqa.le) h
    intro u hu'
    simp only [Finset.mem_filter] at hu' ⊢
    refine ⟨hu'.1, hu'.2.1, ?_⟩
    rintro ⟨y, ⟨h1, h2⟩, h3⟩
    exact hu'.2.2 ⟨y, h1, h2, h3⟩
  · obtain ⟨ψ, hψ1, -, hψ⟩ := GlobalTheory.TraceChar.exists_trace_char L
    let φ : S.V →+ E := AddMonoidHom.mk' (fun u => hf L S.Hm y u) (hf_add_right L S.Hm y)
    let χ : AddChar S.V ℂ := L.psi0.compAddMonoidHom φ
    have hχ1 : ∀ u, ‖χ u‖ = 1 := fun u => by
      obtain ⟨c, hc⟩ := (L.cj_fix (φ u + L.cj (φ u))).1 (by rw [map_add, L.cj_cj, add_comm])
      change ‖L.psi0 (φ u)‖ = 1
      rw [hψ _ c hc.symm, hψ1]
    have hint' := integral_of_reps L S.Hm S.ϖ S.ϖ_irr Λ hSD UU inf_le_left N (by omega) R hR' y hy
    have hχ : ∀ u ∈ UU, χ (algebraMap F E ((S.ϖ : F) ^ N) • u) = 1 := fun u hu' => by
      change L.psi0 (hf L S.Hm y _) = 1
      rw [hf_smul_right, AlgEquiv.commutes]
      simpa using (L.additive_character_dual_ring _).2 (hint' u hu') 1 L.O.one_mem
    have h := hcs χ hχ1 hχ
    rw [sum_char_eq_zero UU _ R hRU' hR' χ hχ u₀ hu₀ hne, sub_zero, norm_mul, norm_pow,
      Complex.norm_natCast] at h
    rw [← mul_div_assoc, le_div_iff₀ hqa]
    exact h

end GlobalTheory.HL.QuadricShare
