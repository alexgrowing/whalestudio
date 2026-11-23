import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.AllLeaves
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UfamConst
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.UnipotentVanishing.InfAtUnipInvEqZero
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.NormalisedExistence.ExistsNormed

open scoped ENNReal
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology Polynomial
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs GlobalTheory.CompanionTheory.Conc
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Global GroundTheory.Automorphic.CuspidalSpectrum

noncomputable section

namespace GlobalTheory.CompanionTheory.ConcCount

variable {K : Type} [Field K] [NumberField K] {n : ℕ}

theorem detModule_conj (b a c : AdelicGLn.AdelicGL K n) :
    detModule K n (b * a * c * a⁻¹ * b⁻¹) = detModule K n c := by
  simp only [map_mul, map_inv]
  generalize detModule K n b = u
  generalize detModule K n a = v
  generalize detModule K n c = w
  calc u * v * w * v⁻¹ * u⁻¹ = (u * u⁻¹) * (v * v⁻¹) * w := by
        simp only [mul_comm, mul_left_comm, mul_assoc]
    _ = w := by simp

theorem exponent_mem (hn : 0 < n) {Q : Set (AdelicGLn.AdelicGL K n)} (hQ : IsCompact Q) :
    ∃ M : Finset ℤ, ∀ (b : AdelicGLn.AdelicGL K n) (x : Fin n → ℝ), ∀ c ∈ Q, ∀ (γ₀ : GL (Fin n) K) (m : ℤ),
      AdelicGLn.diagonal K n γ₀ * count.cen K n ^ m = b * An.tor K x * c * (An.tor K x)⁻¹ * b⁻¹ → m ∈ M := by
  have hdc : Continuous fun g : AdelicGLn.AdelicGL K n => (detModule K n g : ℝ) :=
    continuous_subtype_val.comp continuous_detModule
  obtain ⟨a, b, ha, -, hab⟩ := Reduction.exists_pos_bounds hQ hdc (fun g _ => (detModule K n g).2)
  have hN : 0 < (n : ℝ) * (Module.finrank ℚ K : ℝ) :=
    mul_pos (Nat.cast_pos.2 hn) (Nat.cast_pos.2 Module.finrank_pos)
  set N : ℝ := (n : ℝ) * (Module.finrank ℚ K : ℝ) with hNdef
  refine ⟨Finset.Icc ⌊Real.log a / N⌋ ⌈Real.log b / N⌉, ?_⟩
  intro g x q hq γ₀ m h
  have h1 := congrArg (fun g => (detModule K n g : ℝ)) h
  beta_reduce at h1
  rw [GlobalTheory.CompanionTheory.Latexp.detModule_lhs, detModule_conj] at h1
  obtain ⟨h2, h3⟩ := hab q hq
  rw [← h1] at h2 h3
  have h4 : Real.log a ≤ (m : ℝ) * N := (Real.log_le_iff_le_exp ha).2 h2
  have h5 : (m : ℝ) * N ≤ Real.log b := by
    have hb : 0 < b := lt_of_lt_of_le (Real.exp_pos _) h3
    exact (Real.le_log_iff_exp_le hb).2 h3
  rw [Finset.mem_Icc]
  constructor
  · have : Real.log a / N ≤ (m : ℝ) := (div_le_iff₀ hN).2 h4
    exact Int.cast_le.1 ((Int.floor_le _).trans this)
  · have : (m : ℝ) ≤ Real.log b / N := (le_div_iff₀ hN).2 h5
    exact Int.cast_le.1 (this.trans (Int.le_ceil _))

theorem exists_fin_bound {W Q : Set (AdelicGLn.AdelicGL K n)} (hW : IsCompact W) (hQ : IsCompact Q) :
    ∃ 𝒦 : Set (FiniteAdeleRing (𝓞 K) K), IsCompact 𝒦 ∧ ∀ x : Fin n → ℝ, ∀ b ∈ W, ∀ c ∈ Q, ∀ γ : GL (Fin n) K,
      AdelicGLn.diagonal K n γ = b * An.tor K x * c * (An.tor K x)⁻¹ * b⁻¹ →
      ∀ i j, algebraMap K (FiniteAdeleRing (𝓞 K) K) ((γ : Matrix (Fin n) (Fin n) K) i j) ∈ 𝒦 := by
  refine ⟨⋃ i : Fin n, ⋃ j : Fin n,
    (fun p : AdelicGLn.AdelicGL K n × AdelicGLn.AdelicGL K n =>
      ((AdelicGLn.prodEquiv K n (p.1 * p.2 * p.1⁻¹)).2 :
        Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 K) K)) i j) '' (W ×ˢ Q), ?_, ?_⟩
  · refine isCompact_iUnion fun i => isCompact_iUnion fun j => (hW.prod hQ).image ?_
    exact ((continuous_apply j).comp (continuous_apply i)).comp (Units.continuous_val.comp
      (continuous_snd.comp ((AdelicGLn.prodEquiv K n).continuous.comp
        ((continuous_fst.mul continuous_snd).mul continuous_fst.inv))))
  · intro x b hb c hc γ hγ i j
    have hA : (AdelicGLn.prodEquiv K n (An.tor K x)).2 = 1 :=
      prodEquiv_diagUnits_posIdele_snd _ _
    have e1 : algebraMap K (FiniteAdeleRing (𝓞 K) K) ((γ : Matrix (Fin n) (Fin n) K) i j) =
        ((AdelicGLn.prodEquiv K n (b * An.tor K x * c * (An.tor K x)⁻¹ * b⁻¹)).2 :
          Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 K) K)) i j := by
      rw [← hγ, AdelicGLn.prodEquiv_apply_snd, AdelicGLn.diagonal_apply]
      rfl
    rw [e1]
    refine Set.mem_iUnion₂.2 ⟨i, j, (b, c), ⟨hb, hc⟩, ?_⟩
    simp only [map_mul, map_inv, Prod.snd_mul, Prod.snd_inv, hA, mul_one, inv_one]

theorem exists_inf_bound {W Q : Set (AdelicGLn.AdelicGL K n)} (hW : IsCompact W) (hQ : IsCompact Q) :
    ∃ β : ℝ, 0 ≤ β ∧ ∀ (x : Fin n → ℝ) (L : ℝ), 0 ≤ L → (∀ l m, Real.exp (x l) / Real.exp (x m) ≤ L) →
      ∀ b ∈ W, ∀ c ∈ Q, ∀ γ : GL (Fin n) K,
      AdelicGLn.diagonal K n γ = b * An.tor K x * c * (An.tor K x)⁻¹ * b⁻¹ →
      ∀ i j, ∀ w : InfinitePlace K, w ((γ : Matrix (Fin n) (Fin n) K) i j) ≤ β * L := by
  obtain ⟨β₁, hβ₁0, hβ₁⟩ := exists_norm_infAt_entry_le hW
  obtain ⟨β₂, hβ₂0, hβ₂⟩ := exists_norm_infAt_entry_le hQ
  obtain ⟨β₃, hβ₃0, hβ₃⟩ := exists_norm_infAt_entry_le (hW.image (continuous_inv (G := AdelicGLn.AdelicGL K n)))
  refine ⟨(n : ℝ) ^ 2 * (β₁ * β₂ * β₃), by positivity, ?_⟩
  intro x L hL0 hL b hb c hc γ hγ i j w
  have e1 : w ((γ : Matrix (Fin n) (Fin n) K) i j) =
      ‖(infAt w (b * An.tor K x * c * (An.tor K x)⁻¹ * b⁻¹) :
        Matrix (Fin n) (Fin n) w.Completion) i j‖ := by
    rw [infAt_apply, ← hγ, AdelicGLn.diagonal_apply, ← GroundTheory.Global.norm_algebraMap_apply]
    rfl
  rw [e1]
  have key := count.norm_entry_le w b c b⁻¹ x (L := L) i j (hβ₁ b hb w) (hβ₂ c hc w)
    (hβ₃ _ ⟨b, hb, rfl⟩ w) hβ₁0 hβ₂0 hβ₃0 hL0 (fun l m _ _ => hL l m)
  refine le_trans key (le_of_eq ?_)
  ring

theorem sub_eq_sum (x : Fin n → ℝ) (i j : ℕ) (hij : i ≤ j) (hj : j < n) :
    x ⟨i, by omega⟩ - x ⟨j, hj⟩ = ∑ r ∈ Finset.Ioc i j, An.sr x r := by
  induction j, hij using Nat.le_induction with
  | base => simp
  | succ j hij ih =>
    have hj' : j < n := by omega
    rw [Finset.sum_Ioc_succ_top hij, ← ih hj']
    have : An.sr x (j + 1) = x ⟨j, hj'⟩ - x ⟨j + 1, hj⟩ := by
      unfold An.sr
      rw [dif_pos ⟨by omega, hj⟩]
      rfl
    rw [this]
    ring

theorem sub_le_sum (x : Fin n → ℝ) {t : ℝ} (ht0 : 0 ≤ t) (ht : ∀ r, -t ≤ An.sr x r) (l m : Fin n) :
    x l - x m ≤ ∑ r ∈ Finset.range n, An.sr x r + 2 * n * t := by
  have hf : ∀ r, 0 ≤ An.sr x r + t := fun r => by linarith [ht r]
  have htot : ∑ r ∈ Finset.range n, (An.sr x r + t) = ∑ r ∈ Finset.range n, An.sr x r + n * t := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hnn : 0 ≤ ∑ r ∈ Finset.range n, An.sr x r + n * t := htot ▸ Finset.sum_nonneg fun r _ => hf r
  have hnt : 0 ≤ (n : ℝ) * t := by positivity
  rcases le_total (l : ℕ) (m : ℕ) with h | h
  · have e := sub_eq_sum x l m h m.2
    have hsub : Finset.Ioc (l : ℕ) m ⊆ Finset.range n := fun r hr => by
      have := Finset.mem_Ioc.1 hr
      have := m.2
      exact Finset.mem_range.2 (by omega)
    have h1 : ∑ r ∈ Finset.Ioc (l : ℕ) m, An.sr x r ≤ ∑ r ∈ Finset.Ioc (l : ℕ) m, (An.sr x r + t) :=
      Finset.sum_le_sum fun r _ => by linarith
    have h2 := Finset.sum_le_sum_of_subset_of_nonneg (f := fun r => An.sr x r + t) hsub (fun r _ _ => hf r)
    have e' : x l - x m = ∑ r ∈ Finset.Ioc (l : ℕ) m, An.sr x r := e
    linarith
  · have e := sub_eq_sum x m l h l.2
    have e' : x m - x l = ∑ r ∈ Finset.Ioc (m : ℕ) l, An.sr x r := e
    have h1 : -(((Finset.Ioc (m : ℕ) l).card : ℝ) * t) ≤ ∑ r ∈ Finset.Ioc (m : ℕ) l, An.sr x r := by
      have := Finset.card_nsmul_le_sum (Finset.Ioc (m : ℕ) l) (fun r => An.sr x r) (-t) (fun r _ => ht r)
      simpa using this
    have h2 : ((Finset.Ioc (m : ℕ) l).card : ℝ) * t ≤ n * t := by
      refine mul_le_mul_of_nonneg_right ?_ ht0
      rw [Nat.card_Ioc]
      have := l.2
      exact_mod_cast (by omega : (l : ℕ) - m ≤ n)
    linarith

theorem count_core (hn : 0 < n) {Q' ω Q : Set (AdelicGLn.AdelicGL K n)} (t₀ : ℝ) (hQ' : IsCompact Q')
    (hω : IsCompact ω) (hQ : IsCompact Q) :
    ∃ C : ℝ, ∀ b ∈ ω, ∀ x : Fin n → ℝ, (∀ r, -t₀ ≤ An.sr x r) → ∀ q ∈ Q,
      {γ : AdelicGLn.AdelicGL K n | γ ∈ An.lat K n ∧ ∃ a ∈ Q', ∃ a' ∈ Q',
        γ = (b * An.tor K x * q) * a * a'⁻¹ * (b * An.tor K x * q)⁻¹}.encard ≤
      (⌈C * Real.exp (((n : ℝ) ^ 2 * (Module.finrank ℚ K : ℝ)) * ∑ r ∈ Finset.range n, An.sr x r)⌉₊ : ℕ) := by
  classical
  set c := count.cen K n with hc
  set Qc : Set (AdelicGLn.AdelicGL K n) :=
    (fun p : AdelicGLn.AdelicGL K n × AdelicGLn.AdelicGL K n × AdelicGLn.AdelicGL K n =>
      p.1 * p.2.1 * p.2.2⁻¹ * p.1⁻¹) '' (Q ×ˢ Q' ×ˢ Q') with hQc_def
  have hQc : IsCompact Qc := (hQ.prod (hQ'.prod hQ')).image
    (((continuous_fst.mul (continuous_fst.comp continuous_snd)).mul
      (continuous_snd.comp continuous_snd).inv).mul continuous_fst.inv)
  obtain ⟨M, hM⟩ := exponent_mem hn hQc
  set Qd : Set (AdelicGLn.AdelicGL K n) := ⋃ m ∈ M, (fun q => c ^ (-m) * q) '' Qc with hQd_def
  have hQd : IsCompact Qd := M.isCompact_biUnion fun m _ => hQc.image (continuous_const.mul continuous_id)
  obtain ⟨𝒦, h𝒦, hfinb⟩ := exists_fin_bound hω hQd
  obtain ⟨β, hβ, hinfb⟩ := exists_inf_bound hω hQd
  obtain ⟨C₀, hC₀, hbox⟩ := count.exists_ncard_box_le K n h𝒦
  set d := Module.finrank ℚ K with hd
  set t : ℝ := |t₀| with ht
  have ht0 : 0 ≤ t := abs_nonneg _
  set A : ℝ := Real.exp (n * t) + β * Real.exp (2 * n * t) with hA
  have hA0 : 0 ≤ A := by positivity
  refine ⟨M.card * (C₀ ^ (n * n) * A ^ (d * (n * n))), fun b hb x hx q hq => ?_⟩
  have hx' : ∀ r, -t ≤ An.sr x r := fun r => by
    have := le_abs_self t₀
    linarith [hx r]
  set S : ℝ := ∑ r ∈ Finset.range n, An.sr x r with hS
  have hSnn : 0 ≤ S + n * t := by
    have h1 : ∑ r ∈ Finset.range n, (An.sr x r + t) = S + n * t := by
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rw [← h1]
    exact Finset.sum_nonneg fun r _ => by linarith [hx' r]
  set L : ℝ := Real.exp (S + 2 * n * t) with hL
  have hL0 : 0 ≤ L := (Real.exp_pos _).le
  have hratio : ∀ l m, Real.exp (x l) / Real.exp (x m) ≤ L := fun l m => by
    rw [← Real.exp_sub]
    exact Real.exp_le_exp.2 (sub_le_sum x ht0 hx' l m)
  set T : Fin n → Fin n → ℝ := fun _ _ => β * L with hT
  obtain ⟨hfin, hcard⟩ := hbox T (fun i j => by simp only [T]; positivity)
  set B := hfin.toFinset
  set g : ℤ × GL (Fin n) K → AdelicGLn.AdelicGL K n := fun p => AdelicGLn.diagonal K n p.2 * c ^ p.1
  set St := {γ : AdelicGLn.AdelicGL K n | γ ∈ An.lat K n ∧ ∃ a ∈ Q', ∃ a' ∈ Q',
        γ = (b * An.tor K x * q) * a * a'⁻¹ * (b * An.tor K x * q)⁻¹}
  have hsub : St ⊆ (((M ×ˢ B).image g : Finset _) : Set (AdelicGLn.AdelicGL K n)) := by
    rintro γ ⟨hγl, a, ha, a', ha', hγ⟩
    obtain ⟨γ₀, m, hγm⟩ := count.mem_lat hγl
    set cc := q * a * a'⁻¹ * q⁻¹ with hcc_def
    have hcc : cc ∈ Qc := ⟨(q, a, a'), ⟨hq, ha, ha'⟩, rfl⟩
    have hγ' : γ = b * An.tor K x * cc * (An.tor K x)⁻¹ * b⁻¹ := by
      rw [hγ, hcc_def]
      group
    have hm : m ∈ M := hM b x cc hcc γ₀ m (hγm.symm.trans hγ')
    have h0 : AdelicGLn.diagonal K n γ₀ =
        b * An.tor K x * (c ^ (-m) * cc) * (An.tor K x)⁻¹ * b⁻¹ := by
      have e1 : AdelicGLn.diagonal K n γ₀ = γ * c ^ (-m) := by
        rw [hγm, mul_assoc, ← _root_.zpow_add, add_neg_cancel, zpow_zero, mul_one]
      rw [e1, hγ']
      have e2 := count.cen_zpow_comm (-m) (cc * (An.tor K x)⁻¹ * b⁻¹)
      simp only [mul_assoc] at e2 ⊢
      rw [e2]
    have hq' : c ^ (-m) * cc ∈ Qd := Set.mem_biUnion hm ⟨cc, hcc, rfl⟩
    have hB : γ₀ ∈ B := by
      rw [Set.Finite.mem_toFinset]
      intro i j
      exact ⟨hfinb x b hb _ hq' γ₀ h0 i j, fun w => hinfb x L hL0 hratio b hb _ hq' γ₀ h0 i j w⟩
    rw [Finset.coe_image]
    exact ⟨(m, γ₀), Finset.mem_coe.2 (Finset.mem_product.2 ⟨hm, hB⟩), hγm.symm⟩
  have h1T : 1 + β * L ≤ A * Real.exp S := by
    have e1 : (1 : ℝ) ≤ Real.exp (n * t) * Real.exp S := by
      rw [← Real.exp_add]
      exact Real.one_le_exp (by linarith)
    have e2 : L = Real.exp (2 * n * t) * Real.exp S := by
      rw [hL, ← Real.exp_add, add_comm]
    rw [e2, hA]
    nlinarith
  have hB : (B.card : ℝ) ≤ C₀ ^ (n * n) * A ^ (d * (n * n)) * Real.exp (((n : ℝ) ^ 2 * (d : ℝ)) * S) := by
    rw [← Set.ncard_eq_toFinset_card _ hfin]
    refine hcard.trans ?_
    simp only [T, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [← pow_mul]
    have e3 : Real.exp (((n : ℝ) ^ 2 * (d : ℝ)) * S) = Real.exp S ^ (d * (n * n)) := by
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    rw [e3, mul_assoc, ← mul_pow]
    rw [mul_pow]
    refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hC₀ _)
    rw [← pow_mul]
    exact pow_le_pow_left₀ (by positivity) h1T _
  have hnat : (((M ×ˢ B).image g).card : ℝ) ≤
      M.card * (C₀ ^ (n * n) * A ^ (d * (n * n))) * Real.exp (((n : ℝ) ^ 2 * (d : ℝ)) * S) := by
    calc (((M ×ˢ B).image g).card : ℝ) ≤ ((M ×ˢ B).card : ℝ) := by exact_mod_cast Finset.card_image_le
      _ = M.card * B.card := by rw [Finset.card_product, Nat.cast_mul]
      _ ≤ M.card * (C₀ ^ (n * n) * A ^ (d * (n * n)) * Real.exp (((n : ℝ) ^ 2 * (d : ℝ)) * S)) := by gcongr
      _ = _ := by ring
  calc St.encard ≤ ((((M ×ˢ B).image g : Finset _) : Set (AdelicGLn.AdelicGL K n))).encard := Set.encard_le_encard hsub
    _ = (((M ×ˢ B).image g).card : ℕ∞) := Set.encard_coe_eq_coe_finsetCard _
    _ ≤ _ := by
      have := Nat.le_ceil (M.card * (C₀ ^ (n * n) * A ^ (d * (n * n))) * Real.exp (((n : ℝ) ^ 2 * (d : ℝ)) * S))
      have h2 : ((M ×ˢ B).image g).card ≤ ⌈M.card * (C₀ ^ (n * n) * A ^ (d * (n * n))) * Real.exp (((n : ℝ) ^ 2 * (d : ℝ)) * S)⌉₊ := by
        exact_mod_cast hnat.trans this
      exact_mod_cast h2

theorem count_conj_siegel : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (N : ℕ), ∃ M : ℝ, 0 ≤ M ∧ ∀ (Q' : Set (GA E N)) (ω : Set (GA E N)) (t₀ : ℝ)
  (Q : Set (GA E N)), IsCompact Q' → IsCompact ω → ω ⊆ (adelicBorel (K := E) (n := N) : Set _) → IsCompact Q → ∃ C : ℝ, ∀ b ∈ ω, ∀ x : Fin N → ℝ,
    (∀ r, -t₀ ≤ An.sr x r) → ∀ q ∈ Q,
    {γ : GA E N | γ ∈ latticeGL E N ∧ ∃ a ∈ Q', ∃ a' ∈ Q', γ = (b * An.tor E x * q) * a * a'⁻¹ * (b * An.tor E x * q)⁻¹}.encard ≤
      (⌈C * Real.exp (M * ∑ r ∈ Finset.range N, An.sr x r)⌉₊ : ℕ) := by
  intro E _ _ _ N
  refine ⟨(N : ℝ) ^ 2 * (Module.finrank ℚ E : ℝ), by positivity, ?_⟩
  intro Q' ω t₀ Q hQ' hω _ hQ
  have hS : splitCentre E N 1 = An.tor E fun _ => 1 := (PositivityTheory.Rg.Rs.JDict.tor_const N 1).symm
  have hLat : latticeGL E N = An.lat E N := by
    unfold latticeGL An.lat
    rw [hS]
    rfl
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · refine ⟨1, fun b _ x _ q _ => ?_⟩
    have hsub : Subsingleton (GA E 0) := ⟨fun u v => Units.ext (Subsingleton.elim _ _)⟩
    refine (Set.encard_le_one_iff_subsingleton.2 (Set.subsingleton_of_subsingleton)).trans ?_
    simp
  · obtain ⟨C, hC⟩ := count_core (K := E) hN (Q' := Q') (ω := ω) (Q := Q) t₀ hQ' hω hQ
    refine ⟨C, fun b hb x hx q hq => ?_⟩
    rw [hLat]
    exact hC b hb x hx q hq

end GlobalTheory.CompanionTheory.ConcCount
