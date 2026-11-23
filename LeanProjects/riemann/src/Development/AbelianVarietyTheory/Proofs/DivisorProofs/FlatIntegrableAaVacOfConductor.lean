import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.InvVolConjLevelOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasCompactSupportFlatIntegrand
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatesEqPrimFrameLat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnfoldingTermCoefEqResidueCardZpowStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OriginDatumValueHalfIntegerPowPlaceAAStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MeasureTheory
open scoped TensorProduct nonZeroDivisors

namespace GlobalTheory.FunObj

open GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.StdFrames Formalism.L2.Host Formalism.L2.DIV ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

section Gen
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem apow_zpow (x : kˣ) (n : ℤ) (z : ℂ) : apow (x ^ n) z = apow x (n * z) := by
  induction n using Int.induction_on with
  | zero => simp [apow, nabs_one]
  | succ n ih =>
    rw [_root_.zpow_add_one, apow_mul, ih, ← apow_add]
    congr 1; push_cast; ring
  | pred n ih =>
    rw [_root_.zpow_sub_one, apow_mul, ih, apow_inv, ← apow_add]
    congr 1; push_cast; ring

theorem prod_apow {α : Type*} (x : kˣ) (f : α → ℂ) (l : List α) :
    (l.map fun b => apow x (f b)).prod = apow x (l.map f).sum := by
  induction l with
  | nil => simp [apow]
  | cons b l ih => rw [List.map_cons, List.prod_cons, ih, List.map_cons, List.sum_cons, apow_add]

end Gen

theorem even_mul_add_odd (a d : ℕ) (hd : Odd d) : Even (a * (a + d)) := by
  rcases Nat.even_or_odd a with h | h
  · exact h.mul_right _
  · exact (h.add_odd hd).mul_left _

theorem even_sum_of_even {α : Type*} (P : α → ℕ) : ∀ l : List α, (∀ b ∈ l, Even (P b)) → Even (l.map P).sum
  | [], _ => by simp
  | b :: l, h => by
    rw [List.map_cons, List.sum_cons]
    exact (h b List.mem_cons_self).add (even_sum_of_even P l fun c hc => h c (List.mem_cons_of_mem _ hc))

variable {D : D7}

theorem mem_oppositePath {m : ℕ} {b : Edge} : b ∈ oppositePath m ↔ (∃ i < m, b = .ex i m) ∨ ∃ j < m, b = .theta m j := by
  simp only [oppositePath, List.mem_append, List.mem_map, List.mem_range, List.mem_reverse]
  constructor
  · rintro (⟨i, hi, rfl⟩ | ⟨j, hj, rfl⟩)
    · exact Or.inl ⟨i, hi, rfl⟩
    · exact Or.inr ⟨j, hj, rfl⟩
  · rintro (⟨i, hi, rfl⟩ | ⟨j, hj, rfl⟩)
    · exact Or.inl ⟨i, hi, rfl⟩
    · exact Or.inr ⟨j, hj, rfl⟩

theorem even_rank_mul_path (w : Pl D.host.E) {b : Edge} (hb : b ∈ oppositePath (bareGrid w).m) :
    Even ((bareGrid w).rank b.src * (bareGrid w).rank b.tgt) := by
  rcases mem_oppositePath.1 hb with ⟨i, -, rfl⟩ | ⟨j, -, rfl⟩
  · have := even_mul_add_odd ((bareGrid w).rank (i, (bareGrid w).m)) (sLen D) (odd_sLen D)
    convert this using 2
    simp only [Grid.rank, bareGrid]; ring
  · have := even_mul_add_odd ((bareGrid w).rank ((bareGrid w).m, j)) D.R.t D.R.t_odd
    rw [mul_comm]
    convert this using 2
    simp only [Grid.rank, bareGrid]; ring

theorem rank_path_le (w : Pl D.host.E) {b : Edge} (hb : b ∈ oppositePath (bareGrid w).m) :
    (bareGrid w).rank b.src ≤ bigN D ∧ (bareGrid w).rank b.tgt ≤ bigN D := by
  have hr : D.R.r + 1 = D.R.k + D.R.m := by unfold Ranks.r; have := D.R.two_le_m; omega
  have key : ∀ i j, i ≤ D.R.m → j ≤ D.R.m → (bareGrid w).rank (i, j) ≤ bigN D := fun i j hi hj => by
    simp only [Grid.rank, bareGrid, bigN]
    have h1 := Nat.mul_le_mul_right D.R.t hj
    have h2 := Nat.mul_le_mul_right (sLen D) hi
    nlinarith
  rcases mem_oppositePath.1 hb with ⟨i, hi, rfl⟩ | ⟨j, hj, rfl⟩
  · exact ⟨key _ _ hi.le le_rfl, key _ _ hi le_rfl⟩
  · exact ⟨key _ _ le_rfl hj, key _ _ le_rfl hj.le⟩

theorem path_apow_pow (w : Pl D.host.E) : ∃ n : ℤ, ((oppositePath D.R.m).map fun b =>
    apow (genAt w D.host.AAbar / genAt w D.host.AA)
      (((bareGrid w).rank b.src * (bareGrid w).rank b.tgt : ℕ) / 4)).prod =
      (resCard (Kw w) : ℂ) ^ ((n : ℂ) / 2) ∧
    |n| ≤ (D.R.m : ℤ) ^ 3 * (bigN D : ℤ) ^ 2 *
      (|FractionalIdeal.count D.host.E w D.host.AA| + |FractionalIdeal.count D.host.E w D.host.AAbar|) := by
  set a := FractionalIdeal.count D.host.E w D.host.AA
  set a' := FractionalIdeal.count D.host.E w D.host.AAbar
  set P : Edge → ℕ := fun b => (bareGrid w).rank b.src * (bareGrid w).rank b.tgt
  have hm : (bareGrid w).m = D.R.m := rfl
  have hev : Even ((oppositePath D.R.m).map P).sum := even_sum_of_even P _ fun b hb => even_rank_mul_path w (hm ▸ hb)
  obtain ⟨S, hS⟩ := hev
  have hsum : ((oppositePath D.R.m).map fun b => ((P b : ℕ) : ℂ) / 4).sum = ((((oppositePath D.R.m).map P).sum : ℕ) : ℂ) / 4 := by
    induction (oppositePath D.R.m) with
    | nil => simp
    | cons b l ih => simp only [List.map_cons, List.sum_cons, ih]; push_cast; ring
  refine ⟨(a - a') * S, ?_, ?_⟩
  · rw [prod_apow, hsum, genAt, genAt, div_eq_mul_inv, ← _root_.zpow_sub, apow_zpow, (isUnif_unifAt w).apow_eq, hS]
    congr 1; push_cast; ring
  · have hle : ((oppositePath D.R.m).map P).sum ≤ ((oppositePath D.R.m).map P).length • (bigN D ^ 2) := by
      refine List.sum_le_card_nsmul ((oppositePath D.R.m).map P) _ fun x hx => ?_
      obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hx
      obtain ⟨h1, h2⟩ := rank_path_le w (hm ▸ hb)
      simpa [P, sq] using Nat.mul_le_mul h1 h2
    have hlen : (oppositePath D.R.m).length = 2 * D.R.m := by simp [oppositePath]; ring
    rw [List.length_map, hlen, smul_eq_mul] at hle
    have hS' : (S : ℤ) ≤ D.R.m * bigN D ^ 2 := by
      have : S + S ≤ 2 * D.R.m * bigN D ^ 2 := hS ▸ hle
      have : S ≤ D.R.m * bigN D ^ 2 := by nlinarith
      exact_mod_cast this
    have hm1 : (1 : ℤ) ≤ D.R.m := by have := D.R.two_le_m; omega
    have hN : (0 : ℤ) ≤ bigN D := by positivity
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℤ) ≤ S)]
    have h3 : |a - a'| ≤ |a| + |a'| := abs_sub _ _
    have h4 : (D.R.m : ℤ) * bigN D ^ 2 ≤ D.R.m ^ 3 * bigN D ^ 2 := by
      have : (D.R.m : ℤ) ≤ D.R.m ^ 3 := by nlinarith [mul_le_mul hm1 hm1 zero_le_one (by linarith)]
      exact mul_le_mul_of_nonneg_right this (by positivity)
    calc |a - a'| * (S : ℤ) ≤ (|a| + |a'|) * (D.R.m * bigN D ^ 2) :=
          mul_le_mul h3 hS' (by positivity) (by positivity)
      _ ≤ (|a| + |a'|) * (D.R.m ^ 3 * bigN D ^ 2) := mul_le_mul_of_nonneg_left h4 (by positivity)
      _ = _ := by ring

theorem isLocallyConstant_aaVac (w : Pl D.host.E) : IsLocallyConstant (aaVac w) := by
  classical
  refine (IsLocallyConstant.iff_eventually_eq _).2 fun x => ?_
  set c : Kw w := (((genAt w D.host.AA)⁻¹ : (Kw w)ˣ) : Kw w)
  have h : ∀ᶠ y in nhds x, ∀ b ∈ (oppositePath (bareGrid w).m).toFinset, ∀ i j, c * (y b i j - x b i j) ∈ 𝒪[Kw w] := by
    refine (Filter.eventually_all_finset _).2 fun b _ => Filter.eventually_all.2 fun i =>
      Filter.eventually_all.2 fun j => ?_
    have hc : Continuous fun y : (bareGrid w).Args => c * (y b i j - x b i j) :=
      continuous_const.mul (((continuous_apply b).matrix_elem i j).sub continuous_const)
    exact (Model.isOpen_int.preimage hc).mem_nhds (by simp)
  filter_upwards [h] with y hy
  have key : ∀ b ∈ oppositePath (bareGrid w).m, ∀ i j, (c * y b i j ∈ 𝒪[Kw w] ↔ c * x b i j ∈ 𝒪[Kw w]) :=
    fun b hb i j => by
      have hd := hy b (List.mem_toFinset.2 hb) i j
      have e : c * y b i j = c * x b i j + c * (y b i j - x b i j) := by ring
      rw [e]
      exact ⟨fun h1 => by simpa using sub_mem h1 hd, fun h1 => add_mem h1 hd⟩
  have hs : (y ∈ {z : (bareGrid w).Args | ∀ b ∈ oppositePath (bareGrid w).m, ∀ i j, c * z b i j ∈ 𝒪[Kw w]}) ↔
      (x ∈ {z : (bareGrid w).Args | ∀ b ∈ oppositePath (bareGrid w).m, ∀ i j, c * z b i j ∈ 𝒪[Kw w]}) := by
    exact forall₂_congr fun b hb => forall₂_congr fun i j => key b hb i j
  unfold aaVac
  by_cases hx : x ∈ {z : (bareGrid w).Args | ∀ b ∈ oppositePath (bareGrid w).m, ∀ i j, c * z b i j ∈ 𝒪[Kw w]}
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (hs.2 hx)]; rfl
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (mt hs.1 hx)]

theorem hasCompactSupport_aaVac (w : Pl D.host.E) (ψ : AddChar (Kw w) Circle) (keep : Bool) (g : (bareGrid w).VertexGroup)
    (x : ColArgs (bareGrid w)) (y : RowArgs (bareGrid w)) :
    HasCompactSupport (flatIntegrand one_le_sLen ψ (moved (bareGrid w) keep g (aaVac w)) x y) := by
  classical
  obtain ⟨_, _⟩ := Model.secondCountable_and_t2_local_field (k := Kw w)
  choose a b c h using exists_fill_entry (G := bareGrid w) one_le_sLen x y
  set u : (Kw w)ˣ := (genAt w D.host.AA)⁻¹
  choose K hK hK' using fun j : Fin ((bareGrid w).m - 1) => exists_isCompact_of_mul_mem
    (SplitFlip.diagGL (fun _ => u) * (Assignment.one.read (g (Edge.theta (bareGrid w).m j).tgt))⁻¹)
    (Assignment.one.read (g (Edge.theta (bareGrid w).m j).src))
  refine HasCompactSupport.intro (K := Set.univ.pi fun j => Set.univ.pi fun rs =>
    (fun M => M (a j rs) (b j rs) - c j rs) '' K j) (isCompact_univ_pi fun j => isCompact_univ_pi fun rs =>
      (hK j).image ((continuous_id.matrix_elem _ _).sub continuous_const)) fun v hv => ?_
  have h0 : aaVac w ((bareGrid w).moveArgs .one g (fill one_le_sLen x y v)) = 0 := by
    by_contra hne
    have hmem := Set.mem_of_indicator_ne_zero hne
    refine hv fun j _ rs _ => ⟨_, hK' j _ ?_, (h j rs v).symm⟩
    refine mem_matLat_stdLat.2 fun r s => ?_
    have hb : Edge.theta (bareGrid w).m j ∈ oppositePath (bareGrid w).m := by
      have := j.2; simp [oppositePath]; omega
    have := hmem _ hb r s
    simp only [Grid.moveArgs] at this
    simpa [Units.val_mul, diagGL_val, Matrix.mul_assoc, Matrix.diagonal_mul, u] using this
  simp [flatIntegrand, moved, Grid.pathAct, h0]

theorem flatIntegrable_aaVac (w : Pl D.host.E) {ψ : AddChar (Kw w) Circle} (hψ : Continuous ψ) :
    FlatIntegrable (G := bareGrid w) one_le_sLen ψ (unitVol w) (aaVac w) := by
  classical
  obtain ⟨_, _⟩ := Model.secondCountable_and_t2_local_field (k := Kw w)
  have := (isUnitVol_unitVol w).1
  intro g x y
  unfold varsVol
  have hm : Continuous ((bareGrid w).moveArgs .one g) := continuous_pi fun b =>
    (continuous_const.matrix_mul (continuous_apply b)).matrix_mul continuous_const
  have hc : Continuous (flatIntegrand one_le_sLen ψ (moved (bareGrid w) true g (aaVac w)) x y) :=
    (continuous_const.mul (continuous_const.mul
      ((isLocallyConstant_aaVac w).continuous.comp (hm.comp (continuous_fill one_le_sLen x y))))).mul
      (continuous_subtype_val.comp (hψ.comp (continuous_phase x).neg))
  exact hc.integrable_of_hasCompactSupport (hasCompactSupport_aaVac w ψ true g x y)

variable {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil)

theorem aaScalar_eq_pow (w : Pl D.host.E) (hψ : HasConductor (psiAt W w) (genAt w D.host.AA * genAt w D.host.AAbar)) :
    ∃ n : ℤ, aaScalar W w = (resCard (Kw w) : ℂ) ^ ((n : ℂ) / 2) ∧
    |n| ≤ 16 * ((D.R.m : ℤ) ^ 3 * (bigN D : ℤ) ^ 2 *
      (|FractionalIdeal.count D.host.E w D.host.AA| + |FractionalIdeal.count D.host.E w D.host.AAbar|)) := by
  obtain ⟨n1, h1, b1⟩ := GlobalTheory.T.unfoldingTerm_coef_eq_residueCard_zpow W w
  obtain ⟨n2, h2, b2⟩ := GlobalTheory.T.originDatum_value_halfIntegerPow_placeAA W w fun a ha => hψ.eq_one ha
  obtain ⟨n3, h3, b3⟩ := path_apow_pow w
  have hq : (resCard (Kw w) : ℂ) ≠ 0 := by
    have : 1 < resCard (Kw w) := Finite.one_lt_card; exact_mod_cast (show resCard (Kw w) ≠ 0 by omega)
  refine ⟨2 * n1 + n2 + n3, ?_, ?_⟩
  · have e1 : (((resCard (Kw w) : ℚ) ^ n1 : ℚ) : ℂ) = (resCard (Kw w) : ℂ) ^ (((2 * n1 : ℤ) : ℂ) / 2) := by
      rw [Rat.cast_zpow, Rat.cast_natCast, ← Complex.cpow_intCast]; congr 1; push_cast; ring
    rw [aaScalar, h1, h2, h3, e1, ← Complex.cpow_add _ _ hq, ← Complex.cpow_add _ _ hq]
    congr 1; push_cast; ring
  · have hB : 0 ≤ (D.R.m : ℤ) ^ 3 * (bigN D : ℤ) ^ 2 *
        (|FractionalIdeal.count D.host.E w D.host.AA| + |FractionalIdeal.count D.host.E w D.host.AAbar|) := by positivity
    calc |2 * n1 + n2 + n3| ≤ 2 * |n1| + |n2| + |n3| := by
          have := abs_add_le (2 * n1 + n2) n3; have := abs_add_le (2 * n1) n2
          rw [abs_mul, abs_two] at *; linarith
      _ ≤ _ := by linarith

theorem sAA_facts {U : Set T} (S : GridChoice W U)
    (hψ : ∀ w ∈ S.PA, HasConductor (psiAt W w) (genAt w D.host.AA * genAt w D.host.AAbar)) :
    S.sAA ≠ 0 ∧ (∃ r : ℝ, 0 < r ∧ S.sAA = r) ∧ ∃ Q : ℚ, S.sAA ^ 2 = Q := by
  classical
  have hw : ∀ w ∈ S.PA, ∃ n : ℤ, aaScalar W w = (resCard (Kw w) : ℂ) ^ ((n : ℂ) / 2) :=
    fun w hw => (aaScalar_eq_pow W w (hψ w hw)).imp fun _ h => h.1
  choose! n hn using hw
  have e : ∀ w ∈ S.PA, aaScalar W w = (((resCard (Kw w) : ℝ) ^ ((n w : ℝ) / 2) : ℝ) : ℂ) := fun w hw => by
    rw [hn w hw, Complex.ofReal_cpow (Nat.cast_nonneg _)]; push_cast; rfl
  have hr : S.sAA = ((∏ w ∈ S.PA, (resCard (Kw w) : ℝ) ^ ((n w : ℝ) / 2) : ℝ) : ℂ) := by
    rw [GridChoice.sAA, Complex.ofReal_prod]; exact Finset.prod_congr rfl e
  have hpos : 0 < ∏ w ∈ S.PA, (resCard (Kw w) : ℝ) ^ ((n w : ℝ) / 2) :=
    Finset.prod_pos fun w _ => Real.rpow_pos_of_pos (by have : 1 < resCard (Kw w) := Finite.one_lt_card; positivity) _
  have hsq : (∏ w ∈ S.PA, (resCard (Kw w) : ℝ) ^ ((n w : ℝ) / 2)) ^ 2 =
      ((∏ w ∈ S.PA, (resCard (Kw w) : ℚ) ^ n w : ℚ) : ℝ) := by
    rw [← Finset.prod_pow, Rat.cast_prod]
    refine Finset.prod_congr rfl fun w _ => ?_
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _), Rat.cast_zpow, Rat.cast_natCast, ← Real.rpow_intCast]
    congr 1; push_cast; ring
  refine ⟨by rw [hr]; exact_mod_cast hpos.ne', ⟨_, hpos, hr⟩, ∏ w ∈ S.PA, (resCard (Kw w) : ℚ) ^ n w, ?_⟩
  rw [hr, ← Complex.ofReal_pow, hsq, Complex.ofReal_ratCast]

theorem flatIntegrable_aaVac_of_conductor (w : Pl D.host.E)
    (hψ : HasConductor (psiAt W w) (genAt w D.host.AA * genAt w D.host.AAbar)) :
    FlatIntegrable (G := bareGrid w) one_le_sLen (psiAt W w) (unitVol w) (aaVac w) :=
  flatIntegrable_aaVac w hψ.continuous

end GlobalTheory.FunObj
