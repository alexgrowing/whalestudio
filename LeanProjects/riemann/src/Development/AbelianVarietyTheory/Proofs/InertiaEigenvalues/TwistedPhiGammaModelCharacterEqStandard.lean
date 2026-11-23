import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistedModelAdmissibleCocycles
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.OnePlusPowerAssembly
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EquivariantOfLinear
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsJordanHolderThroughLineStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SenWeightSubquotientModelMemResiduesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HomToCharacterLineEqZeroStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharacterModelExponentsSignsSenWeightStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleLetterDataWindowArithmetic

open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models
open scoped LaurentSeries PowerSeries
namespace GlobalTheory.Models.CharModel

theorem eq_chr_of_bijective {k G : Type} [Field k] [Group G] (A : Ob k G) (χ : G →* kˣ)
    (f : (Fin A.m → k) →ₗ[k] (Fin 1 → k)) (hf : IsHom A (chr χ) f) (hb : Function.Bijective f) : A = chr χ := by
  obtain ⟨m, ρ⟩ := A
  have hm : m = 1 := by
    have := (LinearEquiv.ofBijective f hb).finrank_eq
    simpa using this
  subst hm
  have : ρ = (chr χ).ρ := by
    ext1 g
    refine LinearMap.ext fun x => hb.1 ?_
    rw [hf g x]
    change (χ g : k) • f x = f ((χ g : k) • x)
    rw [map_smul]
  subst this
  rfl

theorem chr_inj {k G : Type} [Field k] [Group G] {χ χ' : G →* kˣ} (h : chr χ = chr χ') : χ = χ' := by
  have h1 : (chr χ).ρ = (chr χ').ρ := eq_of_heq (Ob.mk.inj h).2
  ext g
  have := congrArg (fun ρ : Representation k G (Fin 1 → k) => ρ g (fun _ => 1) 0) h1
  simpa using this

theorem eq_of_cast_eq {k : Type} [Field k] {l : ℕ} [CharP k l] {a b : ℤ} (h : (a : k) = b) (hab : |a - b| < l) :
    a = b := by
  have h1 : ((a - b : ℤ) : k) = 0 := by push_cast; rw [h, sub_self]
  rw [CharP.intCast_eq_zero_iff k l] at h1
  have := Int.eq_zero_of_abs_lt_dvd h1 hab
  omega

theorem resCount_single {k : Type} [Field k] [DecidableEq k] (u : ℤ) (x : k) :
    resCount {u} 0 x = if (u : k) = x then 1 else 0 := by
  unfold resCount
  rw [Multiset.filter_singleton]
  simp only [sub_zero]
  split_ifs <;> simp

theorem resCount_block {k : Type} [Field k] [DecidableEq k] (w : ℤ) (t : ℕ) (x : k) :
    resCount (block w t) w x = ∑ e : Fin t, if ((e.val : ℤ) : k) = x then 1 else 0 := by
  unfold resCount
  rw [Fin.sum_univ_eq_sum_range (fun e => if ((e : ℤ) : k) = x then 1 else 0) t, Finset.sum_boole, block,
    ← Finset.filter_val, Finset.card_val, Nat.cast_id]
  symm
  refine Finset.card_bij (fun e _ => w + e) ?_ ?_ ?_
  · intro e he
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico] at he ⊢
    refine ⟨⟨by omega, by omega⟩, ?_⟩
    rw [add_sub_cancel_left]; exact he.2
  · intro a _ b _ h
    omega
  · intro u hu
    simp only [Finset.mem_filter, Finset.mem_Ico] at hu
    have h : (((u - w).toNat : ℕ) : ℤ) = u - w := by omega
    refine ⟨(u - w).toNat, ?_, by omega⟩
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, by rw [h]; exact hu.2⟩

theorem sum_eq_of_counts {k ι : Type} [Field k] [DecidableEq k] {l : ℕ} [CharP k l] (S : Finset ι) (a b : ι → ℤ)
    (lo hi : ℤ) (hl : hi - lo < l) (ha : ∀ i ∈ S, lo ≤ a i ∧ a i ≤ hi) (hb : ∀ i ∈ S, lo ≤ b i ∧ b i ≤ hi)
    (h : ∀ y : ℤ, lo ≤ y → y ≤ hi →
      (∑ i ∈ S, if (a i : k) = y then 1 else 0 : ℕ) = ∑ i ∈ S, if (b i : k) = y then 1 else 0) :
    ∑ i ∈ S, a i = ∑ i ∈ S, b i := by
  have key : ∀ c : ι → ℤ, (∀ i ∈ S, lo ≤ c i ∧ c i ≤ hi) → ∑ i ∈ S, c i =
      ∑ y ∈ Finset.Icc lo hi, y * ((∑ i ∈ S, if (c i : k) = y then 1 else 0 : ℕ) : ℤ) := by
    intro c hc
    push_cast
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i hi' => ?_
    rw [Finset.sum_eq_single (c i)]
    · simp
    · intro y hy hne
      rw [Finset.mem_Icc] at hy
      have := hc i hi'
      rw [if_neg, mul_zero]
      intro h'
      exact hne (eq_of_cast_eq (l := l) h' (by rw [abs_lt]; omega)).symm
    · intro h'
      exact absurd (Finset.mem_Icc.2 (hc i hi')) h'
  rw [key a ha, key b hb]
  refine Finset.sum_congr rfl fun y hy => ?_
  rw [Finset.mem_Icc] at hy
  rw [h y hy.1 hy.2]

theorem model_of_base {k G : Type} [Field k] [Group G] {l n : ℕ} {R : RingPG k l} {F : DFun R n G} {r : ℕ}
    {Dt : TopData n r} (M : ModTh F Dt) (B : Ob k G) (N : Lats k n B.m) (h : M.Base B N) : M.Model B N := by
  refine ⟨B, N, B, LinearMap.id, LinearMap.id, h, fun _ _ => rfl, Function.injective_id, fun _ _ => rfl,
    Function.surjective_id, ?_⟩
  funext i
  simp only [DFun.push, DFun.pre, F.map_id B (M.base_obj B N h)]
  ext x
  simp

theorem model_chr_eq : ∀ {k G : Type} [Field k] [Group G] {l n : ℕ} [Fact l.Prime] [CharP k l] [NeZero n] {R : RingPG k l} (F : DFun R n G) {r : ℕ} {Dt : TopData n r} (M : ModTh F Dt), Dt.T1 l → Dt.T2 l → Dt.T3 l → ∀ (e : ℤ), 0 ≤ e → e < Dt.t → ∀ N : Lats k n 1, M.Model (chr (M.ω ^ (-e))) N → N = M.Nχ e := by
  intro k G _ _ l n _ _ _ R F r Dt M h1 h2 h3 e he0 het N hN
  classical
  obtain ⟨κ₀, hκ₀⟩ := GlobalTheory.T.character_model_exponents_signs_senWeight F M h1 h2 h3 e he0 het N hN
  obtain ⟨B, Nb, A₁, j, p, hB, hj, hji, hp, hps, hNe⟩ := hN
  obtain ⟨μ, hss, hsen⟩ := M.base_sen B Nb hB
  obtain ⟨s, C, L, a₀, hmod, hsimple, hss', hsum, ha₀⟩ :=
    GlobalTheory.T.exists_jordanHolder_through_line_alt F M B A₁ (M.ω ^ (-e)) j p Nb (model_of_base M B Nb hB) hj hji hp hps
  rw [← hNe] at ha₀
  obtain ⟨c, hsome, hnone, hcard⟩ := GlobalTheory.JHMatch.jh_match M.T M.ω Dt.t μ s C hsimple
    (SameFactors.trans (SameFactors.symm hss') hss)
  have hW := GlobalTheory.WindowArith.windows (k := k) Dt h1 h2 h3
  have htη : ∀ i, (Dt.t : ℤ) ≤ Dt.η i := by
    intro i
    obtain ⟨-, -, hG, hBd⟩ := hW i
    cases hty : Dt.ty i
    · have := hG hty; omega
    · have := hBd hty; omega
  have hC : ∀ a e', c a = some e' → C a = chr (M.ω ^ (-(e'.val : ℤ))) := fun a e' h => by
    obtain ⟨f, hf, hb⟩ := hsome a e' h
    exact eq_chr_of_bijective _ _ f hf hb
  have hch : ∀ (A : Ob k G) (Λ : Lats k n A.m) (e' : Fin Dt.t), M.Model A Λ →
      A = chr (M.ω ^ (-(e'.val : ℤ))) → ∃ κ : ZMod n → ℤ, ∀ i, |κ i| ≤ Dt.sg l i ∧
        (Dt.ty i = LType.G → 0 ≤ κ (i - 1)) ∧ (Dt.ty i = LType.Bd → κ (i - 1) ≤ 0) ∧
        ∀ x, sen ((F.D A).γ i) (Λ i) x = resCount {(e'.val : ℤ) - κ i} 0 x := by
    rintro A Λ e' hm rfl
    obtain ⟨κ, hκ⟩ := GlobalTheory.T.character_model_exponents_signs_senWeight F M h1 h2 h3 e' (by omega) (by omega) Λ hm
    exact ⟨κ, fun i => (hκ i).2⟩
  have hex : ∀ a, ∃ κ : ZMod n → ℤ, ∀ e', c a = some e' → ∀ i, |κ i| ≤ Dt.sg l i ∧
        (Dt.ty i = LType.G → 0 ≤ κ (i - 1)) ∧ (Dt.ty i = LType.Bd → κ (i - 1) ≤ 0) ∧
        ∀ x, sen ((F.D (C a)).γ i) (L a i) x = resCount {(e'.val : ℤ) - κ i} 0 x := by
    intro a
    cases hc : c a with
    | none => exact ⟨0, fun _ h => by cases h⟩
    | some e' =>
      obtain ⟨κ, hκ⟩ := hch (C a) (L a) e' (hmod a) (hC a e' hc)
      exact ⟨κ, fun e'' h => by cases h; exact hκ⟩
  choose κ hκ using hex
  let cc : Fin s → ℤ := fun a => (c a).elim 0 fun e' => (e'.val : ℤ)
  let S : Finset (Fin s) := Finset.univ.filter fun a => c a ≠ none
  have hS : ∀ a ∈ S, ∃ e', c a = some e' ∧ cc a = e'.val := by
    intro a ha
    obtain ⟨e', he'⟩ := Option.ne_none_iff_exists'.1 (Finset.mem_filter.1 ha).2
    exact ⟨e', he', by simp [cc, he']⟩
  have hzero : ∀ i, ∀ a ∈ S, κ a i = 0 := by
    intro i
    have hT := h1 i
    have hη := htη i
    have hsumeq : ∑ a ∈ S, (cc a - κ a i) = ∑ a ∈ S, cc a := by
      refine sum_eq_of_counts (k := k) (l := l) S _ _ (-(Dt.sg l i : ℤ)) (Dt.t + Dt.sg l i) (by omega) ?_ ?_ ?_
      · intro a ha
        obtain ⟨e', he', hcc⟩ := hS a ha
        have := abs_le.1 (hκ a e' he' i).1
        have := e'.2
        omega
      · intro a ha
        obtain ⟨e', he', hcc⟩ := hS a ha
        have := e'.2
        omega
      · intro y hy1 hy2
        have hU : ∀ u ∈ Dt.U i, ((u - Dt.w i : ℤ) : k) ≠ (y : k) := by
          intro u hu h
          refine (hW i).2.1 u hu (Dt.w i + y) (by omega) (by omega) ?_
          push_cast at h ⊢
          linear_combination h
        have e1 : (∑ a ∈ S, if ((cc a - κ a i : ℤ) : k) = y then 1 else 0 : ℕ) =
            ∑ a, sen ((F.D (C a)).γ i) (L a i) (y : k) := by
          rw [Finset.sum_filter]
          refine Finset.sum_congr rfl fun a _ => ?_
          cases hc : c a with
          | none =>
            simp only [ne_eq, not_true_eq_false, if_false]
            by_contra hne
            obtain ⟨A', j', p', q1, q2, q3, q4⟩ := hnone a hc
            obtain ⟨u, hu, hux⟩ := GlobalTheory.T.senWeight_subquotient_model_mem_residues F M h1 h2 h3 A' (C a) j' p' (L a) q1 q2 q3 q4 (hmod a) i y
              (Ne.symm hne)
            exact hU u hu hux
          | some e' =>
            rw [(hκ a e' hc i).2.2.2, resCount_single, if_pos (by simp)]
            simp [cc, hc]
        have e2 : resCount (Dt.Ut i) (Dt.w i) (y : k) = resCount (block (Dt.w i) Dt.t) (Dt.w i) (y : k) := by
          unfold resCount
          rw [TopData.Ut, Multiset.filter_add, Multiset.filter_eq_nil.2 hU, zero_add]
          rfl
        rw [e1, ← hsum, hsen, e2, resCount_block, Finset.sum_filter,
          ← Finset.sum_fiberwise_of_maps_to (g := c) (t := Finset.univ) (fun _ _ => Finset.mem_univ _),
          Fintype.sum_option, Finset.mul_sum,
          Finset.sum_eq_zero (s := Finset.univ.filter fun a => c a = none), zero_add]
        · refine Finset.sum_congr rfl fun e' _ => ?_
          rw [← hcard e', ← smul_eq_mul, ← Finset.sum_const]
          refine Finset.sum_congr rfl fun a ha => ?_
          have hc := (Finset.mem_filter.1 ha).2
          simp [cc, hc]
        · intro a ha
          have hc := (Finset.mem_filter.1 ha).2
          simp [hc]
    have hs0 : ∑ a ∈ S, κ a i = 0 := by
      rw [Finset.sum_sub_distrib] at hsumeq
      linarith
    cases hty : Dt.ty (i + 1)
    · refine (Finset.sum_eq_zero_iff_of_nonneg fun a ha => ?_).1 hs0
      obtain ⟨e', he', -⟩ := hS a ha
      simpa using (hκ a e' he' (i + 1)).2.1 hty
    · refine (Finset.sum_eq_zero_iff_of_nonpos fun a ha => ?_).1 hs0
      obtain ⟨e', he', -⟩ := hS a ha
      simpa using (hκ a e' he' (i + 1)).2.2.1 hty
  have hCa : C a₀ = chr (M.ω ^ (-e)) := congrArg Sigma.fst ha₀
  have haS : a₀ ∈ S := by
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, fun hc => ?_⟩
    have := hnone a₀ hc
    rw [hCa] at this
    obtain ⟨A', j', p', q1, q2, q3, q4⟩ := this
    have hp0 := GlobalTheory.T.hom_to_characterLine_eq_zero F M h1 h2 h3 e (by omega) het A' j' p' q1 q2 q3
    obtain ⟨x, hx⟩ := q4 (fun _ => 1)
    rw [hp0] at hx
    simpa using congrFun hx 0
  obtain ⟨e', he', -⟩ := hS a₀ haS
  have hee : e = e'.val := by
    have hω := chr_inj (hCa.symm.trans (hC a₀ e' he'))
    have hT := h1 0
    have hη := htη 0
    have := e'.2
    by_contra hne
    refine M.ω_ne (e - e'.val).natAbs (by omega) (by omega) ?_
    have h : M.ω ^ (e - (e'.val : ℤ)) = 1 := by
      rw [sub_eq_add_neg, zpow_add, ← hω, ← zpow_add, add_neg_cancel, zpow_zero]
    exact pow_natAbs_eq_one.2 h
  funext i
  have hsen0 := congrArg (fun P : Σ A : Ob k G, Lats k n A.m =>
    sen ((F.D P.1).γ i) (P.2 i) ((e : ℤ) : k)) ha₀
  simp only at hsen0
  rw [(hκ a₀ e' he' i).2.2.2, (hκ₀ i).2.2.2.2, hzero i a₀ haS, resCount_single, resCount_single, ← hee,
    if_pos (by simp)] at hsen0
  have h0 : κ₀ i = 0 := by
    split_ifs at hsen0 with h
    have hT := h1 i
    have hb := abs_le.1 (hκ₀ i).2.1
    have := eq_of_cast_eq (l := l) h (by rw [abs_lt]; omega)
    omega
  rw [(hκ₀ i).1, h0, sh_zero_eq]

end GlobalTheory.Models.CharModel
