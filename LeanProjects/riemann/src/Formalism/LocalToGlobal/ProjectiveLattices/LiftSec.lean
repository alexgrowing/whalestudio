import Formalism.LocalToGlobal.ProjectiveLattices.LiftCurveSt

noncomputable section

namespace Formalism.L2.Pj

open Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Gaps.EtaleWeightGaps NumberField IsDedekindDomain Finset

section HasseH

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (X : PJ D B P j) (la : HeightOneSpectrum (𝓞 B.KO))
  {N : ℕ} {wL : WeightFamilies.Wt D j} (w : Fin N → B.Cusp j wL)

def hasseW (β : Idx D j N →₀ ℕ) (x : Lw X la w) : Lw X la w := hasse X la w β x

theorem hasseW_apply (β : Idx D j N →₀ ℕ) (x : Lw X la w) : hasseW X la w β x = hasse X la w β x := rfl

theorem hasseW_of_mul_eq (β : Idx D j N →₀ ℕ) {s x : Rp X la N} {y : Lw X la w}
    (h : algebraMap (Rp X la N) (Lw X la w) s * y = algebraMap (Rp X la N) (Lw X la w) x) :
    ∑ q ∈ antidiagonal β, algebraMap (Rp X la N) (Lw X la w) (hasseRp X la N q.1 s) * hasseW X la w q.2 y =
      algebraMap (Rp X la N) (Lw X la w) (hasseRp X la N β x) := hasse_of_mul_eq X la w β h

theorem hasseW_zero (x : Lw X la w) : hasseW X la w 0 x = x := hasse_zero X la w x

theorem hasse_frac_succ_mem {u : WeightFamilies.Wt D j} {m : ℕ} {g : Rp X la N} (hg : g ∈ Vw X la N (addL u wL (m + 1)))
    (β : Idx D j N →₀ ℕ) : hasseW X la w β (frac X la w (m + 1) g) ∈ Hfr X la w u := by
  induction hn : Finsupp.degree β using Nat.strong_induction_on generalizing β with
  | _ n ih =>
  have hs0 : sec X la w 0 ^ (m + 1) ∈ Vw X la N (addL (wt0 D j) wL (m + 1)) := by
    have h1 : sec X la w 0 ∈ Vw X la N (addL (wt0 D j) wL 1) := by
      rw [add_zero_weight_one_eq]; exact sec_mem_Vw X la w 0
    have := sec_pow_mul_mem X la w 0 (wt0 D j) 1 m h1
    rwa [← pow_succ, add_comm 1 m] at this
  have hs : algebraMap (Rp X la N) (Lw X la w) (sec X la w 0 ^ (m + 1)) * frac X la w (m + 1) g =
      algebraMap (Rp X la N) (Lw X la w) g := by
    rw [frac_apply, mul_comm (algebraMap _ _ g), ← mul_assoc, map_pow, ← mul_pow, section_mul_inverse_eq_one, one_pow, one_mul]
  have hq := hasseW_of_mul_eq X la w β hs
  have hmem : ((0 : Idx D j N →₀ ℕ), β) ∈ antidiagonal β := mem_antidiagonal.2 (zero_add β)
  rw [← add_sum_erase _ _ hmem, hasseRp_zero] at hq
  have hinv : w0inv X la w ^ (m + 1) * algebraMap (Rp X la N) (Lw X la w) (sec X la w 0 ^ (m + 1)) = 1 := by
    rw [map_pow, ← mul_pow, mul_comm, section_mul_inverse_eq_one, one_pow]
  have key : hasseW X la w β (frac X la w (m + 1) g) = w0inv X la w ^ (m + 1) *
      (algebraMap (Rp X la N) (Lw X la w) (hasseRp X la N β g) -
        ∑ q ∈ (antidiagonal β).erase (0, β), algebraMap (Rp X la N) (Lw X la w) (hasseRp X la N q.1 (sec X la w 0 ^ (m + 1))) *
          hasseW X la w q.2 (frac X la w (m + 1) g)) := by
    rw [← hq, add_sub_cancel_right, ← mul_assoc, hinv, one_mul]
  rw [key, mul_sub, mul_sum]
  refine Submodule.sub_mem _ ?_ (Submodule.sum_mem _ fun q hq' => ?_)
  · rw [mul_comm, ← frac_apply]
    exact frac_mem_Hfr X la w (hasseRp_mem_Vw X la hg β)
  · have h12 : q.1 + q.2 = β := mem_antidiagonal.1 (mem_of_mem_erase hq')
    have hne : q.1 ≠ 0 := by
      intro h
      apply ne_of_mem_erase hq'
      exact Prod.ext h (by rw [← h12, h, zero_add])
    have hlt : Finsupp.degree q.2 < n := by
      rw [← hn, ← h12, map_add]
      have : Finsupp.degree q.1 ≠ 0 := fun h => hne ((Finsupp.degree_eq_zero_iff _).1 h)
      omega
    have h2 := ih _ hlt q.2 rfl
    rw [← mul_assoc, mul_comm (w0inv X la w ^ (m + 1)), ← frac_apply]
    have hf := frac_mem_Hfr X la w (hasseRp_mem_Vw X la hs0 q.1)
    have := mul_mem_Hfr X la w hf h2
    rwa [zero_weight_add] at this

theorem hasse_mem_Hfr {u : WeightFamilies.Wt D j} {x : Lw X la w} (hx : x ∈ Hfr X la w u) (β : Idx D j N →₀ ℕ) :
    hasseW X la w β x ∈ Hfr X la w u := by
  obtain ⟨k, g, hg, rfl⟩ := (mem_Hfr X la w).1 hx
  have hg' := sec_pow_mul_mem X la w 0 u k 1 hg
  rw [← frac_pow_mul X la w k 1 g, pow_one] at *
  exact hasse_frac_succ_mem X la w (by simpa using hg') β

end HasseH

section Model

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} {E : PtExt X} {hM : IntAtExt X E}
  {ka wL wF : WeightFamilies.Wt D j} {G : GlobalFamilyData (xplus X E hM) ka wL wF} {la : HeightOneSpectrum (𝓞 B.KO)}
  {y : PtsG G la → E.Pt' la} {hs : ∀ ζ, SecPt ζ (y ζ)} {g0 : B.Cusp j wF} {T : ℕ}

namespace LiftModel

variable (M : LiftModel G la y hs g0 T)

def I : Ideal M.Λ :=
  Ideal.span (Set.range fun i : Fin (WeightFamilies.dimY D j) => M.ι (sfr (xplus X E hM) la G.w i.succ : Lw (xplus X E hM) la G.w))

def Low (n : ℕ) (z : M.Λ) : Prop := ∀ β : Idx D j G.N →₀ ℕ, M.hd β z ∈ M.I ^ (n - Finsupp.degree β)

theorem low_zero_left (z : M.Λ) : M.Low 0 z := fun β => by simp

theorem low_add {n : ℕ} {z z' : M.Λ} (hz : M.Low n z) (hz' : M.Low n z') : M.Low n (z + z') := fun β => by
  rw [map_add]; exact Ideal.add_mem _ (hz β) (hz' β)

theorem low_mul {n m : ℕ} {z z' : M.Λ} (hz : M.Low n z) (hz' : M.Low m z') : M.Low (n + m) (z * z') := fun β => by
  rw [M.hd_mul]
  refine Ideal.sum_mem _ fun q hq => ?_
  have h12 := mem_antidiagonal.1 hq
  have h := Ideal.mul_mem_mul (hz q.1) (hz' q.2)
  rw [← pow_add] at h
  refine Ideal.pow_le_pow_right ?_ h
  rw [← h12, map_add]
  omega

theorem low_gen (i : Fin (WeightFamilies.dimY D j)) :
    M.Low 1 (M.ι (sfr (xplus X E hM) la G.w i.succ : Lw (xplus X E hM) la G.w)) := fun β => by
  by_cases hβ : β = 0
  · subst hβ
    rw [M.hd_zero, map_zero, Nat.sub_zero, pow_one]
    exact Ideal.subset_span ⟨i, rfl⟩
  · have : Finsupp.degree β ≠ 0 := fun h => hβ ((Finsupp.degree_eq_zero_iff _).1 h)
    rw [show 1 - Finsupp.degree β = 0 by omega, pow_zero, Ideal.one_eq_top]
    exact Submodule.mem_top

theorem low_one {z : M.Λ} (hz : z ∈ M.I) : M.Low 1 z := by
  unfold LiftModel.I at hz
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    exact M.low_gen i
  | zero => exact fun β => by rw [map_zero]; exact Ideal.zero_mem _
  | add x y _ _ hx hy => exact M.low_add hx hy
  | smul a x _ hx =>
    have := M.low_mul (M.low_zero_left a) hx
    rwa [zero_add] at this

theorem hd_pow_mem (n : ℕ) {z : M.Λ} (hz : z ∈ M.I ^ n) : M.Low n z := by
  induction n generalizing z with
  | zero => exact M.low_zero_left z
  | succ n ih =>
    rw [pow_succ] at hz
    exact Submodule.mul_induction_on hz (fun a ha b hb => M.low_mul (ih ha) (M.low_one hb))
      (fun x y hx hy => M.low_add hx hy)

theorem ev_I (ζ : PtsG G la) {z : M.Λ} (hz : z ∈ M.I) : M.ev ζ z = 0 := by
  unfold LiftModel.I at hz
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    rw [M.ev_ι]
    exact (hs ζ).lift_Jid (sfr_succ_mem_Jid (xplus X E hM) la G.w i)
  | zero => exact map_zero _
  | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
  | smul a x _ hx => rw [smul_eq_mul, map_mul, hx, mul_zero]

theorem hd_mul_e' (β : Idx D j G.N →₀ ℕ) (r : M.Λ) : M.hd β (r * M.e') = M.hd β r * M.e' := by
  rw [M.hd_mul, sum_eq_single (β, 0)]
  · rw [M.hd_zero]
  · intro q hq hne
    have h12 := mem_antidiagonal.1 hq
    have h2 : q.2 ≠ 0 := by
      intro h
      apply hne
      exact Prod.ext (by rw [← h12, h, add_zero]) h
    rw [M.e'_hd _ h2, mul_zero]
  · intro h
    exact absurd (mem_antidiagonal.2 (add_zero β)) h

theorem step5 {r : M.Λ} (hr : r ∈ M.RG) (x : Lw (xplus X E hM) la G.w) {n : ℕ} (hx : M.ι x - r * M.e' ∈ M.I ^ n)
    (β : Idx D j G.N →₀ ℕ) (hβ : Finsupp.degree β < n) (ζ : PtsG G la) :
    0 ≤ nval (hs ζ).T.V 1 ((hs ζ).lift (hasse (xplus X E hM) la G.w β x)) := by
  have h1 := M.hd_pow_mem n hx β
  have h2 : M.hd β (M.ι x - r * M.e') ∈ M.I := Ideal.pow_le_self (by omega) h1
  have h3 := M.ev_I ζ h2
  rw [map_sub, M.hd_ι, M.hd_mul_e', map_sub, sub_eq_zero, map_mul] at h3
  have h4 := M.ev_ι ζ (hasse (xplus X E hM) la G.w β x)
  rw [h4] at h3
  rw [h3, nval_mul]
  exact add_nonneg (M.RG_int ζ _ (M.RG_hd β r hr)) (M.e'_int ζ)

end LiftModel

end Model

section Top

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} {E : PtExt X} {hM : IntAtExt X E}
  {ka wL wF : WeightFamilies.Wt D j} {G : GlobalFamilyData (xplus X E hM) ka wL wF} {la : HeightOneSpectrum (𝓞 B.KO)}
  {y : PtsG G la → E.Pt' la} {hs : ∀ ζ, SecPt ζ (y ζ)} {g0 : B.Cusp j wF}

theorem ordA_nonneg {S : Scal B} (hCurve : (secQ y hs g0).InCurve) (hTie : (secQ y hs g0).InTie S)
    (z : ↥(HK (xplus X E hM) la G.w wF)) (ζ : PtsG G la)
    (h : 0 ≤ nval (hs ζ).T.V 1 ((hs ζ).lift (z : Lw (xplus X E hM) la G.w))) :
    0 ≤ (secQ y hs g0).ordA ζ (toA0K (xplus X E hM) la G.w wF z) := by
  have hgen : IsGen (OsK (xplus X E hM) la G.w) (secQ y hs g0).e := hCurve.2.2
  have hg0 : (hs ζ).ev (emb (xplus X E hM) la G.N (X.inc wF g0)) ≠ 0 := by
    intro h0
    have h5 := (hTie ζ).2.2.2.2.1
    have hv : (xplus X E hM).vAt la ((secQ y hs g0).y ζ) ((xplus X E hM).inc wF (secQ y hs g0).g0) =
        nval (hs ζ).T.V (ep (unifO (xplus X E hM) la G.N) ζ) ((hs ζ).ev (emb (xplus X E hM) la G.N (X.inc wF g0))) :=
      (hs ζ).hv wF g0
    rw [hv, h0, nval_zero, EReal.mul_top_of_pos (by exact_mod_cast (hs ζ).ep_pos)] at h5
    exact EReal.coe_ne_top _ h5
  set a := toA0K (xplus X E hM) la G.w wF z with ha
  obtain ⟨f, hf⟩ := toOsK_surjective (xplus X E hM) la G.w (coord (secQ y hs g0).e a)
  have hca : coord (secQ y hs g0).e a • (secQ y hs g0).e = a := coord_smul_self hgen a
  have h1 : toA0K (xplus X E hM) la G.w wF (f • toHK0 (xplus X E hM) la G.w wF
      ⟨emb (xplus X E hM) la G.N (X.inc wF g0), emb_mem_Vw (xplus X E hM) la G.N wF g0⟩) = a := by
    rw [map_smul, ← restriction_apply_eq_reduction, ← hca, ← hf]
    exact (algebraMap_smul (OsK (xplus X E hM) la G.w) f _).symm
  have h2 := (Submodule.Quotient.eq _).1 h1
  have h3 := (hs ζ).lift_JHK h2
  rw [Submodule.coe_sub, map_sub, sub_eq_zero, Submodule.coe_smul, Algebra.smul_def, map_mul, coe_toHK0,
    (hs ζ).lift_alg] at h3
  have hord := (hs ζ).ord f
  rw [hf] at hord
  have key : toE ((secQ y hs g0).ordA ζ a) = nval (hs ζ).T.V 1 ((hs ζ).lift (z : Lw (xplus X E hM) la G.w)) := by
    simp only [LocalPointData.ordA, ordV]
    rw [toE_add_coe, hord, ← h3, nval_mul, nval_of_ne hg0]
    simp only [Nat.cast_one, div_one]
    rfl
  rw [← key] at h
  generalize (secQ y hs g0).ordA ζ a = o at h ⊢
  cases o with
  | top => exact le_top
  | coe n =>
    have h' : (0 : ℝ) ≤ (n : ℝ) := EReal.coe_nonneg.1 h
    have hn : (0 : ℤ) ≤ n := by exact_mod_cast h'
    exact_mod_cast hn

theorem inLiftSec (G : GlobalFamilyData (xplus X E hM) ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) (S : Scal B) (Gc Prw : ℝ) :
    InLiftSecSt G la S Gc Prw := by
  intro y hs g0 T hMod _ hCurve hTie a ha
  obtain ⟨M⟩ := hMod
  obtain ⟨r, hr, x1, hx1a, hx1I⟩ := M.ball a ha
  obtain ⟨x2, hx2⟩ := M.approx r hr
  have hex : ∃ x : ↥(HK (xplus X E hM) la G.w wF), toA0K (xplus X E hM) la G.w wF x = a ∧ ∃ n : ℕ,
      (∀ β : Idx D j G.N →₀ ℕ, β.sum (fun _ n => n) ≤ a0 D j T - 1 → Finsupp.degree β < n) ∧
      M.ι (x : Lw (xplus X E hM) la G.w) - r * M.e' ∈ M.I ^ n := by
    by_cases h0 : a0 D j T = 0
    · refine ⟨x1, hx1a, 1, fun β hβ => ?_, by rw [pow_one]; exact hx1I⟩
      have : Finsupp.degree β = β.sum (fun _ n => n) := rfl
      omega
    · refine ⟨x2, ?_, a0 D j T, fun β hβ => ?_, hx2⟩
      · rw [← hx1a, ← sub_eq_zero, ← map_sub]
        apply M.res_ker
        have e : M.ι ((x2 - x1 : ↥(HK (xplus X E hM) la G.w wF)) : Lw (xplus X E hM) la G.w) =
            (M.ι (x2 : Lw (xplus X E hM) la G.w) - r * M.e') - (M.ι (x1 : Lw (xplus X E hM) la G.w) - r * M.e') := by
          rw [Submodule.coe_sub, map_sub]; ring
        rw [e]
        exact Ideal.sub_mem _ (Ideal.pow_le_self h0 hx2) hx1I
      · have : Finsupp.degree β = β.sum (fun _ n => n) := rfl
        omega
  obtain ⟨x, hxa, n, hn, hxI⟩ := hex
  have hH : ∀ β : Idx D j G.N →₀ ℕ,
      hasse (xplus X E hM) la G.w β (x : Lw (xplus X E hM) la G.w) ∈ HK (xplus X E hM) la G.w wF := fun β =>
    (mem_HK (xplus X E hM) la G.w).2
      (hasse_mem_Hfr (xplus X E hM) la G.w ((mem_HK (xplus X E hM) la G.w).1 x.2) β)
  refine ⟨x, hxa, Submodule.subset_span ⟨x, ⟨fun β _ => hH β, fun β hβ ζ => ?_⟩, rfl⟩⟩
  have := ordA_nonneg hCurve hTie ⟨_, hH β⟩ ζ (M.step5 hr _ hxI β (hn β hβ) ζ)
  simpa using this

end Top

end Formalism.L2.Pj
