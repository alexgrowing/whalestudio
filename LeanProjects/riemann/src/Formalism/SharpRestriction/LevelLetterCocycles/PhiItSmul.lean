import Formalism.SharpRestriction.LevelLetterCocycles.CoordHomMapTrace

noncomputable section

namespace Formalism.MainNotions.WachCoordinates.Br

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions

section Model

variable {O : Type} [CommRing O] {Bs : Formalism.ExponentWindows.E.Base O} {n : ℕ} {V : Type} [AddCommGroup V]
  [Module (PowerSeries O) V]

def PsM (Bs : Formalism.ExponentWindows.E.Base O) : Submonoid (PowerSeries O) := Submonoid.closure (Set.range Bs.p)

theorem p_mem (s : ℕ) : Bs.p s ∈ PsM Bs := Submonoid.subset_closure ⟨s, rfl⟩

theorem q_mem : Bs.q ∈ PsM Bs := p_mem (Bs := Bs) 0

theorem φ_p (s : ℕ) : Bs.φ (Bs.p s) = Bs.p (s + 1) := by
  rw [Formalism.ExponentWindows.E.Base.p, Formalism.ExponentWindows.E.Base.p, Function.iterate_succ_apply']

theorem φ_mem {f : PowerSeries O} (hf : f ∈ PsM Bs) : Bs.φ f ∈ PsM Bs := by
  induction hf using Submonoid.closure_induction with
  | mem x hx =>
    obtain ⟨s, rfl⟩ := hx
    rw [φ_p]
    exact p_mem _
  | one => rw [map_one]; exact one_mem _
  | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy

theorem φit_mem (k : ℕ) {f : PowerSeries O} (hf : f ∈ PsM Bs) : (⇑Bs.φ)^[k] f ∈ PsM Bs := by
  induction k with
  | zero => exact hf
  | succ k ih => rw [Function.iterate_succ_apply']; exact φ_mem ih

theorem Lam_mem (H : ℕ → ℕ) (ell : ℕ) : Formalism.ExponentWindows.abelian₂ Bs.p H ell ∈ PsM Bs :=
  Submonoid.prod_mem _ fun s _ => pow_mem (p_mem s) _

variable (L : Formalism.ExponentWindows.E.Lat Bs n V)

theorem phiIt_smul' (i : ZMod n) (k : ℕ) (a : PowerSeries O) (x : V) :
    L.phiIt i k (a • x) = (⇑Bs.φ)^[k] a • L.phiIt i k x := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Formalism.ExponentWindows.E.Lat.phiIt, ih, L.φ_semi, Function.iterate_succ_apply']
    rfl

theorem phiIt_N (hh : ℕ) (h5 : ∀ i, L.P5M i hh) (k : ℕ) :
    ∃ Pr ∈ PsM Bs, ∀ i, ∀ x ∈ L.N i, Pr • L.phiIt i k x ∈ L.N (i + (k : ZMod n)) := by
  induction k with
  | zero =>
    refine ⟨1, one_mem _, fun i x hx => ?_⟩
    rw [one_smul, Nat.cast_zero, add_zero]
    exact hx
  | succ k ih =>
    obtain ⟨Pr, hPr, h⟩ := ih
    refine ⟨Bs.q ^ hh * Bs.φ Pr, mul_mem (pow_mem q_mem _) (φ_mem hPr), fun i x hx => ?_⟩
    rw [Formalism.ExponentWindows.E.Lat.phiIt, mul_smul, ← L.φ_semi]
    apply h5
    have e : i + ((k + 1 : ℕ) : ZMod n) - 1 = i + (k : ZMod n) := by push_cast; ring
    rw [e]
    exact h i x hx

theorem pull_N (hh : ℕ) (h5 : ∀ i, L.P5M i hh) (k : ℕ) :
    ∃ Pr ∈ PsM Bs, ∀ i, ∀ x ∈ L.pull i k, Pr • x ∈ L.N (i + (k : ZMod n)) := by
  obtain ⟨Pr, hPr, h⟩ := phiIt_N L hh h5 k
  refine ⟨Pr, hPr, fun i x hx => ?_⟩
  have : L.pull i k ≤ Formalism.ExponentWindows.E.dv Pr (L.N (i + (k : ZMod n))) := by
    rw [Formalism.ExponentWindows.E.Lat.pull, Submodule.span_le]
    rintro _ ⟨u, hu, rfl⟩
    exact h i u hu
  exact this hx

theorem relay_N (hh : ℕ) (h5 : ∀ i, L.P5M i hh) (c c' : ZMod n) (k j : ℕ)
    (hc : c' + (k : ZMod n) = c) (Λ : PowerSeries O) (hΛ : Λ ∈ PsM Bs) (a : PowerSeries O) (w τ : V)
    (hw : w ∈ Formalism.ExponentWindows.E.dv Λ (L.pull c' k)) (hτ : τ ∈ L.pull c j) :
    ∃ Pr ∈ PsM Bs, Pr • (a • L.phiIt c j w - τ) ∈ L.N (c + (j : ZMod n)) := by
  obtain ⟨Prk, hPrk, hk⟩ := pull_N L hh h5 k
  obtain ⟨Prj, hPrj, hj⟩ := phiIt_N L hh h5 j
  obtain ⟨Prj', hPrj', hj'⟩ := pull_N L hh h5 j
  have h1 : (Prk * Λ) • w ∈ L.N c := by
    rw [mul_smul, ← hc]
    exact hk c' _ hw
  have h2 := hj c _ h1
  rw [phiIt_smul'] at h2
  have h3 := hj' c τ hτ
  refine ⟨Prj' * (Prj * (⇑Bs.φ)^[j] (Prk * Λ)),
    mul_mem hPrj' (mul_mem hPrj (φit_mem j (mul_mem hPrk hΛ))), ?_⟩
  rw [smul_sub]
  refine Submodule.sub_mem _ ?_ ?_
  · have : (Prj' * (Prj * (⇑Bs.φ)^[j] (Prk * Λ))) • a • L.phiIt c j w =
        (Prj' * a) • Prj • (⇑Bs.φ)^[j] (Prk * Λ) • L.phiIt c j w := by
      simp only [smul_smul]
      congr 1
      ring
    rw [this]
    exact Submodule.smul_mem _ _ h2
  · have : (Prj' * (Prj * (⇑Bs.φ)^[j] (Prk * Λ))) • τ = (Prj * (⇑Bs.φ)^[j] (Prk * Λ)) • Prj' • τ := by
      simp only [smul_smul]
      congr 1
      ring
    rw [this]
    exact Submodule.smul_mem _ _ h3

end Model

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n] {W : LocWach PD LL O v n}
    {I : BaseId W} {T : LocLat G Qp LL O}

theorem prod_pad {R : Type} [CommMonoid R] (F : ℕ → R) (k : ℕ → ℕ) {m m' : ℕ} (h : m ≤ m') :
    ∏ s ∈ Finset.range m', F s ^ (if s < m then k s else 0) = ∏ s ∈ Finset.range m, F s ^ k s := by
  rw [← Finset.prod_subset (Finset.range_subset_range.2 h)]
  · exact Finset.prod_congr rfl fun s hs => by rw [if_pos (Finset.mem_range.1 hs)]
  · intro s _ hs
    rw [if_neg (fun h' => hs (Finset.mem_range.2 h')), pow_zero]

theorem isPs_one : IsPs W (1 : LetA O n) := ⟨fun _ => 0, 0, by simp⟩

theorem isPs_pS (s : ℕ) : IsPs W (pS W s) := by
  refine ⟨fun t => if t = s then 1 else 0, s + 1, ?_⟩
  rw [Finset.prod_eq_single s]
  · simp
  · intro t _ ht; simp [ht]
  · intro h; exact absurd (Finset.mem_range.2 (Nat.lt_succ_self s)) h

theorem isPs_mul {f g : LetA O n} (hf : IsPs W f) (hg : IsPs W g) : IsPs W (f * g) := by
  obtain ⟨k, m, rfl⟩ := hf
  obtain ⟨k', m', rfl⟩ := hg
  refine ⟨fun s => (if s < m then k s else 0) + (if s < m' then k' s else 0), m + m', ?_⟩
  simp only [pow_add, Finset.prod_mul_distrib]
  rw [prod_pad _ k (Nat.le_add_right m m'), prod_pad _ k' (Nat.le_add_left m' m)]

theorem isPs_d {f : PowerSeries O} (hf : f ∈ PsM I.Bs) : IsPs W (I.d f) := by
  induction hf using Submonoid.closure_induction with
  | mem x hx =>
    obtain ⟨s, rfl⟩ := hx
    rw [I.d_p]
    exact isPs_pS s
  | one => rw [map_one]; exact isPs_one
  | mul x y _ _ hx hy => rw [map_mul]; exact isPs_mul hx hy

theorem d_smul_NΔ (f : PowerSeries O) {x : W.DD T} (hx : x ∈ W.NΔ T) : I.d f • x ∈ W.NΔ T :=
  ⟨(W.N T).smul_mem _ hx.1, fun δ hδ => by rw [γD_smulA, I.γA_Δ δ hδ, hx.2 δ hδ]⟩

theorem tot_NΔ (C : Coord W I T) (x : ZMod n → C.V) (hx : ∀ i, x i ∈ (latOf C).N i) :
    tot C x ∈ W.NΔ T :=
  ⟨(W.N T).sum_mem fun i _ => hx i, fun δ hδ => tot_Δ C x δ hδ⟩

theorem tot_single (C : Coord W I T) (k : ZMod n) (x : C.V) : tot C (Pi.single k x) = C.t k x := by
  rw [tot, Finset.sum_eq_single k]
  · rw [Pi.single_eq_same]
  · intro i _ hi
    rw [Pi.single_eq_of_ne hi, C.t_zero]
  · intro h; exact absurd (Finset.mem_univ k) h

theorem tot_sm (C : Coord W I T) (M : ℕ) (z : ZMod n → C.V)
    (hz : ∀ i, z i ∈ Formalism.ExponentWindows.E.sm (PowerSeries.X ^ M) ((latOf C).N i)) :
    tot C z ∈ mulSet W T (W.π₀ ^ M) (W.NΔ T) := by
  have h : ∀ i, ∃ x ∈ (latOf C).N i, (PowerSeries.X ^ M : PowerSeries O) • x = z i := fun i => hz i
  choose x hx hxz using h
  refine ⟨tot C x, tot_NΔ C x hx, ?_⟩
  have : z = (PowerSeries.X ^ M : PowerSeries O) • x := by
    funext i
    exact (hxz i).symm
  rw [this, tot_smul, map_pow, I.d_X]

theorem rho_of (hF1 : F1 W) (hF2 : F2 W) (hcr : IsCrys PD T.ρ) (hh M : ℕ)
    (hJ : ∀ τ : K →ₐ[Qp] LL, JumpsInV PD T.ρ τ (Set.Icc (-(hh : ℤ)) hh))
    (hM : hh < (PD.p - 1) * M) (C : Coord W I T) (h5 : ∀ i, (latOf C).P5M i hh)
    (c c' : ZMod n) (k : ℕ) (hc : c' + (k : ZMod n) = c) (Λ : PowerSeries O) (hΛ : Λ ∈ PsM I.Bs)
    (w : C.V) (hw : w ∈ Formalism.ExponentWindows.E.dv Λ ((latOf C).pull c' k)) (j g sig : ℕ) (y z : ZMod n → C.V)
    (hρ : (latOf C).IsRho c j M g sig w y z) : (y, z) ∈ Zf C := by
  obtain ⟨τ, ⟨hτ, -⟩, hy, hcoc, hz⟩ := hρ
  have hZ : (tot C y, tot C z) ∈ W.wachCocyclesDelta T := (cocycle_iff C y z).1 hcoc
  have hzM := tot_sm C M z hz
  have hyt : tot C y = C.t (c + (j : ZMod n)) (I.Bs.lc ^ sig • (latOf C).phiIt c j w - τ) := by
    rw [hy, tot_single]
  refine (mem_Zf C _).2 ⟨⟨_, hZ⟩, ?_, rfl⟩
  refine hF2 hh M hM T hcr hJ (c + (j : ZMod n)) ⟨_, hZ⟩ ⟨?_, ?_, hzM⟩ ?_
  · change (letE (c + (j : ZMod n)) : LetA O n) • tot C y = tot C y
    rw [hyt]
    exact C.t_letter _ _
  · change W.γD T W.gamK (tot C y) - tot C y ∈ mulSet W T (W.π₀ ^ M) (W.NΔ T)
    rw [((mem_Z1DΔ _ _).1 hZ).1]
    obtain ⟨x, hx, hxz⟩ := hzM
    obtain ⟨x', hx', hφ⟩ := ((hF1 hh M hM).1 T hcr hJ).1 x hx
    refine ⟨I.d I.Bs.q • x' - x, (W.NΔ T).sub_mem (d_smul_NΔ _ hx') hx, ?_⟩
    rw [hxz, hφ, smul_sub, I.d_q, mul_smul]
  · obtain ⟨Pr, hPr, hN⟩ := relay_N (latOf C) hh h5 c c' k j hc Λ hΛ (I.Bs.lc ^ sig) w τ hw hτ
    refine ⟨I.d Pr, isPs_d hPr, ?_⟩
    change I.d Pr • tot C y ∈ W.NΔ T
    rw [hyt, ← C.t_smul]
    exact ⟨hN, fun δ hδ => C.t_Δ _ _ δ hδ⟩

theorem rho_field (hF1 : F1 W) (hF2 : F2 W) (hcr : IsCrys PD T.ρ) (hh : ℕ)
    (hJ : ∀ τ : K →ₐ[Qp] LL, JumpsInV PD T.ρ τ (Set.Icc (-(hh : ℤ)) hh)) (hp : 2 ≤ PD.p)
    (C : Coord W I T) (h5 : ∀ i, (latOf C).P5M i hh) (Cu : Formalism.ExponentWindows.E.Cuts n) (H : ZMod n → ℕ → ℕ)
    (j g sig : ℕ) :
    ∀ c ∈ Cu.cuts, ∀ w, (latOf C).Wc Cu (Formalism.ExponentWindows.E.LamOf I.Bs Cu H) c w →
      ∀ y z, (latOf C).IsRho c j (Formalism.ExponentWindows.E.parM I.Bs.ℓ hh g) g sig w y z → (y, z) ∈ Zf C := by
  intro c _ w hw y z hρ
  refine rho_of hF1 hF2 hcr hh _ hJ ?_ C h5 c (c - (Cu.ell c : ZMod n)) (Cu.ell c) (sub_add_cancel _ _)
    _ (Lam_mem (H c) (Cu.ell c)) w hw.2 j g sig y z hρ
  rw [Formalism.ExponentWindows.E.parM, I.ℓ_eq]
  have := Nat.lt_mul_div_succ (hh + 2 * g) (show 0 < PD.p - 1 by omega)
  omega

end Formalism.MainNotions.WachCoordinates.Br
