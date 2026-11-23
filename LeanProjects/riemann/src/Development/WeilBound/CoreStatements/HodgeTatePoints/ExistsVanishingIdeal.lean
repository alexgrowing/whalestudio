import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IntegralClosureHeightEqOneOfLiesOver
import Development.AutomorphicSpectrum.Statements.GeometryStatements.IsPolLatticePlane
import Development.AutomorphicSpectrum.Statements.AlgebraStatements.HodgeTateNormComparison
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Birational
import Development.WeilBound.CoreStatements.HodgeTatePoints.ExistsMinorNeZero
import Development.WeilBound.CoreStatements.HodgeTatePoints.GfCurve
open CategoryTheory AlgebraicGeometry NumberField MvPolynomial GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles

namespace PositivityTheory.HtPt.Gf

section Det

variable {o Ω : Type} [CommRing o] [CommRing Ω] [Algebra o Ω] (A : Subalgebra o Ω) {n : Type} [Fintype n]
  [DecidableEq n]

theorem det_mem {M : Matrix n n Ω} (h : ∀ i j, M i j ∈ A) : M.det ∈ A := by
  rw [Matrix.det_apply']
  exact sum_mem fun σ _ => mul_mem (intCast_mem _ _) (prod_mem fun i _ => h _ _)

theorem det_add_smul {M Z : Matrix n n Ω} {c : Ω} (hM : ∀ i j, M i j ∈ A) (hZ : ∀ i j, Z i j ∈ A) (hc : c ∈ A) :
    ∃ z ∈ A, (M + c • Z).det = M.det + c * z := by
  let M' : Matrix n n A := fun i j => ⟨M i j, hM i j⟩
  let Z' : Matrix n n A := fun i j => ⟨Z i j, hZ i j⟩
  let c' : A := ⟨c, hc⟩
  have h : (M' + c' • Z').det - M'.det ∈ Ideal.span {c'} := by
    rw [← Ideal.Quotient.eq, RingHom.map_det, RingHom.map_det]
    congr 1
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    rw [Ideal.Quotient.eq, add_sub_cancel_left]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  obtain ⟨z, hz⟩ := Ideal.mem_span_singleton.1 h
  refine ⟨z, z.2, ?_⟩
  have := congrArg A.val hz
  rw [map_sub, AlgHom.map_det, AlgHom.map_det, map_mul] at this
  exact eq_add_of_sub_eq' this

end Det

section Van

variable {Ω : Type} [Field Ω] [CharZero Ω] {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)]
  {y : (Σ k, J k) → Ω} {p : ℕ} [hp : Fact p.Prime] {o : Type} [CommRing o] [Algebra o Ω]

theorem exists_vanishing_ideal
    (ho : ∀ x : Ω, x ∈ (algebraMap o Ω).range ↔ ∃ (a : ℤ) (b : ℕ), ¬ p ∣ b ∧ x = (a : Ω) / (b : Ω))
    {W : Ideal (MRing J)} (hP : W.IsPrime) (hle : mCoordIdeal y ≤ W) (hpW : (p : MRing J) ∈ W) {s : ∀ k, J k}
    (hs : ∀ k, (X ⟨k, s k⟩ : MRing J) ∉ W) :
    ∃ I : Ideal (chartRing o (mseg y) s), I ≠ ⊤ ∧ (p : chartRing o (mseg y) s) ∈ I ∧ ∀ x, x ∉ I →
      ∃ (n d : ℕ) (g : MRing J), ¬ p ∣ n ∧ IsMultiHomog g (fun _ => d) ∧ g ∉ W ∧
        n * (x : Ω) * mseg y s ^ d = aeval y g := by
  have hs0 := mseg_ne_zero hle hs
  let I : Ideal (chartRing o (mseg y) s) :=
    { carrier := {x | ∃ (n d : ℕ) (g : MRing J), ¬ p ∣ n ∧ IsMultiHomog g (fun _ => d) ∧ g ∈ W ∧
        n * (x : Ω) * mseg y s ^ d = aeval y g}
      zero_mem' := ⟨1, 0, 0, hp.out.not_dvd_one, hom_zero _, zero_mem _, by simp⟩
      add_mem' := by
        rintro u v ⟨n, d, g, h1, h2, h3, h4⟩ ⟨n', d', g', h1', h2', h3', h4'⟩
        refine ⟨n * n', d + d', n' * (g * mon s fun _ => d') + n * (mon s (fun _ => d) * g'),
          fun h => (hp.out.dvd_mul.1 h).elim h1 h1',
          hom_add (hom_nat_mul _ (hom_mul h2 (hom_mon _ _))) (hom_nat_mul _ (hom_mul (hom_mon _ _) h2')),
          add_mem (W.mul_mem_left _ (W.mul_mem_right _ h3)) (W.mul_mem_left _ (W.mul_mem_left _ h3')), ?_⟩
        simp only [map_add, map_mul, map_natCast, aeval_mon_const, ← h4, ← h4']
        push_cast; ring
      smul_mem' := by
        rintro u v ⟨n', d', g', h1', h2', h3', h4'⟩
        obtain ⟨n, d, g, h1, h2, h4⟩ := exists_rep ho hs0 u.2
        refine ⟨n * n', d + d', g * g', fun h => (hp.out.dvd_mul.1 h).elim h1 h1', hom_mul h2 h2',
          W.mul_mem_left _ h3', ?_⟩
        simp only [map_mul, ← h4, ← h4', smul_eq_mul]
        push_cast; ring }
  refine ⟨I, fun h => ?_, ⟨1, 0, p * mon s fun _ => 0, hp.out.not_dvd_one, hom_nat_mul _ (hom_mon _ _),
    W.mul_mem_right _ hpW, by simp [aeval_mon_const]⟩, fun x hx => ?_⟩
  · obtain ⟨n, d, g, h1, h2, h3, h4⟩ := (Ideal.eq_top_iff_one I).1 h
    have h5 : (n : MRing J) * mon s (fun _ => d) - g ∈ W := hle (mem_mCoordIdeal
      (hom_sub (hom_nat_mul _ (hom_mon _ _)) h2) (by simp [aeval_mon_const, ← h4]))
    have h6 : (n : MRing J) * mon s (fun _ => d) ∈ W := by simpa using add_mem h5 h3
    exact (hP.mem_or_mem h6).elim (natCast_not_mem hP.ne_top hpW h1) (mon_not_mem hP hs _)
  · obtain ⟨n, d, g, h1, h2, h4⟩ := exists_rep ho hs0 x.2
    exact ⟨n, d, g, h1, h2, fun h3 => hx ⟨n, d, g, h1, h2, h3, h4⟩, h4⟩

end Van

theorem sum_filter_lt {M : Type} [AddCommMonoid M] {N i : ℕ} (hi : i ≤ N) (f : Fin N → M) :
    ∑ l ∈ Finset.univ.filter (fun l : Fin N => (l : ℕ) < i), f l = ∑ l : Fin i, f (Fin.castLE hi l) := by
  symm
  refine Finset.sum_bij (fun l _ => Fin.castLE hi l) (by simp) (fun a _ b _ h => Fin.castLE_injective hi h) ?_
    (fun _ _ => rfl)
  intro b hb
  exact ⟨⟨b, by simpa using hb⟩, by simp, rfl⟩

theorem trivflag_deg : ∀ (Ω : Type) [Field Ω] [CharZero Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (p : ℕ) [Fact p.Prime] (o : Type) [CommRing o] [Algebra o Ω] (ho : ∀ x : Ω, x ∈ (algebraMap o Ω).range ↔ ∃ (a : ℤ) (b : ℕ), ¬ p ∣ b ∧ x = (a : Ω) / (b : Ω)) (W : Ideal (MRing J)) (N : ℕ) (b : Fin N → K → ℤ), IsMultiProjPrime W → mCoordIdeal y ≤ W → charOf W = p → ringKrullDim (MRing J ⧸ W) = ((1 + Fintype.card K : ℕ) : WithBot ℕ∞) → Num.TrivFlagMod o (p : o) y N b → (∀ i : ℕ, i ≤ N → ∑ l ∈ Finset.univ.filter (fun l : Fin N => (l : ℕ) < i), geoNum 1 W (fun _ => b l) ≤ 0) ∧ ∑ l, geoNum 1 W (fun _ => b l) = 0 := by
  intro Ω _ _ K _ J _ y p _ o _ _ ho W N b hW hle hch hdim ⟨g, h1, h2⟩
  have hpW := natCast_mem_of_charOf hch
  choose s₀ hs₀ using hW.2.2
  have hs0 := mseg_ne_zero hle hs₀
  obtain ⟨I, hI, hpI, hrep⟩ := exists_vanishing_ideal ho hW.1 hle hpW hs₀
  obtain ⟨c, hc⟩ := geoNum_one_linear W
  simp only [map_natCast] at h1 h2
  have hg : ∀ s, mseg y s ≠ 0 → ∀ i j, g s i j ∈ chartRing o (mseg y) s := fun s hs => (h1 s hs).1
  choose! h hh ρ hρ hdet using fun s hs => (h1 s hs).2
  have hsum : ∀ {ι : Type} [Fintype ι] (β : ι → K → ℤ),
      geoNum 1 W (fun _ => ∑ l, β l) = ∑ l, geoNum 1 W (fun _ => β l) := by
    intro ι _ β
    simp only [hc, Finset.sum_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
  have hneg : ∀ a : K → ℤ, geoNum 1 W (fun _ => -a) = -geoNum 1 W (fun _ => a) := by
    intro a
    simp [hc]

  have hmin : ∀ (i : ℕ) (hi : i ≤ N) (J₀ : Fin i → Fin N) s t, mseg y s ≠ 0 → mseg y t ≠ 0 →
      ∃ (m : ℕ) (z : Ω), z ∈ chartRing o (mseg y) t ∧
        (mseg y s / mseg y t) ^ m * (((g s).submatrix J₀ (Fin.castLE hi)).det -
          ((g t).submatrix J₀ (Fin.castLE hi)).det * (chartMon y s (∑ l, b (Fin.castLE hi l)) /
            chartMon y t (∑ l, b (Fin.castLE hi l)))) = p * z := by
    intro i hi J₀ s t hs ht
    obtain ⟨m, U, Z, hU, hZ, hU0, hUd, -, e⟩ := h2 s t hs ht
    obtain ⟨z, hz, ez⟩ := det_add_smul (chartRing o (mseg y) t)
      (M := (g t * U).submatrix J₀ (Fin.castLE hi)) (Z := Z.submatrix J₀ (Fin.castLE hi)) (c := p)
      (fun a a' => by
        rw [Matrix.submatrix_apply, Matrix.mul_apply]
        exact sum_mem fun l _ => mul_mem (hg t ht _ _) (hU _ _))
      (fun a a' => hZ _ _) (natCast_mem _ _)
    refine ⟨m * i, z, hz, ?_⟩
    have e1 : (g t * U).submatrix J₀ (Fin.castLE hi) + (p : Ω) • Z.submatrix J₀ (Fin.castLE hi) =
        (mseg y s / mseg y t) ^ m • (g s).submatrix J₀ (Fin.castLE hi) :=
      (congrArg (fun M : Matrix (Fin N) (Fin N) Ω => M.submatrix J₀ (Fin.castLE hi)) e).symm
    rw [e1, Matrix.det_smul, minor_mul_upper hi _ _ _ hU0] at ez
    simp only [hUd, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      Finset.prod_div_distrib, ← pow_mul] at ez
    rw [chartMon_sum hs, chartMon_sum ht]
    linear_combination ez

  let G : Matrix (Fin N) (Fin N) (chartRing o (mseg y) s₀) := fun i j => ⟨g s₀ i j, hg s₀ hs0 i j⟩
  have hG : ∀ {i : ℕ} (u v : Fin i → Fin N), (((G.submatrix u v).det : chartRing o (mseg y) s₀) : Ω) =
      ((g s₀).submatrix u v).det := fun u v => (chartRing o (mseg y) s₀).val.map_det _
  have hone : Ideal.Quotient.mk I G.det * Ideal.Quotient.mk I ⟨h s₀, hh s₀ hs0⟩ = 1 := by
    rw [← map_mul, ← map_one (Ideal.Quotient.mk I), Ideal.Quotient.eq]
    have : G.det * ⟨h s₀, hh s₀ hs0⟩ - 1 = p * ⟨ρ s₀, hρ s₀ hs0⟩ := by
      apply Subtype.ext
      have := hG id id
      simp only [Matrix.submatrix_id_id] at this
      simp [this, hdet s₀ hs0]
    rw [this]
    exact I.mul_mem_right _ hpI
  have hnt : Nontrivial (chartRing o (mseg y) s₀ ⧸ I) := Ideal.Quotient.nontrivial_iff.2 hI
  have hstep : ∀ (i : ℕ) (hi : i ≤ N), ∑ l : Fin i, geoNum 1 W (fun _ => b (Fin.castLE hi l)) ≤ 0 := by
    intro i hi
    obtain ⟨J₀, hJ₀⟩ : ∃ J₀ : Fin i → Fin N, (G.submatrix J₀ (Fin.castLE hi)).det ∉ I := by
      by_contra hall
      push Not at hall
      have := (lead_minor _ N i hi).2 ((Ideal.Quotient.mk I).mapMatrix G)
        (by rw [← RingHom.map_det]; exact IsUnit.of_mul_eq_one _ hone)
      refine bot_ne_top (α := Ideal (chartRing o (mseg y) s₀ ⧸ I)) (le_antisymm bot_le (this ▸ ?_))
      rw [Ideal.span_le]
      rintro _ ⟨J₀, rfl⟩
      have e : ((Ideal.Quotient.mk I).mapMatrix G).submatrix J₀ (Fin.castLE hi) =
        (Ideal.Quotient.mk I).mapMatrix (G.submatrix J₀ (Fin.castLE hi)) := rfl
      simp only [e, ← RingHom.map_det, SetLike.mem_coe, Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem]
      exact hall J₀
    obtain ⟨n, d, f, e1, e2, e3, e4⟩ := hrep _ hJ₀
    rw [hG] at e4
    have key := curve_sec_nef Ω K J y p o ho W (-∑ l, b (Fin.castLE hi l))
      (fun s => ((g s).submatrix J₀ (Fin.castLE hi)).det) hW hle hch hdim
      (fun s hs => det_mem _ fun a a' => hg s hs _ _) (fun s t hs ht => ?_) ⟨s₀, n, d, f, hs₀, e1, e2, e3, e4⟩
    · rw [hneg, hsum] at key
      linarith
    · obtain ⟨m, z, hz, e⟩ := hmin i hi J₀ s t hs ht
      obtain ⟨n', hn'⟩ := exists_pow_mul_trans_mem (o := o) hs ht (-∑ l, b (Fin.castLE hi l))
      refine ⟨n' + m, _, mul_mem hn' hz, ?_⟩
      have a1 := chartMon_ne_zero hs (∑ l, b (Fin.castLE hi l))
      have a2 := chartMon_ne_zero ht (∑ l, b (Fin.castLE hi l))
      rw [chartMon_neg, chartMon_neg, mul_left_comm, ← e]
      field_simp
      ring
  refine ⟨fun i hi => by rw [sum_filter_lt hi]; exact hstep i hi, le_antisymm (hstep N le_rfl) ?_⟩
  have hhI : (⟨h s₀, hh s₀ hs0⟩ : chartRing o (mseg y) s₀) ∉ I := fun hm => by
    rw [Ideal.Quotient.eq_zero_iff_mem.2 hm, mul_zero] at hone
    exact zero_ne_one hone
  obtain ⟨n, d, f, e1, e2, e3, e4⟩ := hrep _ hhI
  rw [← hsum]
  refine curve_sec_nef Ω K J y p o ho W (∑ l, b l) h hW hle hch hdim hh (fun s t hs ht => ?_)
    ⟨s₀, n, d, f, hs₀, e1, e2, e3, e4⟩
  obtain ⟨m, z, hz, e⟩ := hmin N le_rfl id s t hs ht
  change (mseg y s / mseg y t) ^ m * ((g s).det - (g t).det * (chartMon y s (∑ l, b l) /
    chartMon y t (∑ l, b l))) = p * z at e
  obtain ⟨n₁, hn₁⟩ := exists_pow_mul_trans_mem (o := o) hs ht (∑ l, b l)
  obtain ⟨n₂, hn₂⟩ := exists_pow_mul_mem_chartRing (mseg y) s t hs (hh s hs)
  obtain ⟨n₃, hn₃⟩ := exists_pow_mul_mem_chartRing (mseg y) s t hs (hρ s hs)
  have hf := div_mem_chartRing (o := o) (mseg y) t s
  have d1 := hdet s hs
  have d2 := hdet t ht
  rw [mul_div_assoc]
  generalize chartMon y s (∑ l, b l) / chartMon y t (∑ l, b l) = γ at *
  generalize mseg y s / mseg y t = φ at *
  refine ⟨m + n₁ + n₂ + n₃, φ ^ (m + n₁ + n₂) * (φ ^ n₃ * ρ s) * h t - φ ^ (m + n₃) * (φ ^ n₁ * γ) * (φ ^ n₂ * h s) * ρ t -
    φ ^ (n₁ + n₃) * z * (φ ^ n₂ * h s) * h t, sub_mem (sub_mem (mul_mem (mul_mem (pow_mem hf _) hn₃) (hh t ht))
      (mul_mem (mul_mem (mul_mem (pow_mem hf _) hn₁) hn₂) (hρ t ht)))
      (mul_mem (mul_mem (mul_mem (pow_mem hf _) hz) hn₂) (hh t ht)), ?_⟩
  linear_combination (-φ ^ (n₁ + n₂ + n₃) * h s * h t) * e + φ ^ (m + n₁ + n₂ + n₃) * h t * d1 -
    φ ^ (m + n₁ + n₂ + n₃) * γ * h s * d2

end PositivityTheory.HtPt.Gf
