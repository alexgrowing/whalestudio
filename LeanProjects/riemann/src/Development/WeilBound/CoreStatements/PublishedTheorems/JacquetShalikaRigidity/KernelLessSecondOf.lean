import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.ColumnConjugationMeasure

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

namespace PKLt2

variable {E : Type} [Field E] [NumberField E] {k : ℕ}

theorem lastRow_eq (hk : 1 ≤ k) (y : GA E k) (c : Fin k) :
    lastRow y c = y.val ⟨k - 1, by omega⟩ c := by
  unfold lastRow
  rw [Finset.sum_eq_single ⟨k - 1, by omega⟩]
  · rw [if_pos (by simp; omega)]
  · intro b _ hb
    rw [if_neg]
    intro h
    apply hb
    ext
    simp only
    omega
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem lastRow_mir (hk : 1 ≤ k) (p y : GA E k) (hp : Mir (k - 1) p) : lastRow (p * y) = lastRow y := by
  funext c
  rw [lastRow_eq hk, lastRow_eq hk, Units.val_mul, Matrix.mul_apply]
  have h1 : ∀ j, p.val ⟨k - 1, by omega⟩ j = (1 : Matrix (Fin k) (Fin k) (Ad E)) ⟨k - 1, by omega⟩ j :=
    fun j => hp _ _ (Or.inl le_rfl)
  simp only [h1, Matrix.one_apply, ite_mul, one_mul, zero_mul]
  simp

omit [NumberField E] in
theorem isMir_emb {m : ℕ} (ιE : GL (Fin k) E →* GL (Fin m) E) (h : IsEmb ιE) (γ : GL (Fin k) E) :
    IsMir k (ιE γ) := by
  intro i c hic
  rw [h γ, embM, Matrix.of_apply, dif_neg (by omega)]

end PKLt2

theorem kernel_less_second_of : D0 → N0 → H0 → RowsInCompactSet → K1 → CornerEmbedding → TransformsEmbedding → FourierSeriesColumn → ShortRowsEmbedding → K6 → KLt2 := by
  intro hD0 hN0 hH0 hG5 hK1 hK5e hK5a hK5b hK5c hK6 E _ _ _ m k hk hkm ψ hψ S hS ι hι α α' φ' hsec U φ hprep
  obtain ⟨hDpos, hDmul, hDcont, hDrat, -⟩ := hD0 E k
  obtain ⟨hFgood, hpT, -, -, hsupp, hbd⟩ := hK5a E m k hk hkm ψ hψ ι hι φ hprep.good
  obtain ⟨C6, hC6c, hC6⟩ := hK6 E m k hk hkm ψ hψ S hS ι hι α (m ^ 3) U φ hprep
  obtain ⟨-, -, -, -, -, -, -, -, -, hNlast⟩ := hN0 E k k hk le_rfl
  obtain ⟨hhtpos, -, -, -, hB5, -, -⟩ := hH0 E k
  obtain ⟨-, hdminpos, -⟩ := hK1 E m (by omega)
  obtain ⟨hιc, -, -, -, -, -, hιrat, -⟩ := (hK5e E m k hkm.le).2 ι hι
  obtain ⟨ιE, hιE⟩ := (hK5e E m k hkm.le).1 E
  have hrow : ∀ (g : GA E k) (ξ : RowT E k k),
      pT ψ k (m - k) (φ : GA E m → ℂ) (ι (ratGL E k (gam ξ) * g)) ≠ 0 →
      lastRow (ratGL E k (gam ξ) * g) ∈ C6 := by
    intro g ξ hne
    obtain ⟨p, hp, hw⟩ := hsupp _ hne
    have := hC6 _ hw
    rwa [PKLt2.lastRow_mir hk _ _ hp] at this
  have hfin : ∀ g : GA E k,
      {ξ : RowT E k k | colT ψ k (pT ψ (k + 1) (m - (k + 1)) (φ : GA E m → ℂ))
        (ι (ratGL E k (gam ξ) * g)) ≠ 0}.Finite := by
    intro g
    exact ((hG5 E k hk C6 hC6c).1 g).subset fun ξ hξ => hrow g ξ (by rw [hpT]; exact hξ)
  have hsumF : ∀ g, sumF (fun g => pT ψ k (m - k) (φ : GA E m → ℂ) (ι g)) g =
      pT ψ (k + 1) (m - (k + 1)) (φ : GA E m → ℂ) (ι g) := by
    intro g
    rw [hpT]
    exact (hK5b E m k hk hkm ψ hψ ι hι _ hFgood g).2 (hfin g)
  have hFb : ∀ x, ‖pT ψ (k + 1) (m - (k + 1)) (φ : GA E m → ℂ) x‖ ≤ ‖φ‖ := fun x =>
    hbd (k + 1) x ‖φ‖ (by omega) (by omega) fun u _ => φ.norm_coe_le_norm _
  have hcpow : ∀ g : GA E k, ‖(Dt g : ℂ) ^ (-(((m : ℂ) - k) / 2))‖ = Dt g ^ (-(((m : ℝ) - k) / 2)) := by
    intro g
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (hDpos g)]
    congr 1
    simp
  have hcont : Continuous fun g : GA E k => pT ψ (k + 1) (m - (k + 1)) (φ : GA E m → ℂ) (ι g) *
      conj (φ' g) * (Dt g : ℂ) ^ (-(((m : ℂ) - k) / 2)) := by
    refine ((hFgood.cont.comp hιc).mul (Complex.continuous_conj.comp φ'.continuous)).mul ?_
    exact (Complex.continuous_ofReal.comp hDcont).cpow continuous_const
      fun g => Complex.ofReal_mem_slitPlane.2 (hDpos g)
  simp_rw [hsumF]
  refine ⟨hcont.measurable, measurable_zero, ?_, fun _ _ => rfl, fun _ _ => rfl, ⟨0, fun _ => by simp⟩, ?_, ?_⟩
  · intro γ g
    dsimp only
    rw [map_mul ι, hιrat ιE hιE γ, hFgood.left _ (PKLt2.isMir_emb ιE hιE γ), hsec.inv γ g, hDmul, hDrat, one_mul]
  · intro M
    obtain ⟨C₂, hC₂⟩ := hsec.dec (k * M)
    obtain ⟨B, hB⟩ := hB5 C6 hC6c
    refine ⟨‖φ‖ * max C₂ 0 * max B 0 ^ (k * M), fun g hg => ?_⟩
    have hD := hDpos g
    have hk0 : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
    have hnorm : ‖(Dt g : ℂ) ^ (-(((m : ℂ) - k) / 2))‖ ≤ 1 := by
      rw [hcpow]
      apply Real.rpow_le_one_of_one_le_of_nonpos hg
      have : (k : ℝ) < m := by exact_mod_cast hkm
      linarith
    have hnn : 0 ≤ max B 0 ^ (k * M) * (Dt g ^ M)⁻¹ := by positivity
    by_cases hz : pT ψ (k + 1) (m - (k + 1)) (φ : GA E m → ℂ) (ι g) = 0
    · rw [hz, zero_mul, zero_mul, norm_zero]
      exact mul_nonneg (mul_nonneg (mul_nonneg (norm_nonneg _) (le_max_right _ _)) (by positivity))
        (by positivity)
    obtain ⟨ξ, hξ⟩ : ∃ ξ : RowT E k k, pT ψ k (m - k) (φ : GA E m → ℂ) (ι (ratGL E k (gam ξ) * g)) ≠ 0 := by
      by_contra hcon
      simp only [not_exists, not_not] at hcon
      apply hz
      rw [← hsumF g, sumF]
      simp only [hcon, tsum_zero]
    have hlr := hrow g ξ hξ
    rw [hNlast ξ g] at hlr
    have hht := hB g ξ.1 ξ.2.1 hlr
    have hp := hhtpos g ξ.1 ξ.2.1
    have hht2 : ht g ξ.1 ≤ max B 0 / Dt g ^ ((k : ℝ)⁻¹) := by
      unfold ht
      gcongr
      exact hht.trans (le_max_left _ _)
    have hDk : (Dt g ^ ((k : ℝ)⁻¹)) ^ (k * M) = Dt g ^ M := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hD.le, Nat.cast_mul, ← mul_assoc, inv_mul_cancel₀ hk0, one_mul,
        Real.rpow_natCast]
    have hpow : ht g ξ.1 ^ (k * M) ≤ max B 0 ^ (k * M) * (Dt g ^ M)⁻¹ := by
      calc ht g ξ.1 ^ (k * M) ≤ (max B 0 / Dt g ^ ((k : ℝ)⁻¹)) ^ (k * M) := pow_le_pow_left₀ hp.le hht2 _
        _ = _ := by rw [div_pow, hDk, div_eq_mul_inv]
    have hφ' : ‖φ' g‖ ≤ max C₂ 0 * (max B 0 ^ (k * M) * (Dt g ^ M)⁻¹) :=
      (hC₂ g ξ.1 ξ.2.1).trans ((mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)).trans
        (mul_le_mul_of_nonneg_left hpow (le_max_right _ _)))
    rw [norm_mul, norm_mul, RCLike.norm_conj]
    calc ‖pT ψ (k + 1) (m - (k + 1)) (φ : GA E m → ℂ) (ι g)‖ * ‖φ' g‖ * ‖(Dt g : ℂ) ^ (-(((m : ℂ) - k) / 2))‖
        ≤ ‖φ‖ * (max C₂ 0 * (max B 0 ^ (k * M) * (Dt g ^ M)⁻¹)) * 1 :=
          mul_le_mul (mul_le_mul (hFb _) hφ' (norm_nonneg _) (norm_nonneg _)) hnorm (norm_nonneg _)
            (mul_nonneg (norm_nonneg _) ((norm_nonneg _).trans hφ'))
      _ = _ := by ring
  · obtain ⟨C5, hC5⟩ := hK5c E m k hk hkm ι hι
    obtain ⟨Cφ, hCφ⟩ := hprep.dec
    have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast (by omega : 2 ≤ m)
    have hkm' : (k : ℝ) < m := by exact_mod_cast hkm
    have hm0 : (m : ℝ) ≠ 0 := by linarith
    have hm1 : (m : ℝ) - 1 ≠ 0 := by linarith
    have he : (((m : ℝ) - 1)⁻¹ - (m : ℝ)⁻¹) * ((m ^ 3 : ℕ) : ℝ) = (m : ℝ) ^ 2 / ((m : ℝ) - 1) := by
      push_cast
      field_simp
      ring
    have hmle : (m : ℝ) ≤ (m : ℝ) ^ 2 / ((m : ℝ) - 1) := by
      rw [le_div_iff₀ (by linarith)]
      nlinarith
    have hexp : 0 ≤ (((m : ℝ) - 1)⁻¹ - (m : ℝ)⁻¹) * ((m ^ 3 : ℕ) : ℝ) + -(((m : ℝ) - k) / 2) := by
      rw [he]
      linarith
    refine ⟨max Cφ 0 * max C5 0 ^ (m ^ 3) * ‖φ'‖, fun g hg => ?_⟩
    have hD := hDpos g
    have hFs : ‖pT ψ (k + 1) (m - (k + 1)) (φ : GA E m → ℂ) (ι g)‖ ≤ max Cφ 0 * (max C5 0 ^ (m ^ 3) *
        Dt g ^ ((((m : ℝ) - 1)⁻¹ - (m : ℝ)⁻¹) * ((m ^ 3 : ℕ) : ℝ))) := by
      refine hbd (k + 1) (ι g) _ (by omega) (by omega) fun u hu => ?_
      have hdm := (hC5 g u).2 hu
      have hpos := hdminpos (u * ι g)
      have hw0 : 0 ≤ wt (m ^ 3) (u * ι g) := pow_nonneg (le_min zero_le_one hpos.le) _
      calc ‖φ (u * ι g)‖ ≤ Cφ * wt (m ^ 3) (u * ι g) := hCφ _
        _ ≤ max Cφ 0 * wt (m ^ 3) (u * ι g) := mul_le_mul_of_nonneg_right (le_max_left _ _) hw0
        _ ≤ _ := by
          apply mul_le_mul_of_nonneg_left _ (le_max_right _ _)
          unfold wt
          calc min 1 (dmin (u * ι g)) ^ (m ^ 3)
              ≤ (max C5 0 * Dt g ^ (((m : ℝ) - 1)⁻¹ - (m : ℝ)⁻¹)) ^ (m ^ 3) :=
                pow_le_pow_left₀ (le_min zero_le_one hpos.le) ((min_le_right _ _).trans (hdm.trans
                  (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hD.le _)))) _
            _ = _ := by rw [mul_pow, ← Real.rpow_natCast (Dt g ^ _), ← Real.rpow_mul hD.le]
    have hrp : Dt g ^ ((((m : ℝ) - 1)⁻¹ - (m : ℝ)⁻¹) * ((m ^ 3 : ℕ) : ℝ)) * Dt g ^ (-(((m : ℝ) - k) / 2)) ≤ 1 := by
      rw [← Real.rpow_add hD]
      exact Real.rpow_le_one hD.le hg.le hexp
    have hφ'b : ‖φ' g‖ ≤ ‖φ'‖ := φ'.norm_coe_le_norm g
    have hA : 0 ≤ max Cφ 0 * max C5 0 ^ (m ^ 3) * ‖φ'‖ :=
      mul_nonneg (mul_nonneg (le_max_right _ _) (pow_nonneg (le_max_right _ _) _)) (norm_nonneg _)
    rw [Pi.zero_apply, sub_zero, norm_mul, Complex.norm_real, Real.norm_of_nonneg hD.le, norm_mul, norm_mul,
      RCLike.norm_conj, hcpow, mul_comm _ (Dt g)]
    apply mul_le_mul_of_nonneg_left _ hD.le
    calc ‖pT ψ (k + 1) (m - (k + 1)) (φ : GA E m → ℂ) (ι g)‖ * ‖φ' g‖ * Dt g ^ (-(((m : ℝ) - k) / 2))
        ≤ max Cφ 0 * (max C5 0 ^ (m ^ 3) * Dt g ^ ((((m : ℝ) - 1)⁻¹ - (m : ℝ)⁻¹) * ((m ^ 3 : ℕ) : ℝ))) *
            ‖φ'‖ * Dt g ^ (-(((m : ℝ) - k) / 2)) := by
          apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hD.le _)
          exact mul_le_mul hFs hφ'b (norm_nonneg _) ((norm_nonneg _).trans hFs)
      _ = max Cφ 0 * max C5 0 ^ (m ^ 3) * ‖φ'‖ * (Dt g ^ ((((m : ℝ) - 1)⁻¹ - (m : ℝ)⁻¹) * ((m ^ 3 : ℕ) : ℝ)) *
            Dt g ^ (-(((m : ℝ) - k) / 2))) := by ring
      _ ≤ max Cφ 0 * max C5 0 ^ (m ^ 3) * ‖φ'‖ * 1 := mul_le_mul_of_nonneg_left hrp hA
      _ = _ := mul_one _

end PositivityTheory.AdelicQuotientData

end
