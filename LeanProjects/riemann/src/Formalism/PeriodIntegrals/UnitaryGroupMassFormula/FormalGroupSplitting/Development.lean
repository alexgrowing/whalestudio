import Formalism.PeriodIntegrals.FglPhSplit

noncomputable section

namespace PI.FglPhSplit.Wk

open PI.FglPhSplit MvPowerSeries

def S1 : Prop :=
  ∀ (K : Type) [Field K] (l ex : PowerSeries K), PowerSeries.constantCoeff ex = 0 →
    PowerSeries.subst ex l = PowerSeries.X →
    PowerSeries.constantCoeff l = 0 ∧ PowerSeries.subst l ex = PowerSeries.X

def S2 : Prop :=
  ∀ (K : Type) [Field K] (g : Dat K), PowerSeries.constantCoeff g.ex = 0 →
    PowerSeries.subst g.ex g.l = PowerSeries.X → PowerSeries.constantCoeff g.ph = 0 →
    ∀ (κ ι ι' : Type) [Fintype κ] [Fintype ι] [Fintype ι'] (a : ι → κ → K × K)
      (a' : ι' → κ → K × K), (∀ f f', hP (a f) (a' f') = 0) → g.sdR a a' = 0

def S3 : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (W : Subring K) (σ : Type) (f g f' g' : MvPowerSeries σ K),
    SimeqW W f g → SimeqW W f' g' → SimeqW W (f + f') (g + g')

def S4 : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (W : Subring K) (g : Dat K),
    PowerSeries.constantCoeff g.ex = 0 → PowerSeries.subst g.ex g.l = PowerSeries.X →
    ∀ (κ ι ι' : Type) [Fintype κ] [Fintype ι] [Fintype ι'] (b b' : ι → κ → K × K),
      SimeqW W (g.PhOn (Sum.elim b b')) (g.beSum ι) →
      SimeqW W (g.PhV (Sum.elim b b') (fun e => (X (Sum.inl e) : MvPowerSeries ((ι ⊕ ι) ⊕ ι') K)))
        (∑ e : ι, g.be (X (Sum.inl (Sum.inl e))) (X (Sum.inl (Sum.inr e))))

theorem coeff_expMv {K : Type} [Field K] {σ : Type} (f : MvPowerSeries σ K) (α : σ →₀ ℕ) :
    coeff α (expMv f) =
      ∑ n ∈ Finset.range ((α.sum fun _ k => k) + 1), coeff α (f ^ n) / (n.factorial : K) := rfl

theorem simeqW_refl {K : Type} [Field K] (W : Subring K) {σ : Type} (f : MvPowerSeries σ K) :
    SimeqW W f f := by
  classical
  refine ⟨by simp, fun n => ?_⟩
  rw [sub_self, coeff_expMv]
  refine W.sum_mem fun k _ => ?_
  rcases k with _ | k
  · rw [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, MvPowerSeries.coeff_one]
    split_ifs
    · exact W.one_mem
    · exact W.zero_mem
  · simp

theorem simeqW_of_eq {K : Type} [Field K] {W : Subring K} {σ : Type} {f g f' g' : MvPowerSeries σ K}
    (h : SimeqW W f g) (hf : f = f') (hg : g = g') : SimeqW W f' g' := by
  subst hf hg
  exact h

theorem target_of (h2 : S2) (h3 : S3) (h4 : S4) : Target := by
  intro K _ _ W g S hex hl hph hSD hDI κ ι ι' _ _ _ b b' b'' hb hb' hb'' hD hbb hb'b
  have hmem : ∀ e k, Sum.elim b b' e k ∈ S := by
    rintro (e | e) k
    · exact hb e k
    · exact hb' e k
  have hA := hSD κ (ι ⊕ ι) ι' (Sum.elim b b') b'' hmem hb''
  have hR0 : g.sdR (Sum.elim b b') b'' = 0 := by
    apply h2 K g hex hl hph κ (ι ⊕ ι) ι' (Sum.elim b b') b''
    rintro (e | e) f
    · exact hbb e f
    · exact hb'b e f
  have hB := h4 K W g hex hl κ ι ι' b b' (hDI κ ι b b' hb hb' hD)
  have hC := h3 K W _ _ _ _ _ hA hB
  have hE := h3 K W _ _ _ _ _ hC
    (simeqW_refl W (g.PhV b'' (fun f => (X (Sum.inr f) : MvPowerSeries ((ι ⊕ ι) ⊕ ι') K))))
  refine simeqW_of_eq hE ?_ ?_
  · unfold Dat.sdL
    abel
  · rw [hR0, zero_add]

end PI.FglPhSplit.Wk

end
