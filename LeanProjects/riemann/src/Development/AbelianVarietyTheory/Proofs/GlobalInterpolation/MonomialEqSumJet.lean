import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TranslateMomentsAll
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DerivationCoordinateChange
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InducedTypeThetaGenusOnePermutes
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable GlobalTheory.MomT

noncomputable section

namespace GlobalTheory.MonoJet

open GlobalTheory.Proof.DirectionalDerivative GlobalTheory.IndefiniteRowSideFullHecke.PolynomialIntegralityJets MvPowerSeries

variable (D : D7) {p : ℕ} [Fact p.Prime] (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) {N N' : ℕ}

theorem embT_injective : Function.Injective (TaylorLogMetric.embT D) := by
  intro τ τ' h
  apply D.eTau.injective
  apply (GlobalTheory.InducedType.galK_bijective D.host).1
  refine AlgEquiv.ext fun x => D.host.φ₀.injective ?_
  exact congrArg (fun f : D.host.E →+* ℂ => f x) h

theorem lamC_injOn {x y : ℂ} (hx : x ∈ TaylorLogMetric.Qbar) (hy : y ∈ TaylorLogMetric.Qbar) (h : TaylorLogMetric.lamC lam x = TaylorLogMetric.lamC lam y) : x = y := by
  rw [TaylorLogMetric.lamC, TaylorLogMetric.lamC, dif_pos hx, dif_pos hy] at h
  exact congrArg Subtype.val (lam.injective h)

theorem emb_mem {A : Type} [Field A] [NumberField A] (f : A →+* ℂ) (x : A) : f x ∈ TaylorLogMetric.Qbar :=
  mem_algebraicClosure_iff.2 ((Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x).algHom f.toRatAlgHom)

theorem lamC_add {x y : ℂ} (hx : x ∈ TaylorLogMetric.Qbar) (hy : y ∈ TaylorLogMetric.Qbar) :
    TaylorLogMetric.lamC lam (x + y) = TaylorLogMetric.lamC lam x + TaylorLogMetric.lamC lam y := by
  rw [TaylorLogMetric.lamC, TaylorLogMetric.lamC, TaylorLogMetric.lamC, dif_pos hx, dif_pos hy, dif_pos (add_mem hx hy), ← map_add]
  rfl

theorem lamC_sum {ι : Type} (s : Finset ι) (f : ι → ℂ) (hf : ∀ i, f i ∈ TaylorLogMetric.Qbar) :
    TaylorLogMetric.lamC lam (∑ i ∈ s, f i) = ∑ i ∈ s, TaylorLogMetric.lamC lam (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty, TaylorLogMetric.lamC, dif_pos (zero_mem _)]
    exact map_zero lam
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, lamC_add lam (hf a) (sum_mem fun i _ => hf i), ih]

theorem exists_single (τ : D.what₂.Tau) : ∃ (k : ℕ) (γ : Fin k → ℂ_[p]) (x : Fin k → D.host.E),
    (∑ l, γ l * TaylorLogMetric.tauEmb D lam τ (x l) = 1) ∧ ∀ τ', τ' ≠ τ → ∑ l, γ l * TaylorLogMetric.tauEmb D lam τ' (x l) = 0 := by
  classical
  choose g hg using fun τ => exists_lamHom lam (TaylorLogMetric.embT D τ)
  have hinj : Function.Injective fun τ => (g τ : D.host.E →* ℂ_[p]) := by
    intro a b h
    apply embT_injective D
    refine RingHom.ext fun x => lamC_injOn lam (emb_mem _ _) (emb_mem _ _) ?_
    rw [hg, hg]
    exact congrArg (fun f : D.host.E →* ℂ_[p] => f x) h
  have hli : LinearIndependent ℂ_[p] fun τ => (g τ : D.host.E → ℂ_[p]) :=
    (linearIndependent_monoidHom D.host.E ℂ_[p]).comp _ hinj
  have hsp := span_flip_eq_top_iff_linearIndependent.2 hli
  have hm : (Pi.single τ 1 : D.what₂.Tau → ℂ_[p]) ∈
      Submodule.span ℂ_[p] (Set.range (flip fun τ => (g τ : D.host.E → ℂ_[p]))) := hsp ▸ Submodule.mem_top
  obtain ⟨k, γ, v, hv⟩ := Submodule.mem_span_set'.1 hm
  choose x hx using fun l => (v l).2
  have key : ∀ τ', ∑ l, γ l * TaylorLogMetric.tauEmb D lam τ' (x l) = (Pi.single τ 1 : D.what₂.Tau → ℂ_[p]) τ' := by
    intro τ'
    rw [← hv, Finset.sum_apply]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Pi.smul_apply, ← hx l, TaylorLogMetric.tauEmb, hg]
    rfl
  exact ⟨k, γ, x, by rw [key, Pi.single_eq_same], fun τ' h => by rw [key, Pi.single_eq_of_ne h]⟩

open Classical in

theorem exists_vecY (v : D.what₂.Tau × Fin N' × Fin N) : ∃ (k : ℕ) (γ : Fin k → ℂ_[p])
    (z : Fin k → Matrix (Fin N') (Fin N) D.host.E), ∑ l, γ l • vecY D lam (z l) = Pi.single v 1 := by
  obtain ⟨τ, i, j⟩ := v
  obtain ⟨k, γ, x, h1, h2⟩ := exists_single D lam τ
  refine ⟨k, γ, fun l => Matrix.single i j (x l), ?_⟩
  funext ⟨τ', i', j'⟩
  obtain ⟨g, hg⟩ := exists_lamHom lam (TaylorLogMetric.embT D τ')
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, vecY]
  by_cases hij : i = i' ∧ j = j'
  · obtain ⟨rfl, rfl⟩ := hij
    simp only [Matrix.single_apply_same]
    by_cases hτ : τ' = τ
    · subst hτ
      rw [h1, Pi.single_eq_same]
    · rw [h2 τ' hτ, Pi.single_eq_of_ne (fun h => hτ (congrArg Prod.fst h))]
  · rw [Pi.single_eq_of_ne (fun h => hij (by simp only [Prod.mk.injEq] at h; exact ⟨h.2.1.symm, h.2.2.symm⟩))]
    simp only [TaylorLogMetric.tauEmb, hg]
    simp [Matrix.single_apply_of_ne _ _ _ _ _ hij]

theorem lam_hYY (y Y : Matrix (Fin N') (Fin N) D.host.E) :
    TaylorLogMetric.lamC lam (D.host.φ₀ ((TaylorLogMetric.hYY D y Y : D.host.K) : D.host.E)) =
      ∑ k : D.what₂.Tau × Fin N' × Fin N, vecY D lam y k * TaylorLogMetric.lamC lam (TaylorLogMetric.embT D k.1 (D.host.conj (Y k.2.1 k.2.2))) := by
  rw [TaylorLogMetric.hYY, ← GlobalTheory.InducedType.sum_eq_trace D, lamC_sum lam _ _ fun τ => emb_mem _ _, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun τ _ => ?_
  obtain ⟨g, hg⟩ := exists_lamHom lam (TaylorLogMetric.embT D τ)
  rw [hg]
  simp only [vecY, TaylorLogMetric.tauEmb, hg, map_sum, map_mul, Fintype.sum_prod_type]

theorem dirDer_sum {σ ι : Type} [Fintype σ] (s : Finset ι) (c : ι → ℂ_[p]) (w : ι → σ → ℂ_[p]) :
    dirDer (∑ l ∈ s, c l • w l) = ∑ l ∈ s, c l • dirDer (w l) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [dirDer_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, dirDer_add, dirDer_smul, ih]

theorem dirDer_single {σ : Type} [Fintype σ] [DecidableEq σ] (v : σ) (F : MvPowerSeries σ ℂ_[p]) :
    dirDer (Pi.single v 1) F = pderiv ℂ_[p] v F := by
  rw [dirDer_apply, Finset.sum_eq_single v]
  · simp
  · intro b _ hb
    simp [Pi.single_eq_of_ne hb]
  · simp

theorem jet_eq {n : ℕ} (y : Fin n → Matrix (Fin N') (Fin N) D.host.E)
    (F : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p]) :
    TaylorLogMetric.jet D lam y F = constantCoeff (derList D lam (List.ofFn y) F) := by
  rw [TaylorLogMetric.jet, foldr_der]

theorem jet_snoc {n : ℕ} (y : Fin n → Matrix (Fin N') (Fin N) D.host.E) (z : Matrix (Fin N') (Fin N) D.host.E)
    (F : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p]) :
    TaylorLogMetric.jet D lam (Fin.snoc y z : Fin (n + 1) → _) F =
      constantCoeff (derList D lam (List.ofFn y) (dirDer (vecY D lam z) F)) := by
  rw [jet_eq, List.ofFn_succ_last]
  simp [derList]

theorem exists_comb (n : ℕ) : ∀ α : TaylorLogMetric.Mono D N N', α.degree = n →
    ∃ (ι : Type) (_ : Fintype ι) (γ : ι → ℂ_[p]) (y : ι → Fin n → Matrix (Fin N') (Fin N) D.host.E),
    (∀ F : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p], jetAt F α = ∑ l, γ l * TaylorLogMetric.jet D lam (y l) F) ∧
    ∀ Y : Matrix (Fin N') (Fin N) D.host.E,
      (α.prod fun v n => TaylorLogMetric.lamC lam (TaylorLogMetric.embT D v.1 (D.host.conj (Y v.2.1 v.2.2))) ^ n) =
        ∑ l, γ l * ∏ j, TaylorLogMetric.lamC lam (D.host.φ₀ ((TaylorLogMetric.hYY D (y l j) Y : D.host.K) : D.host.E)) := by
  classical
  induction n with
  | zero =>
    intro α hn
    rw [(Finsupp.degree_eq_zero_iff α).1 hn]
    refine ⟨Unit, inferInstance, fun _ => 1, fun _ => Fin.elim0, fun F => ?_, fun Y => ?_⟩
    · simp [jetAt_zero, TaylorLogMetric.jet]
    · simp
  | succ n ih =>
    intro α hn
    have hα : α ≠ 0 := by rintro rfl; simp at hn
    obtain ⟨x, hx⟩ := Finsupp.support_nonempty_iff.2 hα
    have hle : Finsupp.single x 1 ≤ α := by
      rw [Finsupp.single_le_iff]
      exact Nat.one_le_iff_ne_zero.2 (Finsupp.mem_support_iff.1 hx)
    obtain ⟨β, rfl⟩ : ∃ β, α = β + Finsupp.single x 1 := ⟨α - Finsupp.single x 1, (tsub_add_cancel_of_le hle).symm⟩
    have hβ : β.degree = n := by
      rw [map_add, Finsupp.degree_single] at hn
      omega
    obtain ⟨ι, _, γ, y, h1, h2⟩ := ih β hβ
    obtain ⟨k, δ, z, hz⟩ := exists_vecY D lam x
    refine ⟨ι × Fin k, inferInstance, fun l => γ l.1 * δ l.2, fun l => Fin.snoc (y l.1) (z l.2), fun F => ?_, fun Y => ?_⟩
    · rw [jetAt_add_single, h1, Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [← dirDer_single, ← hz, dirDer_sum, jet_eq]
      simp only [jet_snoc, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, constantCoeff_smul,
        smul_eq_mul, Finset.mul_sum, mul_assoc]
    · rw [Finsupp.prod_add_index' (by simp) (fun _ _ _ => pow_add _ _ _), h2, Finsupp.prod_single_index (by simp),
        pow_one, Fintype.sum_prod_type, Finset.sum_mul]
      refine Finset.sum_congr rfl fun l _ => ?_
      have e : TaylorLogMetric.lamC lam (TaylorLogMetric.embT D x.1 (D.host.conj (Y x.2.1 x.2.2))) =
          ∑ m, δ m * TaylorLogMetric.lamC lam (D.host.φ₀ ((TaylorLogMetric.hYY D (z m) Y : D.host.K) : D.host.E)) := by
        simp only [lam_hYY, Finset.mul_sum]
        rw [Finset.sum_comm]
        simp only [← mul_assoc, ← Finset.sum_mul]
        have : ∀ v, ∑ m, δ m * vecY D lam (z m) v = (Pi.single x 1 : _ → ℂ_[p]) v := fun v => by
          rw [← hz, Finset.sum_apply]; rfl
        simp only [this]
        rw [Finset.sum_eq_single x]
        · simp
        · intro b _ hb
          simp [Pi.single_eq_of_ne hb]
        · simp
      rw [e, Finset.mul_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [Fin.prod_univ_castSucc]
      simp only [Fin.snoc_castSucc, Fin.snoc_last]
      ring

theorem monomial_eq_sum_jet : ∀ (D : D7) (p N N' : ℕ) [Fact p.Prime] (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) (α : TaylorLogMetric.Mono D N N'), ∃ (k : ℕ) (γ : Fin k → ℂ_[p]) (y : Fin k → Fin α.degree → Matrix (Fin N') (Fin N) D.host.E), (∀ F : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p], (α.prod fun _ n => (n.factorial : ℂ_[p])) * MvPowerSeries.coeff α F = ∑ l, γ l * TaylorLogMetric.jet D lam (y l) F) ∧ ∀ Y : Matrix (Fin N') (Fin N) D.host.E, (α.prod fun v n => TaylorLogMetric.lamC lam (TaylorLogMetric.embT D v.1 (D.host.conj (Y v.2.1 v.2.2))) ^ n) = ∑ l, γ l * ∏ j, TaylorLogMetric.lamC lam (D.host.φ₀ ((TaylorLogMetric.hYY D (y l j) Y : D.host.K) : D.host.E)) := by
  intro D p N N' _ lam α
  obtain ⟨ι, _, γ, y, h1, h2⟩ := exists_comb D lam _ α rfl
  let e := (Fintype.equivFin ι).symm
  refine ⟨_, γ ∘ e, y ∘ e, fun F => ?_, fun Y => ?_⟩
  · exact (h1 F).trans (e.sum_comp _).symm
  · exact (h2 Y).trans (e.sum_comp _).symm

end GlobalTheory.MonoJet
