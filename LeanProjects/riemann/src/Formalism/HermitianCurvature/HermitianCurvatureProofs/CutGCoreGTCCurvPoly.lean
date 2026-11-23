import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTCCurvPolyCut

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.CurvPoly

noncomputable section

section PLT

variable {R : Type} [Ring R] [Algebra ℂ R]

def PLT (N : ℕ) (f : ℂ → R) : Prop := ∃ a : ℕ → R, ∀ s, f s = ∑ k ∈ Finset.range N, s ^ k • a k

theorem PLT.congr {N : ℕ} {f g : ℂ → R} (h : PLT N f) (e : ∀ s, g s = f s) : PLT N g := by
  obtain ⟨a, ha⟩ := h
  exact ⟨a, fun s => by rw [e, ha]⟩

theorem PLT.mono {N N' : ℕ} {f : ℂ → R} (h : PLT N f) (hN : N ≤ N') : PLT N' f := by
  obtain ⟨a, ha⟩ := h
  refine ⟨fun k => if k < N then a k else 0, fun s => ?_⟩
  rw [ha]
  symm
  rw [← Finset.sum_subset (Finset.range_mono hN)]
  · exact Finset.sum_congr rfl fun k hk => by dsimp only; rw [if_pos (Finset.mem_range.1 hk)]
  · intro k _ hk
    dsimp only
    rw [if_neg (fun h => hk (Finset.mem_range.2 h)), smul_zero]

theorem plt_zero (N : ℕ) : PLT N (fun _ => (0 : R)) := ⟨fun _ => 0, fun s => by simp⟩

theorem PLT.add {N : ℕ} {f g : ℂ → R} (hf : PLT N f) (hg : PLT N g) : PLT N (fun s => f s + g s) := by
  obtain ⟨a, ha⟩ := hf
  obtain ⟨b, hb⟩ := hg
  exact ⟨fun k => a k + b k, fun s => by dsimp only; rw [ha, hb, ← Finset.sum_add_distrib]; simp only [smul_add]⟩

theorem PLT.const_mul {N : ℕ} {f : ℂ → R} (x : R) (hf : PLT N f) : PLT N (fun s => x * f s) := by
  obtain ⟨a, ha⟩ := hf
  exact ⟨fun k => x * a k, fun s => by dsimp only; rw [ha, Finset.mul_sum]; simp only [mul_smul_comm]⟩

theorem PLT.mul_const {N : ℕ} {f : ℂ → R} (hf : PLT N f) (x : R) : PLT N (fun s => f s * x) := by
  obtain ⟨a, ha⟩ := hf
  exact ⟨fun k => a k * x, fun s => by dsimp only; rw [ha, Finset.sum_mul]; simp only [smul_mul_assoc]⟩

theorem PLT.mul {a b : ℕ} {f g : ℂ → R} (hf : PLT (a + 1) f) (hg : PLT (b + 1) g) :
    PLT (a + b + 1) (fun s => f s * g s) :=
  Formalism.FourierDecayAlt.P.MAx3.PG.polyIn_mul (f := f) (g := g) hf hg

theorem plt_monomial (n : ℕ) (x : R) : PLT (n + 1) (fun s => s ^ n • x) := by
  refine ⟨fun k => if k = n then x else 0, fun s => ?_⟩
  rw [Finset.sum_eq_single n]
  · simp
  · intro k _ hk; simp [hk]
  · intro h; exact absurd (Finset.mem_range.2 (Nat.lt_succ_self n)) h

theorem plt_const (x : R) : PLT 1 (fun _ => x) := (plt_monomial 0 x).congr fun s => by simp

theorem plt_sum {ι : Type} {N : ℕ} (t : Finset ι) {f : ι → ℂ → R} (h : ∀ i ∈ t, PLT N (f i)) :
    PLT N (fun s => ∑ i ∈ t, f i s) := by
  classical
  induction t using Finset.induction_on with
  | empty => exact (plt_zero N).congr fun s => by simp
  | insert j t hj ih =>
    refine ((h j (Finset.mem_insert_self _ _)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))).congr ?_
    intro s
    rw [Finset.sum_insert hj]

theorem plt_affine (x y : R) : PLT 2 (fun s => s • x + y) :=
  ((plt_monomial 1 x).add ((plt_const y).mono (by norm_num))).congr fun s => by simp

theorem polyIn_of_plt {f : ℂ → R} {d : ℕ} (h : PLT (d + 1) f) : MAx3.G.PolyIn f d := h

end PLT

theorem plt_kap {P : M.Par} {A : Type} [Ring A] [Algebra ℂ A] (κ : (M.Ty P → ℂ) →ₐ[ℂ] A) {N : ℕ}
    (g : M.Ty P → ℂ → ℂ) (h : ∀ ρ, PLT N (g ρ)) : PLT N (fun u => κ (fun ρ => g ρ u)) := by
  choose c hc using h
  refine ⟨fun i => κ (fun ρ => c ρ i), fun u => ?_⟩
  have e : (fun ρ => g ρ u) = ∑ i ∈ Finset.range N, u ^ i • (fun ρ => c ρ i) := by
    funext ρ
    rw [hc ρ u, Finset.sum_apply]
    rfl
  dsimp only
  rw [e, map_sum]
  simp only [map_smul]

theorem expand {A : Type} [Ring A] [Algebra ℂ A] (m : ℕ) (GG GGi K α β γ Wt1 Wt2 Θ : A)
    (x w ml X' W' : ℂ → A)
    (hx : ∀ u, x u = u ^ (m + 1) • (1 : A) + u ^ m • K + X' u) (hX' : PLT m X')
    (hw : ∀ u, w u = u ^ (m + 3) • Wt1 + u ^ (m + 2) • Wt2 + W' u) (hW' : PLT (m + 2) W')
    (hml : ∀ u, ml u = u ^ 2 • α + u • β + γ)
    (C1 : GG * α + GGi * Wt1 = 1) (C2 : GG * β + GG * K * α + GGi * Wt2 = Θ) :
    PLT (m + 2) (fun u => GGi * w u + GG * x u * ml u - u ^ (m + 3) • (1 : A) - u ^ (m + 2) • Θ) := by
  have key : ∀ u, GGi * w u + GG * x u * ml u - u ^ (m + 3) • (1 : A) - u ^ (m + 2) • Θ -
      (u ^ (m + 1) • (GG * γ + GG * K * β) + u ^ m • (GG * K * γ) + (GG * X' u * ml u + GGi * W' u)) =
      u ^ (m + 3) • (GG * α + GGi * Wt1 - 1) + u ^ (m + 2) • (GG * β + GG * K * α + GGi * Wt2 - Θ) := by
    intro u
    rw [hx, hw, hml u]
    simp only [mul_add, add_mul, smul_mul_assoc, mul_smul_comm, smul_add, mul_one, smul_smul, mul_assoc, smul_sub,
      mul_sub, sub_mul]
    module
  have hlow : PLT (m + 2) (fun u => u ^ (m + 1) • (GG * γ + GG * K * β) + u ^ m • (GG * K * γ) +
      (GG * X' u * ml u + GGi * W' u)) := by
    refine ((plt_monomial (m + 1) _).add ((plt_monomial m _).mono (by omega))).add ?_
    refine PLT.add ?_ (hW'.const_mul GGi)
    have hml' : PLT 3 ml := by
      refine (((plt_monomial 2 α).add ((plt_monomial 1 β).mono (by omega))).add ((plt_const γ).mono (by omega))).congr ?_
      intro s; rw [hml s]; simp
    cases m with
    | zero =>
      obtain ⟨a, ha⟩ := hX'
      exact (plt_zero 2).congr fun s => by simp [ha s]
    | succ n =>
      have := (hX'.const_mul GG).mul (b := 2) hml'
      exact (this.mono (by omega)).congr fun s => by simp only [mul_assoc]
  refine hlow.congr fun u => ?_
  have e := key u
  rw [C1, C2, sub_self, sub_self, smul_zero, smul_zero, add_zero, sub_eq_zero] at e
  exact e

section NF

variable {P : M.Par} {A : Type} [Ring A] [StarRing A] [Algebra ℂ A] (d : Q.NFData P A)

theorem lc {a b : A} (h : a * b = b * a) (c : A) : a * (b * c) = b * (a * c) := by
  rw [← mul_assoc, h, mul_assoc]

theorem fc {x y : A} (hx : x ∈ ({d.L.ζ, d.L.ζi, d.L.ζb, d.L.ζbi, d.L.GG, d.L.GGi} : Set A))
    (hy : y ∈ ({d.L.ζ, d.L.ζi, d.L.ζb, d.L.ζbi, d.L.GG, d.L.GGi} : Set A)) : x * y = y * x :=
  d.L.fns_comm x (Or.inr hx) y (Or.inr hy)

theorem ml_expand (u : ℂ) : d.L.m0 u * d.L.l0 u =
    u ^ 2 • (d.L.ζ * d.L.GGi * (d.L.ζb * d.L.GGi)) +
      u • (d.L.nabs * (d.L.ζb * d.L.GGi) + d.L.ζ * d.L.GGi * d.L.nab) +
      (d.L.nabs * d.L.nab + (1 / 2 : ℂ) • (d.L.nabs * (d.L.ζb * d.L.GGi)) - (1 / 2 : ℂ) • (d.L.ζ * d.L.GGi * d.L.nab) -
        (1 / 4 : ℂ) • (d.L.ζ * d.L.GGi * (d.L.ζb * d.L.GGi))) := by
  unfold R.LevelData.m0 R.LevelData.l0
  simp only [← Algebra.smul_def]
  simp only [neg_mul, mul_neg, sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, smul_smul, neg_neg, mul_assoc,
    smul_sub, smul_neg, neg_sub]
  module

theorem GG_alpha : d.L.GG * (d.L.ζ * d.L.GGi * (d.L.ζb * d.L.GGi)) =
    1 + algebraMap ℂ A d.L.TT * d.L.GGi := by
  have hz : d.L.ζ * d.L.ζb = d.L.GG + algebraMap ℂ A d.L.TT := by rw [d.L.GG_def]; abel
  have h1 : d.L.GG * d.L.ζ = d.L.ζ * d.L.GG := fc d (by simp) (by simp)
  have h2 : d.L.GGi * d.L.ζb = d.L.ζb * d.L.GGi := fc d (by simp) (by simp)
  calc d.L.GG * (d.L.ζ * d.L.GGi * (d.L.ζb * d.L.GGi))
      = d.L.ζ * ((d.L.GG * d.L.GGi) * (d.L.ζb * d.L.GGi)) := by
        simp only [mul_assoc]; rw [lc h1]
    _ = d.L.ζ * d.L.ζb * d.L.GGi := by rw [d.L.GG_GGi, one_mul, mul_assoc]
    _ = 1 + algebraMap ℂ A d.L.TT * d.L.GGi := by rw [hz, add_mul, d.L.GG_GGi]

theorem C1 : d.L.GG * (d.L.ζ * d.L.GGi * (d.L.ζb * d.L.GGi)) + d.L.GGi * algebraMap ℂ A (-d.L.TT) = 1 := by
  rw [GG_alpha, ← Algebra.commutes, map_neg, neg_mul]
  abel

theorem GG_nabs : d.L.GG * (d.L.nabs * (d.L.ζb * d.L.GGi)) =
    d.L.ζb * d.L.nabs + algebraMap ℂ A d.L.TT * d.L.GGi := by
  have hz : d.L.ζb * d.L.ζ = d.L.GG + algebraMap ℂ A d.L.TT := by
    rw [← fc d (x := d.L.ζ) (by simp) (by simp), d.L.GG_def]; abel
  have h1 : d.L.GG * d.L.ζb = d.L.ζb * d.L.GG := fc d (by simp) (by simp)
  have e : d.L.nabs * (d.L.ζb * d.L.GGi) = d.L.ζb * (d.L.GGi * d.L.nabs) + d.L.ζb * (d.L.ζ * d.L.GGi * d.L.GGi) -
      d.L.GGi := by
    rw [← mul_assoc, d.L.nabs_ζb, sub_mul, one_mul, mul_assoc, d.L.nabs_GGi, mul_add]
  rw [e, mul_sub, mul_add, lc h1, lc h1, ← mul_assoc d.L.GG d.L.GGi, d.L.GG_GGi, one_mul]
  have e2 : d.L.GG * (d.L.ζ * d.L.GGi * d.L.GGi) = d.L.ζ * d.L.GGi := by
    have h3 : d.L.GG * d.L.ζ = d.L.ζ * d.L.GG := fc d (by simp) (by simp)
    simp only [mul_assoc]; rw [lc h3, ← mul_assoc d.L.GG, d.L.GG_GGi, one_mul]
  rw [e2, ← mul_assoc, hz, add_mul, d.L.GG_GGi]
  abel

end NF

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.CurvPoly

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.CurvPoly

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

noncomputable section

section NormalFormTwo

variable {P : M.Par} {A : Type} [Ring A] [StarRing A] [Algebra ℂ A] (d : Q.NFData P A)

theorem GG_zGinab : d.L.GG * (d.L.ζ * d.L.GGi * d.L.nab) = d.L.ζ * d.L.nab := by
  have h1 : d.L.GG * d.L.ζ = d.L.ζ * d.L.GG := fc d (by simp) (by simp)
  simp only [mul_assoc]
  rw [lc h1, ← mul_assoc d.L.GG d.L.GGi, d.L.GG_GGi, one_mul]

theorem kappa_of_weight_function : d.κ (fun ρ => (P.TT : ℂ) * (((absTy P ρ : ℝ) : ℂ) - 1 - sumU P)) =
    (P.TT : ℂ) • (d.κ (fun ρ => ((absTy P ρ : ℝ) : ℂ)) - 1 - algebraMap ℂ A (sumU P)) := by
  rw [show (fun ρ => (P.TT : ℂ) * (((absTy P ρ : ℝ) : ℂ) - 1 - sumU P)) = (P.TT : ℂ) •
      ((fun ρ => ((absTy P ρ : ℝ) : ℂ)) - 1 - algebraMap ℂ (M.Ty P → ℂ) (sumU P)) from funext fun ρ => by simp]
  rw [map_smul, map_sub, map_sub, map_one, AlgHom.commutes]

theorem kap_aC : d.κ (fun ρ => ((-2 * M.aC P ρ : ℝ) : ℂ)) =
    (2 : ℂ) • d.κ (fun ρ => ((absTy P ρ : ℝ) : ℂ)) - algebraMap ℂ A (sumU P) := by
  rw [show (fun ρ => ((-2 * M.aC P ρ : ℝ) : ℂ)) = (2 : ℂ) • (fun ρ => ((absTy P ρ : ℝ) : ℂ)) -
      algebraMap ℂ (M.Ty P → ℂ) (sumU P) from funext fun ρ => by
        simp only [M.aC, absTy, sumU, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.algebraMap_apply,
          Algebra.algebraMap_self, RingHom.id_apply]
        push_cast
        ring]
  rw [map_sub, map_smul, AlgHom.commutes]

theorem C2 (hRel : d.Rel) (hTT : d.L.TT = (P.TT : ℂ)) :
    d.L.GG * (d.L.nabs * (d.L.ζb * d.L.GGi) + d.L.ζ * d.L.GGi * d.L.nab) +
      d.L.GG * d.κ (fun ρ => ((absTy P ρ : ℝ) : ℂ)) * (d.L.ζ * d.L.GGi * (d.L.ζb * d.L.GGi)) +
      d.L.GGi * d.κ (fun ρ => (P.TT : ℂ) * (((absTy P ρ : ℝ) : ℂ) - 1 - sumU P)) = ThetaC d := by
  have hKG : d.L.GG * d.κ (fun ρ => ((absTy P ρ : ℝ) : ℂ)) = d.κ (fun ρ => ((absTy P ρ : ℝ) : ℂ)) * d.L.GG :=
    (hRel.2.1 _ d.L.GG (Or.inl (by simp [R.LevelData.fns]))).eq.symm
  have hKGi : d.κ (fun ρ => ((absTy P ρ : ℝ) : ℂ)) * d.L.GGi = d.L.GGi * d.κ (fun ρ => ((absTy P ρ : ℝ) : ℂ)) :=
    (hRel.2.1 _ d.L.GGi (Or.inl (by simp [R.LevelData.fns]))).eq
  unfold ThetaC
  rw [kappa_of_weight_function, kap_aC, mul_add, GG_nabs, GG_zGinab, hKG, mul_assoc (d.κ _) d.L.GG, GG_alpha, hTT]
  simp only [Algebra.algebraMap_eq_smul_one, mul_add, add_mul, mul_sub, sub_mul, smul_mul_assoc, mul_smul_comm,
    one_mul, mul_one, smul_sub, smul_add, smul_smul, hKGi, mul_assoc]
  module

end NormalFormTwo

theorem curvature_polynomial_of_scalar : GTCCurvPolyOfScal := by
  intro hS P A _ _ _ d hRel hk hTT
  obtain ⟨m, hm⟩ : ∃ m, P.k = m + 2 := ⟨P.k - 2, by omega⟩
  have hsc := hS P hk
  choose cw hcw using fun ρ => (hsc ρ).1
  choose cx hcx using fun ρ => (hsc ρ).2.1
  have hex := fun ρ => (hsc ρ).2.2
  have scalPLT : ∀ {N : ℕ} {g : ℂ → ℂ} (c : ℕ → ℂ), (∀ u, g u = ∑ i ∈ Finset.range N, u ^ i * c i) → PLT N g :=
    fun c h => ⟨c, fun u => by rw [h u]; simp only [smul_eq_mul]⟩
  have hxEx : ∀ ex : Finset ℕ, (∃ l ∈ ex, l ∈ Finset.Icc 1 (P.k - 1)) →
      PLT (m + 1) (fun u => d.κ (fun ρ => M.xEx P ex ρ u)) := by
    intro ex hex'
    refine plt_kap d.κ (fun ρ u => M.xEx P ex ρ u) fun ρ => ?_
    obtain ⟨c, hc⟩ := hex ρ ex hex'
    exact scalPLT c (fun u => by rw [hc u, show P.k - 1 = m + 1 by omega])
  have hS21 : PLT (m + 1) (fun u => d.weightedSumBis u) := by
    unfold Q.NFData.weightedSumBis
    exact plt_sum _ fun l hl => (hxEx {l} ⟨l, Finset.mem_singleton_self l, hl⟩).const_mul (d.SS l)
  have hS12 : PLT (m + 1) (fun u => d.S12 u) := by
    unfold Q.NFData.S12
    exact plt_sum _ fun l hl => (hxEx {l} ⟨l, Finset.mem_singleton_self l, hl⟩).mul_const (star (d.SS l))
  have hS4 : PLT (m + 1) (fun u => d.S4 u) := by
    unfold Q.NFData.S4
    exact plt_sum _ fun l hl => plt_sum _ fun j _ =>
      (hxEx {l, j} ⟨l, Finset.mem_insert_self l _, hl⟩).const_mul (star (d.SS l) * d.SS j)
  have hm0 : PLT 2 (fun u => d.L.m0 u) :=
    (plt_affine (-(d.L.ζ * d.L.GGi)) (-d.L.nabs + (1 / 2 : ℂ) • (d.L.ζ * d.L.GGi))).congr fun u => by
      unfold R.LevelData.m0
      simp only [← Algebra.smul_def]
      module
  have hl0 : PLT 2 (fun u => d.L.l0 u) :=
    (plt_affine (-(d.L.ζb * d.L.GGi)) (-d.L.nab - (1 / 2 : ℂ) • (d.L.ζb * d.L.GGi))).congr fun u => by
      unfold R.LevelData.l0
      simp only [← Algebra.smul_def]
      module
  set K := d.κ (fun ρ => ((absTy P ρ : ℝ) : ℂ)) with hK
  set X' : ℂ → A := fun u => d.κ (fun ρ => ∑ i ∈ Finset.range m, u ^ i * cx ρ i) with hX'def
  have hx : ∀ u, d.x u = u ^ (m + 1) • (1 : A) + u ^ m • K + X' u := by
    intro u
    unfold Q.NFData.x
    rw [show (fun ρ => M.xC P ρ u) = u ^ (m + 1) • (1 : M.Ty P → ℂ) + u ^ m • (fun ρ => ((absTy P ρ : ℝ) : ℂ)) +
        (fun ρ => ∑ i ∈ Finset.range m, u ^ i * cx ρ i) from funext fun ρ => by
          rw [hcx ρ u, show P.k - 1 = m + 1 by omega, show P.k - 2 = m by omega]
          simp only [Pi.add_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one]
          ring]
    rw [map_add, map_add, map_smul, map_smul, map_one]
  have hX' : PLT m X' := plt_kap d.κ _ (fun ρ => scalPLT (cx ρ) (fun u => rfl))
  have hxP : PLT (m + 2) (fun u => d.x u) :=
    (((plt_monomial (m + 1) (1 : A)).add ((plt_monomial m K).mono (by omega))).add (hX'.mono (by omega))).congr
      fun u => hx u
  set W' : ℂ → A := fun u => d.κ (fun ρ => ∑ i ∈ Finset.range P.k, u ^ i * cw ρ i) with hW'def
  have hw : ∀ u, d.κ (fun ρ => M.wC P ρ u) = u ^ (m + 3) • algebraMap ℂ A (-(P.TT : ℂ)) +
      u ^ (m + 2) • d.κ (fun ρ => (P.TT : ℂ) * (((absTy P ρ : ℝ) : ℂ) - 1 - sumU P)) + W' u := by
    intro u
    rw [show (fun ρ => M.wC P ρ u) = u ^ (m + 3) • algebraMap ℂ (M.Ty P → ℂ) (-(P.TT : ℂ)) +
        u ^ (m + 2) • (fun ρ => (P.TT : ℂ) * (((absTy P ρ : ℝ) : ℂ) - 1 - sumU P)) +
        (fun ρ => ∑ i ∈ Finset.range P.k, u ^ i * cw ρ i) from funext fun ρ => by
          rw [hcw ρ u, hm]
          simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.algebraMap_apply, Algebra.algebraMap_self,
            RingHom.id_apply]]
    rw [map_add, map_add, map_smul, map_smul, AlgHom.commutes]
  have hW' : PLT (m + 2) W' := plt_kap d.κ _ (fun ρ => scalPLT (cw ρ) (fun u => by rw [hm]))
  have hC1 : d.L.GG * (d.L.ζ * d.L.GGi * (d.L.ζb * d.L.GGi)) + d.L.GGi * algebraMap ℂ A (-(P.TT : ℂ)) = 1 := by
    have := C1 d; rwa [hTT] at this
  have hmain := expand m d.L.GG d.L.GGi K _ _ _ _ _ (ThetaC d) (fun u => d.x u)
    (fun u => d.κ (fun ρ => M.wC P ρ u)) (fun u => d.L.m0 u * d.L.l0 u) X' W' hx hX' hw hW' (ml_expand d) hC1
    (C2 d hRel hTT)
  have hlow : PLT (m + 2) (fun u => d.L.GG * d.L.m0 u * d.L.GGi * d.weightedSumBis u + d.S12 u * d.L.l0 u +
      d.L.GGi * d.S4 u) := by
    have t1 := ((hm0.const_mul d.L.GG).mul (a := 1) (b := m) (hS21.const_mul d.L.GGi)).mono (show 1 + m + 1 ≤ m + 2 by omega)
    have t2 := (hS12.mul (a := m) (b := 1) hl0)
    have t3 := (hS4.const_mul d.L.GGi).mono (show m + 1 ≤ m + 2 by omega)
    exact ((t1.add t2).add t3).congr fun u => by simp only [mul_assoc]
  constructor
  · rw [show P.k - 1 = m + 1 by omega]
    apply polyIn_of_plt
    refine (hmain.add hlow).congr fun u => ?_
    have hQ : d.QQ u 0 0 = d.L.GGi * (d.κ fun ρ => M.wC P ρ u) + d.L.GG * d.x u * d.L.m0 u * d.L.l0 u +
        d.L.GG * d.L.m0 u * d.L.GGi * d.weightedSumBis u + d.S12 u * d.L.l0 u + d.L.GGi * d.S4 u := by
      simp [Q.NFData.QQ]
    rw [hQ, hm]
    simp only [mul_assoc]
    abel
  · rw [hm]
    apply polyIn_of_plt
    have t := ((hxP.const_mul d.L.GG).mul (a := m + 1) (b := 1) hl0).add (hS21.mono (show m + 1 ≤ m + 1 + 1 + 1 by omega))
    refine t.congr fun u => ?_
    simp [Q.NFData.QQ]

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.CurvPoly

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

theorem curvature_polynomial_of_scalar : GTCCurvPolyOfScal := CurvPoly.curvature_polynomial_of_scalar

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
