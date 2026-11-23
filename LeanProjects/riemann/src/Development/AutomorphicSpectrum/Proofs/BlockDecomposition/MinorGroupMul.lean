import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.LocDefs
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GlobalSerreRelations.GlobSerreSt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RepUnique
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb GlobalTheory.CompanionTheory.ConeLocal
open GlobalTheory.CatH (face toLast)

namespace GlobalTheory.CompanionTheory.ConeLocal.JacAlg

def minorGroup {A B : Type} [CommRing A] [CommRing B] (ρ : A →+* B) {d m : ℕ}
    (D : Fin d → B → B) (κ : Fin m → Fin d) : AddSubgroup B :=
  AddSubgroup.closure {y | ∃ (b : A) (bs : Fin m → A),
    y = ρ b * (Matrix.of fun k l => D (κ k) (ρ (bs l))).det}

theorem minorGroup_mul {A B : Type} [CommRing A] [CommRing B] (ρ : A →+* B) {d m : ℕ}
    (D : Fin d → B → B) (κ : Fin m → Fin d) (a : A) {y : B}
    (hy : y ∈ minorGroup ρ D κ) : ρ a * y ∈ minorGroup ρ D κ := by
  unfold minorGroup at hy ⊢
  refine AddSubgroup.closure_induction (fun z hz => ?_) ?_
    (fun z₁ z₂ _ _ h₁ h₂ => ?_) (fun z _ hz => ?_) hy
  · obtain ⟨b, bs, rfl⟩ := hz
    exact AddSubgroup.subset_closure ⟨a * b, bs, by rw [map_mul, mul_assoc]⟩
  · rw [mul_zero]
    exact zero_mem _
  · rw [mul_add]
    exact add_mem h₁ h₂
  · rw [mul_neg]
    exact neg_mem hz

theorem leibniz_pow {R : Type} [CommRing R] (q : R → R)
    (hmul : ∀ x y, q (x * y) = x * q y + y * q x) (φ : R) (N : ℕ) :
    q (φ ^ N) = (N : R) * φ ^ (N - 1) * q φ := by
  induction N with
  | zero =>
    have h1 := hmul 1 1
    simp only [mul_one, one_mul] at h1
    simp only [pow_zero, Nat.cast_zero, zero_mul]
    linear_combination -h1
  | succ n ih =>
    rw [pow_succ, hmul, ih]
    rcases n with _ | n
    · simp
    · simp only [Nat.add_sub_cancel]
      push_cast
      ring

theorem column_clear {A B Af Bw : Type} [CommRing A] [CommRing B] [CommRing Af] [CommRing Bw]
    (ρ : A →+* B) (lam : B →+* Bw) (ι : A →+* Af) (μ : Af →+* Bw) (f : A)
    (hc : μ.comp ι = lam.comp ρ) {d : ℕ} (D : Fin d → B → B) (p : Fin d → Bw → Bw)
    (hmul : ∀ k x y, p k (x * y) = x * p k y + y * p k x)
    (hD : ∀ k x, p k (lam x) = lam (D k x))
    (a : Af) (b : A) (N : ℕ) (hb : ι f ^ N * a = ι b) (k : Fin d) :
    lam (ρ (f ^ N) * D k (ρ b) + ρ (-(N : A) * f ^ (N - 1) * b) * D k (ρ f))
      = (lam (ρ f)) ^ (2 * N) * p k (μ a) := by
  have e1 : ∀ x, μ (ι x) = lam (ρ x) := fun x => by
    simpa using RingHom.congr_fun hc x
  have hF : lam (ρ f) ^ N * μ a = lam (ρ b) := by
    have h1 := congrArg μ hb
    rwa [map_mul, map_pow, e1, e1] at h1
  have hp1 := hmul k (lam (ρ f) ^ N) (μ a)
  rw [hF, hD, leibniz_pow (p k) (hmul k) (lam (ρ f)) N, hD] at hp1
  simp only [map_add, map_mul, map_neg, map_pow, map_natCast]
  rw [hp1, ← hF]
  ring

theorem det_mem {A B : Type} [CommRing A] [CommRing B] (ρ : A →+* B) (f : A) {d m : ℕ}
    (D : Fin d → B → B) (κ : Fin m → Fin d) (c₁ c₂ b : Fin m → A) :
    (Matrix.of fun k l => ρ (c₁ l) * D (κ k) (ρ (b l))
      + ρ (c₂ l) * D (κ k) (ρ f)).det ∈ minorGroup ρ D κ := by
  classical
  unfold minorGroup
  set X : Fin m → Fin m → B := fun l k => ρ (c₁ l) * D (κ k) (ρ (b l)) with hX
  set Y : Fin m → Fin m → B := fun l k => ρ (c₂ l) * D (κ k) (ρ f) with hY
  have h1 : (Matrix.of fun k l => ρ (c₁ l) * D (κ k) (ρ (b l))
      + ρ (c₂ l) * D (κ k) (ρ f)).det = Matrix.det (Matrix.of fun l k => (X + Y) l k) := by
    rw [← Matrix.det_transpose]
    rfl
  have h2 : Matrix.det (Matrix.of fun l k => (X + Y) l k) =
      ∑ s : Finset (Fin m), Matrix.det (Matrix.of fun l k => s.piecewise X Y l k) :=
    (Matrix.detRowAlternating (n := Fin m) (R := B)).toMultilinearMap.map_add_univ X Y
  rw [h1, h2]
  refine AddSubgroup.sum_mem _ fun s _ => AddSubgroup.subset_closure ?_
  refine ⟨∏ l, (if l ∈ s then c₁ l else c₂ l), fun l => if l ∈ s then b l else f, ?_⟩
  rw [map_prod, ← Matrix.det_transpose (Matrix.of fun k l =>
      D (κ k) (ρ ((fun l => if l ∈ s then b l else f) l))),
    ← Matrix.det_mul_column]
  congr 1
  ext l k
  by_cases hl : l ∈ s <;> simp [hl, hX, hY, Finset.piecewise, Matrix.transpose_apply]

theorem det_clear {A B Af Bw : Type} [CommRing A] [CommRing B] [CommRing Af] [CommRing Bw]
    (ρ : A →+* B) (lam : B →+* Bw) (ι : A →+* Af) (μ : Af →+* Bw) (f : A)
    (hc : μ.comp ι = lam.comp ρ) (hloc : ∀ a : Af, ∃ (b : A) (N : ℕ), ι f ^ N * a = ι b)
    {d m : ℕ} (D : Fin d → B → B) (p : Fin d → Bw → Bw)
    (hmul : ∀ k x y, p k (x * y) = x * p k y + y * p k x)
    (hD : ∀ k x, p k (lam x) = lam (D k x))
    (κ : Fin m → Fin d) (u : Fin m → Af) :
    ∃ (M : ℕ) (n : B), n ∈ minorGroup ρ D κ ∧
      (lam (ρ f)) ^ M * (Matrix.of fun k l => p (κ k) (μ (u l))).det = lam n := by
  classical
  choose bb NN hbN using hloc
  obtain ⟨N, hN⟩ : ∃ N, ∀ l, NN (u l) ≤ N :=
    ⟨Finset.univ.sup fun l => NN (u l), fun l => Finset.le_sup (f := fun l => NN (u l))
      (Finset.mem_univ l)⟩
  let b : Fin m → A := fun l => f ^ (N - NN (u l)) * bb (u l)
  have hb : ∀ l, ι f ^ N * u l = ι (b l) := by
    intro l
    simp only [b, map_mul, map_pow]
    rw [← hbN (u l), ← mul_assoc, ← pow_add, Nat.sub_add_cancel (hN l)]
  have hcol : ∀ k l, lam (ρ (f ^ N) * D (κ k) (ρ (b l))
      + ρ (-(N : A) * f ^ (N - 1) * b l) * D (κ k) (ρ f))
      = lam (ρ f) ^ (2 * N) * p (κ k) (μ (u l)) :=
    fun k l => column_clear ρ lam ι μ f hc D p hmul hD (u l) (b l) N (hb l) (κ k)
  refine ⟨2 * N * m, (Matrix.of fun k l => ρ (f ^ N) * D (κ k) (ρ (b l))
      + ρ (-(N : A) * f ^ (N - 1) * b l) * D (κ k) (ρ f)).det,
    det_mem ρ f D κ (fun _ => f ^ N) (fun l => -(N : A) * f ^ (N - 1) * b l) b, ?_⟩
  rw [RingHom.map_det]
  have hmat : lam.mapMatrix (Matrix.of fun k l => ρ (f ^ N) * D (κ k) (ρ (b l))
      + ρ (-(N : A) * f ^ (N - 1) * b l) * D (κ k) (ρ f)) =
      Matrix.of fun k l => (fun _ => lam (ρ f) ^ (2 * N)) k * p (κ k) (μ (u l)) := by
    ext k l
    first
      | exact hcol k l
      | simpa using hcol k l
  rw [hmat, Matrix.det_mul_column, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    ← pow_mul]
  rfl

theorem clear_sum : ∀ {A B Af Bw : Type} [CommRing A] [CommRing B] [CommRing Af] [CommRing Bw] (ρ : A →+* B) (lam : B →+* Bw) (ι : A →+* Af) (μ : Af →+* Bw) (f : A),
    μ.comp ι = lam.comp ρ → (∀ a : Af, ∃ (b : A) (N : ℕ), ι f ^ N * a = ι b) → (∀ x : B, lam x = 0 → ∃ N : ℕ, ρ f ^ N * x = 0) →
    ∀ {d m : ℕ} {Λ : Type} [Fintype Λ] (D : Fin d → B → B) (p : Fin d → Bw → Bw), (∀ k x y, p k (x + y) = p k x + p k y) →
      (∀ k x y, p k (x * y) = x * p k y + y * p k x) → (∀ k x, p k (lam x) = lam (D k x)) →
      ∀ (κ : Fin m → Fin d) (z : Λ → Af) (u : Λ → Fin m → Af) (x : B),
        lam x = ∑ L, μ (z L) * (Matrix.of fun k l => p (κ k) (μ (u L l))).det →
        ∃ M : ℕ, ρ f ^ M * x ∈ AddSubgroup.closure {y | ∃ (b : A) (bs : Fin m → A), y = ρ b * (Matrix.of fun k l => D (κ k) (ρ (bs l))).det} := by
  intro A B Af Bw _ _ _ _ ρ lam ι μ f hc hloc hker d m Λ _ D p _ hmul hD κ z u x hx
  classical
  have e1 : ∀ a : A, μ (ι a) = lam (ρ a) := fun a => by
    simpa using RingHom.congr_fun hc a
  choose MM nn hnn hMM using fun L => det_clear ρ lam ι μ f hc hloc D p hmul hD κ (u L)
  choose bz Nz hz using fun L => hloc (z L)
  obtain ⟨K, hK⟩ : ∃ K, ∀ L, MM L + Nz L ≤ K :=
    ⟨Finset.univ.sup fun L => MM L + Nz L, fun L => Finset.le_sup (f := fun L => MM L + Nz L)
      (Finset.mem_univ L)⟩
  let e : Λ → A := fun L => f ^ (K - (MM L + Nz L)) * bz L
  have hterm : ∀ L, lam (ρ f) ^ K * (μ (z L) * (Matrix.of fun k l => p (κ k) (μ (u L l))).det)
      = lam (ρ (e L) * nn L) := by
    intro L
    have hzL : lam (ρ f) ^ Nz L * μ (z L) = lam (ρ (bz L)) := by
      have h1 := congrArg μ (hz L)
      rwa [map_mul, map_pow, e1, e1] at h1
    have hK' : K = (K - (MM L + Nz L)) + Nz L + MM L := by
      have h := Nat.sub_add_cancel (hK L)
      rw [add_assoc, add_comm (Nz L) (MM L), h]
    simp only [e, map_mul, map_pow, ← hzL, ← hMM L]
    conv_lhs => rw [hK', pow_add, pow_add]
    ring
  have hymem : (∑ L, ρ (e L) * nn L) ∈ minorGroup ρ D κ :=
    AddSubgroup.sum_mem _ fun L _ => minorGroup_mul ρ D κ (e L) (hnn L)
  have h0 : lam (ρ f ^ K * x - ∑ L, ρ (e L) * nn L) = 0 := by
    rw [map_sub, map_mul, map_pow, hx, Finset.mul_sum, map_sum]
    simp only [hterm]
    exact sub_self _
  obtain ⟨N', hN'⟩ := hker _ h0
  refine ⟨N' + K, ?_⟩
  have h2 : ρ f ^ (N' + K) * x = ρ (f ^ N') * ∑ L, ρ (e L) * nn L := by
    rw [pow_add, mul_assoc, ← sub_eq_zero, map_pow, ← mul_sub]
    exact hN'
  rw [h2]
  exact minorGroup_mul ρ D κ (f ^ N') hymem

end GlobalTheory.CompanionTheory.ConeLocal.JacAlg
