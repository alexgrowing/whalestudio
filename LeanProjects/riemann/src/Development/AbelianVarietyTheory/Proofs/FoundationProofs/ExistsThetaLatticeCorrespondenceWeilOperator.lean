import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HESmulRight
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.WeilOperatorConjHeisenbergMovedLattice
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsRationalPointOfMemMovedThetaLattice
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmThetaLatticePointMemThetaLatticeOfAdelic
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InducedTypeThetaGenusOnePermutes
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.InertSign
open scoped BigOperators

namespace GlobalTheory.WeilCorr

open GlobalTheory.NormSum.MovedTheta

theorem exists_close_two {R E : Type} [CommRing R] (ι : E → R) (O : Subring R) (I : AddSubgroup R)
    (hA : ∀ (y : R) (m : ℕ), 0 < m → ∃ e : E, ∃ t ∈ I, ι e - y = (m : R) * t)
    (hO : ∀ y : R, ∃ n : ℕ, 0 < n ∧ (n : R) * y ∈ O) (hI : ∀ s ∈ O, ∀ t ∈ I, s * t ∈ I)
    {a b : ℕ} (X : Matrix (Fin a) (Fin b) R) (P P' : Matrix (Fin a) (Fin a) R) (Q Q' : Matrix (Fin b) (Fin b) R)
    (m : ℕ) (hm : 0 < m) :
    ∃ z : Matrix (Fin a) (Fin b) E, (∀ i j, ∃ y ∈ I, (z.map ι - X) i j = (m : R) * y) ∧
      (∀ i j, (P * z.map ι * Q - P * X * Q) i j ∈ I) ∧ ∀ i j, (P' * z.map ι * Q' - P' * X * Q') i j ∈ I := by
  obtain ⟨n₁, hn₁, hP⟩ := GlobalTheory.WeilEquiv.exists_common_den O hO P
  obtain ⟨n₂, hn₂, hQ⟩ := GlobalTheory.WeilEquiv.exists_common_den O hO Q
  obtain ⟨n₃, hn₃, hP'⟩ := GlobalTheory.WeilEquiv.exists_common_den O hO P'
  obtain ⟨n₄, hn₄, hQ'⟩ := GlobalTheory.WeilEquiv.exists_common_den O hO Q'
  choose e t ht he using fun i j => hA (X i j) (m * n₁ * n₂ * n₃ * n₄) (by positivity)
  have key : ∀ (P : Matrix (Fin a) (Fin a) R) (Q : Matrix (Fin b) (Fin b) R) (n n' c : ℕ),
      (∀ i j, (n : R) * P i j ∈ O) → (∀ i j, (n' : R) * Q i j ∈ O) → m * n₁ * n₂ * n₃ * n₄ = c * n * n' →
      ∀ i j, (P * (Matrix.of e).map ι * Q - P * X * Q) i j ∈ I := by
    intro P Q n n' c hP hQ hc i j
    rw [← Matrix.sub_mul, ← Matrix.mul_sub]
    simp only [Matrix.mul_apply, Matrix.sub_apply, Matrix.map_apply, Matrix.of_apply, Finset.sum_mul, he, hc]
    refine sum_mem fun l _ => sum_mem fun r _ => ?_
    have : P i r * (((c * n * n' : ℕ) : R) * t r l) * Q l j =
        ((c : R) * ((n : R) * P i r) * ((n' : R) * Q l j)) * t r l := by
      push_cast; ring
    rw [this]
    exact hI _ (O.mul_mem (O.mul_mem (natCast_mem O _) (hP i r)) (hQ l j)) _ (ht r l)
  refine ⟨Matrix.of e, fun i j => ⟨((n₁ * n₂ * n₃ * n₄ : ℕ) : R) * t i j, hI _ (natCast_mem O _) _ (ht i j), ?_⟩,
    key P Q n₁ n₂ (m * n₃ * n₄) hP hQ (by ring), key P' Q' n₃ n₄ (m * n₁ * n₂) hP' hQ' (by ring)⟩
  simp only [Matrix.sub_apply, Matrix.map_apply, Matrix.of_apply, he]
  push_cast; ring

section Entries

variable {R : Type} [CommRing R] {I : AddSubgroup R} {a b : ℕ} {A B A' B' : Matrix (Fin a) (Fin b) R}

theorem entries_of_sub (h : ∀ i j, (A - B) i j ∈ I) (h' : ∀ i j, B i j ∈ I) (i : Fin a) (j : Fin b) : A i j ∈ I := by
  have := add_mem (h i j) (h' i j)
  rwa [Matrix.sub_apply, sub_add_cancel] at this

theorem entries_trans (h : ∀ i j, (A - B) i j ∈ I) (h' : ∀ i j, (B - A') i j ∈ I) (i : Fin a) (j : Fin b) :
    (A - A') i j ∈ I := by
  have := add_mem (h i j) (h' i j)
  rwa [Matrix.sub_apply, Matrix.sub_apply, sub_add_sub_cancel] at this

theorem entries_iff (h : ∀ i j, (A - B) i j ∈ I) (h' : ∀ i j, (A' - B') i j ∈ I) :
    (∀ i j, (B - B') i j ∈ I) ↔ ∀ i j, (A - A') i j ∈ I := by
  refine forall₂_congr fun i j => ?_
  have h1 := sub_mem (h i j) (h' i j)
  simp only [Matrix.sub_apply] at h1 ⊢
  constructor
  · intro h2
    convert add_mem h1 h2 using 1
    ring
  · intro h2
    convert sub_mem h2 h1 using 1
    ring

end Entries

variable {D : D7} {N N' : ℕ}

theorem pt_injective (cc : Ideal (𝓞 D.host.K)) {δ : ℂ} (hδ : δ ≠ 0) :
    Function.Injective (pt D (tor0 D cc δ) δ : Matrix (Fin N') (Fin N) D.host.E → VC D N N') := by
  intro z w h
  refine Matrix.ext fun i j => ?_
  have h1 := congrFun (congrFun (congrFun h (D.eTau.symm 1)) i) j
  simp only [pt, embV, tor0, Pi.smul_apply, smul_eq_mul] at h1
  exact (embT D _).injective (mul_left_cancel₀ hδ h1)

theorem pt_sub (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (z w : Matrix (Fin N') (Fin N) D.host.E) :
    pt D (tor0 D cc δ) δ (z - w) = pt D (tor0 D cc δ) δ z - pt D (tor0 D cc δ) δ w := by
  rw [sub_eq_add_neg, pt_add, pt_neg, ← sub_eq_add_neg]

theorem mv_sub (g : GL (Fin N) (AE D)) (g' : GL (Fin N') (AE D)) (z w : Matrix (Fin N') (Fin N) D.host.E) :
    mv g g' (z - w) = mv g g' z - mv g g' w := by
  rw [sub_eq_add_neg, mv_add, mv_neg, ← sub_eq_add_neg]

theorem pt_mem_iff {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (hcc : cc ≠ ⊥) (hδ : δ ≠ 0) {h : GA D N} {h' : GA D N'}
    {L : Lat D N} {L' : Lat D N'} (hL : Moves D (h : GL (Fin N) (AE D)) L) (hL' : Moves D (h' : GL (Fin N') (AE D)) L')
    (u : Matrix (Fin N') (Fin N) D.host.E) :
    pt D (tor0 D cc δ) δ u ∈ La D (tor0 D cc δ) L L' ↔
      ∀ i j, mv (h : GL (Fin N) (AE D)) (h' : GL (Fin N') (AE D)) u i j ∈ IhE D cc := by
  have hD := (GlobalTheory.InducedType.induced_type D).1
  constructor
  · intro hu
    obtain ⟨z, hz, hz'⟩ := GlobalTheory.NormSum.exists_pt_of_mem_La_moved D hD cc δ hcc N N' h h' L L' hL hL' _ hu
    rw [pt_injective cc hδ hz]
    exact hz'
  · exact GlobalTheory.NormSum.pt_mem_La_of_adelic D hD cc δ hcc N N' h h' L L' hL hL' u

theorem move_fwd (g h : GL (Fin N) (AE D)) (g' h' : GL (Fin N') (AE D)) (z : Matrix (Fin N') (Fin N) D.host.E) :
    (((g' * h')⁻¹ : GL (Fin N') (AE D)) : Matrix (Fin N') (Fin N') (AE D)) *
      ((g' : Matrix (Fin N') (Fin N') (AE D)) * z.map (inc D) *
        ((g⁻¹ : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D))) *
      ((g * h : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) = mv h h' z := by
  simp only [mv, mul_inv_rev, Units.val_mul, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc ((g'⁻¹ : GL (Fin N') (AE D)) : Matrix (Fin N') (Fin N') (AE D)),
    ← Matrix.mul_assoc ((g⁻¹ : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)),
    Units.inv_mul, Units.inv_mul, Matrix.one_mul, Matrix.one_mul]

theorem move_bwd (g h : GL (Fin N) (AE D)) (g' h' : GL (Fin N') (AE D)) (z : Matrix (Fin N') (Fin N) D.host.E) :
    ((h'⁻¹ : GL (Fin N') (AE D)) : Matrix (Fin N') (Fin N') (AE D)) * mv g g' z *
      (h : Matrix (Fin N) (Fin N) (AE D)) = mv (g * h) (g' * h') z := by
  simp only [mv, mul_inv_rev, Units.val_mul, Matrix.mul_assoc]

theorem approx_fwd {cc : Ideal (𝓞 D.host.K)} (hcc : cc ≠ ⊥) (g h k : GL (Fin N) (AE D)) (g' h' k' : GL (Fin N') (AE D))
    (z : Matrix (Fin N') (Fin N) D.host.E) (m : ℕ) (hm : 0 < m) :
    ∃ z' : Matrix (Fin N') (Fin N) D.host.E, CloseTo D cc m g g' z z' ∧
      (∀ i j, (mv (g * h) (g' * h') z' - mv h h' z) i j ∈ IhE D cc) ∧
      ∀ i j, (mv (g * k) (g' * k') z' - mv k k' z) i j ∈ IhE D cc := by
  obtain ⟨hA, hO, hI⟩ := GlobalTheory.AdelicApprox.approx_mod_ideal D cc hcc
  rw [← move_fwd g h g' h' z, ← move_fwd g k g' k' z]
  exact exists_close_two (inc D) (OhE D) (IhE D cc) hA hO hI _ _ _ _ _ m hm

theorem approx_bwd {cc : Ideal (𝓞 D.host.K)} (hcc : cc ≠ ⊥) (g h k : GL (Fin N) (AE D)) (g' h' k' : GL (Fin N') (AE D))
    (y : Matrix (Fin N') (Fin N) D.host.E) :
    ∃ z : Matrix (Fin N') (Fin N) D.host.E,
      (∀ i j, (mv h h' z - mv (g * h) (g' * h') y) i j ∈ IhE D cc) ∧
      ∀ i j, (mv k k' z - mv (g * k) (g' * k') y) i j ∈ IhE D cc := by
  obtain ⟨hA, hO, hI⟩ := GlobalTheory.AdelicApprox.approx_mod_ideal D cc hcc
  rw [← move_bwd g h g' h' y, ← move_bwd g k g' k' y]
  obtain ⟨z, -, hz⟩ := exists_close_two (inc D) (OhE D) (IhE D cc) hA hO hI (mv g g' y)
    ((h'⁻¹ : GL (Fin N') (AE D)) : Matrix (Fin N') (Fin N') (AE D))
    ((k'⁻¹ : GL (Fin N') (AE D)) : Matrix (Fin N') (Fin N') (AE D))
    (h : Matrix (Fin N) (Fin N) (AE D)) (k : Matrix (Fin N) (Fin N) (AE D)) 1 one_pos
  exact ⟨z, hz⟩

theorem exists_corr : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → δ ≠ 0 → ∀ (N N' : ℕ) (e0 : VC D N N' → ℂ) (W : WeilO D cc δ N N' e0) (g h k : GA D N) (g' h' k' : GA D N') (L₁ L₂ M₁ M₂ : Lat D N) (L₁' L₂' M₁' M₂' : Lat D N'), Moves D (h : GL (Fin N) (AE D)) L₁ → Moves D (h' : GL (Fin N') (AE D)) L₁' → Moves D ((g * h : GA D N) : GL (Fin N) (AE D)) L₂ → Moves D ((g' * h' : GA D N') : GL (Fin N') (AE D)) L₂' → Moves D (k : GL (Fin N) (AE D)) M₁ → Moves D (k' : GL (Fin N') (AE D)) M₁' → Moves D ((g * k : GA D N) : GL (Fin N) (AE D)) M₂ → Moves D ((g' * k' : GA D N') : GL (Fin N') (AE D)) M₂' → ∀ F ∈ TT D (tor0 D cc δ) N N', ∃ f : La D (tor0 D cc δ) M₁ M₁' → La D (tor0 D cc δ) M₂ M₂', (∀ x : La D (tor0 D cc δ) M₁ M₁', W.Om g g' (Wd D (tor0 D cc δ) (x : VC D N N') F) = Wd D (tor0 D cc δ) (f x : VC D N N') (W.Om g g' F)) ∧ (∀ x y : La D (tor0 D cc δ) M₁ M₁', (x : VC D N N') - (y : VC D N N') ∈ La D (tor0 D cc δ) L₁ L₁' ↔ (f x : VC D N N') - (f y : VC D N N') ∈ La D (tor0 D cc δ) L₂ L₂') ∧ ∀ y : La D (tor0 D cc δ) M₂ M₂', ∃ x : La D (tor0 D cc δ) M₁ M₁', (f x : VC D N N') - (y : VC D N N') ∈ La D (tor0 D cc δ) L₂ L₂' := by
  intro D cc δ hC hδ N N' e0 W g h k g' h' k' L₁ L₂ M₁ M₂ L₁' L₂' M₁' M₂' a1 a1' a2 a2' b1 b1' b2 b2' F hF
  have hcc : cc ≠ ⊥ := hC.1.1
  have hD := (GlobalTheory.InducedType.induced_type D).1
  have step : ∀ z : Matrix (Fin N') (Fin N) D.host.E, ∃ z' : Matrix (Fin N') (Fin N) D.host.E,
      W.Om g g' (Wd D (tor0 D cc δ) (pt D (tor0 D cc δ) δ z) F) =
        Wd D (tor0 D cc δ) (pt D (tor0 D cc δ) δ z') (W.Om g g' F) ∧
      (∀ i j, (mv ((g * h : GA D N) : GL (Fin N) (AE D)) ((g' * h' : GA D N') : GL (Fin N') (AE D)) z' -
        mv (h : GL (Fin N) (AE D)) (h' : GL (Fin N') (AE D)) z) i j ∈ IhE D cc) ∧
      ∀ i j, (mv ((g * k : GA D N) : GL (Fin N) (AE D)) ((g' * k' : GA D N') : GL (Fin N') (AE D)) z' -
        mv (k : GL (Fin N) (AE D)) (k' : GL (Fin N') (AE D)) z) i j ∈ IhE D cc := by
    intro z
    obtain ⟨m, hm, hl⟩ := W.lift g g' z F hF
    obtain ⟨z', hc, h1, h2⟩ := approx_fwd hcc (g : GL (Fin N) (AE D)) h k (g' : GL (Fin N') (AE D)) h' k' z m hm
    exact ⟨z', hl z' hc, h1, h2⟩
  choose s hs1 hs2 hs3 using step
  choose r hr1 hr2 using fun x : La D (tor0 D cc δ) M₁ M₁' =>
    GlobalTheory.NormSum.exists_pt_of_mem_La_moved D hD cc δ hcc N N' k k' M₁ M₁' b1 b1' x x.2
  have hmem : ∀ x, pt D (tor0 D cc δ) δ (s (r x)) ∈ La D (tor0 D cc δ) M₂ M₂' := by
    intro x
    rw [pt_mem_iff hcc hδ b2 b2']
    exact entries_of_sub (hs3 (r x)) (hr2 x)
  refine ⟨fun x => ⟨_, hmem x⟩, fun x => ?_, fun x y => ?_, fun y => ?_⟩
  · have := hs1 (r x)
    rwa [← hr1 x] at this
  · rw [hr1 x, hr1 y]
    dsimp only
    rw [← pt_sub, ← pt_sub, pt_mem_iff hcc hδ a1 a1', pt_mem_iff hcc hδ a2 a2', mv_sub, mv_sub]
    exact entries_iff (hs2 (r x)) (hs2 (r y))
  · obtain ⟨y₀, hy, hy'⟩ := GlobalTheory.NormSum.exists_pt_of_mem_La_moved D hD cc δ hcc N N' _ _ M₂ M₂' b2 b2' y y.2
    obtain ⟨z, h1, h2⟩ := approx_bwd hcc (g : GL (Fin N) (AE D)) h k (g' : GL (Fin N') (AE D)) h' k' y₀
    have hz : pt D (tor0 D cc δ) δ z ∈ La D (tor0 D cc δ) M₁ M₁' := by
      rw [pt_mem_iff hcc hδ b1 b1']
      exact entries_of_sub h2 hy'
    refine ⟨⟨_, hz⟩, ?_⟩
    have e : r ⟨_, hz⟩ = z := (pt_injective cc hδ (hr1 ⟨_, hz⟩)).symm
    dsimp only
    rw [e, hy, ← pt_sub, pt_mem_iff hcc hδ a2 a2', mv_sub]
    exact entries_trans (hs2 z) h1

end GlobalTheory.WeilCorr
