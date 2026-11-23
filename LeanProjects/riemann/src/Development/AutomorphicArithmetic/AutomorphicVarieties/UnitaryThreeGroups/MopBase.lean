import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.IsLocPres
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Graded
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueFixedPointOfAdicContraction

open Matrix IsLocalRing UpperTheory.V.Alg

namespace UpperTheory.V.U3.Mop

theorem emb_map {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (x : GG 3 R)
    (a b : Fin 3 ⊕ Fin 3) : emb (GG.map f x) a b = f (emb x a b) := by
  have h : (theta (GG.map f x).left : Matrix (Fin 3) (Fin 3) S) =
      (theta x.left : Matrix (Fin 3) (Fin 3) R).map f :=
    (congrArg Units.val (map_theta f x.left)).symm
  show (if (GG.map f x).right = 1 then Matrix.fromBlocks (GG.map f x).mat 0 0 (theta (GG.map f x).left : Matrix (Fin 3) (Fin 3) S)
    else Matrix.fromBlocks 0 (GG.map f x).mat (theta (GG.map f x).left : Matrix (Fin 3) (Fin 3) S) 0) a b =
    f ((if x.right = 1 then Matrix.fromBlocks x.mat 0 0 (theta x.left : Matrix (Fin 3) (Fin 3) R)
    else Matrix.fromBlocks 0 x.mat (theta x.left : Matrix (Fin 3) (Fin 3) R) 0) a b)
  rw [h, GG.map_mat, GG.map_right]
  split_ifs <;> rcases a with a | a <;> rcases b with b | b <;> simp

theorem emb_push {O G R S : Type} [CommRing O] [Group G] [CommRing R] [CommRing S] [Algebra O R] [Algebra O S]
    (f : R →ₐ[O] S) (r : G →* GG 3 R) (g : G) (a b : Fin 3 ⊕ Fin 3) :
    emb (push f r g) a b = f (emb (r g) a b) := emb_map (f : R →+* S) (r g) a b

theorem emb_apply {R : Type} [CommRing R] (x : GG 3 R) : emb x =
    if x.right = 1 then Matrix.fromBlocks x.mat 0 0 (theta x.left : Matrix (Fin 3) (Fin 3) R)
    else Matrix.fromBlocks 0 x.mat (theta x.left : Matrix (Fin 3) (Fin 3) R) 0 := rfl

theorem mat_eq_emb {R : Type} [CommRing R] (x : GG 3 R) (a b : Fin 3) :
    x.mat a b = emb x (.inl a) (.inl b) + emb x (.inl a) (.inr b) := by
  rw [emb_apply]
  split_ifs <;> simp

theorem unitaryEmbedding_residualRep_eq_zero_of_weight_ne {G R : Type} [Group G] [CommRing R] (η : G →* ℤˣ) (Ψ : G →* Rˣ) (g : G)
    (a b : Fin 3 ⊕ Fin 3) (h : wt6 a ≠ wt6 b) : emb (r0 η Ψ g) a b = 0 := by
  show (if (r0 η Ψ g).right = 1 then Matrix.fromBlocks (tor R (Ψ g) : Matrix (Fin 3) (Fin 3) R) 0 0
    (theta (tor R (Ψ g)) : Matrix (Fin 3) (Fin 3) R) else Matrix.fromBlocks 0 (tor R (Ψ g) : Matrix (Fin 3) (Fin 3) R)
    (theta (tor R (Ψ g)) : Matrix (Fin 3) (Fin 3) R) 0) a b = 0
  rw [theta_tor, tor_val]
  split_ifs <;> rcases a with a | a <;> rcases b with b | b <;>
    first
    | rfl
    | exact Matrix.diagonal_apply_ne (i := a) (j := b) (fun i => ((Ψ g ^ wt1 i : Rˣ) : R)) (by rintro rfl; exact h rfl)

theorem blockWeight_sub_mem_Icc (a b : Fin 3 ⊕ Fin 3) : -2 ≤ wt6 a - wt6 b ∧ wt6 a - wt6 b ≤ 2 := by
  revert a b; decide

theorem origin_of {O X R : Type} [CommRing O] [AddCommGroup X] [CommRing R] [Algebra O R] (W : WPres O X R)
    (y : R →ₐ[O] O) (hy : ∀ s, y (W.z s) = 0) : ∃ h : W.HasOrigin, W.origin h = y := by
  have key : ∀ F, y (W.π F) = MvPowerSeries.constantCoeff F := fun F => by
    have := GlobalTheory.algHom_sub_constantCoeff_mem (K := ⊥) (y.comp W.π) (fun s => hy s) F
    rw [Ideal.mem_bot, sub_eq_zero] at this
    exact this
  refine ⟨fun F hF => by rw [← key, hF, map_zero], AlgHom.ext fun x => ?_⟩
  obtain ⟨F, rfl⟩ := W.surj x
  exact (W.origin_π _ F).trans (key F).symm

theorem origin_presentation_var_eq_zero {O X R : Type} [CommRing O] [AddCommGroup X] [CommRing R] [Algebra O R] (W : WPres O X R)
    (h : W.HasOrigin) (s : W.σ) : W.origin h (W.z s) = 0 := by
  rw [WPres.z, W.origin_π, MvPowerSeries.constantCoeff_X]

theorem mem_max_of_zero {O R : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
    [IsAdicComplete (maximalIdeal O) O] [CommRing R] [Algebra O R] [IsCO O R] (x : R →ₐ[O] O) {z : R} (hz : x z = 0) :
    z ∈ maximalIdeal R := by
  rw [← res_eq_zero_iff O, ← res_map x, hz, map_zero]

theorem base_coord {O G R : Type} [CommRing O] [Group G] [CommRing R] [Algebra O R] {η : G →* ℤˣ} {Ψ : G →* Oˣ}
    {r : G →* GG 3 R} {x : R →ₐ[O] O} (hx : push x r = r0 η Ψ) (g : G) (a b : Fin 3 ⊕ Fin 3) :
    x (emb (r g) a b - algebraMap O R (emb (r0 η Ψ g) a b)) = 0 := by
  rw [map_sub, AlgHom.commutes, ← emb_push, hx]
  exact sub_self _

theorem approx {O X R σ : Type} [CommRing O] [AddCommGroup X] [CommRing R] [Algebra O R] [Finite σ] (wt : σ → X)
    (Φ : MvPowerSeries σ O →ₐ[O] R) (m : Ideal R) (𝓑 : X → Submodule O R) (h1 : (1 : R) ∈ 𝓑 0)
    (hmul : ∀ i j, ∀ a ∈ 𝓑 i, ∀ b ∈ 𝓑 j, a * b ∈ 𝓑 (i + j))
    (hm : ∀ s, Φ (MvPowerSeries.X s) ∈ m) (hB : ∀ s, Φ (MvPowerSeries.X s) ∈ 𝓑 (wt s)) (j : X)
    (F : MvPowerSeries σ O) (hF : F ∈ wtPart O wt j) (n : ℕ) : ∃ y ∈ 𝓑 j, Φ F - y ∈ m ^ n := by
  classical
  refine ⟨_, ?_, GlobalTheory.algHom_sub_aeval_truncTotal_mem Φ hm n F⟩
  have hpow : ∀ s (k : ℕ), Φ (MvPowerSeries.X s) ^ k ∈ 𝓑 (k • wt s) := fun s k => by
    induction k with
    | zero => simpa using h1
    | succ k ih => rw [pow_succ, succ_nsmul]; exact hmul _ _ _ ih _ (hB s)
  have hmon : ∀ d : σ →₀ ℕ, (d.prod fun s k => Φ (MvPowerSeries.X s) ^ k) ∈ 𝓑 (Finsupp.weight wt d) := fun d => by
    induction d using Finsupp.induction_linear with
    | zero => simpa using h1
    | add f g hf hg =>
      rw [Finsupp.prod_add_index' (by simp) (fun _ _ _ => pow_add _ _ _), map_add]
      exact hmul _ _ _ hf _ hg
    | single i k =>
      rw [Finsupp.prod_single_index (by simp), Finsupp.weight_single]
      exact hpow i k
  rw [(MvPowerSeries.truncTotal n F).as_sum, map_sum]
  refine Submodule.sum_mem _ fun d hd => ?_
  rw [MvPolynomial.aeval_monomial, ← Algebra.smul_def]
  refine Submodule.smul_mem _ _ ?_
  have hw : Finsupp.weight wt d = j := by
    by_contra hne
    refine MvPolynomial.mem_support_iff.1 hd ?_
    by_cases hlt : Finsupp.degree d < n
    · rw [MvPowerSeries.coeff_truncTotal _ hlt]; exact hF d hne
    · exact MvPowerSeries.coeff_truncTotal_eq_zero _ (not_lt.1 hlt)
  exact hw ▸ hmon d

def nEq {G R : Type} [Group G] [CommRing R] (c g₁ : G) (r : G →* GG 3 R) : Fin 8 → R :=
  ![(r c).mat 0 0 - 1, (r c).mat 1 1 - 1, (r c).mat 0 1, (r c).mat 1 0, (r c).mat 0 2, (r c).mat 2 0,
    zmat c g₁ r 0 1, zmat c g₁ r 1 0]

def nWt : Fin 8 → ℤ := ![0, 0, 1, -1, 2, -2, 1, -1]

end UpperTheory.V.U3.Mop
