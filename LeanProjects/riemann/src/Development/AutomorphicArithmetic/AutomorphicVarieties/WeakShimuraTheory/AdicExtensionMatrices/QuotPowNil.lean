import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.AdicContMap
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.NearArt
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.SxLimPt
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.SxExtA
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.NearMap
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoQuot

open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem eq_of_forall_sub_mem_maxIdeal_pow_of_adicComplete {R : Type} [CommRing R] [IsLocalRing R]
    [IsAdicComplete (maximalIdeal R) R] {x y : R}
    (h : ∀ N : ℕ, x - y ∈ maximalIdeal R ^ (N + 1)) : x = y := by
  rw [IsHausdorff.eq_iff_smodEq (I := maximalIdeal R)]
  intro n
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
  cases n with
  | zero => simp
  | succ N => exact h N

private theorem nontrivial_quotient_maxIdeal_pow_succ {R : Type} [CommRing R] [IsLocalRing R] (N : ℕ) :
    Nontrivial (R ⧸ maximalIdeal R ^ (N + 1)) := by
  apply Ideal.Quotient.nontrivial_iff.mpr
  intro h
  apply (maximalIdeal.isMaximal R).ne_top
  exact top_le_iff.mp (h ▸ Ideal.pow_le_self (Nat.succ_ne_zero N))

private theorem isNilpotent_maxIdeal_quotient_maxIdeal_pow_succ {R : Type} [CommRing R] [IsLocalRing R] (N : ℕ)
    [IsLocalRing (R ⧸ maximalIdeal R ^ (N + 1))] :
    IsNilpotent (maximalIdeal (R ⧸ maximalIdeal R ^ (N + 1))) := by
  refine ⟨N + 1, ?_⟩
  have hle : maximalIdeal (R ⧸ maximalIdeal R ^ (N + 1)) ≤
      (maximalIdeal R).map (Ideal.Quotient.mk (maximalIdeal R ^ (N + 1))) := by
    intro x hx
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    apply Ideal.mem_map_of_mem
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hx ⊢
    exact fun hu => hx (hu.map _)
  rw [Ideal.zero_eq_bot, eq_bot_iff]
  calc _ ≤ ((maximalIdeal R).map (Ideal.Quotient.mk (maximalIdeal R ^ (N + 1)))) ^ (N + 1) :=
        Ideal.pow_right_mono hle _
    _ = ⊥ := by rw [← Ideal.map_pow, Ideal.map_quotient_self]

theorem UpperTheory.V.Ws.sxNearA :
    ∀ {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] {Φ : Fr O Γ} {Λ : Type} [CommRing Λ] [IsLocalRing Λ] [IsNoetherianRing Λ] [IsAdicComplete (maximalIdeal Λ) Λ] {a : O →+* Λ} {R : Type} [CommRing R] [Algebra Λ R] [IsCO Λ R] {D : RD Φ R} {W : WPres Λ (ℤ × ℤ) R}, Φ.RUniv a D → D.Graded W → ∀ (D' : RD Φ W.A), D'.map (W.A.val : W.A →+* R) = D → ∀ (R' : Type) [CommRing R'] [Algebra Λ R'] [IsCO Λ R'] (τ : ℤ × ℤ →+ ℤ) (Q : RD Φ R'), Φ.Near a τ Q → ∃ f : W.A →ₐ[Λ] R', D'.map (f : W.A →+* R') = Q := by
  intro O Γ _ _ _ Φ Λ _ _ _ _ a R _ _ _ D W hU hG D' hD' R' _ _ _ τ Q hQ
  classical
  have hlev : ∀ N : ℕ, ∃ f : W.A →ₐ[Λ] R' ⧸ maximalIdeal R' ^ (N + 1),
      D'.map (f : W.A →+* _) = Q.map (Ideal.Quotient.mk (maximalIdeal R' ^ (N + 1))) := by
    intro N
    haveI : Nontrivial (R' ⧸ maximalIdeal R' ^ (N + 1)) := nontrivial_quotient_maxIdeal_pow_succ N
    haveI : IsCO Λ (R' ⧸ maximalIdeal R' ^ (N + 1)) :=
      co_quot Λ R' _ (Ideal.Quotient.mkₐ Λ _) (Ideal.Quotient.mkₐ_surjective Λ _)
    exact sxNearArt hU hG D' hD' _ τ _ (isNilpotent_maxIdeal_quotient_maxIdeal_pow_succ N)
      (sxNearMap (Ideal.Quotient.mkₐ Λ (maximalIdeal R' ^ (N + 1))) hQ)
  have hval : ∀ s : W.σ, ∃ y : R', ∀ (N : ℕ) (f : W.A →ₐ[Λ] R' ⧸ maximalIdeal R' ^ (N + 1)),
      D'.map (f : W.A →+* _) = Q.map (Ideal.Quotient.mk (maximalIdeal R' ^ (N + 1))) →
      f (W.zA s) = Ideal.Quotient.mk _ y := by
    intro s
    rcases hG.var s with ⟨g, i, j, c, hz, -, -⟩ | ⟨v, i, t, c, hz, -⟩
    · refine ⟨Q.r g i j - algebraMap Λ R' c, fun N f hf => ?_⟩
      have e1 : D.r g i j = ((D'.r g i j : W.A) : R) := by rw [← hD']; rfl
      have hA : W.zA s = D'.r g i j - algebraMap Λ W.A c := by
        apply Subtype.ext
        change W.z s = _
        rw [hz, e1]
        rfl
      have e2 : f (D'.r g i j) = Ideal.Quotient.mk _ (Q.r g i j) :=
        congrArg (fun E => E.r g i j) hf
      rw [hA, map_sub, AlgHom.commutes, e2, map_sub, Ideal.Quotient.mk_algebraMap]
    · refine ⟨Q.ψ v i t - algebraMap Λ R' c, fun N f hf => ?_⟩
      have e1 : D.ψ v i t = ((D'.ψ v i t : W.A) : R) := by rw [← hD']; rfl
      have hA : W.zA s = D'.ψ v i t - algebraMap Λ W.A c := by
        apply Subtype.ext
        change W.z s = _
        rw [hz, e1]
        rfl
      have e2 : f (D'.ψ v i t) = Ideal.Quotient.mk _ (Q.ψ v i t) :=
        congrArg (fun E => E.ψ v i t) hf
      rw [hA, map_sub, AlgHom.commutes, e2, map_sub, Ideal.Quotient.mk_algebraMap]
  choose y hy using hval
  choose fN hfN using hlev
  have huniq : ∀ (N : ℕ) (f f' : W.A →ₐ[Λ] R' ⧸ maximalIdeal R' ^ (N + 1)),
      (∀ s, f (W.zA s) = f' (W.zA s)) → f = f' := by
    intro N f f' h
    haveI : Nontrivial (R' ⧸ maximalIdeal R' ^ (N + 1)) := nontrivial_quotient_maxIdeal_pow_succ N
    haveI : IsCO Λ (R' ⧸ maximalIdeal R' ^ (N + 1)) :=
      co_quot Λ R' _ (Ideal.Quotient.mkₐ Λ _) (Ideal.Quotient.mkₐ_surjective Λ _)
    exact sxExtA W hG.max _ f f' h
  haveI : IsAdicComplete (maximalIdeal R') R' := IsCO.complete (O := Λ)
  obtain ⟨F, hF⟩ := sxLimPt (Λ := Λ) (maximalIdeal R') W.zA y
    (fun N => ⟨fN N, fun s => hy s N (fN N) (hfN N)⟩) huniq
  have hcomp : ∀ N, (Ideal.Quotient.mkₐ Λ (maximalIdeal R' ^ (N + 1))).comp F = fN N := by
    intro N
    apply huniq
    intro s
    rw [AlgHom.comp_apply, hF s, hy s N (fN N) (hfN N)]
    rfl
  have hpt : ∀ (x : W.A) (q : R'), (∀ N, fN N x = Ideal.Quotient.mk _ q) → F x = q := by
    intro x q hx
    apply eq_of_forall_sub_mem_maxIdeal_pow_of_adicComplete
    intro N
    rw [← Ideal.Quotient.mk_eq_mk_iff_sub_mem, ← hx N, ← hcomp N]
    rfl
  refine ⟨F, ?_⟩
  apply RD.ext
  · ext g i j
    exact hpt _ _ (fun N => congrArg (fun E => E.r g i j) (hfN N))
  · funext v i
    ext t
    exact hpt _ _ (fun N => congrArg (fun E => E.ψ v i t) (hfN N))
