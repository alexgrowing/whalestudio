import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.MapEta
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.LcOfAdic
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.RhoHom
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.AmFin
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

private theorem card_le_of_rel {P A B Z : Type} (p : P → A) (q : P → B) (hq : Function.Surjective q)
    (S : Set (A → Z)) (S' : Set (B → Z)) (hS : S.Finite) (h : ∀ z' ∈ S', ∃ z ∈ S, ∀ g, z (p g) = z' (q g)) :
    S'.Finite ∧ S'.ncard ≤ S.ncard := by
  have hinj : Function.Injective fun z' : B → Z => z' ∘ q := hq.injective_comp_right
  have hsub : (fun z' : B → Z => z' ∘ q) '' S' ⊆ (fun z : A → Z => z ∘ p) '' S := by
    rintro _ ⟨z', hz', rfl⟩
    obtain ⟨z, hz, e⟩ := h z' hz'
    exact ⟨z, hz, funext e⟩
  refine ⟨Set.Finite.of_finite_image ((hS.image _).subset hsub) hinj.injOn, ?_⟩
  rw [← Set.ncard_image_of_injective S' hinj]
  exact (Set.ncard_le_ncard hsub (hS.image _)).trans (Set.ncard_image_le hS)

theorem UpperTheory.V.Pa.taylorWiles_first_condition_at_limit_of_group_condition :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (T : TWGrp G0) (Λ : Lim T) (n : ℕ) (x : NP G0.frame n) (k : Kap x) (D0 : ℕ), T.B1 k D0 → FirstSelmerCardBoundAtAllLevels Λ.h k D0 := by
  intro l _ L G0 T Λ n x k D0 ⟨C, hC⟩
  refine ⟨C, fun m => ?_⟩
  obtain ⟨hfin, -, hn, hn', -⟩ := am_fin l G0.frame n x m k.g
  obtain ⟨-, ⟨h1, h2, -⟩, h3, -⟩ := rho_hom l G0.frame n x k (x.Am m)
  obtain ⟨N, ⟨hρ, hz, -⟩, hf, hle⟩ := ((t1 l L G0 T Λ n x.A (DD (x.Am m) k.g) x.t (k.ρ1 (x.Am m)) (k.w1 (x.Am m))
    (k.wi1 (x.Am m)) (W1 n x.A (x.Am m) k.g x.a) hn' h1 h2 (h3 hn).2).and (Λ.U_le (hC m))).exists
  obtain ⟨hf', hle'⟩ := card_le_of_rel (Λ.π0 N) Λ.πo0 Λ.πo0_surj (Sel1 (T.h N) (x.Am m) k) (Sel1 Λ.h (x.Am m) k) hf hz
  have hB : (Bd1 Λ.h (x.Am m) k).Finite :=
    (Set.finite_range (dY Λ.G.frame fun g => k.ρ1 (x.Am m) (Λ.h.p₀ g))).subset (by
      rintro _ ⟨Y, -, -, rfl⟩
      exact ⟨Y, rfl⟩)
  have hBle := (card_le_of_rel Λ.πo0 (Λ.π0 N) (Λ.π0_surj N) (Bd1 Λ.h (x.Am m) k) (Bd1 (T.h N) (x.Am m) k) hB (by
    rintro _ ⟨Y, hY, hY', rfl⟩
    refine ⟨_, ⟨Y, hY, hY', rfl⟩, fun g => ?_⟩
    have e1 := hρ g
    have e2 := hρ g⁻¹
    rw [map_inv (Λ.π0 N), map_inv Λ.πo0] at e2
    show k.ρ1 _ (Λ.h.p₀ (Λ.πo0 g)) * Y * k.ρ1 _ (Λ.h.p₀ (Λ.πo0 g)⁻¹) - Y =
      k.ρ1 _ ((T.h N).p₀ (Λ.π0 N g)) * Y * k.ρ1 _ ((T.h N).p₀ (Λ.π0 N g)⁻¹) - Y
    rw [e1, e2])).2
  exact ⟨hf', hle'.trans (hle.trans (Nat.mul_le_mul_right _ hBle))⟩
