import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.CountLoc
import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.FormValuationGeNegDegree

noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset Formalism.MainNotions.G.LatticeSystems

section Loc

variable {W Qq : Type} [CommRing W] [Field Qq] [Algebra W Qq]

theorem between_fin (p k : ℕ) (hfin : Finite (W ⧸ Ideal.span {(p : W)})) (L : Submodule W (Fin k → Qq))
    (hL : IsLattice W L) :
    {A : Submodule W (Fin k → Qq) | A ≤ L ∧ ∀ x ∈ L, (p : W) • x ∈ A}.Finite := by
  classical
  obtain ⟨g, -, hg⟩ := hL
  have hfg : L.FG := by
    rw [hg]; exact Submodule.fg_span (Set.finite_range _)
  have : Module.Finite W L := Module.Finite.iff_fg.mpr hfg
  set I : Ideal W := Ideal.span {(p : W)} with hI
  have : Module.Finite (W ⧸ I) (↥L ⧸ I • (⊤ : Submodule W L)) :=
    Module.Finite.of_restrictScalars_finite W _ _
  have : Finite (↥L ⧸ I • (⊤ : Submodule W L)) := Module.finite_of_finite (W ⧸ I)
  let f : Submodule W (Fin k → Qq) → Set (↥L ⧸ I • (⊤ : Submodule W L)) :=
    fun A => ((A.comap L.subtype).map (I • (⊤ : Submodule W L)).mkQ : Set _)
  refine Set.Finite.of_finite_image (f := f) (Set.toFinite _) ?_
  have key : ∀ A : Submodule W (Fin k → Qq), (∀ x ∈ L, (p : W) • x ∈ A) →
      I • (⊤ : Submodule W L) ≤ A.comap L.subtype := by
    intro A hA
    rw [Submodule.smul_le]
    intro a ha x _
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    rw [mul_smul]
    apply Submodule.smul_mem
    show (p : W) • (x : Fin k → Qq) ∈ A
    exact hA x x.2
  intro A hA B hB hAB
  have h1 : (A.comap L.subtype).map (I • (⊤ : Submodule W L)).mkQ =
      (B.comap L.subtype).map (I • (⊤ : Submodule W L)).mkQ := SetLike.coe_injective hAB
  have h2 := congrArg (Submodule.comap (I • (⊤ : Submodule W L)).mkQ) h1
  rw [Submodule.comap_map_mkQ, Submodule.comap_map_mkQ, sup_eq_right.mpr (key A hA.2),
    sup_eq_right.mpr (key B hB.2)] at h2
  have h3 := congrArg (Submodule.map L.subtype) h2
  rw [Submodule.map_comap_subtype, Submodule.map_comap_subtype, inf_eq_right.mpr hA.1,
    inf_eq_right.mpr hB.1] at h3
  exact h3

theorem up_fin_gen (p n' r k : ℕ) (hfin : Finite (W ⧸ Ideal.span {(p : W)})) (hp : algebraMap W Qq (p : W) ≠ 0)
    (A : Submodule W (Fin k → Qq)) :
    {A1 : Submodule W (Fin k → Qq) | IsEdge p n' r ⟨A, A1⟩}.Finite := by
  by_cases hA : IsLattice W A
  · let φ : (Fin k → Qq) →ₗ[W] (Fin k → Qq) := (p : W) • LinearMap.id
    have hφ : Function.Injective φ := by
      intro x y hxy
      have h1 : (p : W) • x = (p : W) • y := hxy
      rw [← algebraMap_smul Qq (p : W) x, ← algebraMap_smul Qq (p : W) y] at h1
      exact smul_right_injective _ hp h1
    refine Set.Finite.of_finite_image (f := fun A1 => A1.map φ) ((between_fin p k hfin A hA).subset ?_)
      (fun a _ b _ h => Submodule.map_injective_of_injective hφ h)
    rintro _ ⟨A1, hA1, rfl⟩
    refine ⟨?_, ?_⟩
    · rintro _ ⟨x, hx, rfl⟩
      exact hA1.2.2.2.1 x hx
    · intro x hx
      exact ⟨x, hA1.2.2.1 hx, rfl⟩
  · convert Set.finite_empty
    ext A1
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    exact fun h => hA h.1

theorem count_fun (hC : CountLoc) (p n' : ℕ) [IsDomain W] [IsDiscreteValuationRing W] (h1 : IsFractionRing W Qq)
    (h2 : Irreducible (p : W)) (h3 : Nat.card (W ⧸ Ideal.span {(p : W)}) = p ^ n') (N N' g i : ℕ) (hN : N' = N + g)
    (A : Submodule W (Fin N → Qq)) (B : Submodule W (Fin N' → Qq)) (hA : IsLattice W A) (hB : IsLattice W B)
    (SB : Finset (Submodule W (Fin N' → Qq))) (hSB : ∀ B1, B1 ∈ SB ↔ IsEdge p n' i ⟨B1, B⟩)
    (SA : ℕ → Finset (Submodule W (Fin N → Qq))) (hSA : ∀ k A1, A1 ∈ SA k ↔ IsEdge p n' k ⟨A, A1⟩)
    (x : Matrix (Fin N') (Fin N) Qq) :
    (∑ B1 ∈ SB, (by classical exact if ∀ y ∈ A, x.mulVec y ∈ B1 then (1 : ℚ) else 0)) =
      ∑ l ∈ range (i + 1), (((p ^ n') ^ ((i - l) * (g - l)) * Formalism.G0.gaussBinom (p ^ n') g l : ℕ) : ℚ) *
        ∑ A1 ∈ SA (i - l), (by classical exact if ∀ y ∈ A1, x.mulVec y ∈ B then (1 : ℚ) else 0) := by
  classical
  have e1 : ∀ (M : ℕ) (S : Finset (Submodule W (Fin M → Qq))) (E Pp : Submodule W (Fin M → Qq) → Prop)
      (_ : ∀ Z, Z ∈ S ↔ E Z), (∑ Z ∈ S, if Pp Z then (1 : ℚ) else 0) =
        (Nat.card {Z : Submodule W (Fin M → Qq) // E Z ∧ Pp Z} : ℚ) := by
    intro M S E Pp hS
    rw [Finset.sum_boole]
    congr 1
    rw [← Nat.card_eq_fintype_card.trans (Fintype.card_coe (S.filter Pp))]
    apply Nat.card_congr
    exact Equiv.subtypeEquivRight fun Z => by rw [Finset.mem_filter, hS]
  have := hC p n' W Qq h1 h2 h3 N N' g i hN A B hA hB x
  convert congrArg (fun n : ℕ => (n : ℚ)) this using 1
  · exact e1 N' SB _ _ hSB
  · push_cast
    apply Finset.sum_congr rfl
    intro l _
    congr 1
    exact e1 N (SA (i - l)) _ _ (hSA (i - l))

end Loc

section PlacesLevel

variable {p : ℕ} {O Kf : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  (P : Places p O Kf)

theorem hk_pQ_ne (v : Fin P.nV) : algebraMap (P.W v) (P.Qq v) (p : P.W v) ≠ 0 := by
  have := (P.setting v).frac_alt
  exact (map_ne_zero_iff _ (IsFractionRing.injective (P.W v) (P.Qq v))).2 (P.setting v).p_unif.ne_zero

theorem up_fin (v : Fin P.nV) (i : ℕ) (A : Submodule (P.W v) (Fin (P.m + 1) → P.Qq v)) :
    {A1 : Submodule (P.W v) (Fin (P.m + 1) → P.Qq v) | IsEdge p (P.n' v) i ⟨A, A1⟩}.Finite := by
  apply up_fin_gen
  · apply Nat.finite_of_card_ne_zero
    rw [(P.setting v).res_card]
    exact pow_ne_zero _ (P.setting v).prime.ne_zero
  · exact hk_pQ_ne P v

def UP (v : Fin P.nV) (i : ℕ) (A : Submodule (P.W v) (Fin (P.m + 1) → P.Qq v)) :
    Finset (Submodule (P.W v) (Fin (P.m + 1) → P.Qq v)) :=
  (up_fin P v i A).toFinset

theorem mem_UP {v : Fin P.nV} {i : ℕ} {A A1 : Submodule (P.W v) (Fin (P.m + 1) → P.Qq v)} :
    A1 ∈ UP P v i A ↔ IsEdge p (P.n' v) i ⟨A, A1⟩ := by
  simp [UP]

theorem hk_latTup_update {L : P.Tup} (hL : P.IsLatTup L) (v : Fin P.nV)
    (A : Submodule (P.W v) (Fin (P.m + 1) → P.Qq v)) (hA : IsLattice (P.W v) A) :
    P.IsLatTup (Function.update (β := fun v => Submodule (P.W v) (Fin (P.m + 1) → P.Qq v)) L v A) := by
  unfold Places.IsLatTup at *
  intro w
  by_cases h : w = v
  · subst h
    have e : Function.update (β := fun v => Submodule (P.W v) (Fin (P.m + 1) → P.Qq v)) L w A w = A := by
      first
        | exact Function.update_self (β := fun v => Submodule (P.W v) (Fin (P.m + 1) → P.Qq v)) w A L
        | exact Function.update_same (β := fun v => Submodule (P.W v) (Fin (P.m + 1) → P.Qq v)) w A L
    exact (congrArg (fun Z => IsLattice (P.W w) Z) e).mpr hA
  · have e : Function.update (β := fun v => Submodule (P.W v) (Fin (P.m + 1) → P.Qq v)) L v A w = L w := Function.update_of_ne (β := fun v => Submodule (P.W v) (Fin (P.m + 1) → P.Qq v)) h A L
    exact (congrArg (fun Z => IsLattice (P.W w) Z) e).mpr (hL w)

theorem latTup_smul (C : Level P) (γ : C.Γ) (L : P.Tup) : P.IsLatTup (C.smul γ L) ↔ P.IsLatTup L := by
  constructor
  · intro h u
    have h1 : IsLattice (P.W u) ((L u).map (nt_phi (P.W u) (C.act u γ))) := h u
    have h2 := nt_lat_map (C.act u γ)⁻¹ _ h1
    rw [nt_map_inv] at h2
    exact h2
  · intro h u
    exact nt_lat_map (C.act u γ) (L u) (h u)

end PlacesLevel

end Formalism.MainNotions.FormalGroupSystem.Pf
