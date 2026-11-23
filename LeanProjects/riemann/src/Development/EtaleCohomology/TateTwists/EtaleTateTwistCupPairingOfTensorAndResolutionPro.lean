import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.EtaleCohomology.TateTwists.EtaleTwistResolutionPairingCupUnique

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

def twpair_tens_ex : Prop :=
  ∀ (R : Type) [CommRing R] (I J : Cx R), ∃ (K : Cx R) (τ : Pair I J K), τ.IsTensor

def twpair_tens_univ : Prop :=
  ∀ (R : Type) [CommRing R] {I J K : Cx R} (τ : Pair I J K), τ.IsTensor → (∀ {I' J' K' : Cx R} (ν : Pair I' J' K') (f : I ⟶ I') (g : J ⟶ J'), ∃! u : K ⟶ K', τ.Compat ν f g u) ∧ (I.IsStrictlyGE 0 → J.IsStrictlyGE 0 → K.IsStrictlyGE 0) ∧ ∀ {K' : Cx R} (u : K ⟶ K'), ∃ ν : Pair I J K', τ.Compat ν (𝟙 I) (𝟙 J) u

def twpair_tens_twres : Prop :=
  ∀ (q : ℕ) [NeZero q] (i j k : ℤ), i + j = k → ∀ {I J T : Cx (ZMod q)} (e : ∀ U : Scheme.{0}, Prim q Γ(U, ⊤) → Sec (I.X 0) U) (e' : ∀ U : Scheme.{0}, Prim q Γ(U, ⊤) → Sec (J.X 0) U), IsTwRes q i I e → IsTwRes q j J e' → (∀ t, FlatS (J.X t)) → ∀ τ : Pair I J T, τ.IsTensor → IsTwRes q k T fun U ζ => τ.mul U 0 0 0 (add_zero 0) (e U ζ) (e' U ζ)

def twpair_twres_ext : Prop :=
  ∀ (q : ℕ) [NeZero q] (i : ℤ), IsTwRes q i (res _ (tw q i)) (fun _ ζ => resGen i ζ) ∧ (∀ t, FlatS ((res _ (tw q i)).X t)) ∧ ∀ {T : Cx (ZMod q)} (e : ∀ U : Scheme.{0}, Prim q Γ(U, ⊤) → Sec (T.X 0) U), IsTwRes q i T e → (∃ u : T ⟶ res _ (tw q i), ∀ U ζ, Sec.map (u.f 0) (e U ζ) = resGen i ζ) ∧ ∀ u u' : T ⟶ res _ (tw q i), (∀ U ζ, Sec.map (u.f 0) (e U ζ) = Sec.map (u'.f 0) (e U ζ)) → Nonempty (Homotopy u u')

def twpair_cup_compat : Prop :=
  ∀ (R : Type) [CommRing R] {I J K I' J' K' : Cx R} (μ : Pair I J K) (ν : Pair I' J' K') (f : I ⟶ I') (g : J ⟶ J') (u : K ⟶ K'), μ.Compat ν f g u → ∀ (E : Spc) {n m k : ℤ} (hk : n + m = k) a b, cpush _ u k (μ.cup E hk a b) = ν.cup E hk (cpush _ f n a) (cpush _ g m b)

def twpair_zc_fun : Prop :=
  ∀ (R : Type) [CommRing R] , (∀ (K I : Cx R) (n : ℤ) x, cpull (𝟙 K) I n x = x ∧ cpush K (𝟙 I) n x = x) ∧ (∀ {K L M : Cx R} (f : K ⟶ L) (g : L ⟶ M) (I : Cx R) (n : ℤ) x, cpull (f ≫ g) I n x = cpull f I n (cpull g I n x)) ∧ (∀ (K : Cx R) {I J M : Cx R} (f : I ⟶ J) (g : J ⟶ M) (n : ℤ) x, cpush K (f ≫ g) n x = cpush K g n (cpush K f n x)) ∧ (∀ {K L I J : Cx R} (f : K ⟶ L) (g : I ⟶ J) (n : ℤ) x, cpull f J n (cpush L g n x) = cpush K g n (cpull f I n x)) ∧ (∀ {K L : Cx R} (f g : K ⟶ L), Nonempty (Homotopy f g) → ∀ (I : Cx R) (n : ℤ), cpull f I n = cpull g I n ∧ cpush I f n = cpush I g n)

theorem etale_tate_twist_cup_pairing_of_tensor_and_resolution_properties (h1 : twpair_tens_ex) (h2 : twpair_tens_univ) (h3 : twpair_tens_twres)
    (h4 : twpair_twres_ext) (h5 : twpair_cup_compat) (h6 : twpair_zc_fun) : LateralTheory.EtaleFoundations.EtaleTwistResolutionPairingCupUnique := by
  intro q _ i j
  obtain ⟨T, τ, hτ⟩ := h1 (ZMod q) (res _ (tw q i)) (res _ (tw q j))
  have hT := h3 q i j (i + j) rfl _ _ (h4 q i).1 (h4 q j).1 (h4 q j).2.1 τ hτ
  obtain ⟨⟨u, hu⟩, hhom⟩ := (h4 q (i + j)).2.2 _ hT
  refine ⟨?_, ?_⟩
  · obtain ⟨ν, hν⟩ := (h2 (ZMod q) τ hτ).2.2 u
    apply pick_spec
    refine ⟨ν, fun U ζ => ?_⟩
    have := hν U 0 0 0 (add_zero 0) (resGen i ζ) (resGen j ζ)
    rw [← hu U ζ, this]
    rfl
  · intro k hk μ ν hμ hν E n m w h
    subst hk
    obtain ⟨uμ, huμ, -⟩ := (h2 (ZMod q) τ hτ).1 μ (𝟙 _) (𝟙 _)
    obtain ⟨uν, huν, -⟩ := (h2 (ZMod q) τ hτ).1 ν (𝟙 _) (𝟙 _)
    have hgen : ∀ U ζ, Sec.map (uμ.f 0) (τ.mul U 0 0 0 (add_zero 0) (resGen i ζ) (resGen j ζ)) =
        Sec.map (uν.f 0) (τ.mul U 0 0 0 (add_zero 0) (resGen i ζ) (resGen j ζ)) := by
      intro U ζ
      rw [huμ U 0 0 0 (add_zero 0), huν U 0 0 0 (add_zero 0)]
      exact (hμ U ζ).trans (hν U ζ).symm
    have hh := hhom uμ uν hgen
    have hp := ((h6 (ZMod q)).2.2.2.2 uμ uν hh ((chains (ZMod q)).obj E) w).2
    have hid := (h6 (ZMod q)).1
    ext a b
    have e1 := h5 (ZMod q) τ μ (𝟙 _) (𝟙 _) uμ huμ E h a b
    have e2 := h5 (ZMod q) τ ν (𝟙 _) (𝟙 _) uν huν E h a b
    rw [(hid _ _ n a).2, (hid _ _ m b).2] at e1 e2
    rw [← e1, ← e2, hp]

end LateralTheory.EtaleFoundations
