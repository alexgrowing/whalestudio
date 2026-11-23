import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsDualBound
import Lemmata.GeneralBFactLeftRest.Imports

open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.D2

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

namespace RedC

theorem index_eq_card {G T : Type*} [Group G] (N : Subgroup G) (f : G → T) (hs : Function.Surjective f)
    (hf : ∀ a b, f a = f b ↔ a⁻¹ * b ∈ N) : N.index = Nat.card T := by
  first | exact Bl.general_b_fact_left_rest.goal1 .. | (apply Bl.general_b_fact_left_rest.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_left_rest.goal1 <;> assumption)

def redEnd (A : Submodule (𝓞 K) V) (𝔭 : Ideal (𝓞 F)) (k : ℕ) (X : V ≃ₗ[K] V) (hX : X ∈ glSub A) :
    Module.End (𝓞 K) (↥A ⧸ ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥A)) :=
  Submodule.mapQ _ _ (((X : V →ₗ[K] V).restrictScalars (𝓞 K)).restrict fun _ hx => apply_mem hX hx)
    (fun x hx => by
      rw [Submodule.mem_comap, Submodule.mem_smul_top_iff]
      rw [Submodule.mem_smul_top_iff] at hx
      exact apply_mem_smul hX _ hx)

theorem redEnd_mk (A : Submodule (𝓞 K) V) (𝔭 : Ideal (𝓞 F)) (k : ℕ) (X : V ≃ₗ[K] V) (hX : X ∈ glSub A)
    (x : ↥A) : redEnd A 𝔭 k X hX (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk ⟨X x, apply_mem hX x.2⟩ := rfl

theorem mk_eq_redEnd_iff {A : Submodule (𝓞 K) V} {𝔭 : Ideal (𝓞 F)} {k : ℕ} {X : V ≃ₗ[K] V}
    (hX : X ∈ glSub A) (x x' : ↥A) :
    Submodule.Quotient.mk x' = redEnd A 𝔭 k X hX (Submodule.Quotient.mk x) ↔
      (x' : V) - X x ∈ extP K 𝔭 ^ k • A := by
  rw [redEnd_mk, Submodule.Quotient.eq, Submodule.mem_smul_top_iff]
  rfl

theorem redEnd_eq_iff {A : Submodule (𝓞 K) V} {𝔭 : Ideal (𝓞 F)} {k : ℕ} {a b : V ≃ₗ[K] V}
    (ha : a ∈ glSub A) (hb : b ∈ glSub A) :
    redEnd A 𝔭 k a ha = redEnd A 𝔭 k b hb ↔ a⁻¹ * b ∈ nSub A 𝔭 k := by
  have e : ∀ z : V, a⁻¹ (a z) = z := fun z => by
    rw [← LinearEquiv.mul_apply, inv_mul_cancel]
    rfl
  have e' : ∀ z : V, a (a⁻¹ z) = z := fun z => by
    rw [← LinearEquiv.mul_apply, mul_inv_cancel]
    rfl
  constructor
  · intro hab
    refine ⟨mul_mem (inv_mem ha) hb, fun x hx => ?_⟩
    have h1 : Submodule.Quotient.mk (⟨b x, apply_mem hb hx⟩ : ↥A) =
        redEnd A 𝔭 k a ha (Submodule.Quotient.mk ⟨x, hx⟩) := by
      rw [hab, redEnd_mk]
    have h2 := apply_mem_smul (inv_mem ha) _ ((mk_eq_redEnd_iff ha _ _).1 h1)
    simpa [e] using h2
  · rintro ⟨-, hab⟩
    refine LinearMap.ext fun q => ?_
    induction q using Submodule.Quotient.induction_on with | _ x => ?_
    symm
    rw [redEnd_mk, mk_eq_redEnd_iff]
    have h2 := apply_mem_smul ha _ (hab x x.2)
    simpa [e'] using h2

theorem redEnd_cond (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K} {A₀ : Submodule (𝓞 K) V}
    (hA₀i : Formalism.HermitianLatticesTheory.IsIntegralLat h A₀) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {k : ℕ} {X : V ≃ₗ[K] V}
    (hX : X ∈ sSub h (locF 𝔭 A₀) 𝔭 k) (x y x' y' : ↥(locF 𝔭 A₀))
    (hx : Submodule.Quotient.mk x' = redEnd (locF 𝔭 A₀) 𝔭 k X hX.1 (Submodule.Quotient.mk x))
    (hy : Submodule.Quotient.mk y' = redEnd (locF 𝔭 A₀) 𝔭 k X hX.1 (Submodule.Quotient.mk y)) :
    CongrP 𝔭 k (h (x' : V) (y' : V)) (h (x : V) (y : V)) := by
  rw [congrP_algebraMap_iff_sub_mem h𝔭]
  rw [mk_eq_redEnd_iff] at hx hy
  have z : ∀ w ∈ locF 𝔭 A₀, w ∈ extP K 𝔭 ^ 0 • locF 𝔭 A₀ := fun w hw => by rwa [pow_zero_smul]
  have h1 := hX.2 x x.2 y y.2
  have h2 := form_mem_pK hF hA₀i h𝔭 hx (z _ y'.2)
  have h3 := form_mem_pK hF hA₀i h𝔭 (z _ (apply_mem hX.1 x.2)) hy
  rw [add_zero] at h2
  rw [zero_add] at h3
  have h4 := add_mem (add_mem h1 h2) h3
  have e : h (x' : V) (y' : V) - h (x : V) (y : V) =
      h (X x) (X y) - h (x : V) (y : V) + h ((x' : V) - X x) (y' : V) + h (X x) ((y' : V) - X y) := by
    simp only [map_sub, LinearMap.sub_apply]
    abel
  rw [e]
  exact h4

theorem mem_smul_of_smul_mem {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (A : Submodule (𝓞 K) V) (k : ℕ)
    {t : 𝓞 F} (ht : t ∉ 𝔭) {v : V} (hv : v ∈ A)
    (h : algebraMap (𝓞 F) (𝓞 K) t • v ∈ extP K 𝔭 ^ k • A) : v ∈ extP K 𝔭 ^ k • A := by
  obtain ⟨u, hu⟩ := MeanA.exists_mul_sub_one_mem_pow h𝔭 ht k
  have : v = algebraMap (𝓞 F) (𝓞 K) u • (algebraMap (𝓞 F) (𝓞 K) t • v) -
      algebraMap (𝓞 F) (𝓞 K) (u * t - 1) • v := by
    rw [map_sub, map_mul, map_one, sub_smul, mul_smul, one_smul]; abel
  rw [this]
  exact sub_mem (Submodule.smul_mem _ _ h) (Submodule.smul_mem_smul (localizedQuotients.ι_mem_pow hu) hv)

theorem mem_locF_of_smul_mem {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (A₀ : Submodule (𝓞 K) V)
    {t : 𝓞 F} (ht : t ∉ 𝔭) {v : V} (h : algebraMap (𝓞 F) (𝓞 K) t • v ∈ locF 𝔭 A₀) : v ∈ locF 𝔭 A₀ := by
  have := h𝔭.isPrime
  obtain ⟨s, hs, h1⟩ := (LocalSpans.mem_locF 𝔭 A₀ _).1 h
  refine (LocalSpans.mem_locF 𝔭 A₀ _).2 ⟨s * t, fun h => (h𝔭.isPrime.mem_or_mem h).elim hs ht, ?_⟩
  rwa [map_mul, mul_smul]

theorem exists_lift {A₀ : Submodule (𝓞 K) V} (hA₀ : Submodule.IsLattice K A₀) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) (k : ℕ)
    (Y : Module.End (𝓞 K) (↥(locF 𝔭 A₀) ⧸ ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥(locF 𝔭 A₀)))) :
    ∃ D : V →ₗ[K] V, ∀ x : ↥(locF 𝔭 A₀), ∃ hD : D x ∈ locF 𝔭 A₀,
      Submodule.Quotient.mk (⟨D x, hD⟩ : ↥(locF 𝔭 A₀)) = Y (Submodule.Quotient.mk x) := by
  have := h𝔭.isPrime
  obtain ⟨b, -, hb⟩ := LocalSpans.exists_basis_locF hA₀ h𝔭
  have hsp : Submodule.span (𝓞 K) (Set.range b) ≤ locF 𝔭 A₀ := hb ▸ localizedQuotients.le_locF 𝔭 _
  have hbA : ∀ i, b i ∈ locF 𝔭 A₀ := fun i => hsp (Submodule.subset_span ⟨i, rfl⟩)
  choose c hc using fun i => Submodule.Quotient.mk_surjective _ (Y (Submodule.Quotient.mk ⟨b i, hbA i⟩))
  let D : V →ₗ[K] V := b.constr K fun i => (c i : V)
  have hDb : ∀ i, D (b i) = c i := fun i => b.constr_basis K _ i
  have key : ∀ y ∈ Submodule.span (𝓞 K) (Set.range b), ∃ (hy : y ∈ locF 𝔭 A₀) (hD : D y ∈ locF 𝔭 A₀),
      Submodule.Quotient.mk (⟨D y, hD⟩ : ↥(locF 𝔭 A₀)) = Y (Submodule.Quotient.mk ⟨y, hy⟩) := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      refine ⟨hbA i, by rw [hDb]; exact (c i).2, ?_⟩
      rw [← hc i]
      congr 1
      exact Subtype.ext (hDb i)
    | zero =>
      refine ⟨zero_mem _, by rw [map_zero]; exact zero_mem _, ?_⟩
      have e1 : (⟨D 0, by rw [map_zero]; exact zero_mem _⟩ : ↥(locF 𝔭 A₀)) = 0 := Subtype.ext (map_zero D)
      have e2 : (⟨0, zero_mem _⟩ : ↥(locF 𝔭 A₀)) = 0 := rfl
      rw [e1, e2, Submodule.Quotient.mk_zero, map_zero]
    | add y z _ _ h1 h2 =>
      obtain ⟨hy, hDy, e1⟩ := h1
      obtain ⟨hz, hDz, e2⟩ := h2
      refine ⟨add_mem hy hz, by rw [map_add]; exact add_mem hDy hDz, ?_⟩
      have e3 : (⟨D (y + z), by rw [map_add]; exact add_mem hDy hDz⟩ : ↥(locF 𝔭 A₀)) =
          ⟨D y, hDy⟩ + ⟨D z, hDz⟩ := Subtype.ext (map_add D y z)
      have e4 : (⟨y + z, add_mem hy hz⟩ : ↥(locF 𝔭 A₀)) = ⟨y, hy⟩ + ⟨z, hz⟩ := rfl
      rw [e3, e4, Submodule.Quotient.mk_add, Submodule.Quotient.mk_add, map_add, e1, e2]
    | smul a y _ h1 =>
      obtain ⟨hy, hDy, e1⟩ := h1
      have hs : D (a • y) = a • D y := LinearMap.map_smul_of_tower D a y
      refine ⟨Submodule.smul_mem _ a hy, by rw [hs]; exact Submodule.smul_mem _ a hDy, ?_⟩
      have e3 : (⟨D (a • y), by rw [hs]; exact Submodule.smul_mem _ a hDy⟩ : ↥(locF 𝔭 A₀)) =
          a • ⟨D y, hDy⟩ := Subtype.ext hs
      have e4 : (⟨a • y, Submodule.smul_mem _ a hy⟩ : ↥(locF 𝔭 A₀)) = a • ⟨y, hy⟩ := rfl
      rw [e3, e4, Submodule.Quotient.mk_smul, Submodule.Quotient.mk_smul, map_smul, e1]
  refine ⟨D, fun x => ?_⟩
  have hx : (x : V) ∈ locF 𝔭 (Submodule.span (𝓞 K) (Set.range b)) := by rw [hb]; exact x.2
  obtain ⟨t, ht, hxt⟩ := (LocalSpans.mem_locF 𝔭 _ _).1 hx
  obtain ⟨hy, hDy, e1⟩ := key _ hxt
  have hs : D (algebraMap (𝓞 F) (𝓞 K) t • (x : V)) = algebraMap (𝓞 F) (𝓞 K) t • D x :=
    LinearMap.map_smul_of_tower D _ _
  have hDx : D x ∈ locF 𝔭 A₀ := mem_locF_of_smul_mem h𝔭 A₀ ht (hs ▸ hDy)
  refine ⟨hDx, ?_⟩
  obtain ⟨w, hw⟩ := Submodule.Quotient.mk_surjective _ (Y (Submodule.Quotient.mk x))
  rw [← hw, Submodule.Quotient.eq, Submodule.mem_smul_top_iff]
  have e4 : (⟨algebraMap (𝓞 F) (𝓞 K) t • (x : V), hy⟩ : ↥(locF 𝔭 A₀)) = algebraMap (𝓞 F) (𝓞 K) t • x := rfl
  rw [e4, Submodule.Quotient.mk_smul, Y.map_smul, ← hw, ← Submodule.Quotient.mk_smul, Submodule.Quotient.eq,
    Submodule.mem_smul_top_iff] at e1
  refine mem_smul_of_smul_mem h𝔭 _ k ht (sub_mem hDx w.2) ?_
  have e5 : algebraMap (𝓞 F) (𝓞 K) t • (D x - (w : V)) =
      D (algebraMap (𝓞 F) (𝓞 K) t • (x : V)) - algebraMap (𝓞 F) (𝓞 K) t • (w : V) := by
    rw [hs, smul_sub]
  show algebraMap (𝓞 F) (𝓞 K) t • (D x - (w : V)) ∈ _
  rw [e5]
  exact e1

theorem exists_redEnd_eq (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {A₀ : Submodule (𝓞 K) V}
    (hA₀ : Submodule.IsLattice K A₀) (hA₀i : Formalism.HermitianLatticesTheory.IsIntegralLat h A₀) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {k : ℕ} (hk : eA h (locF 𝔭 A₀) 𝔭 + 1 ≤ k)
    (Y : Module.End (𝓞 K) (↥(locF 𝔭 A₀) ⧸ ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥(locF 𝔭 A₀))))
    (hY : ∀ x y x' y' : ↥(locF 𝔭 A₀), Submodule.Quotient.mk x' = Y (Submodule.Quotient.mk x) →
      Submodule.Quotient.mk y' = Y (Submodule.Quotient.mk y) →
      CongrP 𝔭 k (h (x' : V) (y' : V)) (h (x : V) (y : V))) :
    ∃ (X : V ≃ₗ[K] V) (hX : X ∈ sSub h (locF 𝔭 A₀) 𝔭 k), redEnd (locF 𝔭 A₀) 𝔭 k X hX.1 = Y := by
  obtain ⟨g, hg, hgY⟩ := exists_isom_lift hK hF hs hd hA₀ hA₀i h𝔭 hk Y hY
  have hgA : g ∈ glSub (locF 𝔭 A₀) := hg.2
  obtain ⟨D, hD⟩ := exists_lift hA₀ h𝔭 k Y
  have hle : extP K 𝔭 ^ (k - eA h (locF 𝔭 A₀) 𝔭) • locF 𝔭 A₀ ≤ extP K 𝔭 • locF 𝔭 A₀ :=
    Submodule.smul_mono_left (Ideal.pow_le_self (by omega))
  let E : V →ₗ[K] V := (g⁻¹ : V ≃ₗ[K] V).toLinearMap ∘ₗ D - LinearMap.id
  have hE : E ∈ endL (locF 𝔭 A₀) (extP K 𝔭 • locF 𝔭 A₀) := by
    intro x hx
    obtain ⟨hDx, h1⟩ := hD ⟨x, hx⟩
    have h2 := apply_mem_smul (inv_mem hgA) _ (hle (hgY ⟨x, hx⟩ ⟨D x, hDx⟩ h1))
    have h3 := neg_mem h2
    have e3 : E x = -(g⁻¹ (g x - D x)) := by
      simp [E]
    rw [e3]
    exact h3
  obtain ⟨Z, hZ, hZA⟩ := exists_equiv_of_mem_endL hA₀ h𝔭 hE
  have hXD : ∀ x, (g * Z) x = D x := fun x => by
    rw [LinearEquiv.mul_apply, hZ]
    simp [E]
  have hXA : g * Z ∈ glSub (locF 𝔭 A₀) := mul_mem hgA hZA
  have hmk : ∀ x : ↥(locF 𝔭 A₀), Submodule.Quotient.mk (⟨(g * Z) x, apply_mem hXA x.2⟩ : ↥(locF 𝔭 A₀)) =
      Y (Submodule.Quotient.mk x) := fun x => by
    obtain ⟨hDx, h1⟩ := hD x
    rw [← h1]
    congr 1
    exact Subtype.ext (hXD x)
  refine ⟨g * Z, ⟨hXA, fun x hx y hy => ?_⟩, ?_⟩
  · exact (congrP_algebraMap_iff_sub_mem h𝔭).1 (hY ⟨x, hx⟩ ⟨y, hy⟩ _ _ (hmk ⟨x, hx⟩) (hmk ⟨y, hy⟩))
  · refine LinearMap.ext fun q => ?_
    induction q using Submodule.Quotient.induction_on with | _ x => ?_
    rw [redEnd_mk]
    exact hmk x

end RedC

theorem alphaL_eq (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {A₀ : Submodule (𝓞 K) V}
    (hA₀ : Submodule.IsLattice K A₀) (hA₀i : Formalism.HermitianLatticesTheory.IsIntegralLat h A₀) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) :
    ∃ k₀ : ℕ, ∀ k ≥ k₀, alphaL h (locF 𝔭 A₀) 𝔭 =
      (akCount h (locF 𝔭 A₀) 𝔭 k : ℝ) / (Ideal.absNorm 𝔭 : ℝ) ^ (k * finrank K V ^ 2) := by
  refine ⟨2 * vd h A₀ 𝔭 + 1, fun k hk => ?_⟩
  have h1 : alphaL h (locF 𝔭 A₀) 𝔭 = alphaL h A₀ 𝔭 := by
    unfold alphaL
    simp_rw [akCount_locF hF h A₀ 𝔭 h𝔭]
  rw [h1, akCount_locF hF h A₀ 𝔭 h𝔭]
  exact firstFamilyOperatorEnd.alphaL_eq hK hF hs hd hA₀ hA₀i h𝔭 hk

theorem akCount_eq_relIndex (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {A₀ : Submodule (𝓞 K) V}
    (hA₀ : Submodule.IsLattice K A₀) (hA₀i : Formalism.HermitianLatticesTheory.IsIntegralLat h A₀) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) :
    ∃ k₀ : ℕ, ∀ k ≥ k₀, akCount h (locF 𝔭 A₀) 𝔭 k =
      (nSub (locF 𝔭 A₀) 𝔭 k).relIndex (sSub h (locF 𝔭 A₀) 𝔭 k) := by
  refine ⟨eA h (locF 𝔭 A₀) 𝔭 + 1, fun k hk => ?_⟩
  symm
  unfold akCount Subgroup.relIndex
  refine RedC.index_eq_card _
    (fun X : ↥(sSub h (locF 𝔭 A₀) 𝔭 k) => ⟨RedC.redEnd (locF 𝔭 A₀) 𝔭 k X.1 X.2.1,
      RedC.redEnd_cond hF hA₀i h𝔭 X.2⟩) ?_ ?_
  · rintro ⟨Y, hY⟩
    obtain ⟨X, hX, e⟩ := RedC.exists_redEnd_eq hK hF hs hd hA₀ hA₀i h𝔭 hk Y hY
    exact ⟨⟨X, hX⟩, Subtype.ext e⟩
  · intro a b
    rw [Subtype.mk.injEq, RedC.redEnd_eq_iff, Subgroup.mem_subgroupOf]
    rfl

end Formalism.HermitianLattices.Ext.L3.D2
