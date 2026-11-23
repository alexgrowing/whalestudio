import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.BasisOne
import Development.EtaleCohomology.EtaleTrace.LPdCut

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.EtaleTrace
open scoped TensorProduct DirectSum

namespace UpperTheory.Gal.KunnethLefschetz

variable {l : ℕ} [Fact l.Prime] {k : Type} [Field k]

private theorem exterior_product_cup_snd (R : Ring l) {X : Scheme.{0}} (p : X ⟶ S k) {a b n m t w : ℤ}
    (h1 : a + b = m) (h2 : m + n = w) (h3 : b + n = t) (h4 : a + t = w)
    (u : V l X a) (v : V l X b) (x : V l X n) :
    cupV l _ h2 (ext2 l p h1 u v) (pb l (pullback.snd p p) n x) =
      ext2 l p h4 u (cupV l X h3 v x) := by
  simp only [ext2]
  rw [R.assoc _ a b n m t w h1 h2 h3 h4, ← R.nat (pullback.snd p p) b n t h3 v x]

private theorem cup_fst_exterior_product (R : Ring l) {X : Scheme.{0}} (p : X ⟶ S k) {a b n m t w : ℤ}
    (h1 : a + b = m) (h2 : n + m = w) (h3 : n + a = t) (h4 : t + b = w)
    (x : V l X n) (u : V l X a) (v : V l X b) :
    cupV l _ h2 (pb l (pullback.fst p p) n x) (ext2 l p h1 u v) =
      ext2 l p h4 (cupV l X h3 x u) v := by
  simp only [ext2]
  rw [← R.assoc _ n a b t m w h3 h4 h1 h2, ← R.nat (pullback.fst p p) n a t h3 x u]

private theorem int_cup_snd (R : Ring l) {d : ℕ} {X : Scheme.{0}} {p : X ⟶ S k} (K : Kun l k d p)
    {lam : V l X (2 * d) →ₗ[ℚ_[l]] ℚ_[l]} {n w : ℤ} (h : 2 * d + n = w)
    {Λ : V l (pullback p p) w →ₗ[ℚ_[l]] V l X n} (hΛ : IsInt l p lam h Λ)
    {Λ0 : V l (pullback p p) (2 * d) →ₗ[ℚ_[l]] V l X 0} (h0 : IsInt l p lam (add_zero _) Λ0)
    (x : V l X n) (y : V l (pullback p p) (2 * d)) :
    Λ (cupV l _ h y (pb l (pullback.snd p p) n x)) = cupV l X (zero_add n) (Λ0 y) x := by
  have key : Λ ∘ₗ (cupV l (pullback p p) h).flip (pb l (pullback.snd p p) n x) =
      ((cupV l X (zero_add n)).flip x) ∘ₗ Λ0 := by
    apply LinearMap.ext_on (K.span (2 * d))
    rintro _ ⟨a, b, hab, u, v, rfl⟩
    simp only [LinearMap.comp_apply, LinearMap.flip_apply]
    by_cases hb : b = 0
    · subst hb
      have ha : a = 2 * d := by omega
      subst ha
      rw [exterior_product_cup_snd R p hab h (zero_add n) h u v x, hΛ.1, h0.1, map_smul, LinearMap.smul_apply]
    · rw [exterior_product_cup_snd R p hab h rfl (by omega : a + (b + n) = w) u v x,
        hΛ.2 a (b + n) _ (by omega) u _, h0.2 a b hab hb u v, map_zero, LinearMap.zero_apply]
  exact LinearMap.congr_fun key y

private theorem int_fst_cup {d : ℕ} (R : Ring l) {X : Scheme.{0}} {p : X ⟶ S k}
    {lam : V l X (2 * d) →ₗ[ℚ_[l]] ℚ_[l]} {n w a b : ℤ} (h : 2 * d + n = w) (h2 : n + 2 * d = w)
    (h1 : a + b = 2 * d) {Λ : V l (pullback p p) w →ₗ[ℚ_[l]] V l X n} (hΛ : IsInt l p lam h Λ)
    (x : V l X n) (u : V l X a) (v : V l X b)
    (hx : ∀ hh : n + a = 2 * d, lam (cupV l X hh x u) = 0) :
    Λ (cupV l _ h2 (pb l (pullback.fst p p) n x) (ext2 l p h1 u v)) = 0 := by
  by_cases hb : b = n
  · subst b
    have ht : n + a = 2 * d := by omega
    rw [cup_fst_exterior_product R p h1 h2 ht h, hΛ.1, hx ht, zero_smul]
  · rw [cup_fst_exterior_product R p h1 h2 rfl (by omega : n + a + b = w)]
    exact hΛ.2 _ b _ hb _ _

theorem detectL_holds : DetectL := by
  intro l _ k _ _ hl d X p hSP R K lam δ hswap hΛ0
  obtain ⟨Λ0, h0⟩ := K.int lam 0 (2 * d) (add_zero _)
  have hone := hΛ0 Λ0 h0
  have hunit : IsUnit ((l : Γ(X, ⊤))) := by
    have h1 : IsUnit ((l : k)) := isUnit_iff_ne_zero.mpr hl
    have h2 := (h1.map (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom).map p.appTop.hom
    simpa [map_natCast] using h2
  have hδ : δ ∈ Submodule.span ℚ_[l]
      {w | ∃ a b, ∃ (h : a + b = 2 * (d : ℤ)), ∃ u v, w = ext2 l p h u v} := by
    rw [K.span]
    trivial
  obtain ⟨N, f, g, hsum⟩ := Submodule.mem_span_set'.mp hδ
  have hg : ∀ t, ∃ a b, ∃ h : a + b = 2 * (d : ℤ), ∃ u v, (g t : V l (pullback p p) (2 * d)) = ext2 l p h u v :=
    fun t => (g t).2
  choose A B hAB U W hUW using hg
  refine ⟨N, A, U, fun n x hx => ?_⟩
  obtain ⟨Λ, hΛ⟩ := K.int lam n (2 * d + n) rfl
  calc x = cupV l X (zero_add n) (oneV l X) x := (R.one_mul X hunit n x).symm
    _ = cupV l X (zero_add n) (Λ0 δ) x := by rw [hone]
    _ = Λ (cupV l _ (rfl : 2 * (d : ℤ) + n = 2 * d + n) δ (pb l (pullback.snd p p) n x)) :=
        (int_cup_snd R K rfl hΛ h0 x δ).symm
    _ = Λ (cupV l _ (by ring : n + 2 * (d : ℤ) = 2 * d + n) (pb l (pullback.fst p p) n x) δ) := by
        rw [hswap n _ (by ring) rfl x]
    _ = 0 := by
        rw [← hsum, map_sum, map_sum]
        apply Finset.sum_eq_zero
        intro t _
        rw [map_smul, map_smul, hUW t,
          int_fst_cup R rfl (by ring) (hAB t) hΛ x (U t) (W t) (hx t), smul_zero]

end UpperTheory.Gal.KunnethLefschetz
