import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.DiagonalPullbacks.ProjectiveBundleFormulaTorsion
import Development.EtaleCohomology.EtaleTrace.FrobTraceOf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.EtaleTrace
open scoped TensorProduct

namespace UpperTheory.Gal.KunnethLefschetz.Di

variable {l : ℕ} [Fact l.Prime] {k : Type} [Field k]

private theorem pullback_exterior_product (hR : Ring l) {X P : Scheme.{0}} (p : X ⟶ S k) {p₁ p₂ : P ⟶ X} {φ : P ⟶ pullback p p}
    (h₁ : φ ≫ pullback.fst p p = p₁) (h₂ : φ ≫ pullback.snd p p = p₂) {a b w : ℤ} (h : a + b = w)
    (u : V l X a) (v : V l X b) :
    pb l φ w (ext2 l p h u v) = cupV l P h (pb l p₁ a u) (pb l p₂ b v) := by
  subst h₁ h₂
  rw [ext2, hR.nat, pb_comp, pb_comp]
  rfl

private theorem lift_gen (hR : Ring l) {X P : Scheme.{0}} (p : X ⟶ S k) {p₁ p₂ : P ⟶ X} {φ : P ⟶ pullback p p}
    (h₁ : φ ≫ pullback.fst p p = p₁) (h₂ : φ ≫ pullback.snd p p = p₂) (d : ℕ) {w : ℤ}
    (hw : w = ((2 + 2 * d : ℕ) : ℤ)) (c : ℚ_[l]) (x : V l (pullback p p) w)
    (hx : ∃ (n n' : ℤ) (h : n + n' = w) (u : V l X n) (v : V l X n'), 0 ≤ n ∧ 0 < n' ∧ x = ext2 l p h u v) :
    ∃ (i j : ℕ) (_ : i + j = 2 + 2 * d) (u : V l X i) (v : V l X j), j ≠ 0 ∧
      ∀ hh : (i : ℤ) + j = w, c • pb l φ w x = cupV l P hh (pb l p₁ _ u) (pb l p₂ _ v) := by
  obtain ⟨n, n', h, u, v, h0, h1, rfl⟩ := hx
  obtain ⟨i, rfl⟩ := Int.eq_ofNat_of_zero_le h0
  obtain ⟨j, rfl⟩ := Int.eq_ofNat_of_zero_le h1.le
  refine ⟨i, j, by omega, c • u, v, by omega, fun hh => ?_⟩
  rw [pullback_exterior_product hR p h₁ h₂, map_smul, map_smul, LinearMap.smul_apply]

private theorem core (hR : Ring l) (d : ℕ) {X P W : Scheme.{0}} (p : X ⟶ S k) {p₁ p₂ : P ⟶ X}
    {φ : P ⟶ pullback p p} (π : W ⟶ P) (h₁ : φ ≫ pullback.fst p p = p₁) (h₂ : φ ≫ pullback.snd p p = p₂)
    (e : V l W ((2 : ℕ) : ℤ)) {w w' : ℤ} (hw : w = ((2 + 2 * d : ℕ) : ℤ)) (hw' : w' = ((2 * d : ℕ) : ℤ))
    (h2 : ((2 : ℕ) : ℤ) + w' = w) (δ : V l (pullback p p) w) (m : V l W w') (s : ℕ) (a : Fin s → V l X w)
    (b : Fin s → V l X 0) (hδ : pb l (π ≫ φ) w δ = cupV l W h2 e m) (ha : LinearIndependent ℚ_[l] a)
    (hb : ∑ t, b t = oneV l X)
    (hs : δ - ∑ t, ext2 l p (add_zero _) (a t) (b t) ∈ Submodule.span ℚ_[l] {x : V l (pullback p p) w |
      ∃ (n n' : ℤ) (h : n + n' = w) (u : V l X n) (v : V l X n'), 0 ≤ n ∧ 0 < n' ∧ x = ext2 l p h u v}) :
    DiagQ l d p₁ p₂ π e := by
  subst hw hw'
  obtain ⟨t, f, g, hsum⟩ := Submodule.mem_span_set'.1 hs
  choose i j hij u v hj huv using fun c => lift_gen hR p h₁ h₂ d rfl (f c) (g c).1 (g c).2
  refine ⟨pb l φ _ δ, m, s, a, b, t, i, j, hij, u, v, ?_, ha, hb, hj, ?_⟩
  · exact (LinearMap.congr_fun (pb_comp l π φ _) δ).symm.trans hδ
  · have hδ' : δ = ∑ t, ext2 l p (add_zero _) (a t) (b t) + ∑ c, f c • (g c : V l (pullback p p) _) := by
      rw [hsum]; abel
    have e1 : pb l φ _ δ = ∑ t, pb l φ _ (ext2 l p (add_zero _) (a t) (b t)) +
        ∑ c, f c • pb l φ _ (g c : V l (pullback p p) _) := by
      rw [congrArg (pb l φ _) hδ']
      simp only [map_add, map_sum, map_smul]
    refine e1.trans (congrArg₂ (· + ·) (Finset.sum_congr rfl fun c _ => pullback_exterior_product hR p h₁ h₂ _ _ _)
      (Finset.sum_congr rfl fun c _ => huv c _))

theorem diagSq_holds : DiagSq := by
  intro hQ l _ k _ _ hl hR d X P p p₁ p₂ Δ h hΔ₁ hΔ₂ hSP hProj W E π i r c hsq hpair hr U hoff e he hpb
  have e₁ : h.isoPullback.hom ≫ pullback.fst p p = p₁ := h.isoPullback_hom_fst
  have e₂ : h.isoPullback.hom ≫ pullback.snd p p = p₂ := h.isoPullback_hom_snd
  have hdiag : Δ ≫ h.isoPullback.hom = pullback.diagonal p := by
    apply pullback.hom_ext
    · rw [Category.assoc, e₁, hΔ₁, pullback.diagonal_fst]
    · rw [Category.assoc, e₂, hΔ₂, pullback.diagonal_snd]
  have hsq' : IsPullback i r (π ≫ h.isoPullback.hom) (pullback.diagonal p) :=
    IsPullback.of_iso hsq (Iso.refl _) (Iso.refl _) (Iso.refl _) h.isoPullback (by simp) (by simp) (by simp)
      (by simp [hdiag])
  have hpair' : IsPair 1 c ((π ≫ h.isoPullback.hom) ≫ pullback.fst p p ≫ p) i := by
    have hc : (π ≫ h.isoPullback.hom) ≫ pullback.fst p p ≫ p = π ≫ p₁ ≫ p := by
      rw [Category.assoc, ← Category.assoc h.isoPullback.hom, e₁]
    rw [hc]
    exact hpair
  obtain ⟨δ, m, s, a, b, h1, h2, h3, h4⟩ :=
    hQ l k hl d p hSP hProj (π ≫ h.isoPullback.hom) i r c hsq' hpair' hr U hoff e he hpb
  exact core hR d p π e₁ e₂ e (by push_cast; rfl) (by push_cast; rfl) rfl δ m s a b h1 h2 h3 h4

end UpperTheory.Gal.KunnethLefschetz.Di
