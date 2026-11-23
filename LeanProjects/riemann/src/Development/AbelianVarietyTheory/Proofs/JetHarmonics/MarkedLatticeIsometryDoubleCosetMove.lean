import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FormPlus
import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameUniformEmbeddingSecond
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi
open scoped TensorProduct
open GlobalTheory.ShortMove

namespace GlobalTheory.ShortMoveIso

open scoped Matrix

theorem transport {G A : Type} [Group G] [CommRing A] {n : ℕ} (f : G →* GL (Fin n) A)
    (Lh : G → AddSubgroup (Fin n → A)) (hL : ∀ g z, z ∈ Lh g ↔ ∃ y ∈ Lh 1, (f g).1 *ᵥ y = z) (N : ℕ) (δ u k : G)
    (hk : Lh k = Lh 1) :
    (∀ z, z ∈ Lh u ↔ (f δ).1 *ᵥ z ∈ Lh (δ * u * k)) ∧
      ∀ x x' a b, (∃ w ∈ Lh 1, (f k).1 *ᵥ a = b + N • w) → (∃ w ∈ Lh u, x - (f u).1 *ᵥ b = N • w) →
        (∃ w ∈ Lh (δ * u * k), x' - (f (δ * u * k)).1 *ᵥ a = N • w) →
        ∃ w ∈ Lh (δ * u * k), (f δ).1 *ᵥ x - x' = N • w := by
  have hmul : ∀ (a b : G) z, (f (a * b)).1 *ᵥ z = (f a).1 *ᵥ ((f b).1 *ᵥ z) := by
    intro a b z
    rw [map_mul, Units.val_mul, Matrix.mulVec_mulVec]
  have hone : ∀ z, (f 1).1 *ᵥ z = z := by
    intro z
    rw [map_one, Units.val_one, Matrix.one_mulVec]
  have h1 : ∀ z, z ∈ Lh u ↔ (f δ).1 *ᵥ z ∈ Lh (δ * u * k) := by
    intro z
    rw [hL u, hL (δ * u * k)]
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨w, hw, rfl⟩ := (hL k y).1 (hk ▸ hy)
      exact ⟨w, hw, by rw [hmul, hmul]⟩
    · rintro ⟨y, hy, h⟩
      refine ⟨(f k).1 *ᵥ y, hk ▸ (hL k _).2 ⟨y, hy, rfl⟩, ?_⟩
      have := congrArg (fun v => (f δ⁻¹).1 *ᵥ v) h
      simp only [← hmul, inv_mul_cancel, hone] at this
      rw [← this, ← hmul, mul_assoc, inv_mul_cancel_left]
  refine ⟨h1, ?_⟩
  rintro x x' a b ⟨y, hy, ey⟩ ⟨w, hw, e⟩ ⟨w', hw', e'⟩
  refine ⟨(f δ).1 *ᵥ w - (f δ).1 *ᵥ ((f u).1 *ᵥ y) - w',
    sub_mem (sub_mem ((h1 w).1 hw) ((h1 _).1 ((hL u _).2 ⟨y, hy, rfl⟩))) hw', ?_⟩
  rw [sub_eq_iff_eq_add.1 e, sub_eq_iff_eq_add.1 e', hmul, hmul, ey]
  simp only [Matrix.mulVec_add, Matrix.mulVec_smul, smul_sub]
  abel

theorem map_mem_half {R A : Type} [CommRing R] [AddCommGroup A] [Module R A] (I : Ideal R) (s : A →ₗ[R] A) :
    ∀ a ∈ I • (⊤ : Submodule R A), s a ∈ I • (⊤ : Submodule R A) := by
  intro a ha
  refine Submodule.smul_induction_on ha (fun m hm b _ => ?_) (fun x y hx hy => ?_)
  · rw [map_smul]
    exact Submodule.smul_mem_smul hm trivial
  · rw [map_add]
    exact add_mem hx hy

set_option maxHeartbeats 1000000 in

theorem marked_isometry : ∀ (D : D7) (V : HSp D) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (r : ℕ) (hr : V.rank = r) (io : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)) (X X' : Data D.host.E r) (A A' : Datum H) (φ : A.La ≃ₗ[𝓞 D.host.E] X.Λ) (φ' : A'.La ≃ₗ[𝓞 D.host.E] X'.Λ) (t : Dw.La →ₗ[𝓞 D.host.E] A.La) (t' : Dw.La →ₗ[𝓞 D.host.E] A'.La) (s : Dw.La →ₗ[𝓞 D.host.E] Dw.La) (h γ κ : GA D V), ModelW V hr X → ModelW V hr X' → (∀ a b, ((A.EF a b : ℤ) : ℚ) = Algebra.trace ℚ D.host.E (-X.ξ0 * herm X.Gm (φ a : Fin r → D.host.E) (φ b))) → (∀ a b, ((A'.EF a b : ℤ) : ℚ) = Algebra.trace ℚ D.host.E (-X'.ξ0 * herm X'.Gm (φ' a : Fin r → D.host.E) (φ' b))) → γ ∈ GQ V → latGHat V κ = latGHat V 1 → (∀ a, ∃ w ∈ latGHat V 1, (finHom V κ).1.mulVec (finVec V (io a)) = finVec V (io (s a)) + l.M • w) → Marked V hr io l X.Λ (fun a => (φ (t a) : Fin r → D.host.E)) h → Marked V hr io l X'.Λ (fun a => (φ' (t' a) : Fin r → D.host.E)) (γ * h * κ) → ∃ gam : A.La ≃ₗ[𝓞 D.host.E] A'.La, (∀ a b, A'.EF (gam a) (gam b) = A.EF a b) ∧ ∀ a ∈ Mfr l • (⊤ : Submodule (𝓞 D.host.E) Dw.La), ∃ x, gam (t (s a)) = t' a + l.M • x := by
  intro D V H Dw l r hr io X X' A A' φ φ' t t' s h γ κ hW hW' hE hE' hγ hκ hs hm hm'
  subst hr
  obtain ⟨hΛ, hm⟩ := hm
  obtain ⟨hΛ', hm'⟩ := hm'
  obtain ⟨δ, hδu, hδf, -⟩ := GlobalTheory.MarkCoset.rational_matrix V γ hγ
  obtain ⟨ht1, ht2⟩ := transport (finHom V) (latGHat V) (fun g => (GlobalTheory.MarkCoset.latG_spec D V g).2) l.M γ h κ hκ
  have hmem : ∀ v, v ∈ X.Λ ↔ finVec V v ∈ latGHat V h := fun v => by
    rw [← (GlobalTheory.MarkCoset.latG_spec D V h).1, ← SetLike.mem_coe, hΛ]
    exact Set.ext_iff.1 (Set.image_id _) v
  have hmem' : ∀ v, v ∈ X'.Λ ↔ finVec V v ∈ latGHat V (γ * h * κ) := fun v => by
    rw [← (GlobalTheory.MarkCoset.latG_spec D V _).1, ← SetLike.mem_coe, hΛ']
    exact Set.ext_iff.1 (Set.image_id _) v
  have hlat : ∀ v, v ∈ X.Λ ↔ δ.1 *ᵥ v ∈ X'.Λ := fun v => by
    rw [hmem, hmem', ht1, hδf]
  have hM0 : l.M ≠ 0 := by have := l.three_le; omega
  have hri : ∀ v, δ.1 *ᵥ ((δ⁻¹).1 *ᵥ v) = v :=
    fun v => by rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  have hli : ∀ v, (δ⁻¹).1 *ᵥ (δ.1 *ᵥ v) = v :=
    fun v => by rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
  let ψ : X.Λ ≃ₗ[𝓞 D.host.E] X'.Λ :=
    { toFun := fun v => ⟨δ.1 *ᵥ v.1, (hlat _).1 v.2⟩
      invFun := fun v => ⟨(δ⁻¹).1 *ᵥ v.1, (hlat _).2 (by rw [hri]; exact v.2)⟩
      map_add' := fun u v => Subtype.ext (Matrix.mulVec_add δ.1 u.1 v.1)
      map_smul' := fun a v => Subtype.ext (Matrix.mulVec_smul δ.1 a v.1)
      left_inv := fun v => Subtype.ext (hli _)
      right_inv := fun v => Subtype.ext (hri _) }
  let gam : A.La ≃ₗ[𝓞 D.host.E] A'.La := φ.trans (ψ.trans φ'.symm)
  have hgam : ∀ a, (φ' (gam a) : Fin V.rank → D.host.E) = δ.1 *ᵥ (φ a : Fin V.rank → D.host.E) := by
    intro a
    simp [gam, ψ]
  have hG : X.Gm = -V.gram.transpose := hW.1
  have hG' : X'.Gm = -V.gram.transpose := hW'.1
  have hξ : X'.ξ0 = X.ξ0 := hW'.2.trans hW.2.symm
  refine ⟨gam, fun a b => ?_, fun a ha => ?_⟩
  · have h1 := hE' (gam a) (gam b)
    rw [hgam, hgam, hG', hξ, hδu, ← hG, ← hE a b] at h1
    exact_mod_cast h1
  · obtain ⟨z, hz, e⟩ := ht2 (finVec V (φ (t (s a)) : Fin V.rank → D.host.E))
      (finVec V (φ' (t' a) : Fin V.rank → D.host.E)) _ _ (hs a) (hm _ (map_mem_half _ s a ha)) (hm' a ha)
    obtain ⟨w, hw, e'⟩ := GlobalTheory.MarkCoset.finVec_div V l.M hM0 (δ.1 *ᵥ (φ (t (s a)) : Fin V.rank → D.host.E) -
      (φ' (t' a) : Fin V.rank → D.host.E)) z (by
        rw [← e, hδf]
        funext i
        exact TensorProduct.tmul_sub _ _ _)
    refine ⟨φ'.symm ⟨w, (hmem' w).2 (hw ▸ hz)⟩, φ'.injective (Subtype.ext ?_)⟩
    rw [hgam, sub_eq_iff_eq_add'.1 e', map_add, map_nsmul, LinearEquiv.apply_symm_apply]
    rfl

end GlobalTheory.ShortMoveIso
