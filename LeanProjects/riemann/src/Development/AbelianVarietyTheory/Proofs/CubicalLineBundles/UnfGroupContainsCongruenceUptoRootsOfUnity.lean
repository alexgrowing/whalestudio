import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.UnFree
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CongruenceActionMemFrameOrbit
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsSmulOfPreservesFrameOrbits
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj
open scoped Matrix

namespace GlobalTheory

open NumberField in
open scoped Matrix in
private lemma isUStab_one_cubical_line_bundles {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E] {r : ℕ}
    {G : Matrix (Fin r) (Fin r) E} {L : Submodule (NumberField.RingOfIntegers E) (Fin r → E)} :
    _root_.ReciprocityTheory.ChartRestriction.G.FD.IsUStab G L (1 : GL (Fin r) E) := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.IsUStab
  simp

open NumberField in
open scoped Matrix in
private lemma isUStab_mul_cubical_line_bundles {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E] {r : ℕ}
    {G : Matrix (Fin r) (Fin r) E} {L : Submodule (NumberField.RingOfIntegers E) (Fin r → E)}
    {g h : GL (Fin r) E} (hg : _root_.ReciprocityTheory.ChartRestriction.G.FD.IsUStab G L g) (hh : _root_.ReciprocityTheory.ChartRestriction.G.FD.IsUStab G L h) : _root_.ReciprocityTheory.ChartRestriction.G.FD.IsUStab G L (g * h) := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.IsUStab at *
  refine ⟨fun x y => ?_, fun x => ?_⟩
  · rw [Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hg.1, hh.1]
  · rw [Units.val_mul, ← Matrix.mulVec_mulVec]
    exact (hh.2 x).trans (hg.2 _)

open NumberField in
open scoped Matrix in
private lemma isUStab_pow' {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E] {r : ℕ}
    {G : Matrix (Fin r) (Fin r) E} {L : Submodule (NumberField.RingOfIntegers E) (Fin r → E)}
    {g : GL (Fin r) E} (hg : _root_.ReciprocityTheory.ChartRestriction.G.FD.IsUStab G L g) (n : ℕ) : _root_.ReciprocityTheory.ChartRestriction.G.FD.IsUStab G L (g ^ n) := by
  induction n with
  | zero => simpa using isUStab_one_cubical_line_bundles
  | succ n ih => rw [pow_succ]; exact isUStab_mul_cubical_line_bundles ih hg

open NumberField in
open scoped Matrix in

theorem _root_.GlobalTheory.unf_group_contains_congruence_upto_rootsOfUnity : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (l : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l) (c : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : _root_.Formalism.L2.PjFree.Unf Xo c σ r), _root_.Formalism.L2.PjFree.IsUnf U → l.A = 1 → 0 < r → ∀ k (γ : GL (Fin r) E), _root_.ReciprocityTheory.ChartRestriction.G.FD.IsUStab (U.X k).Gm (U.X k).Λ γ → (∀ x ∈ (U.X k).Λ, ∃ y ∈ (U.X k).Λ, Matrix.mulVec (γ : Matrix (Fin r) (Fin r) E) x - x = (l.M : E) • y) → ∃ γ' ∈ (U.X k).Γ, ∃ (u : E) (n : ℕ), 0 < n ∧ u ^ n = 1 ∧ (γ' : Matrix (Fin r) (Fin r) E) = u • (γ : Matrix (Fin r) (Fin r) E) := by
  intro E _ _ _ H Dw l Xo c σ r U hU hA hr k γ hγ hcong
  obtain ⟨γ', hγ'Γ, u, hu⟩ := _root_.GlobalTheory.OrbitScalar.exists_smul_of_orbits E r (U.X k) γ
    (_root_.GlobalTheory.congr_lact_mem_orbit E H Dw l Xo c σ r U hU hA k γ hγ hcong)
  have hu0 : u ≠ 0 := by
    rintro rfl
    have h1 := congrArg (fun M : Matrix (Fin r) (Fin r) E => M ⟨0, hr⟩ ⟨0, hr⟩) γ'.mul_inv
    simp [hu] at h1
  let cu : GL (Fin r) E :=
    Units.map (algebraMap E (Matrix (Fin r) (Fin r) E)).toMonoidHom (Units.mk0 u hu0)
  have hcu : (cu : Matrix (Fin r) (Fin r) E) = u • 1 := by
    simp [cu, Algebra.algebraMap_eq_smul_one]
  have hcomm : ∀ g : GL (Fin r) E, cu * g = g * cu := fun g =>
    Units.ext (by simp [hcu, Matrix.smul_mul, Matrix.mul_smul])
  have hγ' : γ' = cu * γ := Units.ext (by rw [hu, Units.val_mul, hcu, Matrix.smul_mul, one_mul])
  obtain ⟨S, hS⟩ := (U.X k).Γ_index
  have hpow : ∀ j : ℕ, ∃ s ∈ S, s⁻¹ * γ ^ j ∈ (U.X k).Γ := fun j => hS _ (isUStab_pow' hγ j)
  choose f hfS hfΓ using hpow
  have hmem : ∀ j, cu ^ j * f j ∈ (U.X k).Γ := by
    intro j
    have h := (U.X k).Γ.mul_mem ((U.X k).Γ.pow_mem hγ'Γ j) ((U.X k).Γ.inv_mem (hfΓ j))
    have e : γ' ^ j * ((f j)⁻¹ * γ ^ j)⁻¹ = cu ^ j * f j := by
      rw [hγ', (show Commute cu γ from hcomm γ).mul_pow, mul_inv_rev, inv_inv, mul_assoc,
        mul_inv_cancel_left]
    exact e ▸ h
  have key : ∀ a b : ℕ, a < b → f a = f b → ∃ γ' ∈ (U.X k).Γ, ∃ (u : E) (n : ℕ), 0 < n ∧
      u ^ n = 1 ∧ (γ' : Matrix (Fin r) (Fin r) E) = u • (γ : Matrix (Fin r) (Fin r) E) := by
    intro a b hab heq
    have hm : cu ^ (b - a) ∈ (U.X k).Γ := by
      have h := (U.X k).Γ.mul_mem (hmem b) ((U.X k).Γ.inv_mem (hmem a))
      rwa [heq, mul_inv_rev, mul_assoc, mul_inv_cancel_left, ← pow_sub cu hab.le] at h
    have hcm : ((cu ^ (b - a) : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) = u ^ (b - a) • 1 := by
      rw [Units.val_pow_eq_pow_val, hcu, smul_pow, one_pow]
    have h1 : cu ^ (b - a) = 1 := by
      obtain ⟨x, hx⟩ := _root_.GlobalTheory.OrbitScalar.exists_mem_dom (U.X k)
      let β : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame (U.X k).Ψ r := fun τ =>
        (((τ : E →+* ℂ) (u ^ (b - a))) • (1 : Matrix (Fin r) (Fin r) ℂ))
      have hβ : ∀ τ, _root_.ReciprocityTheory.ChartRestriction.G.FD.mat β τ = ((τ : E →+* ℂ) (u ^ (b - a))) • (1 : Matrix (Fin r) (Fin r) ℂ) := by
        intro τ
        rfl
      refine (U.X k).Γ_free _ hm x hx β ?_ ?_
      · unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.Bor
        intro τ
        refine ⟨?_, fun p q hpq => ?_⟩
        · rw [hβ, Matrix.det_smul, Matrix.det_one, mul_one]
          exact pow_ne_zero _ ((map_ne_zero _).2 (pow_ne_zero _ hu0))
        · simp [β, Matrix.one_apply, (ne_of_gt hpq)]
      · unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.lact _root_.ReciprocityTheory.ChartRestriction.G.FD.rmul
        funext τ
        rw [hβ, hcm]
        ext p q
        simp [Matrix.mul_apply, Matrix.one_apply, apply_ite, mul_comm]
    have hn : u ^ (b - a) = 1 := by
      have h2 := congrArg (fun g : GL (Fin r) E => (g : Matrix (Fin r) (Fin r) E) ⟨0, hr⟩ ⟨0, hr⟩) h1
      simpa [hcm] using h2
    exact ⟨γ', hγ'Γ, u, b - a, Nat.sub_pos_of_lt hab, hn, hu⟩
  obtain ⟨i, j, hij, hfij⟩ :=
    Finite.exists_ne_map_eq_of_infinite (fun j : ℕ => (⟨f j, hfS j⟩ : S))
  have hfij' : f i = f j := congrArg Subtype.val hfij
  rcases lt_or_gt_of_ne hij with h | h
  · exact key i j h hfij'
  · exact key j i h hfij'.symm

end GlobalTheory
