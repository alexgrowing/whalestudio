import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TriModOfBlockTriangular
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TriangularModulusInverseStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TridiagonalModuleLocalGeneratorsStatement
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.TrivFlag GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.TrueCx GlobalTheory.ConstLat GlobalTheory.LatChain Filter Topology
open scoped Classical

namespace GlobalTheory.LatChain

theorem gens_change {K : Type} [Field K] {N : ℕ} {R : Subring K} {γ b : K} {A B : Matrix (Fin N) (Fin N) K} {d : Fin N → K}
    (j : Fin N) (hγ : γ ∈ R) (hb : b ∈ R) (hs : Small R (γ * b)) (hA : Fr R A) (hB : Fr R B)
    (H : TriMod R (γ * b) (A⁻¹ * B) d) :
    (∀ i s, Lc R (gens γ (fun l => A⁻¹ l j) i) (gens γ (fun l => B⁻¹ l j) i s) ∧
      Lc R (gens γ (fun l => B⁻¹ l j) i) (gens γ (fun l => A⁻¹ l j) i s)) ∧
    ∀ i : Fin N, (d i ≠ 0 ∧ d i ∈ R ∧ (d i)⁻¹ ∈ R) ∧
      Lc R (gens γ (fun l => B⁻¹ l j) i.succ) (A⁻¹ i j - d i * B⁻¹ i j) := by
  have hT : Fr R (A⁻¹ * B) := hA.inv.mul hB
  obtain ⟨h0, H'⟩ := GlobalTheory.T.triangular_modulus_inverse K N R (γ * b) 1 (A⁻¹ * B) d hs R.one_mem hT.1 (by rw [one_smul]; exact hT.2.2)
    (by rw [mul_one, mul_one]; exact H)
  have e₁ : (A⁻¹ * B).mulVec (fun l => B⁻¹ l j) = fun l => A⁻¹ l j := by
    have : A⁻¹ * B * B⁻¹ = A⁻¹ := by rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hB.1.isUnit, Matrix.mul_one]
    funext l
    conv_rhs => rw [← this]
    rfl
  have e₂ : (A⁻¹ * B)⁻¹.mulVec (fun l => A⁻¹ l j) = fun l => B⁻¹ l j := by
    rw [← e₁, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hT.1.isUnit, Matrix.one_mulVec]
  obtain ⟨a₁, a₂⟩ := GlobalTheory.T.tridiagonal_module_local_generators K N R γ b (A⁻¹ * B) d (fun l => B⁻¹ l j) hγ hb hT.2.1 (fun l => hB.2.2 l j) H
  obtain ⟨b₁, b₂⟩ := GlobalTheory.T.tridiagonal_module_local_generators K N R γ b (A⁻¹ * B)⁻¹ _ (fun l => A⁻¹ l j) hγ hb hT.2.2 (fun l => hA.2.2 l j) H'
  rw [e₁] at a₁ a₂
  rw [e₂] at b₂
  exact ⟨fun i s => ⟨b₂ i s, a₂ i s⟩, fun i => ⟨⟨h0 i, (a₁ i).1, (b₁ i).1⟩, (a₁ i).2⟩⟩

theorem coh_gens : ∀ (X : Scheme.{0}) [IsIntegral X] (p k a N : ℕ) (M : X → Matrix (Fin N) (Fin N) X.functionField) (c : X → Fin N → X.functionFieldˣ) (j : Fin N) (γ : X.functionField), γ ≠ 0 → (∀ x, Ov p x → RegAt x γ ∧ RegAt x ((p : X.functionField) ^ a / γ)) → Coh p (k + 1 + a) M c → ∀ x, Ov p x → ∀ᶠ z in 𝓝 x, Ov p z → (∀ i s, Lc (loc z) (gens γ (fun l => (M x)⁻¹ l j) i) (gens γ (fun l => (M z)⁻¹ l j) i s) ∧ Lc (loc z) (gens γ (fun l => (M z)⁻¹ l j) i) (gens γ (fun l => (M x)⁻¹ l j) i s)) ∧ ∀ i : Fin N, UnitAt z ((c x i : X.functionField) / c z i) ∧ Lc (loc z) (gens γ (fun l => (M z)⁻¹ l j) i.succ) ((M x)⁻¹ i j - (c x i : X.functionField) / c z i * (M z)⁻¹ i j) := by
  intro X _ p k a N M c j γ hγ hreg hc x hx
  obtain ⟨h₁, h₂⟩ := hc x hx
  filter_upwards [h₁.eventually, h₂] with z hz hz' hp
  have e : (p : X.functionField) ^ (k + 1 + a) = γ * ((p : X.functionField) ^ (k + 1) * ((p : X.functionField) ^ a / γ)) := by
    rw [pow_add]; field_simp
  have hb : (p : X.functionField) ^ (k + 1) * ((p : X.functionField) ^ a / γ) ∈ loc z :=
    mul_mem (pow_mem (natCast_mem _ p) _) (hreg z hp).2
  have hs : Small (loc z) ((p : X.functionField) ^ (k + 1 + a)) := by
    rw [show k + 1 + a = k + a + 1 by ring]; exact small_pow hp _
  have H := hz' hp
  rw [e] at hs H
  obtain ⟨r₁, r₂⟩ := gens_change j (hreg z hp).1 hb hs hz (hc z hp).1 H
  exact ⟨r₁, fun i => ⟨(unitAt_iff (r₂ i).1.1).2 (r₂ i).1.2, (r₂ i).2⟩⟩

end GlobalTheory.LatChain
