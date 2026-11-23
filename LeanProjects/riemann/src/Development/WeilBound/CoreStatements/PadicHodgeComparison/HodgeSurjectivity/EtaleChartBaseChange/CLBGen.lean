import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.FormLaws
set_option linter.style.haveILetI false

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace CrystallineSemistableComparison.Onto.CLB

theorem etale_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C)
    (hf : f.Etale) (hg : g.Etale) : (g.comp f).Etale :=
  RingHom.Etale.stableUnderComposition f g hf hg

theorem etale_reindex {K B σ τ : Type} [CommRing K] [CommRing B] (s : K →+* B) (y : σ → B) (e : τ ≃ σ)
    (h : (MvPolynomial.eval₂Hom s y : MvPolynomial σ K →+* B).Etale) :
    (MvPolynomial.eval₂Hom s (y ∘ e) : MvPolynomial τ K →+* B).Etale := by
  have heq : (MvPolynomial.eval₂Hom s (y ∘ e) : MvPolynomial τ K →+* B) =
      (MvPolynomial.eval₂Hom s y).comp (MvPolynomial.rename (R := K) e).toRingHom :=
    RingHom.ext fun p => (MvPolynomial.eval₂Hom_rename s e y p).symm
  rw [heq]
  exact etale_comp _ _ (RingHom.Etale.of_bijective (MvPolynomial.renameEquiv K e).bijective) h

theorem coord_nzd {K B σ : Type} [Field K] [CommRing B] [Algebra K B] (y : σ → B)
    (h : (MvPolynomial.eval₂Hom (algebraMap K B) y : MvPolynomial σ K →+* B).Etale) (j : σ) :
    ∀ (a : ℕ) (ω : Om K B a), y j • ω = 0 → ω = 0 := by
  intro a ω hω
  letI : Algebra (MvPolynomial σ K) B := (MvPolynomial.eval₂Hom (algebraMap K B) y).toAlgebra
  haveI : Algebra.Etale (MvPolynomial σ K) B := h.toAlgebra
  haveI : IsScalarTower K (MvPolynomial σ K) B := IsScalarTower.of_algebraMap_eq fun r => by
    change _ = MvPolynomial.eval₂Hom (algebraMap K B) y (MvPolynomial.C r)
    simp
  haveI : Module.Free (MvPolynomial σ K) Ω[MvPolynomial σ K⁄K] :=
    Module.Free.of_basis (KaehlerDifferential.mvPolynomialBasis K σ)
  haveI : Module.Free B Ω[B⁄K] :=
    Module.Free.of_equiv (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale K (MvPolynomial σ K) B)
  have hX : IsSMulRegular (MvPolynomial σ K) (MvPolynomial.X j : MvPolynomial σ K) :=
    (MvPolynomial.isRegular_X (R := K) (n := j)).left
  have hB : IsSMulRegular B (algebraMap (MvPolynomial σ K) B (MvPolynomial.X j)) := IsSMulRegular.of_flat hX
  have hy : algebraMap (MvPolynomial σ K) B (MvPolynomial.X j) = y j := by
    change MvPolynomial.eval₂Hom (algebraMap K B) y (MvPolynomial.X j) = y j
    simp
  rw [hy] at hB
  have hmem : y j ∈ nonZeroDivisors B := by
    rw [mem_nonZeroDivisors_iff_right]
    intro z hz
    exact hB (by simpa [smul_eq_mul, mul_comm] using hz)
  exact Module.Flat.isSMulRegular_of_nonZeroDivisors hmem (show y j • ω = y j • (0 : Om K B a) by rw [hω, smul_zero])

theorem quot_etale {K B C σ : Type} [CommRing K] [CommRing B] [CommRing C] (s : K →+* B) (y : σ → B) (j0 : σ)
    (h : (MvPolynomial.eval₂Hom s y : MvPolynomial σ K →+* B).Etale) (ψ : B →+* C) (hψ : Function.Surjective ψ)
    (hk : RingHom.ker ψ = Ideal.span {y j0}) :
    (MvPolynomial.eval₂Hom (ψ.comp s) (fun j : {j // j ≠ j0} => ψ (y j)) : MvPolynomial {j // j ≠ j0} K →+* C).Etale := by
  classical
  let f : MvPolynomial σ K →+* B := MvPolynomial.eval₂Hom s y
  let g : MvPolynomial σ K →+* MvPolynomial {j // j ≠ j0} K :=
    MvPolynomial.eval₂Hom MvPolynomial.C (fun j => if hj : j = j0 then 0 else MvPolynomial.X ⟨j, hj⟩)
  let e : MvPolynomial {j // j ≠ j0} K →+* C := MvPolynomial.eval₂Hom (ψ.comp s) (fun j => ψ (y j))
  have hy0 : ψ (y j0) = 0 := by
    rw [← RingHom.mem_ker, hk]; exact Ideal.subset_span rfl
  have heg : e.comp g = ψ.comp f := by
    apply MvPolynomial.ringHom_ext
    · intro r; simp [e, g, f]
    · intro j
      by_cases hj : j = j0
      · subst hj; simp [e, g, f, hy0]
      · simp [e, g, f, hj]
  have hg : Function.Surjective g := by
    have hid : g.comp (MvPolynomial.rename (R := K) (Subtype.val : {j // j ≠ j0} → σ)).toRingHom = RingHom.id _ := by
      apply MvPolynomial.ringHom_ext
      · intro r; simp [g]
      · intro j; simp [g, j.2]
    intro p
    exact ⟨MvPolynomial.rename Subtype.val p, RingHom.congr_fun hid p⟩
  letI : Algebra (MvPolynomial σ K) B := f.toAlgebra
  letI : Algebra (MvPolynomial σ K) (MvPolynomial {j // j ≠ j0} K) := g.toAlgebra
  letI : Algebra (MvPolynomial σ K) C := (ψ.comp f).toAlgebra
  haveI : Algebra.Etale (MvPolynomial σ K) B := h.toAlgebra
  haveI := Algebra.Etale.baseChange (MvPolynomial σ K) B (MvPolynomial {j // j ≠ j0} K)
  let eA : MvPolynomial {j // j ≠ j0} K →ₐ[MvPolynomial σ K] C :=
    { e with commutes' := fun p => RingHom.congr_fun heg p }
  let ψA : B →ₐ[MvPolynomial σ K] C := { ψ with commutes' := fun p => rfl }
  let Φ := Algebra.TensorProduct.lift eA ψA (fun _ _ => Commute.all _ _)
  have key : ∀ t : TensorProduct (MvPolynomial σ K) (MvPolynomial {j // j ≠ j0} K) B, ∃ b : B, t = 1 ⊗ₜ b := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | tmul q b =>
      obtain ⟨p, rfl⟩ := hg q
      refine ⟨f p * b, ?_⟩
      have h1 : (g p : MvPolynomial {j // j ≠ j0} K) = p • (1 : MvPolynomial {j // j ≠ j0} K) := by
        rw [Algebra.smul_def, mul_one]; rfl
      rw [h1, TensorProduct.smul_tmul, Algebra.smul_def]; rfl
    | add a b ha hb =>
      obtain ⟨x, rfl⟩ := ha
      obtain ⟨z, rfl⟩ := hb
      exact ⟨x + z, by rw [TensorProduct.tmul_add]⟩
  have hΦ : Function.Bijective Φ := by
    constructor
    · rw [injective_iff_map_eq_zero]
      intro t ht
      obtain ⟨b, rfl⟩ := key t
      have hb : ψ b = 0 := by simpa [Φ, eA, ψA] using ht
      rw [← RingHom.mem_ker, hk, Ideal.mem_span_singleton'] at hb
      obtain ⟨c, rfl⟩ := hb
      have h2 : c * y j0 = (MvPolynomial.X j0 : MvPolynomial σ K) • c := by
        rw [Algebra.smul_def, mul_comm]
        change _ = MvPolynomial.eval₂Hom s y (MvPolynomial.X j0) * c
        simp
      have h3 : (MvPolynomial.X j0 : MvPolynomial σ K) • (1 : MvPolynomial {j // j ≠ j0} K) = 0 := by
        rw [Algebra.smul_def, mul_one]
        change g (MvPolynomial.X j0) = 0
        simp [g]
      rw [h2, ← TensorProduct.smul_tmul, h3, TensorProduct.zero_tmul]
    · intro c
      obtain ⟨b, rfl⟩ := hψ c
      exact ⟨1 ⊗ₜ b, by simp [Φ, eA, ψA]⟩
  have hcomp : e = (Φ : TensorProduct (MvPolynomial σ K) (MvPolynomial {j // j ≠ j0} K) B →+* C).comp
      (algebraMap (MvPolynomial {j // j ≠ j0} K) (TensorProduct (MvPolynomial σ K) (MvPolynomial {j // j ≠ j0} K) B)) := by
    ext q
    · simp [Φ, eA, ψA, e, Algebra.TensorProduct.algebraMap_apply]
    · simp [Φ, eA, ψA, e, Algebra.TensorProduct.algebraMap_apply]
  change e.Etale
  rw [hcomp]
  exact etale_comp _ _ (RingHom.etale_algebraMap.2 inferInstance) (RingHom.Etale.of_bijective hΦ)

end CrystallineSemistableComparison.Onto.CLB

end
