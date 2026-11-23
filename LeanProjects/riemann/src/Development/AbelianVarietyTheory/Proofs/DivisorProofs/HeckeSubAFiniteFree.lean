import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompEqOneOfTransl

noncomputable section

namespace GlobalTheory.UPel.HT.HeckeAd

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke

variable {S : Scheme.{0}} {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R]

def heckeSubA {b : Base D R} {M : ℕ} {s : S ⟶ Sp R} (o : Obj b M s) (f : D.La →+ D.La) (N : ℕ) :
    Subgroup (𝟙_ (Over S) ⟶ o.A) where
  carrier := {h | ∃ x, h = o.eta (N • f x)}
  one_mem' := ⟨0, by rw [map_zero, smul_zero, eta_zero]⟩
  mul_mem' := by
    rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
    exact ⟨x + y, by rw [map_add, smul_add, o.eta_add]⟩
  inv_mem' := by
    rintro _ ⟨x, rfl⟩
    exact ⟨-x, by rw [map_neg, smul_neg, eta_neg]⟩

theorem mem_heckeSubA {b : Base D R} {M : ℕ} {s : S ⟶ Sp R} (o : Obj b M s) (f : D.La →+ D.La) (N : ℕ)
    (x : D.La) : o.eta (N • f x) ∈ heckeSubA o f N := ⟨x, rfl⟩

theorem eta_pow {b : Base D R} {M : ℕ} {s : S ⟶ Sp R} (o : Obj b M s) (n : ℕ) (z : D.La) :
    (o.eta z) ^ n = o.eta (n • z) := by
  induction n with
  | zero => rw [pow_zero, zero_smul, eta_zero]
  | succ n ih => rw [pow_succ, ih, succ_nsmul, o.eta_add]

theorem pow_eq_one_of_mem {b : Base D R} {N k : ℕ} {s : S ⟶ Sp R} (o : Obj b (N * k) s) (f : D.La →+ D.La)
    (h : 𝟙_ (Over S) ⟶ o.A) (hh : h ∈ heckeSubA o f N) : h ^ k = 1 := by
  obtain ⟨x, rfl⟩ := hh
  rw [eta_pow, smul_smul, show k * N = N * k from mul_comm _ _, o.eta_ker]

theorem act_mem {b : Base D R} {N k : ℕ} {s : S ⟶ Sp R} (o : Obj b (N * k) s) (f : D.La →+ D.La)
    (hf : ∀ (a : D.O) (x : D.La), ∃ z, f (a • x) = a • f x + (N * k) • z) (a : D.O)
    (h : 𝟙_ (Over S) ⟶ o.A) (hh : h ∈ heckeSubA o f N) : h ≫ o.act.act a ∈ heckeSubA o f N := by
  obtain ⟨x, rfl⟩ := hh
  obtain ⟨z, hz⟩ := hf a x
  refine ⟨a • x, ?_⟩
  rw [hz, smul_add, o.eta_add, smul_smul, show N * (N * k) = (N * k) * N from mul_comm _ _, ← smul_smul,
    o.eta_ker, _root_.mul_one, ← o.eta_lin, smul_comm]

theorem heckeSubA_finite_free (b : Base D R) (f : D.La →+ D.La) (k N : ℕ) (hk : 0 < k) (hN : 0 < N)
    (hkp : k.Coprime p) (hNp : N.Coprime p) (s : S ⟶ Sp R) (o : Obj b (N * k) s) :
    Finite (heckeSubA o f N) ∧ ∀ (κ : Type) [Field κ] [IsAlgClosed κ] (x : Sp κ ⟶ S) (h : 𝟙_ (Over S) ⟶ o.A),
      h ∈ heckeSubA o f N → toUnit (Over.mk x) ≫ h = 1 → h = 1 := by
  refine ⟨?_, ?_⟩
  · haveI := D.finLa
    let K : Submodule ℤ D.La := LinearMap.range ((k : ℤ) • LinearMap.id)
    haveI : Finite (D.La ⧸ K) := by
      apply Module.finite_of_fg_torsion
      intro q
      obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective K q
      refine ⟨⟨(k : ℤ), mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast hk.ne')⟩, ?_⟩
      show (k : ℤ) • (Submodule.Quotient.mk y : D.La ⧸ K) = 0
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
      exact ⟨y, by simp⟩
    let σ := Function.surjInv (Submodule.Quotient.mk_surjective K)
    refine Finite.of_surjective
      (fun q : D.La ⧸ K => (⟨o.eta (N • f (σ q)), mem_heckeSubA o f N _⟩ : heckeSubA o f N)) ?_
    rintro ⟨h, x, rfl⟩
    refine ⟨Submodule.Quotient.mk x, Subtype.ext ?_⟩
    have e : Submodule.Quotient.mk (σ (Submodule.Quotient.mk x)) = (Submodule.Quotient.mk x : D.La ⧸ K) :=
      Function.surjInv_eq _ _
    rw [Submodule.Quotient.eq] at e
    obtain ⟨z, hz⟩ := e
    have hz' : σ (Submodule.Quotient.mk x) = x + k • z := by
      simp only [LinearMap.smul_apply, LinearMap.id_apply, natCast_zsmul] at hz
      rw [hz]; abel
    show o.eta (N • f (σ (Submodule.Quotient.mk x))) = o.eta (N • f x)
    rw [hz', map_add, map_nsmul, smul_add, smul_smul, o.eta_add, o.eta_ker, _root_.mul_one]
  · intro κ _ _ x h hh h1
    obtain ⟨x0, rfl⟩ := hh
    have hβ : x ≫ s = spMap (Spec.preimage (x ≫ s)).hom := (Spec.map_preimage _).symm
    obtain ⟨I, hI⟩ := o.geom κ x _ hβ
    have h2 : I.ev (N * k) (N • f x0) = 1 := by rw [← hI]; exact h1
    obtain ⟨y, hy⟩ := (I.ker (N * k) (Nat.mul_pos hN hk) (Nat.Coprime.mul hNp hkp) _).1 h2
    rw [hy, o.eta_ker]

example {b : Base D R} {M : ℕ} {s : S ⟶ Sp R} (o : Obj b M s) (N : ℕ) (h : 𝟙_ (Over S) ⟶ o.A)
    (hh : h ∈ heckeSubA o 0 N) : h = 1 := by
  obtain ⟨x, rfl⟩ := hh
  rw [AddMonoidHom.zero_apply, smul_zero, eta_zero]

end GlobalTheory.UPel.HT.HeckeAd
