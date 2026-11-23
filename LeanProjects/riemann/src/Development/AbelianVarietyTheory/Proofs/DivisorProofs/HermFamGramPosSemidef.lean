import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.KernelSt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieCoordLat
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DemaillyRegularisation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.MatrixLemma
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.QuasiPlurisubharmonic
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LieAlgebraMaps

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory NumberField
open Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.GeometryOfNumbersTheory
open MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Semi Formalism.L2.Pj
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.Toroidal GlobalTheory.LocM.Frm GlobalTheory.LieHt

namespace GlobalTheory.HeightParts

section Gram

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V] (h : HermFam K V) (σ : K →+* ℂ)

theorem hermFam_add_left (x y z : V) : h.form σ (x + y) z = h.form σ x z + h.form σ y z := by
  rw [← h.conj_symm σ z (x + y), h.add_right, map_add, h.conj_symm, h.conj_symm]

theorem hermFam_smul_left (a : K) (x y : V) : h.form σ (a • x) y = starRingEnd ℂ (σ a) * h.form σ x y := by
  rw [← h.conj_symm σ y (a • x), h.smul_right, map_mul, h.conj_symm]

theorem hermFam_sum_sum {α β : Type} [Fintype α] [Fintype β] (c : α → K) (x : α → V) (d : β → K) (y : β → V) :
    h.form σ (∑ i, c i • x i) (∑ j, d j • y j) =
      ∑ i, ∑ j, starRingEnd ℂ (σ (c i)) * σ (d j) * h.form σ (x i) (y j) := by
  classical
  have hl : ∀ (s : Finset α) (z : V), h.form σ (∑ i ∈ s, c i • x i) z = ∑ i ∈ s, h.form σ (c i • x i) z := by
    intro s z
    induction s using Finset.induction_on with
    | empty =>
      have := hermFam_add_left h σ 0 0 z
      simp only [add_zero] at this
      simp only [Finset.sum_empty]
      linear_combination -this
    | insert a s ha ih => rw [Finset.sum_insert ha, hermFam_add_left, ih, Finset.sum_insert ha]
  have hr : ∀ (s : Finset β) (z : V), h.form σ z (∑ j ∈ s, d j • y j) = ∑ j ∈ s, h.form σ z (d j • y j) := by
    intro s z
    induction s using Finset.induction_on with
    | empty =>
      have := h.add_right σ z 0 0
      simp only [add_zero] at this
      simp only [Finset.sum_empty]
      linear_combination -this
    | insert a s ha ih => rw [Finset.sum_insert ha, h.add_right, ih, Finset.sum_insert ha]
  rw [hl]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hr]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hermFam_smul_left, h.smul_right]
  ring

theorem hermFam_gram_posSemidef {n : ℕ} (v : Fin n → V) : (h.gram σ v).PosSemidef := by
  classical
  let W := Submodule.span K (Set.range v)
  haveI : FiniteDimensional K W := FiniteDimensional.span_of_finite K (Set.finite_range v)
  let b := Module.finBasis K W
  have hb : LinearIndependent K (fun i => (b i : V)) := b.linearIndependent.map' W.subtype W.ker_subtype
  let g : Matrix (Fin n) (Fin (Module.finrank K W)) K :=
    Matrix.of fun i j => b.repr ⟨v i, Submodule.subset_span ⟨i, rfl⟩⟩ j
  have hf : ∀ i, v i = ∑ j, g i j • (b j : V) := fun i => by
    have := congrArg W.subtype (b.sum_repr ⟨v i, Submodule.subset_span ⟨i, rfl⟩⟩).symm
    rw [map_sum] at this
    simpa [g] using this
  have hG := (h.posDef σ _ _ hb).posSemidef
  let B : Matrix (Fin n) (Fin (Module.finrank K W)) ℂ := Matrix.of fun i j => starRingEnd ℂ (σ (g i j))
  let G : Matrix (Fin (Module.finrank K W)) (Fin (Module.finrank K W)) ℂ := Matrix.of fun i j => h.form σ (b i : V) (b j)
  have e : h.gram σ v = B * G * B.conjTranspose := by
    ext i j
    simp only [HermFam.gram, G, Matrix.of_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, B, RCLike.star_def,
      Complex.conj_conj]
    rw [hf i, hf j, hermFam_sum_sum, Finset.sum_comm]
    simp only [Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    ring
  rw [e]
  exact hG.mul_mul_conjTranspose_same B

end Gram

section Mono

variable {K : Type} [Field K] [NumberField K] {m r m' : ℕ} {h : HermFam K (Fin m → K)}
  {L : Submodule (𝓞 K) (Fin m → K)} {ε : Fin r → Fin m → K} {q : (Fin m → K) →ₗ[K] (Fin m' → K)}
  {h' : HermFam K (Fin m' → K)} {L' : Submodule (𝓞 K) (Fin m' → K)}

theorem torusExt_mono {C C' : ℝ} (hT : TorusExt h L ε q h' L' C) (hC : C ≤ C') : TorusExt h L ε q h' L' C' := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, hm⟩ := hT
  have hd : (0 : ℂ) ≤ ((C' - C : ℝ) : ℂ) := Complex.zero_le_real.2 (sub_nonneg.2 hC)
  refine ⟨a1, a2, a3, a4, a5, a6, a7, fun σ => ⟨?_, fun n v => ?_⟩⟩
  · have := (hm σ).1.add ((hermFam_gram_posSemidef h σ ε).smul hd)
    convert this using 1
    push_cast
    module
  · have := ((hm σ).2 n v).add ((hermFam_gram_posSemidef h σ v).smul hd)
    convert this using 1
    push_cast
    module

end Mono

section With

variable {D : D7} (O : Setup D)

def IsLieAtWith (x : ToroidalCompactificationData O.s) (P : PolOf x O.Φ) (y : Pt O.s) (K : Type) [Field K] [NumberField K] (io : K →+* Qb)
    (L : Submodule (𝓞 K) (Fin (D.R.f * O.N) → K)) (h : HermFam K (Fin (D.R.f * O.N) → K)) : Prop :=
  ∃ (fK : O.κ.c.F →+* K) (yK : Sp K ⟶ gen O.s.T.Z)
    (xO : Sp (𝓞 K) ⟶ O.s.T.Z.X) (hx : spMap (algebraMap (𝓞 K) K) ≫ xO = yK ≫ genι O.s.T.Z)
    (hio : spMap io ≫ yK = y.y) (e : Fin (D.R.f * O.N) ≃ Letter O.S.Dw)
    (b : Fin (D.R.f * O.N) → TanM (yK ≫ genι O.s.T.Z) O.s.T.Z.t.G),
    O.CoreWith x P ∧ yK ≫ genStr O.s.T.Z = spMap fK ∧
    (∀ i, (tv (bcTan io (by rw [← Category.assoc, hio]) (b i))).left = y.u (e i).1 (e i).2) ∧
    L = lieCoordLat O.s.T.Z.t hx b ∧
    ∀ (σ : K →+* ℂ) (z : CxPts (genStr O.s.T.Z) (σ.comp fK)) (hz : z.1 = spMap σ ≫ yK) (u v : Fin (D.R.f * O.N) → K),
      h.form σ u v = x.met (σ.comp fK) z (bcTan σ (by rw [hz, Category.assoc]) (∑ i, v i • b i))
        (bcTan σ (by rw [hz, Category.assoc]) (∑ i, u i • b i))

variable {O} in

theorem IsLieAtWith.isLieAt {x : ToroidalCompactificationData O.s} {P : PolOf x O.Φ} {y : Pt O.s} {K : Type} [Field K] [NumberField K]
    {io : K →+* Qb} {L : Submodule (𝓞 K) (Fin (D.R.f * O.N) → K)} {h : HermFam K (Fin (D.R.f * O.N) → K)}
    (hw : IsLieAtWith O x P y K io L h) : IsLieAt O y K L h := by
  obtain ⟨fK, yK, xO, hx, hio, e, b, h₁, h₂, h₃, h₄, h₅⟩ := hw
  exact ⟨x, P, io, fK, yK, xO, hx, hio, e, b, h₁, h₂, h₃, h₄, h₅⟩

end With

end GlobalTheory.HeightParts

end
