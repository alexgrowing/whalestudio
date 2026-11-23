import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ISupIInfEigenspaceEqTop
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumWIffGoodFormsOrthSum
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.BadPlacesGoodCoefficients
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSelfDualCoordLatticeOfSelfDualFrame
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsDualFamilySelfDualHermitianSpace
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Mult Formalism.IndefR.Lev GlobalTheory.IndefiniteRowSideFullHecke
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FrameGram

theorem form_mem_span {R : Type} [CommRing R] (S : Subring R) (σ : R →+* R) (hσ : ∀ s ∈ S, σ s ∈ S) {n : ℕ}
    (J : Matrix (Fin n) (Fin n) R) (T : Set (Fin n → R))
    (hT : ∀ x ∈ T, ∀ y ∈ T, ∑ i, ∑ j, σ (x i) * J i j * y j ∈ S) :
    ∀ x ∈ Submodule.span S T, ∀ y ∈ Submodule.span S T, ∑ i, ∑ j, σ (x i) * J i j * y j ∈ S := by
  intro x hx y hy
  induction hx using Submodule.span_induction with
  | mem x hx =>
    induction hy using Submodule.span_induction with
    | mem y hy => exact hT x hx y hy
    | zero => simp
    | add a b _ _ ha hb =>
      simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
      exact S.add_mem ha hb
    | smul c a _ ha =>
      have : ∑ i, ∑ j, σ (x i) * J i j * (c • a) j = (c : R) * ∑ i, ∑ j, σ (x i) * J i j * a j := by
        simp only [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        show _ * ((c : R) * a j) = _
        ring
      rw [this]; exact S.mul_mem c.2 ha
  | zero => simp
  | add a b _ _ ha hb =>
    simp only [Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]
    exact S.add_mem ha hb
  | smul c a _ ha =>
    have : ∑ i, ∑ j, σ ((c • a) i) * J i j * y j = σ (c : R) * ∑ i, ∑ j, σ (a i) * J i j * y j := by
      simp only [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      show σ ((c : R) * a i) * _ * _ = _
      rw [map_mul]; ring
    rw [this]; exact S.mul_mem (hσ _ c.2) ha

theorem exists_unit {R : Type} [CommRing R] (S : Subring R) (σ : R →+* R) (hσ : ∀ s ∈ S, σ s ∈ S) {n m : ℕ}
    (J : Matrix (Fin n) (Fin n) R) (β : GL (Fin n) R) (H : Set (Fin n → R))
    (hβ : ∀ x, x ∈ H ↔ ∀ i, (β⁻¹).1.mulVec x i ∈ S)
    (hH : ∀ x ∈ H, ∀ y ∈ H, ∑ i, ∑ j, σ (x i) * J i j * y j ∈ S)
    (s s' : Fin m → Fin n → R) (hs : ∀ i, s i ∈ H) (hs' : ∀ i, s' i ∈ H)
    (hd : ∀ a j, ∑ i, s i a * ∑ k, σ (s' i k) * J k j = if a = j then 1 else 0) :
    ∃ G : GL (Fin n) S, S.subtype.mapMatrix G.1 = (β.1.map σ)ᵀ * J * β.1 := by
  have hcol : ∀ j, (fun i => β.1 i j) ∈ H := by
    intro j
    rw [hβ]
    intro k
    have : (β⁻¹).1.mulVec (fun i => β.1 i j) k = ((β⁻¹).1 * β.1) k j := rfl
    rw [this, Units.inv_mul, Matrix.one_apply]
    split_ifs
    · exact S.one_mem
    · exact S.zero_mem
  have a1 : ∀ i j, ((β.1.map σ)ᵀ * J * β.1) i j ∈ S := by
    intro i j
    have := hH _ (hcol i) _ (hcol j)
    rw [Finset.sum_comm] at this
    simpa only [Matrix.mul_apply, Finset.sum_mul, Matrix.transpose_apply, Matrix.map_apply] using this
  let P : Matrix (Fin n) (Fin m) R := Matrix.of fun a i => s i a
  let P' : Matrix (Fin n) (Fin m) R := Matrix.of fun a i => s' i a
  have hP : P * ((P'.map σ)ᵀ * J) = 1 := by
    ext a j
    rw [Matrix.one_apply, ← hd]
    rfl
  have a2 : ∀ i j, (((β⁻¹).1 * P) * (((β⁻¹).1 * P').map σ)ᵀ) i j ∈ S := by
    intro i j
    rw [Matrix.mul_apply]
    exact S.sum_mem fun k _ => S.mul_mem ((hβ _).1 (hs k) i) (hσ _ ((hβ _).1 (hs' k) j))
  have hinv : (((β⁻¹).1 * P) * (((β⁻¹).1 * P').map σ)ᵀ) * ((β.1.map σ)ᵀ * J * β.1) = 1 := by
    have e : (((β⁻¹).1 * P').map σ)ᵀ * (β.1.map σ)ᵀ = (P'.map σ)ᵀ := by
      rw [← Matrix.transpose_mul, ← Matrix.map_mul, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
    calc _ = (β⁻¹).1 * (P * (((((β⁻¹).1 * P').map σ)ᵀ * (β.1.map σ)ᵀ) * J)) * β.1 := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [e, hP, Matrix.mul_one, Units.inv_mul]
  let M : Matrix (Fin n) (Fin n) S := fun i j => ⟨_, a1 i j⟩
  let M' : Matrix (Fin n) (Fin n) S := fun i j => ⟨_, a2 i j⟩
  have hM : S.subtype.mapMatrix M = (β.1.map σ)ᵀ * J * β.1 := rfl
  have hM' : S.subtype.mapMatrix M' = ((β⁻¹).1 * P) * (((β⁻¹).1 * P').map σ)ᵀ := rfl
  have inj : Function.Injective (S.subtype.mapMatrix (m := Fin n)) := by
    intro A B h
    ext i j
    exact congrFun (congrFun h i) j
  have p2 : M' * M = 1 := inj (by rw [map_mul, map_one, hM, hM', hinv])
  exact ⟨⟨M, M', mul_eq_one_comm.1 p2, p2⟩, hM⟩

theorem exists_unit_adelic {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n m : ℕ}
    (c : E → E) (σ : E ⊗[F] Formalism.L2.Herm.Af F →+* E ⊗[F] Formalism.L2.Herm.Af F)
    (hσ : ∀ s ∈ Formalism.L2.Herm.intAf F E, σ s ∈ Formalism.L2.Herm.intAf F E)
    (hσι : ∀ x, σ (Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) x) = Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) (c x))
    (J : Matrix (Fin n) (Fin n) E) (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (Λ : Submodule (𝓞 E) (Fin n → E))
    (hβ : IsFrame β Λ) (hΛ : ∀ y ∈ Λ, ∀ x ∈ Λ, ∃ b : 𝓞 E, (b : E) = ∑ i, ∑ j, c (x i) * J i j * y j)
    (s s' : Fin m → Fin n → E) (hs : ∀ i, s i ∈ Λ ∧ s' i ∈ Λ)
    (hd : ∀ a j, ∑ i, s i a * ∑ k, c (s' i k) * J k j = if a = j then 1 else 0) :
    ∃ G : GL (Fin n) (Formalism.L2.Herm.intAf F E), (intGL F E n G).val =
      Formalism.UG.cT σ β.1 * J.map (Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F)) * β.1 := by
  let ι : E →+* E ⊗[F] Formalism.L2.Herm.Af F := Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F)
  replace hσι : ∀ x, σ (ι x) = ι (c x) := hσι
  have hmem : ∀ x ∈ Λ, (fun i => ι (x i)) ∈ Formalism.L2.Herm.hatL (F := F) Λ := fun x hx =>
    Submodule.subset_span ⟨x, hx, rfl⟩
  refine exists_unit (Formalism.L2.Herm.intAf F E) σ hσ (J.map ι) β
    (Formalism.L2.Herm.hatL (F := F) Λ) hβ ?_ (fun i a => ι (s i a)) (fun i a => ι (s' i a))
    (fun i => hmem _ (hs i).1) (fun i => hmem _ (hs i).2) ?_
  · refine form_mem_span _ σ hσ _ _ ?_
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    obtain ⟨b, hb⟩ := hΛ y hy x hx
    have : ∑ i, ∑ j, σ (ι (x i)) * (J.map ι) i j * ι (y j) = ι b := by
      rw [hb]
      simp only [map_sum, RingHom.map_mul, hσι, Matrix.map_apply]
    show ∑ i, ∑ j, σ (ι (x i)) * (J.map ι) i j * ι (y j) ∈ _
    rw [this]
    exact (oToS F E b).2
  · intro a j
    have := congrArg ι (hd a j)
    simp only [map_sum, RingHom.map_mul, ← hσι, apply_ite ι, RingHom.map_one, RingHom.map_zero] at this
    exact this

theorem gram_unimodular : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (N : ℕ), IsBaseFrame V β Λ N → ∃ G : GL (Fin V.rank) (Formalism.L2.Herm.intAf D.host.F D.host.E), (intGL D.host.F D.host.E V.rank G).val = BadPlacesGoodCoefficients.gramIn V β := by
  intro D V β Λ N hB
  have hsd := GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D V β Λ N ⟨1, by rw [pow_one]; exact hB⟩
  obtain ⟨m, s, s', hs, hd⟩ := GlobalTheory.LatVacDual.dualFamily D V Λ hsd
  exact exists_unit_adelic star (Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F)) (fun _ => GlobalTheory.LevSplit.sigR_int)
    (fun _ => rfl) V.gram β Λ hB.1 (fun y hy => (hsd.2 y).1 hy) s s' hs hd

end GlobalTheory.FrameGram
