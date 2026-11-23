import Mathlib
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.HermitianCellMeasures.CellDefs
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsLatticeFrameIsMajorantFrame
import Development.AbelianVarietyTheory.Definitions.Foundations.EqPlaceIdemOfIsPrimeIdem

noncomputable section

open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta GlobalTheory.AdelicU PositivityTheory.Rg.Rsw.L

namespace GlobalTheory.CompanionTheory.UnitCell

theorem artinian_fields {ι : Type} [Finite ι] (A : ι → Type) [∀ i, CommRing (A i)] [∀ i, IsArtinianRing (A i)]
    {R : Type} [CommRing R] (c : ∀ i, R →+* A i) :
    ∃ (m : ℕ) (Ω : Fin m → Type) (_ : ∀ k, Field (Ω k)) (φ : ∀ k, R →+* Ω k),
      (∀ x, (∀ i, c i x = 1) → ∀ k, φ k x = 1) ∧
      ∀ z, (∀ k, φ k z ≠ 0) ↔ ∀ i, IsUnit (c i z) := by
  obtain ⟨m, ⟨q⟩⟩ := Finite.exists_equiv_fin (Σ i, MaximalSpectrum (A i))
  have hmax : ∀ k : Fin m, (q.symm k).2.asIdeal.IsMaximal := fun k => (q.symm k).2.isMaximal
  refine ⟨m, fun k => A (q.symm k).1 ⧸ (q.symm k).2.asIdeal, fun k => Ideal.Quotient.field _,
    fun k => (Ideal.Quotient.mk _).comp (c (q.symm k).1), fun x hx k => ?_, fun z => ⟨fun hz i => ?_, fun hz k h => ?_⟩⟩
  · simp [hx]
  · by_contra hu
    obtain ⟨M, hM, hzM⟩ := exists_max_ideal_of_mem_nonunits hu
    obtain ⟨k, hk⟩ : ∃ k, q.symm k = ⟨i, ⟨M, hM⟩⟩ := ⟨q _, q.symm_apply_apply _⟩
    refine hz k (Ideal.Quotient.eq_zero_iff_mem.2 ?_)
    rw [hk]
    exact hzM
  · have hk := hmax k
    have h' : c (q.symm k).1 z ∈ (q.symm k).2.asIdeal := Ideal.Quotient.eq_zero_iff_mem.1 h
    exact hk.ne_top (Ideal.eq_top_of_isUnit_mem _ h' (hz _))

section Glue

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def sc {R : Type} [CommRing R] (r : Rˣ) : GL (Fin 1) R := Units.map (Matrix.scalar (Fin 1)).toMonoidHom r

theorem sc_apply {R : Type} [CommRing R] (r : Rˣ) : (sc r).1 0 0 = r := by simp [sc]

theorem exists_adele (S : Finset (HeightOneSpectrum (𝓞 F))) (b : ∀ v : HeightOneSpectrum (𝓞 F), (Fv F v ⊗[F] E)ˣ)
    (hb : ∀ v ∉ S, b v = 1) (c : ∀ w : InfinitePlace F, (w.Completion ⊗[F] E)ˣ) :
    ∃ x : AF F ⊗[F] E, (∀ v, compFin F E v x = b v) ∧ ∀ w, compInf F E w x = c w := by
  obtain ⟨a, ha, hc⟩ := GlobalTheory.AdelicU.Frames.exists_GL_of_components S (fun v => sc (b v))
    (fun v hv => by rw [hb v hv]; exact map_one _) (fun w => sc (c w))
  refine ⟨a.1 0 0, fun v => ?_, fun w => ?_⟩
  · have h := congrArg (fun g : GL (Fin 1) (Fv F v ⊗[F] E) => g.1 0 0) (ha v)
    exact h.trans (sc_apply _)
  · have h := congrArg (fun g : GL (Fin 1) (w.Completion ⊗[F] E) => g.1 0 0) (hc w)
    exact h.trans (sc_apply _)

variable (F E) in

def LocR (S : Finset (HeightOneSpectrum (𝓞 F))) : InfinitePlace F ⊕ S → Type
  | .inl w => w.Completion ⊗[F] E
  | .inr v => Fv F v.1 ⊗[F] E

instance locRing (S : Finset (HeightOneSpectrum (𝓞 F))) : ∀ c, CommRing (LocR F E S c)
  | .inl w => inferInstanceAs (CommRing (w.Completion ⊗[F] E))
  | .inr v => inferInstanceAs (CommRing (Fv F v.1 ⊗[F] E))

variable (F E) in

def locC (S : Finset (HeightOneSpectrum (𝓞 F))) : ∀ c, AF F ⊗[F] E →+* LocR F E S c
  | .inl w => compInf F E w
  | .inr v => compFin F E v.1

instance locArt (S : Finset (HeightOneSpectrum (𝓞 F))) : ∀ c, IsArtinianRing (LocR F E S c) := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  rintro (w | v)
  · exact IsArtinianRing.of_finite w.Completion (w.Completion ⊗[F] E)
  · exact IsArtinianRing.of_finite (Fv F v.1) (Fv F v.1 ⊗[F] E)

open Classical in

theorem crit (S : Finset (HeightOneSpectrum (𝓞 F))) (e : AF F ⊗[F] E) (h1 : ∀ w, compInf F E w e = 1)
    (h2 : ∀ v, compFin F E v e = if v ∈ S then 1 else 0) :
    ∃ (m : ℕ) (Ω : Fin m → Type) (_ : ∀ i, Field (Ω i)) (φ : ∀ i, AF F ⊗[F] E →+* Ω i), (∀ i, φ i e = 1) ∧
      ∀ z : AF F ⊗[F] E, IsUnit (1 - e + e * z) ↔ ∀ i, φ i z ≠ 0 := by
  obtain ⟨m, Ω, fld, φ, hφ, hu⟩ := artinian_fields (LocR F E S) (locC F E S)
  have he : ∀ k, φ k e = 1 := hφ e (by
    rintro (w | ⟨v, hv⟩)
    · exact h1 w
    · exact (h2 v).trans (if_pos hv))
  refine ⟨m, Ω, fld, φ, he, fun z => ⟨fun h k => ?_, fun h => ?_⟩⟩
  · have h' := h.map (φ k)
    rw [map_add, map_sub, map_mul, map_one, he, sub_self, zero_add, one_mul] at h'
    exact h'.ne_zero
  · have hz := (hu z).1 h
    have hI : ∀ w, IsUnit (compInf F E w z) := fun w => hz (.inl w)
    have hS : ∀ v (h : v ∈ S), IsUnit (compFin F E v z) := fun v h => hz (.inr ⟨v, h⟩)
    obtain ⟨x, hxf, hxi⟩ := exists_adele (E := E) S
      (fun v => if h : v ∈ S then (hS v h).unit⁻¹ else 1) (fun v hv => dif_neg hv) (fun w => (hI w).unit⁻¹)
    refine isUnit_iff_exists_inv.2 ⟨x, GlobalTheory.AdelicU.Supp.adTens_eq_one' (fun w => ?_) fun v => ?_⟩
    · rw [map_mul, map_add, map_sub, map_mul, map_one, h1, hxi, sub_self, zero_add, one_mul]
      exact (hI w).mul_val_inv
    · rw [map_mul, map_add, map_sub, map_mul, map_one, h2, hxf]
      by_cases hv : v ∈ S
      · simp only [if_pos hv, dif_pos hv, sub_self, zero_add, one_mul]
        exact (hS v hv).mul_val_inv
      · simp [if_neg hv, dif_neg hv]

end Glue

theorem unitCrit : PositivityTheory.Rg.Rsw.L.IdemEx → PositivityTheory.Rg.Rsw.Cell.UnitCrit := fun _ D S e he =>
  crit S e he.1 (by convert he.2 using 4)

end GlobalTheory.CompanionTheory.UnitCell

end
