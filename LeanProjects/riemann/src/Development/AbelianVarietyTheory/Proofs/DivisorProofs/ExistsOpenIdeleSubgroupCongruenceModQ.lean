import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.DatumF
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCmAdeleUnitCharacterReadingHeckeChar
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ExistsIdealsPrimeToEqSpan
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DetCharEqOneOfHasWt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitOpenAndCongrOpen
open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.IndefR.DatumF

noncomputable section

namespace GlobalTheory.OpenCongrIdele

theorem exists_open_congr : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsCMField E] (q : ℕ), q ≠ 0 → ∃ U : Subgroup (AF F ⊗[F] E)ˣ, IsOpen (U : Set (AF F ⊗[F] E)ˣ) ∧ (∀ z : (AF F ⊗[F] E)ˣ, At (evI F) ((z : AF F ⊗[F] E) - 1) → z ∈ U) ∧ ∀ k : Eˣ, Units.map (incAF F E).toMonoidHom k ∈ U → ∃ u : (𝓞 E)ˣ, ((u : 𝓞 E) : E) = k ∧ (u : 𝓞 E) - 1 ∈ Ideal.span {((q : ℕ) : 𝓞 E)} := by
  intro F E _ _ _ _ _ _ q hq
  obtain ⟨Θ, hc, hΘ⟩ := GlobalTheory.CharTransport.exists_toAdele F E
  set 𝔪 : Ideal (𝓞 E) := Ideal.span {((q : ℕ) : 𝓞 E)} with h𝔪
  have hm : 𝔪 ≠ ⊥ := by
    rw [h𝔪, Ne, Ideal.span_singleton_eq_bot]; exact Nat.cast_ne_zero.2 hq
  let V : Subgroup (Neutral.B1.Ideles E) := GlobalTheory.Mem.Chr.unitIdl E ⊓ GlobalTheory.RayChar.congrIdl 𝔪
  let φ : (AF F ⊗[F] E)ˣ →* Neutral.B1.Ideles E := Units.map Θ.toMonoidHom
  refine ⟨V.comap φ, ?_, fun z hz => ?_, fun k hk => ?_⟩
  · exact (GlobalTheory.Mem.UnitOpen.isOpen_unitIdl.inter (GlobalTheory.RayChar.isOpen_congrIdl hm)).preimage
      (Continuous.units_map _ hc)
  · have hfin : (Θ (z : AF F ⊗[F] E)).2 = 1 := by
      let a : AF F := pairA F 0 1
      have ha : evI F a = 0 := by
        show InfiniteAdeleRing.ringEquiv_mixedSpace F 0 = 0
        exact map_zero _
      have h0 : a • ((z : AF F ⊗[F] E) - 1) = 0 := hz a ha
      have h1 : Θ (a • ((z : AF F ⊗[F] E) - 1)) =
          GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.adeleMap F E a * Θ ((z : AF F ⊗[F] E) - 1) := by
        rw [Algebra.smul_def, map_mul]
        congr 1
        change Θ (a ⊗ₜ[F] (1 : E)) = _
        rw [hΘ, map_one, mul_one]
      have h2 : (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.adeleMap F E a).2 = 1 := map_one (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.finiteAdeleMap F E)
      have h3 : (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.adeleMap F E a * Θ ((z : AF F ⊗[F] E) - 1)).2 = 0 := by
        rw [← h1, h0, map_zero]; rfl
      have h4 : (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.adeleMap F E a).2 * (Θ ((z : AF F ⊗[F] E) - 1)).2 = 0 := h3
      rw [h2, one_mul, map_sub, map_one] at h4
      exact sub_eq_zero.1 h4
    have hv : ∀ v : HeightOneSpectrum (𝓞 E), GlobalTheory.RayChar.cmp (φ z) v = 1 := fun v => by
      show (Θ (z : AF F ⊗[F] E)).2 v = 1
      rw [hfin]; rfl
    refine ⟨fun v => ?_, (GlobalTheory.RayChar.mem_congrIdl hm).2 fun v _ => ?_⟩
    · show Valued.v (GlobalTheory.RayChar.cmp (φ z) v) = 1
      rw [hv v, map_one]
    · rw [hv v, sub_self, map_zero]; exact zero_le'
  · have he : φ (Units.map (incAF F E).toMonoidHom k) = Neutral.B1.diagUnits E k := Units.ext (by
      change Θ ((1 : AF F) ⊗ₜ[F] (k : E)) = _
      rw [hΘ, map_one, one_mul]; rfl)
    have hk' : Neutral.B1.diagUnits E k ∈ V := by rw [← he]; exact hk
    obtain ⟨u, hu⟩ := GlobalTheory.DefU.NonTriv.exists_unit k hk'.1
    refine ⟨u, hu, (GlobalTheory.RayChar.mem_iff_at hm _).2 fun v hv => ?_⟩
    rw [GlobalTheory.RayChar.at'_sub_one]
    have h2 := (GlobalTheory.RayChar.mem_congrIdl hm).1 hk'.2 v hv
    rw [GlobalTheory.RayChar.cmp_diag, ← hu] at h2
    exact h2

end GlobalTheory.OpenCongrIdele
