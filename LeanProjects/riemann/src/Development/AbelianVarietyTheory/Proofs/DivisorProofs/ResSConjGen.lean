import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ISupIInfEigenspaceEqTop
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumWIffGoodFormsOrthSum
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.BadPlacesGoodCoefficients
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FactorResIEqResS

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Mult Formalism.IndefR.Lev GlobalTheory.IndefiniteRowSideFullHecke
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ResConjPlace

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem conj_mem_int (τ : E →ₐ[F] E) {s : E ⊗[F] Formalism.L2.Herm.Af F} (hs : s ∈ Formalism.L2.Herm.intAf F E) :
    Formalism.UG.sigR τ (Formalism.L2.Herm.Af F) s ∈ Formalism.L2.Herm.intAf F E := by
  have : Formalism.L2.Herm.intAf F E ≤ (Formalism.L2.Herm.intAf F E).comap (Formalism.UG.sigR τ (Formalism.L2.Herm.Af F)) := by
    refine Subring.closure_le.2 ?_
    rintro _ (⟨⟨_, c, rfl⟩, rfl⟩ | ⟨b, rfl⟩)
    · obtain ⟨c', hc'⟩ : ∃ y' : 𝓞 E, (y' : E) = τ (c : E) :=
        ⟨⟨τ (c : E), (c.isIntegral_coe).map ((τ : E →+* E).toIntAlgHom)⟩, rfl⟩
      refine Subring.subset_closure (Or.inl ⟨⟨_, c', rfl⟩, ?_⟩)
      show (c' : E) ⊗ₜ[F] _ = τ (c : E) ⊗ₜ[F] _
      rw [hc']; rfl
    · refine Subring.subset_closure (Or.inr ⟨b, ?_⟩)
      show _ = τ 1 ⊗ₜ[F] _
      rw [map_one]; rfl
  exact this hs

theorem res_transfer {S k k' : Type} [CommRing S] [CommRing k] [CommRing k'] (r : S →+* k) (r' : S →+* k')
    (σ : S →+* S) (h : ∀ x, r x = 0 → r' (σ x) = 0) (s : S) (p : ℕ) (e : k ≃+* ZMod p) (e' : ZMod p ≃+* k') :
    r' (σ s) = e' (e (r s)) := by
  obtain ⟨n, hn⟩ := ZMod.intCast_surjective (e (r s))
  have h1 : r (s - n) = 0 := by
    rw [map_sub, map_intCast, sub_eq_zero]
    apply e.injective
    rw [← hn, map_intCast]
  have h4 := h _ h1
  rw [map_sub, map_intCast, map_sub, map_intCast, sub_eq_zero] at h4
  rw [h4, ← hn, map_intCast]

theorem resS_conj_gen (τ : E →ₐ[F] E) (w w' : Pl E)
    (hc : ∀ c ∈ w.asIdeal, ∃ c' ∈ w'.asIdeal, (c' : E) = τ (c : E)) (s t : Formalism.L2.Herm.intAf F E)
    (ht : (t : E ⊗[F] Formalism.L2.Herm.Af F) = Formalism.UG.sigR τ (Formalism.L2.Herm.Af F) (s : E ⊗[F] Formalism.L2.Herm.Af F))
    (p : ℕ) (e : kP w ≃+* ZMod p) (e' : ZMod p ≃+* kP w') :
    resS F w' t = e' (e (resS F w s)) := by
  let σ : Formalism.L2.Herm.intAf F E →+* Formalism.L2.Herm.intAf F E :=
    ((Formalism.UG.sigR τ (Formalism.L2.Herm.Af F)).comp
      (Formalism.L2.Herm.intAf F E).subtype).codRestrict _ (fun x => conj_mem_int τ x.2)
  have hts : t = σ s := Subtype.ext ht
  have h3 : idS F w.asIdeal ≤ (idS F w'.asIdeal).comap σ := by
    refine Ideal.map_le_iff_le_comap.2 fun c hcw => ?_
    obtain ⟨c', hc', hcc⟩ := hc c hcw
    have : σ (oToS F E c) = oToS F E c' := by
      apply Subtype.ext
      show τ (c : E) ⊗ₜ[F] _ = (c' : E) ⊗ₜ[F] _
      rw [hcc]; rfl
    rw [Ideal.mem_comap, Ideal.mem_comap, this]
    exact Ideal.mem_map_of_mem _ hc'
  rw [hts]
  refine res_transfer (resS F w) (resS F w') σ (fun x hx => ?_) s p e e'
  rw [GlobalTheory.GeoActCompare.resS_eq_resI, GlobalTheory.GeoActCompare.resI_eq_zero_iff] at hx ⊢
  exact h3 hx

end General

theorem resS_conj : ∀ (D : D7) (w w' : Pl D.host.E), IsConjPl w w' → ∀ (s t : Formalism.L2.Herm.intAf D.host.F D.host.E), (t : EAf D) = Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F) (s : EAf D) → ∀ (p : ℕ) (e : kP w ≃+* ZMod p) (e' : ZMod p ≃+* kP w'), resS D.host.F w' t = e' (e (resS D.host.F w s)) :=
  fun D w w' hc s t ht p e e' => resS_conj_gen D.sp.cm.sig w w' hc s t ht p e e'

end GlobalTheory.ResConjPlace
