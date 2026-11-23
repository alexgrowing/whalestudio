import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NeZeroTop
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPtOfIffUnitaryDecoration

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.TopCh GlobalTheory.Mem.ColAd Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.TopCh

theorem decoRaw_mul_levelIwahori_reduction {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (hc : CMData F E)
    {n : ℕ} [NeZero n] (ST SG : Finset (HeightOneSpectrum (𝓞 E))) (g z : GL (Fin n) (AfE F E)) (hz : z ∈ J0 hc n ST) :
    decoRaw ST SG (g * z) = (decoRaw ST SG g).act 1 (redG hc n ST SG ⟨z, hz⟩)⁻¹ := by
  have h := decoRaw_rawSm hc ST SG 1 (⟨z, hz⟩⁻¹ : J0 hc n ST) g
  rw [map_one, map_inv] at h
  have e : Formalism.UG.bc (iA F E) ((1 : URat hc n) : GL (Fin n) E) * g *
      (((⟨z, hz⟩⁻¹ : J0 hc n ST) : J0 hc n ST) : GL (Fin n) (AfE F E))⁻¹ = g * z := by
    simp
  rw [e] at h
  exact h

theorem isPtOf_mul_J0 : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (hc : CMData F E) (n : ℕ) [NeZero n] (ST SG Q : Finset (HeightOneSpectrum (𝓞 E))) (g z : GL (Fin n) (AfE F E)) (p p' : DecoF E n ST SG Q) (h : GLG E n SG), (IsPtOf hc g p → IsPtOf hc (g * z) p' → ((∃ hz : z ∈ J0 hc n ST, redG hc n ST SG ⟨z, hz⟩ = h⁻¹) ↔ p'.deco = ((1, h) : UF E n × GLG E n SG) • p.deco)) ∧ (Q = ∅ → IsPtOf hc g p → ∀ hz : z ∈ J0 hc n ST, redG hc n ST SG ⟨z, hz⟩ = h⁻¹ → IsPtOf hc (g * z) (((1, h, 1) : UF E n × GLG E n SG × GLQ E n Q) • p)) ∧ (Q = ∅ → g ∈ UAd hc n → ∃ q : DecoF E n ST SG Q, IsPtOf hc g q) := by
  intro F E _ _ _ _ _ _ hc n _ ST SG Q g z p p' h
  refine ⟨fun hp hp' => ⟨?_, fun he => ?_⟩, fun hQ hp hz hr => ?_, fun hQ hg => ?_⟩
  · rintro ⟨hz, hr⟩
    apply Subtype.ext
    have h1 := decoRaw_mul_levelIwahori_reduction hc ST SG g z hz
    rw [hr, inv_inv, (near_of_isPtOf hp 0).deco, (near_of_isPtOf hp' 0).deco] at h1
    exact h1
  · have hx : decoRaw ST SG (g * z) = (decoRaw ST SG g).act 1 h := by
      rw [(near_of_isPtOf hp 0).deco, (near_of_isPtOf hp' 0).deco, he]
      rfl
    obtain ⟨hJ, hr⟩ := mem_congruence_of_action hc ST SG hp'.uni hp.uni h hx
    have e : (g * z)⁻¹ * g = z⁻¹ := by group
    have hz : z ∈ J0 hc n ST := by
      have h1 := inv_mem hJ
      rwa [e, inv_inv] at h1
    refine ⟨hz, ?_⟩
    have e' : (⟨(g * z)⁻¹ * g, hJ⟩ : J0 hc n ST) = (⟨z, hz⟩ : J0 hc n ST)⁻¹ := Subtype.ext e
    rw [e', map_inv] at hr
    rw [← hr, inv_inv]
  · refine (GlobalTheory.Mem.Col2.PtDeco.isPtOf_iff_decoRaw F E hc n ST SG Q (g * z) _ hQ).2
      ⟨mul_mem hp.uni (congruence_le_adelic_unitary hc n ST hz), ?_⟩
    have h1 := decoRaw_mul_levelIwahori_reduction hc ST SG g z hz
    rw [hr, inv_inv, (near_of_isPtOf hp 0).deco] at h1
    exact h1.symm
  · obtain ⟨q, hq⟩ := exists_near (ST := ST) (SG := SG) (Q := Q) hc 0 hg
    exact ⟨q, (GlobalTheory.Mem.Col2.PtDeco.isPtOf_iff_decoRaw F E hc n ST SG Q g q hQ).2 ⟨hg, hq.deco.symm⟩⟩

end GlobalTheory.Mem.Col2.TopCh

end
