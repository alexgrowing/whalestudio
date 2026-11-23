import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.IwasawaCompletion.AwayPartMulIotaWPart
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.IwasawaCompletion.ExistsUpperUnitaryComplex

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.SmGL

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.Rs.C3.Fl

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {N c : ℕ} {n : Fin c → ℕ} (h : ∑ i, n i = N)

theorem infGL_leviEmb (m : ∀ i, GL (Fin (n i)) (Cinf E)) :
    infGL E N (leviEmb (Cinf E) (stdBlocks n h) m) = leviEmb (Ad E) (stdBlocks n h) fun i => infGL E (n i) (m i) :=
  cornerGL_leviEmb _ _ m

theorem infGL_mem_unipRad {u : GL (Fin N) (Cinf E)} (hu : u ∈ unipRad (Cinf E) (stdBlocks n h)) :
    infGL E N u ∈ unipRad (Ad E) (stdBlocks n h) :=
  cornerGL_mem_unipRad _ _ hu

theorem exists_iwasawa (g : GA E N) :
    ∃ (m : ∀ i, GA E (n i)) (u : GA E N) (k : Kinf E N) (g0 : GL (Fin N) (Af E)),
      u ∈ unipRad (Ad E) (stdBlocks n h) ∧
        g = leviEmb (Ad E) (stdBlocks n h) m * u * (infGL E N (Unitary.toUnits k) * finGL E N g0) := by
  obtain ⟨b, k, hb, hy⟩ := exists_borel_unitary (GeneralLinearGroup.map (pInf E) g)
  have hbp : b ∈ parab (Cinf E) (stdBlocks n h) := mem_parab_of_upper _ h hb
  obtain ⟨u, hu, hbu⟩ := exists_levi_mul_unip (Cinf E) (stdBlocks n h) ⟨b, hbp⟩
  generalize leviProj (Cinf E) (stdBlocks n h) ⟨b, hbp⟩ = L at hbu
  change b = _ at hbu
  refine ⟨fun i => infGL E (n i) (L i), infGL E N u, k, GeneralLinearGroup.map (pFin E) g,
    infGL_mem_unipRad h hu, ?_⟩
  conv_lhs => rw [← infGL_mul_finGL g, hy, hbu]
  rw [map_mul, map_mul, infGL_leviEmb, mul_assoc]

theorem exists_iwasawa_left (g : GA E N) :
    ∃ u ∈ unipRad (Ad E) (stdBlocks n h), ∃ (m : ∀ i, GA E (n i)) (k : Kinf E N) (x : GL (Fin N) (Af E)),
      g = u * (leviEmb (Ad E) (stdBlocks n h) m * (infGL E N (Unitary.toUnits k) * finGL E N x)) := by
  obtain ⟨m, u, k, x, hu, e⟩ := exists_iwasawa h g
  refine ⟨leviEmb (Ad E) (stdBlocks n h) m * u * (leviEmb (Ad E) (stdBlocks n h) m)⁻¹,
    (Subgroup.mem_normalizer_iff.1 (leviEmb_mem_normalizer (Ad E) (stdBlocks n h) m) u).1 hu, m, k, x, ?_⟩
  rw [e]
  simp only [mul_assoc, inv_mul_cancel_left]

end PositivityTheory.Rg.Rs.C3.Fl

end
