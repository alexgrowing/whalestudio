import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinStable

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.InducedTensorMap
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.CompanionTheory.LimV
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.LimV.LeviCf

theorem entries_of_unip_lev {R : Type} [CommRing R] {r s : ℕ} (S : Set R) (x : BlockIx (r + s) r → R)
    (g : GL (Fin r) R × GL (Fin s) R)
    (h : ∀ a b : Fin (r + s), ((unip x * lev R r s g : GL (Fin (r + s)) R) : Matrix (Fin (r + s)) (Fin (r + s)) R) a b ∈ S)
    (h' : ∀ a b : Fin (r + s),
      (((unip x * lev R r s g)⁻¹ : GL (Fin (r + s)) R) : Matrix (Fin (r + s)) (Fin (r + s)) R) a b ∈ S) :
    ((∀ a b : Fin r, (g.1 : Matrix (Fin r) (Fin r) R) a b ∈ S) ∧
        ∀ a b : Fin r, ((g.1⁻¹ : GL (Fin r) R) : Matrix (Fin r) (Fin r) R) a b ∈ S) ∧
      ((∀ a b : Fin s, (g.2 : Matrix (Fin s) (Fin s) R) a b ∈ S) ∧
        ∀ a b : Fin s, ((g.2⁻¹ : GL (Fin s) R) : Matrix (Fin s) (Fin s) R) a b ∈ S) := by
  obtain ⟨v, hv⟩ := lev_mul_unip (g⁻¹) (-x)
  have hu : (unip x : GL (Fin (r + s)) R)⁻¹ = unip (-x) := by
    rw [inv_eq_iff_mul_eq_one, ← D.unip_add', add_neg_cancel, unip_zero]
  have hi : (unip x * lev R r s g : GL (Fin (r + s)) R)⁻¹ = unip v * lev R r s g⁻¹ := by
    rw [_root_.mul_inv_rev, hu, ← map_inv, hv]
  rw [hi] at h'
  refine ⟨⟨fun a b => ?_, fun a b => ?_⟩, fun a b => ?_, fun a b => ?_⟩
  · rw [← unip_lev_cc x g a b]; exact h _ _
  · have := unip_lev_cc v g⁻¹ a b
    rw [Prod.fst_inv] at this
    rw [← this]; exact h' _ _
  · rw [← unip_lev_nn x g a b]; exact h _ _
  · have := unip_lev_nn v g⁻¹ a b
    rw [Prod.snd_inv] at this
    rw [← this]; exact h' _ _

theorem levi_cf_integral {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {r s : ℕ}
    (u : BlockIx (r + s) r → Ad E) (m : GA E r × GA E s) (k : Kinf E (r + s)) (c : GL (Fin (r + s)) (Af E))
    (hc : c ∈ KO E (r + s)) (h : unip u * lev (Ad E) r s m = cf (r + s) k c) :
    ∃ (k₁ : Kinf E r) (c₁ : GL (Fin r) (Af E)) (k₂ : Kinf E s) (c₂ : GL (Fin s) (Af E)),
      c₁ ∈ KO E r ∧ c₂ ∈ KO E s ∧ m = (cf r k₁ c₁, cf s k₂ c₂) := by
  obtain ⟨k₁, g₁, k₂, g₂, hm⟩ := levi_cf h
  have f1 : GeneralLinearGroup.map (pFin E) m.1 = g₁ := by
    rw [hm, cf, map_mul, pFin_infGL, pFin_finGL, one_mul]
  have f2 : GeneralLinearGroup.map (pFin E) m.2 = g₂ := by
    rw [show m.2 = cf s k₂ g₂ by rw [hm], cf, map_mul, pFin_infGL, pFin_finGL, one_mul]
  have h2 := congrArg (GeneralLinearGroup.map (pFin E)) h
  rw [map_mul, IwaAd.map_unip, IwaAd.map_lev, cf, map_mul, pFin_infGL, pFin_finGL, one_mul, f1, f2] at h2
  obtain ⟨hc1, hc2⟩ := (GroundTheory.Automorphic.AdelicGLn.mem_integralFiniteGL_iff E (r + s)).1 hc
  obtain ⟨⟨a1, a2⟩, b1, b2⟩ := entries_of_unip_lev (↑(GroundTheory.Global.integralFiniteAdeles (𝓞 E) E) : Set (Af E)) _ (g₁, g₂)
    (by rw [h2]; exact hc1) (by rw [h2]; exact hc2)
  exact ⟨k₁, g₁, k₂, g₂, (GroundTheory.Automorphic.AdelicGLn.mem_integralFiniteGL_iff E r).2 ⟨a1, a2⟩,
    (GroundTheory.Automorphic.AdelicGLn.mem_integralFiniteGL_iff E s).2 ⟨b1, b2⟩, hm⟩

end GlobalTheory.CompanionTheory.LimV.LeviCf

end
