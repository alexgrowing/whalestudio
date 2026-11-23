import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadsOfLocMv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PointDeterminantEqNormOneClassOfLevel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianFormLastCoordinateUniformizerVectorSelf
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.TC.ChTw

theorem carries_mul_self {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {N : ℕ}
    {g h : GL (Fin N) (TensorProduct F E (Formalism.L2.Herm.Af F))} {L : Submodule (𝓞 E) (Fin N → E)}
    (hg : Formalism.L2.Herm.Carries g L L) (hh : Formalism.L2.Herm.Carries h L L) : Formalism.L2.Herm.Carries (g * h) L L := by
  intro x
  rw [hg x, hh, _root_.mul_inv_rev, Units.val_mul, ← Matrix.mulVec_mulVec]

set_option maxHeartbeats 1000000 in

theorem admissibleBasePoint_chart_mul_twist : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (u : B.Word) (a : I.ι) (i : ℕ) (Ch0 : Type) (chOf0 : (I.stp u I.mu0 i).Cl → Ch0) (Lb0 : Ch0 → Submodule (𝓞 B.host.E) (Fin (B.R.N i) → B.host.E)) (U0 : Ch0 → Subgroup (GA B (B.R.N i))) (chi0 : ∀ β, U0 β →* ℂˣ) (y0 : (I.stp u I.mu0 i).Cl → GA B (B.R.N i)) (st0 : ∀ c, (I.stp u I.mu0 i).Stab c → GL (Fin (B.R.N i)) B.host.E) (k0 : Ch0 → GA B (B.R.N i)), I.Reads u I.mu0 i chOf0 Lb0 U0 chi0 y0 st0 k0 → ∀ (g : GlobalTheory.Mem.Col2.TC.ChTw.Chart I u a i → Ch0) (t : GlobalTheory.Mem.Col2.TC.ChTw.Chart I u a i → GA B (B.R.N i)), (∀ β, ∃ p : DecoF B.fields.E (B.R.N i) ∅ ∅ ∅, PtOf (t β) p ∧ p.deco.1.N = stdLat B.fields.E (B.R.N i)) → (∀ β (v : HeightOneSpectrum (𝓞 B.host.F)), ((B.T u : 𝓞 B.host.F) ∈ v.asIdeal ∨ ∀ j, (B.host.g j : 𝓞 B.host.F) ∉ v.asIdeal) → bc (prV (E := B.host.E) v) (t β) = 1) → (a = I.mu0 → ∀ β, t β = 1) → GlobalTheory.Mem.Col2.TC.ChTw.AdmK I u a i (fun β => k0 (g β) * t β) := by
  intro B X I hI u a i Ch0 chOf0 Lb0 U0 chi0 y0 st0 k0 hR g t hstd hoff h0
  refine ⟨fun β => ?_, fun β v hT hQ hd => ?_, fun β P r j hr => ?_⟩
  · obtain ⟨p, hp, hN⟩ := hR.k_std (g β)
    obtain ⟨q, hq, hN'⟩ := hstd β
    have h1 := hp.lat
    have h2 := hq.lat
    rw [hN] at h1
    rw [hN'] at h2
    refine ⟨p, ⟨mul_mem hp.uni hq.uni, ?_, fun P => ?_, fun w => ?_, fun P => ?_⟩, hN⟩
    · rw [hN]
      exact carries_mul_self h1 h2
    · exact absurd P.2 (Finset.notMem_empty _)
    · exact absurd w.2 (Finset.notMem_empty _)
    · exact absurd P.2 (Finset.notMem_empty _)
  · have hq0 : I.Q I.mu0 = ∅ := ColIn.twistPrimes_reference_tuple_eq_empty _
    have hk : bc (prV (E := B.host.E) v) (k0 (g β)) = 1 :=
      hR.k_off (g β) v hT (by rintro ⟨P, hP, -⟩; rw [hq0] at hP; simp at hP) (Or.inl rfl)
    have ht : bc (prV (E := B.host.E) v) (t β) = 1 := by
      rcases hd with rfl | hd
      · rw [h0 rfl β, map_one]
      · exact hoff β v (Or.inr hd)
    have hm := map_mul (bc (prV (E := B.host.E) v)) (k0 (g β)) (t β)
    rw [hk, ht, one_mul] at hm
    exact hm
  · have hv : (B.T u : 𝓞 B.host.F) ∈ (P.1.under (𝓞 B.host.F)).asIdeal := by
      have := T_mem_vT (GlobalTheory.BasePrimes.primes_ok B X).1 u P
      rw [HeightOneSpectrum.under, Ideal.mem_comap, map_natCast]
      exact this
    have ht := hoff β _ (Or.inl hv)
    have ht' := (map_inv (bc (prV (E := B.host.E) (P.1.under (𝓞 B.host.F)))) (t β)).trans (by rw [ht, inv_one])
    have hent : ∀ r l, adAt B.host.F P.1 (((t β)⁻¹ : GA B (B.R.N i)).1 r l) = if r = l then 1 else 0 := by
      intro r l
      have e := congrArg (fun g => g.1 r l) ht'
      simp only [bc, Units.coe_map, Units.val_one, MonoidHom.coe_coe, RingHom.mapMatrix_apply, Matrix.map_apply] at e
      split_ifs with h
      · subst h
        exact FullDt.adAt_eq_one_of_prV P.1 (by simpa using e)
      · exact TilX.adAt_eq_zero_of_prV P.1 _ (by simpa [Matrix.one_apply_ne h] using e)
    have key : adAt B.host.F P.1 (((k0 (g β) * t β)⁻¹ : GA B (B.R.N i)).1 r j) =
        adAt B.host.F P.1 (((k0 (g β))⁻¹ : GA B (B.R.N i)).1 r j) := by
      rw [_root_.mul_inv_rev, Units.val_mul, Matrix.mul_apply, map_sum]
      simp only [map_mul, hent, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [key]
    exact hR.k_T (g β) P r j hr

end GlobalTheory.Mem.Col2.TC.ChTw
