import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.GermSCCols
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.SCMain
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ProdMemPow

set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace ReciprocityTheory.ChartRestriction.G.TB.SCPf

theorem prod_mem_pow {R k : Type} [CommRing R] [CommRing k] [Algebra R k] (J : Submodule R k) {β : Type}
    (t : Finset β) (x : β → k) (e : β → ℕ) (hx : ∀ b ∈ t, x b ∈ J ^ e b) :
    ∏ b ∈ t, x b ∈ J ^ (∑ b ∈ t, e b) := by
  first | exact UpperTheory.Reformulated.B.Qk22.prod_mem_pow .. | (apply UpperTheory.Reformulated.B.Qk22.prod_mem_pow <;> assumption) | (intros; apply UpperTheory.Reformulated.B.Qk22.prod_mem_pow <;> assumption) | (apply @UpperTheory.Reformulated.B.Qk22.prod_mem_pow <;> assumption) | (intros; apply @UpperTheory.Reformulated.B.Qk22.prod_mem_pow <;> assumption) | (apply @UpperTheory.Reformulated.B.Qk22.prod_mem_pow <;> first | assumption | infer_instance)

theorem scCols_of (hSC : SCSt) : SCColsSt := by
  classical
  intro R _ d O _ _ k _ _ _ hRQ J hJ1 B h hcg w0 hw0 m ι π _ _ _ c s ξh ψ hH hψ h11 h21 h12 n P hPint e he f hf
  refine Submodule.sum_mem _ fun mo hmo => ?_
  obtain ⟨r, hr⟩ := hPint mo
  rw [← hr, ← Algebra.smul_def]
  refine Submodule.smul_mem _ r (pow_le_pow_right' (Submodule.one_le.mpr hJ1) (he mo hmo)
    (prod_mem_pow J _ _ _ fun b _ => ?_))
  refine hSC R d O k hRQ J hJ1 B h hcg w0 hw0 m ι π c s ξh ψ hH hψ h11 h21 h12 _ ?_ _ ?_ (f b) (hf b)
  · intro n'
    rw [MvPolynomial.coeff_monomial]
    split_ifs
    · exact ⟨1, map_one _⟩
    · exact ⟨0, map_zero _⟩
  · intro n' hn'
    rw [Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hn')]

theorem scaled_connection_columns (hN1 : ConnectionIntegrality) (hN2 : ConnectionCommutator) (hN3 : ConnectionKillsSeries) : SCColsSt :=
  scCols_of (sc_of hN1 hN2 hN3)

end ReciprocityTheory.ChartRestriction.G.TB.SCPf
