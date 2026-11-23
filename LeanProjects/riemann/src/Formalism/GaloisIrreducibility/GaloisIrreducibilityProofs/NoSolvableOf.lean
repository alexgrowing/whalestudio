import Formalism.GaloisIrreducibility.NoSolvableOf

namespace Formalism.GaloisIrreducibility

theorem no_solvable_subgroup_of : NoSolvableOf := by
  intro h1 h2 h3 h4 α _ _ G σ p hp hσG hpc hlt hge htrans hsolv
  obtain ⟨k, hk, hkc⟩ := h1 α σ p hp hpc hlt
  have hkG : σ ^ k ∈ G := G.pow_mem hσG k
  have hprim := h2 α G (σ ^ k) p hp hkG hk hkc hlt htrans
  have halt := h3 α G (σ ^ k) p hp hkG hk hkc hge hprim
  have h5 : 5 ≤ Fintype.card α := by have := hp.two_le; omega
  apply h4 α h5
  haveI := hsolv
  exact solvable_of_solvable_injective (Subgroup.inclusion_injective halt)

end Formalism.GaloisIrreducibility
