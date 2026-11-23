import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FormsOver
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Formalism.LocalToGlobal.LatticeGeometry.CmTypeMeetsConjugatePair
import Formalism.LocalToGlobal.ProjectiveLattices.HostRank

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.TrueGeo GlobalTheory.ShFam

namespace GlobalTheory.ShFam.CmDim

theorem finrank_host (D : D7) : Module.finrank ℚ D.host.E = 4 * D.R.ord := by
  have hb := (factEmb D.R D.host).1
  have h1 : Nat.card (D.R.GG) = Nat.card (D.host.E →+* ℂ) := Nat.card_congr (Equiv.ofBijective _ hb)
  have h2 : Nat.card (D.host.E →+* ℂ) = Module.finrank ℚ D.host.E := by
    rw [Nat.card_eq_fintype_card]; exact NumberField.Embeddings.card D.host.E ℂ
  have h4 : Nat.card (D.R.GG) = 4 * D.R.ord := D.R.toFrame.natCard_GG
  rw [← h2, ← h1, h4]

theorem two_mul_card_psi (φ : Formalism.HC.Frame) : 2 * Nat.card φ.Psi = 4 * φ.ord := by
  classical
  have h4 : Nat.card φ.GG = 4 * φ.ord := φ.natCard_GG
  have hfin : Finite φ.GG := Nat.finite_of_card_ne_zero (by rw [h4]; have := φ.ord_pos; omega)
  have e1 : {g : φ.GG // g ∈ φ.Psi} ≃ {g : φ.GG // ¬ g ∈ φ.Psi} :=
    (Equiv.mulRight φ.cc).subtypeEquiv fun g => mem_Psi_iff_mul_cc_notMem g
  have h1 := Nat.card_congr (Equiv.sumCompl fun g : φ.GG => g ∈ φ.Psi)
  rw [Nat.card_sum, ← Nat.card_congr e1, h4] at h1
  exact (two_mul _).trans h1

theorem card_tau (D : D7) : Fintype.card D.what₂.Tau = Module.finrank ℚ D.host.E / 2 := by
  have h1 := two_mul_card_psi D.R.toFrame
  have h2 := Nat.card_congr D.eTau
  rw [Nat.card_eq_fintype_card] at h2
  have h3 := finrank_host D
  omega

theorem cmList_nonempty {D : D7} (A : Amb D) : Nonempty (CmList A) := by
  let ψ : D.what₂.Tau → GlobalTheory.AllWt.Psi A.H := fun t => ⟨DV.tauEmb D t, A.cm t⟩
  have hb : Function.Bijective ψ := by
    constructor
    · intro a b h
      exact D.eTau.injective (Subtype.ext ((factEmb D.R D.host).1.1 (congrArg Subtype.val h)))
    · rintro ⟨τ, hτ⟩
      obtain ⟨g, rfl⟩ := (factEmb D.R D.host).1.2 τ
      have h3 : D.host.φ₀ D.host.sqrtMinusD = Complex.I * (Real.sqrt D.host.d : ℂ) := D.host.φ₀_mem
      rw [A.rt_eq, A.cmHost_rootComplex_eq_pm_sqrt, h3] at hτ
      obtain ⟨t, ht⟩ := (exists_tauEmb_iff D g).2 (((factEmb D.R D.host).2 g).1 hτ)
      exact ⟨t, Subtype.ext ht.symm⟩
  exact ⟨⟨Equiv.ofBijective ψ hb, fun _ => rfl⟩⟩

theorem cm_dim : ∀ (D : D7) (A : Amb D), Nonempty (CmList A) ∧ 2 < Module.finrank ℚ D.host.E / 2 ∧
    ∀ (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (Φ : s.Flag) (i : s.Comp),
      (Φ.C i).Y.dim = Formalism.DegreeFormula.dimFl D.what₂.Tau N := by
  intro D A
  refine ⟨cmList_nonempty A, ?_, fun N j S κ s Φ i => ?_⟩
  · rw [finrank_host]
    have h : 2 ^ 2 ≤ 2 ^ D.R.e := Nat.pow_le_pow_right two_pos D.host.two_le_e
    have h' : 2 ^ D.R.e ≤ D.R.ord := by
      exact D.R.toFrame.two_pow_le_ord
    omega
  · rw [Φ.dim_eq i, Formalism.DegreeFormula.dimFl, card_tau]

end GlobalTheory.ShFam.CmDim
