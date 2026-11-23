import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsChartOf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationScaledMultipleStatement
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.TorRef

theorem GlobalTheory.TorRef.exists_common_polRay : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {I : Type} [Finite I] {R : I → Type} [∀ i, CommRing (R i)] {ω : ∀ i, R i →+* c.F} (C : ∀ i, Model Xo c (ω i)) (ψ φ : InvFun (𝓞 E)) (k : ℕ), (∀ i, PolRay ψ φ k (C i)) → ∃ bb N T₀ : ℕ, 0 < bb ∧ 0 < N ∧ ∀ T, T₀ ≤ T → ∀ i, ∃ BD : EffCartierData (C i).X, IsPol (comb (N * T) ψ bb φ) (N * T * k) (C i) BD := by
  intro E _ _ _ H D l Xo c I _ R _ ω C ψ φ k h
  classical
  haveI := Fintype.ofFinite I
  choose b N T0 hb hN hT using h
  refine ⟨∏ i, b i, (∏ i, b i) * ∏ i, N i, Finset.univ.sup T0, ?_, ?_, ?_⟩
  · exact Finset.prod_pos fun i _ => hb i
  · exact Nat.mul_pos (Finset.prod_pos fun i _ => hb i) (Finset.prod_pos fun i _ => hN i)
  · intro T hT' i
    have hi : i ∈ Finset.univ := Finset.mem_univ i
    have hbb : (∏ j ∈ Finset.univ.erase i, b j) * b i = ∏ j, b j := Finset.prod_erase_mul _ _ hi
    have hNN : (∏ j ∈ Finset.univ.erase i, N j) * N i = ∏ j, N j := Finset.prod_erase_mul _ _ hi
    have hnb : 0 < ∏ j ∈ Finset.univ.erase i, b j := Finset.prod_pos fun j _ => hb j
    have hnN : 0 < ∏ j ∈ Finset.univ.erase i, N j := Finset.prod_pos fun j _ => hN j
    have hTi : T0 i ≤ b i * (∏ j ∈ Finset.univ.erase i, N j) * T := by
      have h1 : T0 i ≤ T := le_trans (Finset.le_sup hi) hT'
      have h2 : T ≤ b i * (∏ j ∈ Finset.univ.erase i, N j) * T :=
        Nat.le_mul_of_pos_left T (Nat.mul_pos (hb i) hnN)
      omega
    obtain ⟨BD, hBD⟩ := hT i _ hTi
    obtain ⟨BD', hBD'⟩ := GlobalTheory.T.polarization_scaled_multiple (C i) ψ φ (N i * (b i * (∏ j ∈ Finset.univ.erase i, N j) * T)) (b i)
      (N i * (b i * (∏ j ∈ Finset.univ.erase i, N j) * T) * k) (∏ j ∈ Finset.univ.erase i, b j) BD hnb hBD
    refine ⟨BD', ?_⟩
    have e1 : (∏ j ∈ Finset.univ.erase i, b j) * (N i * (b i * (∏ j ∈ Finset.univ.erase i, N j) * T)) =
        (∏ j, b j) * (∏ j, N j) * T := by rw [← hbb, ← hNN]; ring
    have e3 : (∏ j ∈ Finset.univ.erase i, b j) * (N i * (b i * (∏ j ∈ Finset.univ.erase i, N j) * T) * k) =
        (∏ j, b j) * (∏ j, N j) * T * k := by rw [← hbb, ← hNN]; ring
    rw [e1, hbb, e3] at hBD'
    exact hBD'
