import Mathlib
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.MassLandA
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsCongrIffTraceFormsIsometricCm
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasseNormTheoremQuadraticExtension

open NumberField Formalism.HermitianLattices.Ext.L3

namespace GlobalTheory.Mass

open NumberField in

theorem _root_.GlobalTheory.Mass.binary_hermitian_represents : _root_.Formalism.HermitianLattices.Ext.L3.HermRepUnram := by
  unfold _root_.Formalism.HermitianLattices.Ext.L3.HermRepUnram
  intro K _ _ _ hK a b n ha hb hn hpa hpb hpn
  obtain ⟨w, hw0, hw⟩ := _root_.Formalism.HermitianLattices.Ext.L3.exists_skew hK
  have memF : ∀ x : K, star x = x → x ∈ _root_.Formalism.HermitianLattices.Ext.L3.cmF K := fun x hx => (_root_.Formalism.HermitianLattices.Ext.L3.mem_cmF_iff K x).2 hx
  obtain ⟨ψ₀⟩ : Nonempty (K →+* ℂ) := inferInstance
  have ne_of_pos : ∀ x : K, _root_.Formalism.HermitianLattices.Ext.L3.TotPos x → x ≠ 0 := by
    intro x hx h
    have := hx ψ₀
    simp [h] at this
  let a' : _root_.Formalism.HermitianLattices.Ext.L3.cmF K := ⟨a, memF a ha⟩
  let b' : _root_.Formalism.HermitianLattices.Ext.L3.cmF K := ⟨b, memF b hb⟩
  let n' : _root_.Formalism.HermitianLattices.Ext.L3.cmF K := ⟨n, memF n hn⟩
  let δ : _root_.Formalism.HermitianLattices.Ext.L3.cmF K := ⟨w * w, memF _ (by rw [star_mul, hw]; ring)⟩
  have hnegδ : _root_.Formalism.HermitianLattices.Ext.L3.TotPos ((-δ : _root_.Formalism.HermitianLattices.Ext.L3.cmF K) : K) := by
    unfold _root_.Formalism.HermitianLattices.Ext.L3.TotPos
    intro ψ
    have h1 : ψ (star w) = (starRingEnd ℂ) (ψ w) := hK.2.1 ψ w
    rw [hw, map_neg] at h1
    have hre : (ψ w).re = 0 := by
      have := congrArg Complex.re h1
      simp at this
      linarith
    have hne : ψ w ≠ 0 := (map_ne_zero ψ).2 hw0
    have him : (ψ w).im ≠ 0 := by
      intro him
      exact hne (Complex.ext hre him)
    simp [δ, Complex.mul_re, hre]
    positivity
  have hδneg : ∀ φ : _root_.Formalism.HermitianLattices.Ext.L3.cmF K →+* ℝ, φ δ < 0 := by
    intro φ
    have := (_root_.Formalism.HermitianLattices.Ext.L3.totPos_iff hK (-δ)).1 hnegδ φ
    simpa using this
  have ha' : a' ≠ 0 := fun h => ne_of_pos a hpa (congrArg Subtype.val h)
  have hb' : b' ≠ 0 := fun h => ne_of_pos b hpb (congrArg Subtype.val h)
  have hn' : n' ≠ 0 := fun h => ne_of_pos n hpn (congrArg Subtype.val h)
  have hδ0 : δ ≠ 0 := fun h => hw0 (mul_self_eq_zero.1 (congrArg Subtype.val h))
  let c : Fin 5 → _root_.Formalism.HermitianLattices.Ext.L3.cmF K := ![a', -(a' * δ), b', -(b' * δ), -n']
  have hc : ∀ i, c i ≠ 0 := by
    intro i
    fin_cases i <;> simp [c, ha', hb', hn', hδ0]
  obtain ⟨x, hx0, hx⟩ := _root_.GlobalTheory.LocalQuad.isotropic_of_indefinite _root_.GlobalTheory.QNorm.hasseNormSt
    (_root_.Formalism.HermitianLattices.Ext.L3.cmF K) c (by simp) hc (by
      intro σ
      refine ⟨4, 0, ?_, ?_⟩
      · simpa [c] using (_root_.Formalism.HermitianLattices.Ext.L3.totPos_iff hK n').1 hpn σ
      · simpa [c] using (_root_.Formalism.HermitianLattices.Ext.L3.totPos_iff hK a').1 hpa σ)
  obtain ⟨y, hy4, hy⟩ := _root_.GlobalTheory.LocalQuad.HermClass.exists_zero_coord_ne_zero hc hx0 hx 4
  have h4 : (y 4 : K) ≠ 0 := fun h => hy4 (Subtype.ext h)
  have hy' := congrArg (fun z : _root_.Formalism.HermitianLattices.Ext.L3.cmF K => (z : K)) hy
  simp [Fin.sum_univ_five, c, a', b', n', δ] at hy'
  refine ⟨((y 0 : K) + (y 1 : K) * w) / (y 4 : K), ((y 2 : K) + (y 3 : K) * w) / (y 4 : K), ?_⟩
  simp only [star_div₀, star_add, star_mul, _root_.Formalism.HermitianLattices.Ext.L3.star_coe_cmF, hw]
  field_simp
  linear_combination hy'

end GlobalTheory.Mass
