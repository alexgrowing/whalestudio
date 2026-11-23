import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsIsHaarMeasureSUJ
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryToSpecialUnitaryLocalStatement
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.DSSU
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.SUExt

variable {n : ℕ}

lemma one_mem_SUset (ε : Fin n → Bool) : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ SUset ε := by
  refine ⟨?_, by simp⟩
  show Formalism.REAL.inUJ ε 1
  simp [Formalism.REAL.inUJ]

lemma mul_mem_SUset {ε : Fin n → Bool} {a b : Matrix (Fin n) (Fin n) ℂ} (ha : a ∈ SUset ε)
    (hb : b ∈ SUset ε) : a * b ∈ SUset ε := by
  obtain ⟨ha1, ha2⟩ := ha
  obtain ⟨hb1, hb2⟩ := hb
  refine ⟨?_, by rw [Matrix.det_mul, ha2, hb2, one_mul]⟩
  change Formalism.REAL.inUJ ε a at ha1
  change Formalism.REAL.inUJ ε b at hb1
  show Formalism.REAL.inUJ ε (a * b)
  unfold Formalism.REAL.inUJ at *
  rw [Matrix.conjTranspose_mul]
  calc bᴴ * aᴴ * Formalism.REAL.Jm ε * (a * b) = bᴴ * (aᴴ * Formalism.REAL.Jm ε * a) * b := by
        simp only [Matrix.mul_assoc]
    _ = Formalism.REAL.Jm ε := by rw [ha1, hb1]

lemma ne_zero_of_norm_one {z : ℂ} (hz : ‖z‖ = 1) : z ≠ 0 := by
  intro h; rw [h, norm_zero] at hz; exact zero_ne_one hz

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

lemma central_eq {ε : Fin n → Bool} (hn : 1 ≤ n) (m : ℤ) (π' : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H))
    (hrep : IsURepOn (SUset ε) π')
    (hc : ∀ z : ℂ, z ^ n = 1 → ∀ v, π' (z • (1 : Matrix (Fin n) (Fin n) ℂ)) v = z ^ m • v)
    {g : Matrix (Fin n) (Fin n) ℂ} {z w : ℂ} (hz : ‖z‖ = 1) (hw : ‖w‖ = 1)
    (hgz : z⁻¹ • g ∈ SUset ε) (hgw : w⁻¹ • g ∈ SUset ε) :
    z ^ m • π' (z⁻¹ • g) = w ^ m • π' (w⁻¹ • g) := by
  have hz0 := ne_zero_of_norm_one hz
  have hw0 := ne_zero_of_norm_one hw
  set ζ := z * w⁻¹ with hζ
  have hkey : w⁻¹ • g = (ζ • (1 : Matrix (Fin n) (Fin n) ℂ)) * (z⁻¹ • g) := by
    rw [smul_mul_assoc, one_mul, smul_smul]
    congr 1
    rw [hζ]; field_simp
  have hζn : ζ ^ n = 1 := by
    have h1 := congrArg Matrix.det hkey
    rw [hgw.2, Matrix.det_mul, hgz.2, Matrix.det_smul, Matrix.det_one, Fintype.card_fin] at h1
    simpa using h1.symm
  have hζnorm : ‖ζ‖ = 1 := by rw [hζ, norm_mul, norm_inv, hz, hw]; simp
  have hζ1 : ζ • (1 : Matrix (Fin n) (Fin n) ℂ) ∈ SUset ε :=
    ⟨((GlobalTheory.T.unitary_to_special_unitary_local n hn ε).2.1 ζ hζnorm 1 (one_mem_SUset ε)).1,
      by rw [Matrix.det_smul, Matrix.det_one, Fintype.card_fin, hζn, mul_one]⟩
  ext v
  rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply, hkey, hrep.1.2 _ hζ1 _ hgz,
    ContinuousLinearMap.comp_apply, hc ζ hζn, smul_smul]
  congr 1
  rw [hζ, mul_zpow, _root_.inv_zpow, mul_left_comm, mul_inv_cancel₀ (zpow_ne_zero m hw0), mul_one]

open Classical in

def extRep (ε : Fin n → Bool) (m : ℤ) (π' : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H))
    (g : Matrix (Fin n) (Fin n) ℂ) : H →L[ℂ] H :=
  if h : ∃ z : ℂ, ‖z‖ = 1 ∧ z⁻¹ • g ∈ SUset ε then h.choose ^ m • π' (h.choose⁻¹ • g) else 0

lemma extRep_eq {ε : Fin n → Bool} (hn : 1 ≤ n) (m : ℤ) (π' : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H))
    (hrep : IsURepOn (SUset ε) π')
    (hc : ∀ z : ℂ, z ^ n = 1 → ∀ v, π' (z • (1 : Matrix (Fin n) (Fin n) ℂ)) v = z ^ m • v)
    {g : Matrix (Fin n) (Fin n) ℂ} {z : ℂ} (hz : ‖z‖ = 1) (hg : z⁻¹ • g ∈ SUset ε) :
    extRep ε m π' g = z ^ m • π' (z⁻¹ • g) := by
  have h : ∃ z : ℂ, ‖z‖ = 1 ∧ z⁻¹ • g ∈ SUset ε := ⟨z, hz, hg⟩
  rw [extRep, dif_pos h]
  exact central_eq hn m π' hrep hc h.choose_spec.1 hz h.choose_spec.2 hg

theorem extends_to_U : ∀ (n : ℕ), 1 ≤ n → ∀ (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (m : ℤ) (π' : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)),
    IsURepOn (SUset ε) π' →
    (∀ z : ℂ, z ^ n = 1 → ∀ v, π' (z • (1 : Matrix (Fin n) (Fin n) ℂ)) v = z ^ m • v) →
    ∃ π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H), Ext ε m π' π ∧ IsURepOn (UJset ε) π := by
  intro n hn ε H _ _ m π' hrep hc
  have hS := GlobalTheory.T.unitary_to_special_unitary_local n hn ε
  have hE : Ext ε m π' (extRep ε m π') := by
    intro z hz g hg
    have hg' : z⁻¹ • (z • g) ∈ SUset ε := by
      rwa [smul_smul, inv_mul_cancel₀ (ne_zero_of_norm_one hz), one_smul]
    rw [extRep_eq hn m π' hrep hc hz hg', smul_smul, inv_mul_cancel₀ (ne_zero_of_norm_one hz), one_smul]
  refine ⟨extRep ε m π', hE, ⟨⟨?_, ?_⟩, ?_, ?_⟩⟩
  · have h1 := hE 1 (by simp) 1 (one_mem_SUset ε)
    rw [one_smul] at h1
    rw [h1, _root_.one_zpow, one_smul, hrep.1.1]
  · intro a ha b hb
    obtain ⟨z, hz, a₀, ha₀, rfl, -⟩ := hS.1 a ha
    obtain ⟨w, hw, b₀, hb₀, rfl, -⟩ := hS.1 b hb
    have hab : z • a₀ * w • b₀ = (z * w) • (a₀ * b₀) := smul_mul_smul_comm z a₀ w b₀
    rw [hab, hE _ (by rw [norm_mul, hz, hw, one_mul]) _ (mul_mem_SUset ha₀ hb₀), hE z hz a₀ ha₀,
      hE w hw b₀ hb₀, hrep.1.2 a₀ ha₀ b₀ hb₀]
    ext v
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, map_smul, smul_smul,
      mul_zpow]
    rw [mul_comm (w ^ m)]
  · intro g hg v
    obtain ⟨z, hz, g₀, hg₀, rfl, -⟩ := hS.1 g hg
    rw [hE z hz g₀ hg₀, ContinuousLinearMap.smul_apply, norm_smul, norm_zpow, hz, _root_.one_zpow, one_mul,
      hrep.2.1 g₀ hg₀ v]
  · intro v g hg
    obtain ⟨U, ζ, hUo, hgU, hζc, hζ⟩ := hS.2.2 g hg
    have hζc' : ContinuousOn ζ (UJset ε ∩ U) := hζc.mono Set.inter_subset_right
    have hne : ∀ x ∈ UJset ε ∩ U, ζ x ≠ 0 := fun x hx => ne_zero_of_norm_one (hζ x hx.2 hx.1).1
    have h1 : ContinuousOn (fun x => ζ x ^ m) (UJset ε ∩ U) :=
      hζc'.zpow₀ m (fun x hx => Or.inl (hne x hx))
    have h2 : ContinuousOn (fun x => (ζ x)⁻¹ • x) (UJset ε ∩ U) :=
      (hζc'.inv₀ hne).smul continuousOn_id
    have h3 : ContinuousOn (fun x => π' ((ζ x)⁻¹ • x) v) (UJset ε ∩ U) :=
      (hrep.2.2 v).comp h2 (fun x hx => (hζ x hx.2 hx.1).2)
    have hs : ContinuousOn (fun x => ζ x ^ m • π' ((ζ x)⁻¹ • x) v) (UJset ε ∩ U) := h1.smul h3
    have heq : Set.EqOn (fun x => extRep ε m π' x v) (fun x => ζ x ^ m • π' ((ζ x)⁻¹ • x) v)
        (UJset ε ∩ U) := by
      intro x hx
      simp only
      rw [extRep_eq hn m π' hrep hc (hζ x hx.2 hx.1).1 (hζ x hx.2 hx.1).2,
        ContinuousLinearMap.smul_apply]
    exact (continuousWithinAt_inter (hUo.mem_nhds hgU)).1 ((hs.congr heq) g ⟨hg, hgU⟩)

end GlobalTheory.SUExt

end
