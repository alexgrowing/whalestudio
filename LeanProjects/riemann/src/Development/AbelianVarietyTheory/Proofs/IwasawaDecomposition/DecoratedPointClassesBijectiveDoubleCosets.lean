import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NeZeroTop
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPointOfRationalUnitaryAdelicMul
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianFormLastCoordinateUniformizerVectorSelf
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.TopCh GlobalTheory.Mem.ColAd Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.ClsBij

section SlopeTestRemainingChoices

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {n : ℕ}

theorem ratAd_mem_ratPts (hc : CMData F E) (γ : UF E n) :
    ratAd F γ ∈ ratPts hc.sig (1 : Matrix (Fin n) (Fin n) E) (FiniteAdeleRing (𝓞 F) F) := by
  refine ⟨ufGL E n γ, ?_, rfl⟩
  show cT _ _ * 1 * _ = 1
  rw [mul_one]
  exact GlobalTheory.Mem.Col2.StepOk.ufGL_conjTranspose_mul γ

theorem exists_ratAd_eq (hc : CMData F E) {g : GL (Fin n) (AfE F E)}
    (hg : g ∈ ratPts hc.sig (1 : Matrix (Fin n) (Fin n) E) (FiniteAdeleRing (𝓞 F) F)) :
    ∃ γ : UF E n, ratAd F γ = g := by
  obtain ⟨r, hr, rfl⟩ := hg
  refine ⟨ratEquiv hc n ⟨r, hr⟩, ?_⟩
  show Formalism.UG.bc _ (ufGL E n _) = _
  rw [GlobalTheory.Mem.Col2.RatMove.ufGL_eq hc, MulEquiv.symm_apply_apply]

end SlopeTestRemainingChoices

theorem classes_bijective : ∀ (F E K : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] [Field K] (hc : CMData F E) (n : ℕ) [NeZero n] (ST SG Q : Finset (HeightOneSpectrum (𝓞 E))) (C : Type) (Λ : LevFam E K n SG) (Θ : LevQFam E K n Q) (s : C → DecoF E n ST SG Q) (U : Subgroup (GL (Fin n) (AfE F E))) (k' : GL (Fin n) (AfE F E)) (y : C → UPts hc.sig (1 : Matrix (Fin n) (Fin n) E) (FiniteAdeleRing (𝓞 F) F)), U ≤ UAd hc n → k' ∈ UAd hc n → (∀ (g x : GL (Fin n) (AfE F E)) (p p' : DecoF E n ST SG Q), IsPtOf hc (g * k') p → IsPtOf hc (g * x * k') p' → (x ∈ U ↔ ∃ (h : Λ.grp) (θ : Θ.grp), ((1, h.1, θ.1) : UF E n × GLG E n SG × GLQ E n Q) • p = p')) → (∀ g ∈ UAd hc n, ∃ x ∈ U, ∃ p : DecoF E n ST SG Q, IsPtOf hc (g * x * k') p) → (∀ c, IsPtOf hc ((y c).1 * k') (s c)) → (∀ c c' (γ : UF E n) (h : Λ.grp) (θ : Θ.grp), ((γ, h.1, θ.1) : UF E n × GLG E n SG × GLQ E n Q) • s c = s c' → c = c') → (∀ p, ∃ c, ∃ (γ : UF E n) (h : Λ.grp) (θ : Θ.grp), ((γ, h.1, θ.1) : UF E n × GLG E n SG × GLQ E n Q) • s c = p) → Function.Bijective (fun c => (Quotient.mk'' (y c) : ClassSet ((ratPts hc.sig (1 : Matrix (Fin n) (Fin n) E) (FiniteAdeleRing (𝓞 F) F)).subgroupOf (UPts hc.sig (1 : Matrix (Fin n) (Fin n) E) (FiniteAdeleRing (𝓞 F) F))) (U.subgroupOf (UPts hc.sig (1 : Matrix (Fin n) (Fin n) E) (FiniteAdeleRing (𝓞 F) F))))) := by
  intro F E K _ _ _ _ _ _ _ hc n _ ST SG Q C Λ Θ s U k' y hU hk' hlev hdense hpt hinj hsurj
  constructor
  · intro c c' hcc
    obtain ⟨γ, hγ, u, hu, he⟩ := (DoubleCoset.eq _ _ (y c) (y c')).1 hcc
    have he' : (y c').1 = γ.1 * (y c).1 * u.1 := by rw [he]; rfl
    obtain ⟨δ, hδ⟩ := exists_ratAd_eq hc (Subgroup.mem_subgroupOf.1 hγ)
    have h1 := GlobalTheory.Mem.Col2.RatMove.isPtOf_ratAd F E hc n ST SG Q δ⁻¹ _ _ (hpt c')
    have e1 : ratAd F δ⁻¹ * ((y c').1 * k') = (y c).1 * u.1 * k' := by
      rw [he', ← hδ, ← GlobalTheory.Mem.Col2.TilX.ratAd_inv]
      group
    rw [e1] at h1
    obtain ⟨h, θ, hhθ⟩ := (hlev (y c).1 u.1 (s c) _ (hpt c) h1).1 (Subgroup.mem_subgroupOf.1 hu)
    refine hinj c c' δ h θ ?_
    have e2 : ((δ, h.1, θ.1) : UF E n × GLG E n SG × GLQ E n Q) =
        ((δ, 1, 1) : UF E n × GLG E n SG × GLQ E n Q) * ((1, h.1, θ.1) : UF E n × GLG E n SG × GLQ E n Q) := by
      simp
    rw [e2, mul_smul, hhθ, smul_smul]
    have e3 : ((δ, 1, 1) : UF E n × GLG E n SG × GLQ E n Q) * ((δ⁻¹, 1, 1) : UF E n × GLG E n SG × GLQ E n Q) = 1 := by
      simp
    rw [e3, one_smul]
  · intro q
    induction q using Quotient.inductionOn' with
    | h z =>
    obtain ⟨x, hx, p, hp⟩ := hdense z.1 z.2
    obtain ⟨c, γ, h, θ, hcp⟩ := hsurj p
    refine ⟨c, ?_⟩
    have h1 := GlobalTheory.Mem.Col2.RatMove.isPtOf_ratAd F E hc n ST SG Q γ⁻¹ _ _ hp
    have e1 : ((γ⁻¹, 1, 1) : UF E n × GLG E n SG × GLQ E n Q) • p =
        ((1, h.1, θ.1) : UF E n × GLG E n SG × GLQ E n Q) • s c := by
      rw [← hcp, smul_smul]
      congr 1
      simp
    rw [e1] at h1
    have e2 : ratAd F γ⁻¹ * (z.1 * x * k') = (y c).1 * ((y c).1⁻¹ * ratAd F γ⁻¹ * z.1 * x) * k' := by
      group
    rw [e2] at h1
    have hx' : (y c).1⁻¹ * ratAd F γ⁻¹ * z.1 * x ∈ U := (hlev (y c).1 _ (s c) _ (hpt c) h1).2 ⟨h, θ, rfl⟩
    let kk : UPts hc.sig (1 : Matrix (Fin n) (Fin n) E) (FiniteAdeleRing (𝓞 F) F) :=
      ⟨(y c).1⁻¹ * ratAd F γ⁻¹ * z.1 * x * x⁻¹, hU (mul_mem hx' (inv_mem hx))⟩
    show DoubleCoset.mk _ _ (y c) = DoubleCoset.mk _ _ z
    refine (DoubleCoset.eq _ _ (y c) z).2 ⟨z * kk⁻¹ * (y c)⁻¹, ?_, kk, Subgroup.mem_subgroupOf.2 (mul_mem hx' (inv_mem hx)), by group⟩
    rw [Subgroup.mem_subgroupOf]
    have e4 : ((z * kk⁻¹ * (y c)⁻¹ : UPts hc.sig (1 : Matrix (Fin n) (Fin n) E) (FiniteAdeleRing (𝓞 F) F)) : GL (Fin n) (AfE F E))
        = ratAd F γ := by
      show z.1 * ((y c).1⁻¹ * ratAd F γ⁻¹ * z.1 * x * x⁻¹)⁻¹ * (y c).1⁻¹ = _
      rw [← GlobalTheory.Mem.Col2.TilX.ratAd_inv]
      group
    rw [e4]
    exact ratAd_mem_ratPts hc γ

end GlobalTheory.Mem.Col2.ClsBij
