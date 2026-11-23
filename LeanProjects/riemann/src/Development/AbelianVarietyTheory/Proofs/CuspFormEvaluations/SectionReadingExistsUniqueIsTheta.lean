import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ThConst
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnVal

variable {S : Scheme.{0}} {A : Over S} [GrpObj A]

theorem isHolFam_vtfQ {x0 : Sp ℂ ⟶ S} {g : ℕ} (e : (Fin g → ℂ) → (Over.mk x0 ⟶ A))
    (hol : IsHolFam (fun z => (e z).left)) : IsHolFam (fun z => (vtfQ A (e z)).left) := by
  have he : ∀ z, (e z).left ≫ A.hom = x0 := fun z => Over.w (e z)
  have h := isHolFam_vtfLift A.hom x0 (fun z => (e z).left) he hol
  let σ : pullback A.hom x0 ⟶ (Over.mk x0 ⊗ A).left := (pullbackSymmetry A.hom x0).hom
  have key : ∀ z, (vtfQ A (e z)).left = vtfLift A.hom x0 (fun z => (e z).left) he z ≫ σ := by
    intro z
    symm
    apply vtf_pt_uniq
    · have : σ ≫ (snd (Over.mk x0) A).left = pullback.fst A.hom x0 :=
        pullbackSymmetry_hom_comp_snd A.hom x0
      rw [Category.assoc, this]
      exact pullback.lift_fst _ _ _
    · have : σ ≫ (fst (Over.mk x0) A).left = pullback.snd A.hom x0 :=
        pullbackSymmetry_hom_comp_fst A.hom x0
      rw [Category.assoc, this]
      exact pullback.lift_snd _ _ _
  intro V φ
  have h1 := h (σ ⁻¹ᵁ V) ((σ.app V).hom φ)
  have h2 : (fun z => valAt' (vtfQ A (e z)).left V φ) = fun z =>
      valAt' (vtfLift A.hom x0 (fun z => (e z).left) he z) (σ ⁻¹ᵁ V) ((σ.app V).hom φ) := by
    funext z
    rw [key]
    exact (valAt'_comp _ σ V φ).symm
  have h3 : {z | ⊤ ≤ (vtfQ A (e z)).left ⁻¹ᵁ V} =
      {z | ⊤ ≤ vtfLift A.hom x0 (fun z => (e z).left) he z ⁻¹ᵁ (σ ⁻¹ᵁ V)} := by
    ext z
    rw [Set.mem_ofPred_eq, key]
    rfl
  exact ⟨h3 ▸ h1.1, h3 ▸ h2 ▸ h1.2⟩

variable {L : RigLB A} {x0 : Sp ℂ ⟶ S} {g : ℕ} (Φ : AnFr A L x0 g)

theorem AnFr.exists_chart_e (z : Fin g → ℂ) : ∃ j, ⊤ ≤ (Φ.e z).left ⁻¹ᵁ L.L.U j := by
  have h : (Φ.e z).left cpt ∈ ⨆ i, L.L.U i := by rw [L.isLB.cover]; trivial
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 h
  exact ⟨j, top_le_of_mem hj⟩

theorem AnFr.rd_val {k : ℤ} {F : LB.Sec (LPow A L.L k (Over.mk x0))} {θ : (Fin g → ℂ) → ℂ} (h : Φ.Rd k F θ)
    (j : L.L.ι) (z : Fin g → ℂ) (hj : ⊤ ≤ (Φ.e z).left ⁻¹ᵁ L.L.U j) :
    valAt' (vtfQ A (Φ.e z)).left ((LPow A L.L k (Over.mk x0)).U (fun _ => j)) (F.f (fun _ => j)) =
      θ z * Φ.fr j z ^ k :=
  h j z _ (vtfQ_snd A _) (vtfQ_fst A _) hj

theorem AnFr.rd_iff (k : ℤ) (F : LB.Sec (LPow A L.L k (Over.mk x0))) (θ : (Fin g → ℂ) → ℂ) :
    Φ.Rd k F θ ↔ ∀ z, ∃ j, ⊤ ≤ (Φ.e z).left ⁻¹ᵁ L.L.U j ∧
      valAt' (vtfQ A (Φ.e z)).left ((LPow A L.L k (Over.mk x0)).U (fun _ => j)) (F.f (fun _ => j)) =
        θ z * Φ.fr j z ^ k := by
  constructor
  · intro h z
    obtain ⟨j, hj⟩ := Φ.exists_chart_e z
    exact ⟨j, hj, Φ.rd_val h j z hj⟩
  · intro h j' z pt h1 h2 hj'
    obtain ⟨j, hj, hv⟩ := h z
    rw [vtf_pt_uniq A (Φ.e z) pt h1 h2]
    exact vtf_read A L.L F (Φ.e z) (fun j => Φ.fr j z) (fun a b hab => Φ.fr_g a b z hab) j j' hj hj' _ hv

theorem AnFr.rd_eq_div {k : ℤ} {F : LB.Sec (LPow A L.L k (Over.mk x0))} {θ : (Fin g → ℂ) → ℂ} (h : Φ.Rd k F θ)
    (j : L.L.ι) (z : Fin g → ℂ) (hj : ⊤ ≤ (Φ.e z).left ⁻¹ᵁ L.L.U j) :
    θ z = valAt' (vtfQ A (Φ.e z)).left ((LPow A L.L k (Over.mk x0)).U (fun _ => j)) (F.f (fun _ => j)) /
      Φ.fr j z ^ k := by
  rw [Φ.rd_val h j z hj, mul_div_cancel_right₀ _ (zpow_ne_zero _ (Φ.fr_ne j z hj))]

theorem AnFr.existsUnique_rd (k : ℤ) (F : LB.Sec (LPow A L.L k (Over.mk x0))) : ∃! θ, Φ.Rd k F θ := by
  choose c hc using Φ.exists_chart_e
  refine ⟨fun z => valAt' (vtfQ A (Φ.e z)).left ((LPow A L.L k (Over.mk x0)).U (fun _ => c z))
    (F.f (fun _ => c z)) / Φ.fr (c z) z ^ k, ?_, fun θ hθ => ?_⟩
  · refine (Φ.rd_iff k F _).2 fun z => ⟨c z, hc z, ?_⟩
    rw [div_mul_cancel₀ _ (zpow_ne_zero _ (Φ.fr_ne _ z (hc z)))]
  · funext z
    exact Φ.rd_eq_div hθ (c z) z (hc z)

theorem AnFr.e_add_lat {a : Fin g → ℂ} (ha : a ∈ Φ.lat) (z : Fin g → ℂ) : Φ.e (z + a) = Φ.e z := by
  rw [Φ.e_add, (Φ.e_ker a).2 ha, _root_.mul_one]

theorem AnFr.isTh_of_rd {k : ℤ} {F : LB.Sec (LPow A L.L k (Over.mk x0))} {θ : (Fin g → ℂ) → ℂ}
    (h : Φ.Rd k F θ) : Φ.IsTh k θ := by
  constructor
  · intro z0
    obtain ⟨j, hj⟩ := Φ.exists_chart_e z0
    have hO : IsOpen {z | ⊤ ≤ (Φ.e z).left ⁻¹ᵁ L.L.U j} := (Φ.hol (L.L.U j) 0).1
    have hv := (isHolFam_vtfQ Φ.e Φ.hol ((LPow A L.L k (Over.mk x0)).U (fun _ => j)) (F.f (fun _ => j))).2
    have hv' := hv.mono (s := {z | ⊤ ≤ (Φ.e z).left ⁻¹ᵁ L.L.U j})
      (fun z hz => vtf_chart A L.L k (Φ.e z) (fun _ => j) hz)
    have hd : DifferentiableOn ℂ θ {z | ⊤ ≤ (Φ.e z).left ⁻¹ᵁ L.L.U j} :=
      (hv'.mul ((Φ.fr_hol j).zpow (m := -k) (Or.inl fun z hz => Φ.fr_ne j z hz))).congr fun z hz => by
        rw [Φ.rd_eq_div h j z hz, div_eq_mul_inv, ← zpow_neg]
        rfl
    exact hd.differentiableAt (hO.mem_nhds hj)
  · intro a ha z
    obtain ⟨j, hj⟩ := Φ.exists_chart_e z
    have hj' : ⊤ ≤ (Φ.e (z + a)).left ⁻¹ᵁ L.L.U j := by rw [Φ.e_add_lat ha]; exact hj
    have h1 := Φ.rd_val h j z hj
    have h2 := Φ.rd_val h j (z + a) hj'
    rw [Φ.e_add_lat ha, h1, Φ.fr_per a ha j z hj, mul_zpow] at h2
    apply mul_right_cancel₀ (zpow_ne_zero k (Φ.fr_ne j (z + a) hj'))
    rw [← h2, AnFr.fac]
    ring

theorem reading_existsUnique_isTh : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (L : RigLB A) (x0 : Sp ℂ ⟶ S) (g : ℕ) (Φ : AnFr A L x0 g), ∀ (k : ℤ) (F : LB.Sec (LPow A L.L k (Over.mk x0))), (∃! θ, Φ.Rd k F θ) ∧ (∀ θ, Φ.Rd k F θ → Φ.IsTh k θ) ∧ ∀ θ, Φ.Rd k F θ ↔ ∀ z, ∃ j, ⊤ ≤ (Φ.e z).left ⁻¹ᵁ L.L.U j ∧ valAt' (ptSecT A (Φ.e z)).left ((LPow A L.L k (Over.mk x0)).U (fun _ => j)) (F.f (fun _ => j)) = θ z * Φ.fr j z ^ k := by
  intro S A _ _ L x0 g Φ k F
  exact ⟨Φ.existsUnique_rd k F, fun θ h => Φ.isTh_of_rd h, fun θ => Φ.rd_iff k F θ⟩

end GlobalTheory.AnVal
