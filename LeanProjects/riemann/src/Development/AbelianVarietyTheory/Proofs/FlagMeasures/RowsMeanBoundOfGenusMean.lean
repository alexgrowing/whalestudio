import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.RowsMeanC
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowsGenusWeightedSumComparisonStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BaseLatticeConstructionHoldsStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LatsDiscStable
import Formalism.HermitianLattices.HermitianLatticesProofs.GenusBasic
noncomputable section
open scoped Classical ENNReal
open NumberField Formalism.HermitianLatticesTheory GlobalTheory.Mass

namespace GlobalTheory.RowsMean

section General
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem sameGenus_trans (h : V →ₗ⋆[K] V →ₗ[K] K) {L M N : Submodule (𝓞 K) V}
    (h1 : SameGenus h L M) (h2 : SameGenus h M N) : SameGenus h L N := by
  intro p hp
  obtain ⟨g₁, hg₁, e₁⟩ := h1 p hp
  obtain ⟨g₂, hg₂, e₂⟩ := h2 p hp
  refine ⟨g₂ * g₁, mul_mem hg₂ hg₁, ?_⟩
  rw [genusBasic_gmap_mul, e₁, e₂]

theorem sameGenus_refl (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V) : SameGenus h L L :=
  fun _ _ => ⟨1, one_mem _, genusBasic_gmap_one _⟩

theorem genus_eq_iff (h : V →ₗ⋆[K] V →ₗ[K] K) {L M : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hM : Submodule.IsLattice K M) :
    genus h L = genus h M ↔ L ∈ genus h M := by
  constructor
  · intro e; rw [← e]; exact ⟨hL, sameGenus_refl h L⟩
  · intro hLM
    ext N
    constructor
    · rintro ⟨hN, hs⟩
      exact ⟨hN, sameGenus_trans h hLM.2 hs⟩
    · rintro ⟨hN, hs⟩
      exact ⟨hN, sameGenus_trans h (genusBasic_symm h _ _ hLM.2) hs⟩

theorem mass_nonneg (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V) : 0 ≤ mass h L := by
  unfold mass
  split_ifs
  · exact Finset.sum_nonneg fun _ _ => by positivity
  · exact le_rfl

end General
end GlobalTheory.RowsMean

namespace GlobalTheory.RowsMean
section General
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem inv_card_eq (X : Type) [Nonempty X] :
    ((ENat.card X : ℕ∞) : ℝ≥0∞)⁻¹ = ENNReal.ofReal ((Nat.card X : ℝ))⁻¹ := by
  rcases finite_or_infinite X with hX | hX
  · rw [ENat.card_eq_coe_natCard]
    have hp : 0 < Nat.card X := Nat.card_pos
    rw [ENNReal.ofReal_inv_of_pos (by exact_mod_cast hp), ENNReal.ofReal_natCast]
    simp
  · rw [ENat.card_eq_top_of_infinite, Nat.card_eq_zero_of_infinite]
    simp

def stabEquiv (h : V →ₗ⋆[K] V →ₗ[K] K) (M : Submodule (𝓞 K) V) :
    MulAction.stabilizer (isom h) M ≃ Formalism.ThetaLiftIndependence.autL h M where
  toFun g := ⟨g.1.1, g.1.2, g.2⟩
  invFun a := ⟨⟨a.1, a.2.1⟩, a.2.2⟩
  left_inv g := rfl
  right_inv a := rfl

theorem mass_le_orbMass (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V) :
    ENNReal.ofReal (mass h L) ≤ orbMass (isom h) (genus h L) := by
  unfold mass
  split_ifs with hs
  swap
  · simp
  have hs' : Formalism.ThetaLiftIndependence.IsClassReps h L hs.choose := hs.choose_spec
  rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => by positivity)]
  have hrel : ∀ M : Submodule (𝓞 K) V, MulAction.orbitRel (isom h) (Submodule (𝓞 K) V)
      (Quotient.out (Quotient.mk'' M : MulAction.orbitRel.Quotient (isom h) (Submodule (𝓞 K) V))) M :=
    fun M => Quotient.exact' (Quotient.out_eq' _)
  have hq : ∀ M ∈ hs.choose, Quotient.out (Quotient.mk'' M :
      MulAction.orbitRel.Quotient (isom h) (Submodule (𝓞 K) V)) ∈ genus h L := by
    intro M hM
    obtain ⟨g, hg⟩ := hrel M
    rw [← hg]
    exact GlobalTheory.Mass.Transp.genus_stable L g M (hs'.1 M hM)
  let qm : hs.choose → {q : MulAction.orbitRel.Quotient (isom h) (Submodule (𝓞 K) V) //
      Quotient.out q ∈ genus h L} := fun M => ⟨Quotient.mk'' M.1, hq M.1 M.2⟩
  have hinj : Function.Injective qm := by
    rintro ⟨M₁, h₁⟩ ⟨M₂, h₂⟩ e
    have e' : (Quotient.mk'' M₁ : MulAction.orbitRel.Quotient (isom h) (Submodule (𝓞 K) V)) =
        Quotient.mk'' M₂ := congrArg Subtype.val e
    obtain ⟨g, hg⟩ := Quotient.exact' e'
    have hM₁ : M₁ ∈ genus h L := hs'.1 M₁ h₁
    have u := (hs'.2 M₁ hM₁).unique ⟨h₁, 1, one_mem _, genusBasic_gmap_one _⟩ ⟨h₂, g.1, g.2, hg⟩
    exact Subtype.ext u
  unfold orbMass orbSum
  rw [← Finset.sum_attach]
  have hterm : ∀ M : hs.choose, ENNReal.ofReal (((Nat.card (Formalism.ThetaLiftIndependence.autL h M.1) : ℕ) : ℝ))⁻¹ =
      ((ENat.card (MulAction.stabilizer (isom h) (Quotient.out (qm M).1)) : ℕ∞) : ℝ≥0∞)⁻¹ * 1 := by
    intro M
    rw [mul_one]
    have e1 : ENat.card (MulAction.stabilizer (isom h) (Quotient.out (qm M).1)) =
        ENat.card (Formalism.ThetaLiftIndependence.autL h M.1) :=
      ENat.card_congr (((MulAction.stabilizerEquivStabilizerOfOrbitRel (hrel M.1)).toEquiv).trans
        (stabEquiv h M.1))
    haveI : Nonempty (Formalism.ThetaLiftIndependence.autL h M.1) := ⟨stabEquiv h M.1 1⟩
    rw [e1, inv_card_eq]
  simp_rw [hterm]
  exact (Finset.sum_image (s := hs.choose.attach) (g := qm)
    (f := fun q : {q : MulAction.orbitRel.Quotient (isom h) (Submodule (𝓞 K) V) // Quotient.out q ∈ genus h L} =>
      ((ENat.card (MulAction.stabilizer (isom h) (Quotient.out q.1)) : ℕ∞) : ℝ≥0∞)⁻¹ * 1)
    (fun a _ b _ e => hinj e)).symm.le.trans (ENNReal.sum_le_tsum _)

end General
end GlobalTheory.RowsMean

namespace GlobalTheory.RowsMean

theorem sum_le_of_classes {ι α : Type} (s : Finset ι) (L : ι → α) (G : α → Set α) (P : α → Prop)
    (hP : ∀ i ∈ s, P (L i)) (hG : ∀ a b, P a → P b → (G a = G b ↔ a ∈ G b))
    (F w : ι → ℝ≥0∞) (b : ℝ≥0∞)
    (hcl : ∀ i₀ ∈ s, ∑ i ∈ s.filter (fun i => L i ∈ G (L i₀)), F i ≤
      (∑ i ∈ s.filter (fun i => L i ∈ G (L i₀)), w i) * b) :
    ∑ i ∈ s, F i ≤ (∑ i ∈ s, w i) * b := by
  have hmap : ∀ i ∈ s, G (L i) ∈ s.image (fun i => G (L i)) := fun i hi => Finset.mem_image_of_mem _ hi
  rw [← Finset.sum_fiberwise_of_maps_to hmap F, ← Finset.sum_fiberwise_of_maps_to hmap w, Finset.sum_mul]
  refine Finset.sum_le_sum fun y hy => ?_
  obtain ⟨i₀, hi₀, rfl⟩ := Finset.mem_image.1 hy
  have e : s.filter (fun i => G (L i) = G (L i₀)) = s.filter (fun i => L i ∈ G (L i₀)) :=
    Finset.filter_congr fun i hi => hG _ _ (hP i hi) (hP i₀ hi₀)
  rw [e]
  exact hcl i₀ hi₀

end GlobalTheory.RowsMean

namespace GlobalTheory.TypeAsm
open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.LatticeGluingRadicals
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem rowsMean : RowsMeanC := by
  intro D large₂ X Y u hStd W HW hEmb φ B hB hφ hbd
  have hOrb := GlobalTheory.T.rowsGenus_weightedSumComparison D large₂ X Y u hStd W HW hEmb
  have hLat := GlobalTheory.T.base_lattice_construction_holds D large₂ X Y u hStd W HW hEmb
  have hw : ∀ Λ, 0 ≤ wRow D (X.Fu u) Λ := fun Λ => by unfold wRow; positivity
  have hm : 0 ≤ massRows D (X.Fu u) (Y.what₂ u) := Finset.sum_nonneg fun Λ _ => hw Λ
  rw [ENNReal.ofReal_mul hm]
  unfold massRows
  rw [ENNReal.ofReal_sum_of_nonneg fun Λ _ => hw Λ]
  refine GlobalTheory.RowsMean.sum_le_of_classes (Y.what₂ u) (fun Λ => GlobalTheory.DegAsm.lat0 (F0 X u) W.subtype Λ)
    (Formalism.HermitianLatticesTheory.genus HW.B.flip) (Submodule.IsLattice D.host.E) (fun Λ hΛ => (hLat Λ hΛ).1.1)
    (fun a b ha hb => GlobalTheory.RowsMean.genus_eq_iff _ ha hb) _ _ _ ?_
  intro Λ₀ hΛ₀
  have h1 := hOrb φ hφ Λ₀ hΛ₀
  have h2 := hOrb (fun _ => 1) (fun _ _ => rfl) Λ₀ hΛ₀
  simp only [mul_one] at h2
  rw [h1, h2, mul_assoc]
  gcongr
  refine (hbd Λ₀ hΛ₀).trans ?_
  rw [ENNReal.ofReal_mul (GlobalTheory.RowsMean.mass_nonneg _ _)]
  gcongr
  exact GlobalTheory.RowsMean.mass_le_orbMass _ _

end GlobalTheory.TypeAsm
