import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTypeGroupBlockLift
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodIdempotentFixesOfOnlySeriesOfLabelActs
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroInertia
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeilDeligneParamAboveLIndependentLocalEmbedding
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ContMapRepIotaOQ
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations

noncomputable section

namespace GlobalTheory.Pst.PstBridge

open GlobalTheory.Pst GlobalTheory.Pst.BridgeParam Formalism.MainNotions.N Module

section Rank

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) {LL : Type} [Field LL] [Algebra ℚ_[l] LL]
  {V : Type} [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V]

theorem rank_le_of_conj {K K' : FinExt l} {g : GQ l} {ρ : Representation LL ↥(GK K) V}
    {ρ' : Representation LL ↥(GK K') V}
    (hρ : ∀ (h : ↥(GK K)) (h' : ↥(GK K')), (h' : GQ l) = g * h * g⁻¹ → ρ' h' = ρ h)
    (hK : ∀ x, x ∈ K.1 ↔ g x ∈ K'.1) :
    Module.rank ↥(MaximalUnramifiedExtension l) (DpstUr P ρ) ≤ Module.rank ↥(MaximalUnramifiedExtension l) (DpstUr P ρ') := by
  have hρ' : ∀ (h' : ↥(GK K')) (h : ↥(GK K)), (h : GQ l) = g⁻¹ * h' * g⁻¹⁻¹ → ρ h = ρ' h' :=
    fun h' h hh => (hρ h h' (by rw [hh]; group)).symm
  have hK' : ∀ x, x ∈ K'.1 ↔ g⁻¹ x ∈ K.1 := fun x => by
    rw [hK, show g (g⁻¹ x) = x from g.apply_symm_apply x]
  let i : ↥(MaximalUnramifiedExtension l) → ↥(MaximalUnramifiedExtension l) := fun c => ⟨g c, (BridgeInd.mem_Kur_iff g _).1 c.2⟩
  have hi : Function.Surjective i := fun c =>
    ⟨⟨g⁻¹ c, (BridgeInd.mem_Kur_iff g _).2 (by rw [show g (g⁻¹ (c : Om l)) = c from g.apply_symm_apply _]; exact c.2)⟩,
      Subtype.ext (g.apply_symm_apply _)⟩
  let j : DpstUr P ρ →+ DpstUr P ρ' :=
    (toUr P ρ').toAddMonoidHom.comp ((conjD P hρ hK).toAddMonoidHom.comp (toUr P ρ).symm.toAddMonoidHom)
  have hj : Function.Injective j := by
    intro x y hxy
    have hx : ∀ z : ↥(Dpst P ρ), conjD P hρ' hK' (conjD P hρ hK z) = z := fun z =>
      Subtype.ext (by
        have := LinearMap.congr_fun (conjV_conjV_inv P (LL := LL) (V := V) g⁻¹) z.1
        rw [inv_inv] at this
        exact this)
    have := congrArg (conjD P hρ' hK') hxy
    exact (hx x).symm.trans (this.trans (hx y))
  refine rank_le_of_surjective_injective i j hi hj fun c x => ?_
  exact conjD_mulD P hρ hK c (i c) rfl x

end Rank

theorem isPstAt_indep_bridge : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (O O' : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] [CommRing O'] [Algebra ℤ_[l] O'] [TopologicalSpace O'] (Bw : LocBridge l E Ω (Dec (F := E) A) O) (Bw' : LocBridge l E Ω (Dec (F := E) A) O'), GlobalTheory.Pst.Induces Bw → GlobalTheory.Pst.Induces Bw' → ∀ (a : ℕ) (r : ↥(Dec (F := E) A) →* GL (Fin a) (Om l)), Continuous (fun g => ((r g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l))) → GlobalTheory.Pst.IsPstAt P Bw r → GlobalTheory.Pst.IsPstAt P Bw' r := by
  intro l _ P AI _ E Ω _ _ _ _ _ A O O' _ _ _ _ _ _ Bw Bw' hj hj' a r _ hr
  obtain ⟨L₁, r₁, hm₁, hV₁⟩ := hr
  let L₂ : FinExt l := supExt L₁ Bw'.LL
  have h₁ : L₁.1 ≤ L₂.1 := le_sup_left
  have h₂ : Bw'.LL.1 ≤ L₂.1 := le_sup_right
  let r₂ := mapRep (IntermediateField.inclusion h₁).toRingHom r₁
  have hW := GlobalTheory.PstExt.isPst_enlarge P Bw h₁ r₁ hV₁
  obtain ⟨g, hg, hK⟩ := BridgeInd.exists_conj Bw Bw' hj hj'
  have hρ := BridgeInd.repE_conj Bw Bw' hg L₂ r₂
  refine ⟨L₂, r₂, ⟨h₂, ?_⟩, ?_⟩
  · rw [← hm₁.2]
    ext x i k
    rfl
  · have e1 := rank_le_of_conj P hρ hK
    have hρ' : ∀ (h' : ↥(GK Bw'.Kw)) (h : ↥(GK Bw.Kw)), (h : GQ l) = g⁻¹ * h' * g⁻¹⁻¹ →
        Bw.repE L₂ r₂ h = Bw'.repE L₂ r₂ h' :=
      fun h' h hh => (hρ h h' (by rw [hh]; group)).symm
    have hK' : ∀ x, x ∈ Bw'.Kw.1 ↔ g⁻¹ x ∈ Bw.Kw.1 := fun x => by
      rw [hK, show g (g⁻¹ x) = x from g.apply_symm_apply x]
    have e2 := rank_le_of_conj P hρ' hK'
    unfold IsPst at hW ⊢
    rw [← hW]
    exact le_antisymm e2 e1

end GlobalTheory.Pst.PstBridge
