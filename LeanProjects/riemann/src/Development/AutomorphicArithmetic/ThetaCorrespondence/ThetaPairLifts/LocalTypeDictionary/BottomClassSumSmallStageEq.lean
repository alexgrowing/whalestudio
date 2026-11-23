import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BottomTriangleNonzeroConstantFirst
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BottomFiniteLevelFixed
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.KerMinorMulRealOfRealInvariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BottomTriangleNonzeroConstantFirstStatement

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.BotClassSumSmall
open scoped ComplexOrder
set_option maxHeartbeats 4000000 in
theorem classSum_smallStage : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
    (∀ D, GlobalTheory.NormSum.Inp D) → GlobalTheory.SqTop.BotSmall →
    GlobalTheory.SqTop.GBig fun {D} T _ _ G _ _ _ _ => ∀ (W : G.Weil), IsStdChar D W.ψ (-1) → ∀ (i j : Fin D.R.m) (A A' WW : HSp D)
      (X : Tri T A A' WW) (δ t0 : ℂ), IsBottomTri W i j X →
      ∃ Ω₁ : ℂ, Ω₁ ≠ 0 ∧ ∀ (s : T) (Q : ℕ) (P P' : Pair D ⊤ δ t0 Q), IsBottom G s i j (GlobalTheory.SqTop.modT G s) P P' →
        ∀ (ea : P'.a = A'.rank) (ed : P'.d = WW.rank) (h : GA D P'.d) (g : GA D WW), GlobalTheory.BotFormula.IsFinPt WW g h →
          ∀ (gx : GlobalTheory.NormSum.Cls D P'.a (GlobalTheory.NormSum.intG D P'.a) → GA D A'),
            (∀ x, GlobalTheory.BotFormula.IsFinPt A' (gx x) x.out) → ∀ T' : Tup D P'.a P'.d P'.n,
              X.I' W.ψ W.θ s (GlobalTheory.BotFormula.minorF ea ed T') g =
                Ω₁ * ∑ᶠ x, ((GlobalTheory.NormSum.gam D (GlobalTheory.NormSum.intG D P'.a) x.out : ℂ))⁻¹ *
                  X.ker' W.ψ W.θ s (GlobalTheory.BotFormula.minorF ea ed T') g (gx x) := by
  intro hPr hK hM hI hB
  obtain ⟨c1, h1⟩ := _root_.GlobalTheory.T.bottom_layer_finite_level hPr hK hM hI hB
  obtain ⟨c2, h2⟩ := _root_.GlobalTheory.T.minor_kernel_real_invariant hPr hK hM hI hB
  refine ⟨max c1 c2, fun ε CF hCF => ?_⟩
  obtain ⟨C1, x1, h1⟩ := h1 ε CF (le_trans (le_max_left _ _) hCF)
  obtain ⟨C2, x2, h2⟩ := h2 ε CF (le_trans (le_max_right _ _) hCF)
  refine ⟨max C1 C2, max x1 x2, fun C hC0 D large₂ he hx hR T Lc μ₀ hL G => ?_⟩
  have h1 := h1 C (le_trans (le_max_left _ _) hC0) D large₂ he (le_trans (le_max_left _ _) hx) hR T Lc μ₀ hL G
  have h2 := h2 C (le_trans (le_max_right _ _) hC0) D large₂ he (le_trans (le_max_right _ _) hx) hR T Lc μ₀ hL G
  intro W hψ i j A A' WW X δ t0 hX
  obtain ⟨hJo, hJc⟩ := openCompact X hX.std'
  haveI : X.m'.IsHaarMeasure := hX.is.meas'.1
  have hJtop : X.m' ((Formalism.L2.DIV.St X.rA'.β).comap (Lev.finE A') : Subgroup (GA D A')) ≠ ⊤ := hJc.measure_lt_top.ne
  have hJ0 : X.m' ((Formalism.L2.DIV.St X.rA'.β).comap (Lev.finE A') : Subgroup (GA D A')) ≠ 0 :=
    (hJo.measure_pos X.m' ⟨1, Subgroup.one_mem _⟩).ne'
  refine ⟨((X.m' ((Formalism.L2.DIV.St X.rA'.β).comap (Lev.finE A') : Subgroup (GA D A'))).toReal : ℂ),
    by exact_mod_cast (ENNReal.toReal_pos hJ0 hJtop).ne', fun s Q P P' hP ea ed h g hg gx hgx T' => ?_⟩
  obtain ⟨hu, hcard⟩ := GlobalTheory.T.standardLattice_doubleCosetClasses_stabilisers A' X.rA' hX.is.rigA' hX.std' ea gx hgx
  haveI : Finite (GlobalTheory.NormSum.Cls D P'.a (GlobalTheory.NormSum.intG D P'.a)) := (GlobalTheory.NormSum.cls_finite_card_le D P'.a).1
  letI : Fintype (GlobalTheory.NormSum.Cls D P'.a (GlobalTheory.NormSum.intG D P'.a)) := Fintype.ofFinite _
  have hfin : ∀ x, {γ : GA D A' | γ ∈ GQ A' ∧
      (gx x)⁻¹ * γ * gx x ∈ ((Formalism.L2.DIV.St X.rA'.β).comap (Lev.finE A') : Subgroup (GA D A'))}.Finite := fun x => by
    have h1 := GlobalTheory.InnerClassSum.finite_stab_of_measure X.m' (GQ A') _ hX.is.meas'.2 hJ0 hJtop (gx x)
    have him : {γ : GA D A' | γ ∈ GQ A' ∧
        (gx x)⁻¹ * γ * gx x ∈ ((Formalism.L2.DIV.St X.rA'.β).comap (Lev.finE A') : Subgroup (GA D A'))} =
        Subtype.val '' {γ : GQ A' | (gx x)⁻¹ * (γ : GA D A') * gx x ∈
          ((Formalism.L2.DIV.St X.rA'.β).comap (Lev.finE A') : Subgroup (GA D A'))} := by
      ext γ
      simp only [Set.mem_setOf_eq, Set.mem_image, Subtype.exists, exists_and_right, exists_eq_right]
      exact ⟨fun h => ⟨h.1, h.2⟩, fun ⟨h, h'⟩ => ⟨h, h'⟩⟩
    rw [him]
    exact h1.image _
  have hl := GlobalTheory.SqTower.Normal.ker'_left hX.is s (GlobalTheory.BotFormula.minorF ea ed T') g
  have hr : ∀ k ∈ ((Formalism.L2.DIV.St X.rA'.β).comap (Lev.finE A') : Subgroup (GA D A')), ∀ x,
      X.ker' W.ψ W.θ s (GlobalTheory.BotFormula.minorF ea ed T') g (x * k) = X.ker' W.ψ W.θ s (GlobalTheory.BotFormula.minorF ea ed T') g x := by
    rw [GlobalTheory.Mass.Levels.comap_finE]
    refine GlobalTheory.DefiniteClassSum.invariant_sup ?_ ?_
    · intro k hk x
      obtain ⟨hk1, -⟩ := Lev.mem_levA.1 hk
      have hW : IsWeilDatumO W.ψ A' WW _ _ (X.ω' s) := hX.is.weil' s
      have hf' : IsThetaFunO W.ψ A' WW (X.f' s) :=
        GlobalTheory.GalLift.Vec.theta_of_thetaAt hX.is.isVac.1 hX.is.isVac.2.inf (hX.is.snd s) hX.is.isVac'.2.theta
      show X.ω' s (x * k, g) _ 0 = X.ω' s (x, g) _ 0
      have e : ((x * k, g) : GA D A' × GA D WW) = (x, g) * (k, 1) := by simp
      rw [e, map_mul, Module.End.mul_apply, GlobalTheory.OrientedHeis.om_fin_pureTensorO W.ψ A' WW _ _ _ hW W.θ hX.is.isVac'.2.inf k hk1 1
        (GfC WW).one_mem _ _ _ _ _ _ hf', h1 W hψ i j A A' WW X hX s k hk]
    · intro k hk x
      exact h2 W hψ i j A A' WW X δ t0 hX s Q P P' hP ea ed T' g k hk x
  obtain ⟨-, -, heq⟩ := GlobalTheory.Ker.integral_fundamentalDomain_eq_sum_doubleCoset (GA D A') X.m' (GQ A') _ X.fd' hX.is.meas'.2 hJo hJtop
    _ gx hu hfin _ hl hr
  rw [Tri.I', heq, finsum_eq_sum_of_fintype]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [hcard x]
end GlobalTheory.BotClassSumSmall
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bottom_classSum_smallStage_eq : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
    (∀ D, GlobalTheory.NormSum.Inp D) → GlobalTheory.SqTop.BotSmall →
    GlobalTheory.SqTop.GBig fun {D} T _ _ G _ _ _ _ => ∀ (W : G.Weil), IsStdChar D W.ψ (-1) → ∀ (i j : Fin D.R.m) (A A' WW : HSp D)
      (X : Tri T A A' WW) (δ t0 : ℂ), IsBottomTri W i j X →
      ∃ Ω₁ : ℂ, Ω₁ ≠ 0 ∧ ∀ (s : T) (Q : ℕ) (P P' : Pair D ⊤ δ t0 Q), IsBottom G s i j (GlobalTheory.SqTop.modT G s) P P' →
        ∀ (ea : P'.a = A'.rank) (ed : P'.d = WW.rank) (h : GA D P'.d) (g : GA D WW), GlobalTheory.BotFormula.IsFinPt WW g h →
          ∀ (gx : GlobalTheory.NormSum.Cls D P'.a (GlobalTheory.NormSum.intG D P'.a) → GA D A'),
            (∀ x, GlobalTheory.BotFormula.IsFinPt A' (gx x) x.out) → ∀ T' : Tup D P'.a P'.d P'.n,
              X.I' W.ψ W.θ s (GlobalTheory.BotFormula.minorF ea ed T') g =
                Ω₁ * ∑ᶠ x, ((GlobalTheory.NormSum.gam D (GlobalTheory.NormSum.intG D P'.a) x.out : ℂ))⁻¹ *
                  X.ker' W.ψ W.θ s (GlobalTheory.BotFormula.minorF ea ed T') g (gx x) := by
  first | exact @_root_.GlobalTheory.BotClassSumSmall.classSum_smallStage | exact _root_.GlobalTheory.BotClassSumSmall.classSum_smallStage | (intros; apply _root_.GlobalTheory.BotClassSumSmall.classSum_smallStage <;> assumption)
end
