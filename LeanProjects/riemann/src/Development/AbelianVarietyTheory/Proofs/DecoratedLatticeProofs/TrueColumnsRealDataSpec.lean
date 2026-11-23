import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PinColL
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PsiTContinuous
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueColumnStepsAreStandardHermitianPairsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCharExponentInfinityKernelShiftStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsTupleChainAdelicDataStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueColumnsBranchingMapEquivariantNonzeroCommonStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastGroupEmbeddingRealComponentsBlockFormStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000

namespace GlobalTheory.RealTrue

theorem ontoUni_reindex {ι K : Type} [Group K] [TopologicalSpace K] {a b : ℕ} (h : a = b)
    {r : K → ι → Matrix (Fin a) (Fin a) ℂ} (hr : OntoUni r) :
    OntoUni fun k τ => (r k τ).reindex (finCongr h) (finCongr h) := by
  subst h; simpa using hr

theorem ontoUni_one {ι K : Type} [Group K] [TopologicalSpace K] {a : ℕ}
    {r : K → ι → Matrix (Fin a) (Fin a) ℂ} (hr : OntoUni r) (τ : ι) : r 1 τ = 1 := by
  have hm := hr.mul 1 1 τ
  rw [mul_one] at hm
  have hu := Matrix.mem_unitaryGroup_iff'.1 (hr.uni 1 τ)
  calc r 1 τ = (star (r 1 τ) * r 1 τ) * r 1 τ := by rw [hu, Matrix.one_mul]
    _ = star (r 1 τ) * (r 1 τ * r 1 τ) := Matrix.mul_assoc _ _ _
    _ = 1 := by rw [← hm, hu]

theorem inN_one {D : D7} (θ : InfFam D) (V : HSp D) {n : ℕ} (hn : V.rank = n) (g : GA D V) (τ : D.what₂.Tau) :
    inN θ V (fun _ => 1) hn g τ = infM θ V hn g τ := by
  simp [inN, GlobalTheory.SeeSaw.inB, infM]

theorem valC_transport {ι : Type} [Fintype ι] {n : ℕ} {G G' : ι → Matrix (Fin n) (Fin n) ℂ} (h : G = G')
    (lam : ι → DomWeight n) (f : Formalism.L2.Forms.Frames G → ℂ) (hf : f ∈ ValC G lam) :
    (fun z : Formalism.L2.Forms.Frames G' => f ⟨z.1, z.2⟩) ∈ ValC G' lam := by
  subst h; exact hf

end GlobalTheory.RealTrue

open GlobalTheory.RealTrue in

theorem GlobalTheory.AdForm.realOf_is : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {F : FamIn (I.rec7 l Z).what₂.LL G Pl0 T (I.rec7 l Z).R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks (I.rec7 l Z).what₂.LL] (R : RealDat (I.rec7 l Z) F Ks) (g : GlobalTheory.Fam.Geo (I.rec7 l Z)) (c₀ s : ℕ → ℂ) J, PinX I l Z R.ψ R.θ g.x g.vac c₀ → ∀ j : SmT R.MX →ₗ[ℂ] (FrP (I.rec7 l Z) → ℂ), GlobalTheory.Core.Rk.Top.IsJ u R.MX j → JOf R j J → IsEmbTop (D := (I.rec7 l Z)) (TC.z0 X u) ((g.oT B.R.m rfl).emb.comp (MonoidHom.inl _ _)) → (realOf u R g s J).Is := by
  intro B X I hOk hPins l Z u G _ _ Pl0 T F Ks _ _ _ R g c₀ s J hX j hJ hJO hEmb
  have hstd := GlobalTheory.T.trueColumnSteps_are_standardHermitianPairs I hOk hPins l Z R.ψ R.θ hX.std hX.inf
  have hm2 : 2 ≤ B.R.m := B.R.two_le_m
  have hgX : ∀ i, i ≤ B.R.m → ((I.rec7 l Z).sp.X i).gram = 1 := by
    intro i hi
    rcases Nat.lt_or_ge i B.R.m with h | h
    · exact (hstd.1 i h).gS
    · obtain rfl : i = B.R.m := le_antisymm hi h
      have := (hstd.1 (B.R.m - 1) (by omega)).gT
      rwa [show B.R.m - 1 + 1 = B.R.m by omega] at this
  have hrk : ∀ i, i < B.R.m → 0 < B.R.N i ∧ B.R.N i ≤ B.R.N (i + 1) := by
    intro i hi
    have h := (hstd.1 i hi).rk
    rw [rankN (I.rec7 l Z) i hi.le, rankN (I.rec7 l Z) (i + 1) hi] at h
    exact ⟨h.1, h.2.1.le⟩
  have huni : ∀ i (hi : i ≤ B.R.m), OntoUni fun k : GinfC ((I.rec7 l Z).sp.X i) => (realOf u R g s J).r i hi k.1 := by
    intro i hi
    have hB := (hX.xs i hi).2.1
    have := GlobalTheory.SeeSaw.ontoUni_inB (I.rec7 l Z) R.θ ((I.rec7 l Z).sp.X i) (g.x i).B hX.inf (fun τ => by
      rw [hB]; simp [gramAt, hgX i hi])
    exact ontoUni_reindex (rankN (I.rec7 l Z) i hi) this
  have huniT : OntoUni fun k : GinfC (I.rec7 l Z).sp.X' => (realOf u R g s J).rT k.1 := by
    have := GlobalTheory.SeeSaw.ontoUni_inB (I.rec7 l Z) R.θ (I.rec7 l Z).sp.X' (fun _ => 1) hX.inf (fun τ => by
      simp [gramAt, hstd.2.1])
    exact ontoUni_reindex (rankP (I.rec7 l Z)) this
  have hrT : ∀ k, (realOf u R g s J).rT k = infM R.θ _ (rankP (I.rec7 l Z)) k := fun k => funext fun τ => inN_one _ _ _ _ _
  have hone : ∀ τ, infM R.θ _ (rankP (I.rec7 l Z)) 1 τ = 1 := by
    intro τ
    have := ontoUni_one huniT τ
    rw [← hrT]; exact this
  have htr1 : ∀ z : FrN (I.rec7 l Z) (B.R.N B.R.m - 1), IsTr (infM R.θ _ (rankP (I.rec7 l Z)) 1) z z := by
    intro z τ; rw [hone, Matrix.one_mul]
  have hJ1 : ∀ v, J v 1 = fun z => j v ⟨z.1, z.2⟩ := fun v => funext fun z => hJO v 1 (Subgroup.one_mem _) z z (htr1 z)
  have hG : gramC (gramP (I.rec7 l Z)) (Formalism.L2.Forms.embT (I.rec7 l Z)) = fun _ => 1 := by
    funext τ; simp [gramC, gramP, hstd.2.1]
  refine ⟨huni, ?_, hrk, ?_, ?_, ?_, ?_⟩
  · exact huniT
  · intro i τ
    simp only [realOf]
    split_ifs with h
    · exact one_ne_zero
    · exact div_ne_zero h (hstd.2.2.2.1 τ)
  · intro i hi τ
    obtain ⟨Ch, _, A, hA, -⟩ := GlobalTheory.T.exists_tupleChain_adelicData I hOk hPins l Z u I.mu0
    obtain ⟨e, -, he⟩ := GlobalTheory.T.exists_charExponent_infinity_kernel_shift I hOk hPins l Z u I.mu0 Ch A hA i hi
    exact Int.toNat_of_nonneg (he τ).2.2
  · intro v
    refine ⟨?_, fun k hk z z' hz => ?_⟩
    · show J v 1 ∈ ValC _ (sgT (D := I.rec7 l Z) u)
      rw [hJ1 v]
      have hm : j v ∈ ValC (gramC (gramP (I.rec7 l Z)) (Formalism.L2.Forms.embT (I.rec7 l Z))) (sgT (D := I.rec7 l Z) u) := by
        rw [← hJ.range]; exact LinearMap.mem_range_self j v
      exact valC_transport hG _ _ hm
    · rw [hrT] at hz
      show J v k z' = J v 1 z
      rw [hJO v k hk z z' hz, hJO v 1 (Subgroup.one_mem _) z z (htr1 z)]
  · intro n hn
    subst hn
    have hN : B.R.N B.R.m = (B.R.N B.R.m - 1) + 1 := by
      have := hrk (B.R.m - 1) (by omega)
      rw [show B.R.m - 1 + 1 = B.R.m by omega] at this
      omega
    obtain ⟨h1, h2, h3, -⟩ := GlobalTheory.T.trueColumns_branchingMap_equivariant_nonzero_common I hOk hPins l Z u hN
    refine ⟨hN, h1, h2, h3, ?_⟩
    intro k hk τ
    have hb := GlobalTheory.T.lastGroup_embedding_real_components_block_form I hOk hPins l Z u R.θ hX.inf _ hN hEmb k τ
    have hB := (hX.xs B.R.m le_rfl).2.1
    show GlobalTheory.BranchFormula.IsBlock hN (inN R.θ _ (g.x B.R.m).B (rankN (I.rec7 l Z) B.R.m le_rfl) ((g.oT B.R.m rfl).emb (k, 1)) τ) (inN R.θ _ (fun _ => 1) (rankP (I.rec7 l Z)) k τ) 1
    rw [hB]
    first
      | simpa only [inN_one] using hb
      | simpa [inN, GlobalTheory.SeeSaw.inB, infM] using hb
