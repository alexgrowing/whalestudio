import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriHeckeInjectivity.HeckeInj
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.ExCusp
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.ExSummand
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.NormIff
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.IsoEq
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.SSatIff
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.SInfIff
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PStringStepB
import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.JacquetShalikaRigidity

open MeasureTheory NumberField IsDedekindDomain Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Global GroundTheory.Global.SemiLocal
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq
open GlobalTheory.CuspRep UpperTheory.V.Published
open scoped ComplexConjugate Classical

open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E

private theorem transfer {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a b : ℕ}
    {μ : Measure (normOneGL E a)} [μ.IsHaarMeasure] {μ' : Measure (normOneGL E b)} [μ'.IsHaarMeasure]
    {π : CuspSub E a} {π' : CuspSub E b} {V : Submodule ℂ (LL μ)} {V' : Submodule ℂ (LL μ')}
    (h : Dp.Carries μ π V) (h' : Dp.Carries μ' π' V')
    (e : (⟨a, CG.mk π⟩ : Σ c, CG E c) = ⟨b, CG.mk π'⟩) :
    a = b ∧ ∀ S m B, At μ' S V' m B → At μ S V m B := by
  obtain ⟨rfl, e2⟩ := Sigma.mk.inj_iff.1 e
  obtain rfl : π = π' := (Dp.isoEq E a π π').1 (Quotient.exact (eq_of_heq e2))
  refine ⟨rfl, fun S m B hA => ⟨fun τ => ?_, fun w hw => ?_⟩⟩
  · exact (Dp.sInfIff E a μ π V h τ _).2 ((Dp.sInfIff E a μ' π V' h' τ _).1 (hA.1 τ))
  · exact (Dp.sSatIff E a μ π V h w _).2 ((Dp.sSatIff E a μ' π V' h' w _).1 (hA.2 w hw))

private theorem core {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {ι κ : Type} [Fintype ι] [Fintype κ]
    (d : ι → ℕ) (d' : κ → ℕ) (hd : ∀ i, 0 < d i) (hd' : ∀ j, 0 < d' j)
    (μ : ∀ i, Measure (normOneGL E (d i))) [∀ i, (μ i).IsHaarMeasure]
    (μ' : ∀ j, Measure (normOneGL E (d' j))) [∀ j, (μ' j).IsHaarMeasure]
    (V : ∀ i, Submodule ℂ (LL (μ i))) (V' : ∀ j, Submodule ℂ (LL (μ' j)))
    (hV : ∀ i, IsSummand (μ i) (V i)) (hV' : ∀ j, IsSummand (μ' j) (V' j)) (S : Set (Pl E)) (hS : S.Finite)
    (lam : ι → ℂ) (B : ι → Pl E → Multiset ℂ) (B' : κ → Pl E → Multiset ℂ)
    (hB : ∀ i, ∀ w ∉ S, SSat (μ i) (V i) w (B i w)) (hB' : ∀ j, ∀ w ∉ S, SSat (μ' j) (V' j) w (B' j w))
    (e : ∀ w ∉ S, ∑ j, B' j w = ∑ i, (B i w).map (· * (Ideal.absNorm w.asIdeal : ℂ) ^ (-lam i))) :
    ∃ s : ι ≃ κ, ∀ i, d i = d' (s i) ∧ ∀ S m C, At (μ' (s i)) S (V' (s i)) m C → At (μ i) S (V i) m C := by
  choose π hπ using fun i => (Dp.exCusp E (d i) (μ i) (V i) (hV i)).exists
  choose π' hπ' using fun j => (Dp.exCusp E (d' j) (μ' j) (V' j) (hV' j)).exists
  have hn : ∀ i, GlobalTheory.DiscSpec.IsNormalised (π i) := fun i =>
    (Dp.normIff E _ _).2 ((Dp.exSummand E _ _ _ _).1 (hπ i)).1
  have hn' : ∀ j, GlobalTheory.DiscSpec.IsNormalised (π' j) := fun j =>
    (Dp.normIff E _ _).2 ((Dp.exSummand E _ _ _ _).1 (hπ' j)).1
  obtain ⟨s, hs⟩ := PositivityTheory.AdelicQuotientData.jacquetShalikaRigidity E ι κ d d'
    (fun i => (CG.mk (π i)).twist (GlobalTheory.CuspRep.Model.absC E (lam i)))
    (fun j => (CG.mk (π' j)).twist (GlobalTheory.CuspRep.Model.absC E 0)) hd hd' (by
    filter_upwards [hS.compl_mem_cofinite] with w hw
    choose A hA hA1 using fun i => (Dp.sSatIff E _ (μ i) (π i) (V i) (hπ i) w _).1 (hB i w hw)
    choose A' hA' hA1' using fun j => (Dp.sSatIff E _ (μ' j) (π' j) (V' j) (hπ' j) w _).1 (hB' j w hw)
    refine ⟨fun i => (A i).map (· * (GlobalTheory.CuspRep.Model.absC E (lam i)).val w), A',
      fun i => PositivityTheory.Rg.Rs.StrStepB.hasSat_twist_absC (π i) (hA1 i) (lam i), fun j => ?_, ?_⟩
    · rw [PositivityTheory.Rg.Rs.StrStepB.absC_zero, CG.twist_one]
      exact hA1' j
    · apply Multiset.map_injective (f := fun b : ℂˣ => (b : ℂ)) (fun a b e => Units.ext e)
      have h1 := map_sum (Multiset.mapAddMonoidHom fun b : ℂˣ => (b : ℂ)) A' Finset.univ
      have h2 := map_sum (Multiset.mapAddMonoidHom fun b : ℂˣ => (b : ℂ))
        (fun i => (A i).map (· * (GlobalTheory.CuspRep.Model.absC E (lam i)).val w)) Finset.univ
      refine h2.trans (Eq.trans ?_ h1.symm)
      have h3 := e w hw
      simp only [hA, hA'] at h3
      refine Eq.trans ?_ h3.symm
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Multiset.coe_mapAddMonoidHom, Multiset.map_map, Function.comp_def, Units.val_mul,
        PositivityTheory.Rg.Rs.StrStepB.absC_val])
  exact ⟨s, fun i => transfer (hπ i) (hπ' (s i))
    (PositivityTheory.Rg.Rs.StrStepB.match_twist (hd i) _ _ (hn i) (hn' _) (hs i)).2⟩

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E.rigidE :
    RigidE := by
  intro E _ _ _ τ₁ τ₂ hP S hS m₁ m₂ B₁ B₂ h₁ h₂
  have hs : ∀ j : Fin 2, IsSummand (BW.mu1 E 2) (![τ₁, τ₂] j) := by
    intro j
    fin_cases j
    · exact ⟨hP.irr₁.le, hP.irr₁.closed, hP.irr₁.inv, hP.irr₁.ne, hP.irr₁.irr⟩
    · exact ⟨hP.irr₂.le, hP.irr₂.closed, hP.irr₂.inv, hP.irr₂.ne, hP.irr₂.irr⟩
  have hB : ∀ j : Fin 2, ∀ w ∉ S, SSat (BW.mu1 E 2) (![τ₁, τ₂] j) w (![B₁, B₂] j w) := by
    intro j
    fin_cases j
    · exact h₁.2
    · exact h₂.2
  constructor
  · rintro b ⟨lam, m, B, hA, -, hw⟩
    obtain ⟨s, h⟩ := core b.d (fun _ : Fin 2 => 2) b.pos (fun _ => two_pos) b.μ (fun _ => BW.mu1 E 2) b.V ![τ₁, τ₂]
      b.summand hs S hS lam B ![B₁, B₂] (fun i => (hA i).2) hB fun w hS' => by
        rw [Fin.sum_univ_two]; exact hw w hS'
    refine ⟨by simpa using Fintype.card_congr s, fun i => (h i).1, s.symm 0, s.symm 1,
      s.symm.injective.ne (by decide), (h _).2 _ _ _ ?_, (h _).2 _ _ _ ?_⟩
    · rw [s.apply_symm_apply]; exact h₁
    · rw [s.apply_symm_apply]; exact h₂
  · intro μ _ V hV hA
    obtain ⟨s, -⟩ := core (fun _ : Unit => 2 + 2) (fun _ : Fin 2 => 2) (fun _ => by norm_num) (fun _ => two_pos)
      (fun _ => μ) (fun _ => BW.mu1 E 2) (fun _ => V) ![τ₁, τ₂] (fun _ => hV) hs S hS (fun _ => 0)
      (fun _ w => B₁ w + B₂ w) ![B₁, B₂] (fun _ => hA.2) hB fun w _ => by simp
    simpa using Fintype.card_congr s
