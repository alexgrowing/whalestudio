import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRepApply
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Formalism.LocalToGlobal.Divisibility.TrivialExtensionSideWellFormed
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SpanImageMaxGenEigenspace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpanImageInfOfLinearIndependent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIxOfMemEigAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RangeAdjointLeSpanGoodBlockStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OperatorFamilyAdjointLiftSingleEigensystemStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalOfRowTestOfScalar
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClassPresExtMemExtBijIsom
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)

namespace GlobalTheory.Div

theorem span_range_comp_basis {K V W ι : Type} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module ℂ W]
    (σ : K →+* ℂ) (j : V →ₛₗ[σ] W) (b : Module.Basis ι K V) :
    Submodule.span ℂ (Set.range fun k => j (b k)) = Submodule.span ℂ (Set.range j) := by
  refine le_antisymm (Submodule.span_mono (Set.range_subset_iff.2 fun k => ⟨b k, rfl⟩)) ?_
  rw [Submodule.span_le]
  rintro _ ⟨v, rfl⟩
  have hv : v ∈ Submodule.span K (Set.range b) := b.span_eq ▸ Submodule.mem_top
  induction hv using Submodule.span_induction with
  | mem y hy => obtain ⟨k, rfl⟩ := hy; exact Submodule.subset_span ⟨k, rfl⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add y z _ _ hy hz => rw [map_add]; exact Submodule.add_mem _ hy hz
  | smul a y _ hy => rw [map_smulₛₗ]; exact Submodule.smul_mem _ _ hy

theorem exists_sys_of_mem_span {K V W I ι : Type} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module ℂ W]
    [Finite ι] (σ : K →+* ℂ) (j : V →ₛₗ[σ] W) (b : Module.Basis ι K V) (op : I → Module.End K V)
    (opC : I → Module.End ℂ W) (Z : Submodule K V) (hli : LinearIndependent ℂ (fun k => j (b k)))
    (hsp : Submodule.span ℂ (Set.range j) = ⊤) (hcomm : ∀ i v, j (op i v) = opC i (j v))
    (hpc : Formalism.L2.Col.PairComm op) (hso : Formalism.L2.Col.SplitOver op) (x : I → ℂ) (u : W)
    (hu : ∀ i, opC i u = x i • u) (hu0 : u ≠ 0) (huZ : u ∈ Submodule.span ℂ (j '' (Z : Set V))) :
    ∃ s : I → K, x = (fun i => σ (s i)) ∧
      Formalism.L2.Col.eigAt opC x = Submodule.span ℂ (j '' (Formalism.L2.Col.eigAt op s : Set V)) ∧
      ∃ f, f ≠ 0 ∧ f ∈ Z ∧ f ∈ Formalism.L2.Col.eigAt op s := by
  have hsp' : Submodule.span ℂ (Set.range fun k => j (b k)) = ⊤ := (span_range_comp_basis σ j b).trans hsp
  have key := GlobalTheory.span_image_eigAt_of_basis σ j b op opC hli hsp' hcomm
  have hmem : u ∈ Formalism.L2.Col.eigAt opC x := Formalism.L2.Col.mem_eigAt_of_forall_apply hu
  have hocc : Formalism.L2.Col.Occurs opC x := fun hbot => hu0 ((Submodule.eq_bot_iff _).1 hbot u hmem)
  obtain ⟨s, _, rfl⟩ := key.2.2 hpc hso x hocc
  refine ⟨s, rfl, (key.1 s).symm, ?_⟩
  have hin : u ∈ Submodule.span ℂ (j '' ((Z ⊓ Formalism.L2.Col.eigAt op s : Submodule K V) : Set V)) := by
    rw [← GlobalTheory.span_image_inf_of_linearIndependent σ j b hli]
    exact ⟨huZ, (key.1 s) ▸ hmem⟩
  by_contra hcon
  push_neg at hcon
  apply hu0
  have hle : Submodule.span ℂ (j '' ((Z ⊓ Formalism.L2.Col.eigAt op s : Submodule K V) : Set V)) ≤ ⊥ := by
    rw [Submodule.span_le]
    rintro _ ⟨y, hy, rfl⟩
    by_cases hy0 : y = 0
    · subst hy0; simp
    · exact absurd hy.2 (hcon y hy0 hy.1)
  exact (Submodule.mem_bot ℂ).1 (hle hin)

theorem map_le_span_image {K V W H : Type} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module ℂ W]
    [AddCommGroup H] [Module ℂ H] {σ : K →+* ℂ} (j : V →ₛₗ[σ] W) (Θ : H →ₗ[ℂ] W) (E : Submodule ℂ H)
    (A B : Submodule K V) (h : ∀ v ∈ E, Θ v ∈ Submodule.span ℂ (j '' (A : Set V))) (hAB : A ≤ B) :
    E.map Θ ≤ Submodule.span ℂ (j '' (B : Set V)) := by
  rw [Submodule.map_le_iff_le_comap]
  intro v hv
  exact Submodule.span_mono (Set.image_mono hAB) (h v hv)

set_option maxHeartbeats 400000 in

theorem carries_of_eEc_ne_bot : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, GlobalTheory.Chain.LiftInteg D → A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → SchurAll R.toRealDat → (∀ P, Good R.toRealDat A3.A.μ0 P → conjPl P = P → TwoSided R.toRealDat A3.A.μ0 P) → ((∀ t (k : A3.okI t × List ℕ), A3.heckeRI t k = 0 ∨ ∃ y, Formalism.L2.Col.InertTypeOk (A3.A.fam.R t).n y ∧ A3.heckeRI t k = A3.heckeRI t (k.1, y)) ∧ ∀ j t (k : A3.okI t × List ℕ), A3.heckeLI j t k = 0 ∨ ∃ y, Formalism.L2.Col.InertTypeOk (A3.A.fam.L j t).n y ∧ A3.heckeLI j t k = A3.heckeLI j t (k.1, y)) → R.PGEquiv F → Nonempty A3.fam3.base3.Ix → (∀ c, R.EEc c ≠ ⊥ → ∃ p, R.Carries p c) := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F s hLI hOk hCW hEx hSch hTw hHk hPG hIx c hc
  obtain ⟨Tc, hTc, hx⟩ := GlobalTheory.T.operatorFamily_adjointLift_single_eigensystem R F hLI hOk hCW hEx hSch hTw hHk
  obtain ⟨x, hxc⟩ := hx c
  by_cases h0 : ∀ w ∈ R.EEc c, LinearMap.adjoint (R.Th A3.A.μ0) w = 0
  · obtain ⟨p⟩ := hIx
    refine ⟨p, hc, ?_⟩
    rewrite [Submodule.map_le_iff_le_comap]
    intro w hw
    have h := h0 w hw
    simp only [Submodule.mem_comap, h, Submodule.zero_mem]
  push_neg at h0
  obtain ⟨w, hw, hne⟩ := h0
  let b := (A3.A.fam.R A3.A.μ0).S.basis
  let j := R.jX A3.A.μ0
  let op := (A3.rowI A3.A.μ0).opAll
  have hmodels := hCW.base.models
  have hjX := GlobalTheory.OneFormTest.model_jX R.toRealDat hmodels.HX hmodels.jX A3.A.μ0
  have hExt := (GlobalTheory.classPres_extMem_extBij_isom _ _ _ _ _ _ _ _ _ _ (R.B.R A3.A.μ0).pres).2.1
  have h2 : ∀ f, (R.HX A3.A.μ0).e (R.jX A3.A.μ0 f) = (R.B.R A3.A.μ0).pres.extL f := hmodels.jX A3.A.μ0
  have hli0 : LinearIndependent ℂ (fun k => (R.B.R A3.A.μ0).pres.extL ((A3.A.MtildeCSD A3.A.μ0).basis k)) := hExt.1
  have hli : LinearIndependent ℂ (fun k => j (b k)) := by
    refine LinearIndependent.of_comp (R.HX A3.A.μ0).e ?_
    have h3 : ((R.HX A3.A.μ0).e ∘ fun k => j (b k)) =
        fun k => (R.B.R A3.A.μ0).pres.extL ((A3.A.MtildeCSD A3.A.μ0).basis k) := funext fun k => h2 _
    rewrite [h3]
    exact hli0
  have hcomm : ∀ i f, j (op i f) = Tc i (j f) := hTc
  have hpc : Formalism.L2.Col.PairComm op := (hOk.what₂ A3.A.μ0).comm
  have hso : Formalism.L2.Col.SplitOver op := by
    rintro (i | k)
    · exact (hOk.ok2.what₂ A3.A.μ0).split i
    · exact (hOk.what₂ A3.A.μ0).split k
  have hZ := (GlobalTheory.T.range_adjoint_le_span_jX_image_ZHg R F hLI hOk hCW hEx hSch hPG).1 A3.A.μ0
  obtain ⟨s', hxs, heig, f, hf0, hfZ, hfE⟩ := exists_sys_of_mem_span D.what₂.embLL j b op Tc
    ((A3.A.fam.R A3.A.μ0).ZHg A3.A.X) hli hjX.2.2 hcomm hpc hso x (LinearMap.adjoint (R.Th A3.A.μ0) w) (hxc w hw) hne
    (hZ ⟨w, rfl⟩)
  obtain ⟨p, hp⟩ := GlobalTheory.Div.exists_ix_of_mem_eigAt A3 hOk s' f hf0 hfZ hfE
  refine ⟨p, hc, map_le_span_image j (LinearMap.adjoint (R.Th A3.A.μ0)) (R.EEc c) (Formalism.L2.Col.eigAt op s')
    ((A3.rowI A3.A.μ0).inertTypeEigenspaceSum p.1)
    (fun v hv => heig.le (Formalism.L2.Col.mem_eigAt_of_forall_apply (hxc v hv))) (Formalism.L2.Col.eigAt_le_eigSum hp)⟩

end GlobalTheory.Div
