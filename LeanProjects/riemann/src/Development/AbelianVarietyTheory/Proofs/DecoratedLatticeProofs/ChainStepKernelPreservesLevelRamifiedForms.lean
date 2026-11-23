import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SplitPart
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevChiEqOne
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.KmapEq
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PointDeterminantDiamondOperatorInvariant
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DecoratedPointMoveDiamondOperatorEq
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SharpMemRange
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.KernelEntryRationalEquivarianceTransportsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ReferenceTupleOffPrimesEmpty
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.KRamT

open Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem.Col2.TC GlobalTheory.KerDia

section Entry
attribute [local instance] GlobalTheory.Mem.Col2.starE

variable {B : Base} {X : PreX B.toPre}

theorem tr_one {E K ι : Type} [Field E] [NumberField E] [Field K] [Fintype ι] {n : ℕ} (S : GStep E K n)
    (emb : ι → E →+* K) (σ : K →+* ℂ) (b : S.β) (F : Fr emb σ n → ℂ) : S.tr emb σ b 1 F = F := by
  funext y
  simp only [GStep.tr, map_one, trFr_apply, inv_one, Units.val_one, map_one, one_mul]
  exact congrArg F (frMul_one emb σ y)

theorem ent_dia (I : TC B X) (l : I.Laws) (u : B.Word) (a : I.ι) (i : ℕ) {b : (I.stp u a i).β}
    {b' : (I.stp u a (i + 1)).β} (p : (I.stp u a i).D b) (p' : (I.stp u a (i + 1)).D b') (P : (I.atIn u a).ST) (s : (Res P.1)ˣ) :
    ent I l u a i (((I.atIn u a).A i).dia b P s p) (((I.atIn u a).A (i + 1)).dia b' P s p') = ent I l u a i p p' := by
  unfold ent
  rw [(GlobalTheory.KerDia.RhoDia.rho_dia I l u a i b p b' p' P s).1, (GlobalTheory.KerDia.RhoDia.rho_dia I l u a i b p b' p' P s).2,
    GlobalTheory.DiaTheta.th_dia I l u a i b b' p p' P s]

theorem Kmap_stab (I : TC B X) (l : I.Laws) (hI : I.Ok) (u : B.Word) (a : I.ι) (i : ℕ) (hi : i < B.R.m)
    (c : (I.stp u a i).Cl) (c' : (I.stp u a (i + 1)).Cl) (g : (I.stp u a (i + 1)).Stab c')
    (f : Fr B.fields.emb B.embLL (B.R.N i) → ℂ) (hf : f ∈ ValC (Gr B.fields.emb B.embLL (B.R.N i)) (lamT (B.hcW u) i)) :
    (I.stp u a (i + 1)).tr B.fields.emb B.embLL c'.1 g.1 ((I.chain l u a).Kmap i c c' f) = (I.chain l u a).Kmap i c c' f := by
  rw [GlobalTheory.KerDia.Kmap_eq]
  have e3 := GlobalTheory.T.kernelEntry_rationalEquivariance_transports I l hI u a i ((I.stp u a i).rep c) ((I.stp u a (i + 1)).rep c') 1 g.1 f
    (GlobalTheory.KerDia.sharp_mem_range I l u a i hi f hf)
  have hg : (I.stp u a (i + 1)).act c'.1 g.1 ((I.stp u a (i + 1)).rep c') = (I.stp u a (i + 1)).rep c' := g.2
  have h1 : (I.stp u a i).act c.1 1 ((I.stp u a i).rep c) = (I.stp u a i).rep c :=
    @one_smul _ _ _ (GStep.actD _ c.1) _
  rw [h1, hg, tr_one] at e3
  exact e3.symm

theorem K_mem_Fi (I : TC B X) (l : I.Laws) (hI : I.Ok) (u : B.Word) (a : I.ι) (i : ℕ) (hi : i < B.R.m) :
    ∀ φ ∈ (I.stp u a i).Fi B.fields.emb B.embLL (lamT (B.hcW u) i),
      (I.chain l u a).K i φ ∈ (I.stp u a (i + 1)).Fi B.fields.emb B.embLL (lamT (B.hcW u) (i + 1)) := by
  intro φ hφ c'
  let _ := (I.chain l u a).clsFin i
  have hK : (I.chain l u a).K i φ c' = ∑ c, (I.chain l u a).wt i c • (I.chain l u a).Kmap i c c' (φ c) := rfl
  rw [hK]
  refine ⟨Submodule.sum_mem _ fun c _ => Submodule.smul_mem _ _
    (GlobalTheory.AdForm.Keep.kmap_val I l u a i hi c c' _ (hφ c).1), fun g => ?_⟩
  rw [map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [map_smul, Kmap_stab I l hI u a i hi c c' g _ (hφ c).1]

end Entry
end GlobalTheory.KRamT

namespace GlobalTheory.KRamT

open Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem.Col2.TC GlobalTheory.KerDia

section Dia
attribute [local instance] GlobalTheory.Mem.Col2.starE

variable {B : Base} {X : PreX B.toPre}

theorem entry_dia (I : TC B X) (l : I.Laws) (hI : I.Ok) (u : B.Word) (a : I.ι) (i : ℕ) (hi : i < B.R.m)
    (φ : ColT I l u a i) (hφ : φ ∈ (I.fm l u a).Fi i) (v : (I.atT l u a).vT) (s : ((I.atT l u a).Fv v)ˣ)
    (L : (I.chain l u a).cls i) (c' : (I.chain l u a).cls (i + 1)) :
    (I.fm l u a).dilT (i + 1) v s c' ((I.chain l u a).Kmap i ((I.fm l u a).dil i v s L) ((I.fm l u a).dil (i + 1) v s c')
      (φ ((I.fm l u a).dil i v s L))) =
    (I.chain l u a).Kmap i L c' ((I.fm l u a).dilT i v s L (φ ((I.fm l u a).dil i v s L))) := by
  have hφ' : φ ∈ (I.stp u a i).Fi B.fields.emb B.embLL (lamT (B.hcW u) i) := hφ
  change (I.atIn u a).dilT B.fields.emb B.embLL (i + 1) v s c'
      ((I.chain l u a).Kmap i ((I.atIn u a).dil i v s L) ((I.atIn u a).dil (i + 1) v s c')
        (φ ((I.atIn u a).dil i v s L))) =
    (I.chain l u a).Kmap i L c' ((I.atIn u a).dilT B.fields.emb B.embLL i v s L (φ ((I.atIn u a).dil i v s L)))
  have hx : φ ((I.atIn u a).dil i v s L) ∈ ValC (Gr B.fields.emb B.embLL (B.R.N i)) (lamT (B.hcW u) i) :=
    (hφ' ((I.atIn u a).dil i v s L)).1
  rw [Kmap_eq I l u a i _ _, Kmap_eq I l u a i L c']
  unfold AtIn.dilT AtIn.dil GStep.trTo
  have e1 := (I.stp u a i).mv_smul L.1 (((I.atIn u a).A i).diaPt v s L)
  have e2 := (I.stp u a (i + 1)).mv_smul c'.1 (((I.atIn u a).A (i + 1)).diaPt v s c')
  have e3 := GlobalTheory.T.kernelEntry_rationalEquivariance_transports I l hI u a i
    ((I.stp u a i).rep ((I.stp u a i).cl L.1 (((I.atIn u a).A i).diaPt v s L)))
    ((I.stp u a (i + 1)).rep ((I.stp u a (i + 1)).cl c'.1 (((I.atIn u a).A (i + 1)).diaPt v s c')))
    ((I.stp u a i).mv L.1 (((I.atIn u a).A i).diaPt v s L))
    ((I.stp u a (i + 1)).mv c'.1 (((I.atIn u a).A (i + 1)).diaPt v s c')) _
    (GlobalTheory.KerDia.sharp_mem_range I l u a i hi _ hx)
  unfold GStep.act at e3
  rw [e1, e2] at e3
  refine Eq.trans e3.symm ?_
  exact LinearMap.congr_fun (ent_dia I l u a i ((I.stp u a i).rep L) ((I.stp u a (i + 1)).rep c') v s) _

def dilEquiv (I : TC B X) (l : I.Laws) (u : B.Word) (a : I.ι) (i : ℕ) (v : (I.atT l u a).vT) (s : ((I.atT l u a).Fv v)ˣ) :
    (I.chain l u a).cls i ≃ (I.chain l u a).cls i where
  toFun := (I.fm l u a).dil i v s
  invFun := (I.fm l u a).dil i v s⁻¹
  left_inv c := by rw [← (I.fm l u a).dil_mul, inv_mul_cancel, (I.fm l u a).dil_one]
  right_inv c := by rw [← (I.fm l u a).dil_mul, mul_inv_cancel, (I.fm l u a).dil_one]

theorem dia_K_eq (I : TC B X) (l : I.Laws) (u : B.Word) (a : I.ι) (i : ℕ) (v : (I.atT l u a).vT) (s : ((I.atT l u a).Fv v)ˣ)
    (φ : ColT I l u a i) (c' : (I.chain l u a).cls (i + 1)) :
    (I.fm l u a).dilT (i + 1) v s c' ((I.chain l u a).K i φ ((I.fm l u a).dil (i + 1) v s c')) =
      ∑ L ∈ @Finset.univ _ ((I.chain l u a).clsFin i), (I.chain l u a).wt i L • (I.fm l u a).dilT (i + 1) v s c'
        ((I.chain l u a).Kmap i ((I.fm l u a).dil i v s L) ((I.fm l u a).dil (i + 1) v s c') (φ ((I.fm l u a).dil i v s L))) := by
  letI := (I.chain l u a).clsFin i
  simp only [ColumnChain.K, Formalism.ThetaLiftIndependence.kerOpM, map_sum, map_smul]
  refine (Equiv.sum_comp (dilEquiv I l u a i v s) _).symm.trans (Finset.sum_congr rfl fun L _ => ?_)
  have h : (I.chain l u a).wt i ((I.fm l u a).dil i v s L) = (I.chain l u a).wt i L := by
    unfold ColumnChain.wt
    rw [(I.fm l u a).dil_stab]
  show (I.chain l u a).wt i ((I.fm l u a).dil i v s L) • _ = _
  rw [h]
  rfl

end Dia

theorem kernel_keeps_ramT : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)),
    ∀ (u : B.Word) (a : I.ι) (i : ℕ), i < B.R.m → ∀ φ : ColT I l u a i, RamT i φ → RamT (i + 1) ((I.chain l u a).K i φ) := by
  intro B X I hI _ l _ u a i hi φ hR
  letI := (I.chain l u a).clsFin i
  refine ⟨K_mem_Fi I l hI u a i hi φ hR.1, fun v c' => ?_⟩
  letI := (I.atT l u a).FvFin v
  letI := (I.atT l u a).FvDec v
  have hsum : ∑ s : ((I.atT l u a).Fv v)ˣ,
      (fun L => (I.fm l u a).dilT i v s L (φ ((I.fm l u a).dil i v s L))) = 0 := by
    funext L
    rw [Finset.sum_apply, ← finsum_eq_sum_of_fintype]
    exact hR.2 v L
  have hterm : ∀ s : ((I.atT l u a).Fv v)ˣ,
      (I.fm l u a).dilT (i + 1) v s c' ((I.chain l u a).K i φ ((I.fm l u a).dil (i + 1) v s c')) =
        (I.chain l u a).Klin i (fun L => (I.fm l u a).dilT i v s L (φ ((I.fm l u a).dil i v s L))) c' := by
    intro s
    refine (dia_K_eq I l u a i v s φ c').trans ?_
    show _ = ∑ L, (I.chain l u a).wt i L • (I.chain l u a).Kmap i L c'
      ((I.fm l u a).dilT i v s L (φ ((I.fm l u a).dil i v s L)))
    exact Finset.sum_congr rfl fun L _ => congrArg ((I.chain l u a).wt i L • ·)
      (entry_dia I l hI u a i hi φ hR.1 v s L c')
  rw [finsum_eq_sum_of_fintype]
  simp only [hterm]
  rw [← Finset.sum_apply, ← map_sum, hsum, map_zero]
  rfl

end GlobalTheory.KRamT
