import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PinColL
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.StatementWithTransposeOfBranching
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.BrEquivAll
import Formalism.LocalToGlobal.Divisibility.BrJoint
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TrueBranch

section Gen

open Formalism.L2.DIV Formalism.L2.Col

variable {ι : Type} [Fintype ι] {N n : ℕ}

theorem cSpan_eq_VV {m : ℕ} (lam : ι → DomWeight m) : CSpan lam = Formalism.L2.DIV.VV ℂ lam := by
  unfold CSpan Formalism.L2.DIV.VV Formalism.GradedWeylDivisibility.tensorLat
  congr 1
  ext p
  simp only [Set.mem_ofPred_eq, Formalism.L2.Col.nablaSq_eq_delSq]
  rfl

theorem det_ne_zero_of_mem_unitary {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Matrix.unitaryGroup (Fin n) ℂ) : k.det ≠ 0 := by
  intro h
  have h1 := congrArg Matrix.det (Matrix.mem_unitaryGroup_iff'.1 hk)
  rw [Matrix.det_mul, h, mul_zero, Matrix.det_one] at h1
  exact zero_ne_one h1

theorem polOf_fnOf_frOne (G : ι → Matrix (Fin N) (Fin N) ℂ) (sh : ι → ℤ) (o : Frames G) (ho : ∀ τ, o.1 τ = 1)
    (P : MvPolynomial (ι × Fin N × Fin N) ℂ) : Formalism.L2.Col.polOf G sh o (fnOf G sh 1 P) = P := by
  have e : (fun τ => (o.1 τ)⁻¹) = (1 : ι → Matrix (Fin N) (Fin N) ℂ) := funext fun τ => by rw [ho τ, inv_one]; rfl
  have h := Formalism.L2.Col.polOf_fnOf G sh o P
  rwa [e] at h

theorem fnOf_actP_tr (G : ι → Matrix (Fin n) (Fin n) ℂ) (lam : ι → DomWeight n) (g : ι → GL (Fin n) ℂ)
    (P : Pol ℂ ι n) (y y' : Frames G) (h : IsTr (fun τ => ((g τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)ᵀ) y y') :
    fnOf G (shiftOf lam) 1 (actP lam g P) y = fnOf G (shiftOf lam) 1 P y' := by
  have e1 := congrFun (Formalism.L2.Col.fnOf_mul G (shiftOf lam) (fun τ => ((g τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)ᵀ) 1 P) y
  have e2 := Formalism.L2.Col.fnOf_tr (G := G) (G' := G) (shiftOf lam) 1 (fun τ => ((g τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)ᵀ) P y' y h
  have e3 : (fun τ => (1 : ι → Matrix (Fin n) (Fin n) ℂ) τ * ((g τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)ᵀ) =
      fun τ => ((g τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)ᵀ * (1 : ι → Matrix (Fin n) (Fin n) ℂ) τ := by
    funext τ; simp
  rw [e2, e3, e1]
  have e4 : actP lam g P = (∏ τ, ((g τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)ᵀ.det ^ shiftOf lam τ) •
      Formalism.GradedWeylDivisibility.blockAct ℂ (fun τ => ((g τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)ᵀ) P := by
    simp only [actP, detTwK, trAct, LinearMap.smul_apply, AlgHom.toLinearMap_apply]
    congr 1
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [Matrix.det_transpose]
    simp [detPow, shiftOf, Units.val_zpow_eq_zpow_val, Matrix.GeneralLinearGroup.val_det_apply]
  rw [e4]

theorem brEqv_formula (hN : N = n + 1) (G : ι → Matrix (Fin N) (Fin N) ℂ) (G' : ι → Matrix (Fin n) (Fin n) ℂ)
    (lam : ι → DomWeight N) (sg : ι → DomWeight n) (hS : ∀ τ, Br.SameShift (lam τ) (sg τ)) (c : ℂ) (o : Frames G)
    (ho : ∀ τ, o.1 τ = 1) :
    BrEqv hN G G' lam sg (fnOf G' (shiftOf sg) 1 ∘ₗ (c • ((Formalism.L2.DIV.VV ℂ sg).subtype ∘ₗ Br.brStdP hN lam sg)) ∘ₗ
      Formalism.L2.Col.polOf G (shiftOf lam) o) := by
  have hp := polOf_fnOf_frOne G (shiftOf lam) o ho
  refine ⟨?_, ?_⟩
  · rintro _ ⟨P, -, rfl⟩
    refine ⟨c • (Br.brStdP hN lam sg P : Pol ℂ ι n), ?_, ?_⟩
    · rw [cSpan_eq_VV]; exact (Formalism.L2.DIV.VV ℂ sg).smul_mem c (Br.brStdP hN lam sg P).2
    · simp only [LinearMap.comp_apply, hp, LinearMap.smul_apply, Submodule.subtype_apply]
  · rintro k kt hk hb _ ⟨P, hP, rfl⟩ Φ' hΦ' z z' hz
    have hk0 : ∀ τ, (k τ)ᵀ.det ≠ 0 := fun τ => by
      rw [Matrix.det_transpose]; exact det_ne_zero_of_mem_unitary (hk τ)
    have hkt0 : ∀ τ, (kt τ)ᵀ.det ≠ 0 := fun τ => by
      rw [Matrix.det_transpose, (hb τ).det, mul_one, ← Matrix.det_transpose]; exact hk0 τ
    let g : ι → GL (Fin n) ℂ := fun τ => Matrix.GeneralLinearGroup.mkOfDetNeZero _ (hk0 τ)
    let g' : ι → GL (Fin N) ℂ := fun τ => Matrix.GeneralLinearGroup.mkOfDetNeZero _ (hkt0 τ)
    have hblk : ∀ τ, GlobalTheory.BranchFormula.IsBlock hN ((g' τ : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ)
        ((g τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) 1 := fun τ => (hb τ).transpose
    have hPV : P ∈ Formalism.L2.DIV.VV ℂ lam := cSpan_eq_VV lam ▸ hP
    have hE := GlobalTheory.BranchFormula.brEquiv_all ℂ hN lam sg hS g g' (fun τ => hblk τ) ⟨P, hPV⟩
    have h2 : (Br.brStdP hN lam sg (actP lam g' P) : Pol ℂ ι n) = actP sg g (Br.brStdP hN lam sg P : Pol ℂ ι n) :=
      congrArg Subtype.val hE
    have hΦe : Φ' = fnOf G (shiftOf lam) 1 (actP lam g' P) := by
      funext y
      have hd : ∀ τ, IsUnit (kt τ * y.1 τ).det := fun τ => by
        rw [Matrix.det_mul]
        refine IsUnit.mul (Ne.isUnit ?_) (y.2 τ)
        rw [← Matrix.det_transpose]; exact hkt0 τ
      let y' : Frames G := ⟨fun τ => kt τ * y.1 τ, hd⟩
      rw [hΦ' y y' (fun τ => rfl), fnOf_actP_tr G lam g' P y y' (fun τ => by
        show kt τ * y.1 τ = ((kt τ)ᵀ)ᵀ * y.1 τ
        rw [Matrix.transpose_transpose])]
    rw [hΦe]
    simp only [LinearMap.comp_apply, hp, LinearMap.smul_apply, Submodule.subtype_apply]
    rw [h2, map_smul, map_smul, Pi.smul_apply, Pi.smul_apply, fnOf_actP_tr G' sg g _ z z' (fun τ => by
      rw [hz τ]
      show k τ * z.1 τ = ((k τ)ᵀ)ᵀ * z.1 τ
      rw [Matrix.transpose_transpose])]

theorem ne_formula (hN : N = n + 1) (G : ι → Matrix (Fin N) (Fin N) ℂ) (G' : ι → Matrix (Fin n) (Fin n) ℂ)
    (lam : ι → DomWeight N) (sg : ι → DomWeight n) (hI : ∀ τ, Br.Interlace hN (lam τ) (sg τ))
    (hS : ∀ τ, Br.SameShift (lam τ) (sg τ)) (c : ℂ) (hc : c ≠ 0) (o : Frames G) (ho : ∀ τ, o.1 τ = 1) :
    ∃ Φ ∈ ValC G lam, (fnOf G' (shiftOf sg) 1 ∘ₗ (c • ((Formalism.L2.DIV.VV ℂ sg).subtype ∘ₗ Br.brStdP hN lam sg)) ∘ₗ
      Formalism.L2.Col.polOf G (shiftOf lam) o) Φ ≠ 0 := by
  have hp := polOf_fnOf_frOne G (shiftOf lam) o ho
  have h1 := GlobalTheory.BranchFormula.onePlace Formalism.L2.DIV.BrJ.branching_interlacing_pairs
  choose f hf hf0 using fun τ => (h1 N n hN (lam τ) (sg τ) (hI τ) (hS τ)).2.2.1
  have hn : ∀ τ, f τ ∈ nablaSq ℂ N (lam τ) := fun τ => by rw [Formalism.L2.Col.nablaSq_eq_delSq]; exact hf τ
  have hmem : Formalism.L2.DIV.ten f ∈ Formalism.L2.DIV.VV ℂ lam := GlobalTheory.Proof.TensorMapDescent.ten_mem lam f hn
  have ht := GlobalTheory.BranchFormula.tensor ℂ ι N n hN lam sg hI hS f ⟨_, hmem⟩ hn rfl
  refine ⟨fnOf G (shiftOf lam) 1 (Formalism.L2.DIV.ten f), ⟨_, (cSpan_eq_VV lam).symm ▸ hmem, rfl⟩, fun h => ?_⟩
  simp only [LinearMap.comp_apply, hp, LinearMap.smul_apply, Submodule.subtype_apply] at h
  have h' : (Br.brStdP hN lam sg (Formalism.L2.DIV.ten f) : Pol ℂ ι n) =
      Formalism.L2.DIV.ten fun τ => GlobalTheory.IndefiniteRowSideFullHecke.InterlacingEquivariance.brOne ℂ hN (lam τ) (sg τ) (f τ) := ht
  rw [h', map_smul] at h
  have h0 := Formalism.L2.Col.fnOf_injective G' (shiftOf sg) 1 (fun _ => by simp) ⟨fun _ => 1, fun _ => by simp⟩
    (((smul_eq_zero.1 h).resolve_left hc).trans (map_zero _).symm)
  exact GlobalTheory.Proof.TensorMapDescent.ten_ne_zero _ hf0 h0

end Gen

section True

variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word)

theorem half_mul (R : Ranks) (j : ℕ) : ((j * (R.t + 1) / 2 : ℕ) : ℤ) = (j : ℤ) * (((R.t + 1) / 2 : ℕ) : ℤ) := by
  obtain ⟨a, ha⟩ := R.t_odd
  have h1 : (R.t + 1) / 2 = a + 1 := by omega
  have h2 : j * (R.t + 1) / 2 = j * (a + 1) := by
    rw [ha, show j * (2 * a + 1 + 1) = 2 * (j * (a + 1)) by ring]; omega
  rw [h1, h2]; push_cast; ring

theorem domWeight_ext {M : ℕ} {a b : DomWeight M} (h : a.w = b.w) : a = b := by
  cases a; cases b; simp only at h; subst h; rfl

theorem lamT_record (j : ℕ) : Formalism.L2.Forms.lamT (D := I.rec7 l Z) u j = GlobalTheory.Mem.Col2.lamT (B.hcW u) j := by
  funext τ
  apply domWeight_ext
  funext i
  show (Examples₂.lamOf (B.hcW u τ) j).w i - ((j * (B.R.t + 1) / 2 : ℕ) : ℤ) =
    (Examples₂.lamOf (B.hcW u τ) j).w i + -((j : ℤ) * (((B.R.t + 1) / 2 : ℕ) : ℤ))
  rw [half_mul]; ring

theorem sgT_record (a : I.ι) : Formalism.L2.Forms.sgT (D := I.rec7 l Z) u = (I.perIn u a).sgT := by
  funext τ
  apply domWeight_ext
  funext i
  show (B.wts.sgW τ).w i - ((B.R.m * (B.R.t + 1) / 2 : ℕ) : ℤ) =
    (B.wts.sgW τ).w i + -((B.R.m : ℤ) * (((B.R.t + 1) / 2 : ℕ) : ℤ))
  rw [half_mul]; ring

end True

section Main

theorem branching_true_columns : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (hN : B.R.N B.R.m = (B.R.N B.R.m - 1) + 1), (∀ τ, Formalism.L2.Col.Br.Interlace hN (Formalism.L2.Forms.lamT (D := (I.rec7 l Z)) u B.R.m τ) (sgT (D := (I.rec7 l Z)) u τ)) ∧ BrEqv hN _ _ (Formalism.L2.Forms.lamT (D := (I.rec7 l Z)) u B.R.m) (sgT (D := (I.rec7 l Z)) u) (lowOf I l Z u) ∧ (∃ Φ ∈ ValC _ (Formalism.L2.Forms.lamT (D := (I.rec7 l Z)) u B.R.m), lowOf I l Z u Φ ≠ 0) ∧ ∀ (a : I.ι) z c (y : FrN (I.rec7 l Z) (B.R.N B.R.m - 1)), (I.per l u a).lowerMap z c ⟨y.1, y.2⟩ = lowOf I l Z u (fun y' => z c ⟨y'.1, y'.2⟩) y := by
  intro B X I _ _ l Z u hN
  have hM := fun τ => GlobalTheory.BranchMembers.members B.fields B.Word B.R B.wts B.wts_isOk u τ
  have hI' : ∀ τ, Formalism.L2.Col.Br.Interlace hN (GlobalTheory.Mem.Col2.lamT (B.hcW u) B.R.m τ) ((I.perIn u I.mu0).sgT τ) :=
    fun τ => (hM τ).1
  have hS' : ∀ τ, Formalism.L2.Col.Br.SameShift (GlobalTheory.Mem.Col2.lamT (B.hcW u) B.R.m τ) ((I.perIn u I.mu0).sgT τ) :=
    fun τ => (hM τ).2
  have hc : (∏ τ, Formalism.L2.Col.embAt B.embLL B.fields.emb τ (I.perIn u I.mu0).tz ^
      (-Formalism.L2.Col.Br.nBr (GlobalTheory.Mem.Col2.lamT (B.hcW u) B.R.m τ) ((I.perIn u I.mu0).sgT τ))) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun τ _ => zpow_ne_zero _ ((map_ne_zero _).2 (l.per u I.mu0).tz_ne)
  have hlow : lowOf I l Z u = fnOf _ (shiftOf (I.perIn u I.mu0).sgT) 1 ∘ₗ
      ((∏ τ, Formalism.L2.Col.embAt B.embLL B.fields.emb τ (I.perIn u I.mu0).tz ^
        (-Formalism.L2.Col.Br.nBr (GlobalTheory.Mem.Col2.lamT (B.hcW u) B.R.m τ) ((I.perIn u I.mu0).sgT τ))) •
        ((Formalism.L2.DIV.VV ℂ (I.perIn u I.mu0).sgT).subtype ∘ₗ
          Formalism.L2.Col.Br.brStdP hN (GlobalTheory.Mem.Col2.lamT (B.hcW u) B.R.m) (I.perIn u I.mu0).sgT)) ∘ₗ
      Formalism.L2.Col.polOf _ (shiftOf (GlobalTheory.Mem.Col2.lamT (B.hcW u) B.R.m)) ⟨fun _ => 1, fun _ => by simp⟩ := by
    unfold lowOf
    rw [lamT_record I l Z u, sgT_record I l Z u I.mu0]
    rfl
  refine ⟨?_, ?_, ?_, fun a z c y => ?_⟩
  · rw [lamT_record I l Z u, sgT_record I l Z u I.mu0]; exact hI'
  · rw [lamT_record I l Z u, sgT_record I l Z u I.mu0, hlow]
    exact brEqv_formula hN _ _ _ _ hS' _ _ (fun _ => rfl)
  · rw [lamT_record I l Z u, hlow]
    exact ne_formula hN _ _ _ _ hI' hS' _ hc _ (fun _ => rfl)
  · unfold lowOf
    rw [lamT_record I l Z u, sgT_record I l Z u a]
    rfl

end Main

end GlobalTheory.TrueBranch
