import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.DensEqZeroOfNotMem
import Lemmata.GeneralBFactThirdAltForm.Imports

open NumberField Module Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal
open Classical ValuativeRel

noncomputable section

namespace Formalism.L2.SG.Pf.Cnt.DualityBasisChange

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Herm

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : Loc.HermSp M V)

theorem h_zero_left (y : V) : H.h 0 y = 0 := by
  have := H.h_smul_left 0 0 y
  simpa using this

theorem h_smul_right (c : E) (x y : V) : H.h x (c • y) = M.L.cj c * H.h x y := by
  rw [H.h_herm (c • y) x, H.h_smul_left, map_mul, ← H.h_herm y x]

theorem h_sum_left {ι : Type} (s : Finset ι) (x : ι → V) (y : V) :
    H.h (∑ i ∈ s, x i) y = ∑ i ∈ s, H.h (x i) y := by
  induction s using Finset.induction_on with
  | empty => simp [h_zero_left]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, H.h_add_left, ih]

theorem h_sum_right {ι : Type} (s : Finset ι) (x : ι → V) (y : V) :
    H.h y (∑ i ∈ s, x i) = ∑ i ∈ s, H.h y (x i) := by
  rw [H.h_herm (∑ i ∈ s, x i) y, h_sum_left, map_sum]
  exact Finset.sum_congr rfl fun i _ => (H.h_herm (x i) y).symm

theorem gram_comb {ι : Type} [Fintype ι] (v : ι → V) (A : Matrix ι ι E) :
    (Matrix.of fun a b => H.h (∑ d, A d b • v d) (∑ c, A c a • v c)) =
      (A.map M.L.cj).transpose * (Matrix.of fun a b => H.h (v b) (v a)) * A := by
  ext a b
  simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, h_sum_left,
    h_sum_right, H.h_smul_left, h_smul_right, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
  ring

end Herm

section Basis

variable {E : Type} [CommRing E] {O : Subring E} {V : Type} [AddCommGroup V] [Module E V]
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem change_basis (g b : ι → V) (hg : LinearIndependent O g)
    (hs : Submodule.span O (Set.range g) = Submodule.span O (Set.range b)) :
    ∃ Q P : Matrix ι ι O, (∀ j, g j = ∑ i, Q i j • b i) ∧ P * Q = 1 := by
  first | exact Bl.general_b_fact_third_alt_form.goal1 .. | (apply Bl.general_b_fact_third_alt_form.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_third_alt_form.goal1 <;> assumption)

end Basis

section Glob

variable {D : Formalism.BasicNotions.D7}

theorem flag_hT {T : D.host.E} (F : FlagG (VS D) D.R.rS T) (a b : Fin (D.R.rS + 1)) :
    (VS D).hT (F.fvec a) (F.fvec b) = if a = Fin.last D.R.rS ∧ b = Fin.last D.R.rS then -T else 0 := by
  induction a using Fin.lastCases with
  | last =>
    induction b using Fin.lastCases with
    | last => simp [FlagG.fvec, F.z_norm]
    | cast b =>
      simp only [FlagG.fvec, Fin.snoc_last, Fin.snoc_castSucc]
      rw [if_neg (by simp [Fin.castSucc_ne_last])]
      rw [← (VS D).herm.eq (F.e b) F.z, F.z_orth b, map_zero]
  | cast a =>
    simp only [FlagG.fvec, Fin.snoc_castSucc]
    rw [if_neg (by simp [Fin.castSucc_ne_last])]
    induction b using Fin.lastCases with
    | last => simp only [Fin.snoc_last]; exact F.z_orth a
    | cast b => simp only [Fin.snoc_castSucc]; exact F.e_iso a b

def vfam {T T' : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (F' : LFlag (VS D) D.R.rS T') :
    Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1) → (VS D).V :=
  Sum.elim F0.fvec F'.fl.fvec

theorem ga_eq {T T' : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (F' : LFlag (VS D) D.R.rS T') :
    Ga T T' (ZhatL (lf D F0) F') = Matrix.of fun a b => brS (VS D) (vfam F0 F' b) (vfam F0 F' a) := by
  ext a b
  rcases a with a | a <;> rcases b with b | b
  · simp only [Ga, Matrix.fromBlocks_apply₁₁, Matrix.of_apply, vfam, Sum.elim_inl, brS]
    rw [flag_hT]
  · simp [Ga, vfam, brS, ZhatL, Zhat]
  · simp only [Ga, Matrix.fromBlocks_apply₂₁, Matrix.conjTranspose_apply, Matrix.of_apply, vfam, Sum.elim_inl,
      Sum.elim_inr, brS, ZhatL, Zhat]
    rw [← (VS D).herm.eq (F0.fvec b) (F'.fl.fvec a)]
    rfl
  · simp only [Ga, Matrix.fromBlocks_apply₂₂, Matrix.of_apply, vfam, Sum.elim_inr, brS]
    rw [flag_hT]

variable {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep}

def g0 (L : LocSp D M) (δ : ∀ p : PlF D, (D.s.atP p).Fp) (p : PlF D) {T T' : D.host.E}
    (F0 : FlagG (VS D) D.R.rS T) (F' : LFlag (VS D) D.R.rS T') : Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1) → L.V p :=
  fun a => phi δ p a • L.bc p (vfam F0 F' a)

theorem gaLoc_eq (L : LocSp D M) (δ : ∀ p : PlF D, (D.s.atP p).Fp) (p : PlF D) {T T' : D.host.E}
    (F0 : FlagG (VS D) D.R.rS T) (F' : LFlag (VS D) D.R.rS T') :
    GaLoc M δ p T T' (ZhatL (lf D F0) F') = Matrix.of fun a b => (L.H p).h (g0 L δ p F0 F' b) (g0 L δ p F0 F' a) := by
  ext a b
  simp only [GaLoc, Matrix.of_apply, g0, (L.H p).h_smul_left, h_smul_right, L.bc_form, ga_eq]
  ring

def amat (p : PlF D) (g : Loc.SplitG (M p).L) :
    Matrix (Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1)) (Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1)) (D.s.atP p).Ep :=
  Matrix.fromBlocks 1 (-(algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((g.q : (D.s.atP p).Fp)⁻¹)) •
      (1 : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Ep)) 0
    (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((g.q : (D.s.atP p).Fp)⁻¹) •
      (1 : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Ep))

def locFam (L : LocSp D M) (δ : ∀ p : PlF D, (D.s.atP p).Fp) (p : PlF D) {T T' : D.host.E}
    (F0 : FlagG (VS D) D.R.rS T) (F' : LFlag (VS D) D.R.rS T') : Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1) → L.V p :=
  match (M p).split with
  | none => g0 L δ p F0 F'
  | some g => fun b => ∑ d, amat p g d b • g0 L δ p F0 F' d

theorem gaPlus_eq_gram (L : LocSp D M) (δ : ∀ p : PlF D, (D.s.atP p).Fp) (p : PlF D) {T T' : D.host.E}
    (F0 : FlagG (VS D) D.R.rS T) (F' : LFlag (VS D) D.R.rS T') :
    GaPlus M δ p T T' (ZhatL (lf D F0) F') =
      Matrix.of fun a b => (L.H p).h (locFam L δ p F0 F' b) (locFam L δ p F0 F' a) := by
  unfold GaPlus locFam
  cases hs : (M p).split with
  | none => simp only; exact gaLoc_eq L δ p F0 F'
  | some g =>
    simp only
    rw [gram_comb, gaLoc_eq L δ p F0 F']
    rfl

end Glob

section Cut

def FrameBasisL : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep),
    (∀ p, Agree δ M p) → ∀ (L : LocSp D M) (u u' : D.what₂.Word),
    (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Lat.gS D) ^ 2] →
    ∀ (F0 : FlagG (VS D) D.R.rS (Tn u)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)),
      IsRowReps D F0 what₂ → ∀ F' : LFlag (VS D) D.R.rS (Tn u'), F'.zt = F'.fl.z →
        Formalism.MainNotions.S.LocalSplitGroups.TotPos (GZ (Tn u) (Tn u') (ZhatL (lf D F0) F')) → ∀ p : PlF D,
        LinearIndependent (M p).L.O (locFam L δ p F0 F') ∧
          Submodule.span (M p).L.O (Set.range (locFam L δ p F0 F')) = lattice₂ L p (MMof D F0 F')

def JordanL : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep),
    (∀ p, Agree δ M p) → ∀ (L : LocSp D M) (u u' : D.what₂.Word),
    (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Lat.gS D) ^ 2] →
    ∀ (F0 : FlagG (VS D) D.R.rS (Tn u)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)),
      IsRowReps D F0 what₂ → ∀ F' : LFlag (VS D) D.R.rS (Tn u'), F'.zt = F'.fl.z →
        Formalism.MainNotions.S.LocalSplitGroups.TotPos (GZ (Tn u) (Tn u') (ZhatL (lf D F0) F')) →
        Formalism.HermitianLatticesTheory.IsIntegralLat (VS D).hT (MMof D F0 F') →
        ∀ (p : PlF D) (ϖ : 𝒪[(D.s.atP p).Fp]), Irreducible ϖ →
        ∃ (b : Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1) → L.V p)
          (a : Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1) → 𝒪[(D.s.atP p).Fp]),
          Submodule.span (M p).L.O (Set.range b) = lattice₂ L p (MMof D F0 F') ∧
          (∀ i j, i ≠ j → (L.H p).h (b j) (b i) = 0) ∧
          (∀ i, (L.H p).h (b i) (b i) = algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (a i : (D.s.atP p).Fp)) ∧
          (Finset.univ.filter fun i => ϖ ∣ a i).card = cJ (VS D).hT (UPair D F0 F') (MMof D F0 F') p.asIdeal

theorem gaPlusDiag_of (hF : FrameBasisL) (hJ : JordanL) : GaPlusDiag := by
  intro D δ M hA L u u' hT F0 what₂ hR ϖ hϖ Z F' hz hZ hP hI p
  subst hZ
  obtain ⟨hli, hsp⟩ := hF D δ M hA L u u' hT F0 what₂ hR F' hz hP p
  obtain ⟨b, a, hbs, horth, hdiag, hcnt⟩ := hJ D δ M hA L u u' hT F0 what₂ hR F' hz hP hI p (ϖ p) (hϖ p)
  obtain ⟨Q, P, hQ, hPQ⟩ := change_basis (O := (M p).L.O) (locFam L δ p F0 F') b hli (hsp.trans hbs.symm)
  have hdet : (Q.map (M p).L.O.subtype).det = ((Q.det : (M p).L.O) : (D.s.atP p).Ep) :=
    (RingHom.map_det (M p).L.O.subtype Q).symm
  refine ⟨Q.map (M p).L.O.subtype, a, fun i j => (Q i j).2, ⟨((P.det : (M p).L.O) : (D.s.atP p).Ep), P.det.2, ?_⟩, ?_, hcnt⟩
  · rw [hdet]
    have h1 : P.det * Q.det = 1 := by rw [← Matrix.det_mul, hPQ, Matrix.det_one]
    have h2 : ((Q.det * P.det : (M p).L.O) : (D.s.atP p).Ep) = 1 := by rw [mul_comm, h1]; rfl
    simpa using h2
  · rw [gaPlus_eq_gram L δ p F0 F']
    have hg : locFam L δ p F0 F' = fun j => ∑ i, (Q.map (M p).L.O.subtype) i j • b i := by
      funext j
      rw [hQ j]
      rfl
    rw [hg, gram_comb]
    congr 2
    ext i j
    simp only [Matrix.of_apply, Matrix.diagonal_apply]
    split_ifs with hij
    · subst hij; exact hdiag i
    · exact horth i j hij

end Cut

section Int

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V]

theorem cj_mem_O (x : E) (hx : x ∈ M.L.O) : M.L.cj x ∈ M.L.O := by
  rw [M.L.O_def] at hx ⊢
  exact hx.map (M.L.cj.toAlgHom.restrictScalars 𝒪[F])

theorem h_int_span (H : Loc.HermSp M V) {ι : Type} (g : ι → V) (hG : ∀ a b, H.h (g b) (g a) ∈ M.L.O)
    {x y : V} (hx : x ∈ Submodule.span M.L.O (Set.range g)) (hy : y ∈ Submodule.span M.L.O (Set.range g)) :
    H.h x y ∈ M.L.O := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨b, rfl⟩ := hx
    induction hy using Submodule.span_induction with
    | mem y hy => obtain ⟨a, rfl⟩ := hy; exact hG a b
    | zero => have := h_smul_right H 0 (g b) 0; rw [zero_smul, map_zero, zero_mul] at this; rw [this]; exact M.L.O.zero_mem
    | add y y' _ _ ih ih' =>
      rw [H.h_herm (y + y') (g b), H.h_add_left, map_add, ← H.h_herm y (g b), ← H.h_herm y' (g b)]
      exact M.L.O.add_mem ih ih'
    | smul c y _ ih =>
      rw [Subring.smul_def, h_smul_right]
      exact M.L.O.mul_mem (cj_mem_O _ c.2) ih
  | zero => rw [h_zero_left]; exact M.L.O.zero_mem
  | add x x' _ _ ih ih' => rw [H.h_add_left]; exact M.L.O.add_mem ih ih'
  | smul c x _ ih => rw [Subring.smul_def, H.h_smul_left]; exact M.L.O.mul_mem c.2 ih

end Int

section S3

def LocGlobIntE : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (x : D.host.E), (∀ p : PlF D, (D.s.atP p).ιE x ∈ (D.s.atP p).O) →
    x ∈ (1 : Submodule (𝓞 D.host.E) D.host.E)

theorem gaPlusIntMM_of (hF : FrameBasisL) (hLG : LocGlobIntE) : GaPlusIntMM := by
  intro D δ M hA L u u' hT F0 what₂ hR Z F' hz hZ hP hInt
  subst hZ
  intro x hx y hy
  refine hLG D _ fun p => ?_
  obtain ⟨-, hsp⟩ := hF D δ M hA L u u' hT F0 what₂ hR F' hz hP p
  have hmem : ∀ v ∈ MMof D F0 F', L.bc p v ∈ Submodule.span (M p).L.O (Set.range (locFam L δ p F0 F')) :=
    fun v hv => hsp ▸ Submodule.subset_span ⟨v, hv, rfl⟩
  have e : (D.s.atP p).ιE ((VS D).hT x y) = (L.H p).h (L.bc p y) (L.bc p x) := (L.bc_form p y x).symm
  rw [e, ← (hA p).2.2.2.1]
  refine h_int_span (L.H p) (locFam L δ p F0 F') (fun a b => ?_) (hmem y hy) (hmem x hx)
  have := hInt p a b
  rw [gaPlus_eq_gram L δ p F0 F'] at this
  exact this

theorem notIntDens_of_steps (h1 : LocSelfDual) (hF : FrameBasisL) (hLG : LocGlobIntE) : NotIntDens :=
  notIntDens_of h1 (gaPlusIntMM_of hF hLG)

end S3

end Formalism.L2.SG.Pf.Cnt.DualityBasisChange
