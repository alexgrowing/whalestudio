import Formalism.SharpRestriction.CuspSpanNormBounds.LocalGroupInFamilyNontrivial

noncomputable section

namespace Formalism.L2.SG.CntLocal

open NumberField Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups
open scoped BigOperators
open Classical ValuativeRel

set_option linter.dupNamespace false

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable (D : Formalism.BasicNotions.D7)

structure LocSp (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) : Type 1 where
  V : PlF D → Type
  [acg : ∀ p, AddCommGroup (V p)]
  [mod : ∀ p, Module (D.s.atP p).Ep (V p)]
  H : ∀ p, Loc.HermSp (M p) (V p)
  rank : ∀ p, Module.finrank (D.s.atP p).Ep (V p) = D.R.r
  bc : ∀ p, (VS D).V →+ V p
  bc_smul : ∀ p (a : D.host.E) (x : (VS D).V), bc p (a • x) = (D.s.atP p).ιE a • bc p x
  bc_span : ∀ p, Submodule.span (D.s.atP p).Ep (Set.range (bc p)) = ⊤
  bc_form : ∀ p (x y : (VS D).V), (H p).h (bc p x) (bc p y) = (D.s.atP p).ιE (brS (VS D) x y)

attribute [instance] LocSp.acg LocSp.mod

variable {D}

def LocSp.ofTermLoc {Y : TermTie D} {δ : ∀ p : PlF D, (D.s.atP p).Fp}
    {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep} {u u' : D.what₂.Word}
    (X : TermLoc D Y δ M u u') : LocSp D M where
  V := X.V
  H := X.H
  rank := X.rank
  bc := X.bc
  bc_smul := X.bc_smul
  bc_span := X.bc_span
  bc_form := X.bc_form

abbrev Tn (u : D.what₂.Word) : D.host.E := (((D.mem u).A.T : ℕ) : D.host.E)

abbrev MatZ (D : Formalism.BasicNotions.D7) : Type := Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E

def GZ (T T' : D.host.E) (Z : MatZ D) : D.host.E :=
  leadMinorE Z (D.R.rS + 1) * star (leadMinorE Z (D.R.rS + 1)) -
    T * T' * (leadMinorE Z D.R.rS * star (leadMinorE Z D.R.rS))

def sqrtAbsNormOfScaledGram (T T' : D.host.E) (Z : MatZ D) : ℝ :=
  Real.sqrt |((Algebra.norm ℚ (GZ T T' Z / ((Lat.gS D : D.host.E) ^ D.R.m)) : ℚ) : ℝ)|

def Ga (T T' : D.host.E) (Z : MatZ D) :
    Matrix (Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1)) (Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1)) D.host.E :=
  Matrix.fromBlocks
    (Matrix.of fun a b => if a = Fin.last D.R.rS ∧ b = Fin.last D.R.rS then -T else 0) Z
    Z.conjTranspose
    (Matrix.of fun a b => if a = Fin.last D.R.rS ∧ b = Fin.last D.R.rS then -T' else 0)

variable {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep}

def phi (δ : ∀ p : PlF D, (D.s.atP p).Fp) (p : PlF D) : Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1) → (D.s.atP p).Ep :=
  Sum.elim (frFac δ p) (frFac δ p)

def ZhatLoc (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (p : PlF D) (Z : MatZ D) : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Ep :=
  Matrix.of fun a b => frFac δ p b * (M p).L.cj (frFac δ p a) * (D.s.atP p).ιE (Z a b)

def GaLoc (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (p : PlF D) (T T' : D.host.E) (Z : MatZ D) :
    Matrix (Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1)) (Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1)) (D.s.atP p).Ep :=
  Matrix.of fun a b => phi δ p b * (M p).L.cj (phi δ p a) * (D.s.atP p).ιE (Ga T T' Z a b)

def GaPlus (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (p : PlF D) (T T' : D.host.E) (Z : MatZ D) :
    Matrix (Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1)) (Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1)) (D.s.atP p).Ep :=
  match (M p).split with
  | none => GaLoc M δ p T T' Z
  | some g =>
    let qi : (D.s.atP p).Ep := algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((g.q : (D.s.atP p).Fp)⁻¹)
    let A : Matrix (Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1)) (Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1)) (D.s.atP p).Ep :=
      Matrix.fromBlocks 1 (-qi • (1 : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Ep)) 0
        (qi • (1 : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Ep))
    (A.map (M p).L.cj).transpose * GaLoc M δ p T T' Z * A

def lattice₂ (L : LocSp D M) (p : PlF D) (Λ : Submodule (𝓞 D.host.E) (VS D).V) : Submodule (M p).L.O (L.V p) :=
  Submodule.span (M p).L.O (L.bc p '' (Λ : Set (VS D).V))

def densP (L : LocSp D M) (δ : ∀ p : PlF D, (D.s.atP p).Fp) (ϖ : ∀ p : PlF D, 𝒪[(D.s.atP p).Fp])
    (T T' : D.host.E) (Z : MatZ D) (p : PlF D) : ℝ :=
  (L.H p).dens (ϖ p) (lattice₂ L p (VS D).L0) (GaPlus M δ p T T' Z)

def ZZP (δ : ∀ p : PlF D, (D.s.atP p).Fp) (u u' : D.what₂.Word) (p : PlF D) (Z : MatZ D) :
    Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Ep :=
  Loc.HermSp.ZZplusOf (M p) (ZhatLoc M δ p Z) (((D.mem u).A.T : ℕ) : (D.s.atP p).Fp)
    (((D.mem u').A.T : ℕ) : (D.s.atP p).Fp)

def N0 {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (Λ : Submodule (𝓞 D.host.E) (VS D).V) :
    Set ((VS D).V ≃ₗ[D.host.E] (VS D).V) :=
  {n | n ∈ NLam Λ (lf D F0) ∧ (∀ a, n (F0.e a) = F0.e a) ∧ n F0.z = F0.z}

def EZ {T : D.host.E} (T' : D.host.E) (F0 : FlagG (VS D) D.R.rS T) (Λ : Submodule (𝓞 D.host.E) (VS D).V)
    (Z : MatZ D) : Set (LFlag (VS D) D.R.rS T') :=
  {F' | IsTerm Λ (gS D) (lf D F0) F' ∧ AdmWit Λ (gS D) (lf D F0) F' 1 ∧ IsGeneric Λ (gS D) (lf D F0) F' ∧
    FrameOK D Λ F' ∧ ZhatL (lf D F0) F' = Z}

def NilradicalFlagMoved {T T' : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (Λ : Submodule (𝓞 D.host.E) (VS D).V)
    (F' F'' : LFlag (VS D) D.R.rS T') : Prop :=
  ∃ n ∈ N0 F0 Λ, (∀ a, n (F'.fl.e a) = F''.fl.e a) ∧ n F'.fl.z = F''.fl.z

def cntE {T : D.host.E} (T' : D.host.E) (F0 : FlagG (VS D) D.R.rS T) (Λ : Submodule (𝓞 D.host.E) (VS D).V)
    (Z : MatZ D) : ENat :=
  Set.encard {O : Set (LFlag (VS D) D.R.rS T') | ∃ F' ∈ EZ T' F0 Λ Z,
    O = {F'' | F'' ∈ EZ T' F0 Λ Z ∧ NilradicalFlagMoved F0 Λ F' F''}}

def nu {T : D.host.E} (T' : D.host.E) (F0 : FlagG (VS D) D.R.rS T)
    (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)) (Z : MatZ D) : ℝ :=
  (∑ Λ ∈ what₂, wRow D F0 Λ * ((cntE T' F0 Λ Z).toNat : ℝ)) / ∑ Λ ∈ what₂, wRow D F0 Λ

def RowsOf (u : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (Tn u))
    (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)) : Prop :=
  F0.e = D.sp.hypE ∧ F0.z = D.zmOf u ∧ IsRowReps D F0 what₂ ∧ what₂.Nonempty

def Formula (δ : ∀ p : PlF D, (D.s.atP p).Fp) (L : LocSp D M) (u u' : D.what₂.Word)
    (F0 : FlagG (VS D) D.R.rS (Tn u)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)) (c : ℝ) : Prop :=
  0 < c ∧ ∀ (ϖ : ∀ p : PlF D, 𝒪[(D.s.atP p).Fp]), (∀ p, Irreducible (ϖ p)) → ∀ Z : MatZ D,
    (∀ Λ ∈ what₂, cntE (Tn u') F0 Λ Z ≠ ⊤) ∧
    (TotPos (GZ (Tn u) (Tn u') Z) →
      Multipliable (densP L δ ϖ (Tn u) (Tn u') Z) ∧
      nu (Tn u') F0 what₂ Z =
        c * sqrtAbsNormOfScaledGram (Tn u) (Tn u') Z ^ (D.R.k - 1) * ∏' p, densP L δ ϖ (Tn u) (Tn u') Z p)

def NotPos (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (Tn u))
    (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)) : Prop :=
  ∀ Z : MatZ D, ¬ TotPos (GZ (Tn u) (Tn u') Z) → nu (Tn u') F0 what₂ Z = 0

def NotInt (δ : ∀ p : PlF D, (D.s.atP p).Fp) (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (Tn u))
    (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)) : Prop :=
  ∀ Z : MatZ D, (∃ p a b, ZZP (M := M) δ u u' p Z a b ∉ (M p).R) → nu (Tn u') F0 what₂ Z = 0

def CntLocal (D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (δ : ∀ p : PlF D, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep),
    (∀ p, Agree δ M p) → ∀ (L : LocSp D M) (u u' : D.what₂.Word),
    (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Lat.gS D) ^ 2] →
    ∀ (F0 : FlagG (VS D) D.R.rS (Tn u)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)),
      RowsOf u F0 what₂ →
      (∃ c, Formula δ L u u' F0 what₂ c) ∧ NotPos u u' F0 what₂ ∧ NotInt (M := M) δ u u' F0 what₂

section
variable {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E] [Algebra F E]
    [TopologicalSpace E] [MeasurableSpace E] {M : Formalism.MainNotions.S.Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V]
    (H : Formalism.MainNotions.S.Loc.HermSp M V)

theorem h_smul_right' (c : E) (x y : V) : H.h x (c • y) = M.L.cj c * H.h x y := by
  have h1 : H.h x (c • y) = M.L.cj (H.h (c • y) x) := H.h_herm (c • y) x
  have h2 : H.h x y = M.L.cj (H.h y x) := H.h_herm y x
  rw [h1, H.h_smul_left, map_mul, h2]

def hL (y : V) : V →+ E := AddMonoidHom.mk' (fun x => H.h x y) (fun x x' => H.h_add_left x x' y)

theorem h_sum_left {ι : Type} (s : Finset ι) (x : ι → V) (y : V) :
    H.h (∑ i ∈ s, x i) y = ∑ i ∈ s, H.h (x i) y := map_sum (hL H y) x s

theorem h_sum_right {ι : Type} (s : Finset ι) (x : V) (y : ι → V) :
    H.h x (∑ i ∈ s, y i) = ∑ i ∈ s, H.h x (y i) := by
  rw [H.h_herm, h_sum_left, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← H.h_herm]

theorem gram_comb {ι : Type} [Fintype ι] [DecidableEq ι] (v : ι → V) (A : Matrix ι ι E) (a b : ι) :
    H.h (∑ i, A i b • v i) (∑ k, A k a • v k) =
      ((A.map M.L.cj).transpose * Matrix.of (fun a b => H.h (v b) (v a)) * A) a b := by
  simp only [h_sum_left, h_sum_right, H.h_smul_left, h_smul_right', Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.map_apply, Matrix.of_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
  ring
end

theorem gz_eq (D : Formalism.BasicNotions.D7) {T T' : D.host.E} (F : LFlag (VS D) D.R.rS T) (F' : LFlag (VS D) D.R.rS T') :
    Gval F F' = GZ T T' (ZhatL F F') := rfl

theorem ga_gram (D : Formalism.BasicNotions.D7) {T T' : D.host.E} (F : FlagG (VS D) D.R.rS T) (F' : FlagG (VS D) D.R.rS T')
    (a b : Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1)) :
    Ga T T' (Zhat F F') a b = brS (VS D) (Sum.elim F.fvec F'.fvec b) (Sum.elim F.fvec F'.fvec a) := by
  have hs : ∀ x y : (VS D).V, star ((VS D).hT x y) = (VS D).hT y x := fun x y => (VS D).herm.eq x y
  have key : ∀ {S : ℕ} {U : D.host.E} (G : FlagG (VS D) D.R.rS U) (a b : Fin (D.R.rS + 1)),
      (VS D).hT (G.fvec a) (G.fvec b) = if a = Fin.last D.R.rS ∧ b = Fin.last D.R.rS then -U else 0 := by
    intro S U G a b
    induction a using Fin.lastCases with
    | last =>
      induction b using Fin.lastCases with
      | last => simp [FlagG.fvec, G.z_norm]
      | cast j =>
        simp only [FlagG.fvec, Fin.snoc_last, Fin.snoc_castSucc]
        rw [← hs, G.z_orth j]; simp
    | cast i =>
      induction b using Fin.lastCases with
      | last => simp [FlagG.fvec, G.z_orth]
      | cast j => simp [FlagG.fvec, G.e_iso]
  rcases a with a | a <;> rcases b with b | b
  · simp only [Ga, Matrix.fromBlocks_apply₁₁, Matrix.of_apply, Sum.elim_inl, brS]
    rw [key (S := 0) F a b]
  · rfl
  · simp only [Ga, Matrix.fromBlocks_apply₂₁, Matrix.conjTranspose_apply, Zhat, brS, Sum.elim_inl, Sum.elim_inr]
    exact hs _ _
  · simp only [Ga, Matrix.fromBlocks_apply₂₂, Matrix.of_apply, Sum.elim_inr, brS]
    rw [key (S := 0) F' a b]

theorem gaLoc_gram (D : Formalism.BasicNotions.D7) {M : ∀ p : PlF D, Formalism.MainNotions.S.Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep}
    (L : LocSp D M) (δ : ∀ p : PlF D, (D.s.atP p).Fp) (p : PlF D) {T T' : D.host.E}
    (F : FlagG (VS D) D.R.rS T) (F' : FlagG (VS D) D.R.rS T') (a b : Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1)) :
    GaLoc M δ p T T' (Zhat F F') a b =
      (L.H p).h (phi δ p b • L.bc p (Sum.elim F.fvec F'.fvec b)) (phi δ p a • L.bc p (Sum.elim F.fvec F'.fvec a)) := by
  rw [(L.H p).h_smul_left, h_smul_right' (L.H p), L.bc_form]
  simp only [GaLoc, Matrix.of_apply]
  rw [ga_gram]
  ring

theorem gaPlus_gram_G (D : Formalism.BasicNotions.D7) {M : ∀ p : PlF D, Formalism.MainNotions.S.Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep}
    (L : LocSp D M) (δ : ∀ p : PlF D, (D.s.atP p).Fp) (p : PlF D) {T T' : D.host.E}
    (F : FlagG (VS D) D.R.rS T) (F' : FlagG (VS D) D.R.rS T') (g : Formalism.MainNotions.S.Loc.SplitG (M p).L)
    (hg : (M p).split = some g) (a b : Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1)) :
    let x : Fin (D.R.rS + 1) → L.V p := fun j => frFac δ p j • L.bc p (F.fvec j)
    let x' : Fin (D.R.rS + 1) → L.V p := fun j => frFac δ p j • L.bc p (F'.fvec j)
    let mm := Sum.elim x (fun j => algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((g.q : (D.s.atP p).Fp)⁻¹) • (x' j - x j))
    GaPlus M δ p T T' (Zhat F F') a b = (L.H p).h (mm b) (mm a) := by
  intro x x' mm
  have hG : GaLoc M δ p T T' (Zhat F F') =
      Matrix.of (fun a b => (L.H p).h (Sum.elim x x' b) (Sum.elim x x' a)) := by
    ext a b
    rw [gaLoc_gram D L]
    rcases a with a | a <;> rcases b with b | b <;> rfl
  have hmm : ∀ b, mm b = ∑ i, (Matrix.fromBlocks 1
      (-(algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((g.q : (D.s.atP p).Fp)⁻¹)) •
        (1 : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Ep)) 0
      (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((g.q : (D.s.atP p).Fp)⁻¹) •
        (1 : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Ep))) i b • Sum.elim x x' i := by
    intro b
    rcases b with b | b
    · simp [mm, Fintype.sum_sum_type, Matrix.one_apply]
    · simp [mm, Fintype.sum_sum_type, Matrix.one_apply, sub_eq_neg_add, neg_smul]
      rw [Algebra.algebraMap_eq_smul_one]
  rw [hmm, hmm, gram_comb, ← hG]
  simp only [GaPlus, hg]

theorem gaPlus_eq_gram (D : Formalism.BasicNotions.D7) {M : ∀ p : PlF D, Formalism.MainNotions.S.Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep}
    (L : LocSp D M) (δ : ∀ p : PlF D, (D.s.atP p).Fp) (p : PlF D) {T T' : D.host.E}
    (F : FlagG (VS D) D.R.rS T) (F' : FlagG (VS D) D.R.rS T') (abelian₂ : Submodule (M p).L.O (L.V p))
    (T₀ T₀' : (D.s.atP p).Fp) :
    GaPlus M δ p T T' (Zhat F F') = (L.H p).gram ((L.H p).MMfam
      ({ abelian₂ := abelian₂, f := fun j => frFac δ p j • L.bc p (F.fvec j),
         f' := fun j => frFac δ p j • L.bc p (F'.fvec j), T := T₀, T' := T₀' } :
        Formalism.MainNotions.S.Loc.Term (L.V p) (M p) D.R.rS)) := by
  ext a b
  cases hs : (M p).split with
  | none =>
    simp only [GaPlus, hs, Formalism.MainNotions.S.Loc.HermSp.gram, Formalism.MainNotions.S.Loc.HermSp.MMfam, Matrix.of_apply]
    rw [gaLoc_gram D L]
    rcases a with a | a <;> rcases b with b | b <;> rfl
  | some g =>
    rw [gaPlus_gram_G D L δ p F F' g hs]
    simp only [Formalism.MainNotions.S.Loc.HermSp.gram, Formalism.MainNotions.S.Loc.HermSp.MMfam, hs, Matrix.of_apply]

theorem zhatLoc_eq (D : Formalism.BasicNotions.D7) {M : ∀ p : PlF D, Formalism.MainNotions.S.Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep}
    (L : LocSp D M) (δ : ∀ p : PlF D, (D.s.atP p).Fp) (p : PlF D) {T T' : D.host.E}
    (F : FlagG (VS D) D.R.rS T) (F' : FlagG (VS D) D.R.rS T') :
    ZhatLoc M δ p (Zhat F F') = (L.H p).Zhat (fun j => frFac δ p j • L.bc p (F.fvec j))
      (fun j => frFac δ p j • L.bc p (F'.fvec j)) := by
  ext a b
  simp only [ZhatLoc, Formalism.MainNotions.S.Loc.HermSp.Zhat, Matrix.of_apply]
  rw [(L.H p).h_smul_left, h_smul_right' (L.H p), L.bc_form]
  simp only [Zhat]
  ring

theorem nu_eq_zero_of_GZ (D : Formalism.BasicNotions.D7) {T T' : D.host.E} (F0 : FlagG (VS D) D.R.rS T)
    (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)) (Z : MatZ D) (hZ : GZ T T' Z = 0) :
    Formalism.L2.SG.CntLocal.nu T' F0 what₂ Z = 0 := by
  have hE : ∀ Λ, EZ T' F0 Λ Z = ∅ := by
    intro Λ
    ext F'
    simp only [EZ, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨⟨_, _, hG⟩, _, _, _, hZ'⟩
    exact hG (by rw [gz_eq, hZ', hZ])
  have hc : ∀ Λ, cntE T' F0 Λ Z = 0 := by
    intro Λ
    simp only [cntE, hE Λ, Set.mem_empty_iff_false, false_and, exists_false, Set.ofPred_false,
      Set.encard_empty]
  simp [Formalism.L2.SG.CntLocal.nu, hc]

end Formalism.L2.SG.CntLocal
