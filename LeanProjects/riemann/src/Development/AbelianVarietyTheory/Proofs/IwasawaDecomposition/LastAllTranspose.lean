import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedVectorEqOfStandardData
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsTwIffCanonEq
import Formalism.LocalToGlobal.HermitianForms.TiedBr
import Formalism.LocalToGlobal.HermitianForms.Interlace
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.InterlaceDifferenceShiftInvariant
import Formalism.LocalToGlobal.Columns.PolyFnLemmas
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueColumnSpacesStandardInFrameCoords
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsPtOfOfMem
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BranchingNormIdentityTrueColumnsMembers

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section
set_option maxHeartbeats 2000000

namespace GlobalTheory.Mem.Col2.LowerTie

section Gen
open Formalism.L2.Forms
variable {ι : Type} [Fintype ι] {N n : ℕ}

theorem lastAll_transpose (a : ι → ℂˣ) (τ : ι) :
    (((lastAll N a τ : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ))ᵀ = ((lastAll N a τ : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) := by
  ext i j
  simp only [Matrix.transpose_apply, lastAll, lastGL_apply]
  by_cases h : i = j
  · subst h; rfl
  · rw [if_neg h, if_neg (Ne.symm h)]

theorem fnOf_lastAll (G : ι → Matrix (Fin N) (Fin N) ℂ) (lam : ι → DomWeight N) (a : ι → ℂˣ) (P : Pol ℂ ι N) :
    fnOf G (shiftOf lam) (fun τ => ((lastAll N a τ : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ)) P =
      fnOf G (shiftOf lam) 1 (actP lam (lastAll N a) P) := by
  have h := fnOf_mul G (shiftOf lam) (fun τ => ((lastAll N a τ : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ)) 1 P
  simp only [Pi.one_apply, mul_one] at h
  rw [h]
  refine congrArg (fnOf G (shiftOf lam) 1) ?_
  have e : trAct (lastAll N a) = Formalism.GradedWeylDivisibility.blockAct ℂ (fun τ => ((lastAll N a τ : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ)) := by
    unfold trAct
    simp only [lastAll_transpose]
  simp only [actP, detTwK, detPow, shiftOf, LinearMap.smul_apply, AlgHom.toLinearMap_apply, e]
  refine congrArg (· • _) (Finset.prod_congr rfl fun τ _ => ?_)
  rw [Units.val_zpow_eq_zpow_val, Matrix.GeneralLinearGroup.val_det_apply]

theorem scalar_last (hN : N = n + 1) (lam : DomWeight N) (sg : DomWeight n) (h : ∀ i, 0 ≤ Br.bBr hN lam sg i) (a : ℂˣ) :
    (a : ℂ) ^ (-Br.nBr lam sg) * ((a : ℂ) ^ lam.detShift * ∏ s, (a : ℂ) ^ (Br.bBr hN lam sg s).toNat) = 1 := by
  subst hN
  have ha : (a : ℂ) ≠ 0 := a.ne_zero
  have e : ∏ s, (a : ℂ) ^ (Br.bBr rfl lam sg s).toNat = (a : ℂ) ^ (∑ s, Br.bBr rfl lam sg s) := by
    have : ∀ s, (a : ℂ) ^ (Br.bBr rfl lam sg s).toNat = (a : ℂ) ^ (Br.bBr rfl lam sg s) := fun s => by
      rw [← zpow_natCast, Int.toNat_of_nonneg (h s)]
    simp only [this]
    induction (Finset.univ : Finset (Fin n)) using Finset.cons_induction with
    | empty => simp
    | cons x s hx ih => rw [Finset.prod_cons, Finset.sum_cons, zpow_add₀ ha, ih]
  have e2 : Br.nBr lam sg = lam.detShift + ∑ s, Br.bBr rfl lam sg s := by
    simp only [Br.nBr, Br.bBr, DomWeight.detShift, Finset.sum_sub_distrib, Fin.sum_univ_castSucc]
    simp [Br.iC]
    change ∑ i : Fin n, lam.w i.castSucc + lam.w (Fin.last n) - ∑ i, sg.w i = lam.w (Fin.last n) + (∑ x : Fin n, lam.w x.castSucc - ∑ i, sg.w i)
    ring
  rw [e, ← zpow_add₀ ha, ← zpow_add₀ ha, e2]
  simp

theorem branchingProjection_act_last (hN : N = n + 1) (lam : ι → DomWeight N) (sg : ι → DomWeight n)
    (h : ∀ τ i, 0 ≤ Br.bBr hN (lam τ) (sg τ) i) (a : ι → ℂˣ) (P : Pol ℂ ι N) :
    (∏ τ, (a τ : ℂ) ^ (-Br.nBr (lam τ) (sg τ))) • (Br.brStdP hN lam sg (actP lam (lastAll N a) P) : Pol ℂ ι n) =
      (Br.brStdP hN lam sg P : Pol ℂ ι n) := by
  rw [branchingProjection_last, smul_smul]
  have e : (∏ τ, (a τ : ℂ) ^ (-Br.nBr (lam τ) (sg τ))) * (detTwK lam (lastAll N a) * ∏ τ, ∏ s, (a τ : ℂ) ^ Br.bExp hN lam sg τ s) = 1 := by
    have h2 : detTwK lam (lastAll N a) = ∏ τ, (a τ : ℂ) ^ (lam τ).detShift := by
      simp only [detTwK, detPow, lastAll, det_lastGL' hN, Units.val_zpow_eq_zpow_val]
    rw [h2, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one fun τ _ => ?_
    exact scalar_last hN (lam τ) (sg τ) (h τ) (a τ)
  rw [e, one_smul]
end Gen
end GlobalTheory.Mem.Col2.LowerTie

namespace GlobalTheory.Mem.Col2.LowerTie

section Rec
variable {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word)

theorem embT_eq : Formalism.L2.Forms.embT (I.rec7 l Z) = embAt B.embLL B.fields.emb := by
  funext τ
  ext y
  show B.host.φ₀ _ = _
  rw [← B.embE_φ₀]
  rfl

include l in
theorem pi_mul_star : ((X.piT u : 𝓞 B.host.E) : B.host.E) * star ((X.piT u : 𝓞 B.host.E) : B.host.E) = (B.T u : B.host.E) := by
  have h := congrArg (fun z : 𝓞 B.fields.E => (z : B.fields.E)) (l.pr.piT_norm u)
  simp only [map_mul, map_natCast] at h
  exact h

include l in
theorem star_pi_ne : star ((X.piT u : 𝓞 B.host.E) : B.host.E) ≠ 0 := (l.per u I.mu0).tz_ne

theorem bZ_std (hO : I.Ok) (hP : TC.Pins B X) (z0 : Fin (B.R.N B.R.m) → B.host.E)
    (hz : ∀ j, z0 j = if j.1 + 1 = B.R.N B.R.m then ((X.piT u : 𝓞 B.host.E) : B.host.E) else 0) :
    bZ (D := I.rec7 l Z) u z0 =
      Matrix.diagonal fun i : Fin (B.R.N B.R.m) => if i.1 + 1 = B.R.N B.R.m then (star ((X.piT u : 𝓞 B.host.E) : B.host.E))⁻¹ else 1 := by
  have hc := (spaces_in_coordinates I hO hP l Z).2.2.1
  have hπ := pi_mul_star I l u
  have h0 := star_pi_ne I l u
  have hp0 : ((X.piT u : 𝓞 B.host.E) : B.host.E) ≠ 0 := fun h => h0 (by rw [h, star_zero])
  refine Matrix.ext fun (a b : Fin (B.R.N B.R.m)) => ?_
  have ha := a.2
  have hb := b.2
  rw [Matrix.diagonal_apply]
  by_cases h : b.1 < B.R.N B.R.m - 1
  · have e : bZ (D := I.rec7 l Z) u z0 a b = iXc (I.rec7 l Z) (Pi.single ⟨b.1, h⟩ 1) a := by
      exact (dif_pos h).trans (LinearMap.toMatrix'_apply _ _ _)
    refine (e.trans (hc _ a)).trans ?_
    by_cases hab : a = b
    · subst hab
      rw [dif_pos h, if_pos rfl, if_neg (by omega)]
      exact Pi.single_eq_same (M := fun _ : Fin (B.R.N B.R.m - 1) => B.host.E) _ _
    · rw [if_neg hab]
      split_ifs with h2
      · exact Pi.single_eq_of_ne (M := fun _ : Fin (B.R.N B.R.m - 1) => B.host.E) (fun h3 => hab (Fin.ext (Fin.mk.inj_iff.1 h3))) _
      · rfl
  · have e : bZ (D := I.rec7 l Z) u z0 a b = z0 a / (B.T u : B.host.E) := by
      exact dif_neg h
    rw [e, hz, ← hπ]
    by_cases hab : a = b
    · subst hab
      rw [if_pos rfl, if_pos (by omega), if_pos (by omega)]
      field_simp
    · rw [if_neg hab, if_neg (fun h3 => hab (Fin.ext (by omega))), zero_div]

def aT (τ : Tau B.R) : ℂˣ :=
  Units.mk0 (embAt B.embLL B.fields.emb τ (star ((X.piT u : 𝓞 B.host.E) : B.host.E))) ((map_ne_zero _).2 (star_pi_ne I l u))

theorem mZ_std (hO : I.Ok) (hP : TC.Pins B X) (z0 : Fin (B.R.N B.R.m) → B.host.E)
    (hz : ∀ j, z0 j = if j.1 + 1 = B.R.N B.R.m then ((X.piT u : 𝓞 B.host.E) : B.host.E) else 0) :
    mZ (D := I.rec7 l Z) u z0 =
      fun τ => ((lastAll (B.R.N B.R.m) (aT I l u) τ : GL (Fin (B.R.N B.R.m)) ℂ) : Matrix (Fin (B.R.N B.R.m)) (Fin (B.R.N B.R.m)) ℂ) := by
  have h0 := star_pi_ne I l u
  have e : (bZ (D := I.rec7 l Z) u z0)⁻¹ =
      Matrix.diagonal fun i : Fin (B.R.N B.R.m) => if i.1 + 1 = B.R.N B.R.m then star ((X.piT u : 𝓞 B.host.E) : B.host.E) else 1 := by
    rw [bZ_std I l Z u hO hP z0 hz]
    refine Matrix.inv_eq_left_inv (A := Matrix.diagonal fun i : Fin (B.R.N B.R.m) =>
      if i.1 + 1 = B.R.N B.R.m then (star ((X.piT u : 𝓞 B.host.E) : B.host.E))⁻¹ else 1) ?_
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    split_ifs
    · exact mul_inv_cancel₀ h0
    · exact mul_one 1
  funext τ
  refine Matrix.ext fun (a b : Fin (B.R.N B.R.m)) => ?_
  have e2 : mZ (D := I.rec7 l Z) u z0 τ a b = embAt B.embLL B.fields.emb τ ((Matrix.diagonal fun i : Fin (B.R.N B.R.m) =>
      if i.1 + 1 = B.R.N B.R.m then star ((X.piT u : 𝓞 B.host.E) : B.host.E) else 1) a b) := by
    unfold mZ
    rw [e, embT_eq]
    rfl
  rw [e2]
  simp only [lastAll, lastGL_apply, Matrix.diagonal_apply]
  split_ifs <;> simp [aT]

end Rec
end GlobalTheory.Mem.Col2.LowerTie

namespace GlobalTheory.Mem.Col2.LowerTie

theorem lowerMap_std : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)),
    ∀ (u : B.Word) (Ch : ℕ → Type) (chOf : ∀ i, ((I.rec7 l Z).mem u).C.cls i → Ch i) (F : FormsTiedSym (I.rec7 l Z) u Ch chOf),
    I.StdF l Z u F → ∀ (ψ : ((I.rec7 l Z).mem u).P.Wz) (c : ((I.rec7 l Z).fm u).clsP)
      (P : MvPolynomial ((I.rec7 l Z).what₂.Tau × Fin ((I.rec7 l Z).R.N (I.rec7 l Z).R.m) × Fin ((I.rec7 l Z).R.N (I.rec7 l Z).R.m)) ℂ),
      (∀ s, F.eWz ψ c s = fnOf _ (shiftOf (Formalism.L2.Forms.lamT u (I.rec7 l Z).R.m)) (mZ u F.til.z0) P
        ((F.val (I.rec7 l Z).R.m le_rfl (Or.inr rfl)).eY s)) →
      F.valP.eW (((I.rec7 l Z).mem u).P.lowerMap ψ) c =
        fnOf _ (shiftOf (Formalism.L2.Forms.sgT u)) 1 (Formalism.L2.Ker.brTen (I.rec7 l Z) u P) := by
  intro B X I hO hP l Z u Ch chOf F hS ψ c P hψ
  have hl : Formalism.MainNotions.product_first_zeroth_parts.lamTr (I.rec7 l Z) u = B.wts.lamTrue u B.R.m := funext (trueWeight_lastStep_trueColumns I l Z u)
  have hs : Formalism.MainNotions.product_first_zeroth_parts.sgTr (I.rec7 l Z) u = B.wts.sgTrue := funext (trueRowWeight_trueColumns I l Z u)
  have hl' : Formalism.L2.Forms.lamT (D := I.rec7 l Z) u (I.rec7 l Z).R.m = B.wts.lamTrue u B.R.m := hl
  have hs' : Formalism.L2.Forms.sgT (D := I.rec7 l Z) u = B.wts.sgTrue := hs
  have hI : ∀ τ i, 0 ≤ Br.bBr (N_m_succ B.R) (B.wts.lamTrue u B.R.m τ) (B.wts.sgTrue τ) i := by
    intro τ i
    have h := (Formalism.MainNotions.product_first_zeroth_parts.interlaceTr (I.rec7 l Z) u (sg_interlace F.valP) τ i).1
    rw [hl, hs] at h
    exact sub_nonneg.2 h
  have h1 : ψ c = fnOf (Col2.Gr B.fields.emb B.embLL (B.R.N B.R.m)) (shiftOf (B.wts.lamTrue u B.R.m)) 1
      (actP (B.wts.lamTrue u B.R.m) (lastAll (B.R.N B.R.m) (aT I l u)) P) := by
    refine Eq.trans ?_ (fnOf_lastAll (Col2.Gr B.fields.emb B.embLL (B.R.N B.R.m)) (B.wts.lamTrue u B.R.m) (aT I l u) P)
    funext s
    have h := hψ s
    rw [hS.eWz, hl', mZ_std I l Z u hO hP _ hS.z0] at h
    refine h.trans ?_
    have h2 := hS.eY B.R.m le_rfl (Or.inr rfl) s
    exact congrArg (fnOf (Col2.Gr B.fields.emb B.embLL (B.R.N B.R.m)) (shiftOf (B.wts.lamTrue u B.R.m)) _ P) (Subtype.ext h2)
  have h3 : polOf (Col2.Gr B.fields.emb B.embLL (B.R.N B.R.m)) (shiftOf (B.wts.lamTrue u B.R.m)) (Col2.fr0 B.fields.emb B.embLL (B.R.N B.R.m)) (ψ c) =
      actP (B.wts.lamTrue u B.R.m) (lastAll (B.R.N B.R.m) (aT I l u)) P := by
    have e : (fun τ => ((Col2.fr0 B.fields.emb B.embLL (B.R.N B.R.m)).1 τ)⁻¹) = 1 := funext fun τ => inv_one
    have h := polOf_fnOf (Col2.Gr B.fields.emb B.embLL (B.R.N B.R.m)) (shiftOf (B.wts.lamTrue u B.R.m)) (Col2.fr0 B.fields.emb B.embLL (B.R.N B.R.m))
      (actP (B.wts.lamTrue u B.R.m) (lastAll (B.R.N B.R.m) (aT I l u)) P)
    rw [e] at h
    rw [h1]
    exact h
  have h4 : Formalism.L2.Ker.brTen (I.rec7 l Z) u P = (Br.brStdP (N_m_succ B.R) (B.wts.lamTrue u B.R.m) B.wts.sgTrue P : Pol ℂ (Tau B.R) (B.R.N B.R.m - 1)) := by
    have h := blk_brOne (ι := Tau B.R) (N_m_succ B.R) (B.wts.lamTrue u B.R.m) B.wts.sgTrue P
    refine Eq.trans ?_ h
    unfold Formalism.L2.Ker.brTen
    rw [hl, hs]
    rfl
  have h5 := branchingProjection_act_last (N_m_succ B.R) (B.wts.lamTrue u B.R.m) B.wts.sgTrue hI (aT I l u) P
  funext s
  rw [hS.eW _ c s ⟨s.1, s.2⟩ rfl, hs', h4, ← h5, ← h3]
  rfl

theorem chi_top_std : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)),
    ∀ (u : B.Word) (Ch : ℕ → Type) (chOf : ∀ i, ((I.rec7 l Z).mem u).C.cls i → Ch i) (F : FormsTiedSym (I.rec7 l Z) u Ch chOf),
    I.StdF l Z u F → ∃ n : ℕ, 0 < n ∧ ∀ x : (F.cls (I.rec7 l Z).R.m le_rfl (Or.inr rfl)).lev.U,
      (((F.cls (I.rec7 l Z).R.m le_rfl (Or.inr rfl)).lev.chi x : ℂˣ) : ℂ) ^ n = 1 ∧
        ∃ r : (I.rec7 l Z).what₂.LL, (I.rec7 l Z).what₂.embLL r = (((F.cls (I.rec7 l Z).R.m le_rfl (Or.inr rfl)).lev.chi x : ℂˣ) : ℂ) :=
  fun {B} {_} I hO hP l Z u _ _ F hS =>
    ChiFinTop.chi_top_root_rat I hO hP l Z u (F.cls B.R.m le_rfl (Or.inr rfl)) (hS.ends B.R.m le_rfl (Or.inr rfl))

end GlobalTheory.Mem.Col2.LowerTie

end
