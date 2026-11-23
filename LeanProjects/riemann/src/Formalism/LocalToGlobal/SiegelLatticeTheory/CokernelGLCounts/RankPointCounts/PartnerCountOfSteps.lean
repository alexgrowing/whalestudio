import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.PartnerCount

noncomputable section

namespace Formalism.L2.SG.Pf.PCount

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut
  Formalism.L2.SG.LsDatumB
open Classical ValuativeRel
open Formalism.L2.SG.Pf.AtPt Formalism.L2.SG.TermLoc

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Lead

variable {K : Type*} [CommRing K]

def leadM {m : ℕ} (X : Matrix (Fin m) (Fin m) K) (l : ℕ) : K :=
  if hl : l ≤ m then (X.submatrix (Fin.castLE hl) (Fin.castLE hl)).det else 0

theorem sum_castLE {A : Type*} [AddCommMonoid A] {l m : ℕ} (hl : l ≤ m) (g : Fin m → A)
    (hg : ∀ a : Fin m, l ≤ a.val → g a = 0) : ∑ a, g a = ∑ a : Fin l, g (Fin.castLE hl a) := by
  have e : ∑ a : Fin l, g (Fin.castLE hl a) = ∑ a ∈ Finset.univ.map (Fin.castLEEmb hl), g a := by
    rw [Finset.sum_map]; rfl
  rw [e]
  refine (Finset.sum_subset (Finset.subset_univ _) ?_).symm
  intro a _ ha
  apply hg
  by_contra h
  exact ha (Finset.mem_map.2 ⟨⟨a.val, Nat.lt_of_not_le h⟩, Finset.mem_univ _, Fin.ext rfl⟩)

theorem leadM_mul {m : ℕ} {L X U : Matrix (Fin m) (Fin m) K} (hL : IsLo L) (hU : IsUp U) (l : ℕ) :
    leadM (L * X * U) l = leadM X l := by
  unfold leadM
  split_ifs with hl
  · have e : (L * X * U).submatrix (Fin.castLE hl) (Fin.castLE hl) =
        L.submatrix (Fin.castLE hl) (Fin.castLE hl) * X.submatrix (Fin.castLE hl) (Fin.castLE hl) *
          U.submatrix (Fin.castLE hl) (Fin.castLE hl) := by
      ext i j
      simp only [Matrix.submatrix_apply, Matrix.mul_apply]
      refine (sum_castLE hl _ ?_).trans (Finset.sum_congr rfl fun b _ => ?_)
      · intro b hb
        have hj := j.isLt
        rw [hU.2 _ _ (by simp only [Fin.lt_def, Fin.val_castLE]; omega), mul_zero]
      · congr 1
        refine sum_castLE hl _ fun a ha => ?_
        have hi := i.isLt
        rw [hL.2 _ _ (by simp only [Fin.lt_def, Fin.val_castLE]; omega), zero_mul]
    rw [e, Matrix.det_mul, Matrix.det_mul]
    have h1 : (L.submatrix (Fin.castLE hl) (Fin.castLE hl)).det = 1 :=
      det_lo' ⟨fun a => hL.1 _, fun a b hab => hL.2 _ _ hab⟩
    have h2 : (U.submatrix (Fin.castLE hl) (Fin.castLE hl)).det = 1 :=
      det_up' ⟨fun a => hU.1 _, fun a b hab => hU.2 _ _ hab⟩
    rw [h1, h2, one_mul, mul_one]
  · rfl

end Lead

section Mats

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Loc.Model F E)

def mkMat {m : ℕ} (P : Matrix (Fin m) (Fin m) E) (hP : ∀ a b, P a b ∈ M.R) (hu : IsUnit P.det) : M.Mat m :=
  ⟨Matrix.of fun a b => ⟨P a b, hP a b⟩, by
    have : (Matrix.of fun a b => (⟨P a b, hP a b⟩ : M.R)).map M.R.subtype = P := rfl
    rw [this]; exact hu⟩

theorem clsOf_mk {m : ℕ} (P : Matrix (Fin (m + 1)) (Fin (m + 1)) E) (hP : ∀ a b, P a b ∈ M.R)
    (hu : IsUnit P.det) : clsOf M P = some (Quotient.mk (M.isoSetoid m) (mkMat M P hP hu)) := by
  unfold clsOf
  rw [dif_pos ⟨hP, hu⟩]
  rfl

theorem clsOf_map {m : ℕ} (Z : M.Mat (m + 1)) :
    clsOf M (Z.Z.map M.R.subtype) = some (Quotient.mk (M.isoSetoid m) Z) := by
  exact clsOf_mk M (Z.Z.map M.R.subtype) (fun a b => (Z.Z a b).2) Z.unit

theorem nIso_mk_out {m : ℕ} (Z₁ Z₂ : M.Mat (m + 1)) :
    M.nIso (Quotient.out (Quotient.mk (M.isoSetoid m) Z₁)) (Quotient.out (Quotient.mk (M.isoSetoid m) Z₂)) =
      M.nIso Z₁ Z₂ := by
  have h1 : Nonempty (M.Iso (Quotient.out (Quotient.mk (M.isoSetoid m) Z₁)) Z₁) :=
    Quotient.mk_out (s := M.isoSetoid m) Z₁
  have h2 : Nonempty (M.Iso (Quotient.out (Quotient.mk (M.isoSetoid m) Z₂)) Z₂) :=
    Quotient.mk_out (s := M.isoSetoid m) Z₂
  exact nIso_congr M h1.some h2.some

def headMat {m : ℕ} (P : Matrix (Fin (m + 1)) (Fin (m + 1)) E) (hP : ∀ a b, P a b ∈ M.R)
    (hu : IsUnit (leadM P m)) : M.Mat m :=
  ⟨Matrix.of fun a b => ⟨P a.castSucc b.castSucc, hP _ _⟩, by
    have e1 : (Matrix.of fun a b => (⟨P a.castSucc b.castSucc, hP _ _⟩ : M.R)).map M.R.subtype =
        P.submatrix (Fin.castLE (Nat.le_succ m)) (Fin.castLE (Nat.le_succ m)) := by
      ext a b; rfl
    have e2 : leadM P m = (P.submatrix (Fin.castLE (Nat.le_succ m)) (Fin.castLE (Nat.le_succ m))).det := by
      unfold leadM; exact dif_pos _
    rw [e1, ← e2]; exact hu⟩

end Mats

section Cut

def BridgeBA : Prop :=
  ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Loc.Model F E) (m : ℕ) (n s : E) (P₁ P₂ X₁ X₂ L₁ U₁ L₂ U₂ : Matrix (Fin (m + 1)) (Fin (m + 1)) E),
    IsLo L₁ → IsUp U₁ → IsLo L₂ → IsUp U₂ → P₁ = L₁ * X₁ * U₁ → P₂ = L₂ * X₂ * U₂ →
    (∀ a : Fin m, X₁ a.castSucc (Fin.last m) = 0 ∧ X₁ (Fin.last m) a.castSucc = 0 ∧
      X₂ a.castSucc (Fin.last m) = 0 ∧ X₂ (Fin.last m) a.castSucc = 0) →
    X₁ (Fin.last m) (Fin.last m) = s → X₂ (Fin.last m) (Fin.last m) = s → IsUnit (s + n) → n ∈ M.R →
    ∀ (Y₁ Y₂ : M.Mat m) (be₁ be₂ al₁ al₂ : Fin m → M.R),
      (∀ a b : Fin m, (Y₁.Z a b : E) = P₁ a.castSucc b.castSucc ∧ (Y₂.Z a b : E) = P₂ a.castSucc b.castSucc) →
      (∀ a : Fin m, (be₁ a : E) = P₁ a.castSucc (Fin.last m) ∧ (be₂ a : E) = P₂ a.castSucc (Fin.last m) ∧
        (al₁ a : E) = P₁ (Fin.last m) a.castSucc ∧ (al₂ a : E) = P₂ (Fin.last m) a.castSucc) →
      (∀ a b, P₁ a b ∈ M.R) → (∀ a b, P₂ a b ∈ M.R) →
      ∃ Z₁ Z₂ : M.Mat (m + 1), Z₁.Z.map M.R.subtype = P₁ + n • Ecorner m ∧
        Z₂.Z.map M.R.subtype = P₂ + n • Ecorner m ∧ M.nIsoBA Y₁ Y₂ be₁ be₂ al₁ al₂ = M.nIso Z₁ Z₂

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D)

def LeadZZ : Prop :=
  ∀ (p : PlF D) (Zh : MatP D p) (T T' : (D.s.atP p).Fp),
    (leadM Zh D.R.rS = 0 ↔ leadM (Loc.HermSp.ZZplusOf (Zd.M p) Zh T T') D.R.rS = 0) ∧
    (IsUnit (leadM Zh D.R.rS) ↔ IsUnit (leadM (Loc.HermSp.ZZplusOf (Zd.M p) Zh T T') D.R.rS)) ∧
    (leadM Zh D.R.rS = 0 → IsUnit (leadM Zh (D.R.rS + 1)) →
      IsUnit (Loc.HermSp.ZZplusOf (Zd.M p) Zh T T').det)

def ModKind : Prop :=
  ∀ (p : PlF D) (T T' : ℕ) (w : Point D.host.E (D.R.rS + 1)),
    (Dmin w D.R.rS = 0 → leadM (modMat Zd.δ T T' p w) D.R.rS = 0) ∧
    (Dmin w D.R.rS ≠ 0 → IsUnit (leadM (modMat Zd.δ T T' p w) D.R.rS) ∧
      (∀ a : Fin D.R.rS, modMat Zd.δ T T' p w a.castSucc (Fin.last D.R.rS) = 0 ∧
        modMat Zd.δ T T' p w (Fin.last D.R.rS) a.castSucc = 0) ∧
      modMat Zd.δ T T' p w (Fin.last D.R.rS) (Fin.last D.R.rS) =
        blkMod Zd.δ T T' p (D.R.rS + 1) 1 (zetaOf w) ∧
      IsUnit (blkMod Zd.δ T T' p (D.R.rS + 1) 1 (zetaOf w) +
        ((nSh (blkMod Zd.δ T T' p (D.R.rS + 1) 1 (zetaOf w)) : ℕ) : (D.s.atP p).Ep)))

theorem add_cornE_zero (p : PlF D) (X : MatP D p) : X + cornE p 0 = X := by
  ext a b; simp [cornE]

theorem loUp_of_hyp {p : PlF D} {uL uU : MatP D p} (h1 : ∀ a, uL a a = 1 ∧ uU a a = 1)
    (h2 : ∀ a b, a < b → uL a b = 0 ∧ uU b a = 0) : IsLo uL ∧ IsUp uU :=
  ⟨⟨fun a => (h1 a).1, fun a b hab => (h2 a b hab).1⟩, ⟨fun a => (h1 a).2, fun a b hab => (h2 a b hab).2⟩⟩

set_option maxHeartbeats 1000000 in

theorem partnerIsomorphismCount_of_bounds (hT2 : Formalism.MainNotions.ThinScalesBound.T2 D) (hI : IntGenP Zd) (hL : LeadZZ Zd) (hK : ModKind Zd) (hB : BridgeBA) :
    PartnerIsomorphismCount Zd := by
  intro p T T' w w' t₁ f₂' φ φ' hk hT hT' hyp h1 h2 hint2
  have hkd : (Dmin w D.R.rS = 0 ↔ Dmin w' D.R.rS = 0) := by
    have hk' := hk
    unfold kind at hk'
    constructor
    · intro h; by_contra h'; rw [if_pos h, if_neg h'] at hk'; exact absurd hk' (by simp)
    · intro h; by_contra h'; rw [if_neg h', if_pos h] at hk'; exact absurd hk' (by simp)
  obtain ⟨uL, uU, hd, ho, hP1⟩ := h1
  obtain ⟨uL', uU', hd', ho', hP2⟩ := h2
  obtain ⟨hLo, hUp⟩ := loUp_of_hyp hd ho
  obtain ⟨hLo', hUp'⟩ := loUp_of_hyp hd' ho'
  have hT2p := hT2 _ _ (Zd.M p) (Zd.agree p).1 (Vp D p) (locH Zd p) (finrank_Vp p) t₁ hyp.1 t₁.f f₂' φ φ'
    hyp.2.1 hyp.2.2.1 hyp.2.2.2.1 hyp.2.2.2.2.1 hyp.2.2.2.2.2
  dsimp only at hT2p
  have hint1 : ∀ a b, (locH Zd p).ZZplus t₁ a b ∈ (Zd.M p).R := hI p t₁ hyp.1
  have hLZ1 := hL p ((locH Zd p).Zhat t₁.f t₁.f') t₁.T t₁.T'
  have hLZ2 := hL p ((locH Zd p).Zhat t₁.f f₂') t₁.T t₁.T'
  have hlead1 : leadM ((locH Zd p).ZZplus t₁) D.R.rS = leadM (modMat Zd.δ T T' p w) D.R.rS := by
    rw [hP1]; exact leadM_mul hLo hUp _
  have hlead2 : leadM (Loc.HermSp.ZZplusOf (Zd.M p) ((locH Zd p).Zhat t₁.f f₂') t₁.T t₁.T') D.R.rS =
      leadM (modMat Zd.δ T T' p w') D.R.rS := by
    rw [hP2]; exact leadM_mul hLo' hUp' _
  by_cases hD : Dmin w D.R.rS = 0
  · have hD' := hkd.1 hD
    have hsh : cornerSh Zd.δ T T' p w = 0 := by unfold cornerSh; rw [if_pos hD]
    have hsh' : cornerSh Zd.δ T T' p w' = 0 := by unfold cornerSh; rw [if_pos hD']
    have e1 : (locH Zd p).ZZplus t₁ + cornE p (cornerSh Zd.δ T T' p w) = (locH Zd p).ZZplus t₁ := by
      rw [hsh]; exact add_cornE_zero _ _
    have e2 : Loc.HermSp.ZZplusOf (Zd.M p) ((locH Zd p).Zhat t₁.f f₂') t₁.T t₁.T' + cornE p (cornerSh Zd.δ T T' p w') =
        Loc.HermSp.ZZplusOf (Zd.M p) ((locH Zd p).Zhat t₁.f f₂') t₁.T t₁.T' := by
      rw [hsh']; exact add_cornE_zero _ _
    rw [e1, e2]
    have hl1 : leadM ((locH Zd p).ZZplus t₁) D.R.rS = 0 := hlead1.trans ((hK p T T' w).1 hD)
    have hl2 : leadM (Loc.HermSp.ZZplusOf (Zd.M p) ((locH Zd p).Zhat t₁.f f₂') t₁.T t₁.T') D.R.rS = 0 :=
      hlead2.trans ((hK p T T' w').1 hD')
    have hDl : (locH Zd p).Dl t₁.f t₁.f' D.R.rS = 0 := hLZ1.1.2 hl1
    have hu1 : IsUnit ((locH Zd p).ZZplus t₁).det := hLZ1.2.2 (hLZ1.1.2 hl1) hyp.1.1.2.2.2.1
    by_cases hu2 : IsUnit (Loc.HermSp.ZZplusOf (Zd.M p) ((locH Zd p).Zhat t₁.f f₂') t₁.T t₁.T').det
    · rw [clsOf_mk (Zd.M p) _ hint1 hu1, clsOf_mk (Zd.M p) _ hint2 hu2]
      show _ = (Zd.M p).nIso _ _
      rw [nIso_mk_out]
      exact hT2p.1 hDl _ _ rfl rfl
    · have hc2 : clsOf (Zd.M p) (Loc.HermSp.ZZplusOf (Zd.M p) ((locH Zd p).Zhat t₁.f f₂') t₁.T t₁.T') = none := by
        unfold clsOf; rw [dif_neg (fun h => hu2 h.2)]
      rw [hc2]
      have h0 : ∀ o : Option ((Zd.M p).Cls D.R.rS), nIsoO Zd.M p o none = 0 := fun o => by cases o <;> rfl
      rw [h0, Nat.card_eq_zero]
      left
      constructor
      rintro ⟨Λ₂, hg, -⟩
      exact hu2 (hLZ2.2.2 (hLZ2.1.2 hl2) hg.1.2.2.2.1)
  · have hD' : Dmin w' D.R.rS ≠ 0 := fun h => hD (hkd.2 h)
    have hz : zetaOf w = zetaOf w' := by
      unfold kind at hk; rw [if_neg hD, if_neg hD'] at hk; exact Option.some_inj.1 hk
    obtain ⟨hu1, hcol1, hc1, hs1⟩ := (hK p T T' w).2 hD
    obtain ⟨hu2, hcol2, hc2, -⟩ := (hK p T T' w').2 hD'
    rw [← hz] at hc2
    have hsh : cornerSh Zd.δ T T' p w =
        ((nSh (blkMod Zd.δ T T' p (D.R.rS + 1) 1 (zetaOf w)) : ℕ) : (D.s.atP p).Ep) := by
      unfold cornerSh; rw [if_neg hD]
    have hsh' : cornerSh Zd.δ T T' p w' =
        ((nSh (blkMod Zd.δ T T' p (D.R.rS + 1) 1 (zetaOf w)) : ℕ) : (D.s.atP p).Ep) := by
      unfold cornerSh; rw [if_neg hD', ← hz]
    rw [hsh, hsh', cornE_eq]
    have hl1 : IsUnit (leadM ((locH Zd p).ZZplus t₁) D.R.rS) := hlead1 ▸ hu1
    have hl2 : IsUnit (leadM (Loc.HermSp.ZZplusOf (Zd.M p) ((locH Zd p).Zhat t₁.f f₂') t₁.T t₁.T') D.R.rS) :=
      hlead2 ▸ hu2
    have hDl : IsUnit ((locH Zd p).Dl t₁.f t₁.f' D.R.rS) := hLZ1.2.1.2 hl1
    have hcard := hT2p.2 hDl (headMat (Zd.M p) _ hint1 hl1) (headMat (Zd.M p) _ hint2 hl2)
      (fun a => ⟨(locH Zd p).ZZplus t₁ a.castSucc (Fin.last _), hint1 _ _⟩)
      (fun a => ⟨Loc.HermSp.ZZplusOf (Zd.M p) ((locH Zd p).Zhat t₁.f f₂') t₁.T t₁.T' a.castSucc (Fin.last _),
        hint2 _ _⟩)
      (fun a => ⟨(locH Zd p).ZZplus t₁ (Fin.last _) a.castSucc, hint1 _ _⟩)
      (fun a => ⟨Loc.HermSp.ZZplusOf (Zd.M p) ((locH Zd p).Zhat t₁.f f₂') t₁.T t₁.T' (Fin.last _) a.castSucc,
        hint2 _ _⟩)
      (fun a b => ⟨rfl, rfl⟩) (fun a => ⟨rfl, rfl, rfl, rfl⟩)
    obtain ⟨Z₁, Z₂, e₁, e₂, hb⟩ := hB (Zd.M p) D.R.rS _ _ _ _ _ _ _ _ _ _ hLo hUp hLo' hUp' hP1 hP2
      (fun a => ⟨(hcol1 a).1, (hcol1 a).2, (hcol2 a).1, (hcol2 a).2⟩) hc1 hc2 hs1
      (natCast_mem _ _) (headMat (Zd.M p) _ hint1 hl1) (headMat (Zd.M p) _ hint2 hl2)
      (fun a => ⟨(locH Zd p).ZZplus t₁ a.castSucc (Fin.last _), hint1 _ _⟩)
      (fun a => ⟨Loc.HermSp.ZZplusOf (Zd.M p) ((locH Zd p).Zhat t₁.f f₂') t₁.T t₁.T' a.castSucc (Fin.last _),
        hint2 _ _⟩)
      (fun a => ⟨(locH Zd p).ZZplus t₁ (Fin.last _) a.castSucc, hint1 _ _⟩)
      (fun a => ⟨Loc.HermSp.ZZplusOf (Zd.M p) ((locH Zd p).Zhat t₁.f f₂') t₁.T t₁.T' (Fin.last _) a.castSucc,
        hint2 _ _⟩)
      (fun a b => ⟨rfl, rfl⟩) (fun a => ⟨rfl, rfl, rfl, rfl⟩) hint1 hint2
    refine (show Nat.card (locSet Zd p t₁ f₂' φ φ') = _ from hcard).trans ?_
    have c1 : clsOf (Zd.M p) ((locH Zd p).ZZplus t₁ +
        ((nSh (blkMod Zd.δ T T' p (D.R.rS + 1) 1 (zetaOf w)) : ℕ) : (D.s.atP p).Ep) • Ecorner D.R.rS) =
        some (Quotient.mk ((Zd.M p).isoSetoid D.R.rS) Z₁) := by
      have h := clsOf_map (Zd.M p) Z₁; rw [e₁] at h; exact h
    have c2 : clsOf (Zd.M p) (Loc.HermSp.ZZplusOf (Zd.M p) ((locH Zd p).Zhat t₁.f f₂') t₁.T t₁.T' +
        ((nSh (blkMod Zd.δ T T' p (D.R.rS + 1) 1 (zetaOf w)) : ℕ) : (D.s.atP p).Ep) • Ecorner D.R.rS) =
        some (Quotient.mk ((Zd.M p).isoSetoid D.R.rS) Z₂) := by
      have h := clsOf_map (Zd.M p) Z₂; rw [e₂] at h; exact h
    exact hb.trans ((nIso_mk_out _ Z₁ Z₂).symm.trans (congrArg₂ (nIsoO Zd.M p) c1 c2).symm)

end Cut

end Formalism.L2.SG.Pf.PCount
