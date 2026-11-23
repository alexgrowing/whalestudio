import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlocksUnique

noncomputable section

namespace GlobalTheory.HeightCounting

open Formalism.BasicNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Formalism.L2.Host GlobalTheory.WeilDeligne

def CGK.ofSide {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂} (A : NAut N) : CGK A :=
  { A with }

theorem CGK.naut_ofSide {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂} (A : NAut N)
    (hE : IsEmpty N.Loc) : (CGK.ofSide A).naut hE = A := by
  have h1 : (fun i => hE.elim i) = A.muC := funext fun i => hE.elim i
  have h2 : (fun i => hE.elim i) = @NAut.jumpsInf _ _ _ _ A := funext fun i => hE.elim i
  cases A
  simp only [CGK.naut, CGK.ofSide]
  congr 1

theorem setBC_self (D : D7) : setBC D D.nbc = D := rfl

theorem setTy_self (D : D7) (hE : IsEmpty D.nd.Loc) : setTy D hE D.ntypes D.nStage_trivialCharacter_compat D.nStage_trivialCharacter_coeff_eq = D := rfl

theorem setCG_CG (D : D7) (hE : IsEmpty D.nd.Loc) (K : CGK D.naut) : (setCG D hE K).naut.CG = K.CG := rfl

theorem tame_lpSp {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} (h : IsPlaceOver A w) (n : ℕ) : (WD.lpSp h n).tame :=
  (WD.tame_mk _).2 fun σ hσ => (WDRep.unr_diag (h := h) (WDRep.spEig w n)).2 ⟨σ, Wild_le_Ine hσ⟩

theorem not_mono0_lpSp {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} (h : IsPlaceOver A w) {n : ℕ} (hn : 2 ≤ n) :
    ¬ (WD.lpSp h n).mono0 := by
  rw [WD.lpSp, WD.monodromyZero_ofWeilDeligneRepClass_iff, WDRep.sp_N]
  intro h0
  have := congrFun (LinearMap.congr_fun h0 (fun _ => 1)) ⟨1, hn⟩
  simp [shiftEnd_apply] at this

def RowWD.special (D : D7) : RowWD D where
  par _ w := WD.lpSp (D.nd.plOm.2 w) D.R.r
  sat _ _ := 0
  dim _ _ := WD.lpDim_lpSp _
  tame _ _ _ := tame_lpSp _ _

theorem RowWD.special_not_mono0 (D : D7) (σ w) : ¬ ((RowWD.special D).par σ w).mono0 :=
  not_mono0_lpSp _ (by have := D.R.two_le_m; have := D.R.m_add_three_le_k; unfold Ranks.r; omega)

def RowWD.ofUnr (D : D7) (c : D.what₂.FT → PlE D.host → Fin D.R.r → ℂˣ) (s : D.what₂.FT → PlE D.host → Multiset ℂ) :
    RowWD D where
  par σ w := WD.mk (WDRep.diag (D.nd.plOm.2 w) (c σ w))
  sat := s
  dim _ _ := by simp
  tame _ _ _ := WD.tame_of_unr ((WD.unr_mk _).2 (WDRep.unr_diag _))

def RowWD.ofSide (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut) (hT : LabTrue D T) (Rs : RowSide D)
    (hd : ∀ σ w, D.naut.lpDim (Rs.locR σ w) = D.R.r) : RowWD D where
  par σ w := T.e w (Rs.locR σ w)
  sat := Rs.satR
  dim σ w := (T.dim w _).trans (hd σ w)
  tame σ k v := by
    haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
    refine WD.tame_of_natDegree_lab (τ := D.ntypes.teichC k) (γ := D.ntypes.tg k v) ?_
    rw [← hT k v, ← Rs.lab_eq, (D.nd.lab_monic k σ v).2, T.dim, hd]

theorem BlocksUnique.not_cusp {D : D7} (h : BlocksUnique D) (χ : D.naut.CG 1) (hχ : D.naut.csd χ) (hχ' : D.naut.ralg χ)
    (π : D.naut.CG D.R.r) (hπ : D.naut.csd π) (hπ' : D.naut.ralg π) :
    ¬ ∀ w, IsSplitPl D.host w →
      isoLoc D.nd D.naut [⟨1, χ, D.R.r⟩] w = isoLoc D.nd D.naut [⟨D.R.r, π, 1⟩] w := by
  intro he
  have hr : 2 ≤ D.R.r := by have := D.R.two_le_m; have := D.R.m_add_three_le_k; unfold Ranks.r; omega
  have := h [⟨1, χ, D.R.r⟩] [⟨D.R.r, π, 1⟩] (by
    intro p hp
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact ⟨le_rfl, by simp only; omega, hχ, fun τ => by simpa using (D.naut.ralg_def χ).1 hχ' τ⟩
    · exact ⟨by simp only; omega, le_rfl, hπ, fun τ => by simpa using (D.naut.ralg_def π).1 hπ' τ⟩)
    (by simp [rankIso]) (by simp [rankIso]) he
  simp at this
  omega

end GlobalTheory.HeightCounting

end
