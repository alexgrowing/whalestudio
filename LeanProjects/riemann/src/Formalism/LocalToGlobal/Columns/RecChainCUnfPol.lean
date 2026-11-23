import Formalism.LocalToGlobal.Columns.RecChainUnfOne
import Formalism.LocalToGlobal.Columns.DGamAut

open NumberField IsDedekindDomain Module Matrix MvPolynomial
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.Ker

structure LevCh (X : Fields) (Pr : Primes X) (R : Ranks) where
  β : ℕ → Type
  [finβ : ∀ j, Fintype (β j)]
  [decβ : ∀ j, DecidableEq (β j)]
  lev : ∀ j, β j → LevFam X.E X.K (R.N j) Pr.vGs

attribute [instance] LevCh.finβ LevCh.decβ

def LevCh.one {X : Fields} {Pr : Primes X} {R : Ranks} (Λ : ∀ j, LevFam X.E X.K (R.N j) Pr.vGs) : LevCh X Pr R where
  β _ := Unit
  lev j _ := Λ j

section Step

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Λ : LevCh X Pr R)

@[reducible] def stepF (u : Pr.Word) (j : ℕ) : GFam X.K where
  β := Λ.β j
  V := (colVal W u j (Pr.vT u) Pr.vGs).V
  ιV := VVIdx (colVal W u j (Pr.vT u) Pr.vGs).lam
  bV := (colVal W u j (Pr.vT u) Pr.vGs).bV
  pair := (colVal W u j (Pr.vT u) Pr.vGs).pair
  G b := FormG (Λ.lev j b)
  D _ := DecoSet X.E (R.N j) (Pr.vT u) Pr.vGs
  actD b := formAct (Λ.lev j b)
  ρ b := formRho (colVal W u j (Pr.vT u) Pr.vGs) (Λ.lev j b)
  Nab _ := (colVal W u j (Pr.vT u) Pr.vGs).Nab
  Del _ := (colVal W u j (Pr.vT u) Pr.vGs).Del

theorem stepF_mem (u : Pr.Word) (j : ℕ) (b : Λ.β j) :
    (stepF W Λ u j).mem b = formGSD (colVal W u j (Pr.vT u) Pr.vGs) (Λ.lev j b) := rfl

theorem stepFOk (hX : X.Ok) (u : Pr.Word) (j : ℕ) : (stepF W Λ u j).Ok :=
  fun _ => formGSD_ok _ _ hX (colVal_eqv W hX u j _ _)

abbrev StClC (u : Pr.Word) (j : ℕ) : Type := (stepF W Λ u j).Cl

variable {W Λ} in

def repC {u : Pr.Word} {j : ℕ} (c : StClC W Λ u j) : DecoSet X.E (R.N j) (Pr.vT u) Pr.vGs :=
  ((stepF W Λ u j).mem c.1).outSec.rep c.2

open Classical in

def recDGamC (hX : X.Ok) : ℕ :=
  Finset.univ.lcm fun u : Pr.Word => (Finset.range (R.m + 1)).lcm fun j => famLcm (stepF W Λ u j) (stepFOk W Λ hX u j)

theorem recDGamC_dvd (hX : X.Ok) (u : Pr.Word) (j : ℕ) (hj : j ≤ R.m) (c : StClC W Λ u j) :
    Nat.card (FamStab (stepF W Λ u j) c) ∣ recDGamC W Λ hX := by
  classical
  refine Dvd.dvd.trans ?_ (Finset.dvd_lcm (Finset.mem_univ u))
  refine Dvd.dvd.trans ?_ (Finset.dvd_lcm (Finset.mem_range.2 (Nat.lt_succ_of_le hj)))
  exact famLcm_dvd _ _ c

theorem recDGamC_pos (hX : X.Ok) : 0 < recDGamC W Λ hX := by
  classical
  refine Nat.pos_of_ne_zero ?_
  unfold recDGamC
  rw [Ne, Finset.lcm_eq_zero_iff]
  rintro ⟨u, -, h⟩
  rw [Finset.lcm_eq_zero_iff] at h
  obtain ⟨j, -, h⟩ := h
  exact (famLcm_pos _ _).ne' h

@[irreducible] def recDGamAllC (Λ : LevCh X Pr R) {σ₀ : X.K →+* ℂ} (hX : X.Ok) (G : ChainGlob W σ₀) : ℕ := dGamAut X R

theorem recDGamAllC_eq {σ₀ : X.K →+* ℂ} (hX : X.Ok) (G : ChainGlob W σ₀) : recDGamAllC W Λ hX G = dGamAut X R := by
  unfold recDGamAllC
  rfl

theorem recDGamAllC_pos {σ₀ : X.K →+* ℂ} (hX : X.Ok) (G : ChainGlob W σ₀) : 0 < recDGamAllC W Λ hX G := by
  rw [recDGamAllC_eq]
  exact dGamAut_pos hX

theorem recDGamAllC_dvd {σ₀ : X.K →+* ℂ} (hX : X.Ok) (G : ChainGlob W σ₀) (u : Pr.Word) (j : ℕ) (hj : j ≤ R.m)
    (c : StClC W Λ u j) : Nat.card (FamStab (stepF W Λ u j) c) ∣ recDGamAllC W Λ hX G := by
  rw [recDGamAllC_eq]
  exact formGSD_stab_dvd_dGamAut hX (dga_N_mono R hj) (colVal W u j (Pr.vT u) Pr.vGs) (Λ.lev j c.1) (repC c)

end Step

section RhoPt

variable {X : Fields} {Pr : Primes X} {R : Ranks}

open Classical in

def rhoPt (Dc : DetChr X R.m) {u : Pr.Word} (i : ℕ) (p : DecoSet X.E (R.N i) (Pr.vT u) Pr.vGs) : X.Kˣ :=
  if hc : Formalism.BasicNotions.CMData X.F X.E then
    letI : NeZero (R.N i) := ⟨(R.N_pos i).ne'⟩
    (Formalism.L2.DIV.detTw hc.sig (Dc.muAt i) (ptOf hc (R.N i) (Pr.vT u) Pr.vGs p : GL (Fin (R.N i)) (X.E ⊗[X.F] Formalism.L2.Herm.Af X.F)))⁻¹ *
      (Formalism.L2.DIV.detTw hc.sig Dc.chi (ptOf hc (R.N i) (Pr.vT u) Pr.vGs p : GL (Fin (R.N i)) (X.E ⊗[X.F] Formalism.L2.Herm.Af X.F))) ^
        (-((R.N (i + 1) / 2 : ℕ) : ℤ))
  else 1

open Classical in

def rhoPt' (Dc : DetChr X R.m) {u : Pr.Word} (i : ℕ) (p : DecoSet X.E (R.N (i + 1)) (Pr.vT u) Pr.vGs) : X.Kˣ :=
  if hc : Formalism.BasicNotions.CMData X.F X.E then
    letI : NeZero (R.N (i + 1)) := ⟨(R.N_pos (i + 1)).ne'⟩
    Formalism.L2.DIV.detTw hc.sig (Dc.muAt i)
              (ptOf hc (R.N (i + 1)) (Pr.vT u) Pr.vGs p : GL (Fin (R.N (i + 1))) (X.E ⊗[X.F] Formalism.L2.Herm.Af X.F)) *
      (Formalism.L2.DIV.detTw hc.sig Dc.chi
        (ptOf hc (R.N (i + 1)) (Pr.vT u) Pr.vGs p : GL (Fin (R.N (i + 1))) (X.E ⊗[X.F] Formalism.L2.Herm.Af X.F))) ^ (((R.N i / 2 : ℕ) : ℤ))
  else 1

theorem rhoPt_norm {W : Wts X Pr.Word R} {σ₀ : X.K →+* ℂ} (G : ChainGlob W σ₀) {u : Pr.Word} (i : ℕ)
    (p : DecoSet X.E (R.N i) (Pr.vT u) Pr.vGs) : ‖σ₀ (rhoPt G.chr i p : X.K)‖ = 1 := by
  unfold rhoPt
  split_ifs with hc
  · exact (rec_norm_units σ₀ (rec_norm_detTw σ₀ (G.chr.muAt_unit G.chr_unit i) _ _) (rec_norm_detTw σ₀ G.chr_unit.2 _ _) _).1
  · simp

theorem rhoPt'_norm {W : Wts X Pr.Word R} {σ₀ : X.K →+* ℂ} (G : ChainGlob W σ₀) {u : Pr.Word} (i : ℕ)
    (p : DecoSet X.E (R.N (i + 1)) (Pr.vT u) Pr.vGs) : ‖σ₀ (rhoPt' G.chr i p : X.K)‖ = 1 := by
  unfold rhoPt'
  split_ifs with hc
  · exact (rec_norm_units σ₀ (rec_norm_detTw σ₀ (G.chr.muAt_unit G.chr_unit i) _ _) (rec_norm_detTw σ₀ G.chr_unit.2 _ _) _).2
  · simp

end RhoPt

section Chain

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Λ : LevCh X Pr R)

structure ChainArgC {σ₀ : X.K →+* ℂ} (G : ChainGlob W σ₀) (u : Pr.Word) where
  kk : ∀ i, GFam.Mat (stepF W Λ u i) (stepF W Λ u (i + 1))
  unf : ∀ i, StClC W Λ u i → StClC W Λ u (i + 1) → ((FrS X σ₀ (R.N i) → ℂ) →ₗ[ℂ] (FrS X σ₀ (R.N (i + 1)) → ℂ))
  unf_ev : ∀ i (c : StClC W Λ u i) (c' : StClC W Λ u (i + 1)) (x : VV X.K (W.lamTrue u i)),
    mulFun (fun y' => (dePow σ₀ (R.N (i + 1)) (sDivC W u i) y')⁻¹)
        (unf i c c' (mulFun (dePow σ₀ (R.N i) (sSharpC W u i)) (evV X.emb 1 (W.lamTrue u i) σ₀ x))) =
      (σ₀ (rhoPt G.chr i (repC c) : X.K) * σ₀ (rhoPt' G.chr i (repC c') : X.K))⁻¹ •
        evV X.emb 1 (W.lamTrue u (i + 1)) σ₀ ((kk i c.1 c'.1).k (repC c) (repC c') x)

variable {W Λ}

def ChainArgC.toF {σ₀ : X.K →+* ℂ} {G : ChainGlob W σ₀} {u : Pr.Word} (A : ChainArgC W Λ G u) : ChainArgF R (stepF W Λ u) σ₀ where
  rhoDet i c := σ₀ (rhoPt G.chr i (repC c) : X.K)
  rhoDet' i c := σ₀ (rhoPt' G.chr i (repC c) : X.K)
  rho_norm i _ c := rhoPt_norm G i (repC c)
  rho'_norm i _ c := rhoPt'_norm G i (repC c)
  unf := A.unf

def recChainC (hX : X.Ok) (σ₀ : X.K →+* ℂ) (G : ChainGlob W σ₀) (u : Pr.Word) (A : ChainArgC W Λ G u) : ColumnChain R X.Tau (W.hc u) :=
  recChainF (W.hc u) (stepF W Λ u) (stepFOk W Λ hX u) σ₀ (recDGamAllC W Λ hX G) (recDGamAllC_pos W Λ hX G)
    (fun j hj c => recDGamAllC_dvd W Λ hX G u j hj c) A.toF

theorem recChainC_Kmap (hX : X.Ok) (σ₀ : X.K →+* ℂ) (G : ChainGlob W σ₀) (u : Pr.Word) (A : ChainArgC W Λ G u) (i : ℕ)
    (c : StClC W Λ u i) (c' : StClC W Λ u (i + 1)) (x : VV X.K (W.lamTrue u i)) :
    (recChainC hX σ₀ G u A).Kmap i c c' (evV X.emb 1 (W.lamTrue u i) σ₀ x) =
      evV X.emb 1 (W.lamTrue u (i + 1)) σ₀ ((A.kk i c.1 c'.1).k (repC c) (repC c') x) := by
  set r := σ₀ (rhoPt G.chr i (repC c) : X.K) with hr
  set r' := σ₀ (rhoPt' G.chr i (repC c') : X.K) with hr'
  have h0 : r * r' ≠ 0 := by
    refine mul_ne_zero ?_ ?_
    · intro h; have := rhoPt_norm G i (repC c); rw [← hr, h, norm_zero] at this; exact zero_ne_one this
    · intro h; have := rhoPt'_norm G i (repC c'); rw [← hr', h, norm_zero] at this; exact zero_ne_one this
  funext (y' : FrS X σ₀ (R.N (i + 1)))
  refine (congrArg (fun z : ℂ => (r * r') * z) (congrFun (A.unf_ev i c c' x) y')).trans ?_
  show (r * r') * ((r * r')⁻¹ * _) = _
  rw [← mul_assoc, mul_inv_cancel₀ h0, one_mul]

end Chain

section Xi

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Λ : LevCh X Pr R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (Am : Amb X) (u : Pr.Word)

abbrev XiFamC (Λ : LevCh X Pr R) (u : Pr.Word) : Type :=
  ∀ i, Λ.β i → Λ.β (i + 1) → DecoSet X.E (R.N i) (Pr.vT u) Pr.vGs → DecoSet X.E (R.N (i + 1)) (Pr.vT u) Pr.vGs →
    HomE X.E (R.N i) (R.N (i + 1)) → X.K

variable (Ξ : XiFamC Λ u)

def xiKerC (i : ℕ) (b : Λ.β i) (b' : Λ.β (i + 1)) (p : DecoSet X.E (R.N i) (Pr.vT u) Pr.vGs) (p' : DecoSet X.E (R.N (i + 1)) (Pr.vT u) Pr.vGs) :
    VV X.K (W.lamTrue u i) →ₗ[X.K] VV X.K (W.lamTrue u (i + 1)) :=
  kerOf (stepC W Ch sel mu cst Am u i (W.lamTrue u (i + 1))) (Sall sel mu u) (cAof sel mu cst) (cBof sel mu cst u)
    p.1.N (frsD sel mu p) p'.1.N (frsD sel mu p') (Ξ i b b' p p')

def XiEquivC : Prop :=
  ∀ i (b : Λ.β i) (b' : Λ.β (i + 1)),
    ClsEq (S := (stepF W Λ u i).mem b) (S' := (stepF W Λ u (i + 1)).mem b') (xiKerC W Λ Ch sel mu cst Am u Ξ i b b')

variable {W Λ Ch sel mu cst Am u Ξ} in

def xiKKC (h : XiEquivC W Λ Ch sel mu cst Am u Ξ) : ∀ i, GFam.Mat (stepF W Λ u i) (stepF W Λ u (i + 1)) :=
  fun i b b' => ⟨xiKerC W Λ Ch sel mu cst Am u Ξ i b b', h i b b'⟩

def xiThC (i : ℕ) (c : StClC W Λ u i) (c' : StClC W Λ u (i + 1)) : VCx X.Tau (R.N i) (R.N (i + 1)) → ℂ :=
  Am.thDat (Sall sel mu u) (cAof sel mu cst) (cBof sel mu cst u) (repC c).1.N (repC c').1.N (Ξ i c.1 c'.1 (repC c) (repC c'))

def RhoScalC {σ₀ : X.K →+* ℂ} (G : ChainGlob W σ₀) : Prop :=
  ∀ i, i < R.m → ∀ (c : StClC W Λ u i) (c' : StClC W Λ u (i + 1)),
    σ₀ (rhoPt G.chr i (repC c) : X.K) * σ₀ (rhoPt' G.chr i (repC c') : X.K) * Am.chiF (R.N i) (R.N (i + 1)) (repC c).1.N (repC c').1.N =
      σ₀ (scalK Ch sel mu cst i (repC c).1.N (frsD sel mu (repC c)) (repC c').1.N (frsD sel mu (repC c')))

structure XiHypC {σ₀ : X.K →+* ℂ} (G : ChainGlob W σ₀) : Prop where
  sig : Am.σ₀ = σ₀
  T_pos : 0 < Pr.T u
  smooth : ∀ i, i < R.m → Am.ESmooth (R.N i) (R.N (i + 1))
  rat : ∀ i, i < R.m → Am.JetsRat (R.N i) (R.N (i + 1)) (Sall sel mu u) (cAof sel mu cst * cBof sel mu cst u)
  chi_ne : ∀ i, i < R.m → ∀ (c : StClC W Λ u i) (c' : StClC W Λ u (i + 1)), Am.chiF (R.N i) (R.N (i + 1)) (repC c).1.N (repC c').1.N ≠ 0
  rho : RhoScalC W Λ Ch sel mu cst Am u G
  above : ∀ i, R.m ≤ i → ∀ b b' p p' x, Ξ i b b' p p' x = 0

variable {W Λ Ch sel mu cst Am u Ξ}

def ChainArgC.ofXi {σ₀ : X.K →+* ℂ} {G : ChainGlob W σ₀} (hE : XiEquivC W Λ Ch sel mu cst Am u Ξ) (H : XiHypC W Λ Ch sel mu cst Am u Ξ G) :
    ChainArgC W Λ G u where
  kk := xiKKC hE
  unf i c c' := unfTh σ₀ Am.cD (xiThC W Λ sel mu cst Am u Ξ i c c')
  unf_ev i c c' x := by
    by_cases hi : i < R.m
    · have hp := (repC c).2
      have hp' := (repC c').2
      have h := unfTh_stepC W Ch sel mu cst Am σ₀ H.sig u H.T_pos hi (jet_in_weight_space_chain W u hi) (H.smooth i hi) (H.rat i hi)
        (repC c).1.N (frsD sel mu (repC c)) (repC c').1.N (frsD sel mu (repC c')) ⟨hp.lat, hp.uni⟩ ⟨hp'.lat, hp'.uni⟩
        (Ξ i c.1 c'.1 (repC c) (repC c')) x
      have hr := H.rho i hi c c'
      have hx := H.chi_ne i hi c c'
      set r := σ₀ (rhoPt G.chr i (repC c) : X.K) * σ₀ (rhoPt' G.chr i (repC c') : X.K) with hrdef
      have h0 : r ≠ 0 := by
        refine mul_ne_zero ?_ ?_
        · intro h; have := rhoPt_norm G i (repC c); rw [h, norm_zero] at this; exact zero_ne_one this
        · intro h; have := rhoPt'_norm G i (repC c'); rw [h, norm_zero] at this; exact zero_ne_one this
      have hs : σ₀ (scalK Ch sel mu cst i (repC c).1.N (frsD sel mu (repC c)) (repC c').1.N (frsD sel mu (repC c'))) *
          (Am.chiF (R.N i) (R.N (i + 1)) (repC c).1.N (repC c').1.N)⁻¹ = r := by
        rw [← hr, mul_assoc, mul_inv_cancel₀ hx, mul_one]
      rw [hs] at h
      funext (y' : FrS X σ₀ (R.N (i + 1)))
      have hy := congrFun h y'
      refine Eq.trans ?_ (congrArg (fun z : ℂ => r⁻¹ * z) hy).symm
      show _ = r⁻¹ * (r * _)
      rw [← mul_assoc, inv_mul_cancel₀ h0, one_mul]
      rfl
    · have hi' : R.m ≤ i := Nat.le_of_not_lt hi
      have hk : (xiKKC hE i c.1 c'.1).k (repC c) (repC c') = 0 := kerOf_zero _ _ _ _ _ _ _ _ _ (H.above i hi' _ _ _ _)
      have ht : xiThC W Λ sel mu cst Am u Ξ i c c' = fun _ => 0 := thDat_zero Am _ _ _ _ _ _ (H.above i hi' _ _ _ _)
      rw [hk, ht, unfTh_zero, LinearMap.zero_apply, map_zero]
      have h0 : evV X.emb 1 (W.lamTrue u (i + 1)) σ₀ ((0 : VV X.K (W.lamTrue u i) →ₗ[X.K] VV X.K (W.lamTrue u (i + 1))) x) = 0 := by
        rw [LinearMap.zero_apply, map_zero]
      exact ((congrArg (fun f : FrS X σ₀ (R.N (i + 1)) → ℂ =>
        (σ₀ (rhoPt G.chr i (repC c) : X.K) * σ₀ (rhoPt' G.chr i (repC c') : X.K))⁻¹ • f) h0).trans (smul_zero _)).symm

theorem recChainC_unf_pol (hX : X.Ok) {σ₀ : X.K →+* ℂ} {G : ChainGlob W σ₀} (hE : XiEquivC W Λ Ch sel mu cst Am u Ξ)
    (H : XiHypC W Λ Ch sel mu cst Am u Ξ G) (i : ℕ) (c : StClC W Λ u i) (c' : StClC W Λ u (i + 1)) (Q : Pol ℂ X.Tau (R.N i)) :
    (recChainC hX σ₀ G u (ChainArgC.ofXi hE H)).unf i c c' (polFn σ₀ (R.N i) Q) =
      polFn σ₀ (R.N (i + 1)) (jetMap (ι := X.Tau) (jetC Am.cD (xiThC W Λ sel mu cst Am u Ξ i c c')) (fun _ => 0) Q) :=
  unfTh_polFn σ₀ Am.cD _ Q

end Xi

end Formalism.L2.Col
