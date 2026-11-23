import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadsHecke
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLevelGroupWithCharacterAtTypePlaces
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlaceHeckeOperatorScalarOnSpherical
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

noncomputable section

namespace GlobalTheory.LevParaLoc

theorem locM_eq_one_of_ne {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} (s s' : SplitPlace L)
    {κ : GAf L n} (hκ : TrivOutside {s.v} κ) (h : s'.v ≠ s.v) : NX.locM s' κ = 1 :=
  GlobalTheory.LevGChar.locM_triv s' (B := {s.v}ᶜ) (by rwa [compl_compl]) (by simpa using h)

theorem intLift_one {L : Type} [Field L] [NumberField L] [IsCMField L]
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) : NX.intLift v 1 = 1 := by
  unfold NX.intLift
  rw [dif_pos (v.adicCompletionIntegers (maximalRealSubfield L)).one_mem]
  rfl

theorem intLift_zero {L : Type} [Field L] [NumberField L] [IsCMField L]
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) : NX.intLift v 0 = 0 := by
  unfold NX.intLift
  rw [dif_pos (v.adicCompletionIntegers (maximalRealSubfield L)).zero_mem]
  rfl

end GlobalTheory.LevParaLoc

namespace GlobalTheory.LevParaLoc

theorem redMat_one {L : Type} [Field L] [NumberField L] [IsCMField L] {r : ℕ}
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) {R : Type} [CommRing R]
    (red : v.adicCompletionIntegers (maximalRealSubfield L) →+* R) :
    NX.redMat v red (1 : Matrix (Fin r) (Fin r) (v.adicCompletion (maximalRealSubfield L))) = 1 := by
  refine Matrix.ext fun a b => ?_
  show red (NX.intLift v ((1 : Matrix (Fin r) (Fin r) _) a b)) = (1 : Matrix (Fin r) (Fin r) R) a b
  by_cases hab : a = b
  · subst hab; rw [Matrix.one_apply_eq, Matrix.one_apply_eq, intLift_one, map_one]
  · rw [Matrix.one_apply_ne hab, Matrix.one_apply_ne hab, intLift_zero, map_zero]

open Classical in
theorem gVal_one (D : D7) (i : D.ntw.Tw) (k : ℕ) (b : Bool) (kv : Σ k : Fin 2, D.nd.PlG k) (s : SplitPlace D.host.E)
    (red : s.v.adicCompletionIntegers (maximalRealSubfield D.host.E) →+* ZMod (D.host.g kv.1))
    (τ : (ZMod (D.host.g kv.1))ˣ →* (FractionRing (D.ntw.O i))ˣ) :
    NX.gVal D i k b kv s red τ 1 = 1 := by
  have htop : NX.topR (Nat.le_add_right D.R.r D.R.t : D.R.r ≤ D.R.nV)
      (1 : Matrix (Fin D.R.nV) (Fin D.R.nV) (s.v.adicCompletion (maximalRealSubfield D.host.E))) = 1 :=
    Matrix.submatrix_one _ (Fin.castLE_injective _)
  have hgl : NX.glOf (1 : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1))) = 1 :=
    Units.ext (NX.glOf_val _ (by simp))
  have hpsi : NX.psiUTot D i b 1 = 1 := by
    unfold NX.psiUTot
    rw [dif_pos (one_mem _)]
    have e : (⟨1, one_mem _⟩ : D.nexp.U) = 1 := rfl
    rw [e, map_one, Units.val_one]
  have hd : red (NX.intLift s.v (NX.detT D.R.r
      (1 : Matrix (Fin D.R.nV) (Fin D.R.nV) (s.v.adicCompletion (maximalRealSubfield D.host.E))))) = 1 := by
    rw [GlobalTheory.LevGChar.detT_one', intLift_one, map_one]
  unfold NX.gVal
  rw [htop, redMat_one, hgl, Pi.mulSingle_one, hpsi, map_one, one_mul]
  split_ifs with h
  · have hu : h.unit = 1 := Units.ext (by rw [IsUnit.unit_spec, hd]; rfl)
    rw [hu, map_one, Units.val_one, map_one]
  · exact absurd (hd ▸ isUnit_one) h

theorem resRep_one {L : Type} [Field L] [NumberField L] [IsCMField L] (s : SplitPlace L) :
    NX.resRep s s.w 1 - 1 ∈ s.w.asIdeal := by
  have hu := GlobalTheory.LevGChar.i_resRep s 1 (map_one _)
  show Valued.v (s.i (((NX.resRep s s.w 1 - 1 : 𝓞 L)) : L)) < 1
  have e : s.i (((NX.resRep s s.w 1 - 1 : 𝓞 L)) : L) = s.i ((NX.resRep s s.w 1 : 𝓞 L) : L) - 1 := by
    push_cast; rw [map_sub, map_one]
  rw [e]
  exact hu

end GlobalTheory.LevParaLoc

namespace GlobalTheory.LevParaLoc

theorem mem_iff (D : D7) (i : D.ntw.Tw) (j : ℕ) (b : Bool) (k : ℕ) (Q : Finset (PlE D.host))
    (ψ : G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ) (e₀ : ℤ) (W₀ : Type) [AddCommGroup W₀]
    [Module (FractionRing (D.ntw.O i)) W₀]
    (ρ₀ : Representation (FractionRing (D.ntw.O i)) (ReciprocityTheory.Aut.GQ D.host.E D.R.nV) W₀)
    (τ : ∀ kv : (Σ kk : Fin 2, D.nd.PlG kk), (ZMod (D.host.g kv.1))ˣ →* (FractionRing (D.ntw.O i))ˣ)
    (M : NX.MtVReal D i j b k Q ψ e₀ W₀ ρ₀ τ) (P : PlE D.host)
    (hP : P ∈ M.QP ∨ P ∈ M.DP) (hG : ∀ kv, (M.sp (NX.pG D kv)).v ≠ (M.sp P).v)
    (hQ : ∀ P'' ∈ M.QP, (M.sp P'').v = (M.sp P).v → P'' = P)
    (hD : ∀ P'' ∈ M.DP, (M.sp P'').v = (M.sp P).v → P'' = P)
    (κ : GAf D.host.E D.R.nV) (hκ : TrivOutside {(M.sp P).v} κ) :
    κ ∈ M.J ↔ NG.ParaRT (M.sp P) D.R.r ((M.sp P).loc _ κ) := by
  have hpar : ((∀ P'' ∈ M.QP, NX.InParah (M.sp P'').v D.R.r (NX.locM (M.sp P'') κ)) ∧
      (∀ P'' ∈ M.DP, NX.InParah (M.sp P'').v D.R.r (NX.locM (M.sp P'') κ))) ↔
      NX.InParah (M.sp P).v D.R.r (NX.locM (M.sp P) κ) := by
    constructor
    · rintro ⟨h1, h2⟩
      rcases hP with h | h
      exacts [h1 P h, h2 P h]
    · intro h
      refine ⟨fun P'' hP'' => ?_, fun P'' hP'' => ?_⟩
      · by_cases hv : (M.sp P'').v = (M.sp P).v
        · rw [hQ P'' hP'' hv]; exact h
        · rw [locM_eq_one_of_ne _ _ hκ hv]; exact NX.inParah_one _ _
      · by_cases hv : (M.sp P'').v = (M.sp P).v
        · rw [hD P'' hP'' hv]; exact h
        · rw [locM_eq_one_of_ne _ _ hκ hv]; exact NX.inParah_one _ _
  have hg : ∀ kv, NX.InLevG (M.sp (NX.pG D kv)).v D.R.r (NX.locM (M.sp (NX.pG D kv)) κ) := fun kv => by
    rw [locM_eq_one_of_ne _ _ hκ (hG kv)]; exact NX.inLevG_one _ _
  rw [M.J_mem κ]
  constructor
  · rintro ⟨hU, -, h1, h2⟩
    exact ⟨(GlobalTheory.HeckeScalarSph.loc_mem_GLint_iff _ hκ).2 hU, (hpar.1 ⟨h1, h2⟩).2⟩
  · rintro ⟨hGL, hll⟩
    exact ⟨(GlobalTheory.HeckeScalarSph.loc_mem_GLint_iff _ hκ).1 hGL, hg,
      hpar.2 ⟨fun a b => (GlobalTheory.HeckeScalarSph.mem_GLint_iff.1 hGL).1 a b, hll⟩⟩

theorem levelPara_loc : ∀ (D : D7) (i : D.ntw.Tw) (j : ℕ) (b : Bool) (k : ℕ) (Q : Finset (PlE D.host)) (ψ : G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ) (e₀ : ℤ) (W₀ : Type) [AddCommGroup W₀] [Module (FractionRing (D.ntw.O i)) W₀] (ρ₀ : Representation (FractionRing (D.ntw.O i)) (ReciprocityTheory.Aut.GQ D.host.E D.R.nV) W₀) (τ : ∀ kv : (Σ kk : Fin 2, D.nd.PlG kk), (ZMod (D.host.g kv.1))ˣ →* (FractionRing (D.ntw.O i))ˣ) (M : NX.MtVReal D i j b k Q ψ e₀ W₀ ρ₀ τ) (ek : NX.Kk D i k →+* ℂ) (P : PlE D.host) (ξ : ((M.sp P).v.adicCompletion (maximalRealSubfield D.host.E))ˣ →* ℂˣ), (P ∈ M.QP ∨ P ∈ M.DP) → ¬ (P ∈ M.QP ∧ P ∈ M.DP) → (∀ kv, (M.sp (NX.pG D kv)).v ≠ (M.sp P).v) → (∀ P'' ∈ M.QP, (M.sp P'').v = (M.sp P).v → P'' = P) → (∀ P'' ∈ M.DP, (M.sp P'').v = (M.sp P).v → P'' = P) → (∀ P'' ∈ M.QP, ∀ u : 𝓞 D.host.E, u - 1 ∈ P''.asIdeal → NX.tameVal ψ P'' e₀ u = 1) → (∀ P'' ∈ M.DP, ∀ u : 𝓞 D.host.E, u - 1 ∈ P''.asIdeal → NX.tameVal (D.ntw.delta i) P'' (if b then e₀ else -e₀) u = 1) → (P ∈ M.QP → ∀ (y : ((M.sp P).v.adicCompletion (maximalRealSubfield D.host.E))ˣ) (a : 𝓞 D.host.E), a ∉ P.asIdeal → Valued.v (y : ((M.sp P).v.adicCompletion (maximalRealSubfield D.host.E))) = 1 → Valued.v ((y : ((M.sp P).v.adicCompletion (maximalRealSubfield D.host.E))) - (M.sp P).i (a : D.host.E)) < 1 → ((ξ y : ℂˣ) : ℂ) = ek (NX.ofOk D i k (NX.tameVal ψ P e₀ a).1)) → (P ∈ M.DP → ∀ (y : ((M.sp P).v.adicCompletion (maximalRealSubfield D.host.E))ˣ) (a : 𝓞 D.host.E), a ∉ P.asIdeal → Valued.v (y : ((M.sp P).v.adicCompletion (maximalRealSubfield D.host.E))) = 1 → Valued.v ((y : ((M.sp P).v.adicCompletion (maximalRealSubfield D.host.E))) - (M.sp P).i (a : D.host.E)) < 1 → ((ξ y : ℂˣ) : ℂ) = ek (NX.ofO0 D i k (NX.tameVal (D.ntw.delta i) P (if b then e₀ else -e₀) a).1)) → NG.LevelPara M.J (cx ek M.χ) (M.sp P) D.R.r ξ := by
  intro D i j b k Q ψ e₀ W₀ _ _ ρ₀ τ M ek P ξ hP hPn hG hQ hD hψ hδ hξQ hξD
  refine ⟨fun κ hκ => mem_iff D i j b k Q ψ e₀ W₀ ρ₀ τ M P hP hG hQ hD κ hκ, ?_⟩
  intro κ h hκ u hu
  have hpara := (mem_iff D i j b k Q ψ e₀ W₀ ρ₀ τ M P hP hG hQ hD κ hκ).1 h
  have hUm : κ ∈ Umax D.host.E D.R.nV := ((M.J_mem κ).1 h).1
  have hx : NX.InParah (M.sp P).v D.R.r (NX.locM (M.sp P) κ) :=
    ⟨fun a b => (GlobalTheory.HeckeScalarSph.mem_GLint_iff.1 hpara.1).1 a b, hpara.2⟩
  have hv1 : Valued.v (NX.detT D.R.r (NX.locM (M.sp P) κ)) = 1 :=
    GlobalTheory.LevGChar.i_detT_one _ D.R.r _ (NX.locM (M.sp P) κ⁻¹)
      (by rw [← GlobalTheory.LevGChar.locM_mul, mul_inv_cancel, GlobalTheory.LevGChar.locM_one])
      (fun a b => GlobalTheory.LevGChar.locM_int _ (inv_mem hUm) a b) hx
  have hu' : (u : (M.sp P).v.adicCompletion (maximalRealSubfield D.host.E)) =
      NX.detT D.R.r (NX.locM (M.sp P) κ) := hu
  have hw : (M.sp P).w = P := M.sp_w P (by rcases hP with h | h; exacts [Or.inl h, Or.inr (Or.inl h)])
  have hclose : Valued.v ((u : (M.sp P).v.adicCompletion (maximalRealSubfield D.host.E)) -
      (M.sp P).i ((NX.resRep (M.sp P) P (NX.detT D.R.r (NX.locM (M.sp P) κ)) : 𝓞 D.host.E) : D.host.E)) < 1 := by
    have := GlobalTheory.LevGChar.i_resRep (M.sp P) _ hv1
    rw [hw] at this
    rw [hu', ← Valuation.map_neg, neg_sub]
    exact this
  have hnm := GlobalTheory.LevGChar.resRep_not_mem (M.sp P) P (NX.detT D.R.r (NX.locM (M.sp P) κ))
  have hvu : Valued.v (u : (M.sp P).v.adicCompletion (maximalRealSubfield D.host.E)) = 1 := by rw [hu']; exact hv1
  have hGp : ∏ kv, NX.gVal D i k b kv (M.sp (NX.pG D kv)) (M.redG kv) (τ kv) (NX.locM (M.sp (NX.pG D kv)) κ) = 1 :=
    Finset.prod_eq_one fun kv _ => by rw [locM_eq_one_of_ne _ _ hκ (hG kv)]; exact gVal_one _ _ _ _ _ _ _ _
  have offQ : ∀ P'' ∈ M.QP, P'' ≠ P → NX.ofOk D i k (NX.tameVal ψ P'' e₀
      (NX.resRep (M.sp P'') P'' (NX.detT D.R.r (NX.locM (M.sp P'') κ)))).1 = 1 := by
    intro P'' hP'' hne
    have hv : (M.sp P'').v ≠ (M.sp P).v := fun e => hne (hQ P'' hP'' e)
    have hw'' : (M.sp P'').w = P'' := M.sp_w P'' (Or.inl hP'')
    rw [locM_eq_one_of_ne _ _ hκ hv, GlobalTheory.LevGChar.detT_one']
    have h1 := resRep_one (M.sp P'')
    rw [hw''] at h1
    rw [hψ P'' hP'' _ h1, Units.val_one, map_one]
  have offD : ∀ P'' ∈ M.DP, P'' ≠ P → NX.ofO0 D i k (NX.tameVal (D.ntw.delta i) P'' (if b then e₀ else -e₀)
      (NX.resRep (M.sp P'') P'' (NX.detT D.R.r (NX.locM (M.sp P'') κ)))).1 = 1 := by
    intro P'' hP'' hne
    have hv : (M.sp P'').v ≠ (M.sp P).v := fun e => hne (hD P'' hP'' e)
    have hw'' : (M.sp P'').w = P'' := M.sp_w P'' (Or.inr (Or.inl hP''))
    rw [locM_eq_one_of_ne _ _ hκ hv, GlobalTheory.LevGChar.detT_one']
    have h1 := resRep_one (M.sp P'')
    rw [hw''] at h1
    rw [hδ P'' hP'' _ h1, Units.val_one, map_one]
  apply Units.ext
  rw [cx_apply, M.chi_eq κ h, hGp, one_mul]
  rcases hP with hPQ | hPD
  · have hPD : P ∉ M.DP := fun h' => hPn ⟨hPQ, h'⟩
    rw [Finset.prod_eq_single_of_mem P hPQ offQ,
      Finset.prod_eq_one (fun P'' hP'' => offD P'' hP'' (fun e => hPD (e ▸ hP''))), mul_one]
    exact (hξQ hPQ u _ hnm hvu hclose).symm
  · have hPQ : P ∉ M.QP := fun h' => hPn ⟨h', hPD⟩
    rw [Finset.prod_eq_single_of_mem P hPD offD,
      Finset.prod_eq_one (fun P'' hP'' => offQ P'' hP'' (fun e => hPQ (e ▸ hP''))), one_mul]
    exact (hξD hPD u _ hnm hvu hclose).symm

end GlobalTheory.LevParaLoc
