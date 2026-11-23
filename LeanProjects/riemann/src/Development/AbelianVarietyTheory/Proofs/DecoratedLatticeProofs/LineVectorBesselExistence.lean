import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Framed
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RatioOKOfRootOfUnity
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSBesUnscaledDual
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StarSmulVec
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnfoldingLevelsAndStepsHaarMeasuresExist
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DetNeZeroOfHasSignature
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsThetaLiftSpacesPositiveIndexWithLineNormsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GramEqOfInst
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option genSizeOfSpec false
set_option genInjectivity false

noncomputable section

namespace GlobalTheory.Fam.RatDec

variable {D : D7}

theorem quad_mulVec {m n : ℕ} (A : Matrix (Fin m) (Fin n) D.host.E) (G : Matrix (Fin m) (Fin m) D.host.E)
    (v : Fin n → D.host.E) : star (A *ᵥ v) ⬝ᵥ G *ᵥ (A *ᵥ v) = star v ⬝ᵥ (Aᴴ * G * A) *ᵥ v := by
  rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, Matrix.mul_assoc]

theorem conj_mul_mul {S S' : HSp D} {a b : ℕ} (P : Matrix (Fin S'.rank) (Fin S.rank) D.host.E)
    (A : Matrix (Fin S.rank) (Fin a) D.host.E) (B : Matrix (Fin S.rank) (Fin b) D.host.E) :
    (P * A)ᴴ * S'.gram * (P * B) = Aᴴ * (Pᴴ * S'.gram * P) * B := by
  simp only [conjTranspose_mul, Matrix.mul_assoc]

def pullDec {S S' S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (P : Matrix (Fin S'.rank) (Fin S.rank) D.host.E)
    (hP : Pᴴ * S'.gram * P = S.gram) (hr : S.rank = S'.rank) : HypDec S' S₀ ρ where
  e := P * d.e
  e' := P * d.e'
  i₀ := P * d.i₀
  ee := by rw [conj_mul_mul, hP, d.ee]
  e'e' := by rw [conj_mul_mul, hP, d.e'e']
  e'e := by rw [conj_mul_mul, hP, d.e'e]
  iso := by rw [conj_mul_mul, hP, d.iso]
  i₀e := by rw [conj_mul_mul, hP, d.i₀e]
  i₀e' := by rw [conj_mul_mul, hP, d.i₀e']
  rank_add := d.rank_add.trans hr

theorem mat_of_isom (W₁ W₂ : HSp D) (φ : W₁.V ≃ₗ[D.host.E] W₂.V) (hφ : ∀ x y, W₂.hT (φ x) (φ y) = W₁.hT x y) :
    ∃ P : Matrix (Fin W₂.rank) (Fin W₁.rank) D.host.E, Pᴴ * W₂.gram * P = W₁.gram := by
  refine ⟨Matrix.of fun k j => W₂.frame.equivFun (φ (W₁.frame j)) k, ?_⟩
  ext i j
  have h := GlobalTheory.LandherrSignature.form_eq W₂.hT W₂.frame (W₂.frame.equivFun (φ (W₁.frame i)))
    (W₂.frame.equivFun (φ (W₁.frame j)))
  simp only [LinearEquiv.symm_apply_apply] at h
  rw [hφ] at h
  have hG : (Matrix.of fun a b => W₂.hT (W₂.frame a) (W₂.frame b)) = W₂.gram := rfl
  rw [hG] at h
  rw [show W₁.gram i j = W₁.hT (W₁.frame i) (W₁.frame j) from rfl, h]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, dotProduct, mulVec, Matrix.of_apply, Pi.star_apply,
    Finset.sum_mul, Finset.mul_sum]
  simp_rw [mul_assoc]
  first | exact Finset.sum_comm | (congr 1; exact Finset.sum_comm)

theorem yc_facts (j : ℕ) (hj : j ≤ D.R.m) :
    (Yc D j).SigOK ∧ (Yc D j).rank = D.R.rankY j ∧ ∀ τ, (Yc D j).sig τ = sigYD D.R j := by
  have hmin : min j D.R.m = j := min_eq_left hj
  refine ⟨D.sp.Y_sig _, ?_, fun τ => ?_⟩
  · show (D.sp.Y (min j D.R.m)).rank = _
    rw [hmin]; exact D.sp.Y_rank j hj
  · show (D.sp.Y (min j D.R.m)).sig τ = _
    rw [hmin]; exact D.Y_sigval j hj τ

theorem bes_to_Yc (j ρ : ℕ) (hj : j ≤ D.R.m) {V : HSp D} (b : BesAt V (D.sp.X j) ρ) (hr : V.rank = D.R.rankY j)
    (hs : V.SigOK) (hsig : ∀ τ, V.sig τ = sigYD D.R j) :
    ∃ b' : BesAt (Yc D j) (D.sp.X j) ρ, star b'.ζ ⬝ᵥ b'.L.gram *ᵥ b'.ζ = star b.ζ ⬝ᵥ b.L.gram *ᵥ b.ζ := by
  obtain ⟨hYs, hYr, hYsig⟩ := yc_facts (D := D) j hj
  obtain ⟨φ, hφ⟩ := GlobalTheory.LandherrSignature.exists_isometry_host D V (Yc D j) hs hYs (hr.trans hYr.symm)
    (fun τ => (hsig τ).trans (hYsig τ).symm)
  obtain ⟨P, hP⟩ := mat_of_isom V (Yc D j) φ hφ
  exact ⟨⟨b.V₀, b.L, pullDec b.d P hP (hr.trans hYr.symm), b.o, b.ζ, b.line, b.cpt,
    ((GlobalTheory.Unf.VolExist.measures_exist D).2.1 _ _ _ _).some⟩, rfl⟩

theorem jac_to_Yc (j ρ : ℕ) (hj : j ≤ D.R.m) {V : HSp D} (b : JacAt V (D.sp.X j) ρ) (hr : V.rank = D.R.rankY j)
    (hs : V.SigOK) (hsig : ∀ τ, V.sig τ = sigYD D.R j) : Nonempty (JacAt (Yc D j) (D.sp.X j) ρ) := by
  obtain ⟨hYs, hYr, hYsig⟩ := yc_facts (D := D) j hj
  obtain ⟨φ, hφ⟩ := GlobalTheory.LandherrSignature.exists_isometry_host D V (Yc D j) hs hYs (hr.trans hYr.symm)
    (fun τ => (hsig τ).trans (hYsig τ).symm)
  obtain ⟨P, hP⟩ := mat_of_isom V (Yc D j) φ hφ
  exact ⟨⟨pullDec b.d P hP (hr.trans hYr.symm), b.cpt, ((GlobalTheory.Unf.VolExist.measures_exist D).2.1 _ _ _ _).some⟩⟩

def besOf {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D} {u : D.what₂.Word}
    {ψ : AddChar (AF D.host.F) ℂ} (B : GlobalTheory.Core.Mi.SBes X h u ψ (D.sp.X 0)) : BesAt (D.sp.Y 0) (D.sp.X 0) D.R.rS :=
  ⟨B.V₀, B.L, B.d, B.o, B.ζ, B.line, B.cpt, B.vN⟩

def besF (b0 : BesAt (D.sp.Y 0) (D.sp.X 0) D.R.rS)
    (b' : ∀ j ρ, j + 2 * ρ + 2 = D.R.m → BesAt (Yc D j) (D.sp.X j) ρ) :
    ∀ j ρ, j + 2 * ρ + 2 = D.R.m → BesAt (Yc D j) (D.sp.X j) ρ
  | 0, ρ, h => cast (congrArg (BesAt (Yc D 0) (D.sp.X 0)) (show D.R.m / 2 - 1 = ρ by omega)) b0
  | j + 1, ρ, h => b' (j + 1) ρ h

theorem besF_zero (b0 : BesAt (D.sp.Y 0) (D.sp.X 0) D.R.rS)
    (b' : ∀ j ρ, j + 2 * ρ + 2 = D.R.m → BesAt (Yc D j) (D.sp.X j) ρ) (h0 : 0 + 2 * D.R.rS + 2 = D.R.m) :
    besF b0 b' 0 D.R.rS h0 = b0 := rfl

theorem besF_norm (b0 : BesAt (D.sp.Y 0) (D.sp.X 0) D.R.rS)
    (b' : ∀ j ρ, j + 2 * ρ + 2 = D.R.m → BesAt (Yc D j) (D.sp.X j) ρ) (c N : D.host.E)
    (h0 : star b0.ζ ⬝ᵥ b0.L.gram *ᵥ b0.ζ = c)
    (h' : ∀ j ρ h, star (b' j ρ h).ζ ⬝ᵥ (b' j ρ h).L.gram *ᵥ (b' j ρ h).ζ * N ^ (j / 2) = c) :
    ∀ j ρ h, star (besF b0 b' j ρ h).ζ ⬝ᵥ (besF b0 b' j ρ h).L.gram *ᵥ (besF b0 b' j ρ h).ζ * N ^ (j / 2) = c
  | 0, ρ, h => by
    obtain rfl : D.R.rS = ρ := by show D.R.m / 2 - 1 = ρ; omega
    rw [besF_zero b0 b' h, Nat.zero_div, pow_zero, mul_one]
    exact h0
  | j + 1, ρ, h => h' (j + 1) ρ h

theorem sbes_norm {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D} {u : D.what₂.Word}
    {ψ : AddChar (AF D.host.F) ℂ} (B : GlobalTheory.Core.Mi.SBes X h u ψ (D.sp.X 0)) (hE : GlobalTheory.Core.Mi.IdE X)
    (hz : ∀ k, (B.d.i₀ *ᵥ vecB B.o B.ζ) k = X.ιE (X.zR u (Fin.cast (GlobalTheory.Core.Mi.rank_eq X h) k))) :
    star B.ζ ⬝ᵥ B.L.gram *ᵥ B.ζ = -(((D.mem u).A.T : ℕ) : D.host.E) := by
  have hw : B.d.i₀ *ᵥ (B.o.iB *ᵥ B.ζ) = GlobalTheory.Core.SBesEx.cY X h (X.zu u) := funext hz
  rw [← B.o.isoB, ← quad_mulVec, ← B.d.iso, ← quad_mulVec, hw, GlobalTheory.Core.SBesEx.cY_isom D X h hE, X.zu_norm]

theorem tau_line {n p : ℕ} (hn : n = 1) (hp : p = 1) (G : Matrix (Fin n) (Fin n) D.host.E)
    (G₀ : Matrix (Fin p) (Fin p) D.host.E) (ζ : Fin n → D.host.E) (ζ₀ : Fin p → D.host.E) (lam c : D.host.E)
    (h₀ : star ζ₀ ⬝ᵥ G₀ *ᵥ ζ₀ ≠ 0)
    (hrel : star lam * lam * (star ζ ⬝ᵥ G *ᵥ ζ) = c * (star ζ₀ ⬝ᵥ G₀ *ᵥ ζ₀)) :
    (Matrix.of fun i k => lam * ζ i / ζ₀ k)ᴴ * (G * Matrix.of fun i k => lam * ζ i / ζ₀ k) = c • G₀ ∧
      (Matrix.of fun i k => lam * ζ i / ζ₀ k) *ᵥ ζ₀ = lam • ζ := by
  subst hn; subst hp
  simp only [dotProduct, mulVec, Fin.sum_univ_one, Pi.star_apply] at h₀ hrel
  have hz : ζ₀ 0 ≠ 0 := fun h => h₀ (by rw [h]; simp)
  have hz' : star (ζ₀ 0) ≠ 0 := star_ne_zero.2 hz
  constructor
  · refine Matrix.ext fun i k => ?_
    obtain rfl : i = 0 := Subsingleton.elim _ _
    obtain rfl : k = 0 := Subsingleton.elim _ _
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, Fin.sum_univ_one, Matrix.smul_apply,
      smul_eq_mul, star_div₀, star_mul', star_inv₀]
    field_simp
    first | linear_combination hrel | (rw [div_eq_iff (mul_ne_zero hz' hz)]; linear_combination hrel)
  · funext i
    obtain rfl : i = 0 := Subsingleton.elim _ _
    simp only [mulVec, dotProduct, Matrix.of_apply, Fin.sum_univ_one, Pi.smul_apply, smul_eq_mul]
    field_simp

set_option maxHeartbeats 1000000 in

theorem exists_yRat : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex) (u : D.what₂.Word), PkHyp W → ∀ a : XGeo D, IsLineVec a.Lz a.ζ₀ → star a.ζ₀ ⬝ᵥ a.Lz.gram *ᵥ a.ζ₀ = (((D.mem u).A.T : ℕ) : D.host.E) → ∃ (y : YRat a) (B : GlobalTheory.Core.Mi.SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)) (h0 : 0 + 2 * D.R.rS + 2 = D.R.m), y.Tau (-D.host.xi0 ^ (D.R.m / 2)) ∧ B.lev = (y.bes 0 D.R.rS h0).lev (a.x 0).vol ∧ B.Adapted (W.S.tr u).wt ∧ GlobalTheory.MiTop.Framed B ∧ star B.ζ ⬝ᵥ B.L.gram *ᵥ B.ζ = -(((D.mem u).A.T : ℕ) : D.host.E) ∧ ∀ k, (B.d.i₀ *ᵥ vecB B.o B.ζ) k = W.S.X.ιE (W.S.X.zR u (Fin.cast (GlobalTheory.Core.Mi.rank_eq W.S.X W.Q.instEq) k)) := by
  intro D L hT Gi Gl Kc Yd cX ex W u hP a hLz hT0
  have hxi : D.host.xi0 ≠ 0 := GlobalTheory.ChiGrid.cmHost_imaginaryGenerator_ne_zero
  have hN : D.host.xi0 * star D.host.xi0 ≠ 0 := mul_ne_zero hxi (star_ne_zero.2 hxi)

  obtain ⟨lam0, hlam0, hB⟩ := GlobalTheory.Core.Mi.exists_sBes_scaled_dual D W.S.X W.Q.instEq u W.Q.Rl.ψ _ (W.S.tr u)
    hP.bot.idE W.Q.stdChar
  obtain ⟨B, hA, hvA, hz, he, he'⟩ := hB 1 (a.x 0).vol one_ne_zero
  have hz1 : ∀ k, (B.d.i₀ *ᵥ vecB B.o B.ζ) k = W.S.X.ιE (W.S.X.zR u (Fin.cast (GlobalTheory.Core.Mi.rank_eq W.S.X W.Q.instEq) k)) :=
    fun k => by rw [hz k, one_mul]
  have hB0 := sbes_norm B hP.bot.idE hz1

  have hI := GlobalTheory.T.exists_thetaLiftSpaces_positiveIndex_with_lineNorms D u (fun j hj => D.X_posDef j hj)
  have hbes : ∀ j ρ (h : j + 2 * ρ + 2 = D.R.m), ∃ b : BesAt (Yc D j) (D.sp.X j) ρ,
      star b.ζ ⬝ᵥ b.L.gram *ᵥ b.ζ * (D.host.xi0 * star D.host.xi0) ^ (j / 2) = -(((D.mem u).A.T : ℕ) : D.host.E) := by
    intro j ρ h
    obtain ⟨V, b, hr, hs, hsig, hn⟩ := hI.1 j ρ h
    obtain ⟨b2, hb2⟩ := bes_to_Yc j ρ (by omega) b hr hs hsig
    exact ⟨b2, by rw [hb2]; exact hn⟩
  choose b' hb' using hbes
  have hjac : ∀ j ρ, j + 2 * ρ + 2 = D.R.m → Nonempty (JacAt (Yc D (j + 1)) (D.sp.X (j + 1)) ρ) := by
    intro j ρ h
    obtain ⟨V, b, hr, hs, hsig⟩ := hI.2 j ρ h
    exact jac_to_Yc (j + 1) ρ (by omega) b hr hs hsig
  obtain ⟨bes, hbes_def⟩ : ∃ f, f = besF (besOf B) b' := ⟨_, rfl⟩
  have h0 : 0 + 2 * D.R.rS + 2 = D.R.m := by
    show 0 + 2 * (D.R.m / 2 - 1) + 2 = D.R.m
    obtain ⟨k, hk⟩ := D.R.m_even
    have := D.R.two_le_m
    omega
  have hbes0 : bes 0 D.R.rS h0 = besOf B := by rw [hbes_def]; rfl
  have hnorm : ∀ j ρ h, star (bes j ρ h).ζ ⬝ᵥ (bes j ρ h).L.gram *ᵥ (bes j ρ h).ζ *
      (D.host.xi0 * star D.host.xi0) ^ (j / 2) = -(((D.mem u).A.T : ℕ) : D.host.E) := by
    rw [hbes_def]; exact besF_norm (besOf B) b' _ _ hB0 hb'

  have hlnk : ∀ j σ (h : j + 2 * (σ + 1) + 2 = D.R.m), Nonempty (Link ((bes j (σ + 1) h).lev (a.x j).vol)
      (bes (j + 1 + 1) σ (idx_step h)).L (bes (j + 1 + 1) σ (idx_step h)).ζ) := by
    intro j σ h
    have hn1 := hnorm j (σ + 1) h
    have hn2 := hnorm (j + 1 + 1) σ (idx_step h)
    have e : (j + 1 + 1) / 2 = j / 2 + 1 := by omega
    rw [e, pow_succ] at hn2
    have hrel : star (bes j (σ + 1) h).ζ ⬝ᵥ (bes j (σ + 1) h).L.gram *ᵥ (bes j (σ + 1) h).ζ =
        D.host.xi0 * star D.host.xi0 * (star (bes (j + 1 + 1) σ (idx_step h)).ζ ⬝ᵥ
          (bes (j + 1 + 1) σ (idx_step h)).L.gram *ᵥ (bes (j + 1 + 1) σ (idx_step h)).ζ) := by
      apply mul_right_cancel₀ (pow_ne_zero (j / 2) hN)
      rw [hn1]
      linear_combination -hn2
    have hl := (GlobalTheory.Unf.LinkExist.link_of_norm D (σ + 1) ((bes j (σ + 1) h).lev (a.x j).vol)
      (bes (j + 1 + 1) σ (idx_step h)).L (bes (j + 1 + 1) σ (idx_step h)).ζ D.host.xi0
      (bes (j + 1 + 1) σ (idx_step h)).line hrel).2
    rwa [div_self hxi, one_smul] at hl
  have hvol := GlobalTheory.Unf.VolExist.measures_exist D

  have hrelT : ∀ j (h : j + 2 * 0 + 2 = D.R.m), star (-D.host.xi0 ^ (D.R.m / 2)) * (-D.host.xi0 ^ (D.R.m / 2)) *
      (star (bes j 0 h).ζ ⬝ᵥ (bes j 0 h).L.gram *ᵥ (bes j 0 h).ζ) =
        -(D.host.xi0 * star D.host.xi0) * (star a.ζ₀ ⬝ᵥ a.Lz.gram *ᵥ a.ζ₀) := by
    intro j h
    have hn := hnorm j 0 h
    have e : D.R.m / 2 = j / 2 + 1 := by omega
    have hl : star (-D.host.xi0 ^ (D.R.m / 2)) * (-D.host.xi0 ^ (D.R.m / 2)) =
        (D.host.xi0 * star D.host.xi0) ^ (D.R.m / 2) := by
      rw [star_neg, star_pow, neg_mul_neg, mul_pow]; ring
    rw [hl, e, pow_succ, hT0]
    linear_combination (D.host.xi0 * star D.host.xi0) * hn
  refine ⟨⟨bes, fun j ρ h => (hjac j ρ h).some, fun j σ h => (hlnk j σ h).some, fun j σ h => (hvol.2.2.1 _ _).some,
    fun j h => Matrix.of fun i k => -D.host.xi0 ^ (D.R.m / 2) * (bes j 0 h).ζ i / a.ζ₀ k⟩, B, h0, ?_, ?_, hA,
    ⟨1, lam0, one_ne_zero, hlam0, hz, he, he'⟩, hB0, hz1⟩
  · intro j h
    exact tau_line (bes j 0 h).line.1 hLz.1 _ _ _ _ _ _ hLz.2 (hrelT j h)
  · show B.lev = (bes 0 D.R.rS h0).lev (a.x 0).vol
    rw [hbes0, ← hvA]
    rfl

end GlobalTheory.Fam.RatDec

end
