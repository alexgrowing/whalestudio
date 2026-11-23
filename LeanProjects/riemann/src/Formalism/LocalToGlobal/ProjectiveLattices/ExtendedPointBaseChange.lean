import Formalism.SharpRestriction.Divisibility.WeightAlgebra

noncomputable section

namespace Formalism.L2.Pj

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra NumberField IsDedekindDomain

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ}

structure PtExt (X : PJ D B P j) where
  Pt' : HeightOneSpectrum (𝓞 B.KO) → Type
  extendedPointBaseChange : ∀ la, Pt' la → (P.loc X.dat (resCh la)).Pt (P.loc X.dat (resCh la)).YY
  vAt' : ∀ la, Pt' la → X.Forms → EReal
  vAt'_zero : ∀ la y, vAt' la y 0 = ⊤
  vAt'_ne_bot : ∀ la y F, vAt' la y F ≠ ⊥
  vAt'_add : ∀ la y F G, min (vAt' la y F) (vAt' la y G) ≤ vAt' la y (F + G)
  vAt'_smul : ∀ la y (a : B.KO) F, a ≠ 0 →
    vAt' la y (a • F) = (((vAdd la a : ℤ) : ℝ) : EReal) + vAt' la y F
  vAt'_mul : ∀ la y w w' (F : B.Cusp j w) (G : B.Cusp j w'),
    vAt' la y (X.inc w F * X.inc w' G) = vAt' la y (X.inc w F) + vAt' la y (X.inc w' G)

def IntAtExt (X : PJ D B P j) (E : PtExt X) : Prop :=
  ∀ w (F : B.Cusp j w), F ∈ B.Mlat j w → ∀ la (y : E.Pt' la), 0 ≤ E.vAt' la y (X.inc w F)

def xplus (X : PJ D B P j) (E : PtExt X) (hM : IntAtExt X E) : PJ D B P j where
  Forms := X.Forms
  rF := X.rF
  aF := X.aF
  aFO := X.aFO
  stF := X.stF
  inc := X.inc
  inc_inj := X.inc_inj
  inc_indep := X.inc_indep
  inc_mul := X.inc_mul
  dat := X.dat
  dat_rk := X.dat_rk
  dat_jj := X.dat_jj
  Pt la := X.Pt la ⊕ E.Pt' la
  pt66 la := Sum.elim (X.pt66 la) (E.extendedPointBaseChange la)
  vAt la := Sum.elim (X.vAt la) (E.vAt' la)
  vAt_zero la
    | .inl y => X.vAt_zero la y
    | .inr y => E.vAt'_zero la y
  vAt_ne_bot la
    | .inl y => X.vAt_ne_bot la y
    | .inr y => E.vAt'_ne_bot la y
  vAt_add la
    | .inl y => X.vAt_add la y
    | .inr y => E.vAt'_add la y
  vAt_smul la
    | .inl y => X.vAt_smul la y
    | .inr y => E.vAt'_smul la y
  vAt_mul la
    | .inl y => X.vAt_mul la y
    | .inr y => E.vAt'_mul la y
  Mlat_eq w F :=
    ⟨fun h la y => match y with
      | .inl y => (X.Mlat_eq w F).1 h la y
      | .inr y => hM w F h la y,
     fun h => (X.Mlat_eq w F).2 fun la y => h la (.inl y)⟩
  thAll := X.thAll
  shortTh := X.shortTh

section xplus

variable (X : PJ D B P j) (E : PtExt X) (hM : IntAtExt X E)

theorem xplus_Pt (la : HeightOneSpectrum (𝓞 B.KO)) : (xplus X E hM).Pt la = (X.Pt la ⊕ E.Pt' la) := rfl

theorem xplus_vAt_inl (la : HeightOneSpectrum (𝓞 B.KO)) (y : X.Pt la) (F : X.Forms) :
    (xplus X E hM).vAt la (.inl y) F = X.vAt la y F := rfl

theorem xplus_vAt_inr (la : HeightOneSpectrum (𝓞 B.KO)) (y : E.Pt' la) (F : X.Forms) :
    (xplus X E hM).vAt la (.inr y) F = E.vAt' la y F := rfl

theorem extended_points_left (la : HeightOneSpectrum (𝓞 B.KO)) (y : X.Pt la) :
    (xplus X E hM).pt66 la (.inl y) = X.pt66 la y := rfl

theorem extended_points_right (la : HeightOneSpectrum (𝓞 B.KO)) (y : E.Pt' la) :
    (xplus X E hM).pt66 la (.inr y) = E.extendedPointBaseChange la y := rfl

theorem xplus_depth_inl (s : 𝓞 B.KO) (w : WeightFamilies.Wt D j) (la : HeightOneSpectrum (𝓞 B.KO)) (y : X.Pt la) :
    (xplus X E hM).depth s w la (.inl y) = X.depth s w la y := rfl

theorem xplus_phiC_inl (la : HeightOneSpectrum (𝓞 B.KO)) (y : X.Pt la) :
    (xplus X E hM).phiC la (.inl y) = X.phiC la y := rfl

end xplus

abbrev withNorm (B : WeightFamilies.Prov D) (N : ∀ j ka, (B.KO →+* ℂ) → B.Cusp j ka → ℝ)
    (h0 : ∀ j ka σ F, 0 ≤ N j ka σ F) (h1 : ∀ j ka σ F, N j ka σ F = 0 ↔ F = 0)
    (h2 : ∀ j ka σ (a : B.KO) F, N j ka σ (a • F) = ‖σ a‖ * N j ka σ F)
    (h3 : ∀ j ka σ F G, N j ka σ (F + G) ≤ N j ka σ F + N j ka σ G)
    (h4 : ∀ j ka σ F, N j ka σ F ≤ B.supN j ka σ F) : WeightFamilies.Prov D :=
  { B with l2NormAlt := N, l2Norm_nonneg_bis := h0, l2Norm_eq_zero_iff := h1, l2Norm_smul_alt := h2, l2Norm_add_le' := h3, l2Norm_le_supNorm_alt := h4 }

section tol2NormAlt

variable (N : ∀ j ka, (B.KO →+* ℂ) → B.Cusp j ka → ℝ)
    (h0 : ∀ j ka σ F, 0 ≤ N j ka σ F) (h1 : ∀ j ka σ F, N j ka σ F = 0 ↔ F = 0)
    (h2 : ∀ j ka σ (a : B.KO) F, N j ka σ (a • F) = ‖σ a‖ * N j ka σ F)
    (h3 : ∀ j ka σ F G, N j ka σ (F + G) ≤ N j ka σ F + N j ka σ G)
    (h4 : ∀ j ka σ F, N j ka σ F ≤ B.supN j ka σ F)

def PJ.tol2NormAlt (X : PJ D B P j) : PJ D (withNorm B N h0 h1 h2 h3 h4) P j where
  Forms := X.Forms
  rF := X.rF
  aF := X.aF
  aFO := X.aFO
  stF := X.stF
  inc := X.inc
  inc_inj := X.inc_inj
  inc_indep := X.inc_indep
  inc_mul := X.inc_mul
  dat := X.dat
  dat_rk := X.dat_rk
  dat_jj := X.dat_jj
  Pt := X.Pt
  pt66 := X.pt66
  vAt := X.vAt
  vAt_zero := X.vAt_zero
  vAt_ne_bot := X.vAt_ne_bot
  vAt_add := X.vAt_add
  vAt_smul := X.vAt_smul
  vAt_mul := X.vAt_mul
  Mlat_eq := X.Mlat_eq
  thAll := X.thAll
  shortTh := X.shortTh

def scalarsWithNorm (S : Scal B) : Scal (withNorm B N h0 h1 h2 h3 h4) := ⟨S.sW, S.sF, S.s0, S.sK⟩

def xplusN (X : PJ D B P j) (E : PtExt X) (hM : IntAtExt X E) : PJ D (withNorm B N h0 h1 h2 h3 h4) P j :=
  PJ.tol2NormAlt N h0 h1 h2 h3 h4 (xplus X E hM)

end tol2NormAlt

section Transfer

variable (N : ∀ j ka, (B.KO →+* ℂ) → B.Cusp j ka → ℝ)
    (h0 : ∀ j ka σ F, 0 ≤ N j ka σ F) (h1 : ∀ j ka σ F, N j ka σ F = 0 ↔ F = 0)
    (h2 : ∀ j ka σ (a : B.KO) F, N j ka σ (a • F) = ‖σ a‖ * N j ka σ F)
    (h3 : ∀ j ka σ F G, N j ka σ (F + G) ≤ N j ka σ F + N j ka σ G)
    (h4 : ∀ j ka σ F, N j ka σ F ≤ B.supN j ka σ F)

set_option maxHeartbeats 4000000 in

theorem concl_xplusN (X : PJ D B P j) (E : PtExt X) (hM : IntAtExt X E) (S : Scal B) (ka wL wF : WeightFamilies.Wt D j)
    (T : ℕ) (nus : HeightOneSpectrum (𝓞 B.KO) → ℝ) (β : ℝ) :
    Concl (xplusN N h0 h1 h2 h3 h4 X E hM) (scalarsWithNorm N h0 h1 h2 h3 h4 S) ka wL wF T nus β ↔
      Concl X S ka wL wF T nus β := Iff.rfl

theorem concl_xplus (X : PJ D B P j) (E : PtExt X) (hM : IntAtExt X E) (S : Scal B) (ka wL wF : WeightFamilies.Wt D j)
    (T : ℕ) (nus : HeightOneSpectrum (𝓞 B.KO) → ℝ) (β : ℝ) :
    Concl (xplus X E hM) S ka wL wF T nus β ↔ Concl X S ka wL wF T nus β := Iff.rfl

end Transfer

section On

variable (cov : ∀ j, WeightFamilies.Wt D j → Prop) (Nn : ∀ j ka, (B.KO →+* ℂ) → B.Cusp j ka → ℝ)

open Classical in

def l2nOn : ∀ j ka, (B.KO →+* ℂ) → B.Cusp j ka → ℝ :=
  fun j ka σ F => if cov j ka then Nn j ka σ F else B.supN j ka σ F

variable {cov Nn}
variable (h0 : ∀ j ka, cov j ka → ∀ σ F, 0 ≤ Nn j ka σ F)
    (h1 : ∀ j ka, cov j ka → ∀ σ F, Nn j ka σ F = 0 ↔ F = 0)
    (h2 : ∀ j ka, cov j ka → ∀ σ (a : B.KO) F, Nn j ka σ (a • F) = ‖σ a‖ * Nn j ka σ F)
    (h3 : ∀ j ka, cov j ka → ∀ σ F G, Nn j ka σ (F + G) ≤ Nn j ka σ F + Nn j ka σ G)
    (h4 : ∀ j ka, cov j ka → ∀ σ F, Nn j ka σ F ≤ B.supN j ka σ F)

include h0 in
theorem l2nOn_nonneg : ∀ j ka σ F, 0 ≤ l2nOn cov Nn j ka σ F := fun j ka σ F => by
  unfold l2nOn; split_ifs with h
  · exact h0 j ka h σ F
  · exact B.supN_nonneg j ka σ F

include h1 in
theorem l2nOn_eq_zero : ∀ j ka σ F, l2nOn cov Nn j ka σ F = 0 ↔ F = 0 := fun j ka σ F => by
  unfold l2nOn; split_ifs with h
  · exact h1 j ka h σ F
  · exact B.supN_eq_zero j ka σ F

include h2 in
theorem l2nOn_smul : ∀ j ka σ (a : B.KO) F, l2nOn cov Nn j ka σ (a • F) = ‖σ a‖ * l2nOn cov Nn j ka σ F :=
  fun j ka σ a F => by
  unfold l2nOn; split_ifs with h
  · exact h2 j ka h σ a F
  · exact B.supN_smul j ka σ a F

include h3 in
theorem l2nOn_add : ∀ j ka σ F G, l2nOn cov Nn j ka σ (F + G) ≤ l2nOn cov Nn j ka σ F + l2nOn cov Nn j ka σ G :=
  fun j ka σ F G => by
  unfold l2nOn; split_ifs with h
  · exact h3 j ka h σ F G
  · exact B.supN_add j ka σ F G

include h4 in
theorem l2nOn_le : ∀ j ka σ F, l2nOn cov Nn j ka σ F ≤ B.supN j ka σ F := fun j ka σ F => by
  unfold l2nOn; split_ifs with h
  · exact h4 j ka h σ F
  · exact le_rfl

abbrev withNormOnWeights : WeightFamilies.Prov D :=
  withNorm B (l2nOn cov Nn) (l2nOn_nonneg h0) (l2nOn_eq_zero h1) (l2nOn_smul h2) (l2nOn_add h3) (l2nOn_le h4)

end On

end Formalism.L2.Pj
