import Formalism.SharpRestriction.GrowthBounds.TwistedSubstitution.Proposition5Gram
import Formalism.SharpRestriction.GrowthBounds.RootWeights.ValuationBoundDetPowerFactor
import Formalism.SharpRestriction.GrowthBounds.RootWeights.MulLaurentSup
import Formalism.SharpRestriction.GrowthBounds.RootWeights.DerivativeValuationBounds

noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.TestSideWords

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.PlaneGramData Formalism.MainNotions.TestSideCounting Formalism.MainNotions.G.GLWeightTheory

section TieG

variable {n' r : ℕ} [NeZero n'] (Fr : Frames n' r) (p : ℕ) (deg : Fin n' → ℕ) (Y : ℝ) (k : ℕ) (mS : ℕ)
  {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {J : ℕ} (K : ℕ) [NeZero K]

def TwistedSubstitutionGrowthBound (sc sL : ℝ) (Dt : SignedChainData p O r J) (dPl : TL J Dt.nL r → ℕ) (ka : ZMod J → ℕ → Fin K → ℤ) : Prop :=
  J = Fr.J ∧
  (∀ j, Dt.nL j = (Fr.LLset (segZ j)).card) ∧
  (∀ j l, Dt.sgn j l = decide (Even (llPos Fr (segZ j) l.val))) ∧
  Dt.d = dPl ∧
  (∀ j (mm : Fin r), Dt.gP j mm = (Fr.fr (segZ j + 1) (r - 1) - Fr.fr (segZ j) (r - 1)).toNat) ∧
  (∀ j, Dt.nch j = Dt.nL j + 1) ∧
  (∀ j (i : Fin (Dt.nch j)), Dt.chain j i = {x | x.isRight} ∪ {x | ∃ l : Fin (Dt.nL j), x = Sum.inl l ∧ l.val < i.val}) ∧
  (∀ j (i : Fin (Dt.nch j)), Dt.th j i = thStar Fr p deg Y k mS Dt.nL K ka j i.val - sc * slU Fr p deg Y k Dt.nL j i.val) ∧
  ∀ j (mm : Fin r), mm.val + 2 ≤ r →
    Dt.thL j mm = thStar Fr p deg Y k mS Dt.nL K ka j (Dt.nL j + (r - 1 - mm.val)) -
      sL * slU Fr p deg Y k Dt.nL j (Dt.nL j + (r - 1 - mm.val))

theorem tied_iff (Dt : SignedChainData p O r J) (dPl : TL J Dt.nL r → ℕ) (ka : ZMod J → ℕ → Fin K → ℤ) :
    Tied Fr p deg Y k mS K Dt dPl ka ↔ TwistedSubstitutionGrowthBound Fr p deg Y k mS K (1 / 8) (3 / 8) Dt dPl ka := by
  unfold Tied TwistedSubstitutionGrowthBound
  simp only [one_div_mul_eq_div]

end TieG

def MemAtG (sc sL : ℝ) (p : ℕ) {n' r K m : ℕ} [NeZero n'] [NeZero r] [NeZero K] (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (hk : m + 1 = r + K) (Fr : Frames n' r) (deg : Fin n' → ℕ) (Y : ℝ) (N₁ G' cP : ℕ)
    (F : MvPolynomial (TV n' (m + 1)) (KK O)) : Prop :=
  ∀ (J : ℕ) [NeZero J] (Dt : SignedChainData p O r J) (dPl dNo : TL J Dt.nL r → ℕ) (ka : ZMod J → ℕ → Fin K → ℤ),
    TwistedSubstitutionGrowthBound Fr p deg Y (r + K) (mStar p Fr (r + K) N₁ (p ^ G') cP) K sc sL Dt dPl ka →
    ∀ (rho : TL J Dt.nL r × Fin (r + K) → ℕ) (e : Module.End (KK O) (MvPolynomial (TL J Dt.nL r × Fin K) (KK O))),
      IsJProj (normE p K Dt) {fun i => ka i.1 i.2.val} e →
      ∀ nu : TL J Dt.nL r × Fin K →₀ ℕ,
        Dt.XX (planeCoeff nu (oneT e (levImg Fr p hk Dt.nL rho dPl dNo F)))

theorem memAt_iff (p : ℕ) {n' r K m : ℕ} [NeZero n'] [NeZero r] [NeZero K] (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (hk : m + 1 = r + K) (Fr : Frames n' r) (deg : Fin n' → ℕ) (Y : ℝ) (N₁ G' cP : ℕ)
    (F : MvPolynomial (TV n' (m + 1)) (KK O)) :
    MemAt p O hk Fr deg Y N₁ G' cP F ↔ MemAtG (1 / 8) (3 / 8) p O hk Fr deg Y N₁ G' cP F := by
  unfold MemAt MemAtG
  simp only [tied_iff]

section Lin

theorem sumFilt_sub {σ R M : Type*} [CommSemiring R] [AddCommMonoid M] (P : (σ →₀ ℕ) → Prop) [DecidablePred P]
    (g : (σ →₀ ℕ) → R →+ M) (H : MvPolynomial σ R) (s : Finset (σ →₀ ℕ)) (hs : H.support ⊆ s) :
    ∑ mo ∈ H.support.filter P, g mo (H.coeff mo) = ∑ mo ∈ s.filter P, g mo (H.coeff mo) := by
  refine Finset.sum_subset (Finset.filter_subset_filter P hs) fun mo hmo hnot => ?_
  have h0 : H.coeff mo = 0 := by
    by_contra h
    exact hnot (Finset.mem_filter.mpr ⟨MvPolynomial.mem_support_iff.mpr h, (Finset.mem_filter.mp hmo).2⟩)
  rw [h0, map_zero]

theorem sumFilt_add {σ R M : Type*} [CommSemiring R] [AddCommMonoid M] (P : (σ →₀ ℕ) → Prop) [DecidablePred P]
    (g : (σ →₀ ℕ) → R →+ M) (F G : MvPolynomial σ R) :
    ∑ mo ∈ (F + G).support.filter P, g mo ((F + G).coeff mo) =
      ∑ mo ∈ F.support.filter P, g mo (F.coeff mo) + ∑ mo ∈ G.support.filter P, g mo (G.coeff mo) := by
  classical
  rw [sumFilt_sub P g (F + G) (F.support ∪ G.support) MvPolynomial.support_add,
    sumFilt_sub P g F (F.support ∪ G.support) Finset.subset_union_left,
    sumFilt_sub P g G (F.support ∪ G.support) Finset.subset_union_right, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun mo _ => ?_
  rw [MvPolynomial.coeff_add, map_add]

theorem sumFilt_smul {σ R S M : Type*} [CommSemiring R] [Semiring S] [Module S R] [AddCommMonoid M] [Module S M]
    (P : (σ →₀ ℕ) → Prop) [DecidablePred P] (g : (σ →₀ ℕ) → R →ₗ[S] M) (c : S) (F : MvPolynomial σ R) :
    ∑ mo ∈ (c • F).support.filter P, g mo ((c • F).coeff mo) =
      c • ∑ mo ∈ F.support.filter P, g mo (F.coeff mo) := by
  rw [Finset.smul_sum]
  refine (Finset.sum_subset (Finset.filter_subset_filter P MvPolynomial.support_smul) ?_).trans
    (Finset.sum_congr rfl fun mo _ => ?_)
  · intro mo hmo hnot
    have h0 : (c • F).coeff mo = 0 := by
      by_contra h
      exact hnot (Finset.mem_filter.mpr ⟨MvPolynomial.mem_support_iff.mpr h, (Finset.mem_filter.mp hmo).2⟩)
    rw [h0, map_zero]
  · rw [MvPolynomial.coeff_smul, map_smul]

end Lin

section Lin2

variable {Kf : Type} [Field Kf]

theorem sumSupp_add {σ R M : Type*} [CommSemiring R] [AddCommMonoid M] (g : (σ →₀ ℕ) → R →+ M)
    (F G : MvPolynomial σ R) :
    ∑ mo ∈ (F + G).support, g mo ((F + G).coeff mo) =
      ∑ mo ∈ F.support, g mo (F.coeff mo) + ∑ mo ∈ G.support, g mo (G.coeff mo) := by
  classical
  have key : ∀ H : MvPolynomial σ R, H.support ⊆ F.support ∪ G.support →
      ∑ mo ∈ H.support, g mo (H.coeff mo) = ∑ mo ∈ F.support ∪ G.support, g mo (H.coeff mo) := by
    intro H hH
    refine Finset.sum_subset hH fun mo _ hmo => ?_
    rw [MvPolynomial.notMem_support_iff.mp hmo, map_zero]
  rw [key _ MvPolynomial.support_add, key F Finset.subset_union_left, key G Finset.subset_union_right,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun mo _ => ?_
  rw [MvPolynomial.coeff_add, map_add]

theorem sumSupp_smul {σ R S M : Type*} [CommSemiring R] [Semiring S] [Module S R] [AddCommMonoid M] [Module S M]
    (g : (σ →₀ ℕ) → R →ₗ[S] M) (c : S) (F : MvPolynomial σ R) :
    ∑ mo ∈ (c • F).support, g mo ((c • F).coeff mo) = c • ∑ mo ∈ F.support, g mo (F.coeff mo) := by
  rw [Finset.smul_sum]
  refine (Finset.sum_subset MvPolynomial.support_smul fun mo _ hmo => ?_).trans
    (Finset.sum_congr rfl fun mo _ => ?_)
  · rw [MvPolynomial.notMem_support_iff.mp hmo, map_zero]
  · rw [MvPolynomial.coeff_smul, map_smul]

def mono2 {σ τ : Type} (a : σ →₀ ℕ) (b : τ →₀ ℕ) : Kf →ₗ[Kf] MvPolynomial σ (MvPolynomial τ Kf) where
  toFun x := monomial a (monomial b x)
  map_add' x y := by simp only [map_add]
  map_smul' c x := by simp only [MvPolynomial.smul_monomial, RingHom.id_apply]

def monoE {σ τ : Type} (e : Module.End Kf (MvPolynomial τ Kf)) (a : σ →₀ ℕ) :
    MvPolynomial τ Kf →ₗ[Kf] MvPolynomial σ (MvPolynomial τ Kf) where
  toFun q := monomial a (e q)
  map_add' x y := by simp only [map_add]
  map_smul' c x := by simp only [map_smul, MvPolynomial.smul_monomial, RingHom.id_apply]

def monoC {σ τ : Type} (nu : τ →₀ ℕ) (a : σ →₀ ℕ) : MvPolynomial τ Kf →ₗ[Kf] MvPolynomial σ Kf where
  toFun q := monomial a (q.coeff nu)
  map_add' x y := by simp only [MvPolynomial.coeff_add, map_add]
  map_smul' c x := by simp only [MvPolynomial.coeff_smul, MvPolynomial.smul_monomial, RingHom.id_apply]

def cMul {σ : Type} (Q : MvPolynomial σ Kf) : Kf →ₗ[Kf] MvPolynomial σ Kf where
  toFun x := C x * Q
  map_add' x y := by simp only [map_add, add_mul]
  map_smul' c x := by simp only [MvPolynomial.smul_eq_C_mul, smul_eq_mul, C_mul, mul_assoc, RingHom.id_apply]

theorem oneT_add {σ τ : Type} (e : Module.End Kf (MvPolynomial τ Kf)) (A B : MvPolynomial σ (MvPolynomial τ Kf)) :
    oneT e (A + B) = oneT e A + oneT e B := sumSupp_add (fun mo => (monoE e mo).toAddMonoidHom) A B

theorem oneT_smul {σ τ : Type} (e : Module.End Kf (MvPolynomial τ Kf)) (c : Kf)
    (A : MvPolynomial σ (MvPolynomial τ Kf)) : oneT e (c • A) = c • oneT e A := sumSupp_smul (fun mo => monoE e mo) c A

theorem planeCoeff_add {σ τ : Type} (nu : τ →₀ ℕ) (A B : MvPolynomial σ (MvPolynomial τ Kf)) :
    planeCoeff nu (A + B) = planeCoeff nu A + planeCoeff nu B := sumSupp_add (fun mo => (monoC nu mo).toAddMonoidHom) A B

theorem planeCoeff_smul {σ τ : Type} (nu : τ →₀ ℕ) (c : Kf) (A : MvPolynomial σ (MvPolynomial τ Kf)) :
    planeCoeff nu (c • A) = c • planeCoeff nu A := sumSupp_smul (fun mo => monoC nu mo) c A

theorem oneT_zero {σ τ : Type} (e : Module.End Kf (MvPolynomial τ Kf)) :
    oneT e (0 : MvPolynomial σ (MvPolynomial τ Kf)) = 0 := by
  simp [oneT]

theorem planeCoeff_zero {σ τ : Type} (nu : τ →₀ ℕ) : planeCoeff nu (0 : MvPolynomial σ (MvPolynomial τ Kf)) = 0 := by
  simp [planeCoeff]

end Lin2

section Lin3

variable {n' r K m : ℕ} [NeZero n'] (Fr : Frames n' r) (p : ℕ) {O : Type} [CommRing O] [IsDomain O]
  (hk : m + 1 = r + K) {J : ℕ} [NeZero J] (nL : ZMod J → ℕ)

theorem levImg_add (rho : TL J nL r × Fin (r + K) → ℕ) (dPl dNo : TL J nL r → ℕ)
    (F G : MvPolynomial (TV n' (m + 1)) (KK O)) :
    levImg Fr p hk nL rho dPl dNo (F + G) = levImg Fr p hk nL rho dPl dNo F + levImg Fr p hk nL rho dPl dNo G := by
  exact sumFilt_add (fun mo => InLow Fr p hk nL rho mo ∧ InBlock Fr p hk nL dPl dNo mo)
    (fun mo => (mono2 (plMon Fr p hk nL mo) (noMon Fr p hk nL mo)).toAddMonoidHom) F G

theorem levImg_smul (rho : TL J nL r × Fin (r + K) → ℕ) (dPl dNo : TL J nL r → ℕ) (c : KK O)
    (F : MvPolynomial (TV n' (m + 1)) (KK O)) :
    levImg Fr p hk nL rho dPl dNo (c • F) = c • levImg Fr p hk nL rho dPl dNo F := by
  exact sumFilt_smul (fun mo => InLow Fr p hk nL rho mo ∧ InBlock Fr p hk nL dPl dNo mo)
    (fun mo => mono2 (plMon Fr p hk nL mo) (noMon Fr p hk nL mo)) c F

theorem levImg_zero (rho : TL J nL r × Fin (r + K) → ℕ) (dPl dNo : TL J nL r → ℕ) :
    levImg Fr p hk nL rho dPl dNo (0 : MvPolynomial (TV n' (m + 1)) (KK O)) = 0 := by
  simp [levImg]

end Lin3

section Lin4

variable {p : ℕ} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {r J : ℕ}
  (Dt : SignedChainData p O r J)

theorem Fdig_add (rho : (ZMod J × Fin r) × Fin r → ℕ) (F G : MvPolynomial (TL J Dt.nL r × Fin r) (KK O)) :
    Dt.Fdig rho (F + G) = Dt.Fdig rho F + Dt.Fdig rho G := by
  exact sumFilt_add (Dt.digOK rho)
    (fun mo => (cMul (∏ v ∈ mo.support, MvPolynomial.X (Dt.liftVar v) ^ Dt.liftExp mo v)).toAddMonoidHom) F G

theorem Fdig_smul (rho : (ZMod J × Fin r) × Fin r → ℕ) (c : KK O) (F : MvPolynomial (TL J Dt.nL r × Fin r) (KK O)) :
    Dt.Fdig rho (c • F) = c • Dt.Fdig rho F := by
  exact sumFilt_smul (Dt.digOK rho)
    (fun mo => cMul (∏ v ∈ mo.support, MvPolynomial.X (Dt.liftVar v) ^ Dt.liftExp mo v)) c F

theorem Fdig_zero (rho : (ZMod J × Fin r) × Fin r → ℕ) :
    Dt.Fdig rho (0 : MvPolynomial (TL J Dt.nL r × Fin r) (KK O)) = 0 := by
  simp [SignedChainData.Fdig]

end Lin4

theorem geZ_mono {a b : WithTop ℤ} {t : ℝ} (hab : a ≤ b) (ha : geZ a t) : geZ b t := by
  intro k hk
  subst hk
  induction a using WithTop.recTopCoe with
  | top => exact absurd hab (WithTop.not_top_le_coe k)
  | coe a =>
    have h1 := ha a rfl
    have h2 : a ≤ k := WithTop.coe_le_coe.mp hab
    exact h1.trans (by exact_mod_cast h2)

theorem geZ_min {a b : WithTop ℤ} {t : ℝ} (ha : geZ a t) (hb : geZ b t) : geZ (min a b) t := by
  intro k hk
  rcases min_choice a b with h | h
  · rw [h] at hk; exact ha k hk
  · rw [h] at hk; exact hb k hk

theorem geZ_top (t : ℝ) : geZ ⊤ t := fun k hk => absurd hk WithTop.top_ne_coe

section Val

variable {Kf : Type} [Field Kf] {ι : Type} {n : ℕ} [NeZero n]

theorem valS_C_nn (LL : Letters ι) (S : Set ι) (c : Kf) :
    0 ≤ valS LL S (C c : MvPolynomial (ι × Fin n) Kf) := by
  apply Finset.le_inf
  intro k hk
  rw [flt_mem_sDegs] at hk
  obtain ⟨m, hm⟩ := hk
  simp only [twistSub, MvPolynomial.eval₂Hom_C, RingHom.comp_apply, MvPolynomial.coeff_C, coefL] at hm
  split_ifs at hm with h0
  · by_contra hneg
    have hk0 : k ≠ 0 := by
      intro h
      subst h
      exact hneg (by simp)
    apply hm
    rw [LaurentPolynomial.C_apply, if_neg hk0]
  · first
      | exact (hm rfl).elim
      | exact (hm (by simp only [AddMonoidAlgebra.coeff_zero, Finsupp.coe_zero, Pi.zero_apply])).elim
      | exact (hm (by rw [AddMonoidAlgebra.coeff_zero]; rfl)).elim
      | exact (hm (by rw [← map_zero (LaurentPolynomial.C (R := GLCoord Kf n)), LaurentPolynomial.C_apply]; split_ifs <;> rfl)).elim

theorem valS_smul_ge (LL : Letters ι) (S : Set ι) (c : Kf) (F : MvPolynomial (ι × Fin n) Kf) :
    valS LL S F ≤ valS LL S (c • F) := by
  by_cases hc : c = 0
  · rw [hc, zero_smul]
    have h0 : valS LL S (0 : MvPolynomial (ι × Fin n) Kf) = ⊤ := by simp [valS, sDegs]
    rw [h0]
    exact le_top
  · rw [MvPolynomial.smul_eq_C_mul, mul_valS_mul]
    exact le_add_of_nonneg_left (valS_C_nn LL S c)

theorem valS_zero_eq_top (LL : Letters ι) (S : Set ι) : valS LL S (0 : MvPolynomial (ι × Fin n) Kf) = ⊤ := by
  simp [valS, sDegs]

end Val

section XXLin

variable {p : ℕ} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {r J : ℕ} [NeZero J] [NeZero r]
  (Dt : SignedChainData p O r J)

theorem XX_add {F G : MvPolynomial (TL J Dt.nL r × Fin r) (KK O)} (hF : Dt.XX F) (hG : Dt.XX G) : Dt.XX (F + G) := by
  obtain ⟨hF1, hF2, hF3⟩ := hF
  obtain ⟨hG1, hG2, hG3⟩ := hG
  refine ⟨Submodule.add_mem _ hF1 hG1, fun rho j i => ?_, fun j m hm => ?_⟩
  · rw [Fdig_add]
    exact geZ_mono (mul_valS_add _ _ _ _) (geZ_min (hF2 rho j i) (hG2 rho j i))
  · exact geZ_mono (mul_valS_add _ _ _ _) (geZ_min (hF3 j m hm) (hG3 j m hm))

theorem XX_smul (c : KK O) {F : MvPolynomial (TL J Dt.nL r × Fin r) (KK O)} (hF : Dt.XX F) : Dt.XX (c • F) := by
  obtain ⟨hF1, hF2, hF3⟩ := hF
  refine ⟨Submodule.smul_mem _ c hF1, fun rho j i => ?_, fun j m hm => ?_⟩
  · rw [Fdig_smul]
    exact geZ_mono (valS_smul_ge _ _ c _) (hF2 rho j i)
  · exact geZ_mono (valS_smul_ge _ _ c _) (hF3 j m hm)

theorem XX_zero : Dt.XX (0 : MvPolynomial (TL J Dt.nL r × Fin r) (KK O)) := by
  refine ⟨Submodule.zero_mem _, fun rho j i => ?_, fun j m hm => ?_⟩
  · rw [Fdig_zero, valS_zero_eq_top]
    exact geZ_top _
  · rw [valS_zero_eq_top]
    exact geZ_top _

end XXLin

section MemLin

variable (sc sL : ℝ) (p : ℕ) {n' r K m : ℕ} [NeZero n'] [NeZero r] [NeZero K] (O : Type) [CommRing O] [IsDomain O]
  [IsDiscreteValuationRing O] (hk : m + 1 = r + K) (Fr : Frames n' r) (deg : Fin n' → ℕ) (Y : ℝ) (N₁ G' cP : ℕ)

theorem memAtG_add {F G : MvPolynomial (TV n' (m + 1)) (KK O)} (hF : MemAtG sc sL p O hk Fr deg Y N₁ G' cP F)
    (hG : MemAtG sc sL p O hk Fr deg Y N₁ G' cP G) : MemAtG sc sL p O hk Fr deg Y N₁ G' cP (F + G) := by
  intro J _ Dt dPl dNo ka hT rho e he nu
  rw [levImg_add, oneT_add, planeCoeff_add]
  exact XX_add Dt (hF J Dt dPl dNo ka hT rho e he nu) (hG J Dt dPl dNo ka hT rho e he nu)

theorem memAtG_smul (c : KK O) {F : MvPolynomial (TV n' (m + 1)) (KK O)}
    (hF : MemAtG sc sL p O hk Fr deg Y N₁ G' cP F) : MemAtG sc sL p O hk Fr deg Y N₁ G' cP (c • F) := by
  intro J _ Dt dPl dNo ka hT rho e he nu
  rw [levImg_smul, oneT_smul, planeCoeff_smul]
  exact XX_smul Dt c (hF J Dt dPl dNo ka hT rho e he nu)

theorem memAtG_zero : MemAtG sc sL p O hk Fr deg Y N₁ G' cP 0 := by
  intro J _ Dt dPl dNo ka hT rho e he nu
  rw [levImg_zero, oneT_zero, planeCoeff_zero]
  exact XX_zero Dt

def memSub : Submodule (KK O) (MvPolynomial (TV n' (m + 1)) (KK O)) where
  carrier := {F | MemAtG sc sL p O hk Fr deg Y N₁ G' cP F}
  add_mem' := memAtG_add sc sL p O hk Fr deg Y N₁ G' cP
  zero_mem' := memAtG_zero sc sL p O hk Fr deg Y N₁ G' cP
  smul_mem' c _ h := memAtG_smul sc sL p O hk Fr deg Y N₁ G' cP c h

end MemLin

end Formalism.MainNotions.TestSideWords
