import Formalism.LocalToGlobal.IndefiniteReal.ModelConjugation
import Formalism.LocalToGlobal.IndefiniteReal.DiscreteSeriesParameterPos
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.InfFam

noncomputable section

open Matrix
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Mult

namespace Formalism.IndefR.ModelConjugation

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem isEnum_unique {n : ℕ} {S : SPar} {lam lam' : Fin n → ℝ} {ε ε' : Fin n → Bool}
    (h : IsEnum S lam ε) (h' : IsEnum S lam' ε') : lam = lam' ∧ ε = ε' := by
  obtain ⟨ha, q, hq, hS⟩ := h
  obtain ⟨ha', q', hq', hS'⟩ := h'
  have key : ∀ a, ∃ b, q' b = q a ∧ ε' b = ε a := by
    intro a
    have hm : (q a, ε a) ∈ S := by rw [hS]; exact Finset.mem_image_of_mem _ (Finset.mem_univ a)
    rw [hS'] at hm
    obtain ⟨b, -, hb⟩ := Finset.mem_image.mp hm
    exact ⟨b, congrArg Prod.fst hb, congrArg Prod.snd hb⟩
  have key' : ∀ b, ∃ a, q a = q' b := by
    intro b
    have hm : (q' b, ε' b) ∈ S := by rw [hS']; exact Finset.mem_image_of_mem _ (Finset.mem_univ b)
    rw [hS] at hm
    obtain ⟨a, -, hqa⟩ := Finset.mem_image.mp hm
    exact ⟨a, congrArg Prod.fst hqa⟩
  have hm1 : StrictMono fun a => OrderDual.toDual (lam a) := fun a b hab =>
    OrderDual.toDual_lt_toDual.2 (ha hab)
  have hm2 : StrictMono fun a => OrderDual.toDual (lam' a) := fun a b hab =>
    OrderDual.toDual_lt_toDual.2 (ha' hab)
  have hr : Set.range (fun a => OrderDual.toDual (lam a)) = Set.range (fun a => OrderDual.toDual (lam' a)) := by
    ext x
    constructor
    · rintro ⟨a, rfl⟩
      obtain ⟨b, hb, -⟩ := key a
      exact ⟨b, by simp only [hq, hq', hb]⟩
    · rintro ⟨b, rfl⟩
      obtain ⟨a, hqa⟩ := key' b
      exact ⟨a, by simp only [hq, hq', hqa]⟩
  have hl : lam = lam' := by
    have := (StrictMono.range_inj hm1 hm2).mp hr
    funext a
    exact congrArg OrderDual.ofDual (congrFun this a)
  refine ⟨hl, funext fun a => ?_⟩
  obtain ⟨b, hb, he⟩ := key a
  have hab : b = a := by
    apply ha'.injective
    rw [hq' b, hb, ← hq a, hl]
  rw [← he, hab]

theorem rank_zeroth_component_eq (D : D7) : (D.sp.Y 0).rank = D.R.r := by
  rw [D.sp.Y_rank 0 (Nat.zero_le _)]; simp [Ranks.rankY]

theorem isEnum_parB_rec (D : D7) (τ : D.what₂.Tau) (n : ℕ) (hn : n = D.R.r) :
    IsEnum (parB (tparRec D) 0 τ) (fun a : Fin n => -((lamAt (D.hc τ) (n - 1 - a) : ℚ) : ℝ))
      (fun a : Fin n => sgA D.R (n - 1 - a)) := by
  subst hn
  have hv : ∀ a : Fin D.R.r, D.R.r - 1 - (a : ℕ) = ((Fin.rev a : Fin D.R.r) : ℕ) := by
    intro a; rw [Fin.val_rev]; omega
  have e1 : (fun a : Fin D.R.r => -((lamAt (D.hc τ) (D.R.r - 1 - a) : ℚ) : ℝ)) =
      fun a => -((lamAt (D.hc τ) (Fin.rev a : Fin D.R.r) : ℚ) : ℝ) := funext fun a => by rw [hv a]
  have e2 : (fun a : Fin D.R.r => sgA D.R (D.R.r - 1 - a)) = fun a => sgA D.R (Fin.rev a : Fin D.R.r) :=
    funext fun a => by rw [hv a]
  rw [e1, e2]
  show IsEnum (dualPar (parA (tparHC D _ _) 0 τ)) _ _
  rw [parA_eq]
  exact DiscreteSeriesPlaces.isEnum_dual (lam := fun a => ((lamAt (D.hc τ) a : ℚ) : ℝ))
    ⟨fun _ _ h => by dsimp only; exact_mod_cast lamAt_strictAnti _ h, fun a => lamAt (D.hc τ) a,
      fun _ => rfl, rfl⟩

theorem lamS_eq (R : Ranks) (P : HCParam R) (i : Fin R.r) : Formalism.MainNotions.S.lamS R P i = ((lamAt P i : ℚ) : ℝ) := by
  unfold Formalism.MainNotions.S.lamS lamAt
  split_ifs <;> simp

theorem epsS_eq (R : Ranks) (i : Fin R.r) : Formalism.MainNotions.S.epsS R i = sgA R i := by
  unfold Formalism.MainNotions.S.epsS sgA
  by_cases h : (i : ℕ) < R.k - 1
  · simp [h]
  · simp [h, Nat.even_iff]

theorem model_lam_eps (D : D7) (M : DSModel (D.sp.Y 0) (parB (tparRec D) 0)) (τ : D.what₂.Tau) :
    (∀ a : Fin (D.sp.Y 0).rank, M.lam τ a = -((lamAt (D.hc τ) ((D.sp.Y 0).rank - 1 - a) : ℚ) : ℝ)) ∧
      ∀ a : Fin (D.sp.Y 0).rank, M.ε τ a = sgA D.R ((D.sp.Y 0).rank - 1 - a) := by
  obtain ⟨h1, h2⟩ := isEnum_unique (M.enum τ) (isEnum_parB_rec D τ _ (rank_zeroth_component_eq D))
  exact ⟨fun a => congrFun h1 a, fun a => congrFun h2 a⟩

theorem match_X (D : D7) (M : DSModel (D.sp.Y 0) (parB (tparRec D) 0)) (X : Formalism.L2.SG.HidaSetting.HidaSetting D)
    (v : NumberField.InfinitePlace X.B.I.F) (hN : (D.sp.Y 0).rank = X.B.I.n) :
    (∀ a, M.ε (X.pl v) a = X.B.I.ε v (Fin.rev (finCongr hN a))) ∧
      ∀ a, M.lam (X.pl v) a = -X.B.lam v (Fin.rev (finCongr hN a)) := by
  obtain ⟨hl, he⟩ := model_lam_eps D M (X.pl v)
  have hv : ∀ a : Fin (D.sp.Y 0).rank,
      (D.sp.Y 0).rank - 1 - (a : ℕ) = ((Fin.cast X.n_eq (Fin.rev (finCongr hN a)) : Fin D.R.r) : ℕ) := by
    intro a
    have := a.2
    simp only [Fin.val_cast, Fin.val_rev, finCongr_apply]
    omega
  refine ⟨fun a => ?_, fun a => ?_⟩
  · rw [he a, X.eps_eq, epsS_eq, hv a]
  · rw [hl a, X.lam_eq, lamS_eq, hv a]

theorem hc_gap_transfer {n n' : ℕ} (hN : n = n') (lamM : Fin n → ℝ) (εM : Fin n → Bool) (lamX : Fin n' → ℝ)
    (εX : Fin n' → Bool) (hε : ∀ a, εM a = εX (Fin.rev (finCongr hN a)))
    (hl : ∀ a, lamM a = -lamX (Fin.rev (finCongr hN a))) (h : ℝ) (hc : Formalism.QuantumDeterminants.IsHCParam lamM)
    (hg : Formalism.QuantumDeterminants.GapAtLeast εM lamM h) : Formalism.QuantumDeterminants.IsHCParam lamX ∧ Formalism.QuantumDeterminants.GapAtLeast εX lamX h := by
  subst hN
  have e1 : lamX = fun a => -lamM (Fin.rev a) := funext fun a => by rw [hl]; simp
  have e2 : εX = fun a => εM (Fin.rev a) := funext fun a => by rw [hε]; simp
  rw [e1, e2]
  exact ⟨DiscreteSeriesPlaces.isHCParam_dual hc, DiscreteSeriesPlaces.gap_dual hg⟩

theorem model_hc_gap (D : D7) (h : ℝ) (hN : D.NodeGap h) (M : DSModel (D.sp.Y 0) (parB (tparRec D) 0))
    (τ : D.what₂.Tau) : Formalism.QuantumDeterminants.IsHCParam (M.lam τ) ∧ Formalism.QuantumDeterminants.GapAtLeast (M.ε τ) (M.lam τ) h := by
  obtain ⟨lam, ε, hen, hhc, hgap, -, -⟩ := DiscreteSeriesPlaces.exists_enumB D h hN τ _ (rank_zeroth_component_eq D)
  obtain ⟨e1, e2⟩ := isEnum_unique (M.enum τ) hen
  rw [e1, e2]
  exact ⟨hhc, hgap⟩

variable {D : D7}

def frC (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (τ : D.what₂.Tau) : Matrix (Fin (D.sp.Y 0).rank) (Fin X.B.I.n) ℂ :=
  ((D.sp.Y 0).frame.toMatrix X.bas).map (tauE D τ)

def frC' (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (τ : D.what₂.Tau) : Matrix (Fin X.B.I.n) (Fin (D.sp.Y 0).rank) ℂ :=
  (X.bas.toMatrix (D.sp.Y 0).frame).map (tauE D τ)

theorem frC_mul (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (τ : D.what₂.Tau) : frC X τ * frC' X τ = 1 := by
  unfold frC frC'
  rw [← Matrix.map_mul, Module.Basis.toMatrix_mul_toMatrix_flip]
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem frC'_mul (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (τ : D.what₂.Tau) : frC' X τ * frC X τ = 1 := by
  unfold frC frC'
  rw [← Matrix.map_mul, Module.Basis.toMatrix_mul_toMatrix_flip]
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem gram_change (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (v : NumberField.InfinitePlace X.B.I.F) :
    (frC X (X.pl v))ᴴ * gramAt D (D.sp.Y 0) (X.pl v) * frC X (X.pl v) = X.B.I.J.map (X.B.I.φ v) := by
  ext i j
  rw [Matrix.map_apply, X.φ_eq, X.J_eq]
  show _ = tauE D (X.pl v) ((D.sp.Y 0).hT (X.bas i) (X.bas j))
  rw [← (D.sp.Y 0).frame.sum_repr (X.bas i), ← (D.sp.Y 0).frame.sum_repr (X.bas j)]
  simp only [map_sum, map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, map_mul,
    RingHom.id_apply, starRingEnd_apply, Eqv.tauE_star, Matrix.mul_apply, conjTranspose_apply, frC, gramAt,
    Matrix.map_apply, Module.Basis.toMatrix_apply, HSpace.gram]
  simp only [Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

variable {S : D.what₂.Tau → SPar}

def Afr (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (M : DSModel (D.sp.Y 0) S) (v : NumberField.InfinitePlace X.B.I.F) :
    Matrix (Fin (D.sp.Y 0).rank) (Fin X.B.I.n) ℂ :=
  M.fr (X.pl v) * frC X (X.pl v) * X.B.I.P v

def Afr' (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (M : DSModel (D.sp.Y 0) S) (v : NumberField.InfinitePlace X.B.I.F) :
    Matrix (Fin X.B.I.n) (Fin (D.sp.Y 0).rank) ℂ :=
  (X.B.I.P v)⁻¹ * frC' X (X.pl v) * (M.fr (X.pl v))⁻¹

theorem Afr_mul (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (M : DSModel (D.sp.Y 0) S)
    (v : NumberField.InfinitePlace X.B.I.F) : Afr X M v * Afr' X M v = 1 := by
  have hP : IsUnit (X.B.I.P v).det := (Matrix.isUnit_iff_isUnit_det _).1 (X.B.I.P_unit v)
  have hf : IsUnit (M.fr (X.pl v)).det := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit (X.pl v))
  unfold Afr Afr'
  rw [show M.fr (X.pl v) * frC X (X.pl v) * X.B.I.P v * ((X.B.I.P v)⁻¹ * frC' X (X.pl v) * (M.fr (X.pl v))⁻¹) =
      M.fr (X.pl v) * (frC X (X.pl v) * ((X.B.I.P v * (X.B.I.P v)⁻¹) * frC' X (X.pl v))) * (M.fr (X.pl v))⁻¹ by
    simp only [Matrix.mul_assoc]]
  rw [Matrix.mul_nonsing_inv _ hP, Matrix.one_mul, frC_mul, Matrix.mul_one, Matrix.mul_nonsing_inv _ hf]

theorem Afr'_mul (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (M : DSModel (D.sp.Y 0) S)
    (v : NumberField.InfinitePlace X.B.I.F) : Afr' X M v * Afr X M v = 1 := by
  have hP : IsUnit (X.B.I.P v).det := (Matrix.isUnit_iff_isUnit_det _).1 (X.B.I.P_unit v)
  have hf : IsUnit (M.fr (X.pl v)).det := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit (X.pl v))
  unfold Afr Afr'
  rw [show (X.B.I.P v)⁻¹ * frC' X (X.pl v) * (M.fr (X.pl v))⁻¹ * (M.fr (X.pl v) * frC X (X.pl v) * X.B.I.P v) =
      (X.B.I.P v)⁻¹ * (frC' X (X.pl v) * (((M.fr (X.pl v))⁻¹ * M.fr (X.pl v)) * frC X (X.pl v))) * X.B.I.P v by
    simp only [Matrix.mul_assoc]]
  rw [Matrix.nonsing_inv_mul _ hf, Matrix.one_mul, frC'_mul, Matrix.mul_one, Matrix.nonsing_inv_mul _ hP]

theorem Afr_J (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (M : DSModel (D.sp.Y 0) S)
    (v : NumberField.InfinitePlace X.B.I.F) :
    (Afr X M v)ᴴ * Formalism.REAL.Jm (M.ε (X.pl v)) * Afr X M v = Formalism.REAL.Jm (X.B.I.ε v) := by
  unfold Afr
  calc (M.fr (X.pl v) * frC X (X.pl v) * X.B.I.P v)ᴴ * Formalism.REAL.Jm (M.ε (X.pl v)) *
        (M.fr (X.pl v) * frC X (X.pl v) * X.B.I.P v) =
      (X.B.I.P v)ᴴ * ((frC X (X.pl v))ᴴ * ((M.fr (X.pl v))ᴴ * Formalism.REAL.Jm (M.ε (X.pl v)) * M.fr (X.pl v)) *
        frC X (X.pl v)) * X.B.I.P v := by
        simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = Formalism.REAL.Jm (X.B.I.ε v) := by rw [M.fr_gram, gram_change, X.B.I.P_spec]

theorem modelConjAt_rec (D : D7) (hN : D.NodeGap (4 * (D.R.N D.R.m : ℝ) ^ 3 + 2 * D.R.t + 6))
    (M : DSModel (D.sp.Y 0) (parB (tparRec D) 0)) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) :
    ∀ v, ModelConjAt X M v (X.pl v) (Afr X M v) (Afr' X M v) := by
  intro v
  have hr : (D.sp.Y 0).rank = X.B.I.n := (rank_zeroth_component_eq D).trans X.n_eq.symm
  obtain ⟨hcM, hgM⟩ := model_hc_gap D _ hN M (X.pl v)
  obtain ⟨hε, hl⟩ := match_X D M X v hr
  obtain ⟨hcX, hgX⟩ := hc_gap_transfer hr _ _ _ _ hε hl _ hcM hgM
  have hbig : 2 * ((D.sp.Y 0).rank : ℝ) < 4 * (D.R.N D.R.m : ℝ) ^ 3 + 2 * D.R.t + 6 :=
    lt_of_le_of_lt (le_max_left _ _) (DiscreteSeriesPlaces.big_rec D _ (rank_zeroth_component_eq D) (M.ε (X.pl v)))
  have hrR : (X.B.I.n : ℝ) = ((D.sp.Y 0).rank : ℝ) := by exact_mod_cast hr.symm
  have hbigX : 2 * (X.B.I.n : ℝ) < 4 * (D.R.N D.R.m : ℝ) ^ 3 + 2 * D.R.t + 6 := by rw [hrR]; exact hbig
  exact modelConjAt_of X M v (X.pl v) hr hcX _ hgX hbigX hcM _ hgM hbig hε hl _ _ (Afr_mul X M v)
    (Afr'_mul X M v) (Afr_J X M v)

end Formalism.IndefR.ModelConjugation
