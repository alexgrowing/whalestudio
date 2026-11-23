import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.DataN
import Formalism.LocalRingCardinality.DataRows
import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.NoLocalInvariants
import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.TemperedRepresentations

noncomputable section

namespace GlobalTheory.LocalInv

open NumberField IsDedekindDomain Polynomial Matrix Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory.IndefiniteRowSideFullHecke.NoLocalInvariantsRankParts

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)

abbrev Eig : Type := ∀ w : PlE H, A.LP w → G H.E N.Om → Multiset ℂ

def FrobLift (w : PlE H) (σ : G H.E N.Om) : Prop := IsFrob (F := H.E) (N.plOm.1 w) (normV w) σ

def charRep (i : N.Loc) (χ : G H.E N.Om →* (N.O i)ˣ) : G H.E N.Om →* GL (Fin 1) (N.O i) :=
  (Matrix.GeneralLinearGroup.scalar (Fin 1)).comp χ

def Cont (i : N.Loc) {a : ℕ} (ρ : G H.E N.Om →* GL (Fin a) (N.O i)) : Prop :=
  Continuous (fun g => ((ρ g : GL (Fin a) (N.O i)) : Matrix (Fin a) (Fin a) (N.O i)))

def matK (i : N.Loc) {a : ℕ} (ρ : G H.E N.Om →* GL (Fin a) (N.O i)) (g : G H.E N.Om) :
    Matrix (Fin a) (Fin a) (Kf N i) :=
  ((ρ g : GL (Fin a) (N.O i)) : Matrix (Fin a) (Fin a) (N.O i)).map (algebraMap (N.O i) (Kf N i))

def wd (i : N.Loc) {a : ℕ} (ρ : G H.E N.Om →* GL (Fin a) (N.O i)) (w : PlE H) : A.LP w :=
  A.wdOf i (mapRep (iotaOQ N A i) ρ) w

def DeRham (i : N.Loc) {a : ℕ} (ρ : G H.E N.Om →* GL (Fin a) (N.O i)) (w : PlE H) : Prop :=
  A.IsdRW i (mapRep (iotaOQ N A i) ρ) w

def SubOrQuot (i : N.Loc) {a : ℕ} (ρ : G H.E N.Om →* GL (Fin a) (N.O i)) (χ : G H.E N.Om →* (N.O i)ˣ)
    (w : PlE H) : Prop :=
  ∃ v : Fin a → Kf N i, v ≠ 0 ∧
    ((∀ g ∈ Dec (F := H.E) (N.plOm.1 w), (matK N i ρ g).mulVec v =
        algebraMap (N.O i) (Kf N i) ((χ g : (N.O i)ˣ) : N.O i) • v) ∨
      (∀ g ∈ Dec (F := H.E) (N.plOm.1 w), Matrix.vecMul v (matK N i ρ g) =
        algebraMap (N.O i) (Kf N i) ((χ g : (N.O i)ˣ) : N.O i) • v))

def EigLaws (eig : Eig N A) : Prop := ∀ w σ, FrobLift N w σ →
  (∀ a : A.LP w, Multiset.card (eig w a σ) = A.lpDim a) ∧
  (∀ (a : A.LP w) (s : ℝ), eig w (A.lpTw a s) σ =
    (eig w a σ).map (· * ((normV w : ℕ) : ℂ) ^ ((s : ℝ) : ℂ))) ∧
  (∀ (a χ : A.LP w) (c : ℂ), A.lpDim χ = 1 → eig w χ σ = {c} →
    eig w (A.lpChar a χ) σ = (eig w a σ).map (· * c))

def EigAway (eig : Eig N A) : Prop := ∀ (i : N.Loc) (a : ℕ) (ρ : G H.E N.Om →* GL (Fin a) (N.O i)),
  Cont N i ρ → ∀ w, w ∉ placesOver H.E (N.l i) → ∀ σ, FrobLift N w σ →
    ((ρ σ : GL (Fin a) (N.O i)) : Matrix (Fin a) (Fin a) (N.O i)).charpoly.map (iotaO N A i) =
      ((eig w (wd N A i ρ w) σ).map fun α => X - C α).prod

def EigAbove (eig : Eig N A) : Prop := ∀ (i : N.Loc) (a : ℕ) (ρ : G H.E N.Om →* GL (Fin a) (N.O i))
  (χ : G H.E N.Om →* (N.O i)ˣ), Cont N i ρ → Cont N i (charRep N i χ) →
  ∀ w, w ∈ placesOver H.E (N.l i) → DeRham N A i ρ w → DeRham N A i (charRep N i χ) w →
    SubOrQuot N i ρ χ w → ∀ σ, FrobLift N w σ →
      eig w (wd N A i (charRep N i χ) w) σ ≤ eig w (wd N A i ρ w) σ

def TemperedSizes (eig : Eig N A) : Prop := ∀ w σ, FrobLift N w σ → ∀ a : A.LP w, A.tempered a →
  ∀ α ∈ eig w a σ, ((normV w : ℕ) : ℝ) ^ (-(((A.lpDim a : ℝ) - 1) / 2)) ≤ ‖α‖ ∧
    ‖α‖ ≤ ((normV w : ℕ) : ℝ) ^ (((A.lpDim a : ℝ) - 1) / 2)

def Matches (i : N.Loc) {a : ℕ} (ρ : G H.E N.Om →* GL (Fin a) (N.O i)) (π : A.CG a) (u : ℝ) : Prop :=
  ∀ᶠ w in Filter.cofinite, IsSplitPl H w → ∀ (B : ValuationSubring N.Om) (σ : G H.E N.Om),
    IsPlaceOver (F := H.E) B w → IsFrob (F := H.E) B (normV w) σ →
    ((ρ σ : GL (Fin a) (N.O i)) : Matrix (Fin a) (Fin a) (N.O i)).charpoly.map (iotaO N A i) =
      galPol A (A.lpTw (A.locG π w) u)

def LocalGlobal : Prop := ∀ (i : N.Loc) (a : ℕ), 1 ≤ a → ∀ (π : A.CG a) (η : A.CG 1) (s : ℝ),
  A.csd (A.tw π η) → A.ralg (A.tw π η) → (∀ τ, ∀ z ∈ A.infG η τ, ∃ k : ℤ, (s : ℂ) - z = k) →
  ∀ ρ : G H.E N.Om →* GL (Fin a) (N.O i), Cont N i ρ →
    IsSSRep (mapRep (algebraMap (N.O i) (Kf N i)) ρ) → Matches N A i ρ π (s + (1 - (a : ℝ)) / 2) →
    ∀ w, wd N A i ρ w = A.lpTw (A.locG π w) (s + (1 - (a : ℝ)) / 2) ∧
      (w ∈ placesOver H.E (N.l i) → DeRham N A i ρ w)

def EtaType : Prop := A.csd A.etaT ∧ ∀ τ, ∀ z ∈ A.infG A.etaT τ, ∃ k : ℤ, z = (k : ℂ) + 1 / 2

def WeightRegular : Prop := ∀ (i : N.Loc) (_ : A.AV i) (τ : H.E →+* ℂ), (A.infWt i τ).Nodup ∧
  ∀ z ∈ A.infWt i τ, ∃ k : ℤ, z = (k : ℂ) + ((R.nV : ℂ) - 1) / 2

def GoodCuspidal : Prop := ∀ (i : N.Loc) (x : N.X i) (Sig : List (Part A.CG)),
  HasParamX N A i x Sig → goodSig N A Sig → IsCuspIso N A Sig

theorem weightRegular_of_ext (B : NBC A) : WeightRegular N A := fun i P τ => by
  rw [B.embAV_inf i P]
  exact B.infW_alg _ _ τ

theorem one_lt_normV (w : PlE H) : (1 : ℝ) < ((normV w : ℕ) : ℝ) := by
  have : Finite (𝓞 H.E ⧸ w.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ w.ne_bot
  have : Nontrivial (𝓞 H.E ⧸ w.asIdeal) := Ideal.Quotient.nontrivial_iff.mpr w.isPrime.ne_top
  exact_mod_cast (Finite.one_lt_card : 1 < Nat.card (𝓞 H.E ⧸ w.asIdeal))

theorem normV_ne_zero (w : PlE H) : ((normV w : ℕ) : ℂ) ≠ 0 := by
  have h := one_lt_normV w
  have : (normV w : ℕ) ≠ 0 := by
    intro h0
    rw [h0] at h
    norm_num at h
  exact_mod_cast this

theorem norm_cpow (w : PlE H) (s : ℝ) :
    ‖((normV w : ℕ) : ℂ) ^ ((s : ℝ) : ℂ)‖ = ((normV w : ℕ) : ℝ) ^ s := by
  have h := one_lt_normV w
  have hp : 0 < normV w := by exact_mod_cast (lt_trans one_pos h)
  rw [Complex.norm_natCast_cpow_of_pos hp]
  simp

theorem eventually_out (i : N.Loc) :
    ∀ᶠ w in Filter.cofinite, IsSplitPl H w → SplitOut N i w := by
  have h1 : (placesOver H.E (N.l i)).Finite := by
    have hne : Ideal.span {((N.l i : ℕ) : 𝓞 H.E)} ≠ ⊥ := by
      rw [Ne, Ideal.span_singleton_eq_bot]
      exact_mod_cast (Fact.out : (N.l i).Prime).ne_zero
    refine (Ideal.finite_factors hne).subset fun v hv => ?_
    exact Ideal.dvd_span_singleton.mpr hv
  filter_upwards [h1.compl_mem_cofinite, (N.S i).finite_toSet.compl_mem_cofinite,
    (N.Q i).finite_toSet.compl_mem_cofinite] with w a b c hs
  exact ⟨hs, a, b, c⟩

theorem r_odd (R : Ranks) : Odd R.r := by
  obtain ⟨a, ha⟩ := R.k_even
  obtain ⟨b, hb⟩ := R.m_even
  have := R.two_le_m
  exact ⟨a + b - 1, by unfold Ranks.r; omega⟩

theorem r_add_le (R : Ranks) : R.r + 5 ≤ R.t := R.rank_add_five_le

theorem charRep_val (i : N.Loc) (χ : G H.E N.Om →* (N.O i)ˣ) (g : G H.E N.Om) :
    ((charRep N i χ g : GL (Fin 1) (N.O i)) : Matrix (Fin 1) (Fin 1) (N.O i)) =
      Matrix.scalar (Fin 1) ((χ g : (N.O i)ˣ) : N.O i) := rfl

theorem charRep_charpoly (i : N.Loc) (χ : G H.E N.Om →* (N.O i)ˣ) (g : G H.E N.Om) :
    ((charRep N i χ g : GL (Fin 1) (N.O i)) : Matrix (Fin 1) (Fin 1) (N.O i)).charpoly =
      X - C ((χ g : (N.O i)ˣ) : N.O i) := by
  rw [charRep_val]
  simp [Matrix.charpoly, Matrix.det_unique, Matrix.charmatrix]

theorem charRep_cont (i : N.Loc) (χ : G H.E N.Om →* (N.O i)ˣ)
    (h : Continuous fun g => ((χ g : (N.O i)ˣ) : N.O i)) : Cont N i (charRep N i χ) := by
  unfold Cont
  refine continuous_matrix fun a b => ?_
  obtain rfl : a = b := Subsingleton.elim _ _
  simpa [charRep_val] using h

theorem charRep_ss (i : N.Loc) (χ : G H.E N.Om →* (N.O i)ˣ) :
    IsSSRep (mapRep (algebraMap (N.O i) (Kf N i)) (charRep N i χ)) := by
  intro W _
  obtain ⟨W', h⟩ := W.exists_isCompl
  refine ⟨W', fun g v hv => ?_, h⟩
  have : ((mapRep (algebraMap (N.O i) (Kf N i)) (charRep N i χ) g : GL (Fin 1) (Kf N i)) :
      Matrix (Fin 1) (Fin 1) (Kf N i)).mulVec v =
      algebraMap (N.O i) (Kf N i) ((χ g : (N.O i)ˣ) : N.O i) • v := by
    ext a
    obtain rfl : a = 0 := Subsingleton.elim _ _
    simp [mapRep, charRep_val, Matrix.mulVec, dotProduct]
  rw [this]
  exact W'.smul_mem _ hv

theorem chi_apply (i : N.Loc) (k : ℕ) (hk : k < R.t) (g : G H.E N.Om) :
    N.chi i (k + 1) g = N.chi i 1 g * ((eps N i g) ^ k)⁻¹ := by
  rw [N.chi_def i (k + 1) (by omega) (by omega)]
  simp [eps]

theorem eps_cont (i : N.Loc) : Continuous fun g => ((eps N i g : (N.O i)ˣ) : N.O i) := by
  have h : ∀ g, ((eps N i g : (N.O i)ˣ) : N.O i) =
      ((N.chi i 1 g : (N.O i)ˣ) : N.O i) * ((N.chi i 2 g⁻¹ : (N.O i)ˣ) : N.O i) := by
    intro g
    have := r_add_le R
    rw [← Units.val_mul, chi_apply N i 1 (by omega)]
    simp
  simp only [h]
  exact (N.chi_cont i 1).mul ((N.chi_cont i 2).comp continuous_inv)

theorem iota_eps (i : N.Loc) {w : PlE H} (hw : w ∉ placesOver H.E (N.l i)) {B : ValuationSubring N.Om}
    {σ : G H.E N.Om} (hB : IsPlaceOver (F := H.E) B w) (hσ : IsFrob (F := H.E) B (normV w) σ) :
    iotaO N A i ((eps N i σ : (N.O i)ˣ) : N.O i) = ((normV w : ℕ) : ℂ) := by
  have h := cycZ_of_isFrob (l := N.l i) hw hB hσ
  have : ((eps N i σ : (N.O i)ˣ) : N.O i) =
      algebraMap ℤ_[N.l i] (N.O i) ((cycZ H.E N.Om (N.l i) σ : ℤ_[N.l i]ˣ) : ℤ_[N.l i]) := rfl
  rw [this, h]
  simp

theorem isRoot_charpoly {K : Type} [Field K] {n : ℕ} (M : Matrix (Fin n) (Fin n) K) (c : K)
    (v : Fin n → K) (hv : v ≠ 0) (h : M.mulVec v = c • v ∨ Matrix.vecMul v M = c • v) :
    M.charpoly.IsRoot c := by
  rw [IsRoot.def, Matrix.eval_charpoly]
  rcases h with h | h
  · refine Matrix.exists_mulVec_eq_zero_iff.mp ⟨v, hv, ?_⟩
    rw [Matrix.sub_mulVec, h, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.smul_mulVec,
      Matrix.one_mulVec, sub_self]
  · refine Matrix.exists_vecMul_eq_zero_iff.mp ⟨v, hv, ?_⟩
    rw [Matrix.vecMul_sub, h, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.vecMul_smul,
      Matrix.vecMul_one, sub_self]

theorem eig_mem (eig : Eig N A) (h1 : EigAway N A eig) (h2 : EigAbove N A eig) (i : N.Loc) {a : ℕ}
    (ρ : G H.E N.Om →* GL (Fin a) (N.O i)) (χ : G H.E N.Om →* (N.O i)ˣ) (hρ : Cont N i ρ)
    (hχ : Cont N i (charRep N i χ)) (w : PlE H)
    (dρ : w ∈ placesOver H.E (N.l i) → DeRham N A i ρ w)
    (dχ : w ∈ placesOver H.E (N.l i) → DeRham N A i (charRep N i χ) w)
    (hs : SubOrQuot N i ρ χ w) (σ : G H.E N.Om) (hσ : FrobLift N w σ) (c : ℂ)
    (hc : eig w (wd N A i (charRep N i χ) w) σ = {c}) : c ∈ eig w (wd N A i ρ w) σ := by
  by_cases hw : w ∈ placesOver H.E (N.l i)
  · have := h2 i a ρ χ hρ hχ w hw (dρ hw) (dχ hw) hs σ hσ
    rw [hc] at this
    exact Multiset.singleton_le.mp this
  · have e1 := h1 i 1 _ hχ w hw σ hσ
    rw [hc, charRep_charpoly] at e1
    have hcc : iotaO N A i ((χ σ : (N.O i)ˣ) : N.O i) = c := by
      simpa using e1
    obtain ⟨v, hv, h⟩ := hs
    have hr := isRoot_charpoly (matK N i ρ σ) _ v hv (h.imp (fun h => h σ hσ.1) (fun h => h σ hσ.1))
    have hr2 := hr.map (f := (A.iotaQC i).toRingHom.comp (A.iotaQ i))
    rw [matK, Matrix.charpoly_map, Polynomial.map_map] at hr2
    have hr3 : (((ρ σ : GL (Fin a) (N.O i)) : Matrix (Fin a) (Fin a) (N.O i)).charpoly.map
        (iotaO N A i)).IsRoot c := by
      rw [← hcc]
      exact hr2
    rw [h1 i a ρ hρ w hw σ hσ, IsRoot.def, Polynomial.eval_multiset_prod, Multiset.prod_eq_zero_iff,
      Multiset.map_map, Multiset.mem_map] at hr3
    obtain ⟨α, hα, h0⟩ := hr3
    have : c = α := by simpa [sub_eq_zero] using h0
    rwa [this]

theorem galPol_sum {w : PlE H} (a b : A.LP w) (ha : A.unr a) (hb : A.unr b) :
    galPol A (A.lpSum a b) = galPol A a * galPol A b := by
  unfold galPol
  rw [A.frobEig_sum a b ha hb, Multiset.map_add, Multiset.prod_add]

theorem galPol_tw_sum {w : PlE H} (a b : A.LP w) (ha : A.unr a) (hb : A.unr b) (s : ℝ) :
    galPol A (A.lpTw (A.lpSum a b) s) = galPol A (A.lpTw a s) * galPol A (A.lpTw b s) := by
  rw [A.lpTw_sum, galPol_sum N A _ _ ((A.unr_tw _ _).2 ha) ((A.unr_tw _ _).2 hb)]

theorem galPol_tw_zero (w : PlE H) (s : ℝ) : galPol A (A.lpTw (A.lpZero w) s) = 1 := by
  unfold galPol
  rw [A.frobEig_tw _ _ (A.lpZero_unr w), A.frobEig_zero]
  simp

theorem galPol_foldr {w : PlE H} (a : A.LP w) (ha : A.unr a) (e : ℝ → ℝ) (s : ℝ) (L : List ℝ) :
    A.unr (L.foldr (fun k acc => A.lpSum (A.lpTw a (e k)) acc) (A.lpZero w)) ∧
    galPol A (A.lpTw (L.foldr (fun k acc => A.lpSum (A.lpTw a (e k)) acc) (A.lpZero w)) s) =
      (L.map fun k => galPol A (A.lpTw a (e k + s))).prod := by
  induction L with
  | nil => exact ⟨A.lpZero_unr w, by simpa using galPol_tw_zero N A w s⟩
  | cons k L ih =>
    refine ⟨(A.unr_sum _ _).2 ⟨(A.unr_tw _ _).2 ha, ih.1⟩, ?_⟩
    rw [List.foldr_cons, galPol_tw_sum N A _ _ ((A.unr_tw _ _).2 ha) ih.1, ih.2, A.lpTw_add,
      List.map_cons, List.prod_cons]

theorem list_coe {α β : Type} (f : α → β) (L : List α) :
    (do let a ← L; pure (f a) : List β) = L.map f := by
  induction L with
  | nil => rfl
  | cons a L ih => simpa using ih

theorem galPol_speh (p : Part A.CG) (w : PlE H) (ha : A.unr (A.locG p.π w)) (s : ℝ) :
    A.unr (spehLoc N A p w) ∧ galPol A (A.lpTw (spehLoc N A p w) s) =
      ∏ k ∈ Finset.range p.d, galPol A (A.lpTw (A.locG p.π w) (((p.d : ℝ) - 1) / 2 - k + s)) := by
  have h := galPol_foldr N A _ ha (fun k => ((p.d : ℝ) - 1) / 2 - k) s
    (do let a ← List.range p.d; pure ((a : ℕ) : ℝ))
  refine ⟨h.1, h.2.trans ?_⟩
  rw [list_coe, List.map_map, ← List.prod_toFinset _ List.nodup_range, List.toFinset_range]
  rfl

theorem galPol_block (i : N.Loc) {w : PlE H} (hw : SplitOut N i w) {B : ValuationSubring N.Om}
    {σ : G H.E N.Om} (hB : IsPlaceOver (F := H.E) B w) (hσ : IsFrob (F := H.E) B (normV w) σ) (u : ℝ) :
    galPol A (A.lpTw (A.locG (A.tw (A.muC i) A.etaTinv) w)
      (((R.t : ℝ) - 1) / 2 + (1 - (R.nV : ℝ)) / 2 + u)) =
      X - C (iotaO N A i ((N.chi i 1 σ : (N.O i)ˣ) : N.O i) * ((normV w : ℕ) : ℂ) ^ ((u : ℝ) : ℂ)) := by
  obtain ⟨h1, h2⟩ := A.chi_mu i w hw
  unfold galPol
  rw [← A.lpTw_add, A.frobEig_tw _ _ ((A.unr_tw _ _).2 h1), h2 B σ hB hσ]
  simp [iotaO]

theorem matches_chi (i : N.Loc) (j : ℕ) :
    Matches N A i (charRep N i (N.chi i 1 * eps N i ^ j)) (A.tw (A.muC i) A.etaTinv)
      (((R.t : ℝ) - 1) / 2 + (1 - (R.nV : ℝ)) / 2 + j) := by
  filter_upwards [eventually_out N i] with w hw hs B σ hB hσ
  rw [galPol_block N A i (hw hs) hB hσ, charRep_charpoly]
  simp [iota_eps N A i (hw hs).2.1 hB hσ]

theorem matches_rho (i : N.Loc) (x : N.X i) (π : A.CG R.r) (P : A.AV i) (hP : A.ptV i P = some x)
    (hB : IsBCV N A i P (twistIso N A ([⟨R.r, π, 1⟩] ++ [muPart N A i]) A.etaTinv))
    (ρ : G H.E N.Om →* GL (Fin R.r) (N.O i)) (hρ : IsRankPart N i x ρ) :
    Matches N A i ρ (A.tw π A.etaTinv) ((1 - (R.nV : ℝ)) / 2) := by
  filter_upwards [eventually_out N i, A.locG_unr_ae (A.tw π A.etaTinv)] with w hw hu hs B σ hBw hσ
  have hw := hw hs
  have e1 := congrArg (Polynomial.map (iotaO N A i)) (hρ.2.2 w hw B σ hBw hσ)
  have e2 : (heckePol N i x w).map (iotaO N A i) =
      galPol A (A.lpTw (A.locV i P w) ((1 - (R.nV : ℝ)) / 2)) := A.pt_loc i P x hP w hw
  have e3 := hB.2.2.2.1 w hs
  have s1 := galPol_speh N A ⟨R.r, A.tw π A.etaTinv, 1⟩ w hu ((1 - (R.nV : ℝ)) / 2)
  have s2 := galPol_speh N A ⟨1, A.tw (A.muC i) A.etaTinv, R.t⟩ w (A.chi_mu i w hw).1
    ((1 - (R.nV : ℝ)) / 2)
  have e4 : isoLoc N A (twistIso N A ([⟨R.r, π, 1⟩] ++ [muPart N A i]) A.etaTinv) w =
      A.lpSum (spehLoc N A ⟨R.r, A.tw π A.etaTinv, 1⟩ w)
        (A.lpSum (spehLoc N A ⟨1, A.tw (A.muC i) A.etaTinv, R.t⟩ w) (A.lpZero w)) := rfl
  rw [e2, ← e3, e4, A.lpSum_zero, galPol_tw_sum N A _ _ s1.1 s2.1, s1.2, s2.2, Polynomial.map_mul,
    Polynomial.map_prod] at e1
  have e5 : ∏ c ∈ Finset.Icc 1 R.t,
        (X - C ((N.chi i c σ : (N.O i)ˣ) : N.O i)).map (iotaO N A i) =
      ∏ k ∈ Finset.range R.t, galPol A (A.lpTw (A.locG (A.tw (A.muC i) A.etaTinv) w)
        (((R.t : ℝ) - 1) / 2 - k + (1 - (R.nV : ℝ)) / 2)) := by
    rw [← Finset.Ico_add_one_right_eq_Icc, Finset.prod_Ico_eq_prod_range, Nat.add_sub_cancel]
    refine Finset.prod_congr rfl fun k hk => ?_
    have hx : ((R.t : ℝ) - 1) / 2 - k + (1 - (R.nV : ℝ)) / 2 =
        ((R.t : ℝ) - 1) / 2 + (1 - (R.nV : ℝ)) / 2 + (-(k : ℝ)) := by ring
    rw [hx, galPol_block N A i hw hBw hσ, add_comm 1 k, chi_apply N i k (Finset.mem_range.mp hk)]
    have hq := iota_eps N A i hw.2.1 hBw hσ
    have hinv : iotaO N A i ((((eps N i σ) ^ k)⁻¹ : (N.O i)ˣ) : N.O i) =
        ((normV w : ℕ) : ℂ) ^ (((-(k : ℝ) : ℝ)) : ℂ) := by
      rw [Complex.ofReal_neg, Complex.cpow_neg, Complex.ofReal_natCast, Complex.cpow_natCast, ← hq,
        map_units_inv, Units.val_pow_eq_pow_val, map_pow]
    rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, Units.val_mul, map_mul, hinv]
  have hne : (∏ c ∈ Finset.Icc 1 R.t,
        (X - C ((N.chi i c σ : (N.O i)ˣ) : N.O i)).map (iotaO N A i)) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr fun c _ => ?_
    rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
    exact X_sub_C_ne_zero _
  rw [← e5] at e1
  have := mul_right_cancel₀ hne e1
  simpa using this

theorem part_alg (hη : EtaType N A) (hW : WeightRegular N A) (i : N.Loc) (P : A.AV i)
    (Pa : List (Part A.CG)) (hB : IsBCV N A i P Pa) (p : Part A.CG) (hp : p ∈ Pa) (ha : Odd p.a)
    (hd : Odd p.d) : A.csd (A.tw p.π A.etaT) ∧ A.ralg (A.tw p.π A.etaT) := by
  refine ⟨A.csd_tw _ _ hη.1 (hB.1 p hp).2.2, (A.ralg_def _).2 fun τ => ?_⟩
  obtain ⟨s, hs⟩ := Multiset.card_eq_one.mp (A.infG_card A.etaT τ)
  obtain ⟨k0, hk0⟩ := hη.2 τ s (by rw [hs]; exact Multiset.mem_singleton_self s)
  have hle : (A.infG p.π τ).map (· + (((p.d : ℂ) - 1) / 2 - ((0 : ℕ) : ℂ))) ≤ A.infWt i τ := by
    rw [← hB.2.2.2.2.2 τ]
    unfold isoInf
    refine le_trans ?_ (List.single_le_sum (fun _ _ => Multiset.zero_le _) _ (List.mem_map_of_mem hp))
    refine List.single_le_sum (fun _ _ => Multiset.zero_le _) _
      (List.mem_map_of_mem (f := fun k : ℂ => (A.infG p.π τ).map (· + (((p.d : ℂ) - 1) / 2 - k))) ?_)
    rw [list_coe]
    exact List.mem_map_of_mem (List.mem_range.mpr hd.pos)
  rw [A.infG_tw _ _ τ s hs]
  refine ⟨(Multiset.Nodup.of_map _ (Multiset.nodup_of_le hle (hW i P τ).1)).map (add_left_injective s), ?_⟩
  intro z hz
  obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.mp hz
  obtain ⟨k, hk⟩ := (hW i P τ).2 _ (Multiset.mem_of_le hle (Multiset.mem_map_of_mem _ hy))
  obtain ⟨a, ha⟩ := ha
  obtain ⟨d, hd⟩ := hd
  obtain ⟨r, hr⟩ := r_odd R
  obtain ⟨t, ht⟩ := R.t_odd
  refine ⟨k + k0 + r + t + 1 - d - a, ?_⟩
  rw [Ranks.nV, hr, ht, hd] at hk
  rw [hk0, ha]
  push_cast at hk ⊢
  linear_combination hk

theorem not_subOrQuot (eig : Eig N A) (hT : GlobalTheory.IndefiniteRowSideFullHecke.TemperedRepresentations.Tempered N A) (hLG : LocalGlobal N A)
    (hL : EigLaws N A eig) (hA : EigAway N A eig) (hAb : EigAbove N A eig) (hS : TemperedSizes N A eig)
    (hη : EtaType N A) (hW : WeightRegular N A) (i : N.Loc) (x : N.X i) (π : A.CG R.r)
    (hx : HasParamX N A i x [⟨R.r, π, 1⟩]) (ρ : G H.E N.Om →* GL (Fin R.r) (N.O i))
    (hρ : IsRankPart N i x ρ) (w : PlE H) (j : ℕ) :
    ¬ SubOrQuot N i ρ (N.chi i 1 * eps N i ^ j) w := by
  intro hs
  obtain ⟨P, hP, hB⟩ := hx
  obtain ⟨σ, hσ⟩ : ∃ σ, FrobLift N w σ := exists_isFrob (N.plOm.2 w)
  obtain ⟨r, hr⟩ := r_odd R
  obtain ⟨t, ht⟩ := R.t_odd
  have hrt := r_add_le R
  have a1 := part_alg N A hη hW i P _ hB ⟨R.r, A.tw π A.etaTinv, 1⟩ (by simp [twistIso]) (r_odd R) odd_one
  have a2 := part_alg N A hη hW i P _ hB ⟨1, A.tw (A.muC i) A.etaTinv, R.t⟩ (by simp [twistIso, muPart])
    odd_one R.t_odd

  have x1 : (1 - (R.nV : ℝ)) / 2 = -(R.t : ℝ) / 2 + (1 - (R.r : ℝ)) / 2 := by
    rw [Ranks.nV]; push_cast; ring
  have l1 := hLG i R.r (r_odd R).pos (A.tw π A.etaTinv) A.etaT (-(R.t : ℝ) / 2) a1.1 a1.2
    (fun τ z hz => by
      obtain ⟨k, hk⟩ := hη.2 τ z hz
      refine ⟨-t - 1 - k, ?_⟩
      rw [hk, ht]; push_cast; ring)
    ρ hρ.1 hρ.2.1 (x1 ▸ matches_rho N A i x π P hP hB ρ hρ) w

  have hc : Cont N i (charRep N i (N.chi i 1 * eps N i ^ j)) := by
    refine charRep_cont N i _ ?_
    refine ((N.chi_cont i 1).mul ((eps_cont N i).pow j)).congr fun g => ?_
    simp
  have x2 : ((R.t : ℝ) - 1) / 2 + (1 - (R.nV : ℝ)) / 2 + j =
      (-(R.r : ℝ) / 2 + j) + (1 - ((1 : ℕ) : ℝ)) / 2 := by
    rw [Ranks.nV]; push_cast; ring
  have l2 := hLG i 1 le_rfl (A.tw (A.muC i) A.etaTinv) A.etaT (-(R.r : ℝ) / 2 + j) a2.1 a2.2
    (fun τ z hz => by
      obtain ⟨k, hk⟩ := hη.2 τ z hz
      refine ⟨-r - 1 - k + j, ?_⟩
      rw [hk, hr]; push_cast; ring)
    _ hc (charRep_ss N i _) (x2 ▸ matches_chi N A i j) w
  obtain ⟨c1, c2, c3⟩ := hL w σ hσ
  obtain ⟨m, hm⟩ := Multiset.card_eq_one.mp
    ((c1 (A.locG (A.tw (A.muC i) A.etaTinv) w)).trans (A.locG_dim _ w))
  obtain ⟨c, hcc⟩ := Multiset.card_eq_one.mp ((c1 (A.locG A.etaT w)).trans (A.locG_dim _ w))
  have hmem := eig_mem N A eig hA hAb i ρ _ hρ.1 hc w l1.2 l2.2 hs σ hσ _
    (by rw [l2.1, c2, hm, Multiset.map_singleton])
  rw [l1.1, c2] at hmem
  obtain ⟨α, hα, he⟩ := Multiset.mem_map.mp hmem

  have s1 := (hS w σ hσ _ (hT _ (r_odd R).pos _ a1.1 a1.2 w) (α * c) (by
    rw [A.locG_tw, c3 _ _ c (A.locG_dim _ w) hcc]
    exact Multiset.mem_map_of_mem _ hα)).2
  have s2 := (hS w σ hσ _ (hT _ le_rfl _ a2.1 a2.2 w) (m * c) (by
    rw [A.locG_tw, c3 _ _ c (A.locG_dim _ w) hcc, hm]
    simp)).1
  rw [A.locG_dim] at s1 s2
  have hq := one_lt_normV w
  have hq0 : (0 : ℝ) < ((normV w : ℕ) : ℝ) := lt_trans one_pos hq
  have s2' : 1 ≤ ‖m * c‖ := by simpa using s2
  have hn : ‖α * c‖ * ((normV w : ℕ) : ℝ) ^ (-(R.t : ℝ) / 2 + (1 - (R.r : ℝ)) / 2) =
      ‖m * c‖ * ((normV w : ℕ) : ℝ) ^ ((-(R.r : ℝ) / 2 + j) + (1 - ((1 : ℕ) : ℝ)) / 2) := by
    rw [← norm_cpow w, ← norm_cpow w, ← norm_mul, ← norm_mul]
    congr 1
    linear_combination c * he
  have hle : ((normV w : ℕ) : ℝ) ^ ((-(R.r : ℝ) / 2 + j) + (1 - ((1 : ℕ) : ℝ)) / 2) ≤
      ((normV w : ℕ) : ℝ) ^ (((R.r : ℝ) - 1) / 2 + (-(R.t : ℝ) / 2 + (1 - (R.r : ℝ)) / 2)) := by
    rw [Real.rpow_add hq0 (((R.r : ℝ) - 1) / 2)]
    calc _ ≤ ‖m * c‖ * ((normV w : ℕ) : ℝ) ^ ((-(R.r : ℝ) / 2 + j) + (1 - ((1 : ℕ) : ℝ)) / 2) :=
          le_mul_of_one_le_left (Real.rpow_nonneg hq0.le _) s2'
      _ = _ := hn.symm
      _ ≤ _ := mul_le_mul_of_nonneg_right s1 (Real.rpow_nonneg hq0.le _)
  rw [Real.rpow_le_rpow_left_iff hq] at hle
  have h1 : (R.r : ℝ) + 5 ≤ R.t := by exact_mod_cast hrt
  have h2 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  push_cast at hle
  linarith

theorem matK_eq (i : N.Loc) (ρ : G H.E N.Om →* GL (Fin R.r) (N.O i)) (g : G H.E N.Om) :
    matK N i ρ g = algebraMap (N.O i) (Kf N i) ((N.chi i 1 g : (N.O i)ˣ) : N.O i) • matW N i ρ g := by
  ext a b
  simp only [matK, matW, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul]
  rw [← map_mul, ← mul_assoc, Units.mul_inv, one_mul]

end GlobalTheory.LocalInv
