import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.UsedLocalConclusion
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NotFullBot
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ProdGammaSubJumpUnitsAnnihilatesQuotient
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConvXPowMul
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemWachNIffExpansion
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachNInvQPowGammaStable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineLatticeHodgeTateJumpsFinite
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCrystallineLetterOfHodgeJump
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowerSeriesTwistedScalingTriangularLaurent
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachInclusionXQFrobenius
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLatticeEqFiltrationSumAtLevel
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedSubfieldLeCyclotomicExt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachExpansionBasisDivisibility
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachExpansionsSpanFullLattice

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

namespace GlobalTheory.NL.IntegralScalarUnits

def GoodP {L M : Type} [Field L] [AddCommGroup M] [Module L M] (Sub : ℤ → Submodule L M) (y : ℕ)
    (k : ℤ) (d : M) (f : ℤ → M) (lam : L) : Prop :=
  (∃ m : ℤ, ∀ j < m, f j = 0) ∧ (∀ j, f j ∈ Sub j) ∧ (∀ j < k, f j ∈ Sub (j - y)) ∧
    f k - lam • d ∈ Sub (k - y)

theorem goodP_conv_sub_smul {L M : Type} [Field L] [TopologicalSpace L] [AddCommGroup M] [Module L M]
    (w : PowerSeries L) (u : L) (Sub : ℤ → Submodule L M) (hS : Monotone Sub) (y : ℕ) (k : ℤ)
    (d : M) (f : ℤ → M) (lam c' : L) (hf : GoodP Sub y k d f lam) :
    GoodP Sub y k d (conv w (fun m => u ^ m • f m) - c' • f)
      ((PowerSeries.constantCoeff w * u ^ k - c') * lam) := by
  obtain ⟨hb, h1, h2, h3⟩ := hf
  obtain ⟨t1, t2, t3, t4⟩ := GlobalTheory.NL.Twist.tri w u Sub hS y f hb h1 k h2
  obtain ⟨m1, hm1⟩ := t1
  obtain ⟨m2, hm2⟩ := hb
  refine ⟨⟨min m1 m2, fun j hj => ?_⟩, fun j => ?_, fun j hj => ?_, ?_⟩
  · simp only [Pi.sub_apply, Pi.smul_apply]
    rw [hm1 j (lt_of_lt_of_le hj (min_le_left _ _)), hm2 j (lt_of_lt_of_le hj (min_le_right _ _)),
      smul_zero, sub_zero]
  · exact Submodule.sub_mem _ (t2 j) (Submodule.smul_mem _ _ (h1 j))
  · exact Submodule.sub_mem _ (t3 j hj) (Submodule.smul_mem _ _ (h2 j hj))
  · have e : (conv w (fun m => u ^ m • f m) - c' • f) k -
        ((PowerSeries.constantCoeff w * u ^ k - c') * lam) • d =
        (conv w (fun m => u ^ m • f m) k - (PowerSeries.constantCoeff w * u ^ k) • f k) +
          (PowerSeries.constantCoeff w * u ^ k - c') • (f k - lam • d) := by
      simp only [Pi.sub_apply, Pi.smul_apply]
      module
    rw [e]
    exact Submodule.add_mem _ t4 (Submodule.smul_mem _ _ h3)

theorem algebraMap_units_zpow {O LL : Type} [CommRing O] [Field LL] [Algebra O LL] (v : Oˣ) (m : ℤ) :
    algebraMap O LL ((v ^ m : Oˣ) : O) = (algebraMap O LL (v : O)) ^ m := by
  have e := map_zpow (Units.map (algebraMap O LL : O →* LL)) v m
  calc algebraMap O LL ((v ^ m : Oˣ) : O)
      = ((Units.map (algebraMap O LL : O →* LL) (v ^ m) : LLˣ) : LL) := rfl
    _ = (((Units.map (algebraMap O LL : O →* LL) v) ^ m : LLˣ) : LL) := by rw [e]
    _ = (algebraMap O LL (v : O)) ^ m := by rw [Units.val_zpow_eq_zpow_val]; rfl

theorem algebraMap_units_ne_zero {O LL : Type} [CommRing O] [Field LL] [Algebra O LL] (v : Oˣ) :
    algebraMap O LL (v : O) ≠ 0 :=
  (Units.map (algebraMap O LL : O →* LL) v).ne_zero

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in

theorem ex_smul_O (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) (T : Lt K LL)
    (hT : IsCrys ((D.loc l).PD K) T.ρ) (i : Let K) (ζ : ↥LL.1) (hprim : IsPrimitiveRoot ζ (l ^ s))
    (c' : ↥(OL LL)) (x : ↥(((HW l).W K s LL h).N T)) :
    ex (Cm l) h T i ζ (c' • x) = algebraMap ↥(OL LL) ↥LL.1 c' • ex (Cm l) h T i ζ x := by
  have hfull := GlobalTheory.NL.FullLevel.full_lat D HW F Cm l K s LL h T hT i ζ hprim
  have hlin := (GlobalTheory.NL.LevInj.expansion_basis D HW F Cm l K s LL h T hT i ζ ⟨s, hprim⟩ hfull).1
  have hx : c' • x = (c' • (1 : AA K LL)) • x := by rw [smul_assoc, one_smul]
  rw [hx, hlin]
  have key : ∀ q : ℕ, PowerSeries.coeff q (((HW l).W K s LL h).lev i ζ (c' • (1 : AA K LL))) =
      if q = 0 then algebraMap ↥(OL LL) ↥LL.1 c' else 0 := by
    intro q
    rw [map_smul, map_one]
    rcases q with _ | q
    · simp [Algebra.algebraMap_eq_smul_one]
    · simp
  funext m
  simp only [conv, Pi.smul_apply]
  rw [finsum_eq_single _ 0]
  · rw [key]; simp
  · intro q hq
    rw [key, if_neg hq, zero_smul]

theorem goodP_prod {O L M X : Type} [CommRing O] [Field L] [TopologicalSpace L] [Algebra O L]
    [AddCommGroup M] [Module L M] [AddCommGroup X] [Module O X]
    (γ : X →ₗ[O] X) (P : Submodule O X) (hP : ∀ x ∈ P, γ x ∈ P) (E : X → ℤ → M)
    (w : PowerSeries L) (u : L)
    (hE : ∀ x ∈ P, ∀ c : O, E (γ x - c • x) = conv w (fun m => u ^ m • E x m) - algebraMap O L c • E x)
    (Sub : ℤ → Submodule L M) (hS : Monotone Sub) (y : ℕ) (k : ℤ) (d : M) (x₀ : X) (hx₀ : x₀ ∈ P)
    (lam₀ : L) (h₀ : GoodP Sub y k d (E x₀) lam₀) (S : Finset Oˣ) :
    Polynomial.aeval γ (∏ c ∈ S, ((Polynomial.X : Polynomial O) - Polynomial.C (c : O))) x₀ ∈ P ∧
    GoodP Sub y k d (E (Polynomial.aeval γ (∏ c ∈ S, ((Polynomial.X : Polynomial O) - Polynomial.C (c : O))) x₀))
      (lam₀ * ∏ c ∈ S, (PowerSeries.constantCoeff w * u ^ k - algebraMap O L (c : O))) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using ⟨hx₀, h₀⟩
  | insert c S hc ih =>
    obtain ⟨hm, hg⟩ := ih
    have e : Polynomial.aeval γ (∏ c' ∈ insert c S, ((Polynomial.X : Polynomial O) - Polynomial.C (c' : O))) x₀ =
        γ (Polynomial.aeval γ (∏ c' ∈ S, ((Polynomial.X : Polynomial O) - Polynomial.C (c' : O))) x₀) -
          (c : O) • Polynomial.aeval γ (∏ c' ∈ S, ((Polynomial.X : Polynomial O) - Polynomial.C (c' : O))) x₀ := by
      rw [Finset.prod_insert hc, map_mul, Module.End.mul_apply]
      simp only [map_sub, Polynomial.aeval_X, Polynomial.aeval_C, LinearMap.sub_apply,
        Module.algebraMap_end_apply]
    rw [e, Finset.prod_insert hc, mul_left_comm, hE _ hm]
    exact ⟨P.sub_mem (hP _ hm) (P.smul_mem _ hm), goodP_conv_sub_smul w u Sub hS y k d _ _ _ hg⟩

theorem ex_sub {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} {H : LocHW l P} {F : LocFon l P AI H}
    {K : FinExt l} {s : ℕ} {LL : FinExt l} (C : LocCmpT l P AI H F) (h : Good K s LL) (T : Lt K LL)
    (i : Let K) (ζ : ↥LL.1) (x x' : ↥((H.W K s LL h).N T)) :
    ex C h T i ζ (x - x') = ex C h T i ζ x - ex C h T i ζ x' :=
  ((C.C K s LL h).tie.levB T i ζ).map_sub x x'

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 20000000 in

theorem occ : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → ∀ y : ℕ, 1 ≤ y → ∀ a ∈ Jumps (PD := (D.loc l).PD K) T, ∀ j : ℕ, 1 ≤ j → j ≤ y → ∃ x ∈ invN W T (W.Q ^ y), x ∉ W.N T ∧ W.γ T x - (((uU W ^ (-(a + j)) : (↥(OL LL))ˣ) : ↥(OL LL))) • x ∈ W.N T := by
  intro D HW F Cm l _ K s LL h W T hT y hy a ha j hj1 hjy
  classical
  obtain ⟨τ, hτ⟩ := ha
  have hpts := GlobalTheory.NL.Points.points D HW l K s LL h
  obtain ⟨i, ζ, hPt⟩ := hpts.2.2.1 τ
  have hprim : IsPrimitiveRoot ζ (l ^ s) := (hpts.2.1 i ζ τ hPt).1
  obtain ⟨d, hdD, hdA, hdA1⟩ := GlobalTheory.NL.JumpVec.exists_letter_of_jump D HW l K s LL h T hT i ζ τ hPt a hτ
  have hQ := ((GlobalTheory.NL.IoXQ.main D HW F l K s LL h).2.2.2.2.2.2 0).2
  simp only [pow_zero, AlgHom.one_apply] at hQ
  have hJ := GlobalTheory.NL.JumpsFinite.jumps_finite D HW l K s LL h T hT
  let Fs : Finset (↥(OL LL))ˣ := (hJ.toFinset ×ˢ Finset.Icc 1 y).image
    (fun p : ℤ × ℕ => uU W ^ (-(p.1 + (p.2 : ℤ))))
  have hFs : ∀ a' ∈ Jumps (PD := (D.loc l).PD K) T, ∀ j' : ℕ, 1 ≤ j' → j' ≤ y → uU W ^ (-(a' + j')) ∈ Fs := by
    intro a' ha' j' h1 h2
    simp only [Fs, Finset.mem_image, Finset.mem_product, Set.Finite.mem_toFinset, Finset.mem_Icc, Prod.exists]
    exact ⟨a', j', ⟨ha', h1, h2⟩, rfl⟩
  have hmemInv : ∀ x : W.DD T, x ∈ invN W T (W.Q ^ y) ↔ W.Q ^ y • x ∈ W.N T := by
    intro x
    simp [invN, smulA]
  have hγst := (GlobalTheory.NL.GamQ.gam_Q_pow D HW F Cm l K s LL h T hT y).1
  have hstab : ∀ (S : Finset (↥(OL LL))ˣ) (x : W.DD T), x ∈ invN W T (W.Q ^ y) →
      Polynomial.aeval (W.γ T) (∏ c ∈ S, ((Polynomial.X : Polynomial ↥(OL LL)) - Polynomial.C (Units.val c))) x
        ∈ invN W T (W.Q ^ y) := by
    intro S
    induction S using Finset.induction_on with
    | empty => intro x hx; simpa using hx
    | insert c S hc ih =>
      intro x hx
      rw [Finset.prod_insert hc, map_mul, Module.End.mul_apply]
      have h1 := ih x hx
      set v := Polynomial.aeval (W.γ T) (∏ c ∈ S, ((Polynomial.X : Polynomial ↥(OL LL)) - Polynomial.C (Units.val c))) x
      simp only [map_sub, Polynomial.aeval_X, Polynomial.aeval_C, LinearMap.sub_apply, Module.algebraMap_end_apply]
      refine Submodule.sub_mem _ ?_ (Submodule.smul_of_tower_mem _ _ h1)
      exact (hmemInv _).2 (hγst v ((hmemInv v).1 h1))
  have hFA : ∀ b : ℤ, FilAt ((D.loc l).PD K) T τ (b + 1) ≤ FilAt ((D.loc l).PD K) T τ b := by
    intro b
    apply sup_le_sup_right
    apply inf_le_inf_left
    rintro _ ⟨x, rfl⟩
    have hle : (((D.loc l).PD K).Fil (b + 1)).restrictScalars ℚ_[l] ≤
        (((D.loc l).PD K).Fil b).restrictScalars ℚ_[l] := ((D.loc l).PD K).Fil_anti b
    refine ⟨AlgebraTensorModule.map (LinearMap.id : T.V →ₗ[↥LL.1] T.V) (Submodule.inclusion hle) x, ?_⟩
    rw [← LinearMap.comp_apply, ← AlgebraTensorModule.map_comp]
    rfl
  have hFAnti : Antitone (FilAt ((D.loc l).PD K) T τ) := antitone_int_of_succ_le hFA
  obtain ⟨k, hk⟩ : ∃ k : ℤ, k = (y : ℤ) - a - j := ⟨_, rfl⟩
  obtain ⟨g, hgdef⟩ : ∃ g : ℤ → T.V ⊗[ℚ_[l]] (D.loc l).R.B, g = Pi.single k d := ⟨_, rfl⟩
  have hlat := GlobalTheory.NL.LatFil.lat_eq_fil D HW F Cm l K s LL h T hT i ζ τ hPt
  have hg : g ∈ Lat (Cm l) h T i ζ := by
    refine (hlat g).2 ⟨⟨k, fun j' hj' => by rw [hgdef]; exact Pi.single_eq_of_ne hj'.ne _⟩, fun j' => ?_⟩
    by_cases hj' : j' = k
    · rw [hj', hgdef, Pi.single_eq_same]
      exact ⟨hdD, hFAnti (show -k ≤ a by omega) hdA⟩
    · simp only [hgdef, Pi.single_eq_of_ne hj', map_zero]
      exact ⟨Submodule.zero_mem _, Submodule.zero_mem _⟩
  obtain ⟨n, c, hc, f, hf, hfe⟩ := GlobalTheory.NL.Approx.approx D HW F Cm l K s LL h T hT i ζ hprim g hg y
  obtain ⟨e, he⟩ : ∃ e : W.EE, algebraMap (AA K LL) W.EE (W.Q ^ y) * e = 1 := by
    rw [map_pow]; exact (hQ.pow y).exists_right_inv
  obtain ⟨x₀, hx₀def⟩ : ∃ x₀ : W.DD T, x₀ = e • (n : W.DD T) := ⟨_, rfl⟩
  have hx₀Q : W.Q ^ y • x₀ = (n : W.DD T) := by
    rw [hx₀def, ← smul_assoc, Algebra.smul_def, he, one_smul]
  have hx₀ : x₀ ∈ invN W T (W.Q ^ y) := by rw [hmemInv, hx₀Q]; exact n.2
  have hc₀ : uU W ^ (-(a + j)) ∈ Fs := hFs a ⟨τ, hτ⟩ j hj1 hjy
  obtain ⟨z, hzdef⟩ : ∃ z, z = Polynomial.aeval (W.γ T) (∏ c ∈ Fs.erase (uU W ^ (-(a + j))), ((Polynomial.X : Polynomial ↥(OL LL)) - Polynomial.C (Units.val c))) x₀ := ⟨_, rfl⟩
  have hz : z ∈ invN W T (W.Q ^ y) := hzdef ▸ hstab _ x₀ hx₀
  refine ⟨z, hz, ?_, ?_⟩
  swap
  · have := GlobalTheory.NL.KillLevels.annihilate D HW F Cm l K s LL h T hT y hy Fs hFs x₀ hx₀
    rw [← Finset.mul_prod_erase Fs _ hc₀, map_mul, Module.End.mul_apply, ← hzdef] at this
    simpa only [map_sub, Polynomial.aeval_X, Polynomial.aeval_C, LinearMap.sub_apply,
      Module.algebraMap_end_apply] using this
  intro hzN
  have hzQ : W.Q ^ y • z ∈ W.N T := (hmemInv _).1 hz
  obtain ⟨w, hw0, hwE⟩ := (GlobalTheory.NL.GamQ.gam_Q_pow D HW F Cm l K s LL h T hT y).2 i ζ hprim
  have hexsmul := ex_smul_O D HW F Cm l K s LL h T hT i ζ hprim
  obtain ⟨Sub, hSub⟩ : ∃ Sub : ℤ → Submodule ↥LL.1 (T.V ⊗[ℚ_[l]] (D.loc l).R.B),
      Sub = fun m => Di (HW l) h T i ⊓
        (FilAt ((D.loc l).PD K) T τ (-m)).comap (ιV ((D.loc l).PD K) (LL := ↥LL.1) (V := T.V)) := ⟨_, rfl⟩
  have hSubMono : Monotone Sub := by
    intro m m' hmm
    rw [hSub]
    exact inf_le_inf_left _ (Submodule.comap_mono (hFAnti (neg_le_neg hmm)))
  have hLatSub : ∀ f ∈ Lat (Cm l) h T i ζ, (∃ m : ℤ, ∀ j < m, f j = 0) ∧ ∀ j, f j ∈ Sub j := by
    intro f hf
    obtain ⟨hb, hj⟩ := (hlat f).1 hf
    refine ⟨hb, fun j => ?_⟩
    rw [hSub]
    exact ⟨(hj j).1, (hj j).2⟩
  have hn := hLatSub _ (Submodule.subset_span ⟨1, n, (GlobalTheory.NL.LatFil.conv_one _).symm⟩)
  have hfS := hLatSub f hf
  have hbase_below : ∀ j' < k, ex (Cm l) h T i ζ n j' ∈ Sub (j' - y) := by
    intro j' hj'
    have e := hfe j'
    rw [hgdef, Pi.single_eq_of_ne hj'.ne, smul_zero, sub_zero] at e
    rw [e]
    exact hfS.2 _
  have hbase_k : ex (Cm l) h T i ζ n k - c • d ∈ Sub (k - y) := by
    have e := hfe k
    rw [hgdef, Pi.single_eq_same] at e
    rw [e]
    exact hfS.2 _
  obtain ⟨E, hEdef⟩ : ∃ E : W.DD T → ℤ → T.V ⊗[ℚ_[l]] (D.loc l).R.B,
      E = fun x => if hx : W.Q ^ y • x ∈ W.N T then ex (Cm l) h T i ζ ⟨_, hx⟩ else 0 := ⟨_, rfl⟩
  have hEval : ∀ (x : W.DD T) (hx : W.Q ^ y • x ∈ W.N T), E x = ex (Cm l) h T i ζ ⟨_, hx⟩ := by
    intro x hx
    rw [hEdef]
    exact dif_pos hx
  have hE : ∀ x ∈ (invN W T (W.Q ^ y)).restrictScalars ↥(OL LL), ∀ c' : ↥(OL LL),
      E (W.γ T x - c' • x) = conv w (fun m => (algebraMap ↥(OL LL) ↥LL.1 (W.χΓ W.gam : ↥(OL LL))) ^ m • E x m) -
        algebraMap ↥(OL LL) ↥LL.1 c' • E x := by
    intro x hx c'
    have hx' : W.Q ^ y • x ∈ W.N T := (hmemInv x).1 hx
    have hγ := hγst x hx'
    have h3 : W.Q ^ y • (W.γ T x - c' • x) ∈ W.N T :=
      (hmemInv _).1 (Submodule.sub_mem _ ((hmemInv _).2 hγ) (Submodule.smul_of_tower_mem _ c' hx))
    have e1 : (⟨_, h3⟩ : ↥(W.N T)) = ⟨_, hγ⟩ - c' • ⟨_, hx'⟩ := by
      apply Subtype.ext
      simp only [Submodule.coe_sub, Submodule.coe_smul_of_tower, smul_sub]
      rw [smul_comm]
    rw [hEval _ h3, hEval _ hx']
    refine (congrArg (ex (Cm l) h T i ζ) e1).trans ((ex_sub (Cm l) h T i ζ _ _).trans ?_)
    exact congrArg₂ (· - ·) (funext fun m => hwE _ hx' hγ m) (hexsmul c' ⟨_, hx'⟩)
  have hP : ∀ x ∈ (invN W T (W.Q ^ y)).restrictScalars ↥(OL LL), W.γ T x ∈ (invN W T (W.Q ^ y)).restrictScalars ↥(OL LL) :=
    fun x hx => (hmemInv _).2 (hγst x ((hmemInv x).1 hx))
  have hbase : GoodP Sub y k d (E x₀) c := by
    rw [hEval x₀ ((hmemInv _).1 hx₀)]
    have e : (⟨_, (hmemInv _).1 hx₀⟩ : ↥(W.N T)) = n := Subtype.ext hx₀Q
    rw [e]
    exact ⟨hn.1, hn.2, hbase_below, hbase_k⟩
  obtain ⟨-, hzG⟩ := goodP_prod (W.γ T) ((invN W T (W.Q ^ y)).restrictScalars ↥(OL LL)) hP E w
    (algebraMap ↥(OL LL) ↥LL.1 (W.χΓ W.gam : ↥(OL LL))) hE Sub hSubMono y k d x₀ hx₀ c hbase
    (Fs.erase (uU W ^ (-(a + j))))
  rw [← hzdef, hEval z hzQ] at hzG
  obtain ⟨f2, hf2, hf2e⟩ := (GlobalTheory.NL.WachModulePoleQuotient.mem_N_iff_expansion D HW F Cm l K s LL h T hT y z hzQ).1 hzN i ζ hprim
  have hkmem : ex (Cm l) h T i ζ ⟨_, hzQ⟩ k ∈ Sub (k - y) := by
    rw [hf2e k]
    exact (hLatSub f2 hf2).2 _
  have hune := algebraMap_units_ne_zero (O := ↥(OL LL)) (LL := ↥LL.1) (W.χΓ W.gam)
  have hu0 : PowerSeries.constantCoeff w * (algebraMap ↥(OL LL) ↥LL.1 (W.χΓ W.gam : ↥(OL LL))) ^ k =
      algebraMap ↥(OL LL) ↥LL.1 ((uU W ^ (-(a + j)) : (↥(OL LL))ˣ) : ↥(OL LL)) := by
    rw [hw0, algebraMap_units_zpow, ← zpow_add₀ hune]
    show _ = (algebraMap ↥(OL LL) ↥LL.1 (W.χΓ W.gam : ↥(OL LL))) ^ (-(a + (j : ℤ)))
    congr 1
    omega
  have hlam : (c * ∏ c' ∈ Fs.erase (uU W ^ (-(a + j))), (PowerSeries.constantCoeff w *
          (algebraMap ↥(OL LL) ↥LL.1 (W.χΓ W.gam : ↥(OL LL))) ^ k -
          algebraMap ↥(OL LL) ↥LL.1 (c' : ↥(OL LL)))) ≠ 0 := by
    refine mul_ne_zero hc (Finset.prod_ne_zero_iff.2 fun c' hc' => ?_)
    rw [hu0, sub_ne_zero]
    intro he
    exact (Finset.ne_of_mem_erase hc') (Units.ext (Subtype.val_injective he)).symm
  have hlamd := Submodule.sub_mem _ hkmem hzG.2.2.2
  rw [sub_sub_cancel] at hlamd
  have hdS := Submodule.smul_mem _ (c * ∏ c' ∈ Fs.erase (uU W ^ (-(a + j))), (PowerSeries.constantCoeff w *
          (algebraMap ↥(OL LL) ↥LL.1 (W.χΓ W.gam : ↥(OL LL))) ^ k -
          algebraMap ↥(OL LL) ↥LL.1 (c' : ↥(OL LL))))⁻¹ hlamd
  rw [inv_smul_smul₀ hlam, hSub] at hdS
  exact hdA1 (hFAnti (show a + 1 ≤ -(k - (y : ℤ)) by omega) (Submodule.mem_inf.1 hdS).2)

end GlobalTheory.NL.IntegralScalarUnits
