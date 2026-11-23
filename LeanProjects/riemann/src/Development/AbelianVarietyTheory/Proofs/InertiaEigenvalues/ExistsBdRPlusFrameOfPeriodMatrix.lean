import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AntitoneFiltrationExistsAdaptedLinearIndepSet
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamPeriodRingFieldTPowFiltrationUnitsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsThetaDeRhamFilZeroSurjectiveStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LinearIndependentCyclotomicEigenvectorsWeightsStatement

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.PMon.FrameOne

theorem adapted_basis_fin {L : Type} [Field L] {n : Type} [Fintype n] [DecidableEq n]
    (A : ℤ → Submodule L (n → L)) (hA : Antitone A) (hsep : ∀ x, (∀ a, x ∈ A a) → x = 0)
    (a0 : ℤ) (htop : A a0 = ⊤) :
    ∃ (d : n → n → L) (k : n → ℤ), LinearIndependent L d ∧
      ∀ a, A a = Submodule.span L (d '' {j | a ≤ k j}) := by
  obtain ⟨m, d, k, hli, hsp⟩ := GlobalTheory.filtration_adapted_basis A hA inferInstance hsep
  have hspan : ⊤ ≤ Submodule.span L (Set.range d) := by
    rw [← htop, hsp a0]
    exact Submodule.span_mono (Set.image_subset_range _ _)
  let b := Module.Basis.mk hli hspan
  have hcard : Fintype.card n = Fintype.card (Fin m) := by
    have h1 := Module.finrank_eq_card_basis b
    rw [Module.finrank_fintype_fun_eq_card] at h1
    exact h1
  let e : n ≃ Fin m := Fintype.equivOfCardEq hcard
  refine ⟨d ∘ e, k ∘ e, hli.comp e e.injective, fun a => ?_⟩
  rw [hsp a]
  congr 1
  ext x
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨e.symm i, by simpa using hi, by simp⟩
  · rintro ⟨j, hj, rfl⟩
    exact ⟨e j, hj, rfl⟩

end GlobalTheory.PMon.FrameOne

namespace GlobalTheory.PMon.FrameOne

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l)

theorem fil_zero (a : ℤ) : (0 : P.R.BdR) ∈ Fil P a := ((P.PD (botExt l)).Fil a).zero_mem

theorem fil_add {a : ℤ} {x y : P.R.BdR} (hx : x ∈ Fil P a) (hy : y ∈ Fil P a) : x + y ∈ Fil P a :=
  ((P.PD (botExt l)).Fil a).add_mem hx hy

theorem fil_sum {ι : Type} (s : Finset ι) {a : ℤ} (f : ι → P.R.BdR) (h : ∀ i ∈ s, f i ∈ Fil P a) :
    ∑ i ∈ s, f i ∈ Fil P a :=
  Submodule.sum_mem ((P.PD (botExt l)).Fil a) h

theorem fil_anti {a b : ℤ} (hab : a ≤ b) {x : P.R.BdR} (hx : x ∈ Fil P b) : x ∈ Fil P a := by
  induction b, hab using Int.le_induction with
  | base => exact hx
  | succ c _ ih => exact ih ((P.PD (botExt l)).Fil_anti c hx)

theorem fil_exh (x : P.R.BdR) : ∃ a, x ∈ Fil P a := (P.PD (botExt l)).Fil_exh x

theorem fil_sep (x : P.R.BdR) (h : ∀ a, x ∈ Fil P a) : x = 0 := (P.PD (botExt l)).Fil_sep x h

end GlobalTheory.PMon.FrameOne

namespace GlobalTheory.PMon.FrameOne

open Matrix

theorem frame_of_period_matrix : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (n : Type) [Fintype n] [DecidableEq n] (K : FinExt l) (A : ↥(GK K) → Matrix n n P.R.BdR) (Q : GL n P.R.BdR), (∀ g i j, A g i j ∈ Fil P 0) → (∀ g : ↥(GK K), A g * (Q : Matrix n n P.R.BdR).map (P.actQdR (g : GQ l)) = Q) → ∃ (U : GL n P.R.BdR) (w : n → ℤ), UnitM P U ∧ ∀ g : ↥(GK K), A g * (U : Matrix n n P.R.BdR).map (P.actQdR (g : GQ l)) = (U : Matrix n n P.R.BdR) * Matrix.diagonal fun j => algebraMap ℚ_[l] P.R.BdR ((P.χQ (g : GQ l) ^ w j : ℚ_[l]ˣ) : ℚ_[l]) := by
  intro l _ P AI T n _ _ K A Q hA0 hAQ
  obtain ⟨S, θ, hS, -, hθ0, hθOm, hθg⟩ := GlobalTheory.T.exists_theta_deRhamFilZero_surjective l P AI T
  obtain ⟨hfield, -, htz, hinv, -, hmul, -, htzact, -, -, -⟩ := GlobalTheory.T.deRhamPeriodRing_field_tPow_filtration_units l P AI T
  haveI : Nontrivial P.R.BdR := ⟨hfield.exists_pair_ne⟩
  set Q' : Matrix n n P.R.BdR := (Q : Matrix n n P.R.BdR) with hQ'
  let eK : ↥K.1 →+* P.R.BdR := (algebraMap (Om l) P.R.BdR).comp (K.1.val : ↥K.1 →+* Om l)
  have hE0 : ∀ c, eK c ∈ Fil P 0 := fun c => (hS _).1 (hθOm (c : Om l)).1
  have hEg : ∀ (g : ↥(GK K)) c, P.actQdR (g : GQ l) (eK c) = eK c := by
    intro g c
    show P.actQdR (g : GQ l) (algebraMap (Om l) P.R.BdR (c : Om l)) = algebraMap (Om l) P.R.BdR (c : Om l)
    rw [P.actQdR_Om, (IntermediateField.mem_fixingSubgroup_iff _ _).mp g.2 _ c.2]
  have hEinj : ∀ c, eK c = 0 → c = 0 := by
    intro c hc
    have : (c : Om l) = 0 := (map_eq_zero_iff _ (algebraMap (Om l) P.R.BdR).injective).1 hc
    exact Subtype.ext this
  have hEadd : ∀ c d, eK (c + d) = eK c + eK d := fun c d => map_add eK c d
  have hEmul : ∀ c d, eK (c * d) = eK c * eK d := fun c d => map_mul eK c d
  have hE00 : eK 0 = 0 := map_zero eK
  have hEsum : ∀ (f : n → ↥K.1), eK (∑ j, f j) = ∑ j, eK (f j) := fun f => map_sum eK f _
  let vec : (n → ↥K.1) → n → P.R.BdR := fun c => Q' *ᵥ fun j => eK (c j)
  let Af : ℤ → Submodule ↥K.1 (n → ↥K.1) := fun a =>
    { carrier := {c | ∀ i, vec c i ∈ Fil P a}
      add_mem' := by
        intro c d hc hd i
        have : vec (c + d) = vec c + vec d := by
          simp only [vec, Pi.add_apply, hEadd, ← Matrix.mulVec_add]; rfl
        rw [this]; exact fil_add P (hc i) (hd i)
      zero_mem' := by
        intro i
        have : vec 0 = 0 := by
          simp only [vec, Pi.zero_apply, hE00]; exact Matrix.mulVec_zero _
        rw [this]; exact fil_zero P a
      smul_mem' := by
        intro k c hc i
        have : vec (k • c) = eK k • vec c := by
          simp only [vec, Pi.smul_apply, smul_eq_mul, hEmul, ← Matrix.mulVec_smul]; rfl
        rw [this]
        simpa using hmul 0 a _ _ (hE0 k) (hc i) }

  have hAnti : Antitone Af := by
    intro a b hab c hc i
    exact fil_anti P hab (hc i)
  have hSep : ∀ c, (∀ a, c ∈ Af a) → c = 0 := by
    intro c hc
    have hv : vec c = 0 := funext fun i => fil_sep P _ fun a => hc a i
    have h2 : (fun j => eK (c j)) = 0 := by
      have h3 : ((Q⁻¹ : GL n P.R.BdR) : Matrix n n P.R.BdR) *ᵥ vec c = fun j => eK (c j) := by
        simp only [vec, Matrix.mulVec_mulVec, hQ']
        rw [← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
      rw [← h3, hv, Matrix.mulVec_zero]
    funext j
    exact hEinj _ (congrFun h2 j)
  choose f hf using fun p : n × n => fil_exh P (Q' p.1 p.2)
  let a0 : ℤ := -∑ p : n × n, |f p|
  have ha0 : ∀ p, a0 ≤ f p := by
    intro p
    have h1 : |f p| ≤ ∑ q : n × n, |f q| :=
      Finset.single_le_sum (f := fun q => |f q|) (fun q _ => abs_nonneg _) (Finset.mem_univ p)
    have h2 := neg_abs_le (f p)
    simp only [a0]; linarith
  have hTop : Af a0 = ⊤ := by
    rw [eq_top_iff]
    intro c _ i
    refine fil_sum P _ _ fun j _ => ?_
    have := hmul (f (i, j)) 0 _ _ (hf (i, j)) (hE0 (c j))
    rw [add_zero] at this
    exact fil_anti P (ha0 (i, j)) this
  obtain ⟨d, k, hli, hsp⟩ := adapted_basis_fin Af hAnti hSep a0 hTop
  have hdk : ∀ j i, vec (d j) i ∈ Fil P (k j) := by
    intro j
    have : d j ∈ Af (k j) := by
      rw [hsp]; exact Submodule.subset_span ⟨j, show k j ≤ k j from le_refl _, rfl⟩
    exact this
  let U0 : Matrix n n P.R.BdR := Matrix.of fun i j => tz P (-(k j)) * vec (d j) i
  have hU0 : ∀ i j, U0 i j ∈ Fil P 0 := by
    intro i j
    have := (htz (k j) (-(k j)) _).1 (hdk j i)
    rwa [add_neg_cancel] at this

  have hvg : ∀ (g : ↥(GK K)) j, (A g) *ᵥ (fun m => P.actQdR (g : GQ l) (vec (d j) m)) = vec (d j) := by
    intro g j
    have : (fun m => P.actQdR (g : GQ l) (vec (d j) m)) = (Q'.map (P.actQdR (g : GQ l))) *ᵥ (fun p => eK (d j p)) := by
      funext m
      simp only [vec, Matrix.mulVec, dotProduct, map_sum, map_mul, hEg, Matrix.map_apply]
    rw [this, Matrix.mulVec_mulVec, hAQ]
  have hEig : ∀ g : ↥(GK K), A g * U0.map (P.actQdR (g : GQ l)) = U0 * Matrix.diagonal fun j =>
      algebraMap ℚ_[l] P.R.BdR ((P.χQ (g : GQ l) ^ (-(k j)) : ℚ_[l]ˣ) : ℚ_[l]) := by
    intro g
    ext i j
    rw [Matrix.mul_diagonal, Matrix.mul_apply]
    have key : ∀ X : P.R.BdR, (∑ m, A g i m * (X * P.actQdR (g : GQ l) (vec (d j) m))) = X * vec (d j) i := by
      intro X
      rw [← congrFun (hvg g j) i, Matrix.mulVec, dotProduct, Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => by ring
    simp only [U0, Matrix.map_apply, Matrix.of_apply, map_mul, htzact]
    rw [key]; ring

  have hq : ∀ q : ℚ_[l], ∃ h : algebraMap ℚ_[l] P.R.BdR q ∈ S, θ ⟨_, h⟩ = algebraMap ℚ_[l] ℂ_[l] q := by
    intro q
    obtain ⟨h, hh⟩ := hθOm (algebraMap ℚ_[l] (Om l) q)
    have e : algebraMap ℚ_[l] P.R.BdR q = algebraMap (Om l) P.R.BdR (algebraMap ℚ_[l] (Om l) q) :=
      IsScalarTower.algebraMap_apply ℚ_[l] (Om l) P.R.BdR q
    refine ⟨e ▸ h, ?_⟩
    have e2 : (⟨algebraMap ℚ_[l] P.R.BdR q, e ▸ h⟩ : ↥S) = ⟨_, h⟩ := Subtype.ext e
    rw [e2, hh]
    show algebraMap (PadicAlgCl l) ℂ_[l] (algebraMap ℚ_[l] (PadicAlgCl l) q) = _
    exact (IsScalarTower.algebraMap_apply ℚ_[l] (PadicAlgCl l) ℂ_[l] q).symm
  let U0S : Matrix n n ↥S := Matrix.of fun i j => ⟨U0 i j, (hS _).2 (hU0 i j)⟩
  let M : Matrix n n ℂ_[l] := U0S.map θ
  have hgS : ∀ (g : GQ l) i j, P.actQdR g (U0 i j) ∈ S := fun g i j => (hθg g (U0S i j)).1
  let Aθ : ↥(GK K) → Matrix n n ℂ_[l] := fun g =>
    (Matrix.of fun i j => (⟨A g i j, (hS _).2 (hA0 g i j)⟩ : ↥S)).map θ
  have hc1 : ∀ (g : ↥(GK K)) (j : n), (Aθ g) *ᵥ (fun i => Formalism.Per.σC (g : GQ l) (M i j)) =
      algebraMap ℚ_[l] ℂ_[l] ((P.χQ (g : GQ l) ^ (-(k j)) : ℚ_[l]ˣ) : ℚ_[l]) • (fun i => M i j) := by
    intro g j
    funext i
    obtain ⟨hc, hcθ⟩ := hq ((P.χQ (g : GQ l) ^ (-(k j)) : ℚ_[l]ˣ) : ℚ_[l])
    have hE := congrFun (congrFun (hEig g) i) j
    rw [Matrix.mul_apply, Matrix.mul_diagonal] at hE
    have hsum : (∑ m, (⟨A g i m, (hS _).2 (hA0 g i m)⟩ : ↥S) * ⟨P.actQdR (g : GQ l) (U0 m j), hgS g m j⟩) =
        U0S i j * ⟨_, hc⟩ := by
      apply Subtype.ext
      simpa [U0S] using hE
    have h3 := congrArg θ hsum
    rw [map_sum, map_mul, hcθ] at h3
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, Aθ, M, Matrix.map_apply, Matrix.of_apply]
    rw [mul_comm, ← h3]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [map_mul]
    congr 1
    exact ((hθg _ (U0S m j)).2).symm
  have hvecx : ∀ (c' : n → ↥K.1) i, vec (∑ j, c' j • d j) i = ∑ j, eK (c' j) * vec (d j) i := by
    intro c' i
    simp only [vec, Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hEsum, hEmul]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have hc2 : ∀ (a : ℤ) (c : n → Om l), (∀ j, c j ∈ K.1) → (∀ j, -(k j) ≠ a → c j = 0) →
      ∑ j, (c j : ℂ_[l]) • (fun i => M i j) = 0 → c = 0 := by
    intro a c hcK hcw hsum
    let c' : n → ↥K.1 := fun j => ⟨c j, hcK j⟩
    have hc'0 : ∀ j, -(k j) ≠ a → c' j = 0 := fun j hj => Subtype.ext (hcw j hj)
    have hmemc : ∀ j, eK (c' j) ∈ S := fun j => (hθOm (c j)).1
    have hθc : ∀ j, θ ⟨eK (c' j), hmemc j⟩ = (c j : ℂ_[l]) := fun j => (hθOm (c j)).2
    have hx1 : ∀ i, tz P a * vec (∑ j, c' j • d j) i ∈ Fil P 1 := by
      intro i
      have hi := congrFun hsum i
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hi
      have h0 : θ (∑ j, (⟨eK (c' j), hmemc j⟩ : ↥S) * U0S i j) = 0 := by
        rw [map_sum]
        simp only [map_mul, hθc]
        simpa [M] using hi
      have h1 := (hθ0 _).1 h0
      have h2 : ((∑ j, (⟨eK (c' j), hmemc j⟩ : ↥S) * U0S i j : ↥S) : P.R.BdR) =
          tz P a * vec (∑ j, c' j • d j) i := by
        rw [hvecx, Finset.mul_sum]
        simp only [AddSubmonoidClass.coe_finset_sum, MulMemClass.coe_mul, U0S, U0, Matrix.of_apply]
        refine Finset.sum_congr rfl fun j _ => ?_
        by_cases hj : -(k j) = a
        · rw [hj]; ring
        · rw [hc'0 j hj, hE00]; ring
      rw [← h2]; exact h1
    have hxA : (∑ j, c' j • d j) ∈ Af (1 - a) := by
      intro i
      have := (htz (1 - a) a (vec (∑ j, c' j • d j) i)).2 (by rw [sub_add_cancel]; exact hx1 i)
      exact this
    have hxB : (∑ j, c' j • d j) ∈ Submodule.span ↥K.1 (d '' {j | k j = -a}) := by
      refine Submodule.sum_mem _ fun j _ => ?_
      by_cases hj : -(k j) = a
      · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, show k j = -a by omega, rfl⟩)
      · rw [hc'0 j hj, zero_smul]; exact Submodule.zero_mem _
    have hdisj := hli.disjoint_span_image (s := {j | 1 - a ≤ k j}) (t := {j | k j = -a})
      (Set.disjoint_left.2 fun j h1 h2 => by simp only [Set.mem_setOf_eq] at h1 h2; omega)
    rw [hsp] at hxA
    have hx0 : (∑ j, c' j • d j) = 0 := (Submodule.disjoint_def.1 hdisj) _ hxA hxB
    have := Fintype.linearIndependent_iff.1 hli c' hx0
    funext j
    exact congrArg Subtype.val (this j)
  have hliC : LinearIndependent ℂ_[l] (fun j i => M i j) :=
    GlobalTheory.T.linearIndependent_cyclotomicEigenvectors_weights l P n K Aθ n (fun j i => M i j) (fun j => -(k j)) hc1 hc2
  have hunit : IsUnit M := Matrix.linearIndependent_cols_iff_isUnit.1 hliC
  have hdet : θ U0S.det ≠ 0 := by
    rw [RingHom.map_det]
    exact ((Matrix.isUnit_iff_isUnit_det _).1 hunit).ne_zero
  have hdetU : U0.det = (U0S.det : P.R.BdR) := by
    have := RingHom.map_det S.subtype U0S
    rw [show S.subtype.mapMatrix U0S = U0 from by ext; rfl] at this
    exact this.symm
  have hnot1 : U0.det ∉ Fil P 1 := fun h => hdet ((hθ0 _).2 (hdetU ▸ h))
  have hdet0 : U0.det ∈ Fil P 0 := hdetU ▸ (hS _).1 (U0S.det).2
  obtain ⟨y, hy0, hy⟩ := hinv _ hdet0 hnot1
  have hadj : ∀ i j, U0.adjugate i j ∈ Fil P 0 := by
    have e : U0.adjugate = S.subtype.mapMatrix U0S.adjugate := by
      rw [RingHom.map_adjugate, show S.subtype.mapMatrix U0S = U0 from by ext; rfl]
    intro i j
    rw [e]
    exact (hS _).1 (U0S.adjugate i j).2
  let U : GL n P.R.BdR := ⟨U0, y • U0.adjugate,
    by rw [Matrix.mul_smul, Matrix.mul_adjugate, smul_smul, mul_comm y, hy, one_smul],
    by rw [Matrix.smul_mul, Matrix.adjugate_mul, smul_smul, mul_comm y, hy, one_smul]⟩
  refine ⟨U, fun j => -(k j), ⟨hU0, fun i j => ?_⟩, hEig⟩
  show (y • U0.adjugate) i j ∈ Fil P 0
  rw [Matrix.smul_apply, smul_eq_mul]
  simpa using hmul 0 0 _ _ hy0 (hadj i j)

end GlobalTheory.PMon.FrameOne
