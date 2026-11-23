import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
import Development.AbelianVarietyTheory.Counterexamples.NonGaloisSurvey.ReindexedFiltrationComparison
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyThetaOnBdRPlusPeriodData
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DvrComplete

noncomputable section

namespace GlobalTheory.AdmLoc.CycWitness

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Module TensorProduct

section Line

variable {G Qp LL R : Type} [Group G] [Field Qp] [Field LL] [Algebra Qp LL] [CommRing R] [Algebra Qp R]

theorem mem_of_tmul_mem (S : Submodule Qp R) {v : LL} (hv : v ≠ 0) {r : R}
    (h : v ⊗ₜ[Qp] r ∈ LinearMap.range
      (AlgebraTensorModule.map (LinearMap.id : LL →ₗ[LL] LL) S.subtype)) : r ∈ S := by
  obtain ⟨y, hy⟩ := h
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_eq_one Qp hv
  let m : LL ⊗[Qp] R →ₗ[Qp] R := (TensorProduct.lid Qp R).toLinearMap ∘ₗ φ.rTensor R
  have hm : ∀ y, m (AlgebraTensorModule.map (LinearMap.id : LL →ₗ[LL] LL) S.subtype y) ∈ S := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul v c => simpa [m] using S.smul_mem (φ v) c.2
    | add a b ha hb => simpa only [map_add] using Submodule.add_mem _ ha hb
  have := hm y
  rw [hy] at this
  simpa [m, hφ] using this

theorem finrank_line {r : R} (hr : r ≠ 0) :
    finrank LL ↥(Submodule.span LL {(1 : LL) ⊗ₜ[Qp] r}) = 1 :=
  finrank_span_singleton fun h => hr (mem_of_tmul_mem (LL := LL) (⊥ : Submodule Qp R) one_ne_zero
    (by rw [h]; exact zero_mem _))

theorem fixed_iff (act : G → R →ₗ[Qp] R) (hmul : ∀ g x y, act g (x * y) = act g x * act g y)
    (hinv : ∀ b, (∀ g, act g b = b) → ∃ q : Qp, algebraMap Qp R q = b) {u : R} (hu : IsUnit u)
    (c : G → Qp) (hc : ∀ g, c g • act g u = u) (θ : G →* LLˣ)
    (hθ : ∀ g, (θ g : LL) = algebraMap Qp LL (c g)) (x : LL ⊗[Qp] R) :
    (∀ g, AlgebraTensorModule.map (charRep θ g) (act g) x = x) ↔
      x ∈ Submodule.span LL {(1 : LL) ⊗ₜ[Qp] u} := by
  classical
  have ht : ∀ g (v : LL) (r : R), AlgebraTensorModule.map (charRep θ g) (act g) (v ⊗ₜ[Qp] r) =
      v ⊗ₜ[Qp] (c g • act g r) := by
    intro g v r
    rw [AlgebraTensorModule.map_tmul, ← smul_tmul]
    congr 1
    change (θ g : LL) • v = _
    rw [hθ, algebraMap_smul]
  constructor
  · intro hx
    let b := Module.Basis.ofVectorSpace Qp LL
    let e := TensorProduct.equivFinsuppOfBasisLeft (N := R) b
    have he : ∀ g y i, e (AlgebraTensorModule.map (charRep θ g) (act g) y) i = c g • act g (e y i) := by
      intro g y i
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul v r =>
        rw [ht]
        simp only [e, equivFinsuppOfBasisLeft_apply_tmul_apply, map_smul]
        rw [smul_comm]
      | add a b ha hb => simp only [map_add, Finsupp.add_apply, ha, hb, smul_add]
    have hx' : x = (e x).sum fun i c => b i ⊗ₜ[Qp] c := by
      rw [← TensorProduct.equivFinsuppOfBasisLeft_symm_apply]
      exact (e.symm_apply_apply x).symm
    rw [hx']
    refine Submodule.sum_mem _ fun i _ => ?_
    obtain ⟨z, hz⟩ : ∃ z, e x i = z * u := ⟨e x i * ↑hu.unit⁻¹, by simp [mul_assoc]⟩
    obtain ⟨q, rfl⟩ := hinv z fun g => hu.mul_right_cancel (by
      have h := he g x i
      rw [hx, hz, hmul, ← mul_smul_comm, hc] at h
      exact h.symm)
    refine Submodule.mem_span_singleton.2 ⟨q • b i, ?_⟩
    rw [hz, ← Algebra.smul_def, smul_tmul', smul_eq_mul, mul_one, smul_tmul]
  · intro hx g
    obtain ⟨v, rfl⟩ := Submodule.mem_span_singleton.1 hx
    rw [map_smul, ht, hc]

end Line

section Per

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) {LL : Type} [Field LL] [Algebra Qp LL]

theorem act_t_pow (a : ℕ) (g : G) :
    (((PD.χ g)⁻¹ ^ a : Qpˣ) : Qp) • PD.actB g (PD.t ^ a) = PD.t ^ a := by
  rw [map_pow, PD.t_act, smul_pow, smul_smul, ← Units.val_pow_eq_pow_val, ← Units.val_mul, ← mul_pow]
  simp

theorem t_pow_mem_iff (hs : ∃ s ∈ PD.Fil (-1), PD.ι PD.t * s = 1) (a : ℕ) (b : ℤ) :
    PD.ι (PD.t ^ a) ∈ PD.Fil b ↔ b ≤ a := by
  obtain ⟨s, hs, e⟩ := hs
  have h1 : ∀ a : ℕ, PD.ι (PD.t ^ a) ∈ PD.Fil a := by
    intro a
    induction a with
    | zero => simpa using PD.one_mem
    | succ a ih =>
      rw [pow_succ, map_mul, Nat.cast_succ]
      exact PD.Fil_mul _ _ _ _ ih PD.mem_filtration_one
  have h2 : ∀ a : ℕ, PD.ι (PD.t ^ a) ∉ PD.Fil (a + 1) := by
    intro a
    induction a with
    | zero => simpa using GlobalTheory.Survey.SlowDecayFunctions.one_notMem PD
    | succ a ih =>
      intro h
      have := PD.Fil_mul _ _ _ _ h hs
      rw [pow_succ, map_mul, mul_assoc, e, mul_one,
        show ((a + 1 : ℕ) : ℤ) + 1 + -1 = a + 1 by push_cast; ring] at this
      exact ih this
  refine ⟨fun h => ?_, fun h => GlobalTheory.Survey.SlowDecayFunctions.fil_antitone PD h (h1 a)⟩
  by_contra hb
  exact h2 a (GlobalTheory.Survey.SlowDecayFunctions.fil_antitone PD (by omega) h)

variable (hK : Function.Surjective (algebraMap Qp K)) (a : ℕ) (θ : G →* LLˣ)
  (hθ : ∀ g, (θ g : LL) = algebraMap Qp LL (((PD.χ g)⁻¹ ^ a : Qpˣ) : Qp))

include hK in
theorem surj_K₀ : Function.Surjective (algebraMap Qp K₀) := fun x => by
  obtain ⟨q, hq⟩ := hK (algebraMap K₀ K x)
  exact ⟨q, (algebraMap K₀ K).injective (by rw [← hq, ← IsScalarTower.algebraMap_apply])⟩

include hK hθ

theorem isCrys_pow : IsCrys PD (charRep θ) := by
  have h0 := surj_K₀ (K₀ := K₀) hK
  have hD : Dcris PD (charRep θ) = Submodule.span LL {(1 : LL) ⊗ₜ[Qp] (PD.t ^ a)} := by
    ext x
    simp only [Dcris, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.id_apply, sub_eq_zero]
    refine fixed_iff (fun g => (PD.actB g).toAlgHom.toLinearMap.restrictScalars Qp)
      (fun g x y => map_mul (PD.actB g) x y) (fun b hb => ?_) (PD.t_unit.pow a) _
      (act_t_pow PD a) θ hθ x
    obtain ⟨c, rfl⟩ := PD.invB b hb
    obtain ⟨q, rfl⟩ := h0 c
    exact ⟨q, IsScalarTower.algebraMap_apply _ _ _ q⟩
  have hne : PD.t ^ a ≠ 0 := fun h => by
    have h1 : (1 : B) = 0 := isUnit_zero_iff.1 (h ▸ PD.t_unit.pow a) |>.symm
    exact GlobalTheory.Survey.SlowDecayFunctions.one_notMem PD (by rw [← map_one PD.ι, h1, map_zero]; exact zero_mem _)
  have hf : finrank Qp K₀ = 1 := by
    rw [← (LinearEquiv.ofBijective (Algebra.linearMap Qp K₀)
      ⟨(algebraMap Qp K₀).injective, h0⟩).finrank_eq, finrank_self]
  rw [IsCrys, hD, finrank_line hne, hf, finrank_self]

theorem ddRE_pow (τ : K →ₐ[Qp] LL) :
    DdRE PD (charRep θ) τ = Submodule.span LL {(1 : LL) ⊗ₜ[Qp] PD.ι (PD.t ^ a)} := by
  have hD : DdR PD (charRep θ) = Submodule.span LL {(1 : LL) ⊗ₜ[Qp] PD.ι (PD.t ^ a)} := by
    ext x
    simp only [DdR, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.id_apply, sub_eq_zero]
    refine fixed_iff (fun g => (PD.actdR g).toAlgHom.toLinearMap.restrictScalars Qp)
      (fun g x y => map_mul (PD.actdR g) x y) (fun b hb => ?_) ((PD.t_unit.pow a).map PD.ι) _
      (fun g => ?_) θ hθ x
    · obtain ⟨c, rfl⟩ := PD.invdR b hb
      obtain ⟨q, rfl⟩ := hK c
      exact ⟨q, IsScalarTower.algebraMap_apply _ _ _ q⟩
    · change _ • PD.actdR g (PD.ι (PD.t ^ a)) = _
      rw [← PD.ι_comm]
      exact ((PD.ι.toLinearMap.restrictScalars Qp).map_smul _ _).symm.trans
        (congrArg PD.ι (act_t_pow PD a g))
  rw [DdRE, hD, inf_eq_left, Submodule.span_le, Set.singleton_subset_iff]
  simp only [SetLike.mem_coe, Submodule.mem_iInf, LinearMap.mem_ker]
  intro c
  obtain ⟨q, rfl⟩ := hK c
  simp only [mulVdR, LinearMap.sub_apply, AlgebraTensorModule.map_tmul, LinearMap.id_apply,
    LinearMap.mulLeft_apply, LinearMap.smul_apply, AlgHom.commutes, sub_eq_zero,
    ← IsScalarTower.algebraMap_apply, algebraMap_smul]
  rw [← Algebra.smul_def, tmul_smul]

theorem multV_pow (hs : ∃ s ∈ PD.Fil (-1), PD.ι PD.t * s = 1) (τ : K →ₐ[Qp] LL) (b : ℤ) :
    multV PD (charRep θ) τ b = (({(a : ℤ)} : Multiset ℤ).count b : ℤ) := by
  have hne : PD.ι (PD.t ^ a) ≠ 0 := fun h => by
    have := (t_pow_mem_iff PD hs a (a + 1)).1 (by rw [h]; exact zero_mem _)
    omega
  have hF : ∀ b : ℤ, finrank LL ↥(FildR PD (charRep θ) τ b) = if b ≤ a then 1 else 0 := by
    intro b
    rw [FildR, ddRE_pow PD hK a θ hθ]
    split_ifs with h
    · rw [inf_eq_left.2, finrank_line hne]
      rw [Submodule.span_le, Set.singleton_subset_iff]
      exact ⟨1 ⊗ₜ ⟨_, (t_pow_mem_iff PD hs a b).2 h⟩, rfl⟩
    · rw [Submodule.finrank_eq_zero.2]
      rw [eq_bot_iff]
      rintro x ⟨hx, hx'⟩
      obtain ⟨v, rfl⟩ := Submodule.mem_span_singleton.1 hx
      by_cases hv : v = 0
      · simp [hv]
      · rw [smul_tmul', smul_eq_mul, mul_one] at hx'
        exact absurd ((t_pow_mem_iff PD hs a b).1
          (mem_of_tmul_mem ((PD.Fil b).restrictScalars Qp) hv hx')) h
  rw [multV, hF, hF, Multiset.count_singleton]
  split_ifs <;> simp <;> omega

end Per

def lowData (t : ℕ) (h1 : 1 ≤ t) (h4 : t ≤ 4) : TopData 1 1 where
  h := fun _ => 12
  η := fun _ => 10
  ty := fun _ => LType.G
  w := fun _ => 1
  t := t
  lows := fun _ => {7}
  cloud := fun _ => 0
  two_le_h := fun _ => by norm_num
  one_le_η := fun _ => by norm_num
  one_le_letterBlockLength := h1
  card_eq := fun _ => by simp
  range := fun _ u hu => by simp [mem_block] at hu; push_cast; omega
  lowG := fun _ _ u hu => by simp [mem_block] at hu; push_cast; omega
  cloudG := fun _ _ u hu => by simp at hu
  lowBd := fun _ h => by cases h
  cloudBd := fun _ h => by cases h

theorem lowData_sg {t : ℕ} (h1 : 1 ≤ t) (h4 : t ≤ 4) {l : ℕ} (hl : 17 ≤ l) (i : ZMod 1) :
    (lowData t h1 h4).sg l i = 0 := by
  have hl' : (17 : ℝ) ≤ l := by exact_mod_cast hl
  have hi : (l : ℝ)⁻¹ ≤ 17⁻¹ := inv_anti₀ (by norm_num) hl'
  have h0 : (0 : ℝ) ≤ (l : ℝ)⁻¹ := by positivity
  have h : ∀ j : ℕ, ((12 : ℕ) : ℝ) / (l : ℝ) ^ (j + 1) = (12 * (l : ℝ)⁻¹) * ((l : ℝ)⁻¹) ^ j := by
    intro j; push_cast; rw [div_eq_mul_inv, ← inv_pow]; ring
  change ⌊∑' j : ℕ, ((12 : ℕ) : ℝ) / (l : ℝ) ^ (j + 1)⌋₊ = 0
  simp_rw [h]
  rw [tsum_mul_left, tsum_geometric_of_lt_one h0 (by linarith), Nat.floor_eq_zero,
    mul_inv_lt_iff₀ (by linarith)]
  linarith

theorem lowData_T1_T2_T3_of_seventeen_le {t : ℕ} (h1 : 1 ≤ t) (h4 : t ≤ 4) {l : ℕ} (hl : 17 ≤ l) :
    (lowData t h1 h4).T1 l ∧ (lowData t h1 h4).T2 l ∧ (lowData t h1 h4).T3 l := by
  refine ⟨fun i => ?_, fun i u hu β hβ => ?_, fun i u hu => ?_⟩
  · rw [lowData_sg h1 h4 hl]
    change 10 + 4 * 0 + 6 < l
    omega
  · rw [lowData_sg h1 h4 hl]
    simp only [lowData, TopData.B, mem_block, Multiset.mem_singleton] at hu hβ
    rw [lt_abs]; push_cast; omega
  · simp [lowData] at hu

variable {l : ℕ} [Fact l.Prime]

def cycO (P : LocPrime l) (K LL : FinExt l) : ↥(GK K) →* (↥(OL LL))ˣ :=
  MonoidHom.toHomUnits
    { toFun := fun g => ⟨_, GlobalTheory.IndefiniteRowSideFullHecke.SelmerFiniteUnramified.cyc_mem P K LL g⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun g h => Subtype.ext (by simp) }

theorem cycO_val (P : LocPrime l) (K LL : FinExt l) (g : ↥(GK K)) :
    algebraMap ↥(OL LL) ↥LL.1 (cycO P K LL g) = algebraMap ℚ_[l] ↥LL.1 ((P.PD K).χ g) := rfl

theorem cycO_inv_pow (P : LocPrime l) (K LL : FinExt l) (a : ℕ) (g : ↥(GK K)) :
    algebraMap ↥(OL LL) ↥LL.1 (((cycO P K LL)⁻¹ ^ a) g) =
      algebraMap ℚ_[l] ↥LL.1 ((((P.PD K).χ g)⁻¹ ^ a : ℚ_[l]ˣ) : ℚ_[l]) := by
  rw [MonoidHom.pow_apply, MonoidHom.inv_apply, ← map_inv, ← map_inv, Units.val_pow_eq_pow_val,
    Units.val_pow_eq_pow_val, map_pow, map_pow, cycO_val]

theorem continuous_cycO_inv_pow (P : LocPrime l) (K LL : FinExt l) (a : ℕ) :
    Continuous fun g => algebraMap ↥(OL LL) ↥LL.1 (((cycO P K LL)⁻¹ ^ a) g) := by
  have h := ((GlobalTheory.Survey.SlowDecayFunctions.continuous_cyc P K LL).comp continuous_inv).pow a
  refine h.congr fun g => ?_
  rw [cycO_inv_pow, ← map_inv, Units.val_pow_eq_pow_val, map_pow]
  rfl

theorem surj_bot : Function.Surjective (algebraMap ℚ_[l] ↥(Formalism.MainNotions.LocalSituation.botExt l).1) := fun x => by
  obtain ⟨q, hq⟩ := IntermediateField.mem_bot.1 x.2
  exact ⟨q, Subtype.ext hq⟩

theorem isCrysChar_inv_pow {P : LocPrime l} {AI : LocAinf l P} (T : LocTied l P AI) (LL : FinExt l) {n : ℕ}
    (emb : ZMod n → (↥(K0 (Formalism.MainNotions.LocalSituation.botExt l)) →ₐ[ℚ_[l]] ↥LL.1)) (a : ℕ) :
    IsCrysChar (P.PD (Formalism.MainNotions.LocalSituation.botExt l)) emb ((cycO P (Formalism.MainNotions.LocalSituation.botExt l) LL)⁻¹ ^ a)
      (fun _ => (a : ℤ)) := by
  refine ⟨continuous_cycO_inv_pow P _ LL a, isCrys_pow _ surj_bot a _ (cycO_inv_pow P _ LL a),
    fun i τ _ b => multV_pow _ surj_bot a _ (cycO_inv_pow P _ LL a) ?_ τ b⟩
  rw [P.PD_ι, P.period_datum_t_eq]
  exact GlobalTheory.ThetaTie.exists_inverse_fontaineElement_mem_fil_neg_one T

theorem exists_standing (hl : 5 ≤ l) (P : LocPrime l) :
    ∃ (LL : FinExt l) (emb : ZMod 1 → (↥(K0 (Formalism.MainNotions.LocalSituation.botExt l)) →ₐ[ℚ_[l]] ↥LL.1)) (lam : ↥(OL LL)),
      Standing P (Formalism.MainNotions.LocalSituation.botExt l) LL emb lam := by
  obtain ⟨LL, hL⟩ := GlobalTheory.MemLoc.exists_good_situation l (Formalism.MainNotions.LocalSituation.botExt l) 1 le_rfl
    (fun h => by omega) bot_le
  obtain ⟨_, -⟩ := GlobalTheory.FinExtIntegers.dvr_complete LL
  obtain ⟨lam, hlam⟩ := IsDiscreteValuationRing.exists_irreducible ↥(OL LL)
  have h0 : Function.Surjective (algebraMap ℚ_[l] ↥(K0 (Formalism.MainNotions.LocalSituation.botExt l))) := surj_K₀ surj_bot
  have hsub : ∀ f g : ↥(K0 (Formalism.MainNotions.LocalSituation.botExt l)) →ₐ[ℚ_[l]] ↥LL.1, f = g := fun f g =>
    AlgHom.ext fun x => by
      obtain ⟨q, rfl⟩ := h0 x
      rw [f.commutes, g.commutes]
  let e := AlgEquiv.ofBijective (Algebra.ofId ℚ_[l] ↥(K0 (Formalism.MainNotions.LocalSituation.botExt l)))
    ⟨(algebraMap ℚ_[l] _).injective, h0⟩
  refine ⟨LL, fun _ => (Algebra.ofId ℚ_[l] ↥LL.1).comp e.symm.toAlgHom, lam, hl,
    ⟨bot_le, by omega, hL LL le_rfl⟩, IntermediateField.finrank_bot.symm,
    ⟨fun _ _ _ => Subsingleton.elim _ _, fun f => ⟨0, hsub _ _⟩⟩, fun _ => hsub _ _, hlam⟩

theorem exists_premises_block (hl : 17 ≤ l) (P : LocPrime l) (AI : LocAinf l P)
    (hT : Nonempty (LocTied l P AI)) (t : ℕ) (h1 : 1 ≤ t) (h4 : t ≤ 4) :
    ∃ (K LL : FinExt l) (emb : ZMod 1 → (↥(K0 K) →ₐ[ℚ_[l]] ↥LL.1)) (D : TopData 1 1)
      (Γ : GalData ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)),
      D.t = t ∧ Standing P K LL emb Γ.lam ∧ IsTopGal (P.PD K) emb D Γ ∧ D.T1 l ∧ D.T2 l ∧ D.T3 l := by
  obtain ⟨T⟩ := hT
  obtain ⟨LL, emb, lam, hS⟩ := exists_standing (by omega) P
  have h7 := isCrysChar_inv_pow T LL emb 7
  refine ⟨Formalism.MainNotions.LocalSituation.botExt l, LL, emb, lowData t h1 h4,
    ⟨lam, charLat ℚ_[l] Subtype.val_injective _ h7.1, (cycO P _ LL)⁻¹ ^ 1, cycO P _ LL⟩, rfl, hS,
    ⟨finrank_self ↥LL.1, h7.2, isCrysChar_inv_pow T LL emb 1, cycO_val P _ LL⟩, lowData_T1_T2_T3_of_seventeen_le h1 h4 hl⟩

end GlobalTheory.AdmLoc.CycWitness
