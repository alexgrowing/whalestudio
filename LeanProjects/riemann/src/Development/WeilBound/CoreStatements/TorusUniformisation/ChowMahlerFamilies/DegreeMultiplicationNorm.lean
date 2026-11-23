import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GermSys
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CardTorsionPointsAbelianVariety
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FinrankSecPullSandwich
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsHighTwistSectionNeZeroStatement
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FlatAndSurjectiveOfIsFiniteAbelianEnd
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPositiveDefiniteQuadraticFormEndomorphisms
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ConnectedSpaceSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Statements.FundamentalDomains.ExistsIsAddFundamentalDomain
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.LiePush

noncomputable section

namespace PositivityTheory.Xgn.DegreeMultiplicationNorm

section Algebra

open NumberField

theorem quad_nat {A P : Type*} [AddCommGroup A] [AddCommGroup P] (q : A → P) (h0 : q 0 = 0)
    (hq : ∀ a b, q (a + b) + q (a - b) = 2 • q a + 2 • q b) (x : A) (n : ℕ) : q (n • x) = n ^ 2 • q x := by
  induction n using Nat.twoStepInduction with
  | zero => simpa using h0
  | one => simp
  | more n h1 h2 =>
    have e := hq ((n + 1) • x) x
    rw [← succ_nsmul, show (n + 1) • x - x = n • x by rw [succ_nsmul, add_sub_cancel_right], h1, h2] at e
    rw [eq_sub_of_add_eq e]
    module

theorem quad_int {A P : Type*} [AddCommGroup A] [AddCommGroup P] (q : A → P) (h0 : q 0 = 0)
    (hq : ∀ a b, q (a + b) + q (a - b) = 2 • q a + 2 • q b) (x : A) (n : ℤ) :
    q (n • x) = n.natAbs ^ 2 • q x := by
  have hneg : ∀ y, q (-y) = q y := fun y => by
    have e := hq 0 y
    rw [zero_add, zero_sub, h0, smul_zero, zero_add, two_nsmul] at e
    exact add_left_cancel e
  obtain ⟨m, rfl | rfl⟩ := n.eq_nat_or_neg
  · rw [natCast_zsmul, Int.natAbs_natCast, quad_nat q h0 hq]
  · rw [neg_smul, hneg, natCast_zsmul, Int.natAbs_neg, Int.natAbs_natCast, quad_nat q h0 hq]

theorem quad_bound {A P ι : Type*} [AddCommGroup A] [AddCommGroup P] (q : A → P) (h0 : q 0 = 0)
    (hq : ∀ a b, q (a + b) + q (a - b) = 2 • q a + 2 • q b) (S : AddSubmonoid P) (h : P) (hh : h ∈ S)
    (hS : ∀ a, q a ∈ S) (hN : ∀ a, ∃ N : ℕ, N • h - q a ∈ S) (ω : ι → A) (s : Finset ι) :
    ∃ C : ℕ, 1 ≤ C ∧ ∀ (T : ℕ) (c : ι → ℤ), (∀ i, (c i).natAbs ≤ T) → (C * T ^ 2) • h - q (∑ i ∈ s, c i • ω i) ∈ S := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, le_rfl, fun T c _ => by rw [Finset.sum_empty, h0, sub_zero]; exact S.nsmul_mem hh _⟩
  | insert i s hi ih =>
    obtain ⟨C, hC, ih⟩ := ih
    obtain ⟨N, hN⟩ := hN (ω i)
    refine ⟨2 * N + 2 * C, by omega, fun T c hc => ?_⟩
    obtain ⟨r, hr⟩ := Nat.exists_eq_add_of_le (Nat.pow_le_pow_left (hc i) 2)
    rw [Finset.sum_insert hi, eq_sub_of_add_eq (hq _ _), quad_int q h0 hq]
    have e := S.add_mem (S.add_mem (S.nsmul_mem (S.add_mem (S.nsmul_mem hN ((c i).natAbs ^ 2))
      (S.nsmul_mem hh (N * r))) 2) (S.nsmul_mem (ih T c hc) 2)) (hS (c i • ω i - ∑ j ∈ s, c j • ω j))
    rw [hr] at e ⊢
    convert e using 1
    module

theorem le_of_pow_le {A B K : ℕ} (hB : 1 ≤ B) (h : ∀ k, A ^ k ≤ K * B ^ k) : A ≤ B := by
  by_contra hlt
  have hB' : (0 : ℝ) < B := by exact_mod_cast hB
  have h1 : (1 : ℝ) < A / B := (one_lt_div hB').2 (by exact_mod_cast not_le.1 hlt)
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (K : ℝ) h1
  rw [div_pow, lt_div_iff₀ (pow_pos hB' k)] at hk
  exact absurd (h k) (not_le.2 (by exact_mod_cast hk))

theorem pow_eq_norm {E : Type} [Field E] [NumberField E] (deg : 𝓞 E → ℕ) (e C : ℕ)
    (hmul : ∀ a b, a ≠ 0 → b ≠ 0 → deg (a * b) = deg a * deg b) (hpos : ∀ a, a ≠ 0 → 1 ≤ deg a)
    (hnat : ∀ n : ℕ, n ≠ 0 → deg n = n ^ e)
    (hb : ∀ (T : ℕ) (c : Module.Free.ChooseBasisIndex ℤ (𝓞 E) → ℤ), (∀ i, (c i).natAbs ≤ T) →
      ∑ i, c i • RingOfIntegers.basis E i ≠ 0 → deg (∑ i, c i • RingOfIntegers.basis E i) ≤ C * T ^ e)
    (a : 𝓞 E) (ha : a ≠ 0) : deg a ^ Module.finrank ℚ E = (Algebra.norm ℤ a).natAbs ^ e := by
  classical
  set m := Module.finrank ℚ E with hm
  have hm0 : m ≠ 0 := Module.finrank_pos.ne'
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ (𝓞 E)) = m := by
    rw [← Module.finrank_eq_card_chooseBasisIndex, RingOfIntegers.rank]
  have hN : ∀ a : 𝓞 E, a ≠ 0 → (Algebra.norm ℤ a).natAbs ≠ 0 := fun a ha =>
    Int.natAbs_ne_zero.2 (Algebra.norm_ne_zero_iff.2 ha)
  have hpow : ∀ a : 𝓞 E, a ≠ 0 → ∀ k, deg (a ^ k) = deg a ^ k := fun a ha k => by
    induction k with
    | zero => simpa using hnat 1 one_ne_zero
    | succ k ih => rw [pow_succ, hmul _ _ (pow_ne_zero _ ha) ha, ih, pow_succ]
  have upper : ∀ a : 𝓞 E, a ≠ 0 → deg a ^ m ≤ (Algebra.norm ℤ a).natAbs ^ e := by
    intro a ha
    refine le_of_pow_le (K := C ^ m) (Nat.one_le_iff_ne_zero.2 (pow_ne_zero _ (hN a ha))) fun k => ?_
    set N := (Algebra.norm ℤ a).natAbs ^ k with hNk
    have hex : ∃ T : ℕ, N < (T + 1) ^ m := ⟨N, (Nat.lt_succ_self N).trans_le (Nat.le_self_pow hm0 _)⟩
    obtain ⟨T, hT, hT'⟩ : ∃ T : ℕ, N < (T + 1) ^ m ∧ T ^ m ≤ N := by
      refine ⟨Nat.find hex, Nat.find_spec hex, ?_⟩
      rcases h : Nat.find hex with _ | T
      · rw [zero_pow hm0]; exact Nat.zero_le _
      · exact not_lt.1 (Nat.find_min hex (by omega : T < Nat.find hex))
    let I : Ideal (𝓞 E) := Ideal.span {a ^ k}
    have hI : Nat.card (𝓞 E ⧸ I) = N := by
      rw [← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, Ideal.absNorm_span_singleton, map_pow, Int.natAbs_pow]
    haveI : Finite (𝓞 E ⧸ I) := Nat.finite_of_card_ne_zero (hI ▸ pow_ne_zero _ (hN a ha))
    haveI := Fintype.ofFinite (𝓞 E ⧸ I)
    obtain ⟨u, v, huv, he⟩ := Fintype.exists_ne_map_eq_of_card_lt
      (fun u : Module.Free.ChooseBasisIndex ℤ (𝓞 E) → Fin (T + 1) =>
        Ideal.Quotient.mk I (∑ i, ((u i : ℕ) : ℤ) • RingOfIntegers.basis E i)) (by
        rw [← Nat.card_eq_fintype_card, hI, Fintype.card_fun, hcard, Fintype.card_fin]; exact hT)
    have hmem := Ideal.Quotient.eq.1 he
    simp only [← Finset.sum_sub_distrib, ← sub_smul] at hmem
    have hx : ∑ i, (((u i : ℕ) : ℤ) - ((v i : ℕ) : ℤ)) • RingOfIntegers.basis E i ≠ 0 := fun h0 => huv (by
      funext i
      have := Fintype.linearIndependent_iff.1 (RingOfIntegers.basis E).linearIndependent _ h0 i
      exact Fin.ext (by omega))
    have hle := hb T _ (fun i => by have := (u i).2; have := (v i).2; omega) hx
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 hmem
    have hy0 : y ≠ 0 := by rintro rfl; exact hx (by rw [← hy, zero_mul])
    rw [← hy, hmul _ _ hy0 (pow_ne_zero _ ha), hpow a ha] at hle
    have h2 : deg a ^ k ≤ C * T ^ e := (Nat.le_mul_of_pos_left _ (hpos y hy0)).trans hle
    calc (deg a ^ m) ^ k = (deg a ^ k) ^ m := by rw [← pow_mul, ← pow_mul, mul_comm]
      _ ≤ (C * T ^ e) ^ m := Nat.pow_le_pow_left h2 _
      _ = C ^ m * (T ^ m) ^ e := by rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm e]
      _ ≤ C ^ m * N ^ e := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hT' _)
      _ = _ := by rw [hNk, ← pow_mul, ← pow_mul, mul_comm k]
  obtain ⟨b, hb'⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {a}))
  rw [Ideal.absNorm_span_singleton] at hb'
  set N := (Algebra.norm ℤ a).natAbs with hNa
  have hb0 : b ≠ 0 := by
    rintro rfl
    rw [zero_mul] at hb'
    exact hN a ha (Nat.cast_eq_zero.1 hb'.symm)
  have e1 : deg b * deg a = N ^ e := by rw [← hmul _ _ hb0 ha, hb', hnat _ (hN a ha)]
  have e2 : (Algebra.norm ℤ b).natAbs * N = N ^ m := by
    rw [hNa, ← Int.natAbs_mul, ← map_mul, hb', ← hNa, ← map_natCast (algebraMap ℤ (𝓞 E)),
      Algebra.norm_algebraMap, RingOfIntegers.rank, Int.natAbs_pow, Int.natAbs_natCast]
  have e3 : deg b ^ m * deg a ^ m = (Algebra.norm ℤ b).natAbs ^ e * N ^ e := by
    rw [← mul_pow, ← mul_pow, e1, e2, ← pow_mul, ← pow_mul, mul_comm]
  refine le_antisymm (upper a ha) (Nat.le_of_mul_le_mul_left ?_
    (Nat.pos_of_ne_zero (pow_ne_zero e (hN b hb0))))
  rw [← e3]
  exact Nat.mul_le_mul_right _ (upper b hb0)

end Algebra

section Bundles

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU
open GlobalTheory.FiniteCover GlobalTheory.CechPic
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem sandwich : ∀ (K : Type) [Field K] (X X' : Scheme.{0}) [IsIntegral X] [IsIntegral X'] (f : X ⟶ Spec (CommRingCat.of K)) (φ : X' ⟶ X) [IsFinite φ] [Flat φ] [Surjective φ] (H : LB X) (n : ℕ) (s : Fin (n + 1) → LB.Sec H), H.IsLB → VeryAmpleBy f H s → ∀ d : ℕ, (∀ x : X, φ.finrank x = d) → (∀ t : ℕ, Module.Finite K (SecOnR f (pw H t) ⊤)) → (∀ t : ℕ, Module.Finite K (SecOnR (φ ≫ f) ((pw H t).pull φ) ⊤)) → ∃ a : ℕ, ∀ t : ℕ, d * Module.finrank K (SecOnR (f) (pw H t) ⊤) ≤ Module.finrank K (SecOnR (φ ≫ f) ((pw H (t + a : ℕ)).pull φ) ⊤) ∧ Module.finrank K (SecOnR (φ ≫ f) ((pw H t).pull φ) ⊤) ≤ d * Module.finrank K (SecOnR (f) (pw H (t + a : ℕ)) ⊤) := by
  intro K _ X X' _ _ f φ _ _ _ H n s hH hs d hd hV hW
  have hd1 : 1 ≤ d := hd (genericPoint X) ▸ φ.one_le_finrank_iff_surjective.2 inferInstance _
  letI : Algebra X.functionField X'.functionField := (functionFieldMap φ).toAlgebra
  letI : Algebra K X.functionField := ((toField generic_top).comp (cst f ⊤)).toAlgebra
  letI : Algebra K X'.functionField := ((toField generic_top).comp (cst (φ ≫ f) ⊤)).toAlgebra
  haveI : IsScalarTower K X.functionField X'.functionField :=
    IsScalarTower.of_algebraMap_eq fun r => by
      have w : φ ≫ f = (φ ≫ f) ≫ Spec.map (CommRingCat.ofHom (RingHom.id K)) := by simp
      have e := toField_appLE φ (U := ⊤) (V := ⊤) le_top generic_top generic_top (cst f ⊤ r)
      exact (congrArg (toField generic_top)
        (appLE_cst w (V := ⊤) (V' := ⊤) le_top r)).symm.trans e
  obtain ⟨hcov, hs⟩ := hs
  choose haff r hr _ using hs
  let I := {i // genericPoint X ∈ nonzeroLocus (s i)}
  haveI : Fintype I := Fintype.ofFinite I
  let D : I → X.Opens := fun i => nonzeroLocus (s i.1)
  have hη : ∀ i, genericPoint X ∈ D i := fun i => i.2
  have hc : ⊤ ≤ ⨆ i, D i := fun x hx => by
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (hcov.ge hx)
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨i, generic_mem hi⟩, hi⟩
  have hc' : ⊤ ≤ ⨆ i, φ ⁻¹ᵁ D i := fun x _ => by
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (hc (trivial : φ x ∈ ⊤))
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, hi⟩
  obtain ⟨i₀, -⟩ := TopologicalSpace.Opens.mem_iSup.1 (hc generic_top)
  obtain ⟨k₀, h₀⟩ := TopologicalSpace.Opens.mem_iSup.1 (hH.cover.ge generic_top)
  obtain ⟨x, hx⟩ := (chart_data φ (fun _ => rfl) (haff i₀.1) (hη i₀)).1
  rw [hd] at hx
  haveI : Module.Finite X.functionField X'.functionField :=
    Module.finite_of_finrank_pos (by omega)
  let e := Module.finBasisOfFinrankEq _ _ hx
  choose c hcm hc0 hc₁ hc₂ using fun i : I =>
    (chart_data φ (fun _ => rfl) (haff i.1) (hη i)).2 e
  let ρ : I → X.functionField := fun i => toField h₀ ((s i.1).f k₀)
  have hu : ∀ (i : I) k, IsUnit (rs X (inf_le_right : D i ⊓ H.U k ≤ H.U k) ((s i.1).f k)) :=
    fun i k => SecOn.isUnit_rs_of_le_nonzeroLocus _ k _ inf_le_left
  have hρ : ∀ i, ρ i ≠ 0 := fun i => by
    have := ((hu i k₀).map (toField (generic_inf (hη i) h₀))).ne_zero
    rwa [toField_rs] at this
  have hρr : ∀ i k : I, ρ i / ρ k = toField (hη k) (r k.1 i.1) := fun i k => by
    have := congrArg (toField (generic_inf (hη k) h₀)) (hr k.1 i.1 k₀)
    rw [map_mul, toField_rs, toField_rs, toField_rs] at this
    exact (div_eq_iff (hρ k)).2 this
  let τ : ∀ (t : ℕ) (i : I), SecOn (pw H t) (D i) := fun t i => GlobalTheory.LB.ofSec (powSec (s i.1) t) (D i)
  have hτc : ∀ (t : ℕ) (i : I) (k : H.ι), GlobalTheory.LB.coord (τ t i) k =
      rs X (inf_le_right : D i ⊓ H.U k ≤ H.U k) ((s i.1).f k) ^ t := fun t i k =>
    (GlobalTheory.LB.coord_ofSec _ _ _).trans (map_pow (rs X (inf_le_right : D i ⊓ H.U k ≤ H.U k)) _ _)
  have hτ : ∀ (t : ℕ) (i : I) (k : H.ι), IsUnit (GlobalTheory.LB.coord (τ t i) k) := fun t i k =>
    (hτc t i k).symm ▸ (hu i k).pow t
  have hτv : ∀ (t : ℕ) (i : I), secVal (M := pw H t) (k₀ := k₀) h₀ (hη i) (τ t i) = ρ i ^ t :=
    fun t i => (congrArg (toField (generic_inf (hη i) h₀)) (hτc t i k₀)).trans (by
      rw [map_pow, toField_rs])
  have h₀' : ∀ t : ℕ, genericPoint X' ∈ ((pw H t).pull φ).U fun _ => k₀ := fun t =>
    le_pull (pw H t) φ (i := k₀) le_rfl (generic_mem_preimage φ h₀)
  refine finrank_sandwich e (fun i => (toField (hη i)).range)
    (fun i => (toField (generic_mem_preimage φ (hη i))).range) ρ c hρ hc0
    (fun i k => ⟨_, (hρr i k).symm⟩) (fun i k => ?_) ?_ hc₁ hc₂
    (fun t => SecOnR f (pw H t) ⊤) (fun t => SecOnR (φ ≫ f) ((pw H t).pull φ) ⊤) hV hW
    (fun t => secValLin (M := pw H t) (k₀ := k₀) h₀ f fun _ => rfl)
    (fun t => secValLin (h₀' t) (φ ≫ f) fun _ => rfl)
    (fun t => secVal_injective (M := pw H t) (k₀ := k₀) h₀ generic_top)
    (fun t => secVal_injective (h₀' t) generic_top) (fun t x => ?_) fun t y => ?_
  · obtain ⟨a, ha⟩ := hcm i
    rw [← ha, hρr]
    exact exists_mul_pow_mem (haff k.1) (hη k) (hη i) _
      (hρr i k ▸ div_ne_zero (hρ i) (hρ k)) (basicOpen_le_nonzeroLocus _ _ _ (hr k.1 i.1)) a
  · rintro i _ ⟨a, rfl⟩
    exact ⟨_, toField_appLE φ le_rfl (hη i) _ a⟩
  · refine (exists_secVal_eq_iff (M := pw H t) (k₀ := k₀) h₀ (isLB_pw hH t) D hc hη (τ t) (hτ t)
      x).trans ?_
    simp only [hτv]
  · refine (exists_secVal_eq_iff (h₀' t) (LB.isLB_pull (isLB_pw hH t) φ) (fun i => φ ⁻¹ᵁ D i) hc'
      (fun i => generic_mem_preimage φ (hη i)) (fun i => SecOn.pull (pw H t) φ (D i) (τ t i))
      (fun i k => (hτ t i (k PUnit.unit)).map _) y).trans ?_
    refine forall_congr' fun i => ?_
    rw [secVal_pull (M := pw H t) (k₀ := k₀) h₀ φ (hη i), hτv]
    rfl

variable {X : Scheme.{0}}

theorem cls_pw {L : LB X} (hL : L.IsLB) (d : ℤ) : cls (AbLaw.pw L d) (isLB_pw hL d) = d • cls L hL := by
  have h := LB.isLB_linComb hL (fun _ : PUnit => 𝟙 X) (fun _ => d)
  have e := cls_linComb hL _ _ h
  rw [Fintype.sum_unique, pull_id] at e
  rw [← e]
  refine (cls_eq_iff _ h).2 (iso_of_chart h ⟨fun i _ => i, fun _ _ hy => Set.mem_iInter.2 fun _ => hy, ?_⟩)
  intro y i j hi hj
  refine Eq.trans (map_zpow _ _ _) (Eq.symm ((gm_linComb L (fun _ : PUnit => 𝟙 X) (fun _ => d) (𝟙 X) y
    (fun _ => i) (fun _ => j) (Set.mem_iInter.2 fun _ => hi) (Set.mem_iInter.2 fun _ => hj)).trans ?_))
  rw [Fintype.prod_unique, Category.id_comp]
  rfl

theorem cls_tw {M H : LB X} (hM : M.IsLB) (hH : H.IsLB) (t : ℤ) :
    cls (tw M H t) (isLB_tw hM hH t) = cls M hM + t • cls H hH := by
  have e := cls_div hM (isLB_pw hH (-t)) (isLB_tw hM hH t)
  rw [cls_pw hH, neg_smul, sub_neg_eq_add] at e
  exact e

def Eff (c : Pic X) : Prop := ∃ (L : LB X) (hL : L.IsLB), cls L hL = c ∧ ∃ σ : SecOn L ⊤, σ ≠ 0

theorem exists_injective [IsIntegral X] {A B : LB X} (hA : A.IsLB) (hB : B.IsLB)
    (h : Eff (cls B hB - cls A hA)) : ∃ φ : SecOn A ⊤ →ₗ[Γ(X, ⊤)] SecOn B ⊤, Function.Injective φ := by
  obtain ⟨N, hN, hc, σ, hσ⟩ := h
  have e : cls (tw A N (0 + 1)) (isLB_tw hA hN _) = cls B hB := by
    rw [cls_tw hA hN, hc]; simp
  obtain ⟨w, hw⟩ := (cls_eq_iff _ _).1 e
  obtain ⟨p, hp⟩ := TopologicalSpace.Opens.mem_iSup.1 (hA.cover.ge generic_top)
  obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 (hN.cover.ge generic_top)
  have h0 : secVal hk generic_top σ ≠ 0 := fun h0 => hσ (secVal_injective hk generic_top
    (h0.trans (map_zero (toField (U := ⊤ ⊓ N.U k) (generic_inf generic_top hk))).symm))
  have hinj : Function.Injective (SecOn.mulSec A 0 (SecOn.topEquiv N σ) ⊤) := by
    intro x y hxy
    have hpk : genericPoint X ∈ (tw A N 0).U (p, k) := ⟨hp, hk⟩
    apply secVal_injective hpk generic_top
    have e₁ := congrArg (fun z => toField (U := ⊤ ⊓ (A.U p ⊓ N.U k)) (generic_inf generic_top hpk)
      (SecOn.twCoord z p k)) hxy
    simp only [SecOn.twCoord_mulSec, map_mul, toField_rs, SecOn.topEquiv_f] at e₁
    exact mul_left_cancel₀ h0 e₁
  exact ⟨(SecOn.congr (isLB_tw hA hN _) hB w hw ⊤).toLinearMap ∘ₗ SecOn.mulSec A 0 (SecOn.topEquiv N σ) ⊤ ∘ₗ
    (SecOn.twZeroEquiv hA hN ⊤).toLinearMap,
    (SecOn.congr (isLB_tw hA hN _) hB w hw ⊤).injective.comp (hinj.comp (SecOn.twZeroEquiv hA hN ⊤).injective)⟩

theorem Eff.add [IsIntegral X] {a b : Pic X} (ha : Eff a) (hb : Eff b) : Eff (a + b) := by
  obtain ⟨A, hA, rfl, σ, hσ⟩ := ha
  obtain ⟨B, hB, e⟩ := cls_surj (cls A hA + b)
  obtain ⟨φ, hφ⟩ := exists_injective hA hB (by rw [e, add_sub_cancel_left]; exact hb)
  exact ⟨B, hB, e, φ σ, fun h => hσ (hφ (h.trans (map_zero φ).symm))⟩

theorem eff_of_sec {L : LB X} (hL : L.IsLB) (σ : LB.Sec L) (i : L.ι) (h : σ.f i ≠ 0) : Eff (cls L hL) := by
  refine ⟨L, hL, rfl, (SecOn.topEquiv L).symm σ, fun h0 => h ?_⟩
  have : σ = SecOn.topEquiv L 0 := by rw [← h0, LinearEquiv.apply_symm_apply]
  rw [this, SecOn.topEquiv_f]
  exact map_zero _

theorem eff_zero [IsIntegral X] : Eff (0 : Pic X) := by
  have e : cls _ (Inh.trivLB_isLB X) = 0 := (cls_eq_zero_iff _).2 (triv_trivLB X)
  rw [← e]
  refine eff_of_sec _ (oneSec X) PUnit.unit ?_
  exact one_ne_zero (α := Γ(X, ⊤))

theorem Eff.nsmul [IsIntegral X] {a : Pic X} (ha : Eff a) (n : ℕ) : Eff (n • a) := by
  induction n with
  | zero => rw [zero_nsmul]; exact eff_zero
  | succ n ih => rw [succ_nsmul]; exact ih.add ha

theorem eff_pull {Y : Scheme.{0}} [IsIntegral Y] (φ : Y ⟶ X) {H : LB X} (hH : H.IsLB) {I : Type} (s : I → LB.Sec H)
    (hs : ⨆ i, nonzeroLocus (s i) = ⊤) : Eff (pull φ (cls H hH)) := by
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (hs.ge (trivial : φ (genericPoint Y) ∈ ⊤))
  obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 hi
  refine ⟨H.pull φ, pull_isLB hH φ, rfl, SecOn.pullLE H φ ⊤ ⊤ le_top ((SecOn.topEquiv H).symm (s i)), fun h0 => ?_⟩
  have e := SecOn.coord_pullLE (M := H) φ (V := ⊤) (V' := ⊤) le_top ((SecOn.topEquiv H).symm (s i)) (fun _ => k)
  rw [h0, SecOn.topEquiv_symm_apply, GlobalTheory.LB.coord_ofSec] at e
  have e₂ := congrArg Y.basicOpen e
  rw [Scheme.basicOpen_appLE] at e₂
  erw [Scheme.basicOpen_zero, Scheme.basicOpen_res] at e₂
  have hk' := X.basicOpen_le _ hk
  have hm : genericPoint Y ∈ (⊥ : Y.Opens) := by
    rw [e₂]
    exact ⟨⟨trivial, mem_pull.2 hk'⟩, ⟨trivial, hk'⟩, hk⟩
  exact hm

theorem exists_eff_sub [IsIntegral X] {R : Type} [CommRing R] (f : X ⟶ Spec (CommRingCat.of R)) {H : LB X}
    (hH : H.IsLB) {m : ℕ} {s : Fin (m + 1) → LB.Sec H} (hs : VeryAmpleBy f H s) (c : Pic X) :
    ∃ N : ℕ, Eff (N • cls H hH - c) := by
  obtain ⟨M, hM, e⟩ := cls_surj (-c)
  obtain ⟨t₀, ht⟩ := GlobalTheory.T.exists_high_twist_section_ne_zero R X f H m s M hH hM hs
  obtain ⟨σ, i, hσ⟩ := ht (t₀.toNat : ℕ) (Int.self_le_toNat t₀)
  have := eff_of_sec (isLB_tw hM hH _) σ i hσ
  rw [cls_tw hM hH, e, natCast_zsmul] at this
  exact ⟨t₀.toNat, by rwa [sub_eq_neg_add]⟩

theorem finrank_comp {X X' X'' : Scheme.{0}} [IsIntegral X] [IsIntegral X'] [IsIntegral X'']
    (ψ : X'' ⟶ X') (φ : X' ⟶ X) [IsFinite φ] [Flat φ] [Surjective φ] [IsFinite ψ] [Flat ψ] [Surjective ψ]
    {a b c : ℕ} (ha : ∀ x, φ.finrank x = a) (hb : ∀ x, ψ.finrank x = b) (hc : ∀ x, (ψ ≫ φ).finrank x = c) :
    c = b * a := by
  letI : Algebra X.functionField X'.functionField := (functionFieldMap φ).toAlgebra
  letI : Algebra X'.functionField X''.functionField := (functionFieldMap ψ).toAlgebra
  letI : Algebra X.functionField X''.functionField := (functionFieldMap (ψ ≫ φ)).toAlgebra
  have aff : ∀ (Z : Scheme.{0}) [IsIntegral Z], ∃ D : Z.Opens, IsAffineOpen D ∧ genericPoint Z ∈ D := by
    intro Z _
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
      Z.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (genericPoint Z)) isOpen_univ
    exact ⟨U, hU, hxU⟩
  obtain ⟨D, hD, h⟩ := aff X
  obtain ⟨D', hD', h'⟩ := aff X'
  haveI : IsScalarTower X.functionField X'.functionField X''.functionField :=
    IsScalarTower.of_algebraMap_eq' (by
      haveI : Nonempty D := ⟨⟨_, h⟩⟩
      haveI := functionField_isFractionRing_of_isAffineOpen X D hD
      refine IsLocalization.ringHom_ext (nonZeroDivisors Γ(X, D)) (RingHom.ext fun r => ?_)
      have h1 := generic_mem_preimage φ h
      have h2 := generic_mem_preimage ψ h1
      have e1 := toField_appLE φ le_rfl h h1 r
      have e2 := toField_appLE ψ le_rfl h1 h2 ((φ.appLE D _ le_rfl).hom r)
      have e3 := toField_appLE (ψ ≫ φ) (V := ψ ⁻¹ᵁ φ ⁻¹ᵁ D) le_rfl h h2 r
      rw [← Scheme.Hom.appLE_comp_appLE ψ φ D (φ ⁻¹ᵁ D) _ le_rfl le_rfl] at e3
      exact e3.symm.trans (e2.trans (congrArg _ e1)))
  obtain ⟨x, hx⟩ := (chart_data φ (fun _ => rfl) hD h).1
  obtain ⟨y, hy⟩ := (chart_data ψ (fun _ => rfl) hD' h').1
  obtain ⟨z, hz⟩ := (chart_data (ψ ≫ φ) (fun _ => rfl) hD h).1
  rw [← hc z, ← hz, ← ha x, ← hx, ← hb y, ← hy, mul_comm, Module.finrank_mul_finrank]

theorem finrank_le {K : Type} [Field K] [IsIntegral X] (f : X ⟶ Spec (CommRingCat.of K)) {g : ℕ}
    (hg : SmoothOfRelativeDimension g f) {H : LB X} (hH : H.IsLB) {m : ℕ} {s : Fin (m + 1) → LB.Sec H}
    (hs : VeryAmpleBy f H s) : ∃ C : ℕ, ∀ (φ : X ⟶ X) [IsFinite φ] [Flat φ] [Surjective φ], φ ≫ f = f →
      ∀ d : ℕ, (∀ x, φ.finrank x = d) → ∀ M : ℕ, 1 ≤ M → Eff (M • cls H hH - pull φ (cls H hH)) →
        d ≤ C * M ^ g := by
  obtain ⟨hfin, -, c, C, -, hgrow⟩ := GlobalTheory.VeryAmpleGrowth.finite_monotone_growth K X f g hg H m s hH hs
  refine ⟨c * C * 2 ^ g, fun φ _ _ _ hφ d hd M hM he => ?_⟩
  have inj : ∀ t : ℕ, ∃ F : SecOnR (φ ≫ f) ((AbLaw.pw H t).pull φ) ⊤ →ₗ[K]
      SecOnR f (AbLaw.pw H ((M * t : ℕ) : ℤ)) ⊤, Function.Injective F := by
    intro t
    obtain ⟨F, hF⟩ := exists_injective (pull_isLB (isLB_pw hH t) φ) (isLB_pw hH ((M * t : ℕ) : ℤ)) (by
      rw [cls_pull (isLB_pw hH t), cls_pw hH, cls_pw hH, natCast_zsmul, natCast_zsmul, map_nsmul, mul_comm,
        mul_smul, ← smul_sub]
      exact he.nsmul t)
    rw [hφ]
    exact ⟨SecOnR.lin f F, hF⟩
  obtain ⟨a, ha⟩ := sandwich K X X f φ H m s hH hs d hd hfin fun t => by
    obtain ⟨F, hF⟩ := inj t
    haveI := hfin (M * t)
    exact Module.Finite.of_injective F hF
  obtain ⟨F, hF⟩ := inj (a + 1 + a)
  haveI := hfin (M * (a + 1 + a))
  have h1 := (ha (a + 1)).1.trans (LinearMap.finrank_le_finrank_of_injective hF)
  have h2 := (hgrow (a + 1) (by omega)).1
  have h3 := (hgrow (M * (a + 1 + a)) (Nat.mul_pos hM (by omega))).2
  have h4 : (M * (a + 1 + a)) ^ g ≤ (M * (2 * (a + 1))) ^ g :=
    Nat.pow_le_pow_left (Nat.mul_le_mul_left _ (by omega)) _
  refine Nat.le_of_mul_le_mul_right ?_ (pow_pos (show 0 < a + 1 by omega) g)
  calc d * (a + 1) ^ g ≤ d * (c * _) := Nat.mul_le_mul_left _ h2
    _ = c * (d * _) := by ring
    _ ≤ c * (C * (M * (2 * (a + 1))) ^ g) :=
      Nat.mul_le_mul_left _ (h1.trans (h3.trans (Nat.mul_le_mul_left _ h4)))
    _ = _ := by rw [mul_pow, mul_pow]; ring

section Abelian

variable {k : Type} [Field k] [IsAlgClosed k] (B : Over (Spec (CommRingCat.of k))) [GrpObj B] [IsCommMonObj B]

omit [IsAlgClosed k] in
theorem pull_one (c : Pic B.left) (T : Over (Spec (CommRingCat.of k))) : pull (1 : T ⟶ B).left c = 0 := by
  have e : pull (η[B]).left c = 0 := by
    obtain ⟨L, hL, rfl⟩ := cls_surj c
    exact (cls_eq_zero_iff (pull_isLB hL _)).2 (GlobalTheory.SS.HtForm.gen_field (k := k) _ (pull_isLB hL _))
  rw [Hom.one_def, Over.comp_left, pull_comp, e, map_zero]

omit [IsAlgClosed k] in
theorem pull_par {H : LB B.left} (hH : H.IsLB) (hΘ : ∃ t : LB.Gen (Theta B H), t.IsGen)
    (hsym : Triv (LB.LinComb H (K := Fin 2) ![(ι[B]).left, 𝟙 B.left] ![1, -1]))
    {T : Over (Spec (CommRingCat.of k))} (x y : T ⟶ B) :
    pull (x * y).left (cls H hH) + pull (x * y⁻¹).left (cls H hH) =
      2 • pull x.left (cls H hH) + 2 • pull y.left (cls H hH) := by
  have hs := (cls_eq_zero_iff (LB.isLB_linComb hH _ _)).2 hsym
  rw [cls_linComb hH, Fin.sum_univ_two] at hs
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, pull_id, one_zsmul, neg_one_zsmul] at hs
  have hinv : pull (y⁻¹).left (cls H hH) = pull y.left (cls H hH) := by
    rw [Hom.inv_def, Over.comp_left, pull_comp, eq_of_sub_eq_zero ((sub_eq_add_neg _ _).trans hs)]
  have ht := (cls_eq_zero_iff (LB.isLB_linComb hH _ _)).2 hΘ
  rw [cls_linComb hH] at ht
  have this := congrArg (pull (lift x (lift y y⁻¹)).left) ht
  rw [map_zero, map_sum] at this
  simp only [map_zsmul, ← pull_comp, ← Over.comp_left] at this
  have hsum : ∀ F : Finset (Fin 3) → Pic T.left, ∑ I : ULift.{0} (Finset (Fin 3)), F I.down =
      F ∅ + F {0} + F {1} + F {2} + F {0, 1} + F {0, 2} + F {1, 2} + F {0, 1, 2} := fun F => by
    refine (Equiv.ulift.sum_comp F).trans ?_
    have : (Finset.univ : Finset (Finset (Fin 3))) = {∅, {0}, {1}, {2}, {0, 1}, {0, 2}, {1, 2}, {0, 1, 2}} := by
      decide
    rw [this]
    repeat rw [Finset.sum_insert (by decide)]
    rw [Finset.sum_singleton]
    abel
  rw [hsum fun I => ((-1 : ℤ) ^ (3 - I.card)) • pull (lift x (lift y y⁻¹) ≫ psum B (x3 B) I).left (cls H hH)] at this
  have e0 : lift x (lift y y⁻¹) ≫ x3 B 0 = x := by simp [x3]
  have e1 : lift x (lift y y⁻¹) ≫ x3 B 1 = y := by simp [x3]
  have e2 : lift x (lift y y⁻¹) ≫ x3 B 2 = y⁻¹ := by simp [x3]
  have l0 : (List.finRange 3).filter (· ∈ (∅ : Finset (Fin 3))) = [] := by decide
  have l1 : (List.finRange 3).filter (· ∈ ({0} : Finset (Fin 3))) = [0] := by decide
  have l2 : (List.finRange 3).filter (· ∈ ({1} : Finset (Fin 3))) = [1] := by decide
  have l3 : (List.finRange 3).filter (· ∈ ({2} : Finset (Fin 3))) = [2] := by decide
  have l4 : (List.finRange 3).filter (· ∈ ({0, 1} : Finset (Fin 3))) = [0, 1] := by decide
  have l5 : (List.finRange 3).filter (· ∈ ({0, 2} : Finset (Fin 3))) = [0, 2] := by decide
  have l6 : (List.finRange 3).filter (· ∈ ({1, 2} : Finset (Fin 3))) = [1, 2] := by decide
  have l7 : (List.finRange 3).filter (· ∈ ({0, 1, 2} : Finset (Fin 3))) = [0, 1, 2] := by decide
  have c4 : ({0, 1} : Finset (Fin 3)).card = 2 := by decide
  have c5 : ({0, 2} : Finset (Fin 3)).card = 2 := by decide
  have c6 : ({1, 2} : Finset (Fin 3)).card = 2 := by decide
  have c7 : ({0, 1, 2} : Finset (Fin 3)).card = 3 := by decide
  simp only [GlobalTheory.SS.HtForm.comp_psum] at this
  rw [l0, l1, l2, l3, l4, l5, l6, l7, c4, c5, c6, c7] at this
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, e0, e1, e2, _root_.mul_one,
    mul_inv_cancel, pull_one, hinv, Finset.card_singleton, Finset.card_empty] at this
  rw [← sub_eq_zero, ← neg_eq_zero, ← this]
  norm_num
  abel

theorem finrank_const (hB : IsAbelianScheme B) (φ : B ⟶ B) [IsFinite φ.left] [Flat φ.left] (x y : B.left) :
    φ.left.finrank x = φ.left.finrank y := by
  have := hB.geomConnected
  have := hB.smooth
  have : ConnectedSpace B.left := GeometricallyConnected.connectedSpace_of_subsingleton B.hom
  have : IsLocallyNoetherian B.left := LocallyOfFiniteType.isLocallyNoetherian B.hom
  exact (Scheme.Hom.isLocallyConstant_finrank φ.left).apply_eq_of_preconnectedSpace x y

open NumberField in
theorem finrank_act {E : Type} [Field E] [NumberField E] (hB : IsAbelianScheme B) {g : ℕ}
    (hg : SmoothOfRelativeDimension g B.hom) (ρ : OAct (𝓞 E) B) (a : 𝓞 E) (ha : a ≠ 0) :
    ∃ (_ : IsFinite (ρ.act a).left) (_ : Flat (ρ.act a).left), ∀ x,
      (ρ.act a).left.finrank x ^ Module.finrank ℚ E = (Algebra.norm ℤ a).natAbs ^ (2 * g) := by
  have hG := GlobalTheory.globalFns_holds
  haveI := hB.smooth
  haveI := hB.proper
  haveI : GeometricallyIntegral B.hom :=
    GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ _ hB.smooth hB.geomConnected
  haveI : IsIntegral B.left := GeometricallyIntegral.isIntegral_of_subsingleton B.hom
  have hproj := GlobalTheory.T.isProjectiveOverRingByCharts_abelian_variety k B hB
  obtain ⟨H, m, s, hH, hs, hsym⟩ := GlobalTheory.SymVeryAmple.exists_symmetric_veryAmpleBy k B hB hproj
  have hΘ := GlobalTheory.AbLaw.CubeProj.exists_gen_theta_abelianVariety hG k B hB hproj H hH
  let q : 𝓞 E → Pic B.left := fun a => pull (ρ.act a).left (cls H hH)
  have a0 : ρ.act 0 = 1 := by
    have := ρ.add 0 0
    rw [add_zero] at this
    exact mul_eq_left.1 this.symm
  have h0 : q 0 = 0 := by simp only [q, a0, pull_one]
  have h1 : q 1 = cls H hH := by simp only [q, ρ.one, Over.id_left, pull_id]
  have hq : ∀ a b, q (a + b) + q (a - b) = 2 • q a + 2 • q b := fun a b => by
    have e : ρ.act (a - b) = ρ.act a * (ρ.act b)⁻¹ := by
      rw [eq_mul_inv_iff_mul_eq, ← ρ.add, sub_add_cancel]
    simp only [q, ρ.add, e]
    exact pull_par B hH hΘ hsym _ _
  have hw : ∀ a, (ρ.act a).left ≫ B.hom = B.hom := fun a => Over.w _
  have hiso : ∀ n : ℕ, LBIso (AbLaw.pw H ((n ^ 2 : ℕ) : ℤ)) (H.pull (ρ.act n).left) := fun n => by
    refine (cls_eq_iff (isLB_pw hH _) (pull_isLB hH _)).1 ?_
    have e := quad_nat q h0 hq 1 n
    rw [nsmul_one, h1] at e
    rw [cls_pw hH, natCast_zsmul, ← e]
    rfl
  have hfin : ∀ a, a ≠ 0 → IsFinite (ρ.act a).left := fun a ha => by
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {a}))
    have hN : Ideal.absNorm (Ideal.span {a}) ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]; exact ha
    have h := GlobalTheory.T.isFinite_of_pull_veryAmple_iso_pow k _ _ B.hom _ H H m s _ hH hH inferInstance (by rw [hw]; exact hs)
      (Nat.one_le_iff_ne_zero.2 (pow_ne_zero 2 hN)) (hiso _)
    rw [← hb, mul_comm, ρ.mul, Over.comp_left] at h
    haveI : IsSeparated ((ρ.act b).left ≫ B.hom) := by rw [hw]; infer_instance
    haveI : IsSeparated (ρ.act b).left := IsSeparated.of_comp _ B.hom
    exact IsFinite.of_comp _ (ρ.act b).left
  have hfs : ∀ a, a ≠ 0 → Flat (ρ.act a).left ∧ Surjective (ρ.act a).left := fun a ha =>
    haveI := hfin a ha
    haveI := ρ.hom a
    GlobalTheory.flat_and_surjective_of_isFinite_grpEnd k B _
  let deg : 𝓞 E → ℕ := fun a => (ρ.act a).left.finrank (genericPoint B.left)
  have hd : ∀ a, a ≠ 0 → ∀ x, (ρ.act a).left.finrank x = deg a := fun a ha x =>
    haveI := hfin a ha
    haveI := (hfs a ha).1
    finrank_const B hB _ _ _
  obtain ⟨C₁, hC₁⟩ := finrank_le B.hom hg hH hs
  let S : AddSubmonoid (Pic B.left) := ⟨⟨{c | Eff c}, Eff.add⟩, eff_zero⟩
  have hS : ∀ a, q a ∈ S := fun a => eff_pull _ hH s hs.1
  obtain ⟨C₂, hC₂, hb⟩ := quad_bound q h0 hq S _ (h1 ▸ hS 1) hS (fun a => exists_eff_sub B.hom hH hs _)
    (RingOfIntegers.basis E) Finset.univ
  refine ⟨hfin a ha, (hfs a ha).1, fun x => ?_⟩
  rw [hd a ha]
  refine pow_eq_norm deg (2 * g) (C₁ * C₂ ^ g) (fun a b ha hb => ?_) (fun a ha => ?_) (fun n hn => ?_)
    (fun T c hc hx => ?_) a ha
  · haveI := hfin a ha
    haveI := hfin b hb
    obtain ⟨_, _⟩ := hfs a ha
    obtain ⟨_, _⟩ := hfs b hb
    refine finrank_comp (ρ.act a).left (ρ.act b).left (hd b hb) (hd a ha) fun x => ?_
    rw [← Over.comp_left, ← ρ.mul]
    exact hd _ (mul_ne_zero ha hb) x
  · haveI := hfin a ha
    obtain ⟨_, _⟩ := hfs a ha
    exact (ρ.act a).left.one_le_finrank_iff_surjective.2 inferInstance _
  · have hn' : (n : 𝓞 E) ≠ 0 := Nat.cast_ne_zero.2 hn
    haveI := hfin _ hn'
    obtain ⟨_, _⟩ := hfs _ hn'
    obtain ⟨hfin, hmono, c, C, hc1, hgrow⟩ :=
      GlobalTheory.VeryAmpleGrowth.finite_monotone_growth k B.left B.hom g hg H m s hH hs
    have e := TorsionCount.nonempty_secEquiv B.hom _ (hw n) hH (n ^ 2) (hiso n)
    obtain ⟨a, ha⟩ := sandwich k B.left B.left B.hom (ρ.act n).left H m s hH hs _ (hd _ hn') hfin fun t => by
      obtain ⟨e⟩ := e t
      haveI := hfin (n ^ 2 * t)
      exact Module.Finite.equiv e
    rw [pow_mul]
    refine GlobalTheory.UU.degree_eq_pow_of_growth (fun t : ℕ => Module.finrank k (SecOnR B.hom (AbLaw.pw H t) ⊤)) g c C a _
      (n ^ 2) hc1 (Nat.one_le_iff_ne_zero.2 (pow_ne_zero 2 hn)) hmono hgrow fun t => ?_
    obtain ⟨e₁⟩ := e (t + a)
    obtain ⟨e₂⟩ := e t
    exact ⟨(ha t).1.trans e₁.finrank_eq.ge, e₂.finrank_eq.le.trans (ha t).2⟩
  · haveI := hfin _ hx
    obtain ⟨_, _⟩ := hfs _ hx
    have hT : 1 ≤ T := by
      by_contra hT
      refine hx (Finset.sum_eq_zero fun i _ => ?_)
      have := hc i
      rw [show c i = 0 by omega, zero_smul]
    have := hC₁ _ (hw _) _ (hd _ hx) (C₂ * T ^ 2) (Nat.mul_pos hC₂ (pow_pos hT 2)) (hb T c hc)
    rwa [mul_pow, ← pow_mul, ← _root_.mul_assoc] at this

end Abelian

theorem card_eq_of_isLieBasis {W : Type} [CommRing W] [IsLocalRing W] {G : Over (Sp W)} [GrpObj G] [Smooth G.hom]
    {n d : ℕ} {u : Fin n → (epsR W ⟶ G)} {v : Fin d → (epsR W ⟶ G)} (hu : IsLieBasis u) (hv : IsLieBasis v) :
    n = d := by
  choose U hU using fun i => (hv.2 _ (hu.1 i)).exists
  have key := ReciprocityTheory.ChartRestriction.G.Chart.coords_basis hv hu U hU
  let l : (Fin n → W) →ₗ[W] (Fin d → W) := Matrix.vecMulLinear (Matrix.of U)
  have hl : ∀ a j, l a j = ∑ i, a i * U i j := fun a j => rfl
  have hb : Function.Bijective l := by
    refine ⟨fun a a' e => ?_, fun z => ?_⟩
    · exact (key (l a)).unique (fun j => (hl a j).symm) (fun j => ((hl a' j).symm.trans (congrFun e.symm j)))
    · obtain ⟨a, ha, -⟩ := key z
      exact ⟨a, funext fun j => (hl a j).trans (ha j)⟩
  simpa using (LinearEquiv.ofBijective l hb).finrank_eq

theorem prod_left_congr {S X : Scheme.{0}} {G : Over S} [GrpObj G] {a b : X ⟶ S} (h : a = b) {n : ℕ}
    (u : Fin n → (Over.mk a ⟶ G)) (u' : Fin n → (Over.mk b ⟶ G)) (hu : ∀ i, (u i).left = (u' i).left) :
    (List.ofFn u).prod.left = (List.ofFn u').prod.left := by
  subst h
  rw [show u = u' from funext fun i => Over.OverMorphism.ext (hu i)]

section Bridge

open NumberField Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S : Type} [CommRing S] (t : SAB H (Sp S))

theorem isTanAtG_id (v : epsR S ⟶ t.G) : IsTanAtG t (𝟙 _) v.left ↔ IsTangent v := by
  have e : (1 : Over.mk (𝟙 (Sp S)) ⟶ t.G).left = η[t.G].left := by
    rw [Hom.one_def, show toUnit (Over.mk (𝟙 (Sp S))) = 𝟙 (𝟙_ (Over (Sp S))) from toUnit_unique _ _]
    exact congrArg (·.left) (Category.id_comp η[t.G])
  exact ⟨fun h => h.2.trans e, fun h => ⟨(Over.w v).trans (Category.comp_id _).symm, Eq.trans h e.symm⟩⟩

theorem isCombAtG_id {n : ℕ} (v : Fin n → (epsR S ⟶ t.G)) (cf : Fin n → S) (w : epsR S ⟶ t.G) :
    IsCombAtG t (𝟙 _) (fun i => (v i).left) cf w.left ↔ IsLieComb cf v w := by
  have e := Category.comp_id (spMap (algebraMap S (DualNumber S)))
  constructor
  · rintro ⟨u, hu, h⟩
    refine ⟨fun i => Over.homMk (u i).left ((Over.w (u i)).trans e), hu, Over.OverMorphism.ext (h.symm.trans ?_)⟩
    exact prod_left_congr e _ _ fun _ => rfl
  · rintro ⟨u, hu, rfl⟩
    refine ⟨fun i => Over.homMk (u i).left ((Over.w (u i)).trans e.symm), hu, ?_⟩
    exact prod_left_congr e _ _ fun _ => rfl

theorem dim_eq [IsLocalRing S] [StarRing (𝓞 E)] {d g : ℕ} (gm₀ : GlobalTheory.CompanionTheory.Ar.Conj.GermAt t (𝟙 (Sp S)) d)
    (hg : SmoothOfRelativeDimension g t.G.hom) : g = d := by
  haveI := t.semi.smooth
  obtain ⟨u, hu⟩ := GlobalTheory.KeyPow.exists_isLieBasis t.G hg
  let v : Fin d → (epsR S ⟶ t.G) := fun l => Over.homMk (gm₀.tg l) ((gm₀.tan l).1.trans (Category.comp_id _))
  refine card_eq_of_isLieBasis hu (v := v) ⟨fun l => (isTanAtG_id t (v l)).1 (gm₀.tan l), fun w hw => ?_⟩
  exact (existsUnique_congr fun cf => isCombAtG_id t v cf w).1 (gm₀.basis _ ((isTanAtG_id t w).2 hw))

end Bridge

theorem exists_fibre {X Y : Scheme.{0}} (f : X ⟶ Y) [IsFinite f] (k : Type) [Field k] (y : Sp k ⟶ Y) :
    ∃ (A : Type) (_ : CommRing A) (_ : Algebra k A) (_ : Module.Finite k A) (i : Sp A ⟶ X),
      IsPullback i (spMap (algebraMap k A)) f y := by
  haveI : IsAffine (pullback f y) := isAffine_of_isAffineHom (pullback.snd f y)
  let P := pullback f y
  let g' : Spec Γ(P, ⊤) ⟶ Sp k := P.isoSpec.inv ≫ pullback.snd f y
  haveI : IsFinite g' := inferInstance
  obtain ⟨φ, hφ⟩ := Spec.map_surjective g'
  have hφf : φ.hom.Finite := by
    rw [← IsFinite.SpecMap_iff, hφ]
    infer_instance
  letI : Algebra k Γ(P, ⊤) := φ.hom.toAlgebra
  refine ⟨Γ(P, ⊤), inferInstance, inferInstance, hφf, P.isoSpec.inv ≫ pullback.fst f y, ?_⟩
  exact (IsPullback.of_hasPullback f y).of_iso P.isoSpec (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by simp) (by
      change pullback.snd f y ≫ 𝟙 _ = P.isoSpec.hom ≫ Spec.map φ
      rw [hφ]; simp [g']) (by simp) (by simp)

theorem finrank_fibre {X Y : Scheme.{0}} (f : X ⟶ Y) [IsFinite f] [Flat f] (k : Type) [Field k] (y : Sp k ⟶ Y)
    (A : Type) [CommRing A] [Algebra k A] [Module.Finite k A] (i : Sp A ⟶ X)
    (h : IsPullback i (spMap (algebraMap k A)) f y) : ∃ x, Module.finrank k A = f.finrank x := by
  refine ⟨y (⊥ : PrimeSpectrum k), ?_⟩
  rw [← rankAtStalk_bot]
  exact (Scheme.Hom.finrank_SpecMap_algebraMap k A _).symm.trans (Scheme.Hom.finrank_of_isPullback _ _ _ _ h _)

end Bundles

end PositivityTheory.Xgn.DegreeMultiplicationNorm

end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem PositivityTheory.Xgn.degree_multiplication_norm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (k : Type) [Field k] [IsAlgClosed k] (t : SAB H (Sp k)), IsProper t.G.hom → ∀ (d : ℕ) (_ : GermAt t (𝟙 (Sp k)) d) (a : 𝓞 E), a ≠ 0 → (∃ (A : Type) (_ : CommRing A) (_ : Algebra k A) (_ : Module.Finite k A) (i : Sp A ⟶ t.G.left), IsPullback i (spMap (algebraMap k A)) (t.act.act a).left (η[t.G]).left) ∧ ∀ (A : Type) [CommRing A] [Algebra k A] [Module.Finite k A] (i : Sp A ⟶ t.G.left), IsPullback i (spMap (algebraMap k A)) (t.act.act a).left (η[t.G]).left → Module.finrank k A ^ Module.finrank ℚ E = (Algebra.norm ℤ a).natAbs ^ (2 * d) := by
  intro E _ _ _ H _ _ k _ _ t hp d gm₀ a ha
  have hB : IsAbelianScheme t.G := ⟨t.comm, t.semi.smooth, hp, t.semi.geomConnected⟩
  obtain ⟨g, hg⟩ := GlobalTheory.AbelianDim.exists_relDim k t.G hB
  obtain rfl := PositivityTheory.Xgn.DegreeMultiplicationNorm.dim_eq t gm₀ hg
  obtain ⟨_, _, h⟩ := PositivityTheory.Xgn.DegreeMultiplicationNorm.finrank_act t.G hB hg t.act a ha
  refine ⟨PositivityTheory.Xgn.DegreeMultiplicationNorm.exists_fibre _ k _, fun A _ _ _ i hi => ?_⟩
  obtain ⟨x, hx⟩ := PositivityTheory.Xgn.DegreeMultiplicationNorm.finrank_fibre _ k _ A i hi
  rw [hx]
  exact h x
