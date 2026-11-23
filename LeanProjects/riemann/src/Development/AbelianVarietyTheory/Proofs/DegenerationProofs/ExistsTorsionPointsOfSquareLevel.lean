import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Definitions.Degenerations.RigGen
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUnivBasis
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsVVGenOfIsThetaFamily
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ThetaReal

noncomputable section

namespace GlobalTheory.SquareLevel

open GlobalTheory.ThetaCoord

def halves (g : ℕ) : Fin g ⊕ Fin g ≃ Fin (2 * g) := finSumFinEquiv.trans (finCongr (two_mul g).symm)

theorem halves_inl (g : ℕ) (i : Fin g) : (halves g (.inl i) : ℕ) = i := rfl

theorem halves_inr (g : ℕ) (i : Fin g) : (halves g (.inr i) : ℕ) = g + i := rfl

theorem labelSymp_eq (g M : ℕ) (a b : Fin g ⊕ Fin g → ZMod M) :
    labelSymp (a ∘ (halves g).symm) (b ∘ (halves g).symm) = eStd g M a b := by
  have h₁ : ∀ i j : Fin g, stdSymp g (halves g (.inl i)) (halves g (.inl j)) = 0 := fun i j => by
    have := i.2; have := j.2
    rw [stdSymp, halves_inl, halves_inl, if_neg (by omega), if_neg (by omega)]
  have h₂ : ∀ i j : Fin g, stdSymp g (halves g (.inl i)) (halves g (.inr j)) = if i = j then 1 else 0 := fun i j => by
    have := i.2; have := j.2
    rw [stdSymp, halves_inl, halves_inr]
    by_cases h : i = j
    · rw [if_pos h, if_pos (by subst h; omega)]
    · have : (i : ℕ) ≠ j := fun q => h (Fin.ext q)
      rw [if_neg h, if_neg (by omega), if_neg (by omega)]
  have h₃ : ∀ i j : Fin g, stdSymp g (halves g (.inr i)) (halves g (.inl j)) = if i = j then -1 else 0 := fun i j => by
    have := i.2; have := j.2
    rw [stdSymp, halves_inl, halves_inr]
    by_cases h : i = j
    · rw [if_pos h, if_neg (by omega), if_pos (by subst h; omega)]
    · have : (i : ℕ) ≠ j := fun q => h (Fin.ext q)
      rw [if_neg h, if_neg (by omega), if_neg (by omega)]
  have h₄ : ∀ i j : Fin g, stdSymp g (halves g (.inr i)) (halves g (.inr j)) = 0 := fun i j => by
    have := i.2; have := j.2
    rw [stdSymp, halves_inr, halves_inr, if_neg (by omega), if_neg (by omega)]
  rw [labelSymp, ← (halves g).sum_comp]
  simp_rw [← (halves g).sum_comp]
  simp [Fintype.sum_sum_type, h₁, h₂, h₃, h₄, eStd, sub_eq_add_neg, Finset.sum_add_distrib, add_comm]

variable {S : Scheme.{0}}

theorem linComb_pow_left {A : Over S} [GrpObj A] [IsCommMonObj A] {T : Over S} {n : ℕ} (y : Fin n → (T ⟶ A))
    (c : Fin n → ℕ) (M : ℕ) : linComb (fun i => y i ^ M) c = linComb y (fun i => M * c i) := by
  simp only [linComb, pow_mul]

theorem linComb_pow_right {A : Over S} [GrpObj A] [IsCommMonObj A] {T : Over S} {n : ℕ} (y : Fin n → (T ⟶ A))
    (c : Fin n → ℕ) (M : ℕ) : linComb y c ^ M = linComb y (fun i => M * c i) := by
  simp only [linComb, List.prod_ofFn, ← Finset.prod_pow, ← pow_mul, Nat.mul_comm]

theorem comp_linComb {A : Over S} [GrpObj A] [IsCommMonObj A] {T T' : Over S} (h : T' ⟶ T) {n : ℕ}
    (y : Fin n → (T ⟶ A)) (c : Fin n → ℕ) : h ≫ linComb y c = linComb (fun i => h ≫ y i) c := by
  let F : (T ⟶ A) →* (T' ⟶ A) := MonoidHom.mk' (h ≫ ·) (fun a b => MonObj.comp_mul _ _ _)
  simp only [linComb, List.prod_ofFn]
  exact (map_prod F _ _).trans (Finset.prod_congr rfl fun i _ => map_pow F _ _)

theorem existsUnique_lab {A : Over S} [GrpObj A] [IsCommMonObj A] {T : Over S} {n M : ℕ} [NeZero M]
    (y : Fin n → (T ⟶ A)) (hy : ∀ i, y i ^ (M ^ 2) = 1)
    (ind : ∀ c c' : Fin n → Fin (M ^ 2), linComb y (fun i => (c i : ℕ)) = linComb y (fun i => (c' i : ℕ)) → c = c')
    (z : T ⟶ A) (hz : z ^ M = 1) (sp : ∃ c : Fin n → Fin (M ^ 2), linComb y (fun i => (c i : ℕ)) = z) :
    ∃! a : Fin n → ZMod M, lab (fun i => y i ^ M) a = z := by
  have hM : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
  have lt : ∀ a : ZMod M, M * a.val < M ^ 2 := fun a => by
    rw [sq]; exact Nat.mul_lt_mul_of_pos_left (ZMod.val_lt a) hM
  refine existsUnique_of_exists_of_unique ?_ fun a b ha hb => ?_
  · obtain ⟨c, hc⟩ := sp
    have h₀ := ind (fun i => ⟨(M * c i) % M ^ 2, Nat.mod_lt _ (pow_pos hM 2)⟩) (fun _ => ⟨0, pow_pos hM 2⟩) (by
      have e : linComb y (fun i => (M * c i) % M ^ 2) = linComb y (fun i => M * c i) := by
        simp only [linComb]
        exact congrArg (fun f => (List.ofFn f).prod) (funext fun i => (pow_eq_pow_mod _ (hy i)).symm)
      refine e.trans ?_
      rw [← linComb_pow_right, hc, hz]
      simp [linComb])
    have h₁ : ∀ i, M ∣ (c i : ℕ) := fun i => by
      have q : (M * c i) % M ^ 2 = 0 := congrArg Fin.val (congrFun h₀ i)
      exact Nat.dvd_of_mul_dvd_mul_left hM (sq M ▸ Nat.dvd_of_mod_eq_zero q)
    refine ⟨fun i => ((c i : ℕ) / M : ℕ), (linComb_pow_left _ _ _).trans
      ((congrArg (linComb y) (funext fun i => ?_)).trans hc)⟩
    rw [ZMod.val_cast_of_lt (Nat.div_lt_of_lt_mul (sq M ▸ (c i).2)), Nat.mul_div_cancel' (h₁ i)]
  · have h := ind (fun i => ⟨_, lt (a i)⟩) (fun i => ⟨_, lt (b i)⟩)
      ((linComb_pow_left _ _ _).symm.trans ((ha.trans hb.symm).trans (linComb_pow_left _ _ _)))
    funext i
    exact ZMod.val_injective M (Nat.eq_of_mul_eq_mul_left hM (congrArg Fin.val (congrFun h i)))

theorem weilIs_pow_pow (hW : WeilSt) [IsLocallyNoetherian S] (P : PolAV S) {M : ℕ} {T : Over S}
    (hu : IsUnit (M : Γ(T.left, ⊤))) {x y : T ⟶ P.A} {c : Γ(T.left, ⊤)ˣ} (hM : 1 ≤ M) (hx : x ^ (M ^ 2) = 1)
    (hy : y ^ (M ^ 2) = 1) (H : WeilIs P.A P.L (M ^ 2 : ℕ) x y c) :
    WeilIs P.A P.L M (x ^ M) (y ^ M) (c ^ M) := by
  have H' := CommPairing.weilIs_symm P.isLB H
  have k : ∀ n, WeilIs P.A P.L (M ^ 2 : ℕ) (y ^ (n + 1)) x (c⁻¹ ^ (n + 1)) := fun n => by
    induction n with
    | zero => simpa using H'
    | succ n ih => rw [pow_succ y, pow_succ c⁻¹]; exact (hW S P _ T).2.1 _ _ _ _ _ ih H'
  have k' := CommPairing.weilIs_symm P.isLB (k (M - 1))
  rw [Nat.sub_add_cancel hM, inv_pow, inv_inv] at k'
  refine ((hW S P M T).2.2.2 M x _ _ (by rw [Nat.cast_mul]; exact hu.mul hu) (by rw [← sq, hx])
    (by rw [← pow_mul, ← sq, hy])).1 ?_
  rwa [← Nat.cast_mul, ← sq]

end GlobalTheory.SquareLevel

namespace GlobalTheory

open SquareLevel ThetaCoord in

theorem exists_torsionPoints_of_squareLevel : Laws → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (M : ℕ) (ze : Γ(S, ⊤)ˣ), 1 ≤ M → IsUnit (M : Γ(S, ⊤)) → ∀ lev : Out.Level P (M ^ 2) ze, ∃ pt : (Fin P.g ⊕ Fin P.g → ZMod M) → (baseOver S ⟶ P.A), (∀ a b, pt (a + b) = pt a * pt b) ∧ (∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ S) (z : Over.mk x ⟶ P.A), z ^ M = 1 → ∃! a, (Over.homMk x (by simp) : Over.mk x ⟶ baseOver S) ≫ pt a = z) ∧ (∀ a b, WeilIs P.A P.L (M : ℕ) (pt a) (pt b) (ze ^ (M * (eStd P.g M a b).val))) ∧ (∀ a, ∃ y : baseOver S ⟶ P.A, y ^ (M ^ 2) = 1 ∧ y ^ M = pt a) ∧ ∀ (i : Fin P.g) (i₁ i₂ : Fin (2 * P.g)), (i₁ : ℕ) = i → (i₂ : ℕ) = i + P.g → pt (Pi.single (.inl i) 1) = lev.pt i₁ ^ M ∧ pt (Pi.single (.inr i) 1) = lev.pt i₂ ^ M := by
  intro hL S _ P M ze hM hu lev
  have : NeZero M := ⟨by omega⟩
  have hq : ∀ i, (lev.pt i ^ M) ^ M = 1 := fun i => by rw [← pow_mul, ← sq, lev.torsion]
  refine ⟨fun a => lab (fun i => lev.pt i ^ M) (a ∘ (halves P.g).symm), fun a b => lab_add hq _ _,
    fun K _ _ x z hz => ?_, fun a b => ?_, fun a => ?_, fun i i₁ i₂ h₁ h₂ => ?_⟩
  · have H := existsUnique_lab (M := M)
      (fun i => (Over.homMk x (by simp) : Over.mk x ⟶ baseOver S) ≫ lev.pt i)
      (fun i => by rw [← MonObj.comp_pow, lev.torsion, MonObj.comp_one]) (lev.indep K x) z hz
      (lev.span K x z (by rw [sq, pow_mul, hz, one_pow]))
    refine ((Equiv.arrowCongr (halves P.g) (Equiv.refl (ZMod M))).existsUnique_congr fun a => ?_).2 H
    rw [lab, comp_linComb]
    simp only [MonObj.comp_pow]
    rfl
  · have hze : (ze ^ M) ^ M = 1 := by rw [← pow_mul, ← sq, lev.prim.pow_eq_one]
    have := weilIs_lab hL.globalFns P (T := baseOver S) hq (ze := ze ^ M) hze (fun i j => by
      have := weilIs_pow_pow hL.weil P (T := baseOver S) hu hM (lev.torsion i) (lev.torsion j) (lev.pairing i j)
      convert this using 1
      show (ze ^ M) ^ stdSymp P.g i j = (ze ^ stdSymp P.g i j) ^ M
      rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm])
      (fun a b => ((hL.weil S P M _).1 _ _ (lab_pow hq a) (lab_pow hq b)).exists)
      (a ∘ (halves P.g).symm) (b ∘ (halves P.g).symm)
    rw [labelSymp_eq] at this
    rw [pow_mul]
    exact this
  · refine ⟨linComb lev.pt fun i => (a ((halves P.g).symm i)).val, ?_, ?_⟩
    · simp only [linComb, List.prod_ofFn, ← Finset.prod_pow]
      exact Finset.prod_eq_one fun i _ => by rw [← pow_mul, Nat.mul_comm, pow_mul, lev.torsion, one_pow]
    exact (linComb_pow_right _ _ _).trans (linComb_pow_left _ _ _).symm
  · have k : ∀ s, lab (fun i => lev.pt i ^ M) ((Pi.single s (1 : ZMod M) : _ → ZMod M) ∘ (halves P.g).symm) =
        lev.pt (halves P.g s) ^ M := fun s => by
      rw [← lab_single (M := M) hq (halves P.g s)]
      congr 1
      funext j
      simp [Pi.single_apply, Equiv.symm_apply_eq]
    have e₁ : i₁ = halves P.g (.inl i) := Fin.ext h₁
    have e₂ : i₂ = halves P.g (.inr i) := Fin.ext (h₂.trans (Nat.add_comm _ _))
    rw [e₁, e₂]
    exact ⟨k _, k _⟩

end GlobalTheory

end
