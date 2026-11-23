import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifPowOf3
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifBaseChangeSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdFam
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.BoxLeOfComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.SectionScalarValuation
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueFamOfReps

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FamDimension

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem nonempty_linearEquiv_of_rel {F M N : Type*} [Semiring F] [AddCommMonoid M] [AddCommMonoid N] [Module F M]
    [Module F N] (P : M → N → Prop) (h₁ : ∀ m, ∃! n, P m n) (h₂ : ∀ n, ∃! m, P m n)
    (ha : ∀ m n m' n', P m n → P m' n' → P (m + m') (n + n')) (hs : ∀ (c : F) m n, P m n → P (c • m) (c • n)) :
    Nonempty (M ≃ₗ[F] N) := by
  choose f hf hf' using h₁
  let g : M →ₗ[F] N :=
    { toFun := f
      map_add' := fun m m' => (hf' _ _ (ha _ _ _ _ (hf m) (hf m'))).symm
      map_smul' := fun c m => (hf' _ _ (hs c _ _ (hf m))).symm }
  refine ⟨LinearEquiv.ofBijective g ⟨fun m m' e => ?_, fun n => ?_⟩⟩
  · have e' : f m = f m' := e
    exact (h₂ (f m')).unique (e' ▸ hf m) (hf m')
  · obtain ⟨m, hm, -⟩ := h₂ n
    exact ⟨m, (hf' _ _ hm).symm⟩

section Comb

variable {X Y : Scheme.{0}} {n : ℕ}

def IsComb {M : LB Y} (b : Fin n → LB.Sec M) (a : Fin n → Γ(Y, ⊤)) (s : LB.Sec M) : Prop :=
  ∀ j, s.f j = ∑ i, resTop _ (a i) * (b i).f j

theorem exists_isComb {M : LB Y} (b : Fin n → LB.Sec M) (a : Fin n → Γ(Y, ⊤)) : ∃ s, IsComb b a s :=
  ⟨⟨fun j => ∑ i, resTop _ (a i) * (b i).f j, fun j j' => by
    rw [map_sum, map_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => (SecOps.secScale (a i) (b i)).compat j j'⟩, fun _ => rfl⟩

variable {L : LB X} {K K' : Type} [Fintype K] [Fintype K']

theorem isComb_iff_sval (hL : L.IsLB) {φ : K → (Y ⟶ X)} {ε : K → ℤ} (b : Fin n → LB.Sec (LB.LinComb L φ ε))
    (a : Fin n → Γ(Y, ⊤)) (s : LB.Sec (LB.LinComb L φ ε)) :
    IsComb b a s ↔ ∀ y J, Good L y J →
      sval s (𝟙 Y) y J = ∑ i, gs (𝟙 Y) y ⊤ (a i) * sval (b i) (𝟙 Y) y J := by
  refine ⟨fun h y J hJ => SectionScalarValuation.sval_lin a b h _ y hJ, fun h j => ?_⟩
  obtain ⟨t, ht⟩ := exists_isComb b a
  rw [← ht j]
  exact sec_ext_val hL (fun y J hJ => (h y J hJ).trans (SectionScalarValuation.sval_lin a b ht _ y hJ).symm) j

theorem exists_basis_of_gen (hL : L.IsLB) {K₃ : Type} [Fintype K₃] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ} {φ₃ : K₃ → (Y ⟶ X)} {ε₃ : K₃ → ℤ}
    (u : LB.Gen (LB.LinComb L φ₃ ε₃)) (hu : u.IsGen)
    (h : FormEq (Sum.elim (fun k => 𝟙 Y ≫ φ k) φ₃) (Sum.elim ε ε₃) φ' ε')
    {A : Type} (g : A → Γ(Y, ⊤)) (b : Fin n → LB.Sec (LB.LinComb L φ ε))
    (hb : ∀ s, ∃! c : Fin n → A, IsComb b (fun i => g (c i)) s) :
    ∃ b' : Fin n → LB.Sec (LB.LinComb L φ' ε'), ∀ s, ∃! c : Fin n → A, IsComb b' (fun i => g (c i)) s := by
  have h' : FormEq (Sum.elim (fun k => 𝟙 Y ≫ φ' k) φ₃) (Sum.elim ε' fun k => -ε₃ k) φ ε := fun U _ w => by
    have := h U w
    simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Category.id_comp] at this ⊢
    rw [← this]
    simp only [zpow_neg, Finset.prod_inv_distrib, mul_inv_cancel_right]
  choose b' hb' using fun i => exists_sec hL h (pullMulSec (b i) (𝟙 Y) u hu)
  refine ⟨b', fun s => ?_⟩
  have hu' := invGen_isGen L _ _ u hu
  obtain ⟨t, ht⟩ := exists_sec hL h' (pullMulSec s (𝟙 Y) (LB.invGen L _ _ u) hu')
  refine (existsUnique_congr fun c => ?_).1 (hb t)
  rw [isComb_iff_sval hL, isComb_iff_sval hL]
  refine forall₃_congr fun y J hJ => ?_
  rw [ht _ _ y J hJ, sval_pullMulSec _ _ _ hu' _ y hJ, val_inv, Category.id_comp, Units.mul_inv_eq_iff_eq_mul,
    Finset.sum_mul]
  refine Eq.congr_right (Finset.sum_congr rfl fun i _ => ?_)
  rw [hb' i _ _ y J hJ, sval_pullMulSec _ _ _ hu _ y hJ, Category.id_comp, _root_.mul_assoc]

end Comb

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]

theorem exists_basis_famSec (hT : SecTwistSt) {k : ℕ} (hk : 1 ≤ k) (α : D.X) :
    ∃ b : Fin (k ^ D.P.g) → FamFree.FamSec D F k α,
      ∀ s, ∃! c : Fin (k ^ D.P.g) → F, IsComb b (fun i => gF D F (c i)) s := by
  obtain ⟨⟨b, hb⟩, -⟩ := hT _ D.P k hk F (jFK (R := R) F ≫ jK R) (cP D (TF (R := R) F) α)
  let q : (DegPre.BF D F).left ⟶ (TK R).left := (fst (TF (R := R) F) D.P.A).left ≫ jFK (R := R) F
  let u := LB.pullGen D.P.L _ _ (LB.mulGen D.P.L _ _ _ _ (D.psi α) D.rigK) q
  have hu : u.IsGen := pullGen_isGen _ _ _ _
    (mulGen_isGen _ _ _ _ _ _ _ (D.psi_gen α) (pullGen_isGen _ _ _ _ D.rig_gen _)) _
  refine exists_basis_of_gen D.P.isLB (φ' := DegPre.famφ D F α) (ε' := DegPre.famε k) u hu (fun U _ h => by
      have p := prod_fam D F (𝟙 _) α k h
      simp only [Over.id_left, Category.id_comp] at p
      rw [p]
      have a₁ : q ≫ D.xK α = (cP D (DegPre.BF D F) α).left :=
        congrArg (fun x => x.left) (comp_cP D (fst (TF (R := R) F) D.P.A) α)
      have a₂ : q ≫ (toUnit (TK R)).left ≫ eSec D.P.A = (1 : DegPre.BF D F ⟶ D.P.A).left :=
        congrArg (fun x : DegPre.BF D F ⟶ D.P.A => x.left)
          (MonObj.comp_one (M := D.P.A) (fst (TF (R := R) F) D.P.A))
      have a₃ : translPt D.P.A (cP D (TF (R := R) F) α) = cP D (DegPre.BF D F) α * DegPre.prB D F := by
        rw [translPt, comp_cP]; rfl
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fintype.prod_unique, Fin.prod_univ_two,
        Category.id_comp, a₁, a₂, a₃, Matrix.cons_val_zero, Matrix.cons_val_one, zpow_one, zpow_neg_one]
      rw [← _root_.mul_assoc]) (gF D F) b (fun s => ?_)
  exact (Equiv.existsUnique_congr (Equiv.piCongrRight fun _ : Fin (k ^ D.P.g) =>
      (Scheme.ΓSpecIso (CommRingCat.of F)).symm.commRingCatIsoToRingEquiv.toEquiv) fun _ => Iff.rfl).2 (hb s)

theorem nonempty_fam_equiv (hG : GlobalFnsSt) (hT : SecTwistSt) (hB : D.TauBimult) {k : ℕ} (hk : 1 ≤ k) :
    Nonempty (Fam D F k ≃ₗ[F] (D.X ⧸ FamFree.multiples D k → Fin (k ^ D.P.g) → F)) := by
  let rep : D.X ⧸ FamFree.multiples D k → D.X := Quotient.out
  have hrep : ∀ c, QuotientAddGroup.mk (rep c) = c := fun c => Quotient.out_eq c
  choose b hb using fun c => exists_basis_famSec (D := D) (F := F) hT hk (rep c)
  refine nonempty_linearEquiv_of_rel
    (fun s z => ∀ c, IsComb (b c) (fun i => gF D F (z c i)) (s.s (rep c))) (fun s => ?_) (fun z => ?_) ?_ ?_
  · choose z hz hz' using fun c => hb c (s.s (rep c))
    exact ⟨z, hz, fun z' h => funext fun c => hz' c _ (h c)⟩
  · choose σ hσ using fun c => exists_isComb (b c) (fun i => gF D F (z c i))
    refine (existsUnique_congr fun s => forall_congr' fun c => ?_).1
      (FamFree.existsUnique_fam hG hB hk rep hrep σ)
    exact ⟨fun h => h ▸ hσ c, fun h => SecOps.sec_ext fun j => (h j).trans (hσ c j).symm⟩
  · intro s z s' z' h h' c j
    rw [add_f, h c j, h' c j, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Pi.add_apply, map_add, resTop, add_mul]
  · intro a s z h c j
    rw [smul_f, h c j, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul, map_mul, resTop, _root_.mul_assoc]

theorem finrank_fam (hG : GlobalFnsSt) (hT : SecTwistSt) (hB : D.TauBimult) {k : ℕ} (hk : 1 ≤ k) :
    Module.Finite F (Fam D F k) ∧ Module.finrank F (Fam D F k) = k ^ (D.rank + D.P.g) := by
  obtain ⟨e⟩ := nonempty_fam_equiv (D := D) (F := F) hG hT hB hk
  have hc : Nat.card (D.X ⧸ FamFree.multiples D k) = k ^ D.rank := AddSubgroup.index_range_nsmul D.X k
  have : Finite (D.X ⧸ FamFree.multiples D k) := Nat.finite_of_card_ne_zero (by rw [hc]; positivity)
  have := Fintype.ofFinite (D.X ⧸ FamFree.multiples D k)
  refine ⟨Module.Finite.equiv e.symm, ?_⟩
  rw [e.finrank_eq, Module.finrank_pi_fintype, Finset.sum_const, Module.finrank_fin_fun, Finset.card_univ,
    ← Nat.card_eq_fintype_card, hc, smul_eq_mul, pow_add]

theorem main : GlobalFnsSt → CubeSt → SquareSt → SecTwistSt → ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ), 1 ≤ k → Module.Finite F (Fam D.toPre F k) ∧ Module.finrank F (Fam D.toPre F k) = k ^ (D.toPre.rank + D.toPre.P.g) :=
  fun hG _ _ hT _ _ _ _ D _ _ _ _ hk => finrank_fam hG hT D.tau_bimult hk

end GlobalTheory.FamDimension
