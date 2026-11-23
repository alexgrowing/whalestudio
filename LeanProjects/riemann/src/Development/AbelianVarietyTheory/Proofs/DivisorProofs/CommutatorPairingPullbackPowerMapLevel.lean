import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompEqOneOfTransl
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ConstGen
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGenMovePow
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.BiadditiveOfTrivAxes
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueWeilIs
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilIsDiagRoot
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

noncomputable section

namespace GlobalTheory.HeckePullLevel

open GlobalTheory.CechPic

theorem isMonHom_id_pow {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G] (n : ℕ) :
    IsMonHom ((𝟙 G) ^ n : G ⟶ G) := by
  induction n with
  | zero => rw [pow_zero, Hom.one_def]; infer_instance
  | succ n ih => rw [pow_succ, Hom.mul_def]; infer_instance

theorem weilIs_powPull : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (H₀ : LB A.left) (P : LB (G2 A).left), IsAbelianScheme A → H₀.IsLB → Out.RelAmple A H₀ → P.IsLB → (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → ∀ (m a b : ℕ) (n : ℤ) (T : Over S) (x₁ x₂ y₁ y₂ : T ⟶ A) (c : Γ(T.left, ⊤)ˣ), Out.WeilIs (G2 A) (GlobalTheory.UPel.HT.Hecke.lbPow P m) n (lift (x₁ ^ a) (x₂ ^ b)) (lift (y₁ ^ a) (y₂ ^ b)) c → Out.WeilIs (G2 A) P (n * ((m * a * b : ℕ) : ℤ)) (lift x₁ x₂) (lift y₁ y₂) c := by
  intro S A _ _ H₀ P hA hH hamp hP h₁ h₂ m a b n T x₁ x₂ y₁ y₂ c h
  have hG : Out.GlobalFnsSt := GlobalTheory.globalFns_holds
  have hAA : IsAbelianScheme (G2 A) := ReciprocityTheory.ChartRestriction.G.Geo.Tor.AbelianSchemeGerms.isAbelianScheme_tensor A A hA hA
  have hB : ∀ (T : Over S) (x x' y : T ⟶ A),
      DiagPairing.pc hP (x * x') y = DiagPairing.pc hP x y + DiagPairing.pc hP x' y := fun T x x' y => by
    obtain ⟨t, ht⟩ := (GlobalTheory.Biadditive.biadditive_of_triv_axes hG S A H₀ hA hH hamp P hP h₁ h₂ T x x' y).1
    have e := (cls_eq_zero_iff (LB.isLB_linComb hP _ _)).2 ⟨t, ht⟩
    rw [cls_linComb hP, Fin.sum_univ_three] at e
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons, one_smul, neg_smul] at e
    unfold DiagPairing.pc
    rw [← sub_eq_zero, ← e]
    abel
  have hB' : ∀ (T : Over S) (x y y' : T ⟶ A),
      DiagPairing.pc hP x (y * y') = DiagPairing.pc hP x y + DiagPairing.pc hP x y' := fun T x y y' => by
    obtain ⟨t, ht⟩ := (GlobalTheory.Biadditive.biadditive_of_triv_axes hG S A H₀ hA hH hamp P hP h₁ h₂ T y y' x).2
    have e := (cls_eq_zero_iff (LB.isLB_linComb hP _ _)).2 ⟨t, ht⟩
    rw [cls_linComb hP, Fin.sum_univ_three] at e
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons, one_smul, neg_smul] at e
    unfold DiagPairing.pc
    rw [← sub_eq_zero, ← e]
    abel
  haveI := isMonHom_id_pow A a
  haveI := isMonHom_id_pow A b
  let ψ : G2 A ⟶ G2 A := lift (fst A A ≫ (𝟙 A) ^ a) (snd A A ≫ (𝟙 A) ^ b)
  have e : ∀ {T : Over S} (u v : T ⟶ A), lift u v ≫ ψ = lift (u ^ a) (v ^ b) := fun u v => by
    simp only [ψ, comp_lift, ← Category.assoc, MonObj.comp_pow, Category.comp_id, lift_fst, lift_snd]
  have hM : (GlobalTheory.UPel.HT.Hecke.lbPow P m).IsLB := LB.isLB_linComb hP _ _
  have hψ : pull ψ.left (cls P hP) = (a * b) • cls P hP := by
    have e₀ : ψ = lift (fst A A ^ a) (snd A A ^ b) := by
      rw [← e (fst A A) (snd A A), lift_fst_snd, Category.id_comp]
    rw [e₀]
    change DiagPairing.pc hP (fst A A ^ a) (snd A A ^ b) = _
    rw [DiagPairing.pc_pow_left hP hB, DiagPairing.pc_pow_right hP hB', DiagPairing.pc, lift_fst_snd,
      Over.id_left, pull_id, smul_smul, mul_comm]
  have hw : LBIso (lbPow P (m * a * b)) ((GlobalTheory.UPel.HT.Hecke.lbPow P m).pull ψ.left) := by
    refine (cls_eq_iff (LB.isLB_linComb hP _ _) (pull_isLB hM _)).1 ?_
    have hc : cls _ hM = m • cls P hP := by
      refine (cls_linComb hP (K := Fin m) (fun _ => 𝟙 (G2 A).left) (fun _ => 1) hM).trans ?_
      simp only [pull_id, one_smul, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    rw [cls_lbPow hP, cls_pull hM, hc, map_nsmul, hψ, smul_smul]
    congr 1
    ring
  have h' : Out.WeilIs (G2 A) (GlobalTheory.UPel.HT.Hecke.lbPow P m) n (lift x₁ x₂ ≫ ψ) (lift y₁ y₂ ≫ ψ) c := by
    rw [e, e]; exact h
  exact WeilIsogeny.weilIs_pull_hom hG hAA hP hM ψ hw h'

end GlobalTheory.HeckePullLevel
