import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.SubThickRees
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.IsCompl
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Polynomial DividedPowers GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.B

namespace GlobalTheory.CompanionTheory.EtaleLift

theorem existsUnique_lift_of_nilpotent {P E C D : Type} [CommRing P] [CommRing E] [CommRing C] [CommRing D]
    (ψ : P →+* E) (hψ : ψ.Etale) (u : C →+* D) (hu : Function.Surjective u)
    (hn : IsNilpotent (RingHom.ker u)) (f : P →+* C) (g : E →+* D) (h : g.comp ψ = u.comp f) :
    ∃! l : E →+* C, l.comp ψ = f ∧ u.comp l = g := by
  letI : Algebra P E := ψ.toAlgebra
  letI : Algebra P C := f.toAlgebra
  letI : Algebra P D := (u.comp f).toAlgebra
  haveI : Algebra.Etale P E := hψ
  let uA : C →ₐ[P] D := { u with commutes' := fun _ => rfl }
  let gA : E →ₐ[P] D := { g with commutes' := fun r => congrArg (fun t : P →+* D => t r) h }
  have hn₁ : IsNilpotent (RingHom.ker (uA : C →+* D)) := hn
  have hn₂ : IsNilpotent (RingHom.ker uA) := hn
  let lA : E →ₐ[P] C := Algebra.FormallySmooth.liftOfSurjective gA uA hu hn₁
  have hl : ∀ x, u (lA x) = g x := fun x =>
    Algebra.FormallySmooth.liftOfSurjective_apply gA uA hu hn₂ x
  refine ⟨(lA : E →+* C), ⟨RingHom.ext fun r => lA.commutes r, RingHom.ext hl⟩, ?_⟩
  rintro l' ⟨h1, h2⟩
  let lA' : E →ₐ[P] C := { l' with commutes' := fun r => congrArg (fun t : P →+* C => t r) h1 }
  have : lA' = lA := Algebra.FormallyUnramified.ext' u hn lA' lA fun x => by
    rw [hl]; exact congrArg (fun t : E →+* D => t x) h2
  exact congrArg (fun t : E →ₐ[P] C => (t : E →+* C)) this

variable {B : Type} [CommRing B] (J : Ideal B)

abbrev toBase (n : ℕ) : B ⧸ J ^ (n + 1) →+* B ⧸ J :=
  Ideal.Quotient.factor (Ideal.pow_le_self (Nat.succ_ne_zero n))

theorem toBase_mk (n : ℕ) (x : B) : toBase J n (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk J x := rfl

theorem isNilpotent_ker_toBase (n : ℕ) : IsNilpotent (RingHom.ker (toBase J n)) := by
  refine ⟨n + 1, ?_⟩
  have hk : RingHom.ker (toBase J n) = J.map (Ideal.Quotient.mk (J ^ (n + 1))) := by
    rw [Ideal.Quotient.factor_ker]
  rw [hk, ← Ideal.map_pow]
  simp

theorem existsUnique_level {P E : Type} [CommRing P] [CommRing E] (ψ : P →+* E) (hψ : ψ.Etale)
    (f : P →+* B) (g : E →+* B ⧸ J) (h : g.comp ψ = (Ideal.Quotient.mk J).comp f) (n : ℕ) :
    ∃! l : E →+* B ⧸ J ^ (n + 1), l.comp ψ = (Ideal.Quotient.mk _).comp f ∧ (toBase J n).comp l = g :=
  existsUnique_lift_of_nilpotent ψ hψ (toBase J n) (Ideal.Quotient.factor_surjective _)
    (isNilpotent_ker_toBase J n) _ g h

theorem iInf_pow_eq_bot (hJ : IsAdicComplete J B) : ⨅ i : ℕ, J ^ i = ⊥ := by
  refine eq_bot_iff.2 fun x hx => ?_
  refine (Ideal.mem_bot).2 (IsHausdorff.haus hJ.toIsHausdorff x fun n => ?_)
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
  exact (Ideal.mem_iInf.1 hx) n

end GlobalTheory.CompanionTheory.EtaleLift

open GlobalTheory.CompanionTheory.EtaleLift in

theorem GlobalTheory.CompanionTheory.EtaleLift.etLift_of_isAdicComplete :
    ∀ {B : Type} [CommRing B] (J : Ideal B), IsAdicComplete J B → EtLift J := by
  intro B _ J hJ P E _ _ ψ hψ f g h
  haveI := hJ
  choose l hl hu using existsUnique_level J ψ hψ f g h
  have hcomp : ∀ {m n : ℕ} (hle : m ≤ n), (Ideal.Quotient.factorPow J (Nat.succ_le_succ hle)).comp (l n) = l m := by
    intro m n hle
    refine (hu m _ ⟨?_, ?_⟩).symm ▸ rfl
    · rw [RingHom.comp_assoc, (hl n).1]
      rfl
    · rw [← (hl n).2, ← RingHom.comp_assoc]
      congr 1
      exact Ideal.Quotient.ringHom_ext (RingHom.ext fun _ => rfl)
  let F : (n : ℕ) → E →+* B ⧸ J ^ n := fun n => (Ideal.Quotient.factorPow J (Nat.le_succ n)).comp (l n)
  have hF : ∀ {m n : ℕ} (hle : m ≤ n), (Ideal.Quotient.factorPow J hle).comp (F n) = F m := by
    intro m n hle
    simp only [F]
    rw [← hcomp hle, ← RingHom.comp_assoc, ← RingHom.comp_assoc]
    congr 1
    exact Ideal.Quotient.ringHom_ext (RingHom.ext fun _ => rfl)
  let H : E →+* B := IsAdicComplete.liftRingHom J F hF
  have hH : ∀ n x, Ideal.Quotient.mk (J ^ n) (H x) = F n x := fun n x =>
    IsAdicComplete.mk_liftRingHom J F hF n x
  have h1 : H.comp ψ = f := by
    ext p
    rw [← sub_eq_zero]
    refine IsHausdorff.haus hJ.toIsHausdorff _ fun n => ?_
    rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, ← Ideal.Quotient.eq_zero_iff_mem, map_sub,
      RingHom.comp_apply, hH, sub_eq_zero]
    have := congrArg (fun t : P →+* B ⧸ J ^ (n + 1) => Ideal.Quotient.factorPow J (Nat.le_succ n) (t p)) (hl n).1
    exact this
  have h2 : (Ideal.Quotient.mk J).comp H = g := by
    ext x
    have e1 : (toBase J 0).comp (Ideal.Quotient.factorPow J (Nat.le_succ 1)) = toBase J 1 :=
      Ideal.Quotient.ringHom_ext (RingHom.ext fun _ => rfl)
    have e2 : Ideal.Quotient.mk J (H x) = toBase J 0 (F 1 x) := by
      rw [← hH 1 x]
      rfl
    rw [RingHom.comp_apply, e2, ← (hl 1).2, ← e1]
    rfl
  refine ⟨H, ⟨h1, h2⟩, ?_⟩
  rintro H' ⟨h1', h2'⟩
  letI : Algebra P E := ψ.toAlgebra
  letI : Algebra P B := f.toAlgebra
  haveI : Algebra.Etale P E := hψ
  let A : E →ₐ[P] B := { H with commutes' := fun r => congrArg (fun t : P →+* B => t r) h1 }
  let A' : E →ₐ[P] B := { H' with commutes' := fun r => congrArg (fun t : P →+* B => t r) h1' }
  have : A' = A := Algebra.FormallyUnramified.ext_of_iInf J (iInf_pow_eq_bot J hJ) fun x => by
    exact (congrArg (fun t : E →+* B ⧸ J => t x) h2').trans (congrArg (fun t : E →+* B ⧸ J => t x) h2).symm
  exact congrArg (fun t : E →ₐ[P] B => (t : E →+* B)) this
