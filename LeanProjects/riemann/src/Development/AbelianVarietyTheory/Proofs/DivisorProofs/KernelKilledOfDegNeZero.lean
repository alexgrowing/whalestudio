import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFactorisationThroughAbelianSubvarietyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFiniteIffFiniteKer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyDimLeOfFiniteAndOfSurjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsogenyCompIffAndDegreeMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsoIffDegEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyIntCastSmulIsogenyDegree
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyFiniteHomKernelKilledByNat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsogenyFlatFinrank
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AV.KerInv

variable {K : Type} [Field K]

theorem eq_one_of_coprime {A B : AbVar K} (f : A ⟶ B) (hf : IsIsogeny f) (m : ℕ) (hm : 0 < m)
    (hcop : Nat.Coprime m (deg f)) {T : Over (Sp K)} (x : T ⟶ A.X)
    (hx : x ≫ f.hom = 1) (hxm : x ^ m = 1) : x = 1 := by
  obtain ⟨C, q, i, hq, hi, hqi⟩ := GlobalTheory.T.exists_factorisation_through_abelianSubvariety K A (prod B A) (prodLift f ((m : ℤ) • 𝟙 A))
  have h1 : q ≫ (i ≫ prodFst B A) = f := by
    rw [← Category.assoc, hqi]
    apply AbVar.hom_ext
    simp [prodLift, prodFst]
    exact lift_fst _ _
  have h2 : q ≫ (i ≫ prodSnd B A) = (m : ℤ) • 𝟙 A := by
    rw [← Category.assoc, hqi]
    apply AbVar.hom_ext
    simp [prodLift, prodSnd]
    exact lift_snd _ _
  have hfin : Finite (ptMap f).ker := (isFinite_iff_finite_ker K A B f).1 hf.1
  have hqfin : IsFinite q.hom.left := by
    rw [isFinite_iff_finite_ker]
    refine Finite.of_injective (β := (ptMap f).ker)
      (fun y => ⟨y.1, ?_⟩) (by intro y z h; simp only [Subtype.mk.injEq] at h; exact Subtype.ext h)
    have hy : y.1 ≫ q.hom = 1 := y.2
    rw [MonoidHom.mem_ker, ptMap_apply, ← h1, comp_hom, ← Category.assoc, hy, one_comp]
  have hAC : A.dim = C.dim := le_antisymm ((DimLe.dim_le K A C q).1 hqfin) ((DimLe.dim_le K A C q).2 hq)
  have hAB : A.dim = B.dim := (isogeny_flat_finrank K A B f hf).1
  have hd1 := (isIsogeny_comp_iff_and_deg_comp K A C B q (i ≫ prodFst B A) hAC (hAC ▸ hAB)).2
  rw [h1] at hd1
  have hd2 := (isIsogeny_comp_iff_and_deg_comp K A C A q (i ≫ prodSnd B A) hAC hAC.symm).2
  rw [h2, (MulIsogeny.mul_isogeny K A (m : ℤ) (by exact_mod_cast hm.ne')).2, Int.natAbs_natCast] at hd2
  have hq1 : deg q = 1 := by
    have a : deg q ∣ deg f := ⟨_, hd1⟩
    have b : deg q ∣ m ^ (2 * A.dim) := ⟨_, hd2⟩
    exact Nat.Coprime.eq_one_of_dvd ((Nat.Coprime.pow_left _ hcop).coprime_dvd_left b) a
  have hiso : IsIso q := (isIso_iff_deg_eq_one K A C q).2 hq1

  have hy1 : ((x ≫ q.hom) ≫ i.hom) ≫ (prodFst B A).hom = 1 := by
    have := congrArg Hom.hom h1
    simp only [comp_hom] at this
    rw [Category.assoc, Category.assoc, this]
    exact hx
  have hy2 : ((x ≫ q.hom) ≫ i.hom) ≫ (prodSnd B A).hom = 1 := by
    have := congrArg Hom.hom h2
    simp only [comp_hom] at this
    rw [Category.assoc, Category.assoc, this, zsmul_hom, id_hom, zpow_natCast, MonObj.comp_pow,
      Category.comp_id, hxm]
  have hyi : (x ≫ q.hom) ≫ i.hom = (1 : T ⟶ C.X) ≫ i.hom := by
    rw [MonObj.one_comp]
    apply CartesianMonoidalCategory.hom_ext
    · change ((x ≫ q.hom) ≫ i.hom) ≫ (prodFst B A).hom = (1 : T ⟶ (prod B A).X) ≫ (prodFst B A).hom
      rw [hy1, MonObj.one_comp]
    · change ((x ≫ q.hom) ≫ i.hom) ≫ (prodSnd B A).hom = (1 : T ⟶ (prod B A).X) ≫ (prodSnd B A).hom
      rw [hy2, MonObj.one_comp]
  have hmono : Mono i.hom.left := inferInstance
  have hy : x ≫ q.hom = 1 := by
    apply Over.OverMorphism.ext
    have := congrArg Over.Hom.left hyi
    simp only [Over.comp_left] at this
    exact (cancel_mono i.hom.left).1 this
  have hqq : q.hom ≫ (inv q).hom = 𝟙 A.X := by
    rw [← comp_hom, IsIso.hom_inv_id, id_hom]
  calc x = (x ≫ q.hom) ≫ (inv q).hom := by rw [Category.assoc, hqq, Category.comp_id]
    _ = 1 := by rw [hy, MonObj.one_comp]

theorem kernel_killed_of_deg_ne_zero (K : Type) [Field K] (A B : AbVar K) (f : A ⟶ B) (hf : IsIsogeny f)
    (hd : ((deg f : ℕ) : K) ≠ 0) :
    ∃ n : ℕ, (n : K) ≠ 0 ∧ ∀ (T : Over (Sp K)) (x : T ⟶ A.X), x ≫ f.hom = 1 → x ^ n = 1 := by
  obtain ⟨n0, hn0, hkill⟩ := KerKill.kernel_killed K A B f hf.1
  obtain ⟨p, hp⟩ := CharP.exists K
  rcases CharP.char_is_prime_or_zero K p with hpp | hp0
  · obtain ⟨k, M, hM, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn0.ne' p hpp.ne_one
    refine ⟨M, ?_, ?_⟩
    · rwa [Ne, CharP.cast_eq_zero_iff K p]
    · intro T x hx
      have hpd : ¬ p ∣ deg f := by rwa [Ne, CharP.cast_eq_zero_iff K p] at hd
      refine eq_one_of_coprime f hf (p ^ k) (pow_pos hpp.pos k)
        (Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hpp).2 hpd)) (x ^ M) ?_ ?_
      · rw [MonObj.pow_comp, hx, one_pow]
      · rw [← pow_mul, mul_comm]; exact hkill T x hx
  · subst hp0
    haveI : CharZero K := CharP.charP_to_charZero K
    exact ⟨n0, by exact_mod_cast hn0.ne', hkill⟩

example : ∀ (K : Type) [Field K] (A B : AbVar K) (f : A ⟶ B), IsIsogeny f → ((deg f : ℕ) : K) ≠ 0 →
    ∃ n : ℕ, (n : K) ≠ 0 ∧ ∀ (T : Over (Sp K)) (x : T ⟶ A.X), x ≫ f.hom = 1 → x ^ n = 1 :=
  kernel_killed_of_deg_ne_zero

end GlobalTheory.AV.KerInv
