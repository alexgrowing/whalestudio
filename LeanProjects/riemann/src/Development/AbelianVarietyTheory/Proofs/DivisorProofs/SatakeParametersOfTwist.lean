import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisOfPolarized
open IsDedekindDomain NumberField Formalism.UG GlobalTheory.SphPar GlobalTheory.CuspRep

namespace GlobalTheory.SphGal

open GlobalTheory.LFun GlobalTheory.PRep

theorem satEig_map_mul (q m : ℕ) (B : Multiset ℂˣ) (z : ℂˣ) (j : ℕ) :
    satEig q m (B.map (· * z)) j = (z : ℂ) ^ j * satEig q m B j := by
  have h := Multiset.pow_smul_esymm (z : ℂ) j (B.map fun b : ℂˣ => (b : ℂ))
  simp only [smul_eq_mul, Multiset.map_map, Function.comp_def] at h
  simp only [satEig, Multiset.map_map, Function.comp_def, Units.val_mul]
  rw [mul_left_comm, h]
  simp only [mul_comm]

variable {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {m : ℕ}

theorem isUnitAt_det_of_mem {k : GL (Fin m) (w.adicCompletion E)} (hk : k ∈ KGL w m) :
    Formalism.L2.Host.IsUnitAt w (Matrix.GeneralLinearGroup.det k) := by
  obtain ⟨k, rfl⟩ := hk
  have e : ((Matrix.GeneralLinearGroup.det (bc (Ov E w).subtype k) : (w.adicCompletion E)ˣ) : w.adicCompletion E) =
      ((Matrix.GeneralLinearGroup.det k : (Ov E w)ˣ) : Ov E w) :=
    ((Ov E w).subtype.map_det k.val).symm
  change Valued.v _ = 1
  rw [e]
  generalize Matrix.GeneralLinearGroup.det k = u
  have h1 : Valued.v ((u : Ov E w) : w.adicCompletion E) ≤ 1 := (u : Ov E w).2
  have h2 : Valued.v (((u⁻¹ : (Ov E w)ˣ) : Ov E w) : w.adicCompletion E) ≤ 1 := ((u⁻¹ : (Ov E w)ˣ) : Ov E w).2
  have h3 : Valued.v ((u : Ov E w) : w.adicCompletion E) *
      Valued.v (((u⁻¹ : (Ov E w)ˣ) : Ov E w) : w.adicCompletion E) = 1 := by
    rw [← map_mul, ← Subring.coe_mul, Units.mul_inv]; simp
  exact le_antisymm h1 (h3 ▸ mul_le_of_le_one_right' h2)

theorem det_diagJ {L : Type} [Field L] (ϖ : L) {j : ℕ} (hj : j ≤ m) : (diagJ m ϖ j).det = ϖ ^ j := by
  rw [diagJ, Matrix.det_diagonal, Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one,
    Fin.card_filter_val_lt, min_eq_right hj]

theorem loc_det_of_Tj {χ : Formalism.L2.Host.HChar E} (hχ : χ.UnrAt w) {ϖ : w.adicCompletion E} (hϖ : IsUnifV E w ϖ)
    {j : ℕ} (hj : j ≤ m) {g : GL (Fin m) (w.adicCompletion E)} (hg : Tj ℂ m (Ov E w) ϖ j g ≠ 0) :
    χ.loc w (Matrix.GeneralLinearGroup.det g) = χ.val w ^ j := by
  obtain ⟨a, ha, b, hb, e⟩ := Set.mem_of_indicator_ne_zero hg
  have h0 : ϖ ≠ 0 := fun h0 => by simp [IsUnifV, h0] at hϖ
  have e2 : Matrix.GeneralLinearGroup.det g =
      Matrix.GeneralLinearGroup.det a * Units.mk0 ϖ h0 ^ j * Matrix.GeneralLinearGroup.det b := by
    apply Units.ext
    change g.val.det = a.val.det * _ * b.val.det
    rw [e, Matrix.det_mul, Matrix.det_mul, det_diagJ ϖ hj]
    simp
  rw [e2, map_mul, map_mul, hχ _ (isUnitAt_det_of_mem ha), hχ _ (isUnitAt_det_of_mem hb), map_pow,
    χ.val_eq hχ (Units.mk0 ϖ h0) hϖ, one_mul, mul_one]

theorem hasSatGL_of_twist {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ (GL (Fin m) (w.adicCompletion E)) V}
    {ρ' : Representation ℂ (GL (Fin m) (w.adicCompletion E)) W} {χ : Formalism.L2.Host.HChar E} (hχ : χ.UnrAt w)
    (T : V ≃ₗ[ℂ] W)
    (hT : ∀ g x, ρ' g (T x) = ((χ.loc w (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) • T (ρ g x))
    {B : Multiset ℂˣ} (h : HasSatGL w ρ B) : HasSatGL w ρ' (B.map (· * χ.val w)) := by
  have hf : ∀ x, T x ∈ fixed ρ' (KGL w m) ↔ x ∈ fixed ρ (KGL w m) := fun x => by
    simp only [GlobalTheory.LGrp.mem_fixed]
    refine forall₂_congr fun k hk => ?_
    rw [hT, hχ _ (isUnitAt_det_of_mem hk), Units.val_one, one_smul, T.injective.eq_iff]
  constructor
  · obtain ⟨x, hx, h0⟩ := (Submodule.ne_bot_iff _).1 h.1
    exact (Submodule.ne_bot_iff _).2 ⟨T x, (hf x).2 hx, (map_ne_zero_iff T T.injective).2 h0⟩
  · intro y hy h0
    obtain ⟨x, rfl⟩ := T.surjective y
    have hx := h.2 x ((hf x).1 hy) ((map_ne_zero_iff T T.injective).1 h0)
    refine ⟨h0, hy, by rw [Multiset.card_map, hx.2.2.1], fun ϖ hϖ j hj => ?_⟩
    rw [satEig_map_mul, mul_smul, ← map_smul T, ← hx.2.2.2 ϖ hϖ j hj, heckeVec, heckeVec]
    have e := T.toAddEquiv.map_finsum
      (fun c : _ ⧸ KGL w m => Tj ℂ m (Ov E w) ϖ j c.out • ρ c.out x)
    rw [show T _ = _ from e, smul_finsum]
    refine finsum_congr fun c => ?_
    by_cases hc : Tj ℂ m (Ov E w) ϖ j c.out = 0
    · simp [hc]
    · rw [hT, loc_det_of_Tj hχ hϖ hj hc, smul_comm]
      simp

theorem hasSatGL_twist (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (m : ℕ) (π : CuspSub E m)
    (χ : Formalism.L2.Host.HChar E) (w : HeightOneSpectrum (𝓞 E)) (B : Multiset ℂˣ) (hχ : χ.UnrAt w)
    (h : GlobalTheory.LFun.HasSatGL w (π.locRep w) B) :
    GlobalTheory.LFun.HasSatGL w ((π.twist χ).locRep w) (B.map (· * χ.val w)) := by
  refine hasSatGL_of_twist hχ (π.toTwist χ) (fun g x => ?_) h
  rw [CuspSub.locRep_eq, CuspSub.op_toTwist, opAdd, zero_smul, add_zero, map_smul, opMul, CuspSub.chiDet_locGL]
  rfl

end GlobalTheory.SphGal
