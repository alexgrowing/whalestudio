import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KappaOK
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInclusionCyclotomicAwayRingFiniteEtale
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc

namespace GlobalTheory.ZarhinFam.LevCoord

section Coord

variable {S : Scheme.{0}} (A B : Over S) [GrpObj A] [GrpObj B] [IsCommMonObj A] [IsCommMonObj B]

theorem mkZ_pa {T : Over S} (u : Fin 4 → (T ⟶ A)) (v : Fin 4 → (T ⟶ B)) (i : Fin 4) :
    mkZ A B u v ≫ pa A B i = u i := by
  simp only [mkZ, pa, lift_fst_assoc]
  exact (Out.powIsLimit A 4).fac (Fan.mk T u) ⟨i⟩

theorem mkZ_pb {T : Over S} (u : Fin 4 → (T ⟶ A)) (v : Fin 4 → (T ⟶ B)) (j : Fin 4) :
    mkZ A B u v ≫ pb A B j = v j := by
  simp only [mkZ, pb, lift_snd_assoc]
  exact (Out.powIsLimit B 4).fac (Fan.mk T v) ⟨j⟩

theorem zob_hom_ext {T : Over S} (f g : T ⟶ Zob A B) (ha : ∀ i, f ≫ pa A B i = g ≫ pa A B i)
    (hb : ∀ j, f ≫ pb A B j = g ≫ pb A B j) : f = g := by
  apply CartesianMonoidalCategory.hom_ext
  · apply (Out.powIsLimit A 4).hom_ext
    rintro ⟨i⟩
    simpa [pa] using ha i
  · apply (Out.powIsLimit B 4).hom_ext
    rintro ⟨j⟩
    simpa [pb] using hb j

instance pa_isMonHom (i : Fin 4) : IsMonHom (pa A B i) := by
  unfold pa; infer_instance

instance pb_isMonHom (j : Fin 4) : IsMonHom (pb A B j) := by
  unfold pb; infer_instance

end Coord

theorem oMat_apply (d : ℕ) (k : Fin 8) (p q : Fin 4 ⊕ Fin 4) :
    ((oMat d k : ord d) : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℤ) p q =
      if Sum.inl 0 = p ∧ sig k = q then 1 else 0 := by
  simp [oMat, Matrix.single_apply]

theorem sig_eq_inl (k : Fin 8) (i : Fin 4) : sig k = Sum.inl i ↔ Fin.castAdd 4 i = k := by
  fin_cases k <;> fin_cases i <;> simp [sig] <;> decide

theorem sig_eq_inr (k : Fin 8) (j : Fin 4) : sig k = Sum.inr j ↔ Fin.natAdd 4 j = k := by
  fin_cases k <;> fin_cases j <;> simp [sig] <;> decide

section Key

variable {S : Scheme.{0}} (A B : Over S) [GrpObj A] [GrpObj B] [IsCommMonObj A] [IsCommMonObj B]

theorem incZ_pa (j : Fin 4) : incZ A B ≫ pa A B j = if j = 0 then 𝟙 A else 1 := by
  simp [incZ, mkZ_pa]

theorem incZ_pb (j : Fin 4) : incZ A B ≫ pb A B j = 1 := by
  simp [incZ, mkZ_pb]

theorem inc_act_pa {T : Over S} (d : ℕ) (la : A ⟶ B) (mu : B ⟶ A) (y : T ⟶ A) (k : Fin 8) (i : Fin 4) :
    y ≫ incZ A B ≫ actZ A B d la mu (oMat d k) ≫ pa A B i = if sig k = Sum.inl i then y else 1 := by
  rw [actZ, mkZ_pa]
  simp only [oMat_apply, Fin.prod_univ_four, comp_mul, GrpObj.comp_zpow, ← Category.assoc, incZ_pa]
  simp only [true_and, if_true, Category.comp_id, reduceCtorEq, false_and, if_false, zero_div, zpow_zero,
    mul_one, Sum.inl.injEq, Fin.reduceEq, comp_one, one_zpow]
  split_ifs <;> simp

theorem inc_act_pb {T : Over S} (d : ℕ) (la : A ⟶ B) (mu : B ⟶ A) (y : T ⟶ A) (k : Fin 8) (j : Fin 4) :
    y ≫ incZ A B ≫ actZ A B d la mu (oMat d k) ≫ pb A B j = if sig k = Sum.inr j then y ≫ la else 1 := by
  rw [actZ, mkZ_pb]
  simp only [oMat_apply, Fin.prod_univ_four, comp_mul, GrpObj.comp_zpow, ← Category.assoc, incZ_pa, incZ_pb]
  simp only [true_and, if_true, Category.comp_id, reduceCtorEq, false_and, if_false, zero_div, zpow_zero,
    mul_one, one_mul, Sum.inl.injEq, Fin.reduceEq, comp_one, one_comp, one_zpow]
  split_ifs <;> simp

end Key

theorem list_prod_comp {S : Scheme.{0}} {T M N : Over S} [MonObj M] [MonObj N] (g : M ⟶ N) [IsMonHom g]
    (L : List (T ⟶ M)) : L.prod ≫ g = (L.map (· ≫ g)).prod := by
  let φ : (T ⟶ M) →* (T ⟶ N) :=
    { toFun := (· ≫ g), map_one' := one_comp g, map_mul' := fun x y => mul_comp x y g }
  exact map_list_prod φ L

theorem _root_.GlobalTheory.ZarhinFam.levZ_eq_mkZ {S : Scheme.{0}} (A B : Over S) [GrpObj A] [GrpObj B] [IsCommMonObj A] [IsCommMonObj B]
    (d h h' : ℕ) (la : A ⟶ B) (mu : B ⟶ A) (lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over S) ⟶ A))
    (κ : Fin 8 → (Fin h' ⊕ Fin h' → ℤ) →+ (Fin h ⊕ Fin h → ℤ)) (a : Fin h' ⊕ Fin h' → ℤ) :
    levZ lev (incZ A B) (actZ A B d la mu) (oMat d) κ a =
      mkZ A B (fun i => lev (κ (Fin.castAdd 4 i) a)) (fun j => lev (κ (Fin.natAdd 4 j) a) ≫ la) := by
  apply zob_hom_ext
  · intro i
    rw [mkZ_pa, levZ, list_prod_comp, List.map_ofFn]
    simp only [Function.comp_def, Category.assoc, inc_act_pa, List.prod_ofFn, sig_eq_inl]
    exact Fintype.prod_ite_eq _ _
  · intro j
    rw [mkZ_pb, levZ, list_prod_comp, List.map_ofFn]
    simp only [Function.comp_def, Category.assoc, inc_act_pb, List.prod_ofFn, sig_eq_inr]
    exact Fintype.prod_ite_eq (Fin.natAdd 4 j) (fun k => lev (κ k a) ≫ la)

end GlobalTheory.ZarhinFam.LevCoord
