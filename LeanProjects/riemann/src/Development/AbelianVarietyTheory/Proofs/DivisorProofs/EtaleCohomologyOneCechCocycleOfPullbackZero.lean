import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsZeroChains
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChosenInjectiveResolutionEtaleSheafBasicPropertiStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

noncomputable section
namespace GlobalTheory.EtC.LerayOne

def diag {Y X : Scheme.{0}} (f : Y ⟶ X) : sch.obj Y ⟶ cech f where
  app n := WidePullback.lift (yoneda.map f) (fun _ => 𝟙 _) (fun _ => Category.id_comp _)
  naturality m n g := by
    apply WidePullback.hom_ext
    · intro j
      dsimp [sch, cech, Arrow.cechNerve]
      erw [Category.id_comp, Category.assoc, WidePullback.lift_π, WidePullback.lift_π, WidePullback.lift_π]
    · dsimp [sch, cech, Arrow.cechNerve]
      erw [Category.id_comp, Category.assoc, WidePullback.lift_base, WidePullback.lift_base, WidePullback.lift_base]

theorem diag_aug {Y X : Scheme.{0}} (f : Y ⟶ X) : diag f ≫ cechAug f = sch.map f := by
  ext n : 1
  rw [NatTrans.comp_app]
  dsimp [diag, cechAug, sch, Arrow.augmentedCechNerve]
  erw [WidePullback.lift_base]

theorem diag_zero {Y X : Scheme.{0}} (f : Y ⟶ X) :
    WidePullback.π (fun _ : Fin 1 => yoneda.map f) (0 : Fin 1) ≫ (diag f).app (op ⦋0⦌) = 𝟙 ((cech f).obj (op ⦋0⦌)) := by
  apply WidePullback.hom_ext
  · intro j
    have hj : j = 0 := Fin.fin_one_eq_zero j
    subst hj
    dsimp [diag]
    erw [Category.assoc, WidePullback.lift_π, Category.comp_id]
  · dsimp [diag]
    erw [Category.assoc, WidePullback.lift_base, Category.id_comp, WidePullback.π_arrow]

end GlobalTheory.EtC.LerayOne

noncomputable section
namespace GlobalTheory.EtC.LerayOne

theorem cech_cocycle_of_pull_eq_zero : ∀ (R : Type) [CommRing R] (F : Shv R) (Y X : Scheme.{0}) (f : Y ⟶ X) (x : H R (sch.obj X) F 1), pull R (sch.map f) F 1 x = 0 → ∃ s : (free R).obj ((cech f).obj (op ⦋1⦌)) ⟶ F, cobd s = 0 ∧ IsCls s (pull R (cechAug f) F 1 x) := by
  intro R _ F Y X f x hx
  obtain ⟨-, hneg, hmono, ⟨w0, hex⟩, -, -⟩ := GlobalTheory.T.chosenInjectiveResolutionEtaleSheaf_basic_properties R F
  obtain ⟨z, hz⟩ := (pull R (cechAug f) F 1 x).mk_surjective
  have h0 : pull R (diag f) F 1 (CohomologyClass.mk z) = 0 := by
    rw [hz, ← pull_comp, diag_aug, hx]
  have h0' : CohomologyClass.mk (zcomp (Cocycle.ofHom ((chains R).map (diag f))) z (zero_add 1)) = 0 := h0
  rw [CohomologyClass.mk_eq_zero_iff] at h0'
  obtain ⟨m, hm, w, hw⟩ := h0'
  obtain rfl : m = 0 := by omega

  have hw01 : ((chains R).map (diag f)).f 0 ≫ z.1.v 0 1 (zero_add 1) =
      w.v 0 0 (add_zero 0) ≫ (res R F).d 0 1 := by
    have := Cochain.congr_v hw 0 1 (zero_add 1)
    rw [δ_v 0 1 (zero_add 1) w 0 1 (zero_add 1) 0 1 (by norm_num) (by norm_num),
      (CupSpec.isZero_chains (R := R) (sch.obj Y) 1 one_pos).eq_of_tgt (((chains R).obj (sch.obj Y)).d 0 1) 0,
      zero_comp, smul_zero, add_zero] at this
    rw [this]
    change _ = ((Cochain.ofHom ((chains R).map (diag f))).comp z.1 (zero_add 1)).v 0 1 (zero_add 1)
    rw [Cochain.zero_cochain_comp_v, Cochain.ofHom_v]
  have cm0 : (chainsXIso R (sch.obj Y) 0).inv ≫ ((chains R).map (diag f)).f 0 =
      (free R).map ((diag f).app (op ⦋0⦌)) ≫ (chainsXIso R (cech f) 0).inv := CupSpec.chains_map (diag f) 0
  let r : (cech f).obj (op ⦋0⦌) ⟶ (sch.obj Y).obj (op ⦋0⦌) := WidePullback.π (fun _ : Fin 1 => yoneda.map f) 0
  have hr : r ≫ (diag f).app (op ⦋0⦌) = 𝟙 _ := diag_zero f
  let y0 : (free R).obj ((cech f).obj (op ⦋0⦌)) ⟶ (res R F).X 0 :=
    (free R).map r ≫ (chainsXIso R (sch.obj Y) 0).inv ≫ w.v 0 0 (add_zero 0)
  have hA0 : (chainsXIso R (cech f) 0).inv ≫ z.1.v 0 1 (zero_add 1) = y0 ≫ (res R F).d 0 1 := by
    calc (chainsXIso R (cech f) 0).inv ≫ z.1.v 0 1 (zero_add 1)
        = (free R).map r ≫ ((free R).map ((diag f).app (op ⦋0⦌)) ≫ (chainsXIso R (cech f) 0).inv) ≫
            z.1.v 0 1 (zero_add 1) := by
          rw [← Category.assoc, ← Category.assoc, ← Functor.map_comp, hr, CategoryTheory.Functor.map_id, Category.id_comp]
      _ = y0 ≫ (res R F).d 0 1 := by
          rw [← cm0, Category.assoc, hw01]
          simp only [y0, Category.assoc]
  let c : Cochain ((chains R).obj (cech f)) (res R F) 0 :=
    Cochain.single (p := 0) (q := 0) ((chainsXIso R (cech f) 0).hom ≫ y0) 0
  let b : Cocycle ((chains R).obj (cech f)) (res R F) 1 := Cocycle.mk (δ 0 1 c) 2 (by norm_num) (δ_δ 0 1 2 c)
  have hb : CohomologyClass.mk b = 0 := (CohomologyClass.mk_eq_zero_iff b).2 ⟨0, zero_add 1, c, rfl⟩
  let ζ := z - b
  have hζ : CohomologyClass.mk ζ = pull R (cechAug f) F 1 x := by
    rw [CohomologyClass.mk_sub, hb, sub_zero, hz]
  have hζv : ∀ p q hpq, ζ.1.v p q hpq = z.1.v p q hpq - (δ 0 1 c).v p q hpq := fun p q hpq => by
    simp only [ζ, b, Cocycle.coe_sub, Cochain.sub_v]
    rfl
  have hζ01 : ζ.1.v 0 1 (zero_add 1) = 0 := by
    rw [hζv, δ_v 0 1 (zero_add 1) c 0 1 (zero_add 1) 0 1 (by norm_num) (by norm_num),
      (CupSpec.isZero_chains (R := R) (cech f) 1 one_pos).eq_of_tgt (((chains R).obj (cech f)).d 0 1) 0,
      zero_comp, smul_zero, add_zero, Cochain.single_v]
    rw [← cancel_epi (chainsXIso R (cech f) 0).inv, Preadditive.comp_sub, hA0, comp_zero]
    simp only [Category.assoc, Iso.inv_hom_id_assoc, sub_self]
  have hδζ : δ 1 2 ζ.1 = 0 := Cocycle.δ_eq_zero ζ 2
  have hB : ζ.1.v (-1) 0 (by norm_num) ≫ (res R F).d 0 1 = 0 := by
    have := Cochain.congr_v hδζ (-1) 1 (by norm_num)
    rw [δ_v 1 2 (by norm_num) ζ.1 (-1) 1 (by norm_num) 0 0 (by norm_num) (by norm_num), hζ01, comp_zero,
      smul_zero, add_zero, Cochain.zero_v] at this
    exact this
  haveI := hmono
  let B : (free R).obj ((cech f).obj (op ⦋1⦌)) ⟶ (res R F).X 0 :=
    (chainsXIso R (cech f) 1).inv ≫ ζ.1.v (-1) 0 (by norm_num)
  have hBd : B ≫ (res R F).d 0 1 = 0 := by simp only [B, Category.assoc, hB, comp_zero]
  let s : (free R).obj ((cech f).obj (op ⦋1⦌)) ⟶ F := hex.lift B hBd
  have hs : s ≫ resι R F = B := hex.lift_f B hBd
  refine ⟨s, ?_, ζ, hζ, ?_⟩
  · have h20 := Cochain.congr_v hδζ (-2) 0 (by norm_num)
    rw [δ_v 1 2 (by norm_num) ζ.1 (-2) 0 (by norm_num) (-1) (-1) (by norm_num) (by norm_num),
      (hneg (-1) (by norm_num)).eq_of_tgt (ζ.1.v (-2) (-1) (by norm_num)) 0, zero_comp, zero_add, Cochain.zero_v] at h20
    have h2 : (2 : ℤ).negOnePow = 1 := Int.negOnePow_even 2 even_two
    rw [h2, one_smul] at h20
    have hd : (chainsXIso R (cech f) 2).inv ≫ ((chains R).obj (cech f)).d (-2) (-1) =
        (∑ i : Fin 3, (-1 : ℤ) ^ (i : ℕ) • (free R).map ((cech f).δ i)) ≫ (chainsXIso R (cech f) 1).inv :=
      CupSpec.chains_d (cech f) 1
    have h3 := congrArg ((chainsXIso R (cech f) 2).inv ≫ ·) h20
    simp only [comp_zero] at h3
    rw [← Category.assoc, hd, Category.assoc] at h3
    apply (cancel_mono (resι R F)).1
    rw [zero_comp, cobd, Preadditive.sum_comp]
    rw [Preadditive.sum_comp] at h3
    refine Eq.trans ?_ h3
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [Preadditive.zsmul_comp, Category.assoc, hs, B]
  · apply Cochain.ext
    intro p q hpq
    by_cases hp1 : p = -((1 : ℕ) : ℤ)
    · subst hp1
      obtain rfl : q = 0 := by omega
      rw [Cochain.single_v, hs]
      change _ = (chainsXIso R (cech f) 1).hom ≫ (chainsXIso R (cech f) 1).inv ≫ ζ.1.v _ 0 hpq
      rw [Iso.hom_inv_id_assoc]
    · rw [Cochain.single_v_eq_zero _ _ _ _ _ hp1]
      by_cases hp0 : p = 0
      · subst hp0
        obtain rfl : q = 1 := by omega
        exact hζ01
      · by_cases hpos : 0 < p
        · exact (CupSpec.isZero_chains (cech f) p hpos).eq_of_src _ _
        · exact (hneg q (by omega)).eq_of_tgt _ _

end GlobalTheory.EtC.LerayOne
