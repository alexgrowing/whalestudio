import Mathlib
import GroundTheory.TateCohomology.CupTateShift
set_option maxSynthPendingDepth 1

open CategoryTheory MonoidalCategory groupCohomology

namespace GroundTheory.GroupCoh

universe u

variable {k G : Type u} [CommRing k] [Group G] [Fintype G]

def tensorInvariants {A B : Rep.{u} k G} (x : A.ρ.invariants) (y : B.ρ.invariants) :
    (A ⊗ B).ρ.invariants :=
  ⟨x.1 ⊗ₜ[k] y.1, fun g => by
    change A.ρ g x.1 ⊗ₜ[k] B.ρ g y.1 = x.1 ⊗ₜ[k] y.1
    rw [x.2 g, y.2 g]⟩

omit [Fintype G] in

theorem cupH_zero_zero_π {A B : Rep.{u} k G} (f : (Fin 0 → G) → A) (g : (Fin 0 → G) → B)
    (hf : (inhomogeneousCochains.d A 0).hom f = 0) (hg : (inhomogeneousCochains.d B 0).hom g = 0)
    (fg : (Fin 0 → G) → (A ⊗ B : Rep k G)) (hfg : (inhomogeneousCochains.d (A ⊗ B) 0).hom fg = 0)
    (h : ∀ v, fg v = f v ⊗ₜ[k] g v) :
    cupH rfl (π A 0 (cocyclesMk f hf)) (π B 0 (cocyclesMk g hg)) = π (A ⊗ B) 0 (cocyclesMk fg hfg) := by
  rw [cupH_π]
  congr 1
  apply cocycles_ext
  rw [iCocycles_cupCocycles, iCocycles_mk, iCocycles_mk, iCocycles_mk]
  funext v
  rw [cupCochain_apply, h]
  have hv : ∀ w : Fin 0 → G, w = v := fun w => Subsingleton.elim _ _
  rw [hv (fun i : Fin 0 => v ⟨i, by omega⟩), hv (fun j : Fin 0 => v ⟨0 + j, by omega⟩)]
  simp [Fin.partialProd]

set_option maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in

theorem tateCup_zero_zero (A B : Rep.{u} k G) (x : A.ρ.invariants) (y : B.ρ.invariants) :
    tateCup 0 0 A B 0 (add_zero 0)
        (((tateCohomologyZeroIso k G).app A).inv.hom (Submodule.Quotient.mk x))
        (((tateCohomologyZeroIso k G).app B).inv.hom (Submodule.Quotient.mk y)) =
      ((tateCohomologyZeroIso k G).app (A ⊗ B)).inv.hom
        (Submodule.Quotient.mk (tensorInvariants x y)) := by
  obtain ⟨zA, hzA⟩ := exists_tateComplex_cycles_zero A x
  obtain ⟨zB, hzB⟩ := exists_tateComplex_cycles_zero B y
  obtain ⟨zAB, hzAB⟩ := exists_tateComplex_cycles_zero (A ⊗ B) (tensorInvariants x y)
  rw [tateCohomologyZeroIso_inv_mk A zA x hzA.symm, tateCohomologyZeroIso_inv_mk B zB y hzB.symm,
    tateCohomologyZeroIso_inv_mk (A ⊗ B) zAB _ hzAB.symm]
  rw [tateCup_of_nonpos 0 le_rfl]
  apply moduleIso_hom_injective (tateLeftIso A B 0)
  rw [tateLeftIso_cupL, tateCup_of_pos_of_nonpos (by norm_num) le_rfl]
  apply moduleIso_hom_injective (tateRightIso (augIdeal k G ⊗ A) B (0 + 1))
  rw [tateRightIso_cupR]
  apply moduleIso_hom_injective (tateIsoH ((augIdeal k G ⊗ A) ⊗ (augIdeal k G ⊗ B)) (0 + 1 + 1) 2
    (by norm_num))
  have hA1 := tateIsoH_tδ_homologyπ (augSES_shortExact A) 0 zA
  have hB1 := tateIsoH_tδ_homologyπ (augSES_shortExact B) 0 zB
  have hAB1 := tateIsoH_tδ_homologyπ (augSES_tensorRight_shortExact A B) 0 zAB
  have hxA : ∀ v, ((tateComplex A).iCycles 0).hom zA v = x.1 := fun v => congrFun hzA v
  have hyB : ∀ v, ((tateComplex B).iCycles 0).hom zB v = y.1 := fun v => congrFun hzB v
  have hxyAB : ∀ v, ((tateComplex (A ⊗ B)).iCycles 0).hom zAB v = x.1 ⊗ₜ[k] y.1 :=
    fun v => congrFun hzAB v
  have hcup0 := cupH_zero_zero_π _ _ (tate_d_iCycles A 0 zA) (tate_d_iCycles B 0 zB) _
    (tate_d_iCycles (A ⊗ B) 0 zAB)
    (fun v => (hxyAB v).trans (congrArg₂ (fun a b => a ⊗ₜ[k] b) (hxA v).symm (hyB v).symm))
  have e_left := δ_cupH_left (augSES_shortExact A) B (augSES_tensorRight_shortExact A B)
    (p := 0) (q := 0) rfl rfl
    (π A 0 (cocyclesMk (((tateComplex A).iCycles 0).hom zA) (tate_d_iCycles A 0 zA)))
    (π B 0 (cocyclesMk (((tateComplex B).iCycles 0).hom zB) (tate_d_iCycles B 0 zB)))
  have e_right := δ_cupH_right (augSES_shortExact B) (augIdeal k G ⊗ A)
    (augSES_tensorLeft_shortExact (augIdeal k G ⊗ A) B) (p := 0) (q := 1) rfl rfl
    (δ (augSES_shortExact A) 0 (0 + 1) rfl
      (π A 0 (cocyclesMk (((tateComplex A).iCycles 0).hom zA) (tate_d_iCycles A 0 zA))))
    (π B 0 (cocyclesMk (((tateComplex B).iCycles 0).hom zB) (tate_d_iCycles B 0 zB)))
  have e_br := congr(($(tδ_comp_tateIsoH (augSES_tensorLeft_shortExact (augIdeal k G ⊗ A) B) 1)).hom
    ((tateLeftIso A B 0).hom.hom (((tateComplex (A ⊗ B)).homologyπ 0).hom zAB)))
  have e_base := tateIsoH_tateCup (n := 1) (m := 1) (l := 2) (p := 0 + 1) (q := 0 + 1) (r := 0 + 1 + 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (augIdeal k G ⊗ A) (augIdeal k G ⊗ B) ((augShiftδ A 0).hom (((tateComplex A).homologyπ 0).hom zA))
    ((augShiftδ B 0).hom (((tateComplex B).homologyπ 0).hom zB))
  refine Eq.trans (moduleHom_smul _ _ _) ?_
  refine Eq.trans (congrArg (tsgn k (0 + 1) • ·) e_base) ?_
  refine Eq.trans (congrArg₂ (fun s t => tsgn k (0 + 1) • cupH (show 1 + 1 = 2 by rfl) s t)
    hA1 hB1) ?_
  refine Eq.trans ?_ e_br.symm
  refine Eq.trans ?_ (congrArg (δ (augSES_tensorLeft_shortExact (augIdeal k G ⊗ A) B) 1 (1 + 1)
    rfl).hom hAB1).symm
  refine Eq.trans ?_ (congrArg (fun t => δ (augSES_tensorLeft_shortExact (augIdeal k G ⊗ A) B) 1
    (1 + 1) rfl (δ (augSES_tensorRight_shortExact A B) 0 (0 + 1) rfl t)) hcup0)
  refine Eq.trans ?_ (congrArg (δ (augSES_tensorLeft_shortExact (augIdeal k G ⊗ A) B) 1
    (1 + 1) rfl).hom e_left).symm
  refine Eq.trans ?_ e_right.symm
  have hs : tsgn k (0 + 1) = (-1 : k) ^ 1 := by
    rw [tsgn_add_one]
    simp [tsgn]
  rw [hs]
  rfl

set_option maxHeartbeats 800000 in

theorem tateCup_unique_of_agrees (μ : ∀ p q : ℤ, TateCupFam k G p q)
    (hpos : ∀ (n m l : ℕ) [NeZero n] [NeZero m] [NeZero l] (hl : n + m = l) (A B : Rep.{u} k G)
      (a : tateCohomology A n) (b : tateCohomology B m),
      (tateIsoH (A ⊗ B) l l rfl).hom.hom (μ n m A B l (by omega) a b) =
        cupH hl ((tateIsoH A n n rfl).hom.hom a) ((tateIsoH B m m rfl).hom.hom b))
    (hleft : ∀ (p q : ℤ) (A B : Rep.{u} k G) (r : ℤ) (h : p + q = r) (a : tateCohomology A p)
      (b : tateCohomology B q),
      (tδ (augSES_tensorRight_shortExact A B) r (r + 1) rfl).hom (μ p q A B r h a b) =
        μ (p + 1) q (augIdeal k G ⊗ A) B (r + 1) (by omega)
          ((tδ (augSES_shortExact A) p (p + 1) rfl).hom a) b)
    (hright : ∀ (p q : ℤ) (A B : Rep.{u} k G) (r : ℤ) (h : p + q = r) (a : tateCohomology A p)
      (b : tateCohomology B q),
      (tδ (augSES_tensorLeft_shortExact A B) r (r + 1) rfl).hom (μ p q A B r h a b) =
        tsgn k p • μ p (q + 1) A (augIdeal k G ⊗ B) (r + 1) (by omega) a
          ((tδ (augSES_shortExact B) q (q + 1) rfl).hom b))
    (m : ℕ) : ∀ (p q : ℤ), (1 - p).toNat + (1 - q).toNat = m → ∀ (A B : Rep.{u} k G) (r : ℤ)
      (h : p + q = r) (a : tateCohomology A p) (b : tateCohomology B q),
      μ p q A B r h a b = tateCup p q A B r h a b := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro p q hm A B r h a b
  by_cases hp : p ≤ 0
  · rw [tateCup_of_nonpos q hp]
    apply moduleIso_hom_injective (tateLeftIso A B r)
    rw [tateLeftIso_cupL, tateLeftIso_hom]
    refine (hleft p q A B r h a b).trans ?_
    exact ih _ (by omega) (p + 1) q rfl _ _ _ _ _ _
  by_cases hq : q ≤ 0
  · rw [tateCup_of_pos_of_nonpos (by omega) hq]
    apply moduleIso_hom_injective (tateRightIso A B r)
    rw [tateRightIso_cupR, tateRightIso_hom]
    refine (hright p q A B r h a b).trans ?_
    exact congrArg (tsgn k p • ·) (ih _ (by omega) p (q + 1) rfl _ _ _ _ _ _)
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, p = n := ⟨p.toNat, by omega⟩
    obtain ⟨m', rfl⟩ : ∃ m' : ℕ, q = m' := ⟨q.toNat, by omega⟩
    obtain ⟨l, rfl⟩ : ∃ l : ℕ, r = l := ⟨r.toNat, by omega⟩
    have : NeZero n := ⟨by omega⟩
    have : NeZero m' := ⟨by omega⟩
    have : NeZero l := ⟨by omega⟩
    have hl : n + m' = l := by omega
    apply moduleIso_hom_injective (tateIsoH (A ⊗ B) l l rfl)
    rw [hpos n m' l hl, tateIsoH_tateCup rfl rfl rfl h hl]

noncomputable def tateCupTensor (A B : Rep.{u} k G) (p q : ℤ) :
    TensorProduct k (tateCohomology A p) (tateCohomology B q) →ₗ[k] tateCohomology (A ⊗ B) (p + q) :=
  TensorProduct.lift (tateCup p q A B (p + q) rfl)

theorem tateCup_δ_left {E : ShortComplex (Rep.{u} k G)} (hE : E.ShortExact) (B : Rep.{u} k G)
    (hEB : (E.map (tensorRight B)).ShortExact) (p q r : ℤ) (h : p + q = r)
    (a : tateCohomology E.X₃ p) (b : tateCohomology B q) :
    (TateCohomology.δ hEB r).hom (tateCup p q E.X₃ B r h a b) =
      tateCup (p + 1) q E.X₁ B (r + 1) (by omega) ((TateCohomology.δ hE p).hom a) b :=
  tateCup_connecting_left _ p q rfl hE B hEB r h a b

theorem tateCup_δ_right {E : ShortComplex (Rep.{u} k G)} (hE : E.ShortExact) (A : Rep.{u} k G)
    (hAE : (E.map (tensorLeft A)).ShortExact) (p q r : ℤ) (h : p + q = r)
    (a : tateCohomology A p) (b : tateCohomology E.X₃ q) :
    (TateCohomology.δ hAE r).hom (tateCup p q A E.X₃ r h a b) =
      p.negOnePow • tateCup p (q + 1) A E.X₁ (r + 1) (by omega) a ((TateCohomology.δ hE q).hom b) := by
  rw [Units.smul_def, ← Int.cast_smul_eq_zsmul k]
  exact tateCup_connecting_right _ p q rfl hE A hAE r h a b

end GroundTheory.GroupCoh
