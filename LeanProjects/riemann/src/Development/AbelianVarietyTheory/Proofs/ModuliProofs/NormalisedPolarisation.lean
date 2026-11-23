import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsGenOfMemChart
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LocGenOfTrivial
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSecImageNonzeroLocus
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPrimitiveNormalisation

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.PrimNormPol

open GlobalTheory.MulPull GlobalTheory.PrimNorm

section Classes

variable {X Y Z : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K] [Fintype K']

def chartUnflat (L : LB X) (φ : K → (Y ⟶ X)) (ε : K → ℤ) (ψ : K' → (Z ⟶ Y)) (δ : K' → ℤ) :
    ChartPull (LB.LinComb L (fun p : K' × K => ψ p.1 ≫ φ p.2) (fun p => ε p.2 * δ p.1))
      (LB.LinComb (LB.LinComb L φ ε) ψ δ) (𝟙 Z) :=
  have le : ∀ j : K' × K → L.ι, LB.wchart L (fun p : K' × K => ψ p.1 ≫ φ p.2) j ≤
      LB.wchart (LB.LinComb L φ ε) ψ (fun a b => j (a, b)) := fun j y hy =>
    Set.mem_iInter.2 fun a => Set.mem_iInter.2 fun b => Set.mem_iInter.1 hy (a, b)
  { idx := fun j a b => j (a, b)
    le := le
    g := fun y p q hp hq => ((chartFlat L φ ε ψ δ).g y _ _ (le p hp) (le q hq)).symm }

theorem nested_of_hasGen (hL : L.IsLB) (φ : K → (Y ⟶ X)) (ε : K → ℤ) (ψ : K' → (Z ⟶ Y)) (δ : K' → ℤ)
    (h : HasGen (LB.LinComb L φ ε) ψ δ) : ∏ k, (∏ l, cls L (ψ k ≫ φ l) ^ ε l) ^ δ k = 1 := by
  obtain ⟨t, ht⟩ := h
  have hflat := (hasGen_iff hL (fun p : K' × K => ψ p.1 ≫ φ p.2) (fun p => ε p.2 * δ p.1)).1
    (gen_chartPull (chartUnflat L φ ε ψ δ) t ht)
  rwa [prod_flat] at hflat

theorem cls_eq_one_of_mem_chart (hL : L.IsLB) (ψ : Y ⟶ X) (i : L.ι) (hi : ∀ y, ψ y ∈ L.U i) : cls L ψ = 1 := by
  have hg := GlobalTheory.AbSquare.exists_gen_of_mem_chart hL (fun _ : Unit => ψ) (fun _ => (1 : ℤ)) (fun _ => i)
    (fun _ y => hi y)
  have hp := (hasGen_iff hL (fun _ : Unit => ψ) (fun _ => (1 : ℤ))).1 hg
  simpa using hp

end Classes

section Algebra

variable {A U : Type} [CommGroup A] [CommGroup U] {m : A → U}

theorem diff₂_self (hc : ∀ x y z, diff₃ m x y z = 1) (h₁ : m 1 = 1) {x : A} (hx : m x⁻¹ = m x) :
    diff₂ m x x = m x ^ 2 := by
  have hsplit : diff₂ m x (x * x⁻¹) = diff₂ m x x * diff₂ m x x⁻¹ := diff₂_mul_right hc x x x⁻¹
  have hone : diff₂ m x (x * x⁻¹) = 1 := by
    simp only [diff₂, mul_inv_cancel, _root_.mul_one, h₁, inv_one]
  have hinv : diff₂ m x x⁻¹ = (m x ^ 2)⁻¹ := by
    simp only [diff₂, mul_inv_cancel, h₁, hx, _root_.one_mul, _root_.mul_one, pow_two, mul_inv]
  rw [hone, hinv] at hsplit
  exact (mul_inv_eq_one.mp hsplit.symm)

theorem eq_of_diff₂_eq {n : A → U} {x y : A} (h : diff₂ n x y = diff₂ m x y) (h₁ : n (x * y) = n y)
    (h₂ : n (x * 1) = n 1) (h₃ : m x = 1) (h₄ : m 1 = 1) : m (x * y) ^ (1 : ℤ) * m y ^ (-1 : ℤ) = 1 := by
  have hn : n x = n 1 := by simpa using h₂
  have hzero : diff₂ n x y = 1 := by
    simp only [diff₂, h₁, hn]
    rw [mul_right_comm (n y), mul_inv_cancel, _root_.one_mul, inv_mul_cancel]
  have hm : diff₂ m x y = 1 := h.symm.trans hzero
  simp only [diff₂, h₃, h₄, inv_one, _root_.mul_one] at hm
  simpa only [zpow_one, zpow_neg, zpow_one] using hm

end Algebra

section Main

variable {S : Scheme.{0}} {B : Over S} [GrpObj B] [IsCommMonObj B] {L : LB B.left}

theorem ptCls_one (hL : L.IsLB) (hr : Out.Rigidified B L) (T : Over S) : ptCls L T 1 = 1 := by
  unfold Out.Rigidified at hr
  obtain ⟨t, ht⟩ := hr
  have e1 : (1 : T ⟶ B).left = T.hom ≫ eSec B := by
    rw [Hom.one_def, Over.comp_left]
    congr 1
  have g1 : HasGen L (fun _ : PUnit => eSec B) (fun _ => 1) := ⟨t, ht⟩
  have g2 := (hasGen_iff hL _ _).1 (g1.pull T.hom)
  simpa [ptCls, e1] using g2

theorem normCls_transl (hL : L.IsLB) (w : B ⟶ B) {T : Over S} (x : T ⟶ B) (V : T.left.Opens)
    (c : ∃ c : LB.Gen ((Out.translDiff B (cubeLB B ![𝟙 B, w] L) x).pull ((fst T B).left ⁻¹ᵁ V).ι), c.IsGen)
    {Z : Over S} (u : Z ⟶ T) (b : Z ⟶ B) (hu : ∀ z, u.left z ∈ V) :
    normCls L w ((u ≫ x) * b).left = normCls L w b.left := by
  obtain ⟨t, ht⟩ := c
  have hV : GlobalTheory.KerPow.HasGen (cubeLB B ![𝟙 B, w] L)
      (fun k => ((fst T B).left ⁻¹ᵁ V).ι ≫
        ![(lift (fst T B ≫ x) (snd T B) ≫ μ).left, (snd T B).left] k) ![1, -1] :=
    (GlobalTheory.KerPow.pull_iff _ _ _).1 ⟨t, ht⟩
  have hρ : ∀ z, (lift u b).left z ∈ (fst T B).left ⁻¹ᵁ V := fun z => by
    have hz := hu z
    rw [← lift_fst u b, Over.comp_left] at hz
    exact hz
  have hZ := GlobalTheory.KerPow.HasGen.of_range hV (lift u b).left hρ
    (φ' := ![((u ≫ x) * b).left, b.left]) (fun k => by
      fin_cases k
      · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, ← Over.comp_left, Hom.mul_def]
        rw [← Category.assoc, comp_lift, ← Category.assoc, lift_fst, lift_snd]
      · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one, ← Over.comp_left,
          lift_snd])
  have hn : ∏ k : Fin 2, normCls L w (![((u ≫ x) * b).left, b.left] k) ^ (![1, -1] : Fin 2 → ℤ) k = 1 :=
    nested_of_hasGen hL _ _ _ _ hZ
  simp only [Fin.prod_univ_two, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, zpow_one, zpow_neg] at hn
  exact mul_inv_eq_one.mp hn

omit [IsCommMonObj B] in
theorem exists_gen_translDiff (hL : L.IsLB) {T : Over S} (x : T ⟶ B) (W : (T ⊗ B).left.Opens)
    (h : ∀ (Z : Over S) (ρ : Z ⟶ T ⊗ B), (∀ z, ρ.left z ∈ W) →
      cls L (((ρ ≫ fst T B) ≫ x) * (ρ ≫ snd T B)).left ^ (1 : ℤ) * cls L (ρ ≫ snd T B).left ^ (-1 : ℤ) = 1) :
    ∃ c : LB.Gen ((Out.translDiff B L x).pull W.ι), c.IsGen := by
  unfold Out.translDiff
  refine (GlobalTheory.KerPow.pull_iff _ _ W.ι).2 ?_
  let ρ : Over.mk (W.ι ≫ (T ⊗ B).hom) ⟶ T ⊗ B := Over.homMk W.ι
  have hp := h _ ρ (fun z => z.2)
  have e0 : (ρ ≫ fst T B) ≫ x * ρ ≫ snd T B = ρ ≫ (lift (fst T B ≫ x) (snd T B) ≫ μ) := by
    simp only [Hom.mul_def]
    rw [← Category.assoc ρ, comp_lift]
    simp only [Category.assoc]
  rw [e0, Over.comp_left, Over.comp_left] at hp
  refine (hasGen_iff hL _ _).2 ?_
  simpa [Fin.prod_univ_two, ρ] using hp

theorem kTriv_norm (hL : L.IsLB) (hr : Out.Rigidified B L) (hK : Out.KTriv B L) (w : B ⟶ B)
    (hd : ∀ (T : Over S) (x y : T ⟶ B),
      diff₂ (fun q : T ⟶ B => normCls L w q.left) x y = diff₂ (ptCls L T) x y) :
    Out.KTriv B (cubeLB B ![𝟙 B, w] L) := by
  unfold Out.KTriv at hK ⊢
  intro R _ t x hx
  apply hK R t x
  intro p
  obtain ⟨V, hpV, c⟩ := hx p
  obtain ⟨i, hi⟩ : ∃ i, x.left p ∈ L.U i := by
    have hp : x.left p ∈ ⨆ i, L.U i := by
      rw [hL.cover]
      trivial
    exact TopologicalSpace.Opens.mem_iSup.1 hp
  refine ⟨V ⊓ x.left ⁻¹ᵁ L.U i, ⟨hpV, hi⟩, ?_⟩
  apply exists_gen_translDiff hL x
  intro Z ρ hρ
  exact eq_of_diff₂_eq (n := fun q : Z ⟶ B => normCls L w q.left) (m := ptCls L Z) (hd Z _ _)
    (normCls_transl hL w x V c (ρ ≫ fst _ B) (ρ ≫ snd _ B) (fun z => (hρ z).1))
    (normCls_transl hL w x V c (ρ ≫ fst _ B) 1 (fun z => (hρ z).1))
    (cls_eq_one_of_mem_chart hL _ i (fun z => (hρ z).2))
    (ptCls_one hL hr Z)

end Main

theorem normalised_polarisation : Out.Laws → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ∀ (K : Type) [Field K] (P : Out.PolAV (Sp K)) (w w' : P.A ⟶ P.A), IsMonHom w → IsMonHom w' → w * w' = 𝟙 P.A → LBIso (cubeLB P.A ![fst P.A P.A ≫ w, snd P.A P.A] P.L) (cubeLB P.A ![fst P.A P.A, snd P.A P.A ≫ w'] P.L) → ∀ M : LB P.A.left, M = cubeLB P.A ![𝟙 P.A, w] P.L → M.IsLB ∧ Out.Rigidified P.A M ∧ Out.Sym P.A M ∧ Out.RelAmple P.A M ∧ Out.KTriv P.A M ∧ LBIso (abelian₂ P.A M) (abelian₂ P.A P.L) ∧ LBIso M (cubeLB P.A ![𝟙 P.A, w] M) ∧ LBIso (cubeLB P.A ![fst P.A P.A ≫ w, snd P.A P.A] M) (cubeLB P.A ![fst P.A P.A, snd P.A P.A ≫ w'] M) := by
  intro hLaws hTh K _ P w w' hw hw' hww ha M hM
  have := P.isAb.comm
  obtain ⟨Q, cub, hQL, hQs, hQΛ⟩ := exists_normalised_bundle hLaws.globalFns P.isAb P.isLB
    (hTh _ P _ P.isLB) w w' hww ha
  obtain ⟨QL, Qrig, QLB, Qgen⟩ := Q
  dsimp only at hQL hQΛ
  subst hQL
  subst hM
  have hL := P.isLB
  have hT := hTh _ P _ P.isLB
  have hc : ∀ (T : Over (Sp K)) (x y z : T ⟶ P.A), diff₃ (ptCls P.L T) x y z = 1 :=
    fun T x y z => diff₃_ptCls hL hT x y z
  have hd : ∀ (T : Over (Sp K)) (x y : T ⟶ P.A),
      diff₂ (fun q : T ⟶ P.A => normCls P.L w q.left) x y = diff₂ (ptCls P.L T) x y := by
    intro T x y
    have hf : (fun q : T ⟶ P.A => normCls P.L w q.left) =
        fun q => diff₂ (ptCls P.L T) q (postHom w T q) := funext fun q => normCls_left w q
    rw [hf]
    refine diff₂_quadratic (hc T) (postHom w T) (postHom w' T) (fun q => ?_)
      (fun a b => diff₂_ptCls_adj hL ha a b) x y
    show q ≫ w * q ≫ w' = q
    rw [Hom.mul_def, ← comp_lift, Category.assoc, ← Hom.mul_def, hww, Category.comp_id]
  have hsym : ∀ (T : Over (Sp K)) (q : T ⟶ P.A), normCls P.L w (q⁻¹).left = normCls P.L w q.left := by
    intro T q
    rw [normCls_left, normCls_left]
    change diff₂ (ptCls P.L T) q⁻¹ (postHom w T q⁻¹) = diff₂ (ptCls P.L T) q (postHom w T q)
    rw [map_inv]
    exact diff₂_inv_inv (hc T) _ _
  have hN : ∀ {Y : Scheme.{0}} {J : Type} [Fintype J] (ψ : J → (Y ⟶ P.A.left)) (δ : J → ℤ),
      ∏ k, normCls P.L w (ψ k) ^ δ k = 1 → HasGen (cubeLB P.A ![𝟙 P.A, w] P.L) ψ δ :=
    fun ψ δ h => hasGen_nested hL _ _ ψ δ h
  refine ⟨QLB, ⟨Qrig, Qgen⟩, ?_, ?_, kTriv_norm hL P.rigid P.ktriv w hd, hQΛ _ _ _, ?_, ?_⟩
  · intro s
    refine ⟨⊤, trivial, ?_⟩
    let q : Over.mk ((P.A.hom ⁻¹ᵁ ⊤).ι ≫ P.A.hom) ⟶ P.A := Over.homMk (P.A.hom ⁻¹ᵁ ⊤).ι
    have e : (q⁻¹).left = (P.A.hom ⁻¹ᵁ ⊤).ι ≫ (ι : P.A ⟶ P.A).left := by
      rw [Hom.inv_def, Over.comp_left]
      rfl
    have hq := hsym _ q
    rw [e] at hq
    refine hN _ _ ?_
    simp only [Fin.prod_univ_two, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, zpow_one, zpow_neg]
    rw [hq]
    exact mul_inv_cancel _
  ·
    have hfin : IsFinite (Over.Hom.left (𝟙 P.A)) := by
      rw [Over.id_left]
      infer_instance
    have hA1 := GlobalTheory.relAmple_finite_pow_iso (Sp K) P.A P.A (𝟙 P.A) P.L 2 two_pos P.isAb P.isAb hL hfin
    have hA2 := GlobalTheory.relAmple_finite_pow_iso (Sp K) P.A P.A (𝟙 P.A) (lbPow P.L 2) 2 two_pos P.isAb P.isAb
      (isLB_lbPow hL 2) hfin
    have hA3 := GlobalTheory.relAmple_finite_pow_iso (Sp K) P.A P.A (𝟙 P.A) _ 2 two_pos P.isAb P.isAb QLB hfin

    have hS : cls P.L (ι : P.A ⟶ P.A).left = cls P.L (Over.Hom.left (𝟙 P.A)) := by
      obtain ⟨U, hU, t, ht⟩ := P.sym (Classical.arbitrary _)
      have hall : ∀ y : P.A.left, (𝟙 P.A.left) y ∈ P.A.hom ⁻¹ᵁ U := fun y => by
        have hy : P.A.hom y = _ := Subsingleton.elim (P.A.hom y) (Classical.arbitrary (Sp K))
        show P.A.hom y ∈ U
        rw [hy]
        exact hU
      have H : GlobalTheory.KerPow.HasGen P.L (fun k => (P.A.hom ⁻¹ᵁ U).ι ≫ ![(ι : P.A ⟶ P.A).left, 𝟙 P.A.left] k)
          ![1, -1] := by
        have hfun : (fun k => (P.A.hom ⁻¹ᵁ U).ι ≫ ![(ι : P.A ⟶ P.A).left, 𝟙 P.A.left] k) =
            ![(P.A.hom ⁻¹ᵁ U).ι ≫ (ι : P.A ⟶ P.A).left, (P.A.hom ⁻¹ᵁ U).ι] := by
          funext k
          fin_cases k <;> simp
        rw [hfun]
        exact ⟨t, ht⟩
      have H' := GlobalTheory.KerPow.HasGen.of_range H (𝟙 P.A.left) hall (φ' := ![(ι : P.A ⟶ P.A).left, (Over.Hom.left (𝟙 P.A))])
        (fun k => by fin_cases k <;> simp)
      have hp := (hasGen_iff hL _ _).1 H'
      simp only [Fin.prod_univ_two, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one, zpow_one, zpow_neg] at hp
      exact mul_inv_eq_one.mp hp
    have hsq : normCls P.L w (Over.Hom.left (𝟙 P.A)) ^ 2 = cls P.L (Over.Hom.left (𝟙 P.A)) ^ 2 := by
      have hx : ptCls P.L P.A (𝟙 P.A)⁻¹ = ptCls P.L P.A (𝟙 P.A) := by
        show cls P.L ((𝟙 P.A)⁻¹).left = cls P.L (Over.Hom.left (𝟙 P.A))
        rw [Hom.inv_def, Category.id_comp]
        exact hS
      have hself := diff₂_self (hc P.A) (ptCls_one hL P.rigid P.A) hx
      have hsplit : diff₂ (ptCls P.L P.A) (𝟙 P.A) (𝟙 P.A) =
          diff₂ (ptCls P.L P.A) (𝟙 P.A) (𝟙 P.A ≫ w) * diff₂ (ptCls P.L P.A) (𝟙 P.A) (𝟙 P.A ≫ w') := by
        rw [← diff₂_mul_right (hc P.A), Hom.mul_def, ← comp_lift, Category.assoc, ← Hom.mul_def, hww,
          Category.comp_id]
      have hsw : diff₂ (ptCls P.L P.A) (𝟙 P.A) (𝟙 P.A ≫ w') = diff₂ (ptCls P.L P.A) (𝟙 P.A) (𝟙 P.A ≫ w) := by
        rw [← diff₂_ptCls_adj hL ha, diff₂_comm]
      rw [hsw] at hsplit
      rw [normCls_left, pow_two, ← hsplit, hself]
    have hiso : LBIso (lbPow P.L 2) (lbPow (cubeLB P.A ![𝟙 P.A, w] P.L) 2) := by
      unfold lbPow
      refine LBIso.symm (lbIso_nested hL _ _ _ _ _ _ ?_)
      have h1 : normCls P.L w (𝟙 P.A.left) ^ 2 = cls P.L (𝟙 P.A.left) ^ 2 := by
        simpa only [Over.id_left] using hsq
      simpa [normCls] using h1
    have hLam2 := hA1.2.1.2 P.ample
    have hM2 := hA2.2.2.2 _ (isLB_lbPow QLB 2) hiso hLam2
    exact hA3.2.1.1 hM2
  · refine LBIso.symm (lbIso_nested hL _ _ _ _ _ _ ?_)
    have h1 : ∏ k : ULift.{0} (Finset (Fin 2)),
        normCls P.L w (psum P.A ![𝟙 P.A, w] k.down).left ^ ((-1 : ℤ) ^ (2 - k.down.card)) =
          diff₂ (ptCls P.L P.A) (𝟙 P.A) w :=
      (prod_square_id (𝟙 P.A) w (normCls P.L w)).trans (hd P.A _ _)
    have h2 : normCls P.L w (Over.Hom.left (𝟙 P.A)) = diff₂ (ptCls P.L P.A) (𝟙 P.A) w := by
      rw [normCls_left, Category.id_comp]
    have h3 : normCls P.L w (Over.Hom.left (𝟙 P.A)) = ∏ k : ULift.{0} (Finset (Fin 2)),
        cls P.L (psum P.A ![𝟙 P.A, w] k.down).left ^ ((-1 : ℤ) ^ (2 - k.down.card)) := by
      unfold normCls
      simp only [Over.id_left, Category.id_comp]
    exact h1.trans (h2.symm.trans h3)
  · refine (lbIso_iff QLB _ _ _ _).2 ?_
    have key : HasGen (cubeLB P.A ![𝟙 P.A, w] P.L)
        (Sum.elim (fun I : ULift.{0} (Finset (Fin 2)) => (psum P.A ![fst P.A P.A ≫ w, snd P.A P.A] I.down).left)
          (fun I : ULift.{0} (Finset (Fin 2)) => (psum P.A ![fst P.A P.A, snd P.A P.A ≫ w'] I.down).left))
        (Sum.elim (fun I : ULift.{0} (Finset (Fin 2)) => (-1 : ℤ) ^ (2 - I.down.card))
          (fun I => -((-1 : ℤ) ^ (2 - I.down.card)))) := by
      refine hN _ _ ?_
      rw [Fintype.prod_sum_type]
      simp only [Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib]
      rw [prod_square_id, prod_square_id, hd, hd, diff₂_ptCls_adj hL ha]
      exact mul_inv_cancel _
    have hp := (hasGen_iff QLB _ _).1 key
    rw [Fintype.prod_sum_type] at hp
    simp only [Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib] at hp
    exact mul_inv_eq_one.mp hp

end GlobalTheory.PrimNormPol
