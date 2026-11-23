import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.PfFrom
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.TestOfPre

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory TensorProduct GroundTheory.PAdicHodge CrystallineSemistableComparison.CH

namespace CrystallineSemistableComparison.D

variable (l : ℕ) [Fact l.Prime]

theorem split_clause (A : PfC l (Ob l)) (B : Type) [CommRing B] [Algebra (Ob l) B] [Algebra A.obj B]
    [IsScalarTower (Ob l) A.obj B] (hB : Pf l B) (hS : Splits l (algebraMap (Ob l) A.obj (rt l 0)) (algebraMap A.obj B)) :
    ∀ (t : Test l) (x : A ⟶ (testι l ⋙ toPf l).obj t), ∃ y : pfOb (R := Ob l) B hB ⟶ (testι l ⋙ toPf l).obj t, pfFrom A B hB ≫ y = x := by
  intro t x
  let xa : A.obj →ₐ[Ob l] t.obj.A := x.hom.hom
  have hPf : Pf l t.obj.A := ⟨t.obj.natCast_l, t.obj.perf.bijective_frobenius⟩
  have hV : VAL ((xa : A.obj →+* t.obj.A) (algebraMap (Ob l) A.obj (rt l 0))) := by
    have e : (xa : A.obj →+* t.obj.A) (algebraMap (Ob l) A.obj (rt l 0)) = t.obj.pi := by
      change xa (algebraMap (Ob l) A.obj (rt l 0)) = t.obj.s (pFlat l)
      rw [xa.commutes, ← (isRt_rt l).2]; rfl
    rw [e]; exact t.property.2
  obtain ⟨y, hy⟩ := hS t.obj.A (xa : A.obj →+* t.obj.A) hPf t.property.1 hV
  let ya : B →ₐ[Ob l] t.obj.A :=
    { y with
      commutes' := fun c => by
        change y (algebraMap (Ob l) B c) = algebraMap (Ob l) t.obj.A c
        rw [IsScalarTower.algebraMap_apply (Ob l) A.obj B c, ← RingHom.comp_apply, hy]
        exact xa.commutes c }
  refine ⟨ObjectProperty.homMk (CommAlgCat.ofHom ya), ?_⟩
  apply ObjectProperty.hom_ext
  apply CommAlgCat.hom_ext
  apply AlgHom.ext
  intro a
  change y (algebraMap A.obj B a) = xa a
  exact RingHom.congr_fun hy a

theorem test_clause (N : Type) [AddCommGroup N] [Module (Ob l) N] (M : ℕ) (hN : ∀ x : N, pFlat l ^ M • x = 0)
    (B : Type) [CommRing B] [Algebra (Ob l) B] (hB : Pf l B) (hA : AIC B) (hV : VAL (algebraMap (Ob l) B (rt l 0))) :
    ∃ (t₀ : Test l) (g : pfOb (R := Ob l) B hB ⟶ (testι l ⋙ toPf l).obj t₀),
      (∀ (t : Test l) (y : pfOb (R := Ob l) B hB ⟶ (testι l ⋙ toPf l).obj t), ∃! φ : t₀ ⟶ t, g ≫ (testι l ⋙ toPf l).map φ = y) ∧
      Almost (Ideal.span (Set.range (rt l))) ((tensF l (Ob l) N).map g).hom := by
  have hr := isRt_rt l
  have hIsRt : IsRt l (fun k => algebraMap (Ob l) B (rt l k)) := fun k => by
    simp only; rw [← map_pow, hr.1 k]
  obtain ⟨T, _, g, hPf, hAIC, hVAL, hcompl, hnzd, hsurj, hinj, huniv⟩ :=
    Leaf.test_of_pre l B (fun k => algebraMap (Ob l) B (rt l k)) hB hIsRt hA hV
  let s : Ob l →+* T := g.comp (algebraMap (Ob l) B)
  have hs0 : s (pFlat l) = g (algebraMap (Ob l) B (rt l 0)) := by
    simp only [s, RingHom.comp_apply, hr.2]
  letI : Algebra (Ob l) T := s.toAlgebra
  let P0 : PAlg l :=
    { A := T, s := s, perf := ⟨hPf.bij⟩
      compl := by rw [hs0]; exact hcompl
      tf := by rw [hs0]; exact hnzd }
  let t₀ : Test l := ⟨P0, hAIC, by show VAL (s (pFlat l)); rw [hs0]; exact hVAL⟩
  let gA : B →ₐ[Ob l] T := { g with commutes' := fun _ => rfl }
  let g' : pfOb (R := Ob l) B hB ⟶ (testι l ⋙ toPf l).obj t₀ := ObjectProperty.homMk (CommAlgCat.ofHom gA)
  refine ⟨t₀, g', ?_, ?_⟩
  · intro t y
    let ya : B →ₐ[Ob l] t.obj.A := y.hom.hom
    have hc : (ya : B →+* t.obj.A) (algebraMap (Ob l) B (rt l 0)) = t.obj.s (pFlat l) := by
      change ya (algebraMap (Ob l) B (rt l 0)) = _
      rw [ya.commutes, hr.2]; rfl
    obtain ⟨ψ, hψ, huq⟩ := huniv t.obj.A (ya : B →+* t.obj.A) (by rw [hc]; exact t.obj.compl) (by rw [hc]; exact t.obj.tf)
    have hcomm : ψ.comp P0.s = t.obj.s := by
      ext c
      change ψ (g (algebraMap (Ob l) B c)) = t.obj.s c
      rw [← RingHom.comp_apply ψ g, hψ]
      exact ya.commutes c
    refine ⟨ObjectProperty.homMk (⟨ψ, hcomm⟩ : PAlg.Hom P0 t.obj), ?_, ?_⟩
    · apply ObjectProperty.hom_ext
      apply CommAlgCat.hom_ext
      apply AlgHom.ext
      intro b
      change ψ (g b) = ya b
      exact RingHom.congr_fun hψ b
    · intro φ hφ
      apply ObjectProperty.hom_ext
      apply PAlg.Hom.ext
      apply huq
      ext b
      have := congrArg (fun u => u.hom.hom b) hφ
      exact this
  · have key : ((tensF l (Ob l) N).map g').hom = gA.toLinearMap.lTensor N := rfl
    obtain ⟨hsT, hkT⟩ := Leaf.tens_compl (Ob l) (rt l) M N B T gA (by rw [hr.2]; exact hN)
      (fun y => hsurj M y) (fun x hx k => by rw [Algebra.smul_def]; exact hinj M x hx k)
    rw [key]
    intro a ha
    refine ⟨?_, fun y => ?_⟩
    · induction ha using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨k, rfl⟩ := hx
        intro w hw; exact hkT w hw k
      | zero => intro w _; exact zero_smul _ _
      | add x y _ _ hx hy => intro w hw; rw [add_smul, hx w hw, hy w hw, add_zero]
      | smul c x _ hx => intro w hw; rw [smul_eq_mul, mul_smul, hx w hw, smul_zero]
    · exact hsT (a • y)

end CrystallineSemistableComparison.D
