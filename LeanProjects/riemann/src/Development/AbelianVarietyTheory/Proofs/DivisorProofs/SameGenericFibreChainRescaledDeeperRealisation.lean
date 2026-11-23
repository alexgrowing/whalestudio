import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.SameChain

theorem spec_endo_eq_id {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (R : Subalgebra o Ω)
    (frac : ∀ x : Ω, ∃ a ∈ R, ∃ b ∈ R, x = a / b) (g : Sp Ω ⟶ Sp Ω)
    (h : g ≫ spMap R.val.toRingHom = spMap R.val.toRingHom) : g = 𝟙 _ := by
  obtain ⟨ψ, rfl⟩ := Spec.map_surjective g
  have h2 : CommRingCat.ofHom R.val.toRingHom ≫ ψ = CommRingCat.ofHom R.val.toRingHom :=
    Spec.map_injective (by rw [Spec.map_comp]; exact h)
  have e : ∀ c ∈ R, ψ.hom c = c := fun c hc => congrArg (fun f => f.hom (⟨c, hc⟩ : R)) h2
  have hψ : ψ = 𝟙 _ := by
    ext x
    obtain ⟨a, ha, b, hb, rfl⟩ := frac x
    simp [map_div₀, e a ha, e b hb]
  rw [hψ, Spec.map_id]

theorem sec_of_pt {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} (ρ : S.Real) {G : Over (Sp Ω)}
    (a : G.left ⟶ ρ.P.A.left) (h : IsPullback a G.hom ρ.P.A.hom (spMap S.R.val.toRingHom)) (w : Sp Ω ⟶ G.left)
    (x : S.Gam) (hw : w ≫ a = spMap S.R.val.toRingHom ≫ (ρ.pt x).left) : w ≫ G.hom = 𝟙 _ := by
  refine spec_endo_eq_id S.R S.frac _ ?_
  rw [Category.assoc, ← h.w, ← Category.assoc, hw, Category.assoc, Over.w (ρ.pt x)]
  simp

end GlobalTheory.Poinc.SameChain

open GlobalTheory.Poinc.SameChain in

theorem GlobalTheory.Poinc.same_chain_deep : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (ε₁ : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (D : Deep X₁ ε₁)
  (c₀ : X₁.Ω₁) (hc : c₀ ≠ 0) (R' : Subalgebra X₁.o₁ X₁.Ω₁) (fg : R'.FG) (frac : ∀ x : X₁.Ω₁, ∃ a ∈ R', ∃ b ∈ R', x = a / b) (hth : ∀ x, c₀ * X₁.S.th x ∈ R') (hev : ∀ x k, c₀ * X₁.S.ev x k ∈ R') (ρ' : (X₁.S.rechart c₀ hc R' fg frac hth hev).Real) (ε' : Matrix (Fin 8) (Fin 8) ℤ → (ρ'.P.A ⟶ ρ'.P.A))
  (c₂ : D.X.Ω₁) (hc₂ : c₂ ≠ 0) (R₂ : Subalgebra D.X.o₁ D.X.Ω₁) (fg₂ : R₂.FG) (frac₂ : ∀ x : D.X.Ω₁, ∃ a ∈ R₂, ∃ b ∈ R₂, x = a / b) (hth₂ : ∀ x, c₂ * D.X.S.th x ∈ R₂) (hev₂ : ∀ x k, c₂ * D.X.S.ev x k ∈ R₂) (ρ₂ : (D.X.S.rechart c₂ hc₂ R₂ fg₂ frac₂ hth₂ hev₂).Real) (ε₂ : Matrix (Fin 8) (Fin 8) ℤ → (ρ₂.P.A ⟶ ρ₂.P.A)),
  Same X₁.ρ ε₁ ρ' ε' (fun x => x) (RingHom.id _) → Same D.X.ρ D.ε ρ₂ ε₂ (fun x => x) (RingHom.id _) →
  Same ρ' ε' ρ₂ ε₂ (fun a => D.lab a) (algebraMap X₁.Ω₁ D.X.Ω₁) := by
  intro g n F W Z i X₁ ε₁ D c₀ hc R' fg frac hth hev ρ' ε' c₂ hc₂ R₂ fg₂ frac₂ hth₂ hev₂ ρ₂ ε₂ h1 h3
  obtain ⟨P₁, a₁, a₁', e₁, pa₁, pa₁', L₁, L₁', E₁, T₁⟩ := h1
  obtain ⟨P₀, b, b', e₀, pb, pb', L₀, L₀', E₀, T₀⟩ := D.same
  obtain ⟨P₃, c, c', e₃, pc, pc', L₃, L₃', E₃, T₃⟩ := h3
  have pa₁c : IsGrpPullback P₁.A X₁.ρ.P.A (spMap X₁.S.R.val.toRingHom) a₁ := pa₁.congr (by rw [RingHom.id_comp]) rfl
  have pcc : IsGrpPullback P₃.A D.X.ρ.P.A (spMap D.X.S.R.val.toRingHom) c := pc.congr (by rw [RingHom.id_comp]) rfl
  have hspc := Geo.Tor.spMap_comp X₁.S.R.val.toRingHom (algebraMap X₁.Ω₁ D.X.Ω₁)
  have pbc : IsGrpPullback P₀.A X₁.ρ.P.A (spMap (algebraMap X₁.Ω₁ D.X.Ω₁) ≫ spMap X₁.S.R.val.toRingHom) b :=
    pb.congr hspc rfl
  have wm : b ≫ X₁.ρ.P.A.hom = (P₀.A.hom ≫ spMap (algebraMap X₁.Ω₁ D.X.Ω₁)) ≫ spMap X₁.S.R.val.toRingHom := by
    rw [pbc.1.w, Category.assoc]
  set m := pa₁c.1.lift b (P₀.A.hom ≫ spMap (algebraMap X₁.Ω₁ D.X.Ω₁)) wm with hmdef
  have hm1 : m ≫ a₁ = b := pa₁c.1.lift_fst _ _ wm
  have hm2 : m ≫ P₁.A.hom = P₀.A.hom ≫ spMap (algebraMap X₁.Ω₁ D.X.Ω₁) := pa₁c.1.lift_snd _ _ wm
  have pm : IsGrpPullback P₀.A P₁.A (spMap (algebraMap X₁.Ω₁ D.X.Ω₁)) m := pa₁c.cancel (pbc.congr rfl hm1.symm) hm2
  obtain ⟨e, he_mon, he⟩ := grpPullback_iso pb' pcc
  haveI := he_mon
  have pe := isGrpPullback_of_iso e
  refine ⟨P₀, m ≫ a₁', e.hom.left ≫ c', e₀, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (pm.comp pa₁').congr (Geo.Tor.spMap_comp R'.val.toRingHom (algebraMap X₁.Ω₁ D.X.Ω₁)).symm rfl
  · exact (pe.comp pc').congr (Category.id_comp _) rfl
  · have A : LBIso (X₁.ρ.P.L.pull b) (P₁.L.pull m) :=
      LBIso.chartPull (chartPullSame X₁.ρ.P.L (K := PUnit) (fun _ => b) (fun _ => a₁) (fun _ => 1) m
        (fun _ => hm1.symm)) (chartPullPull P₁.L m) L₁.symm
    have B : LBIso (P₁.L.pull m) (ρ'.P.L.pull (m ≫ a₁')) :=
      LBIso.chartPull (chartPullPull P₁.L m) (chartPullSame ρ'.P.L (K := PUnit) (fun _ => m ≫ a₁') (fun _ => a₁')
        (fun _ => 1) m (fun _ => rfl)) L₁'
    exact LBIso.trans P₀.isLB (pull_isLB P₁.isLB m) (pull_isLB ρ'.P.isLB _)
      (LBIso.trans P₀.isLB (pull_isLB X₁.ρ.P.isLB b) (pull_isLB P₁.isLB m) L₀ A) B
  · have A : LBIso (D.X.ρ.P.L.pull b') (P₃.L.pull e.hom.left) :=
      LBIso.chartPull (chartPullSame D.X.ρ.P.L (K := PUnit) (fun _ => b') (fun _ => c) (fun _ => 1) e.hom.left
        (fun _ => he.symm)) (chartPullPull P₃.L e.hom.left) L₃.symm
    have B : LBIso (P₃.L.pull e.hom.left) (ρ₂.P.L.pull (e.hom.left ≫ c')) :=
      LBIso.chartPull (chartPullPull P₃.L e.hom.left) (chartPullSame ρ₂.P.L (K := PUnit)
        (fun _ => e.hom.left ≫ c') (fun _ => c') (fun _ => 1) e.hom.left (fun _ => rfl)) L₃'
    exact LBIso.trans P₀.isLB (pull_isLB P₃.isLB _) (pull_isLB ρ₂.P.isLB _)
      (LBIso.trans P₀.isLB (pull_isLB D.X.ρ.P.isLB b') (pull_isLB P₃.isLB _) L₀' A) B
  · intro E
    have k1 : (e₀ E).left ≫ m = m ≫ (e₁ E).left := by
      apply pa₁c.1.hom_ext
      · rw [Category.assoc, hm1, (E₀ E).1, Category.assoc, (E₁ E).1, ← Category.assoc, hm1]
      · rw [Category.assoc, hm2, ← Category.assoc, Over.w (e₀ E), Category.assoc, Over.w (e₁ E), hm2]
    have k3 : (e₀ E).left ≫ e.hom.left = e.hom.left ≫ (e₃ E).left := by
      apply pcc.1.hom_ext
      · rw [Category.assoc, he, (E₀ E).2, Category.assoc, (E₃ E).1, ← Category.assoc, he]
      · rw [Category.assoc, Over.w e.hom, Over.w (e₀ E), Category.assoc, Over.w (e₃ E), Over.w e.hom]
    refine ⟨?_, ?_⟩
    · rw [← Category.assoc, k1, Category.assoc, (E₁ E).2, Category.assoc]
    · rw [← Category.assoc, k3, Category.assoc, (E₃ E).2, Category.assoc]
  · intro x
    obtain ⟨w, hw, hw'⟩ := T₀ x
    obtain ⟨w₁, hw₁, hw₁'⟩ := T₁ x
    obtain ⟨w₃, hw₃, hw₃'⟩ := T₃ (D.lab x)
    have s0 : w ≫ P₀.A.hom = 𝟙 _ := sec_of_pt D.X.ρ b' pb'.1 w _ hw'
    have s1 : w₁ ≫ P₁.A.hom = 𝟙 _ := sec_of_pt ρ' a₁' pa₁'.1 w₁ _ hw₁'
    have s3 : w₃ ≫ P₃.A.hom = 𝟙 _ := sec_of_pt ρ₂ c' pc'.1 w₃ _ hw₃'
    have hwm : w ≫ m = spMap (algebraMap X₁.Ω₁ D.X.Ω₁) ≫ w₁ := by
      apply pa₁c.1.hom_ext
      · rw [Category.assoc, hm1, hw, Category.assoc, hw₁, hspc, Category.assoc, RingHom.id_comp]
      · rw [Category.assoc, hm2, ← Category.assoc, s0, Category.id_comp, Category.assoc, s1, Category.comp_id]
    have hwe : w ≫ e.hom.left = w₃ := by
      apply pcc.1.hom_ext
      · rw [Category.assoc, he, hw', hw₃, RingHom.id_comp]
      · rw [Category.assoc, Over.w e.hom, s0, s3]
    refine ⟨w, ?_, ?_⟩
    · rw [← Category.assoc, hwm, Category.assoc, hw₁', Geo.Tor.spMap_comp R'.val.toRingHom (algebraMap X₁.Ω₁ D.X.Ω₁),
        Category.assoc]
    · rw [← Category.assoc, hwe, hw₃']
