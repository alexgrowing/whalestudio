import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.ChartRange

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC CrystallineSemistableComparison CrystallineSemistableComparison.Onto UpperTheory.Gal.KunnethLefschetz.G.PX

namespace UpperTheory.Gal.KunnethLefschetz.G.PX

variable {K : Type} [CommRing K] {W Z Y : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of K)} {i : W ⟶ Z} {π : Y ⟶ Z}
  {D : E.LineData Y} {d : ℕ}

private theorem blowup_chart_relation (B : Blow q i π D d) (α : B.ι) (k n : Fin d) :
    (π.appLE (B.V α) ((B.c α).C k) ((B.c α).C_le k)).hom ((B.c α).t n) =
      (π.appLE (B.V α) ((B.c α).C k) ((B.c α).C_le k)).hom ((B.c α).t k) * (B.c α).u k n := by
  have hmem : (MvPolynomial.C ((B.c α).t n) - MvPolynomial.C ((B.c α).t k) * MvPolynomial.X n :
      MvPolynomial (Fin d) Γ(Z, B.V α)) ∈
      RingHom.ker (MvPolynomial.eval₂Hom ((π.appLE (B.V α) ((B.c α).C k) ((B.c α).C_le k)).hom) ((B.c α).u k)) := by
    rw [(B.c α).rel k]
    exact Ideal.subset_span (Set.mem_insert_of_mem _ ⟨n, rfl⟩)
  have h0 := RingHom.mem_ker.mp hmem
  rw [map_sub, map_mul, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_X, MvPolynomial.eval₂_C,
    MvPolynomial.eval₂_C] at h0
  exact sub_eq_zero.mp h0

private theorem res_chain {V : Scheme.{0}} (y : V ⟶ Y) {A N : Z.Opens} {C : Y.Opens} (hC : C ≤ π ⁻¹ᵁ A)
    (h : ⊤ ≤ y ⁻¹ᵁ C) (n : N ≤ A) (hy : ⊤ ≤ (y ≫ π) ⁻¹ᵁ N) (s : Γ(Z, A)) :
    (y.appLE C ⊤ h).hom ((π.appLE A C hC).hom s) =
      ((y ≫ π).appLE N ⊤ hy).hom ((Z.presheaf.map (homOfLE n).op).hom s) := by
  have e1 := Scheme.Hom.appLE_comp_appLE y π A C ⊤ hC h
  have e2 := Scheme.Hom.map_appLE (y ≫ π) hy (homOfLE n).op
  have : π.appLE A C hC ≫ y.appLE C ⊤ h = Z.presheaf.map (homOfLE n).op ≫ (y ≫ π).appLE N ⊤ hy := by
    rw [e1, e2]
  exact congrArg (fun φ => φ.hom s) this

private theorem top_inv {V : Scheme.{0}} {C : Y.Opens} (g : V ⟶ (C : Scheme.{0})) (h : ⊤ ≤ (g ≫ C.ι) ⁻¹ᵁ C) (s : Γ(Y, C)) :
    g.appTop.hom (C.topIso.inv.hom s) = ((g ≫ C.ι).appLE C ⊤ h).hom s := by
  have e0 : (⊤ : (C : Scheme.{0}).Opens) ≤ C.ι ⁻¹ᵁ C := fun x _ => x.2
  have e1 := Scheme.Hom.appLE_comp_appLE g C.ι C ⊤ ⊤ e0 (fun x _ => trivial)
  have e2 : C.ι.appLE C ⊤ e0 = C.topIso.inv := by
    simp only [Scheme.Hom.appLE, Scheme.Opens.ι_app, Scheme.Opens.topIso_inv, Scheme.Opens.toScheme_presheaf_map]
    refine (Y.presheaf.map_comp _ _).symm.trans ?_
    exact congrArg _ (Subsingleton.elim _ _)
  have e3 : g.appLE ⊤ ⊤ (fun x _ => trivial) = g.appTop := by
    simp only [Scheme.Hom.appLE, Scheme.Hom.appTop]
    exact (congrArg (g.app ⊤ ≫ ·) (V.presheaf.map_id _)).trans (Category.comp_id _)
  rw [e2, e3] at e1
  exact congrArg (fun φ => φ.hom s) e1

private theorem f_sec (B : Blow q i π D d) (α : B.ι) (k : Fin d) {V : Scheme.{0}} (y : V ⟶ Y)
    (h : ⊤ ≤ y ⁻¹ᵁ (B.c α).C k) :
    B.f (secOf B α k y h) =
      (y.appLE ((B.c α).C k) ⊤ h).hom ((π.appLE (B.V α) ((B.c α).C k) ((B.c α).C_le k)).hom ((B.c α).t k)) := by
  unfold secOf
  rw [B.f_nat, B.f_σ]
  have hg : IsOpenImmersion.lift ((B.c α).C k).ι y (chart_range B α k y h) ≫ ((B.c α).C k).ι = y :=
    IsOpenImmersion.lift_fac _ _ _
  have := top_inv (IsOpenImmersion.lift ((B.c α).C k).ι y (chart_range B α k y h)) (by rw [hg]; exact h)
    ((π.appLE (B.V α) ((B.c α).C k) ((B.c α).C_le k)).hom ((B.c α).t k))
  rw [this]
  simp only [hg]

end UpperTheory.Gal.KunnethLefschetz.G.PX

theorem UpperTheory.Gal.KunnethLefschetz.G.PX.gvNzd :
    ∀ {K : Type} [CommRing K] {W Z Y : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of K)} {i : W ⟶ Z} {π : Y ⟶ Z} {D : E.LineData Y} {d : ℕ} (B : Blow q i π D d) {V : Scheme.{0}} (y : V ⟶ Y) (α β : B.ι) (k l : Fin d) (h₁ : ⊤ ≤ y ⁻¹ᵁ (B.c α).C k) (h₂ : ⊤ ≤ y ⁻¹ᵁ (B.c β).C l) {N : Z.Opens} (n₁ : N ≤ B.V α) (n₂ : N ≤ B.V β) (hy : ⊤ ≤ (y ≫ π) ⁻¹ᵁ N) (G : Matrix (Fin d) (Fin d) Γ(Z, N)), IsTr B α β n₁ n₂ G → (y.appLE ((B.c β).C l) ⊤ h₂).hom ((π.appLE (B.V β) ((B.c β).C l) ((B.c β).C_le l)).hom ((B.c β).t l)) ∈ nonZeroDivisors Γ(V, ⊤) → (G.map ((y ≫ π).appLE N ⊤ hy).hom).mulVec (uV B α k y h₁) = (((D.u (secOf B α k y h₁) (secOf B β l y h₂) ((secOf_f B α k y h₁).trans (secOf_f B β l y h₂).symm))⁻¹ : (Γ(V, ⊤))ˣ) : Γ(V, ⊤)) • uV B β l y h₂ := by
  intro K _ W Z Y q i π D d B V y α β k l h₁ h₂ N n₁ n₂ hy G hG hnz
  set a := ((y ≫ π).appLE N ⊤ hy).hom with ha
  set Tk := (y.appLE ((B.c α).C k) ⊤ h₁).hom ((π.appLE (B.V α) ((B.c α).C k) ((B.c α).C_le k)).hom ((B.c α).t k)) with hTk
  set Tl := (y.appLE ((B.c β).C l) ⊤ h₂).hom ((π.appLE (B.V β) ((B.c β).C l) ((B.c β).C_le l)).hom ((B.c β).t l)) with hTl
  set u := D.u (secOf B α k y h₁) (secOf B β l y h₂) ((secOf_f B α k y h₁).trans (secOf_f B β l y h₂).symm) with hu
  have hα : ∀ n, a (tN B α n₁ n) = Tk * uV B α k y h₁ n := by
    intro n
    have := res_chain y ((B.c α).C_le k) h₁ n₁ hy ((B.c α).t n)
    rw [blowup_chart_relation, map_mul] at this
    exact this.symm
  have hβ : ∀ n, a (tN B β n₂ n) = Tl * uV B β l y h₂ n := by
    intro n
    have := res_chain y ((B.c β).C_le l) h₂ n₂ hy ((B.c β).t n)
    rw [blowup_chart_relation, map_mul] at this
    exact this.symm
  have hf : Tk = (u : Γ(V, ⊤)) * Tl := by
    have := B.f_u (secOf B α k y h₁) (secOf B β l y h₂) ((secOf_f B α k y h₁).trans (secOf_f B β l y h₂).symm)
    rwa [f_sec, f_sec] at this
  funext m
  have hm : Tl * uV B β l y h₂ m = Tk * (G.map a).mulVec (uV B α k y h₁) m := by
    rw [← hβ, hG m, map_sum, Matrix.mulVec, dotProduct, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [map_mul, hα, Matrix.map_apply]
    ring
  rw [hf] at hm
  have h3 : Tl * (uV B β l y h₂ m - (u : Γ(V, ⊤)) * (G.map a).mulVec (uV B α k y h₁) m) = 0 := by
    rw [mul_sub, hm]; ring
  have h4 := sub_eq_zero.mp (mem_nonZeroDivisors_iff_right.mp hnz _ (by rwa [mul_comm] at h3))
  rw [Pi.smul_apply, smul_eq_mul, h4, Units.inv_mul_cancel_left]
