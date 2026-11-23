import ReciprocityTheory.AnalyticForms.RegularLocalRings.ExistsClosedOfChartIdeal

namespace ReciprocityTheory.AnForm.R

open MvPolynomial AlgebraicGeometry CategoryTheory

noncomputable section

theorem appLE_constSec_eq {S T : Scheme.{0}} (t : T ⟶ Spec (.of ℂ)) (g : S ⟶ T) {U : T.Opens}
    {V : S.Opens} (h : V ≤ g ⁻¹ᵁ U) (c : ℂ) :
    g.appLE U V h (constSec t U c) = constSec (g ≫ t) V c := by
  exact congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom c))
    (Scheme.Hom.appLE_comp_appLE g t ⊤ U V le_top h)

theorem constSec_map_res {S : Scheme.{0}} (s : S ⟶ Spec (.of ℂ)) {U V : S.Opens} (h : V ≤ U) (c : ℂ) :
    S.presheaf.map (homOfLE h).op (constSec s U c) = constSec s V c := by
  exact congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom c))
    (Scheme.Hom.appLE_map s (le_top : U ≤ s ⁻¹ᵁ ⊤) (homOfLE h).op)

variable {K : Type} [Fintype K] [Nonempty K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable {P D : Ideal (MvPolynomial (Σ k, ι k) ℂ)} {hP : IsMultiHomogIdeal P}

theorem map_eval₂_constSec {S : Scheme.{0}} (s : S ⟶ Spec (.of ℂ)) {U V : S.Opens} (h : V ≤ U)
    {σ : Type} (u : σ → Γ(S, U)) (f : MvPolynomial σ ℂ) :
    S.presheaf.map (homOfLE h).op (eval₂ (constSec s U) u f) =
      eval₂ (constSec s V) (fun q => S.presheaf.map (homOfLE h).op (u q)) f := by
  have e := MvPolynomial.eval₂_comp_left (S.presheaf.map (homOfLE h).op).hom (constSec s U) u f
  refine e.trans ?_
  congr 1
  exact RingHom.ext fun c => constSec_map_res s h c

theorem chart_eval₂_overlap (p p' : (k : K) → ι k) (f : MvPolynomial (Σ k, ι k) ℂ) (a : K → ℕ)
    (hf : IsMultiHomog f a) :
    ∃ u : Γ(projX P hP, (chartOpen hP p).1 ⊓ (chartOpen hP p').1), IsUnit u ∧
      (projX P hP).presheaf.map (homOfLE (inf_le_right : (chartOpen hP p).1 ⊓ (chartOpen hP p').1 ≤ _)).op
          (eval₂ (constSec (toSpecC hP) (chartOpen hP p').1) (chartCoord hP p') f) =
        u * (projX P hP).presheaf.map
          (homOfLE (inf_le_left : (chartOpen hP p).1 ⊓ (chartOpen hP p').1 ≤ _)).op
          (eval₂ (constSec (toSpecC hP) (chartOpen hP p).1) (chartCoord hP p) f) := by
  have hinv : ∀ k,
      (projX P hP).presheaf.map (homOfLE (inf_le_right : (chartOpen hP p).1 ⊓ (chartOpen hP p').1 ≤ _)).op
          (chartCoord hP p' ⟨k, p k⟩) *
        (projX P hP).presheaf.map (homOfLE (inf_le_left : (chartOpen hP p).1 ⊓ (chartOpen hP p').1 ≤ _)).op
          (chartCoord hP p ⟨k, p' k⟩) = 1 := by
    intro k
    have h := chartCoord_overlap hP p p' ⟨k, p' k⟩
    dsimp only at h
    rw [mul_comm, h, chartCoord_self, map_one]
  refine ⟨∏ k, ((projX P hP).presheaf.map
      (homOfLE (inf_le_right : (chartOpen hP p).1 ⊓ (chartOpen hP p').1 ≤ _)).op
        (chartCoord hP p' ⟨k, p k⟩)) ^ a k, ?_, ?_⟩
  · have h1 : (∏ k, ((projX P hP).presheaf.map
        (homOfLE (inf_le_right : (chartOpen hP p).1 ⊓ (chartOpen hP p').1 ≤ _)).op
          (chartCoord hP p' ⟨k, p k⟩)) ^ a k) * (∏ k, ((projX P hP).presheaf.map
        (homOfLE (inf_le_left : (chartOpen hP p).1 ⊓ (chartOpen hP p').1 ≤ _)).op
          (chartCoord hP p ⟨k, p' k⟩)) ^ a k) = 1 := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_eq_one fun k _ => ?_
      rw [← mul_pow, hinv k, one_pow]
    exact ⟨⟨_, _, h1, by rw [mul_comm]; exact h1⟩, rfl⟩
  · rw [map_eval₂_constSec, map_eval₂_constSec]
    have hco : (fun q => (projX P hP).presheaf.map
        (homOfLE (inf_le_right : (chartOpen hP p).1 ⊓ (chartOpen hP p').1 ≤ _)).op (chartCoord hP p' q)) =
        fun q => (projX P hP).presheaf.map
          (homOfLE (inf_le_right : (chartOpen hP p).1 ⊓ (chartOpen hP p').1 ≤ _)).op
            (chartCoord hP p' ⟨q.1, p q.1⟩) *
          (projX P hP).presheaf.map
            (homOfLE (inf_le_left : (chartOpen hP p).1 ⊓ (chartOpen hP p').1 ≤ _)).op
              (chartCoord hP p q) := by
      funext q
      rw [← chartCoord_overlap hP p p' q, mul_comm]
    have key := eval₂_smul_of_isMultiHomog' (R := Γ(projX P hP, (chartOpen hP p).1 ⊓ (chartOpen hP p').1))
      (constSec (toSpecC hP) ((chartOpen hP p).1 ⊓ (chartOpen hP p').1)) hf
      (fun k => (projX P hP).presheaf.map
          (homOfLE (inf_le_right : (chartOpen hP p).1 ⊓ (chartOpen hP p').1 ≤ _)).op
            (chartCoord hP p' ⟨k, p k⟩))
      (fun q => (projX P hP).presheaf.map
            (homOfLE (inf_le_left : (chartOpen hP p).1 ⊓ (chartOpen hP p').1 ≤ _)).op
              (chartCoord hP p q))
    rw [hco]
    exact key

namespace WData

variable (w : WData P D hP)

theorem secHom_bind_lift (c : w.Idx) (f : MvPolynomial (Σ k, ι k) ℂ) :
    (w.pres c.1 c.2).secHom (bind₁ (w.lift c) f) =
      w.π.appLE _ (w.pres c.1 c.2).V (w.le_pres c.1 c.2)
        (eval₂ (constSec (toSpecC hP) (chartOpen hP c.1).1) (chartCoord hP c.1) f) := by
  have h : ((w.pres c.1 c.2).secHom).comp (bind₁ (w.lift c)).toRingHom =
      (w.π.appLE _ (w.pres c.1 c.2).V (w.le_pres c.1 c.2)).hom.comp
        (eval₂Hom (constSec (toSpecC hP) (chartOpen hP c.1).1) (chartCoord hP c.1)) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, bind₁_C_right,
        coe_eval₂Hom, eval₂_C]
      rw [AffPres.secHom_C, appLE_constSec_eq]
    · intro q
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, bind₁_X_right,
        coe_eval₂Hom, eval₂_X]
      by_cases hq : q.2 = c.1 q.1
      · have e : w.lift c q = 1 := by simp [lift, hq]
        rw [e, map_one]
        obtain ⟨k, i⟩ := q
        simp only at hq
        subst hq
        rw [chartCoord_self, map_one]
      · have e : w.lift c q = X (w.yq c.1 c.2 q) := by simp [lift, hq]
        rw [e, w.sec_yq]
  exact RingHom.congr_fun h f

theorem germ_lift_ratio (f : MvPolynomial (Σ k, ι k) ℂ) (a : K → ℕ) (hf : IsMultiHomog f a)
    (c c' : w.Idx) (x : w.W) (hx : x ∈ (w.pres c.1 c.2).V) (hx' : x ∈ (w.pres c'.1 c'.2).V) :
    ∃ u : (w.W.presheaf.stalk x)ˣ,
      w.W.presheaf.germ _ x hx ((w.pres c.1 c.2).secHom (bind₁ (w.lift c) f)) =
        u * w.W.presheaf.germ _ x hx' ((w.pres c'.1 c'.2).secHom (bind₁ (w.lift c') f)) := by
  obtain ⟨u, hu, he⟩ := chart_eval₂_overlap (hP := hP) c.1 c'.1 f a hf
  have hVO : (w.pres c.1 c.2).V ⊓ (w.pres c'.1 c'.2).V ≤
      w.π ⁻¹ᵁ ((chartOpen hP c.1).1 ⊓ (chartOpen hP c'.1).1) := fun y hy =>
    ⟨w.le_pres c.1 c.2 hy.1, w.le_pres c'.1 c'.2 hy.2⟩
  have hxx : x ∈ (w.pres c.1 c.2).V ⊓ (w.pres c'.1 c'.2).V := ⟨hx, hx'⟩
  have hU : IsUnit (w.W.presheaf.germ _ x hxx (w.π.appLE _ _ hVO u)) :=
    (hu.map (w.π.appLE _ _ hVO).hom).map _
  refine ⟨hU.unit⁻¹, ?_⟩
  have e1 : ∀ (d : w.Idx) (hd : (w.pres c.1 c.2).V ⊓ (w.pres c'.1 c'.2).V ≤ (w.pres d.1 d.2).V)
      (hO : (chartOpen hP c.1).1 ⊓ (chartOpen hP c'.1).1 ≤ (chartOpen hP d.1).1)
      (hxd : x ∈ (w.pres d.1 d.2).V),
      w.W.presheaf.germ _ x hxd ((w.pres d.1 d.2).secHom (bind₁ (w.lift d) f)) =
        w.W.presheaf.germ _ x hxx (w.π.appLE _ _ hVO ((projX P hP).presheaf.map (homOfLE hO).op
          (eval₂ (constSec (toSpecC hP) (chartOpen hP d.1).1) (chartCoord hP d.1) f))) := by
    intro d hd hO hxd
    rw [w.secHom_bind_lift d f, ← TopCat.Presheaf.germ_res_apply w.W.presheaf (homOfLE hd) x hxx]
    congr 1
    show (w.π.appLE _ _ _ ≫ w.W.presheaf.map (homOfLE hd).op).hom _ =
      ((projX P hP).presheaf.map (homOfLE hO).op ≫ w.π.appLE _ _ hVO).hom _
    rw [Scheme.Hom.appLE_map, Scheme.Hom.map_appLE]
  rw [e1 c inf_le_left inf_le_left hx, e1 c' inf_le_right inf_le_right hx', he, map_mul, map_mul,
    ← mul_assoc]
  rw [hU.val_inv_mul, one_mul]

end WData

end

end ReciprocityTheory.AnForm.R
