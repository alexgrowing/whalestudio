import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.VertCmp
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UniqueIntegralLiftNormPInverse
open CategoryTheory Limits AlgebraicGeometry IsLocalRing NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.Toroidal
open GlobalTheory.VertCmp
open scoped Classical

namespace UpperTheory.IsoNorm

open Formalism.MainNotions.DIV.Cons (intO)
open MonObj

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
  {t : SAB H X}

private theorem sp_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  rw [← Spec.map_comp]; rfl

private theorem dual_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (dualMap g) ≫ spMap (dualMap f) = spMap (dualMap (g.comp f)) := by
  rw [sp_comp]
  congr 1
  refine RingHom.ext fun z => ?_
  ext <;> simp [dualMap]

private theorem eps_dual {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (a : A) :
    spMap (dualMap f) ≫ spMap (epsMul a) = spMap (epsMul (f a)) ≫ spMap (dualMap f) := by
  rw [sp_comp, sp_comp]
  congr 1
  refine RingHom.ext fun z => ?_
  ext <;> simp [dualMap, epsMul, _root_.mul_comm]

private theorem dlogDvd_iso {O O' : Type} [CommRing O] [CommRing O'] (φ : O ≃+* O') {x : Sp O ⟶ X} {p m : ℕ}
    {v : Sp (DualNumber O) ⟶ t.G.left} (hv : IsTanAtG t x v) (h : DlogDvd t x p m v) :
    DlogDvd t (spMap φ.toRingHom ≫ x) p m (spMap (dualMap φ.toRingHom) ≫ v) := by
  intro n c g hg
  let alg : ∀ (B : Type) [CommRing B] [Algebra O B], Algebra O' B := fun B _ _ =>
    ((algebraMap O B).comp φ.symm.toRingHom).toAlgebra
  have fin : ∀ (B : Type) [CommRing B] [Algebra O B] [Module.Finite O B],
      @Module.Finite O' B _ _ (alg B).toModule := fun B _ _ hB =>
    RingHom.Finite.comp (g := algebraMap O B) (f := φ.symm.toRingHom) (RingHom.finite_algebraMap.2 hB)
      (RingHom.Finite.of_surjective _ φ.symm.surjective)
  let δ : ∀ (B : Type) [CommRing B] [Algebra O B],
      Over.mk (spMap (@algebraMap O' B _ _ (alg B)) ≫ spMap φ.toRingHom ≫ x) ⟶
        Over.mk (spMap (algebraMap O B) ≫ x) := fun B _ _ =>
    Over.homMk (𝟙 _) (by
      show 𝟙 _ ≫ spMap (algebraMap O B) ≫ x =
        spMap ((algebraMap O B).comp φ.symm.toRingHom) ≫ spMap φ.toRingHom ≫ x
      rw [Category.id_comp, ← Category.assoc, sp_comp]
      congr 2
      ext a
      simp)
  have hδ : ∀ (B : Type) [CommRing B] [Algebra O B] (g : Over.mk (spMap (algebraMap O B) ≫ x) ⟶ t.G),
      (δ B ≫ g).left = g.left := fun B _ _ g => Category.id_comp _
  have hpow : ∀ (B : Type) [CommRing B] [Algebra O B] (g : Over.mk (spMap (algebraMap O B) ≫ x) ⟶ t.G),
      g ^ (p ^ n) = 1 → (δ B ≫ g) ^ (p ^ n) = 1 := fun B _ _ g hg => by
    have := map_pow (Formalism.L2.Pj.preHom (δ B)) g (p ^ n)
    rw [hg, map_one] at this
    exact this.symm
  let c' : TorsChar t x (p ^ n) :=
    { χ := fun B _ _ _ g => @TorsChar.χ _ _ _ _ _ _ _ _ _ _ _ c B _ (alg B) (fin B) (δ B ≫ g)
      mul := fun B _ _ _ g g' h1 h2 => by
        rw [MonObj.comp_mul]
        exact @TorsChar.mul _ _ _ _ _ _ _ _ _ _ _ c B _ (alg B) (fin B) _ _ (hpow B g h1) (hpow B g' h2)
      nat := fun B B' _ _ _ _ _ _ ψ g g' h1 h2 => by
        letI := alg B
        letI := alg B'
        haveI := fin B
        haveI := fin B'
        exact c.nat B B' { ψ.toRingHom with commutes' := fun r => ψ.commutes (φ.symm r) } _ _ (hpow B g h1)
          (by rw [hδ, hδ, h2]) }
  obtain ⟨w, hw⟩ := GlobalTheory.HTLevel.red_ex (t := t) (Ideal.span {(p : O) ^ n}) hv
  have h1 := h n c' w hw
  have hwt := GlobalTheory.HTLevel.red_tors (q := p ^ n) _ (by rw [Nat.cast_pow]; exact Ideal.mem_span_singleton_self _) hv w hw
  have hle : Ideal.span {(p : O) ^ n} ≤ (Ideal.span {(p : O') ^ n}).comap φ.toRingHom := by
    rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap, map_pow, map_natCast]
    exact Ideal.mem_span_singleton_self _
  let ρ := Ideal.quotientMap _ φ.toRingHom hle
  letI := alg (DualNumber (O ⧸ Ideal.span {(p : O) ^ n}))
  haveI := fin (DualNumber (O ⧸ Ideal.span {(p : O) ^ n}))
  let ψ : DualNumber (O ⧸ Ideal.span {(p : O) ^ n}) →ₐ[O'] DualNumber (O' ⧸ Ideal.span {(p : O') ^ n}) :=
    { dualMap ρ with
      commutes' := fun r => by
        show dualMap ρ (algebraMap O _ (φ.symm r)) = _
        ext <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl', ρ] }
  have h2 := c.nat _ _ ψ (δ _ ≫ w) g (hpow _ w hwt) (by
    rw [hδ, hg, hw]
    have a1 := dual_comp φ.toRingHom (Ideal.Quotient.mk (Ideal.span {(p : O') ^ n}))
    have a2 := dual_comp (Ideal.Quotient.mk (Ideal.span {(p : O) ^ n})) ρ
    exact ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ v) (a1.trans a2.symm))).trans (Category.assoc _ _ _))
  rw [h2]
  have h3 : ∀ z, (ψ z).snd = ρ z.snd := fun z => by simp [ψ, dualMap]
  rw [h3]
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton.1 h1
  refine Ideal.mem_span_singleton.2 ⟨ρ a, ?_⟩
  rw [← map_natCast ρ, ← map_pow, ← map_mul, ← ha]

variable {C C' : Type} [NontriviallyNormedField C] [IsUltrametricDist C] [NontriviallyNormedField C']
  [IsUltrametricDist C'] (j : C ≃+* C') (hj : ∀ a, ‖j a‖ = ‖a‖)

private def intEquiv : ↥(intO C) ≃+* ↥(intO C') where
  toFun a := ⟨j a, (hj a).trans_le a.2⟩
  invFun b := ⟨j.symm b, show ‖j.symm b‖ ≤ 1 by rw [← hj, j.apply_symm_apply]; exact b.2⟩
  left_inv a := Subtype.ext (j.symm_apply_apply _)
  right_inv b := Subtype.ext (j.apply_symm_apply _)
  map_mul' a b := Subtype.ext (map_mul j _ _)
  map_add' a b := Subtype.ext (map_add j _ _)

include hj in
private theorem lat_map {x : Sp C ⟶ X} {p : ℕ} {b : Bool} {v : Sp (DualNumber C) ⟶ t.G.left}
    (hv : v ∈ lat t p x b) : spMap (dualMap j.toRingHom) ≫ v ∈ lat t p (spMap j.toRingHom ≫ x) b := by
  have e : (intO C').subtype.comp (intEquiv j hj).toRingHom = j.toRingHom.comp (intO C).subtype := rfl
  have e1 : ∀ xO : Sp ↥(intO C) ⟶ X, spMap (intO C').subtype ≫ spMap (intEquiv j hj).toRingHom ≫ xO =
      spMap j.toRingHom ≫ spMap (intO C).subtype ≫ xO := fun xO => by
    rw [← Category.assoc, ← Category.assoc, sp_comp, sp_comp, e]
  have e2 : ∀ vO : Sp (DualNumber ↥(intO C)) ⟶ t.G.left,
      spMap (dualMap (intO C').subtype) ≫ spMap (dualMap (intEquiv j hj).toRingHom) ≫ vO =
      spMap (dualMap j.toRingHom) ≫ spMap (dualMap (intO C).subtype) ≫ vO := fun vO => by
    rw [← Category.assoc, ← Category.assoc, dual_comp, dual_comp, e]
  cases b
  · obtain ⟨xO, rfl, vO, h1, rfl⟩ := hv
    exact ⟨_, e1 xO, _, GlobalTheory.FactorDepth.isTanAtG_map t _ h1, e2 vO⟩
  · obtain ⟨xO, rfl, m, vO, h1, h2, h3⟩ := hv
    refine ⟨_, e1 xO, m, _, GlobalTheory.FactorDepth.isTanAtG_map t _ h1, ?_, dlogDvd_iso (intEquiv j hj) h1 h3⟩
    rw [e2, h2, ← Category.assoc, eps_dual, map_pow, map_natCast, Category.assoc]

include hj in
private theorem grSet_sub {x : Sp C ⟶ X} {p : ℕ} {b : Bool} {m : ℕ} (u : Fin m → (Sp (DualNumber C) ⟶ t.G.left))
    (i : Fin m) {x' : Sp C' ⟶ X} (hx : spMap j.toRingHom ≫ x = x')
    {u' : Fin m → (Sp (DualNumber C') ⟶ t.G.left)} (hu : (fun k => spMap (dualMap j.toRingHom) ≫ u k) = u') :
    {r : ℝ | ∃ cf : Fin m → C, cf i ≠ 0 ∧ (∀ k, i < k → cf k = 0) ∧ (∃ w ∈ lat t p x b, IsCombAtG t x u cf w) ∧
      r = ‖cf i‖⁻¹} ⊆
    {r : ℝ | ∃ cf : Fin m → C', cf i ≠ 0 ∧ (∀ k, i < k → cf k = 0) ∧ (∃ w ∈ lat t p x' b, IsCombAtG t x' u' cf w) ∧
      r = ‖cf i‖⁻¹} := by
  subst hx hu
  rintro _ ⟨cf, h0, hz, ⟨w, hw, hc⟩, rfl⟩
  exact ⟨fun k => j (cf k), (map_ne_zero j).2 h0, fun k hk => (congrArg j (hz k hk)).trans (map_zero j),
    ⟨_, lat_map j hj hw, GlobalTheory.LatDRFree.comb_map t j.toRingHom hc⟩, by rw [hj]⟩

include hj in
private theorem grNorm_iso (x : Sp C ⟶ X) (p : ℕ) (b : Bool) {m : ℕ} (u : Fin m → (Sp (DualNumber C) ⟶ t.G.left))
    (i : Fin m) : grNorm t (spMap j.toRingHom ≫ x) (lat t p (spMap j.toRingHom ≫ x) b)
      (fun k => spMap (dualMap j.toRingHom) ≫ u k) i = grNorm t x (lat t p x b) u i := by
  have e : j.symm.toRingHom.comp j.toRingHom = RingHom.id C := by ext a; simp
  have h1 : spMap (RingHom.id C) = 𝟙 _ := Spec.map_id _
  have h3 : spMap (dualMap (RingHom.id C)) = 𝟙 _ := by
    rw [← Spec.map_id]
    congr 1
    ext r <;> simp [dualMap]
  unfold grNorm
  congr 1
  refine Set.Subset.antisymm (grSet_sub j.symm (fun a => by rw [← hj, j.apply_symm_apply]) _ i ?_ ?_)
    (grSet_sub j hj u i rfl rfl)
  · rw [← Category.assoc, sp_comp, e, h1, Category.id_comp]
  · funext k
    rw [← Category.assoc, dual_comp, e, h3, Category.id_comp]

end UpperTheory.IsoNorm

theorem UpperTheory.lnStep_isometric_base_change :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (X : Scheme.{0}) (t : SAB H X) (C C' : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [NontriviallyNormedField C'] [IsUltrametricDist C'] (j : C ≃+* C'), (∀ a, ‖j a‖ = ‖a‖) → ∀ (x : Sp C ⟶ X) (u : Vecs Dw t C) (p : ℕ) (b : Bool) (st : ((E →+* ℂ) × ℕ) ⊕ ℕ), lnStep t (spMap j.toRingHom ≫ x) (Vecs.bc j.toRingHom u) p b st = lnStep t x u p b st := by
  intro E _ _ _ H Dw X t C C' _ _ _ _ j hj x u p b st
  rcases st with ⟨τ, k⟩ | k
  · simp only [lnStep]
    by_cases h : k < Dw.mult τ
    · rw [dif_pos h, dif_pos h, ← UpperTheory.IsoNorm.grNorm_iso j hj x p b (u τ)]
      rfl
    · rw [dif_neg h, dif_neg h]
  · simp only [lnStep]
    by_cases h : k < (letters Dw).length
    · rw [dif_pos h, dif_pos h, ← UpperTheory.IsoNorm.grNorm_iso j hj x p b]
      rfl
    · rw [dif_neg h, dif_neg h]
