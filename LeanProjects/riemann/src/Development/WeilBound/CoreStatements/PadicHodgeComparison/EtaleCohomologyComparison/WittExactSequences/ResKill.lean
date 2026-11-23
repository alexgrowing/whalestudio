import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.ObFacts

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory TensorProduct GroundTheory.PAdicHodge CrystallineSemistableComparison.CH

universe w v u v' u' v'' u''

namespace CrystallineSemistableComparison.D

section Span
universe w₁
variable {R : Type} [CommRing R]

theorem res_add {K : Cx.{w} R} {M : Type w₁} [AddCommGroup M] [Module R M] {ε : M →ₗ[R] K.X 0} {a b : R}
    (ha : K.ResUpTo a ε) (hb : K.ResUpTo b ε) : K.ResUpTo (a + b) ε := by
  refine ⟨ha.1, fun x hx => ?_, fun y hy => ?_, fun n y hy => ?_⟩
  · rw [add_smul, ha.2.1 x hx, hb.2.1 x hx, add_zero]
  · obtain ⟨x, hx⟩ := ha.2.2.1 y hy
    obtain ⟨x', hx'⟩ := hb.2.2.1 y hy
    exact ⟨x + x', by rw [map_add, hx, hx', add_smul]⟩
  · obtain ⟨x, hx⟩ := ha.2.2.2 n y hy
    obtain ⟨x', hx'⟩ := hb.2.2.2 n y hy
    exact ⟨x + x', by rw [map_add, hx, hx', add_smul]⟩

theorem res_mul {K : Cx.{w} R} {M : Type w₁} [AddCommGroup M] [Module R M] {ε : M →ₗ[R] K.X 0} (r : R) {a : R}
    (ha : K.ResUpTo a ε) : K.ResUpTo (r * a) ε := by
  refine ⟨ha.1, fun x hx => ?_, fun y hy => ?_, fun n y hy => ?_⟩
  · rw [mul_smul, ha.2.1 x hx, smul_zero]
  · obtain ⟨x, hx⟩ := ha.2.2.1 y hy
    exact ⟨r • x, by rw [map_smul, hx, mul_smul]⟩
  · obtain ⟨x, hx⟩ := ha.2.2.2 n y hy
    exact ⟨r • x, by rw [map_smul, hx, mul_smul]⟩

theorem res_kill {K : Cx.{w} R} {M : Type w₁} [AddCommGroup M] [Module R M] {ε : M →ₗ[R] K.X 0} (a : R)
    (h0 : ∀ x, K.d 0 (ε x) = 0) (hM : ∀ x : M, a • x = 0) (hK : ∀ n (y : K.X n), a • y = 0) : K.ResUpTo a ε :=
  ⟨h0, fun x _ => hM x, fun y _ => ⟨0, by rw [map_zero, hK]⟩, fun n y _ => ⟨0, by rw [map_zero, hK]⟩⟩

theorem d_ptsAug {C : Type u} [Category.{v} C] {T : Type u'} [Category.{v'} T] (j : T ⥤ C)
    (F : C ⥤ ModuleCat.{w} R) (A : C) (x : F.obj A) : d (elF (pts j A) (j ⋙ F)) 0 (ptsAug j F A x) = 0 := by
  funext s
  have key : ∀ i : Fin 2, ((elF (pts j A) (j ⋙ F)).map (GlobalTheory.CatH.toLast i s)).hom (ptsAug j F A x (GlobalTheory.CatH.face i s)) =
      (F.map (s.obj (Fin.last 1)).2).hom x := by
    intro i
    change (F.map ((GlobalTheory.CatH.face i s).obj (Fin.last 0)).2 ≫ F.map (j.map (GlobalTheory.CatH.toLast i s).1)).hom x = _
    rw [← F.map_comp]
    congr 3
    exact (GlobalTheory.CatH.toLast i s).2
  change ∑ i : Fin 2, (-1 : ℤ) ^ (i : ℕ) • ((elF (pts j A) (j ⋙ F)).map (GlobalTheory.CatH.toLast i s)).hom
    (ptsAug j F A x (GlobalTheory.CatH.face i s)) = 0
  rw [Fin.sum_univ_two, key, key]
  simp

end Span

def ptsG {C : Type u} [Category.{v} C] {T : Type u'} [Category.{v'} T] (j : T ⥤ C)
    {C' : Type u''} [Category.{v} C'] (G : C ⥤ C') (A : C) : pts j A ⟶ pts (j ⋙ G) (G.obj A) where
  app t := TypeCat.ofHom fun y => G.map y
  naturality t t' φ := by
    ext y
    exact G.map_comp y (j.map φ)

theorem des_ff {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {T : Type u'} [Category.{v'} T] (j : T ⥤ C)
    {C' : Type u''} [Category.{v} C'] (G : C ⥤ C') [G.Full] [G.Faithful] (F : C' ⥤ ModuleCat.{w} R) (s : R) :
    DesJ (j ⋙ G) F s → DesJ j (G ⋙ F) s := by
  intro h A
  have hb : ∀ t, Function.Bijective ((ptsG j G A).app t) := fun t =>
    ⟨fun y y' (e : G.map y = G.map y') => G.map_injective e, fun y => ⟨G.preimage y, G.map_preimage y⟩⟩
  have := (CrystallineSemistableComparison.P.res_semilinear (elMor (ptsG j G A) ((j ⋙ G) ⋙ F)).hom (ptsAug (j ⋙ G) F (G.obj A))
    (ptsAug j (G ⋙ F) A) LinearMap.id s Function.bijective_id (CrystallineSemistableComparison.P.el_iso _ _ hb) (fun x => rfl)).1 (h (G.obj A))
  exact this

theorem des_span {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {T : Type u'} [Category.{v'} T] (j : T ⥤ C) (F : C ⥤ ModuleCat.{w} R) (S : Set R)
    (h : ∀ a ∈ S, DesJ j F a ∨ ∀ (A : C) (x : F.obj A), a • x = 0) : ∀ s ∈ Ideal.span S, DesJ j F s := by
  have kill : ∀ a : R, (∀ (A : C) (x : F.obj A), a • x = 0) → DesJ j F a := fun a ha A =>
    res_kill a (d_ptsAug j F A) (ha A) fun n y => by funext s; exact ha _ (y s)
  intro s hs
  induction hs using Submodule.span_induction with
  | mem a ha => exact (h a ha).elim id (kill a)
  | zero => exact kill 0 fun _ x => zero_smul R x
  | add a b _ _ ha hb => exact fun A => res_add (ha A) (hb A)
  | smul r a _ ha => exact fun A => res_mul r (ha A)

end CrystallineSemistableComparison.D
