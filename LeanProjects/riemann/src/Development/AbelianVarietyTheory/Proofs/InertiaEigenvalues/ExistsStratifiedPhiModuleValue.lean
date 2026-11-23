import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdIPowLe
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NormLeOneOfMemOL
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.RealisesUnitPow
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemilinearProjectiveModuleComposeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFiniteProjectiveDescentPrismCoverStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StableAndCoverPrismHomOfPushoutStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPrismCoverReceivingBreuilKisinStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrismCoverInjectiveAndDescentStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StratifiedCoordinatesOfPrismCoverStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BSP.EvalEx

theorem semiBC_comp {A B C M N P : Type} [CommRing A] [CommRing B] [CommRing C] [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module B N] [AddCommGroup P] [Module C P] {f : A →+* B} {g : B →+* C} {k : A →+* C}
    (u : M →ₛₗ[f] N) (t : N →ₛₗ[g] P) (w : M →ₛₗ[k] P) (hk : ∀ a, k a = g (f a)) (hw : ∀ x, w x = t (u x))
    (hu : SemiBC u) (ht : SemiBC t) : SemiBC w := by
  intro Q _ _ v
  letI : Module B Q := Module.compHom Q g
  let v' : M →ₛₗ[f] Q :=
    { toFun := v
      map_add' := v.map_add
      map_smul' := fun a x => by
        change v (a • x) = g (f a) • v x
        rw [v.map_smulₛₗ, hk] }
  obtain ⟨z, hz, hzu⟩ := hu Q v'
  let z' : N →ₛₗ[g] Q :=
    { toFun := z
      map_add' := z.map_add
      map_smul' := fun b n => z.map_smul b n }
  obtain ⟨y, hy, hyu⟩ := ht Q z'
  refine ⟨y, fun x => by rw [hw, hy]; exact hz x, fun y' hy' => hyu y' fun n => ?_⟩
  let r : N →ₗ[B] Q :=
    { toFun := fun n => y' (t n)
      map_add' := fun n n' => by simp only [map_add]
      map_smul' := fun b n => by
        change y' (t (b • n)) = g b • y' (t n)
        rw [t.map_smulₛₗ, y'.map_smul] }
  have := hzu r fun x => by
    change y' (t (u x)) = v x
    rw [← hw]; exact hy' x
  exact LinearMap.congr_fun this n

theorem ε_mulVec {l : ℕ} [Fact l.Prime] {K : FinExt l} {bk : BK K} {d : ℕ} (S : Strat bk d) {B : Obj l ↥(OL K)}
    (f g h : Hom bk.prism B) (v : Fin d → B.A) :
    (S.ε f g).mulVec ((S.ε g h).mulVec v) = (S.ε f h).mulVec v := by
  rw [Matrix.mulVec_mulVec, S.ε_trans]

theorem hom_comp_assoc {l : ℕ} {R : Type} [CommRing R] {X Y Z W : Obj l R} (p : Hom Z W) (q : Hom Y Z)
    (r : Hom X Y) : (p.comp q).comp r = p.comp (q.comp r) := Hom.ext' rfl

end GlobalTheory.BSP.EvalEx

namespace GlobalTheory.BSP

theorem exists_eval : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (S : Strat bk d)
    (B : Obj l ↥(OL K)), ∃ (N : Type) (_ : AddCommGroup N) (_ : Module B.A N), Nonempty (Eval S B N) := by
  intro l _ K bk d S B
  obtain ⟨C, h, ⟨f⟩, hc⟩ := GlobalTheory.T.exists_prism_cover_receiving_breuilKisin l K bk B
  obtain ⟨P, _, _, _, _, u, hu, hcoc⟩ := GlobalTheory.T.exists_finiteProjective_descent_prismCover l K bk d S B C h f hc
  have hv := GlobalTheory.T.stratifiedCoordinates_of_prismCover l K bk d S B C h f hc P u hcoc
  choose vv hvv using hv
  have po : ∀ (Q : Obj l ↥(OL K)) (a : Hom B Q), ∃ (Q₀ : Obj l ↥(OL K)) (a₀ : Hom C Q₀) (h₀ : Hom Q Q₀),
      a₀.comp h = h₀.comp a ∧ Cover h₀ ∧ Function.Injective h₀.f := by
    intro Q a
    obtain ⟨Q₀, a₀, h₀, hpo⟩ := hc.stable.po Q a
    have hc₀ := (GlobalTheory.T.stable_and_cover_prismHom_of_pushout l _ B C Q Q₀ h a a₀ h₀ hpo).2 hc
    exact ⟨Q₀, a₀, h₀, hpo.comm, hc₀, (GlobalTheory.T.prism_cover_injective_and_descent l _ Q Q₀ h₀ hc₀).1⟩
  refine ⟨P, inferInstance, inferInstance, ⟨{
    fin := inferInstance
    proj := inferInstance
    v := fun {Q} a g => vv Q a g
    bc := ?_
    v_ε := ?_
    v_nat := ?_ }⟩⟩
  · intro Q a g
    obtain ⟨Q₀, a₀, h₀, hcomm, hc₀, -⟩ := po Q a
    have hf : ∀ y, a₀.f (h.f y) = h₀.f (a.f y) := fun y => congrArg (fun φ : Hom B Q₀ => φ.f y) hcomm
    have hE1 : S.ε (h₀.comp g) (a₀.comp f) * S.ε (a₀.comp f) (h₀.comp g) = 1 := by
      rw [S.ε_trans, S.ε_refl]
    have hE2 : S.ε (a₀.comp f) (h₀.comp g) * S.ε (h₀.comp g) (a₀.comp f) = 1 := by
      rw [S.ε_trans, S.ε_refl]
    let s : (Fin d → Q₀.A) ≃ₗ[Q₀.A] (Fin d → Q₀.A) :=
      { toFun := (S.ε (h₀.comp g) (a₀.comp f)).mulVec
        invFun := (S.ε (a₀.comp f) (h₀.comp g)).mulVec
        map_add' := Matrix.mulVec_add _
        map_smul' := fun c x => Matrix.mulVec_smul _ c x
        left_inv := fun x => by
          change (S.ε (a₀.comp f) (h₀.comp g)).mulVec ((S.ε (h₀.comp g) (a₀.comp f)).mulVec x) = x
          rw [Matrix.mulVec_mulVec, hE2, Matrix.one_mulVec]
        right_inv := fun x => by
          change (S.ε (h₀.comp g) (a₀.comp f)).mulVec ((S.ε (a₀.comp f) (h₀.comp g)).mulVec x) = x
          rw [Matrix.mulVec_mulVec, hE1, Matrix.one_mulVec] }
    let w0 : P →ₛₗ[h₀.f.comp a.f] (Fin d → Q₀.A) :=
      { toFun := fun x j => a₀.f (u x j)
        map_add' := fun x y => by funext j; simp only [map_add, Pi.add_apply]
        map_smul' := fun b x => by
          funext j
          simp only [LinearMap.map_smulₛₗ, Pi.smul_apply, smul_eq_mul, map_mul, RingHom.comp_apply, hf] }
    have hw0 : SemiBC w0 := EvalEx.semiBC_comp u (piMap a₀.f (Fin d)) w0 (fun y => (hf y).symm)
      (fun x => rfl) hu (semiBC_piMap a₀.f _)
    exact GlobalTheory.T.semilinear_projective_module_compose l _ Q Q₀ h₀ hc₀ B.A a.f P (Fin d → Q.A) (Fin d → Q₀.A) (vv Q a g)
      (piMap h₀.f (Fin d)) (s.toLinearMap.comp w0) (fun x => (hvv Q a g Q₀ h₀ a₀ hcomm x).symm)
      (semiBC_piMap h₀.f _) (hw0.comp_equiv s)
  · intro Q a g g' x
    obtain ⟨Q₀, a₀, h₀, hcomm, -, hinj⟩ := po Q a
    funext i
    apply hinj
    have e1 := congrFun (hvv Q a g Q₀ h₀ a₀ hcomm x) i
    have e2 := hvv Q a g' Q₀ h₀ a₀ hcomm x
    rw [e1, RingHom.map_mulVec, S.ε_nat,
      show (⇑h₀.f ∘ (vv Q a g') x) = fun i => h₀.f ((vv Q a g') x i) from rfl, e2]
    exact congrFun (EvalEx.ε_mulVec S (h₀.comp g) (h₀.comp g') (a₀.comp f) _).symm i
  · intro Q Q' c a g x i
    have hp := po Q' (c.comp a)
    obtain ⟨Q₁, a₁, h₁, hcomm, -, hinj⟩ := hp
    apply hinj
    have e1 := congrFun (hvv Q' (c.comp a) (c.comp g) Q₁ h₁ a₁ hcomm x) i
    have e2 := congrFun (hvv Q a g Q₁ (h₁.comp c) a₁ (hcomm.trans (EvalEx.hom_comp_assoc h₁ c a).symm) x) i
    have e3 : (h₁.comp c).f ((vv Q a g) x i) = h₁.f (c.f ((vv Q a g) x i)) := rfl
    refine e1.trans (Eq.trans ?_ (e3 ▸ e2).symm)
    exact congrArg (fun φ => (S.ε φ (a₁.comp f)).mulVec (fun j => a₁.f (u x j)) i)
      (EvalEx.hom_comp_assoc h₁ c g).symm

end GlobalTheory.BSP
