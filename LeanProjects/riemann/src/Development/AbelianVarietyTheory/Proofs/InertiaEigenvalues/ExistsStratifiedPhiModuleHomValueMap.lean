import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdIPowLe
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPrismCoverReceivingBreuilKisinStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InjectiveAndRangeOfPrismCoverStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsInjectivePushoutOfPrismCoverStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem stratHom_map_mulVec {m n : Type} [Fintype n] {A A' : Type} [CommRing A] [CommRing A'] (φ : A →+* A')
    (M : Matrix m n A) (v : n → A) : (fun i => φ ((M.mulVec v) i)) = (M.map φ).mulVec (fun i => φ (v i)) := by
  funext i
  exact RingHom.map_mulVec φ M v i

theorem stratHom_coord_nat {l : ℕ} [Fact l.Prime] {K : FinExt l} {bk : BK K} {d d' : ℕ} {S : Strat bk d}
    (Y : Matrix (Fin d') (Fin d) bk.S) {B : Obj l ↥(OL K)} {N : Type} [AddCommGroup N] [Module B.A N]
    (V : Eval S B N) {Q Q' : Obj l ↥(OL K)} (r : Hom Q Q') (a : Hom B Q) (g : Hom bk.prism Q) (x : N) :
    (fun i => r.f (((Y.map (BK.hf g)).mulVec (V.v a g x)) i)) =
      (Y.map (BK.hf (r.comp g))).mulVec (V.v (r.comp a) (r.comp g) x) := by
  rw [stratHom_map_mulVec]
  have e1 : (Y.map (BK.hf g)).map r.f = Y.map (BK.hf (r.comp g)) := by
    rw [Matrix.map_map]; rfl
  have e2 : (fun i => r.f (V.v a g x i)) = V.v (r.comp a) (r.comp g) x := by
    funext i; exact (V.v_nat r a g x i).symm
  rw [e1, e2]

theorem stratHom_coord_ε {l : ℕ} [Fact l.Prime] {K : FinExt l} {bk : BK K} {d d' : ℕ} {S : Strat bk d}
    {S' : Strat bk d'} {Y : Matrix (Fin d') (Fin d) bk.S} (hY : IsStratHom S S' Y) {B : Obj l ↥(OL K)} {N : Type}
    [AddCommGroup N] [Module B.A N] (V : Eval S B N) {Q : Obj l ↥(OL K)} (a : Hom B Q) (g g' : Hom bk.prism Q)
    (x : N) :
    (Y.map (BK.hf g)).mulVec (V.v a g x) = (S'.ε g g').mulVec ((Y.map (BK.hf g')).mulVec (V.v a g' x)) := by
  rw [V.v_ε a g g' x, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hY.ε]

theorem evalHom : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d d' : ℕ) (S : Strat bk d) (S' : Strat bk d')
    (Y : Matrix (Fin d') (Fin d) bk.S), IsStratHom S S' Y → ∀ (B : Obj l ↥(OL K)) (N : Type) [AddCommGroup N]
    [Module B.A N] (N' : Type) [AddCommGroup N'] [Module B.A N'] (V : Eval S B N) (V' : Eval S' B N'),
    ∃ w : N →ₗ[B.A] N', ∀ (Q : Obj l ↥(OL K)) (a : Hom B Q) (g : Hom bk.prism Q) (x : N),
      V'.v a g (w x) = (Y.map (BK.hf g)).mulVec (V.v a g x) := by
  intro l _ K bk d d' S S' Y hY B N _ _ N' _ _ V V'
  obtain ⟨C, h, ⟨f⟩, hc⟩ := GlobalTheory.T.exists_prism_cover_receiving_breuilKisin l K bk B
  obtain ⟨inj, ev⟩ := GlobalTheory.T.injective_and_range_of_prism_cover l K bk d' S' B C N' V' h f hc
  have hz : ∀ x, ∀ (Q : Obj l ↥(OL K)) (p q : Hom C Q), p.comp h = q.comp h →
      (fun i => p.f (((Y.map (BK.hf f)).mulVec (V.v h f x)) i)) = (S'.ε (p.comp f) (q.comp f)).mulVec
        fun i => q.f (((Y.map (BK.hf f)).mulVec (V.v h f x)) i) := by
    intro x Q p q hpq
    have e : V.v (p.comp h) (p.comp f) x = V.v (q.comp h) (p.comp f) x := by rw [hpq]
    refine (stratHom_coord_nat Y V p h f x).trans ?_
    refine Eq.trans ?_ (congrArg (S'.ε (p.comp f) (q.comp f)).mulVec (stratHom_coord_nat Y V q h f x)).symm
    rw [e]
    exact stratHom_coord_ε hY V (q.comp h) (p.comp f) (q.comp f) x
  choose w0 hw0 using fun x => ev _ (hz x)
  let w : N →ₗ[B.A] N' :=
    { toFun := w0
      map_add' := fun x y => by
        apply inj
        show V'.v h f (w0 (x + y)) = V'.v h f (w0 x + w0 y)
        refine (hw0 (x + y)).trans ?_
        refine Eq.trans ?_ ((V'.v h f).map_add (w0 x) (w0 y)).symm
        refine Eq.trans ?_ (congrArg₂ (· + ·) (hw0 x) (hw0 y)).symm
        exact (congrArg (Y.map (BK.hf f)).mulVec ((V.v h f).map_add x y)).trans (Matrix.mulVec_add _ _ _)
      map_smul' := fun c x => by
        apply inj
        show V'.v h f (w0 (c • x)) = V'.v h f (c • w0 x)
        refine (hw0 (c • x)).trans ?_
        refine Eq.trans ?_ ((V'.v h f).map_smulₛₗ c (w0 x)).symm
        refine Eq.trans ?_ (congrArg (h.f c • ·) (hw0 x)).symm
        exact (congrArg (Y.map (BK.hf f)).mulVec ((V.v h f).map_smulₛₗ c x)).trans (Matrix.mulVec_smul _ _ _) }
  refine ⟨w, fun Q a g x => ?_⟩
  obtain ⟨Q', h', a', hcomm, hinj⟩ := GlobalTheory.T.exists_injective_pushout_of_prismCover l K bk d S B C h hc Q a
  have hw : w x = w0 x := rfl
  funext i
  apply hinj
  have lhs : (fun j => h'.f (V'.v a g (w0 x) j)) = V'.v (a'.comp h) (h'.comp g) (w0 x) := by
    exact (funext fun j => (V'.v_nat h' a g (w0 x) j).symm).trans
      (congrArg (fun t => V'.v t (h'.comp g) (w0 x)) hcomm.symm)
  have rhs : (fun j => h'.f (((Y.map (BK.hf g)).mulVec (V.v a g x)) j)) =
      (Y.map (BK.hf (h'.comp g))).mulVec (V.v (a'.comp h) (h'.comp g) x) := by
    exact (stratHom_coord_nat Y V h' a g x).trans
      (congrArg (fun t => (Y.map (BK.hf (h'.comp g))).mulVec (V.v t (h'.comp g) x)) hcomm.symm)
  have mid : V'.v (a'.comp h) (a'.comp f) (w0 x) = (Y.map (BK.hf (a'.comp f))).mulVec (V.v (a'.comp h) (a'.comp f) x) := by
    exact (funext fun j => V'.v_nat a' h f (w0 x) j).trans
      ((congrArg (fun v : Fin d' → C.A => fun j => a'.f (v j)) (hw0 x)).trans (stratHom_coord_nat Y V a' h f x))
  have := congrFun (lhs.trans ((V'.v_ε (a'.comp h) (h'.comp g) (a'.comp f) (w0 x)).trans
    ((congrArg (S'.ε (h'.comp g) (a'.comp f)).mulVec mid).trans
      ((stratHom_coord_ε hY V (a'.comp h) (h'.comp g) (a'.comp f) x).symm.trans rhs.symm)))) i
  rw [hw]
  exact this

end GlobalTheory.BSP
