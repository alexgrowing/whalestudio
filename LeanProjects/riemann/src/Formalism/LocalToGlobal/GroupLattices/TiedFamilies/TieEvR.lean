import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.EvenBlockRowActionEval
import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.NatActRVtupR

open MvPolynomial Matrix Formalism.GradedWeylDivisibility Formalism.MainNotions.G Formalism.BasicNotions Formalism.L2.Forms

noncomputable section

namespace Formalism.L2.G

open Formalism.L2.G.Cmp

section Gen

variable {p : ℕ} {O Kf : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  (P : Places p O Kf) {Tau : Type} [Fintype Tau] {n : ℕ} {LL : Type} [Field LL]

def blkMod (R : Type) [Field R] (v : Fin P.nV) (s : Fin (P.n' v)) :
    Submodule R (MvPolynomial (Fin (P.m + 1) × Fin (P.m + 1)) R) :=
  if Antitone (lamAt (P.lam0 v) s) then dualWeyl R (P.m + 1) (P.m + 1) (nuOf (lamAt (P.lam0 v) s)) else ⊥

def BlockRational (h : P.m + 1 = n) (pos : (Σ v : Fin P.nV, Fin (P.n' v)) ≃ Tau) (G M : Tau → Matrix (Fin n) (Fin n) ℂ)
    (embLL : LL →+* ℂ) (lam : Tau → DomWeight n) : Prop :=
  ∀ v (s : Fin (P.n' v)) (f : MvPolynomial (Fin n × Fin n) ℤ), f ∈ delSq ℤ n (lam (pos ⟨v, s⟩)) →
    ∃ F ∈ blkMod P LL v s, ∀ y : Frames G,
      (zAt P h pos M y.1 v s).det ^ (eAt P v s) *
          eval (fun x => zAt P h pos M y.1 v s x.1 x.2) (MvPolynomial.map embLL F) =
        (y.1 (pos ⟨v, s⟩)).det ^ (lam (pos ⟨v, s⟩)).detShift *
          eval (fun x => y.1 (pos ⟨v, s⟩) x.1 x.2) (MvPolynomial.map (Int.castRingHom ℂ) f)

variable {P}

theorem evRat_gen {h : P.m + 1 = n} {pos : (Σ v : Fin P.nV, Fin (P.n' v)) ≃ Tau} {G M : Tau → Matrix (Fin n) (Fin n) ℂ}
    {embLL : LL →+* ℂ} {lam : Tau → DomWeight n} (hb : BlockRational P h pos G M embLL lam) (r : LL)
    (f : Tau → MvPolynomial (Fin n × Fin n) ℤ) (hf : ∀ τ, f τ ∈ delSq ℤ n (lam τ)) :
    ∃ Q ∈ VtupR P LL, ∀ z : Frames G, evC P h pos G M (MvPolynomial.map embLL Q) z =
      fnOf G (shiftOf lam) 1 (embLL r • ten (fun τ => MvPolynomial.map (Int.castRingHom ℂ) (f τ))) z := by
  choose F hF hev using fun v s => hb v s (f (pos ⟨v, s⟩)) (hf _)
  refine ⟨r • ∏ v, rename (fun x => (⟨v, x⟩ : Var P)) (∏ s, blockEmb LL s (F v s)),
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨fun v => ∏ s, blockEmb LL s (F v s),
      fun v => Submodule.subset_span ⟨F v, hF v, rfl⟩, rfl⟩), fun z => ?_⟩
  have hmap : MvPolynomial.map embLL (r • ∏ v, rename (fun x => (⟨v, x⟩ : Var P)) (∏ s, blockEmb LL s (F v s))) =
      embLL r • ∏ v, rename (fun x => (⟨v, x⟩ : Var P)) (∏ s, blockEmb ℂ s (MvPolynomial.map embLL (F v s))) := by
    rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, ← MvPolynomial.smul_eq_C_mul, map_prod]
    congr 1
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [MvPolynomial.map_rename, map_prod]
    congr 1
    refine Finset.prod_congr rfl fun s _ => ?_
    exact MvPolynomial.map_rename _ _ _
  rw [hmap, map_smul, map_smul, Pi.smul_apply, Pi.smul_apply, evC_prod]
  congr 1
  have h1 : (∏ v, ∏ s : Fin (P.n' v), ((zAt P h pos M z.1 v s).det ^ (eAt P v s) *
      eval (fun x => zAt P h pos M z.1 v s x.1 x.2) (MvPolynomial.map embLL (F v s)))) =
      ∏ τ, ((z.1 τ).det ^ (lam τ).detShift *
        eval (fun x => z.1 τ x.1 x.2) (MvPolynomial.map (Int.castRingHom ℂ) (f τ))) := by
    rw [← pos.prod_comp, Fintype.prod_sigma]
    exact Finset.prod_congr rfl fun v _ => Finset.prod_congr rfl fun s _ => hev v s z
  rw [h1, Finset.prod_mul_distrib]
  show _ = (∏ τ, ((1 : Tau → Matrix (Fin n) (Fin n) ℂ) τ * z.1 τ).det ^ shiftOf lam τ) *
    eval (fun x : Tau × Fin n × Fin n => ((1 : Tau → Matrix (Fin n) (Fin n) ℂ) x.1 * z.1 x.1) x.2.1 x.2.2)
      (ten (fun τ => MvPolynomial.map (Int.castRingHom ℂ) (f τ)))
  simp only [Pi.one_apply, Matrix.one_mul, ten, map_prod, eval_rename, Function.comp_def, shiftOf]

theorem evRat_of_blocks {h : P.m + 1 = n} {pos : (Σ v : Fin P.nV, Fin (P.n' v)) ≃ Tau}
    {G M : Tau → Matrix (Fin n) (Fin n) ℂ} {embLL : LL →+* ℂ} {lam : Tau → DomWeight n}
    (hb : BlockRational P h pos G M embLL lam) (Pp : MvPolynomial (Tau × Fin n × Fin n) ℂ)
    (hP : Pp ∈ AddSubgroup.closure {q | ∃ (r : LL) (f : Tau → MvPolynomial (Fin n × Fin n) ℤ),
      (∀ τ, f τ ∈ delSq ℤ n (lam τ)) ∧
      q = embLL r • ten (fun τ => MvPolynomial.map (Int.castRingHom ℂ) (f τ))}) :
    ∃ Q ∈ VtupR P LL, ∀ z : Frames G, evC P h pos G M (MvPolynomial.map embLL Q) z = fnOf G (shiftOf lam) 1 Pp z := by
  induction hP using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨r, f, hf, rfl⟩ := hx
    exact evRat_gen hb r f hf
  | zero => exact ⟨0, Submodule.zero_mem _, fun z => by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨Q, hQ, e⟩ := hx
    obtain ⟨Q', hQ', e'⟩ := hy
    exact ⟨Q + Q', Submodule.add_mem _ hQ hQ', fun z => by
      rw [map_add, map_add, map_add, Pi.add_apply, Pi.add_apply, e z, e' z]⟩
  | neg x _ hx =>
    obtain ⟨Q, hQ, e⟩ := hx
    exact ⟨-Q, Submodule.neg_mem _ hQ, fun z => by
      rw [map_neg, map_neg, map_neg, Pi.neg_apply, Pi.neg_apply, e z]⟩

end Gen

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : Formalism.L2.Herm.Herm0 D}

def BlockRationalityAtPlace (X : Formalism.L2.Herm.Herm0 D) (Gt : GatTies D) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (B : GL (Fin D.R.k) D.host.E) : Prop :=
  BlockRational (D.gat u w hg).P (locAt X u w hg B).rk (Gt.gat_pos u w hg) (gramC (gramN D 0 (Nat.zero_le _)) (embT D))
    (crdB (embT D) (locAt X u w hg B).B) D.what₂.embLL ((D.fm u).lam 0)

set_option maxHeartbeats 4000000 in

theorem evRatRep_rec (T : ∀ u : D.what₂.Word, Forms0 D u) (Gt : GatTies D) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (B : GL (Fin D.R.k) D.host.E)
    (hb : BlockRationalityAtPlace X Gt u w hg B) :
    EvRatRep (embT D) D.what₂.embLL (D.gat u w hg) (locAt X u w hg B) (Gt.gat_pos u w hg) (embFr T u) := by
  intro x c
  obtain ⟨Pp, hPp, e⟩ := ((((T u).val0).rat _).1 ⟨x, rfl⟩).2 c
  obtain ⟨Q, hQ, hev⟩ := evRat_of_blocks hb Pp hPp
  refine ⟨Q, hQ, fun z => ?_⟩
  rw [hev z]
  show _ = (D.fm u).emb 0 x c (((T u).val0).eY.symm z)
  rw [e, Equiv.apply_symm_apply, lamT_zero]

end Formalism.L2.G
