import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExpandsPullOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdBox
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsGeneratorOfBasis
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsBoxSecPowExt
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.SmoothOfRelativeDimensionPowObj
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.BoxProductLinearIndependent

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory

namespace BoxSpan

theorem span_eq_top_of_card {C M : Type} [CommRing C] (hC : IsField C) [AddCommGroup M] [Module C M]
    {I I' : Type} [Fintype I] [Fintype I'] (b : I → M) (hli : LinearIndependent C b)
    (hsp : Submodule.span C (Set.range b) = ⊤) (v : I' → M) (hv : LinearIndependent C v)
    (hc : Fintype.card I' = Fintype.card I) : Submodule.span C (Set.range v) = ⊤ := by
  let _ : Field C := hC.toField
  have hb : Module.finrank C M = Fintype.card I :=
    Module.finrank_eq_card_basis (Module.Basis.mk hli hsp.ge)
  have _ : Module.Finite C M := Module.Finite.of_basis (Module.Basis.mk hli hsp.ge)
  exact hv.span_eq_top_of_card_eq_finrank' (hc.trans hb.symm)

theorem exists_basis (hS : SecBaseChangeSt) {K : Type} [Field K] (P : PolAV (Spec (CommRingCat.of K))) (n : ℕ)
    (hn : 1 ≤ n) (F : Type) [CommRing F] (q : Spec (CommRingCat.of F) ⟶ Spec (CommRingCat.of K)) :
    ∃ b : Fin (n ^ P.g) → SecM P.A P.L n (Over.mk q), LinearIndependent Γ((Over.mk q).left, ⊤) b ∧
      Submodule.span Γ((Over.mk q).left, ⊤) (Set.range b) = ⊤ := by
  obtain ⟨V, hpV, b, hb⟩ := hS (Spec (CommRingCat.of K)) P n hn default
  have hbo : (baseOver (Spec (CommRingCat.of K))).hom = 𝟙 _ := rfl
  have hr : Set.range q ⊆ Set.range V.ι := by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι]
    have : q x = default := Subsingleton.elim _ _
    rw [this]
    exact hpV
  obtain ⟨t, rfl⟩ : ∃ t : Spec (CommRingCat.of F) ⟶ V.toScheme, t ≫ V.ι ≫ (baseOver (Spec (CommRingCat.of K))).hom = q := by
    refine ⟨IsOpenImmersion.lift V.ι q hr, ?_⟩
    rw [hbo]
    erw [Category.comp_id]
    exact IsOpenImmersion.lift_fac _ _ _
  unfold LPow at b
  choose b' hb' using fun i => GlobalTheory.IndivisibleSection.exists_pull_chart (b i) (homAt (V := V) t ▷ P.A).left
    (fun _ => (snd (baseAt (V := V) t) P.A).left) (fun _ => by rw [← Over.comp_left, whiskerRight_snd])
  obtain ⟨hli, hsp⟩ := hb F t b' (fun i j => hb' i j _)
  exact ⟨fun i => SecM.ofSec P.A (b' i), hli, hsp⟩

theorem comb_apply {S : Scheme.{0}} (A : Over S) [GrpObj A] (L : LB A.left) (a : ℤ) (T : Over S) {I : Type}
    [Fintype I] (c : I → Γ(T.left, ⊤)) (v : I → SecM A L a T) (jj) :
    (∑ l, c l • v l).1 jj = ∑ l, liftFun A _ (c l) * (v l).1 jj := by
  rw [Submodule.coe_sum, Finset.sum_apply]
  exact Finset.sum_congr rfl fun l _ => rfl

private theorem ΓSpecIso_inv_hom_apply (F : Type) [CommRing F] (x : Γ(Spec (CommRingCat.of F), ⊤)) :
    (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom x) = x := by
  rw [← CommRingCat.comp_apply, Iso.hom_inv_id, CommRingCat.id_apply]

end BoxSpan

open BoxSpan in

theorem boxProduct_span : Laws → ∀ (R : Type) [CommRing R] [IsDomain R] (j : ℕ) (A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))) (pA : IsPowPolAV A' A j) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ), 1 ≤ k → ∀ s : LB.Sec (LB.LinComb A'.L (K := Fin 1) (fun _ => (snd (TFK (R := R) F) A'.A).left) (fun _ => (k : ℤ))), ∃ (n : ℕ) (c : Fin n → F) (t : Fin n → Fin j → LB.Sec (LB.LinComb A.L (K := Fin 1) (fun _ => (snd (TFK (R := R) F) A.A).left) (fun _ => (k : ℤ)))) (t' : Fin n → LB.Sec (LB.LinComb A'.L (K := Fin 1) (fun _ => (snd (TFK (R := R) F) A'.A).left) (fun _ => (k : ℤ)))), (∀ l, (∀ (Z : Scheme.{0}) (r : Z ⟶ ((TFK (R := R) F) ⊗ A'.A).left) (z : Z) (J J'), Geo.Tor.Good A.L z J → Geo.Tor.Good A'.L z J' → (bw pA.w (r ≫ (snd (TFK (R := R) F) A'.A).left) z (fun i => J ((r ≫ (snd (TFK (R := R) F) A'.A).left) ≫ (pA.pr i).left)) (J' (r ≫ (snd (TFK (R := R) F) A'.A).left)) ^ k).val * Geo.Tor.sval (t' l) r z J' = ∏ i, Geo.Tor.sval (t l i) (r ≫ ((TFK (R := R) F) ◁ pA.pr i).left) z J)) ∧ ∀ jj, s.f jj = ∑ l, liftFun A'.A _ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (c l)) * (t' l).f jj := by
  intro hL R _ _ j A A' pA F _ _ k hk s
  obtain ⟨b, hbi, -⟩ := exists_basis hL.secBaseChange A k hk F (TFK (R := R) F).hom
  obtain ⟨b', hbi', hbs'⟩ := exists_basis hL.secBaseChange A' k hk F (TFK (R := R) F).hom
  let σ : Fin (k ^ A.g) → LB.Sec (LB.LinComb A.L (K := Fin 1) (fun _ => (snd (TFK (R := R) F) A.A).left)
      (fun _ => (k : ℤ))) := fun l => ⟨(b l).1, fun i i' => (b l).2 i i'⟩
  have hb : ∀ c : Fin (k ^ A.g) → F, (∀ jj, ∑ l, liftFun A.A _
      ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (c l)) * (σ l).f jj = 0) → c = 0 := by
    intro c hc
    have h0 := Fintype.linearIndependent_iff.mp hbi
      (fun l => (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (c l)) (by
        apply Subtype.ext
        funext jj
        exact (comb_apply A.A A.L (k : ℤ) (Over.mk (TFK (R := R) F).hom) _ b jj).trans (hc jj))
    funext l
    have h1 := congrArg (Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom (h0 l)
    rw [← CommRingCat.comp_apply, Iso.inv_hom_id, CommRingCat.id_apply, map_zero] at h1
    exact h1
  choose t' ht' using fun a : Fin j → Fin (k ^ A.g) =>
    exists_boxSec_pow_ext R j A A' pA F k (fun i => σ (a i))
  have hind := boxProduct_linearIndependent R j A A' pA F k (k ^ A.g) σ hb t' ht'
  have hli : LinearIndependent Γ((Over.mk (TFK (R := R) F).hom).left, ⊤)
      (fun a => (SecM.ofSec A'.A (t' a) : SecM A'.A A'.L (k : ℤ) (Over.mk (TFK (R := R) F).hom))) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg a
    have hc := hind (fun a => (Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom (g a)) (by
      intro jj
      have h1 := congrArg (fun x : SecM A'.A A'.L (k : ℤ) (Over.mk (TFK (R := R) F).hom) => x.1 jj) hg
      have h2 := (comb_apply A'.A A'.L (k : ℤ) (Over.mk (TFK (R := R) F).hom) g
        (fun a => SecM.ofSec A'.A (t' a)) jj).symm.trans h1
      refine Eq.trans (Finset.sum_congr rfl fun a _ => ?_) h2
      exact congrArg (fun x => liftFun (T := TFK (R := R) F) A'.A _ x * (t' a).f jj) (ΓSpecIso_inv_hom_apply F (g a)))
    have h2 := congrFun hc a
    rw [Pi.zero_apply] at h2
    rw [← ΓSpecIso_inv_hom_apply F (g a), h2, map_zero]
  have hfield : IsField Γ((Over.mk (TFK (R := R) F).hom).left, ⊤) :=
    MulEquiv.isField (Field.toIsField F)
      (Scheme.ΓSpecIso (CommRingCat.of F)).commRingCatIsoToRingEquiv.toMulEquiv
  have hcard : Fintype.card (Fin j → Fin (k ^ A.g)) = Fintype.card (Fin (k ^ A'.g)) := by
    rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, polAV_g_of_isPowPolAV _ j A A' pA, ← pow_mul,
      mul_comm]
    exact (Fintype.card_fin _).symm
  have hspan := span_eq_top_of_card hfield b' hbi' hbs' _ hli hcard
  have hmem : (SecM.ofSec A'.A s : SecM A'.A A'.L (k : ℤ) (Over.mk (TFK (R := R) F).hom)) ∈
      Submodule.span Γ((Over.mk (TFK (R := R) F).hom).left, ⊤)
        (Set.range fun a => (SecM.ofSec A'.A (t' a) : SecM A'.A A'.L (k : ℤ) (Over.mk (TFK (R := R) F).hom))) := by
    rw [hspan]
    exact Submodule.mem_top
  obtain ⟨g, hg⟩ := Submodule.mem_span_range_iff_exists_fun _ |>.mp hmem
  let e := Fintype.equivFin (Fin j → Fin (k ^ A.g))
  refine ⟨Fintype.card (Fin j → Fin (k ^ A.g)), fun l => (Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom (g (e.symm l)),
    fun l i => σ (e.symm l i), fun l => t' (e.symm l), fun l => ht' (e.symm l), ?_⟩
  intro jj
  have h1 := congrArg (fun x : SecM A'.A A'.L (k : ℤ) (Over.mk (TFK (R := R) F).hom) => x.1 jj) hg
  have h2 := (comb_apply A'.A A'.L (k : ℤ) (Over.mk (TFK (R := R) F).hom) g
    (fun a => SecM.ofSec A'.A (t' a)) jj).symm.trans h1
  refine h2.symm.trans ?_
  rw [← e.symm.sum_comp]
  refine Finset.sum_congr rfl fun l _ => ?_
  congr 1
  congr 1
  exact (ΓSpecIso_inv_hom_apply F _).symm

end GlobalTheory
