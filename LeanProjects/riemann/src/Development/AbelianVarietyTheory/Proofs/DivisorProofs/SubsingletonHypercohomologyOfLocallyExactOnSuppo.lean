import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSuppSub
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSheafShortComplexExactIffLocallyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HypercohomologyPullbackPushforwardFunctorial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCochainEvEqOfNatural
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCochainEvalOnSimplexBasicPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocalPropertyCalculusRules

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC.SuppAcyc

variable {R : Type} [CommRing R]

theorem map_comp {F G H : Shv R} (φ : F ⟶ G) (ψ : G ⟶ H) {U : Scheme.{0}} (a : Sec F U) :
    Sec.map (φ ≫ ψ) a = Sec.map ψ (Sec.map φ a) := rfl

theorem map_zero' {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} : Sec.map φ (0 : Sec F U) = 0 :=
  map_zero (φ.hom.app (op U)).hom

theorem res_zero' {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) : Sec.res g (0 : Sec F U) = 0 :=
  map_zero (F.obj.map g.op).hom

theorem cpush_zero (K I J : Cx R) (n : ℤ) (x : CohomologyClass K I n) : cpush K (0 : I ⟶ J) n x = 0 := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  rw [cpush, cpost_mk]
  have : zcomp x (Cocycle.ofHom (0 : I ⟶ J)) (add_zero n) = 0 := Cocycle.ext (by simp [zcomp])
  rw [this]
  exact CohomologyClass.mk_zero _ _ _

theorem delta_comp_ofHom {K I J : Cx R} {n : ℤ} (a : Cochain K I n) (f : I ⟶ J) :
    δ n (n + 1) (a.comp (Cochain.ofHom f) (add_zero n)) = (δ n (n + 1) a).comp (Cochain.ofHom f) (add_zero _) := by
  rw [δ_comp _ _ (add_zero n) (n + 1) 1 (n + 1) rfl rfl (zero_add 1)]
  simp

end GlobalTheory.EtC.SuppAcyc

open GlobalTheory.EtC.SuppAcyc in

theorem GlobalTheory.EtC.subsingleton_of_locExact_supp : ∀ (R : Type) [CommRing R] (E : Spc) (C : Cx R) [C.IsKInjective], (∀ (U : Scheme.{0}), Nonempty (Sx E 0 U) → ∀ (n : ℤ) (b : Sec (C.X n) U), Sec.map (C.d n (n + 1)) b = 0 → Loc U fun V g => ∃ a : Sec (C.X (n - 1)) V, Sec.map (C.d (n - 1) n) a = Sec.res g b) → ∀ n, Subsingleton (CohomologyClass ((chains R).obj E) C n) := by
  intro R _ E C _ hC n
  let Z : Scheme.{0} → Prop := fun U => Nonempty (Sx E 0 U)
  have hZ : ∀ (V U : Scheme.{0}) (_ : V ⟶ U), Z U → Z V := fun V U g ⟨x⟩ => ⟨Sx.res g x⟩
  obtain ⟨D, ι, hinj, hchar⟩ := SuppSub.exists_supp_sub R C Z hZ
  obtain ⟨ltop, lmono, -, -, ltrans, -, -⟩ := GlobalTheory.EtC.loc_calculus
  have hin : ∀ k U (a : Sec (C.X k) U), Z U → ∃ b, Sec.map (ι.f k) b = a := fun k U a hU =>
    (hchar k U a).2 (ltop _ _ fun V g => Or.inl (hZ V U g hU))

  have hD : D.Acyclic := by
    intro k
    rw [HomologicalComplex.exactAt_iff' D (k - 1) k (k + 1) (by simp) (by simp), GlobalTheory.T.etaleSheaf_shortComplex_exact_iff_locally]
    intro U (b : Sec (D.X k) U) hb
    change Sec.map (D.d k (k + 1)) b = 0 at hb
    have hc : Sec.map (C.d k (k + 1)) (Sec.map (ι.f k) b) = 0 := by
      rw [← map_comp, ι.comm, map_comp, hb, map_zero']
    have hloc := (hchar k U (Sec.map (ι.f k) b)).1 ⟨b, rfl⟩
    refine ltrans _ _ (lmono _ _ _ hloc fun V g hg => ?_)
    rcases hg with hV | h0
    · have hc' : Sec.map (C.d k (k + 1)) (Sec.res g (Sec.map (ι.f k) b)) = 0 := by
        have := congrArg (Sec.res g) hc
        rwa [SuppSub.res_map, res_zero'] at this
      refine lmono _ _ _ (hC V hV k _ hc') fun W h => ?_
      rintro ⟨a, ha⟩
      obtain ⟨a', rfl⟩ := hin (k - 1) W a (hZ W V h hV)
      refine ⟨a', hinj k W ?_⟩
      change Sec.map (ι.f k) (Sec.map (D.d (k - 1) k) a') = Sec.map (ι.f k) (Sec.res (h ≫ g) b)
      rw [← map_comp, ← ι.comm, map_comp, ha, SuppSub.res_comp, SuppSub.res_map, SuppSub.res_map]
    · have h0' : Sec.res g b = 0 := hinj k V (by rw [← SuppSub.res_map, h0, map_zero'])
      refine ltop _ _ fun W h => ⟨0, ?_⟩
      change Sec.map (D.d (k - 1) k) 0 = Sec.res (h ≫ g) b
      rw [map_zero', SuppSub.res_comp, h0', res_zero']
  have hnull : Nonempty (Homotopy ι 0) := IsKInjective.nonempty_homotopy_zero ι hD
  have hpush : cpush ((chains R).obj E) ι n = cpush _ (0 : D ⟶ C) n :=
    ((GlobalTheory.EtC.ZcFun.main R).2.2.2.2 ι 0 hnull ((chains R).obj E) n).2
  obtain ⟨-, hnat, hdet, -, -⟩ := GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R (E := E) (I := C) (n := n)
  obtain ⟨-, -, -, -, hpost⟩ := GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R (E := E) (I := D) (n := n)
  obtain ⟨haddD1, -, hdetD, -, hpost1⟩ := GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R (E := E) (I := D) (n := n + 1)
  obtain ⟨haddC1, -, -, -, -⟩ := GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R (E := E) (I := C) (n := n + 1)
  have hzero : ∀ c : CohomologyClass ((chains R).obj E) C n, c = 0 := by
    intro c
    obtain ⟨α, rfl⟩ := c.mk_surjective

    have hv : ∀ (p : ℕ) (U : Scheme.{0}), Sx E p U → Z U := fun p U x =>
      ⟨Sx.along x (SimplexCategory.const (SimplexCategory.mk 0) (SimplexCategory.mk p) 0)⟩
    let v : ∀ (p : ℕ) (s : ℤ), -(p : ℤ) + n = s → ∀ U : Scheme.{0}, Sx E p U → Sec (D.X s) U :=
      fun p s h U x => Classical.choose (hin s U (ev α.1 p s h U x) (hv p U x))
    have hvspec : ∀ p s h U x, Sec.map (ι.f s) (v p s h U x) = ev α.1 p s h U x :=
      fun p s h U x => Classical.choose_spec (hin s U (ev α.1 p s h U x) (hv p U x))
    have hvnat : ∀ p s h (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U), Sec.res g (v p s h U x) = v p s h V (x.res g) := by
      intro p s h V U g x
      apply hinj s V
      rw [← SuppSub.res_map, hvspec, hvspec, (hnat α.1 p s h V U g x)]
    obtain ⟨α', hα'⟩ := GlobalTheory.EtC.exists_cochain_ev_eq_of_natural R v hvnat
    have hcomp : α'.comp (Cochain.ofHom ι) (add_zero n) = α.1 := by
      apply hdet
      intro p s h U x
      rw [hpost, hα', hvspec]
    have hcoc : δ n (n + 1) α' = 0 := by
      apply hdetD
      intro p s h U x
      apply hinj s U
      rw [← hpost1, ← delta_comp_ofHom, hcomp, (Cocycle.mem_iff n (n + 1) rfl α.1).1 α.2, (haddC1 0 0 p s h U x).2.2.1,
        (haddD1 0 0 p s h U x).2.2.1, map_zero']
    let β : Cocycle ((chains R).obj E) D n := Cocycle.mk α' (n + 1) rfl hcoc
    have hαβ : α = zcomp β (Cocycle.ofHom ι) (add_zero n) := Cocycle.ext hcomp.symm
    rw [hαβ, ← cpost_mk, ← cpush, hpush, cpush_zero]
  exact ⟨fun a b => (hzero a).trans (hzero b).symm⟩
