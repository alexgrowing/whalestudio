import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEtaleCocycleFirstChernClassTateTwist
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChosenInjectiveResolutionEtaleSheafSectionsExactStatement

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC
namespace KumNat
open ClsSpec

theorem sec_subsingleton {R : Type} [CommRing R] (F : Shv R) (U : Scheme.{0}) {s : ℤ} (hs : s < 0) :
    Subsingleton (Sec ((res R F).X s) U) := (GlobalTheory.T.chosenInjectiveResolutionEtaleSheaf_sections_exactness R F U).2.2.2 s hs

theorem ev_sub' {R : Type} [CommRing R] {E : Spc} {I : Cx R} {n : ℤ} (α β : Cochain ((chains R).obj E) I n) (p s h U x) :
    ev (α - β) p s h U x = ev α p s h U x - ev β p s h U x := ((GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R).1 α β p s h U x).2.1

variable {q : ℕ}

theorem kum_unique [NeZero q] {X : Scheme.{0}} (hX : IsUnit (q : Γ(X, ⊤))) (u : (Γ(X, ⊤))ˣ)
    {γ γ' : Cochain ((chains (ZMod q)).obj (sch.obj X)) (res _ (tw q 1)) 1}
    (h₁ : ∀ (U : Scheme.{0}) (x : U ⟶ X), ev γ 1 0 (by simp) U x = 0)
    (h₂ : ∀ (U : Scheme.{0}) (x : U ⟶ X) (v : (Γ(U, ⊤))ˣ), v ^ q = umap x u →
      ev γ 0 1 (by simp) U x = Sec.map ((res _ (tw q 1)).d 0 1) (kumT q U v))
    (h₁' : ∀ (U : Scheme.{0}) (x : U ⟶ X), ev γ' 1 0 (by simp) U x = 0)
    (h₂' : ∀ (U : Scheme.{0}) (x : U ⟶ X) (v : (Γ(U, ⊤))ˣ), v ^ q = umap x u →
      ev γ' 0 1 (by simp) U x = Sec.map ((res _ (tw q 1)).d 0 1) (kumT q U v)) : γ = γ' := by
  refine (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.2.1 _ _ fun p s h U x => ?_
  match p with
  | 0 =>
    obtain rfl : s = 1 := by omega
    change U ⟶ X at x
    refine sep (ClsSpec.loc_mono (root_loc (unit_res x hX) (umap x u)) fun V g ⟨v, hv⟩ => ?_)
    rw [(GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.1 γ 0 1 _ V U g x, (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.1 γ' 0 1 _ V U g x]
    have hv' : v ^ q = umap (g ≫ x) u := by rw [hv, umap_comp]
    exact (h₂ V (g ≫ x) v hv').trans (h₂' V (g ≫ x) v hv').symm
  | 1 =>
    obtain rfl : s = 0 := by omega
    exact (h₁ U x).trans (h₁' U x).symm
  | p + 2 =>
    haveI := sec_subsingleton (tw q 1) U (s := s) (by omega)
    exact Subsingleton.elim _ _

theorem eq_zero_of_kumT [NeZero q] (ht : kumT q = 0) {X : Scheme.{0}} (hX : IsUnit (q : Γ(X, ⊤))) (u : (Γ(X, ⊤))ˣ)
    {γ : Cochain ((chains (ZMod q)).obj (sch.obj X)) (res _ (tw q 1)) 1}
    (h₁ : ∀ (U : Scheme.{0}) (x : U ⟶ X), ev γ 1 0 (by simp) U x = 0)
    (h₂ : ∀ (U : Scheme.{0}) (x : U ⟶ X) (v : (Γ(U, ⊤))ˣ), v ^ q = umap x u →
      ev γ 0 1 (by simp) U x = Sec.map ((res _ (tw q 1)).d 0 1) (kumT q U v)) : γ = 0 :=
  kum_unique hX u h₁ h₂ (fun U x => ev_zero (E := sch.obj X) _ _ _ _ _)
    (fun U x v _ => (ev_zero (E := sch.obj X) _ _ _ _ _).trans (by rw [ht]; exact (smap_zero _).symm))

theorem kum_pull [NeZero q] {Y X : Scheme.{0}} (f : Y ⟶ X) (u : (Γ(X, ⊤))ˣ) (hX : IsUnit (q : Γ(X, ⊤))) :
    pull _ (sch.map f) _ _ (kum q u) = kum q (Units.map f.appTop.hom.toMonoidHom u) := by
  obtain ⟨γ, hγ, h₁, h₂⟩ := kum_spec q hX u
  obtain ⟨γ', hγ', h₁', h₂'⟩ := kum_spec q (unit_res f hX) (umap f u)
  rw [← hγ, ← hγ']
  change CohomologyClass.mk (zcomp (Cocycle.ofHom ((chains (ZMod q)).map (sch.map f))) γ (zero_add 1)) = _
  congr 1
  refine Cocycle.ext (kum_unique (unit_res f hX) (umap f u) (fun U y => ?_) (fun U y v hv => ?_) h₁' h₂')
  · change ev ((Cochain.ofHom ((chains (ZMod q)).map (sch.map f))).comp γ.1 (zero_add 1)) 1 0 _ U y = 0
    rw [(GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.2.2.1 (sch.map f) γ.1 1 0 _ U y]
    exact h₁ U (y ≫ f)
  · change ev ((Cochain.ofHom ((chains (ZMod q)).map (sch.map f))).comp γ.1 (zero_add 1)) 0 1 _ U y = _
    rw [(GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.2.2.1 (sch.map f) γ.1 0 1 _ U y]
    exact h₂ U (y ≫ f) v (by rw [hv, umap_comp])

theorem kum_mul [NeZero q] {X : Scheme.{0}} (hX : IsUnit (q : Γ(X, ⊤))) (u₁ u₂ : (Γ(X, ⊤))ˣ) :
    kum q (u₁ * u₂) = kum q u₁ + kum q u₂ := by
  obtain ⟨γ₁, e₁, a₁, b₁⟩ := kum_spec q hX u₁
  obtain ⟨γ₂, e₂, a₂, b₂⟩ := kum_spec q hX u₂
  obtain ⟨γ₃, e₃, a₃, b₃⟩ := kum_spec q hX (u₁ * u₂)
  rw [← e₁, ← e₂, ← e₃, eq_comm, ← CohomologyClass.mk_add, ← sub_eq_zero, ← CohomologyClass.mk_sub,
    CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ 0 (zero_add 1)]
  rcases kumT_cases q with ht | ht
  · obtain ⟨e, he, hw⟩ := exists_two_family ht (E := sch.obj X) (p := 0) (fun U (x : U ⟶ X) => unit_res x hX)
      (fun U (x : U ⟶ X) => umap x u₁) (fun U (x : U ⟶ X) => umap x u₂)
      (fun V U g (x : U ⟶ X) => umap_comp g x u₁) (fun V U g (x : U ⟶ X) => umap_comp g x u₂)
    obtain ⟨β, c₁, c₂⟩ := exists_single (I := res _ (tw q 1)) (n := 0) 0 0 (by simp) e he
    refine ⟨β, (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.2.1 _ _ fun p s h U x => ?_⟩
    rw [Cocycle.coe_sub, Cocycle.coe_add, ev_sub', ev_add]
    match p with
    | 0 =>
      obtain rfl : s = 1 := by omega
      rw [(GlobalTheory.T.etaleCochainEvalOnSimplex_differential_values (ZMod q) (zero_add 1) β U).1 x, c₁]
      have hxU := unit_res (show U ⟶ X from x) hX
      refine sep (ClsSpec.loc_mono (ClsSpec.loc_and (root_loc hxU (umap (show U ⟶ X from x) u₁))
        (root_loc hxU (umap (show U ⟶ X from x) u₂))) ?_)
      rintro V g ⟨⟨v, hv⟩, w, hw'⟩
      have hv' : v ^ q = umap (show V ⟶ X from x.res g) u₁ := by rw [hv]; exact (umap_comp g _ u₁).symm
      have hw'' : w ^ q = umap (show V ⟶ X from x.res g) u₂ := by rw [hw']; exact (umap_comp g _ u₂).symm
      have hvw : (v * w) ^ q = umap (show V ⟶ X from x.res g) (u₁ * u₂) := by rw [mul_pow, hv', hw'', map_mul]
      rw [res_map, he V U g x, res_sub, res_add, (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.1 γ₁.1 0 1 _ V U g x,
        (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.1 γ₂.1 0 1 _ V U g x, (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.1 γ₃.1 0 1 _ V U g x]
      rw [hw V (x.res g) v w hv' hw'', b₁ V (x.res g) v hv', b₂ V (x.res g) w hw'', b₃ V (x.res g) _ hvw, smap_sub,
        smap_add]
    | 1 =>
      obtain rfl : s = 0 := by omega
      have key := (GlobalTheory.T.etaleCochainEvalOnSimplex_differential_values (ZMod q) (zero_add 1) β U).2 0 (-1) 0 (by simp) h x
      have hf : x.face 0 = x.face 1 := rfl
      rw [key, c₂ (0 + 1) _ _ _ _ one_ne_zero, smap_zero, zero_add, Fin.sum_univ_two, hf, a₁ U x, a₂ U x, a₃ U x]
      simp
    | p + 2 =>
      haveI := sec_subsingleton (tw q 1) U (s := s) (by omega)
      exact Subsingleton.elim _ _
  · refine ⟨0, ?_⟩
    rw [δ_zero, Cocycle.coe_sub, Cocycle.coe_add, eq_zero_of_kumT ht hX u₁ a₁ b₁, eq_zero_of_kumT ht hX u₂ a₂ b₂,
      eq_zero_of_kumT ht hX _ a₃ b₃]
    simp

theorem kum_pow_self [NeZero q] {X : Scheme.{0}} (hX : IsUnit (q : Γ(X, ⊤))) (u : (Γ(X, ⊤))ˣ) : kum q (u ^ q) = 0 := by
  obtain ⟨γ, e, a, b⟩ := kum_spec q hX (u ^ q)
  rw [← e, CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ 0 (zero_add 1)]
  rcases kumT_cases q with ht | ht
  · obtain ⟨β, c₁, c₂⟩ := exists_single (E := sch.obj X) (I := res _ (tw q 1)) (n := 0) 0 0 (by simp)
      (fun U (x : U ⟶ X) => kumT q U (umap x u))
      (fun V U g (x : U ⟶ X) => (ht.1 V U g _ (unit_res x hX)).trans (congrArg (kumT q V) (umap_comp g x u).symm))
    refine ⟨β, (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.2.1 _ _ fun p s h U x => ?_⟩
    match p with
    | 0 =>
      obtain rfl : s = 1 := by omega
      rw [(GlobalTheory.T.etaleCochainEvalOnSimplex_differential_values (ZMod q) (zero_add 1) β U).1 x, c₁]
      change U ⟶ X at x
      exact (b U x _ (by rw [← map_pow])).symm
    | 1 =>
      obtain rfl : s = 0 := by omega
      have key := (GlobalTheory.T.etaleCochainEvalOnSimplex_differential_values (ZMod q) (zero_add 1) β U).2 0 (-1) 0 (by simp) h x
      have hf : x.face 0 = x.face 1 := rfl
      rw [key, c₂ (0 + 1) _ _ _ _ one_ne_zero, smap_zero, zero_add, Fin.sum_univ_two, hf, a U x]
      simp
    | p + 2 =>
      haveI := sec_subsingleton (tw q 1) U (s := s) (by omega)
      exact Subsingleton.elim _ _
  · exact ⟨0, by rw [δ_zero, eq_zero_of_kumT ht hX _ a b]⟩

end KumNat

open KumNat in

theorem kum_cocycle_natural_additive : ∀ (q : ℕ) [NeZero q], (∀ (X : Scheme.{0}) (u : (Γ(X, ⊤))ˣ), IsUnit (q : Γ(X, ⊤)) → ∃ γ : Cocycle ((chains (ZMod q)).obj (sch.obj X)) (res _ (tw q 1)) 1, CohomologyClass.mk γ = kum q u ∧ (∀ (U : Scheme.{0}) (x : U ⟶ X), ev γ.1 1 0 (by simp) U x = 0) ∧ ∀ (U : Scheme.{0}) (x : U ⟶ X) (v : (Γ(U, ⊤))ˣ), v ^ q = Units.map x.appTop.hom.toMonoidHom u → ev γ.1 0 1 (by simp) U x = Sec.map ((res _ (tw q 1)).d 0 1) (kumT q U v)) ∧ (∀ {Y X : Scheme.{0}} (f : Y ⟶ X) (u : (Γ(X, ⊤))ˣ), IsUnit (q : Γ(X, ⊤)) → pull _ (sch.map f) _ _ (kum q u) = kum q (Units.map f.appTop.hom.toMonoidHom u)) ∧ ∀ {X : Scheme.{0}} (u v : (Γ(X, ⊤))ˣ), IsUnit (q : Γ(X, ⊤)) → kum q (u * v) = kum q u + kum q v ∧ kum q (u ^ q) = 0 := by
  intro q _
  exact ⟨fun X u hX => kum_spec q hX u, fun f u hX => kum_pull f u hX, fun u v hX => ⟨kum_mul hX u v, kum_pow_self hX u⟩⟩

end GlobalTheory.EtC

end
