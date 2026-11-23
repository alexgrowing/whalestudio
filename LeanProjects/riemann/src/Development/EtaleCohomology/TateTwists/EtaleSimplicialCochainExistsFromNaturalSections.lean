import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.EtaleCohomology.TateTwists.EtaleSchemeGlobalSectionCohomologyClass

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

def EtaleSimplicialCochainExistsFromNaturalSections : Prop := ∀ (R : Type) [CommRing R] {E : Spc} {I : Cx R} {n : ℤ} (a : ∀ (p : ℕ) (s : ℤ), -(p : ℤ) + n = s → ∀ U : Scheme.{0}, Sx E p U → Sec (I.X s) U), (∀ p s h (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U), Sec.res g (a p s h U x) = a p s h V (x.res g)) → ∃ α : Cochain ((chains R).obj E) I n, ∀ p s h U x, ev α p s h U x = a p s h U x

def EtaleSimplicialCochainEvaluationDifferentialFormula : Prop := ∀ (R : Type) [CommRing R] {E : Spc} {I : Cx R} {n m : ℤ} (hm : n + 1 = m) (α : Cochain ((chains R).obj E) I n) (U : Scheme.{0}), (∀ (x : Sx E 0 U), ev (δ n m α) 0 m (by simp) U x = Sec.map (I.d n m) (ev α 0 n (by simp) U x)) ∧ ∀ (p : ℕ) (s t : ℤ) (hs : -((p + 1 : ℕ) : ℤ) + n = s) (ht : -((p + 1 : ℕ) : ℤ) + m = t) (x : Sx E (p + 1) U), ev (δ n m α) (p + 1) t ht U x = Sec.map (I.d s t) (ev α (p + 1) s hs U x) + m.negOnePow • ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • ev α p t (by omega) U (x.face i)

def EtaleSimplicialCochainEvaluationProperties : Prop := ∀ (R : Type) [CommRing R] {E : Spc} {I : Cx R} {n : ℤ}, (∀ (α β : Cochain ((chains R).obj E) I n) p s h U x, ev (α + β) p s h U x = ev α p s h U x + ev β p s h U x ∧ ev (α - β) p s h U x = ev α p s h U x - ev β p s h U x ∧ ev (0 : Cochain ((chains R).obj E) I n) p s h U x = 0 ∧ ∀ c : ℤ, ev (c • α) p s h U x = c • ev α p s h U x) ∧ (∀ (α : Cochain ((chains R).obj E) I n) p s h (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U), Sec.res g (ev α p s h U x) = ev α p s h V (x.res g)) ∧ (∀ α β : Cochain ((chains R).obj E) I n, (∀ p s h U x, ev α p s h U x = ev β p s h U x) → α = β) ∧ (∀ {E' : Spc} (f : E' ⟶ E) (α : Cochain ((chains R).obj E) I n) p s h U (x : Sx E' p U), ev ((Cochain.ofHom ((chains R).map f)).comp α (zero_add n)) p s h U x = ev α p s h U (x.map f)) ∧ ∀ {J : Cx R} (m : I ⟶ J) (α : Cochain ((chains R).obj E) I n) p s h U x, ev (α.comp (Cochain.ofHom m) (add_zero n)) p s h U x = Sec.map (m.f s) (ev α p s h U x)

def EtaleSimplicialSchemeCocycleVanishingAtIdIsCoboundary : Prop := ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (I : Cx R) (m n : ℤ), m + 1 = n → ∀ α : Cocycle ((chains R).obj (sch.obj X)) I n, ev α.1 0 n (by simp) X (𝟙 X) = 0 → ∃ β : Cochain ((chains R).obj (sch.obj X)) I m, δ m n β = α.1

def a0 {R : Type} [CommRing R] (X : Scheme.{0}) (I : Cx R) (n : ℤ) (z : Sec (I.X n) X) :
    ∀ (p : ℕ) (s : ℤ), -(p : ℤ) + n = s → ∀ U : Scheme.{0}, Sx (sch.obj X) p U → Sec (I.X s) U
  | 0, s, h, U, x => (show n = s by omega) ▸ Sec.res (x : U ⟶ X) z
  | _ + 1, _, _, _, _ => 0

lemma etaleSimplicialCochain_scheme_section_extension_degree_zero {R : Type} [CommRing R] (X : Scheme.{0}) (I : Cx R) (n : ℤ) (z : Sec (I.X n) X) (h : -((0:ℕ) : ℤ) + n = n)
    (U : Scheme.{0}) (x : Sx (sch.obj X) 0 U) : a0 X I n z 0 n h U x = Sec.res (x : U ⟶ X) z := rfl

lemma res_res {R : Type} [CommRing R] {F : Shv R} {W V U : Scheme.{0}} (g : W ⟶ V) (f : V ⟶ U) (z : Sec F U) :
    Sec.res g (Sec.res f z) = Sec.res (g ≫ f) z := by
  simp [Sec.res, op_comp, Functor.map_comp]

lemma res_id {R : Type} [CommRing R] {F : Shv R} {U : Scheme.{0}} (z : Sec F U) : Sec.res (𝟙 U) z = z := by
  simp [Sec.res]

lemma map_res {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (z : Sec F U) :
    Sec.map φ (Sec.res g z) = Sec.res g (Sec.map φ z) := by
  simp only [Sec.map, Sec.res]
  exact congrArg (fun f => ModuleCat.Hom.hom f z) (φ.hom.naturality g.op)

lemma etaleSimplicialCochain_scheme_section_extension_naturality {R : Type} [CommRing R] (X : Scheme.{0}) (I : Cx R) (n : ℤ) (z : Sec (I.X n) X) :
    ∀ p s h (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx (sch.obj X) p U),
      Sec.res g (a0 X I n z p s h U x) = a0 X I n z p s h V (x.res g) := by
  intro p s h V U g x
  cases p with
  | zero =>
    obtain rfl : s = n := by omega
    exact res_res g x z
  | succ q => simp [a0, Sec.res]

end LateralTheory.EtaleFoundations

open LateralTheory.EtaleFoundations in
theorem LateralTheory.EtaleFoundations.etaleSimplicialCochain_scheme_class_of_evaluation_properties (hmk : EtaleSimplicialCochainExistsFromNaturalSections) (hdl : EtaleSimplicialCochainEvaluationDifferentialFormula)
    (hb : EtaleSimplicialCochainEvaluationProperties) (hcob : EtaleSimplicialSchemeCocycleVanishingAtIdIsCoboundary) : EtaleSchemeGlobalSectionCohomologyClass := by
  intro R _ X I m n k hmn hnk

  have v0 : ∀ {q : ℤ} (β : Cochain ((chains R).obj (sch.obj X)) I q) (U : Scheme.{0}) (x : Sx (sch.obj X) 0 U),
      ev β 0 q (by simp) U x = Sec.res (x : U ⟶ X) (ev β 0 q (by simp) X (𝟙 X)) := by
    intro q β U x
    rw [(hb R).2.1 β 0 q (by simp) U X x (𝟙 X)]
    rfl
  refine ⟨?_, ?_⟩
  · intro z hz
    obtain ⟨α, hα⟩ := hmk R (a0 X I n z) (etaleSimplicialCochain_scheme_section_extension_naturality X I n z)
    have hδ : δ n k α = 0 := by
      apply (hb R).2.2.1
      intro p s h U x
      rw [((hb R).1 (δ n k α) (δ n k α) p s h U x).2.2.1]
      cases p with
      | zero =>
        obtain rfl : s = k := by omega
        rw [(hdl R hnk α U).1 x, hα, etaleSimplicialCochain_scheme_section_extension_degree_zero]
        exact (map_res (I.d n s) (x : U ⟶ X) z).trans (by rw [hz]; simp [Sec.res])
      | succ p =>
        rw [(hdl R hnk α U).2 p (-((p + 1 : ℕ) : ℤ) + n) s rfl h x]
        simp only [hα]
        cases p with
        | zero =>
          obtain rfl : s = n := by omega
          simp [a0, Fin.sum_univ_two]
          rw [show x.face 0 = x from rfl, show x.face 1 = x from rfl]
          exact add_neg_cancel _
        | succ p => simp [a0]
    refine ⟨Cocycle.mk α k hnk hδ, ?_, ?_⟩
    · intro U x; exact hα 0 n (by simp) U x
    · intro p s h U x; rw [show (Cocycle.mk α k hnk hδ).1 = α from rfl, hα]; rfl
  · intro α
    have hd0 : Sec.map (I.d n k) (ev α.1 0 n (by simp) X (𝟙 X)) = 0 := by
      rw [← (hdl R hnk α.1 X).1 (𝟙 X), Cocycle.δ_eq_zero]
      exact ((hb R (E := sch.obj X) (I := I) (n := k)).1 0 0 0 k (by simp) X (𝟙 X)).2.2.1
    refine ⟨hd0, ?_⟩
    rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff α m hmn]
    constructor
    · rintro ⟨β, hβ⟩
      refine ⟨ev β 0 m (by simp) X (𝟙 X), ?_⟩
      rw [← (hdl R hmn β X).1 (𝟙 X), hβ]
    · rintro ⟨y, hy⟩
      obtain ⟨γ, hγ⟩ := hmk R (a0 X I m y) (etaleSimplicialCochain_scheme_section_extension_naturality X I m y)
      have hc : δ n k (α.1 - δ m n γ) = 0 := by
        rw [δ_sub, Cocycle.δ_eq_zero, δ_δ, sub_zero]
      obtain ⟨β, hβ⟩ := hcob R X I m n hmn (Cocycle.mk (α.1 - δ m n γ) k hnk hc) (by
        have e := ((hb R).1 (α : Cochain ((chains R).obj (sch.obj X)) I n) (δ m n γ) 0 n (by simp) X (𝟙 X)).2.1
        have e2 : ev (δ m n γ) 0 n (by simp) X (𝟙 X) = Sec.map (I.d m n) y := by
          rw [(hdl R hmn γ X).1 (𝟙 X)]
          exact congrArg (Sec.map (I.d m n)) ((hγ 0 m (by simp) X (𝟙 X)).trans (res_id y))
        exact e.trans ((congrArg (ev (α : Cochain ((chains R).obj (sch.obj X)) I n) 0 n (by simp) X (𝟙 X) - ·) e2).trans
          (sub_eq_zero.mpr hy.symm)))
      refine ⟨β + γ, ?_⟩
      rw [δ_add, hβ]
      show α.1 - δ m n γ + δ m n γ = α.1
      abel
