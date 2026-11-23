import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HypercohomologyMappingConeSecondVariableExactStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocalPropertyCalculusRulesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChosenInjectiveResolutionEtaleSheafPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChosenInjectiveResolutionEtaleSheafSectionsExactStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubsingletonHypercohomologyOfLocallyExactOnSuppoStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC.ConeChase

variable {R : Type} [CommRing R]

theorem map_comp {F G K : Shv R} (a : F ⟶ G) (b : G ⟶ K) {U : Scheme.{0}} (x : Sec F U) :
    Sec.map (a ≫ b) x = Sec.map b (Sec.map a x) := rfl

theorem map_congr {F G : Shv R} {a b : F ⟶ G} (h : a = b) {U : Scheme.{0}} (x : Sec F U) :
    Sec.map a x = Sec.map b x := by rw [h]

theorem map_zero_hom {F G : Shv R} {U : Scheme.{0}} (x : Sec F U) :
    Sec.map (0 : F ⟶ G) x = 0 := rfl

theorem map_add' {F G : Shv R} (a : F ⟶ G) {U : Scheme.{0}} (x y : Sec F U) :
    Sec.map a (x + y) = Sec.map a x + Sec.map a y := map_add _ _ _

theorem map_neg' {F G : Shv R} (a : F ⟶ G) {U : Scheme.{0}} (x : Sec F U) :
    Sec.map a (-x) = -Sec.map a x := map_neg _ _

theorem map_zero' {F G : Shv R} (a : F ⟶ G) {U : Scheme.{0}} :
    Sec.map a (0 : Sec F U) = 0 := map_zero _

theorem res_add {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) (x y : Sec F U) :
    Sec.res g (x + y) = Sec.res g x + Sec.res g y := map_add _ _ _

theorem res_zero {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) :
    Sec.res g (0 : Sec F U) = 0 := map_zero _

theorem res_map {F G : Shv R} (a : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sec F U) :
    Sec.res g (Sec.map a x) = Sec.map a (Sec.res g x) := by
  have := congrArg (fun t => t.hom x) (a.hom.naturality g.op)
  exact this.symm

theorem res_comp {F : Shv R} {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U) (x : Sec F U) :
    Sec.res (k ≫ g) x = Sec.res k (Sec.res g x) := by
  have := congrArg (fun t => t.hom x) (F.obj.map_comp g.op k.op)
  exact this

theorem comm' {I J : Cx R} (f : I ⟶ J) (i j : ℤ) {U : Scheme.{0}} (x : Sec (I.X i) U) :
    Sec.map (J.d i j) (Sec.map (f.f i) x) = Sec.map (f.f j) (Sec.map (I.d i j) x) :=
  map_congr (f.comm i j) x

theorem mappingCone_resolution_localChase_of_succ (E : Spc) {F G : Shv R} (φ : F ⟶ G)
    (hφ : ∀ U : Scheme.{0}, Nonempty (Sx E 0 U) → Function.Bijective (Sec.map φ (U := U)))
    (U : Scheme.{0}) (hU : Nonempty (Sx E 0 U)) (m n k l : ℤ) (hm : m + 1 = n) (hk : n + 1 = k) (hl : k + 1 = l)
    (b₁ : Sec ((res R F).X k) U) (b₂ : Sec ((res R G).X n) U)
    (h₁ : Sec.map ((res R F).d k l) b₁ = 0)
    (h₂ : Sec.map ((resMap R φ).f k) b₁ + Sec.map ((res R G).d n k) b₂ = 0) :
    Loc U fun V g => ∃ (a₁ : Sec ((res R F).X n) V) (a₂ : Sec ((res R G).X m) V),
      Sec.map ((res R F).d n k) a₁ = -Sec.res g b₁ ∧
      Sec.map ((resMap R φ).f n) a₁ + Sec.map ((res R G).d m n) a₂ = Sec.res g b₂ := by
  obtain ⟨Lall, Lmono, -, -, Ltrans, -, -⟩ := GlobalTheory.T.etaleLocal_property_calculus_rules
  have hι := ((GlobalTheory.T.chosenInjectiveResolution_etaleSheaf_properties R F).2.2.2.2.2.2.2 G φ).2
  have hd := (GlobalTheory.T.chosenInjectiveResolution_etaleSheaf_properties R F).2.2.2.2.2.2.1
  rcases lt_or_ge n 0 with hn | hn
  · have hb₂ : b₂ = 0 := ((GlobalTheory.T.chosenInjectiveResolutionEtaleSheaf_sections_exactness R G U).2.2.2 n hn).elim _ _
    have hb₁ : b₁ = 0 := by
      rcases lt_or_ge k 0 with hk0 | hk0
      · exact ((GlobalTheory.T.chosenInjectiveResolutionEtaleSheaf_sections_exactness R F U).2.2.2 k hk0).elim _ _
      · obtain rfl : k = 0 := by omega
        obtain rfl : l = 1 := by omega
        obtain ⟨s, rfl⟩ := ((GlobalTheory.T.chosenInjectiveResolutionEtaleSheaf_sections_exactness R F U).1 b₁).1 h₁
        rw [hb₂, map_zero', add_zero, ← map_comp, map_congr hι, map_comp] at h₂
        have h3 : Sec.map φ s = 0 := (GlobalTheory.T.chosenInjectiveResolutionEtaleSheaf_sections_exactness R G U).2.1 (by rw [h₂, map_zero'])
        have h4 : s = 0 := (hφ U hU).1 (by rw [h3, map_zero'])
        rw [h4, map_zero']
    refine Lall _ _ fun V g => ⟨0, 0, ?_, ?_⟩
    · rw [hb₁, map_zero', res_zero, neg_zero]
    · rw [hb₂, map_zero', map_zero', res_zero, add_zero]
  · apply Ltrans
    refine Lmono _ _ _ ((GlobalTheory.T.chosenInjectiveResolutionEtaleSheaf_sections_exactness R F U).2.2.1 n k l (by omega) hk b₁ hl h₁) ?_
    rintro V g ⟨y, hy⟩
    have hc : Sec.map ((res R G).d n k) (Sec.res g b₂ + Sec.map ((resMap R φ).f n) y) = 0 := by
      rw [map_add', comm', hy, ← res_map, ← res_map, ← res_add, add_comm, h₂, res_zero]
    rcases lt_or_eq_of_le hn with hn' | hn'
    · refine Lmono _ _ _ ((GlobalTheory.T.chosenInjectiveResolutionEtaleSheaf_sections_exactness R G V).2.2.1 m n k hn' hm _ hk hc) ?_
      rintro W j ⟨z, hz⟩
      refine ⟨-Sec.res j y, z, ?_, ?_⟩
      · rw [map_neg', ← res_map, hy, res_comp]
      · rw [hz, map_neg', res_add, res_map, res_comp]; abel
    · subst hn'
      obtain rfl : k = 1 := by omega
      obtain ⟨s, hs⟩ := ((GlobalTheory.T.chosenInjectiveResolutionEtaleSheaf_sections_exactness R G V).1 _).1 hc
      obtain ⟨x⟩ := hU
      obtain ⟨t, rfl⟩ := (hφ V ⟨Sx.res g x⟩).2 s
      refine Lall _ _ fun W j => ⟨Sec.res j (-y + Sec.map (resι R F) t), 0, ?_, ?_⟩
      · rw [← res_map, map_add', map_neg', hy, ← map_comp, map_congr hd, map_zero_hom, add_zero, res_comp]
        exact map_neg _ _
      · rw [map_zero', add_zero, ← res_map, map_add', map_neg', ← map_comp, map_congr hι, map_comp, hs, res_comp]
        congr 1
        abel

theorem chase : ∀ (R : Type) [CommRing R] (E : Spc) {F G : Shv R} (φ : F ⟶ G), (∀ U : Scheme.{0}, Nonempty (Sx E 0 U) → Function.Bijective (Sec.map φ (U := U))) → ∀ (U : Scheme.{0}), Nonempty (Sx E 0 U) → ∀ (n : ℤ) (b₁ : Sec ((res R F).X (n + 1)) U) (b₂ : Sec ((res R G).X n) U), Sec.map ((res R F).d (n + 1) (n + 2)) b₁ = 0 → Sec.map ((resMap R φ).f (n + 1)) b₁ + Sec.map ((res R G).d n (n + 1)) b₂ = 0 → Loc U fun V g => ∃ (a₁ : Sec ((res R F).X n) V) (a₂ : Sec ((res R G).X (n - 1)) V), Sec.map ((res R F).d n (n + 1)) a₁ = -Sec.res g b₁ ∧ Sec.map ((resMap R φ).f n) a₁ + Sec.map ((res R G).d (n - 1) n) a₂ = Sec.res g b₂ :=
  fun _ _ E _ _ φ hφ U hU n b₁ b₂ h₁ h₂ =>
    mappingCone_resolution_localChase_of_succ E φ hφ U hU (n - 1) n (n + 1) (n + 2) (by ring) rfl (by ring) b₁ b₂ h₁ h₂

end GlobalTheory.EtC.ConeChase
