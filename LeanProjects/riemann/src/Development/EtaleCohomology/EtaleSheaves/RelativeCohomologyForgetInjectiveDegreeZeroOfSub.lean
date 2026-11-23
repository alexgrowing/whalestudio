import Development.EtaleCohomology.EtaleSheaves.LeafInj0Of

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.LeafInj0VPf
open CochainComplex CochainComplex.HomComplex
open LateralTheory.E.E4 LateralTheory.E.LeafGhostCut LateralTheory.E.EtaleTopologySheaves LateralTheory.E.LeafDegCut LateralTheory.E.LeafInj0Pf

def LeafSecTr : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (i : ℤ) {B W Y : Scheme.{0}} (ι : W ⟶ B) (P : Y ⟶ B) (U : B.Etale)
  (c : Hrel (ZMod q) (sch.map (prB ι U)) (tw q i) 0), ∃ s : Sec (tw q i) U.left,
  (∀ (U' : B.Etale) (a : U' ⟶ U), Sec.res a.left s = 0 → rB q i ι a 0 c = 0) ∧
  (∀ (U' : B.Etale) (a : U' ⟶ U), rY q i P ι a 0 (bY q i P ι U 0 c) = 0 → Sec.res (toBY P U' ≫ a.left) s = 0)

def LeafSecV : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k], IsUnit (q : k) → ∀ (i : ℤ)
  {B W Y0 Y1 Y2 : Scheme.{0}} (_ : B ⟶ Sp k) (ι : W ⟶ B) [IsClosedImmersion ι] (V : B.Opens), (V : Set B) = (Set.range ι)ᶜ →
  ∀ (p : Y0 ⟶ B) (g1 : Y1 ⟶ Y0) (g2 : Y2 ⟶ Y1), IsProper p → IsProper (g1 ≫ p) → IsProper (g2 ≫ g1 ≫ p) →
  SHV q i V p g1 g2 → ∀ (U : B.Etale) (s : Sec (tw q i) U.left),
  Cov U (fun U' a => Sec.res (toBY (g2 ≫ g1 ≫ p) U' ≫ a.left) s = 0) →
  ∀ x : U.left, U.hom x ∉ Set.range ι →
  ∃ (U' : B.Etale) (a : U' ⟶ U) (y : U'.left), a.left y = x ∧ Sec.res a.left s = 0

theorem res_comp {q : ℕ} {i : ℤ} {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (s : Sec (tw q i) Z) :
    Sec.res (f ≫ g) s = Sec.res f (Sec.res g s) := by
  simp [Sec.res, op_comp, Functor.map_comp]

theorem relative_cohomology_forget_injective_degree_zero_of_subsingleton (R : Type) [CommRing R] (F : Shv R) {U E : Spc} (f : U ⟶ E)
    (hU : Subsingleton (H R U F (-1))) (y : Hrel R f F 0) (hy : fgt R f F 0 y = 0) : y = 0 := by
  obtain ⟨z, rfl⟩ := y.mk_surjective
  change CohomologyClass.mk (zcomp (Cocycle.ofHom (mappingCone.inr ((chains R).map f))) z (zero_add 0)) = 0 at hy
  rw [CohomologyClass.mk_eq_zero_iff] at hy
  obtain ⟨m, hm, γ, hγ⟩ := hy
  obtain rfl : m = -1 := by omega
  simp only [zcomp, Cocycle.mk_coe, Cocycle.ofHom_coe] at hγ
  set φ := (chains R).map f
  let w : Cochain (mappingCone φ) (res R F) (-1) := mappingCone.descCochain φ (0 : Cochain ((chains R).obj U) (res R F) (-2)) γ (by norm_num)
  let z' : Cochain (mappingCone φ) (res R F) 0 := z.1 - δ (-1) 0 w
  have hz'c : δ 0 1 z' = 0 := by
    simp [z', δ_δ]
  have hinr : (Cochain.ofHom (mappingCone.inr φ)).comp z' (zero_add 0) = 0 := by
    have h1 : δ (-1) 0 ((Cochain.ofHom (mappingCone.inr φ)).comp w (zero_add _)) =
        (Cochain.ofHom (mappingCone.inr φ)).comp (δ (-1) 0 w) (zero_add 0) := by
      rw [δ_ofHom_comp]
    simp only [z', Cochain.comp_sub, ← h1, w, mappingCone.inr_descCochain]
    rw [hγ, sub_self]
  let β : Cochain ((chains R).obj U) (res R F) (-1) := (mappingCone.inl φ).comp z' (by norm_num)
  have hβc : δ (-1) 0 β = 0 := by
    simp only [β]
    rw [δ_comp _ _ (by norm_num) 0 1 0 (by norm_num) (by norm_num) (by norm_num), mappingCone.δ_inl, hz'c]
    simp only [Cochain.comp_zero, smul_zero, add_zero, Cochain.ofHom_comp]
    rw [Cochain.comp_assoc_of_first_is_zero_cochain, hinr]
    simp
  have hβ0 : CohomologyClass.mk (Cocycle.mk β 0 (by norm_num) hβc) = (0 : H R U F (-1)) := Subsingleton.elim _ _
  rw [CohomologyClass.mk_eq_zero_iff] at hβ0
  obtain ⟨m', hm', ε, hε⟩ := hβ0
  obtain rfl : m' = -2 := by omega
  have hz' : z' = δ (-1) 0 (mappingCone.descCochain φ ε 0 (by norm_num)) := by
    rw [mappingCone.δ_descCochain _ _ _ _ 0 (by norm_num)]
    rw [mappingCone.ext_cochain_from_iff φ (-1) 0 (by norm_num)]
    constructor
    · simp [β] at hε
      simp [hε, β]
    · simp [hinr]
  rw [CohomologyClass.mk_eq_zero_iff]
  refine ⟨-1, by norm_num, w + mappingCone.descCochain φ ε 0 (by norm_num), ?_⟩
  rw [δ_add, ← hz']
  simp [z']

theorem secTr (hH : Hyps) (q : ℕ) [NeZero q] (i : ℤ) {B W Y : Scheme.{0}} (ι : W ⟶ B) (P : Y ⟶ B) (U : B.Etale)
    (c : Hrel (ZMod q) (sch.map (prB ι U)) (tw q i) 0) : ∃ s : Sec (tw q i) U.left,
    (∀ (U' : B.Etale) (a : U' ⟶ U), Sec.res a.left s = 0 → rB q i ι a 0 c = 0) ∧
    (∀ (U' : B.Etale) (a : U' ⟶ U), rY q i P ι a 0 (bY q i P ι U 0 c) = 0 → Sec.res (toBY P U' ≫ a.left) s = 0) := by
  have hA9 : A9 := hH.2.2.2.2.2.2.2.1
  obtain ⟨hneg, e, hnat, -⟩ := hA9 (ZMod q) (tw q i)
  refine ⟨(e U.left).symm (fgt _ _ _ 0 c), ?_, ?_⟩
  · intro U' a ha
    apply relative_cohomology_forget_injective_degree_zero_of_subsingleton _ _ _ (hneg _ (-1) (by norm_num))
    rw [relNat]
    have := hnat a.left ((e U.left).symm (fgt _ _ _ 0 c))
    rw [AddEquiv.apply_symm_apply] at this
    rw [this, ha, map_zero]
  · intro U' a ha
    have h0 := congrArg (fgt _ _ _ 0) ha
    rw [map_zero, relNat, relNat, ← pull_comp, ← Functor.map_comp] at h0
    have hsq : resY P a ≫ toBY P U = toBY P U' ≫ a.left := by simp only [resY, toBY]; exact pullback.lift_snd _ _ _
    rw [hsq] at h0
    have := hnat (toBY P U' ≫ a.left) ((e U.left).symm (fgt _ _ _ 0 c))
    rw [AddEquiv.apply_symm_apply, h0] at this
    exact (e _).injective (by rw [← this, map_zero])

def LeafSHPt : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k], IsUnit (q : k) → ∀ (i : ℤ) {B : Scheme.{0}}
  (U : B.Etale) (_ : U.left ⟶ Sp k) (x : U.left), ∃ (A : Type) (_ : CommRing A) (t : Sp A ⟶ U.left), SH A ∧
  (∀ O : U.left.Opens, x ∈ O → Set.range t ⊆ O) ∧
  (∀ S ∈ (EtTop B) U, ∃ (U' : B.Etale) (a : U' ⟶ U), S a ∧ ∃ t' : Sp A ⟶ U'.left, t' ≫ a.left = t) ∧
  ∀ s : Sec (tw q i) U.left, Sec.res t s = 0 → ∃ (U' : B.Etale) (a : U' ⟶ U) (y : U'.left), a.left y = x ∧ Sec.res a.left s = 0

theorem LeafSecV_of (hP : LeafSHPt) : LeafSecV := by
  intro hH q _ k _ hq i B W Y0 Y1 Y2 s0 ι _ V hV' p g1 g2 hp1 hp2 hp3 hSH U s hc x hx
  have hA9 : A9 := hH.2.2.2.2.2.2.2.1
  obtain ⟨-, e, hnat, -⟩ := hA9 (ZMod q) (tw q i)
  obtain ⟨A, _, t, hA, hO, hL, hG⟩ := hP hH q k hq i U (U.hom ≫ s0) x
  apply hG
  set P := g2 ≫ g1 ≫ p
  have hxV : x ∈ (U.hom ⁻¹ᵁ V) := by
    change U.hom x ∈ (V : Set B); rw [hV']; exact hx
  have hr : Set.range (t ≫ U.hom) ⊆ (V : Set B) := by
    rintro _ ⟨z, rfl⟩
    exact hO _ hxV ⟨z, rfl⟩
  have hinj := ((hSH A (t ≫ U.hom) hA hr).2.2.2).1
  obtain ⟨S, hS, hPS⟩ := hc
  obtain ⟨U', a, hSa, t', ht'⟩ := hL S hS
  have h0 := hPS U' a hSa
  have hm : pullback.snd P (t ≫ U.hom) ≫ t =
      pullback.map P (t ≫ U.hom) P U'.hom (𝟙 _) t' (𝟙 B) (by simp) (by
        rw [Category.comp_id, ← ht', Category.assoc]; congr 1; simpa using a.w) ≫ (toBY P U' ≫ a.left) := by
    simp only [toBY]
    rw [pullback.lift_snd_assoc, Category.assoc, ht']
  apply (e _).injective
  apply hinj
  rw [map_zero, map_zero]
  change pull _ (sch.map (pullback.snd P (t ≫ U.hom))) _ 0 (e _ (Sec.res t s)) = 0
  rw [hnat, ← res_comp, hm, res_comp, h0]
  simp

theorem LeafInj0V_of_sec (hT : LeafSecTr) (hS : LeafSecV) : LeafInj0V := by
  intro hH q _ k _ hq i B W Y0 Y1 Y2 s0 ι _ V hV' p g1 g2 hp1 hp2 hp3 hSH U c hc x hx
  obtain ⟨s, h1, h2⟩ := hT hH q i ι (g2 ≫ g1 ≫ p) U c
  obtain ⟨U', a, y, hy, hs⟩ := hS hH q k hq i s0 ι V hV' p g1 g2 hp1 hp2 hp3 hSH U s
    (hc.mono fun U'' b hb => h2 U'' b hb) x hx
  refine ⟨U', a, y, hy, Cov.all fun U'' b => h1 U'' (b ≫ a) ?_⟩
  change Sec.res (b.left ≫ a.left) s = 0
  rw [res_comp, hs]
  simp
theorem LeafInj0V_of (hP : LeafSHPt) : LeafInj0V :=
  LeafInj0V_of_sec (fun hH q _ i _ _ _ ι P U c => secTr hH q i ι P U c) (LeafSecV_of hP)
end LateralTheory.E.LeafInj0VPf
