import Development.EtaleCohomology.CohomologicalPurity.LeafClCut

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex.HomComplex

namespace LateralTheory.CohomologicalPurity.Cl

abbrev resO (q : ℕ) {X : Scheme.{0}} (U : X.Opens) (V : X.Opens) (n i : ℤ) :
    Hs q (opn U) n i →+ Hs q (opn (V.ι ⁻¹ᵁ U)) n i :=
  Hs.pull q (opnMap V.ι (V.ι ⁻¹ᵁ U) U le_rfl) n i

def LocVanO (q : ℕ) {X : Scheme.{0}} (U : X.Opens) (m i : ℤ) : Prop := ∀ (x : X) (W : X.Opens), x ∈ W →
  ∃ V : X.Opens, V ≤ W ∧ x ∈ V ∧ ∀ n < m, Subsingleton (Hs q (opn (V.ι ⁻¹ᵁ U)) n i)

def SepO (q : ℕ) {X : Scheme.{0}} (U : X.Opens) (m i : ℤ) : Prop := ∀ s : Hs q (opn U) m i,
  (∀ x : X, x ∉ U → ∃ V : X.Opens, x ∈ V ∧ resO q U V m i s = 0) → s = 0

def GlueO (q : ℕ) {X : Scheme.{0}} (U : X.Opens) (m i : ℤ) : Prop :=
  ∀ (A : Type) (V : A → X.Opens) (s : ∀ a, Hs q (opn ((V a).ι ⁻¹ᵁ U)) m i), (∀ x : X, x ∉ U → ∃ a, x ∈ V a) →
  (∀ a b, ∀ x ∈ V a, x ∈ V b → x ∉ U → ∃ (T : X.Opens) (ha : T ≤ V a) (hb : T ≤ V b)
    (ha' : T.ι ⁻¹ᵁ U ≤ X.homOfLE ha ⁻¹ᵁ ((V a).ι ⁻¹ᵁ U)) (hb' : T.ι ⁻¹ᵁ U ≤ X.homOfLE hb ⁻¹ᵁ ((V b).ι ⁻¹ᵁ U)),
    x ∈ T ∧ Hs.pull q (opnMap (X.homOfLE ha) _ _ ha') m i (s a) = Hs.pull q (opnMap (X.homOfLE hb) _ _ hb') m i (s b)) →
  ∃ c, ∀ a, resO q U (V a) m i c = s a

def LeafDescOSep : Prop := LeafDict → LeafFlq → ∀ (q : ℕ) {X : Scheme.{0}} (U : X.Opens) (m i : ℤ),
  LocVanO q U m i → SepO q U m i

def LeafDescOGlue : Prop := LeafDict → LeafFlq → ∀ (q : ℕ) {X : Scheme.{0}} (U : X.Opens) (m i : ℤ),
  LocVanO q U m i → GlueO q U m i

def LeafPcVan : Prop := ∀ (q : ℕ) {X : Scheme.{0}} (U : X.Opens) (m i : ℤ), LocVan q U m i → LocVanO q U m i

def LeafPcSep : Prop := ∀ (q : ℕ) {X : Scheme.{0}} (U : X.Opens) (m i : ℤ), SepO q U m i → Sep q U m i

def LeafPcGlue : Prop := ∀ (q : ℕ) {X : Scheme.{0}} (U : X.Opens) (m i : ℤ), GlueO q U m i → Glue q U m i

theorem opnMap_id {X : Scheme.{0}} (U : X.Opens) (h) : opnMap (𝟙 X) U U h = 𝟙 _ := by
  apply Arrow.hom_ext
  · change sch.map _ = sch.map (𝟙 _)
    congr 1
    exact (Scheme.Hom.resLE_id (X := X) (V := U) (V' := U) le_rfl).trans (Scheme.homOfLE_rfl _ _)
  · exact sch.map_id X

theorem dbl_id (P : Arrow Spc) : dbl.map (𝟙 P) = 𝟙 _ := by
  apply pushout.hom_ext
  · change dbl.inl _ ≫ _ = _
    rw [inl_map]; erw [Category.id_comp]
  · change dbl.inr _ ≫ _ = _
    rw [dbl.inr_map]; erw [Category.id_comp]

theorem Hs_pull_id (q : ℕ) {X : Scheme.{0}} (U : X.Opens) (h) (n i : ℤ) (c : Hs q (opn U) n i) :
    Hs.pull q (opnMap (𝟙 X) U U h) n i c = c := by
  apply Subtype.ext
  rw [opnMap_id]
  change pull _ (dbl.map _) _ n c.1 = c.1
  rw [dbl_id, pull_id]

section
variable {q : ℕ} {X : Scheme.{0}} {U : X.Opens}

instance (p : Pc U) : IsOpenImmersion p.j := p.op

theorem pc_le (p : Pc U) : p.V ≤ p.j.isoOpensRange.hom ⁻¹ᵁ (p.j.opensRange.ι ⁻¹ᵁ U) := by
  rw [p.hV]
  intro y hy
  change (p.j.isoOpensRange.hom ≫ p.j.opensRange.ι) y ∈ U
  rw [Scheme.Hom.isoOpensRange_hom_ι]; exact hy

theorem pc_le' (p : Pc U) : p.j.opensRange.ι ⁻¹ᵁ U ≤ p.j.isoOpensRange.inv ⁻¹ᵁ p.V := by
  rw [p.hV]
  intro y hy
  change (p.j.isoOpensRange.inv ≫ p.j) y ∈ U
  rw [Scheme.Hom.isoOpensRange_inv_comp]; exact hy

theorem pc_bij (p : Pc U) (n i : ℤ) :
    Function.Bijective (Hs.pull q (opnMap p.j.isoOpensRange.hom p.V _ (pc_le p)) n i) := by
  refine ⟨Function.LeftInverse.injective (g := Hs.pull q (opnMap p.j.isoOpensRange.inv _ _ (pc_le' p)) n i) ?_,
    Function.RightInverse.surjective (g := Hs.pull q (opnMap p.j.isoOpensRange.inv _ _ (pc_le' p)) n i) ?_⟩
  · intro c
    exact (pull_pull _ _ p.j.isoOpensRange.inv_hom_id _ _ _ _ _ (fun _ hy => hy) n i c).trans (Hs_pull_id q _ _ n i c)
  · intro c
    exact (pull_pull _ _ p.j.isoOpensRange.hom_inv_id _ _ _ _ _ (fun _ hy => hy) n i c).trans (Hs_pull_id q _ _ n i c)

theorem pc_res (p : Pc U) (n i : ℤ) (s : Hs q (opn U) n i) :
    p.res q n i s = Hs.pull q (opnMap p.j.isoOpensRange.hom p.V _ (pc_le p)) n i (resO q U p.j.opensRange n i s) :=
  (pull_pull _ _ (Scheme.Hom.isoOpensRange_hom_ι p.j) _ _ _ _ _ _ n i s).symm
end

theorem LeafPcVan_pf : LeafPcVan := by
  intro q X U m i hL x W hx
  obtain ⟨p, hxp, hpW, hs⟩ := hL x W hx
  refine ⟨p.j.opensRange, fun y hy => hpW hy, hxp, fun n hn => ?_⟩
  have := hs n hn
  exact (pc_bij p n i).1.subsingleton

theorem LeafPcSep_pf : LeafPcSep := by
  intro q X U m i hS s hs
  apply hS s
  intro x hx
  obtain ⟨p, hxp, h0⟩ := hs x hx
  refine ⟨p.j.opensRange, hxp, ?_⟩
  apply (pc_bij p m i).1
  rw [← pc_res, h0, map_zero]

theorem LeafDesc_of (hD : LeafDict) (hF : LeafFlq) (hS : LeafDescOSep) (hG : LeafDescOGlue) (hPG : LeafPcGlue) :
    LeafDesc := by
  intro q X U m i hL
  have hO := LeafPcVan_pf q U m i hL
  exact ⟨LeafPcSep_pf q U m i (hS hD hF q U m i hO), hPG q U m i (hG hD hF q U m i hO)⟩

end LateralTheory.CohomologicalPurity.Cl
