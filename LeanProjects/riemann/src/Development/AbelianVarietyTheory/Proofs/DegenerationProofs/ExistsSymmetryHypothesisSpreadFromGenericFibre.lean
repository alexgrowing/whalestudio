import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Definitions.Degenerations.RigGen
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveModel
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.LineBundleSymmetryHypothesisBaseChange
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsSchemeTheoreticallyDominantSpecOfInjective

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.SymSpread

variable {S U : Scheme.{0}} {G : Over S} {A : Over U} [GrpObj G] [GrpObj A] {j : U ⟶ S} {a : A.left ⟶ G.left}

theorem isPullback_square (h : IsGrpPullback A G j a) :
    IsPullback (lift (pushPt h.1.w (fst A A)) (pushPt h.1.w (snd A A))).left (A ⊗ A).hom (G ⊗ G).hom j := by
  let l := lift (pushPt h.1.w (fst A A)) (pushPt h.1.w (snd A A))
  have l₁ : l.left ≫ pullback.fst G.hom G.hom = pullback.fst A.hom A.hom ≫ a :=
    congrArg (fun z => z.left) (lift_fst (pushPt h.1.w (fst A A)) (pushPt h.1.w (snd A A)))
  have l₂ : l.left ≫ pullback.snd G.hom G.hom = pullback.snd A.hom A.hom ≫ a :=
    congrArg (fun z => z.left) (lift_snd (pushPt h.1.w (fst A A)) (pushPt h.1.w (snd A A)))
  have big : IsPullback (pullback.snd A.hom A.hom ≫ a) (pullback.fst A.hom A.hom) G.hom (A.hom ≫ j) :=
    (IsPullback.of_hasPullback A.hom A.hom).flip.paste_horiz h.1
  have h₁ : IsPullback l.left (pullback.fst A.hom A.hom) (pullback.fst G.hom G.hom) a := by
    refine IsPullback.of_right (h₁₂ := pullback.snd G.hom G.hom) (v₁₃ := G.hom) (h₂₂ := G.hom) ?_
      l₁ (IsPullback.of_hasPullback G.hom G.hom).flip
    rw [l₂, h.1.w]
    exact big
  exact h₁.paste_vert h.1

theorem pushPt_comp (h : IsGrpPullback A G j a) {u' : A ⟶ A} {u : G ⟶ G} (e : a ≫ u.left = u'.left ≫ a)
    {T : Over U} (x : T ⟶ A) : pushPt h.1.w (x ≫ u') = pushPt h.1.w x ≫ u :=
  Over.OverMorphism.ext (by
    show (x.left ≫ _) ≫ _ = (x.left ≫ _) ≫ _
    rw [Category.assoc, ← e, Category.assoc])

variable [IsCommMonObj G] [IsCommMonObj A]

theorem lbIso_cube (h : IsGrpPullback A G j a) {L : LB G.left} {LA : LB A.left} (hL : L.IsLB) (hLA : LA.IsLB)
    (hb : LBIso LA (L.pull a)) {T : Over S} {T' : Over U} {n : ℕ} (x : Fin n → (T ⟶ G)) (x' : Fin n → (T' ⟶ A))
    (V : Over.mk (T'.hom ≫ j) ⟶ T) (hx : ∀ i, pushPt h.1.w (x' i) = V ≫ x i) :
    LBIso (cubeLB A x' LA) ((cubeLB G x L).pull V.left) :=
  LBIso.trans (DVR.linComb_isLB _ hLA _ _) (DVR.linComb_isLB _ (pull_isLB hL a) _ _)
    (pull_isLB (DVR.linComb_isLB _ hL _ _) _) (GlobalTheory.PowPrimitive.lbIso_linComb hb _ _)
    (LBIso.chartPull (chartPullLinComb L a _ _ _ V.left fun I => psum_push h _ _ V hx I.down)
      (Geo.Tor.chartPullPull _ V.left V.left rfl) (lbIso_refl (DVR.linComb_isLB _ hL _ _)))

theorem lbIso_sym (h : IsGrpPullback A G j a) {L : LB G.left} {LA : LB A.left} (hL : L.IsLB) (hLA : LA.IsLB)
    (hb : LBIso LA (L.pull a)) {w wd : G ⟶ G} {w' wd' : A ⟶ A}
    (pa : ∀ {T : Over U} (x : T ⟶ A), pushPt h.1.w (x ≫ w') = pushPt h.1.w x ≫ w)
    (pd : ∀ {T : Over U} (x : T ⟶ A), pushPt h.1.w (x ≫ wd') = pushPt h.1.w x ≫ wd) :
    LBIso (cubeLB A ![𝟙 A, w'] LA) ((cubeLB G ![𝟙 G, w] L).pull a) ∧
    LBIso (cubeLB A ![fst A A ≫ w', snd A A] LA) ((cubeLB G ![fst G G ≫ w, snd G G] L).pull
      (lift (pushPt h.1.w (fst A A)) (pushPt h.1.w (snd A A))).left) ∧
    LBIso (cubeLB A ![fst A A, snd A A ≫ wd'] LA) ((cubeLB G ![fst G G, snd G G ≫ wd] L).pull
      (lift (pushPt h.1.w (fst A A)) (pushPt h.1.w (snd A A))).left) := by
  refine ⟨?_, lbIso_cube h hL hLA hb _ _ _ fun i => ?_, lbIso_cube h hL hLA hb _ _ _ fun i => ?_⟩
  · let V := pushPt h.1.w (𝟙 A)
    have hV : V.left = a := Category.id_comp _
    have c := lbIso_cube h hL hLA hb ![𝟙 G, w] ![𝟙 A, w'] V (fun i => by
      fin_cases i
      · simp [V]
      · exact (congrArg (pushPt h.1.w) (Category.id_comp _).symm).trans (pa _))
    rwa [hV] at c
  · fin_cases i
    · exact (pa _).trans (by simp)
    · simp
  · fin_cases i
    · simp
    · exact (pd _).trans (by simp)

theorem exists_forall_hypS : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [Field K] [Algebra R K] [IsFractionRing R K] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A] (φ : A.left ⟶ G.left) (L : LB G.left) (L₀ : LB A.left), IsAbelianScheme G → IsGrpPullback A G (spMap (algebraMap R K)) φ → L.IsLB → L₀.IsLB → LBIso L₀ (L.pull φ) → ∀ (w wd : G ⟶ G) (w₀ wd₀ : A ⟶ A), φ ≫ w.left = w₀.left ≫ φ → φ ≫ wd.left = wd₀.left ≫ φ → IsMonHom w₀ → IsMonHom wd₀ → w₀ * wd₀ = 𝟙 A → LBIso L₀ (cubeLB A ![𝟙 A, w₀] L₀) → LBIso (cubeLB A ![fst A A ≫ w₀, snd A A] L₀) (cubeLB A ![fst A A, snd A A ≫ wd₀] L₀) → ∃ a : R, a ≠ 0 ∧ ∀ (R' : Type) [CommRing R'] (g : R →+* R'), IsUnit (g a) → ∀ (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'] (π : G'.left ⟶ G.left) (L' : LB G'.left), IsGrpPullback G' G (spMap g) π → L'.IsLB → LBIso L' (L.pull π) → HypS G' L' := by
  intro R K _ _ _ _ _ _ G _ _ A _ _ φ L L₀ hG h hL hL₀ hb w wd w₀ wd₀ ew ewd hw₀ hwd₀ hs hp ha
  obtain ⟨_, _⟩ : QuasiCompact (spMap (algebraMap R K)) ∧ IsSchemeTheoreticallyDominant (spMap (algebraMap R K)) :=
    ExtUnique.spec_fractionRing R K
  have := hG.smooth
  have := hG.proper
  have hw : IsMonHom w := ExtUnique.isMonHom_of_isGrpPullback h h w₀ w ew.symm
  have hwd : IsMonHom wd := ExtUnique.isMonHom_of_isGrpPullback h h wd₀ wd ewd.symm
  have hsum : w * wd = 𝟙 G := by
    refine ExtUnique.over_hom_ext_of_isPullback h.1 ?_
    have b : pushPt h.1.w (w₀ * wd₀) = pushPt h.1.w w₀ * pushPt h.1.w wd₀ := map_mul (pushHom h A) _ _
    have c := pushPt_comp h ew (𝟙 A)
    have d := pushPt_comp h ewd (𝟙 A)
    rw [Category.id_comp] at c d
    rw [c, d, ← MonObj.comp_mul, hs] at b
    have e : 𝟙 A.left ≫ φ = (𝟙 A.left ≫ φ) ≫ (w * wd).left := congrArg (fun z => z.left) b
    simp only [Category.id_comp] at e
    simpa using e.symm
  have cl : ∀ {T : Over (Sp R)} (x : Fin 2 → (T ⟶ G)), (cubeLB G x L).IsLB := fun x => DVR.linComb_isLB _ hL _ _
  have cl₀ : ∀ {T : Over (Sp K)} (x : Fin 2 → (T ⟶ A)), (cubeLB A x L₀).IsLB := fun x => DVR.linComb_isLB _ hL₀ _ _
  obtain ⟨c₁, c₂, c₃⟩ := lbIso_sym h hL hL₀ hb (fun x => pushPt_comp h ew x) (fun x => pushPt_comp h ewd x)
  have : IsProper (G ⊗ G).hom := by
    change IsProper (pullback.fst G.hom G.hom ≫ G.hom)
    infer_instance
  obtain ⟨a₁, ha₁, H₁⟩ := GenSpread.exists_lbIso G.hom h.1 hL (cl _)
    (hb.symm.trans (pull_isLB hL _) hL₀ (pull_isLB (cl _) _) (hp.trans hL₀ (cl₀ _) (pull_isLB (cl _) _) c₁))
  obtain ⟨a₂, ha₂, H₂⟩ := GenSpread.exists_lbIso (G ⊗ G).hom (isPullback_square h) (cl _) (cl _)
    (c₂.symm.trans (pull_isLB (cl _) _) (cl₀ _) (pull_isLB (cl _) _)
      (ha.trans (cl₀ _) (cl₀ _) (pull_isLB (cl _) _) c₃))
  refine ⟨a₁ * a₂, mul_ne_zero ha₁ ha₂, fun R' _ g hg G' _ _ π L' h' hL' hb' => ?_⟩
  rw [map_mul, IsUnit.mul_iff] at hg
  obtain ⟨w', hw', pa⟩ := SymBaseChange.exists_endo h' w
  obtain ⟨wd', hwd', pd⟩ := SymBaseChange.exists_endo h' wd
  have cl' : ∀ {T : Over (Sp R')} (x : Fin 2 → (T ⟶ G')), (cubeLB G' x L').IsLB := fun x =>
    DVR.linComb_isLB _ hL' _ _
  obtain ⟨d₁, d₂, d₃⟩ := lbIso_sym h' hL hL' hb' pa pd
  refine ⟨w', wd', hw', hwd', ?_, ?_, ?_⟩
  · apply SymBaseChange.pushPt_injective h'
    have b : pushPt h'.1.w (w' * wd') = pushPt h'.1.w w' * pushPt h'.1.w wd' := map_mul (pushHom h' G') _ _
    have c := pa (𝟙 G')
    have d := pd (𝟙 G')
    rw [Category.id_comp] at c d
    rw [b, c, d, ← MonObj.comp_mul, hsum, Category.comp_id]
  · exact hb'.trans hL' (pull_isLB hL _) (cl' _)
      ((H₁ R' g hg.1 _ π G'.hom h'.1.w).trans (pull_isLB hL _) (pull_isLB (cl _) _) (cl' _) d₁.symm)
  · exact d₂.trans (cl' _) (pull_isLB (cl _) _) (cl' _)
      ((H₂ R' g hg.2 _ _ (G' ⊗ G').hom (isPullback_square h').w).trans (pull_isLB (cl _) _) (pull_isLB (cl _) _)
        (cl' _) d₃.symm)

end GlobalTheory.SymSpread
