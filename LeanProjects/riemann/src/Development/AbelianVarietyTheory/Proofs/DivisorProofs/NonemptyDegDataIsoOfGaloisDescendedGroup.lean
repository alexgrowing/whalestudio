import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisInvariantFunctionsFlatBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisDescentInvariantMorphismFlatExistsUniqueStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPullbackUniformisationOfLineBundleIsoStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationDegenerationDataUnique
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsIsoOfIsClosedImmersionOfThickeningsOfIsProper
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsPullFOfGenRel
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIsPullDegOfVal
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PolarisedAVIsoDescendsOfRationalThreeTorsion
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.DataDescent

open GlobalTheory.ArcPull
open GlobalTheory.PsiEvenPull (proj)

theorem unit_ext_pull {Y Y' : Scheme.{0}} (κ : Y' ⟶ Y) {V : Y.Opens} (hκ : Function.Injective (κ.app V).hom)
    {a b : Γ(Y, V)ˣ} (h : ∀ y, κ y ∈ V → gm κ y V a = gm κ y V b) : a = b := by
  have : pullU κ V a = pullU κ V b := unit_ext fun y hy => by
    refine (gm_pull (𝟙 Y') κ y _ hy _).trans (Eq.trans ?_ (gm_pull (𝟙 Y') κ y _ hy _).symm)
    rw [Category.id_comp]
    exact h y hy
  exact Units.ext (hκ (congrArg Units.val this))

theorem pmaps_of_val_pull {X X' Y Y' Y'' : Scheme.{0}} {L : LB X} {L' : LB X'} {Φ : X' ⟶ X} {K : Type} [Fintype K]
    {w : LB.Iso L' (L.pull Φ)} (hw : PGen w) (hL : L.IsLB) (hL' : L'.IsLB) {φ' : K → (Y' ⟶ X')}
    {φ : K → (Y ⟶ X)} {ε : K → ℤ} {h : Y' ⟶ Y} (hψ : ∀ k, φ' k ≫ Φ = h ≫ φ k)
    {a : LB.Gen (LB.LinComb L' φ' ε)} (ha : a.IsGen) {t : LB.Gen (LB.LinComb L φ ε)} (ht : t.IsGen)
    (κ : Y'' ⟶ Y') (hκ : ∀ V, Function.Injective (κ.app V).hom)
    (H : ∀ (y : Y'') J J', Good L y J → Good L' y J' →
      val t (κ ≫ h) y J = (∏ k, om w y J J' (κ ≫ φ' k) ^ ε k) * val a κ y J') :
    PMaps w φ' φ ε a t h := by
  obtain ⟨a₁, ha₁, H₁⟩ := DegPull.exists_pmaps hw hL hL' h hψ t ht
  have e : ∀ j, a₁.s j = a.s j := fun j => unit_ext_pull κ (hκ _) fun y hy => by
    obtain ⟨J, hJ⟩ := DegPull.exists_good' hL y
    obtain ⟨J', hJ'⟩ := DegPull.exists_good' hL' y
    have v₀ := pmaps_om hψ H₁ κ y hJ hJ'
    have v : val a₁ κ y J' = val a κ y J' := mul_left_cancel (v₀.symm.trans (H y J J' hJ hJ'))
    exact (gen_trans ha₁ κ y hy (hJ'.mem _ _)).trans ((congrArg _ v).trans
      (gen_trans ha κ y hy (hJ'.mem _ _)).symm)
  intro Z r z p q hp hq
  exact (H₁ Z r z p q hp hq).trans (congrArg₂ (· * ·) rfl (congrArg (gm r z (LB.wchart L' φ' q)) (e q)))

section Bundle

variable {X Y Y' S : Scheme.{0}} {M : LB X} {L : LB Y} {L' : LB Y'} {f : Y ⟶ X} {β : Y' ⟶ Y}

abbrev ch (M : LB X) (L : LB Y) (f : Y ⟶ X) (j : M.ι) (i : L.ι) : Y.Opens := (M.pull f).U (fun _ => j) ⊓ L.U i

theorem exists_quot (hM : M.IsLB) (hL : L.IsLB) (hL' : L'.IsLB) {w : LB.Iso L' (L.pull β)}
    {w₁ : LB.Iso L' (M.pull (β ≫ f))} (hw : PGen w) (hw₁ : PGen w₁) (j : M.ι) (i : L.ι) :
    ∃ u : Γ(Y', β ⁻¹ᵁ ch M L f j i)ˣ, ∀ (Z : Scheme.{0}) (g : Z ⟶ Y') (z : Z) (k : L'.ι), β (g z) ∈ ch M L f j i →
      g z ∈ L'.U k → gm g z _ u = gw w₁ g z j k * (gw w g z i k)⁻¹ := by
  let W : L'.ι → Y'.Opens := fun k => β ⁻¹ᵁ ch M L f j i ⊓ L'.U k
  have l₁ : ∀ k, W k ≤ (M.pull (β ≫ f)).U (fun _ => j) ⊓ L'.U k := fun k x hx =>
    ⟨mem_pull₂.2 (mem_pull.1 hx.1.1), hx.2⟩
  have l₂ : ∀ k, W k ≤ (L.pull β).U (fun _ => i) ⊓ L'.U k := fun k x hx => ⟨mem_pull.2 hx.1.2, hx.2⟩
  obtain ⟨u, hu⟩ : ∃ u : ∀ k, Γ(Y', W k)ˣ, ∀ (Z : Scheme.{0}) (g : Z ⟶ Y') (z : Z) (k : L'.ι), g z ∈ W k →
      gm g z (W k) (u k) = gw w₁ g z j k * (gw w g z i k)⁻¹ :=
    ⟨fun k => res (l₁ k) (w₁.s (fun _ => j, k)) * (res (l₂ k) (w.s (fun _ => i, k)))⁻¹, fun Z g z k hz =>
      (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res g z (l₁ k) hz _)
        ((map_inv _ _).trans (congrArg (·⁻¹) (gm_res g z (l₂ k) hz _))))⟩
  obtain ⟨s, hs⟩ := glue_unit _ W (fun _ => inf_le_left) (fun x hx => by
      obtain ⟨k, hk⟩ := exists_chart hL' x
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨k, hx, hk⟩) u (fun k k' x hx => by
      have mj : (β ≫ f) ((𝟙 Y' : Y' ⟶ Y') x) ∈ M.U j := mem_pull.1 hx.1.1.1
      have mi : β ((𝟙 Y' : Y' ⟶ Y') x) ∈ L.U i := hx.1.1.2
      rw [hu _ _ x k hx.1, hu _ _ x k' hx.2, hw₁ _ _ x j j k k' mj mj hx.1.2 hx.2.2, hw _ _ x i i k k' mi mi hx.1.2 hx.2.2,
        gm_self hM (𝟙 Y' ≫ β ≫ f) x mj, gm_self hL (𝟙 Y' ≫ β) x mi]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel)
  refine ⟨s, fun Z g z k h₁ h₂ => ?_⟩
  have hz : g z ∈ W k := ⟨h₁, h₂⟩
  exact (gm_res g z inf_le_left hz s).symm.trans ((congrArg (gm g z (W k)) (hs k)).trans (hu Z g z k hz))

theorem exists_descent (hM : M.IsLB) (hL : L.IsLB) (hL' : L'.IsLB) {w : LB.Iso L' (L.pull β)}
    {w₁ : LB.Iso L' (M.pull (β ≫ f))} (hw : PGen w) (hw₁ : PGen w₁) {Γ' : Type} (act : Γ' → (Y' ⟶ Y'))
    (hact : ∀ σ, act σ ≫ β = β)
    (hfun : ∀ V : Y.Opens, Function.Injective (β.app V).hom ∧ ∀ u : Γ(Y', β ⁻¹ᵁ V),
      (∀ σ (h : β ⁻¹ᵁ V ≤ act σ ⁻¹ᵁ (β ⁻¹ᵁ V)), ((act σ).appLE _ _ h).hom u = u) → u ∈ Set.range (β.app V).hom)
    (p : Y' ⟶ S) (e : S ⟶ Y') (he : e ≫ p = 𝟙 _) (hp : Function.Surjective p.appTop.hom)
    (h₀ : ∀ σ (y : S) j i k k', β (e y) ∈ ch M L f j i → e y ∈ L'.U k → (e ≫ act σ) y ∈ L'.U k' →
      gw w₁ (e ≫ act σ) y j k' * (gw w (e ≫ act σ) y i k')⁻¹ = gw w₁ e y j k * (gw w e y i k)⁻¹) :
    ∃ v : LB.Iso L (M.pull f), PGen v ∧ Tri v w w₁ := by
  choose u hu using exists_quot hM hL hL' hw hw₁
  have tr : ∀ (Z : Scheme.{0}) (g : Z ⟶ Y') (z : Z) j j' i i', β (g z) ∈ ch M L f j i → β (g z) ∈ ch M L f j' i' →
      gm g z _ (u j i) = gm ((g ≫ β) ≫ f) z _ (M.g j j') * (gm (g ≫ β) z _ (L.g i i'))⁻¹ * gm g z _ (u j' i') := by
    intro Z g z j j' i i' h h'
    obtain ⟨k, hk⟩ := exists_chart hL' (g z)
    rw [hu j i Z g z k h hk, hu j' i' Z g z k h' hk,
      hw₁ Z g z j j' k k (mem_pull.1 h.1) (mem_pull.1 h'.1) hk hk, hw Z g z i i' k k h.2 h'.2 hk hk, Category.assoc]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  have pt : ∀ σ x, β (act σ x) = β x := fun σ x => congrArg (fun q => q x) (hact σ)
  have le : ∀ σ (V : Y.Opens), β ⁻¹ᵁ V ≤ act σ ⁻¹ᵁ (β ⁻¹ᵁ V) := fun σ V x hx => by
    show β (act σ x) ∈ V
    rw [pt]; exact hx
  have inv : ∀ σ j i, res (le σ _) (pullU (act σ) _ (u j i)) = u j i := by
    intro σ
    let r : ∀ q : M.ι × L.ι, Γ(Y', β ⁻¹ᵁ ch M L f q.1 q.2)ˣ := fun q =>
      res (le σ _) (pullU (act σ) _ (u q.1 q.2)) * (u q.1 q.2)⁻¹
    have hr : ∀ (Z : Scheme.{0}) (g : Z ⟶ Y') (z : Z) q, β (g z) ∈ ch M L f q.1 q.2 →
        gm g z _ (r q) = gm (g ≫ act σ) z _ (u q.1 q.2) * (gm g z _ (u q.1 q.2))⁻¹ := fun Z g z q h =>
      (map_mul _ _ _).trans (congrArg₂ (· * ·) ((gm_res g z _ h _).trans (gm_pull g (act σ) z (β ⁻¹ᵁ ch M L f q.1 q.2) (le σ (ch M L f q.1 q.2) h) _))
        (map_inv _ _))
    obtain ⟨s, hs⟩ := glue_unit ⊤ (fun q : M.ι × L.ι => β ⁻¹ᵁ ch M L f q.1 q.2) (fun _ => le_top) (fun x _ => by
        obtain ⟨j, hj⟩ := exists_chart hM (f (β x))
        obtain ⟨i, hi⟩ := exists_chart hL (β x)
        exact TopologicalSpace.Opens.mem_iSup.2 ⟨(j, i), mem_pull.2 hj, hi⟩) r (fun q q' x hx => by
        rw [hr _ (𝟙 _) x q hx.1, hr _ (𝟙 _) x q' hx.2, tr _ (𝟙 _ ≫ act σ) x q.1 q'.1 q.2 q'.2
            (le σ (ch M L f q.1 q.2) hx.1) (le σ (ch M L f q'.1 q'.2) hx.2),
          tr _ (𝟙 _) x q.1 q'.1 q.2 q'.2 hx.1 hx.2, Category.assoc (𝟙 _) (act σ), hact]
        apply Additive.ofMul.injective
        simp only [ofMul_mul, ofMul_inv]
        abel)
    obtain ⟨a, ha⟩ := hp s.val
    have a1 : a = 1 := fn_ext fun y _ => by
      obtain ⟨j, hj⟩ := exists_chart hM (f (β (e y)))
      obtain ⟨i, hi⟩ := exists_chart hL (β (e y))
      obtain ⟨k, hk⟩ := exists_chart hL' (e y)
      obtain ⟨k', hk'⟩ := exists_chart hL' ((e ≫ act σ) y)
      have m : β (e y) ∈ ch M L f j i := ⟨mem_pull.2 hj, hi⟩
      have one : gm e y ⊤ s = 1 := by
        refine (gm_res e y le_top m s).symm.trans ((congrArg (gm e y _) (hs (j, i))).trans ((hr _ e y (j, i) m).trans ?_))
        rw [hu j i _ (e ≫ act σ) y k' (le σ (ch M L f j i) m) hk', hu j i _ _ y k m hk, h₀ σ y j i k k' m hk hk', mul_inv_cancel]
      have := (gs_pull e p y ⊤ trivial a).symm.trans ((congrArg (gs e y ⊤) ha).trans
        ((gs_unit e y ⊤ trivial s).trans (congrArg Units.val one)))
      rw [he] at this
      rw [this, gs_eq _ y ⊤ trivial, map_one, map_one, Units.val_one]
    have s1 : s = 1 := Units.ext (ha.symm.trans ((congrArg _ a1).trans (map_one _)))
    intro j i
    exact mul_inv_eq_one.1 ((hs (j, i)).symm.trans ((congrArg _ s1).trans (map_one _)))
  have desc : ∀ j i, ∃ v : Γ(Y, ch M L f j i)ˣ, pullU β _ v = u j i := by
    intro j i
    obtain ⟨a, ha⟩ := (hfun _).2 (u j i).val fun σ _ => congrArg Units.val (inv σ j i)
    obtain ⟨b, hb⟩ := (hfun _).2 (u j i)⁻¹.val fun σ _ => congrArg Units.val
      (show res (le σ _) (pullU (act σ) _ (u j i)⁻¹) = (u j i)⁻¹ by rw [map_inv, map_inv, inv])
    have hab : a * b = 1 := (hfun _).1 (by rw [map_mul, ha, hb, map_one, Units.mul_inv])
    exact ⟨⟨a, b, hab, (mul_comm _ _).trans hab⟩, Units.ext ha⟩
  choose v hv using desc
  have gv : ∀ (Z : Scheme.{0}) (g : Z ⟶ Y') (z : Z) j i, β (g z) ∈ ch M L f j i →
      gm (g ≫ β) z _ (v j i) = gm g z _ (u j i) := fun Z g z j i h =>
    (gm_pull g β z _ h _).symm.trans (congrArg (gm g z _) (hv j i))
  refine ⟨⟨fun q => v (q.1 PUnit.unit) q.2⟩, (isGen_iff _).1 ?_, fun Z g z j i k hj hi hk => ?_⟩
  · rintro ⟨J, i⟩ ⟨J', i'⟩
    refine unit_ext_pull β (hfun _).1 fun x hx => ?_
    have a := gv _ (𝟙 _) x (J PUnit.unit) i hx.1
    have a' := gv _ (𝟙 _) x (J' PUnit.unit) i' hx.2
    have t := tr _ (𝟙 _) x (J PUnit.unit) (J' PUnit.unit) i i' hx.1 hx.2
    rw [← a, ← a', Category.id_comp,
      ← gm_div_g β x (J PUnit.unit) (J' PUnit.unit) i i' (mem_pull.1 hx.1.1) (mem_pull.1 hx.2.1) hx.1.2 hx.2.2] at t
    exact (gm_res _ x _ hx _).trans (t.trans ((map_mul _ _ _).trans (congrArg _ (gm_res _ x _ hx _))).symm)
  · have m : β (g z) ∈ ch M L f j i := ⟨mem_pull.2 hj, hi⟩
    exact (inv_mul_cancel_right _ _).symm.trans
      (congrArg (· * gw w g z i k) ((gv Z g z j i m).trans (hu j i Z g z k m hk)).symm)

end Bundle

theorem tri_om {X X' X'' Z : Scheme.{0}} {L : LB X} {L' : LB X'} {L'' : LB X''} {F : X' ⟶ X} {F' : X'' ⟶ X'}
    {w : LB.Iso L' (L.pull F)} {w' : LB.Iso L'' (L'.pull F')} {w'' : LB.Iso L'' (L.pull (F' ≫ F))} (T : Tri w w' w'')
    {z : Z} {J J' J''} (hJ : Good L z J) (hJ' : Good L' z J') (hJ'' : Good L'' z J'') (x : Z ⟶ X'') :
    om w'' z J J'' x = om w z J J' (x ≫ F') * om w' z J' J'' x :=
  (congrArg (fun u => gw w'' x z (J u) (J'' x)) (Category.assoc x F' F).symm).trans
    (T _ _ z _ _ _ (hJ ((x ≫ F') ≫ F)) (hJ' (x ≫ F')) (hJ'' _))

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] [IsLocalRing R'] {ρ : R →+* R'}

omit [IsDomain R] [IsDomain R'] [IsLocalRing R'] in

theorem spMap_gal (σ : Gal ρ) : spMap (Gal.hom σ) ≫ spMap ρ = spMap ρ :=
  (spMap_comp ρ (Gal.hom σ)).symm.trans (congrArg spMap (RingHom.ext σ.2))

theorem cancel_of_gal (hρ : FinExt ρ) (hG : IsGal ρ) {Y Y' : Scheme.{0}} {y : Y ⟶ Sp R} {y' : Y' ⟶ Sp R'} {β : Y' ⟶ Y}
    (hy : Flat y) (pb : IsPullback β y' y (spMap ρ)) {W : Scheme.{0}} {g g' : Y ⟶ W} (h : β ≫ g = β ≫ g') : g = g' := by
  let act : Gal ρ → (Y' ⟶ Y') := fun σ => pb.lift β (y' ≫ spMap (Gal.hom σ)) (by rw [Category.assoc, spMap_gal, pb.w])
  have a : ∀ σ, act σ ≫ β = β := fun σ => pb.lift_fst _ _ _
  exact (GlobalTheory.T.galoisDescent_invariant_morphism_flat_existsUnique R R' ρ hρ hG Y Y' y y' β hy pb act a (fun σ => pb.lift_snd _ _ _) W (β ≫ g')
    (fun σ => by rw [← Category.assoc, a])).unique h rfl

theorem nonempty_isPullDeg (hρ : FinExt ρ) (hG : IsGal ρ) {D D₁ : DegPre R} (hB : D₁.TauBimult) {D' : DegPre R'}
    (hD : IsPullDeg ρ D D') (h₁ : IsPullDeg ρ D₁ D') (act : Gal ρ → (D'.P.A.left ⟶ D'.P.A.left))
    (a₀ : ∀ σ, act σ ≫ D'.P.A.hom = D'.P.A.hom ≫ spMap (Gal.hom σ)) (a : ∀ σ, act σ ≫ proj hD = proj hD)
    (a₁ : ∀ σ, act σ ≫ proj h₁ = proj h₁) : Nonempty (IsPullDeg (RingHom.id R) D₁ D) := by
  have hL := GlobalTheory.abelianSchemeLaws_all.1
  have hi := hρ.2.1
  have fl : Flat D.P.A.hom := by have := D.P.smoothDim; have : Smooth D.P.A.hom := SmoothOfRelativeDimension.smooth D.P.g _; infer_instance
  have fl₁ : Flat D₁.P.A.hom := by have := D₁.P.smoothDim; have : Smooth D₁.P.A.hom := SmoothOfRelativeDimension.smooth D₁.P.g _; infer_instance
  have pb : IsPullback (proj hD) D'.P.A.hom D.P.A.hom (spMap ρ) := (pull_grp hD).1
  have pb₁ : IsPullback (proj h₁) D'.P.A.hom D₁.P.A.hom (spMap ρ) := (pull_grp h₁).1
  have pb₀ : IsPullback (spMap ρ) (𝟙 _) (𝟙 _) (spMap ρ) := IsPullback.id_vert _
  obtain ⟨f, hf, -⟩ := GlobalTheory.T.galoisDescent_invariant_morphism_flat_existsUnique R R' ρ hρ hG _ _ _ _ _ fl pb act a a₀ _ (proj h₁) a₁
  obtain ⟨g, hg, -⟩ := GlobalTheory.T.galoisDescent_invariant_morphism_flat_existsUnique R R' ρ hρ hG _ _ _ _ _ fl₁ pb₁ act a₁ a₀ _ (proj hD) a
  replace hf : proj hD ≫ f = proj h₁ := hf
  replace hg : proj h₁ ≫ g = proj hD := hg
  have : IsIso f := ⟨g, cancel_of_gal hρ hG fl pb (by rw [← Category.assoc, hf, hg, Category.comp_id]),
    cancel_of_gal hρ hG fl₁ pb₁ (by rw [← Category.assoc, hg, hf, Category.comp_id])⟩
  have hs := specOf_id R
  have fo : f ≫ D₁.P.A.hom = D.P.A.hom := cancel_of_gal hρ hG fl pb (by rw [← Category.assoc, hf, pb.w, pb₁.w])
  have pf : IsPullback f D.P.A.hom D₁.P.A.hom (specOf (RingHom.id R)) := by
    rw [hs]; exact IsPullback.of_horiz_isIso ⟨fo.trans (Category.comp_id _).symm⟩
  have sec : ∀ {s : Sp R ⟶ D.P.A.left} {s₁ : Sp R ⟶ D₁.P.A.left} {s' : Sp R' ⟶ D'.P.A.left},
      s' ≫ proj hD = spMap ρ ≫ s → s' ≫ proj h₁ = spMap ρ ≫ s₁ → s ≫ f = s₁ := fun {s s₁ s'} h h' =>
    cancel_of_gal hρ hG inferInstance pb₀ (by rw [← Category.assoc, ← h, Category.assoc, hf, h'])
  have hE : eSec D.P.A ≫ f = eSec D₁.P.A := sec hD.he h₁.he
  let xe : D.X ≃+ D₁.X := hD.xe.symm.trans h₁.xe
  have hc : ∀ x, (D.c x).left ≫ f = (D₁.c (xe x)).left := fun x =>
    sec ((hD.c_pr (hD.xe.symm x)).trans (by rw [AddEquiv.apply_symm_apply])) (h₁.c_pr (hD.xe.symm x))
  have gp := PolIsoDescent.isGrpPullback_of_one hL D₁.P.isAb D.P.isAb pf
    (hE.trans (by rw [hs]; exact (Category.id_comp _).symm))
  obtain ⟨e, me, he⟩ := grpPullback_iso gp (isGrpPullback_pullback D₁.P.A (specOf (RingHom.id R)))
  obtain ⟨w₁, g₁, r₁, ψ₁⟩ := UnifUniq.exists_transport hf (fun (F : D'.P.A.left ⟶ D₁.P.A.left)
    (w : LB.Iso D'.P.L (D₁.P.L.pull F)) => PGen w ∧
      PMaps w (K := PUnit) (fun _ => eSec D'.P.A) (fun _ => eSec D₁.P.A) (fun _ => 1) D'.rig D₁.rig (spMap ρ) ∧
      ∀ x (z : (TK R').left) J J', Good D₁.P.L z J → Good D'.P.L z J' → val (D₁.psi (h₁.xe x)) (genMap hi) z J =
        (om w z J J' (𝟙 _ ≫ D'.xK x))⁻¹ * val (D'.psi x) (𝟙 _) z J') h₁.w
    ⟨(isGen_iff _).1 h₁.w_gen, FieldPull.pmaps_rig h₁, fun x z J J' hJ hJ' => psi_val h₁ _ _ (fracMap_sq hi) hJ hJ' x⟩
  have g₀ := (isGen_iff _).1 hD.w_gen
  have r₀ := FieldPull.pmaps_rig hD
  have ea : ∀ σ, eSec D'.P.A ≫ act σ = spMap (Gal.hom σ) ≫ eSec D'.P.A := fun σ => pb.hom_ext
    (by
      rw [Category.assoc, a, Category.assoc]
      exact hD.he.trans ((congrArg (· ≫ _) (spMap_gal σ).symm).trans ((Category.assoc _ _ _).trans
        (congrArg (_ ≫ ·) hD.he.symm))))
    (by
      have o : eSec D'.P.A ≫ D'.P.A.hom = 𝟙 _ := Over.w η[D'.P.A]
      rw [Category.assoc, a₀, reassoc_of% o, Category.assoc, o]
      exact (Category.comp_id _).symm)
  obtain ⟨v, gv, T⟩ := exists_descent D₁.P.isLB D.P.isLB D'.P.isLB g₀ g₁ act a
    (GlobalTheory.Mum.InvFun.invariant_functions R R' ρ hρ hG _ _ _ _ _ fl pb act a a₀) D'.P.A.hom (eSec D'.P.A) (Over.w η[D'.P.A])
    (hL.globalFns _ _ D'.P.isAb).2 (fun σ y j i k k' m hk hk' => by
      have key : ∀ (r : Sp R' ⟶ Sp R') (k : D'.P.L.ι), r ≫ spMap ρ = spMap ρ → (r ≫ eSec D'.P.A) y ∈ D'.P.L.U k →
          gw w₁ (r ≫ eSec D'.P.A) y j k * (gw hD.w (r ≫ eSec D'.P.A) y i k)⁻¹ =
            gm (spMap ρ) y _ (D₁.rig.s fun _ => j) * (gm (spMap ρ) y _ (D.rig.s fun _ => i))⁻¹ := by
        intro r k hr hk
        have q : proj hD (eSec D'.P.A (r y)) = proj hD (eSec D'.P.A y) :=
          congrArg (fun q : Sp R' ⟶ D.P.A.left => q y) (show r ≫ eSec D'.P.A ≫ proj hD = eSec D'.P.A ≫ proj hD from
            (congrArg (r ≫ ·) hD.he).trans ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) hr).trans hD.he.symm)))
        have u₀ := r₀ _ r y (fun _ => i) (fun _ => k) (fun _ => by rw [q]; exact m.2) (fun _ => hk)
        have u₁ := r₁ _ r y (fun _ => j) (fun _ => k) (fun _ => by
          show f (proj hD (eSec D'.P.A (r y))) ∈ _
          rw [q]; exact mem_pull.1 m.1) (fun _ => hk)
        rw [hr, Fintype.prod_unique, zpow_one] at u₀ u₁
        refine Eq.trans ?_ (congrArg₂ (fun a b => a * b⁻¹) u₁.symm u₀.symm)
        apply Additive.ofMul.injective
        simp only [ofMul_mul, ofMul_inv]
        abel
      have k₁ := key (𝟙 _) k (Category.id_comp _) hk
      rw [Category.id_comp] at k₁
      rw [ea] at hk' ⊢
      exact (key _ k' (spMap_gal σ) hk').trans k₁.symm)
  have hf' : eSec D'.P.A ≫ proj hD ≫ f = spMap ρ ≫ eSec D₁.P.A := (congrArg (_ ≫ ·) hf).trans h₁.he
  have rv : PMaps v (K := PUnit) (fun _ => eSec D.P.A) (fun _ => eSec D₁.P.A) (fun _ => 1) D.rig D₁.rig (𝟙 _) :=
    pmaps_of_val_pull gv D₁.P.isLB D.P.isLB (fun _ => hE.trans (Category.id_comp _).symm) D.rig_gen D₁.rig_gen (spMap ρ)
      (fun V => (GlobalTheory.Mum.InvFun.invariant_functions R R' ρ hρ hG _ _ _ _ _ inferInstance pb₀ (fun σ => spMap (Gal.hom σ)) spMap_gal
        (fun σ => (Category.comp_id _).trans (Category.id_comp _).symm) V).1) fun y J₁ J hJ₁ hJ => by
      obtain ⟨J', hJ'⟩ := DegPull.exists_good' D'.P.isLB y
      have u₀ := pmaps_om (fun _ => hD.he) r₀ (𝟙 _) y hJ hJ'
      have u₁ := pmaps_om (fun _ => hf') r₁ (𝟙 _) y hJ₁ hJ'
      have t := tri_om T hJ₁ hJ hJ' (eSec D'.P.A)
      simp only [Category.id_comp, Category.comp_id, Fintype.prod_unique, zpow_one] at u₀ u₁ ⊢
      refine u₁.trans (((congrArg₂ (· * ·) t rfl).trans (_root_.mul_assoc _ _ _)).trans (congrArg₂ (· * ·) ?_ u₀.symm))
      exact congrArg (om v y J₁ J) hD.he
  have gi : ∀ V, Function.Injective ((genMap hi).app V).hom := fun V => by
    have : IsDominant (spMap (fracMap hi)) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2
      (((RingHom.injective_iff_ker_eq_bot _).1 (fracMap hi).injective).le.trans bot_le)⟩
    have := IsSchemeTheoreticallyDominant.of_isDominant (spMap (fracMap hi))
    exact (spMap (fracMap hi)).app_injective V
  have ψv : ∀ x, PMaps v (K := PUnit) (fun _ => D.xK x) (fun _ => D₁.xK (xe x)) (fun _ => -1) (D.psi x)
      (D₁.psi (xe x)) (𝟙 _) := fun x => by
    obtain ⟨x, rfl⟩ := hD.xe.surjective x
    have ex : xe (hD.xe x) = h₁.xe x := congrArg h₁.xe (hD.xe.symm_apply_apply x)
    refine pmaps_of_val_pull gv D₁.P.isLB D.P.isLB (fun _ => ?_) (D.psi_gen _) (D₁.psi_gen _) (genMap hi) gi
      fun y J₁ J hJ₁ hJ => ?_
    · exact (Category.assoc _ _ _).trans ((congrArg (jK R ≫ ·) (hc _)).trans (Category.id_comp _).symm)
    · obtain ⟨J', hJ'⟩ := DegPull.exists_good' D'.P.isLB y
      have u₀ := psi_val hD _ _ (fracMap_sq hi) hJ hJ' x
      have u₁ := ψ₁ x y J₁ J' hJ₁ hJ'
      have t := tri_om T hJ₁ hJ hJ' (𝟙 _ ≫ D'.xK x)
      have hx : (𝟙 _ ≫ D'.xK x) ≫ proj hD = genMap hi ≫ D.xK (hD.xe x) := by
        show (𝟙 _ ≫ jK R' ≫ (D'.c x).left) ≫ proj hD = genMap hi ≫ jK R ≫ (D.c (hD.xe x)).left
        exact (Category.assoc _ _ _).trans ((congrArg (𝟙 _ ≫ ·) ((Category.assoc _ _ _).trans
          ((congrArg (jK R' ≫ ·) (hD.c_pr x)).trans (Category.assoc _ _ _).symm))).trans
          ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) (fracMap_sq hi)).trans (Category.assoc _ _ _))))
      rw [t, hx, mul_inv, _root_.mul_assoc, ← u₀, ← ex] at u₁
      rw [Fintype.prod_unique, zpow_neg_one]
      exact (congrArg (fun q => val (D₁.psi (xe (hD.xe x))) q y J₁) (Category.comp_id _)).trans u₁
  subst he
  obtain ⟨W, hW, ⟨ψW⟩⟩ := PsiSpread.exists_psiOn D₁ hB
  obtain ⟨h, -⟩ := UnifUniq.exists_isPullDeg_id D₁ D W hW ψW e me v ((isGen_iff _).2 gv) hE rv xe hc ψv
  exact ⟨h⟩

end GlobalTheory.Mum.DataDescent

namespace GlobalTheory.Mum

open GlobalTheory.PsiEvenPull (proj)

theorem nonempty_isPullDeg_of_galAct : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), FinExt ρ → IsGal ρ → ∀ (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')) (hD : IsPullDeg ρ D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R') D' A' G'), ∀ (a : GalAct ρ hD U') (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (β : G'.left ⟶ G.left), IsSemiAbelian G → IsGrpPullback G' G (spMap ρ) β → (∀ σ, a.act σ ≫ β = β) → ∀ (A : PolAV (Sp (FractionRing R))) (D₁ : DegData R (maximalIdeal R)) (U₁ : Unif (maximalIdeal R) D₁ A G), LBIso U'.LG.L (U₁.LG.L.pull β) → Nonempty (IsPullDeg (RingHom.id R) D₁.toPre D.toPre) := by
  intro R _ _ _ hR R' _ _ _ ρ hρ hG D D' hD A' G' _ _ hs' U' a G _ _ β hs gp ha A D₁ U₁ hL
  obtain ⟨h₁, bc, hbc, ⟨_, -, _, -, K⟩⟩ := GlobalTheory.T.isPullbackUniformisation_of_lineBundle_iso R hR R' ρ hρ D' A' G' hs' U' G β hs gp A D₁ U₁ hL
  choose h b hb H P using a.unif
  have a₀ : ∀ σ, proj (h σ) ≫ D'.toPre.P.A.hom = D'.toPre.P.A.hom ≫ spMap (Gal.hom σ) := fun σ => (pull_grp (h σ)).1.w
  refine DataDescent.nonempty_isPullDeg hρ hG D₁.tau_bimult hD h₁ (fun σ => proj (h σ)) a₀
    (fun σ => (P σ).2 _ _ rfl rfl) fun σ => ?_
  have pb : IsPullback (proj h₁) D'.toPre.P.A.hom D₁.toPre.P.A.hom (spMap ρ) := (pull_grp h₁).1
  have w : (proj (h σ) ≫ proj h₁) ≫ D₁.toPre.P.A.hom = D'.toPre.P.A.hom ≫ spMap ρ := by
    rw [Category.assoc, pb.w, ← Category.assoc, a₀, Category.assoc, DataDescent.spMap_gal]
  let u : D'.toPre.P.A ⟶ D'.toPre.P.A := Over.homMk (pb.lift _ _ w) (pb.lift_snd _ _ _)
  have u₁ : u.left ≫ proj h₁ = proj (h σ) ≫ proj h₁ := pb.lift_fst _ _ _
  have := hρ.1.1
  have := D'.toPre.P.isAb.proper
  have hu : u = 𝟙 _ := GlobalTheory.hom_eq_of_thickenings_of_isProper R' (maximalIdeal R')
    (by rw [jacobson_eq_maximalIdeal ⊥ bot_ne_top]) _ _ u (𝟙 _) fun e => by
      obtain ⟨k, k₁, k₂, -⟩ := K e
      obtain ⟨_, -, _, -, K'⟩ := (H σ).lg
      obtain ⟨m, m₁, m₂, -⟩ := K' e
      rw [hbc] at k₁
      rw [hb] at m₁
      have : IsClosedImmersion (thick R (maximalIdeal R) e) :=
        IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
      have : Mono (fstG (maximalIdeal R) e G).left :=
        inferInstanceAs (Mono (pullback.fst G.hom (thick R (maximalIdeal R) e)))
      have mk : m ≫ k = k := by
        rw [← cancel_mono (fstG (maximalIdeal R) e G).left, Category.assoc, k₁, ← Category.assoc, m₁, Category.assoc, ha]
      have := (U'.gt e).q_flat
      have := (U'.gt e).q_surj
      have := Flat.epi_of_flat_of_surjective (U'.gt e).q.left
      refine pb.hom_ext ?_ ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) ((Over.w u).trans (Over.w (𝟙 D'.toPre.P.A)).symm)).trans
        (Category.assoc _ _ _).symm))
      rw [Category.assoc, u₁, Over.id_left, Category.comp_id]
      refine (cancel_epi (U'.gt e).q.left).1 ?_
      have q : (U'.gt e).q.left ≫ (fstG (maximalIdeal R') e D'.toPre.P.A).left = (U'.gt e).pG.left := rfl
      refine (Category.assoc _ _ _).symm.trans (Eq.trans ?_ (Category.assoc _ _ _))
      refine (congrArg (· ≫ _) q).trans (Eq.trans ?_ (congrArg (· ≫ _) q).symm)
      exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ proj h₁) m₂).trans ((Category.assoc _ _ _).trans
        ((congrArg (m ≫ ·) k₂).trans ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) mk).trans k₂.symm)))))
  rw [hu] at u₁
  exact u₁.symm.trans (Category.id_comp _)

end GlobalTheory.Mum
