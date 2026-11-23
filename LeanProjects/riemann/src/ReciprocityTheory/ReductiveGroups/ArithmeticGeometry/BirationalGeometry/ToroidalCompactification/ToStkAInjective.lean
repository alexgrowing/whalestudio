import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsIsoPairOfEq

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj

section Local

variable {A : Type} [CommRing A] {X : Scheme.{0}}

def toStkA (z : Sp A) : A →+* (Sp A).presheaf.stalk z :=
  ((Sp A).presheaf.germ ⊤ z trivial).hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom

abbrev cpt (A : Type) [CommRing A] [IsLocalRing A] : Sp A := IsLocalRing.closedPoint A

theorem top_le_iff_cpt [IsLocalRing A] (x : Sp A ⟶ X) (U : X.Opens) : ⊤ ≤ x ⁻¹ᵁ U ↔ x (cpt A) ∈ U := by
  constructor
  · intro h
    exact h (show cpt A ∈ (⊤ : (Sp A).Opens) from trivial)
  · intro h z _
    first
    | exact (IsLocalRing.specializes_closedPoint z).mem_open (x ⁻¹ᵁ U).isOpen h
    | exact ((PrimeSpectrum.le_iff_specializes z (cpt A)).mp
        (IsLocalRing.le_maximalIdeal z.isPrime.ne_top)).mem_open (x ⁻¹ᵁ U).isOpen h

theorem toStkA_valR (x : Sp A ⟶ X) (U : X.Opens) (z : Sp A) (ht : ⊤ ≤ x ⁻¹ᵁ U) (a : Γ(X, U)ˣ) :
    toStkA z (valR x U a.val) = (gm x z U a).val := by
  have hz : x z ∈ U := ht (show z ∈ (⊤ : (Sp A).Opens) from trivial)
  have e1 : ∀ c, (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom c) = c :=
    fun c => congrArg (fun f => CommRingCat.Hom.hom f c) (Iso.hom_inv_id (Scheme.ΓSpecIso (CommRingCat.of A)))
  rw [valR, dif_pos ht, gm, dif_pos hz]
  show ((Sp A).presheaf.germ ⊤ z trivial).hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom
      ((Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom ((x.appLE U ⊤ ht).hom a.val))) =
    ((Sp A).presheaf.germ (x ⁻¹ᵁ U) z hz).hom ((x.app U).hom a.val)
  rw [e1]
  exact TopCat.Presheaf.germ_res_apply (Sp A).presheaf (homOfLE ht) z trivial ((x.app U).hom a.val)

theorem toStkA_injective [IsLocalRing A] : Function.Injective (toStkA (cpt A)) := by
  have e := AlgebraicGeometry.ΓSpecIso_hom_stalkClosedPointIso_inv (CommRingCat.of A)
  have key : (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ (Sp A).presheaf.germ ⊤ (cpt A) trivial =
      (AlgebraicGeometry.stalkClosedPointIso (CommRingCat.of A)).inv := by
    rw [Iso.inv_comp_eq]; exact e.symm
  have h5 : ∀ c, (AlgebraicGeometry.stalkClosedPointIso (CommRingCat.of A)).hom.hom
      ((AlgebraicGeometry.stalkClosedPointIso (CommRingCat.of A)).inv.hom c) = c := fun c =>
    congrArg (fun f => CommRingCat.Hom.hom f c) (Iso.inv_hom_id (AlgebraicGeometry.stalkClosedPointIso (CommRingCat.of A)))
  intro a b hab
  have h2 : (AlgebraicGeometry.stalkClosedPointIso (CommRingCat.of A)).inv.hom a =
      (AlgebraicGeometry.stalkClosedPointIso (CommRingCat.of A)).inv.hom b := by
    rw [← key]; exact hab
  rw [← h5 a, ← h5 b, h2]

end Local

section GenR

variable {A : Type} [CommRing A] [IsLocalRing A]
variable {B B' B₀ : Scheme.{0}} {M : LB B} {M' : LB B'} {M₀ : LB B₀} {K : Type} [Fintype K] {ε : K → ℤ}

theorem genRelR_iff {φ : B ⟶ B₀} (w : LB.Iso M (M₀.pull φ)) {pt : K → (Sp A ⟶ B)} {pt₀ : K → (Sp A ⟶ B₀)}
    (t : LB.Gen (LB.LinComb M pt ε)) (t₀ : LB.Gen (LB.LinComb M₀ pt₀ ε)) :
    GenRelR w t t₀ ↔ (∀ k, pt k ≫ φ = pt₀ k) ∧ ∀ (j : K → M.ι) (j₀ : K → M₀.ι),
      (∀ k, φ (pt k (cpt A)) ∈ M₀.U (j₀ k)) → (∀ k, pt k (cpt A) ∈ M.U (j k)) →
      ((∏ k, gw w (pt k) (cpt A) (j₀ k) (j k) ^ ε k) * gm (𝟙 _) (cpt A) (LB.wchart M pt j) (t.s j)).val =
        (gm (𝟙 _) (cpt A) (LB.wchart M₀ pt₀ j₀) (t₀.s j₀)).val := by
  unfold GenRelR
  refine and_congr_right fun hpt => forall_congr' fun j => forall_congr' fun j₀ => ?_
  have hP_iff : (∀ k, ⊤ ≤ pt k ⁻¹ᵁ (LB.div (M₀.pull φ) M).U (fun _ => j₀ k, j k)) ↔
      (∀ k, φ (pt k (cpt A)) ∈ M₀.U (j₀ k)) ∧ (∀ k, pt k (cpt A) ∈ M.U (j k)) := by
    simp only [top_le_iff_cpt]
    exact ⟨fun h => ⟨fun k => Set.mem_iInter.1 (h k).1 PUnit.unit, fun k => (h k).2⟩,
      fun h k => ⟨Set.mem_iInter.2 fun _ => h.1 k, h.2 k⟩⟩
  rw [hP_iff, and_imp]
  refine forall_congr' fun h1 => forall_congr' fun h2 => ?_
  have hP : ∀ k, ⊤ ≤ pt k ⁻¹ᵁ (LB.div (M₀.pull φ) M).U (fun _ => j₀ k, j k) := hP_iff.2 ⟨h1, h2⟩
  have hT : ⊤ ≤ (𝟙 (Sp A)) ⁻¹ᵁ (LB.LinComb M pt ε).U j :=
    (top_le_iff_cpt _ _).2 (Set.mem_iInter.2 fun k => h2 k)
  have hT₀ : ⊤ ≤ (𝟙 (Sp A)) ⁻¹ᵁ (LB.LinComb M₀ pt₀ ε).U j₀ := by
    refine (top_le_iff_cpt _ _).2 (Set.mem_iInter.2 fun k => ?_)
    show pt₀ k ((𝟙 (Sp A)) (cpt A)) ∈ M₀.U (j₀ k)
    rw [← hpt k]
    exact h1 k
  have hW : ∀ k (u : Γ(B, (LB.div (M₀.pull φ) M).U (fun _ => j₀ k, j k))ˣ),
      toStkA (cpt A) (valR (pt k) _ u.val) = (gm (pt k) (cpt A) _ u).val :=
    fun k u => toStkA_valR _ _ _ (hP k) u
  rw [← (toStkA_injective (A := A)).eq_iff, map_mul, map_prod, toStkA_valR _ _ _ hT, toStkA_valR _ _ _ hT₀]
  simp only [hW, map_zpow]
  rw [← Units.coe_prod, ← Units.val_mul, Units.val_inj, Units.val_inj]
  simp only [zpow_neg, Finset.prod_inv_distrib]
  exact eq_inv_mul_iff_mul_eq

theorem genRelR_transfer {φ : B ⟶ B₀} {Φ : B' ⟶ B} {w : LB.Iso M (M₀.pull φ)} {wD : LB.Iso M' (M.pull Φ)}
    {w' : LB.Iso M' (M₀.pull (Φ ≫ φ))} (T : Tri w wD w') (hM : M.IsLB) (hM' : M'.IsLB) {pt : K → (Sp A ⟶ B)}
    {pt' : K → (Sp A ⟶ B')} {pt₀ : K → (Sp A ⟶ B₀)} (hc : ∀ k, pt' k ≫ Φ = 𝟙 _ ≫ pt k)
    {t : LB.Gen (LB.LinComb M pt ε)} {t' : LB.Gen (LB.LinComb M' pt' ε)} (H : PMaps wD pt' pt ε t' t (𝟙 _))
    (t₀ : LB.Gen (LB.LinComb M₀ pt₀ ε)) : GenRelR w t t₀ ↔ GenRelR w' t' t₀ := by
  have hc' : ∀ k, pt' k ≫ Φ = pt k := fun k => (hc k).trans (Category.id_comp _)
  have hcp : ∀ k, Φ (pt' k (cpt A)) = pt k (cpt A) := fun k => by rw [← hc' k]; rfl
  have A' : ∀ (j : K → M.ι) (i : K → M'.ι) (j₀ : K → M₀.ι), (∀ k, φ (pt k (cpt A)) ∈ M₀.U (j₀ k)) →
      (∀ k, pt k (cpt A) ∈ M.U (j k)) → (∀ k, pt' k (cpt A) ∈ M'.U (i k)) →
      (∏ k, gw w' (pt' k) (cpt A) (j₀ k) (i k) ^ ε k) * gm (𝟙 _) (cpt A) (LB.wchart M' pt' i) (t'.s i) =
        (∏ k, gw w (pt k) (cpt A) (j₀ k) (j k) ^ ε k) * gm (𝟙 _) (cpt A) (LB.wchart M pt j) (t.s j) := by
    intro j i j₀ h1 h2 h3
    have eT : ∀ k, gw w' (pt' k) (cpt A) (j₀ k) (i k) =
        gw w (pt k) (cpt A) (j₀ k) (j k) * gw wD (pt' k) (cpt A) (j k) (i k) := by
      intro k
      have e := T (Sp A) (pt' k) (cpt A) (j₀ k) (j k) (i k) (by rw [hcp k]; exact h1 k)
        (by rw [hcp k]; exact h2 k) (h3 k)
      rw [e, hc' k]
    have eH := H (Sp A) (𝟙 _) (cpt A) j i
      (fun k => by show Φ (pt' k (cpt A)) ∈ M.U (j k); rw [hcp k]; exact h2 k) (fun k => h3 k)
    simp only [Category.id_comp] at eH
    simp only [eT, mul_zpow, Finset.prod_mul_distrib]
    rw [eH, _root_.mul_assoc]
  rw [genRelR_iff, genRelR_iff]
  refine and_congr (by simp only [← Category.assoc, hc']) ⟨fun hyp i j₀ h1' h2' => ?_, fun hyp j j₀ h1 h2 => ?_⟩
  · have hj : ∀ k, ∃ a, pt k (cpt A) ∈ M.U a := fun k => by
      have hx : pt k (cpt A) ∈ ⨆ a, M.U a := by rw [hM.cover]; trivial
      exact TopologicalSpace.Opens.mem_iSup.1 hx
    choose j hj using hj
    have h1 : ∀ k, φ (pt k (cpt A)) ∈ M₀.U (j₀ k) := fun k => by rw [← hcp k]; exact h1' k
    rw [A' j i j₀ h1 hj h2']
    exact hyp j j₀ h1 hj
  · have hi : ∀ k, ∃ a, pt' k (cpt A) ∈ M'.U a := fun k => by
      have hx : pt' k (cpt A) ∈ ⨆ a, M'.U a := by rw [hM'.cover]; trivial
      exact TopologicalSpace.Opens.mem_iSup.1 hx
    choose i hi using hi
    have h1' : ∀ k, (Φ ≫ φ) (pt' k (cpt A)) ∈ M₀.U (j₀ k) := fun k => by
      show φ (Φ (pt' k (cpt A))) ∈ M₀.U (j₀ k)
      rw [hcp k]
      exact h1 k
    rw [← A' j i j₀ h1 h2 hi]
    exact hyp i j₀ h1' hi

end GenR

section Pulls

variable {X X' Y Y' Y'' : Scheme.{0}}

private theorem gm_pullU_eq_gm_comp {S T W : Scheme.{0}} (h : T ⟶ S) (r : W ⟶ T) (z : W) (V : S.Opens)
    (a : Γ(S, V)ˣ) : gm r z (h ⁻¹ᵁ V) (pullU h V a) = gm (r ≫ h) z V a := by
  by_cases hz : r z ∈ h ⁻¹ᵁ V
  · have hz' : (r ≫ h) z ∈ V := hz
    simp only [gm, dif_pos hz, dif_pos hz']
    first
    | rfl
    | (ext; simp [pullU, Scheme.comp_app])
  · have hz' : (r ≫ h) z ∉ V := hz
    simp only [gm, dif_neg hz, dif_neg hz', MonoidHom.one_apply]

theorem gm_pullGen' (L : LB X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ) (t : LB.Gen (LB.LinComb L φ ε))
    {Z Z' : Scheme.{0}} (h : Z ⟶ Y) (r : Z' ⟶ Z) (z : Z') (j : K → L.ι) :
    gm r z (LB.wchart L (fun k => h ≫ φ k) j) ((LB.pullGen L φ ε t h).s j) = gm (r ≫ h) z (LB.wchart L φ j) (t.s j) := by
  by_cases hz : r z ∈ LB.wchart L (fun k => h ≫ φ k) j
  · exact (gm_res r z _ hz (pullU h _ (t.s j))).trans (gm_pullU_eq_gm_comp h r z _ _)
  · have hz' : (r ≫ h) z ∉ LB.wchart L φ j := fun H => hz (Set.mem_iInter.2 fun k => Set.mem_iInter.1 H k)
    simp only [gm, dif_neg hz, dif_neg hz', MonoidHom.one_apply]
    rfl

theorem pmaps_pullGen {L : LB X} {L' : LB X'} {F : X' ⟶ X} {w : LB.Iso L' (L.pull F)} {K : Type} [Fintype K]
    {φ' : K → (Y' ⟶ X')} {φ : K → (Y ⟶ X)} {ε : K → ℤ} {a : LB.Gen (LB.LinComb L' φ' ε)}
    {t : LB.Gen (LB.LinComb L φ ε)} {h : Y' ⟶ Y} (H : PMaps w φ' φ ε a t h) (v : Y'' ⟶ Y') (v' : Y'' ⟶ Y)
    (hv : v ≫ h = v') :
    PMaps w (fun k => v ≫ φ' k) (fun k => v' ≫ φ k) ε (LB.pullGen L' φ' ε a v) (LB.pullGen L φ ε t v') (𝟙 _) := by
  intro Z r z p q h1 h2
  have e := H Z (r ≫ v) z p q (fun k => by simpa using h1 k) (fun k => by simpa using h2 k)
  simp only [Category.assoc, hv] at e
  simp only [Category.comp_id]
  rw [gm_pullGen', gm_pullGen', e]

def pullCongr {L : LB X} {L' : LB X'} {F F' : X' ⟶ X} (h : F = F') (w : LB.Iso L' (L.pull F)) : LB.Iso L' (L.pull F') :=
  h ▸ w

theorem gw_pullCongr {L : LB X} {L' : LB X'} {F F' : X' ⟶ X} (h : F = F') (w : LB.Iso L' (L.pull F)) {Z : Scheme.{0}}
    (f : Z ⟶ X') (z : Z) (j : L.ι) (k : L'.ι) : gw (pullCongr h w) f z j k = gw w f z j k := by
  subst h
  rfl

theorem pgen_pullCongr {L : LB X} {L' : LB X'} {F F' : X' ⟶ X} (h : F = F') {w : LB.Iso L' (L.pull F)} (hw : PGen w) :
    PGen (pullCongr h w) := by
  subst h
  exact hw

theorem pmaps_pullCongr {L : LB X} {L' : LB X'} {F F' : X' ⟶ X} (h : F = F') {w : LB.Iso L' (L.pull F)} {K : Type}
    [Fintype K] {φ' : K → (Y' ⟶ X')} {φ : K → (Y ⟶ X)} {ε : K → ℤ} {a : LB.Gen (LB.LinComb L' φ' ε)}
    {t : LB.Gen (LB.LinComb L φ ε)} {e : Y' ⟶ Y} (H : PMaps w φ' φ ε a t e) : PMaps (pullCongr h w) φ' φ ε a t e := by
  subst h
  exact H

theorem gm_of_res_eq' {V U₁ U₂ U₃ U₄ : Y.Opens} {h₁ : V ≤ U₁} {h₂ : V ≤ U₂} {h₃ : V ≤ U₃}
    {h₄ : V ≤ U₄} {a : Γ(Y, U₁)ˣ} {b : Γ(Y, U₂)ˣ} {c : Γ(Y, U₃)ˣ} {d : Γ(Y, U₄)ˣ}
    (H : res h₁ a * res h₂ b = res h₃ c * res h₄ d) {Z : Scheme.{0}} (f : Z ⟶ Y) {y : Z} (hy : f y ∈ V) :
    gm f y U₁ a * gm f y U₂ b = gm f y U₃ c * gm f y U₄ d := by
  rw [← gm_res f y h₁ hy a, ← gm_res f y h₂ hy b, ← gm_res f y h₃ hy c, ← gm_res f y h₄ hy d,
    ← map_mul, ← map_mul, H]

theorem gw_heq {L : LB X} {L' : LB X'} {F F' : X' ⟶ X} (h : F = F') {w : LB.Iso L' (L.pull F)}
    {w' : LB.Iso L' (L.pull F')} (hw : HEq w w') {Z : Scheme.{0}} (f : Z ⟶ X') (z : Z) (j : L.ι) (k : L'.ι) :
    gw w f z j k = gw w' f z j k := by
  subst h
  obtain rfl := eq_of_heq hw
  rfl

theorem genRelR_heq {A : Type} [CommRing A] {B B₀ : Scheme.{0}} {M : LB B} {M₀ : LB B₀} {φ φ' : B ⟶ B₀} (h : φ = φ')
    {w : LB.Iso M (M₀.pull φ)} {w' : LB.Iso M (M₀.pull φ')} (hw : HEq w w') {K : Type} [Fintype K]
    {pt : K → (Sp A ⟶ B)} {pt₀ : K → (Sp A ⟶ B₀)} {ε : K → ℤ} (t : LB.Gen (LB.LinComb M pt ε))
    (t₀ : LB.Gen (LB.LinComb M₀ pt₀ ε)) : GenRelR w t t₀ ↔ GenRelR w' t t₀ := by
  subst h
  obtain rfl := eq_of_heq hw
  exact Iff.rfl

end Pulls

section Thick

theorem thick_mono (R : Type) [CommRing R] (I : Ideal R) (n : ℕ) : Mono (Out.thick R I n) := by
  first
  | exact inferInstance
  | exact (IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective).mono
  | (haveI := IsClosedImmersion.spec_of_surjective
        (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1)))) Ideal.Quotient.mk_surjective
     infer_instance)

theorem thick_map_eq {R : Type} [CommRing R] {I : Ideal R} {n : ℕ} {G G' : Over (Sp R)} (ψ : G ⟶ G')
    (h : (Out.thickObj R I n G).left ⟶ (Out.thickObj R I n G').left)
    (hh : h ≫ (Out.fstG I n G').left = (Out.fstG I n G).left ≫ ψ.left) :
    h = ((Over.pullback (Out.thick R I n)).map ψ).left := by
  have hh' : h ≫ pullback.fst G'.hom (Out.thick R I n) = pullback.fst G.hom (Out.thick R I n) ≫ ψ.left := hh
  haveI := thick_mono R I n
  have m1 : ((Over.pullback (Out.thick R I n)).map ψ).left ≫ pullback.fst G'.hom (Out.thick R I n) =
      pullback.fst G.hom (Out.thick R I n) ≫ ψ.left := by
    first
    | (simp [Over.pullback]; done)
    | (simp [Over.pullback]; exact pullback.lift_fst _ _ _)
    | exact pullback.lift_fst _ _ _
  have m2 : ((Over.pullback (Out.thick R I n)).map ψ).left ≫ pullback.snd G'.hom (Out.thick R I n) =
      pullback.snd G.hom (Out.thick R I n) := by
    first
    | (simp [Over.pullback]; done)
    | (simp [Over.pullback]; exact pullback.lift_snd _ _ _)
    | exact pullback.lift_snd _ _ _
  apply pullback.hom_ext
  · rw [hh', m1]
  · rw [m2, ← cancel_mono (Out.thick R I n), Category.assoc,
      ← pullback.condition (f := G'.hom) (g := Out.thick R I n), reassoc_of% hh', Over.w ψ,
      pullback.condition (f := G.hom) (g := Out.thick R I n)]

end Thick

end ReciprocityTheory.ChartRestriction.G.Geo.Tor
