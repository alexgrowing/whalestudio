import Mathlib
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.StatementsSpreadGlue
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.StatementsIsoGlueTwo
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PVectorBundleLocal
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PSpreadBundle
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.GlueCoherence
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

open CategoryTheory AlgebraicGeometry

noncomputable section

theorem isVectorBundle_of_two {X : Scheme.{0}} {O₁ O₂ O : X.Opens} (h₁ : O₁ ≤ O) (h₂ : O₂ ≤ O)
    (hO : O ≤ O₁ ⊔ O₂) {F : (O : Scheme.{0}).Modules}
    (H₁ : IsVectorBundle ((Scheme.Modules.pullback (X.homOfLE h₁)).obj F))
    (H₂ : IsVectorBundle ((Scheme.Modules.pullback (X.homOfLE h₂)).obj F)) : IsVectorBundle F := by
  have key : ∀ {S : Scheme.{0}} (j : S ⟶ (O : Scheme.{0})) [IsOpenImmersion j],
      IsVectorBundle ((Scheme.Modules.pullback j).obj F) →
        IsVectorBundle ((Scheme.Modules.pullback j.opensRange.ι).obj F) := by
    intro S j _ H
    have e : j.isoOpensRange.inv ≫ j = j.opensRange.ι :=
      (Iso.inv_comp_eq _).2 (Scheme.Hom.isoOpensRange_hom_ι j).symm
    exact (H.pullback_of_isOpenImmersion j.isoOpensRange.inv).of_iso
      (pullbackCompIso e (Iso.refl _)).symm
  refine VectorBundleLocal.proof (O : Scheme.{0}) Bool
    (fun b => bif b then (X.homOfLE h₁).opensRange else (X.homOfLE h₂).opensRange) ?_ F ?_
  · rw [eq_top_iff]
    rintro x -
    rw [TopologicalSpace.Opens.mem_iSup]
    rcases hO x.2 with h | h
    · exact ⟨true, ⟨x.1, h⟩, Scheme.homOfLE_apply' h₁ x.1 h⟩
    · exact ⟨false, ⟨x.1, h⟩, Scheme.homOfLE_apply' h₂ x.1 h⟩
  · intro b
    cases b
    · exact key _ H₂
    · exact key _ H₁

lemma pullbackCompIso_rfl {T Y Z : Scheme.{0}} (g : T ⟶ Y) (h : Y ⟶ Z) (M : Z.Modules) :
    pullbackCompIso (rfl : g ≫ h = g ≫ h) (Iso.refl ((Scheme.Modules.pullback h).obj M)) =
      ((Scheme.Modules.pullbackComp g h).app M).symm := by
  ext1
  simp [pullbackCompIso, Scheme.Modules.pullbackCongr]

lemma restrictSpread_eq {X : Scheme.{0}} (f : X ⟶ SpecZ) (R : Type) [CommRing R]
    (E : (baseChange f R).Modules) {V W : X.Opens} (h : V ≤ W) {E' : (W : Scheme.{0}).Modules}
    (α : (Scheme.Modules.pullback (baseChangeMap f R ∣_ W)).obj E' ≅
      (Scheme.Modules.pullback (baseChangeMap f R ⁻¹ᵁ W).ι).obj E) :
    restrictSpread f R E h α =
      (pullbackCompIso (morphismRestrict_homOfLE (baseChangeMap f R) V W h) (Iso.refl _)).symm ≪≫
        pullbackCompIso rfl α ≪≫
        (pullbackCompIso (Scheme.homOfLE_ι _ ((baseChangeMap f R).preimage_mono h)) (Iso.refl _)).symm := by
  rw [restrictSpread, ← Iso.trans_assoc, pullbackComp_trans_congr, pullbackComp_trans_congr,
    pullbackCompIso_eq_refl_trans _ α, pullbackCompIso_rfl, Iso.trans_assoc]

lemma res_spread {T' T V W Q Y : Scheme.{0}} (u : T' ⟶ T) {g : T ⟶ V} {ℓ : V ⟶ W} {t : T ⟶ Q}
    {gW : Q ⟶ W} {ιQ : Q ⟶ Y} {ι : T ⟶ Y} (mRh : g ≫ ℓ = t ≫ gW) (hιQ : t ≫ ιQ = ι)
    {g' : T' ⟶ V} {s : T' ⟶ Q} {ι' : T' ⟶ Y} (eg : u ≫ g = g') (es : u ≫ t = s) (eι : u ≫ ι = ι')
    (A : g' ≫ ℓ = s ≫ gW) (B : s ≫ ιQ = ι') {E' : W.Modules} {E : Y.Modules}
    (α : (Scheme.Modules.pullback gW).obj E' ≅ (Scheme.Modules.pullback ιQ).obj E) :
    pullbackCompIso eg (Iso.refl ((Scheme.Modules.pullback g).obj ((Scheme.Modules.pullback ℓ).obj E'))) ≪≫
      (Scheme.Modules.pullback u).mapIso ((pullbackCompIso mRh (Iso.refl _)).symm ≪≫
        pullbackCompIso (rfl : t ≫ gW = t ≫ gW) α ≪≫ (pullbackCompIso hιQ (Iso.refl _)).symm) ≪≫
      (pullbackCompIso eι (Iso.refl ((Scheme.Modules.pullback ι).obj E))).symm =
    (pullbackCompIso A (Iso.refl _)).symm ≪≫ pullbackCompIso (rfl : s ≫ gW = s ≫ gW) α ≪≫
      (pullbackCompIso B (Iso.refl _)).symm := by
  have k1 : u ≫ t ≫ gW = s ≫ gW := by rw [← Category.assoc, es]
  have h1 := mapIso_pullbackCompIso_refl u mRh eg k1 A E'
  have h2 := pullbackCompIso_comp' u (rfl : t ≫ gW = t ≫ gW) es k1 rfl α
  have h2' : (Scheme.Modules.pullback u).mapIso (pullbackCompIso (rfl : t ≫ gW = t ≫ gW) α) =
      (pullbackCompIso k1 (Iso.refl _)).symm ≪≫ pullbackCompIso (rfl : s ≫ gW = s ≫ gW) α ≪≫
        pullbackCompIso es (Iso.refl _) := by
    rw [h2]
    simp only [Iso.trans_assoc, Iso.symm_self_id_assoc, Iso.symm_self_id, Iso.trans_refl]
  have h3 := mapIso_pullbackCompIso_refl u hιQ es eι B E
  simp only [Functor.mapIso_trans, Functor.mapIso_symm, h1, h2', h3]
  simp only [Iso.trans_symm, Iso.symm_symm_eq, Iso.trans_assoc, Iso.self_symm_id_assoc,
    Iso.self_symm_id, Iso.trans_refl]

lemma res_phi {T' T P O O₁ O' Y : Scheme.{0}} {u : T' ⟶ T} {a : T ⟶ P} {c : T' ⟶ P} (E1 : u ≫ a = c)
    {gO : P ⟶ O} {gO₁ : T ⟶ O₁} {j : O₁ ⟶ O} (sq1 : gO₁ ≫ j = a ≫ gO)
    {ιP : P ⟶ Y} {ι₁ : T ⟶ Y} (hι : a ≫ ιP = ι₁)
    {gO' : T' ⟶ O'} {k : O' ⟶ O₁} (eg : u ≫ gO₁ = gO' ≫ k) {ι' : T' ⟶ Y} (eι : u ≫ ι₁ = ι')
    (e'ι : c ≫ ιP = ι') (e' : (gO' ≫ k) ≫ j = c ≫ gO)
    {F : O.Modules} {F₁ : O₁.Modules} {E : Y.Modules} (e : (Scheme.Modules.pullback j).obj F ≅ F₁)
    (Rs : (Scheme.Modules.pullback gO₁).obj F₁ ≅ (Scheme.Modules.pullback ι₁).obj E) :
    pullbackIsoAlong E1 ((pullbackCompIso (rfl : a ≫ gO = a ≫ gO) (Iso.refl _)).symm ≪≫
        pullbackCompIso sq1 e ≪≫ Rs ≪≫ pullbackCompIso hι (Iso.refl _)) =
      (pullbackCompIso (rfl : c ≫ gO = c ≫ gO) (Iso.refl _)).symm ≪≫ pullbackCompIso e' e ≪≫
        (pullbackCompIso eg (Iso.refl _) ≪≫ (Scheme.Modules.pullback u).mapIso Rs ≪≫
          (pullbackCompIso eι (Iso.refl _)).symm) ≪≫
        pullbackCompIso e'ι (Iso.refl _) := by
  have ek : u ≫ a ≫ gO = c ≫ gO := by rw [← Category.assoc, E1]
  have h1 := mapIso_pullbackCompIso_refl u (rfl : a ≫ gO = a ≫ gO) E1 ek rfl F
  have h2 := pullbackCompIso_comp' u sq1 eg ek e' e
  have h2' : (Scheme.Modules.pullback u).mapIso (pullbackCompIso sq1 e) =
      (pullbackCompIso ek (Iso.refl _)).symm ≪≫ pullbackCompIso e' e ≪≫ pullbackCompIso eg (Iso.refl _) := by
    rw [h2]
    simp only [Iso.trans_assoc, Iso.symm_self_id_assoc, Iso.symm_self_id, Iso.trans_refl]
  have h3 := mapIso_pullbackCompIso_refl u hι E1 eι e'ι E
  simp only [pullbackIsoAlong, Functor.mapIso_trans, Functor.mapIso_symm, h1, h2', h3]
  simp only [Iso.trans_symm, Iso.symm_symm_eq, Iso.trans_assoc, Iso.self_symm_id_assoc,
    Iso.self_symm_id, Iso.trans_refl]

theorem SpreadGlue.proof (hG : GlueTwo.Statement) (hI : IsoGlueTwo.Statement) :
    SpreadGlue.Statement := by
  intro X f R _ E W₁ W₂ E₁ E₂ hE₁ hE₂ α₁ α₂ V _ θ hθ
  have h₁ : W₁ ⊓ V ≤ (W₁ ⊔ W₂) ⊓ V := inf_le_inf_right V le_sup_left
  have h₂ : W₂ ⊓ V ≤ (W₁ ⊔ W₂) ⊓ V := inf_le_inf_right V le_sup_right
  have hO : (W₁ ⊔ W₂) ⊓ V ≤ W₁ ⊓ V ⊔ W₂ ⊓ V := inf_sup_right W₁ W₂ V ▸ le_rfl
  have k₁ : W₁ ⊓ W₂ ⊓ V ≤ W₁ ⊓ V := inf_le_inf_right V inf_le_left
  have k₂ : W₁ ⊓ W₂ ⊓ V ≤ W₂ ⊓ V := inf_le_inf_right V inf_le_right
  have hk : W₁ ⊓ V ⊓ (W₂ ⊓ V) ≤ W₁ ⊓ W₂ ⊓ V := fun x hx => ⟨⟨hx.1.1, hx.2.1⟩, hx.1.2⟩
  have l₁ : W₁ ⊓ V ≤ W₁ := inf_le_left
  have l₂ : W₂ ⊓ V ≤ W₂ := inf_le_left
  have m : W₁ ⊓ W₂ ⊓ V ≤ W₁ ⊓ W₂ := inf_le_left
  obtain ⟨F, e₁, e₂, he⟩ := hG X _ _ _ _ h₁ h₂ hO k₁ k₂ hk _ _
    ((pullbackCompIso (X.homOfLE_homOfLE k₁ l₁) (Iso.refl _)).symm ≪≫
      pullbackCompIso (X.homOfLE_homOfLE m (inf_le_left : W₁ ⊓ W₂ ≤ W₁)) (Iso.refl _) ≪≫ θ ≪≫
      (pullbackCompIso (X.homOfLE_homOfLE m (inf_le_right : W₁ ⊓ W₂ ≤ W₂)) (Iso.refl _)).symm ≪≫
      pullbackCompIso (X.homOfLE_homOfLE k₂ l₂) (Iso.refl _))
  have hF : IsVectorBundle F := isVectorBundle_of_two h₁ h₂ hO
    ((hE₁.pullback_of_isOpenImmersion _).of_iso e₁.symm)
    ((hE₂.pullback_of_isOpenImmersion _).of_iso e₂.symm)
  have hP₁ := (baseChangeMap f R).preimage_mono h₁
  have hP₂ := (baseChangeMap f R).preimage_mono h₂
  have hP : baseChangeMap f R ⁻¹ᵁ ((W₁ ⊔ W₂) ⊓ V) ≤ baseChangeMap f R ⁻¹ᵁ (W₁ ⊓ V) ⊔ baseChangeMap f R ⁻¹ᵁ (W₂ ⊓ V) := fun x hx => hO hx
  have kP₁ := (baseChangeMap f R).preimage_mono k₁
  have kP₂ := (baseChangeMap f R).preimage_mono k₂
  have hkP : baseChangeMap f R ⁻¹ᵁ (W₁ ⊓ V) ⊓ baseChangeMap f R ⁻¹ᵁ (W₂ ⊓ V) ≤ baseChangeMap f R ⁻¹ᵁ (W₁ ⊓ W₂ ⊓ V) := fun x hx => hk hx
  have sq1 := morphismRestrict_homOfLE (baseChangeMap f R) (W₁ ⊓ V) ((W₁ ⊔ W₂) ⊓ V) h₁
  have sq2 := morphismRestrict_homOfLE (baseChangeMap f R) (W₂ ⊓ V) ((W₁ ⊔ W₂) ⊓ V) h₂
  have hι1 := (baseChange f R).homOfLE_ι hP₁
  have hι2 := (baseChange f R).homOfLE_ι hP₂
  refine ⟨F, hF, ⟨(hI (baseChange f R) _ _ _ _ hP₁ hP₂ hP kP₁ kP₂ hkP _ _
    ((pullbackCompIso (rfl : (baseChange f R).homOfLE hP₁ ≫ baseChangeMap f R ∣_ ((W₁ ⊔ W₂) ⊓ V) = _) (Iso.refl _)).symm ≪≫
      pullbackCompIso sq1 e₁ ≪≫ restrictSpread f R E l₁ α₁ ≪≫ pullbackCompIso hι1 (Iso.refl _))
    ((pullbackCompIso (rfl : (baseChange f R).homOfLE hP₂ ≫ baseChangeMap f R ∣_ ((W₁ ⊔ W₂) ⊓ V) = _) (Iso.refl _)).symm ≪≫
      pullbackCompIso sq2 e₂ ≪≫ restrictSpread f R E l₂ α₂ ≪≫ pullbackCompIso hι2 (Iso.refl _))
    ?_).choose⟩⟩

  have E1 : (baseChange f R).homOfLE kP₁ ≫ (baseChange f R).homOfLE hP₁ = (baseChange f R).homOfLE (kP₁.trans hP₁) :=
    (baseChange f R).homOfLE_homOfLE _ _
  have E2 : (baseChange f R).homOfLE kP₂ ≫ (baseChange f R).homOfLE hP₂ = (baseChange f R).homOfLE (kP₁.trans hP₁) :=
    (baseChange f R).homOfLE_homOfLE _ _
  have eg1 := (morphismRestrict_homOfLE (baseChangeMap f R) (W₁ ⊓ W₂ ⊓ V) (W₁ ⊓ V) k₁).symm
  have eg2 := (morphismRestrict_homOfLE (baseChangeMap f R) (W₁ ⊓ W₂ ⊓ V) (W₂ ⊓ V) k₂).symm
  have eι1 := (baseChange f R).homOfLE_ι kP₁
  have eι2 := (baseChange f R).homOfLE_ι kP₂
  have eιc := (baseChange f R).homOfLE_ι (kP₁.trans hP₁)
  have e'1 : (baseChangeMap f R ∣_ (W₁ ⊓ W₂ ⊓ V) ≫ X.homOfLE k₁) ≫ X.homOfLE h₁ = (baseChange f R).homOfLE (kP₁.trans hP₁) ≫ baseChangeMap f R ∣_ ((W₁ ⊔ W₂) ⊓ V) := by
    rw [← cancel_mono (Scheme.Opens.ι _)]; simp [morphismRestrict_ι]
  have e'2 : (baseChangeMap f R ∣_ (W₁ ⊓ W₂ ⊓ V) ≫ X.homOfLE k₂) ≫ X.homOfLE h₂ = (baseChange f R).homOfLE (kP₁.trans hP₁) ≫ baseChangeMap f R ∣_ ((W₁ ⊔ W₂) ⊓ V) := by
    rw [← cancel_mono (Scheme.Opens.ι _)]; simp [morphismRestrict_ι]
  have mRh1 := morphismRestrict_homOfLE (baseChangeMap f R) (W₁ ⊓ V) W₁ l₁
  have mRh2 := morphismRestrict_homOfLE (baseChangeMap f R) (W₂ ⊓ V) W₂ l₂
  have hιQ1 := (baseChange f R).homOfLE_ι ((baseChangeMap f R).preimage_mono l₁)
  have hιQ2 := (baseChange f R).homOfLE_ι ((baseChangeMap f R).preimage_mono l₂)
  have es1 : (baseChange f R).homOfLE kP₁ ≫ (baseChange f R).homOfLE ((baseChangeMap f R).preimage_mono l₁) =
      (baseChange f R).homOfLE ((baseChangeMap f R).preimage_mono (k₁.trans l₁)) := (baseChange f R).homOfLE_homOfLE _ _
  have es2 : (baseChange f R).homOfLE kP₂ ≫ (baseChange f R).homOfLE ((baseChangeMap f R).preimage_mono l₂) =
      (baseChange f R).homOfLE ((baseChangeMap f R).preimage_mono (k₂.trans l₂)) := (baseChange f R).homOfLE_homOfLE _ _
  have A1 : (baseChangeMap f R ∣_ (W₁ ⊓ W₂ ⊓ V) ≫ X.homOfLE k₁) ≫ X.homOfLE l₁ =
      (baseChange f R).homOfLE ((baseChangeMap f R).preimage_mono (k₁.trans l₁)) ≫ baseChangeMap f R ∣_ W₁ := by
    rw [← cancel_mono (Scheme.Opens.ι _)]; simp [morphismRestrict_ι]
  have A2 : (baseChangeMap f R ∣_ (W₁ ⊓ W₂ ⊓ V) ≫ X.homOfLE k₂) ≫ X.homOfLE l₂ =
      (baseChange f R).homOfLE ((baseChangeMap f R).preimage_mono (k₂.trans l₂)) ≫ baseChangeMap f R ∣_ W₂ := by
    rw [← cancel_mono (Scheme.Opens.ι _)]; simp [morphismRestrict_ι]
  have B1 := (baseChange f R).homOfLE_ι ((baseChangeMap f R).preimage_mono (k₁.trans l₁))
  have B2 := (baseChange f R).homOfLE_ι ((baseChangeMap f R).preimage_mono (k₂.trans l₂))
  rw [res_phi E1 sq1 hι1 eg1 eι1 eιc e'1 e₁, res_phi E2 sq2 hι2 eg2 eι2 eιc e'2 e₂,
    restrictSpread_eq, restrictSpread_eq, res_spread _ mRh1 hιQ1 eg1 es1 eι1 A1 B1,
    res_spread _ mRh2 hιQ2 eg2 es2 eι2 A2 B2]

  have ekO := morphismRestrict_homOfLE (baseChangeMap f R) (W₁ ⊓ W₂ ⊓ V) ((W₁ ⊔ W₂) ⊓ V) (k₁.trans h₁)
  have c1 := pullbackCompIso_comp' (baseChangeMap f R ∣_ (W₁ ⊓ W₂ ⊓ V)) (X.homOfLE_homOfLE k₁ h₁) rfl ekO e'1 e₁
  have c2 := pullbackCompIso_comp' (baseChangeMap f R ∣_ (W₁ ⊓ W₂ ⊓ V)) (X.homOfLE_homOfLE k₂ h₂) rfl ekO e'2 e₂
  rw [c2, he, c1]

  have ek1 := morphismRestrict_homOfLE (baseChangeMap f R) (W₁ ⊓ W₂ ⊓ V) W₁ (k₁.trans l₁)
  have ek2 := morphismRestrict_homOfLE (baseChangeMap f R) (W₁ ⊓ W₂ ⊓ V) W₂ (k₂.trans l₂)
  have Am1 : (baseChangeMap f R ∣_ (W₁ ⊓ W₂ ⊓ V) ≫ X.homOfLE m) ≫ X.homOfLE (inf_le_left : W₁ ⊓ W₂ ≤ W₁) =
      (baseChange f R).homOfLE ((baseChangeMap f R).preimage_mono (k₁.trans l₁)) ≫ baseChangeMap f R ∣_ W₁ := by
    rw [← cancel_mono (Scheme.Opens.ι _)]; simp [morphismRestrict_ι]
  have Am2 : (baseChangeMap f R ∣_ (W₁ ⊓ W₂ ⊓ V) ≫ X.homOfLE m) ≫ X.homOfLE (inf_le_right : W₁ ⊓ W₂ ≤ W₂) =
      (baseChange f R).homOfLE ((baseChangeMap f R).preimage_mono (k₂.trans l₂)) ≫ baseChangeMap f R ∣_ W₂ := by
    rw [← cancel_mono (Scheme.Opens.ι _)]; simp [morphismRestrict_ι]
  have hk1' := mapIso_pullbackCompIso_refl (baseChangeMap f R ∣_ (W₁ ⊓ W₂ ⊓ V)) (X.homOfLE_homOfLE k₁ l₁) rfl ek1 A1 E₁
  have hk2' := mapIso_pullbackCompIso_refl (baseChangeMap f R ∣_ (W₁ ⊓ W₂ ⊓ V)) (X.homOfLE_homOfLE k₂ l₂) rfl ek2 A2 E₂
  have hm1' := mapIso_pullbackCompIso_refl (baseChangeMap f R ∣_ (W₁ ⊓ W₂ ⊓ V))
    (X.homOfLE_homOfLE m (inf_le_left : W₁ ⊓ W₂ ≤ W₁)) rfl ek1 Am1 E₁
  have hm2' := mapIso_pullbackCompIso_refl (baseChangeMap f R ∣_ (W₁ ⊓ W₂ ⊓ V))
    (X.homOfLE_homOfLE m (inf_le_right : W₁ ⊓ W₂ ≤ W₂)) rfl ek2 Am2 E₂
  have hθ' : (Scheme.Modules.pullback (baseChangeMap f R ∣_ (W₁ ⊓ W₂ ⊓ V))).mapIso θ =
      (pullbackCompIso (rfl : baseChangeMap f R ∣_ (W₁ ⊓ W₂ ⊓ V) ≫ X.homOfLE m = _) (Iso.refl _)).symm ≪≫
        pullbackIsoAlong (morphismRestrict_homOfLE (baseChangeMap f R) (W₁ ⊓ W₂ ⊓ V) (W₁ ⊓ W₂) m).symm
          (overlapIso f R E α₁ α₂) ≪≫
        pullbackCompIso (rfl : baseChangeMap f R ∣_ (W₁ ⊓ W₂ ⊓ V) ≫ X.homOfLE m = _) (Iso.refl _) := by
    rw [← hθ]
    simp only [pullbackIsoAlong, Iso.trans_assoc, Iso.symm_self_id_assoc, Iso.symm_self_id,
      Iso.trans_refl]

  have mRh'1 := morphismRestrict_homOfLE (baseChangeMap f R) (W₁ ⊓ W₂) W₁ inf_le_left
  have mRh'2 := morphismRestrict_homOfLE (baseChangeMap f R) (W₁ ⊓ W₂) W₂ inf_le_right
  have hιQ'1 := (baseChange f R).homOfLE_ι ((baseChangeMap f R).preimage_mono (inf_le_left : W₁ ⊓ W₂ ≤ W₁))
  have hιQ'2 := (baseChange f R).homOfLE_ι ((baseChangeMap f R).preimage_mono (inf_le_right : W₁ ⊓ W₂ ≤ W₂))
  have es'1 : (baseChange f R).homOfLE ((baseChangeMap f R).preimage_mono m) ≫
      (baseChange f R).homOfLE ((baseChangeMap f R).preimage_mono (inf_le_left : W₁ ⊓ W₂ ≤ W₁)) =
      (baseChange f R).homOfLE ((baseChangeMap f R).preimage_mono (k₁.trans l₁)) := (baseChange f R).homOfLE_homOfLE _ _
  have es'2 : (baseChange f R).homOfLE ((baseChangeMap f R).preimage_mono m) ≫
      (baseChange f R).homOfLE ((baseChangeMap f R).preimage_mono (inf_le_right : W₁ ⊓ W₂ ≤ W₂)) =
      (baseChange f R).homOfLE ((baseChangeMap f R).preimage_mono (k₂.trans l₂)) := (baseChange f R).homOfLE_homOfLE _ _
  have eιs := (baseChange f R).homOfLE_ι ((baseChangeMap f R).preimage_mono m)
  have r1 := res_spread _ mRh'1 hιQ'1 (morphismRestrict_homOfLE (baseChangeMap f R) (W₁ ⊓ W₂ ⊓ V) (W₁ ⊓ W₂) m).symm
    es'1 eιs Am1 B1 α₁
  have r2 := res_spread _ mRh'2 hιQ'2 (morphismRestrict_homOfLE (baseChangeMap f R) (W₁ ⊓ W₂ ⊓ V) (W₁ ⊓ W₂) m).symm
    es'2 eιs Am2 B2 α₂
  have hov : pullbackIsoAlong (morphismRestrict_homOfLE (baseChangeMap f R) (W₁ ⊓ W₂ ⊓ V) (W₁ ⊓ W₂) m).symm
      (overlapIso f R E α₁ α₂) =
      ((pullbackCompIso Am1 (Iso.refl _)).symm ≪≫
        pullbackCompIso (rfl : (baseChange f R).homOfLE ((baseChangeMap f R).preimage_mono (k₁.trans l₁)) ≫ baseChangeMap f R ∣_ W₁ = _) α₁ ≪≫
        (pullbackCompIso B1 (Iso.refl _)).symm) ≪≫
      ((pullbackCompIso Am2 (Iso.refl _)).symm ≪≫
        pullbackCompIso (rfl : (baseChange f R).homOfLE ((baseChangeMap f R).preimage_mono (k₂.trans l₂)) ≫ baseChangeMap f R ∣_ W₂ = _) α₂ ≪≫
        (pullbackCompIso B2 (Iso.refl _)).symm).symm := by
    rw [← r1, ← r2, overlapIso, restrictSpread_eq, restrictSpread_eq]
    simp only [pullbackIsoAlong, Functor.mapIso_trans, Functor.mapIso_symm, Iso.trans_symm,
      Iso.symm_symm_eq, Iso.trans_assoc, Iso.symm_self_id_assoc]
  simp only [Functor.mapIso_trans, Functor.mapIso_symm]
  rw [hk1', hm1', hθ', hov, hm2', hk2']
  simp only [Iso.trans_symm, Iso.symm_symm_eq, Iso.trans_assoc, Iso.self_symm_id_assoc,
    Iso.symm_self_id_assoc, Iso.self_symm_id, Iso.trans_refl]

end

end GroundTheory.Heights₂.Heights.Model
