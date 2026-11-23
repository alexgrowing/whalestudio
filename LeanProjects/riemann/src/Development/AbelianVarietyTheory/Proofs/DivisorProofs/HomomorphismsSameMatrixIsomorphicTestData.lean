import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WchartCompLe
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PolarizedAbelianEmbeddingBySections
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.PullSec
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfProportionalGermsSectionsEmbedProjectivelyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMatrixIdentityGermPullbackChartStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EmbedsAfterBaseChangeSpecTopOpenOfStableBasisStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat

noncomputable section

namespace GlobalTheory.HomFixMat

private theorem topS_tensor_left_ext {Rg : Type} [CommRing Rg] (A : Over (Sp Rg)) {Z : Scheme.{0}}
    (f g : Z ⟶ (topS Rg ⊗ A).left) (h : f ≫ (snd (topS Rg) A).left = g ≫ (snd (topS Rg) A).left) : f = g := by
  have P := IsPullback.of_hasPullback (topS Rg).hom A.hom
  have h' : f ≫ pullback.snd (topS Rg).hom A.hom = g ≫ pullback.snd (topS Rg).hom A.hom := h
  apply P.hom_ext
  · have hm : Mono (topS Rg).hom := by
      change Mono ((⊤ : (Sp Rg).Opens).ι ≫ 𝟙 _); infer_instance
    rw [← cancel_mono (topS Rg).hom, Category.assoc, Category.assoc, P.w, ← Category.assoc, h', Category.assoc]
  · exact h'

end GlobalTheory.HomFixMat

namespace GlobalTheory.HomFixMat

theorem mat_determines : ∀ (Rg : Type) [CommRing Rg] [IsNoetherianRing Rg] (A B : Over (Sp Rg)) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] (L : LB A.left) (M : LB B.left) (k : ℕ) (mA mB : ℕ) (bA : Fin mA → LB.Sec (LPow A L (k : ℤ) (topS Rg))) (bB : Fin mB → LB.Sec (LPow B M (k : ℤ) (topS Rg))) (eA : LB.Gen (L.pull (eSec A))) (eB : LB.Gen (M.pull (eSec B))), Hyps L M k bA bB eA eB → ∀ (R : Type) [CommRing R] (t : Sp R ⟶ Sp Rg) (A₁ B₁ : Over (Sp R)) [GrpObj A₁] [GrpObj B₁] (φA₁ : A₁.left ⟶ A.left) (φB₁ : B₁.left ⟶ B.left) (Φ₁ : A₁ ⟶ B₁) (A₂ B₂ : Over (Sp R)) [GrpObj A₂] [GrpObj B₂] (φA₂ : A₂.left ⟶ A.left) (φB₂ : B₂.left ⟶ B.left) (Φ₂ : A₂ ⟶ B₂) (c : Fin mA → Fin mB → Γ(Sp R, ⊤)), IsTest A B L M t A₁ B₁ φA₁ φB₁ Φ₁ → IsTest A B L M t A₂ B₂ φA₂ φB₂ Φ₂ → IsMat L M k bA bB eA eB t A₁ B₁ φA₁ φB₁ Φ₁ c → IsMat L M k bA bB eA eB t A₂ B₂ φA₂ φB₂ Φ₂ c → IsPullD φA₁ φB₁ Φ₁ φA₂ φB₂ Φ₂ (𝟙 (Sp R)) := by
  intro Rg _ _ A B _ _ _ _ L M k mA mB bA bB eA eB hH R _ t A₁ B₁ _ _ φA₁ φB₁ Φ₁ A₂ B₂ _ _ φA₂ φB₂ Φ₂ c T₁ T₂ M₁ M₂
  obtain ⟨-, hBab, hL, hM, -, -, -, -, hva, -, hbc⟩ := hH
  let ψA : A₂.left ⟶ A₁.left := T₁.1.1.lift φA₂ A₂.hom T₂.1.1.w
  let ψB : B₂.left ⟶ B₁.left := T₁.2.1.1.lift φB₂ B₂.hom T₂.2.1.1.w
  have hψA1 : ψA ≫ φA₁ = φA₂ := T₁.1.1.lift_fst _ _ _
  have hψA2 : ψA ≫ A₁.hom = A₂.hom := T₁.1.1.lift_snd _ _ _
  have hψB1 : ψB ≫ φB₁ = φB₂ := T₁.2.1.1.lift_fst _ _ _
  have hψB2 : ψB ≫ B₁.hom = B₂.hom := T₁.2.1.1.lift_snd _ _ _
  have gA : IsGrpPullback A₂ A₁ (𝟙 _) ψA :=
    IsGrpPullback.cancel T₁.1 (by rw [Category.id_comp, hψA1]; exact T₂.1) (by rw [hψA2, Category.comp_id])
  have gB : IsGrpPullback B₂ B₁ (𝟙 _) ψB :=
    IsGrpPullback.cancel T₁.2.1 (by rw [Category.id_comp, hψB1]; exact T₂.2.1) (by rw [hψB2, Category.comp_id])
  refine ⟨ψA, ψB, gA, gB, hψA1, hψB1, ?_⟩
  suffices key : Φ₂.left ≫ φB₂ = ψA ≫ Φ₁.left ≫ φB₁ by
    apply T₁.2.1.1.hom_ext
    · rw [Category.assoc, hψB1, key, Category.assoc]
    · rw [Category.assoc, hψB2, Over.w Φ₂, Category.assoc, Over.w Φ₁, hψA2]

  obtain ⟨ψA₁, ψB₁, eA₁, eB₁, g₁⟩ := GlobalTheory.T.isMatrixIdentity_germ_pullback_chart M₁
  obtain ⟨ψA₂, ψB₂, eA₂, eB₂, g₂⟩ := GlobalTheory.T.isMatrixIdentity_germ_pullback_chart M₂
  obtain ⟨x, b', hx, hb', hemb⟩ := GlobalTheory.T.embeds_after_baseChange_specTopOpen_of_stable_basis B M k bB hBab hM hva hbc
  have hG : ψA ≫ ψA₁ = ψA₂ := topS_tensor_left_ext A _ _ (by rw [Category.assoc, eA₁, eA₂, hψA1])
  let H : (baseAt x ⊗ B).left ⟶ (topS Rg ⊗ B).left := (homAt x ▷ B).left
  have hHi : IsIso (homAt x) := by
    have : IsIso ((Over.forget _).map (homAt x)) := hx
    exact isIso_of_reflects_iso (homAt x) (Over.forget _)
  have hH : IsIso H := (inferInstance : IsIso ((Over.forget _).map (homAt x ▷ B)))
  have hHs : H ≫ (snd (topS Rg) B).left = (snd (baseAt x) B).left := by
    rw [← Over.comp_left, whiskerRight_snd]
  let F₁ : A₂.left ⟶ (topS Rg ⊗ B).left := ψA ≫ Φ₁.left ≫ ψB₁
  let F₂ : A₂.left ⟶ (topS Rg ⊗ B).left := Φ₂.left ≫ ψB₂
  suffices hF : F₂ ≫ inv H = F₁ ≫ inv H by
    have e1 : F₂ = F₁ := by simpa using congrArg (· ≫ H) hF
    have e2 : F₂ ≫ (snd (topS Rg) B).left = F₁ ≫ (snd (topS Rg) B).left := by rw [e1]
    simp only [F₁, F₂, Category.assoc] at e2
    rwa [eB₁, eB₂] at e2

  have memw : ∀ {P Q : Scheme.{0}} (W : LB Q) (φ : P ⟶ Q) (j : Fin 1 → W.ι) (y : P), φ y ∈ W.U (j 0) →
      y ∈ LB.wchart W (fun _ : Fin 1 => φ) j := fun W φ j y h =>
    Set.mem_iInter.2 fun i => by rw [Subsingleton.elim i 0]; exact h
  have hsx : (snd (topS Rg) B).left = inv H ≫ (snd (baseAt x) B).left := by
    rw [← hHs, IsIso.inv_hom_id_assoc]
  have hbase : ∀ (Z : Scheme.{0}) (r : Z ⟶ (baseAt x ⊗ B).left) (z : Z) (pM : Fin 1 → M.ι) (j : Fin mB),
      r z ∈ (LPow B M (k : ℤ) (baseAt x)).U pM →
      gs r z _ ((b' j).f pM) = gs (r ≫ H) z _ ((bB j).f pM) := by
    intro Z r z pM j hz
    rw [hb' j pM, gs_res _ _ _ hz, gs_pull]
    exact chart_le_res B M (homAt x ▷ B) (whiskerRight_snd (homAt x) B) (k : ℤ) pM hz
  have hmono : Mono (baseAt x).hom := by
    have : Mono (topS Rg).hom := by
      change Mono ((⊤ : (Sp Rg).Opens).ι ≫ 𝟙 _); infer_instance
    change Mono (x ≫ (topS Rg).hom); infer_instance
  have hπ : ∀ F : A₂.left ⟶ (topS Rg ⊗ B).left, F ≫ inv H ≫ (fst (baseAt x) B).left ≫ (baseAt x).hom =
      F ≫ (snd (topS Rg) B).left ≫ B.hom := by
    intro F
    have w : (fst (baseAt x) B).left ≫ (baseAt x).hom = (snd (baseAt x) B).left ≫ B.hom :=
      pullback.condition
    rw [w, hsx]; simp only [Category.assoc]
  refine GlobalTheory.T.eq_of_proportional_germs_sectionsEmbedProjectively (fst (baseAt x) B).left b' hemb _ _ ?_ ?_
  · rw [← cancel_mono (baseAt x).hom]
    simp only [Category.assoc]
    rw [hπ, hπ]
    simp only [F₁, F₂, Category.assoc]
    rw [reassoc_of% eB₁, reassoc_of% eB₂, T₁.2.1.1.w, T₂.2.1.1.w, reassoc_of% (Over.w Φ₂), reassoc_of% (Over.w Φ₁),
      reassoc_of% hψA2]
  · intro z
    obtain ⟨q0, hq0⟩ := exists_chart hL (φA₂ z)
    obtain ⟨p₁, hp₁⟩ := exists_chart hM ((ψA ≫ Φ₁.left ≫ φB₁) z)
    obtain ⟨p₂, hp₂⟩ := exists_chart hM ((Φ₂.left ≫ φB₂) z)
    have mA₂ : (𝟙 A₂.left ≫ ψA₂) z ∈ (LPow A L (k : ℤ) (topS Rg)).U (fun _ => q0) := by
      refine memw L _ _ _ ?_
      rw [← Scheme.Hom.comp_apply, Category.id_comp, eA₂]; exact hq0
    have mA₁ : (ψA ≫ ψA₁) z ∈ (LPow A L (k : ℤ) (topS Rg)).U (fun _ => q0) := by
      rw [hG]; simpa using mA₂
    have mB₂ : (𝟙 A₂.left ≫ Φ₂.left ≫ ψB₂) z ∈ (LPow B M (k : ℤ) (topS Rg)).U (fun _ => p₂) := by
      refine memw M _ _ _ ?_
      rw [← Scheme.Hom.comp_apply, Category.id_comp, Category.assoc, eB₂]; exact hp₂
    have mB₁ : (ψA ≫ Φ₁.left ≫ ψB₁) z ∈ (LPow B M (k : ℤ) (topS Rg)).U (fun _ => p₁) := by
      refine memw M _ _ _ ?_
      rw [← Scheme.Hom.comp_apply, Category.assoc, Category.assoc, eB₁]; exact hp₁
    obtain ⟨u₂, hu₂⟩ := g₂ A₂.left (𝟙 _) z _ _ mB₂ mA₂
    obtain ⟨u₁, hu₁⟩ := g₁ A₂.left ψA z _ _ mB₁ mA₁
    simp only [Category.id_comp] at hu₂
    rw [hψA2, hG] at hu₁
    refine ⟨fun j => ∑ i, gs A₂.hom z ⊤ (c i j) * gs ψA₂ z _ ((bA i).f (fun _ => q0)), ⟨fun _ => p₂, ?_, u₂, fun l => ?_⟩,
      ⟨fun _ => p₁, ?_, u₁, fun l => ?_⟩⟩
    · refine memw M _ _ _ ?_
      rw [← Scheme.Hom.comp_apply, Category.assoc, ← hsx]; simp only [F₂, Category.assoc]; rw [eB₂]; exact hp₂
    · rw [hbase _ _ _ _ _ (memw M _ _ _ (by rw [← Scheme.Hom.comp_apply, Category.assoc, ← hsx]; simp only [F₂, Category.assoc]; rw [eB₂]; exact hp₂)),
        Category.assoc, IsIso.inv_hom_id, Category.comp_id]
      exact hu₂ l
    · refine memw M _ _ _ ?_
      rw [← Scheme.Hom.comp_apply, Category.assoc, ← hsx]; simp only [F₁, Category.assoc]; rw [eB₁]; exact hp₁
    · rw [hbase _ _ _ _ _ (memw M _ _ _ (by rw [← Scheme.Hom.comp_apply, Category.assoc, ← hsx]; simp only [F₁, Category.assoc]; rw [eB₁]; exact hp₁)),
        Category.assoc, IsIso.inv_hom_id, Category.comp_id]
      exact hu₁ l

end GlobalTheory.HomFixMat
