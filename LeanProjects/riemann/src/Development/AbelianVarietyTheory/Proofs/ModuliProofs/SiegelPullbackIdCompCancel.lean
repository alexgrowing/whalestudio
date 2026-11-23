import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.SiegelPullbackTransfer.ExistsGenTransfer
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section

namespace GlobalTheory.SiegelPullComp

theorem iso_pull {X Y : Scheme.{0}} {L M : LB X} (d : Y ⟶ X) (h : LBIso L M) : LBIso (L.pull d) (M.pull d) := by
  obtain ⟨w, hw⟩ := h
  exact ⟨LB.linCombIso w (fun _ : PUnit => d) (fun _ => 1), DVR.linCombIso_isGen w hw _ _⟩

private theorem gm_res_eq_gm {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) {U V : X.Opens} (h : V ≤ U) (hy : f y ∈ V)
    (x : Γ(X, U)ˣ) : gm f y V (res h x) = gm f y U x := by
  unfold gm
  rw [dif_pos hy, dif_pos (h hy)]
  simp only [MonoidHom.comp_apply]
  rw [pullU_res₂]
  ext
  simp [res]
  exact TopCat.Presheaf.germ_res_apply _ _ _ _ _

private theorem lbIso_of_chart_le_of_gm_transition_eq {Y : Scheme.{0}} {A' B : LB Y} (hB : LBIso B B) (idx : A'.ι → B.ι)
    (le : ∀ i, A'.U i ≤ B.U (idx i))
    (hg : ∀ (y : Y) i j, y ∈ A'.U i → y ∈ A'.U j →
      gm (𝟙 Y) y (A'.U i ⊓ A'.U j) (A'.g i j) = gm (𝟙 Y) y (B.U (idx i) ⊓ B.U (idx j)) (B.g (idx i) (idx j))) :
    LBIso A' B := by
  obtain ⟨w, hw⟩ := hB
  have cp : ChartPull (B.div A') (B.div B) (𝟙 Y) :=
    { idx := fun p => (p.1, idx p.2)
      le := fun p y hy => ⟨hy.1, le p.2 hy.2⟩
      g := by
        rintro y ⟨p1, p2⟩ ⟨q1, q2⟩ hp hq
        have hp' : y ∈ B.U p1 ⊓ A'.U p2 := hp
        have hq' : y ∈ B.U q1 ⊓ A'.U q2 := hq
        change gm (𝟙 Y) y ((B.U p1 ⊓ A'.U p2) ⊓ (B.U q1 ⊓ A'.U q2)) (res _ (B.g p1 q1) * (res _ (A'.g p2 q2))⁻¹) =
          gm (𝟙 Y) y ((B.U p1 ⊓ B.U (idx p2)) ⊓ (B.U q1 ⊓ B.U (idx q2)))
            (res _ (B.g p1 q1) * (res _ (B.g (idx p2) (idx q2)))⁻¹)
        rw [map_mul, map_mul, map_inv, map_inv, gm_res_eq_gm (𝟙 Y) y, gm_res_eq_gm (𝟙 Y) y, gm_res_eq_gm (𝟙 Y) y,
          gm_res_eq_gm (𝟙 Y) y, hg y p2 q2 hp'.2 hq'.2]
        all_goals first
          | exact ⟨hp', hq'⟩
          | exact ⟨⟨hp'.1, le _ hp'.2⟩, ⟨hq'.1, le _ hq'.2⟩⟩ }
  obtain ⟨t, ht⟩ := gen_chartPull cp w hw
  exact ⟨t, ht⟩

theorem iso_pull_pull {X Y Z : Scheme.{0}} {L : LB X} (hL : L.IsLB) (a : Y ⟶ X) (d : Z ⟶ Y) :
    LBIso ((L.pull a).pull d) (L.pull (d ≫ a)) := by
  have base : LBIso (L.pull (d ≫ a)) (L.pull (d ≫ a)) :=
    exists_iso_linComb hL (fun _ : PUnit => d ≫ a) (fun _ => 1) (fun _ _ _ => rfl)
  have le : ∀ K : ((L.pull a).pull d).ι, ((L.pull a).pull d).U K ≤ (L.pull (d ≫ a)).U (fun _ => K ⟨⟩ ⟨⟩) :=
    fun K y hy => by
      have h1 : d y ∈ (L.pull a).U (K ⟨⟩) := mem_pull.1 hy
      have h2 : a (d y) ∈ L.U (K ⟨⟩ ⟨⟩) := mem_pull.1 h1
      exact mem_pull.2 h2
  refine lbIso_of_chart_le_of_gm_transition_eq base (fun K _ => K ⟨⟩ ⟨⟩) le ?_
  intro y K K' hK hK'
  rw [gm_pull_g (L.pull a) d (𝟙 Z) y K K' hK hK', gm_pull_g L (d ≫ a) (𝟙 Z) y _ _ (le K hK) (le K' hK')]
  simp only [Category.id_comp]
  rw [gm_pull_g L a d y (K ⟨⟩) (K' ⟨⟩) (mem_pull.1 hK) (mem_pull.1 hK')]

theorem iso_pull_id {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) : LBIso L (L.pull (𝟙 X)) := by
  have base : LBIso (L.pull (𝟙 X)) (L.pull (𝟙 X)) :=
    exists_iso_linComb hL (fun _ : PUnit => 𝟙 X) (fun _ => 1) (fun _ _ _ => rfl)
  have le : ∀ i : L.ι, L.U i ≤ (L.pull (𝟙 X)).U (fun _ => i) := fun i y hy => mem_pull.2 hy
  refine lbIso_of_chart_le_of_gm_transition_eq base (fun i _ => i) le ?_
  intro y i j hi hj
  rw [gm_pull_g L (𝟙 X) (𝟙 X) y _ _ (le i hi) (le j hj), Category.id_comp]

variable {h k : ℕ} {B B' B'' : Type} [CommRing B] [CommRing B'] [CommRing B''] {ζ : B} {ζ' : B'} {ζ'' : B''}
  {S S' S'' : Scheme.{0}} {s : S ⟶ Sp B} {s' : S' ⟶ Sp B'} {s'' : S'' ⟶ Sp B''}

theorem pb_id (c : SiegPre h k ζ s) : SiegPB c c (𝟙 _) := by
  unfold SiegPB
  have : IsMonHom (Iso.refl c.A).hom := by
    show IsMonHom (𝟙 c.A)
    infer_instance
  refine ⟨𝟙 _, 𝟙 _, ?_, ?_, iso_pull_id c.isLB, fun a => by simp⟩
  · exact (isGrpPullback_of_iso (Iso.refl c.A)).congr rfl rfl
  · unfold Geo.Tor.IsSquare
    simp

theorem pb_comp {c : SiegPre h k ζ s} {c' : SiegPre h k ζ' s'} {c'' : SiegPre h k ζ'' s''} {f : S' ⟶ S}
    {f' : S'' ⟶ S'} (m : SiegPB c' c f) (m' : SiegPB c'' c' f') : SiegPB c'' c (f' ≫ f) := by
  unfold SiegPB at m m' ⊢
  obtain ⟨φ, φ₂, hg, ⟨hs1, hs2⟩, hl, hlev⟩ := m
  obtain ⟨ψ, ψ₂, hg', ⟨ht1, ht2⟩, hl', hlev'⟩ := m'
  refine ⟨ψ ≫ φ, ψ₂ ≫ φ₂, hg'.comp hg, ?_, ?_, fun a => ?_⟩
  · unfold Geo.Tor.IsSquare
    constructor
    · rw [Category.assoc, hs1, ← Category.assoc, ht1, Category.assoc]
    · rw [Category.assoc, hs2, ← Category.assoc, ht2, Category.assoc]
  · exact LBIso.trans c''.isLB (pull_isLB c'.isLB _) (pull_isLB c.isLB _) hl'
      (LBIso.trans (pull_isLB c'.isLB _) (pull_isLB (pull_isLB c.isLB _) _) (pull_isLB c.isLB _)
        (iso_pull ψ₂ hl) (iso_pull_pull c.isLB φ₂ ψ₂))
  · rw [← Category.assoc, hlev' a, Category.assoc, hlev a, ← Category.assoc]

private theorem hom_ext_tensor_left_of_fst_snd_eq {T : Scheme.{0}} {A : Over T} {X : Scheme.{0}} {a b : X ⟶ (A ⊗ A).left}
    (h₁ : a ≫ (fst A A).left = b ≫ (fst A A).left) (h₂ : a ≫ (snd A A).left = b ≫ (snd A A).left) : a = b := by
  have hw : b ≫ (A ⊗ A).hom = a ≫ (A ⊗ A).hom := by
    rw [← Over.w (fst A A), ← Category.assoc, ← Category.assoc, h₁]
  have key : (Over.homMk a rfl : Over.mk (a ≫ (A ⊗ A).hom) ⟶ A ⊗ A) = Over.homMk b hw := by
    apply CartesianMonoidalCategory.hom_ext
    · ext
      simpa only [Over.comp_left, Over.homMk_left] using h₁
    · ext
      simpa only [Over.comp_left, Over.homMk_left] using h₂
  exact congrArg CommaMorphism.left key

theorem pb_cancel {c : SiegPre h k ζ s} {c' : SiegPre h k ζ' s'} {c'' : SiegPre h k ζ'' s''} {f : S' ⟶ S}
    {f' : S'' ⟶ S'} (m : SiegPB c' c f) (n : SiegPB c'' c (f' ≫ f)) : SiegPB c'' c' f' := by
  unfold SiegPB at m n ⊢
  obtain ⟨φ, φ₂, hg, ⟨hs1, hs2⟩, hl, hlev⟩ := m
  obtain ⟨ψ, ψ₂, hn, ⟨ht1, ht2⟩, hln, hlevn⟩ := n
  have hw : ψ ≫ c.A.hom = (c''.A.hom ≫ f') ≫ f := by rw [hn.1.w, Category.assoc]
  obtain ⟨χ, hχ1, hχ2⟩ : ∃ χ : c''.A.left ⟶ c'.A.left, χ ≫ φ = ψ ∧ χ ≫ c'.A.hom = c''.A.hom ≫ f' :=
    ⟨hg.1.lift ψ (c''.A.hom ≫ f') hw, hg.1.lift_fst _ _ _, hg.1.lift_snd _ _ _⟩
  have hgc : IsGrpPullback c''.A c'.A f' χ := IsGrpPullback.cancel hg (hn.congr rfl hχ1.symm) hχ2
  have q1 : ((fst c''.A c''.A).left ≫ χ) ≫ c'.A.hom = (Over.mk ((c''.A ⊗ c''.A).hom ≫ f')).hom := by
    rw [Category.assoc, hχ2, ← Category.assoc, Over.w (fst c''.A c''.A)]
    rfl
  have q2 : ((snd c''.A c''.A).left ≫ χ) ≫ c'.A.hom = (Over.mk ((c''.A ⊗ c''.A).hom ≫ f')).hom := by
    rw [Category.assoc, hχ2, ← Category.assoc, Over.w (snd c''.A c''.A)]
    rfl
  obtain ⟨χ₂, hq1, hq2⟩ : ∃ χ₂ : (c''.A ⊗ c''.A).left ⟶ (c'.A ⊗ c'.A).left,
      χ₂ ≫ (fst c'.A c'.A).left = (fst c''.A c''.A).left ≫ χ ∧
      χ₂ ≫ (snd c'.A c'.A).left = (snd c''.A c''.A).left ≫ χ := by
    refine ⟨(lift (Over.homMk _ q1 : Over.mk ((c''.A ⊗ c''.A).hom ≫ f') ⟶ c'.A) (Over.homMk _ q2)).left, ?_, ?_⟩
    · rw [← Over.comp_left, lift_fst]
      rfl
    · rw [← Over.comp_left, lift_snd]
      rfl
  have e : χ₂ ≫ φ₂ = ψ₂ := by
    apply hom_ext_tensor_left_of_fst_snd_eq
    · rw [Category.assoc, hs1, ← Category.assoc, hq1, Category.assoc, hχ1, ht1]
    · rw [Category.assoc, hs2, ← Category.assoc, hq2, Category.assoc, hχ1, ht2]
  refine ⟨χ, χ₂, hgc, ⟨hq1, hq2⟩, ?_, fun a => ?_⟩
  · rw [← e] at hln
    exact LBIso.trans c''.isLB (pull_isLB c.isLB _) (pull_isLB c'.isLB _) hln
      (LBIso.symm (LBIso.trans (pull_isLB c'.isLB _) (pull_isLB (pull_isLB c.isLB _) _) (pull_isLB c.isLB _)
        (iso_pull χ₂ hl) (iso_pull_pull c.isLB φ₂ χ₂)))
  · apply hg.1.hom_ext
    · simp only [Category.assoc, hχ1, hlevn, hlev]
    · simp only [Category.assoc, hχ2]
      rw [reassoc_of% (Over.w (c''.lev a)), Over.w (c'.lev a)]
      simp

theorem id_comp_cancel : ∀ (h k : ℕ) (B B' B'' : Type) [CommRing B] [CommRing B'] [CommRing B''] (ζ : B) (ζ' : B') (ζ'' : B'') (S S' S'' : Scheme.{0}) (s : S ⟶ Sp B) (s' : S' ⟶ Sp B') (s'' : S'' ⟶ Sp B'') (c : SiegPre h k ζ s) (c' : SiegPre h k ζ' s') (c'' : SiegPre h k ζ'' s'') (f : S' ⟶ S) (f' : S'' ⟶ S'), SiegPB c c (𝟙 _) ∧ (SiegPB c' c f → (SiegPB c'' c' f' ↔ SiegPB c'' c (f' ≫ f))) := by
  intro h k B B' B'' _ _ _ ζ ζ' ζ'' S S' S'' s s' s'' c c' c'' f f'
  exact ⟨pb_id c, fun m => ⟨fun m' => pb_comp m m', fun n => pb_cancel m n⟩⟩

end GlobalTheory.SiegelPullComp
