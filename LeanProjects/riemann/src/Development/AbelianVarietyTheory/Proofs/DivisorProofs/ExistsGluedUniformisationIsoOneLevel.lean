import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusHomOfIff
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TwistBaseChangeAndValuationStatements
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MK
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RosatiAdjointAbelianPartAndClassifyingMapLinear
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMumfordGeneratorAbelianPartAtLevelImports
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two
open GlobalTheory.HomMum

noncomputable section

namespace GlobalTheory.Mum.Two.GlueLevel

section General

variable {X₁ X₂ B₁ B₂ H₁ H₂ : Scheme.{0}} {M₁ : LB B₁} {M₂ : LB B₂} {L₁ : LB H₁} {L₂ : LB H₂}

theorem map_inl_apply (f₁ : X₁ ⟶ B₁) (f₂ : X₂ ⟶ B₂) (x : X₁) :
    (coprod.map f₁ f₂) ((coprod.inl : X₁ ⟶ X₁ ⨿ X₂) x) = (coprod.inl : B₁ ⟶ B₁ ⨿ B₂) (f₁ x) := by
  change ((coprod.inl : X₁ ⟶ X₁ ⨿ X₂) ≫ coprod.map f₁ f₂) x = _
  rw [coprod.inl_map]; rfl

theorem map_inr_apply (f₁ : X₁ ⟶ B₁) (f₂ : X₂ ⟶ B₂) (x : X₂) :
    (coprod.map f₁ f₂) ((coprod.inr : X₂ ⟶ X₁ ⨿ X₂) x) = (coprod.inr : B₂ ⟶ B₁ ⨿ B₂) (f₂ x) := by
  change ((coprod.inr : X₂ ⟶ X₁ ⨿ X₂) ≫ coprod.map f₁ f₂) x = _
  rw [coprod.inr_map]; rfl

theorem mem_pull_inl (M₁ : LB B₁) (M₂ : LB B₂) (f₁ : X₁ ⟶ B₁) (f₂ : X₂ ⟶ B₂) (x : X₁)
    (J : PUnit → (join M₁ M₂).ι) :
    (coprod.inl : X₁ ⟶ X₁ ⨿ X₂) x ∈ ((join M₁ M₂).pull (coprod.map f₁ f₂)).U J ↔
      x ∈ (M₁.pull f₁).U (fun _ => (J PUnit.unit).1) := by
  rw [mem_pull, mem_pull, map_inl_apply]
  exact (isPart_inl M₁ M₂).mem _ _

theorem mem_pull_inr (M₁ : LB B₁) (M₂ : LB B₂) (f₁ : X₁ ⟶ B₁) (f₂ : X₂ ⟶ B₂) (x : X₂)
    (J : PUnit → (join M₁ M₂).ι) :
    (coprod.inr : X₂ ⟶ X₁ ⨿ X₂) x ∈ ((join M₁ M₂).pull (coprod.map f₁ f₂)).U J ↔
      x ∈ (M₂.pull f₂).U (fun _ => (J PUnit.unit).2) := by
  rw [mem_pull, mem_pull, map_inr_apply]
  exact (isPart_inr M₁ M₂).mem _ _

end General

section Glue

variable {X₁ X₂ B₁ B₂ H₁ H₂ : Scheme.{0}} {M₁ : LB B₁} {M₂ : LB B₂} {L₁ : LB H₁} {L₂ : LB H₂}
  {p₁ : X₁ ⟶ B₁} {p₂ : X₂ ⟶ B₂} {f₁ : X₁ ⟶ H₁} {f₂ : X₂ ⟶ H₂}

theorem gm_div_inl (x : X₁) (i j : (PUnit → (join M₁ M₂).ι) × (PUnit → (join L₁ L₂).ι))
    (hi : (coprod.inl : X₁ ⟶ X₁ ⨿ X₂) x ∈
      (LB.div ((join M₁ M₂).pull (coprod.map p₁ p₂)) ((join L₁ L₂).pull (coprod.map f₁ f₂))).U i)
    (hj : (coprod.inl : X₁ ⟶ X₁ ⨿ X₂) x ∈
      (LB.div ((join M₁ M₂).pull (coprod.map p₁ p₂)) ((join L₁ L₂).pull (coprod.map f₁ f₂))).U j) :
    gm coprod.inl x _
        ((LB.div ((join M₁ M₂).pull (coprod.map p₁ p₂)) ((join L₁ L₂).pull (coprod.map f₁ f₂))).g i j) =
      gm (𝟙 X₁) x _ ((LB.div (M₁.pull p₁) (L₁.pull f₁)).g
        (fun _ => (i.1 PUnit.unit).1, fun _ => (i.2 PUnit.unit).1)
        (fun _ => (j.1 PUnit.unit).1, fun _ => (j.2 PUnit.unit).1)) := by
  obtain ⟨I₁, K₁⟩ := i
  obtain ⟨I₂, K₂⟩ := j
  have a₁ := mem_pull.1 hi.1
  have a₂ := mem_pull.1 hj.1
  have b₁ := mem_pull.1 hi.2
  have b₂ := mem_pull.1 hj.2
  rw [map_inl_apply] at a₁ a₂ b₁ b₂
  have a₁' := ((isPart_inl M₁ M₂).mem _ _).1 a₁
  have a₂' := ((isPart_inl M₁ M₂).mem _ _).1 a₂
  have b₁' := ((isPart_inl L₁ L₂).mem _ _).1 b₁
  have b₂' := ((isPart_inl L₁ L₂).mem _ _).1 b₂
  have d := gm_div_g (L := join M₁ M₂) (F := coprod.map p₁ p₂) (L' := (join L₁ L₂).pull (coprod.map f₁ f₂))
    coprod.inl x (I₁ PUnit.unit) (I₂ PUnit.unit) K₁ K₂ (mem_pull.1 hi.1) (mem_pull.1 hj.1) hi.2 hj.2
  have d₁ := gm_div_g (L := M₁) (F := p₁) (L' := L₁.pull f₁) (𝟙 X₁) x (I₁ PUnit.unit).1 (I₂ PUnit.unit).1
    (fun _ => (K₁ PUnit.unit).1) (fun _ => (K₂ PUnit.unit).1) a₁' a₂' (mem_pull.2 b₁') (mem_pull.2 b₂')
  refine d.trans (Eq.trans ?_ d₁.symm)
  rw [gm_pull_g (join L₁ L₂) (coprod.map f₁ f₂) coprod.inl x K₁ K₂ hi.2 hj.2,
    gm_pull_g L₁ f₁ (𝟙 X₁) x _ _ (mem_pull.2 b₁') (mem_pull.2 b₂'), coprod.inl_map, coprod.inl_map,
    (isPart_inl M₁ M₂).g _ p₁ x _ _ a₁' a₂', (isPart_inl L₁ L₂).g _ f₁ x _ _ b₁' b₂', Category.id_comp,
    Category.id_comp]

theorem gm_div_inr (x : X₂) (i j : (PUnit → (join M₁ M₂).ι) × (PUnit → (join L₁ L₂).ι))
    (hi : (coprod.inr : X₂ ⟶ X₁ ⨿ X₂) x ∈
      (LB.div ((join M₁ M₂).pull (coprod.map p₁ p₂)) ((join L₁ L₂).pull (coprod.map f₁ f₂))).U i)
    (hj : (coprod.inr : X₂ ⟶ X₁ ⨿ X₂) x ∈
      (LB.div ((join M₁ M₂).pull (coprod.map p₁ p₂)) ((join L₁ L₂).pull (coprod.map f₁ f₂))).U j) :
    gm coprod.inr x _
        ((LB.div ((join M₁ M₂).pull (coprod.map p₁ p₂)) ((join L₁ L₂).pull (coprod.map f₁ f₂))).g i j) =
      gm (𝟙 X₂) x _ ((LB.div (M₂.pull p₂) (L₂.pull f₂)).g
        (fun _ => (i.1 PUnit.unit).2, fun _ => (i.2 PUnit.unit).2)
        (fun _ => (j.1 PUnit.unit).2, fun _ => (j.2 PUnit.unit).2)) := by
  obtain ⟨I₁, K₁⟩ := i
  obtain ⟨I₂, K₂⟩ := j
  have a₁ := mem_pull.1 hi.1
  have a₂ := mem_pull.1 hj.1
  have b₁ := mem_pull.1 hi.2
  have b₂ := mem_pull.1 hj.2
  rw [map_inr_apply] at a₁ a₂ b₁ b₂
  have a₁' := ((isPart_inr M₁ M₂).mem _ _).1 a₁
  have a₂' := ((isPart_inr M₁ M₂).mem _ _).1 a₂
  have b₁' := ((isPart_inr L₁ L₂).mem _ _).1 b₁
  have b₂' := ((isPart_inr L₁ L₂).mem _ _).1 b₂
  have d := gm_div_g (L := join M₁ M₂) (F := coprod.map p₁ p₂) (L' := (join L₁ L₂).pull (coprod.map f₁ f₂))
    coprod.inr x (I₁ PUnit.unit) (I₂ PUnit.unit) K₁ K₂ (mem_pull.1 hi.1) (mem_pull.1 hj.1) hi.2 hj.2
  have d₁ := gm_div_g (L := M₂) (F := p₂) (L' := L₂.pull f₂) (𝟙 X₂) x (I₁ PUnit.unit).2 (I₂ PUnit.unit).2
    (fun _ => (K₁ PUnit.unit).2) (fun _ => (K₂ PUnit.unit).2) a₁' a₂' (mem_pull.2 b₁') (mem_pull.2 b₂')
  refine d.trans (Eq.trans ?_ d₁.symm)
  rw [gm_pull_g (join L₁ L₂) (coprod.map f₁ f₂) coprod.inr x K₁ K₂ hi.2 hj.2,
    gm_pull_g L₂ f₂ (𝟙 X₂) x _ _ (mem_pull.2 b₁') (mem_pull.2 b₂'), coprod.inr_map, coprod.inr_map,
    (isPart_inr M₁ M₂).g _ p₂ x _ _ a₁' a₂', (isPart_inr L₁ L₂).g _ f₂ x _ _ b₁' b₂', Category.id_comp,
    Category.id_comp]

theorem exists_iso_glue (w₁ : LB.Iso (L₁.pull f₁) (M₁.pull p₁)) (w₂ : LB.Iso (L₂.pull f₂) (M₂.pull p₂))
    (hw₁ : w₁.IsGen) (hw₂ : w₂.IsGen) :
    ∃ W : LB.Iso ((join L₁ L₂).pull (coprod.map f₁ f₂)) ((join M₁ M₂).pull (coprod.map p₁ p₂)), W.IsGen ∧
      (∀ (Z : Scheme.{0}) (r : Z ⟶ X₁) (z : Z) (j : (join M₁ M₂).ι) (k : (join L₁ L₂).ι), p₁ (r z) ∈ M₁.U j.1 →
        f₁ (r z) ∈ L₁.U k.1 → gw W (r ≫ coprod.inl) z j (fun _ => k) = gw w₁ r z j.1 (fun _ => k.1)) ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ X₂) (z : Z) (j : (join M₁ M₂).ι) (k : (join L₁ L₂).ι), p₂ (r z) ∈ M₂.U j.2 →
        f₂ (r z) ∈ L₂.U k.2 → gw W (r ≫ coprod.inr) z j (fun _ => k) = gw w₂ r z j.2 (fun _ => k.2) := by
  have key : ∀ p : (PUnit → (join M₁ M₂).ι) × (PUnit → (join L₁ L₂).ι),
      ∃ a : Γ(X₁ ⨿ X₂,
        (LB.div ((join M₁ M₂).pull (coprod.map p₁ p₂)) ((join L₁ L₂).pull (coprod.map f₁ f₂))).U p)ˣ,
      (∀ (Z : Scheme.{0}) (ψ : Z ⟶ X₁) (z : Z), (coprod.inl : X₁ ⟶ X₁ ⨿ X₂) (ψ z) ∈
          (LB.div ((join M₁ M₂).pull (coprod.map p₁ p₂)) ((join L₁ L₂).pull (coprod.map f₁ f₂))).U p →
        gm (ψ ≫ coprod.inl) z _ a =
          gm ψ z _ (w₁.s (fun _ => (p.1 PUnit.unit).1, fun _ => (p.2 PUnit.unit).1))) ∧
      ∀ (Z : Scheme.{0}) (ψ : Z ⟶ X₂) (z : Z), (coprod.inr : X₂ ⟶ X₁ ⨿ X₂) (ψ z) ∈
          (LB.div ((join M₁ M₂).pull (coprod.map p₁ p₂)) ((join L₁ L₂).pull (coprod.map f₁ f₂))).U p →
        gm (ψ ≫ coprod.inr) z _ a =
          gm ψ z _ (w₂.s (fun _ => (p.1 PUnit.unit).2, fun _ => (p.2 PUnit.unit).2)) := fun p =>
    exists_glue ((LB.div ((join M₁ M₂).pull (coprod.map p₁ p₂)) ((join L₁ L₂).pull (coprod.map f₁ f₂))).U p)
      ((LB.div (M₁.pull p₁) (L₁.pull f₁)).U (fun _ => (p.1 PUnit.unit).1, fun _ => (p.2 PUnit.unit).1))
      ((LB.div (M₂.pull p₂) (L₂.pull f₂)).U (fun _ => (p.1 PUnit.unit).2, fun _ => (p.2 PUnit.unit).2))
      (fun x hx => ⟨(mem_pull_inl M₁ M₂ p₁ p₂ x _).1 hx.1, (mem_pull_inl L₁ L₂ f₁ f₂ x _).1 hx.2⟩)
      (fun x hx => ⟨(mem_pull_inr M₁ M₂ p₁ p₂ x _).1 hx.1, (mem_pull_inr L₁ L₂ f₁ f₂ x _).1 hx.2⟩) _ _
  choose s hs₁ hs₂ using key
  let W : LB.Iso ((join L₁ L₂).pull (coprod.map f₁ f₂)) ((join M₁ M₂).pull (coprod.map p₁ p₂)) := ⟨s⟩
  refine ⟨W, fun i j => unit_ext_coprod (fun x hx => ?_) (fun x hx => ?_), fun Z r z j k hj hk => ?_,
    fun Z r z j k hj hk => ?_⟩
  · have e₁ := hs₁ i X₁ (𝟙 _) x hx.1
    have e₂ := hs₁ j X₁ (𝟙 _) x hx.2
    rw [Category.id_comp] at e₁ e₂
    have m₁ : x ∈ (LB.div (M₁.pull p₁) (L₁.pull f₁)).U
        (fun _ => (i.1 PUnit.unit).1, fun _ => (i.2 PUnit.unit).1) :=
      ⟨(mem_pull_inl M₁ M₂ p₁ p₂ x _).1 hx.1.1, (mem_pull_inl L₁ L₂ f₁ f₂ x _).1 hx.1.2⟩
    have m₂ : x ∈ (LB.div (M₁.pull p₁) (L₁.pull f₁)).U
        (fun _ => (j.1 PUnit.unit).1, fun _ => (j.2 PUnit.unit).1) :=
      ⟨(mem_pull_inl M₁ M₂ p₁ p₂ x _).1 hx.2.1, (mem_pull_inl L₁ L₂ f₁ f₂ x _).1 hx.2.2⟩
    have h := congrArg (gm (𝟙 X₁) x _) (hw₁ (fun _ => (i.1 PUnit.unit).1, fun _ => (i.2 PUnit.unit).1)
      (fun _ => (j.1 PUnit.unit).1, fun _ => (j.2 PUnit.unit).1))
    have m : x ∈ (LB.div (M₁.pull p₁) (L₁.pull f₁)).U (fun _ => (i.1 PUnit.unit).1, fun _ => (i.2 PUnit.unit).1) ⊓
        (LB.div (M₁.pull p₁) (L₁.pull f₁)).U (fun _ => (j.1 PUnit.unit).1, fun _ => (j.2 PUnit.unit).1) := ⟨m₁, m₂⟩
    rw [map_mul, gm_res _ x _ m, gm_res _ x _ m] at h
    rw [map_mul, gm_res _ x _ hx, gm_res _ x _ hx, gm_div_inl x i j hx.1 hx.2]
    exact e₁.trans (h.trans (congrArg _ e₂.symm))
  · have e₁ := hs₂ i X₂ (𝟙 _) x hx.1
    have e₂ := hs₂ j X₂ (𝟙 _) x hx.2
    rw [Category.id_comp] at e₁ e₂
    have m₁ : x ∈ (LB.div (M₂.pull p₂) (L₂.pull f₂)).U
        (fun _ => (i.1 PUnit.unit).2, fun _ => (i.2 PUnit.unit).2) :=
      ⟨(mem_pull_inr M₁ M₂ p₁ p₂ x _).1 hx.1.1, (mem_pull_inr L₁ L₂ f₁ f₂ x _).1 hx.1.2⟩
    have m₂ : x ∈ (LB.div (M₂.pull p₂) (L₂.pull f₂)).U
        (fun _ => (j.1 PUnit.unit).2, fun _ => (j.2 PUnit.unit).2) :=
      ⟨(mem_pull_inr M₁ M₂ p₁ p₂ x _).1 hx.2.1, (mem_pull_inr L₁ L₂ f₁ f₂ x _).1 hx.2.2⟩
    have h := congrArg (gm (𝟙 X₂) x _) (hw₂ (fun _ => (i.1 PUnit.unit).2, fun _ => (i.2 PUnit.unit).2)
      (fun _ => (j.1 PUnit.unit).2, fun _ => (j.2 PUnit.unit).2))
    have m : x ∈ (LB.div (M₂.pull p₂) (L₂.pull f₂)).U (fun _ => (i.1 PUnit.unit).2, fun _ => (i.2 PUnit.unit).2) ⊓
        (LB.div (M₂.pull p₂) (L₂.pull f₂)).U (fun _ => (j.1 PUnit.unit).2, fun _ => (j.2 PUnit.unit).2) := ⟨m₁, m₂⟩
    rw [map_mul, gm_res _ x _ m, gm_res _ x _ m] at h
    rw [map_mul, gm_res _ x _ hx, gm_res _ x _ hx, gm_div_inr x i j hx.1 hx.2]
    exact e₁.trans (h.trans (congrArg _ e₂.symm))
  · exact hs₁ (fun _ => j, fun _ => k) Z r z
      ⟨(mem_pull_inl M₁ M₂ p₁ p₂ _ _).2 (mem_pull.2 hj), (mem_pull_inl L₁ L₂ f₁ f₂ _ _).2 (mem_pull.2 hk)⟩
  · exact hs₂ (fun _ => j, fun _ => k) Z r z
      ⟨(mem_pull_inr M₁ M₂ p₁ p₂ _ _).2 (mem_pull.2 hj), (mem_pull_inr L₁ L₂ f₁ f₂ _ _).2 (mem_pull.2 hk)⟩

end Glue

theorem exists_iso_level : ∀ {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D₁ D₂ : DegData R I} {A₁ A₂ : PolAV (Sp (FractionRing R))} {G₁ G₂ : Over (Sp R)} [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂] (U₁ : UnifPre I D₁ A₁ G₁) (U₂ : UnifPre I D₂ A₂ G₂) (e : ℕ), ∃ W : LB.Iso ((join U₁.LG.L U₂.LG.L).pull (coprod.map (fstG I e G₁).left (fstG I e G₂).left)) ((JN D₁.toPre D₂.toPre).pull (coprod.map (U₁.gt e).pG.left (U₂.gt e).pG.left)), W.IsGen ∧ (∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G₁).left) (z : Z) (j : (JN D₁.toPre D₂.toPre).ι) (k : (join U₁.LG.L U₂.LG.L).ι), (U₁.gt e).pG.left (r z) ∈ D₁.toPre.P.L.U j.1 → (fstG I e G₁).left (r z) ∈ U₁.LG.L.U k.1 → gw W (r ≫ coprod.inl) z j (fun _ => k) = gw (U₁.w e) r z j.1 (fun _ => k.1)) ∧ (∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G₂).left) (z : Z) (j : (JN D₁.toPre D₂.toPre).ι) (k : (join U₁.LG.L U₂.LG.L).ι), (U₂.gt e).pG.left (r z) ∈ D₂.toPre.P.L.U j.2 → (fstG I e G₂).left (r z) ∈ U₂.LG.L.U k.2 → gw W (r ≫ coprod.inr) z j (fun _ => k) = gw (U₂.w e) r z j.2 (fun _ => k.2)) := by
  intro R _ _ I D₁ D₂ A₁ A₂ G₁ G₂ _ _ _ _ U₁ U₂ e
  exact exists_iso_glue (U₁.w e) (U₂.w e) (U₁.w_gen e) (U₂.w_gen e)

end GlobalTheory.Mum.Two.GlueLevel
