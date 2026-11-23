import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusHomOfIff
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TwistBaseChangeAndValuationStatements
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationEndomorphismsToCompleteDvr
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two

namespace GlobalTheory.Mum.Two.ActPull

open GlobalTheory.ArcPull GlobalTheory.PullLinear
open GlobalTheory.PsiEvenPull (proj)

section Join

variable {X X' Y Y' : Scheme.{0}}

theorem isGen_part {N : LB X} {N' : LB X'} {M : LB Y} {M' : LB Y'} {e : Y ⟶ X} {e' : Y' ⟶ X'} {π : N.ι → M.ι}
    {π' : N'.ι → M'.ι} (h : IsPart N M e π) (h' : IsPart N' M' e' π') {Φ : X' ⟶ X} {Ψ : Y' ⟶ Y}
    (sq : e' ≫ Φ = Ψ ≫ e) (w : LB.Iso N' (N.pull Φ)) {v : LB.Iso M' (M.pull Ψ)} (hv : v.IsGen)
    (H : ∀ (x : Y') p q, Ψ x ∈ M.U (π p) → x ∈ M'.U (π' q) → gw w (𝟙 _ ≫ e') x p q = gw v (𝟙 _) x (π p) (π' q))
    (a b : (LB.div (N.pull Φ) N').ι) (x : Y')
    (hx : e' x ∈ (LB.div (N.pull Φ) N').U a ⊓ (LB.div (N.pull Φ) N').U b) :
    gm e' x _ (res (inf_le_left : (LB.div (N.pull Φ) N').U a ⊓ (LB.div (N.pull Φ) N').U b ≤ _) (w.s a)) =
      gm e' x _ ((LB.div (N.pull Φ) N').g a b *
        res (inf_le_right : (LB.div (N.pull Φ) N').U a ⊓ (LB.div (N.pull Φ) N').U b ≤ _) (w.s b)) := by
  obtain ⟨J, k⟩ := a
  obtain ⟨J', k'⟩ := b
  have pt : Φ (e' x) = e (Ψ x) := congrArg (fun q : Y' ⟶ X => q x) sq
  have hj := mem_pull.1 hx.1.1
  have hj' := mem_pull.1 hx.2.1
  have mj := (h.mem _ _).1 (pt ▸ hj)
  have mj' := (h.mem _ _).1 (pt ▸ hj')
  have mk := (h'.mem _ _).1 hx.1.2
  have mk' := (h'.mem _ _).1 hx.2.2
  have e₀ := (isGen_iff v).1 hv _ (𝟙 _) x _ _ _ _ mj mj' mk mk'
  rw [← H x _ _ mj mk, ← H x _ _ mj' mk', ← h.g _ (𝟙 _ ≫ Ψ) x _ _ mj mj', ← h'.g _ (𝟙 _) x _ _ mk mk',
    Category.id_comp, Category.id_comp, ← sq, ← gm_div_g e' x _ _ k k' hj hj' hx.1.2 hx.2.2] at e₀
  exact (gm_res _ x _ hx _).trans (e₀.trans ((map_mul _ _ _).trans (congrArg _ (gm_res _ x _ hx _))).symm)

variable {X₁ X₂ X₁' X₂' : Scheme.{0}} {M₁ : LB X₁} {M₂ : LB X₂} {M₁' : LB X₁'} {M₂' : LB X₂'} {Φ₁ : X₁' ⟶ X₁}
  {Φ₂ : X₂' ⟶ X₂}

theorem exists_join_iso {w₁ : LB.Iso M₁' (M₁.pull Φ₁)} {w₂ : LB.Iso M₂' (M₂.pull Φ₂)} (h₁ : w₁.IsGen) (h₂ : w₂.IsGen) :
    ∃ w : LB.Iso (join M₁' M₂') ((join M₁ M₂).pull (coprod.map Φ₁ Φ₂)), w.IsGen ∧
      ∀ (Z : Scheme.{0}) (z : Z) J J', Good (join M₁ M₂) z J → Good (join M₁' M₂') z J' →
        (∀ ψ, om w z J J' (ψ ≫ coprod.inl) = om w₁ z (rl J) (rl J') ψ) ∧
        ∀ ψ, om w z J J' (ψ ≫ coprod.inr) = om w₂ z (rr J) (rr J') ψ := by
  have s₁ : coprod.inl ≫ coprod.map Φ₁ Φ₂ = Φ₁ ≫ coprod.inl := coprod.inl_map _ _
  have s₂ : coprod.inr ≫ coprod.map Φ₁ Φ₂ = Φ₂ ≫ coprod.inr := coprod.inr_map _ _
  have p₁ : ∀ x, coprod.map Φ₁ Φ₂ ((coprod.inl : X₁' ⟶ _) x) = (coprod.inl : X₁ ⟶ _) (Φ₁ x) :=
    fun x => congrArg (fun q : X₁' ⟶ X₁ ⨿ X₂ => q x) s₁
  have p₂ : ∀ x, coprod.map Φ₁ Φ₂ ((coprod.inr : X₂' ⟶ _) x) = (coprod.inr : X₂ ⟶ _) (Φ₂ x) :=
    fun x => congrArg (fun q : X₂' ⟶ X₁ ⨿ X₂ => q x) s₂
  choose a ha₁ ha₂ using fun i : (LB.div ((join M₁ M₂).pull (coprod.map Φ₁ Φ₂)) (join M₁' M₂')).ι =>
    exists_glue ((LB.div ((join M₁ M₂).pull (coprod.map Φ₁ Φ₂)) (join M₁' M₂')).U i)
      ((M₁.pull Φ₁).U (fun _ => (i.1 PUnit.unit).1) ⊓ M₁'.U i.2.1)
      ((M₂.pull Φ₂).U (fun _ => (i.1 PUnit.unit).2) ⊓ M₂'.U i.2.2)
      (fun x hx => ⟨mem_pull.2 ((mem_jU_inl _ _ _).1 (p₁ x ▸ mem_pull.1 hx.1)), (mem_jU_inl _ _ _).1 hx.2⟩)
      (fun x hx => ⟨mem_pull.2 ((mem_jU_inr _ _ _).1 (p₂ x ▸ mem_pull.1 hx.1)), (mem_jU_inr _ _ _).1 hx.2⟩)
      (w₁.s (fun _ => (i.1 PUnit.unit).1, i.2.1)) (w₂.s (fun _ => (i.1 PUnit.unit).2, i.2.2))
  let w : LB.Iso (join M₁' M₂') ((join M₁ M₂).pull (coprod.map Φ₁ Φ₂)) := ⟨a⟩
  have v₁ : ∀ (Z : Scheme.{0}) (ψ : Z ⟶ X₁') (z : Z) (p : (join M₁ M₂).ι) (q : (join M₁' M₂').ι),
      Φ₁ (ψ z) ∈ M₁.U p.1 → ψ z ∈ M₁'.U q.1 → gw w (ψ ≫ coprod.inl) z p q = gw w₁ ψ z p.1 q.1 :=
    fun Z ψ z p q hp hq => ha₁ (fun _ => p, q) Z ψ z
      ⟨mem_pull.2 ((p₁ (ψ z)).symm ▸ (mem_jU_inl _ _ _).2 hp), (mem_jU_inl _ _ _).2 hq⟩
  have v₂ : ∀ (Z : Scheme.{0}) (ψ : Z ⟶ X₂') (z : Z) (p : (join M₁ M₂).ι) (q : (join M₁' M₂').ι),
      Φ₂ (ψ z) ∈ M₂.U p.2 → ψ z ∈ M₂'.U q.2 → gw w (ψ ≫ coprod.inr) z p q = gw w₂ ψ z p.2 q.2 :=
    fun Z ψ z p q hp hq => ha₂ (fun _ => p, q) Z ψ z
      ⟨mem_pull.2 ((p₂ (ψ z)).symm ▸ (mem_jU_inr _ _ _).2 hp), (mem_jU_inr _ _ _).2 hq⟩
  refine ⟨w, fun i j => unit_ext_coprod
    (isGen_part (isPart_inl M₁ M₂) (isPart_inl M₁' M₂') s₁ w h₁ (fun x => v₁ _ (𝟙 _) x) i j)
    (isGen_part (isPart_inr M₁ M₂) (isPart_inr M₁' M₂') s₂ w h₂ (fun x => v₂ _ (𝟙 _) x) i j),
    fun Z z J J' hJ hJ' => ⟨fun ψ => ?_, fun ψ => ?_⟩⟩
  · have e : (ψ ≫ coprod.inl) ≫ coprod.map Φ₁ Φ₂ = (ψ ≫ Φ₁) ≫ coprod.inl := by
      rw [Category.assoc, s₁, Category.assoc]
    rw [om, e]
    exact v₁ Z ψ z _ _ ((isPart_inl M₁ M₂).good hJ (ψ ≫ Φ₁)) ((isPart_inl M₁' M₂').good hJ' ψ)
  · have e : (ψ ≫ coprod.inr) ≫ coprod.map Φ₁ Φ₂ = (ψ ≫ Φ₂) ≫ coprod.inr := by
      rw [Category.assoc, s₂, Category.assoc]
    rw [om, e]
    exact v₂ Z ψ z _ _ ((isPart_inr M₁ M₂).good hJ (ψ ≫ Φ₂)) ((isPart_inr M₁' M₂').good hJ' ψ)

end Join

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R']

theorem nrm_unique {D₁ D₂ : DegPre R} {a : D₁.P.A ⟶ D₂.P.A} {x : D₁.X} {y : D₂.X} {u u' : LB.Gen (CmpLB D₁ D₂ a x y)}
    (hu : Nrm u) (hu' : Nrm u') (Z : Scheme.{0}) (r : Z ⟶ D₁.P.A.left) (z : Z) (J) (hJ : Good (JN D₁ D₂) z J) :
    val u r z J = val u' r z J :=
  gen_unique (jn_isLB D₁ D₂) D₁.P.A.hom (eSec D₁.P.A) (Over.w η[D₁.P.A]) (GlobalTheory.globalFns_holds _ _ D₁.P.isAb).2 hu.1 hu'.1
    (fun y J hJ => by
      have e := (hu.2 _ (𝟙 _) y J hJ).trans (hu'.2 _ (𝟙 _) y J hJ).symm
      rwa [Category.id_comp] at e) Z r z J hJ

theorem act_iff_of_nrm {D₁ D₂ : DegPre R} {a : D₁.P.A ⟶ D₂.P.A} {h : D₂.X →+ D₁.X}
    (u : ∀ χ, LB.Gen (CmpLB D₁ D₂ a (h χ) χ)) (hu : ∀ χ, Nrm (u χ)) {F : Type} [Field F] [Algebra (FractionRing R) F]
    (g : GtPtF D₁ F) (g' : GtPtF D₂ F) : Act D₁ D₂ a h g g' ↔ g'.b = g.b ≫ a ∧ ∀ χ z J, Good (JN D₁ D₂) z J →
      val (g'.s χ) (𝟙 _) z (rr J) = val (g.s (h χ)) (𝟙 _) z (rl J) * val (u χ) g.b.left z J :=
  and_congr_right fun _ => forall_congr' fun χ => ⟨fun H => H _ (hu χ), fun H _ hv z J hJ =>
    (H z J hJ).trans (congrArg _ (nrm_unique (hu χ) hv _ _ z J hJ))⟩

theorem prod_Oε (D : DegPre R) {T : Over (Spec (CommRingCat.of R))} (p : T ⟶ D.P.A) (x : D.X) {U : Type} [CommGroup U]
    (h : (T.left ⟶ D.P.A.left) → U) : ∏ k, h (D.Oφ p x k) ^ Oε k = (∏ k, h (D.Oφ p x k) ^ Oinvε k)⁻¹ := by
  rw [OLinEnd.prod_Oφ, OLinEnd.prod_Oφ_inv D p]
  simp only [mul_inv, inv_inv]

variable {φ : R →+* R'} {D₁ D₂ : DegPre R} {D₁' D₂' : DegPre R'} (hD₁ : IsPullDeg φ D₁ D₁') (hD₂ : IsPullDeg φ D₂ D₂')

theorem exists_u {a : D₁.P.A ⟶ D₂.P.A} {a' : D₁'.P.A ⟶ D₂'.P.A} [IsMonHom a']
    (ha : a'.left ≫ proj hD₂ = proj hD₁ ≫ a.left) {x : D₁.X} (x' : D₁'.X) (y' : D₂'.X) (hx : hD₁.xe x' = x)
    (u : LB.Gen (CmpLB D₁ D₂ a x (hD₂.xe y'))) (hu : Nrm u) :
    ∃ u' : LB.Gen (CmpLB D₁' D₂' a' x' y'), Nrm u' ∧
      ∀ (T : Over (Spec (CommRingCat.of R'))) (p : T ⟶ D₁'.P.A) (Z : Scheme.{0}) (r : Z ⟶ T.left) (z : Z) J J',
        Good (JN D₁ D₂) z J → Good (JN D₁' D₂') z J' → val u ((r ≫ p.left) ≫ proj hD₁) z J =
          (∏ k, om hD₁.w z (rl J) (rl J') (r ≫ D₁'.Oφ p x' k) ^ Oinvε k)⁻¹ *
            (∏ k, om hD₂.w z (rr J) (rr J') (r ≫ D₂'.Oφ (p ≫ a') y' k) ^ Oinvε k) * val u' (r ≫ p.left) z J' := by
  subst hx
  obtain ⟨w, hw, vw⟩ := exists_join_iso hD₁.w_gen hD₂.w_gen
  obtain ⟨u', hu', vu⟩ := exists_down_om hw (jn_isLB D₁ D₂) (jn_isLB D₁' D₂')
    (φ' := Sum.elim (fun k => D₁'.Oφ (𝟙 _) x' k ≫ coprod.inl) (fun k => D₂'.Oφ a' y' k ≫ coprod.inr)) (proj hD₁) (by
      rintro (k | k)
      · refine (Category.assoc _ _ _).trans (Eq.trans ?_ (Category.assoc _ _ _))
        rw [coprod.inl_map, ← Category.assoc]
        exact congrArg (· ≫ _)
          (TorusCoordPull.Oφ_pull hD₁ (𝟙 _) (𝟙 _) _ ((Category.id_comp _).trans (Category.comp_id _).symm) x' k)
      · refine (Category.assoc _ _ _).trans (Eq.trans ?_ (Category.assoc _ _ _))
        rw [coprod.inr_map, ← Category.assoc]
        exact congrArg (· ≫ _) (TorusCoordPull.Oφ_pull hD₂ a a' _ ha y' k)) u hu.1
  have key : ∀ (T : Over (Spec (CommRingCat.of R'))) (p : T ⟶ D₁'.P.A) (Z : Scheme.{0}) (r : Z ⟶ T.left) (z : Z) J J',
      Good (JN D₁ D₂) z J → Good (JN D₁' D₂') z J' → val u ((r ≫ p.left) ≫ proj hD₁) z J =
        (∏ k, om hD₁.w z (rl J) (rl J') (r ≫ D₁'.Oφ p x' k) ^ Oinvε k)⁻¹ *
          (∏ k, om hD₂.w z (rr J) (rr J') (r ≫ D₂'.Oφ (p ≫ a') y' k) ^ Oinvε k) * val u' (r ≫ p.left) z J' :=
    fun T p Z r z J J' hJ hJ' => by
    refine (vu Z (r ≫ p.left) z J J' hJ hJ').trans (congrArg₂ (· * ·) ?_ rfl)
    obtain ⟨o₁, o₂⟩ := vw Z z J J' hJ hJ'
    rw [Fintype.prod_sum_type, ← prod_Oε D₁' p x' (fun q => om hD₁.w z (rl J) (rl J') (r ≫ q))]
    refine congrArg₂ (· * ·) (Finset.prod_congr rfl fun k _ => congrArg (· ^ Oε k) ?_)
      (Finset.prod_congr rfl fun k _ => congrArg (· ^ Oinvε k) ?_)
    · refine Eq.trans (congrArg _ ?_) (o₁ _)
      rw [Sum.elim_inl, ← Category.assoc, Category.assoc r, WeightPf.Oφ_comp, Category.comp_id]
    · refine Eq.trans (congrArg _ ?_) (o₂ _)
      rw [Sum.elim_inr, ← Category.assoc, Category.assoc r, WeightPf.Oφ_comp]
  refine ⟨u', ⟨hu', fun Z r z J' hJ' => ?_⟩, key⟩
  obtain ⟨J, hJ⟩ := DegPull.exists_good' (jn_isLB D₁ D₂) z
  have o₁ : (1 : 𝟙_ (Over (Sp R')) ⟶ D₁'.P.A).left = eSec D₁'.P.A := Category.id_comp _
  have z₀ : ∀ (D : DegPre R') (T : Over (Spec (CommRingCat.of R'))) (χ : D.X) {U : Type} [CommGroup U]
      (f : (T.left ⟶ D.P.A.left) → U), ∏ k, f (D.Oφ (1 : T ⟶ D.P.A) χ k) ^ Oinvε k = 1 := fun D T χ U _ f => by
    rw [OLinEnd.prod_Oφ_inv, _root_.mul_one]; simp
  have e := key (𝟙_ (Over (Sp R'))) 1 Z r z J J' hJ hJ'
  rw [MonObj.one_comp, o₁] at e
  have e₁ : val u ((r ≫ eSec D₁'.P.A) ≫ proj hD₁) z J = 1 := by
    rw [Category.assoc, hD₁.he, ← Category.assoc]
    exact hu.2 Z _ z J hJ
  have e₂ := e₁.symm.trans (e.trans (congrArg₂ (· * ·) (congrArg₂ (fun a b => a⁻¹ * b)
    (z₀ D₁' (𝟙_ (Over (Sp R'))) x' (fun q => om hD₁.w z (rl J) (rl J') (r ≫ q)))
    (z₀ D₂' (𝟙_ (Over (Sp R'))) y' (fun q => om hD₂.w z (rr J) (rr J') (r ≫ q)))) rfl))
  rw [inv_mul_cancel, _root_.one_mul] at e₂
  exact e₂.symm

theorem main : ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (φ : R →+* R') (D₁ D₂ : DegPre R) (D₁' D₂' : DegPre R') (hD₁ : IsPullDeg φ D₁ D₁') (hD₂ : IsPullDeg φ D₂ D₂') (b : D₁.P.A ⟶ D₂.P.A) (h : D₂.X →+ D₁.X) (b' : D₁'.P.A ⟶ D₂'.P.A) (h' : D₂'.X →+ D₁'.X), IsMonHom b → IsMonHom b' → b' ≫ hD₂.e.hom = hD₁.e.hom ≫ (Over.pullback (specOf φ)).map b → (∀ χ, hD₁.xe (h' χ) = h (hD₂.xe χ)) → (∀ χ, ∃ u : LB.Gen (CmpLB D₁ D₂ b (h χ) χ), Nrm u) → ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] [Algebra (FractionRing R') F] (g₁ : GtPtF D₁ F) (g₂ : GtPtF D₂ F) (g₁' : GtPtF D₁' F) (g₂' : GtPtF D₂' F), IsPullGtF φ hD₁ F g₁ g₁' → IsPullGtF φ hD₂ F g₂ g₂' → (Act D₁ D₂ b h g₁ g₂ ↔ Act D₁' D₂' b' h' g₁' g₂') := by
  intro R R' _ _ _ _ φ D₁ D₂ D₁' D₂' hD₁ hD₂ a h a' h' _ _ hb hx hu F _ _ _ g₁ g₂ g₁' g₂' h₁ h₂
  have ha : a'.left ≫ proj hD₂ = proj hD₁ ≫ a.left := by
    rw [← Category.assoc, ← Over.comp_left, hb, Over.comp_left, Category.assoc, map_left_fst, Category.assoc]
  choose u hu using hu
  choose u' hu' vu using fun χ => exists_u hD₁ hD₂ ha (h' χ) χ (hx χ) (u (hD₂.xe χ)) (hu _)
  rw [act_iff_of_nrm u hu, act_iff_of_nrm u' hu']
  have hb : (g₁'.b ≫ a').left ≫ proj hD₂ = (g₁.b ≫ a).left := by
    rw [Over.comp_left, Over.comp_left, Category.assoc, ha, ← Category.assoc]
    exact congrArg (· ≫ _) h₁.1
  have hiff : g₂.b = g₁.b ≫ a ↔ g₂'.b = g₁'.b ≫ a' :=
    ⟨fun H => ext_of_iso_pullback _ hD₂.e (h₂.1.trans ((congrArg (·.left) H).trans hb.symm)),
      fun H => Over.OverMorphism.ext (h₂.1.symm.trans ((congrArg (·.left ≫ proj hD₂) H).trans hb))⟩
  rw [hiff]
  refine and_congr_right fun H => ?_
  have key : ∀ χ (y : Sp F) J J', Good (JN D₁ D₂) y J → Good (JN D₁' D₂') y J' →
      (vS (g₂.s (hD₂.xe χ)) y (rr J) = vS (g₁.s (h (hD₂.xe χ))) y (rl J) * val (Z := Sp F) (u (hD₂.xe χ)) g₁.b.left y J ↔
        vS (g₂'.s χ) y (rr J') = vS (g₁'.s (h' χ)) y (rl J') * val (Z := Sp F) (u' χ) g₁'.b.left y J') := by
    intro χ y J J' hJ hJ'
    have e₁ : vS (g₁.s (hD₁.xe (h' χ))) y (rl J) =
        (∏ k, om hD₁.w y (rl J) (rl J') (𝟙 (Sp F) ≫ D₁'.Oφ g₁'.b (h' χ) k) ^ Oinvε k) * vS (g₁'.s (h' χ)) y (rl J') :=
      (pullGt_val hD₁ h₁ (h' χ) (𝟙 _) ((isPart_inl _ _).good hJ) ((isPart_inl _ _).good hJ')).trans (congrArg₂ (· * ·)
        (OLinEnd.prod_Oφ_inv D₁' g₁'.b (h' χ) (fun q => om hD₁.w y (rl J) (rl J') (𝟙 (Sp F) ≫ q))).symm rfl)
    have e₂ : vS (g₂.s (hD₂.xe χ)) y (rr J) =
        (∏ k, om hD₂.w y (rr J) (rr J') (𝟙 (Sp F) ≫ D₂'.Oφ (g₁'.b ≫ a') χ k) ^ Oinvε k) * vS (g₂'.s χ) y (rr J') := by
      rw [← H]
      exact (pullGt_val hD₂ h₂ χ (𝟙 _) ((isPart_inr _ _).good hJ) ((isPart_inr _ _).good hJ')).trans (congrArg₂ (· * ·)
        (OLinEnd.prod_Oφ_inv D₂' g₂'.b χ (fun q => om hD₂.w y (rr J) (rr J') (𝟙 (Sp F) ≫ q))).symm rfl)
    have e₃ : val (Z := Sp F) (u (hD₂.xe χ)) g₁.b.left y J =
        (∏ k, om hD₁.w y (rl J) (rl J') (𝟙 (Sp F) ≫ D₁'.Oφ g₁'.b (h' χ) k) ^ Oinvε k)⁻¹ *
          (∏ k, om hD₂.w y (rr J) (rr J') (𝟙 (Sp F) ≫ D₂'.Oφ (g₁'.b ≫ a') χ k) ^ Oinvε k) *
          val (Z := Sp F) (u' χ) g₁'.b.left y J' :=
      (congrArg (fun q => val (Z := Sp F) (u (hD₂.xe χ)) q y J)
        ((congrArg (· ≫ proj hD₁) (Category.id_comp _)).trans h₁.1).symm).trans
        ((vu χ _ g₁'.b (Sp F) (𝟙 _) y J J' hJ hJ').trans (congrArg₂ (· * ·) rfl
          (congrArg (fun q => val (Z := Sp F) (u' χ) q y J') (Category.id_comp _))))
    rw [hx] at e₁
    rw [e₁, e₂, e₃]
    exact EndBaseChange.cancel_iff _ _ _ _ _
  constructor
  · intro H χ y J' hJ'
    obtain ⟨J, hJ⟩ := DegPull.exists_good' (jn_isLB D₁ D₂) (Z := Sp F) y
    exact (key χ y J J' hJ hJ').1 (H _ y J hJ)
  · intro H χ y J hJ
    obtain ⟨χ, rfl⟩ := hD₂.xe.surjective χ
    obtain ⟨J', hJ'⟩ := DegPull.exists_good' (jn_isLB D₁' D₂') (Z := Sp F) y
    exact (key χ y J J' hJ hJ').2 (H _ y J' hJ')

end GlobalTheory.Mum.Two.ActPull
