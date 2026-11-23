import Development.EtaleCohomology.CohomologicalPurity.LeafHtpyPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.Thom

def LeafFreeCov : Prop := ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (U V : X.Opens),
  Epi (biprod.desc ((free R).map (yoneda.map (X.homOfLE (le_sup_left : U ≤ U ⊔ V))))
    ((free R).map (yoneda.map (X.homOfLE (le_sup_right : V ≤ U ⊔ V)))))

namespace HtpyMVPf

theorem bij_pull_iso (R : Type) [CommRing R] (F : Shv R) {A B : Spc} (e : A ≅ B) (n : ℤ) :
    Function.Bijective (pull R e.hom F n) := by
  refine ⟨fun x y h => ?_, fun y => ⟨pull R e.inv F n y, ?_⟩⟩
  · have hx := pull_comp R e.inv e.hom F n x
    have hy := pull_comp R e.inv e.hom F n y
    rw [e.inv_hom_id, pull_id] at hx hy
    rw [hx, hy, h]
  · rw [← pull_comp, e.hom_inv_id, pull_id]

theorem eqv_of_sq (R : Type) [CommRing R] (F : Shv R) {A B A' B' : Spc} (f : A ⟶ B) (g : A' ⟶ B')
    (α : A ≅ A') (β : B ≅ B') (w : α.hom ≫ g = f ≫ β.hom) (hf : Eqv R f F) : Eqv R g F := by
  intro n
  have h1 : (pull R α.hom F n) ∘ (pull R g F n) = (pull R f F n) ∘ (pull R β.hom F n) := by
    funext x; simp only [Function.comp_apply, ← pull_comp, w]
  have h2 : Function.Bijective ((pull R α.hom F n) ∘ (pull R g F n)) := by
    rw [h1]; exact (hf n).comp (bij_pull_iso R F β n)
  exact (Function.Bijective.of_comp_iff' (bij_pull_iso R F α n) _).1 h2

theorem mono_sch {Y Z : Scheme.{0}} (f : Y ⟶ Z) [Mono f] : Mono (sch.map f) := by
  have hy : Mono (yoneda.map f) := by
    have : ∀ T, Mono ((yoneda.map f).app T) := fun T => by
      rw [mono_iff_injective]
      intro a b h
      exact (cancel_mono f).1 h
    exact NatTrans.mono_of_mono_app _
  have : ∀ n, Mono ((sch.map f).app n) := fun _ => hy
  exact NatTrans.mono_of_mono_app _

theorem sch_pres : PreservesLimitsOfShape WalkingCospan sch := by
  unfold sch; infer_instance

end HtpyMVPf

theorem LeafHtpyMV_of (hF : LeafFreeCov) : LeafHtpyMV := by
  intro a4 R _ F X' X p U V U' V' hU hV hI hS hu hv hi
  have cov : ∀ (Y : Scheme.{0}) (A B : Y.Opens),
      Cover2 R (sch.map (Y.homOfLE (le_sup_left : A ≤ A ⊔ B))) (sch.map (Y.homOfLE (le_sup_right : B ≤ A ⊔ B))) :=
    fun Y A B => ⟨HtpyMVPf.mono_sch _, HtpyMVPf.mono_sch _, fun _ => hF R Y A B⟩
  have eu : X'.homOfLE (le_sup_left : U' ≤ U' ⊔ V') ≫ p.resLE (U ⊔ V) (U' ⊔ V') hS =
      p.resLE U U' hU ≫ X.homOfLE (le_sup_left : U ≤ U ⊔ V) := by
    simp
  have ev : X'.homOfLE (le_sup_right : V' ≤ U' ⊔ V') ≫ p.resLE (U ⊔ V) (U' ⊔ V') hS =
      p.resLE V V' hV ≫ X.homOfLE (le_sup_right : V ≤ U ⊔ V) := by
    simp
  have hu' := congrArg sch.map eu
  have hv' := congrArg sch.map ev
  rw [sch.map_comp, sch.map_comp] at hu' hv'
  refine a4 R _ _ _ _ _ _ _ hu' hv' F (cov X' U' V') (cov X U V) hu hv ?_
  have := HtpyMVPf.sch_pres
  have P' := (isPullback_opens_inf_le (X := X') (le_sup_left : U' ≤ U' ⊔ V') (le_sup_right : V' ≤ U' ⊔ V')).map sch
  have P := (isPullback_opens_inf_le (X := X) (le_sup_left : U ≤ U ⊔ V) (le_sup_right : V ≤ U ⊔ V)).map sch
  refine HtpyMVPf.eqv_of_sq R F _ _ P'.isoPullback P.isoPullback ?_ hi
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, IsPullback.isoPullback_hom_fst_assoc, Category.assoc,
      IsPullback.isoPullback_hom_fst, ← sch.map_comp, ← sch.map_comp]
    congr 1
    simp
  · rw [Category.assoc, pullback.lift_snd, IsPullback.isoPullback_hom_snd_assoc, Category.assoc,
      IsPullback.isoPullback_hom_snd, ← sch.map_comp, ← sch.map_comp]
    congr 1
    simp

end LateralTheory.CohomologicalPurity.Thom
