import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIsFib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPowerSectionOfChartFunctions
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.VtUniq

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
open GlobalTheory.Ex.AbPartIso

noncomputable section
namespace GlobalTheory.AbPartSym

theorem exists_move {X₁ X₂ B Y Y' : Scheme.{0}} {L₁ : LB X₁} {L₂ : LB X₂} {f₁ : B ⟶ X₁} {f₂ : B ⟶ X₂}
    (w : LB.Iso (L₁.pull f₁) (L₂.pull f₂)) (hw : w.IsGen) (h₁ : L₁.IsLB) (h₂ : L₂.IsLB) {K : Type} [Fintype K]
    (φ' : K → (Y' ⟶ B)) {φ : K → (Y ⟶ X₁)} {ε : K → ℤ} (h : Y' ⟶ Y) (hc : ∀ k, φ' k ≫ f₁ = h ≫ φ k)
    (t : LB.Gen (LB.LinComb L₁ φ ε)) (ht : t.IsGen) :
    ∃ u : LB.Gen (LB.LinComb L₂ (fun k => φ' k ≫ f₂) ε), u.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) J₂ J₁,
      Good L₂ z J₂ → Good L₁ z J₁ → val u r z J₂ =
        (∏ k, gw w (r ≫ φ' k) z (J₂ ((r ≫ φ' k) ≫ f₂)) (fun _ => J₁ ((r ≫ φ' k) ≫ f₁)) ^ ε k) * val t (r ≫ h) z J₁ := by
  let c := chartPullLinComb L₁ f₁ φ' φ ε h hc
  let a : LB.Gen (LB.LinComb (L₁.pull f₁) φ' ε) := ⟨fun j => res (c.le j) (pullU h _ (t.s (c.idx j)))⟩
  have va : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) j, r z ∈ LB.wchart (L₁.pull f₁) φ' j →
      gm r z (LB.wchart (L₁.pull f₁) φ' j) (a.s j) =
        gm (r ≫ h) z (LB.wchart L₁ φ fun k => j k PUnit.unit) (t.s fun k => j k PUnit.unit) := fun Z r z j hj =>
    (gm_res r z (c.le j) hj _).trans (gm_pull r h z _ (c.le j hj) _)
  have ha : a.IsGen := ReciprocityTheory.ChartRestriction.G.Geo.Tor.isGen_of_gm a fun y j j' hj hj' => by
    rw [va _ _ y j hj, va _ _ y j' hj', Category.id_comp]
    refine (gen_trans ht h y (c.le j hj) (c.le j' hj')).trans (congrArg (· * _) ?_)
    exact ((gm_linComb L₁ φ ε h y _ _ (c.le j hj) (c.le j' hj')).symm.trans (c.g y j j' hj hj').symm).trans
      (gm_linComb (L₁.pull f₁) φ' ε (𝟙 Y') y j j' hj hj')
  obtain ⟨u, hu, hv⟩ := exists_up ((isGen_iff w).1 hw) h₂ (pull_isLB h₁ f₁) a ha
  refine ⟨u, hu, fun Z r z J₂ J₁ g₂ g₁ => ?_⟩
  have m : r z ∈ LB.wchart (L₁.pull f₁) φ' fun k _ => J₁ ((r ≫ φ' k) ≫ f₁) :=
    Set.mem_iInter.2 fun k => mem_pull.2 (g₁ ((r ≫ φ' k) ≫ f₁))
  refine (hv Z r z _ _ (g₂.mem _ r) m).trans (congrArg₂ (· * ·) (Finset.prod_congr rfl fun k _ => ?_) ?_)
  · rw [Category.assoc]
  · exact (va Z r z _ m).trans (val_of t (r ≫ h) z J₁ _ fun k => by
      rw [Category.assoc, Category.assoc, hc]).symm

variable {R : Type} [CommRing R] [IsDomain R] {D D' : DegPre R}

theorem sym_one (D : DegPre R) {Z : Over (Sp R)} {z : Z.left} {J} (hJ : Good D.P.L z J) :
    val D.sym (1 : Z ⟶ D.P.A).left z J = 1 :=
  (val_pull hJ D.sym (eSec D.P.A) Z.hom).symm.trans ((val_corr hJ D.sym_rig Z.hom).trans (val_one _))

theorem val_sym_move (hG : GlobalFnsSt) {T : Over (Sp R)} (g : T ⊗ D.P.A ⟶ D'.P.A)
    (hg : ∀ (Z : Over (Sp R)) (t : Z ⟶ T) (x y : Z ⟶ D.P.A), lift t (x * y) ≫ g = (lift t x ≫ g) * (lift t y ≫ g))
    (w : LB.Iso (D.P.L.pull (snd T D.P.A).left) (D'.P.L.pull g.left)) (hw : w.IsGen) {Z : Over (Sp R)} (t : Z ⟶ T)
    (x : Z ⟶ D.P.A) {z : Z.left} {J J'} (hJ : Good D.P.L z J) (hJ' : Good D'.P.L z J') :
    val D'.sym (lift t x ≫ g).left z J' =
      gw w (lift t x⁻¹).left z (J' (lift t x⁻¹ ≫ g).left) (fun _ => J (x⁻¹).left) *
        (gw w (lift t x).left z (J' (lift t x ≫ g).left) (fun _ => J x.left))⁻¹ * val D.sym x.left z J := by
  let ρ : ∀ {Z : Over (Sp R)} (t : Z ⟶ T), (Z ⟶ D.P.A) →* (Z ⟶ D'.P.A) := fun t =>
    MonoidHom.mk' (fun x => lift t x ≫ g) (hg _ t)
  let n : T ⊗ D.P.A ⟶ T ⊗ D.P.A := lift (fst _ _) (snd _ _)⁻¹
  have hn : ∀ {Z : Over (Sp R)} (t : Z ⟶ T) (x : Z ⟶ D.P.A), (lift t x).left ≫ n.left = (lift t x⁻¹).left :=
    fun t x => by rw [← Over.comp_left, comp_lift, lift_fst, GrpObj.comp_inv, lift_snd]
  have ng : n.left ≫ g.left = g.left ≫ (ι[D'.P.A]).left := by
    have e : n ≫ g = (lift (fst T D.P.A) (snd T D.P.A) ≫ g)⁻¹ := map_inv (ρ (fst T D.P.A)) (snd T D.P.A)
    rw [lift_fst_snd, Category.id_comp] at e
    exact congrArg (fun q => q.left) e
  obtain ⟨u, hu, hv⟩ := exists_move w hw D.P.isLB D'.P.isLB (K := Fin 2) ![n.left, 𝟙 _] (snd T D.P.A).left
    (fun k => by
      fin_cases k
      · exact congrArg (fun q => q.left) (lift_snd (fst T D.P.A) (snd T D.P.A)⁻¹)
      · exact (Category.id_comp _).trans (Category.comp_id _).symm) D.sym D.sym_gen
  have hv' : ∀ {Z : Over (Sp R)} (t : Z ⟶ T) (x : Z ⟶ D.P.A) (z : Z.left) J J', Good D.P.L z J → Good D'.P.L z J' →
      val u (lift t x).left z J' =
      gw w (lift t x⁻¹).left z (J' (lift t x⁻¹ ≫ g).left) (fun _ => J (x⁻¹).left) *
        (gw w (lift t x).left z (J' (lift t x ≫ g).left) (fun _ => J x.left))⁻¹ * val D.sym x.left z J :=
    fun t x z J J' hJ hJ' => by
      refine (hv _ _ z J' J hJ' hJ).trans ?_
      rw [Fin.prod_univ_two]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [hn, Category.comp_id, zpow_one, zpow_neg_one]
      simp only [← Over.comp_left, lift_snd]
  have key := gen_unique' D'.P.isLB
    (φ := fun k => g.left ≫ (![(ι[D'.P.A]).left, 𝟙 D'.P.A.left] : Fin 2 → _) k) (ε := ![1, -1])
    (fun V _ k => by
      rw [Fin.prod_univ_two, Fin.prod_univ_two]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [ng, Category.id_comp, Category.comp_id])
    (fst T D.P.A).left (lift (𝟙 T) (1 : T ⟶ D.P.A)).left (by rw [← Over.comp_left, lift_fst, Over.id_left])
    (ReciprocityTheory.ChartRestriction.G.Geo.Tor.surj_fst hG D.P.isAb T)
    (DVR.pullGen_isGen _ _ _ _ D'.sym_gen g.left) hu (fun y I' hI' => by
      choose I hI using fun χ : T.left ⟶ D.P.A.left => exists_chart D.P.isLB (χ y)
      have o : lift (𝟙 T) (1 : T ⟶ D.P.A) ≫ g = 1 := map_one (ρ (𝟙 T))
      rw [val_pull hI', hv' _ _ y I I' hI hI', ← Over.comp_left, inv_one, o, sym_one D hI, sym_one D' hI',
        mul_inv_cancel, _root_.one_mul]) _ (lift t x).left z J' hJ'
  exact (val_pull hJ' _ _ _).symm.trans (key.trans (hv' t x z J J' hJ hJ'))

open GlobalTheory.ThetaInValues in

theorem sym_values : GlobalFnsSt → AllIso fun {_} _ _ {_} {_} {F} _ _ {N} {N'} ν ν' {_} w f =>
    ∀ x, (N'.σ (f x) : F) * wVal ν ν' w f x = (N.σ x : F) * wVal ν ν' w f x⁻¹ := by
  intro hG R _ _ D D' F _ _ N N' ν ν' φ w f hφ hw hf x
  obtain ⟨y⟩ : Nonempty (TF (R := R) F).left := inferInstanceAs (Nonempty (PrimeSpectrum F))
  have c : ∀ a, lift (𝟙 _) (ν.eA a) ≫ φ.hom ≫ snd _ _ = ν'.eA (f a) := fun a => by
    rw [← Category.assoc, hf a, lift_snd]
  have v : ∀ a, sR y (wVal ν ν' w f a) = (gw w (lift (𝟙 (TF (R := R) F)) (ν.eA a)).left y
      (ν'.J (ν'.eA (f a)).left) (fun _ => ν.J (ν.eA a).left)).val := fun a => by
    refine toStk_valF _ _ y ?_ _
    refine ⟨mem_pull.2 ?_, mem_pull.2 ?_⟩
    · have := good ν' y (ν'.eA (f a)).left
      conv at this => enter [2]; rw [← c a]
      exact this
    · have := good ν y (ν.eA a).left
      conv at this => enter [2]; rw [← lift_snd (𝟙 (TF (R := R) F)) (ν.eA a)]
      exact this
  have key := val_sym_move hG (φ.hom ≫ snd _ _) hφ.2 w hw (𝟙 _) (ν.eA x) (good ν y) (good ν' y)
  rw [← map_inv ν.eA, c, c, sym_eq, sym_eq] at key
  refine (sR (R := R) y).injective ?_
  rw [map_mul, map_mul, v, v, ← sU_val, ← sU_val, key, ← Units.val_mul, ← Units.val_mul]
  congr 1
  rw [mul_right_comm, inv_mul_cancel_right, mul_comm]

end GlobalTheory.AbPartSym
end
