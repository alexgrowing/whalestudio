import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.WithISelf
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.LocGenOfThickenings
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SurjectiveOfComplexPointsLiftOfUniversallyClosed
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsReducedAlgebraOfSmoothOfIsNoetherianRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Relabel
noncomputable section
namespace GlobalTheory.RosMove

def rosO {S : Scheme.{0}} (A : Over S) [GrpObj A] [IsCommMonObj A] (f g : A ⟶ A) : Fin 6 → (A ⊗ A ⟶ A) :=
  ![(fst A A ≫ f) * snd A A, fst A A ≫ f, snd A A, fst A A * (snd A A ≫ g), fst A A, snd A A ≫ g]

theorem rosO_left {S : Scheme.{0}} (A : Over S) [GrpObj A] [IsCommMonObj A] (f g : A ⟶ A) (k : Fin 6) :
    (rosO A f g k).left = rosatiφ A f g k := by
  fin_cases k <;> rfl

theorem lift_rosO {S : Scheme.{0}} (A : Over S) [GrpObj A] [IsCommMonObj A] (f g : A ⟶ A) {T : Over S} (x y : T ⟶ A)
    (k : Fin 6) : lift x y ≫ rosO A f g k = ![(x ≫ f) * y, x ≫ f, y, x * (y ≫ g), x, y ≫ g] k := by
  fin_cases k <;> simp [rosO, MonObj.comp_mul]

theorem val_origin {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {L : LB A.left} {f g : A ⟶ A}
    {u : LB.Gen (LB.LinComb L (rosatiφ A f g) rosatiε)}
    (hu : LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ u (zero2 A)) (LB.oneGen L)) {T : Over S} {z : T.left} {J}
    (hJ : Good L z J) : val u (lift (1 : T ⟶ A) (1 : T ⟶ A)).left z J = 1 := by
  have e : lift (1 : T ⟶ A) (1 : T ⟶ A) = toUnit T ≫ lift η[A] η[A] := by simp [Hom.one_def]
  have := val_corr hJ hu (toUnit T).left
  rw [val_pull hJ, val_one] at this
  rw [e]; exact this

theorem val_move (hG : GlobalFnsSt) {F : Type} [Field F] [IsAlgClosed F] {S S' : Scheme.{0}} (t : Sp F ⟶ S) (t' : Sp F ⟶ S')
    {A : Over S} [GrpObj A] [IsCommMonObj A] {A' : Over S'} [GrpObj A'] [IsCommMonObj A'] (hA : IsAbelianScheme A)
    (hA' : IsAbelianScheme A') {L : LB A.left} {L' : LB A'.left} (hL : L.IsLB) (hL' : L'.IsLB)
    (Φ : (Over.mk t ⊗ A).left ⟶ A'.left) (w : LB.Iso (L.pull (snd (Over.mk t) A).left) (L'.pull Φ)) (hw : w.IsGen)
    (hΦ : Φ ≫ A'.hom = (fst (Over.mk t) A).left ≫ t') (ψ : (Over.mk t ⟶ A) →* (Over.mk t' ⟶ A'))
    (hψ : ∀ x, (lift (𝟙 (Over.mk t)) x).left ≫ Φ = (ψ x).left) (f g : A ⟶ A) [IsMonHom f] [IsMonHom g] (f' g' : A' ⟶ A')
    (hf : ∀ x, ψ (x ≫ f) = ψ x ≫ f') (hg : ∀ x, ψ (x ≫ g) = ψ x ≫ g')
    {u : LB.Gen (LB.LinComb L (rosatiφ A f g) rosatiε)} (hu : u.IsGen)
    (u₀ : LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ u (zero2 A)) (LB.oneGen L))
    {u' : LB.Gen (LB.LinComb L' (rosatiφ A' f' g') rosatiε)} (hu' : u'.IsGen)
    (u₀' : LB.Gen.Corr L' _ _ _ _ (LB.pullGen L' _ _ u' (zero2 A')) (LB.oneGen L'))
    (z : Sp F) (N) (J) (hN : Good L z N) (hJ : Good L' z J) (b b' : Over.mk t ⟶ A) :
    val u' (lift (ψ b) (ψ b')).left z J =
      (∏ k, gw w (lift (𝟙 (Over.mk t)) (lift b b' ≫ rosO A f g k)).left z (J (ψ (lift b b' ≫ rosO A f g k)).left)
        (fun _ => N (lift b b' ≫ rosO A f g k).left) ^ rosatiε k) * val u (lift b b').left z N := by
  let T : Over S := Over.mk t
  let T' : Over S' := Over.mk t'
  let Y : Over S := T ⊗ (A ⊗ A)
  let p : Y.left ⟶ Sp F := (fst T (A ⊗ A)).left
  let Y' : Over S' := Over.mk (p ≫ t')
  let Θ : (Y ⟶ A) → (Y' ⟶ A') := fun x => Over.homMk ((lift (fst T (A ⊗ A)) x).left ≫ Φ) (by
    show ((lift (fst T (A ⊗ A)) x).left ≫ Φ) ≫ A'.hom = p ≫ t'
    rw [Category.assoc, hΦ, ← Category.assoc, ← Over.comp_left, lift_fst])
  let pt : (T ⟶ A ⊗ A) → (T' ⟶ Y') := fun c => Over.homMk (lift (𝟙 T) c).left (by
    show (lift (𝟙 T) c).left ≫ (fst T (A ⊗ A)).left ≫ t' = t'
    rw [← Category.assoc, ← Over.comp_left, lift_fst]; exact Category.id_comp _)
  have hΘ : ∀ c x, pt c ≫ Θ (snd _ _ ≫ x) = ψ (c ≫ x) := fun c x => by
    ext
    show (lift (𝟙 T) c).left ≫ (lift (fst T (A ⊗ A)) (snd _ _ ≫ x)).left ≫ Φ = _
    rw [← Category.assoc, ← Over.comp_left, comp_lift, lift_fst, lift_snd_assoc, hψ]
  let H : Y' ⟶ A' ⊗ A' := lift (Θ (snd _ _ ≫ fst A A)) (Θ (snd _ _ ≫ snd A A))
  have hH : ∀ x y, pt (lift x y) ≫ H = lift (ψ x) (ψ y) := fun x y => by
    rw [comp_lift, hΘ, hΘ, lift_fst, lift_snd]
  have hr : ∀ x y k, lift (ψ x) (ψ y) ≫ rosO A' f' g' k = ψ (lift x y ≫ rosO A f g k) := fun x y k => by
    rw [lift_rosO, lift_rosO]
    fin_cases k <;> simp [hf, hg]
  have := hA.smooth
  have := hA'.proper
  have sm : Smooth (A ⊗ A).hom := by
    show Smooth (pullback.fst A.hom A.hom ≫ A.hom); infer_instance
  have sp : Smooth p := by
    show Smooth (pullback.fst t (A ⊗ A).hom); infer_instance
  have rd : IsReduced Y.left := GlobalTheory.isReduced_of_smooth_of_isReduced p
  have hE : ∀ k, (Θ (snd _ _ ≫ rosO A f g k)).left = H.left ≫ rosatiφ A' f' g' k := fun k => by
    rw [← rosO_left, ← Over.comp_left]
    refine ComplexPoints.hom_ext_of_points (X := Y.left) p A'.hom ((Over.w _).trans (Over.w _).symm) fun x hx => ?_
    let x₀ : T ⟶ Y := Over.homMk x (by
      show x ≫ Y.hom = t
      rw [← Over.w (fst T (A ⊗ A)), ← Category.assoc]
      exact (congrArg (· ≫ t) hx).trans (Category.id_comp _))
    have e : x₀ = lift (𝟙 T) (lift (x₀ ≫ snd _ _ ≫ fst A A) (x₀ ≫ snd _ _ ≫ snd A A)) := by
      refine CartesianMonoidalCategory.hom_ext _ _ ?_ ?_
      · rw [lift_fst]; ext; exact hx
      · rw [lift_snd, ← comp_lift, ← comp_lift, lift_fst_snd, Category.comp_id]
    have e' : x = (pt (lift (x₀ ≫ snd _ _ ≫ fst A A) (x₀ ≫ snd _ _ ≫ snd A A))).left := congrArg (·.left) e
    rw [e', ← Over.comp_left, ← Over.comp_left, hΘ, ← Category.assoc (pt _), hH, hr]
  let φ : Fin 6 → (Y.left ⟶ (T ⊗ A).left) := fun k => (lift (fst T (A ⊗ A)) (snd _ _ ≫ rosO A f g k)).left
  have hφ : ∀ k, φ k ≫ (snd T A).left = (snd T (A ⊗ A)).left ≫ rosatiφ A f g k := fun k => by
    rw [← rosO_left, ← Over.comp_left, ← Over.comp_left, lift_snd]
  have hφc : ∀ c k, (lift (𝟙 T) c).left ≫ φ k = (lift (𝟙 T) (c ≫ rosO A f g k)).left := fun c k => by
    rw [← Over.comp_left, comp_lift, lift_fst, lift_snd_assoc]
  obtain ⟨a, ha, va⟩ := exists_gen hL (φ' := fun k => φ k ≫ (snd T A).left) (ε' := rosatiε)
    (fun U _ h => by simp only [hφ]) (LB.pullGen L _ _ u (snd T (A ⊗ A)).left) (DVR.pullGen_isGen _ _ _ _ hu _)
  obtain ⟨s, hs, vs⟩ := GlobalTheory.EndRosati.exists_gen_through hL hL' w hw φ rosatiε a ha
  have ev : ∀ (c : T ⟶ A ⊗ A) (y : Sp F) N J, Good L y N → Good L' y J → val s (lift (𝟙 T) c).left y J =
      (∏ k, gw w (lift (𝟙 T) (c ≫ rosO A f g k)).left y (J (ψ (c ≫ rosO A f g k)).left)
        (fun _ => N (c ≫ rosO A f g k).left) ^ rosatiε k) * val u c.left y N := fun c y N J hN hJ => by
    rw [vs _ _ y J N hJ hN, va _ _ y N hN, val_pull hN, ← Over.comp_left, lift_snd]
    refine congrArg (· * _) (Finset.prod_congr rfl fun k _ => ?_)
    rw [hφc, hψ, ← Over.comp_left, lift_snd]
  have ev' : ∀ (x x' : T ⟶ A) (y : Sp F) J, Good L' y J →
      val (LB.pullGen L' _ _ u' H.left) (lift (𝟙 T) (lift x x')).left y J = val u' (lift (ψ x) (ψ x')).left y J :=
    fun x x' y J hJ => by rw [val_pull hJ, ← hH]; rfl
  have hp : Function.Surjective p.appTop.hom := by
    let β : Y ≅ A ⊗ (A ⊗ T) := β_ _ _ ≪≫ α_ _ _ _
    have e : p = β.hom.left ≫ (snd A (A ⊗ T)).left ≫ (snd A T).left := by
      have : fst T (A ⊗ A) = β.hom ≫ snd A (A ⊗ T) ≫ snd A T := by simp [β, Y]
      exact congrArg (·.left) this
    rw [e]
    refine surj_comp ?_ (surj_comp (surj_snd hG hA _) (surj_snd hG hA _))
    have : IsIso β.hom.left := inferInstanceAs (IsIso ((Over.forget S).map β.hom))
    have : IsIso β.hom.left.appTop := inferInstanceAs (IsIso (β.hom.left.app ⊤))
    exact (ConcreteCategory.bijective_of_isIso β.hom.left.appTop).2
  refine (ev' b b' z J hJ).symm.trans (Eq.trans ?_ (ev _ z N J hN hJ))
  refine gen_unique' hL' (fun U _ h => Finset.prod_congr rfl fun k _ => congrArg (fun q => h q ^ _) (hE k)) p
    (lift (𝟙 T) (lift 1 1)).left (by rw [← Over.comp_left, lift_fst]; rfl) hp
    (DVR.pullGen_isGen _ _ _ _ hu' _) hs (fun y I hI => ?_) _ _ z J hJ
  choose M hM using fun χ : Sp F ⟶ A.left => exists_chart hL (χ y)
  have o : ∀ k, lift (1 : T ⟶ A) 1 ≫ rosO A f g k = 1 := fun k => by
    rw [lift_rosO]; fin_cases k <;> simp [MonObj.one_comp]
  refine (ev' _ _ y I hI).trans (Eq.trans ?_ (ev _ y M I hM hI).symm)
  rw [map_one, val_origin u₀' (T := T') hI, val_origin u₀ (T := T) hM]
  simp [o, rosatiε, Fin.prod_univ_succ]

theorem rosV_move : Laws → ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (D : DegPre R) (D' : DegPre R') (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] [Algebra (FractionRing R') F] (N N' : NumD F) (ν : NumOf D F N) (ν' : NumOf D' F N') (O : Type) [CommRing O] [StarRing O] (oa : D.P.OAct O) (oa' : D'.P.OAct O) (Φ : (TF (R := R) F ⊗ D.P.A).left ⟶ D'.P.A.left) (w : LB.Iso (D.P.L.pull (snd (TF (R := R) F) D.P.A).left) (D'.P.L.pull Φ)) (φ : N.A →* N'.A) (wv : N.A → F), w.IsGen → Φ ≫ D'.P.A.hom = (fst (TF (R := R) F) D.P.A).left ≫ (TF (R := R') F).hom → (∀ x, (lift (𝟙 (TF (R := R) F)) (ν.eA x)).left ≫ Φ = (ν'.eA (φ x)).left) → (∀ x, wv x = valF (lift (𝟙 (TF (R := R) F)) (ν.eA x)).left _ (w.s (fun _ => ν'.J (ν'.eA (φ x)).left, fun _ => ν.J (ν.eA x).left)).val) → (∀ y b, φ (actV ν oa y b) = actV ν' oa' y (φ b)) → ∀ (a : O) ρ ρ', RosV ν oa a ρ → RosV ν' oa' a ρ' → ∀ b b', ρ' (φ b) (φ b') * (wv (actV ν oa (star a) b) * wv b' * wv (b * actV ν oa a b')) = ρ b b' * (wv (actV ν oa (star a) b * b') * wv b * wv (actV ν oa a b')) := by
  intro hL R R' _ _ _ _ D D' F _ _ _ _ N N' ν ν' O _ _ oa oa' Φ w φ wv hw hΦ hφ hwv hact a ρ ρ' ⟨u, hu, u₀, hρ⟩
    ⟨u', hu', u₀', hρ'⟩ b b'
  have := oa.hom a
  have := oa.hom (star a)
  let ψ : (TF (R := R) F ⟶ D.P.A) →* (TF (R := R') F ⟶ D'.P.A) :=
    (ν'.eA.toMonoidHom.comp φ).comp ν.eA.symm.toMonoidHom
  have e : ∀ x, ψ (ν.eA x) = ν'.eA (φ x) := fun x => by simp [ψ]
  have ea : ∀ y x, ν.eA (actV ν oa y x) = ν.eA x ≫ oa.act y := fun y x => ν.eA.apply_symm_apply _
  have hf : ∀ y x, ψ (x ≫ oa.act y) = ψ x ≫ oa'.act y := fun y x => by
    obtain ⟨x, rfl⟩ := ν.eA.surjective x
    rw [← ea, e, e, hact]; exact ν'.eA.apply_symm_apply _
  have hψ : ∀ x, (lift (𝟙 (TF (R := R) F)) x).left ≫ Φ = (ψ x).left := fun x => by
    obtain ⟨x, rfl⟩ := ν.eA.surjective x
    rw [e, hφ]
  let z : Sp F := IsLocalRing.closedPoint F
  have hN : Good D.P.L z ν.J := fun q => ν.good q trivial
  have hJ : Good D'.P.L z ν'.J := fun q => ν'.good q trivial
  have H := val_move hL.globalFns _ _ D.P.isAb D'.P.isAb D.P.isLB D'.P.isLB Φ w hw hΦ ψ hψ _ _ _ _ (hf (star a)) (hf a)
    hu u₀ hu' u₀' z ν.J ν'.J hN hJ (ν.eA b) (ν.eA b')
  let W : (TF (R := R) F ⟶ D.P.A) → ((Sp F).presheaf.stalk z)ˣ := fun x =>
    gw w (lift (𝟙 (TF (R := R) F)) x).left z (ν'.J (ψ x).left) (fun _ => ν.J x.left)
  have hW : ∀ x, toStk z (wv x) = (W (ν.eA x)).val := fun x => by
    rw [hwv, ← e]
    have m₁ : Φ ((lift (𝟙 (TF (R := R) F)) (ν.eA x)).left z) ∈ D'.P.L.U (ν'.J (ψ (ν.eA x)).left) :=
      (congrArg (fun q : Sp F ⟶ _ => q z ∈ D'.P.L.U (ν'.J (ψ (ν.eA x)).left)) (hψ (ν.eA x))).mpr (hJ _)
    have m₂ : (snd (TF (R := R) F) D.P.A).left ((lift (𝟙 (TF (R := R) F)) (ν.eA x)).left z) ∈ D.P.L.U (ν.J (ν.eA x).left) :=
      (congrArg (fun q : TF (R := R) F ⟶ _ => q.left z ∈ D.P.L.U (ν.J (ν.eA x).left))
        (lift_snd (𝟙 (TF (R := R) F)) (ν.eA x))).mpr (hN _)
    exact toStk_valF _ (_ ⊓ _) z ⟨mem_pull.2 m₁, mem_pull.2 m₂⟩ _
  have H' : val (Z := Sp F) u' (lift (ν'.eA (φ b)) (ν'.eA (φ b'))).left z ν'.J =
      (∏ k, W (lift (ν.eA b) (ν.eA b') ≫ rosO _ (oa.act (star a)) (oa.act a) k) ^ rosatiε k) * val (Z := Sp F) u (lift (ν.eA b) (ν.eA b')).left z ν.J := by
    rw [← e, ← e]; exact H
  have v : toStk z (ρ b b') = (val (Z := Sp F) u (lift (ν.eA b) (ν.eA b')).left z ν.J).val := by
    rw [hρ]; exact toStk_valF _ _ z (hN.mem _ _) _
  have v' : toStk z (ρ' (φ b) (φ b')) = (val (Z := Sp F) u' (lift (ν'.eA (φ b)) (ν'.eA (φ b'))).left z ν'.J).val := by
    rw [hρ']; exact toStk_valF _ _ z (hJ.mem _ _) _
  apply (toStk z).injective
  simp only [map_mul, hW, v, v', ea, ← Units.val_mul, H', lift_rosO]
  congr 1
  clear_value W
  apply Additive.ofMul.injective
  simp [rosatiε, Fin.prod_univ_succ, ofMul_mul, ofMul_inv]
  abel

end GlobalTheory.RosMove
end
