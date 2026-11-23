import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GalLab

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.GalAct

open MonObj in

theorem exists_mulEquiv_points {S S' : Scheme.{0}} {G' : Over S'} [GrpObj G'] {G : Over S} [GrpObj G]
    {f : S' ⟶ S} {F : G'.left ⟶ G.left} (hF : IsGrpPullback G' G f F) {X : Scheme.{0}} (t : X ⟶ S') (g : X ⟶ S)
    (hg : t ≫ f = g) :
    ∃ e : (Over.mk t ⟶ G') ≃* (Over.mk g ⟶ G), ∀ z, (e z).left = z.left ≫ F := by
  subst hg
  let m : (Over.mk t ⟶ G') → (Over.mk (t ≫ f) ⟶ G) := fun z => Over.homMk (z.left ≫ F) (by
    have h : z.left ≫ G'.hom = t := Over.w z
    show (z.left ≫ F) ≫ G.hom = t ≫ f
    rw [Category.assoc, hF.1.w, ← Category.assoc, h])
  have hm : ∀ z, (m z).left = z.left ≫ F := fun _ => rfl
  have hmul : ∀ x y, m (x * y) = m x * m y := fun x y =>
    Over.OverMorphism.ext ((hm _).trans (hF.2 (Over.mk t) x y (m x) (m y) (hm x) (hm y)).symm)
  have hinj : Function.Injective m := fun x y h => by
    refine Over.OverMorphism.ext (hF.1.hom_ext ?_ ((Over.w x).trans (Over.w y).symm))
    rw [← hm, ← hm, h]
  have hsurj : Function.Surjective m := fun z =>
    ⟨Over.homMk (hF.1.lift z.left t (Over.w z)) (hF.1.lift_snd _ _ _),
      Over.OverMorphism.ext ((hm _).trans (hF.1.lift_fst _ _ _))⟩
  exact ⟨MulEquiv.ofBijective (MonoidHom.mk' m hmul) ⟨hinj, hsurj⟩, hm⟩

theorem epi_spMap_of_field {K L : Type} [Field K] [Field L] (f : K →+* L) : Epi (spMap f) := by
  have f₁ : Flat (spMap f) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact RingHom.Flat.of_isField (Field.toIsField K) f
  have f₂ : Surjective (spMap f) := ⟨fun y => ⟨(default : PrimeSpectrum L), Subsingleton.elim (α := PrimeSpectrum K) _ _⟩⟩
  exact Flat.epi_of_flat_of_surjective _

theorem eq_id_of_frac {A K : Type} [CommRing A] [Field K] (φ : A →+* K) (h : ∀ x, ∃ a b, x = φ a / φ b)
    (u : Sp K ⟶ Sp K) (hu : u ≫ spMap φ = spMap φ) : u = 𝟙 _ := by
  obtain ⟨j, rfl⟩ := Spec.map_surjective u
  have e : CommRingCat.ofHom φ ≫ j = CommRingCat.ofHom φ := Spec.map_injective ((Spec.map_comp _ _).trans hu)
  have e' : ∀ a, j.hom (φ a) = φ a := fun a => congrArg (fun q => q.hom a) e
  have : j = 𝟙 _ := by
    ext x
    obtain ⟨a, b, rfl⟩ := h x
    exact (map_div₀ j.hom (φ a) (φ b)).trans (by rw [e', e']; rfl)
  rw [this, Spec.map_id]

open MonObj in

theorem exists_generic_labels {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} (ρ : S.Real)
    {G : Over (Sp Ω)} [GrpObj G] {b : G.left ⟶ ρ.P.A.left} (hb : IsGrpPullback G ρ.P.A (spMap S.R.val.toRingHom) b) :
    ∃ w : S.Gam → (Over.mk (𝟙 (Sp Ω)) ⟶ G), (∀ x, (w x).left ≫ b = spMap S.R.val.toRingHom ≫ (ρ.pt x).left) ∧
      (∀ x y, w (x + y) = w x * w y) ∧ Function.Injective w ∧ (∀ x, w x ^ (S.r * S.N) = 1) ∧
      ∀ z, z ^ (S.r * S.N) = 1 → ∃ a, w a = z := by
  obtain ⟨e, he⟩ := exists_mulEquiv_points hb (𝟙 _) (spMap S.R.val.toRingHom) (Category.id_comp _)
  let j : Over.mk (spMap S.R.val.toRingHom) ⟶ baseOver (Sp S.R) := Over.homMk (spMap S.R.val.toRingHom) (by simp)
  let k : Sp (AlgebraicClosure Ω) ⟶ Sp Ω := spMap (algebraMap Ω (AlgebraicClosure Ω))
  have : Epi k := epi_spMap_of_field _
  let k' : Over.mk (k ≫ spMap S.R.val.toRingHom) ⟶ Over.mk (spMap S.R.val.toRingHom) := Over.homMk k rfl
  let w : S.Gam → (Over.mk (𝟙 (Sp Ω)) ⟶ G) := fun x => e.symm (j ≫ ρ.pt x)
  have hw : ∀ x, e (w x) = j ≫ ρ.pt x := fun x => e.apply_symm_apply _
  have hadd : ∀ x y, w (x + y) = w x * w y := fun x y => by
    apply e.injective
    rw [map_mul, hw, hw, hw, ρ.pt_add, MonObj.comp_mul]
  let w' : Multiplicative S.Gam →* (Over.mk (𝟙 (Sp Ω)) ⟶ G) := MonoidHom.mk' (fun x => w x.toAdd) fun x y => hadd _ _
  have htor : ∀ x, w x ^ (S.r * S.N) = 1 := fun x => by
    have h0 : (S.r * S.N) • x = 0 := by
      funext i
      simp [nsmul_eq_mul]
    have h1 : (Multiplicative.ofAdd x) ^ (S.r * S.N) = 1 := by rw [← ofAdd_nsmul, h0, ofAdd_zero]
    exact (map_pow w' (Multiplicative.ofAdd x) _).symm.trans (by rw [h1, map_one])
  have key : ∀ z : Over.mk (𝟙 (Sp Ω)) ⟶ G, z ^ (S.r * S.N) = 1 → ∃! a, w a = z := fun z hz => by
    have h := ρ.pt_bij (AlgebraicClosure Ω) (k ≫ spMap S.R.val.toRingHom) (k' ≫ e z)
      ((map_pow (preHom k') (e z) _).symm.trans (by rw [← map_pow, hz, map_one, map_one]))
    refine (existsUnique_congr fun a => ?_).1 h
    constructor
    · intro ha
      apply e.injective
      rw [hw]
      refine Over.OverMorphism.ext ((cancel_epi k).1 ?_)
      exact (Category.assoc _ _ _).symm.trans (congrArg (fun q => q.left) ha)
    · rintro rfl
      rw [hw]
      exact Over.OverMorphism.ext (Category.assoc _ _ _)
  refine ⟨w, fun x => (he _).symm.trans (congrArg (fun q => q.left) (hw x)), hadd,
    fun x y h => (key _ (htor y)).unique h rfl, htor, fun z hz => (key z hz).exists⟩

open MonObj in

theorem exists_label_action {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} (ρ : S.Real)
    {G : Over (Sp Ω)} [GrpObj G] {b : G.left ⟶ ρ.P.A.left} (hb : IsGrpPullback G ρ.P.A (spMap S.R.val.toRingHom) b)
    (σ : Ω →+* Ω) (hσ : Function.Surjective σ) {t : G.left ⟶ G.left} (ht : IsGrpPullback G G (spMap σ) t) :
    ∃ a : S.Gam ≃+ S.Gam, (∀ x (w w' : Sp Ω ⟶ G.left), w ≫ b = spMap S.R.val.toRingHom ≫ (ρ.pt x).left →
      w' ≫ t = spMap σ ≫ w → w' ≫ b = spMap S.R.val.toRingHom ≫ (ρ.pt (a x)).left) ∧
      ∀ x (w : Sp Ω ⟶ G.left), w ≫ b = spMap S.R.val.toRingHom ≫ (ρ.pt x).left → w ≫ t = spMap σ ≫ w → a x = x := by
  obtain ⟨p, hp, hadd, hinj, htor, hsurj⟩ := exists_generic_labels ρ hb
  obtain ⟨e, he⟩ := exists_mulEquiv_points ht (𝟙 _) (spMap σ) (Category.id_comp _)
  have : Epi (spMap σ) := epi_spMap_of_field _
  let s : Over.mk (spMap σ) ⟶ Over.mk (𝟙 (Sp Ω)) := Over.homMk (spMap σ) (Category.comp_id _)
  let τ : (Over.mk (𝟙 (Sp Ω)) ⟶ G) →* (Over.mk (𝟙 (Sp Ω)) ⟶ G) := e.symm.toMonoidHom.comp (preHom s)
  have hτ : ∀ z, (τ z).left ≫ t = spMap σ ≫ z.left := fun z =>
    (he _).symm.trans (congrArg (fun q => q.left) (e.apply_symm_apply (s ≫ z)))
  have τinj : Function.Injective τ := fun z z' h => by
    refine Over.OverMorphism.ext ((cancel_epi (spMap σ)).1 ?_)
    rw [← hτ, ← hτ, h]
  have hex : ∀ x, ∃ y, p y = τ (p x) := fun x => hsurj _ (by rw [← map_pow, htor, map_one])
  choose a ha using hex
  let a' : S.Gam →+ S.Gam := AddMonoidHom.mk' a fun x y => hinj (by rw [hadd, ha, ha, ha, hadd, map_mul])
  have ainj : Function.Injective a' := fun x y h => hinj (τinj (by
    rw [← ha, ← ha]; exact congrArg p h))
  haveI : NeZero (S.r * S.N) := ⟨Nat.mul_ne_zero (by have := S.r_pos; omega) (by have := S.N_ge; omega)⟩
  have abij : Function.Bijective a' := Finite.injective_iff_bijective.1 ainj
  have h₁ : ∀ x (w : Sp Ω ⟶ G.left), w ≫ b = spMap S.R.val.toRingHom ≫ (ρ.pt x).left → w = (p x).left := fun x w h => by
    refine hb.1.hom_ext (h.trans (hp x).symm) (Eq.trans ?_ (Over.w (p x)).symm)
    refine eq_id_of_frac S.R.val.toRingHom (fun y => ?_) _ ?_
    · obtain ⟨c, hc, d, hd, rfl⟩ := S.frac y
      exact ⟨⟨c, hc⟩, ⟨d, hd⟩, rfl⟩
    · rw [Category.assoc, ← hb.1.w, ← Category.assoc, h, Category.assoc]
      exact (congrArg _ (Over.w (ρ.pt x))).trans (Category.comp_id _)
  have h₂ : ∀ x (w' : Sp Ω ⟶ G.left), w' ≫ t = spMap σ ≫ (p x).left → w' = (p (a x)).left := fun x w' h => by
    rw [ha]
    refine ht.1.hom_ext (h.trans (hτ _).symm) (Eq.trans ?_ (Over.w (τ (p x))).symm)
    refine eq_id_of_frac σ (fun y => ?_) _ ?_
    · obtain ⟨c, rfl⟩ := hσ y
      exact ⟨c, 1, by rw [map_one, div_one]⟩
    · rw [Category.assoc, ← ht.1.w, ← Category.assoc, h, Category.assoc]
      exact (congrArg _ (Over.w (p x))).trans (Category.comp_id _)
  refine ⟨AddEquiv.ofBijective a' abij, fun x w w' hw hw' => ?_, fun x w hw hw' => ?_⟩
  · rw [h₁ x w hw] at hw'
    rw [h₂ x w' hw']
    exact hp _
  · have e₁ := h₁ x w hw
    subst e₁
    exact hinj (Over.OverMorphism.ext (h₂ x _ hw').symm)

theorem exists_galLab : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i), 1 ≤ g → 3 ≤ n → Odd n → IsOpenImmersion i → IsE8 W → ThetaInt F W i → IsProjOver X₁.M.s → ∀ (ε₁ : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsDiagEnd F W X₁.ρ.P X₁.u ε₁ → ∀ (D : Deep X₁ ε₁) (σ : D.X.Ω₁ ≃ₐ[X₁.Ω₁] D.X.Ω₁), ∃ a : D.X.S.Gam ≃+ D.X.S.Gam, D.GalLab σ a ∧ ∀ x, a (D.lab x) = D.lab x := by
  intro g n F W Z i X₁ _ _ _ _ _ _ _ ε₁ _ D σ
  obtain ⟨P₀, a₁, a₂, ε₀, h₁, h₂, l₁, l₂, hε, hpt⟩ := D.same
  have hs : spMap (σ : D.X.Ω₁ →+* D.X.Ω₁) ≫ spMap ((algebraMap X₁.Ω₁ D.X.Ω₁).comp X₁.S.R.val.toRingHom) =
      spMap ((algebraMap X₁.Ω₁ D.X.Ω₁).comp X₁.S.R.val.toRingHom) :=
    (spMap_comp _ _).symm.trans (congrArg spMap (RingHom.ext fun y => σ.commutes _))
  obtain ⟨t, ht₁, ht₂⟩ : ∃ t : P₀.A.left ⟶ P₀.A.left, t ≫ a₁ = a₁ ∧
      t ≫ P₀.A.hom = P₀.A.hom ≫ spMap (σ : D.X.Ω₁ →+* D.X.Ω₁) :=
    ⟨h₁.1.lift a₁ (P₀.A.hom ≫ spMap (σ : D.X.Ω₁ →+* D.X.Ω₁)) (by rw [Category.assoc, hs, h₁.1.w]),
      h₁.1.lift_fst _ _ _, h₁.1.lift_snd _ _ _⟩
  have ht : IsGrpPullback P₀.A P₀.A (spMap (σ : D.X.Ω₁ →+* D.X.Ω₁)) t := h₁.cancel (h₁.congr hs.symm ht₁.symm) ht₂
  have lt : LBIso (P₀.L.pull t) (X₁.ρ.P.L.pull a₁) :=
    l₁.chartPull (Geo.Tor.chartPullPull P₀.L t t rfl)
      (chartPullSame X₁.ρ.P.L (fun _ => a₁) (fun _ => a₁) _ t fun _ => ht₁.symm)
  obtain ⟨a, ha, ha'⟩ := exists_label_action D.X.ρ h₂ (σ : D.X.Ω₁ →+* D.X.Ω₁) σ.surjective ht
  refine ⟨a, ⟨P₀, a₂, t, ε₀, h₂, ht, l₂,
    LBIso.trans P₀.isLB (pull_isLB X₁.ρ.P.isLB _) (pull_isLB P₀.isLB _) l₁ lt.symm, fun E => ⟨(hε E).2, ?_⟩, ha⟩,
    fun x => ?_⟩
  · refine h₁.1.hom_ext ?_ ?_
    · rw [Category.assoc, Category.assoc, ht₁, (hε E).1, ← Category.assoc, ht₁]
    · rw [Category.assoc, Category.assoc, ht₂, Over.w (ε₀ E), ← Category.assoc, Over.w (ε₀ E), ht₂]
  · obtain ⟨w, hw₁, hw₂⟩ := hpt x
    refine ha' _ w hw₂ (h₁.1.hom_ext ?_ ?_)
    · rw [Category.assoc, Category.assoc, ht₁, hw₁, ← Category.assoc, hs]
    · have hw : w ≫ P₀.A.hom = 𝟙 _ := by
        refine eq_id_of_frac D.X.S.R.val.toRingHom (fun y => ?_) _ ?_
        · obtain ⟨c, hc, d, hd, rfl⟩ := D.X.S.frac y
          exact ⟨⟨c, hc⟩, ⟨d, hd⟩, rfl⟩
        · rw [Category.assoc, ← h₂.1.w, ← Category.assoc, hw₂, Category.assoc]
          exact (congrArg _ (Over.w (D.X.ρ.pt _))).trans (Category.comp_id _)
      rw [Category.assoc, Category.assoc, ht₂, hw, ← Category.assoc, hw, Category.id_comp, Category.comp_id]

end GlobalTheory.Poinc.GalAct
