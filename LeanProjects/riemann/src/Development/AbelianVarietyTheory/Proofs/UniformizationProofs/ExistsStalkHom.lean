import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.InvariantFunctionsDescend

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU TopologicalSpace

noncomputable section
namespace GlobalTheory.EquivDesc
variable {S : Scheme.{0}}

theorem exists_stalk_hom {Z Z' : Scheme.{0}} (κ : Z' ⟶ Z) [IsOpenImmersion κ] (z : Z') :
    ∃ Φ : (Z.presheaf.stalk (κ z))ˣ →* (Z'.presheaf.stalk z)ˣ, Function.Injective Φ ∧
      ∀ (Y : Scheme.{0}) (f : Z ⟶ Y) (U : Y.Opens) (a : Γ(Y, U)ˣ), f (κ z) ∈ U →
        Φ (gm f (κ z) U a) = gm (κ ≫ f) z U a := by
  refine ⟨Units.map (κ.stalkMap z).hom.toMonoidHom,
    Units.map_injective (ConcreteCategory.bijective_of_isIso (κ.stalkMap z)).1, fun Y f U a h => Units.ext ?_⟩
  rw [gm_val (κ ≫ f) z U h]
  change (κ.stalkMap z).hom (gm f (κ z) U a).val = _
  rw [gm_val f (κ z) U h]
  exact Scheme.Hom.germ_stalkMap_apply κ (f ⁻¹ᵁ U) z h _

theorem gm_appLE {Z Y : Scheme.{0}} (f : Z ⟶ Y) (U : Y.Opens) (h : ⊤ ≤ f ⁻¹ᵁ U) (a : Γ(Y, U)ˣ) (z : Z) :
    gm (𝟙 Z) z ⊤ (Units.map (f.appLE U ⊤ h).hom.toMonoidHom a) = gm f z U a :=
  (gm_res (𝟙 Z) z h trivial (pullU f U a)).trans ((gm_pull (𝟙 Z) f z U (h trivial) a).trans
    (by rw [Category.id_comp]))

theorem unit_ext_of_flat {Y B : Scheme.{0}} (q : Y ⟶ B) [Flat q] [Surjective q] {V : B.Opens} {a b : Γ(B, V)ˣ}
    (h : ∀ y, q y ∈ V → gm q y V a = gm q y V b) : a = b := by
  refine Units.map_injective (f := (q.app V).hom.toMonoidHom) (FunDescent.app_injective q V)
    (unit_ext (a := pullU q V a) (b := pullU q V b) fun y hy => ?_)
  rw [gm_pull (𝟙 Y) q y V hy, gm_pull (𝟙 Y) q y V hy, Category.id_comp]
  exact h y hy

theorem exists_units {X : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] {G : Over S} [GrpObj G]
    (Q : TQ G X) (b : Q.B.left) : ∃ V : Q.B.left.Opens, b ∈ V ∧
      ∃ u : Multiplicative X →* Γ(G.left, Q.q.left ⁻¹ᵁ V)ˣ, ∀ χ, IsWt Q.i _ (u (Multiplicative.ofAdd χ)).val χ := by
  let β := Module.Free.chooseBasis ℤ X
  choose V hV u hu using fun k => Q.loc b (β k)
  let V₀ : Q.B.left.Opens := ⟨⋂ k, (V k : Set Q.B.left), isOpen_iInter_of_finite fun k => (V k).isOpen⟩
  have le : ∀ k, Q.q.left ⁻¹ᵁ V₀ ≤ Q.q.left ⁻¹ᵁ V k := fun k y hy => Set.mem_iInter.1 hy k
  let f : X →ₗ[ℤ] Additive Γ(G.left, Q.q.left ⁻¹ᵁ V₀)ˣ := β.constr ℤ fun k => Additive.ofMul (res (le k) (u k))
  refine ⟨V₀, Set.mem_iInter.2 hV, AddMonoidHom.toMultiplicativeLeft f.toAddMonoidHom, fun χ => ?_⟩
  change IsWt Q.i _ (Additive.toMul (f χ)).val χ
  have hχ : χ ∈ AddSubgroup.closure (Set.range β) := by
    rw [← Submodule.span_int_eq_addSubgroupClosure, β.span_eq]; trivial
  induction hχ using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨k, rfl⟩ := hx
    rw [Module.Basis.constr_basis]
    exact (hu k).res (le k)
  | zero => rw [map_zero]; exact isWt_one
  | add x y _ _ hx hy => rw [map_add]; exact hx.mul hy
  | neg x _ hx => rw [map_neg]; exact hx.inv

abbrev opn {G : Over S} (U : G.left.Opens) : Over S := Over.mk (U.ι ≫ G.hom)

abbrev opnι {G : Over S} (U : G.left.Opens) : opn U ⟶ G := Over.homMk U.ι rfl

theorem exists_coord {X : Type} [AddCommGroup X] {G : Over S} [GrpObj G] (i : splitTorus S X ⟶ G) (U : G.left.Opens)
    (u : Multiplicative X →* Γ(G.left, U)ˣ) (hu : ∀ χ, IsWt i _ (u (Multiplicative.ofAdd χ)).val χ) :
    ∃ τ : opn U ⟶ splitTorus S X, ∀ (Z : Over S) (t : Z ⟶ splitTorus S X) (g g' : Z ⟶ opn U),
      g' ≫ opnι U = (t ≫ i) * (g ≫ opnι U) → g' ≫ τ = t * (g ≫ τ) := by
  let τ : opn U ⟶ splitTorus S X := (splitTorusPointsEquiv S X (opn U)).symm
    ((Units.map U.topIso.inv.hom.toMonoidHom).comp u)
  have hτ₀ : ∀ χ : X, τ.left.appTop.hom (charUnit S X χ).val =
      U.topIso.inv.hom (u (Multiplicative.ofAdd χ)).val := by
    intro χ
    rw [← splitTorusPointsEquiv_val, MulEquiv.apply_symm_apply]
    rfl
  have hle : ∀ {Z : Over S} (g : Z ⟶ opn U), ⊤ ≤ (g ≫ opnι U).left ⁻¹ᵁ U := by
    intro Z g x _
    exact (g.left x).2
  have hτ₁ : ∀ {Z : Over S} (g : Z ⟶ opn U) (χ : X), (g ≫ τ).left.appTop.hom (charUnit S X χ).val =
      ((g ≫ opnι U).left.appLE U ⊤ (hle g)).hom (u (Multiplicative.ofAdd χ)).val := by
    intro Z g χ
    let g' : Z.left ⟶ U := g.left
    have h : U.topIso.inv ≫ g'.appTop = (g' ≫ U.ι).appLE U ⊤ (hle g) := by
      rw [← Scheme.Hom.appLE_comp_appLE g' U.ι U ⊤ ⊤ (by simp) (by simp), Scheme.Hom.appTop,
        Scheme.Hom.app_eq_appLE, Scheme.Opens.ι_appLE, Scheme.Opens.topIso_inv]
      rfl
    change g'.appTop.hom (τ.left.appTop.hom (charUnit S X χ).val) = _
    rw [hτ₀]
    exact congrArg (fun f => f.hom (u (Multiplicative.ofAdd χ)).val) h
  refine ⟨τ, fun Z t g g' hg => ?_⟩
  apply (splitTorusPointsEquiv S X Z).injective
  rw [map_mul]
  ext χ
  change (splitTorusPointsEquiv S X Z _ (Multiplicative.ofAdd χ)).val =
    (splitTorusPointsEquiv S X Z _ (Multiplicative.ofAdd χ)).val *
    (splitTorusPointsEquiv S X Z _ (Multiplicative.ofAdd χ)).val
  rw [splitTorusPointsEquiv_val, splitTorusPointsEquiv_val, splitTorusPointsEquiv_val, hτ₁, hτ₁,
    TorusInj.appLE_of_eq (congrArg Over.Hom.left hg)]
  exact hu χ Z t (g ≫ opnι U) _ _

section Action
variable {G H : Over S} [GrpObj G] [GrpObj H] {i : H ⟶ G} {L : LB G.left}

abbrev actφ (i : H ⟶ G) : Fin 2 → ((H ⊗ G).left ⟶ G.left) := ![((fst H G ≫ i) * snd H G).left, (snd H G).left]

def av (a : LB.Gen (LB.LinComb L (actφ i) ![1, -1])) {T : Over S} (t : T ⟶ H) (x : T ⟶ G) (z : T.left)
    (k₁ k₂ : L.ι) : (T.left.presheaf.stalk z)ˣ :=
  gm (lift t x).left z (LB.wchart L (actφ i) ![k₁, k₂]) (a.s ![k₁, k₂])

theorem lift_actφ_zero {T : Over S} (t : T ⟶ H) (x : T ⟶ G) : (lift t x).left ≫ actφ i 0 = ((t ≫ i) * x).left := by
  change (lift t x ≫ ((fst H G ≫ i) * snd H G)).left = _
  rw [MonObj.comp_mul, lift_fst_assoc, lift_snd]

theorem lift_actφ_one {T : Over S} (t : T ⟶ H) (x : T ⟶ G) : (lift t x).left ≫ actφ i 1 = x.left := by
  change (lift t x ≫ snd H G).left = _
  rw [lift_snd]

theorem mem_chart {T : Over S} (t : T ⟶ H) (x : T ⟶ G) (z : T.left) {k₁ k₂ : L.ι}
    (h₁ : ((t ≫ i) * x).left z ∈ L.U k₁) (h₂ : x.left z ∈ L.U k₂) :
    (lift t x).left z ∈ LB.wchart L (actφ i) ![k₁, k₂] := Set.mem_iInter.2 fun k => by
  fin_cases k
  · rw [← lift_actφ_zero] at h₁; exact h₁
  · rw [← lift_actφ_one (i := i) t] at h₂; exact h₂

variable {a : LB.Gen (LB.LinComb L (actφ i) ![1, -1])}

theorem val_eq_av {T : Over S} (t : T ⟶ H) (x : T ⟶ G) (z : T.left) (J) :
    val a (lift t x).left z J = av a t x z (J ((t ≫ i) * x).left) (J x.left) :=
  val_of a _ z J _ fun k => by
    fin_cases k
    · exact congrArg J (lift_actφ_zero t x)
    · exact congrArg J (lift_actφ_one t x)

theorem av_change (ha : a.IsGen) {T : Over S} (t : T ⟶ H) (x : T ⟶ G) (z : T.left) {k₁ k₂ l₁ l₂ : L.ι}
    (h₁ : ((t ≫ i) * x).left z ∈ L.U k₁) (h₂ : x.left z ∈ L.U k₂)
    (g₁ : ((t ≫ i) * x).left z ∈ L.U l₁) (g₂ : x.left z ∈ L.U l₂) :
    av a t x z k₁ k₂ = gm ((t ≫ i) * x).left z _ (L.g k₁ l₁) * (gm x.left z _ (L.g k₂ l₂))⁻¹ * av a t x z l₁ l₂ := by
  refine (gen_trans ha _ z (mem_chart t x z h₁ h₂) (mem_chart t x z g₁ g₂)).trans (congrArg (· * _) ?_)
  rw [trF, Fin.prod_univ_two, lift_actφ_zero, lift_actφ_one]
  change gm _ z _ (L.g k₁ l₁) ^ (1 : ℤ) * gm _ z _ (L.g k₂ l₂) ^ (-1 : ℤ) = _
  rw [zpow_neg, zpow_one, zpow_one]

def IsAct (a : LB.Gen (LB.LinComb L (actφ i) ![1, -1])) : Prop :=
  ∀ (T : Over S) (t t' : T ⟶ H) (x : T ⟶ G) (z : T.left) (J), Good L z J →
    val a (lift (t * t') x).left z J = val a (lift t ((t' ≫ i) * x)).left z J * val a (lift t' x).left z J

theorem av_mul [IsMonHom i] (hL : L.IsLB) (ha : a.IsGen) (hc : IsAct a) {T : Over S} (t t' : T ⟶ H) (x : T ⟶ G)
    (z : T.left) {k₁ k₂ k₃ : L.ι} (h₁ : (((t * t') ≫ i) * x).left z ∈ L.U k₁) (h₂ : ((t' ≫ i) * x).left z ∈ L.U k₂)
    (h₃ : x.left z ∈ L.U k₃) :
    av a (t * t') x z k₁ k₃ = av a t ((t' ≫ i) * x) z k₁ k₂ * av a t' x z k₂ k₃ := by
  obtain ⟨J, hJ⟩ := exists_good_pt hL z
  have e : (t ≫ i) * ((t' ≫ i) * x) = ((t * t') ≫ i) * x := by rw [MonObj.mul_comp, _root_.mul_assoc]
  have c := hc T t t' x z J hJ
  rw [val_eq_av, val_eq_av, val_eq_av] at c
  rw [av_change ha _ _ z h₁ h₃ (hJ _) (hJ _), av_change ha t _ z (by rw [e]; exact h₁) h₂ (hJ _) (hJ _),
    av_change ha t' _ z h₂ h₃ (hJ _) (hJ _), c, e]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

end Action

section Local
variable {G B H : Over S} [GrpObj G] [GrpObj B] [GrpObj H] {q : G ⟶ B} {i : H ⟶ G} [IsMonHom q] [IsMonHom i]
  {L : LB G.left} {a : LB.Gen (LB.LinComb L (actφ i) ![1, -1])}

omit [GrpObj H] [IsMonHom i] in
theorem act_comp (hk : IsPullback i (toUnit _) q η[B]) {T : Over S} (t : T ⟶ H) (x : T ⟶ G) :
    ((t ≫ i) * x).left ≫ q.left = x.left ≫ q.left := by
  have : (t ≫ i) ≫ q = 1 := by
    rw [Category.assoc, hk.w, ← Category.assoc, Hom.one_def]
    congr 1
    exact toUnit_unique _ _
  rw [← Over.comp_left, ← Over.comp_left, MonObj.mul_comp, this, _root_.one_mul]

omit [GrpObj H] [IsMonHom i] in
theorem exists_diff (hk : IsPullback i (toUnit _) q η[B]) {T : Over S} (x x' : T ⟶ G) (e : x' ≫ q = x ≫ q) :
    ∃ t : T ⟶ H, x' = (t ≫ i) * x := by
  have w : (x' * x⁻¹) ≫ q = toUnit T ≫ η[B] := by
    rw [MonObj.mul_comp, GrpObj.inv_comp, e, mul_inv_cancel]
    rfl
  exact ⟨hk.lift _ _ w, by rw [hk.lift_fst, inv_mul_cancel_right]⟩

structure InvGen (q : G ⟶ B) (a : LB.Gen (LB.LinComb L (actφ i) ![1, -1])) (V : B.left.Opens)
    (e : ∀ k, Γ(G.left, q.left ⁻¹ᵁ V ⊓ L.U k)ˣ) : Prop where
  gen : ∀ (Y : Scheme.{0}) (f : Y ⟶ G.left) (y : Y) (k k' : L.ι), q.left (f y) ∈ V → f y ∈ L.U k → f y ∈ L.U k' →
    gm f y _ (e k) = gm f y _ (L.g k k') * gm f y _ (e k')
  inv : ∀ (T : Over S) (t : T ⟶ H) (x : T ⟶ G) (z : T.left) (k₁ k₂ : L.ι), q.left (x.left z) ∈ V →
    ((t ≫ i) * x).left z ∈ L.U k₁ → x.left z ∈ L.U k₂ →
    gm ((t ≫ i) * x).left z _ (e k₁) = av a t x z k₁ k₂ * gm x.left z _ (e k₂)

theorem exists_invGen [Flat q.left] [Surjective q.left] [QuasiCompact q.left] (hk : IsPullback i (toUnit _) q η[B])
    (hL : L.IsLB) (ha : a.IsGen) (hc : IsAct a) (V₀ : B.left.Opens) (τ : opn (q.left ⁻¹ᵁ V₀) ⟶ H)
    (hτ : ∀ (Z : Over S) (t : Z ⟶ H) (g g' : Z ⟶ opn (q.left ⁻¹ᵁ V₀)),
      g' ≫ opnι _ = (t ≫ i) * (g ≫ opnι _) → g' ≫ τ = t * (g ≫ τ)) (b : B.left) (hb : b ∈ V₀) :
    ∃ V : B.left.Opens, b ∈ V ∧ ∃ e, InvGen q a V e := by
  let U : G.left.Opens := q.left ⁻¹ᵁ V₀
  let j : opn U ⟶ G := opnι U
  let ρ : opn U ⟶ G := (τ⁻¹ ≫ i) * j
  have hρ₁ : ∀ {Z : Over S} (g : Z ⟶ opn U), ((g ≫ τ) ≫ i) * (g ≫ ρ) = g ≫ j := fun g => by
    rw [MonObj.comp_mul, ← Category.assoc, GrpObj.comp_inv, GrpObj.inv_comp, mul_inv_cancel_left]
  have hρ₂ : ∀ {Z : Over S} (t : Z ⟶ H) (g g' : Z ⟶ opn U), g' ≫ j = (t ≫ i) * (g ≫ j) → g' ≫ ρ = g ≫ ρ := by
    intro Z t g g' h
    apply mul_left_cancel (a := (g' ≫ τ) ≫ i)
    rw [hρ₁, hτ Z t g g' h, MonObj.mul_comp, _root_.mul_assoc, hρ₁, h]

  have : Surjective (q.left ∣_ V₀) := IsZariskiLocalAtTarget.restrict (P := @Surjective) ‹_› V₀
  let ρ' : U.toScheme ⟶ G.left := ρ.left
  have hd : ∀ {Z : Scheme.{0}} (g₁ g₂ : Z ⟶ U.toScheme), g₁ ≫ (q.left ∣_ V₀) = g₂ ≫ (q.left ∣_ V₀) →
      g₁ ≫ ρ' = g₂ ≫ ρ' := by
    intro Z g₁ g₂ e
    have e₀ : g₁ ≫ U.ι ≫ q.left = g₂ ≫ U.ι ≫ q.left := by
      rw [← morphismRestrict_ι, reassoc_of% e]
    let Z' : Over S := Over.mk (g₂ ≫ U.ι ≫ G.hom)
    let k₂ : Z' ⟶ opn U := Over.homMk g₂ rfl
    let k₁ : Z' ⟶ opn U := Over.homMk g₁ (by
      change g₁ ≫ U.ι ≫ G.hom = g₂ ≫ U.ι ≫ G.hom
      rw [← Over.w q, reassoc_of% e₀])
    obtain ⟨t, ht⟩ := exists_diff hk (k₂ ≫ j) (k₁ ≫ j) (Over.OverMorphism.ext e₀)
    exact congrArg (fun m => m.left) (hρ₂ t k₂ k₁ ht)
  obtain ⟨σ, hσ⟩ : ∃ σ : V₀.toScheme ⟶ G.left, (q.left ∣_ V₀) ≫ σ = ρ' := ⟨_, EffectiveEpi.fac _ ρ' hd⟩
  obtain ⟨k₀, hk₀⟩ := exists_chart hL (σ ⟨b, hb⟩)
  let V : B.left.Opens := V₀.ι ''ᵁ (σ ⁻¹ᵁ L.U k₀)
  have hV₀ : V ≤ V₀ := V₀.ι_image_le _
  have hV : ∀ {Z : Over S} (g : Z ⟶ opn U) (z : Z.left), q.left ((g ≫ j).left z) ∈ V → (g ≫ ρ).left z ∈ L.U k₀ := by
    rintro Z g z ⟨v, hv, e⟩
    have : v = (q.left ∣_ V₀) (g.left z) := Subtype.ext (e.trans
      (congrArg (fun m => m (g.left z)) (morphismRestrict_ι q.left V₀)).symm)
    subst this
    exact (congrArg (fun m : U.toScheme ⟶ G.left => m (g.left z) ∈ L.U k₀) hσ).mp hv
  let m : U.toScheme ⟶ (H ⊗ G).left := (lift τ ρ).left
  choose c hc₀ using fun k : L.ι => exists_ext_unit U.ι (m ⁻¹ᵁ LB.wchart L (actφ i) ![k, k₀])
    (pullU m _ (a.s ![k, k₀]))
  have mem : ∀ {Z : Over S} (g : Z ⟶ opn U) (z : Z.left) (k), q.left ((g ≫ j).left z) ∈ V → (g ≫ j).left z ∈ L.U k →
      m (g.left z) ∈ LB.wchart L (actφ i) ![k, k₀] := fun g z k h₁ h₂ => by
    have := mem_chart (i := i) (g ≫ τ) (g ≫ ρ) z (by rw [hρ₁]; exact h₂) (hV g z h₁)
    rw [← comp_lift] at this
    exact this
  have le : ∀ k, q.left ⁻¹ᵁ V ⊓ L.U k ≤ U.ι ''ᵁ (m ⁻¹ᵁ LB.wchart L (actφ i) ![k, k₀]) := fun k y hy =>
    ⟨⟨y, hV₀ hy.1⟩, mem (𝟙 _) ⟨y, hV₀ hy.1⟩ k hy.1 hy.2, rfl⟩
  have ev : ∀ {Z : Over S} (g : Z ⟶ opn U) (z : Z.left) (k), q.left ((g ≫ j).left z) ∈ V → (g ≫ j).left z ∈ L.U k →
      gm (g ≫ j).left z _ (res (le k) (c k)) = av a (g ≫ τ) (g ≫ ρ) z k k₀ := fun g z k h₁ h₂ => by
    rw [av, ← comp_lift]
    exact (gm_res _ z (le k) ⟨h₁, h₂⟩ _).trans ((hc₀ k _ g.left z (mem g z k h₁ h₂)).trans
      (gm_pull g.left m z _ (mem g z k h₁ h₂) _))

  have loc : ∀ {T : Over S} (x : T ⟶ G) (z : T.left), q.left (x.left z) ∈ V → ∃ (T' : Over S) (κ : T' ⟶ T)
      (_ : IsOpenImmersion κ.left) (z' : T'.left) (g : T' ⟶ opn U), κ.left z' = z ∧ g ≫ j = κ ≫ x := fun x z h =>
    ⟨opn (x.left ⁻¹ᵁ U), opnι _, inferInstanceAs (IsOpenImmersion (x.left ⁻¹ᵁ U).ι), ⟨z, hV₀ h⟩,
      Over.homMk (x.left ∣_ U) (by
        change (x.left ∣_ U) ≫ U.ι ≫ G.hom = (x.left ⁻¹ᵁ U).ι ≫ _
        rw [morphismRestrict_ι_assoc, Over.w]), rfl, Over.OverMorphism.ext (morphismRestrict_ι _ _)⟩
  refine ⟨V, ⟨⟨b, hb⟩, hk₀, rfl⟩, fun k => res (le k) (c k), fun Y f y k k' h₀ h₁ h₂ => ?_,
    fun T t x z k₁ k₂ h₀ h₁ h₂ => ?_⟩
  · let x : Over.mk (f ≫ G.hom) ⟶ G := Over.homMk f rfl
    obtain ⟨T', κ, _, z, g, rfl, hg⟩ := loc x y h₀
    obtain ⟨Φ, hΦ, HΦ⟩ := exists_stalk_hom κ.left z
    have e : κ.left ≫ f = (g ≫ j).left := congrArg (fun m => m.left) hg.symm
    have p : f (κ.left z) = (g ≫ j).left z := congrArg (fun m => m z) e
    apply hΦ
    rw [map_mul, HΦ _ f (q.left ⁻¹ᵁ V ⊓ L.U k) _ ⟨h₀, h₁⟩, HΦ _ f (q.left ⁻¹ᵁ V ⊓ L.U k') _ ⟨h₀, h₂⟩,
      HΦ _ f (L.U k ⊓ L.U k') _ ⟨h₁, h₂⟩, e]
    rw [p] at h₀ h₁ h₂
    rw [ev g z k h₀ h₁, ev g z k' h₀ h₂, av_change ha _ _ z (by rw [hρ₁]; exact h₁) (hV g z h₀)
      (by rw [hρ₁]; exact h₂) (hV g z h₀), hρ₁, gm_self hL _ z (hV g z h₀), inv_one, _root_.mul_one]
  · obtain ⟨T', κ, _, z, g, rfl, hg⟩ := loc x z h₀
    obtain ⟨Φ, hΦ, HΦ⟩ := exists_stalk_hom κ.left z
    have hq := act_comp hk (κ ≫ t) (g ≫ j)
    obtain ⟨g', hg'⟩ : ∃ g' : T' ⟶ opn U, g' ≫ j = ((κ ≫ t) ≫ i) * (g ≫ j) :=
      ⟨Over.homMk (IsOpenImmersion.lift U.ι (((κ ≫ t) ≫ i) * (g ≫ j)).left (by
        rintro _ ⟨y, rfl⟩
        rw [Scheme.Opens.range_ι]
        exact (congrArg (fun m => m y ∈ V₀) hq).mpr (g.left y).2)) ((IsOpenImmersion.lift_fac_assoc U.ι _ _ G.hom).trans
          (Over.w _)), Over.OverMorphism.ext (IsOpenImmersion.lift_fac _ _ _)⟩
    have e : κ.left ≫ x.left = (g ≫ j).left := congrArg (fun m => m.left) hg.symm
    have e' : κ.left ≫ ((t ≫ i) * x).left = (g' ≫ j).left := by
      rw [hg', hg, ← Over.comp_left, MonObj.comp_mul, Category.assoc]
    have e'' : κ.left ≫ (lift t x).left = (lift (κ ≫ t) (g ≫ j)).left := by
      rw [hg, ← Over.comp_left, comp_lift]
    have p : x.left (κ.left z) = (g ≫ j).left z := congrArg (fun m => m z) e
    have p' : ((t ≫ i) * x).left (κ.left z) = (g' ≫ j).left z := congrArg (fun m => m z) e'
    have h₀' : q.left (((t ≫ i) * x).left (κ.left z)) ∈ V :=
      (congrArg (fun m => m (κ.left z) ∈ V) (act_comp hk t x)).mpr h₀
    have A : Φ (av a t x (κ.left z) k₁ k₂) = av a (κ ≫ t) (g ≫ j) z k₁ k₂ :=
      (HΦ _ _ _ _ (mem_chart t x _ h₁ h₂)).trans
        (congrArg (fun r => gm r z (LB.wchart L (actφ i) ![k₁, k₂]) (a.s ![k₁, k₂])) e'')
    apply hΦ
    rw [map_mul, A, HΦ _ ((t ≫ i) * x).left (q.left ⁻¹ᵁ V ⊓ L.U k₁) _ ⟨h₀', h₁⟩,
      HΦ _ x.left (q.left ⁻¹ᵁ V ⊓ L.U k₂) _ ⟨h₀, h₂⟩, e, e']
    rw [p] at h₀ h₂
    rw [p'] at h₀' h₁
    rw [ev g z k₂ h₀ h₂, ev g' z k₁ h₀' h₁, hτ _ _ _ _ hg', hρ₂ _ _ _ hg', av_mul hL ha hc _ _ _ z (k₂ := k₂)
      (by rw [MonObj.mul_comp, _root_.mul_assoc, hρ₁, ← hg']; exact h₁) (by rw [hρ₁]; exact h₂) (hV g z h₀), hρ₁]

end Local

section Global
variable {G B H : Over S} [GrpObj G] [GrpObj B] [GrpObj H] {q : G ⟶ B} {i : H ⟶ G} [IsMonHom q] [IsMonHom i]
  {L : LB G.left} {a : LB.Gen (LB.LinComb L (actφ i) ![1, -1])}

theorem exists_ratio [Flat q.left] [Surjective q.left] [QuasiCompact q.left] (hk : IsPullback i (toUnit _) q η[B])
    (hL : L.IsLB) {V V' : B.left.Opens} {e e'} (he : InvGen q a V e) (he' : InvGen q a V' e') :
    ∃ m : Γ(B.left, V ⊓ V')ˣ, ∀ (Y : Scheme.{0}) (f : Y ⟶ G.left) (y : Y) (k : L.ι), q.left (f y) ∈ V →
      q.left (f y) ∈ V' → f y ∈ L.U k → gm (f ≫ q.left) y _ m = gm f y _ (e' k) * (gm f y _ (e k))⁻¹ := by
  let W : L.ι → G.left.Opens := fun k => q.left ⁻¹ᵁ (V ⊓ V') ⊓ L.U k
  have l₁ : ∀ k, W k ≤ q.left ⁻¹ᵁ V ⊓ L.U k := fun k y hy => ⟨hy.1.1, hy.2⟩
  have l₂ : ∀ k, W k ≤ q.left ⁻¹ᵁ V' ⊓ L.U k := fun k y hy => ⟨hy.1.2, hy.2⟩
  have hu : ∀ (Y : Scheme.{0}) (f : Y ⟶ G.left) (y : Y) (k : L.ι), f y ∈ W k →
      gm f y (W k) (res (l₂ k) (e' k) * (res (l₁ k) (e k))⁻¹) = gm f y _ (e' k) * (gm f y _ (e k))⁻¹ :=
    fun Y f y k h => by rw [map_mul, map_inv, gm_res f y _ h, gm_res f y _ h]
  obtain ⟨s, hs⟩ := glue_unit (q.left ⁻¹ᵁ (V ⊓ V')) W (fun _ => inf_le_left) (fun y hy => by
      obtain ⟨k, hk⟩ := exists_chart hL y
      exact Opens.mem_iSup.2 ⟨k, hy, hk⟩) (fun k => res (l₂ k) (e' k) * (res (l₁ k) (e k))⁻¹) (fun k k' y hy => by
      rw [hu _ (𝟙 _) y k hy.1, hu _ (𝟙 _) y k' hy.2, he.gen _ (𝟙 _) y k k' hy.1.1.1 hy.1.2 hy.2.2,
        he'.gen _ (𝟙 _) y k k' hy.1.1.2 hy.1.2 hy.2.2, ← div_eq_mul_inv, mul_div_mul_left_eq_div, div_eq_mul_inv])
  have hs' : ∀ (Y : Scheme.{0}) (f : Y ⟶ G.left) (y : Y) (k : L.ι), f y ∈ W k →
      gm f y _ s = gm f y _ (e' k) * (gm f y _ (e k))⁻¹ := fun Y f y k h =>
    (gm_res f y inf_le_left h s).symm.trans ((congrArg (gm f y (W k)) (hs k)).trans (hu Y f y k h))
  obtain ⟨-, d₂, d₃⟩ := invariant_functions_descend S G B H q i ‹_› ‹_› ‹_› ‹_› ‹_› hk (V ⊓ V')
  obtain ⟨m, hm⟩ := d₃ s.val fun Z t g h₁ h₂ => by
    refine congrArg Units.val (unit_ext (a := Units.map (((t ≫ i) * g).left.appLE _ ⊤ h₁).hom.toMonoidHom s)
      (b := Units.map (g.left.appLE _ ⊤ h₂).hom.toMonoidHom s) fun z _ => ?_)
    obtain ⟨k₁, hk₁⟩ := exists_chart hL (((t ≫ i) * g).left z)
    obtain ⟨k₂, hk₂⟩ := exists_chart hL (g.left z)
    have m₂ : g.left z ∈ q.left ⁻¹ᵁ (V ⊓ V') := h₂ trivial
    rw [gm_appLE, gm_appLE, hs' _ _ z k₁ ⟨h₁ trivial, hk₁⟩, hs' _ _ z k₂ ⟨m₂, hk₂⟩, he.inv Z t g z k₁ k₂ m₂.1 hk₁ hk₂,
      he'.inv Z t g z k₁ k₂ m₂.2 hk₁ hk₂, ← div_eq_mul_inv, mul_div_mul_left_eq_div, div_eq_mul_inv]
  have um : IsUnit m := d₂ m (hm ▸ s.isUnit)
  have pm : pullU q.left _ um.unit = s := Units.ext hm
  refine ⟨um.unit, fun Y f y k h h' hk => ?_⟩
  rw [← gm_pull f q.left y (V ⊓ V') ⟨h, h'⟩, pm]
  exact hs' Y f y k ⟨⟨h, h'⟩, hk⟩

theorem descend [Flat q.left] [Surjective q.left] [QuasiCompact q.left] (hk : IsPullback i (toUnit _) q η[B])
    (hL : L.IsLB) (h : ∀ b : B.left, ∃ V : B.left.Opens, b ∈ V ∧ ∃ e, InvGen q a V e) :
    ∃ (M : LB B.left) (w : LB.Iso L (M.pull q.left)), M.IsLB ∧ w.IsGen ∧
      ∀ (T : Over S) (t : T ⟶ H) (x : T ⟶ G) (z : T.left) (J) (j : M.ι), Good L z J → q.left (x.left z) ∈ M.U j →
        gw w ((t ≫ i) * x).left z j (J ((t ≫ i) * x).left) * val a (lift t x).left z J = gw w x.left z j (J x.left) := by
  choose V hV e he using h
  choose m hm using fun b b' => exists_ratio hk hL (he b) (he b')
  let M : LB B.left := ⟨B.left, V, m⟩
  let w : LB.Iso L (M.pull q.left) := ⟨fun p => res (le_inf (fun _ hx => mem_pull.1 hx.1) inf_le_right :
    (M.pull q.left).U p.1 ⊓ L.U p.2 ≤ q.left ⁻¹ᵁ V (p.1 PUnit.unit) ⊓ L.U p.2) (e (p.1 PUnit.unit) p.2)⁻¹⟩
  have hw : ∀ (Y : Scheme.{0}) (f : Y ⟶ G.left) (y : Y) (j : M.ι) (k : L.ι), q.left (f y) ∈ V j → f y ∈ L.U k →
      gw w f y j k = (gm f y _ (e j k))⁻¹ := fun Y f y j k hj hk =>
    (gm_res f y _ (show f y ∈ (M.pull q.left).U (fun _ => j) ⊓ L.U k from ⟨mem_pull.2 hj, hk⟩) _).trans (map_inv _ _)
  have hm' : ∀ b b' y k, q.left y ∈ V b → q.left y ∈ V b' → y ∈ L.U k →
      gm q.left y _ (m b b') = gm (𝟙 _) y _ (e b' k) * (gm (𝟙 _) y _ (e b k))⁻¹ := fun b b' y k h₁ h₂ h₃ => by
    have := hm b b' _ (𝟙 _) y k h₁ h₂ h₃
    rwa [Category.id_comp] at this
  refine ⟨M, w, ⟨?_, fun b => unit_ext_of_flat q.left fun y hy => ?_,
    fun b b' b'' => unit_ext_of_flat q.left fun y hy => ?_⟩, (isGen_iff w).2 fun Y f y j j' k k' hj hj' hk hk' => ?_,
    fun T t x z J j hJ hj => ?_⟩
  · exact top_le_iff.1 fun b _ => Opens.mem_iSup.2 ⟨b, hV b⟩
  · obtain ⟨k, hk⟩ := exists_chart hL y
    rw [gm_res _ y _ hy, map_one]
    exact (hm' b b y k hy hy hk).trans (mul_inv_cancel _)
  · obtain ⟨k, hk⟩ := exists_chart hL y
    rw [map_mul, gm_res _ y _ hy, gm_res _ y _ hy, gm_res _ y _ hy]
    refine (congrArg₂ (· * ·) (hm' b b' y k hy.1.1 hy.1.2 hk) (hm' b' b'' y k hy.1.2 hy.2 hk)).trans
      (Eq.trans ?_ (hm' b b'' y k hy.1.1 hy.2 hk).symm)
    rw [mul_comm, _root_.mul_assoc, inv_mul_cancel_left]
  · have := hm j j' Y f y k' hj hj' hk'
    rw [hw Y f y j k hj hk, hw Y f y j' k' hj' hk', (he j).gen Y f y k k' hj hk hk']
    refine Eq.trans ?_ (congrArg (· * _ * _) this).symm
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  · have hj' : q.left (((t ≫ i) * x).left z) ∈ V j := (congrArg (fun m => m z ∈ V j) (act_comp hk t x)).mpr hj
    rw [hw _ _ z j _ hj' (hJ _), hw _ _ z j _ hj (hJ _), (he j).inv T t x z _ _ hj (hJ _) (hJ _), val_eq_av,
      mul_inv_rev, inv_mul_cancel_right]

end Global

theorem main : (∀ (S : Scheme.{0}) (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (G : Over S) [GrpObj G] (Q : TQ G X) (L : LB G.left), L.IsLB → ∀ a : LB.Gen (LB.LinComb L (K := Fin 2) ![((fst (splitTorus S X) G ≫ Q.i) * snd (splitTorus S X) G).left, (snd (splitTorus S X) G).left] ![1, -1]), a.IsGen → (∀ (T : Over S) (t t' : T ⟶ splitTorus S X) (x : T ⟶ G) (z : T.left) (J), Good L z J → val a (lift (t * t') x).left z J = val a (lift t ((t' ≫ Q.i) * x)).left z J * val a (lift t' x).left z J) → ∃ (M : LB Q.B.left) (w : LB.Iso L (M.pull Q.q.left)), M.IsLB ∧ w.IsGen ∧ ∀ (T : Over S) (t : T ⟶ splitTorus S X) (x : T ⟶ G) (z : T.left) (J) (j : M.ι), Good L z J → Q.q.left (x.left z) ∈ M.U j → gw w ((t ≫ Q.i) * x).left z j (J ((t ≫ Q.i) * x).left) * val a (lift t x).left z J = gw w x.left z j (J x.left)) := by
  intro S X _ _ _ G _ Q L hL a ha hc
  have := Q.q_hom
  have := Q.i_hom
  have := Q.q_flat
  have := Q.q_surj
  have := Q.q_affine
  refine descend Q.isKernel hL fun b => ?_
  obtain ⟨V, hV, u, hu⟩ := exists_units Q b
  obtain ⟨τ, hτ⟩ := exists_coord Q.i _ u hu
  exact exists_invGen Q.isKernel hL ha hc V τ hτ b hV

end GlobalTheory.EquivDesc
end
