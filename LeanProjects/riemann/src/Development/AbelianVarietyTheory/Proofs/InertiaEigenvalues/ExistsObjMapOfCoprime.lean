import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PointEqIffIsometryClosed
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArithmeticCMKnownTheoremsProof
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PointExpEqOfIsometry
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ObjMapUniqueOfIsDominant
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SabMapCancelAndCompOver

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.CoverExp

open GlobalTheory.UnifPoint

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {g : ℕ}

theorem exists_sabMap_types {D D₁ D₂ : Datum H}
    {l : Level H} {b : Base l ℂ} {s : Sp ℂ ⟶ Sp ℂ} (o₁ o₂ : Obj D l b s)
    {ty₁ ty₂ : Fin g → (E →+* ℂ)} {P₁ : D₁.La →+ (Fin g → ℂ)} {P₂ : D₂.La →+ (Fin g → ℂ)} (hP₁ : IsPeriod D₁ ty₁ P₁)
    (hP₂ : IsPeriod D₂ ty₂ P₂) {e₁ : (Fin g → ℂ) → (𝟙_ (Over (Sp ℂ)) ⟶ o₁.t.G)}
    {e₂ : (Fin g → ℂ) → (𝟙_ (Over (Sp ℂ)) ⟶ o₂.t.G)} (a₁ : ∀ z w, e₁ (z + w) = e₁ z * e₁ w)
    (s₁ : Function.Surjective e₁) (s₂ : Function.Surjective e₂)
    (r₁ : ReadsPeriods o₁.t unitOn D₁ ty₁ P₁ e₁) (r₂ : ReadsPeriods o₂.t unitOn D₂ ty₂ P₂ e₂)
    (u₁ : ∀ (g₀ : ℕ) (u : HolUnif o₁.t.G o₁.t.PP.L g₀),
      ∃ h : (Fin g₀ → ℂ) ≃ₗ[ℂ] (Fin g → ℂ), ∀ z, e₁ (h z) = u.ex z)
    (u₂ : ∀ (g₀ : ℕ) (u : HolUnif o₂.t.G o₂.t.PP.L g₀),
      ∃ h : (Fin g₀ → ℂ) ≃ₗ[ℂ] (Fin g → ℂ), ∀ z, e₂ (h z) = u.ex z)
    (gam : D₁.La ≃ₗ[𝓞 E] D₂.La) (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ))
    (hEF : ∀ a b, D₂.EF (gam a) (gam b) = D₁.EF a b) (hh : ∀ a, P₂ (gam a) = h (P₁ a)) :
    ∃ m : SABMap o₁.t o₂.t (𝟙 _), ∀ z, (e₁ z).left ≫ m.φ = (e₂ (h z)).left := by
  have hT := GlobalTheory.ArcCM.known_holds.theta
  have hL := GlobalTheory.ArcCM.known_holds.laws
  have hG := hL.globalFns
  have hA : HomAlg := GlobalTheory.exists_isMonHom_of_map_lattice hT hL
  have hD : WeilDet := GlobalTheory.T.lambdaBundleIso_of_primeToP_weilPairings hL
  have p₁ := GlobalTheory.obj_isAbelianScheme_dim_rigidified_sym E H D l _ _ _ _ o₁
  have p₂ := GlobalTheory.obj_isAbelianScheme_dim_rigidified_sym E H D l _ _ _ _ o₂
  obtain ⟨α, hα, hα'⟩ : ∃ α : o₁.t.G ⟶ o₂.t.G, IsMonHom α ∧ ∀ z, e₂ (h z) = e₁ z ≫ α :=
    exists_hom hT hA (objPol o₁ p₁) (objPol o₂ p₂) rfl u₁ u₂ h.toLinearMap fun z hz => by
      obtain ⟨a, rfl⟩ := (r₁.1 z).1 hz
      exact (r₂.1 _).2 ⟨gam a, hh a⟩
  obtain ⟨β, -, hβ'⟩ : ∃ β : o₂.t.G ⟶ o₁.t.G, IsMonHom β ∧ ∀ z, e₁ (h.symm z) = e₂ z ≫ β :=
    exists_hom hT hA (objPol o₂ p₂) (objPol o₁ p₁) rfl u₂ u₁ h.symm.toLinearMap fun z hz => by
      obtain ⟨a, rfl⟩ := (r₂.1 z).1 hz
      refine (r₁.1 _).2 ⟨gam.symm a, h.injective ?_⟩
      rw [← hh, gam.apply_symm_apply]
      exact (h.apply_symm_apply _).symm
  have := p₁.1.smooth
  have := p₂.1.smooth
  have := p₁.1.proper
  have := p₂.1.proper
  have : IsReduced o₁.t.G.left := isReduced_of_smooth_complex _ o₁.t.G.hom inferInstance
  have : IsReduced o₂.t.G.left := isReduced_of_smooth_complex _ o₂.t.G.hom inferInstance
  let ψ : o₁.t.G ≅ o₂.t.G :=
    { hom := α
      inv := β
      hom_inv_id := ComplexPoints.over_hom_ext_of_complexPoints fun x => by
        obtain ⟨z, rfl⟩ := s₁ x
        rw [← Category.assoc, ← hα', ← hβ', h.symm_apply_apply, Category.comp_id]
      inv_hom_id := ComplexPoints.over_hom_ext_of_complexPoints fun x => by
        obtain ⟨z, rfl⟩ := s₂ x
        rw [← Category.assoc, ← hβ', ← hα', h.apply_symm_apply, Category.comp_id] }
  have hcomm : ∀ (a : 𝓞 E) z, h (fun k => ty₁ k (a : E) * z k) = fun k => ty₂ k (a : E) * h z k := fun a z => by
    have k : (h.toLinearMap.restrictScalars ℝ) ∘ₗ LinearMap.mulLeft ℝ (fun k => ty₁ k (a : E)) =
        LinearMap.mulLeft ℝ (fun k => ty₂ k (a : E)) ∘ₗ (h.toLinearMap.restrictScalars ℝ) := by
      refine LinearMap.ext_on_range hP₁.2.2.2.1 fun x => ?_
      show h (fun k => ty₁ k (a : E) * P₁ x k) = fun k => ty₂ k (a : E) * h (P₁ x) k
      rw [← funext (hP₁.1 a x), ← hh, ← hh, map_smul]
      exact funext (hP₂.1 a _)
    exact DFunLike.congr_fun k z
  have hact : ∀ a, o₁.t.act.act a ≫ α = α ≫ o₂.t.act.act a := fun a =>
    ComplexPoints.over_hom_ext_of_complexPoints fun x => by
      obtain ⟨z, rfl⟩ := s₁ x
      rw [← Category.assoc, ← Category.assoc, ← r₁.2.1, ← hα', ← hα', ← r₂.2.1, hcomm]
  have hlam := hD ℂ (objPol o₁ p₁) (objPol o₂ p₂) α 2 1 hα Nat.prime_two inferInstance
    fun k x y c hk _ hx hy hw => by
      obtain ⟨a, rfl⟩ := exists_div_of_pow a₁ s₁ r₁.1 hk hx
      obtain ⟨a', rfl⟩ := exists_div_of_pow a₁ s₁ r₁.1 hk hy
      have w := r₁.2.2 k a a' (Units.mk0 _ (Complex.exp_ne_zero _)) hk rfl
      obtain rfl := weilIs_unique_fieldPoint _ _ _ o₁.t.PP.isLB ℂ (𝟙 _) k _ _ _ _ hw w
      have w' := r₂.2.2 k (gam a) (gam a') (Units.mk0 _ (Complex.exp_ne_zero _)) hk rfl
      rw [hh, hh, ← map_smul h, ← map_smul h, hα', hα', hEF] at w'
      rw [pow_one]
      exact w'
  have : IsMonHom ψ.hom := hα
  exact ⟨⟨CubeMap.ofHom α, isGrpPullback_of_iso ψ, rfl, fun a => congrArg (fun z => z.left) (hact a),
    HeckePoint.isPullCubical_of_iso hG p₁.1 α o₁.t.cub o₂.t.cub (HeckePoint.iso_of_lam o₁.t o₂.t α hact hlam)⟩,
    fun z => congrArg (fun q => q.left) (hα' z).symm⟩

theorem exists_objMap_of_coprime {D : Datum H} {l : Level H} (hA : l.A = 1) {B : Type} [CommRing B] {b : Base l B}
    {S : Scheme.{0}} {s : S ⟶ Sp B} (o₁ o₂ : Obj D l b s) (m : SABMap o₁.t o₂.t (𝟙 S)) (J : Ideal (𝓞 E))
    (hJ : l.Mb ⊔ J = ⊤)
    (h₁ : ∀ a ∈ J • (⊤ : Submodule (𝓞 E) D.La), (o₁.eta a).left ≫ m.φ = (o₂.eta a).left)
    (h₂ : (1 : 𝟙_ (Over S) ⟶ o₁.t.G).left ≫ m.φ = (1 : 𝟙_ (Over S) ⟶ o₂.t.G).left) :
    ∃ n : ObjMap o₁ o₂ (𝟙 S), n.toSABMap.φ = m.φ := by
  refine ⟨⟨m, fun a => ?_, fun a => ?_⟩, rfl⟩
  · have ha : a ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La) ⊔ J • (⊤ : Submodule (𝓞 E) D.La) := by
      rw [← Submodule.sup_smul, hJ, Submodule.top_smul]
      trivial
    obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.1 ha
    rw [o₁.eta_add, o₂.eta_add, o₁.eta_ker x hx, o₂.eta_ker x hx, _root_.one_mul, _root_.one_mul]
    exact (h₁ y hy).trans (Category.id_comp _).symm
  · have c₁ := o₁.etaA_ker a
    have c₂ := o₂.etaA_ker a
    rw [hA, one_smul] at c₁ c₂
    rw [c₁, c₂]
    exact h₂.trans (Category.id_comp _).symm

theorem phi_eq_of_point_eq {D : Datum H} {l : Level H} {B B' : Type} [CommRing B] [CommRing B'] {b : Base l B}
    {b' : Base l B'} {S : Scheme.{0}} {s : S ⟶ Sp B} {s' : Sp ℂ ⟶ Sp B'}
    {o : Obj D l b s} {o₁ : Obj D l b' s'} {y y' : Sp ℂ ⟶ S} (h : y' = y) (m : ObjMap o₁ o y)
    (m' : ObjMap o₁ o y') : m'.toSABMap.φ = m.toSABMap.φ := by
  subst h
  exact objMap_unique_of_field GlobalTheory.ArcCM.known_holds.laws.serre m' m

theorem isExp_family {D : Datum H} {l : Level H} {Xo : Moduli D l} {σ : KA l →+* ℂ} {ty : Fin g → (E →+* ℂ)}
    (F : FamilyUnif Xo σ ty) (i : Fin F.n) {P : (F.Di i).La →+ (Fin g → ℂ)} (hP : IsPeriod (F.Di i) ty P) :
    GlobalTheory.UnifPoint.IsExp (F.ex i P) :=
  ⟨F.ex_add i P hP, F.ex_onto i P hP, GlobalTheory.ArcCM.isHolTo_exp_of_isPeriod F i P hP, (F.ex_diff i P hP).1,
    (F.ex_diff i P hP).2⟩

theorem pow_of_add {V Q : Type} [AddCommGroup V] [Group Q] {e : V → Q} (he : ∀ z w, e (z + w) = e z * e w) (n : ℕ)
    (z : V) : e (n • z) = e z ^ n := by
  induction n with
  | zero =>
    have := he 0 0
    rw [add_zero] at this
    rw [zero_smul, pow_zero]
    exact left_eq_mul.1 this
  | succ n ih => rw [succ_nsmul, he, ih, pow_succ]

theorem ex_comp_eq {D : Datum H} {l l₂ : Level H} {Xo : Moduli D l} {Xo₂ : Moduli D l₂} {r : Xo₂.X ⟶ Xo.X}
    (m : SABMap Xo₂.univ.t Xo.univ.t r) (pd : ℕ) (hA : l.A = 1) (hM : l₂.M = l.M * pd) (hle : l₂.Mb ≤ l.Mb)
    (heta : ∀ a, (Xo₂.univ.eta a ^ pd).left ≫ m.φ = r ≫ (Xo.univ.eta a).left)
    {σ : KA l →+* ℂ} {σ₂ : KA l₂ →+* ℂ} {ty ty₂ : Fin g → (E →+* ℂ)} (F : FamilyUnif Xo σ ty)
    (F₂ : FamilyUnif Xo₂ σ₂ ty₂) (k : Fin F.n) (k₂ : Fin F₂.n) {P : (F.Di k).La →+ (Fin g → ℂ)}
    {P₂ : (F₂.Di k₂).La →+ (Fin g → ℂ)} (hP : IsPeriod (F.Di k) ty P) (hP₂ : IsPeriod (F₂.Di k₂) ty₂ P₂)
    (hy : (F₂.u k₂ P₂ ≫ r) ≫ Xo.s = spMap σ)
    (gam : (F₂.Di k₂).La ≃ₗ[𝓞 E] (F.Di k).La) (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ))
    (hEF : ∀ a b, (F.Di k).EF (gam a) (gam b) = (F₂.Di k₂).EF a b)
    (gM : ∀ a ∈ l₂.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La),
      ∃ x, gam (F₂.t k₂ a) = F.t k a + l.M • x)
    (hh : ∀ a, P (gam a) = h (P₂ a)) :
    F₂.u k₂ P₂ ≫ r = F.u k P ∧ ∀ z, (F₂.ex k₂ P₂ z).left ≫ m.φ = (F.ex k P (h z)).left := by
  have hM0 : 0 < l.M := lt_of_lt_of_le (by norm_num) l.three_le
  have hp0 : pd ≠ 0 := fun h0 => by
    have := l₂.three_le
    rw [hM, h0] at this
    omega
  have hy' := F.over_σ k P hP
  obtain ⟨o₁, ⟨m₁⟩⟩ := GlobalTheory.obj_pull E H D l _ ℂ (baseKA l) (baseOfEmb σ) σ _ _ Xo.s (𝟙 _) (F₂.u k₂ P₂ ≫ r) rfl rfl
    (hy.trans (Category.id_comp _).symm) Xo.univ
  obtain ⟨o₂, ⟨m₂⟩⟩ := GlobalTheory.obj_pull E H D l _ ℂ (baseKA l) (baseOfEmb σ) σ _ _ Xo.s (𝟙 _) (F.u k P) rfl rfl
    (hy'.trans (Category.id_comp _).symm) Xo.univ
  obtain ⟨n, hn⟩ := (GlobalTheory.sabMap_cancel_and_comp_over E H _ _ _ _ _ _ r _ (F₂.u k₂ P₂) m m₁.toSABMap rfl).1
  obtain ⟨e₁, f₁, a₁, s₁, r₁, u₁⟩ := exists_fibre_unif n hP₂ (isExp_family F₂ k₂ hP₂)
    ⟨F₂.ex_ker k₂ P₂ hP₂, F₂.ex_lin k₂ P₂ hP₂, F₂.ex_weil k₂ P₂ hP₂⟩
  obtain ⟨e₂, f₂, a₂, s₂, r₂, u₂⟩ := exists_fibre_unif m₂.toSABMap hP (isExp_family F k hP)
    ⟨F.ex_ker k P hP, F.ex_lin k P hP, F.ex_weil k P hP⟩
  obtain ⟨w, hw⟩ := exists_sabMap_types o₁ o₂ hP₂ hP a₁ s₁ s₂ r₁ r₂ u₁ u₂ gam h hEF hh
  have hmap : l₂.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) ≤ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := Ideal.map_mono hle
  obtain ⟨q, hq⟩ := exists_objMap_of_coprime hA o₁ o₂ w (l₂.Mb.map (H.bar : 𝓞 E →+* 𝓞 E))
    (eq_top_iff.2 (l₂.coprime.symm.le.trans (sup_le_sup_right hle _)))
    (fun a ha => by
      have j₂ := F.ex_eta k P hP a (Submodule.smul_mono_left hmap ha)
      have j₁ : toUnit _ ≫ Xo₂.univ.eta a ^ pd = F₂.ex k₂ P₂ ((l.M : ℂ)⁻¹ • P₂ (F₂.t k₂ a)) := by
        rw [MonObj.comp_pow, F₂.ex_eta k₂ P₂ hP₂ a ha, ← pow_of_add (F₂.ex_add k₂ P₂ hP₂), hM,
          ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, Nat.cast_mul, mul_inv, mul_left_comm,
          mul_inv_cancel₀ (Nat.cast_ne_zero.2 hp0), _root_.mul_one]
      have c₁ : (o₁.eta a).left = (e₁ ((l.M : ℂ)⁻¹ • P₂ (F₂.t k₂ a))).left := by
        refine m₁.cart.1.hom_ext ?_ ((Over.w _).trans (Over.w _).symm)
        refine (m₁.eta a).trans (Eq.trans ?_ (congrArg (_ ≫ ·) hn))
        rw [← Category.assoc (e₁ _).left, f₁, ← j₁, Category.assoc, ← heta]
        exact (Category.assoc _ _ _).symm
      have c₂ : (o₂.eta a).left = (e₂ ((l.M : ℂ)⁻¹ • P (F.t k a))).left :=
        m₂.cart.1.hom_ext ((m₂.eta a).trans ((congrArg (fun q => q.left) j₂).trans (f₂ _).symm))
          ((Over.w _).trans (Over.w _).symm)
      rw [c₁, c₂, hw, map_smul h, ← hh, (div_eq_iff hP.2.1 a₂ r₂.1 hM0 _ _).2 (gM a ha)])
    (by
      have := hw 0
      rwa [map_zero, (r₁.1 0).2 (zero_mem _), (r₂.1 0).2 (zero_mem _)] at this)
  obtain ⟨q', hq'⟩ := ((GlobalTheory.ObjMaps.id_comp_cancel E H D l _ _ _ _ _ _ _ _ _ _ _ _ Xo.univ o₂ o₁).2 (F.u k P)
    (𝟙 _) m₂).1 q
  have hyy : F₂.u k₂ P₂ ≫ r = 𝟙 _ ≫ F.u k P :=
    (GlobalTheory.moduli_rep_of_base GlobalTheory.ObjMaps.id_comp_cancel E H D l Xo ℂ (baseOfEmb σ) σ _ (𝟙 _) o₁ inferInstance rfl
      rfl).unique ⟨hy.trans (Category.id_comp _).symm, ⟨m₁⟩⟩
      ⟨by rw [Category.id_comp, hy', Category.id_comp], ⟨q'⟩⟩
  have hφ := phi_eq_of_point_eq hyy.symm m₁ q'
  refine ⟨hyy.trans (Category.id_comp _), fun z => ?_⟩
  rw [← f₁, ← f₂, ← hw, Category.assoc, Category.assoc, hn, ← hq, ← hq', hφ]

end GlobalTheory.CoverExp
