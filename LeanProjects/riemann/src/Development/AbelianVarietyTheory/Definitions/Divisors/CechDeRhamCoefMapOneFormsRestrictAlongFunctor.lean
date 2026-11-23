import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CechDeRhamTotalDifferentialOneFunctionPart

set_option autoImplicit false

noncomputable section

open CategoryTheory KaehlerDifferential

namespace GlobalTheory.CechDR

open CatCoh

universe v u v' u' v'' u''

section Pull

variable {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R'']
  {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C'] {C'' : Type u''} [Category.{v''} C'']
  {σ : R →+* R'} {τ : R' →+* R''} {F : C ⥤ CommAlgCat.{0} R} {F' : C' ⥤ CommAlgCat.{0} R'}
  {F'' : C'' ⥤ CommAlgCat.{0} R''} (m : CoefMap σ F F')

theorem semiHom_coef (T : C') : SemiHom σ (m.α T) := m.smul T

def q1 (T : C') : Ω[F.obj (m.G.obj T)⁄R] →ₛₗ[σ] Ω[F'.obj T⁄R'] := (semiHom_coef m T).m1

def qOm (j : ℕ) (T : C') : Om R (F.obj (m.G.obj T)) j →ₛₗ[σ] Om R' (F'.obj T) j :=
  (semiHom_coef m T).mOm j

section
variable {T T' : C'}

theorem cechDeRhamCoefMapOneForms_D (b : F.obj (m.G.obj T)) : q1 m T (D R _ b) = D R' _ (m.α T b) := (semiHom_coef m T).m1_D b

theorem prodFirstProjection_smul (b : F.obj (m.G.obj T)) (ω : Ω[F.obj (m.G.obj T)⁄R]) :
    q1 m T (b • ω) = m.α T b • q1 m T ω := (semiHom_coef m T).oneFormMap_smul_semilinear b ω

theorem cechDeRhamCoefMapOneForms_naturality (φ : T ⟶ T') (ω : Ω[F.obj (m.G.obj T)⁄R]) :
    q1 m T' (p1 F (m.G.map φ) ω) = p1 F' φ (q1 m T ω) :=
  (SemiHom.oneFormMap_comp_oneFormMap _ _ ((semiHom_coef m T).comp (semiHom_mp F' φ)) (m.naturality φ) ω).trans
    (SemiHom.oneFormMap_comp_oneFormMap _ _ _ (fun _ ↦ rfl) ω).symm

theorem qOm_pOm {j : ℕ} (φ : T ⟶ T') (x : Om R (F.obj (m.G.obj T)) j) :
    qOm m j T' (pOm F j (m.G.map φ) x) = pOm F' j φ (qOm m j T x) :=
  (SemiHom.mOm_mOm _ _ ((semiHom_coef m T).comp (semiHom_mp F' φ)) (m.naturality φ) x).trans
    (SemiHom.mOm_mOm _ _ _ (fun _ ↦ rfl) x).symm

theorem qOm_dOne (ω : Ω[F.obj (m.G.obj T)⁄R]) : qOm m 2 T (dOne R _ ω) = dOne R' _ (q1 m T ω) :=
  (semiHom_coef m T).mOm_dOne ω

theorem qOm_dTwo (x : Om R (F.obj (m.G.obj T)) 2) : qOm m 3 T (dTwo R _ x) = dTwo R' _ (qOm m 2 T x) :=
  (semiHom_coef m T).mOm_dTwo x

theorem qOm_wedge (a b : Ω[F.obj (m.G.obj T)⁄R]) :
    qOm m 2 T (wedge R _ a b) = wedge R' _ (q1 m T a) (q1 m T b) := (semiHom_coef m T).mOm_wedge a b

end

def pullTot1 : Tot1 F →ₛₗ[σ] Tot1 F' where
  toFun c := (fun _ T' φ ↦ m.α T' (c.1 _ _ (m.G.map φ)), fun T ↦ q1 m T (c.2 _))
  map_add' a b := Tot1.ext (by intros; simp) (by intros; simp)
  map_smul' r a := Tot1.ext (by intros; simp [m.smul]) (by intros; simp)

def pullTot2 : Tot2 F →ₛₗ[σ] Tot2 F' where
  toFun c := (fun _ _ T'' φ ψ ↦ m.α T'' (c.1 _ _ _ (m.G.map φ) (m.G.map ψ)),
    fun _ T' φ ↦ q1 m T' (c.2.1 _ _ (m.G.map φ)), fun T ↦ qOm m 2 T (c.2.2 _))
  map_add' a b := Tot2.ext (by intros; simp) (by intros; simp) (by intros; simp)
  map_smul' r a := Tot2.ext (by intros; simp [m.smul]) (by intros; simp) (by intros; simp)

section
variable {T T' T'' : C'} (φ : T ⟶ T') (ψ : T' ⟶ T'')

theorem pullTot1_f (c : Tot1 F) : (pullTot1 m c).1 T T' φ = m.α T' (c.1 _ _ (m.G.map φ)) := rfl

theorem pullTot1_ω (c : Tot1 F) (T : C') : (pullTot1 m c).2 T = q1 m T (c.2 _) := rfl

theorem cechDeRhamPullbackTotalDegreeTwo_function_part (c : Tot2 F) :
    (pullTot2 m c).1 T T' T'' φ ψ = m.α T'' (c.1 _ _ _ (m.G.map φ) (m.G.map ψ)) := rfl

theorem pullTot2_a (c : Tot2 F) : (pullTot2 m c).2.1 T T' φ = q1 m T' (c.2.1 _ _ (m.G.map φ)) := rfl

theorem pullTot2_η (c : Tot2 F) (T : C') : (pullTot2 m c).2.2 T = qOm m 2 T (c.2.2 _) := rfl

end

theorem pullTot1_dTot0 (g : Tot0 F) : pullTot1 m (dTot0 F g) = dTot0 F' fun T ↦ m.α T (g _) :=
  Tot1.ext (fun T T' φ ↦ by simp only [pullTot1_f, dTot0_f, map_sub, m.naturality])
    fun T ↦ by simp only [pullTot1_ω, dTot0_ω, cechDeRhamCoefMapOneForms_D]

theorem pullTot2_dTot1 (c : Tot1 F) : pullTot2 m (dTot1 F c) = dTot1 F' (pullTot1 m c) :=
  Tot2.ext (fun T T' T'' φ ψ ↦ by
      simp only [cechDeRhamPullbackTotalDegreeTwo_function_part, cechDeRhamTotalDifferentialOne_functionPart, pullTot1_f, map_sub, map_add, m.naturality, Functor.map_comp])
    (fun T T' φ ↦ by simp only [pullTot2_a, dTot1_a, pullTot1_f, pullTot1_ω, map_sub, cechDeRhamCoefMapOneForms_naturality, cechDeRhamCoefMapOneForms_D])
    fun T ↦ by simp only [pullTot2_η, dTot1_η, pullTot1_ω, qOm_dOne]

theorem pullTot2_cupTot (a b : Tot1 F) :
    pullTot2 m (cupTot F a b) = cupTot F' (pullTot1 m a) (pullTot1 m b) :=
  Tot2.ext (fun T T' T'' φ ψ ↦ by simp only [cechDeRhamPullbackTotalDegreeTwo_function_part, cupTot_apply, pullTot1_f, map_mul, m.naturality])
    (fun T T' φ ↦ by simp only [pullTot2_a, cupTot_a, pullTot1_f, pullTot1_ω, map_sub, cechDeRhamCoefMapOneForms_naturality, prodFirstProjection_smul])
    fun T ↦ by simp only [pullTot2_η, cupTot_η, pullTot1_ω, qOm_wedge]

def pullZZ1 : cechDeRhamTotalCocyclesOne F →ₛₗ[σ] cechDeRhamTotalCocyclesOne F' :=
  ((pullTot1 m).domRestrict (cechDeRhamTotalCocyclesOne F)).codRestrict (cechDeRhamTotalCocyclesOne F') fun c ↦ by
    change dTot1 F' (pullTot1 m c.1) = 0
    rw [← pullTot2_dTot1, show dTot1 F c.1 = 0 from c.2, map_zero]

def pullZZ2 : cechDeRhamTotalCocyclesTwo F →ₛₗ[σ] cechDeRhamTotalCocyclesTwo F' :=
  ((pullTot2 m).domRestrict (cechDeRhamTotalCocyclesTwo F)).codRestrict (cechDeRhamTotalCocyclesTwo F') fun c ↦ by
    change pullTot2 m c.1 ∈ _
    refine mem_cechDeRhamTotalCocyclesTwo_iff.2 ⟨fun T T' T'' T''' φ ψ χ ↦ ?_, fun T T' T'' φ ψ ↦ ?_, fun T T' φ ↦ ?_, fun T ↦ ?_⟩
    · simp only [cechDeRhamPullbackTotalDegreeTwo_function_part, Functor.map_comp, ← map_add, ← m.naturality, cechDeRhamTotalCocyclesTwo.comp c]
    · simp only [cechDeRhamPullbackTotalDegreeTwo_function_part, pullTot2_a, Functor.map_comp, cechDeRhamTotalCocyclesTwo.one c, map_add, cechDeRhamCoefMapOneForms_naturality, cechDeRhamCoefMapOneForms_D]
    · simp only [pullTot2_η, pullTot2_a]
      rw [cechDeRhamTotalCocyclesTwo.two c (m.G.map φ), map_add, qOm_pOm, qOm_dOne]
    · rw [pullTot2_η, ← qOm_dTwo, cechDeRhamTotalCocyclesTwo.closed c, map_zero]

theorem coe_pullZZ1 (c : cechDeRhamTotalCocyclesOne F) : (pullZZ1 m c).1 = pullTot1 m c.1 := rfl

theorem coe_pullZZ2 (c : cechDeRhamTotalCocyclesTwo F) : (pullZZ2 m c).1 = pullTot2 m c.1 := rfl

def pullHyp1 : Hyp1 F →ₛₗ[σ] Hyp1 F' :=
  Submodule.mapQ _ _ (pullZZ1 m) (by
    rintro _ ⟨g, rfl⟩
    exact ⟨_, Subtype.ext (pullTot1_dTot0 m g).symm⟩)

def pullHyp2 : Hyp2 F →ₛₗ[σ] Hyp2 F' :=
  Submodule.mapQ _ _ (pullZZ2 m) (by
    rintro _ ⟨g, rfl⟩
    exact ⟨_, Subtype.ext (pullTot2_dTot1 m g).symm⟩)

theorem pullHyp1_mk (c : cechDeRhamTotalCocyclesOne F) : pullHyp1 m (Hyp1.mk F c) = Hyp1.mk F' (pullZZ1 m c) := rfl

theorem pullHyp2_mk (c : cechDeRhamTotalCocyclesTwo F) : pullHyp2 m (Hyp2.mk F c) = Hyp2.mk F' (pullZZ2 m c) := rfl

theorem pullHyp2_cup (a b : Hyp1 F) :
    pullHyp2 m (cupHyp F a b) = cupHyp F' (pullHyp1 m a) (pullHyp1 m b) := by
  obtain ⟨a, rfl⟩ := Hyp1.mk_surjective F a
  obtain ⟨b, rfl⟩ := Hyp1.mk_surjective F b
  exact congrArg (Hyp2.mk F') (Subtype.ext (pullTot2_cupTot m a.1 b.1))

theorem toO_pullHyp1 (c : Hyp1 F) : toO F' (pullHyp1 m c) = m.pull1 (toO F c) := by
  obtain ⟨a, rfl⟩ := Hyp1.mk_surjective F c; rfl

def pullGlob1 : Glob1 F →ₛₗ[σ] Glob1 F' where
  toFun ω := ⟨fun T ↦ q1 m T (ω.1 _), fun T T' φ ↦ by
    simp only; rw [ω.2 (m.G.map φ), cechDeRhamCoefMapOneForms_naturality]⟩
  map_add' a b := Subtype.ext (funext fun T ↦ by simp)
  map_smul' r a := Subtype.ext (funext fun T ↦ by simp)

def pullClosed1 : Closed1 F →ₛₗ[σ] Closed1 F' :=
  ((pullGlob1 m).domRestrict (Closed1 F)).codRestrict (Closed1 F') fun ω T ↦ by
    change dOne R' _ (q1 m T (ω.1.1 _)) = 0
    rw [← qOm_dOne, ω.2, map_zero]

theorem pullHyp1_ofForm (ω : Closed1 F) : pullHyp1 m (ofForm F ω) = ofForm F' (pullClosed1 m ω) :=
  congrArg (Hyp1.mk F') (Subtype.ext (Tot1.ext (fun _ _ _ ↦ map_zero _) fun _ ↦ rfl))

theorem cechDeRhamCoefMapOneForms_restrictAlongFunctor (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C) (T : C') (ω : Ω[F.obj (G.obj T)⁄R]) :
    q1 (CoefMap.restrict F G) T ω = ω := SemiHom.oneFormMap_eq_self_of_id _ (fun _ ↦ rfl) ω

theorem qOm_restrict (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C) {j : ℕ} (T : C')
    (x : Om R (F.obj (G.obj T)) j) : qOm (CoefMap.restrict F G) j T x = x :=
  SemiHom.mOm_id _ (fun _ ↦ rfl) x

theorem pullHyp1_id (c : Hyp1 F) : pullHyp1 (CoefMap.id F) c = c := by
  obtain ⟨a, rfl⟩ := Hyp1.mk_surjective F c
  exact congrArg (Hyp1.mk F) (Subtype.ext (Tot1.ext (fun _ _ _ ↦ rfl)
    fun _ ↦ SemiHom.oneFormMap_eq_self_of_id _ (fun _ ↦ rfl) _))

theorem pullHyp2_id (c : Hyp2 F) : pullHyp2 (CoefMap.id F) c = c := by
  obtain ⟨a, rfl⟩ := Hyp2.mk_surjective F c
  exact congrArg (Hyp2.mk F) (Subtype.ext (Tot2.ext (fun _ _ _ _ _ ↦ rfl)
    (fun _ _ _ ↦ SemiHom.oneFormMap_eq_self_of_id _ (fun _ ↦ rfl) _) fun _ ↦ SemiHom.mOm_id _ (fun _ ↦ rfl) _))

theorem pullHyp1_comp (n : CoefMap τ F' F'') (c : Hyp1 F) :
    pullHyp1 (m.comp n) c = pullHyp1 n (pullHyp1 m c) := by
  obtain ⟨a, rfl⟩ := Hyp1.mk_surjective F c
  exact congrArg (Hyp1.mk F'') (Subtype.ext (Tot1.ext (fun _ _ _ ↦ rfl)
    fun _ ↦ (SemiHom.oneFormMap_comp_oneFormMap _ _ _ (fun _ ↦ rfl) _).symm))

theorem pullHyp2_comp (n : CoefMap τ F' F'') (c : Hyp2 F) :
    pullHyp2 (m.comp n) c = pullHyp2 n (pullHyp2 m c) := by
  obtain ⟨a, rfl⟩ := Hyp2.mk_surjective F c
  exact congrArg (Hyp2.mk F'') (Subtype.ext (Tot2.ext (fun _ _ _ _ _ ↦ rfl)
    (fun _ _ _ ↦ (SemiHom.oneFormMap_comp_oneFormMap _ _ _ (fun _ ↦ rfl) _).symm)
    fun _ ↦ (SemiHom.mOm_mOm _ _ _ (fun _ ↦ rfl) _).symm))

section Nat

variable {σ' : R →+* R'} (m' : CoefMap σ' F F') (θ : m.G ⟶ m'.G)
  (h : ∀ T b, m'.α T (mp F (θ.app T) b) = m.α T b)
include h

theorem cechDeRhamCoefMapOneForms_eq_of_natTrans (T : C') (ω : Ω[F.obj (m.G.obj T)⁄R]) : q1 m' T (p1 F (θ.app T) ω) = q1 m T ω :=
  SemiHom.oneFormMap_comp_oneFormMap _ _ _ (h T) ω

theorem qOm_pOm_app {j : ℕ} (T : C') (x : Om R (F.obj (m.G.obj T)) j) :
    qOm m' j T (pOm F j (θ.app T) x) = qOm m j T x := SemiHom.mOm_mOm _ _ _ (h T) x

theorem pullHyp1_eq_of_natTrans (c : Hyp1 F) : pullHyp1 m c = pullHyp1 m' c := by
  obtain ⟨f, rfl⟩ := Hyp1.mk_surjective F c
  rw [pullHyp1_mk, pullHyp1_mk, Hyp1.mk_eq_mk]
  refine ⟨fun T ↦ -m'.α T (f.1.1 _ _ (θ.app T)), Tot1.ext (fun T T' φ ↦ ?_) fun T ↦ ?_⟩
  · have e := congrArg (fun ξ ↦ m'.α T' (f.1.1 _ _ ξ)) (θ.naturality φ)
    simp only [cechDeRhamTotalCocyclesOne.comp f, map_add, h, m'.naturality] at e
    simp only [dTot0_f, Prod.fst_sub, Pi.sub_apply, coe_pullZZ1, pullTot1_f, map_neg]
    linear_combination -e
  · simp only [dTot0_ω, Prod.snd_sub, Pi.sub_apply, coe_pullZZ1, pullTot1_ω, map_neg]
    rw [cechDeRhamTotalCocyclesOne.conn f (θ.app T), map_add, cechDeRhamCoefMapOneForms_eq_of_natTrans m m' θ h, cechDeRhamCoefMapOneForms_D]; abel

theorem pullHyp2_eq_of_natTrans (c : Hyp2 F) : pullHyp2 m c = pullHyp2 m' c := by
  obtain ⟨z, rfl⟩ := Hyp2.mk_surjective F c
  rw [pullHyp2_mk, pullHyp2_mk, Hyp2.mk_eq_mk]
  refine ⟨(fun T T' φ ↦ m'.α T' (z.1.1 _ _ _ (m.G.map φ) (θ.app T') -
    z.1.1 _ _ _ (θ.app T) (m'.G.map φ)), fun T ↦ -q1 m' T (z.1.2.1 _ _ (θ.app T))),
    Tot2.ext (fun T T' T'' φ ψ ↦ ?_) (fun T T' φ ↦ ?_) fun T ↦ ?_⟩
  · have e1 := congrArg (m'.α T'') (cechDeRhamTotalCocyclesTwo.comp z (m.G.map φ) (m.G.map ψ) (θ.app T''))
    have e2 := congrArg (m'.α T'') (cechDeRhamTotalCocyclesTwo.comp z (m.G.map φ) (θ.app T') (m'.G.map ψ))
    have e3 := congrArg (m'.α T'') (cechDeRhamTotalCocyclesTwo.comp z (θ.app T) (m'.G.map φ) (m'.G.map ψ))
    rw [θ.naturality ψ] at e1
    rw [θ.naturality φ] at e2
    simp only [map_add, h, m'.naturality] at e1 e2 e3
    simp only [cechDeRhamTotalDifferentialOne_functionPart, Prod.fst_sub, Pi.sub_apply, coe_pullZZ2, cechDeRhamPullbackTotalDegreeTwo_function_part, map_sub, Functor.map_comp]
    linear_combination -e1 + e2 - e3
  · have e := congrArg (fun ξ ↦ q1 m' T' (z.1.2.1 _ _ ξ)) (θ.naturality φ)
    simp only [cechDeRhamTotalCocyclesTwo.one z, map_add, cechDeRhamCoefMapOneForms_eq_of_natTrans m m' θ h, cechDeRhamCoefMapOneForms_naturality, cechDeRhamCoefMapOneForms_D] at e
    simp only [dTot1_a, Prod.fst_sub, Prod.snd_sub, Pi.sub_apply, coe_pullZZ2, pullTot2_a, map_sub,
      map_neg]
    linear_combination (norm := abel1) -e
  · simp only [dTot1_η, Prod.snd_sub, Pi.sub_apply, coe_pullZZ2, pullTot2_η, map_neg]
    rw [cechDeRhamTotalCocyclesTwo.two z (θ.app T), map_add, qOm_pOm_app m m' θ h, qOm_dOne]; abel

end Nat

end Pull

section Initial

variable (R B : Type) [CommRing R] [CommRing B] [Algebra R B]

def exact1 : Submodule R (LinearMap.ker (dOne R B)) :=
  (LinearMap.range (D R B).toLinearMap).comap (LinearMap.ker (dOne R B)).subtype

abbrev AlgebraFirstDeRham : Type := LinearMap.ker (dOne R B) ⧸ exact1 R B

variable {R B} {C : Type u} [Category.{v} C] {F : C ⥤ CommAlgCat.{0} R}
  (e : ∀ T : C, B →ₐ[R] F.obj T) (he : ∀ ⦃T T' : C⦄ (φ : T ⟶ T') (b : B), mp F φ (e T b) = e T' b)

def coneForm : LinearMap.ker (dOne R B) →ₗ[R] Closed1 F where
  toFun ω := ⟨⟨fun T ↦ (SemiHom.of_algHom (e T)).m1 ω.1, fun T T' φ ↦
    (SemiHom.oneFormMap_comp_oneFormMap _ _ _ (he φ) _).symm⟩, fun T ↦ by
      change dOne R _ ((SemiHom.of_algHom (e T)).m1 ω.1) = 0
      rw [← SemiHom.mOm_dOne, show dOne R B ω.1 = 0 from ω.2, map_zero]⟩
  map_add' a b := Subtype.ext (Subtype.ext (funext fun T ↦ map_add _ _ _))
  map_smul' r a := Subtype.ext (Subtype.ext (funext fun T ↦ (SemiHom.of_algHom (e T)).m1.map_smulₛₗ r a.1))

theorem coneForm_apply (ω : LinearMap.ker (dOne R B)) (T : C) :
    (coneForm e he ω).1.1 T = (SemiHom.of_algHom (e T)).m1 ω.1 := rfl

def coneMap : AlgebraFirstDeRham R B →ₗ[R] Hyp1 F :=
  Submodule.liftQ _ (ofForm F ∘ₗ coneForm e he) (by
    rintro ω ⟨b, hb⟩
    refine ofForm_eq_zero.2 ⟨fun T ↦ e T b, fun T T' φ ↦ (he φ b).symm, fun T ↦ ?_⟩
    rw [coneForm_apply, show ω.1 = D R B b from hb.symm, SemiHom.m1_D]; rfl)

theorem coneMap_mk (ω : LinearMap.ker (dOne R B)) :
    coneMap e he (Submodule.Quotient.mk ω) = ofForm F (coneForm e he ω) := rfl

theorem coneMap_bijective {T₀ : C} (h : Limits.IsInitial T₀) (hb : Function.Bijective (e T₀)) :
    Function.Bijective (coneMap e he) := by
  let i := (AlgEquiv.ofBijective _ hb).symm.toAlgHom
  have hi : ∀ b, i (e T₀ b) = b := (AlgEquiv.ofBijective _ hb).symm_apply_apply
  have hi' : ∀ b, e T₀ (i b) = b := (AlgEquiv.ofBijective _ hb).apply_symm_apply
  constructor
  · rw [injective_iff_map_eq_zero]
    intro c hc
    obtain ⟨ω, rfl⟩ := Submodule.Quotient.mk_surjective _ c
    obtain ⟨g, -, hg⟩ := ofForm_eq_zero.1 hc
    refine (Submodule.Quotient.mk_eq_zero _).2 ⟨i (g T₀), ?_⟩
    have := congrArg (SemiHom.of_algHom i).m1 (hg T₀)
    rw [SemiHom.m1_D, coneForm_apply] at this
    exact this.trans ((SemiHom.oneFormMap_comp_oneFormMap _ _ (SemiHom.of_algHom (AlgHom.id R B)) (fun b ↦ hi b) _).trans
      (SemiHom.oneFormMap_eq_self_of_id _ (fun _ ↦ rfl) _))
  · intro c
    have hc : c ∈ Fil1 F := H1.eq_zero_of_isInitial F h _
    rw [Fil1_eq_range] at hc
    obtain ⟨ω, rfl⟩ := hc
    refine ⟨Submodule.Quotient.mk ⟨(SemiHom.of_algHom i).m1 (ω.1.1 T₀), ?_⟩, ?_⟩
    · rw [LinearMap.mem_ker, ← SemiHom.mOm_dOne, ω.2 T₀, map_zero]
    · rw [coneMap_mk]
      refine congrArg _ (Subtype.ext (Subtype.ext (funext fun T ↦ ?_)))
      rw [coneForm_apply, ω.1.2 (h.to T)]
      exact SemiHom.oneFormMap_comp_oneFormMap _ _ (semiHom_mp F (h.to T))
        (fun b ↦ ((he (h.to T) (i b)).symm.trans (congrArg _ (hi' b)))) _

end Initial

end GlobalTheory.CechDR
