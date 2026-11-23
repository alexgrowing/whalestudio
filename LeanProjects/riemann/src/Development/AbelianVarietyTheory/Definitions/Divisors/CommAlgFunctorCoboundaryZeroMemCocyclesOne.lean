import Mathlib

set_option autoImplicit false

noncomputable section

open CategoryTheory

namespace GlobalTheory.CatCoh

universe v u v' u' v'' u''

section Complex

variable {R : Type} [CommRing R] {C : Type u} [Category.{v} C] (F : C ⥤ CommAlgCat.{0} R)

abbrev mp {T T' : C} (φ : T ⟶ T') : F.obj T →ₐ[R] F.obj T' := (F.map φ).hom

theorem mp_comp {T T' T'' : C} (φ : T ⟶ T') (ψ : T' ⟶ T'') (b : F.obj T) :
    mp F (φ ≫ ψ) b = mp F ψ (mp F φ b) := by
  simp [mp]

theorem mp_id (T : C) (b : F.obj T) : mp F (𝟙 T) b = b := by
  simp [mp]

abbrev C0 := ∀ T : C, F.obj T

abbrev C1 := ∀ (T T' : C) (_ : T ⟶ T'), F.obj T'

abbrev C2 := ∀ (T T' T'' : C) (_ : T ⟶ T') (_ : T' ⟶ T''), F.obj T''

def d0 : C0 F →ₗ[R] C1 F where
  toFun g T T' φ := g T' - mp F φ (g T)
  map_add' g g' := by funext T T' φ; simp only [Pi.add_apply, map_add]; ring
  map_smul' r g := by funext T T' φ; simp only [Pi.smul_apply, map_smul, smul_sub, RingHom.id_apply]

def d1 : C1 F →ₗ[R] C2 F where
  toFun f T T' T'' φ ψ := mp F ψ (f T T' φ) - f T T'' (φ ≫ ψ) + f T' T'' ψ
  map_add' g g' := by funext T T' T'' φ ψ; simp only [Pi.add_apply, map_add]; ring
  map_smul' r g := by
    funext T T' T'' φ ψ; simp only [Pi.smul_apply, map_smul, smul_sub, smul_add, RingHom.id_apply]

theorem amitsur_d0_apply (g : C0 F) {T T' : C} (φ : T ⟶ T') : d0 F g T T' φ = g T' - mp F φ (g T) := rfl

theorem d1_apply (f : C1 F) {T T' T'' : C} (φ : T ⟶ T') (ψ : T' ⟶ T'') :
    d1 F f T T' T'' φ ψ = mp F ψ (f T T' φ) - f T T'' (φ ≫ ψ) + f T' T'' ψ := rfl

def Z1 : Submodule R (C1 F) where
  carrier := {f | ∀ ⦃T T' T'' : C⦄ (φ : T ⟶ T') (ψ : T' ⟶ T''),
    f T T'' (φ ≫ ψ) = mp F ψ (f T T' φ) + f T' T'' ψ}
  add_mem' {f g} hf hg T T' T'' φ ψ := by
    simp only [Pi.add_apply, map_add, hf φ ψ, hg φ ψ]; ring
  zero_mem' T T' T'' φ ψ := by simp
  smul_mem' r f hf T T' T'' φ ψ := by
    simp only [Pi.smul_apply, map_smul, hf φ ψ, smul_add]

def Z2 : Submodule R (C2 F) where
  carrier := {z | ∀ ⦃T T' T'' T''' : C⦄ (φ : T ⟶ T') (ψ : T' ⟶ T'') (χ : T'' ⟶ T'''),
    mp F χ (z T T' T'' φ ψ) + z T T'' T''' (φ ≫ ψ) χ = z T T' T''' φ (ψ ≫ χ) + z T' T'' T''' ψ χ}
  add_mem' {f g} hf hg T T' T'' T''' φ ψ χ := by
    simp only [Pi.add_apply, map_add]; linear_combination hf φ ψ χ + hg φ ψ χ
  zero_mem' T T' T'' T''' φ ψ χ := by simp
  smul_mem' r f hf T T' T'' T''' φ ψ χ := by
    simp only [Pi.smul_apply, map_smul, ← smul_add, hf φ ψ χ]

variable {F}

theorem Z1.comp (f : Z1 F) {T T' T'' : C} (φ : T ⟶ T') (ψ : T' ⟶ T'') :
    f.1 T T'' (φ ≫ ψ) = mp F ψ (f.1 T T' φ) + f.1 T' T'' ψ := f.2 φ ψ

theorem Z1.id (f : Z1 F) (T : C) : f.1 T T (𝟙 T) = 0 := by
  have h := Z1.comp f (𝟙 T) (𝟙 T)
  rw [Category.id_comp, mp_id] at h
  linear_combination -h

variable (F)

theorem commAlgFunctorCocyclesOne_eq_ker : Z1 F = LinearMap.ker (d1 F) := by
  ext f
  rw [LinearMap.mem_ker]
  constructor
  · intro hf
    funext T T' T'' φ ψ
    have h : f T T'' (φ ≫ ψ) = mp F ψ (f T T' φ) + f T' T'' ψ := hf φ ψ
    show mp F ψ (f T T' φ) - f T T'' (φ ≫ ψ) + f T' T'' ψ = 0
    linear_combination -h
  · intro hf T T' T'' φ ψ
    have h := congrFun (congrFun (congrFun (congrFun (congrFun hf T) T') T'') φ) ψ
    change mp F ψ (f T T' φ) - f T T'' (φ ≫ ψ) + f T' T'' ψ = 0 at h
    show f T T'' (φ ≫ ψ) = mp F ψ (f T T' φ) + f T' T'' ψ
    linear_combination -h

theorem commAlgFunctorCoboundaryZero_mem_cocyclesOne (g : C0 F) : d0 F g ∈ Z1 F := by
  intro T T' T'' φ ψ
  simp only [amitsur_d0_apply, mp_comp, map_sub]
  ring

theorem differential_one_mem_scaled_lattice (f : C1 F) : d1 F f ∈ Z2 F := by
  intro T T' T'' T''' φ ψ χ
  simp only [d1_apply, map_add, map_sub, mp_comp, Category.assoc]
  ring

def H1 : Type _ := Z1 F ⧸ LinearMap.range ((d0 F).codRestrict (Z1 F) (commAlgFunctorCoboundaryZero_mem_cocyclesOne F))

def H2 : Type _ := Z2 F ⧸ LinearMap.range ((d1 F).codRestrict (Z2 F) (differential_one_mem_scaled_lattice F))

instance : AddCommGroup (H1 F) := inferInstanceAs (AddCommGroup (_ ⧸ LinearMap.range _))

instance : Module R (H1 F) := inferInstanceAs (Module R (_ ⧸ LinearMap.range _))

instance : AddCommGroup (H2 F) := inferInstanceAs (AddCommGroup (_ ⧸ LinearMap.range _))

instance : Module R (H2 F) := inferInstanceAs (Module R (_ ⧸ LinearMap.range _))

def H1.mk : Z1 F →ₗ[R] H1 F := Submodule.mkQ _

def H2.mk : Z2 F →ₗ[R] H2 F := Submodule.mkQ _

theorem H1.mk_surjective : Function.Surjective (H1.mk F) := by
  intro c
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ c
  exact ⟨f, rfl⟩

theorem H2.mk_surjective : Function.Surjective (H2.mk F) := by
  intro c
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ c
  exact ⟨z, rfl⟩

variable {F}

theorem H1.mk_eq_zero {f : Z1 F} : H1.mk F f = 0 ↔ ∃ g, d0 F g = f.1 := by
  change Submodule.Quotient.mk f = 0 ↔ _
  rw [Submodule.Quotient.mk_eq_zero, LinearMap.mem_range]
  constructor
  · rintro ⟨g, hg⟩
    exact ⟨g, congrArg Subtype.val hg⟩
  · rintro ⟨g, hg⟩
    exact ⟨g, Subtype.ext hg⟩

theorem H2.mk_eq_zero {z : Z2 F} : H2.mk F z = 0 ↔ ∃ f, d1 F f = z.1 := by
  change Submodule.Quotient.mk z = 0 ↔ _
  rw [Submodule.Quotient.mk_eq_zero, LinearMap.mem_range]
  constructor
  · rintro ⟨f, hf⟩
    exact ⟨f, congrArg Subtype.val hf⟩
  · rintro ⟨f, hf⟩
    exact ⟨f, Subtype.ext hf⟩

theorem H1.mk_eq_mk {f f' : Z1 F} : H1.mk F f = H1.mk F f' ↔ ∃ g, d0 F g = f.1 - f'.1 := by
  rw [← sub_eq_zero, ← map_sub, H1.mk_eq_zero]
  exact Iff.rfl

theorem H2.mk_eq_mk {z z' : Z2 F} : H2.mk F z = H2.mk F z' ↔ ∃ f, d1 F f = z.1 - z'.1 := by
  rw [← sub_eq_zero, ← map_sub, H2.mk_eq_zero]
  exact Iff.rfl

variable (F)

def cupZ : Z1 F →ₗ[R] Z1 F →ₗ[R] Z2 F :=
  LinearMap.mk₂ R
    (fun a b ↦ ⟨fun T T' T'' φ ψ ↦ mp F ψ (a.1 T T' φ) * b.1 T' T'' ψ, fun T T' T'' T''' φ ψ χ ↦ by
      simp only [Z1.comp a, Z1.comp b, map_mul, map_add, mp_comp]; ring⟩)
    (fun a a' b ↦ Subtype.ext (by funext T T' T'' φ ψ; simp [add_mul]))
    (fun r a b ↦ Subtype.ext (by funext T T' T'' φ ψ; simp))
    (fun a b b' ↦ Subtype.ext (by funext T T' T'' φ ψ; simp [mul_add]))
    (fun r a b ↦ Subtype.ext (by funext T T' T'' φ ψ; simp))

theorem cupZ_apply (a b : Z1 F) {T T' T'' : C} (φ : T ⟶ T') (ψ : T' ⟶ T'') :
    (cupZ F a b).1 T T' T'' φ ψ = mp F ψ (a.1 T T' φ) * b.1 T' T'' ψ := rfl

def cup : H1 F →ₗ[R] H1 F →ₗ[R] H2 F :=
  LinearMap.liftQ₂ _ _ ((cupZ F).compr₂ (H2.mk F))
    (by
      rintro _ ⟨g, rfl⟩
      ext b
      refine H2.mk_eq_zero.2 ⟨fun T T' φ ↦ mp F φ (g T) * b.1 T T' φ, ?_⟩
      funext T T' T'' φ ψ
      simp only [d1_apply, cupZ_apply, LinearMap.codRestrict_apply, amitsur_d0_apply, Z1.comp b, map_mul,
        map_sub, mp_comp]
      ring)
    (by
      rintro _ ⟨g, rfl⟩
      ext a
      refine H2.mk_eq_zero.2 ⟨fun T T' φ ↦ -(a.1 T T' φ * g T'), ?_⟩
      funext T T' T'' φ ψ
      simp only [d1_apply, cupZ_apply, LinearMap.codRestrict_apply, amitsur_d0_apply, Z1.comp a, map_mul,
        map_neg]
      ring)

theorem cup_mk (a b : Z1 F) : cup F (H1.mk F a) (H1.mk F b) = H2.mk F (cupZ F a b) := rfl

theorem H1.eq_zero_of_isInitial {T₀ : C} (h : Limits.IsInitial T₀) (c : H1 F) : c = 0 := by
  obtain ⟨f, rfl⟩ := H1.mk_surjective F c
  refine H1.mk_eq_zero.2 ⟨fun T => f.1 T₀ T (h.to T), ?_⟩
  funext T T' φ
  have e := Z1.comp f (h.to T) φ
  rw [h.hom_ext (h.to T ≫ φ) (h.to T')] at e
  simp only [amitsur_d0_apply]
  linear_combination e

end Complex

section Pull

variable {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R'']
  {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C'] {C'' : Type u''} [Category.{v''} C'']

structure CoefMap (σ : R →+* R') (F : C ⥤ CommAlgCat.{0} R) (F' : C' ⥤ CommAlgCat.{0} R') where

  G : C' ⥤ C

  α : ∀ T : C', F.obj (G.obj T) →+* F'.obj T
  naturality : ∀ {T T' : C'} (φ : T ⟶ T') (b : F.obj (G.obj T)),
    α T' (mp F (G.map φ) b) = mp F' φ (α T b)
  smul : ∀ (T : C') (r : R) (b : F.obj (G.obj T)), α T (r • b) = σ r • α T b

namespace CoefMap

variable {σ : R →+* R'} {τ : R' →+* R''} {F : C ⥤ CommAlgCat.{0} R} {F' : C' ⥤ CommAlgCat.{0} R'}
  {F'' : C'' ⥤ CommAlgCat.{0} R''}

def id (F : C ⥤ CommAlgCat.{0} R) : CoefMap (RingHom.id R) F F where
  G := 𝟭 C
  α _ := RingHom.id _
  naturality _ _ := rfl
  smul _ _ _ := rfl

def comp (m : CoefMap σ F F') (n : CoefMap τ F' F'') : CoefMap (τ.comp σ) F F'' where
  G := n.G ⋙ m.G
  α T := (n.α T).comp (m.α (n.G.obj T))
  naturality φ b := (congrArg (n.α _) (m.naturality (n.G.map φ) b)).trans (n.naturality φ _)
  smul T r b := (congrArg (n.α _) (m.smul _ r b)).trans (n.smul _ _ _)

def restrict (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C) : CoefMap (RingHom.id R) F (G ⋙ F) where
  G := G
  α _ := RingHom.id _
  naturality _ _ := rfl
  smul _ _ _ := rfl

variable (m : CoefMap σ F F')

def pullbackOneCocycle : Z1 F →ₛₗ[σ] Z1 F' where
  toFun f := ⟨fun T T' φ ↦ m.α T' (f.1 _ _ (m.G.map φ)), fun T T' T'' φ ψ ↦ by
    simp only [Functor.map_comp, Z1.comp f, map_add, m.naturality]⟩
  map_add' f g := Subtype.ext (by funext T T' φ; simp)
  map_smul' r f := Subtype.ext (by funext T T' φ; simp [m.smul])

def pullbackTwoCocycle : Z2 F →ₛₗ[σ] Z2 F' where
  toFun z := ⟨fun T T' T'' φ ψ ↦ m.α T'' (z.1 _ _ _ (m.G.map φ) (m.G.map ψ)),
    fun T T' T'' T''' φ ψ χ ↦ by
      simp only [Functor.map_comp, ← map_add, ← m.naturality, z.2 (m.G.map φ) (m.G.map ψ) (m.G.map χ)]⟩
  map_add' f g := Subtype.ext (by funext T T' T'' φ ψ; simp)
  map_smul' r f := Subtype.ext (by funext T T' T'' φ ψ; simp [m.smul])

theorem pullCocycleOne_apply (f : Z1 F) {T T' : C'} (φ : T ⟶ T') :
    (m.pullbackOneCocycle f).1 T T' φ = m.α T' (f.1 _ _ (m.G.map φ)) := rfl

theorem pullCocycleTwo_apply (z : Z2 F) {T T' T'' : C'} (φ : T ⟶ T') (ψ : T' ⟶ T'') :
    (m.pullbackTwoCocycle z).1 T T' T'' φ ψ = m.α T'' (z.1 _ _ _ (m.G.map φ) (m.G.map ψ)) := rfl

def pull1 : H1 F →ₛₗ[σ] H1 F' :=
  Submodule.mapQ _ _ m.pullbackOneCocycle (by
    rintro _ ⟨g, rfl⟩
    refine ⟨fun T ↦ m.α T (g _), Subtype.ext ?_⟩
    funext T T' φ
    simp only [LinearMap.codRestrict_apply, pullCocycleOne_apply, amitsur_d0_apply, map_sub, m.naturality])

def pull2 : H2 F →ₛₗ[σ] H2 F' :=
  Submodule.mapQ _ _ m.pullbackTwoCocycle (by
    rintro _ ⟨g, rfl⟩
    refine ⟨fun T T' φ ↦ m.α T' (g _ _ (m.G.map φ)), Subtype.ext ?_⟩
    funext T T' T'' φ ψ
    simp only [LinearMap.codRestrict_apply, pullCocycleTwo_apply, d1_apply, map_sub, map_add, m.naturality,
      Functor.map_comp])

theorem pullCohomologyOne_class (f : Z1 F) : m.pull1 (H1.mk F f) = H1.mk F' (m.pullbackOneCocycle f) := rfl

theorem pullCohomologyTwo_class (z : Z2 F) : m.pull2 (H2.mk F z) = H2.mk F' (m.pullbackTwoCocycle z) := rfl

theorem pullCohomologyTwo_cup (a b : H1 F) : m.pull2 (cup F a b) = cup F' (m.pull1 a) (m.pull1 b) := by
  obtain ⟨a, rfl⟩ := H1.mk_surjective F a
  obtain ⟨b, rfl⟩ := H1.mk_surjective F b
  rw [cup_mk, pullCohomologyTwo_class, pullCohomologyOne_class, pullCohomologyOne_class, cup_mk]
  congr 1
  apply Subtype.ext
  funext T T' T'' φ ψ
  simp only [pullCocycleTwo_apply, cupZ_apply, pullCocycleOne_apply, map_mul, m.naturality]

theorem pullCohomologyOne_id (c : H1 F) : (id F).pull1 c = c := by
  obtain ⟨f, rfl⟩ := H1.mk_surjective F c
  rfl

theorem pullCohomologyTwo_id (c : H2 F) : (id F).pull2 c = c := by
  obtain ⟨z, rfl⟩ := H2.mk_surjective F c
  rfl

theorem pullCohomologyOne_comp (n : CoefMap τ F' F'') (c : H1 F) :
    (m.comp n).pull1 c = n.pull1 (m.pull1 c) := by
  obtain ⟨f, rfl⟩ := H1.mk_surjective F c
  rfl

theorem pullCohomologyTwo_comp (n : CoefMap τ F' F'') (c : H2 F) :
    (m.comp n).pull2 c = n.pull2 (m.pull2 c) := by
  obtain ⟨z, rfl⟩ := H2.mk_surjective F c
  rfl

theorem pullCohomologyOne_eq_of_natTrans {σ' : R →+* R'} (m' : CoefMap σ' F F') (θ : m.G ⟶ m'.G)
    (h : ∀ T b, m'.α T (mp F (θ.app T) b) = m.α T b) (c : H1 F) : m.pull1 c = m'.pull1 c := by
  obtain ⟨f, rfl⟩ := H1.mk_surjective F c
  rw [pullCohomologyOne_class, pullCohomologyOne_class, H1.mk_eq_mk]
  refine ⟨fun T => -(m'.α T (f.1 _ _ (θ.app T))), ?_⟩
  funext T T' φ
  have h1 := Z1.comp f (m.G.map φ) (θ.app T')
  have h2 := Z1.comp f (θ.app T) (m'.G.map φ)
  rw [θ.naturality φ] at h1
  have h3 := congrArg (m'.α T') (h1.symm.trans h2)
  rw [map_add, map_add, h, m'.naturality] at h3
  simp only [amitsur_d0_apply, map_neg, Pi.sub_apply, pullCocycleOne_apply]
  linear_combination -h3

theorem pullCohomologyTwo_eq_of_natTrans {σ' : R →+* R'} (m' : CoefMap σ' F F') (θ : m.G ⟶ m'.G)
    (h : ∀ T b, m'.α T (mp F (θ.app T) b) = m.α T b) (c : H2 F) : m.pull2 c = m'.pull2 c := by
  obtain ⟨z, rfl⟩ := H2.mk_surjective F c
  rw [pullCohomologyTwo_class, pullCohomologyTwo_class, H2.mk_eq_mk]
  refine ⟨fun T T' φ => m'.α T' (z.1 _ _ _ (m.G.map φ) (θ.app T') - z.1 _ _ _ (θ.app T) (m'.G.map φ)), ?_⟩
  funext T T' T'' φ ψ
  have e1 := z.2 (m.G.map φ) (m.G.map ψ) (θ.app T'')
  have e2 := z.2 (m.G.map φ) (θ.app T') (m'.G.map ψ)
  have e3 := z.2 (θ.app T) (m'.G.map φ) (m'.G.map ψ)
  rw [θ.naturality ψ] at e1
  rw [θ.naturality φ] at e2
  have key : mp F (θ.app T'') (z.1 _ _ _ (m.G.map φ) (m.G.map ψ)) - z.1 _ _ _ (m'.G.map φ) (m'.G.map ψ) =
      mp F (m'.G.map ψ) (z.1 _ _ _ (m.G.map φ) (θ.app T') - z.1 _ _ _ (θ.app T) (m'.G.map φ))
      - (z.1 _ _ _ (m.G.map φ ≫ m.G.map ψ) (θ.app T'') - z.1 _ _ _ (θ.app T) (m'.G.map φ ≫ m'.G.map ψ))
      + (z.1 _ _ _ (m.G.map ψ) (θ.app T'') - z.1 _ _ _ (θ.app T') (m'.G.map ψ)) := by
    rw [map_sub]
    linear_combination e1 - e2 + e3
  have e := congrArg (m'.α T'') key
  simp only [map_sub, map_add, h, m'.naturality] at e
  simp only [d1_apply, Pi.sub_apply, pullCocycleTwo_apply, Functor.map_comp, map_sub]
  linear_combination -e

end CoefMap

end Pull

end GlobalTheory.CatCoh
