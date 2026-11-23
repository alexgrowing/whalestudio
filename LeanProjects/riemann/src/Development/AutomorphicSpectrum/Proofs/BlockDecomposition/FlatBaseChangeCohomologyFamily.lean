import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SEqOne
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.CapOComp
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FlatBaseChangeCohomology
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.CosieveRel

universe w w'

theorem tens_transfer {R : Type} [CommRing R] {ι : Type} [DecidableEq ι] {N : ι → Type} [∀ i, AddCommGroup (N i)]
    [∀ i, Module R (N i)] {M M₂ : ι → Type w} [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
    [∀ i, AddCommGroup (M₂ i)] [∀ i, Module R (M₂ i)] {M' M₂' : Type w'} [AddCommGroup M'] [AddCommGroup M₂']
    {f : ∀ i, N i → M i → M'} {f₂ : ∀ i, N i → M₂ i → M₂'} (a : ∀ i, M i ≃ₗ[R] M₂ i) (a' : M' ≃+ M₂')
    (hc : ∀ i n x, a' (f i n x) = f₂ i n (a i x)) (ht : Tens R f) : Tens R f₂ := by
  obtain ⟨g, hg⟩ := ht
  let b : (∀ i, N i ⊗[R] M₂ i) ≃+ (∀ i, N i ⊗[R] M i) :=
    AddEquiv.piCongrRight fun i => (TensorProduct.congr (LinearEquiv.refl R (N i)) (a i).symm).toAddEquiv
  refine ⟨(b.trans g).trans a', fun i n x => ?_⟩
  have hb : b (Pi.single i (n ⊗ₜ x)) = Pi.single i (n ⊗ₜ (a i).symm x) := by
    funext k
    by_cases hk : k = i
    · subst hk
      simp [b]
    · simp [b, Pi.single_eq_of_ne hk]
  simp only [AddEquiv.trans_apply, hb, hg, hc, LinearEquiv.apply_symm_apply]

variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C]

theorem pull_pull_id {D : Type 1} [Category.{0} D] {F : C ⥤ ModuleCat.{0} R} {E : D ⥤ ModuleCat.{0} R}
    (m : CH.Mor F E (RingHom.id R)) (m' : CH.Mor E F (RingHom.id R)) (j : ℕ)
    (h : ∀ f, m'.pullC j (m.pullC j f) = f) (x : CH.H F j) : m'.pull j (m.pull j x) = x := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  exact congrArg Submodule.Quotient.mk (Subtype.ext (h z.1))

abbrev inn (U P : ObjectProperty C) : ObjectProperty U.FullSubcategory := fun T => P T.obj

abbrev toDirect (U P : ObjectProperty C) : (inn U P).FullSubcategory ⥤ P.FullSubcategory :=
  P.lift ((inn U P).ι ⋙ U.ι) fun T => T.property

abbrev ofDirect {U P : ObjectProperty C} (h : P ≤ U) : P.FullSubcategory ⥤ (inn U P).FullSubcategory :=
  (inn U P).lift (U.lift P.ι fun T => h _ T.property) fun T => T.property

def dirMor (F : C ⥤ ModuleCat.{0} R) (U P : ObjectProperty C) :
    CH.Mor (P.ι ⋙ F) ((inn U P).ι ⋙ U.ι ⋙ F) (RingHom.id R) where
  G := toDirect U P
  τ _ := LinearMap.id
  nat _ _ := rfl

def itMor (F : C ⥤ ModuleCat.{0} R) {U P : ObjectProperty C} (h : P ≤ U) :
    CH.Mor ((inn U P).ι ⋙ U.ι ⋙ F) (P.ι ⋙ F) (RingHom.id R) where
  G := ofDirect h
  τ _ := LinearMap.id
  nat _ _ := rfl

def isoH (F : C ⥤ ModuleCat.{0} R) {U P : ObjectProperty C} (h : P ≤ U) (j : ℕ) :
    HU F P j ≃ₗ[R] HU (U.ι ⋙ F) (inn U P) j :=
  LinearEquiv.ofLinear ((dirMor F U P).pull j) ((itMor F h).pull j)
    (LinearMap.ext (pull_pull_id _ _ j fun _ => rfl)) (LinearMap.ext (pull_pull_id _ _ j fun _ => rfl))

theorem isoH_apply (F : C ⥤ ModuleCat.{0} R) {U P : ObjectProperty C} (h : P ≤ U) (j : ℕ) (x : HU F P j) :
    isoH F h j x = (dirMor F U P).pull j x := rfl

theorem isoH_morU {R' : Type} [CommRing R'] {σ : R →+* R'} {C' : Type 1} [Category.{0} C']
    {F : C ⥤ ModuleCat.{0} R} {F' : C' ⥤ ModuleCat.{0} R'} (m : CH.Mor F F' σ) {U P : ObjectProperty C}
    {U' P' : ObjectProperty C'} (hU : ∀ T, U' T → U (m.G.obj T)) (hP : ∀ T, P' T → P (m.G.obj T))
    (h : P ≤ U) (h' : P' ≤ U') (j : ℕ) (x : HU F P j) :
    isoH F' h' j ((morU m hP).pull j x) =
      (morU (morU m hU) (U := inn U P) (U' := inn U' P') fun T hT => hP _ hT).pull j (isoH F h j x) := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rfl

theorem base_change_rel : ∀ {R R' : Type} [CommRing R] [CommRing R'] {σ : R →+* R'} {C C' : Type 1} [Category.{0} C] [Category.{0} C']
    (G : C' ⥤ C) {ι : Type} [Fintype ι] [DecidableEq ι] (N : ι → Type) [∀ i, AddCommGroup (N i)] [∀ i, Module R (N i)]
    [∀ i, Module.Flat R (N i)] (F : ι → (C ⥤ ModuleCat.{0} R)) (F' : C' ⥤ ModuleCat.{0} R')
    (τ : ∀ i, N i → ∀ T : C', (F i).obj (G.obj T) →ₛₗ[σ] F'.obj T) (hτ : ∀ i n {T T' : C'} (φ : T ⟶ T') x,
      τ i n T' (((F i).map (G.map φ)).hom x) = (F'.map φ).hom (τ i n T x))
    (hadd : ∀ i n n' T x, τ i (n + n') T x = τ i n T x + τ i n' T x) (hsm : ∀ i (r : R) n T x, τ i (r • n) T x = σ r • τ i n T x)
    {A : Type} [Fintype A] (W : A → ObjectProperty C) (W' : A → ObjectProperty C')
    (hW : ∀ α ⦃T T' : C⦄, (T ⟶ T') → W α T → (∃ β, W β T') → W α T')
    (hW' : ∀ α ⦃T T' : C'⦄, (T ⟶ T') → W' α T → (∃ β, W' β T') → W' α T') (h : ∀ α T, W' α T → W α (G.obj T)),
    (∀ S : Finset A, S.Nonempty → ∀ j, Tens R (N := N) (M := fun i => HU (F i) (capS W S) j) (M' := HU F' (capS W' S) j)
      fun i n x => (morU (⟨G, τ i n, hτ i n⟩ : CH.Mor (F i) F' σ) (U := capS W S) (U' := capS W' S)
        fun T hT α hα => h α T (hT α hα)).pull j x) →
    ∀ j, Tens R (N := N) (M := fun i => HU (F i) (fun T => ∃ α, W α T) j) (M' := HU F' (fun T => ∃ α, W' α T) j)
      fun i n x => (morU (⟨G, τ i n, hτ i n⟩ : CH.Mor (F i) F' σ) (U := fun T => ∃ α, W α T) (U' := fun T => ∃ α, W' α T)
        fun T ⟨α, hα⟩ => ⟨α, h α T hα⟩).pull j x := by
  intro R R' _ _ σ C C' _ _ G ι _ _ N _ _ _ F F' τ hτ hadd hsm A _ W W' hW hW' h hyp j
  let U : ObjectProperty C := fun T => ∃ α, W α T
  let U' : ObjectProperty C' := fun T => ∃ α, W' α T
  have hUU : ∀ T, U' T → U (G.obj T) := fun T ⟨α, hα⟩ => ⟨α, h α T hα⟩
  let G₁ : U'.FullSubcategory ⥤ U.FullSubcategory := U.lift (U'.ι ⋙ G) fun T => hUU _ T.property
  refine GlobalTheory.CompanionTheory.CosieveBC.base_change_of_cover (C := U.FullSubcategory) (C' := U'.FullSubcategory) G₁ N
    (fun i => U.ι ⋙ F i) (U'.ι ⋙ F') (fun i n T => τ i n T.obj) (fun i n _ _ φ x => hτ i n φ.hom x)
    (fun i n n' T x => hadd i n n' T.obj x) (fun i r n T x => hsm i r n T.obj x)
    (fun α T => W α T.obj) (fun α T => W' α T.obj)
    (fun α _ T' φ hT => hW α φ.hom hT T'.property) (fun α _ T' φ hT => hW' α φ.hom hT T'.property)
    (fun T => T.property) (fun T => T.property) (fun α T hT => h α T.obj hT) ?_ j
  intro S hS j
  obtain ⟨α₀, hα₀⟩ := hS
  have hP : capS W S ≤ U := fun T hT => ⟨α₀, hT α₀ hα₀⟩
  have hP' : capS W' S ≤ U' := fun T hT => ⟨α₀, hT α₀ hα₀⟩
  refine tens_transfer (fun i => isoH (F i) hP j) (isoH F' hP' j).toAddEquiv (fun i n x => ?_) (hyp S ⟨α₀, hα₀⟩ j)
  exact isoH_morU (⟨G, τ i n, hτ i n⟩ : CH.Mor (F i) F' σ) hUU (fun T hT α hα => h α T (hT α hα)) hP hP' j x

end GlobalTheory.CompanionTheory.CosieveRel
