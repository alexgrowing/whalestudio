import Development.EtaleCohomology.EtaleSheaves.LineHigh

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC

namespace LateralTheory.E.MayerVietorisSequence

def MVSpc : Prop := A1 → ∀ (R : Type) [CommRing R] (F : Shv R), ∃ d : ∀ {U V E : Spc} (f : U ⟶ E) (g : V ⟶ E), Cover2 R f g →
  ∀ n : ℤ, H R (pullback f g) F n →+ H R E F (n + 1),
  (∀ {U V E : Spc} (f : U ⟶ E) (g : V ⟶ E) (h : Cover2 R f g) (n : ℤ),
    (∀ a b, pull R (pullback.fst f g) F n a = pull R (pullback.snd f g) F n b ↔ ∃ x, pull R f F n x = a ∧ pull R g F n x = b) ∧
    (∀ c, d f g h n c = 0 ↔ ∃ a b, c = pull R (pullback.fst f g) F n a - pull R (pullback.snd f g) F n b) ∧
    ∀ x, (pull R f F (n + 1) x = 0 ∧ pull R g F (n + 1) x = 0) ↔ ∃ c, d f g h n c = x) ∧
  ∀ {U V E U' V' E' : Spc} (f : U ⟶ E) (g : V ⟶ E) (f' : U' ⟶ E') (g' : V' ⟶ E') (p : E ⟶ E') (u : U ⟶ U') (v : V ⟶ V')
    (hu : f ≫ p = u ≫ f') (hv : g ≫ p = v ≫ g') (h : Cover2 R f g) (h' : Cover2 R f' g') (n : ℤ) c,
    pull R p F (n + 1) (d f' g' h' n c) = d f g h n (pull R (pullback.map f g f' g' u v p hu hv) F n c)

def OpenCov : Prop := ∀ (R : Type) [CommRing R] {U V X : Scheme.{0}} (f : U ⟶ X) (g : V ⟶ X) [IsOpenImmersion f]
  [IsOpenImmersion g], Set.range f ∪ Set.range g = Set.univ → Cover2 R (sch.map f) (sch.map g)

def SchPB : Prop := ∀ {U V X : Scheme.{0}} (f : U ⟶ X) (g : V ⟶ X), IsIso (pullbackComparison sch f g)

variable (R : Type) [CommRing R]

theorem pull_hom_inv {E E' : Spc} (e : E ⟶ E') [IsIso e] (F : Shv R) (n : ℤ) (x : H R E F n) :
    pull R e F n (pull R (inv e) F n x) = x := by
  rw [← pull_comp, IsIso.hom_inv_id, pull_id]

theorem pull_inv_hom {E E' : Spc} (e : E ⟶ E') [IsIso e] (F : Shv R) (n : ℤ) (x : H R E' F n) :
    pull R (inv e) F n (pull R e F n x) = x := by
  rw [← pull_comp, IsIso.inv_hom_id, pull_id]

theorem pull_inj_of_iso' {E E' : Spc} (e : E ⟶ E') [IsIso e] (F : Shv R) (n : ℤ) :
    Function.Injective (pull R e F n) := fun x y h => by
  rw [← pull_inv_hom R e F n x, h, pull_inv_hom]

theorem comp_sq (hP : SchPB) {U V X U' V' X' : Scheme.{0}} (f : U ⟶ X) (g : V ⟶ X) (f' : U' ⟶ X') (g' : V' ⟶ X')
    (u : U ⟶ U') (v : V ⟶ V') (p : X ⟶ X') (hu : f ≫ p = u ≫ f') (hv : g ≫ p = v ≫ g')
    (hu' : sch.map f ≫ sch.map p = sch.map u ≫ sch.map f') (hv' : sch.map g ≫ sch.map p = sch.map v ≫ sch.map g') :
    have := hP f g; have := hP f' g'
    inv (pullbackComparison sch f g) ≫ sch.map (pullback.map f g f' g' u v p hu hv) =
      pullback.map _ _ _ _ (sch.map u) (sch.map v) (sch.map p) hu' hv' ≫ inv (pullbackComparison sch f' g') := by
  have := hP f g; have := hP f' g'
  rw [IsIso.inv_comp_eq, ← Category.assoc, IsIso.eq_comp_inv]
  apply pullback.hom_ext
  · simp only [Category.assoc, pullbackComparison_comp_fst, pullback.lift_fst, ← Functor.map_comp, pullback.lift_fst_assoc]
    rw [pullbackComparison_comp_fst_assoc, ← Functor.map_comp]
  · simp only [Category.assoc, pullbackComparison_comp_snd, pullback.lift_snd, ← Functor.map_comp, pullback.lift_snd_assoc]
    rw [pullbackComparison_comp_snd_assoc, ← Functor.map_comp]

end LateralTheory.E.MayerVietorisSequence

open LateralTheory.E.MayerVietorisSequence in
theorem LateralTheory.E.t_E2Cut.MV_of_three (hS : MVSpc) (hC : OpenCov) (hP : SchPB) : LateralTheory.E.t_E2Cut.MV := by
  classical
  intro hyp R _ F
  obtain ⟨d, hex, hnat⟩ := hS hyp.a1 R F
  refine ⟨fun {U V X} f g n => if h : Cover2 R (sch.map f) (sch.map g) then
    have := hP f g; (d _ _ h n).comp (pull R (inv (pullbackComparison sch f g)) F n) else 0, ?_, ?_⟩
  · intro U V X f g _ _ hcov n
    have := hP f g
    have h := hC R f g hcov
    obtain ⟨h1, h2, h3⟩ := hex (sch.map f) (sch.map g) h n
    have hf : sch.map (pullback.fst f g) = pullbackComparison sch f g ≫ pullback.fst _ _ :=
      (pullbackComparison_comp_fst _ _ _).symm
    have hg : sch.map (pullback.snd f g) = pullbackComparison sch f g ≫ pullback.snd _ _ :=
      (pullbackComparison_comp_snd _ _ _).symm
    simp only [dif_pos h, AddMonoidHom.comp_apply]
    refine ⟨?_, ?_, ?_⟩
    · intro a b hab
      rw [hf, hg, pull_comp, pull_comp] at hab
      exact (h1 a b).1 (pull_inj_of_iso' R _ F n hab)
    · intro w
      rw [h2]
      constructor
      · rintro ⟨a, b, hab⟩
        refine ⟨a, b, ?_⟩
        rw [hf, hg, pull_comp, pull_comp, ← map_sub, ← hab, pull_hom_inv]
      · rintro ⟨a, b, rfl⟩
        refine ⟨a, b, ?_⟩
        rw [hf, hg, pull_comp, pull_comp, ← map_sub, pull_inv_hom]
    · intro x
      rw [h3]
      constructor
      · rintro ⟨c, rfl⟩
        exact ⟨pull R (pullbackComparison sch f g) F n c, by rw [pull_inv_hom]⟩
      · rintro ⟨w, rfl⟩
        exact ⟨_, rfl⟩
  · intro U V X U' V' X' f g f' g' _ _ _ _ hcov hcov' u v p hu hv n w
    have := hP f g; have := hP f' g'
    have h := hC R f g hcov
    have h' := hC R f' g' hcov'
    simp only [dif_pos h, dif_pos h', AddMonoidHom.comp_apply]
    have hu' : sch.map f ≫ sch.map p = sch.map u ≫ sch.map f' := by rw [← Functor.map_comp, hu, Functor.map_comp]
    have hv' : sch.map g ≫ sch.map p = sch.map v ≫ sch.map g' := by rw [← Functor.map_comp, hv, Functor.map_comp]
    rw [hnat (sch.map f) (sch.map g) (sch.map f') (sch.map g') (sch.map p) (sch.map u) (sch.map v) hu' hv' h h' n,
      ← pull_comp, ← pull_comp, comp_sq hP f g f' g' u v p hu hv hu' hv']

namespace LateralTheory.E.MayerVietorisSequence

theorem schPB : SchPB := fun f g => by
  have : PreservesLimitsOfShape WalkingCospan sch := by unfold sch; infer_instance
  infer_instance

end LateralTheory.E.MayerVietorisSequence

namespace LateralTheory.E.MayerVietorisSequence

def SES : Prop := ∀ (R : Type) [CommRing R] {U V E : Spc} (f : U ⟶ E) (g : V ⟶ E), Cover2 R f g → ∃ w,
  (ShortComplex.mk (biprod.lift ((chains R).map (pullback.fst f g)) (-(chains R).map (pullback.snd f g)))
    (biprod.desc ((chains R).map f) ((chains R).map g)) w).ShortExact

def LES : Prop := ∀ (R : Type) [CommRing R] (F : Shv R), ∃ d : ∀ {N K L M : Cx R} (a : N ⟶ K) (b : N ⟶ L) (c : K ⟶ M)
    (e : L ⟶ M) (w : biprod.lift a (-b) ≫ biprod.desc c e = 0), (ShortComplex.mk _ _ w).ShortExact →
    ∀ n : ℤ, HK R N F n →+ HK R M F (n + 1),
  (∀ {N K L M : Cx R} (a : N ⟶ K) (b : N ⟶ L) (c : K ⟶ M) (e : L ⟶ M) (w : biprod.lift a (-b) ≫ biprod.desc c e = 0)
    (hS : (ShortComplex.mk _ _ w).ShortExact) (n : ℤ),
    (∀ x y, HK.pull R a F n x = HK.pull R b F n y ↔ ∃ z, HK.pull R c F n z = x ∧ HK.pull R e F n z = y) ∧
    (∀ t, d a b c e w hS n t = 0 ↔ ∃ x y, t = HK.pull R a F n x - HK.pull R b F n y) ∧
    ∀ z, (HK.pull R c F (n + 1) z = 0 ∧ HK.pull R e F (n + 1) z = 0) ↔ ∃ t, d a b c e w hS n t = z) ∧
  ∀ {N K L M N' K' L' M' : Cx R} (a : N ⟶ K) (b : N ⟶ L) (c : K ⟶ M) (e : L ⟶ M) (a' : N' ⟶ K') (b' : N' ⟶ L')
    (c' : K' ⟶ M') (e' : L' ⟶ M') (w : biprod.lift a (-b) ≫ biprod.desc c e = 0)
    (w' : biprod.lift a' (-b') ≫ biprod.desc c' e' = 0) (hS : (ShortComplex.mk _ _ w).ShortExact)
    (hS' : (ShortComplex.mk _ _ w').ShortExact) (φN : N ⟶ N') (φK : K ⟶ K') (φL : L ⟶ L') (φM : M ⟶ M'),
    a ≫ φK = φN ≫ a' → b ≫ φL = φN ≫ b' → c ≫ φM = φK ≫ c' → e ≫ φM = φL ≫ e' → ∀ (n : ℤ) t,
    HK.pull R φM F (n + 1) (d a' b' c' e' w' hS' n t) = d a b c e w hS n (HK.pull R φN F n t)

theorem mvSpc_of (hE : SES) (hL : LES) : MVSpc := by
  intro _ R _ F
  obtain ⟨d, hex, hnat⟩ := hL R F
  refine ⟨fun f g h n => d _ _ _ _ (hE R f g h).choose (hE R f g h).choose_spec n, ?_, ?_⟩
  · intro U V E f g h n
    exact hex _ _ _ _ (hE R f g h).choose (hE R f g h).choose_spec n
  · intro U V E U' V' E' f g f' g' p u v hu hv h h' n c
    refine hnat _ _ _ _ _ _ _ _ _ _ _ _ ((chains R).map (pullback.map f g f' g' u v p hu hv)) ((chains R).map u)
      ((chains R).map v) ((chains R).map p) ?_ ?_ ?_ ?_ n c
    · rw [← Functor.map_comp, ← Functor.map_comp, pullback.lift_fst]
    · rw [← Functor.map_comp, ← Functor.map_comp, pullback.lift_snd]
    · rw [← Functor.map_comp, ← Functor.map_comp, hu]
    · rw [← Functor.map_comp, ← Functor.map_comp, hv]

end LateralTheory.E.MayerVietorisSequence
