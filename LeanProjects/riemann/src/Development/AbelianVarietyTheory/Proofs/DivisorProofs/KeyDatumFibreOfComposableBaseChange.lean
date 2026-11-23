import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.UnifAlong
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.KeyEven

theorem spMap_comp' {A B K : Type} [CommRing A] [CommRing B] [CommRing K] (f : A →+* B) (h : B →+* K) :
    spMap (h.comp f) = spMap h ≫ spMap f := by
  simp [spMap, CommRingCat.ofHom_comp, Spec.map_comp]

theorem eSec_hom' {S : Scheme.{0}} (G : Over S) [GrpObj G] : eSec G ≫ G.hom = 𝟙 _ := by
  simpa [eSec] using Over.w η[G]

theorem gs_appLE' {X Y Z : Scheme.{0}} (φ : Y ⟶ X) (r : Z ⟶ Y) (p : Z) (U : X.Opens) (V : Y.Opens) (e : V ≤ φ ⁻¹ᵁ U)
    (hp : r p ∈ V) (a : Γ(X, U)) : gs r p V ((φ.appLE U V e).hom a) = gs (r ≫ φ) p U a := by
  rw [← gs_pull r φ p U (e hp) a, ← gs_res r p e hp]
  rfl

theorem dualMap_alg {B K : Type} [CommRing B] [CommRing K] (h : B →+* K) (a : B) :
    GlobalTheory.MBLow.dualMap h (algebraMap B _ a) = algebraMap K _ (h a) := by
  ext <;> simp [GlobalTheory.MBLow.dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem dualMap_eps {B K : Type} [CommRing B] [CommRing K] (h : B →+* K) :
    GlobalTheory.MBLow.dualMap h DualNumber.eps = DualNumber.eps := by
  ext <;> simp [GlobalTheory.MBLow.dualMap]

theorem dual_decomp {A : Type} [CommRing A] (z : DualNumber A) :
    z = algebraMap A _ z.fst + algebraMap A _ z.snd * DualNumber.eps := by
  ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]

theorem ringHom_dual_ext {A K : Type} [CommRing A] [CommRing K] (F G : DualNumber A →+* K)
    (h1 : ∀ a, F (algebraMap A _ a) = G (algebraMap A _ a)) (h2 : F DualNumber.eps = G DualNumber.eps) : F = G := by
  refine DFunLike.ext _ _ fun z => ?_
  rw [dual_decomp z, map_add, map_add, map_mul, map_mul, h1, h1, h2]

end GlobalTheory.KeyEven

namespace GlobalTheory.KeyEven

theorem keyPB_of_keyOn_comp : ∀ (A B K : Type) [CommRing A] [CommRing B] [CommRing K] (f : A →+* B) (h : B →+* K)
    (G : Over (Sp A)) [GrpObj G] [IsCommMonObj G] (L : RigLB G) (σ : L.L.Sec) (g : ℕ) (y : Fin g → (epsR A ⟶ G))
    (x : KeyIn B) (x' : KeyIn K) (hg : x.P.g = g) (hg' : x'.P.g = g),
    KeyOn f x G L σ (fun i => y (i.cast hg)) → KeyOn (h.comp f) x' G L σ (fun i => y (i.cast hg')) → KeyPB x' x h := by
  intro A B K _ _ _ f h G _ _ L σ g y x x' hg hg' H H'
  obtain ⟨φ, he, ψ, F, hpb, hψ, hrig, hsec, hF1, hF2, hv⟩ := H
  obtain ⟨φ', he', ψ', F', hpb', hψ', hrig', hsec', hF1', hF2', hv'⟩ := H'
  have hc : spMap (h.comp f) = spMap h ≫ spMap f := spMap_comp' f h
  obtain ⟨φ₁, h1, h2⟩ : ∃ φ₁ : x'.P.A.left ⟶ x.P.A.left, φ₁ ≫ φ = φ' ∧ φ₁ ≫ x.P.A.hom = x'.P.A.hom ≫ spMap h :=
    ⟨hpb.1.lift φ' (x'.P.A.hom ≫ spMap h) (by rw [hpb'.1.w, hc, Category.assoc]), hpb.1.lift_fst _ _ _,
      hpb.1.lift_snd _ _ _⟩
  subst h1
  have gp : IsGrpPullback x'.P.A x.P.A (spMap h) φ₁ := IsGrpPullback.cancel hpb (hpb'.congr hc rfl) h2
  have he₁ : eSec x'.P.A ≫ φ₁ = spMap h ≫ eSec x.P.A := by
    apply hpb.1.hom_ext
    · rw [Category.assoc, he', Category.assoc, he, hc, Category.assoc]
    · rw [Category.assoc, h2, ← Category.assoc, eSec_hom', Category.assoc, eSec_hom']
      rfl
  have hL := L.isLB
  have hx := x.P.isLB
  have hx' := x'.P.isLB
  have pψ := (isGen_iff ψ).1 hψ
  have pψ' := (isGen_iff ψ').1 hψ'
  obtain ⟨w, T⟩ := exists_cancel hL ψ ψ' pψ pψ' hx hx'
  have hg₁ : x'.P.g = x.P.g := hg'.trans hg.symm
  refine ⟨φ₁, he₁, w, hg₁, GlobalTheory.MBLow.dualMap h, gp, (isGen_iff w).2 (T.pgen_cancel hL pψ pψ'), ?_, ?_,
    dualMap_alg h, dualMap_eps h, ?_⟩
  ·
    have H := (maps_iff ψ _ (fun _ => eSec G) _ x.rig L.rig (spMap f) _ (rigPull_le φ (spMap f) he L.L)
      (fun _ => rfl)).1 hrig
    have H'' := (maps_iff ψ' _ (fun _ => eSec G) _ x'.rig L.rig (spMap (h.comp f)) _
      (rigPull_le (φ₁ ≫ φ) (spMap (h.comp f)) he' L.L) (fun _ => rfl)).1 hrig'
    rw [hc] at H''
    exact (maps_iff w _ (fun _ => eSec x.P.A) _ x'.rig x.rig (spMap h) _ (rigPull_le φ₁ (spMap h) he₁ x.P.L)
      (fun _ => rfl)).2 (T.pmaps_cancel hL (fun _ => he₁) H H'')
  ·
    intro j i hle
    apply fn_ext
    intro p hp
    obtain ⟨c, hcp⟩ := exists_chart hL (φ (φ₁ p))
    have hk : φ₁ p ∈ x.P.L.U (j PUnit.unit) := hle hp
    have le₀ : (L.L.pull φ).U (fun _ => c) ⊓ x.P.L.U (j PUnit.unit) ≤ φ ⁻¹ᵁ L.L.U c := fun q hq => mem_pull.1 hq.1
    have m₀ : φ₁ p ∈ (L.L.pull φ).U (fun _ => c) ⊓ x.P.L.U (j PUnit.unit) := ⟨mem_pull.2 hcp, hk⟩
    have e₀ := congrArg (gs φ₁ p _) (hsec (fun _ => c) (j PUnit.unit) le₀)
    dsimp only at e₀
    rw [gs_appLE' φ φ₁ p _ _ le₀ m₀] at e₀
    erw [gs_mul φ₁ p _ m₀] at e₀
    erw [gs_unit φ₁ p _ m₀, gs_res φ₁ p _ m₀] at e₀
    have le₁ : ((L.L.pull (φ₁ ≫ φ)).U (fun _ => c)) ⊓ x'.P.L.U i ≤ (φ₁ ≫ φ) ⁻¹ᵁ L.L.U c :=
      fun q hq => mem_pull.1 hq.1
    have m₁ : (𝟙 x'.P.A.left) p ∈ (L.L.pull (φ₁ ≫ φ)).U (fun _ => c) ⊓ x'.P.L.U i := ⟨mem_pull.2 hcp, hp.2⟩
    have e₁ := congrArg (gs (𝟙 _) p _) (hsec' (fun _ => c) i le₁)
    dsimp only at e₁
    rw [gs_appLE' (φ₁ ≫ φ) (𝟙 _) p _ _ le₁ m₁] at e₁
    erw [gs_mul (𝟙 _) p _ m₁] at e₁
    erw [gs_unit (𝟙 _) p _ m₁, gs_res (𝟙 _) p _ m₁] at e₁
    rw [Category.id_comp] at e₁
    have tri := T (x'.P.A.left) (𝟙 _) p c (j PUnit.unit) i hcp hk hp.2
    rw [gs_appLE' φ₁ (𝟙 _) p _ _ hle hp, Category.id_comp]
    erw [gs_mul (𝟙 _) p _ hp]
    erw [gs_unit (𝟙 _) p _ hp, gs_res (𝟙 _) p _ hp]
    change gs φ₁ p _ _ = (gw w (𝟙 _) p (j PUnit.unit) i).val * _
    have e₂ : (gw ψ' (𝟙 _) p c i).val * gs (𝟙 _) p (x'.P.L.U i) (x'.th.f i) =
        (gw ψ φ₁ p c (j PUnit.unit)).val * gs φ₁ p (x.P.L.U (j PUnit.unit)) (x.th.f (j PUnit.unit)) :=
      e₁.symm.trans e₀
    rw [tri, Category.id_comp, Units.val_mul, _root_.mul_assoc] at e₂
    exact ((Units.mul_right_inj _).1 e₂).symm
  ·
    intro i
    apply hpb.1.hom_ext
    · have a1 := hv (i.cast hg₁)
      have a2 := hv' i
      simp only at a1 a2
      rw [Category.assoc, a2, Category.assoc, a1, Fin.cast_cast, ← Category.assoc, ← spMap_comp']
      congr 2
      refine ringHom_dual_ext _ _ (fun a => ?_) ?_
      · simp only [RingHom.comp_apply, hF1, hF1', dualMap_alg]
      · simp only [RingHom.comp_apply, hF2, hF2', dualMap_eps]
    · rw [Category.assoc, h2, ← Category.assoc, Over.w (x'.v i), Category.assoc, Over.w (x.v _)]
      show spMap (algebraMap K (DualNumber K)) ≫ spMap h = spMap (GlobalTheory.MBLow.dualMap h) ≫ spMap (algebraMap B (DualNumber B))
      rw [← spMap_comp', ← spMap_comp']
      congr 1
      exact RingHom.ext fun a => (dualMap_alg h a).symm

end GlobalTheory.KeyEven
