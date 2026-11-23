import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.EigLatBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.AlgChart

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

namespace ReciprocityTheory.ChartRestriction.G.Chart

attribute [local instance] Over.cartesianMonoidalCategory

section Ring

variable {R : Type} [CommRing R] {B : Type} [CommRing B] [Algebra R B] (eps : B →ₐ[R] R) {n : ℕ}

def IsUnivRing (m : ℕ) (π : B →ₐ[R] JetR R (Fin n) m) : Prop :=
  ∀ (A : Type) [CommRing A] [Algebra R A] (aug : A →ₐ[R] R), (RingHom.ker aug) ^ (m + 1) = ⊥ →
    ∀ h : B →ₐ[R] A, aug.comp h = eps → ∃! ψ : JetR R (Fin n) m →ₐ[R] A, aug.comp ψ = jetAug R (Fin n) m ∧ h = ψ.comp π

variable {R' : Type} [CommRing R'] [Algebra R R']

def jetMapA (n m : ℕ) : JetR R (Fin n) m →ₐ[R] JetR R' (Fin n) m :=
  jetLift R (RingHom.ker (jetAug R' (Fin n) m)) (ker_jetAug_pow (Fin n) m) (fun j => zR m j) (fun j => zR_mem_ker m j)

theorem jetMapA_zR (m : ℕ) (j : Fin n) : jetMapA (R := R) (R' := R') n m (zR m j) = zR m j := by
  unfold jetMapA
  rw [jetLift_zR]

theorem isUnivRing_bc (m : ℕ) (π : B →ₐ[R] JetR R (Fin n) m) (hπ : IsUnivRing eps m π)
    (hπa : (jetAug R (Fin n) m).comp π = eps) (A : Type) [CommRing A] [Algebra R' A] [Algebra R A]
    [IsScalarTower R R' A] (aug : A →ₐ[R'] R') (hJ : (RingHom.ker aug) ^ (m + 1) = ⊥) (h : B →ₐ[R] A)
    (hh : (aug.restrictScalars R).comp h = (Algebra.ofId R R').comp eps) :
    ∃! ψ : JetR R' (Fin n) m →ₐ[R'] A,
      aug.comp ψ = jetAug R' (Fin n) m ∧ h = (ψ.restrictScalars R).comp ((jetMapA n m).comp π) := by
  classical
  let f1 : R × A →ₐ[R] R' := (Algebra.ofId R R').comp (AlgHom.fst R R A)
  let f2 : R × A →ₐ[R] R' := (aug.restrictScalars R).comp (AlgHom.snd R R A)
  let A' : Subalgebra R (R × A) := AlgHom.equalizer f1 f2
  have memA' : ∀ p : R × A, p ∈ A' ↔ algebraMap R R' p.1 = aug p.2 := by
    intro p
    first
      | exact Iff.rfl
      | simp [A', f1, f2, AlgHom.mem_equalizer]
  let aug' : A' →ₐ[R] R := (AlgHom.fst R R A).comp A'.val
  let snd' : A' →ₐ[R] A := (AlgHom.snd R R A).comp A'.val
  have hJ' : (RingHom.ker aug') ^ (m + 1) = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have hz1 : z ∈ RingHom.ker aug' := Ideal.pow_le_self (by omega) hz
    have hmap : Ideal.map snd' (RingHom.ker aug') ≤ RingHom.ker aug := by
      rw [Ideal.map_le_iff_le_comap]
      intro u hu
      rw [Ideal.mem_comap, RingHom.mem_ker]
      rw [RingHom.mem_ker] at hu
      have hu' := (memA' _).mp u.2
      have hu0 : (u : R × A).1 = 0 := hu
      show aug (u : R × A).2 = 0
      rw [← hu', hu0, map_zero]
    have h2 : snd' z ∈ (RingHom.ker aug) ^ (m + 1) := by
      have := Ideal.mem_map_of_mem snd' hz
      rw [Ideal.map_pow] at this
      exact Ideal.pow_right_mono hmap (m + 1) this
    rw [hJ, Ideal.mem_bot] at h2
    rw [Ideal.mem_bot]
    rw [RingHom.mem_ker] at hz1
    apply Subtype.ext
    apply Prod.ext
    · exact hz1
    · exact h2
  let h' : B →ₐ[R] A' := (eps.prod h).codRestrict A' (fun b => (memA' _).mpr (by
    have := DFunLike.congr_fun hh b
    simpa using this.symm))
  have hcomp : aug'.comp h' = eps := AlgHom.ext fun b => rfl
  obtain ⟨ψ0, ⟨hψ0a, hψ0b⟩, huniq⟩ := hπ A' aug' hJ' h' hcomp
  let ψ1 : JetR R (Fin n) m →ₐ[R] A := snd'.comp ψ0
  have hψ1z : ∀ j, ψ1 (zR m j) ∈ RingHom.ker aug := by
    intro j
    rw [RingHom.mem_ker]
    have e1 := ((memA' _).mp (ψ0 (zR m j)).2).symm
    have e2 : aug' (ψ0 (zR m j)) = 0 := by
      rw [← AlgHom.comp_apply, hψ0a]
      exact (RingHom.mem_ker).mp (zR_mem_ker m j)
    have e2' : ((ψ0 (zR m j) : A') : R × A).1 = 0 := e2
    show aug ((ψ0 (zR m j) : A') : R × A).2 = 0
    rw [e1, e2', map_zero]
  let ψ : JetR R' (Fin n) m →ₐ[R'] A :=
    jetLift R' (RingHom.ker aug) hJ (fun j => ψ1 (zR m j)) hψ1z
  have key1 : (ψ.restrictScalars R).comp (jetMapA n m) = ψ1 := by
    apply jet_ext
    intro j
    simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply, jetMapA_zR, ψ, jetLift_zR]
  refine ⟨ψ, ⟨?_, ?_⟩, ?_⟩
  · apply jet_ext
    intro j
    simp only [AlgHom.comp_apply, ψ, jetLift_zR]
    rw [(RingHom.mem_ker).mp (hψ1z j), (RingHom.mem_ker).mp (zR_mem_ker m j)]
  · rw [← AlgHom.comp_assoc, key1]
    apply AlgHom.ext
    intro b
    show h b = snd' (ψ0 (π b))
    rw [← AlgHom.comp_apply ψ0 π, ← hψ0b]
    rfl
  · rintro ψ' ⟨ha', hb'⟩
    let χ : JetR R (Fin n) m →ₐ[R] A := (ψ'.restrictScalars R).comp (jetMapA n m)
    have hχ0 : (Algebra.ofId R R').comp (jetAug R (Fin n) m) = (aug.restrictScalars R).comp χ := by
      apply jet_ext
      intro j
      have e0 : jetAug R (Fin n) m (zR m j) = 0 := (RingHom.mem_ker).mp (zR_mem_ker m j)
      have e1 : aug (ψ' (zR m j)) = 0 := by
        rw [← AlgHom.comp_apply, ha']
        exact (RingHom.mem_ker).mp (zR_mem_ker m j)
      simp only [AlgHom.comp_apply, χ, AlgHom.restrictScalars_apply, jetMapA_zR, e0, map_zero, e1]
    have hχ : ∀ u, algebraMap R R' (jetAug R (Fin n) m u) = aug (χ u) := by
      intro u
      have := DFunLike.congr_fun hχ0 u
      simpa using this
    let χ' : JetR R (Fin n) m →ₐ[R] A' :=
      ((jetAug R (Fin n) m).prod χ).codRestrict A' (fun u => (memA' _).mpr (hχ u))
    have hχ'a : aug'.comp χ' = jetAug R (Fin n) m := AlgHom.ext fun u => rfl
    have hχ'b : h' = χ'.comp π := by
      apply AlgHom.ext
      intro b
      apply Subtype.ext
      apply Prod.ext
      · show eps b = jetAug R (Fin n) m (π b)
        rw [← hπa]
        rfl
      · show h b = χ (π b)
        rw [hb']
        rfl
    have heq := huniq χ' ⟨hχ'a, hχ'b⟩
    apply jet_ext
    intro j
    have e1 : ψ' (zR m j) = χ (zR m j) := by
      simp only [χ, AlgHom.comp_apply, AlgHom.restrictScalars_apply, jetMapA_zR]
    have e2 : χ (zR m j) = ψ1 (zR m j) := by
      show ((χ' (zR m j) : A') : R × A).2 = ((ψ0 (zR m j) : A') : R × A).2
      rw [heq]
    rw [e1, e2]
    simp only [ψ, jetLift_zR]

end Ring

section Geo

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] (G : Over (Spec (CommRingCat.of R))) [GrpObj G]

abbrev fB (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] :
    Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R R'))

variable {P : Type} [CommRing P] [Algebra R' P] [Algebra R P] [IsScalarTower R R' P]

theorem sp_hom_fB : (sp (R₀ := R') P).hom ≫ fB R R' = (sp (R₀ := R) P).hom := by
  simp only [sp, Over.mk_hom, fB]
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]

def iotaB : sp (R₀ := R) P ⟶ Over.mk ((sp (R₀ := R') P).hom ≫ fB R R') :=
  Over.homMk (𝟙 _) (by rw [Category.id_comp]; exact sp_hom_fB (R := R) (R' := R') (P := P))

def pushR (y : sp (R₀ := R') P ⟶ (Over.pullback (fB R R')).obj G) : sp (R₀ := R) P ⟶ G :=
  iotaB ≫ pushPt (isGrpPullback_pullback G (fB R R')).1.w y

theorem pushR_left (y : sp (R₀ := R') P ⟶ (Over.pullback (fB R R')).obj G) :
    (pushR G y).left = y.left ≫ pullback.fst G.hom (fB R R') := by
  simp only [pushR, iotaB, pushPt, Over.comp_left, Over.homMk_left, Category.id_comp]

def pullR (q : sp (R₀ := R) P ⟶ G) : sp (R₀ := R') P ⟶ (Over.pullback (fB R R')).obj G :=
  Over.homMk ((isGrpPullback_pullback G (fB R R')).1.lift q.left (sp (R₀ := R') P).hom
    ((Over.w q).trans (sp_hom_fB (R := R) (R' := R') (P := P)).symm)) ((isGrpPullback_pullback G (fB R R')).1.lift_snd _ _ _)

theorem pushR_pullR (q : sp (R₀ := R) P ⟶ G) : pushR G (pullR (R' := R') G q) = q := by
  apply Over.OverMorphism.ext
  rw [pushR_left]
  simp only [pullR, Over.homMk_left]
  exact IsPullback.lift_fst _ _ _ _

theorem pushR_inj {y y' : sp (R₀ := R') P ⟶ (Over.pullback (fB R R')).obj G} (h : pushR G y = pushR G y') :
    y = y' := by
  have h1 : (pushR G y).left = (pushR G y').left := by rw [h]
  rw [pushR_left, pushR_left] at h1
  apply Over.OverMorphism.ext
  exact (isGrpPullback_pullback G (fB R R')).1.hom_ext h1 ((Over.w y).trans (Over.w y').symm)

theorem pushR_spMap {P' : Type} [CommRing P'] [Algebra R' P'] [Algebra R P'] [IsScalarTower R R' P'] (g : P →ₐ[R'] P')
    (y : sp (R₀ := R') P ⟶ (Over.pullback (fB R R')).obj G) :
    pushR G (spMap g ≫ y) = spMap (g.restrictScalars R) ≫ pushR G y := by
  apply Over.OverMorphism.ext
  rw [pushR_left, Over.comp_left, Over.comp_left, pushR_left, Category.assoc]
  rfl

theorem pushR_one : pushR G (1 : sp (R₀ := R') P ⟶ (Over.pullback (fB R R')).obj G) = 1 := by
  have hw := (isGrpPullback_pullback G (fB R R')).1.w
  have hmul : ∀ x y : sp (R₀ := R') P ⟶ (Over.pullback (fB R R')).obj G,
      pushR G (x * y) = pushR G x * pushR G y := by
    intro x y
    have hpp : pushPt hw (x * y) = pushPt hw x * pushPt hw y := by
      apply Over.OverMorphism.ext
      exact ((isGrpPullback_pullback G (fB R R')).2 _ x y (pushPt hw x) (pushPt hw y) rfl rfl).symm
    simp only [pushR]
    rw [hpp, MonObj.comp_mul]
  have h1 : pushR G (1 : sp (R₀ := R') P ⟶ (Over.pullback (fB R R')).obj G) *
      pushR G (1 : sp (R₀ := R') P ⟶ (Over.pullback (fB R R')).obj G) =
      pushR G (1 : sp (R₀ := R') P ⟶ (Over.pullback (fB R R')).obj G) := by
    rw [← hmul, _root_.mul_one]
  exact mul_eq_left.mp h1

variable (R R') in

def dualMapA : DualNumber R →ₐ[R] DualNumber R' :=
  { dualMapR (algebraMap R R') with
    commutes' := fun r => by ext <;> simp [dualMapR, TrivSqZeroExt.algebraMap_eq_inl'] }

theorem dualMapA_inr (t : R) : dualMapA R R' (TrivSqZeroExt.inr t) = TrivSqZeroExt.inr (algebraMap R R' t) := by
  show dualMapR (algebraMap R R') (TrivSqZeroExt.inr t) = _
  ext <;> simp [dualMapR]

end Geo

theorem tanBC_alg {R R' : Type} [CommRing R] [IsLocalRing R] [CommRing R'] [Algebra R R']
    (G : Over (Spec (CommRingCat.of R))) [GrpObj G] (n : ℕ) (x : ∀ m : ℕ, sp (R₀ := R) (JetR R (Fin n) m) ⟶ G)
    (hx : IsUnivChart G n x) :
    ∃ x' : ∀ m : ℕ, sp (R₀ := R') (JetR R' (Fin n) m) ⟶ (Over.pullback (fB R R')).obj G,
      IsUnivChart _ n x' ∧ ∀ c : Fin n → R,
        (tvec (x := x') (algebraMap R R' ∘ c)).left ≫ pullback.fst G.hom (fB R R') =
          Spec.map (CommRingCat.ofHom (dualMapR (algebraMap R R'))) ≫ (tvec (x := x) c).left := by
  obtain ⟨C⟩ := exists_chart G
  have hin : ∀ m, ∃ π : Γ(G.left, C.U) →ₐ[R] JetR R (Fin n) m, x m = pt C π := fun m =>
    exists_pt C (x m) (le_preimage_of_nil C (jetAug R (Fin n) m) (aug_surj _)
      (elt_nil _ (ker_jetAug_nil (Fin n) m)) (x m) ((Algebra.ofId R R).comp (eps C))
      ((spMap_jetAug_alt hx m).trans (pt_eps C R).symm))
  choose π hπ using hin
  have hoe : (Algebra.ofId R R).comp (eps C) = eps C := AlgHom.ext fun _ => rfl
  have hπa : ∀ m, (jetAug R (Fin n) m).comp (π m) = eps C := fun m => by
    rw [← hoe]
    apply pt_injective C
    rw [← spMap_pt, ← hπ, spMap_jetAug_alt hx, pt_eps]
  have hπtr : ∀ m, (jetTruncR R (Fin n) m).comp (π (m + 1)) = π m := fun m =>
    pt_injective C (by rw [← spMap_pt, ← hπ, ← hπ, hx.1 m])
  have hπ0 : ∀ m, (jetZeroR R (Fin n) m).comp (π m) = (Algebra.ofId R _).comp (eps C) := fun m =>
    pt_injective C (by rw [← spMap_pt, ← hπ, hx.2.1 m, pt_eps])
  have huniv : ∀ m, IsUnivRing (eps C) m (π m) := by
    intro m A _ _ aug hJ h hh
    have hy : spMap aug ≫ pt C h = 1 := by rw [spMap_pt, hh, ← hoe, pt_eps]
    obtain ⟨ψ, ⟨h1, h2⟩, hu⟩ := hx.2.2 A aug m hJ (pt C h) hy
    refine ⟨ψ, ⟨h1, pt_injective C (by rw [← spMap_pt, ← hπ]; exact h2)⟩, fun ψ₂ hψ₂ => hu ψ₂ ⟨hψ₂.1, ?_⟩⟩
    rw [hπ, spMap_pt, ← hψ₂.2]
  refine ⟨fun m => pullR G (pt C ((jetMapA n m).comp (π m))), ⟨fun m => ?_, fun m => ?_, ?_⟩, fun c => ?_⟩
  · apply pushR_inj G
    rw [pushR_spMap, pushR_pullR, pushR_pullR, spMap_pt, ← hπtr m, ← AlgHom.comp_assoc, ← AlgHom.comp_assoc]
    congr 2
    apply jet_ext
    intro j
    show jetTruncR R' (Fin n) m (jetMapA n (m + 1) (zR (m + 1) j)) = jetMapA n m (zR m j)
    rw [jetMapA_zR, jetMapA_zR]
    rfl
  · apply pushR_inj G
    rw [pushR_spMap, pushR_pullR, spMap_pt, pushR_one, ← pt_eps C (JetR R' (Fin n) 0)]
    congr 1
    have e : ((jetZeroR R' (Fin n) m).restrictScalars R).comp (jetMapA n m) = (jetMapA n 0).comp (jetZeroR R (Fin n) m) := by
      apply jet_ext
      intro j
      show jetZeroR R' (Fin n) m (jetMapA n m (zR m j)) = jetMapA n 0 (zR 0 j)
      rw [jetMapA_zR, jetMapA_zR]
      rfl
    rw [← AlgHom.comp_assoc, e, AlgHom.comp_assoc, hπ0, ← AlgHom.comp_assoc]
    congr 1
    exact AlgHom.ext fun r => (jetMapA n 0).commutes r
  · intro A _ _ aug m hJ y hy
    let _ : Algebra R A := ((algebraMap R' A).comp (algebraMap R R')).toAlgebra
    have _ : IsScalarTower R R' A := IsScalarTower.of_algebraMap_eq fun _ => rfl
    have hz : spMap (aug.restrictScalars R) ≫ pushR G y = pt C ((Algebra.ofId R R').comp (eps C)) := by
      rw [← pushR_spMap, hy, pushR_one, pt_eps]
    obtain ⟨h, hh⟩ := exists_pt C (pushR G y) (le_preimage_of_nil C (aug.restrictScalars R) (aug_surj aug)
      (fun a ha => elt_nil _ (nil_of_pow _ hJ) a ha) _ _ hz)
    have hha : (aug.restrictScalars R).comp h = (Algebra.ofId R R').comp (eps C) :=
      pt_injective C (by rw [← spMap_pt, ← hh, hz])
    obtain ⟨ψ, ⟨h1, h2⟩, hu⟩ := isUnivRing_bc (eps C) m (π m) (huniv m) (hπa m) A aug hJ h hha
    have key : ∀ ψ' : JetR R' (Fin n) m →ₐ[R'] A,
        y = spMap ψ' ≫ pullR G (pt C ((jetMapA n m).comp (π m))) ↔
          h = (ψ'.restrictScalars R).comp ((jetMapA n m).comp (π m)) := by
      intro ψ'
      constructor
      · intro e
        apply pt_injective C
        rw [← hh, e, pushR_spMap, pushR_pullR, spMap_pt]
      · intro e
        apply pushR_inj G
        rw [hh, e, pushR_spMap, pushR_pullR, spMap_pt]
    exact ⟨ψ, ⟨h1, (key ψ).mpr h2⟩, fun ψ₂ hψ₂ => hu ψ₂ ⟨hψ₂.1, (key ψ₂).mp hψ₂.2⟩⟩
  · have e1 : pushR G (tvec (x := fun m => pullR G (pt C ((jetMapA n m).comp (π m)))) (algebraMap R R' ∘ c)) =
        pt C (((dualLift (algebraMap R R' ∘ c)).restrictScalars R).comp ((jetMapA n 1).comp (π 1))) := by
      show pushR G (spMap _ ≫ _) = _
      rw [pushR_spMap, pushR_pullR, spMap_pt]
    have e2 : spMap (dualMapA R R') ≫ tvec (x := x) c = pt C ((dualMapA R R').comp ((dualLift c).comp (π 1))) := by
      show spMap _ ≫ spMap _ ≫ x 1 = _
      rw [hπ 1, spMap_pt, spMap_pt]
    have e3 : (dualMapA R R').comp ((dualLift c).comp (π 1)) =
        ((dualLift (algebraMap R R' ∘ c)).restrictScalars R).comp ((jetMapA n 1).comp (π 1)) := by
      rw [← AlgHom.comp_assoc, ← AlgHom.comp_assoc]
      congr 1
      apply jet_ext
      intro j
      show dualMapA R R' (dualLift c (zR 1 j)) = dualLift (algebraMap R R' ∘ c) (jetMapA n 1 (zR 1 j))
      rw [jetMapA_zR, dualLift_zR, dualLift_zR, dualMapA_inr]
      rfl
    rw [← pushR_left, e1, ← e3, ← e2]
    rfl

theorem tanBC : TanBCSt := by
  intro R R' _ _ _ φ G _ n x hx
  letI := φ.toAlgebra
  exact tanBC_alg G n x hx

end ReciprocityTheory.ChartRestriction.G.Chart
