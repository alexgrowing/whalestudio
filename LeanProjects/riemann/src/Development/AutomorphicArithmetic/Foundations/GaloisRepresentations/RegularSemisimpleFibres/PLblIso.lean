import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.ResEmbCompat
open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

section SlopeTestRemainingChoices

open GlobalTheory.Parabolic (mem_fixed)

variable {k K : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

private def intEquiv (i : k ≃+* K) (hi : ∀ x : k, valuation K (i x) ≤ 1 ↔ valuation k x ≤ 1) : 𝒪[k] ≃+* 𝒪[K] where
  toFun x := ⟨i x, (hi x).2 x.2⟩
  invFun y := ⟨i.symm y, (hi _).1 (by rw [i.apply_symm_apply]; exact y.2)⟩
  left_inv x := Subtype.ext (by simp)
  right_inv y := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by simp)
  map_add' x y := Subtype.ext (by simp)

private def resEquiv (i₀ : 𝒪[k] ≃+* 𝒪[K]) : 𝓀[k] ≃+* 𝓀[K] := IsLocalRing.ResidueField.mapEquiv i₀

private def glEquiv {F F' : Type} [Field F] [Field F'] (r : F ≃+* F') (n : ℕ) : GL (Fin n) F ≃ GL (Fin n) F' where
  toFun := Matrix.GeneralLinearGroup.map r.toRingHom
  invFun := Matrix.GeneralLinearGroup.map r.symm.toRingHom
  left_inv g := by ext a b; simp
  right_inv g := by ext a b; simp

variable (i : k ≃+* K) (hi : ∀ x : k, valuation K (i x) ≤ 1 ↔ valuation k x ≤ 1) {n : ℕ}

include hi

private theorem map_alg (u : GL (Fin n) 𝒪[k]) :
    Matrix.GeneralLinearGroup.map i.toRingHom (Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) u) =
      Matrix.GeneralLinearGroup.map (algebraMap 𝒪[K] K)
        (Matrix.GeneralLinearGroup.map (intEquiv i hi).toRingHom u) := by
  ext a b; rfl

private theorem map_mem_KO {g : GL (Fin n) k} (hg : g ∈ KO k (Fin n)) :
    Matrix.GeneralLinearGroup.map i.toRingHom g ∈ KO K (Fin n) := by
  obtain ⟨u, rfl⟩ := hg
  exact ⟨_, (map_alg i hi u).symm⟩

private theorem exists_KO {y : GL (Fin n) K} (hy : y ∈ KO K (Fin n)) :
    ∃ g ∈ KO k (Fin n), Matrix.GeneralLinearGroup.map i.toRingHom g = y := by
  obtain ⟨u, rfl⟩ := hy
  refine ⟨_, ⟨Matrix.GeneralLinearGroup.map (intEquiv i hi).symm.toRingHom u, rfl⟩, ?_⟩
  rw [map_alg i hi]
  congr 1
  ext a b
  simp

private theorem red_map (g : KO k (Fin n)) :
    redK K (Fin n) ⟨Matrix.GeneralLinearGroup.map i.toRingHom g, map_mem_KO i hi g.2⟩ =
      Matrix.GeneralLinearGroup.map (resEquiv (intEquiv i hi)).toRingHom (redK k (Fin n) g) := by
  ext a b
  rw [redK_apply]
  show _ = resEquiv (intEquiv i hi) ((redK k (Fin n) g : Matrix (Fin n) (Fin n) 𝓀[k]) a b)
  rw [redK_apply]
  rfl

private theorem map_mem_KOne_iff {g : GL (Fin n) k} (hg : g ∈ KO k (Fin n)) :
    Matrix.GeneralLinearGroup.map i.toRingHom g ∈ KOne K (Fin n) ↔ g ∈ KOne k (Fin n) := by
  rw [← redK_eq_one_iff ⟨g, hg⟩, ← redK_eq_one_iff ⟨_, map_mem_KO i hi hg⟩, red_map i hi ⟨g, hg⟩]
  constructor
  · intro h
    have := congrArg (glEquiv (resEquiv (intEquiv i hi)) n).symm h
    rw [show Matrix.GeneralLinearGroup.map (resEquiv (intEquiv i hi)).toRingHom (redK k (Fin n) ⟨g, hg⟩) =
      glEquiv (resEquiv (intEquiv i hi)) n (redK k (Fin n) ⟨g, hg⟩) from rfl, Equiv.symm_apply_apply] at this
    rw [this]
    exact map_one (Matrix.GeneralLinearGroup.map (resEquiv (intEquiv i hi)).symm.toRingHom)
  · intro h
    rw [h, map_one]

variable {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  (π : Representation ℂ (GL (Fin n) k) V) (P : Representation ℂ (GL (Fin n) K) W) (e : V ≃ₗ[ℂ] W)
  (he : ∀ g x, e (π g x) = P (Matrix.GeneralLinearGroup.map i.toRingHom g) (e x))

include he in
private theorem map_fixed :
    (fixed π (KOne k (Fin n))).map (e : V →ₗ[ℂ] W) = fixed P (KOne K (Fin n)) := by
  ext w
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine mem_fixed.2 fun y hy => ?_
    obtain ⟨g, hg, rfl⟩ := exists_KO i hi (GlobalTheory.StepData.KOne_le_KO hy)
    show P _ (e x) = e x
    rw [← he, mem_fixed.1 hx g ((map_mem_KOne_iff i hi hg).1 hy)]
  · intro hw
    refine ⟨e.symm w, mem_fixed.2 fun g hg => ?_, by simp⟩
    apply e.injective
    rw [he, e.apply_symm_apply,
      mem_fixed.1 hw _ ((map_mem_KOne_iff i hi (GlobalTheory.StepData.KOne_le_KO hg)).2 hg)]

private def fixEquiv : fixed π (KOne k (Fin n)) ≃ₗ[ℂ] fixed P (KOne K (Fin n)) :=
  e.ofSubmodules _ _ (map_fixed i hi π P e he)

private theorem fixEquiv_level (γ : GL (Fin n) 𝓀[k]) (x : fixed π (KOne k (Fin n))) :
    fixEquiv i hi π P e he (levelZero π γ x) =
      levelZero P (Matrix.GeneralLinearGroup.map (resEquiv (intEquiv i hi)).toRingHom γ)
        (fixEquiv i hi π P e he x) := by
  obtain ⟨g, rfl⟩ := redK_surjective γ
  rw [← red_map i hi g]
  apply Subtype.ext
  rw [levelZero_apply]
  show e (levelZero π (redK k (Fin n) g) x : V) = P _ (e x)
  rw [levelZero_apply, he]

include he in
private theorem trace_level (γ : GL (Fin n) 𝓀[k]) :
    LinearMap.trace ℂ _ (levelZero P (Matrix.GeneralLinearGroup.map (resEquiv (intEquiv i hi)).toRingHom γ)) =
      LinearMap.trace ℂ _ (levelZero π γ) := by
  have h : levelZero P (Matrix.GeneralLinearGroup.map (resEquiv (intEquiv i hi)).toRingHom γ) =
      (fixEquiv i hi π P e he).conj (levelZero π γ) := by
    refine LinearMap.ext fun x => ?_
    obtain ⟨y, rfl⟩ := (fixEquiv i hi π P e he).surjective x
    rw [LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply, fixEquiv_level]
  rw [h, LinearMap.trace_conj']

end SlopeTestRemainingChoices

theorem UpperTheory.Gal.InertialTypesAlt.lblIso :
    JDIso → LblIso := by
  intro hJ k _ _ _ _ K _ _ _ _ i hi j hj θ N V W _ _ _ _ π P e he a ha
  obtain ⟨hok, hq, hn, hm⟩ := ha
  have hjr : ∀ x, j (algebraMap _ _ x) = algebraMap _ _ (resEquiv (intEquiv i hi) x) := by
    intro x
    obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective x
    exact hj y (intEquiv i hi y) rfl
  refine ⟨hok, hq.trans (Nat.card_congr (resEquiv (intEquiv i hi)).toEquiv), hn, ?_⟩
  unfold Meets at hm ⊢
  rw [← finsum_comp_equiv (glEquiv (resEquiv (intEquiv i hi)) N)]
  have key : ∀ γ : GL (Fin N) 𝓀[k],
      star (JD θ a.D a.L N (glEquiv (resEquiv (intEquiv i hi)) N γ)) *
          LinearMap.trace ℂ _ (levelZero P (glEquiv (resEquiv (intEquiv i hi)) N γ)) =
        star (JD (θ.comp j.toMonoidHom) a.D a.L N γ) * LinearMap.trace ℂ _ (levelZero π γ) := by
    intro γ
    rw [← hJ _ _ (resEquiv (intEquiv i hi)) j hjr θ a.D a.L N γ, ← trace_level i hi π P e he γ]
    rfl
  rw [finsum_congr key]
  exact hm
