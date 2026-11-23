import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.ResidueCharMemLevelPrimes
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.EntryMem
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Graded
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoSqz

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV

namespace UpperTheory.V.GradeZeroInterpolatingElement

instance dualCO (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] :
    IsCO O (DualNumber O) := co_sqz O O O fun _ => rfl

abbrev QDer {O A : Type} [CommRing O] [CommRing A] [Algebra O A] (x : A →ₐ[O] O) (a : O) :
    Submodule O (A →ₗ[O] O ⧸ Ideal.span {a}) := PtDer x (O ⧸ Ideal.span {a})

def Sp1 (O : Type) [CommRing O] [IsLocalRing O] {R : Type} [CommRing R] [Algebra O R] [IsCO O R] (h : M4 R) : Prop :=
  IsGSp 1 h ∧ h.map (res O R) = 1

namespace Ex

section

variable {R R' : Type} [CommRing R] [CommRing R']

theorem adj_map' (f : R →+* R') (X : M4 R) : adj (f.mapMatrix X) = f.mapMatrix (adj X) := by
  ext i j
  simp [adj_apply]

theorem smul_map' (f : R →+* R') (a : R) (X : M4 R) : f.mapMatrix (a • X) = f a • f.mapMatrix X := by
  ext i j
  simp [RingHom.mapMatrix_apply]

theorem isGSp_map (f : R →+* R') {ν : R} {g : M4 R} (h : IsGSp ν g) : IsGSp (f ν) (f.mapMatrix g) := by
  unfold IsGSp at *
  rw [adj_map', ← map_mul, h, smul_map', map_one]

theorem aeval_map' (f : R →+* R') (X : M4 R) (p : Polynomial R) :
    Polynomial.aeval (f.mapMatrix X) (p.map f) = f.mapMatrix (Polynomial.aeval X p) := by
  rw [Polynomial.aeval_def, Polynomial.aeval_def, Polynomial.eval₂_map, Polynomial.hom_eval₂]
  congr 1
  refine RingHom.ext fun r => ?_
  ext i j
  by_cases h : i = j
  · subst h
    simp [Matrix.algebraMap_eq_diagonal]
  · simp [Matrix.algebraMap_eq_diagonal, Matrix.diagonal_apply, h]

theorem prj_map (f : R →+* R') (c : Fin 4 → R) (X : M4 R) (i : Fin 4) :
    prj (fun a => f (c a)) (f.mapMatrix X) i = f.mapMatrix (prj c X i) := by
  simp only [prj]
  rw [← aeval_map']
  congr 1
  simp [Polynomial.map_prod]

theorem ord_map {H : Type} [Group H] (f : R →+* R') {I : Subgroup H} {ps : Fin 4 → H → R} {s₀ : H}
    {r : H →* M4 R} {r' : H →* M4 R'} (hr : ∀ g, r' g = f.mapMatrix (r g)) {ps' : Fin 4 → H → R'}
    (hps : ∀ i g, ps' i g = f (ps i g)) (h : Ord I ps s₀ r) : Ord I ps' s₀ r' := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [hr, hps, RingHom.mapMatrix_apply, Matrix.charpoly_map, h.charpoly, Polynomial.map_prod,
      Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
  · intro g i j hij
    simp only [hr, hps]
    rw [prj_map, prj_map, ← map_mul, ← map_mul, h.stable g i j hij, map_zero]
  · intro s hs i
    simp only [hr, hps]
    have e : f.mapMatrix (r s) - f (ps i s) • (1 : M4 R') = f.mapMatrix (r s - ps i s • 1) := by
      rw [map_sub, smul_map', map_one]
    rw [e, prj_map, ← map_mul, ← map_mul, h.inert s hs i, map_zero]

end

section

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c)
  {R : Type} [CommRing R] [Algebra c.O R] [IsCO c.O R] {R' : Type} [CommRing R'] [Algebra c.O R'] [IsCO c.O R']

theorem condL_map (f : R →ₐ[c.O] R') (ρ : Lift c.O (D.rbarAt l) R) (h : D.condL R ρ) :
    D.condL R' (ρ.map f) := by
  have hm : ∀ g, (ρ.map f).hom g = (f : R →+* R').mapMatrix (ρ.hom g) := fun g => by
    ext a b
    exact Lift.map_hom f ρ g a b
  refine ⟨fun g => ?_, ord_map (f : R →+* R') hm (fun i g => (f.commutes _).symm) h.2⟩
  rw [hm, ← f.commutes]
  exact isGSp_map (f : R →+* R') (h.1 g)

theorem condP_map (p : ℕ) (f : R →ₐ[c.O] R') (ρ : Lift c.O (D.rbarAt p) R) (h : D.condP p R ρ) :
    D.condP p R' (ρ.map f) := by
  refine ⟨fun g => ?_, fun g hg => ?_⟩
  · have := isGSp_map (f : R →+* R') (h.1 g)
    rw [RingHom.coe_coe, f.commutes] at this
    exact this
  · show (f : R →+* R').mapMatrix (ρ.hom g) = 1
    rw [h.2 g hg, map_one]

theorem mult_map (f : R →ₐ[c.O] R') (ρ : Lift c.O D.rbar R) (h : D.Mult ρ.hom) : D.Mult (ρ.map f).hom := by
  intro g
  have hm : (ρ.map f).hom g = (f : R →+* R').mapMatrix (ρ.hom g) := by
    ext a b
    exact Lift.map_hom f ρ g a b
  rw [hm, ← f.commutes]
  exact isGSp_map (f : R →+* R') (h g)

theorem unr_map (f : R →ₐ[c.O] R') (ρ : Lift c.O D.rbar R) (h : D.UnrT ρ.hom 1) :
    D.UnrT (ρ.map f).hom 1 := by
  intro A hA g hg h1
  show (f : R →+* R').mapMatrix (ρ.hom g) = 1
  rw [h A hA g hg h1, map_one]

theorem hEl_map (f : R →ₐ[c.O] R') (ρ : Lift c.O D.rbar R) (i j : Fin 4) :
    D.hEl (ρ.map f).hom i j = f (D.hEl ρ.hom i j) := by
  simp only [Raw.hEl, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Lift.map_hom, map_add, map_mul, AlgHom.commutes]

theorem loc_map (f : R →ₐ[c.O] R') (ρ : Lift c.O D.rbar R) (v : ℕ) :
    D.loc (ρ.map f) v = (D.loc ρ v).map f := Lift.ext (MonoidHom.ext fun _ => rfl)

theorem nrm_map (f : R →ₐ[c.O] R') (ρ : Lift c.O D.rbar R) (h : D.Nrm ρ.hom) : D.Nrm (ρ.map f).hom := by
  refine ⟨fun i j hij => ?_, ?_, ?_⟩
  · rw [Lift.map_hom, h.1 i j hij, map_zero]
  · rw [hEl_map, h.2.1, map_zero]
  · rw [hEl_map, h.2.2, map_zero]

end

end Ex

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l}

theorem Raw.LocEqs.map {D : Raw Ω c} {R : Type} [CommRing R] [Algebra c.O R] [IsCO c.O R] {R' : Type} [CommRing R']
    [Algebra c.O R'] [IsCO c.O R'] {ρ : ∀ v : D.T, Lift c.O (D.rbarAt v) R} (h : D.LocEqs ρ) (f : R →ₐ[c.O] R') :
    D.LocEqs fun v => (ρ v).map f :=
  ⟨Ex.condL_map D f _ h.1, fun p hp => Ex.condP_map D p f _ (h.2 p hp)⟩

structure IsFr {D : Raw Ω c} (L : LocBase D) {R : Type} [CommRing R] [Algebra c.O R] [IsCO c.O R] (i : L.B →ₐ[c.O] R)
    (r : Lift c.O D.rbar R) (α : D.T → M4 R) : Prop where
  mult : D.Mult r.hom
  unr : D.UnrT r.hom 1
  sp : ∀ v, Sp1 c.O (α v)
  atL : α ⟨l, D.residueChar_mem_levelPrimes⟩ = 1
  loc : ∀ (v : D.T) (g : D.Gp v), r.hom g * α v = α v * ((L.ρ v).hom g).map i

structure Fr (D : Raw Ω c) (L : LocBase D) where
  U : Type
  [cU : CommRing U]
  [aU : Algebra c.O U]
  [coU : IsCO c.O U]
  i : L.B →ₐ[c.O] U
  r : Lift c.O D.rbar U
  α : D.T → M4 U
  fr : IsFr L i r α
  univ : ∀ (R : Type) [CommRing R] [Algebra c.O R] [IsCO c.O R] (i' : L.B →ₐ[c.O] R) (r' : Lift c.O D.rbar R)
    (α' : D.T → M4 R), IsFr L i' r' α' → ∃! y : U →ₐ[c.O] R, y.comp i = i' ∧ r.map y = r' ∧ ∀ v, (α v).map y = α' v
  W : WPres c.O (ℤ × ℤ) U
  τ : Type
  κ : Type
  [fτ : Fintype τ]
  [fκ : Fintype κ]
  e : L.W.σ ⊕ τ ≃ W.σ
  f : κ → MvPowerSeries W.σ c.O
  wf : κ → ℤ × ℤ
  rel : IsRelPres L.W i W e f wf
  homr : ∀ g a b, r.hom g a b ∈ W.part (wt a b)
  homα : ∀ v a b, α v a b ∈ W.part (wt a b)
  vars : ∀ t, ∃ a b, W.wt (e (.inr t)) = wt a b ∧
    ((∃ g, W.z (e (.inr t)) = r.hom g a b - algebraMap c.O U (D.r0 g a b)) ∨ ∃ v, W.z (e (.inr t)) = (α v - 1) a b)
  org : W.HasOrigin
  at0r : ∀ g a b, W.origin org (r.hom g a b) = D.r0 g a b
  at0α : ∀ v, (α v).map (W.origin org) = 1
  at0i : (W.origin org).comp i = L.W.origin L.org
  numf : ∀ j, Nat.card {u // wf u = j} =
    Nat.card {t // W.wt (e (.inr t)) = j} + (if j = 0 then 2 else if j = wPs ∨ j = -wPs then 1 else 0)
  numz : ∀ j, j ≠ 0 → j ≠ wPs → j ≠ -wPs → Nat.card {t // W.wt (e (.inr t)) = j} = 0

attribute [instance] Fr.cU Fr.aU Fr.coU Fr.fτ Fr.fκ

structure Cover {O X B U : Type} [CommRing O] [IsDomain O] [IsLocalRing O] [AddCommGroup X] [CommRing B] [Algebra O B]
    [CommRing U] [Algebra O U] (WB : WPres O X B) (hB : WB.HasOrigin) (i : B →ₐ[O] U) (W : WPres O X U) (h : W.HasOrigin)
    {τ κ : Type} (e : WB.σ ⊕ τ ≃ W.σ) (wf : κ → X) (n : X → ℕ) where
  P : Type
  [cP : CommRing P]
  [aP : Algebra O P]
  [coP : IsCO O P]
  WP : WPres O X P
  org : WP.HasOrigin
  p : P →ₐ[O] U
  iP : B →ₐ[O] P
  g : κ → P
  wts : ∀ s, ∃ s', WP.wt s = W.wt s'
  surj : Function.Surjective p
  part : ∀ j, W.part j = (WP.part j).map p.toLinearMap
  comp : p.comp iP = i
  org_p : (W.origin h).comp p = WP.origin org
  hg : ∀ u, g u ∈ WP.part (wf u)
  ker : RingHom.ker p = Ideal.span (Set.range g)
  smooth : SmoothPt WP.part (WP.origin org) fun j => n j + Nat.card {t // W.wt (e (.inr t)) = j}
  der : ∀ (a : O) (j : X), ∀ Db ∈ QDer (W.origin h) a, ∀ DB ∈ PtDer (WB.origin hB) O,
    HasWt WB.part j DB → (∀ x, Db (i x) = Ideal.Quotient.mk _ (DB x)) →
    (∀ t, W.wt (e (.inr t)) ≠ j → Db (W.z (e (.inr t))) = 0) →
    ∃ δ ∈ PtDer (WP.origin org) O, HasWt WP.part j δ ∧ ∀ y, Ideal.Quotient.mk _ (δ y) = Db (p y)

attribute [instance] Cover.cP Cover.aP Cover.coP

end UpperTheory.V.GradeZeroInterpolatingElement

end
