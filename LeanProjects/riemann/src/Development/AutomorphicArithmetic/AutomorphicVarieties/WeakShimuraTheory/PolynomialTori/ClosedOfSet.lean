import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.ResidueCharMemLevelPrimes
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.SgnMulSelf
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.LMemMax
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.OnCompSelf
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.OnCompMap
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.SpChartL
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.SpChartP
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.CompKer
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.PhiCond
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.DecEmb
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.UnivLift
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.UnivCond

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

namespace UpperTheory.V.Ws.Po

section Eqs

variable {R R' : Type} [CommRing R] [CommRing R']

theorem prj_hom {A A' : Type} [CommRing A] [CommRing A'] (f : A →+* A') (F : GradeZeroInterpolatingElement.M4 A →+* GradeZeroInterpolatingElement.M4 A')
    (hF : ∀ (a : A) X, F (a • X) = f a • F X) (c : Fin 4 → A) (X : GradeZeroInterpolatingElement.M4 A) (i : Fin 4) :
    prj (fun a => f (c a)) (F X) i = F (prj c X i) := by
  have key : ∀ p : Polynomial A, Polynomial.aeval (F X) (p.map f) = F (Polynomial.aeval X p) := fun p => by
    induction p using Polynomial.induction_on' with
    | add p q hp hq => rw [Polynomial.map_add, map_add, map_add, map_add, hp, hq]
    | monomial n a =>
      rw [Polynomial.map_monomial, Polynomial.aeval_monomial, Polynomial.aeval_monomial, ← Algebra.smul_def,
        ← Algebra.smul_def, hF, map_pow]
  unfold prj
  rw [← key, Polynomial.map_prod]
  simp

theorem smul_map' (f : R →+* R') (a : R) (X : GradeZeroInterpolatingElement.M4 R) : f.mapMatrix (a • X) = f a • f.mapMatrix X := by
  ext i j
  simp [RingHom.mapMatrix_apply]

theorem map_zero_iff (f : R →+* R') (X : GradeZeroInterpolatingElement.M4 R) : f.mapMatrix X = 0 ↔ ∀ i j, f (X i j) = 0 :=
  Matrix.ext_iff.symm

theorem gsp_iff (f : R →+* R') (ν : R) (g : GradeZeroInterpolatingElement.M4 R) :
    IsGSp (f ν) (f.mapMatrix g) ↔ ∀ i j, f ((adj g * g - ν • (1 : GradeZeroInterpolatingElement.M4 R)) i j) = 0 := by
  rw [← map_zero_iff, map_sub, sub_eq_zero, smul_map', map_one, map_mul, IsGSp, RingHom.mapMatrix_apply,
    (grp R).2.2.2.2.2.1]
  rfl

theorem one_iff (f : R →+* R') (g : GradeZeroInterpolatingElement.M4 R) : f.mapMatrix g = 1 ↔ ∀ i j, f ((g - 1) i j) = 0 := by
  rw [← map_zero_iff, map_sub, sub_eq_zero, map_one]

variable {H : Type} [Group H]

def ordSet (I : Subgroup H) (ps : Fin 4 → H → R) (s₀ : H) (r : H →* GradeZeroInterpolatingElement.M4 R) : Set R :=
  {x | (∃ n, x = ((r s₀).charpoly - ∏ j, (Polynomial.X - Polynomial.C (ps j s₀))).coeff n) ∨
    (∃ g i j a b, i < j ∧ x = (prj (fun a => ps a s₀) (r s₀) j * r g * prj (fun a => ps a s₀) (r s₀) i) a b) ∨
    ∃ s ∈ I, ∃ i a b, x = (prj (fun a => ps a s₀) (r s₀) i * (r s - ps i s • (1 : GradeZeroInterpolatingElement.M4 R)) *
      prj (fun a => ps a s₀) (r s₀) i) a b}

theorem ord_iff (f : R →+* R') (I : Subgroup H) (ps : Fin 4 → H → R) (s₀ : H) (r : H →* GradeZeroInterpolatingElement.M4 R) :
    GradeZeroInterpolatingElement.Ord I (fun i g => f (ps i g)) s₀ (mapRep f r) ↔ ∀ x ∈ ordSet I ps s₀ r, f x = 0 := by
  have hr : ∀ g, mapRep f r g = f.mapMatrix (r g) := fun _ => rfl
  have hp := prj_hom f f.mapMatrix (smul_map' f) (fun a => ps a s₀) (r s₀)
  have h1 : (mapRep f r s₀).charpoly = ∏ j, (Polynomial.X - Polynomial.C (f (ps j s₀))) ↔
      ∀ n, f (((r s₀).charpoly - ∏ j, (Polynomial.X - Polynomial.C (ps j s₀))).coeff n) = 0 := by
    have : ∏ j, (Polynomial.X - Polynomial.C (f (ps j s₀))) =
        (∏ j, (Polynomial.X - Polynomial.C (ps j s₀))).map f := by
      rw [Polynomial.map_prod]; simp
    rw [this, hr, RingHom.mapMatrix_apply, Matrix.charpoly_map, ← sub_eq_zero, ← Polynomial.map_sub,
      Polynomial.ext_iff]
    simp only [Polynomial.coeff_map, Polynomial.coeff_zero]
  have h2 : ∀ g i j, prj (fun a => f (ps a s₀)) (mapRep f r s₀) j * mapRep f r g *
      prj (fun a => f (ps a s₀)) (mapRep f r s₀) i = 0 ↔
      ∀ a b, f ((prj (fun a => ps a s₀) (r s₀) j * r g * prj (fun a => ps a s₀) (r s₀) i) a b) = 0 := fun g i j => by
    rw [hr, hr, hp, hp, ← map_mul, ← map_mul, map_zero_iff]
  have h3 : ∀ s i, prj (fun a => f (ps a s₀)) (mapRep f r s₀) i * (mapRep f r s - f (ps i s) • (1 : GradeZeroInterpolatingElement.M4 R')) *
      prj (fun a => f (ps a s₀)) (mapRep f r s₀) i = 0 ↔
      ∀ a b, f ((prj (fun a => ps a s₀) (r s₀) i * (r s - ps i s • (1 : GradeZeroInterpolatingElement.M4 R)) *
        prj (fun a => ps a s₀) (r s₀) i) a b) = 0 := fun s i => by
    have e : f (ps i s) • (1 : GradeZeroInterpolatingElement.M4 R') = f.mapMatrix (ps i s • (1 : GradeZeroInterpolatingElement.M4 R)) := by rw [smul_map', map_one]
    rw [hr, hr, hp, e, ← map_sub, ← map_mul, ← map_mul, map_zero_iff]
  refine ⟨fun h x hx => ?_, fun h => ⟨h1.2 fun n => h _ (.inl ⟨n, rfl⟩),
    fun g i j hij => (h2 g i j).2 fun a b => h _ (.inr (.inl ⟨g, i, j, a, b, hij, rfl⟩)),
    fun s hs i => (h3 s i).2 fun a b => h _ (.inr (.inr ⟨s, hs, i, a, b, rfl⟩))⟩⟩
  obtain ⟨n, rfl⟩ | ⟨g, i, j, a, b, hij, rfl⟩ | ⟨s, hs, i, a, b, rfl⟩ := hx
  · exact h1.1 h.charpoly n
  · exact (h2 g i j).1 (h.stable g i j hij) a b
  · exact (h3 s i).1 (h.inert s hs i) a b

theorem ord_conj (u : (GradeZeroInterpolatingElement.M4 R)ˣ) {I : Subgroup H} {ps : Fin 4 → H → R} {s₀ : H} {r r' : H →* GradeZeroInterpolatingElement.M4 R}
    (hr : ∀ g, r' g = u * r g * (u⁻¹ : (GradeZeroInterpolatingElement.M4 R)ˣ)) (h : GradeZeroInterpolatingElement.Ord I ps s₀ r) : GradeZeroInterpolatingElement.Ord I ps s₀ r' := by
  let F : GradeZeroInterpolatingElement.M4 R →+* GradeZeroInterpolatingElement.M4 R := MulSemiringAction.toRingHom _ _ (ConjAct.toConjAct u)
  have hF : ∀ X, F X = u * X * (u⁻¹ : (GradeZeroInterpolatingElement.M4 R)ˣ) := fun X => by simp [F, ConjAct.units_smul_def]
  have hs : ∀ (a : R) X, F (a • X) = a • F X := fun a X => by rw [hF, hF, mul_smul_comm, smul_mul_assoc]
  have hp : ∀ i, prj (fun a => ps a s₀) (F (r s₀)) i = F (prj (fun a => ps a s₀) (r s₀) i) :=
    prj_hom (RingHom.id R) F hs (fun a => ps a s₀) (r s₀)
  have hr' : ∀ g, r' g = F (r g) := fun g => by rw [hr, hF]
  refine ⟨?_, fun g i j hij => ?_, fun s hs' i => ?_⟩
  · rw [hr, Matrix.coe_units_inv, Matrix.charpoly_units_conj, h.charpoly]
  · rw [hr', hr', hp, hp, ← map_mul, ← map_mul, h.stable g i j hij, map_zero]
  · have e : ps i s • (1 : GradeZeroInterpolatingElement.M4 R) = F (ps i s • (1 : GradeZeroInterpolatingElement.M4 R)) := by rw [hs, map_one]
    rw [hr', hr', hp, e, ← map_sub, ← map_mul, ← map_mul, h.inert s hs' i, map_zero]

theorem gsp_conj (s : Rˣ × Rˣ) {ν : R} {g : GradeZeroInterpolatingElement.M4 R} (h : IsGSp ν g) : IsGSp ν (tconj s g) := by
  obtain ⟨-, -, -, -, -, -, -, -, hmul, hone, hadj, -⟩ := grp R
  show adj (tconj s _) * tconj s _ = _
  rw [hadj, ← hmul, h]
  conv_rhs => rw [← hone s]
  ext i j
  exact mul_left_comm _ _ _

end Eqs

section Stable

variable {O : Type} [CommRing O] [IsLocalRing O] {Γ : Type} [Group Γ] [TopologicalSpace Γ]
  {rbar : Γ →* GradeZeroInterpolatingElement.M4 (ResidueField O)}

theorem closed_of_set (P : Cond O rbar)
    (h : ∀ (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (r : Lift O rbar R), ∃ S : Set R,
      ∀ (R' : Type) [CommRing R'] [Algebra O R'] [IsCO O R'] (f : R →ₐ[O] R'), P R' (r.map f) ↔ ∀ x ∈ S, f x = 0) :
    P.IsClosed := fun R _ _ _ r => by
  obtain ⟨S, hS⟩ := h R r
  refine ⟨Ideal.span S, fun R' _ _ _ f => (hS R' f).trans ⟨fun h x hx => ?_, fun h x hx => h x (Ideal.subset_span hx)⟩⟩
  exact (Ideal.span_le (I := RingHom.ker f)).2 h hx

theorem tstable {P : Cond O rbar} {R : Type} [CommRing R] [Algebra O R] [IsCO O R] {ρ : Lift O rbar R}
    (hrep : Represents P ρ)
    (hP : ∀ (R' : Type) [CommRing R'] [Algebra O R'] [IsCO O R'] (r r' : Lift O rbar R') (s : R'ˣ × R'ˣ),
      res O R' s.1 = 1 → res O R' s.2 = 1 → (∀ g, r'.hom g = tconj s (r.hom g)) → P R' r → P R' r') : ρ.TStable w4 := by
  intro R' _ _ _ f t ht
  let s : R'ˣ × R'ˣ := (t (Multiplicative.ofAdd (1, 0)), t (Multiplicative.ofAdd (0, 1)))
  have hs : ∀ j, wv s j = t (Multiplicative.ofAdd j) := fun j => by
    show t (Multiplicative.ofAdd (1, 0)) ^ j.1 * t (Multiplicative.ofAdd (0, 1)) ^ j.2 = _
    rw [← map_zpow t, ← map_zpow t, ← map_mul, ← ofAdd_zsmul, ← ofAdd_zsmul, ← ofAdd_add]
    simp
  obtain ⟨-, -, -, -, -, -, -, -, hmul, hone, -⟩ := grp R'
  let r' : Lift O rbar R' :=
    { hom := ⟨⟨fun g => tconj s ((ρ.map f).hom g), by rw [map_one, hone]⟩, fun g h => by
        show tconj s _ = _
        rw [map_mul, hmul]⟩
      cont := fun a b N => by
        show IsLocallyConstant fun g => Ideal.Quotient.mk _ ((wv s (wt a b) : R') * (ρ.map f).hom g a b)
        simp only [map_mul]
        exact (IsLocallyConstant.const _).mul ((ρ.map f).cont a b N)
      red := fun g a b => by
        show res _ _ ((wv s (wt a b) : R') * (ρ.map f).hom g a b) = _
        rw [map_mul, hs, ht, one_mul, (ρ.map f).red] }
  obtain ⟨f', hf', -⟩ := (hrep R').2 r' (hP R' _ r' s (ht _) (ht _) (fun _ => rfl) ((hrep R').1 f))
  refine ⟨f', fun g a b => ?_⟩
  rw [hf', w4_sub_w4_eq_wt, ← hs]
  rfl

end Stable

theorem phi_emb {Γ Δ : Type} [Group Γ] [TopologicalSpace Γ] [Group Δ] [TopologicalSpace Δ] (φ : Γ →* Δ)
    (hφ : Topology.IsOpenEmbedding φ) {l : ℕ} (h : PhiCond Δ l) : PhiCond Γ l := fun H hH => by
  haveI := h (H.map φ) (hφ.isOpenMap _ hH)
  let e := H.equivMapOfInjective φ hφ.injective
  have hc : Continuous e.symm := by
    refine Continuous.subtype_mk (f := fun x => (e.symm x : Γ)) (hφ.isInducing.continuous_iff.2 ?_) _
    refine continuous_subtype_val.congr fun x => ?_
    exact (congrArg Subtype.val (e.apply_symm_apply x)).symm
  refine Finite.of_injective
    (β := {ψ : H.map φ →* Multiplicative (ZMod l) // IsOpen (ψ.ker : Set (H.map φ))})
    (fun ψ => ⟨ψ.1.comp e.symm.toMonoidHom, ψ.2.preimage hc⟩) fun ψ ψ' he => ?_
  exact Subtype.ext ((MonoidHom.cancel_right e.symm.surjective).1 (congrArg Subtype.val he))

theorem frac_alg (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] :
    ∃ _ : Algebra ℚ_[l] (FractionRing O), IsScalarTower ℤ_[l] ℚ_[l] (FractionRing O) ∧
      Module.Finite ℚ_[l] (FractionRing O) := by
  have hi : Function.Injective (algebraMap ℤ_[l] O) := (dvrFacts l O).1
  haveI : FaithfulSMul ℤ_[l] O := (faithfulSMul_iff_algebraMap_injective _ _).2 hi
  have hi2 : Function.Injective (algebraMap ℤ_[l] (FractionRing O)) := by
    rw [IsScalarTower.algebraMap_eq ℤ_[l] O (FractionRing O)]
    exact (IsFractionRing.injective O _).comp hi
  letI : Algebra ℚ_[l] (FractionRing O) := (IsFractionRing.lift hi2).toAlgebra
  haveI : IsScalarTower ℤ_[l] ℚ_[l] (FractionRing O) :=
    IsScalarTower.of_algebraMap_eq fun x => (IsFractionRing.lift_algebraMap hi2 x).symm
  haveI : IsLocalization (Algebra.algebraMapSubmonoid O (nonZeroDivisors ℤ_[l])) (FractionRing O) := inferInstance
  exact ⟨inferInstance, inferInstance,
    Module.Finite.of_isLocalization ℤ_[l] O (nonZeroDivisors ℤ_[l])⟩

theorem union_iff {α : Type} {S T : Set α} {p : α → Prop} :
    ((∀ x ∈ S, p x) ∧ ∀ x ∈ T, p x) ↔ ∀ x ∈ S ∪ T, p x :=
  ⟨fun h x hx => hx.elim (h.1 x) (h.2 x), fun h => ⟨fun x hx => h x (.inl hx), fun x hx => h x (.inr hx)⟩⟩

section Main

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [hl : Fact l.Prime] {c : Coef l} (D : Raw Ω c)

theorem phi_dec (hP : Loc.LocalPublishedTheorems) (v : ℕ) [Fact v.Prime] (A : ValuationSubring Ω)
    (hA : A.valuation (v : Ω) < 1) : PhiCond (Dec (F := ℚ) A) l := by
  obtain ⟨w, hw, hAw⟩ := GlobalTheory.DecLocal.exists_place_below (p := v) (F := ℚ) A hA
  obtain ⟨j, rfl⟩ := (Loc.decEmb (F := ℚ) (Ω := Ω) (v := v)).1 A w hAw hw
  obtain ⟨-, φ, hφ, -⟩ := (Loc.decEmb (F := ℚ) (Ω := Ω) (v := v)).2 j
  exact phi_emb φ hφ (Loc.phiCond hP v l)

theorem rep_ex (hD : D.Good) (hP : Loc.LocalPublishedTheorems) (v : ℕ) (hv : v.Prime) (P : Cond c.O (D.rbarAt v))
    (hc : P.IsClosed) (ρ₀ : Lift c.O (D.rbarAt v) c.O) (h0 : P _ ρ₀) :
    ∃ (R : Type) (_ : CommRing R) (_ : Algebra c.O R) (_ : IsCO c.O R) (ρ : Lift c.O (D.rbarAt v) R),
      Represents P ρ := by
  haveI : Fact v.Prime := ⟨hv⟩
  haveI : IsGalois ℚ Ω := {}
  haveI : CompactSpace (D.Gp v) := isCompact_iff_compactSpace.1 (isClosed_Dec _).isCompact
  haveI : IsLocalHom (algebraMap ℤ_[l] c.O) := (dvrFacts l c.O).2.2.1
  haveI : Finite (ResidueField ℤ_[l]) := Finite.of_equiv _ (PadicInt.residueField (p := l)).symm.toEquiv
  haveI : Finite (ResidueField c.O) := Module.finite_of_finite (ResidueField ℤ_[l])
  haveI : CharP (ResidueField c.O) l := by
    rw [CharP.charP_iff_prime_eq_zero hl.out, ← map_natCast (residue c.O), residue_eq_zero_iff,
      mem_maximalIdeal, mem_nonunits_iff, ← map_natCast (algebraMap ℤ_[l] c.O)]
    intro hu
    exact PadicInt.prime_p.not_unit (isUnit_of_map_unit _ _ hu)
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hk, -⟩ := facts D hD
  have hlc : IsLocallyConstant (D.rbarAt v) := by
    refine IsLocallyConstant.comp_continuous (g := D.rbar) ?_ continuous_subtype_val
    refine (IsLocallyConstant.iff_exists_open _).2 fun g =>
      ⟨(fun x => g⁻¹ * x) ⁻¹' (D.rbar.ker : Set _), hk.preimage (by fun_prop), by simp, fun x hx => ?_⟩
    have : D.rbar (g⁻¹ * x) = 1 := hx
    rw [← mul_inv_cancel_left g x, map_mul, this, mul_one]
  obtain ⟨R, _, _, _, r, hr⟩ := univ_lift l c.O (D.Gp v) (Fin 4) (D.rbarAt v)
    (phi_dec hP v _ (hD.pl_over v hv)) hlc
  obtain ⟨R', _, _, _, p, -, h⟩ := univ_cond c.O (D.Gp v) (Fin 4) (D.rbarAt v) R r _ P hr hc
    ⟨c.O, inferInstance, inferInstance, inferInstance, ρ₀, trivial, h0⟩
  exact ⟨R', inferInstance, inferInstance, inferInstance, r.map p, fun C _ _ _ =>
    ⟨fun f => ((h C).1 f).2, fun r' h' => (h C).2 r' ⟨trivial, h'⟩⟩⟩

theorem mult_iff {v : ℕ} {R R' : Type} [CommRing R] [Algebra c.O R] [IsCO c.O R] [CommRing R'] [Algebra c.O R']
    [IsCO c.O R'] (r : Lift c.O (D.rbarAt v) R) (f : R →ₐ[c.O] R') :
    (∀ g : D.Gp v, IsGSp (algebraMap c.O R' (D.th g)) ((r.map f).hom g)) ↔
      ∀ x ∈ {x | ∃ (g : D.Gp v) (i j : Fin 4),
        x = (adj (r.hom g) * r.hom g - algebraMap c.O R (D.th g) • (1 : GradeZeroInterpolatingElement.M4 R)) i j}, f x = 0 := by
  have key : ∀ g : D.Gp v, IsGSp (algebraMap c.O R' (D.th g)) ((r.map f).hom g) ↔
      ∀ i j, f ((adj (r.hom g) * r.hom g - algebraMap c.O R (D.th g) • (1 : GradeZeroInterpolatingElement.M4 R)) i j) = 0 := fun g => by
    rw [← f.commutes]
    exact gsp_iff (f : R →+* R') _ (r.hom g)
  refine ⟨?_, fun h g => (key g).2 fun i j => h _ ⟨g, i, j, rfl⟩⟩
  rintro h _ ⟨g, i, j, rfl⟩
  exact (key g).1 (h g) i j

theorem closedL : D.condL.IsClosed := closed_of_set _ fun R _ _ _ r => by
  refine ⟨{x | ∃ (g : D.Gp _) (i j : Fin 4),
      x = (adj (r.hom g) * r.hom g - algebraMap c.O R (D.th g) • (1 : GradeZeroInterpolatingElement.M4 R)) i j} ∪
    ordSet ((D.Ip l).subgroupOf (D.Gp l)) (fun i g => algebraMap c.O R (D.ps i g)) D.s0 r.hom,
    fun R' _ _ _ f => Iff.trans (and_congr (mult_iff D r f) ?_) union_iff⟩
  have := ord_iff (f : R →+* R') ((D.Ip l).subgroupOf (D.Gp l)) (fun i g => algebraMap c.O R (D.ps i g)) D.s0 r.hom
  simp only [RingHom.coe_coe, AlgHom.commutes] at this
  exact this

theorem closedP (p : ℕ) : (D.condP p).IsClosed := closed_of_set _ fun R _ _ _ r => by
  refine ⟨{x | ∃ (g : D.Gp _) (i j : Fin 4),
      x = (adj (r.hom g) * r.hom g - algebraMap c.O R (D.th g) • (1 : GradeZeroInterpolatingElement.M4 R)) i j} ∪
    {x | ∃ (g : D.Gp p) (i j : Fin 4), (g : G ℚ Ω) ∈ D.Ip p ⊓ D.ψ.ker ∧ x = (r.hom g - 1) i j},
    fun R' _ _ _ f => Iff.trans (and_congr (mult_iff D r f) ?_) union_iff⟩
  refine ⟨?_, fun h g hg => (one_iff (f : R →+* R') (r.hom g)).2 fun i j => h _ ⟨g, i, j, hg, rfl⟩⟩
  rintro h _ ⟨g, i, j, hg, rfl⟩
  exact (one_iff (f : R →+* R') (r.hom g)).1 (h g hg) i j

theorem torusL {R : Type} [CommRing R] [Algebra c.O R] [IsCO c.O R] (r r' : Lift c.O (D.rbarAt l) R) (s : Rˣ × Rˣ)
    (hr : ∀ g, r'.hom g = tconj s (r.hom g)) (h : D.condL R r) : D.condL R r' := by
  refine ⟨fun g => ?_, ?_⟩
  · rw [hr]
    exact gsp_conj s (h.1 g)
  · obtain ⟨u, hu⟩ := (grp R).2.2.2.2.2.2.2.2.2.2.2.2 s
    exact ord_conj u (fun g => by rw [hr, hu]) h.2

theorem torusP (p : ℕ) {R : Type} [CommRing R] [Algebra c.O R] [IsCO c.O R] (r r' : Lift c.O (D.rbarAt p) R) (s : Rˣ × Rˣ)
    (hr : ∀ g, r'.hom g = tconj s (r.hom g)) (h : D.condP p R r) : D.condP p R r' := by
  refine ⟨fun g => ?_, fun g hg => ?_⟩
  · rw [hr]
    exact gsp_conj s (h.1 g)
  · rw [hr, h.2 g hg]
    exact (grp R).2.2.2.2.2.2.2.2.2.1 s

theorem compL (hD : D.Good) (hP : Loc.LocalPublishedTheorems) :
    ∃ (U : Type) (_ : CommRing U) (_ : Algebra c.O U) (_ : IsCO c.O U) (ρ : Lift c.O (D.rbarAt l) U) (J : Ideal U),
      Represents D.condL ρ ∧ ∀ (C : Type) [CommRing C] [Algebra c.O C] [IsCO c.O C] (f : U →ₐ[c.O] C),
        OnComp D.condL (D.r0At l) (ρ.map f) ↔ J ≤ RingHom.ker f := by
  obtain ⟨ρ₀, -, hpt⟩ := r0pt D hD
  obtain ⟨R, _, _, _, ρ, hrep⟩ := rep_ex D hD hP l hl.out _ (closedL D) _ ((ptMap D hD c.O ρ₀).1 hpt).atL
  obtain ⟨_, _, _⟩ := frac_alg l c.O
  obtain ⟨x, P, w, φ, hx, hφ, hy, -, -⟩ := Loc.spChartL hP D hD (FractionRing c.O) R ρ hrep
  refine ⟨R, inferInstance, inferInstance, inferInstance, ρ, P, hrep, fun C _ _ _ f => ?_⟩
  rw [← hx]
  exact Loc.compKer (l := l) (FractionRing c.O) _ _ R ρ hrep x P φ hφ hy C f

theorem compP (hD : D.Good) (hP : Loc.LocalPublishedTheorems) (p : ℕ) (hp : p ∈ D.Sb) :
    ∃ (U : Type) (_ : CommRing U) (_ : Algebra c.O U) (_ : IsCO c.O U) (ρ : Lift c.O (D.rbarAt p) U) (J : Ideal U),
      Represents (D.condP p) ρ ∧ ∀ (C : Type) [CommRing C] [Algebra c.O C] [IsCO c.O C] (f : U →ₐ[c.O] C),
        OnComp (D.condP p) (D.r0At p) (ρ.map f) ↔ J ≤ RingHom.ker f := by
  obtain ⟨ρ₀, -, hpt⟩ := r0pt D hD
  obtain ⟨R, _, _, _, ρ, hrep⟩ := rep_ex D hD hP p ((facts D hD).1 p hp).1 _ (closedP D p) _
    (((ptMap D hD c.O ρ₀).1 hpt).atP p hp)
  obtain ⟨_, _, _⟩ := frac_alg l c.O
  obtain ⟨x, P, w, φ, hx, hφ, hy, -, -⟩ := Loc.spChartP D hD p hp (FractionRing c.O) R ρ hrep
  refine ⟨R, inferInstance, inferInstance, inferInstance, ρ, P, hrep, fun C _ _ _ f => ?_⟩
  rw [← hx]
  exact Loc.compKer (l := l) (FractionRing c.O) _ _ R ρ hrep x P φ hφ hy C f

theorem fin_res (c : Coef l) : Finite (ResidueField c.O) ∧ CharP (ResidueField c.O) l := by
  haveI : IsLocalHom (algebraMap ℤ_[l] c.O) := (dvrFacts l c.O).2.2.1
  haveI : Finite (ResidueField ℤ_[l]) := Finite.of_equiv _ (PadicInt.residueField (p := l)).symm.toEquiv
  refine ⟨Module.finite_of_finite (ResidueField ℤ_[l]), ?_⟩
  rw [CharP.charP_iff_prime_eq_zero hl.out, ← map_natCast (residue c.O), residue_eq_zero_iff,
    mem_maximalIdeal, mem_nonunits_iff, ← map_natCast (algebraMap ℤ_[l] c.O)]
  intro hu
  exact PadicInt.prime_p.not_unit (isUnit_of_map_unit _ _ hu)

end Main

end UpperTheory.V.Ws.Po
