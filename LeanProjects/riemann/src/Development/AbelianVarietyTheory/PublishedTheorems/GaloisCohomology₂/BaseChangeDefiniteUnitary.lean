import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.FiniteIntertwining

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions

namespace GlobalTheory.UnitaryBC

section Linear

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

variable (E a) in

def splitCentre (t : ℝ) : GA E a :=
  infGL E a (Units.map (Matrix.scalar (Fin a)).toMonoidHom (expU fun _ : InfinitePlace E => (t : ℂ)))

variable (E a) in

def latticeGL : Subgroup (GA E a) := (ratGL E a).range ⊔ Subgroup.zpowers (splitCentre E a 1)

def IsSqInt (φ : GA E a → ℂ) : Prop :=
  (∀ t g, φ (splitCentre E a t * g) = φ g) ∧
    letI : MeasurableSpace (GA E a) := borel _
    ∃ (μ : Measure (GA E a)) (𝓕 : Set (GA E a)), μ.IsHaarMeasure ∧ IsFundamentalDomain (latticeGL E a) 𝓕 μ ∧
      ∫⁻ g in 𝓕, ‖φ g‖ₑ ^ 2 ∂μ < ⊤

structure IsDiscrete (V : Submodule ℂ (Sm E a)) : Prop where
  aut : ∀ φ ∈ V, IsAutForm φ
  sqInt : ∀ φ ∈ V, IsSqInt φ.1
  stable : IsStable V
  ne_bot : V ≠ ⊥
  irred : ∀ W ≤ V, IsStable W → W = ⊥ ∨ W = V

def IsLocCompGL (V : Submodule ℂ (Sm E a)) (w : HeightOneSpectrum (𝓞 E))
    (σ : SmIrr (GL (Fin a) (w.adicCompletion E))) : Prop :=
  ∃ f : σ.V →ₗ[ℂ] Sm E a, f ≠ 0 ∧ (∀ v, f v ∈ V) ∧ ∀ g v, f (σ.ρ g v) = finRep E a (locGL E a w g) (f v)

def HasInfCharGL (V : Submodule ℂ (Sm E a)) (τ : E →+* ℂ) (m : Multiset ℂ) : Prop :=
  Multiset.card m = a ∧ ∀ u, ∀ φ ∈ V, cap τ u φ = (m.map (u + ·)).prod • φ

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField in
omit [IsTotallyComplex E] in

def locProd {c n : ℕ} {N : Fin c → ℕ} (h : ∑ i, N i = n) (w : HeightOneSpectrum (𝓞 E))
    (σ : ∀ i, SmIrr (GL (Fin (N i)) (w.adicCompletion E))) :=
  GlobalTheory.SmGL.multiProd (GlobalTheory.SmGL.stdBlocks N h) fun i => (σ i).ρ

end Linear

section CM

variable (E : Type) [Field E] [NumberField E] [IsCMField E] {a : ℕ}

variable {E} in

def IsCsdGL (V : Submodule ℂ (Sm E a)) : Prop :=
  ∃ T : V ≃ₗ[ℂ] V, ∀ (o : Op E a) (φ ψ : V), ψ.1 = act (thetaOp o) φ.1 → (T ψ).1 = act o (T φ).1

def conjAd : Ad E →+* Ad E :=
  RingHom.prodMap
    ((infEq E).toRingHom.comp ((starRingEnd (Cinf E)).comp (infEq E).symm.toRingHom))
    (conjFin (IsCMField.complexConj E).toRingEquiv)

abbrev UA (n : ℕ) : Subgroup (GA E n) := UJ (conjAd E) 1

variable {E} {n : ℕ}

def cInf : UA E n →* GL (Fin n) (Cinf E) := (GeneralLinearGroup.map (pInf E)).comp (UA E n).subtype

def cLoc (w : HeightOneSpectrum (𝓞 E)) : UA E n →* GL (Fin n) (w.adicCompletion E) :=
  (GeneralLinearGroup.map ((pLoc E w).comp (pFin E))).comp (UA E n).subtype

def cEmb (τ : E →+* ℂ) : UA E n →* GL (Fin n) ℂ := (GeneralLinearGroup.map (coord τ)).comp cInf

variable (E n) in

def ratU : Subgroup (UA E n) := (ratGL E n).range.subgroupOf (UA E n)

variable (E n) in

def finU : Subgroup (UA E n) := (cInf (E := E) (n := n)).ker

variable (E n) in

def infU : Subgroup (UA E n) := ((GeneralLinearGroup.map (pFin E)).comp (UA E n).subtype).ker

variable (n) in

def locU (w : HeightOneSpectrum (𝓞 E)) : Subgroup (UA E n) :=
  finU E n ⊓ ⨅ (u : HeightOneSpectrum (𝓞 E))
    (_ : u.under (𝓞 (maximalRealSubfield E)) ≠ w.under (𝓞 (maximalRealSubfield E))), (cLoc u).ker

variable (n) in

def embU (τ : E →+* ℂ) : Subgroup (UA E n) :=
  infU E n ⊓ ⨅ (τ' : E →+* ℂ) (_ : InfinitePlace.mk τ' ≠ InfinitePlace.mk τ), (cEmb τ').ker

variable (E n) in

abbrev RU : Representation ℂ (UA E n) (UA E n → ℂ) := rightReg ℂ (UA E n) ℂ

structure IsAutFormU (φ : UA E n → ℂ) : Prop where
  cont : Continuous φ
  left : ∀ γ ∈ ratU E n, ∀ g, φ (γ * g) = φ g
  level : IsOpen {k : finU E n | RU E n k φ = φ}
  kfin : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : infU E n => RU E n k φ))

structure IsAutRepU (π : Submodule ℂ (UA E n → ℂ)) : Prop where
  aut : ∀ φ ∈ π, IsAutFormU φ
  stable : ∀ x, ∀ φ ∈ π, RU E n x φ ∈ π
  ne_bot : π ≠ ⊥
  irred : ∀ W ≤ π, (∀ x, ∀ φ ∈ W, RU E n x φ ∈ W) → W = ⊥ ∨ W = π

def IsCompAlong (π : Submodule ℂ (UA E n → ℂ)) (Gv : Subgroup (UA E n)) {H W : Type} [Group H] [AddCommGroup W]
    [Module ℂ W] (p : Gv →* H) (σ : Representation ℂ H W) : Prop :=
  σ.IsIrreducible ∧
    ∃ f : W →ₗ[ℂ] (UA E n → ℂ), f ≠ 0 ∧ (∀ v, f v ∈ π) ∧ ∀ (x : Gv) v, f (σ (p x) v) = RU E n x (f v)

def IsSplitAt (w : HeightOneSpectrum (𝓞 E)) : Prop :=
  ∃ u : HeightOneSpectrum (𝓞 E), u ≠ w ∧
    u.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E))

def IsUnramU (π : Submodule ℂ (UA E n → ℂ)) (w : HeightOneSpectrum (𝓞 E)) : Prop :=
  ∃ φ ∈ π, φ ≠ 0 ∧ ∀ x ∈ locU n w, cLoc w x ∈ GlobalTheory.LFun.KGL w n → RU E n x φ = φ

def HasSatAt (π : Submodule ℂ (UA E n → ℂ)) (w : HeightOneSpectrum (𝓞 E))
    (s : w.adicCompletion E →+* w.adicCompletion E) (ϖ : w.adicCompletion E) (q : ℕ) (α : Fin (n / 2) → ℂˣ) : Prop :=
  ∃ b ∈ GlobalTheory.LFun.KGL w n, cT s b.val * b.val = antiJ (w.adicCompletion E) n ∧
    ∃ p : locU n w →* GU s n, (∀ x, (p x).val = b⁻¹ * cLoc w x.val * b) ∧
      ∃ σ : SmIrr (GU s n), IsCompAlong π (locU n w) p σ.ρ ∧ GlobalTheory.LFun.HasSatU ϖ q σ.ρ α

def HasWeightAt (π : Submodule ℂ (UA E n → ℂ)) (τ : E →+* ℂ) (lam : DomWeight n) : Prop :=
  IsCompAlong π (embU n τ) ((cEmb τ).comp (embU n τ).subtype) (GlobalTheory.Branching.sqRep ℂ n lam)

def infOfWeight (lam : DomWeight n) : Multiset ℂ :=
  Finset.univ.val.map fun k : Fin n => (lam.w k : ℂ) + (((n : ℂ) - 1) / 2 - (k : ℕ))

structure IsBaseChange (π : Submodule ℂ (UA E n → ℂ)) {c : ℕ} {N : Fin c → ℕ} (h : ∑ i, N i = n)
    (V : ∀ i, Submodule ℂ (Sm E (N i)))
    (σ : ∀ i (w : HeightOneSpectrum (𝓞 E)), SmIrr (GL (Fin (N i)) (w.adicCompletion E)))
    (m : Fin c → (E →+* ℂ) → Multiset ℂ) : Prop where
  pos : ∀ i, 0 < N i
  discrete : ∀ i, IsDiscrete (V i)
  csd : ∀ i, IsCsdGL (V i)
  loc : ∀ i w, IsLocCompGL (V i) w (σ i w)
  inf : ∀ i τ, HasInfCharGL (V i) τ (m i τ)

  unram : ∀ w, IsUnramU π w → GlobalTheory.LGrp.IsSpherical (locProd h w (σ · w)) (GlobalTheory.LFun.KGL w n)

  inert : ∀ (w : HeightOneSpectrum (𝓞 E)) (s : w.adicCompletion E →+* w.adicCompletion E) (ϖ : w.adicCompletion E)
    (q : ℕ), (∀ x : E, s (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x)) → IsUnramInv ϖ s q →
    ∀ α, HasSatAt π w s ϖ q α → GlobalTheory.LFun.HasSatGL w (locProd h w (σ · w)) (GlobalTheory.LGrp.bcParam n α)

  split : ∀ w, IsSplitAt w → IsCompAlong π (locU n w) ((cLoc w).comp (locU n w).subtype) (locProd h w (σ · w))

  weight : ∀ τ lam, HasWeightAt π τ lam → ∑ i, m i τ = infOfWeight lam

theorem conjAd_algebraMap (x : E) :
    conjAd E (algebraMap E (Ad E) x) = algebraMap E (Ad E) (IsCMField.complexConj E x) := by
  refine ad_ext ?_ ?_
  · rw [pInf_complexConj]
    change (infEq E).symm (infEq E _) = _
    rw [RingEquiv.symm_apply_apply]
    rfl
  · exact conjFin_algebraMap _ x

theorem isAutRepU_const : IsAutRepU (Submodule.span ℂ {(fun _ => 1 : UA E n → ℂ)}) := by
  have h0 : (fun _ => 1 : UA E n → ℂ) ≠ 0 := fun h => one_ne_zero (congrFun h 1)
  have hc : ∀ φ ∈ Submodule.span ℂ {(fun _ => 1 : UA E n → ℂ)}, ∀ x, RU E n x φ = φ := fun φ hφ x => by
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hφ
    rfl
  refine ⟨fun φ hφ => ⟨?_, ?_, ?_, ?_⟩, fun x φ hφ => by rwa [hc φ hφ], by simpa using h0,
    fun W hW _ => (nonzero_span_atom _ h0).le_iff.1 hW⟩
  · obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hφ
    exact continuous_const
  · obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hφ
    exact fun _ _ _ => rfl
  · rw [Set.eq_univ_of_forall (s := {k : finU E n | RU E n k φ = φ}) fun k => hc φ hφ k]
    exact isOpen_univ
  · refine FiniteDimensional.span_of_finite ℂ ((Set.finite_singleton φ).subset ?_)
    rintro _ ⟨k, rfl⟩
    exact hc φ hφ k

theorem isUnramU_const (w : HeightOneSpectrum (𝓞 E)) :
    IsUnramU (Submodule.span ℂ {(fun _ => 1 : UA E n → ℂ)}) w :=
  ⟨_, Submodule.mem_span_singleton_self _, fun h => one_ne_zero (congrFun h 1), fun _ _ _ => rfl⟩

theorem isDiscrete_of_cuspSub (P : CuspSub E a) (h : ∀ φ ∈ P.V, IsSqInt φ.1) : IsDiscrete P.V :=
  ⟨fun φ hφ => (P.cusp φ hφ).1, h, P.stable, P.ne_bot, P.irred⟩

theorem isCsdGL_const : IsCsdGL (Submodule.span ℂ {oneFn E a}) := by
  refine ⟨.refl _ _, fun o φ ψ h => ?_⟩
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 φ.2
  change ψ.1 = act o φ.1
  rw [h, ← hc, map_smul, map_smul, act_oneFn, act_oneFn]
  cases o <;> rfl

theorem isDiscrete_const (h : ∀ c : ℂ, IsSqInt fun _ : GA E a => c * 1) :
    IsDiscrete (Submodule.span ℂ {oneFn E a}) :=
  ⟨fun _ => isAutForm_const, fun φ hφ => by
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hφ
      exact h c,
    isStable_const, fun e => oneFn_ne_zero (Submodule.span_singleton_eq_bot.1 e),
    fun W hW _ => (nonzero_span_atom _ oneFn_ne_zero).le_iff.1 hW⟩

theorem cuspSub_iff (P : CuspSub E a) :
    (IsCsdGL P.V ↔ P.IsCsd) ∧ (∀ w σ, IsLocCompGL P.V w σ ↔ P.IsLocComp w σ) ∧
      ∀ τ m, HasInfCharGL P.V τ m ↔ P.HasInfChar τ m := by
  refine ⟨exists_congr fun T => ⟨fun h o φ => Subtype.ext (h o φ _ rfl), fun h o φ ψ e => ?_⟩,
    fun w σ => ⟨?_, ?_⟩, fun _ _ => Iff.rfl⟩
  · rw [show ψ = P.op (thetaOp o) φ from Subtype.ext e, h]
    rfl
  · rintro ⟨f, h0, h1, h2⟩
    exact ⟨f.codRestrict _ h1, fun e => h0 (LinearMap.ext fun v => congrArg Subtype.val (LinearMap.congr_fun e v)),
      fun g v => Subtype.ext (h2 g v)⟩
  · rintro ⟨f, h0, h1⟩
    exact ⟨P.V.subtype.comp f, fun e => h0 (LinearMap.ext fun v => Subtype.ext (LinearMap.congr_fun e v)),
      fun v => (f v).2, fun g v => congrArg Subtype.val (h1 g v)⟩

end CM

end GlobalTheory.UnitaryBC

namespace GlobalTheory.Published

open GlobalTheory.UnitaryBC

def BaseChangeDefiniteUnitary : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E],
    (∀ w : HeightOneSpectrum (𝓞 E), Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield E)) w.asIdeal) →
    ∀ n : ℕ, 1 ≤ n → ∀ π : Submodule ℂ (UA E n → ℂ), IsAutRepU π →
      ∃ (c : ℕ) (N : Fin c → ℕ) (h : ∑ i, N i = n) (V : ∀ i, Submodule ℂ (Sm E (N i)))
        (σ : ∀ i (w : HeightOneSpectrum (𝓞 E)), SmIrr (GL (Fin (N i)) (w.adicCompletion E)))
        (m : Fin c → (E →+* ℂ) → Multiset ℂ), UnitaryBC.IsBaseChange π h V σ m

end GlobalTheory.Published

end
