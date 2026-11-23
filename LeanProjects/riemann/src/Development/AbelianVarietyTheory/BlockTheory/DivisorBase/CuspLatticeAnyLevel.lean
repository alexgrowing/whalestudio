import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.CuspidalL2Subspace
import Formalism.LocalToGlobal.ProjectiveLattices.BaseEmbeddingInclusion
import Formalism.LocalToGlobal.IndefiniteReal.GramCEqTranspose
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.KaSmallNonpos

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.GoodBasisCentralIdempotents

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.IndefR.Arith
open scoped TensorProduct

section Abstract

variable {LL Ks : Type} [Field LL] [NumberField LL] [Field Ks] [NumberField Ks] [Algebra Ks LL]
variable {WL : Type} [AddCommGroup WL] [Module LL WL] [Module Ks WL] [IsScalarTower Ks LL WL]
  [Module (𝓞 LL) WL] [IsScalarTower (𝓞 LL) LL WL] [Module (𝓞 Ks) WL] [IsScalarTower (𝓞 Ks) Ks WL]
variable {W : (LL →+* ℂ) → Type} [∀ σ, NormedAddCommGroup (W σ)] [∀ σ, InnerProductSpace ℂ (W σ)]
variable {G : Type} [Group G] [Fintype G]

def IsGoodBasis (A : FormsL LL Ks WL W G) (J0 : Subgroup G) (lam0 : J0 →* LLˣ) (eC : G → LL) {d : ℕ}
    (b : Fin d → WL) : Prop :=
  LinearIndependent LL b ∧ Submodule.span LL (Set.range b) = A.Wgood J0 lam0 eC

def MjFull (A : FormsL LL Ks WL W G) (J0 : Subgroup G) (lam0 : J0 →* LLˣ) (eC : G → LL) : Prop :=
  FiniteDimensional LL (A.Wgood J0 lam0 eC) ∧
    ∀ (d : ℕ) (b : Fin d → WL), IsGoodBasis A J0 lam0 eC b → Submodule.IsLattice LL (A.Mcoord J0 lam0 eC b)

theorem exists_isGoodBasis (A : FormsL LL Ks WL W G) (J0 : Subgroup G) (lam0 : J0 →* LLˣ) (eC : G → LL)
    [FiniteDimensional LL (A.Wgood J0 lam0 eC)] :
    ∃ b : Fin (Module.finrank LL (A.Wgood J0 lam0 eC)) → WL, IsGoodBasis A J0 lam0 eC b := by
  let B := Module.finBasis LL (A.Wgood J0 lam0 eC)
  refine ⟨fun i => (A.Wgood J0 lam0 eC).subtype (B i), ?_, ?_⟩
  · exact B.linearIndependent.map' _ (Submodule.ker_subtype _)
  · show Submodule.span LL (Set.range ((A.Wgood J0 lam0 eC).subtype ∘ B)) = _
    rw [Set.range_comp, Submodule.span_image, B.span_eq, Submodule.map_top, Submodule.range_subtype]

omit [NumberField LL] in

def IsCentralIdem (eC : G → LL) : Prop :=
  (∀ g h, eC (h * g * h⁻¹) = eC g) ∧ ∀ g, ∑ h, eC h * eC (h⁻¹ * g) = eC g

end Abstract

variable {D : D7}

def IsKappa (D : D7) (j : ℕ) (w : WeightFamilies.Wt D j) : Prop :=
  w.n = D.R.nV ∧ ∀ τ, (∀ i, ((w.aP τ i : ℕ) : ℚ) = DV.aPlusQ D j τ i) ∧
    ∀ c : Fin (D.R.sigW j).2, ((w.aM τ (Fin.rev c) : ℕ) : ℚ) = DV.aMinusQ D j τ c

abbrev Cusp (T : Core D) (j : ℕ) (w : WeightFamilies.Wt D j) : Type := ↥(T.cuspA j (wtA w) w.n)

section Comparison₂

variable (T : Core D) (j : ℕ) (w : WeightFamilies.Wt D j)
variable {LL : Type} [Field LL] [NumberField LL] [Algebra T.Q.c.F LL]
variable {WL : Type} [AddCommGroup WL] [Module LL WL] [Module T.Q.c.F WL] [IsScalarTower T.Q.c.F LL WL]
variable {W : (LL →+* ℂ) → Type} [∀ σ, NormedAddCommGroup (W σ)] [∀ σ, InnerProductSpace ℂ (W σ)]
variable {G : Type} [Group G]

def CarriesCusp (A : FormsL LL T.Q.c.F WL W G) (ι : Cusp T j w →ₗ[T.Q.c.F] WL) : Prop :=
  IsBaseChange LL ι ∧ A.WK = LinearMap.range ι ∧
    ∀ (lp : HeightOneSpectrum (𝓞 T.Q.c.F)) (f : Cusp T j w) (h : ι f ∈ A.WK),
      (∀ y : A.Pt lp, A.nrm lp y ⟨ι f, h⟩ ≤ 1) ↔ ∀ y : T.PtM j lp, T.nrmM j lp y (f : T.R j) ≤ 1

end Comparison₂

def IsTypeSet (T : Core D) (Pg : Finset (Formalism.L2.DIV.Pl D.host.E)) : Prop :=
  ∀ PP : Formalism.L2.DIV.Pl D.host.E, PP ∈ Pg ↔
    ∃ k, (T.pb k).asIdeal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) ≤ PP.asIdeal

section Level

variable {E : Type} [Field E] [NumberField E] {Pg : Finset (Formalism.L2.DIV.Pl E)} {r : ℕ} {LL : Type} [Field LL]
  {G : Type} [Group G]

def levJ (φ : G ≃* Formalism.L2.DIV.G0 Pg r) (P : Formalism.L2.DIV.LevelP Pg r LL) : Subgroup G :=
  P.H.comap φ.toMonoidHom

def levLam (φ : G ≃* Formalism.L2.DIV.G0 Pg r) (P : Formalism.L2.DIV.LevelP Pg r LL) : levJ φ P →* LLˣ :=
  P.chi.comp (φ.toMonoidHom.subgroupComap P.H)

def IsDetChar (φ : G ≃* Formalism.L2.DIV.G0 Pg r) (chi : G →* LLˣ) : Prop :=
  ∃ χ : ∀ PP : ↥Pg, (Formalism.L2.DIV.kP PP.1)ˣ →* LLˣ,
    ∀ g, chi g = ∏ PP : ↥Pg, χ PP (Matrix.GeneralLinearGroup.det (φ g PP))

end Level

def MLat : Prop :=
  ∀ (D : D7) (T : Core D), LawsM T → ∀ j, InR D j → ∀ w : WeightFamilies.Wt D j, IsKappa D j w →
  ∀ (LL : Type) [Field LL] [NumberField LL] [Algebra T.Q.c.F LL]
    (WL : Type) [AddCommGroup WL] [Module LL WL] [Module T.Q.c.F WL] [IsScalarTower T.Q.c.F LL WL]
    [Module (𝓞 LL) WL] [IsScalarTower (𝓞 LL) LL WL] [Module (𝓞 T.Q.c.F) WL]
    [IsScalarTower (𝓞 T.Q.c.F) T.Q.c.F WL]
    (W : (LL →+* ℂ) → Type) [∀ σ, NormedAddCommGroup (W σ)] [∀ σ, InnerProductSpace ℂ (W σ)]
    (G : Type) [Group G] [Fintype G]
    (A : FormsL LL T.Q.c.F WL W G) (ι : Cusp T j w →ₗ[T.Q.c.F] WL), CarriesCusp T j w A ι →
  ∀ (Pg : Finset (Formalism.L2.DIV.Pl D.host.E)), IsTypeSet T Pg →
  ∀ (φ : G ≃* Formalism.L2.DIV.G0 Pg D.R.r), IsDetChar φ A.chi →
  ∀ (ψ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, AddChar (Formalism.L2.DIV.kP PP) LL), Formalism.L2.DIV.IsGenericPsi Pg ψ →
  ∀ eC : G → LL, IsCentralIdem eC →
    MjFull A (levJ φ (Formalism.L2.DIV.P0 Pg D.R.r ψ).conj) (levLam φ (Formalism.L2.DIV.P0 Pg D.R.r ψ).conj) eC

def MLatAnyLevel : Prop :=
  ∀ (D : D7) (T : Core D), LawsM T → ∀ j, InR D j → ∀ w : WeightFamilies.Wt D j, IsKappa D j w →
  ∀ (LL : Type) [Field LL] [NumberField LL] [Algebra T.Q.c.F LL]
    (WL : Type) [AddCommGroup WL] [Module LL WL] [Module T.Q.c.F WL] [IsScalarTower T.Q.c.F LL WL]
    [Module (𝓞 LL) WL] [IsScalarTower (𝓞 LL) LL WL] [Module (𝓞 T.Q.c.F) WL]
    [IsScalarTower (𝓞 T.Q.c.F) T.Q.c.F WL]
    (W : (LL →+* ℂ) → Type) [∀ σ, NormedAddCommGroup (W σ)] [∀ σ, InnerProductSpace ℂ (W σ)]
    (G : Type) [Group G] [Fintype G]
    (A : FormsL LL T.Q.c.F WL W G) (ι : Cusp T j w →ₗ[T.Q.c.F] WL), CarriesCusp T j w A ι →
  ∀ (J0 : Subgroup G) (lam0 : J0 →* LLˣ) (eC : G → LL), MjFull A J0 lam0 eC

theorem MLat.of_anyLevel (h : MLatAnyLevel) : MLat := by
  intro D T hT j hj w hw LL _ _ _ WL _ _ _ _ _ _ _ _ W _ _ G _ _ A ι hA Pg _ φ _ ψ _ eC _
  exact h D T hT j hj w hw LL WL W G A ι hA _ _ eC

theorem isKappa_kaWt (hK : DV.KapDef D) (hn : Even D.R.nV) {j : ℕ} (hj : InR D j) :
    IsKappa D j (DIV.Cons.kaWt D hK hn j) := by
  refine ⟨DIV.Cons.kaWt_n D hK hn j, fun τ => ⟨fun i => ?_, fun c => ?_⟩⟩
  · rw [← (hK j hj.1 hj.2 τ).1 i, ← DIV.Cons.kaWt_big D hK hn j hj.1 hj.2 τ i]; simp
  · have h1 := DIV.Cons.kaWt_small D hK hn j hj.1 hj.2 τ (Fin.rev c)
    have h2 := (hK j hj.1 hj.2 τ).2 c
    rw [Fin.rev_rev] at h1
    have h3 : (((DIV.Cons.kaWt D hK hn j).aM τ (Fin.rev c) : ℕ) : ℚ) = -(D.what₂.kaSmall j τ c : ℚ) := by
      exact_mod_cast h1
    rw [h3, h2, neg_neg]

example {LL G : Type} [Field LL] [Group G] [Fintype G] [DecidableEq G] :
    IsCentralIdem (fun g : G => if g = 1 then (1 : LL) else 0) := by
  refine ⟨fun g h => ?_, fun g => ?_⟩
  · simp [mul_inv_eq_one, mul_inv_eq_iff_eq_mul]
  · rw [Finset.sum_eq_single (1 : G)] <;> simp +contextual

theorem carriesCusp_formsLOf (T : Core D) (j : ℕ) (w : WeightFamilies.Wt D j)
    {LL : Type} [Field LL] [NumberField LL] [Algebra T.Q.c.F LL]
    {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
    (Comp : (LL →+* ℂ) → Type) (X : ∀ σ, Comp σ → ReciprocityTheory.ChartRestriction.G.FD.Data E r)
    (la : ∀ σ c, ReciprocityTheory.ChartRestriction.G.FD.Wt (X σ c).Ψ r)
    (rd : ∀ σ : LL →+* ℂ, Cusp T j w →ₛₗ[σ.comp (algebraMap T.Q.c.F LL)] FDSec (X σ))
    (V : (LL →+* ℂ) → _) (dict) (mu) (hL2) (hRd) (h0) (hz) (ha) (hs)
    {G : Type} [Group G] (ρC : G →* (Cusp T j w →ₗ[T.Q.c.F] Cusp T j w)) (chiC : G →* (T.Q.c.F)ˣ) :
    CarriesCusp T j w
      (formsLOf (D := D) Comp X la rd V dict mu hL2 hRd (T.PtM j) (fun lp y f => T.nrmM j lp y (f : T.R j))
        h0 hz ha hs ρC chiC) incl := by
  refine ⟨TensorProduct.isBaseChange _ _ LL, rfl, fun lp f h => ?_⟩
  have e : (LinearEquiv.ofInjective (incl (K := T.Q.c.F) (L := LL) (M := Cusp T j w)) incl_injective).symm
      ⟨incl f, h⟩ = f := by
    rw [LinearEquiv.symm_apply_eq]; rfl
  refine forall_congr' fun y => ?_
  show T.nrmM j lp y (((LinearEquiv.ofInjective (incl (K := T.Q.c.F) (L := LL) (M := Cusp T j w))
    incl_injective).symm ⟨incl f, h⟩ : Cusp T j w) : T.R j) ≤ 1 ↔ _
  rw [e]

theorem nrmOf_nonneg {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K)) (v : EReal) :
    0 ≤ nrmOf la v := by
  unfold nrmOf; split_ifs
  · exact le_rfl
  · exact Real.rpow_nonneg (Nat.cast_nonneg _) _

theorem nrmOf_anti {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K)) {u v : EReal} (hu : u ≠ ⊥)
    (h : u ≤ v) : nrmOf la v ≤ nrmOf la u := by
  by_cases hv : v = ⊤
  · subst hv; simpa [nrmOf] using nrmOf_nonneg la u
  have hu' : u ≠ ⊤ := fun e => hv (top_le_iff.mp (e ▸ h))
  unfold nrmOf
  rw [if_neg hv, if_neg hu']
  exact Real.rpow_le_rpow_of_exponent_le (one_lt_absNorm_real la).le (neg_le_neg (EReal.toReal_le_toReal h hu hv))

theorem nrmM_laws (T : Core D) (j : ℕ) (lp : HeightOneSpectrum (𝓞 T.Q.c.F)) (y : T.PtM j lp) :
    (∀ f, 0 ≤ T.nrmM j lp y f) ∧ T.nrmM j lp y 0 = 0 ∧
      (∀ f g, T.nrmM j lp y (f + g) ≤ max (T.nrmM j lp y f) (T.nrmM j lp y g)) ∧
      ∀ (x : T.Q.c.F) f, T.nrmM j lp y (x • f) = FinitePlace.mk lp x * T.nrmM j lp y f := by
  have hv := isVal_valSet lp y.1 y.2
  have hz : T.nrmM j lp y 0 = 0 := by simp [Core.nrmM, hv.zero, nrmOf]
  refine ⟨fun f => nrmOf_nonneg _ _, hz, fun f g => ?_, fun x f => ?_⟩
  · rcases le_total (y.1 f) (y.1 g) with h | h
    · exact (nrmOf_anti lp (hv.ne_bot f) ((min_eq_left h).symm.le.trans (hv.add f g))).trans (le_max_left _ _)
    · exact (nrmOf_anti lp (hv.ne_bot g) ((min_eq_right h).symm.le.trans (hv.add f g))).trans (le_max_right _ _)
  · by_cases hx : x = 0
    · subst hx; rw [zero_smul, hz]; simp
    · unfold Core.nrmM
      rw [hv.smul x f hx]
      exact nrmOf_smul lp hx (hv.ne_bot f)

end GlobalTheory.IndefiniteRowSideFullHecke.GoodBasisCentralIdempotents
