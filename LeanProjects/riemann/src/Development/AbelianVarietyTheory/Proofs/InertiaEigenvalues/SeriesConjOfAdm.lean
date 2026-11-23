import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DetCharacterMemPrincipalCongruenceFixedVectors
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.PadicIntGLSmulMemPrincipalCongruenceFixed
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TeichmullerRoots
import Development.AbelianVarietyTheory.Counterexamples.DegenerateExamples.NotAdmissibleWithAmbientTop
import Formalism.SharpRestriction.Divisibility.PrimeDegreeVariant

noncomputable section

namespace GlobalTheory.GoodTypes

open Polynomial GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys GlobalTheory.TypeLeaf Formalism.BasicNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders Formalism.MainNotions.PrimeDegreeVariant
open scoped Classical

section Local

variable {g : ℕ} [Fact g.Prime] {n : ℕ} {G V U : Type} [Group G] [AddCommGroup V] [Module ℂ V]
  [AddCommGroup U] [Module ℂ U]

def ConjIn (ρ : Representation ℂ G V) (W : Submodule ℂ V) (j : Gn g n →* G)
    (π : Representation ℂ (GL (Fin n) ℚ_[g]) U) : Prop :=
  ∀ y ∈ W, y ≠ 0 → ∃ Λ : V →ₛₗ[starRingEnd ℂ] U, Λ y ≠ 0 ∧
    ∀ z ∈ W, Λ z ∈ fixK1 π ∧ ∀ h, Λ (ρ (j h) z) = π (lift g n h) (Λ z)

def typeSpan {ι T : Type} (ρ : Representation ℂ G V) (b : ι → V) (ty : ι → T) (π : T) : Submodule ℂ V :=
  Submodule.span ℂ {z | ∃ (x : G) (σ : ι), ty σ = π ∧ z = ρ x (b σ)}

theorem ConjIn.act_ne {ρ : Representation ℂ G V} {W : Submodule ℂ V} {j : Gn g n →* G}
    {π : Representation ℂ (GL (Fin n) ℚ_[g]) U} (h : ConjIn ρ W j π) (a a' : MonoidAlgebra ℂ (Gn g n))
    (ha : ∀ x, starRingEnd ℂ (a.coeff x) = a'.coeff x) {y : V} (hy : y ∈ W) (h0 : y ≠ 0)
    (hfix : ∑ x, a.coeff x • ρ (j x) y = y) : ∃ u ∈ fixK1 π, actK π a' u ≠ 0 := by
  obtain ⟨Λ, h1, h2⟩ := h y hy h0
  refine ⟨Λ y, (h2 y hy).1, ?_⟩
  have : actK π a' (Λ y) = Λ y := by
    conv_rhs => rw [← hfix]
    rw [map_sum, actK, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [LinearMap.smul_apply, map_smulₛₗ, ha, (h2 y hy).2]
  rwa [this]

theorem eq_of_teich (τ : Formalism.CyclotomicNorms.Fbar g →* ℂ) (hτ : Function.Injective τ) {f f' : (ZMod g)[X]} (hf : f.Monic)
    (hf' : f'.Monic) (h : ((Formalism.CyclotomicNorms.rootsBar f).map fun x => X - C (τ x)).prod =
      ((Formalism.CyclotomicNorms.rootsBar f').map fun x => X - C (τ x)).prod) : f = f' := by
  have h3 := congrArg Polynomial.roots h
  have e : ∀ m : Multiset (Formalism.CyclotomicNorms.Fbar g), ((m.map fun x => X - C (τ x)).prod).roots = m.map τ := fun m => by
    rw [← roots_multiset_prod_X_sub_C (m.map τ), Multiset.map_map]; rfl
  rw [e, e] at h3
  apply Polynomial.map_injective (algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g)) (RingHom.injective _)
  rw [(IsAlgClosed.splits _).eq_prod_roots_of_monic (hf.map _),
    (IsAlgClosed.splits (f'.map _)).eq_prod_roots_of_monic (hf'.map _)]
  exact congrArg (fun m => (Multiset.map (fun x => X - C x) m).prod) (Multiset.map_injective hτ h3)

end Local

local instance factPrime (D : D7) (k : Fin 2) : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩

local instance neZeroPrime (D : D7) (k : Fin 2) : NeZero (D.host.g k) := ⟨(D.host.g_prime k).ne_zero⟩

def facHom (D : D7) (k : Fin 2) (v : D.nd.PlG k) : Gn (D.host.g k) D.R.r →* G0g D.nd :=
  MonoidHom.mulSingle (fun kv : (Σ k : Fin 2, D.nd.PlG k) => GL (Fin D.R.r) (ZMod (D.host.g kv.1))) ⟨k, v⟩

abbrev LocRep (D : D7) (k : Fin 2) : Type 1 := Rep.{0} ℂ (GL (Fin D.R.r) ℚ_[D.host.g k])

abbrev Corr (D : D7) : Type 1 := ∀ (k : Fin 2) (v : D.nd.PlG k), LocRep D k → D.naut.LP (D.naut.plGw k v)

abbrev Comp (D : D7) : Type 1 := D.what₂.FT → ∀ k : Fin 2, D.nd.PlG k → LocRep D k

def SeriesTame (D : D7) (rc : Corr D) : Prop :=
  ∀ (k : Fin 2) (v : D.nd.PlG k) (π : LocRep D k), IsIrrRep π.ρ → GlobalTheory.SplitWeil.IsSmoothRep π.ρ →
    D.naut.lpDim (rc k v π) = D.R.r ∧
    ∀ f, (∃ u ∈ fixK1 π.ρ, actK π.ρ (D.ntypes.eSer k f) u ≠ 0) →
      D.naut.inePol (rc k v π) (D.ntypes.tg k v) =
        ((Formalism.CyclotomicNorms.rootsBar f).map fun x => X - C (D.ntypes.teichC k x)).prod

def ParamTie (D : D7) (i : D.nd.Loc) (rc : Corr D) (cp : Comp D) : Prop :=
  ∀ (σ : D.what₂.FT) (k : Fin 2) (v : D.nd.PlG k), IsIrrRep (cp σ k v).ρ ∧ GlobalTheory.SplitWeil.IsSmoothRep (cp σ k v).ρ ∧
    D.naut.locW i σ (D.naut.plGw k v) = rc k v (cp σ k v)

def SeriesConj (D : D7) : Prop :=
  ∀ (k : Fin 2) (f : (ZMod (D.host.g k))[X]), IsLabel D k f →
    (D.ntypes.eSer k f).coeff.mapRange (starRingAut : ℂ ≃+* ℂ) (map_zero _) =
      (D.ntypes.eSer k (labAct D starRingAut k f)).coeff

theorem labAct_conj (D : D7) (k : Fin 2) {f : (ZMod (D.host.g k))[X]} (hf : IsLabel D k f) :
    labAct D starRingAut k f = dualLab D k f := by
  obtain ⟨h1, h2⟩ := GlobalTheory.Compare.TeichmullerRoots.dual_spec hf.1 hf.2.2
  refine GlobalTheory.Compare.TeichmullerRoots.labAct_eq D k _ (-1) (fun ζ hζ => ?_) hf h1 h2
  have hn : ‖ζ‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hζ
    (GlobalTheory.IndefiniteRowSideFullHecke.FactorSeriesSupport.rootExp_ne_zero D.R.r _ (D.host.g_prime k).two_le)
  rw [zpow_neg_one, Complex.inv_eq_conj hn]
  rfl

theorem act_atPlace (D : D7) {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (G0g D.nd) V)
    (k : Fin 2) (v : D.nd.PlG k) (a : MonoidAlgebra ℂ (Gn (D.host.g k) D.R.r)) (y : V) :
    ρ.asAlgebraHom (atPlace D k v a) y = ∑ x, a.coeff x • ρ (facHom D k v x) y := by
  rw [GlobalTheory.SeriesSupportTest.atPlace_eq]
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp [ha, hb, add_smul, Finset.sum_add_distrib]
  | single h c =>
    have : GlobalTheory.SeriesSupportTest.plHom D k v (MonoidAlgebra.single h c) =
        MonoidAlgebra.single (facHom D k v h) c := MonoidAlgebra.mapDomain_single
    rw [this, Representation.asAlgebraHom_single]
    simp [Finsupp.single_apply]

theorem exists_good (D : D7) {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (G0g D.nd) V) {x : V}
    (hx : x ≠ 0) (he : ρ.asAlgebraHom D.ntypes.e0 x = x) :
    ∃ (t : Tup2 D) (a : MonoidAlgebra ℂ (G0g D.nd)), D.ntypes.goodTuple t ∧ ρ.asAlgebraHom a x ≠ 0 ∧
      ∀ k v, ρ.asAlgebraHom (atPlace D k v (D.ntypes.eSer k (t k v))) (ρ.asAlgebraHom a x) = ρ.asAlgebraHom a x := by
  rw [Ten.e0_eq, Ten.eGood, map_sum, LinearMap.sum_apply] at he
  obtain ⟨p, -, hp⟩ := Finset.exists_ne_zero_of_sum_ne_zero (he.trans_ne hx)
  by_cases hg : Ten.goodVec D p
  · rw [if_pos hg] at hp
    refine ⟨_, _, hg, hp, fun k v => ?_⟩
    rw [← Module.End.mul_apply, ← map_mul,
      ← Subalgebra.mem_center_iff.1 (GlobalTheory.SeriesSupportTest.atPlace_central D k v _ (D.ntypes.eSer_central k _)),
      Ten.atPlace_eq, Ten.tens_mul_plc]
    congr 3
    exact Function.update_eq_self_iff.2 (D.ntypes.eSer_idem _ _)
  · rw [if_neg hg] at hp
    simp at hp

variable {D : D7} {X : BaseLevelRowSide D}

def TypeTie (Y : Prov D X) (cp : Comp D) {EE : Type} [NormedAddCommGroup EE] [InnerProductSpace ℂ EE]
    [FiniteDimensional ℂ EE] (S : RowSide D EE) (P : Pair D.what₂.LL (G0g D.nd))
    (j : S.RR.V →ₗ[D.what₂.LL] Y.sK.RR.V) {ι : Type} (b : ι → EE) (ty : ι → D.what₂.FT) : Prop :=
  ∃ (aE : EE →ₗ[ℂ] Y.EEK) (aA : ∀ μ, S.Amb μ →ₗ[ℂ] Y.sK.Amb μ), IsLevelIn Y S P j aE aA ∧
    ∀ σ k v, ConjIn Y.actEE (typeSpan Y.actEE (fun s => aE (b s)) ty σ) (facHom D k v) (cp σ k v).ρ

end GlobalTheory.GoodTypes
