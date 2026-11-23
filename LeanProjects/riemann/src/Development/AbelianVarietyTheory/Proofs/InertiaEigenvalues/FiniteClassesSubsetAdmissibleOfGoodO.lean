import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ResBound
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteLengthOfSmulEqZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteQuotientPow

noncomputable section

open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct
open Formalism.MainNotions.N (twistRep coefRep)
open Formalism.GaloisCohomology (scalRep)
open ReciprocityTheory.Def (Z1 H1)
open scoped Pointwise

namespace GlobalTheory.FiniteAdm

section Alg

variable {O G : Type} [CommRing O] [Group G]

theorem sameSS_red_ext {A M R : Type} [AddCommGroup A] [Module O A] [AddCommGroup M] [Module O M]
    [AddCommGroup R] [Module O R] (α : Representation O G A) (π : Representation O G M) (χ : G →* Oˣ)
    (e : M ≃ₗ[O] A × O) (b : G → A)
    (he : ∀ g x, e (π g x) = (α g (e x).1 + ((χ g : O) * (e x).2) • b g, (χ g : O) * (e x).2))
    (c : O) (β : Representation O G R) (h : SameSS (modRep α c) β)
    (hc : IsFiniteLength O (QuotSMulTop c O)) :
    SameSS (modRep π c) (β.prod (modRep (scalRep O χ) c)) := by
  let f : A →ₗ[O] M := e.symm.toLinearMap ∘ₗ LinearMap.inl O A O
  let p : M →ₗ[O] O := LinearMap.snd O A O ∘ₗ e.toLinearMap
  let r : M →ₗ[O] A := LinearMap.fst O A O ∘ₗ e.toLinearMap
  have hp : Function.Surjective p := Prod.snd_surjective.comp e.surjective
  have hex : Function.Exact f p := by
    intro x
    constructor
    · intro hx
      refine ⟨(e x).1, e.injective ?_⟩
      have hx' : (e x).2 = 0 := hx
      simp [f, Prod.ext_iff, hx']
    · rintro ⟨y, rfl⟩
      simp [f, p]
  refine SameSS.of_exact_of_exact (α := modRep α c) (γ := modRep (scalRep O χ) c)
    (f := QuotSMulTop.map c f) (p := QuotSMulTop.map c p) ?_ ?_ ?_ (QuotSMulTop.map_surjective c hp)
    (QuotSMulTop.map_exact c hex hp) (f' := LinearMap.inl O _ _) (p' := LinearMap.snd O _ _)
    (fun g x => by simp) (fun g x => by simp) LinearMap.inl_injective LinearMap.snd_surjective .inl_snd h
    (SameSS.refl _ hc)
  · intro g x
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    change Submodule.Quotient.mk (f (α g x)) = Submodule.Quotient.mk (π g (f x))
    congr 1
    apply e.injective
    rw [he]
    simp [f]
  · intro g x
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    change Submodule.Quotient.mk (p (π g x)) = Submodule.Quotient.mk ((χ g : O) • (p x))
    congr 1
    change (e (π g x)).2 = _
    rw [he]
    rfl
  · refine Function.LeftInverse.injective (g := QuotSMulTop.map c r) fun x => ?_
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    change Submodule.Quotient.mk (r (f x)) = Submodule.Quotient.mk x
    simp [r, f]

def lastEquiv (O A B : Type) [CommRing O] [AddCommGroup A] [Module O A] [AddCommGroup B] [Module O B] (s : ℕ) :
    (A × (Fin (s + 1) → B)) ≃ₗ[O] ((A × (Fin s → B)) × B) where
  toFun x := ((x.1, fun i => x.2 i.castSucc), x.2 (Fin.last s))
  invFun y := (y.1.1, Fin.snoc (α := fun _ => B) y.1.2 y.2)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv x := Prod.ext rfl (Fin.snoc_init_self x.2)
  right_inv y := by simp

theorem exists_pow_smul_eq_zero [IsLocalRing O] {c : O} (hc : ¬ IsUnit c) (X : Type) [AddCommGroup X]
    [Module O X] [Finite X] : ∃ a : ℕ, 1 ≤ a ∧ ∀ x : X, c ^ a • x = 0 := by
  obtain ⟨m, n, hmn, h⟩ := Finite.exists_ne_map_eq_of_infinite (fun n : ℕ => fun x : X => c ^ n • x)
  wlog hlt : m < n generalizing m n
  · exact this n m hmn.symm h.symm (by omega)
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hlt
  have hu : IsUnit (1 - c ^ (k + 1)) :=
    IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _ fun h => hc ((isUnit_pow_iff (by omega)).mp h)
  refine ⟨m + 1, by omega, fun x => ?_⟩
  have h1 : c ^ m • x = c ^ (m + k + 1) • x := congrFun h x
  have h2 : (1 - c ^ (k + 1)) • c ^ m • x = 0 := by
    rw [sub_smul, one_smul, smul_smul, ← pow_add, h1, sub_eq_zero]
    congr 2
    omega
  rw [pow_succ', mul_smul, (hu.smul_eq_zero).mp h2, smul_zero]

end Alg

section Top

variable {LL O V : Type} [Field LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL] [IsTopologicalRing LL]
  [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V] [TopologicalSpace V] [IsModuleTopology LL V]

theorem isOpen_of_fg (hO : IsOpen (Set.range (algebraMap O LL))) (T : Submodule O V) (hT : T.FG)
    (hs : Submodule.span LL (T : Set V) = ⊤) : IsOpen (T : Set V) := by
  obtain ⟨n, v, rfl⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hT
  rw [Submodule.span_span_of_tower] at hs
  let f : (Fin n → LL) →ₗ[LL] V := Fintype.linearCombination LL v
  have hf : Function.Surjective f := by
    rw [← LinearMap.range_eq_top, Fintype.range_linearCombination, hs]
  have ho : IsOpenMap f := (IsModuleTopology.isOpenQuotientMap_of_surjective hf).isOpenMap
  have h : (Submodule.span O (Set.range v) : Set V) =
      f '' Set.pi Set.univ (fun _ => Set.range (algebraMap O LL)) := by
    ext x
    rw [SetLike.mem_coe, Submodule.mem_span_range_iff_exists_fun]
    constructor
    · rintro ⟨c, rfl⟩
      exact ⟨fun i => algebraMap O LL (c i), fun i _ => ⟨_, rfl⟩, by simp [f, Fintype.linearCombination_apply]⟩
    · rintro ⟨y, hy, rfl⟩
      choose c hc using fun i => hy i (Set.mem_univ i)
      exact ⟨c, by simp [f, Fintype.linearCombination_apply, ← hc]⟩
  rw [h]
  exact ho _ (isOpen_set_pi Set.finite_univ fun _ _ => hO)

theorem isLocallyConstant_comp {G N : Type} [TopologicalSpace G] [AddCommGroup N] [Module O N]
    (hO : IsOpen (Set.range (algebraMap O LL))) (T : Submodule O V) (hT : T.FG)
    (hs : Submodule.span LL (T : Set V) = ⊤) {c : O} (hc : algebraMap O LL c ≠ 0) (q : ↥T →ₗ[O] N)
    (hN : ∀ y : N, c • y = 0) (z : G → ↥T) (hz : Continuous fun g => (z g : V)) :
    IsLocallyConstant fun g => q (z g) := by
  haveI : ContinuousSMul LL V := IsModuleTopology.toContinuousSMul LL V
  haveI : IsTopologicalAddGroup V := IsModuleTopology.topologicalAddGroup LL V
  have hT' := isOpen_of_fg hO T hT hs
  rw [IsLocallyConstant.iff_exists_open]
  intro g
  refine ⟨(fun h => (algebraMap O LL c)⁻¹ • ((z h : V) - z g)) ⁻¹' (T : Set V),
    hT'.preimage ((hz.sub continuous_const).const_smul _), by simp, fun h hh => ?_⟩
  have h1 : z h - z g = c • (⟨_, hh⟩ : ↥T) := by
    apply Subtype.ext
    change (z h : V) - z g = c • (algebraMap O LL c)⁻¹ • ((z h : V) - z g)
    rw [← algebraMap_smul LL c, smul_inv_smul₀ hc]
  rw [← sub_eq_zero, ← map_sub, h1, map_smul, hN]

end Top

section Lat

variable {G : Type} [Group G] [TopologicalSpace G] {Qp LL O : Type} [Field Qp] [Field LL] [Algebra Qp LL]
  [CommRing O] [Algebra O LL] [TopologicalSpace LL] [IsTopologicalRing LL]

def extEquiv {V : Type} [AddCommGroup V] [Module O V] (hinj : Function.Injective (algebraMap O LL))
    (T : Submodule O V) : (↥T × O) ≃ₗ[O] ↥(T.prod (LinearMap.range (Algebra.linearMap O LL))) :=
  LinearEquiv.ofBijective
    (LinearMap.codRestrict (T.prod (LinearMap.range (Algebra.linearMap O LL)))
      (T.subtype.prodMap (Algebra.linearMap O LL)) fun x => Submodule.mem_prod.mpr ⟨x.1.2, x.2, rfl⟩)
    ⟨fun x y h => by
      have h' := congrArg Subtype.val h
      exact Prod.ext (Subtype.ext (congrArg Prod.fst h')) (hinj (congrArg Prod.snd h')),
    by
      rintro ⟨⟨v, y⟩, hv, a, ha⟩
      exact ⟨(⟨v, hv⟩, a), Subtype.ext (Prod.ext rfl ha)⟩⟩

def extLat (hinj : Function.Injective (algebraMap O LL)) (T : LocLat G Qp LL O) (z : ↥(latticeCocycles T.L)) :
    LocLat G Qp LL O where
  V := T.V × LL
  ρ := GlobalTheory.IndefiniteRowSideFullHecke.CrystallineExtensions.extRep T.ρ ⟨z, z.2.1⟩
  cont := fun x => by
    haveI : ContinuousSMul LL T.V := IsModuleTopology.toContinuousSMul LL T.V
    change Continuous fun g => (T.ρ g x.1 + x.2 • (z : G → T.V) g, x.2)
    exact ((T.cont x.1).add (z.2.1.1.const_smul x.2)).prodMk continuous_const
  L :=
    { T := T.L.T.prod (LinearMap.range (Algebra.linearMap O LL))
      stable := by
        rintro g ⟨v, _⟩ ⟨hv, a, rfl⟩
        refine ⟨?_, a, rfl⟩
        change T.ρ g v + algebraMap O LL a • (z : G → T.V) g ∈ T.L.T
        rw [algebraMap_smul]
        exact T.L.T.add_mem (T.L.stable g v hv) (T.L.T.smul_mem _ (z.2.2 g (Set.mem_univ g)))
      fg := T.L.fg.prod (by
        rw [← Submodule.map_top]
        exact Module.Finite.fg_top.map _)
      free := by
        haveI := T.L.free
        exact Module.Free.of_equiv (extEquiv hinj T.L.T)
      span := by
        rw [eq_top_iff]
        rintro ⟨v, y⟩ -
        have h1 : ∀ v ∈ Submodule.span LL (T.L.T : Set T.V), ((v, 0) : T.V × LL) ∈ Submodule.span LL
            ((T.L.T.prod (LinearMap.range (Algebra.linearMap O LL)) : Submodule O (T.V × LL)) : Set (T.V × LL)) := by
          intro v hv
          induction hv using Submodule.span_induction with
          | mem w hw => exact Submodule.subset_span ⟨hw, Submodule.zero_mem _⟩
          | zero => exact Submodule.zero_mem _
          | add u w _ _ hu hw => simpa using Submodule.add_mem _ hu hw
          | smul c u _ hu => simpa using Submodule.smul_mem _ c hu
        have h2 : ((0, 1) : T.V × LL) ∈ Submodule.span LL
            ((T.L.T.prod (LinearMap.range (Algebra.linearMap O LL)) : Submodule O (T.V × LL)) : Set (T.V × LL)) :=
          Submodule.subset_span ⟨Submodule.zero_mem _, 1, by simp⟩
        have h3 := Submodule.add_mem _ (h1 v (by rw [T.L.span]; trivial)) (Submodule.smul_mem _ y h2)
        simpa using h3 }

end Lat

section Per

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] [IsTopologicalRing LL] {n : ℕ}
    {emb : ZMod n → (K₀ →ₐ[Qp] LL)}

variable (PD emb O) in

abbrev TwistCrys : Prop :=
  ∀ (T : LocLat G Qp LL O) (U : ZMod n → Multiset ℤ) (θ : G →* Oˣ) (a : ZMod n → ℤ),
    CrysWith PD emb T.ρ U → IsCrysChar PD emb θ a →
    CrysWith PD emb (twistRep T.ρ (chiLL LL θ)) (fun i => (U i).map (· + a i)) ∧
    IsCrysChar PD emb θ⁻¹ (fun i => -a i)

theorem exists_ext (hinj : Function.Injective (algebraMap O LL)) (hext : GlobalTheory.IndefiniteRowSideFullHecke.CrystallineExtensions.ExtCrysAt PD emb)
    (htw : TwistCrys PD O emb) (T : LocLat G Qp LL O) {U : ZMod n → Multiset ℤ} (hT : CrysWith PD emb T.ρ U)
    {χ : G →* Oˣ} {a : ZMod n → ℤ} (hχ : IsCrysChar PD emb χ a) (z : ↥(latticeCocycles (twLattice T.L χ⁻¹)))
    (hz : (z : G → T.V) ∈ finiteCocycles PD (twistRep T.ρ (chiLL LL χ⁻¹))) :
    ∃ T' : LocLat G Qp LL O, CrysWith PD emb T'.ρ (fun i => U i + {a i}) ∧
      ∃ e : ↥T'.L.T ≃ₗ[O] (↥T.L.T × O), ∀ g x, e (latRep T'.L g x) =
        (latRep T.L g (e x).1 + ((χ g : O) * (e x).2) • (evT (twLattice T.L χ⁻¹) g z : ↥T.L.T),
          (χ g : O) * (e x).2) := by
  have hχ' := (htw T U χ a hT hχ).2
  have h1 := (htw T U χ⁻¹ _ hT hχ').1
  let T₁ := twLat T χ⁻¹ hχ'.1
  let T₂ := extLat hinj T₁ z
  let z' : ↥(continuousCocycles (twistRep T.ρ (chiLL LL χ⁻¹))) := ⟨z.1, z.2.1⟩
  have h0 := GlobalTheory.IndefiniteRowSideFullHecke.CrystallineExtensions.extRep_isExt (twistRep T.ρ (chiLL LL χ⁻¹)) z'
  have hcont : ∀ x : T.V, Continuous fun g => twistRep T.ρ (chiLL LL χ⁻¹) g x := T₁.cont
  have h2 := hext T.V (twistRep T.ρ (chiLL LL χ⁻¹)) hcont h1.1 (T.V × LL) _ _ _ h0.1 z' h0.2
  have h3 := h2.1.mpr ((GlobalTheory.IndefiniteRowSideFullHecke.CrystallineExtensions.mk_mem_H1fSub PD _ z').mpr hz)
  have h4 := (htw T₂ _ χ a ⟨h3, fun i => h2.2 h3 i _ (h1.2 i)⟩ hχ).1
  refine ⟨twLat T₂ χ hχ.1, ?_, (extEquiv hinj T.L.T).symm, fun g x => ?_⟩
  · have h5 : (fun i => U i + {a i}) = fun i => ((U i).map (· + -a i) + {0}).map (· + a i) := by
      funext i
      simp [Multiset.map_map]
    rw [h5]
    exact h4
  · obtain ⟨⟨v, y⟩, rfl⟩ := (extEquiv hinj T.L.T).surjective x
    refine (extEquiv hinj T.L.T).symm_apply_eq.mpr ?_
    erw [(extEquiv hinj T.L.T).symm_apply_apply]
    apply Subtype.ext
    change algebraMap O LL (χ g) • ((algebraMap O LL (χ⁻¹ g) • T.ρ g v + algebraMap O LL y • (z : G → T.V) g,
      algebraMap O LL y) : T.V × LL) = (T.ρ g v + ((χ g : O) * y) • (z : G → T.V) g, algebraMap O LL (χ g * y))
    simp only [Prod.smul_mk, smul_add, algebraMap_smul, smul_smul, map_mul, Algebra.smul_def]
    simp

theorem isCrysChar_chi (hinj : Function.Injective (algebraMap O LL)) (htw : TwistCrys PD O emb)
    (Γ : GalData G Qp LL O) {w : ZMod n → ℤ} (h1 : IsCrysChar PD emb Γ.χ₁ w)
    (hε : IsCrysChar PD emb Γ.ε (fun _ => -1)) (s : ℕ) :
    IsCrysChar PD emb (Γ.chi (s + 1)) (fun i => w i + s) := by
  induction s with
  | zero => simpa using h1
  | succ s ih =>
    have h2 := (htw (charLat Qp hinj _ ih.1) _ _ _ ih.2 hε).2
    have h3 := (htw (charLat Qp hinj _ ih.1) _ _ _ ih.2 h2).1
    rw [GalData.chi_succ]
    refine ⟨(ih.1.mul h2.1).congr fun g => by simp, ?_⟩
    have h4 : charRep (chiLL LL (Γ.chi (s + 1) * Γ.ε⁻¹)) =
        twistRep (charRep (chiLL LL (Γ.chi (s + 1)))) (chiLL LL Γ.ε⁻¹) := by
      ext g
      simp [charRep, twistRep, mul_comm, Algebra.smul_def]
    have h5 : (fun i => ({w i + ((s + 1 : ℕ) : ℤ)} : Multiset ℤ)) =
        fun i => ({w i + (s : ℤ)} : Multiset ℤ).map (· + - -1) := by
      funext i
      simp [add_assoc]
    rw [h4, h5]
    exact h3

variable [IsDomain O] [IsDiscreteValuationRing O] [IsFractionRing O LL]

theorem admissible_of_surjective {Γ : GalData G Qp LL O} {t : ℕ} {Ut : ZMod n → Multiset ℤ}
    {T : LocLat G Qp LL O} (hT : Full PD emb Γ t Ut T) {M : Type} [AddCommGroup M] [Module O M] [Finite M]
    (π : Representation O G M) (p : ↥T.L.T →ₗ[O] M) (hp : Function.Surjective p)
    (hg : ∀ g x, p (latRep T.L g x) = π g (p x)) {c : O} (hc : c ≠ 0) (hM : ∀ y : M, c • y = 0) :
    Admissible PD emb Γ t Ut π := by
  haveI := T.L.free
  haveI : Module.Finite O ↥T.L.T := Module.Finite.iff_fg.mpr T.L.fg
  let L₂ : Lattice (O := O) T.ρ :=
    { T := (LinearMap.ker p).map T.L.T.subtype
      stable := by
        rintro g _ ⟨x, hx, rfl⟩
        refine ⟨latRep T.L g x, ?_, rfl⟩
        rw [SetLike.mem_coe, LinearMap.mem_ker] at hx ⊢
        rw [hg, hx, map_zero]
      fg := (IsNoetherian.noetherian _).map _
      free := Module.Free.of_equiv (Submodule.equivMapOfInjective _ T.L.T.subtype_injective (LinearMap.ker p))
      span := by
        rw [eq_top_iff, ← T.L.span, Submodule.span_le]
        intro x hx
        have h0 : algebraMap O LL c ≠ 0 := by simpa using hc
        refine (Submodule.smul_mem_iff _ h0).mp (Submodule.subset_span ⟨c • ⟨x, hx⟩, ?_, ?_⟩)
        · rw [SetLike.mem_coe, LinearMap.mem_ker, map_smul, hM]
        · simp }
  refine ⟨inferInstance, 1, T, hT.sumFull, L₂, p, Submodule.map_subtype_le _ _, hp, hg, fun x => ⟨fun h => ⟨x, h, rfl⟩, ?_⟩⟩
  rintro ⟨y, hy, h⟩
  rwa [← Subtype.ext h]

theorem exists_step (hext : GlobalTheory.IndefiniteRowSideFullHecke.CrystallineExtensions.ExtCrysAt PD emb) (htw : TwistCrys PD O emb)
    (Γ : GalData G Qp LL O) (hlam : Γ.lam ≠ 0) {U : ZMod n → Multiset ℤ} {w : ZMod n → ℤ} {s : ℕ}
    (T : LocLat G Qp LL O) (hT : CrysWith PD emb T.ρ (fun i => U i + block (w i) s))
    (hss : SameSS (modRep (latRep T.L) Γ.lam) (Γ.refRep s)) {χ : G →* Oˣ} (hχs : χ = Γ.chi (s + 1))
    (hχ : IsCrysChar PD emb χ (fun i => w i + s)) (z : ↥(latticeCocycles (twLattice T.L χ⁻¹)))
    (hz : (z : G → T.V) ∈ finiteCocycles PD (twistRep T.ρ (chiLL LL χ⁻¹))) :
    ∃ T' : LocLat G Qp LL O, CrysWith PD emb T'.ρ (fun i => U i + block (w i) (s + 1 : ℕ)) ∧
      SameSS (modRep (latRep T'.L) Γ.lam) (Γ.refRep (s + 1)) ∧
      ∃ e : ↥T'.L.T ≃ₗ[O] (↥T.L.T × O), ∀ g x, e (latRep T'.L g x) =
        (latRep T.L g (e x).1 + ((χ g : O) * (e x).2) • (evT (twLattice T.L χ⁻¹) g z : ↥T.L.T),
          (χ g : O) * (e x).2) := by
  obtain ⟨T', h1, e, he⟩ := exists_ext (IsFractionRing.injective O LL) hext htw T hT hχ z hz
  refine ⟨T', ?_, ?_, e, he⟩
  · convert h1 using 2 with i
    rw [add_assoc]
    congr 1
    unfold block
    rw [Nat.cast_succ, ← add_assoc, ← Finset.insert_Ico_right_eq_Ico_add_one (by omega),
      Finset.insert_val_of_notMem (by simp), ← Multiset.singleton_add]
    exact add_comm _ _
  · have h2 := sameSS_red_ext (latRep T.L) (latRep T'.L) χ e _ he Γ.lam _ hss
      (finiteLength_of_smul_eq_zero hlam fun x => by
        obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
        rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
        exact Submodule.smul_mem_pointwise_smul _ _ _ Submodule.mem_top)
    subst hχs
    exact (h2.symm.congr_left (lastEquiv O _ _ s).symm fun g x => by
      apply (lastEquiv O _ _ s).injective
      rw [LinearEquiv.apply_symm_apply]
      conv_lhs => rw [← (lastEquiv O _ _ s).apply_symm_apply x]
      rfl).symm

theorem exists_full (hext : GlobalTheory.IndefiniteRowSideFullHecke.CrystallineExtensions.ExtCrysAt PD emb) (htw : TwistCrys PD O emb)
    (Γ : GalData G Qp LL O) (hlam : Irreducible Γ.lam) {r : ℕ} (D : TopData n r) (hD : IsTopGal PD emb D Γ)
    (hε : IsCrysChar PD emb Γ.ε (fun _ => -1)) (z : ↥(latticeCocycles (twLattice Γ.T₀.L Γ.χ₁⁻¹)))
    (hz : (z : G → Γ.T₀.V) ∈ finiteCocycles PD (twistRep Γ.T₀.ρ (chiLL LL Γ.χ₁⁻¹))) :
    ∃ T : LocLat G Qp LL O, Full PD emb Γ D.t D.Ut T ∧
      ∃ e : ↥T.L.T →ₗ[O] (↥Γ.T₀.L.T × O), Function.Surjective e ∧ ∀ g x, e (latRep T.L g x) =
        (Γ.W₀ g (e x).1 + ((Γ.χ₁ g : O) * (e x).2) • (evT (twLattice Γ.T₀.L Γ.χ₁⁻¹) g z : ↥Γ.T₀.L.T),
          (Γ.χ₁ g : O) * (e x).2) := by
  have hch := isCrysChar_chi (IsFractionRing.injective O LL) htw Γ hD.2.2.1 hε
  have key : ∀ s : ℕ, ∃ T : LocLat G Qp LL O, CrysWith PD emb T.ρ (fun i => D.U i + block (D.w i) (s + 1 : ℕ)) ∧
      SameSS (modRep (latRep T.L) Γ.lam) (Γ.refRep (s + 1)) ∧
      ∃ e : ↥T.L.T →ₗ[O] (↥Γ.T₀.L.T × O), Function.Surjective e ∧ ∀ g x, e (latRep T.L g x) =
        (Γ.W₀ g (e x).1 + ((Γ.χ₁ g : O) * (e x).2) • (evT (twLattice Γ.T₀.L Γ.χ₁⁻¹) g z : ↥Γ.T₀.L.T),
          (Γ.χ₁ g : O) * (e x).2) := by
    intro s
    induction s with
    | zero =>
      obtain ⟨T, h1, h2, e, he⟩ := exists_step hext htw Γ hlam.ne_zero (U := D.U) (w := D.w) (s := 0) Γ.T₀
        (by simpa [block] using hD.2.1)
        ((lattice_reduction_sameSS hlam Γ.T₀.L Γ.T₀.L).congr_right (LinearEquiv.prodUnique).symm
          fun g x => Prod.ext rfl (Subsingleton.elim _ _))
        (χ := Γ.χ₁) (Γ.chi_one).symm (by simpa using hD.2.2.1) z hz
      exact ⟨T, h1, h2, e, e.surjective, he⟩
    | succ s ih =>
      obtain ⟨T, h1, h2, p, hp, hg⟩ := ih
      obtain ⟨T', h3, h4, e, he⟩ := exists_step hext htw Γ hlam.ne_zero T h1 h2 rfl (hch (s + 1)) 0
        (Submodule.zero_mem _)
      refine ⟨T', h3, h4, p ∘ₗ LinearMap.fst O _ _ ∘ₗ e.toLinearMap,
        hp.comp (Prod.fst_surjective.comp e.surjective), fun g x => ?_⟩
      change p (e (latRep T'.L g x)).1 = _
      rw [he, map_zero, smul_zero, add_zero]
      exact hg g _
  obtain ⟨s, hs⟩ := Nat.exists_eq_add_of_le' D.one_le_letterBlockLength
  obtain ⟨T, h1, h2, h3⟩ := key s
  rw [← hs] at h1 h2
  exact ⟨T, ⟨h1, fun L => (lattice_reduction_sameSS hlam L T.L).trans h2⟩, h3⟩

end Per

section Main

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] [IsTopologicalRing LL] {n : ℕ}
    {emb : ZMod n → (K₀ →ₐ[Qp] LL)} [IsDomain O] [IsDiscreteValuationRing O] [IsFractionRing O LL]

theorem tensCoc_mem (hO : IsOpen (Set.range (algebraMap O LL))) (T : LocLat G Qp LL O) (χ : G →* Oˣ)
    {X : Type} [AddCommGroup X] [Module O X] {c : O} (hc : c ≠ 0) (hX : ∀ x : X, c • x = 0)
    (z : ↥(latticeCocycles (twLattice T.L χ⁻¹))) (x : X) : tensCoc T.L χ X z x ∈ Z1 (twCoef (latRep T.L) χ X) ⊤ := by
  refine ⟨⟨?_, fun _ => Submodule.mem_top⟩, ?_⟩
  · exact isLocallyConstant_comp hO T.L.T T.L.fg T.L.span (c := c) (by simpa using hc)
      ((TensorProduct.mk O ↥T.L.T X).flip x) (smul_tensor_eq_zero hX)
      (fun g => evT (twLattice T.L χ⁻¹) g z) z.2.1.1
  · funext gh
    obtain ⟨g, h⟩ := gh
    change twistRep (latRep T.L) χ⁻¹ g (evT (twLattice T.L χ⁻¹) h z) ⊗ₜ[O] x -
      (evT (twLattice T.L χ⁻¹) (g * h) z : ↥T.L.T) ⊗ₜ[O] x + (evT (twLattice T.L χ⁻¹) g z : ↥T.L.T) ⊗ₜ[O] x = 0
    rw [← sub_tmul, ← add_tmul, ← latRep_twLattice, ← zero_tmul ↥T.L.T x]
    congr 1
    apply Subtype.ext
    change twistRep T.ρ (chiLL LL χ⁻¹) g ((z : G → T.V) h) - (z : G → T.V) (g * h) + (z : G → T.V) g = 0
    rw [z.2.1.2 g h]
    abel

theorem cyclic_mem_adm (hext : GlobalTheory.IndefiniteRowSideFullHecke.CrystallineExtensions.ExtCrysAt PD emb) (htw : TwistCrys PD O emb)
    (Γ : GalData G Qp LL O) (hlam : Irreducible Γ.lam) {r : ℕ} (D : TopData n r) (hD : IsTopGal PD emb D Γ)
    (hε : IsCrysChar PD emb Γ.ε (fun _ => -1)) (z : ↥(latticeCocycles (twLattice Γ.T₀.L Γ.χ₁⁻¹)))
    (hz : (z : G → Γ.T₀.V) ∈ finiteCocycles PD (twistRep Γ.T₀.ρ (chiLL LL Γ.χ₁⁻¹))) {a : ℕ} (ha : 1 ≤ a)
    [Finite (O ⧸ Ideal.span {Γ.lam ^ a})]
    (hm : tensCoc Γ.T₀.L Γ.χ₁ (O ⧸ Ideal.span {Γ.lam ^ a}) z 1 ∈
      Z1 (twCoef Γ.W₀ Γ.χ₁ (O ⧸ Ideal.span {Γ.lam ^ a})) ⊤) :
    Submodule.Quotient.mk ⟨_, hm⟩ ∈ adm PD emb Γ D.t D.Ut Γ.W₀ (O ⧸ Ideal.span {Γ.lam ^ a}) := by
  have hX : ∀ x : O ⧸ Ideal.span {Γ.lam ^ a}, Γ.lam ^ a • x = 0 := fun x => by
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))
  refine ⟨a, hX, ha, _, rfl, ?_⟩
  obtain ⟨T, hT, e, he, hg⟩ := exists_full hext htw Γ hlam D hD hε z hz
  haveI : Module.Finite O ↥Γ.T₀.L.T := Module.Finite.iff_fg.mpr Γ.T₀.L.fg
  haveI : Finite (↥Γ.T₀.L.T ⊗[O] (O ⧸ Ideal.span {Γ.lam ^ a})) := by
    haveI : Finite ((O ⧸ Ideal.span {Γ.lam ^ a}) ⊗[O] ↥Γ.T₀.L.T) :=
      Module.finite_of_finite (O ⧸ Ideal.span {Γ.lam ^ a})
    exact Finite.of_equiv _ (TensorProduct.comm O _ _).toEquiv
  let q : ↥Γ.T₀.L.T →ₗ[O] ↥Γ.T₀.L.T ⊗[O] (O ⧸ Ideal.span {Γ.lam ^ a}) := (TensorProduct.mk O _ _).flip 1
  have hq : Function.Surjective q := fun y => by
    induction y using TensorProduct.induction_on with
    | zero => exact ⟨0, map_zero q⟩
    | add _ _ h1 h2 =>
      obtain ⟨u, rfl⟩ := h1
      obtain ⟨v, rfl⟩ := h2
      exact ⟨u + v, map_add q u v⟩
    | tmul t y =>
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
      refine ⟨y • t, ?_⟩
      change (y • t) ⊗ₜ[O] 1 = _
      rw [smul_tmul, Algebra.smul_def, mul_one]
      rfl
  refine admissible_of_surjective hT _ ((q.prodMap (Submodule.mkQ (Ideal.span {Γ.lam ^ a}))) ∘ₗ e)
    ((hq.prodMap (Submodule.mkQ_surjective _)).comp he) (fun g x => ?_) (pow_ne_zero a hlam.ne_zero)
    (fun y => Prod.ext (smul_tensor_eq_zero hX y.1) (hX y.2))
  change (q (e (latRep T.L g x)).1, Ideal.Quotient.mk _ (e (latRep T.L g x)).2) =
    Ea Γ.W₀ Γ.χ₁ hX _ g (q (e x).1, Ideal.Quotient.mk _ (e x).2)
  rw [Ea_apply, hg, map_add, map_smul]
  rfl

theorem finite_subset_adm (hO : IsOpen (Set.range (algebraMap O LL)))
    (hfin : ∀ c : O, c ≠ 0 → Finite (O ⧸ Ideal.span {c}))
    (hext : GlobalTheory.IndefiniteRowSideFullHecke.CrystallineExtensions.ExtCrysAt PD emb) (htw : TwistCrys PD O emb)
    (Γ : GalData G Qp LL O) (hlam : Irreducible Γ.lam) {r : ℕ} (D : TopData n r) (hD : IsTopGal PD emb D Γ)
    (hε : IsCrysChar PD emb Γ.ε (fun _ => -1)) (X : Type) [AddCommGroup X] [Module O X] [Finite X]
    (hA : ∃ A : Submodule O (H1 (twCoef Γ.W₀ Γ.χ₁ X) ⊤), adm PD emb Γ D.t D.Ut Γ.W₀ X = A)
    (hmap : ∀ (Y : Type) [AddCommGroup Y] [Module O Y] [Finite Y] (f : Y →ₗ[O] X)
      (c : H1 (twCoef Γ.W₀ Γ.χ₁ Y) ⊤), c ∈ adm PD emb Γ D.t D.Ut Γ.W₀ Y →
        coefH1 Γ.W₀ Γ.χ₁ f c ∈ adm PD emb Γ D.t D.Ut Γ.W₀ X) :
    (finiteSelmer PD Γ.T₀.L Γ.χ₁ X : Set _) ⊆ adm PD emb Γ D.t D.Ut Γ.W₀ X := by
  obtain ⟨A, hA⟩ := hA
  obtain ⟨a, ha, hX⟩ := exists_pow_smul_eq_zero hlam.not_isUnit X
  have h0 := pow_ne_zero a hlam.ne_zero
  haveI := hfin _ h0
  rintro c ⟨y, hy⟩
  have key : ((tensAmb Γ.T₀.L Γ.χ₁ X).comp ((latticeFiniteCohomology PD (twLattice Γ.T₀.L Γ.χ₁⁻¹)).subtype.rTensor X)) y ∈
      A.map (toAmb (twCoef Γ.W₀ Γ.χ₁ X)) := by
    clear hy
    induction y using TensorProduct.induction_on with
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add _ _ h1 h2 => rw [map_add]; exact Submodule.add_mem _ h1 h2
    | tmul κ x =>
      obtain ⟨_, z, hz, rfl⟩ := κ
      have hY : ∀ x : O ⧸ Ideal.span {Γ.lam ^ a}, Γ.lam ^ a • x = 0 := fun x => by
        obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
        exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))
      have h1 := hmap _ (cycMap hX x) _ (cyclic_mem_adm hext htw Γ hlam D hD hε z hz.2 ha
        (tensCoc_mem hO Γ.T₀ Γ.χ₁ h0 hY z 1))
      rw [hA] at h1
      refine ⟨_, h1, ?_⟩
      change Submodule.Quotient.mk _ = Submodule.Quotient.mk (tensCoc Γ.T₀.L Γ.χ₁ X z x)
      congr 1
      funext g
      change (evT (twLattice Γ.T₀.L Γ.χ₁⁻¹) g z : ↥Γ.T₀.L.T) ⊗ₜ[O] ((1 : O) • x) =
        (evT (twLattice Γ.T₀.L Γ.χ₁⁻¹) g z : ↥Γ.T₀.L.T) ⊗ₜ[O] x
      rw [one_smul]
  obtain ⟨c', hc', h⟩ := key
  rw [hA, ← toAmb_injective _ (h.trans hy)]
  exact hc'

omit [IsTopologicalRing LL] [IsDomain O] [IsDiscreteValuationRing O] [IsFractionRing O LL] in

theorem finite_classes_subset_admissible_of_goodO [TopologicalSpace Qp] (hO : Formalism.MainNotions.N.GoodO (Qp := Qp) LL O)
    (hfin : ∀ c : O, c ≠ 0 → Finite (O ⧸ Ideal.span {c}))
    (hext : GlobalTheory.IndefiniteRowSideFullHecke.CrystallineExtensions.ExtCrysAt PD emb) (htw : TwistCrys PD O emb)
    (Γ : GalData G Qp LL O) (hlam : Irreducible Γ.lam) {r : ℕ} (D : TopData n r) (hD : IsTopGal PD emb D Γ)
    (hε : IsCrysChar PD emb Γ.ε (fun _ => -1)) (X : Type) [AddCommGroup X] [Module O X] [Finite X]
    (hA : ∃ A : Submodule O (H1 (twCoef Γ.W₀ Γ.χ₁ X) ⊤), adm PD emb Γ D.t D.Ut Γ.W₀ X = A)
    (hmap : ∀ (Y : Type) [AddCommGroup Y] [Module O Y] [Finite Y] (f : Y →ₗ[O] X)
      (c : H1 (twCoef Γ.W₀ Γ.χ₁ Y) ⊤), c ∈ adm PD emb Γ D.t D.Ut Γ.W₀ Y →
        coefH1 Γ.W₀ Γ.χ₁ f c ∈ adm PD emb Γ D.t D.Ut Γ.W₀ X) :
    (finiteSelmer PD Γ.T₀.L Γ.χ₁ X : Set _) ⊆ adm PD emb Γ D.t D.Ut Γ.W₀ X := by
  obtain ⟨⟨_, _, _⟩, -, -, _, hO⟩ := hO
  exact finite_subset_adm hO hfin hext htw Γ hlam D hD hε X hA hmap

end Main

theorem finite_quotient (l : ℕ) [Fact l.Prime] (LL : FinExt l) (c : ↥(OL LL)) (hc : c ≠ 0) :
    Finite (↥(OL LL) ⧸ Ideal.span {c}) := by
  have h1 : (Ideal.span {c}).comap (algebraMap ℤ_[l] ↥(OL LL)) ≠ ⊥ :=
    Ideal.comap_ne_bot_of_integral_mem hc (Ideal.mem_span_singleton_self c) (integralClosure.isIntegral c)
  obtain ⟨m, hm⟩ := PadicInt.ideal_eq_span_pow_p h1
  have h2 : Ideal.span {((l : ℕ) : ↥(OL LL)) ^ m} ≤ Ideal.span {c} := by
    rw [Ideal.span_singleton_le_iff_mem]
    have h3 : ((l : ℕ) : ℤ_[l]) ^ m ∈ (Ideal.span {c}).comap (algebraMap ℤ_[l] ↥(OL LL)) := by
      rw [hm]
      exact Ideal.mem_span_singleton_self _
    rwa [Ideal.mem_comap, map_pow, map_natCast] at h3
  haveI := (GlobalTheory.LocalIntegers.good_integers l LL).2 m
  exact Finite.of_surjective _ (Ideal.Quotient.factor_surjective h2)

theorem finAdm : ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} (S : TopSit P),
    S.CrysCalc → GlobalTheory.IndefiniteRowSideFullHecke.CrystallineExtensions.ExtCrys P → S.Closed → S.StdAdm → S.Lem0 S.Γ.W₀ → S.FinAdm := by
  intro l _ P S hC hE _ _ hL X i1 i2 i3
  have h1 : TwistCrys (P.PD S.K) S.O S.emb := hC.2.1
  have h2 := hE S.K S.LL S.n S.emb S.Γ.lam S.hyp.1
  have h3 := finite_classes_subset_admissible_of_goodO (GlobalTheory.LocalIntegers.good_integers l S.LL).1 (finite_quotient l S.LL) h2 h1 S.Γ
    S.hyp.1.2.2.2.2.2 S.D S.hyp.2.1 hC.2.2.1 X
  have h4 := h3 (hL X).1
  have h5 := h4 (fun Y j1 j2 j3 f c => ((@hL Y j1 j2 j3).2.2 X f c).1)
  exact h5

end GlobalTheory.FiniteAdm
