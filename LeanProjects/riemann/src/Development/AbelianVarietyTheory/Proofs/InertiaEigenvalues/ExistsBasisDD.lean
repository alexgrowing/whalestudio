import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.UnitDualParts
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.GammaStableInverse
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.WachLettersFree
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.CrystallineSubrepresentation
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqTopOfSpanImage
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IoEquivariant

noncomputable section

namespace GlobalTheory.WachTensor

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.UnitDualParts GlobalTheory.EtaleExact

section Ext

variable {O : Type} [CommRing O] (R : Type) [CommRing R] [Algebra O R] {M M' M'' : Type}
    [AddCommGroup M] [Module O M] [AddCommGroup M'] [Module O M'] [AddCommGroup M''] [Module O M'']

def mulL (m : M ⊗[O] M' →ₗ[O] M'') : R ⊗[O] M →ₗ[R] R ⊗[O] M' →ₗ[R] R ⊗[O] M'' :=
  (TensorProduct.mk R _ _).compr₂
    (m.baseChange R ∘ₗ (AlgebraTensorModule.distribBaseChange O R M M').symm.toLinearMap)

theorem mulL_apply (m : M ⊗[O] M' →ₗ[O] M'') (x : R ⊗[O] M) (y : R ⊗[O] M') :
    mulL R m x y = extMul R m x y := rfl

theorem mulL_tmul (m : M ⊗[O] M' →ₗ[O] M'') (r r' : R) (a : M) (a' : M') :
    mulL R m (r ⊗ₜ[O] a) (r' ⊗ₜ[O] a') = (r * r') ⊗ₜ[O] m (a ⊗ₜ[O] a') :=
  extMul_tmul R m r r' a a'

theorem map_mulL (m : M ⊗[O] M' →ₗ[O] M'') (f : R →ₐ[O] R) (a : M →ₗ[O] M) (a' : M' →ₗ[O] M')
    (a'' : M'' →ₗ[O] M'') (h : ∀ x y, m (a x ⊗ₜ[O] a' y) = a'' (m (x ⊗ₜ[O] y)))
    (x : R ⊗[O] M) (y : R ⊗[O] M') :
    TensorProduct.map f.toLinearMap a'' (mulL R m x y) =
      mulL R m (TensorProduct.map f.toLinearMap a x) (TensorProduct.map f.toLinearMap a' y) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, hx, hx']
  | tmul r u =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add y y' hy hy' => simp only [map_add, hy, hy']
    | tmul r' u' => simp [mulL_tmul, h]

def pairL (β : M →ₗ[O] M' →ₗ[O] O) : R ⊗[O] M →ₗ[R] R ⊗[O] M' →ₗ[R] R :=
  (mulL R (TensorProduct.lift β)).compr₂ (AlgebraTensorModule.rid O R R).toLinearMap

theorem pairL_apply (β : M →ₗ[O] M' →ₗ[O] O) (x : R ⊗[O] M) (y : R ⊗[O] M') :
    pairL R β x y = extPair R β x y := rfl

theorem pairL_tmul (β : M →ₗ[O] M' →ₗ[O] O) (r r' : R) (a : M) (a' : M') :
    pairL R β (r ⊗ₜ[O] a) (r' ⊗ₜ[O] a') = β a a' • (r * r') :=
  extPair_tmul R β r r' a a'

theorem map_pairL (β : M →ₗ[O] M' →ₗ[O] O) (f : R →ₐ[O] R) (a : M →ₗ[O] M) (a' : M' →ₗ[O] M')
    (h : ∀ x y, β (a x) (a' y) = β x y) (x : R ⊗[O] M) (y : R ⊗[O] M') :
    f (pairL R β x y) =
      pairL R β (TensorProduct.map f.toLinearMap a x) (TensorProduct.map f.toLinearMap a' y) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, hx, hx']
  | tmul r u =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add y y' hy hy' => simp only [map_add, hy, hy']
    | tmul r' u' => simp [pairL_tmul, h]

theorem map_smul_alg (f : R →ₐ[O] R) (a : M →ₗ[O] M) (r : R) (x : R ⊗[O] M) :
    TensorProduct.map f.toLinearMap a (r • x) = f r • TensorProduct.map f.toLinearMap a x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x x' hx hx' => simp only [smul_add, map_add, hx, hx']
  | tmul r' u => simp [TensorProduct.smul_tmul']

end Ext

theorem exists_descend {E R D D' D'' M M' M'' : Type} [CommRing E] [CommRing R]
    [AddCommGroup D] [Module E D] [AddCommGroup D'] [Module E D'] [AddCommGroup D''] [Module E D'']
    [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M'] [AddCommGroup M''] [Module R M'']
    (io : E → R) (j : D →+ M) (j' : D' →+ M') (j'' : D'' →+ M'')
    (hj : ∀ e x, j (e • x) = io e • j x) (hj' : ∀ e x, j' (e • x) = io e • j' x)
    (hj'' : ∀ e x, j'' (e • x) = io e • j'' x) (hinj : Function.Injective j'')
    (b : M →ₗ[R] M' →ₗ[R] M'') {ι κ : Type} [Fintype ι] [Fintype κ] (e : Module.Basis ι E D)
    (e' : Module.Basis κ E D') (h : ∀ a c, ∃ z, j'' z = b (j (e a)) (j' (e' c))) :
    ∃ μ : D →ₗ[E] D' →ₗ[E] D'', ∀ x y, j'' (μ x y) = b (j x) (j' y) := by
  choose z hz using h
  refine ⟨e.constr E fun a => e'.constr E fun c => z a c, fun x y => ?_⟩
  conv_rhs => rw [← e.sum_repr x, ← e'.sum_repr y]
  simp only [Module.Basis.constr_apply_fintype, LinearMap.sum_apply, LinearMap.smul_apply, map_sum,
    hj, hj', hj'', hz, map_smul, Module.Basis.equivFun_apply, Finset.smul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  rw [smul_comm]

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {W : LocWach PD LL O v n} {RA RW : Type} [CommRing RA] [CommRing RW] [Algebra O RA]
    [Algebra O RW] {inclR : RA →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : RA}
    (E : EtTie W RA RW inclR φR gR πA)

def Descends : Prop :=
  ∀ (ι : Type) [Fintype ι] (M : ι → ι → W.EE) (w : ι → RW),
    (∀ g : G, W.resΓ g = 1 → ∀ i, gR g (w i) = w i) →
    (∀ i, w i = ∑ j, E.ioE (M i j) * φR (w j)) → ∀ i, ∃ e : W.EE, E.ioE e = w i

theorem nontrivial_EE (W : LocWach PD LL O v n) : Nontrivial W.EE :=
  haveI : Nontrivial O := (algebraMap O LL).domain_nontrivial
  W.EE_inj.nontrivial

theorem exists_basis_jD (T : LocLat G Qp LL O) {ι : Type} [Fintype ι]
    (e : Module.Basis ι W.EE (W.DD T)) :
    ∃ c : Module.Basis ι RW (TW RW T), ∀ i, c i = E.jD T (e i) := by
  classical
  haveI : Nontrivial O := (algebraMap O LL).domain_nontrivial
  haveI := nontrivial_EE W
  haveI : Nontrivial RW := (ioE_injective E).nontrivial
  haveI := T.L.free
  have hsp : ⊤ ≤ Submodule.span RW (Set.range fun i => E.jD T (e i)) := by
    rw [← E.jD_span T, Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    rw [← e.sum_repr x, map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [E.jD_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  refine ⟨basisOfTopLeSpanOfCardEqFinrank (fun i => E.jD T (e i)) hsp ?_,
    fun i => congrFun (coe_basisOfTopLeSpanOfCardEqFinrank _ _ _) i⟩
  rw [Module.finrank_baseChange, ← (W.DD_free T).2, Module.finrank_eq_card_basis e]

include E in
theorem exists_basis_DD (T : LocLat G Qp LL O) :
    Nonempty (Module.Basis (Fin (Module.finrank O ↥T.L.T)) W.EE (W.DD T)) := by
  haveI := nontrivial_EE W
  haveI := (W.DD_free T).1
  haveI := finite_DD E T
  exact ⟨Module.finBasisOfFinrankEq _ _ (W.DD_free T).2⟩

theorem jD_fixed (T : LocLat G Qp LL O) (g : G) (hg : W.resΓ g = 1) (x : W.DD T) :
    TWact (gR g) T g (E.jD T x) = E.jD T x := by
  rw [← E.jD_act, hg, W.γD_one]

theorem exists_frob_inv (hm : ∀ m : Ideal W.EE, m.IsMaximal → m.map E.ioE.toRingHom ≠ ⊤)
    (hφ : Function.Surjective φR) (T : LocLat G Qp LL O) {ι : Type} [Fintype ι]
    (e : Module.Basis ι W.EE (W.DD T)) :
    Submodule.span W.EE (Set.range fun i => W.φD T (e i)) = ⊤ := by
  refine eq_top_DD E hm T _ ?_
  obtain ⟨c, hc⟩ := exists_basis_jD E T e
  rw [eq_top_iff]
  intro y _
  obtain ⟨x, rfl⟩ : ∃ x, TWmap φR T x = y :=
    TensorProduct.map_surjective (g := φR.toLinearMap) hφ Function.surjective_id y
  rw [← c.sum_repr x, map_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [TWmap, map_smul_alg]
  refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨W.φD T (e i),
    Submodule.subset_span ⟨i, rfl⟩, ?_⟩)
  rw [E.jD_φ, hc]
  rfl

theorem mem_range_jD (hd : Descends E) (T : LocLat G Qp LL O) {ι : Type} [Fintype ι]
    (U : ι → ι → W.EE) (z : ι → TW RW T)
    (hz : ∀ g : G, W.resΓ g = 1 → ∀ a, TWact (gR g) T g (z a) = z a)
    (hU : ∀ a, z a = ∑ b, E.ioE (U a b) • TWmap φR T (z b)) (a : ι) :
    ∃ x, E.jD T x = z a := by
  classical
  obtain ⟨e⟩ := exists_basis_DD E T
  obtain ⟨c, hc⟩ := exists_basis_jD E T e
  have h := hd (ι × Fin (Module.finrank O ↥T.L.T))
    (fun p q => U p.1 q.1 * e.repr (W.φD T (e q.2)) p.2) (fun p => c.repr (z p.1) p.2) ?_ ?_
  · choose u hu using h
    refine ⟨∑ k, u (a, k) • e k, ?_⟩
    rw [map_sum, ← c.sum_repr (z a)]
    exact Finset.sum_congr rfl fun k _ => by rw [E.jD_smul, hu, hc]
  · rintro g hg ⟨a, k⟩
    have h1 := hz g hg a
    conv_lhs at h1 => rw [← c.sum_repr (z a), map_sum]
    simp only [GlobalTheory.Cyc.Decomp.TWact_smul, hc, jD_fixed E T g hg] at h1
    simp only [← hc] at h1
    conv_rhs => rw [← h1]
    simp [Finsupp.single_apply]
  · rintro ⟨a, k⟩
    have h2 : ∀ q, TWmap φR T (c q) = ∑ r, E.ioE (e.repr (W.φD T (e q)) r) • c r := by
      intro q
      rw [hc, ← E.jD_φ]
      conv_lhs => rw [← e.sum_repr (W.φD T (e q)), map_sum]
      simp only [E.jD_smul, hc]
    have h3 : ∀ b, c.repr (TWmap φR T (z b)) k =
        ∑ q, E.ioE (e.repr (W.φD T (e q)) k) * φR (c.repr (z b) q) := by
      intro b
      conv_lhs => rw [← c.sum_repr (z b), map_sum, map_sum, Finsupp.finset_sum_apply]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [TWmap, map_smul_alg]
      change c.repr (_ • TWmap φR T (c q)) k = _
      rw [h2, map_smul, Finsupp.smul_apply, c.repr_sum_self, smul_eq_mul, mul_comm]
    change c.repr (z a) k = _
    conv_lhs => rw [hU a, map_sum, Finsupp.finset_sum_apply]
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [map_smul, Finsupp.smul_apply, h3, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun q _ => by rw [map_mul, mul_assoc]

theorem ioE_φE (hO : Function.Injective (algebraMap O LL)) (a : W.EE) :
    E.ioE (W.φE a) = φR (E.ioE a) := by
  obtain ⟨e, e₀, h₀, hj, -⟩ := E.one_e
  obtain ⟨e₁, he₁, hT⟩ := W.one_line
  have he₁T : e₁ ∈ W.one.L.T := by rw [hT]; exact Submodule.mem_span_singleton_self e₁
  have h1 : TWmap φR W.one ((1 : RW) ⊗ₜ[O] e₀) = (1 : RW) ⊗ₜ[O] e₀ := by simp [TWmap]
  have h2 := E.jD_φ W.one (a • e)
  rw [W.φD_smul, E.jD_smul, E.jD_smul, E.jD_φ, hj, h1, TensorProduct.smul_tmul',
    TensorProduct.smul_tmul', smul_eq_mul, smul_eq_mul, mul_one, mul_one] at h2
  exact GlobalTheory.Cyc.Decomp.tmul_gen_cancel hO W.one e₁ he₁ he₁T e₀ h₀ _ _ h2

theorem ioE_γE (hO : Function.Injective (algebraMap O LL)) (g : G) (a : W.EE) :
    E.ioE (W.γE (W.resΓ g) a) = gR g (E.ioE a) := by
  obtain ⟨e, e₀, h₀, hj, -⟩ := E.one_e
  obtain ⟨e₁, he₁, hT⟩ := W.one_line
  have he₁T : e₁ ∈ W.one.L.T := by rw [hT]; exact Submodule.mem_span_singleton_self e₁
  have hact : W.one.actT g e₀ = e₀ := Subtype.ext (W.one_triv g e₀)
  have h1 : TWact (gR g) W.one g ((1 : RW) ⊗ₜ[O] e₀) = (1 : RW) ⊗ₜ[O] e₀ := by
    simp [TWact, hact]
  have h2 := E.jD_act W.one g (a • e)
  rw [W.γD_smul, E.jD_smul, E.jD_smul, E.jD_act, hj, GlobalTheory.Cyc.Decomp.TWact_smul, h1,
    TensorProduct.smul_tmul', TensorProduct.smul_tmul', smul_eq_mul, smul_eq_mul,
    mul_one, mul_one] at h2
  exact GlobalTheory.Cyc.Decomp.tmul_gen_cancel hO W.one e₁ he₁ he₁T e₀ h₀ _ _ h2

theorem exists_basis_V [IsFractionRing O LL] (T : LocLat G Qp LL O) {ι : Type}
    (t : Module.Basis ι O ↥T.L.T) : ∃ b : Module.Basis ι LL T.V, ∀ i, b i = (t i : T.V) := by
  have h1 : LinearIndependent O fun i => (t i : T.V) :=
    t.linearIndependent.map' T.L.T.subtype (Submodule.ker_subtype _)
  have h2 : LinearIndependent LL fun i => (t i : T.V) := (LinearIndependent.iff_fractionRing O LL).1 h1
  refine ⟨Module.Basis.mk h2 ?_, fun i => Module.Basis.mk_apply _ _ i⟩
  rw [← T.L.span, Submodule.span_le]
  intro x hx
  have h3 : (⟨x, hx⟩ : ↥T.L.T) ∈ Submodule.span O (Set.range t) := by rw [t.span_eq]; trivial
  have h4 := Submodule.mem_map_of_mem (f := T.L.T.subtype) h3
  rw [Submodule.map_span, ← Set.range_comp] at h4
  exact Submodule.span_le_restrictScalars O LL _ h4

theorem exists_extend [IsFractionRing O LL] (T : LocLat G Qp LL O) {U : Type} [AddCommGroup U]
    [Module LL U] [Module O U] [IsScalarTower O LL U] (g : ↥T.L.T →ₗ[O] U) :
    ∃ f : T.V →ₗ[LL] U, ∀ x : ↥T.L.T, f x = g x := by
  haveI := T.L.free
  let t := Module.Free.chooseBasis O ↥T.L.T
  obtain ⟨b, hb⟩ := exists_basis_V T t
  refine ⟨b.constr LL fun i => g (t i), fun x => ?_⟩
  have : ((b.constr LL fun i => g (t i)).restrictScalars O) ∘ₗ T.L.T.subtype = g :=
    t.ext fun i => by simp [← hb]
  exact LinearMap.congr_fun this x

theorem ext_lat (T : LocLat G Qp LL O) {U : Type} [AddCommGroup U] [Module LL U]
    {f g : T.V →ₗ[LL] U} (h : ∀ x : ↥T.L.T, f x = g x) : f = g :=
  LinearMap.ext_on T.L.span fun x hx => h ⟨x, hx⟩

theorem φD_smulA (T : LocLat G Qp LL O) (a : LetA O n) (x : W.DD T) :
    W.φD T (a • x) = W.φA a • W.φD T x := by
  have := W.φD_smul T (algebraMap (LetA O n) W.EE a) x
  rwa [algebraMap_smul, W.φE_ext, algebraMap_smul] at this

theorem γA_sub (W : LocWach PD LL O v n) (g : W.Gam) (a : LetA O n) :
    ∃ b : LetA O n, W.γA g a - a = letπ * b := by
  have h : ∀ f : PowerSeries O, ∃ b, W.γ₀ g f - f = PowerSeries.X * b := by
    intro f
    rw [← dvd_def, PowerSeries.X_dvd_iff]
    have hf := PowerSeries.eq_X_mul_shift_add_const f
    have hC : ∀ c : O, W.γ₀ g (PowerSeries.C c) = PowerSeries.C c := fun c => (W.γ₀ g).commutes c
    rw [map_sub, sub_eq_zero]
    conv_lhs => rw [hf, map_add, map_mul, hC]
    simp [(W.γ₀_X g).1]
  choose b hb using h
  exact ⟨fun i => b (a i), funext fun i => hb (a i)⟩

end Generic

end GlobalTheory.WachTensor
