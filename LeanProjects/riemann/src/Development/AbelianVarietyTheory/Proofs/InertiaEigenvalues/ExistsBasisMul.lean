import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.UnitDualParts
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.GammaStableInverse
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.WachLettersFree
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.CrystallineSubrepresentation
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqTopOfSpanImage
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IoEquivariant
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBasisDD

noncomputable section

namespace GlobalTheory.WachTensor

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.UnitDualParts GlobalTheory.EtaleExact
open GlobalTheory.IndefiniteRowSideFullHecke.CrystallineSubrepresentation (QuotCrys TensorCrys DualCrys)
open GlobalTheory.IndefiniteRowSideFullHecke.GammaStableInverse GlobalTheory.IndefiniteRowSideFullHecke.WachLettersFreeness

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

theorem bil_expand {R M M' M'' : Type} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup M']
    [Module R M'] [AddCommGroup M''] [Module R M''] (b : M →ₗ[R] M' →ₗ[R] M'') {ι κ : Type}
    [Fintype ι] [Fintype κ] (u : ι → R) (x : ι → M) (u' : κ → R) (y : κ → M') :
    b (∑ i, u i • x i) (∑ k, u' k • y k) = ∑ q : ι × κ, (u q.1 * u' q.2) • b (x q.1) (y q.2) := by
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
    Fintype.sum_prod_type, mul_smul, Finset.smul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => smul_comm _ _ _

theorem exists_frob_mat (hm : ∀ m : Ideal W.EE, m.IsMaximal → m.map E.ioE.toRingHom ≠ ⊤)
    (hφ : Function.Surjective φR) (T : LocLat G Qp LL O) {ι : Type} [Fintype ι]
    (e : Module.Basis ι W.EE (W.DD T)) : ∃ U : ι → ι → W.EE, ∀ a,
      E.jD T (e a) = ∑ b, E.ioE (U a b) • TWmap φR T (E.jD T (e b)) := by
  choose U hU using fun a => (Submodule.mem_span_range_iff_exists_fun W.EE).1
    ((exists_frob_inv E hm hφ T e).ge (Submodule.mem_top (x := e a)))
  refine ⟨U, fun a => ?_⟩
  conv_lhs => rw [← hU a, map_sum]
  exact Finset.sum_congr rfl fun b _ => by rw [E.jD_smul, E.jD_φ]

theorem exists_bases {T : LocLat G Qp LL O} {r : ℕ} {b : Fin r → W.DD T} (hb : IsWachBasis W T b) :
    ∃ (e : Module.Basis (Fin r) W.EE (W.DD T)) (c : Module.Basis (Fin r) (LetA O n) ↥(W.N T)),
      ∀ i, e i = (c i : W.DD T) := by
  obtain ⟨h1, h2, h3, h4⟩ := hb
  refine ⟨Module.Basis.mk h3 h4.ge, (Module.Basis.span h1).map (LinearEquiv.ofEq _ _ h2), fun i => ?_⟩
  simp [Module.Basis.span_apply]

theorem isCrys_tensor [IsFractionRing O LL] (hq : QuotCrys PD LL) (ht : TensorCrys PD LL)
    {T T' T'' : LocLat G Qp LL O} (hT : IsCrys PD T.ρ) (hT' : IsCrys PD T'.ρ)
    (m : ↥T.L.T ⊗[O] ↥T'.L.T ≃ₗ[O] ↥T''.L.T) (hm : IsTensorLat m) : IsCrys PD T''.ρ := by
  obtain ⟨f₁, hf₁⟩ := exists_extend T
    ((TensorProduct.mk O ↥T.L.T ↥T'.L.T).compr₂ (T''.L.T.subtype ∘ₗ m.toLinearMap))
  obtain ⟨f₂, hf₂⟩ := exists_extend T' f₁.flip
  have hf : ∀ (x : ↥T.L.T) (y : ↥T'.L.T), f₂ y x = (m (x ⊗ₜ[O] y) : T''.V) := fun x y => by
    rw [hf₂, LinearMap.flip_apply, hf₁]; rfl
  refine hq _ (T.ρ.tprod T'.ρ) _ T''.ρ (TensorProduct.lift f₂.flip) ?_ ?_ (ht _ _ _ _ hT hT')
  · intro g z
    have : (f₂.flip.compl₁₂ (T.ρ g) (T'.ρ g)) = f₂.flip.compr₂ (T''.ρ g) := by
      refine ext_lat T fun x => ext_lat T' fun y => ?_
      have h1 := hf (T.actT g x) (T'.actT g y)
      rw [hm] at h1
      change f₂ (T'.ρ g y) (T.ρ g x) = T''.ρ g (f₂ y x)
      rw [hf]
      exact h1
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul x y => simpa using LinearMap.congr_fun₂ this x y
  · rw [← LinearMap.range_eq_top, eq_top_iff, ← T''.L.span, Submodule.span_le]
    intro z hz
    obtain ⟨w, hw⟩ := m.surjective ⟨z, hz⟩
    have hz' : z = (m w : T''.V) := by rw [hw]
    rw [hz']
    clear hw hz' hz
    induction w using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => rw [map_add, Submodule.coe_add]; exact Submodule.add_mem _ hx hy
    | tmul x y => exact ⟨(x : T.V) ⊗ₜ[LL] (y : T'.V), by simp [hf]⟩

theorem exists_mul (hm : ∀ m : Ideal W.EE, m.IsMaximal → m.map E.ioE.toRingHom ≠ ⊤)
    (hφ : Function.Surjective φR) (hd : Descends E) {T T' T'' : LocLat G Qp LL O}
    (m : ↥T.L.T ⊗[O] ↥T'.L.T ≃ₗ[O] ↥T''.L.T) (hmt : IsTensorLat m) :
    ∃ μ : W.DD T →ₗ[W.EE] W.DD T' →ₗ[W.EE] W.DD T'',
      ∀ x y, E.jD T'' (μ x y) = mulL RW m.toLinearMap (E.jD T x) (E.jD T' y) := by
  obtain ⟨e⟩ := exists_basis_DD E T
  obtain ⟨e'⟩ := exists_basis_DD E T'
  obtain ⟨U, hU⟩ := exists_frob_mat E hm hφ T e
  obtain ⟨U', hU'⟩ := exists_frob_mat E hm hφ T' e'
  have hact : ∀ (g : G) (x : TW RW T) (y : TW RW T'),
      TWact (gR g) T'' g (mulL RW m.toLinearMap x y) =
        mulL RW m.toLinearMap (TWact (gR g) T g x) (TWact (gR g) T' g y) := fun g x y =>
    map_mulL RW m.toLinearMap (gR g) (T.actT g) (T'.actT g) (T''.actT g) (hmt g) x y
  have hfr : ∀ (x : TW RW T) (y : TW RW T'), TWmap φR T'' (mulL RW m.toLinearMap x y) =
      mulL RW m.toLinearMap (TWmap φR T x) (TWmap φR T' y) := fun x y =>
    map_mulL RW m.toLinearMap φR LinearMap.id LinearMap.id LinearMap.id (fun _ _ => rfl) x y
  generalize mulL RW m.toLinearMap = b at hact hfr ⊢
  have key := mem_range_jD E hd T''
    (ι := Fin (Module.finrank O ↥T.L.T) × Fin (Module.finrank O ↥T'.L.T))
    (fun p q => U p.1 q.1 * U' p.2 q.2) (fun p => b (E.jD T (e p.1)) (E.jD T' (e' p.2)))
    (fun g hg p => by simp only [hact, jD_fixed E T g hg, jD_fixed E T' g hg])
    (fun p => by
      simp only [hfr, map_mul]
      rw [← bil_expand b (fun b => E.ioE (U p.1 b))
        (fun b => TWmap φR T (E.jD T (e b))) (fun b => E.ioE (U' p.2 b))
        (fun b => TWmap φR T' (E.jD T' (e' b))), ← hU, ← hU'])
  exact exists_descend E.ioE (E.jD T).toAddMonoidHom (E.jD T').toAddMonoidHom
    (E.jD T'').toAddMonoidHom (E.jD_smul T) (E.jD_smul T') (E.jD_smul T'') (E.jD_inj T'')
    b e e' fun a c => key (a, c)

theorem exists_basis_mul (hm : ∀ m : Ideal W.EE, m.IsMaximal → m.map E.ioE.toRingHom ≠ ⊤)
    {T T' T'' : LocLat G Qp LL O} (m : ↥T.L.T ⊗[O] ↥T'.L.T ≃ₗ[O] ↥T''.L.T)
    (μ : W.DD T →ₗ[W.EE] W.DD T' →ₗ[W.EE] W.DD T'')
    (hμ : ∀ x y, E.jD T'' (μ x y) = mulL RW m.toLinearMap (E.jD T x) (E.jD T' y))
    {ι κ : Type} [Fintype ι] [Fintype κ] (e : Module.Basis ι W.EE (W.DD T))
    (e' : Module.Basis κ W.EE (W.DD T')) :
    ∃ e'' : Module.Basis (ι × κ) W.EE (W.DD T''), ∀ p, e'' p = μ (e p.1) (e' p.2) := by
  classical
  haveI : Nontrivial O := (algebraMap O LL).domain_nontrivial
  haveI := nontrivial_EE W
  haveI := T.L.free
  haveI := T'.L.free
  obtain ⟨c, hc⟩ := exists_basis_jD E T e
  obtain ⟨c', hc'⟩ := exists_basis_jD E T' e'
  have hsp : Submodule.span W.EE (Set.range fun p : ι × κ => μ (e p.1) (e' p.2)) = ⊤ := by
    refine eq_top_DD E hm T'' _ ?_
    set S := Submodule.span RW (E.jD T'' '' (Submodule.span W.EE
      (Set.range fun p : ι × κ => μ (e p.1) (e' p.2)) : Set (W.DD T''))) with hS
    have h1 : ∀ x y, mulL RW m.toLinearMap x y ∈ S := by
      intro x y
      rw [← c.sum_repr x, ← c'.sum_repr y]
      simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply]
      refine Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _
        (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_)
      rw [hc, hc', ← hμ]
      exact Submodule.subset_span ⟨_, Submodule.subset_span ⟨(i, k), rfl⟩, rfl⟩
    rw [eq_top_iff]
    rintro z -
    induction z using TensorProduct.induction_on with
    | zero => exact S.zero_mem
    | add x y hx hy => exact S.add_mem hx hy
    | tmul r u =>
      obtain ⟨w, rfl⟩ := m.surjective u
      induction w using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => rw [map_add, TensorProduct.tmul_add]; exact S.add_mem hx hy
      | tmul x y =>
        have := h1 (r ⊗ₜ[O] x) ((1 : RW) ⊗ₜ[O] y)
        rwa [mulL_tmul, mul_one] at this
  refine ⟨basisOfTopLeSpanOfCardEqFinrank _ hsp.ge ?_,
    fun i => congrFun (coe_basisOfTopLeSpanOfCardEqFinrank _ _ _) i⟩
  rw [(W.DD_free T'').2, ← m.finrank_eq, Module.finrank_tensorProduct, ← (W.DD_free T).2,
    ← (W.DD_free T').2, Module.finrank_eq_card_basis e, Module.finrank_eq_card_basis e',
    Fintype.card_prod]

theorem tensorFor [IsFractionRing O LL]
    (hm : ∀ m : Ideal W.EE, m.IsMaximal → m.map E.ioE.toRingHom ≠ ⊤)
    (hφ : Function.Surjective φR) (hd : Descends E) (hq : QuotCrys PD LL) (ht : TensorCrys PD LL)
    (hU : WachUniqueAt W) (hF : ∀ T : LocLat G Qp LL O, IsCrys PD T.ρ → FreeLetters W T) :
    TensorFor E := by
  classical
  intro T T' T'' hT hT' m hmt
  obtain ⟨μ, hμ⟩ := exists_mul E hm hφ hd m hmt
  obtain ⟨⟨b₀, hb₀⟩, -⟩ := hF T hT
  obtain ⟨⟨b₀', hb₀'⟩, -⟩ := hF T' hT'
  obtain ⟨e, b, heb⟩ := exists_bases hb₀
  obtain ⟨e', b', heb'⟩ := exists_bases hb₀'
  obtain ⟨e'', he''⟩ := exists_basis_mul E hm m μ hμ e e'
  have hφμ : ∀ x y, W.φD T'' (μ x y) = μ (W.φD T x) (W.φD T' y) := fun x y => by
    apply E.jD_inj
    rw [E.jD_φ, hμ, hμ, E.jD_φ, E.jD_φ]
    exact map_mulL RW m.toLinearMap φR LinearMap.id LinearMap.id LinearMap.id (fun _ _ => rfl) _ _
  have hγμ : ∀ (g : W.Gam) x y, W.γD T'' g (μ x y) = μ (W.γD T g x) (W.γD T' g y) := fun g x y => by
    obtain ⟨g, rfl⟩ := W.resΓ_onto g
    apply E.jD_inj
    rw [E.jD_act, hμ, hμ, E.jD_act, E.jD_act]
    exact map_mulL RW m.toLinearMap (gR g) (T.actT g) (T'.actT g) (T''.actT g) (hmt g) _ _
  have hA₁ : ∀ (a : LetA O n) x y, μ (a • x) y = a • μ x y := fun a x y => by
    rw [← algebraMap_smul W.EE a x, map_smul, LinearMap.smul_apply, algebraMap_smul]
  have hA₂ : ∀ (a : LetA O n) x y, μ x (a • y) = a • μ x y := fun a x y => by
    rw [← algebraMap_smul W.EE a y, map_smul, algebraMap_smul]
  let ν₀ : ↥(W.N T) ⊗[LetA O n] ↥(W.N T') →ₗ[LetA O n] W.DD T'' :=
    TensorProduct.lift (LinearMap.mk₂ (LetA O n) (fun x y => μ (x : W.DD T) (y : W.DD T'))
      (fun x x' y => by simp) (fun a x y => hA₁ a x y) (fun x y y' => by simp)
      (fun a x y => hA₂ a x y))
  have hν₀ : ∀ x y, ν₀ (x ⊗ₜ y) = μ (x : W.DD T) (y : W.DD T') := fun x y => rfl
  have hνb : ∀ p, ν₀ (b.tensorProduct b' p) = e'' p := fun p => by
    rw [Module.Basis.tensorProduct_apply', hν₀, he'', heb, heb']
  have hinj : Function.Injective ν₀ := by
    have h1 : LinearIndependent (LetA O n) e'' := e''.linearIndependent.restrict_scalars (by
      simpa [Algebra.smul_def] using W.EE_inj)
    have h2 : ν₀ = (b.tensorProduct b').constr (LetA O n) e'' :=
      (b.tensorProduct b').ext fun p => by rw [hνb, Module.Basis.constr_basis]
    rw [h2]
    exact (b.tensorProduct b').injective_constr_of_linearIndependent h1
  have hmem : ∀ x ∈ W.N T, ∀ y ∈ W.N T', μ x y ∈ LinearMap.range ν₀ :=
    fun x hx y hy => ⟨(⟨x, hx⟩ : ↥(W.N T)) ⊗ₜ (⟨y, hy⟩ : ↥(W.N T')), rfl⟩
  have hγmem : ∀ (g : W.Gam), ∀ z ∈ LinearMap.range ν₀, W.γD T'' g z ∈ LinearMap.range ν₀ := by
    rintro g _ ⟨w, rfl⟩
    induction w using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => rw [map_add, map_add]; exact Submodule.add_mem _ hx hy
    | tmul x y => rw [hν₀, hγμ]; exact hmem _ (W.N_Γ T g x x.2) _ (W.N_Γ T' g y y.2)
  have hN : LinearMap.range ν₀ = W.N T'' := by
    refine hU T'' (isCrys_tensor hq ht hT hT' m hmt) _ ?_ ?_ ?_ ?_
    · exact ⟨_, (b.tensorProduct b').map (LinearEquiv.ofInjective ν₀ hinj), e'',
        fun p => (hνb p).symm⟩
    · apply Set.Subset.antisymm
      · rintro _ ⟨x, hx, rfl⟩
        exact hγmem W.gam x hx
      · intro x hx
        refine ⟨W.γD T'' W.gam⁻¹ x, hγmem _ x hx, ?_⟩
        change W.γD T'' W.gam (W.γD T'' W.gam⁻¹ x) = x
        rw [← W.γD_mul, mul_inv_cancel, W.γD_one]
    · rintro _ ⟨w, rfl⟩
      induction w using TensorProduct.induction_on with
      | zero => exact ⟨0, Submodule.zero_mem _, by simp⟩
      | add x y hx hy =>
        obtain ⟨u, hu, hu'⟩ := hx
        obtain ⟨u', hv, hv'⟩ := hy
        refine ⟨u + u', Submodule.add_mem _ hu hv, ?_⟩
        rw [map_add, map_add, smul_add, ← hu', ← hv']
        abel
      | tmul x y =>
        obtain ⟨x', hx', h1⟩ := W.N_π T W.gam x x.2
        obtain ⟨y', hy', h2⟩ := W.N_π T' W.gam y y.2
        refine ⟨μ x' (W.γD T' W.gam y) + μ x y',
          Submodule.add_mem _ (hmem _ hx' _ (W.N_Γ T' _ y y.2)) (hmem _ x.2 _ hy'), ?_⟩
        rw [hν₀, smul_add, ← hA₁, ← hA₂, ← h1, ← h2, LocWach.γ, hγμ]
        simp only [map_sub, LinearMap.sub_apply]
        abel
    · apply le_antisymm
      · apply invSub_le
        apply Submodule.span_le.mpr
        rintro _ ⟨_, ⟨w, rfl⟩, rfl⟩
        induction w using TensorProduct.induction_on with
        | zero => simp
        | add x y hx hy => rw [map_add, map_add]; exact Submodule.add_mem _ hx hy
        | tmul x y =>
          obtain ⟨k, hk⟩ := W.N_φ T x x.2
          obtain ⟨k', hk'⟩ := W.N_φ T' y y.2
          refine ⟨k + k', ?_⟩
          rw [hν₀, hφμ, pow_add, mul_smul, ← hA₂, ← hA₁]
          exact hmem _ hk _ hk'
      · apply invSub_le
        rintro _ ⟨w, rfl⟩
        induction w using TensorProduct.induction_on with
        | zero => simp
        | add x y hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
        | tmul x y =>
          obtain ⟨k, hk⟩ := W.N_φinv T x x.2
          obtain ⟨k', hk'⟩ := W.N_φinv T' y y.2
          refine ⟨k + k', ?_⟩
          rw [hν₀, pow_add, mul_smul, ← hA₂, ← hA₁]
          have key : ∀ u ∈ Submodule.span (LetA O n) (W.φD T '' (W.N T : Set (W.DD T))),
              ∀ u' ∈ Submodule.span (LetA O n) (W.φD T' '' (W.N T' : Set (W.DD T'))),
              μ u u' ∈ phiSpan W T'' (LinearMap.range ν₀) := by
            intro u hu u' hu'
            induction hu using Submodule.span_induction with
            | zero => simp
            | add x y _ _ hx hy => rw [map_add, LinearMap.add_apply]; exact Submodule.add_mem _ hx hy
            | smul a x _ hx => rw [hA₁]; exact Submodule.smul_mem _ _ hx
            | mem u hu =>
              induction hu' using Submodule.span_induction with
              | zero => simp
              | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
              | smul a x _ hx => rw [hA₂]; exact Submodule.smul_mem _ _ hx
              | mem u' hu' =>
                obtain ⟨x, hx, rfl⟩ := hu
                obtain ⟨y, hy, rfl⟩ := hu'
                exact Submodule.subset_span ⟨μ x y, hmem _ hx _ hy, hφμ x y⟩
          exact key _ hk _ hk'
  refine ⟨μ, hμ, ?_, hφμ, hγμ,
    (LinearEquiv.ofInjective ν₀ hinj).trans (LinearEquiv.ofEq _ _ hN), fun x y => rfl⟩
  have : TensorProduct.lift μ = ((e.tensorProduct e').equiv e'' (Equiv.refl _)).toLinearMap :=
    (e.tensorProduct e').ext fun p => by
      rw [LinearEquiv.coe_coe, Module.Basis.equiv_apply, Module.Basis.tensorProduct_apply',
        TensorProduct.lift.tmul, Equiv.refl_apply, he'']
  rw [this]
  exact LinearEquiv.bijective _

end GlobalTheory.WachTensor
