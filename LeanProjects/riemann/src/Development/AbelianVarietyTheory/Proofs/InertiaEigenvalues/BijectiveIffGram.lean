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
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBasisMul

noncomputable section

namespace GlobalTheory.WachTensor

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.UnitDualParts GlobalTheory.EtaleExact
open GlobalTheory.IndefiniteRowSideFullHecke.CrystallineSubrepresentation (QuotCrys TensorCrys DualCrys)
open GlobalTheory.IndefiniteRowSideFullHecke.GammaStableInverse GlobalTheory.IndefiniteRowSideFullHecke.WachLettersFreeness

theorem bijective_iff_gram {R M M' : Type} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup M'] [Module R M'] {ι : Type} [Fintype ι] [DecidableEq ι]
    (b : M →ₗ[R] M' →ₗ[R] R) (t : Module.Basis ι R M) (t' : Module.Basis ι R M') :
    Function.Bijective b ↔ IsUnit (Matrix.of fun i j => b (t j) (t' i)).det := by
  have h : LinearMap.toMatrix t t'.dualBasis b = Matrix.of fun i j => b (t j) (t' i) := by
    ext i j
    simp [LinearMap.toMatrix_apply]
  rw [← h]
  constructor
  · intro hb
    exact LinearEquiv.isUnit_det (LinearEquiv.ofBijective b hb) t t'.dualBasis
  · intro hb
    exact (LinearEquiv.ofIsUnitDet hb).bijective

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

theorem flip_bijective {T T' : LocLat G Qp LL O} {Pr : T.V →ₗ[LL] T'.V →ₗ[LL] LL}
    (h : IsDualLat T.L T'.L Pr) : Function.Bijective Pr.flip := by
  have h1 : Function.Injective Pr.flip :=
    (injective_iff_map_eq_zero _).2 fun y hy => h.2.2.1 y fun x => LinearMap.congr_fun hy x
  refine ⟨h1, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).1 h1⟩
  rw [← h.2.2.2.1]
  exact (Subspace.dual_finrank_eq (K := LL) (V := T.V)).symm

theorem isCrys_dual (hq : QuotCrys PD LL) (hdu : DualCrys PD LL) {T T' : LocLat G Qp LL O}
    (hT : IsCrys PD T.ρ) {Pr : T.V →ₗ[LL] T'.V →ₗ[LL] LL} (h : IsDualLat T.L T'.L Pr) :
    IsCrys PD T'.ρ := by
  let ε := LinearEquiv.ofBijective Pr.flip (flip_bijective h)
  refine hq _ T.ρ.dual _ T'.ρ ε.symm.toLinearMap ?_ ε.symm.surjective (hdu _ _ hT)
  intro g f
  obtain ⟨y, rfl⟩ := ε.surjective f
  rw [LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_eq]
  ext x
  change Pr (T.ρ g⁻¹ x) y = Pr x (T'.ρ g y)
  rw [← h.1 g, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]

theorem exists_intPair [IsFractionRing O LL] {T T' : LocLat G Qp LL O}
    {Pr : T.V →ₗ[LL] T'.V →ₗ[LL] LL} (h : IsDualLat T.L T'.L Pr) :
    ∃ β : ↥T.L.T →ₗ[O] ↥T'.L.T →ₗ[O] O,
      (∀ (x : ↥T.L.T) (y : ↥T'.L.T), Pr (x : T.V) (y : T'.V) = algebraMap O LL (β x y)) ∧
      Function.Bijective β.flip := by
  have hO := IsFractionRing.injective O LL
  choose f hf using fun (x : ↥T.L.T) (y : ↥T'.L.T) => (h.2.2.2.2 y).1 y.2 x x.2
  let β : ↥T.L.T →ₗ[O] ↥T'.L.T →ₗ[O] O := LinearMap.mk₂ O f
    (fun x x' y => hO (by rw [map_add, ← hf, ← hf, ← hf]; simp))
    (fun c x y => hO (by
      rw [smul_eq_mul, map_mul, ← hf, ← hf, Submodule.coe_smul, ← algebraMap_smul LL c]
      simp [Algebra.smul_def]))
    (fun x y y' => hO (by rw [map_add, ← hf, ← hf, ← hf]; simp))
    (fun c x y => hO (by
      rw [smul_eq_mul, map_mul, ← hf, ← hf, Submodule.coe_smul, ← algebraMap_smul LL c]
      simp [Algebra.smul_def]))
  have hβ : ∀ x y, β x y = f x y := fun _ _ => rfl
  refine ⟨β, hf, (injective_iff_map_eq_zero _).2 fun y hy => ?_, fun u => ?_⟩
  · apply Subtype.ext
    apply (flip_bijective h).1
    refine ext_lat T fun x => ?_
    have h1 : β x y = 0 := LinearMap.congr_fun hy x
    rw [LinearMap.flip_apply, hf, ← hβ, h1]
    simp
  · obtain ⟨u', hu'⟩ := exists_extend T (Algebra.linearMap O LL ∘ₗ u)
    obtain ⟨y, hy⟩ := (flip_bijective h).2 u'
    have h1 : ∀ x : ↥T.L.T, Pr x y = algebraMap O LL (u x) := fun x =>
      (LinearMap.congr_fun hy x).trans (hu' x)
    refine ⟨⟨y, (h.2.2.2.2 y).2 fun x hx => ⟨_, h1 ⟨x, hx⟩⟩⟩, LinearMap.ext fun x => hO ?_⟩
    rw [LinearMap.flip_apply, hβ, ← hf, h1]

theorem exists_pair (hm : ∀ m : Ideal W.EE, m.IsMaximal → m.map E.ioE.toRingHom ≠ ⊤)
    (hφ : Function.Surjective φR) (hd : Descends E) {T T' : LocLat G Qp LL O}
    (β : ↥T.L.T →ₗ[O] ↥T'.L.T →ₗ[O] O) (hβ : ∀ g x y, β (T.actT g x) (T'.actT g y) = β x y) :
    ∃ b : W.DD T →ₗ[W.EE] W.DD T' →ₗ[W.EE] W.EE,
      ∀ x y, E.ioE (b x y) = pairL RW β (E.jD T x) (E.jD T' y) := by
  obtain ⟨e⟩ := exists_basis_DD E T
  obtain ⟨e'⟩ := exists_basis_DD E T'
  obtain ⟨U, hU⟩ := exists_frob_mat E hm hφ T e
  obtain ⟨U', hU'⟩ := exists_frob_mat E hm hφ T' e'
  have hact : ∀ (g : G) (x : TW RW T) (y : TW RW T'), gR g (pairL RW β x y) =
      pairL RW β (TWact (gR g) T g x) (TWact (gR g) T' g y) := fun g x y =>
    map_pairL RW β (gR g) (T.actT g) (T'.actT g) (hβ g) x y
  have hfr : ∀ (x : TW RW T) (y : TW RW T'), φR (pairL RW β x y) =
      pairL RW β (TWmap φR T x) (TWmap φR T' y) := fun x y =>
    map_pairL RW β φR LinearMap.id LinearMap.id (fun _ _ => rfl) x y
  generalize pairL RW β = b at hact hfr ⊢
  have key := hd (Fin (Module.finrank O ↥T.L.T) × Fin (Module.finrank O ↥T'.L.T))
    (fun p q => U p.1 q.1 * U' p.2 q.2) (fun p => b (E.jD T (e p.1)) (E.jD T' (e' p.2)))
    (fun g hg p => by simp only [hact, jD_fixed E T g hg, jD_fixed E T' g hg])
    (fun p => by
      simp only [hfr, map_mul, ← smul_eq_mul (α := RW) (_ * _)]
      rw [← bil_expand b (fun b => E.ioE (U p.1 b))
        (fun b => TWmap φR T (E.jD T (e b))) (fun b => E.ioE (U' p.2 b))
        (fun b => TWmap φR T' (E.jD T' (e' b))), ← hU, ← hU'])
  exact exists_descend E.ioE (E.jD T).toAddMonoidHom (E.jD T').toAddMonoidHom
    E.ioE.toRingHom.toAddMonoidHom (E.jD_smul T) (E.jD_smul T') (fun a x => map_mul E.ioE a x)
    (ioE_injective E) b e e' fun a c => key (a, c)

theorem pair_perfect (hm : ∀ m : Ideal W.EE, m.IsMaximal → m.map E.ioE.toRingHom ≠ ⊤)
    {T T' : LocLat G Qp LL O} (β : ↥T.L.T →ₗ[O] ↥T'.L.T →ₗ[O] O) (hβ : Function.Bijective β.flip)
    (b : W.DD T →ₗ[W.EE] W.DD T' →ₗ[W.EE] W.EE)
    (hb : ∀ x y, E.ioE (b x y) = pairL RW β (E.jD T x) (E.jD T' y)) :
    Function.Bijective b ∧ Function.Bijective b.flip := by
  classical
  haveI : Nontrivial O := (algebraMap O LL).domain_nontrivial
  haveI := T.L.free
  haveI : Module.Finite O ↥T.L.T := Module.Finite.iff_fg.2 T.L.fg
  let t := Module.finBasis O ↥T.L.T
  let t' := t.dualBasis.map (LinearEquiv.ofBijective β.flip hβ).symm
  have htt : ∀ i j, β (t j) (t' i) = if i = j then 1 else 0 := fun i j => by
    have : β.flip (t' i) = t.dualBasis i :=
      (LinearEquiv.ofBijective β.flip hβ).apply_symm_apply _
    rw [← LinearMap.flip_apply β, this, Module.Basis.dualBasis_apply_self]
    simp only [eq_comm]
  have hr : Module.finrank O ↥T'.L.T = Module.finrank O ↥T.L.T := by
    rw [Module.finrank_eq_card_basis t', Fintype.card_fin]
  have h1 : Function.Bijective (pairL RW β) := by
    rw [bijective_iff_gram _ (Algebra.TensorProduct.basis RW t) (Algebra.TensorProduct.basis RW t')]
    have : (Matrix.of fun i j => pairL RW β (Algebra.TensorProduct.basis RW t j)
        (Algebra.TensorProduct.basis RW t' i)) = 1 := by
      ext i j
      simp [Algebra.TensorProduct.basis_apply, pairL_tmul, htt, Matrix.one_apply]
    rw [this, Matrix.det_one]
    exact isUnit_one
  obtain ⟨e⟩ := exists_basis_DD E T
  obtain ⟨e₁⟩ := exists_basis_DD E T'
  let e' := e₁.reindex (finCongr hr)
  obtain ⟨c, hc⟩ := exists_basis_jD E T e
  obtain ⟨c', hc'⟩ := exists_basis_jD E T' e'
  rw [bijective_iff_gram _ c c'] at h1
  have h2 : IsUnit (Matrix.of fun i j => b (e j) (e' i)).det := by
    by_contra hn
    obtain ⟨m, hmax, hle⟩ := exists_max_ideal_of_mem_nonunits hn
    refine hm m hmax (Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ hle) ?_)
    rw [RingHom.map_det]
    convert h1 using 2
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, hc, hc', ← hb]
    rfl
  refine ⟨(bijective_iff_gram b e e').2 h2, (bijective_iff_gram b.flip e' e).2 ?_⟩
  rw [← Matrix.det_transpose] at h2
  exact h2

theorem isUnit_or_smul_pi (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (x : W.DD T) :
    ∃ y : W.DD T, x = (letπ : LetA O n) • y := by
  obtain ⟨u, hu⟩ := W.EE_π.exists_right_inv
  exact ⟨u • x, by rw [← algebraMap_smul W.EE letπ, smul_smul, hu, one_smul]⟩

theorem dualFor [IsFractionRing O LL]
    (hm : ∀ m : Ideal W.EE, m.IsMaximal → m.map E.ioE.toRingHom ≠ ⊤)
    (hφ : Function.Surjective φR) (hd : Descends E) (hq : QuotCrys PD LL) (hdu : DualCrys PD LL)
    (hU : WachUniqueAt W) (hF : ∀ T : LocLat G Qp LL O, IsCrys PD T.ρ → FreeLetters W T) :
    DualFor E := by
  classical
  intro T T' hT Pr hPr
  have hO := IsFractionRing.injective O LL
  obtain ⟨β, hβ, hβb⟩ := exists_intPair hPr
  have hβg : ∀ g x y, β (T.actT g x) (T'.actT g y) = β x y := fun g x y => hO (by
    rw [← hβ, ← hβ]; exact hPr.1 g x y)
  obtain ⟨b, hb⟩ := exists_pair E hm hφ hd β hβg
  obtain ⟨hb1, hb2⟩ := pair_perfect E hm β hβb b hb
  have hφb : ∀ x y, b (W.φD T x) (W.φD T' y) = W.φE (b x y) := fun x y => by
    apply ioE_injective E
    rw [ioE_φE E hO, hb, hb, E.jD_φ, E.jD_φ]
    exact (map_pairL RW β φR LinearMap.id LinearMap.id (fun _ _ => rfl) _ _).symm
  have hγb : ∀ (g : W.Gam) x y, b (W.γD T g x) (W.γD T' g y) = W.γE g (b x y) := fun g x y => by
    obtain ⟨g, rfl⟩ := W.resΓ_onto g
    apply ioE_injective E
    rw [ioE_γE E hO, hb, hb, E.jD_act, E.jD_act]
    exact (map_pairL RW β (gR g) (T.actT g) (T'.actT g) (hβg g) _ _).symm
  obtain ⟨⟨b₀, hb₀⟩, -⟩ := hF T hT
  obtain ⟨e, c, hec⟩ := exists_bases hb₀
  obtain ⟨e', hee⟩ : ∃ e' : Module.Basis (Fin (Module.finrank O ↥T.L.T)) W.EE (W.DD T'),
      ∀ x i, b x (e' i) = e.repr x i := by
    refine ⟨e.dualBasis.map (LinearEquiv.ofBijective b.flip hb2).symm, fun x i => ?_⟩
    have : b.flip (e.dualBasis.map (LinearEquiv.ofBijective b.flip hb2).symm i) = e.dualBasis i :=
      (LinearEquiv.ofBijective b.flip hb2).apply_symm_apply _
    rw [← LinearMap.flip_apply b, this, Module.Basis.dualBasis_apply]
  have hA₁ : ∀ (a : LetA O n) x y, b (a • x) y = algebraMap _ W.EE a * b x y := fun a x y => by
    rw [← algebraMap_smul W.EE a x, map_smul, LinearMap.smul_apply, smul_eq_mul]
  have hA₂ : ∀ (a : LetA O n) x y, b x (a • y) = algebraMap _ W.EE a * b x y := fun a x y => by
    rw [← algebraMap_smul W.EE a y, map_smul, smul_eq_mul]

  let δ₀ : Module.Dual (LetA O n) ↥(W.N T) →ₗ[LetA O n] W.DD T' := c.dualBasis.constr (LetA O n) e'
  have hδe : ∀ i, δ₀ (c.dualBasis i) = e' i := fun i => Module.Basis.constr_basis _ _ _ _
  have hinj : Function.Injective δ₀ :=
    c.dualBasis.injective_constr_of_linearIndependent
      (e'.linearIndependent.restrict_scalars (by simpa [Algebra.smul_def] using W.EE_inj))
  have hsum : ∀ f, δ₀ f = ∑ i, f (c i) • e' i := fun f => by
    simp [δ₀, Module.Basis.constr_apply_fintype]
  have hci : ∀ i y, e'.repr y i = b (c i) y := fun i y => by
    conv_rhs => rw [← e'.sum_repr y, ← hec]
    simp only [map_sum, map_smul, hee, e.repr_self, Finsupp.single_apply, smul_eq_mul]
    simp
  have hδ : ∀ (x : ↥(W.N T)) f, b x (δ₀ f) = algebraMap _ W.EE (f x) := fun x f => by
    conv_lhs => rw [← c.sum_repr x]
    conv_rhs => rw [← c.sum_repr x]
    simp only [Submodule.coe_sum, Submodule.coe_smul, map_sum, LinearMap.sum_apply, hA₁, map_smul,
      smul_eq_mul, map_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hsum]
    simp [map_sum, hA₂, hee, ← hec, Finsupp.single_apply]
  have hbas : ∀ y, (∀ i, ∃ a : LetA O n, b (c i) y = algebraMap _ W.EE a) →
      y ∈ LinearMap.range δ₀ := by
    intro y hy
    choose a ha using hy
    rw [← e'.sum_repr y]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [hci, ha, algebraMap_smul]
    exact Submodule.smul_mem _ _ ⟨_, hδe i⟩
  have hiff : ∀ y, y ∈ LinearMap.range δ₀ ↔
      ∀ x ∈ W.N T, ∃ a : LetA O n, b x y = algebraMap _ W.EE a := fun y =>
    ⟨by rintro ⟨f, rfl⟩ x hx; exact ⟨_, hδ ⟨x, hx⟩ f⟩, fun h => hbas y fun i => h _ (c i).2⟩
  have hγinv : ∀ (g : W.Gam) x, W.γD T g (W.γD T g⁻¹ x) = x := fun g x => by
    rw [← W.γD_mul, mul_inv_cancel, W.γD_one]
  have hγmem : ∀ (g : W.Gam), ∀ z ∈ LinearMap.range δ₀, W.γD T' g z ∈ LinearMap.range δ₀ := by
    intro g z hz
    rw [hiff] at hz ⊢
    intro x hx
    obtain ⟨a, ha⟩ := hz _ (W.N_Γ T g⁻¹ x hx)
    exact ⟨_, by rw [← hγinv g x, hγb, ha, W.γE_ext]⟩
  have hN : LinearMap.range δ₀ = W.N T' := by
    refine hU T' (isCrys_dual hq hdu hT hPr) _ ?_ ?_ ?_ ?_
    · exact ⟨_, c.dualBasis.map (LinearEquiv.ofInjective δ₀ hinj), e', fun p => (hδe p).symm⟩
    · apply Set.Subset.antisymm
      · rintro _ ⟨x, hx, rfl⟩
        exact hγmem W.gam x hx
      · intro x hx
        refine ⟨W.γD T' W.gam⁻¹ x, hγmem _ x hx, ?_⟩
        change W.γD T' W.gam (W.γD T' W.gam⁻¹ x) = x
        rw [← W.γD_mul, mul_inv_cancel, W.γD_one]
    · intro y hy
      obtain ⟨y', hy'⟩ := isUnit_or_smul_pi W T' (W.γ T' y - y)
      refine ⟨y', (hiff y').2 fun x hx => ?_, hy'⟩
      rw [hiff] at hy
      obtain ⟨x', hx', h1⟩ := W.N_π T W.gam⁻¹ x hx
      obtain ⟨a, ha⟩ := hy _ (W.N_Γ T W.gam⁻¹ x hx)
      obtain ⟨a', ha'⟩ := hy _ hx'
      obtain ⟨d, hd⟩ := γA_sub W W.gam a
      refine ⟨d + a', W.EE_π.mul_left_cancel ?_⟩
      have h2 : b x (W.γ T' y) = algebraMap _ W.EE (W.γA W.gam a) := by
        rw [← hγinv W.gam x, LocWach.γ, hγb, ha, W.γE_ext]; rfl
      have h3 : algebraMap _ W.EE a - b x y =
          algebraMap (LetA O n) W.EE letπ * algebraMap _ W.EE a' := by
        rw [← ha, ← ha', ← hA₁, ← h1, map_sub, LinearMap.sub_apply]
      have h4 := congrArg (algebraMap _ W.EE) hd
      rw [map_sub, map_mul] at h4
      rw [← hA₂, ← hy', map_sub, h2, map_add]
      linear_combination h4 + h3
    · apply le_antisymm
      · apply invSub_le
        apply Submodule.span_le.mpr
        rintro _ ⟨y, hy, rfl⟩
        choose k hk using fun i => W.N_φinv T (c i) (c i).2
        have key : ∀ u ∈ Submodule.span (LetA O n) (W.φD T '' (W.N T : Set (W.DD T))),
            ∃ a : LetA O n, b u (W.φD T' y) = algebraMap _ W.EE a := by
          intro u hu
          induction hu using Submodule.span_induction with
          | zero => exact ⟨0, by simp⟩
          | add x y _ _ hx hy =>
            obtain ⟨a, ha⟩ := hx
            obtain ⟨a', ha'⟩ := hy
            exact ⟨a + a', by rw [map_add, LinearMap.add_apply, ha, ha', map_add]⟩
          | smul a x _ hx =>
            obtain ⟨a', ha'⟩ := hx
            exact ⟨a * a', by rw [hA₁, ha', map_mul]⟩
          | mem u hu =>
            obtain ⟨x, hx, rfl⟩ := hu
            obtain ⟨a, ha⟩ := (hiff y).1 hy x hx
            exact ⟨_, by rw [hφb, ha, W.φE_ext]⟩
        refine ⟨∑ i, k i, hbas _ fun i => ?_⟩
        obtain ⟨r, hr⟩ := Nat.exists_eq_add_of_le'
          (Finset.single_le_sum (f := k) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i))
        rw [hA₂, ← hA₁, hr, pow_add, mul_smul]
        exact key _ (Submodule.smul_mem _ _ (hk i))
      · apply invSub_le
        intro y hy
        have h1 : y = ∑ i, b (W.φD T (e i)) y • W.φD T' (e' i) := by
          apply hb2.1
          refine LinearMap.ext_on_range (exists_frob_inv E hm hφ T e) fun j => ?_
          simp [map_sum, hφb, hee, Finsupp.single_apply, apply_ite W.φE]
        rw [h1]
        refine Submodule.sum_mem _ fun i _ => ?_
        obtain ⟨k, hk⟩ := W.N_φ T (c i) (c i).2
        obtain ⟨a, ha⟩ := (hiff y).1 hy _ hk
        refine ⟨k, ?_⟩
        rw [hA₁, ← hec] at ha
        have h2 : W.Q ^ k • b (W.φD T (e i)) y • W.φD T' (e' i) = a • W.φD T' (e' i) := by
          rw [← algebraMap_smul W.EE (W.Q ^ k), smul_smul, ← algebraMap_smul W.EE a, ← ha]
          rfl
        rw [h2]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨e' i, ⟨_, hδe i⟩, rfl⟩)
  refine ⟨β, b, hβ, hb, hb1, hb2, hφb, hγb, fun y => by rw [← hN]; exact hiff y,
    ((LinearEquiv.ofInjective δ₀ hinj).trans (LinearEquiv.ofEq _ _ hN)).symm, fun x y => ?_⟩
  obtain ⟨f, rfl⟩ := ((LinearEquiv.ofInjective δ₀ hinj).trans (LinearEquiv.ofEq _ _ hN)).surjective y
  rw [LinearEquiv.symm_apply_apply]
  exact hδ x f

end GlobalTheory.WachTensor
