import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardLeOfSpan

open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps GlobalTheory.Present GlobalTheory.RedFun Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped LaurentSeries PowerSeries TensorProduct

noncomputable section

namespace GlobalTheory.RedDim

theorem count {F M N : Type} [Field F] [AddCommGroup M] [Module F M] [AddCommGroup N] [Module F N]
    (g : M →ₗ[F] N) {r m s : ℕ} (v : Fin r → M) (V' : Submodule F M)
    (hle : V' ≤ Submodule.span F (Set.range v)) (hk : V' ≤ LinearMap.ker g) (hr : r ≤ m + s)
    (hm : m ≤ Module.finrank F ((Submodule.span F (Set.range v)).map g)) (hs : s ≤ Module.finrank F V') :
    Module.finrank F ((Submodule.span F (Set.range v)).map g) = m ∧
      Submodule.span F (Set.range v) ⊓ LinearMap.ker g = V' ∧ LinearIndependent F v := by
  set V := Submodule.span F (Set.range v) with hV
  haveI : FiniteDimensional F V := FiniteDimensional.span_of_finite F (Set.finite_range v)
  have h1 : Module.finrank F V ≤ r := (finrank_range_le_card (R := F) v).trans (Fintype.card_fin r).le
  have h2 := (g.domRestrict V).finrank_range_add_finrank_ker
  rw [LinearMap.range_domRestrict, LinearMap.ker_domRestrict,
    ← Submodule.finrank_map_subtype_eq, Submodule.map_comap_subtype] at h2
  haveI : FiniteDimensional F ↥(V ⊓ LinearMap.ker g) := Submodule.finiteDimensional_of_le inf_le_left
  have h3 : V' ≤ V ⊓ LinearMap.ker g := le_inf hle hk
  have h4 := Submodule.finrank_mono h3
  refine ⟨by omega, (Submodule.eq_of_le_of_finrank_le h3 (by omega)).symm, ?_⟩
  rw [linearIndependent_iff_card_eq_finrank_span]
  change Fintype.card (Fin r) = Module.finrank F V
  rw [Fintype.card_fin]
  omega

section Abs

variable {F R EE : Type} [Field F] [CommRing R] [CommRing EE] (κ : F →+* R) (ρ : EE →+* R) (ε : R)

theorem mem_img (h1 : ∀ c, ∃ e, ε * κ c = ε * ρ e) {D N : Type} [AddCommGroup D] [Module EE D]
    [AddCommGroup N] [Module R N] [Module F N] (hκ : ∀ (c : F) (x : N), c • x = κ c • x)
    (J : D →+ N) (hJ : ∀ (e : EE) x, J (e • x) = ρ e • J x) {y : N}
    (hy : y ∈ Submodule.span F (Set.range fun x => ε • J x)) : ∃ x, y = ε • J x := by
  induction hy using Submodule.span_induction with
  | mem y hy => obtain ⟨x, rfl⟩ := hy; exact ⟨x, rfl⟩
  | zero => exact ⟨0, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨x, rfl⟩ := hy; obtain ⟨x', rfl⟩ := hz
    exact ⟨x + x', by simp⟩
  | smul c y _ hy =>
    obtain ⟨x, rfl⟩ := hy
    obtain ⟨e, he⟩ := h1 c
    exact ⟨e • x, by rw [hκ, hJ, smul_smul, smul_smul, mul_comm, he]⟩

theorem le_finrank {N : Type} [AddCommGroup N] [Module R N] [Module F N]
    (hκ : ∀ (c : F) (x : N), c • x = κ c • x) {D : Type} (w : D → N) (V : Submodule F N)
    [FiniteDimensional F V] (hw : ∀ x, w x ∈ V) {m : ℕ}
    (h : ∀ (t : ℕ) (u : Fin t → N), (∀ x, w x ∈ Submodule.span R (Set.range u)) → m ≤ t) :
    m ≤ Module.finrank F V := by
  let b := Module.finBasis F V
  refine h _ (fun j => (b j : N)) fun x => ?_
  have := congrArg Subtype.val (b.sum_repr ⟨w x, hw x⟩)
  simp only [Submodule.coe_sum, Submodule.coe_smul] at this
  rw [← this]
  refine Submodule.sum_mem _ fun j _ => ?_
  rw [hκ]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

theorem abs_main (h1 : ∀ c, ∃ e, ε * κ c = ε * ρ e) (h2 : ∀ e, ∃ c, ε * ρ e = ε * κ c)
    {D D' M N : Type} [AddCommGroup D] [Module EE D] [AddCommGroup D'] [Module EE D']
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (J : D →+ M) (hJ : ∀ (e : EE) x, J (e • x) = ρ e • J x) (φ : D' →ₗ[EE] D) (g : M →ₗ[R] N)
    {r m s : ℕ} (b : Module.Basis (Fin r) EE D) (hg : ∀ y, g (J (φ y)) = 0) (hr : r ≤ m + s)
    (hm : ∀ (t : ℕ) (u : Fin t → N), (∀ x, ε • g (J x) ∈ Submodule.span R (Set.range u)) → m ≤ t)
    (hs : ∀ (t : ℕ) (u : Fin t → M), (∀ y, ε • J (φ y) ∈ Submodule.span R (Set.range u)) → s ≤ t) :
    (∃ u : Fin m → D, ∀ x, ∃ c : Fin m → F, ε • g (J x) = ∑ j, κ (c j) • ε • g (J (u j))) ∧
      ∀ x, ε • g (J x) = 0 → ∃ y, ∀ j, ε * ρ (b.repr (x - φ y) j) = 0 := by
  letI : Module F M := Module.compHom M κ
  letI : Module F N := Module.compHom N κ
  have hM : ∀ (c : F) (x : M), c • x = κ c • x := fun _ _ => rfl
  have hN : ∀ (c : F) (x : N), c • x = κ c • x := fun _ _ => rfl
  let gF : M →ₗ[F] N :=
    { toFun := g, map_add' := g.map_add, map_smul' := fun c x => g.map_smul (κ c) x }
  have hgF : ∀ x, gF x = g x := fun _ => rfl
  let v : Fin r → M := fun j => ε • J (b j)
  choose cc hcc using h2
  have hexp : ∀ x, ε • J x = ∑ j, cc (b.repr x j) • v j := by
    intro x
    conv_lhs => rw [← b.sum_repr x, map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hJ, hM, smul_smul, hcc, smul_smul, mul_comm]
  have hmem : ∀ x, ε • J x ∈ Submodule.span F (Set.range v) := fun x => by
    rw [hexp]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  have hback : ∀ y ∈ Submodule.span F (Set.range v), ∃ x, y = ε • J x := fun y hy =>
    mem_img κ ρ ε h1 hM J hJ (Submodule.span_mono (by rintro _ ⟨j, rfl⟩; exact ⟨b j, rfl⟩) hy)
  let J' : D' →+ M := J.comp φ.toAddMonoidHom
  let V' := Submodule.span F (Set.range fun y => ε • J' y)
  have hle : V' ≤ Submodule.span F (Set.range v) :=
    Submodule.span_le.2 (by rintro _ ⟨y, rfl⟩; exact hmem _)
  have hk : V' ≤ LinearMap.ker gF := Submodule.span_le.2 (by
    rintro _ ⟨y, rfl⟩
    change g (ε • J (φ y)) = 0
    rw [map_smul, hg, smul_zero])
  haveI : FiniteDimensional F (Submodule.span F (Set.range v)) :=
    FiniteDimensional.span_of_finite F (Set.finite_range v)
  haveI : FiniteDimensional F V' := Submodule.finiteDimensional_of_le hle
  have hmem' : ∀ x, ε • g (J x) ∈ (Submodule.span F (Set.range v)).map gF := fun x =>
    ⟨_, hmem x, by rw [hgF, map_smul]⟩
  obtain ⟨e1, e2, e3⟩ := count gF v V' hle hk hr
    (le_finrank κ hN (fun x => ε • g (J x)) _ hmem' hm)
    (le_finrank κ hM (fun y => ε • J (φ y)) V' (fun y => Submodule.subset_span (Set.mem_range_self y)) hs)
  constructor
  · let c := Module.finBasisOfFinrankEq F _ e1
    have hu : ∀ j, ∃ x, (c j : N) = ε • g (J x) := fun j => by
      obtain ⟨y, hy, e⟩ := (c j).2
      obtain ⟨x, rfl⟩ := hback y hy
      exact ⟨x, by rw [← e, hgF, map_smul]⟩
    choose u hu using hu
    refine ⟨u, fun x => ⟨fun j => c.repr ⟨_, hmem' x⟩ j, ?_⟩⟩
    have := congrArg Subtype.val (c.sum_repr ⟨_, hmem' x⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul, hu, hN] at this
    exact this.symm
  · intro x hx
    have h3 : ε • J x ∈ V' := by
      rw [← e2]
      exact ⟨hmem x, by change g _ = 0; rw [map_smul, hx]⟩
    obtain ⟨y, hy⟩ := mem_img κ ρ ε h1 hM J' (fun e y => by
      change J (φ (e • y)) = _ • J (φ y); rw [map_smul, hJ]) h3
    refine ⟨y, fun j => ?_⟩
    have h4 : ε • J (x - φ y) = 0 := by rw [map_sub, smul_sub, hy]; exact sub_self _
    rw [hexp] at h4
    rw [hcc, Fintype.linearIndependent_iff.1 e3 _ h4 j, map_zero, mul_zero]

end Abs

section Comparison₂

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {W : LocWach PD LL O v n} {RA RW : Type} [CommRing RA] [CommRing RW] [Algebra O RA]
    [Algebra O RW] {inclR : RA →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : RA}
    (E : EtTie W RA RW inclR φR gR πA) {k : Type} [Field k] [Algebra O k]
    {Rk : Type} [CommRing Rk] [Algebra k Rk] [Algebra O Rk] [IsScalarTower O k Rk] (ρ : RW →ₐ[O] Rk)

theorem le_of_span (i : ZMod n) (h0 : eps E ρ i ≠ 0) (T : LocLat G Qp LL O) {m : ℕ}
    (q : ↥T.L.T →ₗ[O] (Fin m → k)) {s : ℕ} (b : Fin s → (Fin m → k)) (hb : LinearIndependent k b)
    (hq : ∀ j, ∃ x, q x = b j) (t : ℕ) (u : Fin t → Rk ⊗[k] (Fin m → k))
    (hu : ∀ x, eps E ρ i • J E ρ T q x ∈ Submodule.span Rk (Set.range u)) : s ≤ t := by
  refine card_le_of_span (eps_idem E ρ i) h0 u b hb fun j => ?_
  obtain ⟨x, hx⟩ := hq j
  have h1 : Submodule.span Rk (Set.range (J E ρ T q)) ≤
      (Submodule.span Rk (Set.range u)).comap (eps E ρ i • LinearMap.id) :=
    Submodule.span_le.2 (by rintro _ ⟨y, rfl⟩; exact hu y)
  have h2 := h1 (J_span E ρ T q x)
  rw [hx] at h2
  simpa [TensorProduct.smul_tmul'] using h2

end Comparison₂

theorem dim_ker : ∀ {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K] [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K] {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B] [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n) {RA RW : Type} [CommRing RA] [CommRing RW] [Algebra O RA] [Algebra O RW] {inclR : RA →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : RA} (E : EtTie W RA RW inclR φR gR πA) {k : Type} [Field k] [Algebra O k] {Rk : Type} [CommRing Rk] [Algebra k Rk] [Algebra O Rk] [IsScalarTower O k Rk] (ρ : RW →ₐ[O] Rk) (lam : O) (κ : k⸨X⸩ →+* Rk), IsRed E ρ (k := k) lam κ → ∀ (T : LocLat G Qp LL O) (m : ℕ) (q : ↥T.L.T →ₗ[O] (Fin m → k)), Function.Surjective q → ∀ (T' : LocLat G Qp LL O) (f : LatHom T'.L T.L), (∀ x : ↥T.L.T, q x = 0 ↔ ∃ y ∈ T'.L.T, f.f y = x) → ∀ i, (∃ u : Fin m → W.DD T, ∀ x, ∃ c : Fin m → k⸨X⸩, eps E ρ i • J E ρ T q x = ∑ j, κ (c j) • eps E ρ i • J E ρ T q (u j)) ∧ ∀ h : LatHom T.L T'.L, (∀ x, f.f (h.f x) = algebraMap O LL lam • x) → ∀ x, eps E ρ i • J E ρ T q x = 0 → ∃ y, W.map f y = (letE i : LetA O n) • x := by
  intro G _ _ Qp K₀ K _ _ _ _ _ _ _ B BdR _ _ _ _ _ _ _ _ _ _ _ PD LL O _ _ _ _ _ v n W RA RW _ _ _ _
    inclR φR gR πA E k _ _ Rk _ _ _ _ ρ lam κ hR T m q hq T' f hf i
  classical
  haveI : Nontrivial O := (algebraMap O LL).domain_nontrivial
  haveI := T.L.free
  haveI : Module.Finite O ↥T.L.T := Module.Finite.iff_fg.2 T.L.fg
  haveI := (W.DD_free T).1
  haveI := GlobalTheory.EtaleExact.finite_DD E T
  haveI : Nontrivial W.EE := by
    by_contra hn
    rw [not_nontrivial_iff_subsingleton] at hn
    apply hR.eps_ne i
    rw [eps, Subsingleton.elim (algebraMap (LetA O n) W.EE (letE i)) 0, map_zero]
  set r := Module.finrank O ↥T.L.T with hr
  let t : Module.Basis (Fin r) O ↥T.L.T := Module.finBasis O _
  let b : Module.Basis (Fin r) W.EE (W.DD T) := Module.finBasisOfFinrankEq _ _ (W.DD_free T).2
  let qb : ↥T.L.T →ₗ[O] (Fin r → k) := t.constr O fun j => Pi.single j 1
  let g : (Fin r → k) →ₗ[k] (Fin m → k) := (Pi.basisFun k (Fin r)).constr k fun j => q (t j)
  have hgq : ∀ x, q x = g (qb x) := by
    have : q = (g.restrictScalars O) ∘ₗ qb := t.ext fun j => by
      have := (Pi.basisFun k (Fin r)).constr_basis k (fun j => q (t j)) j
      rw [Pi.basisFun_apply] at this
      simp only [LinearMap.comp_apply, qb, Module.Basis.constr_basis, LinearMap.restrictScalars_apply]
      exact this.symm
    intro x
    conv_lhs => rw [this]
    rfl
  have hqb : Function.Surjective qb := by
    intro y
    choose c hc using fun j => hR.res_surj (y j)
    refine ⟨∑ j, c j • t j, ?_⟩
    rw [map_sum]
    funext a
    simp [qb, Finset.sum_apply, Pi.single_apply, Algebra.smul_def, hc]
  have hg : Function.Surjective g := fun y => by
    obtain ⟨x, rfl⟩ := hq y
    exact ⟨_, (hgq x).symm⟩
  have hrk := g.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.2 hg] at hrk
  simp only [finrank_top, Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hrk
  let q' : ↥T'.L.T →ₗ[O] (Fin r → k) := qb ∘ₗ GlobalTheory.EtaleExact.latMap f
  have hJ' : ∀ y, J E ρ T qb (W.map f y) = J E ρ T' q' y := fun y => by
    rw [J_map E ρ f q' qb LinearMap.id (fun x x' e => congrArg qb (Subtype.ext e)), LinearMap.baseChange_id]
    rfl
  have hJ : ∀ x, g.baseChange Rk (J E ρ T qb x) = J E ρ T q x := fun x => (J_comp E ρ T qb q g hgq x).symm
  let cK := Module.finBasis k (LinearMap.ker g)
  obtain ⟨h1, h2⟩ := abs_main κ (rE E ρ) (eps E ρ i) (hR.κ_of i) (hR.of_κ i) (J E ρ T qb) (J_smul E ρ T qb)
    (W.map f) (g.baseChange Rk) (m := m) b (fun y => by
      rw [hJ, J_map E ρ f q' q 0 (fun x x' e => (hf x').2 ⟨x, x.2, e.symm⟩)]
      simp) hrk.ge
    (fun s u hu => le_of_span E ρ i (hR.eps_ne i) T q (Pi.basisFun k (Fin m))
      (Pi.basisFun k (Fin m)).linearIndependent (fun j => hq _) s u (fun x => hJ x ▸ hu x))
    (fun s u hu => le_of_span E ρ i (hR.eps_ne i) T' q' (fun j => (cK j : Fin r → k))
      (cK.linearIndependent.map' (LinearMap.ker g).subtype (Submodule.ker_subtype _)) (fun j => by
        obtain ⟨x, hx⟩ := hqb (cK j)
        obtain ⟨y, hy, e⟩ := (hf x).1 (by rw [hgq, hx]; exact (cK j).2)
        exact ⟨⟨y, hy⟩, hx ▸ congrArg qb (Subtype.ext e)⟩) s u (fun y => hJ' y ▸ hu y))
  simp only [hJ] at h1 h2
  refine ⟨h1, fun h hh x hx => ?_⟩
  obtain ⟨y, hy⟩ := h2 x hx
  choose e he using fun j => hR.ker i _ (hy j)
  have h3 : ∀ z, W.map f (W.map h z) = algebraMap O W.EE lam • z := fun z => by
    have : latComp f h = latSmul T lam := by
      have : f.f.comp h.f = algebraMap O LL lam • LinearMap.id := LinearMap.ext hh
      unfold latComp latSmul
      congr 1
    rw [← W.map_comp, this, W.map_latSmul, algebraMap_smul]
  have h4 : algebraMap (LetA O n) W.EE (letE i) • (x - W.map f y) =
      algebraMap O W.EE lam • ∑ j, e j • b j := by
    conv_lhs => rw [← b.sum_repr (x - W.map f y)]
    simp only [Finset.smul_sum, smul_smul, he]
  refine ⟨W.map h (∑ j, e j • b j) + algebraMap (LetA O n) W.EE (letE i) • y, ?_⟩
  rw [map_add, h3, ← h4, map_smul, ← smul_add, sub_add_cancel, algebraMap_smul]

end GlobalTheory.RedDim
