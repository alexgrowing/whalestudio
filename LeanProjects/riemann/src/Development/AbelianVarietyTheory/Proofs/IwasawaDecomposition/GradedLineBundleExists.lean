import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MultiplicationLatticeSecond
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBlockMetricDiagForm
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemRangeCompIffOfIsClosedImmersion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LieBridgeG

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TopologicalSpace
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj GlobalTheory.LieMet GlobalTheory.LocM GlobalTheory.Points

namespace GlobalTheory.GradedPieces

attribute [local instance] Over.cartesianMonoidalCategory

section Linear

variable {k M : Type} [Field k] [AddCommGroup M] [Module k M] {m : ℕ}

def Diag (p q : Fin m → M) (d : Fin m → k) : Prop :=
  ∀ a, ∃ cf : Fin m → k, cf a = d a ∧ (∀ b, a < b → cf b = 0) ∧ q a = ∑ b, cf b • p b

theorem Diag.refl (p : Fin m → M) : Diag p p (fun _ => (1 : k)) := fun a =>
  ⟨Pi.single a 1, by simp, fun b hb => Pi.single_eq_of_ne hb.ne' _, by simp [Pi.single_apply]⟩

theorem Diag.unique {p q : Fin m → M} (hp : LinearIndependent k p) {d d' : Fin m → k} (h : Diag p q d)
    (h' : Diag p q d') : d = d' := funext fun a => by
  obtain ⟨c, hc, -, e⟩ := h a
  obtain ⟨c', hc', -, e'⟩ := h' a
  rw [← hc, ← hc', Fintype.linearIndependent_iffₛ.1 hp c c' (e.symm.trans e') a]

theorem Diag.trans {p q r : Fin m → M} {d d' : Fin m → k} (h : Diag p q d) (h' : Diag q r d') :
    Diag p r (fun a => d' a * d a) := fun a => by
  choose A hA hA0 hq using h
  obtain ⟨c, hc, hc0, e⟩ := h' a
  have z : ∀ b j, a < j ∨ (j = a ∧ b ≠ a) → c b * A b j = 0 := fun b j hj => by
    by_cases hb : a < b
    · rw [hc0 b hb, zero_mul]
    · rw [hA0 b j (by rcases hj with hj | ⟨rfl, hj⟩ <;> omega), mul_zero]
  refine ⟨fun j => ∑ b, c b * A b j, ?_, fun j hj => Finset.sum_eq_zero fun b _ => z b j (Or.inl hj), ?_⟩
  · show ∑ b, c b * A b a = d' a * d a
    rw [Finset.sum_eq_single a (fun b _ hb => z b a (Or.inr ⟨rfl, hb⟩)) (by simp), hc, hA]
  · rw [e]
    simp only [hq, Finset.smul_sum, Finset.sum_smul, smul_smul]
    exact Finset.sum_comm

theorem diag_iff_span (p q : Fin m → M) :
    (∃ d : Fin m → k, Diag p q d) ↔ ∀ a, q a ∈ Submodule.span k (p '' Set.Iic a) := by
  constructor
  · rintro ⟨d, h⟩ a
    obtain ⟨c, -, hc0, e⟩ := h a
    rw [e]
    refine Submodule.sum_mem _ fun b _ => ?_
    by_cases hb : a < b
    · simp [hc0 b hb]
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, not_lt.1 hb, rfl⟩)
  · intro h
    have : ∀ a, ∃ cf : Fin m → k, (∀ b, a < b → cf b = 0) ∧ q a = ∑ b, cf b • p b := fun a => by
      obtain ⟨l, hl, e⟩ := (Finsupp.mem_span_image_iff_linearCombination k).1 (h a)
      refine ⟨l, fun b hb => (Finsupp.mem_supported' k l).1 hl b (not_le.2 hb), ?_⟩
      rw [← e, Finsupp.linearCombination_apply, Finsupp.sum_fintype _ _ (by simp)]
    choose c h0 e using this
    exact ⟨fun a => c a a, fun a => ⟨c a, rfl, h0 a, e a⟩⟩

theorem Diag.symm {p q : Fin m → M} {d : Fin m → k} (h : Diag p q d) (hq : LinearIndependent k q) :
    ∃ d' : Fin m → k, Diag q p d' := by
  have h1 := (diag_iff_span p q).1 ⟨d, h⟩
  refine (diag_iff_span q p).2 fun a => ?_
  have le : Submodule.span k (q '' Set.Iic a) ≤ Submodule.span k (p '' Set.Iic a) := by
    rw [Submodule.span_le]
    rintro _ ⟨b, hb, rfl⟩
    exact Submodule.span_mono (Set.image_mono (Set.Iic_subset_Iic.2 hb)) (h1 b)
  have e1 : ∀ f : Fin m → M, f '' Set.Iic a = Set.range fun b : Set.Iic a => f b := fun f => Set.image_eq_range f _
  have : FiniteDimensional k (Submodule.span k (p '' Set.Iic a)) :=
    FiniteDimensional.span_of_finite k (Set.toFinite _)
  have e := Submodule.eq_of_le_of_finrank_le le (by
    rw [e1, e1]
    exact (finrank_range_le_card _).trans
      (finrank_span_eq_card (hq.comp (fun b : Set.Iic a => (b : Fin m)) Subtype.val_injective)).ge)
  rw [e]
  exact Submodule.subset_span ⟨a, Set.mem_Iic.2 le_rfl, rfl⟩

theorem coeff_eq {n : ℕ} {V : Fin n → M} (hV : LinearIndependent k V) (e : Fin m ↪ Fin n) {c : Fin n → k}
    {cf : Fin m → k} (h : ∑ j, c j • V j = ∑ b, cf b • V (e b)) (a : Fin m) : c (e a) = cf a := by
  have e1 : ∑ b, cf b • V (e b) = ∑ j, Function.extend e cf 0 j • V j :=
    Fintype.sum_of_injective e e.injective _ _
      (fun j hj => by rw [Function.extend_apply' _ _ _ hj, Pi.zero_apply, zero_smul])
      (fun b => by rw [e.injective.extend_apply])
  rw [Fintype.linearIndependent_iffₛ.1 hV _ _ (h.trans e1) (e a), e.injective.extend_apply]

end Linear

section Tangent

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} {t : SAB H X}
  {S T : Type} [CommRing S] [CommRing T] {x : Sp S ⟶ X} {m : ℕ}

theorem comb_iff {v : Fin m → (Sp (DualNumber S) ⟶ t.G.left)} (hv : ∀ i, IsTanAtG t x (v i)) (a : Fin m → S)
    {w : Sp (DualNumber S) ⟶ t.G.left} (hw : IsTanAtG t x w) :
    IsCombAtG t x v a w ↔ tanOf hw = ∑ i, a i • tanOf (hv i) :=
  isComb_iff (fun i => tanOf (hv i)) a (tanOf hw)

theorem comb_map (φ : S →+* T) {x' : Sp T ⟶ X} (hx : spMap φ ≫ x = x')
    {v : Fin m → (Sp (DualNumber S) ⟶ t.G.left)} {cf : Fin m → S} {w : Sp (DualNumber S) ⟶ t.G.left}
    (h : IsCombAtG t x v cf w) :
    IsCombAtG t x' (fun i => spMap (dualMap φ) ≫ v i) (fun i => φ (cf i)) (spMap (dualMap φ) ≫ w) := by
  subst hx
  obtain ⟨u, hu, rfl⟩ := h
  let δ : tEpsG (spMap φ ≫ x) ⟶ tEpsG x := Over.homMk (spMap (dualMap φ)) (by
    show spMap (dualMap φ) ≫ spMap (algebraMap S (DualNumber S)) ≫ x =
      spMap (algebraMap T (DualNumber T)) ≫ spMap φ ≫ x
    rw [← Category.assoc, ← Category.assoc, spMap_comp_spMap, spMap_comp_spMap, Formalism.L2.Pj.dualMap_comp_alg])
  have e : ∀ a : S, spMap (dualMap φ) ≫ spMap (epsMul a) = spMap (epsMul (φ a)) ≫ spMap (dualMap φ) := fun a => by
    rw [spMap_comp_spMap, spMap_comp_spMap]
    congr 1
    refine RingHom.ext fun z => TrivSqZeroExt.ext ?_ ?_ <;> simp [dualMap, epsMul, mul_comm]
  refine ⟨fun i => δ ≫ u i, fun i => ?_, ?_⟩
  · simp only [Over.comp_left, δ, Over.homMk_left]
    rw [hu i, ← Category.assoc, e, Category.assoc]
  · rw [List.prod_ofFn, List.prod_ofFn, ← comp_prodT]
    rfl

theorem basis_iff {G' : Over (Sp S)} [GrpObj G'] [IsCommMonObj G'] {Φ : G'.left ⟶ t.G.left}
    (h : IsGrpPullback G' t.G x Φ) {u : Fin m → (epsR S ⟶ G')} {v : Fin m → (Sp (DualNumber S) ⟶ t.G.left)}
    (hv : ∀ i, IsTanAtG t x (v i)) (e : ∀ i, pushHom h (epsR S) (u i) = tv (tanOf (hv i))) :
    IsLieBasis u ↔ ∀ w, IsTanAtG t x w → ∃! cf, IsCombAtG t x v cf w := by
  have key : ∀ a p (n : TanM x t.G), pushHom h (epsR S) p = tv n →
      (IsLieComb a u p ↔ IsCombAtG t x v a (tv n).left) := fun a p n hp => by
    rw [isLieComb_iff h, hp]
    simp only [e]
    refine Iff.trans ?_ (isCombAtG_iff t x (fun i => tv (tanOf (hv i))) a _).symm
    exact ⟨fun q => by rw [q], fun q => Over.OverMorphism.ext q.symm⟩
  refine ⟨fun hu w hw => ?_, fun hb => ⟨fun i => (isTangent_iff h _).2 (by rw [e]; exact tv_mem _), fun p hp => ?_⟩⟩
  · obtain ⟨p, hp⟩ := push_surj h (tv (tanOf hw))
    simpa only [key _ p _ hp, left_tanOf] using hu.2 p ((isTangent_iff h p).2 (by rw [hp]; exact tv_mem _))
  · simpa only [key _ p (mkT _ ((isTangent_iff h p).1 hp)) rfl] using
      hb _ (isTan_tv (mkT _ ((isTangent_iff h p).1 hp)))

theorem basis_map (ψ : S →+* T) {x' : Sp T ⟶ X} (hx : spMap ψ ≫ x = x') {v : Fin m → (Sp (DualNumber S) ⟶ t.G.left)}
    (hv : ∀ i, IsTanAtG t x (v i)) (hb : ∀ w, IsTanAtG t x w → ∃! cf, IsCombAtG t x v cf w) :
    ∀ w, IsTanAtG t x' w → ∃! cf, IsCombAtG t x' (fun i => spMap (dualMap ψ) ≫ v i) cf w := by
  subst hx
  have h₀ := isGrpPullback_pullback t.G x
  have h := isGrpPullback_pullback t.G (spMap ψ ≫ x)
  have hv' := fun i => isTan_map ψ rfl (hv i)
  choose u hu using fun i => push_surj h₀ (tv (tanOf (hv i)))
  choose u' hu' using fun i => push_surj h (tv (tanOf (hv' i)))
  have := t.semi.smooth
  have : Smooth ((Over.pullback x).obj t.G).hom := show Smooth (pullback.snd _ _) from inferInstance
  refine (basis_iff h hv' hu').1 (Chart.frameLieBCR _ ((basis_iff h₀ hv hu).2 hb) ψ
    (Chart.isGrpPullback_factor x (spMap ψ) h)
    (fun a b v hv => push_inj h (by
      have := smT_add _ _ ((isTangent_iff h v).1 ((Chart.isTan_iff _).1 hv)) a b
      rw [← push_scK h, ← push_scK h, ← push_scK h, ← map_mul] at this
      exact this)) (fun i => (isTangent_iff h _).2 (by rw [hu']; exact tv_mem _)) fun i => ?_)
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, Category.assoc]
    exact (congrArg (fun q => q.left) (hu' i)).trans (congrArg (_ ≫ ·) (congrArg (fun q => q.left) (hu i)).symm)
  · rw [Category.assoc, pullback.lift_snd, ← Category.assoc, Over.w (u' i), Category.assoc]
    refine Eq.trans ?_ (congrArg (_ ≫ ·) (Over.w (u i)).symm)
    exact (spMap_comp_spMap _ _).trans ((congrArg spMap (Formalism.L2.Pj.dualMap_comp_alg _).symm).trans (spMap_comp_spMap _ _).symm)

theorem dual_comp {R : Type} [CommRing R] (ρ : R →+* S) (ψ : S →+* T) {Y : Scheme.{0}} (v : Sp (DualNumber R) ⟶ Y) :
    spMap (dualMap ψ) ≫ spMap (dualMap ρ) ≫ v = spMap (dualMap (ψ.comp ρ)) ≫ v := by
  rw [← Category.assoc, spMap_comp_spMap]
  congr 2
  refine RingHom.ext fun z => TrivSqZeroExt.ext ?_ ?_ <;> simp [dualMap]

variable {k : Type} [Field k] {y : Sp k ⟶ X}

theorem linInd_of_basis {v : Fin m → (Sp (DualNumber k) ⟶ t.G.left)} (hv : ∀ i, IsTanAtG t y (v i))
    (hb : ∀ w, IsTanAtG t y w → ∃! cf, IsCombAtG t y v cf w) : LinearIndependent k fun i => tanOf (hv i) :=
  Fintype.linearIndependent_iffₛ.2 fun c c' h => congrFun
    ((hb _ (isTan_tv (∑ i, c i • tanOf (hv i)))).unique ((isComb_iff (fun i => tanOf (hv i)) c _).2 rfl)
      ((isComb_iff (fun i => tanOf (hv i)) c' _).2 h))

variable (t y) in

def DiagAt (p q : Fin m → (Sp (DualNumber k) ⟶ t.G.left)) (d : Fin m → k) : Prop :=
  ∀ a, ∃ cf : Fin m → k, cf a = d a ∧ (∀ b, a < b → cf b = 0) ∧ IsCombAtG t y p cf (q a)

theorem diagAt_iff {p q : Fin m → (Sp (DualNumber k) ⟶ t.G.left)} (hp : ∀ i, IsTanAtG t y (p i))
    (hq : ∀ i, IsTanAtG t y (q i)) (d : Fin m → k) :
    DiagAt t y p q d ↔ Diag (fun i => tanOf (hp i)) (fun i => tanOf (hq i)) d := by
  simp only [DiagAt, Diag, comb_iff hp _ (hq _)]

theorem diagAt_of_sameFlag {Dw : Datum H} {ty : (E →+* ℂ) → Finset ℕ} (hty : ∀ σ, ty σ = Finset.range (Dw.mult σ + 1))
    {u u' : Vecs Dw t k} (h : SameFlag ty t y u u') (σ : E →+* ℂ) : ∃ d, DiagAt t y (u σ) (u' σ) d := by
  choose c h0 hc using fun a : Fin (Dw.mult σ) =>
    h σ (a + 1) (by rw [hty, Finset.mem_range]; exact Nat.succ_lt_succ a.2) a (Nat.lt_succ_self _)
  exact ⟨fun a => c a a, fun a => ⟨c a, rfl, fun b hb => h0 a b hb, hc a⟩⟩

end Tangent

section Model

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
  {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}
  (Z : Mdl Y i₀)

theorem exists_diag_of_flagAt (hty : ∀ σ, Z.ty σ = Finset.range (Dw.mult σ + 1)) {k : Type} [Field k] {x : Sp k ⟶ Z.X}
    {u u' : Vecs Dw (Y Z.i).t k} (h : Z.FlagAt x u) (h' : Z.FlagAt x u') (σ : E →+* ℂ)
    (hu : ∀ i, IsTanAtG (Y Z.i).t (x ≫ Z.π) (u σ i)) (hu' : ∀ i, IsTanAtG (Y Z.i).t (x ≫ Z.π) (u' σ i))
    (li : LinearIndependent k fun i => tanOf (hu' i)) :
    ∃ d : Fin (Dw.mult σ) → k, Diag (fun i => tanOf (hu' i)) (fun i => tanOf (hu i)) d := by
  obtain ⟨a, φ, hx, -, hs⟩ := h
  obtain ⟨a', φ', hx', -, hs'⟩ := h'
  have hf : ∀ a φ, spMap φ ≫ Z.chart a = x → ∀ i, IsTanAtG (Y Z.i).t (x ≫ Z.π) ((Z.fr a).bc φ σ i) :=
    fun a φ hx i => isTan_map φ (by rw [← hx, Category.assoc]) ((Z.frame a).1 σ i).1
  have hg := Z.glue k a' a φ' φ (hx'.trans hx.symm)
  rw [← Category.assoc, hx'] at hg
  obtain ⟨d₁, h₁⟩ := diagAt_of_sameFlag hty hs σ
  obtain ⟨d₂, h₂⟩ := diagAt_of_sameFlag hty hs' σ
  obtain ⟨d₃, h₃⟩ := diagAt_of_sameFlag hty hg σ
  rw [diagAt_iff (hf a φ hx) hu] at h₁
  rw [diagAt_iff (hf a' φ' hx') hu'] at h₂
  rw [diagAt_iff (hf a' φ' hx') (hf a φ hx)] at h₃
  obtain ⟨d₄, h₄⟩ := h₂.symm li
  exact ⟨_, (h₄.trans h₃).trans h₁⟩

variable {Z}

theorem tan_bc {U : Z.X.Opens} {hU : IsAffineOpen U} {w : Vecs Dw (Y Z.i).t Γ(Z.X, U)} (hw : IntFrame Z hU w)
    {R : Type} [CommRing R] (φ : Γ(Z.X, U) →+* R) {x : Sp R ⟶ Z.X} (hx : spMap φ ≫ hU.fromSpec = x) (σ : E →+* ℂ)
    (i : Fin (Dw.mult σ)) : IsTanAtG (Y Z.i).t (x ≫ Z.π) (w.bc φ σ i) := by
  obtain ⟨n, v, e, he, hv, -⟩ := hw.1 σ
  have hx' : spMap φ ≫ hU.fromSpec ≫ Z.π = x ≫ Z.π := by rw [← hx, Category.assoc]
  have h := hv (e i)
  rw [he i] at h
  exact isTan_map φ hx' h

theorem linInd_bc {U : Z.X.Opens} {hU : IsAffineOpen U} {w : Vecs Dw (Y Z.i).t Γ(Z.X, U)} (hw : IntFrame Z hU w)
    {k : Type} [Field k] (φ : Γ(Z.X, U) →+* k) {x : Sp k ⟶ Z.X} (hx : spMap φ ≫ hU.fromSpec = x) (σ : E →+* ℂ) :
    LinearIndependent k fun i => tanOf (tan_bc hw φ hx σ i) := by
  obtain ⟨n, v, e, he, hv, hb⟩ := hw.1 σ
  have hx' : spMap φ ≫ hU.fromSpec ≫ Z.π = x ≫ Z.π := by rw [← hx, Category.assoc]
  have li := (linInd_of_basis (fun i => isTan_map φ hx' (hv i)) (basis_map φ hx' hv hb)).comp e e.injective
  convert li using 2 with i
  exact tan_ext (congrArg (spMap (dualMap φ) ≫ ·) (he i).symm)

theorem exists_diag (hty : ∀ σ, Z.ty σ = Finset.range (Dw.mult σ + 1)) {U U' : Z.X.Opens} {hU : IsAffineOpen U}
    {hU' : IsAffineOpen U'} (hV : IsAffineOpen (U ⊓ U')) {w : Vecs Dw (Y Z.i).t Γ(Z.X, U)}
    {w' : Vecs Dw (Y Z.i).t Γ(Z.X, U')} (hw : IntFrame Z hU w) (hw' : IntFrame Z hU' w') (σ : E →+* ℂ) :
    ∃ D : Fin (Dw.mult σ) → Γ(Z.X, U ⊓ U'), ∀ (k : Type) [Field k] (φ : Γ(Z.X, U) →+* k) (φ' : Γ(Z.X, U') →+* k)
      (x : Sp k ⟶ Z.X) (hx : spMap φ ≫ hU.fromSpec = x) (hx' : spMap φ' ≫ hU'.fromSpec = x), Set.range x ⊆ Z.opn →
      Diag (fun i => tanOf (tan_bc hw' φ' hx' σ i)) (fun i => tanOf (tan_bc hw φ hx σ i))
        fun a => valR x (U ⊓ U') (D a) := by
  obtain ⟨n, v, e, he, hv, hb⟩ := hw'.1 σ
  let ρ : Γ(Z.X, U) →+* Γ(Z.X, U ⊓ U') := (Z.X.presheaf.map (homOfLE inf_le_left).op).hom
  let ρ' : Γ(Z.X, U') →+* Γ(Z.X, U ⊓ U') := (Z.X.presheaf.map (homOfLE inf_le_right).op).hom
  have hρ : spMap ρ ≫ hU.fromSpec = hV.fromSpec := hU.map_fromSpec hV _
  have hρ' : spMap ρ' ≫ hU'.fromSpec = hV.fromSpec := hU'.map_fromSpec hV _
  have hρ2 : spMap ρ' ≫ hU'.fromSpec ≫ Z.π = hV.fromSpec ≫ Z.π := by rw [← hρ', Category.assoc]
  choose c hc using fun a => (basis_map ρ' hρ2 hv hb _ (tan_bc hw ρ hρ σ a)).exists
  refine ⟨fun a => c a (e a), fun k _ φ φ' x hx hx' ho => ?_⟩
  have h1 : ⊤ ≤ x ⁻¹ᵁ U := hx ▸ le_preimage_specMap_fromSpec hU (CommRingCat.ofHom φ)
  have h2 : ⊤ ≤ x ⁻¹ᵁ U' := hx' ▸ le_preimage_specMap_fromSpec hU' (CommRingCat.ofHom φ')
  have h3 : ⊤ ≤ x ⁻¹ᵁ (U ⊓ U') := fun z hz => ⟨h1 hz, h2 hz⟩
  let ψ : Γ(Z.X, U ⊓ U') →+* k := (valMap x _ h3).hom
  have hψ : spMap ψ ≫ hV.fromSpec = x := specMap_valMap_fromSpec hV x h3
  have e1 : ψ.comp ρ = φ := by
    subst hx
    exact congrArg (fun f => f.hom) ((res_valMap _ inf_le_left h3 h1).trans
      (valMap_specMap_fromSpec hU (CommRingCat.ofHom φ) h1))
  have e2 : ψ.comp ρ' = φ' := by
    subst hx'
    exact congrArg (fun f => f.hom) ((res_valMap _ inf_le_right h3 h2).trans
      (valMap_specMap_fromSpec hU' (CommRingCat.ofHom φ') h2))
  have hx2 : spMap φ' ≫ hU'.fromSpec ≫ Z.π = x ≫ Z.π := by rw [← hx', Category.assoc]
  have hvk := fun i => isTan_map φ' hx2 (hv i)
  have li := linInd_of_basis hvk (basis_map φ' hx2 hv hb)
  obtain ⟨d, hd⟩ := exists_diag_of_flagAt Z hty (hx ▸ hw.2 k φ (hx ▸ ho)) (hx' ▸ hw'.2 k φ' (hx' ▸ ho)) σ
    (tan_bc hw φ hx σ) (tan_bc hw' φ' hx' σ) (linInd_bc hw' φ' hx' σ)
  intro a
  obtain ⟨cf, -, h0, hs⟩ := hd a
  refine ⟨cf, ?_, h0, hs⟩
  have hk := comb_map ψ (x' := x ≫ Z.π) (by rw [← hψ, Category.assoc]) (hc a)
  simp only [Vecs.bc, dual_comp, e1, e2] at hk
  have hk' := (comb_iff hvk _ (tan_bc hw φ hx σ a)).1 hk
  refine Eq.trans ?_ (valR_eq x _ h3 _).symm
  refine (coeff_eq li e (hk'.symm.trans (hs.trans (Finset.sum_congr rfl fun b _ => ?_))) a).symm
  exact congrArg (cf b • ·) (tan_ext (congrArg (spMap (dualMap φ') ≫ ·) (he b).symm))

variable (Z)

theorem fn_ext {U : Z.X.Opens} {f g : Γ(Z.X, U)}
    (h : ∀ (k : Type) [Field k] (x : Sp k ⟶ Z.X), ⊤ ≤ x ⁻¹ᵁ U → Set.range x ⊆ Z.opn → valR x U f = valR x U g) :
    f = g := by
  have : IsReduced Z.X := by
    have : ∀ x : Z.X, IsDomain (Z.X.presheaf.stalk x) := Z.normal.isDomain_stalk
    exact isReduced_of_isReduced_stalk _
  rw [← sub_eq_zero, ← basicOpen_eq_bot_iff]
  by_contra hne
  have hn : ((Z.X.basicOpen (f - g) : Z.X.Opens) : Set Z.X).Nonempty :=
    Set.nonempty_iff_ne_empty.2 fun e => hne (SetLike.coe_injective e)
  obtain ⟨z, hz, ho⟩ := Z.dense.inter_open_nonempty _ (Z.X.basicOpen (f - g)).isOpen hn
  let x : Sp (Z.X.residueField z) ⟶ Z.X := Z.X.fromSpecResidueField z
  have hx : ∀ s, x s = z := Scheme.fromSpecResidueField_apply z
  have hb : ⊤ ≤ x ⁻¹ᵁ Z.X.basicOpen (f - g) := fun s _ => show x s ∈ _ from (hx s).symm ▸ hz
  have hU : ⊤ ≤ x ⁻¹ᵁ U := le_preimage_mono x (Z.X.basicOpen_le _) hb
  have hu := (le_preimage_basicOpen_iff x hU _).1 hb
  have e := h _ x hU (by rintro _ ⟨s, rfl⟩; exact (hx s).symm ▸ ho)
  rw [valR_eq x U hU, valR_eq x U hU, ← sub_eq_zero, ← map_sub] at e
  rw [valR_eq x U hU, e] at hu
  exact not_isUnit_zero hu

theorem isAffineOpen_inf {U U' : Z.X.Opens} (hU : IsAffineOpen U) (hU' : IsAffineOpen U') :
    IsAffineOpen (U ⊓ U') := by
  have : IsSeparated (PSpace.str (Z.i.c.V W) Z.n) := by
    unfold PSpace.str
    infer_instance
  have : IsSeparated Z.s := by
    unfold Pre.s
    infer_instance
  have : IsSeparated (terminal.from Z.X) := by
    rw [← terminal.comp_from Z.s]
    infer_instance
  exact hU.inf hU'

theorem valR_prod_zpow {X : Scheme.{0}} {k : Type} [Field k] (x : Sp k ⟶ X) {U : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ U)
    {κ : Type} [Fintype κ] {m : κ → ℕ} (u : ∀ σ, Fin (m σ) → Γ(X, U)ˣ) (e : ∀ σ, Fin (m σ) → ℤ) :
    valR x U (∏ σ, ∏ a, u σ a ^ e σ a : Γ(X, U)ˣ).val = ∏ σ, ∏ a, valR x U (u σ a).val ^ e σ a := by
  simp only [valR_eq x U h]
  have := congrArg Units.val (show Units.map (valMap x U h).hom.toMonoidHom (∏ σ, ∏ a, u σ a ^ e σ a) =
    ∏ σ, ∏ a, Units.map (valMap x U h).hom.toMonoidHom (u σ a) ^ e σ a by simp only [map_prod, map_zpow])
  simp only [Units.coe_prod, Units.val_zpow_eq_zpow_val] at this
  exact this

theorem exists_isGrLB' (hZ : HasDR Z) (e : ∀ σ : E →+* ℂ, Fin (Dw.mult σ) → ℤ) : ∃ L, IsGrLB Z e L := by
  obtain ⟨hty, hc⟩ := hZ
  choose U hU w hm hw using hc
  choose D hD using fun (i j : Z.X) σ => exists_diag hty (isAffineOpen_inf Z (hU i) (hU j)) (hw i) (hw j) σ
  have pt : ∀ {k : Type} [Field k] (x : Sp k ⟶ Z.X) i (h : ⊤ ≤ x ⁻¹ᵁ U i),
      spMap (valMap x _ h).hom ≫ (hU i).fromSpec = x := fun x i h => specMap_valMap_fromSpec (hU i) x h
  have self : ∀ {k : Type} [Field k] (x : Sp k ⟶ Z.X) i, ⊤ ≤ x ⁻¹ᵁ U i → Set.range x ⊆ Z.opn → ∀ σ a,
      valR x _ (D i i σ a) = 1 := fun x i h ho σ a =>
    congrFun ((hD i i σ _ _ _ x (pt x i h) (pt x i h) ho).unique (linInd_bc (hw i) _ (pt x i h) σ) (Diag.refl _)) a
  have coc : ∀ {k : Type} [Field k] (x : Sp k ⟶ Z.X) i j l, ⊤ ≤ x ⁻¹ᵁ U i → ⊤ ≤ x ⁻¹ᵁ U j → ⊤ ≤ x ⁻¹ᵁ U l →
      Set.range x ⊆ Z.opn → ∀ σ a, valR x _ (D i j σ a) * valR x _ (D j l σ a) = valR x _ (D i l σ a) :=
    fun x i j l hi hj hl ho σ a =>
      congrFun (((hD j l σ _ _ _ x (pt x j hj) (pt x l hl) ho).trans (hD i j σ _ _ _ x (pt x i hi) (pt x j hj) ho)).unique
        (linInd_bc (hw l) _ (pt x l hl) σ) (hD i l σ _ _ _ x (pt x i hi) (pt x l hl) ho)) a
  have unit : ∀ i j σ a, IsUnit (D i j σ a) := fun i j σ a => by
    refine IsUnit.of_mul_eq_one ((Z.X.presheaf.map (homOfLE (inf_comm (U i) (U j)).le).op).hom (D j i σ a))
      (fn_ext Z fun k _ x h ho => ?_)
    have hi := le_preimage_mono x inf_le_left h
    rw [valR_mul x _ h, valR_res x _ h, valR_one x _ h, coc x i j i hi (le_preimage_mono x inf_le_right h) hi ho,
      self x i hi ho]
  let g : ∀ i j, Γ(Z.X, U i ⊓ U j)ˣ := fun i j => ∏ σ, ∏ a, (unit i j σ a).unit ^ e σ a
  have hg : ∀ {k : Type} [Field k] (x : Sp k ⟶ Z.X) i j, ⊤ ≤ x ⁻¹ᵁ (U i ⊓ U j) →
      valR x _ (g i j).val = ∏ σ, ∏ a, valR x _ (D i j σ a) ^ e σ a := fun x i j h => valR_prod_zpow x h _ e
  have hr : ∀ {k : Type} [Field k] (x : Sp k ⟶ Z.X) i j {V : Z.X.Opens} (hV : V ≤ U i ⊓ U j), ⊤ ≤ x ⁻¹ᵁ V →
      valR x V (res hV (g i j)).val = ∏ σ, ∏ a, valR x _ (D i j σ a) ^ e σ a := fun x i j V hV h =>
    (valR_res x hV h _).trans (hg x i j (le_preimage_mono x hV h))
  refine ⟨⟨Z.X, U, g⟩, ⟨?_, fun i => ?_, fun i j l => ?_⟩, hU, w, hw, fun i j k _ φ φ' d hx ho hd => ?_⟩
  · exact top_unique fun z _ => Opens.mem_iSup.2 ⟨z, hm z⟩
  · refine Units.ext (fn_ext Z fun k _ x h ho => ?_)
    refine (hr x i i _ h).trans ?_
    simp only [self x i h ho, one_zpow, Finset.prod_const_one]
    exact (valR_one x _ h).symm
  · refine Units.ext (fn_ext Z fun k _ x h ho => ?_)
    refine (valR_mul x _ h _ _).trans ?_
    rw [hr x i j _ h, hr x j l _ h, hr x i l _ h]
    simp only [← Finset.prod_mul_distrib, ← mul_zpow, coc x i j l (le_preimage_mono x (inf_le_left.trans inf_le_left) h)
      (le_preimage_mono x (inf_le_left.trans inf_le_right) h) (le_preimage_mono x inf_le_right h) ho]
  · have h1 := le_preimage_specMap_fromSpec (hU i) (CommRingCat.ofHom φ)
    have h2 : ⊤ ≤ (spMap φ ≫ (hU i).fromSpec) ⁻¹ᵁ U j := hx ▸ le_preimage_specMap_fromSpec (hU j) (CommRingCat.ofHom φ')
    refine (hg _ i j fun z hz => ⟨h1 hz, h2 hz⟩).trans
      (Finset.prod_congr rfl fun σ _ => Finset.prod_congr rfl fun a _ => ?_)
    have h3 : DiagAt (Y Z.i).t ((spMap φ ≫ (hU i).fromSpec) ≫ Z.π) ((w j).bc φ' σ) ((w i).bc φ σ) (d σ) := by
      rw [Category.assoc]
      exact hd σ
    rw [diagAt_iff (tan_bc (hw j) φ' hx.symm σ) (tan_bc (hw i) φ rfl σ)] at h3
    exact congrArg (· ^ e σ a)
      (congrFun ((hD i j σ k φ φ' _ rfl hx.symm ho).unique (linInd_bc (hw j) φ' hx.symm σ) h3) a)

end Model

theorem exists_isGrLB : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ), p.Prime → (p : ℂ) ∈ W.nonunits →
    ∀ (Y : LocalSystem Xo p W) (i₀ : Idx H p), ∀ (Z : Mdl Y i₀), HasDR Z → ∀ e, ∃ L, IsGrLB Z e L :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ Z hZ e => exists_isGrLB' Z hZ e

end GlobalTheory.GradedPieces
