import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.BernsteinUnitaryProductIrreducible
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsLocallyConstantModulus
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LowerEquivUpperSwap

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel Matrix
open scoped TensorProduct

namespace GlobalTheory.SmGL.MultiIrr

section General

variable {F G H M V W U : Type} [Field F] [Group G] [Group H] [Group M] [AddCommGroup V] [Module F V]
  [AddCommGroup W] [Module F W] [AddCommGroup U] [Module F U]

theorem isIrreducible_iff_of_linearEquiv {ρ : Representation F G V} {σ : Representation F H W} (φ : G → H)
    (hφ : Function.Surjective φ) (κ : V ≃ₗ[F] W) (h : ∀ g v, κ (ρ g v) = σ (φ g) (κ v)) :
    ρ.IsIrreducible ↔ σ.IsIrreducible := by
  let E : Subrepresentation ρ ≃o Subrepresentation σ :=
    { toFun := fun S => ⟨S.toSubmodule.comap κ.symm.toLinearMap, fun g w hw => by
        obtain ⟨g, rfl⟩ := hφ g
        obtain ⟨v, rfl⟩ := κ.surjective w
        have hv : v ∈ S.toSubmodule := κ.symm_apply_apply v ▸ hw
        simpa [← h] using S.apply_mem_toSubmodule g hv⟩
      invFun := fun T => ⟨T.toSubmodule.comap κ.toLinearMap, fun g v hv => by
        show κ (ρ g v) ∈ T.toSubmodule
        rw [h]
        exact T.apply_mem_toSubmodule _ hv⟩
      left_inv := fun S => Subrepresentation.toSubmodule_injective (by ext v; simp)
      right_inv := fun T => Subrepresentation.toSubmodule_injective (by ext v; simp)
      map_rel_iff' := fun {S T} => ⟨fun hh v hv => by
        have : κ.symm (κ v) ∈ S.toSubmodule := (κ.symm_apply_apply v).symm ▸ hv
        have h2 : κ.symm (κ v) ∈ T.toSubmodule := hh this
        exact κ.symm_apply_apply v ▸ h2, fun hh v hv => hh hv⟩ }
  exact E.isSimpleOrder_iff

theorem isIrreducible_iff_of_equiv {ρ : Representation F G V} {σ : Representation F G W} (E : ρ.Equiv σ) :
    ρ.IsIrreducible ↔ σ.IsIrreducible :=
  isIrreducible_iff_of_linearEquiv id Function.surjective_id E.toLinearEquiv
    fun g v => E.toIntertwiningMap.isIntertwining _ _ g v

variable [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace H] [IsTopologicalGroup H]

theorem mem_smooth_of_eventually {P : Subgroup G} {σ : Representation F P W} (f : indSpace P σ)
    (h : ∀ᶠ u in nhds (1 : G), ∀ x, f.1 (x * u) = f.1 x) : f ∈ smoothPart (ind P σ) :=
  mem_smoothPart_of_nhds (h.mono fun _ hu => Subtype.ext (funext hu))

theorem eventually_of_smooth {P : Subgroup G} {σ : Representation F P W} (f : smoothPart (ind P σ)) :
    ∀ᶠ u in nhds (1 : G), ∀ x, f.1.1 (x * u) = f.1.1 x :=
  Filter.mem_of_superset (IsOpen.mem_nhds f.2 (by simp)) fun _ hu x =>
    congrFun (congrArg Subtype.val hu) x

def indPull {P : Subgroup G} {Q : Subgroup H} {σ : Representation F P V} {τ : Representation F Q W}
    (φ : G →* H) (hφ : Continuous φ) (κ : W →ₗ[F] V)
    (h : ∀ p : P, ∃ q : Q, (q : H) = φ p ∧ ∀ w, σ p (κ w) = κ (τ q w)) :
    smoothPart (ind Q τ) →ₗ[F] smoothPart (ind P σ) where
  toFun f := ⟨⟨fun g => κ (f.1.1 (φ g)), fun p g => by
      obtain ⟨q, hq, hs⟩ := h p
      show κ (f.1.1 (φ (p * g))) = σ p (κ (f.1.1 (φ g)))
      rw [map_mul, ← hq, f.1.2 q, hs]⟩,
    mem_smooth_of_eventually _ (((hφ.tendsto' 1 1 (map_one φ)).eventually (eventually_of_smooth f)).mono
      fun u hu x => by
        show κ (f.1.1 (φ (x * u))) = κ (f.1.1 (φ x))
        rw [map_mul, hu])⟩
  map_add' _ _ := Subtype.ext (Subtype.ext (funext fun _ => map_add κ _ _))
  map_smul' _ _ := Subtype.ext (Subtype.ext (funext fun _ => map_smul κ _ _))

theorem isIrreducible_smInd_iff {P : Subgroup G} {Q : Subgroup H} {σ : Representation F P V}
    {τ : Representation F Q W} (φ : G ≃* H) (hφ : Continuous φ) (hφ' : Continuous φ.symm) (κ : V ≃ₗ[F] W)
    (hP : ∀ g, g ∈ P ↔ φ g ∈ Q) (h : ∀ (p : P) v, κ (σ p v) = τ ⟨φ p, (hP p).1 p.2⟩ (κ v)) :
    (smInd P σ).IsIrreducible ↔ (smInd Q τ).IsIrreducible := by
  refine isIrreducible_iff_of_linearEquiv φ φ.surjective (LinearEquiv.ofLinear
    (indPull (σ := τ) (τ := σ) φ.symm.toMonoidHom hφ' κ.toLinearMap fun q =>
      ⟨⟨φ.symm q, (hP _).2 (by simp)⟩, rfl, fun w => by simp [h]⟩)
    (indPull (σ := σ) (τ := τ) φ.toMonoidHom hφ κ.symm.toLinearMap fun p =>
      ⟨⟨φ p, (hP p).1 p.2⟩, rfl, fun w => κ.injective (by simp [h])⟩) ?_ ?_) fun g f => ?_
  · refine LinearMap.ext fun f => Subtype.ext (Subtype.ext (funext fun x => ?_))
    show κ (κ.symm (f.1.1 (φ (φ.symm x)))) = f.1.1 x
    simp
  · refine LinearMap.ext fun f => Subtype.ext (Subtype.ext (funext fun x => ?_))
    show κ.symm (κ (f.1.1 (φ.symm (φ x)))) = f.1.1 x
    simp
  · refine Subtype.ext (Subtype.ext (funext fun x => ?_))
    show κ (f.1.1 (φ.symm x * g)) = κ (f.1.1 (φ.symm (x * φ g)))
    simp

def ev {P : Subgroup H} (ρ : Representation F P W) (x : H) : smoothPart (ind P ρ) →ₗ[F] W where
  toFun f := f.1.1 x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace H] [IsTopologicalGroup H] in

def coord (l : V →ₗ[F] F) (W : Type) [AddCommGroup W] [Module F W] : V ⊗[F] W →ₗ[F] W :=
  (TensorProduct.lid F W).toLinearMap ∘ₗ l.rTensor W

theorem coord_lTensor (l : V →ₗ[F] F) (A : W →ₗ[F] U) (x : V ⊗[F] W) :
    coord l U (A.lTensor V x) = A (coord l W x) := by
  induction x with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | tmul v w => simp [coord]

theorem exists_sum_coord {ι : Type} (b : Module.Basis ι F V) (x : V ⊗[F] W) :
    ∃ s : Finset ι, (∀ i ∉ s, coord (b.coord i) W x = 0) ∧
      ∀ t : Finset ι, s ⊆ t → x = ∑ i ∈ t, b i ⊗ₜ coord (b.coord i) W x := by
  classical
  induction x with
  | zero => exact ⟨∅, by simp, by simp⟩
  | add x y hx hy =>
    obtain ⟨s, h1, h2⟩ := hx
    obtain ⟨s', h1', h2'⟩ := hy
    refine ⟨s ∪ s', fun i hi => ?_, fun t ht => ?_⟩
    · rw [Finset.mem_union, not_or] at hi
      rw [map_add, h1 i hi.1, h1' i hi.2, add_zero]
    · simp only [map_add, TensorProduct.tmul_add, Finset.sum_add_distrib]
      rw [← h2 t (Finset.union_subset_left ht), ← h2' t (Finset.union_subset_right ht)]
  | tmul v w =>
    refine ⟨(b.repr v).support, fun i hi => ?_, fun t ht => ?_⟩
    · simp [coord, Finsupp.notMem_support_iff.1 hi]
    · have : v = ∑ i ∈ t, b.repr v i • b i := by
        conv_lhs => rw [← b.linearCombination_repr v, Finsupp.linearCombination_apply,
          Finsupp.sum_of_support_subset _ ht _ (by simp)]
      conv_lhs => rw [this, TensorProduct.sum_tmul]
      simp [coord, TensorProduct.smul_tmul]

omit [TopologicalSpace G] [IsTopologicalGroup G] in

theorem eq_zero_of_ev {P : Subgroup H} (ρ : Representation F P W) (t : V ⊗[F] smoothPart (ind P ρ))
    (h : ∀ x, (ev ρ x).lTensor V t = 0) : t = 0 := by
  obtain ⟨s, -, h2⟩ := exists_sum_coord (Module.Basis.ofVectorSpace F V) t
  rw [h2 s le_rfl]
  refine Finset.sum_eq_zero fun i _ => ?_
  have : coord ((Module.Basis.ofVectorSpace F V).coord i) _ t = 0 :=
    Subtype.ext (Subtype.ext (funext fun x => by
      have := coord_lTensor ((Module.Basis.ofVectorSpace F V).coord i) (ev ρ x) t
      rw [h, map_zero] at this
      exact this.symm))
  rw [this, TensorProduct.tmul_zero]

omit [TopologicalSpace G] [IsTopologicalGroup G] in

theorem exists_tensor {P : Subgroup H} (ρ : Representation F P W) {K : Set H} (hK : IsCompact K)
    (hPK : ∀ x, ∃ p : P, ∃ w ∈ K, x = p * w) (f : H → V ⊗[F] W)
    (hf : ∀ (p : P) x, f (p * x) = (ρ p).lTensor V (f x))
    (hs : ∀ᶠ u in nhds (1 : H), ∀ x, f (x * u) = f x) :
    ∃ t : V ⊗[F] smoothPart (ind P ρ), ∀ x, (ev ρ x).lTensor V t = f x := by
  classical
  let b := Module.Basis.ofVectorSpace F V
  have hlc : IsLocallyConstant f := by
    refine (IsLocallyConstant.iff_eventually_eq f).2 fun x => ?_
    have : Filter.Tendsto (fun y => x⁻¹ * y) (nhds x) (nhds 1) :=
      (continuous_const.mul continuous_id).tendsto' _ _ (by simp)
    filter_upwards [this.eventually hs] with y hy
    simpa using hy x
  have hfin : (f '' K).Finite := by
    haveI := isCompact_iff_compactSpace.1 hK
    rw [Set.image_eq_range]
    exact (hlc.comp_continuous continuous_subtype_val).range_finite
  choose s h1 h2 using exists_sum_coord (W := W) b
  let S := hfin.toFinset.biUnion s
  let c : ∀ i, smoothPart (ind P ρ) := fun i => ⟨⟨fun x => coord (b.coord i) W (f x), fun p x => by
      show coord _ W (f (p * x)) = _
      rw [hf, coord_lTensor]⟩, mem_smooth_of_eventually _ (hs.mono fun u hu x => by
      show coord _ W (f (x * u)) = _
      rw [hu])⟩
  refine ⟨∑ i ∈ S, b i ⊗ₜ c i, fun x => ?_⟩
  obtain ⟨p, w, hw, rfl⟩ := hPK x
  rw [hf, h2 (f w) S (Finset.subset_biUnion_of_mem s (hfin.mem_toFinset.2 ⟨w, hw, rfl⟩)), map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [LinearMap.lTensor_tmul, LinearMap.lTensor_tmul]
  exact congrArg _ ((c i).1.2 p w)

theorem smInd_stages {P Q : Subgroup G} (hPQ : P ≤ Q) {P' : Subgroup H} (π : Q →* M × H) (j : H →* Q)
    (hj : Continuous fun x => (j x : G)) (hπj : ∀ x, π (j x) = (1, x))
    (hP : ∀ q : Q, (q : G) ∈ P ↔ (π q).2 ∈ P') {K : Set H} (hK : IsCompact K)
    (hPK : ∀ x, ∃ p : P', ∃ w ∈ K, x = p * w) (D : M × H →* Fˣ)
    (hD : ∀ᶠ u in nhds (1 : H), D (1, u) = 1)
    (σ₀ : Representation F M V) (ρ : Representation F P' W) (σ : Representation F P U)
    (κ : V ⊗[F] W ≃ₗ[F] U)
    (hσ : ∀ (q : Q) (h1 : (q : G) ∈ P) (h2 : (π q).2 ∈ P') x, σ ⟨q, h1⟩ (κ x) =
      (D (π q) : F) • κ (TensorProduct.map (σ₀ (π q).1) (ρ ⟨_, h2⟩) x))
    (τ : Representation F Q (V ⊗[F] smoothPart (ind P' ρ)))
    (hτ : ∀ q x, τ q x = (D (π q) : F) • TensorProduct.map (σ₀ (π q).1) (smInd P' ρ (π q).2) x) :
    Nonempty ((smInd Q τ).Equiv (smInd P σ)) := by
  let ε : V ⊗[F] smoothPart (ind P' ρ) →ₗ[F] U := κ.toLinearMap ∘ₗ (ev ρ 1).lTensor V
  have hε : ∀ (q : Q) (h1 : (q : G) ∈ P) t, σ ⟨q, h1⟩ (ε t) = ε (τ q t) := by
    intro q h1 t
    show σ _ (κ _) = κ _
    rw [hσ q h1 ((hP q).1 h1), hτ, map_smul, map_smul]
    congr 2
    induction t with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul v f =>
      simp only [LinearMap.lTensor_tmul, TensorProduct.map_tmul]
      congr 1
      show _ = f.1.1 (1 * (π q).2)
      exact (f.1.2 ⟨_, (hP q).1 h1⟩ 1).symm.trans (by rw [one_mul, mul_one])
  have hεj : ∀ x t, ε (τ (j x) t) = (D (1, x) : F) • κ ((ev ρ x).lTensor V t) := by
    intro x t
    show κ _ = _
    rw [hτ, hπj, map_smul, map_smul]
    congr 2
    induction t with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul v f =>
      simp only [LinearMap.lTensor_tmul, TensorProduct.map_tmul, map_one, Module.End.one_apply]
      congr 1
      show f.1.1 (1 * x) = f.1.1 x
      rw [one_mul]
  have inj : ∀ t t', (∀ q, ε (τ q t) = ε (τ q t')) → t = t' := fun t t' h =>
    sub_eq_zero.1 (eq_zero_of_ev ρ _ fun x => by
      have := h (j x)
      rw [hεj, hεj] at this
      rw [map_sub, κ.injective (smul_right_injective U (D (1, x)).ne_zero this), sub_self])
  have surj : ∀ f : smoothPart (ind P σ), ∃ t, ∀ q : Q, ε (τ q t) = f.1.1 q := by
    intro f
    obtain ⟨t, ht⟩ := exists_tensor ρ hK hPK (fun x => (D (1, x) : F)⁻¹ • κ.symm (f.1.1 (j x)))
      (fun p x => by
        have h2 : (π (j p)).2 ∈ P' := by rw [hπj]; exact p.2
        have h3 := f.1.2 ⟨j p, (hP _).2 h2⟩ (j x)
        have h4 := hσ (j p) ((hP _).2 h2) h2 (κ.symm (f.1.1 (j x)))
        simp only [hπj, map_one, LinearEquiv.apply_symm_apply] at h4
        have h5 : D (1, (p : H) * x) = D (1, (p : H)) * D (1, x) := by rw [← map_mul]; simp
        simp only [map_mul, Subgroup.coe_mul, h5]
        rw [h3, h4, map_smul, map_smul, κ.symm_apply_apply, smul_smul]
        congr 1
        simp only [Units.val_mul]
        field_simp)
      (by
        filter_upwards [hD, (hj.tendsto' 1 1 (by simp)).eventually (eventually_of_smooth f)] with u h1 h2 x
        have h5 : D (1, x * u) = D (1, x) * D (1, u) := by rw [← map_mul]; simp
        simp only [map_mul, Subgroup.coe_mul, h5, h1, mul_one, h2])
    refine ⟨t, fun q => ?_⟩
    have hp : ((q * (j (π q).2)⁻¹ : Q) : G) ∈ P := (hP _).2 (by simp [hπj])
    have hq : q = (q * (j (π q).2)⁻¹) * j (π q).2 := by simp
    conv_lhs => rw [hq, map_mul, Module.End.mul_apply, ← hε _ hp, hεj, ht]
    conv_rhs => rw [hq, Subgroup.coe_mul]
    rw [f.1.2 ⟨_, hp⟩]
    simp [smul_smul]
  let Ψ : smoothPart (ind Q τ) →ₗ[F] smoothPart (ind P σ) :=
    indPull (MonoidHom.id G) continuous_id ε fun p => ⟨⟨p, hPQ p.2⟩, rfl, hε ⟨p, hPQ p.2⟩ p.2⟩
  refine ⟨Representation.IntertwiningMap.ofBijective ⟨Ψ, fun g => rfl⟩ ⟨?_, fun f => ?_⟩⟩
  · intro f f' h
    refine Subtype.ext (Subtype.ext (funext fun x => inj _ _ fun q => ?_))
    rw [← f.1.2, ← f'.1.2]
    exact congrFun (congrArg (fun φ => φ.1.1) h) (q * x)
  · choose t ht using fun g => surj (smInd P σ g f)
    have ht' : ∀ g (q : Q), ε (τ q (t g)) = f.1.1 (q * g) := ht
    refine ⟨⟨⟨t, fun q g => inj _ _ fun q' => ?_⟩, mem_smooth_of_eventually _
      ((eventually_of_smooth f).mono fun u hu x => inj _ _ fun q => ?_)⟩,
      Subtype.ext (Subtype.ext (funext fun x => ?_))⟩
    · rw [← Module.End.mul_apply, ← map_mul, ht', ht', Subgroup.coe_mul, mul_assoc]
    · show ε (τ q (t (x * u))) = ε (τ q (t x))
      rw [ht', ht', ← mul_assoc, hu]
    · show ε (t x) = _
      simpa using ht' x 1

end General

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {a b n a' b' n' : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype n] [DecidableEq n]
  [Fintype a'] [DecidableEq a'] [Fintype b'] [DecidableEq b'] [Fintype n'] [DecidableEq n']
  {V W U : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] [AddCommGroup U] [Module ℂ U]

def relabel (R : Type) [CommRing R] (e : a ≃ b) : GL a R ≃* GL b R :=
  Units.mapEquiv (Matrix.reindexAlgEquiv R R e).toMulEquiv

theorem relabel_apply {R : Type} [CommRing R] (e : a ≃ b) (g : GL a R) (i j : a) :
    (relabel R e g).val (e i) (e j) = g.val i j := by
  show g.val (e.symm (e i)) (e.symm (e j)) = _
  rw [e.symm_apply_apply, e.symm_apply_apply]

theorem continuous_relabel {R : Type} [CommRing R] [TopologicalSpace R] (e : a ≃ b) :
    Continuous (relabel R e) :=
  Units.continuous_iff.2 ⟨Units.continuous_val.matrix_submatrix _ _,
    Units.continuous_coe_inv.matrix_submatrix _ _⟩

theorem det_relabel {R : Type} [CommRing R] (e : a ≃ b) (g : GL a R) :
    GeneralLinearGroup.det (relabel R e g) = GeneralLinearGroup.det g :=
  Units.ext (det_reindex_self e g.val)

theorem isIrreducible_ind₂_iff (e : a ⊕ b ≃ n) (e' : a' ⊕ b' ≃ n') (ea : a ≃ a') (eb : b ≃ b')
    {ρ : Representation ℂ (GL a k × GL b k) V} {ρ' : Representation ℂ (GL a' k × GL b' k) W} (κ : V ≃ₗ[ℂ] W)
    (h : ∀ g v, κ (ρ g v) = ρ' (relabel k ea g.1, relabel k eb g.2) (κ v)) :
    (ind₂ e ρ).IsIrreducible ↔ (ind₂ e' ρ').IsIrreducible := by
  let en : n ≃ n' := e.symm.trans ((ea.sumCongr eb).trans e')
  have hen : ∀ (g : GL n k) x y, (relabel k en g).val (e' (Sum.map ea eb x)) (e' (Sum.map ea eb y)) =
      g.val (e x) (e y) := fun g x y => by
    rw [← relabel_apply en]
    simp [en]
  have hP : ∀ g, g ∈ parab k (two e) ↔ relabel k en g ∈ parab k (two e') := fun g => by
    rw [mem_parab_two, mem_parab_two, eb.surjective.forall]
    refine forall_congr' fun j => ?_
    rw [ea.surjective.forall]
    exact forall_congr' fun i => by rw [← hen g (.inr j) (.inl i)]; rfl
  refine isIrreducible_smInd_iff (relabel k en) (continuous_relabel en) (continuous_relabel en.symm) κ hP
    fun p v => ?_
  obtain ⟨x, h1⟩ := (leviTwo k a b).surjective (leviProj k (two e) p)
  have h2 : leviProj k (two e') ⟨_, (hP p).1 p.2⟩ = leviTwo k a' b' (relabel k ea x.1, relabel k eb x.2) := by
    funext y
    cases y
    · ext i j
      obtain ⟨i, rfl⟩ := ea.surjective i
      obtain ⟨j, rfl⟩ := ea.surjective j
      exact (hen p (.inl i) (.inl j)).trans ((congrArg (fun g : Levi k (Two a b) => (g false).val i j)
        h1).symm.trans (relabel_apply ea x.1 i j).symm)
    · ext i j
      obtain ⟨i, rfl⟩ := eb.surjective i
      obtain ⟨j, rfl⟩ := eb.surjective j
      exact (hen p (.inr i) (.inr j)).trans ((congrArg (fun g : Levi k (Two a b) => (g true).val i j)
        h1).symm.trans (relabel_apply eb x.2 i j).symm)
  show κ ((deltaHalf k _ (leviProj k (two e) p) : ℂ) • ρ ((leviTwo k a b).symm (leviProj k (two e) p)) v) =
    (deltaHalf k _ (leviProj k (two e') ⟨_, (hP p).1 p.2⟩) : ℂ) •
      ρ' ((leviTwo k a' b').symm (leviProj k (two e') ⟨_, (hP p).1 p.2⟩)) (κ v)
  rw [h2, ← h1, deltaHalf_two, deltaHalf_two, MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply, map_smul, h,
    det_relabel, det_relabel, Fintype.card_congr ea, Fintype.card_congr eb]

theorem isIrreducible_ind₂ (H : GlobalTheory.Published.BernsteinUnitaryProductIrreducible) (e : a ⊕ b ≃ n)
    {π₁ : Representation ℂ (GL a k) V} {π₂ : Representation ℂ (GL b k) W}
    (s₁ : IsSmooth π₁) (i₁ : π₁.IsIrreducible) (u₁ : IsUnitarisable π₁)
    (s₂ : IsSmooth π₂) (i₂ : π₂.IsIrreducible) (u₂ : IsUnitarisable π₂) :
    (ind₂ e (extTensor π₁ π₂)).IsIrreducible := by
  let ea := (Fintype.equivFin a).symm
  let eb := (Fintype.equivFin b).symm
  have := H k _ _ V W (π₁.comp (relabel k ea).toMonoidHom) (π₂.comp (relabel k eb).toMonoidHom)
    (isSmooth_comp s₁ _ (continuous_relabel ea))
    ((isIrreducible_iff_of_linearEquiv _ (relabel k ea).surjective (.refl ℂ V) fun _ _ => rfl).2 i₁)
    (UnitInd.isUnitarisable_comp u₁ _) (isSmooth_comp s₂ _ (continuous_relabel eb))
    ((isIrreducible_iff_of_linearEquiv _ (relabel k eb).surjective (.refl ℂ W) fun _ _ => rfl).2 i₂)
    (UnitInd.isUnitarisable_comp u₂ _)
  exact (isIrreducible_ind₂_iff _ e ea eb (.refl ℂ _) fun _ _ => rfl).1 this

theorem isIrreducible_ind₂Lower (H : GlobalTheory.Published.BernsteinUnitaryProductIrreducible) (e : a ⊕ b ≃ n)
    {π₁ : Representation ℂ (GL a k) V} {π₂ : Representation ℂ (GL b k) W}
    (s₁ : IsSmooth π₁) (i₁ : π₁.IsIrreducible) (u₁ : IsUnitarisable π₁)
    (s₂ : IsSmooth π₂) (i₂ : π₂.IsIrreducible) (u₂ : IsUnitarisable π₂) :
    (ind₂Lower e (extTensor π₁ π₂)).IsIrreducible := by
  obtain ⟨E⟩ := (SwapBlocks.lower_equiv_upper_swap k a b n e _).1 (extTensor π₁ π₂)
  refine (isIrreducible_iff_of_equiv E).2 ((isIrreducible_ind₂_iff _ _ (.refl b) (.refl a)
    (TensorProduct.comm ℂ W V) fun g x => ?_).1
      (isIrreducible_ind₂ H ((Equiv.sumComm b a).trans e) s₂ i₂ u₂ s₁ i₁ u₁))
  show _ = extTensor π₁ π₂ (g.2, g.1) _
  induction x with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul v w => simp

theorem exists_parab_mul {α : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ i, Fintype (m i)]
    [∀ i, DecidableEq (m i)] (e : (Σ i, m i) ≃ n) (x : GL n k) :
    ∃ p : parab k e, ∃ w ∈ (KO k n : Set (GL n k)), x = p * w := by
  obtain ⟨u, g, w, hw, rfl⟩ := UnitInd.exists_iwasawa e x
  exact ⟨⟨u * leviEmb k e g, mul_mem (unipRad_le_parab k _ u.2) (leviEmb_mem_parab k _ g)⟩, w, hw, rfl⟩

variable {s : ℕ} {m : Fin (s + 1) → Type} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)]

def headTail (m : Fin (s + 1) → Type) : m 0 ⊕ (Σ i : Fin s, m i.succ) ≃ Σ i, m i :=
  Equiv.ofBijective (Sum.elim (fun x => ⟨0, x⟩) fun y => ⟨y.1.succ, y.2⟩) ⟨by
    rintro (x | ⟨i, x⟩) (y | ⟨j, y⟩) h
    · simpa using h
    · exact absurd (congrArg Sigma.fst h) (Fin.succ_ne_zero _).symm
    · exact absurd (congrArg Sigma.fst h) (Fin.succ_ne_zero _)
    · obtain rfl : i = j := Fin.succ_injective _ (congrArg Sigma.fst h)
      simpa using h, by
    rintro ⟨i, x⟩
    induction i using Fin.cases with
    | zero => exact ⟨.inl x, rfl⟩
    | succ i => exact ⟨.inr ⟨i, x⟩, rfl⟩⟩

omit [∀ i, DecidableEq (m i)] in

theorem modExp_zero : modExp m 0 = Fintype.card (Σ i : Fin s, m i.succ) := by
  simp [modExp, Finset.sum_filter, Fin.sum_univ_succ]

omit [∀ i, DecidableEq (m i)] in

theorem modExp_succ (i : Fin s) :
    modExp m i.succ = -Fintype.card (m 0) + modExp (fun i : Fin s => m i.succ) i := by
  simp [modExp, Finset.sum_filter, Fin.sum_univ_succ]
  ring

theorem ind₂_parInd_equiv (e : (Σ i, m i) ≃ n) (σ₀ : Representation ℂ (GL (m 0) k) V)
    (ρ : Representation ℂ (Levi k fun i : Fin s => m i.succ) W) (σ : Representation ℂ (Levi k m) U)
    (κ : V ⊗[ℂ] W ≃ₗ[ℂ] U)
    (h : ∀ g x, σ g (κ x) = κ (TensorProduct.map (σ₀ (g 0)) (ρ fun i => g i.succ) x)) :
    Nonempty ((ind₂ ((headTail m).trans e) (extTensor σ₀ (parInd (Equiv.refl _) ρ))).Equiv (parInd e σ)) := by
  let e' := (headTail m).trans e
  let π := (leviTwo k (m 0) (Σ i : Fin s, m i.succ)).symm.toMonoidHom.comp (leviProj k (two e'))
  let j := ((emb₂ k e').comp (MonoidHom.inr _ _)).codRestrict (parab k (two e'))
    fun _ => leviEmb_mem_parab k _ _
  refine smInd_stages (P' := parab k (Equiv.refl (Σ i : Fin s, m i.succ))) (fun g hg => ?_) π j ?_
    (fun x => ?_) (fun q => ?_) SplitFlip.isCompact_KO (fun x => ?_)
    ((deltaHalf k _).comp (leviTwo k _ _).toMonoidHom) ?_ σ₀ _ _ κ (fun q h1 h2 x => ?_) _ fun q x => rfl
  · exact (mem_parab_two k).2 fun y x => mem_parab_iff.1 hg y.1.succ 0 y.2 x (Fin.succ_pos _)
  · exact (continuous_leviEmb k _).comp ((continuous_leviTwo k).comp (Continuous.prodMk_right 1))
  · exact (leviTwo k _ _).symm_apply_eq.2 (leviProj_leviEmb k _ _)
  · rw [mem_parab_iff, mem_parab_iff]
    refine ⟨fun hq x y u v hxy => hq x.succ y.succ u v (Fin.succ_lt_succ_iff.2 hxy), fun hq x y u v hxy => ?_⟩
    induction x using Fin.cases with
    | zero => exact absurd hxy (Fin.not_lt_zero _)
    | succ x =>
      induction y using Fin.cases with
      | zero => exact (mem_parab_two k).1 q.2 ⟨x, u⟩ v
      | succ y => exact hq x y u v (Fin.succ_lt_succ_iff.1 hxy)
  · exact exists_parab_mul _ x
  · have h1 : IsSmoothChar (((deltaHalf k _).comp
        (leviTwo k (m 0) (Σ i : Fin s, m i.succ)).toMonoidHom).comp (MonoidHom.inr _ _)) :=
      ((isSmoothChar_deltaHalf k).comp _ (continuous_leviTwo k)).comp _ (Continuous.prodMk_right 1)
    filter_upwards [h1.mem_nhds (one_mem _)] with u hu
    exact MonoidHom.mem_ker.1 hu
  · let g := leviProj k e ⟨q, h1⟩
    have e1 : (π q).1 = g 0 := Units.ext rfl
    have e2 : leviProj k _ ⟨(π q).2, h2⟩ = fun i : Fin s => g i.succ := funext fun _ => Units.ext rfl
    have e3 : GeneralLinearGroup.det (π q).2 = ∏ i : Fin s, GeneralLinearGroup.det (g i.succ) := by
      have := det_parab k _ ⟨(π q).2, h2⟩
      rwa [e2] at this
    have e4 : deltaHalf k m g = deltaHalf k _ (leviTwo k _ _ (π q)) *
        deltaHalf k (fun i : Fin s => m i.succ) fun i => g i.succ := by
      rw [deltaHalf_two, deltaHalf_apply, deltaHalf_apply, Fin.prod_univ_succ, e1, e3, map_prod, modExp_zero,
        mul_assoc, ← Finset.prod_mul_distrib]
      refine congrArg₂ _ (by simp) (Finset.prod_congr rfl fun i _ => ?_)
      rw [modExp_succ, ← MonoidHom.mul_apply, ← absPow_add]
      congr 2
      push_cast
      ring
    show (deltaHalf k m g : ℂ) • σ g (κ x) = (deltaHalf k _ (leviTwo k _ _ (π q)) : ℂ) •
      κ (TensorProduct.map (σ₀ (π q).1) ((deltaHalf k _ (leviProj k _ ⟨(π q).2, h2⟩) : ℂ) •
        ρ (leviProj k _ ⟨(π q).2, h2⟩)) x)
    rw [h, e4, e2, e1, TensorProduct.map_smul_right, LinearMap.smul_apply, map_smul, smul_smul, Units.val_mul]

def tensorCons (X : Fin (s + 1) → Type) [∀ i, AddCommGroup (X i)] [∀ i, Module ℂ (X i)] :
    X 0 ⊗[ℂ] (⨂[ℂ] i : Fin s, X i.succ) ≃ₗ[ℂ] ⨂[ℂ] i, X i :=
  LinearEquiv.ofLinear
    (TensorProduct.lift (PiTensorProduct.lift.toLinearMap ∘ₗ (PiTensorProduct.tprod ℂ).curryLeft))
    (PiTensorProduct.lift (LinearMap.uncurryLeft
      { toFun := fun x => (TensorProduct.mk ℂ _ _ x).compMultilinearMap (PiTensorProduct.tprod ℂ)
        map_add' := fun x y => by ext; simp [TensorProduct.add_tmul]
        map_smul' := fun c x => by ext; simp [TensorProduct.smul_tmul'] }))
    (by ext x; simp) (by ext x y; simp)

theorem tensorCons_tmul {X : Fin (s + 1) → Type} [∀ i, AddCommGroup (X i)] [∀ i, Module ℂ (X i)]
    (x : X 0) (y : ∀ i : Fin s, X i.succ) :
    tensorCons X (x ⊗ₜ PiTensorProduct.tprod ℂ y) = PiTensorProduct.tprod ℂ (Fin.cons x y) := by
  simp [tensorCons]

theorem multiProd_succ_equiv (e : (Σ i, m i) ≃ n) {X : Fin (s + 1) → Type} [∀ i, AddCommGroup (X i)]
    [∀ i, Module ℂ (X i)] (σ : ∀ i, Representation ℂ (GL (m i) k) (X i)) :
    Nonempty ((ind₂ ((headTail m).trans e)
      (extTensor (σ 0) (multiProd (Equiv.refl _) fun i : Fin s => σ i.succ))).Equiv (multiProd e σ)) := by
  refine ind₂_parInd_equiv e (σ 0) _ _ (tensorCons X) fun g x => ?_
  induction x with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul v w =>
    induction w using PiTensorProduct.induction_on with
    | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]
    | smul_tprod c y =>
      simp only [TensorProduct.tmul_smul, map_smul, TensorProduct.map_tmul, piTensor_tprod, tensorCons_tmul]
      congr 2
      funext i
      induction i using Fin.cases <;> rfl

theorem isIrreducible_multiProd_zero {m : Fin 0 → Type} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)]
    (e : (Σ i, m i) ≃ n) {X : Fin 0 → Type} [∀ i, AddCommGroup (X i)] [∀ i, Module ℂ (X i)]
    (σ : ∀ i, Representation ℂ (GL (m i) k) (X i)) : (multiProd e σ).IsIrreducible := by
  haveI : IsEmpty n := ⟨fun x => (e.symm x).1.elim0⟩
  haveI : Subsingleton (GL n k) := ⟨fun _ _ => Units.ext (Subsingleton.elim _ _)⟩
  let κ : IndSp e (piTensor σ) ≃ₗ[ℂ] ⨂[ℂ] i, X i := LinearEquiv.ofBijective (ev _ 1) ⟨fun f g h =>
    Subtype.ext (Subtype.ext (funext fun x => by rw [Subsingleton.elim x 1]; exact h)), fun v =>
    ⟨⟨⟨fun _ => v, fun p _ => by rw [Subsingleton.elim p 1, map_one]; rfl⟩,
      mem_smooth_of_eventually _ (.of_forall fun _ _ => rfl)⟩, rfl⟩⟩
  refine (isIrreducible_iff_of_linearEquiv (σ := ofChar (1 : GL n k →* ℂˣ)) id Function.surjective_id
    (κ.trans (PiTensorProduct.isEmptyEquiv _)) fun g v => ?_).2 (isIrreducible_ofChar _)
  rw [Subsingleton.elim g 1]
  simp

theorem isIrreducible_multiProd (H : GlobalTheory.Published.BernsteinUnitaryProductIrreducible) {s : ℕ} :
    ∀ {m : Fin s → Type} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] {n : Type} [Fintype n] [DecidableEq n]
    (e : (Σ i, m i) ≃ n) {X : Fin s → Type} [∀ i, AddCommGroup (X i)] [∀ i, Module ℂ (X i)]
    {σ : ∀ i, Representation ℂ (GL (m i) k) (X i)}, (∀ i, IsSmooth (σ i)) → (∀ i, (σ i).IsIrreducible) →
    (∀ i, IsUnitarisable (σ i)) → (multiProd e σ).IsIrreducible := by
  induction s with
  | zero => exact fun e _ _ _ σ _ _ _ => isIrreducible_multiProd_zero e σ
  | succ s ih =>
    intro m _ _ n _ _ e X _ _ σ hs hi hu
    obtain ⟨E⟩ := multiProd_succ_equiv e σ
    exact (isIrreducible_iff_of_equiv E).1 (isIrreducible_ind₂ H _ (hs 0) (hi 0) (hu 0) (isSmooth_parInd _ _)
      (ih _ (fun i => hs i.succ) (fun i => hi i.succ) fun i => hu i.succ)
      (UnitInd.isUnitarisable_multiProd _ fun i => hu i.succ))

end Local

theorem products_irreducible (H : GlobalTheory.Published.BernsteinUnitaryProductIrreducible)
    (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    (∀ (s : ℕ) (d : Fin s → ℕ) (n : Type) [Fintype n] [DecidableEq n] (e : (Σ a, Fin (d a)) ≃ n)
      (X : Fin s → Type) [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)]
      (σ : ∀ a, Representation ℂ (GL (Fin (d a)) k) (X a)),
      (∀ a, IsSmooth (σ a)) → (∀ a, (σ a).IsIrreducible) → (∀ a, IsUnitarisable (σ a)) →
      IsSmooth (multiProd e σ) ∧ (multiProd e σ).IsIrreducible ∧ IsUnitarisable (multiProd e σ)) ∧
    ∀ (a b n : Type) [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype n] [DecidableEq n]
      (e : a ⊕ b ≃ n) (V W : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
      (π₁ : Representation ℂ (GL a k) V) (π₂ : Representation ℂ (GL b k) W),
      IsSmooth π₁ → π₁.IsIrreducible → IsUnitarisable π₁ →
      IsSmooth π₂ → π₂.IsIrreducible → IsUnitarisable π₂ →
      (ind₂ e (extTensor π₁ π₂)).IsIrreducible ∧ (ind₂Lower e (extTensor π₁ π₂)).IsIrreducible :=
  ⟨fun _ _ _ _ _ e _ _ _ _ hs hi hu => ⟨isSmooth_parInd _ _, isIrreducible_multiProd H e hs hi hu,
      UnitInd.isUnitarisable_multiProd e hu⟩,
    fun _ _ _ _ _ _ _ _ _ e _ _ _ _ _ _ _ _ s₁ i₁ u₁ s₂ i₂ u₂ =>
      ⟨isIrreducible_ind₂ H e s₁ i₁ u₁ s₂ i₂ u₂, isIrreducible_ind₂Lower H e s₁ i₁ u₁ s₂ i₂ u₂⟩⟩

end GlobalTheory.SmGL.MultiIrr
