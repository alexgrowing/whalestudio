import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.ColValMonomial
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SubstMapAlgebraMap
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.InvariantDerivAlongEndo
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MapDofIterate
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsFormalBiextMap
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.GermEvalOneStandardPointSelf
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.IsNilpotentOfMemKerJetTruncR
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsGoodConst
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsExtensionPullOver
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.DualLiftInjective

noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj MvPowerSeries
open ReciprocityTheory.ChartRestriction.G.Chart ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.JetSer
open ReciprocityTheory.ChartRestriction.G.Out (scal resTop)
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (IsGrpPullback pushHom isGrpPullback_pullback)
open ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.EigenGerm

section Values

variable {A R : Type} [CommRing A] [CommRing R] {X : Scheme.{0}}

theorem fnVal_const (p : Spec (CommRingCat.of A) ⟶ X) (π : X ⟶ Spec (CommRingCat.of R)) (θ : R →+* A)
    (hp : p ≫ π = Spec.map (CommRingCat.ofHom θ)) (U : X.Opens) (h : ⊤ ≤ p ⁻¹ᵁ U) (c : R) :
    fnVal p U (resTop U (scal π c)) = θ c := by
  refine (fnVal_res p U ⊤ le_top h _).2.symm.trans ?_
  refine (ChartBaseChange.fnVal_comp p π ⊤ _).trans ?_
  rw [hp, ← Category.comp_id (Spec.map _), fnVal_specMap θ _ ⊤ le_top]
  congr 1
  unfold fnVal
  rw [dif_pos (show ⊤ ≤ (𝟙 (Spec (CommRingCat.of R)) : _ ⟶ _) ⁻¹ᵁ ⊤ from le_top)]
  have e : (𝟙 (Spec (CommRingCat.of R)) : _ ⟶ _).appLE ⊤ ⊤ le_top = 𝟙 _ := by
    simp [Scheme.Hom.appLE]
  rw [e]
  exact congrArg (fun q => q.hom c) (Scheme.ΓSpecIso (CommRingCat.of R)).inv_hom_id

variable {G : Over (Spec (CommRingCat.of R))} {d : ℕ} {x : Fam G (Fin d)} {U : G.left.Opens}

theorem exists_evHom {m n : ℕ} {a : Fin m → Pt R n d} (ha : ∀ j i, constantCoeff (a j i) = 0) :
    ∃ Ψ : PS R m d →ₐ[R] PS R n d, ∀ f, ev a f = Ψ f :=
  ⟨MvPowerSeries.substAlgHom (R := R) (FBMap.hasSubst_of ha),
    fun f => (congrFun (MvPowerSeries.coe_substAlgHom (FBMap.hasSubst_of ha)) f).symm⟩

theorem isSer1_mul (hJ : JetAlgSt) {f f' : Γ(G.left, U)} {g g' : PS R 1 d} (h : IsSer1 x U f g)
    (h' : IsSer1 x U f' g') : IsSer1 x U (f * f') (g * g') := by
  intro n a y hy m
  obtain ⟨τ, hτ, -⟩ := (hJ R (Fin n × Fin d)).1 m
  obtain ⟨Ψ, hΨ⟩ := exists_evHom (a := ![a]) (single_point_zero_constant hy.1)
  obtain ⟨h₁, h₂⟩ := h n a y hy m
  obtain ⟨-, h₃⟩ := h' n a y hy m
  refine ⟨h₁, ?_⟩
  rw [fnVal_eq_fnValHom _ _ h₁] at h₂ h₃ ⊢
  rw [map_mul, h₂, h₃, hΨ, hΨ, hΨ, map_mul, ← hτ, ← hτ, ← hτ, map_mul]

theorem isSer1_mul_pow (hJ : JetAlgSt) {f f' : Γ(G.left, U)} {g g' : PS R 1 d} (h : IsSer1 x U f g)
    (h' : IsSer1 x U f' g') (k : ℕ) : IsSer1 x U (f * f' ^ k) (g * g' ^ k) := by
  induction k with
  | zero => simpa only [pow_zero, _root_.mul_one] using h
  | succ k ih =>
    rw [pow_succ, pow_succ, ← _root_.mul_assoc, ← _root_.mul_assoc]
    exact isSer1_mul hJ ih h'

theorem isSer1_res {W : G.left.Opens} (hle : U ≤ W) {f : Γ(G.left, W)} {g : PS R 1 d}
    (h : IsSer1 x U ((G.left.presheaf.map (homOfLE hle).op).hom f) g) : IsSer1 x W f g := by
  intro n a y hy m
  obtain ⟨h₁, h₂⟩ := h n a y hy m
  obtain ⟨h₃, h₄⟩ := fnVal_res _ U W hle h₁ f
  exact ⟨h₃, h₄.trans h₂⟩

end Values

section BaseChange

variable {V R : Type} [CommRing V] [CommRing R] [Algebra V R]

theorem dof_baseChange (hJ : JetAlgSt) (hRep : RepSt) (hSer : SerSt) [IsLocalRing V]
    {G : Over (Spec (CommRingCat.of V))} [GrpObj G] {d : ℕ} {x : Fam G (Fin d)} (hx : IsUnivChart G d x)
    (Gl : FGLaw V d) (hGl : IsLawOf x Gl.F) {U : G.left.Opens} (hU : ⊤ ≤ η[G].left ⁻¹ᵁ U) {l : ℕ}
    (s : Fin l → Γ(G.left, U)) (S : Fin l → PS V 1 d) (hS : ∀ i, IsSer1 x U (s i) (S i)) (c : Fin l → R)
    (v : Fin d → R) (y : R) (φ : JetR V (Fin d) 1 →ₐ[V] DualNumber R)
    (hφ : ∀ i, φ (zR 1 i) = TrivSqZeroExt.inr (v i))
    (H : ∀ (A : Type) [CommRing A] [Algebra V A] (θ : DualNumber R →ₐ[V] A) (r : sp (R₀ := V) A ⟶ G),
      ⊤ ≤ r.left ⁻¹ᵁ U → ⊤ ≤ (r * (spMap θ ≫ spMap φ ≫ x 1)).left ⁻¹ᵁ U →
      ∑ i, θ (TrivSqZeroExt.inl (c i)) * fnVal (r * (spMap θ ≫ spMap φ ≫ x 1)).left U (s i) =
        θ (1 + TrivSqZeroExt.inr y) * ∑ i, θ (TrivSqZeroExt.inl (c i)) * fnVal r.left U (s i)) :
    Dof (fun i => MvPowerSeries.map (algebraMap V R) (Gl.F i)) v
        (∑ i, C (c i) * MvPowerSeries.map (algebraMap V R) (S i)) =
      C y * ∑ i, C (c i) * MvPowerSeries.map (algebraMap V R) (S i) := by
  let G' := (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap V R)))).obj G
  let π : G'.left ⟶ G.left := pullback.fst _ _
  have hπ : IsGrpPullback G' G (Spec.map (CommRingCat.ofHom (algebraMap V R))) π := isGrpPullback_pullback _ _
  choose x' hx' using fun m => ChartBaseChange.push_surjective hπ
    (spMap (ChartBaseChange.jetCoeff V R (Fin d) m) ≫ x m)
  have hx'' := ChartBaseChange.isUnivChart_baseChange hπ hx hx'
  have hlaw : IsLawOf x' (FBMap.mapLaw (algebraMap V R) Gl).F := by
    refine ⟨fun i => ChartBaseChange.const_map (hGl.1 i), fun n a b y z hy hz => ?_⟩
    obtain ⟨Θ, t, hΘ, ht, e⟩ := ChartBaseChange.exists_move hπ hJ hx' ![a, b] ![y, z]
      (fun i => by fin_cases i; exacts [hy, hz])
    have H := hGl.2 2 _ _ _ _ (ht 0) (ht 1)
    have hFe : addOf Gl.F (pt V (n := 2) d 0) (pt V d 1) = Gl.F := funext fun i => ChartBaseChange.eval_standard_points_two _
    rw [hFe] at H
    refine (ChartBaseChange.rep_iff hπ hJ hx' (pair_points_zero_constant hy.1 hz.1) hΘ H _).2 fun m => ?_
    rw [ChartBaseChange.push_mul, MonObj.comp_mul, ← e 0 m, ← e 1 m]
    rfl
  have hser : ∀ i, IsSer1 x' (π ⁻¹ᵁ U) ((π.app U).hom (s i)) (MvPowerSeries.map (algebraMap V R) (S i)) := by
    intro i n a y hy
    obtain ⟨Θ, t, hΘ, ht, e⟩ := ChartBaseChange.exists_move hπ hJ hx' ![a] ![y] (fun i => by fin_cases i; exact hy)
    have H := hS i 1 _ _ (ht 0)
    rw [ChartBaseChange.germEval_oneStandardPoint_self] at H
    exact ChartBaseChange.hasSer_move hΘ π _ _ (fun m => congrArg (fun k => k.left) (e 0 m)) U _ _ H
  have hη : η[G'].left ≫ π = Spec.map (CommRingCat.ofHom (algebraMap V R)) ≫ η[G].left := by
    have e := congrArg (fun z => z.left) (map_one (pushHom hπ (𝟙_ _)))
    have e₁ : (1 : 𝟙_ _ ⟶ G') = η[G'] := by rw [Hom.one_def]; simp
    rw [e₁] at e
    refine e.trans ?_
    show (toUnit _ ≫ η[G]).left = _
    simp
  have hU' : ⊤ ≤ η[G'].left ⁻¹ᵁ (π ⁻¹ᵁ U) := by
    show ⊤ ≤ (η[G'].left ≫ π) ⁻¹ᵁ U
    rw [hη]
    exact top_le_preimage_comp _ _ U hU
  have val : ∀ (A : Type) [CommRing A] [Algebra R A] (r : sp (R₀ := R) A ⟶ G'), ⊤ ≤ r.left ⁻¹ᵁ (π ⁻¹ᵁ U) →
      fnVal r.left (π ⁻¹ᵁ U) (∑ i, resTop _ (scal G'.hom (c i)) * (π.app U).hom (s i)) =
        ∑ i, algebraMap R A (c i) * fnVal r.left (π ⁻¹ᵁ U) ((π.app U).hom (s i)) := by
    intro A _ _ r hr
    rw [fnVal_eq_fnValHom _ _ hr, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, ← fnVal_eq_fnValHom _ _ hr, ← fnVal_eq_fnValHom _ _ hr,
      fnVal_const r.left G'.hom (algebraMap R A) (Over.w r) _ hr]
  have hcomb : IsSer1 x' (π ⁻¹ᵁ U) (∑ i, resTop _ (scal G'.hom (c i)) * (π.app U).hom (s i))
      (∑ i, C (c i) * MvPowerSeries.map (algebraMap V R) (S i)) := by
    intro n a y hy m
    obtain ⟨τ, hτ, -⟩ := (hJ R (Fin n × Fin d)).1 m
    obtain ⟨Ψ, hΨ⟩ := exists_evHom (a := ![a]) (single_point_zero_constant hy.1)
    obtain ⟨hc, h0⟩ := (hRep R G' d x' hx'' (Fin n × Fin d)).2.2.1 a y hy
    have h₁ : ⊤ ≤ (y m).left ⁻¹ᵁ (π ⁻¹ᵁ U) := by
      refine top_le_preimage_of_nil (jetAug R (Fin n × Fin d) m).toRingHom
        (fun b => ⟨algebraMap R _ b, (jetAug R (Fin n × Fin d) m).commutes b⟩)
        (fun b hb => ⟨m + 1, ?_⟩) _ _ ?_
      · have : b ^ (m + 1) ∈ (RingHom.ker (jetAug R (Fin n × Fin d) m)) ^ (m + 1) := Ideal.pow_mem_pow hb _
        rwa [ker_jetAug_pow] at this
      · show ⊤ ≤ (spMap (jetAug R (Fin n × Fin d) m) ≫ y m).left ⁻¹ᵁ (π ⁻¹ᵁ U)
        rw [h0 m]
        exact top_le_preimage_comp (toUnit _ : sp (R₀ := R) R ⟶ _).left _ _ hU'
    refine ⟨h₁, (val _ (y m) h₁).trans ?_⟩
    rw [hΨ, map_sum, ← hτ, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, map_mul, ← hΨ (MvPowerSeries.map _ _), hτ (ev _ _), ← (hser i n a y hy m).2]
    congr 1
    exact ((congrArg τ (Ψ.commutes (c i))).trans (τ.commutes (c i))).symm
  refine EigenDer.dof_eq_of_eigen hJ hRep hSer R G' d x' hx'' (FBMap.mapLaw (algebraMap V R) Gl) hlaw _ hU' _ _ hcomb
    v y (dualLift v) (dualLift_zR v) fun A _ _ θ r h₁ h₂ => ?_
  letI : Algebra V A := ((algebraMap R A).comp (algebraMap V R)).toAlgebra
  haveI : IsScalarTower V R A := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have e₀ : ((dualLift v).restrictScalars V).comp (ChartBaseChange.jetCoeff V R (Fin d) 1) = φ :=
    jet_ext fun j => by
      rw [hφ, AlgHom.comp_apply, ChartBaseChange.jetCoeff_zR]
      exact dualLift_zR v j
  have e₁ : ChartBaseChange.push hπ (r * (spMap θ ≫ spMap (dualLift v) ≫ x' 1)) =
      ChartBaseChange.push hπ r * (spMap (θ.restrictScalars V) ≫ spMap φ ≫ x 1) := by
    rw [ChartBaseChange.push_mul, ChartBaseChange.push_spMap, ChartBaseChange.push_spMap, hx', ← e₀]
    congr 2
    rw [← Category.assoc]
    congr 1
    apply Over.OverMorphism.ext
    simp only [Over.comp_left, spMap_left]
    rw [← Spec.map_comp]
    rfl
  have := H A (θ.restrictScalars V) (ChartBaseChange.push hπ r) h₁ (by rw [← e₁]; exact h₂)
  rw [← e₁] at this
  rw [val _ _ h₁, val _ _ h₂]
  simp only [ChartBaseChange.fnVal_comp]
  have e₂ : ∀ i, (θ.restrictScalars V) (TrivSqZeroExt.inl (c i)) = algebraMap R A (c i) := fun i => θ.commutes (c i)
  simp only [e₂] at this
  exact this

end BaseChange

section Algebra

variable {d : ℕ} {𝒪 : Type} [CommRing 𝒪] [StarRing 𝒪]

theorem dof_ev_eq_zero {R : Type} [CommRing R] (B : FB R d 𝒪) (a : 𝒪) (u : Fin d → R)
    (hu : (dLin (B.A.act a)).mulVec u = 0) (g : PS R 1 d) : Dof B.G.F u (ev (n := 1) ![B.A.act a] g) = 0 := by
  have hom := B.A.hom a
  rw [FGLaw.add, FGLaw.add, QuadDeriv.addOf_pt] at hom
  rw [DerivEndo.dof_endo B.G.F B.G.const (congrFun (QuadDeriv.unit_right B.G)) (B.A.act a) (B.A.const a) hom, hu]
  obtain ⟨Ψ, hΨ⟩ := exists_evHom (a := ![B.A.act a]) (single_point_zero_constant (B.A.const a))
  have := DerivEndo.dof_smul_dir B.G.F 0 u g
  rw [zero_smul, map_zero, zero_mul] at this
  rw [this, hΨ, map_zero]

theorem dLin_map {R S : Type} [CommRing R] [CommRing S] (β : R →+* S) (φ : Pt R 1 d) :
    dLin (fun i => MvPowerSeries.map β (φ i) : Pt S 1 d) = (dLin φ).map β := by
  ext i j
  simp [dLin]

theorem coeff_dof_sub_mem {V O F : Type} [CommRing V] [CommRing O] [CommRing F] [Algebra ℚ F] [Algebra V F]
    (β : V →+* O) (io : O →+* F) (hio : Function.Injective io) (hβ : io.comp β = algebraMap V F) (I : Ideal O)
    (B : FB V d 𝒪) (a : 𝒪) (e : Fin d → O) (α yy : O) (hα : α ∈ I)
    (he : (dAct F B a).mulVec (fun i => io (e i)) = io α • fun i => io (e i)) (S : PS O 1 d)
    (hS : Dof (fun i => MvPowerSeries.map ((Ideal.Quotient.mk I).comp β) (B.G.F i))
        (fun i => Ideal.Quotient.mk I (e i)) (MvPowerSeries.map (Ideal.Quotient.mk I) S) =
      C (Ideal.Quotient.mk I yy) * MvPowerSeries.map (Ideal.Quotient.mk I) S)
    (r : PS V 1 d) (κ : V) (k : ℕ) (f : PS F 1 d)
    (hf : f = C (algebraMap V F κ) * MvPowerSeries.map io S *
      MvPowerSeries.map (algebraMap V F) (ev (n := 1) ![B.A.act a] r) ^ k) (mo) :
    ∃ x ∈ I, coeff mo (Dof (B.FK F) (fun i => io (e i)) f - C (io yy) * f) = io x := by
  let q := Ideal.Quotient.mk I
  let fO : PS O 1 d := C (β κ) * S * MvPowerSeries.map β (ev (n := 1) ![B.A.act a] r) ^ k
  have mm : ∀ {n : ℕ} {T : Type} [CommRing T] (ga : O →+* T) (g : PS V n d),
      MvPowerSeries.map ga (MvPowerSeries.map β g) = MvPowerSeries.map (ga.comp β) g := fun ga g => by
    ext m; simp
  have h₁ : f = MvPowerSeries.map io fO := by
    rw [hf, map_mul, map_mul, map_pow, mm, hβ, MvPowerSeries.map_C, ← hβ]; rfl
  have h₂ : Dof (B.FK F) (fun i => io (e i)) f - C (io yy) * f =
      MvPowerSeries.map io (Dof (fun i => MvPowerSeries.map β (B.G.F i)) e fO - C yy * fO) := by
    rw [map_sub, map_mul, InvDerMap.map_Dof, MvPowerSeries.map_C, ← h₁]
    simp only [mm, hβ]
    rfl
  refine ⟨coeff mo (Dof (fun i => MvPowerSeries.map β (B.G.F i)) e fO - C yy * fO), ?_, by rw [h₂, coeff_map]⟩
  have hO : ((dLin (B.A.act a)).map β).mulVec e = α • e := by
    funext i
    apply hio
    have := congrFun he i
    have e₁ : dAct F B a = ((dLin (B.A.act a)).map β).map io := by
      rw [Matrix.map_map, ← RingHom.coe_comp, hβ, ← dLin_map]; rfl
    rw [e₁] at this
    rw [RingHom.map_mulVec]
    exact this.trans (map_mul io _ _).symm
  have h₃ : Dof (fun i => MvPowerSeries.map (q.comp β) (B.G.F i)) (fun i => q (e i))
      (MvPowerSeries.map (q.comp β) (ev (n := 1) ![B.A.act a] r)) = 0 := by
    rw [FBMap.map_ev1 _ (B.A.const a)]
    refine dof_ev_eq_zero (FBMap.mapFB (q.comp β) B) a _ ?_ _
    show (dLin (fun i => MvPowerSeries.map (q.comp β) (B.A.act a i) : Pt (O ⧸ I) 1 d)).mulVec _ = 0
    rw [dLin_map]
    funext i
    have := congrArg q (congrFun hO i)
    rw [RingHom.map_mulVec, Matrix.map_map, Pi.smul_apply, smul_eq_mul, map_mul,
      Ideal.Quotient.eq_zero_iff_mem.2 hα, zero_mul] at this
    exact this
  have h₄ : ∀ n : ℕ, Dof (fun i => MvPowerSeries.map (q.comp β) (B.G.F i)) (fun i => q (e i))
      (MvPowerSeries.map (q.comp β) (ev (n := 1) ![B.A.act a] r) ^ n) = 0 := fun n => by
    induction n with
    | zero => rw [pow_zero, ← map_one (C : _ →+* PS (O ⧸ I) 1 d), GE.dof_C]
    | succ n ih => rw [pow_succ, GE.dof_mul, ih, h₃, mul_zero, mul_zero, add_zero]
  rw [← Ideal.Quotient.eq_zero_iff_mem, ← coeff_map, map_sub, map_mul, InvDerMap.map_Dof, MvPowerSeries.map_C]
  simp only [fO, mm, map_mul, map_pow, MvPowerSeries.map_C]
  rw [GE.dof_mul, h₄, GE.dof_C_mul, hS]
  have : ∀ a b c e : PS (O ⧸ I) 1 d, a * b * 0 + c * (a * (e * b)) - e * (a * b * c) = 0 := fun a b c e => by ring
  rw [this, map_zero]

end Algebra

end GlobalTheory.EigenGerm
