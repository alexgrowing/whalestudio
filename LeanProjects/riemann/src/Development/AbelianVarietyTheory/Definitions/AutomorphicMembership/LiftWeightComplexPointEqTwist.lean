import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ConcretePkgSpec
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.ONLeaves
import Formalism.LocalToGlobal.Divisibility.LiftLatLemmas
import Formalism.LocalRingCardinality.DataParams

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Module

namespace GlobalTheory.OntoChain

open Formalism.BasicNotions Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx

section Roots

variable {K G : Type} [Field K] [NumberField K] [Group G] [Finite G]

omit [NumberField K] in

theorem isIntegral_char (χ : G →* Kˣ) (g : G) : IsIntegral ℤ ((χ g : Kˣ) : K) := by
  refine IsIntegral.of_pow (n := orderOf g) (orderOf_pos g) ?_
  rw [← Units.val_pow_eq_pow_val, ← map_pow, pow_orderOf_eq_one, map_one, Units.val_one]
  exact isIntegral_one

end Roots

section Twisted

variable {LL Ks : Type} [Field LL] [NumberField LL] [Field Ks] [NumberField Ks] [Algebra Ks LL] {n : ℕ}
variable {W : (LL →+* ℂ) → Type} [∀ σ, NormedAddCommGroup (W σ)] [∀ σ, InnerProductSpace ℂ (W σ)]
variable {G : Type} [Group G] [Fintype G] (A : Arith.FormsL LL Ks (Fin n → LL) W G)

def twRep : Representation LL G (Fin n → LL) where
  toFun g := (((A.chi g)⁻¹ : LLˣ) : LL) • A.ρ g
  map_one' := by rw [map_one, map_one, inv_one, Units.val_one, one_smul]
  map_mul' g h := by
    rw [map_mul, map_mul, mul_inv, Units.val_mul, smul_mul_smul_comm]

omit [Fintype G] in
theorem twRep_apply (g : G) (x : Fin n → LL) : twRep A g x = (((A.chi g)⁻¹ : LLˣ) : LL) • A.ρ g x := rfl

omit [Fintype G] in

theorem twRep_of_chi_eq_one {g : G} (h : A.chi g = 1) : twRep A g = A.ρ g := by
  show (((A.chi g)⁻¹ : LLˣ) : LL) • A.ρ g = _
  rw [h, inv_one, Units.val_one, one_smul]

theorem eOp_eq (a : MonoidAlgebra LL G) : A.eOp (fun g => a.coeff g) = (twRep A).asAlgebraHom a := by
  classical
  have ha : a = ∑ g : G, MonoidAlgebra.single g (a.coeff g) := by
    ext g
    simp [MonoidAlgebra.coeff_sum, Finsupp.finset_sum_apply, Finsupp.single_apply]
  conv_rhs => rw [ha]
  rw [map_sum]
  unfold Arith.FormsL.eOp
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [Representation.asAlgebraHom_single, mul_smul]
  rfl

omit [Fintype G] in

theorem mem_eigenspace_iff₂ (J : Subgroup G) (lam : J →* LLˣ) (x : Fin n → LL) :
    x ∈ A.typeP J lam ↔ ∀ p : J, twRep A p x = ((lam p : LLˣ) : LL) • x := by
  show (∀ p : J, A.ρ p x = ((A.chi p * lam p : LLˣ) : LL) • x) ↔ _
  refine forall_congr' fun p => ?_
  rw [twRep_apply, Units.val_mul, mul_smul]
  constructor
  · intro h
    rw [h, smul_smul, Units.inv_mul, one_smul]
  · intro h
    rw [← h, smul_smul, Units.mul_inv, one_smul]

def supLat : Submodule (𝓞 LL) (Fin n → LL) := Submodule.span (𝓞 LL) (A.MK : Set (Fin n → LL))

omit [Fintype G] in

theorem supLat_isLatIn (h1 : A.IsKsForm) (h2 : A.MKFull) : IsLatIn ⊤ (supLat A) := by
  constructor
  · obtain ⟨s, hs⟩ := h2.1
    refine ⟨s, le_antisymm (Submodule.span_mono ?_) (Submodule.span_le.2 fun x hx => ?_)⟩
    · rw [← hs]; exact Submodule.subset_span
    · rw [← hs] at hx
      induction hx using Submodule.span_induction with
      | mem x hx => exact Submodule.subset_span hx
      | zero => exact Submodule.zero_mem _
      | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
      | smul a x _ hx =>
        have : a • x = (algebraMap (𝓞 Ks) (𝓞 LL) a) • x := by
          funext i
          simp only [Pi.smul_apply, Algebra.smul_def]
          rfl
        rw [this]; exact Submodule.smul_mem _ _ hx
  · obtain ⟨m, b, hb, -, -, -, htop⟩ := h1
    rw [eq_top_iff, ← htop]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨i, rfl⟩
    have hi := hb i
    rw [← h2.2] at hi
    refine Submodule.span_induction (p := fun x _ => x ∈ Submodule.span LL (supLat A : Set (Fin n → LL)))
      (fun x hx => Submodule.subset_span (Submodule.subset_span hx)) (Submodule.zero_mem _)
      (fun x y _ _ hx hy => Submodule.add_mem _ hx hy) (fun a x _ hx => ?_) hi
    rw [← algebraMap_smul LL a x]
    exact Submodule.smul_mem _ _ hx

theorem supLat_stable (h : A.MKStable) (g : G) :
    (supLat A).map ((twRep A g).restrictScalars (𝓞 LL)) ≤ supLat A := by
  unfold supLat
  rw [Submodule.map_span, Submodule.span_le]
  rintro _ ⟨x, hx, rfl⟩
  have e : ((twRep A g).restrictScalars (𝓞 LL)) x =
      (⟨_, isIntegral_char A.chi⁻¹ g⟩ : 𝓞 LL) • A.ρ g x := rfl
  rw [e]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ((h g x).2 hx))

end Twisted

section Block

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 : Type}
  {B : BlockDat K G Pl0} {ℓ : Lvl K G} {Z : Submodule K B.S.Forms} {v0 : InfinitePlace K} {s : ℕ}

theorem lPr_mul_lvlOp (h : BlockHyp B ℓ v0 s) :
    B.lPr ℓ Z * B.S.lvlOp B.r ℓ.P ℓ.ψ (idemOf ℓ.X) = B.lPr ℓ Z := by
  have hc := idempotent_central K G ℓ.X h.irr
  have h1 := (level_operator_spec K v0 h.conj B.S (h.ok.hpos v0) G B.r h.ok.act ℓ.P ℓ.ψ (idemOf ℓ.X) (hc.2 _).symm).1
  obtain ⟨⟨h2, -⟩, h3⟩ := BlockDat.lf_v_proj h
  have h4 : goodAt ℓ.X ℓ.P ℓ.ψ * idemOf ℓ.X = goodAt ℓ.X ℓ.P ℓ.ψ := by
    unfold goodAt
    rw [mul_assoc, hc.2, ← mul_assoc, hc.1]
  have h5 : B.vPr ℓ * B.S.gaMat B.r (idemOf ℓ.X) = B.vPr ℓ := by
    calc B.vPr ℓ * B.S.gaMat B.r (idemOf ℓ.X)
        = B.vPr ℓ * B.vE ℓ * B.vPr ℓ * B.S.gaMat B.r (idemOf ℓ.X) := by rw [h2, Matrix.one_mul]
      _ = B.vPr ℓ * (B.vE ℓ * B.vPr ℓ * B.S.gaMat B.r (idemOf ℓ.X)) := by simp only [Matrix.mul_assoc]
      _ = B.vPr ℓ * (B.vE ℓ * B.vPr ℓ) := by rw [h3, ← (group_action_matrix_hom K B.S G B.r).2, h4]
      _ = B.vPr ℓ := by rw [← Matrix.mul_assoc, h2, Matrix.one_mul]
  unfold BlockDat.lPr
  rw [Matrix.mul_assoc, h1, ← Matrix.mul_assoc, Matrix.mul_assoc (B.Pq ℓ Z), h5]

end Block

section Local

variable {k : Type} [Field k] {r n : ℕ}

def glCast (hr : r = n + 1) : GL (Fin (n + 1)) k ≃* GL (Fin r) k :=
  Units.mapEquiv (Matrix.reindexAlgEquiv k k (finCongr hr.symm)).toMulEquiv

theorem glCast_apply (hr : r = n + 1) (h : GL (Fin (n + 1)) k) (i j : Fin r) :
    (glCast hr h : Matrix (Fin r) (Fin r) k) i j =
      (h : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.cast hr i) (Fin.cast hr j) := rfl

theorem glCast_mem_unip (hr : r = n + 1) (h : GL (Fin (n + 1)) k) :
    glCast hr h ∈ unip k r ↔ IsUniU (h : Matrix (Fin (n + 1)) (Fin (n + 1)) k) := by
  subst hr
  exact ⟨fun hh => ⟨hh.2, fun _ _ hij => hh.1 hij⟩, fun hh => ⟨fun i j hij => hh.2 i j hij, hh.1⟩⟩

theorem edgeSum_glCast (hr : r = n + 1) (h : GL (Fin (n + 1)) k) :
    edgeSum supEdge (glCast hr h) = supd (h : Matrix (Fin (n + 1)) (Fin (n + 1)) k) := by
  subst hr
  show (∑ i : Fin (n + 1), ∑ j : Fin (n + 1), if j.val = i.val + 1 then
    (h : Matrix (Fin (n + 1)) (Fin (n + 1)) k) i j else 0) = _
  unfold supd
  rw [Fin.sum_univ_castSucc]
  have h0 : (∑ j : Fin (n + 1), if j.val = (Fin.last n).val + 1 then
      (h : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.last n) j else 0) = 0 :=
    Finset.sum_eq_zero fun j _ => if_neg (by have := j.2; simp; omega)
  rw [h0, add_zero]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i.succ]
  · simp
  · intro j _ hj
    exact if_neg fun h => hj (Fin.ext (by simpa using h))
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem exists_uni_supd (hn : 0 < n) (a : k) :
    ∃ u : GL (Fin (n + 1)) k, IsUniU (u : Matrix (Fin (n + 1)) (Fin (n + 1)) k) ∧
      supd (u : Matrix (Fin (n + 1)) (Fin (n + 1)) k) = a := by
  let i0 : Fin n := ⟨0, hn⟩
  have hne : i0.castSucc ≠ i0.succ := (Fin.castSucc_lt_succ (i := i0)).ne
  have hdet : (Matrix.transvection i0.castSucc i0.succ a).det ≠ 0 := by
    rw [Matrix.det_transvection_of_ne _ _ hne]; exact one_ne_zero
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdet, ⟨fun i => ?_, fun i j hij => ?_⟩, ?_⟩
  · show Matrix.transvection i0.castSucc i0.succ a i i = 1
    rw [Matrix.transvection, Matrix.add_apply, Matrix.one_apply_eq, Matrix.single_apply_of_ne, add_zero]
    rintro ⟨h1, h2⟩
    exact hne (h1.trans h2.symm)
  · show Matrix.transvection i0.castSucc i0.succ a i j = 0
    rw [Matrix.transvection, Matrix.add_apply, Matrix.one_apply_ne hij.ne', Matrix.single_apply_of_ne, add_zero]
    rintro ⟨rfl, rfl⟩
    exact absurd hij (Fin.castSucc_lt_succ (i := i0)).not_gt
  · show ∑ i : Fin n, Matrix.transvection i0.castSucc i0.succ a i.castSucc i.succ = a
    rw [Finset.sum_eq_single i0]
    · rw [Matrix.transvection, Matrix.add_apply, Matrix.one_apply_ne hne, Matrix.single_apply_same, zero_add]
    · intro i _ hi
      rw [Matrix.transvection, Matrix.add_apply, Matrix.one_apply_ne (Fin.castSucc_lt_succ (i := i)).ne,
        Matrix.single_apply_of_ne, add_zero]
      rintro ⟨h1, -⟩
      exact hi (Fin.castSucc_injective _ h1).symm
    · intro h
      exact absurd (Finset.mem_univ _) h

end Local

section Product

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι] [DecidableEq ι] {kf : ι → Type}
  [∀ v, Field (kf v)] [∀ v, Fintype (kf v)] {n : ℕ}

omit [NumberField K] in

theorem exists_psiU_eq (hn : 0 < n) (v : ι) (a : kf v) :
    ∃ u ∈ Subgroup.pi Set.univ (fun v => uniSub (kf v) n),
      (∀ w, supd (((u w : mirabSub (kf w) n) : GL (Fin (n + 1)) (kf w)) : Matrix (Fin (n + 1)) (Fin (n + 1)) (kf w)) =
        Pi.single (M := kf) v a w) ∧
      ∀ χ : ∀ v, AddChar (kf v) (𝓞 K), psiU kf n χ (fun v => mirabSub (kf v) n) u = χ v a := by
  choose u hu hs using fun w => exists_uni_supd hn (Pi.single (M := kf) v a w)
  refine ⟨fun w => ⟨u w, isMirab_of_isUniU _ (hu w)⟩, fun w _ => hu w, hs, fun χ => ?_⟩
  unfold psiU
  simp only [hs]
  rw [Finset.prod_eq_single v]
  · rw [Pi.single_eq_same]
  · intro w _ hw
    rw [Pi.single_eq_of_ne hw, AddChar.map_zero_eq_one]
  · intro h
    exact absurd (Finset.mem_univ _) h

end Product

scoped instance resField {E : Type} [Field E] [NumberField E] (PP : Pl E) : Field (kP PP) :=
  haveI := PP.isMaximal
  Ideal.Quotient.field PP.asIdeal

scoped instance resFintype {E : Type} [Field E] [NumberField E] (PP : Pl E) : Fintype (kP PP) :=
  haveI : Finite (kP PP) := Ideal.finiteQuotientOfFreeOfNeBot PP.asIdeal PP.ne_bot
  Fintype.ofFinite _

def rankPred (R : Ranks) : ℕ := R.k + R.m - 2

theorem rank_eq (R : Ranks) : R.r = rankPred R + 1 := by
  have := R.two_le_m
  unfold Ranks.r rankPred
  omega

theorem rankPred_pos (R : Ranks) : 0 < rankPred R := by
  have := R.two_le_m
  have := R.m_add_three_le_k
  unfold rankPred
  omega

section Level

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A)

abbrev Res (v : R.Pg) : Type := kP v.1

abbrev Mir : Type := ∀ v : R.Pg, mirabSub (Res R v) (rankPred D.R)

instance : Finite (Mir R) := inferInstance

def uni : Subgroup (Mir R) := Subgroup.pi Set.univ fun v => uniSub (Res R v) (rankPred D.R)

def mirToGL : Mir R →* G0 R.Pg D.R.r where
  toFun x v := glCast (rank_eq D.R) (x v : GL (Fin (rankPred D.R + 1)) (Res R v))
  map_one' := funext fun _ => map_one (glCast (rank_eq D.R))
  map_mul' _ _ := funext fun _ => map_mul (glCast (rank_eq D.R)) _ _

def mirIncl : Mir R →* G := R.eG.symm.toMonoidHom.comp (mirToGL R)

theorem eG_mirIncl (x : Mir R) : R.eG (mirIncl R x) = mirToGL R x := R.eG.apply_symm_apply _

theorem mirIncl_injective : Function.Injective (mirIncl R) := by
  intro x y h
  have h' : mirToGL R x = mirToGL R y := R.eG.symm.injective h
  funext v
  exact Subtype.ext ((glCast (rank_eq D.R)).injective (congrFun h' v))

theorem mem_pi_unip_iff (g : G0 R.Pg D.R.r) :
    g ∈ Subgroup.pi Set.univ (fun v : R.Pg => unip (kP v.1) D.R.r) ↔ ∃ u ∈ uni R, mirToGL R u = g := by
  constructor
  · intro h
    have hu : ∀ v : R.Pg, IsUniU (((glCast (rank_eq D.R)).symm (g v) : GL (Fin (rankPred D.R + 1)) (Res R v)) :
        Matrix (Fin (rankPred D.R + 1)) (Fin (rankPred D.R + 1)) (Res R v)) := fun v =>
      (glCast_mem_unip (rank_eq D.R) _).1 (by rw [MulEquiv.apply_symm_apply]; exact h v (Set.mem_univ v))
    exact ⟨fun v => ⟨_, isMirab_of_isUniU _ (hu v)⟩, fun v _ => hu v,
      funext fun v => (glCast (rank_eq D.R)).apply_symm_apply _⟩
  · rintro ⟨u, hu, rfl⟩ v _
    exact (glCast_mem_unip (rank_eq D.R) _).2 (hu v (Set.mem_univ v))

structure IsLevelChar (χ : ∀ v : R.Pg, AddChar (Res R v) (𝓞 D.what₂.LL)) : Prop where
  generic : IsGenericChar (Res R) χ
  val : ∀ u ∈ uni R, ∀ h : mirIncl R u ∈ F.P0,
    ((psiU (Res R) (rankPred D.R) χ _ u : 𝓞 D.what₂.LL) : D.what₂.LL) = ((F.ψ0⁻¹ ⟨mirIncl R u, h⟩ : D.what₂.LLˣ) : D.what₂.LL)

variable {R F}

theorem mem_base_iff (h : R.grp_levels F) (g : G) : g ∈ F.P0 ↔ ∃ u ∈ uni R, mirIncl R u = g := by
  obtain ⟨ψ, -, h0, -⟩ := h
  have h1 : F.P0.comap R.eG.symm.toMonoidHom = Subgroup.pi Set.univ (fun v : R.Pg => unip (kP v.1) D.R.r) :=
    congrArg LevelP.H h0
  have h2 : g ∈ F.P0 ↔ R.eG g ∈ F.P0.comap R.eG.symm.toMonoidHom := by
    rw [Subgroup.mem_comap]; simp
  rw [h2, h1, mem_pi_unip_iff]
  refine exists_congr fun u => and_congr_right fun _ => ?_
  rw [← eG_mirIncl, R.eG.injective.eq_iff]

theorem IsLevelChar.unique (h : R.grp_levels F) {χ χ' : ∀ v : R.Pg, AddChar (Res R v) (𝓞 D.what₂.LL)}
    (h1 : IsLevelChar R F χ) (h2 : IsLevelChar R F χ') : χ = χ' := by
  classical
  funext v
  ext a
  obtain ⟨u, hu, -, hv⟩ := exists_psiU_eq (K := D.what₂.LL) (rankPred_pos D.R) v a
  have hm := (mem_base_iff h _).2 ⟨u, hu, rfl⟩
  rw [← hv χ, ← hv χ']
  exact (h1.val u hu hm).trans (h2.val u hu hm).symm

theorem exists_isLevelChar (h : R.grp_levels F) : ∃ χ, IsLevelChar R F χ := by
  classical
  have hmem := mem_base_iff h
  obtain ⟨ψ, hgen, h0, -⟩ := h
  have key : ∀ (L L' : LevelP R.Pg D.R.r ℂ), L = L' → ∀ g (hg : g ∈ L.H) (hg' : g ∈ L'.H),
      L.chi ⟨g, hg⟩ = L'.chi ⟨g, hg'⟩ := by
    rintro L _ rfl g hg hg'; rfl
  have hval : ∀ u ∈ uni R, ∀ hu : mirIncl R u ∈ F.P0,
      D.what₂.embLL ((F.ψ0 ⟨mirIncl R u, hu⟩ : D.what₂.LLˣ) : D.what₂.LL) =
        ∏ v : R.Pg, ψ v.1 (supd (((u v : mirabSub (Res R v) (rankPred D.R)) : GL (Fin (rankPred D.R + 1)) (Res R v)) :
          Matrix (Fin (rankPred D.R + 1)) (Fin (rankPred D.R + 1)) (Res R v))) := by
    intro u hu hu'
    have e := congrArg Units.val (key _ _ h0 (mirToGL R u) hu' ((mem_pi_unip_iff R _).2 ⟨u, hu, rfl⟩))
    refine Eq.trans e ?_
    refine (congrArg Units.val (MonoidHom.finset_prod_apply (fun v : R.Pg =>
      (addCharHom (ψ v.1) (supHom (kP v.1) D.R.r)).comp (LevelP.prj (fun v : R.Pg => unip (kP v.1) D.R.r) v))
        Finset.univ _)).trans ?_
    rw [Units.coe_prod]
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [← edgeSum_glCast (rank_eq D.R)]
    rfl
  have hex : ∀ (v : R.Pg) (a : Res R v), ∃ z : 𝓞 D.what₂.LL, D.what₂.embLL (z : D.what₂.LL) = ψ v.1 (-a) := by
    intro v a
    obtain ⟨u, hu, hs, -⟩ := exists_psiU_eq (K := D.what₂.LL) (rankPred_pos D.R) v (-a)
    have hm := (hmem _).2 ⟨u, hu, rfl⟩
    refine ⟨⟨_, isIntegral_char F.ψ0 ⟨mirIncl R u, hm⟩⟩, (hval u hu hm).trans ?_⟩
    simp only [hs]
    rw [Finset.prod_eq_single v]
    · rw [Pi.single_eq_same]
    · intro w _ hw
      rw [Pi.single_eq_of_ne hw, AddChar.map_zero_eq_one]
    · intro h
      exact absurd (Finset.mem_univ _) h
  choose z hz using hex
  have hinj : ∀ x y : 𝓞 D.what₂.LL, D.what₂.embLL (x : D.what₂.LL) = D.what₂.embLL (y : D.what₂.LL) → x = y :=
    fun x y hxy => Subtype.ext (D.what₂.embLL.injective hxy)
  let χ : ∀ v : R.Pg, AddChar (Res R v) (𝓞 D.what₂.LL) := fun v =>
    { toFun := z v
      map_zero_eq_one' := hinj _ _ (by rw [hz, neg_zero, AddChar.map_zero_eq_one]; simp)
      map_add_eq_mul' := fun a b => hinj _ _ (by
        rw [hz, neg_add, AddChar.map_add_eq_mul, ← hz, ← hz, ← map_mul]; rfl) }
  refine ⟨χ, fun v hv => hgen v.1 v.2 ?_, fun u hu hm => D.what₂.embLL.injective ?_⟩
  · ext a
    have h1 : z v (-a) = 1 := congrArg (fun c : AddChar (Res R v) (𝓞 D.what₂.LL) => c (-a)) hv
    have h2 := hz v (-a)
    rw [h1, neg_neg] at h2
    rw [← h2]; simp
  · rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, map_inv₀, hval u hu hm, ← Finset.prod_inv_distrib]
    unfold psiU
    rw [show ∀ y : 𝓞 D.what₂.LL, D.what₂.embLL (y : D.what₂.LL) =
      (D.what₂.embLL.comp (algebraMap (𝓞 D.what₂.LL) D.what₂.LL)) y from fun _ => rfl, map_prod]
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [← AddChar.map_neg_eq_inv]
    exact hz v _

variable (R F)

open Classical in

def levelChar : ∀ v : R.Pg, AddChar (Res R v) (𝓞 D.what₂.LL) :=
  if h : ∃ χ, IsLevelChar R F χ then h.choose else 1

variable {R F}

theorem levelChar_spec (h : R.grp_levels F) : IsLevelChar R F (levelChar R F) := by
  have h' := exists_isLevelChar h
  unfold levelChar
  rw [dif_pos h']
  exact h'.choose_spec

end Level

structure ChainArgs (K : Type) [Field K] [NumberField K] (J : Type) (nZ : J → ℕ) where

  Th1 : HeightOneSpectrum (𝓞 K) → ∀ j, Submodule (𝓞 K) (Fin (nZ j) → K)

  Th : HeightOneSpectrum (𝓞 K) → ∀ j, Submodule (𝓞 K) (Fin (nZ j) → K)

  ThK : HeightOneSpectrum (𝓞 K) → ∀ j, Submodule (𝓞 K) (Fin (nZ j) → K)

  Th0 : HeightOneSpectrum (𝓞 K) → ∀ j, Submodule (𝓞 K) (Fin (nZ j) → K)

  ThJ : HeightOneSpectrum (𝓞 K) → ∀ j, Submodule (𝓞 K) (Fin (nZ j) → K)

  X₃ : HeightOneSpectrum (𝓞 K) → ∀ j, Submodule (𝓞 K) (Fin (nZ j) → K)

  σ : HeightOneSpectrum (𝓞 K) → J → K

  a : HeightOneSpectrum (𝓞 K) → J → K

  E : HeightOneSpectrum (𝓞 K) → J → ℕ

  r1 : HeightOneSpectrum (𝓞 K) → J → ℝ

  r2 : HeightOneSpectrum (𝓞 K) → J → ℝ

  ε0 : HeightOneSpectrum (𝓞 K) → J → ℝ

  nnK : J → K

  Jp : J → ℕ → ℝ

  bp : ℝ

  Sc : ℝ

  eta : ℝ

  T : ℝ

  DF : ℝ

  X2 : ℝ

  x : ℝ

  eps : ℝ

  vd : ℝ

  de2 : ℝ

  Nc : ℝ

  wt : J → ℝ

  th : ℕ → ℝ

  ad : ℕ → ℝ

def ChainArgs.ofObj {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {Df : DefSide Bs} {S : IndefData Df}
    {P : Type} [Group P] [Finite P] {c : OnConst} (O : OnObj S P c) : ChainArgs K Bs.J O.nZ :=
  { O with }

section Objects

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A)

abbrev liftLvl : Lvl D.what₂.LL G := A.fam.lvlA F.P0 F.ψ0

abbrev liftSub (j : Fin D.R.m) (t : T) : Submodule D.what₂.LL (A.fam.L j t).S.Forms := (R.toCx F).zs.Zl j t

abbrev srcDim (j : Fin D.R.m) (t : T) : ℕ := (A.fam.L j t).S.lvlDim (A.fam.L j t).r (liftLvl F).P (liftLvl F).ψ

def goodOp (j : Fin D.R.m) : (Fin (R.nW j) → D.what₂.LL) →ₗ[D.what₂.LL] (Fin (R.nW j) → D.what₂.LL) :=
  (R.FW j).eOp fun g => (idemOf A.X).coeff g

def coordMap (j : Fin D.R.m) :
    (Fin (finrank D.what₂.LL (R.WL F false j)) → D.what₂.LL) →ₗ[D.what₂.LL] (Fin (R.nW j) → D.what₂.LL) :=
  Fintype.linearCombination D.what₂.LL (R.bL F false j)

def thetaMat (j : Fin D.R.m) (t : T) : Matrix (Fin (finrank D.what₂.LL (R.WL F false j)))
    (Fin ((A.fam.L j t).dZ (liftLvl F) (liftSub R F j t))) D.what₂.LL :=
  (R.toCx F).liftMat F.cr false j t

def thetaOp (j : Fin D.R.m) (t : T) : (Fin (srcDim F j t) → D.what₂.LL) →ₗ[D.what₂.LL] (Fin (R.nW j) → D.what₂.LL) :=
  coordMap R F j ∘ₗ (thetaMat R F j t * (A.fam.L j t).lPr (liftLvl F) (liftSub R F j t)).mulVecLin

def srcGood (j : Fin D.R.m) (t : T) : (Fin (srcDim F j t) → D.what₂.LL) →ₗ[D.what₂.LL] (Fin (srcDim F j t) → D.what₂.LL) :=
  ((A.fam.L j t).S.lvlOp (A.fam.L j t).r (liftLvl F).P (liftLvl F).ψ (idemOf A.X)).mulVecLin

def srcProj (j : Fin D.R.m) (t : T) : (Fin (srcDim F j t) → D.what₂.LL) →ₗ[D.what₂.LL] (Fin (srcDim F j t) → D.what₂.LL) :=
  ((A.fam.L j t).lE (liftLvl F) (liftSub R F j t) * (A.fam.L j t).lPr (liftLvl F) (liftSub R F j t)).mulVecLin

def srcLat (j : Fin D.R.m) (t : T) : Submodule (𝓞 D.what₂.LL) (Fin (srcDim F j t) → D.what₂.LL) :=
  (A.fam.L j t).S.lvlNab (A.fam.L j t).r (liftLvl F).P (liftLvl F).ψ

def onOf (c : OnConst) (a : ChainArgs D.what₂.LL (Fin D.R.m) R.nW) : OnObj ((R.toCx F).data F.cr false) (Mir R) c where
  nZ := R.nW
  ρ j := (twRep (R.FW j)).comp (mirIncl R)
  U := uni R
  ψ := psiU (Res R) (rankPred D.R) (levelChar R F) _
  V₀ j := (R.FW j).good fun g => (idemOf A.X).coeff g
  e := goodOp R
  Ms j := supLat (R.FW j)
  φ := coordMap R F
  Th1 := a.Th1
  Th := a.Th
  ThK := a.ThK
  Th0 := a.Th0
  ThJ := a.ThJ
  X₃ := a.X₃
  σ := a.σ
  a := a.a
  E := a.E
  r1 := a.r1
  r2 := a.r2
  pde := D.host.pde
  ε0 := a.ε0
  nX v j := srcDim F j (R.mu v)
  θ' v j := thetaOp R F j (R.mu v)
  eX v j := srcGood F j (R.mu v)
  pr v j := srcProj R F j (R.mu v)
  Mt v j := srcLat F j (R.mu v)
  nnK := a.nnK
  Jp := a.Jp
  k := D.R.k
  m := D.R.m
  f := D.R.f
  bp := a.bp
  Sc := a.Sc
  eta := a.eta
  T := a.T
  DF := a.DF
  X2 := a.X2
  x := a.x
  eps := a.eps
  vd := a.vd
  rr := D.R.r
  de2 := a.de2
  Nc := a.Nc
  wt := a.wt
  th := a.th
  ad := a.ad
  T2 := D.host.T2.card
  g1 := D.host.g 0
  g2 := D.host.g 1
  q1 := D.host.q
  sm := D.host.small
  dd := D.host.d

variable (c : OnConst) (a : ChainArgs D.what₂.LL (Fin D.R.m) R.nW)

theorem ofObj_onOf : ChainArgs.ofObj (onOf R F c a) = a := rfl

theorem tieU : TieU (onOf R F c a) fun v => uniSub (Res R v) (rankPred D.R) := rfl

theorem tiePsi : TiePsi (onOf R F c a) (levelChar R F) := rfl

theorem tieLevelNum : TieLevelNum (onOf R F c a) (rankPred D.R) D.R.f :=
  ⟨rfl, by show ((D.R.r : ℕ) : ℝ) = _; rw [rank_eq]; push_cast; rfl⟩

theorem tieProj : TieProj (onOf R F c a) (fun j => twRep (R.FW j)) fun _ => idemOf A.X :=
  fun j => ⟨eOp_eq (R.FW j) (idemOf A.X), rfl⟩

variable {R F}

theorem goodOp_idem (hX : ∀ χ ∈ A.X, IsAbsIrrChar χ) (j : Fin D.R.m) : goodOp R j ∘ₗ goodOp R j = goodOp R j := by
  unfold goodOp
  rw [eOp_eq, ← Module.End.mul_eq_comp, ← map_mul, (idempotent_central _ G A.X hX).1]

theorem goodOp_comm (hX : ∀ χ ∈ A.X, IsAbsIrrChar χ) (j : Fin D.R.m) (g : G) :
    goodOp R j ∘ₗ twRep (R.FW j) g = twRep (R.FW j) g ∘ₗ goodOp R j := by
  unfold goodOp
  rw [eOp_eq, ← Representation.asAlgebraHom_of, ← Module.End.mul_eq_comp, ← Module.End.mul_eq_comp, ← map_mul, ← map_mul,
    (idempotent_central _ G A.X hX).2]

theorem coordMap_injective (j : Fin D.R.m) : Function.Injective (coordMap R F j) :=
  linearIndependent_iff_injective_fintypeLinearCombination.1
    ((finBasis D.what₂.LL (R.WL F false j)).linearIndependent.map' (R.WL F false j).subtype (Submodule.ker_subtype _))

theorem range_coordMap (j : Fin D.R.m) : LinearMap.range (coordMap R F j) = R.WL F false j := by
  unfold coordMap
  rw [Fintype.range_linearCombination]
  have h := congrArg (Submodule.map (R.WL F false j).subtype) (finBasis D.what₂.LL (R.WL F false j)).span_eq
  rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype, ← Set.range_comp] at h
  exact h

theorem eig_eq (h : R.grp_levels F) (j : Fin D.R.m) :
    eig ((onOf R F c a).ρ j) (onOf R F c a).U (onOf R F c a).ψ = (R.FW j).typeP F.P0 F.ψ0⁻¹ := by
  ext x
  have e1 : x ∈ eig ((onOf R F c a).ρ j) (onOf R F c a).U (onOf R F c a).ψ ↔ ∀ u : uni R,
      twRep (R.FW j) (mirIncl R u) x =
        ((psiU (Res R) (rankPred D.R) (levelChar R F) _ (u : Mir R) : 𝓞 D.what₂.LL) : D.what₂.LL) • x := by
    unfold eig
    rw [Submodule.mem_iInf]
    exact forall_congr' fun u => sub_eq_zero
  refine e1.trans (Iff.trans ?_ (mem_eigenspace_iff₂ (R.FW j) F.P0 F.ψ0⁻¹ x).symm)
  constructor
  · rintro hx ⟨g, hg⟩
    obtain ⟨u, hu, rfl⟩ := (mem_base_iff h g).1 hg
    rw [← (levelChar_spec h).val u hu hg]
    exact hx ⟨u, hu⟩
  · intro hx u
    have hg := (mem_base_iff h _).2 ⟨u.1, u.2, rfl⟩
    rw [(levelChar_spec h).val u.1 u.2 hg]
    exact hx ⟨_, hg⟩

theorem zg_eq (h : R.grp_levels F) (j : Fin D.R.m) : (onOf R F c a).Zg j = R.WL F false j := by
  unfold OnObj.Zg
  rw [eig_eq c a h]
  rfl

theorem cut_eq (h : R.grp_levels F) (j : Fin D.R.m) :
    cut ((onOf R F c a).Zg j) ((onOf R F c a).Ms j) = (R.FW j).Mj F.P0 F.ψ0⁻¹ fun g => (idemOf A.X).coeff g := by
  rw [zg_eq c a h]
  ext x
  exact and_assoc.symm

variable {s : ℕ}

theorem blockHyp (hOk : A.fam.Ok s) (j : Fin D.R.m) (t : T) : BlockHyp (A.fam.L j t) (liftLvl F) A.v0 s :=
  ⟨hOk.conj, hOk.irr, hOk.lifts j t⟩

theorem thetaOp_srcGood (hOk : A.fam.Ok s) (j : Fin D.R.m) (t : T) :
    thetaOp R F j t ∘ₗ srcGood F j t = thetaOp R F j t := by
  have h := lPr_mul_lvlOp (Z := liftSub R F j t) (blockHyp (F := F) hOk j t)
  unfold thetaOp srcGood
  rw [LinearMap.comp_assoc, ← Matrix.mulVecLin_mul, Matrix.mul_assoc]
  exact congrArg (fun M => coordMap R F j ∘ₗ (thetaMat R F j t * M).mulVecLin) h

theorem thetaOp_srcProj (hOk : A.fam.Ok s) (j : Fin D.R.m) (t : T) :
    thetaOp R F j t ∘ₗ srcProj R F j t = thetaOp R F j t := by
  have h := BlockDat.lf_lPr_lE (Z := liftSub R F j t) (blockHyp (F := F) hOk j t)
  unfold thetaOp srcProj
  rw [LinearMap.comp_assoc, ← Matrix.mulVecLin_mul, Matrix.mul_assoc, ← Matrix.mul_assoc _ ((A.fam.L j t).lE _ _), h,
    Matrix.one_mul]

theorem goodOp_thetaOp (hX : ∀ χ ∈ A.X, IsAbsIrrChar χ) (j : Fin D.R.m) (t : T) :
    goodOp R j ∘ₗ thetaOp R F j t = thetaOp R F j t := by
  refine LinearMap.ext fun x => ?_
  have hx : thetaOp R F j t x ∈ R.WL F false j := by
    rw [← range_coordMap]; exact ⟨_, rfl⟩
  obtain ⟨y, hy⟩ : thetaOp R F j t x ∈ LinearMap.range (goodOp R j) := hx.2
  rw [LinearMap.comp_apply, ← hy]
  exact LinearMap.congr_fun (goodOp_idem hX j) y

theorem srcProj_idem (hOk : A.fam.Ok s) (j : Fin D.R.m) (t : T) :
    srcProj R F j t ∘ₗ srcProj R F j t = srcProj R F j t := by
  have h := BlockDat.lf_lPr_lE (Z := liftSub R F j t) (blockHyp (F := F) hOk j t)
  unfold srcProj
  rw [← Matrix.mulVecLin_mul, Matrix.mul_assoc, ← Matrix.mul_assoc _ ((A.fam.L j t).lE _ _), h, Matrix.one_mul]

theorem tjId (hOk : A.fam.Ok s) (j : Fin D.R.m) (v : HeightOneSpectrum (𝓞 D.what₂.LL)) :
    (onOf R F c a).TjId j v (R.mu v) := by
  have h1 := thetaOp_srcGood (R := R) (F := F) hOk j (R.mu v)
  have h2 := thetaOp_srcProj (R := R) (F := F) hOk j (R.mu v)
  have h3 : ∀ x, thetaOp R F j (R.mu v) (srcProj R F j (R.mu v) (srcGood F j (R.mu v) x)) = thetaOp R F j (R.mu v) x :=
    fun x => (LinearMap.congr_fun h2 _).trans (LinearMap.congr_fun h1 x)
  have h4 : ∀ x, thetaOp R F j (R.mu v) x = coordMap R F j ((thetaMat R F j (R.mu v)).mulVec
      (((A.fam.L j (R.mu v)).lPr (liftLvl F) (liftSub R F j (R.mu v))).mulVec x)) := fun x => by
    rw [Matrix.mulVec_mulVec]; rfl
  apply le_antisymm
  · rintro _ ⟨_, ⟨_, ⟨x, hx, rfl⟩, rfl⟩, rfl⟩
    exact ⟨_, ⟨_, ⟨x, hx, rfl⟩, rfl⟩, (h3 x).trans (h4 x)⟩
  · rintro _ ⟨_, ⟨_, ⟨x, hx, rfl⟩, rfl⟩, rfl⟩
    exact ⟨_, ⟨_, ⟨x, hx, rfl⟩, rfl⟩, ((h3 x).trans (h4 x)).symm⟩

theorem tieCoord (hOk : A.fam.Ok s) (h : R.grp_levels F) (hμ : R.tup_mu_conj) : TieCoord (onOf R F c a) := by
  refine ⟨fun j => ⟨coordMap_injective j, (range_coordMap j).trans (zg_eq c a h j).symm, ?_⟩,
    fun w _ j => ⟨tjId c a hOk j w, ?_⟩⟩
  · rw [cut_eq c a h]
    refine Submodule.map_comap_eq_self (f := (coordMap R F j).restrictScalars (𝓞 D.what₂.LL)) fun x hx => ?_
    have hx' : x ∈ LinearMap.range (coordMap R F j) := by
      rw [range_coordMap]; exact (R.FW j).Mj_sub_Wgood _ _ _ hx
    exact hx'
  · have h' := tjId (R := R) (F := F) c a hOk j (conjPl w)
    rwa [hμ w] at h'

theorem leafProj (hX : ∀ χ ∈ A.X, IsAbsIrrChar χ) : LeafProj (onOf R F c a) := fun j => ⟨goodOp_idem hX j, rfl⟩

theorem leafIdentity (hOk : A.fam.Ok s) : LeafIdentity (onOf R F c a) := by
  have H : ∀ v j, (onOf R F c a).θ' v j ∘ₗ (onOf R F c a).eX v j = (onOf R F c a).e j ∘ₗ (onOf R F c a).θ' v j ∧
      ∀ x ∈ LinearMap.range ((onOf R F c a).eX v j),
        x - (onOf R F c a).pr v j x ∈ LinearMap.ker ((onOf R F c a).θ' v j) := fun v j =>
    ⟨(thetaOp_srcGood hOk j _).trans (goodOp_thetaOp hOk.irr j _).symm, fun x _ => by
      rw [LinearMap.mem_ker, map_sub, sub_eq_zero]
      exact (LinearMap.congr_fun (thetaOp_srcProj hOk j (R.mu v)) x).symm⟩
  exact fun w _ => ⟨H w, H (conjPl w)⟩

theorem leafSup (h : R.LIntegral) : LeafSup (onOf R F c a) :=
  fun j => ⟨supLat_isLatIn _ (h j).1 (h j).2.1, fun g => supLat_stable _ (h j).2.2 (mirIncl R g)⟩

theorem leafMackey (h : R.grp_levels F) : LeafMackey (onOf R F c a) := by
  classical
  exact leafMackey_of _ _ (mirab_levelGroups _ _) (levelChar_spec h).generic (tieU R F c a) (tiePsi R F c a)

theorem leafLevelSq (h : R.grp_record) : LeafLevelSq (onOf R F c a) (Res R) D.R.f := by
  classical
  obtain ⟨-, plg, iso, -⟩ := h
  have hc : ∀ kv, Fintype.card (Res R (plg kv)) = D.host.g kv.1 := fun kv => by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_congr (iso kv).toEquiv, Nat.card_zmod]
  have hinj : Function.Injective D.host.g := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · rfl
    · exact absurd hij D.host.g_ne
    · exact absurd hij.symm D.host.g_ne
    · rfl
  have hn : ∀ i, (Finset.univ.filter fun v => Fintype.card (Res R v) = D.host.g i).card = D.R.f := by
    intro i
    rw [← D.nd.card_PlG i, ← Fintype.card_subtype]
    refine (Fintype.card_congr (Equiv.ofBijective (fun w : D.nd.PlG i => (⟨plg ⟨i, w⟩, hc ⟨i, w⟩⟩ :
      {v // Fintype.card (Res R v) = D.host.g i})) ⟨fun x y hxy => ?_, fun v => ?_⟩)).symm
    · exact eq_of_heq (Sigma.mk.inj (plg.injective (congrArg Subtype.val hxy))).2
    · obtain ⟨v, hv⟩ := v
      obtain ⟨⟨i', w⟩, rfl⟩ := plg.surjective v
      obtain rfl : i' = i := hinj ((hc ⟨i', w⟩).symm.trans hv)
      exact ⟨w, rfl⟩
  refine ⟨D.host.g_prime 0, D.host.g_prime 1, D.host.g_ne, fun v => ?_, hn 0, hn 1⟩
  obtain ⟨⟨i, w⟩, rfl⟩ := plg.surjective v
  rw [hc]
  fin_cases i
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem leafYBound {L : SizeData₂ D} (Q : ParameterChoice' D L) : LeafYBound (onOf R F c a) := by
  show 2 * (D.R.f : ℝ) / (((min (D.host.g 0) (D.host.g 1) : ℕ) : ℝ) - 1) ≤ 1 / (4 * ((D.R.f : ℝ) * D.R.k) ^ 3)
  obtain ⟨Y, hY, -, -, hg⟩ := Q.g_Y
  have hb : (2 : ℝ) ≤ L.sc.b := by
    have h1 : (1 : ℝ) ≤ L.sc.L := Real.one_le_rpow L.sc.one_lt_alt.le L.sc.eps_pos.le
    have h2 := Real.add_one_le_exp L.sc.L
    unfold Scale.b
    linarith
  have hfk : (D.R.f : ℝ) ≤ D.R.k := by exact_mod_cast D.R.f_le_k
  have hf : (1 : ℝ) ≤ D.R.f := by
    have : 0 < D.R.f := by unfold Ranks.f Ranks.n; positivity
    exact_mod_cast this
  have hk : (1 : ℝ) ≤ D.R.k := hf.trans hfk
  have hmin : Y ≤ ((min (D.host.g 0) (D.host.g 1) : ℕ) : ℝ) := by
    rw [Nat.cast_min]
    exact le_min (hg 0).1 (hg 1).1
  have h1 : ((D.R.k : ℝ) * 2) ^ 8 ≤ ((D.R.k : ℝ) * L.sc.b) ^ 8 := by gcongr
  have h2 : (D.R.f : ℝ) ^ 4 * (D.R.k : ℝ) ^ 3 ≤ (D.R.k : ℝ) ^ 8 := by
    calc (D.R.f : ℝ) ^ 4 * (D.R.k : ℝ) ^ 3 ≤ (D.R.k : ℝ) ^ 4 * (D.R.k : ℝ) ^ 4 := by gcongr; norm_num
      _ = _ := by ring
  have h3 : (1 : ℝ) ≤ (D.R.k : ℝ) ^ 8 := one_le_pow₀ hk
  rw [div_le_div_iff₀ (by nlinarith) (by positivity)]
  nlinarith

theorem leafIndexU (h : R.grp_record) (hY : LeafYBound (onOf R F c a)) : LeafIndexU (onOf R F c a) := by
  classical
  exact leafIndexU_of _ D.R.f (mirab_levelGroups _ _) (leafLevelSq c a h) hY (tieU R F c a) (tieLevelNum R F c a)

theorem leafUnip (h : R.grp_record) : LeafUnip (onOf R F c a) := by
  classical
  exact leafUnip_of _ D.R.f (mirab_levelGroups _ _) (leafLevelSq c a h) (tieU R F c a) (tieLevelNum R F c a)

theorem onOf_leaves (hOk : A.fam.Ok s) (hC : R.Char F) (hI : R.LIntegral) {L : SizeData₂ D} (Q : ParameterChoice' D L) :
    TieCoord (onOf R F c a) ∧ LeafProj (onOf R F c a) ∧ LeafIdentity (onOf R F c a) ∧ LeafSup (onOf R F c a) ∧
      LeafMackey (onOf R F c a) ∧ LeafIndexU (onOf R F c a) ∧ LeafUnip (onOf R F c a) :=
  ⟨tieCoord c a hOk hC.grp.levels hC.tup.mu_conj, leafProj c a hOk.irr, leafIdentity c a hOk, leafSup c a hI,
    leafMackey c a hC.grp.levels, leafIndexU c a hC.grp.record (leafYBound c a Q), leafUnip c a hC.grp.record⟩

end Objects

section Checks

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A}

theorem tC_cpt {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {A : DefAmb Bs} (X : CxData A)
    {fc : DefSub A → DefFace Bs} (cr : Crd A fc) (b : Bool) (j : Bs.J) (t : Bs.Tup) (y : Fin ((lv (fc X.zs) b).dZ j t) → K) :
    X.tC cr b j t (cpt Bs.v0.embedding y) = X.θ' j t (X.jL j t (cr.toL X.zs b j t y)) := by
  conv_rhs => rw [← Finset.univ_sum_single y, map_sum, map_sum, map_sum]
  show ∑ k, Bs.v0.embedding (y k) • X.θ' j t (X.jL j t (cr.toL X.zs b j t (Pi.single k 1))) = _
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← map_smul, ← map_smulₛₗ, ← map_smul, ← Pi.single_smul', smul_eq_mul, mul_one]

theorem liftWeight_complexPoint_eq_twist {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {A : DefAmb Bs} (X : CxData A)
    (b : Bool) (j : Bs.J) (z : Fin (X.dW b j) → K) :
    X.w0C b j (cpt Bs.v0.embedding z) = ∑ k, Bs.v0.embedding (z k) • X.eW b j (X.bW b j Bs.v0 k) := by
  show X.eW b j (∑ k, Bs.v0.embedding (z k) • X.bW b j Bs.v0 k) = _
  rw [map_sum]
  exact Finset.sum_congr rfl fun k _ => map_smul _ _ _

theorem out_sum {s : Bool} {E ι : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [Fintype ι] (f : ι → Tw s E) :
    Tw.out (∑ k, f k) = ∑ k, Tw.out (f k) := rfl

theorem j_coordMap (j : Fin D.R.m) (z : Fin (finrank D.what₂.LL (R.WL F false j)) → D.what₂.LL) :
    (R.FW j).j (sg0 D A) (coordMap R F j z) =
      Tw.out (s := twAt D.what₂.embLL A.v0) ((R.toCx F).w0C false j (cpt A.v0.embedding z)) := by
  have hsq : ((Real.sqrt (RealDat.nP F false) : ℝ) : ℂ) * (((Real.sqrt (RealDat.nP F false))⁻¹ : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, mul_inv_cancel₀ (Real.sqrt_pos.2 (RealDat.nP_pos false)).ne', Complex.ofReal_one]
  refine Eq.trans ?_ (congrArg (Tw.out (s := twAt D.what₂.embLL A.v0)) (liftWeight_complexPoint_eq_twist (R.toCx F) false j z)).symm
  refine Eq.trans ?_ (out_sum _).symm
  unfold coordMap
  rw [Fintype.linearCombination_apply, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  show _ = cj (twAt D.what₂.embLL A.v0) (A.v0.embedding (z k)) • (((Real.sqrt (RealDat.nP F false) : ℝ) : ℂ) •
    ((((Real.sqrt (RealDat.nP F false))⁻¹ : ℝ) : ℂ) • (R.FW j).j (sg0 D A) (R.bL F false j k)))
  rw [smul_smul _ _ ((R.FW j).j _ _), hsq, one_smul, map_smulₛₗ, emb_eq D.what₂.embLL A.v0, cj_cj]

theorem j_thetaMat (h5 : R.LTheta F) (hr : R.LRatTh F) (j : Fin D.R.m) (t : T)
    (y : Fin ((A.fam.L j t).dZ (liftLvl F) (liftSub R F j t)) → D.what₂.LL) :
    (R.FW j).j (sg0 D A) (coordMap R F j ((thetaMat R F j t).mulVec y)) =
      R.thG j t (R.jV j t ((A.fam.L j t).toF (liftLvl F) (liftSub R F j t) y)) := by
  have k0 := j_coordMap (R := R) (F := F) j ((thetaMat R F j t).mulVec y)
  have k1 := (R.toCx F).key_lift F.cr false (h5 false) (hr false) j t y
  have k2 := tC_cpt (R.toCx F) F.cr false j t y
  have k3 : (R.toCx F).θ' j t ((R.toCx F).jL j t (F.cr.toL (R.toCx F).zs false j t y)) =
      Tw.mk (twAt D.what₂.embLL A.v0) (R.thG j t (R.jV j t ((A.fam.L j t).toF (liftLvl F) (liftSub R F j t) y))) := rfl
  exact k0.trans ((k1.trans k2).trans k3)

theorem j_thetaOp (h5 : R.LTheta F) (hr : R.LRatTh F) (j : Fin D.R.m) (t : T) (x : Fin (srcDim F j t) → D.what₂.LL) :
    (R.FW j).j (sg0 D A) (thetaOp R F j t x) = R.thG j t (R.jV j t ((A.fam.L j t).toF (liftLvl F) (liftSub R F j t)
      (((A.fam.L j t).lPr (liftLvl F) (liftSub R F j t)).mulVec x))) := by
  have h0 : thetaOp R F j t x = coordMap R F j ((thetaMat R F j t).mulVec
      (((A.fam.L j t).lPr (liftLvl F) (liftSub R F j t)).mulVec x)) := by
    rw [Matrix.mulVec_mulVec]; rfl
  exact (congrArg ((R.FW j).j (sg0 D A)) h0).trans (j_thetaMat h5 hr j t _)

theorem range_thetaOp {s : ℕ} (hOk : A.fam.Ok s) (j : Fin D.R.m) (t : T)
    (hb : Function.Surjective (thetaMat R F j t).mulVec) : LinearMap.range (thetaOp R F j t) = R.WL F false j := by
  rw [← range_coordMap]
  unfold thetaOp
  refine LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.2 fun z => ?_)
  obtain ⟨y, rfl⟩ := hb z
  obtain ⟨x, rfl⟩ := BlockDat.lf_lPr_surj (Z := liftSub R F j t) (blockHyp (F := F) hOk j t) y
  exact ⟨x, by rw [Matrix.mulVecLin_apply, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec]⟩

variable (c : OnConst) (a : ChainArgs D.what₂.LL (Fin D.R.m) R.nW)

theorem psi_mul_base (h : R.grp_levels F) (u : Mir R) (hu : u ∈ (onOf R F c a).U) (hm : mirIncl R u ∈ F.P0) :
    (((onOf R F c a).ψ u : 𝓞 D.what₂.LL) : D.what₂.LL) * ((F.ψ0 ⟨mirIncl R u, hm⟩ : D.what₂.LLˣ) : D.what₂.LL) = 1 := by
  have := (levelChar_spec h).val u hu hm
  exact (congrArg (· * _) this).trans (Units.inv_mul _)

theorem card_U (h : R.grp_record) : Nat.card (onOf R F c a).U =
    D.host.g 0 ^ (D.R.r * (D.R.r - 1) / 2 * D.R.f) * D.host.g 1 ^ (D.R.r * (D.R.r - 1) / 2 * D.R.f) := by
  classical
  obtain ⟨-, -, h3, h4, h5, h6⟩ := leafLevelSq (F := F) c a h
  rw [rank_eq, Nat.add_sub_cancel]
  exact card_piU_level (mirab_levelGroups _ _) _ _ _ h3 h4 h5 h6

variable (R) in

def supArgs : ChainArgs D.what₂.LL (Fin D.R.m) R.nW where
  Th1 _ j := supLat (R.FW j)
  Th _ j := supLat (R.FW j)
  ThK _ j := supLat (R.FW j)
  Th0 _ j := supLat (R.FW j)
  ThJ _ j := supLat (R.FW j)
  X₃ _ j := cut ((R.FW j).good fun g => (idemOf A.X).coeff g) (supLat (R.FW j))
  σ _ _ := 1
  a _ _ := 1
  E _ _ := 0
  r1 _ _ := 0
  r2 _ _ := 0
  ε0 _ _ := 0
  nnK _ := 1
  Jp _ _ := 0
  bp := 1
  Sc := 1
  eta := 1
  T := 1
  DF := 1
  X2 := 1
  x := 1
  eps := 1
  vd := 1
  de2 := 1
  Nc := 1
  wt _ := 1
  th _ := 0
  ad _ := 0

example (h : R.LIntegral) : LeafSpan (onOf R F c (supArgs R)) ∧ LeafLemmaS (onOf R F c (supArgs R)) :=
  have hs := leafSup (F := F) c (supArgs R) h
  ⟨fun _ _ => ⟨fun j => ⟨(hs j).1, (hs j).1⟩, fun j => ⟨(hs j).1, (hs j).1⟩⟩,
    fun _ _ => ⟨fun j => ⟨le_rfl, (hs j).2, one_ne_zero, (sc_one' _ _).ge⟩,
      fun j => ⟨le_rfl, (hs j).2, one_ne_zero, (sc_one' _ _).ge⟩⟩⟩

end Checks

example (K : Type) [Field K] [NumberField K] [StarRing K] (v0 : InfinitePlace K) :
    ∃ a : ChainArgs K Unit fun _ => 1, ∀ v, IsLatIn ⊤ (a.Th v ()) ∧ a.σ v () = 1 :=
  ⟨ChainArgs.ofObj (exampleObject K v0 ∅), fun _ => ⟨stdLat_isLatIn K 1, rfl⟩⟩

example (a : ℚ) (h : (!![1, a; 0, 1] : Matrix (Fin 2) (Fin 2) ℚ).det ≠ 0) :
    edgeSum supEdge (glCast (n := 1) rfl (Matrix.GeneralLinearGroup.mkOfDetNeZero _ h)) = a := by
  rw [edgeSum_glCast]
  simp [supd]

end GlobalTheory.OntoChain
