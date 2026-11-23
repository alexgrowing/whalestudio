import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MultiplicationLatticeSecond
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.HomAppHomOfRestrictImage
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GradedLineBundleExists

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TopologicalSpace
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam
open GlobalTheory.LieMet GlobalTheory.Points GlobalTheory.GradedPieces
open Formalism.MainNotions.DIV.Cons (SCF intO)

namespace GlobalTheory.LocM.Frm

attribute [local instance] Over.cartesianMonoidalCategory

section Linear

variable {C M : Type} [NormedField C] [IsUltrametricDist C] [AddCommGroup M] [Module C M] {m : ℕ}

theorem mem_Ospan_image (b : Fin m → M) (s : Set (Fin m)) (v : M) :
    v ∈ Ospan (C := C) (b '' s) ↔ ∃ c : Fin m → C, (∀ i, ‖c i‖ ≤ 1) ∧ (∀ i, i ∉ s → c i = 0) ∧ v = ∑ i, c i • b i := by
  classical
  constructor
  · intro h
    induction h using AddSubgroup.closure_induction with
    | mem x hx =>
      obtain ⟨a, ha, _, ⟨i, hi, rfl⟩, rfl⟩ := hx
      refine ⟨Pi.single i a, fun k => ?_, fun k hk => Pi.single_eq_of_ne (fun e : k = i => hk (e ▸ hi)) _, ?_⟩
      · by_cases e : k = i
        · subst e; simpa using ha
        · simp [Pi.single_eq_of_ne e]
      · simp [Pi.single_apply, ite_smul]
    | zero => exact ⟨0, by simp, by simp, by simp⟩
    | add x x' _ _ hx hx' =>
      obtain ⟨c, h1, h0, rfl⟩ := hx
      obtain ⟨c', h1', h0', rfl⟩ := hx'
      exact ⟨c + c', fun i => (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (h1 i) (h1' i)),
        fun i hi => by simp [h0 i hi, h0' i hi], by simp [add_smul, Finset.sum_add_distrib]⟩
    | neg x _ hx =>
      obtain ⟨c, h1, h0, rfl⟩ := hx
      exact ⟨-c, fun i => by simpa using h1 i, fun i hi => by simp [h0 i hi], by simp⟩
  · rintro ⟨c, h1, h0, rfl⟩
    refine AddSubgroup.sum_mem _ fun i _ => ?_
    by_cases hi : i ∈ s
    · exact AddSubgroup.subset_closure ⟨c i, h1 i, _, ⟨i, hi, rfl⟩, rfl⟩
    · simp [h0 i hi]

variable (C) in

def Adapted (Λ : ℕ → AddSubgroup M) (b : Fin m → M) : Prop :=
  ∀ a : Fin m, Λ (a + 1) = Ospan (C := C) (b '' Set.Iic a)

theorem Adapted.exists_diag {Λ : ℕ → AddSubgroup M} {b b' : Fin m → M} (h : Adapted C Λ b) (h' : Adapted C Λ b') :
    ∃ d : Fin m → C, Diag b b' d ∧ ∀ a, ‖d a‖ ≤ 1 := by
  have : ∀ a, b' a ∈ Ospan (C := C) (b '' Set.Iic a) := fun a => by
    rw [← h a, h' a]
    exact AddSubgroup.subset_closure ⟨1, by simp, _, ⟨a, Set.mem_Iic.2 le_rfl, rfl⟩, (one_smul _ _).symm⟩
  choose c h1 h0 e using fun a => (mem_Ospan_image b _ _).1 (this a)
  exact ⟨fun a => c a a, fun a => ⟨c a, rfl, fun k hk => h0 a k (not_le.2 hk), e a⟩, fun a => h1 a a⟩

theorem Adapted.norm_diag {Λ : ℕ → AddSubgroup M} {b b' : Fin m → M} (h : Adapted C Λ b) (h' : Adapted C Λ b')
    (li : LinearIndependent C b) {d : Fin m → C} (hd : Diag b b' d) (a : Fin m) : ‖d a‖ = 1 := by
  obtain ⟨d₁, h₁, n₁⟩ := h.exists_diag h'
  obtain ⟨d₂, h₂, n₂⟩ := h'.exists_diag h
  obtain rfl := hd.unique li h₁
  have e : ‖d₂ a‖ * ‖d a‖ = 1 := by
    rw [← norm_mul, congrFun ((hd.trans h₂).unique li (Diag.refl b)) a, norm_one]
  refine le_antisymm (n₁ a) ?_
  nlinarith [n₂ a, norm_nonneg (d a)]

omit [IsUltrametricDist C] in

theorem linearIndependent_of_diag {w b : Fin m → M} {d : Fin m → C} (li : LinearIndependent C w) (h : Diag w b d)
    (hd : ∀ a, d a ≠ 0) : LinearIndependent C b := by
  classical
  choose A hA h0 e using h
  have hdet : (Matrix.of A).det ≠ 0 := by
    rw [Matrix.det_of_lowerTriangular (Matrix.of A) (fun i k hik => h0 i k hik)]
    exact Finset.prod_ne_zero_iff.2 fun a _ => fun h => hd a ((hA a).symm.trans h)
  refine Fintype.linearIndependent_iff.2 fun c hc => ?_
  have h1 : Matrix.vecMul c (Matrix.of A) = 0 := funext (Fintype.linearIndependent_iff.1 li _ (by
    rw [← hc]
    simp only [e, Finset.smul_sum, smul_smul, Matrix.vecMul, dotProduct, Finset.sum_smul, Matrix.of_apply]
    exact Finset.sum_comm))
  exact congrFun (Matrix.eq_zero_of_vecMul_eq_zero hdet h1)

omit [IsUltrametricDist C] in

theorem mem_span_of_diag {w b : Fin m → M} (h : ∃ d : Fin m → C, Diag w b d) {i a : Fin m} (hi : i ≤ a) :
    b i ∈ Submodule.span C (w '' Set.Iic a) :=
  Submodule.span_mono (Set.image_mono (Set.Iic_subset_Iic.2 hi)) ((diag_iff_span w b).1 h i)

omit [IsUltrametricDist C] in

theorem finrank_span_Iic {w : Fin m → M} (li : LinearIndependent C w) (a : Fin m) :
    Module.finrank C (Submodule.span C (w '' Set.Iic a)) = a + 1 := by
  rw [Set.image_eq_range]
  exact (finrank_span_eq_card (li.comp (fun b : Set.Iic a => (b : Fin m)) Subtype.val_injective)).trans (by simp)

theorem mem_Ospan_of_coord {n : ℕ} {V : Fin n → M} (li : LinearIndependent C V) (e : Fin m ↪ Fin n) {w : Fin m → M}
    (he : ∀ i, V (e i) = w i) {s : Set (Fin m)} {v : M} (hv : v ∈ Submodule.span C (w '' s)) {c : Fin n → C}
    (hc : ∀ k, ‖c k‖ ≤ 1) (e' : v = ∑ k, c k • V k) : v ∈ Ospan (C := C) (w '' s) := by
  obtain ⟨l, hl0, hl⟩ := (Finsupp.mem_span_image_iff_linearCombination C).1 hv
  rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype _ _ (by simp)] at hl
  refine (mem_Ospan_image w s v).2 ⟨l, fun i => ?_, fun i hi => (Finsupp.mem_supported' _ l).1 hl0 i hi, hl.symm⟩
  rw [← coeff_eq li e (cf := l) (c := c) (by simp only [he, hl, e']) i]
  exact hc _

omit [IsUltrametricDist C] in

theorem Ospan_le {s : Set M} {Λ : AddSubgroup M} (h : ∀ a : C, ‖a‖ ≤ 1 → ∀ v ∈ s, a • v ∈ Λ) : Ospan (C := C) s ≤ Λ :=
  (AddSubgroup.closure_le _).2 fun _ ⟨a, ha, v, hv, e⟩ => e ▸ h a ha v hv

end Linear

section Tangent

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
  {t : SAB H X} {S T : Type} [CommRing S] [CommRing T] {x : Sp S ⟶ X} {x' : Sp T ⟶ X}

theorem tanOf_map_sum (φ : S →+* T) (hx : spMap φ ≫ x = x') {m : ℕ} (u : Fin m → TanM x t.G) (a : Fin m → S) :
    tanOf (isTan_map φ hx (isTan_tv (∑ i, a i • u i))) = ∑ i, φ (a i) • tanOf (isTan_map φ hx (isTan_tv (u i))) :=
  (comb_iff (fun i => isTan_map φ hx (isTan_tv (u i))) _ _).1 (comb_map φ hx ((isComb_iff u a _).2 rfl))

def bcTan (φ : S →+* T) (hx : spMap φ ≫ x = x') : TanM x t.G →ₛₗ[φ] TanM x' t.G where
  toFun v := tanOf (isTan_map φ hx (isTan_tv v))
  map_add' v w := by simpa using tanOf_map_sum φ hx ![v, w] ![1, 1]
  map_smul' a v := by simpa using tanOf_map_sum φ hx ![v] ![a]

theorem left_bcTan (φ : S →+* T) (hx : spMap φ ≫ x = x') (v : TanM x t.G) :
    (tv (bcTan φ hx v)).left = spMap (dualMap φ) ≫ (tv v).left := rfl

end Tangent

theorem isGreatest_nrmSet_chart {X : Scheme.{0}} {p : ℕ} {C : SCF p} (z : Sp ↥(intO ↥C.S) ⟶ X) (hp : p ≠ 0) {L : LB X}
    (hL : L.IsLB) {i : L.ι} (hU : IsAffineOpen (L.U i)) (h : ⊤ ≤ z ⁻¹ᵁ L.U i) (s : Γ(GlobalTheory.LB.toMod L, PtNorm.gen X p)) :
    IsGreatest (PtNorm.nrmSet z _ s) ‖valR (PtNorm.zq z) _ (GlobalTheory.LB.coord s i)‖ := by
  haveI := GlobalTheory.LB.isQuasicoherent_toMod hL
  have hv : PtNorm.evq z hp h (GlobalTheory.LB.chartEquiv hL i inf_le_left (GlobalTheory.Twist.resM _ inf_le_right s)) =
      valR (PtNorm.zq z) _ (GlobalTheory.LB.coord s i) := by
    rw [← valR_res _ (inf_comm _ _).le (PtNorm.zq_le z hp h), valR_eq _ _ (PtNorm.zq_le z hp h)]
    exact congrArg (PtNorm.evq z hp h) (GlobalTheory.LB.resG_resG _ _ _)
  rw [PtNorm.nrmSet_eq z hp hU h]
  refine ⟨⟨(PtNorm.evq z hp h).toSemilinearMap.comp (GlobalTheory.LB.chartEquiv hL i inf_le_left).toLinearMap, fun m => ?_,
    (congrArg norm hv).symm⟩, ?_⟩
  · refine le_of_eq_of_le (congrArg (fun t => ‖PtNorm.evq z hp h t‖)
      (GlobalTheory.LB.chartEquiv_map hL i le_rfl inf_le_left m)) ?_
    rw [PtNorm.evq_res]
    exact (PtNorm.evz z h _).2
  · rintro r ⟨ν, hν, rfl⟩
    rw [← (GlobalTheory.LB.chartEquiv hL i inf_le_left).symm_apply_apply (GlobalTheory.Twist.resM _ _ _), GlobalTheory.LB.chartEquiv_symm_apply,
      ν.map_smulₛₗ, smul_eq_mul, norm_mul, hv]
    exact mul_le_of_le_one_right (norm_nonneg _) (hν _)

section Free

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}
  {Z : Mdl Y i₀} (y : Z.Pt)

def Lie : Type := TanM (y.gen ≫ Z.π) (Y Z.i).t.G

instance instAddCommGroupLie : AddCommGroup (Lie y) := inferInstanceAs (AddCommGroup (TanM (y.gen ≫ Z.π) (Y Z.i).t.G))

instance instModuleLie : Module ↥y.C.S (Lie y) := inferInstanceAs (Module ↥y.C.S (TanM (y.gen ≫ Z.π) (Y Z.i).t.G))

def act : 𝓞 E →+* Module.End ↥y.C.S (Lie y) := actR (Y Z.i).t.act

def lieEquiv : TanM y.gen Z.t.G ≃ₗ[↥y.C.S] Lie y := pushE Z.tMap y.gen rfl

abbrev LieInt : Type := TanM (y.z ≫ Z.π) (Y Z.i).t.G

theorem gen_π : spMap (intO ↥y.C.S).subtype ≫ y.z ≫ Z.π = y.gen ≫ Z.π := (Category.assoc _ _ _).symm

def toGen : LieInt y →ₛₗ[(intO ↥y.C.S).subtype] Lie y := bcTan _ (gen_π y)

def lieL : AddSubgroup (Lie y) := (toGen y).toAddMonoidHom.range

def eig (σ : E →+* ℂ) : Submodule ↥y.C.S (Lie y) :=
  ⨅ a : 𝓞 E, Module.End.eigenspace (act y a) (y.P.emb σ a)

def Wst (σ : E →+* ℂ) (i : ℕ) : Submodule ↥y.C.S (Lie y) :=
  Submodule.span ↥y.C.S
    {v | ∃ u : Vecs Dw (Y Z.i).t ↥y.C.S, Z.FlagAt y.gen u ∧ ∃ b : Fin (Dw.mult σ), (b : ℕ) < i ∧ (tv v).left = u σ b}

def taut (σ : E →+* ℂ) (i : ℕ) : AddSubgroup (Lie y) := (Wst y σ i).toAddSubgroup ⊓ lieL y

variable {y}

theorem mem_lieL {v : Lie y} : v ∈ lieL y ↔ ∃ w, IsTanAtG (Y Z.i).t (y.z ≫ Z.π) w ∧
    (tv v).left = spMap (dualMap (intO ↥y.C.S).subtype) ≫ w :=
  ⟨fun ⟨w, hw⟩ => ⟨_, isTan_tv w, hw ▸ rfl⟩, fun ⟨_, hw, e⟩ => ⟨tanOf hw, tan_ext e.symm⟩⟩

theorem smul_mem_lieL {a : ↥y.C.S} (ha : ‖a‖ ≤ 1) {v : Lie y} (hv : v ∈ lieL y) : a • v ∈ lieL y := by
  obtain ⟨w, rfl⟩ := hv
  exact ⟨(⟨a, ha⟩ : ↥(intO ↥y.C.S)) • w, (toGen y).map_smulₛₗ _ w⟩

theorem mem_eig {σ : E →+* ℂ} {v : Lie y} : v ∈ eig y σ ↔ ∀ a : 𝓞 E, act y a v = y.P.emb σ a • v := by
  simp only [eig, Submodule.mem_iInf, Module.End.mem_eigenspace_iff]

theorem mem_eig_iff_left {σ : E →+* ℂ} {v : Lie y} : v ∈ eig y σ ↔ ∀ a : 𝓞 E,
    (tv v).left ≫ ((Y Z.i).t.act.act a).left = spMap (epsMul (y.P.fK (embK Z.i.c σ a))) ≫ (tv v).left :=
  mem_eig.trans (forall_congr' fun _ => ⟨fun h => congrArg (fun z => (tv z).left) h, fun h => tan_ext h⟩)

variable (y) in

theorem range_gen : Set.range y.gen ⊆ Z.opn := by
  rintro _ ⟨s, rfl⟩
  have e : y.gen ≫ Z.π = y.P.y ≫ (Y Z.i).j := by rw [← gen_π, y.z_π, y.P.ext]
  exact ⟨y.P.y s, by rw [← Scheme.Hom.comp_apply, ← e, Scheme.Hom.comp_apply]⟩

theorem isFrame_of_flagAt {u : Vecs Dw (Y Z.i).t ↥y.C.S} (h : Z.FlagAt y.gen u) :
    IsFrame (Y Z.i).t y.P.fK (y.gen ≫ Z.π) u := by
  obtain ⟨a, φ, hx, hf, -⟩ := h
  have e : spMap ((φ.comp (Z.alg a)).comp (Z.i.c.V W).subtype) = spMap (y.P.fK.comp (Z.i.c.V W).subtype) := by
    rw [RingHom.comp_assoc, ← spMap_comp_spMap, ← Z.alg_s, ← Category.assoc, hx, ← Z.π_s, ← Category.assoc, ← gen_π,
      y.z_π, Category.assoc, y.P.yt_over, spMap_comp_spMap, y.P.compat]
  have e' : ∀ x ∈ Z.i.c.V W, φ.comp (Z.alg a) x = y.P.fK x := fun x hx =>
    RingHom.congr_fun (congrArg (fun f => f.hom) (Spec.map_injective e)) ⟨x, hx⟩
  have : φ.comp (Z.alg a) = y.P.fK := RingHom.ext fun x => ((Z.i.c.V W).mem_or_inv_mem x).elim (e' x) fun hx =>
    inv_injective (by rw [← map_inv₀, ← map_inv₀, e' _ hx])
  exact this ▸ hf

def flagVec {u : Vecs Dw (Y Z.i).t ↥y.C.S} (h : Z.FlagAt y.gen u) (σ : E →+* ℂ) (a : Fin (Dw.mult σ)) : Lie y :=
  tanOf ((isFrame_of_flagAt h).1 σ a).1

theorem flagVec_mem_eig {u : Vecs Dw (Y Z.i).t ↥y.C.S} (h : Z.FlagAt y.gen u) (σ : E →+* ℂ) (a : Fin (Dw.mult σ)) :
    flagVec h σ a ∈ eig y σ := mem_eig_iff_left.2 ((isFrame_of_flagAt h).1 σ a).2

theorem existsUnique_flagVec {u : Vecs Dw (Y Z.i).t ↥y.C.S} (h : Z.FlagAt y.gen u) {σ : E →+* ℂ} {v : Lie y}
    (hv : v ∈ eig y σ) : ∃! c : Fin (Dw.mult σ) → ↥y.C.S, v = ∑ a, c a • flagVec h σ a := by
  exact (existsUnique_congr fun c => LieMet.isComb_iff (flagVec h σ) c v).1
    ((isFrame_of_flagAt h).2 σ _ (isTan_tv v) (mem_eig_iff_left.1 hv))

theorem linearIndependent_flagVec {u : Vecs Dw (Y Z.i).t ↥y.C.S} (h : Z.FlagAt y.gen u) (σ : E →+* ℂ) :
    LinearIndependent ↥y.C.S (flagVec h σ) :=
  Fintype.linearIndependent_iffₛ.2 fun c _ e => congrFun
    ((existsUnique_flagVec h (Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ (c a) (flagVec_mem_eig h σ a))).unique
      rfl e)

theorem exists_diag_flagVec (hty : ∀ σ, Z.ty σ = Finset.range (Dw.mult σ + 1)) {u u' : Vecs Dw (Y Z.i).t ↥y.C.S}
    (h : Z.FlagAt y.gen u) (h' : Z.FlagAt y.gen u') (σ : E →+* ℂ) :
    ∃ d : Fin (Dw.mult σ) → ↥y.C.S, Diag (flagVec h σ) (flagVec h' σ) d :=
  exists_diag_of_flagAt Z hty h' h σ (fun a => ((isFrame_of_flagAt h').1 σ a).1)
    (fun a => ((isFrame_of_flagAt h).1 σ a).1) (linearIndependent_flagVec h σ)

variable (y) in

theorem Wst_le (σ : E →+* ℂ) (i : ℕ) : Wst y σ i ≤ eig y σ := by
  refine Submodule.span_le.2 ?_
  rintro v ⟨u, h, b, -, e⟩
  exact (tan_ext e : v = flagVec h σ b) ▸ flagVec_mem_eig h σ b

theorem Wst_succ (hty : ∀ σ, Z.ty σ = Finset.range (Dw.mult σ + 1)) {u : Vecs Dw (Y Z.i).t ↥y.C.S}
    (h : Z.FlagAt y.gen u) (σ : E →+* ℂ) (a : Fin (Dw.mult σ)) :
    Wst y σ (a + 1) = Submodule.span ↥y.C.S (flagVec h σ '' Set.Iic a) := by
  refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_mono ?_)
  · rintro v ⟨u', h', b, hb, e⟩
    obtain rfl : v = flagVec h' σ b := tan_ext e
    exact mem_span_of_diag (exists_diag_flagVec hty h h' σ) (Nat.lt_succ_iff.1 hb)
  · rintro _ ⟨b, hb, rfl⟩
    exact ⟨u, h, b, Nat.lt_succ_iff.2 hb, rfl⟩

theorem Wst_eq_eig {u : Vecs Dw (Y Z.i).t ↥y.C.S} (h : Z.FlagAt y.gen u) (σ : E →+* ℂ) {i : ℕ} (hi : Dw.mult σ ≤ i) :
    Wst y σ i = eig y σ := by
  refine le_antisymm (Wst_le y σ i) fun v hv => ?_
  obtain ⟨c, rfl⟩ := (existsUnique_flagVec h hv).exists
  exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨u, h, a, a.2.trans_le hi, rfl⟩)

theorem finrank_Wst_succ (hty : ∀ σ, Z.ty σ = Finset.range (Dw.mult σ + 1)) {u : Vecs Dw (Y Z.i).t ↥y.C.S}
    (h : Z.FlagAt y.gen u) (σ : E →+* ℂ) (a : Fin (Dw.mult σ)) :
    Module.finrank ↥y.C.S (Wst y σ (a + 1)) = a + 1 := by
  rw [Wst_succ hty h]
  exact finrank_span_Iic (linearIndependent_flagVec h σ) a

theorem flagAt_of_intFrame {U : Z.X.Opens} {hU : IsAffineOpen U} {w : Vecs Dw (Y Z.i).t Γ(Z.X, U)}
    (hw : IntFrame Z hU w) (h : ⊤ ≤ y.gen ⁻¹ᵁ U) : Z.FlagAt y.gen (w.bc (valMap y.gen U h).hom) := by
  have hx : spMap (valMap y.gen U h).hom ≫ hU.fromSpec = y.gen := specMap_valMap_fromSpec hU y.gen h
  have := hw.2 _ (valMap y.gen U h).hom (by rw [hx]; exact range_gen y)
  rwa [hx] at this

theorem gen_le {U : Z.X.Opens} (h : ⊤ ≤ y.z ⁻¹ᵁ U) : ⊤ ≤ y.gen ⁻¹ᵁ U := fun _ _ => h trivial

theorem adapted_taut (hty : ∀ σ, Z.ty σ = Finset.range (Dw.mult σ + 1)) {U : Z.X.Opens} {hU : IsAffineOpen U}
    {w : Vecs Dw (Y Z.i).t Γ(Z.X, U)} (hw : IntFrame Z hU w) (h : ⊤ ≤ y.z ⁻¹ᵁ U) (σ : E →+* ℂ) :
    Adapted ↥y.C.S (taut y σ) (flagVec (flagAt_of_intFrame hw (gen_le h)) σ) := by
  intro a
  have hz : spMap (valMap y.z U h).hom ≫ hU.fromSpec = y.z := specMap_valMap_fromSpec hU y.z h
  have hc : (intO ↥y.C.S).subtype.comp (valMap y.z U h).hom = (valMap y.gen U (gen_le h)).hom :=
    RingHom.ext fun f => by
      rw [RingHom.comp_apply, ← valR_eq, ← valR_eq, ← valR_spMap_comp _ _ _ h]
      rfl
  refine le_antisymm (fun v hv => ?_) (Ospan_le ?_)
  · obtain ⟨n, V, em, he, hV, hb⟩ := hw.1 σ
    obtain ⟨u, hu, eu⟩ := mem_lieL.1 hv.2
    have hz' : spMap (valMap y.z U h).hom ≫ hU.fromSpec ≫ Z.π = y.z ≫ Z.π := by rw [← Category.assoc, hz]
    have hg' : spMap (valMap y.gen U (gen_le h)).hom ≫ hU.fromSpec ≫ Z.π = y.gen ≫ Z.π := by
      rw [← Category.assoc]
      exact congrArg (· ≫ Z.π) (specMap_valMap_fromSpec hU y.gen (gen_le h))
    obtain ⟨cf, hcf⟩ := (basis_map _ hz' hV hb u hu).exists
    have hk := comb_map (intO ↥y.C.S).subtype (gen_π y) hcf
    simp only [dual_comp, hc, ← eu] at hk
    have hVk := fun i => isTan_map _ hg' (hV i)
    have h1 : v ∈ Wst y σ (a + 1) := hv.1
    rw [Wst_succ hty (flagAt_of_intFrame hw (gen_le h))] at h1
    exact mem_Ospan_of_coord (linInd_of_basis hVk (basis_map _ hg' hV hb)) em
      (w := flagVec (flagAt_of_intFrame hw (gen_le h)) σ)
      (fun i => tan_ext (congrArg (spMap (dualMap (valMap y.gen U (gen_le h)).hom) ≫ ·) (he i))) h1
      (fun k => (cf k).2) ((LieMet.isComb_iff (fun i => tanOf (hVk i)) _ v).1 hk)
  · rintro c hc1 _ ⟨i, hi, rfl⟩
    exact ⟨(Wst y σ (a + 1)).smul_mem c (Submodule.subset_span ⟨_, flagAt_of_intFrame hw (gen_le h), i,
        Nat.lt_succ_iff.2 hi, rfl⟩),
      smul_mem_lieL hc1 (mem_lieL.2 ⟨_, tan_bc hw _ hz σ i, by rw [Vecs.bc, dual_comp, hc]; rfl⟩)⟩

theorem gen_le_genO (hp : p ≠ 0) : ⊤ ≤ y.gen ⁻¹ᵁ Z.genO :=
  (le_preimage_basicOpen_iff y.gen (le_preimage_top _) _).2 (by
    rw [valR_eq _ _ (le_preimage_top _), map_natCast]
    exact (Nat.cast_ne_zero.2 hp).isUnit)

variable (y) in

def secVal {F : Z.X.Modules} {L : LB Z.X} (e : F ≅ GlobalTheory.LB.toMod L) (f : Γ(F, Z.genO)) (i : L.ι) : ↥y.C.S :=
  valR y.gen (Z.genO ⊓ L.U i) (GlobalTheory.LB.coord (e.hom.app Z.genO f) i)

theorem secVal_change (hp : p ≠ 0) {F : Z.X.Modules} {L : LB Z.X} (e : F ≅ GlobalTheory.LB.toMod L) (f : Γ(F, Z.genO)) {i i' : L.ι}
    (h : ⊤ ≤ y.gen ⁻¹ᵁ L.U i) (h' : ⊤ ≤ y.gen ⁻¹ᵁ L.U i') :
    secVal y e f i = valR y.gen _ (L.g i i').val * secVal y e f i' := by
  have hw : ⊤ ≤ y.gen ⁻¹ᵁ (Z.genO ⊓ L.U i ⊓ L.U i') := fun z hz => ⟨⟨gen_le_genO hp hz, h hz⟩, h' hz⟩
  have := congrArg (valR y.gen _) (GlobalTheory.LB.coord_rel (e.hom.app Z.genO f) i i' (W := Z.genO ⊓ L.U i ⊓ L.U i') inf_le_left
    (inf_le_inf_right _ inf_le_left) (inf_le_inf_right _ inf_le_right))
  rw [valR_mul _ _ hw] at this
  exact ((valR_res _ _ hw _).symm.trans this).trans (congrArg₂ (· * ·) (valR_res _ _ hw _) (valR_res _ _ hw _))

theorem nrm_eq_secVal (hp : p ≠ 0) {F : Z.X.Modules} {L : LB Z.X} (hL : L.IsLB) (e : F ≅ GlobalTheory.LB.toMod L)
    (f : Γ(F, Z.genO)) {i : L.ι} (hU : IsAffineOpen (L.U i)) (h : ⊤ ≤ y.z ⁻¹ᵁ L.U i) :
    Mdl.nrm F f y = ‖secVal y e f i‖ :=
  (congrArg sSup (PtNorm.nrmSet_iso y.z e f)).symm.trans (isGreatest_nrmSet_chart y.z hp hL hU h _).csSup_eq

theorem exists_diag_transition (hty : ∀ σ, Z.ty σ = Finset.range (Dw.mult σ + 1)) {U U' : Z.X.Opens}
    {hU : IsAffineOpen U} {hU' : IsAffineOpen U'} {w : Vecs Dw (Y Z.i).t Γ(Z.X, U)} {w' : Vecs Dw (Y Z.i).t Γ(Z.X, U')}
    (hw : IntFrame Z hU w) (hw' : IntFrame Z hU' w') {g : Γ(Z.X, U ⊓ U')} {e : ∀ σ : E →+* ℂ, Fin (Dw.mult σ) → ℤ}
    (hg : ∀ (k : Type) [Field k] (φ : Γ(Z.X, U) →+* k) (φ' : Γ(Z.X, U') →+* k) (d : ∀ σ : E →+* ℂ, Fin (Dw.mult σ) → k),
      spMap φ ≫ hU.fromSpec = spMap φ' ≫ hU'.fromSpec → Set.range (spMap φ ≫ hU.fromSpec) ⊆ Z.opn →
      (∀ σ a, ∃ cf : Fin (Dw.mult σ) → k, cf a = d σ a ∧ (∀ b, a < b → cf b = 0) ∧
        IsCombAtG (Y Z.i).t (spMap φ ≫ hU.fromSpec ≫ Z.π) (w'.bc φ' σ) cf (w.bc φ σ a)) →
      valR (spMap φ ≫ hU.fromSpec) _ g = ∏ σ, ∏ a, d σ a ^ e σ a)
    (h : ⊤ ≤ y.gen ⁻¹ᵁ U) (h' : ⊤ ≤ y.gen ⁻¹ᵁ U') :
    ∃ d : ∀ σ : E →+* ℂ, Fin (Dw.mult σ) → ↥y.C.S,
      (∀ σ, Diag (flagVec (flagAt_of_intFrame hw' h') σ) (flagVec (flagAt_of_intFrame hw h) σ) (d σ)) ∧
      (∀ σ a, d σ a ≠ 0) ∧ valR y.gen _ g = ∏ σ, ∏ a, d σ a ^ e σ a := by
  have hf := flagAt_of_intFrame hw h
  have hf' := flagAt_of_intFrame hw' h'
  choose d hd using exists_diag_flagVec hty hf' hf
  refine ⟨d, hd, fun σ a => ?_, ?_⟩
  · obtain ⟨d', hd'⟩ := exists_diag_flagVec hty hf hf' σ
    exact left_ne_zero_of_mul_eq_one
      (congrFun ((hd'.trans (hd σ)).unique (linearIndependent_flagVec hf σ) (Diag.refl _)) a)
  have hx : spMap (valMap y.gen _ h).hom ≫ hU.fromSpec = y.gen := specMap_valMap_fromSpec _ y.gen h
  have hx' : spMap (valMap y.gen _ h').hom ≫ hU'.fromSpec = y.gen := specMap_valMap_fromSpec _ y.gen h'
  have key := hg _ (valMap y.gen _ h).hom (valMap y.gen _ h').hom d
  rw [← Category.assoc, hx, hx'] at key
  exact key rfl (range_gen y) fun σ a => (hd σ a).imp fun cf hcf =>
    ⟨hcf.1, hcf.2.1, (LieMet.isComb_iff (flagVec hf' σ) cf (flagVec hf σ a)).2 hcf.2.2⟩

end Free

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {p : ℕ} (ct : At S κ p)

scoped instance fintypePsiT : Fintype (PsiT D) := Fintype.ofEquiv _ D.eTau

def embOf (s : PsiT D × Bool) : D.host.E →+* ℂ :=
  if s.2 then conjEmb (DV.tauEmb D (D.eTau.symm s.1)) else DV.tauEmb D (D.eTau.symm s.1)

def expOf (N : ℕ) (l : PsiT D → ℕ → ℤ) (s : PsiT D × Bool) (a : ℕ) : ℤ :=
  if s.2 then -l s.1 (N - a) else l s.1 (a + 1)

theorem prod_expo (l : PsiT D → ℕ → ℤ) {k : Type} [Field k] (d : ∀ σ : D.host.E →+* ℂ, Fin (S.Dw.mult σ) → k)
    (hd : ∀ σ a, d σ a ≠ 0) :
    ∏ σ, ∏ a, d σ a ^ ct.expo l σ a = ∏ s : PsiT D × Bool, ∏ a, d (embOf s) a ^ expOf N l s a := by
  classical
  have zs : ∀ (x : k), x ≠ 0 → ∀ (n : D.what₂.Tau → ℤ), x ^ (∑ t, n t) = ∏ t, x ^ n t := fun x hx n => by
    induction (Finset.univ : Finset D.what₂.Tau) using Finset.induction_on with
    | empty => simp
    | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, zpow_add₀ hx, ih]
  have one : ∀ (ρ : D.host.E →+* ℂ) (n : ℕ → ℤ),
      ∏ σ, ∏ a, d σ a ^ (if σ = ρ then n a else 0) = ∏ a, d ρ a ^ n a := fun ρ n => by
    rw [Finset.prod_eq_single ρ (fun σ _ hσ => by simp [hσ]) (by simp)]
    simp
  simp only [At.expo, zs _ (hd _ _), zpow_add₀ (hd _ _)]
  rw [Finset.prod_congr rfl fun σ _ => Finset.prod_comm, Finset.prod_comm, Fintype.prod_prod_type,
    ← Equiv.prod_comp D.eTau]
  refine Finset.prod_congr rfl fun t _ => ?_
  simp only [Finset.prod_mul_distrib]
  rw [Fintype.prod_bool, mul_comm]
  have e : ∀ b, embOf (D.eTau t, b) = if b then conjEmb (DV.tauEmb D t) else DV.tauEmb D t := fun b => by
    simp [embOf]
  refine congrArg₂ (· * ·) ?_ ?_
  · rw [← one (embOf (D.eTau t, true)) (expOf N l (D.eTau t, true)), e]
    simp [expOf]
  · rw [← one (embOf (D.eTau t, false)) (expOf N l (D.eTau t, false)), e]
    simp [expOf]

theorem ty_YY (σ : D.host.E →+* ℂ) : ct.YY.ty σ = Finset.range (S.Dw.mult σ + 1) := ct.isYY.2.1.1 σ

theorem exists_grLB (l : PsiT D → ℕ → ℤ) : ∃ L, IsGrLB ct.YY (ct.expo l) L := exists_isGrLB' ct.YY ct.isYY.2.1 _

def grLB (l : PsiT D → ℕ → ℤ) : LB ct.YY.X := (exists_grLB ct l).choose

theorem isGrLB_grLB (l : PsiT D → ℕ → ℤ) : IsGrLB ct.YY (ct.expo l) (grLB ct l) := (exists_grLB ct l).choose_spec

theorem grAff (l : PsiT D → ℕ → ℤ) (i : (grLB ct l).ι) : IsAffineOpen ((grLB ct l).U i) := (isGrLB_grLB ct l).2.choose i

def grFr (l : PsiT D → ℕ → ℤ) (i : (grLB ct l).ι) : Vecs S.Dw (ct.Y ct.YY.i).t Γ(ct.YY.X, (grLB ct l).U i) :=
  (isGrLB_grLB ct l).2.choose_spec.choose i

theorem intFrame_grFr (l : PsiT D → ℕ → ℤ) (i : (grLB ct l).ι) : IntFrame ct.YY (grAff ct l i) (grFr ct l i) :=
  (isGrLB_grLB ct l).2.choose_spec.choose_spec.1 i

theorem nonempty_grIso (l : PsiT D → ℕ → ℤ) : Nonempty ((ct.Lb l).toMod ≅ GlobalTheory.LB.toMod (grLB ct l)) := by
  haveI := (GlobalTheory.VB.isVB_toMod (isGrLB_grLB ct l).1).isFiniteQC
  unfold At.Lb
  rw [dif_pos (exists_grLB ct l)]
  exact GlobalTheory.ModelPresentation.nonempty_ofMod_toMod_iso _ _ _ _ p ct.W ct.hp ct.hW _ _ ct.YY (GlobalTheory.LB.toMod (grLB ct l))

def grIso (l : PsiT D → ℕ → ℤ) : (ct.Lb l).toMod ≅ GlobalTheory.LB.toMod (grLB ct l) := (nonempty_grIso ct l).some

variable {ct}

def chartVec (l : PsiT D → ℕ → ℤ) (y : ct.Pt ct.YY) {i : (grLB ct l).ι} (h : ⊤ ≤ y.gen ⁻¹ᵁ (grLB ct l).U i)
    (σ : D.host.E →+* ℂ) : Fin (S.Dw.mult σ) → Lie y :=
  flagVec (flagAt_of_intFrame (intFrame_grFr ct l i) h) σ

def IsReading (l : PsiT D → ℕ → ℤ) (f : ct.Sec (ct.Lb l)) (y : ct.Pt ct.YY)
    (Λ : PsiT D × Bool → ℕ → AddSubgroup (Lie y)) (r : ℝ) : Prop :=
  ∃ (i : (grLB ct l).ι) (h : ⊤ ≤ y.gen ⁻¹ᵁ (grLB ct l).U i) (b : ∀ s : PsiT D × Bool, Fin (S.Dw.mult (embOf s)) → Lie y)
    (d : ∀ s : PsiT D × Bool, Fin (S.Dw.mult (embOf s)) → ↥y.C.S),
    (∀ s, Adapted ↥y.C.S (Λ s) (b s)) ∧ (∀ s, Diag (chartVec l y h (embOf s)) (b s) (d s)) ∧ (∀ s a, d s a ≠ 0) ∧
    r = ‖secVal y (grIso ct l) f i * ∏ s, ∏ a, d s a ^ expOf N l s a‖

def nrmIn (l : PsiT D → ℕ → ℤ) (f : ct.Sec (ct.Lb l)) (y : ct.Pt ct.YY)
    (Λ : PsiT D × Bool → ℕ → AddSubgroup (Lie y)) : ℝ := sSup {r | IsReading l f y Λ r}

theorem exists_diag_chartVec (l : PsiT D → ℕ → ℤ) (y : ct.Pt ct.YY) {i i' : (grLB ct l).ι}
    (h : ⊤ ≤ y.gen ⁻¹ᵁ (grLB ct l).U i) (h' : ⊤ ≤ y.gen ⁻¹ᵁ (grLB ct l).U i') :
    ∃ d : ∀ σ : D.host.E →+* ℂ, Fin (S.Dw.mult σ) → ↥y.C.S, (∀ σ, Diag (chartVec l y h' σ) (chartVec l y h σ) (d σ)) ∧
      (∀ σ a, d σ a ≠ 0) ∧
      valR y.gen _ ((grLB ct l).g i i').val = ∏ s : PsiT D × Bool, ∏ a, d (embOf s) a ^ expOf N l s a := by
  obtain ⟨d, hd, h0, e⟩ := exists_diag_transition (ty_YY ct) (intFrame_grFr ct l i) (intFrame_grFr ct l i')
    ((isGrLB_grLB ct l).2.choose_spec.choose_spec.2 i i') h h'
  exact ⟨d, hd, h0, e.trans (prod_expo ct l d h0)⟩

theorem IsReading.eq_mul {l : PsiT D → ℕ → ℤ} {f : ct.Sec (ct.Lb l)} {y : ct.Pt ct.YY}
    {Λ Λ' : PsiT D × Bool → ℕ → AddSubgroup (Lie y)} {r r' : ℝ} (H : IsReading l f y Λ r) (H' : IsReading l f y Λ' r')
    {u u' : ∀ s : PsiT D × Bool, Fin (S.Dw.mult (embOf s)) → Lie y}
    {c : ∀ s : PsiT D × Bool, Fin (S.Dw.mult (embOf s)) → ↥y.C.S} (hu : ∀ s, Adapted ↥y.C.S (Λ s) (u s))
    (hu' : ∀ s, Adapted ↥y.C.S (Λ' s) (u' s)) (hc : ∀ s, Diag (u s) (u' s) (c s)) :
    r' = r * ∏ s, ∏ a, ‖c s a‖ ^ expOf N l s a := by
  obtain ⟨i, h, b, d, hb, hd, h0, rfl⟩ := H
  obtain ⟨i', h', b', d', hb', hd', h0', rfl⟩ := H'
  obtain ⟨g, hg, -, e⟩ := exists_diag_chartVec l y h h'
  have li := fun s => linearIndependent_flagVec (flagAt_of_intFrame (intFrame_grFr ct l i) h) (embOf s)
  have li' := fun s => linearIndependent_flagVec (flagAt_of_intFrame (intFrame_grFr ct l i') h') (embOf s)
  have key : ∀ s a, ‖d' s a‖ = ‖g (embOf s) a‖ * ‖d s a‖ * ‖c s a‖ := fun s a => by
    obtain ⟨c₁, h₁, -⟩ := (hb s).exists_diag (hu s)
    obtain ⟨c₂, h₂, -⟩ := (hu' s).exists_diag (hb' s)
    obtain ⟨c₃, h₃, -⟩ := (hb' s).exists_diag (hu' s)
    have lb := linearIndependent_of_diag (li s) (hd s) (h0 s)
    have lb' := linearIndependent_of_diag (li' s) (hd' s) (h0' s)
    have n₁ := (hb s).norm_diag (hu s) lb h₁ a
    have n₃ := fun a => (hb' s).norm_diag (hu' s) lb' h₃ a
    have n₂ := (hu' s).norm_diag (hb' s)
      (linearIndependent_of_diag lb' h₃ fun a h => by simpa [h] using n₃ a) h₂ a
    have := congrFun ((hd' s).unique (li' s) (((((hg _).trans (hd s)).trans h₁).trans (hc s)).trans h₂)) a
    rw [this]
    simp only [norm_mul, n₁, n₂]
    ring
  rw [secVal_change ct.hp.ne_zero _ f h h', e]
  simp only [norm_mul, norm_prod, norm_zpow, key, mul_zpow, Finset.prod_mul_distrib]
  ring

theorem IsReading.unique {l : PsiT D → ℕ → ℤ} {f : ct.Sec (ct.Lb l)} {y : ct.Pt ct.YY}
    {Λ : PsiT D × Bool → ℕ → AddSubgroup (Lie y)} {r r' : ℝ} (H : IsReading l f y Λ r) (H' : IsReading l f y Λ r') :
    r' = r := by
  obtain ⟨_, _, b, _, hb, -⟩ := id H
  simpa using H.eq_mul H' hb hb fun s => Diag.refl (b s)

theorem IsReading.nrmIn_eq {l : PsiT D → ℕ → ℤ} {f : ct.Sec (ct.Lb l)} {y : ct.Pt ct.YY}
    {Λ : PsiT D × Bool → ℕ → AddSubgroup (Lie y)} {r : ℝ} (H : IsReading l f y Λ r) : nrmIn l f y Λ = r := by
  rw [nrmIn, show {r | IsReading l f y Λ r} = {r} from Set.eq_singleton_iff_unique_mem.2 ⟨H, fun _ h => H.unique h⟩,
    csSup_singleton]

theorem exists_chart (l : PsiT D → ℕ → ℤ) (y : ct.Pt ct.YY) : ∃ i, ⊤ ≤ y.z ⁻¹ᵁ (grLB ct l).U i := by
  haveI := PtNorm.isLocalRing_intO ↥y.C.S
  have : y.z (IsLocalRing.closedPoint _) ∈ ⨆ i, (grLB ct l).U i := by rw [(isGrLB_grLB ct l).1.cover]; trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.1 this
  exact ⟨i, (PtNorm.top_le_preimage_iff _).2 hi⟩

theorem isReading_taut (l : PsiT D → ℕ → ℤ) (f : ct.Sec (ct.Lb l)) (y : ct.Pt ct.YY) :
    IsReading l f y (fun s => taut y (embOf s)) (ct.nrm (ct.Lb l) f y) := by
  obtain ⟨i, h⟩ := exists_chart l y
  refine ⟨i, gen_le h, fun s => chartVec l y (gen_le h) (embOf s), fun _ _ => 1,
    fun s => adapted_taut (ty_YY ct) (intFrame_grFr ct l i) h _, fun s => Diag.refl _, fun _ _ => one_ne_zero, ?_⟩
  simp only [one_zpow, Finset.prod_const_one]
  rw [_root_.mul_one]
  exact nrm_eq_secVal ct.hp.ne_zero (isGrLB_grLB ct l).1 (grIso ct l) f (grAff ct l i) h

theorem nrm_eq_nrmIn (l : PsiT D → ℕ → ℤ) (f : ct.Sec (ct.Lb l)) (y : ct.Pt ct.YY) :
    ct.nrm (ct.Lb l) f y = nrmIn l f y fun s => taut y (embOf s) := (isReading_taut l f y).nrmIn_eq.symm

variable (ct) in

def _root_.GlobalTheory.LocM.frmTrue : FrmSt ct where
  nrmRef l f y := nrmIn l f y fun s i => (Wst y (embOf s) i).toAddSubgroup ⊓ ((eig y (embOf s)).toAddSubgroup ⊓ lieL y)
  LieV y := Lie y
  lvAdd y := instAddCommGroupLie y
  lvMod y := instModuleLie y
  lieL y := lieL y
  eig y s := eig y (embOf s)
  Wst y s := Wst y (embOf s)
  Wst_le y s := Wst_le y (embOf s)
  taut y s := taut y (embOf s)
  taut_eq _ _ _ := rfl
  nrmIn := nrmIn
  nrmRef_def _ _ _ := rfl
  nrm_Lb_def := nrm_eq_nrmIn

theorem IsReading.eq_nrm_mul {l : PsiT D → ℕ → ℤ} {f : ct.Sec (ct.Lb l)} {y : ct.Pt ct.YY}
    {Λ : PsiT D × Bool → ℕ → AddSubgroup (Lie y)} {r : ℝ} (H : IsReading l f y Λ r)
    {u b : ∀ s : PsiT D × Bool, Fin (S.Dw.mult (embOf s)) → Lie y}
    {c : ∀ s : PsiT D × Bool, Fin (S.Dw.mult (embOf s)) → ↥y.C.S}
    (hu : ∀ s, Adapted ↥y.C.S (taut y (embOf s)) (u s)) (hb : ∀ s, Adapted ↥y.C.S (Λ s) (b s))
    (hc : ∀ s, Diag (u s) (b s) (c s)) :
    r = ct.nrm (ct.Lb l) f y * ∏ s, ∏ a, ‖c s a‖ ^ expOf N l s a :=
  (isReading_taut l f y).eq_mul H hu hb hc

theorem exists_flagAt_adapted (y : ct.Pt ct.YY) : ∃ (u : Vecs S.Dw (ct.Y ct.YY.i).t ↥y.C.S) (h : ct.YY.FlagAt y.gen u),
    ∀ σ, Adapted ↥y.C.S (taut y σ) (flagVec h σ) := by
  obtain ⟨i, h⟩ := exists_chart (fun _ _ => 0) y
  exact ⟨_, _, adapted_taut (ty_YY ct) (intFrame_grFr ct _ i) h⟩

theorem exists_isReading (l : PsiT D → ℕ → ℤ) (f : ct.Sec (ct.Lb l)) (y : ct.Pt ct.YY)
    {Λ : PsiT D × Bool → ℕ → AddSubgroup (Lie y)} {b : ∀ s : PsiT D × Bool, Fin (S.Dw.mult (embOf s)) → Lie y}
    (hb : ∀ s, Adapted ↥y.C.S (Λ s) (b s)) (li : ∀ s, LinearIndependent ↥y.C.S (b s))
    (hW : ∀ s (a : Fin (S.Dw.mult (embOf s))), b s a ∈ Wst y (embOf s) ((a : ℕ) + 1)) :
    ∃ r, IsReading l f y Λ r := by
  obtain ⟨i, h⟩ := exists_chart l y
  have hf := flagAt_of_intFrame (intFrame_grFr ct l i) (gen_le h)
  choose d hd using fun s => (diag_iff_span (k := ↥y.C.S) (flagVec hf (embOf s)) (b s)).2 fun a =>
    Wst_succ (ty_YY ct) hf (embOf s) a ▸ hW s a
  refine ⟨_, i, gen_le h, b, d, hb, hd, fun s a => ?_, rfl⟩
  obtain ⟨d', hd'⟩ := (hd s).symm (li s)
  exact left_ne_zero_of_mul_eq_one (congrFun ((hd'.trans (hd s)).unique (li s) (Diag.refl _)) a)

theorem nrmIn_eq_nrm_mul (l : PsiT D → ℕ → ℤ) (f : ct.Sec (ct.Lb l)) (y : ct.Pt ct.YY)
    {Λ : PsiT D × Bool → ℕ → AddSubgroup (Lie y)} {u b : ∀ s : PsiT D × Bool, Fin (S.Dw.mult (embOf s)) → Lie y}
    {c : ∀ s : PsiT D × Bool, Fin (S.Dw.mult (embOf s)) → ↥y.C.S}
    (hu : ∀ s, Adapted ↥y.C.S (taut y (embOf s)) (u s)) (hb : ∀ s, Adapted ↥y.C.S (Λ s) (b s))
    (li : ∀ s, LinearIndependent ↥y.C.S (b s)) (hc : ∀ s, Diag (u s) (b s) (c s)) :
    nrmIn l f y Λ = ct.nrm (ct.Lb l) f y * ∏ s, ∏ a, ‖c s a‖ ^ expOf N l s a := by
  obtain ⟨r, H⟩ := exists_isReading l f y hb li fun s a => by
    have hu' : ∀ k : Fin _, k ≤ a → u s k ∈ Wst y (embOf s) ((a : ℕ) + 1) := fun k hk =>
      (show u s k ∈ taut y (embOf s) ((a : ℕ) + 1) from hu s a ▸
        AddSubgroup.subset_closure ⟨1, by simp, _, ⟨k, hk, rfl⟩, (one_smul _ _).symm⟩).1
    refine Submodule.span_le.2 ?_ (mem_span_of_diag ⟨_, hc s⟩ (le_refl a))
    rintro _ ⟨k, hk, rfl⟩
    exact hu' k hk
  rw [H.nrmIn_eq, H.eq_nrm_mul hu hb hc]

example (y : ct.Pt ct.YY) (σ : D.host.E →+* ℂ) :
    (∀ a : Fin (S.Dw.mult σ), Module.finrank ↥y.C.S (Wst y σ (a + 1)) = a + 1) ∧ Wst y σ (S.Dw.mult σ) = eig y σ := by
  obtain ⟨u, h, -⟩ := exists_flagAt_adapted y
  exact ⟨finrank_Wst_succ (ty_YY ct) h σ, Wst_eq_eig h σ le_rfl⟩

example (y : ct.Pt ct.YY) (σ : D.host.E →+* ℂ) (hσ : 0 < S.Dw.mult σ) :
    ∃ v ∈ lieL y, (p : ↥y.C.S)⁻¹ • v ∉ lieL y := by
  obtain ⟨u, h, ha⟩ := exists_flagAt_adapted y
  have hv : flagVec h σ ⟨0, hσ⟩ ∈ taut y σ (((⟨0, hσ⟩ : Fin _) : ℕ) + 1) := ha σ ⟨0, hσ⟩ ▸
    AddSubgroup.subset_closure ⟨1, by simp, _, ⟨_, Set.mem_Iic.2 le_rfl, rfl⟩, (one_smul _ _).symm⟩
  refine ⟨_, hv.2, fun h' => ?_⟩
  have h2 : (p : ↥y.C.S)⁻¹ • flagVec h σ ⟨0, hσ⟩ ∈ taut y σ (((⟨0, hσ⟩ : Fin _) : ℕ) + 1) :=
    ⟨Submodule.smul_mem _ _ hv.1, h'⟩
  rw [ha σ ⟨0, hσ⟩, mem_Ospan_image] at h2
  obtain ⟨c, h1, -, e⟩ := h2
  have := Fintype.linearIndependent_iffₛ.1 (linearIndependent_flagVec h σ) (Pi.single ⟨0, hσ⟩ (p : ↥y.C.S)⁻¹) c
    (by simpa [Pi.single_apply, ite_smul] using e) ⟨0, hσ⟩
  have h3 := h1 ⟨0, hσ⟩
  rw [← this, Pi.single_eq_same, norm_inv, y.C.norm_p, inv_inv] at h3
  exact absurd h3 (not_le.2 (by exact_mod_cast ct.hp.one_lt))

example (l : PsiT D → ℕ → ℤ) (f : ct.Sec (ct.Lb l)) (y : ct.Pt ct.YY) {u : Vecs S.Dw (ct.Y ct.YY.i).t ↥y.C.S}
    (h : ct.YY.FlagAt y.gen u) (ha : ∀ σ, Adapted ↥y.C.S (taut y σ) (flagVec h σ))
    {Λ : PsiT D × Bool → ℕ → AddSubgroup (Lie y)}
    (hΛ : ∀ s, Adapted ↥y.C.S (Λ s) fun a => (p : ↥y.C.S) • flagVec h (embOf s) a) :
    nrmIn l f y Λ = ct.nrm (ct.Lb l) f y *
      ∏ s : PsiT D × Bool, ∏ a : Fin (S.Dw.mult (embOf s)), ((p : ℝ)⁻¹) ^ expOf N l s a := by
  classical
  have hd : ∀ s, Diag (flagVec h (embOf s)) (fun a => (p : ↥y.C.S) • flagVec h (embOf s) a) fun _ => (p : ↥y.C.S) :=
    fun s a => ⟨Pi.single a p, by simp, fun b hb => Pi.single_eq_of_ne hb.ne' _, by simp [Pi.single_apply, ite_smul]⟩
  rw [nrmIn_eq_nrm_mul l f y (fun s => ha _) hΛ (fun s => linearIndependent_of_diag (linearIndependent_flagVec h _) (hd s)
    fun _ => Nat.cast_ne_zero.2 ct.hp.ne_zero) hd, y.C.norm_p]

end GlobalTheory.LocM.Frm
