import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CutsSecOfIsLat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsChartOfMaximal

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open CategoryTheory Limits AlgebraicGeometry IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.LocM GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains GlobalTheory.BundleChernComparison GlobalTheory.ChainPts
open GlobalTheory.LineNorm (IsTanBasis)
open GlobalTheory.Twist (resM resM_resM resM_smul resM_self)
open Formalism.MainNotions.DIV.Cons (intO SCF)
open GlobalTheory.FieldPtGlue

namespace GlobalTheory.OmegaHT.SpanLoc

section Sheaf

variable {X : Scheme.{0}} {F : X.Modules} {r : ℕ} {V V' T : X.Opens}

def valH {k : Type} [Field k] {w : Sp k ⟶ X} {U : X.Opens} (h : ⊤ ≤ w ⁻¹ᵁ U) : Γ(X, U) →+* k :=
  (Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom.comp (w.appLE U ⊤ h).hom

theorem valF_eq {k : Type} [Field k] {w : Sp k ⟶ X} {U : X.Opens} (h : ⊤ ≤ w ⁻¹ᵁ U) (a : Γ(X, U)) :
    valF w U a = valH h a := dif_pos h

theorem valH_res {k : Type} [Field k] {w : Sp k ⟶ X} {U U' : X.Opens} (e : U' ≤ U) (h : ⊤ ≤ w ⁻¹ᵁ U') (a : Γ(X, U)) :
    valH h (resG X e a) = valF w U a := (valF_eq h _).symm.trans (valF_restrict e h a)

theorem exists_comb {p : ℕ} {η : Fin r → Γ(F, V)} (hη : SectionsSatisfyAtPrime p η) (σ : Γ(F, V')) :
    ∃ N : Fin r → Γ(X, V ⊓ V'), (p : Γ(X, V ⊓ V')) • resM F inf_le_right σ = ∑ l, N l • resM F inf_le_left (η l) := by
  obtain ⟨f, hf, hp⟩ := hη
  choose M hM using fun i => (Submodule.mem_span_range_iff_exists_fun _).1 (hp i)
  have h1 (i : Fin r) : (p : Γ(X, V ⊓ V')) • resM F (inf_le_left : V ⊓ V' ≤ V) (f i) =
      ∑ l, resG X (inf_le_left : V ⊓ V' ≤ V) (M i l) • resM F (inf_le_left : V ⊓ V' ≤ V) (η l) := by
    have := congrArg (resM F (inf_le_left : V ⊓ V' ≤ V)) (hM i)
    rw [map_sum, resM_smul, map_natCast] at this
    rw [← this]
    simp only [resM_smul]
  refine ⟨fun l => ∑ i, (hf.basis inf_le_left).repr (resM F inf_le_right σ) i * resG X inf_le_left (M i l), ?_⟩
  conv_lhs => rw [← (hf.basis inf_le_left).sum_repr (resM F (inf_le_right : V ⊓ V' ≤ V') σ)]
  simp only [Finset.smul_sum, Finset.sum_smul, mul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_comm, GlobalTheory.VB.IsFrame.basis_apply, h1, Finset.smul_sum]

theorem val_comb {p : ℕ} {η : Fin r → Γ(F, V)} {σ : Γ(F, V')} {N : Fin r → Γ(X, V ⊓ V')}
    (hN : (p : Γ(X, V ⊓ V')) • resM F inf_le_right σ = ∑ l, N l • resM F inf_le_left (η l))
    {s : Fin r → Γ(F, T)} (hs : GlobalTheory.VB.IsFrame s) {k : Type} [Field k] {w : Sp k ⟶ X}
    (hV : ⊤ ≤ w ⁻¹ᵁ V) (hV' : ⊤ ≤ w ⁻¹ᵁ V') (hT : ⊤ ≤ w ⁻¹ᵁ T) (i : Fin r) :
    (p : k) * valF w _ (crd hs σ i) = ∑ l, valF w _ (N l) * valF w _ (crd hs (η l) i) := by
  have hw : ⊤ ≤ w ⁻¹ᵁ ((V ⊓ V') ⊓ T) := fun q hq => ⟨⟨hV hq, hV' hq⟩, hT hq⟩
  have l₁ : (V ⊓ V') ⊓ T ≤ V ⊓ T := inf_le_inf_right _ inf_le_left
  have l₂ : (V ⊓ V') ⊓ T ≤ V' ⊓ T := inf_le_inf_right _ inf_le_right
  have h1 := congrArg (fun m => valH hw ((hs.basis inf_le_right).repr (resM F (inf_le_left : (V ⊓ V') ⊓ T ≤ _) m) i)) hN
  simp only [map_sum, resM_smul, resM_resM, map_natCast, map_smul, Finsupp.smul_apply, Finsupp.coe_finset_sum,
    Finset.sum_apply, smul_eq_mul, map_mul, valH_res] at h1
  rw [← valH_res l₂ hw, crd, ← hs.repr_resM, resM_resM]
  refine h1.trans (Finset.sum_congr rfl fun l _ => ?_)
  rw [← valH_res l₁ hw, crd, ← hs.repr_resM, resM_resM]

theorem exists_inv {p : ℕ} {η : Fin r → Γ(F, V)} (hη : SectionsSatisfyAtPrime p η) {s : Fin r → Γ(F, T)} (hs : GlobalTheory.VB.IsFrame s)
    {k : Type} [Field k] {w : Sp k ⟶ X} (hV : ⊤ ≤ w ⁻¹ᵁ V) (hT : ⊤ ≤ w ⁻¹ᵁ T) (hp : (p : k) ≠ 0) (l : Fin r) :
    ∃ cf : Fin r → k, ∀ j, ∑ i, cf i * valF w _ (crd hs (η j) i) = if j = l then 1 else 0 := by
  choose N hN using fun i => exists_comb hη (s i)
  let P : Matrix (Fin r) (Fin r) k := Matrix.of fun j i => valF w _ (crd hs (η j) i)
  let Q : Matrix (Fin r) (Fin r) k := Matrix.of fun j i => (p : k)⁻¹ * valF w _ (N j i)
  have hw : ⊤ ≤ w ⁻¹ᵁ (T ⊓ T) := fun q hq => ⟨hT hq, hT hq⟩
  have h1 : Q * P = 1 := by
    ext j i
    have := val_comb (hN j) hs hV hT hT i
    rw [valF_eq hw, crd, ← hs.basis_apply, Module.Basis.repr_self, Finsupp.single_apply, apply_ite (valH hw), map_one,
      map_zero] at this
    simp only [Matrix.mul_apply, Q, P, Matrix.of_apply, mul_assoc, Matrix.one_apply]
    rw [← Finset.mul_sum, ← this, inv_mul_cancel_left₀ hp]
  have h2 : P * Q = 1 := mul_eq_one_comm.1 h1
  refine ⟨fun i => Q i l, fun j => ?_⟩
  have := congrFun (congrFun h2 j) l
  rw [Matrix.mul_apply, Matrix.one_apply] at this
  rw [← this]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem span_of_ne {p : ℕ} {η : Fin r → Γ(F, V)} (hη : SectionsSatisfyAtPrime p η) (η' : Fin r → Γ(F, V')) {z : X} (hz : z ∈ V)
    (hz' : z ∈ V') (hp : (p : X.residueField z) ≠ 0) : ∃ (U : X.Opens) (h : U ≤ V) (h' : U ≤ V'), z ∈ U ∧
    ∀ j, resM F h' (η' j) ∈ Submodule.span Γ(X, U) (Set.range fun l => resM F h (η l)) := by
  have hle : X.basicOpen (p : Γ(X, V ⊓ V')) ≤ V ⊓ V' := X.basicOpen_le _
  refine ⟨X.basicOpen (p : Γ(X, V ⊓ V')), hle.trans inf_le_left, hle.trans inf_le_right, ?_, fun j => ?_⟩
  · by_contra hn
    have := (X.evaluation_eq_zero_iff_notMem_basicOpen z (show z ∈ V ⊓ V' from ⟨hz, hz'⟩) (p : Γ(X, V ⊓ V'))).2 hn
    rw [map_natCast] at this
    exact hp this
  · have hu : IsUnit (resG X hle (p : Γ(X, V ⊓ V'))) := X.toRingedSpace.isUnit_res_basicOpen _
    obtain ⟨N, hN⟩ := exists_comb hη (η' j)
    have h1 := congrArg (resM F hle) hN
    simp only [map_sum, resM_smul, resM_resM] at h1
    rw [← Submodule.smul_mem_iff_of_isUnit _ hu, h1]
    exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, rfl⟩)

end Sheaf

section Model

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}
  {Z : LocM.Mdl Y i₀}

theorem exists_inv_cast (hp : p ≠ 0) {X : Scheme.{0}} (h : X ⟶ Z.X) (a : Fin Z.m) :
    ∃ q : Γ(X, h ⁻¹ᵁ (Z.U a).1), q * p = 1 := by
  refine ⟨(h.app (Z.U a).1).hom (Z.alg a (p : Z.i.c.F)⁻¹), ?_⟩
  rw [← map_natCast ((h.app (Z.U a).1).hom.comp (Z.alg a)) p, RingHom.comp_apply, ← map_mul, ← map_mul,
    inv_mul_cancel₀ (Nat.cast_ne_zero.2 hp), map_one, map_one]

theorem cast_ne_zero (hp : p ≠ 0) {X : Scheme.{0}} (h : X ⟶ Z.X) {a : Fin Z.m} {k : Type} [Field k] {w : Sp k ⟶ X}
    (hw : ⊤ ≤ w ⁻¹ᵁ (h ⁻¹ᵁ (Z.U a).1)) : (p : k) ≠ 0 := by
  obtain ⟨q, hq⟩ := exists_inv_cast hp h a
  have := congrArg (valH hw) hq
  rw [map_mul, map_natCast, map_one] at this
  exact right_ne_zero_of_mul_eq_one this

theorem gen_le {X : Scheme.{0}} {h : X ⟶ Z.X} {y : Z.Pt} {w : Sp ↥(intO ↥y.C.S) ⟶ X} (hw : w ≫ h = y.z) {a : Fin Z.m}
    (ha : ⊤ ≤ y.gen ⁻¹ᵁ (Z.U a).1) : ⊤ ≤ (spMap (intO ↥y.C.S).subtype ≫ w) ⁻¹ᵁ (h ⁻¹ᵁ (Z.U a).1) := by
  have e : (spMap (intO ↥y.C.S).subtype ≫ w) ≫ h = y.gen := by rw [Category.assoc, hw]; rfl
  rw [← e] at ha
  exact ha

theorem norm_le (hp : p ≠ 0) {X : Scheme.{0}} {h : X ⟶ Z.X} {r : ℕ} {x : Fin r → Letter Dw} {b : Bool} {F : X.Modules}
    {s : ∀ a : Fin Z.m, Fin r → Γ(F, h ⁻¹ᵁ (Z.U a).1)} {hs : ∀ a, GlobalTheory.VB.IsFrame (s a)} {V V' : X.Opens}
    {η : Fin r → Γ(F, V)} {η' : Fin r → Γ(F, V')} (hη : SectionsSatisfyAtPrime p η) (c : CutsSec Z h x b hs η)
    (c' : CutsSec Z h x b hs η') {j : Fin r} {N : Fin r → Γ(X, V ⊓ V')}
    (hN : (p : Γ(X, V ⊓ V')) • resM F inf_le_right (η' j) = ∑ l, N l • resM F inf_le_left (η l)) (l : Fin r)
    (y : Z.Pt) (w : Sp ↥(intO ↥y.C.S) ⟶ X) (hw : w ≫ h = y.z) (a : Fin Z.m) (ha : ⊤ ≤ y.gen ⁻¹ᵁ (Z.U a).1)
    (hU : ⊤ ≤ w ⁻¹ᵁ (V ⊓ V')) :
    ‖(p : ↥y.C.S)⁻¹ * valF (spMap (intO ↥y.C.S).subtype ≫ w) _ (N l)‖ ≤ 1 := by
  let w' : Sp ↥y.C.S ⟶ X := spMap (intO ↥y.C.S).subtype ≫ w
  have hT : ⊤ ≤ w' ⁻¹ᵁ (h ⁻¹ᵁ (Z.U a).1) := gen_le hw ha
  have hV : ⊤ ≤ w' ⁻¹ᵁ V := fun q _ => (hU (Set.mem_univ (spMap (intO ↥y.C.S).subtype q))).1
  have hV' : ⊤ ≤ w' ⁻¹ᵁ V' := fun q _ => (hU (Set.mem_univ (spMap (intO ↥y.C.S).subtype q))).2
  have hpk : (p : ↥y.C.S) ≠ 0 := cast_ne_zero hp h hT
  obtain ⟨φ, hφ⟩ := Pull.exists_fromSpec (Z.U a).2 y.gen ha
  have hφ' : spMap φ ≫ Z.chart a = y.gen := hφ
  obtain ⟨cf, hcf⟩ := exists_inv hη (hs a) hV hT hpk l
  have htan (i : Fin r) : IsTanAtG (Y Z.i).t (y.gen ≫ Z.π) ((Z.fr a).bc φ (x i).1 (x i).2) :=
    LieMet.isTan_map φ (by rw [← Category.assoc, hφ']) ((Z.frame a).1 _ _).1
  have hv : IsCombAtG (Y Z.i).t (y.gen ≫ Z.π) (fun i => (Z.fr a).bc φ (x i).1 (x i).2) cf _ :=
    (isCombAtG_iff (Y Z.i).t (y.gen ≫ Z.π) (fun i => ovT (htan i)) cf _).2 rfl
  have h1 := (c y w hw a φ hφ' (fun q hq => (hU hq).1) cf _ hv).2 fun j' => by
    rw [hcf]
    split_ifs <;> simp
  have h2 := (c' y w hw a φ hφ' (fun q hq => (hU hq).2) cf _ hv).1 h1 j
  convert h2 using 2
  rw [inv_mul_eq_iff_eq_mul₀ hpk, Finset.mul_sum]
  have h3 (i : Fin r) : (p : ↥y.C.S) * (cf i * valF w' _ (crd (hs a) (η' j) i)) =
      ∑ m, valF w' _ (N m) * (cf i * valF w' _ (crd (hs a) (η m) i)) := by
    rw [mul_left_comm, val_comb hN (hs a) hV hV' hT, Finset.mul_sum]
    exact Finset.sum_congr rfl fun m _ => mul_left_comm _ _ _
  refine Eq.symm ((Finset.sum_congr rfl fun i _ => h3 i).trans ?_)
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum, hcf, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rfl

theorem span_of_ext (hp0 : p ≠ 0) {X : Scheme.{0}} [IsReduced X] {h : X ⟶ Z.X} (hopn : ToOpen Z h) {r : ℕ}
    {F : X.Modules} {V V' : X.Opens} {η : Fin r → Γ(F, V)} {η' : Fin r → Γ(F, V')} (hη : SectionsSatisfyAtPrime p η)
    {N : Fin r → Fin r → Γ(X, V ⊓ V')}
    (hN : ∀ j, (p : Γ(X, V ⊓ V')) • resM F inf_le_right (η' j) = ∑ l, N j l • resM F inf_le_left (η l))
    {z : X} (hz : z ∈ V) (hz' : z ∈ V') {U : Fin r → Fin r → X.Opens} (t : ∀ j l, Γ(X, U j l))
    (hzU : ∀ j l, z ∈ U j l)
    (ht : ∀ j l (k : Type) [Field k] (w : Sp k ⟶ X) (a : Fin Z.m), ⊤ ≤ w ⁻¹ᵁ (h ⁻¹ᵁ (Z.U a).1) → ⊤ ≤ w ⁻¹ᵁ U j l →
      ⊤ ≤ w ⁻¹ᵁ (V ⊓ V') → valF w _ (t j l) = (p : k)⁻¹ * valF w _ (N j l)) :
    ∃ (U : X.Opens) (h : U ≤ V) (h' : U ≤ V'), z ∈ U ∧
      ∀ j, resM F h' (η' j) ∈ Submodule.span Γ(X, U) (Set.range fun l => resM F h (η l)) := by
  let U₀ : X.Opens := (V ⊓ V') ⊓ Finset.univ.inf fun jl : Fin r × Fin r => U jl.1 jl.2
  have hz₀ : z ∈ U₀ := ⟨⟨hz, hz'⟩, by
    rw [TopologicalSpace.Opens.coe_finset_inf]; simpa using hzU⟩
  have hle (j l : Fin r) : U₀ ≤ U j l :=
    inf_le_right.trans (Finset.inf_le (f := fun jl : Fin r × Fin r => U jl.1 jl.2) (Finset.mem_univ (j, l)))
  have l₀ : U₀ ≤ V ⊓ V' := inf_le_left
  refine ⟨U₀, l₀.trans inf_le_left, l₀.trans inf_le_right, hz₀, fun j => ?_⟩
  have h1 (l : Fin r) : resG X l₀ (N j l) = p * resG X (hle j l) (t j l) := by
    refine GlobalTheory.TestPts.ext_chart h hopn fun k _ w a ha hw => ?_
    rw [valF_eq hw, valF_eq hw, map_mul, map_natCast, valH_res, valH_res,
      ht j l k w a ha (fun q hq => hle j l (hw hq)) (fun q hq => l₀ (hw hq)),
      mul_inv_cancel_left₀ (cast_ne_zero hp0 h ha)]
  have h2 := congrArg (resM F l₀) (hN j)
  simp only [map_sum, resM_smul, resM_resM, map_natCast, h1, mul_smul] at h2
  rw [← Finset.smul_sum] at h2
  obtain ⟨f, hf, -⟩ := hη
  have h3 : resM F (l₀.trans inf_le_right) (η' j) =
      ∑ l, resG X (hle j l) (t j l) • resM F (l₀.trans inf_le_left) (η l) := by
    refine (hf.basis (l₀.trans inf_le_left)).ext_elem fun i => ?_
    have h4 := congrArg (fun m => (hf.basis (l₀.trans inf_le_left)).repr m i) h2
    simp only [map_smul, Finsupp.smul_apply, smul_eq_mul] at h4
    refine GlobalTheory.TestPts.ext_chart h hopn fun k _ w a ha hw => ?_
    have h5 := congrArg (valH hw) h4
    rw [map_mul, map_mul, map_natCast] at h5
    rw [valF_eq hw, valF_eq hw]
    exact mul_left_cancel₀ (cast_ne_zero hp0 h ha) h5
  rw [h3]
  exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, rfl⟩)

end Model

theorem spanSt : GlobalTheory.OmegaHT.SpanSt := by
  intro E _ _ _ H Dw Xo p W Y i₀ Z hp hW _ B hB h hopn r x b F s hs V V' η η' hη _ c c' z hz hz'
  by_cases hpz : (p : B.X.residueField z) = 0
  swap
  · exact span_of_ne hη η' hz hz' hpz
  have hp0 : p ≠ 0 := hp.ne_zero
  choose N hN using fun j => exists_comb hη (η' j)
  choose q hq using fun a => exists_inv_cast (Z := Z) hp0 h a
  let A : Fin r → Fin r → ∀ a, Γ(B.X, h ⁻¹ᵁ (Z.U a).1 ⊓ (V ⊓ V')) := fun j l a =>
    resG B.X inf_le_left (q a) * resG B.X inf_le_right (N j l)
  have hA (j l : Fin r) (k : Type) [Field k] (w : Sp k ⟶ B.X) (a : Fin Z.m) (ha : ⊤ ≤ w ⁻¹ᵁ (h ⁻¹ᵁ (Z.U a).1))
      (hU : ⊤ ≤ w ⁻¹ᵁ (V ⊓ V')) : valF w _ (A j l a) = (p : k)⁻¹ * valF w _ (N j l) := by
    have hw : ⊤ ≤ w ⁻¹ᵁ (h ⁻¹ᵁ (Z.U a).1 ⊓ (V ⊓ V')) := fun q hq => ⟨ha hq, hU hq⟩
    have h1 := congrArg (valH ha) (hq a)
    rw [map_mul, map_natCast, map_one] at h1
    rw [valF_eq hw, map_mul, valH_res, valH_res, valF_eq ha, eq_inv_of_mul_eq_one_left h1]
  have key (j l : Fin r) := GlobalTheory.TestPts.exists_extension hp hW hB h hopn (A j l)
    (fun k _ w a a' ha ha' hU => by rw [hA j l k w a ha hU, hA j l k w a' ha' hU])
    (fun y w hw a ha hU => by
      have e := hA j l _ _ a (gen_le hw ha) fun q _ => hU (Set.mem_univ (spMap (intO ↥y.C.S).subtype q))
      exact (congrArg norm e).trans_le (norm_le hp0 hη c c' (hN j) l y w hw a ha hU))
    (show z ∈ V ⊓ V' from ⟨hz, hz'⟩) hpz
  choose U t hzU hUV ht using key
  exact span_of_ext hp0 hopn hη hN hz hz' t hzU fun j l k _ w a ha hw hU =>
    (ht j l k w a ha hw).trans (hA j l k w a ha hU)

end GlobalTheory.OmegaHT.SpanLoc
