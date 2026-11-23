import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CutsSecOfIsLat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeUniquenessOfCovering
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentSectionsFormFrame

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open CategoryTheory Limits AlgebraicGeometry IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.LocM GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains GlobalTheory.BundleChernComparison GlobalTheory.ChainPts
open GlobalTheory.Twist (resM resM_resM resM_self resM_smul app_resM sec_ext_of_cover exists_sec_of_cover)
open Formalism.MainNotions.DIV.Cons (intO SCF)
open GlobalTheory.ChainPts.LatUniq (resM_inj coef_mul exists_frames exists_ext exists_ev)

namespace GlobalTheory.OmegaHT.Transpose

section General

variable {X : Scheme.{0}} {F G : X.Modules} {U : X.Opens} {r r' : ℕ}

def lin {s : Fin r → Γ(F, U)} (hs : GlobalTheory.VB.IsFrame s) (t : Fin r → Γ(G, U)) {V : X.Opens} (h : V ≤ U) :
    Γ(F, V) →ₗ[Γ(X, V)] Γ(G, V) :=
  (hs.basis h).constr Γ(X, V) fun i => resM G h (t i)

theorem lin_apply {s : Fin r → Γ(F, U)} (hs : GlobalTheory.VB.IsFrame s) (t : Fin r → Γ(G, U)) {V : X.Opens} (h : V ≤ U)
    (σ : Γ(F, V)) : lin hs t h σ = ∑ i, (hs.basis h).repr σ i • resM G h (t i) :=
  (hs.basis h).constr_apply_fintype _ _ σ

theorem lin_frame {s : Fin r → Γ(F, U)} (hs : GlobalTheory.VB.IsFrame s) (t : Fin r → Γ(G, U)) {V : X.Opens} (h : V ≤ U)
    (i : Fin r) : lin hs t h (resM F h (s i)) = resM G h (t i) := by
  rw [← hs.basis_apply h]
  exact (hs.basis h).constr_basis _ _ i

theorem lin_resM {s : Fin r → Γ(F, U)} (hs : GlobalTheory.VB.IsFrame s) (t : Fin r → Γ(G, U)) {V V' : X.Opens} (h : V ≤ U)
    (h' : V' ≤ V) (σ : Γ(F, V)) : resM G h' (lin hs t h σ) = lin hs t (h'.trans h) (resM F h' σ) := by
  rw [lin_apply, lin_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [resM_smul, resM_resM, hs.repr_resM h h']

theorem exists_hom [IsIntegral X] (hG : GlobalTheory.VB.IsVB G r') (hU : (U : Set X).Nonempty) {s : Fin r → Γ(F, U)}
    (hs : GlobalTheory.VB.IsFrame s) (s' : Fin r → Γ(G, U))
    (H : ∀ x : X, ∃ (V : X.Opens) (e : Fin r → Γ(F, V)) (t : Fin r → Γ(G, V)), x ∈ V ∧ GlobalTheory.VB.IsFrame e ∧
      ∀ j, resM G inf_le_left (t j) = lin hs s' (inf_le_right : V ⊓ U ≤ U) (resM F inf_le_left (e j))) :
    ∃ u : F ⟶ G, ∀ i, u.app U (s i) = s' i := by
  have nat {V W : X.Opens} (h : W ≤ V) {σ : Γ(F, V)} {τ : Γ(G, V)}
      (k : resM G inf_le_left τ = lin hs s' (inf_le_right : V ⊓ U ≤ U) (resM F inf_le_left σ)) :
      resM G inf_le_left (resM G h τ) = lin hs s' (inf_le_right : W ⊓ U ≤ U) (resM F inf_le_left (resM F h σ)) := by
    have k' := congrArg (resM G (inf_le_inf_right U h)) k
    rw [lin_resM, resM_resM, resM_resM] at k'
    rw [resM_resM, resM_resM]
    exact k'
  have ex (V : X.Opens) (σ : Γ(F, V)) : ∃ τ : Γ(G, V),
      resM G inf_le_left τ = lin hs s' (inf_le_right : V ⊓ U ≤ U) (resM F inf_le_left σ) := by
    have loc (x : V) : ∃ (W : X.Opens) (h : W ≤ V) (τ : Γ(G, W)), x.1 ∈ W ∧
        resM G inf_le_left τ = lin hs s' (inf_le_right : W ⊓ U ≤ U) (resM F inf_le_left (resM F h σ)) := by
      obtain ⟨W, e, t, hx, he, ht⟩ := H x
      refine ⟨V ⊓ W, inf_le_left, ∑ j, (he.basis inf_le_right).repr (resM F inf_le_left σ) j • resM G inf_le_right (t j),
        ⟨x.2, hx⟩, ?_⟩
      conv_rhs => rw [← (he.basis (inf_le_right : V ⊓ W ≤ W)).sum_repr (resM F inf_le_left σ)]
      simp only [map_sum, resM_smul, map_smul, GlobalTheory.VB.IsFrame.basis_apply, nat inf_le_right (ht _)]
    choose W hW τ hx hτ using loc
    have hc : V ≤ iSup W := fun x hxV => TopologicalSpace.Opens.mem_iSup.2 ⟨⟨x, hxV⟩, hx _⟩
    obtain ⟨t, ht⟩ := exists_sec_of_cover W hW hc τ fun x y => resM_inj hG hU (by
      rw [nat inf_le_left (hτ x), nat inf_le_right (hτ y), resM_resM, resM_resM, resM_resM, resM_resM])
    refine ⟨t, sec_ext_of_cover (fun x => W x ⊓ U) (fun x => inf_le_inf_right U (hW x))
      (fun x hxV => TopologicalSpace.Opens.mem_iSup.2 ⟨⟨x, hxV.1⟩, hx _, hxV.2⟩) fun x => ?_⟩
    have k := hτ x
    rw [← ht x, resM_resM, resM_resM] at k
    rw [lin_resM, resM_resM, resM_resM]
    exact k
  choose u hu using ex
  refine ⟨GlobalTheory.LB.homOfLinear (fun V =>
    { toFun := u V
      map_add' := fun a b => resM_inj hG hU (by simp only [map_add, hu])
      map_smul' := fun a b => resM_inj hG hU (by simp only [resM_smul, map_smul, hu, RingHom.id_apply]) })
    fun h σ => resM_inj hG hU ((hu _ _).trans (nat h (hu _ σ)).symm), fun i => resM_inj hG hU ?_⟩
  exact (hu U (s i)).trans (lin_frame hs s' _ i)

theorem lin_eq_sum {V : X.Opens} {e : Fin r → Γ(F, V)} {e' : Fin r → Γ(G, V)} {s : Fin r → Γ(F, U)}
    {s' : Fin r → Γ(G, U)} (he : GlobalTheory.VB.IsFrame e) (he' : GlobalTheory.VB.IsFrame e') (hs : GlobalTheory.VB.IsFrame s)
    (hs' : GlobalTheory.VB.IsFrame s') (c : Fin r → Γ(X, U)) (j : Fin r) :
    lin hs (fun i => c i • s' i) (inf_le_right : V ⊓ U ≤ U) (resM F inf_le_left (e j)) =
      ∑ l, (∑ i, coef true he hs j i * (resG X inf_le_right (c i) * coef false he' hs' l i)) •
        resM G inf_le_left (e' l) := by
  rw [lin_apply]
  simp only [Finset.sum_smul, mul_smul, resM_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.smul_sum, ← Finset.smul_sum]
  congr 2
  rw [← (he'.basis (inf_le_left : V ⊓ U ≤ V)).sum_repr (resM G inf_le_right (s' i))]
  simp only [GlobalTheory.VB.IsFrame.basis_apply]
  rfl

theorem exists_local {V : X.Opens} {e : Fin r → Γ(F, V)} {e' : Fin r → Γ(G, V)} {s : Fin r → Γ(F, U)}
    {s' : Fin r → Γ(G, U)} (he : GlobalTheory.VB.IsFrame e) (hs : GlobalTheory.VB.IsFrame s) {x : X} (hx : x ∈ V)
    (A : Fin r → Fin r → Γ(X, V ⊓ U))
    (hA : ∀ j, lin hs s' (inf_le_right : V ⊓ U ≤ U) (resM F inf_le_left (e j)) = ∑ l, A j l • resM G inf_le_left (e' l))
    (H : ∀ j l : Fin r, ∃ (T : X.Opens) (hT : T ≤ V) (t : Γ(X, T)), x ∈ T ∧ resG X inf_le_left t =
      resG X (inf_le_inf_right U hT) (A j l)) :
    ∃ (V : X.Opens) (e : Fin r → Γ(F, V)) (t : Fin r → Γ(G, V)), x ∈ V ∧ GlobalTheory.VB.IsFrame e ∧
      ∀ j, resM G inf_le_left (t j) = lin hs s' (inf_le_right : V ⊓ U ≤ U) (resM F inf_le_left (e j)) := by
  choose T hT t hxT ht using fun q : Fin r × Fin r => H q.1 q.2
  obtain ⟨V', hxV, hle, hV⟩ : ∃ V' : X.Opens, x ∈ V' ∧ V' ≤ V ∧ ∀ q, V' ≤ T q :=
    ⟨V ⊓ Finset.univ.inf T, ⟨hx, by rw [TopologicalSpace.Opens.coe_finset_inf]; simpa using hxT⟩, inf_le_left,
      fun q => inf_le_right.trans (Finset.inf_le (Finset.mem_univ q))⟩
  refine ⟨V', _, fun j => ∑ l, resG X (hV (j, l)) (t (j, l)) • resM G hle (e' l), hxV, he.res hle, fun j => ?_⟩
  have k := congrArg (resM G (inf_le_inf_right U hle)) (hA j)
  rw [lin_resM, resM_resM] at k
  rw [resM_resM]
  refine Eq.trans ?_ k.symm
  rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [resM_smul, resM_smul, resM_resM, resM_resM]
  have k' := congrArg (resG X (inf_le_inf_right U (hV (j, l)))) (ht (j, l))
  rw [GlobalTheory.LB.resG_resG, GlobalTheory.LB.resG_resG] at k'
  rw [GlobalTheory.LB.resG_resG, k']

theorem app_eq [IsIntegral X] (hG : GlobalTheory.VB.IsVB G r') (hU : (U : Set X).Nonempty) {V : X.Opens} {e : Fin r → Γ(F, V)}
    {e' : Fin r → Γ(G, V)} {s : Fin r → Γ(F, U)} {s' : Fin r → Γ(G, U)} (he : GlobalTheory.VB.IsFrame e) (he' : GlobalTheory.VB.IsFrame e')
    (hs : GlobalTheory.VB.IsFrame s) (hs' : GlobalTheory.VB.IsFrame s') {u : F ⟶ G} {c : Fin r → Γ(X, U)} {d : Fin r → Γ(X, V)}
    (hu : ∀ i, u.app U (s i) = c i • s' i)
    (H : ∀ i j, coef true he hs i j * resG X inf_le_right (c j) = resG X inf_le_left (d i) * coef true he' hs' i j)
    (i : Fin r) : u.app V (e i) = d i • e' i := by
  refine resM_inj hG hU ?_
  rw [← app_resM, resM_smul, ← (hs.basis (inf_le_right : V ⊓ U ≤ U)).sum_repr (resM F inf_le_left (e i)),
    ← (hs'.basis (inf_le_right : V ⊓ U ≤ U)).sum_repr (resM G inf_le_left (e' i))]
  simp only [map_sum, Scheme.Modules.Hom.app_smul, GlobalTheory.VB.IsFrame.basis_apply, app_resM, hu, resM_smul, Finset.smul_sum,
    smul_smul]
  exact Finset.sum_congr rfl fun j _ => congrArg (· • resM G inf_le_right (s' j)) (H i j)

end General

section Tan

open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv actR)
open GlobalTheory.LieMet GlobalTheory.ShFam.Pad.Pull
open scoped MonObj

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {X : Scheme.{0}} {t : SAB H X} {l : Level H} {c : Coeff l} {k : Type} [Field k] {y : Sp k ⟶ X} {r : ℕ}
  {x : Fin r → Letter Dw}

theorem comb_op {f : c.F →+* k} {u : Vecs Dw t k} (hu : GlobalTheory.LocM.IsFrame t f y u) {cf : Fin r → k}
    {v : Sp (DualNumber k) ⟶ t.G.left} (hv : IsCombAtG t y (fun i => u (x i).1 (x i).2) cf v) (g : k) (a : 𝓞 E) :
    IsTanAtG t y v ∧ IsCombAtG t y (fun i => u (x i).1 (x i).2) (fun i => cf i * (g * f (embK c (x i).1 a)))
      (spMap (epsMul g) ≫ v ≫ (t.act.act a).left) := by
  let U : Fin r → TanM y t.G := fun i => tanOf (hu.1 (x i).1 (x i).2).1
  obtain rfl := (comb_iff U cf v).1 hv
  refine ⟨isTan_tv _, (comb_iff U _ _).2 ?_⟩
  have e : g • actR t.act a (∑ i, cf i • U i) = ∑ i, (cf i * (g * f (embK c (x i).1 a))) • U i := by
    rw [map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, (eig_iff (U i) a _).1 ((hu.1 (x i).1 (x i).2).2 a), smul_smul, smul_smul, mul_comm g, mul_assoc]
  rw [← e]
  rfl

theorem comb_unique {f : c.F →+* k} {u : Vecs Dw t k} (hu : GlobalTheory.LocM.IsFrame t f y u) (hx : Function.Bijective x)
    {cf cf' : Fin r → k} {v : Sp (DualNumber k) ⟶ t.G.left} (hv : IsCombAtG t y (fun i => u (x i).1 (x i).2) cf v)
    (hv' : IsCombAtG t y (fun i => u (x i).1 (x i).2) cf' v) : cf = cf' := by
  let U : Fin r → TanM y t.G := fun i => tanOf (hu.1 (x i).1 (x i).2).1
  have e : ∑ i, cf i • U i = ∑ i, cf' i • U i :=
    tan_ext (((comb_iff U cf v).1 hv).symm.trans ((comb_iff U cf' v).1 hv'))
  let ε := Equiv.ofBijective x hx
  have key (d : Fin r → k) : ∑ i, d i • U i = ∑ q, d (ε.symm q) • tanOf (hu.1 q.1 q.2).1 := by
    rw [← ε.sum_comp]
    simp only [Equiv.symm_apply_apply]
    rfl
  have := (GlobalTheory.TanSec.Frame.exists_unique_coords hu (∑ i, cf i • U i)).unique (key cf) (e.trans (key cf'))
  funext i
  simpa using congrFun this (ε i)

theorem comb_eig {f f' : c.F →+* k} {u u' : Vecs Dw t k} (hu : GlobalTheory.LocM.IsFrame t f y u) (hu' : GlobalTheory.LocM.IsFrame t f' y u')
    (hx : Function.Bijective x) {cf : Fin r → k} {q : Letter Dw}
    (hv : IsCombAtG t y (fun i => u (x i).1 (x i).2) cf (u' q.1 q.2)) (a : 𝓞 E) (i : Fin r) :
    cf i * f' (embK c q.1 a) = f (embK c (x i).1 a) * cf i := by
  have h₁ := (comb_op hu hv 1 a).2
  have h₂ := (comb_op hu hv (f' (embK c q.1 a)) 1).2
  have e : spMap (epsMul (1 : k)) ≫ u' q.1 q.2 ≫ (t.act.act a).left =
      spMap (epsMul (f' (embK c q.1 a))) ≫ u' q.1 q.2 ≫ (t.act.act 1).left := by
    rw [(hu'.1 q.1 q.2).2, (hu'.1 q.1 q.2).2, map_one, map_one, ← Category.assoc, ← Category.assoc]
    congr 1
    rw [ModelRelProbe.spMap_comp, ModelRelProbe.spMap_comp]
    congr 1
    ext z <;> simp [epsMul]
  rw [e] at h₁
  have := congrFun (comb_unique hu hx h₁ h₂) i
  simp only [map_one, one_mul, mul_one] at this
  rw [← this, mul_comm]

end Tan

section Model

open GlobalTheory.FieldPtGlue GlobalTheory.ShFam.Pad.Pull

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}
  {Z : LocM.Mdl Y i₀} {X : Scheme.{0}} {h : X ⟶ Z.X} {r : ℕ} {x : Fin r → Letter Dw} {b b' : Bool} {F F' : X.Modules}
  {s : ∀ a : Fin Z.m, Fin r → Γ(F, h ⁻¹ᵁ (Z.U a).1)} {s' : ∀ a : Fin Z.m, Fin r → Γ(F', h ⁻¹ᵁ (Z.U a).1)}

def eig (h : X ⟶ Z.X) (g : Γ(X, ⊤)) (c : 𝓞 E) (a : Fin Z.m) (q : Letter Dw) : Γ(X, h ⁻¹ᵁ (Z.U a).1) :=
  resG X le_top g * (h.app (Z.U a).1).hom (Z.alg a (embK Z.i.c q.1 c))

theorem valF_eig (g : Γ(X, ⊤)) (c : 𝓞 E) {a : Fin Z.m} (q : Letter Dw) {k : Type} [Field k] {w : Sp k ⟶ X}
    {φ : Γ(Z.X, (Z.U a).1) →+* k} (hφ : spMap φ ≫ Z.chart a = w ≫ h) {V : X.Opens} (l : V ≤ h ⁻¹ᵁ (Z.U a).1)
    (hV : ⊤ ≤ w ⁻¹ᵁ V) :
    valF w V (resG X l (eig h g c a q)) = valF w ⊤ g * (φ.comp (Z.alg a)) (embK Z.i.c q.1 c) := by
  have h' : ⊤ ≤ w ⁻¹ᵁ (h ⁻¹ᵁ (Z.U a).1) := fun z hz => l (hV hz)
  rw [valF_restrict l hV, eig, valF_mul h', valF_restrict le_top h', h.app_eq_appLE, valF_appLE h _ _ h', ← hφ]
  exact congrArg _ (valF_fromSpec (Z.U a).2 φ _)

theorem coef_eig [IsReduced X] (hopn : ToOpen Z h) (hx : Function.Bijective x) (hF : IsLat Z h x true b F s)
    (hF' : IsLat Z h x true b' F' s') (g : Γ(X, ⊤)) (c : 𝓞 E) (a a' : Fin Z.m) (i j : Fin r) :
    coef true (hF.frame a) (hF.frame a') i j * resG X inf_le_right (eig h g c a' (x j)) =
      resG X inf_le_left (eig h g c a (x i)) * coef true (hF'.frame a) (hF'.frame a') i j := by
  refine GlobalTheory.TestPts.ext_chart h hopn fun k _ w _ _ hw => ?_
  obtain ⟨φ, hφ⟩ := exists_fromSpec (Z.U a).2 (w ≫ h) fun q hq => (hw hq).1
  obtain ⟨φ', hφ'⟩ := exists_fromSpec (Z.U a').2 (w ≫ h) fun q hq => (hw hq).2
  have f := chart_frame Z (a := a) hφ
  have f' := chart_frame Z (a := a') hφ'
  rw [Category.assoc] at f f'
  have k₁ := hF.glue k w a a' φ φ' hφ hφ' j
  have k₂ := congrFun (comb_unique f hx k₁ (hF'.glue k w a a' φ φ' hφ hφ' j)) i
  have k₃ := comb_eig f f' hx k₁ c i
  rw [valF_mul hw, valF_mul hw, valF_eig g c _ hφ _ hw, valF_eig g c _ hφ' _ hw, ← k₂, mul_left_comm, k₃, mul_assoc]

theorem norm_le (hF : IsLat Z h x true b F s) (hF' : IsLat Z h x true b' F' s') (g : Γ(X, ⊤)) (c : 𝓞 E) (a : Fin Z.m)
    {V : X.Opens} {e : Fin r → Γ(F, V)} {e' : Fin r → Γ(F', V)} (he : GlobalTheory.VB.IsFrame e) (he' : GlobalTheory.VB.IsFrame e')
    (j l : Fin r) (y : Z.Pt) (w : Sp ↥(intO ↥y.C.S) ⟶ X) (hw : w ≫ h = y.z) (hy : ⊤ ≤ y.gen ⁻¹ᵁ (Z.U a).1)
    (hV : ⊤ ≤ w ⁻¹ᵁ V)
    (hop : ∀ v : Sp (DualNumber ↥y.C.S) ⟶ (Y Z.i).t.G.left,
      IsTanAtG (Y Z.i).t (y.gen ≫ Z.π) v → v ∈ lat (Y Z.i).t p (y.gen ≫ Z.π) b' →
        spMap (epsMul (valF (spMap (intO ↥y.C.S).subtype ≫ w) ⊤ g)) ≫ v ≫ ((Y Z.i).t.act.act c).left ∈
          lat (Y Z.i).t p (y.gen ≫ Z.π) b) :
    ‖valF (spMap (intO ↥y.C.S).subtype ≫ w) _ (∑ i, coef true he (hF.frame a) j i *
      (resG X inf_le_right (eig h g c a (x i)) * coef false he' (hF'.frame a) l i))‖ ≤ 1 := by
  obtain ⟨φ, hφ⟩ := exists_fromSpec (Z.U a).2 y.gen hy
  have hg : y.gen = (spMap (intO ↥y.C.S).subtype ≫ w) ≫ h := by rw [Category.assoc, hw]; rfl
  have hw' : ⊤ ≤ (spMap (intO ↥y.C.S).subtype ≫ w) ⁻¹ᵁ (V ⊓ h ⁻¹ᵁ (Z.U a).1) :=
    fun q hq => ⟨hV (Set.mem_univ (spMap (intO ↥y.C.S).subtype q)), by
      have := hy hq
      rw [hg] at this
      exact this⟩
  obtain ⟨ev, hev⟩ := exists_ev hw'
  have f := chart_frame Z (a := a) hφ
  obtain ⟨v, hv⟩ := GlobalTheory.ChainPts.LatUniq.exists_comb (Y Z.i).t (fun i => (f.1 (x i).1 (x i).2).1)
    fun i => ev (coef false he' (hF'.frame a) l i)
  obtain ⟨k₁, k₂⟩ := comb_op f hv (valF (spMap (intO ↥y.C.S).subtype ≫ w) ⊤ g) c
  have k₃ := (hF.norm y w hw a φ hφ V e he hV _ _ k₂).1 (hop v k₁ ((hF'.norm y w hw a φ hφ V e' he' hV _ v hv).2 fun m => by
    simp only [hev, ← map_mul, ← map_sum, mul_comm (coef false _ _ _ _), coef_mul]
    split_ifs <;> simp)) j
  rw [hev, map_sum]
  convert k₃ using 3 with i
  rw [map_mul, map_mul, ← hev (resG _ _ _), valF_eig g c _ (hφ.trans hg) _ hw', hev]
  ring

end Model

theorem mapSt : MapSt := by
  intro E _ _ _ H Dw Xo p W Y i₀ Z hp hW _ B hN h hopn r x hx b b' F F' s s' vF vF' hF hF' g c hop
  obtain ⟨a₀, ha₀⟩ := GlobalTheory.TestPts.exists_chart_of_maximal h hopn (η := genericPoint B.X) fun y hy =>
    (hy.antisymm ((genericPoint_spec B.X).specializes (Set.mem_univ y))).eq
  have ha : ((h ⁻¹ᵁ (Z.U a₀).1 : B.X.Opens) : Set B.X).Nonempty := ⟨_, ha₀⟩
  obtain ⟨u, hu⟩ := exists_hom vF' ha (hF.frame a₀) (fun i => eig h g c a₀ (x i) • s' a₀ i) fun z => by
    obtain ⟨z₀, hz, hz₀⟩ := GlobalTheory.TestPts.exists_special_V hp hW B z
    obtain ⟨V, e, e', hxV, he, he'⟩ := exists_frames vF vF' z₀
    obtain ⟨V', e₂, t, k₁, k₂⟩ := exists_local he (hF.frame a₀) hxV _
      (lin_eq_sum he he' (hF.frame a₀) (hF'.frame a₀) fun i => eig h g c a₀ (x i)) fun j l =>
      exists_ext hp hW hN h ha (U := V) _
        (fun y w k₁ k₂ k₃ => norm_le hF hF' g c a₀ he he' j l y w k₁ k₂ k₃ (hop y w k₁)) hxV hz₀
    exact ⟨V', e₂, t, hz.mem_open V'.isOpen k₁, k₂⟩
  exact ⟨u, fun a i => app_eq vF' ha (hF.frame a) (hF'.frame a) (hF.frame a₀) (hF'.frame a₀)
    (d := fun i => eig h g c a (x i)) hu (coef_eig hopn hx hF hF' g c a a₀) i⟩

end GlobalTheory.OmegaHT.Transpose
