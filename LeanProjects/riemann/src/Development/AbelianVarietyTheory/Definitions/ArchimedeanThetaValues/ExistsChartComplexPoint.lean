import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.CoeffFSumDerivEqFderiv
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RelationsAreFunctions
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ZeroFLeftExt
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SurjectiveOfComplexPointsLiftOfUniversallyClosed
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.IsReducedSchemeOfSmoothOfIsIntegrallyClosed

noncomputable section

namespace GlobalTheory

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

def frameProd {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g) {K : Type} [Fintype K]
    (j : K → L.ι) (z : K → (Fin g → ℂ)) (ε : K → ℤ) : ℂ :=
  ∏ k, u.fr (j k) (z k) ^ ε k

theorem frameProd_ne_zero {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g) {K : Type}
    [Fintype K] {j : K → L.ι} {z : K → (Fin g → ℂ)} (ε : K → ℤ) (h : ∀ k, ⊤ ≤ (u.ex (z k)).left ⁻¹ᵁ L.U (j k)) :
    frameProd u j z ε ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (u.fr_ne _ _ (h k))

theorem top_le_wchart_iff {X Y : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (j : K → L.ι)
    (x : Sp ℂ ⟶ Y) : ⊤ ≤ x ⁻¹ᵁ LB.wchart L φ j ↔ ∀ k, ⊤ ≤ (x ≫ φ k) ⁻¹ᵁ L.U (j k) := by
  simp only [top_le_preimage_iff_mem]
  exact Set.mem_iInter

theorem exists_chart_complexPoint {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) (x : Sp ℂ ⟶ X) :
    ∃ i, ⊤ ≤ x ⁻¹ᵁ L.U i :=
  (exists_chart hL (x (default : PrimeSpectrum ℂ))).imp fun _ h => (top_le_preimage_iff_mem x _).2 h

section Dict

variable {O : Type} [CommRing O] [StarRing O] [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ]

theorem jFK_comp_jK_complex : Out.jFK (R := ℂ) ℂ ≫ Out.jK ℂ = 𝟙 (Sp ℂ) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
  exact Spec.map_id _

theorem toUnit_TF_comp_left {B : Over (Sp ℂ)} (p : 𝟙_ (Over (Sp ℂ)) ⟶ B) :
    (show Sp ℂ ⟶ _ from (toUnit (Out.TF (R := ℂ) ℂ) ≫ p).left) = p.left := by
  change (Out.jFK (R := ℂ) ℂ ≫ Out.jK ℂ) ≫ p.left = _
  rw [jFK_comp_jK_complex]
  exact Category.id_comp _

structure GtDict [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (D₀ : Out.DegPre ℂ)
    [Module O D₀.X] (oa : D₀.OAct O) where

  A : AnArc O

  eX : A.X ≃ₗ[O] D₀.X

  u : HolUnif D₀.P.A D₀.P.L A.gB

  lam_eq : u.Λ = A.abelian₂

  isAH : u.IsAH A.Hm fun l => A.chi ⟨l, lam_eq.le l.2⟩

  isRig : u.IsRig D₀.rig

  ex_act : ∀ (a : O) z, u.ex (A.F a z) = u.ex z ≫ oa.onB.act a

  ex_ct : ∀ x, u.ex (A.ct x) = D₀.c (eX x)

  psi_val : ∀ x (j : PUnit → D₀.P.L.ι), ⊤ ≤ (u.ex (A.ct x)).left ⁻¹ᵁ D₀.P.L.U (j PUnit.unit) →
    valAt' (Out.jFK (R := ℂ) ℂ) _ ((D₀.psi (eX x)).s j).val = A.psi x * (u.fr (j PUnit.unit) (A.ct x))⁻¹

  ex₀ : A.V → Out.GtPtF D₀ ℂ

  ex₀_b : ∀ v, (ex₀ v).b = toUnit _ ≫ u.ex v.2

  chi_val : ∀ v x j, ⊤ ≤ LB.wchart D₀.P.L (Out.DegPre.gtφ D₀ ℂ (ex₀ v).b (eX x)) j →
    chiVal (ex₀ v) (eX x) j = eTwoPi (v.1 x) * frameProd u j ![A.ct x + v.2, A.ct x, v.2, 0] Out.DegPre.gtε

  add : ∀ v v', (ex₀ v).IsAdd (ex₀ v') (ex₀ (v + v'))

  onto : Function.Surjective ex₀

  lin : ∀ (a : O) v, GtAct oa a (ex₀ v) (ex₀ (A.actV a v))

  ker : ∀ v, (ex₀ v).IsZero ↔ ∃ la : A.La, la.y = 0 ∧ v = A.P0 la

  iota : ∀ la : A.La, Out.GtPtF.IsIota (eX la.y) (ex₀ (A.P0 la))

namespace GtDict

variable {D₀ : Out.DegPre ℂ} [Module O D₀.X] {oa : D₀.OAct O} (d : GtDict D₀ oa)

def IsFamFn (j : ℕ) (α : d.A.X) (s : D₀.SecB j (d.eX α)) (θ : (Fin d.A.gB → ℂ) → ℂ) : Prop :=
  ∀ z (i : Fin 4 → D₀.P.L.ι), ⊤ ≤ (d.u.ex z).left ⁻¹ᵁ LB.wchart D₀.P.L (D₀.famφB (d.eX α)) i →
    valAt' (d.u.ex z).left _ (s.f i) = θ z * frameProd d.u i ![z, z + d.A.ct α, d.A.ct α, 0] (Out.DegPre.famε j)

structure SecFn where

  fn : ∀ (j : ℕ) [NeZero j] (α : d.A.X), D₀.SecB j (d.eX α) ≃ d.A.Theta j α

  fn_val : ∀ (j : ℕ) [NeZero j] α s, d.IsFamFn j α s (fn j α s)

theorem ex₀_b_left (v : d.A.V) : (show Sp ℂ ⟶ _ from (d.ex₀ v).b.left) = (d.u.ex v.2).left := by
  rw [d.ex₀_b]; exact toUnit_TF_comp_left _

theorem ex_zero : d.u.ex 0 = η[D₀.P.A] := by
  rw [(d.u.ker 0).2 (zero_mem _), Hom.one_def, toUnit_unit, Category.id_comp]

theorem gtφ_eq (v : d.A.V) (x : d.A.X) (k : Fin 4) :
    (show Sp ℂ ⟶ _ from Out.DegPre.gtφ D₀ ℂ (d.ex₀ v).b (d.eX x) k) =
      (d.u.ex (![d.A.ct x + v.2, d.A.ct x, v.2, 0] k)).left := by
  fin_cases k
  · refine Eq.trans ?_ (toUnit_TF_comp_left _)
    change (toUnit _ ≫ D₀.c (d.eX x) * (d.ex₀ v).b).left = (toUnit _ ≫ d.u.ex (d.A.ct x + v.2)).left
    rw [d.ex₀_b, d.u.ex_add, MonObj.comp_mul, d.ex_ct]
  · exact (toUnit_TF_comp_left _).trans (congrArg (·.left) (d.ex_ct x).symm)
  · exact d.ex₀_b_left v
  · exact (toUnit_TF_comp_left _).trans (congrArg (·.left) d.ex_zero.symm)

theorem ex_comp_famφB (z : Fin d.A.gB → ℂ) (α : d.A.X) (k : Fin 4) :
    (d.u.ex z).left ≫ D₀.famφB (d.eX α) k = (d.u.ex (![z, z + d.A.ct α, d.A.ct α, 0] k)).left := by
  have h : ∀ p : 𝟙_ (Over (Sp ℂ)) ⟶ D₀.P.A, d.u.ex z ≫ toUnit D₀.P.A ≫ p = p := fun p => by
    rw [← Category.assoc, comp_toUnit, toUnit_unit, Category.id_comp]
  fin_cases k
  · exact Category.comp_id _
  · change (d.u.ex z ≫ (𝟙 D₀.P.A * toUnit _ ≫ D₀.c (d.eX α))).left = (d.u.ex (z + d.A.ct α)).left
    rw [MonObj.comp_mul, h, Category.comp_id, d.u.ex_add, d.ex_ct]
  · change (d.u.ex z ≫ toUnit _ ≫ D₀.c (d.eX α)).left = (d.u.ex (d.A.ct α)).left
    rw [h, d.ex_ct]
  · change (d.u.ex z ≫ toUnit _ ≫ η[D₀.P.A]).left = (d.u.ex 0).left
    rw [h, d.ex_zero]

theorem top_le_gtChart_iff (v : d.A.V) (x : d.A.X) (j : Fin 4 → D₀.P.L.ι) :
    ⊤ ≤ LB.wchart D₀.P.L (Out.DegPre.gtφ D₀ ℂ (d.ex₀ v).b (d.eX x)) j ↔
      ∀ k, ⊤ ≤ (d.u.ex (![d.A.ct x + v.2, d.A.ct x, v.2, 0] k)).left ⁻¹ᵁ D₀.P.L.U (j k) := by
  refine (top_le_wchart_iff D₀.P.L (Y := Sp ℂ) _ j (𝟙 _)).trans (forall_congr' fun k => ?_)
  rw [Category.id_comp, ← d.gtφ_eq]

theorem top_le_famChart_iff (z : Fin d.A.gB → ℂ) (α : d.A.X) (i : Fin 4 → D₀.P.L.ι) :
    ⊤ ≤ (d.u.ex z).left ⁻¹ᵁ LB.wchart D₀.P.L (D₀.famφB (d.eX α)) i ↔
      ∀ k, ⊤ ≤ (d.u.ex (![z, z + d.A.ct α, d.A.ct α, 0] k)).left ⁻¹ᵁ D₀.P.L.U (i k) := by
  refine (top_le_wchart_iff D₀.P.L _ i (d.u.ex z).left).trans (forall_congr' fun k => ?_)
  rw [← d.ex_comp_famφB]

theorem hol_b : IsHolTo Set.univ (fun v => (show Sp ℂ ⟶ _ from (d.ex₀ v).b.left)) := by
  intro U f
  simp only [d.ex₀_b_left, Set.mem_univ, true_and]
  exact ⟨(d.u.hol U f).1.preimage continuous_snd,
    (d.u.hol U f).2.comp differentiable_snd.differentiableOn fun _ h => h⟩

theorem hol_chi (x : D₀.X) (j : Fin 4 → D₀.P.L.ι) : DifferentiableOn ℂ (fun v => chiVal (d.ex₀ v) x j)
    {v | ⊤ ≤ LB.wchart D₀.P.L (Out.DegPre.gtφ D₀ ℂ (d.ex₀ v).b x) j} := by
  obtain ⟨x, rfl⟩ := d.eX.surjective x
  refine DifferentiableOn.congr ?_ fun v hv => d.chi_val v x j hv
  have h1 : Differentiable ℂ fun v : d.A.V => v.1 x := (d.A.evalCLM x).differentiable.comp differentiable_fst
  refine DifferentiableOn.mul (Differentiable.differentiableOn (by unfold eTwoPi; fun_prop)) ?_
  suffices hk : ∀ k, DifferentiableOn ℂ
      (fun v : d.A.V => d.u.fr (j k) (![d.A.ct x + v.2, d.A.ct x, v.2, 0] k) ^ Out.DegPre.gtε k)
      {v | ⊤ ≤ LB.wchart D₀.P.L (Out.DegPre.gtφ D₀ ℂ (d.ex₀ v).b (d.eX x)) j} by
    simp only [frameProd, Fin.prod_univ_four]
    exact (((hk 0).mul (hk 1)).mul (hk 2)).mul (hk 3)
  refine fun k => DifferentiableOn.zpow ?_
    (Or.inl fun v hv => d.u.fr_ne _ _ ((d.top_le_gtChart_iff v x j).1 hv k))
  refine (d.u.fr_hol (j k)).comp (f := fun v : d.A.V => ![d.A.ct x + v.2, d.A.ct x, v.2, 0] k)
    (Differentiable.differentiableOn ?_) fun v hv => (d.top_le_gtChart_iff v x j).1 hv k
  fin_cases k <;> simp

theorem isTorusPt_ex₀ {v : d.A.V} (hv : v.2 = 0) : IsTorusPt (d.ex₀ v) fun x => eTwoPi (v.1 (d.eX.symm x)) := by
  refine ⟨by rw [d.ex₀_b, hv, d.ex_zero], fun x j hc hj => ?_⟩
  obtain ⟨x, rfl⟩ := d.eX.surjective x
  have h01 : j 0 = j 1 := hc 0 1 ((d.gtφ_eq v x 0).trans (Eq.trans (by simp [hv]) (d.gtφ_eq v x 1).symm))
  have h23 : j 2 = j 3 := hc 2 3 ((d.gtφ_eq v x 2).trans (Eq.trans (by simp [hv]) (d.gtφ_eq v x 3).symm))
  have n1 := d.u.fr_ne _ _ ((d.top_le_gtChart_iff v x j).1 hj 1)
  have n3 := d.u.fr_ne _ _ ((d.top_le_gtChart_iff v x j).1 hj 3)
  rw [d.chi_val v x j hj, frameProd, Fin.prod_univ_four, h01, h23]
  simp [hv, Out.DegPre.gtε] at n1 n3 ⊢
  field_simp

theorem shift (w : ℂ) (la : d.A.La) :
    IsTorusPt (d.ex₀ (w • d.A.N la)) fun x => eTwoPi (w * d.A.be la.y (d.eX.symm x)) :=
  d.isTorusPt_ex₀ (v := w • d.A.N la) (by simp)

theorem isZero_ex₀_zero : (d.ex₀ 0).IsZero := (d.ker 0).2 ⟨0, rfl, (map_zero _).symm⟩

theorem isNsmul_ex₀ (k : ℕ) (v : d.A.V) : Out.GtPtF.IsNsmul k (d.ex₀ v) (d.ex₀ (k • v)) :=
  ⟨fun i => d.ex₀ ((i : ℕ) • v), by simpa using d.isZero_ex₀_zero,
    fun i => by simpa [succ_nsmul] using d.add ((i : ℕ) • v) v, rfl⟩

theorem ex₀_eq_iff (v v' : d.A.V) : d.ex₀ v = d.ex₀ v' ↔ ∃ la : d.A.La, la.y = 0 ∧ v - v' = d.A.P0 la := by
  let := TorusExt.gtGroup D₀ ℂ
  have h := (TorusExt.isAdd_iff_eq _ _ _).1 (d.add (v - v') v')
  rw [sub_add_cancel] at h
  rw [← d.ker, TorusExt.isZero_iff_eq, h, add_eq_right]

def qk (k : ℕ) [NeZero k] (la : d.A.La) : Out.QkPt D₀ ℂ k where
  y := d.eX la.y
  g := d.ex₀ ((k : ℂ)⁻¹ • d.A.P0 la)
  eq := ⟨d.ex₀ (d.A.P0 la), by
    have := d.isNsmul_ex₀ k ((k : ℂ)⁻¹ • d.A.P0 la)
    rwa [← Nat.cast_smul_eq_nsmul ℂ, smul_inv_smul₀ (Nat.cast_ne_zero.2 (NeZero.ne k))] at this, d.iota la⟩

@[simp] theorem qk_y (k : ℕ) [NeZero k] (la : d.A.La) : (d.qk k la).y = d.eX la.y := rfl

@[simp] theorem qk_g (k : ℕ) [NeZero k] (la : d.A.La) : (d.qk k la).g = d.ex₀ ((k : ℂ)⁻¹ • d.A.P0 la) := rfl

theorem qk_surjective (k : ℕ) [NeZero k] : Function.Surjective (d.qk k) := by
  let := TorusExt.gtGroup D₀ ℂ
  intro q
  obtain ⟨v, hv⟩ := d.onto q.g
  obtain ⟨y, hy⟩ := d.eX.surjective q.y
  obtain ⟨h, h₁, h₂⟩ := q.eq
  have e1 : d.ex₀ (k • v) = h := by
    rw [(TorusExt.isNsmul_iff_eq _ _ _).1 h₁, (TorusExt.isNsmul_iff_eq _ _ _).1 (d.isNsmul_ex₀ k v), hv]
  have e2 : h = d.ex₀ (d.A.P0 (AnArc.La.mk y 0 0)) :=
    TorusExt.isIota_unique h₂ (hy ▸ d.iota (AnArc.La.mk y 0 0))
  obtain ⟨la, hla, e⟩ := (d.ex₀_eq_iff _ _).1 (e1.trans e2)
  refine ⟨la + AnArc.La.mk y 0 0, TorusExt.qk_ext (by simp [hla, hy]) ?_⟩
  rw [qk_g, map_add, ← e, sub_add_cancel, ← Nat.cast_smul_eq_nsmul ℂ,
    inv_smul_smul₀ (Nat.cast_ne_zero.2 (NeZero.ne k)), hv]

theorem qk_equiv_add (k : ℕ) [NeZero k] (la la' : d.A.La) :
    Out.QkPt.Equiv D₀ ℂ (d.qk k la) (d.qk k (la + k • la')) := by
  refine ⟨d.eX la'.y, by simp, _, d.iota la', ?_⟩
  rw [qk_g, qk_g, map_add, map_nsmul, smul_add, ← Nat.cast_smul_eq_nsmul ℂ,
    inv_smul_smul₀ (Nat.cast_ne_zero.2 (NeZero.ne k))]
  exact d.add _ _

theorem qk_equiv_iff (k : ℕ) [NeZero k] (la la' : d.A.La) :
    Out.QkPt.Equiv D₀ ℂ (d.qk k la) (d.qk k la') ↔ ∃ m, la' = la + k • m := by
  refine ⟨fun ⟨z, hz, h, h₁, h₂⟩ => ?_, fun ⟨m, hm⟩ => hm ▸ d.qk_equiv_add k la m⟩
  obtain ⟨y, rfl⟩ := d.eX.surjective z
  obtain rfl : h = d.ex₀ (d.A.P0 (AnArc.La.mk y 0 0)) := TorusExt.isIota_unique h₁ (d.iota (AnArc.La.mk y 0 0))
  obtain ⟨n, hn, e⟩ := (d.ex₀_eq_iff _ _).1 (TorusExt.isAdd_unique h₂ (d.add _ _))
  have hk : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne k)
  have hy : la'.y = la.y + k • y := d.eX.injective (by simpa using hz)
  have e' : d.A.P0 (la' - (la + k • (AnArc.La.mk y 0 0 + n))) = 0 := by
    rw [map_sub, map_add, map_nsmul, map_add, ← e, ← Nat.cast_smul_eq_nsmul ℂ]
    simp only [smul_add, smul_sub, smul_inv_smul₀ hk]
    abel
  refine ⟨AnArc.La.mk y 0 0 + n, sub_eq_zero.1 ?_⟩
  have hy' : (la' - (la + k • (AnArc.La.mk y 0 0 + n))).y = 0 := by simp [hy, hn]
  generalize la' - (la + k • (AnArc.La.mk y 0 0 + n)) = m at e' hy'
  have hl : m.l = 0 := Subtype.ext (by simpa [hy'] using congrArg Prod.snd e')
  refine AnArc.La.ext hy' (AddMonoidHom.ext fun x => ?_) hl
  simpa [hy', hl] using congrArg (fun v : d.A.V => v.1 x) e'

theorem fr_eq_ah_mul (l : d.A.abelian₂) (i : D₀.P.L.ι) (z : Fin d.A.gB → ℂ) (h : ⊤ ≤ (d.u.ex z).left ⁻¹ᵁ D₀.P.L.U i) :
    d.u.fr i z = d.A.ah l z * d.u.fr i (z + l) :=
  d.isAH.2.2.2 ⟨l, d.lam_eq.ge l.2⟩ i z h

theorem ex_add_lam (z : Fin d.A.gB → ℂ) (l : d.A.abelian₂) : d.u.ex (z + l) = d.u.ex z := by
  rw [d.u.ex_add, (d.u.ker l).2 (d.lam_eq.ge l.2), _root_.mul_one]

def fn₁ (th : D₀.P.L.Sec) (z : Fin d.A.gB → ℂ) : ℂ :=
  valAt' (d.u.ex z).left _ (th.f (exists_chart_complexPoint D₀.P.isLB (d.u.ex z).left).choose) /
    d.u.fr (exists_chart_complexPoint D₀.P.isLB (d.u.ex z).left).choose z

theorem isFn_fn₁ (th : D₀.P.L.Sec) : d.u.IsFn th (d.fn₁ th) := by
  intro i z hi
  have hj := (exists_chart_complexPoint D₀.P.isLB (d.u.ex z).left).choose_spec
  rw [fn₁]
  generalize (exists_chart_complexPoint D₀.P.isLB (d.u.ex z).left).choose = j at hj
  have hij := (top_le_preimage_inf (d.u.ex z).left _ _).2 ⟨hi, hj⟩
  have h := congrArg (valAt' (d.u.ex z).left _) (th.compat i j)
  rw [valAt'_mul, valAt'_map _ _ _ hij, valAt'_map _ _ _ hij] at h
  have := d.u.fr_ne j z hj
  rw [h, d.u.fr_compat i j z hij]
  field_simp

theorem eq_fn₁ {th : D₀.P.L.Sec} {θ : (Fin d.A.gB → ℂ) → ℂ} (h : d.u.IsFn th θ) : θ = d.fn₁ th := by
  funext z
  obtain ⟨i, hi⟩ := exists_chart_complexPoint D₀.P.isLB (d.u.ex z).left
  exact mul_right_cancel₀ (d.u.fr_ne i z hi) ((h i z hi).symm.trans (d.isFn_fn₁ th i z hi))

theorem fn₁_mem (th : D₀.P.L.Sec) : d.fn₁ th ∈ d.A.Theta 1 0 := by
  refine ⟨fun z => ?_, fun l z => ?_⟩
  · obtain ⟨i, hi⟩ := exists_chart_complexPoint D₀.P.isLB (d.u.ex z).left
    obtain ⟨ho, hd⟩ := d.u.hol _ (th.f i)
    refine DifferentiableOn.differentiableAt ((hd.mul ((d.u.fr_hol i).inv (d.u.fr_ne i))).congr fun z' hz' => ?_)
      (ho.mem_nhds hi)
    exact eq_div_of_mul_eq (d.u.fr_ne i z' hz') (d.isFn_fn₁ th i z' hz').symm
  · obtain ⟨i, hi⟩ := exists_chart_complexPoint D₀.P.isLB (d.u.ex z).left
    have hi' : ⊤ ≤ (d.u.ex (z + l)).left ⁻¹ᵁ D₀.P.L.U i := by rwa [d.ex_add_lam]
    have h1 := d.isFn_fn₁ th i _ hi'
    rw [d.ex_add_lam, d.isFn_fn₁ th i z hi, d.fr_eq_ah_mul l i z hi] at h1
    refine mul_right_cancel₀ (d.u.fr_ne i _ hi') ?_
    rw [← h1]
    simp only [map_zero, AnArc.H_zero_left, mul_zero, Complex.exp_zero]
    ring

theorem fn₁_ne_zero {th : D₀.P.L.Sec} (h : ∃ j, th.f j ≠ 0) : d.fn₁ th ≠ 0 := by
  obtain ⟨j, hj⟩ := h
  intro h0
  have := D₀.P.isAb.smooth
  have := isReduced_of_smooth_complex _ D₀.P.A.hom inferInstance
  refine hj (ComplexPoints.eq_of_valAt'_eq D₀.P.A.hom _ _ _ fun x hp hx => ?_)
  obtain ⟨z, hz⟩ := d.u.ex_onto (Over.homMk x hp)
  obtain rfl : (d.u.ex z).left = x := congrArg (·.left) hz
  rw [d.isFn_fn₁ th j z hx, h0, valAt'_zero, Pi.zero_apply, zero_mul]

theorem IsFamFn.unique {j : ℕ} {α : d.A.X} {s : D₀.SecB j (d.eX α)} {θ θ' : (Fin d.A.gB → ℂ) → ℂ}
    (h : d.IsFamFn j α s θ) (h' : d.IsFamFn j α s θ') : θ = θ' := by
  funext z
  choose i hi using fun k : Fin 4 =>
    exists_chart_complexPoint D₀.P.isLB (d.u.ex (![z, z + d.A.ct α, d.A.ct α, 0] k)).left
  have hi' := (d.top_le_famChart_iff z α i).2 hi
  exact mul_right_cancel₀ (frameProd_ne_zero d.u _ hi) ((h z i hi').symm.trans (h' z i hi'))

variable {d}

theorem SecFn.fn_add (σ : d.SecFn) {j : ℕ} [NeZero j] {α : d.A.X} {s s' s'' : D₀.SecB j (d.eX α)}
    (h : ∀ i, s''.f i = s.f i + s'.f i) : σ.fn j α s'' = σ.fn j α s + σ.fn j α s' :=
  Subtype.ext (IsFamFn.unique d (σ.fn_val j α s'') fun z i hi => by
    refine (congrArg _ (h i)).trans ((valAt'_add _ _ _ _).trans ?_)
    rw [σ.fn_val j α s z i hi, σ.fn_val j α s' z i hi, ← add_mul]; rfl)

theorem SecFn.fn_smul (σ : d.SecFn) {j : ℕ} [NeZero j] {α : d.A.X} {s s' : D₀.SecB j (d.eX α)} (a : ℂ)
    (h : ∀ i, s'.f i = constFn D₀.P.A.hom _ a * s.f i) : σ.fn j α s' = a • σ.fn j α s :=
  Subtype.ext (IsFamFn.unique d (σ.fn_val j α s') fun z i hi => by
    refine (congrArg _ (h i)).trans ((valAt'_mul _ _ _ _).trans ?_)
    rw [σ.fn_val j α s z i hi]
    exact (congrArg (· * _) (valAt'_constFn _ _ (Over.w (d.u.ex z)) _ _ hi)).trans (mul_assoc _ _ _).symm)

end GtDict

end Dict

namespace ToricDict

open ToricData Out.Inh Out.InhTate

theorem valAt'_gv_unitOn (t : ℂˣ) {W : (Sp ℂ).Opens} (h : ⊤ ≤ W) : valAt' (𝟙 (Sp ℂ)) W (gv (unitOn t) W).val = t :=
  (valAt'_res (𝟙 (Sp ℂ)) le_top _ h).trans (valAt'_id_top _)

def expChar {X : Type} [AddCommGroup X] (l : X →+ ℂ) : Multiplicative X →* ℂˣ :=
  MonoidHom.mk' (fun x => Units.mk0 (eTwoPi (l x.toAdd)) (AnArc.e_ne_zero _)) fun a b =>
    Units.ext (by simp [AnArc.e_add])

@[simp] theorem expChar_apply {X : Type} [AddCommGroup X] (l : X →+ ℂ) (x : X) :
    (expChar l (Multiplicative.ofAdd x) : ℂ) = eTwoPi (l x) := rfl

theorem expChar_surjective {X : Type} [AddCommGroup X] [Module.Free ℤ X] :
    Function.Surjective (expChar (X := X)) := by
  intro t
  let f : ℂ →ₗ[ℤ] Additive ℂˣ := (AddMonoidHom.toMultiplicativeLeft.symm (expChar (AddMonoidHom.id ℂ))).toIntLinearMap
  have hf : Function.Surjective f := fun a => ⟨Complex.log (Additive.toMul a : ℂˣ) / (2 * Real.pi * Complex.I), by
    refine Units.ext ?_
    change eTwoPi (Complex.log (Additive.toMul a : ℂˣ) / (2 * Real.pi * Complex.I)) = (Additive.toMul a : ℂˣ)
    rw [eTwoPi, mul_div_cancel₀ _ Complex.two_pi_I_ne_zero, Complex.exp_log (Units.ne_zero _)]⟩
  obtain ⟨l, hl⟩ := Module.projective_lifting_property f (AddMonoidHom.toMultiplicativeLeft.symm t).toIntLinearMap hf
  exact ⟨l.toAddMonoidHom, MonoidHom.ext fun x => LinearMap.congr_fun hl x.toAdd⟩

theorem expChar_eq_one_iff {X : Type} [AddCommGroup X] (l : X →+ ℂ) :
    expChar l = 1 ↔ ∃ n : X →+ ℤ, ∀ x, l x = n x := by
  constructor
  · intro h
    have : ∀ x, ∃ n : ℤ, l x = n := fun x => by
      have h1 : eTwoPi (l x) = 1 := congrArg Units.val (DFunLike.congr_fun h (Multiplicative.ofAdd x))
      obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.1 h1
      exact ⟨n, mul_left_cancel₀ Complex.two_pi_I_ne_zero (hn.trans (mul_comm _ _))⟩
    choose n hn using this
    refine ⟨AddMonoidHom.mk' n fun a b => ?_, hn⟩
    exact_mod_cast (hn (a + b)).symm.trans ((map_add l a b).trans (congrArg₂ (· + ·) (hn a) (hn b)))
  · rintro ⟨n, hn⟩
    exact MonoidHom.ext fun x => Units.ext (by
      change eTwoPi (l x.toAdd) = 1
      rw [hn, AnArc.e_intCast])

variable {O : Type} [CommRing O] [StarRing O] (A : AnArc O) [IsEmpty (Fin A.gB)]

def zeroUnif : HolUnif (zeroPolAV (Sp ℂ)).A (zeroPolAV (Sp ℂ)).L A.gB where
  ex _ := η[(zeroPolAV (Sp ℂ)).A]
  ex_add _ _ := toUnit_unique _ _
  ex_onto _ := ⟨0, toUnit_unique _ _⟩
  Λ := A.abelian₂
  ker z := ⟨fun _ => Subsingleton.elim 0 z ▸ zero_mem _, fun _ => toUnit_unique _ _⟩
  discrete := A.discrete
  full := A.full
  hol _ _ := ⟨isOpen_discrete _, differentiableOn_const _⟩
  fr _ _ := 1
  fr_hol _ := differentiableOn_const _
  fr_ne _ _ _ := one_ne_zero
  fr_compat _ _ _ h := ((_root_.mul_one _).trans (valAt'_one _ h)).symm

theorem frameProd_zeroUnif {K : Type} [Fintype K] (j z) (ε : K → ℤ) : frameProd (zeroUnif A) j z ε = 1 :=
  Finset.prod_eq_one fun _ _ => one_zpow _

theorem lam_eq_zero (l : A.abelian₂) : l = 0 := Subtype.ext (Subsingleton.elim _ _)

variable [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ]
  (q : A.X → (FractionRing ℂ)ˣ) (hq : ∀ x, algebraMap (FractionRing ℂ) ℂ (q x) = A.psi x)
  (h : ∀ (a : O) y z, polar q (a • y) z = polar q y (star a • z))

def dict : GtDict (toricPre ℂ A.X q) (toricOAct q O h) where
  A := A
  eX := LinearEquiv.refl O A.X
  u := zeroUnif A
  lam_eq := rfl
  isAH := ⟨A.Hm_herm, A.Hm_pos, fun _ => A.chi_norm _, fun l i z _ => by
    change (1 : ℂ) = A.ah l z * 1
    rw [lam_eq_zero A l]
    simp [AnArc.ah]⟩
  isRig j hj := (valAt'_gv_unitOn 1 hj).symm.trans (by rw [unitOn_one]; rfl)
  ex_act _ _ := toUnit_unique _ _
  ex_ct _ := toUnit_unique _ _
  psi_val x j _ := by
    change valAt' (Out.jFK (R := ℂ) ℂ) _ (gv (unitOn (q x)) _).val = A.psi x * (1 : ℂ)⁻¹
    rw [inv_one, _root_.mul_one, ← hq]
    refine (valAt'_res _ le_top _ (le_top.trans_eq ?_)).trans ?_
    · exact (congrArg (Out.jFK (R := ℂ) ℂ ⁻¹ᵁ ·) (wchart_triv _ _)).symm
    · have := valAt'_comp (𝟙 (Sp ℂ)) (Out.jFK (R := ℂ) ℂ) ⊤ (unitOn (q x)).val
      rw [Category.id_comp] at this
      rw [← this]
      exact (congrArg (fun t : Γ(Sp ℂ, ⊤)ˣ => valAt' (𝟙 (Sp ℂ)) ⊤ t.val) (pullTop_unitOn _ (q x))).trans
        (valAt'_id_top _)
  ex₀ v := pt q ℂ (expChar v.1)
  ex₀_b _ := rfl
  chi_val v x j hj := (valAt'_gv_unitOn _ hj).trans
    ((_root_.mul_one _).symm.trans (congrArg _ (frameProd_zeroUnif A _ _ _).symm))
  add v v' := (isAdd_pt q ℂ _ _ _).2 (MonoidHom.ext fun x => Units.ext (AnArc.e_add _ _))
  onto g := by
    obtain ⟨t, rfl⟩ := (pt_bijective q ℂ).2 g
    obtain ⟨l, rfl⟩ := expChar_surjective t
    exact ⟨(l, 0), rfl⟩
  lin a v := (gtAct_pt q ℂ O h a _ _).2 fun _ => rfl
  ker v := (isZero_pt q ℂ _).trans ((expChar_eq_one_iff _).trans
    ⟨fun ⟨n, hn⟩ => ⟨AnArc.La.mk 0 n 0, rfl, Prod.ext (AddMonoidHom.ext fun x => by simp [hn]) (Subsingleton.elim _ _)⟩,
      fun ⟨la, h0, e⟩ => ⟨la.n, fun x => by simp [e, h0, lam_eq_zero A la.l]⟩⟩)
  iota la := (isIota_pt q ℂ la.y _).2 fun x => by
    have h1 := (A.psi la.y).ne_zero
    have h2 := (A.psi x).ne_zero
    simp [polar, hq, A.psi_add, lam_eq_zero A la.l, AnArc.e_add]
    field_simp

omit [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] in

theorem mem_Theta (j : ℕ) (α : A.X) (θ : (Fin A.gB → ℂ) → ℂ) : θ ∈ A.Theta j α :=
  ⟨by
    rw [show θ = fun _ => θ 0 from funext fun z => congrArg θ (Subsingleton.elim _ _)]
    exact differentiable_const _, fun l z => by simp [lam_eq_zero A l, AnArc.ah]⟩

def secFn : (dict A q hq h).SecFn where
  fn j _ α := Equiv.ofBijective
    (fun s => ⟨fun _ => valAt' (𝟙 (Sp ℂ)) _ (s.f fun _ => PUnit.unit), mem_Theta A j α _⟩) (by
      constructor
      · rintro ⟨f, _⟩ ⟨f', _⟩ e
        have e' := congrFun (congrArg Subtype.val e) 0
        congr 1
        funext i
        refine ComplexPoints.eq_of_valAt'_eq (𝟙 (Sp ℂ)) _ _ _ fun x hx _ => ?_
        obtain rfl : x = 𝟙 _ := (Category.comp_id _).symm.trans hx
        exact e'
      · intro θ
        refine ⟨⟨fun i => constFn (𝟙 (Sp ℂ)) _ (θ.1 0), fun i i' => ?_⟩, Subtype.ext (funext fun z => ?_)⟩
        · obtain rfl : i = i' := funext fun _ => rfl
          erw [linComb_triv_g]
          exact (_root_.one_mul _).symm
        · exact (valAt'_constFn _ _ (Category.comp_id _) _ _ (wchart_triv _ _).ge).trans
            (congrArg θ.1 (Subsingleton.elim (α := Fin A.gB → ℂ) _ _)))
  fn_val j _ α s z i _ :=
    (_root_.mul_one _).symm.trans (congrArg _ (frameProd_zeroUnif A _ _ _).symm)

def psiFrac (x : A.X) : (FractionRing ℂ)ˣ := Units.map (algebraMap ℂ (FractionRing ℂ)).toMonoidHom (A.psi x)

omit [IsEmpty (Fin A.gB)] in

theorem algebraMap_psiFrac (x : A.X) : algebraMap (FractionRing ℂ) ℂ (psiFrac A x) = A.psi x :=
  (IsScalarTower.algebraMap_apply ℂ (FractionRing ℂ) ℂ _).symm

omit [IsEmpty (Fin A.gB)] [IsScalarTower ℂ (FractionRing ℂ) ℂ] in
include hq in

theorem polar_bal (a : O) (y z : A.X) : polar q (a • y) z = polar q y (star a • z) := by
  have key : ∀ y z, algebraMap (FractionRing ℂ) ℂ (polar q y z) = eTwoPi (A.T y z) := fun y z => by
    have h1 := (A.psi y).ne_zero
    have h2 := (A.psi z).ne_zero
    simp [polar, hq, A.psi_add]
    field_simp
  exact Units.ext ((algebraMap (FractionRing ℂ) ℂ).injective (by rw [key, key, A.T_adj]))

instance (τ₀ : ℂ) : IsEmpty (Fin (AnArc.tate τ₀).gB) := inferInstanceAs (IsEmpty (Fin 0))

def tate (τ₀ : ℂ) : GtDict (toricPre ℂ (AnArc.tate τ₀).X (psiFrac (AnArc.tate τ₀)))
    (toricOAct _ ℤ (polar_bal (AnArc.tate τ₀) _ (algebraMap_psiFrac _))) :=
  dict _ _ (algebraMap_psiFrac _) _

example (τ₀ : ℂ) : Nonempty (tate τ₀).SecFn := ⟨secFn _ _ _ _⟩

example (τ₀ : ℂ) : ¬ ((tate τ₀).ex₀ ((2 : ℂ)⁻¹ • Int.castAddHom ℂ, 0)).IsZero := by
  intro h
  obtain ⟨n, hn⟩ := (expChar_eq_one_iff _).1 ((isZero_pt _ ℂ _).1 h)
  have h1 : (2 : ℂ)⁻¹ * ((1 : ℤ) : ℂ) = n (1 : ℤ) := hn (1 : ℤ)
  have h2 : ((2 * n (1 : ℤ) : ℤ) : ℂ) = (1 : ℤ) := by push_cast at h1 ⊢; rw [← h1]; norm_num
  have h3 := Int.cast_injective h2
  omega

end ToricDict

end GlobalTheory
