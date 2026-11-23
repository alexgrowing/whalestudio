import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ConcretePkgSpec
import Formalism.LocalToGlobal.Divisibility.ProjLemmas
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelTypeEigenfunctionOfLiftableElement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Arith

namespace GlobalTheory.LevelForms

section Abstract

variable {LL Ks : Type} [Field LL] [NumberField LL] [Field Ks] [NumberField Ks] [Algebra Ks LL]
  {WL : Type} [AddCommGroup WL] [Module LL WL] [Module Ks WL]
  {W : (LL →+* ℂ) → Type} [∀ σ, NormedAddCommGroup (W σ)] [∀ σ, InnerProductSpace ℂ (W σ)]
  {G : Type} [Group G] [Fintype G] (A : FormsL LL Ks WL W G)

def twRep : Representation LL G WL where
  toFun g := (((A.chi g)⁻¹ : LLˣ) : LL) • A.ρ g
  map_one' := by simp
  map_mul' g h := by
    rw [map_mul, map_mul, smul_mul_smul_comm, mul_inv_rev, Units.val_mul, mul_comm]

omit [Fintype G] in
theorem twRep_apply (g : G) (x : WL) : twRep A g x = (((A.chi g)⁻¹ : LLˣ) : LL) • A.ρ g x := rfl

omit [Fintype G] in
theorem rho_eq (g : G) (x : WL) : A.ρ g x = ((A.chi g : LLˣ) : LL) • twRep A g x := by
  rw [twRep_apply, smul_smul]; simp

theorem eOp_eq_sum (c : G → LL) (x : WL) : A.eOp c x = ∑ g, c g • twRep A g x := by
  simp only [FormsL.eOp, LinearMap.sum_apply, LinearMap.smul_apply]
  exact Finset.sum_congr rfl fun g _ => by rw [twRep_apply, smul_smul]

theorem eOp_eq_asAlgebraHom (e : MonoidAlgebra LL G) :
    A.eOp (fun g => e.coeff g) = (twRep A).asAlgebraHom e := by
  induction e using MonoidAlgebra.induction_linear with
  | zero => ext x; simp [eOp_eq_sum]
  | add a b ha hb =>
    rw [map_add, ← ha, ← hb]; ext x
    simp [eOp_eq_sum, add_smul, Finset.sum_add_distrib]
  | single g a =>
    classical
    ext x
    rw [eOp_eq_sum, Finset.sum_eq_single g]
    · simp
    · intro b _ hb
      simp [Finsupp.single_apply, hb.symm]
    · simp

theorem eOp_idem_comm (e : MonoidAlgebra LL G) (h1 : e * e = e) (h2 : ∀ b, b * e = e * b) :
    A.eOp (fun g => e.coeff g) ∘ₗ A.eOp (fun g => e.coeff g) = A.eOp (fun g => e.coeff g) ∧
      ∀ g, A.eOp (fun g => e.coeff g) ∘ₗ A.ρ g = A.ρ g ∘ₗ A.eOp (fun g => e.coeff g) := by
  rw [eOp_eq_asAlgebraHom]
  refine ⟨by rw [← Module.End.mul_eq_comp, ← map_mul, h1], fun g => ?_⟩
  have h := congrArg (twRep A).asAlgebraHom (h2 (MonoidAlgebra.of LL G g))
  rw [map_mul, map_mul, Representation.asAlgebraHom_of] at h
  ext x
  have := LinearMap.congr_fun h x
  simp only [Module.End.mul_apply] at this
  simp only [LinearMap.comp_apply, rho_eq, map_smul, this]

omit [Fintype G] in
theorem mem_eigenspace_iff₂ (P : Subgroup G) (lam : P →* LLˣ) (x : WL) :
    x ∈ A.typeP P lam ↔ ∀ p : P, twRep A p x = ((lam p : LLˣ) : LL) • x := by
  show (∀ p : P, A.ρ p x = ((A.chi p * lam p : LLˣ) : LL) • x) ↔ _
  refine forall_congr' fun p => ?_
  rw [rho_eq, Units.val_mul, mul_smul]
  exact (smul_right_injective WL (Units.ne_zero _)).eq_iff

open Classical in

def avg (P : Subgroup G) (lam : P →* LLˣ) (x : WL) : WL :=
  ∑ p : P, ((Nat.card P : LL)⁻¹ * (((lam p)⁻¹ : LLˣ) : LL)) • twRep A p x

theorem avg_mem (P : Subgroup G) (lam : P →* LLˣ) (x : WL) : avg A P lam x ∈ A.typeP P lam := by
  classical
  rw [mem_eigenspace_iff₂]
  intro q
  unfold avg
  rw [map_sum, Finset.smul_sum, ← Equiv.sum_comp (Equiv.mulLeft q) (fun p => ((lam q : LLˣ) : LL) • _)]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp only [Equiv.coe_mulLeft, map_smul, Subgroup.coe_mul, map_mul, Module.End.mul_apply, smul_smul]
  congr 1
  simp only [mul_inv_rev, Units.val_mul, Units.val_inv_eq_inv_val]
  have := (lam q).ne_zero
  field_simp

theorem mem_span_good_iff (σ : LL →+* ℂ) {M : Type} [AddCommGroup M] [Module ℂ M] (e : W σ →ₗ[ℂ] M)
    (he : Function.Injective e) (a : G → M →ₗ[ℂ] M) (hspan : Submodule.span ℂ (Set.range (A.j σ)) = ⊤)
    (heq : ∀ g x, e (A.j σ (A.ρ g x)) = σ ((A.chi g : LLˣ) : LL) • a g (e (A.j σ x)))
    (c : G → LL) (h1 : A.eOp c ∘ₗ A.eOp c = A.eOp c) (h2 : ∀ g, A.eOp c ∘ₗ A.ρ g = A.ρ g ∘ₗ A.eOp c)
    (P : Subgroup G) (lam : P →* LLˣ) (h : W σ) :
    h ∈ Submodule.span ℂ (A.j σ '' (A.Wgood P lam c : Set WL)) ↔
      (∀ p : P, a p (e h) = σ ((lam p : LLˣ) : LL) • e h) ∧ ∑ g, σ (c g) • a g (e h) = e h := by
  classical
  have htw : ∀ g x, e (A.j σ (twRep A g x)) = a g (e (A.j σ x)) := by
    intro g x
    rw [twRep_apply, map_smulₛₗ, map_smul, heq, smul_smul, ← map_mul]
    simp
  have hE : ∀ x, e (A.j σ (A.eOp c x)) = ∑ g, σ (c g) • a g (e (A.j σ x)) := by
    intro x
    rw [eOp_eq_sum, map_sum, map_sum]
    exact Finset.sum_congr rfl fun g _ => by rw [map_smulₛₗ, map_smul, htw]
  constructor
  · intro hh
    induction hh using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨x, ⟨hx1, z, rfl⟩, rfl⟩ := hy
      refine ⟨fun p => ?_, ?_⟩
      · rw [← htw, (mem_eigenspace_iff₂ A P lam _).1 hx1 p, map_smulₛₗ, map_smul]
      · rw [← hE, ← LinearMap.comp_apply (A.eOp c) (A.eOp c), h1]
    | zero => simp
    | add x y _ _ hx hy =>
      refine ⟨fun p => ?_, ?_⟩
      · rw [map_add, map_add, hx.1, hy.1, smul_add]
      · simp only [map_add, smul_add, Finset.sum_add_distrib, hx.2, hy.2]
    | smul r x _ hx =>
      refine ⟨fun p => ?_, ?_⟩
      · rw [map_smul, map_smul, hx.1, smul_comm]
      · simp only [map_smul]
        rw [← hx.2, Finset.smul_sum, hx.2]
        exact Finset.sum_congr rfl fun g _ => smul_comm _ _ _
  · rintro ⟨hP, hG⟩
    let Pi : M →ₗ[ℂ] M := ∑ p : P, σ ((Nat.card P : LL)⁻¹ * (((lam p)⁻¹ : LLˣ) : LL)) • a p
    let E : M →ₗ[ℂ] M := ∑ g, σ (c g) • a g
    have key : ∀ y : W σ, ∃ y' ∈ Submodule.span ℂ (A.j σ '' (A.Wgood P lam c : Set WL)), e y' = E (Pi (e y)) := by
      intro y
      have hy : y ∈ Submodule.span ℂ (Set.range (A.j σ)) := hspan ▸ Submodule.mem_top
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨x, rfl⟩ := hy
        refine ⟨A.j σ (A.eOp c (avg A P lam x)), Submodule.subset_span ⟨_, ⟨fun p => ?_, ⟨_, rfl⟩⟩, rfl⟩, ?_⟩
        · rw [← LinearMap.comp_apply (A.ρ p) (A.eOp c), ← h2, LinearMap.comp_apply, avg_mem A P lam x p, map_smul]
        · have : e (A.j σ (avg A P lam x)) = Pi (e (A.j σ x)) := by
            unfold avg
            simp only [Pi, map_sum, LinearMap.sum_apply, LinearMap.smul_apply]
            exact Finset.sum_congr rfl fun g _ => by rw [map_smulₛₗ, map_smul, htw]
          rw [hE, this]
          simp only [E, LinearMap.sum_apply, LinearMap.smul_apply]
      | zero => exact ⟨0, Submodule.zero_mem _, by simp⟩
      | add x y _ _ hx hy =>
        obtain ⟨x', hx', ex⟩ := hx
        obtain ⟨y', hy', ey⟩ := hy
        exact ⟨x' + y', Submodule.add_mem _ hx' hy', by simp only [map_add, ex, ey]⟩
      | smul r x _ hx =>
        obtain ⟨x', hx', ex⟩ := hx
        exact ⟨r • x', Submodule.smul_mem _ r hx', by simp only [map_smul, ex]⟩
    obtain ⟨y', hy', ey⟩ := key h
    have hPi : Pi (e h) = e h := by
      simp only [Pi, LinearMap.sum_apply, LinearMap.smul_apply, hP, smul_smul, ← map_mul]
      have hc : (Nat.card P : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
      rw [← Finset.sum_smul]
      simp only [mul_assoc, Units.inv_mul, mul_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, map_inv₀, map_natCast]
      rw [← Nat.card_eq_fintype_card, mul_inv_cancel₀ hc, one_smul]
    have hEh : E (e h) = e h := by
      simp only [E, LinearMap.sum_apply, LinearMap.smul_apply]; exact hG
    rw [hPi, hEh] at ey
    rw [← he ey]; exact hy'

end Abstract

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem ws_eq_span (R : RealDat D A Ks) (F : Face D A) (b : Bool) (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) :
    R.WS F b i σ = Submodule.span ℂ ((R.FW i).j σ '' (R.WL F b i : Set (Fin (R.nW i) → D.what₂.LL))) := by
  have hc : (((Real.sqrt (RealDat.nP F b))⁻¹ : ℝ) : ℂ) ≠ 0 := by
    have := Real.sqrt_pos.2 (RealDat.nP_pos (F := F) b)
    exact_mod_cast (inv_pos.2 this).ne'
  unfold RealDat.WS
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, (Module.finBasis D.what₂.LL (R.WL F b i) k).2, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    have h1 := congrArg (fun z : R.WL F b i => (z : Fin (R.nW i) → D.what₂.LL))
      ((Module.finBasis D.what₂.LL (R.WL F b i)).sum_repr ⟨x, hx⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h1
    rw [← h1, map_sum]
    refine Submodule.sum_mem _ fun k _ => ?_
    rw [map_smulₛₗ]
    refine Submodule.smul_mem _ _ ?_
    rw [← Submodule.smul_mem_iff _ hc]
    exact Submodule.subset_span ⟨k, rfl⟩

theorem exists_lift (R : RealDat D A Ks) (hU : R.LUnif) (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ)
    (hinj : Function.Injective (R.HW i σ).e) {x : (R.HW i σ).H} (hx : x ≠ 0) (g : G) :
    ∃ κ, IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) κ := by
  by_contra hk
  apply hx
  have h0 : ∀ y, (R.FW i).j σ y = 0 := by
    intro y
    have : y = (R.FW i).ρ g ((R.FW i).ρ g⁻¹ y) := by
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
    apply hinj
    rw [this, (hU i σ).2.2, map_zero]
    ext v h
    show _ * actG0 _ _ _ _ _ h = 0
    unfold actG0
    rw [dif_neg hk]
    simp
  have h1 : x ∈ Submodule.span ℂ (Set.range ((R.FW i).j σ)) := (hU i σ).2.1 ▸ Submodule.mem_top
  have h2 : Submodule.span ℂ (Set.range ((R.FW i).j σ)) = ⊥ := by
    rw [Submodule.span_eq_bot]
    rintro _ ⟨y, rfl⟩
    exact h0 y
  rwa [h2] at h1

theorem mem_wat_iff (R : RealDat D A Ks) (F : Face D A) (hU : R.LUnif) (hW : R.models_HW) (b : Bool) (i : Fin D.R.m)
    (σ : D.what₂.LL →+* ℂ) (x : (R.HW i σ).H) :
    (R.HW i σ).e x ∈ R.Wat i σ (R.levL F b σ) ↔
      (∀ p : (F.lvl b).P, postOn _ (actL (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG p)) ((R.HW i σ).e x) =
        σ ((((F.lvl b).ψ⁻¹ p : D.what₂.LLˣ)) : D.what₂.LL) • (R.HW i σ).e x) ∧
      ∑ g, σ ((idemOf A.X).coeff g) • postOn _ (actL (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g)) ((R.HW i σ).e x) =
        (R.HW i σ).e x := by
  have hx : (R.HW i σ).e x ∈ R.Wall i σ := (hW i σ).2.1 ▸ LinearMap.mem_range_self _ x
  unfold RealDat.Wall at hx
  unfold RealDat.Wat
  rw [mem_goodPart]
  rw [GlobalTheory.MultMem.mem_mult_iff] at hx ⊢
  refine and_congr ?_ ?_
  · constructor
    · intro h1 g
      by_cases h0 : x = 0
      · simp [h0]
      ext v h
      have hmem : R.eG g ∈ (R.levL F b σ).H := by
        show R.eG.symm (R.eG g) ∈ (F.lvl b).P
        rw [MulEquiv.symm_apply_apply]; exact g.2
      have h2 := GlobalTheory.LevelRows.levelType_eigenfunction_of_liftable_element (V := Wc D i) (β := R.βW i) (L := R.datWp i R.triv) (P := R.levL F b σ)
        (F := (R.HW i σ).e x v) (fun κ hκ h => h1.lev v κ hκ h) ⟨R.eG g, hmem⟩ (exists_lift R hU i σ (hW i σ).1 h0 g)
      have h3 : (R.eG.symm.toMonoidHom.subgroupComap (F.lvl b).P) ⟨R.eG g, hmem⟩ = g :=
        Subtype.ext (R.eG.symm_apply_apply g)
      refine (congrFun h2 h).trans ?_
      show σ (((F.lvl b).ψ⁻¹ ((R.eG.symm.toMonoidHom.subgroupComap (F.lvl b).P) ⟨R.eG g, hmem⟩) : D.what₂.LLˣ) : D.what₂.LL) * _ = _
      rw [h3]
      rfl
    · intro h
      refine ⟨hx.aut, hx.cusp, fun v => ?_, hx.equiv, hx.cont⟩
      have hP : IsPLevel (Wc D i) (R.βW i) (R.datWp i R.triv) (R.levL F b σ) ((R.HW i σ).e x v) := by
        refine ⟨fun κ hκ y => hx.lev v κ hκ y, fun p => ?_⟩
        have h1 := congrArg (fun z : MMap (R.MW i σ) => z v) (h ⟨R.eG.symm p.1, p.2⟩)
        have h2 : R.eG (R.eG.symm p.1) = p.1 := R.eG.apply_symm_apply p.1
        simp only [h2] at h1
        exact h1
      exact fun κ hκ y => hP.hasType κ hκ y
  · have h3 : ∀ v, R.eWf i σ ((R.HW i σ).e x v) = (∑ g, σ ((idemOf A.X).coeff g) •
        postOn _ (actL (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g)) ((R.HW i σ).e x)) v := by
      intro v
      simp only [RealDat.eWf, gaL, RealDat.eC, LinearMap.sum_apply, LinearMap.smul_apply, MultilinearMap.sum_apply,
        MultilinearMap.smul_apply, postOn_apply]
      rfl
    simp only [h3]
    exact ⟨fun h => MultilinearMap.ext h, fun h v => by rw [h]⟩

theorem levelW_of_idem (R : RealDat D A Ks) (F : Face D A) (hU : R.LUnif) (hW : R.models_HW)
    (h1 : ∀ i, (R.FW i).eOp (fun g => (idemOf A.X).coeff g) ∘ₗ (R.FW i).eOp (fun g => (idemOf A.X).coeff g) =
      (R.FW i).eOp (fun g => (idemOf A.X).coeff g))
    (h2 : ∀ i g, (R.FW i).eOp (fun g => (idemOf A.X).coeff g) ∘ₗ (R.FW i).ρ g =
      (R.FW i).ρ g ∘ₗ (R.FW i).eOp (fun g => (idemOf A.X).coeff g)) : R.LLevelW F := by
  intro b i σ
  ext x
  rw [ws_eq_span, Submodule.mem_comap, mem_wat_iff R F hU hW]
  exact mem_span_good_iff (R.FW i) σ (R.HW i σ).e (hW i σ).1
    (fun g => postOn _ (actL (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g))) (hU i σ).2.1 (hU i σ).2.2 _ (h1 i) (h2 i) _ _ x

theorem levelW_of_irr (R : RealDat D A Ks) (F : Face D A) (hX : ∀ χ ∈ A.X, IsAbsIrrChar χ) (hU : R.LUnif)
    (hW : R.models_HW) : R.LLevelW F :=
  levelW_of_idem R F hU hW
    (fun i => (eOp_idem_comm (R.FW i) _ (idemOf_mul_self A.X hX) (idemOf_central A.X hX)).1)
    fun i => (eOp_idem_comm (R.FW i) _ (idemOf_mul_self A.X hX) (idemOf_central A.X hX)).2

end GlobalTheory.LevelForms

end
