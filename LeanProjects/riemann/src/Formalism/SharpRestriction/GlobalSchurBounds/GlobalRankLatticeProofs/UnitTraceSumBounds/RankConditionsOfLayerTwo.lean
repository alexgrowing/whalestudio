import Formalism.LocalToGlobal.GroupLattices.Joint0
import Formalism.LocalToGlobal.HermitianForms.FormsTied
import Formalism.LocalToGlobal.Columns.PolyFnLemmas
import Formalism.LocalToGlobal.Columns.CoefficientsModP.PairingNondegenerateHolds
import Formalism.LocalToGlobal.Columns.InputsWeyl
import Formalism.LocalToGlobal.Columns.CmUnramifiedOfFieldConditions
import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
import Formalism.SharpRestriction.GlobalSchurBounds.TheoremThreeFamilyOfFormalDegreeInput
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.LwRankTies
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.LwAdmWeyl
import Formalism.SharpRestriction.GlobalSchurBounds.LinkTied

noncomputable section

namespace Formalism.MainNotions.Ext.Lw

open NumberField IsDedekindDomain Matrix Formalism.UG Formalism.L2.Forms Formalism.BasicNotions
open scoped TensorProduct

section Frames

variable {ι : Type} [Fintype ι] {n : ℕ}

def trFr {G : ι → Matrix (Fin n) (Fin n) ℂ} (g : ι → Matrix (Fin n) (Fin n) ℂ) (hg : ∀ τ, IsUnit (g τ).det)
    (y : Frames G) : Frames G :=
  (⟨fun τ => g τ * y.1 τ, fun τ => by rw [det_mul]; exact (hg τ).mul (y.2 τ)⟩ :
    {y : ι → Matrix (Fin n) (Fin n) ℂ // ∀ τ, IsUnit (y τ).det})

theorem trFr_val {G : ι → Matrix (Fin n) (Fin n) ℂ} (g : ι → Matrix (Fin n) (Fin n) ℂ) (hg : ∀ τ, IsUnit (g τ).det)
    (y : Frames G) (τ : ι) : (trFr g hg y).1 τ = g τ * y.1 τ := rfl

def frOne (G : ι → Matrix (Fin n) (Fin n) ℂ) : Frames G :=
  (⟨fun _ => 1, fun _ => by simp⟩ : {y : ι → Matrix (Fin n) (Fin n) ℂ // ∀ τ, IsUnit (y τ).det})

theorem cspan_eq (lam : ι → DomWeight n) : CSpan lam = Formalism.L2.DIV.VV ℂ lam := by
  refine le_antisymm ((Formalism.L2.Col.CSpan_le_span (RingHom.id ℂ) lam).trans ?_) fun F hF => ?_
  · rw [Submodule.span_le]
    rintro _ ⟨P, hP, rfl⟩
    show MvPolynomial.map (RingHom.id ℂ) P ∈ _
    rw [MvPolynomial.map_id]
    exact hP
  · have h := Formalism.L2.Col.map_mem_CSpan (RingHom.id ℂ) lam F hF
    rwa [MvPolynomial.map_id] at h

theorem valC_eq (G : ι → Matrix (Fin n) (Fin n) ℂ) (lam : ι → DomWeight n) :
    ValC G lam = (Formalism.L2.DIV.VV ℂ lam).map (fnOf G (shiftOf lam) 1) := by
  unfold ValC
  rw [cspan_eq]

def valCEquiv (G : ι → Matrix (Fin n) (Fin n) ℂ) (lam : ι → DomWeight n) :
    Formalism.L2.DIV.VV ℂ lam ≃ₗ[ℂ] ValC G lam :=
  (Submodule.equivMapOfInjective _ (Formalism.L2.Col.fnOf_injective G (shiftOf lam) 1 (fun _ => by simp) (frOne G)) _).trans
    (LinearEquiv.ofEq _ _ (valC_eq G lam).symm)

instance valC_fd (G : ι → Matrix (Fin n) (Fin n) ℂ) (lam : ι → DomWeight n) : FiniteDimensional ℂ (ValC G lam) :=
  haveI : FiniteDimensional ℂ (Formalism.L2.DIV.VV ℂ lam) := Module.Finite.of_basis (Formalism.L2.DIV.bVV ℂ lam)
  Module.Finite.equiv (valCEquiv G lam)

theorem finrank_valC (G : ι → Matrix (Fin n) (Fin n) ℂ) (lam : ι → DomWeight n) :
    Module.finrank ℂ (ValC G lam) = ∏ τ, Nat.card (Formalism.GradedWeylDivisibility.ssIdx n n (lam τ).natW) := by
  rw [← (valCEquiv G lam).finrank_eq, Module.finrank_eq_nat_card_basis (Formalism.L2.DIV.bVV ℂ lam)]
  exact Nat.card_pi

theorem valC_tr (G : ι → Matrix (Fin n) (Fin n) ℂ) (lam : ι → DomWeight n) (g : ι → Matrix (Fin n) (Fin n) ℂ)
    (hg : ∀ τ, IsUnit (g τ).det) {v : Frames G → ℂ} (hv : v ∈ ValC G lam) :
    (fun z => v (trFr g hg z)) ∈ ValC G lam := by
  rw [valC_eq] at hv ⊢
  obtain ⟨P, hP, rfl⟩ := hv
  refine ⟨(∏ τ, (g τ).det ^ shiftOf lam τ) • Formalism.GradedWeylDivisibility.blockAct ℂ g P,
    Submodule.smul_mem _ _ (Formalism.L2.DIV.ps_blockAct_mem_VV lam g hP), ?_⟩
  rw [← Formalism.L2.Col.fnOf_mul]
  funext z
  simp only [fnOf, LinearMap.coe_mk, AddHom.coe_mk, trFr_val, Pi.one_apply, Matrix.one_mul, Matrix.mul_one]

def piConstEquiv {M : Type} [AddCommGroup M] [Module ℂ M] (c : Type) (V : Submodule ℂ M) :
    (Submodule.pi Set.univ fun _ : c => V) ≃ₗ[ℂ] (c → V) where
  toFun p i := ⟨p.1 i, (Submodule.mem_pi.1 p.2) i (Set.mem_univ i)⟩
  invFun q := ⟨fun i => (q i).1, Submodule.mem_pi.2 fun i _ => (q i).2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

theorem finrank_pi_const {M : Type} [AddCommGroup M] [Module ℂ M] (c : Type) [Fintype c] (V : Submodule ℂ M)
    [FiniteDimensional ℂ V] :
    Module.finrank ℂ (Submodule.pi Set.univ fun _ : c => V) = Fintype.card c * Module.finrank ℂ V := by
  rw [(piConstEquiv c V).finrank_eq, Module.finrank_pi_fintype]
  simp

end Frames

section Adelic

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}
  {ι : Type} [Fintype ι]

theorem atInf_mul (emb : ι → E →+* ℂ) (a b : Matrix (Fin n) (Fin n) E) :
    atInf emb (a * b) = atInf emb a * atInf emb b := by
  funext τ
  show (a * b).map (emb τ) = a.map (emb τ) * b.map (emb τ)
  exact Matrix.map_mul

theorem isUnit_atInf (emb : ι → E →+* ℂ) (γ : GL (Fin n) E) (τ : ι) : IsUnit (atInf emb γ.1 τ).det := by
  have h := (Matrix.isUnits_det_units γ).map (emb τ)
  rw [RingHom.map_det] at h
  exact h

theorem fiC_eq_pi (S : StepLevel F E σ J T f bad) (emb : ι → E →+* ℂ) (lam : ι → DomWeight n) {c : Type}
    (y : c → UPts σ J (FiniteAdeleRing (𝓞 F) F))
    (hy : Function.Bijective (fun c => (Quotient.mk'' (y c) : Cls S)))
    (hs : ∀ c (γ : UJ (σ : E →+* E) J),
      bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ.1 ∈ S.U.map (MulAut.conj (y c).1).toMonoidHom → γ = 1) :
    FiC S emb lam y = Submodule.pi Set.univ (fun _ => ValC (gramC J emb) lam) := by
  classical
  have hU : ∀ κ : S.U, (κ : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F) :=
    fun κ => ((S.U_eq _).1 κ.2).1
  have dec : ∀ x : UPts σ J (FiniteAdeleRing (𝓞 F) F), ∃ (c0 : c) (γ : UJ (σ : E →+* E) J) (κ : S.U),
      x.1 = bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ.1 * (y c0).1 * κ.1 := by
    intro x
    obtain ⟨c0, hc0⟩ := hy.2 (Quotient.mk'' x)
    obtain ⟨h, hh, k, hk, e⟩ := (DoubleCoset.eq _ _ (y c0) x).1 hc0
    have hh' : (h : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) ∈
        (UJ (σ : E →+* E) J).map (bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F))) := Subgroup.mem_subgroupOf.1 hh
    have hk' : (k : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) ∈ S.U := Subgroup.mem_subgroupOf.1 hk
    obtain ⟨γ, hγ, hγe⟩ := Subgroup.mem_map.1 hh'
    refine ⟨c0, ⟨γ, hγ⟩, ⟨_, hk'⟩, ?_⟩
    rw [e, Subgroup.coe_mul, Subgroup.coe_mul, ← hγe]
  have uniq : ∀ (c1 c2 : c) (γ1 γ2 : UJ (σ : E →+* E) J) (κ1 κ2 : S.U),
      bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ1.1 * (y c1).1 * κ1.1 =
        bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ2.1 * (y c2).1 * κ2.1 → c1 = c2 ∧ γ1 = γ2 ∧ κ1 = κ2 := by
    intro c1 c2 γ1 γ2 κ1 κ2 e
    have hr : bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) (γ2⁻¹ * γ1).1 =
        (y c2).1 * (κ2 * κ1⁻¹).1 * ((y c1).1)⁻¹ := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]
      calc (bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ2.1)⁻¹ * bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ1.1
          = (bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ2.1)⁻¹ *
              (bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ1.1 * (y c1).1 * κ1.1) * (κ1.1)⁻¹ * ((y c1).1)⁻¹ := by group
        _ = (bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ2.1)⁻¹ *
              (bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ2.1 * (y c2).1 * κ2.1) * (κ1.1)⁻¹ * ((y c1).1)⁻¹ := by rw [e]
        _ = (y c2).1 * (κ2.1 * (κ1.1)⁻¹) * ((y c1).1)⁻¹ := by group
    have hc : c1 = c2 := by
      let r : UPts σ J (FiniteAdeleRing (𝓞 F) F) := y c2 * ⟨(κ2 * κ1⁻¹).1, hU _⟩ * (y c1)⁻¹
      let kk : UPts σ J (FiniteAdeleRing (𝓞 F) F) := ⟨(κ1 * κ2⁻¹).1, hU _⟩
      have hrR : r ∈ (ratPts σ J (FiniteAdeleRing (𝓞 F) F)).subgroupOf (UPts σ J (FiniteAdeleRing (𝓞 F) F)) := by
        rw [Subgroup.mem_subgroupOf]
        refine Subgroup.mem_map.2 ⟨(γ2⁻¹ * γ1).1, (γ2⁻¹ * γ1).2, ?_⟩
        rw [hr]
        rfl
      have hkK : kk ∈ S.U.subgroupOf (UPts σ J (FiniteAdeleRing (𝓞 F) F)) := by
        rw [Subgroup.mem_subgroupOf]
        exact (κ1 * κ2⁻¹).2
      refine hy.1 (show (Quotient.mk'' (y c1) : Cls S) = Quotient.mk'' (y c2) from
        (DoubleCoset.eq _ _ (y c1) (y c2)).2 ⟨r, hrR, kk, hkK, ?_⟩)
      apply Subtype.ext
      simp only [r, kk, Subgroup.coe_mul, Subgroup.coe_inv]
      group
    subst hc
    have hγ : γ2⁻¹ * γ1 = 1 := by
      refine hs c1 _ ?_
      rw [hr]
      refine Subgroup.mem_map.2 ⟨(κ2 * κ1⁻¹).1, (κ2 * κ1⁻¹).2, ?_⟩
      simp [MulAut.conj_apply]
    have hγ' : γ1 = γ2 := (inv_mul_eq_one.1 hγ).symm
    subst hγ'
    refine ⟨rfl, rfl, Subtype.ext (mul_left_cancel e)⟩
  choose cc gam kap hdec using dec
  ext φ
  constructor
  · rintro ⟨g, hg, rfl⟩
    refine Submodule.mem_pi.2 fun c0 _ => ?_
    exact (Submodule.mem_pi.1 (Submodule.mem_inf.1 hg).2) (y c0) (Set.mem_univ _)
  · intro hφ
    have hφ' : ∀ c0, φ c0 ∈ ValC (gramC J emb) lam := fun c0 => (Submodule.mem_pi.1 hφ) c0 (Set.mem_univ _)
    let gf : UPts σ J (FiniteAdeleRing (𝓞 F) F) → Frames (gramC J emb) → ℂ := fun x z =>
      ((S.chi (kap x) : ℂˣ) : ℂ) * φ (cc x) (trFr (atInf emb (((gam x).1)⁻¹ : GL (Fin n) E).1) (isUnit_atInf emb _) z)
    have hAd : gf ∈ AdFun S emb := by
      intro γ hγ x x' κ hx z z' hz
      have e : bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) ((⟨γ, hγ⟩ : UJ (σ : E →+* E) J) * gam x).1 *
          (y (cc x)).1 * (kap x * κ).1 =
          bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) (gam x').1 * (y (cc x')).1 * (kap x').1 := by
        rw [← hdec x', hx, hdec x]
        simp only [Subgroup.coe_mul, map_mul, mul_assoc]
      obtain ⟨e1, e2, e3⟩ := uniq _ _ _ _ _ _ e
      have hfr : trFr (atInf emb (((gam x').1)⁻¹ : GL (Fin n) E).1) (isUnit_atInf emb _) z =
          trFr (atInf emb (((gam x).1)⁻¹ : GL (Fin n) E).1) (isUnit_atInf emb _) z' := by
        apply Subtype.ext
        funext τ
        rw [trFr_val, trFr_val, hz τ, ← Matrix.mul_assoc, ← e2]
        congr 1
        have h1 : ((((⟨γ, hγ⟩ : UJ (σ : E →+* E) J) * gam x).1)⁻¹ : GL (Fin n) E).1 * γ.1 =
            (((gam x).1)⁻¹ : GL (Fin n) E).1 := by
          rw [← Units.val_mul]
          congr 1
          rw [Subgroup.coe_mul]
          group
        have h2 := congrFun (atInf_mul emb ((((⟨γ, hγ⟩ : UJ (σ : E →+* E) J) * gam x).1)⁻¹ : GL (Fin n) E).1 γ.1) τ
        rw [h1] at h2
        rw [h2]
        rfl
      show ((S.chi (kap x') : ℂˣ) : ℂ) * φ (cc x') _ = ((S.chi κ : ℂˣ) : ℂ) * (((S.chi (kap x) : ℂˣ) : ℂ) * φ (cc x) _)
      rw [hfr, ← e1, ← e3, map_mul, Units.val_mul]
      ring
    have hpi : ∀ x, gf x ∈ ValC (gramC J emb) lam := by
      intro x
      have : gf x = ((S.chi (kap x) : ℂˣ) : ℂ) •
          (fun z => φ (cc x) (trFr (atInf emb (((gam x).1)⁻¹ : GL (Fin n) E).1) (isUnit_atInf emb _) z)) := rfl
      rw [this]
      exact Submodule.smul_mem _ _ (valC_tr _ lam _ _ (hφ' (cc x)))
    show φ ∈ (AdFun S emb ⊓ Submodule.pi Set.univ (fun _ => ValC (gramC J emb) lam)).map (res emb y)
    refine Submodule.mem_map.2 ⟨gf, Submodule.mem_inf.2 ⟨hAd, Submodule.mem_pi.2 fun x _ => hpi x⟩, ?_⟩
    funext c0 z
    have e : bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) (gam (y c0)).1 * (y (cc (y c0))).1 * (kap (y c0)).1 =
        bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) (1 : UJ (σ : E →+* E) J).1 * (y c0).1 * (1 : S.U).1 := by
      rw [← hdec (y c0)]
      simp
    obtain ⟨e1, e2, e3⟩ := uniq _ _ _ _ _ _ e
    show ((S.chi (kap (y c0)) : ℂˣ) : ℂ) * φ (cc (y c0)) _ = φ c0 z
    have hfr : trFr (atInf emb (((gam (y c0)).1)⁻¹ : GL (Fin n) E).1) (isUnit_atInf emb _) z = z := by
      apply Subtype.ext
      funext τ
      rw [trFr_val, e2]
      simp [atInf]
    rw [hfr, e1, e3, map_one, Units.val_one, one_mul]

end Adelic

section Rec

theorem finrank_lowest_forms_space {D : D7} (C : ColsTiedSym D) (u : D.what₂.Word) (hst : (D.mem u).C.StabZero) :
    Module.finrank ℂ (D.mem u).A.Mu0 = Fintype.card ((D.mem u).C.cls 0) *
      ∏ τ, Nat.card (Formalism.GradedWeylDivisibility.ssIdx (D.R.N 0) (D.R.N 0) ((D.fm u).lam 0 τ).natW) := by
  let T := (C.forms u).to0
  let e : ((D.mem u).C.cls 0 → (D.mem u).C.Y 0 → ℂ) ≃ₗ[ℂ] ((D.mem u).C.cls 0 → Fr D 0 (Nat.zero_le _) → ℂ) :=
    { toFun := fun φ c z => φ c (T.val0.eY.symm z)
      invFun := fun ψ c w => ψ c (T.val0.eY w)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun φ => by funext c w; simp
      right_inv := fun ψ => by funext c z; simp }
  have hmap : (D.mem u).A.Mu0.map (e : _ →ₗ[ℂ] _) = FiC T.cls0.lev (embT D) ((D.fm u).lam 0) T.cls0.y := by
    ext ψ
    rw [Submodule.mem_map_equiv, Mu0_iff T.val0]
    have h1 : (fun c z => (e.symm ψ) c (T.val0.eY.symm z)) = ψ :=
      funext fun c => funext fun z => by
        show ψ c (T.val0.eY (T.val0.eY.symm z)) = ψ c z
        rw [Equiv.apply_symm_apply]
    rw [h1]
  have hs : ∀ c (γ : UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _))),
      bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ.1 ∈
        T.cls0.lev.U.map (MulAut.conj (T.cls0.y c).1).toMonoidHom → γ = 1 := by
    intro c γ hγ
    obtain ⟨s, hs⟩ := (T.cls0.stabI_range c γ).2 hγ
    have := hst c
    rw [← hs, Subsingleton.elim s 1, map_one]
  rw [← LinearEquiv.finrank_map_eq e, hmap, fiC_eq_pi _ _ _ _ T.cls0.y_bij hs, finrank_pi_const, finrank_valC]

theorem card_ssIdx_eq {D : D7} (u : D.what₂.Word) (τ : D.what₂.Tau) :
    (Nat.card (Formalism.GradedWeylDivisibility.ssIdx (D.R.N 0) (D.R.N 0) ((D.fm u).lam 0 τ).natW) : ℝ) = StandardLattice.dimV (StandardLattice.uColR D u τ) := by
  have hw : (Nat.card (Formalism.GradedWeylDivisibility.ssIdx (D.R.N 0) (D.R.N 0) ((D.fm u).lam 0 τ).natW) : ℝ) =
      Formalism.LogVandermondeBounds.StandardLattice.dimVN (Formalism.L2.Col.wSeq ((D.fm u).lam 0 τ)) (D.R.N 0) := Formalism.L2.Col.weylDim_holds _
  rw [hw, StandardLattice.column_param_eq_fun, StandardLattice.dim_weyl_fin_eq_nat]
  have key : ∀ (x : ℕ → ℝ) (N : ℕ), N = D.R.k →
      (∀ i, i < D.R.k → x i = StandardLattice.uN D u τ i - ((D.R.k : ℝ) - 1) / 2) →
      Formalism.LogVandermondeBounds.StandardLattice.dimVN x N = Formalism.LogVandermondeBounds.StandardLattice.dimVN (StandardLattice.uN D u τ) D.R.k := by
    intro x N hN hx
    subst hN
    unfold Formalism.LogVandermondeBounds.StandardLattice.dimVN
    rw [Formalism.L2.Col.vandN_congr (y := StandardLattice.uN D u τ) fun i j hi hj => by rw [hx i hi, hx j hj]; ring]
  refine key _ _ (Formalism.L2.Col.rankN_zero D.R) fun i hi => ?_
  have hi0 : i < D.R.N 0 := by rw [Formalism.L2.Col.rankN_zero]; exact hi
  have h := (D.fm u).lam_eq 0 (Nat.zero_le _) τ ⟨i, hi0⟩
  rw [dif_pos hi] at h
  unfold hcToWeightQ rhoVec at h
  have h' : ((((D.fm u).lam 0 τ).w ⟨i, hi0⟩ : ℤ) : ℝ) =
      (((D.hcW u τ).u ⟨i, hi⟩ : ℚ) : ℝ) - (((D.R.k : ℝ) - 1) / 2 - (i : ℝ)) := by
    have h2 := congrArg (fun q : ℚ => (q : ℝ)) h
    push_cast at h2
    exact h2
  unfold Formalism.L2.Col.wSeq StandardLattice.uN
  rw [dif_pos hi0, dif_pos hi, h']
  ring

theorem mu0Tie_of_sym {D : D7} (C : ColsTiedSym D) (u : D.what₂.Word) : StandardLattice.Mu0Tie D u := by
  intro hst
  show ((Module.finrank ℂ (D.mem u).A.Mu0 : ℕ) : ℝ) = _
  rw [finrank_lowest_forms_space C u hst, Nat.cast_mul, Nat.cast_prod, Nat.card_eq_fintype_card]
  congr 1
  exact Finset.prod_congr rfl fun τ _ => card_ssIdx_eq u τ

end Rec

section Fam

theorem rank_conditions_of_layer_two {eps : ℝ} (Fm : FamP eps) (h : RealPlaceSecondLayerConditions Fm) : RankTiesF Fm := by
  obtain ⟨x0, h⟩ := h
  exact rank_conditions_of_lowest_space Fm ⟨x0, fun x hx i u => mu0Tie_of_sym (h x hx i).2.choose u⟩

theorem rankTiesF_of_col' {eps : ℝ} (Fm : FamP eps)
    (h : ∃ x0 : ℝ, ∀ x (hx : Fm.x1 < x), x0 ≤ x → ∀ i : Fm.Ix x, ∀ u : (Fm.D x i).what₂.Word,
      ∃ X : StandardLattice.ColRep (Fm.D x i) (Fm.ex x hx i).lev u, StandardLattice.BaseWeightColumnCondition (Fm.D x i) (Fm.ex x hx i).lev u X) :
    RankTiesF Fm := by
  obtain ⟨x0, h⟩ := h
  exact rankTiesF_of_col Fm ⟨x0, fun x hx h0 i =>
    ⟨StandardLattice.HarishChandraReduction.content_bound_clause _ _, StandardLattice.HarishChandraReduction.levels_pro_g_on_columns _ _, weyl_dimension_formula_holds _, h x hx h0 i⟩⟩

end Fam

end Formalism.MainNotions.Ext.Lw

end
