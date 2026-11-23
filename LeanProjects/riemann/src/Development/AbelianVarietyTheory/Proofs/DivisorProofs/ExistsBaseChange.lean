import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReadingsExistRow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicFormsHilbertModuleExists
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ClassPresBasic

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature
open scoped TensorProduct InnerProductSpace
open GlobalTheory.GalLift
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConjForms

theorem exists_conjChar {J K : Type} [Group J] [Field K] (σ₀ σ : K →+* ℂ) (χ : J →* ℂˣ)
    (hχ : ∀ k, ∃ y, σ₀ y = ((χ k : ℂˣ) : ℂ)) :
    ∃ χ' : J →* ℂˣ, ∀ k, ∃ y, σ₀ y = ((χ k : ℂˣ) : ℂ) ∧ σ y = ((χ' k : ℂˣ) : ℂ) := by
  choose y hy using hχ
  have h0 : ∀ k, σ (y k) ≠ 0 := fun k h => by
    have h1 := hy k
    rw [(map_eq_zero σ).1 h, map_zero] at h1
    exact (χ k).ne_zero h1.symm
  have hm : ∀ k k', y (k * k') = y k * y k' := fun k k' => σ₀.injective (by
    rw [map_mul, hy, hy, hy, map_mul, Units.val_mul])
  refine ⟨MonoidHom.mk' (fun k => Units.mk0 _ (h0 k)) fun k k' => Units.ext ?_, fun k => ⟨y k, hy k, rfl⟩⟩
  simp only [Units.val_mul, Units.val_mk0, hm, map_mul]

theorem exists_baseChange {G Γ W W' K M : Type} [Group G] [Group Γ] [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    [NormedAddCommGroup W'] [InnerProductSpace ℂ W'] [FiniteDimensional ℂ W'] [Field K] [NumberField K] [StarRing K]
    [AddCommGroup M] [Module K M] {ι : Γ →* G} {S : CSD K} {σ₀ : K →+* ℂ} (σ : K →+* ℂ) {ρ : Γ →* Module.End ℂ W}
    (ρ' : Γ →* Module.End ℂ W') {J : Subgroup G} {χ : J →* ℂˣ} (P : Bridge.ClassPres ι S σ₀ ρ J χ)
    (c₀ : M →ₛₗ[σ₀] W) (c₁ : M →ₛₗ[σ] W') (e : S.V ≃ₗ[K] M) (he : ∀ x, P.coef x = c₀ (e x))
    (hact : ∀ γ, ∃ T : M → M, (∀ v, c₀ (T v) = ρ γ (c₀ v)) ∧ ∀ v, c₁ (T v) = ρ' γ (c₁ v))
    (hχ : ∀ k, ∃ y, σ₀ y = ((χ k : ℂˣ) : ℂ)) :
    ∃ (H : HMod (G → W')) (j : S.Forms →ₛₗ[σ] H.H),
      (∃ χ' : J →* ℂˣ, (∀ k, ∃ y, σ₀ y = ((χ k : ℂˣ) : ℂ) ∧ σ y = ((χ' k : ℂˣ) : ℂ)) ∧
        H.Is (Bridge.AdForms ι ρ' J χ') (Bridge.adInner ι J P.y)) ∧
      ∀ x h, ∃ v, P.extL x h = c₀ v ∧ H.e (j x) h = c₁ v := by
  obtain ⟨χ', hχ'⟩ := exists_conjChar σ₀ σ χ hχ
  obtain ⟨H, hH⟩ := GlobalTheory.AdFormsModel.exists_hmod_adForms G Γ W' ι ρ' J χ' S.Cl P.y P.reps
    fun c => Finite.of_equiv _ (P.stabI c).toEquiv
  have hinj : Function.Injective c₀ := by
    intro v v' h
    obtain ⟨x, rfl⟩ := e.surjective v
    obtain ⟨x', rfl⟩ := e.surjective v'
    rw [← he, ← he] at h
    rw [GlobalTheory.PresBasic.coef_injective P h]
  have hv : ∀ (x : S.Forms) h, ∃ v, P.extL x h = c₀ v := by
    intro x h
    obtain ⟨y, hy, -⟩ := hχ' (P.decK h)
    obtain ⟨T, hT, -⟩ := hact (P.decG h)
    refine ⟨y • T (e ((x : S.Cl → S.V) (P.decC h))), ?_⟩
    rw [map_smulₛₗ, hy, hT, ← he]
    rfl
  choose v hv using hv
  obtain ⟨j, hj⟩ := GlobalTheory.HilbertModel.exists_lift_fun σ hH (fun x h => c₁ (v x h))
    (fun a b => by
      funext h
      have : v (a + b) h = v a h + v b h := hinj (by rw [map_add, ← hv, ← hv, ← hv, map_add]; rfl)
      rw [this, map_add]; rfl)
    (fun c a => by
      funext h
      have : v (c • a) h = c • v a h := hinj (by rw [map_smulₛₗ, ← hv, ← hv, map_smulₛₗ]; rfl)
      rw [this, map_smulₛₗ]; rfl)
    (fun a γ h k => by
      obtain ⟨y, hy, hy'⟩ := hχ' k
      obtain ⟨T, hT, hT'⟩ := hact γ
      have : v a (ι γ * h * k) = y • T (v a h) := hinj (by
        rw [map_smulₛₗ, hy, hT, ← hv, ← hv]
        exact GlobalTheory.PresBasic.extMem P a γ h k)
      show c₁ (v a (ι γ * h * k)) = _
      rw [this, map_smulₛₗ, hy', hT'])
  exact ⟨H, j, ⟨χ', hχ', hH⟩, fun x h => ⟨v x h, hv x h, congrFun (hj x) h⟩⟩

theorem factor_mem {I : Type} [Fintype I] {k : I → Type} [∀ a, CommRing (k a)] {r : ℕ} (hr : 0 < r) (S : Subfield ℂ)
    (c : ∀ a, (k a)ˣ →* ℂˣ)
    (h : ∀ g : ∀ a, GL (Fin r) (k a), (∏ a, ((c a (Matrix.GeneralLinearGroup.det (g a)) : ℂˣ) : ℂ)) ∈ S)
    (a : I) (u : (k a)ˣ) : ((c a u : ℂˣ) : ℂ) ∈ S := by
  classical
  haveI : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
  obtain ⟨g, hg⟩ := Matrix.GeneralLinearGroup.det_surjective (n := Fin r) (R := k a) u
  have h1 := h (Pi.mulSingle a g)
  rw [Finset.prod_eq_single a] at h1
  · rwa [Pi.mulSingle_eq_same, hg] at h1
  · intro b _ hb
    simp [Pi.mulSingle_eq_of_ne hb]
  · simp

theorem levFn_mem {D : D7} {n : ℕ} (β : GL (Fin n) (Lev.EAf D)) (L : LevDat D.host.E ℂ n) (S : Subfield ℂ)
    (hg : ∀ PP ∈ L.Pg, ∀ c u, ((L.cg c PP u : ℂˣ) : ℂ) ∈ S) (hq : L.Q = ∅) (x : GL (Fin n) (Lev.EAf D)) :
    ((levFn β (Lev.flag1L L) x : ℂˣ) : ℂ) ∈ S := by
  have h1 : ext1 (Lev.flag1L L).P.H (Lev.flag1L L).P.chi (rTup β (Lev.flag1L L) x) = 1 := Lev.subgroupCharExtension_one_apply _ _
  have h2 : (Lev.flag1L L).Q = ∅ := hq
  unfold levFn
  rw [h1, h2, one_mul, Finset.prod_empty, mul_one, Units.coe_prod]
  refine prod_mem fun PP hP => ?_
  rw [Units.coe_prod]
  exact prod_mem fun c _ => hg PP hP _ _

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem exists_ratMat (V : HSp D) (γ : GQ V) : ∃ γE, Bridge.IsRatMat V γ γE := by
  obtain ⟨γ, hγ⟩ := γ
  unfold GQ HFinIn at hγ
  obtain ⟨g, -, hg⟩ := hγ
  exact ⟨g, hg.symm⟩

theorem chi_mem (R : RealDat D A Ks) (hW : R.grp_chiW) (i : Fin D.R.m) (PP : Pl D.host.E) (hP : PP ∈ R.Pg) (u : (kP PP)ˣ) :
    ((R.chi ((i : ℕ) + 1) PP u : ℂˣ) : ℂ) ∈ D.what₂.embLL.fieldRange := by
  have hr : 0 < D.R.r := by
    have := D.R.m_add_three_le_k
    unfold Ranks.r; omega
  refine factor_mem (I := R.Pg) (k := fun PP => kP PP.1) hr _ (fun PP => R.chi ((i : ℕ) + 1) PP.1) (fun g => ?_) ⟨PP, hP⟩ u
  have h := hW i (R.eG.symm g)
  rw [MulEquiv.apply_symm_apply] at h
  exact ⟨_, h⟩

theorem levChar_mem (R : RealDat D A Ks) (hL : R.toLevCh.Is A.μ0) (hW : R.grp_chiW) (i : Fin D.R.m) (k : levJ R i A.μ0) :
    ∃ y, D.what₂.embLL y = (((levEnv (Vc D i) (R.βV i) (R.datVt i A.μ0)).χ k : ℂˣ) : ℂ) := by
  have hQ : R.Q A.μ0 = ∅ := by
    refine Finset.eq_empty_of_forall_notMem fun PP hP => ?_
    refine (hL.Q_ram A.μ0 PP).2 (Or.inl hP) ?_
    rw [hL.xi_base]
    intro x _
    rfl
  refine levFn_mem (R.βV i) (R.datVt i A.μ0) D.what₂.embLL.fieldRange (fun PP hP c u => ?_) hQ _
  show (((R.chi ((i : ℕ) + 1) PP u)⁻¹ : ℂˣ) : ℂ) ∈ _
  rw [Units.val_inv_eq_inv_val]
  exact inv_mem (chi_mem R hW i PP hP u)

set_option maxHeartbeats 2000000 in

theorem exists_conjForms : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.Char F → ∀ (i : Fin D.R.m), ∀ gramR c0R c0L, Comparison₂ R gramR c0R c0L → ∀ (σ : D.what₂.LL →+* ℂ) (c : CoefA (Vc D i)) (c₁ : VsV D i D.what₂.LL →ₛₗ[σ] c.W), CoefAt i σ c c₁ → ∃ (H : HMod (Bridge.Gf (Vc D i) → c.W)) (j : A.fam.amb.FL i A.μ0 →ₛₗ[σ] H.H), IsConjForms R i σ (c0L i) c c₁ H j := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hC i gramR c0R c0L hT σ c c₁ hc
  have h1 := hT.coefL i A.μ0
  obtain ⟨e, -, he, -⟩ := h1
  have hact : ∀ γ : GQ (Vc D i), ∃ T : VsV D i D.what₂.LL → VsV D i D.what₂.LL,
      (∀ v, c0L i (T v) = (R.cV i).coef.ρ γ (c0L i v)) ∧ ∀ v, c₁ (T v) = c.coef.ρ γ (c₁ v) := fun γ =>
    (exists_ratMat (Vc D i) γ).elim fun γE hγ =>
      ⟨rhoVr (labLL D) (lamV D i) γE, (hT.mapL i).1 γ γE hγ, hc.act γ γE hγ⟩
  have h2 := exists_baseChange (W' := c.W) σ c.coef.ρ (R.B.L i A.μ0).pres (c0L i) c₁ e he hact
    (levChar_mem R hC.lev hC.grp.chiW i)
  obtain ⟨H, j, hm, hb⟩ := h2
  refine ⟨H, j, hc.coef, hc.act, hc.indep, hc.span, hc.pair, hm, fun x h => ?_⟩
  exact (hb x h).imp fun v hv => ⟨(congrFun (hC.models.jV i A.μ0 x) h).trans hv.1, hv.2⟩

end GlobalTheory.ConjForms

end
