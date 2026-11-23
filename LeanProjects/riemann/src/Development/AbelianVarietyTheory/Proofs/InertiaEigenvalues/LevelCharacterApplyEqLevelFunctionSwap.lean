import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MapVVSymmMapVV
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoefficientMapUniqueBijectiveComplexExtensionStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ActOfMemGfC
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ExportSeries GlobalTheory.ConjTwist GlobalTheory.SeriesTie.Scale

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace GlobalTheory.MtLatConj

variable {D : D7}

theorem locC_conj {τ : ℂ ≃+* ℂ} {ν ν' : Twist D Circle} (h : ConjChar τ ν ν') (hν : ν.Good) (hν' : ν'.Good)
    (PP : Pl D.host.E) (u : (kP PP)ˣ) : τ ((ν.locC PP u : ℂˣ) : ℂ) = ((ν'.locC PP u : ℂˣ) : ℂ) := by
  classical
  unfold Twist.locC
  by_cases hP : PP ∈ ν.Q
  · have hP' : PP ∈ ν'.Q := by rw [h.1]; exact hP
    rw [if_pos hP, if_pos hP']
    exact (h.res hν hν' hP u).symm
  · have hP' : PP ∉ ν'.Q := by rw [h.1]; exact hP
    rw [if_neg hP, if_neg hP']
    simp

theorem levPOf_ext1_apply_eq_units_map_inv {r : ℕ} {Pg : Finset (Pl D.host.E)} (P : LevelP Pg r ℂ) {τ : ℂ ≃+* ℂ}
    (hP : ∀ p, τ ((P.chi p : ℂˣ) : ℂ) = ((P.chi p : ℂˣ) : ℂ)) (g : G0 Pg r) :
    τ ((Formalism.L2.DIV.ext1 P.H P.chi g : ℂˣ) : ℂ) = ((Formalism.L2.DIV.ext1 P.H P.chi g : ℂˣ) : ℂ) := by
  unfold Formalism.L2.DIV.ext1
  split_ifs
  · exact hP _
  · simp

theorem levFn_conj {S T : HSp D} {B : Base S T} (hB : B.Good) {τ : ℂ ≃+* ℂ} {ψ ψ' : Twist D Circle} (hψ : ψ.Good)
    (hψ' : ψ'.Good) (hcc : ConjChar τ ψ ψ') (hf : FixDat B τ) (x : GL (Fin S.rank) (Lev.EAf D)) :
    τ ((levFn B.F.βS (B.levS ψ) x : ℂˣ) : ℂ) = ((levFn B.F.βS (B.levS ψ') x : ℂˣ) : ℂ) := by
  simp only [levFn, Base.levS, Units.val_mul, Units.coe_prod, map_mul, map_prod]
  rw [hcc.1]
  congr 1
  congr 1
  · exact levPOf_ext1_apply_eq_units_map_inv B.G.P hf.2.1 _
  · refine Finset.prod_congr rfl fun PP hPP => Finset.prod_congr rfl fun c _ => ?_
    exact hf.2.2 PP hPP _
  · refine Finset.prod_congr rfl fun PP _ => ?_
    rw [MonoidHom.mul_apply, MonoidHom.mul_apply, Units.val_mul, Units.val_mul, map_mul,
      locC_conj hf.conjChar hB.de hB.de, locC_conj hcc hψ hψ']

theorem mem_levJ_of {S T : HSp D} (B : Base S T) {ψ ψ' : Twist D Circle} (hQ : ψ'.Q = ψ.Q) {k : Bridge.Gf S}
    (hk : k ∈ B.levJ ψ') : k ∈ B.levJ ψ := by
  simp only [Base.levJ, Subgroup.mem_comap, Lev.toAfE, mem_lev, mem_parLev, Base.levS] at hk ⊢
  rw [hQ] at hk
  exact hk

set_option maxHeartbeats 800000 in
theorem levelCharacter_apply_eq_levelFunction_swap {S T : HSp D} (B : Base S T) (ψ : Twist D Circle) (k : B.levJ ψ) :
    B.levLam ψ k = levFn B.F.βS (B.levS ψ) (Formalism.UG.bc (Lev.swapAE D) k.1.1) := by
  unfold Base.levLam Lev.levCharAfE
  rfl

theorem levLam_conj {S T : HSp D} {B : Base S T} (hB : B.Good) {τ : ℂ ≃+* ℂ} {ψ ψ' : Twist D Circle} (hψ : ψ.Good)
    (hψ' : ψ'.Good) (hcc : ConjChar τ ψ ψ') (hf : FixDat B τ) (k : B.levJ ψ') :
    ((B.levLam ψ' k : ℂˣ) : ℂ) = τ ((B.levLam ψ ⟨k.1, mem_levJ_of B hcc.1 k.2⟩ : ℂˣ) : ℂ) := by
  rw [levelCharacter_apply_eq_levelFunction_swap, levelCharacter_apply_eq_levelFunction_swap]
  exact (levFn_conj hB hψ hψ' hcc hf _).symm

variable {n : ℕ}

def cmapGL (τ : ℂ ≃+* ℂ) : GLR D n →* GLR D n :=
  MonoidHom.pi fun t => (Units.map (RingHom.mapMatrix (τ : ℂ →+* ℂ) : Matrix (Fin n) (Fin n) ℂ →+* _).toMonoidHom).comp
    (Pi.evalMonoidHom (fun _ : D.what₂.Tau => GL (Fin n) ℂ) t)

theorem cmapGL_val (τ : ℂ ≃+* ℂ) (y : GLR D n) (t : D.what₂.Tau) (a b : Fin n) :
    ((cmapGL τ y t : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) a b = τ (((y t : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) a b) := rfl

theorem coefFn_conj (τ : ℂ ≃+* ℂ) (lam : D.what₂.Tau → DomWeight n) (F : Pol ℂ D.what₂.Tau n) (y : GLR D n) :
    coefFn (RingHom.id ℂ) lam (MvPolynomial.map (τ : ℂ →+* ℂ) F) y = τ (coefFn (RingHom.id ℂ) lam F (cmapGL τ.symm y)) := by
  simp only [coefFn, map_mul]
  congr 1
  · simp only [detFam, MonoidHom.coe_mk, OneHom.coe_mk, Units.coe_prod, map_prod, Units.val_zpow_eq_zpow_val, map_zpow₀,
      GeneralLinearGroup.val_det_apply]
    refine Finset.prod_congr rfl fun t _ => ?_
    congr 1
    have e := RingHom.map_det (τ : ℂ →+* ℂ) (((cmapGL τ.symm y t : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ))
    refine Eq.trans ?_ e.symm
    congr 1
    ext a b
    simp [cmapGL_val]
  · simp only [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_map]
    have e := MvPolynomial.hom_eval₂ F (RingHom.id ℂ) (τ : ℂ →+* ℂ)
      (fun v : D.what₂.Tau × Fin n × Fin n => ((cmapGL τ.symm y v.1 : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) v.2.1 v.2.2)
    refine Eq.trans ?_ e.symm
    congr 1
    funext v
    simp [cmapGL_val]

theorem cmapGL_embGL (τ : ℂ ≃+* ℂ) (hτ : ∀ (t : D.what₂.Tau) (e : D.host.E), τ (tauE D t e) = tauE D t e)
    (g : GL (Fin n) D.host.E) : cmapGL τ (embGL (tauE D) g) = embGL (tauE D) g := by
  funext t
  refine Units.ext (Matrix.ext fun a b => ?_)
  rw [cmapGL_val]
  exact hτ t _

theorem hasLaw_conj {i : Fin D.R.m} {B : Base (Vc D i) (Wc D i)} (hB : B.Good)
    {Φ : VsV D i ℂ →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank} {κ : ℂ} (hκ0 : κ ≠ 0) (hval : ∀ x, Φ x ∈ B.valSpace)
    (hκ : ∀ x : VsV D i ℂ, harmFn (Wc D i).rank B.w B.F.BS (Φ x) =
      κ • coefFn (RingHom.id ℂ) (lamV D i) (x : Pol ℂ D.what₂.Tau (Vc D i).rank))
    {τ : ℂ ≃+* ℂ} (hτE : ∀ (t : D.what₂.Tau) (e : D.host.E), τ.symm (tauE D t e) = tauE D t e)
    {ψ ψ' : Twist D Circle} (hψ : ψ.Good) (hψ' : ψ'.Good) (hcc : ConjChar τ ψ ψ') (hf : FixDat B τ)
    {x x' : Bridge.Gf (Vc D i) → VsV D i ℂ} (hxx : ∀ h, ConjVec i τ (x h) (x' h))
    (hlaw : B.HasLaw ψ (fun h => Φ (x h))) : B.HasLaw ψ' (fun h => Φ ((τ κ / κ) • x' h)) := by
  intro γ h k
  have hfn : ∀ (w : VsV D i ℂ) z, harmFn (Wc D i).rank B.w B.F.BS (Φ w) z = κ * coefLin (lamV D i) w z :=
    fun w z => congrFun (hκ w) z
  obtain ⟨γE, hγ⟩ : ∃ γE, Bridge.IsRatMat (Vc D i) γ γE := by
    obtain ⟨y, -, hy⟩ := γ.2
    exact ⟨y, hy.symm⟩
  set u := realGL B.F.θ (Vc D i) γ with hu_def
  have hu : u = embGL (tauE D) γE := realGL_rat hB.frame.vac.2.inf hγ
  have hact : ∀ P z, harmFn (Wc D i).rank B.w B.F.BS (B.act γ P) z =
      harmFn (Wc D i).rank B.w B.F.BS P (u⁻¹ * z) := fun P z => harmFn_fockGL _ _ _ _ _
  have hfix : ∀ z, cmapGL τ.symm (u⁻¹ * z) = u⁻¹ * cmapGL τ.symm z := by
    intro z
    rw [map_mul, hu, ← map_inv, cmapGL_embGL τ.symm hτE]
  have hconj : ∀ w z, coefLin (lamV D i) (x' w) z = τ (coefLin (lamV D i) (x w) (cmapGL τ.symm z)) := fun w z => by
    change coefFn (RingHom.id ℂ) (lamV D i) (x' w : Pol ℂ D.what₂.Tau (Vc D i).rank) z =
      τ (coefFn (RingHom.id ℂ) (lamV D i) (x w : Pol ℂ D.what₂.Tau (Vc D i).rank) _)
    rw [hxx w]
    exact coefFn_conj τ _ _ z
  set g := Bridge.ratF (Vc D i) γ * h * (k : Bridge.Gf (Vc D i)) with hg
  set lam : ℂ := ((B.levLam ψ ⟨k.1, mem_levJ_of B hcc.1 k.2⟩ : ℂˣ) : ℂ) with hlam
  have hL : Φ (x g) = lam • B.act γ (Φ (x h)) := hlaw γ h ⟨k.1, mem_levJ_of B hcc.1 k.2⟩
  have E1 : ∀ z, coefLin (lamV D i) (x g) z = lam * coefLin (lamV D i) (x h) (u⁻¹ * z) := by
    intro z
    have e1 : harmFn (Wc D i).rank B.w B.F.BS (Φ (x g)) z =
        lam * harmFn (Wc D i).rank B.w B.F.BS (B.act γ (Φ (x h))) z := by
      rw [hL, map_smul]
      rfl
    rw [hact, hfn, hfn] at e1
    apply mul_left_cancel₀ hκ0
    rw [e1]
    ring
  have hl' : ((B.levLam ψ' k : ℂˣ) : ℂ) = τ lam := levLam_conj hB hψ hψ' hcc hf k
  show Φ ((τ κ / κ) • x' g) = ((B.levLam ψ' k : ℂˣ) : ℂ) • B.act γ (Φ ((τ κ / κ) • x' h))
  rw [hl']
  refine sub_eq_zero.1 (GlobalTheory.T.harmonic_polynomial_eq_zero_of_function D _ _ B.w B.F.BS hB.wt (GlobalTheory.CoefLatConj.pq_le hB) _
    (sub_mem (hval _) (Submodule.smul_mem _ _ (Base.act_mem_valSpace _ (hval _)))) ?_)
  funext z
  have e2 : ∀ (P Q : PolF D (Wc D i).rank (Vc D i).rank) (a : ℂ), harmFn (Wc D i).rank B.w B.F.BS (P - a • Q) z =
      harmFn (Wc D i).rank B.w B.F.BS P z - a * harmFn (Wc D i).rank B.w B.F.BS Q z := fun P Q a => by
    rw [map_sub, map_smul]
    rfl
  rw [e2, hact, hfn, hfn, map_smul, map_smul]
  change κ * ((τ κ / κ) * coefLin (lamV D i) (x' g) z) - τ lam * (κ * ((τ κ / κ) * coefLin (lamV D i) (x' h) (u⁻¹ * z))) = 0
  rw [hconj, hconj, hfix, E1, map_mul]
  ring

theorem mtLat_conj : ∀ (D : D7) (i : Fin D.R.m) (B : Base (Vc D i) (Wc D i)), B.Good → B.w.lam = lamV D i → ∀ (Φ : VsV D i ℂ →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank) (κ : ℂ), κ ≠ 0 → (∀ x, Φ x ∈ B.valSpace) → (∀ x : VsV D i ℂ, harmFn (Wc D i).rank B.w B.F.BS (Φ x) = κ • coefFn (RingHom.id ℂ) (lamV D i) (x : Pol ℂ D.what₂.Tau (Vc D i).rank)) → ∀ (K : Type) [Field K] [NumberField K] (σ : K →+* ℂ) (emb : D.what₂.Tau → (D.host.E →+* K)) (O : Subring ℂ), IsCoefRing σ emb O → ∀ τ : ℂ ≃+* ℂ, (∀ a : K, τ (σ a) = σ a) → ∀ (ψ ψ' : Twist D Circle), ψ.Good → ψ'.Good → ConjChar τ ψ ψ' → FixDat B τ → ∀ f f' : Bridge.Gf (Vc D i) → PolF D (Wc D i).rank (Vc D i).rank, (∀ h, ∃ x x' : VsV D i ℂ, ConjVec i τ x x' ∧ f h = Φ x ∧ f' h = Φ ((τ κ / κ) • x')) → f ∈ B.mtLat σ emb O ψ → f' ∈ B.mtLat σ emb (O.map (τ : ℂ →+* ℂ)) ψ' := by
  intro D i B hB hlam Φ κ hκ0 hval hκ K _ _ σ emb O hc τ hτ ψ ψ' hψ hψ' hcc hf f f' hff hfm
  choose x x' hxx hfx hfx' using hff
  have hτE : ∀ (t : D.what₂.Tau) (e : D.host.E), τ.symm (tauE D t e) = tauE D t e := fun t e => by
    rw [← hc.emb t, RingHom.comp_apply, τ.symm_apply_eq, hτ]
  obtain ⟨hform, hlat⟩ := (Base.mem_mtLat B σ emb O).1 hfm
  have hlaw : B.HasLaw ψ (fun h => Φ (x h)) := by
    have e : f = fun h => Φ (x h) := funext hfx
    rw [← e]
    exact ((Base.mem_formsC B).1 hform).2
  have e' : f' = fun h => Φ ((τ κ / κ) • x' h) := funext hfx'
  refine (Base.mem_mtLat B σ emb (O.map (τ : ℂ →+* ℂ))).2 ⟨(Base.mem_formsC B).2 ⟨fun h => (hfx' h).symm ▸ hval _, ?_⟩, fun h => ?_⟩
  · rw [e']
    exact hasLaw_conj hB hκ0 hval hκ hτE hψ hψ' hcc hf hxx hlaw
  · rw [hfx' h]
    exact (GlobalTheory.CoefLatConj.conj_mem_iff Φ hlam hκ0 hval hκ σ emb O τ hτ h (hxx h)).1 (hfx h ▸ hlat h)

end GlobalTheory.MtLatConj
