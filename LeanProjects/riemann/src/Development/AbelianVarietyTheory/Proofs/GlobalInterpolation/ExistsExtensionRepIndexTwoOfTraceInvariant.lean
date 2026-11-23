import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.DataN
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ColRepSemisimple

open Formalism.MainNotions.N Polynomial

noncomputable section

namespace GlobalTheory.IndexTwoExt

variable {Γ k : Type} [Group Γ] [Field k] {n : ℕ}

variable {Γ k : Type} [Group Γ] [Field k] {n : ℕ} in

theorem _root_.GlobalTheory.IndexTwoExt.isSSRep_of_ker [CharZero k] (η : Γ →* ℤˣ) (t : Γ)
    (ht : η t = -1) (ρ : Γ →* GL (Fin n) k)
    (hρ : _root_.Formalism.MainNotions.N.IsSSRep (ρ.comp η.ker.subtype)) : _root_.Formalism.MainNotions.N.IsSSRep ρ := by
  intro W hW
  set σ := _root_.GlobalTheory.TraceConj.colRep ρ with hσdef
  have hσ : ∀ g v, σ g v = (ρ g : Matrix (Fin n) (Fin n) k).mulVec v := fun g v => by
    rw [hσdef, _root_.GlobalTheory.TraceConj.colRep_apply, Matrix.toLin'_apply]
  have hWσ : ∀ g, ∀ v ∈ W, σ g v ∈ W := fun g v hv => by rw [hσ]; exact hW g v hv
  obtain ⟨W', hW', hc⟩ := hρ W (fun h v hv => hW h v hv)
  set p : Module.End k (Fin n → k) := W.subtype ∘ₗ W.linearProjOfIsCompl W' hc with hpdef
  have hp1 : ∀ v, p v ∈ W := fun v => by simp [hpdef]
  have hpW : ∀ v ∈ W, p v = v := fun v hv => by
    simp only [hpdef, LinearMap.comp_apply, Submodule.subtype_apply]
    exact congrArg Subtype.val (Submodule.linearProjOfIsCompl_apply_left hc ⟨v, hv⟩)
  have hpW' : ∀ v ∈ W', p v = 0 := fun v hv => by
    simp only [hpdef, LinearMap.comp_apply, Submodule.subtype_apply]
    exact congrArg Subtype.val (Submodule.linearProjOfIsCompl_apply_right hc ⟨v, hv⟩)
  have hpc : ∀ g, η g = 1 → Commute (σ g) p := by
    intro g hg
    refine LinearMap.ext fun v => ?_
    obtain ⟨y, hy, z, hz, rfl⟩ :=
      Submodule.mem_sup.1 (hc.sup_eq_top ▸ Submodule.mem_top : v ∈ W ⊔ W')
    have hz' : σ g z ∈ W' := by rw [hσ]; exact hW' ⟨g, hg⟩ z hz
    simp only [Module.End.mul_apply, map_add, hpW y hy, hpW' z hz, hpW _ (hWσ g y hy),
      hpW' _ hz', add_zero, map_zero]
  have hconj : ∀ g, η (t⁻¹ * g * t) = η g := fun g => by
    rw [map_mul, map_mul, map_inv, mul_comm (η t)⁻¹ (η g), inv_mul_cancel_right]
  have htt : η (t * t) = 1 := by rw [map_mul, ht, neg_mul_neg, one_mul]
  have h3 : σ t⁻¹ * σ t = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
  have h4 : σ t * σ t⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  set q : Module.End k (Fin n → k) := (2⁻¹ : k) • (p + σ t * p * σ t⁻¹) with hqdef
  have hqH : ∀ h, η h = 1 → Commute (σ h) q := by
    intro h hh
    refine (Commute.add_right (hpc h hh) ?_).smul_right _
    have e1 : σ h * σ t = σ t * σ (t⁻¹ * h * t) := by
      rw [← map_mul, ← map_mul]; congr 1; group
    have e2 : σ t⁻¹ * σ h = σ (t⁻¹ * h * t) * σ t⁻¹ := by
      rw [← map_mul, ← map_mul]; congr 1; group
    have h' : η (t⁻¹ * h * t) = 1 := by rw [hconj, hh]
    show σ h * (σ t * p * σ t⁻¹) = σ t * p * σ t⁻¹ * σ h
    calc σ h * (σ t * p * σ t⁻¹) = (σ h * σ t) * p * σ t⁻¹ := by simp only [mul_assoc]
      _ = σ t * (σ (t⁻¹ * h * t) * p) * σ t⁻¹ := by rw [e1]; simp only [mul_assoc]
      _ = σ t * (p * σ (t⁻¹ * h * t)) * σ t⁻¹ := by rw [(hpc _ h').eq]
      _ = σ t * p * (σ (t⁻¹ * h * t) * σ t⁻¹) := by simp only [mul_assoc]
      _ = σ t * p * σ t⁻¹ * σ h := by rw [← e2]; simp only [mul_assoc]
  have hqt : Commute (σ t) q := by
    refine Commute.smul_right ?_ _
    have h2 := (hpc (t * t) htt).eq
    rw [map_mul] at h2
    show σ t * (p + σ t * p * σ t⁻¹) = (p + σ t * p * σ t⁻¹) * σ t
    rw [mul_add, add_mul, add_comm (p * σ t)]
    congr 1
    · rw [mul_assoc, h3, mul_one]
    · calc σ t * (σ t * p * σ t⁻¹) = (σ t * σ t * p) * σ t⁻¹ := by simp only [mul_assoc]
        _ = p * σ t * (σ t * σ t⁻¹) := by rw [h2]; simp only [mul_assoc]
        _ = p * σ t := by rw [h4, mul_one]
  have hqc : ∀ g, Commute (σ g) q := by
    intro g
    rcases Int.units_eq_one_or (η g) with hg | hg
    · exact hqH g hg
    · have h1 : η (t⁻¹ * g) = 1 := by
        rw [map_mul, map_inv, ht, hg, Int.units_inv_eq_self, neg_mul_neg, one_mul]
      have e : σ g = σ t * σ (t⁻¹ * g) := by rw [← map_mul, mul_inv_cancel_left]
      rw [e]
      exact hqt.mul_left (hqH _ h1)
  have hproj : LinearMap.IsProj W q := by
    constructor
    · intro v
      simp only [hqdef, LinearMap.smul_apply, LinearMap.add_apply, Module.End.mul_apply]
      exact W.smul_mem _ (W.add_mem (hp1 v) (hWσ t _ (hp1 _)))
    · intro v hv
      simp only [hqdef, LinearMap.smul_apply, LinearMap.add_apply, Module.End.mul_apply]
      rw [hpW v hv, hpW _ (hWσ _ v hv), ← Module.End.mul_apply, h4, Module.End.one_apply,
        ← two_smul k v, smul_smul, inv_mul_cancel₀ two_ne_zero, one_smul]
  refine ⟨LinearMap.ker q, fun g v hv => ?_, hproj.isCompl⟩
  rw [← hσ, LinearMap.mem_ker]
  have := LinearMap.congr_fun (hqc g).eq v
  simp only [Module.End.mul_apply] at this
  rw [← this, LinearMap.mem_ker.1 hv, map_zero]

theorem continuous_of_open {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [TopologicalSpace Γ] [IsTopologicalGroup Γ] (H : Subgroup Γ) (hH : IsOpen (H : Set Γ))
    (ρ : Γ →* G) (r : H →* G) (hr : Continuous r) (h : ∀ x : H, ρ x = r x) : Continuous ρ := by
  apply continuous_of_continuousAt_one
  have e : (ρ : Γ → G) ∘ (Subtype.val : H → Γ) = r := funext h
  have := (hH.isOpenEmbedding_subtypeVal.continuousAt_iff (g := (ρ : Γ → G)) (x := (1 : H))).mp
    (by
      show ContinuousAt ((ρ : Γ → G) ∘ (Subtype.val : H → Γ)) 1
      rw [e]; exact hr.continuousAt)
  exact this

private theorem isSSRep_comp_of_surjective {Γ Γ' k : Type} [Group Γ] [Group Γ'] [Field k] {n : ℕ}
    (ρ : Γ →* GL (Fin n) k) (φ : Γ' →* Γ) (hφ : Function.Surjective φ) (hρ : _root_.Formalism.MainNotions.N.IsSSRep ρ) :
    _root_.Formalism.MainNotions.N.IsSSRep (ρ.comp φ) := by
  intro W hW
  obtain ⟨W', hW', hc⟩ := hρ W (fun g v hv => by
    obtain ⟨g', rfl⟩ := hφ g
    exact hW g' v hv)
  exact ⟨W', fun g v hv => hW' (φ g) v hv, hc⟩

open Polynomial in
private theorem exists_dvd_sq_sub_X_of_eval_zero_ne_zero {k : Type} [Field k] [IsAlgClosed k] [CharZero k] :
    ∀ (d : ℕ) (f : k[X]), f.natDegree = d → f.eval 0 ≠ 0 → ∃ q : k[X], f ∣ q ^ 2 - X := by
  intro d
  induction d with
  | zero =>
    intro f hd h0
    refine ⟨0, ?_⟩
    have hc : f.coeff 0 ≠ 0 := by rwa [Polynomial.coeff_zero_eq_eval_zero]
    rw [Polynomial.eq_C_of_natDegree_eq_zero hd]
    exact (Polynomial.isUnit_C.2 (IsUnit.mk0 _ hc)).dvd
  | succ d ih =>
    intro f hd h0
    have hf : f ≠ 0 := by rintro rfl; simp at h0
    have hdeg : f.degree ≠ 0 := by
      rw [Polynomial.degree_eq_natDegree hf, hd]; exact_mod_cast Nat.succ_ne_zero d
    obtain ⟨μ, hμ⟩ := IsAlgClosed.exists_root f hdeg
    have hfg : (X - C μ) * (f /ₘ (X - C μ)) = f := Polynomial.mul_divByMonic_eq_iff_isRoot.2 hμ
    set g := f /ₘ (X - C μ) with hg
    have hgd : g.natDegree = d := by
      rw [hg, Polynomial.natDegree_divByMonic _ (Polynomial.monic_X_sub_C μ), hd,
        Polynomial.natDegree_X_sub_C]; rfl
    rw [← hfg, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] at h0
    obtain ⟨hμ0, hg0⟩ := mul_ne_zero_iff.1 h0
    have hμ' : μ ≠ 0 := fun h => hμ0 (by rw [h, sub_zero])
    obtain ⟨q, e, he⟩ := ih g hgd hg0
    have hq : q.eval μ ^ 2 = μ + g.eval μ * e.eval μ := by
      have h1 := congrArg (Polynomial.eval μ) he
      simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
        Polynomial.eval_mul] at h1
      linear_combination h1
    obtain ⟨a, ha⟩ : ∃ a : k, g.eval μ * (a * a) + 2 * q.eval μ * a + e.eval μ = 0 := by
      by_cases hgμ : g.eval μ = 0
      · have hqμ : q.eval μ ≠ 0 := by
          intro h
          apply hμ'
          rw [h, hgμ] at hq
          linear_combination -hq
        refine ⟨-e.eval μ / (2 * q.eval μ), ?_⟩
        rw [hgμ]
        field_simp
        ring
      · obtain ⟨s, hs⟩ := IsAlgClosed.exists_eq_mul_self
          (discrim (g.eval μ) (2 * q.eval μ) (e.eval μ))
        obtain ⟨x, hx⟩ := exists_quadratic_eq_zero hgμ ⟨s, hs⟩
        exact ⟨x, by linear_combination hx⟩
    have hroot : (e + 2 * C a * q + C a * C a * g).IsRoot μ := by
      simp only [Polynomial.IsRoot, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_ofNat]
      linear_combination ha
    obtain ⟨w, hw⟩ := Polynomial.dvd_iff_isRoot.2 hroot
    refine ⟨q + g * C a, w, ?_⟩
    rw [show (q + g * C a) ^ 2 - X = g * (e + 2 * C a * q + C a * C a * g) by
      linear_combination he, hw, ← hfg]
    ring

open Polynomial in
private theorem exists_sqrt_commute_of_isUnit_det {k : Type} [Field k] [IsAlgClosed k] [CharZero k] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) k) (hM : IsUnit M.det) :
    ∃ D : Matrix (Fin n) (Fin n) k, D * D = M ∧ ∀ Y, Commute M Y → Commute D Y := by
  have h0 : M.charpoly.eval 0 ≠ 0 := by
    rw [← Polynomial.coeff_zero_eq_eval_zero]
    intro h
    apply hM.ne_zero
    rw [Matrix.det_eq_sign_charpoly_coeff, h, mul_zero]
  obtain ⟨q, e, he⟩ := exists_dvd_sq_sub_X_of_eval_zero_ne_zero _ M.charpoly rfl h0
  refine ⟨Polynomial.aeval M q, ?_, fun Y hY => ?_⟩
  · have h1 := congrArg (Polynomial.aeval M) he
    rw [map_sub, map_pow, Polynomial.aeval_X, map_mul, Matrix.aeval_self_charpoly, zero_mul,
      sub_eq_zero, sq] at h1
    exact h1
  · refine Polynomial.induction_on q (fun a => ?_) (fun p r hp hr => ?_) (fun m a _ => ?_)
    · rw [Polynomial.aeval_C]; exact Algebra.commute_algebraMap_left a Y
    · rw [map_add]; exact hp.add_left hr
    · rw [map_mul, map_pow, Polynomial.aeval_C, Polynomial.aeval_X]
      exact (Algebra.commute_algebraMap_left a Y).mul_left (hY.pow_left _)

variable {Γ k : Type} [Group Γ] [Field k] {n : ℕ} in

theorem _root_.GlobalTheory.IndexTwoExt.main : ∀ (Γ k : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [Field k] [CharZero k] [IsAlgClosed k] [TopologicalSpace k] [IsTopologicalRing k] (n : ℕ) (η : Γ →* ℤˣ), IsOpen (η.ker : Set Γ) → ∀ r : η.ker →* GL (Fin n) k, Continuous r → _root_.Formalism.MainNotions.N.IsSSRep r → (∀ (g : Γ) (h h' : η.ker), (h' : Γ) = g * h * g⁻¹ → ((r h' : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).trace = ((r h : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).trace) → ∃ ρ : Γ →* GL (Fin n) k, Continuous ρ ∧ _root_.Formalism.MainNotions.N.IsSSRep ρ ∧ ∀ h : η.ker, ρ h = r h := by
  intro Γ k _ _ _ _ _ _ _ _ n η hH r hr hrss htr
  have hη : ∀ g, η g = 1 ∨ η g = -1 := fun g => Int.units_eq_one_or (η g)
  by_cases hall : ∀ g, η g = 1
  · let φ : Γ →* η.ker :=
      { toFun := fun g => ⟨g, MonoidHom.mem_ker.2 (hall g)⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    refine ⟨r.comp φ, ?_, isSSRep_comp_of_surjective r φ (fun h => ⟨h, rfl⟩) hrss, fun h => rfl⟩
    change Continuous (fun g => r (φ g))
    exact hr.comp (continuous_id.subtype_mk fun g => MonoidHom.mem_ker.2 (hall g))
  push_neg at hall
  obtain ⟨t, ht1⟩ := hall
  have ht : η t = -1 := (hη t).resolve_left ht1
  have hmem : ∀ x, η x = 1 → η (t * x * t⁻¹) = 1 := fun x hx => by
    rw [map_mul, map_mul, map_inv, hx, mul_one, mul_inv_cancel]
  have hmem' : ∀ x, η x = 1 → η (t⁻¹ * x * t) = 1 := fun x hx => by
    rw [map_mul, map_mul, map_inv, hx, mul_one, inv_mul_cancel]
  have hneg : ∀ g, η g = -1 → η (g * t⁻¹) = 1 := fun g hg => by
    rw [map_mul, map_inv, hg, ht, Int.units_inv_eq_self, neg_mul_neg, one_mul]
  have htt : η (t * t) = 1 := by rw [map_mul, ht, neg_mul_neg, one_mul]
  let c : η.ker →* η.ker :=
    { toFun := fun h => ⟨t * h * t⁻¹, MonoidHom.mem_ker.2 (hmem h (MonoidHom.mem_ker.1 h.2))⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by
        show t * ((a : Γ) * b) * t⁻¹ = (t * a * t⁻¹) * (t * b * t⁻¹)
        group) }
  have hc : ∀ h : η.ker, (c h : Γ) = t * h * t⁻¹ := fun h => rfl
  have hcs : Function.Surjective c := fun h =>
    ⟨⟨t⁻¹ * h * t, MonoidHom.mem_ker.2 (hmem' h (MonoidHom.mem_ker.1 h.2))⟩,
      Subtype.ext (by rw [hc]; show t * (t⁻¹ * (h : Γ) * t) * t⁻¹ = h; group)⟩
  obtain ⟨P, hP⟩ := _root_.GlobalTheory.TraceConj.conj_of_trace_eq η.ker k n r (r.comp c) hrss
    (isSSRep_comp_of_surjective r c hcs hrss) (fun h => (htr t h (c h) (hc h)).symm)
  have hP' : ∀ h, r (c h) = P * r h * P⁻¹ := hP
  let s : η.ker := ⟨t * t, MonoidHom.mem_ker.2 htt⟩
  have hcs' : c s = s := Subtype.ext (by rw [hc]; show t * (t * t) * t⁻¹ = t * t; group)
  have hcc : ∀ h, c (c h) = s * h * s⁻¹ := fun h => Subtype.ext (by
    rw [hc, hc]; show t * (t * (h : Γ) * t⁻¹) * t⁻¹ = (t * t) * h * (t * t)⁻¹; group)
  have hPs : Commute P (r s) := by
    have h1 := hP' s
    rw [hcs'] at h1
    show P * r s = r s * P
    calc P * r s = P * r s * P⁻¹ * P := by group
      _ = r s * P := by rw [← h1]
  have E : ∀ h, r s * r h = P * (P * r h * P⁻¹) * P⁻¹ * r s := by
    intro h
    have h1 := hP' (c h)
    rw [hcc, hP' h, map_mul, map_mul, map_inv] at h1
    rw [← h1]
    group
  have hCP : Commute (P⁻¹ * P⁻¹ * r s) P := by
    show P⁻¹ * P⁻¹ * r s * P = P * (P⁻¹ * P⁻¹ * r s)
    rw [mul_assoc, ← hPs.eq]
    group
  have hCr : ∀ h, Commute (P⁻¹ * P⁻¹ * r s) (r h) := by
    intro h
    show P⁻¹ * P⁻¹ * r s * r h = r h * (P⁻¹ * P⁻¹ * r s)
    rw [mul_assoc, E h]
    group
  have hval : ∀ x y : GL (Fin n) k, Commute x y →
      Commute (x : Matrix (Fin n) (Fin n) k) (y : Matrix (Fin n) (Fin n) k) := fun x y hxy => by
    show (x : Matrix (Fin n) (Fin n) k) * y = y * x
    rw [← Units.val_mul, ← Units.val_mul, hxy.eq]
  have hunit : ∀ x y : GL (Fin n) k,
      Commute (x : Matrix (Fin n) (Fin n) k) (y : Matrix (Fin n) (Fin n) k) → Commute x y :=
    fun x y hxy => show x * y = y * x from Units.ext (by rw [Units.val_mul, Units.val_mul]; exact hxy.eq)
  obtain ⟨D, hDD, hDc⟩ := exists_sqrt_commute_of_isUnit_det
    ((P⁻¹ * P⁻¹ * r s : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) (Matrix.isUnits_det_units _)
  have hDinv : Commute D (((P⁻¹ * P⁻¹ * r s)⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) := by
    refine hDc _ ?_
    show _ * _ = _ * _
    rw [Units.mul_inv, Units.inv_mul]
  let Dg : GL (Fin n) k :=
    ⟨D, D * (((P⁻¹ * P⁻¹ * r s)⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k),
      by rw [← mul_assoc, hDD, Units.mul_inv],
      by rw [mul_assoc, ← hDinv.eq, ← mul_assoc, hDD, Units.mul_inv]⟩
  have hDgP : Commute Dg P := hunit _ _ (hDc _ (hval _ _ hCP))
  have hDgr : ∀ h, Commute Dg (r h) := fun h => hunit _ _ (hDc _ (hval _ _ (hCr h)))
  have hDgD : Dg * Dg = P⁻¹ * P⁻¹ * r s := Units.ext (by rw [Units.val_mul]; exact hDD)
  set B : GL (Fin n) k := P * Dg with hB
  have hBB : B * B = r s := by
    calc P * Dg * (P * Dg) = P * (Dg * P) * Dg := by group
      _ = P * (P * Dg) * Dg := by rw [hDgP.eq]
      _ = P * P * (Dg * Dg) := by group
      _ = r s := by rw [hDgD]; group
  have hBr : ∀ h, B * r h = r (c h) * B := fun h => by
    rw [hP' h]
    calc P * Dg * r h = P * (Dg * r h) := by group
      _ = P * (r h * Dg) := by rw [(hDgr h).eq]
      _ = P * r h * P⁻¹ * (P * Dg) := by group
  let f : Γ → GL (Fin n) k := fun x => if hx : x ∈ η.ker then r ⟨x, hx⟩ else 1
  have hf : ∀ x (hx : η x = 1), f x = r ⟨x, MonoidHom.mem_ker.2 hx⟩ := fun x hx => dif_pos _
  have hfm : ∀ x y, η x = 1 → η y = 1 → f (x * y) = f x * f y := by
    intro x y hx hy
    have hxy : η (x * y) = 1 := by rw [map_mul, hx, hy, one_mul]
    rw [hf x hx, hf y hy, hf (x * y) hxy]
    exact map_mul r ⟨x, MonoidHom.mem_ker.2 hx⟩ ⟨y, MonoidHom.mem_ker.2 hy⟩
  have hfB : ∀ x, η x = 1 → B * f x = f (t * x * t⁻¹) * B := by
    intro x hx
    rw [hf x hx, hf _ (hmem x hx)]
    exact hBr _
  have hfs : B * B = f (t * t) := by rw [hBB, hf (t * t) htt]
  let F : Γ → GL (Fin n) k := fun g => if η g = 1 then f g else f (g * t⁻¹) * B
  have hF1 : ∀ g, η g = 1 → F g = f g := fun g hg => if_pos hg
  have hF2 : ∀ g, η g = -1 → F g = f (g * t⁻¹) * B := fun g hg => if_neg (by rw [hg]; decide)
  let ρ : Γ →* GL (Fin n) k :=
    { toFun := F
      map_one' := by
        rw [hF1 1 (map_one η), hf 1 (map_one η)]
        exact map_one r
      map_mul' := by
        intro g₁ g₂
        rcases hη g₁ with h₁ | h₁ <;> rcases hη g₂ with h₂ | h₂
        · rw [hF1 _ (by rw [map_mul, h₁, h₂, one_mul]), hF1 _ h₁, hF1 _ h₂, hfm _ _ h₁ h₂]
        · rw [hF2 _ (by rw [map_mul, h₁, h₂, one_mul]), hF1 _ h₁, hF2 _ h₂,
            show g₁ * g₂ * t⁻¹ = g₁ * (g₂ * t⁻¹) by group, hfm _ _ h₁ (hneg _ h₂), mul_assoc]
        · rw [hF2 _ (by rw [map_mul, h₁, h₂, mul_one]), hF2 _ h₁, hF1 _ h₂,
            mul_assoc (f (g₁ * t⁻¹)), hfB _ h₂, ← mul_assoc (f (g₁ * t⁻¹)), ← hfm _ _ (hneg _ h₁) (hmem _ h₂),
            show g₁ * t⁻¹ * (t * g₂ * t⁻¹) = g₁ * g₂ * t⁻¹ by group]
        · rw [hF1 _ (by rw [map_mul, h₁, h₂, neg_mul_neg, one_mul]), hF2 _ h₁, hF2 _ h₂,
            show f (g₁ * t⁻¹) * B * (f (g₂ * t⁻¹) * B) = f (g₁ * t⁻¹) * (B * f (g₂ * t⁻¹)) * B by
              simp only [mul_assoc],
            hfB _ (hneg _ h₂),
            show f (g₁ * t⁻¹) * (f (t * (g₂ * t⁻¹) * t⁻¹) * B) * B =
              f (g₁ * t⁻¹) * f (t * (g₂ * t⁻¹) * t⁻¹) * (B * B) by simp only [mul_assoc],
            hfs, ← hfm _ _ (hneg _ h₁) (hmem _ (hneg _ h₂)),
            ← hfm _ _ (by rw [map_mul, hneg _ h₁, hmem _ (hneg _ h₂), one_mul]) htt,
            show g₁ * t⁻¹ * (t * (g₂ * t⁻¹) * t⁻¹) * (t * t) = g₁ * g₂ by group] }
  have hρr : ∀ h : η.ker, ρ h = r h := fun h => by
    show F h = r h
    rw [hF1 _ (MonoidHom.mem_ker.1 h.2), hf _ (MonoidHom.mem_ker.1 h.2)]
  have hfc : ContinuousOn f (η.ker : Set Γ) := by
    rw [continuousOn_iff_continuous_restrict]
    exact hr.congr fun x => (dif_pos x.2 : f (x : Γ) = r ⟨x, x.2⟩).symm
  have hcont : Continuous ρ := by
    refine continuous_of_continuousAt_one ρ ?_
    have hnhds : (η.ker : Set Γ) ∈ nhds (1 : Γ) := hH.mem_nhds (one_mem η.ker)
    refine (hfc.continuousAt hnhds).congr ?_
    filter_upwards [hnhds] with x hx
    exact (hF1 x (MonoidHom.mem_ker.1 hx)).symm
  have hcomp : ρ.comp η.ker.subtype = r := MonoidHom.ext hρr
  refine ⟨ρ, hcont, _root_.GlobalTheory.IndexTwoExt.isSSRep_of_ker η t ht ρ ?_, hρr⟩
  rw [hcomp]
  exact hrss

end GlobalTheory.IndexTwoExt

end
