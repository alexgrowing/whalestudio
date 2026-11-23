import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DiscreteSpectrumResidual
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CapCommuteRtInfGL

open NumberField IsDedekindDomain Formalism.L2.Host
open scoped ContDiff Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec

noncomputable section

namespace GlobalTheory.BlockCap

open Matrix

theorem qdet_intertwine {M M' : Type} [AddCommGroup M] [Module ℂ M] [AddCommGroup M'] [Module ℂ M'] {k : ℕ}
    (R : M →ₗ[ℂ] M') (X : Fin k → Fin k → Module.End ℂ M) (Y : Fin k → Fin k → Module.End ℂ M')
    (h : ∀ p q, R ∘ₗ X p q = Y p q ∘ₗ R) (v : ℂ) :
    R ∘ₗ Formalism.REAL.qdet X v = Formalism.REAL.qdet Y v ∘ₗ R := by
  let S : Subalgebra ℂ (Module.End ℂ M × Module.End ℂ M') :=
    { carrier := {z | R ∘ₗ z.1 = z.2 ∘ₗ R}
      mul_mem' := fun {x y} hx hy => by
        change R ∘ₗ (x.1 ∘ₗ y.1) = (x.2 ∘ₗ y.2) ∘ₗ R
        rw [← LinearMap.comp_assoc, hx, LinearMap.comp_assoc, hy, LinearMap.comp_assoc]
      add_mem' := fun {x y} hx hy => by
        change R ∘ₗ (x.1 + y.1) = (x.2 + y.2) ∘ₗ R
        rw [LinearMap.comp_add, LinearMap.add_comp, hx, hy]
      algebraMap_mem' := fun c => by
        change R ∘ₗ (algebraMap ℂ (Module.End ℂ M) c) = (algebraMap ℂ (Module.End ℂ M') c) ∘ₗ R
        ext φ; simp }
  let Z : Fin k → Fin k → S := fun p q => ⟨(X p q, Y p q), h p q⟩
  have h1 := map_qdet ((AlgHom.fst ℂ _ _).comp S.val) Z v
  have h2 := map_qdet ((AlgHom.snd ℂ _ _).comp S.val) Z v
  have hm : R ∘ₗ ((Formalism.REAL.qdet Z v : S) : Module.End ℂ M × Module.End ℂ M').1 =
      ((Formalism.REAL.qdet Z v : S) : Module.End ℂ M × Module.End ℂ M').2 ∘ₗ R := (Formalism.REAL.qdet Z v).2
  have e1 : ((Formalism.REAL.qdet Z v : S) : Module.End ℂ M × Module.End ℂ M').1 = Formalism.REAL.qdet X v := h1
  have e2 : ((Formalism.REAL.qdet Z v : S) : Module.End ℂ M × Module.End ℂ M').2 = Formalism.REAL.qdet Y v := h2
  rw [e1, e2] at hm
  exact hm

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E]

theorem tensorForms_update {c : ℕ} {n : Fin c → ℕ} (π : ∀ i, CuspSub E (n i)) (i : Fin c)
    (m : ∀ j, GA E (n j)) {F : (∀ j, GA E (n j)) → ℂ} (hF : F ∈ tensorForms π) :
    ∃ θ ∈ (π i).V, ∀ y, F (Function.update m i y) = θ.1 y := by
  classical
  let L : ((∀ j, GA E (n j)) → ℂ) →ₗ[ℂ] (GA E (n i) → ℂ) :=
    { toFun := fun F y => F (Function.update m i y), map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  have hle : tensorForms π ≤ ((π i).V.map (Sm E (n i)).subtype).comap L := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨φ, rfl⟩
    refine ⟨(∏ j ∈ Finset.univ.erase i, (φ j).1.1 (m j)) • (φ i).1, (π i).V.smul_mem _ (φ i).2, ?_⟩
    funext y
    change (∏ j ∈ Finset.univ.erase i, (φ j).1.1 (m j)) * (φ i).1.1 y =
      ∏ j, (φ j).1.1 (Function.update m i y j)
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i), Function.update_self, mul_comm]
    congr 1
    refine Finset.prod_congr rfl fun j hj => ?_
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  obtain ⟨θ, hθ, e⟩ := hle hF
  exact ⟨θ, hθ, fun y => (congrFun e y).symm⟩

theorem map_leviEmb {R S : Type} [CommRing R] [CommRing S] (p : R →+* S) {c N : ℕ} {n : Fin c → ℕ}
    (e : (Σ j, Fin (n j)) ≃ Fin N) (g : Levi R fun j => Fin (n j)) :
    GeneralLinearGroup.map p (leviEmb R e g) = leviEmb S e fun j => GeneralLinearGroup.map p (g j) := by
  ext a b
  obtain ⟨⟨j, x⟩, rfl⟩ := e.surjective a
  obtain ⟨⟨k, y⟩, rfl⟩ := e.surjective b
  by_cases hjk : j = k
  · subst hjk
    simp [leviEmb_apply_same]
  · simp [leviEmb_apply_ne _ e _ hjk]

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {c N : ℕ} {n : Fin c → ℕ}

theorem leviEmb_update_infGL (e : (Σ j, Fin (n j)) ≃ Fin N) (i : Fin c) (y : GL (Fin (n i)) (Cinf E)) :
    leviEmb (Ad E) e (Function.update 1 i (infGL E (n i) y)) =
      infGL E N (leviEmb (Cinf E) e (Function.update 1 i y)) := by
  classical
  refine ga_ext ?_ ?_
  · rw [pInf_infGL, map_leviEmb]
    congr 1
    funext j
    by_cases hj : j = i
    · subst hj; simp
    · simp [Function.update_of_ne hj]
  · rw [pFin_infGL, map_leviEmb]
    have : (fun j => GeneralLinearGroup.map (pFin E) (Function.update (1 : Levi (Ad E) fun j => Fin (n j)) i
        (infGL E (n i) y) j)) = 1 := by
      funext j
      by_cases hj : j = i
      · subst hj; simp
      · simp [Function.update_of_ne hj]
    rw [this, map_one]

theorem update_mul (m : Levi (Ad E) fun j => Fin (n j)) (i : Fin c) (g z : GA E (n i)) :
    Function.update m i (g * z) = Function.update m i g * Function.update (1 : Levi (Ad E) fun j => Fin (n j)) i z := by
  classical
  funext j
  by_cases hj : j = i
  · subst hj; simp
  · simp [Function.update_of_ne hj]

def iota (e : (Σ j, Fin (n j)) ≃ Fin N) (i : Fin c) (x : Lie E (n i)) : Lie E N :=
  toL (reindex e e (blockDiagonal' (Function.update (fun j => (1 : Matrix (Fin (n j)) (Fin (n j)) (Cinf E))) i
    (Matrix.of x))))

theorem iota_val (e : (Σ j, Fin (n j)) ≃ Fin N) (i : Fin c) (y : GL (Fin (n i)) (Cinf E)) :
    iota e i (toL y.val) = toL (leviEmb (Cinf E) e (Function.update 1 i y)).val := by
  classical
  have h : (fun j => ((Function.update (1 : Levi (Cinf E) fun j => Fin (n j)) i y j : GL _ _) :
      Matrix (Fin (n j)) (Fin (n j)) (Cinf E))) =
      Function.update (fun j => (1 : Matrix (Fin (n j)) (Fin (n j)) (Cinf E))) i y.val := by
    funext j
    by_cases hj : j = i
    · subst hj; simp
    · simp [Function.update_of_ne hj]
  simp only [iota, leviEmb, MonoidHom.coe_toHomUnits, MonoidHom.coe_mk, OneHom.coe_mk]
  rw [h]
  congr
  exact Subsingleton.elim _ _

def blockLin (e : (Σ j, Fin (n j)) ≃ Fin N) (i : Fin c) : Lie E (n i) →ₗ[ℝ] Lie E N where
  toFun x := toL (reindex e e (blockDiagonal' (Pi.single (M := fun j => Matrix (Fin (n j)) (Fin (n j)) (Cinf E)) i
    (Matrix.of x))))
  map_add' x y := by
    rw [← Matrix.of_add_of, Pi.single_add, blockDiagonal'_add]
    rfl
  map_smul' r x := by
    ext a b
    obtain ⟨⟨j, p⟩, rfl⟩ := e.surjective a
    obtain ⟨⟨k, q⟩, rfl⟩ := e.surjective b
    by_cases hjk : j = k
    · subst hjk
      by_cases hj : j = i
      · subst hj
        simp [blockDiagonal'_apply_eq]
      · simp [blockDiagonal'_apply_eq, Pi.single_eq_of_ne hj]
    · simp [blockDiagonal'_apply_ne _ _ _ hjk]

def blockCLM (e : (Σ j, Fin (n j)) ≃ Fin N) (i : Fin c) : Lie E (n i) →L[ℝ] Lie E N :=
  LinearMap.toContinuousLinearMap (blockLin e i)

theorem blockCLM_apply (e : (Σ j, Fin (n j)) ≃ Fin N) (i : Fin c) (x : Lie E (n i)) :
    blockCLM e i x = blockLin e i x := rfl

theorem iota_eq (e : (Σ j, Fin (n j)) ≃ Fin N) (i : Fin c) (x : Lie E (n i)) :
    iota e i x = iota e i 0 + blockCLM e i x := by
  classical
  have h : Function.update (fun j => (1 : Matrix (Fin (n j)) (Fin (n j)) (Cinf E))) i (Matrix.of x) =
      Function.update (fun j => (1 : Matrix (Fin (n j)) (Fin (n j)) (Cinf E))) i (Matrix.of 0) +
        Pi.single (M := fun j => Matrix (Fin (n j)) (Fin (n j)) (Cinf E)) i (Matrix.of x) := by
    funext j
    by_cases hj : j = i
    · subst hj; ext; simp
    · simp [Function.update_of_ne hj, Pi.single_eq_of_ne hj]
  simp only [iota, blockCLM_apply, blockLin, LinearMap.coe_mk, AddHom.coe_mk]
  rw [h, blockDiagonal'_add]
  rfl

theorem contDiff_iota (e : (Σ j, Fin (n j)) ≃ Fin N) (i : Fin c) : ContDiff ℝ ∞ (iota (E := E) e i) := by
  have : iota (E := E) e i = fun x => iota e i 0 + blockCLM e i x := funext (iota_eq e i)
  rw [this]
  have h2 : ContDiff ℝ ∞ (blockCLM (E := E) e i) := (blockCLM (E := E) e i).contDiff
  exact contDiff_const.add h2

theorem hasFDerivAt_iota (e : (Σ j, Fin (n j)) ≃ Fin N) (i : Fin c) (x : Lie E (n i)) :
    HasFDerivAt (iota (E := E) e i) (blockCLM e i) x := by
  have : iota (E := E) e i = fun x => iota e i 0 + blockCLM e i x := funext (iota_eq e i)
  rw [this]
  exact (blockCLM e i).hasFDerivAt.const_add _

theorem iota_one (e : (Σ j, Fin (n j)) ≃ Fin N) (i : Fin c) : iota (E := E) e i (oneL E (n i)) = oneL E N := by
  have h := iota_val (E := E) e i 1
  rw [show Function.update (1 : Levi (Cinf E) fun j => Fin (n j)) i 1 = 1 from Function.update_eq_self i 1,
    map_one] at h
  exact h

theorem iota_mem_invSet (e : (Σ j, Fin (n j)) ≃ Fin N) (i : Fin c) {x : Lie E (n i)} (hx : x ∈ invSet E (n i)) :
    iota e i x ∈ invSet E N := by
  obtain ⟨u, hu⟩ := hx
  have e1 : x = toL u.val := hu.symm
  rw [e1, iota_val]
  exact val_mem_invSet _

theorem blockLin_single (e : (Σ j, Fin (n j)) ≃ Fin N) (i : Fin c) (p q : Fin (n i)) (x : Cinf E) :
    blockLin e i (toL (Matrix.single p q x)) = toL (Matrix.single (e ⟨i, p⟩) (e ⟨i, q⟩) x) := by
  funext a b
  obtain ⟨⟨j, p'⟩, rfl⟩ := e.surjective a
  obtain ⟨⟨k, q'⟩, rfl⟩ := e.surjective b
  by_cases hjk : j = k
  · subst hjk
    by_cases hj : j = i
    · subst hj
      simp only [blockLin, LinearMap.coe_mk, AddHom.coe_mk]
      change (blockDiagonal' _).submatrix e.symm e.symm (e ⟨j, p'⟩) (e ⟨j, q'⟩) =
        Matrix.single (e ⟨j, p⟩) (e ⟨j, q⟩) x (e ⟨j, p'⟩) (e ⟨j, q'⟩)
      rw [submatrix_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply, blockDiagonal'_apply_eq,
        Pi.single_eq_same, Matrix.single_apply, Matrix.of_apply]
      change Matrix.single p q x p' q' = _
      rw [Matrix.single_apply]
      simp
    · simp [blockLin, blockDiagonal'_apply_eq, Pi.single_eq_of_ne hj, Matrix.single_apply, Ne.symm hj]
  · simp only [blockLin, LinearMap.coe_mk, AddHom.coe_mk]
    change (blockDiagonal' _).submatrix e.symm e.symm (e ⟨j, p'⟩) (e ⟨k, q'⟩) =
      Matrix.single (e ⟨i, p⟩) (e ⟨i, q⟩) x (e ⟨j, p'⟩) (e ⟨k, q'⟩)
    rw [submatrix_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply, blockDiagonal'_apply_ne _ _ _ hjk,
      Matrix.single_apply, if_neg]
    rintro ⟨h1, h2⟩
    exact hjk ((congrArg Sigma.fst (e.injective h1)).symm.trans (congrArg Sigma.fst (e.injective h2)))

def restr (e : (Σ j, Fin (n j)) ≃ Fin N) (m : Levi (Ad E) fun j => Fin (n j)) (i : Fin c) (φ : GA E N → ℂ) :
    GA E (n i) → ℂ := fun y => φ (leviEmb (Ad E) e (Function.update m i y))

theorem chart_restr (e : (Σ j, Fin (n j)) ≃ Fin N) (m : Levi (Ad E) fun j => Fin (n j)) (i : Fin c)
    (φ : GA E N → ℂ) (g : GA E (n i)) {x : Lie E (n i)} (hx : x ∈ invSet E (n i)) :
    chart (restr e m i φ) g x = chart φ (leviEmb (Ad E) e (Function.update m i g)) (iota e i x) := by
  obtain ⟨u, hu⟩ := hx
  have e1 : x = toL u.val := hu.symm
  subst e1
  rw [chart_val, iota_val, chart_val, restr, update_mul, map_mul, leviEmb_update_infGL]

theorem restr_mem_Sm (e : (Σ j, Fin (n j)) ≃ Fin N) (m : Levi (Ad E) fun j => Fin (n j)) (i : Fin c)
    {φ : GA E N → ℂ} (hφ : φ ∈ Sm E N) : restr e m i φ ∈ Sm E (n i) := fun g =>
  ((hφ _).comp (contDiff_iota e i).contDiffOn fun _ hx => iota_mem_invSet e i hx).congr
    fun _ hx => chart_restr e m i φ g hx

theorem lieD_restr (e : (Σ j, Fin (n j)) ≃ Fin N) (m : Levi (Ad E) fun j => Fin (n j)) (i : Fin c)
    {φ : GA E N → ℂ} (hφ : φ ∈ Sm E N) (X : Lie E (n i)) (y : GA E (n i)) :
    lieD X (restr e m i φ) y = lieD (blockCLM e i X) φ (leviEmb (Ad E) e (Function.update m i y)) := by
  have ev : chart (restr e m i φ) y =ᶠ[𝓝 (oneL E (n i))]
      chart φ (leviEmb (Ad E) e (Function.update m i y)) ∘ iota e i :=
    Filter.eventually_of_mem (isOpen_invSet.mem_nhds isUnit_one) fun _ hx => chart_restr e m i φ y hx
  have hd : HasFDerivAt (chart φ (leviEmb (Ad E) e (Function.update m i y)) ∘ iota e i)
      ((fderiv ℝ (chart φ (leviEmb (Ad E) e (Function.update m i y))) (oneL E N)).comp (blockCLM e i))
      (oneL E (n i)) := by
    have h1 := (differentiableAt_chart hφ (leviEmb (Ad E) e (Function.update m i y))).hasFDerivAt
    rw [← iota_one e i] at h1
    rw [← iota_one (E := E) e i]
    exact h1.comp _ (hasFDerivAt_iota e i _)
  rw [lieD, ev.fderiv_eq, hd.fderiv]
  rfl

def restrLin (e : (Σ j, Fin (n j)) ≃ Fin N) (m : Levi (Ad E) fun j => Fin (n j)) (i : Fin c) :
    Sm E N →ₗ[ℂ] Sm E (n i) where
  toFun ψ := ⟨restr e m i ψ.1, restr_mem_Sm e m i ψ.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem restrLin_lie (e : (Σ j, Fin (n j)) ≃ Fin N) (m : Levi (Ad E) fun j => Fin (n j)) (i : Fin c)
    (X : Lie E (n i)) : restrLin e m i ∘ₗ lie E N (blockCLM e i X) = lie E (n i) X ∘ₗ restrLin e m i :=
  LinearMap.ext fun ψ => Subtype.ext <| funext fun y => (lieD_restr e m i ψ.2 X y).symm

theorem restrLin_Eop (e : (Σ j, Fin (n j)) ≃ Fin N) (m : Levi (Ad E) fun j => Fin (n j)) (i : Fin c)
    (τ : E →+* ℂ) (p q : Fin (n i)) :
    restrLin e m i ∘ₗ Eop (a := N) τ (e ⟨i, p⟩) (e ⟨i, q⟩) = Eop τ p q ∘ₗ restrLin e m i := by
  have hS : ∀ z : Cinf E, restrLin e m i ∘ₗ lieS E N (e ⟨i, p⟩) (e ⟨i, q⟩) z =
      lieS E (n i) p q z ∘ₗ restrLin e m i := by
    intro z
    rw [lieS_apply, lieS_apply, ← blockLin_single, ← blockCLM_apply, restrLin_lie]
  simp only [Eop]
  rw [LinearMap.comp_smul, LinearMap.smul_comp, LinearMap.comp_sub, LinearMap.sub_comp, LinearMap.comp_smul,
    LinearMap.smul_comp, hS, hS]

theorem qdet_block_levi : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] {c N : ℕ} (n : Fin c → ℕ)
    (h : ∑ i, n i = N) (π : ∀ i, CuspSub E (n i)) (τ : E →+* ℂ) (i : Fin c) (M : Multiset ℂ),
    (π i).HasInfChar τ M → ∀ (u : ℂ) (ψ : Sm E N),
      (fun m => ψ.1 (leviEmb (Ad E) (stdBlocks n h) m)) ∈ tensorForms π → ∀ m,
        (Formalism.REAL.qdet (fun p q : Fin (n i) => Eop (a := N) τ (stdBlocks n h ⟨i, p⟩) (stdBlocks n h ⟨i, q⟩))
          (u + ((n i : ℂ) - 1) / 2) ψ).1 (leviEmb (Ad E) (stdBlocks n h) m) =
          (M.map (u + ·)).prod * ψ.1 (leviEmb (Ad E) (stdBlocks n h) m) := by
  intro E _ _ _ c N n h π τ i M hM u ψ hψ m
  obtain ⟨θ, hθ, hθe⟩ := tensorForms_update π i m hψ
  have hR : restrLin (stdBlocks n h) m i ψ = θ := Subtype.ext (funext fun y => hθe y)
  have key := LinearMap.congr_fun (qdet_intertwine (restrLin (stdBlocks n h) m i) _ (Eop τ)
    (restrLin_Eop (stdBlocks n h) m i τ) (u + ((n i : ℂ) - 1) / 2)) ψ
  rw [LinearMap.comp_apply, LinearMap.comp_apply, hR] at key
  have k2 := congrArg (fun φ : Sm E (n i) => φ.1 (m i)) key
  have hc : Formalism.REAL.qdet (Eop τ) (u + ((n i : ℂ) - 1) / 2) θ = (M.map (u + ·)).prod • θ := hM.2 u θ hθ
  have hm : Function.update m i (m i) = m := Function.update_eq_self i m
  simp only [hc] at k2
  have k3 : (Formalism.REAL.qdet (fun p q : Fin (n i) => Eop (a := N) τ (stdBlocks n h ⟨i, p⟩) (stdBlocks n h ⟨i, q⟩))
      (u + ((n i : ℂ) - 1) / 2) ψ).1 (leviEmb (Ad E) (stdBlocks n h) (Function.update m i (m i))) =
      (M.map (u + ·)).prod * θ.1 (m i) := k2
  rw [hm, ← hθe, hm] at k3
  exact k3

end GlobalTheory.BlockCap
