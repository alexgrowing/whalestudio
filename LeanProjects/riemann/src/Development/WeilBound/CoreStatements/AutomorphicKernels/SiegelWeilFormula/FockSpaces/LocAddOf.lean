import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AuxiliaryPrimeFunction

noncomputable section

open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.KFock

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

variable {d : SD σ} (R : RD d)

theorem tens_add (w : InfinitePlace F) (f : (Fin d.m → Fin d.n → ℂ) → ℂ) (Ψ Ψ' : Mx F E d.m d.n → ℂ) :
    R.tens w f (Ψ + Ψ') = R.tens w f Ψ + R.tens w f Ψ' := by
  funext X
  simp only [RD.tens, Pi.add_apply, mul_add]

theorem tens_smul (w : InfinitePlace F) (f : (Fin d.m → Fin d.n → ℂ) → ℂ) (a : ℂ) (Ψ : Mx F E d.m d.n → ℂ) :
    R.tens w f (a • Ψ) = a • R.tens w f Ψ := by
  funext X
  simp only [RD.tens, Pi.smul_apply, smul_eq_mul]
  ring

def tensL (w : InfinitePlace F) (f : (Fin d.m → Fin d.n → ℂ) → ℂ) : (Mx F E d.m d.n → ℂ) →ₗ[ℂ] (Mx F E d.m d.n → ℂ) where
  toFun := R.tens w f
  map_add' := tens_add R w f
  map_smul' a Ψ := tens_smul R w f a Ψ

omit R in
theorem cw_add (d : SD σ) (w : InfinitePlace F) (X Z : Mx F E d.m d.n) : d.cw w (X + Z) = d.cw w X + d.cw w Z :=
  Matrix.map_add _ (map_add _) X Z

theorem loc_add_of (w : InfinitePlace F) (X Z : Mx F E d.m d.n) (h : d.cw w Z = 0) : R.loc w (X + Z) = R.loc w X := by
  unfold RD.loc
  rw [cw_add, h, add_zero]

omit R in
theorem crd_add (d : SD σ) (X Z : Mx F E d.m d.n) (k : Fin d.m × Fin d.n × Fin 2) :
    d.crd (X + Z) k = d.crd X k + d.crd Z k := by
  unfold SD.crd
  rw [Matrix.add_apply, map_add, Finsupp.add_apply]

omit R in
theorem crd_fin (d : SD σ) (Z : Mx F E d.m d.n) (h : finOne F • Z = 0) (k : Fin d.m × Fin d.n × Fin 2) :
    (d.crd Z k).2 = 0 := by
  have e1 : d.crd (finOne F • Z) k = finOne F * d.crd Z k := by
    unfold SD.crd
    rw [Matrix.smul_apply, map_smul, Finsupp.smul_apply, smul_eq_mul]
  have e2 : d.crd (finOne F • Z) k = 0 := by
    rw [h]
    unfold SD.crd
    rw [Matrix.zero_apply, map_zero, Finsupp.zero_apply]
  have e3 : (finOne F * d.crd Z k).2 = (d.crd Z k).2 := by
    show (finOne F).2 * (d.crd Z k).2 = _
    rw [show (finOne F).2 = 1 from rfl, one_mul]
  rw [← e3, ← e1, e2]
  rfl

theorem away_inv (w : InfinitePlace F) (Ψ : Mx F E d.m d.n → ℂ) (hΨ : Ψ ∈ R.away w) :
    ∀ X Z, (∀ w', w' ≠ w → d.cw w' Z = 0) → finOne F • Z = 0 → Ψ (X + Z) = Ψ X := by
  intro X Z hZ hf
  induction hΨ using Submodule.span_induction generalizing X with
  | mem x hx =>
    obtain ⟨P, g, -, rfl⟩ := hx
    have e1 : ∀ w' ∈ Finset.univ.erase w, fP (P w') (R.loc w' (X + Z)) = fP (P w') (R.loc w' X) := fun w' hw' => by
      rw [loc_add_of R w' X Z (hZ w' (Finset.ne_of_mem_erase hw'))]
    have e2 : (fun k => (d.crd (X + Z) k).2) = fun k => (d.crd X k).2 := by
      funext k
      rw [crd_add]
      show (d.crd X k).2 + (d.crd Z k).2 = _
      rw [crd_fin d Z hf k, add_zero]
    show (∏ w' ∈ Finset.univ.erase w, fP (P w') (R.loc w' (X + Z))) * g (fun k => (d.crd (X + Z) k).2) =
      (∏ w' ∈ Finset.univ.erase w, fP (P w') (R.loc w' X)) * g (fun k => (d.crd X k).2)
    rw [Finset.prod_congr rfl e1, e2]
  | zero => rfl
  | add x y _ _ hx hy => simp only [Pi.add_apply, hx, hy]
  | smul a x _ hx => simp only [Pi.smul_apply, hx]

theorem away_tens (w : InfinitePlace F) (Ψ : Mx F E d.m d.n → ℂ) (hΨ : Ψ ∈ R.away w) (P : PX d.m d.n) :
    R.tens w (fP P) Ψ ∈ R.fock := by
  have h : R.away w ≤ R.fock.comap (tensL R w (fP P)) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨P', g, hg, rfl⟩
    refine Submodule.subset_span ⟨Function.update P' w P, g, hg, ?_⟩
    funext X
    show fP P (R.loc w X) * ((∏ w' ∈ Finset.univ.erase w, fP (P' w') (R.loc w' X)) * g fun k => (d.crd X k).2) =
      (∏ w', fP (Function.update P' w P w') (R.loc w' X)) * g fun k => (d.crd X k).2
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ w), Function.update_self, mul_assoc]
    congr 2
    exact Finset.prod_congr rfl fun w' hw' => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hw')]
  exact h hΨ

theorem fock_dec (w : InfinitePlace F) (f : Mx F E d.m d.n → ℂ) (hf : f ∈ R.fock) :
    ∃ (k : ℕ) (P : Fin k → PX d.m d.n) (Ψ : Fin k → Mx F E d.m d.n → ℂ),
      (∀ i, Ψ i ∈ R.away w) ∧ f = ∑ i, R.tens w (fP (P i)) (Ψ i) := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨P, g, hg, rfl⟩ := hx
    refine ⟨1, fun _ => P w, fun _ X => (∏ w' ∈ Finset.univ.erase w, fP (P w') (R.loc w' X)) * g fun k => (d.crd X k).2,
      fun _ => Submodule.subset_span ⟨P, g, hg, rfl⟩, ?_⟩
    rw [Fin.sum_univ_one]
    funext X
    show (∏ w', fP (P w') (R.loc w' X)) * g (fun k => (d.crd X k).2) =
      fP (P w) (R.loc w X) * ((∏ w' ∈ Finset.univ.erase w, fP (P w') (R.loc w' X)) * g fun k => (d.crd X k).2)
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ w), mul_assoc]
  | zero => exact ⟨0, Fin.elim0, Fin.elim0, fun i => Fin.elim0 i, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨k1, P1, Ψ1, h1, e1⟩ := hx
    obtain ⟨k2, P2, Ψ2, h2, e2⟩ := hy
    refine ⟨k1 + k2, Fin.append P1 P2, Fin.append Ψ1 Ψ2, fun i => ?_, ?_⟩
    · refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · rw [Fin.append_left]; exact h1 j
      · rw [Fin.append_right]; exact h2 j
    · rw [Fin.sum_univ_add, e1, e2]
      simp only [Fin.append_left, Fin.append_right]
  | smul a x _ hx =>
    obtain ⟨k, P, Ψ, h, e⟩ := hx
    refine ⟨k, P, fun i => a • Ψ i, fun i => (R.away w).smul_mem a (h i), ?_⟩
    rw [e, Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => (tens_smul R w _ a (Ψ i)).symm

omit R in
theorem T_add (d : SD σ) (Φ Φ' : d.Fn) : d.T (Φ + Φ') = d.T Φ + d.T Φ' := by
  funext X
  show d.l (d.dd.rho d.B.ψ _ (Φ + Φ')) = d.l (d.dd.rho d.B.ψ _ Φ) + d.l (d.dd.rho d.B.ψ _ Φ')
  rw [← map_add]
  congr 1
  funext x
  simp only [Darboux.rho, schr, Pi.add_apply, mul_add]

omit R in
theorem T_smul (d : SD σ) (a : ℂ) (Φ : d.Fn) : d.T (a • Φ) = a • d.T Φ := by
  funext X
  show d.l (d.dd.rho d.B.ψ _ (a • Φ)) = a • d.l (d.dd.rho d.B.ψ _ Φ)
  rw [← map_smul]
  congr 1
  funext x
  simp only [Darboux.rho, schr, Pi.smul_apply, smul_eq_mul]
  ring

end PositivityTheory.SiegelWeilFormula.KFock

end
