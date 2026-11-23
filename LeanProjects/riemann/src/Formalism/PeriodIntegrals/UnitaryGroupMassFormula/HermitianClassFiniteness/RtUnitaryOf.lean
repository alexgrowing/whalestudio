import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HermitianClassFiniteness.Development
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.DictRing

noncomputable section

open NumberField Matrix Formalism.UG PI.InHHClassFin IsDedekindDomain
open scoped TensorProduct

namespace PI.UnitaryGroupMassFormula.InHHClassFin

abbrev rtA (I : Formalism.MainNotions.S.AutInst) : Type := I.E ⊗[I.F] FiniteAdeleRing (𝓞 I.F) I.F

abbrev rtι (I : Formalism.MainNotions.S.AutInst) : I.E →+* rtA I := inclE (F := I.F) (FiniteAdeleRing (𝓞 I.F) I.F)

theorem rt_inj (I : Formalism.MainNotions.S.AutInst) : Function.Injective (rtι I) := by
  haveI : Nonempty (HeightOneSpectrum (𝓞 I.F)) := by
    obtain ⟨p, hp0, hp⟩ := Ring.not_isField_iff_exists_prime.mp (RingOfIntegers.not_isField I.F)
    exact ⟨⟨p, hp, hp0⟩⟩
  haveI : Nontrivial (FiniteAdeleRing (𝓞 I.F) I.F) := by
    obtain ⟨v⟩ := ‹Nonempty (HeightOneSpectrum (𝓞 I.F))›
    refine ⟨⟨0, 1, fun h => ?_⟩⟩
    have h2 := congrArg (fun x : FiniteAdeleRing (𝓞 I.F) I.F => x v) h
    first
    | exact zero_ne_one (α := v.adicCompletion I.F) h2
    | exact zero_ne_one (α := v.adicCompletion I.F) (by simpa using h2)
  first
  | (have h1 : ⇑(rtι I) = (LinearMap.lTensor I.E (Algebra.linearMap I.F (FiniteAdeleRing (𝓞 I.F) I.F))) ∘
        (TensorProduct.rid I.F I.E).symm := by
      funext a
      simp [rtι, inclE]
     rw [h1]
     exact (Module.Flat.lTensor_preserves_injective_linearMap _ (algebraMap I.F _).injective).comp
       (TensorProduct.rid I.F I.E).symm.injective)
  | exact Algebra.TensorProduct.includeLeft_injective (R := I.F) (S := I.F) (algebraMap I.F _).injective

theorem rt_map_inj (I : Formalism.MainNotions.S.AutInst) {p q : Type} (M N : Matrix p q I.E)
    (h : M.map (rtι I) = N.map (rtι I)) : M = N := by
  ext i j
  exact rt_inj I (congrFun (congrFun h i) j)

theorem rt_sig (I : Formalism.MainNotions.S.AutInst) (e : I.E) :
    sigR I.cm.sig (FiniteAdeleRing (𝓞 I.F) I.F) (rtι I e) = rtι I (starRingEnd I.E e) := by
  show Algebra.TensorProduct.map I.cm.sig (AlgHom.id I.F _) (e ⊗ₜ 1) = (starRingEnd I.E e) ⊗ₜ 1
  rw [Algebra.TensorProduct.map_tmul]
  rfl

theorem rt_cT_map (I : Formalism.MainNotions.S.AutInst) {p q : Type} (M : Matrix p q I.E) :
    cT (sigR I.cm.sig (FiniteAdeleRing (𝓞 I.F) I.F)) (M.map (rtι I)) =
      (cT (starRingEnd I.E) M).map (rtι I) := by
  ext i j
  simp only [cT, Matrix.map_apply, Matrix.transpose_apply, rt_sig]

theorem rt_unitary_of (I : Formalism.MainNotions.S.AutInst) {k : Type} [Fintype k] (M J : Matrix k k I.E)
    (h : cT (sigR I.cm.sig (FiniteAdeleRing (𝓞 I.F) I.F)) (M.map (rtι I)) * J.map (rtι I) *
      M.map (rtι I) = J.map (rtι I)) :
    cT (starRingEnd I.E) M * J * M = J := by
  rw [rt_cT_map, ← Matrix.map_mul, ← Matrix.map_mul] at h
  exact rt_map_inj I _ _ h

theorem rt_det_ne (I : Formalism.MainNotions.S.AutInst) {k : Type} [Fintype k] [DecidableEq k]
    (M : Matrix k k I.E) (u : GL k (rtA I)) (hu : (u : Matrix k k (rtA I)) = M.map (rtι I)) :
    M.det ≠ 0 := by
  intro h0
  haveI : Nontrivial (rtA I) :=
    nontrivial_of_ne _ _ (by simpa using (rt_inj I).ne (one_ne_zero (α := I.E)))
  have h1 : IsUnit ((u : Matrix k k (rtA I)).det) := (Matrix.isUnit_iff_isUnit_det _).mp u.isUnit
  rw [hu, ← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero] at h1
  exact not_isUnit_zero h1

theorem rt_sig_eq (I : Formalism.MainNotions.S.AutInst) : (I.cm.sig : I.E →+* I.E) = starRingEnd I.E := by
  first
  | rfl
  | exact RingHom.ext fun e => rfl

theorem rt_conj_mul {k : Type} [Fintype k] [DecidableEq k] (P Pi A B : Matrix k k ℂ) (h1 : P * Pi = 1) :
    (Pi * A * P) * (Pi * B * P) = Pi * (A * B) * P := by
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc P Pi, h1, Matrix.one_mul]

def rtReal (I : Formalism.MainNotions.S.AutInst) (γ : GL (Fin I.n) I.E) (hγ : γ ∈ UJ (starRingEnd I.E) I.J)
    (v : InfinitePlace I.F) : Formalism.REAL.UJ (I.ε v) :=
  ⟨⟨(I.P v)⁻¹ * (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) * I.P v,
    (I.P v)⁻¹ * ((γ⁻¹ : GL (Fin I.n) I.E) : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) * I.P v,
    by
      have e1 : (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) *
          ((γ⁻¹ : GL (Fin I.n) I.E) : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) = 1 := by
        rw [← Matrix.map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
          Matrix.map_one _ (map_zero _) (map_one _)]
      rw [rt_conj_mul _ _ _ _ (Formalism.MainNotions.LeviCoordinates.rrg_P_mul_inv I v), e1, Matrix.mul_one,
        Formalism.MainNotions.LeviCoordinates.rrg_P_inv_mul],
    by
      have e1 : ((γ⁻¹ : GL (Fin I.n) I.E) : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) *
          (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) = 1 := by
        rw [← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
          Matrix.map_one _ (map_zero _) (map_one _)]
      rw [rt_conj_mul _ _ _ _ (Formalism.MainNotions.LeviCoordinates.rrg_P_mul_inv I v), e1, Matrix.mul_one,
        Formalism.MainNotions.LeviCoordinates.rrg_P_inv_mul]⟩,
  by
    have hγ' : cT (starRingEnd I.E) (γ : Matrix (Fin I.n) (Fin I.n) I.E) * I.J *
        (γ : Matrix (Fin I.n) (Fin I.n) I.E) = I.J := hγ
    have hc : (cT (starRingEnd I.E) (γ : Matrix (Fin I.n) (Fin I.n) I.E)).map (I.φ v) =
        ((γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v))ᴴ := by
      ext i j
      simp only [cT, Matrix.map_apply, Matrix.transpose_apply, Matrix.conjTranspose_apply,
        starRingEnd_apply]
      exact I.cm.cmUnram.2.1 (I.φ v) _
    have hu : ((γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v))ᴴ * I.J.map (I.φ v) *
        (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) = I.J.map (I.φ v) := by
      rw [← hc, ← Matrix.map_mul, ← Matrix.map_mul, hγ']
    have hPP : ((I.P v)⁻¹)ᴴ * (I.P v)ᴴ = 1 := by
      rw [← Matrix.conjTranspose_mul, Formalism.MainNotions.LeviCoordinates.rrg_P_mul_inv, Matrix.conjTranspose_one]
    show ((I.P v)⁻¹ * (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) * I.P v)ᴴ *
        Formalism.REAL.Jm (I.ε v) * ((I.P v)⁻¹ * (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) * I.P v) =
        Formalism.REAL.Jm (I.ε v)
    rw [← I.P_spec v]
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc ((I.P v)⁻¹)ᴴ (I.P v)ᴴ, hPP, Matrix.one_mul,
      ← Matrix.mul_assoc (I.P v) (I.P v)⁻¹, Formalism.MainNotions.LeviCoordinates.rrg_P_mul_inv, Matrix.one_mul]
    congr 1
    simp only [← Matrix.mul_assoc]
    rw [hu]⟩

theorem rt_uMat (I : Formalism.MainNotions.S.AutInst) (γ : GL (Fin I.n) I.E) (hγ : γ ∈ UJ (starRingEnd I.E) I.J)
    (v : InfinitePlace I.F) :
    Formalism.MainNotions.S.uMat (rtReal I γ hγ v) =
      (I.P v)⁻¹ * (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) * I.P v := rfl

theorem frameRat : FrameRat := by
  intro I S fr Φ hΦ
  have hBiB : fr.Bi.map (rtι I) * fr.B.map (rtι I) = 1 := by
    rw [← Matrix.map_mul, fr.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]
  ext y
  rw [Subgroup.mem_map, Subgroup.mem_subgroupOf]
  constructor
  · rintro ⟨h, hh, rfl⟩
    obtain ⟨γ, rfl⟩ := MonoidHom.mem_range.1 hh
    obtain ⟨γ0, hγ0, -, hfin⟩ := (Subgroup.mem_inf.1 γ.2).1
    set z := Φ.toMonoidHom (iotaFS I S γ) with hz
    have h1 := hΦ z
    rw [hz, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply] at h1
    have h2 : I.fmat ((iotaFS I S γ : HfinS I S) : I.Gf) =
        (γ0 : Matrix (Fin I.n) (Fin I.n) I.E).map (rtι I) := hfin
    set yM : Matrix (Fin fr.k) (Fin fr.k) (rtA I) :=
      ((z : GL (Fin fr.k) (rtA I)) : Matrix (Fin fr.k) (Fin fr.k) (rtA I)) with hyM
    set M := fr.Bi * (γ0 : Matrix (Fin I.n) (Fin I.n) I.E) * fr.B with hMdef
    have hM : M.map (rtι I) =
        Matrix.fromBlocks (1 : Matrix (Fin fr.m) (Fin fr.m) (rtA I)) 0 0 yM := by
      rw [hMdef, Matrix.map_mul, Matrix.map_mul, ← h2, h1]
      unfold psiMat
      simp only [Matrix.mul_assoc]
      rw [hBiB, Matrix.mul_one, ← Matrix.mul_assoc, hBiB, Matrix.one_mul]
      rfl
    have hYm : M.toBlocks₂₂.map (rtι I) = yM := by
      have := congrArg Matrix.toBlocks₂₂ hM
      rw [Matrix.toBlocks_fromBlocks₂₂] at this
      rw [← this]
      ext i j
      rfl
    have hdet : M.toBlocks₂₂.det ≠ 0 := rt_det_ne I _ (z : GL (Fin fr.k) (rtA I)) hYm.symm
    refine Subgroup.mem_map.2 ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdet, ?_, ?_⟩
    · show cT (I.cm.sig : I.E →+* I.E) M.toBlocks₂₂ * fr.J' * M.toBlocks₂₂ = fr.J'
      rw [rt_sig_eq]
      apply rt_unitary_of
      rw [hYm]
      exact z.2
    · ext i j
      change (M.toBlocks₂₂.map (rtι I)) i j = yM i j
      rw [hYm]
  · intro hy
    obtain ⟨γ', hγ', hyγ⟩ := Subgroup.mem_map.1 hy
    set g := Φ.symm y with hg
    have h1 := hΦ y
    have hyv : ((y : GL (Fin fr.k) (rtA I)) : Matrix (Fin fr.k) (Fin fr.k) (rtA I)) =
        (γ' : Matrix (Fin fr.k) (Fin fr.k) I.E).map (rtι I) := by
      rw [← hyγ]; rfl
    set γ0m := fr.B * Matrix.fromBlocks (1 : Matrix (Fin fr.m) (Fin fr.m) I.E) 0 0
      (γ' : Matrix (Fin fr.k) (Fin fr.k) I.E) * fr.Bi with hγ0m
    have hγ0 : γ0m.map (rtι I) = I.fmat (g : I.Gf) := by
      rw [h1, hyv, hγ0m]
      unfold psiMat
      rw [Matrix.map_mul, Matrix.map_mul, Matrix.fromBlocks_map,
        Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_zero _ (map_zero _),
        Matrix.map_zero _ (map_zero _)]
    have hdet : γ0m.det ≠ 0 := rt_det_ne I _ ((g : I.Gf) : GL (Fin I.n) (rtA I)) hγ0.symm
    set γ0 := Matrix.GeneralLinearGroup.mkOfDetNeZero γ0m hdet with hγ0def
    have hγv : (γ0 : Matrix (Fin I.n) (Fin I.n) I.E) = γ0m := rfl
    have hU : γ0 ∈ UJ (starRingEnd I.E) I.J := by
      show cT (starRingEnd I.E) (γ0 : Matrix (Fin I.n) (Fin I.n) I.E) * I.J *
        (γ0 : Matrix (Fin I.n) (Fin I.n) I.E) = I.J
      rw [hγv]
      apply rt_unitary_of
      rw [hγ0]
      exact (g : I.Gf).2
    have hfix : ∀ s ∈ S, γ0m *ᵥ s = s := by
      intro s hs
      have := g.2 s hs
      rw [← hγ0] at this
      funext i
      apply rt_inj I
      exact (RingHom.map_mulVec (rtι I) γ0m s i).trans (congrFun this i)
    let x : I.GA := (fun v => rtReal I γ0 hU v, (g : I.Gf))
    have hx : x ∈ GamS I S := by
      refine Subgroup.mem_inf.2 ⟨⟨γ0, hU, fun v => rfl, ?_⟩, Subgroup.mem_prod.2 ⟨?_, g.2⟩⟩
      · show I.fmat (g : I.Gf) = _
        rw [hγv, hγ0]
      · intro v s hs
        show Formalism.MainNotions.S.uMat (rtReal I γ0 hU v) *ᵥ rv I v s = rv I v s
        rw [rt_uMat, rv, Matrix.mulVec_mulVec,
          show (I.P v)⁻¹ * (γ0 : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) * I.P v * (I.P v)⁻¹ =
            (I.P v)⁻¹ * (γ0 : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) by
            rw [Matrix.mul_assoc, Formalism.MainNotions.LeviCoordinates.rrg_P_mul_inv, Matrix.mul_one],
          ← Matrix.mulVec_mulVec]
        congr 1
        funext i
        have e := RingHom.map_mulVec (I.φ v) (γ0 : Matrix (Fin I.n) (Fin I.n) I.E) s i
        rw [hγv, hfix s hs] at e
        rw [hγv]
        exact e.symm
    exact ⟨g, MonoidHom.mem_range.2 ⟨⟨x, hx⟩, Subtype.ext rfl⟩, by simp [hg]⟩

end PI.UnitaryGroupMassFormula.InHHClassFin
