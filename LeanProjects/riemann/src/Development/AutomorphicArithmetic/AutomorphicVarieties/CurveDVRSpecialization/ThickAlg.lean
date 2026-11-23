import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.UniversalOrdinaryDeterminantRing
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DGmap
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.SelfTwistEigenvalues.UnipTorsion
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.IrreducibleSpans.Burnside

noncomputable section

open IsLocalRing Matrix Polynomial UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.W UpperTheory.V.CA

namespace UpperTheory.V.Pr.Thick

section Th

variable {n : ℕ} {A Q G : Type} [CommRing A] [CommRing Q] [Group G]

def th (f : A →+* Q) (σ : G →* Matrix (Fin n) (Fin n) Q) : MonoidAlgebra A G →+* Matrix (Fin n) (Fin n) Q :=
  (GDet.repAlg σ Q).toRingHom.comp (MonoidAlgebra.mapRingHom G f)

theorem th_apply (f : A →+* Q) (σ : G →* Matrix (Fin n) (Fin n) Q) (y : MonoidAlgebra A G) :
    th f σ y = GDet.repAlg σ Q (MonoidAlgebra.mapRingHom G f y) := rfl

@[simp] theorem th_single (f : A →+* Q) (σ : G →* Matrix (Fin n) (Fin n) Q) (g : G) (a : A) :
    th f σ (MonoidAlgebra.single g a) = f a • σ g := by
  simp [th_apply, GDet.repAlg, MonoidAlgebra.lift_single]

theorem th_map {Q' : Type} [CommRing Q'] (f : A →+* Q) (σ : G →* Matrix (Fin n) (Fin n) Q) (j : Q →+* Q')
    (y : MonoidAlgebra A G) : th (j.comp f) (j.mapMatrix.toMonoidHom.comp σ) y = (th f σ y).map j := by
  induction y using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb =>
    rw [map_add, map_add, ha, hb]
    ext i k
    simp
  | single g a => simp [th_single, Matrix.map_smul']

theorem th_comp {A' : Type} [CommRing A'] (e : A' →+* A) (f : A →+* Q) (σ : G →* Matrix (Fin n) (Fin n) Q)
    (y : MonoidAlgebra A' G) : th f σ (MonoidAlgebra.mapRingHom G e y) = th (f.comp e) σ y := by
  rw [th_apply, th_apply, ← RingHom.comp_apply, ← MonoidAlgebra.mapRingHom_comp]

theorem chi_ofRep (σ : G →* Matrix (Fin n) (Fin n) Q) (y : MonoidAlgebra Q G) :
    (GDet.ofRep σ).chi y = (GDet.repAlg σ Q y).charpoly := by
  have key : ∀ y : MonoidAlgebra Q G, GDet.repAlg σ Q[X] (MonoidAlgebra.mapRingHom G C y) = (C : Q →+* Q[X]).mapMatrix (GDet.repAlg σ Q y) := by
    intro y
    induction y using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb =>
      rw [map_add, map_add, ha, hb]
      ext i k
      simp
    | single g a =>
      ext i k
      simp [GDet.repAlg, MonoidAlgebra.lift_single]
  simp only [GDet.chi, GDet.ofRep]
  rw [Matrix.charpoly, Matrix.charmatrix]
  simp [map_sub, key]
  congr 2
  ext i k
  simp [GDet.repAlg, MonoidAlgebra.lift_single, Matrix.diagonal, Matrix.one_apply, Algebra.smul_def]

private theorem gdet_map_chi_mapRingHom {n : ℕ} {A Q G : Type} [CommRing A] [CommRing Q] [Group G]
    (D : GDet n A G) (f : A →+* Q) (y : MonoidAlgebra A G) :
    (D.map f).chi (MonoidAlgebra.mapRingHom G f y) = (D.chi y).map f := by
  letI : Algebra A Q[X] := ((algebraMap Q Q[X]).comp f).toAlgebra
  let φ : A[X] →ₐ[A] Q[X] :=
    { Polynomial.mapRingHom f with
      commutes' := fun a => by simp [RingHom.algebraMap_toAlgebra] }
  have hn := D.nat A[X] Q[X] φ (MonoidAlgebra.single 1 X - MonoidAlgebra.mapRingHom G C y)
  have e : MonoidAlgebra.mapRingHom G (φ : A[X] →+* Q[X])
      (MonoidAlgebra.single 1 X - MonoidAlgebra.mapRingHom G C y) =
      MonoidAlgebra.single 1 X - MonoidAlgebra.mapRingHom G C (MonoidAlgebra.mapRingHom G f y) := by
    rw [map_sub, MonoidAlgebra.mapRingHom_single]
    congr 1
    · congr 1
      show Polynomial.map f X = X
      simp
    · rw [← RingHom.comp_apply, ← RingHom.comp_apply, ← MonoidAlgebra.mapRingHom_comp,
        ← MonoidAlgebra.mapRingHom_comp]
      congr 2
      exact RingHom.ext fun a => by simp [φ]
  rw [e] at hn
  unfold GDet.chi GDet.map
  exact hn

theorem charpoly_th {D : GDet n A G} {f : A →+* Q} {σ : G →* Matrix (Fin n) (Fin n) Q}
    (h : D.map f = GDet.ofRep σ) (y : MonoidAlgebra A G) : (th f σ y).charpoly = (D.chi y).map f := by
  rw [th_apply, ← chi_ofRep, ← h, gdet_map_chi_mapRingHom]

theorem th_aeval (f : A →+* Q) (σ : G →* Matrix (Fin n) (Fin n) Q) (y : MonoidAlgebra A G) (p : A[X]) :
    th f σ (aeval y p) = aeval (th f σ y) (p.map f) := by
  rw [aeval_def, aeval_def, Polynomial.eval₂_map, Polynomial.hom_eval₂]
  congr 1
  refine RingHom.ext fun a => ?_
  simp [MonoidAlgebra.coe_algebraMap, th_single, Algebra.algebraMap_eq_smul_one]

private theorem th_map_coeffAddMonoidHom_eq_coeff_th {n m : ℕ} {A Q G : Type} [CommRing A] [CommRing Q] [Group G]
    (f : A →+* Q) (σ : G →* Matrix (Fin n) (Fin n) Q) (β : Fin m →₀ ℕ)
    (x : MonoidAlgebra (MvPolynomial (Fin m) A) G) (i k : Fin n) :
    th f σ (MonoidAlgebra.map (MvPolynomial.coeffAddMonoidHom β) x) i k =
      MvPolynomial.coeff β (th (MvPolynomial.map f)
        ((MvPolynomial.C : Q →+* MvPolynomial (Fin m) Q).mapMatrix.toMonoidHom.comp σ) x i k) := by
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb =>
    rw [MonoidAlgebra.map_add, map_add, map_add, Matrix.add_apply, Matrix.add_apply, ha, hb,
      MvPolynomial.coeff_add]
  | single g p =>
    simp only [MonoidAlgebra.map_single, th_single]
    simp [mul_comm (MvPolynomial.map f p), MvPolynomial.coeff_C_mul, MvPolynomial.coeff_map, mul_comm]

theorem th_CH {D : GDet n A G} {f : A →+* Q} {σ : G →* Matrix (Fin n) (Fin n) Q}
    (h : D.map f = GDet.ofRep σ) {z : MonoidAlgebra A G} (hz : z ∈ D.CH) : th f σ z = 0 := by
  obtain ⟨m, y, β, hz⟩ := hz
  set F := MvPolynomial.map (σ := Fin m) f
  set σ' := (MvPolynomial.C : Q →+* MvPolynomial (Fin m) Q).mapMatrix.toMonoidHom.comp σ
  have hD : (D.map (MvPolynomial.C : A →+* MvPolynomial (Fin m) A)).map F = GDet.ofRep σ' := by
    show D.map ((MvPolynomial.map f).comp MvPolynomial.C) = _
    rw [MvPolynomial.map_comp_C]
    show (D.map f).map MvPolynomial.C = _
    rw [h]
    rfl
  have h0 : th F σ' (aeval (GDet.gen y) ((D.map MvPolynomial.C).chi (GDet.gen y))) = 0 := by
    rw [th_aeval, ← charpoly_th hD, Matrix.aeval_self_charpoly]
  have hz' : z = MonoidAlgebra.map (MvPolynomial.coeffAddMonoidHom β)
      (aeval (GDet.gen y) ((D.map MvPolynomial.C).chi (GDet.gen y))) := by
    ext g
    simp [hz g]
  ext i k
  rw [hz', th_map_coeffAddMonoidHom_eq_coeff_th, h0]
  simp

theorem th_closure [TopologicalSpace G] [IsTopologicalGroup G] [IsLocalRing Q] [IsNoetherianRing Q] (I : Ideal A)
    (f : A →+* Q) (hf : ∀ a ∈ I, f a ∈ maximalIdeal Q) (σ : G →* Matrix (Fin n) (Fin n) Q)
    (hσ : ∀ i j, AdicCont (maximalIdeal Q) fun g => σ g i j) (S : Set (MonoidAlgebra A G))
    (hS : ∀ z ∈ S, th f σ z = 0) {y : MonoidAlgebra A G} (hy : y ∈ closureIdeal I S) : th f σ y = 0 := by
  ext i k
  have hm : maximalIdeal Q ≠ ⊤ := (maximalIdeal.isMaximal Q).ne_top
  have key : ∀ N : ℕ, th f σ y i k ∈ maximalIdeal Q ^ N := by
    intro N
    let π : Matrix (Fin n) (Fin n) Q →+* Matrix (Fin n) (Fin n) (Q ⧸ maximalIdeal Q ^ N) :=
      (Ideal.Quotient.mk (maximalIdeal Q ^ N)).mapMatrix
    let ψ : G →* Matrix (Fin n) (Fin n) (Q ⧸ maximalIdeal Q ^ N) := π.toMonoidHom.comp σ
    have hker : (ψ.ker : Set G) = ⋂ a, ⋂ b, {g | Ideal.Quotient.mk (maximalIdeal Q ^ N) (σ g a b) =
        (1 : Matrix (Fin n) (Fin n) (Q ⧸ maximalIdeal Q ^ N)) a b} := by
      ext g
      simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_iInter, Set.mem_setOf_eq]
      constructor
      · intro h a b
        rw [← h]
        rfl
      · intro h
        ext a b
        exact h a b
    have hopen : IsOpen (ψ.ker : Set G) := by
      rw [hker]
      exact isOpen_iInter_of_finite fun a => isOpen_iInter_of_finite fun b => (hσ a b N).isOpen_fiber _
    let H : OpenNormalSubgroup G :=
      { toOpenSubgroup := { toSubgroup := ψ.ker, isOpen' := hopen }, isNormal' := MonoidHom.normal_ker ψ }
    have hy' := (TwoSidedIdeal.mem_iInf _).mp ((TwoSidedIdeal.mem_iInf _).mp hy N) H
    have hle : TwoSidedIdeal.span (S ∪ {z : MonoidAlgebra A G | ∃ a ∈ I ^ N, z = MonoidAlgebra.single 1 a} ∪
        {z : MonoidAlgebra A G | ∃ h ∈ H, z = MonoidAlgebra.single h 1 - 1}) ≤ TwoSidedIdeal.ker (π.comp (th f σ)) := by
      rw [TwoSidedIdeal.span_le]
      rintro z ((hz | ⟨a, ha, rfl⟩) | ⟨h, hh, rfl⟩)
      · simp [TwoSidedIdeal.mem_ker, hS z hz]
      · have hfa : f a ∈ maximalIdeal Q ^ N := by
          have h1 : Ideal.map f (I ^ N) ≤ maximalIdeal Q ^ N := by
            rw [Ideal.map_pow]
            exact Ideal.pow_right_mono (Ideal.map_le_iff_le_comap.mpr hf) N
          exact h1 (Ideal.mem_map_of_mem f ha)
        rw [SetLike.mem_coe, TwoSidedIdeal.mem_ker]
        ext a' b'
        simp [π, th_single, Ideal.Quotient.eq_zero_iff_mem.mpr hfa]
      · have hh' : ψ h = 1 := hh
        rw [SetLike.mem_coe, TwoSidedIdeal.mem_ker, RingHom.comp_apply, map_sub, th_single, map_one, map_one,
          one_smul, map_sub, map_one]
        rw [← hh']
        simp [ψ]
    have h0 := (TwoSidedIdeal.mem_ker _).mp (hle hy')
    have h1 := congrFun (congrFun h0 i) k
    exact Ideal.Quotient.eq_zero_iff_mem.mp h1
  have := (Ideal.iInf_pow_eq_bot_of_isLocalRing (maximalIdeal Q) hm) ▸ (Submodule.mem_iInf _).mpr key
  simpa using this

end Th

section Field

variable {κ K G : Type} [Field κ] [Field K] [Group G]

theorem root_row {R : Type} [CommRing R] (M : Matrix (Fin 3) (Fin 3) R) (h0 : M 1 0 = 0) (h2 : M 1 2 = 0) :
    M.charpoly.eval (M 1 1) = 0 := by
  rw [Matrix.charpoly, Matrix.det_fin_three]
  simp [Matrix.charmatrix_apply, h0, h2]

theorem th_row {A R : Type} [CommRing A] [CommRing R] (j : A →+* R) (σ : G →* Matrix (Fin 3) (Fin 3) R)
    (hσ : ∀ g, σ g 1 0 = 0 ∧ σ g 1 2 = 0) (y : MonoidAlgebra A G) : th j σ y 1 0 = 0 ∧ th j σ y 1 2 = 0 := by
  induction y using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp [map_add, ha.1, ha.2, hb.1, hb.2]
  | single g a => simp [th_single, (hσ g).1, (hσ g).2]

def mid {E R : Type} [Ring E] [CommRing R] (τ : E →+* Matrix (Fin 3) (Fin 3) R)
    (h : ∀ y, τ y 1 0 = 0 ∧ τ y 1 2 = 0) : E →+* R where
  toFun y := τ y 1 1
  map_one' := by simp
  map_mul' a b := by simp [Matrix.mul_apply, Fin.sum_univ_three, h a]
  map_zero' := by simp
  map_add' a b := by simp

private theorem repAlg_surjective_of_matIrr_fin_three {κ G : Type} [Field κ] [IsAlgClosed κ] [Group G]
    (ρ : G →* Matrix (Fin 3) (Fin 3) κ) (h : MatIrr ⊤ ρ) : Function.Surjective (GDet.repAlg ρ κ) := by
  classical
  let α : MonoidAlgebra κ G →ₐ[κ] Module.End κ (Fin 3 → κ) :=
    (Matrix.toLinAlgEquiv' : Matrix (Fin 3) (Fin 3) κ ≃ₐ[κ] _).toAlgHom.comp (GDet.repAlg ρ κ)
  letI : Module (MonoidAlgebra κ G) (Fin 3 → κ) := Module.compHom (Fin 3 → κ) α.toRingHom
  have hsm : ∀ (r : MonoidAlgebra κ G) (v : Fin 3 → κ), r • v = GDet.repAlg ρ κ r *ᵥ v :=
    fun r v => rfl
  haveI : IsScalarTower κ (MonoidAlgebra κ G) (Fin 3 → κ) := by
    refine ⟨fun c r v => ?_⟩
    simp only [hsm, map_smul, Matrix.smul_mulVec]
  haveI : Nontrivial (Submodule (MonoidAlgebra κ G) (Fin 3 → κ)) := by
    refine ⟨⟨⊥, ⊤, ?_⟩⟩
    intro he
    have hm : (Pi.single 0 1 : Fin 3 → κ) ∈ (⊥ : Submodule (MonoidAlgebra κ G) (Fin 3 → κ)) :=
      he ▸ Submodule.mem_top
    simp at hm
  haveI : IsSimpleModule (MonoidAlgebra κ G) (Fin 3 → κ) := by
    refine { eq_bot_or_eq_top := fun N => ?_ }
    have hN := h (N.restrictScalars κ) (fun g _ v hv => by
      have hv' : (MonoidAlgebra.single g (1 : κ)) • v ∈ N := N.smul_mem _ hv
      simpa [hsm, GDet.repAlg, MonoidAlgebra.lift_single] using hv')
    rcases hN with hN | hN
    · left
      apply Submodule.restrictScalars_injective κ
      simpa using hN
    · right
      apply Submodule.restrictScalars_injective κ
      simpa using hN
  have hschur :=
    IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed (A := MonoidAlgebra κ G) (V := Fin 3 → κ) κ
  intro M
  let f : Module.End (Module.End (MonoidAlgebra κ G) (Fin 3 → κ)) (Fin 3 → κ) :=
    { toFun := fun v => M *ᵥ v
      map_add' := fun v w => Matrix.mulVec_add _ _ _
      map_smul' := fun e v => by
        obtain ⟨c, rfl⟩ := hschur.2 e
        simp [Module.End.smul_def, Module.algebraMap_end_apply, Matrix.mulVec_smul] }
  obtain ⟨r, hr⟩ := jacobson_density f (Finset.univ.image fun i : Fin 3 => (Pi.single i 1 : Fin 3 → κ))
  refine ⟨r, ?_⟩
  ext a b
  have hb := congrFun (hr (Pi.single b 1) (by simp)) a
  simpa [f, hsm] using hb.symm

theorem not_irr [IsAlgClosed κ] (j : κ →+* K) (σ : G →* Matrix (Fin 3) (Fin 3) K)
    (hσ : ∀ g, σ g 1 0 = 0 ∧ σ g 1 2 = 0) (ρ : G →* Matrix (Fin 3) (Fin 3) κ)
    (h : (GDet.ofRep ρ).map j = GDet.ofRep σ) : ¬ MatIrr ⊤ ρ := by
  intro hirr
  have hsurj := repAlg_surjective_of_matIrr_fin_three ρ hirr
  have hrow := th_row j σ hσ
  let ψ := mid (th j σ) hrow
  have L : ∀ y, GDet.repAlg ρ κ y = 0 → ψ y = 0 := by
    intro y hy
    have h1 := charpoly_th h y
    rw [chi_ofRep, hy, Matrix.charpoly_zero] at h1
    have h2 := root_row (th j σ y) (hrow y).1 (hrow y).2
    rw [h1] at h2
    show th j σ y 1 1 = 0
    simpa using h2
  choose e he using fun a b : Fin 3 => hsurj (Matrix.single a b (1 : κ))
  have hsq : ∀ a b, a ≠ b → ψ (e a b) = 0 := by
    intro a b hab
    have h3 := L (e a b * e a b) (by
      rw [map_mul, he]
      exact Matrix.single_mul_single_of_ne (1 : κ) a b a hab.symm 1)
    rw [map_mul] at h3
    exact mul_self_eq_zero.mp h3
  have hd : ∀ a b, ψ (e a a) = ψ (e a b) * ψ (e b a) := by
    intro a b
    have h3 := L (e a a - e a b * e b a) (by rw [map_sub, map_mul, he, he, he]; simp)
    rw [map_sub, map_mul, sub_eq_zero] at h3
    exact h3
  have h1 := L (1 - (e 0 0 + e 1 1 + e 2 2)) (by
    rw [map_sub, map_add, map_add, he, he, he, map_one]
    ext i k
    fin_cases i <;> fin_cases k <;> simp [Matrix.single_apply, Matrix.one_apply])
  rw [map_sub, map_one, map_add, map_add, hd 0 1, hd 1 2, hd 2 0, hsq 0 1 (by decide),
    hsq 1 2 (by decide), hsq 2 0 (by decide)] at h1
  simp at h1

theorem split_of_ss [IsAlgClosed κ] (j : κ →+* K) (σ : G →* Matrix (Fin 3) (Fin 3) K)
    (hσ : ∀ g, σ g 1 0 = 0 ∧ σ g 1 2 = 0) (D : GDet 3 κ G) (h : D.map j = GDet.ofRep σ)
    (I : TwoSidedIdeal (MonoidAlgebra κ G)) (hI : ∀ y ∈ I, th j σ y = 0)
    (hss : IsSemisimpleRing I.ringCon.Quotient) :
    ∃ y : Fin 3 → K, y 1 = 1 ∧ ∀ g, σ g *ᵥ y = σ g 1 1 • y := by
  have hrow : ∀ g, ∃ a, j a = σ g 1 1 := by
    intro g
    have hc := charpoly_th h (MonoidAlgebra.single g 1)
    rw [th_single, map_one, one_smul] at hc
    have hr := root_row (σ g) (hσ g).1 (hσ g).2
    rw [hc] at hr
    have hne : (D.chi (MonoidAlgebra.single g 1)).map j ≠ 0 := by
      rw [← hc]
      exact (Matrix.charpoly_monic _).ne_zero
    have hmem : σ g 1 1 ∈ ((D.chi (MonoidAlgebra.single g 1)).map j).roots :=
      (Polynomial.mem_roots hne).mpr hr
    rw [(IsAlgClosed.splits _).roots_map_of_ne_zero hne, Multiset.mem_map] at hmem
    obtain ⟨a, -, ha⟩ := hmem
    exact ⟨a, ha⟩
  have hker : I.ringCon ≤ RingCon.ker (th j σ) := by
    intro x y hxy
    rw [TwoSidedIdeal.rel_iff] at hxy
    have := hI _ hxy
    rw [map_sub, sub_eq_zero] at this
    exact this
  let τ : I.ringCon.Quotient →+* Matrix (Fin 3) (Fin 3) K := I.ringCon.lift (th j σ) hker
  let ψ : I.ringCon.Quotient →+* Module.End K (Fin 3 → K) :=
    (Matrix.toLinAlgEquiv' : Matrix (Fin 3) (Fin 3) K ≃ₐ[K] _).toRingEquiv.toRingHom.comp τ
  letI : Module I.ringCon.Quotient (Fin 3 → K) := Module.compHom (Fin 3 → K) ψ
  have hsmul : ∀ (y : MonoidAlgebra κ G) (v : Fin 3 → K),
      (I.ringCon.mk' y) • v = th j σ y *ᵥ v := by
    intro y v
    show ψ (I.ringCon.mk' y) v = _
    simp [ψ, τ, RingCon.lift_mk']
  let W : Submodule I.ringCon.Quotient (Fin 3 → K) :=
    { carrier := {v | v 1 = 0}
      add_mem' := by
        intro a b ha hb
        simp_all
      zero_mem' := by simp
      smul_mem' := by
        intro r v hv
        obtain ⟨y, rfl⟩ := RingCon.mk'_surjective _ r
        simp only [Set.mem_setOf_eq] at hv ⊢
        rw [hsmul, Matrix.mulVec, dotProduct, Fin.sum_univ_three, (th_row j σ hσ y).1,
          (th_row j σ hσ y).2, hv]
        simp }
  obtain ⟨C, hWC⟩ := exists_isCompl W
  have he : (Pi.single 1 1 : Fin 3 → K) ∈ W ⊔ C := by
    rw [hWC.sup_eq_top]
    trivial
  obtain ⟨w, hw, c, hcC, hwc⟩ := Submodule.mem_sup.mp he
  have hw1 : w 1 = 0 := hw
  have hc1 : c 1 = 1 := by
    have := congr_fun hwc 1
    simp only [Pi.add_apply, hw1, zero_add, Pi.single_eq_same] at this
    exact this
  refine ⟨c, hc1, fun g => ?_⟩
  obtain ⟨a, ha⟩ := hrow g
  have h1 : (I.ringCon.mk' (MonoidAlgebra.single g 1)) • c -
      (I.ringCon.mk' (MonoidAlgebra.single 1 a)) • c ∈ W ⊓ C := by
    refine ⟨?_, C.sub_mem (C.smul_mem _ hcC) (C.smul_mem _ hcC)⟩
    show (_ : Fin 3 → K) 1 = 0
    rw [hsmul, hsmul, th_single, th_single]
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, (hσ g).1, (hσ g).2, hc1, ha]
  rw [hWC.inf_eq_bot, Submodule.mem_bot, hsmul, hsmul, th_single, th_single, sub_eq_zero] at h1
  simp [ha] at h1
  rw [h1]
  ext i
  simp [Matrix.mulVec, dotProduct, Matrix.one_apply]

end Field

section Unip

variable {l : ℕ} [Fact l.Prime] {G : GFrame l} {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] {n : ℕ}
  {r : Resid G O n} (B : UniversalOrdinaryDeterminantRing r) {Q : Type} [CommRing Q] [IsLocalRing Q]

set_option maxHeartbeats 400000 in
theorem chi_res {u : G.St} {g : G.G₀} (hg : g ∈ r.Ip u) (f : B.B →+* Q)
    (hf : ∀ a ∈ maximalIdeal B.B, f a ∈ maximalIdeal Q) :
    ((B.u.D.chi (MonoidAlgebra.single g 1)).map f).map (residue Q) = (X - 1) ^ n := by
  haveI : IsLocalHom f := ⟨fun a ha => by
    by_contra hna
    exact (IsLocalRing.mem_maximalIdeal _).mp (hf a ((IsLocalRing.mem_maximalIdeal _).mpr hna)) ha⟩
  have hcomp : (residue Q).comp f = ((ResidueField.map f).comp (ResidueField.map (algebraMap O B.B))).comp
      (res O B.B : B.B →+* ResidueField O) := by
    ext x
    simp only [res, RingHom.coe_comp, Function.comp_apply]
    simp only [AlgHom.coe_ringHom_mk, RingHom.coe_mk, RingEquiv.toRingHom_eq_coe, RingHom.coe_comp,
      RingEquiv.coe_toRingHom, Function.comp_apply]
    rw [← ResidueField.map_residue]
    congr 1
    symm
    generalize_proofs at *
    rename_i hb
    exact (RingEquiv.ofBijective (ResidueField.map (algebraMap O B.B)) hb).apply_symm_apply ((residue B.B) x)
  have hg1 : ∀ i, r.chib i g = 1 := by
    intro i
    have := (Subgroup.mem_inf.mp hg).2
    exact (Subgroup.mem_iInf.mp this i)
  rw [Polynomial.map_map, hcomp, ← Polynomial.map_map, ← gdet_map_chi_mapRingHom, B.u.red, Resid.Dbar,
    MonoidAlgebra.mapRingHom_single, map_one, chi_ofRep]
  have hM : GDet.repAlg (diagRep r.chib) (ResidueField O) (MonoidAlgebra.single g 1) = 1 := by
    ext i k
    simp [GDet.repAlg, MonoidAlgebra.lift_single, diagRep, hg1]
  rw [hM, Matrix.charpoly_one]
  simp

theorem charpoly_star {f : B.B →+* Q} {σ : G.G₀ →* Matrix (Fin n) (Fin n) Q} (h : B.u.D.map f = GDet.ofRep σ)
    (g : G.G₀) : (th f σ (G.star O B.B n (MonoidAlgebra.single g 1))).charpoly =
      (th f σ (MonoidAlgebra.single g 1)).charpoly := by
  ext k
  by_cases hk : k ≤ n
  · rw [charpoly_th h, charpoly_th h, coeff_map, coeff_map]
    congr 1
    have hP := B.u.P (n - k) g
    simp only [GDet.lam, Nat.sub_sub_self hk] at hP
    have := congrArg (fun t => (-1 : B.B) ^ (n - k) * t) hP
    simpa [← mul_assoc, ← mul_pow] using this
  · push_neg at hk
    have hd : ∀ M : Matrix (Fin n) (Fin n) Q, M.charpoly.coeff k = 0 := by
      intro M
      apply Polynomial.coeff_eq_zero_of_natDegree_lt
      rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
      exact hk
    rw [hd, hd]

theorem th_Ip {u : G.St} {g : G.G₀} (hg : g ∈ r.Ip u) {f : B.B →+* Q}
    (hf : ∀ a ∈ maximalIdeal B.B, f a ∈ maximalIdeal Q) {σ : G.G₀ →* Matrix (Fin n) (Fin n) Q}
    (h : B.u.D.map f = GDet.ofRep σ) {m : ℕ} (hm : IsUnit (m : Q)) (y : MonoidAlgebra B.B G.G₀)
    (hy : y = MonoidAlgebra.single g 1 ∨ y = G.star O B.B n (MonoidAlgebra.single g 1)) (h1 : th f σ y ^ m = 1) :
    th f σ (y - 1) = 0 := by
  have hchar : (th f σ y).charpoly.map (residue Q) = (X - 1) ^ n := by
    rcases hy with rfl | rfl
    · rw [charpoly_th h]
      exact chi_res B hg f hf
    · rw [charpoly_star B h, charpoly_th h]
      exact chi_res B hg f hf
  rw [map_sub, map_one]
  set M := th f σ y with hM
  set π := residue Q
  set x := π.mapMatrix M with hx
  have hnil : IsNilpotent (x - 1) := by
    refine ⟨n, ?_⟩
    have := Matrix.aeval_self_charpoly x
    rw [hx, RingHom.mapMatrix_apply, Matrix.charpoly_map, hchar] at this
    simpa [hx, RingHom.mapMatrix_apply] using this
  set p : Polynomial (ResidueField Q) := ∑ i ∈ Finset.range m, X ^ i
  have hroot : (p - C (p.eval 1)).IsRoot 1 := by simp
  have hq := (Polynomial.mul_divByMonic_eq_iff_isRoot (p := p - C (p.eval 1)) (a := 1)).mpr hroot
  have hsum : π.mapMatrix (∑ i ∈ Finset.range m, M ^ i) =
      algebraMap (ResidueField Q) _ (p.eval 1) + (x - 1) * aeval x ((p - C (p.eval 1)) /ₘ (X - C 1)) := by
    have e := congrArg (aeval x) hq
    rw [map_mul, map_sub, aeval_C, aeval_X, map_one] at e
    rw [e, map_sub, aeval_C, add_sub_cancel, map_sum, map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [map_pow, aeval_X_pow]
  have hunit : IsUnit (∑ i ∈ Finset.range m, M ^ i) := by
    rw [Matrix.isUnit_iff_isUnit_det, ← IsLocalRing.residue_ne_zero_iff_isUnit, RingHom.map_det]
    refine ((Matrix.isUnit_iff_isUnit_det _).mp ?_).ne_zero
    rw [hsum]
    refine IsNilpotent.isUnit_add_left_of_commute ?_ ?_ ?_
    · refine Commute.isNilpotent_mul_right ?_ hnil
      have hc := (Commute.all (X - C 1 : Polynomial (ResidueField Q))
        ((p - C (p.eval 1)) /ₘ (X - C 1))).map (aeval x)
      simpa using hc
    · have : p.eval 1 = (m : ResidueField Q) := by simp [p]
      rw [this]
      have hmu : IsUnit (π (m : Q)) := hm.map π
      rw [map_natCast] at hmu
      exact hmu.map _
    · exact (Algebra.commute_algebraMap_left _ _).symm
  have hs : (M - 1) * ∑ i ∈ Finset.range m, M ^ i = 0 := by
    rw [mul_geom_sum, h1, sub_self]
  exact (hunit.mul_left_eq_zero).mp hs

end Unip

theorem star_single {l : ℕ} [Fact l.Prime] (G : GFrame l) (O : Type) [CommRing O] [Algebra ℤ_[l] O] (R : Type)
    [CommRing R] [Algebra O R] (n : ℕ) (g : G.G₀) (a : R) :
    G.star O R n (MonoidAlgebra.single g a) =
      MonoidAlgebra.single (G.conj g)⁻¹ (a * ((G.eps O R g ^ (1 - (n : ℤ)) : Rˣ) : R)) := by
  simp [GFrame.star, GFrame.starOp]

theorem local_of_finite {B R : Type} [CommRing B] [IsLocalRing B] [CommRing R] [IsLocalRing R]
    [Finite (ResidueField R)] (f : B →+* R) : ∀ a ∈ maximalIdeal B, f a ∈ maximalIdeal R := by
  classical
  intro a ha
  by_contra hfa
  letI := Fintype.ofFinite (ResidueField R)
  have hne : residue R (f a) ≠ 0 := by
    rwa [Ne, IsLocalRing.residue_eq_zero_iff]
  have hq := FiniteField.pow_card_sub_one_eq_one _ hne
  have hpos : 0 < Fintype.card (ResidueField R) - 1 := by
    have := Fintype.one_lt_card (α := ResidueField R)
    omega
  have hu : IsUnit (1 - a ^ (Fintype.card (ResidueField R) - 1)) := by
    apply IsLocalRing.isUnit_one_sub_self_of_mem_nonunits
    exact (IsLocalRing.mem_maximalIdeal _).mp (Ideal.pow_mem_of_mem _ ha _ hpos)
  have := hu.map ((residue R).comp f)
  simp [map_sub, map_pow, hq] at this

end UpperTheory.V.Pr.Thick

end
