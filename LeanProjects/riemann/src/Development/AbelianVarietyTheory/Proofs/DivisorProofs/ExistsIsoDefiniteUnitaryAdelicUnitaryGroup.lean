import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStableComplBot
import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.QuotientMeasureEqChosenProbability
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnramifiedOfIsCMUnram
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFinsetDefiniteUnitaryDoubleCosets
import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.OrthonormalBaseFrameNeg

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Formalism.L2.Theta
open Formalism.IndefR.Mult Formalism.UG GlobalTheory.SphPar GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefTransfer
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DefTransfer.Glob

section Abstract

variable {R S : Type} [CommRing R] [CommRing S] {n : ℕ}

theorem conj_mem_iff (s : S →+* S) (J : Matrix (Fin n) (Fin n) S) (N : GL (Fin n) S)
    (hN : cT s N.val * J * N.val = 1) (y : GL (Fin n) S) : N * y * N⁻¹ ∈ UJ s J ↔ y ∈ UJ s 1 := by
  change cT s (N * y * N⁻¹).val * J * (N * y * N⁻¹).val = J ↔ cT s y.val * 1 * y.val = 1
  have e : ∀ g : GL (Fin n) S, cT s g.val * J * g.val = cT s (N⁻¹ * g).val * 1 * (N⁻¹ * g).val := fun g => by
    rw [← hN]
    calc _ = cT s (N * (N⁻¹ * g)).val * J * (N * (N⁻¹ * g)).val := by rw [mul_inv_cancel_left]
      _ = _ := by simp only [Units.val_mul N, cT_mul, Matrix.mul_assoc]
  have hJ : J = cT s (N⁻¹).val * (N⁻¹).val := by
    have := e 1
    simpa [cT] using this
  have hu : cT s N.val * cT s (N⁻¹).val = 1 := by
    rw [← cT_mul, Units.inv_mul]; simp [cT]
  rw [e, mul_assoc N, inv_mul_cancel_left, Units.val_mul, cT_mul]
  constructor
  · intro h
    have := congrArg (fun X => cT s N.val * X * N.val) h
    simp only [hN, ← Matrix.mul_assoc, hu] at this
    simpa [Matrix.mul_assoc] using this
  · intro h
    rw [hJ]
    calc _ = cT s (N⁻¹).val * (cT s y.val * 1 * y.val) * (N⁻¹).val := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [h, Matrix.mul_one]

theorem map_mem_iff (ψ : R ≃+* S) (c : R →+* R) (s : S →+* S) (h : ∀ a, ψ (c a) = s (ψ a)) (x : GL (Fin n) R) :
    bc ψ.toRingHom x ∈ UJ s 1 ↔ x ∈ UJ c 1 := by
  change cT s (x.val.map ψ) * 1 * x.val.map ψ = 1 ↔ cT c x.val * 1 * x.val = 1
  have e : cT s (x.val.map ψ) = (cT c x.val).map ψ := by ext i j; exact (h _).symm
  rw [e, Matrix.mul_one, Matrix.mul_one, ← (ψ.mapMatrix (m := Fin n)).injective.eq_iff (a := cT c x.val * x.val), map_mul, map_one]
  rfl

variable [TopologicalSpace R] [TopologicalSpace S] [IsTopologicalRing S]

theorem exists_equiv (ψ : R ≃+* S) (h1 : Continuous ψ) (h2 : Continuous ψ.symm) (c : R →+* R) (s : S →+* S)
    (h : ∀ a, ψ (c a) = s (ψ a)) (J : Matrix (Fin n) (Fin n) S) (N : GL (Fin n) S)
    (hN : cT s N.val * J * N.val = 1) :
    ∃ j : UJ c (1 : Matrix (Fin n) (Fin n) R) ≃ₜ* UJ s J, ∀ x, (j x).1 = N * bc ψ.toRingHom x.1 * N⁻¹ := by
  have l1 : ∀ x : GL (Fin n) R, bc ψ.symm.toRingHom (bc ψ.toRingHom x) = x := fun x =>
    Units.ext (Matrix.ext fun i j => ψ.symm_apply_apply _)
  have l2 : ∀ x : GL (Fin n) S, bc ψ.toRingHom (bc ψ.symm.toRingHom x) = x := fun x =>
    Units.ext (Matrix.ext fun i j => ψ.apply_symm_apply _)
  have c1 : Continuous (bc (n := Fin n) ψ.toRingHom) := GlobalTheory.AutQuotCompare.continuous_map h1
  have c2 : Continuous (bc (n := Fin n) ψ.symm.toRingHom) := GlobalTheory.AutQuotCompare.continuous_map h2
  refine ⟨{ toFun := fun x => ⟨N * bc ψ.toRingHom x.1 * N⁻¹, (conj_mem_iff s J N hN _).2 ((map_mem_iff ψ c s h _).2 x.2)⟩
            invFun := fun y => ⟨bc ψ.symm.toRingHom (N⁻¹ * y.1 * N), (map_mem_iff ψ c s h _).1 (by
              rw [l2, ← conj_mem_iff s J N hN]
              convert y.2 using 1
              group)⟩
            left_inv := fun x => Subtype.ext (by
              change bc ψ.symm.toRingHom (N⁻¹ * (N * bc ψ.toRingHom x.1 * N⁻¹) * N) = x.1
              rw [← l1 x.1, l2]; congr 1; group)
            right_inv := fun y => Subtype.ext (by
              change N * bc ψ.toRingHom (bc ψ.symm.toRingHom (N⁻¹ * y.1 * N)) * N⁻¹ = y.1
              rw [l2]; group)
            map_mul' := fun x y => Subtype.ext (by
              change N * bc ψ.toRingHom (x.1 * y.1) * N⁻¹ = N * bc ψ.toRingHom x.1 * N⁻¹ * (N * bc ψ.toRingHom y.1 * N⁻¹)
              rw [map_mul]; group)
            continuous_toFun := Continuous.subtype_mk
              ((continuous_const.mul (c1.comp continuous_subtype_val)).mul continuous_const) _
            continuous_invFun := Continuous.subtype_mk
              (c2.comp ((continuous_const.mul continuous_subtype_val).mul continuous_const)) _ }, fun x => rfl⟩

end Abstract

section Ring

variable (E : Type) [Field E] [NumberField E] [IsCMField E]

local notation "F₀" => maximalRealSubfield E

theorem exists_ring : ∃ (ψ : Ad E ≃+* AF F₀ ⊗[F₀] E) (Θ : Ainf F₀ ⊗[F₀] E ≃+* Cinf E),
    Continuous ψ ∧ Continuous ψ.symm ∧ (∀ x : E, ψ (algebraMap E (Ad E) x) = inclR (AF F₀) x) ∧
    (∀ a, ψ (conjAd E a) = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F₀) (IsCMField.complexConj E : E →ₐ[F₀] E) (ψ a)) ∧
    (∀ a, Algebra.TensorProduct.map (sndA F₀) (AlgHom.id F₀ E) (ψ a) = (GlobalTheory.LFun.finAdEquiv F₀ E).symm (pFin E a)) ∧
    (∀ a, Algebra.TensorProduct.map (fstA F₀) (AlgHom.id F₀ E) (ψ a) = Θ.symm (pInf E a)) ∧
    ∀ τ θ, IsInfEmb τ θ → ∀ z, θ z = coord τ (Θ z) := by
  obtain ⟨Θ, h1, h2, h3, h4⟩ := GlobalTheory.AutQuotCompare.exists_inf_equiv E
  obtain ⟨e, he, h5, h6⟩ := GlobalTheory.AdSplit.exists_adele_equiv F₀ E
  let p : Ad E ≃+* (Ainf F₀ ⊗[F₀] E) × (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F₀ ⊗[F₀] E) :=
    RingEquiv.prodCongr ((infEq E).symm.trans Θ.symm) (GlobalTheory.LFun.finAdEquiv F₀ E).symm
  have ci : Continuous (infEq E).symm := continuous_pi fun w =>
    (InfinitePlace.Completion.isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).continuous.comp
      (continuous_apply w)
  have hp : Continuous p := (h2.comp ci).prodMap GlobalTheory.LFun.continuous_finAdEquiv_symm
  have hp' : Continuous p.symm :=
    ((continuous_infEq E).comp h1).prodMap (GlobalTheory.UnitaryBC.ClassTransport.continuous_finAdEquiv F₀ E)
  have hf : ∀ a, Algebra.TensorProduct.map (sndA F₀) (AlgHom.id F₀ E) (e.symm (p a)) =
      (GlobalTheory.LFun.finAdEquiv F₀ E).symm (pFin E a) := fun a =>
    (he _).2.symm.trans (congrArg Prod.snd (e.apply_symm_apply (p a)))
  have hi : ∀ a, Algebra.TensorProduct.map (fstA F₀) (AlgHom.id F₀ E) (e.symm (p a)) = Θ.symm (pInf E a) := fun a =>
    (he _).1.symm.trans (congrArg Prod.fst (e.apply_symm_apply (p a)))
  have hext : ∀ y z : AF F₀ ⊗[F₀] E,
      Algebra.TensorProduct.map (fstA F₀) (AlgHom.id F₀ E) y = Algebra.TensorProduct.map (fstA F₀) (AlgHom.id F₀ E) z →
      Algebra.TensorProduct.map (sndA F₀) (AlgHom.id F₀ E) y = Algebra.TensorProduct.map (sndA F₀) (AlgHom.id F₀ E) z →
      y = z := fun y z a b =>
    e.injective (Prod.ext ((he y).1.trans (a.trans (he z).1.symm)) ((he y).2.trans (b.trans (he z).2.symm)))
  have hsg : ∀ {B : Type} [CommRing B] [Algebra F₀ B] (q : AF F₀ →ₐ[F₀] B) (z : AF F₀ ⊗[F₀] E),
      Algebra.TensorProduct.map q (AlgHom.id _ E)
          (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F₀) (IsCMField.complexConj E : E →ₐ[F₀] E) z) =
        Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR B (IsCMField.complexConj E : E →ₐ[F₀] E)
          (Algebra.TensorProduct.map q (AlgHom.id _ E) z) := by
    intro B _ _ q z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a x => rfl
    | add x y h1 h2 => simp only [map_add, h1, h2]
  refine ⟨p.trans e.symm, Θ, h6.comp hp, hp'.comp h5, fun x => hext _ _ ?_ ?_, fun a => hext _ _ ?_ ?_, hf, hi,
    fun τ θ hθ z => ?_⟩
  · refine (hi _).trans (Θ.symm_apply_eq.2 (funext fun w => ?_))
    exact (pInf_algebraMap x w).trans (h3 x w).symm
  · refine (hf _).trans ((GlobalTheory.LFun.finAdEquiv F₀ E).symm_apply_eq.2 ?_)
    refine Eq.trans ?_ (GlobalTheory.LFun.toFinAd_tmul (F := F₀) 1 x).symm
    rw [map_one, one_mul]
    rfl
  · rw [hsg]
    refine (hi _).trans (Θ.symm_apply_eq.2 (funext fun w => ?_))
    refine Eq.trans ?_ (h4 _ w).symm
    rw [RingEquiv.trans_apply, hi, RingEquiv.apply_symm_apply]
    exact congrFun ((infEq E).symm_apply_apply _) w
  · rw [hsg]
    refine (hf _).trans ((GlobalTheory.LFun.finAdEquiv F₀ E).symm_apply_eq.2 ?_)
    rw [RingEquiv.trans_apply, hf]
    refine Eq.trans ?_ (GlobalTheory.UnitaryBC.ClassTransport.finAdEquiv_sigR _).symm
    rw [RingEquiv.apply_symm_apply]
    rfl
  · have : IsModuleTopology (Ainf F₀) (Ainf F₀ ⊗[F₀] E) := ⟨rfl⟩
    have hl : Continuous fun a : Ainf F₀ => a ⊗ₜ[F₀] (1 : E) := by
      have := IsModuleTopology.toContinuousSMul (R := Ainf F₀) (A := Ainf F₀ ⊗[F₀] E)
      refine (continuous_id.smul (continuous_const (y := (1 : Ainf F₀) ⊗ₜ (1 : E)))).congr fun a => ?_
      simp [TensorProduct.smul_tmul']
    have hc : Continuous (coord τ) := by
      unfold coord
      split_ifs
      · exact continuous_apply _
      · exact Complex.continuous_conj.comp (continuous_apply _)
    have := GlobalTheory.LettersCheck.isInfEmb_unique τ θ ((coord τ).comp Θ.toRingHom) hθ
      ⟨fun x => by
        refine Eq.trans (congrArg (coord τ) (funext fun w => ?_)) (coord_algebraMap τ x)
        exact (h3 x w).trans (pInf_algebraMap x w).symm, hc.comp (h1.comp hl)⟩
    rw [this]; rfl

end Ring

section Group

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

local notation "F₀" => maximalRealSubfield E
local notation "σ₀" => (IsCMField.complexConj E : E →ₐ[maximalRealSubfield E] E)

theorem conj_eq_one_iff {G : Type} [Group G] (a x : G) : a * x * a⁻¹ = 1 ↔ x = 1 := by
  rw [mul_inv_eq_one, mul_eq_left]

theorem bc_eq_one_iff {R S : Type} [CommRing R] [CommRing S] (φ : R ≃+* S) (x : GL (Fin n) R) :
    bc φ.toRingHom x = 1 ↔ x = 1 := by
  refine ⟨fun h => Units.ext ((φ.mapMatrix (m := Fin n)).injective ?_), fun h => by rw [h, map_one]⟩
  rw [Units.val_one, map_one]
  exact congrArg Units.val h

theorem exists_group (J : Matrix (Fin n) (Fin n) E) (M : GL (Fin n) E) (hM : cT (σ₀ : E →+* E) M.val * J * M.val = 1) :
    ∃ j : UA E n ≃ₜ* HA (AF F₀) σ₀ J,
      (∀ x, x ∈ ratU E n ↔ j x ∈ HFinIn (AF F₀) σ₀ J) ∧
      (∀ x, x ∈ finU E n ↔
        bc (Algebra.TensorProduct.map (fstA F₀) (AlgHom.id F₀ E)).toRingHom (HA.mat (AF F₀) σ₀ J (j x)) = 1) ∧
      (∀ x, x ∈ infU E n ↔
        bc (Algebra.TensorProduct.map (sndA F₀) (AlgHom.id F₀ E)).toRingHom (HA.mat (AF F₀) σ₀ J (j x)) = 1) ∧
      (∀ τ θ, IsInfEmb τ θ → ∀ x, infMat σ₀ J θ (j x) =
        (bc τ M).val * (cEmb τ x : Matrix (Fin n) (Fin n) ℂ) * (bc τ M).val⁻¹) ∧
      ∀ x, finMat σ₀ J (j x) =
        M.val.map (Algebra.TensorProduct.includeRight : E →ₐ[F₀] Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F₀ ⊗[F₀] E) *
        ((x : GL (Fin n) (Ad E)) : Matrix (Fin n) (Fin n) (Ad E)).map
          (fun a => (GlobalTheory.LFun.finAdEquiv F₀ E).symm (pFin E a)) *
        M.val⁻¹.map (Algebra.TensorProduct.includeRight : E →ₐ[F₀] Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F₀ ⊗[F₀] E) := by
  obtain ⟨ψ, Θ, h1, h2, h3, h4, h5, h6, h7⟩ := exists_ring E
  have : IsModuleTopology (AF F₀) (AF F₀ ⊗[F₀] E) := ⟨rfl⟩
  have : IsTopologicalRing (AF F₀ ⊗[F₀] E) := IsModuleTopology.isTopologicalRing (AF F₀) _
  have hN : cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F₀) σ₀) (bc (inclR (AF F₀)) M).val * JR (AF F₀) J *
      (bc (inclR (F := F₀) (AF F₀)) M).val = 1 := by
    have := congrArg (inclR (F := F₀) (AF F₀)).mapMatrix hM
    rw [map_mul, map_mul, map_one] at this
    exact this
  obtain ⟨j, hj⟩ := exists_equiv ψ h1 h2 (conjAd E) _ h4 _ _ hN
  let qi := (Algebra.TensorProduct.map (fstA F₀) (AlgHom.id F₀ E)).toRingHom
  let qf := (Algebra.TensorProduct.map (sndA F₀) (AlgHom.id F₀ E)).toRingHom
  have ei : ∀ x : UA E n, bc qi (bc ψ.toRingHom x.1) = bc Θ.symm.toRingHom (cInf x) := fun x =>
    Units.ext (Matrix.ext fun a b => h6 _)
  have ef : ∀ x : UA E n, bc qf (bc ψ.toRingHom x.1) =
      bc (GlobalTheory.LFun.finAdEquiv F₀ E).symm.toRingHom (Matrix.GeneralLinearGroup.map (pFin E) x.1) := fun x =>
    Units.ext (Matrix.ext fun a b => h5 _)
  have er : ∀ γ : GL (Fin n) E, bc ψ.toRingHom (ratGL E n γ) = bc (inclR (AF F₀)) γ := fun γ =>
    Units.ext (Matrix.ext fun a b => h3 _)
  refine ⟨j, fun x => ⟨?_, ?_⟩, fun x => ?_, fun x => ?_, fun τ θ hθ x => ?_, fun x => ?_⟩
  · rintro ⟨γ, hγ⟩
    refine ⟨M * γ * M⁻¹, (conj_mem_iff _ J M hM γ).2 ?_, ?_⟩
    · have hx : cT (conjAd E) (ratGL E n γ).val * 1 * (ratGL E n γ).val = 1 := hγ ▸ x.2
      change cT (σ₀ : E →+* E) γ.val * 1 * γ.val = 1
      have hinj : Function.Injective (algebraMap E (Ad E)) := AdeleRing.algebraMap_injective (𝓞 E) E
      refine Matrix.map_injective hinj ?_
      change (algebraMap E (Ad E)).mapMatrix _ = (algebraMap E (Ad E)).mapMatrix _
      rw [map_mul, map_mul, map_one]
      refine Eq.trans ?_ hx
      congr 2
      ext a b
      exact (conjAd_algebraMap _).symm
    · refine Eq.trans ?_ (hj x).symm
      have hγ' : ratGL E n γ = x.1 := hγ
      rw [map_mul, map_mul, map_inv, ← hγ', er]
  · rintro ⟨γ, -, hγ⟩
    refine ⟨M⁻¹ * γ * M, ?_⟩
    have h := hγ.trans (hj x)
    change _ = x.1
    rw [← mul_inv_eq_one, ← bc_eq_one_iff ψ, map_mul, er, map_mul, map_mul, h, map_inv, map_inv]
    group
  · change cInf x = 1 ↔ bc qi (j x).1 = 1
    rw [hj, map_mul, map_mul, map_inv, conj_eq_one_iff, ei, bc_eq_one_iff]
  · change Matrix.GeneralLinearGroup.map (pFin E) x.1 = 1 ↔ bc qf (j x).1 = 1
    rw [hj, map_mul, map_mul, map_inv, conj_eq_one_iff, ef, bc_eq_one_iff]
  · change (bc θ (bc qi (j x).1)).val = _
    have e1 : bc θ (bc qi (bc (inclR (AF F₀)) M)) = bc τ M := Units.ext (Matrix.ext fun a b => hθ.1 _)
    have e2 : bc θ (bc Θ.symm.toRingHom (cInf x)) = cEmb τ x := Units.ext (Matrix.ext fun a b =>
      (h7 τ θ hθ _).trans (congrArg (coord τ) (Θ.apply_symm_apply _)))
    rw [hj, map_mul (bc qi), map_mul (bc qi), map_inv, ei, map_mul, map_mul, map_inv, e1, e2, Units.val_mul, Units.val_mul,
      Matrix.coe_units_inv]
  · change (bc qf (j x).1).val = _
    rw [hj, ← map_inv, map_mul, map_mul, ef, Units.val_mul, Units.val_mul, ← Matrix.coe_units_inv]
    rfl

end Group

section Record

theorem exists_matrix (D : D7) [IsCMField D.host.E] (V : HSp D) (hs : V.SigOK) (hp : V.IsPosDef) :
    ∃ M : GL (Fin V.rank) D.host.E, cT (D.sp.cm.sig : D.host.E →+* D.host.E) M.val * V.gram * M.val = 1 := by
  obtain ⟨e, he⟩ := GlobalTheory.DefiniteMass.exists_isometry (E := D.host.E) D.sp.cm.cmUnram V hs hp
  let b := (Pi.basisFun D.host.E (Fin V.rank)).map e.symm
  have hM : cT (D.sp.cm.sig : D.host.E →+* D.host.E) (V.frame.toMatrix b) * V.gram * V.frame.toMatrix b = 1 := by
    refine Matrix.ext fun i k => ?_
    have h1 : V.hT (b i) (b k) = (1 : Matrix (Fin V.rank) (Fin V.rank) D.host.E) i k := by
      rw [← he]
      change ∑ l, star (e (b i) l) * e (b k) l = _
      simp only [b, Module.Basis.map_apply, LinearEquiv.apply_symm_apply, Pi.basisFun_apply]
      rw [Finset.sum_eq_single i (fun l _ hl => by simp [hl]) (by simp)]
      simp [Matrix.one_apply, Pi.single_apply]
    rw [← h1]
    conv_rhs => rw [← V.frame.sum_repr (b i), ← V.frame.sum_repr (b k)]
    simp only [map_sum, LinearMap.sum_apply, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, Matrix.mul_apply, cT,
      Finset.sum_mul, Finset.mul_sum, Matrix.transpose_apply, Matrix.map_apply, Module.Basis.toMatrix_apply,
      HSpace.gram]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => mul_comm _ _
  exact ⟨⟨_, _, mul_eq_one_comm.1 hM, hM⟩, hM⟩

theorem exists_iso : ∀ (D : D7) [IsCMField D.host.E] (V : HSp D) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)),
    IsInfFam θ → V.SigOK → V.IsPosDef →
    ∃ (j : UA D.host.E V.rank ≃ₜ* GA D V) (M : Matrix (Fin V.rank) (Fin V.rank) D.host.E),
      cT (D.sp.cm.sig : D.host.E →+* D.host.E) M * V.gram * M = 1 ∧
      (∀ x, x ∈ ratU D.host.E V.rank ↔ j x ∈ GQ V) ∧
      (∀ x, x ∈ finU D.host.E V.rank ↔ j x ∈ GfC V) ∧
      (∀ x, x ∈ infU D.host.E V.rank ↔ j x ∈ GinfC V) ∧
      (∃ A : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ, (∀ τ, IsUnit (A τ)) ∧
        ∀ τ x, infMat D.sp.cm.sig V.gram (θ τ) (j x) =
          A τ * (cEmb (tauE D τ) x : Matrix (Fin V.rank) (Fin V.rank) ℂ) * (A τ)⁻¹) ∧
      (∀ x, finMat D.sp.cm.sig V.gram (j x) =
      M.map (Algebra.TensorProduct.includeRight : D.host.E →ₐ[D.host.F] Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) *
      ((x : GL (Fin V.rank) (Ad D.host.E)) : Matrix (Fin V.rank) (Fin V.rank) (Ad D.host.E)).map
        (fun a => (GlobalTheory.LFun.finAdEquiv D.host.F D.host.E).symm (pFin D.host.E a)) *
      M⁻¹.map (Algebra.TensorProduct.includeRight : D.host.E →ₐ[D.host.F] Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) := by
  intro D _ V θ hθ hs hp
  obtain ⟨M, hM⟩ := exists_matrix D V hs hp
  obtain ⟨j, h1, h2, h3, h4, h5⟩ := exists_group (E := D.host.E) V.gram M hM
  exact ⟨j, M.val, hM, h1, h2, h3, ⟨fun τ => (bc (tauE D τ) M).val, fun τ => Units.isUnit _,
    fun τ x => h4 _ _ (hθ τ) x⟩, h5⟩

end Record

end GlobalTheory.DefTransfer.Glob
