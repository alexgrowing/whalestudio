import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PrinInf
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SkewGramHalfModule
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HeckeLPartialContinuationHolds
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IwasawaDoubledHermitianSpaceNonsplitPlace
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsUnitaryIsometryIsotropicFrameLocalRingStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsOfFixedInt
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.StabTransitiveOfLemmas
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsTameFinitePlaceHermitianAll
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DisjointSpanPerpLat

noncomputable section

namespace GlobalTheory.InertIwasawaIso

section Algebra

open Matrix Formalism.UG GlobalTheory.InertIwasawa

variable {A : Type} [CommRing A] {n r : ℕ}

theorem exists_minor_ne_zero [Nontrivial A] {X : Matrix (Fin n) (Fin r) A} {P : Matrix (Fin r) (Fin n) A}
    (h : P * X = 1) : ∃ f : Fin r → Fin n, (X.submatrix f id).det ≠ 0 := by
  by_contra hc
  push Not at hc
  have e : (P * X).det = (detRowAlternating (n := Fin r) (R := A)).toMultilinearMap fun i => ∑ k, P i k • X k := by
    change detRowAlternating (P * X) = detRowAlternating _
    congr 1
    ext i j
    simp [mul_apply]
  rw [h, det_one, MultilinearMap.map_sum] at e
  refine one_ne_zero (e.trans (Finset.sum_eq_zero fun f _ => ?_))
  rw [MultilinearMap.map_smul_univ]
  exact (congrArg (_ • ·) (hc f)).trans (smul_zero _)

theorem exists_frame (O : Subring A) {K : Type} [Field K] (V : ValuationSubring K) (φ : A ≃+* K)
    (hφ : ∀ y, y ∈ O ↔ φ y ∈ V) {X : Matrix (Fin n) (Fin r) A} {P : Matrix (Fin r) (Fin n) A} (h : P * X = 1) :
    ∃ (C : Matrix (Fin n) (Fin r) O) (c : GL (Fin r) A), (∃ L : Matrix (Fin r) (Fin n) O, L * C = 1) ∧
      X = C.map O.subtype * c.1 := by
  haveI := φ.toEquiv.nontrivial
  obtain ⟨f₀, h₀⟩ := exists_minor_ne_zero h
  haveI : Nonempty (Fin r → Fin n) := ⟨f₀⟩
  obtain ⟨f, hf⟩ := Finite.exists_max fun f : Fin r → Fin n => V.valuation (φ (X.submatrix f id).det)
  have h1 : 0 < V.valuation (φ (X.submatrix f id).det) :=
    lt_of_lt_of_le (zero_lt_iff.2 (by simpa using h₀)) (hf f₀)
  have hu : IsUnit (X.submatrix f id) := by
    rw [isUnit_iff_isUnit_det, ← MulEquiv.isUnit_map (f := φ), isUnit_iff_ne_zero]
    exact fun e => by simp [e] at h1
  set Y := X * (hu.unit⁻¹).1 with hY
  have hX : X = Y * X.submatrix f id := by rw [hY, Matrix.mul_assoc, hu.val_inv_mul, Matrix.mul_one]
  have hO : ∀ i j, Y i j ∈ O := fun i j => by
    have e : X.submatrix (Function.update f j i) id =
        (X.submatrix f id).updateRow j (∑ k, Y i k • X.submatrix f id k) := by
      ext a b
      by_cases ha : a = j
      · subst ha
        have := congrFun (congrFun hX i) b
        simpa [mul_apply] using this
      · simp [ha]
    have := hf (Function.update f j i)
    rw [e, det_updateRow_sum, smul_eq_mul, map_mul, map_mul] at this
    rw [hφ, ← V.valuation_le_one_iff]
    exact (mul_le_iff_le_one_left h1).1 this
  refine ⟨Matrix.of fun i j => ⟨_, hO i j⟩, hu.unit, ⟨(1 : Matrix (Fin n) (Fin n) O).submatrix f id, ?_⟩, hX⟩
  have e : Y.submatrix f id = 1 := by
    rw [← hu.mul_val_inv, hY]; rfl
  ext i j
  have := congrFun (congrFun e i) j
  simpa [mul_apply, one_apply, apply_ite ((↑) : O → A)] using this

theorem isLocalRing_of_equiv (O : Subring A) {K : Type} [Field K] (V : ValuationSubring K) (φ : A ≃+* K)
    (hφ : ∀ y, y ∈ O ↔ φ y ∈ V) : IsLocalRing O :=
  haveI := φ.toEquiv.nontrivial
  IsLocalRing.of_surjective' ((φ.symm.toRingHom.comp V.subtype).codRestrict O fun x => (hφ _).2 (by simp))
    fun y => ⟨⟨φ y, (hφ _).1 y.2⟩, Subtype.ext (φ.symm_apply_apply _)⟩

theorem exists_stab (O : Subring A) {K : Type} [Field K] (V : ValuationSubring K) (φ : A ≃+* K)
    (hφ : ∀ y, y ∈ O ↔ φ y ∈ V) {σ : A →+* A} (hσ : ∀ x ∈ O, σ x ∈ O)
    (hs : ∀ x, σ (σ x) = x) {τ : A} (hτO : τ ∈ O) (hτ : τ + σ τ = 1)
    (hN : ∀ u ∈ O, σ u = u → (∃ b ∈ O, u * b = 1) → ∃ x ∈ O, σ x * x = u)
    {J : Matrix (Fin n) (Fin n) A} (hJ : cT σ J = J)
    (hu : IsUnit J) {Λ : Submodule O (Fin n → A)} (hΛ : ∀ y, y ∈ Λ ↔ ∀ x ∈ Λ, hform σ J x y ∈ O) {a : GL (Fin n) A}
    (ha : ∀ y, (∀ i, y i ∈ O) ↔ a.1 *ᵥ y ∈ Λ) {X : Matrix (Fin n) (Fin r) A} {P : Matrix (Fin r) (Fin n) A}
    (hP : P * X = 1) (hX : cT σ X * J * X = 0) {g : GL (Fin n) A} (hg : g ∈ UJ σ J) :
    ∃ k ∈ UJ σ J, k ∈ stabGL Λ ∧ ∃ β : GL (Fin r) A, (g * k⁻¹).1 * X = X * β.1 := by
  haveI := isLocalRing_of_equiv O V φ hφ
  obtain ⟨B, hB, eB⟩ := exists_gram O hσ hu hΛ ha
  let s : O →+* O := σ.restrict O O hσ
  have hc : ∀ {a b : Type} (M : Matrix a b O), cT σ (M.map O.subtype) = (cT s M).map O.subtype := fun M => rfl
  have key : ∀ h ∈ UJ σ J, ∃ (C : Matrix (Fin n) (Fin r) O) (c : GL (Fin r) A),
      (∃ L : Matrix (Fin r) (Fin n) O, L * C = 1) ∧ cT s C * B * C = 0 ∧
        h.1 * X * (c⁻¹).1 = a.1 * C.map O.subtype := fun h hh => by
    obtain ⟨C, c, h1, h2⟩ := exists_frame O V φ hφ (X := (a⁻¹ * h).1 * X) (P := P * ((a⁻¹ * h)⁻¹).1)
      (by rw [Matrix.mul_assoc, ← Matrix.mul_assoc _ _ X, Units.inv_mul, Matrix.one_mul, hP])
    have h3 : h.1 * X * (c⁻¹).1 = a.1 * C.map O.subtype := by
      calc _ = a.1 * ((a⁻¹ * h).1 * X) * (c⁻¹).1 := by
            rw [← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel_left]
        _ = _ := by rw [h2, Matrix.mul_assoc, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
    refine ⟨C, c, h1, ?_, h3⟩
    apply Matrix.map_injective O.subtype_injective
    change Matrix.map _ O.subtype = Matrix.map _ O.subtype
    rw [Matrix.map_mul, Matrix.map_mul, ← hc, eB, Matrix.map_zero _ (map_zero _)]
    calc _ = cT σ (a.1 * C.map O.subtype) * J * (a.1 * C.map O.subtype) := by
          rw [cT_mul]; simp only [Matrix.mul_assoc]
      _ = cT σ (c⁻¹).1 * (cT σ X * (cT σ h.1 * J * h.1) * X) * (c⁻¹).1 := by
          rw [← h3, cT_mul, cT_mul]; simp only [Matrix.mul_assoc]
      _ = 0 := by rw [show cT σ h.1 * J * h.1 = J from hh, hX, Matrix.mul_zero, Matrix.zero_mul]
  obtain ⟨C, c, h1, h2, h3⟩ := key 1 (one_mem _)
  obtain ⟨C', c', h1', h2', h3'⟩ := key g⁻¹ (inv_mem hg)
  obtain ⟨k, hk, hkC⟩ := GlobalTheory.T.exists_unitaryIsometry_isotropicFrame_localRing O s (fun x => Subtype.ext (hs x)) ⟨⟨τ, hτO⟩, Subtype.ext hτ⟩
    (fun u hu' hsu => by
      obtain ⟨b, hb⟩ := hu'.exists_right_inv
      obtain ⟨x, hx, e⟩ := hN u u.2 (congrArg Subtype.val hsu) ⟨b, b.2, congrArg Subtype.val hb⟩
      exact ⟨⟨x, hx⟩, Subtype.ext e⟩) n r B (by
      apply Matrix.map_injective O.subtype_injective
      change Matrix.map _ O.subtype = Matrix.map _ O.subtype
      rw [← hc, eB, cT_mul, cT_mul, cT_cT hs, hJ, Matrix.mul_assoc]) hB C' C h1' h1 h2' h2
  have hka : (a * bc O.subtype k * a⁻¹).1 * a.1 = a.1 * k.1.map O.subtype := by
    rw [← Units.val_mul, inv_mul_cancel_right]; rfl
  refine ⟨a * bc O.subtype k * a⁻¹, ?_, fun w => ?_, c'⁻¹ * c, ?_⟩
  · change cT σ (a.1 * k.1.map O.subtype * (a⁻¹).1) * J * (a.1 * k.1.map O.subtype * (a⁻¹).1) = J
    calc _ = cT σ (a⁻¹).1 * (cT σ (k.1.map O.subtype) * (cT σ a.1 * J * a.1) * k.1.map O.subtype) * (a⁻¹).1 := by
          rw [cT_mul, cT_mul]; simp only [Matrix.mul_assoc]
      _ = cT σ (a.1 * (a⁻¹).1) * J * (a.1 * (a⁻¹).1) := by
          rw [← eB, hc, ← Matrix.map_mul, ← Matrix.map_mul, hk, eB, cT_mul]; simp only [Matrix.mul_assoc]
      _ = J := by rw [Units.mul_inv, cT_one, Matrix.one_mul, Matrix.mul_one]
  · obtain ⟨w, rfl⟩ : ∃ w', w = a.1 *ᵥ w' := ⟨(a⁻¹).1 *ᵥ w, by rw [mulVec_mulVec, Units.mul_inv, one_mulVec]⟩
    rw [mulVec_mulVec, hka, ← mulVec_mulVec, ← ha, ← ha]
    exact mulVec_mem_iff O k w
  · have e : (a * bc O.subtype k * a⁻¹).1 * ((g⁻¹).1 * X * (c'⁻¹).1) = X * (c⁻¹).1 := by
      rw [h3', ← Matrix.mul_assoc, hka, Matrix.mul_assoc, ← Matrix.map_mul, hkC, ← h3, Units.val_one, Matrix.one_mul]
    generalize a * bc O.subtype k * a⁻¹ = κ at e
    calc _ = (g * κ⁻¹).1 * (X * (c⁻¹).1) * c.1 := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
      _ = ((g * κ⁻¹) * κ * g⁻¹).1 * X * (c'⁻¹ * c).1 := by
          rw [← e]; simp only [Units.val_mul, Matrix.mul_assoc]
      _ = _ := by rw [inv_mul_cancel_right, mul_inv_cancel, Units.val_one, Matrix.one_mul]

end Algebra

section Ext

open scoped TensorProduct Matrix
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups

variable {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {n r : ℕ} (J : Matrix (Fin n) (Fin n) E)
  {R R' : Type} [CommRing R] [Algebra F R] [CommRing R'] [Algebra F R']

theorem tensNU_mul_inclR (j : R →ₗ[F] R') (hj : ∀ a b, j (a * b) = j a * j b) (y : R ⊗[F] E) (x : E) :
    tensNU j hj (y * inclR R x) = tensNU j hj y * inclR R' x := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => simp [inclR]
  | add y z hy hz => rw [add_mul, map_add, map_add, hy, hz, add_mul]

theorem glue_mul_rect {A B : Type} [CommRing A] [CommRing B] (j : B →ₙ+* A) {M : Matrix (Fin n) (Fin n) B}
    {β : Matrix (Fin r) (Fin r) B} {X : Matrix (Fin n) (Fin r) B} {X' : Matrix (Fin n) (Fin r) A}
    (hj : ∀ y a b, j (y * X a b) = j y * X' a b) (h : M * X = X * β) : glue j 1 M * X' = X' * glue j 1 β := by
  rw [glue, glue, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]
  congr 1
  ext a b
  have := congrArg j (congrFun (congrFun h a) b)
  simp only [Matrix.mul_apply, map_sum, mul_comm (X _ _), hj] at this
  simp only [Matrix.mul_apply, Matrix.map_apply, mul_comm (X' _ _), this]

theorem extH_stab (j : R →ₗ[F] R') (hj : ∀ a b, j (a * b) = j a * j b) (e : Matrix (Fin n) (Fin r) E) (g : HA R σ J)
    (h : ∃ β : GL (Fin r) (R ⊗[F] E), (HA.mat R σ J g).1 * e.map (inclR R) = e.map (inclR R) * β.1) :
    ∃ β : GL (Fin r) (R' ⊗[F] E),
      (HA.mat R' σ J (extH σ J j hj g)).1 * e.map (inclR R') = e.map (inclR R') * β.1 := by
  obtain ⟨β, h⟩ := h
  refine ⟨⟨glue (tensNU j hj) 1 β.1, glue (tensNU j hj) 1 (β⁻¹).1, ?_, ?_⟩, ?_⟩
  · rw [glue_mul, one_mul, Units.mul_inv, glue_one]
  · rw [glue_mul, one_mul, Units.inv_mul, glue_one]
  · exact glue_mul_rect (tensNU j hj) (fun y a b => tensNU_mul_inclR j hj y (e a b)) h

end Ext

section Place

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.LFun

theorem exists_of_inert {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (hσ : IsCMExt F E σ) {c : 𝓞 E} (hc : (c : E) + σ c = 1) {n r : ℕ}
    {J : Matrix (Fin n) (Fin n) E} (hJ : IsHermND σ J) {L : Submodule (𝓞 E) (Fin n → E)} [Submodule.IsLattice E L]
    {v : HeightOneSpectrum (𝓞 F)} {w : HeightOneSpectrum (𝓞 E)} (hw : Formalism.UG.IsInertAt F E v w)
    (hv : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryLatticeOrthogonal.UnramAt F E v) (hL : IsSelfDualAt σ J L v) {e : Matrix (Fin n) (Fin r) E}
    {p : Matrix (Fin r) (Fin n) E} (hp : p * e = 1) (he : Formalism.UG.cT (σ : E →+* E) e * J * e = 0) (y : GLoc σ J v) :
    ∃ q k : GLoc σ J v, (∃ β : GL (Fin r) (AF F ⊗[F] E),
      (HA.mat (AF F) σ J (emb σ J v q)).1 * e.map (inclR (AF F)) = e.map (inclR (AF F)) * β.1) ∧
      k ∈ stabLoc σ J L v ∧ y = q * k := by
  have h := (InertChart.under_eq_iff hw w).2 rfl
  obtain ⟨a, ha⟩ := Frames.exists_isLatticeFrame (F := F) L
  have hN := GlobalTheory.UnramSelfDual.exists_norm v hσ (GlobalTheory.UnramConjUnit.exists_sub_conj_unit _ _ _ hσ v hv)
  have hO : ∀ z, z ∈ GlobalTheory.IndefiniteRowSideFullHecke.UnitaryLatticeOrthogonal.OEv F E v ↔ z ∈ intLoc F E v := GlobalTheory.StabOrbit.mem_OEv_iff v
  simp only [hO] at hN
  let ι : E →+* Fv F v ⊗[F] E := inclR (Fv F v)
  obtain ⟨k, h1, h2, h3⟩ := exists_stab (intLoc F E v) (w.adicCompletionIntegers E)
    (InertChart.complEquiv hw h) (InertChart.mem_intLoc_iff hw h)
    (σ := Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ) (fun _ => sigR_mem_intLoc σ) (sigR_invol (InertChart.conj_conj hσ))
    (τ := ι c) (tmul_mem_intLoc (one_mem _) c)
    (by change ι c + ι (σ c) = 1
        rw [← map_add, hc, map_one]) hN
    (J := JR (Fv F v) J) (by ext i j; exact congrArg ι (hJ.1 i j))
    ((Matrix.isUnit_iff_isUnit_det _).2 (isUnit_det_JR hJ.2)) (Λ := latLoc F L v)
    (fun y => Submodule.ext_iff.1 hL y) (ha v) (X := e.map ι) (P := p.map ι)
    (by rw [← Matrix.map_mul, hp, Matrix.map_one _ (map_zero _) (map_one _)])
    (by rw [GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.cT_map (σ : E →+* E) _ ι (fun _ => rfl), show JR (Fv F v) J = J.map ι from rfl,
          ← Matrix.map_mul, ← Matrix.map_mul, he, Matrix.map_zero _ (map_zero _)])
    (g := matHom _ σ J y) y.2
  let κ : GLoc σ J v := ⟨k, h1⟩
  have h4 : ∃ β : GL (Fin r) (Fv F v ⊗[F] E), (HA.mat (Fv F v) σ J (y * κ⁻¹)).1 * e.map (inclR (Fv F v)) =
      e.map (inclR (Fv F v)) * β.1 := h3
  refine ⟨y * κ⁻¹, κ, ?_, h2, (inv_mul_cancel_right y κ).symm⟩
  rw [emb, MonoidHom.comp_apply, ofFin, embLocFin]
  exact extH_stab σ J _ _ e _ (extH_stab σ J _ _ e _ h4)

end Place

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW

theorem iwasawa_inert : ∀ (D : D7) (T T₀ : HSp D) (r : ℕ) (d : HypDec T T₀ r) (v : FinPl D), ¬ Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) v → ∀ y : Gv T v, ∃ q k : Gv T v, emb D.sp.cm.sig T.gram v q ∈ stab d ∧ k ∈ stabLoc D.sp.cm.sig T.gram (frameLat T) v ∧ y = q * k := by
  intro D T T₀ r d v hv y
  haveI := isLattice_frameLat_host T
  have := v.isMaximal
  obtain ⟨P, hP, hPv⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 D.host.E) v.asIdeal
  let w : HeightOneSpectrum (𝓞 D.host.E) := ⟨P, hP.isPrime, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot P⟩
  have h : w.under (𝓞 D.host.F) = v := HeightOneSpectrum.ext hPv.over.symm
  have hi := GlobalTheory.LPositivity.split_or_inert D w
  rw [h] at hi
  obtain ⟨c, hc⟩ := D.host.exists_trace_one
  rw [← show D.sp.cm.sig (c : D.host.E) = D.host.conj c from D.host.φ₀.injective
    (((isCMExt_host D).2.2.2 _ _).trans (Formalism.HC.HostAx.conjE_apply _ _ _).symm)] at hc
  exact exists_of_inert (isCMExt_host D) (c := c) hc (GlobalTheory.Doubling.isHermND_gram T) (hi.resolve_left hv)
    ((GlobalTheory.SelfDualLatticeCompare.unram_iff ..).2 fun u hu =>
      haveI := u.isPrime
      GlobalTheory.FinPl.TamePlaces.extUnramAt D v u.asIdeal hu)
    (SelfDual.isSelfDualAt_frameLat D T v) d.e'e d.ee y

end GlobalTheory.InertIwasawaIso

end
