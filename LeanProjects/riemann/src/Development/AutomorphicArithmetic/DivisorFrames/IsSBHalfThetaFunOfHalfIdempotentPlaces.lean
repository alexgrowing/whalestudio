import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.FinMatchDefs
import Development.AutomorphicArithmetic.DivisorFrames.ThetaOperatorIntertwinesHeisenberg
import Development.AutomorphicArithmetic.DivisorFrames.PtOSgnMemLatAtVIffMemLatO
import Development.AutomorphicArithmetic.DivisorFrames.ExistsNeZeroLinearModelVacuumEqSmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergStableRelationOfVacuaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoxGraphGraphHeis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitBasisWittModelLocal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStdCharNegOneOfStandardTraceAdelicAddCharStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawWeilZetaGlobal

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints GlobalTheory.Grid GlobalTheory.ChainFr GlobalTheory.SquareComm GlobalTheory.FinMatch
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model piW chrW unifAt latAtV At SInf)
open GlobalTheory.TripleRead (thO ptO)
open GlobalTheory.AdelicU (evFin splitPrime)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.FmPlace

section Generic

open GlobalTheory.LatVac (liftV evFin_liftV at_liftV)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

private theorem evFin_liftV_ne {v w : HeightOneSpectrum (𝓞 F)} (h : w ≠ v) (a : Fv F v) : evFin F w (liftV v a) = 0 :=
  GlobalTheory.AdelicU.evalV_singleFin_ne h a

private theorem at_liftV_smul {M : Type} [AddCommGroup M] [Module (AF F) M] (v : HeightOneSpectrum (𝓞 F)) (z : M) :
    At (evFin F v) (liftV v (1 : Fv F v) • z) := fun u hu => by
  rw [smul_smul, ← smul_eq_mul u, at_liftV v 1 u hu, zero_smul]

private theorem at_entry {n d : ℕ} {v : HeightOneSpectrum (𝓞 F)} {x : Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E)}
    (hx : At (evFin F v) x) (i : Fin n) (j : Fin d) : At (evFin F v) (x i j) := fun u hu =>
  congrFun (congrFun (hx u hu) i) j

private theorem exists_idem (hcm : IsCMExt F E σ) {v : HeightOneSpectrum (𝓞 F)} (t : E →ₐ[F] Fv F v) :
    ∃ a : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E, At (evFin F v) a ∧ piW t a = 1 ∧ piW (t.comp σ) a = 0 := by
  obtain ⟨h1, h0⟩ := GlobalTheory.LatSplit.piW_splitIdemAd hcm t
  refine ⟨liftV v (1 : Fv F v) • GlobalTheory.AdelicU.Supp.splitIdemAd hcm t, at_liftV_smul v _, ?_, ?_⟩
  · rw [GlobalTheory.LatFill.piW_smul, h1, evFin_liftV, mul_one]
  · rw [GlobalTheory.LatFill.piW_smul, h0, mul_zero]

private theorem piW_of_at_ne {v w : HeightOneSpectrum (𝓞 F)} (h : w ≠ v) (t : E →ₐ[F] Fv F w) {z : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E}
    (hz : At (evFin F v) z) : piW t z = 0 := by
  have h1 := GlobalTheory.LatFill.piW_smul t (liftV w (1 : Fv F w)) z
  rw [hz _ (evFin_liftV_ne h.symm 1), map_zero, evFin_liftV, one_mul] at h1
  exact h1.symm

private theorem halfEl_of_at {P : Finset (HeightOneSpectrum (𝓞 F))} (t : ∀ v : P, E →ₐ[F] Fv F v) (v : P)
    {z : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E} (hz : At (evFin F v.1) z) (h0 : piW (t v) z = 0) : HalfEl P t z := by
  refine ⟨fun u hu => hz u (hu v v.2), fun w => ?_⟩
  by_cases h : w = v
  · subst h; exact h0
  · exact piW_of_at_ne (fun e => h (Subtype.ext e)) _ hz

private theorem eq_sum_of_halfEl {P : Finset (HeightOneSpectrum (𝓞 F))} {t : ∀ v : P, E →ₐ[F] Fv F v}
    {z : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E} (hz : HalfEl P t z) : z = ∑ v : P, liftV v.1 (1 : Fv F v) • z := by
  have h := hz.1 (1 - ∑ v : P, liftV v.1 (1 : Fv F v)) fun w hw => by
    rw [map_sub, map_one, map_sum, Finset.sum_eq_single (⟨w, hw⟩ : P) (fun v _ hv => evFin_liftV_ne
      (fun e => hv (Subtype.ext e.symm)) 1) (fun h => absurd (Finset.mem_univ _) h), evFin_liftV, sub_self]
  rw [sub_smul, one_smul, sub_eq_zero, Finset.sum_smul] at h
  exact h

private theorem at_mul_smul {n d : ℕ} {v : HeightOneSpectrum (𝓞 F)} {a : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E} (ha : At (evFin F v) a)
    (x : Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E)) : At (evFin F v) (a • x) := fun u hu => by
  rw [← smul_assoc, ha u hu, zero_smul]

private theorem symp_idem (hcm : IsCMExt F E σ) {v : HeightOneSpectrum (𝓞 F)} (t : E →ₐ[F] Fv F v)
    {a : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E} (h1 : piW t a = 1) {n d : ℕ} (ξ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E)
    (JA : Matrix (Fin n) (Fin n) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E)) (JB : Matrix (Fin d) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E))
    (u : Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E)) {y : Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E)}
    (hy : At (evFin F v) y) (hy1 : y.map (piW t) = 0) :
    GlobalTheory.WeilM.symp (R := AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) ξ JA JB u y =
      GlobalTheory.WeilM.symp (R := AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) ξ JA JB (a • u) y := by
  have key : ∀ k l, a * GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ (y k l) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ (y k l) := fun k l => by
    have hat : At (evFin F v) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ (y k l)) := fun c hc => by
      rw [← map_smul, at_entry hy k l c hc, map_zero]
    have h0 : piW (t.comp σ) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ (y k l)) = 0 := by
      rw [GlobalTheory.VacIso.piW_cA, GlobalTheory.AdelicU.comp_conj_conj hcm]
      exact congrFun (congrFun hy1 k) l
    rw [← sub_eq_zero]
    refine GlobalTheory.VacIso.eq_zero_of_at_split hcm t (fun c hc => ?_) ?_ ?_
    · rw [smul_sub, ← mul_smul_comm, hat c hc, mul_zero, sub_zero]
    · rw [map_sub, map_mul, h1, one_mul, sub_self]
    · rw [map_sub, map_mul, h0, mul_zero, sub_zero]
  unfold GlobalTheory.WeilM.symp GlobalTheory.WeilM.hTens
  congr 2
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ =>
    Finset.sum_congr rfl fun l _ => ?_
  rw [Matrix.smul_apply, smul_eq_mul]
  linear_combination (-(u i j * JA i k * JB j l)) * key k l

end Generic

section Host

open GlobalTheory.LatVac (liftV evFin_liftV at_liftV)

variable {D : D7}

private theorem infPart_liftV_smul (v : HeightOneSpectrum (𝓞 D.host.F)) (z : AE D) :
    infPart D (liftV v (1 : Fv D.host.F v) • z) = 0 := by
  induction z using TensorProduct.induction_on with
  | zero => rw [smul_zero, map_zero]
  | add x y hx hy => rw [smul_add, map_add, hx, hy, add_zero]
  | tmul b x =>
    rw [TensorProduct.smul_tmul']
    change ((0 : Ainf D.host.F) * b.1) ⊗ₜ[D.host.F] x = 0
    rw [zero_mul, TensorProduct.zero_tmul]

private theorem infPart_halfEl {P : Finset (HeightOneSpectrum (𝓞 D.host.F))} {t : ∀ v : P, D.host.E →ₐ[D.host.F] Fv D.host.F v}
    {z : AE D} (hz : HalfEl P t z) : infPart D z = 0 := by
  rw [eq_sum_of_halfEl hz, map_sum]
  exact Finset.sum_eq_zero fun v _ => infPart_liftV_smul _ _

private theorem ptO_smul {m k d : ℕ} (G : Matrix (Fin m) (Fin m) D.host.E) (e : Fin k ≃ Fin d) (a : AE D)
    (x : Matrix (Fin d) (Fin m) (AE D)) : ptO G e (a • x) = a • ptO G e x := by
  unfold ptO
  rw [Matrix.smul_mul]; rfl

private theorem ptO_smul' {m k d : ℕ} (G : Matrix (Fin m) (Fin m) D.host.E) (e : Fin k ≃ Fin d) (a : AF D.host.F)
    (x : Matrix (Fin d) (Fin m) (AE D)) : ptO G e (a • x) = a • ptO G e x := by
  unfold ptO
  rw [Matrix.smul_mul]; rfl

private theorem ptO_add {m k d : ℕ} (G : Matrix (Fin m) (Fin m) D.host.E) (e : Fin k ≃ Fin d)
    (x y : Matrix (Fin d) (Fin m) (AE D)) : ptO G e (x + y) = ptO G e x + ptO G e y := by
  unfold ptO
  rw [Matrix.add_mul]; rfl

private theorem ptO_bij {m k d : ℕ} (G : Matrix (Fin m) (Fin m) D.host.E) (hG : IsUnit G.det) (e : Fin k ≃ Fin d) :
    Function.Bijective (ptO (D := D) G e) := (GlobalTheory.FockThetaOnto.crd G hG e).symm.bijective

private theorem isHalf_iff_ptO {m k d : ℕ} (G : Matrix (Fin m) (Fin m) D.host.E) (hG : IsUnit G.det) (e : Fin k ≃ Fin d)
    (a : AE D) (x : Matrix (Fin d) (Fin m) (AE D)) : IsHalf a x ↔ IsHalf a (ptO G e x) := by
  have h : ∀ {p q : ℕ} (y : Matrix (Fin p) (Fin q) (AE D)), IsHalf a y ↔ a • y = y := fun y =>
    ⟨fun h => Matrix.ext h, fun h i j => congrFun (congrFun h i) j⟩
  rw [h, h, ← ptO_smul, (ptO_bij G hG e).1.eq_iff]

private theorem sb_zero {m n : ℕ} (a : AE D) (Λ : AddSubgroup (Mx D m n)) : IsSBHalf a Λ 0 :=
  ⟨fun _ h => absurd rfl h, 1, one_pos, fun _ _ _ _ => rfl, fun _ h => absurd rfl h⟩

private theorem sb_smul {m n : ℕ} {a : AE D} {Λ : AddSubgroup (Mx D m n)} {φ : Mx D m n → ℂ} (h : IsSBHalf a Λ φ) (c : ℂ) :
    IsSBHalf a Λ (c • φ) := by
  obtain ⟨h1, k, hk, h2, h3⟩ := h
  exact ⟨fun t ht => h1 t (right_ne_zero_of_mul ht), k, hk, fun u hu hu' t => congrArg (c * ·) (h2 u hu hu' t),
    fun t ht => h3 t (right_ne_zero_of_mul ht)⟩

private theorem sb_add {m n : ℕ} {a : AE D} {Λ : AddSubgroup (Mx D m n)} {φ φ' : Mx D m n → ℂ} (h : IsSBHalf a Λ φ)
    (h' : IsSBHalf a Λ φ') : IsSBHalf a Λ (φ + φ') := by
  obtain ⟨h1, k, hk, h2, h3⟩ := h
  obtain ⟨h1', k', hk', h2', h3'⟩ := h'
  have hor : ∀ t, (φ + φ') t ≠ 0 → φ t ≠ 0 ∨ φ' t ≠ 0 := fun t ht => by
    by_contra! hc
    exact ht (by rw [Pi.add_apply, hc.1, hc.2, add_zero])
  refine ⟨fun t ht => (hor t ht).elim (h1 t) (h1' t), k * k', Nat.mul_pos hk hk', fun u hu hu' t => ?_, fun t ht => ?_⟩
  · rw [Pi.add_apply, Pi.add_apply, mul_smul, h2 _ (nsmul_mem hu k') (GlobalTheory.BigDat.GraphHeis.isHalf_nsmul' hu' k'),
      smul_comm k k' u, h2' _ (nsmul_mem hu k) (GlobalTheory.BigDat.GraphHeis.isHalf_nsmul' hu' k)]
  · rcases hor t ht with h | h
    · rw [mul_comm, mul_smul]; exact nsmul_mem (h3 t h) k'
    · rw [mul_smul]; exact nsmul_mem (h3' t h) k

end Host

end UpperTheory.FmPlace

open UpperTheory.FmPlace GlobalTheory.BigDat.GraphHeis in
set_option maxHeartbeats 1600000 in
theorem UpperTheory.isSBHalf_thetaFun_of_halfIdempotent_places :
    ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (ε : Bool) (S X : HSp D) (d : ℕ) (e : Fin d ≃ Fin X.rank)
        (Bs : Base D.host.F D.host.E) (Vs : Spc D.host.F D.host.E S.rank) (Ws : Spc D.host.F D.host.E d)
        (M : Model D.sp.cm.sig Vs Ws), IsPair ψ ε S X e Bs Vs Ws M → ∀ (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛX : Submodule (𝓞 D.host.E) (Fin X.rank → D.host.E)),
        IsLat e Vs Ws ΛS ΛX → IsSelfDualC (sgn ε S) ΛS → IsSelfDualC X ΛX →
        ∀ (P : Finset (HeightOneSpectrum (𝓞 D.host.F))) (t₁ t₀ : ∀ v : P, D.host.E →ₐ[D.host.F] Fv D.host.F v),
        (∀ v x, t₀ v x = t₁ v (D.sp.cm.sig x)) →
        ∀ eh : AE D, (∀ z : AE D, eh * z = z ↔ HalfEl P t₀ z) → (∀ z : AE D, cA D eh * z = z ↔ HalfEl P t₁ z) →
        ∀ (b : ∀ v : P, GL (Fin S.rank) (Fv D.host.F v)) (c : ∀ v : P, GL (Fin d) (Fv D.host.F v))
          (ι : ∀ v : P, ((Fin S.rank × Fin d → Fv D.host.F v) → ℂ) →ₗ[ℂ] (Matrix (Fin S.rank) (Fin d) (Fv D.host.F v) → ℂ)),
        (∀ v, M.IsLin ψ (piW (t₁ v)) (piW (t₀ v)) (fun u => (b v).1 * u.map (piW (t₁ v)) * (c v).1) (ι v)) →
        ∀ (φ : ∀ v : HeightOneSpectrum (𝓞 D.host.F), (Fin S.rank × Fin d → Fv D.host.F v) → ℂ), (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) →
        (∀ v, v ∉ P → φ v = M.vac v) →
        ∀ (g : SInf D.host.F (Fin S.rank × Fin d)) (Φ f : WO (sgn ε S) X → ℂ),
        (∀ x, Φ x = if IsHalf eh x then ∏ v : P, ι v (φ v) ((b v).1 * (ptO (sgn ε S).gram e x).map (piW (t₁ v)) * (c v).1) else 0) →
        IsThetaAt ψ (symplO (sgn ε S) X) (heisO ψ (sgn ε S) X) eh (latO (sgn ε S) X (ΛS : Set (Fin S.rank → D.host.E)) (ΛX : Set (Fin X.rank → D.host.E)) fun _ => True) 1
          (thO M ψ (sgn ε S).gram e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g M.vac)) Φ f →
        ∃ z : ℂ, z ≠ 0 ∧ f = thO M ψ (sgn ε S).gram e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (z • g) φ) := by
  intro D ψ ε S X d e Bs Vs Ws M hP ΛS ΛX hLat sdS sdX P t₁ t₀ ht eh h₀ h₁ b c ι hι φ hφ hφv g Φ f hΦ hth
  obtain ⟨⟨T, hT⟩, hf⟩ := hth
  have hfT := hf T hT
  obtain ⟨lsym, lrho, ladd, lsmul, -, -⟩ := UpperTheory.thetaOperator_intertwines_heisenberg D ψ ε S X d e Bs Vs Ws M hP
  obtain ⟨lat₁, lat₂⟩ := UpperTheory.ptO_sgn_mem_latAtV_iff_mem_latO D ψ ε S X d e Bs Vs Ws M hP ΛS ΛX hLat
  obtain ⟨hB, rfl, -, -, ⟨r, s, hV⟩, ⟨r', s', hW⟩, hM⟩ := hP
  have hcm := hB.cm
  have hstd := hB.std
  have hψ := GlobalTheory.T.isStdChar_neg_one_of_standardTraceAdelicAddChar D _ hstd
  have ht' : ∀ v, t₀ v = (t₁ v).comp D.sp.cm.sig := fun v => AlgHom.ext (ht v)
  choose z hz0 hz using fun v : P => UpperTheory.exists_ne_zero_linearModel_vacuum_eq_smul _ _ _ Bs _ _ Vs Ws M r s r' s' hB hV hW hM v.1 (t₁ v) (t₀ v) (ht v)
    (b v) (c v) (ι v) (hι v)
  choose a ha ha1 ha0 using fun v : P => exists_idem hcm (t₁ v)
  have hG : IsUnit (sgn ε S).gram.det := GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.gram_det_isUnit (sgn ε S)
  have hbij := ptO_bij (D := D) (sgn ε S).gram hG e
  set Λ := latO (sgn ε S) X (ΛS : Set (Fin S.rank → D.host.E)) (ΛX : Set (Fin X.rank → D.host.E)) fun _ => True with hΛ
  let H : AddSubgroup (Matrix (Fin S.rank) (Fin d) (AE D)) :=
    { carrier := {u | IsHalf eh u}
      zero_mem' := fun _ _ => mul_zero _
      add_mem' := fun {x y} hx hy i j => by rw [Matrix.add_apply, mul_add, hx i j, hy i j]
      neg_mem' := fun {x} hx i j => by rw [Matrix.neg_apply, mul_neg, hx i j] }
  have hH : ∀ x : WO (sgn ε S) X, ptO (sgn ε S).gram e x ∈ H ↔ IsHalf eh x := fun x =>
    (isHalf_iff_ptO (sgn ε S).gram hG e eh x).symm
  let R : Submodule ℂ ((Matrix (Fin S.rank) (Fin d) (AE D) → ℂ) × ((Fin S.rank × Fin d → AF D.host.F) → ℂ)) :=
    { carrier := {p | p.2 ∈ GlobalTheory.WeilM.schA D.host.F _ ∧ IsSBHalf eh Λ (fun x => p.1 (ptO (sgn ε S).gram e x)) ∧
        T (fun x => p.1 (ptO (sgn ε S).gram e x)) = thO M Bs.ψ (sgn ε S).gram e p.2}
      zero_mem' := ⟨zero_mem _, sb_zero _ _, by
        have := lsmul 0 0
        rw [zero_smul, zero_smul] at this
        exact (map_zero T).trans this.symm⟩
      add_mem' := fun {p q} hp hq => ⟨add_mem hp.1 hq.1, sb_add hp.2.1 hq.2.1, by
        rw [Prod.snd_add, ladd _ hp.1 _ hq.1, ← hp.2.2, ← hq.2.2, ← map_add]; rfl⟩
      smul_mem' := fun a p hp => ⟨Submodule.smul_mem _ a hp.1, sb_smul hp.2.1 a, by
        rw [Prod.smul_snd, lsmul, ← hp.2.2, ← map_smul]; rfl⟩ }
  have hind : ∀ χ : ∀ v : HeightOneSpectrum (𝓞 D.host.F), (Fin S.rank × Fin d → Fv D.host.F v) → ℂ, ∀ x : WO (sgn ε S) X,
      Set.indicator (H : Set _) (fun u => ∏ v : P, ι v (χ v) ((b v).1 * u.map (piW (t₁ v)) * (c v).1)) (ptO (sgn ε S).gram e x) =
        if IsHalf eh x then ∏ v : P, ι v (χ v) ((b v).1 * (ptO (sgn ε S).gram e x).map (piW (t₁ v)) * (c v).1) else 0 := by
    intro χ x
    by_cases hx : IsHalf eh x
    · rw [if_pos hx, Set.indicator_of_mem ((hH x).2 hx)]
    · rw [if_neg hx, Set.indicator_of_notMem (mt (hH x).1 hx)]
  have hbase : (fun x : WO (sgn ε S) X => Set.indicator (H : Set _)
      (fun u => ∏ v : P, ι v (M.vac v) ((b v).1 * u.map (piW (t₁ v)) * (c v).1)) (ptO (sgn ε S).gram e x)) =
      (∏ v, z v) • halfInd eh Λ := by
    funext x
    rw [hind, Pi.smul_apply, smul_eq_mul, halfInd]
    by_cases hx : IsHalf eh x
    · have hu := (hH x).2 hx
      have key : ∀ v : P, ι v (M.vac v) ((b v).1 * (ptO (sgn ε S).gram e x).map (piW (t₁ v)) * (c v).1) =
          if GlobalTheory.LatVac.liftV v.1 (1 : Fv D.host.F v) • ptO (sgn ε S).gram e x ∈ latAtV Vs Ws v then z v else 0 := fun v => by
        rw [← hz v _ (at_liftV_smul v.1 _) (Matrix.ext fun i j => by
          rw [Matrix.map_apply, Matrix.smul_apply, GlobalTheory.LatFill.piW_smul, ((h₀ _).1 (hu i j)).2 v, mul_zero]; rfl)]
        refine congrArg (fun w => ι v (M.vac v) ((b v).1 * w * (c v).1)) (Matrix.ext fun i j => ?_)
        rw [Matrix.map_apply, Matrix.map_apply, Matrix.smul_apply, GlobalTheory.LatFill.piW_smul, GlobalTheory.LatVac.evFin_liftV, one_mul]
      rw [if_pos hx, Finset.prod_congr rfl fun v _ => key v]
      by_cases hl : x ∈ Λ
      · rw [if_pos ⟨hl, hx⟩, mul_one]
        exact Finset.prod_congr rfl fun v _ => if_pos (lat₂ v _ (GlobalTheory.LatVac.at_liftV v.1 1)
          (by rw [GlobalTheory.LatVac.evFin_liftV]; exact one_mem _) x hl)
      · rw [if_neg fun h => hl h.1, mul_zero]
        by_contra hne
        refine hl ?_
        have hx' : x = ∑ v : P, GlobalTheory.LatVac.liftV v.1 (1 : Fv D.host.F v) • x := Matrix.ext fun i j => by
          rw [Matrix.sum_apply]
          exact eq_sum_of_halfEl ((h₀ _).1 (hx i j))
        rw [hx']
        refine sum_mem fun v _ => lat₁ v _ ?_
        rw [ptO_smul']
        by_contra hn
        exact hne (Finset.prod_eq_zero (Finset.mem_univ v) (if_neg hn))
    · rw [if_neg hx, if_neg fun h => hx h.2, mul_zero]
  have hmm : ∀ (v : P) (t : D.host.E →ₐ[D.host.F] Fv D.host.F v) (w : AE D) (u : Matrix (Fin S.rank) (Fin d) (AE D)),
      (w • u).map (piW t) = piW t w • u.map (piW t) := fun v t w u => Matrix.ext fun i j => map_mul (piW t) w (u i j)
  have hR := GlobalTheory.T.heisenbergStableRelation_of_vacua M Bs.ψ hstd hM (Finset.univ : Finset P) Subtype.val Subtype.val_injective.injOn
    (fun v => Matrix (Fin S.rank) (Fin d) (Fv D.host.F v))
    (fun v => {u | At (evFin D.host.F v.1) u ∧ u.map (piW (t₀ v)) = 0})
    (fun v => {u | At (evFin D.host.F v.1) u ∧ u.map (piW (t₁ v)) = 0})
    (fun v u => (b v).1 * u.map (piW (t₁ v)) * (c v).1) ι H R ((∏ v, z v) • g)
    (fun v _ => GlobalTheory.BigNZ.isLagrModel_of_isLin (hι v))
    (fun v _ u hu => ⟨hu.1, fun i j => (h₀ _).2 (halfEl_of_at t₀ v (at_entry hu.1 i j) (congrFun (congrFun hu.2 i) j))⟩)
    (fun v _ u hu => hu.1)
    (fun v _ u hu => ⟨a v • u, ⟨at_mul_smul (ha v) u, by rw [hmm, ht', ha0, zero_smul]⟩, u - a v • u,
      ⟨fun q hq => by rw [smul_sub, hu q hq, at_mul_smul (ha v) u q hq, sub_zero],
        by rw [Matrix.map_sub _ (map_sub _), hmm, ha1, one_smul, sub_self]⟩, (add_sub_cancel _ _).symm⟩)
    (fun v _ x _ u => by rw [Matrix.map_add _ (map_add _), Matrix.mul_add, Matrix.add_mul])
    (fun v _ v' _ hne x hx u => by
      have : x.map (piW (t₁ v')) = 0 := Matrix.ext fun i j =>
        piW_of_at_ne (fun e => hne (Subtype.ext e)) _ (at_entry hx.1 i j)
      rw [Matrix.map_add _ (map_add _), this, add_zero])
    (fun v _ u => ⟨a v • u, ⟨at_mul_smul (ha v) u, by rw [hmm, ht', ha0, zero_smul]⟩, by
      beta_reduce; rw [hmm, ha1, one_smul], fun y hy => symp_idem hcm (t₁ v) (ha1 v) _ _ _ u hy.1 hy.2⟩)
    (fun v _ x hx p hp => by
      obtain ⟨y, rfl⟩ := hbij.2 x
      have hy : IsHalf eh y := (hH y).1 fun i j =>
        (h₀ _).2 (halfEl_of_at t₀ v (at_entry hx.1 i j) (congrFun (congrFun hx.2 i) j))
      obtain ⟨k, hk, hky⟩ := GlobalTheory.PlaceVec.exists_nsmul_mem_latO (S := sgn ε S) (T := X) sdS.1 sdX.1 y
        (Matrix.ext fun i j => infPart_halfEl ((h₀ _).1 (hy i j)))
      refine ⟨GlobalTheory.HeisSchA.rho_mem_schA M _ hstd _ _ hp.1, ?_, ?_⟩
      · simp only [← ptO_add]
        exact sb_trans hp.2.1 hy hk hky
      · simp only [← ptO_add]
        rw [lrho, ← hp.2.2]
        exact hT.trans _ hp.2.1 y hy)
    (fun v _ x hx p hp => by
      obtain ⟨y, rfl⟩ := hbij.2 x
      have hy : IsHalf (cA D eh) y := (isHalf_iff_ptO (sgn ε S).gram hG e _ y).2 fun i j =>
        (h₁ _).2 (halfEl_of_at t₁ v (at_entry hx.1 i j) (congrFun (congrFun hx.2 i) j))
      obtain ⟨k, hk, hky⟩ := GlobalTheory.PlaceVec.exists_nsmul_mem_latO (S := sgn ε S) (T := X) sdS.1 sdX.1 y
        (Matrix.ext fun i j => infPart_halfEl ((h₁ _).1 (hy i j)))
      refine ⟨GlobalTheory.HeisSchA.rho_mem_schA M _ hstd _ _ hp.1, ?_, ?_⟩
      · simp only [lsym]
        refine sb_modul hp.2.1 (fun t => Bs.ψ (symplO (sgn ε S) X t y)) (fun q q' => ?_) hk (fun u hu _ => ?_)
        · rw [symplO_add_left', AddChar.map_add_eq_mul]
        · rw [symplO_nsmul']
          exact GlobalTheory.LatVac.char_sympl_eq_one hψ sdS sdX hu hky
      · simp only [lsym]
        rw [lrho, ← hp.2.2]
        exact hT.modul _ hp.2.1 y hy)
    ⟨(GlobalTheory.BigNZ.isFinPart_vac hM ∅).fam.mem hM _, by
      rw [hbase]; exact sb_smul (GlobalTheory.isSBHalf_halfInd _ _) _, by
      have e1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure ((∏ v, z v) • g) M.vac = (∏ v, z v) • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g M.vac :=
        funext fun _ => mul_assoc _ _ _
      rw [hbase, e1, lsmul, ← hT.vac, one_smul, map_smul]⟩
    φ hφ fun v hv => hφv v fun hm => hv ⟨v, hm⟩ (Finset.mem_univ _) rfl
  refine ⟨∏ v, z v, Finset.prod_ne_zero_iff.2 fun v _ => hz0 v, ?_⟩
  rw [hfT, ← hR.2.2]
  exact congrArg T (funext fun x => (hΦ x).trans (hind φ x).symm)
