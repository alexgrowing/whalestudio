import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMixModelB
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAwayUnitOfPowEqOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsScalarFiniteTensorEqDatumSmallModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergStableRelationOfVacua
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GridLocalTensorPlacesSplitIdempotentSum
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OrthogonalSumSelfDualExists
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchrodingerThetaDatumHeisenbergOriented
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsAddEquivSymplecticCoordsOrientedModel
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrimeDvdAbsNormHalfDifferent

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta Formalism.L2.DIV IsDedekindDomain NumberField MeasureTheory Matrix
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SqTower GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.ChainFr GlobalTheory.SquareDict GlobalTheory.SquareComm GlobalTheory.BigNZ GlobalTheory.FlipMatch GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB incM)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep Acts SInf At piW psiLoc chrW)
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopFlip

noncomputable section

namespace GlobalTheory.TopFlip.LinSmall

open GlobalTheory.SmallDat (PtS IxS sympS thetaS heisS thetaS_rho thetaS_smul)
open GlobalTheory.BigDat (atW atW_atPl_self atW_atPl_ne atPl_one_mul symplO_cA_smul isHalf_smul_self
  smul_of_isHalf smul_eq_zero_of_isHalf map_infPart_of_isHalf)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (latAtV)

section Sb

variable {D : D7}

theorem sb_zero {m n : ℕ} (a : AE D) (Λ : AddSubgroup (Mx D m n)) : IsSBHalf a Λ 0 :=
  ⟨fun _ h => absurd rfl h, 1, one_pos, fun _ _ _ _ => rfl, fun _ h => absurd rfl h⟩

theorem sb_smul {m n : ℕ} {a : AE D} {Λ : AddSubgroup (Mx D m n)} {Φ : Mx D m n → ℂ} (c : ℂ)
    (h : IsSBHalf a Λ Φ) : IsSBHalf a Λ (c • Φ) := by
  obtain ⟨h1, k, hk, h2, h3⟩ := h
  have hne : ∀ t, (c • Φ) t ≠ 0 → Φ t ≠ 0 := fun t ht h0 => ht (by rw [Pi.smul_apply, h0, smul_zero])
  exact ⟨fun t ht => h1 t (hne t ht), k, hk,
    fun u hu hu' t => by rw [Pi.smul_apply, Pi.smul_apply, h2 u hu hu' t], fun t ht => h3 t (hne t ht)⟩

theorem sb_add {m n : ℕ} {a : AE D} {Λ : AddSubgroup (Mx D m n)} {Φ Ψ : Mx D m n → ℂ}
    (h : IsSBHalf a Λ Φ) (h' : IsSBHalf a Λ Ψ) : IsSBHalf a Λ (Φ + Ψ) := by
  obtain ⟨h1, k, hk, h2, h3⟩ := h
  obtain ⟨h1', k', hk', h2', h3'⟩ := h'
  have hne : ∀ t, (Φ + Ψ) t ≠ 0 → Φ t ≠ 0 ∨ Ψ t ≠ 0 := fun t ht => by
    by_contra hc
    rw [not_or, not_not, not_not] at hc
    exact ht (by rw [Pi.add_apply, hc.1, hc.2, add_zero])
  have hh : ∀ (j : ℕ) (u : Mx D m n), IsHalf a u → IsHalf a (j • u) := fun j u hu p q => by
    rw [Matrix.smul_apply, nsmul_eq_mul, mul_left_comm, hu p q]
  refine ⟨fun t ht => (hne t ht).elim (h1 t) (h1' t), k * k', Nat.mul_pos hk hk', fun u hu hu' t => ?_,
    fun t ht => ?_⟩
  · have e1 : Φ (t + (k * k') • u) = Φ t := by
      rw [mul_smul]; exact h2 _ (Λ.nsmul_mem hu k') (hh _ _ hu') t
    have e2 : Ψ (t + (k * k') • u) = Ψ t := by
      rw [mul_comm, mul_smul]; exact h2' _ (Λ.nsmul_mem hu k) (hh _ _ hu') t
    rw [Pi.add_apply, Pi.add_apply, e1, e2]
  · rcases hne t ht with h | h
    · rw [mul_comm, mul_smul]; exact Λ.nsmul_mem (h3 t h) k'
    · rw [mul_smul]; exact Λ.nsmul_mem (h3' t h) k

theorem exists_nat_conj {w : Pl D.host.E}
    (hw : ((D.host.QS * D.host.q * D.host.d * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal) :
    ∃ m : ℕ, (m : 𝓞 D.host.E) ∉ w.asIdeal ∧ ∀ a ∈ D.host.AA, star ((m : D.host.E) * a) ∈ D.host.AA := by
  obtain ⟨p, hp, hP⟩ := GlobalTheory.HalfCompare.exists_prime_under w
  have hb := ReciprocityTheory.ChartRestriction.G.PullbackSections.MLI.bb_ne_bot D
  have h0 : ((D.host.𝔟 : Ideal (𝓞 D.host.E)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.2 hb
  refine ⟨Ideal.absNorm D.host.ccK * Ideal.absNorm D.host.𝔟, fun h => hw ((hP _).2 ?_), fun a ha => ?_⟩
  · rcases hp.dvd_mul.1 ((hP _).1 h) with h | h
    · exact h.mul_left _
    · exact (((GlobalTheory.HalfCompare.prime_dvd_absNorm_halfDifferent D hp).1 h).mul_right _).mul_right _
  · have h1 : ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∈ D.host.ccE := by
      have := Ideal.mem_map_of_mem (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) (Ideal.absNorm_mem D.host.ccK)
      rwa [map_natCast] at this
    have h2 : (1 : D.host.E) ∈ D.host.AA0 := by
      rw [Host.AA0, FractionalIdeal.mem_inv_iff h0]
      intro y hy
      rw [one_mul]
      exact FractionalIdeal.coeIdeal_le_one hy
    have h3 := FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_coeIdeal_of_mem (nonZeroDivisors (𝓞 D.host.E)) h1) h2
    rw [mul_one, map_natCast] at h3
    have h4 : a ∈ D.host.AA0 := by
      have : D.host.AA ≤ D.host.AA0 := by
        rw [Host.AA]
        calc _ ≤ 1 * D.host.AA0 := by gcongr; exact FractionalIdeal.coeIdeal_le_one
          _ = _ := one_mul _
      exact this ha
    rw [Host.AA0, FractionalIdeal.mem_inv_iff h0] at h4
    have h5 := h4 _ (FractionalIdeal.mem_coeIdeal_of_mem (nonZeroDivisors (𝓞 D.host.E)) (Ideal.absNorm_mem D.host.𝔟))
    rw [map_natCast] at h5
    obtain ⟨r, hr⟩ := (FractionalIdeal.mem_one_iff _).1 h5
    have h6 : IsIntegral ℤ (star (r : D.host.E)) :=
      (map_isIntegral_int (starRingEnd D.host.E) (RingOfIntegers.isIntegral_coe r) :)
    have h7 := D.host.AA.1.smul_mem (⟨_, h6⟩ : 𝓞 D.host.E) h3
    have e : star (((Ideal.absNorm D.host.ccK * Ideal.absNorm D.host.𝔟 : ℕ) : D.host.E) * a) =
        star (r : D.host.E) * (Ideal.absNorm D.host.ccK : ℕ) := by
      rw [show (r : D.host.E) = _ from hr, Nat.cast_mul, mul_assoc, star_mul', star_natCast, mul_comm a, mul_comm]
    rw [e]
    exact h7

theorem inv_nat_mem {w : Pl D.host.E} {m : ℕ} (hm : (m : 𝓞 D.host.E) ∉ w.asIdeal) :
    (m : Fv D.host.F (w.under (𝓞 D.host.F))) ≠ 0 ∧
      (m : Fv D.host.F (w.under (𝓞 D.host.F)))⁻¹ ∈ (w.under (𝓞 D.host.F)).adicCompletionIntegers D.host.F := by
  set v := w.under (𝓞 D.host.F)
  have h1 : (m : 𝓞 D.host.F) ∉ v.asIdeal := fun h => hm (by
    have : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) m ∈ w.asIdeal := h
    rwa [map_natCast] at this)
  have h2 : Valued.v (m : v.adicCompletion D.host.F) = 1 := by
    have := HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (algebraMap (𝓞 D.host.F) D.host.F m)
    rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff.2 h1, map_natCast] at this
    rw [← this]
    congr 1
    exact (map_natCast (algebraMap D.host.F (v.adicCompletion D.host.F)) m).symm
  refine ⟨fun h => ?_, ?_⟩
  · rw [show (m : v.adicCompletion D.host.F) = 0 from h, map_zero] at h2
    exact zero_ne_one h2
  · rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, h2, inv_one]

end Sb

section Pt

variable {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc} {i j : ℕ}

def ptE (e : Num G i j) : PtS G i j ≃ₗ[AE D] WO (spW₁ G i j) (spX G i j) :=
  { GlobalTheory.Twist.exists_addEquiv_symplecticCoords_orientedModel.coordsEquiv (e.symm.trans finSumFinEquiv).symm (incM (spW₁ G i j).gram)
      (by simpa only [one_smul] using GlobalTheory.Twist.exists_addEquiv_symplecticCoords_orientedModel.isUnit_det_incM (spW₁ G i j) 1 one_ne_zero) with
    map_smul' := fun a u => Matrix.smul_mul a (uᵀ.submatrix (e.symm.trans finSumFinEquiv).symm id) (incM (spW₁ G i j).gram) }

theorem ptE_apply (e : Num G i j) (u : PtS G i j) : ptE e u = ptB e u := rfl

theorem ptB_add (e : Num G i j) (u x : PtS G i j) : ptB e (u + x) = ptB e u + ptB e x := map_add (ptE e) u x

theorem ptB_smul (e : Num G i j) (a : AE D) (u : PtS G i j) : ptB e (a • u) = a • ptB e u := map_smul (ptE e) a u

theorem ptB_symm (e : Num G i j) (y : WO (spW₁ G i j) (spX G i j)) : ptB e ((ptE e).symm y) = y := (ptE e).apply_symm_apply y

theorem smul_of_half (e : Num G i j) {a : AE D} {u : PtS G i j} (h : IsHalf a (ptB e u)) : a • u = u :=
  (ptE e).injective ((ptB_smul e a u).trans (smul_of_isHalf h))

theorem sympS_ptB (e : Num G i j) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (hW : Γ.V'.J = (-1 : D.host.E) • (spW₁ G i j).gram)
    (hWW : Γ.W.J = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.skewGram (spV G i j) (spV₁ G i j) e) (u x : PtS G i j) :
    sympS Γ u x = symplO (spW₁ G i j) (spX G i j) (ptB e u) (ptB e x) := by
  refine GlobalTheory.SquareAgree.HeisCov.symp_eq false (spW₁ G i j) (spX G i j) (finSumFinEquiv.symm.trans e) Γ.V'.J Γ.W.J hW ?_ (ptB e)
    (fun u => ?_) u x
  · rw [hWW, GlobalTheory.Doubling.gram_hsum, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.skewGram]
    congr 1
    ext a b
    obtain ⟨a | a, rfl⟩ := e.surjective a <;> obtain ⟨b | b, rfl⟩ := e.surjective b <;>
      simp [GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk, GlobalTheory.Doubling.blkMat]
  · rw [if_neg Bool.false_ne_true, one_smul]
    rfl

theorem heisS_ptB (e : Num G i j) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (hW : Γ.V'.J = (-1 : D.host.E) • (spW₁ G i j).gram)
    (hWW : Γ.W.J = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.skewGram (spV G i j) (spV₁ G i j) e) (ψ : AddChar (AF D.host.F) ℂ) (x : PtS G i j)
    (f : WO (spW₁ G i j) (spX G i j) → ℂ) :
    heisS Γ ψ x (fun u => f (ptB e u)) = fun u => heisO ψ (spW₁ G i j) (spX G i j) (ptB e x) f (ptB e u) := by
  funext u
  unfold heisS heisO symplOH
  rw [sympS_ptB e Γ hW hWW, ← ptB_add, GlobalTheory.BigDat.invOf_two]

theorem at_of_half (e : Num G i j) (v : Pl D.host.F) {b : AE D}
    (hb : b * algebraMap (AF D.host.F) (AE D) (GlobalTheory.LatVac.liftV v 1) = b) {u : PtS G i j} (hu : IsHalf b (ptB e u)) :
    At (evFin D.host.F v) u := fun c hc =>
  smul_eq_zero_of_isHalf v hb (x := u) (fun p q => congrFun (congrFun (smul_of_half e hu) p) q) c hc

theorem liftV_smul {v : Pl D.host.F} {u : PtS G i j} (hu : At (evFin D.host.F v) u) : GlobalTheory.LatVac.liftV v 1 • u = u := by
  have := hu (1 - GlobalTheory.LatVac.liftV v 1) (by rw [map_sub, map_one, GlobalTheory.LatVac.evFin_liftV, sub_self])
  rw [sub_smul, one_smul, sub_eq_zero] at this
  exact this.symm

theorem symm_gen (e : Num G i j) (β : AF D.host.F) (a : D.host.E) (s : Fin (spW₁ G i j).rank → D.host.E)
    (r : Fin (spX G i j).rank → D.host.E) :
    (ptE e).symm (Matrix.of fun i' j' => β ⊗ₜ[D.host.F] (a * r i' * ∑ k, star (s k) * (spW₁ G i j).gram k j')) =
      β • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F (vecMulVec (star s) fun q => a * r (finSumFinEquiv (e.symm q))) := by
  rw [LinearEquiv.symm_apply_eq, ← GlobalTheory.BigDat.mulG_divG (spW₁ G i j) (Matrix.of _)]
  refine congrArg (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.mulG (spW₁ G i j)) (Matrix.ext fun p q => ?_)
  refine (GlobalTheory.BigDat.divG_gen (spW₁ G i j) β a s r p q).trans ?_
  rw [submatrix_apply, transpose_apply, GlobalTheory.BigDat.smul_incM_apply, vecMulVec_apply, mul_comm]
  simp

theorem mem_latAtV {t : T} {e : Num G i j} {Bs : Base D.host.F D.host.E} {Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j}
    {X : Chars D.host.F D.host.E} (h : IsDoublyCompatible t i j e Bs Γ X) {w : Pl D.host.E}
    (hw : ((D.host.QS * D.host.q * D.host.d * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal) {u : PtS G i j}
    (hu : At (evFin D.host.F (w.under (𝓞 D.host.F))) u) (hl : ptB e u ∈ homLatB G i j) :
    u ∈ latAtV Γ.V' Γ.W (w.under (𝓞 D.host.F)) := by
  obtain ⟨m, hm, hA⟩ := exists_nat_conj hw
  obtain ⟨hm0, hmi⟩ := inv_nat_mem hm
  set v := w.under (𝓞 D.host.F)
  have key : ∀ y ∈ homLatB G i j, GlobalTheory.LatVac.liftV v 1 • m • (ptE e).symm y ∈ latAtV Γ.V' Γ.W v := fun y hy => by
    refine GlobalTheory.BigDat.map_mem_of_closure ((DistribMulAction.toAddMonoidHom (PtS G i j) (GlobalTheory.LatVac.liftV v 1)).comp
      ((DistribMulAction.toAddMonoidHom (PtS G i j) m).comp (ptE e).symm.toLinearMap.toAddMonoidHom)) ?_ hy
    rintro _ ⟨α, hα, -, a, ha, s, hs, r, hr, rfl⟩
    have e1 : m • (pairA D.host.F 0 α) • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F
        (vecMulVec (star s) fun q => a * r (finSumFinEquiv (e.symm q))) = (pairA D.host.F 0 α) • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F
        (vecMulVec (star s) fun q => (m * a) * r (finSumFinEquiv (e.symm q))) := by
      ext p q
      rw [Matrix.smul_apply, GlobalTheory.BigDat.smul_incM_apply, GlobalTheory.BigDat.smul_incM_apply, vecMulVec_apply, vecMulVec_apply,
        ← TensorProduct.tmul_smul, nsmul_eq_mul]
      congr 1
      ring
    refine (congrArg (fun z => GlobalTheory.LatVac.liftV v 1 • z ∈ latAtV Γ.V' Γ.W v)
      ((congrArg (m • ·) (symm_gen e (pairA _ 0 α) a s r)).trans e1)).mpr
      (GlobalTheory.BigDat.one_smul_gen_mem _ _ v hα (h.2.ge (GlobalTheory.BigDat.star_mem_conjSub hs)) (h.1.2.1.ge ?_))
    rw [GlobalTheory.SkewLat.mem_pairLat]
    simp only [Equiv.symm_apply_apply]
    have hma : (m : D.host.E) * a ∈ D.host.AA := by
      have := D.host.AA.1.smul_mem (m : 𝓞 D.host.E) ha
      rwa [Algebra.smul_def, map_natCast] at this
    refine ⟨GlobalTheory.BigDat.smul_mem_scLat_of_mem hma hr.1, ?_⟩
    have := GlobalTheory.BigDat.star_mem_conjSub (GlobalTheory.BigDat.smul_mem_scLat_of_mem (hA a ha) (GlobalTheory.BigDat.star_mem_conjSub hr.2))
    rwa [star_smul, star_star, star_star] at this
  have h1 := (GlobalTheory.LatVac.latAtV_at_stable Γ.V' Γ.W v).2 _ hmi _ (key _ hl)
  rw [← ptE_apply, LinearEquiv.symm_apply_apply, smul_comm _ m, liftV_smul hu, smul_comm, ← smul_assoc, ← map_nsmul,
    nsmul_eq_mul, mul_inv_cancel₀ hm0, liftV_smul hu] at h1
  exact h1

end Pt

section Co

variable {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc}

def atC (w : Pl D.host.E) : AE D →+* Kw w := (atW w).comp (cA D)

theorem atC_cA (w : Pl D.host.E) (a : AE D) : atC w (cA D a) = atW w a := congrArg (atW w) (GlobalTheory.DualPairCheck.cA_cA a)

theorem adj_eq (S X : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βX : GL (Fin X.rank) (EAf D)) (w : Pl D.host.E) (y : WO S X) :
    (frMapAdj S X βS βX y).map (cpt w) = ((βS⁻¹).val.map (cpt w) * ((S.gram⁻¹).map (incA D)).map (atW w)) *
      ((y : Matrix (Fin X.rank) (Fin S.rank) (AE D)).map (atC w))ᵀ * ((X.gram.map (incA D)).map (atW w) * βX.val.map (cpt w)) := by
  unfold frMapAdj
  rw [Matrix.map_mul, Matrix.map_mul, Matrix.map_mul (f := toEAf D), Matrix.map_mul (f := toEAf D), Matrix.map_mul, Matrix.map_mul]
  simp only [Matrix.mul_assoc]
  rfl

theorem adj_surj (S X : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βX : GL (Fin X.rank) (EAf D)) (w : Pl D.host.E)
    (z : Matrix (Fin S.rank) (Fin X.rank) (Kw w)) :
    ∃ y : WO S X, IsHalf (cA D (atPl w 1)) y ∧ (frMapAdj S X βS βX y).map (cpt w) = z := by
  have h1 : ((βS⁻¹).val.map (cpt w) * ((S.gram⁻¹).map (incA D)).map (atW w)) *
      ((S.gram.map (incA D)).map (atW w) * βS.val.map (cpt w)) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (Matrix.map _ (atW w)), ← Matrix.map_mul, GlobalTheory.SquareAgree.HeisCov.gram_inv_mul,
      Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul, ← Matrix.map_mul, Units.inv_mul,
      Matrix.map_one _ (map_zero _) (map_one _)]
  have h2 : ((βX⁻¹).val.map (cpt w) * ((X.gram⁻¹).map (incA D)).map (atW w)) *
      ((X.gram.map (incA D)).map (atW w) * βX.val.map (cpt w)) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (Matrix.map _ (atW w)), ← Matrix.map_mul, GlobalTheory.SquareAgree.HeisCov.gram_inv_mul,
      Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul, ← Matrix.map_mul, Units.inv_mul,
      Matrix.map_one _ (map_zero _) (map_one _)]
  obtain ⟨y₀, hy₀⟩ : ∃ y₀ : Matrix (Fin S.rank) (Fin X.rank) (Kw w), y₀ = ((S.gram.map (incA D)).map (atW w) * βS.val.map (cpt w)) * z *
    ((βX⁻¹).val.map (cpt w) * ((X.gram⁻¹).map (incA D)).map (atW w)) := ⟨_, rfl⟩
  refine ⟨y₀ᵀ.map fun a => cA D (atPl w a), fun p q => ?_, ?_⟩
  · rw [map_apply, ← RingHom.map_mul, atPl_one_mul]
  · have e : ((y₀ᵀ.map fun a => cA D (atPl w a)).map (atC w))ᵀ = y₀ :=
      Matrix.ext fun p q => (atC_cA w _).trans (atW_atPl_self w _)
    rw [adj_eq, e, hy₀, ← Matrix.mul_assoc _ (_ * z), ← Matrix.mul_assoc _ _ z, h1, Matrix.one_mul, Matrix.mul_assoc, h2,
      Matrix.mul_one]

variable (B : Frames G) (t : T) (i j : Fin D.R.m) (w : Pl D.host.E)

theorem linB_add (x y : WO (spW₁ G i j) (spX G i j)) : linB B t i j w (x + y) = linB B t i j w x + linB B t i j w y := by
  unfold linB
  rw [adj_eq, adj_eq, adj_eq, Matrix.map_add _ (map_add _), transpose_add, Matrix.mul_add, Matrix.add_mul]
  rfl

theorem linB_surj (z : MatB G t i j w) : ∃ y, IsHalf (cA D (atPl w 1)) y ∧ linB B t i j w y = z := by
  obtain ⟨y, h1, h2⟩ := adj_surj (spW₁ G i j) (spX G i j) (B.β i j) (frX B i j) w
    ((reindex (finCongr (rankW₁ G t i j w)) (colX G t i j w)).symm z)
  exact ⟨y, h1, (congrArg _ h2).trans (Equiv.apply_symm_apply _ z)⟩

theorem linB_smul (y : WO (spW₁ G i j) (spX G i j)) : linB B t i j w (cA D (atPl w 1) • y) = linB B t i j w y := by
  have e : (cA D (atPl w 1) • y).map (atC w) = y.map (atC w) := Matrix.ext fun p q => by
    rw [map_apply, map_apply, Matrix.smul_apply, smul_eq_mul, RingHom.map_mul, atC_cA, atW_atPl_self, one_mul]
  unfold linB
  rw [adj_eq, adj_eq, e]

theorem linB_ne {w' : Pl D.host.E} (h : w ≠ w') {y : WO (spW₁ G i j) (spX G i j)} (hy : IsHalf (cA D (atPl w' 1)) y) :
    linB B t i j w y = 0 := by
  have e : y.map (atC w) = 0 := Matrix.ext fun p q => by
    rw [map_apply, ← hy p q, RingHom.map_mul, atC_cA, atW_atPl_ne h, zero_mul, Matrix.zero_apply]
  unfold linB
  rw [adj_eq, e, transpose_zero, Matrix.mul_zero, Matrix.zero_mul]
  rfl

end Co

section Vac

variable {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc} {i j : ℕ}

theorem vac_fixed_half {W : G.Weil} {M : Vol G} {t : T} {e : Num G i j} {Bs : Base D.host.F D.host.E}
    {Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j} {X : Chars D.host.F D.host.E} {om : Rep D.sp.cm.sig Γ.V Γ.W} {om' : Rep D.sp.cm.sig Γ.V' Γ.W}
    (h : IsTripleOf W M t i j e Bs Γ X) (hT : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ X om om') {v : Pl D.host.F} {γ : PtS G i j}
    (hγ : γ ∈ latAtV Γ.V' Γ.W v) {b : AE D} (hb : b * cA D b = 0) (hh : IsHalf b (ptB e γ)) :
    Acts (evFin D.host.F v) (Γ.M'.co.rho W.ψ γ) (Γ.M'.vac v) (Γ.M'.vac v) := by
  obtain ⟨-, -, θ, -, hθ⟩ := hT.geo.hM'.vac v
  have h1 := hθ γ hγ
  have h0 : GlobalTheory.WeilM.hTens (R := AF D.host.F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.V'.J)
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.W.J) γ γ = 0 := by
    have hl : ∀ p q, b * γ p q = γ p q := fun p q => congrFun (congrFun (smul_of_half e hh) p) q
    unfold GlobalTheory.WeilM.hTens
    refine Finset.sum_eq_zero fun p _ => Finset.sum_eq_zero fun q _ => Finset.sum_eq_zero fun k _ =>
      Finset.sum_eq_zero fun l _ => ?_
    have u : cA D b * cA D (γ k l) = cA D (γ k l) := by rw [← RingHom.map_mul, hl]
    change γ p q * _ * _ * cA D (γ k l) = 0
    rw [← u, ← hl p q]
    linear_combination (γ p q * GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.V'.J p k * GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.W.J q l *
      cA D (γ k l)) * hb
  unfold GlobalTheory.WeilM.symp at h1
  rw [h0, mul_zero, map_zero, mul_zero, AddChar.map_zero_eq_one, one_smul, h.ψ] at h1
  exact h1

theorem halves (e : Num G i j) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (hW : Γ.V'.J = (-1 : D.host.E) • (spW₁ G i j).gram)
    (hWW : Γ.W.J = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.skewGram (spV G i j) (spV₁ G i j) e) {ψ : AddChar (AF D.host.F) ℂ} (hstd : IsStdChar D ψ (-1))
    (hS : IsSelfDualC (spW₁ G i j) (G.Λ (.grid i j))) (hX : IsSelfDualC (spX G i j) (latX G i j)) (v : Pl D.host.F) {c : AE D}
    (hc : IsSplitIdem D c) (hsum : c + cA D c = algebraMap (AF D.host.F) (AE D) (GlobalTheory.LatVac.liftV v 1)) :
    (∀ u : PtS G i j, IsHalf (cA D c) (ptB e u) → At (evFin D.host.F v) u) ∧
    (∀ u : PtS G i j, IsHalf c (ptB e u) → At (evFin D.host.F v) u) ∧
    (∀ u : PtS G i j, At (evFin D.host.F v) u → ∃ x, IsHalf (cA D c) (ptB e x) ∧ ∃ y, IsHalf c (ptB e y) ∧ u = x + y) ∧
    (∀ x : PtS G i j, IsHalf (cA D c) (ptB e x) → (∀ y, At (evFin D.host.F v) y ∧ ptB e y ∈ homLatB G i j → IsHalf c (ptB e y) →
      ψ (sympS Γ x y) = 1) → At (evFin D.host.F v) x ∧ ptB e x ∈ homLatB G i j) ∧
    ∀ u : PtS G i j, IsHalf (cA D c) (ptB e (cA D c • u)) ∧
      (∀ y, IsHalf c (ptB e y) → sympS Γ u y = sympS Γ (cA D c • u) y) ∧
      (ptB e u ∈ homLatB G i j → ptB e (cA D c • u) ∈ homLatB G i j) := by
  obtain ⟨haa, hac, -⟩ := hc
  have hcc : cA D c * cA D c = cA D c := by rw [← RingHom.map_mul, haa]
  have hca : cA D c * c = 0 := by rw [mul_comm, hac]
  have ha1 : c * algebraMap (AF D.host.F) (AE D) (GlobalTheory.LatVac.liftV v 1) = c := by
    rw [← hsum, mul_add, haa, hac, add_zero]
  have hc1 : cA D c * algebraMap (AF D.host.F) (AE D) (GlobalTheory.LatVac.liftV v 1) = cA D c := by
    rw [← hsum, mul_add, hca, hcc, zero_add]
  have hfa : finPart D c ∈ intAE D := GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← map_mul, haa])
  have hfc : finPart D (cA D c) ∈ intAE D := GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← map_mul, hcc])
  have hp : ∀ {b : AE D}, b * b = b → ∀ u : PtS G i j, IsHalf b (ptB e (b • u)) := fun hb u => by
    rw [ptB_smul]; exact isHalf_smul_self hb _
  have hs : ∀ x y : WO (spW₁ G i j) (spX G i j), symplO _ _ x (c • y) = symplO _ _ (cA D c • x) y := fun x y => by
    rw [← symplO_cA_smul, GlobalTheory.DualPairCheck.cA_cA]
  refine ⟨fun u hu => at_of_half e v hc1 hu, fun u hu => at_of_half e v ha1 hu, fun u hu =>
    ⟨_, hp hcc u, _, hp haa u, ?_⟩, fun x hx hψ => ⟨at_of_half e v hc1 hx, ?_⟩, fun u => ⟨hp hcc u, fun y hy => ?_, fun hu => ?_⟩⟩
  · rw [← add_smul, add_comm (cA D c), hsum, algebraMap_smul, liftV_smul hu]
  · refine GlobalTheory.LatVac.mem_of_char hstd hS hX (map_infPart_of_isHalf v hc1 hx) fun l hl => ?_
    have := hψ (c • (ptE e).symm l) ⟨at_of_half e v ha1 (hp haa _), by
      rw [ptB_smul, ptB_symm]; exact GlobalTheory.LatticeStable.smul_mem_latO D _ _ _ _ _ _ hfa l hl⟩ (hp haa _)
    rwa [sympS_ptB e Γ hW hWW, ptB_smul, ptB_symm, hs, smul_of_isHalf hx] at this
  · rw [sympS_ptB e Γ hW hWW, sympS_ptB e Γ hW hWW, ptB_smul, ← hs, smul_of_isHalf hy]
  · rw [ptB_smul]
    exact GlobalTheory.LatticeStable.smul_mem_latO D _ _ _ _ _ _ hfc _ hu

end Vac

set_option maxHeartbeats 1600000 in

theorem isDatum_linB : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc} {μ₀ : T}, L.Is μ₀ → ∀ (W : G.Weil) (B : Frames G) (t : T) (i j : Fin D.R.m) (M : Vol G), SquareStanding G t →
    ∀ (e : Num G i j) (Bs : Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (X : Chars D.host.F D.host.E)
      (om : Rep D.sp.cm.sig Γ.V Γ.W) (om' : Rep D.sp.cm.sig Γ.V' Γ.W), IsTripleOf W M t i j e Bs Γ X →
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ X om om' → IsDoublyCompatible t i j e Bs Γ X → ∀ (ρ : RealMatch W) f₀,
      GlobalTheory.SquareAgree.IsDatum Γ.M' W.ψ (ptB e) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f₀ Γ.M'.vac) (vacB ρ i j) →
      ∀ ι : ∀ w, ToB G t i j w, (∀ w ∈ locPl G t, IsLinModelB W B t e Γ w (ι w)) →
      ∀ ε, IsIdemSum ε (locPl G t) → ∀ Ψ F, IsLinB B t i j ρ ε Ψ F →
      ∀ φ, IsFinPart Γ.M' X.T φ → (∀ w ∈ locPl G t, ι w (φ (w.under (𝓞 D.host.F))) = Ψ w) →
        GlobalTheory.SquareAgree.IsDatum Γ.M' W.ψ (ptB e) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure ((∏ w ∈ locPl G t, ι w (Γ.M'.vac _) 0) • f₀) φ) F := by
  intro D T L sc G μ₀ hL W B t i j M hst e Bs Γ X om om' h hT hti ρ f hf₀ I hI ε hε Ψ F hF φ hφ hΨ
  classical
  have hstd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd W.ψ := h.ψ ▸ hT.base.std
  have hG : Γ.M'.IsGood W.ψ := h.ψ ▸ hT.geo.hM'
  have hadd : ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F (IxS G i j), ∀ Φ' ∈ GlobalTheory.WeilM.schA D.host.F (IxS G i j),
      thetaS Γ W.ψ (Φ + Φ') = thetaS Γ W.ψ Φ + thetaS Γ W.ψ Φ' := fun Φ hΦ Φ' hΦ' => funext fun u =>
    (tsum_congr fun _ => mul_add _ _ _).trans
      ((GlobalTheory.WeilM.summable_of_mem_schA _ (GlobalTheory.HeisSchA.rho_mem_schA Γ.M' W.ψ hstd u _ hΦ)).tsum_add
        (GlobalTheory.WeilM.summable_of_mem_schA _ (GlobalTheory.HeisSchA.rho_mem_schA Γ.M' W.ψ hstd u _ hΦ')))
  obtain ⟨hid, hsumid⟩ := GlobalTheory.IdemAtPl.main hL (G := G) t
  have sW : IsSelfDualC (spW₁ G i j) (G.Λ (.grid i j)) := (node_isV G hL (X := .grid i j) ⟨i.2.le, j.2.le⟩).sd
  have sX : IsSelfDualC (spX G i j) (latX G i j) := GlobalTheory.Twist.OrthSum.selfDual_hsum
    (node_isV G hL (X := .grid i (j + 1)) ⟨i.2.le, j.2⟩).sd (node_isV G hL (X := .grid (i + 1) j) ⟨i.2, j.2.le⟩).sd
  have hh := fun w hw => halves e Γ h.JW₁ h.JWW W.ψ_std sW sX _ (hid w hw).1 (hid w hw).2
  have hv := fun w hw => GlobalTheory.SmallPlaces.lagr_vac (hI w hw) (hG.vac _).1 (hG.vac _).2.1
    {u | At (evFin D.host.F (w.under (𝓞 D.host.F))) u ∧ ptB e u ∈ homLatB G i j}
    (fun γ hγ hγ' => hγ'.elim
      (fun h' => vac_fixed_half h hT (mem_latAtV hti (hst.2 w hw) hγ.1 hγ.2) (GlobalTheory.SmallPlaces.splitIdem_conj (hid w hw).1).2.1 h')
      fun h' => vac_fixed_half h hT (mem_latAtV hti (hst.2 w hw) hγ.1 hγ.2) (hid w hw).1.2.1 h')
    (fun z => let ⟨y, h1, h2⟩ := linB_surj B t i j w z
      ⟨(ptE e).symm y, (congrArg (IsHalf _) (ptB_symm e y)).mpr h1, (congrArg (linB B t i j w) (ptB_symm e y)).trans h2⟩)
    (hh w hw).2.2.2.1
  set c := ∏ w ∈ locPl G t, I w (Γ.M'.vac _) 0 with hc
  have hb : thetaS Γ W.ψ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (c • f) Γ.M'.vac) = fun u => (c • vacB ρ i j) (ptB e u) :=
    funext fun u => (congrArg (thetaS Γ W.ψ · u) (funext fun _ => mul_assoc _ _ _)).trans
      ((thetaS_smul _ _ _ _ u).trans (congrArg (c * ·) (hf₀.2 u)))
  obtain ⟨⟨T₁, hT₁⟩, hall⟩ := hF
  obtain ⟨hεs, hεw⟩ := hsumid ε hε
  have hinf : infPart D ε = 0 := GlobalTheory.PlaceVec.idemSum_infPart hε
  have hcε : cA D (cA D ε) = ε := GlobalTheory.DualPairCheck.cA_cA ε
  let R : Submodule ℂ ((PtS G i j → ℂ) × ((IxS G i j → AF D.host.F) → ℂ)) :=
    { carrier := {p | p.2 ∈ GlobalTheory.WeilM.schA D.host.F _ ∧ ∃ g, IsSBHalf (cA D ε) (homLatB G i j) g ∧ p.1 = (fun u => g (ptB e u)) ∧
        thetaS Γ W.ψ p.2 = fun u => T₁ g (ptB e u)}
      zero_mem' := ⟨zero_mem _, 0, sb_zero _ _, rfl, funext fun u => by
        rw [map_zero]; simpa using thetaS_smul Γ W.ψ 0 0 u⟩
      add_mem' := fun {p q} ⟨hp, g, g1, g2, g3⟩ ⟨hq, k, k1, k2, k3⟩ => ⟨add_mem hp hq, g + k, sb_add g1 k1, by
        rw [Prod.fst_add, g2, k2]; rfl, by
        rw [Prod.snd_add, hadd _ hp _ hq, g3, k3, map_add]; rfl⟩
      smul_mem' := fun a p ⟨hp, g, g1, g2, g3⟩ => ⟨Submodule.smul_mem _ a hp, a • g, sb_smul a g1, by
        rw [Prod.smul_fst, g2]; rfl, funext fun u => by
        rw [Prod.smul_snd, thetaS_smul, g3, map_smul]; rfl⟩ }
  let H : AddSubgroup (PtS G i j) := (GlobalTheory.PlaceModel.half _ _ (cA D ε)).comap (ptE e).toLinearMap.toAddMonoidHom
  have hH : ∀ u, u ∈ H ↔ IsHalf (cA D ε) (ptB e u) := fun u => (GlobalTheory.PlaceModel.isHalf_iff _ _).symm
  have hA : ∀ w ∈ locPl G t, ∀ x : WO (spW₁ G i j) (spX G i j), IsHalf (cA D (atPl w 1)) x → IsHalf (cA D ε) x :=
    fun w hw x hx => GlobalTheory.SmallPlaces.isHalf_mono (by rw [← RingHom.map_mul, hεw w hw]) hx
  have hA' : ∀ w ∈ locPl G t, ∀ x : WO (spW₁ G i j) (spX G i j), IsHalf (atPl w 1) x → IsHalf (cA D (cA D ε)) x :=
    fun w hw x hx => GlobalTheory.SmallPlaces.isHalf_mono (by rw [hcε, hεw w hw]) hx
  have hco : ∀ w u, linB B t i j w (ptB e (cA D (atPl w 1) • u)) = linB B t i j w (ptB e u) := fun w u => by
    rw [ptB_smul, linB_smul]
  have hbase : (Set.indicator (H : Set _) fun u => ∏ w ∈ locPl G t, I w (Γ.M'.vac _) (linB B t i j w (ptB e u))) =
      fun u => (c • halfInd (cA D ε) (homLatB G i j)) (ptB e u) := by
    funext u
    rw [Pi.smul_apply, smul_eq_mul, halfInd]
    by_cases hu : IsHalf (cA D ε) (ptB e u)
    · rw [Set.indicator_of_mem ((hH u).2 hu), Finset.prod_congr rfl fun w hw =>
        (congrArg _ (hco w u).symm).trans ((hv w hw).2 _ ((hh w hw).2.2.2.2 u).1)]
      by_cases hl : ptB e u ∈ homLatB G i j
      · rw [if_pos ⟨hl, hu⟩, mul_one]
        refine Finset.prod_congr rfl fun w hw => Set.indicator_of_mem ?_ _
        exact ⟨(hh w hw).1 _ ((hh w hw).2.2.2.2 u).1, ((hh w hw).2.2.2.2 u).2.2 hl⟩
      · have : ∃ w ∈ locPl G t, ptB e (cA D (atPl w 1) • u) ∉ homLatB G i j := by
          by_contra! hall
          refine hl (GlobalTheory.SmallPlaces.mem_of_sum_smul (P := locPl G t) (a := fun w => cA D (atPl w 1)) ?_
            fun w hw => (congrArg (· ∈ homLatB G i j) (ptB_smul e _ u)).mp (hall w hw))
          rw [← map_sum, ← hεs]
          exact hu
        obtain ⟨w, hw, hn⟩ := this
        rw [if_neg fun h' => hl h'.1, mul_zero]
        refine Finset.prod_eq_zero hw (Set.indicator_of_notMem ?_ _)
        exact fun h' => hn h'.2
    · rw [Set.indicator_of_notMem (mt (hH u).1 hu), if_neg fun h' => hu h'.2, mul_zero]
  have hR := GlobalTheory.InductLagr.rel_of_vac Γ.M' W.ψ hstd hG (locPl G t) (fun w => w.under (𝓞 D.host.F)) (Good.under_injOn hL G t) _
    (fun w => {u | IsHalf (cA D (atPl w 1)) (ptB e u)}) (fun w => {u | IsHalf (atPl w 1) (ptB e u)})
    (fun w u => linB B t i j w (ptB e u)) I H R (c • f)
    hI (fun w hw u hu => ⟨(hh w hw).1 u hu, (hH u).2 (hA w hw _ hu)⟩) (fun w hw => (hh w hw).2.1)
    (fun w hw => (hh w hw).2.2.1) (fun w _ x _ u => (congrArg _ (ptB_add e u x)).trans (linB_add B t i j w _ _))
    (fun w _ w' _ hne x hx u => (congrArg _ (ptB_add e u x)).trans ((linB_add B t i j w' _ _).trans
      ((congrArg _ (linB_ne B t i j w' hne hx)).trans (add_zero _))))
    (fun w hw u => ⟨_, ((hh w hw).2.2.2.2 u).1, hco w u, ((hh w hw).2.2.2.2 u).2.1⟩)
    (fun w hw x hx p ⟨hp, g, g1, g2, g3⟩ => ⟨GlobalTheory.HeisSchA.rho_mem_schA Γ.M' W.ψ hstd x _ hp, _,
      GlobalTheory.BigDat.GraphHeis.sb_trans_latO sW.1 sX.1 (GlobalTheory.PlaceVec.infPart_cA hinf) g1 (hA w hw _ hx),
      funext fun u => (congrFun g2 _).trans (congrArg g (ptB_add e u x)), by
        rw [hT₁.trans g g1 _ (hA w hw _ hx), ← heisS_ptB e Γ h.JW₁ h.JWW, ← g3]
        exact thetaS_rho Γ W.ψ p.2 x⟩)
    (fun w hw x hx p ⟨hp, g, g1, g2, g3⟩ => ⟨GlobalTheory.HeisSchA.rho_mem_schA Γ.M' W.ψ hstd x _ hp, _,
      GlobalTheory.BigDat.GraphHeis.sb_modul_latO W.ψ_std sW sX (hcε.symm ▸ hinf) g1 (hA' w hw _ hx),
      funext fun u => congrArg₂ (· * ·) (congrArg W.ψ (sympS_ptB e Γ h.JW₁ h.JWW u x)) (congrFun g2 u), by
        rw [hT₁.modul g g1 _ (hA' w hw _ hx), ← heisS_ptB e Γ h.JW₁ h.JWW, ← g3]
        exact thetaS_rho Γ W.ψ p.2 x⟩)
    ⟨(isFinPart_vac hG ∅).fam.mem hG _, _, sb_smul c (GlobalTheory.isSBHalf_halfInd _ _), hbase, by
      rw [map_smul, (congrArg T₁ (one_smul ℂ _).symm).trans hT₁.vac]
      exact hb⟩
    φ hφ.1 fun v hv => hφ.2 v fun hm => let ⟨w, hw, e⟩ := (hti.1.2.2.1 v).1 hm; hv w hw e
  obtain ⟨r1, g, -, g2, g3⟩ := hR
  have hg : g = prodB B t i j ε Ψ := funext fun y => by
    obtain ⟨u, rfl⟩ := (ptE e).surjective y
    refine (congrFun g2 u).symm.trans ?_
    rw [ptE_apply, prodB]
    dsimp only
    by_cases hu : IsHalf (cA D ε) (ptB e u)
    · rw [if_pos hu]
      rw [Set.indicator_of_mem ((hH u).2 hu)]
      exact Finset.prod_congr rfl fun w hw => congrFun (hΨ w hw) _
    · rw [if_neg hu]
      exact Set.indicator_of_notMem (mt (hH u).1 hu) _
  refine ⟨r1, fun u => ?_⟩
  rw [hall T₁ hT₁, ← hg]
  exact congrFun g3 u

end GlobalTheory.TopFlip.LinSmall

end
