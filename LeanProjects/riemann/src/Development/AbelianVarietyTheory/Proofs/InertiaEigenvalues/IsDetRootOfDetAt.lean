import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsIsScalar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.VacuumVectorDropAuxiliaryPlaces
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentMulAddOneSubInverse
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CardInversePrimeRepsIntegralRightMulHecke
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaVacuumHeckeIdentitySplitPlace
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SumHeckeIndicatorIntegralEqPrimitiveStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlaceChartFiniteAdeleTensorLevelsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SumUniversalDeterminantDatumCoeffEqPrimitiveStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ArtinMapSplitPlaceUniformiserEqFrobeniusInvStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ModulusUnramifiedCharDetHeckeDoubleCosetSplitStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryGroupCharacterOfHeckeChar
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergCombinationCommFockPolynomialVectors
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.VacuumVectorDropAuxiliaryPlacesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InvNatPowRpowNegHalfEvenEqPow
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.ExportSeries
open Formalism.L2.NTheta (IsIdemAt IsHeckeElt)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
noncomputable section

namespace GlobalTheory.DistRel
variable {D : D7} {S T : HSp D}
open Classical

theorem isDetRoot_of_detAt {e : AE D} (he : IsSplitIdem D e) {V : HSp D} {g : GA D V} (hg : SuppAt e V g) {x : (AE D)ˣ}
    (hx : IsDetAt e V g x) : IsDetRoot V g x := by
  have h1 : (cA D) (Formalism.L2.Theta.mt V g).det * (Formalism.L2.Theta.mt V g).det = 1 := by
    rw [mul_comm]; exact GlobalTheory.SplitDetCharacter.det_mul_conj V g
  have hd : (1 - (e + cA D e)) * (Formalism.L2.Theta.mt V g).det = (1 - (e + cA D e)) * (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)).det :=
    GlobalTheory.WeilSplit.mul_det_eq _ _ _ fun i j => by
      have := hg i j
      rw [Matrix.sub_apply] at this
      linear_combination (-1 : AE D) * this
  rw [Matrix.det_one, mul_one] at hd
  have e1 : e * e = e := he.1
  have e2 : e * cA D e = 0 := he.2.1
  have e3 : cA D e * cA D e = cA D e := by rw [← map_mul, e1]
  unfold IsDetRoot
  have hcx : cA D (x : AE D) = cA D e * cA D (Formalism.L2.Theta.mt V g).det + (1 - cA D e) := by
    rw [hx, map_add, map_mul, map_sub, map_one]
  rw [hcx, hx]
  change e * (Formalism.L2.Theta.mt V g).det + (1 - e) = (Formalism.L2.Theta.mt V g).det * (cA D e * cA D (Formalism.L2.Theta.mt V g).det + (1 - cA D e))
  set d := (Formalism.L2.Theta.mt V g).det
  linear_combination (-(cA D e)) * h1 - hd

theorem unram_at_gen {A : Type} [CommGroup A] {χ : (AE D)ˣ →* A} {Q S' : Finset (Pl D.host.E)} (hχ : UnramOutside χ Q)
    (hS : SplitSet S') (hQ : Q ⊆ S') {P : Pl D.host.E} (hP : P ∈ S') (hn : P ∉ Q) (y : (AE D)ˣ)
    (h1 : (1 - idemAt P) * (y : AE D) = 1 - idemAt P) (h2 : finPart D (idemAt P * (y : AE D)) ∈ intAE D)
    (h3 : finPart D (idemAt P * ((y⁻¹ : (AE D)ˣ) : AE D)) ∈ intAE D) : χ y = 1 := by
  have he := hS.isIdemAt hP
  have h1' : (1 - idemAt P) * ((y⁻¹ : (AE D)ˣ) : AE D) = 1 - idemAt P := by
    conv_lhs => rw [← h1, mul_assoc, Units.mul_inv, mul_one]
  have key : ∀ z : AE D, (1 - idemAt P) * z = 1 - idemAt P → finPart D (idemAt P * z) ∈ intAE D → finPart D z ∈ intAE D :=
    fun z a b => by
      have : z = idemAt P * z + 1 - idemAt P := by linear_combination a
      rw [this, RingHom.map_sub, RingHom.map_add, RingHom.map_one]
      exact sub_mem (add_mem b (GlobalTheory.SplitDivisors.one_mem_int D)) (finPart_idem_mem he)
  have hinf : infPart D (y : AE D) = 1 := by
    have h0 : infPart D (idemAt P) = 0 := GlobalTheory.StepVec.infPart_idemAt he
    have : (y : AE D) = idemAt P * (y : AE D) + (1 - idemAt P) := by linear_combination h1
    rw [this, RingHom.map_add, RingHom.map_mul, RingHom.map_sub, RingHom.map_one, h0]
    ring
  refine hχ y hinf (key _ h1 h2) (key _ h1' h3) ?_
  have h0 : idemAt P * (idem Q + cA D (idem Q)) = 0 := by
    rw [mul_add, idem, map_sum, Finset.mul_sum, Finset.mul_sum,
      Finset.sum_eq_zero fun j hj => hS.mul_eq_zero hP (hQ hj) fun e => hn (e ▸ hj),
      Finset.sum_eq_zero fun j hj => hS.mul_conj hP (hQ hj), add_zero]
  linear_combination (idem Q + cA D (idem Q)) * h1 + ((y : AE D) - 1) * h0

end GlobalTheory.DistRel

namespace GlobalTheory.DistRel
variable {D : D7} {S T : HSp D}
open Classical
open Formalism.IndefR.Links (PolF)

theorem fock_sum {F : Frame S T} (hF : F.Good) {ι : Type} (s : Finset ι) (f : ι → WO S T → ℂ)
    (hf : ∀ i, IsThetaFunO F.ψ S T (f i)) (Pol : PolF D T.rank S.rank) :
    IsThetaFunO F.ψ S T (∑ i ∈ s, f i) ∧ F.fock (∑ i ∈ s, f i) Pol = ∑ i ∈ s, F.fock (f i) Pol := by
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact ⟨GlobalTheory.OrientedHeis.theta_zero, GlobalTheory.FockFiniteHeis.pureTensorO_zero F.ψ F.θ S T hF.vac.1 hF.vac.2.inf _ _ _ _ Pol⟩
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    refine ⟨GlobalTheory.OrientedHeis.theta_add (hf i) ih.1, ?_⟩
    have := GlobalTheory.FockFiniteHeis.pureTensorO_lin F.ψ F.θ S T hF.vac.1 hF.vac.2.inf (fun _ => 1) (fun τ => (F.BS τ).val) F.sT F.BT
      1 (hf i) ih.1 Pol
    rw [one_smul, one_smul] at this
    unfold Frame.fock
    rw [this]
    unfold Frame.fock at ih
    rw [ih.2]

theorem series_sum {F : Frame S T} (hF : F.Good) (ω : PairRep S T) {ι : Type} (s : Finset ι) (f : ι → WO S T → ℂ)
    (hf : ∀ i, IsThetaFunO F.ψ S T (f i)) (h : GA D S) (Pol : PolF D T.rank S.rank) (g : GA D T) :
    series F ω (∑ i ∈ s, f i) h Pol g = ∑ i ∈ s, series F ω (f i) h Pol g := by
  simp only [series_apply, (fock_sum hF s f hf Pol).2, map_sum, Finset.sum_apply]

theorem series_smul (F : Frame S T) (ω : PairRep S T) (c : ℂ) (f : WO S T → ℂ) (h : GA D S) (Pol : PolF D T.rank S.rank)
    (g : GA D T) : series F ω (c • f) h Pol g = c * series F ω f h Pol g := by
  simp only [series_apply, Frame.fock, GlobalTheory.FiniteFock.pureTensorO_smul, map_smul, Pi.smul_apply, smul_eq_mul]

theorem series_translate {F : Frame S T} (hF : F.Good) {ω : PairRep S T} {χS χT : (AE D)ˣ →* Circle}
    (hω : IsWeilDatumO F.ψ S T χS χT ω) {f : WO S T → ℂ} (hf : IsThetaFunO F.ψ S T f) {γ : GA D T} (hγ : γ ∈ GfC T)
    (h : GA D S) (Pol : PolF D T.rank S.rank) (g : GA D T) :
    series F ω f h Pol (g * γ) = series F ω (ω (1, γ) f) h Pol g := by
  have k := (GlobalTheory.OrientedHeis.om_pureTensorO D F.ψ F.θ S T χS χT ω hω hF.vac.2.inf (fun _ => 1) (fun _ => 1)
    (fun τ => (F.BS τ).val) (fun τ => (F.BS τ).val) F.sT F.sT F.BT F.BT 1 γ
    (fun τ => by simp [GlobalTheory.FiniteFock.compAt_mt_of_finite _ τ (one_mem _)])
    (fun τ => by simp [GlobalTheory.FiniteFock.compAt_mt_of_finite _ τ hγ])
    (fun τ => by simp [GlobalTheory.FiniteFock.compAt_mt_of_finite _ τ (one_mem _)])
    (fun τ => by simp [GlobalTheory.FiniteFock.compAt_mt_of_finite _ τ hγ]) f hf Pol).2
  have e2 : ((h, g * γ) : GA D S × GA D T) = (h, g) * (1, γ) := by simp
  rw [series_apply, series_apply, e2, map_mul, Module.End.mul_apply]
  unfold Frame.fock
  rw [k]

end GlobalTheory.DistRel

namespace GlobalTheory.DistRel
variable {D : D7} {S T : HSp D}
open Classical

theorem sum_ext_prod {ι C : Type} [Fintype ι] [Fintype C] (i₀ : ι) (b : ι → C) (f : ι → C → ℂ) :
    ∑ c ∈ Finset.univ.filter (fun c : ι → C => ∀ i, i ≠ i₀ → c i = b i), ∏ i, f i (c i) =
      ∏ i, (if i = i₀ then ∑ c, f i c else f i (b i)) := by
  have h := (Finset.prod_univ_sum (fun i => if i = i₀ then (Finset.univ : Finset C) else {b i}) f).symm
  have hs : Fintype.piFinset (fun i => if i = i₀ then (Finset.univ : Finset C) else {b i}) =
      Finset.univ.filter (fun c : ι → C => ∀ i, i ≠ i₀ → c i = b i) := by
    ext c
    simp only [Fintype.mem_piFinset, Finset.mem_filter, Finset.mem_univ, true_and]
    refine forall_congr' fun i => ?_
    by_cases hi : i = i₀
    · simp [hi]
    · simp [hi]
  rw [← hs, h]
  refine Finset.prod_congr rfl fun i _ => ?_
  by_cases hi : i = i₀
  · rw [if_pos hi, if_pos hi]
  · rw [if_neg hi, if_neg hi, Finset.sum_singleton]

theorem vecAt_sum (B : Base S T) {Q : Finset (Pl D.host.E)} {P : Pl D.host.E} (hP : P ∈ Q) {C : Type} [Fintype C]
    (Φ : ∀ PP : Pl D.host.E, C → Matrix (Fin T.rank) (Fin S.rank) (kP PP) → ℂ) (b : ↥Q → C) :
    ∑ c ∈ Finset.univ.filter (fun c : ↥Q → C => ∀ v : ↥Q, v.1 ≠ P → c v = b v), B.vecAt Q (fun PP y => Φ PP.1 (c PP) y) =
      B.vecAt Q (fun PP y => if PP.1 = P then ∑ c, Φ PP.1 c y else Φ PP.1 (b PP) y) := by
  have e1 : ∀ φ : ∀ PP : ↥Q, Matrix (Fin T.rank) (Fin S.rank) (kP PP.1) → ℂ,
      B.vecAt Q φ = B.F.vecL B.G (B.de.Q ∪ Q) (B.locFn Q φ) := fun φ => rfl
  simp only [e1, ← map_sum]
  congr 1
  funext y
  rw [Finset.sum_apply]
  unfold Base.locFn
  rw [← Finset.mul_sum]
  congr 1
  have hf : Finset.univ.filter (fun c : ↥Q → C => ∀ v : ↥Q, v.1 ≠ P → c v = b v) =
      Finset.univ.filter (fun c : ↥Q → C => ∀ v, v ≠ ⟨P, hP⟩ → c v = b v) := by
    refine Finset.filter_congr fun c _ => forall_congr' fun v => ?_
    exact ⟨fun h hv => h fun e => hv (Subtype.ext e), fun h hv => h fun e => hv (congrArg Subtype.val e)⟩
  rw [hf]
  convert sum_ext_prod (⟨P, hP⟩ : ↥Q) b (fun v c => Φ v.1 c (y v.1)) using 1
  · congr 1
    ext c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  refine Finset.prod_congr rfl fun v _ => ?_
  dsimp only
  by_cases h : v.1 = P
  · rw [if_pos (Subtype.ext h), if_pos h]
  · rw [if_neg fun e => h (congrArg Subtype.val e), if_neg h]

end GlobalTheory.DistRel

namespace GlobalTheory.DistRel
variable {D : D7} {S T : HSp D}
open Classical
open Formalism.IndefR.Links (PolF)

theorem series_add {F : Frame S T} (hF : F.Good) (ω : PairRep S T) {f f' : WO S T → ℂ} (hf : IsThetaFunO F.ψ S T f)
    (hf' : IsThetaFunO F.ψ S T f') (h : GA D S) (Pol : PolF D T.rank S.rank) (g : GA D T) :
    series F ω (f + f') h Pol g = series F ω f h Pol g + series F ω f' h Pol g := by
  have := series_sum hF ω (Finset.univ : Finset Bool) (fun b => if b then f else f') (fun b => by cases b <;> simp [hf, hf']) h Pol g
  simpa [Fintype.sum_bool] using this

theorem theta_vecAt {B : Base S T} (hB : B.Good) {Q : Finset (Pl D.host.E)} (hQ : B.admitted Q)
    (φ : ∀ PP : ↥Q, Matrix (Fin T.rank) (Fin S.rank) (kP PP.1) → ℂ) : IsThetaFunO B.F.ψ S T (B.vecAt Q φ) :=
  GlobalTheory.GalLift.Vec.theta_of_thetaAt hB.frame.vac.1 hB.frame.vac.2.inf (Base.isThetaAt_vecAt hB hQ φ) hB.frame.vac.2.theta

theorem xi_rel (B : Base S T) (hB : B.Good) (hbT : Lev.IsBaseFrame T B.F.βT B.F.ΛT 1) {ω : PairRep S T}
    (hω : B.IsWeil 1 ω) {C : Type} [AddCommGroup C] [Fintype C] (u u' : UnivTwist D C)
    (β : ∀ PP : Pl D.host.E, DetBases (kP PP) T.rank S.rank) {Q Q' : Finset (Pl D.host.E)} (hQ : B.admitted Q) (hu : u.Good Q)
    (hu' : u'.Good Q') {P : Pl D.host.E} (hP : P ∈ Q) (hQ' : Q' ⊆ Q) (hQQ : ∀ v ∈ Q, v ∈ Q' ↔ v ≠ P)
    (hdel : ∀ v ∈ Q', u'.del v = u.del v) (hkap : ∀ v ∈ Q', u'.kap v = u.kap v)
    {ϖ : 𝓞 D.host.E} (hϖ1 : ϖ ∈ P.asIdeal) (hϖ2 : ϖ ∉ P.asIdeal ^ 2) (x : (AE D)ˣ)
    (hx : (x : AE D) = idemAt P * incA D (ϖ : D.host.E) + (1 - idemAt P))
    (α : ℕ → GA D T) (R : ℕ → Finset (GA D T))
    (hα : ∀ k ∈ Finset.Icc 1 T.rank, IsHeckeElt T (idemAt P) (ϖ : D.host.E) k (α k) ∧ (∀ γ ∈ R k, SuppAt (idemAt P) T γ) ∧
      Mult.IsCosetRep T (Mult.locPart T (KsphC T ∅) (idemAt P)) (α k) (R k))
    (h : GA D S) (Pol : PolF D T.rank S.rank) (a' : ↥Q' → C) (g : GA D T) :
    ∑ c ∈ Finset.univ.filter (fun c : ↥Q → C => ∀ v : ↥Q', c ⟨v.1, hQ' v.2⟩ = a' v),
        B.xiCoef ω u Q (Base.univFam u β) h Pol c g =
      B.xiCoef ω u' Q' (Base.univFam u' β) h Pol a' g +
        ∑ k ∈ Finset.Icc 1 T.rank, ((-1 : ℂ) ^ k * ((Ideal.absNorm P.asIdeal : ℕ) : ℂ) ^ (k * (k - 1) / 2) *
          (((B.mu x : Circle) : ℂ) ^ k * ((Ideal.absNorm P.asIdeal : ℕ) : ℂ) ^ (k * (S.rank / 2)))⁻¹) *
          ∑ γ ∈ R k, B.xiCoef ω u' Q' (Base.univFam u' β) h Pol (a' + k • Multiplicative.toAdd (u'.delQ Q' x)) (g * γ) := by
  obtain ⟨S', -, hq', hS'⟩ := hQ.1.split
  have he : IsIdemAt (idemAt P) P := hS'.isIdemAt (hq' (Finset.mem_union_right _ hP))
  set dQ : ↥Q → C := Multiplicative.toAdd (detChar T (u.delQ Q) g) with hdQ
  set dQ' : ↥Q' → C := Multiplicative.toAdd (detChar T (u'.delQ Q') g) with hdQ'
  have hres : ∀ v : ↥Q', dQ ⟨v.1, hQ' v.2⟩ = dQ' v := fun v => by
    simp only [hdQ, hdQ', detChar, UnivTwist.delQ, MonoidHom.coe_mk, OneHom.coe_mk, toAdd_ofAdd]
    rw [hdel v.1 v.2]
  set b0 : ↥Q → C := fun v => if hv : v.1 ∈ Q' then a' ⟨v.1, hv⟩ - dQ' ⟨v.1, hv⟩ else 0 with hb0
  set Φ : ∀ PP : Pl D.host.E, C → Matrix (Fin T.rank) (Fin S.rank) (kP PP) → ℂ :=
    fun PP c y => ((Base.univFam u β PP c y : ℚ) : ℂ) with hΦ

  have s1 : ∑ c ∈ Finset.univ.filter (fun c : ↥Q → C => ∀ v : ↥Q', c ⟨v.1, hQ' v.2⟩ = a' v),
      B.xiCoef ω u Q (Base.univFam u β) h Pol c g =
      ∑ b ∈ Finset.univ.filter (fun c : ↥Q → C => ∀ v : ↥Q, v.1 ≠ P → c v = b0 v),
        series B.F ω (B.vecAt Q fun PP y => Φ PP.1 (b PP) y) h Pol g := by
    refine Finset.sum_equiv (Equiv.subRight dQ) (fun c => ?_) (fun c _ => ?_)
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and, Equiv.subRight_apply, Pi.sub_apply]
      constructor
      · intro hc v hv
        have hv' := (hQQ v.1 v.2).2 hv
        have := hc ⟨v.1, hv'⟩
        simp only [hb0, dif_pos hv']
        rw [← this, ← hres ⟨v.1, hv'⟩]
      · intro hc w
        have hw : w.1 ≠ P := (hQQ w.1 (hQ' w.2)).1 w.2
        have := hc ⟨w.1, hQ' w.2⟩ hw
        simp only [hb0, dif_pos w.2, hres] at this
        rw [sub_left_inj] at this
        exact this
    · rw [Base.xiCoef_apply]
      rfl

  have htheta : ∀ b : ↥Q → C, IsThetaFunO B.F.ψ S T (B.vecAt Q fun PP y => Φ PP.1 (b PP) y) := fun b => theta_vecAt hB hQ _
  rw [s1, ← series_sum hB.frame ω _ _ (fun b => htheta b) h Pol g, vecAt_sum B hP Φ b0]
  set φ : ∀ PP : Pl D.host.E, Matrix (Fin T.rank) (Fin S.rank) (kP PP) → ℂ :=
    fun PP y => if hP' : PP ∈ Q then Φ PP (b0 ⟨PP, hP'⟩) y else 0 with hφ
  have hv1 : B.vecAt Q (fun PP y => if PP.1 = P then ∑ c, Φ PP.1 c y else Φ PP.1 (b0 PP) y) =
      B.vecAt Q (fun PP y => if PP.1 = P then ((prim y : ℚ) : ℂ) else φ PP.1 y) := by
    congr 1
    funext PP y
    by_cases hPP : PP.1 = P
    · rw [if_pos hPP, if_pos hPP]
      simp only [hΦ, Base.univFam]
      rw [← Rat.cast_sum, GlobalTheory.T.sum_universalDeterminantDatumCoeff_eq_primitive (kP PP.1) C T.rank S.rank B.hr (β PP.1) (u.kap PP.1) y]
    · rw [if_neg hPP, if_neg hPP, hφ]
      simp only [dif_pos PP.2]
  rw [hv1, vec_rel B hB hbT hω hQ hP φ hϖ1 hϖ2 x hx α R hα]

  set f1 := B.vecAt Q fun PP y => if PP.1 = P then 1 else φ PP.1 y with hf1
  have hf1' : f1 = B.vecFam Q' (Base.univFam u' β) (a' - dQ') := by
    rw [hf1, Base.vecFam]
    have := GlobalTheory.T.vacuumVector_drop_auxiliary_places D S T B Q Q' (fun v y => if hv : v ∈ Q' then ((Base.univFam u' β v ((a' - dQ') ⟨v, hv⟩) y : ℚ) : ℂ)
      else 0) hB hQ hQ'
    convert this using 2
    · funext PP y
      by_cases hPP : PP.1 = P
      · rw [if_pos hPP, if_neg (fun h => ((hQQ PP.1 PP.2).1 h) hPP)]
      · have hm := (hQQ PP.1 PP.2).2 hPP
        rw [if_neg hPP, if_pos hm, dif_pos hm, hφ]
        simp only [dif_pos PP.2, hb0, dif_pos hm, hΦ, Base.univFam, hkap PP.1 hm, Pi.sub_apply]
    · funext PP y
      rw [dif_pos PP.2]
  have hth1 : IsThetaFunO B.F.ψ S T f1 := theta_vecAt hB hQ _
  have hom : ∀ γ : GA D T, IsThetaFunO B.F.ψ S T (ω (1, γ) f1) := fun γ => hω.om_pres _ _ hth1

  have hlin : series B.F ω (f1 + ∑ k ∈ Finset.Icc 1 T.rank, ((-1 : ℂ) ^ k * ((Ideal.absNorm P.asIdeal : ℕ) : ℂ) ^ (k * (k - 1) / 2) *
      (((B.mu x : Circle) : ℂ) ^ k * ((Ideal.absNorm P.asIdeal : ℕ) : ℂ) ^ (k * (S.rank / 2)))⁻¹) •
        ∑ γ ∈ R k, ω (1, γ) f1) h Pol g = series B.F ω f1 h Pol g +
      ∑ k ∈ Finset.Icc 1 T.rank, ((-1 : ℂ) ^ k * ((Ideal.absNorm P.asIdeal : ℕ) : ℂ) ^ (k * (k - 1) / 2) *
        (((B.mu x : Circle) : ℂ) ^ k * ((Ideal.absNorm P.asIdeal : ℕ) : ℂ) ^ (k * (S.rank / 2)))⁻¹) *
        ∑ γ ∈ R k, series B.F ω (ω (1, γ) f1) h Pol g := by
    have t1 : ∀ k, IsThetaFunO B.F.ψ S T (∑ γ ∈ R k, ω (1, γ) f1) := fun k => (fock_sum hB.frame (R k) _ hom 0).1
    have t2 : ∀ k, IsThetaFunO B.F.ψ S T (((-1 : ℂ) ^ k * ((Ideal.absNorm P.asIdeal : ℕ) : ℂ) ^ (k * (k - 1) / 2) *
      (((B.mu x : Circle) : ℂ) ^ k * ((Ideal.absNorm P.asIdeal : ℕ) : ℂ) ^ (k * (S.rank / 2)))⁻¹) • ∑ γ ∈ R k, ω (1, γ) f1) :=
      fun k => GlobalTheory.OrientedHeis.theta_smul _ (t1 k)
    rw [series_add hB.frame ω hth1 (fock_sum hB.frame _ _ t2 0).1, series_sum hB.frame ω _ _ t2]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [series_smul, series_sum hB.frame ω _ _ hom]
  rw [hlin, Base.xiCoef_apply, ← hf1']
  congr 1
  refine Finset.sum_congr rfl fun k hk => ?_
  congr 1
  refine Finset.sum_congr rfl fun γ hγ => ?_
  have hγf : γ ∈ GfC T := ((hα k hk).2.2.1 γ hγ).1
  rw [← series_translate hB.frame hω hth1 hγf, Base.xiCoef_apply, hf1', Base.vecFam, Base.vecFam]

  have hsupp := (hα k hk).2.1 γ hγ
  obtain ⟨-, k₁, hk₁, k₂, hk₂, hγe⟩ := (hα k hk).2.2.1 γ hγ
  have hH := (GlobalTheory.T.modulus_unramifiedChar_det_heckeDoubleCoset_split D T P (idemAt P) he ϖ hϖ1 hϖ2 x hx k (α k) (hα k hk).1 k₁ hk₁ k₂ hk₂
    (GlobalTheory.VecInv.detAt (idemAt P) he.1.1 T γ) (by rw [← hγe]; exact GlobalTheory.VecInv.isDetAt_detAt _ he.1.1 T γ)).2
    (Multiplicative (↥Q' → C)) (u'.delQ Q') (fun y h1 h2 h3 => by
      ext v
      simp only [UnivTwist.delQ, MonoidHom.coe_mk, OneHom.coe_mk, toAdd_ofAdd, toAdd_one, Pi.zero_apply]
      rw [hdel v.1 v.2]
      have hv := (hu.2 v.1 (hQ' v.2)).unram
      have := unram_at_gen hv hu.1 (Finset.singleton_subset_iff.2 (hQ' v.2)) hP
        (fun hm => ((hQQ v.1 (hQ' v.2)).1 v.2) (Finset.mem_singleton.1 hm).symm) y h1 h2 h3
      rw [this]
      rfl)
  have hdet : Multiplicative.toAdd (detChar T (u'.delQ Q') γ) = k • Multiplicative.toAdd (u'.delQ Q' x) := by
    rw [detChar_eq hu'.delQ_real (isDetRoot_of_detAt he.1 hsupp (GlobalTheory.VecInv.isDetAt_detAt _ he.1.1 T γ)), hH, toAdd_pow]
  have key : a' + k • Multiplicative.toAdd (u'.delQ Q' x) - Multiplicative.toAdd (detChar T (u'.delQ Q') (g * γ)) = a' - dQ' := by
    rw [detChar_mul hu'.delQ_real, toAdd_mul, hdet]
    abel
  rw [key]

end GlobalTheory.DistRel
