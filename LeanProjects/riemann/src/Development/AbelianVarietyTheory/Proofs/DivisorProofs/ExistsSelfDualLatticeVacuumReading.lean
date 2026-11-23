import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodModModT
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemScaleLat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealExtendConjMulEqAbsNorm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaOfUnitVacuum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockVacuumRealRestrictionGaussianEntire
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MapFinNeg
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaLatticeImageRationalHomLattice
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaSpaceSelfDualPairAtMostLine
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsVacuumMovedThetaVacuum
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualLatticesConsecutiveStep
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSelfDualImageOrthonormalFrameLattice

open NumberField MeasureTheory IsDedekindDomain UniqueFactorizationMonoid
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum
open GlobalTheory.SqTop (modT)
open GlobalTheory.BottomIPData (sfB)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl Lat IsFockVec IsSphOff volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip)
open GlobalTheory.Core.Rk.IP (openOff integrand wcoef)
open GlobalTheory.StdLoc (glVol blockIdx)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.NormRatio

noncomputable section

namespace GlobalTheory.NormRatio.VacLat

open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U YYl homL)
open Formalism.MainNotions.StandardLatticesGL3 (stdL pt SD)
open GlobalTheory.InertSign (IntE RL)
open GlobalTheory.VacRead (cE)

section Copy

def posSig {D : D7} (S : HSp D) : HSp D := {S with sig := fun _ => (S.rank, 0)}

theorem hasSignature_one (n : ℕ) : Formalism.UG.HasSignature (1 : Matrix (Fin n) (Fin n) ℂ) n 0 := by
  refine ⟨(Equiv.sumEmpty (Fin n) (Fin 0)).symm, 1, ?_⟩
  ext i j
  rcases i with i | i
  · rcases j with j | j
    · simp [Formalism.UG.Jpq, Formalism.UG.cT, Matrix.one_apply]
    · exact j.elim0
  · exact i.elim0

theorem sigOK_posSig {D : D7} (S : HSp D) (h : S.gram = 1) : (posSig S).SigOK := by
  intro τ
  show Formalism.UG.HasSignature (S.gram.map τ) S.rank 0
  rw [h, Matrix.map_one _ (map_zero τ) (map_one τ)]
  exact hasSignature_one _

open scoped ComplexOrder in
theorem isCartanInv_one {D : D7} (S : HSp D) (h : S.gram = 1) (τ : D.what₂.Tau) : IsCartanInv (gramAt D S τ) 1 := by
  have : gramAt D S τ = 1 := by
    show (HSpace.gram S).map (tauE D τ) = 1
    rw [h, Matrix.map_one _ (map_zero _) (map_one _)]
  rw [this]
  exact ⟨by simp, by simp, by simpa using (Matrix.PosDef.one : Matrix.PosDef (1 : Matrix (Fin S.rank) (Fin S.rank) ℂ))⟩

theorem vac_exists_gram_one {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (hψ : IsStdChar D ψ (-1))
    (hθ : IsInfFam θ) (S T : HSp D) (gS : S.gram = 1) (gT : T.gram = 1)
    (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E))
    (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT) :
    ∃ f : WO S T → ℂ, IsVacO ψ θ S T (fun _ => 1) (fun _ => 1) ΛS ΛT f := by
  obtain ⟨f, hf⟩ := GlobalTheory.VacuumO.vacExists D ψ θ hψ hθ (posSig S) (posSig T) (fun _ => 1) (fun _ => 1)
    (sigOK_posSig S gS) (sigOK_posSig T gT) (isCartanInv_one S gS) (isCartanInv_one T gT) ΛS ΛT hS hT
  exact ⟨f, hf.1, ⟨hf.2.inf, ⟨hf.2.theta.quasi, hf.2.theta.level, hf.2.theta.cont, hf.2.theta.smooth⟩, hf.2.lat,
    hf.2.fock, hf.2.norm⟩⟩

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {r : D.host.E}

theorem Hf_div_scale (hc : Formalism.MainNotions.StandardLatticesGL3.Crv D cc δ) (h : IsScale D cc r) {a d : ℕ} (z x : VC D a d) :
    Hf D (tor0 D D.host.ccK δ) (fun τ i j => z τ i j / embT D τ r) (fun τ i j => x τ i j / embT D τ r) =
      Hf D (tor0 D cc δ) z x := by
  have hr : r ≠ 0 := IsScale.ne_zero hc.1.1 h
  have hA := area_pos hc
  have hx := xiR_pos D
  have key : ∀ τ, Complex.normSq (embT D τ r) * area (lamOf D D.host.ccK δ) = area (lamOf D cc δ) := by
    intro τ
    have h1 := normSq_scale hc.1.1 h δ τ
    have h2 := normSq_scale D.host.ccK_ne_bot (isScale_one D) δ τ
    rw [map_one, mul_one] at h2
    rw [Complex.normSq_mul, h2] at h1
    have h3 : (2 * Formalism.L2.Pj.xiR D) * (Complex.normSq (embT D τ r) * area (lamOf D D.host.ccK δ)) =
        (2 * Formalism.L2.Pj.xiR D) * area (lamOf D cc δ) := by rw [← h1]; ring
    exact mul_left_cancel₀ (by positivity) h3
  have hL : ∀ c : Ideal (𝓞 D.host.K), (tor0 D c δ).abelian₂ = lamOf D c δ := fun _ => rfl
  rw [Formalism.MainNotions.TaylorLogMetric.Hf, Formalism.MainNotions.TaylorLogMetric.Hf, hL, hL, Finset.sum_div, Finset.sum_div]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [Finset.sum_div, Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_div, Finset.sum_div]
  refine Finset.sum_congr rfl fun j _ => ?_
  have ht : embT D τ r ≠ 0 := (map_ne_zero _).2 hr
  have htc : starRingEnd ℂ (embT D τ r) ≠ 0 := (map_ne_zero _).2 ht
  have hK : (area (lamOf D D.host.ccK δ) : ℂ) ≠ 0 := by
    have : 0 < area (lamOf D D.host.ccK δ) := by
      have := key τ
      have h0 : 0 < Complex.normSq (embT D τ r) := Complex.normSq_pos.2 ht
      nlinarith
    exact_mod_cast this.ne'
  rw [← key τ, map_div₀]
  push_cast
  rw [← Complex.mul_conj]
  field_simp

theorem th_div_scale (hc : Formalism.MainNotions.StandardLatticesGL3.Crv D cc δ) (h : IsScale D cc r) {a d : ℕ}
    {L Ls : GlobalTheory.InertSign.Lat D a} {L' Lt : GlobalTheory.InertSign.Lat D d}
    (hLa : ∀ x ∈ Formalism.MainNotions.TaylorLogMetric.La D (tor0 D cc δ) L L',
      (fun τ i j => x τ i j / embT D τ r) ∈ Formalism.MainNotions.TaylorLogMetric.La D (tor0 D D.host.ccK δ) Ls Lt)
    {Φ : VC D a d → ℂ} (hΦ : Φ ∈ Th D (tor0 D D.host.ccK δ) Ls Lt) :
    (fun Y => Φ (fun τ i j => Y τ i j / embT D τ r)) ∈ Th D (tor0 D cc δ) L L' := by
  refine ⟨?_, ?_⟩
  · have hl : Differentiable ℂ (fun Y : VC D a d => (fun τ i j => Y τ i j / embT D τ r : VC D a d)) := by
      fun_prop
    exact hΦ.1.comp hl
  · intro x hx z
    have e1 := hΦ.2 _ (hLa x hx) (fun τ i j => z τ i j / embT D τ r)
    have hal : Formalism.MainNotions.TaylorLogMetric.al D (tor0 D cc δ) x =
        Formalism.MainNotions.TaylorLogMetric.al D (tor0 D D.host.ccK δ) (fun τ i j => x τ i j / embT D τ r) := by
      simp only [Formalism.MainNotions.TaylorLogMetric.al, Hf_div_scale hc h]
    have hadd : (fun τ i j => (z + x) τ i j / embT D τ r) =
        (fun τ i j => z τ i j / embT D τ r) + (fun τ i j => x τ i j / embT D τ r) := by
      funext τ i j
      simp [add_div]
    show _ = Φ fun τ i j => z τ i j / embT D τ r
    rw [← e1, hal]
    simp only [Formalism.MainNotions.TaylorLogMetric.U]
    rw [Hf_div_scale hc h, Hf_div_scale hc h, hadd]

end Copy

variable {D : D7} {r : D.host.E}

theorem mem_cE {α : D.host.E} : α ∈ cE D D.host.ccK ↔ ∃ c ∈ D.host.ccE, (c : D.host.E) = α := by
  constructor
  · intro h
    induction h using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨c, hc, rfl⟩ := hx
      exact ⟨algebraMap (𝓞 D.host.K) (𝓞 D.host.E) c, Ideal.mem_map_of_mem _ hc, rfl⟩
    | zero => exact ⟨0, zero_mem _, rfl⟩
    | add x y _ _ hx hy =>
      obtain ⟨c, hc, rfl⟩ := hx
      obtain ⟨c', hc', rfl⟩ := hy
      exact ⟨c + c', add_mem hc hc', rfl⟩
    | smul o x _ hx =>
      obtain ⟨c, hc, rfl⟩ := hx
      exact ⟨o * c, Ideal.mul_mem_left _ o hc, rfl⟩
  · rintro ⟨c, hc, rfl⟩
    unfold Host.ccE Ideal.map at hc
    induction hc using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨c, hc, rfl⟩ := hx
      exact Submodule.subset_span ⟨c, hc, rfl⟩
    | zero => exact zero_mem _
    | add x y _ _ hx hy => exact add_mem hx hy
    | smul o x _ hx => exact Submodule.smul_mem _ o hx

theorem mem_scaleInv {x : D.host.E} : x ∈ scaleInv D r ↔ ∀ α ∈ cE D D.host.ccK, IntE D (r * α * x) := by
  constructor
  · intro h α hα
    obtain ⟨c, hc, rfl⟩ := mem_cE.1 hα
    exact Submodule.mem_one.1 (h c hc)
  · intro h c hc
    exact Submodule.mem_one.2 (h _ (mem_cE.2 ⟨c, hc, rfl⟩))

theorem mem_scaleLat' {n : ℕ} {y : Fin n → D.host.E} : y ∈ scaleLat D r n ↔ ∀ i, y i ∈ scaleInv D r := by
  simp only [scaleLat, Submodule.mem_pi, Set.mem_univ, true_implies]

theorem scale_eq (hs : IsScale D ⊤ r) : r * D.host.conj r * (Ideal.absNorm D.host.ccK : D.host.E) = 1 := by
  have h := hs
  unfold IsScale at h
  rw [h]; simp

theorem scale_ne (hs : IsScale D ⊤ r) : r ≠ 0 := IsScale.ne_zero top_ne_bot hs

theorem conj_mem_scaleInv (hs : IsScale D ⊤ r) {α : D.host.E} (hα : α ∈ cE D D.host.ccK) :
    D.host.conj r * D.host.conj α ∈ scaleInv D r := by
  refine mem_scaleInv.2 fun β hβ => ?_
  obtain ⟨o, ho⟩ := (GlobalTheory.VacRead.conj_mul_cE_absNorm D D.host.ccK).1 α hα β hβ
  refine ⟨o, ?_⟩
  change (o : D.host.E) = _
  linear_combination (-(o : D.host.E)) * scale_eq hs - r * D.host.conj r * ho

theorem inv_mem_of_gen (hs : IsScale D ⊤ r) (M : Submodule (𝓞 D.host.E) D.host.E)
    (h : ∀ α ∈ cE D D.host.ccK, ∀ β ∈ cE D D.host.ccK, D.host.conj r * (D.host.conj α * β) ∈ M) : r⁻¹ ∈ M := by
  have hle : Submodule.span (𝓞 D.host.E) {t | ∃ α ∈ cE D D.host.ccK, ∃ β ∈ cE D D.host.ccK, t = D.host.conj α * β} ≤
      M.comap (LinearMap.mulLeft (𝓞 D.host.E) (D.host.conj r)) := by
    rw [Submodule.span_le]
    rintro _ ⟨α, hα, β, hβ, rfl⟩
    exact h α hα β hβ
  have h1 : D.host.conj r * (Ideal.absNorm D.host.ccK : D.host.E) ∈ M :=
    hle (GlobalTheory.VacRead.conj_mul_cE_absNorm D D.host.ccK).2
  have h2 : r⁻¹ = D.host.conj r * (Ideal.absNorm D.host.ccK : D.host.E) :=
    inv_eq_of_mul_eq_one_right (by rw [← mul_assoc]; exact scale_eq hs)
  rwa [h2]

theorem intE_mul_conj (hs : IsScale D ⊤ r) {u x : D.host.E} (hu : u ∈ scaleInv D r) (hx : x ∈ scaleInv D r) :
    IntE D (u * D.host.conj x) := by
  have h := inv_mem_of_gen hs ((1 : Submodule (𝓞 D.host.E) D.host.E).comap
    (LinearMap.mulLeft (𝓞 D.host.E) (r * (u * D.host.conj x)))) fun α hα β hβ => by
      have h1 := mul_mem (mem_scaleInv.1 hu β hβ) (mem_scaleInv.1 hx α hα).conj
      refine Submodule.mem_one.2 ?_
      have e : r * (u * D.host.conj x) * (D.host.conj r * (D.host.conj α * β)) = r * β * u * D.host.conj (r * α * x) := by
        simp only [map_mul]; ring
      change IntE D (r * (u * D.host.conj x) * (D.host.conj r * (D.host.conj α * β)))
      rw [e]
      exact h1
  have h2 : IntE D (r * (u * D.host.conj x) * r⁻¹) := Submodule.mem_one.1 h
  have hr := scale_ne hs
  convert h2 using 1
  field_simp

theorem single_mem {n : ℕ} (i : Fin n) {M : Submodule (𝓞 D.host.E) D.host.E} {u : D.host.E} (hu : u ∈ M) (j : Fin n) :
    (Pi.single i u : Fin n → D.host.E) j ∈ M := by
  by_cases hj : j = i
  · subst hj; simpa using hu
  · simp only [Pi.single_apply, hj, if_false]; exact zero_mem _

theorem sd_scaleLat (hs : IsScale D ⊤ r) (n : ℕ) : SD D (scaleLat D r n) := by
  have hr := scale_ne hs
  have hri : r⁻¹ ∈ scaleInv D r := fun c _ => Submodule.mem_one.2 ⟨c, by
    change (c : D.host.E) = _; field_simp⟩
  have hc : D.host.conj r ≠ 0 := (map_ne_zero_iff _ D.host.conj.injective).mpr hr
  rw [GlobalTheory.InertSign.sd_iff]
  refine ⟨?_, ?_, fun y => ?_⟩
  · refine Submodule.fg_pi fun _ => ?_
    have hM : (Submodule.span (𝓞 D.host.E) {D.host.conj r}).FG := Submodule.fg_span (Set.finite_singleton _)
    haveI := isNoetherian_of_fg_of_noetherian _ hM
    refine Submodule.FG.of_le_of_isNoetherian (T := Submodule.span (𝓞 D.host.E) {D.host.conj r}) fun y hy => ?_
    obtain ⟨o, ho⟩ := intE_mul_conj hs hy hri
    refine Submodule.mem_span_singleton.2 ⟨o, ?_⟩
    rw [Algebra.smul_def, ho, map_inv₀]
    field_simp
  · rw [eq_top_iff]
    intro v _
    rw [pi_eq_sum_univ' v]
    refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
    have e : (Pi.single i (1 : D.host.E) : Fin n → D.host.E) = r • Pi.single i r⁻¹ := by
      rw [← Pi.single_smul, smul_eq_mul, mul_inv_cancel₀ hr]
    rw [e]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (mem_scaleLat'.2 (single_mem i hri)))
  · rw [mem_scaleLat']
    constructor
    · intro hy x hx
      rw [mem_scaleLat'] at hx
      unfold GlobalTheory.InertSign.hE
      exact Subring.sum_mem _ fun i _ => intE_mul_conj hs (hy i) (hx i)
    · intro h i
      refine mem_scaleInv.2 fun α hα => ?_
      have h' := h (Pi.single i _) (mem_scaleLat'.2 (single_mem i (conj_mem_scaleInv hs hα)))
      unfold GlobalTheory.InertSign.hE at h'
      rw [Finset.sum_eq_single i (fun j _ hj => by simp [Pi.single_apply, hj]) (by simp), Pi.single_eq_same,
        map_mul, GlobalTheory.InertSign.conj_conj, GlobalTheory.InertSign.conj_conj] at h'
      convert h' using 1
      ring

theorem isSelfDualC_of_sd (S : HSp D) (gS : S.gram = 1) {L : Lat S} (hL : SD D L) : IsSelfDualC S L := by
  obtain ⟨Λ, hΛ, h⟩ := GlobalTheory.MovedDict.isSelfDualC_inV S 1 (by rw [gS]; simp [Formalism.UG.cT]) L hL
  have e : Λ = L := SetLike.coe_injective (by rw [hΛ]; simp [GlobalTheory.MovedDict.inV])
  exact e ▸ h

variable {a d : ℕ}

theorem mem_of_single {W : AddSubgroup (Matrix (Fin d) (Fin a) D.host.E)} {z : Matrix (Fin d) (Fin a) D.host.E}
    (h : ∀ i j, Matrix.single i j (z i j) ∈ W) : z ∈ W := by
  rw [Matrix.matrix_eq_sum_single z]
  exact sum_mem fun i _ => sum_mem fun j _ => h i j

theorem inv_smul_mem (hs : IsScale D ⊤ r) (W : AddSubgroup (Matrix (Fin d) (Fin a) D.host.E))
    (hW : ∀ o : 𝓞 D.host.E, ∀ M ∈ W, (o : D.host.E) • M ∈ W)
    (h : ∀ α ∈ cE D D.host.ccK, ∀ β ∈ cE D D.host.ccK, ∀ b ∈ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E), ∀ i j,
      Matrix.single i j (D.host.conj r * (D.host.conj α * β) * b) ∈ W)
    {z : Matrix (Fin d) (Fin a) D.host.E} (hz : ∀ i j, z i j ∈ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E)) :
    r⁻¹ • z ∈ W := by
  refine mem_of_single fun i j => ?_
  let M : Submodule (𝓞 D.host.E) D.host.E :=
    { carrier := {x | Matrix.single i j (x * z i j) ∈ W}
      add_mem' := fun {x y} hx hy => by
        change Matrix.single i j ((x + y) * z i j) ∈ W
        rw [add_mul, Matrix.single_add]
        exact add_mem hx hy
      zero_mem' := by
        change Matrix.single i j (0 * z i j) ∈ W
        rw [zero_mul, Matrix.single_zero]
        exact zero_mem _
      smul_mem' := fun o x hx => by
        change Matrix.single i j (((o : D.host.E) * x) * z i j) ∈ W
        have := hW o _ hx
        rwa [Matrix.smul_single, smul_eq_mul, ← mul_assoc] at this }
  exact inv_mem_of_gen hs M fun α hα β hβ => h α hα β hβ _ (hz i j) i j

theorem single_mem_homL {J : Submodule (𝓞 D.host.E) D.host.E} {u : D.host.E} (hu : u ∈ J) (i : Fin d) (j : Fin a) :
    Matrix.single i j u ∈ homL D (stdL D a) (Submodule.pi Set.univ fun _ : Fin d => J) := by
  refine GlobalTheory.ThetaLatImage.mem_homL.2 fun x hx k _ => ?_
  obtain ⟨o, ho⟩ := GlobalTheory.ThetaLatImage.mem_stdL.1 hx j
  rw [Matrix.single_mulVec]
  refine single_mem i (u := u * x j) ?_ k
  rw [← ho, mul_comm]
  exact J.smul_mem o hu

theorem int_of_mem_homL {A : Matrix (Fin d) (Fin a) D.host.E} (hA : A ∈ homL D (stdL D a) (stdL D d)) (i : Fin d) (j : Fin a) :
    IntE D (A i j) := by
  have h := GlobalTheory.ThetaLatImage.mem_stdL.1 (GlobalTheory.ThetaLatImage.mem_homL.1 hA (Pi.single j 1)
    (fun k _ => single_mem j (M := (1 : Submodule (𝓞 D.host.E) D.host.E)) (Submodule.mem_one.2 ⟨1, map_one _⟩) k)) i
  simpa using h

theorem entries_of_span {J : Submodule (𝓞 D.host.E) D.host.E} {z : Matrix (Fin d) (Fin a) D.host.E}
    (hz : z ∈ Submodule.span (𝓞 D.host.E) {B | ∃ t ∈ J, ∃ A ∈ homL D (stdL D a) (stdL D d), B = t • A}) (i : Fin d)
    (j : Fin a) : z i j ∈ J := by
  induction hz using Submodule.span_induction with
  | mem B hB =>
    obtain ⟨t, ht, A, hA, rfl⟩ := hB
    obtain ⟨o, ho⟩ := int_of_mem_homL hA i j
    rw [Matrix.smul_apply, smul_eq_mul, ← ho, mul_comm]
    exact J.smul_mem o ht
  | zero => exact zero_mem _
  | add x y _ _ hx hy => exact add_mem hx hy
  | smul o x _ hx => exact J.smul_mem o hx

theorem mem_YYl {z : Matrix (Fin d) (Fin a) D.host.E} : z ∈ YYl D (stdL D a) (stdL D d) ↔
    ∀ i j, z i j ∈ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) := by
  refine ⟨fun h => entries_of_span h, fun h => ?_⟩
  refine mem_of_single (W := (YYl D (stdL D a) (stdL D d)).toAddSubgroup) fun i j => ?_
  refine Submodule.subset_span ⟨_, h i j, Matrix.single i j 1,
    single_mem_homL (J := 1) (Submodule.mem_one.2 ⟨1, map_one _⟩) i j, ?_⟩
  rw [Matrix.smul_single, smul_eq_mul, mul_one]

theorem rl_div (hs : IsScale D ⊤ r) {z : Matrix (Fin d) (Fin a) D.host.E} (hz : z ∈ RL D ⊤ (stdL D a) (stdL D d)) :
    r⁻¹ • z ∈ RL D D.host.ccK (stdL D a) (scaleLat D r d) := by
  have hI : GlobalTheory.InertSign.Iid D ⊤ ≤ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨c, -, b, hb, rfl⟩
    exact Submodule.smul_mem _ (algebraMap (𝓞 D.host.K) (𝓞 D.host.E) c) hb
  refine inv_smul_mem hs (RL D D.host.ccK (stdL D a) (scaleLat D r d)).toAddSubgroup
    (fun o M hM => Submodule.smul_mem _ o hM) (fun α hα β hβ b hb i j => ?_) fun i j => hI (entries_of_span hz i j)
  have hβb : β * b ∈ GlobalTheory.InertSign.Iid D D.host.ccK := by
    have hle : cE D D.host.ccK ≤ (GlobalTheory.InertSign.Iid D D.host.ccK).comap (LinearMap.mulRight (𝓞 D.host.E) b) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨c, hc, rfl⟩
      exact Submodule.subset_span ⟨c, hc, b, hb, rfl⟩
    exact hle hβ
  refine Submodule.subset_span ⟨β * b, hβb, _, single_mem_homL (conj_mem_scaleInv hs hα) i j, ?_⟩
  rw [Matrix.smul_single, smul_eq_mul]
  congr 1
  ring

theorem mem_latRat (hs : IsScale D ⊤ r) (S T : HSp D) (gS : S.gram = 1) (z : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    r⁻¹ • z ∈ GlobalTheory.LatVac.latRat S T (stdLat S) (scaleLat D r T.rank) ↔
      ∀ i j, z i j ∈ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) := by
  have hr := scale_ne hs
  have hg : ∀ (s : Fin S.rank → D.host.E) j, ∑ k, star (s k) * S.gram k j = D.host.conj (s j) := by
    intro s j
    rw [gS]
    simp [Matrix.one_apply, GlobalTheory.NormSum.AdLattice.star_eq_conj]
  constructor
  · have key : ∀ M ∈ GlobalTheory.LatVac.latRat S T (stdLat S) (scaleLat D r T.rank), ∀ i j,
        r * M i j ∈ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) := by
      intro M hM i j
      induction hM using AddSubgroup.closure_induction with
      | mem w hw =>
        obtain ⟨x, hx, s, hs', t, ht, rfl⟩ := hw
        obtain ⟨o, ho⟩ := (GlobalTheory.ThetaLatImage.mem_stdL.1 hs' j).conj
        have h1 : r * (x * t i) ∈ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) := by
          unfold Host.AA at hx
          refine FractionalIdeal.mul_induction_on hx (fun c hc b hb => ?_) fun x y hx hy => ?_
          · obtain ⟨c, hc', rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hc
            obtain ⟨o', ho'⟩ := Submodule.mem_one.1 (mem_scaleLat.1 ht i c hc')
            have e : r * (algebraMap (𝓞 D.host.E) D.host.E c * b * t i) = o' • b := by
              rw [Algebra.smul_def, ho']; ring
            rw [e]
            exact Submodule.smul_mem _ o' hb
          · rw [add_mul, mul_add]; exact add_mem hx hy
        have e : r * GlobalTheory.LatVac.genMap S T x s t i j = o • (r * (x * t i)) := by
          rw [GlobalTheory.LatVac.genMap, Matrix.of_apply, hg, Algebra.smul_def, ho]; ring
        rw [e]
        exact Submodule.smul_mem _ o h1
      | zero => simp
      | add x y _ _ hx hy => rw [Matrix.add_apply, mul_add]; exact add_mem hx hy
      | neg x _ hx => rw [Matrix.neg_apply, mul_neg]; exact neg_mem hx
    intro h i j
    have := key _ h i j
    rwa [Matrix.smul_apply, smul_eq_mul, mul_inv_cancel_left₀ hr] at this
  · refine inv_smul_mem hs _ (fun o M hM => GlobalTheory.LatVac.smul_mem_latRat o hM) fun α hα β hβ b hb i j => ?_
    obtain ⟨c, hc, rfl⟩ := mem_cE.1 hβ
    refine AddSubgroup.subset_closure ⟨(c : D.host.E) * b,
      FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_coeIdeal_of_mem _ hc) hb, Pi.single j 1,
      fun k _ => single_mem j (M := (1 : Submodule (𝓞 D.host.E) D.host.E)) (Submodule.mem_one.2 ⟨1, map_one _⟩) k,
      Pi.single i _, mem_scaleLat'.2 (single_mem i (conj_mem_scaleInv hs hα)), ?_⟩
    ext k l
    rw [GlobalTheory.LatVac.genMap, Matrix.of_apply, hg]
    by_cases hk : i = k
    · subst hk
      by_cases hl : j = l
      · subst hl; simp; ring
      · simp [hl, Ne.symm hl]
    · simp [hk, Ne.symm hk]

theorem finRat_mem_iff {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S T : HSp D} {LS : Lat S} {LT : Lat T}
    (hS : IsSelfDualC S LS) (hT : IsSelfDualC T LT) (M : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    GlobalTheory.VacUnique.finRat S T M ∈ latO S T LS LT (fun _ => True) ↔ M ∈ GlobalTheory.LatVac.latRat S T LS LT := by
  refine ⟨fun h => ?_, fun h => GlobalTheory.LatVac.finTens_mem_latO (GlobalTheory.LatVac.one_mem_intAf _) h⟩
  refine (GlobalTheory.T.rationalHermitianRankOneLattice_selfDual D S T LS LT hS hT (GlobalTheory.T.exists_dual_family_selfDual_hermitianSpace D S LS hS) _).2 fun ℓ hℓ => ?_
  have h1 := GlobalTheory.LatVac.char_sympl_eq_one hψ hS hT (u := GlobalTheory.LatVac.finTens 1 M) h
    (GlobalTheory.LatVac.finTens_mem_latO (GlobalTheory.LatVac.one_mem_intAf _) hℓ)
  rw [GlobalTheory.LatVac.symplO_finTens, one_mul, one_mul] at h1
  exact (GlobalTheory.LatVac.char_rat hψ _).1 h1

theorem vac_reads {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D} {δ : ℂ} (hset : Setup ψ θ S T ⊤ δ r)
    {f : WO S T → ℂ} (hf : IsVacO ψ θ S T (fun _ => 1) (fun _ => 1) (stdLat S) (scaleLat D r T.rank) f) :
    ∃ G ∈ Th D (tor0 D ⊤ δ) (stdL D S.rank) (stdL D T.rank), G ≠ 0 ∧ Reads ψ θ rfl rfl ⊤ δ r G f := by
  obtain ⟨hψ, hθ, gS, gT, crv, sc⟩ := hset
  have hr : r ≠ 0 := scale_ne sc
  have hδ : δ ≠ 0 := delta_ne_zero crv
  have hS1 : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (1 : GL (Fin S.rank) D.host.E).1 * S.gram *
      (1 : GL (Fin S.rank) D.host.E).1 = 1 := by
    rw [gS]; simp [Formalism.UG.cT]
  have hT1 : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (1 : GL (Fin T.rank) D.host.E).1 * T.gram *
      (1 : GL (Fin T.rank) D.host.E).1 = 1 := by
    rw [gT]; simp [Formalism.UG.cT]
  obtain ⟨Φ, hΦd, hΦ⟩ := GlobalTheory.FockPos.vacuum_real_entire ψ θ S T 1 1 _ _ hS1 hT1 f hf
  have hinV : ∀ {k : ℕ} (L : Submodule (𝓞 D.host.E) (Fin k → D.host.E)),
      GlobalTheory.MovedDict.inV (D := D) 1 L = (L : Set (Fin k → D.host.E)) := by
    intro k L
    simp [GlobalTheory.MovedDict.inV]
  have hf' := hf
  rw [← hinV (stdL D S.rank), ← hinV (scaleLat D r T.rank)] at hf'
  have hth := GlobalTheory.VacRead.theta_of_unit_vacuum ψ θ S T 1 1 hS1 hT1 δ hδ _ _ (GlobalTheory.MovedVacuum.sd_stdL D _)
    (sd_scaleLat sc _) f hf' Φ hΦd hΦ
  have hLa : ∀ x ∈ Formalism.MainNotions.TaylorLogMetric.La D (tor0 D ⊤ δ) (stdL D S.rank) (stdL D T.rank),
      (fun τ i j => x τ i j / embT D τ r) ∈
        Formalism.MainNotions.TaylorLogMetric.La D (tor0 D D.host.ccK δ) (stdL D S.rank) (scaleLat D r T.rank) := by
    intro x hx
    obtain ⟨z, hz, rfl⟩ := GlobalTheory.ThetaLatImage.La_sub hx
    have h2 := GlobalTheory.ThetaLatImage.pt_mem_La (δ := δ) (rl_div sc hz) 1
    convert h2 using 1
    funext τ i j
    rw [one_smul, GlobalTheory.ThetaLatImage.pt_apply, GlobalTheory.ThetaLatImage.pt_apply]
    have ht : embT D τ r ≠ 0 := (map_ne_zero _).2 hr
    simp only [Matrix.smul_apply, smul_eq_mul, map_mul, map_inv₀]
    field_simp
  have hG := th_div_scale crv sc hLa hth
  have hback : ∀ Z : VC D S.rank T.rank,
      (δ⁻¹ • fun τ i j => (δ * embT D τ r * Z τ i j) / embT D τ r : VC D S.rank T.rank) = Z := by
    intro Z
    funext τ i j
    have ht : embT D τ r ≠ 0 := (map_ne_zero _).2 hr
    simp only [Pi.smul_apply, smul_eq_mul]
    field_simp
  refine ⟨_, hG, ?_, (reads_iff crv sc _ f).2 ⟨hf.2.theta, fun w hw => ?_⟩⟩
  · intro h0
    apply GlobalTheory.StepMove.vacO_ne_zero hf
    refine GlobalTheory.TwistFactorCompare.theta_eq_zero_of_real hf.2.theta fun w hw => ?_
    rw [hΦ w hw]
    have e := congrFun h0 (fun τ i j => δ * embT D τ r * GlobalTheory.FockPos.zCo θ 1 1 w τ i j)
    simp only [Pi.zero_apply, hback] at e
    rw [e, mul_zero]
  · rw [hΦ w hw]
    simp only [hback]

end GlobalTheory.NormRatio.VacLat

namespace GlobalTheory.NormRatio

open GlobalTheory.NormRatio.VacLat

theorem vacLat_of_reads : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) {a d : ℕ} (hS : S.rank = a) (hT : T.rank = d)
  (δ : ℂ) (r : D.host.E), Setup ψ θ S T ⊤ δ r →
  ∃ LT : Lat T, IsSelfDualC T LT ∧
    (∀ z : Matrix (Fin d) (Fin a) D.host.E, z ∈ Formalism.MainNotions.TaylorLogMetric.YYl D (Formalism.MainNotions.StandardLatticesGL3.stdL D a) (Formalism.MainNotions.StandardLatticesGL3.stdL D d) ↔
      finPt hS hT r z ∈ latO S T (stdLat S) LT fun _ => True) ∧
    ∀ e0 ∈ Formalism.MainNotions.TaylorLogMetric.Th D (Formalism.MainNotions.TaylorLogMetric.tor0 D ⊤ δ) (Formalism.MainNotions.StandardLatticesGL3.stdL D a) (Formalism.MainNotions.StandardLatticesGL3.stdL D d), ∀ f₀,
      Reads ψ θ hS hT ⊤ δ r e0 f₀ → IsSphOff ψ S T (stdLat S) LT ∅ f₀ := by
  intro D ψ θ S T a d hS hT δ r hs
  subst hS hT
  have sdS : IsSelfDualC S (stdLat S) := isSelfDualC_of_sd S hs.gS (GlobalTheory.MovedVacuum.sd_stdL D _)
  have sdT : IsSelfDualC T (scaleLat D r T.rank) := isSelfDualC_of_sd T hs.gT (sd_scaleLat hs.scale _)
  refine ⟨scaleLat D r T.rank, sdT, fun z => ?_, fun e0 he0 f₀ hf₀ => ?_⟩
  · have e : finPt (rfl : S.rank = S.rank) (rfl : T.rank = T.rank) r z = GlobalTheory.VacUnique.finRat S T (-(r⁻¹ • z)) := rfl
    rw [e, finRat_mem_iff hs.std sdS sdT, neg_mem_iff, mem_latRat hs.scale S T hs.gS, mem_YYl]
  · obtain ⟨f, hf⟩ := vac_exists_gram_one ψ θ hs.std hs.inf S T hs.gS hs.gT _ _ sdS sdT
    obtain ⟨G, hG, hG0, hrd⟩ := vac_reads hs hf
    obtain ⟨c, rfl⟩ := (GlobalTheory.ThetaLine.theta_line D (GlobalTheory.InducedType.induced_type D).1 ⊤ δ hs.crv _ _ _
      (Or.inr ⟨_, _, GlobalTheory.MovedVacuum.sd_stdL D _, GlobalTheory.MovedVacuum.sd_stdL D _, rfl⟩)).1 e0 he0 G hG hG0
    have hP : (fun v : FinPl D => v ∉ (∅ : Finset (FinPl D))) = fun _ => True := by
      funext v; simp
    rw [hf₀.unique (hrd.smul c)]
    unfold IsSphOff
    rw [hP]
    exact ⟨fun u hu => by rw [GlobalTheory.LatVac.heisO_smul, hf.2.lat.1 u hu],
      fun e he u hu hh => by rw [GlobalTheory.LatVac.heisO_smul, hf.2.lat.2 e he u hu hh]⟩

end GlobalTheory.NormRatio
