import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdmissibleEmptyOfGood
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsRepsOfOpenCompact
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsCompactParahoricLevelAndContainsLifts
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SchrodingerIntertwinerInjectiveSchwartzBruhat
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNonvanishingFiniteDatumDefiniteLift
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasChr

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum
  IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Links (PolF)
open scoped TensorProduct ComplexOrder

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.ExportSeries.Model

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {S T : HSp D}

theorem hecke_mul {χ χ' : (AE D)ˣ →* Circle} (h : IsHeckeChar D χ) (h' : IsHeckeChar D χ') : IsHeckeChar D (χ * χ') :=
  ⟨h.1.mul h'.1, fun x => by rw [MonoidHom.mul_apply, h.2, h'.2, mul_one]⟩

theorem hecke_inv {χ : (AE D)ˣ →* Circle} (h : IsHeckeChar D χ) : IsHeckeChar D χ⁻¹ :=
  ⟨h.1.inv, fun x => by rw [MonoidHom.inv_apply, h.2, inv_one]⟩

theorem exists_isWeil (hP : GlobalTheory.Published.WeilRepresentationUnitaryPair) {B : Base S T} (hB : B.Good) {ψ : Twist D Circle}
    (hψ : ψ.Good) : ∃ ω, B.IsWeil ψ.chi ω := by
  have h1 : IsHeckeChar D (B.mu * ψ.chi) := hecke_mul (hecke_mul hB.hecke hB.de.isHeckeChar) hψ.isHeckeChar
  have r0 : ResEta D (B.mu * ψ.chi) 0 := ⟨hB.eta.2.2.1.1, fun η _ a => by
    rw [Base.mu, MonoidHom.mul_apply, MonoidHom.mul_apply, hB.real, hB.de.real, hψ.real]; simp⟩
  refine hP D _ S T _ _ hB.frame.vac.1 h1 (hecke_mul h1 (hecke_inv hB.eta.1)) ?_ ?_
  · exact resEta_parity r0 (by have := Nat.even_iff.1 hB.even; omega)
  · exact resEta_parity (resEta_mul r0 (resEta_inv hB.eta.2.2.1)) (by have := Nat.odd_iff.1 hB.odd; omega)

theorem not_isWeil_swap {B : Base S T} (hB : B.Good) (ω : PairRep S T) :
    ¬ IsWeilDatumO B.F.ψ S T (B.mu * B.eta⁻¹) B.mu ω := fun h => by
  have r0 : ResEta D B.mu 0 := ⟨hB.eta.2.2.1.1, fun η _ a => by
    rw [Base.mu, MonoidHom.mul_apply, hB.real, hB.de.real]; simp⟩
  exact resEta_not_both r0 (resEta_parity h.resT (by have := Nat.odd_iff.1 hB.odd; omega))

theorem posDef_of_good {F : Frame S T} (hF : F.Good) (τ : D.what₂.Tau) : (gramAt D S τ).PosDef := by
  obtain ⟨ε, h1, h2, -⟩ := hF.onbS τ
  have hε : (Matrix.diagonal fun a => (ε a : ℂ)) = 1 := by
    rw [← Matrix.diagonal_one]
    congr 1
    funext a
    rcases h1 a with h | h
    · simp [h.1]
    · exact absurd a.2 (not_lt.2 h.2)
  rw [hε] at h2
  have e : gramAt D S τ = ((F.BS τ)⁻¹).valᴴ * 1 * ((F.BS τ)⁻¹).val := by
    rw [← h2]
    have a : ((F.BS τ)⁻¹).valᴴ * (F.BS τ).valᴴ = 1 := by rw [← conjTranspose_mul, Units.mul_inv, conjTranspose_one]
    calc gramAt D S τ = (((F.BS τ)⁻¹).valᴴ * (F.BS τ).valᴴ) * gramAt D S τ * ((F.BS τ).val * ((F.BS τ)⁻¹).val) := by
          rw [a, Units.mul_inv, Matrix.one_mul, Matrix.mul_one]
      _ = _ := by simp only [Matrix.mul_assoc]
  rw [e]
  exact Matrix.PosDef.one.conjTranspose_mul_mul_same (Matrix.mulVec_injective_iff_isUnit.2 (Units.isUnit _))

theorem exists_lift (V : HSp D) (u : Bridge.Gf V) : ∃ k : GA D V, k ∈ GfC V ∧ (finHom V).rangeRestrict k = u := by
  obtain ⟨_, g, rfl⟩ := u
  obtain ⟨h1, h2⟩ := GlobalTheory.Mass.parts_spec D.sp.cm.sig V.gram
  obtain ⟨k, k1, k2⟩ := h2 1 (finHom V g)
  have hk : k ∈ HR (AF D.host.F) D.sp.cm.sig V.gram :=
    (h1 k).2 ⟨k1 ▸ one_mem _, k2 ▸ ((h1 _).1 g.2).2⟩
  exact ⟨⟨k, hk⟩, k1, Subtype.ext k2⟩

theorem exists_isClassSystem (B : Base S T) (hF : B.F.Good) (ψ : Twist D Circle) :
    ∃ (m : ℕ) (h : Fin m → GA D S), IsClassSystem S (B.levJ ψ) h := by
  have hV := posDef_of_good hF
  obtain ⟨m, c, hc⟩ := GlobalTheory.RepsObj.exists_cover S hV (B.levJ ψ) (GlobalTheory.ParahoricCompact.isOpen_comap_lev S B.F.βS (B.levS ψ))
  have hr : Equivalence fun g g' : Bridge.Gf S => ∃ (γ : GQ S) (k : B.levJ ψ), g = Bridge.ratF S γ * g' * k :=
    ⟨fun g => ⟨1, 1, by simp⟩, by
      rintro g g' ⟨γ, k, rfl⟩
      exact ⟨γ⁻¹, k⁻¹, by simp [mul_assoc]⟩, by
      rintro g g' g'' ⟨γ, k, rfl⟩ ⟨γ', k', rfl⟩
      exact ⟨γ * γ', k' * k, by simp [mul_assoc]⟩⟩
  obtain ⟨n, f, hf⟩ := GlobalTheory.UnRep.FullReps.exists_subfamily _ hr c
  choose l hl1 hl2 using fun a => exists_lift S (c (f a))
  obtain ⟨C, hC, hCe⟩ := GlobalTheory.ParahoricCompact.exists_compact_entries B.F.βS
  refine ⟨n, l, hl1, fun g => ?_, fun i => GlobalTheory.RepsObj.finite_stab S hV _ hC
    (fun k hk => hCe k.1 (Base.mem_St_of_mem_levJ hk)) _⟩
  obtain ⟨a, ha⟩ := hc g
  have := hf g a ha
  simp only [finPt, hl2]
  exact this

open GlobalTheory.AdelicLatMove GlobalTheory.PlaceVec GlobalTheory.AdjDatumNe

theorem pair_int {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (Λ : Submodule (𝓞 E) (Fin n → E)) (u : Fin n → E)
    (hu : ∀ y ∈ Λ, ∃ c : 𝓞 E, algebraMap (𝓞 E) E c = ∑ k, u k * y k)
    (z : Fin n → E ⊗[F] Formalism.L2.Herm.Af F) (hz : z ∈ Formalism.L2.Herm.hatL (F := F) Λ) :
    ∑ k, (u k ⊗ₜ[F] (1 : Formalism.L2.Herm.Af F)) * z k ∈ Formalism.L2.Herm.intAf F E := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨y, hy, rfl⟩ := hz
    obtain ⟨c, hc⟩ := hu y hy
    have hm : (algebraMap (𝓞 E) E c) ⊗ₜ[F] (1 : Formalism.L2.Herm.Af F) ∈ Formalism.L2.Herm.intAf F E :=
      Subring.subset_closure (Or.inl ⟨⟨_, c, rfl⟩, rfl⟩)
    convert hm using 1
    rw [hc, TensorProduct.sum_tmul]
    refine Finset.sum_congr rfl fun k _ => ?_
    change (u k ⊗ₜ[F] (1 : Formalism.L2.Herm.Af F)) * (y k ⊗ₜ[F] 1) = _
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
  | zero => simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero]; exact zero_mem _
  | add x y _ _ hx hy => simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]; exact add_mem hx hy
  | smul c x _ hx =>
    have := mul_mem c.2 hx
    convert this using 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    change _ * (c.1 * x k) = _
    ring

def ct {a b : ℕ} (A : Matrix (Fin a) (Fin b) (EAf D)) : Matrix (Fin b) (Fin a) (EAf D) := (A.map (cF D))ᵀ

theorem ct_mul {a b c : ℕ} (A : Matrix (Fin a) (Fin b) (EAf D)) (B : Matrix (Fin b) (Fin c) (EAf D)) :
    ct (A * B) = ct B * ct A := by
  rw [ct, Matrix.map_mul, Matrix.transpose_mul]; rfl

theorem ct_map {a b : ℕ} (A : Matrix (Fin a) (Fin b) D.host.E) : ct (A.map (eToEAf D)) = Aᴴ.map (eToEAf D) := rfl

theorem int_ct {a b : ℕ} {A : Matrix (Fin a) (Fin b) (EAf D)} (h : IsIntM A) : IsIntM (ct A) :=
  fun i j => cF_mem_int (h j i)

theorem int_mul {a b c : ℕ} {A : Matrix (Fin a) (Fin b) (EAf D)} {B : Matrix (Fin b) (Fin c) (EAf D)} (h : IsIntM A)
    (h' : IsIntM B) : IsIntM (A * B) := fun i j => by
  rw [Matrix.mul_apply]
  exact sum_mem fun p _ => mul_mem (h i p) (h' p j)

theorem gram_frame_int (V : HSp D) {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} {β : GL (Fin V.rank) (EAf D)}
    (hV : IsSelfDualC V Λ) (f : IsFrame β Λ) :
    IsIntM (ct β.val * V.gram.map (eToEAf D) * β.val) ∧
      IsIntM ((β⁻¹).val * (V.gram⁻¹).map (eToEAf D) * ct (β⁻¹).val) := by
  obtain ⟨n, s, s', hs, hss⟩ := GlobalTheory.LatVacDual.dualFamily D V Λ hV
  obtain ⟨s₁, hs₁⟩ : ∃ A : Matrix (Fin V.rank) (Fin n) D.host.E, A = Matrix.of fun a k => s k a := ⟨_, rfl⟩
  obtain ⟨s₂, hs₂⟩ : ∃ A : Matrix (Fin V.rank) (Fin n) D.host.E, A = Matrix.of fun a k => s' k a := ⟨_, rfl⟩
  have e1 : s₁ * (s₂ᴴ * V.gram) = 1 := by
    subst hs₁ hs₂
    exact Matrix.ext fun a j => (hss a j).trans (Matrix.one_apply).symm
  have hG : V.gramᴴ = V.gram := Matrix.ext fun i j => GlobalTheory.LatVac.gram_star V j i
  have hcol : ∀ a, (fun k => β.val k a) ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ := fun a => by
    refine (f _).2 fun i => ?_
    have e : ((β⁻¹).val *ᵥ fun k => β.val k a) i = ((β⁻¹).val * β.val) i a := rfl
    rw [e, Units.inv_mul, Matrix.one_apply]
    split_ifs
    exacts [one_mem _, zero_mem _]
  have i1 : ∀ t : Fin n → Fin V.rank → D.host.E, (∀ k, t k ∈ Λ) →
      IsIntM (((Matrix.of fun a k => t k a)ᴴ * V.gram).map (eToEAf D) * β.val) := fun t ht k a => by
    refine pair_int Λ (fun j => ((Matrix.of fun a k => t k a)ᴴ * V.gram) k j) (fun y hy => ?_) _ (hcol a)
    obtain ⟨b, hb⟩ := (hV.2 y).1 hy _ (ht k)
    refine ⟨b, hb.trans ?_⟩
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => (Finset.sum_mul _ _ _).symm
  have i2 : ∀ t : Fin n → Fin V.rank → D.host.E, (∀ k, t k ∈ Λ) →
      IsIntM ((β⁻¹).val * (Matrix.of fun a k => t k a).map (eToEAf D)) := fun t ht a k =>
    (f _).1 (pure_mem_hatL Λ 1 (one_mem _) _ (ht k)) a
  constructor
  · have := int_mul (int_ct (i1 s fun k => (hs k).1)) (i1 s' fun k => (hs k).2)
    rw [← hs₁, ← hs₂, ct_mul, ct_map, conjTranspose_mul, conjTranspose_conjTranspose, hG, Matrix.mul_assoc,
      ← Matrix.mul_assoc _ _ β.val, ← Matrix.map_mul, Matrix.mul_assoc V.gram, e1, Matrix.mul_one] at this
    rwa [Matrix.mul_assoc]
  · have := int_mul (i2 s fun k => (hs k).1) (int_ct (i2 s' fun k => (hs k).2))
    rw [← hs₁, ← hs₂, ct_mul, ct_map, Matrix.mul_assoc, ← Matrix.mul_assoc _ _ (ct _), ← Matrix.map_mul] at this
    rwa [Matrix.inv_eq_left_inv (B := s₁ * s₂ᴴ) (by rw [Matrix.mul_assoc, e1]), Matrix.mul_assoc]

theorem int_adj_of_int {F : Frame S T} (hF : F.Good) {x : WO S T} (h : IsIntM (frMapO S T F.βS F.βT x)) :
    IsIntM (frMapAdj S T F.βS F.βT x) := by
  have e : x.map (toEAf D) = F.βT.val * frMapO S T F.βS F.βT x * (F.βS⁻¹).val := by
    unfold frMapO
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul, Matrix.mul_assoc, Units.mul_inv,
      Matrix.mul_one]
  have := int_mul (int_mul (gram_frame_int S hF.sdS hF.frS).2 (int_ct h)) (gram_frame_int T hF.sdT hF.frT).1
  rw [frMapAdj_eq]
  change IsIntM (_ * ct (x.map (toEAf D)) * _)
  rw [e, ct_mul, ct_mul]
  simpa only [Matrix.mul_assoc] using this

theorem vac_ne_zero {F : Frame S T} (hF : F.Good) : F.f₀ ≠ 0 := fun h => by
  obtain ⟨p, hp⟩ := hF.vac.2.norm.1
  have := hF.vac.2.norm.2 p hp
  rw [h] at this
  simp [nrm2] at this

theorem omegaG_empty (y : Reds D S.rank T.rank) :
    omegaG (TypeDat.empty D T.rank).levT (TypeDat.empty D T.rank).muC y = 1 := by
  have : IsEmpty ↥(TypeDat.empty D T.rank).levT.Pg := ⟨fun PP => absurd PP.2 (Finset.notMem_empty _)⟩
  unfold omegaG
  rw [dif_pos ⟨fun _ h => absurd h (Finset.notMem_empty _), fun PP => isEmptyElim PP, fun PP => isEmptyElim PP,
    fun PP => isEmptyElim PP, Subgroup.mem_bot.2 (Subsingleton.elim _ _)⟩, Finset.univ_eq_empty, Finset.prod_empty,
    Finset.prod_empty, mul_one, mul_one]
  rfl

theorem flat_rectOne {k : Type} [CommRing k] {r n : ℕ} (h : r ≤ n) (ν : kˣ →* ℂˣ) : flat ν (rectOne k r n) = 1 := by
  rw [flat_of_isUnit ν (u := 1), map_one, Units.val_one]
  have : topL r (rectOne k r n) = 1 := by
    ext i j
    have h1 : i.val < r ∧ j.val < n := ⟨i.2, by omega⟩
    unfold topL rectOne
    rw [dif_pos h1, Matrix.one_apply]
    simp only [Fin.ext_iff]
  rw [this, det_one, Units.val_one]

theorem vecFlat_ne_zero {B : Base S T} (hB : B.Good) (hG : B.G = TypeDat.empty D T.rank) (ψ : Twist D Circle)
    (hQ : B.admitted ψ.Q) : B.vecFlat ψ ≠ 0 := by
  classical
  have hF := hB.frame
  have hP := hQ.1
  have hω : ∀ y y', (∀ PP ∈ B.de.Q ∪ ψ.Q, y PP = y' PP) →
      B.locFn ψ.Q (fun PP => flat (ψ.resC PP.1)) y = B.locFn ψ.Q (fun PP => flat (ψ.resC PP.1)) y' := fun y y' hy => by
    unfold Base.locFn
    rw [Finset.prod_congr rfl fun PP hPP => by rw [hy PP (Finset.mem_union_left _ hPP)],
      Finset.prod_congr (s₁ := Finset.univ) rfl fun PP _ => by rw [hy PP.1 (Finset.mem_union_right _ PP.2)]]
  refine GlobalTheory.PlaceModelInj.placeModel_ne_zero D _ S T _ _ _ _ _ _ hF.vac.1 hF.sdS hF.sdT hP.isOrthSum.1.idem hP.isOrthSum.2
    hP.isOrthSum.1.infPart_eq (Frame.isPlaceModel_placeMap hF hP) (vac_ne_zero hF) (Frame.isSBHalf_datumFn hF hP hω) ?_
  obtain ⟨P, -, h2, hS⟩ := hP.split
  have he := (hS.mono h2).isIdemSum
  obtain ⟨hi, hres⟩ := idemSum_res he
  have h0 : halfIdem B.G.Pg (B.de.Q ∪ ψ.Q) = idem (B.de.Q ∪ ψ.Q) := by
    rw [hG]
    change cA D (idem ∅) + _ = _
    rw [idem_empty, RingHom.map_zero, zero_add]
  have hee := hP.isOrthSum.1.idem
  rw [h0] at hee
  choose N hN using fun (i : Fin T.rank) (j : Fin S.rank) =>
    toEAf_surjective ((B.F.βT.val * rectOne (EAf D) T.rank S.rank * (B.F.βS⁻¹).val) i j)
  let x : WO S T := Matrix.of fun i j => idem (B.de.Q ∪ ψ.Q) * N i j
  have hx : IsHalf (halfIdem B.G.Pg (B.de.Q ∪ ψ.Q)) x := fun i j => by
    rw [h0]
    exact (mul_assoc _ _ (N i j)).symm.trans (congrArg (· * N i j) hee)
  have e : frMapO S T B.F.βS B.F.βT x = toEAf D (idem (B.de.Q ∪ ψ.Q)) • rectOne (EAf D) T.rank S.rank := by
    have : x.map (toEAf D) = toEAf D (idem (B.de.Q ∪ ψ.Q)) •
        (B.F.βT.val * rectOne (EAf D) T.rank S.rank * (B.F.βS⁻¹).val) := Matrix.ext fun i j => by
      change toEAf D (_ * _) = _ * _
      rw [RingHom.map_mul, hN]
    unfold frMapO
    rw [this, Matrix.mul_smul, Matrix.smul_mul, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul,
      Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
  have i1 : IsIntM (frMapO S T B.F.βS B.F.βT x) := e ▸ isIntM_smul_rectOne hi _ _
  intro hz
  have := congrFun hz x
  rw [Frame.datumFn, if_pos ⟨hx, int_adj_of_int hF i1⟩, if_pos ⟨hx, i1⟩, hG, omegaG_empty, one_mul, e, Base.locFn,
    Finset.prod_eq_one fun PP hPP => by
      rw [redM_smul_rectOne hi PP (hres PP (Finset.mem_union_left _ hPP)), flat_rectOne B.hr],
    Finset.prod_eq_one fun PP _ => by
      rw [redM_smul_rectOne hi PP.1 (hres PP.1 (Finset.mem_union_right _ PP.2)), flat_rectOne B.hr], mul_one] at this
  exact one_ne_zero this

open GlobalTheory.IdemSupport in

theorem exists_split_off (D : D7) (R : Finset (Pl D.host.E)) :
    ∃ (P : Pl D.host.E) (p : ℕ), SplitSet {P} ∧ (p : 𝓞 D.host.E) ∈ P.asIdeal ∧ ∀ Q ∈ R, (p : 𝓞 D.host.E) ∉ Q.asIdeal := by
  have hsq : D.host.sqrtMinusD ^ 2 = -(D.host.d : D.host.E) :=
    by simpa [Host.sqrtMinusD] using D.host.sqd_sq
  have hst : star D.host.sqrtMinusD = -D.host.sqrtMinusD := by
    apply D.host.φ₀.injective
    have h1 : D.host.φ₀ D.host.sqrtMinusD = Complex.I * (Real.sqrt D.host.d : ℂ) := D.host.φ₀_mem
    have := D.host.isCMField_hostE
    have h2 : D.host.φ₀ (star D.host.sqrtMinusD) = starRingEnd ℂ (D.host.φ₀ D.host.sqrtMinusD) :=
      NumberField.IsCMField.complexEmbedding_complexConj D.host.E D.host.φ₀ D.host.sqrtMinusD
    rw [h2, map_neg, h1]
    simp
  have hint : IsIntegral ℤ D.host.sqrtMinusD :=
    IsIntegral.of_pow two_pos (by rw [hsq]; exact (isIntegral_natCast _).neg)
  obtain ⟨rt, hrt⟩ : ∃ rt : 𝓞 D.host.E, (rt : D.host.E) = D.host.sqrtMinusD := ⟨⟨_, hint⟩, rfl⟩
  have rsq : rt ^ 2 = -(D.host.d : 𝓞 D.host.E) := RingOfIntegers.ext (by simpa [hrt] using hsq)
  have hbar : cO D rt = -rt := RingOfIntegers.ext (by rw [cO_coe, hrt, hst, ← hrt]; rfl)
  have hd : 0 < D.host.d := Nat.pos_of_ne_zero D.host.hyp.2.1.ne_zero
  generalize D.host.d = d at rsq hd
  obtain ⟨M, hM'⟩ : ∃ M : ℕ, M = ∏ Q ∈ R, Ideal.absNorm Q.asIdeal := ⟨_, rfl⟩
  have hM : 0 < M := hM' ▸ Finset.prod_pos fun Q _ => Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.2 Q.ne_bot)
  obtain ⟨p, hp, hdiv⟩ := Nat.exists_prime_and_dvd (n := d * (2 * M) ^ 2 + 1) (by
    have : 0 < d * (2 * M) ^ 2 := by positivity
    omega)
  have hcop : ¬ p ∣ d * (2 * M) ^ 2 := fun h => hp.not_dvd_one ((Nat.dvd_add_right h).1 hdiv)
  have hnu : Ideal.span {(p : 𝓞 D.host.E)} ≠ ⊤ := by
    rw [Ne, Ideal.span_singleton_eq_top]
    intro hu
    have h1 : IsUnit (Algebra.norm ℤ (algebraMap ℤ (𝓞 D.host.E) p)) := by simpa using hu.map (Algebra.norm ℤ)
    rw [Algebra.norm_algebraMap, isUnit_pow_iff Module.finrank_pos.ne', Int.isUnit_iff_natAbs_eq] at h1
    exact hp.ne_one (by simpa using h1)
  obtain ⟨I, hI, hle⟩ := Ideal.exists_le_maximal _ hnu
  have hpI : (p : 𝓞 D.host.E) ∈ I := hle (Ideal.mem_span_singleton_self _)
  have hne : I ≠ ⊥ := fun h => by
    rw [h, Ideal.mem_bot] at hpI
    exact hp.ne_zero (by exact_mod_cast hpI)
  have hco : ∀ (J : Ideal (𝓞 D.host.E)) (m : ℕ), J ≠ ⊤ → ¬ p ∣ m → (p : 𝓞 D.host.E) ∈ J → (m : 𝓞 D.host.E) ∉ J :=
    fun J m hJ hm h1 h2 => by
      obtain ⟨u, v, huv⟩ : IsCoprime (p : 𝓞 D.host.E) (m : 𝓞 D.host.E) := ((Nat.Prime.coprime_iff_not_dvd hp).2 hm).cast
      exact hJ ((Ideal.eq_top_iff_one _).2 (huv ▸ J.add_mem (J.mul_mem_left _ h1) (J.mul_mem_left _ h2)))
  let P : Pl D.host.E := ⟨I, hI.isPrime, hne⟩
  refine ⟨P, p, ?_, hpI, fun Q hQ h => hco _ _ Q.isPrime.ne_top (fun h' => hcop ?_) h (Ideal.absNorm_mem _)⟩
  · obtain ⟨Φ, hΦ⟩ := exists_comp D
    obtain ⟨e, f, h⟩ := exists_isPrimeIdem hΦ P
    rcases h with ⟨h, -⟩ | ⟨-, ⟨v, ε, -, rfl⟩, ht⟩
    · exact ⟨e, ⟨fun _ => e, fun PP hPP => by rw [Finset.mem_singleton.1 hPP]; exact h, by simp⟩, h.1.2.1⟩
    · exfalso
      have h2 := Comparison₂.conj (P := P) ht
      rw [cA_algebraMap] at h2
      have hb : ∀ y ∈ I, cO D y ∈ I := fun y hy => by
        by_cases h0 : y = 0
        · rw [h0, map_zero]; exact zero_mem _
        · exact (h2 y h0).2 ((ht y h0).1 hy)
      obtain ⟨x, hx⟩ : ∃ x : 𝓞 D.host.E, x = ((d * (2 * M) : ℕ) : 𝓞 D.host.E) := ⟨_, rfl⟩
      have hprod : (x - rt) * (x + rt) ∈ I := by
        obtain ⟨k, hk⟩ := hdiv
        have e : (x - rt) * (x + rt) = (d : 𝓞 D.host.E) * ((d * (2 * M) ^ 2 + 1 : ℕ) : 𝓞 D.host.E) := by
          rw [hx]; push_cast; linear_combination (-1 : 𝓞 D.host.E) * rsq
        rw [e, hk]
        push_cast
        exact I.mul_mem_left _ (I.mul_mem_right _ hpI)
      have hxb : cO D x = x := by rw [hx]; exact map_natCast _ _
      have h2x : x + x ∈ I := by
        rcases hI.isPrime.mem_or_mem hprod with h | h
        · have := I.add_mem h (hb _ h)
          rwa [map_sub, hxb, hbar, show x - rt + (x - -rt) = x + x by ring] at this
        · have := I.add_mem h (hb _ h)
          rwa [map_add, hxb, hbar, show x + rt + (x + -rt) = x + x by ring] at this
      refine hco I _ hI.ne_top hcop hpI ?_
      have e : ((d * (2 * M) ^ 2 : ℕ) : 𝓞 D.host.E) = (x + x) * (M : 𝓞 D.host.E) := by rw [hx]; push_cast; ring
      rw [e]
      exact I.mul_mem_right _ h2x
  · have : Ideal.absNorm Q.asIdeal ∣ M := hM' ▸ Finset.dvd_prod_of_mem (fun Q : Pl D.host.E => Ideal.absNorm Q.asIdeal) hQ
    exact (h'.trans this).trans ⟨4 * d * M, by ring⟩

theorem exists_placesOK (D : D7) : ∃ P : Pl D.host.E, PlacesOK ∅ {P} := by
  have hf := Filter.eventually_cofinite.1 (FractionalIdeal.finite_factors (K := D.host.E) D.host.AA)
  obtain ⟨P, p, h1, h2, h3⟩ := exists_split_off D hf.toFinset
  refine ⟨P, ⟨{P}, Finset.empty_subset _, le_rfl, h1⟩, Finset.disjoint_empty_left _, fun PP hPP PP' h => ?_⟩
  obtain rfl : PP = P := by simpa using hPP
  by_contra hc
  refine h3 PP' (hf.mem_toFinset.2 hc) ?_
  rcases h with rfl | h
  · exact h2
  · obtain ⟨c, hc, e⟩ := h _ h2
    have : c = p := RingOfIntegers.ext (by rw [e]; simp)
    exact this ▸ hc

theorem exists_model (S T : HSp D) (hS : S.SigOK) (hpos : S.IsPosDef) (hT : T.SigOK) (hr : T.rank ≤ S.rank)
    (he : Even S.rank) (ho : Odd T.rank) (hsum : ∀ τ, (T.sig (tauE D τ)).1 + (T.sig (tauE D τ)).2 = T.rank) :
    ∃ (B : Base S T) (ψ : Twist D Circle), B.Good ∧ ψ.Good ∧ ψ.Q.Nonempty ∧ B.admitted ψ.Q ∧ B.vecFlat ψ ≠ 0 ∧
      (∃ (m : ℕ) (h : Fin m → GA D S), IsClassSystem S (B.levJ ψ) h) ∧
      (GlobalTheory.Published.WeilRepresentationUnitaryPair → ∃ ω ω', B.IsWeil 1 ω ∧ B.IsWeil ψ.chi ω') := by
  classical
  obtain ⟨F, hF⟩ := exists_frame_good S T hS hpos hT hr
  obtain ⟨P, hP⟩ := exists_placesOK D
  obtain ⟨η, hη⟩ := GlobalTheory.WeilParts.exists_isEtaTilde_unramified D
  obtain ⟨k, hk⟩ := id ho
  let c : D.what₂.Tau → ℤ := fun τ => (k : ℤ) - (T.sig (tauE D τ)).2
  let w : Weight D S.rank := ⟨fun τ => (T.sig (tauE D τ)).1, fun τ => (T.sig (tauE D τ)).2, fun _ _ => 0, fun _ _ => 0, c,
    fun τ => ⟨fun _ => c τ, fun _ _ _ => le_rfl⟩⟩
  let B : Base S T := ⟨hr, F, TypeDat.empty D _, Twist.triv Circle ∅, w, 1, η⟩
  have hB : B.Good :=
    { even := he
      odd := ho
      frame := hF
      de := Twist.triv_good splitSet_empty
      places := placesOK_empty
      wt := ⟨fun τ => (hsum τ).le.trans hr, fun τ i => by simp [B, w]⟩
      sig := fun _ => rfl
      sigOK := hT
      eta := hη
      hecke := ⟨continuous_const, fun _ => rfl⟩
      real := fun _ => rfl
      unram := fun _ _ _ _ _ => rfl
      tame := fun _ h => absurd h (Finset.notMem_empty _)
      inf := fun τ => ⟨0, by
        have h1 : (((T.sig (tauE D τ)).1 : ℕ) : ℚ) + (T.sig (tauE D τ)).2 = 2 * k + 1 := by
          exact_mod_cast (hsum τ).trans hk
        simp only [B, w, c]
        push_cast
        linarith, ⟨_, hF.vac.2.inf⟩, fun _ _ _ _ _ => by simp [B]⟩ }
  have hs : SplitSet {P} := by
    obtain ⟨R, -, h2, h3⟩ := hP.split
    exact h3.mono h2
  have hA : B.admitted {P} := ⟨by simpa [B, Twist.triv, TypeDat.empty] using hP, Finset.disjoint_empty_left _⟩
  refine ⟨B, Twist.triv Circle {P}, hB, Twist.triv_good hs, Finset.singleton_nonempty _, hA,
    vecFlat_ne_zero hB rfl _ hA, exists_isClassSystem B hF _, fun h => ?_⟩
  obtain ⟨ω, hω⟩ := exists_isWeil h hB (Twist.triv_good (A := Circle) hs)
  exact ⟨ω, ω, hω, hω⟩

theorem univCoef_ne_zero {k C : Type} [Field k] [Finite k] [AddCommGroup C] (β : DetBases k 1 2) (κ : kˣ →* Multiplicative C) :
    ∃ c, univCoef β κ c (!![1, 0] : Matrix (Fin 1) (Fin 2) k) ≠ 0 := by
  have hv : (![0, 1] : Fin 2 → k) ≠ 0 := fun h => one_ne_zero (congrFun h 1)
  let U : Planes k 1 2 := ⟨Submodule.span k {![0, 1]}, by rw [finrank_span_singleton hv]⟩
  have hU : Compl U.1 (!![1, 0] : Matrix (Fin 1) (Fin 2) k) := by
    refine eq_top_iff.2 fun v _ => ?_
    have : v = v 0 • (![1, 0] : Fin 2 → k) + v 1 • ![0, 1] := by ext i; fin_cases i <;> simp
    rw [this]
    exact Submodule.add_mem_sup (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
      (Submodule.smul_mem _ _ (Submodule.subset_span rfl))
  refine ⟨Multiplicative.toAdd (κ (Units.mk0 _ ((dU_ne_zero_iff β U _).2 hU))), ?_⟩
  rw [univCoef_eq]
  refine mul_ne_zero (inv_ne_zero (pow_ne_zero _ (by exact_mod_cast Nat.card_pos.ne'))) ?_
  exact Nat.cast_ne_zero.2 (Nat.card_ne_zero.2 ⟨⟨⟨U, _, rfl, rfl⟩⟩, inferInstance⟩)

end GlobalTheory.ExportSeries.Model

end
