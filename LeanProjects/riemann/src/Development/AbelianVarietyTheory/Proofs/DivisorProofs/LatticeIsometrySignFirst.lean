import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GenReads
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.ZeroNotAdmissibleOfRankPos
import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.TransformIndicator
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GramMapMulInv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SelfDualVectorPairsIntegralFrameColumns
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConjPrincipalFractionalIntegralIdempotentSum
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InverseSelfDualFrameStandardSpaceIntegral
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSelfDualCoordLatticeOfSelfDualFrame
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DcOpCommOfCommute
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsDualFamilySelfDualHermitianSpace
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.StdCharFinitePartRationalEqExpTrace

noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.DatumFourier

section Fourier

open NumberField Complex ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.AdTh GlobalTheory.LevelPairing
open scoped Classical

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} (l : Geo.Tor.Level H)

abbrev zM : ℂ := Complex.exp (2 * Real.pi * Complex.I / (l.M : ℂ))

theorem zM_prim : IsPrimitiveRoot (zM l) l.M :=
  Complex.isPrimitiveRoot_exp l.M (by have := l.three_le; omega)

theorem zM_ne : zM l ≠ 0 := Complex.exp_ne_zero _

theorem zM_congr {a b : ℤ} (h : (l.M : ℤ) ∣ a - b) : zM l ^ a = zM l ^ b := by
  have := ((zM_prim l).zpow_eq_one_iff_dvd (a - b)).2 h
  rwa [zpow_sub₀ (zM_ne l), div_eq_one_iff_eq (zpow_ne_zero _ (zM_ne l))] at this

theorem mk_levRep (q : LevQ Dw l) : Submodule.Quotient.mk (levRep q) = q :=
  Classical.choose_spec (Submodule.Quotient.mk_surjective _ q)

theorem mk_qRep {K : Submodule (𝓞 E) Dw.La} (q : Dw.La ⧸ K) : Submodule.Quotient.mk (qRep q) = q :=
  Classical.choose_spec (Submodule.Quotient.mk_surjective _ q)

def chr {n : ℕ} (w : Fin n → Dw.La) : AddChar (Fin n → LevQ Dw l) ℂ where
  toFun q := zM l ^ pairL (l := l) w (fun b => levRep (q b))
  map_zero_eq_one' := by
    rw [zM_congr l (b := pairL (l := l) w 0) (pairL_congr _ _ _ _ (fun b => by simp) fun b => by
      simpa using levRep_mk (l := l) (0 : Dw.La))]
    simp [pairL]
  map_add_eq_mul' q q' := by
    rw [← zpow_add₀ (zM_ne l), zM_congr l (b := pairL (l := l) w fun b => levRep (q b) + levRep (q' b))
      (pairL_congr _ _ _ _ (fun b => by simp) fun b => by
        rw [← Submodule.Quotient.eq, Submodule.Quotient.mk_add, mk_levRep, mk_levRep, mk_levRep, Pi.add_apply])]
    congr 1
    simp [pairL, Finset.sum_add_distrib]

theorem chr_eq_zero_iff {n : ℕ} (w : Fin n → Dw.La) :
    chr l w = 0 ↔ ∀ b, w b ∈ (Mfr l • ⊤ : Submodule (𝓞 E) Dw.La) := by
  constructor
  · intro h b
    refine mem_of_dvd fun y => ?_
    have h1 : zM l ^ pairL (l := l) w (fun i => levRep (Submodule.Quotient.mk ((Pi.single b y : Fin n → Dw.La) i) : LevQ Dw l)) = 1 :=
      DFunLike.congr_fun h (fun i => (Submodule.Quotient.mk ((Pi.single b y : Fin n → Dw.La) i) : LevQ Dw l))
    rw [zM_congr l (pairL_congr w w _ (Pi.single b y) (fun b => by simp) fun i => levRep_mk _),
      (zM_prim l).zpow_eq_one_iff_dvd] at h1
    unfold pairL at h1
    rw [Finset.sum_eq_single b (fun i _ hi => by simp [Pi.single_eq_of_ne hi]) (by simp)] at h1
    simpa using h1
  · intro h
    ext q
    change zM l ^ pairL (l := l) w (fun b => levRep (q b)) = 1
    rw [(zM_prim l).zpow_eq_one_iff_dvd]
    exact Finset.dvd_sum fun b _ => dvd_left _ (h b)

theorem inversion {n : ℕ} [Fintype (Fin n → LevQ Dw l)] (φ : (Fin n → LevQc Dw l) → ℂ) (x : Fin n → Dw.La) :
    ∑ q : Fin n → LevQ Dw l, ((Nat.card (Fin n → LevQ Dw l) : ℂ)⁻¹ * hatC l φ q) *
      zM l ^ (-pairL (l := l) x (fun b => levRep (q b))) = φ fun b => Submodule.Quotient.mk (x b) := by
  have : Finite (LevQc Dw l) := GlobalTheory.ClassSumProbe.finite_conj_half
  have := Fintype.ofFinite (Fin n → LevQc Dw l)
  have h1 : ∀ q : Fin n → LevQ Dw l, ((Nat.card (Fin n → LevQ Dw l) : ℂ)⁻¹ * hatC l φ q) *
      zM l ^ (-pairL (l := l) x (fun b => levRep (q b))) =
      ∑ y : Fin n → LevQc Dw l, (Nat.card (Fin n → LevQ Dw l) : ℂ)⁻¹ * φ y * chr l (fun b => qRep (y b) - x b) q := fun q => by
    rw [hatC, finsum_eq_sum_of_fintype, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun y _ => ?_
    change _ * (_ * zM l ^ _) * _ = _ * zM l ^ pairL (l := l) (fun b => qRep (y b) - x b) (fun b => levRep (q b))
    rw [mul_assoc, mul_assoc, mul_assoc _ (φ y), ← zpow_add₀ (zM_ne l)]
    congr 3
    simp only [pairL, map_sub, LinearMap.sub_apply, Finset.sum_sub_distrib]
    ring
  simp only [h1]
  rw [Finset.sum_comm, Finset.sum_eq_single (fun b => Submodule.Quotient.mk (x b))]
  · rw [← Finset.mul_sum, AddChar.sum_eq_ite, if_pos ((chr_eq_zero_iff l _).2 fun b => by
      rw [← Submodule.Quotient.eq, mk_qRep]), Nat.card_eq_fintype_card]
    have : (Fintype.card (Fin n → LevQ Dw l) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
    field_simp
  · intro y _ hy
    rw [← Finset.mul_sum, AddChar.sum_eq_ite, if_neg, mul_zero]
    rw [chr_eq_zero_iff]
    exact fun h => hy (funext fun b => by rw [← mk_qRep (y b), Submodule.Quotient.eq]; exact h b)
  · simp

end Fourier

section General

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
  IsDedekindDomain NumberField Matrix GlobalTheory.LatVac GlobalTheory.AdelicLatMove GlobalTheory.PlaceVec
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {S T : HSp D} {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
  {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}

theorem approx_mod {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)} {k : ℕ} (hk : 0 < k) {t : WO S T}
    (ht : t ∈ latO S T LS LT fun _ => True) :
    ∃ M ∈ latRat S T LS LT, ∃ u ∈ latO S T LS LT (fun _ => True), t = finTens 1 M + k • u := by
  refine latO_induction (p := fun t => ∃ M ∈ latRat S T LS LT, ∃ u ∈ latO S T LS LT (fun _ => True),
    t = finTens 1 M + k • u) ?_ ?_ ?_ ?_ ht
  · intro α hα M hM
    obtain ⟨x, β, hβ, hx⟩ := (GlobalTheory.AdLat.strong_approximation_mod_nat D.host.F k hk).2 α hα
    refine ⟨_, smul_mem_latRat (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x) hM, _, finTens_mem_latO (α := β) hβ hM, ?_⟩
    ext i j
    refine GlobalTheory.SplitScalar.adele_ext ?_ ?_
    · rw [Matrix.add_apply, RingHom.map_add, Matrix.smul_apply, map_nsmul]
      simp only [finTens, Matrix.map_apply, infPart_pair, smul_zero, add_zero]
    · rw [Matrix.add_apply, RingHom.map_add, Matrix.smul_apply, map_nsmul]
      simp only [finTens, Matrix.map_apply, finPart_pair]
      rw [hx, approx_tmul, TensorProduct.tmul_smul k, Algebra.smul_def]
      rfl
  · exact ⟨0, zero_mem _, 0, zero_mem _, by rw [finTens_zero, smul_zero, add_zero]⟩
  · rintro _ _ ⟨M, hM, u, hu, rfl⟩ ⟨M', hM', u', hu', rfl⟩
    exact ⟨_, add_mem hM hM', _, add_mem hu hu', by rw [finTens_add, smul_add]; abel⟩
  · rintro _ ⟨M, hM, u, hu, rfl⟩
    exact ⟨_, neg_mem hM, _, neg_mem hu, by rw [finTens_neg, smul_neg]; abel⟩

theorem mem_latG_one {β : GL (Fin T.rank) (EAf D)} (hβ : IsSDFrame T β ΛT 1) (v : Fin T.rank → D.host.E) :
    finVec T v ∈ gLat T 1 ↔ v ∈ ΛT := by
  rw [GlobalTheory.PrincInLevel.eq_latC hβ]
  obtain ⟨h1, -, hfg, hsp, -⟩ := GlobalTheory.Member.latHat_eq_hat_and_gram D T
  rw [← ((GlobalTheory.AdLat.hat_rational_points_and_approx D.host.F D.host.E T.rank _ hfg hsp).1 v), ← h1]
  constructor
  · rintro ⟨z, hz, e⟩
    rw [map_one, Units.val_one, Matrix.one_mulVec] at e
    subst e
    exact hz
  · intro h
    exact ⟨_, h, by rw [map_one, Units.val_one, Matrix.one_mulVec]; rfl⟩

theorem star_int (c : 𝓞 D.host.E) : ∃ c' : 𝓞 D.host.E, (c' : D.host.E) = star (c : D.host.E) :=
  ⟨⟨_, (RingOfIntegers.isIntegral_coe c).map (starRingEnd D.host.E).toIntAlgHom⟩, rfl⟩

theorem mem_latRat_iff (hG : S.gram = 1)
    (hS : ΛS = Submodule.pi Set.univ fun _ => (1 : Submodule (𝓞 D.host.E) D.host.E))
    {β : GL (Fin T.rank) (EAf D)} (hβ : IsSDFrame T β ΛT 1) (M : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    M ∈ latRat S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) ↔
      ∀ b, (fun a => M a b) ∈ latG T 1 := by
  have hg : ∀ (s : Fin S.rank → D.host.E) j, ∑ k, star (s k) * S.gram k j = star (s j) := fun s j => by
    rw [hG, Finset.sum_eq_single j (fun k _ hk => by rw [Matrix.one_apply_ne hk, mul_zero]) (by simp),
      Matrix.one_apply_eq, mul_one]
  constructor
  · intro hM b
    induction hM using AddSubgroup.closure_induction with
    | mem w hw =>
      obtain ⟨a, ha, s, hs, t, ht, rfl⟩ := hw
      rw [hS] at hs
      obtain ⟨c, hc⟩ := Submodule.mem_one.1 (hs b trivial)
      obtain ⟨c', hc'⟩ := star_int c
      have h1 : a • t ∈ latG T 1 := Submodule.subset_span ⟨a, ha, t, (mem_latG_one hβ t).2 ht, rfl⟩
      convert Submodule.smul_mem _ c' h1 using 1
      funext i
      change a * t i * _ = (c' : D.host.E) * (a * t i)
      rw [hg, hc', ← hc, mul_comm]
    | zero => exact zero_mem _
    | add x y _ _ hx hy => exact add_mem hx hy
    | neg x _ hx => exact neg_mem hx
  · intro h
    have key : ∀ b, ∀ v ∈ latG T 1, (Matrix.of fun a j => v a * (Pi.single b 1 : Fin S.rank → D.host.E) j) ∈
        latRat S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) := by
      intro b v hv
      induction hv using Submodule.span_induction with
      | mem v hv =>
        obtain ⟨a, ha, t, ht, rfl⟩ := hv
        refine AddSubgroup.subset_closure ⟨a, ha, Pi.single b 1, ?_, t, (mem_latG_one hβ t).1 ht, ?_⟩
        · rw [hS]
          intro k _
          rw [Pi.single_apply]
          split_ifs
          · exact Submodule.mem_one.2 ⟨1, map_one _⟩
          · exact zero_mem _
        · ext i j
          simp only [genMap, Matrix.of_apply, hg, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
          split_ifs <;> simp
      | zero => convert (latRat S T _ _).zero_mem using 1; ext i j; simp
      | add x y _ _ hx hy => convert add_mem hx hy; ext i j; simp [add_mul]
      | smul c x _ hx =>
        convert smul_mem_latRat c hx using 1
        exact Matrix.ext fun i j => mul_assoc (c : D.host.E) (x i) _
    have e : M = ∑ b, Matrix.of fun a j => M a b * (Pi.single b 1 : Fin S.rank → D.host.E) j := by
      ext i j
      simp [Matrix.sum_apply, Pi.single_apply]
    rw [e]
    exact sum_mem fun b _ => key b _ (h b)

theorem frMapAdj_half (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (e : AE D) (α : Af D.host.F)
    (M : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    frMapAdj S T βS βT (cA D e • finTens α M) =
      ((1 : D.host.E) ⊗ₜ[D.host.F] α : EAf D) • FWT.uMat S T βS βT e fun b a => M a b := by
  have h1 : (((cA D e • finTens α M).map (toEAf D)).map (cF D))ᵀ =
      (((1 : D.host.E) ⊗ₜ[D.host.F] α : EAf D) * toEAf D e) •
        (Matrix.of fun b a => D.sp.cm.sig (M a b)).map (eToEAf D) := by
    ext b a
    change cF D (toEAf D (cA D e * finTens α M a b)) = _ * eToEAf D (D.sp.cm.sig (M a b))
    rw [RingHom.map_mul, RingHom.map_mul, toEAf_cA, cF_cF_toEAf, mul_comm _ (toEAf D e), mul_assoc]
    congr 1
    change star (M a b) ⊗ₜ[D.host.F] α = ((1 : D.host.E) ⊗ₜ[D.host.F] α) * (star (M a b) ⊗ₜ[D.host.F] 1)
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
  rw [frMapAdj_eq, h1, Matrix.mul_smul, Matrix.smul_mul, mul_smul]
  congr 1
  ext b a
  unfold FWT.uMat
  rw [Matrix.map_mul, Matrix.map_mul]
  simp only [Matrix.mul_assoc]
  rfl

theorem conj_map {m n : ℕ} (A : Matrix (Fin m) (Fin n) D.host.E) :
    (((A.map (incA D)).map (toEAf D)).map (cF D))ᵀ = Aᴴ.map (eToEAf D) := rfl

theorem idem_div_int {e : AE D} {P : Finset (Formalism.L2.DIV.Pl D.host.E)} (he : IsIdemSum e P) {N : ℕ} (hN : N ≠ 0)
    (hP : ∀ PP ∈ P, (N : 𝓞 D.host.E) ∉ PP.asIdeal) :
    toEAf D (e * incA D (N : D.host.E)⁻¹) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := he
  rw [Finset.sum_mul, map_sum]
  refine sum_mem fun PP hPP => GlobalTheory.IdemIntegral.toEAf_mem_of_finPart ?_
  by_contra h
  refine hP PP hPP (((hes PP hPP).2 _ (Nat.cast_ne_zero.2 hN)).2 ?_)
  rwa [show ((N : 𝓞 D.host.E) : D.host.E) = N from map_natCast (algebraMap (𝓞 D.host.E) D.host.E) N]

set_option maxHeartbeats 4000000 in

theorem mem_latO_of_int {βS : GL (Fin S.rank) (EAf D)} {βT : GL (Fin T.rank) (EAf D)}
    (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT) (fS : Formalism.L2.DIV.IsFrame βS ΛS) (fT : Formalism.L2.DIV.IsFrame βT ΛT)
    {e : AE D} {P : Finset (Formalism.L2.DIV.Pl D.host.E)} (he : IsIdemSum e P) {N : ℕ} (hN : N ≠ 0)
    (hA : (N : D.host.E) ∈ D.host.AA) (hP : ∀ PP ∈ P, (N : 𝓞 D.host.E) ∉ PP.asIdeal) {x : WO S T}
    (hx : IsHalf (cA D e) x) (hi : IsIntM (frMapAdj S T βS βT x)) :
    x ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True := by
  obtain ⟨n, s, s', hs, hss⟩ := GlobalTheory.LatVacDual.dualFamily D S ΛS hS
  obtain ⟨m, t, t', ht, htt⟩ := GlobalTheory.LatVacDual.dualFamily D T ΛT hT
  obtain ⟨s₁, hs₁⟩ : ∃ A : Matrix (Fin S.rank) (Fin n) D.host.E, A = Matrix.of fun a k => s k a := ⟨_, rfl⟩
  obtain ⟨s₂, hs₂⟩ : ∃ A : Matrix (Fin S.rank) (Fin n) D.host.E, A = Matrix.of fun a k => s' k a := ⟨_, rfl⟩
  obtain ⟨t₁, ht₁⟩ : ∃ A : Matrix (Fin T.rank) (Fin m) D.host.E, A = Matrix.of fun a k => t k a := ⟨_, rfl⟩
  obtain ⟨t₂, ht₂⟩ : ∃ A : Matrix (Fin T.rank) (Fin m) D.host.E, A = Matrix.of fun a k => t' k a := ⟨_, rfl⟩
  have e1 : s₁ * (s₂ᴴ * S.gram) = 1 := by
    subst hs₁ hs₂
    exact Matrix.ext fun a j => (hss a j).trans (Matrix.one_apply).symm
  have e2 : t₁ * (t₂ᴴ * T.gram) = 1 := by
    subst ht₁ ht₂
    exact Matrix.ext fun a j => (htt a j).trans (Matrix.one_apply).symm
  obtain ⟨w, hw⟩ : ∃ w : Matrix (Fin m) (Fin n) (AE D), w = (t₂ᴴ * T.gram).map (incA D) * x * s₁.map (incA D) := ⟨_, rfl⟩
  have hx' : cA D e • x = x := Matrix.ext hx
  have hw1 : cA D e • w = w := by rw [hw, ← Matrix.smul_mul, ← Matrix.mul_smul, hx']
  have hG : T.gramᴴ = T.gram := Matrix.ext fun i j => gram_star T j i
  have hw2 : ((w.map (toEAf D)).map (cF D))ᵀ = (s₁ᴴ * S.gram).map (eToEAf D) * βS.val * frMapAdj S T βS βT x *
      ((βT⁻¹).val * t₂.map (eToEAf D)) := by
    rw [hw, Matrix.map_mul (f := toEAf D), Matrix.map_mul (f := toEAf D), Matrix.map_mul (f := cF D),
      Matrix.map_mul (f := cF D), Matrix.transpose_mul,
      Matrix.transpose_mul, conj_map, conj_map, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hG,
      frMapAdj_eq, Matrix.map_mul, Matrix.map_mul]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc βS.val, Units.mul_inv, Matrix.one_mul, ← Matrix.mul_assoc βT.val, Units.mul_inv, Matrix.one_mul,
      ← Matrix.mul_assoc (S.gram.map (eToEAf D)), gram_map_mul_inv, Matrix.one_mul]
  have hcol : ∀ a, (fun k => βS.val k a) ∈ Formalism.L2.Herm.hatL (F := D.host.F) ΛS := fun a => by
    refine (fS _).2 fun i => ?_
    have e : ((βS⁻¹).val *ᵥ fun k => βS.val k a) i = ((βS⁻¹).val * βS.val) i a := rfl
    rw [e, Units.inv_mul, Matrix.one_apply]
    split_ifs
    exacts [one_mem _, zero_mem _]
  have i1 : IsIntM ((s₁ᴴ * S.gram).map (eToEAf D) * βS.val) := fun k a => by
    refine GlobalTheory.PairIntegral.sum_mem_intAf ΛS (fun j => (s₁ᴴ * S.gram) k j) (fun y hy => ?_) _ (hcol a)
    obtain ⟨b, hb⟩ := (hS.2 y).1 hy _ (hs k).1
    refine ⟨b, hb.trans ?_⟩
    rw [Finset.sum_comm, hs₁]
    exact Finset.sum_congr rfl fun j _ => (Finset.sum_mul _ _ _).symm
  have i2 : IsIntM ((βT⁻¹).val * t₂.map (eToEAf D)) := fun a k => by
    rw [ht₂]
    exact (fT _).1 (pure_mem_hatL ΛT 1 (one_mem _) _ (ht k).2) a
  have hw3 : ∀ i k, toEAf D (w i k * incA D (N : D.host.E)⁻¹) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := fun i k => by
    have h1 : cF D (toEAf D (w i k)) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
      rw [show cF D (toEAf D (w i k)) = _ from congrFun (congrFun hw2 k) i, Matrix.mul_apply]
      refine sum_mem fun p _ => mul_mem ?_ (i2 p i)
      rw [Matrix.mul_apply]
      exact sum_mem fun q _ => mul_mem (i1 k q) (hi q p)
    have h2 := cF_mem_int (mul_mem h1 (idem_div_int he hN hP))
    have h3 : cA D (incA D (N : D.host.E)⁻¹) = incA D (N : D.host.E)⁻¹ := by
      change incA D (star (N : D.host.E)⁻¹) = _
      rw [star_inv₀, star_natCast]
    rwa [RingHom.map_mul, cF_cF_toEAf, ← toEAf_cA, ← RingHom.map_mul, RingHom.map_mul (cA D), h3, ← mul_assoc,
      mul_comm (w i k), show cA D e * w i k = w i k from congrFun (congrFun hw1 i) k] at h2
  have hxw : x = t₁.map (incA D) * w * (s₂ᴴ * S.gram).map (incA D) := by
    rw [hw, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.map_mul, e2, Matrix.mul_assoc, ← Matrix.map_mul, e1,
      Matrix.map_one _ (RingHom.map_zero _) (RingHom.map_one _), Matrix.map_one _ (RingHom.map_zero _) (RingHom.map_one _),
      Matrix.one_mul, Matrix.mul_one]
  have hsum : x = ∑ k, ∑ i, (w i k * incA D (N : D.host.E)⁻¹) • finTens 1 (genMap S T N (s' k) (t i)) := by
    rw [hxw]
    ext a j
    simp only [Matrix.mul_apply (M := t₁.map (incA D) * w), Matrix.mul_apply (M := t₁.map (incA D)), Matrix.sum_apply,
      Finset.sum_mul, Matrix.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
    have h0 : infPart D (w i k) = 0 := by
      rw [← show cA D e * w i k = w i k from congrFun (congrFun hw1 i) k, RingHom.map_mul,
        infPart_cA (idemSum_infPart he), zero_mul]
    refine GlobalTheory.SplitScalar.adele_ext (by simp only [RingHom.map_mul, h0, mul_zero, zero_mul]) ?_
    have h4 : finPart D (finTens 1 (genMap S T N (s' k) (t i)) a j) =
        finPart D (incA D (N * t₁ a i * (s₂ᴴ * S.gram) k j)) := by
      rw [ht₁, hs₂]; rfl
    have h5 : incA D (t₁ a i) * w i k * incA D ((s₂ᴴ * S.gram) k j) =
        w i k * incA D (N : D.host.E)⁻¹ * incA D (N * t₁ a i * (s₂ᴴ * S.gram) k j) := by
      rw [mul_assoc (w i k), ← RingHom.map_mul (incA D), mul_assoc (N : D.host.E),
        inv_mul_cancel_left₀ (Nat.cast_ne_zero.2 hN), RingHom.map_mul (incA D), ← mul_assoc, mul_comm (w i k)]
    rw [Matrix.map_apply, Matrix.map_apply, h5]
    exact ((finPart D).map_mul _ _).trans ((congrArg (fun z => finPart D (w i k * incA D (N : D.host.E)⁻¹) * z) h4.symm).trans
      ((finPart D).map_mul _ _).symm)
  rw [hsum]
  exact sum_mem fun k _ => sum_mem fun i _ => GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ _ (finPart_mem_intAE (hw3 i k)) _
    (finTens_mem_latO (one_mem_intAf _) (AddSubgroup.subset_closure ⟨_, hA, _, (hs k).2, _, (ht i).1, rfl⟩))

theorem int_of_mem_latO {βS : GL (Fin S.rank) (EAf D)} {βT : GL (Fin T.rank) (EAf D)} {e : AE D}
    {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)}
    (h : ∀ M ∈ latRat S T LS LT, IsIntM (FWT.uMat S T βS βT e fun b a => M a b)) {u : WO S T}
    (hu : u ∈ latO S T LS LT fun _ => True) : IsIntM (frMapAdj S T βS βT (cA D e • u)) := by
  let g : WO S T →+ Matrix (Fin S.rank) (Fin T.rank) (EAf D) := AddMonoidHom.mk' _ (frMapAdj_add S T βS βT)
  refine latO_induction (p := fun u => IsIntM (g (cA D e • u))) ?_ ?_ ?_ ?_ hu
  · intro α hα M hM i j
    change frMapAdj S T βS βT _ i j ∈ _
    rw [frMapAdj_half]
    exact mul_mem (Subring.subset_closure (Or.inr ⟨⟨α, hα⟩, rfl⟩)) (h M hM i j)
  · rw [smul_zero, map_zero]; exact fun _ _ => zero_mem _
  · intro x y hx hy; rw [smul_add, map_add]; exact fun i j => add_mem (hx i j) (hy i j)
  · intro x hx; rw [smul_neg, map_neg]; exact fun i j => neg_mem (hx i j)

theorem idemSum_unique (V : HSp D) {e e' : AE D} {P : Finset (Formalism.L2.DIV.Pl D.host.E)} (h : IsIdemSum e P)
    (h' : IsIdemSum e' P) : e' = e := by
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := h
  obtain ⟨⟨es', hes', rfl⟩, -⟩ := h'
  exact Finset.sum_congr rfl fun PP hPP => GlobalTheory.SplitHeckeAdj.idem_unique V (hes PP hPP) (hes' PP hPP)

theorem thetaAt_eq_sum {ψ : AddChar (AF D.host.F) ℂ} {e : AE D} {Λ : AddSubgroup (WO S T)} {f₀ Φ f : WO S T → ℂ}
    {I : Type} [Fintype I] (y : I → WO S T) (a : I → ℂ) (hθ : IsThetaAt ψ (symplO S T) (heisO ψ S T) e Λ 1 f₀ Φ f)
    (hY : ∀ q, IsHalf (cA D e) (y q)) (hΦ : ∀ t, Φ t = halfInd e Λ t * ∑ q, a q * ψ (symplO S T t (y q))) :
    f = ∑ q, a q • heisO ψ S T (y q) f₀ := by
  obtain ⟨⟨Tm, hTm⟩, hall⟩ := hθ
  have hΦ' : Φ = ∑ q, a q • fun t => ψ (symplO S T t (y q)) * halfInd e Λ t := by
    funext t
    rw [hΦ t, Finset.sum_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  have hvac : Tm (halfInd e Λ) = f₀ := by simpa using hTm.vac
  rw [hall Tm hTm, hΦ', map_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [map_smul, hTm.modul _ (GlobalTheory.isSBHalf_halfInd e Λ) _ (hY q), hvac]

theorem hRat_std (hG : S.gram = 1) (X Y : Fin S.rank → Fin T.rank → D.host.E) (c : D.host.E) (hc : star c = c) :
    hRat S T (Matrix.of fun a b => X b a) (Matrix.of fun a b => c * Y b a) =
      c * ∑ b, T.hT (T.frame.equivFun.symm (Y b)) (T.frame.equivFun.symm (X b)) := by
  unfold hRat
  rw [hG, inv_one, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_eq_single b (fun k _ hk => by simp [Matrix.one_apply_ne hk.symm]) (by simp)]
  simp only [Module.Basis.equivFun_symm_apply, map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply,
    map_smul, smul_eq_mul, Finset.mul_sum, Matrix.one_apply_eq, Matrix.of_apply, star_mul', hc, HSpace.gram]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  simp only [starRingEnd_apply]
  ring

theorem char_eq {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT)
    {e : AE D} (he : infPart D e = 0) {k : ℕ} {t u : WO S T} (ht : IsHalf (cA D e) t)
    (hu : u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True)
    {M Y : Matrix (Fin T.rank) (Fin S.rank) D.host.E} (htM : t = finTens 1 M + k • u)
    (hY : k • Y ∈ latRat S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E))) :
    ψ (symplO S T t (Matrix.of fun a b => e * incA D (Y a b))) =
      Complex.exp (2 * Real.pi * Complex.I * ((Algebra.trace ℚ D.host.E (D.host.xi0 * hRat S T M Y) : ℚ) : ℂ)) := by
  have h1 : (Matrix.of fun a b => e * incA D (Y a b) : WO S T) = cA D (cA D e) • finTens 1 Y := by
    rw [GlobalTheory.LatVac.cA_cA]
    ext a b
    refine GlobalTheory.SplitScalar.adele_ext ?_ ?_
    · change infPart D (e * _) = infPart D (e * _)
      rw [RingHom.map_mul, RingHom.map_mul, he, zero_mul, zero_mul]
    · change finPart D (e * _) = finPart D (e * _)
      rw [RingHom.map_mul, RingHom.map_mul]
      rfl
  have h2 : symplO S T (k • u) (finTens 1 Y) = symplO S T u (finTens 1 (k • Y)) := by
    have : finTens (1 : Af D.host.F) (k • Y) = k • finTens 1 Y :=
      (AddMonoidHom.mk' (finTens (1 : Af D.host.F)) (finTens_add 1)).map_nsmul k Y
    rw [this, ← symplHom_apply, ← symplHom_apply, map_nsmul, map_nsmul]
    rfl
  rw [h1, ← GlobalTheory.PlaceModel.symplO_smul, show cA D e • t = t from Matrix.ext ht, htM, symplO_add_left,
    ψ.map_add_eq_mul, h2, char_sympl_eq_one hψ hS hT hu (finTens_mem_latO (one_mem_intAf _) hY), mul_one, symplO_finTens,
    one_mul, one_mul, GlobalTheory.StdRat.stdChar_fin_rat D ψ hψ, Algebra.trace_trace]

end General

open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1600000 in

theorem thetaVector_eq_sum_heisenberg : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.Char F → ∀ (i : Fin D.R.m), VStd D i → ∀ (H : Geo.Tor.Host D.host.E) (Dw : Datum H) (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin (Wc D i).rank → D.host.E)), LatEmb (Wc D i) ι → LatIsom (Wc D i) Dw.EF ι → ∃ δ : ℤˣ, ∀ (t : T0) (l₂ : Geo.Tor.Level H) (φ : (Fin (Vc D i).rank → LevQc Dw l₂) → ℂ), PhiIs R i (RingHom.id ℂ) t ι (Mfr l₂ • ⊤) φ → (∀ PP, PP ∈ R.Pg ∨ PP ∈ R.Q t → l₂.Mb ≤ PP.asIdeal ∧ ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) → ∀ e : AE D, IsIdemSum e (R.Pg ∪ R.Q t) → R.vP i t = ((Nat.card (Fin (Vc D i).rank → LevQ Dw l₂) : ℂ))⁻¹ • ∑ᶠ q : Fin (Vc D i).rank → LevQ Dw l₂, hatC l₂ φ q • heisO R.ψ (Vc D i) (Wc D i) (Matrix.of fun a b => e * incA D (((δ : ℤ) : D.host.E) * ι (cSep l₂ • levRep (q b)) a / (l₂.M : D.host.E))) (R.vacP i) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hR i hV H Dw ι hι hI
  obtain ⟨ε, hε⟩ := hI
  refine ⟨ε, fun t l φ hφ hP e he => ?_⟩
  obtain ⟨hvac, e₁, he₁, hθ⟩ := hR.thP.vP i t
  obtain ⟨e₂, he₂, hφ⟩ := hφ
  obtain rfl := idemSum_unique (Vc D i) he₁ he
  obtain rfl := idemSum_unique (Vc D i) he₂ he
  have hβV := hR.lev.βV i
  have hβW := hR.lev.βW i
  have hS := GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ hβV
  have hT := GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ hβW
  have hstd : R.ΛV i = Submodule.pi Set.univ fun _ => (1 : Submodule (𝓞 D.host.E) D.host.E) := by
    rw [GlobalTheory.PrincInLevel.eq_latC hβV, ← GlobalTheory.SplitReps.hLat_one, hV.2]
  have hlat := mem_latRat_iff hV.1 hstd hβW
  have hM : l.M ≠ 0 := by have := l.three_le; omega
  have hM' : (l.M : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hM
  have hsurj : ∀ M ∈ GlobalTheory.LatVac.latRat (Vc D i) (Wc D i) (R.ΛV i : Set (Fin (Vc D i).rank → D.host.E))
      (R.ΛW i : Set (Fin (Wc D i).rank → D.host.E)), ∃ x : Fin (Vc D i).rank → Dw.La, M = Matrix.of fun a b => ι (x b) a := by
    intro M hM
    choose x hx using fun b => hι.2.ge ((hlat M).1 hM b)
    exact ⟨x, Matrix.ext fun a b => (congrFun (hx b) a).symm⟩
  have hint : ∀ u ∈ latO (Vc D i) (Wc D i) (R.ΛV i : Set (Fin (Vc D i).rank → D.host.E))
      (R.ΛW i : Set (Fin (Wc D i).rank → D.host.E)) (fun _ => True),
      IsIntM (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) (cA D e • u)) := fun u hu =>
    int_of_mem_latO (fun M hM => by
      obtain ⟨x, rfl⟩ := hsurj M hM
      exact (hφ x).1) hu
  have : Finite (LevQ Dw l) := GlobalTheory.LevelPairing.finite_LevQ
  have := Fintype.ofFinite (Fin (Vc D i).rank → LevQ Dw l)
  rw [finsum_eq_sum_of_fintype, Finset.smul_sum]
  simp only [smul_smul]
  refine thetaAt_eq_sum _ _ hθ (fun q a b => ?_) fun w => ?_
  · rw [GlobalTheory.LatVac.cA_cA, Matrix.of_apply, ← mul_assoc, GlobalTheory.PlaceVec.idemSum_mul_self he]
  by_cases hw : w ∈ latO (Vc D i) (Wc D i) (R.ΛV i : Set (Fin (Vc D i).rank → D.host.E))
      (R.ΛW i : Set (Fin (Wc D i).rank → D.host.E)) (fun _ => True) ∧ IsHalf (cA D e) w
  swap
  · rw [halfInd, if_neg hw, zero_mul, if_neg]
    rintro ⟨h1, h2⟩
    have hN : ∀ PP ∈ R.Pg ∪ R.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal := fun PP hPP h =>
      (hP PP (Finset.mem_union.1 hPP)).2 (by rw [Nat.cast_mul]; exact Ideal.mul_mem_left _ _ h)
    exact hw ⟨mem_latO_of_int hS hT hβV.choose_spec.1 hβW.choose_spec.1 he (Ideal.absNorm_eq_zero_iff.not.2 D.host.ccK_ne_bot)
      (ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA.normCc_mem_AA D) hN h1 h2, h1⟩
  have hw' : cA D e • w = w := Matrix.ext hw.2
  obtain ⟨M, hM0, u, hu, hwM⟩ := approx_mod (Nat.pos_of_ne_zero hM) hw.1
  obtain ⟨x, rfl⟩ := hsurj M hM0
  have hfr : frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) w =
      uMat (Vc D i) (Wc D i) (R.βV i) (R.βW i) e (fun b => ι (x b)) +
        l.M • frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) (cA D e • u) := by
    rw [← hw', hwM, smul_add, GlobalTheory.PlaceVec.frMapAdj_add, frMapAdj_half, smul_comm]
    congr 1
    · exact one_smul _ _
    · exact (AddMonoidHom.mk' _ (GlobalTheory.PlaceVec.frMapAdj_add _ _ (R.βV i) (R.βW i))).map_nsmul _ _
  have hred : ∀ PP, PP ∈ R.Pg ∨ PP ∈ R.Q t → redM PP (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) w) =
      redM PP (uMat (Vc D i) (Wc D i) (R.βV i) (R.βW i) e (fun b => ι (x b))) := fun PP hPP => by
    rw [hfr]
    have : Ideal.span {(l.M : 𝓞 D.host.E)} ≤ l.Mb := l.prod ▸ Ideal.mul_le_left
    exact GlobalTheory.PlaceVec.redM_add_nsmul PP ((hP PP hPP).1 (this (Ideal.subset_span rfl))) (hφ x).1 (hint u hu)
  rw [halfInd, if_pos hw, one_mul, if_pos ⟨hw.2, hw' ▸ hint w hw.1⟩,
    GlobalTheory.PlaceVec.omegaK_congr _ fun PP h => hred PP (Or.inl h),
    GlobalTheory.PlaceVec.omegaQ_congr _ _ _ _ fun PP h => hred PP (Or.inr h), ← (hφ x).2, RingHom.id_apply, ← inversion l φ x]
  refine Finset.sum_congr rfl fun q _ => congrArg _ ?_
  have hY : (Matrix.of fun a b => ((ε : ℤ) : D.host.E) * ι (cSep l • levRep (q b)) a / (l.M : D.host.E)) =
      Matrix.of fun a b => (((ε : ℤ) : D.host.E) / (l.M : D.host.E)) * ι (cSep l • levRep (q b)) a :=
    Matrix.ext fun a b => by simp only [Matrix.of_apply]; ring
  refine Eq.trans ?_ (char_eq (Y := Matrix.of fun a b => ((ε : ℤ) : D.host.E) * ι (cSep l • levRep (q b)) a / (l.M : D.host.E))
    hvac.1 hS hT (GlobalTheory.PlaceVec.idemSum_infPart he) hw.2 hu hwM ((hlat _).2 fun b => ?_)).symm
  · rw [hY, hRat_std hV.1 _ _ _ (by rw [star_div₀, star_intCast, star_natCast]), ← Complex.exp_int_mul]
    congr 1
    have h1 : ∀ c : ℚ, ∀ z : D.host.E, Algebra.trace ℚ D.host.E (D.host.xi0 * ((c : D.host.E) * z)) =
        c * Algebra.trace ℚ D.host.E (D.host.xi0 * z) := fun c z => by
      rw [mul_left_comm, ← Rat.smul_def, map_smul, smul_eq_mul]
    have h2 : ∀ y z, Dw.EF y z = -Dw.EF z y := fun y z => (LinearMap.IsAlt.neg Dw.alt z y).symm
    have h3 : ((pairL (l := l) x (fun b => levRep (q b)) : ℤ) : ℚ) = -(((ε : ℤ) : ℚ) * Algebra.trace ℚ D.host.E (D.host.xi0 *
        ∑ b, (Wc D i).hT ((Wc D i).frame.equivFun.symm (ι (cSep l • levRep (q b)))) ((Wc D i).frame.equivFun.symm (ι (x b))))) := by
      rw [pairL, Int.cast_sum, Finset.mul_sum, map_sum, Finset.mul_sum, ← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun b _ => by rw [h2, Int.cast_neg, hε]
    have h4 := congrArg (fun z : ℚ => (z : ℂ)) h3
    rw [show (((ε : ℤ) : D.host.E) / (l.M : D.host.E)) = ((((ε : ℤ) : ℚ) / (l.M : ℚ) : ℚ) : D.host.E) by push_cast; rfl, h1]
    push_cast at h4 ⊢
    rw [h4]
    ring
  · have h1 := hι.2.le (LinearMap.mem_range_self ι ((ε : ℤ) • cSep l • levRep (q b)))
    convert h1 using 1
    funext a
    rw [map_zsmul, Matrix.smul_apply, Matrix.of_apply, nsmul_eq_mul, mul_div_cancel₀ _ hM', Pi.smul_apply, zsmul_eq_mul]

end GlobalTheory.DatumFourier

end
