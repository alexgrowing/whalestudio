import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Formalism.SharpRestriction.Divisibility.KudlaSiegelWeil
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertPlaceHeckeDoubleCosetsInverseRepsLabel
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemHomLatticeIffIntegralMatrixSplitChart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnramifiedConjugatePlaceUniformiser
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsFinWeil
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsDeltaPsi

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Datum Formalism.IndefR.Mult
open IsDedekindDomain NumberField Matrix
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.InertLoc

open Formalism.UG (intL IsUnramInv UJ GLint cT cT_mul cT_one)
open GlobalTheory.LatticeStable GlobalTheory.SplitScalar GlobalTheory.SplitHomLattice

variable {D : D7} {P : HeightOneSpectrum (𝓞 D.host.E)} {e : AE D} {σ : LP D P →+* LP D P} {π : AE D →+* LP D P}

theorem Chart.mul_eq_iff (h : Chart e σ π) {a b : AE D} : e * a = e * b ↔ π a = π b := by
  rw [← sub_eq_zero, ← mul_sub, ← h.2.2.1, RingHom.map_sub, sub_eq_zero]

theorem Chart.pi_idem (h : Chart e σ π) : π e = 1 := by
  rw [← π.map_one, ← h.mul_eq_iff, h.1.1, mul_one]

theorem Chart.idem_int (h : Chart e σ π) : finPart D e ∈ intAE D :=
  GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, h.1.1])

theorem Chart.ext (h : Chart e σ π) {a b : AE D} (ha : e * a = a) (hb : e * b = b) (hab : π a = π b) : a = b := by
  rw [← ha, ← hb, h.mul_eq_iff, hab]

theorem Chart.ext_half (h : Chart e σ π) {m n : ℕ} {u u' : Mx D m n} (hu : IsHalf e u) (hu' : IsHalf e u')
    (huu : u.map π = u'.map π) : u = u' :=
  Matrix.ext fun i j => h.ext (hu i j) (hu' i j) (congrFun (congrFun huu i) j)

theorem Chart.half_fin (h : Chart e σ π) {m n : ℕ} {u : Mx D m n} (hu : IsHalf e u) : u.map (infPart D) = 0 := by
  ext i j
  show infPart D (u i j) = 0
  rw [← hu i j, RingHom.map_mul, h.1.2.2, zero_mul]

theorem Chart.pi_eq_of_finPart (h : Chart e σ π) {a b : AE D} (hab : finPart D a = finPart D b) : π a = π b := by
  rw [← h.mul_eq_iff]
  exact adele_ext (by rw [RingHom.map_mul, RingHom.map_mul, h.1.2.2, zero_mul, zero_mul])
    (by rw [RingHom.map_mul, RingHom.map_mul, hab])

def Chart.sec (h : Chart e σ π) : LP D P →+ AE D :=
  AddMonoidHom.mk' (fun z => e * Function.surjInv h.2.1 z) fun z z' => by
    rw [← mul_add, h.mul_eq_iff, RingHom.map_add]
    simp only [Function.surjInv_eq]

theorem Chart.mul_sec (h : Chart e σ π) (z : LP D P) : e * h.sec z = h.sec z := by
  show e * (e * _) = e * _
  rw [← mul_assoc, h.1.1]

theorem Chart.pi_sec (h : Chart e σ π) (z : LP D P) : π (h.sec z) = z := by
  show π (e * _) = z
  rw [RingHom.map_mul, h.pi_idem, one_mul, Function.surjInv_eq h.2.1]

def IsGen (D : D7) (P : HeightOneSpectrum (𝓞 D.host.E)) (c : LP D P) : Prop :=
  c ≠ 0 ∧ (∃ a ∈ D.host.AA, algebraMap D.host.E (LP D P) a = c) ∧
    ∀ a ∈ D.host.AA, c⁻¹ * algebraMap D.host.E (LP D P) a ∈ intL (LP D P)

theorem exists_isGen (D : D7) (P : HeightOneSpectrum (𝓞 D.host.E)) : ∃ c, IsGen D P c := by
  obtain ⟨s, hs⟩ : (D.host.AA : Submodule (𝓞 D.host.E) D.host.E).FG :=
    FractionalIdeal.fg_of_isUnit _ (Ne.isUnit (ideal_ne_zero D))
  have hne : s.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    rintro rfl
    rw [Finset.coe_empty, Submodule.span_empty] at hs
    exact ideal_ne_zero D (FractionalIdeal.coeToSubmodule_eq_bot.1 hs.symm)
  obtain ⟨a₀, ha₀, hmax⟩ := s.exists_max_image (fun a => Valued.v (algebraMap D.host.E (LP D P) a)) hne
  have hle : ∀ a ∈ (D.host.AA : Submodule (𝓞 D.host.E) D.host.E),
      Valued.v (algebraMap D.host.E (LP D P) a) ≤ Valued.v (algebraMap D.host.E (LP D P) a₀) := by
    intro a ha
    rw [← hs] at ha
    induction ha using Submodule.span_induction with
    | mem a ha => exact hmax a ha
    | zero => simp only [map_zero, zero_le]
    | add x y _ _ hx hy => rw [RingHom.map_add]; exact Valuation.map_add_le _ hx hy
    | smul o x _ hx =>
      have ho : Valued.v (algebraMap D.host.E (LP D P) (o : D.host.E)) ≤ 1 := by
        rw [GlobalTheory.Idele.valued_algebraMap]
        exact HeightOneSpectrum.valuation_le_one P o
      rw [show o • x = (o : D.host.E) * x from rfl, RingHom.map_mul, Valuation.map_mul]
      exact (mul_le_of_le_one_left' ho).trans hx
  have h0 : algebraMap D.host.E (LP D P) a₀ ≠ 0 := by
    intro h
    apply ideal_ne_zero D
    rw [FractionalIdeal.eq_zero_iff]
    intro a ha
    have := hle a ha
    rw [h, map_zero, le_zero_iff, map_eq_zero] at this
    exact (map_eq_zero _).1 this
  refine ⟨_, h0, ⟨a₀, ?_, rfl⟩, fun a ha => ?_⟩
  · show a₀ ∈ (D.host.AA : Submodule (𝓞 D.host.E) D.host.E)
    rw [← hs]; exact Submodule.subset_span ha₀
  · rw [mem_intL, Valuation.map_mul, map_inv₀, inv_mul_le_one₀ (zero_lt_iff.2 ((map_ne_zero _).2 h0))]
    exact hle a ha

theorem mul_tmul_one_mem {w : Af D.host.F ⊗[D.host.F] D.host.E} (hw : w ∈ intAE D) {α : Af D.host.F}
    (hα : α ∈ intAf D.host.F) : w * (α ⊗ₜ[D.host.F] (1 : D.host.E)) ∈ intAE D := by
  induction hw using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨β, hβ, o', rfl⟩ := hw
    refine AddSubgroup.subset_closure ⟨β * α, GlobalTheory.LatVac.mul_mem_intAf hβ hα, o', ?_⟩
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
  | zero => rw [zero_mul]; exact zero_mem _
  | add x y _ _ hx hy => rw [add_mul]; exact add_mem hx hy
  | neg x _ hx => rw [neg_mul]; exact neg_mem hx

theorem Frame.gram_mul {V : HSp D} {β : GL (Fin V.rank) (LP D P)} (h : Frame V e σ π β) :
    V.gram.map (algebraMap D.host.E (LP D P)) * β.1 = cT σ (β⁻¹).1 := by
  have h1 : cT σ (β⁻¹).1 * cT σ β.1 = 1 := by rw [← cT_mul, Units.mul_inv, cT_one]
  rw [← Matrix.one_mul (_ * _), ← h1, Matrix.mul_assoc, ← Matrix.mul_assoc (cT σ β.1), h.1, Matrix.mul_one]

theorem Frame.mul_gram {V : HSp D} {β : GL (Fin V.rank) (LP D P)} (h : Frame V e σ π β) :
    cT σ β.1 * V.gram.map (algebraMap D.host.E (LP D P)) = (β⁻¹).1 := by
  rw [← Matrix.one_mul (β⁻¹).1, ← h.1, Matrix.mul_assoc _ β.1, Units.mul_inv, Matrix.mul_one]

theorem Frame.gram_inv {V : HSp D} {β : GL (Fin V.rank) (LP D P)} (h : Frame V e σ π β) :
    (V.gram⁻¹).map (algebraMap D.host.E (LP D P)) = β.1 * cT σ β.1 := by
  refine Matrix.left_inv_eq_left_inv (A := V.gram.map (algebraMap D.host.E (LP D P))) ?_ ?_
  · rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ (GlobalTheory.LatVac.gram_det_isUnit V),
      Matrix.map_one _ (map_zero _) (map_one _)]
  · rw [Matrix.mul_assoc, h.mul_gram, Units.mul_inv]

variable {S T : HSp D} {βS : GL (Fin S.rank) (LP D P)} {βT : GL (Fin T.rank) (LP D P)} {c : LP D P}

theorem Chart.pi_rk (h : Chart e σ π) (S T : HSp D) (a : D.host.E) (s : Fin S.rank → AE D)
    (t : Fin T.rank → AE D) (i : Fin T.rank) (j : Fin S.rank) :
    π (rk S T a (fun k => finPart D (e * s k)) (fun k => finPart D (e * t k)) i j) =
      algebraMap D.host.E (LP D P) a * π (t i) * ∑ k, σ (π (s k)) * algebraMap D.host.E (LP D P) (S.gram k j) := by
  have h1 : π (rk S T a (fun k => finPart D (e * s k)) (fun k => finPart D (e * t k)) i j) =
      π (incA D a * (e * t i) * ∑ k, cA D (e * s k) * incA D (S.gram k j)) := by
    refine h.pi_eq_of_finPart ?_
    rw [rk, Matrix.of_apply, finPart_liftFin]
    simp only [← finPart_cA]
    rw [RingHom.map_mul (finPart D) (_ * _), RingHom.map_mul (finPart D) (incA D a), map_sum (finPart D)]
    simp only [finPart_mul_incA]
    rfl
  rw [h1]
  simp only [RingHom.map_mul, map_sum π, h.1.2.1, h.pi_idem, one_mul, h.2.2.2.1, h.2.2.2.2.1]

theorem mem_latO_iff (h : Chart e σ π) (hσ : ∀ x, Valued.v (σ x) = Valued.v x) (hS : Frame S e σ π βS) (hT : Frame T e σ π βT)
    (hc : IsGen D P c) {u : WO S T} (hu : IsHalf e u) :
    u ∈ latO S T (L0c D S) (L0c D T) (fun _ => True) ↔
      ∀ i j, (c⁻¹ • ((βT⁻¹).1 * u.map π * βS.1)) i j ∈ intL (LP D P) := by
  obtain ⟨h0, ⟨a₀, ha₀, rfl⟩, hgen⟩ := hc
  refine ⟨fun hl => ?_, fun hl => ?_⟩
  · clear hu
    induction hl using AddSubgroup.closure_induction with
    | mem w hw =>
      obtain ⟨α, hα, -, a, ha, s, hs, t, ht, rfl⟩ := hw
      intro i j
      have h1 := (hT.2 fun k => incA D (t k)).1 (by
        simp only [finPart_mul_incA]; exact mul_lat_mem T h.idem_int ht) i
      have h2 := (hS.2 fun k => incA D (s k)).1 (by
        simp only [finPart_mul_incA]; exact mul_lat_mem S h.idem_int hs) j
      have h2' := mem_intL.2 ((hσ _).trans_le h2)
      have h4 : π (pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 : D.host.E)) ∈ intL _ :=
        (h.2.2.2.2.2 _).1 (by rw [RingHom.map_mul]; exact mul_tmul_one_mem h.idem_int hα)
      have h5 := mul_mem (mul_mem (mul_mem h4 (hgen a ha)) h1) h2'
      have hm : ∀ m : D.host.E, π (pairA D.host.F 0 α ⊗ₜ[D.host.F] m) =
          π (pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 : D.host.E)) * algebraMap D.host.E (LP D P) m := by
        intro m
        rw [← h.2.2.2.1, ← RingHom.map_mul]
        congr 1
        change _ = (pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 : D.host.E)) * ((1 : AF D.host.F) ⊗ₜ[D.host.F] m)
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      have hs' : ∀ k, algebraMap D.host.E (LP D P) (star (s k)) = σ (algebraMap D.host.E (LP D P) (s k)) := fun k => by
        rw [← h.2.2.2.1, ← h.2.2.2.1, ← h.2.2.2.2.1, GlobalTheory.DualPairCheck.cA_incA]
      have e1 : Matrix.map (Matrix.of fun i j => pairA D.host.F 0 α ⊗ₜ[D.host.F] (a * t i * ∑ k, star (s k) * S.gram k j) :
          WO S T) π = (π (pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 : D.host.E)) * algebraMap D.host.E (LP D P) a) •
            vecMulVec (fun k => π (incA D (t k))) ((fun k => σ (π (incA D (s k)))) ᵥ*
              S.gram.map (algebraMap D.host.E (LP D P))) := by
        ext i j : 2
        rw [Matrix.map_apply, Matrix.of_apply, hm]
        simp only [Matrix.smul_apply, smul_eq_mul, vecMulVec_apply, Matrix.vecMul, dotProduct, Matrix.map_apply,
          RingHom.map_mul, map_sum, hs', h.2.2.2.1]
        ring
      rw [e1, Matrix.mul_smul, Matrix.smul_mul, mul_vecMulVec, vecMulVec_mul, vecMul_vecMul, hS.gram_mul]
      convert h5 using 1
      have e2 : ((fun k => σ (π (incA D (s k)))) ᵥ* cT σ (βS⁻¹).1) j = σ (((βS⁻¹).1 *ᵥ fun k => π (incA D (s k))) j) := by
        rw [Matrix.mulVec, dotProduct, map_sum, Matrix.vecMul, dotProduct]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [σ.map_mul, mul_comm]
        rfl
      rw [Matrix.smul_apply, Matrix.smul_apply, vecMulVec_apply, e2, smul_eq_mul, smul_eq_mul]
      ring
    | zero =>
      rw [Matrix.map_zero _ π.map_zero, Matrix.mul_zero, Matrix.zero_mul, smul_zero]
      exact fun i j => zero_mem _
    | add x y _ _ hx hy =>
      rw [Matrix.map_add _ π.map_add, Matrix.mul_add, Matrix.add_mul, smul_add]
      exact fun i j => add_mem (hx i j) (hy i j)
    | neg x _ hx =>
      rw [Matrix.map_neg _ π.map_neg, Matrix.mul_neg, Matrix.neg_mul, smul_neg]
      exact fun i j => neg_mem (hx i j)
  · set Y : Matrix (Fin T.rank) (Fin S.rank) (LP D P) := (algebraMap D.host.E (LP D P) a₀)⁻¹ • (Matrix.map u π * βS.1) with hY
    have hs : ∀ j, (fun k => finPart D (e * h.sec (βS.1 k j))) ∈ LamHat S := by
      intro j
      refine (hS.2 fun k => h.sec (βS.1 k j)).2 fun l => ?_
      simp only [h.pi_sec]
      have : ((βS⁻¹).1 *ᵥ fun k => βS.1 k j) l = ((βS⁻¹).1 * βS.1) l j := rfl
      rw [this, Units.inv_mul, Matrix.one_apply]
      split_ifs
      exacts [one_mem _, zero_mem _]
    have ht : ∀ j, (fun k => finPart D (e * h.sec (Y k j))) ∈ LamHat T := by
      intro j
      refine (hT.2 fun k => h.sec (Y k j)).2 fun i => ?_
      simp only [h.pi_sec]
      have : ((βT⁻¹).1 *ᵥ fun k => Y k j) i = ((βT⁻¹).1 * Y) i j := rfl
      rw [this, hY, Matrix.mul_smul, ← Matrix.mul_assoc]
      exact hl i j
    have hU := smul_mem_latO D S T _ _ _ e h.idem_int _
      (sum_mem fun j (_ : j ∈ Finset.univ) => rk_mem S T ha₀ (hs j) (ht j))
    convert hU using 1
    ext i l
    rw [Matrix.smul_apply, smul_eq_mul, ← hu i l, h.mul_eq_iff, Matrix.sum_apply, map_sum]
    have hsum : ∀ j, π (rk S T a₀ (fun k => finPart D (e * h.sec (βS.1 k j)))
        (fun k => finPart D (e * h.sec (Y k j))) i l) = algebraMap D.host.E (LP D P) a₀ * (Y i j * (βS⁻¹).1 j l) := by
      intro j
      rw [h.pi_rk S T a₀ (fun k => h.sec (βS.1 k j)) (fun k => h.sec (Y k j)) i l, mul_assoc, ← hS.mul_gram]
      simp only [h.pi_sec]
      rfl
    simp only [hsum]
    rw [← Finset.mul_sum, ← Matrix.mul_apply, hY, Matrix.smul_mul, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one,
      Matrix.smul_apply, smul_eq_mul, mul_inv_cancel_left₀ h0, Matrix.map_apply]

def kap (h : Chart e σ π) (βS : GL (Fin S.rank) (LP D P)) (βT : GL (Fin T.rank) (LP D P)) (c : LP D P)
    (x : Matrix (Fin T.rank) (Fin S.rank) (LP D P)) : WO S T :=
  (c • (βT.1 * x * (βS⁻¹).1)).map h.sec

theorem kap_half (h : Chart e σ π) (x : Matrix (Fin T.rank) (Fin S.rank) (LP D P)) : IsHalf e (kap h βS βT c x) :=
  fun _ _ => h.mul_sec _

theorem kap_pi (h : Chart e σ π) (x : Matrix (Fin T.rank) (Fin S.rank) (LP D P)) :
    (kap h βS βT c x).map π = c • (βT.1 * x * (βS⁻¹).1) :=
  Matrix.ext fun _ _ => h.pi_sec _

theorem kap_add (h : Chart e σ π) (x y : Matrix (Fin T.rank) (Fin S.rank) (LP D P)) :
    kap h βS βT c (x + y) = kap h βS βT c x + kap h βS βT c y := by
  rw [kap, Matrix.mul_add, Matrix.add_mul, smul_add, Matrix.map_add _ h.sec.map_add]
  rfl

theorem kap_zero (h : Chart e σ π) : kap h βS βT c 0 = 0 := by
  rw [kap, Matrix.mul_zero, Matrix.zero_mul, smul_zero, Matrix.map_zero _ h.sec.map_zero]

theorem kap_surj (h : Chart e σ π) (hc : c ≠ 0) {u : WO S T} (hu : IsHalf e u) : ∃ x, kap h βS βT c x = u := by
  refine ⟨c⁻¹ • ((βT⁻¹).1 * u.map π * βS.1), h.ext_half (kap_half h _) hu ?_⟩
  rw [kap_pi, Matrix.mul_smul, Matrix.smul_mul, smul_inv_smul₀ hc, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.mul_inv,
    Matrix.one_mul, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]

theorem kap_mem_iff (h : Chart e σ π) (hσ : ∀ x, Valued.v (σ x) = Valued.v x) (hS : Frame S e σ π βS) (hT : Frame T e σ π βT)
    (hc : IsGen D P c) (x : Matrix (Fin T.rank) (Fin S.rank) (LP D P)) :
    kap h βS βT c x ∈ latO S T (L0c D S) (L0c D T) (fun _ => True) ↔ ∀ i j, x i j ∈ intL (LP D P) := by
  rw [mem_latO_iff h hσ hS hT hc (kap_half h x), kap_pi, Matrix.mul_smul, Matrix.smul_mul, inv_smul_smul₀ hc.1,
    ← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]

theorem actO_kap (h : Chart e σ π) {ιS ιT} (hS : GrpChart S e σ π βS ιS) (hT : GrpChart T e σ π βT ιT) (g k)
    (x : Matrix (Fin T.rank) (Fin S.rank) (LP D P)) :
    actO S T (ιS g) (ιT k) (kap h βS βT c x) = kap h βS βT c (k.1.1 * x * (g.1⁻¹).1) := by
  refine h.ext_half ?_ (kap_half h _) ?_
  · rw [isHalf_iff, ← GlobalTheory.FinWeilO.actO_smul, (isHalf_iff _ _).1 (kap_half h x)]
  · rw [actO, Matrix.map_mul, Matrix.map_mul, ← map_inv, hS.2.1, hT.2.1, kap_pi, kap_pi]
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc, Units.inv_mul_cancel_left,
      ← Matrix.mul_assoc (βT⁻¹).1 βT.1, Units.inv_mul, Matrix.one_mul]
    rfl

def th (ψ : AddChar (AF D.host.F) ℂ) (h : Chart e σ π) (c : LP D P) : AddChar (LP D P) ℂ :=
  ψ.compAddMonoidHom ((Algebra.trace (AF D.host.F) (AE D)).toAddMonoidHom.comp
    ((AddMonoidHom.mulLeft (incA D D.host.xi0)).comp (h.sec.comp (AddMonoidHom.mulLeft (c * σ c)))))

variable {ψ : AddChar (AF D.host.F) ℂ}

theorem th_apply (h : Chart e σ π) (z : LP D P) :
    th ψ h c z = ψ (Algebra.trace (AF D.host.F) (AE D) (incA D D.host.xi0 * h.sec (c * σ c * z))) := rfl

theorem th_conj (h : Chart e σ π) (hσ : ∀ x, σ (σ x) = x) (z : LP D P) : th ψ h c (σ z) * th ψ h c z = 1 := by
  have h1 : h.sec (c * σ c * σ z) = cA D (h.sec (c * σ c * z)) := by
    refine h.ext (h.mul_sec _) ?_ ?_
    · conv_rhs => rw [← h.mul_sec, RingHom.map_mul, h.1.2.1]
    · rw [h.2.2.2.2.1, h.pi_sec, h.pi_sec, RingHom.map_mul, RingHom.map_mul, hσ, mul_comm c]
  rw [th_apply, th_apply, h1, ← GlobalTheory.DualPairCheck.trace_cA (_ * cA D _), RingHom.map_mul, GlobalTheory.DualPairCheck.cA_cA,
    GlobalTheory.DualPairCheck.cA_incA, GlobalTheory.DualPairCheck.star_purely_imaginary_eq_neg, RingHom.map_neg, neg_mul, LinearMap.map_neg,
    ← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]

theorem Chart.pi_hO (h : Chart e σ π) (u u' : WO S T) :
    π (hO S T u u') = Matrix.trace ((S.gram⁻¹).map (algebraMap D.host.E (LP D P)) * cT σ (u'.map π) *
      T.gram.map (algebraMap D.host.E (LP D P)) * u.map π) := by
  simp only [hO, map_sum π, RingHom.map_mul, h.2.2.2.1, h.2.2.2.2.1, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine Eq.trans (Finset.sum_congr rfl fun c _ => Finset.sum_comm) ?_
  rw [Finset.sum_comm]
  rfl

theorem symplO_kap (h : Chart e σ π) (hS : Frame S e σ π βS) (hT : Frame T e σ π βT)
    (x y : Matrix (Fin T.rank) (Fin S.rank) (LP D P)) :
    ψ (symplO S T (kap h βS βT c x) (kap h βS βT c y)) = th ψ h c (Matrix.trace (cT σ y * x)) := by
  rw [th_apply, symplO]
  congr 3
  refine h.ext ?_ (h.mul_sec _) ?_
  · rw [← hO_smul_left, (isHalf_iff _ _).1 (kap_half h x)]
  · have h1 : cT σ (c • (βT.1 * y * (βS⁻¹).1)) = σ c • (cT σ (βS⁻¹).1 * (cT σ y * cT σ βT.1)) := by
      rw [← cT_mul, ← cT_mul]
      exact Matrix.ext fun i j => σ.map_mul _ _
    have h2 : cT σ βS.1 * cT σ (βS⁻¹).1 = 1 := by rw [← cT_mul, Units.inv_mul, cT_one]
    rw [h.pi_hO, h.pi_sec, kap_pi, kap_pi, hS.gram_inv, h1]
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (cT σ βS.1), h2, Matrix.one_mul, ← Matrix.mul_assoc (cT σ βT.1), hT.mul_gram,
      ← Matrix.mul_assoc (βT⁻¹).1, Units.inv_mul, Matrix.one_mul, Matrix.trace_mul_comm, Matrix.mul_assoc, Matrix.mul_assoc,
      Units.inv_mul, Matrix.mul_one, mul_assoc]

theorem half_add_half {m n : ℕ} (x : Matrix (Fin m) (Fin n) (LP D P)) : (2⁻¹ : LP D P) • x + (2⁻¹ : LP D P) • x = x := by
  have : CharZero (LP D P) := algebraRat.charZero _
  rw [← add_smul, ← two_mul, mul_inv_cancel₀ two_ne_zero, one_smul]

theorem symplOH_kap (h : Chart e σ π) (hS : Frame S e σ π βS) (hT : Frame T e σ π βT)
    (x y : Matrix (Fin T.rank) (Fin S.rank) (LP D P)) :
    ψ (symplOH S T (kap h βS βT c x) (kap h βS βT c y)) = th ψ h c (2⁻¹ * Matrix.trace (cT σ y * x)) := by
  conv_lhs => rw [← half_add_half x, kap_add, symplOH_add_left, symplOH_add_self, symplO_kap h hS hT, Matrix.mul_smul,
    Matrix.trace_smul, smul_eq_mul]

theorem latO_dual (hψ : IsStdChar D ψ (-1)) (S T : HSp D) (u : WO S T) (hu : u.map (infPart D) = 0) :
    u ∈ latO S T (L0c D S) (L0c D T) (fun _ => True) ↔
      ∀ u' ∈ latO S T (L0c D S) (L0c D T) (fun _ => True), ψ (symplO S T u u') = 1 := by
  have := (GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ S T _ _ hψ (GlobalTheory.PlaceModel.isSelfDualC_latFrame S)
    (GlobalTheory.PlaceModel.isSelfDualC_latFrame T)).1 u hu
  rwa [GlobalTheory.PlaceModel.coe_latFrame, GlobalTheory.PlaceModel.coe_latFrame] at this

theorem th_cond (hψ : IsStdChar D ψ (-1)) (h : Chart e σ π) (hσ : ∀ x, Valued.v (σ x) = Valued.v x) (hS : Frame S e σ π βS)
    (i : Fin S.rank) (hc : IsGen D P c) (z : LP D P) : (∀ u ∈ intL (LP D P), th ψ h c (z * u) = 1) ↔ z ∈ intL (LP D P) := by
  have key : ∀ (z : LP D P) (y : Matrix (Fin S.rank) (Fin S.rank) (LP D P)),
      ψ (symplO S S (kap h βS βS c (Matrix.single i i z)) (kap h βS βS c y)) = th ψ h c (z * σ (y i i)) := fun z y => by
    rw [symplO_kap h hS hS, Matrix.trace_mul_single, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, mul_comm]
    rfl
  have hs : ∀ z : LP D P, kap h βS βS c (Matrix.single i i z) ∈ latO S S (L0c D S) (L0c D S) (fun _ => True) ↔
      z ∈ intL (LP D P) := fun z => by
    rw [kap_mem_iff h hσ hS hS hc]
    refine ⟨fun h1 => by simpa only [Matrix.single_apply_same] using h1 i i, fun h1 a b => ?_⟩
    rw [Matrix.single_apply]
    split_ifs
    exacts [h1, zero_mem _]
  constructor
  · intro hz
    rw [← hs, latO_dual hψ _ _ _ (h.half_fin (kap_half h _))]
    intro u' hu'
    have h1 : IsHalf e (e • u') := by rw [isHalf_iff, smul_smul, h.1.1]
    obtain ⟨y, hy⟩ := kap_surj (βS := βS) (βT := βS) h hc.1 h1
    have h2 := (kap_mem_iff h hσ hS hS hc y).1 (hy ▸ smul_mem_latO D S S _ _ _ e h.idem_int _ hu')
    rw [← (isHalf_iff _ _).1 (kap_half h (Matrix.single i i z)), symplO_smul, h.1.2.1, ← hy, key]
    exact hz _ (mem_intL.2 ((hσ _).trans_le (h2 i i)))
  · intro hz u hu
    have h1 := (latO_dual hψ _ _ _ (h.half_fin (kap_half h _))).1 ((hs _).2 (mul_mem hz hu)) _ ((hs 1).2 (one_mem _))
    rwa [key, Matrix.single_apply_same, σ.map_one, mul_one] at h1

open GlobalTheory.FinWeilO GlobalTheory.FinWeil in

theorem span_vacua (hψ : IsStdChar D ψ (-1)) (he : e * e = e) (hce : cA D e = e)
    (h2 : ∀ u ∈ latO S T (L0c D S) (L0c D T) (fun _ => True), IsHalf e u →
      ∃ u' ∈ latO S T (L0c D S) (L0c D T) (fun _ => True), u' + u' = u) (N : Submodule ℂ (thetaSub ψ S T))
    (hN : ∀ x, IsHalf e x → ∀ s m : thetaSub ψ S T,
      (∀ u ∈ latO S T (L0c D S) (L0c D T) (fun _ => True), IsHalf e u → heisO ψ S T u s = s) →
        (m : WO S T → ℂ) = heisO ψ S T x s → m ∈ N) : N = ⊤ := by
  have hS := GlobalTheory.PlaceModel.isSelfDualC_latFrame S
  have hT := GlobalTheory.PlaceModel.isSelfDualC_latFrame T
  obtain ⟨w, hw⟩ := exists_w D
  have hA := selfDual_latF (GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ S T _ _ hψ hS hT).1
  have hspan := GlobalTheory.T.span_heisenberg_translates_of_lattice_vacua_eq_top (isHeis_opF hψ.1 S T hw) _ hA
    (smooth_theta hψ.1 hS hT hw hA (GlobalTheory.T.completedHomLattice_multiple_mem_open_level D S T _ _ hS hT (GlobalTheory.T.completedHomLattice_finitelyGenerated D S T _ _ hS hT)).1)
  rw [GlobalTheory.PlaceModel.coe_latFrame, GlobalTheory.PlaceModel.coe_latFrame] at hspan
  rw [eq_top_iff, ← hspan, Submodule.span_le]
  rintro _ ⟨x, s, hs, rfl⟩
  have hfix : ∀ u ∈ latO S T (L0c D S) (L0c D T) (fun _ => True), IsHalf e u → heisO ψ S T u s = s := by
    intro u hu hh
    have h3 := congrArg Subtype.val (hs (XF.mk u (latO_fin hu)) hu)
    obtain ⟨u', hu', rfl⟩ := h2 u hu hh
    have h4 := smul_mem_latO D S T _ _ _ _ (finPart_intA w) _ hu'
    rw [coe_opF, phase, XF.coe_mk, smul_add, symplOH_add_left, symplOH_add_self, AddChar.map_neg_eq_inv,
      (latO_dual hψ S T _ (latO_fin h4)).1 h4 _ hu, inv_one, one_smul] at h3
    exact h3
  have h0 : cA D e * (1 - e) = 0 := by rw [hce, mul_sub, mul_one, he, sub_self]
  have hx1 : IsHalf e (e • (x : WO S T)) := by rw [isHalf_iff, smul_smul, he]
  have hx2 : IsHalf (1 - e) ((1 - e) • (x : WO S T)) := by
    rw [isHalf_iff, smul_smul, sub_mul, one_mul, mul_sub, mul_one, he, sub_self, sub_zero]
  have hf1 : (e • (x : WO S T)).map (infPart D) = 0 := (finSub S T).smul_mem e x.fin
  have hf2 : ((1 - e) • (x : WO S T)).map (infPart D) = 0 := (finSub S T).smul_mem (1 - e) x.fin
  let s' : thetaSub ψ S T := ⟨_, GlobalTheory.FinTranslate.isTheta_heisO_fin hψ.1 hf2 s.2⟩
  let m : thetaSub ψ S T := ⟨_, GlobalTheory.FinTranslate.isTheta_heisO_fin hψ.1 hf1 s'.2⟩
  have hm : m ∈ N := hN _ hx1 s' m (fun u hu hh => by
    show heisO ψ S T u (heisO ψ S T _ s) = heisO ψ S T _ s
    rw [heisO_comm, symplO_eq_zero S T h0 hh hx2, AddChar.map_zero_eq_one, one_smul, hfix u hu hh]) rfl
  have h5 : opF hψ.1 S T w x s = phase ψ w x • m := Subtype.ext (by
    rw [coe_opF, Submodule.coe_smul]
    congr 1
    show _ = heisO ψ S T _ (heisO ψ S T _ s)
    rw [← heisO_add_of_orth ψ S T (symplO_eq_zero S T h0 hx1 hx2), ← add_smul, add_sub_cancel, one_smul])
  rw [SetLike.mem_coe, h5]
  exact N.smul_mem _ hm

end GlobalTheory.InertLoc
