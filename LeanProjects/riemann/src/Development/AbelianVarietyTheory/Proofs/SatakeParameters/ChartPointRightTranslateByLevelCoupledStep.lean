import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.UnderTie
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SmulCompSmul
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatAdXMulLev
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AbsNormEqOfSplitFactor
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.XiAtCongInvariant
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntegralDivUniformizerOfRedZero
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV
open GlobalTheory.TopStep Formalism.L2.Forms Formalism.UG

noncomputable section
namespace GlobalTheory.CplPt
open Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

section CongBasic

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {N : ℕ} {P : HeightOneSpectrum (𝓞 E)}

theorem intAtA_add {a b : E ⊗[F] FiniteAdeleRing (𝓞 F) F} (ha : IntAtA (F := F) P a) (hb : IntAtA (F := F) P b) :
    IntAtA (F := F) P (a + b) := by
  obtain ⟨s, hs, h1⟩ := ha
  obtain ⟨r, hr, h2⟩ := hb
  have hi : ∀ x : 𝓞 E, iA F E (algebraMap (𝓞 E) E x) ∈ Formalism.L2.Herm.intAf F E := fun x => (toRInt F E x).2
  refine ⟨s * r, fun h => (P.isPrime.mem_or_mem h).elim hs hr, ?_⟩
  have e : iA F E (algebraMap (𝓞 E) E (s * r)) * (a + b) =
      iA F E (algebraMap (𝓞 E) E r) * (iA F E (algebraMap (𝓞 E) E s) * a) +
        iA F E (algebraMap (𝓞 E) E s) * (iA F E (algebraMap (𝓞 E) E r) * b) := by
    rw [map_mul, map_mul]; ring
  rw [e]
  exact add_mem (mul_mem (hi r) h1) (mul_mem (hi s) h2)

theorem intAtA_mul {a b : E ⊗[F] FiniteAdeleRing (𝓞 F) F} (ha : IntAtA (F := F) P a) (hb : IntAtA (F := F) P b) :
    IntAtA (F := F) P (a * b) := by
  obtain ⟨s, hs, h1⟩ := ha
  obtain ⟨r, hr, h2⟩ := hb
  refine ⟨s * r, fun h => (P.isPrime.mem_or_mem h).elim hs hr, ?_⟩
  have e : iA F E (algebraMap (𝓞 E) E (s * r)) * (a * b) =
      (iA F E (algebraMap (𝓞 E) E s) * a) * (iA F E (algebraMap (𝓞 E) E r) * b) := by
    rw [map_mul, map_mul]; ring
  rw [e]
  exact mul_mem h1 h2

theorem intAtA_int (x : 𝓞 E) : IntAtA (F := F) P (iA F E (algebraMap (𝓞 E) E x)) :=
  ⟨1, fun h => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h), by
    rw [map_one, map_one, one_mul]; exact (toRInt F E x).2⟩

theorem intAtA_sum {ι : Type} (s : Finset ι) (f : ι → E ⊗[F] FiniteAdeleRing (𝓞 F) F) (h : ∀ i ∈ s, IntAtA (F := F) P (f i)) :
    IntAtA (F := F) P (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using intAtA_int (F := F) (P := P) 0
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact intAtA_add (h a (Finset.mem_insert_self _ _)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem congAt_mul (n : ℕ) {k k' : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)} (h : CongAt P n k) (h' : CongAt P n k') :
    CongAt P n (k * k') := by
  intro a b
  have hq : ((qOf P : ℕ) : E) ≠ 0 := by
    have : qOf P ≠ 0 := fun h0 => P.ne_bot (Ideal.absNorm_eq_zero_iff.1 h0)
    exact_mod_cast this
  set c := iA F E (((qOf P : ℕ) : E) ^ n)⁻¹ with hc
  set d := iA F E (algebraMap (𝓞 E) E (((qOf P : ℕ) : 𝓞 E) ^ n)) with hd
  have hcd : d * c = 1 := by
    rw [hc, hd, ← map_mul, map_pow, map_natCast, mul_inv_cancel₀ (pow_ne_zero _ hq), map_one]
  have e : ((k * k' : GL (Fin N) _) : Matrix (Fin N) (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) - 1 =
      ((k : Matrix (Fin N) (Fin N) _) - 1) * ((k' : Matrix (Fin N) (Fin N) _) - 1) + (((k : Matrix (Fin N) (Fin N) _) - 1) + ((k' : Matrix (Fin N) (Fin N) _) - 1)) := by
    rw [Units.val_mul]; noncomm_ring
  rw [e, Matrix.add_apply, Matrix.add_apply, mul_add, mul_add, Matrix.mul_apply, Finset.mul_sum]
  refine intAtA_add (intAtA_sum _ _ fun l _ => ?_) (intAtA_add (h a b) (h' a b))
  have e2 : ∀ x y : E ⊗[F] FiniteAdeleRing (𝓞 F) F, c * (x * y) = d * ((c * x) * (c * y)) := by
    intro x y
    linear_combination (-(c * (x * y))) * hcd
  rw [e2]
  exact intAtA_mul (intAtA_int _) (intAtA_mul (h a l) (h' l b))

theorem nearAt_mul (n : ℕ) {x : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)} {g k : GL (Fin N) E} (h : NearAt P n x g)
    (hk : CongAt P n (ratA F k)) : NearAt P n x (g * k) := by
  unfold NearAt
  rw [map_mul, ← mul_assoc]
  exact congAt_mul n h hk

end CongBasic

section Conj

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {N : ℕ} {P : HeightOneSpectrum (𝓞 E)}

theorem intAtA_of_intAt {e : E} (h : IntAt P e) : IntAtA (F := F) P (iA F E e) := by
  obtain ⟨r, s, hs, hr⟩ := h
  refine ⟨s, hs, ?_⟩
  rw [← map_mul, hr]
  exact (toRInt F E r).2

theorem ratA_apply (h : GL (Fin N) E) (a b : Fin N) :
    ((ratA F h : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin N) (Fin N) _) a b = iA F E ((h : Matrix (Fin N) (Fin N) E) a b) := rfl

theorem congAt_conj (n : ℕ) {C : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)} {h : GL (Fin N) E} (hC : CongAt P n C)
    (hh : ∀ a b, IntAt P ((h : Matrix (Fin N) (Fin N) E) a b) ∧ IntAt P (((h⁻¹ : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) a b)) :
    CongAt P n ((ratA F h)⁻¹ * C * ratA F h) := by
  intro a b
  set A' : Matrix (Fin N) (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F) := ((ratA F h⁻¹ : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin N) (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))
  set A : Matrix (Fin N) (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F) := ((ratA F h : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin N) (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))
  have hAA : A' * A = 1 := by
    simp only [A', A, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]
  have e : (((ratA F h)⁻¹ * C * ratA F h : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin N) (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) - 1 =
      A' * ((C : Matrix (Fin N) (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) - 1) * A := by
    rw [← map_inv, Units.val_mul, Units.val_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hAA]
  rw [e, Matrix.mul_apply, Finset.mul_sum]
  refine intAtA_sum _ _ fun m _ => ?_
  rw [Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
  refine intAtA_sum _ _ fun l _ => ?_
  have e2 : iA F E (((qOf P : ℕ) : E) ^ n)⁻¹ * (A' a l * ((C : Matrix (Fin N) (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) - 1) l m * A m b) =
      A' a l * (iA F E (((qOf P : ℕ) : E) ^ n)⁻¹ * ((C : Matrix (Fin N) (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) - 1) l m) * A m b := by ring
  rw [e2]
  refine intAtA_mul (intAtA_mul ?_ (hC l m)) ?_
  · exact intAtA_of_intAt (hh a l).2
  · exact intAtA_of_intAt (hh m b).1

theorem nearAt_mul_int (n : ℕ) {x y : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)} {g h : GL (Fin N) E}
    (hx : NearAt P n x g) (hy : NearAt P n y h)
    (hh : ∀ a b, IntAt P ((h : Matrix (Fin N) (Fin N) E) a b) ∧ IntAt P (((h⁻¹ : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) a b)) :
    NearAt P n (x * y) (g * h) := by
  unfold NearAt at *
  have e : (x * y)⁻¹ * ratA F (g * h) = (y⁻¹ * ratA F h) * ((ratA F h)⁻¹ * (x⁻¹ * ratA F g) * ratA F h) := by
    rw [map_mul]; group
  rw [e]
  exact congAt_mul n hy (congAt_conj n hx hh)

end Conj

theorem intAt_map {D : D7} {X : Fields} (s : Seam D X) {P : HeightOneSpectrum (𝓞 X.E)} {a : X.E} (h : IntAt P a) :
    IntAt (seamP s P) (s.iE a) := by
  obtain ⟨r, c, hc, e⟩ := h
  refine ⟨RingOfIntegers.mapRingEquiv s.iE r, RingOfIntegers.mapRingEquiv s.iE c, (mem_seamP s P c).not.2 hc, ?_⟩
  have := congrArg s.iE e
  simpa using this

theorem seamGL_int {D : D7} {X : Fields} (s : Seam D X) {n : ℕ} {P : HeightOneSpectrum (𝓞 X.E)} (k : GLint X.E n P) (a b : Fin n) :
    IntAt (seamP s P) (((seamGL s k.1 : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E) a b) ∧
      IntAt (seamP s P) ((((seamGL s k.1)⁻¹ : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E) a b) := by
  have e1 : ∀ g : Sp X.E n ≃ₗ[X.E] Sp X.E n, ((seamGL s g : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E) a b =
      s.iE (g (Pi.single b 1) a) := fun g => by
    show ((LinearMap.toMatrix' g.toLinearMap).map (s.iE : X.E →+* D.host.E)) a b = _
    rw [Matrix.map_apply, LinearMap.toMatrix'_apply]
    rfl
  refine ⟨?_, ?_⟩
  · rw [e1]
    exact intAt_map s (glint_entry k a b)
  · rw [← map_inv, e1]
    exact intAt_map s (glint_entry k⁻¹ a b)

theorem congAt_one_of_redGL {D : D7} {X : Fields} (s : Seam D X) {n : ℕ} {P : HeightOneSpectrum (𝓞 X.E)}
    (hq : ((qOf P : ℕ) : 𝓞 X.E) ∉ P.asIdeal ^ 2) (k : GLint X.E n P) (hk : redGL n P k = 1) :
    CongAt (F := D.host.F) (seamP s P) 1 (ratA D.host.F (seamGL s k.1)) := by
  classical
  intro a b
  have hm : redMat k = 1 := by rw [← redGL_val, hk, Units.val_one]
  have hab : redP P (k.1 (Pi.single b 1) a) = (1 : Matrix (Fin n) (Fin n) (𝓞 X.E ⧸ P.asIdeal)) a b := congrFun (congrFun hm a) b
  have hδ : IntAt P (if a = b then (1 : X.E) else 0) := by
    split_ifs
    · simpa using IntAt.coe P 1
    · simpa using IntAt.coe P 0
  have hent : IntAt P (k.1 (Pi.single b 1) a - (if a = b then (1 : X.E) else 0)) := by
    rw [sub_eq_add_neg]
    exact (glint_entry k a b).add (intAt_neg hδ)
  have hred : redP P (k.1 (Pi.single b 1) a - (if a = b then (1 : X.E) else 0)) = 0 := by
    rw [reduction_sub (glint_entry k a b) hδ, hab, Matrix.one_apply]
    split_ifs
    · simpa using (sub_eq_zero.2 (reduction_coe P 1).symm)
    · simpa using (reduction_coe P 0)
  have h1 := intAt_div_of_redP hq hent hred
  have h2 : IntAt P ((((qOf P : ℕ) : X.E) ^ 1)⁻¹ * (k.1 (Pi.single b 1) a - (if a = b then (1 : X.E) else 0))) := by
    rwa [pow_one, ← div_eq_inv_mul]
  convert intAtA_of_intAt (F := D.host.F) (intAt_map s h2) using 1
  rw [MidIndep.qOf_seamP, map_mul s.iE, map_mul (iA D.host.F D.host.E), map_inv₀ s.iE, map_pow s.iE, map_natCast s.iE]
  congr 1
  rw [Matrix.sub_apply, Matrix.one_apply, map_sub, map_sub]
  congr 1
  split_ifs <;> simp

set_option maxHeartbeats 1000000 in

theorem funMoved_mul_lev {D : D7} {X : Fields} (s : Seam D X) {i : ℕ} {hi : i ≤ D.R.m} {T : ℕ} {bad : Set (HeightOneSpectrum (𝓞 D.host.F))}
    (lev : StepLevel D.host.F D.host.E (sigD D) (gramN D i hi) T D.R.f bad) {ST SG : Finset (HeightOneSpectrum (𝓞 X.E))} (P : ST)
    (v : HeightOneSpectrum (𝓞 D.host.F)) (h : (T : 𝓞 D.host.F) ∈ v.asIdeal) (ι : lev.fM v h →+ 𝓞 X.E ⧸ P.1.asIdeal)
    (x : GL (Fin (D.R.N i)) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (d : Deco X.E (D.R.N i) ST SG) (κ : lev.U) :
    FunMoved s lev P v h ι x d → FunMoved s lev P v h ι (x * κ.1) d := by
  unfold FunMoved
  intro H w hw z hz
  have hU := (lev.U_eq κ.1).1 κ.2
  have hk : bc (prV (E := D.host.E) v) κ.1 ∈ lev.Uloc v := hU.2 v
  rw [lev.UlocAlt v h] at hk
  have hk2 := (Subgroup.mem_inf.1 hk).2
  change ∃ _, _ at hk2
  obtain ⟨hst, hf⟩ := hk2
  have hp : pullV (F := D.host.F) (x * κ.1) (fun a => s.iE (w a)) =
      (κ.1⁻¹).val *ᵥ pullV (F := D.host.F) x (fun a => s.iE (w a)) := by
    unfold pullV
    rw [_root_.mul_inv_rev, Units.val_mul, ← Matrix.mulVec_mulVec]
  have hz1 : z.1 = (bc (prV (E := D.host.E) v) κ.1⁻¹).val *ᵥ
      (fun l => prV (E := D.host.E) v (pullV (F := D.host.F) x (fun a => s.iE (w a)) l)) := by
    rw [hz, hp]
    funext l
    exact RingHom.map_mulVec _ _ _ l
  have hz0 : (bc (prV (E := D.host.E) v) κ.1).val *ᵥ z.1 =
      fun l => prV (E := D.host.E) v (pullV (F := D.host.F) x (fun a => s.iE (w a)) l) := by
    have e : (bc (prV (E := D.host.E) v) κ.1).val * (bc (prV (E := D.host.E) v) κ.1⁻¹).val = 1 := by
      rw [← Units.val_mul (bc (prV (E := D.host.E) v) κ.1), ← map_mul, mul_inv_cancel, map_one, Units.val_one]
    refine (congrArg (fun y => (bc (prV (E := D.host.E) v) κ.1).val *ᵥ y) hz1).trans ?_
    simp only [Matrix.mulVec_mulVec, e, Matrix.one_mulVec]
  rw [H w hw ⟨_, (hst z.1).1 z.2⟩ hz0]
  exact congrArg ι (hf z)

section Pt

variable {X : Fields} {Pr : Primes X} {R : Ranks}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S} {u : Pr.Word} {j : ℕ}

theorem exists_pt_frames (p : ChPt (R := R) sel mu u j) (g : ∀ P : rowSG Pr sel mu, GLint X.E (R.N j) P.1) :
    ∃ (q : ChPt (R := R) sel mu u j) (κ : GLQ X.E (R.N j) (rowSG Pr sel mu)),
      q.deco.1.N = p.deco.1.N ∧ q.deco.1.f = p.deco.1.f ∧ (∀ P, frsF sel mu q P = frsF sel mu p P * ((κ P)⁻¹).1) ∧
      ∀ P, redGL _ P.1 ((g P)⁻¹ * (κ P)⁻¹) = 1 ∧ (P.1 ∉ Pr.vGs → (κ P)⁻¹ = g P) := by
  classical
  let h : GLG X.E (R.N j) Pr.vGs := fun w => redGL _ w.1 (g ⟨w.1, Finset.mem_union_left _ w.2⟩)⁻¹
  let k : GLQ X.E (R.N j) (QE sel (mu : Chr X.F X.E X.K)) := fun P => (g ⟨P.1, Finset.mem_union_right _ P.2⟩)⁻¹
  let q : ChPt (R := R) sel mu u j := ((1 : UF X.E (R.N j)), h, k) • p
  have hl : ∀ w : Pr.vGs, IsLiftFr (p.deco.1.act 1 h) w (q.deco.1.liftFr w) := fun w => liftFr_spec q.deco.2 w
  let t1 : ∀ w : Pr.vGs, GLint X.E (R.N j) w.1 := fun w => passFr (d := p.deco.1) 1 h (liftFr_spec p.deco.2 w) (hl w)
  let κ : GLQ X.E (R.N j) (rowSG Pr sel mu) := fun P => if hP : P.1 ∈ Pr.vGs then t1 ⟨P.1, hP⟩ else (g P)⁻¹
  refine ⟨q, κ, Submodule.map_id _, rfl, fun P => ?_, fun P => ?_⟩
  · unfold frsF
    by_cases hP : P.1 ∈ Pr.vGs
    · simp only [dif_pos hP, κ]
      show _ = p.deco.1.liftFr ⟨P.1, hP⟩ * ((q.deco.1.liftFr ⟨P.1, hP⟩)⁻¹ * 1 * p.deco.1.liftFr ⟨P.1, hP⟩)⁻¹
      group
    · simp only [dif_neg hP, κ]
      show 1 * p.fr _ * ((k _)⁻¹).1 = _
      simp [k]
  · by_cases hP : P.1 ∈ Pr.vGs
    · simp only [κ, dif_pos hP, not_not.2 hP, IsEmpty.forall_iff, and_true]
      have e : redGL _ P.1 (t1 ⟨P.1, hP⟩) = h ⟨P.1, hP⟩ := redGL_passFr (d := p.deco.1) (w := ⟨P.1, hP⟩) 1 h (liftFr_spec p.deco.2 _) (hl _)
      rw [map_mul, map_inv, map_inv, e]
      simp only [h, map_inv, inv_inv, Subtype.coe_eta, inv_mul_cancel]
    · simp only [κ, dif_neg hP, inv_inv, inv_mul_cancel, map_one]
      exact ⟨trivial, fun _ => trivial⟩

end Pt

theorem exists_glint_inFrame : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ (hj : t.m2 + 1 ≤ D.R.m) (β' : (St (t.m2 + 1) hj).Ch)
    (κ' : ((St (t.m2 + 1) hj).K β').lev.U) (P : SB t μ),
    ∃ g : GLint t.X.E (D.R.N (t.m2 + 1)) P.1, InFrame t.seam (A.fb (t.m2 + 1) hj β') (t.cst μ).D P κ'.1 g.1) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a _ hTie hj β' κ' P
  obtain ⟨hLe, -, -⟩ := hTie.levCpl β'
  have hv : IsOver (HeightOneSpectrum.under (𝓞 D.host.F) (seamP t.seam P.1)) (seamP t.seam P.1) := by
    unfold IsOver
    rw [HeightOneSpectrum.under_asIdeal]
  have hU := (((St (t.m2 + 1) hj).K β').lev.U_eq κ'.1).1 κ'.2
  obtain ⟨g, z, ⟨hmid, -⟩, hin⟩ := hLe P _ hv κ'.1 hU.1 (hU.2 _)
  have hpr := (exists_midLev_iff t.Ch t.sel (t.tup μ) (t.cst μ) (t.m2 + 1) P _ g).1 ⟨z, hmid⟩
  exact ⟨⟨g, (t.idx_ok μ).int (t.m2 + 1) _ P hpr⟩, hin⟩

theorem ptAd_levCpl : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ (hj : t.m2 + 1 ≤ D.R.m) (β' : (St (t.m2 + 1) hj).Ch)
    (x' x₁' : UA D (t.m2 + 1) hj) (κ' : ((St (t.m2 + 1) hj).K β').lev.U) p', x₁'.1 = x'.1 * κ'.1 → IsPtAd A a (t.m2 + 1) hj β' x' p' →
    ∃ (q' : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) (t.m2 + 1)) (κ'' : GLQ t.X.E (D.R.N (t.m2 + 1)) (SB t μ)),
      IsPtAd A a (t.m2 + 1) hj β' x₁' q' ∧
      (∀ (p : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) t.m2) w, phiT t.X.K p.deco.1 q'.deco.1 w = phiT t.X.K p.deco.1 p'.deco.1 w) ∧
      (∀ P, frsF t.sel (t.tup μ) q' P = frsF t.sel (t.tup μ) p' P * ((κ'' P)⁻¹).1) ∧
      ∀ P, InFrame t.seam (A.fb (t.m2 + 1) hj β') (t.cst μ).D P κ'.1 ((κ'' P)⁻¹).1) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hPin hTie hj β' x' x₁' κ' p' hx hp'
  choose g hg using exists_glint_inFrame A dtU a hPin hTie hj β' κ'
  obtain ⟨q', κ'', hN, hf, hfr, hκ⟩ := exists_pt_frames p' g
  have hin : ∀ P, InFrame t.seam (A.fb (t.m2 + 1) hj β') (t.cst μ).D P κ'.1 ((κ'' P)⁻¹).1 := by
    intro P
    by_cases hP : P.1 ∈ t.Pr.vGs
    · have hD : (t.cst μ).D P = 1 := (t.idx_ok μ).depthG P hP
      have hq := (GlobalTheory.ColPeriod.levelPrimes t.X t.Pr t.sel t.S (t.tup μ) hPin.fields.ok t.pr_ok hPin.sel P).1.2
      have e : ((κ'' P)⁻¹).1 = (g P).1 * ((g P)⁻¹ * (κ'' P)⁻¹).1 := by
        rw [← Subgroup.coe_mul, mul_inv_cancel_left]
      unfold InFrame
      rw [e, map_mul]
      refine nearAt_mul _ (hg P) ?_
      rw [hD]
      exact congAt_one_of_redGL t.seam hq ((g P)⁻¹ * (κ'' P)⁻¹) (hκ P).1
    · rw [(hκ P).2 hP]
      exact hg P
  refine ⟨q', κ'', ⟨?_, fun P => ?_, fun P v h hvP => ?_⟩, fun p w => ?_, hfr, hin⟩
  · rw [hN, hp'.lat]
    unfold latCo
    rw [hx, Formalism.MainNotions.G.KAat.latAd_stab _ _ _ (hatStab_of_lev _ κ')]
  · rw [hfr P, map_mul, hx]
    have e : ratA D.host.F (A.crd _ hj) * (x'.1 * κ'.1) * ratA D.host.F (A.fb _ hj β' P) =
        (ratA D.host.F (A.crd _ hj) * x'.1 * ratA D.host.F (A.fb _ hj β' P)) *
          ((ratA D.host.F (A.fb _ hj β' P))⁻¹ * κ'.1 * ratA D.host.F (A.fb _ hj β' P)) := by
      group
    rw [e]
    exact nearAt_mul_int _ (hp'.frame P) (hin P) (seamGL_int t.seam (κ'' P)⁻¹)
  · have H := funMoved_mul_lev t.seam _ P v h _ _ _ κ' (hp'.fnl P v h hvP)
    rw [hx, ← mul_assoc]
    unfold FunMoved at H ⊢
    intro w hw z hz
    exact (congrFun (congrFun hf P) w).trans (H w (hN ▸ hw) z hz)
  · unfold phiT
    refine @if_congr _ _ _ (_) (_) _ _ _ _ ?_ rfl rfl
    simp only [Deco.at, hN, hf]

end GlobalTheory.CplPt
