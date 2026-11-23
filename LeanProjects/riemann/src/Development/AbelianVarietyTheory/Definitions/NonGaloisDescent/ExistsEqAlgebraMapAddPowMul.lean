import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InstTameDescentExponentDataPadicThree
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgebraMapMemNonZeroDivisorsAdicCompletion

noncomputable section

namespace GlobalTheory.BK

open PowerSeries Filter Topology Matrix

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] {l e a : ℕ} {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

section Scalars

variable (l e) [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [CompleteSpace K]

theorem mem_A_of_E_mul_mem {h : K⟦X⟧} (hh : h ∈ Rpi O K l e) (hE : E K l e * h ∈ A O K) :
    h ∈ A O K := by
  obtain ⟨b, hb⟩ := (mem_invL_A_iff l).1 (mem_invL_A_of_E_mul l e hh (le_away _ _ hE))
  have hbdd : BddAbove (Set.range fun n => ‖coeff n h‖) := ⟨b, by rintro _ ⟨n, rfl⟩; exact hb n⟩
  have hle (n : ℕ) : ‖coeff n h‖ ≤ ⨆ n, ‖coeff n h‖ := le_ciSup hbdd n
  have h1 : ⨆ n, ‖coeff n h‖ ≤ max 1 (‖(l : K)‖ * ⨆ n, ‖coeff n h‖) := ciSup_le fun n => by
    have : coeff n h = coeff (n + e) (E K l e * h) + -(l * coeff (n + e) h) := by
      rw [coeff_E_mul]; ring
    rw [this]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le_max (hE _) ?_)
    rw [norm_neg, norm_mul]
    exact mul_le_mul_of_nonneg_left (hle _) (norm_nonneg _)
  intro n
  refine (hle n).trans ?_
  rcases le_max_iff.1 h1 with h2 | h2
  · exact h2
  · nlinarith [norm_l_lt_one (K := K) l]

theorem mem_A_of_E_pow_mul_mem (m : ℕ) {h : K⟦X⟧} (hh : h ∈ Rpi O K l e)
    (hE : E K l e ^ m * h ∈ A O K) : h ∈ A O K := by
  induction m with
  | zero => simpa using hE
  | succ m ih =>
    refine ih (mem_A_of_E_mul_mem l e (mul_mem (pow_mem (E_mem l e _) m) hh) ?_)
    rwa [← mul_assoc, ← pow_succ']

theorem algebraMap_AhatE_injective :
    Function.Injective (algebraMap (Ahat O K l e) (AhatE O K l e)) :=
  IsLocalization.injective _ (Submonoid.powers_le.2 (Ehat_mem_nonZeroDivisors O K l e))

theorem hat_E_pow_mul (n : ℕ) {f : K⟦X⟧} (hf : f ∈ RpiE O K l e) :
    hat O l e (E K l e ^ n * f) = algebraMap _ _ (Ehat O K l e ^ n) * hat O l e f := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', mul_assoc, hat_mul l e (E_mem l e _) (mul_mem (pow_mem (E_mem l e _) n) hf), ih,
      hat_E, pow_succ', map_mul, mul_assoc]

theorem hat_sub {f g : K⟦X⟧} (hf : f ∈ RpiE O K l e) (hg : g ∈ RpiE O K l e) :
    hat O l e (f - g) = hat O l e f - hat O l e g := by
  rw [eq_sub_iff_add_eq, ← hat_add l e (sub_mem hf hg) hg, sub_add_cancel]

theorem hat_mem_range_iff {f : K⟦X⟧} (hf : f ∈ RpiE O K l e) :
    (∃ x : Ahat O K l e, algebraMap _ _ x = hat O l e f) ↔ f ∈ Rpi O K l e := by
  refine ⟨fun ⟨x, hx⟩ => ?_, fun h => ⟨_, (hat_coe_Rpi l e ⟨f, h⟩).symm⟩⟩
  obtain ⟨n, hn⟩ := id hf
  have h1 : toHat O K l e ⟨_, hn⟩ = Ehat O K l e ^ n * x := algebraMap_AhatE_injective l e (by
    rw [← hat_coe_Rpi, map_mul, hx]
    exact hat_E_pow_mul l e n hf)
  have hE : AdicCompletion.evalₐ (idE O K l e) n (Ehat O K l e) =
      Ideal.Quotient.mk _ (EIn l e _) := AlgHom.commutes _ _
  obtain ⟨h, hh, H⟩ := (evalₐ_toHat_eq_iff l e n ⟨_, hn⟩ 0).1 (by
    rw [h1, map_mul, map_pow, hE, ← map_pow, Ideal.Quotient.eq_zero_iff_mem.2
      (Ideal.pow_mem_pow (Ideal.mem_span_singleton_self _) n), zero_mul, map_zero])
  have H' : E K l e ^ n * f = E K l e ^ n * h := by simpa using H
  rwa [((isUnit_E l e).pow n).mul_left_cancel H']

theorem exists_eq_algebraMap_add_pow_mul {B : Type} [CommRing B] (s : B) (n : ℕ)
    (x : AdicCompletion (Ideal.span {s}) B) :
    ∃ (g : B) (x' : AdicCompletion (Ideal.span {s}) B),
      x = algebraMap B _ g + algebraMap B _ s ^ n * x' := by
  obtain ⟨g, hg⟩ := Submodule.Quotient.mk_surjective _ (AdicCompletion.eval (Ideal.span {s}) B n x)
  have h : x - AdicCompletion.of (Ideal.span {s}) B g ∈
      Ideal.span {s} ^ n • (⊤ : Submodule B (AdicCompletion (Ideal.span {s}) B)) := by
    rw [AdicCompletion.pow_smul_top_eq_ker_eval (Submodule.fg_span_singleton _), LinearMap.mem_ker,
      map_sub, ← hg, sub_eq_zero]
    rfl
  rw [Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul,
    Submodule.mem_smul_pointwise_iff_exists] at h
  obtain ⟨x', -, hx'⟩ := h
  refine ⟨g, x', ?_⟩
  rw [Algebra.smul_def, map_pow, eq_sub_iff_add_eq'] at hx'
  exact hx'.symm

theorem toHat_derivative (f : Rpi O K l e) :
    toHat O K l e ⟨_, derivative_mem_R l f.2⟩ = dHat O K l e (toHat O K l e f) := by
  refine AdicCompletion.ext_evalₐ fun n => ?_
  obtain ⟨g, hg⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ _ (n + 1) (toHat O K l e f))
  rw [dHat, evalₐ_complDer _ _ hg.symm, evalₐ_toHat_eq_iff]
  obtain ⟨h, hh, H⟩ := (evalₐ_toHat_eq_iff l e (n + 1) f g).1 hg.symm
  refine ⟨E K l e * PowerSeries.derivative K h +
    h * (((n + 1 : ℕ) : K⟦X⟧) * PowerSeries.derivative K (E K l e)), add_mem
      (mul_mem (E_mem l e _) (derivative_mem_R l hh)) (mul_mem hh (mul_mem (natCast_mem _ _)
        (derivative_mem_R l (E_mem l e _)))), ?_⟩
  rw [coe_derAl, ← map_sub, H, Derivation.leibniz, derivative_pow]
  simp only [smul_eq_mul, Nat.add_sub_cancel]
  ring

omit [NormedAlgebra ℚ_[l] K] [NeZero e] [CompleteSpace K] in
theorem N_mem_RpiE {f : K⟦X⟧} (hf : f ∈ RpiE O K l e) : N K f ∈ RpiE O K l e :=
  N_mem (derivative_mem_away _ (fun _ => derivative_mem_R l) hf)

theorem hat_N_of_mem_Rpi {f : K⟦X⟧} (hf : f ∈ Rpi O K l e) :
    hat O l e (N K f) = NHatE O K l e (hat O l e f) := by
  have hu : hat O l e (X : K⟦X⟧) = algebraMap _ _ (uhat O K l e) :=
    (hat_coe_Rpi l e (uIn _)).trans (congrArg _ (toHat_eq_ofAl l e rfl))
  rw [N_apply, hat_mul l e HasU.X_mem (le_away _ _ (derivative_mem_R l hf)), hu,
    hat_coe_Rpi l e ⟨f, hf⟩, hat_coe_Rpi l e ⟨_, derivative_mem_R l hf⟩, toHat_derivative l e ⟨f, hf⟩,
    NHatE, Derivation.smul_apply, dHatE_algebraMap, smul_eq_mul]

theorem hat_N {f : K⟦X⟧} (hf : f ∈ RpiE O K l e) :
    hat O l e (N K f) = NHatE O K l e (hat O l e f) := by
  obtain ⟨n, hn⟩ := id hf
  have hE : E K l e ^ n ∈ Rpi O K l e := pow_mem (E_mem l e _) n
  have hE' : E K l e ^ n ∈ RpiE O K l e := le_away _ _ hE
  have h1 := hat_N_of_mem_Rpi l e hn
  rw [coe_EIn, Derivation.leibniz, smul_eq_mul, smul_eq_mul,
    hat_add l e (mul_mem hE' (N_mem_RpiE l e hf)) (mul_mem hf (N_mem_RpiE l e hE')),
    hat_mul l e hf (N_mem_RpiE l e hE'), hat_N_of_mem_Rpi l e hE, hat_mul l e hE' hf,
    Derivation.leibniz, smul_eq_mul, smul_eq_mul, add_left_inj, hat_E_pow_mul l e n (N_mem_RpiE l e hf),
    ← mul_one (E K l e ^ n), hat_E_pow_mul l e n (one_mem _),
    show hat O l e (1 : K⟦X⟧) = 1 from (hat_coe l e 1).trans (map_one _), mul_one, map_pow] at h1
  exact ((IsLocalization.Away.algebraMap_isUnit (Ehat O K l e)).pow n).mul_left_cancel h1

variable (K) in

def Ezpow (i : ℤ) : K⟦X⟧ := (((isUnit_E (K := K) l e).unit ^ i : K⟦X⟧ˣ) : K⟦X⟧)

omit [IsUltrametricDist K] [CompleteSpace K]

@[simp] theorem Ezpow_natCast (n : ℕ) : Ezpow K l e n = E K l e ^ n := by simp [Ezpow]

theorem Ezpow_add (i j : ℤ) : Ezpow K l e (i + j) = Ezpow K l e i * Ezpow K l e j := by
  simp [Ezpow, _root_.zpow_add]

theorem E_pow_mul_Ezpow_neg (n : ℕ) : E K l e ^ n * Ezpow K l e (-n) = 1 := by
  rw [← Ezpow_natCast, ← Ezpow_add]
  simp [Ezpow]

end Scalars

section DivE

variable {R : Type} [Semiring R] [Module R (Vec K a ι)] [SMulCommClass R K⟦X⟧ (Vec K a ι)]

variable (l e) in

def divE (n : ℕ) (W : Submodule R (Vec K a ι)) : Submodule R (Vec K a ι) where
  carrier := {y | E K l e ^ n • y ∈ W}
  add_mem' hv hw := by simpa only [Set.mem_ofPred_eq, smul_add] using W.add_mem hv hw
  zero_mem' := by simp
  smul_mem' c y hy := by simpa only [Set.mem_ofPred_eq, smul_comm c] using W.smul_mem c hy

omit [IsUltrametricDist K] [Fintype ι] [DecidableEq ι] in
theorem mem_divE {n : ℕ} {W : Submodule R (Vec K a ι)} {y : Vec K a ι} :
    y ∈ divE l e n W ↔ E K l e ^ n • y ∈ W := Iff.rfl

variable [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e]

variable (l e) in

def shiftE (i : ℤ) (W : Submodule R (Vec K a ι)) : Submodule R (Vec K a ι) where
  carrier := {y | Ezpow K l e (-i) • y ∈ W}
  add_mem' hv hw := by simpa only [Set.mem_ofPred_eq, smul_add] using W.add_mem hv hw
  zero_mem' := by simp
  smul_mem' c y hy := by simpa only [Set.mem_ofPred_eq, smul_comm c] using W.smul_mem c hy

omit [IsUltrametricDist K] [Fintype ι] [DecidableEq ι] in
theorem mem_shiftE {i : ℤ} {W : Submodule R (Vec K a ι)} {y : Vec K a ι} :
    y ∈ shiftE l e i W ↔ Ezpow K l e (-i) • y ∈ W := Iff.rfl

end DivE

variable (K a ι) in

def mulV (f : K⟦X⟧) : Module.End K (Vec K a ι) where
  toFun v := f • v
  map_add' := smul_add f
  map_smul' c v := smul_comm f c v

omit [IsUltrametricDist K] [Fintype ι] [DecidableEq ι] in
@[simp] theorem mulV_apply (f : K⟦X⟧) (v : Vec K a ι) : mulV K a ι f v = f • v := rfl

namespace PhiMod

variable (P : PhiMod O K l e a ι)

abbrev EM (η : ℕ) : Submodule (A O K) (Vec K a ι) := divE l e η P.M

theorem mem_Mext_invE_of_mem_divE {B : Subalgebra O K⟦X⟧} [HasU B] {n : ℕ} {y : Vec K a ι}
    (hy : E K l e ^ n • y ∈ P.Mext B) : y ∈ P.Mext (invE l e B) :=
  mem_tot.2 fun τ i => ⟨n, mem_tot.1 hy τ i⟩

def Man : Submodule K (Vec K a ι) := (P.Mext (Rpi O K l e)).restrictScalars K

theorem mem_Man {v : Vec K a ι} : v ∈ P.Man ↔ v ∈ P.Mext (Rpi O K l e) := Iff.rfl

theorem smul_mem_Man {f : K⟦X⟧} (hf : f ∈ Rpi O K l e) {v : Vec K a ι} (hv : v ∈ P.Man) :
    f • v ∈ P.Man := P.smul_tot_mem_Mext (f := fun _ => f) (fun _ => hf) hv

abbrev Pol : Type := Vec K a ι ⧸ P.Man

abbrev cls : Vec K a ι →ₗ[K] P.Pol := P.Man.mkQ

theorem cls_eq_zero_iff {v : Vec K a ι} : P.cls v = 0 ↔ v ∈ P.Man := Submodule.Quotient.mk_eq_zero _

def PolEta (η : ℕ) : Submodule K P.Pol := (divE l e η P.Man).map P.cls

def mulPol (f : Rpi O K l e) : Module.End K P.Pol :=
  P.Man.mapQ P.Man (mulV K a ι f) fun _ => P.smul_mem_Man f.2

@[simp] theorem mulPol_cls (f : Rpi O K l e) (v : Vec K a ι) :
    P.mulPol f (P.cls v) = P.cls ((f : K⟦X⟧) • v) := rfl

def vPol : Module.End K P.Pol := P.mulPol (uIn _ ^ e)

@[simp] theorem vPol_cls (v : Vec K a ι) : P.vPol (P.cls v) = P.cls ((X : K⟦X⟧) ^ e • v) := rfl

variable [Fact l.Prime]

def EN : Module.End K (Vec K a ι) := mulV K a ι (E K l e) * P.conn

theorem EN_apply (v : Vec K a ι) : P.EN v = E K l e • P.conn v := rfl

def Mon : Vec K a ι →ₗ[K] P.Pol := P.cls ∘ₗ (P.EN - mulV K a ι (E K l e) * P.zeta)

theorem Mon_apply (y : Vec K a ι) : P.Mon y = P.cls (P.EN y - E K l e • P.zeta y) := rfl

theorem eisenstein_x_eq_neg {y : Vec K a ι} (hy : y ∈ P.Mext (invE l e (A O K))) :
    (P.plus hy).EN xVec = -(P.plusInl hy).app (P.EN y - E K l e • P.zeta y) := by
  rw [EN_apply, plus_conn_xVec_eq, EN_apply, ← smul_sub, ← map_smul, ← map_neg, ← smul_neg, neg_sub]

theorem Mon_eq_zero_iff {y : Vec K a ι} (hy : y ∈ P.Mext (invE l e (A O K))) :
    P.Mon y = 0 ↔ (P.plus hy).EN xVec ∈ (P.plus hy).Man := by
  rw [eisenstein_x_eq_neg, neg_mem_iff, plusInl_app, mem_Man, P.join_mem_Mext hy, Mon_apply, cls_eq_zero_iff]
  exact ⟨fun h => ⟨h, fun _ => zero_mem _⟩, fun h => h.1⟩

theorem Mon_phi_sub (m : Vec K a ι) : P.Mon (P.phi m - m) = -P.cls (P.EN m) := by
  rw [Mon_apply, zeta_phi_sub, map_sub P.EN, ← EN_apply, sub_sub_cancel_left, map_neg]

theorem E_pow_smul_EN (n : ℕ) (y : Vec K a ι) : E K l e ^ n • P.EN y =
    P.EN (E K l e ^ n • y) - ((n : K⟦X⟧) * N K (E K l e)) • E K l e ^ n • y := by
  rw [EN_apply, EN_apply, conn_smul, Derivation.leibniz_pow]
  cases n with
  | zero => simp
  | succ n =>
    ext τ i : 2
    simp only [Nat.add_sub_cancel, nsmul_eq_mul, smul_eq_mul, Pi.smul_apply, Pi.sub_apply,
      Pi.add_apply]
    ring

variable [NormedAlgebra ℚ_[l] K] [NeZero e]

theorem M_le_Man {v : Vec K a ι} (hv : v ∈ P.M) : v ∈ P.Man := P.Mext_mono (A_le_Rpi l e) hv

theorem cls_mem_PolEta {η : ℕ} {y : Vec K a ι} (hy : y ∈ P.EM η) : P.cls y ∈ P.PolEta η :=
  ⟨y, P.M_le_Man hy, rfl⟩

def filL (i : ℤ) : Submodule (invL l (A O K)) (Vec K a ι) :=
  (P.ext (invL l (A O K)) ⊓ shiftE l e i (P.Mext (invL l (A O K)))) ⊔
    shiftE l e 1 (P.ext (invL l (A O K)))

def jumps : Set ℤ := {i | P.filL (i + 1) ≠ P.filL i}

variable [CompleteSpace K]

theorem mem_M_of_mem_Man {η : ℕ} {y : Vec K a ι} (hy : y ∈ P.EM η) (h : y ∈ P.Man) : y ∈ P.M :=
  mem_tot.2 fun τ i => mem_A_of_E_pow_mul_mem l e η (mem_tot.1 h τ i) (mem_tot.1 hy τ i)

theorem mem_Mhat {w : ZMod a → ι → AhatE O K l e} :
    w ∈ P.Mhat ↔ ∀ τ i, ∃ x : Ahat O K l e, algebraMap _ _ x = w τ i := by
  simp only [Mhat, Submodule.mem_pi, Set.mem_univ, true_imp_iff, mem_Mhatc]

theorem hatTot_mem_Mhat_iff {v : Vec K a ι} (hv : v ∈ P.Mext (RpiE O K l e)) :
    P.hatTot v ∈ P.Mhat ↔ v ∈ P.Man :=
  P.mem_Mhat.trans <| Iff.trans (forall₂_congr fun τ i => hat_mem_range_iff l e (mem_tot.1 hv τ i))
    (mem_tot (P := fun _ => vecs ι (Rpi O K l e))).symm

theorem hatTot_sub_mem_Mhat_iff {v w : Vec K a ι} (hv : v ∈ P.Mext (RpiE O K l e))
    (hw : w ∈ P.Mext (RpiE O K l e)) : P.hatTot v - P.hatTot w ∈ P.Mhat ↔ P.cls v = P.cls w := by
  have : P.hatTot v - P.hatTot w = P.hatTot (v - w) := funext fun τ => funext fun i =>
    (hat_sub l e (mem_tot.1 hv τ i) (mem_tot.1 hw τ i)).symm
  rw [this, P.hatTot_mem_Mhat_iff (sub_mem hv hw)]
  exact (Submodule.Quotient.eq _).symm

theorem smul_hatTot_mem_Mhat_iff (η : ℕ) {v : Vec K a ι} (hv : v ∈ P.Mext (RpiE O K l e)) :
    Ehat O K l e ^ η • P.hatTot v ∈ P.Mhat ↔ v ∈ divE l e η P.Man := by
  have : Ehat O K l e ^ η • P.hatTot v = P.hatTot (E K l e ^ η • v) := funext fun τ => funext fun i =>
    (Algebra.smul_def _ _).trans (hat_E_pow_mul l e η (mem_tot.1 hv τ i)).symm
  rw [this, mem_divE]
  exact P.hatTot_mem_Mhat_iff
    (P.smul_tot_mem_Mext (f := fun _ => E K l e ^ η) (fun _ => pow_mem (E_mem l e _) η) hv)

theorem exists_sub_hatTot_mem_Mhat (η : ℕ) {w : ZMod a → ι → AhatE O K l e}
    (hw : Ehat O K l e ^ η • w ∈ P.Mhat) :
    ∃ v ∈ divE l e η (P.Mext (invL l (A O K))), w - P.hatTot v ∈ P.Mhat := by
  choose x hx using P.mem_Mhat.1 hw
  choose g x' hg using fun τ i =>
    exists_eq_algebraMap_add_pow_mul (EIn l e (invL l (A O K))) η (x τ i)
  have hE (τ i) : E K l e ^ η * (Ezpow K l e (-η) * g τ i) = g τ i := by
    rw [← mul_assoc, E_pow_mul_Ezpow_neg, one_mul]
  refine ⟨fun τ i => Ezpow K l e (-η) * g τ i, mem_tot.2 fun τ i => ?_,
    P.mem_Mhat.2 fun τ i => ⟨x' τ i, ?_⟩⟩
  · change E K l e ^ η * (Ezpow K l e (-η) * g τ i) ∈ invL l (A O K)
    rw [hE]
    exact (g τ i).2
  · have hg' := invL_A_le_Rpi l e (g τ i).2
    have h0 : Ezpow K l e (-η) * (g τ i : K⟦X⟧) ∈ RpiE O K l e := ⟨η, by rw [coe_EIn, hE]; exact hg'⟩
    have h1 := hat_E_pow_mul l e η h0
    rw [hE, hat_coe_Rpi l e ⟨_, hg'⟩, toHat_eq_ofAl l e (g := g τ i) rfl] at h1
    have h2 : algebraMap _ _ (x τ i) = algebraMap _ _ (Ehat O K l e ^ η) * w τ i :=
      (hx τ i).trans (Algebra.smul_def (Ehat O K l e ^ η) (w τ i))
    have h3 : x τ i = ofAl O K l e (g τ i) + Ehat O K l e ^ η * x' τ i := hg τ i
    rw [h3, map_add, map_mul, h1, add_comm, ← eq_sub_iff_add_eq, ← mul_sub, map_pow] at h2
    exact ((IsLocalization.Away.algebraMap_isUnit (Ehat O K l e)).pow η).mul_left_cancel h2

def connHat (w : ZMod a → ι → AhatE O K l e) : ZMod a → ι → AhatE O K l e :=
  fun τ i => NHatE O K l e (w τ i) + ∑ j, w τ j * P.hatTot (P.conn (bas j)) τ i

omit [NormedAlgebra ℚ_[l] K] [NeZero e] [CompleteSpace K] in
theorem conn_apply_eq (v : Vec K a ι) (τ : ZMod a) (i : ι) :
    P.conn v τ i = N K (v τ i) + ∑ j, v τ j * P.conn (bas j) τ i := by
  conv_lhs => rw [eq_sum_bas v]
  simp [conn_smul_tot, Finset.sum_apply, Finset.sum_add_distrib, bas, NTot, Pi.single_apply]

theorem hatTot_conn (hN : ∀ j, P.conn (bas j) ∈ P.Mext (RpiE O K l e)) {v : Vec K a ι}
    (hv : v ∈ P.Mext (RpiE O K l e)) : P.hatTot (P.conn v) = P.connHat (P.hatTot v) := by
  ext τ i
  have h1 (j) : v τ j ∈ RpiE O K l e := mem_tot.1 hv τ j
  have h2 (j) : P.conn (bas j) τ i ∈ RpiE O K l e := mem_tot.1 (hN j) τ i
  have h3 : ∑ j, v τ j * P.conn (bas j) τ i =
      ((∑ j, ⟨_, h1 j⟩ * ⟨_, h2 j⟩ : RpiE O K l e) : K⟦X⟧) := by simp
  change hat O l e (P.conn v τ i) = NHatE O K l e (hat O l e _) + ∑ j, hat O l e _ * hat O l e _
  rw [conn_apply_eq, hat_add l e (N_mem_RpiE l e (h1 i))
    (sum_mem fun j _ => mul_mem (h1 j) (h2 j)), hat_N l e (h1 i), h3, hat_coe, map_sum]
  simp only [map_mul, hat_of_mem l e (h1 _), hat_of_mem l e (h2 _)]

end PhiMod

namespace Hom

variable [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e]
  {P : PhiMod O K l e a ι} {Q : PhiMod O K l e a κ} (F : Hom P Q)

def onPol : P.Pol →ₗ[K] Q.Pol :=
  P.Man.mapQ Q.Man (F.app.restrictScalars K) fun _ => F.app_mem_Mext (A_le_Rpi l e)

@[simp] theorem onPol_cls (v : Vec K a ι) : F.onPol (P.cls v) = Q.cls (F.app v) := rfl

omit [NormedAlgebra ℚ_[l] K] [NeZero e] in
theorem app_EN (v : Vec K a ι) : F.app (P.EN v) = Q.EN (F.app v) := by
  rw [PhiMod.EN_apply, map_smul, app_conn, PhiMod.EN_apply]

theorem onPol_Mon (y : Vec K a ι) : F.onPol (P.Mon y) = Q.Mon (F.app y) := by
  rw [PhiMod.Mon_apply, onPol_cls, map_sub, app_EN, map_smul, app_zeta, PhiMod.Mon_apply]

omit [NormedAlgebra ℚ_[l] K] [NeZero e] in
theorem app_mem_EM {η : ℕ} {y : Vec K a ι} (hy : y ∈ P.EM η) : F.app y ∈ Q.EM η := by
  rw [mem_divE, ← map_smul]
  exact F.app_mem_M hy

theorem onPol_mem_PolEta {η : ℕ} {w : P.Pol} (hw : w ∈ P.PolEta η) : F.onPol w ∈ Q.PolEta η := by
  obtain ⟨y, hy, rfl⟩ := hw
  refine ⟨F.app y, ?_, rfl⟩
  rw [SetLike.mem_coe, mem_divE, ← map_smul]
  exact F.app_mem_Mext (A_le_Rpi l e) hy

omit [NormedAlgebra ℚ_[l] K] [NeZero e]

def imM : Submodule (A O K) (Vec K a κ) := P.M.map (F.app.restrictScalars (A O K))

def imL : Submodule (A O K) (Vec K a κ) := P.L.map (F.app.restrictScalars (A O K))

abbrev coker : Type := Q.M ⧸ F.imM.submoduleOf Q.M

abbrev cokerL : Type := Q.L ⧸ F.imL.submoduleOf Q.L

end Hom

end GlobalTheory.BK
