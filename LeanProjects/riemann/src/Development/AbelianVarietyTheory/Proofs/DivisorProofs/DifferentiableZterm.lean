import Mathlib
import Formalism.PairingDivisors.StatementA
import Development.AbelianVarietyTheory.Definitions.Divisors.IsFinSetSplitPlacesCoprimeConductor
import Development.AbelianVarietyTheory.Definitions.Divisors.HasSumZeroOfTwoLe
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValuedEqOneOfLe
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.TsumIdealMulAbsNormCpowEqExpTsum

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal

namespace GlobalTheory.CMVal.LatEnt

def QSum {G : Type} [CommGroup G] (H : Subgroup G) (F : G → ℂ) (a : ℂ) : Prop :=
  HasSum (fun q : G ⧸ H => F q.out) a

section Generic

variable {G : Type} [CommGroup G] {H H' : Subgroup G} {F : G → ℂ} {a : ℂ}

theorem out_mk (hF : ∀ g, ∀ u ∈ H, F (g * u) = F g) (g : G) : F (QuotientGroup.mk g : G ⧸ H).out = F g := by
  obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul H g
  rw [hu, hF _ _ u.2]

theorem QSum.translate (hF : ∀ g, ∀ u ∈ H, F (g * u) = F g) (h : QSum H F a) (t : G) :
    QSum H (fun g => F (t * g)) a := by
  unfold QSum at *
  rw [← (Equiv.mulLeft (QuotientGroup.mk t : G ⧸ H)).hasSum_iff] at h
  refine h.congr_fun fun q => ?_
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  have h2 : ∀ g, ∀ u ∈ H, F (t * (g * u)) = F (t * g) := fun g u hu => by rw [← mul_assoc, hF _ _ hu]
  exact (out_mk (F := fun g => F (t * g)) h2 g).trans (out_mk hF (t * g)).symm

theorem QSum.eq_zero (hF : ∀ g, ∀ u ∈ H, F (g * u) = F g) (h : QSum H F a) {t : G} {c : ℂ} (hc : c ≠ 1)
    (ht : ∀ g, F (t * g) = c * F g) : a = 0 := by
  have h1 := h.translate hF t
  unfold QSum at *
  simp only [ht] at h1
  have h2 := h1.unique (h.mul_left c)
  have : (c - 1) * a = 0 := by linear_combination -h2
  exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hc)

theorem qsum_index (hle : H ≤ H') (hn : H.relIndex H' ≠ 0) (hF : ∀ g, ∀ u ∈ H', F (g * u) = F g) :
    QSum H' F a ↔ QSum H F (H.relIndex H' * a) := by
  unfold QSum
  haveI : (H.subgroupOf H').FiniteIndex := ⟨hn⟩
  haveI := Fintype.ofFinite (H' ⧸ H.subgroupOf H')
  have hc : (Fintype.card (H' ⧸ H.subgroupOf H') : ℂ) = H.relIndex H' := by
    rw [Subgroup.relIndex, Subgroup.index, Nat.card_eq_fintype_card]
  have hn' : (H.relIndex H' : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn
  let e := Subgroup.quotientEquivProdOfLE hle
  have he : ∀ q : G ⧸ H, F q.out = (fun p : (G ⧸ H') × (H' ⧸ H.subgroupOf H') => F p.1.out * 1) (e q) := fun q => by
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    rw [out_mk fun g u hu => hF g u (hle hu)]
    show _ = F (QuotientGroup.mk g : G ⧸ H').out * 1
    rw [out_mk hF, mul_one]
  simp only [he]
  rw [show (fun q => (fun p : (G ⧸ H') × (H' ⧸ H.subgroupOf H') => F p.1.out * 1) (e q)) =
    (fun p : (G ⧸ H') × (H' ⧸ H.subgroupOf H') => F p.1.out * 1) ∘ e from rfl, e.hasSum_iff]
  have h1 : HasSum (fun _ : H' ⧸ H.subgroupOf H' => (1 : ℂ)) (H.relIndex H') := by
    simpa [hc] using hasSum_fintype (fun _ : H' ⧸ H.subgroupOf H' => (1 : ℂ))
  constructor
  · intro h
    rw [mul_comm]
    have h3 := summable_mul_of_summable_norm (f := fun q : G ⧸ H' => F q.out)
      (g := fun _ : H' ⧸ H.subgroupOf H' => (1 : ℂ)) h.summable.norm h1.summable.norm
    exact HasSum.mul (f := fun q : G ⧸ H' => F q.out) (g := fun _ : H' ⧸ H.subgroupOf H' => (1 : ℂ)) h h1 h3
  · intro h
    have h2 := (h.prod_fiberwise fun q => h1.mul_left (F q.out)).mul_right (H.relIndex H' : ℂ)⁻¹
    simp only [mul_assoc, mul_inv_cancel₀ hn', mul_one] at h2
    rwa [mul_left_comm, mul_inv_cancel₀ hn', mul_one] at h2

end Generic

variable {E : Type} [Field E] [NumberField E]

def box (r : HeightOneSpectrum (𝓞 E) → WithZero (Multiplicative ℤ)) : Set (Af E)ˣ :=
  {z | ∀ w, Valued.v ((z : Af E) w - 1) ≤ r w}

def congr (r : HeightOneSpectrum (𝓞 E) → WithZero (Multiplicative ℤ)) : Subgroup (Af E)ˣ where
  carrier := {z | ∀ w, Valued.v ((z : Af E) w) = 1 ∧ Valued.v ((z : Af E) w - 1) ≤ r w}
  one_mem' := fun w => by
    have : ((1 : (Af E)ˣ) : Af E) w = 1 := rfl
    rw [this]; simp
  mul_mem' := fun {a b} ha hb w => by
    have : ((a * b : (Af E)ˣ) : Af E) w = (a : Af E) w * (b : Af E) w := rfl
    rw [this]
    refine ⟨by rw [map_mul, (ha w).1, (hb w).1, one_mul], ?_⟩
    rw [show (a : Af E) w * (b : Af E) w - 1 = (a : Af E) w * ((b : Af E) w - 1) + ((a : Af E) w - 1) by ring]
    exact Valuation.map_add_le _ (by rw [map_mul, (ha w).1, one_mul]; exact (hb w).2) (ha w).2
  inv_mem' := fun {a} ha w => by
    have h : (a : Af E) w * ((a⁻¹ : (Af E)ˣ) : Af E) w = 1 := (coord w a).val_inv
    have h1 : Valued.v (((a⁻¹ : (Af E)ˣ) : Af E) w) = 1 := by
      have := congrArg Valued.v h
      rwa [map_mul, (ha w).1, one_mul, map_one] at this
    refine ⟨h1, ?_⟩
    rw [show ((a⁻¹ : (Af E)ˣ) : Af E) w - 1 = -(((a⁻¹ : (Af E)ˣ) : Af E) w * ((a : Af E) w - 1)) by
      linear_combination h, Valuation.map_neg, map_mul, h1, one_mul]
    exact (ha w).2

theorem mem_congr {r : HeightOneSpectrum (𝓞 E) → WithZero (Multiplicative ℤ)} {z : (Af E)ˣ} :
    z ∈ congr r ↔ ∀ w, Valued.v ((z : Af E) w) = 1 ∧ Valued.v ((z : Af E) w - 1) ≤ r w := Iff.rfl

def radN (E : Type) [Field E] [NumberField E] (N : ℕ) (w : HeightOneSpectrum (𝓞 E)) : WithZero (Multiplicative ℤ) :=
  Valued.v (N : w.adicCompletion E)

def zterm (χ : HChar E) (s : ℂ) (z : (Af E)ˣ) : ℂ := (finPart χ z : ℂ) * ((modF z : ℝ) : ℂ) ^ s

theorem zterm_mul (χ : HChar E) (s : ℂ) (z z' : (Af E)ˣ) : zterm χ s (z * z') = zterm χ s z * zterm χ s z' := by
  unfold zterm
  rw [map_mul, ObjModel.modF_mul, Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg (ObjModel.modF_pos _).le (ObjModel.modF_pos _).le, Units.val_mul]
  ring

theorem differentiable_zterm (χ : HChar E) (z : (Af E)ˣ) : Differentiable ℂ fun s => zterm χ s z :=
  Differentiable.const_mul (Differentiable.const_cpow differentiable_id
    (Or.inl (by exact_mod_cast (ObjModel.modF_pos z).ne'))) _

theorem zterm_ne_zero (χ : HChar E) (s : ℂ) (z : (Af E)ˣ) : zterm χ s z ≠ 0 :=
  mul_ne_zero (Units.ne_zero _) (by
    rw [Ne, Complex.cpow_eq_zero_iff, not_and_or]
    exact Or.inl (by exact_mod_cast (ObjModel.modF_pos z).ne'))

theorem modF_eq_one {u : (Af E)ˣ} (hu : ∀ w, Valued.v ((u : Af E) w) = 1) : modF u = 1 := by
  unfold modF
  exact finprod_eq_one_of_forall_eq_one fun v => by simp [hu v]

theorem zterm_unit (χ : HChar E) (s : ℂ) {u : (Af E)ˣ} (hu : ∀ w, Valued.v ((u : Af E) w) = 1) :
    zterm χ s u = finPart χ u := by
  simp [zterm, modF_eq_one hu]

theorem norm_zterm {χ : HChar E} (h : IsUnitary χ) (s : ℂ) (z : (Af E)ˣ) : ‖zterm χ s z‖ = modF z ^ s.re := by
  have : ‖(finPart χ z : ℂ)‖ = 1 := h _
  rw [zterm, norm_mul, this, one_mul, Complex.norm_cpow_eq_rpow_re_of_pos (ObjModel.modF_pos z)]

theorem mul_mem_box {r : HeightOneSpectrum (𝓞 E) → WithZero (Multiplicative ℤ)} {z u : (Af E)ˣ} (hu : u ∈ congr r) :
    z * u ∈ box r ↔ z ∈ box r := by
  have key : ∀ z u : (Af E)ˣ, u ∈ congr r → z ∈ box r → z * u ∈ box r := fun z u hu hz w => by
    have : ((z * u : (Af E)ˣ) : Af E) w = (z : Af E) w * (u : Af E) w := rfl
    rw [this, show (z : Af E) w * (u : Af E) w - 1 = (u : Af E) w * ((z : Af E) w - 1) + ((u : Af E) w - 1) by ring]
    exact Valuation.map_add_le _ (by rw [map_mul, (hu w).1, one_mul]; exact hz w) (hu w).2
  exact ⟨fun h => by simpa using key _ _ (inv_mem hu) h, key _ _ hu⟩

theorem congr_mono {r r' : HeightOneSpectrum (𝓞 E) → WithZero (Multiplicative ℤ)} (h : ∀ w, r w ≤ r' w) :
    congr r ≤ congr r' := fun _ hz w => ⟨(hz w).1, (hz w).2.trans (h w)⟩

theorem mem_hatO_of_sub {c : Ideal (OF E)} {n : ℕ} (hn : 0 < n) (hc : (n : OF E) ∈ c) {a z : Af E} (ha : a ∈ hatO c)
    (hz : ∀ P, Valued.v (z P - a P) ≤ radN E n P) : z ∈ hatO c := by
  have hn0 : (n : E) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  have key := GlobalTheory.IntDense.mem_of_isClosed E (C := {α | algebraMap E (Af E) n * α ∈ hatO c})
    ((Subring.isClosed_topologicalClosure _).preimage (continuous_const.mul continuous_id)) (fun a => by
      show _ ∈ hatO c
      rw [← map_mul]
      refine algebraMap_mem_hatO (mem_orderC.2 ⟨0, algebraMap (OF E) (𝓞 E) n * a,
        Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hc), ?_⟩)
      simp) (algebraMap E (Af E) (n : E)⁻¹ * (z - a)) fun P => by
      have h0 := GlobalTheory.AdLat.valued_natCast_ne_zero P hn
      show Valued.v (algebraMap E (P.adicCompletion E) (n : E)⁻¹ * (z P - a P)) ≤ 1
      rw [map_mul, map_inv₀, map_inv₀, map_natCast, inv_mul_le_iff₀ (zero_lt_iff.2 h0), mul_one]
      exact hz P
  have e : z = algebraMap E (Af E) n * (algebraMap E (Af E) (n : E)⁻¹ * (z - a)) + a := by
    rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hn0, map_one, one_mul, sub_add_cancel]
  rw [e]
  exact add_mem key ha

theorem congr_le_hatOUnits {c : Ideal (OF E)} {n : ℕ} (hn : 0 < n) (hc : (n : OF E) ∈ c) :
    congr (radN E n) ≤ hatOUnits c := fun _ hu =>
  mem_hatOUnits.2 ⟨mem_hatO_of_sub hn hc (one_mem _) fun P => (hu P).2,
    mem_hatO_of_sub hn hc (one_mem _) fun P => (inv_mem hu P).2⟩

theorem hatOUnits_le_congr (c : Ideal (OF E)) : hatOUnits c ≤ congr (fun _ => 1) := fun u hu w => by
  have h : Valued.v ((u : Af E) w) = 1 :=
    GlobalTheory.Mem.TupHecke.valued_eq_one_of_le (coord w u) (ObjModel.hatO_integral hu.1 w) (ObjModel.hatO_integral hu.2 w)
  exact ⟨h, Valuation.map_sub_le _ h.le (by simp)⟩

end GlobalTheory.CMVal.LatEnt
