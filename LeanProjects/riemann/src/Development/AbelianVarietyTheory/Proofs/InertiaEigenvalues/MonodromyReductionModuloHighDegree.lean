import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ImageStableDegreeBounds
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilRingModHighDegreePropertyStatement

noncomputable section

namespace GlobalTheory.NModHigh

open PowerSeries GlobalTheory.BK GlobalTheory.IndefiniteRowSideFullHecke.ImageStableDegreeBounds Matrix

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] {l e a : ℕ} {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem part_top (V : Submodule O (Vec K a ι)) : part (⊤ : Submodule K (Vec K a ι)) V = V := by
  simp [part]

theorem N_X_pow (i : ℕ) : N K ((X : K⟦X⟧) ^ i) = (i : K⟦X⟧) * X ^ i := by
  ext n
  rw [coeff_N, coeff_X_pow, ← map_natCast (C (R := K)) i, coeff_C_mul, coeff_X_pow]
  split_ifs with h <;> simp [h]

theorem C_mem_A {k : K} (hk : ‖k‖ ≤ 1) : C k ∈ A O K := fun n => by
  rw [coeff_C]
  split_ifs
  · exact hk
  · simp

section Top

variable [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero a]

theorem MMHigh_le_MM (P : PhiMod O K l e a ι) {v : Vec K a ι} (hv : v ∈ MMHigh P) : v ∈ P.MM :=
  Submodule.smul_le_right hv

theorem smul_mem_MMHigh (P : PhiMod O K l e a ι) {f : ZMod a → K⟦X⟧}
    (hf : ∀ τ, f τ ∈ S O K e ∧ (X : K⟦X⟧) ^ (l * e) ∣ f τ) {m : Vec K a ι} (hm : m ∈ P.MM) :
    f • m ∈ MMHigh P := by
  have h1 : f • m = ∑ τ, (⟨f τ, (hf τ).1⟩ : S O K e) •
      ((Pi.single τ (1 : K⟦X⟧) : ZMod a → K⟦X⟧) • m) := by
    funext τ' i
    rw [Finset.sum_apply, Finset.sum_apply, Finset.sum_eq_single τ']
    · simp [Subalgebra.smul_def]
    · intro b _ hb
      simp [Subalgebra.smul_def, Pi.single_apply, Ne.symm hb]
    · simp
  rw [h1]
  change _ ∈ SHigh O K l e • P.MM
  refine Submodule.sum_mem _ fun τ _ => Submodule.smul_mem_smul (mem_SHigh.2 (hf τ).2) ?_
  exact P.smul_tot_mem_ext (fun τ' => by
    rw [Pi.single_apply]
    split_ifs
    exacts [one_mem _, zero_mem _]) hm

theorem coord_dvd_of_mem_MMHigh (P : PhiMod O K l e a ι) {v : Vec K a ι} (hv : v ∈ MMHigh P)
    (τ : ZMod a) (i : ι) : (X : K⟦X⟧) ^ (l * e) ∣ (P.mxInv τ *ᵥ v τ) i := by
  change v ∈ SHigh O K l e • P.MM at hv
  refine Submodule.smul_induction_on
    (p := fun v => ∀ τ i, (X : K⟦X⟧) ^ (l * e) ∣ (P.mxInv τ *ᵥ v τ) i) hv ?_ ?_ τ i
  · intro s hs m _ τ i
    have h1 : (s • m) τ = (s : K⟦X⟧) • m τ := rfl
    rw [h1, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]
    exact dvd_mul_of_dvd_left (mem_SHigh.1 hs) _
  · intro x y hx hy τ i
    rw [Pi.add_apply, Matrix.mulVec_add, Pi.add_apply]
    exact dvd_add (hx τ i) (hy τ i)

theorem X_pow_smul_mem_MMHigh (P : PhiMod O K l e a ι) (i : ℕ) {v : Vec K a ι} (hv : v ∈ MMHigh P) :
    (X : K⟦X⟧) ^ i • v ∈ MMHigh P := by
  change v ∈ SHigh O K l e • P.MM at hv
  change _ ∈ SHigh O K l e • P.MM
  have h1 := (SHigh O K l e • P.MM).smul_mem (⟨X ^ i, pow_mem HasU.X_mem i⟩ : S O K e) hv
  rw [Subalgebra.smul_def] at h1
  exact h1

variable [NeZero e]

theorem L_le_MM (P : PhiMod O K l e a ι) {v : Vec K a ι} (hv : v ∈ P.L) : v ∈ P.MM :=
  P.ext_mono (A_le_S l e) hv

theorem MM_le_sup (hR : RingModHigh O K l e) (P : PhiMod O K l e a ι) {v : Vec K a ι}
    (hv : v ∈ P.MM) : v ∈ P.L.restrictScalars O ⊔ MMHigh P := by
  have hc : ∀ τ i, (P.mxInv τ *ᵥ v τ) i ∈ S O K e := fun τ i =>
    P.mem_extc_iff.1 (mem_tot.1 hv τ) i
  choose g hg h hh hgh using fun p : ZMod a × ι => (hR.eq_add _).1 (hc p.1 p.2)
  rw [P.eq_sum_phi_bas v]
  have h1 : (∑ i, (fun τ => (P.mxInv τ *ᵥ v τ) i) • P.phi (bas i)) =
      (∑ i, (fun τ => g (τ, i)) • P.phi (bas i)) +
        ∑ i, (fun τ => (h (τ, i) : K⟦X⟧)) • P.phi (bas i) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← add_smul]
    congr 1
    funext τ
    exact hgh (τ, i)
  rw [h1]
  refine Submodule.add_mem_sup ?_ ?_
  · exact Submodule.sum_mem _ fun i _ =>
      P.smul_tot_mem_ext (fun τ => hg (τ, i)) (P.phi_mem_L (P.bas_mem_M i))
  · exact Submodule.sum_mem _ fun i _ => smul_mem_MMHigh P
      (fun τ => ⟨(h (τ, i)).2, mem_SHigh.1 (hh (τ, i))⟩)
      (L_le_MM P (P.phi_mem_L (P.bas_mem_M i)))

theorem MM_eq_sup (hR : RingModHigh O K l e) (P : PhiMod O K l e a ι) :
    P.MM.restrictScalars O = P.L.restrictScalars O ⊔ MMHigh P :=
  le_antisymm (fun _ hv => MM_le_sup hR P hv)
    (sup_le (fun _ hv => L_le_MM P hv) (fun _ hv => MMHigh_le_MM P hv))

theorem inter_eq_vL (hR : RingModHigh O K l e) (P : PhiMod O K l e a ι) :
    P.L.restrictScalars O ⊓ MMHigh P = vL P l := by
  ext v
  simp only [Submodule.mem_inf, Submodule.restrictScalars_mem]
  constructor
  · rintro ⟨hL, hH⟩
    have hc : ∀ τ i, ∃ g ∈ A O K, (P.mxInv τ *ᵥ v τ) i = ((X : K⟦X⟧) ^ e) ^ l * g := fun τ i =>
      (hR.inter_eq _).1 ⟨P.mem_extc_iff.1 (mem_tot.1 hL τ) i,
        ⟨⟨_, P.mem_extc_iff.1 (mem_tot.1 (MMHigh_le_MM P hH) τ) i⟩,
          mem_SHigh.2 (coord_dvd_of_mem_MMHigh P hH τ i), rfl⟩⟩
    choose g hg hgv using fun p : ZMod a × ι => hc p.1 p.2
    refine mem_mulL.2 ⟨∑ i, (fun τ => g (τ, i)) • P.phi (bas i), Submodule.sum_mem _ fun i _ =>
      P.smul_tot_mem_ext (fun τ => hg (τ, i)) (P.phi_mem_L (P.bas_mem_M i)), ?_⟩
    conv_rhs => rw [P.eq_sum_phi_bas v]
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ext τ j
    simp only [Pi.smul_apply', Pi.smul_apply, smul_eq_mul]
    rw [hgv (τ, i), mul_assoc]
  · rintro h
    obtain ⟨y, hy, rfl⟩ := mem_mulL.1 h
    have h1 := P.L.smul_mem (⟨_, pow_mem (pow_mem HasU.X_mem e) l⟩ : A O K) hy
    have h2 := Submodule.smul_mem_smul (r := (⟨_, pow_mem (pow_mem HasU.X_mem e) l⟩ : S O K e))
      (mem_SHigh.2 (show (X : K⟦X⟧) ^ (l * e) ∣ (X ^ e) ^ l by rw [← pow_mul, mul_comm])) (L_le_MM P hy)
    rw [Subalgebra.smul_def] at h1 h2
    exact ⟨h1, h2⟩

end Top

section TopConn

variable [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero a] [NeZero e]

theorem conn_mem_MMHigh (hR : RingModHigh O K l e) (P : PhiMod O K l e a ι)
    (hMM : ∀ m ∈ P.MM, P.conn m ∈ P.MM) {v : Vec K a ι} (hv : v ∈ MMHigh P) :
    P.conn v ∈ MMHigh P := by
  change v ∈ SHigh O K l e • P.MM at hv
  change _ ∈ SHigh O K l e • P.MM
  refine Submodule.smul_induction_on (p := fun v => P.conn v ∈ SHigh O K l e • P.MM) hv ?_ ?_
  · intro s hs m hm
    obtain ⟨g, hg, hgN⟩ := hR.N_stable s hs
    have h1 : P.conn (s • m) = g • m + s • P.conn m := by
      simp only [Subalgebra.smul_def, P.conn_smul, hgN]
    rw [h1]
    exact add_mem (Submodule.smul_mem_smul hg hm) (Submodule.smul_mem_smul hs (hMM m hm))
  · intro x y hx hy
    rw [map_add]
    exact add_mem hx hy

theorem conn_mem_uL_sup (hR : RingModHigh O K l e) (P : PhiMod O K l e a ι)
    (hMM : ∀ m ∈ P.MM, P.conn m ∈ P.MM) (i : ℕ) {x : Vec K a ι} (hx : x ∈ uL P i ⊔ MMHigh P) :
    P.conn x ∈ uL P i ⊔ MMHigh P := by
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
  obtain ⟨y', hy', rfl⟩ := mem_mulL.1 hy
  obtain ⟨p, hp, q, hq, hpq⟩ := Submodule.mem_sup.1 (MM_le_sup hR P (hMM y' (L_le_MM P hy')))
  have h1 : P.conn ((X : K⟦X⟧) ^ i • y' + z) =
      (X : K⟦X⟧) ^ i • (i • y' + p) + ((X : K⟦X⟧) ^ i • q + P.conn z) := by
    rw [map_add, P.conn_smul, N_X_pow, ← hpq, mul_comm, mul_smul, Nat.cast_smul_eq_nsmul,
      smul_add, smul_add]
    abel
  rw [h1]
  exact Submodule.add_mem_sup (mem_mulL.2 ⟨_, add_mem (nsmul_mem hy' i) hp, rfl⟩)
    (add_mem (X_pow_smul_mem_MMHigh P i hq) (conn_mem_MMHigh hR P hMM hz))

theorem conn_graded_top (hR : RingModHigh O K l e) (P : PhiMod O K l e a ι)
    (hX : ∀ m ∈ P.MM, ∃ w ∈ P.MM, P.conn m = (X : K⟦X⟧) • w) (i : ℕ) {x : Vec K a ι}
    (hx : x ∈ uL P i) : P.conn x - i • x ∈ uL P (i + 1) ⊔ MMHigh P := by
  obtain ⟨y', hy', rfl⟩ := mem_mulL.1 hx
  obtain ⟨w, hw, hcw⟩ := hX y' (L_le_MM P hy')
  obtain ⟨p, hp, q, hq, hpq⟩ := Submodule.mem_sup.1 (MM_le_sup hR P hw)
  have h1 : P.conn ((X : K⟦X⟧) ^ i • y') - i • ((X : K⟦X⟧) ^ i • y') =
      (X : K⟦X⟧) ^ (i + 1) • p + (X : K⟦X⟧) ^ (i + 1) • q := by
    rw [P.conn_smul, N_X_pow, hcw, ← hpq, mul_smul, Nat.cast_smul_eq_nsmul, add_sub_cancel_left,
      ← mul_smul, ← pow_succ, smul_add]
  rw [h1]
  exact Submodule.add_mem_sup (mem_mulL.2 ⟨p, hp, rfl⟩) (X_pow_smul_mem_MMHigh P _ hq)

theorem modHigh_top (hR : RingModHigh O K l e) (P : PhiMod O K l e a ι)
    (hX : ∀ m ∈ P.MM, ∃ w ∈ P.MM, P.conn m = (X : K⟦X⟧) • w) : ModHigh P ⊤ := by
  have hMM : ∀ m ∈ P.MM, P.conn m ∈ P.MM := fun m hm => by
    obtain ⟨w, hw, h⟩ := hX m hm
    rw [h]
    exact P.MM.smul_mem (uIn (S O K e)) hw
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [part_top]
  · exact MM_eq_sup hR P
  · exact inter_eq_vL hR P
  · exact fun x hx => hMM x hx
  · exact fun x hx => conn_mem_MMHigh hR P hMM hx
  · exact fun i x hx => conn_mem_uL_sup hR P hMM i hx
  · exact fun i _ x hx => conn_graded_top hR P hX i hx

theorem app_mem_MMHigh {P : PhiMod O K l e a ι} {Q : PhiMod O K l e a κ} (F : Hom P Q)
    {v : Vec K a ι} (hv : v ∈ MMHigh P) : F.app v ∈ MMHigh Q := by
  change v ∈ SHigh O K l e • P.MM at hv
  change _ ∈ SHigh O K l e • Q.MM
  refine Submodule.smul_induction_on (p := fun v => F.app v ∈ SHigh O K l e • Q.MM) hv ?_ ?_
  · intro s hs m hm
    have h1 : F.app (s • m) = s • F.app m := by simp only [Subalgebra.smul_def, map_smul]
    rw [h1]
    exact Submodule.smul_mem_smul hs (F.app_mem_ext (A_le_S l e) hm)
  · intro x y hx hy
    rw [map_add]
    exact add_mem hx hy

theorem mem_imL {P : PhiMod O K l e a ι} {Q : PhiMod O K l e a κ} (F : Hom P Q) {y : Vec K a ι}
    (hy : y ∈ P.L) : F.app y ∈ F.imL.restrictScalars O :=
  (Submodule.restrictScalars_mem O _ _).2 (Submodule.mem_map.2 ⟨y, hy, rfl⟩)

theorem imageStable_top (hR : RingModHigh O K l e) {P : PhiMod O K l e a ι}
    {Q : PhiMod O K l e a κ} (F : Hom P Q) (hMM₁ : ∀ m ∈ P.MM, P.conn m ∈ P.MM)
    (hMM₂ : ∀ m ∈ Q.MM, Q.conn m ∈ Q.MM) : ImageStable F ⊤ := by
  intro x hx
  simp only [part_top] at hx ⊢
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
  obtain ⟨y', hy', hyy⟩ := Submodule.mem_map.1 ((Submodule.restrictScalars_mem O _ _).1 hy)
  simp only [LinearMap.coe_restrictScalars] at hyy
  subst hyy
  obtain ⟨p, hp, q, hq, hpq⟩ := Submodule.mem_sup.1 (MM_le_sup hR P (hMM₁ y' (L_le_MM P hy')))
  have h1 : Q.conn (F.app y' + z) = F.app p + (F.app q + Q.conn z) := by
    rw [map_add, ← F.app_conn, ← hpq, map_add, add_assoc]
  rw [h1]
  exact Submodule.add_mem_sup (mem_imL F hp)
    (add_mem (app_mem_MMHigh F hq) (conn_mem_MMHigh hR Q hMM₂ hz))

end TopConn

section Proj

theorem mem_part_sup {W : Submodule K (Vec K a ι)} (π : Vec K a ι →ₗ[K] Vec K a ι)
    (hπW : ∀ v, π v ∈ W) (hπ : ∀ v ∈ W, π v = v) {V₁ V₂ : Submodule O (Vec K a ι)}
    (h₁ : ∀ v ∈ V₁, π v ∈ V₁) (h₂ : ∀ v ∈ V₂, π v ∈ V₂) {x : Vec K a ι} (hx : x ∈ V₁ ⊔ V₂)
    (hxW : x ∈ W) : x ∈ part W V₁ ⊔ part W V₂ := by
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
  rw [← hπ _ hxW, map_add]
  exact Submodule.add_mem_sup (Submodule.mem_inf.2 ⟨h₁ y hy, hπW y⟩)
    (Submodule.mem_inf.2 ⟨h₂ z hz, hπW z⟩)

variable [Fact l.Prime]

theorem modHigh_of_proj {P : PhiMod O K l e a ι} {W : Submodule K (Vec K a ι)}
    (π : Vec K a ι →ₗ[K] Vec K a ι) (hπW : ∀ v, π v ∈ W) (hπ : ∀ v ∈ W, π v = v)
    (hL : ∀ v ∈ P.L, π v ∈ P.L) (hH : ∀ v ∈ MMHigh P, π v ∈ MMHigh P)
    (hu : ∀ i, ∀ v ∈ uL P i, π v ∈ uL P i) (hW : ∀ v ∈ W, P.conn v ∈ W) (h : ModHigh P ⊤) :
    ModHigh P W := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  simp only [part_top] at h1 h2 h3 h4 h5 h6
  refine ⟨le_antisymm ?_ ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨hx, hxW⟩ := Submodule.mem_inf.1 hx
    rw [h1] at hx
    exact mem_part_sup π hπW hπ hL hH hx hxW
  · refine sup_le (inf_le_inf_right _ ?_) (inf_le_inf_right _ ?_) <;> rw [h1]
    exacts [le_sup_left, le_sup_right]
  · rw [← h2]
    exact (inf_inf_distrib_right _ _ _).symm
  · intro x hx
    obtain ⟨hx, hxW⟩ := Submodule.mem_inf.1 hx
    exact Submodule.mem_inf.2 ⟨h3 x hx, hW x hxW⟩
  · intro x hx
    obtain ⟨hx, hxW⟩ := Submodule.mem_inf.1 hx
    exact Submodule.mem_inf.2 ⟨h4 x hx, hW x hxW⟩
  · intro i x hx
    have hxW : x ∈ W := (sup_le inf_le_right inf_le_right : part W (uL P i) ⊔ part W (MMHigh P) ≤
      W.restrictScalars O) hx
    have hx' := (sup_le_sup inf_le_left inf_le_left : part W (uL P i) ⊔ part W (MMHigh P) ≤
      uL P i ⊔ MMHigh P) hx
    exact mem_part_sup π hπW hπ (hu i) hH (h5 i x hx') (hW x hxW)
  · intro i hi x hx
    obtain ⟨hx, hxW⟩ := Submodule.mem_inf.1 hx
    exact mem_part_sup π hπW hπ (hu (i + 1)) hH (h6 i hi x hx)
      (sub_mem (hW x hxW) (nsmul_mem (show x ∈ W from hxW) i))

theorem imageStable_of_proj {P : PhiMod O K l e a ι} {Q : PhiMod O K l e a κ} (F : Hom P Q)
    {W : Submodule K (Vec K a κ)} (π : Vec K a κ →ₗ[K] Vec K a κ) (hπW : ∀ v, π v ∈ W)
    (hπ : ∀ v ∈ W, π v = v) (hI : ∀ v ∈ F.imL.restrictScalars O, π v ∈ F.imL.restrictScalars O)
    (hH : ∀ v ∈ MMHigh Q, π v ∈ MMHigh Q) (hW : ∀ v ∈ W, Q.conn v ∈ W) (h : ImageStable F ⊤) :
    ImageStable F W := by
  intro x hx
  have hxW : x ∈ W := (sup_le inf_le_right inf_le_right : part W (F.imL.restrictScalars O) ⊔
    part W (MMHigh Q) ≤ W.restrictScalars O) hx
  have hx' := (sup_le_sup inf_le_left inf_le_left : part W (F.imL.restrictScalars O) ⊔
    part W (MMHigh Q) ≤ F.imL.restrictScalars O ⊔ MMHigh Q) hx
  have h1 := h x (by simpa only [part_top] using hx')
  simp only [part_top] at h1
  exact mem_part_sup π hπW hπ hI hH h1 (hW x hxW)

end Proj

section Iso

variable [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a]

local instance : Fintype (rootsOfUnity e K) := Fintype.ofFinite _

theorem root_inertia_mul (ζ ξ : rootsOfUnity e K) (τ : ZMod a) :
    (TameGal.inertia (ζ * ξ) : TameGal K l e a).root τ =
      (TameGal.inertia ζ : TameGal K l e a).root τ * (TameGal.inertia ξ : TameGal K l e a).root τ := by
  simp [TameGal.root]

theorem root_inertia_one (τ : ZMod a) : (TameGal.inertia 1 : TameGal K l e a).root τ = 1 := by
  simp [TameGal.root]

theorem shift_inertia (ζ : rootsOfUnity e K) : (TameGal.inertia ζ : TameGal K l e a).shift = 0 := by
  simp [TameGal.shift]

theorem ringAct_inertia_C (ζ : rootsOfUnity e K) (k : ZMod a → K) :
    ringAct (TameGal.inertia ζ : TameGal K l e a) (fun τ => C (k τ)) = fun τ => C (k τ) := by
  funext τ
  rw [ringAct_apply, shift_inertia, sub_zero]
  ext n
  simp only [coeff_rescale, coeff_C]
  split_ifs with h
  · simp [h]
  · simp

omit [NeZero e] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero a] [TameDescentExponentData K l e a] in
theorem norm_e (l a : ℕ) [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero a] [TameDescentExponentData K l e a] :
    ‖(e : K)‖ = 1 := by
  rw [norm_natCast_eq l, Padic.norm_natCast_eq_one_iff]
  refine (Nat.Prime.coprime_iff_not_dvd Fact.out).2 fun h => ?_
  have h1 : l ∣ e + 1 := by
    rw [TameDescentExponentData.succ_eq K (l := l) (e := e) (a := a)]
    exact dvd_pow_self l (NeZero.ne a)
  exact (Fact.out : l.Prime).one_lt.ne' (Nat.dvd_one.1 ((Nat.dvd_add_right h).1 h1))

variable (l a) in

def isoCoef (c : ZMod e) (ζ : rootsOfUnity e K) : ZMod a → K⟦X⟧ :=
  fun τ => C ((e : K)⁻¹ * (TameGal.inertia ζ⁻¹ : TameGal K l e a).root τ ^ c.val)

theorem isoCoef_mem_A (c : ZMod e) (ζ : rootsOfUnity e K) (τ : ZMod a) :
    isoCoef l a c ζ τ ∈ A O K := by
  refine C_mem_A (le_of_eq ?_)
  rw [norm_mul, norm_inv, norm_e l a, norm_pow, TameGal.norm_root, one_pow, inv_one, one_mul]

theorem ringAct_isoCoef (c : ZMod e) (ζ ξ : rootsOfUnity e K) :
    ringAct (TameGal.inertia ξ : TameGal K l e a) (isoCoef l a c ζ) = isoCoef l a c ζ :=
  ringAct_inertia_C ξ _

def isoProj {P : PhiMod O K l e a ι} (Δ : Descent P) (c : ZMod e) : Vec K a ι →ₗ[K] Vec K a ι where
  toFun v := ∑ ζ : rootsOfUnity e K, isoCoef l a c ζ • Δ.act (TameGal.inertia ζ) v
  map_add' v w := by simp only [map_add, smul_add, Finset.sum_add_distrib]
  map_smul' r v := by
    simp only [map_smul, Finset.smul_sum, RingHom.id_apply]
    refine Finset.sum_congr rfl fun ζ _ => ?_
    funext τ
    simp only [Pi.smul_apply', Pi.smul_apply]
    exact smul_comm _ _ _

theorem isoProj_def {P : PhiMod O K l e a ι} (Δ : Descent P) (c : ZMod e) (v : Vec K a ι) :
    isoProj Δ c v = ∑ ζ : rootsOfUnity e K, isoCoef l a c ζ • Δ.act (TameGal.inertia ζ) v := rfl

theorem isoProj_mem {P : PhiMod O K l e a ι} (Δ : Descent P) (c : ZMod e) (v : Vec K a ι) :
    isoProj Δ c v ∈ Δ.isotypic c := by
  intro ξ τ
  have h1 : Δ.act (TameGal.inertia ξ) (isoProj Δ c v) =
      ∑ ζ, isoCoef l a c (ξ⁻¹ * ζ) • Δ.act (TameGal.inertia ζ) v := by
    rw [isoProj_def, map_sum]
    refine Fintype.sum_equiv (Equiv.mulLeft ξ) _ _ fun ζ => ?_
    rw [Δ.act_smul_tot, ringAct_isoCoef, Equiv.coe_mulLeft, inv_mul_cancel_left]
    simp only [map_mul, Module.End.mul_apply]
  rw [h1, isoProj_def, Finset.sum_apply, Finset.sum_apply, Finset.smul_sum]
  refine Finset.sum_congr rfl fun ζ _ => ?_
  funext i
  simp only [Pi.smul_apply', Pi.smul_apply, isoCoef, smul_eq_mul, smul_eq_C_mul]
  rw [_root_.mul_inv_rev, inv_inv, root_inertia_mul, mul_pow]
  simp only [map_mul, map_pow]
  ring

omit [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero a] [TameDescentExponentData K l e a] in
theorem card_roots (l a : ℕ) [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero a] [TameDescentExponentData K l e a] :
    Nat.card (rootsOfUnity e K) = e := by
  obtain ⟨ζ, hζ⟩ := TameDescentExponentData.prim (K := K) (l := l) (e := e) (a := a)
  exact hζ.card_rootsOfUnity

theorem isoProj_of_mem {P : PhiMod O K l e a ι} (Δ : Descent P) (c : ZMod e) {v : Vec K a ι}
    (hv : v ∈ Δ.isotypic c) : isoProj Δ c v = v := by
  funext τ i
  rw [isoProj_def, Finset.sum_apply, Finset.sum_apply]
  have h1 : ∀ ζ : rootsOfUnity e K, (isoCoef l a c ζ • Δ.act (TameGal.inertia ζ) v) τ i =
      C ((e : K)⁻¹) * v τ i := by
    intro ζ
    rw [Pi.smul_apply', hv ζ τ]
    simp only [Pi.smul_apply, isoCoef, smul_eq_mul, smul_eq_C_mul]
    rw [← mul_assoc, ← map_mul, mul_assoc, ← mul_pow, ← root_inertia_mul, inv_mul_cancel,
      root_inertia_one, one_pow, mul_one]
  have he : (e : K) ≠ 0 := norm_ne_zero_iff.1 (by rw [norm_e l a]; exact one_ne_zero)
  simp only [h1, Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card, card_roots l a, nsmul_eq_mul]
  rw [← mul_assoc, ← map_natCast (C (R := K)), ← map_mul, mul_inv_cancel₀ he, map_one, one_mul]

end Iso

section IsoStable

variable [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a]

local instance : Fintype (rootsOfUnity e K) := Fintype.ofFinite _

theorem smulTot_mem_MMHigh (P : PhiMod O K l e a ι) {f : ZMod a → K⟦X⟧} (hf : ∀ τ, f τ ∈ A O K)
    {v : Vec K a ι} (hv : v ∈ MMHigh P) : f • v ∈ MMHigh P := by
  change v ∈ SHigh O K l e • P.MM at hv
  change _ ∈ SHigh O K l e • P.MM
  refine Submodule.smul_induction_on (p := fun v => f • v ∈ SHigh O K l e • P.MM) hv ?_ ?_
  · intro s hs m hm
    have h1 : f • (s • m) = s • (f • m) := by
      funext τ i
      simp only [Pi.smul_apply', Pi.smul_apply, Subalgebra.smul_def, smul_eq_mul]
      ring
    rw [h1]
    exact Submodule.smul_mem_smul hs (P.smul_tot_mem_ext (fun τ => A_le_S l e (hf τ)) hm)
  · intro x y hx hy
    rw [smul_add]
    exact add_mem hx hy

theorem act_mem_MMHigh {P : PhiMod O K l e a ι} (Δ : Descent P) (g : TameGal K l e a)
    {v : Vec K a ι} (hv : v ∈ MMHigh P) : Δ.act g v ∈ MMHigh P := by
  change v ∈ SHigh O K l e • P.MM at hv
  refine Submodule.smul_induction_on (p := fun v => Δ.act g v ∈ MMHigh P) hv ?_ ?_
  · intro s hs m hm
    have h0 : (s • m : Vec K a ι) = (fun _ : ZMod a => (s : K⟦X⟧)) • m := by
      funext τ i
      rfl
    rw [h0, Δ.act_smul_tot]
    refine smul_mem_MMHigh P (fun τ => ⟨rot_S.ringAct_mem g (fun _ => s.2) τ, ?_⟩)
      (Δ.act_mem_ext g (A_le_S l e) rot_S hm)
    show (X : K⟦X⟧) ^ (l * e) ∣ rescale (g.root τ) (s : K⟦X⟧)
    obtain ⟨t, ht⟩ := mem_SHigh.1 hs
    rw [ht, map_mul, map_pow, rescale_X, mul_pow]
    exact Dvd.dvd.mul_right (dvd_mul_left _ _) _
  · intro x y hx hy
    rw [map_add]
    exact add_mem hx hy

theorem act_mem_uL {P : PhiMod O K l e a ι} (Δ : Descent P) (g : TameGal K l e a) (i : ℕ)
    {v : Vec K a ι} (hv : v ∈ uL P i) : Δ.act g v ∈ uL P i := by
  obtain ⟨y, hy, rfl⟩ := mem_mulL.1 hv
  have h1 : Δ.act g ((X : K⟦X⟧) ^ i • y) =
      (X : K⟦X⟧) ^ i • ((fun τ => C (g.root τ ^ i)) • Δ.act g y) := by
    have h0 : ((X : K⟦X⟧) ^ i • y : Vec K a ι) = (fun _ : ZMod a => (X : K⟦X⟧) ^ i) • y := by
      funext τ j
      rfl
    rw [h0, Δ.act_smul_tot]
    funext τ j
    simp only [Pi.smul_apply', Pi.smul_apply, ringAct_apply, smul_eq_mul, map_pow, rescale_X, mul_pow]
    ring
  rw [h1]
  refine mem_mulL.2 ⟨_, P.smul_tot_mem_ext (fun τ => C_mem_A (le_of_eq ?_))
    (Δ.act_mem_ext g le_rfl rot_A hy), rfl⟩
  rw [norm_pow, TameGal.norm_root, one_pow]

theorem smulTot_mem_uL (P : PhiMod O K l e a ι) {f : ZMod a → K⟦X⟧} (hf : ∀ τ, f τ ∈ A O K)
    (i : ℕ) {v : Vec K a ι} (hv : v ∈ uL P i) : f • v ∈ uL P i := by
  obtain ⟨y, hy, rfl⟩ := mem_mulL.1 hv
  refine mem_mulL.2 ⟨f • y, P.smul_tot_mem_ext hf hy, ?_⟩
  funext τ j
  simp only [Pi.smul_apply', Pi.smul_apply, smul_eq_mul]
  ring

theorem isoProj_mem_L {P : PhiMod O K l e a ι} (Δ : Descent P) (c : ZMod e) {v : Vec K a ι}
    (hv : v ∈ P.L) : isoProj Δ c v ∈ P.L :=
  Submodule.sum_mem _ fun ζ _ =>
    P.smul_tot_mem_ext (isoCoef_mem_A c ζ) (Δ.act_mem_ext _ le_rfl rot_A hv)

theorem isoProj_mem_MMHigh {P : PhiMod O K l e a ι} (Δ : Descent P) (c : ZMod e)
    {v : Vec K a ι} (hv : v ∈ MMHigh P) : isoProj Δ c v ∈ MMHigh P :=
  Submodule.sum_mem _ fun ζ _ => smulTot_mem_MMHigh P (isoCoef_mem_A c ζ) (act_mem_MMHigh Δ _ hv)

theorem isoProj_mem_uL {P : PhiMod O K l e a ι} (Δ : Descent P) (c : ZMod e) (i : ℕ)
    {v : Vec K a ι} (hv : v ∈ uL P i) : isoProj Δ c v ∈ uL P i :=
  Submodule.sum_mem _ fun ζ _ => smulTot_mem_uL P (isoCoef_mem_A c ζ) i (act_mem_uL Δ _ i hv)

theorem isoProj_app {P : PhiMod O K l e a ι} {Q : PhiMod O K l e a κ} {Δ₁ : Descent P}
    {Δ₂ : Descent Q} (F : Descent.Hom Δ₁ Δ₂) (c : ZMod e) (y : Vec K a ι) :
    isoProj Δ₂ c (F.app y) = F.app (isoProj Δ₁ c y) := by
  simp only [isoProj_def, map_sum, BK.Hom.app_smul_tot, F.app_act]

theorem conn_mem_isotypic {P : PhiMod O K l e a ι} (Δ : Descent P) (c : ZMod e) {v : Vec K a ι}
    (hv : v ∈ Δ.isotypic c) : P.conn v ∈ Δ.isotypic c := by
  intro ζ τ
  have h1 : Δ.act (TameGal.inertia ζ) v =
      (fun τ => C ((TameGal.inertia ζ : TameGal K l e a).root τ ^ c.val)) • v := by
    funext τ' j
    rw [hv ζ τ']
    simp [smul_eq_C_mul]
  have h2 : NTot (fun τ => C ((TameGal.inertia ζ : TameGal K l e a).root τ ^ c.val)) = 0 := by
    funext τ'
    simp [NTot, N_apply]
  rw [Δ.act_conn, h1, P.conn_smul_tot, h2, zero_smul, zero_add]
  funext j
  simp [smul_eq_C_mul]

end IsoStable

section Main

variable [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a]
  {η H : ℕ}

theorem modHigh_top_dat (hR : RingModHigh O K l e) (D : BKDat O K l e a ι η H) :
    ModHigh D.toPhiMod ⊤ :=
  modHigh_top hR D.toPhiMod fun _ hm => D.exists_conn_eq hm

theorem modHigh_isotypic (hR : RingModHigh O K l e) (D : BKDat O K l e a ι η H) (c : ZMod e) :
    ModHigh D.toPhiMod (D.desc.isotypic c) :=
  modHigh_of_proj (isoProj D.desc c) (isoProj_mem D.desc c) (fun _ hv => isoProj_of_mem D.desc c hv)
    (fun _ hv => isoProj_mem_L D.desc c hv) (fun _ hv => isoProj_mem_MMHigh D.desc c hv)
    (fun i _ hv => isoProj_mem_uL D.desc c i hv) (fun _ hv => conn_mem_isotypic D.desc c hv)
    (modHigh_top_dat hR D)

theorem imageStable_top_hom (hR : RingModHigh O K l e) {B₁ : BKDat O K l e a ι η H}
    {B₂ : BKDat O K l e a κ η H} (F : BKHom B₁ B₂) : ImageStable F.toHom ⊤ :=
  imageStable_top hR F.toHom (fun _ hm => B₁.conn_mem_MM hm) (fun _ hm => B₂.conn_mem_MM hm)

theorem imageStable_isotypic (hR : RingModHigh O K l e) {B₁ : BKDat O K l e a ι η H}
    {B₂ : BKDat O K l e a κ η H} (F : BKHom B₁ B₂) (c : ZMod e) :
    ImageStable F.toHom (B₂.desc.isotypic c) := by
  refine imageStable_of_proj F.toHom (isoProj B₂.desc c) (isoProj_mem _ c)
    (fun _ hv => isoProj_of_mem _ c hv) (fun v hv => ?_) (fun _ hv => isoProj_mem_MMHigh _ c hv)
    (fun _ hv => conn_mem_isotypic _ c hv) (imageStable_top_hom hR F)
  obtain ⟨y, hy, hyv⟩ := Submodule.mem_map.1 ((Submodule.restrictScalars_mem O _ _).1 hv)
  simp only [LinearMap.coe_restrictScalars] at hyv
  subst hyv
  rw [isoProj_app F c y]
  exact mem_imL F.toHom (isoProj_mem_L B₁.desc c hy)

end Main

theorem reduction : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    [Algebra O K] [IsUnitBall O K] (l e a : ℕ) [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e]
    [NeZero a] [TameDescentExponentData K l e a], GlobalTheory.IndefiniteRowSideFullHecke.ImageStableDegreeBounds.Reduction O K l e a := by
  intro O K _ _ _ _ _ _ l e a _ _ _ _ _
  have hR : RingModHigh O K l e := GlobalTheory.T.breuilRing_mod_high_degree_property O K l e a
  refine ⟨hR, fun ι _ _ η H D => ⟨modHigh_top_dat hR D, fun ζ x => D.desc.act_conn _ x,
    fun c => modHigh_isotypic hR D c⟩, fun ι κ _ _ _ _ η H B₁ B₂ F => ⟨fun x hx =>
      ⟨F.app_mem_ext (A_le_S l e) hx, F.app_conn x⟩, imageStable_top_hom hR F,
      fun c => imageStable_isotypic hR F c⟩⟩

end GlobalTheory.NModHigh
