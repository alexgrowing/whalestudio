import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EntryAgree
import Formalism.LocalToGlobal.Columns.ChainTw
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjSymmEntry
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemStabLIff
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ResiduesOfCompletionAtPrimeWithUniformizer
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ToLocEqMapToMatrix
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymmetricChainSupportOneOfPattern

open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.TwBridge
open GlobalTheory.SymBridge (toLoc IsOrd yPos xPos IsCompl)
open GlobalTheory.SymSupport (InR mem_R_of_inR)

noncomputable section
namespace GlobalTheory.TwBridge.Lev

section Plain
variable {k : Type} [Field k] {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}

theorem inR_mul {g h : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k} (hg : InR g) (hh : InR h) : InR (g * h) := by
  refine ⟨fun l s => ?_, fun r i hl => ?_⟩
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero ?_
    rintro (m | m) -
    · rw [hg.1, zero_mul]
    · rw [hh.1, mul_zero]
  · rw [Matrix.mul_apply, Finset.sum_eq_single (Sum.inr i)]
    · rw [hh.2 _ i le_rfl, Matrix.one_apply_eq, mul_one, hg.2 r i hl]
    · rintro (m | m) - hm
      · rcases r with r | r
        · rw [hh.2 (.inl m) i hl, Matrix.one_apply_ne hm, mul_zero]
        · rw [hg.1, zero_mul]
      · by_cases hmi : i.val ≤ m.val
        · rw [hh.2 (.inr m) i (by simpa [RootEx.lev] using hmi), Matrix.one_apply_ne hm, mul_zero]
        · have h1 : RootEx.lev 1 (Sum.inr m : n ⊕ Fin c) < RootEx.lev 1 r := lt_of_lt_of_le (by simp only [RootEx.lev, Sum.elim_inr]; omega) hl
          rw [hg.2 r m h1.le, Matrix.one_apply_ne (by rintro rfl; exact lt_irrefl _ h1), zero_mul]
    · simp

theorem inR_embX (γ : GL n k) : InR (embX c γ).val := by
  change InR (fromBlocks γ.val 0 0 1)
  refine ⟨fun l s => rfl, ?_⟩
  rintro (r | r) i -
  · simp
  · simp [Matrix.one_apply]

theorem inR_of_inN {g : GL (n ⊕ Fin c) k} (h : InN 1 g) : InR g.val :=
  ⟨fun l s => by rw [h _ _ (by simp [RootEx.lev])]; simp, fun r i hl => h _ _ hl⟩

theorem inR_of_mem_R {g : GL (n ⊕ Fin c) k} (h : g ∈ GlobalTheory.RootEx.R k n c 1) : InR g.val := by
  let S : Subgroup (GL (n ⊕ Fin c) k) :=
    { carrier := {g | InR g.val ∧ InR (g⁻¹).val}
      one_mem' := by
        have : InR (1 : GL (n ⊕ Fin c) k).val := by simpa using inR_embX (c := c) (1 : GL n k)
        exact ⟨this, by rwa [inv_one]⟩
      mul_mem' := fun {a b} ha hb => ⟨inR_mul ha.1 hb.1, by rw [_root_.mul_inv_rev]; exact inR_mul hb.2 ha.2⟩
      inv_mem' := fun {a} ha => ⟨ha.2, by rw [inv_inv]; exact ha.1⟩ }
  have : GlobalTheory.RootEx.R k n c 1 ≤ S := by
    refine sup_le ?_ fun u hu => ⟨inR_of_inN (Model.mem_N_iff.1 hu), inR_of_inN (Model.mem_N_iff.1 (inv_mem hu))⟩
    rintro _ ⟨γ, rfl⟩
    exact ⟨inR_embX γ, by rw [← map_inv]; exact inR_embX _⟩
  exact (this h).1

end Plain

section Rat
variable {E k : Type} [Field E] [Field k] (ι : E →+* k)

theorem apply_sum {N : ℕ} (φ : (Fin N → E) ≃ₗ[E] (Fin N → E)) (v : Fin N → E) (l : Fin N) :
    φ v l = ∑ l' : Fin N, φ (Pi.single l' 1) l * v l' := by
  have hv : v = ∑ l' : Fin N, v l' • (Pi.single l' (1 : E) : Fin N → E) := by
    funext i
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hv]
  rw [map_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun l' _ => ?_
  rw [map_smul, Pi.smul_apply, smul_eq_mul, mul_comm]

theorem eN_eq {N : ℕ} (u : Fin N) : Loc.eN E N u.val = Pi.single u 1 := by
  funext l; simp [Loc.eN, Pi.single_apply, Fin.ext_iff]

theorem eN_eq_zero {N i : ℕ} (h : N ≤ i) : Loc.eN E N i = 0 := by
  funext l
  have := l.2
  simp only [Loc.eN, Pi.zero_apply]
  rw [if_neg (by omega)]

theorem r1cond_iff {n c : ℕ} (γ : (Fin (n + c) → E) ≃ₗ[E] (Fin (n + c) → E)) :
    Loc.R1cond E n c γ ↔ ∀ l l' : Fin (n + c), ((n ≤ l.val ∧ l'.val ≤ l.val) ∨ l'.val = n) →
      γ (Pi.single l' 1) l = if l = l' then 1 else 0 := by
  constructor
  · rintro ⟨h1, h2, h3⟩ l l' h
    rcases h with ⟨ha, hb⟩ | ha
    · by_cases hl : l'.val < n
      · rw [if_neg (by rintro rfl; omega)]
        refine h1 0 (Pi.single l' 1) (fun m hm => ?_) l (by simpa using ha)
        rw [Pi.single_eq_of_ne]
        rintro rfl
        exact hm (by simpa using hl)
      · obtain ⟨i, hi⟩ : ∃ i, l'.val = n + i := ⟨l'.val - n, by omega⟩
        have := h3 i l (by simp only [Set.mem_setOf_eq]; omega)
        rw [← hi, eN_eq, Pi.sub_apply, sub_eq_zero] at this
        rw [this, Pi.single_apply]
    · rw [show Loc.eN E (n + c) n = Pi.single l' 1 from by rw [← eN_eq, ha]] at h2
      rw [h2, Pi.single_apply]
  · intro h
    refine ⟨fun i v hv l hl => ?_, ?_, fun i l hl => ?_⟩
    · rw [apply_sum]
      refine Finset.sum_eq_zero fun l' _ => ?_
      simp only [Set.mem_setOf_eq] at hl
      by_cases h' : l'.val < n + i
      · rw [h l l' (Or.inl ⟨by omega, by omega⟩), if_neg (by rintro rfl; omega), zero_mul]
      · rw [hv l' h', mul_zero]
    · by_cases hn : n < n + c
      · have := eN_eq (E := E) (⟨n, hn⟩ : Fin (n + c))
        rw [show Loc.eN E (n + c) n = _ from this]
        funext l
        rw [h l _ (Or.inr rfl), Pi.single_apply]
      · rw [eN_eq_zero (by omega), map_zero]
    · simp only [Set.mem_setOf_eq] at hl
      have hn : n + i < n + c := by have := l.2; omega
      have := eN_eq (E := E) (⟨n + i, hn⟩ : Fin (n + c))
      rw [show Loc.eN E (n + c) (n + i) = _ from this, Pi.sub_apply, h l _ (Or.inl ⟨by omega, by simp only; omega⟩),
        Pi.single_apply, sub_self]

variable {A : Type} [Fintype A] [DecidableEq A] {n c : ℕ} {pos : A → ℕ}

theorem r1cond_iff_inR (hpos : ∀ a, pos a < n) {e : A ⊕ Fin c ≃ Fin (n + c)} (he : IsOrd (yPos pos n) e)
    (γ : (Fin (n + c) → E) ≃ₗ[E] (Fin (n + c) → E)) : Loc.R1cond E n c γ ↔ InR (toLoc ι e e γ.toLinearMap) := by
  have h1 : ∀ a, (e (.inl a)).val < n := fun a => by rw [he]; exact hpos a
  have h2 : ∀ i, (e (.inr i)).val = n + i.val := fun i => he _
  have key : ∀ a b, toLoc ι e e γ.toLinearMap a b = (1 : Matrix _ _ k) a b ↔
      γ (Pi.single (e b) 1) (e a) = if e a = e b then 1 else 0 := fun a b => by
    rw [← ι.injective.eq_iff, Matrix.one_apply]
    simp [toLoc, apply_ite ι]
  rw [r1cond_iff]
  constructor
  · intro h
    refine ⟨fun l s => ?_, fun r i hl => (key _ _).2 (h _ _ ?_)⟩
    · have := h1 s
      have := h2 l
      rw [(key _ _).2 (h _ _ (Or.inl ⟨by omega, by omega⟩))]
      simp
    · have := h2 i
      rcases r with r | r
      · simp only [RootEx.lev, Sum.elim_inl, Sum.elim_inr] at hl
        right; omega
      · simp only [RootEx.lev, Sum.elim_inr] at hl
        have := h2 r
        left; omega
  · intro h l l' hl
    obtain ⟨a, rfl⟩ := e.surjective l
    obtain ⟨b, rfl⟩ := e.surjective l'
    refine (key _ _).1 ?_
    rcases b with b | i
    · have := h1 b
      rcases a with a | a
      · have := h1 a; omega
      · rw [h.1]; simp
    · refine h.2 a i ?_
      have := h2 i
      rcases a with a | a
      · have := h1 a
        simp only [RootEx.lev, Sum.elim_inl, Sum.elim_inr]; omega
      · have := h2 a
        simp only [RootEx.lev, Sum.elim_inr]; omega

def phi {B : Type} [Fintype B] [DecidableEq B] {N : ℕ} (e : B ≃ Fin N) : ((Fin N → E) ≃ₗ[E] (Fin N → E)) →* GL B k :=
  MonoidHom.toHomUnits
    { toFun := fun γ => toLoc ι e e γ.toLinearMap
      map_one' := GlobalTheory.SymBridge.toLoc_id_square ι e
      map_mul' := fun a b => GlobalTheory.SymBridge.toLoc_comp_square ι e a.toLinearMap b.toLinearMap }

theorem phi_val {B : Type} [Fintype B] [DecidableEq B] {N : ℕ} (e : B ≃ Fin N) (γ : (Fin N → E) ≃ₗ[E] (Fin N → E)) :
    (phi ι e γ).val = toLoc ι e e γ.toLinearMap := rfl

theorem mem_rationalFirstParabolic_iff_localGL_mem_rootExchange (hpos : ∀ a, pos a < n) {e : A ⊕ Fin c ≃ Fin (n + c)} (he : IsOrd (yPos pos n) e)
    (γ : (Fin (n + c) → E) ≃ₗ[E] (Fin (n + c) → E)) : γ ∈ Loc.R1 E n c ↔ phi ι e γ ∈ GlobalTheory.RootEx.R k A c 1 := by
  refine ⟨fun h => mem_R_of_inR ((r1cond_iff_inR ι hpos he γ).1 h.1), fun h => ⟨(r1cond_iff_inR ι hpos he γ).2 (inR_of_mem_R h),
    (r1cond_iff_inR ι hpos he γ⁻¹).2 ?_⟩⟩
  have := inR_of_mem_R (inv_mem h)
  rwa [← map_inv] at this

theorem exists_phi {B : Type} [Fintype B] [DecidableEq B] {N : ℕ} (e : B ≃ Fin N) (M : Matrix B B E) (u : GL B k)
    (hu : u.val = M.map ι) : ∃ γ, phi ι e γ = u := by
  have hd : (M.submatrix e.symm e.symm).det ≠ 0 := by
    rw [det_submatrix_equiv_self]
    intro h
    have := u.det_ne_zero
    rw [hu, ← RingHom.mapMatrix_apply, ← RingHom.map_det, h, map_zero] at this
    exact this rfl
  refine ⟨Matrix.toLinearEquiv' _ (invertibleOfIsUnitDet _ (Ne.isUnit hd)), Units.ext ?_⟩
  rw [hu, phi_val]
  ext a b
  simp only [toLoc, Matrix.toLinearEquiv'_apply, Matrix.toLin'_apply, mulVec_single_one, Matrix.map_apply]
  simp

end Rat

section Dense
variable {E k : Type} [Field E] [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : E →+* k)
  {B : Type} [Fintype B] [DecidableEq B]

theorem exists_approx (hι : DenseRange ι) (M : Matrix B B k) {U : Set (Matrix B B k)} (hU : IsOpen U) (hM : M ∈ U) :
    ∃ M₀ : Matrix B B E, M₀.map ι ∈ U ∧ ∀ a b, M a b = (1 : Matrix B B k) a b → M₀.map ι a b = (1 : Matrix B B k) a b := by
  classical
  let T : (B × B → k) → Matrix B B k := fun x => Matrix.of fun a b =>
    if M a b = (1 : Matrix B B k) a b then (1 : Matrix B B k) a b else x (a, b)
  have hT : Continuous T := by
    refine continuous_pi fun a => continuous_pi fun b => ?_
    simp only [T, Matrix.of_apply]
    split_ifs
    · exact continuous_const
    · exact continuous_apply _
  have hd : DenseRange (Pi.map fun _ : B × B => (ι : E → k)) := DenseRange.piMap fun _ => hι
  obtain ⟨x, hx⟩ := hd.exists_mem_open (hU.preimage hT) ⟨fun p => M p.1 p.2, by
    have : T (fun p => M p.1 p.2) = M := by
      ext a b
      simp only [T, Matrix.of_apply]
      split_ifs with h
      · exact h.symm
      · rfl
    rwa [Set.mem_preimage, this]⟩
  have e : (Matrix.of fun a b => if M a b = (1 : Matrix B B k) a b then (1 : Matrix B B E) a b else x (a, b)).map ι =
      T (Pi.map (fun _ : B × B => (ι : E → k)) x) := by
    ext a b
    simp only [T, Matrix.of_apply, Matrix.map_apply, Pi.map_apply]
    split_ifs
    · simp [Matrix.one_apply, apply_ite ι]
    · rfl
  refine ⟨_, by rw [e]; exact hx, fun a b h => ?_⟩
  rw [e]
  exact if_pos h

theorem dc_iff (hι : DenseRange ι) {A : Type} [Fintype A] [DecidableEq A] {n c : ℕ} {pos : A → ℕ} (hpos : ∀ a, pos a < n)
    {e : A ⊕ Fin c ≃ Fin (n + c)} (he : IsOrd (yPos pos n) e) (J : Subgroup (GL (A ⊕ Fin c) k)) (hJ : KOne k _ ≤ J)
    (J₀ : Subgroup ((Fin (n + c) → E) ≃ₗ[E] (Fin (n + c) → E))) (hJ₀ : ∀ γ, phi ι e γ ∈ J ↔ γ ∈ J₀)
    (γ γ' : (Fin (n + c) → E) ≃ₗ[E] (Fin (n + c) → E)) :
    (∃ r ∈ Loc.R1 E n c, ∃ κ ∈ J₀, γ' = r * γ * κ) ↔ DoubleCoset.mk (GlobalTheory.RootEx.R k A c 1) J (phi ι e γ) =
      DoubleCoset.mk (GlobalTheory.RootEx.R k A c 1) J (phi ι e γ') := by
  rw [DoubleCoset.eq]
  constructor
  · rintro ⟨r, hr, κ, hκ, rfl⟩
    exact ⟨_, (mem_rationalFirstParabolic_iff_localGL_mem_rootExchange ι hpos he r).1 hr, _, (hJ₀ κ).2 hκ, by rw [map_mul, map_mul]⟩
  · rintro ⟨r, hr, κ, hκ, h⟩
    set g := phi ι e γ with hg
    have hU : IsOpen {M : Matrix (A ⊕ Fin c) (A ⊕ Fin c) k | MaxM ((g⁻¹).val * M * (r * g).val - 1)} := by
      simp only [MaxM, Set.setOf_forall]
      refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_
      exact IsOpen.preimage (f := fun M : Matrix (A ⊕ Fin c) (A ⊕ Fin c) k => ((g⁻¹).val * M * (r * g).val - 1) i j)
        (t := {z | valuation k z < 1}) (by fun_prop) (by simpa using (valuation k).isOpen_ball 1)
    obtain ⟨M₀, h1, h2⟩ := exists_approx ι hι (r⁻¹).val hU (by
      change MaxM _
      rw [← Units.val_mul, ← Units.val_mul, show g⁻¹ * r⁻¹ * (r * g) = 1 by group, Units.val_one, sub_self]
      exact maxM_zero)
    obtain ⟨u, hu, eu⟩ := exists_mem_KOne h1
    have ev : (g * u * (r * g)⁻¹).val = M₀.map ι := by
      rw [Units.val_mul, Units.val_mul, eu, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul,
        Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
    obtain ⟨ρ, hρ⟩ := exists_phi ι e M₀ _ ev
    have hi := inR_of_mem_R (inv_mem hr)
    have hρR : ρ ∈ Loc.R1 E n c := by
      rw [mem_rationalFirstParabolic_iff_localGL_mem_rootExchange ι hpos he, hρ]
      refine mem_R_of_inR ?_
      rw [ev]
      exact ⟨fun l s => by rw [h2 _ _ (by rw [hi.1]; simp)]; simp, fun a i hl => h2 _ _ (hi.2 a i hl)⟩
    refine ⟨ρ⁻¹, inv_mem hρR, γ⁻¹ * ρ * γ', (hJ₀ _).1 ?_, by group⟩
    rw [map_mul, map_mul, map_inv, hρ, h, ← hg, show g⁻¹ * (g * u * (r * g)⁻¹) * (r * g * κ) = u * κ by group]
    exact mul_mem (hJ hu) hκ

end Dense

section Lat
variable {E : Type} [Field E] [NumberField E] {P : HeightOneSpectrum (𝓞 E)} {q : ℕ}

theorem map_sclLat_iff (hq0 : (q : E) ≠ 0) {N : ℕ} (ex : ℕ → ℤ) (κ : Sp E N ≃ₗ[E] Sp E N) :
    (∀ v ∈ LocE.sclLat P q N ex, κ v ∈ LocE.sclLat P q N ex) ↔
      ∀ l l' : Fin N, IntAt P (κ (Pi.single l' 1) l * (q : E) ^ (ex l'.1 - ex l.1)) := by
  constructor
  · intro h l l'
    have h1 := h (((q : E) ^ ex l'.1) • (Pi.single l' (1 : E) : Sp E N)) (by
      rw [StabRef.mem_sclLat]
      intro l
      rw [Pi.smul_apply, smul_eq_mul]
      by_cases h : l = l'
      · subst h
        rw [Pi.single_eq_same, mul_one, inv_mul_cancel₀ (zpow_ne_zero _ hq0)]
        simpa using IntAt.coe P 1
      · rw [Pi.single_eq_of_ne h, mul_zero, mul_zero]
        exact StabRef.intAt_zero)
    have h2 := (StabRef.mem_sclLat _ _).1 h1 l
    rw [map_smul, Pi.smul_apply, smul_eq_mul] at h2
    convert h2 using 1
    rw [zpow_sub₀ hq0]
    ring
  · intro hκ v hv
    rw [StabRef.mem_sclLat] at hv ⊢
    intro l
    rw [apply_sum κ v l, Finset.mul_sum]
    refine StabRef.intAt_sum _ _ fun l' _ => ?_
    convert (hκ l l').mul (hv l') using 1
    rw [zpow_sub₀ hq0]
    have h1 : (q : E) ^ ex l'.1 ≠ 0 := zpow_ne_zero _ hq0
    field_simp

theorem mem_stabL_iff {N : ℕ} (L : Submodule (𝓞 E) (Sp E N)) (κ : Sp E N ≃ₗ[E] Sp E N) :
    κ ∈ stabL E N L ↔ (∀ v ∈ L, κ v ∈ L) ∧ ∀ v ∈ L, κ⁻¹ v ∈ L := by
  refine ⟨fun h => ⟨fun v hv => (h v).2 hv, fun v hv => ((inv_mem h : κ⁻¹ ∈ stabL E N L) v).2 hv⟩, fun h v => ⟨fun hv => ?_, h.1 v⟩⟩
  have := h.2 _ hv
  rwa [show κ⁻¹ (κ v) = v from LinearEquiv.symm_apply_apply κ v] at this

theorem stdAt_eq (N : ℕ) : stdAt E N P = LocE.sclLat P q N 0 := by
  ext v
  rw [StabRef.mem_sclLat, stdAt, StabRef.mem_locStd]
  simp

variable (P q) in

def Par (kj n c : ℕ) (κ : Sp E (n + c) ≃ₗ[E] Sp E (n + c)) : Prop :=
  (∀ l l', IntAt P (κ (Pi.single l' 1) l)) ∧ ∀ l l' : Fin (n + c), (kj ≤ l.1 ∧ l.1 < n) → ¬ (kj ≤ l'.1 ∧ l'.1 < n) →
    IntAt P (κ (Pi.single l' 1) l / (q : E))

theorem par_iff (hq0 : (q : E) ≠ 0) (kj n c : ℕ) (κ : Sp E (n + c) ≃ₗ[E] Sp E (n + c)) :
    Par P q kj n c κ ↔ (∀ v ∈ stdAt E (n + c) P, κ v ∈ stdAt E (n + c) P) ∧
      ∀ v ∈ LocE.parL P q kj n c, κ v ∈ LocE.parL P q kj n c := by
  rw [stdAt_eq (q := q), LocE.parL, map_sclLat_iff hq0, map_sclLat_iff hq0, Par]
  simp only [Pi.zero_apply, sub_self, zpow_zero, mul_one]
  refine and_congr_right fun h => ⟨fun h' l l' => ?_, fun h' l l' h1 h2 => ?_⟩
  · split_ifs with h1 h2 h2
    · simpa using h l l'
    · simpa using (h l l').mul (IntAt.coe P (q : 𝓞 E))
    · simpa [div_eq_mul_inv] using h' l l' h2 h1
    · simpa using h l l'
  · have := h' l l'
    rw [if_pos h1, if_neg h2] at this
    simpa [div_eq_mul_inv] using this

theorem mem_JQ_iff [StarRing E] (hq0 : (q : E) ≠ 0) (kj n c : ℕ) (κ : Sp E (n + c) ≃ₗ[E] Sp E (n + c)) :
    κ ∈ LocE.JQ P q kj n c ↔ Par P q kj n c κ ∧ Par P q kj n c κ⁻¹ := by
  rw [LocE.JQ, Subgroup.mem_inf, mem_stabL_iff, mem_stabL_iff, par_iff hq0, par_iff hq0]
  tauto

end Lat

section Level
variable {E k : Type} [Field E] [NumberField E] [StarRing E] [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] {P : HeightOneSpectrum (𝓞 E)} {q : ℕ} {ι : E →+* k} {ϖ : kˣ} {κ τ j c s n : ℕ}

theorem pos_stdOrd (h : j + c = s + 1) (hn : n = κ + j * (τ + 1)) (x : Ix (Fin κ ⊕ Fin (s + 1)) (Fin τ) j) :
    (κ + j ≤ yPos xPos n (stdOrd (Fin κ) (Fin τ) j c h x) ∧ yPos xPos n (stdOrd (Fin κ) (Fin τ) j c h x) < n) ↔
      x.isRight = true := by
  obtain ⟨y, rfl⟩ := (stdOrd (Fin κ) (Fin τ) j c h).symm.surjective x
  rw [Equiv.apply_symm_apply]
  rcases y with ((i | i) | p) | i
  · rw [(Equiv.symm_apply_eq _).2 (stdOrd_eps _ _ j c h i).symm]
    have := i.2
    simp [yPos, xPos]; omega
  · rw [(Equiv.symm_apply_eq _).2 (stdOrd_f _ _ j c h i).symm]
    simp [yPos, xPos]
  · rw [(Equiv.symm_apply_eq _).2 (stdOrd_d _ _ j c h p).symm]
    have := GlobalTheory.SymBridge.Coords.xPos_lt (κ := κ) (.inr p)
    simp only [yPos, xPos, Sum.elim_inl, Sum.isRight_inr, iff_true] at this ⊢
    omega
  · rw [(Equiv.symm_apply_eq _).2 (standardOrderExtendedBasis_apply_low_block _ _ j c h i).symm]
    simp [yPos]

theorem par_iff_mat (hc : IsCompl P q ι ϖ) (hu : GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsUnif ϖ) (h : j + c = s + 1) (hn : n = κ + j * (τ + 1))
    {e : XIx (Fin κ) (Fin τ) j ⊕ Fin c ≃ Fin (n + c)} (he : IsOrd (yPos xPos n) e) (γ : Sp E (n + c) ≃ₗ[E] Sp E (n + c)) :
    Par P q (κ + j) n c γ ↔ IntM ((reGL (stdOrd (Fin κ) (Fin τ) j c h)).symm (phi ι e γ)).val ∧
      MaxM ((reGL (stdOrd (Fin κ) (Fin τ) j c h)).symm (phi ι e γ)).val.toBlocks₂₁ := by
  set o := stdOrd (Fin κ) (Fin τ) j c h
  have hv : ∀ x y, ((reGL o).symm (phi ι e γ)).val x y = ι (γ (Pi.single (e (o y)) 1) (e (o x))) := fun _ _ => rfl
  refine and_congr ⟨fun H x y => (hc.int _).2 (H _ _), fun H l l' => ?_⟩ ⟨fun H x y => ?_, fun H l l' h1 h2 => ?_⟩
  · obtain ⟨x, rfl⟩ := (o.trans e).surjective l
    obtain ⟨y, rfl⟩ := (o.trans e).surjective l'
    exact (hc.int _).1 (H x y)
  · refine (GlobalTheory.SymBridge.ComplRes.v_div_q hc hu _).2 (H (e (o (.inr x))) (e (o (.inl y))) ?_ ?_)
    · rw [he, pos_stdOrd h hn]; rfl
    · rw [he, pos_stdOrd h hn]; simp
  · obtain ⟨x, rfl⟩ := (o.trans e).surjective l
    obtain ⟨y, rfl⟩ := (o.trans e).surjective l'
    rw [Equiv.trans_apply, he, pos_stdOrd h hn] at h1 h2
    rcases x with x | x
    · simp at h1
    rcases y with y | y
    · exact (GlobalTheory.SymBridge.ComplRes.v_div_q hc hu _).1 (H x y)
    · simp at h2

theorem mem_par_iff (hc : IsCompl P q ι ϖ) (hu : GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsUnif ϖ) (h : j + c = s + 1) (hn : n = κ + j * (τ + 1))
    {e : XIx (Fin κ) (Fin τ) j ⊕ Fin c ≃ Fin (n + c)} (he : IsOrd (yPos xPos n) e) {δ : kˣ →* ℂˣ} (hδ : IsTame δ)
    (γ : Sp E (n + c) ≃ₗ[E] Sp E (n + c)) :
    (reGL (stdOrd (Fin κ) (Fin τ) j c h)).symm (phi ι e γ) ∈ (parahoric _ (Fin j × Fin τ) δ hδ).J ↔
      γ ∈ LocE.JQ P q (κ + j) n c := by
  rw [mem_JQ_iff (GlobalTheory.SymBridge.ComplRes.q_ne_zero hc), par_iff_mat hc hu h hn he, par_iff_mat hc hu h hn he, map_inv, map_inv]
  constructor
  · intro H
    have H1 := mem_parahoric.1 H
    have H2 := mem_parahoric.1 (inv_mem H)
    exact ⟨⟨intM_of_mem_KO H1.1, H1.2⟩, intM_of_mem_KO H2.1, H2.2⟩
  · intro H
    exact mem_parahoric.2 ⟨mem_KO.2 ⟨H.1.1, H.2.1⟩, H.1.2⟩

theorem det_block (h : j + c = s + 1) (hn : n = κ + j * (τ + 1))
    {e : XIx (Fin κ) (Fin τ) j ⊕ Fin c ≃ Fin (n + c)} (he : IsOrd (yPos xPos n) e) (γ : Sp E (n + c) ≃ₗ[E] Sp E (n + c)) :
    ((reGL (stdOrd (Fin κ) (Fin τ) j c h)).symm (phi ι e γ)).val.toBlocks₂₂.det =
      ι (Matrix.det (Matrix.of fun a b : Fin (n - (κ + j)) =>
        Loc.atN (γ.toLinearMap (Loc.eN E (n + c) (κ + j + b.1))) (κ + j + a.1))) := by
  have hm : j * τ = n - (κ + j) := by
    have : j * (τ + 1) = j * τ + j := by ring
    omega
  let f : Fin j × Fin τ ≃ Fin (n - (κ + j)) := finProdFinEquiv.trans (finCongr hm)
  have hf : ∀ p, κ + j + (f p).1 = (e (.inl (.inr p))).1 := fun p => by
    rw [he]
    simp [f, yPos, xPos, finProdFinEquiv]
    ring
  rw [RingHom.map_det, ← det_submatrix_equiv_self f]
  congr 1
  ext a b
  simp only [RingHom.mapMatrix_apply, submatrix_apply, Matrix.map_apply, Matrix.of_apply]
  rw [hf, hf, eN_eq, Loc.atN, dif_pos (Fin.is_lt _)]
  rfl

end Level

theorem levelAgree : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S₀ : Set ℕ) (mu : Tup X.F X.E X.K S₀) (cst : LocCst X (rowSG Pr sel mu)) (σ₀ : X.K →+* ℂ) (P : rowSG Pr sel mu) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : X.E →+* k) (s : ℕ) (W : TwData k) [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν → cst.Ok → AtTwist (R := R) sel mu cst σ₀ P ι s W → LevelAgree Ch sel mu cst σ₀ P ι s W := by
  intro X Pr R Ch sel S₀ mu cst σ₀ P k _ _ _ _ ι s W _ _ ν _ _ hA j c h γ g hg
  have hc : c = cOf R j := by have := hA.steps; unfold cOf; omega
  subst hc
  obtain ⟨e, he, hg⟩ := hg
  obtain rfl : g = phi ι e γ := Units.ext hg
  have hn : R.N j = R.k + j * (R.t + 1) := rfl
  set o := stdOrd (Fin R.k) (Fin R.t) j (cOf R j) h with ho
  have hconj : ∀ g : GL _ k, (plainFrame (k := k) o).conj.symm g = (reGL o).symm g := fun g => by
    rw [MulEquiv.symm_apply_eq, LatFrame.conj_apply, show (plainFrame (k := k) o).bas = 1 from rfl,
      show (plainFrame (k := k) o).ord = o from rfl, MulEquiv.apply_symm_apply]
    simp
  have hJ : ∀ g, g ∈ ((W.T s R).lev j (cOf R j) h).J ↔ (reGL o).symm g ∈ (parahoric _ (Fin j × Fin R.t) W.δ W.tame).J :=
    fun g => by rw [← hconj]; rfl
  have hmem : ∀ γ : AutY X R j, phi ι e γ ∈ ((W.T s R).lev j (cOf R j) h).J ↔ γ ∈ Jat (Pr := Pr) cst.sharp j P.1 := fun γ => by
    rw [hJ, Jat, if_neg hA.nmem]
    exact mem_par_iff hA.compl W.unif h hn he W.tame γ
  refine ⟨hmem γ, fun hg' => ?_, fun _ γ' g' hg' => ?_⟩
  · obtain ⟨h1, h2⟩ := mem_parahoric.1 ((hJ _).1 hg')
    obtain ⟨-, D, hD, eD⟩ := exists_diag_blocks h1 h2
    have e1 : ((W.T s R).lev j (cOf R j) h).lam ⟨_, hg'⟩ = W.δ (Matrix.GeneralLinearGroup.det D) :=
      parahoric_lam (δ := W.δ) (hδ := W.tame) ⟨(plainFrame (k := k) o).conj.symm (phi ι e γ), hg'⟩ D
        (eD.trans (by rw [← hconj]))
    have e2 := det_block (ι := ι) h hn he γ
    rw [← eD, ← Matrix.GeneralLinearGroup.val_det_apply] at e2
    have hv := valuation_det_of_mem_KO hD
    rw [e2] at hv
    have hi := GlobalTheory.SymBridge.ComplRes.intAt_of_v hA.compl hv.le
    rw [e1, hA.del _ _ hi ((GlobalTheory.SymBridge.ComplRes.v_eq_one_iff_red hA.compl W.unif hi).1 hv) e2, lamRow, if_neg hA.nmem,
      LocE.lamQB, map_inv₀]
  · obtain ⟨e', he', hg'⟩ := hg'
    obtain rfl : e' = e := Equiv.ext fun a => Fin.ext ((he' a).trans (he a).symm)
    obtain rfl : g' = phi ι e' γ' := Units.ext hg'
    exact dc_iff ι hA.compl.dense (fun a => GlobalTheory.SymBridge.Coords.xPos_lt a) he _
      (fun u hu => (hJ u).2 (((parahoric _ (Fin j × Fin R.t) W.δ W.tame).reindex o).KOne_le hu)) _ hmem γ γ'

end GlobalTheory.TwBridge.Lev
