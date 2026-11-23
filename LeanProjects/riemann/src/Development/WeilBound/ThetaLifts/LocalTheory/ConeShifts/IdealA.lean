import Development.WeilBound.ThetaLifts.LocalTheory.ConeShifts.ArchCone
import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.VaceigenDual

noncomputable section

namespace PositivityTheory.ThKG.Loc.Cone.Id

open scoped TensorProduct NNReal Matrix nonZeroDivisors
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes WithZero
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Idele
open Formalism.L2.Host (IsUnitAt IsUnifAt atFin unif unif_spec)
open FractionalIdeal (count)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

abbrev FI (E : Type) [Field E] [NumberField E] : Type := FractionalIdeal (𝓞 E)⁰ E

variable (F) in

def cp (w : HeightOneSpectrum (𝓞 E)) : AE F E →+* w.adicCompletion E :=
  (evalV E w).toRingHom.comp ((finAdEquiv F E).toRingHom.comp (finTens F E))

theorem cp_apply (w : HeightOneSpectrum (𝓞 E)) (x : AE F E) : cp F w x = finAdEquiv F E (finTens F E x) w := rfl

theorem inAt_iff {𝔞 : FI E} {v : Pl F} {x : AE F E} :
    InAt 𝔞 v x ↔ ∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) = v → Valued.v (cp F w x) ≤ exp (-count E w 𝔞) := Iff.rfl

theorem cp_tmul (w : HeightOneSpectrum (𝓞 E)) (a : AF F) (s : E) :
    cp F w (a ⊗ₜ[F] s) = complMap rfl (evFin F (w.under (𝓞 F)) a) * algebraMap E _ s := rfl

theorem smul_eq (a : AF F) (x : AE F E) : a • x = (a ⊗ₜ[F] (1 : E)) * x := Algebra.smul_def a x

theorem cp_smul (w : HeightOneSpectrum (𝓞 E)) (a : AF F) (x : AE F E) :
    cp F w (a • x) = complMap rfl (evFin F (w.under (𝓞 F)) a) * cp F w x := by
  rw [smul_eq, map_mul, cp_tmul, map_one, mul_one]

theorem ev_idem (v : Pl F) : evFin F v (idem F v) = 1 := evalV_singleFin_self v 1

theorem ev_idem_ne {v u : Pl F} (h : u ≠ v) : evFin F u (idem F v) = 0 := evalV_singleFin_ne h 1

theorem at_idem (v : Pl F) : At (evFin F v) (idem F v) := GlobalTheory.LatVac.at_liftV v 1

theorem cp_idem {w : HeightOneSpectrum (𝓞 E)} {v : Pl F} (h : w.under (𝓞 F) = v) (x : AE F E) :
    cp F w (idem F v • x) = cp F w x := by
  subst h; rw [cp_smul, ev_idem, map_one, one_mul]

theorem cp_idem_ne {w : HeightOneSpectrum (𝓞 E)} {v : Pl F} (h : w.under (𝓞 F) ≠ v) (x : AE F E) :
    cp F w (idem F v • x) = 0 := by
  rw [cp_smul, ev_idem_ne h, map_zero, zero_mul]

theorem inf_idem (v : Pl F) (x : AE F E) : infTens F E (idem F v • x) = 0 := by
  rw [smul_eq, map_mul]
  have : infTens F E (idem F v ⊗ₜ[F] (1 : E)) = 0 := TensorProduct.zero_tmul _ _
  rw [this, zero_mul]

theorem ext_cp {x y : AE F E} (h1 : infTens F E x = infTens F E y) (h2 : ∀ w, cp F w x = cp F w y) : x = y :=
  tens_ext h1 ((finAdEquiv F E).injective (FiniteAdeleRing.ext _ h2))

def Lat (𝔞 : FI E) (v : Pl F) : AddSubgroup (AE F E) :=
  AddSubgroup.closure {z | ∃ a : AF F, At (evFin F v) a ∧ evFin F v a ∈ v.adicCompletionIntegers F ∧ ∃ s ∈ 𝔞, z = a ⊗ₜ[F] s}

theorem inAt_of_lat {𝔞 : FI E} (h0 : 𝔞 ≠ 0) {v : Pl F} {z : AE F E} (hz : z ∈ Lat 𝔞 v) : InAt 𝔞 v z := by
  rw [inAt_iff]
  intro w hw
  subst hw
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, -, ha, s, hs, rfl⟩ := hz
    rw [cp_tmul, map_mul, valued_algebraMap]
    have h1 : Valued.v (complMap (rfl : w.under (𝓞 F) = _) (evFin F _ a)) ≤ 1 := complMap_mem rfl ha
    exact (mul_le_of_le_one_left' h1).trans ((mem_iff_valuation_le h0 s).1 hs w)
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact (Valuation.map_add _ _ _).trans (max_le hx hy)
  | neg x _ hx => rwa [map_neg, Valuation.map_neg]

theorem lat_of_inAt {𝔞 : FI E} (h0 : 𝔞 ≠ 0) {v : Pl F} {x : AE F E} (hx : InAt 𝔞 v x) : idem F v • x ∈ Lat 𝔞 v := by
  have h1 : (1 : E) ∈ 𝔞 * 𝔞⁻¹ := by rw [mul_inv_cancel₀ h0]; exact FractionalIdeal.one_mem_one _
  have key : idem F v • (((1 : AF F) ⊗ₜ[F] (1 : E)) * x) ∈ Lat 𝔞 v := by
    refine FractionalIdeal.mul_induction_on (C := fun r => idem F v • (((1 : AF F) ⊗ₜ[F] r) * x) ∈ Lat 𝔞 v) h1 ?_ ?_
    · intro s hs t ht
      set y := idem F v • (((1 : AF F) ⊗ₜ[F] t) * x) with hy
      have hint := (mem_int_iff (finTens F E y)).2 fun P => by
        rw [← cp_apply]
        by_cases hP : P.under (𝓞 F) = v
        · rw [hy, cp_idem hP, map_mul, cp_tmul, map_one, map_one, one_mul, map_mul, valued_algebraMap]
          have a1 := (mem_iff_valuation_le (inv_ne_zero h0) t).1 ht P
          rw [FractionalIdeal.count_inv, neg_neg] at a1
          refine (mul_le_mul' a1 (inAt_iff.1 hx P hP)).trans ?_
          rw [← exp_add]; simp
        · rw [hy, cp_idem_ne hP]; simp
      have e1 : extZero F E (finTens F E y) = y :=
        tens_ext (by rw [infTens_extZero, hy, inf_idem]) (finTens_extZero _)
      have h2 : ∀ y' ∈ AddSubgroup.closure {y : Af F ⊗[F] E | ∃ a ∈ Formalism.MainNotions.StandardLattice.intAf F, ∃ x : 𝓞 E, y = a ⊗ₜ[F] (x : E)},
          idem F v • (((1 : AF F) ⊗ₜ[F] s) * extZero F E y') ∈ Lat 𝔞 v := fun y' hy' => by
        induction hy' using AddSubgroup.closure_induction with
        | mem z hz =>
          obtain ⟨a, ha, o, rfl⟩ := hz
          refine AddSubgroup.subset_closure ⟨idem F v * pairA F 0 a,
            GlobalTheory.VacAny.at_mul_right (at_idem v) _, ?_, s * o, ?_, ?_⟩
          · rw [map_mul, ev_idem, one_mul]; exact ha v
          · rw [mul_comm]; exact 𝔞.val.smul_mem o hs
          · change idem F v • (((1 : AF F) ⊗ₜ[F] s) * (pairA F 0 a ⊗ₜ[F] (o : E))) = _
            rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, TensorProduct.smul_tmul', smul_eq_mul]
        | zero => rw [map_zero, mul_zero, smul_zero]; exact zero_mem _
        | add x y _ _ hx hy => rw [map_add, mul_add, smul_add]; exact add_mem hx hy
        | neg x _ hx => rw [map_neg, mul_neg, smul_neg]; exact neg_mem hx
      have h3 := h2 _ hint
      rw [e1, hy, mul_smul_comm, smul_smul, ← mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, one_mul] at h3
      have hi : idem F v * idem F v = idem F v := (GlobalTheory.LatVacArith.eq_liftV_of_at (at_idem v)).symm
      rwa [hi] at h3
    · intro a b ha hb
      rw [TensorProduct.tmul_add, add_mul, smul_add]; exact add_mem ha hb
  rwa [show ((1 : AF F) ⊗ₜ[F] (1 : E)) = 1 from rfl, one_mul] at key

theorem lat_iff {𝔞 : FI E} (h0 : 𝔞 ≠ 0) {v : Pl F} {x : AE F E} : idem F v • x ∈ Lat 𝔞 v ↔ InAt 𝔞 v x :=
  ⟨fun h => inAt_iff.2 fun w hw => cp_idem hw x ▸ inAt_iff.1 (inAt_of_lat h0 h) w hw, lat_of_inAt h0⟩

def so (σ : E →ₐ[F] E) (o : 𝓞 E) : 𝓞 E := ⟨σ o, (RingOfIntegers.isIntegral_coe o).map (σ.restrictScalars ℤ)⟩

def cj (hσ : ∀ x, σ (σ x) = x) (𝔞 : FI E) : FI E :=
  ⟨{ carrier := {t | σ t ∈ 𝔞}
     add_mem' := fun {a b} ha hb => by
       change σ (a + b) ∈ 𝔞
       rw [map_add]; exact 𝔞.val.add_mem ha hb
     zero_mem' := by
       change σ 0 ∈ 𝔞
       rw [map_zero]; exact 𝔞.zero_mem
     smul_mem' := fun c x hx => by
       change σ ((c : E) * x) ∈ 𝔞
       rw [map_mul]; exact 𝔞.val.smul_mem (so σ c) hx }, by
    obtain ⟨a, ha, h⟩ := 𝔞.isFractional
    refine ⟨so σ a, mem_nonZeroDivisors_of_ne_zero fun e => nonZeroDivisors.ne_zero ha ?_, fun b hb => ?_⟩
    · have : σ (a : E) = 0 := congrArg Subtype.val e
      exact Subtype.ext ((map_eq_zero σ).1 this)
    · obtain ⟨c, hc⟩ := h _ hb
      refine ⟨so σ c, ?_⟩
      change σ (algebraMap _ E c) = σ a * b
      rw [hc]
      change σ ((a : E) * σ b) = _
      rw [map_mul, hσ]⟩

variable (hσ : ∀ x, σ (σ x) = x)

theorem mem_cj {𝔞 : FI E} {t : E} : t ∈ cj hσ 𝔞 ↔ σ t ∈ 𝔞 := Iff.rfl

theorem cj_cj (𝔞 : FI E) : cj hσ (cj hσ 𝔞) = 𝔞 := FractionalIdeal.ext fun x => by rw [mem_cj, mem_cj, hσ]

theorem cj_ne {𝔞 : FI E} (h : 𝔞 ≠ 0) : cj hσ 𝔞 ≠ 0 := fun e => h (FractionalIdeal.eq_zero_iff.2 fun x hx => by
  have : σ x ∈ cj hσ 𝔞 := (mem_cj hσ).2 (by rwa [hσ])
  rw [e, FractionalIdeal.mem_zero_iff] at this
  exact (map_eq_zero σ).1 this)

theorem mem_one_conj {x : E} (h : x ∈ (1 : FI E)) : σ x ∈ (1 : FI E) := by
  obtain ⟨o, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 h
  exact (FractionalIdeal.mem_one_iff _).2 ⟨so σ o, rfl⟩

theorem cj_inv {𝔞 : FI E} (h : 𝔞 ≠ 0) : cj hσ 𝔞⁻¹ = (cj hσ 𝔞)⁻¹ := FractionalIdeal.ext fun x => by
  rw [mem_cj, FractionalIdeal.mem_inv_iff h, FractionalIdeal.mem_inv_iff (cj_ne hσ h)]
  constructor
  · intro H y hy
    have := mem_one_conj (σ := σ) (H _ hy)
    rwa [map_mul, hσ, hσ] at this
  · intro H y hy
    have := mem_one_conj (σ := σ) (H (σ y) ((mem_cj hσ).2 (by rwa [hσ])))
    rwa [map_mul, hσ] at this

theorem lat_cj {𝔞 : FI E} {v : Pl F} {z : AE F E} (hz : z ∈ Lat 𝔞 v) : cA σ z ∈ Lat (cj hσ 𝔞) v := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, h1, h2, s, hs, rfl⟩ := hz
    exact AddSubgroup.subset_closure ⟨a, h1, h2, σ s, (mem_cj hσ).2 (by rwa [hσ]), rfl⟩
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | neg x _ hx => rw [map_neg]; exact neg_mem hx

theorem inAt_cj {𝔞 : FI E} (h0 : 𝔞 ≠ 0) {v : Pl F} {x : AE F E} (h : InAt 𝔞 v x) : InAt (cj hσ 𝔞) v (cA σ x) := by
  have := lat_cj hσ (lat_of_inAt h0 h)
  rw [map_smul] at this
  exact (lat_iff (cj_ne hσ h0)).1 this

theorem inAt_cj_iff {𝔞 : FI E} (h0 : 𝔞 ≠ 0) {v : Pl F} {x : AE F E} : InAt 𝔞 v (cA σ x) ↔ InAt (cj hσ 𝔞) v x := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have := inAt_cj hσ h0 h
    rwa [PositivityTheory.ThK.Vac.cA_cA hσ] at this
  · have := inAt_cj hσ (cj_ne hσ h0) h
    rwa [cj_cj] at this

theorem cp_loc_self (w : HeightOneSpectrum (𝓞 E)) (y : (w.adicCompletion E)ˣ) : cp F w (locIdele F w y : AE F E) = y := by
  rw [cp_apply, finTens_locIdele]; exact finSingle_self w _

theorem cp_loc_ne {w u : HeightOneSpectrum (𝓞 E)} (h : u ≠ w) (y : (w.adicCompletion E)ˣ) :
    cp F u (locIdele F w y : AE F E) = 1 := by
  rw [cp_apply, finTens_locIdele]; exact finSingle_ne h _

theorem cp_prod (S : Finset (HeightOneSpectrum (𝓞 E))) (y : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ)
    (u : HeightOneSpectrum (𝓞 E)) : cp F u ((∏ w ∈ S, locIdele F w (y w) : (AE F E)ˣ) : AE F E) = by
      classical exact if u ∈ S then (y u : u.adicCompletion E) else 1 := by
  classical
  rw [Units.coe_prod, map_prod]
  split_ifs with h
  · rw [Finset.prod_eq_single_of_mem u h fun w _ hw => cp_loc_ne hw.symm _, cp_loc_self]
  · exact Finset.prod_eq_one fun w hw => cp_loc_ne (fun e : u = w => h (e ▸ hw)) _

theorem inf_prod (S : Finset (HeightOneSpectrum (𝓞 E))) (y : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ) :
    infTens F E ((∏ w ∈ S, locIdele F w (y w) : (AE F E)ˣ) : AE F E) = 1 := by
  rw [Units.coe_prod, map_prod]; exact Finset.prod_eq_one fun w _ => infTens_locIdele w _

theorem locChar_eq {ν : Chr F E} {w : HeightOneSpectrum (𝓞 E)} (h : UnrAt ν w) (x : (w.adicCompletion E)ˣ) {k : ℤ}
    (hx : Valued.v (x : w.adicCompletion E) = exp (-k)) : locChar ν w x = val ν w ^ k := by
  have h1 : IsUnitAt w (x * (atFin w (unif w) ^ k)⁻¹) := by
    have := unif_spec w
    unfold IsUnifAt at this
    unfold IsUnitAt
    rw [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_zpow_eq_zpow_val, map_mul, map_inv₀, map_zpow₀, hx, this,
      ← exp_zsmul, smul_eq_mul, mul_neg, mul_one, mul_inv_cancel₀ exp_ne_zero]
  have := h _ h1
  rw [map_mul, map_inv, mul_inv_eq_one, map_zpow] at this
  exact this

structure Gen (P : Finset (Pl F)) (𝔞 : FI E) (T : Finset (Pl F)) (l : (AE F E)ˣ) : Prop where
  dis : ∀ v ∈ T, v ∉ P
  inf : infTens F E l = 1
  off : ∀ v ∉ T, idem F v • (l : AE F E) = idem F v • (1 : AE F E)
  vl : ∀ w, Valued.v (cp F w l) = exp (-count E w 𝔞)

theorem Gen.eq {P T : Finset (Pl F)} {𝔞 : FI E} {l : (AE F E)ˣ} (h : Gen P 𝔞 T l) {ν : Chr F E}
    (hν : UnrOff ν (P : Set (Pl F))) : Circle.toUnits (ν l) = idealVal ν 𝔞 := by
  classical
  let S := T.biUnion fun v => Formalism.L2.Host.aboveF (L := E) F v
  have hS : ∀ w, w ∈ S ↔ w.under (𝓞 F) ∈ T := fun w => by simp [S, mem_aboveF]
  have h1 : ∀ w ∉ S, cp F w l = 1 := fun w hw => by
    have := congrArg (cp F w) (h.off _ (mt (hS w).2 hw))
    rwa [cp_idem rfl, cp_idem rfl, map_one] at this
  have e : l = ∏ w ∈ S, locIdele F w (Units.map (cp F w).toMonoidHom l) :=
    Units.ext (ext_cp (h.inf.trans (inf_prod _ _).symm) fun w => by
      rw [cp_prod]; split_ifs with hw
      exacts [rfl, h1 w hw])
  have h2 : ∀ w ∉ S, count E w 𝔞 = 0 := fun w hw => by
    have := h.vl w
    rw [h1 w hw, map_one, ← exp_zero, exp_inj] at this
    omega
  rw [idealVal, finprod_eq_prod_of_mulSupport_subset (s := S) _ fun w hw => by
    by_contra hn; exact hw (by simp [h2 w hn])]
  conv_lhs => rw [e]
  rw [map_prod, map_prod]
  exact Finset.prod_congr rfl fun w hw =>
    locChar_eq (hν w fun hP => h.dis _ ((hS w).1 hw) hP) _ (h.vl w)

def Pr (P : Finset (Pl F)) (𝔞 : FI E) : Prop := ∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) ∈ P → count E w 𝔞 = 0

theorem exists_gen {P : Finset (Pl F)} {𝔞 : FI E} (h : Pr P 𝔞) : ∃ T l, Gen P 𝔞 T l := by
  classical
  have hf : {w : HeightOneSpectrum (𝓞 E) | count E w 𝔞 ≠ 0}.Finite := FractionalIdeal.finite_factors 𝔞
  refine ⟨hf.toFinset.image fun w => w.under (𝓞 F), ∏ w ∈ hf.toFinset, locIdele F w (atFin w (unif w) ^ count E w 𝔞),
    fun v hv hP => ?_, inf_prod _ _, fun v hv => ext_cp (by rw [inf_idem, inf_idem]) fun w => ?_, fun w => ?_⟩
  · obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 hv
    exact hf.mem_toFinset.1 hw (h w hP)
  · by_cases hw : w.under (𝓞 F) = v
    · rw [cp_idem hw, cp_idem hw, cp_prod, if_neg fun hm => hv (Finset.mem_image.2 ⟨w, hm, hw⟩), map_one]
    · rw [cp_idem_ne hw, cp_idem_ne hw]
  · rw [cp_prod]
    split_ifs with hw
    · have := unif_spec w
      unfold IsUnifAt at this
      rw [Units.val_zpow_eq_zpow_val, map_zpow₀, this, ← exp_zsmul, smul_eq_mul, mul_neg, mul_one]
    · have : count E w 𝔞 = 0 := by by_contra hn; exact hw (hf.mem_toFinset.2 hn)
      simp [this]

theorem vl_of_inAt {𝔞 : FI E} {l : (AE F E)ˣ} {w : HeightOneSpectrum (𝓞 E)} (h1 : InAt 𝔞 (w.under (𝓞 F)) (l : AE F E))
    (h2 : InAt 𝔞⁻¹ (w.under (𝓞 F)) ((l⁻¹ : (AE F E)ˣ) : AE F E)) : Valued.v (cp F w l) = exp (-count E w 𝔞) := by
  have a1 := inAt_iff.1 h1 w rfl
  have a2 := inAt_iff.1 h2 w rfl
  rw [FractionalIdeal.count_inv, neg_neg] at a2
  have a3 : Valued.v (cp F w l) * Valued.v (cp F w ((l⁻¹ : (AE F E)ˣ) : AE F E)) = 1 := by
    rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
  refine le_antisymm a1 ?_
  calc exp (-count E w 𝔞) = exp (-count E w 𝔞) * (Valued.v (cp F w l) * Valued.v (cp F w ((l⁻¹ : (AE F E)ˣ) : AE F E))) := by
        rw [a3, mul_one]
    _ ≤ exp (-count E w 𝔞) * (Valued.v (cp F w l) * exp (count E w 𝔞)) := by gcongr
    _ = _ := by rw [mul_left_comm, ← exp_add]; simp

theorem Gen.conj {P T : Finset (Pl F)} {𝔞 : FI E} (h0 : 𝔞 ≠ 0) {l : (AE F E)ˣ} (h : Gen P 𝔞 T l) :
    Gen P (cj hσ 𝔞) T (Units.map (cA σ : AE F E →* AE F E) l) := by
  refine ⟨h.dis, ?_, fun v hv => ?_, fun w => vl_of_inAt ?_ ?_⟩
  · have : ∀ x : AE F E, infTens F E (cA σ x) = Algebra.TensorProduct.map (AlgHom.id F (Ainf F)) σ (infTens F E x) := fun x => by
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul a e => rfl
      | add x y hx hy => simp only [map_add, hx, hy]
    change infTens F E (cA σ l) = 1
    rw [this, h.inf, map_one]
  · have := congrArg (cA σ) (h.off v hv)
    rwa [map_smul, map_smul, map_one] at this
  · exact inAt_cj hσ h0 (inAt_iff.2 fun u _ => (h.vl u).le)
  · rw [← cj_inv hσ h0]
    refine inAt_cj hσ (inv_ne_zero h0) (x := ((l⁻¹ : (AE F E)ˣ) : AE F E)) (inAt_iff.2 fun u _ => le_of_eq ?_)
    have a3 : Valued.v (cp F u l) * Valued.v (cp F u ((l⁻¹ : (AE F E)ˣ) : AE F E)) = 1 := by
      rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
    rw [h.vl] at a3
    rw [FractionalIdeal.count_inv, neg_neg, eq_inv_of_mul_eq_one_right a3, ← exp_neg, neg_neg]

theorem idealVal_mul (ν : Chr F E) {𝔞 𝔟 : FI E} (ha : 𝔞 ≠ 0) (hb : 𝔟 ≠ 0) :
    idealVal ν (𝔞 * 𝔟) = idealVal ν 𝔞 * idealVal ν 𝔟 := by
  have hf : ∀ 𝔠 : FI E, (Function.mulSupport fun w => val ν w ^ count E w 𝔠).Finite := fun 𝔠 =>
    Set.Finite.subset (FractionalIdeal.finite_factors 𝔠) fun w hw hc => hw (by simp [show count E w 𝔠 = 0 from hc])
  unfold idealVal
  rw [← finprod_mul_distrib (hf 𝔞) (hf 𝔟)]
  exact finprod_congr fun w => by rw [FractionalIdeal.count_mul _ _ ha hb, zpow_add]

theorem idealVal_inv (ν : Chr F E) (𝔞 : FI E) : idealVal ν 𝔞⁻¹ = (idealVal ν 𝔞)⁻¹ := by
  unfold idealVal
  rw [← finprod_inv_distrib]
  exact finprod_congr fun w => by rw [FractionalIdeal.count_inv, zpow_neg]

theorem idealVal_cj {P : Finset (Pl F)} {𝔞 : FI E} (h0 : 𝔞 ≠ 0) (h : Pr P 𝔞) {ν : Chr F E} (hν : UnrOff ν (P : Set (Pl F)))
    (hc : ∀ z, ν (Units.map (cA σ : AE F E →* AE F E) z) = (ν z)⁻¹) : idealVal ν (cj hσ 𝔞) = (idealVal ν 𝔞)⁻¹ := by
  obtain ⟨T, l, hl⟩ := exists_gen h
  rw [← (hl.conj hσ h0).eq hν, ← hl.eq hν, hc, map_inv]

end PositivityTheory.ThKG.Loc.Cone.Id

end
