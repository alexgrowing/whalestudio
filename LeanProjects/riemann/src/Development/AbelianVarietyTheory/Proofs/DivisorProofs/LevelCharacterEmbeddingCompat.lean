import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Formalism.LocalToGlobal.IndefiniteReal.RhoGeo
import Formalism.LocalToGlobal.ProjectiveLattices.CuspFormsFiniteDimensionalOf
import Formalism.LocalToGlobal.ProjectiveLattices.ThProps
import Formalism.LocalToGlobal.ProjectiveLattices.FreeBridge
import Formalism.LocalToGlobal.UnitaryNorms.CharUniq
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsHalfOfBasePins
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CompletedLatticeEqAdelicCompletionAndGram

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LiftLevel

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem resS_eq_zero {I : Ideal (𝓞 E)} {PP : Pl E} (h : I ≤ PP.asIdeal) {s : Formalism.L2.Herm.intAf F E}
    (hs : s ∈ idS F I) : resS F PP s = 0 := by
  have : idS F I ≤ RingHom.ker (resS F PP) := by
    refine Ideal.map_le_iff_le_comap.2 fun a ha => ?_
    show resS F PP (oToS F E a) = 0
    rw [resS_oToS]
    exact Ideal.Quotient.eq_zero_iff_mem.2 (h ha)
  exact this hs

theorem mem_idS {I : Ideal (𝓞 E)} (hI : Squarefree I) {s : Formalism.L2.Herm.intAf F E}
    (hs : ∀ PP : Pl E, I ≤ PP.asIdeal → resS F PP s = 0) : s ∈ idS F I := by
  have h0 : I ≠ ⊥ := hI.ne_zero
  obtain ⟨q, hq⟩ := cmpS_surj (F := F) I h0 (Ideal.Quotient.mk _ s)
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q
  have h1 : oToS F E a - s ∈ idS F I := Ideal.Quotient.eq.1 hq
  have hr : I.IsRadical := by
    intro x hx
    obtain ⟨m, hm⟩ := hx
    have := hI.isRadical m (Ideal.span {x}) (by
      rw [Ideal.span_singleton_pow, Ideal.dvd_span_singleton]; exact hm)
    exact Ideal.dvd_span_singleton.1 this
  have ha : a ∈ I := by
    apply hr
    rw [Ideal.radical_eq_sInf, Ideal.mem_sInf]
    rintro J ⟨hJ, hp⟩
    let PP : Pl E := ⟨J, hp, fun h => h0 (eq_bot_iff.2 (h ▸ hJ))⟩
    have h2 := resS_eq_zero (PP := PP) hJ h1
    rw [map_sub, hs PP hJ, sub_zero, resS_oToS] at h2
    exact Ideal.Quotient.eq_zero_iff_mem.1 h2
  have := (idS F I).sub_mem (Ideal.mem_map_of_mem (oToS F E) ha) h1
  simpa using this

theorem redFn_eq_one_iff (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (PP : Pl E)
    (y : GL (Fin n) (Formalism.L2.Herm.intAf F E)) :
    redFn β PP (frGL β y) = 1 ↔ ∀ i j, resS F PP ((y.1 - 1) i j) = 0 := by
  rw [redFn_frGL, Units.ext_iff, ← Matrix.ext_iff]
  refine forall₂_congr fun i j => ?_
  rw [Matrix.sub_apply, map_sub, sub_eq_zero]
  have : resS F PP ((1 : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E)) i j) =
      (1 : Matrix (Fin n) (Fin n) (kP PP)) i j := by
    rw [Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  rw [this]
  rfl

theorem inv_mulVec_sub (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (y : GL (Fin n) (Formalism.L2.Herm.intAf F E))
    (z : Fin n → E ⊗[F] Formalism.L2.Herm.Af F) (i : Fin n) :
    ((β⁻¹).1 *ᵥ ((frGL β y).1 *ᵥ z - z)) i =
      ∑ j, (((y.1 - 1) i j : Formalism.L2.Herm.intAf F E) : E ⊗[F] Formalism.L2.Herm.Af F) * ((β⁻¹).1 *ᵥ z) j := by
  have e1 : ((frGL β y : GL (Fin n) _) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) =
      β.1 * (intGL F E n y).1 * (β⁻¹).1 := rfl
  have e2 : (β⁻¹).1 *ᵥ ((frGL β y).1 *ᵥ z - z) = ((intGL F E n y).1 - 1) *ᵥ ((β⁻¹).1 *ᵥ z) := by
    rw [e1, Matrix.mulVec_sub, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_mulVec, ← Matrix.mul_assoc,
      ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul, Matrix.mulVec_mulVec]
  rw [e2]
  show ∑ j : Fin n, ((intGL F E n y).1 - 1) i j * ((β⁻¹).1 *ᵥ z) j = _
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  rw [Matrix.sub_apply, Matrix.sub_apply, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> rfl

theorem redFn_of_cong {β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} {Λ : Submodule (𝓞 E) (Fin n → E)}
    (hβ : IsFrame β Λ) {x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} (hx : x ∈ St β) {N : ℕ}
    (h : ∀ z ∈ Formalism.L2.Herm.hatL (F := F) Λ, ∃ w ∈ Formalism.L2.Herm.hatL (F := F) Λ, x.1 *ᵥ z - z = N • w)
    {PP : Pl E} (hN : (N : 𝓞 E) ∈ PP.asIdeal) : redFn β PP x = 1 := by
  obtain ⟨y, rfl⟩ := hx
  rw [redFn_eq_one_iff]
  intro i j
  have e0 : (β⁻¹).1 *ᵥ (β.1 *ᵥ Pi.single j 1) = Pi.single j 1 := by
    rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
  have h1 : β.1 *ᵥ Pi.single j 1 ∈ Formalism.L2.Herm.hatL (F := F) Λ := by
    rw [hβ]
    intro k
    rw [e0, Pi.single_apply]
    split_ifs
    · exact Subring.one_mem _
    · exact Subring.zero_mem _
  obtain ⟨w, hw, e⟩ := h _ h1
  have h2 := inv_mulVec_sub β y (β.1 *ᵥ Pi.single j 1) i
  rw [e, e0, Matrix.mulVec_smul, Finset.sum_eq_single j (fun b _ hb => by simp [hb]) (by simp)] at h2
  have h3 : (y.1 - 1) i j = oToS F E N * ⟨_, (hβ w).1 hw i⟩ := by
    apply Subtype.ext
    rw [Pi.single_eq_same, mul_one] at h2
    rw [← h2, map_natCast]
    simp
  rw [h3, map_mul, resS_oToS, Ideal.Quotient.eq_zero_iff_mem.2 hN, zero_mul]

theorem cong_of_redFn {β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} {Λ : Submodule (𝓞 E) (Fin n → E)}
    (hβ : IsFrame β Λ) {x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} (hx : x ∈ St β) {M : ℕ} {I J : Ideal (𝓞 E)}
    (hI : Squarefree I) (hIJ : I * J = Ideal.span {(M : 𝓞 E)})
    (h : ∀ PP : Pl E, I ≤ PP.asIdeal → redFn β PP x = 1) {b : 𝓞 E} (hb : b ∈ J) :
    ∀ z ∈ Formalism.L2.Herm.hatL (F := F) Λ, ∃ w ∈ Formalism.L2.Herm.hatL (F := F) Λ,
      x.1 *ᵥ (oToS F E b • z) - oToS F E b • z = M • w := by
  obtain ⟨y, rfl⟩ := hx
  intro z hz
  have h1 : ∀ i j, ∃ t, t * (M : Formalism.L2.Herm.intAf F E) = (y.1 - 1) i j * oToS F E b := fun i j => by
    have h2 : (y.1 - 1) i j ∈ idS F I :=
      mem_idS hI fun PP hP => (redFn_eq_one_iff β PP y).1 (h PP hP) i j
    have h3 := Ideal.mul_mem_mul h2 (Ideal.mem_map_of_mem (oToS F E) hb)
    rw [idS, ← Ideal.map_mul, hIJ, Ideal.map_span, Set.image_singleton, map_natCast,
      Ideal.mem_span_singleton'] at h3
    exact h3
  choose t ht using h1
  let u : Fin n → E ⊗[F] Formalism.L2.Herm.Af F := fun i => ∑ j, (t i j : E ⊗[F] Formalism.L2.Herm.Af F) * ((β⁻¹).1 *ᵥ z) j
  refine ⟨β.1 *ᵥ u, ?_, ?_⟩
  · rw [hβ]
    intro i
    rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
    exact Subring.sum_mem _ fun j _ => Subring.mul_mem _ (t i j).2 ((hβ z).1 hz j)
  · have e : (β⁻¹).1 *ᵥ ((frGL β y).1 *ᵥ (oToS F E b • z) - oToS F E b • z) = M • u := by
      funext i
      rw [inv_mulVec_sub, Pi.smul_apply, Finset.smul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      have h4 := congrArg Subtype.val (ht i j)
      push_cast at h4
      rw [Subring.smul_def, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, nsmul_eq_mul, ← mul_assoc, ← mul_assoc,
        mul_comm (M : E ⊗[F] Formalism.L2.Herm.Af F), h4]
    rw [← Matrix.mulVec_smul, ← e, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]

theorem cong_of_redFn' {β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} {Λ : Submodule (𝓞 E) (Fin n → E)}
    (hβ : IsFrame β Λ) {x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} (hx : x ∈ St β) {M : ℕ} {I J : Ideal (𝓞 E)}
    (hI : Squarefree I) (hIJ : I * J = Ideal.span {(M : 𝓞 E)})
    (h : ∀ PP : Pl E, I ≤ PP.asIdeal → redFn β PP x = 1) {b : 𝓞 E} (hb : b ∈ J) :
    ∀ z ∈ Formalism.L2.Herm.hatL (F := F) Λ, ∃ w ∈ Formalism.L2.Herm.hatL (F := F) Λ,
      x.1 *ᵥ (fun i => (oToS F E b).1 * z i) - (fun i => (oToS F E b).1 * z i) = M • w :=
  cong_of_redFn hβ hx hI hIJ h hb

theorem mulVec_mem_of_cong {Λ : Submodule (𝓞 E) (Fin n → E)} {x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} {N : ℕ}
    (h : ∀ z ∈ Formalism.L2.Herm.hatL (F := F) Λ, ∃ w ∈ Formalism.L2.Herm.hatL (F := F) Λ, x.1 *ᵥ z - z = N • w) :
    ∀ z ∈ Formalism.L2.Herm.hatL (F := F) Λ, x.1 *ᵥ z ∈ Formalism.L2.Herm.hatL (F := F) Λ := by
  intro z hz
  obtain ⟨w, hw, e⟩ := h z hz
  rw [sub_eq_iff_eq_add.1 e]
  exact add_mem (nsmul_mem hw N) hz

theorem map_cong_iff {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (hφ : Function.Injective φ)
    (x : Matrix (Fin n) (Fin n) R) (M : ℕ) (z y : Fin n → R) :
    x *ᵥ z - z = M • y ↔ x.map φ *ᵥ (fun i => φ (z i)) - (fun i => φ (z i)) = M • fun i => φ (y i) := by
  rw [funext_iff, funext_iff]
  refine forall_congr' fun i => ?_
  have e : (x.map φ *ᵥ fun i => φ (z i)) i = φ ((x *ᵥ z) i) := (RingHom.map_mulVec φ x z i).symm
  rw [Pi.sub_apply, Pi.sub_apply, Pi.smul_apply, Pi.smul_apply, e, ← map_sub, ← map_nsmul]
  exact hφ.eq_iff.symm

end General

section Space

variable {D : D7}

theorem latHat_iff_frame {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)}
    {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} (h : IsSDFrame V β Λ 1)
    (z : Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E) :
    z ∈ latHat V ↔ (fun i => Lev.swapAE D (z i)) ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ := by
  obtain ⟨c, -, -, -, h1, h2⟩ := h
  have e : (Λ : Set (Fin V.rank → D.host.E)) = (GlobalTheory.Member.latC V : Set (Fin V.rank → D.host.E)) := by
    rw [GlobalTheory.Member.coe_selfDualLatticeInFrameCoordinates_eq]
    ext x
    exact ⟨fun hx => by simpa using h2 x hx, fun hx => by simpa using h1 x hx⟩
  rw [(GlobalTheory.Member.latHat_eq_hat_and_gram D V).1, ← e]
  exact GlobalTheory.LevSplit.latHat_iff Λ z

theorem swap_surj {n : ℕ} (w : Fin n → Lev.EAf D) :
    ∃ z : Fin n → Af D.host.F ⊗[D.host.F] D.host.E, (fun i => Lev.swapAE D (z i)) = w := by
  choose z hz using fun i => (GlobalTheory.LevSplit.swp_bij (F := D.host.F) (E := D.host.E)).2 (w i)
  exact ⟨z, funext hz⟩

theorem swap_cong_iff (V : HSp D) (k : GA D V) (M : ℕ) (z y : Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E) :
    (finHom V k).1 *ᵥ z - z = M • y ↔
      (Lev.finE V k).1 *ᵥ (fun i => Lev.swapAE D (z i)) - (fun i => Lev.swapAE D (z i)) =
        M • fun i => Lev.swapAE D (y i) :=
  map_cong_iff (Lev.swapAE D) (GlobalTheory.LevSplit.swp_bij (F := D.host.F) (E := D.host.E)).1 (finHom V k).1 M z y

theorem isLift_one_iff {V : HSp D} (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank)
    (hr : V.rank ≤ L.r) (hQ : L.Q = ∅) (k : GA D V) :
    Lev.IsLevelLift V β L 1 k ↔
      k ∈ GfC V ∧ Lev.finE V k ∈ St β ∧ ∀ PP ∈ L.Pg, redFn β PP (Lev.finE V k) = 1 := by
  refine and_congr_right fun _ => ⟨fun ⟨h1, h2⟩ => ⟨parLev_St h1, fun PP hP => ?_⟩, fun ⟨h1, h2⟩ => ⟨?_, ?_⟩⟩
  · have h3 : upperLeftBlock L.hr (redFn β PP (Lev.finE V k)) = 1 := congrFun h2 ⟨PP, hP⟩
    have h4 := upper_block_val_submatrix L.hr (blockTri_blkOf_le _ _ (parLev_g h1 hP))
    rw [h3] at h4
    apply Units.ext
    ext i j
    have h5 := congrFun (congrFun h4 ⟨i, i.2.trans_le hr⟩) ⟨j, j.2.trans_le hr⟩
    refine h5.symm.trans ?_
    simp [Matrix.one_apply, Fin.ext_iff]
  · refine mem_parLev.2 ⟨GlobalTheory.LevSplit.finE_mem_UA V k, h1, fun PP hP => ?_, fun PP hP => ?_⟩
    · rw [h2 PP hP]; exact Subgroup.one_mem _
    · rw [hQ] at hP; exact absurd hP (Finset.notMem_empty _)
  · funext PP
    show upperLeftBlock L.hr (redFn β PP.1 _) = 1
    rw [h2 PP.1 PP.2]; exact blockDiagonalExtendByOnePrimeField_one _ _

set_option maxHeartbeats 800000 in

theorem mem_level_iff {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)}
    {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} (h : IsSDFrame V β Λ 1)
    {Kf : Subgroup (GA D V)} {N M : ℕ} {I J : Ideal (𝓞 D.host.E)} (hK : IsLevelK V N Kf) (hH : KfHalf V Kf M J)
    (hI : Squarefree I) (hIJ : I * J = Ideal.span {(M : 𝓞 D.host.E)}) (hN : (N : 𝓞 D.host.E) ∈ I) (k : GA D V) :
    (k ∈ GfC V ∧ Lev.finE V k ∈ St β ∧ ∀ PP : Pl D.host.E, I ≤ PP.asIdeal → redFn β PP (Lev.finE V k) = 1) ↔
      k ∈ Kf := by
  have hβ : IsFrame β Λ := h.choose_spec.1
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine (hH k).2 ⟨h1, fun b hb z hz => ?_⟩
    obtain ⟨w, hw, e⟩ := cong_of_redFn' hβ h2 hI hIJ h3 hb _ ((latHat_iff_frame h z).1 hz)
    obtain ⟨y, rfl⟩ := swap_surj w
    refine ⟨y, (latHat_iff_frame h y).2 hw, (swap_cong_iff V k M _ y).2 ?_⟩
    have e1 : (fun i => Lev.swapAE D (halfVec V b z i)) =
        fun i => (oToS D.host.F D.host.E b).1 * Lev.swapAE D (z i) := by
      funext i
      exact (Lev.swapAE D).map_mul _ _
    rw [e1]
    exact e
  · intro hk
    have key : ∀ k ∈ Kf, ∀ z ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ, ∃ w ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ,
        (Lev.finE V k).1 *ᵥ z - z = N • w := by
      intro k hk z hz
      obtain ⟨z, rfl⟩ := swap_surj z
      obtain ⟨y, hy, e⟩ := ((hK k).1 hk).2 z ((latHat_iff_frame h z).2 hz)
      exact ⟨_, (latHat_iff_frame h y).1 hy, (swap_cong_iff V k N z y).1 e⟩
    have e : (Lev.finE V k)⁻¹ = Lev.finE V k⁻¹ := ((Lev.finE V).map_inv k).symm
    have h3 := mulVec_mem_of_cong (x := Lev.finE V k⁻¹) (key k⁻¹ (Kf.inv_mem hk))
    rw [← e] at h3
    have hS : Lev.finE V k ∈ St β := (GlobalTheory.LevSplit.mem_St_iff β Λ hβ _).2
      ⟨mulVec_mem_of_cong (x := Lev.finE V k) (key k hk), h3⟩
    exact ⟨((hK k).1 hk).1, hS, fun PP hP => redFn_of_cong hβ hS (key k hk) (hP hN)⟩

theorem prod_le_iff (P : Formalism.L2.Host.PiBar D.host) (PP : Pl D.host.E) :
    ∏ k, (P.pb k).asIdeal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) ≤ PP.asIdeal ↔ ∃ k, P.Div k PP := by
  rw [PP.isPrime.prod_le]
  refine exists_congr fun k => ?_
  rw [Ideal.map_le_iff_le_comap]
  constructor
  · rintro ⟨-, h⟩
    exact HeightOneSpectrum.ext ((P.pb k).isMaximal.eq_of_le (Ideal.comap_ne_top _ PP.isPrime.ne_top) h).symm
  · intro h
    exact ⟨Finset.mem_univ _, (congrArg HeightOneSpectrum.asIdeal h).ge⟩

theorem natCast_mem_prod (P : Formalism.L2.Host.PiBar D.host) :
    ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈
      ∏ k, (P.pb k).asIdeal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) := by
  rw [Fin.prod_univ_two, Nat.cast_mul]
  refine Ideal.mul_mem_mul ?_ ?_
  · simpa using Ideal.mem_map_of_mem (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) (P.pb_over 0)
  · simpa using Ideal.mem_map_of_mem (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) (P.pb_over 1)

theorem transport {V W : HSp D} (hV : V = W) {Kf : Subgroup (GA D V)} {N M : ℕ} {J : Ideal (𝓞 D.host.E)}
    (hK : IsLevelK V N Kf) (hH : KfHalf V Kf M J) :
    ∃ K' : Subgroup (GA D W), IsLevelK W N K' ∧ KfHalf W K' M J ∧
      ∀ k, k ∈ K' ↔ cast (congrArg (GA D) hV.symm) k ∈ Kf := by
  subst hV
  exact ⟨Kf, hK, hH, fun _ => Iff.rfl⟩

end Space

set_option maxHeartbeats 1000000 in

theorem isLift_one_iff_mem_level : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), R.toLevCh.Is A.μ0 → TieIn T R κ v₀ → T.pb = R.C.P.pb → ∀ (i : Fin D.R.m) (σ : T.Q.c.F →+* ℂ), GoodEmb T.Q.c σ → ∀ hV : T.V ((i : ℕ) + 1) σ = Wc D i, ∀ k : GA D (Wc D i), Lev.IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) 1 k ↔ cast (congrArg (GA D) hV.symm) k ∈ T.Kf ((i : ℕ) + 1) σ := by
  intro D G _ _ Pl0 T0 A T _ R κ v₀ hIs ht hpb i σ hσ hV k
  obtain ⟨K', hK, hH, hk⟩ := transport hV (ht.laws.levelK _ (inR i) σ hσ) (ht.laws.kfHalf _ (inR i) σ hσ)
  have hMb : T.Q.l.Mb = ∏ k, (R.C.P.pb k).asIdeal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) := by
    rw [← hpb]; exact ht.laws.half.2
  have hN : ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ T.Q.l.Mb := by
    rw [hMb]; exact natCast_mem_prod _
  have hsq : Squarefree T.Q.l.Mb := (GlobalTheory.CoverHalf.squarefree_span_g D).squarefree_of_dvd
    (Ideal.dvd_span_singleton.2 hN)
  rw [← hk, ← mem_level_iff (hIs.βW i) hK hH hsq T.Q.l.prod hN k,
    isLift_one_iff (R.βW i) (R.datWp i R.triv) (D.sp.W_rank _ (Nat.le_add_left _ _) i.2).le rfl k]
  refine and_congr_right fun _ => and_congr_right fun _ => forall_congr' fun PP => imp_congr_left ?_
  rw [hMb, prod_le_iff]
  exact hIs.Pg PP

end GlobalTheory.LiftLevel
