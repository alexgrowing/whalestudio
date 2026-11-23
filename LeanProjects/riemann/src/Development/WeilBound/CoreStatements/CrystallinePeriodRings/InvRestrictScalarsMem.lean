import Mathlib
import Development.WeilBound.CoreStatements.CrystallinePeriodRings.ExistsMapEqOfPowMul
import Development.WeilBound.CoreStatements.CrystallinePeriodRings.PhiGalCris
import GroundTheory.PAdicHodge.GalSmulAlgebraMapPadicPlus

noncomputable section

namespace PositivityTheory.LocInh

open GroundTheory.PAdicHodge Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc

section Abstract

theorem inv_away_range {A E : Type} [CommRing A] [Field E] {a : A}
    (F : Localization.Away a →+* E) (f : A → E)
    (h : ∀ x, F (algebraMap A (Localization.Away a) x) = f x) {k : ℕ} {y : A} {z : E}
    (e : f y = f a ^ k * z) : ∃ x, F x = z := by
  rw [← h, ← h] at e
  exact exists_map_eq_of_pow_mul F (IsLocalization.Away.algebraMap_isUnit a) e

theorem inv_map_frac {A B E : Type} [CommRing A] [CommRing B] [Field E] {F : B →+* E} {f : A →+* B}
    {g : A →+* E} (h : Fac F f g) {a t y : A} {m n : ℕ} {x : B} (e : f a ^ m * f t ^ n * x = f y) :
    g y = g a ^ m * (g t ^ n * F x) := by
  have h1 := congrArg F e
  rw [map_mul, map_mul, map_pow, map_pow, h, h, h] at h1
  rw [← h1, mul_assoc]

theorem inv_equivariant {A B E : Type} [CommRing A] [CommRing B] [Field E] {F : B →+* E}
    {f : A →+* B} {g : A →+* E} (h : Fac F f g) {a t : A} (hf : IsFrac f a t) {s : B →+* B}
    {s₀ : A →+* A} (hs : s.comp f = f.comp s₀) (τ : E ≃+* E) (hτ : ∀ x, g (s₀ x) = τ (g x))
    (b : B) : F (s b) = τ (F b) := by
  have e : F.comp s = (τ : E →+* E).comp F := by
    refine hf.hom_ext fun x => ?_
    have h1 : s (f x) = f (s₀ x) := RingHom.congr_fun hs x
    rw [RingHom.comp_apply, RingHom.comp_apply, h1, h, h, hτ, RingHom.coe_coe]
  exact RingHom.congr_fun e b

end Abstract

section Restrict

variable {p : ℕ} [Fact p.Prime] {K L : IntermediateField ℚ_[p] (PadicAlgCl p)}

local notation "𝔹" => BDeRhamPlus (normInteger ℂ_[p]) p
local notation "𝔹dR" => BDeRham (normInteger ℂ_[p]) p

theorem inv_galCp_congr (σ : Gal(PadicAlgCl p/K)) (τ : Gal(PadicAlgCl p/L)) (h : ∀ x, σ x = τ x) :
    (galCp σ : ℂ_[p] →+* ℂ_[p]) = (galCp τ : ℂ_[p] →+* ℂ_[p]) :=
  RingHom.ext (congrFun (eq_galCp_of_continuous τ (galCp σ) (continuous_galCp σ)
    fun y => by rw [galCp_coe, h]))

theorem inv_galMap_congr (σ : Gal(PadicAlgCl p/K)) (τ : Gal(PadicAlgCl p/L)) (h : ∀ x, σ x = τ x) :
    AInf.galMap σ = AInf.galMap τ :=
  AInf.map_congr (inv_galCp_congr σ τ h) _ _

theorem inv_galAway_congr (σ : Gal(PadicAlgCl p/K)) (τ : Gal(PadicAlgCl p/L)) (h : ∀ x, σ x = τ x) :
    galAway σ = galAway τ :=
  IsLocalization.ringHom_ext (Submonoid.powers (p : AInf ℂ_[p] p)) (RingHom.ext fun w => by
    rw [RingHom.comp_apply, RingHom.comp_apply, galAway_algebraMap, galAway_algebraMap,
      AInf.gal_smul_def, AInf.gal_smul_def, inv_galMap_congr σ τ h])

theorem inv_galQuot_congr (σ : Gal(PadicAlgCl p/K)) (τ : Gal(PadicAlgCl p/L)) (h : ∀ x, σ x = τ x)
    (n : ℕ) : galQuot σ n = galQuot τ n :=
  Ideal.Quotient.ringHom_ext (RingHom.ext fun a => by
    simp only [RingHom.comp_apply, galQuot_mk, inv_galAway_congr σ τ h])

theorem inv_galBdRHom_congr (σ : Gal(PadicAlgCl p/K)) (τ : Gal(PadicAlgCl p/L))
    (h : ∀ x, σ x = τ x) (x : 𝔹) : galBdRHom σ x = galBdRHom τ x :=
  IsPerfectoidField.evalB_ext fun n => by
    rw [evalB_galBdRHom, evalB_galBdRHom, inv_galQuot_congr σ τ h]

theorem inv_galBdRField_congr (σ : Gal(PadicAlgCl p/K)) (τ : Gal(PadicAlgCl p/L))
    (h : ∀ x, σ x = τ x) : galBdRField σ = galBdRField τ := by
  have e : galBdR σ = galBdR τ := RingEquiv.ext fun x => by
    rw [galBdR_apply, galBdR_apply, gal_smul_bdR_def, gal_smul_bdR_def, inv_galBdRHom_congr σ τ h]
  unfold galBdRField
  rw [e]

end Restrict

variable {l : ℕ} [Fact l.Prime]

theorem inv_galBdRField_eq {K : IntermediateField ℚ_[l] (Om l)} (σ : Gal(PadicAlgCl l/K)) :
    galBdRField σ = Per6.σD (σ.restrictScalars ℚ_[l]) :=
  inv_galBdRField_congr σ (Per6.toBot (σ.restrictScalars ℚ_[l])) fun _ => rfl

theorem inv_restrictScalars_mem (K : FinExt l) (σ : Gal(PadicAlgCl l/K.1)) :
    σ.restrictScalars ℚ_[l] ∈ GK K :=
  (IntermediateField.mem_fixingSubgroup_iff _ _).2 fun x hx => σ.commutes ⟨x, hx⟩

theorem invD (K : FinExt l) (b : Per6.BdR l) (hb : ∀ g ∈ GK K, Per6.σD g b = b) :
    ∃ c ∈ K.1, oD l c = b := by
  have := K.2
  obtain ⟨k, hk⟩ := bDeRham_fixed K.1 b fun σ => by
    rw [gal_smul_bDeRham_def, inv_galBdRField_eq]
    exact hb _ (inv_restrictScalars_mem K σ)
  exact ⟨k.1, k.2, hk⟩

theorem inv_cD_galCris (g : GQ l) (x : ACris.ACris ℂ_[l] l) :
    cD l (ACris.galCris (Per6.toBot g) x) = Per6.σD g (cD l x) := by
  rw [cD_apply, cD_apply, ← ACris.gal_smul_def, ACris.iota_gal_smul]
  exact (galBdRField_algebraMap _ _).symm

theorem inv_ιCD_σB (g : GQ l) (b : Per6.Bcris l) : ιCD l (Per6.σB g b) = Per6.σD g (ιCD l b) :=
  inv_equivariant (ιCD_fac l) (cB_isFrac l) (σB_comp g) (Per6.σD g) (inv_cD_galCris g) b

variable (l) in

def invPlusD : ACris.BCrisPlus ℂ_[l] l →+* Per6.BdR l :=
  (algebraMap (Per6.BdRp l) (Per6.BdR l)).comp (ACris.iotaPlus ℂ_[l] l)

theorem invPlusD_algebraMap (x : ACris.ACris ℂ_[l] l) :
    invPlusD l (algebraMap (ACris.ACris ℂ_[l] l) (ACris.BCrisPlus ℂ_[l] l) x) = cD l x :=
  congrArg (algebraMap (Per6.BdRp l) (Per6.BdR l)) (ACris.iotaPlus_algebraMap x)

theorem inv_exists_plus (b : Per6.Bcris l) : ∃ (n : ℕ) (y : ACris.BCrisPlus ℂ_[l] l),
    invPlusD l y = cD l (Per6.tA l) ^ n * ιCD l b := by
  obtain ⟨m, n, y, h⟩ := bcris_surj b
  exact ⟨n, inv_away_range (invPlusD l) (cD l) invPlusD_algebraMap (inv_map_frac (ιCD_fac l) h)⟩

set_option maxHeartbeats 1600000 in
theorem inv_exists_iotaB {ε : PreTilt (normInteger ℂ_[l]) l} (hε : PreTilt.untilt ε = 1)
    (hζ : PreTilt.untilt ((_root_.frobeniusEquiv (PreTilt (normInteger ℂ_[l]) l) l).symm ε) ≠ 1)
    {n : ℕ} {y : ACris.BCrisPlus ℂ_[l] l} {z : Per6.BdR l}
    (h : invPlusD l y = cD l (ACris.periodT hε) ^ n * z) :
    ∃ x : ACris.BCris hε, ACris.iotaB hε hζ x = z :=
  inv_away_range (ACris.iotaB hε hζ) (invPlusD l) (ACris.iotaB_algebraMap hε hζ)
    (h.trans (congrArg (· ^ n * z) (invPlusD_algebraMap (ACris.periodT hε)).symm))

set_option maxHeartbeats 1600000 in
theorem inv_mem_Kur {b : Per6.Bcris l} {c : Om l} (h : oD l c = ιCD l b) : c ∈ MaximalUnramifiedExtension l := by
  obtain ⟨n, y, hy⟩ := inv_exists_plus b
  rw [← h] at hy
  rw [kur_eq]
  exact (ACris.exists_iotaB_eq_iff untilt_epsilon untilt_frobeniusEquiv_symm_epsilon_ne_one).1
    (inv_exists_iotaB untilt_epsilon untilt_frobeniusEquiv_symm_epsilon_ne_one hy)

theorem invB (K : FinExt l) (b : Per6.Bcris l) (hb : ∀ g ∈ GK K, Per6.σB g b = b) :
    ∃ c : ↥(MaximalUnramifiedExtension l), (c : Om l) ∈ K.1 ∧ uB l c = b := by
  obtain ⟨c, hc, h⟩ := invD K (ιCD l b) fun g hg =>
    (inv_ιCD_σB g b).symm.trans (congrArg (ιCD l) (hb g hg))
  exact ⟨⟨c, inv_mem_Kur h⟩, hc, ιCD_injective ((ιCD_uB _).trans h)⟩

end PositivityTheory.LocInh
