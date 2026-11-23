import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.WeilBound.CoreStatements.CrystallinePeriodRings.MaximalIdealEqSpanT
import GroundTheory.PAdicHodge.WAKummerEps

noncomputable section

open GroundTheory.PAdicHodge

namespace UpperTheory.Lit.Drps.Kum

variable {l : ℕ} [Fact l.Prime]

local notation "𝒪" => normInteger ℂ_[l]
local notation "𝒪♭" => PreTilt (normInteger ℂ_[l]) l
local notation "φi" => RingEquiv.symm (_root_.frobeniusEquiv (PreTilt (normInteger ℂ_[l]) l) l)

variable {P : Formalism.BasicNotions.LocPrime l} (AI : Formalism.BasicNotions.LocAinf l P)

def zeta (n : ℕ) : 𝒪 := Formalism.Per6.intEquiv l (AI.ζ n)

theorem zeta_succ (n : ℕ) : zeta AI (n + 1) ^ l = zeta AI n := by
  rw [zeta, ← map_pow, AI.ζ_succ]; rfl

def epsT : 𝒪♭ := IsPerfectoidField.ofCompatible l (zeta AI) (zeta_succ AI)

theorem tiltMap_eps : Formalism.Per6.tiltMap l AI.ε = epsT AI :=
  IsPerfectoidField.preTilt_ext l fun n => by
    rw [epsT, IsPerfectoidField.coeff_ofCompatible, Formalism.Per6.tiltMap]
    show (Formalism.Per6.modPEquiv l) (PreTilt.coeff n AI.ε) = _
    rw [AI.ε_coeff]
    rfl

theorem untilt_epsT : PreTilt.untilt (epsT AI) = 1 := by
  rw [epsT, IsPerfectoidField.untilt_ofCompatible, zeta, AI.ζ_zero, map_one]

theorem coe_pow' (x : PadicAlgCl l) (n : ℕ) : ((x ^ n : PadicAlgCl l) : ℂ_[l]) = (x : ℂ_[l]) ^ n :=
  map_pow (UniformSpace.Completion.coeRingHom (α := PadicAlgCl l)) x n

theorem norm_lRoot_le (m : ℕ) : ‖((GlobalTheory.Pst.lRoot l m : PadicAlgCl l) : ℂ_[l])‖ ≤ 1 := by
  have h : ‖((GlobalTheory.Pst.lRoot l m : PadicAlgCl l) : ℂ_[l])‖ ^ (l ^ m) = ‖(((l : PadicAlgCl l)) : ℂ_[l])‖ := by
    rw [← norm_pow, ← coe_pow', GlobalTheory.Pst.lRoot_pow l m]
  have hl : ‖(((l : PadicAlgCl l)) : ℂ_[l])‖ ≤ 1 := by
    have := (IsPerfectoidField.norm_natCast_integer_lt_one (K := ℂ_[l]) (p := l)).le
    simpa using this
  rw [← h] at hl
  by_contra hlt
  push_neg at hlt
  exact absurd hl (not_le.2 (one_lt_pow₀ hlt (pow_ne_zero _ (Fact.out : l.Prime).ne_zero)))

def lRootInt (m : ℕ) : 𝒪 := ⟨((GlobalTheory.Pst.lRoot l m : PadicAlgCl l) : ℂ_[l]), mem_normInteger.2 (norm_lRoot_le m)⟩

theorem lRootInt_succ (m : ℕ) : lRootInt (l := l) (m + 1) ^ l = lRootInt m :=
  Subtype.ext (by
    show ((GlobalTheory.Pst.lRoot l (m + 1) : PadicAlgCl l) : ℂ_[l]) ^ l = ((GlobalTheory.Pst.lRoot l m : PadicAlgCl l) : ℂ_[l])
    rw [← GlobalTheory.Pst.lRoot_succ l m, coe_pow'])

variable (l) in

def lFlat : 𝒪♭ := IsPerfectoidField.ofCompatible l lRootInt lRootInt_succ

theorem coe_untilt_iterate_lFlat (n : ℕ) :
    ((PreTilt.untilt (φi^[n] (lFlat l)) : 𝒪) : ℂ_[l]) = ((GlobalTheory.Pst.lRoot l n : PadicAlgCl l) : ℂ_[l]) := by
  rw [lFlat, untilt_iterate_ofCompatible]; rfl

theorem iterate_mul (n : ℕ) (x y : 𝒪♭) : φi^[n] (x * y) = φi^[n] x * φi^[n] y :=
  by
  induction n with
  | zero => rfl
  | succ n ih => simp only [Function.iterate_succ_apply', ih, map_mul]

theorem coe_untilt_mul (x y : 𝒪♭) :
    ((PreTilt.untilt (x * y) : 𝒪) : ℂ_[l]) = ((PreTilt.untilt x : 𝒪) : ℂ_[l]) * ((PreTilt.untilt y : 𝒪) : ℂ_[l]) := by
  rw [map_mul]; rfl

theorem coe_untilt_iterate_epsT (n : ℕ) :
    ((PreTilt.untilt (φi^[n] (epsT AI)) : 𝒪) : ℂ_[l]) = ((P.ζQ n : PadicAlgCl l) : ℂ_[l]) := by
  rw [epsT, untilt_iterate_ofCompatible, zeta]
  exact AI.ζ_eq n

theorem tiltGal_lFlat (g : Formalism.BasicNotions.Loc.GQ l) :
    tiltGal (Formalism.Per6.toBot g) (lFlat l) = lFlat l * epsPow (untilt_epsT AI) (GlobalTheory.Pst.kummer P g) := by
  refine tilt_ext_untilt fun n => Subtype.ext ?_
  show ((PreTilt.untilt (φi^[n] (tiltGal (Formalism.Per6.toBot g) (lFlat l))) : 𝒪) : ℂ_[l]) =
    ((PreTilt.untilt (φi^[n] (lFlat l * epsPow (untilt_epsT AI) (GlobalTheory.Pst.kummer P g))) : 𝒪) : ℂ_[l])
  rw [coe_untilt_iterate_tiltGal, coe_untilt_iterate_lFlat, iterate_mul, coe_untilt_mul, coe_untilt_iterate_lFlat,
    untilt_iterate_epsPow, SubmonoidClass.coe_pow, coe_untilt_iterate_epsT, gal_smul_coe]
  show (((g (GlobalTheory.Pst.lRoot l n) : PadicAlgCl l)) : ℂ_[l]) = _
  rw [GlobalTheory.Pst.isKummer_kummer P g n, mul_comm]
  push_cast [coe_pow']
  rfl

local notation "ε₀" => epsilon l

theorem untilt_lFlat : ((PreTilt.untilt (lFlat l) : 𝒪) : ℂ_[l]) = l := by
  have := coe_untilt_iterate_lFlat (l := l) 0
  rw [Function.iterate_zero_apply] at this
  rw [this, GlobalTheory.Pst.lRoot_zero]
  norm_cast

theorem exists_lFlat_eq : ∃ b : ℤ_[l], lFlat l = pFlat l * epsPow untilt_epsilon b := by
  obtain ⟨η, hη⟩ : pFlat l ∣ lFlat l :=
    preTilt_dvd_iff_norm_le.2 (le_of_eq (by rw [preTilt_norm_def, preTilt_norm_def, untilt_lFlat, coe_untilt_pFlat]))
  have hη1 : PreTilt.untilt η = 1 := by
    have h := congrArg (fun y => ((PreTilt.untilt y : 𝒪) : ℂ_[l])) hη
    rw [coe_untilt_mul, untilt_lFlat, coe_untilt_pFlat] at h
    apply Subtype.ext
    rw [OneMemClass.coe_one]
    exact ((mul_eq_left₀ natCast_p_ne_zero_cp).1 h.symm)
  obtain ⟨b, hb⟩ := exists_epsPow_eq untilt_epsilon untilt_frobeniusEquiv_symm_epsilon_ne_one hη1
  exact ⟨b, by rw [hη, hb]⟩

theorem exists_epsT_eq : ∃ a : ℤ_[l], epsPow untilt_epsilon a = epsT AI :=
  exists_epsPow_eq untilt_epsilon untilt_frobeniusEquiv_symm_epsilon_ne_one (untilt_epsT AI)

theorem pow_mod_of_pow_eq_one {M : Type*} [Monoid M] {x : M} {m : ℕ} (h : x ^ m = 1) (k : ℕ) : x ^ (k % m) = x ^ k := by
  conv_rhs => rw [← Nat.mod_add_div k m, pow_add, pow_mul, h, one_pow, mul_one]

theorem epsPow_epsPow {a : ℤ_[l]} (ha : epsPow untilt_epsilon a = epsT AI) (c : ℤ_[l]) :
    epsPow (untilt_epsT AI) c = epsPow untilt_epsilon (a * c) := by
  refine tilt_ext_untilt fun n => ?_
  have e1 : PreTilt.untilt (φi^[n] (epsT AI)) =
      PreTilt.untilt (φi^[n] (ε₀)) ^ (PadicInt.toZModPow n a).val := by
    rw [← ha]; exact untilt_iterate_epsPow _ a n
  haveI : NeZero (l ^ n) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have e2 : (PadicInt.toZModPow n (a * c)).val = (PadicInt.toZModPow n a).val * (PadicInt.toZModPow n c).val % (l ^ n) := by
    rw [map_mul, ZMod.val_mul]
  have L := untilt_iterate_epsPow (untilt_epsT AI) c n
  have R := untilt_iterate_epsPow (untilt_epsilon (p := l)) (a * c) n
  rw [L, R, e1, ← pow_mul, e2, pow_mod_of_pow_eq_one (untilt_iterate_pow_eq_one (untilt_epsilon (p := l)) n)]

theorem kummer_rel {a b : ℤ_[l]} (ha : epsPow untilt_epsilon a = epsT AI) (hb : lFlat l = pFlat l * epsPow untilt_epsilon b)
    (g : Formalism.BasicNotions.Loc.GQ l) :
    kummerC untilt_epsilon untilt_frobeniusEquiv_symm_epsilon_ne_one (Formalism.Per6.toBot g) +
      (cycloChar ⊥ (Formalism.Per6.toBot g) : ℤ_[l]) * b = b + a * GlobalTheory.Pst.kummer P g := by
  apply epsPow_injective untilt_epsilon untilt_frobeniusEquiv_symm_epsilon_ne_one
  apply tilt_mul_left_cancel (pFlat_ne_zero (p := l))
  have h1 := tiltGal_lFlat AI g
  have hp : tiltGal (Formalism.Per6.toBot g) (pFlat l) = pFlat l * kummerEta (Formalism.Per6.toBot g) :=
    pFlat_mul_kummerEta (Formalism.Per6.toBot g)
  rw [hb, map_mul, hp, tiltGal_epsPow, epsPow_epsPow AI ha,
    kummerEta_eq_epsPow untilt_epsilon untilt_frobeniusEquiv_symm_epsilon_ne_one, mul_assoc, mul_assoc,
    ← epsPow_add, ← epsPow_add] at h1
  exact h1

theorem fontaineT_congr' {x y : 𝒪♭} (h : x = y) (hx : PreTilt.untilt x = 1) (hy : PreTilt.untilt y = 1) :
    fontaineT x hx = fontaineT y hy := by
  subst h; rfl

theorem exists_rel (T : Formalism.BasicNotions.LocTied6 l P AI) : ∃ a b : ℤ_[l],
    T.eD (P.ιB P.tB) = algebraMap (Formalism.Per6.BdRp l) (Formalism.Per6.BdR l)
      (algebraMap ℚ_[l] (Formalism.Per6.BdRp l) (a : ℚ_[l]) * fontaineT (epsilon l) untilt_epsilon) ∧
    ∀ g : Formalism.BasicNotions.Loc.GQ l,
      kummerC untilt_epsilon untilt_frobeniusEquiv_symm_epsilon_ne_one (Formalism.Per6.toBot g) +
        (cycloChar ⊥ (Formalism.Per6.toBot g) : ℤ_[l]) * b = b + a * GlobalTheory.Pst.kummer P g := by
  obtain ⟨a, ha⟩ := exists_epsT_eq AI
  obtain ⟨b, hb⟩ := exists_lFlat_eq (l := l)
  refine ⟨a, b, ?_, kummer_rel AI ha hb⟩
  rw [PositivityTheory.LocInh.tie_t T, ← fontaineT_epsPow,
    fontaineT_congr' ((tiltMap_eps AI).trans ha.symm) _ (untilt_epsPow _ a)]

end UpperTheory.Lit.Drps.Kum
