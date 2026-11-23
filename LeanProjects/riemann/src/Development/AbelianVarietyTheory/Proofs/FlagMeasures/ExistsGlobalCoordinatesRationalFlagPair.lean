import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.VolPin
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Vanish
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NotField
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.ExistsDualGen
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SpanDifferentEqLocalGenerator
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.HL.GCoordEx

open ValuativeRel

section Loc

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Formalism.MainNotions.S.Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V]

theorem h_smul_right (H : Formalism.MainNotions.S.Loc.HermSp M V) (c : E) (x y : V) :
    H.h x (c • y) = M.L.cj c * H.h x y := by
  rw [H.h_herm (c • y) x, H.h_smul_left, map_mul, ← H.h_herm]

theorem loc_ex (hM : M.OK) (H : Formalism.MainNotions.S.Loc.HermSp M V) (r k : ℕ) (P : Formalism.MainNotions.S.LocNG.FPair H r)
    (hP : P.RelG (Formalism.MainNotions.S.LocNG.theta M)) (b : Module.Basis (Fin (k + 2 * r + 1)) E V) (es es' : Fin r → V)
    (hd : ∀ a j, H.h (P.A.f a) (es j) = if a = j.castSucc then 1 else 0)
    (hd' : ∀ a j, H.h (P.B.f a) (es' j) = if a = j.castSucc then 1 else 0)
    (hi : ∀ i j, H.h (es i) (es j) = 0) (hi' : ∀ i j, H.h (es' i) (es' j) = 0) :
    ∃ S : Frames M.L r k, S.Hm = Matrix.of (fun i j => H.h (b i) (b j)) ∧
      S.es = (fun j => b.equivFun (es j)) ∧ S.es' = (fun j => b.equivFun (es' j)) ∧
      S.gg = M.split.isSome ∧ ∃ c : WCoord P S, c.e = b.equivFun := by
  obtain ⟨-, -, hG, -, -, ⟨w, hw⟩, hTo, hT, hTo', hT', hgg⟩ := hP
  have := hM.loc
  have := CoordExist.nontriv M.L
  obtain ⟨ϖ, hϖ, hϖg⟩ : ∃ ϖ : 𝒪[F], Irreducible ϖ ∧ ∀ g, M.split = some g → ϖ = g.q := by
    rcases h : M.split with _ | g
    · obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
      exact ⟨ϖ, hϖ, fun g hg => by cases hg⟩
    · exact ⟨g.q, g.q_irr, fun g' hg => by cases hg; rfl⟩
  refine ⟨
    { ϖ := ϖ
      ϖ_irr := hϖ
      Hm := Matrix.of fun i j => H.h (b i) (b j)
      herm := CoordExist.hermND H b
      T := Units.mk0 _ hT
      T' := Units.mk0 _ hT'
      f := fun a => b.equivFun (P.A.f a)
      f' := fun a => b.equivFun (P.B.f a)
      es := fun a => b.equivFun (es a)
      es' := fun a => b.equivFun (es' a)
      gram := fun a c => by rw [CoordExist.hf_basis]; exact CoordExist.gram_eq _ _ _
      gram' := fun a c => by rw [CoordExist.hf_basis]; exact CoordExist.gram_eq _ _ _
      dual := fun a c => by rw [CoordExist.hf_basis]; exact hd _ _
      dual' := fun a c => by rw [CoordExist.hf_basis]; exact hd' _ _
      iso := fun a c => by rw [CoordExist.hf_basis]; exact hi _ _
      iso' := fun a c => by rw [CoordExist.hf_basis]; exact hi' _ _
      w := w
      relevant := fun a c => ?_
      G_ne := ?_
      gg := M.split.isSome
      gg_ok := fun h => ?_ }, rfl, rfl, rfl, rfl,
    { e := b.equivFun
      h_eq := fun x y => CoordExist.hf_basis H b x y
      f_eq := fun _ => rfl
      f'_eq := fun _ => rfl
      T_eq := rfl
      T'_eq := rfl
      gg_none := fun h => by simp only [h, Option.isSome_none]
      gg_some := fun g h => ⟨by simp only [h, Option.isSome_some], hϖg g h⟩ }, rfl⟩
  · rw [CoordExist.hf_basis, ← hw, mul_right_comm, ← mul_pow]
    simp [Formalism.MainNotions.S.Loc.HermSp.Zhat]
  · simp only [CoordExist.hf_basis]
    have h1 : H.Dl P.A.f P.B.f (r + 1) =
        lead (Matrix.of fun a c => H.h (P.B.f c) (P.A.f a)) (Fin.last (r + 1)) := by
      unfold Formalism.MainNotions.S.Loc.HermSp.Dl; rw [dif_pos le_rfl]; rfl
    have h2 : H.Dl P.A.f P.B.f r =
        lead (Matrix.of fun a c => H.h (P.B.f c) (P.A.f a)) (Fin.last r).castSucc := by
      unfold Formalism.MainNotions.S.Loc.HermSp.Dl; rw [dif_pos (Nat.le_succ r)]; rfl
    rw [← h1, ← h2]
    exact hG
  · obtain ⟨g, hg⟩ := Option.isSome_iff_exists.1 h
    obtain ⟨⟨u, v, hu, hv⟩, -⟩ := hgg g hg
    exact ⟨CoordExist.not_field M.L g, CoordExist.unit_of hTo u hu, CoordExist.unit_of hTo' v hv⟩

end Loc

section Glob

variable {D : D7}

theorem nV_eq (D : D7) : nV D = D.R.k + 2 * D.R.rS + 1 := by
  have h1 : nV D = D.R.r := by
    show (D.sp.Y 0).rank = _
    rw [D.sp.Y_rank 0 (Nat.zero_le _)]
    simp [Ranks.rankY]
  have hm2 := D.R.two_le_m
  obtain ⟨j, hj⟩ := D.R.m_even
  have hrS : 2 * D.R.rS + 1 = D.R.m - 1 := by
    unfold Formalism.BasicNotions.Ranks.rS
    rw [hj]
    omega
  rw [h1]
  unfold Formalism.BasicNotions.Ranks.r
  omega

def sg (D : D7) : Fin (D.R.k + 2 * D.R.rS + 1) ≃ Fin (nV D) := finCongr (nV_eq D).symm

def eG (D : D7) : (VS D).V ≃ₗ[D.host.E] (Fin (D.R.k + 2 * D.R.rS + 1) → D.host.E) :=
  (VS D).frame.equivFun.trans (LinearEquiv.funCongrLeft D.host.E D.host.E (sg D))

def eL (D : D7) (p : PlF D) : Vp D p ≃ₗ[(D.s.atP p).Ep] (Fin (D.R.k + 2 * D.R.rS + 1) → (D.s.atP p).Ep) :=
  LinearEquiv.funCongrLeft _ _ (sg D)

def HmG (D : D7) : Matrix (Fin (D.R.k + 2 * D.R.rS + 1)) (Fin (D.R.k + 2 * D.R.rS + 1)) D.host.E :=
  Matrix.of fun i j => gramV D (sg D i) (sg D j)

theorem eL_bcP (Z : LocDat D) (p : PlF D) (x : (VS D).V) : eL D p (baseChange₂ D p x) = (placesOf Z).bc p (eG D x) := by
  funext i; rfl

theorem sum_sg {R : Type} [AddCommMonoid R] (g : Fin (nV D) → Fin (nV D) → R) :
    ∑ i, ∑ j, g (sg D i) (sg D j) = ∑ i, ∑ j, g i j := by
  calc ∑ i, ∑ j, g (sg D i) (sg D j) = ∑ i, ∑ j, g (sg D i) j :=
        Finset.sum_congr rfl fun i _ => Equiv.sum_comp (sg D) (g (sg D i))
    _ = ∑ i, ∑ j, g i j := Equiv.sum_comp (sg D) (fun i => ∑ j, g i j)

theorem h_eqG (x y : (VS D).V) :
    ∑ i, ∑ j, eG D x i * HmG D i j * star (eG D y j) = brS (VS D) x y := by
  have key : (VS D).hT y x = ∑ j, ∑ i, star ((VS D).frame.repr y j) *
      ((VS D).frame.repr x i * (VS D).hT ((VS D).frame j) ((VS D).frame i)) := by
    conv_lhs => rw [← (VS D).frame.sum_repr y, ← (VS D).frame.sum_repr x]
    simp only [map_sum, map_smulₛₗ, smul_eq_mul, starRingEnd_apply, LinearMap.sum_apply, LinearMap.smul_apply,
      RingHom.id_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
    ring
  have e1 : ∑ i, ∑ j, eG D x i * HmG D i j * star (eG D y j) = ∑ i, ∑ j,
      (fun a b => (VS D).frame.repr x a * gramV D a b * star ((VS D).frame.repr y b)) (sg D i) (sg D j) := rfl
  rw [e1, sum_sg (D := D) (fun a b => (VS D).frame.repr x a * gramV D a b * star ((VS D).frame.repr y b)), brS, key, Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  simp only [gramV, brS]
  ring

theorem split_isSome (Z : LocDat D) (p : PlF D) : (Z.M p).split.isSome = (D.s.atP p).split.isSome := by
  obtain ⟨-, -, -, -, -, h⟩ := Z.agree p
  revert h
  cases (Z.M p).split <;> cases (D.s.atP p).split <;> simp

end Glob

section Glob2

variable {D : D7}

def bL (D : D7) (p : PlF D) : Module.Basis (Fin (D.R.k + 2 * D.R.rS + 1)) (D.s.atP p).Ep (Vp D p) :=
  Module.Basis.ofEquivFun (eL D p)

theorem bL_apply (p : PlF D) (i : Fin (D.R.k + 2 * D.R.rS + 1)) : bL D p i = Pi.single (sg D i) 1 := by
  funext j
  simp only [bL, Module.Basis.coe_ofEquivFun, eL, LinearEquiv.funCongrLeft_symm]
  simp only [LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply]
  by_cases h : j = sg D i
  · subst h; simp
  · rw [Pi.single_eq_of_ne h, Pi.single_eq_of_ne]
    intro h'; apply h; rw [← h']; simp

theorem gram_bL (Z : LocDat D) (p : PlF D) :
    Matrix.of (fun i j => (locH Z p).h (bL D p i) (bL D p j)) = (HmG D).map (D.s.atP p).ιE := by
  ext i j
  simp only [Matrix.of_apply, bL_apply, Matrix.map_apply, HmG]
  show LocFacts₂ Z.M p _ _ = _
  rw [localForm_single]
  simp [Matrix.vecMul, dotProduct, Pi.single_apply]

theorem loc_pair (Z : LocDat D) (p : PlF D) (s t : (D.s.atP p).Ep) (x y : (VS D).V) :
    (locH Z p).h (s • baseChange₂ D p x) (t • baseChange₂ D p y) = s * ((Z.M p).L.cj t * (D.s.atP p).ιE (brS (VS D) x y)) := by
  rw [(locH Z p).h_smul_left, h_smul_right]
  congr 2
  exact baseChangeAt_form Z.M p (Z.hcj p) x y

end Glob2

section Glob3

variable {D : D7}

def cval (Z : LocDat D) (p : PlF D) : (D.s.atP p).Fp := Z.δ p * (D.s.atP p).ιF ((uP p : ℚ) : D.host.F)

theorem unitAt_ne (p : PlF D) : uP p ≠ 0 := by
  have h0 := D.host.g_prime 0
  have h1 := D.host.g_prime 1
  unfold uP gpart
  refine div_ne_zero ?_ ?_
  · split_ifs
    · exact_mod_cast h0.ne_zero
    · exact_mod_cast h1.ne_zero
    · exact one_ne_zero
  · unfold Formalism.MainNotions.S.Lat.gS
    exact_mod_cast (Nat.mul_ne_zero h0.ne_zero h1.ne_zero)

theorem cval_ne (Z : LocDat D) (p : PlF D) : cval Z p ≠ 0 := by
  obtain ⟨-, hδ, -⟩ := Z.agree p
  refine mul_ne_zero hδ ?_
  rw [map_ne_zero]
  exact_mod_cast unitAt_ne p

theorem cval_E (Z : LocDat D) (p : PlF D) :
    algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (Z.δ p) * (D.s.atP p).ιE ((uP p : ℚ) : D.host.E) =
      algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cval Z p) := by
  rw [cval, map_mul, ← (D.s.atP p).compat, map_ratCast (algebraMap D.host.F D.host.E)]

theorem cval_unitE (Z : LocDat D) (p : PlF D) : IsUnit (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cval Z p)) :=
  (isUnit_iff_ne_zero.2 (cval_ne Z p)).map _

theorem frFac_eq (Z : LocDat D) (p : PlF D) (a : Fin (D.R.rS + 1)) :
    frFac Z.δ p a = Ring.inverse (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cval Z p ^ (D.R.rS - (a : ℕ)))) := by
  rw [frFac, cval_E, map_pow]

theorem frFac_mul (Z : LocDat D) (p : PlF D) (a : Fin (D.R.rS + 1)) :
    algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cval Z p ^ (D.R.rS - (a : ℕ))) * frFac Z.δ p a = 1 := by
  rw [frFac_eq, map_pow]
  exact Ring.mul_inverse_cancel _ ((cval_unitE Z p).pow _)

theorem loc_dual (Z : LocDat D) (p : PlF D) {N : ℕ} (F0 : FlagG (VS D) D.R.rS (N : D.host.E))
    (y : Fin D.R.rS → (VS D).V) (hy : Formalism.L2.SG.Pf.Cnt.R1.Dual F0.e y F0.z N) (a : Fin (D.R.rS + 1))
    (j : Fin D.R.rS) :
    (locH Z p).h (scaled Z p F0.fvec a)
      (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cval Z p ^ (D.R.rS - (j : ℕ))) • baseChange₂ D p (y j)) =
      if a = j.castSucc then 1 else 0 := by
  show (locH Z p).h (frFac Z.δ p a • baseChange₂ D p (F0.fvec a)) _ = _
  rw [loc_pair, AlgEquiv.commutes]
  induction a using Fin.lastCases with
  | last =>
    have h0 : brS (VS D) (F0.fvec (Fin.last _)) (y j) = 0 := by
      simp only [FlagG.fvec, Fin.snoc_last, brS]; exact hy.yz j
    rw [h0, map_zero, mul_zero, mul_zero, if_neg (Fin.castSucc_lt_last j).ne']
  | cast i =>
    have h0 : brS (VS D) (F0.fvec i.castSucc) (y j) = if i = j then 1 else 0 := by
      simp only [FlagG.fvec, Fin.snoc_castSucc, brS]; exact hy.ye j i
    rw [h0]
    simp only [Fin.castSucc_inj]
    split_ifs with hij
    · subst hij
      rw [map_one, mul_one, mul_comm]
      have := frFac_mul Z p i.castSucc
      rwa [Fin.coe_castSucc] at this
    · rw [map_zero, mul_zero, mul_zero]

theorem loc_iso (Z : LocDat D) (p : PlF D) (s t : (D.s.atP p).Ep) {N : ℕ} (F0 : FlagG (VS D) D.R.rS (N : D.host.E))
    (y : Fin D.R.rS → (VS D).V) (hy : Formalism.L2.SG.Pf.Cnt.R1.Dual F0.e y F0.z N) (i j : Fin D.R.rS) :
    (locH Z p).h (s • baseChange₂ D p (y i)) (t • baseChange₂ D p (y j)) = 0 := by
  rw [loc_pair]
  simp only [brS, hy.yy, map_zero, mul_zero]

end Glob3

section Fin

variable {D : D7}

theorem unit_of_mem {K : Type} [Field K] [ValuativeRel K] {c : K} (hc : c ≠ 0) (h1 : c ∈ 𝒪[K])
    (h2 : c⁻¹ ∈ 𝒪[K]) : ∃ u : (𝒪[K])ˣ, ((u : 𝒪[K]) : K) = c :=
  ⟨⟨⟨c, h1⟩, ⟨c⁻¹, h2⟩, Subtype.ext (mul_inv_cancel₀ hc), Subtype.ext (inv_mul_cancel₀ hc)⟩, rfl⟩

theorem resChar_mem (p : PlF D) : ((Formalism.MainNotions.S.Loc.resChar p : ℕ) : 𝓞 D.host.F) ∈ p.asIdeal := by
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
  exact ringChar.Nat.cast_ringChar

theorem iF_unit (p : PlF D) (x : 𝓞 D.host.F) (hx : x ∉ p.asIdeal) :
    ((D.s.atP p).ιF (x : D.host.F))⁻¹ ∈ 𝒪[(D.s.atP p).Fp] ∧ (D.s.atP p).ιF (x : D.host.F) ≠ 0 := by
  have hv : p.valuation D.host.F (x : D.host.F) = 1 := by
    rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
      IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff]
    exact hx
  have h1 : (D.s.atP p).ιF 1 ≤ᵥ (D.s.atP p).ιF (x : D.host.F) := by
    rw [(D.s.atP p).val, hv, map_one]
  rw [map_one, Valuation.Compatible.vle_iff_le (v := valuation (D.s.atP p).Fp), map_one] at h1
  have hx0 : (D.s.atP p).ιF (x : D.host.F) ≠ 0 := by
    intro h0
    rw [h0, map_zero] at h1
    exact absurd h1 (not_le.2 zero_lt_one)
  refine ⟨?_, hx0⟩
  rw [Valuation.mem_integer_iff, map_inv₀]
  exact inv_le_one_of_one_le₀ h1

theorem gg_ne_zero (D : D7) : ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.F) ≠ 0 := by
  exact_mod_cast Nat.mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero

theorem not_mem_of (p : PlF D) (hn : ¬ ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.F) ∈ p.asIdeal) (i : Fin 2) :
    Formalism.MainNotions.S.Loc.resChar p ≠ D.host.g i := by
  intro h
  apply hn
  have hc := resChar_mem p
  rw [h] at hc
  rw [Nat.cast_mul]
  fin_cases i
  · exact Ideal.mul_mem_right _ _ hc
  · exact Ideal.mul_mem_left _ _ hc

theorem split_fin (D : D7) : {p : PlF D | (D.s.atP p).split.isSome = true}.Finite := by
  refine (Ideal.finite_factors (I := Ideal.span {((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.F)}) ?_).subset ?_
  · rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact gg_ne_zero D
  intro p hp
  simp only [Set.mem_setOf_eq] at hp ⊢
  rw [Ideal.dvd_span_singleton]
  by_contra hn
  rw [D.s_split] at hp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with h | h
  · exact not_mem_of p hn 0 h
  · exact not_mem_of p hn 1 h

theorem isUnit_unitAt (D : D7) :
    {p : PlF D | ¬ ∃ u : (𝒪[(D.s.atP p).Fp])ˣ,
      ((u : 𝒪[(D.s.atP p).Fp]) : (D.s.atP p).Fp) = (D.s.atP p).ιF ((uP p : ℚ) : D.host.F)}.Finite := by
  refine (Ideal.finite_factors (I := Ideal.span {((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.F)}) ?_).subset ?_
  · rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact gg_ne_zero D
  intro p hp
  simp only [Set.mem_setOf_eq] at hp ⊢
  rw [Ideal.dvd_span_singleton]
  by_contra hn
  apply hp
  have hu : uP p = ((D.host.g 0 * D.host.g 1 : ℕ) : ℚ)⁻¹ := by
    unfold uP gpart
    rw [if_neg (not_mem_of p hn 0), if_neg (not_mem_of p hn 1)]
    unfold Formalism.MainNotions.S.Lat.gS
    push_cast
    ring
  obtain ⟨hinv, hx0⟩ := iF_unit p _ hn
  have e : (D.s.atP p).ιF ((uP p : ℚ) : D.host.F) =
      ((D.s.atP p).ιF (((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.F) : D.host.F))⁻¹ := by
    rw [hu, ← map_inv₀]
    congr 1
    push_cast
    rfl
  rw [e]
  refine unit_of_mem (inv_ne_zero hx0) hinv ?_
  rw [inv_inv]
  exact GlobalTheory.LocDiffGen.iF_int p _

theorem memF_of (p : PlF D) (c : (D.s.atP p).Fp) (h : algebraMap (D.s.atP p).Fp (D.s.atP p).Ep c ∈ (D.s.atP p).O) :
    c ∈ 𝒪[(D.s.atP p).Fp] := by
  rw [(D.s.atP p).O_def] at h
  have hi : IsIntegral 𝒪[(D.s.atP p).Fp] c :=
    (isIntegral_algHom_iff (IsScalarTower.toAlgHom 𝒪[(D.s.atP p).Fp] (D.s.atP p).Fp (D.s.atP p).Ep)
      (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep).injective).1 h
  exact PI.UnitaryGroupMassFormula.CntFormula.DeltaC.mem_of_isIntegral_fp (D.s.atP p) hi

theorem delta_unit (D : D7) (Z : LocDat D) :
    {p : PlF D | ¬ ∃ u : (𝒪[(D.s.atP p).Fp])ˣ, ((u : 𝒪[(D.s.atP p).Fp]) : (D.s.atP p).Fp) = Z.δ p}.Finite := by
  refine (Ideal.finite_factors (I := differentIdeal ℤ (𝓞 D.host.F)) ?_).subset ?_
  · exact differentIdeal_ne_bot
  intro p hp
  simp only [Set.mem_setOf_eq] at hp ⊢
  rw [Ideal.dvd_iff_le]
  intro x hx
  by_contra hxp
  apply hp
  obtain ⟨-, hδ, -, hO, -, -⟩ := Z.agree p
  have hspan := GlobalTheory.LocDiffGen.span_different_eq D Z p
  have himg : ∀ y : 𝓞 D.host.F, (D.s.atP p).ιE (algebraMap D.host.F D.host.E (y : D.host.F)) =
      algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((D.s.atP p).ιF (y : D.host.F)) := fun y => (D.s.atP p).compat _
  have hin : algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (Z.δ p) ∈ (D.s.atP p).O := by
    have hm : algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (Z.δ p) ∈ Submodule.span (Z.M p).L.O
        ((fun x : 𝓞 D.host.F => (D.s.atP p).ιE (algebraMap D.host.F D.host.E x)) ''
          (differentIdeal ℤ (𝓞 D.host.F) : Set (𝓞 D.host.F))) := by
      rw [hspan]; exact Submodule.mem_span_singleton_self _
    have key : ∀ v ∈ Submodule.span (Z.M p).L.O
        ((fun x : 𝓞 D.host.F => (D.s.atP p).ιE (algebraMap D.host.F D.host.E x)) ''
          (differentIdeal ℤ (𝓞 D.host.F) : Set (𝓞 D.host.F))), v ∈ (Z.M p).L.O := by
      intro v hv
      induction hv using Submodule.span_induction with
      | mem z hz =>
        obtain ⟨y, -, rfl⟩ := hz
        show (D.s.atP p).ιE (algebraMap D.host.F D.host.E (y : D.host.F)) ∈ (Z.M p).L.O
        rw [himg, hO]
        exact PI.CntNotIntW.algMap_mem_O D p _ (GlobalTheory.LocDiffGen.iF_int p y)
      | zero => exact zero_mem _
      | add a b _ _ ha hb => exact add_mem ha hb
      | smul c a _ ha => exact (Z.M p).L.O.mul_mem c.2 ha
    rw [← hO]
    exact key _ hm
  have hx2 : (D.s.atP p).ιE (algebraMap D.host.F D.host.E (x : D.host.F)) ∈
      (Z.M p).L.O ∙ algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (Z.δ p) := by
    rw [← hspan]
    exact Submodule.subset_span ⟨x, hx, rfl⟩
  obtain ⟨o, ho⟩ := Submodule.mem_span_singleton.1 hx2
  obtain ⟨hinvx, hx0⟩ := iF_unit p x hxp
  rw [himg] at ho
  have hinv : algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (Z.δ p)⁻¹ ∈ (D.s.atP p).O := by
    have e : algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (Z.δ p)⁻¹ =
        (o : (D.s.atP p).Ep) * algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((D.s.atP p).ιF (x : D.host.F))⁻¹ := by
      have ho' : (o : (D.s.atP p).Ep) * algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (Z.δ p) =
          algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((D.s.atP p).ιF (x : D.host.F)) := ho
      have h3 : algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (Z.δ p)⁻¹ =
          algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((D.s.atP p).ιF (x : D.host.F)) *
            algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (((D.s.atP p).ιF (x : D.host.F))⁻¹ * (Z.δ p)⁻¹) := by
        rw [← map_mul]; congr 1; field_simp
      rw [h3, ← ho', map_mul]
      have h4 : algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (Z.δ p) * algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (Z.δ p)⁻¹ = 1 := by
        rw [← map_mul, mul_inv_cancel₀ hδ, map_one]
      calc (o : (D.s.atP p).Ep) * algebraMap _ _ (Z.δ p) *
            (algebraMap _ _ ((D.s.atP p).ιF (x : D.host.F))⁻¹ * algebraMap _ _ (Z.δ p)⁻¹)
          = (o : (D.s.atP p).Ep) * algebraMap _ _ ((D.s.atP p).ιF (x : D.host.F))⁻¹ *
            (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (Z.δ p) * algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (Z.δ p)⁻¹) := by ring
        _ = _ := by rw [h4, mul_one]
    rw [e, ← hO]
    refine (Z.M p).L.O.mul_mem o.2 ?_
    rw [hO]
    exact PI.CntNotIntW.algMap_mem_O D p _ hinvx
  exact unit_of_mem hδ (memF_of p _ hin) (memF_of p _ hinv)

end Fin

section Main

variable {D : D7}

theorem cval_unit_fin (Z : LocDat D) :
    {p : PlF D | ¬ ∃ u : (𝒪[(D.s.atP p).Fp])ˣ, ((u : 𝒪[(D.s.atP p).Fp]) : (D.s.atP p).Fp) = cval Z p}.Finite := by
  refine ((delta_unit D Z).union (isUnit_unitAt D)).subset ?_
  intro p hp
  simp only [Set.mem_setOf_eq, Set.mem_union] at hp ⊢
  by_contra h
  push_neg at h
  obtain ⟨⟨u, hu⟩, ⟨v, hv⟩⟩ := h
  refine hp ⟨u * v, ?_⟩
  rw [cval, ← hu, ← hv, Units.val_mul, MulMemClass.coe_mul]

theorem exists_gen (D : D7) (Z : LocDat D) (N N' : ℕ) (hN : 0 < N) (hN' : 0 < N')
    (F00 : LFlag (VS D) D.R.rS (N : D.host.E)) (F'0 : LFlag (VS D) D.R.rS (N' : D.host.E))
    (FP : ∀ p : PlF D, Formalism.MainNotions.S.LocNG.FPair (locH Z p) D.R.rS)
    (hFP : ∀ p, AtBase Z p F00 F'0 N N' (FP p) ∧ (FP p).RelG (Formalism.MainNotions.S.LocNG.theta (Z.M p))) :
    ∃ G : GFrames (placesOf Z) D.R.rS D.R.k, Nonempty (GCoord Z F00 F'0 FP G) := by
  obtain ⟨y, hy⟩ := Formalism.L2.SG.Pf.Cnt.R1.dual_of_flag D hN F00.fl
  obtain ⟨y', hy'⟩ := Formalism.L2.SG.Pf.Cnt.R1.dual_of_flag D hN' F'0.fl
  have hloc : ∀ p, ∃ S : Frames (Z.M p).L D.R.rS D.R.k,
      S.Hm = Matrix.of (fun i j => (locH Z p).h (bL D p i) (bL D p j)) ∧
      S.es = (fun j : Fin D.R.rS => (bL D p).equivFun
        (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cval Z p ^ (D.R.rS - (j : ℕ))) • baseChange₂ D p (y j))) ∧
      S.es' = (fun j : Fin D.R.rS => (bL D p).equivFun
        (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cval Z p ^ (D.R.rS - (j : ℕ))) • baseChange₂ D p (y' j))) ∧
      S.gg = (Z.M p).split.isSome ∧ ∃ c : WCoord (FP p) S, c.e = (bL D p).equivFun := by
    intro p
    obtain ⟨⟨hA, hB, -, -⟩, hR⟩ := hFP p
    refine loc_ex (Z.agree p).1 (locH Z p) D.R.rS D.R.k (FP p) hR (bL D p) _ _ ?_ ?_ ?_ ?_
    · intro a j; rw [hA]; exact loc_dual Z p F00.fl y hy a j
    · intro a j; rw [hB]; exact loc_dual Z p F'0.fl y' hy' a j
    · intro i j; exact loc_iso Z p _ _ F00.fl y hy i j
    · intro i j; exact loc_iso Z p _ _ F'0.fl y' hy' i j
  choose S hS using hloc
  choose W hW using fun p => (hS p).2.2.2.2
  have heq : ∀ p, (bL D p).equivFun = eL D p := fun p => Module.Basis.equivFun_ofEquivFun _
  refine ⟨
    { Hm := HmG D
      f := fun a => eG D (frame F00 a)
      f' := fun a => eG D (frame F'0 a)
      es := fun a => eG D (y a)
      es' := fun a => eG D (y' a)
      c := fun p => Units.mk0 (cval Z p) (cval_ne Z p)
      S := S
      Hm_eq := fun p => by rw [(hS p).1, gram_bL]; rfl
      f_eq := ?_
      f'_eq := ?_
      es_eq := ?_
      es'_eq := ?_
      c_unit := ?_
      gg_fin := ?_ }, ⟨
    { e := eG D
      h_eq := h_eqG
      f_eq := fun a => rfl
      f'_eq := fun a => rfl
      c := W
      compat := ?_
      c_eq := ?_ }⟩⟩
  · intro p a
    obtain ⟨⟨hA, -, -, -⟩, -⟩ := hFP p
    rw [(W p).f_eq, hW p, hA, heq, ← eL_bcP Z]
    show algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cval Z p ^ (D.R.rS - (a : ℕ))) •
      eL D p (frFac Z.δ p a • baseChange₂ D p (frame F00 a)) = eL D p (baseChange₂ D p (frame F00 a))
    rw [LinearEquiv.map_smul, smul_smul, frFac_mul, one_smul]
  · intro p a
    obtain ⟨⟨-, hB, -, -⟩, -⟩ := hFP p
    rw [(W p).f'_eq, hW p, hB, heq, ← eL_bcP Z]
    show algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cval Z p ^ (D.R.rS - (a : ℕ))) •
      eL D p (frFac Z.δ p a • baseChange₂ D p (frame F'0 a)) = eL D p (baseChange₂ D p (frame F'0 a))
    rw [LinearEquiv.map_smul, smul_smul, frFac_mul, one_smul]
  · intro p a
    rw [(hS p).2.1]
    show (bL D p).equivFun _ = _
    rw [heq, LinearEquiv.map_smul, eL_bcP Z]
    rfl
  · intro p a
    rw [(hS p).2.2.1]
    show (bL D p).equivFun _ = _
    rw [heq, LinearEquiv.map_smul, eL_bcP Z]
    rfl
  · exact cval_unit_fin Z
  · refine (split_fin D).subset ?_
    intro p hp
    simp only [Set.mem_setOf_eq] at hp ⊢
    rw [← split_isSome Z p, ← (hS p).2.2.2.1]
    exact hp
  · intro p x
    have h1 := congrArg (fun e : Vp D p ≃ₗ[(D.s.atP p).Ep] (Fin (D.R.k + 2 * D.R.rS + 1) → (D.s.atP p).Ep) =>
      e (baseChange₂ D p x)) ((hW p).trans (heq p))
    exact h1.trans (eL_bcP Z p x)
  · intro p
    show algebraMap _ _ (cval Z p) = _
    rw [cval_E]

theorem exists_global_coords : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Formalism.MainNotions.S.Cnt.Stand D u u' → ∀ (w : Point D.host.E (D.R.rS + 1)) (F00 : LFlag (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (F'0 : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (FP : ∀ p : PlF D, LocNG.FPair (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS), ZhatOM (ZhatL F00 F'0) = ptMat w → Gval F00 F'0 ≠ 0 → (∀ p, AtBase (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p F00 F'0 (Tu D u) (Tu D u') (FP p) ∧ (FP p).RelG (LocNG.theta (Y.M p))) → ∃ G : GFrames (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) D.R.rS D.R.k, Nonempty (GCoord (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) F00 F'0 FP G) := by
  intro D X Y u u' hst w F00 F'0 FP _ _ hFP
  have hN : 0 < Tu D u := by have := hst.2.2.2.1; omega
  have hN' : 0 < Tu D u' := by have := hst.2.2.2.2.1; omega
  exact exists_gen D _ _ _ hN hN' F00 F'0 FP hFP

end Main

end GlobalTheory.HL.GCoordEx
