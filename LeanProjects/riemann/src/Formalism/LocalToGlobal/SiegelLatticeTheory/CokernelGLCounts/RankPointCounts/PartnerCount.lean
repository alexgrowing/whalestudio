import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LsDatumBTup
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LocalSplitTypeMixedSecond
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.PairValPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.GenericRatioOfBoundHolds
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LocModel
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LsDatumACut
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AtPtRel

noncomputable section

namespace Formalism.L2.SG.Pf.PCount

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut
  Formalism.L2.SG.LsDatumB
open Classical ValuativeRel
open Formalism.L2.SG.Pf.AtPt Formalism.L2.SG.TermLoc Formalism.MainNotions.S.Lat

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Defs

variable {D : Formalism.BasicNotions.D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
  (δ : ∀ p : PlF D, (D.s.atP p).Fp)

def AtMat (w : Point D.host.E (D.R.rS + 1)) (Z : PairVal.MatR D) : Prop :=
  ∃ L U : PairVal.MatR D, IsLoUni L ∧ IsUpUni U ∧ ZhatOM Z = L * ptMat w * U

def tupZ (u u' : D.what₂.Word) (Z : PairVal.MatR D) (p : PlF D) : Set (MatP D p) :=
  kkOrb M p (CntLocal.ZZP (M := M) δ u u' p Z * LsDatumB.sgnP p)

variable {M δ}

theorem locT_eq_tupZ {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
    {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)} (γ : TermDef.Term D u u' F0 what₂) :
    locT M δ γ = tupZ M δ u u' (zT γ) := rfl

variable {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

def frPart (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D) :
    Set (Set (LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E))) :=
  {O | ∃ F' ∈ CntLocal.EZ (D := D) ((Tu D u' : ℕ) : D.host.E) F0 γ.lam Z,
    (∃ γ' : TermDef.Term D u u' F0 what₂, Corank.TermScal D γ γ' ∧
      Rep γ'.lam (lf D F0) (PD D γ'.lam (lf D F0) u') γ'.cls F') ∧
    O = {F'' | F'' ∈ CntLocal.EZ (D := D) ((Tu D u' : ℕ) : D.host.E) F0 γ.lam Z ∧ CntLocal.NilradicalFlagMoved F0 γ.lam F' F''}}

end Defs

section Steps

variable {D : Formalism.BasicNotions.D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
  (δ : ∀ p : PlF D, (D.s.atP p).Fp) (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u))
  (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))

def Restr : Prop :=
  ∀ (γ' : TermDef.Term D u u' F0 what₂) (w' : Point D.host.E (D.R.rS + 1)), EligAt γ' w' →
    {p | locT M δ γ' p ≠ x0L M δ (D.mem u).A.T (D.mem u').A.T p w'}.Finite

def Exist : Prop :=
  ∀ w' : Point D.host.E (D.R.rS + 1), Gpt (D.mem u).A.T (D.mem u').A.T w' ≠ 0 →
  ∀ x : Rst (fun p => x0L M δ (D.mem u).A.T (D.mem u').A.T p w'),
    (∀ p, IsLCls M δ (D.mem u).A.T (D.mem u').A.T p w' (x.1 p)) →
    ∃ Z : PairVal.MatR D, AtMat w' Z ∧ tupZ M δ u u' Z = x.1

def SumFr : Prop :=
  ∀ (γ : TermDef.Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1)), EligAt γ w →
  ∀ w' : Point D.host.E (D.R.rS + 1), Gpt (D.mem u).A.T (D.mem u').A.T w' ≠ 0 → kind w' = kind w →
  ∀ Z : PairVal.MatR D, AtMat w' Z →
    (frPart γ Z).Finite ∧
    HasSum (fun γ' : {γ' : TermDef.Term D u u' F0 what₂ //
        (Corank.TermScal D γ γ' ∧ EligAt γ' w') ∧ locT M δ γ' = tupZ M δ u u' Z} =>
        ((PairVal.orbT D u u' F0 what₂ γ'.1 (zT γ'.1)).ncard : ℂ))
      ((frPart γ Z).ncard : ℂ)

def FrCount : Prop :=
  ∀ (γ : TermDef.Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1)), EligAt γ w →
  ∀ w' : Point D.host.E (D.R.rS + 1), Gpt (D.mem u).A.T (D.mem u').A.T w' ≠ 0 → kind w' = kind w →
  ∀ Z : PairVal.MatR D, AtMat w' Z →
    ((frPart γ Z).ncard : ℂ) = ∏ᶠ p, kL M δ (D.mem u).A.T (D.mem u').A.T p w' (thT M δ γ p) (tupZ M δ u u' Z p)

end Steps

section IntMat

variable {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E] [Algebra F E]
  [TopologicalSpace E] [MeasurableSpace E] {Mp : Loc.Model F E} {n : ℕ}

theorem intLow_mul {l l' : Matrix (Fin n) (Fin n) E} (h : TieN.IntLow Mp l) (h' : TieN.IntLow Mp l') :
    TieN.IntLow Mp (l * l') := by
  have hm := isLo_mul (R := E) (n := n) ⟨h.1, h.2.1⟩ ⟨h'.1, h'.2.1⟩
  refine ⟨hm.1, hm.2, fun a b => ?_⟩
  rw [Matrix.mul_apply]
  exact Subring.sum_mem _ fun c _ => Subring.mul_mem _ (h.2.2 a c) (h'.2.2 c b)

theorem intUp_mul {l l' : Matrix (Fin n) (Fin n) E} (h : TieN.IntUp Mp l) (h' : TieN.IntUp Mp l') :
    TieN.IntUp Mp (l * l') := by
  have hm := isUp_mul (R := E) (n := n) ⟨h.1, fun a b hab => h.2.1 b a hab⟩ ⟨h'.1, fun a b hab => h'.2.1 b a hab⟩
  refine ⟨hm.1, fun a b hab => hm.2 b a hab, fun a b => ?_⟩
  rw [Matrix.mul_apply]
  exact Subring.sum_mem _ fun c _ => Subring.mul_mem _ (h.2.2 a c) (h'.2.2 c b)

theorem intLow_conj (d d' : Fin n → E) (hd : ∀ a, d a * d' a = 1) (hdR : ∀ a, d a ∈ Mp.R) (hd'R : ∀ a, d' a ∈ Mp.R)
    {L : Matrix (Fin n) (Fin n) E} (hL : IsLo L) (hLR : ∀ a b, L a b ∈ Mp.R) :
    TieN.IntLow Mp (Matrix.diagonal d * L * Matrix.diagonal d') := by
  have hc := isLo_conj hL d d' hd
  refine ⟨hc.1, hc.2, fun a b => ?_⟩
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  exact Subring.mul_mem _ (Subring.mul_mem _ (hdR a) (hLR a b)) (hd'R b)

theorem intUp_conj (d d' : Fin n → E) (hd : ∀ a, d a * d' a = 1) (hdR : ∀ a, d a ∈ Mp.R) (hd'R : ∀ a, d' a ∈ Mp.R)
    {U : Matrix (Fin n) (Fin n) E} (hU : IsUp U) (hUR : ∀ a b, U a b ∈ Mp.R) :
    TieN.IntUp Mp (Matrix.diagonal d * U * Matrix.diagonal d') := by
  have hc := isUp_conj hU d d' hd
  refine ⟨hc.1, fun a b hab => hc.2 b a hab, fun a b => ?_⟩
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  exact Subring.mul_mem _ (Subring.mul_mem _ (hdR a) (hUR a b)) (hd'R b)

end IntMat

section Orb

variable {D : Formalism.BasicNotions.D7} {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep}

theorem kkOrb_eq_of {p : PlF D} {X Y l ρ l' ρ' : MatP D p} (hl : TieN.IntLow (M p) l) (hρ : TieN.IntUp (M p) ρ)
    (hl' : TieN.IntLow (M p) l') (hρ' : TieN.IntUp (M p) ρ') (h1 : Y = l * X * ρ) (h2 : X = l' * Y * ρ') :
    kkOrb M p Y = kkOrb M p X := by
  ext Y'
  constructor
  · rintro ⟨a, b, ha, hb, rfl⟩
    exact ⟨a * l, ρ * b, intLow_mul ha hl, intUp_mul hρ hb, by rw [h1]; simp only [Matrix.mul_assoc]⟩
  · rintro ⟨a, b, ha, hb, rfl⟩
    exact ⟨a * l', ρ' * b, intLow_mul ha hl', intUp_mul hρ' hb, by rw [h2]; simp only [Matrix.mul_assoc]⟩

end Orb

section Tri

variable {K : Type*} [CommRing K] {n : ℕ}

theorem isLo_of_uni {L : Matrix (Fin n) (Fin n) K} (h : IsLoUni L) : IsLo L :=
  ⟨fun a => (h a a).2 rfl, fun a b hab => (h a b).1 hab⟩

theorem isUp_of_uni {U : Matrix (Fin n) (Fin n) K} (h : IsUpUni U) : IsUp U :=
  ⟨fun a => (h a a).2 rfl, fun a b hab => (h b a).1 hab⟩

theorem isUp_inv {U : Matrix (Fin n) (Fin n) K} (h : IsUp U) : IsUp U⁻¹ := by
  obtain ⟨h0, h1⟩ := inv_unitri U (fun a b hab => h.2 b a hab) h.1
  exact ⟨h1, fun a b hab => h0 b a hab⟩

theorem isLo_inv {L : Matrix (Fin n) (Fin n) K} (h : IsLo L) : IsLo L⁻¹ := by
  have h1 : IsUp L.transpose := isUp_transpose h
  have h2 := isUp_inv h1
  rw [← Matrix.transpose_nonsing_inv] at h2
  exact ⟨fun a => h2.1 a, fun a b hab => h2.2 a b hab⟩

theorem det_up' {U : Matrix (Fin n) (Fin n) K} (h : IsUp U) : U.det = 1 := by
  have hbt : U.BlockTriangular id := fun i j hij => h.2 j i hij
  rw [Matrix.det_of_isUpperTriangular hbt]; simp [h.1]

theorem det_lo' {L : Matrix (Fin n) (Fin n) K} (h : IsLo L) : L.det = 1 := by
  rw [← Matrix.det_transpose]; exact det_up' (isUp_transpose h)

end Tri

section Local

variable {D : Formalism.BasicNotions.D7}

theorem zzp_sgn_ord (Zd : LocDat D) (u u' : D.what₂.Word) (p : PlF D) (hM : (Zd.M p).split = none)
    (Z : PairVal.MatR D) :
    CntLocal.ZZP (M := Zd.M) Zd.δ u u' p Z * LsDatumB.sgnP p =
      Matrix.diagonal (fun a => algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cf Zd p a)) *
        (Z * Sg D.host.E D.R.rS).map (D.s.atP p).ιE *
        Matrix.diagonal (fun a => algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cf Zd p a)) := by
  have e0 : CntLocal.ZZP (M := Zd.M) Zd.δ u u' p Z = CntLocal.ZhatLoc Zd.M Zd.δ p Z := by
    simp only [CntLocal.ZZP, Loc.HermSp.ZZplusOf, hM]
  rw [e0]
  ext a b
  simp only [CntLocal.ZhatLoc, LsDatumB.sgnP, Sg, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.map_apply,
    Matrix.of_apply, Zd.hcj p, frFac_eq, cf, cj_alg, map_mul, map_pow, map_neg, map_one]
  ring

end Local

section LocalOrb

variable {D : Formalism.BasicNotions.D7} {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep}
  {δ : ∀ p : PlF D, (D.s.atP p).Fp}

theorem alg_mem_O' (p : PlF D) {c : (D.s.atP p).Fp} (hc : c ∈ 𝒪[(D.s.atP p).Fp]) :
    algebraMap (D.s.atP p).Fp (D.s.atP p).Ep c ∈ (D.s.atP p).O := by
  rw [(D.s.atP p).O_def]
  have h := isIntegral_algebraMap (R := 𝒪[(D.s.atP p).Fp]) (A := (D.s.atP p).Ep) (x := ⟨c, hc⟩)
  rw [IsScalarTower.algebraMap_apply 𝒪[(D.s.atP p).Fp] (D.s.atP p).Fp (D.s.atP p).Ep] at h
  exact h

theorem iotaE_alg (p : PlF D) (x : D.host.F) :
    (D.s.atP p).ιE (algebraMap D.host.F D.host.E x) = algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((D.s.atP p).ιF x) :=
  (D.s.atP p).compat x

theorem yP_int (Zd : LocDat D) (p : PlF D) (hd1 : Zd.δ p ∈ 𝒪[(D.s.atP p).Fp])
    (hd2 : (Zd.δ p)⁻¹ ∈ 𝒪[(D.s.atP p).Fp])
    (hu1 : (D.s.atP p).ιE ((uP p : ℚ) : D.host.E) ∈ (D.s.atP p).O)
    (hu2 : (D.s.atP p).ιE (((uP p : ℚ) : D.host.E))⁻¹ ∈ (D.s.atP p).O) :
    algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (yP Zd p) ∈ (D.s.atP p).O ∧
      algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (yP Zd p)⁻¹ ∈ (D.s.atP p).O := by
  have eu : ((uP p : ℚ) : D.host.E) = algebraMap D.host.F D.host.E ((uP p : ℚ) : D.host.F) :=
    (map_ratCast (algebraMap D.host.F D.host.E) _).symm
  have eu' : (((uP p : ℚ) : D.host.E))⁻¹ = algebraMap D.host.F D.host.E (((uP p : ℚ) : D.host.F))⁻¹ := by
    rw [map_inv₀, eu]
  rw [eu, iotaE_alg] at hu1
  rw [eu', iotaE_alg, map_inv₀] at hu2
  unfold yP
  refine ⟨?_, ?_⟩
  · rw [map_mul]; exact Subring.mul_mem _ (alg_mem_O' p hd1) hu1
  · rw [mul_inv, map_mul]; exact Subring.mul_mem _ (alg_mem_O' p hd2) hu2

theorem tupZ_eq_x0L_at (hA : ∀ p, Agree δ M p) (u u' : D.what₂.Word) {w : Point D.host.E (D.R.rS + 1)}
    {Z L U : PairVal.MatR D} (hL : IsLo L) (hU : IsUp U) (hZ : Z * Sg D.host.E D.R.rS = L * ptMat w * U)
    (p : PlF D) (hM : (M p).split = none) (hd1 : δ p ∈ 𝒪[(D.s.atP p).Fp]) (hd2 : (δ p)⁻¹ ∈ 𝒪[(D.s.atP p).Fp])
    (hu1 : (D.s.atP p).ιE ((uP p : ℚ) : D.host.E) ∈ (D.s.atP p).O)
    (hu2 : (D.s.atP p).ιE (((uP p : ℚ) : D.host.E))⁻¹ ∈ (D.s.atP p).O)
    (hent : ∀ a b, (D.s.atP p).ιE (L a b) ∈ (D.s.atP p).O ∧ (D.s.atP p).ιE (U a b) ∈ (D.s.atP p).O ∧
      (D.s.atP p).ιE (L⁻¹ a b) ∈ (D.s.atP p).O ∧ (D.s.atP p).ιE (U⁻¹ a b) ∈ (D.s.atP p).O) :
    tupZ M δ u u' Z p = x0L M δ (D.mem u).A.T (D.mem u').A.T p w := by
  set Zd : LocDat D := ⟨δ, M, hA⟩
  have hR : (D.s.atP p).split = none := by
    have h := (hA p).2.2.2.2.2
    rw [hM] at h
    cases h' : (D.s.atP p).split with
    | none => rfl
    | some sg => rw [h'] at h; exact h.elim
  have hRO : (M p).R = (D.s.atP p).O := by
    simp only [Loc.Model.R, hM]; exact (hA p).2.2.2.1
  set ι := (D.s.atP p).ιE
  set al := algebraMap (D.s.atP p).Fp (D.s.atP p).Ep
  set fr : Fin (D.R.rS + 1) → (D.s.atP p).Ep := fun a => al (cf Zd p a)
  set fri : Fin (D.R.rS + 1) → (D.s.atP p).Ep := fun a => al (cfi Zd p a)
  have hfr : ∀ a, fri a * fr a = 1 := fun a => by simp only [fr, fri, ← map_mul, cfi_cf, map_one]
  have hfr' : ∀ a, fr a * fri a = 1 := fun a => by simp only [fr, fri, ← map_mul, cf_cfi, map_one]
  obtain ⟨hy1, hy2⟩ := yP_int Zd p hd1 hd2 hu1 hu2
  have hfrR : ∀ a, fr a ∈ (M p).R := fun a => by
    rw [hRO]; simp only [fr, cf, map_pow]; exact Subring.pow_mem _ hy2 _
  have hfriR : ∀ a, fri a ∈ (M p).R := fun a => by
    rw [hRO]; simp only [fri, cfi, map_pow]; exact Subring.pow_mem _ hy1 _
  have hmod : Matrix.diagonal fr * (ptMat w).map ι * Matrix.diagonal fr =
      modMat δ (D.mem u).A.T (D.mem u').A.T p w := by
    ext a b
    rw [modMat_apply', Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.map_apply, ptMat_apply']
    by_cases hb : b = sgF w a
    · rw [if_pos hb, if_pos hb, modMat_blk Zd]
      simp only [twist, qE, tau0, hR, Ring.inverse_one, mul_one, ite_self, sub_zero, map_mul, fr]
      subst hb
      ring
    · rw [if_neg hb, if_neg hb, map_zero, mul_zero, zero_mul]
  have hY : CntLocal.ZZP (M := M) δ u u' p Z * LsDatumB.sgnP p =
      Matrix.diagonal fr * (Z * Sg D.host.E D.R.rS).map ι * Matrix.diagonal fr :=
    zzp_sgn_ord Zd u u' p hM Z
  have hLu : IsUnit L.det := by rw [det_lo' hL]; exact isUnit_one
  have hUu : IsUnit U.det := by rw [det_up' hU]; exact isUnit_one
  have hP : ptMat w = L⁻¹ * (Z * Sg D.host.E D.R.rS) * U⁻¹ := by
    rw [hZ, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul L hLu, Matrix.one_mul,
      Matrix.mul_assoc, Matrix.mul_nonsing_inv U hUu, Matrix.mul_one]
  have hent' : ∀ (X : PairVal.MatR D), (∀ a b, ι (X a b) ∈ (D.s.atP p).O) → ∀ a b, X.map ι a b ∈ (M p).R :=
    fun X hX a b => by rw [hRO]; exact hX a b
  unfold tupZ x0L
  refine kkOrb_eq_of (l := Matrix.diagonal fr * L.map ι * Matrix.diagonal fri)
    (ρ := Matrix.diagonal fri * U.map ι * Matrix.diagonal fr)
    (l' := Matrix.diagonal fr * L⁻¹.map ι * Matrix.diagonal fri)
    (ρ' := Matrix.diagonal fri * U⁻¹.map ι * Matrix.diagonal fr)
    (intLow_conj fr fri hfr' hfrR hfriR (isLo_map ι hL) (hent' L fun a b => (hent a b).1))
    (intUp_conj fri fr hfr hfriR hfrR (isUp_map ι hU) (hent' U fun a b => (hent a b).2.1))
    (intLow_conj fr fri hfr' hfrR hfriR (isLo_map ι (isLo_inv hL)) (hent' L⁻¹ fun a b => (hent a b).2.2.1))
    (intUp_conj fri fr hfr hfriR hfrR (isUp_map ι (isUp_inv hU)) (hent' U⁻¹ fun a b => (hent a b).2.2.2)) ?_ ?_
  · rw [hY, hZ, Matrix.map_mul, Matrix.map_mul, regroup fr fri hfr, hmod]
  · rw [← hmod, hP, Matrix.map_mul, Matrix.map_mul, regroup fr fri hfr, ← hY]

theorem tupZ_restr (hA : ∀ p, Agree δ M p) (u u' : D.what₂.Word) {w : Point D.host.E (D.R.rS + 1)}
    {Z : PairVal.MatR D} (hZ : AtMat w Z)
    (hgood : ∀ᶠ p in Filter.cofinite, (M p).split = none ∧
      (δ p ∈ 𝒪[(D.s.atP p).Fp] ∧ (δ p)⁻¹ ∈ 𝒪[(D.s.atP p).Fp]) ∧
      ((D.s.atP p).ιE ((uP p : ℚ) : D.host.E) ∈ (D.s.atP p).O ∧
        (D.s.atP p).ιE (((uP p : ℚ) : D.host.E))⁻¹ ∈ (D.s.atP p).O))
    (hint : ∀ x : D.host.E, ∀ᶠ p in Filter.cofinite, (D.s.atP p).ιE x ∈ (D.s.atP p).O) :
    {p | tupZ M δ u u' Z p ≠ x0L M δ (D.mem u).A.T (D.mem u').A.T p w}.Finite := by
  obtain ⟨L, U, hL, hU, e⟩ := hZ
  have hL' := isLo_of_uni hL
  have hU' := isUp_of_uni hU
  have hZ' : Z * Sg D.host.E D.R.rS = L * ptMat w * U := by rw [← zhatOM_eq]; exact e
  have hE : ∀ᶠ p in Filter.cofinite, ∀ a b, (D.s.atP p).ιE (L a b) ∈ (D.s.atP p).O ∧
      (D.s.atP p).ιE (U a b) ∈ (D.s.atP p).O ∧ (D.s.atP p).ιE (L⁻¹ a b) ∈ (D.s.atP p).O ∧
      (D.s.atP p).ιE (U⁻¹ a b) ∈ (D.s.atP p).O := by
    refine Filter.eventually_all.2 fun a => Filter.eventually_all.2 fun b => ?_
    exact (hint _).and ((hint _).and ((hint _).and (hint _)))
  have hev : ∀ᶠ p in Filter.cofinite, tupZ M δ u u' Z p = x0L M δ (D.mem u).A.T (D.mem u').A.T p w := by
    filter_upwards [hgood, hE] with p hp he
    exact tupZ_eq_x0L_at hA u u' hL' hU' hZ' p hp.1 hp.2.1.1 hp.2.1.2 hp.2.2.1 hp.2.2.2 he
  exact Filter.eventually_cofinite.1 hev

end LocalOrb

section TermRestr

variable {D : Formalism.BasicNotions.D7} {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

theorem atMat_zT (hN : PairVal.NormRepExists D u u' F0 what₂) (hrows : IsRowReps D F0 what₂)
    {γ : TermDef.Term D u u' F0 what₂} {w : Point D.host.E (D.R.rS + 1)} (hγ : EligAt γ w) (hrel : γ.relevant) :
    AtMat w (zT γ) := by
  obtain ⟨⟨hgen, -⟩, hat⟩ := hγ
  obtain ⟨y, hy⟩ := hN γ w hat hrel hgen
  have hex : ∃ x : Point D.host.E (D.R.rS + 1) × LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E) × PairVal.MatR D ×
      PairVal.MatR D, PairVal.NormRep γ x.1 x.2.1 x.2.2.1 x.2.2.2 := ⟨(w, y), hy⟩
  have hn : nrep γ = some hex.choose := dif_pos hex
  obtain ⟨hRep, -, hL, hU, e⟩ := hex.choose_spec
  have hz : zT γ = ZhatL (lf D F0) hex.choose.2.1 := by unfold zT; rw [hn]
  obtain ⟨F₁, hR₁, -, hc₁⟩ := hat
  have hw : w = hex.choose.1 := pt_eq_of_cells cell_point_uniqueness (Formalism.L2.SG.Closed.TermFun_holds D u u') hrows γ
    hR₁ hRep hc₁ ⟨_, _, hL, hU, e⟩
  exact ⟨_, _, hL, hU, by rw [hz, hw]; exact e⟩

end TermRestr

section TauInv

variable {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E] [Algebra F E]
  [TopologicalSpace E] [MeasurableSpace E] (M : Loc.Model F E) {m : ℕ}

def matLR (Y : M.Mat m) (l ρ : Matrix (Fin m) (Fin m) M.R) (hl : IsUnit l.det) (hρ : IsUnit ρ.det) : M.Mat m :=
  ⟨l * Y.Z * ρ, by
    have e1 : ((l * Y.Z * ρ).map M.R.subtype).det = M.R.subtype l.det * (Y.Z.map M.R.subtype).det *
        M.R.subtype ρ.det := by
      rw [Matrix.map_mul, Matrix.map_mul, Matrix.det_mul, Matrix.det_mul, RingHom.map_det, RingHom.map_det]
      rfl
    rw [e1]
    exact ((hl.map _).mul Y.unit).mul (hρ.map _)⟩

theorem range_matLR (Y : M.Mat m) (l ρ : Matrix (Fin m) (Fin m) M.R) (hl : IsUnit l.det) (hρ : IsUnit ρ.det) :
    LinearMap.range (matLR M Y l ρ hl hρ).Z.mulVecLin = (LinearMap.range Y.Z.mulVecLin).map l.mulVecLin := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    refine ⟨Y.Z.mulVec (ρ.mulVec y), ⟨_, rfl⟩, ?_⟩
    simp only [matLR, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, Matrix.mul_assoc]
  · rintro ⟨_, ⟨y, rfl⟩, rfl⟩
    refine ⟨ρ⁻¹.mulVec y, ?_⟩
    simp only [matLR, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ hρ, Matrix.mul_one]

def cokLR (Y : M.Mat m) (l ρ : Matrix (Fin m) (Fin m) M.R) (hl : IsUnit l.det) (hρ : IsUnit ρ.det) :
    M.Cok Y ≃ₗ[M.R] M.Cok (matLR M Y l ρ hl hρ) :=
  Submodule.Quotient.equiv _ _ (Matrix.toLinearEquiv' l (Matrix.invertibleOfIsUnitDet l hl)) (by
    rw [range_matLR]; rfl)

theorem cokLR_mk (Y : M.Mat m) (l ρ : Matrix (Fin m) (Fin m) M.R) (hl : IsUnit l.det) (hρ : IsUnit ρ.det)
    (x : Fin m → M.R) :
    cokLR M Y l ρ hl hρ (Submodule.Quotient.mk x) = Submodule.Quotient.mk (l.mulVec x) := rfl

theorem unit_map {l : Matrix (Fin m) (Fin m) M.R} (hl : IsUnit l.det) : IsUnit (l.map M.R.subtype).det := by
  have : (l.map M.R.subtype).det = M.R.subtype l.det := by rw [RingHom.map_det]; rfl
  rw [this]; exact hl.map _

def isoLR (Y : M.Mat (m + 1)) (l ρ : Matrix (Fin (m + 1)) (Fin (m + 1)) M.R) (hl : IsUnit l.det) (hρ : IsUnit ρ.det)
    (hle : l.mulVec (Pi.single (Fin.last m) 1) = Pi.single (Fin.last m) 1)
    (hρe : ∀ b, (ρ.map M.R.subtype)⁻¹ (Fin.last m) b = if b = Fin.last m then 1 else 0) :
    M.Iso Y (matLR M Y l ρ hl hρ) :=
  ⟨cokLR M Y l ρ hl hρ, by
    show cokLR M Y l ρ hl hρ (Submodule.Quotient.mk _) = Submodule.Quotient.mk _
    rw [cokLR_mk, hle], by
    intro v
    induction v using Submodule.Quotient.induction_on with
    | H x =>
      rw [cokLR_mk]
      simp only [Loc.Model.lam, Submodule.liftQ_apply, Loc.Model.lamRaw, LinearMap.coe_comp, Function.comp_apply,
        Submodule.mkQ_apply, LinearMap.restrictScalars_apply, Matrix.mulVecLin_apply, LinearMap.proj_apply]
      congr 1
      have hxl : (LinearMap.compLeft (Algebra.linearMap M.R E) (Fin (m + 1))) (l.mulVec x) =
          (l.map M.R.subtype).mulVec ((LinearMap.compLeft (Algebra.linearMap M.R E) (Fin (m + 1))) x) := by
        funext i
        simp only [LinearMap.compLeft_apply, Function.comp_apply, Algebra.linearMap_apply]
        exact RingHom.map_mulVec M.R.subtype l x i
      rw [hxl]
      have hm : ((matLR M Y l ρ hl hρ).Z.map M.R.subtype) =
          l.map M.R.subtype * Y.Z.map M.R.subtype * ρ.map M.R.subtype := by
        simp only [matLR, Matrix.map_mul]
      rw [hm, Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_assoc,
        Matrix.nonsing_inv_mul _ (unit_map M hl), Matrix.mul_one, ← Matrix.mulVec_mulVec]
      rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single (Fin.last m)]
      · rw [hρe, if_pos rfl, one_mul]
      · intro b _ hb; rw [hρe, if_neg hb, zero_mul]
      · intro h; exact absurd (Finset.mem_univ _) h⟩

theorem nIso_congr {Y₁ Y₁' Y₂ Y₂' : M.Mat (m + 1)} (h₁ : M.Iso Y₁ Y₁') (h₂ : M.Iso Y₂ Y₂') :
    M.nIso Y₁ Y₂ = M.nIso Y₁' Y₂' := by
  unfold Loc.Model.nIso
  refine Nat.card_congr
    { toFun := fun φ => ⟨(h₁.1.symm.trans φ.1).trans h₂.1, ?_, ?_⟩
      invFun := fun ψ => ⟨(h₁.1.trans ψ.1).trans h₂.1.symm, ?_, ?_⟩
      left_inv := fun φ => Subtype.ext (LinearEquiv.ext fun v => by simp)
      right_inv := fun ψ => Subtype.ext (LinearEquiv.ext fun v => by simp) }
  · have e1 : h₁.1.symm (M.eCls Y₁') = M.eCls Y₁ := (LinearEquiv.symm_apply_eq _).2 h₁.2.1.symm
    simp [e1, φ.2.1, h₂.2.1]
  · intro v
    simp only [LinearEquiv.trans_apply]
    rw [h₂.2.2, φ.2.2, ← h₁.2.2 (h₁.1.symm v), LinearEquiv.apply_symm_apply]
  · have e1 : h₂.1.symm (M.eCls Y₂') = M.eCls Y₂ := (LinearEquiv.symm_apply_eq _).2 h₂.2.1.symm
    simp [h₁.2.1, ψ.2.1, e1]
  · intro v
    simp only [LinearEquiv.trans_apply]
    rw [← h₂.2.2 (h₂.1.symm (ψ.1 (h₁.1 v))), LinearEquiv.apply_symm_apply, ψ.2.2, h₁.2.2]

end TauInv

section FrCut

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

def repF (γ : TermDef.Term D u u' F0 what₂) : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E) :=
  match nrep γ with
  | some x => x.2.1
  | none => (Quot.out γ.cls).1

def tLoc (p : PlF D) (γ : TermDef.Term D u u' F0 what₂) : Loc.Term (Vp D p) (Zd.M p) D.R.rS :=
  locTerm Zd p γ.lam (lf D F0) (repF γ) (Tu D u) (Tu D u')

def locF' (p : PlF D) {T' : D.host.E} (F' : LFlag (VS D) D.R.rS T') : Fin (D.R.rS + 1) → Vp D p :=
  fun b => (TermLoc.sgnP' D p b * frFac Zd.δ p b) • baseChange₂ D p (frame F' b)

def locSet (p : PlF D) (t₁ : Loc.Term (Vp D p) (Zd.M p) D.R.rS) (f₂' : Fin (D.R.rS + 1) → Vp D p)
    (φ : (locH Zd p).Wb t₁.f ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb t₁.f)
    (φ' : (locH Zd p).Wb t₁.f' ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb f₂') : Set (Submodule (Zd.M p).L.O (Vp D p)) :=
  {Λ₂ | (locH Zd p).IsGeneric ⟨Λ₂, t₁.f, f₂', t₁.T, t₁.T'⟩ ∧
    (locH Zd p).Respects t₁ ⟨Λ₂, t₁.f, f₂', t₁.T, t₁.T'⟩ φ φ'}

variable (u u' F0 what₂)

def FrGlob : Prop :=
  ∀ (γ : TermDef.Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1)), EligAt γ w →
  ∀ w' : Point D.host.E (D.R.rS + 1), Gpt (D.mem u).A.T (D.mem u').A.T w' ≠ 0 → kind w' = kind w →
  ∀ Z : PairVal.MatR D, AtMat w' Z →
  ∃ (F'₂ : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E))
    (φ : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (tLoc Zd p γ).f)
    (φ' : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f' ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (locF' Zd p F'₂)),
    ZhatL (lf D F0) F'₂ = Z ∧
    (∀ p, LsDatumA.LocalCountHypotheses (locH Zd p) (tLoc Zd p γ) (tLoc Zd p γ).f (locF' Zd p F'₂) (φ p) (φ' p)) ∧
    (frPart γ Z).ncard = ∏ᶠ p, Nat.card (locSet Zd p (tLoc Zd p γ) (locF' Zd p F'₂) (φ p) (φ' p))

def FrLoc : Prop :=
  ∀ (γ : TermDef.Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1)), EligAt γ w →
  ∀ w' : Point D.host.E (D.R.rS + 1), Gpt (D.mem u).A.T (D.mem u').A.T w' ≠ 0 → kind w' = kind w →
  ∀ Z : PairVal.MatR D, AtMat w' Z →
  ∀ (F'₂ : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (p : PlF D)
    (φ : (locH Zd p).Wb (tLoc Zd p γ).f ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (tLoc Zd p γ).f)
    (φ' : (locH Zd p).Wb (tLoc Zd p γ).f' ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (locF' Zd p F'₂)),
    ZhatL (lf D F0) F'₂ = Z →
    LsDatumA.LocalCountHypotheses (locH Zd p) (tLoc Zd p γ) (tLoc Zd p γ).f (locF' Zd p F'₂) φ φ' →
    (Nat.card (locSet Zd p (tLoc Zd p γ) (locF' Zd p F'₂) φ φ') : ℂ) =
      kL Zd.M Zd.δ (D.mem u).A.T (D.mem u').A.T p w' (thT Zd.M Zd.δ γ p) (tupZ Zd.M Zd.δ u u' Z p)

variable {u u' F0 what₂}

theorem frCount_of (hG : FrGlob Zd u u' F0 what₂) (hL : FrLoc Zd u u' F0 what₂) :
    FrCount Zd.M Zd.δ u u' F0 what₂ := by
  intro γ w hγ w' hG' hk Z hZ
  obtain ⟨F'₂, φ, φ', hF, hT, hc⟩ := hG γ w hγ w' hG' hk Z hZ
  rw [hc]
  have hcast := (Nat.castRingHom ℂ).toMonoidHom.map_finprod_of_injective Nat.cast_injective
    (fun p => Nat.card (locSet Zd p (tLoc Zd p γ) (locF' Zd p F'₂) (φ p) (φ' p)))
  simp only [RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, Nat.coe_castRingHom] at hcast
  rw [hcast]
  exact finprod_congr fun p => hL γ w hγ w' hG' hk Z hZ F'₂ p (φ p) (φ' p) hF (hT p)

end FrCut

section RestrFinal

variable {D : Formalism.BasicNotions.D7} {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep}
  {δ : ∀ p : PlF D, (D.s.atP p).Fp} {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

variable (u u' F0 what₂) in

def EligRel : Prop :=
  ∀ (γ : TermDef.Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1)), EligAt γ w → γ.relevant

theorem eligRel_holds : EligRel u u' F0 what₂ := fun γ w h =>
  Formalism.L2.SG.Pf.FinXP.atPtRelevant_holds D u u' F0 what₂ γ w h.2

theorem restr_of (hA : ∀ p, Agree δ M p) (hrows : IsRowReps D F0 what₂) (hN : PairVal.NormRepExists D u u' F0 what₂)
    (hRel : EligRel u u' F0 what₂) : Restr M δ u u' F0 what₂ := by
  intro γ' w' h
  have hZ := atMat_zT hN hrows h (hRel γ' w' h)
  exact tupZ_restr hA u u' hZ ((Formalism.L2.SG.Pf.LocModel.good_cofinite δ M hA ∅).mono fun p hp => ⟨hp.1, hp.2.1, hp.2.2.1⟩)
    (fun x => Formalism.L2.SG.Pf.LocModel.LM.iotaIntegral_almost_all D x)

end RestrFinal

section SgnLoc

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D)

theorem zhat_locF' (p : PlF D) (Λ : Submodule (𝓞 D.host.E) (VS D).V) {T T' T'' : D.host.E}
    (F : LFlag (VS D) D.R.rS T) (F' : LFlag (VS D) D.R.rS T') (F'₂ : LFlag (VS D) D.R.rS T'') (Tn T'n : ℕ)
    (a b : Fin (D.R.rS + 1)) :
    (locH Zd p).Zhat (locTerm Zd p Λ F F' Tn T'n).f (locF' Zd p F'₂) a b =
      (TermLoc.sgnP' D p b * frFac Zd.δ p b) * (D.s.atP p).cj (TermLoc.sgnP D p a * frFac Zd.δ p a) *
        (D.s.atP p).ιE (ZhatL F F'₂ a b) := by
  simp only [Loc.HermSp.Zhat, Matrix.of_apply, locH, locHerm, locTerm, locF']
  rw [localForm_smul, Zd.hcj p, baseChangeAt_form Zd.M p (Zd.hcj p)]
  rfl

theorem zzplus_locF' (u u' : D.what₂.Word) (p : PlF D) (Λ : Submodule (𝓞 D.host.E) (VS D).V) {T T' T'' : D.host.E}
    (F : LFlag (VS D) D.R.rS T) (F' : LFlag (VS D) D.R.rS T') (F'₂ : LFlag (VS D) D.R.rS T'')
    (Λ₂ : Submodule (Zd.M p).L.O (Vp D p)) :
    (locH Zd p).ZZplus ⟨Λ₂, (locTerm Zd p Λ F F' (Tu D u) (Tu D u')).f, locF' Zd p F'₂,
        ((Tu D u : ℕ) : (D.s.atP p).Fp), ((Tu D u' : ℕ) : (D.s.atP p).Fp)⟩ =
      CntLocal.ZZP (M := Zd.M) Zd.δ u u' p (ZhatL F F'₂) * LsDatumB.sgnP p := by
  have hAg := (Zd.agree p).2.2.2.2.2
  rcases hM : (Zd.M p).split with _ | g <;> rcases hR : (D.s.atP p).split with _ | sg <;>
    simp only [hM, hR] at hAg
  ·
    ext a b
    simp only [Loc.HermSp.ZZplus, Loc.HermSp.ZZplusOf, hM, CntLocal.ZZP, CntLocal.ZhatLoc, LsDatumB.sgnP,
      Matrix.mul_diagonal, Matrix.of_apply]
    rw [zhat_locF']
    simp only [TermLoc.sgnP, TermLoc.sgnP', hR, one_mul, Zd.hcj p]
    ring
  ·
    obtain ⟨hge, hgq⟩ := hAg
    have hcj1 : ∀ x, p1 sg.e ((D.s.atP p).cj x) = p2 sg.e x := fun x => by
      rw [adeleInfiniteComponent_apply, adele_ext_components, sg.e_cj]; rfl
    have hcj2 : ∀ x, p2 sg.e ((D.s.atP p).cj x) = p1 sg.e x := fun x => by
      rw [adeleInfiniteComponent_apply, adele_ext_components, sg.e_cj]; rfl
    have hs1 : ∀ a, p1 sg.e (TermLoc.sgnP D p a) = (-1) ^ (D.R.rS - a.val) := fun a => by
      simp only [TermLoc.sgnP, hR, fst_proj_symm]
    have hs2 : ∀ a, p2 sg.e (TermLoc.sgnP D p a) = 1 := fun a => by
      simp only [TermLoc.sgnP, hR, snd_proj_symm]
    have hs' : ∀ b, TermLoc.sgnP' D p b = TermLoc.sgnP D p b := fun b => by simp only [TermLoc.sgnP', hR]
    have hm1 : ∀ k : ℕ, p1 sg.e ((-1 : (D.s.atP p).Ep) ^ k) = (-1) ^ k := fun k => by simp
    have hm2 : ∀ k : ℕ, p2 sg.e ((-1 : (D.s.atP p).Ep) ^ k) = (-1) ^ k := fun k => by simp
    have hf1 : ∀ a, p1 sg.e (frFac Zd.δ p a) = cf Zd p a := fun a => by rw [frFac_eq, fst_proj_algebraMap]; rfl
    have hf2 : ∀ a, p2 sg.e (frFac Zd.δ p a) = cf Zd p a := fun a => by rw [frFac_eq, snd_proj_algebraMap]; rfl
    apply mat_eq sg.e
    · ext a b
      simp only [Matrix.map_apply, Loc.HermSp.ZZplus, Loc.HermSp.ZZplusOf, hM, CntLocal.ZZP, CntLocal.ZhatLoc,
        LsDatumB.sgnP, Matrix.mul_diagonal, Matrix.of_apply, hge, hgq, map_mul, map_sub, fst_proj_symm, apply_ite (p1 sg.e),
        map_zero, zhat_locF', Prod.fst_mul, Prod.snd_mul, ← adeleInfiniteComponent_apply, ← adele_ext_components, hs', hs1, hcj1, hcj2, hs2, hm1, hf1, hf2, Tu, Zd.hcj p]
      split_ifs with h
      · obtain ⟨rfl, rfl⟩ := h
        simp only [Fin.val_last, Nat.sub_self, pow_zero]
        ring
      · ring
    · ext a b
      simp only [Matrix.map_apply, Loc.HermSp.ZZplus, Loc.HermSp.ZZplusOf, hM, CntLocal.ZZP, CntLocal.ZhatLoc,
        LsDatumB.sgnP, Matrix.mul_diagonal, Matrix.of_apply, hge, hgq, map_mul, map_sub, snd_proj_symm, apply_ite (p2 sg.e),
        map_zero, zhat_locF', Prod.fst_mul, Prod.snd_mul, ← adeleInfiniteComponent_apply, ← adele_ext_components, hs', hs1, hcj1, hcj2, hs2, hm2, hf1, hf2, Tu, map_neg, Zd.hcj p]
      split_ifs with h
      · obtain ⟨rfl, rfl⟩ := h
        simp only [Fin.val_last, Nat.sub_self, pow_zero]
        ring
      · ring

end SgnLoc

section OrbAlg

variable {D : Formalism.BasicNotions.D7} {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep}

theorem kL_of_not_cls {δ : ∀ p : PlF D, (D.s.atP p).Fp} {T T' : ℕ} {p : PlF D} {w : Point D.host.E (D.R.rS + 1)}
    {τ : Option ((M p).Cls D.R.rS)} {O : Set (MatP D p)} (h : ¬ IsLCls M δ T T' p w O) : kL M δ T T' p w τ O = 0 := by
  simp [kL, h]

theorem intLow_one (p : PlF D) : TieN.IntLow (M p) (1 : MatP D p) :=
  ⟨fun a => Matrix.one_apply_eq a, fun a b hab => Matrix.one_apply_ne (ne_of_lt hab), fun a b => by
    by_cases h : a = b
    · subst h; rw [Matrix.one_apply_eq]; exact Subring.one_mem _
    · rw [Matrix.one_apply_ne h]; exact Subring.zero_mem _⟩

theorem intUp_one (p : PlF D) : TieN.IntUp (M p) (1 : MatP D p) :=
  ⟨fun a => Matrix.one_apply_eq a, fun a b hab => Matrix.one_apply_ne (ne_of_gt hab), fun a b => by
    by_cases h : a = b
    · subst h; rw [Matrix.one_apply_eq]; exact Subring.one_mem _
    · rw [Matrix.one_apply_ne h]; exact Subring.zero_mem _⟩

theorem mem_kkOrb_self (p : PlF D) (Y : MatP D p) : Y ∈ kkOrb M p Y :=
  ⟨1, 1, intLow_one p, intUp_one p, by rw [Matrix.one_mul, Matrix.mul_one]⟩

theorem int_of_mem_kkOrb {p : PlF D} {Y Y' : MatP D p} (hY : ∀ a b, Y a b ∈ (M p).R) (h : Y' ∈ kkOrb M p Y) :
    ∀ a b, Y' a b ∈ (M p).R := by
  obtain ⟨l, ρ, hl, hρ, rfl⟩ := h
  intro a b
  rw [Matrix.mul_apply]
  refine Subring.sum_mem _ fun c _ => Subring.mul_mem _ ?_ (hρ.2.2 c b)
  rw [Matrix.mul_apply]
  exact Subring.sum_mem _ fun d _ => Subring.mul_mem _ (hl.2.2 a d) (hY d c)

theorem not_isLCls_of_nonint {δ : ∀ p : PlF D, (D.s.atP p).Fp} {T T' : ℕ} {p : PlF D}
    {w : Point D.host.E (D.R.rS + 1)} {Y : MatP D p} (h : ¬ ∀ a b, Y a b ∈ (M p).R) :
    ¬ IsLCls M δ T T' p w (kkOrb M p Y) := by
  rintro ⟨Y', hint, -, hO⟩
  have hm : Y ∈ kkOrb M p Y' := hO ▸ mem_kkOrb_self p Y
  exact h (int_of_mem_kkOrb hint hm)

def cornE (p : PlF D) (s : (D.s.atP p).Ep) : MatP D p :=
  Matrix.of fun a b => if a = Fin.last D.R.rS ∧ b = Fin.last D.R.rS then s else 0

theorem cornE_eq (p : PlF D) (s : (D.s.atP p).Ep) : cornE p s = s • Ecorner D.R.rS := by
  ext a b; simp [cornE, Ecorner]

theorem cornerSh_eq_of_kind (δ : ∀ p, (D.s.atP p).Fp) (T T' : ℕ) (p : PlF D) {w w' : Point D.host.E (D.R.rS + 1)}
    (h : kind w = kind w') : cornerSh δ T T' p w = cornerSh δ T T' p w' := by
  unfold kind at h
  unfold cornerSh
  by_cases h0 : Dmin w D.R.rS = 0 <;> by_cases h0' : Dmin w' D.R.rS = 0 <;> simp only [h0, h0', if_true, if_false] at h ⊢
  · exact absurd h (by simp)
  · exact absurd h (by simp)
  · rw [Option.some_inj.1 h]

end OrbAlg

section ClsOrb

variable {D : Formalism.BasicNotions.D7} {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep}

def toR {p : PlF D} (l : MatP D p) (h : ∀ a b, l a b ∈ (M p).R) : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (M p).R :=
  Matrix.of fun a b => ⟨l a b, h a b⟩

theorem toR_map {p : PlF D} (l : MatP D p) (h : ∀ a b, l a b ∈ (M p).R) : (toR (M := M) l h).map (M p).R.subtype = l := by
  ext a b; rfl

theorem toIntegral_mul_three {p : PlF D} (l Y ρ : MatP D p) (h1 : ∀ a b, l a b ∈ (M p).R) (h2 : ∀ a b, Y a b ∈ (M p).R)
    (h3 : ∀ a b, ρ a b ∈ (M p).R) :
    (toR (M := M) l h1 * toR Y h2 * toR ρ h3).map (M p).R.subtype = l * Y * ρ := by
  rw [Matrix.map_mul, Matrix.map_mul, toR_map, toR_map, toR_map]

theorem det_toR_lo {p : PlF D} {l : MatP D p} (hl : TieN.IntLow (M p) l) : (toR (M := M) l hl.2.2).det = 1 := by
  have hbt : (toR (M := M) l hl.2.2).BlockTriangular OrderDual.toDual := fun i j hij => by
    apply Subtype.ext; exact hl.2.1 i j hij
  rw [Matrix.det_of_lowerTriangular _ hbt]
  exact Finset.prod_eq_one fun a _ => Subtype.ext (hl.1 a)

theorem det_toR_up {p : PlF D} {ρ : MatP D p} (hρ : TieN.IntUp (M p) ρ) : (toR (M := M) ρ hρ.2.2).det = 1 := by
  have hbt : (toR (M := M) ρ hρ.2.2).BlockTriangular id := fun i j hij => by
    apply Subtype.ext; exact hρ.2.1 i j hij
  rw [Matrix.det_of_upperTriangular hbt]
  exact Finset.prod_eq_one fun a _ => Subtype.ext (hρ.1 a)

theorem clsOf_orb {p : PlF D} {Y Y' l ρ l' ρ' : MatP D p} (hl : TieN.IntLow (M p) l) (hρ : TieN.IntUp (M p) ρ)
    (hl' : TieN.IntLow (M p) l') (hρ' : TieN.IntUp (M p) ρ') (h1 : Y' = l * Y * ρ) (h2 : Y = l' * Y' * ρ')
    (s : (D.s.atP p).Ep) :
    clsOf (M p) (Y' + cornE p s) = clsOf (M p) (Y + cornE p s) := by
  have hL : IsLo l := ⟨hl.1, hl.2.1⟩
  have hU : IsUp ρ := ⟨hρ.1, fun a b hab => hρ.2.1 b a hab⟩
  have hL' : IsLo l' := ⟨hl'.1, hl'.2.1⟩
  have hU' : IsUp ρ' := ⟨hρ'.1, fun a b hab => hρ'.2.1 b a hab⟩
  have e1 : Y' + cornE p s = l * (Y + cornE p s) * ρ := by
    rw [h1, Matrix.mul_add, Matrix.add_mul, cornE_eq, Matrix.mul_smul, Matrix.smul_mul, lo_corner_up hL hU]
  have e2 : Y + cornE p s = l' * (Y' + cornE p s) * ρ' := by
    rw [h2, Matrix.mul_add, Matrix.add_mul, cornE_eq, Matrix.mul_smul, Matrix.smul_mul, lo_corner_up hL' hU']
  have hdet : (Y' + cornE p s).det = (Y + cornE p s).det := by
    rw [e1, Matrix.det_mul, Matrix.det_mul, det_lo' hL, det_up' hU, one_mul, mul_one]
  have hint : (∀ a b, (Y' + cornE p s) a b ∈ (M p).R) ↔ (∀ a b, (Y + cornE p s) a b ∈ (M p).R) := by
    constructor
    · intro h; rw [e2]; exact int_of_mem_kkOrb h ⟨l', ρ', hl', hρ', rfl⟩
    · intro h; rw [e1]; exact int_of_mem_kkOrb h ⟨l, ρ, hl, hρ, rfl⟩
  unfold clsOf
  by_cases hc : (∀ a b, (Y + cornE p s) a b ∈ (M p).R) ∧ IsUnit (Y + cornE p s).det
  · have hc' : (∀ a b, (Y' + cornE p s) a b ∈ (M p).R) ∧ IsUnit (Y' + cornE p s).det := ⟨hint.2 hc.1, hdet ▸ hc.2⟩
    rw [dif_pos hc, dif_pos hc']
    congr 1
    apply Eq.symm
    apply Quotient.sound
    have hlR := det_toR_lo (M := M) hl
    have hρR := det_toR_up (M := M) hρ
    have hle : (toR (M := M) l hl.2.2).mulVec (Pi.single (Fin.last D.R.rS) 1) = Pi.single (Fin.last D.R.rS) 1 := by
      funext a
      rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single (Fin.last D.R.rS)]
      · rw [Pi.single_eq_same, mul_one]
        by_cases ha : a = Fin.last D.R.rS
        · subst ha; rw [Pi.single_eq_same]; exact Subtype.ext (hl.1 _)
        · rw [Pi.single_eq_of_ne ha]; exact Subtype.ext (hl.2.1 a _ (lt_of_le_of_ne (Fin.le_last a) ha))
      · intro b _ hb; rw [Pi.single_eq_of_ne hb, mul_zero]
      · intro h; exact absurd (Finset.mem_univ _) h
    have hρe : ∀ b, ((toR (M := M) ρ hρ.2.2).map (M p).R.subtype)⁻¹ (Fin.last D.R.rS) b =
        if b = Fin.last D.R.rS then 1 else 0 := by
      intro b
      rw [toR_map]
      have hi := isUp_inv hU
      by_cases hb : b = Fin.last D.R.rS
      · subst hb; rw [if_pos rfl]; exact hi.1 _
      · rw [if_neg hb]; exact hi.2 b _ (lt_of_le_of_ne (Fin.le_last b) hb)
    refine ⟨?_⟩
    have key := isoLR (M p) ⟨Matrix.of fun a b => ⟨(Y + cornE p s) a b, hc.1 a b⟩, by
        have : (Matrix.of fun a b => (⟨(Y + cornE p s) a b, hc.1 a b⟩ : (M p).R)).map (M p).R.subtype = Y + cornE p s := rfl
        rw [this]; exact hc.2⟩ (toR l hl.2.2) (toR ρ hρ.2.2) (by rw [hlR]; exact isUnit_one) (by rw [hρR]; exact isUnit_one)
      hle hρe
    have hZ : toR (M := M) l hl.2.2 * toR (Y + cornE p s) hc.1 * toR ρ hρ.2.2 = toR (Y' + cornE p s) hc'.1 := by
      ext a b
      have h3 := congrFun (congrFun (toIntegral_mul_three (M := M) l (Y + cornE p s) ρ hl.2.2 hc.1 hρ.2.2) a) b
      rw [← e1] at h3
      exact h3
    refine cast ?_ key
    congr 1
    unfold matLR
    congr 1
  · have hc' : ¬ ((∀ a b, (Y' + cornE p s) a b ∈ (M p).R) ∧ IsUnit (Y' + cornE p s).det) := by
      rintro ⟨h1', h2'⟩; exact hc ⟨hint.1 h1', hdet ▸ h2'⟩
    rw [dif_neg hc, dif_neg hc']

end ClsOrb

section FrLocCut

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D)

def IntGenP : Prop :=
  ∀ (p : PlF D) (t : Loc.Term (Vp D p) (Zd.M p) D.R.rS), (locH Zd p).IsGeneric t →
    ∀ a b, (locH Zd p).ZZplus t a b ∈ (Zd.M p).R

variable (u u' : D.what₂.Word)

def InOrbZ : Prop :=
  ∀ (w : Point D.host.E (D.R.rS + 1)) (Z : PairVal.MatR D), AtMat w Z → ∀ p,
    InOrbP Zd.δ (D.mem u).A.T (D.mem u').A.T p w (CntLocal.ZZP (M := Zd.M) Zd.δ u u' p Z * LsDatumB.sgnP p)

variable (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))

def Tau1 : Prop :=
  ∀ (γ : TermDef.Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1)), EligAt γ w → ∀ p,
    thT Zd.M Zd.δ γ p = clsOf (Zd.M p) ((locH Zd p).ZZplus (tLoc Zd p γ) +
      cornE p (cornerSh Zd.δ (D.mem u).A.T (D.mem u').A.T p w))

def PartnerIsomorphismCount : Prop :=
  ∀ (p : PlF D) (T T' : ℕ) (w w' : Point D.host.E (D.R.rS + 1)) (t₁ : Loc.Term (Vp D p) (Zd.M p) D.R.rS)
    (f₂' : Fin (D.R.rS + 1) → Vp D p)
    (φ : (locH Zd p).Wb t₁.f ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb t₁.f)
    (φ' : (locH Zd p).Wb t₁.f' ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb f₂'),
    kind w = kind w' → t₁.T = ((T : ℕ) : (D.s.atP p).Fp) → t₁.T' = ((T' : ℕ) : (D.s.atP p).Fp) →
    LsDatumA.LocalCountHypotheses (locH Zd p) t₁ t₁.f f₂' φ φ' →
    (∃ uL uU : MatP D p, (∀ a, uL a a = 1 ∧ uU a a = 1) ∧ (∀ a b, a < b → uL a b = 0 ∧ uU b a = 0) ∧
      (locH Zd p).ZZplus t₁ = uL * modMat Zd.δ T T' p w * uU) →
    (∃ uL uU : MatP D p, (∀ a, uL a a = 1 ∧ uU a a = 1) ∧ (∀ a b, a < b → uL a b = 0 ∧ uU b a = 0) ∧
      Loc.HermSp.ZZplusOf (Zd.M p) ((locH Zd p).Zhat t₁.f f₂') t₁.T t₁.T' = uL * modMat Zd.δ T T' p w' * uU) →
    (∀ a b, Loc.HermSp.ZZplusOf (Zd.M p) ((locH Zd p).Zhat t₁.f f₂') t₁.T t₁.T' a b ∈ (Zd.M p).R) →
    Nat.card (locSet Zd p t₁ f₂' φ φ') =
      nIsoO Zd.M p (clsOf (Zd.M p) ((locH Zd p).ZZplus t₁ + cornE p (cornerSh Zd.δ T T' p w)))
        (clsOf (Zd.M p) (Loc.HermSp.ZZplusOf (Zd.M p) ((locH Zd p).Zhat t₁.f f₂') t₁.T t₁.T' +
          cornE p (cornerSh Zd.δ T T' p w')))

end FrLocCut

section FrLocPf

variable {D : Formalism.BasicNotions.D7} {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

theorem inOrbP_shape {δ : ∀ p : PlF D, (D.s.atP p).Fp} {T T' : ℕ} {p : PlF D} {w : Point D.host.E (D.R.rS + 1)}
    {Y : MatP D p} (h : InOrbP δ T T' p w Y) :
    ∃ uL uU : MatP D p, (∀ a, uL a a = 1 ∧ uU a a = 1) ∧ (∀ a b, a < b → uL a b = 0 ∧ uU b a = 0) ∧
      Y = uL * modMat δ T T' p w * uU := by
  obtain ⟨w₀, -, xy, e⟩ := h
  refine ⟨Loc.uLow xy.1, Loc.uUp w₀ xy.2, fun a => ⟨by simp [Loc.uLow], by simp [Loc.uUp]⟩, fun a b hab => ⟨?_, ?_⟩, e⟩
  · simp [Loc.uLow, ne_of_lt hab, not_lt.2 (le_of_lt hab)]
  · simp [Loc.uUp, ne_of_gt hab, not_lt.2 (le_of_lt hab)]

theorem repL_spec {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep} {δ : ∀ p : PlF D, (D.s.atP p).Fp}
    {T T' : ℕ} {p : PlF D} {w : Point D.host.E (D.R.rS + 1)} {O : Set (MatP D p)} (h : IsLCls M δ T T' p w O) :
    IntP M p (repL M δ T T' p w O) ∧ O = kkOrb M p (repL M δ T T' p w O) := by
  unfold repL; rw [dif_pos h]; exact ⟨h.choose_spec.1, h.choose_spec.2.2⟩

theorem kL_of_orb {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep} {δ : ∀ p : PlF D, (D.s.atP p).Fp}
    {T T' : ℕ} {p : PlF D} {w : Point D.host.E (D.R.rS + 1)} {P₂ : MatP D p}
    (hcls : IsLCls M δ T T' p w (kkOrb M p P₂)) (τ : Option ((M p).Cls D.R.rS)) :
    kL M δ T T' p w τ (kkOrb M p P₂) = (nIsoO M p τ (clsOf (M p) (P₂ + cornE p (cornerSh δ T T' p w))) : ℂ) := by
  unfold kL
  rw [if_pos hcls]
  obtain ⟨-, hO⟩ := repL_spec hcls
  generalize repL M δ T T' p w (kkOrb M p P₂) = Y at hO ⊢
  have hm1 : Y ∈ kkOrb M p P₂ := by rw [hO]; exact mem_kkOrb_self p Y
  have hm2 : P₂ ∈ kkOrb M p Y := by rw [← hO]; exact mem_kkOrb_self p P₂
  obtain ⟨l, ρ, hl, hρ, e1⟩ := hm1
  obtain ⟨l', ρ', hl', hρ', e2⟩ := hm2
  have hth : thL M δ T T' p w Y = clsOf (M p) (P₂ + cornE p (cornerSh δ T T' p w)) := clsOf_orb hl hρ hl' hρ' e1 e2 _
  rw [hth]

theorem repF_cell (hN : PairVal.NormRepExists D u u' F0 what₂) (hrows : IsRowReps D F0 what₂)
    {γ : TermDef.Term D u u' F0 what₂} {w : Point D.host.E (D.R.rS + 1)} (hγ : EligAt γ w) :
    zT γ = ZhatL (lf D F0) (repF γ) ∧ IsInCell (ZhatOM (ZhatL (lf D F0) (repF γ))) w := by
  obtain ⟨⟨hgen, hG⟩, hat⟩ := hγ
  obtain ⟨y, hy⟩ := hN γ w hat (eligRel_holds γ w ⟨⟨hgen, hG⟩, hat⟩) hgen
  have hex : ∃ x : Point D.host.E (D.R.rS + 1) × LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E) × PairVal.MatR D ×
      PairVal.MatR D, PairVal.NormRep γ x.1 x.2.1 x.2.2.1 x.2.2.2 := ⟨(w, y), hy⟩
  have hn : nrep γ = some hex.choose := dif_pos hex
  have hz : zT γ = ZhatL (lf D F0) (repF γ) := by unfold zT repF; rw [hn]
  have hA := atMat_zT hN hrows ⟨⟨hgen, hG⟩, hat⟩ (eligRel_holds γ w ⟨⟨hgen, hG⟩, hat⟩)
  rw [hz] at hA
  exact ⟨hz, hA⟩

theorem card_locSet_zero (Zd : LocDat D) (p : PlF D) (t₁ : Loc.Term (Vp D p) (Zd.M p) D.R.rS)
    (f₂' : Fin (D.R.rS + 1) → Vp D p)
    (φ : (locH Zd p).Wb t₁.f ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb t₁.f)
    (φ' : (locH Zd p).Wb t₁.f' ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb f₂') (hI : IntGenP Zd)
    (hnot : ¬ ∀ a b, Loc.HermSp.ZZplusOf (Zd.M p) ((locH Zd p).Zhat t₁.f f₂') t₁.T t₁.T' a b ∈ (Zd.M p).R) :
    Nat.card (locSet Zd p t₁ f₂' φ φ') = 0 := by
  rw [Nat.card_eq_zero]
  left
  constructor
  rintro ⟨Λ₂, hg, -⟩
  exact hnot (hI p ⟨Λ₂, t₁.f, f₂', t₁.T, t₁.T'⟩ hg)

theorem frLoc_of (Zd : LocDat D) (hN : PairVal.NormRepExists D u u' F0 what₂) (hrows : IsRowReps D F0 what₂)
    (hI : IntGenP Zd) (hO : InOrbZ Zd u u') (hτ : Tau1 Zd u u' F0 what₂) (hT : PartnerIsomorphismCount Zd) :
    FrLoc Zd u u' F0 what₂ := by
  intro γ w hγ w' hG' hk Z hZ F'₂ p φ φ' hF hTH
  have hP2 : Loc.HermSp.ZZplusOf (Zd.M p) ((locH Zd p).Zhat (tLoc Zd p γ).f (locF' Zd p F'₂)) (tLoc Zd p γ).T
      (tLoc Zd p γ).T' = CntLocal.ZZP (M := Zd.M) Zd.δ u u' p Z * LsDatumB.sgnP p := by
    rw [← hF]
    exact zzplus_locF' Zd u u' p γ.lam (lf D F0) (repF γ) F'₂ ⊥
  by_cases hint : ∀ a b, (CntLocal.ZZP (M := Zd.M) Zd.δ u u' p Z * LsDatumB.sgnP p) a b ∈ (Zd.M p).R
  · have hcls : IsLCls Zd.M Zd.δ (D.mem u).A.T (D.mem u').A.T p w'
        (kkOrb Zd.M p (CntLocal.ZZP (M := Zd.M) Zd.δ u u' p Z * LsDatumB.sgnP p)) :=
      ⟨_, hint, hO w' Z hZ p, rfl⟩
    have hsh := cornerSh_eq_of_kind Zd.δ (D.mem u).A.T (D.mem u').A.T p hk.symm
    show (Nat.card _ : ℂ) = kL Zd.M Zd.δ (D.mem u).A.T (D.mem u').A.T p w' (thT Zd.M Zd.δ γ p)
      (kkOrb Zd.M p (CntLocal.ZZP (M := Zd.M) Zd.δ u u' p Z * LsDatumB.sgnP p))
    rw [kL_of_orb hcls, hτ γ w hγ p, hsh]
    obtain ⟨-, hcell⟩ := repF_cell hN hrows hγ
    have h1 := termLoc_atPt_frame Zd γ.lam (lf D F0) (repF γ) (Tu D u) (Tu D u') w hcell p
    have h2 := inOrbP_shape (hO w' Z hZ p)
    have h2' : ∃ uL uU : MatP D p, (∀ a, uL a a = 1 ∧ uU a a = 1) ∧ (∀ a b, a < b → uL a b = 0 ∧ uU b a = 0) ∧
        Loc.HermSp.ZZplusOf (Zd.M p) ((locH Zd p).Zhat (tLoc Zd p γ).f (locF' Zd p F'₂)) (tLoc Zd p γ).T
          (tLoc Zd p γ).T' = uL * modMat Zd.δ (D.mem u).A.T (D.mem u').A.T p w' * uU := by
      rw [hP2]; exact h2
    have hint' : ∀ a b, Loc.HermSp.ZZplusOf (Zd.M p) ((locH Zd p).Zhat (tLoc Zd p γ).f (locF' Zd p F'₂))
        (tLoc Zd p γ).T (tLoc Zd p γ).T' a b ∈ (Zd.M p).R := by
      rw [hP2]; exact hint
    have hc := hT p (D.mem u).A.T (D.mem u').A.T w w' (tLoc Zd p γ) (locF' Zd p F'₂) φ φ' hk.symm rfl rfl hTH h1 h2'
      hint'
    rw [hP2, hsh] at hc
    exact congrArg (fun n : ℕ => (n : ℂ)) hc
  · have hk0 : kL Zd.M Zd.δ (D.mem u).A.T (D.mem u').A.T p w' (thT Zd.M Zd.δ γ p) (tupZ Zd.M Zd.δ u u' Z p) = 0 :=
      kL_of_not_cls (not_isLCls_of_nonint hint)
    rw [hk0]
    have hnot : ¬ ∀ a b, Loc.HermSp.ZZplusOf (Zd.M p) ((locH Zd p).Zhat (tLoc Zd p γ).f (locF' Zd p F'₂))
        (tLoc Zd p γ).T (tLoc Zd p γ).T' a b ∈ (Zd.M p).R := by
      rw [hP2]; exact hint
    rw [card_locSet_zero Zd p _ _ φ φ' hI hnot]
    simp

end FrLocPf

section Assembly

variable {D : Formalism.BasicNotions.D7} {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep}
  {δ : ∀ p : PlF D, (D.s.atP p).Fp} {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

theorem partnerCount_of {θ0 : ∀ p, Option ((M p).Cls D.R.rS)}
    (hU : LocUnram M δ u u' θ0) (hR : ThRestricted M δ u u' F0 what₂ θ0)
    (hrows : IsRowReps D F0 what₂) (hN : PairVal.NormRepExists D u u' F0 what₂) (hRel : EligRel u u' F0 what₂)
    (hRs : Restr M δ u u' F0 what₂) (hE : Exist M δ u u')
    (hS : SumFr M δ u u' F0 what₂) (hF : FrCount M δ u u' F0 what₂) : PartnerCount M δ u u' F0 what₂ := by
  intro γ w hγ w' hG' hk
  refine ⟨fun γ' _ hγ' => hRs γ' w' hγ', fun x => ?_⟩
  by_cases hZ : ∃ Z : PairVal.MatR D, AtMat w' Z ∧ tupZ M δ u u' Z = x.1
  · obtain ⟨Z, hZ, hZx⟩ := hZ
    obtain ⟨-, hsum⟩ := hS γ w hγ w' hG' hk Z hZ
    have hcnt := hF γ w hγ w' hG' hk Z hZ
    rw [hZx] at hsum hcnt
    rw [← hcnt]
    exact hsum
  ·
    have hempty : IsEmpty {γ' : TermDef.Term D u u' F0 what₂ //
        (Corank.TermScal D γ γ' ∧ EligAt γ' w') ∧ locT M δ γ' = x.1} :=
      ⟨fun γ' => hZ ⟨zT γ'.1, atMat_zT hN hrows γ'.2.1.2 (hRel γ'.1 w' γ'.2.1.2), γ'.2.2⟩⟩

    have hx : ∃ p₀, ¬ IsLCls M δ (D.mem u).A.T (D.mem u').A.T p₀ w' (x.1 p₀) := by
      by_contra h
      simp only [not_exists, not_not] at h
      exact hZ (hE w' hG' x h)
    obtain ⟨p₀, hp₀⟩ := hx
    obtain ⟨S, hS0⟩ := hU w' hG'
    have hRf := hR γ w hγ
    have hone : ∀ p ∉ S ∪ hRf.toFinset ∪ x.2.toFinset,
        kL M δ (D.mem u).A.T (D.mem u').A.T p w' (thT M δ γ p) (x.1 p) = 1 := by
      intro p hp
      have hpS : p ∉ S := fun h => hp (Finset.mem_union_left _ (Finset.mem_union_left _ h))
      have hth : thT M δ γ p = θ0 p := by
        by_contra h
        exact hp (Finset.mem_union_left _ (Finset.mem_union_right _ (hRf.mem_toFinset.2 h)))
      have hxp : x.1 p = x0L M δ (D.mem u).A.T (D.mem u').A.T p w' := by
        by_contra h
        exact hp (Finset.mem_union_right _ (x.2.mem_toFinset.2 h))
      rw [hxp, hth]
      exact (base_factors (fun τ O => ((hS0 p hpS).2 τ O).1) (fun τ O => ((hS0 p hpS).2 τ O).2)).2.1
    have hfin : (Function.mulSupport fun p =>
        kL M δ (D.mem u).A.T (D.mem u').A.T p w' (thT M δ γ p) (x.1 p)).Finite := by
      refine (S ∪ hRf.toFinset ∪ x.2.toFinset).finite_toSet.subset fun p hp => ?_
      by_contra h
      exact (Function.mem_mulSupport.1 hp) (hone p h)
    have hzero : (∏ᶠ p, kL M δ (D.mem u).A.T (D.mem u').A.T p w' (thT M δ γ p) (x.1 p)) = 0 := by
      rw [finprod_eq_prod _ hfin]
      refine Finset.prod_eq_zero (i := p₀) ?_ (kL_of_not_cls hp₀)
      rw [Set.Finite.mem_toFinset, Function.mem_mulSupport, kL_of_not_cls hp₀]
      exact zero_ne_one
    rw [hzero]
    exact hasSum_empty

end Assembly

end Formalism.L2.SG.Pf.PCount

namespace Formalism.L2.SG.Pf

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem pcount_restr {D : Formalism.BasicNotions.D7} {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep}
    {δ : ∀ p : PlF D, (D.s.atP p).Fp} {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
    {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)} (hA : ∀ p, Agree δ M p) (hrows : IsRowReps D F0 what₂)
    (hN : PairVal.NormRepExists D u u' F0 what₂) :
    PCount.Restr M δ u u' F0 what₂ :=
  PCount.restr_of hA hrows hN PCount.eligRel_holds

theorem pcount_frCount {D : Formalism.BasicNotions.D7} {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
    {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)} (Zd : TermLoc.LocDat D)
    (hN : PairVal.NormRepExists D u u' F0 what₂) (hrows : IsRowReps D F0 what₂)
    (hG : PCount.FrGlob Zd u u' F0 what₂) (hI : PCount.IntGenP Zd) (hO : PCount.InOrbZ Zd u u')
    (hτ : PCount.Tau1 Zd u u' F0 what₂) (hT : PCount.PartnerIsomorphismCount Zd) : PCount.FrCount Zd.M Zd.δ u u' F0 what₂ :=
  PCount.frCount_of Zd hG (PCount.frLoc_of Zd hN hrows hI hO hτ hT)

end Formalism.L2.SG.Pf
