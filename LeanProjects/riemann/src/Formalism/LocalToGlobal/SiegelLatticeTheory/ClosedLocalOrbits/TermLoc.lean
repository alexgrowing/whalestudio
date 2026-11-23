import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.LocalGroupInFamilyNontrivial
import Formalism.SharpRestriction.CuspSpanNormBounds.IsTermOver
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.Saturated
import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators

noncomputable section

open scoped Classical BigOperators

namespace Formalism.L2.SG.TermLoc

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef
  Formalism.L2.SG.Saturated ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable (D : D7)

abbrev nV : ℕ := (VS D).rank

abbrev Vp (p : PlF D) : Type := Fin (nV D) → (D.s.atP p).Ep

def baseChange₂ (p : PlF D) : (VS D).V →+ Vp D p where
  toFun x i := (D.s.atP p).ιE ((VS D).frame.repr x i)
  map_zero' := by funext i; simp
  map_add' x y := by funext i; simp

def gramV (i j : Fin (nV D)) : D.host.E := brS (VS D) ((VS D).frame i) ((VS D).frame j)

variable {D}

def LocFacts₂ (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (p : PlF D) (x y : Vp D p) :
    (D.s.atP p).Ep :=
  ∑ i, ∑ j, x i * (M p).L.cj (y j) * (D.s.atP p).ιE (gramV D i j)

theorem star_gramV (i j : Fin (nV D)) : star (gramV D i j) = gramV D j i := by
  simp only [gramV, brS]
  exact (VS D).herm.eq _ _

theorem cj_iota {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep} {p : PlF D}
    (hcj : (M p).L.cj = (D.s.atP p).cj) (z : D.host.E) :
    (M p).L.cj ((D.s.atP p).ιE z) = (D.s.atP p).ιE (star z) := by
  rw [hcj, (D.s.atP p).cj_ιE, D.conjF_eq, Formalism.BasicNotions.Examples₂.star_eq_conj]

theorem gram_det_ne : (Matrix.of (gramV D)).det ≠ 0 := by
  intro h
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_vecMul_eq_zero_iff.2 h
  apply hv0
  set b := (VS D).frame
  set w : (VS D).V := ∑ i, v i • b i with hw
  have hj : ∀ j, (VS D).hT (b j) w = 0 := by
    intro j
    have := congrFun hv j
    simp only [Matrix.vecMul, dotProduct, Matrix.of_apply, Pi.zero_apply, gramV, brS] at this
    rw [hw, map_sum]
    simpa [map_smul, smul_eq_mul] using this
  have hall : (VS D).hT.flip w = 0 := b.ext fun j => by simpa using hj j
  have hw0 : w = 0 := (VS D).nondeg.2 w fun x => by
    have := congrArg (fun f => f x) hall
    simpa using this
  have := (Fintype.linearIndependent_iff.1 b.linearIndependent) v (by rw [← hw]; exact hw0)
  funext i; exact this i

instance ntEp (p : PlF D) : Nontrivial (D.s.atP p).Ep := by
  by_contra h
  rw [not_nontrivial_iff_subsingleton] at h
  have := (D.s.atP p).rank
  rw [Module.finrank_zero_of_subsingleton] at this
  omega

theorem localForm_single (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (p : PlF D) (x : Vp D p)
    (j : Fin (nV D)) :
    LocFacts₂ M p x (Pi.single j 1) = Matrix.vecMul x ((Matrix.of (gramV D)).map (D.s.atP p).ιE) j := by
  simp [LocFacts₂, Matrix.vecMul, dotProduct, Pi.single_apply, apply_ite, Finset.sum_ite_eq']

def locHerm (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (p : PlF D)
    (hcj : (M p).L.cj = (D.s.atP p).cj) : Loc.HermSp (M p) (Vp D p) where
  h := LocFacts₂ M p
  h_add_left x x' y := by
    simp only [LocFacts₂, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  h_smul_left a x y := by
    simp only [LocFacts₂, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]
  h_herm x y := by
    simp only [LocFacts₂, map_sum, map_mul, (M p).L.cj_cj, cj_iota hcj, star_gramV]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  nondeg x hx := by
    have h0 : Matrix.vecMul x ((Matrix.of (gramV D)).map (D.s.atP p).ιE) = 0 := by
      funext j; rw [← localForm_single]; exact hx _
    have hu : IsUnit ((Matrix.of (gramV D)).map (D.s.atP p).ιE).det := by
      have e : ((Matrix.of (gramV D)).map (D.s.atP p).ιE).det = (D.s.atP p).ιE (Matrix.of (gramV D)).det := by
        rw [RingHom.map_det]; rfl
      rw [e]
      exact (isUnit_iff_ne_zero.2 gram_det_ne).map _
    have := congrArg (fun v => Matrix.vecMul v ((Matrix.of (gramV D)).map (D.s.atP p).ιE)⁻¹) h0
    simpa [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hu] using this
  free := inferInstance
  fin := inferInstance

theorem finrank_Vp (p : PlF D) : Module.finrank (D.s.atP p).Ep (Vp D p) = D.R.r := by
  rw [Module.finrank_fin_fun]
  show (D.sp.Y 0).rank = _
  rw [D.sp.Y_rank 0 (Nat.zero_le _)]
  simp [Ranks.rankY]

theorem baseChange_smul₂ (p : PlF D) (a : D.host.E) (x : (VS D).V) :
    baseChange₂ D p ((a • x : (VS D).V)) = ((D.s.atP p).ιE a : (D.s.atP p).Ep) • (baseChange₂ D p x : Vp D p) := by
  funext i
  simp only [baseChange₂, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Pi.smul_apply, smul_eq_mul, LinearEquiv.map_smul,
    Finsupp.smul_apply, map_mul]

theorem baseChangeAt_frame (p : PlF D) (i : Fin (nV D)) : baseChange₂ D p ((VS D).frame i) = Pi.single i 1 := by
  funext j; simp [baseChange₂, Finsupp.single_apply, Pi.single_apply, eq_comm, apply_ite]

theorem span_baseChange_eq_top (p : PlF D) : Submodule.span (D.s.atP p).Ep (Set.range (baseChange₂ D p)) = ⊤ := by
  rw [eq_top_iff, ← (Pi.basisFun (D.s.atP p).Ep (Fin (nV D))).span_eq]
  apply Submodule.span_mono
  rintro _ ⟨i, rfl⟩
  exact ⟨(VS D).frame i, by rw [baseChangeAt_frame, Pi.basisFun_apply]⟩

theorem baseChangeAt_form (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (p : PlF D)
    (hcj : (M p).L.cj = (D.s.atP p).cj) (x y : (VS D).V) :
    LocFacts₂ M p (baseChange₂ D p x) (baseChange₂ D p y) = (D.s.atP p).ιE (brS (VS D) x y) := by
  have key : (VS D).hT y x = ∑ j, ∑ i, star ((VS D).frame.repr y j) *
      ((VS D).frame.repr x i * (VS D).hT ((VS D).frame j) ((VS D).frame i)) := by
    conv_lhs => rw [← (VS D).frame.sum_repr y, ← (VS D).frame.sum_repr x]
    simp only [map_sum, map_smulₛₗ, smul_eq_mul, starRingEnd_apply, LinearMap.sum_apply, LinearMap.smul_apply,
      RingHom.id_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
    ring
  simp only [LocFacts₂, brS, key, baseChange₂, AddMonoidHom.coe_mk, ZeroHom.coe_mk, cj_iota hcj, map_sum, map_mul, gramV]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

structure LocDat (D : D7) where
  δ : ∀ p : PlF D, (D.s.atP p).Fp
  M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep
  agree : ∀ p, Agree δ M p

theorem LocDat.hcj (Z : LocDat D) (p : PlF D) : (Z.M p).L.cj = (D.s.atP p).cj := (Z.agree p).2.2.1

def locH (Z : LocDat D) (p : PlF D) : Loc.HermSp (Z.M p) (Vp D p) := locHerm Z.M p (Z.hcj p)

variable (D) in

def sgnP (p : PlF D) (a : Fin (D.R.rS + 1)) : (D.s.atP p).Ep :=
  match (D.s.atP p).split with
  | some sg => sg.e.symm ((-1) ^ (D.R.rS - a.val), 1)
  | none => 1

variable (D) in

def sgnP' (p : PlF D) (b : Fin (D.R.rS + 1)) : (D.s.atP p).Ep :=
  match (D.s.atP p).split with
  | some _ => sgnP D p b
  | none => (-1) ^ (D.R.rS - b.val)

theorem localSign_sq (p : PlF D) (a : Fin (D.R.rS + 1)) : sgnP D p a * sgnP D p a = 1 := by
  unfold sgnP
  split
  · rename_i sg _
    rw [← map_mul]
    have h : (((-1 : (D.s.atP p).Fp) ^ (D.R.rS - a.val), (1 : (D.s.atP p).Fp)) *
        ((-1) ^ (D.R.rS - a.val), 1) : (D.s.atP p).Fp × (D.s.atP p).Fp) = 1 := by
      ext <;> simp [← mul_pow]
    rw [h, map_one]
  · exact one_mul 1

theorem sgnP'_sq (p : PlF D) (b : Fin (D.R.rS + 1)) : sgnP' D p b * sgnP' D p b = 1 := by
  unfold sgnP'
  split
  · exact localSign_sq p b
  · rw [← mul_pow]; simp

variable (D) in

def lattice₂ (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (p : PlF D)
    (Λ : Submodule (𝓞 D.host.E) (VS D).V) : Submodule (M p).L.O (Vp D p) :=
  Submodule.span (M p).L.O (baseChange₂ D p '' (Λ : Set (VS D).V))

variable (D) in

def admXi (Λ : Submodule (𝓞 D.host.E) (VS D).V) {T T' : D.host.E} (F : LFlag (VS D) D.R.rS T)
    (F' : LFlag (VS D) D.R.rS T') : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (𝓞 D.host.E) :=
  if h : IsAdmissible Λ (gS D) F F' then h.choose else 1

theorem admissibility_witness_unitriangular (Λ : Submodule (𝓞 D.host.E) (VS D).V) {T T' : D.host.E} (F : LFlag (VS D) D.R.rS T)
    (F' : LFlag (VS D) D.R.rS T') :
    (∀ a b, b < a → admXi D Λ F F' a b = 0) ∧ (∀ a, admXi D Λ F F' a a = 1) := by
  unfold admXi
  split_ifs with h
  · exact ⟨h.choose_spec.1, h.choose_spec.2.1⟩
  · exact ⟨fun a b hab => Matrix.one_apply_ne (ne_of_lt hab).symm, fun a => Matrix.one_apply_eq a⟩

theorem inv_unitri {n : ℕ} {R : Type*} [CommRing R] (ξ : Matrix (Fin n) (Fin n) R)
    (h1 : ∀ a b, b < a → ξ a b = 0) (h2 : ∀ a, ξ a a = 1) :
    (∀ a b, b < a → ξ⁻¹ a b = 0) ∧ (∀ a, ξ⁻¹ a a = 1) := by
  have hbt : ξ.BlockTriangular id := fun i j hij => h1 i j hij
  have hdet : ξ.det = 1 := by
    rw [Matrix.det_of_isUpperTriangular hbt]; simp [h2]
  have hu : IsUnit ξ.det := by rw [hdet]; exact isUnit_one
  let _inst : Invertible ξ := ξ.invertibleOfIsUnitDet hu
  have hbt' : ξ⁻¹.BlockTriangular id := Matrix.blockTriangular_inv_of_blockTriangular hbt
  refine ⟨fun a b hab => hbt' hab, fun a => ?_⟩
  have h := congrFun (congrFun (Matrix.nonsing_inv_mul ξ hu) a) a
  rw [Matrix.mul_apply, Finset.sum_eq_single a] at h
  · simpa [h2] using h
  · intro k _ hk
    rcases lt_or_gt_of_ne hk with hk | hk
    · rw [hbt' (show id k < id a from hk), zero_mul]
    · rw [h1 k a hk, mul_zero]
  · intro h; exact absurd (Finset.mem_univ a) h

def locTerm (Z : LocDat D) (p : PlF D) (Λ : Submodule (𝓞 D.host.E) (VS D).V) {T T' : D.host.E}
    (F : LFlag (VS D) D.R.rS T) (F' : LFlag (VS D) D.R.rS T') (Tn T'n : ℕ) :
    Loc.Term (Vp D p) (Z.M p) D.R.rS where
  abelian₂ := lattice₂ D Z.M p Λ
  f a := (sgnP D p a * frFac Z.δ p a) • baseChange₂ D p (frame F a)
  f' b := (sgnP' D p b * frFac Z.δ p b) • baseChange₂ D p (frameAct (frame F') (admXi D Λ F F')⁻¹ b)
  T := (Tn : (D.s.atP p).Fp)
  T' := (T'n : (D.s.atP p).Fp)

def locBBne (Z : LocDat D) (p : PlF D) (Λ : Submodule (𝓞 D.host.E) (VS D).V) {T T' : D.host.E}
    (F : LFlag (VS D) D.R.rS T) (F' : LFlag (VS D) D.R.rS T') (Tn T'n : ℕ) : Prop :=
  LocNG.BBne (H := locH Z p) (locTerm Z p Λ F F' Tn T'n)

variable (D) in

def BBTie (Z : LocDat D) : Prop :=
  ∀ (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E))
    (Λ : Submodule (𝓞 D.host.E) (VS D).V) (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)),
    IsRowLat D F0 Λ → PD D Λ (lf D F0) u' F' → MplusIndep Λ (lf D F0) (gS D) F' →
      ∀ p : PlF D, BBneF D Λ (lf D F0) F' p ↔ locBBne Z p Λ (lf D F0) F' (Tu D u) (Tu D u')

def locBBneT (Z : LocDat D) {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)}
    {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)} (t : Term D u u' F0 what₂) (p : PlF D) : Prop :=
  locBBne Z p t.lam (lf D F0) (Quot.out t.cls).1 (Tu D u) (Tu D u')

theorem termBBne_iff_loc (Z : LocDat D) (hT : BBTie D Z) {u u' : D.what₂.Word}
    {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)} {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}
    (hrows : IsRowReps D F0 what₂) (hBF : BBFun D u u')
    (hMI : ∀ (Λ : Submodule (𝓞 D.host.E) (VS D).V) (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)),
      MplusIndep Λ (lf D F0) (gS D) F')
    (t : Term D u u' F0 what₂) (p : PlF D) : termBBne t p ↔ locBBneT Z t p := by
  have hL := hrows.1 t.lam t.mem
  have hxm : mk t.lam (lf D F0) (PD D t.lam (lf D F0) u') (Quot.out t.cls) = t.cls := Quot.out_eq _
  rw [locBBneT, ← hT u u' F0 t.lam (Quot.out t.cls).1 hL (Quot.out t.cls).2 (hMI _ _) p]
  constructor
  · rintro ⟨F', ⟨h, hm⟩, P, hP, hbb⟩
    have e := const_of_mk (fun y : Carrier (PD D t.lam (lf D F0) u') => BBneP t.lam (gS D) (lf D F0) y.1 P)
      (fun a b hab => propext (hBF F0 t.lam hL P a b hab)) (hm.trans hxm.symm)
    simp only at e
    exact ⟨P, hP, e ▸ hbb⟩
  · intro h
    exact ⟨(Quot.out t.cls).1, ⟨(Quot.out t.cls).2, hxm⟩, h⟩

variable (D) in

def below (P : HeightOneSpectrum (𝓞 D.host.E)) : PlF D where
  asIdeal := P.asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E))
  isPrime := Ideal.comap_isPrime _ _
  ne_bot := fun h => P.ne_bot (Ideal.eq_bot_of_comap_eq_bot h)

variable (D) in

def GenIffLocBB (Z : LocDat D) (u u' : D.what₂.Word) : Prop :=
  ∀ (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)),
    IsRowReps D F0 what₂ → ∀ t : Term D u u' F0 what₂, t.generic ↔ ∀ p, ¬ locBBneT Z t p

theorem genIffLocBB_of (Z : LocDat D) (hT : BBTie D Z) (u u' : D.what₂.Word) (hBF : BBFun D u u')
    (hMI : ∀ (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (Λ : Submodule (𝓞 D.host.E) (VS D).V)
      (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)), MplusIndep Λ (lf D F0) (gS D) F') :
    GenIffLocBB D Z u u' := by
  intro F0 what₂ hrows t
  have hloc := fun p => termBBne_iff_loc Z hT hrows hBF (hMI F0) t p
  simp only [← hloc]
  constructor
  · intro hg p
    exact not_bbne_of_generic hrows hBF hg p
  · intro h
    have hL := hrows.1 t.lam t.mem
    have hxm : mk t.lam (lf D F0) (PD D t.lam (lf D F0) u') (Quot.out t.cls) = t.cls := Quot.out_eq _
    refine ⟨(Quot.out t.cls).1, ⟨(Quot.out t.cls).2, hxm⟩, ?_⟩
    refine generic_of_not_BBneP (hMI F0 t.lam _) hL.2.1.2.2.1 hL.2.1.2.2.2 (Quot.out t.cls).2.2.1 ?_
    intro P hP
    exact h (below D P) ⟨(Quot.out t.cls).1, ⟨(Quot.out t.cls).2, hxm⟩, P, rfl, hP⟩

variable (D) in

def locY (Z : LocDat D) (Y : TermTie D) {u u' : D.what₂.Word} (γ : D.s.Term u u') (p : PlF D) :
    Loc.Term (Vp D p) (Z.M p) D.R.rS :=
  locTerm Z p (Y.abelian₂ γ) (Y.fl γ) (Y.fl' γ) (Tu D u) (Tu D u')

variable (D) in

def RecBBTie (Z : LocDat D) (Y : TermTie D) (u u' : D.what₂.Word) : Prop :=
  ∀ (γ : D.s.Term u u') (p : PlF D), D.s.BBne γ (D.s_PlF.symm p) ↔ LocNG.BBne (H := locH Z p) (locY D Z Y γ p)

variable (D) in

def RecBBGlob (Y : TermTie D) (u u' : D.what₂.Word) : Prop :=
  ∀ (γ : D.s.Term u u') (p : PlF D), D.s.BBne γ (D.s_PlF.symm p) ↔ BBneF D (Y.abelian₂ γ) (Y.fl γ) (Y.fl' γ) p

variable (D) in

def GPtC (u u' : D.what₂.Word) : Prop :=
  ∀ γ : D.s.Term u u', (D.s.Gterm γ ≠ 0 ∧ D.s.relevant γ) ↔ Gpt (D.mem u).A.T (D.mem u').A.T (D.s.ptOf γ) ≠ 0

variable (D) in

def GenLocC (Z : LocDat D) (Y : TermTie D) (u u' : D.what₂.Word) : Prop :=
  ∀ γ : D.s.Term u u', D.s.Gterm γ ≠ 0 → (D.s.generic γ ↔ ∀ p, (locH Z p).IsGeneric (locY D Z Y γ p))

variable (D) in

def AtPtC (Z : LocDat D) (Y : TermTie D) (u u' : D.what₂.Word) : Prop :=
  ∀ γ : D.s.Term u u', D.s.generic γ → D.s.Gterm γ ≠ 0 → D.s.relevant γ → ∀ p : PlF D,
    ∃ uL uU : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Ep,
      (∀ a, uL a a = 1 ∧ uU a a = 1) ∧ (∀ a b, a < b → uL a b = 0 ∧ uU b a = 0) ∧
      (locH Z p).ZZplus (locY D Z Y γ p) = uL * modMat Z.δ (D.mem u).A.T (D.mem u').A.T p (D.s.ptOf γ) * uU

variable (D) in

def ScalarC (Z : LocDat D) (Y : TermTie D) (u u' : D.what₂.Word) : Prop :=
  ∀ P : D.s.Pair u u', Formalism.MainNotions.S.scalarP D.s P → D.s.Gterm (D.s.pfst P) ≠ 0 → D.s.Gterm (D.s.psnd P) ≠ 0 →
    ∀ p : PlF D, (locH Z p).IsScalarPair (locY D Z Y (D.s.pfst P) p) (locY D Z Y (D.s.psnd P) p)

variable (D) in

structure MassDat (Y : TermTie D) (u u' : D.what₂.Word) where
  massT : D.s.Term u u' → ℝ
  massT_nonneg : ∀ γ, 0 ≤ massT γ
  massTot : ℝ
  massTot_pos : 0 < massTot
  massPair_eq : ∀ P : D.s.Pair u u', D.s.massPair P = massT (D.s.pfst P) ∧
    D.s.massPair P = massT (D.s.psnd P) ∧ D.s.massPair P = Y.wRow P / massTot
  mass_def : ∃ (F0 : FlagG (VS D) D.R.rS ((Formalism.MainNotions.S.Lat.Tu D u : ℕ) : D.host.E))
    (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)),
    F0.e = D.sp.hypE ∧ F0.z = D.zmOf u ∧ IsRowReps D F0 what₂ ∧ massTot = ∑ Λ ∈ what₂, Formalism.MainNotions.S.wRow D F0 Λ ∧
      ∀ γ, massT γ = Formalism.MainNotions.S.wRow D F0 (Y.abelian₂ γ) / massTot
  term_inj : ∀ γ γ' : D.s.Term u u', Y.abelian₂ γ = Y.abelian₂ γ' →
    (∃ n ∈ Formalism.MainNotions.S.Lat.NLam (Y.abelian₂ γ) (Y.fl γ), ∃ m ∈ Formalism.MainNotions.S.Lat.NLam (Y.abelian₂ γ) (Y.fl' γ),
      ∀ b, Formalism.MainNotions.S.Lat.frame (Y.fl' γ') b = n (m (Formalism.MainNotions.S.Lat.frame (Y.fl' γ) b))) → γ = γ'

def mkTermLoc (Z : LocDat D) (Y : TermTie D) (u u' : D.what₂.Word) (hG : GPtC D u u') (hgen : GenLocC D Z Y u u')
    (hat : AtPtC D Z Y u u') (hsc : ScalarC D Z Y u u') (ms : MassDat D Y u u') :
    Formalism.MainNotions.S.LocalSplitGroups.TermLoc D Y Z.δ Z.M u u' where
  V := Vp D
  H := locH Z
  rank := finrank_Vp
  bc := baseChange₂ D
  bc_smul := baseChange_smul₂
  bc_span := span_baseChange_eq_top
  bc_form p x y := baseChangeAt_form Z.M p (Z.hcj p) x y
  sgn := sgnP D
  sgn' := sgnP' D
  sgn_sq p a := ⟨localSign_sq p a, sgnP'_sq p a⟩
  loc γ p := locY D Z Y γ p
  loc_Lam _ _ := rfl
  loc_f _ _ _ := rfl
  loc_f' γ _ := ⟨(admXi D (Y.abelian₂ γ) (Y.fl γ) (Y.fl' γ))⁻¹,
    (inv_unitri _ (admissibility_witness_unitriangular (Y.abelian₂ γ) (Y.fl γ) (Y.fl' γ)).1 (admissibility_witness_unitriangular (Y.abelian₂ γ) (Y.fl γ) (Y.fl' γ)).2).1,
    (inv_unitri _ (admissibility_witness_unitriangular (Y.abelian₂ γ) (Y.fl γ) (Y.fl' γ)).1 (admissibility_witness_unitriangular (Y.abelian₂ γ) (Y.fl γ) (Y.fl' γ)).2).2,
    fun _ => rfl⟩
  local_group_in_family_nontrivial _ _ := ⟨rfl, rfl⟩
  G_pt := hG
  generic_iff := hgen
  at_pt := hat
  scalar_loc := hsc
  massT := ms.massT
  massT_nonneg := ms.massT_nonneg
  massTot := ms.massTot
  massTot_pos := ms.massTot_pos
  massPair_eq := ms.massPair_eq
  mass_def := ms.mass_def
  term_inj := ms.term_inj

variable (D) in

def LocDatExists : Prop := Nonempty (LocDat D)

theorem recGenIff_of (Z : LocDat D) (Y : TermTie D) (u u' : D.what₂.Word) (hY : RecBBGlob D Y u u')
    (hR : RecBBTie D Z Y u u')
    (hMI : ∀ γ : D.s.Term u u', MplusIndep (Y.abelian₂ γ) (Y.fl γ) (gS D) (Y.fl' γ)) (γ : D.s.Term u u') :
    D.s.generic γ ↔ ∀ p : PlF D, ¬ LocNG.BBne (H := locH Z p) (locY D Z Y γ p) := by
  simp only [← hR γ, hY γ, Y.gen_iff γ]
  constructor
  · rintro hg p ⟨P, -, hP⟩
    exact not_BBneP_of_generic hg P hP
  · intro h
    have hfix := Y.fixed γ
    refine generic_of_not_BBneP (hMI γ) hfix.2.2.1 hfix.2.2.2 (Y.adm γ) ?_
    intro P hP
    exact h (below D P) ⟨P, rfl, hP⟩

theorem recBBTie_of (Z : LocDat D) (hT : BBTie D Z) (Y : TermTie D) (u u' : D.what₂.Word) (hY : RecBBGlob D Y u u')
    (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (hfl : ∀ γ : D.s.Term u u', Y.fl γ = lf D F0)
    (hrow : ∀ γ : D.s.Term u u', IsRowLat D F0 (Y.abelian₂ γ))
    (hok : ∀ γ : D.s.Term u u', FrameOK D (Y.abelian₂ γ) (Y.fl' γ))
    (hMI : ∀ γ : D.s.Term u u', MplusIndep (Y.abelian₂ γ) (lf D F0) (gS D) (Y.fl' γ)) : RecBBTie D Z Y u u' := by
  intro γ p
  rw [hY γ p]
  unfold locY
  have hadm := Y.adm γ
  rw [hfl γ] at hadm ⊢
  exact hT u u' F0 (Y.abelian₂ γ) (Y.fl' γ) (hrow γ) ⟨Y.lift' γ, hadm, hok γ⟩ (hMI γ) p

end Formalism.L2.SG.TermLoc
