import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsKitWithKitWith
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SSupCompSecId
import Development.AbelianVarietyTheory.Definitions.Divisors.ReferenceMetricMulDualEqOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagNonempty
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyToroidalBoundaryDataOfSncStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBoundaryOfTorusDataStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NatCastMemNonunitsOfInduces
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBettiOfFlatStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlatSectionIsFlatStatement
import Formalism.SharpRestriction.Divisibility.PlaceRankTwoOne

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory.Toroidal GlobalTheory.TrueGeo GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjVar GlobalTheory.Cartier

namespace GlobalTheory.ShFam.KitCheck

variable {D : D7}

theorem nonempty_stFams (D : D7) : Nonempty (StFams D) := ⟨fun _ _ _ S κ => AllPrimesCheck.stFam0 S κ⟩

theorem exists_mem (st : StFams D) {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} (s : FinalTheorems S κ) (L : CmList A)
    {jC : JC D} (hj : jC.Pinned) (hA : AdmEx S κ) (hP : ∀ (Φ : s.Flag) (x : ToroidalCompactificationData s), Nonempty (PolOf x Φ)) :
    ∃ k d, IsKitOf st A N j S κ s L jC k d := by
  obtain ⟨Φ⟩ := KitEx.flag_nonempty s
  obtain ⟨key⟩ := KitEx.key_nonempty s
  obtain ⟨x⟩ : Nonempty (ToroidalCompactificationData s) := GlobalTheory.T.nonempty_toroidal_boundary_data_of_snc _ _ _ _ _ _ _ _ s.T.Z s.T.snc
  obtain ⟨P⟩ := hP Φ x
  obtain ⟨B, hB⟩ := GlobalTheory.T.exists_boundary_of_torus_data D A N j S κ s L x
  choose cts hc using fun (p : ℕ) [hp : Fact p.Prime] (v : PlL D p) =>
    exists_at D A N j S κ p hp.out _ (placeW_over D p v _ (hj p v)).1
  exact ⟨kitWith _ L Φ key x B P cts hj hA, _, x, P, cts, hj, hA, isKitWith_kitWith _ Φ key hB P hc hj hA⟩

section One

variable {st : StFams D} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {s : FinalTheorems S κ} {L : CmList A} {jC : JC D}

theorem core_of_mem (hi : 1 ≤ j ∧ j < N) {k : KitT s L jC} {d : s.Comp → D.what₂.Tau → ℝ}
    (h : IsKitOf st A N j S κ s L jC k d) (adm : AdmSt D N j jC) :
    ∃ m : GlobalTheory.Mean4O.MetIn k.Φ, (GlobalTheory.Mean4O.Setup.ofKit hi k adm m).Core :=
  have ⟨x, P, _, _, _, h⟩ := h
  ⟨_, x, P, GlobalTheory.Mean4O.Setup.coreWith_ofKit hi k adm h.bd h.fl h.mb⟩

theorem not_mem_placeholder (hb : (genBd s.T.Z : Set (gen s.T.Z : Scheme.{0})).Nonempty) (Φ : s.Flag)
    (key : KeySec s.Xo κ.c) (pad : PadPkg D N j s.Comp jC ngTrue) (d : s.Comp → D.what₂.Tau → ℝ) :
    ¬ IsKitOf st A N j S κ s L jC (KitEx.kitOf s L _ Φ key pad) d := fun h => h.bd_ne_invariant hb rfl

theorem qDiv_mb {k : KitT s L jC} {d : s.Comp → D.what₂.Tau → ℝ} (h : IsKitOf st A N j S κ s L jC k d) :
    ∃ bd : ∀ c, (k.Φ.C c).Y.Dv, (∀ c, (bd c).Eff ∧ ∀ y, y ∈ (bd c).supp ↔ (k.Φ.C c).π y ∈ genBd s.T.Z) ∧
      ∀ (B : ℝ) (u : D.what₂.Tau → Fin N → ℚ) (r : ℚ), 0 < r → ∀ c,
        qDiv (k.Mb B (fun τ i => u τ i) r c) = qL k.Φ c u - r ⊗ₜ bd c := by
  obtain ⟨x, P, _, _, _, h⟩ := h
  refine ⟨P.bd, fun c => ⟨P.eff_bd c, P.mem_supp_bd c⟩, fun B u r hr c => ?_⟩
  rw [h.mb, mbarOf_cast P B u hr, P.qDiv_mbarQ]

theorem innerPt_spec (Φ : s.Flag) (c : s.Comp) :
    IsClosed ({innerPt s Φ c} : Set (Φ.C c).Y.X) ∧ (Φ.C c).π (innerPt s Φ c) ∉ genBd s.T.Z := by
  refine Classical.epsilon_spec (p := fun x => IsClosed ({x} : Set (Φ.C c).Y.X) ∧ (Φ.C c).π x ∉ genBd s.T.Z) ?_
  have : JacobsonSpace (Φ.C c).Y.X := LocallyOfFiniteType.jacobsonSpace (Φ.C c).Y.str
  have ho : IsOpen ((Φ.C c).π ⁻¹' (genBd s.T.Z : Set (gen s.T.Z : Scheme.{0}))ᶜ) :=
    (genBd s.T.Z).isClosed.isOpen_compl.preimage (Φ.C c).π.continuous
  obtain ⟨y, h1, h2⟩ := nonempty_inter_closedPoints (Z := (Φ.C c).π ⁻¹' (genBd s.T.Z : Set (gen s.T.Z : Scheme.{0}))ᶜ)
    ⟨genericPoint _, fun h => CartierDiv.genericPoint_notMem_supp (Φ.C c).bd (((Φ.C c).bd_supp _).2 h)⟩
    ho.isLocallyClosed
  exact ⟨y, h2, h1⟩

theorem parOf_detSym (a : ℕ → Bool) (τ : D.host.E →+* ℂ) : parOf (detSym S.Dw a none τ) = none := by
  classical
  unfold parOf
  split_ifs with h
  · obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.1 (Finsupp.support_finsetSum h.choose_spec)
    unfold rootSym at hi
    split_ifs at hi <;> rw [Finset.mem_singleton.1 (Finsupp.support_single_subset hi)]
  · rfl

theorem metsOf_none_h (x x' : ToroidalCompactificationData s) (Φ : s.Flag) (c : s.Comp) (σ : D.what₂.LL →+* ℂ) (n : Letter S.Dw → ℤ)
    {z : Pts (Φ.C c).Y σ} (hz : (Φ.C c).π (under z) ∉ genBd s.T.Z) (a : (Φ.C c).Y.Fnˣ) :
    Var.Met.h (metsOf x Φ c none σ n) a z = Var.Met.h (metsOf x' Φ c none σ n) a z := by
  refine FlagCpt.met_congr (x.eigMetAt _ none) n (G' := x'.eigMetAt _ none) (fun g τ => ?_) a
  obtain ⟨f, hf⟩ := (FinalTheorems.exists_isHodgeFrame_iff (s := s) (y := (Φ.C c).down z)).2 hz
  exact (x.hodge_gram hf g τ).trans (x'.hodge_gram hf g τ).symm

theorem ht_det_eq (x x' : ToroidalCompactificationData s) (Φ : s.Flag) (c : s.Comp) (a : ℕ → Bool) (τ : D.host.E →+* ℂ) :
    (adlOf (Φ.C c) (metsOf x Φ c) (detSym S.Dw a none τ)).ht (innerPt s Φ c) =
      (adlOf (Φ.C c) (metsOf x' Φ c) (detSym S.Dw a none τ)).ht (innerPt s Φ c) := by
  have key : ∀ (σ : D.what₂.LL →+* ℂ) (z : Pts (Φ.C c).Y σ), under z = innerPt s Φ c → ∀ (R : Option ℝ), R = none →
      ∀ n f, (cxSt D.what₂.LL).pn _ σ _ (metsOf x Φ c R σ n) f z = (cxSt D.what₂.LL).pn _ σ _ (metsOf x' Φ c R σ n) f z := by
    rintro σ z hz _ rfl n f
    exact congrArg (‖Var.fval (Var.eqn _ z) f z‖ ^ 2 * ·) (metsOf_none_h x x' Φ c σ n (hz ▸ (innerPt_spec Φ c).2) _)
  unfold Adl.ht
  refine congrArg₂ (· / ·) (congrArg Neg.neg (congrArg₂ (· + ·) ?_ rfl)) rfl
  refine Finset.sum_congr rfl fun σ _ => finsum_congr fun z => finsum_congr fun hz => ?_
  exact congrArg₂ (· - ·) (congrArg (Real.log · / 2) (key σ z hz _ (parOf_detSym a τ) _ _)) rfl

theorem deg_unique {k : KitT s L jC} {d d' : s.Comp → D.what₂.Tau → ℝ} {st' : StFams D}
    (h : IsKitOf st A N j S κ s L jC k d) (h' : IsKitOf st' A N j S κ s L jC k d') : d = d' := by
  obtain ⟨x, _, _, _, _, h⟩ := h
  obtain ⟨x', _, _, _, _, h'⟩ := h'
  funext c τ
  rw [h.deg, h'.deg, degFlat, degFlat, degFrame, degFrame, ht_det_eq x x']

theorem not_mem_add_one {k : KitT s L jC} {d : s.Comp → D.what₂.Tau → ℝ} (h : IsKitOf st A N j S κ s L jC k d)
    (τ : D.what₂.Tau) : ¬ IsKitOf st A N j S κ s L jC k (d + 1) := fun h' =>
  have ⟨c⟩ := s.compNe
  by simpa using congrFun₂ (deg_unique h' h) c τ

theorem isBetti_of_mem {k : KitT s L jC} {d : s.Comp → D.what₂.Tau → ℝ} (h : IsKitOf st A N j S κ s L jC k d)
    (c : s.Comp) (τ : D.what₂.Tau) : IsFlat (k.Φ.C c) (DV.tauEmb D τ) (flatSec s k.Φ c τ) ∧
      IsBetti s k.Φ L c τ (flatSec s k.Φ c τ) (k.fl c τ) :=
  have ⟨_, _, _, _, _, h⟩ := h
  have hf := GlobalTheory.T.flat_section_isFlat D A N j S κ s k.Φ c τ
  ⟨hf, h.isBetti (GlobalTheory.T.exists_betti_of_flat D A N j S κ s k.Φ L c τ _ hf)⟩

theorem not_mem_fl {k : KitT s L jC} {d d' : s.Comp → D.what₂.Tau → ℝ} (h : IsKitOf st A N j S κ s L jC k d)
    (τ : D.what₂.Tau) : ¬ IsKitOf st A N j S κ s L jC { k with fl := fun c t => -k.fl c t } d' := fun h' => by
  obtain ⟨c⟩ := s.compNe
  have e : -k.fl c τ = k.fl c τ := (congrFun₂ h'.fl_eq c τ).trans (congrFun₂ h.fl_eq c τ).symm
  have e' := congrArg (Units.val) e
  rw [Units.val_neg, neg_eq_iff_add_eq_zero, ← two_mul] at e'
  exact mul_ne_zero two_ne_zero (k.fl c τ).ne_zero e'

theorem eq_setup_kit (hi : 1 ≤ j ∧ j < N) {k : KitT s L jC} {d : s.Comp → D.what₂.Tau → ℝ}
    (h : IsKitOf st A N j S κ s L jC k d) : ∃ (adm : AdmSt D N j jC) (m : GlobalTheory.Mean4O.MetIn k.Φ),
      (GlobalTheory.Mean4O.Setup.ofKit hi k adm m).Core ∧ (GlobalTheory.Mean4O.Setup.ofKit hi k adm m).pad = k.pad := by
  obtain ⟨x, P, cts, hj, hA, h⟩ := h
  refine ⟨admissible_representation_factorisation S κ jC hj hA, GlobalTheory.Mean4O.metTrue x k.Φ P,
    ⟨x, P, GlobalTheory.Mean4O.Setup.coreWith_ofKit hi k _ h.bd h.fl h.mb⟩, ?_⟩
  have e := h.pad_eq
  change padAt _ (.ofPkg k.pad) (.ofPkg k.pad) _ _ _ = _
  generalize k.pad = Q at e ⊢
  subst e
  rfl

theorem ats_place {F : StFam S κ} {k : KitT s L jC} {d : s.Comp → D.what₂.Tau → ℝ} {x : ToroidalCompactificationData s} {P : PolOf x k.Φ}
    {cts : Ats S κ} {hj : jC.Pinned} {hA : AdmEx S κ} (h : IsKitWith F s L jC k d x P cts hj hA) (p : ℕ) [Fact p.Prime]
    (v : PlL D p) (a : D.what₂.LL) :
    ((κ.e a : κ.c.F) : ℂ) ∈ (cts p v).W ↔ v.1.valuation D.what₂.LL a ≤ 1 := by
  rw [h.ats p v, κ.e_emb]
  exact (placeW_over D p v _ (hj p v)).2 a

theorem normDet_of_mem {k : KitT s L jC} {d : s.Comp → D.what₂.Tau → ℝ} (h : IsKitOf st A N j S κ s L jC k d) :
    ∃ (e : k.pad.Pt = Pt s) (x : ToroidalCompactificationData s), ∀ p τ y,
      k.pad.normDetT p τ y = normDetAt s p true τ (cast e y) ((flatSt s k.Φ (metsOf x k.Φ)).sv τ (cast e y)) ∧
      k.pad.normDetH p τ y = normDetAt s p false τ (cast e y) ((flatSt s k.Φ (metsOf x k.Φ)).sv τ (cast e y)) := by
  obtain ⟨x, P, cts, hj, hA, h⟩ := h
  have e := h.pad
  generalize k.pad = Q at e ⊢
  subst e
  exact ⟨rfl, x, fun _ _ _ => ⟨rfl, rfl⟩⟩

theorem deg_defect {F : StFam S κ} {k : KitT s L jC} {d : s.Comp → D.what₂.Tau → ℝ} {x : ToroidalCompactificationData s} {P : PolOf x k.Φ}
    {cts : Ats S κ} {hj : jC.Pinned} {hA : AdmEx S κ} (h : IsKitWith F s L jC k d x P cts hj hA) (c : s.Comp)
    (τ : D.what₂.Tau) : d c τ = degFrame s k.Φ (metsOf x k.Φ) c τ +
      ((N - j : ℕ) : ℝ) * (2 * Real.log (placeRankTwoOne.rdK D) - Real.log D.host.rdE) := by
  have hq : S.Dw.q = N - j := by have := S.p_eq; have := S.rank_eq; omega
  have h0 : (0 : ℝ) < |(discr D.host.E : ℝ)| := abs_pos.2 (Int.cast_ne_zero.2 (discr_ne_zero _))
  rw [h.deg, degFlat, hq, A.d_eq, placeRankTwoOne.rdK, Real.log_sqrt (Nat.cast_nonneg _), Formalism.BasicNotions.Host.rdE, Real.log_rpow h0,
    Nat.cast_natAbs, Int.cast_abs]
  ring

end One

end GlobalTheory.ShFam.KitCheck
