import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.KerDatTuple
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Development.AbelianVarietyTheory.Definitions.Divisors.IsDeltaDelAtOwnAt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilActionLiftPairStepVectorInvLevelChar
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelCharactersRamificationLevelPlaces
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TameHeckeCharSplitSupportedEqProdResidueStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeCharTrivialOnIdempotentIntegralUnitsStatement

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound

namespace GlobalTheory.KerMove

variable {D : D7}

theorem ramif_ker {T0 : Type} {L : LevCh D T0} {μ0 : T0} (hL : L.Is μ0) {ξ : Formalism.L2.Host.HChar D.host.E}
    {Q : Finset (Pl D.host.E)} (hpl : IsTwistPlaces D.host.g Q)
    (hram : ∀ PP, ¬ ξ.UnrAt PP ↔ PP ∈ Q ∨ ∃ PP' ∈ Q, IsConjPl PP' PP) (j : Fin D.R.m) :
    Disjoint L.Pg Q ∧ (∀ PP ∈ Q, (L.C.mu0 j).UnrAt PP) ∧ (∀ PP ∈ L.Pg, ξ.UnrAt PP) ∧
      ∀ PP', PP' ∉ L.Pg → (∀ PP ∈ L.Pg, ¬ IsConjPl PP PP') → (L.C.mu0 j).UnrAt PP' := by
  classical
  have hoff : ∀ (k : Fin 2) (PP : Pl D.host.E), ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal →
      PP ∉ Q ∧ ¬ ∃ PP' ∈ Q, IsConjPl PP' PP := by
    intro k PP hk
    refine ⟨fun hQ => ?_, fun ⟨PP', hQ, hc⟩ => ?_⟩
    · obtain ⟨q, hq, hm, hne⟩ := GlobalTheory.LevelRamif.exists_prime_mem hpl hQ
      exact GlobalTheory.LevelRamif.not_two_primes PP hq (D.host.g_prime k) (hne k) hm hk
    · obtain ⟨q, hq, hm, hne⟩ := GlobalTheory.LevelRamif.exists_prime_mem hpl hQ
      exact GlobalTheory.LevelRamif.not_two_primes PP hq (D.host.g_prime k) (hne k) (GlobalTheory.LevelRamif.natCast_mem_conj hc hm) hk
  have hPg : ∀ PP ∈ L.Pg, PP ∉ Q ∧ ¬ ∃ PP' ∈ Q, IsConjPl PP' PP := by
    intro PP h
    obtain ⟨k, hk⟩ := (hL.Pg PP).1 h
    exact hoff k PP (GlobalTheory.LevelRamif.typePrime_mem hk)
  have hM := L.C.isMu0 j
  refine ⟨Finset.disjoint_left.2 fun PP h => (hPg PP h).1, fun PP hQ => ?_, fun PP h => ?_, fun PP h1 h2 => ?_⟩
  · exact hM.unr PP fun k hk => (hoff k PP hk).1 hQ
  · by_contra hn
    rcases (hram PP).1 hn with h' | h'
    · exact (hPg PP h).1 h'
    · exact (hPg PP h).2 h'
  · refine hM.unr PP fun k hk => ?_
    rcases GlobalTheory.ConjOverQuad.div_or_conj_div D L.C.P k PP hk with h | ⟨PP', h, hc⟩
    · exact h1 ((hL.Pg PP).2 ⟨k, h⟩)
    · exact h2 PP' ((hL.Pg PP').2 ⟨k, h⟩) (GlobalTheory.LevelRamif.isConjPl_of_eq hc)

theorem unrOff_ker {T0 : Type} {L : LevCh D T0} {μ0 : T0} (hL : L.Is μ0) {ξ : Formalism.L2.Host.HChar D.host.E}
    {χ : (AE D)ˣ →* Circle} {Q : Finset (Pl D.host.E)} (hchr : ChrEq χ ξ) (hpl : IsTwistPlaces D.host.g Q)
    (hram : ∀ PP, ¬ ξ.UnrAt PP ↔ PP ∈ Q ∨ ∃ PP' ∈ Q, IsConjPl PP' PP) (j : Fin D.R.m)
    {P : Finset (Pl D.host.E)} {e : AE D} (hP : ∀ PP, PP ∈ P ↔ PP ∈ L.Pg ∨ PP ∈ Q) (he : IsIdemSum e P) :
    GlobalTheory.VecInv.UnrOff (e + cA D e) (L.mu0 ((j : ℕ) + 1) * χ) ∧ GlobalTheory.VecInv.UnrOff (e + cA D e) L.eta := by
  obtain ⟨-, -, -, h4⟩ := ramif_ker hL hpl hram j
  refine ⟨GlobalTheory.VecInv.UnrOff.mul (GlobalTheory.T.heckeChar_trivial_on_idempotentIntegralUnits D _ _ P e (hL.mu0 j) he fun PP' h1 h2 =>
      h4 PP' (fun h => h1 ((hP _).2 (Or.inl h))) fun PP h => h2 PP ((hP _).2 (Or.inl h)))
    (GlobalTheory.T.heckeChar_trivial_on_idempotentIntegralUnits D _ _ P e hchr he fun PP' h1 h2 => ?_), GlobalTheory.T.heckeChar_trivial_on_idempotentIntegralUnits D _ _ P e hL.eta he fun PP' _ _ => L.C.isEta.unr PP'⟩
  by_contra hn
  rcases (hram PP').1 hn with h | ⟨PP, h, h'⟩
  · exact h1 ((hP _).2 (Or.inr h))
  · exact h2 PP ((hP _).2 (Or.inr h)) h'

theorem val_ker {T0 : Type} {L : LevCh D T0} {μ0 : T0} (hL : L.Is μ0) {ξ : Formalism.L2.Host.HChar D.host.E}
    {χ : (AE D)ˣ →* Circle} {ξR : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ} {Q : Finset (Pl D.host.E)} (hchr : ChrEq χ ξ)
    (htame : ∀ v, ξ.TameAt v) (hres : ∀ PP ∈ Q, IsRes ξ PP (ξR PP)) (hpl : IsTwistPlaces D.host.g Q)
    (hram : ∀ PP, ¬ ξ.UnrAt PP ↔ PP ∈ Q ∨ ∃ PP' ∈ Q, IsConjPl PP' PP) (j : Fin D.R.m)
    {P : Finset (Pl D.host.E)} {e : AE D} (hP : ∀ PP, PP ∈ P ↔ PP ∈ L.Pg ∨ PP ∈ Q) (he : IsIdemSum e P)
    (x : (AE D)ˣ) (a : AE D) (a' : Formalism.L2.Herm.intAf D.host.F D.host.E) (u : ∀ PP : Pl D.host.E, (kP PP)ˣ)
    (hx : (x : AE D) = e * a + (1 - e)) (ha : (a' : Lev.EAf D) = toEAf D a)
    (hu : ∀ PP ∈ P, (u PP : kP PP) = resS D.host.F PP a') :
    ((L.mu0 ((j : ℕ) + 1) x : Circle) : ℂ) = ((∏ PP ∈ L.Pg, (L.chi ((j : ℕ) + 1) PP (u PP))⁻¹ : ℂˣ) : ℂ) ∧
      ((χ x : Circle) : ℂ) = ((∏ PP ∈ Q, ξR PP (u PP) : ℂˣ) : ℂ) ∧ L.eta x = 1 := by
  classical
  obtain ⟨-, h2, h3, -⟩ := ramif_ker hL hpl hram j
  have e1 := GlobalTheory.T.tameHeckeChar_splitSupported_eq_prod_residue D _ _ P e (fun PP => if PP ∈ L.Pg then (L.chi ((j : ℕ) + 1) PP)⁻¹ else 1) (hL.mu0 j) he
    (fun PP h => ⟨(L.C.isMu0 j).tame PP, by
      by_cases hg : PP ∈ L.Pg
      · rw [if_pos hg]; exact hL.chi j PP hg
      · rw [if_neg hg]; exact GlobalTheory.VecInv.isRes_one (h2 PP (((hP _).1 h).resolve_left hg))⟩) x a a' u hx ha hu
  have e2 := GlobalTheory.T.tameHeckeChar_splitSupported_eq_prod_residue D _ _ P e (fun PP => if PP ∈ Q then ξR PP else 1) hchr he
    (fun PP h => ⟨htame PP, by
      by_cases hg : PP ∈ Q
      · rw [if_pos hg]; exact hres PP hg
      · rw [if_neg hg]; exact GlobalTheory.VecInv.isRes_one (h3 PP (((hP _).1 h).resolve_right hg))⟩) x a a' u hx ha hu
  have e3 := GlobalTheory.T.tameHeckeChar_splitSupported_eq_prod_residue D _ _ P e (fun _ => 1) hL.eta he
    (fun PP _ => ⟨GlobalTheory.VecInv.tameAt_of_unrAt (L.C.isEta.unr PP), GlobalTheory.VecInv.isRes_one (L.C.isEta.unr PP)⟩) x a a' u hx ha hu
  refine ⟨?_, ?_, Subtype.ext (e3.trans (Finset.prod_eq_one fun _ _ => rfl))⟩
  · rw [e1, Units.coe_prod]
    symm
    refine Finset.prod_subset_one_on_sdiff (fun PP h => (hP _).2 (Or.inl h)) (fun PP h => ?_) fun PP h => ?_
    · rw [if_neg (Finset.mem_sdiff.1 h).2]; rfl
    · rw [if_pos h]; rfl
  · rw [e2, Units.coe_prod]
    symm
    refine Finset.prod_subset_one_on_sdiff (fun PP h => (hP _).2 (Or.inr h)) (fun PP h => ?_) fun PP h => ?_
    · rw [if_neg (Finset.mem_sdiff.1 h).2]; rfl
    · rw [if_pos h]

end GlobalTheory.KerMove

namespace GlobalTheory.KerMove

variable {D : D7}

def RootLL (D : D7) (w : ℂ) : Prop := ∃ z : D.what₂.LL, IsOfFinOrder z ∧ D.what₂.embLL z = w

theorem RootLL.one : RootLL D 1 := ⟨1, isOfFinOrder_iff_pow_eq_one.2 ⟨1, one_pos, one_pow 1⟩, map_one _⟩

theorem RootLL.mul {w w' : ℂ} (h : RootLL D w) (h' : RootLL D w') : RootLL D (w * w') := by
  obtain ⟨z, hz, rfl⟩ := h
  obtain ⟨z', hz', rfl⟩ := h'
  exact ⟨z * z', hz.mul hz', map_mul _ _ _⟩

theorem RootLL.inv {w : ℂ} (h : RootLL D w) : RootLL D w⁻¹ := by
  obtain ⟨z, hz, rfl⟩ := h
  obtain ⟨n, hn, hzn⟩ := isOfFinOrder_iff_pow_eq_one.1 hz
  exact ⟨z⁻¹, isOfFinOrder_iff_pow_eq_one.2 ⟨n, hn, by rw [inv_pow, hzn, inv_one]⟩, map_inv₀ _ _⟩

theorem RootLL.units_prod {ι : Type} (s : Finset ι) (f : ι → ℂˣ) (h : ∀ i ∈ s, RootLL D (f i : ℂ)) :
    RootLL D ((∏ i ∈ s, f i : ℂˣ) : ℂ) := by
  rw [Units.coe_prod]
  exact Finset.prod_induction _ (RootLL D) (fun _ _ => RootLL.mul) RootLL.one h

theorem RootLL.of_range {w : ℂ} (hw : w ∈ D.what₂.embLL.range) (ho : IsOfFinOrder w) : RootLL D w := by
  obtain ⟨z, rfl⟩ := hw
  obtain ⟨n, hn, hzn⟩ := isOfFinOrder_iff_pow_eq_one.1 ho
  refine ⟨z, isOfFinOrder_iff_pow_eq_one.2 ⟨n, hn, D.what₂.embLL.injective ?_⟩, rfl⟩
  rw [map_pow, hzn, map_one]

theorem rootLL_res {ξ : Formalism.L2.Host.HChar D.host.E} (hv : ∀ x, ((ξ.1 x : ℂˣ) : ℂ) ∈ D.what₂.embLL.range)
    (hfin : ∃ n : ℕ, 0 < n ∧ ξ.OrderDvd n) {PP : Pl D.host.E} {c : (kP PP)ˣ →* ℂˣ} (hc : IsRes ξ PP c)
    (u : (kP PP)ˣ) : RootLL D ((c u : ℂˣ) : ℂ) := by
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (u : kP PP)
  have ha0 : ((a : 𝓞 D.host.E) : D.host.E) ≠ 0 := by
    intro h0
    have : a = 0 := RingOfIntegers.ext (by rw [h0]; rfl)
    apply u.ne_zero
    rw [← ha, this, map_zero]
  have e := hc a (Units.mk0 _ ha0) u rfl ha.symm
  rw [e]
  obtain ⟨n, hn, hξ⟩ := hfin
  have hord : ∀ y, IsOfFinOrder ((ξ.1 y : ℂˣ) : ℂ) := fun y => by
    refine isOfFinOrder_iff_pow_eq_one.2 ⟨n, hn, ?_⟩
    have h1 : (ξ ^ n).1 = (1 : Formalism.L2.Host.HChar D.host.E).1 := congrArg Subtype.val hξ
    have h2 := congrArg Units.val (DFunLike.congr_fun h1 y)
    simpa using h2
  exact RootLL.of_range (hv _) (hord _)

end GlobalTheory.KerMove

namespace GlobalTheory.KerMove

variable {D : D7}

def diagU {K : Type} [CommRing K] {r : ℕ} (d : Fin r → Kˣ) : GL (Fin r) K :=
  ⟨Matrix.diagonal fun a => (d a : K), Matrix.diagonal fun a => ((d a)⁻¹ : Kˣ),
    by rw [Matrix.diagonal_mul_diagonal]; simp, by rw [Matrix.diagonal_mul_diagonal]; simp⟩

theorem det_diagU {K : Type} [CommRing K] {r : ℕ} (d : Fin r → Kˣ) :
    Matrix.GeneralLinearGroup.det (diagU d) = ∏ a, d a := by
  ext
  simp [diagU, Matrix.det_diagonal]

theorem one_le_r : 1 ≤ D.R.r := by
  unfold Formalism.BasicNotions.Ranks.r
  have := D.R.two_le_m
  omega

theorem rootLL_chi {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A} (hg : R.IsGrp F)
    (j : Fin D.R.m) (u : ∀ PP : Pl D.host.E, (kP PP)ˣ) :
    RootLL D ((∏ PP ∈ R.Pg, R.chi ((j : ℕ) + 1) PP (u PP) : ℂˣ) : ℂ) := by
  classical
  have hr := one_le_r (D := D)
  let g0 : G0 R.Pg D.R.r := fun PP => diagU (Pi.mulSingle (⟨0, hr⟩ : Fin D.R.r) (u PP.1))
  have hdet : ∀ PP : R.Pg, Matrix.GeneralLinearGroup.det (g0 PP) = u PP.1 := fun PP => by
    simp only [g0, det_diagU]
    exact Fintype.prod_pi_mulSingle' _ _
  have h1 := hg.chiW j (R.eG.symm g0)
  simp only [MulEquiv.apply_symm_apply, hdet] at h1
  have e : ((∏ PP ∈ R.Pg, R.chi ((j : ℕ) + 1) PP (u PP) : ℂˣ) : ℂ) =
      ∏ PP : R.Pg, ((R.chi ((j : ℕ) + 1) PP.1 (u PP.1) : ℂˣ) : ℂ) := by
    rw [Units.coe_prod]
    exact (Finset.prod_coe_sort R.Pg (fun PP => ((R.chi ((j : ℕ) + 1) PP (u PP) : ℂˣ) : ℂ))).symm
  refine RootLL.of_range ⟨_, h1.trans e.symm⟩ ?_
  refine (Units.coeHom ℂ).isOfFinOrder ?_
  exact Finset.prod_induction _ IsOfFinOrder (fun _ _ h h' => h.mul h') (isOfFinOrder_iff_pow_eq_one.2 ⟨1, one_pos, one_pow 1⟩)
    fun PP _ => (R.chi ((j : ℕ) + 1) PP).isOfFinOrder (isOfFinOrder_of_finite _)

end GlobalTheory.KerMove

namespace GlobalTheory.KerMove

variable {D : D7}

theorem smul_root {X : Type} {f f' : X → ℂ} {A : ℂˣ} {s : ℂ} (h : (A : ℂ) • f = s • f') (hA : RootLL D (A : ℂ))
    (hs : RootLL D s) : ∃ (z : D.what₂.LL) (n : ℕ), 0 < n ∧ z ^ n = 1 ∧ f = D.what₂.embLL z • f' := by
  obtain ⟨z, hz, hz'⟩ := hA.inv.mul hs
  obtain ⟨n, hn, hzn⟩ := isOfFinOrder_iff_pow_eq_one.1 hz
  refine ⟨z, n, hn, hzn, ?_⟩
  rw [hz', mul_smul, ← h, smul_smul, inv_mul_cancel₀ (Units.ne_zero A), one_smul]

theorem smul_fix {X : Type} {f f' : X → ℂ} {A : ℂˣ} {s : ℂ} (h : (A : ℂ) • f = s • f') (hs : s = A) : f = f' := by
  rw [hs] at h
  exact smul_right_injective _ (Units.ne_zero A) h

end GlobalTheory.KerMove

namespace GlobalTheory.KerMove

theorem kerDat_move : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m), ∀ (ξ : Formalism.L2.Host.HChar D.host.E) (χ : (AE D)ˣ →* Circle) (ξR : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (Q : Finset (Pl D.host.E)) (ω : WeilRep D i) (φ : WO (Vc D i) (Wc D i) → ℂ), KerDat R i ξ χ ξR Q ω φ → (∀ x, ((ξ.1 x : ℂˣ) : ℂ) ∈ D.what₂.embLL.range) → (∀ k ∈ GfC (Vc D i), fin (Vc D i) k ∈ dataLevel R i Q → ∃ (z : D.what₂.LL) (n : ℕ), 0 < n ∧ z ^ n = 1 ∧ ω (k, 1) φ = D.what₂.embLL z • φ) ∧ ∀ k', IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) 1 k' → ω (1, k') φ = φ := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hc i ξ χ ξR Q ω φ hK hv
  classical
  have hL := hc.lev
  have rV : (Vc D i).rank = D.R.r + D.R.t := D.sp.V_rank _ (Nat.le_add_left _ _) i.2
  have rW : (Wc D i).rank = D.R.r := D.sp.W_rank _ (Nat.le_add_left _ _) i.2
  have hW := hK.weil
  have hη := GlobalTheory.T.isUnramifiedEtaTilde_of_odd_exponentSum D _ _ hL.eta R.C.isEta _ _ _ hW.resS hW.resT (by
    rw [rV, rW]
    obtain ⟨c, hc⟩ := D.R.t_odd
    exact ⟨D.R.r + c, by omega⟩)
  obtain ⟨P, e, hee, hP, he, hom⟩ := GlobalTheory.VecInv.om_vec hW ⟨_, hη⟩ (GlobalTheory.T.isSelfDualCoordLattice_of_selfDualFrame D _ _ _ _ (hL.βV i))
    (GlobalTheory.T.isSelfDualCoordLattice_of_selfDualFrame D _ _ _ _ (hL.βW i)) (hL.βV i).choose_spec.1 (hL.βW i).choose_spec.1 hK.vec
  obtain ⟨u1, u2⟩ := unrOff_ker hL hK.chr hK.pl hK.ram i hP he
  have vals := fun x a a' u hx ha hu => val_ker hL hK.chr hK.tame hK.res hK.pl hK.ram i hP he x a a' u hx ha hu
  refine ⟨fun k hk hfin => ?_, fun k' hk' => ?_⟩
  · have hlev : finE (Vc D i) k ∈ Formalism.L2.DIV.lev D.sp.cm (Vc D i).gram (R.βV i)
        (flag1L (Lev.datY _ D.R.r D.R.t 1 (r_le_V i) R.Pg Q (LevelP.triv _ _ _) (fun _ _ => 1) (fun _ => 1) Lev.Frm.A)) :=
      hfin
    have sV : finE (Vc D i) k ∈ St (R.βV i) := parLev_St hlev.1
    have tg : ∀ PP ∈ R.Pg, redFn (R.βV i) PP (finE (Vc D i) k) ∈ blockTri (blkOf D.R.r D.R.t) := fun PP h =>
      parLev_g hlev.1 h
    have tri : ∀ PP, PP ∈ R.Pg ∨ PP ∈ Q → redFn (R.βV i) PP (finE (Vc D i) k) ∈ blockTri (blk2 D.R.r) := fun PP h =>
      h.elim (fun h => blockTri_blkOf_le _ _ (tg PP h)) fun h => parLev_q hlev.1 h
    have top1 : ∀ PP ∈ R.Pg, upperLeftBlock (r_le_V i) (redFn (R.βV i) PP (finE (Vc D i) k)) = 1 := fun PP h =>
      congrFun (Subgroup.mem_bot.1 hlev.2) ⟨PP, h⟩
    have same : ∀ PP ∈ R.Pg, upperLeftBlock (r_le_V i) (redFn (R.βV i) PP (finE (Vc D i) k)) =
        upperLeftBlock (r_le_rank_Wc i) (redFn (R.βW i) PP (finE (Wc D i) 1)) := fun PP h => by
      rw [top1 PP h, map_one, redFn_one]
      exact (blockDiagonalExtendByOnePrimeField_one _ _).symm
    have h1 := hom u1 (u1.mul u2.inv) _ (r_le_V i) (r_le_rank_Wc i) rW k 1 ⟨hk, sV⟩ (GlobalTheory.VecInv.Stab.one _ _) tri same
    obtain ⟨aV, haV, hrV⟩ := GlobalTheory.VecInv.exists_det_int sV
    obtain ⟨m1, m2, m3⟩ := vals (GlobalTheory.VecInv.detAt e hee _ k) _ aV _ (GlobalTheory.VecInv.isDetAt_detAt e hee _ k) haV
      fun PP _ => hrV PP
    rw [← Units.coe_prod] at h1
    refine smul_root h1 (RootLL.units_prod _ _ fun PP hPP => ?_) ?_
    · rw [Units.val_mul, Units.val_inv_eq_inv_val]
      exact (rootLL_res hv hK.fin (hK.res PP hPP) _).inv.mul (rootLL_res hv hK.fin (hK.res PP hPP) _)
    · simp only [splitFacO, map_one, mul_one, Circle.coe_inv]
      refine RootLL.inv ?_
      show RootLL D (((R.mu0 ((i : ℕ) + 1) * χ * R.eta⁻¹) (GlobalTheory.VecInv.detAt e hee _ k) : Circle) : ℂ)
      rw [MonoidHom.mul_apply, MonoidHom.mul_apply, MonoidHom.inv_apply, m3, inv_one, mul_one, Circle.coe_mul, m1, m2,
        Finset.prod_inv_distrib, Units.val_inv_eq_inv_val]
      exact (rootLL_chi hc.grp i _).inv.mul (RootLL.units_prod _ _ fun PP hPP => rootLL_res hv hK.fin (hK.res PP hPP) _)
  · have sW : finE (Wc D i) k' ∈ St (R.βW i) := parLev_St hk'.2.1
    have rt : ∀ PP ∈ R.Pg, upperLeftBlock (r_le_rank_Wc i) (redFn (R.βW i) PP (finE (Wc D i) k')) = 1 := fun PP h =>
      congrFun hk'.2.2 ⟨PP, h⟩
    have tri : ∀ PP, PP ∈ R.Pg ∨ PP ∈ Q → redFn (R.βV i) PP (finE (Vc D i) 1) ∈ blockTri (blk2 D.R.r) := fun PP _ => by
      rw [map_one, redFn_one]
      exact Subgroup.one_mem _
    have same : ∀ PP ∈ R.Pg, upperLeftBlock (r_le_V i) (redFn (R.βV i) PP (finE (Vc D i) 1)) =
        upperLeftBlock (r_le_rank_Wc i) (redFn (R.βW i) PP (finE (Wc D i) k')) := fun PP h => by
      rw [rt PP h, map_one, redFn_one]
      exact blockDiagonalExtendByOnePrimeField_one _ _
    have h2 := hom u1 (u1.mul u2.inv) _ (r_le_V i) (r_le_rank_Wc i) rW 1 k' (GlobalTheory.VecInv.Stab.one _ _) ⟨hk'.1, sW⟩ tri same
    obtain ⟨aW, haW, hrW⟩ := GlobalTheory.VecInv.exists_det_int sW
    obtain ⟨m1, m2, -⟩ := vals (GlobalTheory.VecInv.detAt e hee _ k') _ aW _ (GlobalTheory.VecInv.isDetAt_detAt e hee _ k') haW
      fun PP _ => hrW PP
    have lhs : ∀ PP ∈ Q, (ξR PP (Matrix.GeneralLinearGroup.det (upperLeftBlock (r_le_V i) (redFn (R.βV i) PP (finE (Vc D i) 1)))))⁻¹ *
        ξR PP (Matrix.GeneralLinearGroup.det (redFn (R.βW i) PP (finE (Wc D i) k'))) =
        ξR PP (Matrix.GeneralLinearGroup.det (redFn (R.βW i) PP (finE (Wc D i) k'))) := fun PP _ => by
      have h1 : upperLeftBlock (r_le_V i) (redFn (R.βV i) PP (finE (Vc D i) 1)) = 1 := by
        rw [map_one, redFn_one]
        exact blockDiagonalExtendByOnePrimeField_one _ _
      rw [h1, map_one, map_one, inv_one, one_mul]
    have pg1 : ∏ PP ∈ R.Pg, (R.chi ((i : ℕ) + 1) PP (Matrix.GeneralLinearGroup.det (redFn (R.βW i) PP (finE (Wc D i) k'))))⁻¹ = 1 :=
      by
        refine Finset.prod_eq_one fun PP h => ?_
        rw [← (GlobalTheory.T.det_twoDiagBlocks_properties (kP PP) _ D.R.r 0 (r_le_rank_Wc i) (redFn (R.βW i) PP (finE (Wc D i) k'))).2.2 rW, rt PP h, map_one,
          map_one, inv_one]
    rw [← Units.coe_prod] at h2
    refine smul_fix h2 ?_
    rw [Finset.prod_congr rfl lhs]
    simp only [splitFacO, map_one, inv_one, one_mul]
    show (((R.mu0 ((i : ℕ) + 1) * χ) (GlobalTheory.VecInv.detAt e hee _ k') : Circle) : ℂ) = _
    have t2 : ((χ (GlobalTheory.VecInv.detAt e hee _ k') : Circle) : ℂ) =
        ((∏ PP ∈ Q, ξR PP (Matrix.GeneralLinearGroup.det (redFn (R.βW i) PP (finE (Wc D i) k'))) : ℂˣ) : ℂ) := m2
    have t1 : ((R.mu0 ((i : ℕ) + 1) (GlobalTheory.VecInv.detAt e hee _ k') : Circle) : ℂ) = 1 := m1.trans (congrArg Units.val pg1)
    rw [MonoidHom.mul_apply, Circle.coe_mul, t1, t2]
    exact one_mul _

end GlobalTheory.KerMove
