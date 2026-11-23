import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousMulVec
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ResidueSequenceHolds
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PhiGpCommutationHolds
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PhiPgCommutationHoldsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PhiPgRankZeroHolds
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DerivativeTwistedIso
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedJacquetIteratedPhiEquiv
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RestrictionMirabolicTwistedKernel
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DerivativeZeroWhittakerKernel
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalTwistedKernelTopStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalIsGenericStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EquivariantFunctionalsEqDualAnnihilator
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnipBEqUnipotent
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SumFilterSuperdiag
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FixedEqFixedVectors
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.BernsteinZelevinskyGL.TopAdm
import GroundTheory.AutomorphicForms.ContragredientTranspose

noncomputable section
open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibOrd GlobalTheory.SplitWeil GlobalTheory.JHMult GlobalTheory.CompanionTheory.BZShell GlobalTheory.CompanionTheory.MirPair
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZShellOpen

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

open GlobalTheory.CompanionTheory.LeibOrd.Main in

theorem gp_iter (ψ : AddChar k Circle) (hc : Continuous ψ) (h1 : ψ ≠ 1) :
    ∀ (j n m : ℕ) (ρ : GRep k m) (τ : MRep k (n + j)) (N : ℕ) (hN : m + n = N) (h : m + (n + j) = N + j),
      IsSmooth ρ.ρ → IsSmooth τ.ρ →
        MIso (iterN ψ j (mcast h (prodGPn ρ τ))) (mcast hN (prodGPn ρ (iterN ψ j τ))) := by
  intro j
  induction j with
  | zero =>
    intro n m ρ τ N hN h hρ hτ
    subst hN
    exact miso_refl _
  | succ j ih =>
    intro n m ρ τ N hN h hρ hτ
    subst hN
    have h2 : m + (n + (j + 1)) = (m + (n + j)) + 1 := by omega
    have e : m + (n + j) = (m + n) + j := by omega
    have s1 := GlobalTheory.CompanionTheory.LeibPhi.phiGP k ψ hc h1 m (n + j) ρ τ hρ hτ
    have s2 : MIso (phiN ψ (mcast h (prodGPn ρ τ))) (mcast e (prodGPn ρ (phiN ψ τ))) := by
      rw [phiN_mcast ψ _ h h2 e]
      exact miso_mcast e s1
    exact miso_trans (miso_iterN ψ j s2) (ih n m ρ (phiN ψ τ) _ rfl e hρ (isSmooth_phiN ψ hτ))

theorem subsingleton_cInd {G W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup W] [Module ℂ W]
    (H : Subgroup G) (σ : Representation ℂ H W) [Subsingleton W] : Subsingleton (cIndSpace H σ) := by
  refine ⟨fun f f' => ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  funext g
  exact Subsingleton.elim _ _

theorem subsingleton_prodGPn {m j : ℕ} (ρ : GRep k m) (τ : MRep k j) (h : Subsingleton ρ.V) :
    Subsingleton (prodGPn ρ τ).V := by
  haveI : Subsingleton ((ρ.tw (((j + 1 : ℕ) : ℝ) / 2)).V ⊗[ℂ] (mtw τ (-((m : ℕ) : ℝ) / 2)).V) := by
    haveI : Subsingleton (ρ.tw (((j + 1 : ℕ) : ℝ) / 2)).V := h
    refine ⟨fun x y => ?_⟩
    have key : ∀ z : (ρ.tw (((j + 1 : ℕ) : ℝ) / 2)).V ⊗[ℂ] (mtw τ (-((m : ℕ) : ℝ) / 2)).V, z = 0 := by
      intro z
      induction z using TensorProduct.induction_on with
      | zero => rfl
      | tmul a b => rw [Subsingleton.elim a 0, TensorProduct.zero_tmul]
      | add a b ha hb => rw [ha, hb, add_zero]
    rw [key x, key y]
  exact subsingleton_cInd _ _

open GlobalTheory.CompanionTheory.LeibOrd.Main in

theorem pg_iter (ψ : AddChar k Circle) (hc : Continuous ψ) (h1 : ψ ≠ 1) :
    ∀ (j n t : ℕ) (τ : MRep k (n + j)) (σ : GRep k (t + 1)) (N : ℕ) (hN : n + (t + 1) = N)
      (h : (n + j) + (t + 1) = N + j), IsSmooth τ.ρ → IsSmooth σ.ρ →
      (∀ (i n' : ℕ) (e : n + j = n' + i), i < j → Subsingleton (dN ψ i (mcast e τ)).V) →
        MIso (iterN ψ j (mcast h (prodPGn τ σ))) (mcast hN (prodPGn (iterN ψ j τ) σ)) := by
  intro j
  induction j with
  | zero =>
    intro n t τ σ N hN h hτ hσ _
    subst hN
    exact miso_refl _
  | succ j ih =>
    intro n t τ σ N hN h hτ hσ hv
    subst hN
    have e : (n + j) + (t + 1) = (n + (t + 1)) + j := by omega
    have h2 : (n + j + 1) + (t + 1) = ((n + j) + t + 1) + 1 := by omega
    have e0 : (n + j) + t + 1 = (n + (t + 1)) + j := by omega
    have hext := GlobalTheory.T.phi_pg_commutation_holds k ψ hc h1 (n + j) t τ σ hτ hσ
    have hz : Subsingleton (psiN τ).V := hv 0 (n + (j + 1)) rfl (by omega)
    haveI : Subsingleton (mcast (by omega : (n + j + 1) + t = (n + j) + t + 1) (prodGPn (psiN τ) (gres σ))).V :=
      subsingleton_mcast _ (subsingleton_prodGPn _ _ hz)
    obtain ⟨q⟩ := equiv_of_ses_zero (ses_of_mext hext)
    have s2 : MIso (phiN ψ (mcast h (prodPGn τ σ))) (mcast e (prodPGn (phiN ψ τ) σ)) := by
      rw [phiN_mcast ψ _ h h2 e0]
      have := miso_mcast e0 (miso_symm (⟨q⟩ : MIso _ _))
      rwa [mcast_mcast] at this
    refine miso_trans (miso_iterN ψ j s2) (ih n t (phiN ψ τ) σ _ rfl e (isSmooth_phiN ψ hτ) hσ ?_)
    intro i n' e' hi
    have e'' : n + (j + 1) = n' + (i + 1) := by omega
    have h3 : Subsingleton (dN ψ i (phiN ψ (mcast e'' τ))).V := hv (i + 1) n' e'' (by omega)
    rwa [phiN_mcast ψ τ e'' rfl e'] at h3

open GlobalTheory.CompanionTheory.LeibOrd.DerivTw in

theorem dN_equiv (ψ : AddChar k Circle) {n : ℕ} (j : ℕ) (τ : MRep k (n + j)) :
    Nonempty ((dN ψ j τ).V ≃ₗ[ℂ] TwJacquet τ.ρ (derUnipM k (n + j) n) (derCharM k ψ (n + j) n)) := by
  obtain ⟨e1⟩ := giso_psiG (iterN_iso ψ j τ)
  obtain ⟨e2⟩ := psiG_mtw (iterPhi k ψ j τ) (-(j : ℝ) / 2)
  obtain ⟨e3⟩ := GlobalTheory.CompanionTheory.BZMir.iterPhi_twJacquet_equiv k ψ n j τ
  exact ⟨(e1.toLinearEquiv.trans e2.toLinearEquiv).trans e3⟩

theorem dN_gres_vanish (ψ : AddChar k Circle) {p : ℕ} (π : GRep k (p + 1)) (hcu : IsCuspidal π.ρ) (i n' : ℕ)
    (e : p = n' + i) (hn : 0 < n') : Subsingleton (dN ψ i (mcast e (gres π))).V := by
  subst e
  obtain ⟨q⟩ := dN_equiv ψ i (gres π)
  have h : twKer (gres π).ρ (derUnipM k (n' + i) n') (derCharM k ψ (n' + i) n') = ⊤ :=
    (GlobalTheory.CompanionTheory.BZMirDer.twKer_resM_derUnipM k ψ (n' + i) n' π.V π.ρ).trans
      (GlobalTheory.T.cuspidal_twisted_kernel_top k ψ _ _ _ π.ρ hcu hn (by omega))
  haveI : Subsingleton (TwJacquet (gres π).ρ (derUnipM k (n' + i) n') (derCharM k ψ (n' + i) n')) :=
    Submodule.Quotient.subsingleton_iff.2 h
  exact q.toEquiv.subsingleton

theorem subsingleton_mir_zero : Subsingleton (Mir k 0) := by
  refine ⟨fun a b => Subtype.ext (Units.ext ?_)⟩
  have ha := (mem_Mir_iff k _).1 a.2
  have hb := (mem_Mir_iff k _).1 b.2
  ext i j
  obtain rfl : i = Fin.last 0 := Fin.ext (by have := i.2; simp only [Fin.val_last]; omega)
  exact congrFun (ha.trans hb.symm) j

open GlobalTheory.LocGL GlobalTheory.BZSeg

theorem rank_functionals_congr {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) {N N' : Subgroup G} (h : N = N') (χ : N → ℂ) (χ' : N' → ℂ)
    (hχ : ∀ u : N, χ u = χ' ⟨u, h ▸ u.2⟩) :
    Module.rank ℂ (GroundTheory.Automorphic.Whittaker.equivariantFunctionals ρ χ) =
      Module.rank ℂ (GroundTheory.Automorphic.Whittaker.equivariantFunctionals ρ χ') := by
  subst h
  have : χ = χ' := funext fun u => hχ u
  rw [this]

theorem whit_rank_le (ψ : AddChar k Circle) (hc : Continuous ψ) (h1 : ψ ≠ 1) (N : ℕ) {V : Type} [AddCommGroup V]
    [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V) (hs : IsSmooth π) (hi : π.IsIrreducible) :
    Module.rank ℂ (TwJacquet π (unipB k (Fin N)) (whitChar ψ N)) ≤ 1 := by
  have hadm : GroundTheory.Automorphic.IsAdmissible π :=
    (GlobalTheory.CompanionTheory.AdmDict.isAdmissible_iff π).1 (PositivityTheory.Tls2.BZGL.irreducibleAdmissibleGL_top k N V π hs hi)
  have hc0 : Continuous (Circle.coeHom.compAddChar ψ) := continuous_subtype_val.comp hc
  have h10 : Circle.coeHom.compAddChar ψ ≠ 1 := by
    intro h
    apply h1
    ext x
    have h2 : Circle.coeHom (ψ x) = 1 := by simpa using DFunLike.congr_fun h x
    have h3 : ((ψ x : Circle) : ℂ) = 1 := h2
    simpa using h3
  haveI := hi
  have hle := GroundTheory.Automorphic.ContragredientTranspose.rank_whittaker_le_one
    (Circle.coeHom.compAddChar ψ) hc0 h10 π hadm
  rw [GlobalTheory.CompanionTheory.TwistedDual.rank_twJacquet_le_one_iff]
  rw [rank_functionals_congr π (GlobalTheory.CompanionTheory.IwasawaDict.unipB_eq_unipotent k N) _
    (fun u => GroundTheory.Automorphic.Whittaker.psiN (Circle.coeHom.compAddChar ψ) (u : GL (Fin N) k))
    (fun u => GlobalTheory.CompanionTheory.WhitDict.whitChar_eq_psiN k ψ N u)]
  exact hle

theorem finrank_whit (ψ : AddChar k Circle) (hc : Continuous ψ) (h1 : ψ ≠ 1) {p : ℕ} (π : GRep k (p + 1))
    (hs : IsSmooth π.ρ) (hi : π.ρ.IsIrreducible) (hcu : IsCuspidal π.ρ) :
    Module.finrank ℂ (TwJacquet π.ρ (unipB k (Fin (p + 1))) (whitChar ψ (p + 1))) = 1 := by
  have hV : Nontrivial π.V := by
    by_contra hV
    rw [not_nontrivial_iff_subsingleton] at hV
    obtain ⟨a, b, hab⟩ := hi.toNontrivial.exists_pair_ne
    apply hab
    ext x
    simp [Subsingleton.elim x 0]
  have hg : IsGenericFor ψ π.ρ := GlobalTheory.T.cuspidal_is_generic k ψ hc h1 p _ π.ρ hcu hV
  have hle := whit_rank_le ψ hc h1 (p + 1) π.ρ hs hi
  haveI : Nontrivial (TwJacquet π.ρ (unipB k (Fin (p + 1))) (whitChar ψ (p + 1))) := hg
  exact Module.finrank_eq_of_rank_eq (le_antisymm hle (Cardinal.one_le_iff_pos.2 rank_pos))

theorem finrank_iterN (ψ : AddChar k Circle) (hc : Continuous ψ) (h1 : ψ ≠ 1) {m : ℕ} (π : GRep k (0 + m + 1))
    (hs : IsSmooth π.ρ) (hi : π.ρ.IsIrreducible) (hcu : IsCuspidal π.ρ) :
    Module.finrank ℂ (iterN ψ m (gres π)).V = 1 := by
  obtain ⟨q⟩ := dN_equiv ψ m (gres π)
  have hb : twKer (iterN ψ m (gres π)).ρ (MirUin k 0) 1 = ⊥ := by
    haveI := subsingleton_mir_zero (k := k)
    unfold twKer
    rw [Submodule.span_eq_bot]
    rintro w ⟨u, v, rfl⟩
    have hu : (u : Mir k 0) = 1 := Subsingleton.elim _ _
    have hu' : u = 1 := Subtype.ext hu
    subst hu'
    simp
  have hk : twKer (gres π).ρ (derUnipM k (0 + m) 0) (derCharM k ψ (0 + m) 0) =
      twKer π.ρ (unipB k (Fin (0 + m + 1))) (whitChar ψ (0 + m + 1)) :=
    (GlobalTheory.CompanionTheory.BZMirDer.twKer_resM_derUnipM k ψ (0 + m) 0 π.V π.ρ).trans
      (GlobalTheory.CompanionTheory.DerWhit.twKer_derUnip_zero (k := k) ψ (0 + m + 1) π.V π.ρ)
  have e1 : (iterN ψ m (gres π)).V ≃ₗ[ℂ] (dN ψ m (gres π)).V := (Submodule.quotEquivOfEqBot _ hb).symm
  have e3 : TwJacquet (gres π).ρ (derUnipM k (0 + m) 0) (derCharM k ψ (0 + m) 0) ≃ₗ[ℂ]
      TwJacquet π.ρ (unipB k (Fin (0 + m + 1))) (whitChar ψ (0 + m + 1)) := Submodule.quotEquivOfEq (M := π.V) _ _ hk
  rw [e1.finrank_eq, q.finrank_eq, e3.finrank_eq]
  exact finrank_whit ψ hc h1 π hs hi hcu

def glCast {a b : ℕ} (c : a = b) (g : GL (Fin a) k) : GL (Fin b) k := c ▸ g

theorem glCast_apply {a b : ℕ} (c : a = b) (g : GL (Fin a) k) (i j : Fin b) :
    (glCast c g : GL (Fin b) k).val i j = g.val (Fin.cast c.symm i) (Fin.cast c.symm j) := by
  subst c; rfl

theorem glCast_glCast {a b : ℕ} (c : a = b) (g : GL (Fin b) k) : glCast c (glCast c.symm g) = g := by
  subst c; rfl

open GlobalTheory.CompanionTheory.MirFourier GlobalTheory.CompanionTheory.MirLevi GlobalTheory.CompanionTheory.BZOnto.PerpSmall

theorem isOpen_shiftBall (n : ℕ) (s : kˣ) (p : Fin n → k) :
    IsOpen {v : Fin n → k | Multiplicative.ofAdd (v - p) ∈ polyBall (k := k) n s} :=
  (isOpen_polyBall n s).preimage (continuous_ofAdd.comp (continuous_id.sub continuous_const))

theorem exists_period {n : ℕ} {E : Type} [AddCommGroup E] (φ : (Fin n → k) → E) (hl : IsLocallyConstant φ)
    (hK : HasCompactSupport φ) :
    ∃ s : kˣ, ∀ v a : Fin n → k, Multiplicative.ofAdd a ∈ polyBall (k := k) n s → φ (v + a) = φ v := by
  have hloc : ∀ p : Fin n → k, ∃ s : kˣ, ∀ a : Fin n → k, Multiplicative.ofAdd a ∈ polyBall (k := k) n s →
      φ (p + a) = φ p := by
    intro p
    have hU : (fun x : Multiplicative (Fin n → k) => p + Multiplicative.toAdd x) ⁻¹' (φ ⁻¹' {φ p}) ∈
        nhds (1 : Multiplicative (Fin n → k)) := by
      refine ((hl.isOpen_fiber (φ p)).preimage
        (continuous_const.add continuous_toAdd)).mem_nhds ?_
      simp
    obtain ⟨s, hs⟩ := exists_polyBall_subset hU
    exact ⟨s, fun a ha => hs ha⟩
  choose sp hsp using hloc
  obtain ⟨t, ht⟩ := hK.isCompact.elim_finite_subcover
    (fun p : Fin n → k => {v : Fin n → k | Multiplicative.ofAdd (v - p) ∈ polyBall (k := k) n (sp p)})
    (fun p => isOpen_shiftBall n (sp p) p)
    (fun v _ => Set.mem_iUnion.2 ⟨v, by simp [sub_self, one_mem]⟩)
  have hcom : ∀ t : Finset (Fin n → k), ∃ s : kˣ, ∀ p ∈ t, polyBall (k := k) n s ≤ polyBall n (sp p) := by
    intro t
    classical
    induction t using Finset.induction_on with
    | empty => exact ⟨1, by simp⟩
    | insert a t _ ih =>
      obtain ⟨S, hS⟩ := ih
      obtain ⟨s, h1, h2⟩ := exists_common n S (sp a)
      refine ⟨s, fun p hp => ?_⟩
      rcases Finset.mem_insert.1 hp with rfl | hp
      · exact h2
      · exact h1.trans (hS p hp)
  obtain ⟨s, hs⟩ := hcom t
  have key : ∀ v ∈ tsupport φ, ∀ a : Fin n → k, Multiplicative.ofAdd a ∈ polyBall (k := k) n s → φ (v + a) = φ v := by
    intro v hv a ha
    obtain ⟨p, hp, hvp⟩ : ∃ p ∈ t, Multiplicative.ofAdd (v - p) ∈ polyBall (k := k) n (sp p) := by
      have := ht hv
      simp only [Set.mem_iUnion] at this
      obtain ⟨p, hp, h⟩ := this
      exact ⟨p, hp, h⟩
    have h2 : Multiplicative.ofAdd (v + a - p) ∈ polyBall (k := k) n (sp p) := by
      have := mul_mem hvp (hs p hp ha)
      rw [← ofAdd_add] at this
      rwa [show v - p + a = v + a - p by abel] at this
    have e1 := hsp p _ hvp
    have e2 := hsp p _ h2
    rw [show p + (v - p) = v by abel] at e1
    rw [show p + (v + a - p) = v + a by abel] at e2
    rw [e1, e2]
  refine ⟨s, fun v a ha => ?_⟩
  by_cases hv : v ∈ tsupport φ
  · exact key v hv a ha
  · by_cases hv' : v + a ∈ tsupport φ
    · have h3 : Multiplicative.ofAdd (-a) ∈ polyBall (k := k) n s := by
        have := inv_mem ha
        rwa [← ofAdd_neg] at this
      have := key _ hv' (-a) h3
      rw [add_neg_cancel_right] at this
      exact this.symm
    · rw [image_eq_zero_of_notMem_tsupport hv, image_eq_zero_of_notMem_tsupport hv']

theorem restr_lc {n : ℕ} {E : Type} [AddCommGroup E] [Module ℂ E] (ρ : Representation ℂ (LH k n) E)
    (f : cIndSpace (LH k n) ρ) : IsLocallyConstant (restr ρ f) := by
  obtain ⟨s, hs⟩ := restr_periodic ρ f
  refine (IsLocallyConstant.iff_exists_open _).2 fun v => ⟨_, isOpen_shiftBall n s v, ?_, fun y hy => ?_⟩
  · show Multiplicative.ofAdd (v - v) ∈ polyBall (k := k) n s
    rw [sub_self, ofAdd_zero]; exact one_mem _
  have hy' : Multiplicative.ofAdd (y - v) ∈ polyBall (k := k) n s := hy
  have e : v + (y - v) = y := by abel
  exact (congrArg (restr ρ f) e).symm.trans (hs v (y - v) hy')

theorem restr_cs {n : ℕ} {E : Type} [AddCommGroup E] [Module ℂ E] (ρ : Representation ℂ (LH k n) E)
    (f : cIndSpace (LH k n) ρ) : HasCompactSupport (restr ρ f) := by
  obtain ⟨S, hS⟩ := restr_support ρ f
  refine HasCompactSupport.intro ((isCompact_polyBall n S).image continuous_toAdd) fun v hv => ?_
  by_contra h
  exact hv ⟨Multiplicative.ofAdd v, hS v h, rfl⟩

def restrS {n : ℕ} {E : Type} [AddCommGroup E] [Module ℂ E] (ρ : Representation ℂ (LH k n) E) :
    cIndSpace (LH k n) ρ →ₗ[ℂ] SchF k n E where
  toFun f := ⟨restr ρ f, restr_lc ρ f, restr_cs ρ f⟩
  map_add' _ _ := Subtype.ext (map_add (restr ρ) _ _)
  map_smul' c f := Subtype.ext (map_smul (restr ρ) c f)

set_option maxHeartbeats 2000000 in
open Classical in
theorem restrS_surjective {n : ℕ} {E : Type} [AddCommGroup E] [Module ℂ E] (ρ : Representation ℂ (LH k n) E)
    (hρ : IsSmooth ρ) : Function.Surjective (restrS ρ) := by
  intro f
  obtain ⟨s, hs⟩ := exists_period f.1 f.2.1 f.2.2
  obtain ⟨S, hS⟩ := exists_compact_polyBall n f.2.2.isCompact
  obtain ⟨R, hR⟩ := exists_reps f.1 s S hs (fun v hv => hS v (subset_tsupport _ hv))
  choose b hb using fun e : E => exists_bump ρ hρ s e
  refine ⟨∑ x ∈ R, cInd (LH k n) ρ (uv n (-x)) (b (f.1 x)), Subtype.ext (funext fun v => ?_)⟩
  have hx : ∀ x, restr ρ (cInd (LH k n) ρ (uv n (-x)) (b (f.1 x))) v =
      if Multiplicative.ofAdd (v - x) ∈ polyBall (k := k) n s then f.1 x else 0 := fun x =>
    (restr_uv ρ (-x) _ v).trans ((hb (f.1 x) (v + -x)).trans (by rw [sub_eq_add_neg]))
  refine (congrFun (map_sum (restr ρ) _ _) v).trans ((Finset.sum_apply _ _ _).trans ?_)
  exact (Finset.sum_congr rfl fun x _ => hx x).trans (hR v).symm

theorem model_LH {n : ℕ} {E : Type} [AddCommGroup E] [Module ℂ E] (ρ : Representation ℂ (LH k n) E) (hρ : IsSmooth ρ) :
    ∃ e : SchF k n E ≃ₗ[ℂ] cIndSpace (LH k n) ρ, ∀ f y, restr ρ (e f) y = f.1 y := by
  have hi : Function.Injective (restrS ρ) := fun f f' h =>
    restr_injective ρ (congrArg Subtype.val h)
  refine ⟨(LinearEquiv.ofBijective (restrS ρ) ⟨hi, restrS_surjective ρ hρ⟩).symm, fun f y => ?_⟩
  have := (LinearEquiv.ofBijective (restrS ρ) ⟨hi, restrS_surjective ρ hρ⟩).apply_symm_apply f
  exact congrFun (congrArg Subtype.val this) y

set_option maxHeartbeats 2000000 in

theorem model_H {n : ℕ} {E : Type} [AddCommGroup E] [Module ℂ E] (H : Subgroup (Mir k n)) (hH : H = LH k n)
    (ρ : Representation ℂ H E) (hρ : IsSmooth ρ) (hm : ∀ g, levi k n g ∈ H) :
    ∃ e : SchF k n E ≃ₗ[ℂ] cIndSpace H ρ, (∀ x f, e (shiftF x f) = cInd H ρ (uM n x) (e f)) ∧
      ∀ g f, e (actF (ρ.comp ((levi k n).codRestrict H hm)) g f) = cInd H ρ (levi k n g) (e f) := by
  subst hH
  obtain ⟨e, he⟩ := model_LH ρ hρ
  refine ⟨e, fun x f => restr_injective ρ (funext fun y => ?_), fun g f => restr_injective ρ (funext fun y => ?_)⟩
  · exact (he _ y).trans ((he f (y + x)).symm.trans (restr_uv ρ x (e f) y).symm)
  · exact (he _ y).trans ((congrArg (ρ (lv k n g)) (he f _)).symm.trans (restr_levi ρ g (e f) y).symm)

theorem ePG_zero_true' (t : ℕ) (b : Fin t) : (ePG 0 t ⟨true, b⟩ : Fin (0 + t + 1)).val = b.val := by
  simp [ePG, two]

theorem pg_levi (t : ℕ) (c : 0 + t = t) (g : GL (Fin (0 + t)) k) (h : levi k (0 + t) g ∈ HPG k 0 t) :
    pgProj k 0 t ⟨_, h⟩ = (1, glCast c g) := by
  refine Prod.ext ?_ ?_
  · haveI := subsingleton_mir_zero (k := k)
    exact Subsingleton.elim _ _
  · apply Units.ext
    ext i j
    show ((levi k (0 + t) g : Mir k (0 + t)) : GL (Fin (0 + t + 1)) k).val
        (ePG 0 t ⟨true, i⟩) (ePG 0 t ⟨true, j⟩) = (glCast c g).val i j
    have e : ∀ b : Fin t, (ePG 0 t ⟨true, b⟩ : Fin (0 + t + 1)) = Fin.castSucc (Fin.cast c.symm b) := fun b =>
      Fin.ext ((ePG_zero_true' t b).trans rfl)
    rw [e, e, glCast_apply]
    show glEmbMat k _ g.val _ _ = _
    simp [glEmbMat]

def schMap {d : ℕ} {E E' : Type} [AddCommGroup E] [Module ℂ E] [AddCommGroup E'] [Module ℂ E'] (ι : E →ₗ[ℂ] E') :
    SchF k d E →ₗ[ℂ] SchF k d E' where
  toFun f := ⟨fun y => ι (f.1 y), f.2.1.comp ι, f.2.2.comp_left (map_zero ι)⟩
  map_add' f f' := Subtype.ext (funext fun y => map_add ι _ _)
  map_smul' c f := Subtype.ext (funext fun y => map_smul ι c _)

theorem model_cast {N t : ℕ} (c : N = t) {E E' : Type} [AddCommGroup E] [Module ℂ E] [AddCommGroup E'] [Module ℂ E']
    (ι : E ≃ₗ[ℂ] E') (X : Representation ℂ (GL (Fin t) k) E) (X' : Representation ℂ (GL (Fin N) k) E')
    (hX : ∀ g v, ι (X g v) = X' (glCast c.symm g) (ι v)) :
    ∃ T : SchF k t E ≃ₗ[ℂ] SchF k N E', (∀ x f, T (shiftF x f) = shiftF (x ∘ Fin.cast c) (T f)) ∧
      ∀ g f, T (actF X g f) = actF X' (glCast c.symm g) (T f) := by
  subst c
  refine ⟨LinearEquiv.ofLinear (schMap ι.toLinearMap) (schMap ι.symm.toLinearMap) ?_ ?_, fun x f => rfl, fun g f => ?_⟩
  · ext f y
    exact congrFun (congrArg Subtype.val (rfl : _ = _)) y |>.trans (ι.apply_symm_apply _)
  · ext f y
    exact ι.symm_apply_apply _
  · exact Subtype.ext (funext fun y => hX g _)

theorem mcast_act {a b : ℕ} (h : a = b) (R : MRep k a) :
    ∃ E : R.V ≃ₗ[ℂ] (mcast h R).V, (∀ x v, E (R.ρ (uM a (x ∘ Fin.cast h)) v) = (mcast h R).ρ (uM b x) (E v)) ∧
      ∀ g v, E (R.ρ (levi k a (glCast h.symm g)) v) = (mcast h R).ρ (levi k b g) (E v) := by
  subst h
  exact ⟨LinearEquiv.refl _ _, fun _ _ => rfl, fun _ _ => rfl⟩

theorem exists_line_tensor {W V : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup V] [Module ℂ V]
    (h : Module.finrank ℂ W = 1) : ∃ (w : W) (ι : V ≃ₗ[ℂ] W ⊗[ℂ] V), ∀ v, ι v = w ⊗ₜ[ℂ] v := by
  haveI : Module.Finite ℂ W := Module.finite_of_finrank_pos (by omega)
  let e : ℂ ≃ₗ[ℂ] W := LinearEquiv.ofFinrankEq _ _ (by simp [h])
  refine ⟨e 1, (TensorProduct.lid ℂ V).symm.trans (TensorProduct.congr e (LinearEquiv.refl ℂ V)), fun v => ?_⟩
  simp

set_option maxHeartbeats 2000000 in

theorem model' (t : ℕ) (c : 0 + t = t) (τ : MRep k 0) (σ : GRep k t) (hτ : IsSmooth τ.ρ) (hσ : IsSmooth σ.ρ)
    (h1 : Module.finrank ℂ τ.V = 1) :
    ∃ e : SchF k t σ.V ≃ₗ[ℂ] (mcast c (prodPGn τ σ)).V,
      (∀ x f, e (shiftF x f) = (mcast c (prodPGn τ σ)).ρ (uM t x) (e f)) ∧
      ∀ g f, e (actF (σ.tw (-((0 + 1 : ℕ) : ℝ) / 2)).ρ g f) = (mcast c (prodPGn τ σ)).ρ (levi k t g) (e f) := by
  have hm : ∀ g, levi k (0 + t) g ∈ HPG k 0 t := fun g => by
    rw [HPG_zero t]
    exact ⟨g, rfl⟩
  have hsm := smooth_pg 0 t (mtw τ (((t : ℕ) : ℝ) / 2)).ρ (σ.tw (-((0 + 1 : ℕ) : ℝ) / 2)).ρ (sm_mtw hτ _) (sm_tw hσ _)
  obtain ⟨e, e1, e2⟩ := model_H (HPG k 0 t) (HPG_zero t) _ hsm hm
  obtain ⟨w, ι, hι⟩ := exists_line_tensor (W := (mtw τ (((t : ℕ) : ℝ) / 2)).V) (V := (σ.tw (-((0 + 1 : ℕ) : ℝ) / 2)).V) h1
  obtain ⟨T, T1, T2⟩ := model_cast c ι (σ.tw (-((0 + 1 : ℕ) : ℝ) / 2)).ρ
    (((extTensor (mtw τ (((t : ℕ) : ℝ) / 2)).ρ (σ.tw (-((0 + 1 : ℕ) : ℝ) / 2)).ρ).comp (pgProj k 0 t)).comp
      ((levi k (0 + t)).codRestrict (HPG k 0 t) hm)) (fun g v => by
    show _ = extTensor _ _ (pgProj k 0 t ⟨levi k (0 + t) (glCast c.symm g), hm _⟩) (ι v)
    rw [pg_levi t c, glCast_glCast]
    refine (hι _).trans (Eq.trans ?_ (congrArg _ (hι v)).symm)
    refine Eq.trans ?_ (extTensor_tmul _ _ _ _ _).symm
    have h2 : (mtw τ (((t : ℕ) : ℝ) / 2)).ρ (1 : Mir k 0) w = w := by
      rw [map_one]
      rfl
    exact (congrArg (fun z => z ⊗ₜ[ℂ] ((σ.tw (-((0 + 1 : ℕ) : ℝ) / 2)).ρ g v)) h2).symm)
  obtain ⟨E, E1, E2⟩ := mcast_act c (prodPGn τ σ)
  refine ⟨(T.trans e).trans E, fun x f => ?_, fun g f => ?_⟩
  · exact (congrArg (fun z => E (e z)) (T1 x f)).trans ((congrArg E (e1 _ (T f))).trans (E1 x _))
  · exact (congrArg (fun z => E (e z)) (T2 g f)).trans ((congrArg E (e2 _ (T f))).trans (E2 g _))

theorem mem_mirabolicParabolic_zero_right (d : ℕ) (g : Mir k (d + 0)) : g ∈ MirabolicParabolic k d 0 := by
  show (g : GL (Fin (d + 0 + 1)) k) ∈ parab k (eGP d 0)
  rw [mem_parab_iff]
  intro a c i j hac
  obtain ⟨rfl, rfl⟩ : a = true ∧ c = false := by
    revert hac; cases a <;> cases c <;> decide
  have hi : i = Fin.last 0 := Fin.ext (by have := i.2; simp only [Fin.val_last]; omega)
  subst hi
  rw [blockIndex_true_last]
  have hh := congrFun ((mem_Mir_iff k _).1 g.2) (eGP d 0 ⟨false, j⟩)
  rw [hh]
  simp only [eLast, Pi.single_apply]
  exact if_neg (blockIndex_false_ne_last d 0 j)

theorem gp_uM (d : ℕ) (x : Fin (d + 0) → k) (h : uM (d + 0) x ∈ MirabolicParabolic k d 0) : gpProj k d 0 ⟨_, h⟩ = 1 := by
  refine Prod.ext ?_ ?_
  · apply Units.ext
    ext i j
    show (1 + colMat k (d + 0) x) (eGP d 0 ⟨false, i⟩) (eGP d 0 ⟨false, j⟩) = (1 : Matrix (Fin d) (Fin d) k) i j
    have hinj : eGP d 0 ⟨false, i⟩ = eGP d 0 ⟨false, j⟩ ↔ i = j := by
      constructor
      · intro e
        simpa using (eGP d 0).injective e
      · rintro rfl; rfl
    have hl : eGP d 0 ⟨false, j⟩ ≠ Fin.last (d + 0) := blockIndex_false_ne_last d 0 j
    simp [colMat, hl, one_apply, hinj]
    exact fun h => absurd h hl
  · haveI := subsingleton_mir_zero (k := k)
    exact Subsingleton.elim _ _

theorem cInd_top {G W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup W] [Module ℂ W]
    (H : Subgroup G) (σ : Representation ℂ H W) (htop : ∀ g, g ∈ H) (u : G) (h1 : ∀ w, σ ⟨u, htop u⟩ w = w)
    (f : cIndSpace H σ) : cInd H σ u f = f := by
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  funext g
  have hf : ∀ (h : H) (x : G), f.1.1.1 ((h : G) * x) = σ h (f.1.1.1 x) := f.1.1.2
  show f.1.1.1 (g * u) = f.1.1.1 g
  have a1 := hf ⟨g, htop g⟩ u
  have a2 := hf ⟨u, htop u⟩ 1
  have a3 := hf ⟨g, htop g⟩ 1
  rw [mul_one] at a2 a3
  simp only at a1 a2 a3
  rw [a1, a3, a2, h1]

theorem gp_triv {d : ℕ} (ρ : GRep k d) (Z : MRep k 0) (x : Fin (d + 0) → k) (v : (prodGPn ρ Z).V) :
    (prodGPn ρ Z).ρ (uM (d + 0) x) v = v := by
  refine cInd_top _ _ (mem_mirabolicParabolic_zero_right d) _ (fun w => ?_) v
  show extTensor _ _ (gpProj k d 0 ⟨uM (d + 0) x, _⟩) w = w
  rw [gp_uM, map_one]
  rfl

theorem gres_cast {p q : ℕ} (h : p = q) (h' : p + 1 = q + 1) (π : GRep k (p + 1)) :
    gres (π.cast h') = mcast h (gres π) := by
  subst h; rfl

theorem irr_cast {p q : ℕ} (h : p = q) (π : GRep k p) (hi : π.ρ.IsIrreducible) : (π.cast h).ρ.IsIrreducible := by
  subst h; exact hi

theorem cusp_cast {p q : ℕ} (h : p = q) (π : GRep k p) (hi : IsCuspidal π.ρ) : IsCuspidal (π.cast h).ρ := by
  subst h; exact hi

theorem mcast_pg {p q t N : ℕ} (e : p = q) (τ : MRep k p) (σ : GRep k t) (h : p + t = N) (h' : q + t = N) :
    mcast h (prodPGn τ σ) = mcast h' (prodPGn (mcast e τ) σ) := by
  subst e; rfl

theorem mcast_gp {p q r N : ℕ} (e : p = q) (ρ : GRep k r) (τ : MRep k p) (h : r + p = N) (h' : r + q = N) :
    mcast h (prodGPn ρ τ) = mcast h' (prodGPn ρ (mcast e τ)) := by
  subst e; rfl

theorem model (t : ℕ) (c : 0 + t = t) (τ : MRep k 0) (σ : GRep k t) (hτ : IsSmooth τ.ρ) (hσ : IsSmooth σ.ρ)
    (h1 : Module.finrank ℂ τ.V = 1) :
    ∃ e : SchF k t σ.V ≃ₗ[ℂ] (mcast c (prodPGn τ σ)).V,
      (∀ x f, e (shiftF x f) = (mcast c (prodPGn τ σ)).ρ (uM t x) (e f)) ∧
      ∀ g f, e (actF (σ.tw (-1 / 2)).ρ g f) = (mcast c (prodPGn τ σ)).ρ (levi k t g) (e f) := by
  have h := model' t c τ σ hτ hσ h1
  rwa [show -((0 + 1 : ℕ) : ℝ) / 2 = -1 / 2 by norm_num] at h

open GlobalTheory.CompanionTheory.LeibOrd.Main in

theorem open_part : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (ψ : AddChar k Circle) (hc : Continuous ψ) (h1 : ψ ≠ 1) (m : ℕ) (a b : GRep k (m + 1))
    (hs : IsSmooth a.ρ) (hb : IsSmooth b.ρ) (hi : a.ρ.IsIrreducible) (hcu : IsCuspidal a.ρ),
    ∃ ι : SchF k (m + 1) b.V →ₗ[ℂ] (Rm ψ a b).V, Function.Injective ι ∧
      (∀ x f, ι (shiftF x f) = (Rm ψ a b).ρ (uM (m + 1) x) (ι f)) ∧
      (∀ g f, ι (actF (b.tw (-1 / 2)).ρ g f) = (Rm ψ a b).ρ (levi k (m + 1) g) (ι f)) ∧
      ∀ x v, (Rm ψ a b).ρ (uM (m + 1) x) v - v ∈ LinearMap.range ι := by
  intro k _ _ _ _ ψ hc h1 m a b hs hb hi hcu
  have e0 : m = 0 + m := by omega
  have e1 : m + 1 = 0 + m + 1 := by omega
  have sa' : IsSmooth (a.cast e1).ρ := isSmooth_gcast e1 hs
  have sb' : IsSmooth (b.cast e1).ρ := isSmooth_gcast e1 hb
  have sga : IsSmooth (gres (a.cast e1)).ρ := isSmooth_gres sa'
  have sgb : IsSmooth (gres (b.cast e1)).ρ := isSmooth_gres sb'
  have hx := GlobalTheory.CompanionTheory.BZRes.resSeq k m m ((m + 1) + m) (by omega) a b hs hb
  have ses := ses_iterN ψ hc m (n := m + 1) (isSmooth_mcast _ (isSmooth_prodPGn _ _))
    (isSmooth_gres (isSmooth_gcast _ (isSmooth_prod _ _))) (isSmooth_mcast _ (isSmooth_prodGPn _ _)) (ses_of_mext hx)
  have hτ₀ : IsSmooth (iterN ψ m (gres (a.cast e1))).ρ := isSmooth_iterN ψ m sga
  have hfin := finrank_iterN ψ hc h1 (a.cast e1) sa' (irr_cast e1 a hi) (cusp_cast e1 a hcu)
  have isoA : MIso (iterN ψ m (mcast (by omega : m + (m + 1) = (m + 1) + m) (prodPGn (gres a) b)))
      (mcast (by omega : 0 + (m + 1) = m + 1) (prodPGn (iterN ψ m (gres (a.cast e1))) b)) := by
    rw [mcast_pg e0 (gres a) b (by omega) (by omega : (0 + m) + (m + 1) = (m + 1) + m), ← gres_cast e0 e1 a]
    exact pg_iter ψ hc h1 m 0 m (gres (a.cast e1)) b (m + 1) (by omega) (by omega) sga hb
      (fun i n' e hi' => dN_gres_vanish ψ (a.cast e1) (cusp_cast e1 a hcu) i n' e (by omega))
  have isoC : MIso (iterN ψ m (mcast (by omega : (m + 1) + m = (m + 1) + m) (prodGPn a (gres b))))
      (prodGPn (m := m + 1) (j := 0) a (iterN ψ m (gres (b.cast e1)))) := by
    rw [mcast_gp e0 a (gres b) (by omega) (by omega : (m + 1) + (0 + m) = (m + 1) + m), ← gres_cast e0 e1 b]
    exact gp_iter ψ hc h1 m 0 (m + 1) a (gres (b.cast e1)) (m + 1) rfl (by omega) hs sgb
  obtain ⟨f, g, hf, hg, hinj, hsurj, hex⟩ := ses
  obtain ⟨eA⟩ := isoA
  obtain ⟨eC⟩ := isoC
  obtain ⟨e, he1, he2⟩ := model (m + 1) (by omega) (iterN ψ m (gres (a.cast e1))) b hτ₀ hb hfin
  refine ⟨f ∘ₗ eA.symm.toLinearEquiv.toLinearMap ∘ₗ e.toLinearMap, ?_, ?_, ?_, ?_⟩
  · exact hinj.comp (eA.symm.toLinearEquiv.injective.comp e.injective)
  · intro x φ
    show f (eA.symm (e (shiftF x φ))) = _
    rw [he1, eint eA.symm, hf]
    rfl
  · intro x φ
    exact (congrArg (fun z => f (eA.symm z)) (he2 x φ)).trans ((congrArg f (eint eA.symm _ _)).trans (hf _ _))
  · intro x v
    have h0 : (Rm ψ a b).ρ (uM (m + 1) x) v - v ∈ LinearMap.ker g := by
      have h4 : g ((Rm ψ a b).ρ (uM (m + 1) x) v) = g v := by
        refine (hg _ _).trans ?_
        apply eC.toLinearEquiv.injective
        exact (eint eC _ _).trans (gp_triv a _ x _)
      exact (map_sub g _ _).trans (sub_eq_zero.2 h4)
    obtain ⟨w, hw⟩ := hex.ge h0
    obtain ⟨φ, hφ⟩ := e.surjective (eA w)
    refine ⟨φ, ?_⟩
    exact (congrArg (fun z => f (eA.symm z)) hφ).trans ((congrArg f (Representation.Equiv.symm_apply_apply eA w)).trans hw)

end GlobalTheory.CompanionTheory.BZShellOpen

end
